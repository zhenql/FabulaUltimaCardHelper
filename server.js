const express = require("express");
const http = require("http");
const path = require("path");
const fs = require("fs");
const crypto = require("crypto");
const Database = require("better-sqlite3");
const { WebSocket, WebSocketServer } = require("ws");

const PORT = Number(process.env.PORT || 6021);
const DATA_DIR = path.join(__dirname, "data");
const DB_PATH = path.join(DATA_DIR, "card_tool.sqlite");
const ROOMS_PATH = path.join(__dirname, "rooms.json");

fs.mkdirSync(DATA_DIR, { recursive: true });

const db = new Database(DB_PATH);
db.pragma("journal_mode = WAL");
db.exec(`
  CREATE TABLE IF NOT EXISTS rooms (
    room_id TEXT PRIMARY KEY,
    state_json TEXT NOT NULL,
    updated_at TEXT NOT NULL
  )
`);

const getRoomStmt = db.prepare("SELECT state_json FROM rooms WHERE room_id = ?");
const saveRoomStmt = db.prepare(`
  INSERT INTO rooms (room_id, state_json, updated_at)
  VALUES (?, ?, datetime('now'))
  ON CONFLICT(room_id) DO UPDATE SET
    state_json = excluded.state_json,
    updated_at = excluded.updated_at
`);

const SUITS = [
  { symbol: "♦", name: "风", red: true },
  { symbol: "♥", name: "火", red: true },
  { symbol: "♠", name: "冰", red: false },
  { symbol: "♣", name: "土", red: false },
];

const SKILL_LIMITS = {
  gamble: 1,
  hedge: 1,
  magic: 3,
  fortune: 5,
  trap: 4,
};

const SKILL_NAMES = {
  gamble: "豪赌乾坤",
  hedge: "风险对冲",
  magic: "魔法卡牌",
  fortune: "时运再来",
  trap: "陷阱卡牌",
};

const DEFAULT_SKILL_LEVELS = {
  gamble: 0,
  hedge: 0,
  magic: 0,
  fortune: 0,
  trap: 0,
};

const roomClients = new Map();
const roomStates = new Map();
const allowedRooms = loadAllowedRooms();

function loadAllowedRooms() {
  if (!fs.existsSync(ROOMS_PATH)) {
    throw new Error("rooms.json not found. Define allowed room ids before starting the server.");
  }

  const raw = JSON.parse(fs.readFileSync(ROOMS_PATH, "utf8"));
  const entries = Array.isArray(raw) ? raw : raw.rooms;
  if (!Array.isArray(entries)) {
    throw new Error("rooms.json must be an array, or an object with a rooms array.");
  }

  const rooms = new Map();
  for (const entry of entries) {
    const id = normalizeRoomId(typeof entry === "string" ? entry : entry.id);
    if (!id) continue;
    rooms.set(id, typeof entry === "string" ? { id } : { ...entry, id });
  }

  if (!rooms.size) {
    throw new Error("rooms.json does not define any valid room ids.");
  }
  return rooms;
}

function cloneCards(cards) {
  return cards.map((card) => ({ ...card }));
}

function cloneState(state) {
  return {
    ...state,
    deck: cloneCards(state.deck),
    hand: cloneCards(state.hand),
    discard: cloneCards(state.discard),
    selectedIds: [...state.selectedIds],
    records: state.records.map((record) => ({
      ...record,
      before: record.before ? {
        deck: cloneCards(record.before.deck),
        hand: cloneCards(record.before.hand),
        discard: cloneCards(record.before.discard),
        selectedIds: [...record.before.selectedIds],
        pendingHedge: record.before.pendingHedge ? { ...record.before.pendingHedge } : null,
        activeSkill: record.before.activeSkill,
        characterLevel: record.before.characterLevel,
        skillLevels: { ...record.before.skillLevels },
      } : null,
    })),
    skillLevels: { ...state.skillLevels },
    pendingHedge: state.pendingHedge ? { ...state.pendingHedge } : null,
  };
}

function serializeState(state) {
  return JSON.stringify({
    ...state,
    selectedIds: [...state.selectedIds],
  });
}

function hydrateState(raw) {
  return {
    ...raw,
    selectedIds: new Set(raw.selectedIds || []),
    skillLevels: {
      ...DEFAULT_SKILL_LEVELS,
      ...(raw.skillLevels || {}),
    },
    skillNotice: raw.skillNotice || "",
  };
}

function publicState(state) {
  return {
    ...state,
    selectedIds: [...state.selectedIds],
  };
}

function makeCard(state, value, suit) {
  const info = SUITS.find((item) => item.symbol === suit);
  return {
    id: `c${state.nextId++}`,
    value,
    suit,
    type: info.name,
    red: info.red,
    joker: false,
  };
}

function makeJoker(state, index) {
  return {
    id: `j${state.nextId++}`,
    value: null,
    suit: null,
    type: `百搭${index}`,
    red: false,
    joker: true,
  };
}

function shuffle(cards) {
  const copy = cloneCards(cards);
  for (let i = copy.length - 1; i > 0; i -= 1) {
    const j = Math.floor(Math.random() * (i + 1));
    [copy[i], copy[j]] = [copy[j], copy[i]];
  }
  return copy;
}

function createDeck(state) {
  const cards = [];
  for (const suit of SUITS) {
    for (let value = 1; value <= 7; value += 1) {
      cards.push(makeCard(state, value, suit.symbol));
    }
  }
  cards.push(makeJoker(state, 1), makeJoker(state, 2));
  return shuffle(cards);
}

function createInitialState() {
  const state = {
    deck: [],
    hand: [],
    discard: [],
    selectedIds: new Set(),
    records: [],
    nextId: 1,
    activeSkill: "magic",
    characterLevel: 5,
    skillLevels: { ...DEFAULT_SKILL_LEVELS },
    skillNotice: "",
    pendingHedge: null,
    version: 0,
  };
  state.deck = createDeck(state);
  drawCards(state, 5, []);
  return state;
}

function snapshot(state) {
  return {
    deck: cloneCards(state.deck),
    hand: cloneCards(state.hand),
    discard: cloneCards(state.discard),
    selectedIds: [...state.selectedIds],
    pendingHedge: state.pendingHedge ? { ...state.pendingHedge } : null,
    activeSkill: state.activeSkill,
    characterLevel: state.characterLevel,
    skillLevels: { ...state.skillLevels },
  };
}

function restoreSnapshot(state, snap) {
  state.deck = cloneCards(snap.deck);
  state.hand = cloneCards(snap.hand);
  state.discard = cloneCards(snap.discard);
  state.selectedIds = new Set(snap.selectedIds);
  state.pendingHedge = snap.pendingHedge ? { ...snap.pendingHedge } : null;
  state.activeSkill = snap.activeSkill || state.activeSkill;
  state.characterLevel = snap.characterLevel || state.characterLevel;
  state.skillLevels = { ...state.skillLevels, ...(snap.skillLevels || {}) };
}

function drawCards(state, count, events, options = {}) {
  const drawn = [];
  while (drawn.length < count) {
    if (state.deck.length === 0) {
      if (state.discard.length === 0) break;
      const discardCount = state.discard.length;
      state.deck = shuffle(state.discard);
      state.discard = [];
      events.push("牌堆不足，已洗入弃牌堆继续抽牌。");
      if (options.recordShuffle) {
        addRecord(
          state,
          "牌堆洗牌",
          "触发抽牌时牌堆数量不足。",
          `将弃牌堆 ${discardCount} 张牌洗入牌堆后继续抽牌。`,
          null,
          { undoable: false },
        );
      }
    }
    drawn.push(state.deck.shift());
  }
  state.hand.push(...drawn);
  return drawn;
}

function selectedCards(state) {
  return state.hand.filter((card) => state.selectedIds.has(card.id));
}

function removeFromHand(state, cards) {
  const ids = new Set(cards.map((card) => card.id));
  state.hand = state.hand.filter((card) => !ids.has(card.id));
  ids.forEach((id) => state.selectedIds.delete(id));
}

function discardCards(state, cards) {
  state.discard.unshift(...cloneCards(cards));
}

function cardText(card) {
  return card.joker ? "百搭牌" : `${card.suit}${card.value}(${card.type})`;
}

function cardsText(cards) {
  return cards.length ? cards.map(cardText).join("、") : "无";
}

function countBy(items) {
  return items.reduce((acc, item) => {
    acc[item] = (acc[item] || 0) + 1;
    return acc;
  }, {});
}

function possibleAssignments(cards) {
  let assignments = [[]];
  for (const card of cards) {
    const options = card.joker
      ? SUITS.flatMap((suit) => Array.from({ length: 7 }, (_, index) => ({
          ...card,
          value: index + 1,
          suit: suit.symbol,
          type: suit.name,
          red: suit.red,
          jokerAs: true,
        })))
      : [card];
    assignments = assignments.flatMap((assignment) => options.map((option) => [...assignment, option]));
  }
  return assignments;
}

function isStraight(values) {
  const sorted = [...values].sort((a, b) => a - b);
  return sorted.every((value, index) => index === 0 || value === sorted[index - 1] + 1);
}

function sumValues(cards) {
  return cards.reduce((sum, card) => sum + card.value, 0);
}

function levelDamageBonus(state) {
  if (state.characterLevel >= 40) return 20;
  if (state.characterLevel >= 20) return 10;
  return 0;
}

function damageText(state, base, suffix) {
  const bonus = levelDamageBonus(state);
  return `${base + bonus} 点${suffix}${bonus ? `（含等级额外 +${bonus}）` : ""}`;
}

function addCombo(map, condition, name, assignedCards, effect) {
  if (!condition || map.has(name)) return;
  const assignedText = assignedCards
    .map((card) => card.jokerAs ? `百搭→${card.suit}${card.value}` : cardText(card))
    .join("、");
  map.set(name, { name, effect, assignedText });
}

function detectCombos(state, rawCards) {
  if (rawCards.length < 2 || rawCards.length > 5) return [];
  const combos = new Map();
  const hasNaturalJoker = rawCards.some((card) => card.joker);

  for (const cards of possibleAssignments(rawCards)) {
    const values = cards.map((card) => card.value);
    const suits = cards.map((card) => card.suit);
    const counts = Object.values(countBy(values)).sort((a, b) => b - a);
    const sum = sumValues(cards);
    const highest = Math.max(...values);
    const sameSuit = suits.every((suit) => suit === suits[0]);
    const noJoker = !hasNaturalJoker;

    addCombo(combos, rawCards.length === 4 && noJoker && counts[0] === 4, "王牌轰炸", cards,
      "你和场景中的每个盟友恢复 777 点 HP 和 777 点 MP；已投降的玩家角色立即恢复意识。");
    addCombo(combos, rawCards.length === 4 && isStraight(values) && sameSuit, "魔法同花顺", cards,
      `对在场每个敌人造成 ${damageText(state, 25 + sum, `${cards[0].type}伤害`)}。`);
    addCombo(combos, rawCards.length === 4 && isStraight(values), "炫目连顺", cards,
      `对在场每个敌人造成 ${damageText(state, 15 + sum, `${sum % 2 ? "暗" : "光"}属性伤害`)}。`);
    addCombo(combos, rawCards.length === 5 && counts[0] === 3 && counts[1] === 2, "状态满贯", cards,
      highest % 2 === 0
        ? "选择晕眩、颤抖、缓慢、虚弱中的两种；你和全部盟友恢复这些状态。"
        : "选择晕眩、颤抖、缓慢、虚弱中的两种；全部敌人获得这些状态。");
    addCombo(combos, rawCards.length === 3 && counts[0] === 3, "支援三条", cards,
      `你和在场每个盟友恢复 ${sum} 点 HP 和 MP。`);
    addCombo(combos, rawCards.length === 4 && counts[0] === 2 && counts[1] === 2, "双重麻烦", cards,
      `至多两名敌人受到 ${damageText(state, 10 + highest, "伤害")}；伤害属性可从结算牌花色中选择。`);
    addCombo(combos, rawCards.length === 2 && counts[0] === 2, "魔法对子", cards,
      "使用装备武器进行一次自由攻击；若造成伤害，从结算牌中选择一个花色改变本次攻击伤害属性。");
  }

  return [...combos.values()];
}

function cardsByMp(mp, sl) {
  if (mp < 10) return 0;
  return Math.min(Math.floor(Math.min(mp, 10 + sl * 5) / 5), 5);
}

function skillLevel(state, skillId) {
  return Math.max(0, Number(state.skillLevels[skillId] || 0));
}

function skillTotal(levels) {
  return Object.keys(SKILL_LIMITS).reduce((total, skillId) => total + Math.max(0, Number(levels[skillId] || 0)), 0);
}

function addRecord(state, skillName, operation, result, before, options = {}) {
  state.records.push({
    id: `r${Date.now()}-${crypto.randomBytes(4).toString("hex")}`,
    skillName,
    operation,
    result,
    before,
    undoable: options.undoable !== false,
    cancelled: false,
    time: new Date().toLocaleTimeString("zh-CN", { hour: "2-digit", minute: "2-digit" }),
  });
}

function latestUndoableRecord(state) {
  return [...state.records].reverse().find((item) => item.undoable && !item.cancelled) || null;
}

function applyAction(state, action) {
  switch (action.type) {
    case "startConflict": {
      const nextId = 1;
      state.deck = [];
      state.hand = [];
      state.discard = [];
      state.selectedIds.clear();
      state.records = [];
      state.nextId = nextId;
      state.pendingHedge = null;
      state.skillNotice = "";
      state.deck = createDeck(state);
      drawCards(state, 5, []);
      break;
    }
    case "toggleSelection": {
      if (!state.hand.some((card) => card.id === action.cardId)) break;
      if (state.selectedIds.has(action.cardId)) state.selectedIds.delete(action.cardId);
      else state.selectedIds.add(action.cardId);
      break;
    }
    case "clearSelection":
      state.selectedIds.clear();
      break;
    case "setActiveSkill":
      if (state.pendingHedge && action.skillId !== "hedge") break;
      state.activeSkill = action.skillId;
      state.selectedIds.clear();
      break;
    case "setCharacterLevel":
      state.characterLevel = Math.max(1, Math.min(50, Number(action.value || 1)));
      break;
    case "setSkillLevel":
      if (!Object.hasOwn(SKILL_LIMITS, action.skillId)) break;
      {
        const maxLevel = SKILL_LIMITS[action.skillId];
        const requested = Math.max(0, Number(action.value || 0));
        if (requested > maxLevel) {
          state.skillNotice = `${SKILL_NAMES[action.skillId]}的等级上限是 ${maxLevel}。`;
          break;
        }
        const nextLevels = { ...state.skillLevels };
        nextLevels[action.skillId] = requested;
        const total = skillTotal(nextLevels);
        if (total > 10) {
          state.skillNotice = `技能等级总和不能超过 10；当前尝试会达到 ${total}。`;
          break;
        }
        state.skillLevels[action.skillId] = requested;
        state.skillNotice = "";
      }
      break;
    case "executeMagic": {
      if (skillLevel(state, "magic") === 0) {
        state.skillNotice = "魔法卡牌未习得，不可发动该技能。";
        break;
      }
      const sl = skillLevel(state, "magic");
      const mp = Number(action.mp || 10);
      const cards = selectedCards(state);
      const required = cardsByMp(mp, sl);
      if (cards.length !== required) break;
      const before = snapshot(state);
      const combos = detectCombos(state, cards);
      const events = [];
      removeFromHand(state, cards);
      discardCards(state, cards);
      const drawn = drawCards(state, cards.length, events, { recordShuffle: true });
      addRecord(
        state,
        "魔法卡牌",
        `消耗 ${mp} MP，打出 ${cardsText(cards)}。`,
        `${combos.length ? combos.map((combo) => `${combo.name}：${combo.effect}`).join(" ") : "未触发组合。"} 抽取 ${drawn.length} 张牌。${events.join(" ")}`,
        before,
      );
      break;
    }
    case "executeFortune": {
      if (skillLevel(state, "fortune") === 0) {
        state.skillNotice = "时运再来未习得，不可发动该技能。";
        break;
      }
      const sl = skillLevel(state, "fortune");
      const cards = selectedCards(state);
      if (!cards.length || cards.length > sl) break;
      const before = snapshot(state);
      const events = [];
      removeFromHand(state, cards);
      discardCards(state, cards);
      const drawn = drawCards(state, cards.length, events, { recordShuffle: true });
      addRecord(state, "时运再来", `弃掉 ${cardsText(cards)}。`, `抽取 ${drawn.length} 张牌。${events.join(" ")}`, before);
      break;
    }
    case "executeTrap": {
      if (skillLevel(state, "trap") === 0) {
        state.skillNotice = "陷阱卡牌未习得，不可发动该技能。";
        break;
      }
      const sl = skillLevel(state, "trap");
      const suit = action.suit || "♦";
      if (!state.deck.length && !state.discard.length) break;
      const before = snapshot(state);
      const events = [];
      if (state.deck.length === 0) {
        const discardCount = state.discard.length;
        state.deck = shuffle(state.discard);
        state.discard = [];
        events.push("牌堆为空，先洗入弃牌堆。");
        addRecord(
          state,
          "牌堆洗牌",
          "触发陷阱卡牌时牌堆为空。",
          `将弃牌堆 ${discardCount} 张牌洗入牌堆后继续翻牌。`,
          null,
          { undoable: false },
        );
      }
      const card = state.deck.pop();
      discardCards(state, [card]);
      const hit = card.joker || card.suit === suit;
      addRecord(
        state,
        "陷阱卡牌",
        `宣言 ${suit}，翻开牌堆底牌并弃牌。`,
        `翻出 ${cardText(card)}，${hit ? `命中，可用自由动作施放 MP≤${sl * 5} 的法术。` : "未命中。"} ${events.join(" ")}`,
        before,
      );
      break;
    }
    case "executeHedgeDraw": {
      if (skillLevel(state, "hedge") === 0) {
        state.skillNotice = "风险对冲未习得，不可发动该技能。";
        break;
      }
      if (state.pendingHedge) break;
      const before = snapshot(state);
      const events = [];
      const drawn = drawCards(state, 1, events, { recordShuffle: true });
      state.pendingHedge = {
        before,
        drawnText: cardsText(drawn),
        events: events.join(" "),
      };
      state.activeSkill = "hedge";
      state.selectedIds.clear();
      break;
    }
    case "executeHedgeDiscard": {
      if (skillLevel(state, "hedge") === 0) {
        state.skillNotice = "风险对冲未习得，不可发动该技能。";
        break;
      }
      if (!state.pendingHedge) break;
      const cards = selectedCards(state);
      if (cards.length !== 1) break;
      const pending = state.pendingHedge;
      removeFromHand(state, cards);
      discardCards(state, cards);
      state.pendingHedge = null;
      addRecord(
        state,
        "风险对冲",
        `大成功或大失败后抽牌：${pending.drawnText}；随后弃掉 ${cardsText(cards)}。`,
        `风险对冲完成。${pending.events}`,
        pending.before,
      );
      break;
    }
    case "undoRecord": {
      const record = state.records.find((item) => item.id === action.recordId);
      const latest = latestUndoableRecord(state);
      if (!record || record.cancelled || !record.undoable || record.id !== latest?.id) break;
      restoreSnapshot(state, record.before);
      record.cancelled = true;
      state.selectedIds.clear();
      break;
    }
    default:
      return false;
  }
  state.version += 1;
  return true;
}

function getRoomState(roomId) {
  if (roomStates.has(roomId)) return roomStates.get(roomId);
  const row = getRoomStmt.get(roomId);
  const state = row ? hydrateState(JSON.parse(row.state_json)) : createInitialState();
  roomStates.set(roomId, state);
  if (!row) saveRoom(roomId, state);
  return state;
}

function saveRoom(roomId, state) {
  saveRoomStmt.run(roomId, serializeState(state));
}

function send(ws, message) {
  if (ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify(message));
}

function broadcast(roomId) {
  const state = getRoomState(roomId);
  const clients = roomClients.get(roomId) || new Set();
  for (const client of clients) {
    send(client, { type: "state", roomId, state: publicState(state) });
  }
}

function normalizeRoomId(roomId) {
  return String(roomId || "")
    .trim()
    .replace(/[^a-zA-Z0-9_-]/g, "")
    .slice(0, 48);
}

function isAllowedRoom(roomId) {
  return allowedRooms.has(roomId);
}

const app = express();
const server = http.createServer(app);
const wss = new WebSocketServer({ server, path: "/ws" });

app.use(express.static(__dirname));

app.get("/room/:roomId", (req, res) => {
  const roomId = normalizeRoomId(req.params.roomId);
  if (!isAllowedRoom(roomId)) {
    res.status(404).send("Room not found. Ask the administrator to define it in rooms.json.");
    return;
  }
  res.sendFile(path.join(__dirname, "index.html"));
});

app.get("/api/rooms/:roomId", (req, res) => {
  const roomId = normalizeRoomId(req.params.roomId);
  if (!isAllowedRoom(roomId)) {
    res.status(404).json({ error: "Room not found" });
    return;
  }
  res.json({ roomId, state: publicState(getRoomState(roomId)) });
});

wss.on("connection", (ws, req) => {
  const url = new URL(req.url, `http://${req.headers.host}`);
  const roomId = normalizeRoomId(url.searchParams.get("room"));
  if (!isAllowedRoom(roomId)) {
    send(ws, { type: "error", message: "房间不存在，请联系管理者在 rooms.json 中添加。" });
    ws.close(1008, "room not allowed");
    return;
  }
  ws.roomId = roomId;

  if (!roomClients.has(roomId)) roomClients.set(roomId, new Set());
  roomClients.get(roomId).add(ws);

  send(ws, { type: "state", roomId, state: publicState(getRoomState(roomId)) });

  ws.on("message", (raw) => {
    let message;
    try {
      message = JSON.parse(raw.toString());
    } catch {
      send(ws, { type: "error", message: "无法解析客户端消息。" });
      return;
    }

    if (message.type !== "action") return;
    const state = getRoomState(roomId);
    const changed = applyAction(state, message.action || {});
    if (!changed) {
      send(ws, { type: "state", roomId, state: publicState(state) });
      return;
    }
    saveRoom(roomId, state);
    broadcast(roomId);
  });

  ws.on("close", () => {
    const clients = roomClients.get(roomId);
    if (!clients) return;
    clients.delete(ws);
    if (!clients.size) roomClients.delete(roomId);
  });
});

server.listen(PORT, () => {
  console.log(`Card tool server running at http://localhost:${PORT}`);
});
