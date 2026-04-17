/**
 * Gridworks — expanded factory: multi-ore patches, processing chain, milestones.
 */

const TAU = Math.PI * 2;

const TILE = {
  EMPTY: 0,
  BELT: 1,
  MINER: 2,
  SMELTER: 3,
  CHEST: 4,
  PRESS: 5,
  BLAST: 6,
  ASSEMBLER: 7,
  QUARTER: 8,
};

const ITEM = {
  NONE: 0,
  IRON_ORE: 1,
  COPPER_ORE: 2,
  COAL_ORE: 3,
  IRON_INGOT: 4,
  COPPER_INGOT: 5,
  STEEL_INGOT: 6,
  PLATE: 7,
  CHIP: 8,
};

const PATCH = { NONE: 0, IRON: 1, COPPER: 2, COAL: 3 };

const D = [
  { x: 0, y: -1 },
  { x: 1, y: 0 },
  { x: 0, y: 1 },
  { x: -1, y: 0 },
];

const W = 34;
const H = 24;
const N = W * H;

const COST = {
  belt: 3,
  miner: 38,
  smelter: 62,
  chest: 12,
  press: 55,
  blast: 95,
  assembler: 110,
  quarter: 48,
};

const REFUND = 0.42;

const MILESTONES = [
  {
    title: "Foundation",
    desc: "Place 18 conveyor tiles.",
    kind: "build_belt",
    need: 18,
    reward: 120,
  },
  {
    title: "First heat",
    desc: "Produce 22 iron ingots (lifetime).",
    kind: "produced",
    item: ITEM.IRON_INGOT,
    need: 22,
    reward: 200,
  },
  {
    title: "Quarter link",
    desc: "Deliver 14 copper ingots to any Quartermaster.",
    kind: "deliver",
    item: ITEM.COPPER_INGOT,
    need: 14,
    reward: 220,
  },
  {
    title: "Stamped supply",
    desc: "Deliver 12 iron plates to any Quartermaster.",
    kind: "deliver",
    item: ITEM.PLATE,
    need: 12,
    reward: 260,
  },
  {
    title: "Heavy alloy",
    desc: "Produce 8 steel ingots (lifetime).",
    kind: "produced",
    item: ITEM.STEEL_INGOT,
    need: 8,
    reward: 280,
  },
  {
    title: "Silicon contract",
    desc: "Deliver 6 circuit chips to any Quartermaster.",
    kind: "deliver",
    item: ITEM.CHIP,
    need: 6,
    reward: 320,
  },
  {
    title: "Launch window",
    desc: "Deliver 20 steel ingots to any Quartermaster.",
    kind: "deliver",
    item: ITEM.STEEL_INGOT,
    need: 20,
    reward: 600,
    victory: true,
  },
];

/** @type {{ id:string, label:string, cost:number, tile:number, hint:string, unlockAfter:number }} */
const TOOL_DEFS = [
  { id: "belt", label: "Conveyor", cost: COST.belt, tile: TILE.BELT, hint: "Moves items along arrow.", unlockAfter: 0 },
  { id: "miner", label: "Miner", cost: COST.miner, tile: TILE.MINER, hint: "Ore patch → matching ore on belt ahead.", unlockAfter: 0 },
  { id: "smelter", label: "Smelter", cost: COST.smelter, tile: TILE.SMELTER, hint: "2 same ores → ingot. Orange out, peach in.", unlockAfter: 1 },
  { id: "chest", label: "Storage", cost: COST.chest, tile: TILE.CHEST, hint: "Stores all item types.", unlockAfter: 0 },
  { id: "press", label: "Press", cost: COST.press, tile: TILE.PRESS, hint: "1 iron ingot → 1 plate.", unlockAfter: 2 },
  { id: "blast", label: "Blast furnace", cost: COST.blast, tile: TILE.BLAST, hint: "2 iron ingots + 1 coal → steel.", unlockAfter: 3 },
  { id: "assembler", label: "Assembler", cost: COST.assembler, tile: TILE.ASSEMBLER, hint: "1 plate + 2 copper ingots → chip.", unlockAfter: 4 },
  { id: "quarter", label: "Quartermaster", cost: COST.quarter, tile: TILE.QUARTER, hint: "Counts deliveries for the active milestone.", unlockAfter: 0 },
  { id: "demolish", label: "Demolish", cost: 0, tile: -1, hint: "Remove tile (partial refund).", unlockAfter: 0 },
];

let canvas, ctx;
let cellPx = 20;
let money = 280;
let paused = false;
let showGrid = true;
let sandboxUnlocked = false;
let beltLoad = 0;
let score = 0;

let kind = new Uint8Array(N);
let rot = new Uint8Array(N);
let orePatch = new Uint8Array(N);

let smelterCnt = new Uint8Array(N);
let smelterKind = new Uint8Array(N);
let smelterProg = new Float32Array(N);

let pressBuf = new Uint8Array(N);
let pressProg = new Float32Array(N);

let blastFe = new Uint8Array(N);
let blastCoal = new Uint8Array(N);
let blastProg = new Float32Array(N);

let asmPlate = new Uint8Array(N);
let asmCu = new Uint8Array(N);
let asmProg = new Float32Array(N);

let minerCd = new Uint16Array(N);
/** @type {(null | Record<number, number>)[]} */
let chestInv = new Array(N).fill(null);

let items = new Map();
let activeTool = "belt";
let placeRot = 0;
let simAcc = 0;
let lastFrame = 0;
const MS_PER_TICK = 105;

const stats = {
  beltsPlaced: 0,
  produced: new Map(),
  qmDeliverThisMs: 0,
};

const completedMs = new Array(MILESTONES.length).fill(false);
let gameVictory = false;

function idx(x, y) {
  return y * W + x;
}

function inBounds(x, y) {
  return x >= 0 && x < W && y >= 0 && y < H;
}

function tileAt(x, y) {
  return kind[idx(x, y)];
}

function rotAt(x, y) {
  return rot[idx(x, y)];
}

function key(x, y) {
  return `${x},${y}`;
}

function itemAt(x, y) {
  return items.get(key(x, y)) ?? ITEM.NONE;
}

function setItem(x, y, t) {
  const k = key(x, y);
  if (t === ITEM.NONE) items.delete(k);
  else items.set(k, t);
}

function machineInDir(r) {
  return (r + 2) & 3;
}

function neighbor(x, y, dir) {
  return { x: x + D[dir].x, y: y + D[dir].y };
}

function toast(msg) {
  const el = document.getElementById("toast");
  el.textContent = msg;
  el.classList.add("show");
  clearTimeout(toast._t);
  toast._t = setTimeout(() => el.classList.remove("show"), 2400);
}

function addProduced(it, n = 1) {
  stats.produced.set(it, (stats.produced.get(it) ?? 0) + n);
}

function patchToOreItem(p) {
  if (p === PATCH.IRON) return ITEM.IRON_ORE;
  if (p === PATCH.COPPER) return ITEM.COPPER_ORE;
  if (p === PATCH.COAL) return ITEM.COAL_ORE;
  return ITEM.NONE;
}

function genOre() {
  orePatch.fill(PATCH.NONE);
  const layers = [
    { n: 5, r: 2.8, t: PATCH.IRON },
    { n: 4, r: 2.4, t: PATCH.COPPER },
    { n: 4, r: 2.1, t: PATCH.COAL },
  ];
  for (const layer of layers) {
    for (let b = 0; b < layer.n; b++) {
      const cx = 4 + ((Math.random() * (W - 8)) | 0);
      const cy = 4 + ((Math.random() * (H - 8)) | 0);
      const r = 1.6 + Math.random() * layer.r;
      for (let y = 0; y < H; y++) {
        for (let x = 0; x < W; x++) {
          const dx = x - cx;
          const dy = y - cy;
          if (dx * dx + dy * dy <= r * r) orePatch[idx(x, y)] = layer.t;
        }
      }
    }
  }
}

function clearMachineArrays() {
  smelterCnt.fill(0);
  smelterKind.fill(0);
  smelterProg.fill(0);
  pressBuf.fill(0);
  pressProg.fill(0);
  blastFe.fill(0);
  blastCoal.fill(0);
  blastProg.fill(0);
  asmPlate.fill(0);
  asmCu.fill(0);
  asmProg.fill(0);
  minerCd.fill(0);
  for (let i = 0; i < N; i++) chestInv[i] = null;
}

function clearFloor() {
  kind.fill(TILE.EMPTY);
  rot.fill(0);
  items.clear();
  clearMachineArrays();
  stats.beltsPlaced = 0;
  stats.produced = new Map();
  stats.qmDeliverThisMs = 0;
  completedMs.fill(false);
  gameVictory = false;
  document.getElementById("victory").classList.add("hidden");
}

function initGame() {
  genOre();
  clearFloor();
  money = 300;
  score = 0;
}

function currentMilestoneIndex() {
  for (let i = 0; i < MILESTONES.length; i++) if (!completedMs[i]) return i;
  return -1;
}

function milestonesDoneCount() {
  let n = 0;
  for (let i = 0; i < completedMs.length; i++) if (completedMs[i]) n++;
  return n;
}

function toolUnlocked(def) {
  if (sandboxUnlocked) return true;
  return milestonesDoneCount() >= def.unlockAfter;
}

function milestoneProgressPair() {
  const mi = currentMilestoneIndex();
  if (mi < 0) return [1, 1];
  const m = MILESTONES[mi];
  if (m.kind === "build_belt") return [Math.min(stats.beltsPlaced, m.need), m.need];
  if (m.kind === "produced") return [Math.min(stats.produced.get(m.item) ?? 0, m.need), m.need];
  if (m.kind === "deliver") return [Math.min(stats.qmDeliverThisMs, m.need), m.need];
  return [0, 1];
}

function tryCompleteMilestones() {
  let guard = 0;
  while (guard++ < 8) {
    const mi = currentMilestoneIndex();
    if (mi < 0) break;
    const m = MILESTONES[mi];
    let ok = false;
    if (m.kind === "build_belt") ok = stats.beltsPlaced >= m.need;
    else if (m.kind === "produced") ok = (stats.produced.get(m.item) ?? 0) >= m.need;
    else if (m.kind === "deliver") ok = stats.qmDeliverThisMs >= m.need;
    if (!ok) break;
    completedMs[mi] = true;
    money += m.reward;
    score += m.reward + 40;
    stats.qmDeliverThisMs = 0;
    toast(`Milestone: ${m.title} (+$${m.reward})`);
    if (m.victory) {
      gameVictory = true;
      document.getElementById("victory").classList.remove("hidden");
    }
    refreshToolButtons();
  }
  refreshMilestoneUI();
}

function refreshMilestoneUI() {
  const mi = currentMilestoneIndex();
  const title = document.getElementById("ms-title");
  const desc = document.getElementById("ms-desc");
  const bar = document.getElementById("ms-bar");
  const prog = document.getElementById("ms-prog");
  if (mi < 0) {
    title.textContent = "All milestones complete";
    desc.textContent = "Sandbox on — keep building, or start a new map.";
    bar.style.width = "100%";
    prog.textContent = "Done";
    return;
  }
  const m = MILESTONES[mi];
  title.textContent = m.title;
  desc.textContent = m.desc;
  const [a, b] = milestoneProgressPair();
  bar.style.width = `${(a / b) * 100}%`;
  prog.textContent = `${a} / ${b}`;
}

function refundForTile(t) {
  for (const def of TOOL_DEFS) {
    if (def.tile === t) return Math.floor(def.cost * REFUND);
  }
  return 0;
}

function demolish(x, y) {
  const i = idx(x, y);
  const t = kind[i];
  if (t === TILE.EMPTY) return;
  if (t === TILE.BELT) stats.beltsPlaced = Math.max(0, stats.beltsPlaced - 1);
  money += refundForTile(t);
  setItem(x, y, ITEM.NONE);
  kind[i] = TILE.EMPTY;
  rot[i] = 0;
  smelterCnt[i] = 0;
  smelterKind[i] = 0;
  smelterProg[i] = 0;
  pressBuf[i] = 0;
  pressProg[i] = 0;
  blastFe[i] = 0;
  blastCoal[i] = 0;
  blastProg[i] = 0;
  asmPlate[i] = 0;
  asmCu[i] = 0;
  asmProg[i] = 0;
  minerCd[i] = 0;
  chestInv[i] = null;
}

function canPlace(t, x, y) {
  if (!inBounds(x, y)) return false;
  if (tileAt(x, y) !== TILE.EMPTY) return false;
  if (t === TILE.MINER && orePatch[idx(x, y)] === PATCH.NONE) return false;
  return true;
}

function tryBuy(cost) {
  if (money < cost) {
    toast("Not enough credits.");
    return false;
  }
  money -= cost;
  return true;
}

function makeEmptyInv() {
  /** @type Record<number, number> */
  const o = {};
  for (let it = ITEM.IRON_ORE; it <= ITEM.CHIP; it++) o[it] = 0;
  return o;
}

function placeTile(t, x, y) {
  if (!canPlace(t, x, y)) {
    if (t === TILE.MINER) toast("Miners need an ore patch.");
    else toast("Blocked.");
    return;
  }
  const def = TOOL_DEFS.find((d) => d.tile === t);
  if (!def || !toolUnlocked(def)) {
    toast("Locked — complete earlier milestones or enable sandbox.");
    return;
  }
  if (def.cost > 0 && !tryBuy(def.cost)) return;
  const i = idx(x, y);
  kind[i] = t;
  rot[i] = placeRot & 3;
  if (t === TILE.CHEST) chestInv[i] = makeEmptyInv();
  if (t === TILE.BELT) stats.beltsPlaced++;
}

function handleBuildClick(x, y) {
  if (activeTool === "demolish") {
    demolish(x, y);
    return;
  }
  const def = TOOL_DEFS.find((d) => d.id === activeTool);
  if (!def || def.tile < 0) return;
  placeTile(def.tile, x, y);
}

function tryChest(x, y, it) {
  const i = idx(x, y);
  if (kind[i] !== TILE.CHEST || !chestInv[i]) return false;
  chestInv[i][it] = (chestInv[i][it] ?? 0) + 1;
  return true;
}

function tryQuarter(x, y, it, sx, sy) {
  const i = idx(x, y);
  if (kind[i] !== TILE.QUARTER) return false;
  const inD = machineInDir(rot[i]);
  const src = neighbor(x, y, inD);
  if (src.x !== sx || src.y !== sy) return false;
  const mi = currentMilestoneIndex();
  if (mi < 0) return false;
  const m = MILESTONES[mi];
  if (m.kind !== "deliver" || m.item !== it) return false;
  stats.qmDeliverThisMs++;
  score += 3;
  tryCompleteMilestones();
  return true;
}

function trySmelterOre(si, type) {
  if (type !== ITEM.IRON_ORE && type !== ITEM.COPPER_ORE) return false;
  if (smelterCnt[si] === 0) {
    smelterKind[si] = type;
    smelterCnt[si] = 1;
    return true;
  }
  if (smelterKind[si] !== type || smelterCnt[si] >= 10) return false;
  smelterCnt[si]++;
  return true;
}

function tryPressIn(pi, type) {
  if (type !== ITEM.IRON_INGOT) return false;
  if (pressBuf[pi] >= 6) return false;
  pressBuf[pi]++;
  return true;
}

function tryBlastIn(bi, type) {
  if (type === ITEM.IRON_INGOT) {
    if (blastFe[bi] >= 8) return false;
    blastFe[bi]++;
    return true;
  }
  if (type === ITEM.COAL_ORE) {
    if (blastCoal[bi] >= 6) return false;
    blastCoal[bi]++;
    return true;
  }
  return false;
}

function tryAsmIn(ai, type) {
  if (type === ITEM.PLATE) {
    if (asmPlate[ai] >= 6) return false;
    asmPlate[ai]++;
    return true;
  }
  if (type === ITEM.COPPER_INGOT) {
    if (asmCu[ai] >= 10) return false;
    asmCu[ai]++;
    return true;
  }
  return false;
}

function moveItems() {
  const entries = [...items.entries()].map(([k, t]) => {
    const [sx, sy] = k.split(",").map(Number);
    return { x: sx, y: sy, type: t };
  });
  entries.sort(() => Math.random() - 0.5);
  const want = new Map();
  const stay = (x0, y0, t0) => want.set(key(x0, y0), t0);

  for (const e of entries) {
    const { x, y, type } = e;
    const dir = tileAt(x, y) === TILE.BELT ? rotAt(x, y) : -1;
    if (dir < 0) {
      stay(x, y, type);
      continue;
    }
    const nx = x + D[dir].x;
    const ny = y + D[dir].y;
    if (!inBounds(nx, ny)) {
      stay(x, y, type);
      continue;
    }
    const nt = tileAt(nx, ny);
    const tk = key(nx, ny);

    if (nt === TILE.BELT) {
      if (want.has(tk)) {
        stay(x, y, type);
        continue;
      }
      want.set(tk, type);
      continue;
    }

    if (nt === TILE.SMELTER) {
      const si = idx(nx, ny);
      const src = neighbor(nx, ny, machineInDir(rot[si]));
      if (src.x === x && src.y === y && trySmelterOre(si, type)) continue;
      stay(x, y, type);
      continue;
    }

    if (nt === TILE.PRESS) {
      const pi = idx(nx, ny);
      const src = neighbor(nx, ny, machineInDir(rot[pi]));
      if (src.x === x && src.y === y && tryPressIn(pi, type)) continue;
      stay(x, y, type);
      continue;
    }

    if (nt === TILE.BLAST) {
      const bi = idx(nx, ny);
      const src = neighbor(nx, ny, machineInDir(rot[bi]));
      if (src.x === x && src.y === y && tryBlastIn(bi, type)) continue;
      stay(x, y, type);
      continue;
    }

    if (nt === TILE.ASSEMBLER) {
      const ai = idx(nx, ny);
      const src = neighbor(nx, ny, machineInDir(rot[ai]));
      if (src.x === x && src.y === y && tryAsmIn(ai, type)) continue;
      stay(x, y, type);
      continue;
    }

    if (nt === TILE.CHEST) {
      if (tryChest(nx, ny, type)) continue;
      stay(x, y, type);
      continue;
    }

    if (nt === TILE.QUARTER) {
      if (tryQuarter(nx, ny, type, x, y)) continue;
      stay(x, y, type);
      continue;
    }

    stay(x, y, type);
  }

  items.clear();
  for (const [k, t] of want) {
    if (t !== ITEM.NONE) items.set(k, t);
  }
}

function outputIfFree(ox, oy, it) {
  if (!inBounds(ox, oy) || itemAt(ox, oy) !== ITEM.NONE) return false;
  const ot = tileAt(ox, oy);
  if (ot === TILE.BELT) {
    setItem(ox, oy, it);
    addProduced(it, 1);
    return true;
  }
  if (ot === TILE.CHEST && chestInv[idx(ox, oy)]) {
    chestInv[idx(ox, oy)][it]++;
    addProduced(it, 1);
    return true;
  }
  return false;
}

function tickSmelters() {
  const rate = 0.052;
  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const i = idx(x, y);
      if (kind[i] !== TILE.SMELTER) continue;
      const out = neighbor(x, y, rot[i]);
      if (smelterCnt[i] >= 2) {
        smelterProg[i] += rate;
        if (smelterProg[i] >= 1) {
          const ing = smelterKind[i] === ITEM.IRON_ORE ? ITEM.IRON_INGOT : ITEM.COPPER_INGOT;
          if (outputIfFree(out.x, out.y, ing)) {
            smelterCnt[i] -= 2;
            smelterProg[i] = 0;
            if (smelterCnt[i] === 0) smelterKind[i] = 0;
          } else smelterProg[i] = 0.97;
        }
      } else smelterProg[i] *= 0.9;
    }
  }
}

function tickPress() {
  const rate = 0.07;
  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const i = idx(x, y);
      if (kind[i] !== TILE.PRESS) continue;
      const out = neighbor(x, y, rot[i]);
      if (pressBuf[i] >= 1) {
        pressProg[i] += rate;
        if (pressProg[i] >= 1) {
          if (outputIfFree(out.x, out.y, ITEM.PLATE)) {
            pressBuf[i]--;
            pressProg[i] = 0;
          } else pressProg[i] = 0.96;
        }
      } else pressProg[i] *= 0.9;
    }
  }
}

function tickBlast() {
  const rate = 0.04;
  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const i = idx(x, y);
      if (kind[i] !== TILE.BLAST) continue;
      const out = neighbor(x, y, rot[i]);
      if (blastFe[i] >= 2 && blastCoal[i] >= 1) {
        blastProg[i] += rate;
        if (blastProg[i] >= 1) {
          if (outputIfFree(out.x, out.y, ITEM.STEEL_INGOT)) {
            blastFe[i] -= 2;
            blastCoal[i]--;
            blastProg[i] = 0;
          } else blastProg[i] = 0.96;
        }
      } else blastProg[i] *= 0.9;
    }
  }
}

function tickAssembler() {
  const rate = 0.045;
  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const i = idx(x, y);
      if (kind[i] !== TILE.ASSEMBLER) continue;
      const out = neighbor(x, y, rot[i]);
      if (asmPlate[i] >= 1 && asmCu[i] >= 2) {
        asmProg[i] += rate;
        if (asmProg[i] >= 1) {
          if (outputIfFree(out.x, out.y, ITEM.CHIP)) {
            asmPlate[i]--;
            asmCu[i] -= 2;
            asmProg[i] = 0;
          } else asmProg[i] = 0.96;
        }
      } else asmProg[i] *= 0.9;
    }
  }
}

function tickMiners() {
  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const i = idx(x, y);
      if (kind[i] !== TILE.MINER) continue;
      const r = rot[i];
      const out = neighbor(x, y, r);
      if (!inBounds(out.x, out.y)) continue;
      if (tileAt(out.x, out.y) !== TILE.BELT) continue;
      if (itemAt(out.x, out.y) !== ITEM.NONE) continue;
      minerCd[i]++;
      if (minerCd[i] < 52) continue;
      minerCd[i] = 0;
      const ore = patchToOreItem(orePatch[i]);
      if (ore === ITEM.NONE) continue;
      setItem(out.x, out.y, ore);
    }
  }
}

function tick() {
  if (paused) return;
  moveItems();
  tickSmelters();
  tickPress();
  tickBlast();
  tickAssembler();
  tickMiners();
  tryCompleteMilestones();
  beltLoad = items.size;
}

function itemColor(t) {
  switch (t) {
    case ITEM.IRON_ORE:
      return "#fca5a5";
    case ITEM.COPPER_ORE:
      return "#67e8f9";
    case ITEM.COAL_ORE:
      return "#94a3b8";
    case ITEM.IRON_INGOT:
      return "#e2e8f0";
    case ITEM.COPPER_INGOT:
      return "#f59e0b";
    case ITEM.STEEL_INGOT:
      return "#7dd3fc";
    case ITEM.PLATE:
      return "#c4b5fd";
    case ITEM.CHIP:
      return "#86efac";
    default:
      return "#fff";
  }
}

function drawItem(px, py, cw, ch, t) {
  const c = itemColor(t);
  ctx.fillStyle = c;
  if (t === ITEM.IRON_ORE || t === ITEM.COPPER_ORE || t === ITEM.COAL_ORE) {
    ctx.beginPath();
    ctx.arc(px, py, cw * 0.2, 0, TAU);
    ctx.fill();
  } else if (t === ITEM.CHIP) {
    ctx.fillRect(px - cw * 0.2, py - ch * 0.15, cw * 0.4, ch * 0.3);
    ctx.strokeStyle = "#166534";
    ctx.lineWidth = 1;
    ctx.strokeRect(px - cw * 0.2, py - ch * 0.15, cw * 0.4, ch * 0.3);
  } else {
    ctx.fillRect(px - cw * 0.18, py - ch * 0.12, cw * 0.36, ch * 0.24);
    ctx.strokeStyle = "rgba(0,0,0,0.35)";
    ctx.strokeRect(px - cw * 0.18, py - ch * 0.12, cw * 0.36, ch * 0.24);
  }
}

function patchColor(p) {
  if (p === PATCH.IRON) return "rgba(248, 113, 113, 0.18)";
  if (p === PATCH.COPPER) return "rgba(34, 211, 238, 0.16)";
  if (p === PATCH.COAL) return "rgba(148, 163, 184, 0.2)";
  return "#11161d";
}

function draw() {
  const pad = 1;
  const cw = cellPx;
  const ch = cellPx;
  ctx.save();
  ctx.fillStyle = "#0a0d12";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const px = pad + x * cw;
      const py = pad + y * ch;
      const i = idx(x, y);
      const t = kind[i];
      const p = orePatch[i];

      ctx.fillStyle = patchColor(p);
      ctx.fillRect(px, py, cw - 1, ch - 1);

      if (t === TILE.BELT) {
        ctx.fillStyle = "#1e293b";
        ctx.fillRect(px + 2, py + 2, cw - 5, ch - 5);
        const r = rot[i];
        ctx.strokeStyle = "#64748b";
        ctx.lineWidth = 2;
        const cx = px + cw * 0.5;
        const cy = py + ch * 0.5;
        ctx.beginPath();
        ctx.moveTo(cx - D[r].x * 4, cy - D[r].y * 4);
        ctx.lineTo(cx + D[r].x * 7, cy + D[r].y * 7);
        ctx.stroke();
        ctx.fillStyle = "#94a3b8";
        ctx.beginPath();
        ctx.arc(cx + D[r].x * 5, cy + D[r].y * 5, 2.5, 0, TAU);
        ctx.fill();
      } else if (t === TILE.MINER) {
        ctx.fillStyle = "#334155";
        ctx.fillRect(px + 2, py + 2, cw - 5, ch - 5);
        ctx.fillStyle = p === PATCH.COPPER ? "#22d3ee" : p === PATCH.COAL ? "#94a3b8" : "#f87171";
        ctx.beginPath();
        ctx.arc(px + cw * 0.5, py + ch * 0.5, 5, 0, TAU);
        ctx.fill();
        const r = rot[i];
        ctx.fillStyle = "#93c5fd";
        ctx.fillRect(px + cw * 0.5 + D[r].x * 7 - 2, py + ch * 0.5 + D[r].y * 7 - 2, 4, 4);
      } else if (t === TILE.SMELTER) {
        ctx.fillStyle = "#431407";
        ctx.fillRect(px + 2, py + 2, cw - 5, ch - 5);
        const r = rot[i];
        ctx.strokeStyle = "#fb923c";
        ctx.lineWidth = 2;
        const cx = px + cw * 0.5;
        const cy = py + ch * 0.5;
        ctx.beginPath();
        ctx.moveTo(cx, cy);
        ctx.lineTo(cx + D[r].x * 9, cy + D[r].y * 9);
        ctx.stroke();
        ctx.fillStyle = "#fed7aa";
        const id = machineInDir(r);
        ctx.fillRect(px + cw * 0.5 + D[id].x * 7 - 2, py + ch * 0.5 + D[id].y * 7 - 2, 4, 4);
        if (smelterCnt[i] > 0) {
          ctx.fillStyle = "#fff";
          ctx.font = `600 ${Math.max(7, cw * 0.28)}px IBM Plex Mono, monospace`;
          ctx.textAlign = "center";
          ctx.fillText(String(smelterCnt[i]), cx, cy + 3);
        }
      } else if (t === TILE.CHEST) {
        ctx.fillStyle = "#172554";
        ctx.fillRect(px + 2, py + 2, cw - 5, ch - 5);
        const inv = chestInv[i];
        if (inv) {
          const tot =
            (inv[ITEM.IRON_ORE] ?? 0) +
            (inv[ITEM.COPPER_ORE] ?? 0) +
            (inv[ITEM.IRON_INGOT] ?? 0) +
            (inv[ITEM.COPPER_INGOT] ?? 0) +
            (inv[ITEM.STEEL_INGOT] ?? 0) +
            (inv[ITEM.PLATE] ?? 0) +
            (inv[ITEM.CHIP] ?? 0);
          ctx.fillStyle = "#94a3b8";
          ctx.font = `${Math.max(6, cw * 0.24)}px IBM Plex Mono, monospace`;
          ctx.textAlign = "center";
          ctx.fillText(String(tot), px + cw * 0.5, py + ch * 0.55);
        }
      } else if (t === TILE.PRESS) {
        ctx.fillStyle = "#3f3f46";
        ctx.fillRect(px + 2, py + 2, cw - 5, ch - 5);
        drawMachineIO(px, py, cw, ch, rot[i], "#a78bfa");
        if (pressBuf[i] > 0) {
          ctx.fillStyle = "#fff";
          ctx.font = `${Math.max(6, cw * 0.26)}px IBM Plex Mono, monospace`;
          ctx.textAlign = "center";
          ctx.fillText(String(pressBuf[i]), px + cw * 0.5, py + ch * 0.52);
        }
      } else if (t === TILE.BLAST) {
        ctx.fillStyle = "#1c1917";
        ctx.fillRect(px + 2, py + 2, cw - 5, ch - 5);
        drawMachineIO(px, py, cw, ch, rot[i], "#38bdf8");
        ctx.fillStyle = "#e7e5e4";
        ctx.font = `${Math.max(5, cw * 0.22)}px IBM Plex Mono, monospace`;
        ctx.textAlign = "center";
        ctx.fillText(`${blastFe[i]}/${blastCoal[i]}`, px + cw * 0.5, py + ch * 0.52);
      } else if (t === TILE.ASSEMBLER) {
        ctx.fillStyle = "#14532d";
        ctx.fillRect(px + 2, py + 2, cw - 5, ch - 5);
        drawMachineIO(px, py, cw, ch, rot[i], "#4ade80");
        ctx.fillStyle = "#dcfce7";
        ctx.font = `${Math.max(5, cw * 0.22)}px IBM Plex Mono, monospace`;
        ctx.textAlign = "center";
        ctx.fillText(`${asmPlate[i]}|${asmCu[i]}`, px + cw * 0.5, py + ch * 0.52);
      } else if (t === TILE.QUARTER) {
        ctx.fillStyle = "#3b0764";
        ctx.fillRect(px + 2, py + 2, cw - 5, ch - 5);
        drawMachineIO(px, py, cw, ch, rot[i], "#d8b4fe");
        ctx.fillStyle = "#fae8ff";
        ctx.font = `${Math.max(6, cw * 0.24)}px IBM Plex Mono, monospace`;
        ctx.textAlign = "center";
        ctx.fillText("QM", px + cw * 0.5, py + ch * 0.52);
      }

      if (showGrid) {
        ctx.strokeStyle = "rgba(48, 54, 61, 0.28)";
        ctx.lineWidth = 1;
        ctx.strokeRect(px - 0.5, py - 0.5, cw, ch);
      }
    }
  }

  for (const [k, t] of items) {
    const [sx, sy] = k.split(",").map(Number);
    const px = pad + sx * cw + cw * 0.5;
    const py = pad + sy * ch + ch * 0.5;
    drawItem(px, py, cw, ch, t);
  }

  ctx.restore();
}

function drawMachineIO(px, py, cw, ch, r, accent) {
  const cx = px + cw * 0.5;
  const cy = py + ch * 0.5;
  ctx.strokeStyle = accent;
  ctx.lineWidth = 2;
  ctx.beginPath();
  ctx.moveTo(cx, cy);
  ctx.lineTo(cx + D[r].x * 8, cy + D[r].y * 8);
  ctx.stroke();
  const id = machineInDir(r);
  ctx.fillStyle = "#fde68a";
  ctx.fillRect(px + cw * 0.5 + D[id].x * 6 - 2, py + ch * 0.5 + D[id].y * 6 - 2, 4, 4);
}

function resize() {
  const stage = document.getElementById("stage");
  const sw = stage.clientWidth - 20;
  const sh = stage.clientHeight - 20;
  const needW = W * 18 + 2;
  const needH = H * 18 + 2;
  const scale = Math.min(sw / needW, sh / needH, 1.15);
  cellPx = Math.max(14, Math.floor(18 * scale));
  canvas.width = W * cellPx + 2;
  canvas.height = H * cellPx + 2;
}

function screenToCell(clientX, clientY) {
  const r = canvas.getBoundingClientRect();
  const sx = clientX - r.left;
  const sy = clientY - r.top;
  const x = Math.floor((sx - 1) / cellPx);
  const y = Math.floor((sy - 1) / cellPx);
  if (!inBounds(x, y)) return null;
  return { x, y };
}

function refreshToolButtons() {
  document.querySelectorAll(".tool-btn").forEach((b) => {
    const id = b.dataset.tool;
    const def = TOOL_DEFS.find((d) => d.id === id);
    if (!def) return;
    const ok = toolUnlocked(def);
    b.classList.toggle("locked", !ok && !sandboxUnlocked);
    b.disabled = false;
  });
}

function bindUI() {
  const tb = document.getElementById("tool-buttons");
  tb.innerHTML = "";
  TOOL_DEFS.forEach((def, ix) => {
    const hot = def.id === "demolish" ? "0" : String(ix + 1);
    const b = document.createElement("button");
    b.type = "button";
    b.className = "tool-btn" + (activeTool === def.id ? " active" : "");
    b.dataset.tool = def.id;
    const lock = !toolUnlocked(def);
    if (lock) b.classList.add("locked");
    b.innerHTML = `<span><span class="hotkey">${hot}</span>${def.label}</span>${def.cost ? `<span class="cost">$${def.cost}</span>` : ""}`;
    b.addEventListener("click", () => {
      if (!toolUnlocked(def) && !sandboxUnlocked) {
        toast("Complete earlier milestones — or enable sandbox.");
        return;
      }
      activeTool = def.id;
      document.querySelectorAll(".tool-btn").forEach((x) => x.classList.remove("active"));
      b.classList.add("active");
      document.getElementById("tool-hint").textContent = def.hint;
    });
    tb.appendChild(b);
  });

  document.getElementById("grid-lines").addEventListener("change", (e) => {
    showGrid = e.target.checked;
  });

  document.getElementById("sandbox").addEventListener("change", (e) => {
    sandboxUnlocked = e.target.checked;
    refreshToolButtons();
    toast(sandboxUnlocked ? "Sandbox: all buildings unlocked." : "Progression gates on.");
  });

  document.getElementById("btn-pause").addEventListener("click", (e) => {
    paused = !paused;
    e.target.textContent = paused ? "Resume" : "Pause";
  });

  document.getElementById("btn-clear").addEventListener("click", () => {
    if (!confirm("Clear the entire floor and reset milestones?")) return;
    clearFloor();
    money = 300;
    score = 0;
    refreshMilestoneUI();
    refreshToolButtons();
    toast("Fresh floor.");
  });

  document.getElementById("vic-new").addEventListener("click", () => {
    initGame();
    refreshMilestoneUI();
    refreshToolButtons();
    document.getElementById("victory").classList.add("hidden");
    toast("New ore map.");
  });

  window.addEventListener("keydown", (e) => {
    const k = e.key.toLowerCase();
    if (k === "r") {
      placeRot = (placeRot + 1) & 3;
      toast(`Output → ${["N", "E", "S", "W"][placeRot]}`);
    } else if (k === "0") {
      selectToolById("demolish");
    } else if (k >= "1" && k <= "9") {
      const ix = +k - 1;
      if (TOOL_DEFS[ix]) selectToolById(TOOL_DEFS[ix].id);
    }
  });

  function selectToolById(id) {
    const def = TOOL_DEFS.find((d) => d.id === id);
    if (!def) return;
    if (!toolUnlocked(def) && !sandboxUnlocked) {
      toast("Locked — milestone or sandbox.");
      return;
    }
    activeTool = id;
    document.querySelectorAll(".tool-btn").forEach((b) => {
      b.classList.toggle("active", b.dataset.tool === id);
    });
    document.getElementById("tool-hint").textContent = def.hint;
  }

  setInterval(() => {
    document.getElementById("money").textContent = String(money);
    document.getElementById("stat-score").textContent = String(score);
    document.getElementById("stat-belt").textContent = String(beltLoad);
    refreshMilestoneUI();
  }, 200);
}

function loop(ts) {
  if (!lastFrame) lastFrame = ts;
  simAcc += ts - lastFrame;
  lastFrame = ts;
  if (!paused && !gameVictory) {
    while (simAcc >= MS_PER_TICK) {
      tick();
      simAcc -= MS_PER_TICK;
    }
  } else {
    simAcc = 0;
  }
  draw();
  requestAnimationFrame(loop);
}

function init() {
  canvas = document.getElementById("game");
  ctx = canvas.getContext("2d");
  initGame();
  refreshMilestoneUI();

  canvas.addEventListener("pointerdown", (e) => {
    if (gameVictory) return;
    const c = screenToCell(e.clientX, e.clientY);
    if (!c) return;
    handleBuildClick(c.x, c.y);
  });

  window.addEventListener("resize", () => {
    resize();
    draw();
  });

  bindUI();
  resize();
  requestAnimationFrame(loop);
}

init();
