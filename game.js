/**
 * Gridworks — rebuilt core: flat buffers, deterministic belts, cached terrain draw.
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

const ITEM_MAX = ITEM.CHIP;
const CHEST_STRIDE = ITEM_MAX + 1;

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
  { title: "Foundation", desc: "Place 18 conveyor tiles.", kind: "build_belt", need: 18, reward: 120 },
  { title: "First heat", desc: "Produce 22 iron ingots (lifetime).", kind: "produced", item: ITEM.IRON_INGOT, need: 22, reward: 200 },
  { title: "Quarter link", desc: "Deliver 14 copper ingots to any Quartermaster.", kind: "deliver", item: ITEM.COPPER_INGOT, need: 14, reward: 220 },
  { title: "Stamped supply", desc: "Deliver 12 iron plates to any Quartermaster.", kind: "deliver", item: ITEM.PLATE, need: 12, reward: 260 },
  { title: "Heavy alloy", desc: "Produce 8 steel ingots (lifetime).", kind: "produced", item: ITEM.STEEL_INGOT, need: 8, reward: 280 },
  { title: "Silicon contract", desc: "Deliver 6 circuit chips to any Quartermaster.", kind: "deliver", item: ITEM.CHIP, need: 6, reward: 320 },
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

const TOOL_DEFS = [
  { id: "belt", label: "Conveyor", cost: COST.belt, tile: TILE.BELT, hint: "Moves items along arrow.", unlockAfter: 0 },
  { id: "miner", label: "Miner", cost: COST.miner, tile: TILE.MINER, hint: "Ore patch → matching ore on belt ahead.", unlockAfter: 0 },
  { id: "smelter", label: "Smelter", cost: COST.smelter, tile: TILE.SMELTER, hint: "2 same ores → ingot. Orange out, peach in.", unlockAfter: 1 },
  { id: "chest", label: "Storage", cost: COST.chest, tile: TILE.CHEST, hint: "Stores all item types.", unlockAfter: 0 },
  { id: "press", label: "Press", cost: COST.press, tile: TILE.PRESS, hint: "1 iron ingot → 1 plate.", unlockAfter: 2 },
  { id: "blast", label: "Blast furnace", cost: COST.blast, tile: TILE.BLAST, hint: "2 iron ingots + 1 coal → steel.", unlockAfter: 3 },
  { id: "assembler", label: "Assembler", cost: COST.assembler, tile: TILE.ASSEMBLER, hint: "1 plate + 2 copper ingots → chip.", unlockAfter: 4 },
  { id: "quarter", label: "Quartermaster", cost: COST.quarter, tile: TILE.QUARTER, hint: "Deliveries for the active milestone (peach = in).", unlockAfter: 0 },
  { id: "demolish", label: "Demolish", cost: 0, tile: -1, hint: "Remove tile (partial refund).", unlockAfter: 0 },
];

const TOOL_BY_TILE = new Map(TOOL_DEFS.filter((d) => d.tile >= 0).map((d) => [d.tile, d]));

let canvas, ctx;
let cellPx = 20;
let money = 300;
let paused = false;
let showGrid = true;
let sandboxUnlocked = false;
let beltLoad = 0;
let score = 0;

let kind = new Uint8Array(N);
let rot = new Uint8Array(N);
let orePatch = new Uint8Array(N);

let itemIn = new Uint8Array(N);
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

let chestInv = new Uint16Array(N * CHEST_STRIDE);

let activeTool = "belt";
let placeRot = 0;
let simAcc = 0;
let lastFrame = 0;
const MS_PER_TICK = 105;

const stats = {
  beltsPlaced: 0,
  produced: new Uint32Array(ITEM_MAX + 1),
  qmDeliverThisMs: 0,
};

const completedMs = new Uint8Array(MILESTONES.length);
let gameVictory = false;

let terrainCanvas = null;
let terrainDirty = true;

const moveOrder = new Uint32Array(N);
const nextItem = new Uint8Array(N);
const destClaim = new Uint8Array(N);

function idx(x, y) {
  return y * W + x;
}

function inBounds(x, y) {
  return x >= 0 && x < W && y >= 0 && y < H;
}

function tileAtI(i) {
  return kind[i];
}

function rotAtI(i) {
  return rot[i];
}

function machineInDir(r) {
  return (r + 2) & 3;
}

function neighbor(x, y, dir) {
  return { x: x + D[dir].x, y: y + D[dir].y };
}

function toast(msg) {
  const el = document.getElementById("toast");
  if (!el) return;
  el.textContent = msg;
  el.classList.add("show");
  clearTimeout(toast._t);
  toast._t = setTimeout(() => el.classList.remove("show"), 2400);
}

function addProduced(it, n = 1) {
  if (it >= 1 && it <= ITEM_MAX) stats.produced[it] += n;
}

function chestPtr(i) {
  return i * CHEST_STRIDE;
}

function chestAdd(i, it) {
  const p = chestPtr(i);
  chestInv[p + it]++;
}

function chestTotal(i) {
  let s = 0;
  const p = chestPtr(i);
  for (let t = 1; t <= ITEM_MAX; t++) s += chestInv[p + t];
  return s;
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
      const r2 = r * r;
      const x0 = Math.max(0, Math.floor(cx - r - 1));
      const y0 = Math.max(0, Math.floor(cy - r - 1));
      const x1 = Math.min(W - 1, Math.ceil(cx + r + 1));
      const y1 = Math.min(H - 1, Math.ceil(cy + r + 1));
      for (let y = y0; y <= y1; y++) {
        const dy = y - cy;
        for (let x = x0; x <= x1; x++) {
          const dx = x - cx;
          if (dx * dx + dy * dy <= r2) orePatch[idx(x, y)] = layer.t;
        }
      }
    }
  }
}

function clearMachineState() {
  itemIn.fill(0);
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
  chestInv.fill(0);
}

function clearFloor() {
  kind.fill(TILE.EMPTY);
  rot.fill(0);
  clearMachineState();
  stats.beltsPlaced = 0;
  stats.produced.fill(0);
  stats.qmDeliverThisMs = 0;
  completedMs.fill(0);
  gameVictory = false;
  terrainDirty = true;
  const vic = document.getElementById("victory");
  if (vic) vic.classList.add("hidden");
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
  for (let i = 0; i < completedMs.length; i++) n += completedMs[i];
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
  if (m.kind === "produced") return [Math.min(stats.produced[m.item] ?? 0, m.need), m.need];
  if (m.kind === "deliver") return [Math.min(stats.qmDeliverThisMs, m.need), m.need];
  return [0, 1];
}

function tryCompleteMilestones() {
  let guard = 0;
  while (guard++ < 12) {
    const mi = currentMilestoneIndex();
    if (mi < 0) break;
    const m = MILESTONES[mi];
    let ok = false;
    if (m.kind === "build_belt") ok = stats.beltsPlaced >= m.need;
    else if (m.kind === "produced") ok = stats.produced[m.item] >= m.need;
    else if (m.kind === "deliver") ok = stats.qmDeliverThisMs >= m.need;
    if (!ok) break;
    completedMs[mi] = 1;
    money += m.reward;
    score += m.reward + 40;
    stats.qmDeliverThisMs = 0;
    toast(`Milestone: ${m.title} (+$${m.reward})`);
    if (m.victory) {
      gameVictory = true;
      const vic = document.getElementById("victory");
      if (vic) vic.classList.remove("hidden");
    }
    refreshToolButtons();
  }
  refreshMilestoneUI();
}

function refreshMilestoneUI() {
  const title = document.getElementById("ms-title");
  const desc = document.getElementById("ms-desc");
  const bar = document.getElementById("ms-bar");
  const prog = document.getElementById("ms-prog");
  if (!title) return;
  const mi = currentMilestoneIndex();
  if (mi < 0) {
    title.textContent = "All milestones complete";
    desc.textContent = "Enable sandbox or clear floor for a new run.";
    bar.style.width = "100%";
    prog.textContent = "Done";
    return;
  }
  const m = MILESTONES[mi];
  title.textContent = m.title;
  desc.textContent = m.desc;
  const [a, b] = milestoneProgressPair();
  bar.style.width = `${(a / Math.max(1, b)) * 100}%`;
  prog.textContent = `${a} / ${b}`;
}

function refundForTile(t) {
  const def = TOOL_BY_TILE.get(t);
  return def ? Math.floor(def.cost * REFUND) : 0;
}

function demolish(x, y) {
  const i = idx(x, y);
  const t = kind[i];
  if (t === TILE.EMPTY) return;
  if (t === TILE.BELT) stats.beltsPlaced = Math.max(0, stats.beltsPlaced - 1);
  money += refundForTile(t);
  itemIn[i] = 0;
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
  chestInv.fill(0, chestPtr(i), CHEST_STRIDE);
  terrainDirty = true;
}

function canPlace(t, x, y) {
  if (!inBounds(x, y)) return false;
  const i = idx(x, y);
  if (kind[i] !== TILE.EMPTY) return false;
  if (t === TILE.MINER && orePatch[i] === PATCH.NONE) return false;
  return true;
}

function tryBuy(cost) {
  if (cost <= 0) return true;
  if (money < cost) {
    toast("Not enough credits.");
    return false;
  }
  money -= cost;
  return true;
}

function placeTile(t, x, y) {
  if (!canPlace(t, x, y)) {
    toast(t === TILE.MINER ? "Miners need an ore patch." : "Blocked.");
    return;
  }
  const def = TOOL_BY_TILE.get(t);
  if (!def || !toolUnlocked(def)) {
    toast("Locked — milestones or sandbox.");
    return;
  }
  if (!tryBuy(def.cost)) return;
  const i = idx(x, y);
  kind[i] = t;
  rot[i] = placeRot & 3;
  if (t === TILE.BELT) stats.beltsPlaced++;
  terrainDirty = true;
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

function tryQuarter(i, it, fromI) {
  if (tileAtI(i) !== TILE.QUARTER) return false;
  const inD = machineInDir(rot[i]);
  const mx = i % W;
  const my = (i / W) | 0;
  const nx = mx + D[inD].x;
  const ny = my + D[inD].y;
  const fromX = fromI % W;
  const fromY = (fromI / W) | 0;
  if (nx !== fromX || ny !== fromY) return false;
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
  if (type !== ITEM.IRON_INGOT || pressBuf[pi] >= 6) return false;
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

function buildMoveOrder() {
  let c = 0;
  for (let i = 0; i < N; i++) {
    if (itemIn[i] !== 0 && kind[i] === TILE.BELT) moveOrder[c++] = i;
  }
  const sub = moveOrder.subarray(0, c);
  sub.sort((a, b) => b - a);
  return c;
}

function tryConsumeAt(fromI, it, nx, ny) {
  const ni = idx(nx, ny);
  const nt = tileAtI(ni);
  const fx = fromI % W;
  const fy = (fromI / W) | 0;

  if (nt === TILE.SMELTER) {
    const src = neighbor(nx, ny, machineInDir(rot[ni]));
    if (src.x === fx && src.y === fy && trySmelterOre(ni, it)) return true;
  } else if (nt === TILE.PRESS) {
    const src = neighbor(nx, ny, machineInDir(rot[ni]));
    if (src.x === fx && src.y === fy && tryPressIn(ni, it)) return true;
  } else if (nt === TILE.BLAST) {
    const src = neighbor(nx, ny, machineInDir(rot[ni]));
    if (src.x === fx && src.y === fy && tryBlastIn(ni, it)) return true;
  } else if (nt === TILE.ASSEMBLER) {
    const src = neighbor(nx, ny, machineInDir(rot[ni]));
    if (src.x === fx && src.y === fy && tryAsmIn(ni, it)) return true;
  } else if (nt === TILE.CHEST) {
    chestAdd(ni, it);
    return true;
  } else if (nt === TILE.QUARTER) {
    if (tryQuarter(ni, it, fromI)) return true;
  }
  return false;
}

function moveItems() {
  const nMove = buildMoveOrder();
  nextItem.fill(0);
  destClaim.fill(0);

  for (let i = 0; i < N; i++) {
    const it = itemIn[i];
    if (it !== 0 && kind[i] !== TILE.BELT) nextItem[i] = it;
  }

  for (let k = 0; k < nMove; k++) {
    const i = moveOrder[k];
    const it = itemIn[i];
    if (it === 0) continue;

    const r = rotAtI(i);
    const x = i % W;
    const y = (i / W) | 0;
    const nx = x + D[r].x;
    const ny = y + D[r].y;
    if (!inBounds(nx, ny)) {
      nextItem[i] = it;
      continue;
    }
    const ni = idx(nx, ny);
    const nt = tileAtI(ni);

    if (nt === TILE.BELT) {
      if (destClaim[ni]) {
        nextItem[i] = it;
        continue;
      }
      destClaim[ni] = 1;
      nextItem[ni] = it;
      continue;
    }

    if (tryConsumeAt(i, it, nx, ny)) continue;
    nextItem[i] = it;
  }

  itemIn.set(nextItem);
}

function outputIfFree(ox, oy, it) {
  if (!inBounds(ox, oy)) return false;
  const oi = idx(ox, oy);
  if (itemIn[oi] !== 0) return false;
  const ot = tileAtI(oi);
  if (ot === TILE.BELT) {
    itemIn[oi] = it;
    addProduced(it, 1);
    return true;
  }
  if (ot === TILE.CHEST) {
    chestAdd(oi, it);
    addProduced(it, 1);
    return true;
  }
  return false;
}

function tickMachines() {
  const rs = 0.052;
  const rp = 0.07;
  const rb = 0.04;
  const ra = 0.045;

  for (let i = 0; i < N; i++) {
    const t = kind[i];
    if (t === TILE.SMELTER) {
      const x = i % W;
      const y = (i / W) | 0;
      const out = neighbor(x, y, rot[i]);
      if (smelterCnt[i] >= 2) {
        smelterProg[i] += rs;
        if (smelterProg[i] >= 1) {
          const ing = smelterKind[i] === ITEM.IRON_ORE ? ITEM.IRON_INGOT : ITEM.COPPER_INGOT;
          if (outputIfFree(out.x, out.y, ing)) {
            smelterCnt[i] -= 2;
            smelterProg[i] = 0;
            if (smelterCnt[i] === 0) smelterKind[i] = 0;
          } else smelterProg[i] = 0.97;
        }
      } else smelterProg[i] *= 0.9;
    } else if (t === TILE.PRESS) {
      const x = i % W;
      const y = (i / W) | 0;
      const out = neighbor(x, y, rot[i]);
      if (pressBuf[i] >= 1) {
        pressProg[i] += rp;
        if (pressProg[i] >= 1) {
          if (outputIfFree(out.x, out.y, ITEM.PLATE)) {
            pressBuf[i]--;
            pressProg[i] = 0;
          } else pressProg[i] = 0.96;
        }
      } else pressProg[i] *= 0.9;
    } else if (t === TILE.BLAST) {
      const x = i % W;
      const y = (i / W) | 0;
      const out = neighbor(x, y, rot[i]);
      if (blastFe[i] >= 2 && blastCoal[i] >= 1) {
        blastProg[i] += rb;
        if (blastProg[i] >= 1) {
          if (outputIfFree(out.x, out.y, ITEM.STEEL_INGOT)) {
            blastFe[i] -= 2;
            blastCoal[i]--;
            blastProg[i] = 0;
          } else blastProg[i] = 0.96;
        }
      } else blastProg[i] *= 0.9;
    } else if (t === TILE.ASSEMBLER) {
      const x = i % W;
      const y = (i / W) | 0;
      const out = neighbor(x, y, rot[i]);
      if (asmPlate[i] >= 1 && asmCu[i] >= 2) {
        asmProg[i] += ra;
        if (asmProg[i] >= 1) {
          if (outputIfFree(out.x, out.y, ITEM.CHIP)) {
            asmPlate[i]--;
            asmCu[i] -= 2;
            asmProg[i] = 0;
          } else asmProg[i] = 0.96;
        }
      } else asmProg[i] *= 0.9;
    } else if (t === TILE.MINER) {
      const x = i % W;
      const y = (i / W) | 0;
      const out = neighbor(x, y, rot[i]);
      if (!inBounds(out.x, out.y)) continue;
      const oi = idx(out.x, out.y);
      if (kind[oi] !== TILE.BELT || itemIn[oi] !== 0) continue;
      minerCd[i]++;
      if (minerCd[i] < 52) continue;
      minerCd[i] = 0;
      const ore = patchToOreItem(orePatch[i]);
      if (ore !== ITEM.NONE) itemIn[oi] = ore;
    }
  }
}

function tick() {
  if (paused) return;
  moveItems();
  tickMachines();
  tryCompleteMilestones();
  beltLoad = 0;
  for (let i = 0; i < N; i++) if (itemIn[i]) beltLoad++;
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
  ctx.fillStyle = itemColor(t);
  if (t <= ITEM.COAL_ORE) {
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

function ensureTerrainCache() {
  if (!terrainDirty && terrainCanvas) return;
  if (!terrainCanvas) terrainCanvas = document.createElement("canvas");
  terrainCanvas.width = W * cellPx + 2;
  terrainCanvas.height = H * cellPx + 2;
  const tctx = terrainCanvas.getContext("2d");
  const pad = 1;
  const cw = cellPx;
  const ch = cellPx;
  tctx.fillStyle = "#0a0d12";
  tctx.fillRect(0, 0, terrainCanvas.width, terrainCanvas.height);
  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const px = pad + x * cw;
      const py = pad + y * ch;
      const p = orePatch[idx(x, y)];
      tctx.fillStyle = patchColor(p);
      tctx.fillRect(px, py, cw - 1, ch - 1);
    }
  }
  terrainDirty = false;
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

function draw() {
  ensureTerrainCache();
  const pad = 1;
  const cw = cellPx;
  const ch = cellPx;
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.drawImage(terrainCanvas, 0, 0);

  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const px = pad + x * cw;
      const py = pad + y * ch;
      const i = idx(x, y);
      const t = kind[i];
      if (t === TILE.EMPTY) {
        if (showGrid) {
          ctx.strokeStyle = "rgba(48, 54, 61, 0.28)";
          ctx.lineWidth = 1;
          ctx.strokeRect(px - 0.5, py - 0.5, cw, ch);
        }
        continue;
      }

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
        const p = orePatch[i];
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
        ctx.fillStyle = "#94a3b8";
        ctx.font = `${Math.max(6, cw * 0.24)}px IBM Plex Mono, monospace`;
        ctx.textAlign = "center";
        ctx.fillText(String(chestTotal(i)), px + cw * 0.5, py + ch * 0.55);
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

  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const i = idx(x, y);
      const it = itemIn[i];
      if (it === 0) continue;
      const px = pad + x * cw + cw * 0.5;
      const py = pad + y * ch + ch * 0.5;
      drawItem(px, py, cw, ch, it);
    }
  }
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
  terrainDirty = true;
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
  });
}

function bindUI() {
  const tb = document.getElementById("tool-buttons");
  tb.innerHTML = "";
  TOOL_DEFS.forEach((def, ix) => {
    const b = document.createElement("button");
    b.type = "button";
    b.className = "tool-btn" + (activeTool === def.id ? " active" : "");
    b.dataset.tool = def.id;
    if (!toolUnlocked(def)) b.classList.add("locked");
    const hk = def.id === "demolish" ? "0" : ix < 8 ? String(ix + 1) : "—";
    b.innerHTML = `<span><span class="hotkey">${hk}</span>${def.label}</span>${def.cost ? `<span class="cost">$${def.cost}</span>` : ""}`;
    b.addEventListener("click", () => {
      if (!toolUnlocked(def) && !sandboxUnlocked) {
        toast("Complete milestones — or sandbox.");
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
    toast(sandboxUnlocked ? "Sandbox: all buildings unlocked." : "Progression on.");
  });

  document.getElementById("btn-pause").addEventListener("click", (e) => {
    paused = !paused;
    e.target.textContent = paused ? "Resume" : "Pause";
  });

  document.getElementById("btn-clear").addEventListener("click", () => {
    if (!confirm("Clear floor and reset milestones?")) return;
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
    toast("New map.");
  });

  window.addEventListener("keydown", (e) => {
    const k = e.key.toLowerCase();
    if (k === "r") {
      placeRot = (placeRot + 1) & 3;
      toast(`Output → ${["N", "E", "S", "W"][placeRot]}`);
    } else if (k === "0") {
      selectToolById("demolish");
    } else if (k >= "1" && k <= "8") {
      const ix = +k - 1;
      if (TOOL_DEFS[ix]) selectToolById(TOOL_DEFS[ix].id);
    }
  });

  function selectToolById(id) {
    const def = TOOL_DEFS.find((d) => d.id === id);
    if (!def) return;
    if (!toolUnlocked(def) && !sandboxUnlocked) {
      toast("Locked.");
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
  }, 350);
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
