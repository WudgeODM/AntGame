/**
 * Ant Realm — surface survival (rivals, predators) + anthill base building.
 */

const TAU = Math.PI * 2;
const N_COLONIES = 3;
const PLAYER = 0;

const WORLD = Object.freeze({ w: 2400, h: 2400 });
const GRID = Object.freeze({ w: 320, h: 320 });
const CELL = Object.freeze({ x: WORLD.w / GRID.w, y: WORLD.h / GRID.h });

const STATE = Object.freeze({ FORAGE: 0, RETURN: 1 });

const HILL_W = 9;
const HILL_H = 7;
const TILE = Object.freeze({ ROCK: 0, TUNNEL: 1, QUEEN: 2, GRANARY: 3, NURSERY: 4 });

const cfg = {
  antSpeed: 60,
  maxTurn: 2.25,
  sensorDist: 26,
  sensorSpread: 0.52,
  carryDeposit: 2.6,
  forageDeposit: 0.11,
  nestHomeEmit: 3.9,
  nestRadius: 40,
  pickFood: 5.5,
  maxAntsPerColony: 420,
  spawnCost: 68,
  initialPlayerAnts: 220,
  initialEnemyAnts: 130,
  rainWipe: 0.52,
  combatRange: 9,
  combatChance: 0.14,
  bugSpeed: 48,
  bugEatRadius: 11,
  bugDamageRadius: 15,
  bugHp: 92,
  bugDpsFromAnts: 24,
  bugSpawnInterval: 42,
  bugMax: 6,
  chitinPerKill: 14,
  baseFoodCap: 160,
  foodPerGranary: 95,
};

let canvas, ctx;
let dpr = 1;
let view = { x: WORLD.w * 0.5, y: WORLD.h * 0.5, zoom: 0.52 };
let dragging = { pan: false, paint: false, button: 0, lx: 0, ly: 0 };
let brush = "none";
let brushRadius = 36;
let paused = false;
let speedIdx = 2;
const speedSteps = [0.25, 0.5, 1, 2, 3];
let uiEvap = 0.35;
let uiDiffuse = 0.4;
let uiNoise = 0.2;

let foodPher, homePherLayers, scratchA, scratchB;
let foodAmount;
let rocks;
let pheromap;

/** @type {{x:number,y:number}[]} */
let nests = [];
/** @type {{stored:number,gathered:number,chitin:number,color:string,enemy:boolean}[]} */
let colonies = [];

let ants;
/** @type {{x:number,y:number,a:number,hp:number,cool:number}[]} */
let predators = [];
let bugSpawnAcc = 0;

let lastTs = 0;
let raf = 0;
let avgTrail = 0;

let scene = "surface";
let hillTool = "dig";
/** @type {{cells:Uint8Array}} */
let hill;

let gameOver = false;

const BUCK = 88;
let BW = 1;
let BH = 1;
/** @type {number[][]} */
let buckets;

function clamp(v, a, b) {
  return Math.max(a, Math.min(b, v));
}

function worldToGrid(wx, wy) {
  const gx = clamp((wx / WORLD.w) * GRID.w, 0, GRID.w - 1);
  const gy = clamp((wy / WORLD.h) * GRID.h, 0, GRID.h - 1);
  return { gx, gy };
}

function idx(gx, gy) {
  return (gy | 0) * GRID.w + (gx | 0);
}

function bilinear(grid, wx, wy) {
  const fx = (wx / WORLD.w) * GRID.w - 0.5;
  const fy = (wy / WORLD.h) * GRID.h - 0.5;
  const x0 = clamp(Math.floor(fx), 0, GRID.w - 2);
  const y0 = clamp(Math.floor(fy), 0, GRID.h - 2);
  const x1 = x0 + 1;
  const y1 = y0 + 1;
  const tx = fx - x0;
  const ty = fy - y0;
  const i00 = idx(x0, y0);
  const i10 = idx(x1, y0);
  const i01 = idx(x0, y1);
  const i11 = idx(x1, y1);
  return (
    grid[i00] * (1 - tx) * (1 - ty) +
    grid[i10] * tx * (1 - ty) +
    grid[i01] * (1 - tx) * ty +
    grid[i11] * tx * ty
  );
}

function rockAtWorld(wx, wy) {
  const { gx, gy } = worldToGrid(wx, wy);
  return rocks[idx(gx | 0, gy | 0)] === 1;
}

function dist2(ax, ay, bx, by) {
  const dx = ax - bx;
  const dy = ay - by;
  return dx * dx + dy * dy;
}

function initBuckets() {
  BW = Math.ceil(WORLD.w / BUCK) + 2;
  BH = Math.ceil(WORLD.h / BUCK) + 2;
  const n = BW * BH;
  buckets = new Array(n);
  for (let i = 0; i < n; i++) buckets[i] = [];
}

function bucketIndex(ax, ay) {
  const bx = clamp((ax / BUCK) | 0, 0, BW - 1);
  const by = clamp((ay / BUCK) | 0, 0, BH - 1);
  return by * BW + bx;
}

function clearBuckets() {
  for (let i = 0; i < buckets.length; i++) buckets[i].length = 0;
}

function initGrids() {
  const n = GRID.w * GRID.h;
  foodPher = new Float32Array(n);
  scratchA = new Float32Array(n);
  scratchB = new Float32Array(n);
  homePherLayers = [];
  for (let c = 0; c < N_COLONIES; c++) homePherLayers.push(new Float32Array(n));
  foodAmount = new Float32Array(n);
  rocks = new Uint8Array(n);
}

function clearPheromones(factor = 1) {
  const n = GRID.w * GRID.h;
  for (let i = 0; i < n; i++) {
    foodPher[i] *= factor;
    for (let c = 0; c < N_COLONIES; c++) homePherLayers[c][i] *= factor;
  }
}

function emitNestHome(dt) {
  const r = cfg.nestRadius / Math.max(CELL.x, CELL.y);
  const addBase = cfg.nestHomeEmit * dt;
  for (let ci = 0; ci < N_COLONIES; ci++) {
    const nest = nests[ci];
    const homePher = homePherLayers[ci];
    const cx = (nest.x / WORLD.w) * GRID.w;
    const cy = (nest.y / WORLD.h) * GRID.h;
    const r2 = r * r;
    const x0 = Math.max(0, Math.floor(cx - r - 1));
    const y0 = Math.max(0, Math.floor(cy - r - 1));
    const x1 = Math.min(GRID.w - 1, Math.ceil(cx + r + 1));
    const y1 = Math.min(GRID.h - 1, Math.ceil(cy + r + 1));
    for (let gy = y0; gy <= y1; gy++) {
      const dy = gy - cy;
      for (let gx = x0; gx <= x1; gx++) {
        const dx = gx - cx;
        if (dx * dx + dy * dy <= r2) {
          const i = idx(gx, gy);
          if (!rocks[i]) homePher[i] += addBase * (ci === PLAYER ? 1.05 : 0.92);
        }
      }
    }
  }
}

function diffuseOneLayer(layer) {
  const evap = clamp(0.985 - uiEvap * 0.028, 0.9, 0.999);
  const diff = uiDiffuse * 0.2;
  const w = GRID.w;
  const h = GRID.h;
  const src = layer;
  const dst = scratchA;
  for (let y = 1; y < h - 1; y++) {
    const row = y * w;
    for (let x = 1; x < w - 1; x++) {
      const i = row + x;
      if (rocks[i]) {
        dst[i] = 0;
        continue;
      }
      const v = src[i];
      const avg =
        (src[i - 1] + src[i + 1] + src[i - w] + src[i + w] + src[i - w - 1] + src[i - w + 1] + src[i + w - 1] + src[i + w + 1]) * (1 / 8);
      dst[i] = (v * (1 - diff) + avg * diff) * evap;
    }
  }
  for (let y = 1; y < h - 1; y++) {
    const row = y * w;
    for (let x = 1; x < w - 1; x++) {
      const i = row + x;
      layer[i] = dst[i];
    }
  }
}

function diffuseFoodLayer() {
  const evap = clamp(0.985 - uiEvap * 0.028, 0.9, 0.999);
  const diff = uiDiffuse * 0.2;
  const w = GRID.w;
  const h = GRID.h;
  const src = foodPher;
  const dst = scratchB;
  for (let y = 1; y < h - 1; y++) {
    const row = y * w;
    for (let x = 1; x < w - 1; x++) {
      const i = row + x;
      if (rocks[i]) {
        dst[i] = 0;
        continue;
      }
      const v = src[i];
      const avg =
        (src[i - 1] + src[i + 1] + src[i - w] + src[i + w] + src[i - w - 1] + src[i - w + 1] + src[i + w - 1] + src[i + w + 1]) * (1 / 8);
      dst[i] = (v * (1 - diff) + avg * diff) * evap;
    }
  }
  for (let y = 1; y < h - 1; y++) {
    const row = y * w;
    for (let x = 1; x < w - 1; x++) {
      const i = row + x;
      foodPher[i] = dst[i];
    }
  }
}

function evaporateAndDiffuse() {
  diffuseFoodLayer();
  for (let c = 0; c < N_COLONIES; c++) diffuseOneLayer(homePherLayers[c]);
}

function paintCircle(wx, wy, rWorld, mode) {
  const rgx = rWorld / CELL.x;
  const rgy = rWorld / CELL.y;
  const cx = (wx / WORLD.w) * GRID.w;
  const cy = (wy / WORLD.h) * GRID.h;
  const x0 = clamp(Math.floor(cx - rgx), 0, GRID.w - 1);
  const y0 = clamp(Math.floor(cy - rgy), 0, GRID.h - 1);
  const x1 = clamp(Math.ceil(cx + rgx), 0, GRID.w - 1);
  const y1 = clamp(Math.ceil(cy + rgy), 0, GRID.h - 1);
  for (let gy = y0; gy <= y1; gy++) {
    const dy = (gy + 0.5 - cy) / Math.max(0.001, rgy);
    for (let gx = x0; gx <= x1; gx++) {
      const dx = (gx + 0.5 - cx) / Math.max(0.001, rgx);
      if (dx * dx + dy * dy > 1) continue;
      const i = idx(gx, gy);
      if (mode === "food") {
        foodAmount[i] = clamp(foodAmount[i] + 16 + Math.random() * 22, 0, 200);
        rocks[i] = 0;
      } else if (mode === "rock") {
        rocks[i] = 1;
        foodAmount[i] = 0;
        foodPher[i] = 0;
        for (let c = 0; c < N_COLONIES; c++) homePherLayers[c][i] = 0;
      } else if (mode === "erase") {
        rocks[i] = 0;
        foodAmount[i] = 0;
        foodPher[i] = 0;
        for (let c = 0; c < N_COLONIES; c++) homePherLayers[c][i] = 0;
      }
    }
  }
}

function placeNests() {
  nests = [
    { x: WORLD.w * 0.5, y: WORLD.h * 0.5 },
    { x: WORLD.w * 0.22, y: WORLD.h * 0.72 },
    { x: WORLD.w * 0.78, y: WORLD.h * 0.28 },
  ];
  colonies = [
    { stored: 28, gathered: 0, chitin: 6, color: "#a7f3d0", enemy: false },
    { stored: 40, gathered: 0, chitin: 0, color: "#fda4af", enemy: true },
    { stored: 40, gathered: 0, chitin: 0, color: "#93c5fd", enemy: true },
  ];
}

function initHill() {
  const n = HILL_W * HILL_H;
  const cells = new Uint8Array(n);
  cells.fill(TILE.ROCK);
  const qx = (HILL_W / 2) | 0;
  const qy = (HILL_H / 2) | 0;
  const qi = qy * HILL_W + qx;
  cells[qi] = TILE.QUEEN;
  const open = [
    [0, -1],
    [0, 1],
    [-1, 0],
    [1, 0],
  ];
  for (const [dx, dy] of open) {
    const x = qx + dx;
    const y = qy + dy;
    if (x < 0 || x >= HILL_W || y < 0 || y >= HILL_H) continue;
    cells[y * HILL_W + x] = TILE.TUNNEL;
  }
  hill = { cells };
}

function hillIdx(x, y) {
  return y * HILL_W + x;
}

function countHillTiles(t) {
  let n = 0;
  for (let i = 0; i < hill.cells.length; i++) if (hill.cells[i] === t) n++;
  return n;
}

function foodCapFromHill() {
  const g = countHillTiles(TILE.GRANARY);
  return cfg.baseFoodCap + g * cfg.foodPerGranary;
}

function spawnDiscountFromHill() {
  const n = countHillTiles(TILE.NURSERY);
  return Math.min(46, n * 12);
}

function clampPlayerFoodToCap() {
  const cap = foodCapFromHill();
  if (colonies[PLAYER].stored > cap) colonies[PLAYER].stored = cap;
}

function effectiveSpawnCost(ci) {
  if (ci !== PLAYER) return 56;
  return Math.max(18, cfg.spawnCost - spawnDiscountFromHill());
}

function seedWorld() {
  gameOver = false;
  document.getElementById("gameover").classList.add("hidden");

  foodPher.fill(0);
  for (let c = 0; c < N_COLONIES; c++) homePherLayers[c].fill(0);
  foodAmount.fill(0);
  rocks.fill(0);

  placeNests();
  initHill();
  clampPlayerFoodToCap();

  const clusters = 10 + ((Math.random() * 5) | 0);
  const avoidR = 280;
  for (let c = 0; c < clusters; c++) {
    let wx;
    let wy;
    let guard = 0;
    do {
      wx = 200 + Math.random() * (WORLD.w - 400);
      wy = 200 + Math.random() * (WORLD.h - 400);
      guard++;
    } while (guard < 50 && nests.some((n) => dist2(wx, wy, n.x, n.y) < avoidR * avoidR));
    paintCircle(wx, wy, 65 + Math.random() * 120, "food");
  }

  for (let k = 0; k < 26; k++) {
    const wx = 140 + Math.random() * (WORLD.w - 280);
    const wy = 140 + Math.random() * (WORLD.h - 280);
    paintCircle(wx, wy, 20 + Math.random() * 65, "rock");
  }

  ants = [];
  spawnAntsForColony(PLAYER, cfg.initialPlayerAnts);
  spawnAntsForColony(1, cfg.initialEnemyAnts);
  spawnAntsForColony(2, cfg.initialEnemyAnts);

  predators = [];
  bugSpawnAcc = 0;
  renderHillBoard();
}

function spawnAntsForColony(ci, count) {
  const nest = nests[ci];
  let have = 0;
  for (let i = 0; i < ants.length; i++) if (ants[i].c === ci) have++;
  const cap = cfg.maxAntsPerColony - have;
  const n = Math.min(count, cap);
  for (let i = 0; i < n; i++) {
    const t = Math.random() * TAU;
    const d = Math.random() * cfg.nestRadius * 0.5;
    ants.push({
      x: nest.x + Math.cos(t) * d,
      y: nest.y + Math.sin(t) * d,
      a: Math.random() * TAU,
      s: STATE.FORAGE,
      carry: 0,
      c: ci,
    });
  }
}

function countColonyAnts(ci) {
  let n = 0;
  for (let i = 0; i < ants.length; i++) if (ants[i].c === ci) n++;
  return n;
}

function tryColonySpawn(ci) {
  const have = countColonyAnts(ci);
  if (have >= cfg.maxAntsPerColony) return;
  const col = colonies[ci];
  const cost = effectiveSpawnCost(ci);
  if (col.stored < cost) return;
  col.stored -= cost;
  spawnAntsForColony(ci, 1);
  if (ci === PLAYER) toast("New worker hatched.");
}

function depositPher(wx, wy, grid, amount) {
  const { gx, gy } = worldToGrid(wx, wy);
  const i = idx(gx | 0, gy | 0);
  if (!rocks[i]) grid[i] += amount;
}

function sampleSensors(ant, grid) {
  const d = cfg.sensorDist;
  const spread = cfg.sensorSpread;
  const noise = (Math.random() * 2 - 1) * uiNoise * 6;
  const left = bilinear(grid, ant.x + Math.cos(ant.a - spread) * d, ant.y + Math.sin(ant.a - spread) * d) + noise;
  const mid = bilinear(grid, ant.x + Math.cos(ant.a) * d, ant.y + Math.sin(ant.a) * d) + noise;
  const right = bilinear(grid, ant.x + Math.cos(ant.a + spread) * d, ant.y + Math.sin(ant.a + spread) * d) + noise;
  return { left, mid, right };
}

function steerFromSamples(ant, left, mid, right, wander) {
  let turn = 0;
  const best = Math.max(left, mid, right);
  if (best > 0.08) {
    if (best === left) turn = -cfg.maxTurn;
    else if (best === right) turn = cfg.maxTurn;
    else turn = (Math.random() * 2 - 1) * cfg.maxTurn * 0.22;
  } else {
    turn = (Math.random() * 2 - 1) * wander;
  }
  ant.a += clamp(turn, -cfg.maxTurn, cfg.maxTurn);
}

function updateAnt(ant, dt) {
  const homePher = homePherLayers[ant.c];
  const nest = nests[ant.c];
  const col = colonies[ant.c];
  const speed = cfg.antSpeed * dt;

  if (ant.s === STATE.FORAGE) {
    const f = sampleSensors(ant, foodPher);
    steerFromSamples(ant, f.left, f.mid, f.right, cfg.maxTurn * 0.82);

    const pick = bilinear(foodAmount, ant.x, ant.y);
    if (pick > 0.35 && ant.carry === 0) {
      const { gx, gy } = worldToGrid(ant.x, ant.y);
      const i = idx(gx | 0, gy | 0);
      const take = Math.min(pick, cfg.pickFood);
      foodAmount[i] -= take;
      ant.carry = 1;
      ant.s = STATE.RETURN;
    }

    depositPher(ant.x, ant.y, homePher, cfg.forageDeposit * dt);
  } else {
    const h = sampleSensors(ant, homePher);
    steerFromSamples(ant, h.left, h.mid, h.right, cfg.maxTurn * 0.42);

    const nx = nest.x - ant.x;
    const ny = nest.y - ant.y;
    const desired = Math.atan2(ny, nx);
    let diff = desired - ant.a;
    while (diff > Math.PI) diff -= TAU;
    while (diff < -Math.PI) diff += TAU;
    ant.a += clamp(diff, -cfg.maxTurn * 1.12, cfg.maxTurn * 1.12) * 0.54;

    depositPher(ant.x, ant.y, foodPher, cfg.carryDeposit * dt);
  }

  let nx = ant.x + Math.cos(ant.a) * speed;
  let ny = ant.y + Math.sin(ant.a) * speed;

  if (nx < 8 || nx > WORLD.w - 8 || ny < 8 || ny > WORLD.h - 8) {
    ant.a += Math.PI * 0.5 + (Math.random() - 0.5) * 0.75;
    nx = clamp(nx, 8, WORLD.w - 8);
    ny = clamp(ny, 8, WORLD.h - 8);
  }

  if (rockAtWorld(nx, ny)) {
    ant.a += (Math.random() < 0.5 ? 1 : -1) * (1.05 + Math.random() * 1.1);
  } else {
    ant.x = nx;
    ant.y = ny;
  }

  if (ant.s === STATE.RETURN && ant.carry) {
    const dNest = Math.sqrt(dist2(ant.x, ant.y, nest.x, nest.y));
    if (dNest < cfg.nestRadius * 0.52) {
      if (ant.c === PLAYER) {
        const cap = foodCapFromHill();
        if (col.stored >= cap) {
          /* granaries full — keep hauling until there is room */
        } else {
          ant.carry = 0;
          ant.s = STATE.FORAGE;
          col.stored += 1;
          col.gathered += 1;
        }
      } else {
        ant.carry = 0;
        ant.s = STATE.FORAGE;
        col.stored += 1;
        col.gathered += 1;
      }
    }
  }
}

function resolveCombat() {
  const r2 = cfg.combatRange * cfg.combatRange;
  clearBuckets();
  for (let i = 0; i < ants.length; i++) {
    buckets[bucketIndex(ants[i].x, ants[i].y)].push(i);
  }
  const dead = new Set();
  for (let i = 0; i < ants.length; i++) {
    if (dead.has(i)) continue;
    const a = ants[i];
    const bx = clamp((a.x / BUCK) | 0, 0, BW - 1);
    const by = clamp((a.y / BUCK) | 0, 0, BH - 1);
    for (let oy = -1; oy <= 1; oy++) {
      for (let ox = -1; ox <= 1; ox++) {
        const nx = bx + ox;
        const ny = by + oy;
        if (nx < 0 || ny < 0 || nx >= BW || ny >= BH) continue;
        const arr = buckets[ny * BW + nx];
        for (let k = 0; k < arr.length; k++) {
          const j = arr[k];
          if (j <= i || dead.has(j)) continue;
          const b = ants[j];
          if (a.c === b.c) continue;
          if (dist2(a.x, a.y, b.x, b.y) > r2) continue;
          if (Math.random() > cfg.combatChance) continue;
          dead.add(Math.random() < 0.5 ? i : j);
          if (dead.has(i)) break;
        }
      }
      if (dead.has(i)) break;
    }
  }
  if (!dead.size) return;
  const next = [];
  for (let i = 0; i < ants.length; i++) if (!dead.has(i)) next.push(ants[i]);
  ants = next;
}

function updatePredators(dt) {
  const eatR2 = cfg.bugEatRadius * cfg.bugEatRadius;
  const dmgR2 = cfg.bugDamageRadius * cfg.bugDamageRadius;
  for (let p = predators.length - 1; p >= 0; p--) {
    const b = predators[p];
    let best = -1;
    let bestD = 1e15;
    for (let i = 0; i < ants.length; i++) {
      const a = ants[i];
      const d = dist2(a.x, a.y, b.x, b.y);
      if (d < bestD) {
        bestD = d;
        best = i;
      }
    }
    if (best >= 0) {
      const t = ants[best];
      const ang = Math.atan2(t.y - b.y, t.x - b.x);
      let diff = ang - b.a;
      while (diff > Math.PI) diff -= TAU;
      while (diff < -Math.PI) diff += TAU;
      b.a += clamp(diff, -2.8 * dt, 2.8 * dt) * 1.15;
    } else {
      b.a += (Math.random() - 0.5) * 0.9 * dt;
    }
    const sp = cfg.bugSpeed * dt;
    b.x += Math.cos(b.a) * sp;
    b.y += Math.sin(b.a) * sp;
    b.x = clamp(b.x, 20, WORLD.w - 20);
    b.y = clamp(b.y, 20, WORLD.h - 20);

    let near = 0;
    for (let i = ants.length - 1; i >= 0; i--) {
      const a = ants[i];
      const d = dist2(a.x, a.y, b.x, b.y);
      if (d <= eatR2) {
        ants.splice(i, 1);
        b.hp = Math.min(cfg.bugHp, b.hp + 6);
        break;
      }
      if (d <= dmgR2) near++;
    }
    b.hp -= near * cfg.bugDpsFromAnts * dt;
    if (b.hp <= 0) {
      colonies[PLAYER].chitin += cfg.chitinPerKill;
      predators.splice(p, 1);
      toast("Predator fell — chitin salvaged.");
    }
  }

  bugSpawnAcc += dt;
  if (predators.length < cfg.bugMax && bugSpawnAcc > cfg.bugSpawnInterval) {
    bugSpawnAcc = 0;
    const edge = (Math.random() * 4) | 0;
    let x;
    let y;
    if (edge === 0) {
      x = Math.random() * WORLD.w;
      y = 30;
    } else if (edge === 1) {
      x = WORLD.w - 30;
      y = Math.random() * WORLD.h;
    } else if (edge === 2) {
      x = Math.random() * WORLD.w;
      y = WORLD.h - 30;
    } else {
      x = 30;
      y = Math.random() * WORLD.h;
    }
    predators.push({ x, y, a: Math.random() * TAU, hp: cfg.bugHp, cool: 0 });
  }
}

function checkGameOver() {
  if (gameOver) return;
  const pl = colonies[PLAYER];
  const workers = countColonyAnts(PLAYER);
  if (workers === 0 && pl.stored < effectiveSpawnCost(PLAYER)) {
    gameOver = true;
    document.getElementById("gameover").classList.remove("hidden");
  }
}

function enemyEconomyTick(dt) {
  void dt;
  for (let ci = 1; ci < N_COLONIES; ci++) {
    if (Math.random() < 0.04) colonies[ci].stored += 1;
    tryColonySpawn(ci);
  }
}

function updateSimulation(dt, steps) {
  emitNestHome(dt);
  for (let s = 0; s < steps; s++) evaporateAndDiffuse();

  let sum = 0;
  let pc = 0;
  for (let i = 0; i < ants.length; i++) {
    const ant = ants[i];
    updateAnt(ant, dt);
    if (ant.c === PLAYER) {
      pc++;
      const g = worldToGrid(ant.x, ant.y);
      sum += foodPher[idx(g.gx | 0, g.gy | 0)];
    }
  }
  avgTrail = pc ? sum / pc : 0;

  resolveCombat();
  updatePredators(dt);
  enemyEconomyTick(dt);

  tryColonySpawn(PLAYER);
  checkGameOver();
}

function buildPheromap() {
  if (!pheromap) {
    pheromap = document.createElement("canvas");
    pheromap.width = GRID.w;
    pheromap.height = GRID.h;
  }
  const pctx = pheromap.getContext("2d", { willReadFrequently: true });
  const img = pctx.createImageData(GRID.w, GRID.h);
  const d = img.data;
  const hp0 = homePherLayers[0];
  const hp1 = homePherLayers[1];
  const hp2 = homePherLayers[2];
  for (let i = 0; i < GRID.w * GRID.h; i++) {
    const di = i * 4;
    const f = Math.min(1, foodPher[i] * 0.034);
    const h0 = Math.min(1, hp0[i] * 0.027);
    const h1 = Math.min(1, hp1[i] * 0.018);
    const h2 = Math.min(1, hp2[i] * 0.018);
    const fa = foodAmount[i];
    const foodTint = Math.min(1, fa * 0.0085);
    if (rocks[i]) {
      d[di] = 38;
      d[di + 1] = 42;
      d[di + 2] = 50;
      d[di + 3] = 255;
    } else {
      d[di] = Math.floor(14 + f * 210 + h1 * 90 + h2 * 40 + foodTint * 200);
      d[di + 1] = Math.floor(16 + h0 * 200 + f * 28 + foodTint * 160 + h2 * 70);
      d[di + 2] = Math.floor(26 + h0 * 55 + h2 * 180 + f * 36 + foodTint * 35);
      d[di + 3] = Math.floor(38 + (f + h0 + (h1 + h2) * 0.45 + foodTint * 0.55) * 195);
    }
  }
  pctx.putImageData(img, 0, 0);
}

function drawWorld() {
  const vw = canvas.width / dpr;
  const vh = canvas.height / dpr;
  ctx.save();
  ctx.scale(dpr, dpr);
  ctx.fillStyle = "#06080c";
  ctx.fillRect(0, 0, vw, vh);

  ctx.save();
  ctx.translate(vw * 0.5, vh * 0.5);
  ctx.scale(view.zoom, view.zoom);
  ctx.translate(-view.x, -view.y);

  buildPheromap();
  ctx.imageSmoothingEnabled = true;
  ctx.drawImage(pheromap, 0, 0, WORLD.w, WORLD.h);

  for (let ci = 0; ci < N_COLONIES; ci++) {
    const n = nests[ci];
    const hue = ci === 0 ? "52, 211, 153" : ci === 1 ? "251, 113, 133" : "147, 197, 253";
    const mound = ctx.createRadialGradient(n.x, n.y, 0, n.x, n.y, cfg.nestRadius * 2.1);
    mound.addColorStop(0, `rgba(${hue}, 0.32)`);
    mound.addColorStop(0.5, `rgba(${hue}, 0.14)`);
    mound.addColorStop(1, `rgba(${hue}, 0)`);
    ctx.fillStyle = mound;
    ctx.beginPath();
    ctx.arc(n.x, n.y, cfg.nestRadius * 2.1, 0, TAU);
    ctx.fill();

    ctx.strokeStyle = ci === 0 ? "rgba(167, 243, 208, 0.55)" : "rgba(254, 202, 202, 0.45)";
    ctx.lineWidth = (ci === 0 ? 2.2 : 1.6) / view.zoom;
    ctx.beginPath();
    ctx.arc(n.x, n.y, cfg.nestRadius, 0, TAU);
    ctx.stroke();

    if (ci === 0) {
      ctx.fillStyle = "rgba(15, 23, 42, 0.55)";
      ctx.font = `${12 / view.zoom}px JetBrains Mono, monospace`;
      ctx.textAlign = "center";
      ctx.fillText("YOU", n.x, n.y - cfg.nestRadius - 8 / view.zoom);
    }
  }

  ctx.lineWidth = 1.05 / view.zoom;
  for (let i = 0; i < ants.length; i++) {
    const ant = ants[i];
    const len = ant.s === STATE.RETURN ? 6.8 : 5.9;
    const wx = ant.x;
    const wy = ant.y;
    const x2 = wx + Math.cos(ant.a) * len;
    const y2 = wy + Math.sin(ant.a) * len;
    const col = colonies[ant.c]?.color ?? "#e2e8f0";
    ctx.strokeStyle = ant.s === STATE.RETURN ? col : `${col}cc`;
    ctx.globalAlpha = ant.c === PLAYER ? 1 : 0.82;
    ctx.beginPath();
    ctx.moveTo(wx, wy);
    ctx.lineTo(x2, y2);
    ctx.stroke();
    ctx.fillStyle = col;
    ctx.beginPath();
    ctx.arc(wx, wy, ant.c === PLAYER ? 1.4 / view.zoom : 1.15 / view.zoom, 0, TAU);
    ctx.fill();
    ctx.globalAlpha = 1;
  }

  for (let p = 0; p < predators.length; p++) {
    const b = predators[p];
    ctx.save();
    ctx.translate(b.x, b.y);
    ctx.rotate(b.a);
    ctx.strokeStyle = "rgba(30, 20, 18, 0.95)";
    ctx.fillStyle = "rgba(55, 38, 32, 0.92)";
    ctx.lineWidth = 2.2 / view.zoom;
    ctx.beginPath();
    ctx.ellipse(0, 0, 10 / view.zoom, 7 / view.zoom, 0, 0, TAU);
    ctx.fill();
    ctx.stroke();
    for (let k = -2; k <= 2; k++) {
      ctx.beginPath();
      ctx.moveTo(-4 / view.zoom, k * 3.5);
      ctx.lineTo(-18 / view.zoom, k * 5.5 - 2);
      ctx.stroke();
      ctx.beginPath();
      ctx.moveTo(4 / view.zoom, k * 3.5);
      ctx.lineTo(18 / view.zoom, k * 5.5 - 2);
      ctx.stroke();
    }
    ctx.restore();
  }

  ctx.restore();
  ctx.restore();
}

function screenToWorld(sx, sy) {
  const vw = canvas.width / dpr;
  const vh = canvas.height / dpr;
  const wx = (sx - vw * 0.5) / view.zoom + view.x;
  const wy = (sy - vh * 0.5) / view.zoom + view.y;
  return { wx, wy };
}

function resize() {
  dpr = Math.min(2, window.devicePixelRatio || 1);
  canvas.width = Math.floor(canvas.clientWidth * dpr);
  canvas.height = Math.floor(canvas.clientHeight * dpr);
}

function loop(ts) {
  raf = requestAnimationFrame(loop);
  const raw = Math.min(0.05, (ts - lastTs) / 1000 || 0);
  lastTs = ts;
  if (!paused && !gameOver) {
    const mul = speedSteps[speedIdx];
    const dt = raw * mul;
    const steps = mul >= 2 ? 2 : 1;
    updateSimulation(dt, steps);
  }
  drawWorld();
}

function setScene(next) {
  scene = next;
  const hillEl = document.getElementById("hill-screen");
  const canvasEl = document.getElementById("c");
  if (next === "hill") {
    hillEl.classList.remove("hidden");
    hillEl.setAttribute("aria-hidden", "false");
    canvasEl.classList.add("no-interact");
    syncHillHud();
    renderHillBoard();
  } else {
    hillEl.classList.add("hidden");
    hillEl.setAttribute("aria-hidden", "true");
    canvasEl.classList.remove("no-interact");
  }
}

function syncHillHud() {
  const pl = colonies[PLAYER];
  document.getElementById("hill-food").textContent = String(Math.floor(pl.stored));
  document.getElementById("hill-cap").textContent = String(foodCapFromHill());
  document.getElementById("hill-chitin").textContent = String(Math.floor(pl.chitin));
}

function hillOpenNeighbors(x, y) {
  const dirs = [
    [0, -1],
    [0, 1],
    [-1, 0],
    [1, 0],
  ];
  for (const [dx, dy] of dirs) {
    const nx = x + dx;
    const ny = y + dy;
    if (nx < 0 || nx >= HILL_W || ny < 0 || ny >= HILL_H) continue;
    const t = hill.cells[hillIdx(nx, ny)];
    if (t !== TILE.ROCK) return true;
  }
  return false;
}

function tryHillAction(x, y) {
  const pl = colonies[PLAYER];
  const i = hillIdx(x, y);
  const t = hill.cells[i];

  if (hillTool === "dig") {
    if (t !== TILE.ROCK) {
      toast("Dig soil only.");
      return;
    }
    if (!hillOpenNeighbors(x, y)) {
      toast("Dig next to an open chamber.");
      return;
    }
    if (pl.stored < 8 || pl.chitin < 5) {
      toast("Need 8 food and 5 chitin to dig.");
      return;
    }
    pl.stored -= 8;
    pl.chitin -= 5;
    hill.cells[i] = TILE.TUNNEL;
    toast("Tunnel excavated.");
  } else if (hillTool === "granary") {
    if (t !== TILE.TUNNEL) {
      toast("Granaries need a cleared tunnel tile.");
      return;
    }
    if (pl.stored < 30 || pl.chitin < 12) {
      toast("Need 30 food and 12 chitin.");
      return;
    }
    pl.stored -= 30;
    pl.chitin -= 12;
    hill.cells[i] = TILE.GRANARY;
    toast("Granary built — larger food cap.");
  } else if (hillTool === "nursery") {
    if (t !== TILE.TUNNEL) {
      toast("Nurseries need a cleared tunnel tile.");
      return;
    }
    if (pl.stored < 45 || pl.chitin < 18) {
      toast("Need 45 food and 18 chitin.");
      return;
    }
    pl.stored -= 45;
    pl.chitin -= 18;
    hill.cells[i] = TILE.NURSERY;
    toast("Nursery built — cheaper hatches.");
  }
  clampPlayerFoodToCap();
  syncHillHud();
  renderHillBoard();
}

function renderHillBoard() {
  const board = document.getElementById("hill-board");
  board.innerHTML = "";
  board.style.gridTemplateColumns = `repeat(${HILL_W}, 1fr)`;
  for (let y = 0; y < HILL_H; y++) {
    for (let x = 0; x < HILL_W; x++) {
      const t = hill.cells[hillIdx(x, y)];
      const el = document.createElement("button");
      el.type = "button";
      el.className = "hill-cell";
      if (t === TILE.ROCK) el.classList.add("rock");
      else if (t === TILE.TUNNEL) el.classList.add("tunnel");
      else if (t === TILE.QUEEN) el.classList.add("queen");
      else if (t === TILE.GRANARY) el.classList.add("granary");
      else if (t === TILE.NURSERY) el.classList.add("nursery");
      el.textContent =
        t === TILE.ROCK ? "soil" : t === TILE.TUNNEL ? "hall" : t === TILE.QUEEN ? "queen" : t === TILE.GRANARY ? "gran" : "nurse";
      el.addEventListener("click", () => tryHillAction(x, y));
      board.appendChild(el);
    }
  }
}

function bindUI() {
  const $ = (id) => document.getElementById(id);

  $("btn-hill").addEventListener("click", () => setScene("hill"));
  $("hill-exit").addEventListener("click", () => setScene("surface"));

  document.querySelectorAll("#hill-tools .tool").forEach((btn) => {
    btn.addEventListener("click", () => {
      document.querySelectorAll("#hill-tools .tool").forEach((b) => b.classList.remove("active"));
      btn.classList.add("active");
      hillTool = btn.getAttribute("data-tool");
      $("hill-hint").textContent =
        hillTool === "dig"
          ? "Dig: expands tunnels from open rock touching a chamber."
          : hillTool === "granary"
            ? "Granary: place on a hall tile. Raises surface food cap."
            : "Nursery: place on a hall tile. Lowers food cost per hatch.";
    });
  });

  $("go-restart").addEventListener("click", () => {
    seedWorld();
    view.x = nests[PLAYER].x;
    view.y = nests[PLAYER].y;
    setScene("surface");
    toast("New world.");
  });

  $("speed").addEventListener("input", () => {
    speedIdx = clamp(+$("speed").value, 0, speedSteps.length - 1);
  });
  $("evap").addEventListener("input", () => {
    uiEvap = +$("evap").value / 100;
  });
  $("diffuse").addEventListener("input", () => {
    uiDiffuse = +$("diffuse").value / 100;
  });
  $("noise").addEventListener("input", () => {
    uiNoise = +$("noise").value / 100;
  });

  $("btn-pause").addEventListener("click", () => {
    paused = !paused;
    $("btn-pause").textContent = paused ? "Resume" : "Pause";
  });
  $("btn-rain").addEventListener("click", () => {
    clearPheromones(1 - cfg.rainWipe);
    toast("Rain washed trails.");
  });
  $("btn-reset").addEventListener("click", () => {
    seedWorld();
    view.x = nests[PLAYER].x;
    view.y = nests[PLAYER].y;
    toast("World reseeded.");
  });

  $("brush-size").addEventListener("input", () => {
    brushRadius = +$("brush-size").value;
  });

  document.querySelectorAll(".brush").forEach((btn) => {
    btn.addEventListener("click", () => {
      document.querySelectorAll(".brush").forEach((b) => b.classList.remove("active"));
      btn.classList.add("active");
      brush = btn.getAttribute("data-brush");
    });
  });

  setInterval(() => {
    $("stat-ants").textContent = String(countColonyAnts(PLAYER));
    $("stat-food").textContent = String(Math.floor(colonies[PLAYER].stored));
    $("stat-chitin").textContent = String(Math.floor(colonies[PLAYER].chitin));
    let rivals = 0;
    for (let ci = 1; ci < N_COLONIES; ci++) rivals += countColonyAnts(ci);
    $("stat-rivals").textContent = String(rivals);
    $("stat-bugs").textContent = String(predators.length);
    $("stat-trail").textContent = avgTrail.toFixed(1);
    if (scene === "hill") syncHillHud();
  }, 200);
}

let toastTimer = 0;
function toast(msg) {
  const el = document.getElementById("toast");
  el.textContent = msg;
  el.classList.add("show");
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => el.classList.remove("show"), 2200);
}

function onPointerDown(e) {
  if (scene !== "surface") return;
  const rect = canvas.getBoundingClientRect();
  const sx = e.clientX - rect.left;
  const sy = e.clientY - rect.top;
  dragging.lx = sx;
  dragging.ly = sy;
  dragging.button = e.button;
  if (e.button === 2 || (e.button === 0 && brush === "none")) {
    dragging.pan = true;
    dragging.paint = false;
  } else if (e.button === 0 && brush !== "none") {
    dragging.pan = false;
    dragging.paint = true;
    const { wx, wy } = screenToWorld(sx, sy);
    paintCircle(wx, wy, brushRadius, brush);
  }
  e.preventDefault();
}

function onPointerMove(e) {
  if (scene !== "surface") return;
  const rect = canvas.getBoundingClientRect();
  const sx = e.clientX - rect.left;
  const sy = e.clientY - rect.top;
  if (dragging.pan) {
    const dx = sx - dragging.lx;
    const dy = sy - dragging.ly;
    view.x -= dx / view.zoom;
    view.y -= dy / view.zoom;
    dragging.lx = sx;
    dragging.ly = sy;
  } else if (dragging.paint && brush !== "none") {
    const { wx, wy } = screenToWorld(sx, sy);
    paintCircle(wx, wy, brushRadius * 0.65, brush);
  }
}

function onPointerUp() {
  dragging.pan = false;
  dragging.paint = false;
}

function onWheel(e) {
  if (scene !== "surface") return;
  const rect = canvas.getBoundingClientRect();
  const sx = e.clientX - rect.left;
  const sy = e.clientY - rect.top;
  const before = screenToWorld(sx, sy);
  const factor = e.deltaY > 0 ? 0.92 : 1.09;
  view.zoom = clamp(view.zoom * factor, 0.16, 2.4);
  const after = screenToWorld(sx, sy);
  view.x += before.wx - after.wx;
  view.y += before.wy - after.wy;
  e.preventDefault();
}

function init() {
  canvas = document.getElementById("c");
  ctx = canvas.getContext("2d", { alpha: false });
  initGrids();
  initBuckets();
  seedWorld();
  view.x = nests[PLAYER].x;
  view.y = nests[PLAYER].y;

  resize();
  window.addEventListener("resize", resize);

  canvas.addEventListener("pointerdown", onPointerDown);
  window.addEventListener("pointermove", onPointerMove);
  window.addEventListener("pointerup", onPointerUp);
  canvas.addEventListener("wheel", onWheel, { passive: false });
  canvas.addEventListener("contextmenu", (e) => e.preventDefault());

  bindUI();
  lastTs = performance.now();
  cancelAnimationFrame(raf);
  raf = requestAnimationFrame(loop);
}

init();
