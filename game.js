/**
 * Ant Realm — grid pheromones, stigmergy, nest economy, obstacles.
 * Vanilla ES modules; host on GitHub Pages from repo root.
 */

const TAU = Math.PI * 2;

const WORLD = Object.freeze({ w: 2400, h: 2400 });
const GRID = Object.freeze({ w: 320, h: 320 });
const CELL = Object.freeze({ x: WORLD.w / GRID.w, y: WORLD.h / GRID.h });

const STATE = Object.freeze({ FORAGE: 0, RETURN: 1 });

const cfg = {
  antSpeed: 62,
  maxTurn: 2.35,
  sensorDist: 26,
  sensorSpread: 0.55,
  carryDeposit: 2.8,
  forageDeposit: 0.12,
  nestHomeEmit: 4.2,
  nestRadius: 42,
  pickFood: 6,
  maxAnts: 950,
  spawnCost: 72,
  initialAnts: 380,
  rainWipe: 0.55,
};

let canvas, ctx;
let dpr = 1;
let view = { x: WORLD.w * 0.5, y: WORLD.h * 0.5, zoom: 0.55 };
let dragging = { pan: false, paint: false, button: 0, lx: 0, ly: 0 };
let brush = "none";
let brushRadius = 36;
let paused = false;
let speedIdx = 2;
const speedSteps = [0.25, 0.5, 1, 2, 3];
let uiEvap = 0.35;
let uiDiffuse = 0.4;
let uiNoise = 0.2;

let foodPher, homePher, scratchA, scratchB;
let foodAmount;
let rocks;
let pheromap; // offscreen for trail visualization

let ants;
let colony = { stored: 0, gathered: 0 };
let nest = { x: WORLD.w * 0.5, y: WORLD.h * 0.5 };

let lastTs = 0;
let raf = 0;
let avgTrail = 0;

function clamp(v, a, b) {
  return Math.max(a, Math.min(b, v));
}

function worldToGrid(wx, wy) {
  const gx = clamp((wx / WORLD.w) * GRID.w, 0, GRID.w - 1);
  const gy = clamp((wy / WORLD.h) * GRID.h, 0, GRID.h - 1);
  return { gx, gy };
}

function gridToWorld(gx, gy) {
  return { x: (gx + 0.5) * CELL.x, y: (gy + 0.5) * CELL.y };
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
  const v =
    grid[i00] * (1 - tx) * (1 - ty) +
    grid[i10] * tx * (1 - ty) +
    grid[i01] * (1 - tx) * ty +
    grid[i11] * tx * ty;
  return v;
}

function rockAtWorld(wx, wy) {
  const { gx, gy } = worldToGrid(wx, wy);
  return rocks[idx(gx | 0, gy | 0)] === 1;
}

function initGrids() {
  const n = GRID.w * GRID.h;
  foodPher = new Float32Array(n);
  homePher = new Float32Array(n);
  scratchA = new Float32Array(n);
  scratchB = new Float32Array(n);
  foodAmount = new Float32Array(n);
  rocks = new Uint8Array(n);
}

function clearPheromones(factor = 1) {
  const n = GRID.w * GRID.h;
  for (let i = 0; i < n; i++) {
    foodPher[i] *= factor;
    homePher[i] *= factor;
  }
}

function emitNestHome(dt) {
  const r = cfg.nestRadius / Math.max(CELL.x, CELL.y);
  const cx = (nest.x / WORLD.w) * GRID.w;
  const cy = (nest.y / WORLD.h) * GRID.h;
  const r2 = r * r;
  const x0 = Math.max(0, Math.floor(cx - r - 1));
  const y0 = Math.max(0, Math.floor(cy - r - 1));
  const x1 = Math.min(GRID.w - 1, Math.ceil(cx + r + 1));
  const y1 = Math.min(GRID.h - 1, Math.ceil(cy + r + 1));
  const add = cfg.nestHomeEmit * dt;
  for (let gy = y0; gy <= y1; gy++) {
    const dy = gy - cy;
    for (let gx = x0; gx <= x1; gx++) {
      const dx = gx - cx;
      if (dx * dx + dy * dy <= r2) {
        const i = idx(gx, gy);
        if (!rocks[i]) homePher[i] += add;
      }
    }
  }
}

function evaporateAndDiffuse() {
  const evap = clamp(0.985 - uiEvap * 0.028, 0.9, 0.999);
  const diff = uiDiffuse * 0.22;
  const w = GRID.w;
  const h = GRID.h;
  const srcF = foodPher;
  const srcH = homePher;
  const dstF = scratchA;
  const dstH = scratchB;

  for (let y = 1; y < h - 1; y++) {
    const row = y * w;
    for (let x = 1; x < w - 1; x++) {
      const i = row + x;
      if (rocks[i]) {
        dstF[i] = 0;
        dstH[i] = 0;
        continue;
      }
      const f = srcF[i];
      const hh = srcH[i];
      const avgF =
        (srcF[i - 1] + srcF[i + 1] + srcF[i - w] + srcF[i + w] + srcF[i - w - 1] + srcF[i - w + 1] + srcF[i + w - 1] + srcF[i + w + 1]) * (1 / 8);
      const avgH =
        (srcH[i - 1] + srcH[i + 1] + srcH[i - w] + srcH[i + w] + srcH[i - w - 1] + srcH[i - w + 1] + srcH[i + w - 1] + srcH[i + w + 1]) * (1 / 8);
      dstF[i] = (f * (1 - diff) + avgF * diff) * evap;
      dstH[i] = (hh * (1 - diff) + avgH * diff) * evap;
    }
  }

  for (let y = 1; y < h - 1; y++) {
    const row = y * w;
    for (let x = 1; x < w - 1; x++) {
      const i = row + x;
      foodPher[i] = dstF[i];
      homePher[i] = dstH[i];
    }
  }
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
        foodAmount[i] = clamp(foodAmount[i] + 18 + Math.random() * 24, 0, 200);
        rocks[i] = 0;
      } else if (mode === "rock") {
        rocks[i] = 1;
        foodAmount[i] = 0;
        foodPher[i] = 0;
        homePher[i] = 0;
      } else if (mode === "erase") {
        rocks[i] = 0;
        foodAmount[i] = 0;
        foodPher[i] = 0;
        homePher[i] = 0;
      }
    }
  }
}

function seedWorld() {
  foodPher.fill(0);
  homePher.fill(0);
  foodAmount.fill(0);
  rocks.fill(0);

  const clusters = 9 + (Math.random() * 6) | 0;
  const avoidR = 320;
  for (let c = 0; c < clusters; c++) {
    let wx;
    let wy;
    let guard = 0;
    do {
      wx = 220 + Math.random() * (WORLD.w - 440);
      wy = 220 + Math.random() * (WORLD.h - 440);
      guard++;
    } while (dist2(wx, wy, nest.x, nest.y) < avoidR * avoidR && guard < 40);
    const r = 70 + Math.random() * 130;
    paintCircle(wx, wy, r, "food");
  }

  for (let k = 0; k < 28; k++) {
    const wx = 160 + Math.random() * (WORLD.w - 320);
    const wy = 160 + Math.random() * (WORLD.h - 320);
    paintCircle(wx, wy, 22 + Math.random() * 70, "rock");
  }

  colony = { stored: 0, gathered: 0 };
  spawnAnts(cfg.initialAnts, true);
}

function spawnAnts(count, reset) {
  if (reset) ants = [];
  const cap = cfg.maxAnts - ants.length;
  const n = Math.min(count, cap);
  for (let i = 0; i < n; i++) {
    const t = Math.random() * TAU;
    const d = Math.random() * cfg.nestRadius * 0.55;
    ants.push({
      x: nest.x + Math.cos(t) * d,
      y: nest.y + Math.sin(t) * d,
      a: Math.random() * TAU,
      s: STATE.FORAGE,
      carry: 0,
    });
  }
}

function tryColonySpawn() {
  if (ants.length >= cfg.maxAnts) return;
  if (colony.stored < cfg.spawnCost) return;
  colony.stored -= cfg.spawnCost;
  spawnAnts(1, false);
  toast("New ant hatched from stored food.");
}

function depositPher(wx, wy, grid, amount) {
  const { gx, gy } = worldToGrid(wx, wy);
  const gxi = gx | 0;
  const gyi = gy | 0;
  const i = idx(gxi, gyi);
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
    else turn = (Math.random() * 2 - 1) * cfg.maxTurn * 0.25;
  } else {
    turn = (Math.random() * 2 - 1) * wander;
  }
  ant.a += clamp(turn, -cfg.maxTurn, cfg.maxTurn);
}

function dist2(ax, ay, bx, by) {
  const dx = ax - bx;
  const dy = ay - by;
  return dx * dx + dy * dy;
}

function updateAnt(ant, dt) {
  const speed = cfg.antSpeed * dt;

  if (ant.s === STATE.FORAGE) {
    const f = sampleSensors(ant, foodPher);
    steerFromSamples(ant, f.left, f.mid, f.right, cfg.maxTurn * 0.85);

    const pick = bilinear(foodAmount, ant.x, ant.y);
    if (pick > 0.4 && ant.carry === 0) {
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
    steerFromSamples(ant, h.left, h.mid, h.right, cfg.maxTurn * 0.45);

    const nx = nest.x - ant.x;
    const ny = nest.y - ant.y;
    const nd = Math.hypot(nx, ny) + 0.001;
    const desired = Math.atan2(ny, nx);
    let diff = desired - ant.a;
    while (diff > Math.PI) diff -= TAU;
    while (diff < -Math.PI) diff += TAU;
    ant.a += clamp(diff, -cfg.maxTurn * 1.15, cfg.maxTurn * 1.15) * 0.55;

    depositPher(ant.x, ant.y, foodPher, cfg.carryDeposit * dt);
  }

  let nx = ant.x + Math.cos(ant.a) * speed;
  let ny = ant.y + Math.sin(ant.a) * speed;

  if (nx < 8 || nx > WORLD.w - 8 || ny < 8 || ny > WORLD.h - 8) {
    ant.a += Math.PI * 0.5 + (Math.random() - 0.5) * 0.8;
    nx = clamp(nx, 8, WORLD.w - 8);
    ny = clamp(ny, 8, WORLD.h - 8);
  }

  if (rockAtWorld(nx, ny)) {
    ant.a += (Math.random() < 0.5 ? 1 : -1) * (1.1 + Math.random() * 1.2);
  } else {
    ant.x = nx;
    ant.y = ny;
  }

  if (ant.s === STATE.RETURN) {
    const dNest = Math.sqrt(dist2(ant.x, ant.y, nest.x, nest.y));
    if (dNest < cfg.nestRadius * 0.55 && ant.carry) {
      ant.carry = 0;
      ant.s = STATE.FORAGE;
      colony.stored += 1;
      colony.gathered += 1;
    }
  }
}

function updateSimulation(dt, steps) {
  emitNestHome(dt);
  for (let s = 0; s < steps; s++) {
    evaporateAndDiffuse();
  }

  let sum = 0;
  const n = ants.length;
  for (let i = 0; i < n; i++) {
    const ant = ants[i];
    updateAnt(ant, dt);
    const g = worldToGrid(ant.x, ant.y);
    sum += foodPher[idx(g.gx | 0, g.gy | 0)];
  }
  avgTrail = n ? sum / n : 0;

  tryColonySpawn();
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
  const w = GRID.w;
  const h = GRID.h;
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const i = y * w + x;
      const di = i * 4;
      const f = Math.min(1, foodPher[i] * 0.035);
      const hh = Math.min(1, homePher[i] * 0.028);
      const fa = foodAmount[i];
      const foodTint = Math.min(1, fa * 0.009);
      const rock = rocks[i];
      if (rock) {
        d[di] = 40;
        d[di + 1] = 44;
        d[di + 2] = 52;
        d[di + 3] = 255;
      } else {
        d[di] = Math.floor(12 + f * 220 + hh * 40 + foodTint * 210);
        d[di + 1] = Math.floor(18 + hh * 210 + f * 30 + foodTint * 170);
        d[di + 2] = Math.floor(28 + f * 40 + hh * 160 + foodTint * 40);
        d[di + 3] = Math.floor(40 + (f + hh + foodTint * 0.6) * 200);
      }
    }
  }
  pctx.putImageData(img, 0, 0);
}

function drawWorld() {
  const vw = canvas.width / dpr;
  const vh = canvas.height / dpr;
  ctx.save();
  ctx.scale(dpr, dpr);
  ctx.fillStyle = "#07090d";
  ctx.fillRect(0, 0, vw, vh);

  ctx.save();
  ctx.translate(vw * 0.5, vh * 0.5);
  ctx.scale(view.zoom, view.zoom);
  ctx.translate(-view.x, -view.y);

  buildPheromap();
  ctx.imageSmoothingEnabled = true;
  ctx.drawImage(pheromap, 0, 0, WORLD.w, WORLD.h);

  // Nest
  const mound = ctx.createRadialGradient(nest.x, nest.y, 0, nest.x, nest.y, cfg.nestRadius * 2.2);
  mound.addColorStop(0, "rgba(52, 211, 153, 0.35)");
  mound.addColorStop(0.45, "rgba(16, 185, 129, 0.2)");
  mound.addColorStop(1, "rgba(16, 185, 129, 0)");
  ctx.fillStyle = mound;
  ctx.beginPath();
  ctx.arc(nest.x, nest.y, cfg.nestRadius * 2.2, 0, TAU);
  ctx.fill();

  ctx.strokeStyle = "rgba(167, 243, 208, 0.55)";
  ctx.lineWidth = 2 / view.zoom;
  ctx.beginPath();
  ctx.arc(nest.x, nest.y, cfg.nestRadius, 0, TAU);
  ctx.stroke();

  // Ants
  ctx.lineWidth = 1.1 / view.zoom;
  const n = ants.length;
  for (let i = 0; i < n; i++) {
    const ant = ants[i];
    const len = ant.s === STATE.RETURN ? 7.2 : 6.2;
    const wx = ant.x;
    const wy = ant.y;
    const x2 = wx + Math.cos(ant.a) * len;
    const y2 = wy + Math.sin(ant.a) * len;
    ctx.strokeStyle = ant.s === STATE.RETURN ? "rgba(254, 215, 170, 0.92)" : "rgba(226, 232, 240, 0.78)";
    ctx.beginPath();
    ctx.moveTo(wx, wy);
    ctx.lineTo(x2, y2);
    ctx.stroke();
    ctx.fillStyle = ant.s === STATE.RETURN ? "rgba(251, 191, 36, 0.95)" : "rgba(248, 250, 252, 0.9)";
    ctx.beginPath();
    ctx.arc(wx, wy, 1.35 / view.zoom, 0, TAU);
    ctx.fill();
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
  if (!paused) {
    const mul = speedSteps[speedIdx];
    const dt = raw * mul;
    const steps = mul >= 2 ? 2 : 1;
    updateSimulation(dt, steps);
  }
  drawWorld();
}

function bindUI() {
  const $ = (id) => document.getElementById(id);

  $("stat-ants").textContent = String(ants.length);
  $("stat-food").textContent = String(colony.stored);
  $("stat-gathered").textContent = String(colony.gathered);
  $("stat-trail").textContent = avgTrail.toFixed(1);

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
    toast("Rain washed trails (pheromones weakened).");
  });
  $("btn-reset").addEventListener("click", () => {
    seedWorld();
    view.x = nest.x;
    view.y = nest.y;
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
    $("stat-ants").textContent = String(ants.length);
    $("stat-food").textContent = String(colony.stored);
    $("stat-gathered").textContent = String(colony.gathered);
    $("stat-trail").textContent = avgTrail.toFixed(1);
  }, 180);
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
  const rect = canvas.getBoundingClientRect();
  const sx = e.clientX - rect.left;
  const sy = e.clientY - rect.top;
  const before = screenToWorld(sx, sy);
  const factor = e.deltaY > 0 ? 0.92 : 1.09;
  view.zoom = clamp(view.zoom * factor, 0.18, 2.4);
  const after = screenToWorld(sx, sy);
  view.x += before.wx - after.wx;
  view.y += before.wy - after.wy;
  e.preventDefault();
}

function init() {
  canvas = document.getElementById("c");
  ctx = canvas.getContext("2d", { alpha: false });
  initGrids();
  seedWorld();
  view.x = nest.x;
  view.y = nest.y;

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
