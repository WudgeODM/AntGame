/**
 * Gridworks — belt logistics + miners + smelters + chests.
 */

const TAU = Math.PI * 2;

const TILE = { EMPTY: 0, BELT: 1, MINER: 2, SMELTER: 3, CHEST: 4 };
const ITEM = { NONE: 0, ORE: 1, INGOT: 2 };

const D = [
  { x: 0, y: -1 },
  { x: 1, y: 0 },
  { x: 0, y: 1 },
  { x: -1, y: 0 },
];

const W = 30;
const H = 22;
const N = W * H;

const COST = { belt: 4, miner: 42, smelter: 68, chest: 14 };
const REFUND = 0.45;

const TOOLS = [
  { id: "belt", label: "Conveyor", cost: COST.belt, hint: "Moves items in arrow direction." },
  { id: "miner", label: "Miner", cost: COST.miner, hint: "Ore patch only. Drops onto belt ahead." },
  { id: "smelter", label: "Smelter", cost: COST.smelter, hint: "2 ore → 1 ingot. Orange = out, peach = in." },
  { id: "chest", label: "Storage", cost: COST.chest, hint: "Accepts any item from belts." },
  { id: "demolish", label: "Demolish", cost: 0, hint: "Remove tile (partial refund)." },
];

let canvas, ctx;
let cellPx = 22;
let money = 260;
let paused = false;
let showGrid = true;
let oreMined = 0;
let ingotsMade = 0;
let beltLoad = 0;

let kind = new Uint8Array(N);
let rot = new Uint8Array(N);
let orePatch = new Uint8Array(N);
let smelterOre = new Uint8Array(N);
let smelterProg = new Float32Array(N);
let minerCd = new Uint16Array(N);
/** @type {(null | { ore: number; ingot: number })[]} */
let chestInv = new Array(N).fill(null);

let items = new Map();
let activeTool = "belt";
let placeRot = 0;
let simAcc = 0;
let lastFrame = 0;
const MS_PER_TICK = 115;

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

function toast(msg) {
  const el = document.getElementById("toast");
  el.textContent = msg;
  el.classList.add("show");
  clearTimeout(toast._t);
  toast._t = setTimeout(() => el.classList.remove("show"), 2000);
}

function genOre() {
  orePatch.fill(0);
  const blobs = 5 + (Math.random() * 4) | 0;
  for (let b = 0; b < blobs; b++) {
    const cx = 3 + ((Math.random() * (W - 6)) | 0);
    const cy = 3 + ((Math.random() * (H - 6)) | 0);
    const r = 2.2 + Math.random() * 2.8;
    for (let y = 0; y < H; y++) {
      for (let x = 0; x < W; x++) {
        const dx = x - cx;
        const dy = y - cy;
        if (dx * dx + dy * dy <= r * r) orePatch[idx(x, y)] = 1;
      }
    }
  }
}

function clearFloor() {
  kind.fill(TILE.EMPTY);
  rot.fill(0);
  smelterOre.fill(0);
  smelterProg.fill(0);
  minerCd.fill(0);
  for (let i = 0; i < N; i++) chestInv[i] = null;
  items.clear();
  oreMined = 0;
  ingotsMade = 0;
}

function initGame() {
  genOre();
  clearFloor();
  money = 260;
}

function smelterInputDir(r) {
  return (r + 2) & 3;
}

function neighbor(x, y, dir) {
  return { x: x + D[dir].x, y: y + D[dir].y };
}

function refundForTile(t) {
  if (t === TILE.BELT) return Math.floor(COST.belt * REFUND);
  if (t === TILE.MINER) return Math.floor(COST.miner * REFUND);
  if (t === TILE.SMELTER) return Math.floor(COST.smelter * REFUND);
  if (t === TILE.CHEST) return Math.floor(COST.chest * REFUND);
  return 0;
}

function demolish(x, y) {
  const i = idx(x, y);
  const t = kind[i];
  if (t === TILE.EMPTY) return;
  money += refundForTile(t);
  setItem(x, y, ITEM.NONE);
  kind[i] = TILE.EMPTY;
  rot[i] = 0;
  smelterOre[i] = 0;
  smelterProg[i] = 0;
  minerCd[i] = 0;
  chestInv[i] = null;
}

function canPlace(t, x, y) {
  if (!inBounds(x, y)) return false;
  if (tileAt(x, y) !== TILE.EMPTY) return false;
  if (t === TILE.MINER && !orePatch[idx(x, y)]) return false;
  return true;
}

function tryBuy(t) {
  const c =
    t === TILE.BELT ? COST.belt : t === TILE.MINER ? COST.miner : t === TILE.SMELTER ? COST.smelter : COST.chest;
  if (money < c) {
    toast("Not enough credits.");
    return false;
  }
  money -= c;
  return true;
}

function placeTile(t, x, y) {
  if (!canPlace(t, x, y)) {
    if (t === TILE.MINER) toast("Miners need an ore patch.");
    else toast("Blocked.");
    return;
  }
  if (!tryBuy(t)) return;
  const i = idx(x, y);
  kind[i] = t;
  rot[i] = placeRot & 3;
  if (t === TILE.CHEST) chestInv[i] = { ore: 0, ingot: 0 };
}

function handleBuildClick(x, y) {
  if (activeTool === "demolish") {
    demolish(x, y);
    return;
  }
  const map = { belt: TILE.BELT, miner: TILE.MINER, smelter: TILE.SMELTER, chest: TILE.CHEST };
  const t = map[activeTool];
  if (t === undefined) return;
  placeTile(t, x, y);
}

function tickSmelters() {
  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const i = idx(x, y);
      if (kind[i] !== TILE.SMELTER) continue;
      const r = rot[i];
      const out = neighbor(x, y, r);
      const smeltRate = 0.055;
      if (smelterOre[i] >= 2) {
        smelterProg[i] += smeltRate;
        if (smelterProg[i] >= 1) {
          if (inBounds(out.x, out.y) && itemAt(out.x, out.y) === ITEM.NONE) {
            const ot = tileAt(out.x, out.y);
            if (ot === TILE.BELT) {
              setItem(out.x, out.y, ITEM.INGOT);
              ingotsMade++;
            } else if (ot === TILE.CHEST && chestInv[idx(out.x, out.y)]) {
              chestInv[idx(out.x, out.y)].ingot++;
              ingotsMade++;
            } else {
              smelterProg[i] = 0.98;
              continue;
            }
          } else {
            smelterProg[i] = 0.98;
            continue;
          }
          smelterOre[i] -= 2;
          smelterProg[i] = 0;
        }
      } else {
        smelterProg[i] *= 0.88;
      }
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
      if (minerCd[i] < 55) continue;
      minerCd[i] = 0;
      setItem(out.x, out.y, ITEM.ORE);
      oreMined++;
    }
  }
}

function beltFlowDir(x, y) {
  if (tileAt(x, y) !== TILE.BELT) return -1;
  return rotAt(x, y);
}

function tryInsertIntoChest(x, y, it) {
  const i = idx(x, y);
  if (kind[i] !== TILE.CHEST || !chestInv[i]) return false;
  if (it === ITEM.ORE) chestInv[i].ore++;
  else if (it === ITEM.INGOT) chestInv[i].ingot++;
  return true;
}

function moveItems() {
  const entries = [...items.entries()].map(([k, t]) => {
    const [sx, sy] = k.split(",").map(Number);
    return { x: sx, y: sy, type: t, k };
  });
  entries.sort(() => Math.random() - 0.5);

  const want = new Map();

  function stay(x0, y0, t0) {
    want.set(key(x0, y0), t0);
  }

  for (const e of entries) {
    const { x, y, type } = e;
    const dir = beltFlowDir(x, y);
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
    if (nt === TILE.BELT) {
      const tk = key(nx, ny);
      if (want.has(tk)) {
        stay(x, y, type);
        continue;
      }
      want.set(tk, type);
      continue;
    }

    if (nt === TILE.SMELTER) {
      const si = idx(nx, ny);
      const inDir = smelterInputDir(rot[si]);
      const src = neighbor(nx, ny, inDir);
      if (src.x === x && src.y === y && type === ITEM.ORE && smelterOre[si] < 8) {
        smelterOre[si]++;
        continue;
      }
      stay(x, y, type);
      continue;
    }

    if (nt === TILE.CHEST) {
      if (tryInsertIntoChest(nx, ny, type)) continue;
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

function tick() {
  if (paused) return;
  moveItems();
  tickSmelters();
  tickMiners();
  beltLoad = items.size;
}

function draw() {
  const pad = 1;
  const cw = cellPx;
  const ch = cellPx;
  ctx.save();
  ctx.fillStyle = "#0d1117";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const px = pad + x * cw;
      const py = pad + y * ch;
      const i = idx(x, y);
      const t = kind[i];
      const ore = orePatch[i];

      if (ore) {
        ctx.fillStyle = "rgba(201, 162, 39, 0.22)";
        ctx.fillRect(px, py, cw - 1, ch - 1);
      } else {
        ctx.fillStyle = "#11161d";
        ctx.fillRect(px, py, cw - 1, ch - 1);
      }

      if (t === TILE.BELT) {
        ctx.fillStyle = "#1f2937";
        ctx.fillRect(px + 2, py + 2, cw - 5, ch - 5);
        const r = rot[i];
        ctx.strokeStyle = "#6b7280";
        ctx.lineWidth = 2;
        const cx = px + cw * 0.5;
        const cy = py + ch * 0.5;
        const arr = 7;
        ctx.beginPath();
        ctx.moveTo(cx - D[r].x * 4, cy - D[r].y * 4);
        ctx.lineTo(cx + D[r].x * arr, cy + D[r].y * arr);
        ctx.stroke();
        ctx.fillStyle = "#9ca3af";
        ctx.beginPath();
        ctx.arc(cx + D[r].x * 5, cy + D[r].y * 5, 3, 0, TAU);
        ctx.fill();
      } else if (t === TILE.MINER) {
        ctx.fillStyle = "#374151";
        ctx.fillRect(px + 2, py + 2, cw - 5, ch - 5);
        ctx.fillStyle = "#fbbf24";
        ctx.beginPath();
        ctx.arc(px + cw * 0.5, py + ch * 0.5, 5, 0, TAU);
        ctx.fill();
        const r = rot[i];
        ctx.fillStyle = "#93c5fd";
        ctx.fillRect(px + cw * 0.5 + D[r].x * 8 - 2, py + ch * 0.5 + D[r].y * 8 - 2, 5, 5);
      } else if (t === TILE.SMELTER) {
        ctx.fillStyle = "#422006";
        ctx.fillRect(px + 2, py + 2, cw - 5, ch - 5);
        const r = rot[i];
        ctx.strokeStyle = "#f97316";
        ctx.lineWidth = 2;
        const cx = px + cw * 0.5;
        const cy = py + ch * 0.5;
        ctx.beginPath();
        ctx.moveTo(cx, cy);
        ctx.lineTo(cx + D[r].x * 10, cy + D[r].y * 10);
        ctx.stroke();
        ctx.fillStyle = "#fdba74";
        const id = smelterInputDir(r);
        ctx.fillRect(px + cw * 0.5 + D[id].x * 8 - 2, py + ch * 0.5 + D[id].y * 8 - 2, 5, 5);
        if (smelterOre[i] > 0) {
          ctx.fillStyle = "#fff";
          ctx.font = `600 ${Math.max(8, cw * 0.32)}px IBM Plex Mono, monospace`;
          ctx.textAlign = "center";
          ctx.fillText(String(smelterOre[i]), cx, cy + 4);
        }
      } else if (t === TILE.CHEST) {
        ctx.fillStyle = "#1e3a5f";
        ctx.fillRect(px + 2, py + 2, cw - 5, ch - 5);
        const inv = chestInv[i];
        if (inv) {
          ctx.fillStyle = "#94a3b8";
          ctx.font = `${Math.max(7, cw * 0.28)}px IBM Plex Mono, monospace`;
          ctx.textAlign = "center";
          ctx.fillText(`${inv.ore} · ${inv.ingot}`, px + cw * 0.5, py + ch * 0.55);
        }
      }

      if (showGrid) {
        ctx.strokeStyle = "rgba(48, 54, 61, 0.35)";
        ctx.lineWidth = 1;
        ctx.strokeRect(px - 0.5, py - 0.5, cw, ch);
      }
    }
  }

  for (const [k, t] of items) {
    const [sx, sy] = k.split(",").map(Number);
    const px = pad + sx * cw + cw * 0.5;
    const py = pad + sy * ch + ch * 0.5;
    if (t === ITEM.ORE) {
      ctx.fillStyle = "#facc15";
      ctx.beginPath();
      ctx.arc(px, py, cw * 0.22, 0, TAU);
      ctx.fill();
    } else if (t === ITEM.INGOT) {
      ctx.fillStyle = "#c4b5fd";
      ctx.fillRect(px - cw * 0.18, py - ch * 0.12, cw * 0.36, ch * 0.24);
      ctx.strokeStyle = "#7c3aed";
      ctx.lineWidth = 1;
      ctx.strokeRect(px - cw * 0.18, py - ch * 0.12, cw * 0.36, ch * 0.24);
    }
  }

  ctx.restore();
}

function resize() {
  const stage = document.getElementById("stage");
  const sw = stage.clientWidth - 24;
  const sh = stage.clientHeight - 24;
  const needW = W * 24 + 2;
  const needH = H * 24 + 2;
  const scale = Math.min(sw / needW, sh / needH, 1.2);
  cellPx = Math.max(16, Math.floor(24 * scale));
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

function bindUI() {
  const tb = document.getElementById("tool-buttons");
  for (const t of TOOLS) {
    const b = document.createElement("button");
    b.type = "button";
    b.className = "tool-btn" + (activeTool === t.id ? " active" : "");
    b.dataset.tool = t.id;
    b.innerHTML = `<span>${t.label}</span>${t.cost ? `<span class="cost">$${t.cost}</span>` : ""}`;
    b.addEventListener("click", () => {
      activeTool = t.id;
      document.querySelectorAll(".tool-btn").forEach((x) => x.classList.remove("active"));
      b.classList.add("active");
      document.getElementById("tool-hint").textContent = t.hint;
    });
    tb.appendChild(b);
  }

  document.getElementById("grid-lines").addEventListener("change", (e) => {
    showGrid = e.target.checked;
  });

  document.getElementById("btn-pause").addEventListener("click", (e) => {
    paused = !paused;
    e.target.textContent = paused ? "Resume" : "Pause";
  });

  document.getElementById("btn-clear").addEventListener("click", () => {
    if (!confirm("Clear every tile and item on the floor?")) return;
    clearFloor();
    toast("Floor cleared.");
  });

  window.addEventListener("keydown", (e) => {
    const k = e.key.toLowerCase();
    if (k === "r") {
      placeRot = (placeRot + 1) & 3;
      toast(`Rotate → ${["N", "E", "S", "W"][placeRot]}`);
    } else if (k === "x") {
      activeTool = "demolish";
      document.querySelectorAll(".tool-btn").forEach((b) => {
        b.classList.toggle("active", b.dataset.tool === "demolish");
      });
      document.getElementById("tool-hint").textContent = TOOLS.find((t) => t.id === "demolish").hint;
    } else if (k >= "1" && k <= "5") {
      const ti = +k - 1;
      const def = TOOLS[ti];
      if (!def) return;
      activeTool = def.id;
      document.querySelectorAll(".tool-btn").forEach((b) => {
        b.classList.toggle("active", b.dataset.tool === def.id);
      });
      document.getElementById("tool-hint").textContent = def.hint;
    }
  });

  setInterval(() => {
    document.getElementById("money").textContent = String(money);
    document.getElementById("stat-ore").textContent = String(oreMined);
    document.getElementById("stat-ingot").textContent = String(ingotsMade);
    document.getElementById("stat-belt").textContent = String(beltLoad);
  }, 150);
}

function loop(ts) {
  if (!lastFrame) lastFrame = ts;
  simAcc += ts - lastFrame;
  lastFrame = ts;
  if (!paused) {
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

  canvas.addEventListener("pointerdown", (e) => {
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
