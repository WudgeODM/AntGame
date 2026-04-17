# Gridworks

Browser factory sim (belts, miners, smelter, press, blast furnace, assembler, chests, Quartermaster, milestones).

**Rebuild notes:** Items and chest contents use **typed grid buffers** (no string `Map` keys). Belts use **deterministic** high-index-first moves + destination claims. **Ore generation** only paints blob bounding boxes. **Terrain** (patches) is drawn to an **offscreen cache** and blitted until you build or demolish.

Run locally:

```bash
python3 -m http.server 8080
```

Open the served URL (ES modules).
