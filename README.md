# Ant Realm

Browser ant-colony simulator: pheromone trails (stigmergy), nest economy, rocks, painting tools, pan and zoom.

## Play locally

Open `index.html` in a browser via a local server (ES modules block `file://` imports in many browsers):

```bash
cd "/Users/oli/Fun simulator game"
python3 -m http.server 8080
```

Then visit `http://localhost:8080`.

## Publish on GitHub Pages

1. Create a new repository on GitHub and push this folder (include `index.html`, `styles.css`, `game.js`).
2. In the repo on GitHub: **Settings → Pages**.
3. Under **Build and deployment**, set **Source** to **Deploy from a branch**.
4. Choose branch **main** (or **master**) and folder **/ (root)**, then save.
5. After a minute, the site will be at `https://<your-username>.github.io/<repo-name>/`.

If the game loads but scripts fail, confirm `game.js` is in the repository root next to `index.html`.
