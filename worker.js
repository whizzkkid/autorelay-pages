/* Relay-candidate worker for the node picker: e-SNR node <-> relay over a slice of the candidate grid. */
importScripts("engine.js");
const E = self.AutoRelayEngine;
let model = null;
const grids = {};

self.onmessage = (ev) => {
  const q = ev.data;
  if (q.type === "init") {  // load one region's terrain (regions/<id>/terrain_data.js sets AUTORELAY_TERRAIN)
    importScripts("regions/" + q.region + "/terrain_data.js");
    model = E.makeModel(self.AUTORELAY_TERRAIN);
    self.postMessage({ type: "ready" });
    return;
  }
  if (q.type !== "relay" || !model) return;
  if (q.radio) Object.assign(model.p, q.radio);  // EESM beta / sensitivity edited on the page
  let grid, i0 = q.i0, i1 = q.i1;
  if (q.pts) { grid = q.pts; i0 = 0; i1 = q.pts.x.length; }  // fine search: the points come with the job
  else { const key = q.step + "/" + q.border + "/" + q.onWater; grid = grids[key] || (grids[key] = E.candidateGrid(model, q.step, q.border, q.onWater)); }
  const r = E.relayLinks(model, q.node, q.hNode, q.txNode, grid, i0, i1, q.hR, q.txR, q.cab);
  self.postMessage({ type: "relay", job: q.job, gen: q.gen, name: q.name, i0: q.i0, to: r.to, from: r.from },
                   [r.to.buffer, r.from.buffer]);
};
