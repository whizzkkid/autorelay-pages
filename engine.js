/* AutoRelay terrain engine for the browser (and Node, for validation).
 *
 * A line-by-line port of the parts of the Python framework the node picker needs:
 *   autorelay/terrain.py    _terrain_kernel in delta-Bullington mode (rays over a DSM profile)
 *   autorelay/terrain.py    TerrainModel.channel (antenna elevation pattern, H(f) over the band)
 *   autorelay/phy.py        snr_db, eesm_db
 *   autorelay/topology.py   AirtimeTable, edge_weight, dijkstra, decide_dijkstra, relay_grid_dijkstra
 *   autorelay/terrain_planner.py  candidate_grid, candidate ordering
 * scripts/validate_web_engine.py runs this file under Node and compares it with the Python code.
 */
(function (root) {
  "use strict";
  const C0 = 299792458.0;
  const R_EARTH = 6371000.0;
  const MAXR = 5;
  const NODE_NAMES = ["BS", "MS1", "MS2"];
  const MS_NODES = ["MS1", "MS2"];
  const RELAY = "R";

  // ---------------------------------------------------------------- terrain model
  function b64ToBytes(b64) {
    if (typeof atob === "function") {
      const s = atob(b64), out = new Uint8Array(s.length);
      for (let i = 0; i < s.length; i++) out[i] = s.charCodeAt(i);
      return out;
    }
    return new Uint8Array(Buffer.from(b64, "base64"));
  }

  /** data: {W, H, mpp, dsm_offset, dsm_scale, dsm_b64 (uint16 LE), water_b64 (bit-packed, row-major), params} */
  function makeModel(data) {
    const W = data.W, H = data.H;
    const raw = b64ToBytes(data.dsm_b64);
    const T = new Float64Array(W * H);
    for (let i = 0; i < W * H; i++) T[i] = (raw[2 * i] | (raw[2 * i + 1] << 8)) * data.dsm_scale + data.dsm_offset;
    // ground under the terminals: 10th percentile of the 3x3 neighbourhood (= minimum for 9 samples),
    // scipy 'reflect' borders (edge pixel repeats), then min with the DSM itself
    const G = new Float64Array(W * H);
    for (let r = 0; r < H; r++) {
      for (let c = 0; c < W; c++) {
        let m = Infinity;
        for (let dr = -1; dr <= 1; dr++) {
          const rr = Math.min(Math.max(r + dr, 0), H - 1);
          for (let dc = -1; dc <= 1; dc++) {
            const cc = Math.min(Math.max(c + dc, 0), W - 1);
            const v = T[rr * W + cc];
            if (v < m) m = v;
          }
        }
        G[r * W + c] = Math.min(m, T[r * W + c]);
      }
    }
    const wb = b64ToBytes(data.water_b64);
    const water = new Uint8Array(W * H);
    for (let i = 0; i < W * H; i++) water[i] = (wb[i >> 3] >> (7 - (i & 7))) & 1;
    const p = data.params;
    const maxN = Math.ceil(Math.hypot(W, H) * data.mpp / p.step_m) + 4;
    return {
      W, H, T, G, water, mpp: data.mpp, p,
      lam: C0 / p.fc_hz, ae: p.k_factor * R_EARTH, smooth_n: Math.max(Math.round(p.smooth_m / p.step_m / 2), 1),
      buf: {
        d: new Float64Array(maxN), z: new Float64Array(maxN), zraw: new Float64Array(maxN),
        zs: new Float64Array(maxN), zse: new Float64Array(maxN), wat: new Uint8Array(maxN),
        hr: new Float64Array(p.n_sub), hi: new Float64Array(p.n_sub), s: new Float64Array(p.n_sub),
        out: { n: 0, L: new Float64Array(MAXR), cr: new Float64Array(MAXR), ci: new Float64Array(MAXR),
               et: new Float64Array(MAXR), er: new Float64Array(MAXR), px: new Float64Array(MAXR), los: false, diff_db: 0 },
      },
    };
  }

  function bilinear(R, W, H, row, col) {
    const r0 = Math.min(Math.max(Math.floor(row), 0), H - 2);
    const c0 = Math.min(Math.max(Math.floor(col), 0), W - 2);
    const fr = Math.min(Math.max(row - r0, 0), 1);
    const fc = Math.min(Math.max(col - c0, 0), 1);
    const i = r0 * W + c0;
    return R[i] * (1 - fr) * (1 - fc) + R[i + 1] * (1 - fr) * fc + R[i + W] * fr * (1 - fc) + R[i + W + 1] * fr * fc;
  }

  function groundAt(m, x, y) {
    return bilinear(m.G, m.W, m.H, m.H - y / m.mpp - 0.5, x / m.mpp - 0.5);
  }

  function J(v) {
    if (v <= -0.78) return 0.0;
    return 6.9 + 20.0 * Math.log10(Math.sqrt((v - 0.1) * (v - 0.1) + 1.0) + v - 0.1);
  }

  function maxV(z, d, i0, i1, za, zb, lam) {
    let bestV = -1e30, bestI = -1;
    const D = d[i1] - d[i0];
    for (let i = i0 + 1; i < i1; i++) {
      const d1 = d[i] - d[i0], d2 = d[i1] - d[i];
      if (d1 <= 0 || d2 <= 0) continue;
      const h = z[i] - (za + (zb - za) * d1 / D);
      const v = h * Math.sqrt(2.0 * D / (lam * d1 * d2));
      if (v > bestV) { bestV = v; bestI = i; }
    }
    return [bestI, bestV];
  }

  // complex helpers (re, im pairs)
  function csqrt(a, b) {
    const r = Math.hypot(a, b);
    const re = Math.sqrt(Math.max((r + a) / 2, 0));
    let im = Math.sqrt(Math.max((r - a) / 2, 0));
    if (b < 0 || (b === 0 && Object.is(b, -0))) im = -im;
    return [re, im];
  }

  function gammaTM(s, er, ei) {
    const c2 = 1.0 - s * s;
    const [wr, wi] = csqrt(er - c2, ei);
    const ar = er * s, ai = ei * s;
    const nr = ar - wr, ni = ai - wi, dr = ar + wr, di = ai + wi;
    const den = dr * dr + di * di;
    return [(nr * dr + ni * di) / den, (ni * dr - nr * di) / den];
  }

  function clear(z, d, i0, i1, xa, za, xb, zb, skipLo, skipHi) {
    if (xb === xa) return true;
    const lo = Math.min(xa, xb), hi = Math.max(xa, xb);
    for (let i = i0 + 1; i < i1; i++) {
      if (skipLo <= i && i <= skipHi) continue;
      const x = d[i];
      if (x <= lo || x >= hi) continue;
      const zl = za + (zb - za) * (x - xa) / (xb - xa);
      if (z[i] > zl + 1e-3) return false;
    }
    return true;
  }

  const FS = { px: 0, pz: 0, sin: 0, mis: 0 };
  function facetSpecular(zs, d, j, xa, za, xb, zb) {
    const x1 = d[j], y1 = zs[j], x2 = d[j + 1], y2 = zs[j + 1];
    let tx = x2 - x1, ty = y2 - y1;
    const tl = Math.sqrt(tx * tx + ty * ty);
    tx /= tl; ty /= tl;
    const nx = -ty, ny = tx;
    const sa = (xa - x1) * nx + (za - y1) * ny;
    const sb = (xb - x1) * nx + (zb - y1) * ny;
    if (sa <= 0 || sb <= 0) return false;
    const ix = xa - 2 * sa * nx, iz = za - 2 * sa * ny;
    const dx = xb - ix, dz = zb - iz;
    const den = dx * ty - dz * tx;
    if (Math.abs(den) < 1e-15) return false;
    const s = ((x1 - ix) * ty - (y1 - iz) * tx) / den;
    if (s <= 0 || s >= 1) return false;
    const px = ix + s * dx, pz = iz + s * dz;
    const L1 = Math.sqrt((px - xa) * (px - xa) + (pz - za) * (pz - za));
    FS.px = px; FS.pz = pz; FS.sin = sa / L1; FS.mis = px - 0.5 * (x1 + x2);
    return true;
  }

  /** Specular reflections; writes rays at index off.. of out, returns the number found. */
  function reflections(m, z, zs, d, wat, i0, i1, xa, za, xb, zb, win, out, off, maxn) {
    const p = m.p, lam = m.lam, ae = m.ae;
    let n = 0, prevOk = false, prevM = 0.0;
    for (let j = i0 + 1; j < i1 - 1; j++) {
      if (!facetSpecular(zs, d, j, xa, za, xb, zb)) { prevOk = false; continue; }
      let px = FS.px, pz = FS.pz, sinPsi = FS.sin;
      const mis = FS.mis;
      const fl = d[j + 1] - d[j];
      let hit = Math.abs(mis) <= 0.5 * fl;
      if (!hit && prevOk && (prevM > 0) !== (mis > 0)) {
        hit = true;
        px = d[j]; pz = zs[j];
        const L1 = Math.sqrt((px - xa) * (px - xa) + (pz - za) * (pz - za));
        const sl = (zs[j + 1] - zs[j - 1]) / (d[j + 1] - d[j - 1]);
        const cn = 1.0 / Math.sqrt(1 + sl * sl);
        sinPsi = ((xa - px) * (-sl * cn) + (za - pz) * cn) / L1;
      }
      prevOk = true;
      prevM = mis;
      if (!hit || sinPsi <= 0) continue;
      let dup = false;
      for (let q = 0; q < Math.min(n, maxn); q++) if (Math.abs(out.px[off + q] - px) < 3.0 * fl) dup = true;
      if (dup) continue;
      if (!clear(z, d, i0, i1, xa, za, px, pz, j - win, j + 1 + win)) continue;
      if (!clear(z, d, i0, i1, px, pz, xb, zb, j - win, j + 1 + win)) continue;
      const L1 = Math.sqrt((px - xa) * (px - xa) + (pz - za) * (pz - za));
      const L2 = Math.sqrt((xb - px) * (xb - px) + (zb - pz) * (zb - pz));
      let g, sig;
      if (wat[j]) {
        g = gammaTM(sinPsi, p.ew_r, p.ew_i);
        sig = p.water_roughness_m;
      } else {
        g = gammaTM(sinPsi, p.eg_r, p.eg_i);
        let acc = 0.0, cnt = 0;
        for (let k = Math.max(j - win, 0); k < Math.min(j + win + 1, z.length); k++) {
          acc += (z[k] - zs[k]) * (z[k] - zs[k]);
          cnt++;
        }
        sig = Math.sqrt(acc / Math.max(cnt, 1));
      }
      const t = 2 * Math.PI * sig * sinPsi / lam;
      const rho = Math.exp(-2.0 * t * t);
      const dd1 = px - xa, dd2 = xb - px;
      const tpsi = Math.max(sinPsi / Math.sqrt(Math.max(1 - sinPsi * sinPsi, 1e-12)), 1e-9);
      const div = 1.0 / Math.sqrt(1.0 + 2.0 * dd1 * dd2 / (ae * (dd1 + dd2) * tpsi));
      const cr = g[0] * rho * div, ci = g[1] * rho * div;
      const cabs = Math.hypot(cr, ci);
      let k;
      if (n < maxn) {
        k = n; n++;
      } else {
        k = 0;
        for (let q = 1; q < maxn; q++) {
          if (Math.hypot(out.cr[off + q], out.ci[off + q]) / out.L[off + q]
              < Math.hypot(out.cr[off + k], out.ci[off + k]) / out.L[off + k]) k = q;
        }
        if (cabs / (L1 + L2) <= Math.hypot(out.cr[off + k], out.ci[off + k]) / out.L[off + k]) continue;
      }
      out.L[off + k] = L1 + L2;
      out.cr[off + k] = cr;
      out.ci[off + k] = ci;
      out.et[off + k] = Math.atan2(pz - za, px - xa);
      out.er[off + k] = Math.atan2(pz - zb, xb - px);
      out.px[off + k] = px;
    }
    return n;
  }

  function bullington(z, d, N, za, zb, lam) {
    const D = d[N];
    let stim = -1e30;
    for (let i = 1; i < N; i++) stim = Math.max(stim, (z[i] - za) / d[i]);
    const str = (zb - za) / D;
    let luc, dbp, zbp, sT, sR;
    if (stim < str) {
      let vmax = -1e30, imax = 1;
      for (let i = 1; i < N; i++) {
        const v = (z[i] - (za * (D - d[i]) + zb * d[i]) / D) * Math.sqrt(2.0 * D / (lam * d[i] * (D - d[i])));
        if (v > vmax) { vmax = v; imax = i; }
      }
      luc = J(vmax);
      dbp = d[imax];
      zbp = za + (zb - za) * dbp / D;
      sT = str; sR = -str;
    } else {
      let srim = -1e30;
      for (let i = 1; i < N; i++) srim = Math.max(srim, (z[i] - zb) / (D - d[i]));
      dbp = (zb - za + srim * D) / (stim + srim);
      dbp = Math.min(Math.max(dbp, 1e-3), D - 1e-3);
      zbp = za + stim * dbp;
      const vb = (za + stim * dbp - (za * (D - dbp) + zb * dbp) / D) * Math.sqrt(2.0 * D / (lam * dbp * (D - dbp)));
      luc = J(vb);
      sT = stim; sR = srim;
    }
    const loss = luc + (1.0 - Math.exp(-luc / 6.0)) * (10.0 + 0.02 * D / 1000.0);
    return [loss, dbp, zbp, sT, sR];
  }

  function ldft(aKm, dKm, hte, hre, fGhz, eps, sigma) {
    const kh = 0.036 * Math.pow(aKm * fGhz, -1.0 / 3.0) * Math.pow((eps - 1.0) ** 2 + (18.0 * sigma / fGhz) ** 2, -0.25);
    const K = kh * Math.pow(eps ** 2 + (18.0 * sigma / fGhz) ** 2, 0.5);
    const beta = (1 + 1.6 * K ** 2 + 0.67 * K ** 4) / (1 + 4.5 * K ** 2 + 1.53 * K ** 4);
    const X = 21.88 * beta * Math.pow(fGhz / aKm ** 2, 1.0 / 3.0) * dKm;
    const fx = X >= 1.6 ? 11.0 + 10.0 * Math.log10(X) - 17.6 * X : -20.0 * Math.log10(X) - 5.6488 * Math.pow(X, 1.425);
    let gsum = 0.0;
    for (const h of [hte, hre]) {
      const Y = 0.9575 * beta * Math.pow(fGhz ** 2 / aKm, 1.0 / 3.0) * h;
      const B = beta * Y;
      let g = B > 2 ? 17.6 * Math.sqrt(B - 1.1) - 5.0 * Math.log10(B - 1.1) - 8.0 : 20.0 * Math.log10(B + 0.1 * B ** 3);
      g = Math.max(g, 2.0 + 20.0 * Math.log10(K));
      gsum += g;
    }
    return -fx - gsum;
  }

  function ldsph(aKm, dKm, hte, hre, lam, fGhz, eps, sigma) {
    hte = Math.max(hte, 0.1);
    hre = Math.max(hre, 0.1);
    const dlos = Math.sqrt(2 * aKm) * (Math.sqrt(0.001 * hte) + Math.sqrt(0.001 * hre));
    if (dKm >= dlos) return ldft(aKm, dKm, hte, hre, fGhz, eps, sigma);
    const c = (hte - hre) / (hte + hre);
    const mm = 250.0 * dKm ** 2 / (aKm * (hte + hre));
    let arg = 1.5 * c * Math.sqrt(3 * mm / (mm + 1) ** 3);
    arg = Math.min(Math.max(arg, -1.0), 1.0);
    const b = 2 * Math.sqrt((mm + 1) / (3 * mm)) * Math.cos(Math.PI / 3 + Math.acos(arg) / 3);
    const dse1 = dKm / 2 * (1 + b), dse2 = dKm - dse1;
    const hse = ((hte - 500 * dse1 ** 2 / aKm) * dse2 + (hre - 500 * dse2 ** 2 / aKm) * dse1) / dKm;
    const hreq = 17.456 * Math.sqrt(dse1 * dse2 * lam / dKm);
    if (hse > hreq) return 0.0;
    const aem = 500 * (dKm / (Math.sqrt(hte) + Math.sqrt(hre))) ** 2;
    const l = ldft(aem, dKm, hte, hre, fGhz, eps, sigma);
    if (l < 0) return 0.0;
    return (1 - hse / hreq) * l;
  }

  function deltaBullington(m, zraw, z, d, N, hTx, hRx, wfrac) {
    const p = m.p, ae = m.ae, lam = m.lam;
    const D = d[N];
    const za = zraw[0] + hTx, zb = zraw[N] + hRx;
    const [lba, dbp, zbp, sT, sR] = bullington(z, d, N, za, zb, lam);
    let v1 = 0.0, v2 = 0.0;
    for (let i = 1; i <= N; i++) {
      const dd = d[i] - d[i - 1];
      v1 += dd * (zraw[i] + zraw[i - 1]);
      v2 += dd * (zraw[i] * (2 * d[i] + d[i - 1]) + zraw[i - 1] * (d[i] + 2 * d[i - 1]));
    }
    const hst = Math.min((2 * v1 * D - v2) / (D * D), zraw[0]);
    const hsr = Math.min((v2 - v1 * D) / (D * D), zraw[N]);
    const hte = za - hst, hre = zb - hsr;
    const zse = m.buf.zse;
    for (let i = 0; i <= N; i++) zse[i] = d[i] * (D - d[i]) / (2.0 * ae);
    const lbs = bullington(zse, d, N, hte, hre, lam)[0];
    const aKm = ae / 1000.0, dKm = D / 1000.0, fGhz = p.fc_hz / 1e9;
    const land = ldsph(aKm, dKm, hte, hre, lam, fGhz, p.eps_land, p.sigma_land);
    const sea = ldsph(aKm, dKm, hte, hre, lam, fGhz, 80.0, 5.0);
    const lsph = wfrac * sea + (1 - wfrac) * land;
    return [lba + Math.max(lsph - lbs, 0.0), dbp, zbp, sT, sR];
  }

  /** Rays of one link (x, y in metres: east from the left edge, north from the bottom edge). */
  function rays(m, sx, sy, hTx, rx, ry, hRx) {
    const { W, H, mpp, ae, lam, p } = m;
    const { d, z, zraw, zs, wat } = m.buf;
    const dx = rx - sx, dy = ry - sy;
    const D = Math.sqrt(dx * dx + dy * dy);
    const N = Math.max(Math.floor(D / p.step_m), 2);
    const clearM = p.terminal_clearance_m;
    let nw = 0;
    for (let i = 0; i <= N; i++) {
      const t = i / N;
      const x = sx + dx * t, y = sy + dy * t;
      const col = x / mpp - 0.5, row = H - y / mpp - 0.5;
      d[i] = D * t;
      zraw[i] = bilinear(d[i] <= clearM || D - d[i] <= clearM ? m.G : m.T, W, H, row, col);
      z[i] = zraw[i] + d[i] * (D - d[i]) / (2.0 * ae);
      const rr = Math.min(Math.max(Math.floor(row + 0.5), 0), H - 1);
      const cc = Math.min(Math.max(Math.floor(col + 0.5), 0), W - 1);
      wat[i] = m.water[rr * W + cc];
      nw += wat[i];
    }
    zraw[0] = groundAt(m, sx, sy);
    zraw[N] = groundAt(m, rx, ry);
    z[0] = zraw[0];
    z[N] = zraw[N];
    const za = z[0] + hTx, zb = z[N] + hRx;
    const out = m.buf.out;  // reused: callers consume it before the next call
    out.L.fill(0); out.cr.fill(0); out.ci.fill(0); out.et.fill(0); out.er.fill(0); out.px.fill(0);
    out.n = 0; out.los = false; out.diff_db = 0.0;
    const [im, vm] = maxV(z, d, 0, N, za, zb, lam);
    const db = deltaBullington(m, zraw, z, d, N, hTx, hRx, nw / (N + 1.0));
    const geoLos = im < 0 || vm < 0.0;
    if (geoLos && db[0] <= 0.5) {
      const sn = m.smooth_n;
      for (let i = 0; i <= N; i++) {
        let a = 0.0, c = 0;
        for (let q = Math.max(i - sn, 0); q < Math.min(i + sn + 1, N + 1); q++) { a += z[q]; c++; }
        zs[i] = a / c;
      }
      const win = Math.max(Math.floor(sn / 2), 1);
      out.los = true;
      out.L[0] = Math.sqrt(D * D + (zb - za) * (zb - za));
      out.cr[0] = 1.0;
      out.et[0] = Math.atan2(zb - za, D);
      out.er[0] = Math.atan2(za - zb, D);
      // the Python kernel hands the reflection routine profile views of length N + 1
      const zv = z.subarray(0, N + 1), zsv = zs.subarray(0, N + 1);
      const nr = reflections(m, zv, zsv, d, wat, 0, N, 0.0, za, D, zb, win, out, 1, Math.min(p.max_reflections, MAXR - 1));
      out.n = 1 + nr;
    } else {
      out.los = geoLos;
      out.diff_db = db[0];
      const [jdb, dbp, zbp, sT, sR] = db;
      out.L[0] = Math.sqrt(dbp * dbp + (zbp - za) * (zbp - za)) + Math.sqrt((D - dbp) * (D - dbp) + (zbp - zb) * (zbp - zb));
      out.cr[0] = Math.pow(10, -jdb / 20.0);
      out.et[0] = Math.atan(sT);
      out.er[0] = Math.atan(sR);
      out.n = 1;
    }
    return out;
  }

  function elevGainDb(el, hpbw, sll) {
    const deg = el * 180 / Math.PI;
    return -Math.min(12.0 * (deg / hpbw) ** 2, sll);
  }

  /** |H|^2 on the evaluation subcarriers (antenna pattern relative to peak gain included). */
  function channelGain(m, r, out) {
    const p = m.p, K = p.n_sub;
    const lam = m.lam;
    if (r.n === 1) {  // flat channel: one ray
      const L = Math.max(r.L[0], 1.0);
      const g = Math.pow(10, (elevGainDb(r.et[0], p.hpbw_deg, p.sidelobe_db) + elevGainDb(r.er[0], p.hpbw_deg, p.sidelobe_db)) / 20);
      const a = lam / (4 * Math.PI * L) * g;
      const v = a * a * (r.cr[0] * r.cr[0] + r.ci[0] * r.ci[0]);
      for (let k = 0; k < K; k++) out[k] = v;
      return out;
    }
    const hr = m.buf.hr.fill(0), hi = m.buf.hi.fill(0);
    for (let q = 0; q < r.n; q++) {
      const L = Math.max(r.L[q], 1.0);
      const g = Math.pow(10, (elevGainDb(r.et[q], p.hpbw_deg, p.sidelobe_db) + elevGainDb(r.er[q], p.hpbw_deg, p.sidelobe_db)) / 20);
      const s = lam / (4 * Math.PI * L) * g;
      const ar = s * r.cr[q], ai = s * r.ci[q];
      for (let k = 0; k < K; k++) {
        const f = p.fc_hz + (k - (K - 1) / 2) * p.bandwidth_hz / K;
        const ph = -2 * Math.PI * f * L / C0;
        const c = Math.cos(ph), sn = Math.sin(ph);
        hr[k] += ar * c - ai * sn;
        hi[k] += ar * sn + ai * c;
      }
    }
    for (let k = 0; k < K; k++) out[k] = hr[k] * hr[k] + hi[k] * hi[k];
    return out;
  }

  /** Noise reference [dBm]: from the receiver sensitivity when given (autorelay.phy.noise_power_dbm), else kTB + NF. */
  function noiseDbm(p) {
    if (p.rx_sensitivity_dbm != null) return p.rx_sensitivity_dbm - (p.sensitivity_snr_db || 0);
    return -174.0 + 10 * Math.log10(p.bandwidth_hz) + p.noise_figure_db;
  }
  function mismatchDb(vswr) { const g = (vswr - 1) / (vswr + 1); return -10 * Math.log10(1 - g * g); }

  /** Cable + connector loss [dB] of one node (a number for every node, or per node). */
  function cableDb(p, name) { const c = p.cable_loss_db; return typeof c === "number" ? c : (c[name] || 0); }
  /** Link budget [dB] above the noise reference; cab = cable loss of both ends, fade margin taken off. */
  function budgetDb(p, txPowerDbm, cab) {
    return txPowerDbm + 2 * p.antenna_gain_dbi - cab - 2 * mismatchDb(p.vswr)
      - p.implementation_loss_db - (p.fade_margin_db || 0) - noiseDbm(p);
  }

  /** EESM e-SNR [dB] of a link with channel power gains `gain` and the given link budget. */
  function eesmDb(gain, budget, beta, scratch) {
    const K = gain.length;
    const lin = Math.pow(10, budget / 10);
    let mn = Infinity, mx = -Infinity;
    const s = scratch || new Float64Array(K);
    for (let k = 0; k < K; k++) {
      s[k] = lin * Math.max(gain[k], 1e-30);
      if (s[k] < mn) mn = s[k];
      if (s[k] > mx) mx = s[k];
    }
    if (mx === mn) return 10 * Math.log10(Math.max(mn, 1e-30));  // flat channel: EESM = SNR
    let acc = 0.0;
    for (let k = 0; k < K; k++) acc += Math.exp(-(s[k] - mn) / beta);
    const eff = mn - beta * Math.log(acc / K);
    return 10 * Math.log10(Math.max(eff, 1e-30));
  }

  /** Both directions of one link: e-SNR src->rx (src power) and rx->src (rx power), same reciprocal channel. */
  function linkEsnr(m, src, rx, txSrc, txRx, scratch, cab) {
    if (cab === undefined) cab = typeof m.p.cable_loss_db === "number" ? 2 * m.p.cable_loss_db : 0;
    const r = rays(m, src.x, src.y, src.h, rx.x, rx.y, rx.h);
    const g = channelGain(m, r, scratch || new Float64Array(m.p.n_sub));
    const beta = m.p.eesm_beta;
    return {
      fwd: eesmDb(g, budgetDb(m.p, txSrc, cab), beta, m.buf.s),
      rev: eesmDb(g, budgetDb(m.p, txRx, cab), beta, m.buf.s),
      los: r.los, diff_db: r.diff_db, n: r.n,
    };
  }

  // ---------------------------------------------------------------- topology (Dijkstra)
  // The only link cost: the modem's channel-occupancy (airtime) table, as autorelay.topology.AirtimeTable.
  /** Highest table level whose e-SNR threshold is met, -1 below the lowest. */
  function tableLevel(t, esnrDb) { let k = -1; for (let i = 0; i < t.snr_db.length; i++) if (esnrDb >= t.snr_db[i]) k = i; return k; }
  // under the lowest threshold a link is unusable (Infinity), as autorelay.topology.AirtimeTable
  function tableUL(t, esnrDb) { const k = tableLevel(t, esnrDb); return k >= 0 ? t.airtime[k] : Infinity; }
  function tableDL(t, esnrDb) { return esnrDb >= t.snr_db[t.dl_index] ? t.airtime[t.dl_index] : Infinity; }
  /** Cost model of a parameter set: the airtime table. */
  function costOf(p) { return p.airtime; }
  /** Numerator of rate = scale / (sum of the MS path costs): airtime[DL MCS] x rate[DL MCS]. */
  function rateScale(p) { return p.airtime.airtime[p.airtime.dl_index] * p.airtime.rate_mbps[p.airtime.dl_index] * 1e6; }

  /** Weight of the tree edge a -> b (a = parent: a -> b is DL, b -> a is UL). */
  function edgeWeight(esnr, a, b, traffic, t) {
    if (traffic === "mean") return tableUL(t, (esnr[a + ">" + b] + esnr[b + ">" + a]) / 2);  // mean of both directions [dB]
    let w = 0.0;
    if (traffic === "downlink" || traffic === "bidirectional") w += tableDL(t, esnr[a + ">" + b]);
    if (traffic === "uplink" || traffic === "bidirectional") w += tableUL(t, esnr[b + ">" + a]);
    return w;
  }

  function dijkstra(nodes, esnr, traffic, cost) {
    const dist = {}, parent = {}, done = new Set();
    for (const n of nodes) { dist[n] = Infinity; parent[n] = null; }
    dist.BS = 0.0;
    for (;;) {
      // heap order of the Python code: smallest (dist, name)
      let u = null;
      for (const n of nodes) {
        if (done.has(n) || dist[n] === Infinity) continue;
        if (u === null || dist[n] < dist[u] || (dist[n] === dist[u] && n < u)) u = n;
      }
      if (u === null) break;
      done.add(u);
      for (const v of nodes) {
        if (v === u || done.has(v)) continue;
        const w = edgeWeight(esnr, u, v, traffic, cost);
        if (dist[u] + w < dist[v]) { dist[v] = dist[u] + w; parent[v] = u; }
      }
    }
    return { dist, parent };
  }

  function topologyOf(parent) {  // parent: {child: parent}
    const depth = (n) => { let k = 0; while (n !== "BS") { n = parent[n]; k++; } return k; };
    const nodes = ["BS", ...Object.keys(parent)];
    const ds = nodes.map(depth);
    const maxd = Math.max(...ds);
    const label = Array.from({ length: maxd + 1 }, (_, k) => ds.filter((x) => x === k).length).join(":");
    const links = Object.keys(parent).map((c) => [parent[c], c]);
    links.sort((a, b) => depth(a[1]) - depth(b[1]) || (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : a[1] < b[1] ? -1 : a[1] > b[1] ? 1 : 0));
    return { label, links, description: links.map(([p, c]) => p + "->" + c).join(", "),
             usesRelay: links.some(([p, c]) => p === RELAY || c === RELAY) };
  }

  /** Trees rooted at BS in the order of autorelay.topology.enumerate_topologies. */
  function enumerateTrees(withRelay) {
    const nonRoot = [...MS_NODES, ...(withRelay ? [RELAY] : [])], all = ["BS", ...nonRoot], out = [];
    const rec = (k, par) => {
      if (k === nonRoot.length) {
        for (const n of nonRoot) {  // every node must reach BS without a cycle
          const seen = new Set();
          for (let cur = n; cur !== "BS"; cur = par[cur]) { if (seen.has(cur)) return; seen.add(cur); }
        }
        if (withRelay && !Object.values(par).includes(RELAY)) return;
        out.push(Object.assign({}, par));
        return;
      }
      for (const a of all) { if (a === nonRoot[k]) continue; par[nonRoot[k]] = a; rec(k + 1, par); }
      delete par[nonRoot[k]];
    };
    rec(0, {});
    return out;
  }

  /** Every tree (star, MS relaying, relay variants) with its Dijkstra cost and rate, best first (rank_trees). */
  function rankTrees(esnr, p, withRelay) {
    const trees = [...enumerateTrees(false), ...(withRelay ? enumerateTrees(true) : [])];
    const out = trees.map((par) => {
      let total = 0.0;
      for (const ms of MS_NODES) for (let n = ms; n !== "BS"; n = par[n]) total += edgeWeight(esnr, par[n], n, p.traffic, costOf(p));
      const t = topologyOf(par);
      return { label: t.label, description: t.description, usesRelay: t.usesRelay, links: t.links, total_cost: total,
               rate_bps: isFinite(total) ? rateScale(p) / total : 0 };
    });
    return out.map((r, i) => [r, i]).sort((a, b) => (a[0].total_cost - b[0].total_cost) || (a[1] - b[1])).map((x) => x[0]);
  }

  function decide(esnr, p, withRelay) {
    const nodes = ["BS", ...MS_NODES, ...(withRelay ? [RELAY] : [])];
    const { dist, parent } = dijkstra(nodes, esnr, p.traffic, costOf(p));
    const routes = {};  // every radio's shortest path to the control station (BS)
    for (const n of nodes) {
      if (n !== "BS" && !isFinite(dist[n])) { routes[n] = { path: null, cost: Infinity }; continue; }
      const path = [n]; for (let k = n; k !== "BS"; ) { k = parent[k]; path.push(k); }
      routes[n] = { path, cost: dist[n] };
    }
    const reach = MS_NODES.filter((m) => isFinite(dist[m])), lost = MS_NODES.filter((m) => !isFinite(dist[m]));
    const alternatives = rankTrees(esnr, p, withRelay);
    if (!reach.length) {
      return { label: "-", links: [], description: "통제국까지 유효 경로가 있는 MS가 없음", usesRelay: false, feasible: false,
               reachable: [], unreachable: lost, total_cost: Infinity, rate_bps: 0, path_cost: { MS1: dist.MS1, MS2: dist.MS2 },
               routes, alternatives };
    }
    const used = {};
    for (const ms of reach) { let n = ms; while (n !== "BS") { used[n] = parent[n]; n = parent[n]; } }
    const topo = topologyOf(used);
    const total = reach.reduce((a, m) => a + dist[m], 0);
    const desc = topo.description + lost.map((m) => `; ${m}: 유효 경로 없음`).join("");
    return { ...topo, description: desc, feasible: !lost.length, reachable: reach, unreachable: lost, total_cost: total,
             rate_bps: rateScale(p) / total, path_cost: { MS1: dist.MS1, MS2: dist.MS2 }, routes, alternatives };
  }

  const MS_PATHS = {  // order of autorelay.topology._ms_paths(True)
    MS1: [["BS", "MS1"], ["BS", "MS2", "MS1"], ["BS", "R", "MS1"], ["BS", "MS2", "R", "MS1"], ["BS", "R", "MS2", "MS1"]],
    MS2: [["BS", "MS2"], ["BS", "MS1", "MS2"], ["BS", "R", "MS2"], ["BS", "MS1", "R", "MS2"], ["BS", "R", "MS1", "MS2"]],
  };

  /** Relay at every candidate: tab = scalar e-SNR among BS/MS1/MS2, rel[n] = {to: Float32Array, from: Float32Array}. */
  function relayGrid(tab, rel, p) {
    const N = rel.BS.to.length;
    const rate = new Float64Array(N), usesRelay = new Uint8Array(N), best = { MS1: new Uint8Array(N), MS2: new Uint8Array(N) };
    const margin = new Float64Array(N), reach = new Uint8Array(N);
    const e = Object.assign({}, tab);
    const cost = costOf(p), w = (a, b) => edgeWeight(e, a, b, p.traffic, cost);
    const fixed = {};
    for (const a of NODE_NAMES) for (const b of NODE_NAMES) if (a !== b) fixed[a + ">" + b] = w(a, b);
    for (let i = 0; i < N; i++) {
      for (const n of NODE_NAMES) { e[n + ">R"] = rel[n].to[i]; e["R>" + n] = rel[n].from[i]; }
      let total = 0.0, ur = 0, nr = 0;
      for (const ms of MS_NODES) {
        let bc = Infinity, bi = 0;
        MS_PATHS[ms].forEach((path, pi) => {
          let c = 0.0;
          for (let k = 0; k < path.length - 1; k++) {
            const key = path[k] + ">" + path[k + 1];
            c += key in fixed ? fixed[key] : w(path[k], path[k + 1]);
          }
          if (c < bc) { bc = c; bi = pi; }
        });
        best[ms][i] = bi;
        if (!isFinite(bc)) continue;  // this MS has no valid path to BS
        total += bc; nr++;
        if (MS_PATHS[ms][bi].includes(RELAY)) ur = 1;
      }
      reach[i] = nr;
      rate[i] = nr ? rateScale(p) / total : 0;  // per connected MS
      usesRelay[i] = ur;
      // weakest e-SNR over the relay links in use (tie-break between candidates of equal rate)
      let mg = Infinity;
      for (const ms of MS_NODES) {
        const path = MS_PATHS[ms][best[ms][i]];
        if (path.some((n, k) => k < path.length - 1 && !isFinite(w(n, path[k + 1])))) continue;
        for (let k = 0; k < path.length - 1; k++) {
          if (path[k] === RELAY || path[k + 1] === RELAY) mg = Math.min(mg, e[path[k] + ">" + path[k + 1]], e[path[k + 1] + ">" + path[k]]);
        }
      }
      margin[i] = mg === Infinity ? -Infinity : mg;
    }
    return { rate, usesRelay, best, margin, reach };
  }

  function treeFromPaths(p1, p2) {
    const parent = {};
    for (const path of [p1, p2]) for (let k = 0; k < path.length - 1; k++) if (!(path[k + 1] in parent)) parent[path[k + 1]] = path[k];
    return topologyOf(parent);
  }

  // ---------------------------------------------------------------- relay candidates
  function roundHalfEven(x) {
    const r = Math.round(x);
    return Math.abs(x % 1) === 0.5 && r % 2 !== 0 ? r - 1 : r;
  }

  function candidateGrid(m, step, border, onWater) {
    if (onWater === undefined) onWater = !!m.p.relay_on_water;
    const Wm = m.W * m.mpp, Hm = m.H * m.mpp;
    const xs = [], ys = [];
    for (let i = 0, n = Math.ceil((Wm - border - (border + step / 2)) / step); i < n; i++) xs.push(border + step / 2 + i * step);
    for (let i = 0, n = Math.ceil((Hm - border - (border + step / 2)) / step); i < n; i++) ys.push(border + step / 2 + i * step);
    const x = [], y = [], ii = [], jj = [];
    for (let i = 0; i < ys.length; i++) {
      for (let j = 0; j < xs.length; j++) {
        const col = Math.min(Math.max(roundHalfEven(xs[j] / m.mpp - 0.5), 0), m.W - 1);
        const row = Math.min(Math.max(roundHalfEven(m.H - ys[i] / m.mpp - 0.5), 0), m.H - 1);
        if (m.water[row * m.W + col] && !onWater) continue;
        x.push(xs[j]); y.push(ys[i]); ii.push(i); jj.push(j);
      }
    }
    return { x: Float64Array.from(x), y: Float64Array.from(y), i: Int32Array.from(ii), j: Int32Array.from(jj),
             ny: ys.length, nx: xs.length, step };
  }

  /** TerrainPlanner.local_grid: a `step` lattice (anchored at each centre) within `radius` of a centre; win = centre index. */
  function localGrid(m, centers, step, radius, border, onWater) {
    if (onWater === undefined) onWater = !!m.p.relay_on_water;
    const Wm = m.W * m.mpp, Hm = m.H * m.mpp, k = Math.ceil(radius / step), seen = new Set();
    const x = [], y = [], win = [];
    centers.forEach(([cx, cy], w) => {
      for (let b = -k; b <= k; b++) for (let a = -k; a <= k; a++) {
        if ((a * a + b * b) * step * step > radius * radius + 1e-9) continue;
        const px = cx + a * step, py = cy + b * step;
        if (px < border || px > Wm - border || py < border || py > Hm - border) continue;
        const key = Math.round(px * 1e3) + "," + Math.round(py * 1e3);
        if (seen.has(key)) continue;
        seen.add(key);
        const col = Math.min(Math.max(roundHalfEven(px / m.mpp - 0.5), 0), m.W - 1);
        const row = Math.min(Math.max(roundHalfEven(m.H - py / m.mpp - 0.5), 0), m.H - 1);
        if (m.water[row * m.W + col] && !onWater) continue;
        x.push(px); y.push(py); win.push(w);
      }
    });
    return { x: Float64Array.from(x), y: Float64Array.from(y), win: Int32Array.from(win), step, nwin: centers.length };
  }
  /** TerrainPlanner.refine: the best fine points in ranking order, as many as there were windows (the windows of
   * neighbouring candidates overlap, so a point is not tied to one window). picks[0] is the drone spot. */
  function refinePick(fg, score, margin) {
    const idx = Array.from({ length: score.length }, (_, i) => i);
    const mg = (i) => (margin ? margin[i] : 0), nr = (i) => Math.floor(score[i] / BIG);
    const cmp = (x, y) => (x > y ? -1 : x < y ? 1 : 0);
    idx.sort((a, b) => cmp(nr(a), nr(b)) || cmp(score[a], score[b]) || cmp(mg(a), mg(b)));  // stable: full ties keep lattice order
    return idx.slice(0, fg.nwin);
  }

  /** Ranking score of TerrainPlanner.run: MSs connected first, then rate (BIG exceeds any rate). */
  const BIG = 1e10;
  function relayScore(g) { const s = new Float64Array(g.rate.length); for (let i = 0; i < s.length; i++) s[i] = g.reach[i] * BIG + g.rate[i]; return s; }
  /** TerrainPlanner.rank / pick: the topK best cells, neighbours allowed (no spacing rule); the drone stands exactly at the point. */
  function pickCandidates(grid, score, topK, margin) {
    const idx = Array.from({ length: score.length }, (_, i) => i);
    const mg = (i) => (margin ? margin[i] : 0), nr = (i) => Math.floor(score[i] / BIG);
    const cmp = (x, y) => (x > y ? -1 : x < y ? 1 : 0);  // descending, safe with +-Infinity
    // MSs connected first, then the score (rate = scale / Dijkstra cost sum, so the lowest cost), then the weakest
    // relay link (ties are common). The sort is stable, so cells that tie on all three keep grid order; that only happens
    // when no cell gains from the drone (every margin -inf), and then no drone is shown.
    idx.sort((a, b) => cmp(nr(a), nr(b)) || cmp(score[a], score[b]) || cmp(mg(a), mg(b)));
    return idx.slice(0, topK);
  }

  // ---------------------------------------------------------------- whole plan (TerrainPlanner.run)
  /** Node e-SNR table: each directed link traced from its transmitter, as TerrainPlanner.node_table. */
  function nodeTable(m, nodes, s) {
    const tab = {}, info = {};
    for (const a of NODE_NAMES) for (const b of NODE_NAMES) {
      if (a === b) continue;
      const r = linkEsnr(m, { x: nodes[a].x, y: nodes[a].y, h: s.heights[a] }, { x: nodes[b].x, y: nodes[b].y, h: s.heights[b] },
                         s.tx[a], s.tx[b], undefined, cableDb(m.p, a) + cableDb(m.p, b));
      tab[a + ">" + b] = r.fwd;
      info[a + ">" + b] = { los: r.los, diff_db: r.diff_db, n: r.n };
    }
    return { tab, info };
  }

  /** e-SNR node <-> relay for candidates [i0, i1) of the grid (node transmits for `to`, relay for `from`). */
  function relayLinks(m, node, hNode, txNode, grid, i0, i1, hR, txR, cab) {
    const to = new Float32Array(i1 - i0), from = new Float32Array(i1 - i0);
    const scratch = new Float64Array(m.p.n_sub), src = { x: node.x, y: node.y, h: hNode };
    for (let q = i0; q < i1; q++) {
      const r = linkEsnr(m, src, { x: grid.x[q], y: grid.y[q], h: hR }, txNode, txR, scratch, cab);
      to[q - i0] = r.fwd;
      from[q - i0] = r.rev;
    }
    return { to, from };
  }

  /** Node table plus the relay links at rxy; `info` (optional) receives LOS / diffraction per relay link. */
  function finalTable(m, tab, nodes, s, rxy, info) {
    const t = Object.assign({}, tab);
    for (const n of NODE_NAMES) {
      const rn = { x: nodes[n].x, y: nodes[n].y, h: s.heights[n] }, rr = { x: rxy[0], y: rxy[1], h: s.heights.R };
      const cab = cableDb(m.p, n) + cableDb(m.p, "R");
      const a = linkEsnr(m, rr, rn, s.tx.R, s.tx[n], undefined, cab), b = linkEsnr(m, rn, rr, s.tx[n], s.tx.R, undefined, cab);
      t["R>" + n] = a.fwd;
      t[n + ">R"] = b.fwd;
      if (info) {
        info["R>" + n] = { los: a.los, diff_db: a.diff_db, n: a.n };
        info[n + ">R"] = { los: b.los, diff_db: b.diff_db, n: b.n };
      }
    }
    return t;
  }

  function plan(m, nodes, s) {
    const p = Object.assign({}, m.p, s.params || {});
    const { tab, info } = nodeTable(m, nodes, s);
    const base = decide(tab, p, false);
    const grid = candidateGrid(m, s.grid_m || p.grid_m, p.border_m, !!p.relay_on_water);
    const rel = {};
    for (const n of NODE_NAMES) rel[n] = relayLinks(m, nodes[n], s.heights[n], s.tx[n], grid, 0, grid.x.length, s.heights.R, s.tx.R,
                                                 cableDb(m.p, n) + cableDb(m.p, "R"));
    const g = relayGrid(tab, rel, p);
    const cands = pickCandidates(grid, relayScore(g), p.top_k, g.margin);
    let xy = [grid.x[cands[0]], grid.y[cands[0]]], fine = null;
    if (p.fine_m && p.fine_m < grid.step && cands.length) {  // TerrainPlanner.refine
      const fg = localGrid(m, cands.map((i) => [grid.x[i], grid.y[i]]), p.fine_m, p.fine_radius_m || 1.5 * grid.step, p.border_m, !!p.relay_on_water);
      if (fg.x.length) {
        const frel = {};
        for (const n of NODE_NAMES) frel[n] = relayLinks(m, nodes[n], s.heights[n], s.tx[n], fg, 0, fg.x.length, s.heights.R, s.tx.R,
                                                      cableDb(m.p, n) + cableDb(m.p, "R"));
        const fgr = relayGrid(tab, frel, p), picks = refinePick(fg, relayScore(fgr), fgr.margin);
        xy = [fg.x[picks[0]], fg.y[picks[0]]];
        fine = { grid: fg, rate: fgr.rate, usesRelay: fgr.usesRelay, cands: picks };
      }
    }
    const fin = finalTable(m, tab, nodes, s, xy);
    return { tab, info, base, grid, rel, rate: g.rate, usesRelay: g.usesRelay, best: g.best, cands, fine,
             relay_xy: xy, final_table: fin, final: decide(fin, p, true) };
  }

  const api = { cableDb, tableLevel, costOf, rateScale, edgeWeight, nodeTable, relayLinks, finalTable, plan, makeModel, rays, channelGain, eesmDb, budgetDb, linkEsnr, groundAt, decide, dijkstra, relayGrid,
                treeFromPaths, relayScore, BIG, rankTrees, enumerateTrees, candidateGrid, localGrid, refinePick, pickCandidates, MS_PATHS, NODE_NAMES, RELAY };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else root.AutoRelayEngine = api;
})(typeof self !== "undefined" ? self : this);
