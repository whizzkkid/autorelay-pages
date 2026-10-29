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
  const KMAX = 4;              // reflection slots (max_reflections is capped here)
  const OUT_CAP = 32;         // reflection rays per link (output capacity, the same for every max_reflections)
  const MAXR = 1 + OUT_CAP;    // rays per link: the direct / diffracted ray and up to OUT_CAP reflection rays
  // continuous ray model (autorelay/terrain.py)
  const FADE_X1 = Math.PI;    // k * dL [rad] at which a specular point reaches full weight (barrier lambda / 2)
  const WRAY_J0 = 0.0;        // delta-Bullington loss [dB] up to which the ray model has full weight ...
  const WRAY_J1 = 3.0;        // ... and from which the diffraction model alone is used
  const LEG_VSHIFT = 0.78062; // leg loss J(v_max - LEG_VSHIFT): a clear leg gives exactly 0 dB
  const CAP_BETA = 0.5;       // soft cap: a region has full weight at a strength >= (1 + CAP_BETA) x the cut level
  const CUT_LO = 0.25;        // cut level: mean region strength over the counts [maxn + CUT_LO, maxn + CUT_HI] ...
  const CUT_HI = 0.75;        // ... i.e. the (maxn + 1)-th strongest region
  const FAINT_LO = 5e-4;      // a reflection weaker than FAINT_LO x the free-space direct ray is not output (handed
  const FAINT_HI = 1e-3;      // to its tight partners), full output from FAINT_HI (smoothstep)
  const TIE_REL = 0.25;       // persistence tie band: full claim at a barrier-depth ratio (2 + TIE_REL) / (2 - TIE_REL)
  const TIE_BLEND = 2.0;      // the same claims with the widest band (full only at zero depth): amplitude blend masses
  const EG_BOUND = 8.0;       // a member carries its region's external weight e up to EG_BOUND x its own weight
  const SIN_EPS = 1e-4;       // grazing fade
  const GB_LO = 1.9, GB_HI = 2.1;    // P.452 G(Y): branch blend over B in [GB_LO, GB_HI] (0.0175 dB apart at B = 2)
  const FX_LO = 1.55, FX_HI = 1.65;  // P.452 F(X): branch blend over X in [FX_LO, FX_HI] (7e-6 dB apart at X = 1.6)
  const END_EPS = 1e-6;       // [m] an outermost sample pair closer than this to the terminals is dropped
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
    const maxN = Math.ceil(Math.hypot(W, H) * data.mpp / p.step_m) + 4;  // N <= D / step + 2
    const mr = 2 * maxN + 2, F64 = (n) => new Float64Array(n);
    return {
      W, H, T, G, water, mpp: data.mpp, p,
      lam: C0 / p.fc_hz, ae: p.k_factor * R_EARTH, smooth_n: Math.max(Math.round(p.smooth_m / p.step_m / 2), 1),
      buf: {
        d: F64(maxN), z: F64(maxN), zraw: F64(maxN), zs: F64(maxN), zse: F64(maxN),
        wv: F64(maxN), pres: F64(maxN), ms: F64(maxN), F: F64(maxN),
        Ux: F64(maxN), Uz: F64(maxN), f: F64(maxN),
        r_x: F64(mr), r_y: F64(mr), r_L: F64(mr), r_d: F64(mr), r_s: F64(mr), r_t: new Int8Array(mr),
        wg: F64(mr), eg: F64(mr), mu: F64(mr),
        dE: F64(6 * maxN + 8), ety: new Int8Array(6 * maxN + 8),
        mi: new Int32Array(mr), mc: F64(mr), cidx: new Int32Array(mr),
        c_cr: F64(mr), c_ci: F64(mr), c_r: new Int32Array(mr), c_s: F64(mr), c_m: F64(mr),
        fac: F64(mr), c_br: F64(mr), c_bi: F64(mr), kap: F64(mr), sl: F64(mr), rho0: F64(mr),
        u: F64(mr), g: F64(mr), ek: F64(mr), Dn: F64(mr),
        s_rho: F64(mr), s_kap: F64(mr), s_b: new Int32Array(mr), done: new Uint8Array(mr),
        o_b: new Int32Array(mr), o_w: F64(mr), o_e: F64(mr),
        hr: F64(p.n_sub), hi: F64(p.n_sub), s: F64(p.n_sub),
        out: { n: 0, L: F64(MAXR), cr: F64(MAXR), ci: F64(MAXR), et: F64(MAXR), er: F64(MAXR), los: false, diff_db: 0 },
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

  /** Bilinear DSM height (returned) and bilinear water fraction (TW.wv) at one point, shared weights. */
  const TW = { wv: 0 };
  function bilinearTW(R, Wm, W, H, row, col) {
    const r0 = Math.min(Math.max(Math.floor(row), 0), H - 2);
    const c0 = Math.min(Math.max(Math.floor(col), 0), W - 2);
    const fr = Math.min(Math.max(row - r0, 0), 1);
    const fc = Math.min(Math.max(col - c0, 0), 1);
    const w00 = (1 - fr) * (1 - fc), w01 = (1 - fr) * fc, w10 = fr * (1 - fc), w11 = fr * fc;
    const i = r0 * W + c0;
    let wv = 0.0;
    if (Wm[i]) wv += w00;
    if (Wm[i + 1]) wv += w01;
    if (Wm[i + W]) wv += w10;
    if (Wm[i + W + 1]) wv += w11;
    TW.wv = wv;
    return R[i] * w00 + R[i + 1] * w01 + R[i + W] * w10 + R[i + W + 1] * w11;
  }

  function groundAt(m, x, y) {
    return bilinear(m.G, m.W, m.H, m.H - y / m.mpp - 0.5, x / m.mpp - 0.5);
  }

  /** Knife-edge loss J(v) [dB], exactly continuous (the formula crosses 0 at v = -0.7806194). */
  function J(v) {
    if (v <= -0.79) return 0.0;
    const x = v - 0.1;
    return Math.max(6.9 + 20.0 * Math.log10(Math.sqrt(x * x + 1.0) + x), 0.0);
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

  // ---------------------------------------------------------------- continuous ray model (autorelay/terrain.py)
  /** Index i in [1, N] of the profile interval [d[i-1], d[i]] that contains x (interior spacing s). */
  function seg(d, N, s, x) {
    if (x <= d[1]) return 1;
    if (x >= d[N - 1]) return N;
    let j = 1 + Math.floor((x - d[1]) / s);
    if (j > N - 2) j = N - 2;
    if (j < 1) j = 1;
    return j + 1;
  }

  /** Box filter of half-width a of the piecewise-linear profile, point-symmetric continuation: heights zs, slopes ms. */
  function smoothProfile(z, d, N, a, F, zs, ms) {
    const D = d[N];
    F[0] = 0.0;
    for (let i = 1; i <= N; i++) F[i] = F[i - 1] + 0.5 * (d[i] - d[i - 1]) * (z[i] + z[i - 1]);
    let jp = 1, jm = 1, ep = N, em = N;
    for (let i = 0; i <= N; i++) {
      let x = d[i] + a, j, u;
      if (x <= D) {
        while (jp < N && d[jp] < x) jp++;
        j = jp;
        u = x;
      } else {
        u = 2.0 * D - x;
        while (ep > 1 && d[ep - 1] > u) ep--;
        j = ep;
      }
      let zq = z[j - 1] + (z[j] - z[j - 1]) * (u - d[j - 1]) / (d[j] - d[j - 1]);
      let Fq = F[j - 1] + (u - d[j - 1]) * 0.5 * (z[j - 1] + zq);
      let zp, Fp;
      if (x <= D) {
        zp = zq;
        Fp = Fq;
      } else {
        zp = 2.0 * z[N] - zq;
        Fp = Fq + 2.0 * z[N] * (x - D);
      }
      x = d[i] - a;
      if (x >= 0.0) {
        while (jm < N && d[jm] < x) jm++;
        j = jm;
        u = x;
      } else {
        u = -x;
        while (em > 1 && d[em - 1] > u) em--;
        j = em;
      }
      zq = z[j - 1] + (z[j] - z[j - 1]) * (u - d[j - 1]) / (d[j] - d[j - 1]);
      Fq = F[j - 1] + (u - d[j - 1]) * 0.5 * (z[j - 1] + zq);
      let zm, Fm;
      if (x >= 0.0) {
        zm = zq;
        Fm = Fq;
      } else {
        zm = 2.0 * z[0] - zq;
        Fm = Fq + 2.0 * z[0] * x;
      }
      zs[i] = (Fp - Fm) / (2.0 * a);
      ms[i] = (zp - zm) / (2.0 * a);
    }
  }

  /** 0 for x <= 0, 1 for x >= FADE_X1, sin^2 ramp in between. */
  function fade(x) {
    if (x <= 0.0) return 0.0;
    if (x >= FADE_X1) return 1.0;
    const q = Math.sin(0.5 * Math.PI * x / FADE_X1);
    return q * q;
  }

  /** Weight of the ray model vs. the diffraction model: smoothstep 1 -> 0 over [WRAY_J0, WRAY_J1]. */
  function wray(jdb) {
    if (jdb <= WRAY_J0) return 1.0;
    if (jdb >= WRAY_J1) return 0.0;
    const u = (jdb - WRAY_J0) / (WRAY_J1 - WRAY_J0);
    return 1.0 - u * u * (3.0 - 2.0 * u);
  }

  /** The root in [0, 1] of a2 t^2 + b1 t + c0 when the values at t = 0 and t = 1 differ in sign (0 counts as positive). */
  function rootOdd(a2, b1, c0) {
    let t;
    if (a2 === 0.0) {
      t = -c0 / b1;
    } else {
      let disc = b1 * b1 - 4.0 * a2 * c0;
      if (disc < 0.0) disc = 0.0;
      const sq = Math.sqrt(disc);
      const q = b1 >= 0.0 ? -0.5 * (b1 + sq) : -0.5 * (b1 - sq);
      if (q === 0.0) {
        t = 0.0;
      } else {
        const t1 = q / a2, t2 = c0 / q;
        const e1 = Math.max(-t1, t1 - 1.0, 0.0), e2 = Math.max(-t2, t2 - 1.0, 0.0);
        if (e1 < e2) t = t1;
        else if (e2 < e1) t = t2;
        else if (Math.min(t1, 1.0 - t1) >= Math.min(t2, 1.0 - t2)) t = t1;  // one is an exact zero at an end
        else t = t2;
      }
    }
    return Math.min(Math.max(t, 0.0), 1.0);
  }

  /** Largest Fresnel parameter (floor 0) of the raw profile above the leg (xt, zt) -> (px, pz); samples within r0 of
   * the reflection point are ignored and ramped in linearly up to r1. */
  function legVmax(z, d, N, s, xt, zt, px, pz, lam, r0, r1) {
    const lo = Math.min(xt, px), hi = Math.max(xt, px), Lh = hi - lo;
    let best = 0.0;
    if (Lh <= 0.0) return best;
    const iLo = seg(d, N, s, lo), iHi = seg(d, N, s, hi) - 1;
    const sl = (pz - zt) / (px - xt);
    for (let i = iLo; i <= iHi; i++) {
      const x = d[i];
      const h = z[i] - (zt + sl * (x - xt));
      if (h <= 0.0) continue;
      if (x <= lo || x >= hi) continue;
      const r = Math.abs(px - x);
      if (r <= r0) continue;
      let v = h * Math.sqrt(2.0 * Lh / (lam * Math.abs(x - xt) * r));
      if (r < r1) {
        const g = (r - r0) / (r1 - r0);
        v = g * v;
      }
      if (v > best) best = v;
    }
    return best;
  }

  /** Complementary tie ramp: claim(u) + claim(-u) = 1. */
  function claim(u) {
    if (u <= -1.0) return 0.0;
    if (u >= 1.0) return 1.0;
    const q = Math.sin(0.25 * Math.PI * (u + 1.0));
    return q * q;
  }

  /** Integral of c0 + b1 t + a2 t^2 over [ta, tb] as (tb - ta) x its mean value. */
  function chordInt(c0, b1, a2, ta, tb) {
    return (tb - ta) * (c0 + 0.5 * b1 * (ta + tb) + a2 * (ta * ta + ta * tb + tb * tb) / 3.0);
  }

  /** Extended alternating sequence [B_L, mirrors about 0, roots, mirrors about D, B_R] as types ety and local steps
   * dE[e] = value[e+1] - value[e]; steps of the wrong sign (rounding) are set to 0 (r_d in place). */
  function extendedSteps(r_d, r_t, nr, tail, dE, ety) {
    if ((r_d[0] > 0.0 && r_t[0] > 0) || (r_d[0] < 0.0 && r_t[0] < 0)) r_d[0] = 0.0;
    for (let q = 1; q < nr; q++) {
      if ((r_d[q] < 0.0 && r_t[q - 1] > 0) || (r_d[q] > 0.0 && r_t[q - 1] < 0)) r_d[q] = 0.0;
    }
    if ((tail < 0.0 && r_t[nr - 1] > 0) || (tail > 0.0 && r_t[nr - 1] < 0)) tail = 0.0;
    const hl = r_d[0];
    dE[0] = tail;
    for (let e = 1; e < nr; e++) dE[e] = r_d[nr - e];
    dE[nr] = 2.0 * hl;
    for (let q = 0; q < nr - 1; q++) dE[nr + 1 + q] = r_d[q + 1];
    dE[2 * nr] = 2.0 * tail;
    for (let k = 0; k < nr - 1; k++) dE[2 * nr + 1 + k] = r_d[nr - 1 - k];
    dE[3 * nr] = hl;
    for (let q = 0; q < nr; q++) {
      ety[nr - q] = -r_t[q];
      ety[nr + 1 + q] = r_t[q];
      ety[3 * nr - q] = -r_t[q];
    }
    ety[0] = r_t[nr - 1];
    ety[3 * nr + 1] = r_t[0];
  }

  /** Fold / end weight w of root q (returned) and the external weight e of its stationary region (PWE.e): fade(k *
   * persistence) of its path-length extremum, values relative to the root from the local steps; soft elder rule with
   * complementary claims (two nearly equal extrema share one weight), combined through the running maximum Q (a fold
   * pair elsewhere changes nothing); for e each claim is scaled by fade(k * range to the candidate). */
  const PWE = { e: 0, w2: 0 };
  function persistenceWeight(dE, ety, nr, q, kw) {
    const p = nr + 1 + q, t = ety[p];
    const sg = t > 0 ? 1.0 : -1.0;
    const ne = 3 * nr + 2;
    let w = 1.0, e = 1.0, w2 = 1.0;
    for (let dirn = -1; dirn <= 1; dirn += 2) {
      let rel = 0.0, M = 0.0, Q = 0.0, acc = 0.0, Qe = 0.0, acce = 0.0, Q2 = 0.0, acc2 = 0.0;
      for (let j = p + dirn; j >= 0 && j < ne; j += dirn) {
        if (dirn > 0) rel += sg * dE[j - 1];
        else rel -= sg * dE[j];
        if (ety[j] === t) {
          const dd = M + (M - rel);
          const den = TIE_REL * dd;
          let qk, qk2;
          if (den > 0.0) {
            qk = claim(-2.0 * rel / den);
            qk2 = claim(-2.0 * rel / (TIE_BLEND * dd));
          } else {
            qk = 0.5;
            qk2 = 0.5;
          }
          if (qk > Q) {
            acc += (qk - Q) * fade(kw * M);
            Q = qk;
          }
          const qe = qk * fade(kw * (M - Math.min(rel, 0.0)));  // the claim of a candidate outside the root's region
          if (qe > Qe) {
            acce += (qe - Qe) * fade(kw * M);
            Qe = qe;
          }
          if (qk2 > Q2) {
            acc2 += (qk2 - Q2) * fade(kw * M);
            Q2 = qk2;
          }
          if (Q >= 1.0 && Qe >= 1.0 && Q2 >= 1.0) break;
        } else if (rel > M) {
          M = rel;
          if (kw * M >= FADE_X1) break;  // every later fade is 1: the rest adds exactly 1 - Q (1 - Qe, 1 - Q2)
        }
      }
      if (Q < 1.0) acc += (1.0 - Q) * fade(kw * M);
      if (Qe < 1.0) acce += (1.0 - Qe) * fade(kw * M);
      if (Q2 < 1.0) acc2 += (1.0 - Q2) * fade(kw * M);
      if (acc < w) w = acc;
      if (acce < e) e = acce;
      if (acc2 < w2) w2 = acc2;
    }
    PWE.e = e;
    PWE.w2 = w2;
    return w;
  }

  /** Members of the stationary region around root q (same-type real roots j with closeness c = 1 - fade(k b_qj) > 0):
   * mi[0] = q, mc[0] = 1, then the walk to the left, then to the right; returns their number. */
  function regionMembers(dE, ety, nr, q, kw, mi, mc) {
    const p = nr + 1 + q, t = ety[p];
    const sg = t > 0 ? 1.0 : -1.0;
    mi[0] = q;
    mc[0] = 1.0;
    let m = 1;
    for (let dirn = -1; dirn <= 1; dirn += 2) {
      let rel = 0.0, M = 0.0;
      for (let j = p + dirn; j >= nr + 1 && j <= 2 * nr; j += dirn) {
        if (dirn > 0) rel += sg * dE[j - 1];
        else rel -= sg * dE[j];
        if (ety[j] === t) {
          const c = 1.0 - fade(kw * (M - Math.min(rel, 0.0)));
          if (c > 0.0) {
            mi[m] = j - nr - 1;
            mc[m] = c;
            m++;
          }
        } else if (rel > M) {
          M = rel;
          if (kw * M >= FADE_X1) break;
        }
      }
    }
    return m;
  }

  /** Summed weight S (returned) and external weight R (CS.r) of the stationary region around root q. */
  const CS = { r: 0 };
  function clusterSum(dE, ety, wg, eg, nr, q, kw, mi, mc) {
    const m = regionMembers(dE, ety, nr, q, kw, mi, mc);
    let S = wg[q], Rg = eg[q];
    for (let k = 1; k < m; k++) {
      const j = mi[k], c = mc[k];
      S += c * wg[j];
      if (c * eg[j] > Rg) Rg = c * eg[j];
    }
    CS.r = Rg;
    return S;
  }

  /** Soft-cap weight of strength a at the cut level lv. */
  function capH(a, lv) {
    if (a <= lv) return 0.0;
    const den = CAP_BETA * lv;  // can underflow to 0 for a subnormal lv
    return den > 0.0 ? Math.min(1.0, (a - lv) / den) : 1.0;
  }

  /** Amplitude factor of the leg obstruction of a reflection at (x, y). */
  function legFactor(z, d, N, s, za, zb, x, y, lam, r0, r1) {
    const D = d[N];
    const va = legVmax(z, d, N, s, 0.0, za, x, y, lam, r0, r1);
    const vb = legVmax(z, d, N, s, D, zb, x, y, lam, r0, r1);
    let jl = 0.0;
    if (va > 0.0) jl += J(va - LEG_VSHIFT);  // J(0 - LEG_VSHIFT) == 0: the skip only saves time
    if (vb > 0.0) jl += J(vb - LEG_VSHIFT);
    return jl > 0.0 ? Math.pow(10, -jl / 20.0) : 1.0;
  }

  /** Cut level: mean of the quantile function of the region strengths (sorted descending, counts s_kap) over the
   * counts [K + CUT_LO, K + CUT_HI], i.e. the (K + 1)-th strongest region. */
  function cutLevel(s_rho, s_kap, ns, K) {
    const lo = K + CUT_LO, hi = K + CUT_HI;
    let acc = 0.0, cum = 0.0;
    for (let p = 0; p < ns; p++) {
      const c1 = cum + s_kap[p];
      const ov = Math.min(c1, hi) - Math.max(cum, lo);
      if (ov > 0.0) acc += ov * s_rho[p];
      cum = c1;
      if (cum >= hi) break;
    }
    return acc / (hi - lo);
  }

  /** Tight closeness c^32 of two members of a stationary region, by five squarings (as terrain._tight). */
  function tight(c) {
    let t = c * c;
    t = t * t;
    t = t * t;
    t = t * t;
    return t * t;
  }

  /** Region amplitudes (blend of the members' coefficients with masses tight(c) c_m, into c_br / c_bi) and the soft
   * cap over stationary regions (region strength rho, counts kappa, cut at the (maxn + 1)-th strongest region); legs
   * evaluated lazily into fac; kept share u = share x cut weight, keep factor g = faint fade x output capacity
   * (OUT_CAP rays), the rest handed to the tight partners.  Writes the kept candidates to o_b / o_w in order of
   * decreasing output strength and returns their number (a line-by-line copy of terrain._cap_weights). */
  function capWeights(B, dE, ety, nr, kw, nc, maxn, z, d, N, s, za, zb, lam, r0, r1) {
    const { mi, mc, cidx, c_r, c_s, c_m, c_cr, c_ci, r_L, r_x, r_y, fac, c_br, c_bi, kap, sl, rho0 } = B;
    const { s_rho, s_kap, s_b, done, o_b, o_w, o_e, u, g, ek, Dn } = B;
    for (let b = 0; b < nc; b++) {
      const m = regionMembers(dE, ety, nr, c_r[b], kw, mi, mc);
      let P = 0.0, SL = 0.0, Mu = 0.0, AM = 0.0;
      for (let k = 0; k < m; k++) {
        const jc = cidx[mi[k]];
        if (jc >= 0) {
          P += mc[k] * c_s[jc];
          SL += mc[k] * c_s[jc] / r_L[c_r[jc]];
          const t = tight(mc[k]) * c_m[jc];
          Mu += t;
          AM += t * Math.hypot(c_cr[jc], c_ci[jc]);
        }
      }
      kap[b] = c_s[b] / P;
      sl[b] = SL;
      rho0[b] = (Mu > 0.0 ? AM / Mu : Math.hypot(c_cr[b], c_ci[b])) * SL;
      done[b] = 0;
    }
    const K = maxn, hiC = K + CUT_HI;
    let ns = 0;
    for (;;) {
      let b = -1, ba = -1.0;
      for (let k = 0; k < nc; k++) {
        if (!done[k] && rho0[k] > ba) { ba = rho0[k]; b = k; }
      }
      if (b < 0) break;
      let qh = 0.0, cum = 0.0;  // resolved quantile at count hiC (from below)
      for (let p = 0; p < ns; p++) {
        cum += s_kap[p];
        if (cum >= hiC) { qh = s_rho[p]; break; }
      }
      if (ba <= qh) break;
      done[b] = 1;
      const m = regionMembers(dE, ety, nr, c_r[b], kw, mi, mc);
      let Mu = 0.0, ar = 0.0, ai = 0.0;
      for (let k = 0; k < m; k++) {
        const jc = cidx[mi[k]];
        if (jc < 0) continue;
        if (fac[jc] < 0.0) {
          const qq = c_r[jc];
          fac[jc] = legFactor(z, d, N, s, za, zb, r_x[qq], r_y[qq], lam, r0, r1);
        }
        const t = tight(mc[k]) * c_m[jc];
        Mu += t;
        const tf = t * fac[jc];
        ar += c_cr[jc] * tf;
        ai += c_ci[jc] * tf;
      }
      if (Mu > 0.0) {
        ar = ar / Mu;
        ai = ai / Mu;
      } else {
        ar = c_cr[b] * fac[b];
        ai = c_ci[b] * fac[b];
      }
      c_br[b] = ar;
      c_bi[b] = ai;
      const rb = Math.hypot(ar, ai) * sl[b];
      let p = ns;
      ns++;
      while (p > 0 && s_rho[p - 1] < rb) {
        s_rho[p] = s_rho[p - 1];
        s_kap[p] = s_kap[p - 1];
        s_b[p] = s_b[p - 1];
        p--;
      }
      s_rho[p] = rb;
      s_kap[p] = kap[b];
      s_b[p] = b;
    }
    const lv = cutLevel(s_rho, s_kap, ns, K);
    // kept share u (cut weight), keep factor g (faint fade x output capacity)
    const D = d[N];
    const L0 = Math.sqrt(D * D + (zb - za) * (zb - za));
    for (let b = 0; b < nc; b++) { u[b] = 0.0; g[b] = 0.0; ek[b] = 0.0; Dn[b] = 0.0; }
    let ne = 0;
    for (let p = 0; p < ns; p++) {
      const hh = capH(s_rho[p], lv);
      if (hh <= 0.0) break;  // descending strengths: all further ones are cut too
      const b = s_b[p];
      u[b] = c_s[b] * hh;
      let e = u[b] * Math.hypot(c_br[b], c_bi[b]) / r_L[c_r[b]];
      const x = e * L0;
      if (x >= FAINT_HI) g[b] = 1.0;
      else if (x > FAINT_LO) {
        const t = (x - FAINT_LO) / (FAINT_HI - FAINT_LO);
        g[b] = t * t * (3.0 - 2.0 * t);
      }
      e = g[b] * e;
      ek[b] = e;
      if (e > 0.0) {
        let k = ne;
        ne++;
        while (k > 0 && o_e[k - 1] < e) {
          o_e[k] = o_e[k - 1];
          k--;
        }
        o_e[k] = e;
      }
    }
    if (ne > OUT_CAP) {
      const eCut = o_e[OUT_CAP];
      for (let b = 0; b < nc; b++) {
        if (g[b] > 0.0) g[b] = g[b] * capH(ek[b], eCut);  // ek > eCut for at most OUT_CAP members
      }
    }
    // hand-off of the parts not kept to the tight partners
    for (let b = 0; b < nc; b++) {
      if (u[b] > 0.0 && g[b] < 1.0) {
        const m = regionMembers(dE, ety, nr, c_r[b], kw, mi, mc);
        let Dh = 0.0;
        for (let k = 0; k < m; k++) {
          const jc = cidx[mi[k]];
          if (jc >= 0) Dh += tight(mc[k]) * (g[jc] * u[jc]);
        }
        Dn[b] = Math.max(Dh, u[b]);
      }
    }
    let na = 0;
    for (let b = 0; b < nc; b++) {
      const gu = g[b] * u[b];
      if (gu <= 0.0) continue;
      const m = regionMembers(dE, ety, nr, c_r[b], kw, mi, mc);
      let add = 0.0;
      for (let k = 0; k < m; k++) {
        const jc = cidx[mi[k]];
        if (jc >= 0 && Dn[jc] > 0.0) add += tight(mc[k]) * ((1.0 - g[jc]) * u[jc] / Dn[jc]);
      }
      const w = gu * (1.0 + add) / c_s[b];
      const e = c_s[b] * Math.hypot(c_br[b], c_bi[b]) / r_L[c_r[b]] * w;
      let k = na;
      na++;
      while (k > 0 && o_e[k - 1] < e) {
        o_e[k] = o_e[k - 1];
        o_b[k] = o_b[k - 1];
        o_w[k] = o_w[k - 1];
        k--;
      }
      o_e[k] = e;
      o_b[k] = b;
      o_w[k] = w;
    }
    return na;
  }

  /** Specular reflections A = (0, za) -> B = (D, zb) on the C1 smoothed surface (zs, ms); rays written in strength
   * order at out[off..], returns their number. */
  function smoothReflections(m, z, zs, ms, d, wv, pres, N, s, za, zb, win, maxn, wr, out, off) {
    const p = m.p, lam = m.lam, ae = m.ae, B = m.buf;
    const D = d[N];
    const kw = 2.0 * Math.PI / lam;
    const { Ux, Uz, f, r_x, r_y, r_L, r_d, r_s, r_t, wg, eg, mu, dE, ety, mi, mc, cidx, c_cr, c_ci, c_r, c_s, c_m } = B;
    const { fac, c_br, c_bi, o_b, o_w } = B;
    // mirror condition at the knots: f = (1, zs') . (u_A + u_B)
    for (let i = 0; i <= N; i++) {
      const ax = -d[i], az = za - zs[i];
      const la = Math.max(Math.sqrt(ax * ax + az * az), 1e-9);
      const bx = D - d[i], bz = zb - zs[i];
      const lb = Math.max(Math.sqrt(bx * bx + bz * bz), 1e-9);
      Ux[i] = ax / la + bx / lb;
      Uz[i] = az / la + bz / lb;
      f[i] = Ux[i] + ms[i] * Uz[i];
    }
    // roots per chord (quadratic model of f; f = 0 counts as positive), in profile order, with the local path-length
    // step between neighbouring roots (integral of the same model of f; the exact cubic for a pair in one chord)
    let nr = 0;
    let acc = 0.0;  // path-length step since the last root (since x = 0 before the first one)
    for (let i = 0; i < N; i++) {
      const c0 = f[i], c1 = f[i + 1];
      const a2 = (ms[i + 1] - ms[i]) * (Uz[i + 1] - Uz[i]);
      const b1 = c1 - c0 - a2;
      const h = d[i + 1] - d[i];
      let t1 = -1.0, t2 = -1.0, ty1 = 1, pair = 0.0;
      if ((c0 >= 0.0) !== (c1 >= 0.0)) {
        t1 = rootOdd(a2, b1, c0);
        ty1 = c0 >= 0.0 ? 1 : -1;  // f decreasing through the root: minimum of the path length
      } else if (a2 !== 0.0 && (a2 > 0.0) === (c0 >= 0.0)) {
        const disc = b1 * b1 - 4.0 * a2 * c0;
        if (disc > 0.0) {
          const sq = Math.sqrt(disc);
          const q = b1 >= 0.0 ? -0.5 * (b1 + sq) : -0.5 * (b1 - sq);
          let ta = q / a2, tb = c0 / q;
          if (ta > tb) { const tt = ta; ta = tb; tb = tt; }
          if (c1 === 0.0) {  // exact zero at the end knot: the roots are exactly 1 and c0 / a2 (q / a2 can be 1 + 1 ulp)
            ta = Math.min(c0 / a2, 1.0);
            tb = Math.max(c0 / a2, 1.0);
          }
          if (ta >= 0.0 && tb <= 1.0) {  // a root exactly at an end belongs to the pair (f = 0 counts as positive)
            t1 = ta;
            t2 = tb;
            ty1 = a2 > 0.0 ? 1 : -1;
            pair = h * (sq * disc) / (6.0 * a2 * Math.abs(a2));  // h a2 (tb - ta)^3 / 6
          }
        }
      }
      let ts = 0.0;
      for (let w_ = 0; w_ < 2; w_++) {
        const tt = w_ === 0 ? t1 : t2;
        if (tt < 0.0) continue;
        if (w_ === 0) acc -= h * chordInt(c0, b1, a2, ts, tt);
        else acc = pair;
        ts = tt;
        const x = d[i] + tt * (d[i + 1] - d[i]);
        const y = zs[i] + tt * (zs[i + 1] - zs[i]);
        const mm = ms[i] + tt * (ms[i + 1] - ms[i]);
        const ax = -x, az = za - y;
        const la = Math.max(Math.sqrt(ax * ax + az * az), 1e-9);
        const bx = D - x, bz = zb - y;
        const lb = Math.max(Math.sqrt(bx * bx + bz * bz), 1e-9);
        const nn = Math.sqrt(1.0 + mm * mm);
        const sp = 0.5 * ((-mm * ax + az) / la + (-mm * bx + bz) / lb) / nn;
        r_x[nr] = x;
        r_y[nr] = y;
        r_L[nr] = la + lb;
        r_d[nr] = acc;
        r_s[nr] = sp;
        r_t[nr] = w_ === 0 ? ty1 : -ty1;
        nr++;
        acc = 0.0;
      }
      acc -= h * chordInt(c0, b1, a2, ts, 1.0);
    }
    if (nr === 0) return 0;
    // extended sequence (mirrors about both ends); back-facing roots stay in it
    extendedSteps(r_d, r_t, nr, acc, dE, ety);
    // persistence weights x grazing fade (wg), and the external weight of each root's region (eg, clusterSum)
    for (let q = 0; q < nr; q++) {
      if (r_s[q] > 0.0) {
        const w_ = persistenceWeight(dE, ety, nr, q, kw), e_ = PWE.e, w2_ = PWE.w2;
        const gz = Math.min(r_s[q] / SIN_EPS, 1.0);
        wg[q] = w_ * gz;
        eg[q] = Math.min(e_, EG_BOUND * w_) * gz;
        mu[q] = w2_ * gz;
      } else {
        wg[q] = 0.0;
        eg[q] = 0.0;
        mu[q] = 0.0;
      }
    }
    // candidates: front-facing roots; the members of a stationary region (extrema within lambda / 2 of path length)
    // share the region's external weight R in proportion to their weights when their sum S exceeds it
    let nc = 0;
    const hw = (win + 1) * s;
    for (let q = 0; q < nr; q++) {
      const sp = r_s[q];
      cidx[q] = -1;
      if (wg[q] <= 0.0) continue;
      const S = clusterSum(dE, ety, wg, eg, nr, q, kw, mi, mc);
      const wf = wg[q] * Math.min(1.0, CS.r / S);
      const x = r_x[q];
      // water fraction and roughness: triangle kernel around x, presence-weighted samples
      let aw = 0.0, ar = 0.0, aq = 0.0;
      const iLo = seg(d, N, s, Math.max(x - hw, 0.0)) - 1, iHi = seg(d, N, s, Math.min(x + hw, D));
      for (let i = iLo; i <= iHi; i++) {
        const u = Math.abs(d[i] - x);
        if (u >= hw) continue;
        const wk = (1.0 - u / hw) * pres[i];
        aw += wk;
        const dz = z[i] - zs[i];
        ar += wk * (dz * dz);
        aq += wk * wv[i];
      }
      let wfr = 0.0, sig = 0.0;
      if (aw > 0.0) {  // (the window always holds a terminal sample of presence 1)
        wfr = aq / aw;
        sig = Math.sqrt(ar / aw);
      }
      let gr = 0.0, gi = 0.0;
      if (wfr < 1.0) {
        const tg = 2.0 * Math.PI * sig * sp / lam;
        const g = gammaTM(sp, p.eg_r, p.eg_i), ex = Math.exp(-2.0 * (tg * tg));
        gr += (1.0 - wfr) * g[0] * ex;
        gi += (1.0 - wfr) * g[1] * ex;
      }
      if (wfr > 0.0) {
        const tw = 2.0 * Math.PI * p.water_roughness_m * sp / lam;
        const g = gammaTM(sp, p.ew_r, p.ew_i), ex = Math.exp(-2.0 * (tw * tw));
        gr += wfr * g[0] * ex;
        gi += wfr * g[1] * ex;
      }
      // divergence factor of a reflection on the (effective) spherical earth
      const dd1 = x, dd2 = D - x;
      const tpsi = Math.max(sp / Math.sqrt(Math.max(1 - sp * sp, 1e-12)), 1e-9);
      const div = 1.0 / Math.sqrt(1.0 + 2.0 * dd1 * dd2 / (ae * (dd1 + dd2) * tpsi));
      c_cr[nc] = gr * div;
      c_ci[nc] = gi * div;
      c_m[nc] = mu[q];
      c_s[nc] = wf;
      c_r[nc] = q;
      cidx[q] = nc;
      fac[nc] = -1.0;
      nc++;
    }
    if (nc === 0) return 0;
    // soft cap over stationary regions (legs evaluated there, lazily)
    const na = capWeights(B, dE, ety, nr, kw, nc, maxn, z, d, N, s, za, zb, lam, win * s, (win + 1) * s);
    let n = 0;
    for (let k = 0; k < na; k++) {
      const w = o_w[k] * wr;
      if (w <= 0.0) continue;
      const b = o_b[k], q = c_r[b];
      const t = c_s[b] * w;
      out.L[off + n] = r_L[q];
      out.cr[off + n] = c_br[b] * t;
      out.ci[off + n] = c_bi[b] * t;
      out.et[off + n] = Math.atan2(r_y[q] - za, r_x[q]);
      out.er[off + n] = Math.atan2(r_y[q] - zb, D - r_x[q]);
      n++;
    }
    return n;
  }

  function bullington(z, d, N, za, zb, lam) {
    const D = d[N];
    let stim = -1e30;
    for (let i = 1; i < N; i++) stim = Math.max(stim, (z[i] - za) / d[i]);
    const str = (zb - za) / D;
    let luc, dbp, zbp, sT, sR;
    let los = stim < str, srim = -1e30;
    if (!los) {
      for (let i = 1; i < N; i++) srim = Math.max(srim, (z[i] - zb) / (D - d[i]));
      if (stim + srim <= 0.0) los = true;  // exact grazing: the limit of the line-of-sight case (no 0 / 0)
    }
    if (los) {
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
      dbp = (zb - za + srim * D) / (stim + srim);
      const e = Math.min(1e-3, 0.5 * D);  // keep the Bullington point off the terminals (D >= 1e-6 m)
      dbp = Math.min(Math.max(dbp, e), D - e);
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
    let fx = 0.0;  // the two branches of F(X) meet at X = 1.6 only to 7e-6 dB: smoothstep blend over [FX_LO, FX_HI]
    if (X > FX_LO) fx = 11.0 + 10.0 * Math.log10(X) - 17.6 * X;
    if (X < FX_HI) {
      const fl = -20.0 * Math.log10(X) - 5.6488 * Math.pow(X, 1.425);
      if (X > FX_LO) {
        const u = (X - FX_LO) / (FX_HI - FX_LO), v = u * u * (3.0 - 2.0 * u);
        fx = fl + v * (fx - fl);
      } else fx = fl;
    }
    let gsum = 0.0;
    for (const h of [hte, hre]) {
      const Y = 0.9575 * beta * Math.pow(fGhz ** 2 / aKm, 1.0 / 3.0) * h;
      const B = beta * Y;
      let g = 0.0;  // the two branches of G(Y) meet at B = 2 only to 0.0175 dB: smoothstep blend over [GB_LO, GB_HI]
      if (B > GB_LO) g = 17.6 * Math.sqrt(B - 1.1) - 5.0 * Math.log10(B - 1.1) - 8.0;
      if (B < GB_HI) {
        const gl = 20.0 * Math.log10(B + 0.1 * B ** 3);
        if (B > GB_LO) {
          const u = (B - GB_LO) / (GB_HI - GB_LO), v = u * u * (3.0 - 2.0 * u);
          g = gl + v * (g - gl);
        } else g = gl;
      }
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
    const { d, z, zraw, zs, ms, wv, pres, F } = m.buf;
    const s = p.step_m;
    const dx = rx - sx, dy = ry - sy;
    const D = Math.max(Math.sqrt(dx * dx + dy * dy), 1e-6);
    // samples at spacing s anchored at the midpoint (symmetric); the outermost pair fades in next to the terminals
    const half = 0.5 * D;
    let K = Math.max(Math.ceil(half / s) - 1, 0);
    let e = half - K * s;
    if (K > 0 && e < END_EPS) {
      K -= 1;
      e = half - K * s;
    }
    const N = 2 * K + 2;
    const wend = Math.sqrt(Math.min(Math.max(e - END_EPS, 0.0) / s, 1.0));  // 0 where the pair appears (e = END_EPS)
    const clearM = p.terminal_clearance_m;
    for (let i = 0; i <= N; i++) {
      const di = i === 0 ? 0.0 : i === N ? D : half + (i - K - 1) * s;
      d[i] = di;
      const t = di / D;
      const x = sx + dx * t, y = sy + dy * t;
      const col = x / mpp - 0.5, row = H - y / mpp - 0.5;
      let zt = bilinearTW(m.T, m.water, W, H, row, col);
      wv[i] = TW.wv;
      pres[i] = 1.0;
      if (i === 0) zraw[i] = groundAt(m, sx, sy);  // terminals stand on the ground (the DSM includes trees / roofs)
      else if (i === N) zraw[i] = groundAt(m, rx, ry);
      else {
        if (clearM > 0.0) {  // open site around each antenna, ramped over one step
          const gq = Math.min(Math.max((Math.min(di, D - di) - clearM) / s, 0.0), 1.0);
          if (gq < 1.0) {
            const zgr = bilinear(m.G, W, H, row, col);
            zt = zgr + gq * (zt - zgr);
          }
        }
        zraw[i] = zt;
      }
    }
    // end fade: the outermost samples start on the line terminal ground -> next sample
    if (K === 0) {
      zraw[1] = wend * zraw[1] + (1.0 - wend) * (zraw[0] + (zraw[2] - zraw[0]) * d[1] / D);
      pres[1] = wend;
    } else {
      zraw[1] = wend * zraw[1] + (1.0 - wend) * (zraw[0] + (zraw[2] - zraw[0]) * d[1] / d[2]);
      zraw[N - 1] = wend * zraw[N - 1] + (1.0 - wend) * (
        zraw[N] + (zraw[N - 2] - zraw[N]) * (D - d[N - 1]) / (D - d[N - 2]));
      pres[1] = wend;
      pres[N - 1] = wend;
    }
    for (let i = 0; i <= N; i++) z[i] = zraw[i] + d[i] * (D - d[i]) / (2.0 * ae);
    const za = z[0] + hTx, zb = z[N] + hRx;
    const out = m.buf.out;  // reused: callers consume it before the next call
    out.L.fill(0); out.cr.fill(0); out.ci.fill(0); out.et.fill(0); out.er.fill(0);
    out.n = 0; out.los = false; out.diff_db = 0.0;
    const [im, vm] = maxV(z, d, 0, N, za, zb, lam);
    let ps = 0.0, pw = 0.0;
    for (let i = 0; i <= N; i++) {
      ps += pres[i];
      pw += pres[i] * wv[i];
    }
    const db = deltaBullington(m, zraw, z, d, N, hTx, hRx, pw / ps);
    const jdb = db[0];
    const geoLos = im < 0 || vm < 0.0;
    // weight of the ray model (direct + reflections) against the diffraction model
    const wr = geoLos ? wray(jdb) : 0.0;
    if (geoLos) {
      out.los = true;
      out.diff_db = jdb * (1.0 - wr);
      out.L[0] = Math.sqrt(D * D + (zb - za) * (zb - za));
      out.cr[0] = Math.pow(10, -jdb * (1.0 - wr) / 20.0);
      out.et[0] = Math.atan2(zb - za, D);
      out.er[0] = Math.atan2(za - zb, D);
      out.n = 1;
      if (wr > 0.0 && p.max_reflections > 0) {
        // continuous box filter (half-width a) of the piecewise-linear profile: heights and slopes
        smoothProfile(z, d, N, Math.min((m.smooth_n + 0.5) * s, half), F, zs, ms);
        const win = Math.max(Math.floor(m.smooth_n / 2), 1);
        out.n = 1 + smoothReflections(m, z, zs, ms, d, wv, pres, N, s, za, zb, win,
                                      Math.min(p.max_reflections, KMAX), wr, out, 1);
      }
    } else {
      out.los = false;
      out.diff_db = jdb;
      const [, dbp, zbp, sT, sR] = db;
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

  /** Rays that matter for the label: the direct / diffraction ray plus the reflections with |c| >= 0.1 (n also counts
   * the faint ones a reflection fades in / out with). */
  function mainRays(r) {
    let k = r.n > 0 ? 1 : 0;
    for (let q = 1; q < r.n; q++) if (Math.hypot(r.cr[q], r.ci[q]) >= 0.1) k++;
    return k;
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
      los: r.los, diff_db: r.diff_db, n: r.n, n_main: mainRays(r),
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
      info[a + ">" + b] = { los: r.los, diff_db: r.diff_db, n: r.n, n_main: r.n_main };
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
        info["R>" + n] = { los: a.los, diff_db: a.diff_db, n: a.n, n_main: a.n_main };
        info[n + ">R"] = { los: b.los, diff_db: b.diff_db, n: b.n, n_main: b.n_main };
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

  const api = { cableDb, tableLevel, costOf, rateScale, edgeWeight, nodeTable, relayLinks, finalTable, plan, makeModel, rays, channelGain, eesmDb, budgetDb, linkEsnr, groundAt, bullington, decide, dijkstra, relayGrid,
                treeFromPaths, relayScore, BIG, rankTrees, enumerateTrees, candidateGrid, localGrid, refinePick, pickCandidates, MS_PATHS, NODE_NAMES, RELAY };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else root.AutoRelayEngine = api;
})(typeof self !== "undefined" ? self : this);
