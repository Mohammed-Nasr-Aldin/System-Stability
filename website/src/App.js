import { useState, useMemo, useEffect, useRef, useId, memo } from "react";

/* =====================================================================
   CONTROL SYSTEMS SUITE  -  Routh / Root Locus / Bode
   The numerical algorithms are a port of the MATLAB version.
   ===================================================================== */

const COL = { blue: "#2563eb", purple: "#7c3aed", orange: "#ea8a0c", green: "#16a34a", red: "#dc2626", gray: "#94a3b8", ink: "#0f172a", magenta: "#c026d3" };
const BRANCH = ["#2563eb", "#dc2626", "#16a34a", "#9333ea", "#ea580c", "#0891b2", "#be185d", "#4d7c0f", "#7c2d12", "#1e40af"];

/* ---------------------------------------------------------------------
   1. NUMERIC UTILITIES  (complex numbers are [re, im])
   --------------------------------------------------------------------- */
const cadd = (a, b) => [a[0] + b[0], a[1] + b[1]];
const csub = (a, b) => [a[0] - b[0], a[1] - b[1]];
const cmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const cdiv = (a, b) => { const d = b[0] * b[0] + b[1] * b[1]; return [(a[0] * b[0] + a[1] * b[1]) / d, (a[1] * b[0] - a[0] * b[1]) / d]; };
const cabs = (a) => Math.hypot(a[0], a[1]);

const fmt = (v, d = 5) => {
  if (!Number.isFinite(v)) return String(v);
  if (v === 0) return "0";
  const a = Math.abs(v);
  if (a >= 1e6 || a < 1e-3) return v.toExponential(d - 1);
  return String(+v.toPrecision(d));
};
const fmtC = (z, d = 4) => {
  const [re, im] = z;
  if (Math.abs(im) < 1e-9) return fmt(re, d);
  return `${fmt(re, d)} ${im < 0 ? "−" : "+"} ${fmt(Math.abs(im), d)}j`;
};

const polyvalR = (p, x) => p.reduce((acc, c) => acc * x + c, 0);
function polyvalC(p, z) {
  let re = 0, im = 0;
  for (const c of p) { const nr = re * z[0] - im * z[1] + c; const ni = re * z[1] + im * z[0]; re = nr; im = ni; }
  return [re, im];
}
const polyder = (p) => { const n = p.length - 1; return n < 1 ? [0] : p.slice(0, -1).map((c, i) => c * (n - i)); };
const polyAdd = (a, b) => {
  const L = Math.max(a.length, b.length);
  const A = [...Array(L - a.length).fill(0), ...a], B = [...Array(L - b.length).fill(0), ...b];
  return A.map((v, i) => v + B[i]);
};
const polyScale = (a, k) => a.map((v) => v * k);
const polySub = (a, b) => polyAdd(a, polyScale(b, -1));
const polyConv = (a, b) => { const r = Array(a.length + b.length - 1).fill(0); a.forEach((x, i) => b.forEach((y, j) => { r[i + j] += x * y; })); return r; };
const cconv = (A, B) => { const r = Array.from({ length: A.length + B.length - 1 }, () => [0, 0]); A.forEach((x, i) => B.forEach((y, j) => { r[i + j] = cadd(r[i + j], cmul(x, y)); })); return r; };
function trimLead(p, tol = 1e-12) {
  const i = p.findIndex((c) => Math.abs(c) > tol);
  if (i < 0) throw new Error("Polynomial cannot be all zeros.");
  return p.slice(i);
}

/* Aberth-Ehrlich root finder (works for any real polynomial, highest power first) */
function polyRoots(pIn) {
  const p = pIn.slice();
  while (p.length && p[0] === 0) p.shift();
  if (!p.length) throw new Error("Polynomial cannot be all zeros.");
  let nz = 0;
  while (p.length > 1 && p[p.length - 1] === 0) { p.pop(); nz++; }
  const n = p.length - 1;
  const out = [];
  if (n >= 1) {
    const q = p.map((c) => c / p[0]);
    const dq = polyder(q);
    const r0 = Math.pow(Math.abs(q[n]), 1 / n) || 1;
    const z = Array.from({ length: n }, (_, k) => { const a = (2 * Math.PI * k) / n + 0.4; return [r0 * Math.cos(a), r0 * Math.sin(a)]; });
    for (let it = 0; it < 1000; it++) {
      let worst = 0;
      for (let k = 0; k < n; k++) {
        const pz = polyvalC(q, z[k]);
        if (cabs(pz) === 0) continue;
        const dz = polyvalC(dq, z[k]);
        const ratio = cabs(dz) === 0 ? [1e-3, 1e-3] : cdiv(pz, dz);
        let s = [0, 0];
        for (let j = 0; j < n; j++) if (j !== k) { const d = csub(z[k], z[j]); if (cabs(d) > 0) s = cadd(s, cdiv([1, 0], d)); }
        const den = csub([1, 0], cmul(ratio, s));
        const w = cabs(den) === 0 ? ratio : cdiv(ratio, den);
        z[k] = csub(z[k], w);
        worst = Math.max(worst, cabs(w) / (1 + cabs(z[k])));
      }
      if (worst < 1e-14) break;
    }
    out.push(...z);
  }
  for (let i = 0; i < nz; i++) out.push([0, 0]);
  return out;
}
const rootsClean = (p) => polyRoots(p).map(([r, i]) => [r, Math.abs(i) < 1e-9 ? 0 : i]).sort((a, b) => b[0] - a[0] || b[1] - a[1]);

const countChanges = (sg) => { let c = 0; for (let i = 0; i < sg.length - 1; i++) if (sg[i] * sg[i + 1] < 0) c++; return c; };
const rangeStr = (lo, hi) => (!Number.isFinite(lo) && !Number.isFinite(hi) ? "all K" : !Number.isFinite(lo) ? `K < ${fmt(hi, 6)}` : !Number.isFinite(hi) ? `K > ${fmt(lo, 6)}` : `${fmt(lo, 6)} < K < ${fmt(hi, 6)}`);
const slopeStr = (v) => { v = Math.round(v); return v === 0 ? "0 dB/dec" : `${v > 0 ? "+" : ""}${v} dB/dec`; };
const statusOfPoles = (r) => (r.every((z) => z[0] < -1e-7) ? "stable" : r.some((z) => z[0] > 1e-7) ? "unstable" : "marginal");
const STATUS_TXT = { stable: "STABLE", marginal: "MARGINALLY STABLE", unstable: "UNSTABLE" };

/* ---------------------------------------------------------------------
   2. SAFE EXPRESSION PARSER   (numbers, pi, e, K, + - * / ^, sqrt, ...)
   --------------------------------------------------------------------- */
const FUNCS = { sqrt: Math.sqrt, abs: Math.abs, exp: Math.exp, sin: Math.sin, cos: Math.cos, tan: Math.tan, log: Math.log, ln: Math.log, log10: Math.log10 };
function parseExpr(src, allowK = false) {
  const s = String(src).trim();
  if (!s) throw new Error("Empty value");
  const toks = [];
  for (let i = 0; i < s.length; ) {
    const ch = s[i];
    if (/\s/.test(ch)) { i++; continue; }
    let m = s.slice(i).match(/^(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?/);
    if (m) { toks.push({ t: "num", v: parseFloat(m[0]) }); i += m[0].length; continue; }
    m = s.slice(i).match(/^[A-Za-z_][A-Za-z_0-9]*/);
    if (m) { toks.push({ t: "id", v: m[0] }); i += m[0].length; continue; }
    if ("+-*/^()".includes(ch)) { toks.push({ t: ch }); i++; continue; }
    throw new Error(`Unexpected character '${ch}'`);
  }
  let pos = 0;
  const peek = () => toks[pos], eat = () => toks[pos++];
  function expr() {
    let l = term();
    while (peek() && (peek().t === "+" || peek().t === "-")) {
      const op = eat().t, r = term(), a = l;
      l = op === "+" ? (v) => a(v) + r(v) : (v) => a(v) - r(v);
    }
    return l;
  }
  function term() {
    let l = unary();
    for (;;) {
      const p = peek();
      if (!p) break;
      if (p.t === "*" || p.t === "/") {
        eat(); const r = unary(), a = l;
        l = p.t === "*" ? (v) => a(v) * r(v) : (v) => a(v) / r(v);
      } else if (p.t === "id" || p.t === "(") {          // implicit multiplication: 2K, 2(K+1)
        const r = power(), a = l; l = (v) => a(v) * r(v);
      } else break;
    }
    return l;
  }
  function unary() {
    const p = peek();
    if (p && p.t === "-") { eat(); const u = unary(); return (v) => -u(v); }
    if (p && p.t === "+") { eat(); return unary(); }
    return power();
  }
  function power() {
    const b = atom();
    if (peek() && peek().t === "^") { eat(); const e = unary(); return (v) => Math.pow(b(v), e(v)); }
    return b;
  }
  function atom() {
    const t = eat();
    if (!t) throw new Error("Unexpected end of expression");
    if (t.t === "num") return () => t.v;
    if (t.t === "(") { const e = expr(); if (!peek() || peek().t !== ")") throw new Error("Missing ')'"); eat(); return e; }
    if (t.t === "id") {
      const low = t.v.toLowerCase();
      if (FUNCS[low] && peek() && peek().t === "(") { eat(); const e = expr(); if (!peek() || peek().t !== ")") throw new Error("Missing ')'"); eat(); const f = FUNCS[low]; return (v) => f(e(v)); }
      if (low === "pi") return () => Math.PI;
      if (low === "e") return () => Math.E;
      if (low === "k") { if (!allowK) throw new Error("K is only allowed in K mode"); return (v) => v; }
      throw new Error(`Unknown symbol '${t.v}'`);
    }
    throw new Error(`Unexpected '${t.t}'`);
  }
  const f = expr();
  if (pos < toks.length) throw new Error(`Unexpected '${toks[pos].t === "num" ? toks[pos].v : toks[pos].t}'`);
  const test = f(1);
  if (!Number.isFinite(test)) throw new Error("Value is not a finite number");
  return f;
}
const parseNum = (s) => parseExpr(s, false)(0);

/* ---------------------------------------------------------------------
   3. ROUTH ENGINE  (zero first element -> epsilon, zero row -> dA/dS)
   --------------------------------------------------------------------- */
function routhNumeric(S) {
  const n = S.length - 1;
  const cols = Math.ceil((n + 1) / 2) + 1;
  const scale = Math.max(...S.map(Math.abs));
  const epsVal = 1e-6 * scale;
  let special = false;
  const info = { zeroRows: [], epsRows: [], aux: [], epsVal };
  const R = Array.from({ length: n + 1 }, () => new Array(cols).fill(0));
  S.forEach((c, i) => { if (i % 2 === 0) R[0][i / 2] = c; else R[1][(i - 1) / 2] = c; });
  for (let i = 1; i <= n; i++) {
    if (i >= 2) for (let j = 0; j < cols - 1; j++) R[i][j] = (R[i - 1][0] * R[i - 2][j + 1] - R[i - 2][0] * R[i - 1][j + 1]) / R[i - 1][0];
    let mx = 0;
    for (let r = Math.max(i - 2, 0); r <= i - 1; r++) for (const v of R[r]) mx = Math.max(mx, Math.abs(v));
    const tolz = 1e-9 * mx;
    if (R[i].every((v) => Math.abs(v) <= tolz)) {            // zero row -> auxiliary polynomial
      special = true;
      const d = n - i + 1;
      const aux = new Array(d + 1).fill(0);
      for (let j = 0; j < cols; j++) if (2 * j <= d) aux[2 * j] = R[i - 1][j];
      info.zeroRows.push(i); info.aux.push(aux);
      for (let j = 0; j < cols; j++) R[i][j] = (d - 2 * j) * R[i - 1][j];
    }
    if (Math.abs(R[i][0]) <= tolz && i < n) { special = true; R[i][0] = epsVal; info.epsRows.push(i); }   // zero first element
  }
  return { R, special, info, cols };
}
function analyzePoly(Sin) {
  const S = trimLead(Sin);
  const n = S.length - 1;
  if (n < 1) throw new Error("Polynomial must be of order 1 or higher.");
  const { R, special, info, cols } = routhNumeric(S);
  const sg = R.map((r) => Math.sign(r[0]));
  const numRHP = countChanges(sg);
  let numImag = 0;
  for (const i of info.zeroRows) numImag += n - i + 1 - 2 * countChanges(sg.slice(i - 1));
  numImag = Math.max(numImag, 0);
  return { S, n, R, cols, special, info, numRHP, numImag, numLHP: n - numRHP - numImag };
}
function hasRepeatedImag(roots) {
  const ir = roots.filter((r) => Math.abs(r[0]) <= 1e-6);
  for (let a = 0; a < ir.length - 1; a++) for (let b = a + 1; b < ir.length; b++) if (cabs(csub(ir[a], ir[b])) < 1e-3 * Math.max(1, cabs(ir[a]))) return true;
  return false;
}
function routhVerdict(A, roots) {
  const rep = roots ? hasRepeatedImag(roots) : false;
  if (A.numRHP > 0) return { level: "unstable", text: `UNSTABLE (${A.numRHP} RHP pole${A.numRHP > 1 ? "s" : ""})` };
  if (A.numImag > 0 && rep) return { level: "unstable", text: "UNSTABLE (repeated poles on jω axis)" };
  if (A.numImag > 0) return { level: "marginal", text: "MARGINALLY STABLE" };
  return { level: "stable", text: "STABLE" };
}

/* jω-axis crossings of  D(s) + K N(s) = 0  (K real). Used by Root Locus and by K-mode Routh. */
function crossingsJw(D, N, positiveOnly) {
  const nD = D.length - 1, nN = N.length - 1;
  const cj = (c, k) => { const r = ((k % 4) + 4) % 4; return r === 0 ? [c, 0] : r === 1 ? [0, c] : r === 2 ? [-c, 0] : [0, -c]; };
  const Dj = D.map((c, i) => cj(c, nD - i));
  const Nj = N.map((c, i) => { const z = cj(c, nN - i); return [z[0], -z[1]]; });
  const Pi = cconv(Dj, Nj).map((z) => z[1]);
  if (!Pi.some((v) => Math.abs(v) > 1e-12)) return [];
  const wr = polyRoots(trimLead(Pi));
  const ws = [...new Set(wr.filter((r) => Math.abs(r[1]) < 1e-6 && r[0] > -1e-9).map((r) => Math.round(Math.max(r[0], 0) * 1e8) / 1e8))];
  const out = [];
  for (const w of ws) {
    const Nw = polyvalC(N, [0, w]), Dw = polyvalC(D, [0, w]);
    if (cabs(Nw) < 1e-9) continue;
    const Kc = cdiv([-Dw[0], -Dw[1]], Nw);
    if (Math.abs(Kc[1]) > 1e-6 * Math.max(1, cabs(Kc))) continue;
    if (positiveOnly && Kc[0] <= 1e-9) continue;
    out.push({ K: Kc[0], w });
  }
  const seen = new Set();
  return out.filter((o) => { const k = Math.round(o.K * 1e8); if (seen.has(k)) return false; seen.add(k); return true; }).sort((a, b) => a.K - b.K);
}

/* K-mode: coefficients are functions of K */
function classifyAt(Sfn, K) {
  try {
    const c = Sfn(K);
    if (c.some((v) => !Number.isFinite(v)) || c.every((v) => v === 0)) return { bad: true, level: "unstable", text: "undefined", key: "bad" };
    const S = trimLead(c);
    if (S.length < 2) return { bad: true, level: "unstable", text: "constant polynomial", key: "bad" };
    const A = analyzePoly(S);
    const v = routhVerdict(A, rootsClean(S));
    return { ...v, A, key: `${A.numRHP}|${A.numImag}` };
  } catch (e) { return { bad: true, level: "unstable", text: "undefined", key: "bad" }; }
}
function kGrid(lo, hi) {
  const pts = new Set();
  const N = 1500;
  for (let i = 0; i <= N; i++) pts.add(lo + ((hi - lo) * i) / N);
  const span = Math.max(Math.abs(lo), Math.abs(hi), 1e-6);
  for (let e = -6; e <= Math.log10(span); e += 0.05) { const v = Math.pow(10, e); if (v >= lo && v <= hi) pts.add(v); if (-v >= lo && -v <= hi) pts.add(-v); }
  if (lo <= 0 && hi >= 0) pts.add(0);
  return [...pts].sort((a, b) => a - b);
}
function analyzeK(Sfn, Kfrom, Kto) {
  const keyAt = (K) => classifyAt(Sfn, K).key;
  const pts = kGrid(Kfrom, Kto);
  const keys = pts.map(keyAt);
  const found = [];
  for (let i = 0; i < pts.length - 1; i++) {
    if (keys[i] !== keys[i + 1]) {
      let a = pts[i], b = pts[i + 1];
      for (let it = 0; it < 70; it++) { const mid = (a + b) / 2; if (keyAt(mid) === keys[i]) a = mid; else b = mid; }
      found.push((a + b) / 2);
    }
  }
  // exact critical values when every coefficient is affine in K:  a + K b
  let exact = [], affine = false;
  try {
    const a = Sfn(0), b = Sfn(1).map((v, i) => v - a[i]);
    const c2 = Sfn(2), c3 = Sfn(-3);
    affine = a.every(Number.isFinite) && b.every(Number.isFinite) &&
      a.every((_, i) => Math.abs(c2[i] - (a[i] + 2 * b[i])) < 1e-9 * (1 + Math.abs(a[i]) + Math.abs(b[i])) && Math.abs(c3[i] - (a[i] - 3 * b[i])) < 1e-9 * (1 + Math.abs(a[i]) + Math.abs(b[i])));
    if (affine && b.some((v) => Math.abs(v) > 1e-12)) {
      exact = crossingsJw(a, b, false).map((o) => o.K);
      if (Math.abs(b[0]) > 1e-12) exact.push(-a[0] / b[0]);
    }
  } catch (e) { affine = false; }
  exact = exact.filter((k) => k > Kfrom && k < Kto);
  const crits = [...exact];
  for (const f of found) if (!exact.some((e) => Math.abs(e - f) < 1e-6 * (1 + Math.abs(f)))) crits.push(f);
  const uniq = [...new Set(crits.map((c) => +c.toPrecision(10)))].sort((a, b) => a - b);
  const edges = [Kfrom, ...uniq, Kto];
  const intervals = [];
  for (let i = 0; i < edges.length - 1; i++) {
    const lo = edges[i], hi = edges[i + 1];
    if (!(hi > lo)) continue;
    const c = classifyAt(Sfn, (lo + hi) / 2);
    intervals.push({ lo, hi, level: c.level, text: c.text, bad: c.bad });
  }
  const critInfo = uniq.map((kc) => {
    const c = classifyAt(Sfn, kc);
    let ws = [];
    try { ws = [...new Set(rootsClean(trimLead(Sfn(kc))).filter((r) => Math.abs(r[0]) <= 1e-6 && r[1] >= -1e-9).map((r) => +r[1].toFixed(6)))]; } catch (e) { /* ignore */ }
    return { K: kc, level: c.level, text: c.text, ws };
  });
  const firstStable = intervals.find((x) => x.level === "stable");
  const kDefault = firstStable ? (firstStable.lo + firstStable.hi) / 2 : (Kfrom + Kto) / 2;
  return { intervals, critInfo, affine, Kfrom, Kto, kDefault };
}

/* ---------------------------------------------------------------------
   4. ROOT LOCUS ENGINE
   --------------------------------------------------------------------- */
function trackLocus(D, padN, Kvec) {
  const n = D.length - 1;
  const get = (K) => { const r = polyRoots(polyAdd(D, polyScale(padN, K))); while (r.length < n) r.push([1e6, 0]); return r; };
  const br = Array.from({ length: n }, () => []);
  let prev = get(Kvec[0]);
  prev.forEach((z, b) => br[b].push(z));
  for (let i = 1; i < Kvec.length; i++) {
    const r = get(Kvec[i]);
    const dist = prev.map((a) => r.map((b) => cabs(csub(a, b))));
    const ord = new Array(n).fill(0);
    for (let t = 0; t < n; t++) {
      let best = Infinity, bi = 0, bj = 0;
      for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) if (dist[a][b] < best) { best = dist[a][b]; bi = a; bj = b; }
      ord[bi] = bj;
      for (let b = 0; b < n; b++) dist[bi][b] = Infinity;
      for (let a = 0; a < n; a++) dist[a][bj] = Infinity;
    }
    prev = ord.map((j) => r[j]);
    prev.forEach((z, b) => br[b].push(z));
  }
  return br;
}
function computeLocus(Nin, Din, K0) {
  const N = trimLead(Nin), D = trimLead(Din);
  const m = N.length - 1, n = D.length - 1;
  const padN = [...Array(n - m).fill(0), ...N];
  const tol = 1e-6;
  const z = m > 0 ? rootsClean(N) : [], p = rootsClean(D);

  const na = n - m;
  let angA = [], sigA = null;
  if (na > 0) {
    angA = Array.from({ length: na }, (_, k) => ((2 * k + 1) * 180) / na);
    sigA = (p.reduce((s, r) => s + r[0], 0) - z.reduce((s, r) => s + r[0], 0)) / na;
  }
  const realPts = [...p.filter((r) => Math.abs(r[1]) < tol).map((r) => r[0]), ...z.filter((r) => Math.abs(r[1]) < tol).map((r) => r[0])].sort((a, b) => b - a);
  const segments = [];
  for (let k = 0; k < realPts.length; k += 2) segments.push(k + 1 < realPts.length ? `[${fmt(realPts[k + 1])} , ${fmt(realPts[k])}]` : `(−∞ , ${fmt(realPts[k])}]`);
  const onLocus = (x) => realPts.filter((v) => v > x + 1e-9).length % 2 === 1;

  const bp = [], bpK = [];
  const B = polySub(polyConv(polyder(D), N), polyConv(D, polyder(N)));
  if (B.some((v) => Math.abs(v) > 1e-12)) {
    const Bt = trimLead(B);
    if (Bt.length > 1) {
      for (const r of polyRoots(Bt)) {
        if (Math.abs(r[1]) >= tol) continue;
        const c = r[0];
        if (Math.abs(polyvalR(N, c)) < 1e-12) continue;
        const Kb = -polyvalR(D, c) / polyvalR(N, c);
        if (Kb > 1e-9 && onLocus(c)) { bp.push(c); bpK.push(Kb); }
      }
    }
  }
  const wrap = (a) => ((((a + 180) % 360) + 360) % 360) - 180;
  const ang = (v) => (Math.atan2(v[1], v[0]) * 180) / Math.PI;
  const departures = p.filter((r) => r[1] > tol).map((pk) => {
    const others = p.slice(); others.splice(others.findIndex((q) => cabs(csub(q, pk)) < 1e-9), 1);
    const a = wrap(180 + z.reduce((s, zz) => s + ang(csub(pk, zz)), 0) - others.reduce((s, q) => s + ang(csub(pk, q)), 0));
    return { pole: pk, ang: a };
  });
  const arrivals = z.filter((r) => r[1] > tol).map((zk) => {
    const oz = z.slice(); oz.splice(oz.findIndex((q) => cabs(csub(q, zk)) < 1e-9), 1);
    const a = wrap(180 - oz.reduce((s, q) => s + ang(csub(zk, q)), 0) + p.reduce((s, q) => s + ang(csub(zk, q)), 0));
    return { zero: zk, ang: a };
  });

  const cross = crossingsJw(D, N, true);
  const Kcrit = cross.map((c) => c.K), wcr = cross.map((c) => c.w);

  const edges = [0, ...Kcrit, Infinity];
  const intervals = [], stableRanges = [];
  for (let k = 0; k < edges.length - 1; k++) {
    const lo = edges[k], hi = edges[k + 1];
    const pt = !Number.isFinite(hi) ? Math.max(2 * lo, 1) : (lo + hi) / 2;
    const rr = polyRoots(polyAdd(D, polyScale(padN, pt)));
    const nR = rr.filter((r) => r[0] > 1e-7).length;
    const stable = nR === 0 && rr.every((r) => r[0] < -1e-7);
    intervals.push({ lo, hi, stable, nR });
    if (stable) stableRanges.push(rangeStr(lo, hi));
  }
  const condTxt = stableRanges.length ? stableRanges.join("  ,  ") : "unstable for all K > 0";

  const Kmax = 1e4 * Math.max(1, ...Kcrit, Math.abs(K0), ...bpK);
  const Kvec = [...new Set([0, ...Array.from({ length: 1500 }, (_, i) => Math.pow(10, -6 + ((Math.log10(Kmax) + 6) * i) / 1499)), ...Kcrit, ...bpK])].sort((a, b) => a - b);
  const branches = trackLocus(D, padN, Kvec);

  const xs = [0, ...p.map((a) => a[0]), ...z.map((a) => a[0]), ...bp, ...(sigA !== null ? [sigA] : [])];
  const ys = [1, ...p.map((a) => Math.abs(a[1])), ...z.map((a) => Math.abs(a[1])), ...wcr];
  const xc = (Math.min(...xs) + Math.max(...xs)) / 2, hx = (Math.max(...xs) - Math.min(...xs)) / 2;
  const half = 1.6 * Math.max(Math.max(...ys), hx / 1.49, 1);
  return {
    N, D, padN, m, n, K0, z, p, na, angA, sigA, segments, bp, bpK, departures, arrivals, Kcrit, wcr, intervals, condTxt,
    branches, view: { x0: xc - half, x1: xc + half, y0: -half, y1: half }, Kslider: 2 * Math.max(1, ...Kcrit, ...bpK, K0),
  };
}

/* ---------------------------------------------------------------------
   5. BODE ENGINE
   --------------------------------------------------------------------- */
const makeGrid = (lo, hi) => { const N = Math.max(2000, Math.ceil(300 * Math.log10(hi / lo))); return Array.from({ length: N }, (_, i) => Math.pow(10, Math.log10(lo) + ((Math.log10(hi) - Math.log10(lo)) * i) / (N - 1))); };
function evalTF(N, D, K0, w) {
  const mag = new Array(w.length), ph = new Array(w.length);
  for (let i = 0; i < w.length; i++) {
    const H = cdiv(polyvalC(N, [0, w[i]]), polyvalC(D, [0, w[i]]));
    mag[i] = 20 * Math.log10(Math.abs(K0) * cabs(H));
    ph[i] = Math.atan2(K0 < 0 ? -H[1] : H[1], K0 < 0 ? -H[0] : H[0]);
  }
  return { mag, ph };
}
function unwrap(a) {
  const out = [a[0]]; let off = 0;
  for (let i = 1; i < a.length; i++) {
    const d = a[i] - a[i - 1];
    if (d > Math.PI) off -= 2 * Math.PI * Math.ceil((d - Math.PI) / (2 * Math.PI));
    else if (d < -Math.PI) off += 2 * Math.PI * Math.ceil((-d - Math.PI) / (2 * Math.PI));
    out.push(a[i] + off);
  }
  return out;
}
function crossings(w, y, extra) {
  const wc = [], ex = [];
  for (let i = 0; i < y.length - 1; i++) if (y[i] * y[i + 1] < 0) {
    const t = y[i] / (y[i] - y[i + 1]);
    wc.push(Math.pow(10, Math.log10(w[i]) + t * (Math.log10(w[i + 1]) - Math.log10(w[i]))));
    ex.push(extra[i] + t * (extra[i + 1] - extra[i]));
  }
  return { wc, ex };
}
const trailingZeros = (v) => { let k = 0; while (k < v.length - 1 && Math.abs(v[v.length - 1 - k]) < 1e-12) k++; return k; };
function asymptoteData(N, D, K0) {
  const zO = trailingZeros(N), pO = trailingZeros(D);
  const Nn = N.slice(0, N.length - zO), Dn = D.slice(0, D.length - pO);
  const zr = Nn.length > 1 ? polyRoots(Nn).map(cabs) : [], pr = Dn.length > 1 ? polyRoots(Dn).map(cabs) : [];
  const all = [...zr.map((c) => ({ c, d: 20 })), ...pr.map((c) => ({ c, d: -20 }))].sort((a, b) => a.c - b.c);
  const cw = [], dchg = [];
  for (const it of all) {
    if (cw.length && Math.abs(it.c - cw[cw.length - 1]) <= 1e-6 * cw[cw.length - 1]) dchg[dchg.length - 1] += it.d;
    else { cw.push(it.c); dchg.push(it.d); }
  }
  const slope0 = 20 * (zO - pO);
  const segSlope = [slope0]; let acc = slope0;
  for (const d of dchg) { acc += d; segSlope.push(acc); }
  const c0 = Math.abs((K0 * Nn[Nn.length - 1]) / Dn[Dn.length - 1]);
  return { cw, segSlope, c0, slope0 };
}
const arrMax = (a) => a.reduce((s, v) => Math.max(s, v), -Infinity);
const arrMin = (a) => a.reduce((s, v) => Math.min(s, v), Infinity);
function computeBode(Nin, Din, K0) {
  const N = trimLead(Nin), D = trimLead(Din);
  const m = N.length - 1, n = D.length - 1;
  const padN = [...Array(n - m).fill(0), ...N];
  const z = m > 0 ? rootsClean(N) : [], p = rootsClean(D);
  const { cw, segSlope, c0, slope0 } = asymptoteData(N, D, K0);

  let wlo, whi;
  if (!cw.length) { wlo = 0.1; whi = 100; } else { wlo = Math.pow(10, Math.floor(Math.log10(Math.min(...cw))) - 1); whi = Math.pow(10, Math.ceil(Math.log10(Math.max(...cw))) + 1); }
  for (let it = 0; it < 12; it++) {
    const w = makeGrid(wlo, whi);
    const { mag } = evalTF(N, D, K0, w);
    let changed = false;
    if (n > m && mag[mag.length - 1] > -40 && whi < 1e9) { whi *= 10; changed = true; }
    if (slope0 < 0 && mag[0] < 20 && wlo > 1e-9) { wlo /= 10; changed = true; }
    if (!changed) break;
  }
  const w = makeGrid(wlo, whi);
  const { mag, ph: phr } = evalTF(N, D, K0, w);
  const ph = unwrap(phr).map((v) => (v * 180) / Math.PI);

  const gx = crossings(w, mag, ph);
  const wgc = gx.wc, phgc = gx.ex;
  const PM = phgc.map((v) => ((((v % 360) + 360) % 360) - 180));
  const refPh = phgc.map((v, i) => v - PM[i]);
  let px = [];
  for (let k = -3; k <= 3; k++) {
    const L = -180 + 360 * k;
    const c = crossings(w, ph.map((v) => v - L), mag);
    c.wc.forEach((wc, i) => px.push({ w: wc, mag: c.ex[i], L }));
  }
  px.sort((a, b) => a.w - b.w);
  const wpc = px.map((o) => o.w), magpc = px.map((o) => o.mag), PXL = px.map((o) => o.L), GM = magpc.map((v) => -v);

  const UGF = wgc.length ? wgc[0] : NaN;
  const bounds = [0, ...cw];
  let slopeAtUGF = NaN;
  if (!Number.isNaN(UGF)) { let idx = 0; bounds.forEach((b, i) => { if (UGF > b) idx = i; }); slopeAtUGF = segSlope[idx]; }
  let GBW = NaN, gbwNote = "";
  if (slope0 === 0) {
    const target = 20 * Math.log10(c0) - 3.0103;
    const w3 = crossings(w, mag.map((v) => v - target), mag).wc;
    if (w3.length) { GBW = c0 * w3[0]; gbwNote = `DC gain ${fmt(c0)} × BW(−3 dB) ${fmt(w3[0])} rad/s`; }
  }
  if (Number.isNaN(GBW) && !Number.isNaN(UGF)) { GBW = UGF; gbwNote = "equals UGF since |G(UGF)| = 1"; }

  const status = statusOfPoles(polyRoots(polyAdd(D, polyScale(padN, K0))));

  const vw = [wlo, ...cw, whi], vA = [20 * Math.log10(c0) + slope0 * Math.log10(wlo)];
  for (let k = 1; k < vw.length; k++) vA.push(vA[k - 1] + segSlope[k - 1] * (Math.log10(vw[k]) - Math.log10(vw[k - 1])));
  const fin = mag.filter(Number.isFinite);
  const ytop = Math.max(arrMax(fin), arrMax(vA));
  let ybot = Math.min(arrMin(fin), arrMin(vA));
  ybot = Math.max(ybot, ytop - 300);
  const pad = 0.12 * (ytop - ybot) + 5;
  const pmin = Math.min(arrMin(ph), ...refPh), pmax = Math.max(arrMax(ph), ...refPh);
  const span = pmax - pmin;
  const tick = span > 900 ? 180 : span > 450 ? 90 : 45;
  const slopeRows = segSlope.map((s, k) => ({ lo: k === 0 ? 0 : cw[k - 1], hi: k < cw.length ? cw[k] : Infinity, slope: s }));
  return {
    N, D, K0, m, n, z, p, w, mag, ph, cw, segSlope, c0, slope0, wlo, whi, vw, vA, yl1: [ybot - pad, ytop + pad],
    yl2: [tick * Math.floor((pmin - 5) / tick), tick * Math.ceil((pmax + 5) / tick)], tick,
    wgc, phgc, PM, refPh, wpc, magpc, PXL, GM, UGF, GBW, gbwNote, slopeAtUGF, status, slopeRows,
  };
}

/* ---------------------------------------------------------------------
   6. HIGH-QUALITY PNG EXPORT OF A PLOT
   --------------------------------------------------------------------- */
function exportPlotPNG(svg, W, H, title, legend, fileName) {
  const esc = (s) => String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
  const items = (legend || []).map((l) => ({ ...l, w: 34 + l.label.length * 6.6 + 12 }));
  const rowH = 20, top = 46;
  let rows = 0, cx = 16;
  const parts = [];
  items.forEach((l) => {
    if (cx + l.w > W - 10 && cx > 16) { cx = 16; rows++; }
    const y = top + rows * rowH;
    let sw;
    if (l.dot) sw = `<circle cx="${cx + 9}" cy="${y - 4}" r="4.5" fill="${l.color}"/>`;
    else if (l.dash) sw = `<line x1="${cx}" x2="${cx + 18}" y1="${y - 4}" y2="${y - 4}" stroke="${l.color}" stroke-width="2" stroke-dasharray="5 3"/>`;
    else sw = `<line x1="${cx}" x2="${cx + 18}" y1="${y - 4}" y2="${y - 4}" stroke="${l.color}" stroke-width="3"/>`;
    parts.push(sw + `<text x="${cx + 25}" y="${y}" font-size="12" fill="#334155">${esc(l.label)}</text>`);
    cx += l.w;
  });
  const hh = top + (items.length ? (rows + 1) * rowH : 0) + 4;
  const clone = svg.cloneNode(true);
  clone.removeAttribute("class");
  clone.removeAttribute("style");
  clone.setAttribute("x", "0");
  clone.setAttribute("y", String(hh));
  clone.setAttribute("width", String(W));
  clone.setAttribute("height", String(H));
  clone.querySelectorAll("[data-hover]").forEach((n) => n.remove());
  const inner = new XMLSerializer().serializeToString(clone);
  const total = H + hh;
  const xml =
    `<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${total}" viewBox="0 0 ${W} ${total}" font-family="Inter, system-ui, -apple-system, Segoe UI, Roboto, Arial, sans-serif">` +
    `<rect width="${W}" height="${total}" fill="#ffffff"/>` +
    `<text x="16" y="28" font-size="18" font-weight="700" fill="#0f172a">${esc(title)}</text>` +
    parts.join("") + inner + `</svg>`;
  const scale = Math.max(1, Math.min(8, Math.sqrt(14e6 / (W * total))));      // as sharp as the browser allows
  const cw = Math.round(W * scale), ch = Math.round(total * scale);
  const url = URL.createObjectURL(new Blob([xml], { type: "image/svg+xml;charset=utf-8" }));
  const img = new Image();
  img.onload = () => {
    const c = document.createElement("canvas");
    c.width = cw; c.height = ch;
    const ctx = c.getContext("2d");
    ctx.fillStyle = "#ffffff"; ctx.fillRect(0, 0, cw, ch);
    ctx.imageSmoothingEnabled = true; ctx.imageSmoothingQuality = "high";
    ctx.drawImage(img, 0, 0, cw, ch);
    URL.revokeObjectURL(url);
    c.toBlob((blob) => {
      if (!blob) return;
      const u = URL.createObjectURL(blob);
      const a = document.createElement("a");
      a.href = u; a.download = fileName;
      document.body.appendChild(a); a.click(); a.remove();
      setTimeout(() => URL.revokeObjectURL(u), 5000);
    }, "image/png");
  };
  img.onerror = () => { URL.revokeObjectURL(url); window.alert("Could not export the graph."); };
  img.src = url;
}

/* ---------------------------------------------------------------------
   7. INTERACTIVE SVG PLOT  (wheel / pinch zoom, drag pan, buttons, PNG download)
      The plot width follows its container, so text stays readable on phones.
   --------------------------------------------------------------------- */
function Plot({ title, xlabel, ylabel, x0, x1, y0, y1, logX = false, equal = false, height = 420, yStep, render, xView, onXView, legend }) {
  const wrapRef = useRef(null);
  const [W, setW] = useState(820);
  useEffect(() => {
    const el = wrapRef.current;
    if (!el) return undefined;
    const measure = () => {
      const w = Math.round(el.getBoundingClientRect().width);
      if (w > 120) setW((o) => (Math.abs(o - w) > 2 ? Math.min(w, 1200) : o));
    };
    measure();
    if (typeof ResizeObserver === "undefined") { window.addEventListener("resize", measure); return () => window.removeEventListener("resize", measure); }
    const ro = new ResizeObserver(measure);
    ro.observe(el);
    return () => ro.disconnect();
  }, []);
  const small = W < 560;
  const ml = small ? 50 : 66, mr = small ? 10 : 16, mt = 12, mb = small ? 40 : 46;
  const H = equal ? Math.round(Math.min(height, Math.max(300, W * 0.95 + 40))) : small ? Math.round(height * 0.78) : height;
  const pw = W - ml - mr, ph = H - mt - mb;

  const cid = "c" + useId().replace(/[^a-zA-Z0-9]/g, "");
  const svgRef = useRef(null), hoverRef = useRef(null);
  const ptrs = useRef(new Map()), gesture = useRef(null);
  const [touchMode, setTouchMode] = useState(false);
  const init = useMemo(() => {
    if (!equal) return { x0, x1, y0, y1 };
    const xc = (x0 + x1) / 2, span = ((y1 - y0) * pw) / ph;
    return { x0: xc - span / 2, x1: xc + span / 2, y0, y1 };
  }, [x0, x1, y0, y1, equal, pw, ph]);
  const [view, setView] = useState(init);
  useEffect(() => setView(init), [init]);
  const cx = xView || { x0: view.x0, x1: view.x1 };
  const cur = { x0: cx.x0, x1: cx.x1, y0: view.y0, y1: view.y1 };
  const curRef = useRef(cur); curRef.current = cur;
  const X = (v) => (logX ? Math.log10(v) : v);
  const XI = (v) => (logX ? Math.pow(10, v) : v);
  const sx = (v) => ml + ((X(v) - X(cur.x0)) / (X(cur.x1) - X(cur.x0))) * pw;
  const sy = (v) => mt + ((cur.y1 - v) / (cur.y1 - cur.y0)) * ph;

  const apply = (nx0, nx1, ny0, ny1) => {
    if (![nx0, nx1, ny0, ny1].every(Number.isFinite) || nx1 <= nx0 || ny1 <= ny0) return;
    if (onXView) onXView({ x0: nx0, x1: nx1 });
    setView((v) => ({ x0: onXView ? v.x0 : nx0, x1: onXView ? v.x1 : nx1, y0: ny0, y1: ny1 }));
  };
  const zoomAt = (px, py, f) => {
    const c = curRef.current, a = X(c.x0), b = X(c.x1);
    const xv = a + ((px - ml) / pw) * (b - a), yv = c.y1 - ((py - mt) / ph) * (c.y1 - c.y0);
    apply(XI(xv + (a - xv) * f), XI(xv + (b - xv) * f), yv + (c.y0 - yv) * f, yv + (c.y1 - yv) * f);
  };
  const reset = () => { setView(init); if (onXView) onXView({ x0: init.x0, x1: init.x1 }); };
  useEffect(() => {
    const el = svgRef.current;
    const h = (e) => { e.preventDefault(); const r = el.getBoundingClientRect(); zoomAt(((e.clientX - r.left) * W) / r.width, ((e.clientY - r.top) * H) / r.height, e.deltaY > 0 ? 1.2 : 1 / 1.2); };
    el.addEventListener("wheel", h, { passive: false });
    return () => el.removeEventListener("wheel", h);
  });
  const pt = (e) => { const r = svgRef.current.getBoundingClientRect(); return [((e.clientX - r.left) * W) / r.width, ((e.clientY - r.top) * H) / r.height]; };
  const onDown = (e) => {
    const p = pt(e);
    ptrs.current.set(e.pointerId, p);
    try { e.currentTarget.setPointerCapture(e.pointerId); } catch (err) { /* ignore */ }
    const c = { ...curRef.current };
    if (ptrs.current.size === 1) gesture.current = { type: "pan", p0: p, cur: c };
    else if (ptrs.current.size === 2) {
      const [a, b] = [...ptrs.current.values()];
      gesture.current = { type: "pinch", d0: Math.hypot(a[0] - b[0], a[1] - b[1]) || 1, m0: [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2], cur: c };
    }
  };
  const onMove = (e) => {
    const p = pt(e);
    if (ptrs.current.has(e.pointerId)) ptrs.current.set(e.pointerId, p);
    const g = gesture.current;
    if (g && g.type === "pan" && ptrs.current.size === 1) {
      const c = g.cur, a = X(c.x0), b = X(c.x1);
      const dx = ((p[0] - g.p0[0]) / pw) * (b - a), dy = ((p[1] - g.p0[1]) / ph) * (c.y1 - c.y0);
      apply(XI(a - dx), XI(b - dx), c.y0 + dy, c.y1 + dy);
    } else if (g && g.type === "pinch" && ptrs.current.size >= 2) {
      const [a1, b1] = [...ptrs.current.values()];
      const d = Math.hypot(a1[0] - b1[0], a1[1] - b1[1]) || 1;
      const m = [(a1[0] + b1[0]) / 2, (a1[1] + b1[1]) / 2];
      const f = g.d0 / d, c = g.cur, A = X(c.x0), B = X(c.x1);
      const xv = A + ((g.m0[0] - ml) / pw) * (B - A), yv = c.y1 - ((g.m0[1] - mt) / ph) * (c.y1 - c.y0);
      const sxn = (B - A) * f, syn = (c.y1 - c.y0) * f;
      const nA = xv - ((m[0] - ml) / pw) * sxn, ny1 = yv + ((m[1] - mt) / ph) * syn;
      apply(XI(nA), XI(nA + sxn), ny1 - syn, ny1);
    } else if (!g && hoverRef.current) {
      const c = curRef.current, a = X(c.x0), b = X(c.x1);
      const inside = p[0] >= ml && p[0] <= ml + pw && p[1] >= mt && p[1] <= mt + ph;
      hoverRef.current.textContent = inside ? `${xlabel.split(" ")[0]} = ${fmt(XI(a + ((p[0] - ml) / pw) * (b - a)), 4)}   y = ${fmt(c.y1 - ((p[1] - mt) / ph) * (c.y1 - c.y0), 4)}` : "";
    }
  };
  const onUp = (e) => {
    ptrs.current.delete(e.pointerId);
    if (ptrs.current.size === 0) gesture.current = null;
    else if (ptrs.current.size === 1) gesture.current = { type: "pan", p0: [...ptrs.current.values()][0], cur: { ...curRef.current } };
  };
  const download = () => {
    const slug = title.toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-|-$/g, "") || "graph";
    exportPlotPNG(svgRef.current, W, H, title, legend, `${slug}.png`);
  };

  /* ticks */
  const niceTicks = (lo, hi, step0) => {
    let step = step0;
    if (!step) { const raw = (hi - lo) / (small ? 5 : 7), mg = Math.pow(10, Math.floor(Math.log10(raw))), nm = raw / mg; step = (nm < 1.5 ? 1 : nm < 3 ? 2 : nm < 7 ? 5 : 10) * mg; }
    const t = []; for (let v = Math.ceil(lo / step - 1e-9) * step; v <= hi + step * 1e-9 && t.length < 60; v += step) t.push(+v.toPrecision(12));
    return t;
  };
  const tickFmt = (v) => (v !== 0 && (Math.abs(v) >= 1e5 || Math.abs(v) < 1e-3) ? v.toExponential(1) : String(+v.toPrecision(6)));
  let xt = [];
  if (logX) {
    const a = Math.log10(cur.x0), b = Math.log10(cur.x1);
    for (let k = Math.floor(a); k <= Math.ceil(b); k++) for (let mm = 1; mm <= 9; mm++) {
      const v = mm * Math.pow(10, k);
      if (v < cur.x0 || v > cur.x1) continue;
      if (b - a > (small ? 3 : 4) && mm !== 1) continue;
      xt.push({ v, major: mm === 1, label: mm === 1 || (b - a < 1.5 && (mm === 2 || mm === 5)) });
    }
  } else xt = niceTicks(cur.x0, cur.x1).map((v) => ({ v, major: true, label: true }));
  const yt = niceTicks(cur.y0, cur.y1, yStep);

  return (
    <div className="plot" ref={wrapRef}>
      <div className="plot-bar">
        <span className="plot-title">{title}</span>
        <span className="plot-btns">
          <button className={"touch-only" + (touchMode ? " on" : "")} onClick={() => setTouchMode((t) => !t)} title="Switch between scrolling the page and moving the graph with your finger">{touchMode ? "✋ Move" : "☝ Scroll"}</button>
          <button onClick={() => zoomAt(ml + pw / 2, mt + ph / 2, 1 / 1.4)} title="Zoom in">＋</button>
          <button onClick={() => zoomAt(ml + pw / 2, mt + ph / 2, 1.4)} title="Zoom out">－</button>
          <button onClick={reset}>Reset</button>
        </span>
      </div>
      {legend && (
        <div className="legend">
          {legend.map((l, i) => (
            <span key={i}>
              <i style={{ width: l.dot ? 9 : 18, height: l.dash ? 0 : l.dot ? 9 : 3, borderRadius: l.dot ? "50%" : 2, background: l.dash ? "transparent" : l.color, borderTop: l.dash ? `2px dashed ${l.color}` : "none" }} />
              {l.label}
            </span>
          ))}
        </div>
      )}
      <svg ref={svgRef} viewBox={`0 0 ${W} ${H}`} className="plot-svg" style={{ touchAction: touchMode ? "none" : "pan-y" }} onPointerDown={onDown} onPointerMove={onMove} onPointerUp={onUp} onPointerCancel={onUp} onPointerLeave={() => { if (hoverRef.current && !gesture.current) hoverRef.current.textContent = ""; }}>
        <defs><clipPath id={cid}><rect x={ml} y={mt} width={pw} height={ph} /></clipPath></defs>
        <rect x={ml} y={mt} width={pw} height={ph} fill="#fff" />
        {xt.map((t, i) => (<line key={"gx" + i} x1={sx(t.v)} x2={sx(t.v)} y1={mt} y2={mt + ph} stroke={t.major ? "#dbe3ee" : "#eef2f7"} strokeWidth="1" />))}
        {yt.map((v, i) => (<line key={"gy" + i} x1={ml} x2={ml + pw} y1={sy(v)} y2={sy(v)} stroke="#dbe3ee" strokeWidth="1" />))}
        <g clipPath={`url(#${cid})`}>{render({ sx, sy, cur, pw, ph, ml, mt, W, H })}</g>
        <rect x={ml} y={mt} width={pw} height={ph} fill="none" stroke="#94a3b8" />
        {xt.filter((t) => t.label).map((t, i) => (<text key={"tx" + i} x={sx(t.v)} y={mt + ph + 16} fontSize="11" textAnchor="middle" fill="#475569">{logX && t.v >= 1e-2 && t.v <= 1e4 ? String(t.v) : logX ? t.v.toExponential(0).replace("e+", "e") : tickFmt(t.v)}</text>))}
        {yt.map((v, i) => (<text key={"ty" + i} x={ml - 7} y={sy(v) + 4} fontSize="11" textAnchor="end" fill="#475569">{tickFmt(v)}</text>))}
        <text x={ml + pw / 2} y={H - 8} fontSize="12" textAnchor="middle" fill="#334155">{xlabel}</text>
        <text transform={`translate(14 ${mt + ph / 2}) rotate(-90)`} fontSize="12" textAnchor="middle" fill="#334155">{ylabel}</text>
        <text ref={hoverRef} data-hover="1" x={ml + pw - 6} y={mt + 14} fontSize="11" textAnchor="end" fill="#64748b" fontFamily="ui-monospace,monospace" />
      </svg>
      <div className="plot-foot">
        <button className="dl-btn" onClick={download}>⬇ Download graph (PNG)</button>
        <span className="plot-hint">wheel / pinch = zoom · drag = pan</span>
      </div>
    </div>
  );
}

/* small SVG helpers */
function Tag({ x, y, lines, color = COL.ink, anchor = "start", size = 11 }) {
  const arr = Array.isArray(lines) ? lines : [lines];
  const w = Math.max(...arr.map((s) => s.length)) * size * 0.6 + 10, h = arr.length * (size + 3) + 4;
  const rx = anchor === "end" ? x - w : anchor === "middle" ? x - w / 2 : x;
  return (
    <g pointerEvents="none">
      <rect x={rx} y={y - h + 2} width={w} height={h} rx="3" fill="#ffffff" fillOpacity="0.9" stroke="#e2e8f0" strokeWidth="0.7" />
      {arr.map((s, i) => (<text key={i} x={rx + 5} y={y - h + 2 + (i + 1) * (size + 3) - 1} fontSize={size} fill={color} fontWeight="600" fontFamily="ui-monospace,monospace">{s}</text>))}
    </g>
  );
}
const Cross = ({ x, y, r = 6, color, w = 2.4 }) => (<g stroke={color} strokeWidth={w} strokeLinecap="round"><line x1={x - r} y1={y - r} x2={x + r} y2={y + r} /><line x1={x - r} y1={y + r} x2={x + r} y2={y - r} /></g>);
function pathD(pts, sx, sy, lim = 1e6) {
  let d = "", pen = false;
  for (const [x, y] of pts) {
    if (!Number.isFinite(x) || !Number.isFinite(y) || Math.abs(x) > lim || Math.abs(y) > lim) { pen = false; continue; }
    d += (pen ? "L" : "M") + sx(x).toFixed(1) + " " + sy(y).toFixed(1); pen = true;
  }
  return d;
}
/* path in DATA coordinates (drawn through an SVG transform, so zoom / pan / slider never rebuild it) */
function pathDataCoords(pts, lim = 1e5) {
  let d = "", pen = false;
  for (const [x, y] of pts) {
    if (!Number.isFinite(x) || !Number.isFinite(y) || Math.abs(x) > lim || Math.abs(y) > lim) { pen = false; continue; }
    d += (pen ? "L" : "M") + +x.toPrecision(6) + " " + +y.toPrecision(6); pen = true;
  }
  return d;
}

/* ---------------------------------------------------------------------
   8. SHARED VIEW COMPONENTS
   --------------------------------------------------------------------- */
const Badge = ({ level, children }) => <span className={`badge ${level}`}>{children}</span>;
const Chip = ({ label, value, tone }) => (<div className={`chip ${tone || ""}`}><span>{label}</span><b>{value}</b></div>);

function PoleMap({ roots, title = "S-domain poles" }) {
  const m = Math.max(1.3 * Math.max(1, ...roots.map((r) => Math.abs(r[0])), ...roots.map((r) => Math.abs(r[1]))), 1);
  const colorOf = (r) => (r[0] < -1e-6 ? COL.green : r[0] > 1e-6 ? COL.red : COL.orange);
  return (
    <Plot title={title} xlabel="Real axis (σ)" ylabel="Imaginary axis (jω)" x0={-m} x1={m} y0={-m} y1={m} equal height={430}
      legend={[{ color: COL.green, label: "× stable (LHP)" }, { color: COL.orange, label: "× on jω axis" }, { color: COL.red, label: "× unstable (RHP)" }]}
      render={({ sx, sy, cur }) => (
        <g>
          <rect x={sx(0)} y={sy(cur.y1)} width={Math.max(0, sx(cur.x1) - sx(0))} height={sy(cur.y0) - sy(cur.y1)} fill="#fecaca" opacity=".4" />
          <rect x={sx(cur.x0)} y={sy(cur.y1)} width={Math.max(0, sx(0) - sx(cur.x0))} height={sy(cur.y0) - sy(cur.y1)} fill="#bbf7d0" opacity=".35" />
          <line x1={sx(cur.x0)} x2={sx(cur.x1)} y1={sy(0)} y2={sy(0)} stroke="#0f172a" />
          <line x1={sx(0)} x2={sx(0)} y1={sy(cur.y0)} y2={sy(cur.y1)} stroke="#0f172a" />
          {roots.map((r, i) => (<g key={i}><Cross x={sx(r[0])} y={sy(r[1])} r={7} color={colorOf(r)} w={2.8} /><Tag x={sx(r[0]) + 9} y={sy(r[1]) - 6} lines={fmtC(r, 3)} color={colorOf(r)} size={10} /></g>))}
          <text x={sx(cur.x1) - 8} y={sy(cur.y0) - 8} textAnchor="end" fill={COL.red} fontWeight="700" fontSize="13">RHP</text>
          <text x={sx(cur.x0) + 8} y={sy(cur.y0) - 8} fill={COL.green} fontWeight="700" fontSize="13">LHP</text>
        </g>
      )} />
  );
}

function RouthTable({ A }) {
  const { R, cols, n, info } = A;
  return (
    <div className="scroll">
      <table className="tbl mono">
        <tbody>
          {R.map((row, i) => (
            <tr key={i} className={info.epsRows.includes(i) ? "eps" : info.zeroRows.includes(i) ? "zrow" : ""}>
              <th>S<sup>{n - i}</sup></th>
              {row.slice(0, cols - 1).map((v, j) => (<td key={j}>{fmt(v, 5)}</td>))}
              <td className="note">{info.epsRows.includes(i) ? `first element was 0 → ε = ${fmt(info.epsVal, 2)}` : info.zeroRows.includes(i) ? "zero row → replaced by dA/dS" : ""}</td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}
function RouthDetails({ A, roots }) {
  const verdict = routhVerdict(A, roots);
  const tol = 1e-6;
  const nR = roots.filter((r) => r[0] > tol).length, nI = roots.filter((r) => Math.abs(r[0]) <= tol).length, nL = roots.filter((r) => r[0] < -tol).length;
  return (
    <>
      <div className="verdict"><Badge level={verdict.level}>{verdict.text}</Badge></div>
      <div className="chips"><Chip label="RHP poles" value={A.numRHP} tone={A.numRHP ? "bad" : ""} /><Chip label="On jω axis" value={A.numImag} tone={A.numImag ? "warn" : ""} /><Chip label="LHP poles" value={A.numLHP} /></div>
      <h4>Routh table</h4>
      <RouthTable A={A} />
      <p className="muted mono">First column: [{A.R.map((r) => fmt(r[0], 4)).join(", ")}]</p>
      {A.info.aux.map((a, k) => (
        <div key={k} className="note-box">
          <b>Zero row at S<sup>{A.n - A.info.zeroRows[k]}</sup></b> → auxiliary polynomial A(S) of degree {a.length - 1}, coefficients [{a.map((v) => fmt(v, 4)).join(", ")}]
          <div className="mono">roots of A(S): {rootsClean(a).map((r) => fmtC(r)).join("  ,  ")}</div>
        </div>
      ))}
      <h4>Verification with roots()</h4>
      <div className="mono pole-list">{roots.map((r, i) => (<span key={i} className={r[0] > tol ? "neg" : Math.abs(r[0]) <= tol ? "mid" : "pos"}>{fmtC(r)}</span>))}</div>
      <p className="muted">RHP = {nR} · jω axis = {nI} · LHP = {nL}{(nR !== A.numRHP || nI !== A.numImag) && <b className="warn-txt"> — warning: roots() disagrees with the Routh counts (numerical sensitivity near the jω axis).</b>}</p>
      <PoleMap roots={roots} />
    </>
  );
}
function RouthNumericView({ res }) {
  const A = useMemo(() => analyzePoly(res.S), [res]);
  const roots = useMemo(() => rootsClean(A.S), [A]);
  return (<div className="card"><h3>Routh result — order {A.n}</h3><RouthDetails A={A} roots={roots} /></div>);
}
function RouthKView({ res }) {
  const [kt, setKt] = useState(String(+res.kDefault.toPrecision(6)));
  useEffect(() => setKt(String(+res.kDefault.toPrecision(6))), [res]);
  const kv = (() => { try { return parseNum(kt); } catch (e) { return NaN; } })();
  const at = useMemo(() => {
    if (!Number.isFinite(kv)) return null;
    try { const S = trimLead(res.Sfn(kv)); if (S.length < 2) return null; return { A: analyzePoly(S), roots: rootsClean(S) }; } catch (e) { return null; }
  }, [res, kv]);
  return (
    <>
      <div className="card">
        <h3>Stability by K range <small>({fmt(res.Kfrom)} ≤ K ≤ {fmt(res.Kto)})</small></h3>
        <div className="ranges">
          {res.intervals.map((x, i) => (<div key={i} className="range-row"><span className="mono">{rangeStr(x.lo, x.hi)}</span><Badge level={x.level}>{x.text}</Badge></div>))}
        </div>
        {res.intervals.some((x) => x.level === "stable") ? (<p className="ok-txt">Stable for: {res.intervals.filter((x) => x.level === "stable").map((x) => rangeStr(x.lo, x.hi)).join("  ,  ")}</p>) : (<p className="warn-txt">No K in this range makes the system stable.</p>)}
        {res.critInfo.length > 0 && (<><h4>Critical K values</h4><div className="ranges">{res.critInfo.map((c, i) => (<div key={i} className="range-row"><span className="mono">K = {fmt(c.K, 7)}</span><span className="muted">{c.level === "marginal" && c.ws.length ? `poles on jω axis at ω = ${c.ws.join(", ")} rad/s` : c.text}</span></div>))}</div></>)}
        <p className="muted small">{res.affine ? "Critical values are exact (coefficients are linear in K)." : "Coefficients are non-linear in K: critical values were found by scanning + bisection."}</p>
      </div>
      <div className="card">
        <h3>Routh table at a chosen K</h3>
        <div className="kbar">
          <label>K = <input value={kt} onChange={(e) => setKt(e.target.value)} className="num" /></label>
          <input type="range" min={res.Kfrom} max={res.Kto} step={(res.Kto - res.Kfrom) / 2000} value={Number.isFinite(kv) ? Math.min(Math.max(kv, res.Kfrom), res.Kto) : res.Kfrom} onChange={(e) => setKt(String(+(+e.target.value).toPrecision(6)))} />
        </div>
        {at ? <RouthDetails A={at.A} roots={at.roots} /> : <div className="alert">The polynomial is undefined or constant at this K.</div>}
      </div>
    </>
  );
}

/* ---------------------------------------------------------------------
   9. ROOT LOCUS VIEW
   The locus branches are built ONCE (in data coordinates) and drawn with an SVG
   transform. Moving the K slider only updates the small red squares.
   --------------------------------------------------------------------- */
const Branches = memo(function Branches({ paths, transform }) {
  return (
    <g transform={transform}>
      {paths.map((d, b) => (<path key={b} d={d} fill="none" stroke={BRANCH[b % BRANCH.length]} strokeWidth="2" strokeLinejoin="round" vectorEffect="non-scaling-stroke" />))}
    </g>
  );
});

const LocusData = memo(function LocusData({ res }) {
  return (
    <div className="card">
      <h3>Locus data</h3>
      <p className="muted small">On the plot: × = open-loop poles, ○ = open-loop zeros. Characteristic equation: D(S) + K·N(S) = 0, K ≥ 0.</p>
      <h4>Poles ({res.p.length})</h4><div className="mono pole-list">{res.p.map((r, i) => <span key={i}>p{i + 1} = {fmtC(r)}</span>)}</div>
      <h4>Zeros ({res.z.length})</h4><div className="mono pole-list">{res.z.length ? res.z.map((r, i) => <span key={i}>z{i + 1} = {fmtC(r)}</span>) : <span className="muted">none (finite)</span>}</div>
      <h4>Branches</h4><p>{res.n}</p>
      <h4>Asymptotes</h4>
      {res.na > 0 ? <p className="mono">n − m = {res.na} · centroid = {fmt(res.sigA)} · angles = {res.angA.map((a) => fmt(a, 5) + "°").join(", ")}</p> : <p className="muted">n = m: no asymptotes (branches end on finite zeros).</p>}
      <h4>Real-axis segments</h4><p className="mono">{res.segments.length ? res.segments.join("  ,  ") : "none"}</p>
      <h4>Break-away / break-in points</h4>
      {res.bp.length ? res.bp.map((c, i) => <p key={i} className="mono">S = {fmt(c)} at K = {fmt(res.bpK[i])}</p>) : <p className="muted">none</p>}
      <h4>Angles of departure / arrival</h4>
      {res.departures.map((d, i) => <p key={i} className="mono">pole {fmtC(d.pole)} : {fmt(d.ang, 4)}° (conjugate {fmt(-d.ang, 4)}°)</p>)}
      {res.arrivals.map((d, i) => <p key={i} className="mono">zero {fmtC(d.zero)} : {fmt(d.ang, 4)}° (conjugate {fmt(-d.ang, 4)}°)</p>)}
      {!res.departures.length && !res.arrivals.length && <p className="muted">no complex poles or zeros</p>}
      <h4>jω-axis crossings</h4>
      {res.Kcrit.length ? res.Kcrit.map((k, i) => <p key={i} className="mono">K = {fmt(k)} at ω = {fmt(res.wcr[i])} rad/s</p>) : <p className="muted">none for K &gt; 0</p>}
      <h4>Stability condition</h4>
      {res.intervals.map((x, i) => (<div key={i} className="range-row"><span className="mono">{rangeStr(x.lo, x.hi)}</span><Badge level={x.stable ? "stable" : "unstable"}>{x.stable ? "STABLE" : `UNSTABLE (${x.nR} RHP)`}</Badge></div>))}
      <p className={res.condTxt.startsWith("unstable") ? "warn-txt" : "ok-txt"}><b>Stable for:</b> {res.condTxt}</p>
    </div>
  );
});

function LocusView({ res }) {
  const [K, setK] = useState(res.K0);
  const [Kt, setKt] = useState(String(res.K0));
  useEffect(() => { setK(res.K0); setKt(String(res.K0)); }, [res]);
  const paths = useMemo(() => res.branches.map((br) => pathDataCoords(br)), [res]);
  const clp = useMemo(() => rootsClean(polyAdd(res.D, polyScale(res.padN, K))), [res, K]);
  const st = statusOfPoles(clp);
  const { view } = res;
  return (
    <>
      <div className="card">
        <div className="kbar sticky">
          <label>K = <input value={Kt} onChange={(e) => { setKt(e.target.value); try { const v = parseNum(e.target.value); if (v >= 0) setK(v); } catch (er) { /* ignore */ } }} className="num" inputMode="decimal" /></label>
          <input type="range" min="0" max={res.Kslider} step={res.Kslider / 4000} value={Math.min(K, res.Kslider)} onChange={(e) => { const v = +e.target.value; setK(v); setKt(String(+v.toPrecision(6))); }} />
          <Badge level={st}>{STATUS_TXT[st]}</Badge>
        </div>
        <Plot title="Root Locus" xlabel="Real axis (σ)" ylabel="Imaginary axis (jω)" x0={view.x0} x1={view.x1} y0={view.y0} y1={view.y1} equal height={560}
          legend={[{ color: "#111", label: "× open-loop poles" }, { color: "#111", label: "○ open-loop zeros" }, { color: COL.magenta, label: "jω crossing", dot: true }, { color: COL.green, label: "break-away / break-in", dot: true }, { color: COL.red, label: "closed-loop poles (K)", dot: true }, { color: "#6b7280", label: "asymptotes", dash: true }]}
          render={({ sx, sy, cur, pw, ph, ml, mt }) => {
            const span = cur.y1 - cur.y0;
            const kx = pw / (cur.x1 - cur.x0), ky = ph / (cur.y1 - cur.y0);
            const tf = `matrix(${kx} 0 0 ${-ky} ${ml - cur.x0 * kx} ${mt + cur.y1 * ky})`;
            return (
              <g>
                <rect x={sx(0)} y={sy(cur.y1)} width={Math.max(0, sx(cur.x1) - sx(0))} height={sy(cur.y0) - sy(cur.y1)} fill="#fecaca" opacity=".4" />
                <rect x={sx(cur.x0)} y={sy(cur.y1)} width={Math.max(0, sx(0) - sx(cur.x0))} height={sy(cur.y0) - sy(cur.y1)} fill="#bbf7d0" opacity=".35" />
                <line x1={sx(cur.x0)} x2={sx(cur.x1)} y1={sy(0)} y2={sy(0)} stroke="#0f172a" />
                <line x1={sx(0)} x2={sx(0)} y1={sy(cur.y0)} y2={sy(cur.y1)} stroke="#0f172a" />
                {res.angA.map((a, i) => (<line key={"as" + i} x1={sx(res.sigA)} y1={sy(0)} x2={sx(res.sigA + 6 * span * Math.cos((a * Math.PI) / 180))} y2={sy(6 * span * Math.sin((a * Math.PI) / 180))} stroke="#6b7280" strokeDasharray="6 5" strokeWidth="1.2" />))}
                <Branches paths={paths} transform={tf} />
                {res.p.map((r, i) => (<Cross key={"p" + i} x={sx(r[0])} y={sy(r[1])} r={7} color="#111" w={2.6} />))}
                {res.z.map((r, i) => (<circle key={"z" + i} cx={sx(r[0])} cy={sy(r[1])} r="6" fill="#fff" stroke="#111" strokeWidth="2.2" />))}
                {res.wcr.map((w, i) => (<g key={"w" + i}>{[w, -w].map((yy, q) => (<rect key={q} x={sx(0) - 6} y={sy(yy) - 6} width="12" height="12" fill={COL.magenta} stroke="#fff" />))}<Tag x={sx(0) + 10} y={sy(w) - 4} lines={`K=${fmt(res.Kcrit[i], 4)}  ω=${fmt(w, 4)}`} color={COL.magenta} size={10} /></g>))}
                {res.bp.map((c, i) => (<g key={"b" + i}><polygon points={`${sx(c)},${sy(0) - 8} ${sx(c) - 7},${sy(0) + 6} ${sx(c) + 7},${sy(0) + 6}`} fill={COL.green} stroke="#fff" /><Tag x={sx(c) + 8} y={sy(0) - 12} lines={`S=${fmt(c, 4)}  K=${fmt(res.bpK[i], 4)}`} color="#15803d" size={10} /></g>))}
                {clp.map((r, i) => (<rect key={"c" + i} x={sx(r[0]) - 6} y={sy(r[1]) - 6} width="12" height="12" fill={COL.red} stroke="#fff" strokeWidth="1.5" />))}
                <text x={sx(cur.x1) - 8} y={sy(cur.y0) - 8} textAnchor="end" fill={COL.red} fontWeight="700" fontSize="13">RHP</text>
                <text x={sx(cur.x0) + 8} y={sy(cur.y0) - 8} fill={COL.green} fontWeight="700" fontSize="13">LHP</text>
              </g>
            );
          }} />
        <h4>Closed-loop poles at K = {fmt(K, 6)}</h4>
        <div className="mono pole-list">{clp.map((r, i) => (<span key={i} className={r[0] > 1e-7 ? "neg" : Math.abs(r[0]) <= 1e-7 ? "mid" : "pos"}>{fmtC(r)}</span>))}</div>
        <p className="muted small">Move the slider and the red squares slide along the locus.</p>
      </div>
      <LocusData res={res} />
    </>
  );
}

/* ---------------------------------------------------------------------
   10. BODE VIEW
   --------------------------------------------------------------------- */
function BodeView({ res }) {
  const [xv, setXv] = useState({ x0: res.wlo, x1: res.whi });
  useEffect(() => setXv({ x0: res.wlo, x1: res.whi }), [res]);
  const r = res;
  const magPts = useMemo(() => r.w.map((w, i) => [w, r.mag[i]]), [r]);
  const phPts = useMemo(() => r.w.map((w, i) => [w, r.ph[i]]), [r]);
  const sv = [r.wlo, ...r.cw, r.whi];
  return (
    <>
      <div className="card">
        <h3>Bode summary <Badge level={r.status}>closed loop: {STATUS_TXT[r.status]}</Badge></h3>
        <div className="chips">
          <Chip label="UGF" value={Number.isNaN(r.UGF) ? "none" : `${fmt(r.UGF, 4)} rad/s`} />
          <Chip label="GBW" value={Number.isNaN(r.GBW) ? "n/a" : `${fmt(r.GBW, 4)} rad/s`} />
          <Chip label="Roll-off" value={slopeStr(r.segSlope[r.segSlope.length - 1])} />
        </div>
        <div className="chips">
          {r.wgc.length ? r.wgc.map((w, i) => <Chip key={i} label={`GX${r.wgc.length > 1 ? i + 1 : ""} → PM`} value={`${fmt(w, 4)} rad/s → ${fmt(r.PM[i], 4)}°`} tone={r.PM[i] > 0 ? "" : "bad"} />) : <Chip label="GX / PM" value="no gain crossover" />}
          {r.wpc.length ? r.wpc.map((w, i) => <Chip key={i} label={`PX${r.wpc.length > 1 ? i + 1 : ""} → GM`} value={`${fmt(w, 4)} rad/s → ${fmt(r.GM[i], 4)} dB`} tone={r.GM[i] > 0 ? "" : "bad"} />) : <Chip label="PX / GM" value="phase never −180° (GM = ∞)" />}
        </div>
        <p className="muted small">GBW: {Number.isNaN(r.GBW) ? "not defined" : r.gbwNote}. GX = gain crossover (|G| = 0 dB), PX = phase crossover (phase = −180°).</p>
      </div>
      <div className="card">
        <Plot title="Bode Magnitude" xlabel="Frequency (rad/s)" ylabel="Magnitude (dB)" logX x0={r.wlo} x1={r.whi} y0={r.yl1[0]} y1={r.yl1[1]} height={440} xView={xv} onXView={setXv}
          legend={[{ color: COL.blue, label: "|G(jω)|" }, { color: COL.orange, label: "asymptotes + slopes", dash: true }, { color: COL.green, label: "GX / PM", dot: true }, { color: COL.red, label: "PX / GM", dot: true }]}
          render={({ sx, sy, cur, pw, ml, mt }) => (
            <g>
              {r.cw.map((c, i) => (<g key={"cw" + i}><line x1={sx(c)} x2={sx(c)} y1={sy(cur.y0)} y2={sy(cur.y1)} stroke="#cbd5e1" strokeDasharray="2 4" /><text x={sx(c) + 3} y={mt + 12} fontSize="10" fill="#64748b">{fmt(c, 3)}</text></g>))}
              {r.wgc.map((w, i) => (<line key={"g" + i} x1={sx(w)} x2={sx(w)} y1={sy(cur.y0)} y2={sy(cur.y1)} stroke={COL.green} strokeDasharray="2 4" />))}
              {r.wpc.map((w, i) => (<line key={"p" + i} x1={sx(w)} x2={sx(w)} y1={sy(cur.y0)} y2={sy(cur.y1)} stroke={COL.red} strokeDasharray="2 4" />))}
              <line x1={sx(cur.x0)} x2={sx(cur.x1)} y1={sy(0)} y2={sy(0)} stroke="#475569" strokeDasharray="6 4" />
              <path d={pathD(r.vw.map((w, i) => [w, r.vA[i]]), sx, sy)} fill="none" stroke={COL.orange} strokeWidth="1.8" strokeDasharray="7 5" />
              <path d={pathD(magPts, sx, sy)} fill="none" stroke={COL.blue} strokeWidth="2.4" />
              {r.segSlope.map((s, k) => {
                const wm = Math.sqrt(sv[k] * sv[k + 1]), ym = r.vA[k] + s * (Math.log10(wm) - Math.log10(sv[k]));
                if (wm < cur.x0 || wm > cur.x1) return null;
                return <Tag key={"s" + k} x={sx(wm)} y={sy(ym) - 8} anchor="middle" lines={k === r.segSlope.length - 1 ? `Roll-off ${slopeStr(s)}` : slopeStr(s)} color="#b45309" size={10} />;
              })}
              {r.wgc.map((w, i) => (<g key={"gm" + i}><circle cx={sx(w)} cy={sy(0)} r="6" fill={COL.green} stroke="#fff" strokeWidth="1.5" /><Tag x={sx(w) + 9} y={sy(0) - 8} lines={`GX${r.wgc.length > 1 ? i + 1 : ""} (UGF) = ${fmt(w, 4)}`} color="#15803d" size={10} /></g>))}
              {r.wpc.map((w, i) => (<g key={"pm" + i}><line x1={sx(w)} x2={sx(w)} y1={sy(0)} y2={sy(r.magpc[i])} stroke={COL.red} strokeWidth="3.5" /><rect x={sx(w) - 5} y={sy(r.magpc[i]) - 5} width="10" height="10" fill={COL.red} stroke="#fff" /><Tag x={sx(w) + 9} y={sy(r.magpc[i] / 2) + 8} lines={[`GM = ${fmt(r.GM[i], 4)} dB`, `at PX = ${fmt(w, 4)}`]} color="#b91c1c" size={10} /></g>))}
              <Tag x={ml + pw - 8} y={mt + 70} anchor="end" lines={[Number.isNaN(r.UGF) ? "UGF = none" : `UGF = ${fmt(r.UGF, 4)} rad/s (${fmt(r.UGF / (2 * Math.PI), 4)} Hz)`, Number.isNaN(r.GBW) ? "GBW = n/a" : `GBW = ${fmt(r.GBW, 4)} rad/s (${fmt(r.GBW / (2 * Math.PI), 4)} Hz)`, `Roll-off = ${slopeStr(r.segSlope[r.segSlope.length - 1])}`]} color="#0f172a" size={10} />
            </g>
          )} />
      </div>
      <div className="card">
        <Plot title="Bode Phase" xlabel="Frequency (rad/s)" ylabel="Phase (deg)" logX x0={r.wlo} x1={r.whi} y0={r.yl2[0]} y1={r.yl2[1]} yStep={r.tick} height={400} xView={xv} onXView={setXv}
          legend={[{ color: COL.purple, label: "∠G(jω)" }, { color: COL.red, label: "−180° line", dash: true }]}
          render={({ sx, sy, cur }) => (
            <g>
              {r.wgc.map((w, i) => (<line key={"g" + i} x1={sx(w)} x2={sx(w)} y1={sy(cur.y0)} y2={sy(cur.y1)} stroke={COL.green} strokeDasharray="2 4" />))}
              {r.wpc.map((w, i) => (<line key={"p" + i} x1={sx(w)} x2={sx(w)} y1={sy(cur.y0)} y2={sy(cur.y1)} stroke={COL.red} strokeDasharray="2 4" />))}
              {[-3, -2, -1, 0, 1, 2, 3].map((k) => { const L = -180 + 360 * k; return L > cur.y0 && L < cur.y1 ? <line key={"L" + k} x1={sx(cur.x0)} x2={sx(cur.x1)} y1={sy(L)} y2={sy(L)} stroke={COL.red} strokeDasharray="6 4" /> : null; })}
              <path d={pathD(phPts, sx, sy)} fill="none" stroke={COL.purple} strokeWidth="2.4" />
              {r.wpc.map((w, i) => (<g key={"px" + i}><rect x={sx(w) - 5} y={sy(r.PXL[i]) - 5} width="10" height="10" fill={COL.red} stroke="#fff" /><Tag x={sx(w) + 9} y={sy(r.PXL[i]) + 20} lines={`PX${r.wpc.length > 1 ? i + 1 : ""} = ${fmt(w, 4)} rad/s`} color="#b91c1c" size={10} /></g>))}
              {r.wgc.map((w, i) => (<g key={"pm" + i}><line x1={sx(w)} x2={sx(w)} y1={sy(r.refPh[i])} y2={sy(r.phgc[i])} stroke={COL.green} strokeWidth="3.5" /><circle cx={sx(w)} cy={sy(r.phgc[i])} r="6" fill={COL.green} stroke="#fff" strokeWidth="1.5" /><Tag x={sx(w) + 9} y={sy((r.refPh[i] + r.phgc[i]) / 2) + 8} lines={[`PM = ${fmt(r.PM[i], 4)}°`, `at GX = ${fmt(w, 4)}`]} color="#15803d" size={10} /></g>))}
            </g>
          )} />
      </div>
      <div className="card">
        <h3>Magnitude slopes</h3>
        {r.slopeRows.map((s, i) => (<div key={i} className="range-row"><span className="mono">{s.lo === 0 && !Number.isFinite(s.hi) ? "all ω" : !Number.isFinite(s.hi) ? `ω > ${fmt(s.lo, 4)}` : s.lo === 0 ? `ω < ${fmt(s.hi, 4)}` : `${fmt(s.lo, 4)} < ω < ${fmt(s.hi, 4)}`}</span><b className="mono">{slopeStr(s.slope)}</b></div>))}
        <h4>Poles / zeros</h4>
        <div className="mono pole-list">{r.p.map((c, i) => <span key={"p" + i}>p{i + 1} = {fmtC(c)}</span>)}{r.z.map((c, i) => <span key={"z" + i}>z{i + 1} = {fmtC(c)}</span>)}</div>
      </div>
    </>
  );
}

/* ---------------------------------------------------------------------
   11. INPUT COMPONENTS
   --------------------------------------------------------------------- */
const resize = (arr, len) => Array.from({ length: len }, (_, i) => (i < arr.length ? arr[i] : ""));
function CoeffInputs({ title, vals, setVals, n, bad, prefix }) {
  return (
    <div className="coeffs">
      <div className="coeffs-title">{title}</div>
      <div className="coeff-grid">
        {Array.from({ length: n + 1 }, (_, k) => n - k).map((p) => (
          <label key={p} className={"field" + (bad[`${prefix}${p}`] ? " bad" : "")} title={bad[`${prefix}${p}`] || ""}>
            <span>S<sup>{p}</sup></span>
            <input value={vals[p] ?? ""} onChange={(e) => { const c = vals.slice(); c[p] = e.target.value; setVals(c); }} autoCapitalize="off" autoCorrect="off" spellCheck="false" />
          </label>
        ))}
      </div>
    </div>
  );
}
const Field = ({ label, value, onChange, bad, w }) => (
  <label className={"field wide" + (bad ? " bad" : "")} title={bad || ""} style={w ? { maxWidth: w } : null}><span>{label}</span><input value={value} onChange={(e) => onChange(e.target.value)} autoCapitalize="off" autoCorrect="off" spellCheck="false" /></label>
);

/* ---------------------------------------------------------------------
   12. APP
   --------------------------------------------------------------------- */
const rev = (a) => a.slice().reverse();                         // "highest first" -> "by power"
const ROUTH_EX = {
  "Zero row:  s³+2s²+s+2": { mode: "numeric", n: "3", c: ["1", "2", "1", "2"] },
  "Epsilon case:  s⁵+2s⁴+2s³+4s²+11s+10": { mode: "numeric", n: "5", c: ["1", "2", "2", "4", "11", "10"] },
  "Zero row + RHP:  s⁵+2s⁴+24s³+48s²−25s−50": { mode: "numeric", n: "5", c: ["1", "2", "24", "48", "-25", "-50"] },
  "Stable 4th order": { mode: "numeric", n: "4", c: ["1", "10", "35", "50", "24"] },
  "With gain:  s³+6s²+5s+K": { mode: "k", n: "3", c: ["1", "6", "5", "K"] },
};
const TF_EX = {
  "Locus: K(s+1)/(s³+6s²+8s)": { m: "1", n: "3", num: ["1", "1"], den: ["1", "6", "8", "0"], K: "5" },
  "Bode: 10/(s³+6s²+11s+6)": { m: "0", n: "3", num: ["10"], den: ["1", "6", "11", "6"], K: "1" },
  "Second order: 25/(s²+2s)": { m: "0", n: "2", num: ["25"], den: ["1", "2", "0"], K: "1" },
};

export default function App() {
  const [tab, setTab] = useState("routh");
  const [busy, setBusy] = useState(false);
  const [errs, setErrs] = useState({ routh: [], locus: [], bode: [] });
  const [bad, setBad] = useState({});
  const [out, setOut] = useState({ routh: null, locus: null, bode: null });
  const resRef = useRef(null);

  /* Routh inputs */
  const [rMode, setRMode] = useState("numeric");
  const [rN, setRN] = useState("4");
  const [rC, setRC] = useState(rev(["1", "2", "3", "4", "5"]));
  const [Kfrom, setKfrom] = useState("0");
  const [Kto, setKto] = useState("1000");
  /* shared TF inputs (Root Locus + Bode) */
  const [tm, setTm] = useState("1");
  const [tn, setTn] = useState("3");
  const [num, setNum] = useState(rev(["1", "1"]));
  const [den, setDen] = useState(rev(["1", "6", "8", "0"]));
  const [tK, setTK] = useState("5");

  const setErr = (k, list, badMap = {}) => { setErrs((e) => ({ ...e, [k]: list })); setBad(badMap); };
  const finish = (k, value) => setOut((o) => ({ ...o, [k]: value }));
  const scrollToResults = () => {
    if (window.matchMedia && window.matchMedia("(max-width: 960px)").matches && resRef.current) resRef.current.scrollIntoView({ behavior: "smooth", block: "start" });
  };
  const go = (k, fn) => { setBusy(true); setTimeout(() => { try { fn(); setTimeout(scrollToResults, 120); } catch (e) { setErr(k, [e.message]); } setBusy(false); }, 30); };
  const intIn = (s, lo, hi, name, b, key) => {
    let v; try { v = parseNum(s); } catch (e) { b[key] = e.message; return null; }
    if (!Number.isInteger(v) || v < lo || v > hi) { b[key] = `${name} must be an integer between ${lo} and ${hi}`; return null; }
    return v;
  };
  const readPoly = (vals, n, allowK, prefix, b) => {
    const out = [];
    for (let p = n; p >= 0; p--) {
      try { out.push(allowK ? parseExpr(vals[p] ?? "", true) : parseNum(vals[p] ?? "")); } catch (e) { b[`${prefix}${p}`] = `S^${p}: ${e.message}`; out.push(null); }
    }
    return out;
  };

  const runRouth = () => {
    const b = {};
    const n = intIn(rN, 1, 30, "Order n", b, "n");
    let coeffs = null;
    if (n !== null) coeffs = readPoly(rC, n, rMode === "k", "c", b);
    let kf, kt;
    if (rMode === "k") {
      try { kf = parseNum(Kfrom); } catch (e) { b.Kfrom = e.message; }
      try { kt = parseNum(Kto); } catch (e) { b.Kto = e.message; }
      if (kf !== undefined && kt !== undefined && !(kf < kt)) b.Kto = "K to must be larger than K from";
    }
    if (Object.keys(b).length) { setErr("routh", Object.values(b), b); return; }
    setErr("routh", [], {});
    go("routh", () => {
      if (rMode === "numeric") {
        if (!coeffs.some((c) => c !== 0)) throw new Error("All coefficients are zero.");
        const S = trimLead(coeffs);
        if (S.length < 2) throw new Error("The polynomial reduces to a constant: there are no poles to analyze.");
        finish("routh", { kind: "numeric", S, id: Math.random() });
      } else {
        const Sfn = (K) => coeffs.map((f) => f(K));
        finish("routh", { kind: "k", Sfn, ...analyzeK(Sfn, kf, kt), id: Math.random() });
      }
    });
  };
  const runTF = (kind) => {
    const b = {};
    const m = intIn(tm, 0, 20, "Numerator order m", b, "m");
    const n = intIn(tn, 1, 20, "Denominator order n", b, "n");
    if (m !== null && n !== null && m > n) b.m = "Improper TF: m must not exceed n";
    let nv = null, dv = null, K0 = null;
    if (!Object.keys(b).length) { nv = readPoly(num, m, false, "num", b); dv = readPoly(den, n, false, "den", b); }
    try { K0 = parseNum(tK); if (kind === "locus" && K0 < 0) b.K = "For the root locus, K must be ≥ 0"; if (kind === "bode" && K0 === 0) b.K = "For a Bode plot, K must be non-zero"; } catch (e) { b.K = e.message; }
    if (!Object.keys(b).length) {
      if (!nv.some((c) => c !== 0)) b.num0 = "The numerator is all zeros";
      else if (!dv.some((c) => c !== 0)) b.den0 = "The denominator is all zeros";
      else {
        const N = trimLead(nv), D = trimLead(dv);
        if (D.length < 2) b.n = "The denominator must be of order 1 or higher";
        else if (N.length > D.length) b.m = "Improper TF: numerator order exceeds denominator order";
      }
    }
    if (Object.keys(b).length) { setErr(kind, Object.values(b), b); return; }
    setErr(kind, [], {});
    go(kind, () => finish(kind, kind === "locus" ? { ...computeLocus(nv, dv, K0), id: Math.random() } : { ...computeBode(nv, dv, K0), id: Math.random() }));
  };

  const onN = (v, setter, arr, setArr) => { setter(v); const k = parseInt(v, 10); if (Number.isInteger(k) && k >= 0 && k <= 30) setArr(resize(arr, k + 1)); };
  const loadRouth = (key) => { const ex = ROUTH_EX[key]; if (!ex) return; setRMode(ex.mode); setRN(ex.n); setRC(rev(ex.c)); setBad({}); };
  const loadTF = (key) => { const ex = TF_EX[key]; if (!ex) return; setTm(ex.m); setTn(ex.n); setNum(rev(ex.num)); setDen(rev(ex.den)); setTK(ex.K); setBad({}); };

  const nR = parseInt(rN, 10), nT = parseInt(tn, 10), mT = parseInt(tm, 10);
  const ok = (v, lo, hi) => Number.isInteger(v) && v >= lo && v <= hi;
  const curErr = errs[tab];

  return (
    <div className="app">
      <header className="hero">
        <h1>Control Systems Suite</h1>
        <p>Routh stability · Root locus · Bode plot</p>
        <nav className="tabs">
          {[["routh", "Routh"], ["locus", "Root Locus"], ["bode", "Bode"]].map(([k, l]) => (<button key={k} className={tab === k ? "on" : ""} onClick={() => { setTab(k); setBad({}); }}>{l}</button>))}
        </nav>
      </header>

      <main className="layout">
        <section className="card inputs">
          {tab === "routh" && (
            <>
              <h3>Characteristic equation</h3>
              <div className="seg">
                <button className={rMode === "numeric" ? "on" : ""} onClick={() => setRMode("numeric")}>Numeric</button>
                <button className={rMode === "k" ? "on" : ""} onClick={() => setRMode("k")}>With gain K</button>
              </div>
              <select className="select" value="" onChange={(e) => loadRouth(e.target.value)}><option value="">Load an example…</option>{Object.keys(ROUTH_EX).map((k) => <option key={k}>{k}</option>)}</select>
              <Field label="Order n" value={rN} onChange={(v) => onN(v, setRN, rC, setRC)} bad={bad.n} />
              {ok(nR, 1, 30) && <CoeffInputs title={rMode === "k" ? "Coefficients (expressions in K allowed: 2K, K+2, 3*K^2)" : "Coefficients (numbers, 1/3, 2*pi, 1e3 …)"} vals={rC} setVals={setRC} n={nR} bad={bad} prefix="c" />}
              {rMode === "k" && (<div className="row2"><Field label="K from" value={Kfrom} onChange={setKfrom} bad={bad.Kfrom} /><Field label="K to" value={Kto} onChange={setKto} bad={bad.Kto} /></div>)}
              <button className="btn primary" disabled={busy} onClick={runRouth}>{busy ? "Computing…" : "▶ Run Routh"}</button>
            </>
          )}
          {(tab === "locus" || tab === "bode") && (
            <>
              <h3>Transfer function  K · N(S) / D(S)</h3>
              <select className="select" value="" onChange={(e) => loadTF(e.target.value)}><option value="">Load an example…</option>{Object.keys(TF_EX).map((k) => <option key={k}>{k}</option>)}</select>
              <div className="row2"><Field label="Numerator order m" value={tm} onChange={(v) => onN(v, setTm, num, setNum)} bad={bad.m} /><Field label="Denominator order n" value={tn} onChange={(v) => onN(v, setTn, den, setDen)} bad={bad.n} /></div>
              {ok(mT, 0, 20) && <CoeffInputs title="Numerator N(S)" vals={num} setVals={setNum} n={mT} bad={bad} prefix="num" />}
              {ok(nT, 1, 20) && <CoeffInputs title="Denominator D(S)" vals={den} setVals={setDen} n={nT} bad={bad} prefix="den" />}
              <Field label={tab === "locus" ? "Gain K (≥ 0)" : "Gain K (≠ 0)"} value={tK} onChange={setTK} bad={bad.K} />
              <button className="btn primary" disabled={busy} onClick={() => runTF(tab)}>{busy ? "Computing…" : tab === "locus" ? "▶ Run Root Locus" : "▶ Run Bode"}</button>
            </>
          )}
          {curErr.length > 0 && (<div className="alert"><b>Please fix:</b><ul>{curErr.slice(0, 5).map((e, i) => <li key={i}>{e}</li>)}</ul></div>)}
          <p className="muted small">Tip: inputs accept expressions like <code>1/3</code>, <code>2*pi</code>, <code>1e3</code>.</p>
        </section>

        <section className="results" ref={resRef}>
          {out[tab] === null && <div className="card empty"><h3>Ready</h3><p>Enter the system (or load an example) and press Run.</p></div>}
          {tab === "routh" && out.routh && (out.routh.kind === "numeric" ? <RouthNumericView key={out.routh.id} res={out.routh} /> : <RouthKView key={out.routh.id} res={out.routh} />)}
          {tab === "locus" && out.locus && <LocusView key={out.locus.id} res={out.locus} />}
          {tab === "bode" && out.bode && <BodeView key={out.bode.id} res={out.bode} />}
        </section>
      </main>

      <footer className="foot">© 2026 <b>Mohammed Nasr Eldin</b></footer>
    </div>
  );
}
