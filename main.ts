import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DR = [[0, -1, 'u'], [0, 1, 'd'], [-1, 0, 'l'], [1, 0, 'r']];
const BUD = 250000;
function nb(c, w, h) {
const x = c % w, y = (c / w) | 0, o = [];
if (y > 0) o.push([c - w, 0]);
if (y < h - 1) o.push([c + w, 1]);
if (x > 0) o.push([c - 1, 2]);
if (x < w - 1) o.push([c + 1, 3]);
return o;
}
function Wk(w, h, ok, blk, a, b) {
if (a === b) return '';
const n = w * h, par = new Int32Array(n).fill(-1), pd = new Int8Array(n);
const q = [a]; par[a] = a;
for (let k = 0; k < q.length; k++)
for (const [m, d] of nb(q[k], w, h)) {
if (!ok[m] || blk[m] || par[m] >= 0) continue;
par[m] = q[k]; pd[m] = d;
if (m === b) { let s = '', c = m; while (c !== a) { s = DR[pd[c]][2] + s; c = par[c]; } return s; }
q.push(m);
}
return null;
}
function Rg(w, h, ok, blk, a) {
const n = w * h, sn = new Uint8Array(n);
const q = [a]; sn[a] = 1; let mn = a;
for (let k = 0; k < q.length; k++) {
const c = q[k]; if (c < mn) mn = c;
for (const [m] of nb(c, w, h)) if (ok[m] && !blk[m] && !sn[m]) { sn[m] = 1; q.push(m); }
}
return { mn, sn };
}
function hl(a, b) { return a[0] < b[0] || (a[0] === b[0] && (a[1] > b[1] || (a[1] === b[1] && a[2] < b[2]))); }
function hp(H, e) {
let i = H.length; H.push(e);
while (i > 0) { const p = (i - 1) >> 1; if (!hl(H[i], H[p])) break; const t = H[i]; H[i] = H[p]; H[p] = t; i = p; }
}
function hq(H) {
const t = H[0], l = H.pop();
if (H.length) {
H[0] = l;
for (let i = 0; ;) {
let c = 2 * i + 1;
if (c >= H.length) break;
if (c + 1 < H.length && hl(H[c + 1], H[c])) c++;
if (!hl(H[c], H[i])) break;
const x = H[i]; H[i] = H[c]; H[c] = x; i = c;
}
}
return t;
}
function SR(w, h, ok, pok, gl, boxes0, hs) {
const n = w * h, m = gl.length;
const gs = new Uint8Array(n);
for (const g of gl) gs[g] = 1;
const Lv = new Uint8Array(n);
const lq = gl.slice();
for (const g of gl) Lv[g] = 1;
for (let k = 0; k < lq.length; k++) {
const b = lq[k];
for (let d = 0; d < 4; d++) {
const p = b - DR[d][1] * w - DR[d][0], q = b - 2 * DR[d][1] * w - 2 * DR[d][0];
if (ok[p] && pok[q] && !Lv[p]) { Lv[p] = 1; lq.push(p); }
}
}
for (const b of boxes0) if (!Lv[b]) return null;
const dg = gl.map(g => {
const di = new Int32Array(n).fill(-1), q = [g]; di[g] = 0;
for (let k = 0; k < q.length; k++)
for (const [mm] of nb(q[k], w, h)) if (ok[mm] && di[mm] < 0) { di[mm] = di[q[k]] + 1; q.push(mm); }
return di;
});
const pm = [];
(function gen(p, u) {
if (p.length === m) { pm.push(p.slice()); return; }
for (let j = 0; j < m; j++) if (!u[j]) { u[j] = 1; p.push(j); gen(p, u); p.pop(); u[j] = 0; }
})([], new Uint8Array(m));
const hc = new Map();
function He(bx) {
const key = bx.join(',');
const c = hc.get(key);
if (c !== undefined) return c;
let Be = Infinity;
for (const p of pm) {
let s = 0;
for (let i = 0; i < m; i++) { const d = dg[p[i]][bx[i]]; if (d < 0) { s = Infinity; break; } s += d; }
if (s < Be) Be = s;
}
hc.set(key, Be);
return Be;
}
function Fz(bx) {
const fr = new Uint8Array(n);
let ch = true;
while (ch) {
ch = false;
for (const b of bx) {
if (fr[b]) continue;
let all = true;
for (let d = 0; d < 4; d++) {
const t = b + DR[d][1] * w + DR[d][0], p = b - DR[d][1] * w - DR[d][0];
if ((!ok[t] || fr[t]) || (!pok[p] || fr[p])) continue;
all = false; break;
}
if (all) { fr[b] = 1; ch = true; }
}
}
for (const b of bx) if (fr[b] && !gs[b]) return true;
return false;
}
function Sh(gd) {
const b0 = boxes0.slice().sort((a, b) => a - b);
if (Fz(b0)) return null;
const blk0 = new Uint8Array(n);
for (const b of b0) blk0[b] = 1;
const r0 = Rg(w, h, pok, blk0, hs);
const S = [{ b: b0, p: hs, g: 0, par: -1, pb: -1, pd: -1, k: b0.join(',') + '|' + r0.mn }];
const Be = new Map([[S[0].k, 0]]);
const H = [];
const h0 = He(b0);
if (!isFinite(h0)) return null;
hp(H, [h0, 0, 0]);
let ex = 0;
function recon(id) {
const ps = [];
for (let c = id; c > 0; c = S[c].par) ps.push([S[c].pb, S[c].pd]);
ps.reverse();
let mv = '', cu = hs;
const occ = new Uint8Array(n);
for (const b of boxes0) occ[b] = 1;
for (const [b, d] of ps) {
const pu = b - DR[d][1] * w - DR[d][0];
const w1 = Wk(w, h, pok, occ, cu, pu);
if (w1 === null) return null;
mv += w1 + DR[d][2];
occ[b] = 0; occ[b + DR[d][1] * w + DR[d][0]] = 1;
cu = b;
}
const w2 = Wk(w, h, pok, occ, cu, hs);
if (w2 === null) return null;
return mv + w2;
}
while (H.length) {
const [, g, id] = hq(H);
const st = S[id];
if (Be.get(st.k) !== id) continue;
const blk = new Uint8Array(n);
for (const b of st.b) blk[b] = 1;
const rg = Rg(w, h, pok, blk, st.p);
if (st.b.every(b => gs[b]) && rg.sn[hs]) return recon(id);
if (++ex > BUD) return null;
for (let i = 0; i < st.b.length; i++) {
const b = st.b[i];
for (let d = 0; d < 4; d++) {
const t = b + DR[d][1] * w + DR[d][0], p = b - DR[d][1] * w - DR[d][0];
if (!ok[t] || blk[t] || !rg.sn[p]) continue;
const nb2 = st.b.slice(); nb2[i] = t; nb2.sort((a, c) => a - c);
if (!Lv[t] || Fz(nb2)) continue;
const hh = He(nb2);
if (!isFinite(hh)) continue;
const bk2 = new Uint8Array(n);
for (const x of nb2) bk2[x] = 1;
const r2 = Rg(w, h, pok, bk2, b);
const k2 = nb2.join(',') + '|' + r2.mn;
const g2 = g + 1;
const old = Be.get(k2);
if (old !== undefined && S[old].g <= g2) continue;
const nid = S.length;
S.push({ b: nb2, p: b, g: g2, par: id, pb: b, pd: d, k: k2 });
Be.set(k2, nid);
hp(H, [gd ? hh : g2 + hh, g2, nid]);
}
}
}
return null;
}
return Sh(false) ?? Sh(true);
}
function SL(t) {
const rows = t.split('\n').filter(r => r.length);
const w = Math.max(...rows.map(r => r.length));
const h = rows.length, n = w * h;
const wa = new Uint8Array(n).fill(1);
const go = new Uint8Array(n);
const bx = []; let pl = 0;
rows.forEach((r, y) => {
for (let x = 0; x < w; x++) {
const c = r[x] || '#', i = y * w + x;
if (c !== '#') wa[i] = 0;
if (c === '.' || c === '*' || c === '+') go[i] = 1;
if (c === '$' || c === '*') bx.push(i);
if (c === '@' || c === '+') pl = i;
}
});
const hy = (pl / w) | 0;
const ha = new Uint8Array(n);
for (let x = 0; x < w; x++) if (!wa[hy * w + x]) ha[hy * w + x] = 1;
const sn = new Uint8Array(n);
const rm = [];
for (let i = 0; i < n; i++) {
if (wa[i] || ha[i] || sn[i]) continue;
const ce = [], q = [i]; sn[i] = 1;
for (let k = 0; k < q.length; k++) {
const c = q[k]; ce.push(c);
for (const [m] of nb(c, w, h)) if (!wa[m] && !ha[m] && !sn[m]) { sn[m] = 1; q.push(m); }
}
const ok = new Uint8Array(n);
for (const c of ce) ok[c] = 1;
let dt = -1;
for (const c of ce) {
let f = false;
for (const [m] of nb(c, w, h)) if (ha[m]) { dt = c; f = true; break; }
if (f) break;
}
if (dt < 0) return '';
const rb = bx.filter(b => ok[b]);
if (rb.length === 0) continue;
const rg2 = [];
for (let j = 0; j < n; j++) if (go[j] && ok[j]) rg2.push(j);
if (rb.length !== rg2.length) return '';
rm.push({ ok, dt, bx: rb, gl: rg2 });
}
let cnt = 0;
for (const r of rm) cnt += r.bx.length;
if (cnt !== bx.length) return '';
rm.sort((a, b) => a.dt - b.dt);
let mv = '', cu = pl;
for (const r of rm) {
let hs = -1;
for (const [m] of nb(r.dt, w, h)) if (ha[m]) { hs = m; break; }
const pok = new Uint8Array(n);
for (let i = 0; i < n; i++) if (r.ok[i]) pok[i] = 1;
pok[hs] = 1;
const wok = new Uint8Array(n);
for (let i = 0; i < n; i++) if (ha[i]) wok[i] = 1;
wok[r.dt] = 1; wok[cu] = 1; wok[hs] = 1;
const w1 = Wk(w, h, wok, new Uint8Array(n), cu, hs);
if (w1 === null) return '';
mv += w1;
const rs = SR(w, h, r.ok, pok, r.gl, r.bx, hs);
if (rs === null) return '';
mv += rs;
cu = hs;
}
return mv;
}
for (const id of readdirSync(I).sort()) {
const mv = SL(readFileSync(join(I, id, 'level.txt'), 'utf8'));
mkdirSync(join(O, id), { recursive: true });
writeFileSync(join(O, id, 'solution.txt'), `${mv}\n`);
}
