// Single-model (V1) verification of the multi-component formulas.
// Everything lives in one explicit model F_E = GF2[x]/(P); the brute-force
// T_h = N_{E/h}(kappa_h) is compared *as an element* with the value produced
// by each reduction formula.  Usage: mcverify tower.txt tasks.txt
#include <NTL/GF2E.h>
#include <NTL/GF2EX.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <chrono>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <vector>
using namespace NTL;
using namespace std;

static double now() {
  return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();
}
long E, H;
vector<long> Qlist;
struct Comp { char type; long q, ell, c; vector<long> ids; };
vector<Comp> comps;
map<long, long> Dof;
map<long, GF2E> val;

ZZ pow2m1(long d) { ZZ z; power2(z, d); return z - 1; }
GF2E frob(const GF2E& x, long k) {
  k %= E; if (k < 0) k += E;
  GF2E y = x;
  for (long i = 0; i < k; i++) sqr(y, y);
  return y;
}
// N_{F_d / F_s}(x) for x in F_d (s | d), by Frobenius doubling.
GF2E relnorm(const GF2E& x, long d, long s) {
  long n = d / s;
  // binary method on n: maintain Nm = prod_{j<m} sigma^{s j}(x)
  GF2E acc; set(acc); long m = 0;  // acc = N_m
  GF2E base = x; long bm = 1;        // base = N_bm
  // process bits of n from least significant: acc = acc * sigma^{s m}(base) when bit set
  long nn = n;
  while (nn) {
    if (nn & 1) { acc = acc * frob(base, s * m); m += bm; }
    nn >>= 1;
    if (nn) { base = base * frob(base, s * bm); bm *= 2; }
  }
  return acc;
}
GF2E absnorm_pow(const GF2E& x, long d, long s) {  // same via exponent (check)
  ZZ ex = pow2m1(d) / pow2m1(s);
  GF2E y; power(y, x, ex); return y;
}
long vval(ZZ n, long l) { long v = 0; while (n % l == 0) { n /= l; v++; } return v; }
map<pair<long,long>, GF2E> sylow_gen;
GF2E sylowgen(long l, long v) {  // generator of the l^v-torsion of F_E^x
  auto key = make_pair(l, v);
  if (sylow_gen.count(key)) return sylow_gen[key];
  ZZ N = pow2m1(E); ZZ lv = power_ZZ(l, v);
  ZZ ex = N / lv;
  ZZ lv1 = power_ZZ(l, v - 1);
  for (;;) {
    GF2E w; random(w); if (IsZero(w)) continue;
    GF2E g; power(g, w, ex);
    GF2E t; power(t, g, lv1);
    if (!IsOne(t)) { sylow_gen[key] = g; return g; }
  }
}
// l-th root of a (a an l-th power in F_{Dc}), root returned in F_{Dc}.
GF2E kroot(const GF2E& a, long l, long Dc) {
  ZZ N = pow2m1(Dc);
  long v = vval(N, l);
  ZZ lv = power_ZZ(l, v);
  ZZ m = N / lv;
  if (v == 0) { ZZ u = InvMod(ZZ(l) % N, N); GF2E y; power(y, a, u); return y; }
  ZZ u = InvMod(ZZ(l) % m, m);
  GF2E y0; power(y0, a, u);
  GF2E s; power(s, y0, l); s = s / a;  // s in S (order | l^v)
  GF2E g = sylowgen(l, v);
  // dlog of sinv = s^{-1} base g
  GF2E sinv = inv(s);
  GF2E gamma; power(gamma, g, power_ZZ(l, v - 1));  // order l
  vector<GF2E> gpow(l); set(gpow[0]); for (long i = 1; i < l; i++) gpow[i] = gpow[i-1] * gamma;
  ZZ k(0); ZZ lpow(1);
  for (long i = 0; i < v; i++) {
    GF2E t; power(t, g, k); t = sinv / t;  // sinv * g^{-k}
    GF2E tt; power(tt, t, power_ZZ(l, v - 1 - i));
    long dgt = -1; for (long j = 0; j < l; j++) if (gpow[j] == tt) { dgt = j; break; }
    if (dgt < 0) { cerr << "dlog fail\n"; exit(1); }
    k += lpow * dgt; lpow *= l;
  }
  if (k % l != 0) { cerr << "not an l-th power\n"; exit(1); }
  GF2E t; power(t, g, k / l);
  GF2E y = y0 * t;
  GF2E chk; power(chk, y, l);
  if (chk != a) { cerr << "kroot check failed\n"; exit(1); }
  return y;
}
GF2E asroot(const GF2E& a, long d) {  // y^2+y=a with y in F_d (d even)
  ZZ ex = pow2m1(E) / pow2m1(d);
  GF2E delta;
  for (;;) {
    GF2E w; random(w); if (IsZero(w)) continue;
    power(delta, w, ex);  // random-ish element of F_d
    GF2E tr; clear(tr); GF2E t = delta;
    for (long i = 0; i < d; i++) { tr += t; sqr(t, t); }
    if (IsOne(tr)) break;
  }
  // y = sum_{i=1}^{d-1} (sum_{j<i} delta^{2^j}) a^{2^i}
  GF2E y; clear(y); GF2E part; clear(part); GF2E dpow = delta; GF2E apow = a;
  for (long i = 1; i < d; i++) { part += dpow; sqr(dpow, dpow); sqr(apow, apow); y += part * apow; }
  if (y * y + y != a) { y = y; cerr << "asroot formula check failed\n"; exit(1); }
  return y;
}
GF2E sumids(const vector<long>& ids, long c) {
  GF2E s; clear(s); if (c) set(s);
  for (long id : ids) s += val.at(id);
  return s;
}
// min poly of x over F_s (x in F_d): prod_{j<d/s} (X - sigma^{sj} x)
GF2EX subminpoly(const GF2E& x, long d, long s) {
  GF2EX P; set(P); GF2E c = x; long n = d / s;
  for (long j = 0; j < n; j++) {
    GF2EX lin; SetCoeff(lin, 1); SetCoeff(lin, 0, c);  // X + c
    P = P * lin; c = frob(c, s);
  }
  return P;
}
GF2E evalpoly(const GF2EX& P, const GF2E& x) { GF2E r; eval(r, P, x); return r; }
GF2EX shiftpoly(const GF2EX& P, const GF2E& z) {  // P(X+z)
  GF2EX lin; SetCoeff(lin, 1); SetCoeff(lin, 0, z);
  GF2EX R; clear(R);
  for (long i = deg(P); i >= 0; i--) { R = R * lin; R += coeff(P, i); }
  return R;
}
GF2EX scalepoly(const GF2EX& P, const GF2E& lam) {  // P(lam X)
  GF2EX R; GF2E lp; set(lp);
  for (long i = 0; i <= deg(P); i++) { SetCoeff(R, i, coeff(P, i) * lp); lp *= lam; }
  return R;
}
bool inSub(const GF2E& x, long s) { return frob(x, s) == x; }
long ordtwo(long p) { long o = 1; long t = 2 % p; while (t != 1) { t = (t * 2) % p; o++; } return o; }

int main(int argc, char** argv) {
  SetSeed(ZZ(12345));
  ifstream tf(argv[1]);
  string line;
  while (getline(tf, line)) {
    istringstream is(line); string tag; is >> tag;
    if (tag == "E") { string hh; is >> E >> hh >> H; }
    else if (tag == "Q") { long q; while (is >> q) Qlist.push_back(q); }
    else if (tag == "A") { Comp c; c.type = 'A'; long n; is >> c.q >> n; c.ids.resize(n); for (auto& x : c.ids) is >> x; comps.push_back(c); }
    else if (tag == "K") { Comp c; c.type = 'K'; long n; is >> c.q >> c.ell >> c.c >> n; c.ids.resize(n); for (auto& x : c.ids) is >> x; comps.push_back(c); }
    else if (tag == "D") { string tok; while (is >> tok) { auto k = tok.find(':'); Dof[stol(tok.substr(0, k))] = stol(tok.substr(k + 1)); } }
  }
  double t0 = now();
  GF2X P; BuildSparseIrred(P, E); GF2E::init(P);
  cout << "model E=" << E << " h=" << H << " weight(P)=" << weight(P) << endl;
  for (auto& c : comps) {
    if (c.type == 'A') {
      GF2E a; set(a); for (long id : c.ids) a *= val.at(id);
      val[c.q] = asroot(a, c.q);
    } else {
      GF2E a = sumids(c.ids, c.c);
      val[c.q] = kroot(a, c.ell, Dof.at(c.q));
    }
    if (!inSub(val[c.q], Dof.at(c.q))) { cerr << "component not in its field " << c.q << endl; exit(1); }
  }
  cout << "tower built " << now() - t0 << "s" << endl;
  GF2E kappa; clear(kappa); for (long q : Qlist) kappa += val[q];
  double t1 = now();
  GF2E T = relnorm(kappa, E, H);
  cout << "T_h computed " << now() - t1 << "s" << endl;
  if (!inSub(T, H)) { cerr << "T not in F_h\n"; exit(1); }
  GF2X mp; MinPolyMod(mp, rep(T), GF2XModulus(P), H);
  cout << "minpoly(T_h) deg " << deg(mp) << " weight " << weight(mp) << endl;
  cout << "minpoly_exps"; for (long i = 0; i <= deg(mp); i++) if (IsOne(coeff(mp, i))) cout << " " << i; cout << endl;

  ifstream task(argv[2]);
  while (getline(task, line)) {
    istringstream is(line); string tag; is >> tag;
    if (tag == "euler") {  // euler p1 p2 ...
      long p; while (is >> p) {
        ZZ ex = pow2m1(H) / p; GF2E u; power(u, T, ex);
        cout << "euler p=" << p << " f(p)=" << ordtwo(p) << " kappa_is_pth_power=" << (IsOne(u) ? 1 : 0) << endl;
      }
    } else if (tag == "res") {  // res e : shared-subfield resultant at test field e
      long e; is >> e;
      GF2E z; clear(z); vector<long> bigs;
      for (long q : Qlist) { long s = GCD(Dof[q], e); if (Dof[q] / s == 1) z += val[q]; else bigs.push_back(q); }
      double ts = now(); GF2E N;
      if (bigs.empty()) N = z;
      else if (bigs.size() == 1) { long q = bigs[0]; N = evalpoly(subminpoly(val[q], Dof[q], GCD(Dof[q], e)), z); }
      else if (bigs.size() == 2) {
        GF2EX P1 = subminpoly(val[bigs[0]], Dof[bigs[0]], GCD(Dof[bigs[0]], e));
        GF2EX P2 = subminpoly(val[bigs[1]], Dof[bigs[1]], GCD(Dof[bigs[1]], e));
        resultant(N, P1, shiftpoly(P2, z));
      } else {
        GF2EX P2 = subminpoly(val[bigs[1]], Dof[bigs[1]], GCD(Dof[bigs[1]], e));
        GF2EX P3 = subminpoly(val[bigs[2]], Dof[bigs[2]], GCD(Dof[bigs[2]], e));
        long s1 = GCD(Dof[bigs[0]], e); long n1 = Dof[bigs[0]] / s1; set(N);
        GF2E x1 = val[bigs[0]];
        for (long j = 0; j < n1; j++) { GF2E rr; resultant(rr, P2, shiftpoly(P3, z + x1)); N *= rr; x1 = frob(x1, e); }
      }
      bool inE = inSub(N, e);
      GF2E Nd = relnorm(kappa, E, e);
      GF2E T1 = relnorm(N, e, H);
      cout << "res e=" << e << " bigs=" << bigs.size() << " N in F_e=" << inE << " N==N_{E/e}(kappa): " << (N == Nd)
           << "  T==T_h: " << (T1 == T) << "  (" << now() - ts << "s)" << endl;
    } else if (tag == "cross") {  // cross q ex : crossing of component q (R=r^a), test field ex
      long q, ex; is >> q >> ex;
      Comp* cr = nullptr; for (auto& c : comps) if (c.q == q) cr = &c;
      // find prime r and a, and base alpha_r
      long r = cr->ell; long R = q; long a_exp = 0; { long t = q; while (t > 1) { t /= r; a_exp++; } }
      const Comp* base = nullptr; for (auto& c : comps) if (c.q == r) base = &c;
      GF2E alpha = sumids(base->ids, base->c);
      long b = Dof[r] / r;  // d(alpha_r) = b_r
      long fr = ordtwo(r);
      double ts = now();
      GF2E Nb = relnorm(alpha, b, fr);
      ZZ M = pow2m1(b) / pow2m1(fr);
      ZZ RZ(R);
      ZZ w = InvMod(M % RZ, RZ);
      GF2E c; power(c, Nb, w);
      if (!inSub(c, fr)) { cerr << "c not in F_fr\n"; exit(1); }
      GF2E ratio = alpha / c;
      GF2E aroot = kroot(ratio, R, b);  // R-th root in F_b
      GF2E y = val[q];
      GF2E v = y / aroot;
      GF2E vR; power(vR, v, R);
      bool vok = (vR == c) && inSub(v, R * fr);
      long t = GCD(b, ex); long n1 = b / t;
      GF2EX fa = subminpoly(aroot, b, t);
      GF2E z = kappa - y;
      GF2E vn; power(vn, v, n1);
      GF2E W = vn * evalpoly(fa, z / v);
      GF2E Wd = relnorm(kappa, E, ex);
      GF2E T1 = relnorm(W, ex, H);
      cout << "cross q=" << q << " b=" << b << " f(r)=" << fr << " t=" << t << " n'=" << n1 << " ex=" << ex
           << " v^R=c & v in F_{R f(r)}: " << vok << "  W==N_{E/ex}(kappa): " << (W == Wd) << "  T==T_h: " << (T1 == T)
           << "  (" << now() - ts << "s)" << endl;
    } else if (tag == "cross2") {  // cross2 q1 q2 ex : both big components crossed (a=1 each)
      long q1, q2, ex; is >> q1 >> q2 >> ex;
      long qs[2] = {q1, q2}; GF2E av[2], vv[2]; GF2EX fv[2]; long nv[2]; GF2E ysum; clear(ysum);
      double ts = now();
      for (int i = 0; i < 2; i++) {
        long r = qs[i];
        const Comp* base = nullptr; for (auto& c : comps) if (c.q == r) base = &c;
        GF2E alpha = sumids(base->ids, base->c);
        long b = Dof[r] / r; long fr = ordtwo(r);
        GF2E Nb = relnorm(alpha, b, fr);
        ZZ M = pow2m1(b) / pow2m1(fr);
        ZZ w = InvMod(M % ZZ(r), ZZ(r));
        GF2E c; power(c, Nb, w);
        av[i] = kroot(alpha / c, r, b);
        vv[i] = val[r] / av[i];
        long t = GCD(b, ex); nv[i] = b / t;
        fv[i] = subminpoly(av[i], b, t);
        ysum += val[r];
      }
      GF2E z = kappa - ysum;
      // N = prod_{i,j} (z + a1i v1 + a2j v2) = Res_X(f_a1(X), v2^{n2} f_a2((z + v1 X)/v2))
      GF2EX lin; SetCoeff(lin, 1, vv[0] / vv[1]); SetCoeff(lin, 0, z / vv[1]);
      GF2EX G; clear(G);
      for (long i = deg(fv[1]); i >= 0; i--) { G = G * lin; G += coeff(fv[1], i); }
      GF2E v2n; power(v2n, vv[1], nv[1]); G = G * v2n;
      GF2E N; resultant(N, fv[0], G);
      GF2E Wd = relnorm(kappa, E, ex);
      GF2E T1 = relnorm(N, ex, H);
      cout << "cross2 " << q1 << "," << q2 << " n'=(" << nv[0] << "," << nv[1] << ") ex=" << ex
           << "  N==N_{E/ex}(kappa): " << (N == Wd) << "  T==T_h: " << (T1 == T) << "  (" << now() - ts << "s)" << endl;
    } else if (tag == "phase") {  // phase k : replace small part z by sigma^k(z) -> should break T unless k = 0 mod g
      long k; is >> k; long big; is >> big;
      GF2E y = val[big]; GF2E z = kappa - y;
      GF2E kap2 = frob(z, k) + y;
      GF2E T2 = relnorm(kap2, E, H);
      GF2X mp2; MinPolyMod(mp2, rep(T2), GF2XModulus(P), H);
      cout << "phase shift k=" << k << " on small part: minpoly equal: " << (mp2 == mp) << " element equal: " << (T2 == T) << endl;
    }
  }
  cout << "total " << now() - t0 << "s" << endl;
}
