// engine v2: crossed-binomial test for rows of the 0/1/4 Lenstra-excess rule.
//
// Input program (stdin), produced by plan.py:
//   B <B>                          parent field degree (model F_2[x]/(P), P sparse)
//   H <h>                          conductor h = f(p)
//   R <R> <k> <l1> ... <lk>        radical degree and its distinct primes
//   T <t>                          cut: k = F_{2^t} subset K
//   N <n>                          number of K components
//   C <q> <ell> <deg> <nt> : <monos>   closure component (as ../ref/refengine)
//   A <exp> <nt> : <monos>         radicand factor: A *= (expr)^exp (exp may be < 0)
//   M <label> <nt> : <monos>       translate: test (m + z), m = expr in k
//   PS <np> <p1> ... <pnp>         primes p with f(p) = h to test
// Mathematics (see README.md): z^R = A, [K(z):K] = R; choose c in k, a in K with
// A = c a^R; H = k[V]/(V^R - c); N_{K(z)/H}(m + z) = V^D F_a(m/V) with F_a the
// characteristic polynomial of a over k; Euler test after a norm to F_{2^h}.
// Every structural fact the reduction uses is checked exactly; see CHECKS.
#include <NTL/GF2E.h>
#include <NTL/GF2EX.h>
#include <NTL/GF2X.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <NTL/vec_GF2.h>
#include <NTL/vec_GF2E.h>
#include <sys/resource.h>
#include <unistd.h>

#include <chrono>
#include <cmath>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>
using namespace NTL;
using namespace std;

// ---------------------------------------------------------------- utilities
static double wall() {
  return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();
}
static double cpu() {
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  return ru.ru_utime.tv_sec + 1e-6 * ru.ru_utime.tv_usec + ru.ru_stime.tv_sec +
         1e-6 * ru.ru_stime.tv_usec;
}
static void die(const string &m) {
  cout << "FATAL " << m << endl;
  cerr << "FATAL: " << m << endl;
  exit(2);
}
static map<string, long> CHECKS;
static void need(bool ok, const string &name) {
  if (!ok) die("check failed: " + name);
  CHECKS[name]++;
}
struct Phase {
  string name;
  double w, c;
  explicit Phase(const string &n) : name(n), w(wall()), c(cpu()) {}
  ~Phase() {
    fprintf(stdout, "TIME %-14s wall %9.3f cpu %9.3f\n", name.c_str(), wall() - w, cpu() - c);
    fflush(stdout);
  }
};

static vector<long> prime_factors(long n) {
  vector<long> out;
  for (long l = 2; l * l <= n; l++)
    if (n % l == 0) {
      out.push_back(l);
      while (n % l == 0) n /= l;
    }
  if (n > 1) out.push_back(n);
  return out;
}
static long v_ell(ZZ n, long ell) {
  long v = 0;
  while (!IsZero(n) && n % ell == 0) {
    n /= ell;
    v++;
  }
  return v;
}
static long powmod_long(long b, long e, long m) {
  ZZ r = PowerMod(ZZ(b % m), ZZ(e), ZZ(m));
  return conv<long>(r);
}
static long ord2_mod(long p) {  // multiplicative order of 2 mod odd p
  long o = p - 1;
  for (long q : prime_factors(p - 1))
    while (o % q == 0 && powmod_long(2, o / q, p) == 1) o /= q;
  return o;
}
static string to_hex(const GF2X &a) {
  long d = deg(a);
  if (d < 0) return "0";
  string s;
  for (long i = (d / 4) * 4; i >= 0; i -= 4) {
    int nib = 0;
    for (int b = 0; b < 4; b++)
      if (i + b <= d && IsOne(coeff(a, i + b))) nib |= 1 << b;
    s += "0123456789abcdef"[nib];
  }
  return s;
}

// ------------------------------------------------------- GF2X model helpers
static GF2X frob(const GF2X &a, long k, const GF2XModulus &F) {
  GF2X t = a;
  for (long i = 0; i < k; i++) SqrMod(t, t, F);
  return t;
}
// prod_{i<cnt} x^(2^(e i))
static GF2X relnorm(const GF2X &x, long e, long cnt, const GF2XModulus &F) {
  if (cnt <= 1) return x;
  long nb = NumBits(cnt);
  GF2X P = x;
  long j = 1;
  for (long b = nb - 2; b >= 0; b--) {
    GF2X t = frob(P, e * j, F);
    MulMod(P, P, t, F);
    j *= 2;
    if ((cnt >> b) & 1) {
      GF2X u = frob(P, e, F);
      MulMod(P, u, x, F);
      j += 1;
    }
  }
  need(j == cnt, "relnorm count");
  return P;
}
// sum_{i<cnt} x^(2^(e i))
static GF2X reltrace(const GF2X &x, long e, long cnt, const GF2XModulus &F) {
  if (cnt <= 1) return x;
  long nb = NumBits(cnt);
  GF2X T = x;
  long j = 1;
  for (long b = nb - 2; b >= 0; b--) {
    GF2X t = frob(T, e * j, F);
    add(T, T, t);
    j *= 2;
    if ((cnt >> b) & 1) {
      GF2X u = frob(T, e, F);
      add(T, u, x);
      j += 1;
    }
  }
  return T;
}
// exact degree test: a^(2^d) = a and a^(2^(d/l)) != a for primes l | d
static bool has_degree(const GF2X &a, long d, const GF2XModulus &F) {
  if (frob(a, d, F) != a) return false;
  for (long l : prime_factors(d))
    if (frob(a, d / l, F) == a) return false;
  return true;
}
// Rabin irreducibility test (deterministic, exact).
static bool rabin_irred(const GF2X &f) {
  long n = deg(f);
  if (n <= 0) return false;
  if (n == 1) return true;
  GF2XModulus Fm(f);
  vector<long> ps = prime_factors(n);
  map<long, long> at;  // n/q -> q
  for (long q : ps) at[n / q] = q;
  GF2X X;
  SetX(X);
  GF2X y = X;
  for (long i = 1; i <= n; i++) {
    SqrMod(y, y, Fm);
    if (at.count(i)) {
      GF2X d = y;
      add(d, d, X);
      GF2X gg = GCD(d, f);
      if (!IsOne(gg)) return false;
    }
  }
  return y == X;
}

static string CACHE_DIR = "cache";
static GF2X sparse_irred(long n) {
  GF2X P;
  vector<string> paths = {CACHE_DIR + "/irred_" + to_string(n) + ".txt",
                          "../ref/irred_" + to_string(n) + ".txt"};
  for (auto &pth : paths) {
    ifstream in(pth);
    if (in) {
      GF2X Q;
      in >> Q;
      if (deg(Q) == n && weight(Q) <= 5 && IsOne(ConstTerm(Q))) {
        P = Q;
        break;
      }
    }
  }
  if (deg(P) != n) {
    BuildSparseIrred(P, n);
    string fn = CACHE_DIR + "/irred_" + to_string(n) + ".txt";
    string tmp = fn + ".tmp." + to_string((long)getpid());
    {
      ofstream out(tmp);
      out << P;
    }
    rename(tmp.c_str(), fn.c_str());
  }
  return P;
}

// ------------------------------------------------------------ program input
typedef vector<vector<long>> Expr;
static Expr parse_expr(const string &s) {
  Expr e;
  vector<string> monos;
  string acc;
  for (char c : s) {
    if (c == ';') {
      monos.push_back(acc);
      acc.clear();
    } else
      acc += c;
  }
  if (!acc.empty() || !monos.empty()) monos.push_back(acc);
  for (auto &m : monos) {
    stringstream ms(m);
    string t;
    vector<long> mono;
    bool any = false;
    while (ms >> t) {
      any = true;
      if (t == "-") continue;
      mono.push_back(stol(t));
    }
    if (any) e.push_back(mono);
  }
  return e;
}
struct Comp {
  long q, ell, deg;
  Expr rhs;
  GF2X val;
};
static GF2X eval(const Expr &e, const vector<Comp> &cs, const GF2XModulus &F) {
  GF2X s;
  for (auto &mono : e) {
    GF2X t;
    set(t);
    for (long i : mono) MulMod(t, t, cs.at(i).val, F);
    add(s, s, t);
  }
  return s;
}

// --------------------------------------------------------- component roots
static GF2X as_root(const GF2X &a, long d, long B, const GF2XModulus &F) {
  for (int attempt = 0; attempt < 64; attempt++) {
    GF2X r;
    random(r, B);
    GF2X th = reltrace(r, d, B / d, F);  // in F_{2^d}
    GF2X tr = reltrace(th, 1, d, F);    // absolute trace
    if (!IsOne(tr)) continue;
    vector<GF2X> thp(d), ap(d);
    thp[0] = th;
    ap[0] = a;
    for (long i = 1; i < d; i++) {
      SqrMod(thp[i], thp[i - 1], F);
      SqrMod(ap[i], ap[i - 1], F);
    }
    GF2X suffix, y;
    for (long i = d - 2; i >= 0; i--) {
      add(suffix, suffix, thp[i + 1]);
      GF2X t2;
      MulMod(t2, suffix, ap[i], F);
      add(y, y, t2);
    }
    GF2X chk;
    SqrMod(chk, y, F);
    add(chk, chk, y);
    need(chk == a, "AS root y^2+y=a");
    return y;
  }
  die("no trace-one element found");
  return GF2X();
}

static uint64_t hashx(const GF2X &a) {
  uint64_t h = 1469598103934665603ULL;
  long n = a.xrep.length();
  for (long i = 0; i < n; i++) {
    h ^= (uint64_t)a.xrep[i];
    h *= 1099511628211ULL;
  }
  return h ^ (uint64_t)n;
}
// discrete log in the cyclic group of order ell generated by gl (BSGS)
struct BSGS {
  long ell, m;
  unordered_multimap<uint64_t, pair<long, GF2X>> baby;
  GF2X giant;  // gl^-m
  BSGS(const GF2X &gl, long ell_, const GF2XModulus &F) : ell(ell_) {
    m = (long)ceil(sqrt((double)ell));
    GF2X x;
    set(x);
    for (long j = 0; j < m; j++) {
      baby.insert({hashx(x), {j, x}});
      MulMod(x, x, gl, F);
    }
    InvMod(giant, x, F.f);
  }
  long log(const GF2X &h, const GF2XModulus &F) const {
    GF2X y = h;
    for (long i = 0; i <= m; i++) {
      auto rg = baby.equal_range(hashx(y));
      for (auto it = rg.first; it != rg.second; ++it)
        if (it->second.second == y) return (i * m + it->second.first) % ell;
      MulMod(y, y, giant, F);
    }
    return -1;
  }
};

// y with y^ell = a, where a in F_{2^(deg/ell)}, y of degree deg (| B).
// Exponent of deg/ell bits, then a Pohlig-Hellman correction in mu_{ell^v}.
static GF2X kummer_root(const GF2X &a, long ell, long dg, long B, const GF2XModulus &F) {
  need(dg % ell == 0 && B % dg == 0, "Kummer degrees divide");
  long ea = dg / ell;
  need(frob(a, ea, F) == a, "Kummer radicand lies in F_{2^(deg/ell)}");
  ZZ M = power2_ZZ(ea) - 1, Mp = M;
  while (Mp % ell == 0) Mp /= ell;
  GF2X y0;
  if (IsOne(Mp))
    set(y0);
  else
    y0 = PowerMod(a, InvMod(ZZ(ell) % Mp, Mp), F);
  GF2X ainv;
  InvMod(ainv, a, F.f);
  GF2X eps;
  MulMod(eps, PowerMod(y0, ell, F), ainv, F);
  if (!IsOne(eps)) {
    ZZ Nd = power2_ZZ(dg) - 1;
    long v = v_ell(Nd, ell);
    need(v >= 1, "ell | 2^deg - 1");
    ZZ L = power_ZZ(ell, v);
    // order of 2 mod ell^v divides dg
    long el = dg;
    for (long q : prime_factors(dg))
      while (el % q == 0 && PowerMod(ZZ(2), ZZ(el / q), L) == 1) el /= q;
    need(PowerMod(ZZ(2), ZZ(el), L) == 1, "ord_{ell^v}(2)");
    ZZ cof = (power2_ZZ(el) - 1) / L;
    GF2X g;
    for (int attempt = 0;; attempt++) {
      if (attempt > 200) die("no generator of the ell-Sylow subgroup");
      GF2X r;
      random(r, B);
      if (IsZero(r)) continue;
      GF2X y = relnorm(r, el, B / el, F);  // in F_{2^el}
      g = PowerMod(y, cof, F);
      if (!IsOne(PowerMod(g, L / ell, F))) break;
    }
    need(IsOne(PowerMod(g, L, F)), "Sylow generator order");
    GF2X target;
    InvMod(target, eps, F.f);
    GF2X gl = PowerMod(g, L / ell, F);
    BSGS bs(gl, ell, F);
    ZZ x(0), pw(1);
    for (long i = 0; i < v; i++) {
      GF2X gx = PowerMod(g, x, F), gxi;
      InvMod(gxi, gx, F.f);
      GF2X hh;
      MulMod(hh, target, gxi, F);
      hh = PowerMod(hh, power_ZZ(ell, v - 1 - i), F);
      long dgt = bs.log(hh, F);
      need(dgt >= 0, "Sylow dlog digit found");
      x += pw * dgt;
      pw *= ell;
    }
    need(x % ell == 0, "radicand is an ell-th power in F_{2^deg}");
    MulMod(y0, y0, PowerMod(g, x / ell, F), F);
  }
  need(PowerMod(y0, ell, F) == a, "Kummer root y^ell=a");
  return y0;
}

// ------------------------------------------------------------- the H ring
// H = k[V]/(V^R - c), k = GF2E (current modulus).  Elements: vec_GF2E length R.
struct HRing {
  long R, t;
  GF2E c;
  vector<GF2E> cpow;  // c^i, i < R
};
typedef vec_GF2E Hel;
static Hel H_zero(const HRing &H) {
  Hel z;
  z.SetLength(H.R);
  return z;
}
static Hel H_one(const HRing &H) {
  Hel z = H_zero(H);
  set(z[0]);
  return z;
}
static bool H_isone(const Hel &x) {
  if (!IsOne(x[0])) return false;
  for (long i = 1; i < x.length(); i++)
    if (!IsZero(x[i])) return false;
  return true;
}
static bool H_iszero(const Hel &x) {
  for (long i = 0; i < x.length(); i++)
    if (!IsZero(x[i])) return false;
  return true;
}
static void H_mul(Hel &z, const Hel &x, const Hel &y, const HRing &H) {
  GF2EX X, Y, Z;
  X.rep = x;
  X.normalize();
  Y.rep = y;
  Y.normalize();
  mul(Z, X, Y);
  long dz = deg(Z);
  Hel out = H_zero(H);
  for (long i = 0; i <= dz && i < H.R; i++) out[i] = Z.rep[i];
  for (long i = H.R; i <= dz; i++) {
    if (IsZero(Z.rep[i])) continue;
    GF2E s;
    mul(s, Z.rep[i], H.c);
    add(out[i - H.R], out[i - H.R], s);
  }
  z = out;
}
static void H_sqr(Hel &z, const Hel &x, const HRing &H) {
  Hel out = H_zero(H);
  for (long i = 0; i < H.R; i++) {
    if (IsZero(x[i])) continue;
    GF2E s;
    sqr(s, x[i]);
    long k = 2 * i;
    if (k >= H.R) {
      k -= H.R;
      mul(s, s, H.c);
    }
    out[k] = s;  // i -> 2i mod R is a bijection (R odd)
  }
  z = out;
}
static Hel H_pow(const Hel &x, const ZZ &e, const HRing &H) {
  if (IsZero(e)) return H_one(H);
  const long w = 5;
  vector<Hel> odd(1L << (w - 1));
  odd[0] = x;
  Hel x2;
  H_sqr(x2, x, H);
  for (long i = 1; i < (long)odd.size(); i++) H_mul(odd[i], odd[i - 1], x2, H);
  long nb = NumBits(e);
  Hel r = H_one(H);
  bool started = false;
  long i = nb - 1;
  while (i >= 0) {
    if (!bit(e, i)) {
      if (started) H_sqr(r, r, H);
      i--;
      continue;
    }
    long j = max(0L, i - w + 1);
    while (!bit(e, j)) j++;
    long val = 0;
    for (long k = i; k >= j; k--) val = 2 * val + bit(e, k);
    if (started)
      for (long k = i; k >= j; k--) H_sqr(r, r, H);
    if (started)
      H_mul(r, r, odd[val >> 1], H);
    else {
      r = odd[val >> 1];
      started = true;
    }
    i = j - 1;
  }
  return r;
}
// Frobenius x -> x^(2^e) on H.
struct FrobMap {
  long j, emod;
  vector<GF2E> M;
  bool comp;
  GF2XArgument arg;
};
static FrobMap frob_prepare(const HRing &H, long e) {
  FrobMap fm;
  fm.j = powmod_long(2, e, H.R);
  ZZ num = power2_ZZ(e) - fm.j;
  need(num % H.R == 0, "Frobenius exponent split");
  ZZ ex = (num / H.R) % (power2_ZZ(H.t) - 1);
  GF2E C = power(H.c, ex);  // V^(2^e) = C V^j
  fm.M.resize(H.R);
  GF2E Ci;
  set(Ci);
  for (long i = 0; i < H.R; i++) {
    long fl = (i * fm.j) / H.R;  // < j < R
    mul(fm.M[i], Ci, H.cpow[fl]);
    mul(Ci, Ci, C);
  }
  fm.emod = e % H.t;
  long thr = 2 * (long)sqrt((double)H.t) + 4;
  fm.comp = fm.emod > thr;
  if (fm.comp) {
    const GF2XModulus &gm = GF2E::modulus();
    GF2X X;
    SetX(X);
    GF2X psi = frob(X, fm.emod, gm);
    build(fm.arg, psi, gm, (long)sqrt((double)H.t) + 1);
  }
  return fm;
}
static void frob_apply(Hel &z, const Hel &x, const FrobMap &fm, const HRing &H) {
  Hel out = H_zero(H);
  const GF2XModulus &gm = GF2E::modulus();
  for (long i = 0; i < H.R; i++) {
    if (IsZero(x[i])) continue;
    GF2E a;
    if (fm.comp) {
      GF2X r;
      CompMod(r, rep(x[i]), fm.arg, gm);
      conv(a, r);
    } else {
      a = x[i];
      for (long k = 0; k < fm.emod; k++) sqr(a, a);
    }
    mul(a, a, fm.M[i]);
    out[(i * fm.j) % H.R] = a;
  }
  z = out;
}
// x^e by sliding windows, runs of squarings replaced by one Frobenius map
struct FrobCache {
  map<long, FrobMap> m;
  const FrobMap &get(const HRing &H, long len) {
    auto it = m.find(len);
    if (it != m.end()) return it->second;
    return m.emplace(len, frob_prepare(H, len)).first->second;
  }
};
static void H_frobpow(Hel &r, long len, const HRing &H, FrobCache &fc) {
  if (len <= 0) return;
  if (len == 1) {
    H_sqr(r, r, H);
    return;
  }
  Hel z;
  frob_apply(z, r, fc.get(H, len), H);
  r = z;
}
static Hel H_pow_frob(const Hel &x, const ZZ &e, const HRing &H, FrobCache &fc) {
  if (IsZero(e)) return H_one(H);
  const long w = 5;
  vector<Hel> odd(1L << (w - 1));
  odd[0] = x;
  Hel x2;
  H_sqr(x2, x, H);
  for (long i = 1; i < (long)odd.size(); i++) H_mul(odd[i], odd[i - 1], x2, H);
  long nb = NumBits(e);
  Hel r;
  bool started = false;
  long pend = 0;  // pending squarings
  long i = nb - 1;
  while (i >= 0) {
    if (!bit(e, i)) {
      if (started) pend++;
      i--;
      continue;
    }
    long j = max(0L, i - w + 1);
    while (!bit(e, j)) j++;
    long val = 0;
    for (long k = i; k >= j; k--) val = 2 * val + bit(e, k);
    if (started) {
      pend += i - j + 1;
      H_frobpow(r, pend, H, fc);
      pend = 0;
      H_mul(r, r, odd[val >> 1], H);
    } else {
      r = odd[val >> 1];
      started = true;
    }
    i = j - 1;
  }
  H_frobpow(r, pend, H, fc);
  return r;
}

// N_{H/F_{2^h}}(x) = prod_{i<cnt} x^(2^(h i)), cnt = Rt/h
static Hel H_norm(const Hel &x, long h, long cnt, const HRing &H) {
  if (cnt == 1) return x;
  long nb = NumBits(cnt);
  Hel P = x;
  long j = 1;
  FrobMap f1 = frob_prepare(H, h);
  for (long b = nb - 2; b >= 0; b--) {
    FrobMap fj = frob_prepare(H, h * j);
    Hel t;
    frob_apply(t, P, fj, H);
    H_mul(P, P, t, H);
    j *= 2;
    if ((cnt >> b) & 1) {
      Hel u;
      frob_apply(u, P, f1, H);
      H_mul(P, u, x, H);
      j += 1;
    }
  }
  need(j == cnt, "H norm count");
  return P;
}
static long gf2x_dot(const GF2X &a, const GF2X &b) {
  long n = min(a.xrep.length(), b.xrep.length());
  unsigned long acc = 0;
  for (long i = 0; i < n; i++) acc ^= (unsigned long)(a.xrep[i] & b.xrep[i]);
  return __builtin_parityl(acc);
}

// ----------------------------------------------------------------- main
int main(int argc, char **argv) {
  long direct_max = 0;  // also run the full Euler exponent when R*t <= this
  bool want_minpoly = false;
  long seed = 1;
  for (int i = 1; i < argc; i++) {
    string s = argv[i];
    if (s == "--direct" && i + 1 < argc) direct_max = atol(argv[++i]);
    else if (s == "--minpoly") want_minpoly = true;
    else if (s == "--seed" && i + 1 < argc) seed = atol(argv[++i]);
    else if (s == "--cache" && i + 1 < argc) CACHE_DIR = argv[++i];
    else die("unknown option " + s);
  }
  SetSeed(ZZ(seed));
  double W0 = wall(), C0 = cpu();

  long B = 0, h = 0, R = 0, t = 0, n = 0;
  vector<long> Rprimes, ps;
  vector<Comp> cs;
  vector<pair<long, Expr>> radicand;
  vector<pair<long, Expr>> trans;
  string line;
  while (getline(cin, line)) {
    if (line.empty()) continue;
    stringstream ss(line);
    string tag;
    ss >> tag;
    if (tag == "B") ss >> B;
    else if (tag == "H") ss >> h;
    else if (tag == "R") {
      long k;
      ss >> R >> k;
      Rprimes.resize(k);
      for (auto &x : Rprimes) ss >> x;
    } else if (tag == "T") ss >> t;
    else if (tag == "N") ss >> n;
    else if (tag == "C") {
      Comp c;
      long nt;
      string colon;
      ss >> c.q >> c.ell >> c.deg >> nt >> colon;
      string rest;
      getline(ss, rest);
      c.rhs = parse_expr(rest);
      if ((long)c.rhs.size() != nt) die("term count mismatch at q=" + to_string(c.q));
      cs.push_back(c);
    } else if (tag == "A") {
      long e, nt;
      string colon;
      ss >> e >> nt >> colon;
      string rest;
      getline(ss, rest);
      Expr ex = parse_expr(rest);
      if ((long)ex.size() != nt) die("radicand term count");
      radicand.push_back({e, ex});
    } else if (tag == "M") {
      long m, nt;
      string colon;
      ss >> m >> nt >> colon;
      string rest;
      getline(ss, rest);
      Expr ex = parse_expr(rest);
      if ((long)ex.size() != nt) die("translate term count");
      trans.push_back({m, ex});
    } else if (tag == "PS") {
      long np;
      ss >> np;
      ps.resize(np);
      for (auto &x : ps) ss >> x;
    } else
      die("bad tag " + tag);
  }
  if ((long)cs.size() != n) die("component count");
  long D = B / t;
  cout << "ROW h=" << h << " B=" << B << " R=" << R << " t=" << t << " D=" << D << " Rt=" << R * t
       << " ncomp=" << n << endl;

  // ---- cut / arithmetic validity (exact integer checks)
  {
    Phase ph("arith");
    need(B > 0 && t > 0 && B % t == 0, "cut t | B");
    need(R > 1 && R % 2 == 1, "R odd > 1");
    long rr = R;
    for (long l : Rprimes) {
      need(rr % l == 0, "listed prime divides R");
      while (rr % l == 0) rr /= l;
    }
    need(rr == 1, "R factorization complete");
    need(prime_factors(R) == Rprimes, "R primes listed exactly (sorted)");
    {
      long g = GCD(D, R);
      need(g == 1, "gcd(B/t, R) = 1 (K cap H = k)");
    }
    ZZ NB = power2_ZZ(B) - 1, Nt = power2_ZZ(t) - 1;
    for (long l : Rprimes) {
      need(powmod_long(2, t, l) == 1, "ell | 2^t - 1 (mu_ell in k)");
      need(v_ell(Nt, l) == v_ell(NB, l), "v_ell(2^t-1) = v_ell(2^B-1)");
    }
    need((R * t) % h == 0, "h | R t");
    for (long p : ps) {
      need(ord2_mod(p) == h, "f(p) = h");
    }
  }

  // ---- parent model K = F_2[x]/(P)
  GF2X P;
  {
    Phase ph("model");
    P = sparse_irred(B);
    need(deg(P) == B, "model degree");
    need(rabin_irred(P), "model modulus irreducible (Rabin)");
  }
  GF2XModulus F(P);
  {
    Phase ph("components");
    for (size_t i = 0; i < cs.size(); i++) {
      GF2X a = eval(cs[i].rhs, cs, F);
      need(!IsZero(a), "nonzero radicand/AS constant");
      need(B % cs[i].deg == 0, "component degree divides B");
      if (cs[i].ell == 2)
        cs[i].val = as_root(a, cs[i].deg, B, F);
      else
        cs[i].val = kummer_root(a, cs[i].ell, cs[i].deg, B, F);
      need(has_degree(cs[i].val, cs[i].deg, F), "component exact degree");
    }
  }
  // ---- radicand and translates
  GF2X A;
  set(A);
  for (auto &fa : radicand) {
    GF2X x = eval(fa.second, cs, F);
    need(!IsZero(x), "radicand factor nonzero");
    long e = fa.first;
    GF2X y = PowerMod(x, labs(e), F);
    if (e < 0) InvMod(y, y, P);
    MulMod(A, A, y, F);
  }
  vector<GF2X> mval;
  for (auto &tr : trans) {
    GF2X x = eval(tr.second, cs, F);
    need(frob(x, t, F) == x, "translate lies in k");
    mval.push_back(x);
  }

  // ---- crossing: A = c a^R, c in k
  GF2X c, a;
  {
    Phase ph("crossing");
    ZZ NB = power2_ZZ(B) - 1, Nt = power2_ZZ(t) - 1;
    ZZ G(1);
    for (long l : Rprimes) G *= power_ZZ(l, v_ell(NB, l));
    ZZ nn = NB / Nt;
    ZZ w = InvMod(nn % G, G);
    GF2X Nm = relnorm(A, t, D, F);  // N_{K/k}(A) = A^n
    c = PowerMod(Nm, w, F);
    need(frob(c, t, F) == c, "c in k");
    GF2X cinv;
    InvMod(cinv, c, P);
    GF2X quot;
    MulMod(quot, A, cinv, F);
    ZZ Np = NB / G;
    if (IsOne(Np))
      set(a);
    else
      a = PowerMod(quot, InvMod(ZZ(R) % Np, Np), F);
    need(PowerMod(a, R, F) == quot, "a^R = A/c");
  }
  // ---- characteristic polynomial of a over k
  vector<GF2X> fa(D + 1);  // F_a(T) = sum fa[j] T^j, monic
  {
    Phase ph("charpoly");
    vector<GF2X> conj(D);
    conj[0] = a;
    for (long i = 1; i < D; i++) conj[i] = frob(conj[i - 1], t, F);
    need(frob(conj[D - 1], t, F) == a, "a^(2^B) = a");
    // exact degree d of a over k: least divisor d of D with a^(2^(t d)) = a
    long d = D;
    for (long q : prime_factors(D))
      while (d % q == 0 && conj[(d / q) % D] == a) d /= q;
    need(d == D || conj[d % D] == a, "degree of a over k");
    for (long q : prime_factors(d)) need(conj[d / q] != a, "degree of a over k is exact");
    cout << "DEG_A_OVER_K " << d << " of " << D << endl;
    if (D == 1) {
      fa[0] = a;
      set(fa[1]);
    } else {
      // minimal polynomial P_a = prod_{i<d} (T + a^(2^(t i))); F_a = P_a^(D/d)
      GF2EPush push;
      GF2E::init(P);
      vec_GF2E roots;
      roots.SetLength(d);
      for (long i = 0; i < d; i++) conv(roots[i], conj[i]);
      GF2EX f;
      BuildFromRoots(f, roots);
      need(deg(f) == d && IsOne(LeadCoeff(f)), "min poly monic degree d");
      for (long j = 0; j <= d; j++)
        need(frob(rep(coeff(f, j)), t, F) == rep(coeff(f, j)), "min poly coefficient in k");
      {  // P_a(a) = 0 (Horner in K)
        GF2E av, acc;
        conv(av, a);
        for (long j = d; j >= 0; j--) acc = acc * av + coeff(f, j);
        need(IsZero(acc), "min poly annihilates a");
      }
      // a in k(..) of degree d, P_a in k[T] monic of degree d with P_a(a)=0 => P_a = minpoly
      if (d < D) {
        GF2EX fp = power(f, D / d);  // multiplicity correction
        f = fp;
      }
      need(deg(f) == D && IsOne(LeadCoeff(f)), "char poly monic degree D");
      for (long j = 0; j <= D; j++) fa[j] = rep(coeff(f, j));
    }
    for (long j = 0; j <= D; j++) need(frob(fa[j], t, F) == fa[j], "char poly coefficient in k");
  }

  // ---- k-model: F_2[y]/(g), y -> theta in k subset K
  GF2X g, theta;
  bool identity_map = (t == B);
  vector<GF2X> kc;  // mapped: c, fa[0..D], m-values
  {
    Phase ph("kmodel");
    vector<GF2X> toMap;
    toMap.push_back(c);
    for (long j = 0; j <= D; j++) toMap.push_back(fa[j]);
    for (auto &x : mval) toMap.push_back(x);
    if (identity_map) {
      g = P;
      SetX(theta);
      kc = toMap;
    } else {
      for (int attempt = 0;; attempt++) {
        if (attempt > 50) die("no generator of k found");
        GF2X r;
        random(r, B);
        theta = reltrace(r, t, D, F);
        need(frob(theta, t, F) == theta, "theta in k");
        MinPolyMod(g, theta, F, t);
        if (deg(g) == t) break;
      }
      need(rabin_irred(g), "k modulus irreducible (Rabin)");
      need(IsZero(CompMod(g, theta, F)), "g(theta) = 0");
      GF2XArgument targ;
      build(targ, theta, F, (long)sqrt((double)t) + 1);
      GF2XModulus gmod(g);
      vec_GF2 lam;
      GF2X invAs;
      auto Apoly = [&](const vec_GF2 &s) {
        GF2X S;
        for (long j = 0; j < t; j++)
          if (IsOne(s[j])) SetCoeff(S, t - 1 - j);
        GF2X prod;
        mul(prod, g, S);
        return RightShift(prod, t);
      };
      for (int attempt = 0;; attempt++) {
        if (attempt > 50) die("no generic functional found");
        random(lam, B);
        vec_GF2 s;
        ProjectPowers(s, lam, t, targ, F);
        GF2X As = Apoly(s);
        if (IsOne(GCD(As, g))) {
          InvMod(invAs, As % g, g);
          break;
        }
      }
      for (auto &x : toMap) {
        if (IsZero(x) || IsOne(x)) {
          kc.push_back(x);
          continue;
        }
        GF2XTransMultiplier tm;
        build(tm, x, F);
        vec_GF2 lx;
        UpdateMap(lx, lam, tm, F);
        vec_GF2 u;
        ProjectPowers(u, lx, t, targ, F);
        GF2X Q;
        MulMod(Q, Apoly(u), invAs, gmod);
        need(CompMod(Q, targ, F) == x, "k-map: Q(theta) = x");
        kc.push_back(Q);
      }
    }
  }

  // ---- H = k[V]/(V^R - c), Euler test via norm to F_{2^h}
  GF2E::init(g);
  HRing H;
  H.R = R;
  H.t = t;
  conv(H.c, kc[0]);
  H.cpow.resize(R);
  set(H.cpow[0]);
  for (long i = 1; i < R; i++) mul(H.cpow[i], H.cpow[i - 1], H.c);
  {
    Phase ph("binomial");
    need(!IsZero(H.c), "c nonzero");
    ZZ Nt = power2_ZZ(t) - 1;
    for (long l : Rprimes) need(!IsOne(power(H.c, Nt / l)), "c not an ell-th power in k (V^R-c irreducible)");
  }
  vector<GF2E> fk(D + 1);
  for (long j = 0; j <= D; j++) conv(fk[j], kc[1 + j]);
  need(IsOne(fk[D]), "mapped char poly monic");
  long cnt = R * t / h;
  ZZ e2 = (power2_ZZ(h) - 1);
  for (size_t ti = 0; ti < trans.size(); ti++) {
    GF2E m;
    conv(m, kc[2 + D + ti]);
    Hel Wv = H_zero(H);
    {
      GF2E mj;
      set(mj);
      for (long j = 0; j <= D; j++) {
        // coefficient f_j m^j of V^(D-j), reduced by V^R = c
        GF2E co;
        mul(co, fk[j], mj);
        long ex = D - j;
        GF2E red = power(H.c, ex / R);
        mul(co, co, red);
        add(Wv[ex % R], Wv[ex % R], co);
        mul(mj, mj, m);
      }
    }
    need(!H_iszero(Wv), "target norm nonzero");
    Hel Nh;
    {
      Phase ph("norm_to_h");
      Nh = H_norm(Wv, h, cnt, H);
      FrobMap fh = frob_prepare(H, h);
      Hel chk;
      frob_apply(chk, Nh, fh, H);
      need(chk == Nh, "norm lies in F_{2^h}");
    }
    if (want_minpoly) {
      Phase ph("minpoly");
      vector<GF2X> rho(R);
      for (long i = 0; i < R; i++) random(rho[i], t);
      vec_GF2 s;
      s.SetLength(2 * h);
      Hel x = H_one(H);
      for (long j = 0; j < 2 * h; j++) {
        long bitv = 0;
        for (long i = 0; i < R; i++) bitv ^= gf2x_dot(rep(x[i]), rho[i]);
        s[j] = bitv;
        H_mul(x, x, Nh, H);
      }
      GF2X mu;
      MinPolySeq(mu, s, h);
      // exact check: mu(N) = 0 (Horner) and mu irreducible with deg | h
      Hel acc = H_zero(H);
      for (long i = deg(mu); i >= 0; i--) {
        H_mul(acc, acc, Nh, H);
        if (IsOne(coeff(mu, i))) { GF2E one; set(one); add(acc[0], acc[0], one); }
      }
      need(H_iszero(acc), "minpoly annihilates norm");
      need(rabin_irred(mu) && h % deg(mu) == 0, "minpoly irreducible, degree | h");
      cout << "MINPOLY m=" << trans[ti].first << " deg=" << deg(mu) << " hex=" << to_hex(mu) << endl;
    }
    for (long p : ps) {
      need(e2 % p == 0, "p | 2^h - 1");
      // Cyclotomic split of the Euler exponent: with q1 < q2 the two smallest
      // primes of h, 2^h-1 = P1 P2 Rest, P1 = 2^(h/q1)-1,
      // P2 = (2^(h/q2)-1)/(2^(h/(q1 q2))-1) = sum_{i<q1} 2^(i h/(q1 q2)), and p | Rest.
      // N^((2^h-1)/p) = 1  <=>  Y := (N^(Rest/p))^P2 satisfies Y^(2^(h/q1)) = Y.
      vector<long> qs = prime_factors(h);
      long q1 = qs[0], q2 = qs.size() >= 2 ? qs[1] : 0;
      ZZ P1 = power2_ZZ(h / q1) - 1, P2(1);
      if (q2) P2 = (power2_ZZ(h / q2) - 1) / (power2_ZZ(h / (q1 * q2)) - 1);
      need(e2 % (P1 * P2) == 0, "cyclotomic split divides 2^h-1");
      ZZ rest = e2 / (P1 * P2);
      need(rest % p == 0, "p | Rest");
      bool power;
      Hel Y;
      {
        Phase ph("euler_exp");
        FrobCache fc;
        Hel Z = H_pow_frob(Nh, rest / p, H, fc);
        Y = Z;
        if (q2) {
          long step = h / (q1 * q2);
          for (long i = 1; i < q1; i++) {
            Hel u;
            frob_apply(u, Z, fc.get(H, i * step), H);
            H_mul(Y, Y, u, H);
          }
        }
        const FrobMap &fq = fc.get(H, h / q1);
        Hel fy;
        frob_apply(fy, Y, fq, H);
        power = (fy == Y);
        // phase sanity: X = Y^(P1) has order | p  <=>  (Y^p)^(2^(h/q1)) = Y^p
        Hel Yp = H_pow_frob(Y, ZZ(p), H, fc), fyp;
        frob_apply(fyp, Yp, fq, H);
        need(fyp == Yp, "Euler phase has order | p");
      }
      if (direct_max > 0 && R * t <= direct_max) {
        Phase ph("direct_euler");
        Hel X = H_pow(Nh, e2 / p, H);
        need(H_isone(X) == power, "plain h-bit Euler power agrees with cyclotomic split");
        ZZ exd = (power2_ZZ(R * t) - 1) / p;
        Hel Yd = H_pow(Wv, exd, H);
        need(Yd == X, "direct Euler power equals norm route");
      }
      cout << "p=" << p << " m=" << trans[ti].first << " pth_power=" << (power ? 1 : 0) << endl;
    }
  }
  long total = 0;
  for (auto &kv : CHECKS) {
    cout << "CHECK " << kv.first << " x" << kv.second << endl;
    total += kv.second;
  }
  printf("TOTAL wall %.3f cpu %.3f checks %ld\n", wall() - W0, cpu() - C0, total);
  return 0;
}
