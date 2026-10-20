// Reference engine for Lenstra excess rows: one explicit model F_2[x]/(P) of
// F_{2^E}; components embedded in dependency order by exact root extraction;
// Euler test for each translate.  Slow but simple; every root is checked.
//
// Input program (stdin), produced by rowprog.py:
//   E <E>
//   P <p>
//   N <n>
//   C <q> <ell> <deg> <nterms> : <mono> ; <mono> ...   (mono = idx idx ... or '-')
//   T <n> : idx ; idx ...
//   M <m> <nterms> : <mono> ; ...
// ell = 2 means y^2 + y = rhs, odd ell means y^ell = rhs.
#include <NTL/GF2X.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <chrono>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <unistd.h>
#include <cstdio>
using namespace NTL;
using namespace std;

static double now() {
  return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();
}
static void die(const string &m) { cerr << "FATAL: " << m << endl; exit(2); }

typedef vector<vector<long>> Expr;  // sum of monomials (products of components)

static Expr parse_expr(const string &s) {
  Expr e;
  stringstream ss(s);
  string tok, cur;
  vector<string> monos;
  string acc;
  for (char c : s) {
    if (c == ';') { monos.push_back(acc); acc.clear(); } else acc += c;
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

struct Comp { long q, ell, deg; Expr rhs; GF2X val; };

static GF2X eval(const Expr &e, const vector<Comp> &cs, const GF2XModulus &F) {
  GF2X s;
  for (auto &mono : e) {
    GF2X t; set(t);
    for (long i : mono) MulMod(t, t, cs.at(i).val, F);
    add(s, s, t);
  }
  return s;
}

// x^(2^k) by repeated squaring
static GF2X frob(const GF2X &a, long k, const GF2XModulus &F) {
  GF2X t = a;
  for (long i = 0; i < k; i++) SqrMod(t, t, F);
  return t;
}

// exact degree of a over F_2 given the claimed degree d (d | E): a^(2^d)=a and
// a^(2^(d/l)) != a for every prime l | d.
static bool has_degree(const GF2X &a, long d, const GF2XModulus &F) {
  if (frob(a, d, F) != a) return false;
  long x = d;
  vector<long> primes;
  for (long l = 2; l * l <= x; l++)
    if (x % l == 0) { primes.push_back(l); while (x % l == 0) x /= l; }
  if (x > 1) primes.push_back(x);
  for (long l : primes)
    if (frob(a, d / l, F) == a) return false;
  return true;
}

// Artin-Schreier root in the subfield of degree d = 2^k: y^2 + y = a.
static GF2X as_root(const GF2X &a, long d, long E, const GF2XModulus &F) {
  // theta in F_{2^d} with absolute trace 1: relative trace of random elements.
  for (int attempt = 0; attempt < 64; attempt++) {
    GF2X r; random(r, E);
    GF2X th, t = r;
    for (long j = 0; j < E / d; j++) { add(th, th, t); t = frob(t, d, F); }
    GF2X tr, u = th;
    for (long i = 0; i < d; i++) { add(tr, tr, u); SqrMod(u, u, F); }
    if (!IsOne(tr)) continue;
    // y = sum_{i=0}^{d-2} (sum_{j=i+1}^{d-1} th^(2^j)) a^(2^i)
    vector<GF2X> thp(d), ap(d);
    thp[0] = th; ap[0] = a;
    for (long i = 1; i < d; i++) { SqrMod(thp[i], thp[i - 1], F); SqrMod(ap[i], ap[i - 1], F); }
    GF2X suffix, y;
    for (long i = d - 2; i >= 0; i--) {
      add(suffix, suffix, thp[i + 1]);
      GF2X t2; MulMod(t2, suffix, ap[i], F);
      add(y, y, t2);
    }
    GF2X chk; SqrMod(chk, y, F); add(chk, chk, y);
    if (chk != a) die("AS root check failed");
    return y;
  }
  die("no trace-one element found");
  return GF2X();
}

// ell-th root of a in F_{2^E}^x (ell odd prime dividing 2^E-1), exact.
static GF2X kummer_root(const GF2X &a, long ell, long E, const GF2XModulus &F) {
  ZZ N = power2_ZZ(E) - 1;
  long v = 0;
  ZZ Np = N;
  while (Np % ell == 0) { Np /= ell; v++; }
  if (v == 0) die("ell does not divide 2^E-1");
  ZZ L = power_ZZ(ell, v);
  // y0 = a^(ell^-1 mod N')
  ZZ u = (Np == 1) ? ZZ(0) : InvMod(ZZ(ell) % Np, Np);
  GF2X y0;
  if (Np == 1) set(y0); else y0 = PowerMod(a, u, F);
  // eps = y0^ell / a  in mu_{ell^v}
  GF2X y0l = PowerMod(y0, ZZ(ell), F);
  GF2X ainv; InvMod(ainv, a, F);
  GF2X eps; MulMod(eps, y0l, ainv, F);
  if (!IsOne(eps)) {
    // generator g of mu_{ell^v}
    GF2X g;
    ZZ Lred = L / ell;
    for (int attempt = 0;; attempt++) {
      GF2X r; random(r, E);
      if (IsZero(r)) continue;
      g = PowerMod(r, Np, F);
      if (!IsOne(PowerMod(g, Lred, F))) break;
      if (attempt > 200) die("no generator of ell-Sylow");
    }
    // discrete log of target = eps^-1 base g, digit by digit (ell^v small)
    GF2X target; InvMod(target, eps, F);
    GF2X gl = PowerMod(g, Lred, F);  // order ell
    // table of gl^j
    vector<GF2X> tab(ell);
    set(tab[0]);
    for (long j = 1; j < ell; j++) MulMod(tab[j], tab[j - 1], gl, F);
    ZZ x = ZZ(0), pw = ZZ(1);
    for (long i = 0; i < v; i++) {
      // h = (target * g^-x)^(ell^(v-1-i))
      GF2X gx = PowerMod(g, x, F), gxi; InvMod(gxi, gx, F);
      GF2X hh; MulMod(hh, target, gxi, F);
      hh = PowerMod(hh, power_ZZ(ell, v - 1 - i), F);
      long dgt = -1;
      for (long j = 0; j < ell; j++) if (tab[j] == hh) { dgt = j; break; }
      if (dgt < 0) die("dlog digit not found");
      x += pw * dgt; pw *= ell;
    }
    if (x % ell != 0) die("radicand is not an ell-th power");
    GF2X delta = PowerMod(g, x / ell, F);
    MulMod(y0, y0, delta, F);
  }
  GF2X chk = PowerMod(y0, ZZ(ell), F);
  if (chk != a) die("Kummer root check failed");
  return y0;
}

int main(int argc, char **argv) {
  long E = 0, p = 0, n = 0;
  string line;
  vector<Comp> cs;
  vector<long> target;
  vector<pair<long, Expr>> trans;
  while (getline(cin, line)) {
    if (line.empty()) continue;
    stringstream ss(line);
    string tag; ss >> tag;
    if (tag == "E") ss >> E;
    else if (tag == "P") ss >> p;
    else if (tag == "N") ss >> n;
    else if (tag == "C") {
      Comp c; long nt; string colon;
      ss >> c.q >> c.ell >> c.deg >> nt >> colon;
      string rest; getline(ss, rest);
      c.rhs = parse_expr(rest);
      if ((long)c.rhs.size() != nt) die("term count mismatch at q=" + to_string(c.q));
      cs.push_back(c);
    } else if (tag == "T") {
      long nt; string colon; ss >> nt >> colon;
      string rest; getline(ss, rest);
      Expr e = parse_expr(rest);
      for (auto &m : e) target.push_back(m.at(0));
    } else if (tag == "M") {
      long m, nt; string colon; ss >> m >> nt >> colon;
      string rest; getline(ss, rest);
      trans.push_back({m, parse_expr(rest)});
    }
  }
  double t0 = now();
  string cache = "irred_" + to_string(E) + ".txt";
  GF2X P;
  {
    ifstream in(cache);
    if (in) { in >> P; }
  }
  if (deg(P) != E || weight(P) > 5 || !IsOne(ConstTerm(P))) {
    BuildSparseIrred(P, E);
    string tmp = cache + ".tmp." + to_string((long)getpid());
    { ofstream out(tmp); out << P; }
    rename(tmp.c_str(), cache.c_str());
  }
  GF2XModulus F(P);
  cerr << "model degree " << E << " weight " << weight(P) << " (" << now() - t0 << "s)" << endl;
  if ((power2_ZZ(E) - 1) % p != 0) die("p does not divide 2^E-1");
  for (size_t i = 0; i < cs.size(); i++) {
    double t = now();
    GF2X a = eval(cs[i].rhs, cs, F);
    if (IsZero(a) && cs[i].ell != 2) die("zero radicand");
    if (cs[i].ell == 2) cs[i].val = as_root(a, cs[i].deg, E, F);
    else cs[i].val = kummer_root(a, cs[i].ell, E, F);
    if (!has_degree(cs[i].val, cs[i].deg, F)) die("component q=" + to_string(cs[i].q) + " has wrong degree");
    cerr << "  chi_" << cs[i].q << " embedded, degree " << cs[i].deg << " (" << now() - t << "s)" << endl;
  }
  GF2X kappa;
  for (long i : target) add(kappa, kappa, cs.at(i).val);
  ZZ ex = (power2_ZZ(E) - 1) / p;
  for (auto &tr : trans) {
    double t = now();
    GF2X beta = kappa;
    add(beta, beta, eval(tr.second, cs, F));
    bool power;
    if (IsZero(beta)) power = true;
    else power = IsOne(PowerMod(beta, ex, F));
    cout << "p=" << p << " m=" << tr.first << " pth_power=" << (power ? 1 : 0) << " (" << now() - t << "s)" << endl;
  }
  cerr << "total " << now() - t0 << "s" << endl;
  return 0;
}
