// Minimal polynomial over F_2 of the quoted 359-certificate norm theta in
// F_2[X]/(X^179+X^4+X^2+X+1), and theta^((2^179-1)/p) for p in {359, 1433}.
#include <NTL/GF2X.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <iostream>
#include <string>
using namespace NTL;
using namespace std;
static GF2X from_hex(const string &s) {
  GF2X a;
  long n = s.size();
  for (long i = 0; i < n; i++) {
    char ch = s[n - 1 - i];
    int v = (ch >= '0' && ch <= '9') ? ch - '0' : (tolower(ch) - 'a' + 10);
    for (int b = 0; b < 4; b++)
      if ((v >> b) & 1) SetCoeff(a, 4 * i + b);
  }
  return a;
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
int main() {
  GF2X P;
  SetCoeff(P, 179);
  SetCoeff(P, 4);
  SetCoeff(P, 2);
  SetCoeff(P, 1);
  SetCoeff(P, 0);
  if (!IterIrredTest(P)) { cout << "modulus reducible" << endl; return 1; }
  GF2XModulus F(P);
  GF2X theta = from_hex("28494A54795638CF203B2404FE5133E2AE0E13C2CA4E6");
  GF2X mu;
  MinPolyMod(mu, theta, F);
  GF2X chk = CompMod(mu, theta, F);
  cout << "THETA_MINPOLY deg=" << deg(mu) << " annihilates=" << IsZero(chk)
       << " irreducible=" << IterIrredTest(mu) << " hex=" << to_hex(mu) << endl;
  for (long p : {359L, 1433L}) {
    ZZ e = (power2_ZZ(179) - 1) / p;
    GF2X x = PowerMod(theta, e, F);
    cout << "theta^((2^179-1)/" << p << ") = 0x" << to_hex(x) << " is_one=" << IsOne(x)
         << " order_divides_p=" << IsOne(PowerMod(x, p, F)) << endl;
  }
  return 0;
}
