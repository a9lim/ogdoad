//! A quick tour of pleroma's verified core. Run with:
//!   cargo run --example tour

use pleroma::clifford::{CliffordAlgebra, Metric};
use pleroma::nimber::Nimber;
use pleroma::scalar::{Rational, Scalar};
use pleroma::surcomplex::Surcomplex;
use pleroma::surreal::Surreal;
use std::collections::BTreeMap;

fn rule(title: &str) {
    println!("\n── {title} ──");
}

fn main() {
    rule("nimbers On₂ — char 2, the non-commutative Clifford case");
    // b[(0,1)] = *1  ⇒  e0 e1 + e1 e0 = *1 ≠ 0  ⇒  non-commutative
    let mut b = BTreeMap::new();
    b.insert((0usize, 1usize), Nimber(1));
    let alg = CliffordAlgebra::new(2, Metric { q: vec![Nimber(2), Nimber(3)], b });
    let (e0, e1) = (alg.gen(0), alg.gen(1));
    println!("  e0 e1      = {}", alg.mul(&e0, &e1).display());
    println!("  e1 e0      = {}", alg.mul(&e1, &e0).display());
    println!(
        "  {{e0,e1}}   = {}   (the anticommutator b[(0,1)] = *1)",
        alg.add(&alg.mul(&e0, &e1), &alg.mul(&e1, &e0)).display()
    );
    println!("  e0²        = {}   (a nimber square, not ±1)", alg.mul(&e0, &e0).display());

    rule("Grassmann — fully null metric, nilpotent generators");
    let g = CliffordAlgebra::new(3, Metric::<Rational>::grassmann(3));
    println!("  e0²        = {}", g.mul(&g.gen(0), &g.gen(0)).display());
    println!("  e0 e1      = {}", g.mul(&g.gen(0), &g.gen(1)).display());
    println!("  e1 e0      = {}   (antisymmetric)", g.mul(&g.gen(1), &g.gen(0)).display());

    rule("surreals — a Clifford metric with NO finite entries");
    // e0² = ω (infinite), e1² = ε = ω⁻¹ (infinitesimal), orthogonal.
    let s = CliffordAlgebra::new(
        2,
        Metric::diagonal(vec![Surreal::omega(), Surreal::epsilon()]),
    );
    let e0e1 = s.mul(&s.gen(0), &s.gen(1));
    println!("  e0²        = {}", s.mul(&s.gen(0), &s.gen(0)).display());
    println!("  e1²        = {}", s.mul(&s.gen(1), &s.gen(1)).display());
    println!("  (e0 e1)²   = {}   (= -(ω·ε) = -1, a unit bivector)", s.mul(&e0e1, &e0e1).display());

    rule("surreal arithmetic — recursive exponents");
    let w = Surreal::omega();
    println!("  ω·ε        = {:?}", w.mul(&Surreal::epsilon()));
    println!("  (ω+1)(ω-1) = {:?}", w.add(&Surreal::from_int(1)).mul(&w.sub(&Surreal::from_int(1))));
    println!("  √ω squared = {:?}", {
        let r = Surreal::omega_pow(Surreal::from_rational(Rational::new(1, 2)));
        r.mul(&r)
    });
    println!("  ω^ω        = {:?}", Surreal::omega_pow(Surreal::omega()));

    rule("surcomplex — why it only works over the surreals");
    type NC = Surcomplex<Nimber>;
    let one_plus_i = NC::new(Nimber(1), Nimber(1));
    println!("  over On₂:  i²        = {:?}   (= -1 = 1 in char 2)", NC::i().mul(&NC::i()));
    println!("  over On₂:  (1+i)²    = {:?}   (nonzero nilpotent ⇒ not a field)", one_plus_i.mul(&one_plus_i));
    type SC = Surcomplex<Surreal>;
    let z = SC::new(Surreal::omega(), Surreal::from_int(1)); // ω + i
    println!("  over No:   (ω+i)(ω-i) = {:?}   (= ω²+1, a genuine norm)", z.mul(&z.conj()));
}
