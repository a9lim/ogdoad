//! Sparse PBW Weyl algebra and its rank-one polynomial action. Run with:
//!   cargo run --example weyl

use ogdoad::scalar::{Poly, Rational, Scalar};
use ogdoad::weyl::{SparsePolynomial, WeylAlgebra, WeylExpansionBudget};

fn r(value: i128) -> Rational {
    Rational::from_int(value)
}

fn main() {
    let algebra = WeylAlgebra::<Rational>::standard(1);
    let x = algebra.x(0);
    let d = algebra.d(0);

    println!("[d,x] = {}", algebra.commutator(&d, &x));
    println!(
        "d↑2 x↑3 = {}",
        algebra.mul(&algebra.pow(&d, 2), &algebra.pow(&x, 3))
    );

    let polynomial = Poly::new(vec![r(1), r(2), r(3)]); // 1 + 2t + 3t^2
    let operator = algebra.mul(&d, &x);
    println!(
        "(d x) ⋅ ({polynomial}) = {}",
        algebra.act_on_poly(&operator, &polynomial).unwrap()
    );

    let plane = WeylAlgebra::<Rational>::standard(2);
    let polynomial =
        SparsePolynomial::monomial(&[2, 3], r(1)) + SparsePolynomial::monomial(&[1, 0], r(2));
    let operator = plane.mul(&plane.d(0), &plane.x(1));
    println!(
        "(d0 x1) ⋅ ({polynomial}) = {}",
        plane
            .act_on_sparse_poly_with_budget(
                &operator,
                &polynomial,
                WeylExpansionBudget::new(32, 1_000),
            )
            .unwrap()
    );
}
