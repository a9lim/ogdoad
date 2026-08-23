use ogdoad::scalar::{Fp, Nimber, Scalar};
use ogdoad::weyl::{
    WeylAlgebra, WeylExpansionBudget, WeylFiberBrauerEvidence, WeylPSymbolError,
    WeylRepresentationBudget,
};

type F3 = Fp<3>;

fn f3(value: i128) -> F3 {
    F3::from_int(value)
}

fn representation_budget() -> WeylRepresentationBudget {
    WeylRepresentationBudget::new(256, 100_000, 20_000_000)
}

fn expansion_budget() -> WeylExpansionBudget {
    WeylExpansionBudget::new(1_000, 1_000_000)
}

#[test]
fn psymbol_residue_matches_split_matrix_trace() {
    let algebra = WeylAlgebra::<F3>::standard(1);
    let presentation = algebra
        .psymbol_presentation(vec![f3(2), f3(1)], representation_budget())
        .unwrap();
    assert_eq!(presentation.characteristic(), 3);
    assert_eq!(presentation.tensor_rank(), 1);
    assert_eq!(presentation.pairs()[0].position_power(), &f3(2));
    assert_eq!(presentation.pairs()[0].momentum_power(), &f3(1));
    assert_eq!(presentation.brauer_report().is_split(), None);

    let top = algebra.monomial(&[2, 2], f3(1));
    let reduced = presentation.fiber().reduce(&top).unwrap();
    assert_eq!(presentation.p_residue(&reduced).unwrap(), f3(1));

    // Frobenius is the identity on F_3, so the central values are their own
    // verified splitting roots.
    let module = algebra
        .split_central_character_module(
            vec![f3(2), f3(1)],
            vec![f3(2), f3(1)],
            representation_budget(),
        )
        .unwrap();
    assert!(presentation
        .split_matrix_trace_matches_residue(&module, &reduced, representation_budget())
        .unwrap());

    let certificate = algebra
        .odd_matrix_fiber_certificate(
            vec![f3(2), f3(1)],
            vec![f3(2), f3(1)],
            representation_budget(),
        )
        .unwrap();
    let report = presentation
        .brauer_report_with_matrix_certificate(&certificate)
        .unwrap();
    assert_eq!(report.is_split(), Some(true));
    assert!(matches!(
        report.evidence(),
        WeylFiberBrauerEvidence::SplitMatrixCertificate {
            matrix_dimension: 3,
            image_rank: 9,
        }
    ));
}

#[test]
fn psymbol_cyclic_conversion_checks_all_relations() {
    let algebra = WeylAlgebra::<F3>::standard(1);
    let presentation = algebra
        .psymbol_presentation(vec![f3(2), f3(1)], representation_budget())
        .unwrap();
    let cyclic = presentation
        .cyclic_factor(0, representation_budget(), expansion_budget())
        .unwrap();
    assert_eq!(cyclic.characteristic(), 3);
    assert_eq!(cyclic.position_power(), &f3(2));
    assert_eq!(cyclic.momentum_power(), &f3(1));
    assert_eq!(cyclic.artin_schreier_parameter(), &f3(2));
    assert!(!cyclic.eta().is_zero());
    assert!(!cyclic.zeta().is_zero());

    let nonsplit_presentation = algebra
        .psymbol_presentation(vec![f3(1), f3(0)], representation_budget())
        .unwrap();
    assert_eq!(
        nonsplit_presentation
            .cyclic_factor(0, representation_budget(), expansion_budget())
            .unwrap_err(),
        WeylPSymbolError::NonInvertibleCyclicParameter { pair: 0 }
    );
}

#[test]
fn automorphisms_pull_back_central_characters_with_char2_correction() {
    let odd = WeylAlgebra::<F3>::standard(1);
    let fourier = odd.fourier_automorphism().unwrap();
    let pulled = fourier
        .pullback_central_character(
            vec![f3(1), f3(2)],
            representation_budget(),
            expansion_budget(),
        )
        .unwrap();
    // x -> d and d -> -x; in odd characteristic (-x)^p = -x^p.
    assert_eq!(pulled.pulled_back_values(), &[f3(2), f3(2)]);

    let translated = odd
        .translation_automorphism(&[f3(1), f3(2)])
        .unwrap()
        .pullback_central_character(
            vec![f3(1), f3(2)],
            representation_budget(),
            expansion_budget(),
        )
        .unwrap();
    assert_eq!(translated.pulled_back_values(), &[f3(2), f3(1)]);

    let even = WeylAlgebra::<Nimber>::standard(1);
    let sheared = even
        .shear_automorphism(&[vec![Nimber(1)]])
        .unwrap()
        .pullback_central_character(
            vec![Nimber(2), Nimber(3)],
            representation_budget(),
            expansion_budget(),
        )
        .unwrap();
    // d -> d+x gives (d+x)^2 = d^2+x^2+[d,x] in characteristic two.
    assert_eq!(sheared.pulled_back_values(), &[Nimber(2), Nimber(0)]);
}

#[test]
fn arbitrary_alternating_presentations_get_bounded_transported_fibres() {
    let algebra = WeylAlgebra::from_commutator(vec![
        vec![f3(0), f3(1), f3(1)],
        vec![f3(-1), f3(0), f3(2)],
        vec![f3(-1), f3(-2), f3(0)],
    ])
    .unwrap();
    let fiber = algebra
        .transported_central_fiber(vec![f3(2), f3(1)], vec![f3(2)], representation_budget())
        .unwrap();
    assert_eq!(fiber.decomposition().weyl_rank(), 1);
    assert_eq!(fiber.decomposition().central_rank(), 1);
    assert_eq!(fiber.basis_dimension(), 9);
    assert_eq!(fiber.psymbol_presentation().tensor_rank(), 1);

    let left = fiber.generator(0).unwrap();
    let right = fiber.generator(1).unwrap();
    assert!(fiber
        .products_agree_with_source(&left, &right, expansion_budget())
        .unwrap());

    let normal_radical = fiber.decomposition().central_generator(0).unwrap();
    let source_radical = fiber.decomposition().from_normal(&normal_radical).unwrap();
    let reduced_radical = fiber.reduce(&source_radical).unwrap();
    assert_eq!(reduced_radical.coefficients()[0], f3(2));
    assert!(reduced_radical
        .coefficients()
        .iter()
        .skip(1)
        .all(Scalar::is_zero));

    let lifted = fiber.lift(&left).unwrap();
    assert_eq!(fiber.reduce(&lifted).unwrap(), left);
}

#[test]
fn transported_fibre_character_shapes_are_checked() {
    let algebra = WeylAlgebra::from_commutator(vec![
        vec![f3(0), f3(1), f3(0)],
        vec![f3(-1), f3(0), f3(0)],
        vec![f3(0), f3(0), f3(0)],
    ])
    .unwrap();
    assert_eq!(
        algebra
            .transported_central_fiber(vec![f3(0)], vec![f3(0)], representation_budget())
            .unwrap_err(),
        WeylPSymbolError::PairedCharacterDimensionMismatch {
            expected: 2,
            actual: 1,
        }
    );
    assert_eq!(
        algebra
            .transported_central_fiber(vec![f3(0), f3(0)], Vec::new(), representation_budget(),)
            .unwrap_err(),
        WeylPSymbolError::RadicalCharacterDimensionMismatch {
            expected: 1,
            actual: 0,
        }
    );
}
