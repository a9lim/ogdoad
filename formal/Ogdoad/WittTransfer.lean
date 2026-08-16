import Ogdoad.Fifo
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.RingTheory.Trace.Basic

/-!
# Finite-field trace calculation for the ramified Arf generator

This file formalizes the basis calculation behind the statement that every
nonzero Scharlau transfer from a finite extension of `F_2` preserves the
unique nonzero quadratic Witt class.  In the trace-normalized case, the
transferred plane has Arf coordinate

```text
sum_i Tr(e_i^2) * Tr(a * f_i^2),
```

where `(e_i)` is any basis and `(f_i)` its trace-dual basis.  The main theorem
proves that this sum is exactly `Tr(a)`.  Consequently it is one whenever the
source binary plane has Arf invariant one.

Packaging this calculation as a theorem about Scharlau transfer on quadratic
Witt groups still awaits a quadratic Witt-group API; the arithmetic identity
itself is kernel-checked here.
-/

namespace Ogdoad.WittTransfer

open Module
open scoped BigOperators CharTwo

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [Field E] [Finite E] [CharP E 2] [Algebra F2 E]

/-- The unique trace-pairing coefficient representing an `F_2`-linear
functional. -/
noncomputable def functionalCoefficient (s : E →ₗ[F2] F2) : E :=
  ((Algebra.traceForm F2 E).toDual
    (traceForm_nondegenerate F2 E)).symm s

theorem functionalCoefficient_spec (s : E →ₗ[F2] F2) (z : E) :
    s z = Algebra.trace F2 E (functionalCoefficient s * z) := by
  symm
  exact (LinearMap.BilinForm.apply_toDual_symm_apply
    (B := Algebra.traceForm F2 E) s z)

theorem functionalCoefficient_ne_zero {s : E →ₗ[F2] F2} (hs : s ≠ 0) :
    functionalCoefficient s ≠ 0 := by
  intro hc
  apply hs
  apply LinearMap.ext
  intro z
  rw [functionalCoefficient_spec, hc]
  simp

/-- Every nonzero functional is trace against a nonzero square. -/
theorem exists_square_trace_coefficient (s : E →ₗ[F2] F2) (hs : s ≠ 0) :
    ∃ d : E, d ≠ 0 ∧
      ∀ z : E, s z = Algebra.trace F2 E (d ^ 2 * z) := by
  let c := functionalCoefficient s
  have hc : c ≠ 0 := functionalCoefficient_ne_zero hs
  obtain ⟨d, hd⟩ := surjective_frobenius E 2 c
  have hdsq : d ^ 2 = c := by
    simpa only [frobenius_def] using hd
  have hd0 : d ≠ 0 := by
    intro hd0
    apply hc
    rw [← hdsq, hd0]
    simp
  refine ⟨d, hd0, fun z ↦ ?_⟩
  rw [functionalCoefficient_spec, hdsq]

/-- Simultaneous scaling by the square root turns the transfer along an
arbitrary nonzero functional into the trace-normalized plane used below. -/
theorem scharlau_plane_change (s : E →ₗ[F2] F2) (d a x y : E)
    (hs : ∀ z : E, s z = Algebra.trace F2 E (d ^ 2 * z)) :
    s (x ^ 2 + x * y + a * y ^ 2) =
      Algebra.trace F2 E
        ((d * x) ^ 2 + (d * x) * (d * y) + a * (d * y) ^ 2) := by
  rw [hs]
  congr 1
  ring

/-- Absolute trace is invariant under squaring over `F_2`. -/
theorem trace_sq (x : E) :
    Algebra.trace F2 E (x ^ 2) = Algebra.trace F2 E x := by
  apply (algebraMap F2 E).injective
  calc
    algebraMap F2 E (Algebra.trace F2 E (x ^ 2)) =
        ∑ i ∈ Finset.range (Module.finrank F2 E),
          (x ^ 2) ^ (Nat.card F2 ^ i) :=
      FiniteField.algebraMap_trace_eq_sum_pow F2 E (x ^ 2)
    _ = (∑ i ∈ Finset.range (Module.finrank F2 E),
          x ^ (Nat.card F2 ^ i)) ^ 2 := by
      rw [CharTwo.sum_sq]
      apply Finset.sum_congr rfl
      intro i _
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    _ = (algebraMap F2 E (Algebra.trace F2 E x)) ^ 2 := by
      rw [FiniteField.algebraMap_trace_eq_sum_pow]
    _ = algebraMap F2 E ((Algebra.trace F2 E x) ^ 2) := by
      rw [map_pow]
    _ = algebraMap F2 E (Algebra.trace F2 E x) := by
      rw [show (Algebra.trace F2 E x) ^ 2 = Algebra.trace F2 E x by
        simpa [pow_two] using Ogdoad.zmod2_sq_eq_self
          (Algebra.trace F2 E x)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared trace-dual resolution of one. -/
theorem sum_trace_smul_traceDual_sq (b : Basis ι F2 E) :
    (∑ i, Algebra.trace F2 E (b i) • (b.traceDual i) ^ 2) = 1 := by
  have hone := b.traceDual.sum_repr (1 : E)
  have hrepr (i : ι) :
      b.traceDual.repr (1 : E) i = Algebra.trace F2 E (b i) := by
    rw [Module.Basis.traceDual_repr_apply]
    simp [Algebra.traceForm_apply]
  rw [show (1 : E) = (1 : E) ^ 2 by simp]
  rw [← hone]
  rw [CharTwo.sum_sq]
  apply Finset.sum_congr rfl
  intro i _
  rw [hrepr]
  simp only [Algebra.smul_def, mul_pow]
  rw [show (algebraMap F2 E (Algebra.trace F2 E (b i))) ^ 2 =
      algebraMap F2 E (Algebra.trace F2 E (b i)) by
    rw [← map_pow]
    congr 1
    simpa [pow_two] using Ogdoad.zmod2_sq_eq_self
      (Algebra.trace F2 E (b i))]

/-- The transferred trace plane has the same Arf coordinate as its source
plane. -/
theorem transfer_arf_sum (b : Basis ι F2 E) (a : E) :
    (∑ i, Algebra.trace F2 E ((b i) ^ 2) *
      Algebra.trace F2 E (a * (b.traceDual i) ^ 2)) =
        Algebra.trace F2 E a := by
  simp_rw [trace_sq]
  have hterm (i : ι) :
      Algebra.trace F2 E (b i) *
          Algebra.trace F2 E (a * (b.traceDual i) ^ 2) =
        Algebra.trace F2 E
          (Algebra.trace F2 E (b i) • (a * (b.traceDual i) ^ 2)) := by
    rw [map_smul]
    rfl
  simp_rw [hterm]
  rw [← map_sum (Algebra.trace F2 E)]
  congr 1
  calc
    (∑ i, Algebra.trace F2 E (b i) •
        (a * (b.traceDual i) ^ 2)) =
        a * (∑ i, Algebra.trace F2 E (b i) • (b.traceDual i) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Algebra.smul_def]
      ring
    _ = a := by rw [sum_trace_smul_traceDual_sq b, mul_one]

/-- Arf-one specialization used by the global reciprocity map. -/
theorem transfer_arf_one (b : Basis ι F2 E) {a : E}
    (ha : Algebra.trace F2 E a = 1) :
    (∑ i, Algebra.trace F2 E ((b i) ^ 2) *
      Algebra.trace F2 E (a * (b.traceDual i) ^ 2)) = 1 := by
  rw [transfer_arf_sum b a, ha]

end

end Ogdoad.WittTransfer
