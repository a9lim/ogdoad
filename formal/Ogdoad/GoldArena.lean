import Ogdoad.GoldMatchingAlgebra
import Ogdoad.ImpartialRealizer
import Ogdoad.PhysicalDeferred
import Ogdoad.WittFrame
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# End-to-end weighted-source Gold arena

This file constructs the public Witt frame, loading map, potential matching,
refinement-selected weight graph, public close ledger, and normal-play root.
The final theorem states the realization without accepting any of those joins
as premises.

The module exposes both the paper's literal transition system and its deferred
compiler form.  The literal game starts at score zero, charges a binary edge
exactly when its second endpoint opens, and charges the public label at CLOSE.
Two proved state conjugacies transport its complete strategy tree to the
deferred safe-front realization.  The flagship theorem
`gold_literal_root_isP_iff` therefore reaches the literal root, not merely an
accounting-equivalent terminal score.
-/

noncomputable section

namespace Ogdoad.GoldArena

open Module

open scoped BigOperators CharTwo
open Ogdoad.Fifo
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {V J : Type*} [AddCommGroup V] [Module F2 V]
  [FiniteDimensional F2 V] [Fintype J] [LinearOrder J]

/-- The upper-triangular half of an alternating form in the public original
basis.  Its diagonal is zero and its symmetrization is `B`. -/
def upperBilin (B : LinearMap.BilinForm F2 V) (original : Basis J F2 V) :
    LinearMap.BilinForm F2 V :=
  original.constr F2 fun i ↦
    original.constr F2 fun j ↦
      if i < j then B (original i) (original j) else 0

@[simp] theorem upperBilin_basis (B : LinearMap.BilinForm F2 V)
    (original : Basis J F2 V) (i j : J) :
    upperBilin B original (original i) (original j) =
      if i < j then B (original i) (original j) else 0 := by
  simp only [upperBilin, Basis.constr_basis]

/-- The refinement-blind quadratic form determined by `B` and the ordered
original basis. -/
def publicQuadratic (B : LinearMap.BilinForm F2 V)
    (original : Basis J F2 V) : QuadraticForm F2 V :=
  (upperBilin B original).toQuadraticMap

@[simp] theorem publicQuadratic_basis (B : LinearMap.BilinForm F2 V)
    (original : Basis J F2 V) (i : J) :
    publicQuadratic B original (original i) = 0 := by
  rw [publicQuadratic, LinearMap.BilinMap.toQuadraticMap_apply, upperBilin_basis]
  simp

/-- The public quadratic has exactly the supplied alternating polar form. -/
theorem publicQuadratic_polar (B : LinearMap.BilinForm F2 V)
    (hAlt : B.IsAlt) (original : Basis J F2 V) :
    (publicQuadratic B original).polarBilin = B := by
  apply original.ext
  intro i
  apply original.ext
  intro j
  change QuadraticMap.polar (publicQuadratic B original)
    (original i) (original j) = B (original i) (original j)
  rw [publicQuadratic, LinearMap.BilinMap.polar_toQuadraticMap]
  simp only [LinearMap.add_apply, upperBilin_basis]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [hij, not_lt.mpr hij.le]
  · simp [hAlt.self_eq_zero]
  · have hsymm : B (original j) (original i) = B (original i) (original j) := by
      calc
        B (original j) (original i) = -B (original i) (original j) :=
          (hAlt.neg_eq (original i) (original j)).symm
        _ = B (original i) (original j) := by simp
    simp [hji, not_lt.mpr hji.le, hsymm]

/-- Linear source whose values on the original basis are the singleton
queries `Q(e_j)`. -/
def diagonalSource (Q : QuadraticForm F2 V) (b : Basis J F2 V) : V →ₗ[F2] F2 :=
  b.constr F2 fun j ↦ Q (b j)

@[simp] theorem diagonalSource_basis (Q : QuadraticForm F2 V)
    (b : Basis J F2 V) (j : J) : diagonalSource Q b (b j) = Q (b j) := by
  simp [diagonalSource]

omit [FiniteDimensional F2 V] [Fintype J] [LinearOrder J] in
/-- The source map is exactly the sum of active singleton queries. -/
theorem diagonalSource_eq_support_sum (Q : QuadraticForm F2 V)
    (b : Basis J F2 V) (x : V) :
    diagonalSource Q b x = ∑ j ∈ (b.repr x).support, Q (b j) := by
  classical
  rw [diagonalSource, Basis.constr_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hne : b.repr x j ≠ 0 := Finsupp.mem_support_iff.mp hj
  have hone : b.repr x j = 1 := Ogdoad.zmod2_eq_one_of_ne_zero _ hne
  simp [hone]

/-- Two refinements with the same polar form differ by exactly their public
diagonal source. -/
theorem refinement_split (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (Q : QuadraticForm F2 V)
    (hpolar : Q.polarBilin = B) (x : V) :
    Q x = publicQuadratic B original x + diagonalSource Q original x := by
  let Q₀ := publicQuadratic B original
  have hQ₀polar : Q₀.polarBilin = B := publicQuadratic_polar B hAlt original
  let D : V →ₗ[F2] F2 :=
    { toFun := fun y ↦ Q y + Q₀ y
      map_add' := by
        intro u v
        rw [QuadraticMap.map_add (⇑Q) u v, QuadraticMap.map_add (⇑Q₀) u v]
        have hp : QuadraticMap.polar Q u v = QuadraticMap.polar Q₀ u v := by
          change Q.polarBilin u v = Q₀.polarBilin u v
          rw [hpolar, hQ₀polar]
        rw [hp]
        calc
          Q u + Q v + QuadraticMap.polar Q₀ u v +
                (Q₀ u + Q₀ v + QuadraticMap.polar Q₀ u v) =
              (Q u + Q₀ u) + (Q v + Q₀ v) +
                (QuadraticMap.polar Q₀ u v + QuadraticMap.polar Q₀ u v) := by
            ring
          _ = (Q u + Q₀ u) + (Q v + Q₀ v) := by simp
      map_smul' := by
        intro a y
        rw [QuadraticMap.map_smul Q a y, QuadraticMap.map_smul Q₀ a y]
        have ha : a * a = a := by fin_cases a <;> decide
        rw [ha]
        simp only [smul_eq_mul, RingHom.id_apply, mul_add] }
  have hD : D = diagonalSource Q original := by
    apply original.ext
    intro i
    simp [D, Q₀, diagonalSource, publicQuadratic_basis]
  have hDx := LinearMap.congr_fun hD x
  change Q x + Q₀ x = diagonalSource Q original x at hDx
  calc
    Q x = Q x + (Q₀ x + Q₀ x) := by simp
    _ = Q₀ x + (Q x + Q₀ x) := by ring
    _ = Q₀ x + diagonalSource Q original x := by rw [hDx]

/-- The deterministic adapted basis supplied by `WittFrame`. -/
def adaptedBasis (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt) :
    Basis (WittFrame.frame B hAlt).Index F2 V :=
  (WittFrame.frame B hAlt).basis.map Submodule.topEquiv

/-- Active basis coordinates are the strategic coins. -/
abbrev Active (b : Basis J F2 V) (x : V) := ↑(b.repr x).support

/-- The public loaded coin type: one strategic coin per active adapted
coordinate, and a two-coin source pair per active original coordinate. -/
abbrev Coin (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V) :=
  Active (adaptedBasis B hAlt) x ⊕ (Active original x × Fin 2)

/-- The public potential relation.  It depends on `B`, the two coordinate
supports, and the fixed frame, but not on `Q`. -/
def publicRel (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V) :
    Coin B hAlt original x → Coin B hAlt original x → Prop
  | .inl i, .inl j => (WittFrame.frame B hAlt).mate i = some j
  | .inr (i, a), .inr (j, b) => i = j ∧ a ≠ b
  | _, _ => False

def publicGraph (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V) :
    SimpleGraph (Coin B hAlt original x) :=
  SimpleGraph.fromRel (publicRel B hAlt original x)

/-- Unit-weight strategic edges and refinement-weighted source edges. -/
def weightedRel (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (Q : QuadraticForm F2 V) (x : V) :
    Coin B hAlt original x → Coin B hAlt original x → Prop
  | .inl i, .inl j => (WittFrame.frame B hAlt).mate i = some j
  | .inr (i, a), .inr (j, b) => i = j ∧ a ≠ b ∧ Q (original i) = 1
  | _, _ => False

def weightedGraph (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (Q : QuadraticForm F2 V) (x : V) :
    SimpleGraph (Coin B hAlt original x) :=
  SimpleGraph.fromRel (weightedRel B hAlt original Q x)

private theorem publicRel_symm (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V)
    {u v : Coin B hAlt original x} :
    publicRel B hAlt original x u v → publicRel B hAlt original x v u := by
  intro huv
  rcases u with i | ⟨i, a⟩ <;> rcases v with j | ⟨j, b⟩
  · exact (WittFrame.frame B hAlt).mate_symm huv
  · contradiction
  · contradiction
  · exact ⟨huv.1.symm, huv.2.symm⟩

private theorem publicRel_irrefl (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V) :
    ∀ u, ¬publicRel B hAlt original x u u := by
  intro u
  rcases u with i | ⟨i, a⟩
  · exact (WittFrame.frame B hAlt).mate_ne_self i
  · simp [publicRel]

theorem publicGraph_adj_iff (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V)
    (u v : Coin B hAlt original x) :
    (publicGraph B hAlt original x).Adj u v ↔ publicRel B hAlt original x u v := by
  rw [publicGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, huv | hvu⟩
    · exact huv
    · exact publicRel_symm B hAlt original x hvu
  · intro huv
    exact ⟨fun h ↦ publicRel_irrefl B hAlt original x u (h ▸ huv), Or.inl huv⟩

/-- The public board is a matching plus isolates. -/
theorem publicGraph_isMatching (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V) :
    IsMatchingGraph (publicGraph B hAlt original x) := by
  intro v y z hvy hvz
  rw [publicGraph_adj_iff] at hvy hvz
  rcases v with i | ⟨i, a⟩ <;> rcases y with j | ⟨j, b⟩ <;>
    rcases z with k | ⟨k, c⟩
  · apply congrArg Sum.inl
    apply Subtype.ext
    exact Option.some.inj (hvy.symm.trans hvz)
  all_goals try contradiction
  · simp only [publicRel] at hvy hvz
    obtain ⟨rfl, hab⟩ := hvy
    obtain ⟨rfl, hac⟩ := hvz
    apply congrArg Sum.inr
    apply Prod.ext
    · rfl
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

/-- The actual unit-weight graph only deletes zero-weight source edges. -/
theorem weightedGraph_le_public (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (Q : QuadraticForm F2 V) (x : V) :
    weightedGraph B hAlt original Q x ≤ publicGraph B hAlt original x := by
  intro u v huv
  rw [publicGraph_adj_iff]
  rw [weightedGraph, SimpleGraph.fromRel_adj] at huv
  rcases huv.2 with huv | hvu
  · rcases u with i | ⟨i, a⟩ <;> rcases v with j | ⟨j, b⟩
    · exact huv
    · contradiction
    · contradiction
    · exact ⟨huv.1, huv.2.1⟩
  · apply publicRel_symm B hAlt original x
    rcases u with i | ⟨i, a⟩ <;> rcases v with j | ⟨j, b⟩
    · exact hvu
    · contradiction
    · contradiction
    · exact ⟨hvu.1, hvu.2.1⟩

/-- Public close charges on the active adapted coordinates. -/
def closeCharge (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V) : F2 :=
  ∑ i ∈ ((adaptedBasis B hAlt).repr x).support,
    publicQuadratic B original (adaptedBasis B hAlt i)

/-- Opening charges of active strategic matching edges, expressed by the
public quadratic cross term in the adapted frame. -/
def strategicCharge (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V) : F2 :=
  publicQuadratic B original x +
    diagonalSource (publicQuadratic B original) (adaptedBasis B hAlt) x

/-- Source-edge weights are exactly the active original singleton queries. -/
def sourceCharge (Q : QuadraticForm F2 V) (original : Basis J F2 V)
    (x : V) : F2 :=
  diagonalSource Q original x

/-- Deferred initial ledger for the physical weighted arena. -/
def initialCharge (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (Q : QuadraticForm F2 V) (x : V) : F2 :=
  closeCharge B hAlt original x + strategicCharge B hAlt original x +
    sourceCharge Q original x

/-- Per edge, deferred charging is exactly physical open charging: if an edge
is either overlapped or missed, charging it initially and toggling on a miss
leaves precisely its overlap charge. -/
theorem deferred_edge_charge_eq_overlap (overlap missed : F2)
    (partition : overlap + missed = 1) : 1 + missed = overlap := by
  calc
    1 + missed = (overlap + missed) + missed := by rw [partition]
    _ = overlap := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem closeCharge_eq_diagonalSource (B : LinearMap.BilinForm F2 V)
    (hAlt : B.IsAlt) (original : Basis J F2 V) (x : V) :
    closeCharge B hAlt original x =
      diagonalSource (publicQuadratic B original) (adaptedBasis B hAlt) x := by
  rw [closeCharge, diagonalSource_eq_support_sum]

/-- The three compiled ledgers add to the requested quadratic value. -/
theorem initialCharge_eq_quadratic (B : LinearMap.BilinForm F2 V)
    (hAlt : B.IsAlt) (original : Basis J F2 V)
    (Q : QuadraticForm F2 V) (hpolar : Q.polarBilin = B) (x : V) :
    initialCharge B hAlt original Q x = Q x := by
  rw [initialCharge, closeCharge_eq_diagonalSource]
  rw [strategicCharge, sourceCharge]
  have hsplit := refinement_split B hAlt original Q hpolar x
  calc
    diagonalSource (publicQuadratic B original) (adaptedBasis B hAlt) x +
          (publicQuadratic B original x +
            diagonalSource (publicQuadratic B original) (adaptedBasis B hAlt) x) +
          diagonalSource Q original x =
        publicQuadratic B original x + diagonalSource Q original x := by
      calc
        _ = (diagonalSource (publicQuadratic B original) (adaptedBasis B hAlt) x +
              diagonalSource (publicQuadratic B original) (adaptedBasis B hAlt) x) +
            (publicQuadratic B original x + diagonalSource Q original x) := by abel
        _ = publicQuadratic B original x + diagonalSource Q original x := by
          rw [CharTwo.add_self_eq_zero, zero_add]
    _ = Q x := hsplit.symm

/-- Boolean presentation of an `F₂` charge for the existing impartial tail
compiler. -/
def chargeBool (z : F2) : Bool := decide (z = 1)

theorem chargeBool_eq_false_iff (z : F2) : chargeBool z = false ↔ z = 0 := by
  by_cases hz : z = 1
  · simp [chargeBool, hz]
  · have : z = 0 := Ogdoad.zmod2_eq_zero_of_ne_one z hz
    simp [chargeBool, this]

/-- Deferred compiler endpoint.  The types, frame, loading, public matching,
source weights, deferred weighted charge, safe-front policy, exact even tempo,
and one-move tail are all instantiated here. -/
theorem gold_root_isP_iff (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (Q : QuadraticForm F2 V)
    (hpolar : Q.polarBilin = B) (x : V) :
    ImpartialRealizer.TailWins (weightedGraph B hAlt original Q x) true
      (ImpartialRealizer.initial
        (V := Coin B hAlt original x)
        (ImpartialRealizer.scoreBit
          (chargeBool (initialCharge B hAlt original Q x)))) ↔
      Q x = 0 := by
  rw [ImpartialRealizer.root_isP_iff_charge_zero
    (publicGraph_isMatching B hAlt original x)
    (weightedGraph_le_public B hAlt original Q x)]
  rw [chargeBool_eq_false_iff, initialCharge_eq_quadratic B hAlt original Q hpolar x]

variable {V J : Type*} [AddCommGroup V] [Module F2 V]
  [FiniteDimensional F2 V] [Fintype J] [LinearOrder J]

noncomputable local instance frameIndexLinearOrder
    (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt) :
    LinearOrder (WittFrame.frame B hAlt).Index := by
  letI : DecidableRel (@WellOrderingRel (WittFrame.frame B hAlt).Index) :=
    Classical.decRel _
  exact linearOrderOfSTO WellOrderingRel

noncomputable local instance sourceCoinLinearOrder
    (original : Basis J F2 V) (x : V) :
    LinearOrder (Active original x × Fin 2) :=
  LinearOrder.lift' toLex toLex.injective

noncomputable local instance goldCoinDecidableEq
    (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V) :
    DecidableEq (Coin B hAlt original x) := instDecidableEqSum

noncomputable local instance coinLinearOrder
    (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V) :
    LinearOrder (Coin B hAlt original x) := by
  letI : LinearOrder (WittFrame.frame B hAlt).Index :=
    frameIndexLinearOrder B hAlt
  letI : LinearOrder (Active (adaptedBasis B hAlt) x) := inferInstance
  letI : LinearOrder (Active original x × Fin 2) :=
    sourceCoinLinearOrder original x
  exact LinearOrder.lift' toLex toLex.injective

def sourceLess (original : Basis J F2 V) (x : V)
    (p q : Active original x × Fin 2) : Prop :=
  @LT.lt _ (sourceCoinLinearOrder original x).toLT p q

def coinLess (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V)
    (u v : Coin B hAlt original x) : Prop :=
  @LT.lt _ (coinLinearOrder B hAlt original x).toLT u v

noncomputable local instance sourceLessDecidable
    (original : Basis J F2 V) (x : V) : DecidableRel (sourceLess original x) :=
  Classical.decRel _

private theorem weightedRel_symm' (B : LinearMap.BilinForm F2 V)
    (hAlt : B.IsAlt) (original : Basis J F2 V) (Q : QuadraticForm F2 V)
    (x : V) {u v : Coin B hAlt original x} :
    weightedRel B hAlt original Q x u v →
      weightedRel B hAlt original Q x v u := by
  intro huv
  rcases u with i | ⟨i, a⟩ <;> rcases v with j | ⟨j, b⟩
  · exact (WittFrame.frame B hAlt).mate_symm huv
  · contradiction
  · contradiction
  · obtain ⟨rfl, hab, hQ⟩ := huv
    exact ⟨rfl, hab.symm, hQ⟩

private theorem weightedRel_irrefl' (B : LinearMap.BilinForm F2 V)
    (hAlt : B.IsAlt) (original : Basis J F2 V) (Q : QuadraticForm F2 V)
    (x : V) : ∀ u, ¬weightedRel B hAlt original Q x u u := by
  intro u
  rcases u with i | ⟨i, a⟩
  · exact (WittFrame.frame B hAlt).mate_ne_self i
  · simp [weightedRel]

theorem weightedGraph_adj_iff (B : LinearMap.BilinForm F2 V)
    (hAlt : B.IsAlt) (original : Basis J F2 V) (Q : QuadraticForm F2 V)
    (x : V) (u v : Coin B hAlt original x) :
    (weightedGraph B hAlt original Q x).Adj u v ↔
      weightedRel B hAlt original Q x u v := by
  rw [weightedGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, huv | hvu⟩
    · exact huv
    · exact weightedRel_symm' B hAlt original Q x hvu
  · intro huv
    exact ⟨fun h ↦ weightedRel_irrefl' B hAlt original Q x u (h ▸ huv), Or.inl huv⟩

theorem strategicCharge_eq_ordered_edges (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V) :
    strategicCharge B hAlt original x =
      ∑ i : Active (adaptedBasis B hAlt) x,
        ∑ j : Active (adaptedBasis B hAlt) x,
          if (i : (WittFrame.frame B hAlt).Index) < j ∧
              (WittFrame.frame B hAlt).mate
                (i : (WittFrame.frame B hAlt).Index) =
                  some (j : (WittFrame.frame B hAlt).Index) then 1 else 0 := by
  let b := adaptedBasis B hAlt
  let Q₀ := publicQuadratic B original
  have hexp := PhysicalDeferred.quadratic_support_expansion Q₀ b x
  have hpolar : Q₀.polarBilin = B := publicQuadratic_polar B hAlt original
  rw [strategicCharge]
  rw [hexp]
  have hdiag :
      (∑ i ∈ (b.repr x).support, Q₀ (b i)) =
        diagonalSource Q₀ b x := by
    exact (diagonalSource_eq_support_sum Q₀ b x).symm
  rw [hdiag]
  change ((diagonalSource Q₀ b x +
    (∑ i ∈ (b.repr x).support, ∑ j ∈ (b.repr x).support,
      if i < j then QuadraticMap.polar Q₀ (b i) (b j) else 0)) +
        diagonalSource Q₀ b x) = _
  calc
    _ = (∑ i ∈ (b.repr x).support, ∑ j ∈ (b.repr x).support,
        if i < j then QuadraticMap.polar Q₀ (b i) (b j) else 0) +
          (diagonalSource Q₀ b x + diagonalSource Q₀ b x) := by abel
    _ = (∑ i ∈ (b.repr x).support, ∑ j ∈ (b.repr x).support,
        if i < j then QuadraticMap.polar Q₀ (b i) (b j) else 0) := by
      rw [CharTwo.add_self_eq_zero, add_zero]
    _ = _ := by
      rw [Finset.sum_subtype (b.repr x).support (fun _ ↦ Iff.rfl)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_subtype (b.repr x).support (fun _ ↦ Iff.rfl)]
      apply Finset.sum_congr rfl
      intro j hj
      change (if i < j then QuadraticMap.polar Q₀ (b i) (b j) else 0) = _
      change (if i < j then Q₀.polarBilin (b i) (b j) else 0) = _
      rw [hpolar]
      have hpair : B (b (i : (WittFrame.frame B hAlt).Index))
          (b (j : (WittFrame.frame B hAlt).Index)) =
          if (WittFrame.frame B hAlt).mate
              (i : (WittFrame.frame B hAlt).Index) =
                some (j : (WittFrame.frame B hAlt).Index) then 1 else 0 := by
        simpa [b, adaptedBasis] using
          (WittFrame.frame B hAlt).pairing
            (i : (WittFrame.frame B hAlt).Index)
            (j : (WittFrame.frame B hAlt).Index)
      rw [hpair]
      by_cases hij : i < j <;> simp [hij]

theorem coin_inl_lt (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V)
    (i j : Active (adaptedBasis B hAlt) x) :
    coinLess B hAlt original x (Sum.inl i) (Sum.inl j) ↔ i < j := by
  change Sum.Lex (fun a b : Active (adaptedBasis B hAlt) x ↦ a < b)
    (fun a b : Active original x × Fin 2 ↦ sourceLess original x a b)
    (Sum.inl i) (Sum.inl j) ↔ i < j
  exact Sum.lex_inl_inl

theorem coin_inr_lt (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V)
    (i j : Active original x × Fin 2) :
    coinLess B hAlt original x (Sum.inr i) (Sum.inr j) ↔
      sourceLess original x i j := by
  change Sum.Lex (fun a b : Active (adaptedBasis B hAlt) x ↦ a < b)
    (fun a b : Active original x × Fin 2 ↦ sourceLess original x a b)
    (Sum.inr i) (Sum.inr j) ↔ sourceLess original x i j
  exact Sum.lex_inr_inr

theorem source_same_lt (original : Basis J F2 V) (x : V)
    (i : Active original x) (a b : Fin 2) :
    sourceLess original x (i, a) (i, b) ↔ a < b := by
  change Prod.Lex (fun a b : Active original x ↦ a < b)
    (fun a b : Fin 2 ↦ a < b) (i, a) (i, b) ↔ a < b
  rw [Prod.lex_def]
  simp

theorem sourceCharge_eq_ordered_edges (Q : QuadraticForm F2 V) (original : Basis J F2 V)
    (x : V) :
    (∑ p : Active original x × Fin 2,
      ∑ q : Active original x × Fin 2,
        if sourceLess original x p q ∧ p.1 = q.1 ∧ p.2 ≠ q.2 ∧
          Q (original p.1) = 1
        then 1 else 0) = sourceCharge Q original x := by
  rw [sourceCharge, diagonalSource_eq_support_sum]
  have hrhs :
      (∑ i : Active original x, Q (original i)) =
        ∑ i ∈ (original.repr x).support, Q (original i) :=
    (Finset.sum_subtype (original.repr x).support (fun _ ↦ Iff.rfl)
      (fun i ↦ Q (original i))).symm
  rw [← hrhs]
  simp_rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  have hcollapse (a : Fin 2) :
      (∑ j : Active original x, ∑ b : Fin 2,
        if sourceLess original x (i, a) (j, b) ∧ i = j ∧ a ≠ b ∧
          Q (original i) = 1
        then (1 : F2) else 0) =
      ∑ b : Fin 2,
        if a < b ∧ a ≠ b ∧ Q (original i) = 1 then (1 : F2) else 0 := by
    classical
    rw [Fintype.sum_eq_single i]
    · apply Finset.sum_congr rfl
      intro b _
      simp only [source_same_lt, true_and]
    · intro j hji
      simp [Ne.symm hji]
  rw [Fin.sum_univ_two]
  calc
    _ = (∑ b : Fin 2,
          if (0 : Fin 2) < b ∧ 0 ≠ b ∧ Q (original i) = 1 then 1 else 0) +
        (∑ b : Fin 2,
          if (1 : Fin 2) < b ∧ 1 ≠ b ∧ Q (original i) = 1 then 1 else 0) :=
      congrArg₂ (fun a b : F2 ↦ a + b) (hcollapse 0) (hcollapse 1)
    _ = Q (original i) := by
      simp_rw [Fin.sum_univ_two]
      by_cases hQ : Q (original i) = 1
      · simp [hQ]
      · have hzero := Ogdoad.zmod2_eq_zero_of_ne_one _ hQ
        simp [hQ, hzero]

set_option maxHeartbeats 800000 in
theorem totalEdgeCharge_eq_strategic_add_source (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (Q : QuadraticForm F2 V) (x : V) :
    PhysicalDeferred.inducedEdgeCharge (weightedGraph B hAlt original Q x) Finset.univ =
      strategicCharge B hAlt original x + sourceCharge Q original x := by
  classical
  rw [PhysicalDeferred.inducedEdgeCharge]
  have hlt (u v : Coin B hAlt original x) :
      @LT.lt _ (coinLinearOrder B hAlt original x).toLT u v ↔
        coinLess B hAlt original x u v := Iff.rfl
  simp_rw [hlt]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  simp only [weightedGraph_adj_iff, weightedRel, and_false, if_false, add_zero,
    zero_add]
  simp only [Finset.sum_const_zero, add_zero, zero_add]
  congr 1
  · simp_rw [coin_inl_lt]
    exact (strategicCharge_eq_ordered_edges B hAlt original x).symm
  · simp_rw [coin_inr_lt]
    exact sourceCharge_eq_ordered_edges Q original x

/-- The public close label from the paper; source coins have zero close
charge. -/
noncomputable def closeWeight (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V) : Coin B hAlt original x → F2
  | .inl i => publicQuadratic B original (adaptedBasis B hAlt i)
  | .inr _ => 0

theorem sum_closeWeight (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (x : V) :
    (∑ v : Coin B hAlt original x, closeWeight B hAlt original x v) =
      closeCharge B hAlt original x := by
  rw [Fintype.sum_sum_type]
  simp only [closeWeight, Finset.sum_const_zero, add_zero, closeCharge]
  exact (Finset.sum_subtype ((adaptedBasis B hAlt).repr x).support
    (fun _ ↦ Iff.rfl)
    (fun i ↦ publicQuadratic B original (adaptedBasis B hAlt i))).symm

theorem scoreBit_chargeBool (z : F2) :
    ImpartialRealizer.scoreBit (chargeBool z) = z := by
  fin_cases z <;> decide

set_option maxHeartbeats 800000 in
theorem encoded_literal_root (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (Q : QuadraticForm F2 V) (x : V) :
    PhysicalDeferred.encode (weightedGraph B hAlt original Q x)
        (PhysicalDeferred.closeEncode (closeWeight B hAlt original x)
          (ImpartialRealizer.initial (V := Coin B hAlt original x) 0)) =
      ImpartialRealizer.initial
        (V := Coin B hAlt original x)
        (ImpartialRealizer.scoreBit
          (chargeBool (initialCharge B hAlt original Q x))) := by
  let G := weightedGraph B hAlt original Q x
  let c := closeWeight B hAlt original x
  simp only [PhysicalDeferred.encode, PhysicalDeferred.closeEncode,
    ImpartialRealizer.initial]
  congr 1
  rw [PhysicalDeferred.pendingCloseCharge, PhysicalDeferred.pendingEdgeCharge]
  have hedgeEmpty : PhysicalDeferred.inducedEdgeCharge
      (weightedGraph B hAlt original Q x) ∅ = 0 := by
    simp [PhysicalDeferred.inducedEdgeCharge]
  simp only [List.toFinset_nil, Finset.union_empty, Finset.sum_empty, add_zero,
    hedgeEmpty, zero_add]
  rw [totalEdgeCharge_eq_strategic_add_source B hAlt original Q x, sum_closeWeight B hAlt original x,
    initialCharge, scoreBit_chargeBool]
  abel

/-- Fully literal end-to-end theorem: score starts at zero, OPEN charges a
weighted edge exactly on its second endpoint, and CLOSE charges the public
strategic label. -/
theorem gold_literal_root_isP_iff (B : LinearMap.BilinForm F2 V) (hAlt : B.IsAlt)
    (original : Basis J F2 V) (Q : QuadraticForm F2 V)
    (hpolar : Q.polarBilin = B) (x : V) :
    PhysicalDeferred.LiteralTailWins (weightedGraph B hAlt original Q x)
      (closeWeight B hAlt original x) true
      (ImpartialRealizer.initial (V := Coin B hAlt original x) 0) ↔
      Q x = 0 := by
  let root := ImpartialRealizer.initial (V := Coin B hAlt original x) 0
  have hroot : WellFormed root := by simp [root, WellFormed, ImpartialRealizer.initial]
  rw [PhysicalDeferred.literalTailWins_iff hroot]
  have hclose : WellFormed
      (PhysicalDeferred.closeEncode (closeWeight B hAlt original x) root) := hroot
  rw [PhysicalDeferred.physicalTailWins_iff hclose]
  rw [show PhysicalDeferred.encode (weightedGraph B hAlt original Q x)
      (PhysicalDeferred.closeEncode (closeWeight B hAlt original x) root) =
      ImpartialRealizer.initial
        (V := Coin B hAlt original x)
        (ImpartialRealizer.scoreBit
          (chargeBool (initialCharge B hAlt original Q x))) by
    simpa [root] using encoded_literal_root B hAlt original Q x]
  refine (@ImpartialRealizer.root_isP_iff_charge_zero
    (Coin B hAlt original x) inferInstance LinearOrder.toDecidableEq
    (publicGraph B hAlt original x) (weightedGraph B hAlt original Q x)
    (publicGraph_isMatching B hAlt original x)
    (weightedGraph_le_public B hAlt original Q x)
    (chargeBool (initialCharge B hAlt original Q x))).trans ?_
  rw [chargeBool_eq_false_iff,
    initialCharge_eq_quadratic B hAlt original Q hpolar x]
end Ogdoad.GoldArena
