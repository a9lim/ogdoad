import Ogdoad.MisereParityTrace

/-!
# Two-element ideals in valid misere quotients

A finite overflow marker cannot be repaired merely by adding the star phase.
Any nontrivial reduced valid quotient with a two-element ideal is already the
two-element quotient. No finiteness assumption on the ambient monoid is used.
-/

namespace Ogdoad.MisereIdealObstruction

open Set
open Ogdoad.MisereTransition
open Ogdoad.MisereNaturalUniversality
open Ogdoad.MisereParityTrace

variable {Q : Type*} [CommMonoid Q]

/-- An option remains different from its source after multiplication by
every context, even when multiplication is not cancellative. -/
theorem option_mul_ne_value_mul
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hP : P.Nonempty) (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {t : Transition Q} (ht : t ∈ T) {e : Q} (he : e ∈ t.options)
    (z : Q) : e * z ≠ t.value * z := by
  obtain ⟨F, hzT, _⟩ := hranked z
  have hnot := value_not_mem_own_options hP hterminal hreduced hclosed
    hparity hranked (hclosed ht hzT)
  intro heq
  apply hnot
  exact Or.inl ⟨e, he, by simpa [product, mul_comm] using heq⟩

/-- If one principal ideal consists only of a star pair, rank induction
forces every quotient value to be the identity or the star. -/
theorem binary_principal_ideal_forces_binary
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {a : Q} (hstar : Transition.mk a ({1} : Set Q) ∈ T)
    (z : Q) (hbinary : ∀ q : Q, q * z = z ∨ q * z = a * z) :
    ∀ q : Q, q = 1 ∨ q = a := by
  classical
  have h1P : (1 : Q) ∉ P := by
    intro h
    have := (hparity hterminal).mp h
    simpa using this.1
  have haP : a ∈ P := (hparity hstar).mpr
    ⟨⟨1, by simp⟩, by simpa using h1P⟩
  have ha2 := star_square_eq_one hterminal hreduced hclosed hparity hranked hstar
  have hback : Transition.mk 1 ({a} : Set Q) ∈ T := by
    simpa [ha2] using unary_chain_transition hclosed hstar 1
  intro q
  induction q using (measure R).wf.induction with
  | h q ih =>
    obtain ⟨E, hqT, hdesc⟩ := hranked q
    have hsmall : ∀ e ∈ E, e = 1 ∨ e = a := by
      intro e he
      exact ih e (hdesc e he)
    have hnotboth : ¬(1 ∈ E ∧ a ∈ E) := by
      rintro ⟨h1, ha⟩
      rcases hbinary q with hq | hq
      · exact option_mul_ne_value_mul ⟨a, haP⟩ hterminal hreduced hclosed
          hparity hranked hqT h1 z (by simpa using hq.symm)
      · exact option_mul_ne_value_mul ⟨a, haP⟩ hterminal hreduced hclosed
          hparity hranked hqT ha z hq.symm
    by_cases h1 : 1 ∈ E
    · have hE : E = ({1} : Set Q) := by
        ext e
        constructor
        · intro he
          rcases hsmall e he with he1 | hea
          · simp [he1]
          · exact False.elim (hnotboth ⟨h1, by simpa [hea] using he⟩)
        · intro he
          simpa using (show e = 1 from he) ▸ h1
      exact Or.inr (value_eq_of_options_eq hreduced hclosed hparity hranked
        hqT hstar hE)
    · by_cases ha : a ∈ E
      · have hE : E = ({a} : Set Q) := by
          ext e
          constructor
          · intro he
            rcases hsmall e he with he1 | hea
            · exact False.elim (h1 (by simpa [he1] using he))
            · simp [hea]
          · intro he
            simpa using (show e = a from he) ▸ ha
        exact Or.inl (value_eq_of_options_eq hreduced hclosed hparity hranked
          hqT hback hE)
      · have hE : E = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro e he
          rcases hsmall e he with he1 | hea
          · exact h1 (by simpa [he1] using he)
          · exact ha (by simpa [hea] using he)
        exact Or.inl (value_eq_of_options_eq hreduced hclosed hparity hranked
          hqT hterminal hE)

/-- A two-element ideal in a reduced valid quotient forces the entire
quotient, including its distinguished portion, to be the star quotient.
The finite ideal is an explicit witness; the ambient monoid may be infinite. -/
theorem two_element_ideal_forces_star_quotient
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R) (hR1 : R 1 = 0)
    (I : Finset Q) (hcard : I.card = 2)
    (hideal : ∀ q z : Q, z ∈ I → q * z ∈ I) :
    ∃ a : Q, a ≠ 1 ∧ a ^ 2 = 1 ∧ P = {a} ∧ ∀ q : Q, q = 1 ∨ q = a := by
  classical
  obtain ⟨u, v, huv, hI⟩ := Finset.card_eq_two.mp hcard
  have hne : ∃ q : Q, q ≠ 1 := by
    by_cases hu : u = 1
    · exact ⟨v, by simpa [hu] using Ne.symm huv⟩
    · exact ⟨u, hu⟩
  obtain ⟨a, ha1, hstar⟩ := exists_star_transition
    hreduced hclosed hparity hranked hR1 hne
  obtain ⟨F, h1T, hdesc⟩ := hranked (1 : Q)
  have hF : F = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro f hf
    have := hdesc f hf
    omega
  have hterminal : Transition.mk 1 ∅ ∈ T := by simpa [hF] using h1T
  have hau : a * u = v := by
    have hmem := hideal a u (by simp [hI])
    have hneq := star_mul_ne_self hterminal hreduced hclosed hparity hranked hstar u
    simpa [hI, hneq] using hmem
  have hbinary : ∀ q : Q, q * u = u ∨ q * u = a * u := by
    intro q
    have hmem := hideal q u (by simp [hI])
    simpa [hI, hau] using hmem
  have hwhole := binary_principal_ideal_forces_binary
    hterminal hreduced hclosed hparity hranked hstar u hbinary
  have h1P : (1 : Q) ∉ P := by
    intro h
    have := (hparity hterminal).mp h
    simpa using this.1
  have haP : a ∈ P := (hparity hstar).mpr
    ⟨⟨1, by simp⟩, by simpa using h1P⟩
  have hP : P = {a} := by
    ext q
    rcases hwhole q with rfl | rfl <;> simp [h1P, haP, Ne.symm ha1]
  exact ⟨a, ha1, star_square_eq_one hterminal hreduced hclosed hparity hranked hstar,
    hP, hwhole⟩

end Ogdoad.MisereIdealObstruction
