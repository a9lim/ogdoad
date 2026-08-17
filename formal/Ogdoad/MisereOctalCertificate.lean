import Ogdoad.MisereTransition

/-!
# Exact periodic certificates for finite octal traces

This module upgrades periodicity of the bare split convolution to periodicity
of the complete option-value record of a finite octal code.  In particular,
once a proposed heap word is ultimately periodic, membership of one full
period of tail records in a transition table certifies membership of every
later record.  No bounded-game or bounded-multiplicity computation appears
in the statement.

The three masks use the usual octal convention: `whole` permits removal of a
whole heap, `one` permits one nonempty remainder, and `two` permits two
nonempty remainders.  Equal parts are included; passing to unordered splits
does not change their set of quotient values in a commutative monoid.
-/

namespace Ogdoad.MisereOctalCertificate

open Set
open Ogdoad.MisereTransition

variable {Q : Type*} [CommMonoid Q]

section ExactQuotient

variable {G : Type*}

/-- The defining previous-player-win recurrence for a well-founded misere
ruleset.  The terminal position has no options and is therefore not in `W`. -/
def MisereRecurrence (options : G → Set G) (W : G → Prop) : Prop :=
  ∀ g, W g ↔ (options g).Nonempty ∧ ∀ h ∈ options g, ¬W h

/-- Contextual indistinguishability in a universe closed under sum. -/
def Indistinguishable [Add G] (W : G → Prop) (g h : G) : Prop :=
  ∀ z, W (g + z) ↔ W (h + z)

omit [CommMonoid Q] in
/-- Transition-table parity proves outcome correctness for every position,
not only for heaps, once every option decreases a rank and every position's
exact option image is a table record. -/
theorem outcome_iff_value_mem
    {P : Set Q} {T : Set (Transition Q)}
    {options : G → Set G} {W : G → Prop} {rank : G → Nat} {value : G → Q}
    (hdesc : ∀ g h, h ∈ options g → rank h < rank g)
    (hrecurrence : MisereRecurrence options W)
    (hparity : ParityTable P T)
    (hrecord : ∀ g, Transition.mk (value g) (value '' options g) ∈ T) :
    ∀ g, W g ↔ value g ∈ P := by
  intro g
  induction g using (measure rank).wf.induction with
  | h g ih =>
      have htable :
          ParityCorrect P (Transition.mk (value g) (value '' options g)) :=
        hparity (hrecord g)
      change value g ∈ P ↔
        (value '' options g).Nonempty ∧ ∀ q ∈ value '' options g, q ∉ P at htable
      rw [hrecurrence g, htable]
      constructor
      · rintro ⟨⟨h, hh⟩, hall⟩
        refine ⟨⟨value h, h, hh, rfl⟩, ?_⟩
        rintro q ⟨k, hk, rfl⟩ hkP
        exact hall k hk ((ih k (hdesc g k hk)).mpr hkP)
      · rintro ⟨⟨q, h, hh, rfl⟩, hall⟩
        refine ⟨⟨h, hh⟩, ?_⟩
        intro k hk hkW
        exact hall (value k) ⟨k, hk, rfl⟩ ((ih k (hdesc g k hk)).mp hkW)

/-- **Exact quotient certificate.** Suppose position values multiply under
sum, every quotient value is represented by a position, and table parity has
already proved the outcome criterion.  Then equality of values is exactly
contextual indistinguishability.  Reduction supplies a separating context in
the converse direction. -/
theorem value_eq_iff_indistinguishable
    [Add G] {P : Set Q} {W : G → Prop} {value : G → Q}
    (hreduced : Reduced P)
    (houtcome : ∀ g, W g ↔ value g ∈ P)
    (hadd : ∀ g h, value (g + h) = value g * value h)
    (hsurjective : Function.Surjective value) (g h : G) :
    value g = value h ↔ Indistinguishable W g h := by
  constructor
  · intro hvalue z
    rw [houtcome, houtcome, hadd, hadd, hvalue]
  · intro hindist
    by_contra hne
    obtain ⟨q, hsep⟩ := hreduced hne
    obtain ⟨z, rfl⟩ := hsurjective q
    have hsame : value g * value z ∈ P ↔ value h * value z ∈ P := by
      rw [← hadd, ← hadd, ← houtcome, ← houtcome]
      exact hindist z
    rcases hsep with hsep | hsep
    · exact hsep.2 (hsame.mp hsep.1)
    · exact hsep.1 (hsame.mpr hsep.2)

/-- The rank/parity and reduction arguments combine into one reusable exact
quotient theorem. -/
theorem exact_quotient_of_transition_certificate
    [Add G] {P : Set Q} {T : Set (Transition Q)}
    {options : G → Set G} {W : G → Prop} {rank : G → Nat} {value : G → Q}
    (hdesc : ∀ g h, h ∈ options g → rank h < rank g)
    (hrecurrence : MisereRecurrence options W)
    (hparity : ParityTable P T)
    (hrecord : ∀ g, Transition.mk (value g) (value '' options g) ∈ T)
    (hreduced : Reduced P)
    (hadd : ∀ g h, value (g + h) = value g * value h)
    (hsurjective : Function.Surjective value) (g h : G) :
    value g = value h ↔ Indistinguishable W g h := by
  apply value_eq_iff_indistinguishable hreduced
  · exact outcome_iff_value_mem hdesc hrecurrence hparity hrecord
  · exact hadd
  · exact hsurjective

end ExactQuotient

/-- Quotient values of options that leave one nonempty heap. -/
def oneRemainderOptions (x : Nat → Q) (one : Set Nat) (n : Nat) : Set Q :=
  {q | ∃ k, k ∈ one ∧ k < n ∧ q = x (n - k)}

/-- Quotient values of options that leave two nonempty heaps. -/
def twoRemainderOptions (x : Nat → Q) (two : Set Nat) (n : Nat) : Set Q :=
  {q | ∃ k, k ∈ two ∧ k + 2 ≤ n ∧ q ∈ splitSet x (n - k)}

/-- The terminal quotient value contributed by a whole-heap removal. -/
def wholeHeapOptions (whole : Set Nat) (n : Nat) : Set Q :=
  {q | q = 1 ∧ n ∈ whole}

/-- The complete option-value set for a heap of size `n`. -/
def octalOptions
    (x : Nat → Q) (whole one two : Set Nat) (n : Nat) : Set Q :=
  wholeHeapOptions whole n ∪
    oneRemainderOptions x one n ∪ twoRemainderOptions x two n

/-- All nonzero digits of the three octal masks occur by place `d`. -/
def MasksBounded
    (whole one two : Set Nat) (d : Nat) : Prop :=
  (∀ k, k ∈ whole → k ≤ d) ∧
    (∀ k, k ∈ one → k ≤ d) ∧
    ∀ k, k ∈ two → k ≤ d

theorem wholeHeapOptions_eq_empty_of_bound
    {whole : Set Nat} {d n : Nat}
    (hwhole : ∀ k, k ∈ whole → k ≤ d) (hdn : d < n) :
    wholeHeapOptions (Q := Q) whole n = ∅ := by
  have hn : n ∉ whole := by
    intro hn
    exact (not_le_of_gt hdn) (hwhole n hn)
  ext q
  simp [wholeHeapOptions, hn]

omit [CommMonoid Q] in
/-- The one-remainder contribution inherits the period of the heap word once
all permitted removals lie wholly inside the periodic tail. -/
theorem oneRemainderOptions_add_period
    (x : Nat → Q) {one : Set Nat} {d N p n : Nat}
    (hN : 1 ≤ N) (hp : 1 ≤ p)
    (hone : ∀ k, k ∈ one → k ≤ d)
    (hperiod : ∀ m, N ≤ m → x (m + p) = x m)
    (hn : 2 * N + p + d ≤ n) :
    oneRemainderOptions x one (n + p) = oneRemainderOptions x one n := by
  ext q
  constructor
  · rintro ⟨k, hk, _, hq⟩
    have hkd : k ≤ d := hone k hk
    have hkn : k < n := by omega
    have hNk : N ≤ n - k := by omega
    have hidx : n + p - k = (n - k) + p := by omega
    refine ⟨k, hk, hkn, ?_⟩
    rw [hidx, hperiod (n - k) hNk] at hq
    exact hq
  · rintro ⟨k, hk, hkn, hq⟩
    have hkd : k ≤ d := hone k hk
    have hNk : N ≤ n - k := by omega
    have hidx : n + p - k = (n - k) + p := by omega
    refine ⟨k, hk, by omega, ?_⟩
    rw [hidx, hperiod (n - k) hNk]
    exact hq

/-- The two-remainder contribution inherits the period of the heap word past
the explicit preperiod-crossing bound. -/
theorem twoRemainderOptions_add_period
    (x : Nat → Q) {two : Set Nat} {d N p n : Nat}
    (hN : 1 ≤ N) (hp : 1 ≤ p)
    (htwo : ∀ k, k ∈ two → k ≤ d)
    (hperiod : ∀ m, N ≤ m → x (m + p) = x m)
    (hn : 2 * N + p + d ≤ n) :
    twoRemainderOptions x two (n + p) = twoRemainderOptions x two n := by
  ext q
  constructor
  · rintro ⟨k, hk, _, hq⟩
    have hkd : k ≤ d := htwo k hk
    have hres : 2 * N + p ≤ n - k := by omega
    have hidx : n + p - k = (n - k) + p := by omega
    have hsplit : splitSet x ((n - k) + p) = splitSet x (n - k) :=
      splitSet_add_period x hN hp hperiod hres
    refine ⟨k, hk, by omega, ?_⟩
    rw [hidx, hsplit] at hq
    exact hq
  · rintro ⟨k, hk, hkn, hq⟩
    have hkd : k ≤ d := htwo k hk
    have hres : 2 * N + p ≤ n - k := by omega
    have hidx : n + p - k = (n - k) + p := by omega
    have hsplit : splitSet x ((n - k) + p) = splitSet x (n - k) :=
      splitSet_add_period x hN hp hperiod hres
    refine ⟨k, hk, by omega, ?_⟩
    rw [hidx, hsplit]
    exact hq

/-- A finite octal code applied to an ultimately periodic heap word has an
ultimately periodic complete option-value word. -/
theorem octalOptions_add_period
    (x : Nat → Q) {whole one two : Set Nat} {d N p n : Nat}
    (hN : 1 ≤ N) (hp : 1 ≤ p)
    (hbounded : MasksBounded whole one two d)
    (hperiod : ∀ m, N ≤ m → x (m + p) = x m)
    (hn : 2 * N + p + d ≤ n) :
    octalOptions x whole one two (n + p) =
      octalOptions x whole one two n := by
  rcases hbounded with ⟨hwhole, hone, htwo⟩
  have hdn : d < n := by omega
  have hdnp : d < n + p := by omega
  unfold octalOptions
  rw [wholeHeapOptions_eq_empty_of_bound hwhole hdnp]
  rw [wholeHeapOptions_eq_empty_of_bound hwhole hdn]
  rw [oneRemainderOptions_add_period x hN hp hone hperiod hn]
  rw [twoRemainderOptions_add_period x hN hp htwo hperiod hn]

/-- The complete transition record attached to one heap. -/
def octalRecord
    (x : Nat → Q) (whole one two : Set Nat) (n : Nat) : Transition Q :=
  Transition.mk (x n) (octalOptions x whole one two n)

/-- An exact octal heap record in a reduced ranked parity table cannot contain
its own heap value among its option values. -/
theorem octal_value_not_mem_own_options
    (x : Nat → Q) {whole one two : Set Nat}
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat} {n : Nat}
    (hP : P.Nonempty) (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hrecord : octalRecord x whole one two n ∈ T) :
    x n ∉ octalOptions x whole one two n := by
  simpa [octalRecord] using
    value_not_mem_own_options hP hterminal hreduced hclosed hparity hranked hrecord

/-- If the whole-heap bit is present at `n`, the value of `H_n` cannot be the
terminal value. -/
theorem octal_whole_bit_value_ne_one
    (x : Nat → Q) {whole one two : Set Nat}
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat} {n : Nat}
    (hP : P.Nonempty) (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hrecord : octalRecord x whole one two n ∈ T)
    (hnwhole : n ∈ whole) :
    x n ≠ 1 := by
  intro hxn
  apply octal_value_not_mem_own_options x hP hterminal hreduced hclosed
    hparity hranked hrecord
  simp [octalOptions, wholeHeapOptions, hnwhole, hxn]

/-- If removing `k` may leave one nonempty heap, a heap cannot have the same
value as that remainder. -/
theorem octal_one_bit_value_ne_remainder
    (x : Nat → Q) {whole one two : Set Nat}
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat} {n k : Nat}
    (hP : P.Nonempty) (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hrecord : octalRecord x whole one two n ∈ T)
    (hkone : k ∈ one) (hkn : k < n) :
    x n ≠ x (n - k) := by
  intro hxn
  apply octal_value_not_mem_own_options x hP hterminal hreduced hclosed
    hparity hranked hrecord
  simp only [octalOptions, mem_union]
  exact Or.inl (Or.inr ⟨k, hkone, hkn, hxn⟩)

/-- If removing `k` may leave two nonempty heaps of sizes `i,j`, the source
heap cannot have the product of those two heap values. -/
theorem octal_two_bit_value_ne_split_product
    (x : Nat → Q) {whole one two : Set Nat}
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    {n k i j : Nat}
    (hP : P.Nonempty) (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hrecord : octalRecord x whole one two n ∈ T)
    (hktwo : k ∈ two) (hkn : k + 2 ≤ n)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i + j = n - k) :
    x n ≠ x i * x j := by
  intro hxn
  apply octal_value_not_mem_own_options x hP hterminal hreduced hclosed
    hparity hranked hrecord
  simp only [octalOptions, mem_union]
  exact Or.inr ⟨k, hktwo, hkn, ⟨i, j, hi, hj, hij, hxn⟩⟩

/-- Both fields of the heap transition record inherit the asserted period. -/
theorem octalRecord_add_period
    (x : Nat → Q) {whole one two : Set Nat} {d N p n : Nat}
    (hN : 1 ≤ N) (hp : 1 ≤ p)
    (hbounded : MasksBounded whole one two d)
    (hperiod : ∀ m, N ≤ m → x (m + p) = x m)
    (hn : 2 * N + p + d ≤ n) :
    octalRecord x whole one two (n + p) =
      octalRecord x whole one two n := by
  unfold octalRecord
  rw [hperiod n (by omega)]
  rw [octalOptions_add_period x hN hp hbounded hperiod hn]

/-- **Exact infinite-tail certificate.** If the heap word has an asserted
period and the `p` records in one tail period belong to a transition table,
then every later record belongs to that table. -/
theorem octalRecord_mem_of_fundamental_period
    (x : Nat → Q) {whole one two : Set Nat} {T : Set (Transition Q)}
    {d N p B : Nat}
    (hN : 1 ≤ N) (hp : 1 ≤ p)
    (hbounded : MasksBounded whole one two d)
    (hperiod : ∀ m, N ≤ m → x (m + p) = x m)
    (hB : 2 * N + p + d ≤ B)
    (hfundamental : ∀ n, B ≤ n → n < B + p →
      octalRecord x whole one two n ∈ T) :
    ∀ n, B ≤ n → octalRecord x whole one two n ∈ T := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hfirst : n < B + p
      · exact hfundamental n hn hfirst
      · have hBp : B + p ≤ n := by omega
        have hpn : p ≤ n := by omega
        have hnsub : B ≤ n - p := by omega
        have hlower : 2 * N + p + d ≤ n - p := le_trans hB hnsub
        have hlt : n - p < n := by omega
        have hprevious : octalRecord x whole one two (n - p) ∈ T :=
          ih (n - p) hlt hnsub
        have hrecord :=
          octalRecord_add_period x hN hp hbounded hperiod hlower
        have hdecomp : n - p + p = n := Nat.sub_add_cancel hpn
        rw [hdecomp] at hrecord
        rw [hrecord]
        exact hprevious

/-- A finite prefix through the first certified tail period proves transition-
table membership for the complete infinite heap trace. -/
theorem octalRecord_mem_of_finite_certificate
    (x : Nat → Q) {whole one two : Set Nat} {T : Set (Transition Q)}
    {d N p B : Nat}
    (hN : 1 ≤ N) (hp : 1 ≤ p)
    (hbounded : MasksBounded whole one two d)
    (hperiod : ∀ m, N ≤ m → x (m + p) = x m)
    (hB : 2 * N + p + d ≤ B)
    (hfinite : ∀ n, n < B + p → octalRecord x whole one two n ∈ T) :
    ∀ n, octalRecord x whole one two n ∈ T := by
  intro n
  by_cases hn : B ≤ n
  · apply octalRecord_mem_of_fundamental_period x hN hp hbounded hperiod hB
    · intro m hmB hm
      exact hfinite m hm
    · exact hn
  · apply hfinite n
    omega

end Ogdoad.MisereOctalCertificate
