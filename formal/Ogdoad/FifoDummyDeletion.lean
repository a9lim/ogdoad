import Ogdoad.Fifo

/-!
# Dummy deletion has two adjacent ko walls

The permutation--threshold normal form records a complete FIFO schedule by
the number `r b` of CLOSEs before its `b`-th OPEN.  Deleting the vertex in
opening position `j` deletes its FIFO-close coordinate as well.  The resulting
raw real threshold word can violate the ko condition, but only at the two
positions adjacent to `j`.  Both violations can occur simultaneously.

This corrects the tempting stronger assertion that dummy deletion creates at
most one internal ko wall.  The result is graph-independent; the final theorem
also kernel-checks the minimal four-vertex legal FIFO schedule exhibiting the
two-wall phenomenon against the authoritative `step` semantics.
-/

namespace Ogdoad.Fifo

noncomputable section

/-! ## Threshold deletion -/

/-- The arithmetic conditions on a length-`n` threshold word.  Only values at
indices below `n` matter. -/
def ThresholdLegal (n : Nat) (r : Nat → Nat) : Prop :=
  r 0 = 0 ∧
  (∀ a b, a < n → b < n → a ≤ b → r a ≤ r b) ∧
  (∀ b, b < n → r b ≤ b) ∧
  (∀ b, b + 1 < n → r b = b → r (b + 1) = b)

/-- Delete the vertex in zero-based opening position `j`.  Before `j` the
threshold is unchanged.  Afterwards its old index increases by one, and its
close count drops by one exactly when the deleted FIFO coordinate has already
closed. -/
def eraseThreshold (j : Nat) (r : Nat → Nat) (k : Nat) : Nat :=
  if k < j then r k
  else r (k + 1) - if j < r (k + 1) then 1 else 0

/-- Any internal ko violation created by deleting one FIFO coordinate is at
one of the two adjacent projected ranks: immediately before the deleted OPEN
rank, or at that rank. -/
theorem threshold_violation_after_erase_adjacent
    {n j k : Nat} {r : Nat → Nat}
    (hr : ThresholdLegal n r) (hk : k + 2 < n)
    (hhere : eraseThreshold j r k = k)
    (hnext : eraseThreshold j r (k + 1) ≠ k) :
    j = k ∨ j = k + 1 := by
  rcases hr with ⟨_hzero, hmono, hbound, hko⟩
  by_contra hadj
  push Not at hadj
  rcases lt_or_gt_of_ne hadj.1 with hjk | hkj
  · have hjk' : j < k := hjk
    have hcut : j < r (k + 1) := by
      by_contra hnot
      have herase : eraseThreshold j r k = r (k + 1) := by
        rw [eraseThreshold, if_neg (by omega), if_neg hnot, Nat.sub_zero]
      have hrk : r (k + 1) = k := by omega
      exact hnot (by omega)
    have herase : eraseThreshold j r k = r (k + 1) - 1 := by
      rw [eraseThreshold, if_neg (by omega), if_pos hcut]
    have hrmax : r (k + 1) = k + 1 := by
      have hub := hbound (k + 1) (by omega)
      omega
    have hrnext : r (k + 2) = k + 1 :=
      hko (k + 1) (by omega) hrmax
    have hcutNext : j < r (k + 2) := by omega
    have heraseNext : eraseThreshold j r (k + 1) = k := by
      rw [eraseThreshold, if_neg (by omega), hrnext, if_pos (by omega)]
      omega
    exact hnext heraseNext
  · have hjFar : k + 1 < j := by
      have hne := hadj.2
      omega
    have hrk : r k = k := by
      simpa [eraseThreshold, show k < j by omega] using hhere
    have hrnext : r (k + 1) = k := hko k (by omega) hrk
    have heraseNext : eraseThreshold j r (k + 1) = k := by
      simp [eraseThreshold, show k + 1 < j by omega, hrnext]
    exact hnext heraseNext

/-! ## Sharp four-vertex witness -/

/-- Threshold word `(0,0,1,3)`. -/
def twoKoWallThreshold : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 3
  | _ => 0

theorem twoKoWallThreshold_legal :
    ThresholdLegal 4 twoKoWallThreshold := by
  constructor
  · rfl
  constructor
  · intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      simp [twoKoWallThreshold] at *
  constructor
  · intro b hb
    interval_cases b <;> simp [twoKoWallThreshold]
  · intro b hb hmax
    have hb' : b ≤ 2 := by omega
    interval_cases b <;> simp [twoKoWallThreshold] at *

/-- Deleting opening rank `1` from `(0,0,1,3)` produces `(0,1,2)`.
Consequently the raw projected word violates ko after each of its first two
OPENs; these are both adjacent ranks allowed by the preceding theorem. -/
theorem two_ko_walls_after_threshold_erase :
    eraseThreshold 1 twoKoWallThreshold 0 = 0 ∧
    eraseThreshold 1 twoKoWallThreshold 1 ≠ 0 ∧
    eraseThreshold 1 twoKoWallThreshold 1 = 1 ∧
    eraseThreshold 1 twoKoWallThreshold 2 ≠ 1 := by
  decide

/-! ## The single exchange repairs both adjacent walls -/

/-- A ko violation in a raw threshold word. -/
def ThresholdKoViolation (r : Nat → Nat) (k : Nat) : Prop :=
  r k = k ∧ r (k + 1) ≠ k

/-- Move the later OPEN in `O_(j-1), C_(j-1), O_j` before the CLOSE.  In
threshold coordinates this lowers exactly the `j`-th threshold by one. -/
def repairEarlierKoWall (j : Nat) (r : Nat → Nat) (b : Nat) : Nat :=
  if b = j then j - 1 else r b

/-- When both adjacent raw ko violations occur, repairing the earlier one
removes both: the earlier implication now has the required equal successor,
while the later index is no longer maximal, so its ko antecedent is false. -/
theorem repair_earlier_ko_wall_removes_both
    {j : Nat} {r : Nat → Nat} (hj : 0 < j)
    (hprev : ThresholdKoViolation r (j - 1))
    (hhere : ThresholdKoViolation r j) :
    ¬ThresholdKoViolation (repairEarlierKoWall j r) (j - 1) ∧
      ¬ThresholdKoViolation (repairEarlierKoWall j r) j := by
  have hjpred : j - 1 + 1 = j := by omega
  rcases hprev with ⟨hprevAt, hprevNext⟩
  rcases hhere with ⟨hhereAt, hhereNext⟩
  constructor
  · intro hbad
    exact hbad.2 (by simp [repairEarlierKoWall, hjpred])
  · intro hbad
    have hrepair : repairEarlierKoWall j r j = j - 1 := by
      simp [repairEarlierKoWall]
    rcases hbad with ⟨hbadAt, _hbadNext⟩
    rw [hrepair] at hbadAt
    omega

/-- In zero-based threshold coordinates, two opening ranks `a < b` have
disjoint FIFO intervals exactly when `a < r b`. -/
def ThresholdSeparated (r : Nat → Nat) (a b : Nat) : Prop :=
  a < b ∧ a < r b

/-- The repair removes the separation edge joining opening ranks `j-1,j`. -/
theorem repair_earlier_ko_wall_removes_edge
    {j : Nat} {r : Nat → Nat} (hj : 0 < j) (hrj : r j = j) :
    ThresholdSeparated r (j - 1) j ∧
      ¬ThresholdSeparated (repairEarlierKoWall j r) (j - 1) j := by
  constructor
  · exact ⟨by omega, by omega⟩
  · intro hsep
    have hlt := hsep.2
    simp [repairEarlierKoWall] at hlt

/-- Every other separation coordinate is unchanged.  Together with
`repair_earlier_ko_wall_removes_edge`, this says that the schedule exchange
changes exactly one coordinate of the real disjointness vector. -/
theorem repair_earlier_ko_wall_preserves_other_edges
    {j a b : Nat} {r : Nat → Nat} (hj : 0 < j) (hrj : r j = j)
    (hoff : ¬(a = j - 1 ∧ b = j)) :
    ThresholdSeparated (repairEarlierKoWall j r) a b ↔
      ThresholdSeparated r a b := by
  by_cases hbj : b = j
  · subst b
    have hrepair : repairEarlierKoWall j r j = j - 1 := by
      simp [repairEarlierKoWall]
    simp only [ThresholdSeparated]
    rw [hrepair, hrj]
    constructor
    · rintro ⟨haj, hapred⟩
      exact ⟨haj, by omega⟩
    · rintro ⟨haj, haj'⟩
      refine ⟨haj, ?_⟩
      by_contra hnot
      have haeq : a = j - 1 := by omega
      exact hoff ⟨haeq, rfl⟩
  · simp [ThresholdSeparated, repairEarlierKoWall, hbj]

/-! ## General one-exchange legalization -/

/-- Threshold conditions other than ko. -/
def ThresholdCoreLegal (n : Nat) (r : Nat → Nat) : Prop :=
  r 0 = 0 ∧
  (∀ a b, a < n → b < n → a ≤ b → r a ≤ r b) ∧
  (∀ b, b < n → r b ≤ b)

private def eraseCloseCount (j x : Nat) : Nat :=
  x - if j < x then 1 else 0

private theorem eraseCloseCount_mono {j x y : Nat} (hxy : x ≤ y) :
    eraseCloseCount j x ≤ eraseCloseCount j y := by
  unfold eraseCloseCount
  by_cases hx : j < x <;> by_cases hy : j < y <;>
    simp [hx, hy] <;> omega

private theorem le_eraseCloseCount_of_lt
    {j x y : Nat} (hxj : x < j) (hxy : x ≤ y) :
    x ≤ eraseCloseCount j y := by
  unfold eraseCloseCount
  by_cases hy : j < y <;> simp [hy] <;> omega

private theorem eraseCloseCount_le_index
    {j k x : Nat} (hjk : j ≤ k) (hx : x ≤ k + 1) :
    eraseCloseCount j x ≤ k := by
  unfold eraseCloseCount
  by_cases hjx : j < x <;> simp [hjx] <;> omega

/-- Deleting one opening/FIFO-close coordinate preserves the initial value,
monotonicity, and the threshold bounds.  Only the ko implications can fail. -/
theorem eraseThreshold_coreLegal
    {n j : Nat} {r : Nat → Nat} (hn : 2 ≤ n) (hj : j < n)
    (hr : ThresholdLegal n r) :
    ThresholdCoreLegal (n - 1) (eraseThreshold j r) := by
  rcases hr with ⟨hzero, hmono, hbound, _hko⟩
  constructor
  · by_cases hj0 : j = 0
    · subst j
      have hr1 := hbound 1 (by omega)
      by_cases hz : r 1 = 0
      · simp [eraseThreshold, hz]
      · have hone : r 1 = 1 := by omega
        simp [eraseThreshold, hone]
    · have h0j : 0 < j := by omega
      simpa [eraseThreshold, h0j] using hzero
  constructor
  · intro a b ha hb hab
    have haN : a < n := by omega
    have hbN : b + 1 < n := by omega
    by_cases haj : a < j
    · by_cases hbj : b < j
      · simpa [eraseThreshold, haj, hbj] using
          hmono a b haN (by omega) hab
      · have har : r a < j :=
          lt_of_le_of_lt (hbound a haN) haj
        have hrab : r a ≤ r (b + 1) :=
          hmono a (b + 1) haN hbN (by omega)
        have hcross : r a ≤ eraseCloseCount j (r (b + 1)) :=
          le_eraseCloseCount_of_lt har hrab
        simpa [eraseThreshold, haj, hbj, eraseCloseCount] using hcross
    · have hbj : ¬b < j := by omega
      have hrab : r (a + 1) ≤ r (b + 1) :=
        hmono (a + 1) (b + 1) (by omega) hbN (by omega)
      have hadjust := eraseCloseCount_mono (j := j) hrab
      simpa [eraseThreshold, haj, hbj, eraseCloseCount] using hadjust
  · intro b hb
    by_cases hbj : b < j
    · simpa [eraseThreshold, hbj] using hbound b (by omega)
    · have hrb := hbound (b + 1) (by omega)
      have hadjust := eraseCloseCount_le_index
        (j := j) (k := b) (x := r (b + 1)) (by omega) hrb
      simpa [eraseThreshold, hbj, eraseCloseCount] using hadjust

/-- Core threshold legality plus absence of ko violations is full threshold
legality. -/
theorem thresholdLegal_of_core_of_no_violation
    {n : Nat} {r : Nat → Nat} (hcore : ThresholdCoreLegal n r)
    (hnone : ∀ k, k + 1 < n → ¬ThresholdKoViolation r k) :
    ThresholdLegal n r := by
  rcases hcore with ⟨hzero, hmono, hbound⟩
  refine ⟨hzero, hmono, hbound, ?_⟩
  intro k hk hmax
  by_contra hnext
  exact hnone k hk ⟨hmax, hnext⟩

/-- Repairing an actual ko violation preserves all core threshold
conditions. -/
theorem repair_ko_violation_coreLegal
    {n k : Nat} {r : Nat → Nat} (hcore : ThresholdCoreLegal n r)
    (hk : k + 1 < n) (hbad : ThresholdKoViolation r k) :
    ThresholdCoreLegal n (repairEarlierKoWall (k + 1) r) := by
  rcases hcore with ⟨hzero, hmono, hbound⟩
  have hrk : r k = k := hbad.1
  have hrnextNe : r (k + 1) ≠ k := hbad.2
  have hrnextLower : k ≤ r (k + 1) := by
    have hm := hmono k (k + 1) (by omega) hk (by omega)
    rw [hrk] at hm
    exact hm
  have hrnextUpper : r (k + 1) ≤ k + 1 := hbound (k + 1) hk
  have hrnext : r (k + 1) = k + 1 := by omega
  constructor
  · simp [repairEarlierKoWall, hzero]
  constructor
  · intro a b ha hb hab
    by_cases haEq : a = k + 1
    · subst a
      by_cases hbEq : b = k + 1
      · subst b
        rfl
      · have hkb : k + 1 < b := by omega
        have hold := hmono (k + 1) b hk hb (by omega)
        simp [repairEarlierKoWall, hbEq]
        omega
    · by_cases hbEq : b = k + 1
      · subst b
        have hak : a ≤ k := by omega
        have hold := hmono a k ha (by omega) hak
        simp [repairEarlierKoWall, haEq]
        omega
      · simpa [repairEarlierKoWall, haEq, hbEq] using
          hmono a b ha hb hab
  · intro b hb
    by_cases hbEq : b = k + 1
    · subst b
      simp [repairEarlierKoWall]
    · simpa [repairEarlierKoWall, hbEq] using hbound b hb

/-- At any genuine in-range ko violation, the one-exchange repair changes
exactly the separation edge between the two adjacent opening ranks. -/
theorem repair_ko_violation_changes_exact_edge
    {n k : Nat} {r : Nat → Nat} (hcore : ThresholdCoreLegal n r)
    (hk : k + 1 < n) (hbad : ThresholdKoViolation r k) :
    (ThresholdSeparated r k (k + 1) ∧
      ¬ThresholdSeparated (repairEarlierKoWall (k + 1) r) k (k + 1)) ∧
    ∀ a b, ¬(a = k ∧ b = k + 1) →
      (ThresholdSeparated (repairEarlierKoWall (k + 1) r) a b ↔
        ThresholdSeparated r a b) := by
  have hrk : r k = k := hbad.1
  have hrnextNe : r (k + 1) ≠ k := hbad.2
  have hlower := hcore.2.1 k (k + 1) (by omega) hk (by omega)
  rw [hrk] at hlower
  have hupper := hcore.2.2 (k + 1) hk
  have hrnext : r (k + 1) = k + 1 := by omega
  constructor
  · simpa using repair_earlier_ko_wall_removes_edge
      (j := k + 1) (r := r) (by omega) hrnext
  · intro a b hoff
    exact repair_earlier_ko_wall_preserves_other_edges
      (j := k + 1) (r := r) (by omega) hrnext hoff

/-- Repairing a violation removes it, cannot leave/create a violation at the
next rank, and preserves every other violation verbatim. -/
theorem repair_ko_violation_no_new
    {k i : Nat} {r : Nat → Nat} (_hbad : ThresholdKoViolation r k)
    (hrepaired :
      ThresholdKoViolation (repairEarlierKoWall (k + 1) r) i) :
    ThresholdKoViolation r i ∧ i ≠ k ∧ i ≠ k + 1 := by
  by_cases hik : i = k
  · subst i
    have hfalse := hrepaired.2
    simp [repairEarlierKoWall] at hfalse
  by_cases hinext : i = k + 1
  · subst i
    have hfalse := hrepaired.1
    simp [repairEarlierKoWall] at hfalse
  have hiRepair : i ≠ k + 1 := hinext
  have hiNextRepair : i + 1 ≠ k + 1 := by omega
  simpa [ThresholdKoViolation, repairEarlierKoWall, hiRepair, hiNextRepair,
    hik, hinext] using hrepaired

/-- General threshold legalization after dummy deletion.  Either the raw
erased threshold is already legal, or repairing one actual (and necessarily
earliest adjacent) ko violation makes it legal.  Hence dummy deletion needs
at most one adjacent OPEN/CLOSE exchange. -/
theorem eraseThreshold_legalize_one_exchange
    {n j : Nat} {r : Nat → Nat} (hn : 2 ≤ n) (hj : j < n)
    (hr : ThresholdLegal n r) :
    let e := eraseThreshold j r
    ∃ q, ThresholdLegal (n - 1) q ∧
      (q = e ∨ ∃ k, ThresholdKoViolation e k ∧
        q = repairEarlierKoWall (k + 1) e) := by
  let e := eraseThreshold j r
  change ∃ q, ThresholdLegal (n - 1) q ∧
    (q = e ∨ ∃ k, ThresholdKoViolation e k ∧
      q = repairEarlierKoWall (k + 1) e)
  have hcore : ThresholdCoreLegal (n - 1) e :=
    eraseThreshold_coreLegal hn hj hr
  by_cases hj0 : j = 0
  · subst j
    by_cases hzeroBad : 1 < n - 1 ∧ ThresholdKoViolation e 0
    · let q := repairEarlierKoWall 1 e
      have hqcore : ThresholdCoreLegal (n - 1) q :=
        repair_ko_violation_coreLegal hcore hzeroBad.1 hzeroBad.2
      refine ⟨q, thresholdLegal_of_core_of_no_violation hqcore ?_, ?_⟩
      · intro i hi hqi
        obtain ⟨hei, hi0, hi1⟩ :=
          repair_ko_violation_no_new hzeroBad.2 hqi
        have hloc := threshold_violation_after_erase_adjacent hr (by omega)
          hei.1 hei.2
        omega
      · exact Or.inr ⟨0, hzeroBad.2, rfl⟩
    · refine ⟨e, thresholdLegal_of_core_of_no_violation hcore ?_, Or.inl rfl⟩
      intro i hi hei
      have hloc := threshold_violation_after_erase_adjacent hr (by omega)
        hei.1 hei.2
      rcases hloc with hji | hji
      · subst i
        exact hzeroBad ⟨hi, hei⟩
      · omega
  · have hjpos : 0 < j := by omega
    by_cases hprev : j < n - 1 ∧ ThresholdKoViolation e (j - 1)
    · let q := repairEarlierKoWall j e
      have hqcore : ThresholdCoreLegal (n - 1) q := by
        have hraw := repair_ko_violation_coreLegal hcore (k := j - 1)
          (by omega) hprev.2
        have hpred : (j - 1) + 1 = j := by omega
        rw [hpred] at hraw
        exact hraw
      refine ⟨q, thresholdLegal_of_core_of_no_violation hqcore ?_, ?_⟩
      · intro i hi hqi
        have hqi' : ThresholdKoViolation
            (repairEarlierKoWall ((j - 1) + 1) e) i := by
          simpa only [q, show (j - 1) + 1 = j by omega] using hqi
        obtain ⟨hei, hinePrev, hineJ⟩ :=
          repair_ko_violation_no_new hprev.2 hqi'
        have hloc := threshold_violation_after_erase_adjacent hr (by omega)
          hei.1 hei.2
        omega
      · refine Or.inr ⟨j - 1, hprev.2, ?_⟩
        have hpred : (j - 1) + 1 = j := by omega
        rw [hpred]
    · by_cases hhere : j + 1 < n - 1 ∧ ThresholdKoViolation e j
      · let q := repairEarlierKoWall (j + 1) e
        have hqcore : ThresholdCoreLegal (n - 1) q :=
          repair_ko_violation_coreLegal hcore hhere.1 hhere.2
        refine ⟨q, thresholdLegal_of_core_of_no_violation hqcore ?_, ?_⟩
        · intro i hi hqi
          obtain ⟨hei, hineJ, hineNext⟩ :=
            repair_ko_violation_no_new hhere.2 hqi
          have hloc := threshold_violation_after_erase_adjacent hr (by omega)
            hei.1 hei.2
          rcases hloc with hji | hji
          · exact hineJ hji.symm
          · have : i = j - 1 := by omega
            exact hprev ⟨by omega, this ▸ hei⟩
        · exact Or.inr ⟨j, hhere.2, rfl⟩
      · refine ⟨e, thresholdLegal_of_core_of_no_violation hcore ?_, Or.inl rfl⟩
        intro i hi hei
        have hloc := threshold_violation_after_erase_adjacent hr (by omega)
          hei.1 hei.2
        rcases hloc with hji | hji
        · exact hhere ⟨by omega, hji ▸ hei⟩
        · have : i = j - 1 := by omega
          exact hprev ⟨by omega, this ▸ hei⟩

/-! ## Controller parity after deleting the dummy interval -/

/-- The raw event position after deleting positions `od < cd`.  This is used
only for retained real events, so neither deleted endpoint is queried. -/
def eraseTwoEventPositions (od cd t : Nat) : Nat :=
  t - (if od < t then 1 else 0) - (if cd < t then 1 else 0)

/-- Deleting the dummy OPEN and CLOSE reverses controller parity exactly for
the retained real events strictly between them.  Outside that interval the
two deleted events change event position by zero or two, so parity is
preserved. -/
theorem erase_dummy_interval_toggles_controller_iff
    {od cd t : Nat} (hodcd : od < cd) (htod : t ≠ od) (htcd : t ≠ cd) :
    eraseTwoEventPositions od cd t % 2 ≠ t % 2 ↔
      od < t ∧ t < cd := by
  by_cases hodt : od < t
  · by_cases hcdt : cd < t
    · simp only [eraseTwoEventPositions, if_pos hodt, if_pos hcdt]
      omega
    · have htcd' : t < cd := by omega
      simp only [eraseTwoEventPositions, if_pos hodt, if_neg hcdt]
      omega
  · have htod' : t < od := by omega
    have hcdt : ¬cd < t := by omega
    simp only [eraseTwoEventPositions, if_neg hodt, if_neg hcdt]
    omega

/-- The original threshold witness is realized by the legal schedule

`O₀,O₁,C₀,O₂,C₁,C₂,O₃,P,C₃`

on the edgeless four-vertex board.  Vertex `1` is the coordinate to delete.
The two raw projected ko violations are the patterns `O₀,C₀,O₂` and
`O₂,C₂,O₃`, certified above by the erased threshold word `(0,1,2)`.
-/
theorem two_ko_wall_schedule_is_legal :
    let G : SimpleGraph (Fin 4) := ⊥
    let s0 : State (Fin 4) := initial
    let s1 : State (Fin 4) :=
      ⟨{1, 2, 3}, [0], true, true, 0⟩
    let s2 : State (Fin 4) :=
      ⟨{2, 3}, [0, 1], false, false, 0⟩
    let s3 : State (Fin 4) :=
      ⟨{2, 3}, [1], false, true, 0⟩
    let s4 : State (Fin 4) :=
      ⟨{3}, [1, 2], false, false, 0⟩
    let s5 : State (Fin 4) :=
      ⟨{3}, [2], false, true, 0⟩
    let s6 : State (Fin 4) :=
      ⟨{3}, [], false, false, 0⟩
    let s7 : State (Fin 4) :=
      ⟨∅, [3], true, true, 0⟩
    let s8 : State (Fin 4) :=
      ⟨∅, [3], false, false, 0⟩
    let s9 : State (Fin 4) :=
      ⟨∅, [], false, true, 0⟩
    step G s0 (.open 0) = some s1 ∧
    step G s1 (.open 1) = some s2 ∧
    step G s2 .close = some s3 ∧
    step G s3 (.open 2) = some s4 ∧
    step G s4 .close = some s5 ∧
    step G s5 .close = some s6 ∧
    step G s6 (.open 3) = some s7 ∧
    step G s7 .pass = some s8 ∧
    step G s8 .close = some s9 := by
  norm_num [step, initial, flip]
  decide

end

end Ogdoad.Fifo
