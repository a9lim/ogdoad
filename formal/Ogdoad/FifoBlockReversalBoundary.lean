import Ogdoad.FifoInterlace
import Ogdoad.FifoParitySeatCloseFirst

/-!
# Whole-block reversal and its strategy boundary

A completed FIFO block has a simple time-reversal symmetry.  Reverse the
endpoint word and exchange OPEN with CLOSE.  The opening and closing orders
remain equal, and two labelled intervals are disjoint before the transform
exactly when they are disjoint afterwards.  Consequently every graph-weighted
overlap payoff is unchanged.

This symmetry is schedule-level, not strategy-level.  Reversing a completed
block chooses its first move from the original block's last move, which is
future information unavailable to an online strategy.  The final three-label
countermodel makes the quantifier failure exact: every legal two-move history
has a legal payoff-equal reverse on an odd carrier, yet the first mover cannot
force payoff zero.  Thus whole-block reversal alone cannot prove the FIFO
parity-seat theorem; a proof must add causal control of which reversed branch
belongs to the same strategy ancestry.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

/-! ## Exact endpoint-word reversal -/

/-- Exchange the two endpoint types without changing the label. -/
def Endpoint.dual {V : Type u} : Endpoint V → Endpoint V
  | .open v => .close v
  | .close v => .open v

@[simp] theorem Endpoint.dual_dual {V : Type u} (e : Endpoint V) :
    e.dual.dual = e := by
  cases e <;> rfl

/-- Reverse time and exchange OPEN with CLOSE. -/
def reverseDualWord {V : Type u} (word : List (Endpoint V)) :
    List (Endpoint V) :=
  word.reverse.map Endpoint.dual

@[simp] theorem reverseDualWord_nil {V : Type u} :
    reverseDualWord ([] : List (Endpoint V)) = [] := rfl

@[simp] theorem reverseDualWord_append {V : Type u}
    (left right : List (Endpoint V)) :
    reverseDualWord (left ++ right) =
      reverseDualWord right ++ reverseDualWord left := by
  simp [reverseDualWord, List.map_append]

@[simp] theorem reverseDualWord_singleton {V : Type u} (e : Endpoint V) :
    reverseDualWord [e] = [e.dual] := by
  simp [reverseDualWord]

@[simp] theorem reverseDualWord_cons {V : Type u}
    (e : Endpoint V) (word : List (Endpoint V)) :
    reverseDualWord (e :: word) = reverseDualWord word ++ [e.dual] := by
  simp [reverseDualWord, List.map_append]

@[simp] theorem reverseDualWord_involutive {V : Type u}
    (word : List (Endpoint V)) :
    reverseDualWord (reverseDualWord word) = word := by
  simp [reverseDualWord, List.map_reverse, List.map_map,
    Function.comp_def]

@[simp] theorem opens_map_dual {V : Type u} (word : List (Endpoint V)) :
    opens (word.map Endpoint.dual) = closes word := by
  induction word with
  | nil => rfl
  | cons e tail ih => cases e <;> simp [Endpoint.dual, opens, closes, ih]

@[simp] theorem closes_map_dual {V : Type u} (word : List (Endpoint V)) :
    closes (word.map Endpoint.dual) = opens word := by
  induction word with
  | nil => rfl
  | cons e tail ih => cases e <;> simp [Endpoint.dual, opens, closes, ih]

@[simp] theorem opens_reverseDualWord {V : Type u}
    (word : List (Endpoint V)) :
    opens (reverseDualWord word) = (closes word).reverse := by
  simp [reverseDualWord]

@[simp] theorem closes_reverseDualWord {V : Type u}
    (word : List (Endpoint V)) :
    closes (reverseDualWord word) = (opens word).reverse := by
  simp [reverseDualWord]

/-- Reverse-dual is an involution on FIFO-ordered complete endpoint words. -/
theorem fifoOrder_reverseDualWord_iff {V : Type u}
    (word : List (Endpoint V)) :
    FifoOrder (reverseDualWord word) ↔ FifoOrder word := by
  have forward (w : List (Endpoint V)) (h : FifoOrder w) :
      FifoOrder (reverseDualWord w) := by
    rcases h with ⟨horder, hnodup⟩
    constructor
    · simp only [opens_reverseDualWord, closes_reverseDualWord]
      exact congrArg List.reverse horder.symm
    · rw [opens_reverseDualWord, List.nodup_reverse]
      rwa [← horder]
  constructor
  · intro h
    rw [← reverseDualWord_involutive word]
    exact forward (reverseDualWord word) h
  · exact forward word

/-! ## Pairwise interval and payoff invariance -/

/-- One endpoint occurs strictly before another in a displayed word. -/
def EndpointPrecedes {V : Type u}
    (a b : Endpoint V) (word : List (Endpoint V)) : Prop :=
  ∃ before middle after,
    word = before ++ a :: middle ++ b :: after

/-- Reversing time exchanges the order and dualizes both endpoints. -/
theorem endpointPrecedes_reverseDualWord_iff {V : Type u}
    (a b : Endpoint V) (word : List (Endpoint V)) :
    EndpointPrecedes a b word ↔
      EndpointPrecedes b.dual a.dual (reverseDualWord word) := by
  have forward {x y : Endpoint V} {w : List (Endpoint V)}
      (h : EndpointPrecedes x y w) :
      EndpointPrecedes y.dual x.dual (reverseDualWord w) := by
    rcases h with ⟨before, middle, after, rfl⟩
    refine ⟨reverseDualWord after, reverseDualWord middle,
      reverseDualWord before, ?_⟩
    simp only [reverseDualWord_append, reverseDualWord_cons]
    simp [List.append_assoc]
  constructor
  · exact forward
  · intro h
    have h' := forward h
    simpa using h'

/-- Two labelled intervals are separated when either one closes before the
other opens. -/
def IntervalsSeparated {V : Type u}
    (word : List (Endpoint V)) (x y : V) : Prop :=
  EndpointPrecedes (.close x) (.open y) word ∨
    EndpointPrecedes (.close y) (.open x) word

/-- Whole-word reversal preserves interval disjointness label by label. -/
theorem intervalsSeparated_reverseDualWord_iff {V : Type u}
    (word : List (Endpoint V)) (x y : V) :
    IntervalsSeparated (reverseDualWord word) x y ↔
      IntervalsSeparated word x y := by
  constructor
  · rintro (h | h)
    · exact Or.inr
        ((endpointPrecedes_reverseDualWord_iff
          (.close y) (.open x) word).mpr (by simpa [Endpoint.dual] using h))
    · exact Or.inl
        ((endpointPrecedes_reverseDualWord_iff
          (.close x) (.open y) word).mpr (by simpa [Endpoint.dual] using h))
  · rintro (h | h)
    · exact Or.inr (by
        simpa [Endpoint.dual] using
          (endpointPrecedes_reverseDualWord_iff
            (.close x) (.open y) word).mp h)
    · exact Or.inl (by
        simpa [Endpoint.dual] using
          (endpointPrecedes_reverseDualWord_iff
            (.close y) (.open x) word).mp h)

/-- Binary overlap coordinate of two labelled intervals. -/
def intervalOverlapBit {V : Type u}
    (word : List (Endpoint V)) (x y : V) : ZMod 2 :=
  by
    classical
    exact if IntervalsSeparated word x y then 0 else 1

@[simp] theorem intervalOverlapBit_reverseDualWord {V : Type u}
    (word : List (Endpoint V)) (x y : V) :
    intervalOverlapBit (reverseDualWord word) x y =
      intervalOverlapBit word x y := by
  rw [intervalOverlapBit, intervalOverlapBit,
    intervalsSeparated_reverseDualWord_iff]

/-- Payoff of any oriented list of graph edges.  Choosing one orientation of
each edge recovers the usual graph overlap parity. -/
def endpointOverlapPayoff {V : Type u}
    (edges : List (V × V)) (word : List (Endpoint V)) : ZMod 2 :=
  (edges.map fun e ↦ intervalOverlapBit word e.1 e.2).sum

/-- Every graph-weighted overlap payoff is invariant under whole-block
reverse-dual. -/
@[simp] theorem endpointOverlapPayoff_reverseDualWord {V : Type u}
    (edges : List (V × V)) (word : List (Endpoint V)) :
    endpointOverlapPayoff edges (reverseDualWord word) =
      endpointOverlapPayoff edges word := by
  simp [endpointOverlapPayoff]

/-! ## Why the symmetry does not steal a strategy -/

/-- Abstract two-move payoff on three labels: every distinct pair has unit
payoff.  This is the complete graph `K₃` written without graph machinery. -/
def reversalBoundaryPayoff (x y : Fin 3) : ZMod 2 :=
  if x = y then 0 else 1

/-- The legal histories are ordered distinct pairs. -/
def ReversalBoundaryLegal (x y : Fin 3) : Prop := x ≠ y

/-- The first mover can force zero precisely when some first label has only
zero-payoff legal replies. -/
def ReversalBoundaryMoverForcesZero : Prop :=
  ∃ x : Fin 3, ∀ y : Fin 3,
    ReversalBoundaryLegal x y → reversalBoundaryPayoff x y = 0

theorem reversalBoundary_card_odd : Odd (Fintype.card (Fin 3)) := by
  decide

/-- Every legal history has a legal reversed history. -/
theorem reversalBoundary_legal_reverse (x y : Fin 3) :
    ReversalBoundaryLegal x y ↔ ReversalBoundaryLegal y x := by
  simp [ReversalBoundaryLegal, ne_comm]

/-- Reversing a history preserves its payoff. -/
theorem reversalBoundary_payoff_reverse (x y : Fin 3) :
    reversalBoundaryPayoff x y = reversalBoundaryPayoff y x := by
  simp [reversalBoundaryPayoff, eq_comm]

/-- Nevertheless the first mover cannot force zero: after any first label,
the second mover selects a distinct label and obtains unit payoff. -/
theorem reversalBoundary_mover_cannot_force_zero :
    ¬ReversalBoundaryMoverForcesZero := by
  rintro ⟨x, h⟩
  fin_cases x
  · have := h 1 (by simp [ReversalBoundaryLegal])
    norm_num [reversalBoundaryPayoff] at this
  · have := h 0 (by simp [ReversalBoundaryLegal])
    norm_num [reversalBoundaryPayoff] at this
  · have := h 0 (by simp [ReversalBoundaryLegal])
    norm_num [reversalBoundaryPayoff] at this

/-- Exact route no-go: odd carrier size, reversal-closed legality, and
reversal-invariant payoff do not imply a mover winning strategy. -/
theorem blockReversal_strategyStealing_boundary :
    Odd (Fintype.card (Fin 3)) ∧
      (∀ x y : Fin 3,
        ReversalBoundaryLegal x y ↔ ReversalBoundaryLegal y x) ∧
      (∀ x y : Fin 3,
        reversalBoundaryPayoff x y = reversalBoundaryPayoff y x) ∧
      ¬ReversalBoundaryMoverForcesZero := by
  exact ⟨reversalBoundary_card_odd, reversalBoundary_legal_reverse,
    reversalBoundary_payoff_reverse,
    reversalBoundary_mover_cannot_force_zero⟩

end

end Ogdoad.Fifo
