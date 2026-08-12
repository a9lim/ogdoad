import Mathlib

/-!
# FIFO endpoint words and the kappa-transform obstruction

A completed FIFO schedule, after omitting its possible forced pass, is a
double-occurrence word: each vertex has a labelled `open` and `close`
endpoint, and the opening and closing projections are the same permutation.
The overlap graph is therefore the interlacement graph of the word.

The standard word-level kappa transformation at `v` reverses the subword
between the two occurrences of `v`; on interlacement graphs this is local
complementation at `v`.  The theorem `kappaWord_fifoOrder_iff` records the
causal obstruction to importing that operation into FIFO play.  A rooted
kappa transformation of a FIFO word is again FIFO-ordered exactly when the
reversed interval contains at most one opening and at most one closing.
Thus local complementation is confined to the two-switch corridor and cannot
by itself contract an arbitrary strategy-pruned fan.

This module formalizes the endpoint-order statement only.  It does not assume
that a kappa mate belongs to the same strategy tree, which is a strictly
stronger and generally false causal assertion.
-/

namespace Ogdoad.Fifo

/-- A labelled endpoint in the pass-deleted complete schedule word. -/
inductive Endpoint (V : Type*) where
  | open (v : V)
  | close (v : V)
deriving DecidableEq

/-- Opening-order projection of a labelled endpoint word. -/
def opens {V : Type*} : List (Endpoint V) → List V
  | [] => []
  | .open v :: es => v :: opens es
  | .close _ :: es => opens es

/-- Closing-order projection of a labelled endpoint word. -/
def closes {V : Type*} : List (Endpoint V) → List V
  | [] => []
  | .open _ :: es => closes es
  | .close v :: es => v :: closes es

@[simp] theorem opens_append {V : Type*} (xs ys : List (Endpoint V)) :
    opens (xs ++ ys) = opens xs ++ opens ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [opens, ih]

@[simp] theorem closes_append {V : Type*} (xs ys : List (Endpoint V)) :
    closes (xs ++ ys) = closes xs ++ closes ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [closes, ih]

@[simp] theorem opens_reverse {V : Type*} (xs : List (Endpoint V)) :
    opens xs.reverse = (opens xs).reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [opens, ih]

@[simp] theorem closes_reverse {V : Type*} (xs : List (Endpoint V)) :
    closes xs.reverse = (closes xs).reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [closes, ih]

private theorem nodup_reverse_eq_self_iff_length_le_one {V : Type*}
    (xs : List V) (hxs : xs.Nodup) :
    xs.reverse = xs ↔ xs.length ≤ 1 := by
  constructor
  · intro hrev
    have hp : xs.Palindrome := List.Palindrome.of_reverse_eq hrev
    cases hp with
    | nil => simp
    | singleton x => simp
    | @cons_concat x middle hp =>
        simp at hxs
  · intro hlen
    match xs with
    | [] => rfl
    | [x] => rfl
    | x :: y :: rest => simp at hlen

private theorem reverse_eq_self_of_length_le_one {V : Type*}
    (xs : List V) (hxs : xs.length ≤ 1) : xs.reverse = xs := by
  cases xs with
  | nil => rfl
  | cons x tail =>
      cases tail with
      | nil => rfl
      | cons y rest => simp at hxs

/-- Reverse one displayed middle segment of a labelled endpoint word. -/
def reverseMiddle {V : Type*}
    (before middle after : List (Endpoint V)) : List (Endpoint V) :=
  before ++ middle.reverse ++ after

/-- A labelled endpoint word has the FIFO order property when its opening
and closing projections agree and the common order has no repetition. -/
def FifoOrder {V : Type*} (word : List (Endpoint V)) : Prop :=
  opens word = closes word ∧ (opens word).Nodup

/-- A rooted double-occurrence word with the two occurrences of `v`
displayed. -/
def framedWord {V : Type*} (before : List (Endpoint V)) (v : V)
    (middle after : List (Endpoint V)) : List (Endpoint V) :=
  before ++ [.open v] ++ middle ++ [.close v] ++ after

/-- The rooted word obtained by the word-level kappa transformation at `v`. -/
def kappaWord {V : Type*} (before : List (Endpoint V)) (v : V)
    (middle after : List (Endpoint V)) : List (Endpoint V) :=
  before ++ [.open v] ++ middle.reverse ++ [.close v] ++ after

/-- Reversing a word segment preserves both endpoint-order projections exactly
when each of its two endpoint types occurs at most once. -/
theorem reverseMiddle_preserves_fifo_orders_iff
    {V : Type*} (before middle after : List (Endpoint V))
    (ho : (opens middle).Nodup) (hc : (closes middle).Nodup) :
    (opens (reverseMiddle before middle after) =
        opens (before ++ middle ++ after) ∧
      closes (reverseMiddle before middle after) =
        closes (before ++ middle ++ after)) ↔
      (opens middle).length ≤ 1 ∧ (closes middle).length ≤ 1 := by
  simp only [reverseMiddle, opens_append, closes_append,
    opens_reverse, closes_reverse]
  constructor
  · rintro ⟨hopens, hcloses⟩
    have hopens' : (opens middle).reverse = opens middle := by
      have h := List.append_cancel_left
        (show opens before ++ ((opens middle).reverse ++ opens after) =
          opens before ++ (opens middle ++ opens after) by
            simpa [List.append_assoc] using hopens)
      exact List.append_cancel_right h
    have hcloses' : (closes middle).reverse = closes middle := by
      have h := List.append_cancel_left
        (show closes before ++ ((closes middle).reverse ++ closes after) =
          closes before ++ (closes middle ++ closes after) by
            simpa [List.append_assoc] using hcloses)
      exact List.append_cancel_right h
    exact ⟨(nodup_reverse_eq_self_iff_length_le_one _ ho).mp hopens',
      (nodup_reverse_eq_self_iff_length_le_one _ hc).mp hcloses'⟩
  · rintro ⟨hopens, hcloses⟩
    rw [(nodup_reverse_eq_self_iff_length_le_one _ ho).mpr hopens,
      (nodup_reverse_eq_self_iff_length_le_one _ hc).mpr hcloses]
    exact ⟨rfl, rfl⟩

/-- Exact FIFO boundary for a rooted kappa transformation.

For a FIFO-ordered word displayed as `before, O_v, middle, C_v, after`, the
kappa transform is FIFO-ordered if and only if `middle` contains at most one
OPEN and at most one CLOSE.  In an actual schedule these are respectively a
later interval beginning before `C_v` and an earlier interval ending after
`O_v`; hence the surviving case is precisely the local two-switch corridor. -/
theorem kappaWord_fifoOrder_iff
    {V : Type*} (before middle after : List (Endpoint V)) (v : V)
    (hbase : FifoOrder (framedWord before v middle after)) :
    FifoOrder (kappaWord before v middle after) ↔
      (opens middle).length ≤ 1 ∧ (closes middle).length ≤ 1 := by
  rcases hbase with ⟨horder, hnodup⟩
  have horder0 :
      opens before ++ v :: (opens middle ++ opens after) =
        (closes before ++ closes middle) ++ v :: closes after := by
    simpa [framedWord, opens, closes, List.append_assoc] using horder
  have hnodup0 :
      (opens before ++ v :: (opens middle ++ opens after)).Nodup := by
    simpa [framedWord, opens, List.append_assoc] using hnodup
  have hvpre : v ∉ opens before := by
    intro hv
    exact (List.nodup_append.mp hnodup0).2.2 v hv v (by simp)
      (by simp)
  have hvpost : v ∉ opens middle ++ opens after := by
    exact (List.nodup_cons.mp
      (List.nodup_append.mp hnodup0).2.1).1
  have hparts0 :=
    (List.append_cons_inj_of_notMem hvpre hvpost).mp horder0
  constructor
  · rintro ⟨hkorder, _hkNodup⟩
    have hkorder0 :
        opens before ++ v :: ((opens middle).reverse ++ opens after) =
          (closes before ++ (closes middle).reverse) ++ v :: closes after := by
      simpa [kappaWord, opens, closes, List.append_assoc] using hkorder
    have hvpost' : v ∉ (opens middle).reverse ++ opens after := by
      simpa using hvpost
    have hpartsK :=
      (List.append_cons_inj_of_notMem hvpre hvpost').mp hkorder0
    have hopenPalindrome : (opens middle).reverse = opens middle := by
      have hsuffix :
          (opens middle).reverse ++ opens after =
            opens middle ++ opens after := by
        exact hpartsK.2.2.trans hparts0.2.2.symm
      exact List.append_cancel_right hsuffix
    have hclosePalindrome : (closes middle).reverse = closes middle := by
      have hprefix :
          closes before ++ (closes middle).reverse =
            closes before ++ closes middle := by
        exact hpartsK.1.symm.trans hparts0.1
      exact List.append_cancel_left hprefix
    have hopenNodup : (opens middle).Nodup := by
      have hall : (v :: (opens middle ++ opens after)).Nodup :=
        (List.nodup_append.mp hnodup0).2.1
      exact (List.nodup_append.mp (List.nodup_cons.mp hall).2).1
    have hcloseNodup : (closes middle).Nodup := by
      have hcloseAll : (closes (framedWord before v middle after)).Nodup := by
        rw [← horder]
        exact hnodup
      have hexpanded :
          (closes before ++ closes middle ++ v :: closes after).Nodup := by
        simpa [framedWord, closes, List.append_assoc] using hcloseAll
      exact (List.nodup_append.mp
        (List.nodup_append.mp hexpanded).1).2.1
    exact ⟨(nodup_reverse_eq_self_iff_length_le_one _ hopenNodup).mp
        hopenPalindrome,
      (nodup_reverse_eq_self_iff_length_le_one _ hcloseNodup).mp
        hclosePalindrome⟩
  · rintro ⟨hopenLen, hcloseLen⟩
    have hopenRev : (opens middle).reverse = opens middle :=
      reverse_eq_self_of_length_le_one _ hopenLen
    have hcloseRev : (closes middle).reverse = closes middle :=
      reverse_eq_self_of_length_le_one _ hcloseLen
    constructor
    · simpa [kappaWord, framedWord, opens, closes, List.append_assoc,
        hopenRev, hcloseRev] using horder
    · simpa [kappaWord, framedWord, opens, List.append_assoc,
        hopenRev] using hnodup

end Ogdoad.Fifo
