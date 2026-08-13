import Ogdoad.FifoStrategy
import Ogdoad.FifoNormalization
import Ogdoad.FifoHub
import Ogdoad.FifoControlledDivergence
import Ogdoad.FifoPublicSeparatorAutomaton

/-!
# A canonical positional odd strategy on full FIFO states

Every `OddWins G seat s` witness can be represented by a strategy whose
continuation depends only on the full concrete state `s`.  At a selected node
we choose canonically from the finite Bellman-winning moves; at a universal
node we recurse canonically on every legal child.  Well-founded recursion on
`rank` makes the construction terminate.  Proof irrelevance shows that two
`OddWins` proofs at the same state produce propositionally equal canonical
subtrees.

This closes one genuine ancestry gap: histories which reconverge at exactly
the same `State` share their future continuation.  It does not identify
merely public reconvergence.  A real OPEN/CLOSE square has a one-bit score
curvature when the opened vertex is adjacent to the closed front, so its two
endpoints are score translates rather than the same full state.  An isolated
dummy square does reconverge exactly, but positionality is conditional on the
policy actually taking the complementary second edges; it does not force
those selected moves.

The module is a reduction, not a proof of FIFO linking.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

namespace PositionalOdd

/-! ## Bellman data independent of a displayed proof tree -/

/-- One legal selected move into the odd-winning region.  The type depends
only on the full state, graph, and distinguished seat. -/
structure OddWinningChoice (G : SimpleGraph V) (seat : Bool) (s : State V) where
  move : Move V
  next : State V
  step : step G s move = some next
  wins : OddWins G seat next

omit [Fintype V] in
/-- An odd-winning selected node has at least one odd-winning legal child. -/
theorem oddWins_nonempty_oddWinningChoice
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (hwin : OddWins G seat s) (ht : ¬Terminal s)
    (hturn : s.toMove ≠ seat) : Nonempty (OddWinningChoice G seat s) := by
  cases hwin with
  | terminal _ hterminal _ => exact False.elim (ht hterminal)
  | choose _ _ m t hstep hchild =>
      exact ⟨⟨m, t, hstep, hchild⟩⟩
  | answer _ hseat _ _ => exact False.elim (hturn hseat)

/-- A canonical winning selected move.  Although its existence proof is an
argument, that proof lives in `Prop`, so proof irrelevance makes the returned
choice independent of which `OddWins` derivation was supplied. -/
noncomputable def canonicalOddWinningChoice
    (G : SimpleGraph V) (seat : Bool) (s : State V)
    (hwin : OddWins G seat s) (ht : ¬Terminal s)
    (hturn : s.toMove ≠ seat) : OddWinningChoice G seat s :=
  Classical.choice (oddWins_nonempty_oddWinningChoice hwin ht hturn)

omit [Fintype V] in
theorem canonicalOddWinningChoice_proof_irrelevant
    (G : SimpleGraph V) (seat : Bool) (s : State V)
    (h₁ h₂ : OddWins G seat s) (ht : ¬Terminal s)
    (hturn : s.toMove ≠ seat) :
    canonicalOddWinningChoice G seat s h₁ ht hturn =
      canonicalOddWinningChoice G seat s h₂ ht hturn := by
  have : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

omit [Fintype V] in
/-- At a terminal odd-winning state the accumulated score is nonzero. -/
theorem oddWins_terminal_score_ne_zero
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (hwin : OddWins G seat s) (ht : Terminal s) : s.score ≠ 0 := by
  cases hwin with
  | terminal _ _ hscore => exact hscore
  | choose _ _ m t hstep _ =>
      exact False.elim (terminal_no_step ht ⟨m, t, hstep⟩)
  | answer _ _ hasMove _ =>
      exact False.elim (terminal_no_step ht hasMove)

/-! ## Canonical rank-recursive strategy -/

/-- The canonical positional odd strategy.  Each recursive call is made only
from the full successor state and its proposition-valued `OddWins` fact. -/
noncomputable def canonicalOddStrategy
    (G : SimpleGraph V) (seat : Bool) (s : State V)
    (hwin : OddWins G seat s) : OddStrategy G seat s := by
  by_cases ht : Terminal s
  · exact .terminal s ht (oddWins_terminal_score_ne_zero hwin ht)
  · by_cases hturn : s.toMove = seat
    · exact .answer s hturn (not_terminal_has_step ht)
        (fun m t hstep ↦ canonicalOddStrategy G seat t
          (hwin.answer_child hturn hstep))
    · let choice := canonicalOddWinningChoice G seat s hwin ht hturn
      exact .choose s hturn choice.move choice.next choice.step
        (canonicalOddStrategy G seat choice.next choice.wins)
termination_by rank s
decreasing_by
  · exact rank_step_lt hstep
  · exact rank_step_lt choice.step

omit [Fintype V] in
/-- Canonical continuations at the same full state are equal, independently
of which proof established membership in the odd-winning region. -/
theorem canonicalOddStrategy_proof_irrelevant
    (G : SimpleGraph V) (seat : Bool) (s : State V)
    (h₁ h₂ : OddWins G seat s) :
    canonicalOddStrategy G seat s h₁ = canonicalOddStrategy G seat s h₂ := by
  have : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

omit [Fintype V] in
/-- Equal full states reached through different histories carry the same
canonical continuation.  The equality is heterogeneous only because the
strategy type is indexed by the state. -/
theorem canonicalOddStrategy_eq_of_state_eq
    (G : SimpleGraph V) (seat : Bool) {s t : State V}
    (hst : s = t) (hs : OddWins G seat s) (ht : OddWins G seat t) :
    HEq (canonicalOddStrategy G seat s hs)
      (canonicalOddStrategy G seat t ht) := by
  subst t
  exact heq_of_eq (canonicalOddStrategy_proof_irrelevant G seat s hs ht)

omit [Fintype V] in
/-- Every alleged odd counterexample therefore has a canonical positional
Type-valued strategy at its root. -/
theorem oddWins_nonempty_canonicalOddStrategy
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (h : OddWins G seat s) : Nonempty (OddStrategy G seat s) :=
  ⟨canonicalOddStrategy G seat s h⟩

/-! ## The canonical root is genuinely memoized by full state -/

/-- Every stored immediate child is the canonical strategy of its concrete
successor, and satisfies the same condition recursively. -/
def CanonicallyMemoized
    {G : SimpleGraph V} {seat : Bool} :
    {s : State V} → OddStrategy G seat s → Prop
  | _, .terminal _ _ _ => True
  | _, .choose _ _ _ t _ child =>
      child = canonicalOddStrategy G seat t child.toOddWins ∧
        CanonicallyMemoized child
  | _, .answer _ _ _ children =>
      ∀ m t (hstep : step G _ m = some t),
        children m t hstep =
            canonicalOddStrategy G seat t (children m t hstep).toOddWins ∧
          CanonicallyMemoized (children m t hstep)

omit [Fintype V] in
/-- The rank-recursive construction is memoized at every immediate child. -/
theorem canonicalOddStrategy_memoized
    (G : SimpleGraph V) (seat : Bool) :
    ∀ (s : State V) (hodd : OddWins G seat s),
      CanonicallyMemoized (canonicalOddStrategy G seat s hodd) := by
  intro s
  induction s using (measure rank).wf.induction with
  | h s ih =>
      intro hodd
      rw [canonicalOddStrategy.eq_def]
      split
      · trivial
      · rename_i ht
        split
        · rename_i hturn
          intro m t hstep
          constructor
          · exact canonicalOddStrategy_proof_irrelevant G seat t
              (hodd.answer_child hturn hstep)
              (canonicalOddStrategy G seat t
                (hodd.answer_child hturn hstep)).toOddWins
          · exact ih t (rank_step_lt hstep)
              (hodd.answer_child hturn hstep)
        · rename_i hturn
          let choice := canonicalOddWinningChoice G seat s hodd ht hturn
          constructor
          · exact canonicalOddStrategy_proof_irrelevant G seat choice.next
              choice.wins
              (canonicalOddStrategy G seat choice.next choice.wins).toOddWins
          · exact ih choice.next (rank_step_lt choice.step) choice.wins

omit [Fintype V] in
/-- Every descendant occurrence inside a canonical root is itself the
canonical strategy of its concrete state. -/
theorem CanonicallyMemoized.node_eq_canonical
    {G : SimpleGraph V} {seat : Bool} {r s : State V}
    {root : OddStrategy G seat r} {desc : OddStrategy G seat s}
    (hroot : root = canonicalOddStrategy G seat r root.toOddWins)
    (hmemo : CanonicallyMemoized root)
    (hnode : StrategyNode G seat root desc) :
    desc = canonicalOddStrategy G seat s desc.toOddWins := by
  induction hnode with
  | root => exact hroot
  | @choose a b c hseat m hstep child desc hdesc ih =>
      exact ih hmemo.1 hmemo.2
  | @answer a b c hseat hasMove children m hstep desc hdesc ih =>
      exact ih (hmemo m b hstep).1 (hmemo m b hstep).2

omit [Fintype V] in
/-- Two occurrences of the same full state in one canonical root have
literally equal Type-valued continuation trees.  Thus a countermodel based
on assigning distinct continuations at an exact state join cannot remain
positional after canonicalization. -/
theorem canonicalOddStrategy_subtree_unique
    (G : SimpleGraph V) (seat : Bool) (r : State V)
    (hodd : OddWins G seat r) {s : State V}
    (left right : OddStrategy G seat s)
    (hleft : StrategyNode G seat
      (canonicalOddStrategy G seat r hodd) left)
    (hright : StrategyNode G seat
      (canonicalOddStrategy G seat r hodd) right) :
    left = right := by
  have hmemo := canonicalOddStrategy_memoized G seat r hodd
  have hroot : canonicalOddStrategy G seat r hodd =
      canonicalOddStrategy G seat r
        (canonicalOddStrategy G seat r hodd).toOddWins :=
    canonicalOddStrategy_proof_irrelevant G seat r _ _
  have hl := hmemo.node_eq_canonical hroot hleft
  have hr := hmemo.node_eq_canonical hroot hright
  calc
    left = canonicalOddStrategy G seat s left.toOddWins := hl
    _ = canonicalOddStrategy G seat s right.toOddWins :=
      canonicalOddStrategy_proof_irrelevant G seat s _ _
    _ = right := hr.symm

/-- Replacing an arbitrary odd witness at the isolated-dummy root by the
canonical positional witness preserves the separator contradiction: the
forgotten canonical policy is still entirely on sheet one for the graph
represented by `ell`.

Thus positionalization is a legitimate reduction of an alleged FIFO
counterexample, rather than an extra hypothesis on it. -/
theorem canonicalOddStrategy_initial_separator_one
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool)
    (hodd : OddWins (graphOfRealEdgeFunctional d ell) seat
      (initial (V := V))) :
    PublicPolicySeparatorSheet d ell seat
      (canonicalOddStrategy (graphOfRealEdgeFunctional d ell) seat
        (initial (V := V)) hodd).toPublicPolicy 1 := by
  intro z hz
  have heval :=
    (hz.toAffineResponseMoment
      (canonicalOddStrategy (graphOfRealEdgeFunctional d ell) seat
        (initial (V := V)) hodd)).graphEvaluation_eq wellFormed_initial
  rw [graphEvaluation_graphOfRealEdgeFunctional] at heval
  simpa [publicSeparatorEvaluation, potential, initial, queueCut] using heval

/-! ## Exact and public-only diamonds -/

omit [Fintype V] [DecidableEq V] in
/-- Translation by one has no fixed full state. -/
theorem scoreTranslate_one_ne (s : State V) : scoreTranslate 1 s ≠ s := by
  intro h
  have hs := congrArg State.score h
  simp only [scoreTranslate] at hs
  have hone : (1 : ZMod 2) = 0 := by
    calc
      1 = (1 + s.score) + s.score := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = s.score + s.score := by rw [hs]
      _ = 0 := CharTwo.add_self_eq_zero _
  exact one_ne_zero hone

omit [Fintype V] in
/-- A unit-curvature real OPEN/CLOSE square reconverges only publicly.  Its
two endpoints differ by score translation, so full-state positionality does
not correlate their continuations. -/
theorem openClose_unitCurvature_public_not_full_merge
    (G : SimpleGraph V) (s : State V) (f z : V) (q : List V)
    (hqueue : s.queue = f :: q) (hq : q ≠ [])
    (hko : s.ko = false) (hz : z ∈ s.untouched)
    (hadj : adjacencyBit G f z = 1) :
    ∃ (soc sco : State V),
      soc.public = sco.public ∧ sco = scoreTranslate 1 soc ∧ soc ≠ sco := by
  obtain ⟨so, soc, sc, sco, hopen, hcloseAfterOpen, hclose,
      hopenAfterClose, hU, hqeq, hkoeq, hturn, hscore⟩ :=
    open_close_square_away_singleton G s f z q hqueue hq hko hz
  have hpublic : soc.public = sco.public := by
    simp only [State.public, PublicState.mk.injEq]
    exact ⟨hU, hqeq, hkoeq, hturn⟩
  have htranslate : sco = scoreTranslate 1 soc := by
    obtain ⟨socU, socQ, socKo, socTurn, socScore⟩ := soc
    obtain ⟨scoU, scoQ, scoKo, scoTurn, scoScore⟩ := sco
    simp only at hU hqeq hkoeq hturn hscore ⊢
    subst scoU
    subst scoQ
    subst scoKo
    subst scoTurn
    rw [hscore, hadj]
    simp only [scoreTranslate]
    congr 1
    ac_rfl
  refine ⟨soc, sco, hpublic, htranslate, ?_⟩
  intro heq
  have : scoreTranslate 1 soc = soc := by rw [← htranslate, ← heq]
  exact scoreTranslate_one_ne soc this

omit [Fintype V] in
/-- An isolated-dummy OPEN/CLOSE square away from the singleton wall does
reconverge as a full state.  Hence, if both complementary two-edge histories
occur inside the canonical strategy, their endpoint continuations are equal.
The theorem deliberately assumes those histories occur; positionality alone
does not force either selected complementary edge. -/
theorem canonicalOddStrategy_isolatedDummy_conditional_join
    (G : SimpleGraph V) (seat : Bool) (s : State V) (d f : V) (q : List V)
    (hqueue : s.queue = f :: q) (hq : q ≠ [])
    (hko : s.ko = false) (hdmem : d ∈ s.untouched) (hd : IsDummy G d) :
    ∃ so soc sc sco,
      step G s (.open d) = some so ∧
      step G so .close = some soc ∧
      step G s .close = some sc ∧
      step G sc (.open d) = some sco ∧ soc = sco ∧
      ∀ (hsoc : OddWins G seat soc) (hsco : OddWins G seat sco),
        HEq (canonicalOddStrategy G seat soc hsoc)
          (canonicalOddStrategy G seat sco hsco) := by
  obtain ⟨so, soc, sc, sco, hopen, hcloseAfterOpen, hclose,
      hopenAfterClose, heq⟩ :=
    isolatedUntouched_open_close_commute G s d f q hqueue hq hko hdmem hd
  exact ⟨so, soc, sc, sco, hopen, hcloseAfterOpen, hclose,
    hopenAfterClose, heq, fun hsoc hsco ↦
      canonicalOddStrategy_eq_of_state_eq G seat heq hsoc hsco⟩

end PositionalOdd

end

end Ogdoad.Fifo
