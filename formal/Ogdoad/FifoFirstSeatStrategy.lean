import Ogdoad.FifoFirstSeatRoot
import Ogdoad.FifoBadArcCycle

/-!
# Common ancestry in a first-seat FIFO counterstrategy

`FifoFirstSeatRoot` gives the proposition-valued Bellman normal form.  This
module retains the stronger datum available from one explicit first-seat odd
strategy.  Every first `OPEN x` is present in that one tree, and the selected
reply below it is necessarily a second `OPEN (reply x)`.  The resulting
fixed-point-free map is therefore not an arbitrary family of pair-state
counterexamples: every selected pair child has exact ancestry in the same
root strategy.

Finiteness forces a nontrivial periodic orbit of the reply map.  This is the
precise root-cycle carrier suggested by the paper.  It is not yet a
contraction of the branch-dependent continuation cosets, and hence is not a
proof of FIFO linking or of the stronger all-pairs assertion.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- One selected second-OPEN branch below a specified first opener, retaining
its exact membership in the original Type-valued odd strategy. -/
structure FirstSeatSelectedBranch (G : SimpleGraph V)
    (root : OddStrategy G false (initial (V := V))) (x : V) where
  reply : V
  legal : reply ∈ (Finset.univ.erase x : Finset V)
  child : OddStrategy G false (afterInitialTwoOpens x reply)
  node : StrategyNode G false root child
  ancestry : StrategyPrefix G false root child
    (twoOpenArcPrefix Finset.univ (x, reply))

/-- Extract the attacker's selected second opener below one universal initial
branch.  Nontriviality guarantees that the protected singleton after the
first OPEN has a legal second OPEN; ko excludes CLOSE and nonempty untouched
carrier excludes PASS. -/
def OddStrategy.firstSeatSelectedBranch [Nontrivial V]
    {G : SimpleGraph V}
    (root : OddStrategy G false (initial (V := V))) (x : V) :
    FirstSeatSelectedBranch G root x := by
  have hfirst := initial_step_open G x
  cases root with
  | terminal _ hterminal _ =>
      exact False.elim (by
        have hnonempty : (Finset.univ : Finset V).Nonempty :=
          Finset.univ_nonempty
        exact hnonempty.ne_empty hterminal.1)
  | choose _ hseat _ _ _ _ =>
      exact False.elim (hseat rfl)
  | answer _ _ hasMove children =>
      let firstChild := children (.open x) (afterInitialOpen x) hfirst
      have hfirstNode : StrategyNode G false
          (OddStrategy.answer (initial (V := V)) rfl hasMove children)
          firstChild :=
        StrategyNode.answer (StrategyNode.root firstChild)
      cases hchild : firstChild with
      | terminal _ hterminal _ =>
          exact False.elim (by
            have hmove := afterInitialOpen_hasMove G x
            exact terminal_no_step hterminal hmove)
      | answer _ hseat _ _ =>
          exact False.elim (by simp [afterInitialOpen] at hseat)
      | choose _ hseat m t hstep tail =>
          cases m with
          | close =>
              exact False.elim (by simp [step, afterInitialOpen] at hstep)
          | pass =>
              exact False.elim (by
                have hne : (Finset.univ.erase x : Finset V) ≠ ∅ := by
                  obtain ⟨y, hyx⟩ := exists_ne x
                  exact Finset.nonempty_iff_ne_empty.mp ⟨y, by simp [hyx]⟩
                simp [step, afterInitialOpen, hne] at hstep)
          | «open» y =>
              have hy : y ∈ (Finset.univ.erase x : Finset V) := by
                simp only [step, afterInitialOpen] at hstep
                split at hstep
                · assumption
                · contradiction
              have hcanonical :=
                (afterInitialOpen_step_open_iff G x y).2 hy
              rw [hcanonical] at hstep
              have ht : t = afterInitialTwoOpens x y :=
                Option.some.inj hstep.symm
              subst t
              refine {
                reply := y
                legal := hy
                child := tail
                node := ?_
                ancestry := ?_ }
              have hchoose : StrategyNode G false firstChild tail := by
                rw [hchild]
                exact StrategyNode.choose (StrategyNode.root tail)
              exact hfirstNode.trans hchoose
              have hprefixFirst : StrategyPrefix G false
                  (OddStrategy.answer (initial (V := V)) rfl hasMove children)
                  firstChild (moveLiveStar (initial (V := V)) (.open x)) := by
                simpa using StrategyPrefix.answer
                  (hstep := hfirst)
                  (StrategyPrefix.root : StrategyPrefix G false
                    (OddStrategy.answer (initial (V := V)) rfl hasMove children)
                    (OddStrategy.answer (initial (V := V)) rfl hasMove children)
                    0)
              have hprefix : StrategyPrefix G false
                  (OddStrategy.answer (initial (V := V)) rfl hasMove children)
                  tail
                  (moveLiveStar (initial (V := V)) (.open x) +
                    moveLiveStar (afterInitialOpen x) (.open y)) := by
                rw [hchild] at hprefixFirst
                simpa using StrategyPrefix.choose hprefixFirst
              have hliveInitial : liveSet (initial (V := V)) = Finset.univ := by
                simp [liveSet, initial]
              have hliveFirst : liveSet (afterInitialOpen x) = Finset.univ := by
                ext z
                simp [liveSet, afterInitialOpen]
              simpa [twoOpenArcPrefix, moveLiveStar, hliveInitial,
                hliveFirst] using hprefix

/-- The selected second-opener fan carried by one explicit root strategy. -/
structure FirstSeatSelectedFan (G : SimpleGraph V)
    (root : OddStrategy G false (initial (V := V))) where
  reply : V → V
  legal : ∀ x, reply x ∈ (Finset.univ.erase x : Finset V)
  child : ∀ x, OddStrategy G false (afterInitialTwoOpens x (reply x))
  node : ∀ x, StrategyNode G false root (child x)
  ancestry : ∀ x, StrategyPrefix G false root (child x)
    (twoOpenArcPrefix Finset.univ (x, reply x))

/-- Assemble all first branches into one data-carrying selected fan. -/
def OddStrategy.firstSeatSelectedFan [Nontrivial V]
    {G : SimpleGraph V}
    (root : OddStrategy G false (initial (V := V))) :
    FirstSeatSelectedFan G root where
  reply x := (root.firstSeatSelectedBranch x).reply
  legal x := (root.firstSeatSelectedBranch x).legal
  child x := (root.firstSeatSelectedBranch x).child
  node x := (root.firstSeatSelectedBranch x).node
  ancestry x := (root.firstSeatSelectedBranch x).ancestry

/-- The selected reply map has no fixed point. -/
theorem FirstSeatSelectedFan.reply_ne
    {G : SimpleGraph V} {root : OddStrategy G false (initial (V := V))}
    (fan : FirstSeatSelectedFan G root) (x : V) :
    fan.reply x ≠ x := by
  exact (Finset.mem_erase.mp (fan.legal x)).1

/-- Choose one continuation representative at every selected pair child. -/
def FirstSeatSelectedFan.continuation
    {G : SimpleGraph V} {root : OddStrategy G false (initial (V := V))}
    (fan : FirstSeatSelectedFan G root) (x : V) : EdgeVector V :=
  Classical.choose (exists_affineResponseMoment (fan.child x))

/-- The selected branch's continuation representative belongs to its child
affine space. -/
theorem FirstSeatSelectedFan.continuation_mem
    {G : SimpleGraph V} {root : OddStrategy G false (initial (V := V))}
    (fan : FirstSeatSelectedFan G root) (x : V) :
    AffineResponseMoment G false (fan.child x) (fan.continuation x) :=
  Classical.choose_spec (exists_affineResponseMoment (fan.child x))

/-- Each decorated selected arc is a point of the one common root affine
response space.  This is the exact interface required by the balanced-cycle
lemmas in `FifoBadArcCycle`. -/
theorem FirstSeatSelectedFan.decoratedArc_mem_root
    {G : SimpleGraph V} {root : OddStrategy G false (initial (V := V))}
    (fan : FirstSeatSelectedFan G root) (x : V) :
    AffineResponseMoment G false root
      (twoOpenArcPrefix Finset.univ (x, fan.reply x) +
        fan.continuation x) :=
  (fan.ancestry x).lift (fan.continuation_mem x)

omit [DecidableEq V] in
/-- Every fixed-point-free self-map of a nonempty finite type has a periodic
point of period at least two.  The period need not be minimal. -/
theorem exists_nontrivial_periodicPoint_of_noFixed [Nonempty V]
    (f : V → V) (hfixed : ∀ x, f x ≠ x) :
    ∃ x n, 2 ≤ n ∧ Function.IsPeriodicPt f n x := by
  let a : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨i, j, heq, hij⟩ :
      ∃ i j : Nat, (f^[i]) a = (f^[j]) a ∧ i ≠ j := by
    simpa [Function.Injective] using
      (not_injective_infinite_finite (fun n : Nat ↦ (f^[n]) a))
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hnpos : 0 < j - i := Nat.sub_pos_of_lt hijlt
    have hperiod : Function.IsPeriodicPt f (j - i) ((f^[i]) a) := by
      change (f^[j - i]) ((f^[i]) a) = (f^[i]) a
      rw [← Function.iterate_add_apply,
        Nat.sub_add_cancel (Nat.le_of_lt hijlt)]
      exact heq.symm
    have hnone : j - i ≠ 1 := by
      intro hn
      apply hfixed ((f^[i]) a)
      have := hperiod
      simpa [Function.IsPeriodicPt, Function.IsFixedPt, hn] using this
    exact ⟨(f^[i]) a, j - i, by omega, hperiod⟩
  · have hnpos : 0 < i - j := Nat.sub_pos_of_lt hjilt
    have hperiod : Function.IsPeriodicPt f (i - j) ((f^[j]) a) := by
      change (f^[i - j]) ((f^[j]) a) = (f^[j]) a
      rw [← Function.iterate_add_apply,
        Nat.sub_add_cancel (Nat.le_of_lt hjilt)]
      exact heq
    have hnone : i - j ≠ 1 := by
      intro hn
      apply hfixed ((f^[j]) a)
      have := hperiod
      simpa [Function.IsPeriodicPt, Function.IsFixedPt, hn] using this
    exact ⟨(f^[j]) a, i - j, by omega, hperiod⟩

/-- A first-seat odd root strategy therefore carries a nontrivial directed
periodic orbit of selected two-OPEN branches, all with exact membership in the
same root strategy. -/
theorem OddStrategy.firstSeatSelectedCycle [Nontrivial V]
    {G : SimpleGraph V}
    (root : OddStrategy G false (initial (V := V))) :
    ∃ (fan : FirstSeatSelectedFan G root) (x : V) (n : Nat),
      2 ≤ n ∧ Function.IsPeriodicPt fan.reply n x := by
  let fan := root.firstSeatSelectedFan
  obtain ⟨x, n, hn, hperiod⟩ :=
    exists_nontrivial_periodicPoint_of_noFixed fan.reply fan.reply_ne
  exact ⟨fan, x, n, hn, hperiod⟩

end

end Ogdoad.Fifo
