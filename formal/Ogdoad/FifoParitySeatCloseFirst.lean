import Ogdoad.FifoParitySeat

/-!
# CLOSE-first exclusion for the parity-selected FIFO seat

The proposed dummy-free parity-seat theorem has a normalization consequence
which does not require an isolated vertex.  On odd order the alleged odd
counterplayer moves second at the root, so the stopped CLOSE-first empty-root
theorem excludes it directly.  On even order the alleged odd counterplayer
moves first; after its selected first OPEN, the complete second-player fan
contains an OPEN which makes the first queued CLOSE neutral.  The latter
selector follows from even carrier cardinality alone.

Thus every counterstrategy against the parity-selected seat contains a
genuine OPEN deviation at a clear attacker node.  This is a universal
normalization theorem, not a proof of the parity-seat conjecture: the selected
deviation still has to be compared with earlier defender siblings in the
same strategy tree.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A CLOSE-first odd seeker moving second at an empty initial root is
excluded on every finite graph. -/
theorem no_closeFirstOddStrategy_initial_attacker_true
    (G : SimpleGraph V) :
    ¬CloseFirstWins G true 1 (initial (V := V)) := by
  intro hwin
  have hsafe : StoppedEmptyRootSafe G Finset.univ true :=
    stoppedCloseFirstEmptyRootTheorem V inferInstance inferInstance
      G true Finset.univ
  apply hsafe
  simpa [StoppedEmptyRootSafe, stoppedEmptyRoot, initial] using
    hwin.toStoppedOne

/-- On even carrier order, a CLOSE-first odd seeker moving first is also
excluded without a dummy.  Even cardinality supplies the neutral second OPEN
needed to enter the conditioned CLOSE-first contraction. -/
theorem no_closeFirstOddStrategy_initial_attacker_false_of_even
    (G : SimpleGraph V) (hcard : Even (Fintype.card V)) :
    ¬CloseFirstWins G false 1 (initial (V := V)) := by
  intro hwin
  cases hwin with
  | terminal _ _ hscore =>
      simp [initial] at hscore
  | answer _ hdefender _ _ =>
      exact hdefender rfl
  | choose _ _ m child hstep _ hchild =>
      cases m with
      | close => simp [step, initial] at hstep
      | pass => simp [step, initial] at hstep
      | «open» v =>
          let sv : State V := {
            untouched := Finset.univ.erase v
            queue := [v]
            ko := true
            toMove := true
            score := 0 }
          have hopenv : step G (initial (V := V)) (.open v) = some sv := by
            simp [step, initial, sv]
          have hchildEq : child = sv := by
            rw [hopenv] at hstep
            exact Option.some.inj hstep.symm
          subst child
          have hcardZ :
              ((((Finset.univ : Finset V).card : Nat) : ZMod 2)) = 0 := by
            rw [Finset.card_univ, ← ZMod.natCast_mod (Fintype.card V) 2,
              Nat.even_iff.mp hcard]
            rfl
          obtain ⟨w, hw, hfront⟩ :=
            exists_second_open_making_front_even_of_even_card
              (G := G) (S := Finset.univ) (x := v) (Finset.mem_univ v)
              hcardZ
          let svw : State V := {
            untouched := (Finset.univ.erase v).erase w
            queue := [v, w]
            ko := false
            toMove := false
            score := 0 }
          have hopenw : step G sv (.open w) = some svw := by
            simp [step, sv, svw, hw]
          have hpair : CloseFirstWins G false 1 svw :=
            hchild.answer_child (by simp [sv]) hopenw
          let sc : State V := {
            untouched := (Finset.univ.erase v).erase w
            queue := [w]
            ko := false
            toMove := true
            score := 0 }
          have hclose : step G svw .close = some sc := by
            simp [step, svw, sc, hfront]
          have hsctree : CloseFirstWins G false 1 sc :=
            hpair.close_child rfl hclose
          have hcoherent : Coherent sc := by
            exact coherent_step
              (coherent_step
                (coherent_step coherent_initial hopenv) hopenw) hclose
          exact ConditionedCloseFirstTheorem V inferInstance inferInstance
            G false sc hcoherent (by simp [sc]) (by simp [sc]) rfl (by
              simpa [sc] using hsctree)

/-- No CLOSE-first odd strategy exists against the parity-selected seat. -/
theorem no_closeFirstParitySeatCounterstrategy
    (G : SimpleGraph V) (seat : Bool)
    (hseat : (Odd (Fintype.card V) ∧ seat = false) ∨
      (Even (Fintype.card V) ∧ seat = true)) :
    ∀ h : OddWins G seat (initial (V := V)),
      ¬OddStrategyCloseFirst h := by
  intro h hclose
  rcases hseat with ⟨_odd, rfl⟩ | ⟨heven, rfl⟩
  · exact no_closeFirstOddStrategy_initial_attacker_true G
      hclose.toCloseFirstWins
  · exact no_closeFirstOddStrategy_initial_attacker_false_of_even G heven
      hclose.toCloseFirstWins

/-- Every hypothetical odd strategy against the parity-selected seat has a
genuine non-CLOSE move at some attacker-controlled clear node. -/
theorem paritySeatCounterstrategy_has_clearDeviation
    (G : SimpleGraph V) (seat : Bool)
    (hseat : (Odd (Fintype.card V) ∧ seat = false) ∨
      (Even (Fintype.card V) ∧ seat = true))
    (h : OddWins G seat (initial (V := V))) :
    OddStrategyHasClearDeviation h := by
  rcases oddStrategy_deviation_or_closeFirst h with hdev | hclose
  · exact hdev
  · exact False.elim
      (no_closeFirstParitySeatCounterstrategy G seat hseat h hclose)

end

end Ogdoad.Fifo
