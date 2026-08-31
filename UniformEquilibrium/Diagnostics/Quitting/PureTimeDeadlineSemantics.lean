import UniformEquilibrium.Quitting.Paths.PureTimeDeadlineProfile
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreement
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Terminal semantics at canonical pure deadlines

This layer supplies terminal-semantic formulas for the screened endpoint menu
and deadline descent.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quittingProfileLiveRoot_pureTimeProfileBehavior
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingPureTimeProfileBehavior reward times) time =
      QuittingSureSetOwnerRepair.quittingPureSetRoot
        (quittingPureTimeCoalitionAt times time) := by
  funext who
  simp only [quittingProfileLiveRoot, quittingPureTimeProfileBehavior,
    quittingPureTimeBehaviorStrategy, quittingPureTimeCoalitionAt,
    QuittingSureSetOwnerRepair.quittingPureSetRoot,
    QuittingSureSetOwnerRepair.quittingSetAction, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases hchoice : times who with
  | none => simp [quittingPureTimeHazard]
  | some chosen =>
      by_cases hchosen : chosen = time
      · subst chosen
        simp
      · rw [quittingPureTimeHazard_some_of_ne (Ne.symm hchosen)]
        simp [hchosen]

omit [DecidableEq ι] in
theorem quittingProfileLiveRoot_allContinueContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingProfileAllContinueContinuation reward profile) time =
      quittingProfileLiveRoot reward profile (time + 1) := by
  funext who
  unfold quittingProfileLiveRoot quittingProfileAllContinueContinuation
    StochasticGame.shiftProfile
  rw [consHist_allContinue_quittingLiveHist]

omit [DecidableEq ι] in
theorem quittingAllContinueProfileSpine_continuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingAllContinueProfileSpine reward
        (quittingProfileAllContinueContinuation reward profile) time =
      quittingAllContinueProfileSpine reward profile (time + 1) := by
  induction time with
  | zero => rfl
  | succ time ih =>
      change quittingProfileAllContinueContinuation reward
          (quittingAllContinueProfileSpine reward
            (quittingProfileAllContinueContinuation reward profile) time) =
        quittingProfileAllContinueContinuation reward
          (quittingAllContinueProfileSpine reward profile (time + 1))
      exact congrArg (quittingProfileAllContinueContinuation reward) ih

/-- A finite all-Continue prefix only inserts the all-Continue semantic
prefix once: further copies are idempotent. -/
theorem quittingTerminalSemanticPair_eq_one_allContinuePrefix_of_roots_before
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∀ {deadline : ℕ},
      (∀ time < deadline,
        quittingProfileLiveRoot reward profile time = quittingAllContinueRoot) →
      quittingTerminalSemanticPair reward profile =
        if deadline = 0 then
          quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile deadline)
        else
          quittingTerminalSemanticPrefix reward quittingAllContinueRoot
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile deadline)) := by
  intro deadline
  induction deadline generalizing profile with
  | zero =>
      intro _
      rfl
  | succ deadline ih =>
      intro hbefore
      rw [if_neg (Nat.succ_ne_zero deadline)]
      rw [quittingTerminalSemanticPair_eq_prefix_allContinueContinuation]
      have hroot : quittingProfileRoot reward profile =
          quittingAllContinueRoot := by
        have hzero := hbefore 0 (Nat.zero_lt_succ deadline)
        rw [← quittingProfileSpineRoot_eq_profileLiveRoot] at hzero
        simpa [quittingProfileSpineRoot,
          quittingAllContinueProfileSpine] using hzero
      rw [hroot]
      have htailBefore : ∀ time < deadline,
          quittingProfileLiveRoot reward
              (quittingProfileAllContinueContinuation reward profile) time =
            quittingAllContinueRoot := by
        intro time htime
        rw [quittingProfileLiveRoot_allContinueContinuation]
        exact hbefore (time + 1) (by omega)
      rw [ih _ htailBefore]
      cases deadline with
      | zero => rfl
      | succ later =>
          rw [if_neg (Nat.succ_ne_zero later)]
          rw [quittingAllContinueProfileSpine_continuation]
          apply quittingTerminalSemanticPrefix_allContinue_idempotent

/-- Terminal semantic pair of a nontrivial pure coalition, before any leading
all-Continue rows are restored. -/
def quittingPureCoalitionTerminalSemanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (coalition : Finset ι) : QuittingTerminalSemanticPair ι :=
  (QuittingSureSetOwnerRepair.quittingSetReward reward coalition,
    fun who => max
      (QuittingSureSetOwnerRepair.quittingSetReward reward
        (insert who coalition) who)
      (QuittingSureSetOwnerRepair.quittingSetReward reward
        (coalition.erase who) who))

/-- Exact semantic pair of a canonical profile at a displayed first deadline
whose quitting coalition has at least two members. -/
theorem quittingTerminalSemanticPair_pureTimeProfileBehavior_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (deadline : ℕ)
    (hbefore : ∀ time < deadline,
      quittingPureTimeCoalitionAt times time = ∅)
    (hcard : 2 ≤ (quittingPureTimeCoalitionAt times deadline).card) :
    quittingTerminalSemanticPair reward
        (quittingPureTimeProfileBehavior reward times) =
      if deadline = 0 then
        quittingPureCoalitionTerminalSemanticPair reward
          (quittingPureTimeCoalitionAt times deadline)
      else
        quittingTerminalSemanticPrefix reward quittingAllContinueRoot
          (quittingPureCoalitionTerminalSemanticPair reward
            (quittingPureTimeCoalitionAt times deadline)) := by
  let profile := quittingPureTimeProfileBehavior reward times
  let coalition := quittingPureTimeCoalitionAt times deadline
  have hrootsBefore : ∀ time < deadline,
      quittingProfileLiveRoot reward profile time = quittingAllContinueRoot := by
    intro time htime
    rw [quittingProfileLiveRoot_pureTimeProfileBehavior]
    rw [hbefore time htime]
    exact quittingPureSetRoot_empty
  have hprefix :=
    quittingTerminalSemanticPair_eq_one_allContinuePrefix_of_roots_before
      reward profile hrootsBefore
  have hat : quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile deadline) =
        quittingPureCoalitionTerminalSemanticPair reward coalition := by
    rw [quittingTerminalSemanticPair_eq_prefix_allContinueContinuation]
    have hroot : quittingProfileRoot reward
        (quittingAllContinueProfileSpine reward profile deadline) =
      QuittingSureSetOwnerRepair.quittingPureSetRoot coalition := by
      have hlive := quittingProfileLiveRoot_pureTimeProfileBehavior
        reward times deadline
      rw [← quittingProfileSpineRoot_eq_profileLiveRoot] at hlive
      simpa [quittingProfileSpineRoot, profile, coalition] using hlive
    rw [hroot]
    rw [← quittingTerminalSemanticPair_rootThenContinuation]
    exact
      quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
        reward coalition hcard
          (quittingProfileAllContinueContinuation reward
            (quittingAllContinueProfileSpine reward profile deadline))
  rw [hprefix, hat]

/-- The prescribed payoff of a canonical profile is the reward of its first
nonempty deadline coalition.  Unlike the full semantic-pair formula, this
payoff identity also applies to a singleton first coalition. -/
theorem quittingTerminalPayoff_pureTimeProfileBehavior_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (deadline : ℕ)
    (hbefore : ∀ time < deadline,
      quittingPureTimeCoalitionAt times time = ∅)
    (hnonempty : (quittingPureTimeCoalitionAt times deadline).Nonempty) :
    quittingTerminalPayoff reward
        (quittingPureTimeProfileBehavior reward times) =
      reward ⟨quittingPureTimeCoalitionAt times deadline, hnonempty⟩ := by
  let profile := quittingPureTimeProfileBehavior reward times
  let coalition := quittingPureTimeCoalitionAt times deadline
  have hrootsBefore : ∀ time < deadline,
      quittingProfileLiveRoot reward profile time = quittingAllContinueRoot := by
    intro time htime
    rw [quittingProfileLiveRoot_pureTimeProfileBehavior]
    rw [hbefore time htime]
    exact quittingPureSetRoot_empty
  have hprefix :=
    quittingTerminalSemanticPair_eq_one_allContinuePrefix_of_roots_before
      reward profile hrootsBefore
  have hat : (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile deadline)).1 =
        reward ⟨coalition, by simpa only [coalition] using hnonempty⟩ := by
    funext who
    rw [quittingTerminalSemanticPair_eq_prefix_allContinueContinuation]
    have hroot : quittingProfileRoot reward
        (quittingAllContinueProfileSpine reward profile deadline) =
      QuittingSureSetOwnerRepair.quittingPureSetRoot coalition := by
      have hlive := quittingProfileLiveRoot_pureTimeProfileBehavior
        reward times deadline
      rw [← quittingProfileSpineRoot_eq_profileLiveRoot] at hlive
      simpa [quittingProfileSpineRoot, profile, coalition] using hlive
    rw [hroot]
    change (quittingTerminalSemanticPrefix reward
      (QuittingSureSetOwnerRepair.quittingPureSetRoot coalition)
      (quittingTerminalSemanticPair reward
        (quittingProfileAllContinueContinuation reward
          (quittingAllContinueProfileSpine reward profile deadline)))).1 who = _
    rw [← quittingTerminalSemanticPair_rootThenContinuation]
    change quittingTerminalPayoff reward
        (quittingRootThenContinuationProfile reward
          (QuittingSureSetOwnerRepair.quittingPureSetRoot coalition)
          (quittingProfileAllContinueContinuation reward
            (quittingAllContinueProfileSpine reward profile deadline))) who = _
    rw [← QuittingSureSetOwnerRepair.quittingSetReward_of_nonempty
      reward hnonempty]
    exact quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward
      coalition hnonempty _ who
  change (quittingTerminalSemanticPair reward profile).1 = _
  rw [hprefix]
  split
  · exact hat
  · rw [quittingTerminalSemanticPrefix_allContinue_eq]
    exact hat

end GameTheory
