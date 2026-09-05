import UniformEquilibrium.Quitting.Terminal.CompactStoppingLawCapUpperBound
import UniformEquilibrium.Quitting.Terminal.TerminalExploitability

/-! # Positive singleton rewards charge the all-Never cylinder -/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open _root_.Math.Probability _root_.Math.Probability.DiscreteHazard

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Move only the `Never` atom to one displayed finite date. -/
def moveNeverToFinite (time : ℕ) : Option ℕ → Option ℕ
  | none => some time
  | some original => some original

/-- Against an arbitrary literal profile, delayed deterministic Quit tends to
literal Never plus the opponents' Never cylinder times the singleton reward. -/
theorem quittingTerminalPayoff_update_finiteTime_tendsto_of_profile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    Tendsto (fun time => quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some time))) who)
      atTop (nhds (quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who none)) who +
        quittingOpponentNeverProduct
            (quittingCompactStoppingLawsOfProfile reward profile) who *
          reward (quittingSingletonTerminal who) who)) := by
  have h :=
    quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton
      reward (quittingCompactStoppingLawsOfProfile reward profile) who
  have hfun : (fun time => quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some time))) who) =
      fun time => quittingTerminalPayoff reward
        (Function.update
          (quittingCompactStoppingLawProfile reward
            (quittingCompactStoppingLawsOfProfile reward profile)) who
          (quittingPureTimeBehaviorStrategy reward who (some time))) who := by
    funext time
    exact quittingTerminalPayoff_update_pureTime_eq_compactStoppingLawsOfProfile
      reward profile who (some time)
  rw [hfun]
  convert h using 1
  rw [quittingTerminalPayoff_update_pureTime_eq_compactStoppingLawsOfProfile
    reward profile who none]

/-- Replacing only one's original Never atom by date `time` changes payoff by
that Never mass times the deterministic late-Quit versus Never difference. -/
theorem quittingTerminalPayoff_moveNeverToFinite_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (time : ℕ) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingStoppingLawBehaviorStrategy reward who
            ((quittingBehaviorStoppingLaw reward (profile who)).map
              (moveNeverToFinite time)))) who -
      quittingTerminalPayoff reward profile who =
    (quittingBehaviorStoppingLaw reward (profile who) none).toReal *
      (quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who (some time))) who -
        quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who none)) who) := by
  let value : Option ℕ → ℝ := fun choice =>
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  have hvalue : ∀ choice, |value choice| ≤ quittingRewardBound reward := by
    intro choice
    exact abs_quittingTerminalPayoff_le_quittingRewardBound reward _ who
  rw [quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect,
    expect_map]
  have horiginal := quittingTerminalPayoff_eq_expect_behaviorStoppingLaw_pureTime
    reward profile who who
  change expect (quittingBehaviorStoppingLaw reward (profile who))
      (value ∘ moveNeverToFinite time) -
      quittingTerminalPayoff reward profile who = _
  rw [horiginal]
  unfold quittingBehaviorStoppingLaw
  have hcomposed : ∀ choice,
      |(value ∘ moveNeverToFinite time) choice| ≤ quittingRewardBound reward := by
    intro choice
    exact hvalue (moveNeverToFinite time choice)
  rw [quittingHazardStoppingLaw_expect _ _ hcomposed,
    quittingHazardStoppingLaw_expect _ _ hvalue]
  simp [value, moveNeverToFinite]
  ring

/-- A singleton reward is charged against the probability that every player
chooses their original Never atom. No best-response attainment is used. -/
theorem neverMass_mul_opponentNeverProduct_mul_singleton_le_terminalDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    (quittingBehaviorStoppingLaw reward (profile who) none).toReal *
        quittingOpponentNeverProduct
          (quittingCompactStoppingLawsOfProfile reward profile) who *
        reward (quittingSingletonTerminal who) who ≤
      quittingTerminalDeviationDebt reward profile who := by
  let ownNever :=
    (quittingBehaviorStoppingLaw reward (profile who) none).toReal
  let opponentNever := quittingOpponentNeverProduct
    (quittingCompactStoppingLawsOfProfile reward profile) who
  let neverValue := quittingTerminalPayoff reward
    (Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who none)) who
  let finiteValue : ℕ → ℝ := fun time => quittingTerminalPayoff reward
    (Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who (some time))) who
  let movedValue : ℕ → ℝ := fun time => quittingTerminalPayoff reward
    (Function.update profile who
      (quittingStoppingLawBehaviorStrategy reward who
        ((quittingBehaviorStoppingLaw reward (profile who)).map
          (moveNeverToFinite time)))) who
  have hfinite : Tendsto finiteValue atTop
      (nhds (neverValue + opponentNever *
        reward (quittingSingletonTerminal who) who)) := by
    simpa [finiteValue, neverValue, opponentNever] using
      quittingTerminalPayoff_update_finiteTime_tendsto_of_profile
        reward profile who
  have hgain : Tendsto (fun time => movedValue time -
      quittingTerminalPayoff reward profile who) atTop
      (nhds (ownNever * opponentNever *
        reward (quittingSingletonTerminal who) who)) := by
    have hnever : Tendsto (fun _ : ℕ => neverValue) atTop (nhds neverValue) :=
      tendsto_const_nhds
    have hdifference := (hfinite.sub hnever).const_mul ownNever
    have hrewrite : (fun time => movedValue time -
          quittingTerminalPayoff reward profile who) =
        fun time => ownNever * (finiteValue time - neverValue) := by
      funext time
      exact quittingTerminalPayoff_moveNeverToFinite_sub_eq
        reward profile who time
    rw [hrewrite]
    convert hdifference using 1
    ring_nf
  apply le_of_tendsto hgain
  filter_upwards with time
  have hdev := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile who
      (quittingStoppingLawBehaviorStrategy reward who
        ((quittingBehaviorStoppingLaw reward (profile who)).map
          (moveNeverToFinite time)))
  dsimp only [movedValue]
  unfold quittingTerminalDeviationDebt
  linarith

/-- The own-Never factor times the opponents' Never product is the full
product of the actual stopping laws' Never atoms. -/
theorem stoppingLaw_none_mul_opponentNeverProduct_eq_prod_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    (quittingBehaviorStoppingLaw reward (profile who) none).toReal *
        quittingOpponentNeverProduct
          (quittingCompactStoppingLawsOfProfile reward profile) who =
      ∏ player, (quittingBehaviorStoppingLaw reward (profile player) none).toReal := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun player =>
      (quittingBehaviorStoppingLaw reward (profile player) none).toReal)
    (Finset.mem_univ who)]
  congr 1
  unfold quittingOpponentNeverProduct quittingCompactStoppingLawsOfProfile
  apply Finset.prod_congr rfl
  intro player _
  change (((_root_.Math.Probability.CompactStoppingLaw.ofPMF
    (quittingBehaviorStoppingLaw reward (profile player))).toPMF ⊤)).toReal = _
  rw [_root_.Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
  rfl

/-- Source-facing form of the positive-singleton joint-Never debt bound. -/
theorem prod_stoppingLaw_none_mul_singleton_le_terminalDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    (∏ player, (quittingBehaviorStoppingLaw reward (profile player) none).toReal) *
        reward (quittingSingletonTerminal who) who ≤
      quittingTerminalDeviationDebt reward profile who := by
  rw [← stoppingLaw_none_mul_opponentNeverProduct_eq_prod_none
    reward profile who]
  exact neverMass_mul_opponentNeverProduct_mul_singleton_le_terminalDebt
    reward profile who

/-- The positive-singleton all-Never mass estimate in exploitability form. -/
theorem prod_stoppingLaw_none_mul_singleton_le_terminalExploitability
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    (∏ player, (quittingBehaviorStoppingLaw reward (profile player) none).toReal) *
        reward (quittingSingletonTerminal who) who ≤
      quittingTerminalExploitability reward profile :=
  (prod_stoppingLaw_none_mul_singleton_le_terminalDebt
    reward profile who).trans
      (quittingTerminalDeviationDebt_le_exploitability reward profile who)

end GameTheory
