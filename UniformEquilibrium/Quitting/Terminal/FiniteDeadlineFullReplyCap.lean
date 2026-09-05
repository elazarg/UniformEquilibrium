import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineReplyCap
import UniformEquilibrium.Quitting.Terminal.CompactStoppingLawCapUpperBound
import UniformEquilibrium.Quitting.Terminal.TerminalExploitability
import MathUE.ProbabilityMassFunction.BoundedSupportAverage

/-! # Full behavioral response caps of finite timing menus -/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingFiniteDeadlineNeverPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) (who : ι) : ℝ :=
  quittingTerminalPayoff reward
    (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
      (quittingPureTimeBehaviorStrategy reward who none)) who

def quittingFiniteDeadlineOpponentNeverProduct
    (deadline : ℕ) (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) : ℝ :=
  quittingOpponentNeverProduct (fun player ↦ quittingFiniteDeadlineTimingLaw (mixed player)) who

def quittingFiniteDeadlineJointNeverProduct
    (deadline : ℕ) (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) : ℝ :=
  ∏ who, (mixed who none).toReal

theorem quittingFiniteDeadline_purePayoff_le_replyCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) (who : ι)
    (action : QuittingFiniteDeadlineTimingAction deadline) :
    quittingTerminalPayoff reward
        (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
          (quittingPureTimeBehaviorStrategy reward who
            (quittingFiniteDeadlineTimingActionTime action))) who ≤
      quittingFiniteDeadlineReplyCap reward deadline mixed who := by
  exact Finset.le_sup'
    (fun choice : QuittingFiniteDeadlineTimingAction deadline ↦
      quittingTerminalPayoff reward
        (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
          (quittingPureTimeBehaviorStrategy reward who
            (quittingFiniteDeadlineTimingActionTime choice))) who)
    (Finset.mem_univ action)

/-- Once the displayed deadline has passed, the finite timing realization has
no remaining finite opponent atom, so every later Quit has the same literal row. -/
theorem quittingFiniteDeadlineTimingProfile_pureTime_eq_never_add_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) (who : ι)
    {time : ℕ} (htime : deadline ≤ time) :
    quittingTerminalPayoff reward
        (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
          (quittingPureTimeBehaviorStrategy reward who (some time))) who =
      quittingFiniteDeadlineNeverPayoff reward deadline mixed who +
        quittingFiniteDeadlineOpponentNeverProduct deadline mixed who *
          reward (quittingSingletonTerminal who) who := by
  let laws := fun player ↦ quittingFiniteDeadlineTimingLaw (mixed player)
  have hlimit :=
    quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton
      reward laws who
  have hprofile : quittingCompactStoppingLawProfile reward laws =
      quittingFiniteDeadlineTimingProfile reward deadline mixed := rfl
  rw [hprofile] at hlimit
  -- The finite-support law makes the convergent sequence constant from `deadline` onward.
  have hconstant : ∀ later, deadline ≤ later →
      quittingTerminalPayoff reward
          (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
            (quittingPureTimeBehaviorStrategy reward who (some later))) who =
        quittingTerminalPayoff reward
          (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
            (quittingPureTimeBehaviorStrategy reward who (some deadline))) who := by
    intro later hlater
    let roots := quittingProfileLiveRoot reward
      (quittingFiniteDeadlineTimingProfile reward deadline mixed)
    have hroot : ∀ t, deadline ≤ t → roots t = quittingAllContinueRoot := by
      intro t ht
      exact quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
        reward deadline mixed ht
    have hstep : ∀ t, deadline ≤ t →
        quittingRootSequencePureTimeTerminalValue reward roots who (some (t + 1)) 0 =
          quittingRootSequencePureTimeTerminalValue reward roots who (some t) 0 := by
      intro t ht
      rw [quittingRootSequencePureTimeTerminalValue_some_eq,
        quittingRootSequencePureTimeTerminalValue_some_eq,
        quittingLiveLedgerAccum_zero_succ,
        quittingOpponentSurvivalWeight_zero_succ]
      simp only [quittingFixedOpponentsContinueReward,
        quittingFixedOpponentsContinueMass, quittingFixedOpponentsQuitValue]
      rw [hroot t ht, hroot (t + 1) (by omega)]
      have hm : quittingStationaryContinueMass
          (Function.update quittingAllContinueRoot who (PMF.pure false)) = 1 := by
        have hu : Function.update quittingAllContinueRoot who (PMF.pure false) =
            quittingAllContinueRoot := by
          funext player
          by_cases hp : player = who
          · subst player
            simp [quittingAllContinueRoot]
          · simp [Function.update_of_ne hp, quittingAllContinueRoot]
        rw [hu, quittingStationaryContinueMass_allContinueRoot]
      have hr := quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
        reward (root := quittingAllContinueRoot) (who := who) (by
          change quittingStationaryContinueMass
            (Function.update quittingAllContinueRoot who (PMF.pure false)) = 1
          exact hm)
      change quittingRootAbsorbingContribution reward
        (Function.update quittingAllContinueRoot who (PMF.pure false)) who = 0 at hr
      rw [hm, hr]
      ring
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    change quittingRootSequencePureTimeTerminalValue reward roots who (some later) 0 =
      quittingRootSequencePureTimeTerminalValue reward roots who (some deadline) 0
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hlater
    induction offset with
    | zero => simp
    | succ offset ih =>
        rw [Nat.add_succ, hstep (deadline + offset) (by omega), ih (by omega)]
  have hevent : ∀ᶠ later in atTop,
      quittingTerminalPayoff reward
          (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
            (quittingPureTimeBehaviorStrategy reward who (some later))) who =
        quittingTerminalPayoff reward
          (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
            (quittingPureTimeBehaviorStrategy reward who (some deadline))) who :=
    (eventually_ge_atTop deadline).mono hconstant
  have hconstLimit : Tendsto (fun _ : ℕ ↦ quittingTerminalPayoff reward
      (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
        (quittingPureTimeBehaviorStrategy reward who (some deadline))) who)
      atTop (nhds (quittingTerminalPayoff reward
        (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
          (quittingPureTimeBehaviorStrategy reward who none)) who +
        quittingOpponentNeverProduct laws who *
          reward (quittingSingletonTerminal who) who)) :=
    hlimit.congr' hevent
  have heq := tendsto_nhds_unique tendsto_const_nhds hconstLimit
  rw [hconstant time htime]
  simpa [quittingFiniteDeadlineNeverPayoff,
    quittingFiniteDeadlineOpponentNeverProduct, laws] using heq

/-- The unrestricted behavioral cap is exactly the displayed finite-menu cap
plus the single late-row candidate. This includes deadline zero. -/
theorem quittingContinuationBestResponseValue_finiteDeadlineTimingProfile_eq_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) (who : ι) :
    quittingContinuationBestResponseValue reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) who =
      max (quittingFiniteDeadlineReplyCap reward deadline mixed who)
        (quittingFiniteDeadlineNeverPayoff reward deadline mixed who +
          quittingFiniteDeadlineOpponentNeverProduct deadline mixed who *
            reward (quittingSingletonTerminal who) who) := by
  let profile := quittingFiniteDeadlineTimingProfile reward deadline mixed
  let late := quittingFiniteDeadlineNeverPayoff reward deadline mixed who +
    quittingFiniteDeadlineOpponentNeverProduct deadline mixed who *
      reward (quittingSingletonTerminal who) who
  apply le_antisymm
  · rw [show quittingContinuationBestResponseValue reward profile who =
        sSup (Set.range fun choice : Option ℕ ↦ quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who choice)) who) by
      unfold quittingContinuationBestResponseValue
      exact sSup_range_quittingTerminalPayoff_update_eq_pureTime reward profile who]
    apply csSup_le
    · exact ⟨_, ⟨none, rfl⟩⟩
    · rintro value ⟨choice, rfl⟩
      cases choice with
      | none =>
          apply le_max_of_le_left
          exact quittingFiniteDeadline_purePayoff_le_replyCap reward deadline mixed who none
      | some time =>
          by_cases htime : time < deadline
          · apply le_max_of_le_left
            exact quittingFiniteDeadline_purePayoff_le_replyCap reward deadline mixed who
              (some ⟨time, htime⟩)
          · apply le_max_of_le_right
            change _ ≤ late
            exact le_of_eq (quittingFiniteDeadlineTimingProfile_pureTime_eq_never_add_of_le
              reward deadline mixed who (by omega))
  · apply max_le
    · apply Finset.sup'_le
      intro action _
      exact quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile who _
    · rw [← quittingFiniteDeadlineTimingProfile_pureTime_eq_never_add_of_le
        reward deadline mixed who (le_rfl : deadline ≤ deadline)]
      exact quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile who _

def quittingFiniteDeadlineMenuDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) (who : ι) : ℝ :=
  quittingFiniteDeadlineReplyCap reward deadline mixed who -
    quittingTerminalPayoff reward (quittingFiniteDeadlineTimingProfile reward deadline mixed) who

def quittingFiniteDeadlineMenuExploitability [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) : ℝ :=
  QuittingBoundaryHolonomy.finitePlayerMax fun who ↦
    quittingFiniteDeadlineMenuDebt reward deadline mixed who

theorem quittingFiniteDeadlineMenuDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) (who : ι) :
    0 ≤ quittingFiniteDeadlineMenuDebt reward deadline mixed who := by
  let game := quittingFiniteDeadlineTimingGame reward deadline
  let value := fun action : QuittingFiniteDeadlineTimingAction deadline ↦
    game.mixedExtension.eu (Function.update mixed who (PMF.pure action)) who
  have hbound : ∀ action, |value action| ≤ quittingRewardBound reward := by
    intro action
    rw [show value action = quittingTerminalPayoff reward
        (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
          (quittingPureTimeBehaviorStrategy reward who
            (quittingFiniteDeadlineTimingActionTime action))) who by
      exact (quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
        reward deadline mixed who action).symm]
    exact abs_quittingTerminalPayoff_le reward _ who (abs_reward_le_quittingRewardBound reward)
  obtain ⟨action, _, hmean⟩ :=
    Math.ProbabilityMassFunction.exists_mem_support_expect_le (mixed who) value hbound
  have havg : game.mixedExtension.eu mixed who =
      Math.Probability.expect (mixed who) value := by
    simpa [game, value] using game.mixedExtension_eu_update mixed who (mixed who)
  unfold quittingFiniteDeadlineMenuDebt
  have hcap := quittingFiniteDeadline_purePayoff_le_replyCap
    reward deadline mixed who action
  rw [quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU] at hcap
  rw [quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU, havg]
  linarith

omit [DecidableEq ι] in
theorem finiteDeadlineJointNeverProduct_eq_zero_of_player_never_eq_zero
    (deadline : ℕ) (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (hzero : (mixed who none).toReal = 0) :
    quittingFiniteDeadlineJointNeverProduct deadline mixed = 0 := by
  unfold quittingFiniteDeadlineJointNeverProduct
  exact Finset.prod_eq_zero (Finset.mem_univ who) hzero

end GameTheory
