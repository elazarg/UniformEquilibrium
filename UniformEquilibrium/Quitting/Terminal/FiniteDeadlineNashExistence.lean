import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineFullReplyCap

/-! # Exact mixed Nash laws on finite timing menus -/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mixedNash_isQuittingFiniteDeadlineNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash mixed) :
    IsQuittingFiniteDeadlineNash reward deadline 0 mixed := by
  rw [isQuittingFiniteDeadlineNash_iff_pure]
  intro who action
  rw [add_zero, quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU,
    quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU]
  exact hnash who (PMF.pure action)

/-- A fresh exact finite-menu Nash law exists at every deadline, including zero. -/
theorem exists_exactFiniteDeadlineTimingNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash mixed ∧
      IsQuittingFiniteDeadlineNash reward deadline 0 mixed := by
  letI : ∀ player, Finite
      ((quittingFiniteDeadlineTimingGame reward deadline).Strategy player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI : ∀ player, Nonempty
      ((quittingFiniteDeadlineTimingGame reward deadline).Strategy player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI : Finite (quittingFiniteDeadlineTimingGame reward deadline).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  obtain ⟨mixed, hnash⟩ :=
    (quittingFiniteDeadlineTimingGame reward deadline).mixed_nash_exists
  exact ⟨mixed, hnash, mixedNash_isQuittingFiniteDeadlineNash reward deadline mixed hnash⟩

theorem finiteDeadline_mixedNash_neverSupport_payoff_eq_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) (pivot : ι)
    (hnash : (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash mixed)
    (hsupport : 0 < (mixed pivot none).toReal) :
    quittingTerminalPayoff reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot =
      quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot := by
  let game := quittingFiniteDeadlineTimingGame reward deadline
  let value := fun action : QuittingFiniteDeadlineTimingAction deadline ↦
    game.mixedExtension.eu (Function.update mixed pivot (PMF.pure action)) pivot
  let prescribed := game.mixedExtension.eu mixed pivot
  have havg : prescribed = Math.Probability.expect (mixed pivot) value := by
    simpa [game, value, prescribed] using game.mixedExtension_eu_update mixed pivot (mixed pivot)
  have hle : ∀ action, value action ≤ prescribed := fun action ↦ hnash pivot (PMF.pure action)
  have hvalue : ∀ action, |value action| ≤ quittingRewardBound reward := by
    intro action
    rw [show value action = quittingTerminalPayoff reward
        (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot
          (quittingPureTimeBehaviorStrategy reward pivot
            (quittingFiniteDeadlineTimingActionTime action))) pivot by
      exact (quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
        reward deadline mixed pivot action).symm]
    exact abs_quittingTerminalPayoff_le reward _ pivot (abs_reward_le_quittingRewardBound reward)
  have hprescribed : |prescribed| ≤ quittingRewardBound reward := by
    dsimp [prescribed, game]
    rw [← quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU]
    exact abs_quittingTerminalPayoff_le reward _ pivot (abs_reward_le_quittingRewardBound reward)
  have hnone : none ∈ (mixed pivot).support := by
    rw [PMF.mem_support_iff]
    intro hzero
    rw [hzero] at hsupport
    simp at hsupport
  have heq : value none = prescribed := by
    apply le_antisymm (hle none)
    by_contra hnot
    have hstrict : value none < prescribed := lt_of_not_ge hnot
    have hlt := Math.ProbabilityMassFunction.expect_lt_of_le_on_support_of_bounded
      (mixed pivot) value (fun _ ↦ prescribed) hvalue
      (fun _ ↦ hprescribed) (fun action _ ↦ hle action) ⟨none, hnone, hstrict⟩
    rw [← havg, Math.Probability.expect_const] at hlt
    linarith
  rw [quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU]
  change prescribed = _
  rw [← heq]
  exact (quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
    reward deadline mixed pivot none).symm

end GameTheory
