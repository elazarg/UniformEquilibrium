import UniformEquilibrium.Quitting.Punishment.FiniteMenuCompletion
import UniformEquilibrium.Quitting.Terminal.FiniteMenuEarlyAbsorption
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-! # Early finite-menu absorption produces one uniform-equilibrium payoff -/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The early-absorption source predicate produces actual terminal approximate
Nash profiles at every accuracy, with no reward-sign assumption. -/
theorem terminalNash_all_errors_of_finiteMenuEarlyAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hearly : HasQuittingFiniteMenuEarlyAbsorption reward) :
    ∀ accuracy : ℝ, 0 < accuracy →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) accuracy profile := by
  intro accuracy haccuracy
  let bound := quittingRewardBound reward
  have hbound : 0 ≤ bound := quittingRewardBound_nonneg reward
  let scale := min 1 (accuracy / (16 * (bound + 1)))
  have hden : 0 < 16 * (bound + 1) := by positivity
  have hscale : 0 < scale := lt_min one_pos (div_pos haccuracy hden)
  have hscaleOne : scale ≤ 1 := min_le_left _ _
  have hscaleBound : scale * (16 * (bound + 1)) ≤ accuracy :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hscaled : 2 * bound * scale < accuracy / 4 := by nlinarith
  have hsquare : scale ^ 2 ≤ scale := by nlinarith
  have hreach : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hpayoffSmall : 2 * bound * scale ^ 2 < accuracy / 4 := by
    have h := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ 2 * bound by positivity)
    exact h.trans_lt hscaled
  have hcapSmall : 2 * bound * Real.sqrt (scale ^ 2) < accuracy / 4 := by
    rwa [Real.sqrt_sq_eq_abs, abs_of_pos hscale]
  have hdeficit : ∀ᶠ horizon in atTop,
      quittingFiniteMenuPunishmentDeficit reward horizon < accuracy / 8 :=
    (tendsto_order.1 (tendsto_quittingFiniteMenuPunishmentDeficit reward)).2
      (accuracy / 8) (by positivity)
  obtain ⟨horizon, hhorizon, hsmall⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and hdeficit).exists
  obtain ⟨deadline, hdeadline, mixed, hnash, hsurvival⟩ :=
    hearly (accuracy / 4) (by positivity) horizon hhorizon (scale ^ 2) hreach 1
  obtain ⟨target, root, _, _, hcompletion⟩ :=
    exists_finiteMenu_samePrefix_completion reward
      (abs_reward_le_quittingRewardBound reward) deadline horizon
      ((le_max_left horizon 1).trans hdeadline) mixed hnash hreach
      (show 0 < accuracy / 8 by positivity) hsurvival
  have hmaximum : max (2 * bound * Real.sqrt (scale ^ 2))
      (quittingFiniteMenuPunishmentDeficit reward horizon + accuracy / 8) < accuracy / 4 :=
    max_lt hcapSmall (by linarith)
  refine ⟨quittingFiniteMenuPunishmentCompletionProfile reward mixed horizon target root, ?_⟩
  apply isεAsymptoticNash_of_quittingTerminalExploitability_le
  apply hcompletion.trans
  change accuracy / 4 + 2 * bound * scale ^ 2 +
    max (2 * bound * Real.sqrt (scale ^ 2))
      (quittingFiniteMenuPunishmentDeficit reward horizon + accuracy / 8) ≤ accuracy
  linarith

/-- The accuracy-dependent completions select one fixed uniform payoff through
the established terminal semantic endpoint. The source profile need not itself
have a small unrestricted deviation cap. -/
theorem exists_uniformEquilibriumPayoff_of_finiteMenuEarlyAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hearly : HasQuittingFiniteMenuEarlyAbsorption reward) :
    ∃ payoff : Payoff ι, (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  (quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors reward).2
    (terminalNash_all_errors_of_finiteMenuEarlyAbsorption reward hearly)

end GameTheory
