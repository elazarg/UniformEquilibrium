/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Calculus.Monotone
import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQContinuousPath

/-!
# Almost-everywhere rates of continuous singleton paths

A normalized monotone singleton-mass path has ordinary derivatives almost
everywhere on the open clock interval.  These derivatives are nonnegative,
sum to one, and a positive derivative activates the upper sequential-
perfection inequality.  This is the original-clock density certificate; a
logarithmic reparametrization can scale these rates without changing their
support.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Filter Finset Set unitInterval
open MeasureTheory QuittingAbsorptionPath
open scoped Topology unitInterval

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The ordinary-clock density of one singleton mass coordinate. -/
def ContinuousZeroPerfectSingletonPath.clockRate
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) (time : ℝ) : ℝ :=
  deriv (fun second => witness.mass.extend second who) time

theorem ContinuousZeroPerfectSingletonPath.monotone_mass_extend
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward) (who : ι) :
    Monotone fun time => witness.mass.extend time who := by
  change Monotone fun time =>
    Set.IccExtend (show (0 : ℝ) ≤ 1 by norm_num)
      (fun clock : unitInterval => witness.mass clock who) time
  exact (witness.monotone who).IccExtend (by norm_num)

theorem ContinuousZeroPerfectSingletonPath.clockRate_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) (time : ℝ) :
    0 ≤ witness.clockRate who time :=
  (witness.monotone_mass_extend who).deriv_nonneg

/-- All singleton mass coordinates are differentiable almost everywhere. -/
theorem ContinuousZeroPerfectSingletonPath.ae_forall_differentiableAt_mass_extend
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward) :
    ∀ᵐ time : ℝ, ∀ who,
      DifferentiableAt ℝ (fun second => witness.mass.extend second who) time := by
  apply Filter.eventually_all.mpr
  intro who
  exact (witness.monotone_mass_extend who).ae_differentiableAt

/-- At an interior differentiability point, the path's lower right derivative
is the ordinary derivative of the corresponding mass coordinate. -/
theorem ContinuousZeroPerfectSingletonPath.pathRightDerivative_eq_clockRate
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {time : ℝ} (htime : time ∈ Set.Ioo (0 : ℝ) 1) (who : ι)
    (hdifferentiable : DifferentiableAt ℝ
      (fun second => witness.mass.extend second who) time) :
    pathRightDerivative witness.path.1 time
        (quittingProjectiveSingletonTerminal who) =
      witness.clockRate who time := by
  letI : NeBot (nhdsWithin time (Set.Ioo time 1)) :=
    left_nhdsWithin_Ioo_neBot htime.2
  have htendstoSlope : Tendsto
      (slope (fun second => witness.mass.extend second who) time)
      (nhdsWithin time {time}ᶜ) (𝓝 (witness.clockRate who time)) := by
    exact hasDerivAt_iff_tendsto_slope.mp hdifferentiable.hasDerivAt
  have hfilter : nhdsWithin time (Set.Ioo time 1) ≤
      nhdsWithin time {time}ᶜ := by
    apply inf_le_inf_left
    apply principal_mono.mpr
    intro second hsecond
    exact ne_of_gt hsecond.1
  have htendsto : Tendsto
      (fun second =>
        (witness.mass.extend second who - witness.mass.extend time who) /
          (second - time))
      (nhdsWithin time (Set.Ioo time 1))
      (𝓝 (witness.clockRate who time)) := by
    have hslope := htendstoSlope.mono_left hfilter
    change Tendsto
      (fun second => (second - time)⁻¹ *
        (witness.mass.extend second who - witness.mass.extend time who))
      (nhdsWithin time (Set.Ioo time 1))
      (𝓝 (witness.clockRate who time)) at hslope
    simpa only [div_eq_inv_mul] using hslope
  unfold ContinuousZeroPerfectSingletonPath.path pathRightDerivative
    singletonAbsorptionPathOfPlayerPath singletonCadlagPathOfPlayerPath
  simp_rw [singletonCoalitionMass_singleton]
  exact htendsto.liminf_eq

/-- At almost every interior time the nonnegative singleton rates sum to the
unit clock rate. -/
theorem ContinuousZeroPerfectSingletonPath.ae_sum_clockRate_eq_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward) :
    ∀ᵐ time : ℝ, time ∈ Set.Ioo (0 : ℝ) 1 →
      ∑ who, witness.clockRate who time = 1 := by
  filter_upwards [witness.ae_forall_differentiableAt_mass_extend]
    with time hdifferentiable htime
  have hsumDeriv : HasDerivAt
      (fun second => ∑ who, witness.mass.extend second who)
      (∑ who, witness.clockRate who time) time := by
    have hraw := HasDerivAt.sum fun who (_ : who ∈ Finset.univ) =>
      (hdifferentiable who).hasDerivAt
    have hfun : (∑ who, fun second => witness.mass.extend second who) =
        (fun second => ∑ who, witness.mass.extend second who) := by
      funext second
      exact Finset.sum_apply second Finset.univ
        (fun who second => witness.mass.extend second who)
    rw [hfun] at hraw
    simpa only [ContinuousZeroPerfectSingletonPath.clockRate] using hraw
  have hlocal :
      (fun second => ∑ who, witness.mass.extend second who) =ᶠ[𝓝 time]
        fun second => second := by
    filter_upwards [Ioo_mem_nhds htime.1 htime.2] with second hsecond
    rw [show witness.mass.extend second =
        witness.mass ⟨second, hsecond.1.le, hsecond.2.le⟩ from
      Path.extend_apply witness.mass ⟨hsecond.1.le, hsecond.2.le⟩,
      witness.total]
  have hid : HasDerivAt
      (fun second => ∑ who, witness.mass.extend second who) 1 time := by
    exact hlocal.hasDerivAt_iff.mpr (hasDerivAt_id time)
  exact hsumDeriv.unique hid

/-- Positive singleton density implies exact active-owner indifference at
every interior differentiability point. -/
theorem ContinuousZeroPerfectSingletonPath.payoff_eq_solo_of_clockRate_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {time : ℝ} (htime : time ∈ Set.Ioo (0 : ℝ) 1) (who : ι)
    (hdifferentiable : DifferentiableAt ℝ
      (fun second => witness.mass.extend second who) time)
    (hpositive : 0 < witness.clockRate who time) :
    absorptionPathPayoff reward witness.path time who =
      quittingSoloReward reward who who := by
  have hpathTime : time ∈ pathTimes witness.path.1 := by
    rw [witness.continuous]
    exact ⟨htime.1.le, htime.2.le⟩
  have htimeOne : time ≠ 1 := ne_of_lt htime.2
  have hperfect := (witness.zeroPerfect who).2 time hpathTime htimeOne
  have hderivative : 0 < pathRightDerivative witness.path.1 time
      (quittingProjectiveSingletonTerminal who) := by
    rwa [witness.pathRightDerivative_eq_clockRate htime who hdifferentiable]
  have hlower := hperfect.1
  have hupper := hperfect.2 hderivative
  change quittingSoloReward reward who who - 0 ≤
      absorptionPathPayoff reward witness.path time who at hlower
  change absorptionPathPayoff reward witness.path time who ≤
      quittingSoloReward reward who who + 0 at hupper
  linarith

/-- Almost everywhere, every active singleton density coordinate is exactly
indifferent between continuation and solo quitting. -/
theorem ContinuousZeroPerfectSingletonPath.ae_active_clockRate_indifferent
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward) :
    ∀ᵐ time : ℝ, time ∈ Set.Ioo (0 : ℝ) 1 → ∀ who,
      0 < witness.clockRate who time →
        absorptionPathPayoff reward witness.path time who =
          quittingSoloReward reward who who := by
  filter_upwards [witness.ae_forall_differentiableAt_mass_extend]
    with time hdifferentiable htime who hpositive
  exact witness.payoff_eq_solo_of_clockRate_pos
    htime who (hdifferentiable who) hpositive

end QuittingLCPClassification
end GameTheory
