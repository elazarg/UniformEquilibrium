import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Convex
import UniformEquilibrium.Quitting.Stationary.DiscountedAmbientQuadraticRemainder
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotient

/-! # Cube response invariance is the actual whole-ambient identity

The existing residual is analytic after coordinate repetition. Equality on
the cube supplies an actual neighborhood of its center, so analytic uniqueness
extends it throughout the connected signed ambient space. Empty block index
types are covered by the same finite-product neighborhood theorem.
-/

noncomputable section

namespace GameTheory

open Set Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- Coordinate repetition and recipient projection retain actual analyticity. -/
theorem analyticAt_quittingBlockResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (who : ι) (point : Fin k → ℝ) :
    AnalyticAt ℝ (fun source : Fin k → ℝ =>
      quittingDiscountedDisplacement reward 0 (quittingBlockLift block source) who) point := by
  have hlift : AnalyticAt ℝ (quittingBlockLift block) point := by
    change AnalyticAt ℝ (fun source : Fin k → ℝ => fun player => source (block player)) point
    apply AnalyticAt.pi
    intro player
    exact (ContinuousLinearMap.proj (block player) :
      (Fin k → ℝ) →L[ℝ] ℝ).analyticAt point
  have hpath : AnalyticAt ℝ (fun source : Fin k → ℝ =>
      ((0 : ℝ), quittingBlockLift block source)) point :=
    analyticAt_const.prod hlift
  have hfull : AnalyticAt ℝ (fun source : Fin k → ℝ =>
      quittingDiscountedDisplacement reward 0 (quittingBlockLift block source)) point := by
    simpa only [Function.comp_def] using
      (analyticAt_quittingDiscountedDisplacement reward
        ((0 : ℝ), quittingBlockLift block point)).comp
          (f := fun source : Fin k → ℝ => ((0 : ℝ), quittingBlockLift block source))
          (x := point) hpath
  have hproject := ((ContinuousLinearMap.proj who : (ι → ℝ) →L[ℝ] ℝ).analyticAt
    (quittingDiscountedDisplacement reward 0 (quittingBlockLift block point))).comp
      (f := fun source : Fin k → ℝ =>
        quittingDiscountedDisplacement reward 0 (quittingBlockLift block source))
      (x := point) hfull
  simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using hproject

/-- The actual cube identity extends to every signed block vector. No polynomial
coefficient data, selected representatives or equilibrium witness is assumed. -/
theorem quittingBlockResponse_eq_of_responseInvariant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (first second : ι) (hblock : block first = block second) (point : Fin k → ℝ) :
    quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) first =
      quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) second := by
  have hfirst : AnalyticOnNhd ℝ (fun source : Fin k → ℝ =>
      quittingDiscountedDisplacement reward 0 (quittingBlockLift block source) first) univ :=
    fun source _ => analyticAt_quittingBlockResponse reward block first source
  have hsecond : AnalyticOnNhd ℝ (fun source : Fin k → ℝ =>
      quittingDiscountedDisplacement reward 0 (quittingBlockLift block source) second) univ :=
    fun source _ => analyticAt_quittingBlockResponse reward block second source
  let center : Fin k → ℝ := fun _ => 1 / 2
  have hcube : Icc (0 : Fin k → ℝ) 1 ∈ 𝓝 center :=
    pi_Icc_mem_nhds'
      (by intro coordinate; change (0 : ℝ) < 1 / 2; norm_num)
      (by intro coordinate; change (1 / 2 : ℝ) < 1; norm_num)
  have heventually : (fun source : Fin k → ℝ =>
      quittingDiscountedDisplacement reward 0 (quittingBlockLift block source) first) =ᶠ[𝓝 center]
      (fun source : Fin k → ℝ =>
        quittingDiscountedDisplacement reward 0 (quittingBlockLift block source) second) := by
    filter_upwards [hcube] with source hsource
    exact hresponse source (fun coordinate => ⟨hsource.1 coordinate, hsource.2 coordinate⟩)
      first second hblock
  exact congrFun (hfirst.eq_of_eventuallyEq hsecond heventually) point

/-- Cube response invariance and literal whole-signed-ambient equality are equivalent.
The separate finite linear coefficient encoding is not asserted by this theorem. -/
theorem quittingResponseInvariantOnUnitCube_iff_forall_ambient
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (block : ι → Fin k) :
    QuittingResponseInvariantOnUnitCube reward block ↔
      ∀ point : Fin k → ℝ, ∀ first second : ι, block first = block second →
        quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) first =
          quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) second := by
  constructor
  · intro hresponse point first second hblock
    exact quittingBlockResponse_eq_of_responseInvariant
      reward block hresponse first second hblock point
  · intro hambient point _ first second hblock
    exact hambient point first second hblock

end GameTheory
