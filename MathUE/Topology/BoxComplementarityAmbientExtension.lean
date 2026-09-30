import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.MetricSpace.Bounded
import MathUE.Topology.BoxComplementarityAmbientMapAdapter
import MathUE.Topology.BoxComplementarityFrontierReplacement

/-!
# Continuous ambient extensions in one positive rectangular chart

A bounded source region and a field continuous only on its closure give an
actual enclosing positive-width rectangle and a continuous global extension.
For a fixed chart, any two extensions agreeing on the source closure have
the same existing local complementarity degree on the pulled-back region,
provided the source frontier is zero-free.

This is an extension prerequisite and independence result, not a completed
ambient Brouwer-degree construction or a chart-independence theorem.
-/

noncomputable section

namespace Math.Topology

open Set

/-- A bounded finite-dimensional source has a positive-width rectangular
enclosure and a global continuous extension of every field continuous on its
closure. Neither openness nor nonemptiness is needed for this prerequisite. -/
theorem exists_rectangular_continuousExtension_of_isBounded
    {ι : Type} [Fintype ι] (region : Set (ι → ℝ))
    (hbounded : Bornology.IsBounded region)
    (field : (ι → ℝ) → ι → ℝ) (hfield : ContinuousOn field (closure region)) :
    ∃ lower upper : ι → ℝ,
      (∀ who, lower who < upper who) ∧
      closure region ⊆ {point | ∀ who, lower who < point who ∧ point who < upper who} ∧
      ∃ extension : C(ι → ℝ, ι → ℝ), EqOn extension field (closure region) := by
  obtain ⟨radius, hradius, henclosure⟩ :=
    hbounded.closure.subset_ball_lt (0 : ℝ) (0 : ι → ℝ)
  let source : C(closure region, ι → ℝ) :=
    ⟨(closure region).domRestrict field, hfield.domRestrict⟩
  obtain ⟨extension, hextension⟩ :=
    ContinuousMap.exists_restrict_eq isClosed_closure source
  refine ⟨(fun _ => -radius), (fun _ => radius), ?_, ?_, extension, ?_⟩
  · intro who
    linarith
  · intro point hpoint who
    have hnorm : ‖point‖ < radius := by
      simpa only [Metric.mem_ball, dist_zero_right] using henclosure hpoint
    have hcoordinate : |point who| < radius := by
      have hnormCoordinate := norm_le_pi_norm point who
      rw [Real.norm_eq_abs] at hnormCoordinate
      exact hnormCoordinate.trans_lt hnorm
    exact abs_lt.mp hcoordinate
  · intro point hpoint
    exact congrArg
      (fun map : C(closure region, ι → ℝ) => map ⟨point, hpoint⟩) hextension

end Math.Topology

namespace Math.BoxComplementarityProblem

open Set Math.Topology

/-- In the same chart, two fields continuous on the closed rectangle and
equal to one source field on the source closure have the same existing local
degree. Both isolations are derived from the source's zero-free frontier. -/
theorem localDegree_ofAmbientMap_eq_of_extensions
    {n : ℕ} (lower upper : Fin n → ℝ) (hwidth : ∀ who, lower who < upper who)
    (region : Set (Fin n → ℝ)) (hopen : IsOpen region)
    (hclosure : closure region ⊆
      {point | ∀ who, lower who < point who ∧ point who < upper who})
    (field first second : (Fin n → ℝ) → Fin n → ℝ)
    (hfirst : ContinuousOn first (Icc lower upper))
    (hsecond : ContinuousOn second (Icc lower upper))
    (hfirstEqual : EqOn first field (closure region))
    (hsecondEqual : EqOn second field (closure region))
    (hzeroFree : ∀ point ∈ frontier region, field point ≠ 0) :
    let firstProblem := ofAmbientMap lower upper hwidth first hfirst
    let secondProblem := ofAmbientMap lower upper hwidth second hsecond
    let cubeRegion := rectangularCubePoint lower upper ⁻¹' region
    ∃ hfirstIsolating : firstProblem.IsIsolating cubeRegion,
      ∃ hsecondIsolating : secondProblem.IsIsolating cubeRegion,
        firstProblem.localDegree cubeRegion hfirstIsolating =
          secondProblem.localDegree cubeRegion hsecondIsolating := by
  let firstProblem := ofAmbientMap lower upper hwidth first hfirst
  let secondProblem := ofAmbientMap lower upper hwidth second hsecond
  let cubeRegion := rectangularCubePoint lower upper ⁻¹' region
  have hfirstZeroFree : ∀ point ∈ frontier region, first point ≠ 0 := by
    intro point hpoint
    rw [hfirstEqual (frontier_subset_closure hpoint)]
    exact hzeroFree point hpoint
  have hfirstIsolating : firstProblem.IsIsolating cubeRegion :=
    isIsolating_ofAmbientMap_preimage_of_closure_subset lower upper hwidth
      first hfirst region hopen hclosure hfirstZeroFree
  have hequal : EqOn firstProblem.gain secondProblem.gain (frontier cubeRegion) := by
    intro point hpoint
    have hsource : rectangularCubePoint lower upper point ∈ frontier region :=
      (continuous_rectangularCubePoint lower upper).frontier_preimage_subset region hpoint
    have hsourceClosure := frontier_subset_closure hsource
    have hfields : first (rectangularCubePoint lower upper point) =
        second (rectangularCubePoint lower upper point) :=
      (hfirstEqual hsourceClosure).trans (hsecondEqual hsourceClosure).symm
    funext who
    change -first (rectangularCubePoint lower upper point) who =
      -second (rectangularCubePoint lower upper point) who
    exact congrArg (fun value : Fin n → ℝ => -value who) hfields
  refine ⟨hfirstIsolating,
    firstProblem.isIsolating_of_gain_eqOn_frontier secondProblem cubeRegion
      hfirstIsolating hequal, ?_⟩
  exact firstProblem.localDegree_eq_of_gain_eqOn_frontier secondProblem cubeRegion
    hfirstIsolating hequal

end Math.BoxComplementarityProblem
