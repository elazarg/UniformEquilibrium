import MathUE.Topology.BoxComplementarityAmbientExtension
import MathUE.Topology.BoxComplementarityRectangularChartIndependence

/-!
# Intrinsic ambient degree: construction and computation

The source is an actual field, an open bounded region, and a target absent
from its frontier image. Continuity is required only on the source closure.
An enclosing positive rectangle and a continuous extension are constructed
internally. Chart independence and extension independence make the resulting
integer independent of both auxiliary choices.

This module constructs the operation and its actual-field comparison theorem.
Homotopy, signed affine normalization, and the full ambient degree properties
are separate consumers; their identification must not be inferred from the
definition alone. Nonisolated roots, empty sources, and dimension zero are
not excluded.
-/

noncomputable section

namespace Math.Topology

open Set

variable {n : ℕ}

/-- A source-owned extension and positive chart derive actual isolation after
subtracting the requested target. -/
theorem isIsolating_ambientExtension
    (field : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ))
    (target : Fin n → ℝ) (hopen : IsOpen region)
    (hfrontier : ∀ point ∈ frontier region, field point ≠ target)
    (lower upper : Fin n → ℝ) (hwidth : ∀ who, lower who < upper who)
    (hclosure : closure region ⊆
      {point | ∀ who, lower who < point who ∧ point who < upper who})
    (extension : (Fin n → ℝ) → Fin n → ℝ)
    (hExtension : ContinuousOn extension (Icc lower upper))
    (hEqual : EqOn extension field (closure region)) :
    (BoxComplementarityProblem.ofAmbientMap lower upper hwidth
      (fun point => extension point - target) (hExtension.sub continuousOn_const)).IsIsolating
      (rectangularCubePoint lower upper ⁻¹' region) := by
  apply BoxComplementarityProblem.isIsolating_ofAmbientMap_preimage_of_closure_subset
    lower upper hwidth (fun point => extension point - target)
    (hExtension.sub continuousOn_const) region hopen hclosure
  intro point hpoint
  rw [hEqual (frontier_subset_closure hpoint)]
  exact sub_ne_zero.mpr (hfrontier point hpoint)

private structure AmbientDegreeAuxiliary
    (field : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ)) where
  lower : Fin n → ℝ
  upper : Fin n → ℝ
  width : ∀ who, lower who < upper who
  enclosure : closure region ⊆
    {point | ∀ who, lower who < point who ∧ point who < upper who}
  extension : C(Fin n → ℝ, Fin n → ℝ)
  agrees : EqOn extension field (closure region)

private theorem exists_ambientDegreeAuxiliary
    (field : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ))
    (hbounded : Bornology.IsBounded region)
    (hfield : ContinuousOn field (closure region)) :
    Nonempty (AmbientDegreeAuxiliary field region) := by
  obtain ⟨lower, upper, hwidth, hclosure, extension, hEqual⟩ :=
    exists_rectangular_continuousExtension_of_isBounded region hbounded field hfield
  exact ⟨⟨lower, upper, hwidth, hclosure, extension, hEqual⟩⟩

private def chosenAmbientDegreeAuxiliary
    (field : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ))
    (hbounded : Bornology.IsBounded region)
    (hfield : ContinuousOn field (closure region)) : AmbientDegreeAuxiliary field region :=
  Classical.choice (exists_ambientDegreeAuxiliary field region hbounded hfield)

private def AmbientDegreeAuxiliary.degree
    {field : (Fin n → ℝ) → Fin n → ℝ} {region : Set (Fin n → ℝ)}
    (auxiliary : AmbientDegreeAuxiliary field region)
    (target : Fin n → ℝ) (hopen : IsOpen region)
    (hfrontier : ∀ point ∈ frontier region, field point ≠ target) : ℤ :=
  (BoxComplementarityProblem.ofAmbientMap auxiliary.lower auxiliary.upper auxiliary.width
    (fun point => auxiliary.extension point - target)
    (auxiliary.extension.continuous.continuousOn.sub continuousOn_const)).localDegree
      (rectangularCubePoint auxiliary.lower auxiliary.upper ⁻¹' region)
      (isIsolating_ambientExtension field region target hopen hfrontier
        auxiliary.lower auxiliary.upper auxiliary.width auxiliary.enclosure
        auxiliary.extension auxiliary.extension.continuous.continuousOn auxiliary.agrees)

/-- The integer constructed from the actual ambient source. The rectangle and
extension are produced internally, rather than supplied as a fixed chart. -/
def ambientDegree
    (field : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ))
    (target : Fin n → ℝ) (hopen : IsOpen region)
    (hbounded : Bornology.IsBounded region)
    (hfield : ContinuousOn field (closure region))
    (hfrontier : ∀ point ∈ frontier region, field point ≠ target) : ℤ :=
  (chosenAmbientDegreeAuxiliary field region hbounded hfield).degree target hopen hfrontier

private theorem AmbientDegreeAuxiliary.degree_eq_of_extension
    {field : (Fin n → ℝ) → Fin n → ℝ} {region : Set (Fin n → ℝ)}
    (auxiliary : AmbientDegreeAuxiliary field region)
    (target : Fin n → ℝ) (hopen : IsOpen region)
    (hfrontier : ∀ point ∈ frontier region, field point ≠ target)
    (lower upper : Fin n → ℝ) (hwidth : ∀ who, lower who < upper who)
    (hclosure : closure region ⊆
      {point | ∀ who, lower who < point who ∧ point who < upper who})
    (extension : (Fin n → ℝ) → Fin n → ℝ)
    (hExtension : ContinuousOn extension (Icc lower upper))
    (hEqual : EqOn extension field (closure region)) :
    auxiliary.degree target hopen hfrontier =
      (BoxComplementarityProblem.ofAmbientMap lower upper hwidth
        (fun point => extension point - target)
        (hExtension.sub continuousOn_const)).localDegree
        (rectangularCubePoint lower upper ⁻¹' region)
        (isIsolating_ambientExtension field region target hopen hfrontier
          lower upper hwidth hclosure extension hExtension hEqual) := by
  have hzeroFree : ∀ point ∈ frontier region, auxiliary.extension point - target ≠ 0 := by
    intro point hpoint
    rw [auxiliary.agrees (frontier_subset_closure hpoint)]
    exact sub_ne_zero.mpr (hfrontier point hpoint)
  have hchart :=
    BoxComplementarityProblem.localDegree_ofAmbientMap_chart_independent_of_continuous
      auxiliary.lower auxiliary.upper lower upper auxiliary.width hwidth
      (fun point => auxiliary.extension point - target)
      (auxiliary.extension.continuous.sub continuous_const)
      region hopen auxiliary.enclosure hclosure hzeroFree
  have hfirstEqual : EqOn (fun point => auxiliary.extension point - target)
      (fun point => field point - target) (closure region) := by
    intro point hpoint
    exact congrArg (fun value => value - target) (auxiliary.agrees hpoint)
  have hsecondEqual : EqOn (fun point => extension point - target)
      (fun point => field point - target) (closure region) := by
    intro point hpoint
    exact congrArg (fun value => value - target) (hEqual hpoint)
  obtain ⟨hfirst, hsecond, hextensions⟩ :=
    BoxComplementarityProblem.localDegree_ofAmbientMap_eq_of_extensions
      lower upper hwidth region hopen hclosure (fun point => field point - target)
      (fun point => auxiliary.extension point - target) (fun point => extension point - target)
      (auxiliary.extension.continuous.continuousOn.sub continuousOn_const)
      (hExtension.sub continuousOn_const) hfirstEqual hsecondEqual
      (fun point hpoint => sub_ne_zero.mpr (hfrontier point hpoint))
  exact hchart.trans hextensions

/-- Any qualifying rectangle and any continuous extension agreeing with the
actual source on its closure compute the intrinsic operation. Neither the
extension nor an equality of degrees is assumed as source data. -/
theorem ambientDegree_eq_of_extension
    (field : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ))
    (target : Fin n → ℝ) (hopen : IsOpen region)
    (hbounded : Bornology.IsBounded region)
    (hfield : ContinuousOn field (closure region))
    (hfrontier : ∀ point ∈ frontier region, field point ≠ target)
    (lower upper : Fin n → ℝ) (hwidth : ∀ who, lower who < upper who)
    (hclosure : closure region ⊆
      {point | ∀ who, lower who < point who ∧ point who < upper who})
    (extension : (Fin n → ℝ) → Fin n → ℝ)
    (hExtension : ContinuousOn extension (Icc lower upper))
    (hEqual : EqOn extension field (closure region)) :
    ambientDegree field region target hopen hbounded hfield hfrontier =
      (BoxComplementarityProblem.ofAmbientMap lower upper hwidth
        (fun point => extension point - target)
        (hExtension.sub continuousOn_const)).localDegree
        (rectangularCubePoint lower upper ⁻¹' region)
        (isIsolating_ambientExtension field region target hopen hfrontier
          lower upper hwidth hclosure extension hExtension hEqual) :=
  (chosenAmbientDegreeAuxiliary field region hbounded hfield).degree_eq_of_extension
    target hopen hfrontier lower upper hwidth hclosure extension hExtension hEqual

/-- Two arbitrary qualifying chart/extension choices compute the same integer.
The source, region, and target stay fixed; the equality is derived. -/
theorem ambientDegree_auxiliary_choices_eq
    (field : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ))
    (target : Fin n → ℝ) (hopen : IsOpen region)
    (hbounded : Bornology.IsBounded region)
    (hfield : ContinuousOn field (closure region))
    (hfrontier : ∀ point ∈ frontier region, field point ≠ target)
    (lower upper : Fin 2 → Fin n → ℝ)
    (hwidth : ∀ index who, lower index who < upper index who)
    (hclosure : ∀ index, closure region ⊆
      {point | ∀ who, lower index who < point who ∧ point who < upper index who})
    (extension : Fin 2 → (Fin n → ℝ) → Fin n → ℝ)
    (hExtension : ∀ index, ContinuousOn (extension index) (Icc (lower index) (upper index)))
    (hEqual : ∀ index, EqOn (extension index) field (closure region)) :
    let chartCount := fun index : Fin 2 =>
      (BoxComplementarityProblem.ofAmbientMap (lower index) (upper index) (hwidth index)
        (fun point => extension index point - target)
        ((hExtension index).sub continuousOn_const)).localDegree
        (rectangularCubePoint (lower index) (upper index) ⁻¹' region)
        (isIsolating_ambientExtension field region target hopen hfrontier
          (lower index) (upper index) (hwidth index) (hclosure index)
          (extension index) (hExtension index) (hEqual index))
    chartCount 0 = chartCount 1 := by
  dsimp only
  exact (ambientDegree_eq_of_extension field region target hopen hbounded hfield hfrontier
    (lower 0) (upper 0) (hwidth 0) (hclosure 0) (extension 0) (hExtension 0) (hEqual 0)).symm.trans
      (ambientDegree_eq_of_extension field region target hopen hbounded hfield hfrontier
        (lower 1) (upper 1) (hwidth 1) (hclosure 1) (extension 1) (hExtension 1) (hEqual 1))

/-- A nonzero intrinsic degree produces an actual point of the source region
with the requested target value, including for nonisolated fibers. -/
theorem exists_eq_target_of_ambientDegree_ne_zero
    (field : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ))
    (target : Fin n → ℝ) (hopen : IsOpen region)
    (hbounded : Bornology.IsBounded region)
    (hfield : ContinuousOn field (closure region))
    (hfrontier : ∀ point ∈ frontier region, field point ≠ target)
    (hnonzero : ambientDegree field region target hopen hbounded hfield hfrontier ≠ 0) :
    ∃ point ∈ region, field point = target := by
  let auxiliary := chosenAmbientDegreeAuxiliary field region hbounded hfield
  let problem := BoxComplementarityProblem.ofAmbientMap
    auxiliary.lower auxiliary.upper auxiliary.width
    (fun point => auxiliary.extension point - target)
    (auxiliary.extension.continuous.continuousOn.sub continuousOn_const)
  let cubeRegion := rectangularCubePoint auxiliary.lower auxiliary.upper ⁻¹' region
  have hisolating : problem.IsIsolating cubeRegion :=
    isIsolating_ambientExtension field region target hopen hfrontier
      auxiliary.lower auxiliary.upper auxiliary.width auxiliary.enclosure
      auxiliary.extension auxiliary.extension.continuous.continuousOn auxiliary.agrees
  have hdegree : problem.localDegree cubeRegion hisolating ≠ 0 := hnonzero
  obtain ⟨point, hpoint, hsolution⟩ :=
    problem.exists_solution_mem_of_localDegree_ne_zero cubeRegion hisolating hdegree
  have hsourceClosure : rectangularCubePoint auxiliary.lower auxiliary.upper point ∈
      closure region := subset_closure hpoint
  have hzero := (BoxComplementarityProblem.isSolution_ofAmbientMap_iff_of_imageInterior
    auxiliary.lower auxiliary.upper auxiliary.width
    (fun point => auxiliary.extension point - target)
    (auxiliary.extension.continuous.continuousOn.sub continuousOn_const) point
    (auxiliary.enclosure hsourceClosure)).mp hsolution
  rw [auxiliary.agrees hsourceClosure] at hzero
  exact ⟨rectangularCubePoint auxiliary.lower auxiliary.upper point, hpoint, sub_eq_zero.mp hzero⟩

/-- A source with no target-valued point has zero intrinsic degree. This
also treats the empty source without a nonemptiness assumption. -/
theorem ambientDegree_eq_zero_of_forall_ne
    (field : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ))
    (target : Fin n → ℝ) (hopen : IsOpen region)
    (hbounded : Bornology.IsBounded region)
    (hfield : ContinuousOn field (closure region))
    (hfrontier : ∀ point ∈ frontier region, field point ≠ target)
    (hnoTarget : ∀ point ∈ region, field point ≠ target) :
    ambientDegree field region target hopen hbounded hfield hfrontier = 0 := by
  by_contra hnonzero
  obtain ⟨point, hpoint, hequal⟩ :=
    exists_eq_target_of_ambientDegree_ne_zero field region target hopen hbounded
      hfield hfrontier hnonzero
  exact hnoTarget point hpoint hequal

end Math.Topology
