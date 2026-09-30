import MathUE.Topology.BoxComplementarityAmbientMapAdapter
import MathUE.Topology.BoxComplementarityFrontierPerturbation
import MathUE.Topology.BoxComplementaritySolutionExcision
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.TietzeExtension

/-!
# Positive rectangular chart independence

The same ambient field and the same open source region are used in both
positive rectangles. Closure containment and a zero-free source frontier
derive isolation and equality of the actual normalized complementarity degrees.

A compact tube argument controls the moving source preimages. Frontier
perturbation compares nearby fields on a fixed region, and same-problem
excision then compares that region with the moving one. No finite or regular
zero inventory, differentiability, or supplied degree-equality premise is used.
-/

noncomputable section

namespace Math

open Set Filter Math.Topology
open scoped _root_.Topology

variable {n : ℕ}

namespace BoxComplementarityProblem

/-- Joint continuity and a zero-free source frontier make the degrees of moving
preimages locally constant. The family and its actual isolation are explicit. -/
theorem isLocallyConstant_localDegree_preimage
    (family : Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n))
    (hcontinuous : IsContinuousBoxComplementarityFamily (Fin n) family)
    (chart : Icc (0 : ℝ) 1 → UnitCube (Fin n) → (Fin n → ℝ))
    (hchart : Continuous fun pair : Icc (0 : ℝ) 1 × UnitCube (Fin n) =>
      chart pair.1 pair.2)
    (region : Set (Fin n → ℝ)) (hopen : IsOpen region)
    (hisolating : ∀ parameter, (family parameter).IsIsolating (chart parameter ⁻¹' region))
    (hfrontier : ∀ parameter point, (family parameter).IsSolution point →
      chart parameter point ∉ frontier region) :
    IsLocallyConstant fun parameter =>
      (family parameter).localDegree (chart parameter ⁻¹' region) (hisolating parameter) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro parameter
  let fixed := chart parameter ⁻¹' region
  have hgraph := hcontinuous.isClosed_solutionGraph
  have hbaseChart : Continuous
      (fun pair : Icc (0 : ℝ) 1 × UnitCube (Fin n) => chart parameter pair.2) :=
    hchart.comp (continuous_const.prodMk continuous_snd)
  have hmembership : ∀ᶠ nearby in 𝓝 parameter, ∀ point,
      (family nearby).IsSolution point →
        (chart nearby point ∈ region ↔ chart parameter point ∈ region) := by
    have htube : ∀ point ∈ (univ : Set (UnitCube (Fin n))),
        ∀ᶠ pair : Icc (0 : ℝ) 1 × UnitCube (Fin n) in 𝓝 (parameter, point),
          (family pair.1).IsSolution pair.2 →
            (chart pair.1 pair.2 ∈ region ↔ chart parameter pair.2 ∈ region) := by
      intro point _
      by_cases hsolution : (family parameter).IsSolution point
      · have hnotFrontier := hfrontier parameter point hsolution
        by_cases hin : chart parameter point ∈ region
        · have hnear := (hopen.preimage hchart).mem_nhds (x := (parameter, point)) hin
          have hbase := (hopen.preimage hbaseChart).mem_nhds (x := (parameter, point)) hin
          filter_upwards [hnear, hbase] with pair hnear hbase
          exact fun _ => iff_of_true hnear hbase
        · have hout : chart parameter point ∈ (closure region)ᶜ := by
            intro hclosure
            apply hnotFrontier
            rw [frontier, hopen.interior_eq]
            exact ⟨hclosure, hin⟩
          have hnear := (isClosed_closure.isOpen_compl.preimage hchart).mem_nhds
            (x := (parameter, point)) hout
          have hbase := (isClosed_closure.isOpen_compl.preimage hbaseChart).mem_nhds
            (x := (parameter, point)) hout
          filter_upwards [hnear, hbase] with pair hnear hbase
          exact fun _ => iff_of_false
            (fun h => hnear (subset_closure h)) (fun h => hbase (subset_closure h))
      · have hnear := hgraph.isOpen_compl.mem_nhds (x := (parameter, point)) hsolution
        filter_upwards [hnear] with pair hnear
        exact fun h => False.elim (hnear h)
    have hcompact : IsCompact (univ : Set (UnitCube (Fin n))) := isCompact_univ
    have hnearby := hcompact.eventually_forall_of_forall_eventually
      (P := fun nearby point => (family nearby).IsSolution point →
        (chart nearby point ∈ region ↔ chart parameter point ∈ region)) htube
    filter_upwards [hnearby] with nearby hnear point
    exact hnear point (mem_univ point)
  obtain ⟨tolerance, htolerance, hstable⟩ :=
    (family parameter).exists_pos_localDegree_eq_of_norm_sub_lt fixed (hisolating parameter)
  have hgain : Continuous
      (fun pair : Icc (0 : ℝ) 1 × UnitCube (Fin n) => (family pair.1).gain pair.2) :=
    continuous_pi hcontinuous
  have hbaseGain : Continuous
      (fun pair : Icc (0 : ℝ) 1 × UnitCube (Fin n) => (family parameter).gain pair.2) :=
    (continuous_pi (family parameter).continuous_gain).comp continuous_snd
  have hclose : ∀ᶠ nearby in 𝓝 parameter, ∀ point ∈ frontier fixed,
      ‖(family nearby).gain point - (family parameter).gain point‖ < tolerance := by
    apply isClosed_frontier.isCompact.eventually_forall_of_forall_eventually
    intro point _
    exact (isOpen_lt (hgain.sub hbaseGain).norm continuous_const).mem_nhds
      (by simpa using htolerance)
  filter_upwards [hmembership, hclose] with nearby hmembership hclose
  obtain ⟨hfixed, hdegree⟩ := hstable (family nearby) hclose
  have hselected : (family nearby).solutionsIn (chart nearby ⁻¹' region) =
      (family nearby).solutionsIn fixed := by
    ext point
    change ((family nearby).IsSolution point ∧ chart nearby point ∈ region) ↔
      ((family nearby).IsSolution point ∧ chart parameter point ∈ region)
    constructor
    · exact fun h => ⟨h.1, (hmembership point h.1).mp h.2⟩
    · exact fun h => ⟨h.1, (hmembership point h.1).mpr h.2⟩
  exact ((family nearby).localDegree_eq_of_solutionsIn_eq _ _
    (hisolating nearby) hfixed hselected).trans hdegree.symm

private theorem rectangular_mix_pos (parameter : Icc (0 : ℝ) 1)
    {first second : ℝ} (hfirst : 0 < first) (hsecond : 0 < second) :
    0 < (1 - (parameter : ℝ)) * first + (parameter : ℝ) * second := by
  by_cases hzero : (parameter : ℝ) = 0
  · simpa [hzero] using hfirst
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr parameter.property.2) hfirst.le)
      (mul_pos (lt_of_le_of_ne parameter.property.1 (Ne.symm hzero)) hsecond)

/-- With a globally continuous source field, literal rectangle interpolation
and the moving-preimage theorem identify the two actual chart counts. -/
theorem localDegree_ofAmbientMap_chart_independent_of_continuous
    (lower₀ upper₀ lower₁ upper₁ : Fin n → ℝ)
    (hwidth₀ : ∀ who, lower₀ who < upper₀ who)
    (hwidth₁ : ∀ who, lower₁ who < upper₁ who)
    (field : (Fin n → ℝ) → Fin n → ℝ) (hfield : Continuous field)
    (region : Set (Fin n → ℝ)) (hopen : IsOpen region)
    (hclosure₀ : closure region ⊆
      {point | ∀ who, lower₀ who < point who ∧ point who < upper₀ who})
    (hclosure₁ : closure region ⊆
      {point | ∀ who, lower₁ who < point who ∧ point who < upper₁ who})
    (hzeroFree : ∀ point ∈ frontier region, field point ≠ 0) :
    (ofAmbientMap lower₀ upper₀ hwidth₀ field hfield.continuousOn).localDegree
        (rectangularCubePoint lower₀ upper₀ ⁻¹' region)
        (isIsolating_ofAmbientMap_preimage_of_closure_subset lower₀ upper₀ hwidth₀
          field hfield.continuousOn region hopen hclosure₀ hzeroFree) =
      (ofAmbientMap lower₁ upper₁ hwidth₁ field hfield.continuousOn).localDegree
        (rectangularCubePoint lower₁ upper₁ ⁻¹' region)
        (isIsolating_ofAmbientMap_preimage_of_closure_subset lower₁ upper₁ hwidth₁
          field hfield.continuousOn region hopen hclosure₁ hzeroFree) := by
  let lower (parameter : Icc (0 : ℝ) 1) (who : Fin n) :=
    (1 - (parameter : ℝ)) * lower₀ who + (parameter : ℝ) * lower₁ who
  let upper (parameter : Icc (0 : ℝ) 1) (who : Fin n) :=
    (1 - (parameter : ℝ)) * upper₀ who + (parameter : ℝ) * upper₁ who
  have hwidth (parameter : Icc (0 : ℝ) 1) (who : Fin n) :
      lower parameter who < upper parameter who := by
    have hpositive := rectangular_mix_pos parameter (sub_pos.mpr (hwidth₀ who))
      (sub_pos.mpr (hwidth₁ who))
    dsimp [lower, upper]
    nlinarith
  have hclosure (parameter : Icc (0 : ℝ) 1) : closure region ⊆
      {point | ∀ who, lower parameter who < point who ∧ point who < upper parameter who} := by
    intro point hpoint who
    have hfirst := hclosure₀ hpoint who
    have hsecond := hclosure₁ hpoint who
    have hlower := rectangular_mix_pos parameter (sub_pos.mpr hfirst.1)
      (sub_pos.mpr hsecond.1)
    have hupper := rectangular_mix_pos parameter (sub_pos.mpr hfirst.2)
      (sub_pos.mpr hsecond.2)
    dsimp [lower, upper]
    constructor <;> nlinarith
  let chart (parameter : Icc (0 : ℝ) 1) :=
    rectangularCubePoint (lower parameter) (upper parameter)
  have hchart : Continuous
      (fun pair : Icc (0 : ℝ) 1 × UnitCube (Fin n) => chart pair.1 pair.2) := by
    apply continuous_pi
    intro who
    dsimp [chart, rectangularCubePoint, rectangularPoint, lower, upper]
    fun_prop
  let family (parameter : Icc (0 : ℝ) 1) :=
    ofAmbientMap (lower parameter) (upper parameter) (hwidth parameter)
      field hfield.continuousOn
  have hcontinuous : IsContinuousBoxComplementarityFamily (Fin n) family := by
    intro who
    change Continuous
      (fun pair : Icc (0 : ℝ) 1 × UnitCube (Fin n) => -field (chart pair.1 pair.2) who)
    exact ((continuous_apply who).comp (hfield.comp hchart)).neg
  have hisolating (parameter : Icc (0 : ℝ) 1) :
      (family parameter).IsIsolating (chart parameter ⁻¹' region) :=
    isIsolating_ofAmbientMap_preimage_of_closure_subset _ _ (hwidth parameter)
      field hfield.continuousOn region hopen (hclosure parameter) hzeroFree
  have hfrontier (parameter : Icc (0 : ℝ) 1) (point : UnitCube (Fin n))
      (hsolution : (family parameter).IsSolution point) :
      chart parameter point ∉ frontier region := by
    intro hpoint
    have hzero := (isSolution_ofAmbientMap_iff_of_imageInterior _ _ (hwidth parameter)
      field hfield.continuousOn point
      (hclosure parameter (frontier_subset_closure hpoint))).mp hsolution
    exact hzeroFree _ hpoint hzero
  have hdegree := (isLocallyConstant_localDegree_preimage family hcontinuous chart hchart
    region hopen hisolating hfrontier).apply_eq_of_preconnectedSpace 0 1
  simpa [family, chart, lower, upper] using hdegree

/-- Positive rectangular chart independence for the same literal ambient field
and open source region. Continuity is needed only on the two closed rectangles.
Closure containment already implies boundedness of the source region. -/
theorem localDegree_ofAmbientMap_chart_independent
    (lower₀ upper₀ lower₁ upper₁ : Fin n → ℝ)
    (hwidth₀ : ∀ who, lower₀ who < upper₀ who)
    (hwidth₁ : ∀ who, lower₁ who < upper₁ who)
    (field : (Fin n → ℝ) → Fin n → ℝ)
    (hfield₀ : ContinuousOn field (Icc lower₀ upper₀))
    (hfield₁ : ContinuousOn field (Icc lower₁ upper₁))
    (region : Set (Fin n → ℝ)) (hopen : IsOpen region)
    (hclosure₀ : closure region ⊆
      {point | ∀ who, lower₀ who < point who ∧ point who < upper₀ who})
    (hclosure₁ : closure region ⊆
      {point | ∀ who, lower₁ who < point who ∧ point who < upper₁ who})
    (hzeroFree : ∀ point ∈ frontier region, field point ≠ 0) :
    (ofAmbientMap lower₀ upper₀ hwidth₀ field hfield₀).localDegree
        (rectangularCubePoint lower₀ upper₀ ⁻¹' region)
        (isIsolating_ofAmbientMap_preimage_of_closure_subset lower₀ upper₀ hwidth₀
          field hfield₀ region hopen hclosure₀ hzeroFree) =
      (ofAmbientMap lower₁ upper₁ hwidth₁ field hfield₁).localDegree
        (rectangularCubePoint lower₁ upper₁ ⁻¹' region)
        (isIsolating_ofAmbientMap_preimage_of_closure_subset lower₁ upper₁ hwidth₁
          field hfield₁ region hopen hclosure₁ hzeroFree) := by
  let source := Icc lower₀ upper₀ ∪ Icc lower₁ upper₁
  have hclosed : IsClosed source := isClosed_Icc.union isClosed_Icc
  have hsource : ContinuousOn field source :=
    (continuousOn_union_iff_of_isClosed isClosed_Icc isClosed_Icc).mpr ⟨hfield₀, hfield₁⟩
  let restricted : C(source, Fin n → ℝ) :=
    ⟨fun point => field point, hsource.domRestrict⟩
  obtain ⟨extended, hextended⟩ := ContinuousMap.exists_restrict_eq hclosed restricted
  have hequal : EqOn extended field source := by
    intro point hpoint
    exact congrArg (fun map : C(source, Fin n → ℝ) => map ⟨point, hpoint⟩) hextended
  have hproblem₀ : ofAmbientMap lower₀ upper₀ hwidth₀ field hfield₀ =
      ofAmbientMap lower₀ upper₀ hwidth₀ extended extended.continuous.continuousOn := by
    apply BoxComplementarityProblem.ext
    funext point who
    change -field (rectangularCubePoint lower₀ upper₀ point) who =
      -extended (rectangularCubePoint lower₀ upper₀ point) who
    rw [hequal (Or.inl (rectangularCubePoint_mem_Icc hwidth₀ point))]
  have hproblem₁ : ofAmbientMap lower₁ upper₁ hwidth₁ field hfield₁ =
      ofAmbientMap lower₁ upper₁ hwidth₁ extended extended.continuous.continuousOn := by
    apply BoxComplementarityProblem.ext
    funext point who
    change -field (rectangularCubePoint lower₁ upper₁ point) who =
      -extended (rectangularCubePoint lower₁ upper₁ point) who
    rw [hequal (Or.inr (rectangularCubePoint_mem_Icc hwidth₁ point))]
  have hzeroFreeExtended : ∀ point ∈ frontier region, extended point ≠ 0 := by
    intro point hpoint
    rw [hequal (Or.inl ⟨fun who => (hclosure₀ (frontier_subset_closure hpoint) who).1.le,
      fun who => (hclosure₀ (frontier_subset_closure hpoint) who).2.le⟩)]
    exact hzeroFree point hpoint
  have hdegree := localDegree_ofAmbientMap_chart_independent_of_continuous
    lower₀ upper₀ lower₁ upper₁ hwidth₀ hwidth₁ extended extended.continuous
    region hopen hclosure₀ hclosure₁ hzeroFreeExtended
  simpa only [hproblem₀, hproblem₁] using hdegree

end BoxComplementarityProblem

end Math
