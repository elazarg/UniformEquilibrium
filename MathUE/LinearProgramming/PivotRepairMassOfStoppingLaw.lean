import MathUE.LinearProgramming.PivotRepairStoppingLaw

/-! # Feasible repair coordinates extracted from a complete stopping law -/

noncomputable section

namespace Math.LinearProgramming

open _root_.Math.Probability
open scoped BigOperators

/-- Actual head, late-finite, and Never masses, with a separately specified
first-atom coordinate. -/
def pivotRepairMassOfStoppingLaw (law : PMF (Option ℕ)) (deadline : ℕ)
    (firstAtom : ℝ) : PivotRepairMass deadline
  | .inl time => (law (some time.val)).toReal
  | .inr .late => stoppingLawLateFiniteMass law (deadline - 1)
  | .inr .never => (law none).toReal
  | .inr .firstAtom => firstAtom

theorem isPivotRepairMassFeasible_ofStoppingLaw (law : PMF (Option ℕ))
    {deadline : ℕ} (hdeadline : 0 < deadline) (firstAtom : ℝ)
    (hnonneg : 0 ≤ firstAtom)
    (hle : firstAtom ≤ stoppingLawLateFiniteMass law (deadline - 1)) :
    IsPivotRepairMassFeasible (pivotRepairMassOfStoppingLaw law deadline firstAtom) := by
  refine ⟨fun _ ↦ ENNReal.toReal_nonneg, pmfFiniteComplementMass_nonneg _ _,
    ENNReal.toReal_nonneg, ?_, hnonneg, hle⟩
  change (∑ time : Fin deadline, (law (some time.val)).toReal) +
    stoppingLawLateFiniteMass law (deadline - 1) + (law none).toReal = 1
  rw [stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead]
  have hhead : stoppingLawFiniteHeadMass law (deadline - 1) =
      ∑ time : Fin deadline, (law (some time.val)).toReal := by
    unfold stoppingLawFiniteHeadMass
    rw [show deadline - 1 + 1 = deadline by omega, Finset.sum_range]
  rw [hhead]
  ring

/-- Reconstructing the extracted coordinates preserves every head atom. -/
theorem pivotRepairProvisionalStoppingLaw_ofStoppingLaw_head
    (law : PMF (Option ℕ)) (deadline : ℕ) (firstAtom : ℝ)
    (hfeasible : IsPivotRepairMassFeasible (pivotRepairMassOfStoppingLaw law deadline firstAtom))
    {time : ℕ} (htime : time < deadline) :
    pivotRepairProvisionalStoppingLaw
        (pivotRepairMassOfStoppingLaw law deadline firstAtom) hfeasible (some time) =
      law (some time) := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  exact pivotRepairProvisionalStoppingLaw_head_toReal _ hfeasible ⟨time, htime⟩

/-- Reconstructing the extracted coordinates preserves the literal Never atom. -/
theorem pivotRepairProvisionalStoppingLaw_ofStoppingLaw_none
    (law : PMF (Option ℕ)) (deadline : ℕ) (firstAtom : ℝ)
    (hfeasible : IsPivotRepairMassFeasible (pivotRepairMassOfStoppingLaw law deadline firstAtom)) :
    pivotRepairProvisionalStoppingLaw
        (pivotRepairMassOfStoppingLaw law deadline firstAtom) hfeasible none = law none := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  exact pivotRepairProvisionalStoppingLaw_none_toReal _ hfeasible

/-- The geometric law constructed from extracted finite coordinates is
literally the same complete PMF as geometric replacement of the source. -/
theorem geometricPivotStoppingLaw_ofStoppingLaw_eq
    (law : PMF (Option ℕ)) {deadline : ℕ} (hdeadline : 0 < deadline) (firstAtom : ℝ)
    (hfeasible : IsPivotRepairMassFeasible (pivotRepairMassOfStoppingLaw law deadline firstAtom))
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    geometricPivotStoppingLaw
        (pivotRepairProvisionalStoppingLaw
          (pivotRepairMassOfStoppingLaw law deadline firstAtom) hfeasible)
        deadline hazard hpositive hle =
      geometricPivotStoppingLaw law deadline hazard hpositive hle := by
  apply PMF.ext
  intro choice
  cases choice with
  | none =>
      simp only [geometricPivotStoppingLaw_none]
      exact pivotRepairProvisionalStoppingLaw_ofStoppingLaw_none law deadline firstAtom hfeasible
  | some time =>
      by_cases htime : time < deadline
      · rw [geometricPivotStoppingLaw_some_of_lt _ _ _ _ _ htime,
          geometricPivotStoppingLaw_some_of_lt _ _ _ _ _ htime]
        exact pivotRepairProvisionalStoppingLaw_ofStoppingLaw_head
          law deadline firstAtom hfeasible htime
      · obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le (show deadline ≤ time by omega)
        apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
        rw [geometricPivotStoppingLaw_add_apply_toReal _ hdeadline,
          geometricPivotStoppingLaw_add_apply_toReal _ hdeadline,
          pivotRepairProvisionalStoppingLaw_lateFiniteMass hdeadline]
        rfl

end Math.LinearProgramming
