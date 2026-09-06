import MathUE.ProbabilityMassFunction.GeometricPivotStoppingLaw
import MathUE.ProbabilityMassFunction.ExactLateFiniteCensor

/-! # Exact remaining mass after retaining a finite geometric tail -/

noncomputable section

namespace Math.Probability

open Filter
open scoped Topology

theorem stoppingLawLateFiniteMass_add_eq_sub_Ico
    (law : PMF (Option ℕ)) {deadline : ℕ} (hdeadline : 0 < deadline) (retained : ℕ) :
    stoppingLawLateFiniteMass law (deadline + retained - 1) =
      stoppingLawLateFiniteMass law (deadline - 1) -
        ∑ time ∈ Finset.Ico deadline (deadline + retained), (law (some time)).toReal := by
  rw [stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead,
    stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead]
  unfold stoppingLawFiniteHeadMass
  rw [show deadline + retained - 1 + 1 = deadline + retained by omega,
    show deadline - 1 + 1 = deadline by omega]
  have hsum := Finset.sum_range_add_sum_Ico
    (fun time ↦ (law (some time)).toReal) (show deadline ≤ deadline + retained by omega)
  linarith

/-- Retaining exactly the first displayed number of geometric late atoms
leaves the geometric power tail as the precise discarded finite mass. -/
theorem geometricPivotStoppingLaw_lateFiniteMass_after
    (source : PMF (Option ℕ)) {deadline : ℕ} (hdeadline : 0 < deadline)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) (retained : ℕ) :
    stoppingLawLateFiniteMass (geometricPivotStoppingLaw source deadline hazard hpositive hle)
        (deadline + retained - 1) =
      stoppingLawLateFiniteMass source (deadline - 1) * (1 - hazard) ^ retained := by
  rw [stoppingLawLateFiniteMass_add_eq_sub_Ico _ hdeadline,
    geometricPivotStoppingLaw_lateFiniteMass source hdeadline,
    geometricPivotStoppingLaw_sum_Ico_add source hdeadline]
  ring

/-- The censored geometric law retains the source Never mass and adds
exactly the unretained geometric finite tail, including zero retained atoms. -/
theorem censor_geometricPivotStoppingLaw_none_toReal
    (source : PMF (Option ℕ)) {deadline : ℕ} (hdeadline : 0 < deadline)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) (retained : ℕ) :
    (censorLateFiniteStoppingLaw (geometricPivotStoppingLaw source deadline hazard hpositive hle)
      (deadline + retained - 1) none).toReal =
      (source none).toReal +
        stoppingLawLateFiniteMass source (deadline - 1) * (1 - hazard) ^ retained := by
  rw [censorLateFiniteStoppingLaw_none_toReal_eq, geometricPivotStoppingLaw_none,
    geometricPivotStoppingLaw_lateFiniteMass_after source hdeadline]

theorem geometricPivotStoppingLaw_lateFiniteMass_after_tendsto
    (source : PMF (Option ℕ)) {deadline : ℕ} (hdeadline : 0 < deadline)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    Tendsto (fun retained ↦
      stoppingLawLateFiniteMass (geometricPivotStoppingLaw source deadline hazard hpositive hle)
        (deadline + retained - 1)) atTop (𝓝 0) := by
  simp_rw [geometricPivotStoppingLaw_lateFiniteMass_after source hdeadline]
  have hpow : Tendsto (fun retained : ℕ ↦ (1 - hazard) ^ retained) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  simpa using hpow.const_mul (stoppingLawLateFiniteMass source (deadline - 1))

end Math.Probability
