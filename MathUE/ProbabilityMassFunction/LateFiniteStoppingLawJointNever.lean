import MathUE.ProbabilityMassFunction.LateFiniteStoppingLawCensor
import MathUE.SurvivalProduct

/-! # Joint Never mass under late-finite censoring -/

noncomputable section

namespace Math.Probability

private theorem pmf_coordinate_toReal_le_one {Ω : Type}
    (law : PMF Ω) (outcome : Ω) :
    (law outcome).toReal ≤ 1 := by
  exact (ENNReal.toReal_le_toReal (PMF.apply_ne_top law outcome) (by norm_num)).mpr
    (PMF.coe_le_one law outcome) |>.trans_eq (by simp)

/-- Censoring all marginals changes their joint Never product by at most
twice the summed late-finite mass. -/
theorem prod_censorLateFiniteStoppingLaw_none_le
    {ι : Type} [Fintype ι]
    (laws : ι → PMF (Option ℕ)) (cutoff : ℕ) :
    (∏ who, (censorLateFiniteStoppingLaw (laws who) cutoff none).toReal) ≤
      (∏ who, (laws who none).toReal) +
        2 * ∑ who, stoppingLawLateFiniteMass (laws who) cutoff := by
  classical
  have hproduct := Math.abs_prod_sub_prod_le_sum_abs Finset.univ
    (fun who => (censorLateFiniteStoppingLaw (laws who) cutoff none).toReal)
    (fun who => (laws who none).toReal)
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun who _ => pmf_coordinate_toReal_le_one _ _)
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun who _ => pmf_coordinate_toReal_le_one _ _)
  have hcoordinate (who : ι) :
      |(censorLateFiniteStoppingLaw (laws who) cutoff none).toReal -
          (laws who none).toReal| ≤
        2 * stoppingLawLateFiniteMass (laws who) cutoff := by
    calc
      _ ≤ 2 * pmfGeneralTV
          (censorLateFiniteStoppingLaw (laws who) cutoff) (laws who) :=
        abs_pmf_apply_toReal_sub_le_two_mul_pmfGeneralTV _ _ none
      _ = 2 * pmfGeneralTV
          (laws who) (censorLateFiniteStoppingLaw (laws who) cutoff) := by
        rw [pmfGeneralTV_symm]
      _ ≤ 2 * stoppingLawLateFiniteMass (laws who) cutoff := by
        gcongr
        exact pmfGeneralTV_censorLateFiniteStoppingLaw_le _ _
  have hsum :
      (∑ who,
        |(censorLateFiniteStoppingLaw (laws who) cutoff none).toReal -
          (laws who none).toReal|) ≤
        2 * ∑ who, stoppingLawLateFiniteMass (laws who) cutoff := by
    calc
      _ ≤ ∑ who, 2 * stoppingLawLateFiniteMass (laws who) cutoff :=
        Finset.sum_le_sum fun who _ => hcoordinate who
      _ = _ := by rw [Finset.mul_sum]
  have habs := le_of_abs_le hproduct
  linarith

end Math.Probability
