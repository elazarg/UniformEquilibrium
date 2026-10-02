import MathUE.Analysis.CoordinateHessianExtrema
import Mathlib.Data.Fintype.EquivFin
import UniformEquilibrium.Quitting.Projective.RobustPotentialSingletonFaceDrift
import UniformEquilibrium.Quitting.Projective.SingletonBoxStandardQFaceExclusion

/-! # Actual quantitative negative least-Hessian-eigenvalue requirement

The corrected function is convex only on the actual singleton box. Its
face drift, not a full-root certificate, is passed to the standard-Q face
theorem. The spectral minimum and the positive curvature budget are outputs.
-/

noncomputable section

namespace GameTheory

open Set Math.LinearProgramming QuittingLCPClassification
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- The packet's exact A, in receiver-row, sole-quitter-column convention. -/
def quittingPositiveFaceCurvatureBudget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  Math.positiveFaceCurvatureBudget (quittingProjectiveLCPMatrix reward)

theorem quittingPositiveFaceCurvatureBudget_pos_of_standardQ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hQ : IsStandardQ (quittingProjectiveLCPMatrix reward)) :
    0 < quittingPositiveFaceCurvatureBudget reward := by
  obtain ⟨owner, hentry⟩ := exists_positive_entry_in_row_of_standardQ
    (quittingProjectiveLCPMatrix reward) ((isStandardQ_iff_isStandardQMatrix _).mp hQ)
    (Classical.arbitrary ι)
  exact Math.positiveFaceCurvatureBudget_pos_of_positive_entry
    (quittingProjectiveLCPMatrix reward) (fun who => by simp [quittingProjectiveLCPMatrix])
    (Classical.arbitrary ι) owner hentry

theorem quittingPositiveFaceCurvatureBudget_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    quittingPositiveFaceCurvatureBudget reward ≤
      ((Fintype.card ι - 1 : ℕ) : ℝ) * bound ^ 2 := by
  have hbound : 0 ≤ bound := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal (Classical.arbitrary ι)) (Classical.arbitrary ι))
  apply Math.positiveFaceCurvatureBudget_le _ bound hbound
  intro receiver owner
  have hsolo := (le_abs_self _).trans
    (hreward (quittingSingletonTerminal owner) receiver)
  have hown := neg_le_of_abs_le (hreward (quittingSingletonTerminal receiver) receiver)
  change quittingSoloReward reward owner receiver ≤ bound at hsolo
  change -bound ≤ quittingSoloReward reward receiver receiver at hown
  change quittingSoloReward reward owner receiver -
    quittingSoloReward reward receiver receiver ≤ 2 * bound
  linarith

/-- Theorem 3 equation (5), with textbook Q for the actual singleton matrix.
Twice continuous differentiability is required only on an open neighborhood of the closed box.
The least eigenvalue and its full-box minimum are literal, attained, and
spectral: the minimizing value is an eigenvalue of the actual Hessian. -/
theorem quittingRobustPotential_negativeHessianEigenvalue_of_standardQ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound tolerance : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (htolerance0 : 0 < tolerance) (htolerance1 : tolerance ≤ 1 / 4)
    (hQ : IsStandardQ (quittingProjectiveLCPMatrix reward))
    (potential : Payoff ι → ℝ) (domain : Set (Payoff ι))
    (hopen : IsOpen domain) (hbox : quittingSingletonBox reward bound ⊆ domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain)
    (hpotential :
      (quittingFloorFreeRobustChargedRelation reward tolerance (bound + 2)).IsPotential
        (fun state => potential state.1)) :
    (0 < quittingPositiveFaceCurvatureBudget reward) ∧
    (Math.coordinateMinimumHessianEigenvalue potential (quittingSingletonBox reward bound) ≤
      -((2 * bound + 1) / (2 * bound + 1 - tolerance)) /
        quittingPositiveFaceCurvatureBudget reward) ∧
    (0 < bound →
      Math.coordinateMinimumHessianEigenvalue potential (quittingSingletonBox reward bound) ≤
        -((2 * bound + 1) / (2 * bound + 1 - tolerance)) /
          (((Fintype.card ι - 1 : ℕ) : ℝ) * bound ^ 2)) ∧
    ∃ point ∈ quittingSingletonBox reward bound,
      IsMinOn (Math.coordinateLeastHessianEigenvalue potential)
        (quittingSingletonBox reward bound) point ∧
      Module.End.HasEigenvalue (Math.coordinateHessian potential point).toLinearMap
        (Math.coordinateLeastHessianEigenvalue potential point) ∧
      Math.coordinateLeastHessianEigenvalue potential point ≤
        -((2 * bound + 1) / (2 * bound + 1 - tolerance)) /
          quittingPositiveFaceCurvatureBudget reward := by
  classical
  let lower := fun who => quittingSoloReward reward who who
  let matrix := quittingProjectiveLCPMatrix reward
  let budget := quittingPositiveFaceCurvatureBudget reward
  let gain := (2 * bound + 1) / (2 * bound + 1 - tolerance)
  have hbound : 0 ≤ bound := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal (Classical.arbitrary ι)) (Classical.arbitrary ι))
  have hgain : 0 < gain := div_pos (by linarith) (by linarith)
  have hbudget : 0 < budget := quittingPositiveFaceCurvatureBudget_pos_of_standardQ reward hQ
  have hnonempty : (quittingSingletonBox reward bound).Nonempty := by
    refine ⟨lower, le_rfl, ?_⟩
    intro who
    have h := (le_abs_self _).trans (hreward (quittingSingletonTerminal who) who)
    change quittingSoloReward reward who who ≤ bound at h
    exact h.trans (by linarith)
  obtain ⟨point, hpoint, hmin, hvalue, heigenvalue, hfloor⟩ :=
    Math.exists_coordinateMinimumHessianEigenvalue potential (quittingSingletonBox reward bound)
      domain isCompact_Icc hnonempty hopen hbox hsmooth
  let minimum := Math.coordinateLeastHessianEigenvalue potential point
  let correction := max 0 (-minimum)
  have hcorrection : 0 ≤ correction := le_max_left _ _
  have hfloor' : ∀ input ∈ quittingSingletonBox reward bound,
      ∀ direction : EuclideanSpace ℝ ι,
      -(correction * ‖direction‖ ^ 2) ≤
        fderiv ℝ (fderiv ℝ (potential ∘ EuclideanSpace.equiv ι ℝ))
          ((EuclideanSpace.equiv ι ℝ).symm input) direction direction := by
    intro input hinput direction
    have hminimum : -correction ≤ minimum := by
      have h := le_max_right 0 (-minimum)
      change -minimum ≤ correction at h
      linarith
    have hscaled : -(correction * ‖direction‖ ^ 2) ≤ minimum * ‖direction‖ ^ 2 := by
      simpa only [neg_mul] using
        mul_le_mul_of_nonneg_right hminimum (sq_nonneg ‖direction‖)
    exact hscaled.trans (hfloor input hinput direction)
  let corrected := fun input =>
    potential input + Math.coordinateShiftedQuadratic lower correction input
  have hconvex : ConvexOn ℝ (quittingSingletonBox reward bound) corrected :=
    Math.convexOn_add_coordinateShiftedQuadratic_of_hessian_floor potential
      (quittingSingletonBox reward bound) domain lower correction (convex_Icc _ _)
      hopen hbox hsmooth hfloor'
  have hdiff : ∀ input ∈ quittingSingletonBox reward bound, DifferentiableAt ℝ potential input :=
    fun input hinput => (hsmooth.differentiableOn (by norm_num) input
      (hbox hinput)).differentiableAt (hopen.mem_nhds (hbox hinput))
  have hquadratic := Math.coordinateShiftedQuadratic_contDiff lower correction 1
  have hcorrectedDiff : ∀ input ∈ quittingSingletonBox reward bound,
      DifferentiableAt ℝ corrected input :=
    fun input hinput => (hdiff input hinput).add (hquadratic.differentiable one_ne_zero input)
  have hforced : gain ≤ correction * budget := by
    by_contra hnot
    have hstrict : correction * budget < gain := lt_of_not_ge hnot
    have hdrift : ∀ input ∈ quittingSingletonBox reward bound, ∀ owner,
        input owner = quittingSoloReward reward owner owner →
        0 < fderiv ℝ corrected input (input - quittingSoloReward reward owner) := by
      intro input hinput owner howner
      have hactual := (quittingRobustPotential_singletonFace_fderiv_bounds reward hreward
        htolerance0 htolerance1 potential hpotential input owner
        (fun who => ⟨hinput.1 who, hinput.2 who⟩) howner (hdiff input hinput)).2.2
      let translated := input - lower
      have htranslated : ∀ who, 0 ≤ translated who :=
        fun who => sub_nonneg.mpr (hinput.1 who)
      have htranslatedOwner : translated owner = 0 := by simp [translated, lower, howner]
      have hquadraticBound := Math.sum_face_quadratic_ge_neg_budget matrix translated
        htranslated owner htranslatedOwner
      have hsum : (∑ receiver, (input receiver - lower receiver) *
          (input - quittingSoloReward reward owner) receiver) =
          ∑ receiver, translated receiver * (translated receiver - matrix receiver owner) := by
        apply Finset.sum_congr rfl
        intro receiver _
        change (input receiver - quittingSoloReward reward receiver receiver) *
            (input receiver - quittingSoloReward reward owner receiver) =
          (input receiver - quittingSoloReward reward receiver receiver) *
            ((input receiver - quittingSoloReward reward receiver receiver) -
              (quittingSoloReward reward owner receiver -
                quittingSoloReward reward receiver receiver))
        ring
      change -budget ≤ _ at hquadraticBound
      have hderivative : fderiv ℝ corrected input (input - quittingSoloReward reward owner) =
          fderiv ℝ potential input (input - quittingSoloReward reward owner) +
            correction * ∑ receiver,
              translated receiver * (translated receiver - matrix receiver owner) := by
        rw [fderiv_fun_add (hdiff input hinput) (hquadratic.differentiable one_ne_zero input)]
        simp only [add_apply,
          Math.coordinateShiftedQuadratic_fderiv_apply, hsum]
      rw [hderivative]
      have hscaled := mul_le_mul_of_nonneg_left hquadraticBound hcorrection
      change gain ≤ _ at hactual
      linarith
    exact not_quasiconvex_singletonBox_of_standardQ_positive_face_drift
      reward hreward hQ corrected hcorrectedDiff hdrift hconvex.quasiconvexOn
  have hnegative : minimum < 0 := by
    by_contra hnot
    have hnonnegative : 0 ≤ minimum := le_of_not_gt hnot
    have hzero : correction = 0 := max_eq_left (neg_nonpos.mpr hnonnegative)
    rw [hzero, zero_mul] at hforced
    exact (not_le_of_gt hgain) hforced
  have hcorrectionEq : correction = -minimum := max_eq_right (neg_nonneg.mpr hnegative.le)
  have hminimumBound : minimum ≤ -gain / budget := by
    rw [hcorrectionEq] at hforced
    have hdiv := (div_le_iff₀ hbudget).mpr hforced
    rw [neg_div]
    linarith
  have hboxBound : Math.coordinateMinimumHessianEigenvalue potential
      (quittingSingletonBox reward bound) ≤ -gain / budget := by
    rw [hvalue]
    exact hminimumBound
  refine ⟨hbudget, hboxBound, ?_, point, hpoint, hmin, heigenvalue, hminimumBound⟩
  intro hpositiveBound
  have hupperBudget := quittingPositiveFaceCurvatureBudget_le reward hreward
  have hcard : (0 : ℝ) < ((Fintype.card ι - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (Fintype.one_lt_card (α := ι))
  have hdenominator : 0 < ((Fintype.card ι - 1 : ℕ) : ℝ) * bound ^ 2 :=
    mul_pos hcard (sq_pos_of_pos hpositiveBound)
  have hratio : gain / (((Fintype.card ι - 1 : ℕ) : ℝ) * bound ^ 2) ≤ gain / budget :=
    (div_le_div_iff₀ hdenominator hbudget).mpr
      (mul_le_mul_of_nonneg_left hupperBudget hgain.le)
  exact hboxBound.trans (by simpa only [neg_div] using neg_le_neg hratio)

/-- The same-game Fin4 facade obtains its actual textbook Q from bare no-UE;
it does not add a matrix, eigenvector, or convexification premise. -/
theorem quittingRobustPotential_finFour_negativeHessianEigenvalue
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound tolerance : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (htolerance0 : 0 < tolerance) (htolerance1 : tolerance ≤ 1 / 4)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (potential : Payoff (Fin 4) → ℝ) (domain : Set (Payoff (Fin 4)))
    (hopen : IsOpen domain) (hbox : quittingSingletonBox reward bound ⊆ domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain)
    (hpotential :
      (quittingFloorFreeRobustChargedRelation reward tolerance (bound + 2)).IsPotential
        (fun state => potential state.1)) :
    (0 < quittingPositiveFaceCurvatureBudget reward) ∧
    (Math.coordinateMinimumHessianEigenvalue potential (quittingSingletonBox reward bound) ≤
      -((2 * bound + 1) / (2 * bound + 1 - tolerance)) /
        quittingPositiveFaceCurvatureBudget reward) ∧
    (0 < bound →
      Math.coordinateMinimumHessianEigenvalue potential (quittingSingletonBox reward bound) ≤
        -((2 * bound + 1) / (2 * bound + 1 - tolerance)) / (3 * bound ^ 2)) ∧
    ∃ point ∈ quittingSingletonBox reward bound,
      IsMinOn (Math.coordinateLeastHessianEigenvalue potential)
        (quittingSingletonBox reward bound) point ∧
      Module.End.HasEigenvalue (Math.coordinateHessian potential point).toLinearMap
        (Math.coordinateLeastHessianEigenvalue potential point) ∧
      Math.coordinateLeastHessianEigenvalue potential point ≤
        -((2 * bound + 1) / (2 * bound + 1 - tolerance)) /
          quittingPositiveFaceCurvatureBudget reward := by
  simpa only [Fintype.card_fin, Nat.reduceSub, Nat.cast_ofNat] using
    quittingRobustPotential_negativeHessianEigenvalue_of_standardQ reward hreward
      htolerance0 htolerance1
      (isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff reward hnot)
      potential domain hopen hbox hsmooth hpotential

end GameTheory
