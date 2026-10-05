import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialQuadraticExclusion
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialMultiAffineExclusion

/-! # Zero drift and arbitrary positive full-root drift coefficients

The same full-root quantifiers are retained. A positive coefficient is
reduced to the existing unit-charge predicate by the literal function `P/κ`.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def IsQuittingFullExactRootPotentialWithCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound coefficient : ℝ) (potential : Payoff ι → ℝ) : Prop :=
  ∀ tail, (∀ who, |tail who| ≤ bound) → ∀ root,
    IsεQuittingRootNash reward tail 0 root →
      potential (quittingRootSuccessorPayoff reward tail root) +
        coefficient * quittingRootAbsorptionMass root ≤ potential tail

theorem constant_isQuittingFullExactRootPotentialWithCharge_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound constant : ℝ) :
    IsQuittingFullExactRootPotentialWithCharge reward bound 0 (fun _ => constant) := by
  intro tail _ root _
  simp

theorem isQuittingFullExactRootPotentialWithCharge_iff_div
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) {coefficient : ℝ} (hcoefficient : 0 < coefficient)
    (potential : Payoff ι → ℝ) :
    IsQuittingFullExactRootPotentialWithCharge reward bound coefficient potential ↔
      IsQuittingFullExactRootPotential reward bound
        (fun point => potential point / coefficient) := by
  constructor
  · intro hpotential tail htail root hnash
    have h := (div_le_div_iff_of_pos_right hcoefficient).mpr
      (hpotential tail htail root hnash)
    simpa only [add_div, mul_div_cancel_left₀ _ hcoefficient.ne'] using h
  · intro hpotential tail htail root hnash
    have h := (div_le_div_iff_of_pos_right hcoefficient).mp
      (show (potential (quittingRootSuccessorPayoff reward tail root) +
        coefficient * quittingRootAbsorptionMass root) / coefficient ≤
          potential tail / coefficient by
        simpa only [add_div, mul_div_cancel_left₀ _ hcoefficient.ne'] using
          hpotential tail htail root hnash)
    exact h

theorem not_fullExactRootPotentialWithCharge_coordinateAffine [Nontrivial ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ quittingSoloReward reward who who)
    (potential : Payoff ι → ℝ) (haffine : Math.IsCoordinateAffine potential)
    (hcontinuous : ContinuousOn potential (Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3)))
    (hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => 3), DifferentiableAt ℝ potential point)
    {coefficient : ℝ} (hcoefficient : 0 < coefficient) :
    ¬ IsQuittingFullExactRootPotentialWithCharge reward 3 coefficient potential := by
  intro hpotential
  have haffineDiv : Math.IsCoordinateAffine (fun point => potential point / coefficient) := by
    intro point coordinate
    obtain ⟨offset, slope, hline⟩ := haffine point coordinate
    refine ⟨offset / coefficient, slope / coefficient, ?_⟩
    intro value
    change potential (Function.update point coordinate value) / coefficient =
      offset / coefficient + slope / coefficient * value
    rw [hline]
    ring
  have hdiffDiv : ∀ point ∈ Set.Icc
      (fun who => quittingSoloReward reward who who) (fun _ => 3),
      DifferentiableAt ℝ (fun input => potential input / coefficient) point := by
    intro point hpoint
    simpa only [div_eq_mul_inv] using (hdiff point hpoint).mul_const coefficient⁻¹
  exact not_isQuittingFullExactRootPotential_coordinateAffine hreward hsingleton
    (fun point => potential point / coefficient) haffineDiv
    (hcontinuous.div_const coefficient) hdiffDiv
    ((isQuittingFullExactRootPotentialWithCharge_iff_div reward 3 hcoefficient potential).mp
      hpotential)

omit [Fintype ι] [DecidableEq ι] in
theorem not_fullExactRootPotentialWithCharge_totalDegree_le_two
    {dimension : ℕ} [Nonempty (Fin dimension)]
    {reward : {S : Finset (Fin dimension) // S.Nonempty} → Payoff (Fin dimension)}
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ quittingSoloReward reward who who)
    (polynomial : MvPolynomial (Fin dimension) ℝ) (hdegree : polynomial.totalDegree ≤ 2)
    {coefficient : ℝ} (hcoefficient : 0 < coefficient) :
    ¬ IsQuittingFullExactRootPotentialWithCharge reward 3 coefficient
      (fun point => MvPolynomial.eval point polynomial) := by
  intro hpotential
  have hunit := (isQuittingFullExactRootPotentialWithCharge_iff_div
    reward 3 hcoefficient (fun point => MvPolynomial.eval point polynomial)).mp hpotential
  have heval : (fun point => MvPolynomial.eval point polynomial / coefficient) =
      (fun point => MvPolynomial.eval point (coefficient⁻¹ • polynomial)) := by
    funext point
    rw [MvPolynomial.smul_eval]
    simp only [div_eq_mul_inv, mul_comm]
  rw [heval] at hunit
  exact not_isQuittingFullExactRootPotential_totalDegree_le_two hreward hsingleton
    (coefficient⁻¹ • polynomial) ((MvPolynomial.totalDegree_smul_le _ _).trans hdegree) hunit

omit [Fintype ι] [DecidableEq ι] in
theorem not_fullExactRootPotentialWithCharge_multiAffine
    {dimension : ℕ} [Nontrivial (Fin dimension)]
    {reward : {S : Finset (Fin dimension) // S.Nonempty} → Payoff (Fin dimension)}
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ quittingSoloReward reward who who)
    (polynomial : MvPolynomial (Fin dimension) ℝ)
    (haffine : Math.IsMultiAffineMvPolynomial polynomial)
    {coefficient : ℝ} (hcoefficient : 0 < coefficient) :
    ¬ IsQuittingFullExactRootPotentialWithCharge reward 3 coefficient
      (fun point => MvPolynomial.eval point polynomial) := by
  have hsmooth := Math.contDiff_eval_mvPolynomial polynomial 1
  exact not_fullExactRootPotentialWithCharge_coordinateAffine hreward hsingleton _
    (Math.isCoordinateAffine_eval_mvPolynomial polynomial haffine)
    hsmooth.continuous.continuousOn (fun point _ => hsmooth.differentiable_one point)
    hcoefficient

end GameTheory
