import MathUE.Interval.RationalPolynomialL1
import MathUE.Polynomial.MvPolynomialQuadraticReflection
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialReflection

/-! # Full exact-root exclusion of every polynomial of degree at most two

Total degree is measured after coefficient cancellation in `MvPolynomial`.
No convexity, definiteness, or interior-minimum hypothesis is imposed.
-/

noncomputable section

namespace GameTheory

open Set

variable {dimension : ℕ} [Nonempty (Fin dimension)]

/-- Every real polynomial of total degree at most two is excluded from the
full-root relation, irrespective of the signs or degeneracy of its Hessian. -/
theorem not_isQuittingFullExactRootPotential_totalDegree_le_two
    {reward : {S : Finset (Fin dimension) // S.Nonempty} → Payoff (Fin dimension)}
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ quittingSoloReward reward who who)
    (polynomial : MvPolynomial (Fin dimension) ℝ) (hdegree : polynomial.totalDegree ≤ 2) :
    ¬ IsQuittingFullExactRootPotential reward 3
      (fun point => MvPolynomial.eval point polynomial) := by
  intro hpotential
  have hsmooth := Math.contDiff_eval_mvPolynomial polynomial 1
  have hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => 3), DifferentiableAt ℝ
        (fun input => MvPolynomial.eval input polynomial) point :=
    fun point _ => hsmooth.differentiable_one point
  obtain ⟨minimum, hminimum, hmin, _⟩ :=
    hpotential.exists_minimum_above_singleton hreward (by norm_num : (1 : ℝ) < 3)
      hsmooth.continuous.continuousOn hdiff
  obtain ⟨hgap, point, _, _, hnegative, hreflection, _⟩ :=
    hpotential.radialReversal hreward hsingleton hdiff minimum hminimum hmin
  have hnonneg := hmin hreflection
  have hidentity := Math.eval_mvPolynomial_reflection_sub_eq_twice_fderiv
    polynomial hdegree minimum point
  change MvPolynomial.eval minimum polynomial ≤
    MvPolynomial.eval (2 • point - minimum) polynomial at hnonneg
  linarith

/-- The identical exclusion for the repository's actual rational syntax
uses its normalized polynomial, so syntactic cancellations do not affect scope. -/
theorem not_isQuittingFullExactRootPotential_rational_totalDegree_le_two
    {reward : {S : Finset (Fin dimension) // S.Nonempty} → Payoff (Fin dimension)}
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ quittingSoloReward reward who who)
    (expression : Math.Interval.RationalPolynomial dimension)
    (hdegree : expression.toMvPolynomial.totalDegree ≤ 2) :
    ¬ IsQuittingFullExactRootPotential reward 3
      (fun point => Math.Interval.RationalPolynomial.evalReal point expression) := by
  let polynomial := MvPolynomial.map (Rat.castHom ℝ) expression.toMvPolynomial
  have hrealDegree : polynomial.totalDegree ≤ 2 := by
    apply le_trans ?_ hdegree
    change polynomial.support.sup (fun exponent => exponent.sum (fun _ power => power)) ≤ _
    apply Finset.sup_le
    intro exponent hexponent
    exact MvPolynomial.le_totalDegree
      (MvPolynomial.support_map_subset (Rat.castHom ℝ) expression.toMvPolynomial hexponent)
  have hevaluation : (fun point => Math.Interval.RationalPolynomial.evalReal point expression) =
      (fun point => MvPolynomial.eval point polynomial) := by
    funext point
    rw [Math.Interval.RationalPolynomial.evalReal_eq_eval₂_toMvPolynomial,
      MvPolynomial.eval₂_eq_eval_map]
  rw [hevaluation]
  exact not_isQuittingFullExactRootPotential_totalDegree_le_two
    hreward hsingleton polynomial hrealDegree

end GameTheory
