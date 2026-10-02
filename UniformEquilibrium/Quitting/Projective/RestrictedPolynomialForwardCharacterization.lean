import MathUE.Interval.RationalPolynomialRegularity
import UniformEquilibrium.Quitting.Classification.AbnormalPlayers
import UniformEquilibrium.Quitting.Projective.PolynomialForwardCertificateCharacterization
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialQuadraticExclusion
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialMultiAffineExclusion
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialThirdDerivative

/-! # The same unit-box polynomial has the packet's degree and minimum restrictions

Singleton signs produce actual punishment normality. The existing obstruction
characterization then produces one rational tolerance and one polynomial on
box three. All added restrictions concern that same witness. No signed-table
normalization or positive scaling is asserted here.
-/

noncomputable section

namespace GameTheory

open Set
open Math.Interval Math.Interval.RationalPolynomial

private theorem rationalPotential_iff_of_box_eq
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (tolerance : ℝ) (expression : RationalPolynomial 4)
    {first second : ℝ} (hbox : first = second) :
    (quittingFloorFreeRobustChargedRelation reward tolerance first).IsPotential
        (fun state => evalReal state.1 expression) ↔
      (quittingFloorFreeRobustChargedRelation reward tolerance second).IsPotential
        (fun state => evalReal state.1 expression) := by
  subst second
  rfl

/-- Output-only geometric restrictions on one actual rational polynomial:
every global minimum has adaptive radial reversal and the quantitative
directional third derivative along ONE internally produced boundary-minimum
direction. Upper-face minima, its boxed reflection and the full segment are retained. -/
def QuittingRationalPolynomialAdaptiveMinimumConditions
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (expression : RationalPolynomial 4) : Prop :=
  let potential := fun point => evalReal point expression
  ∀ minimum : Payoff (Fin 4), (∀ who, |minimum who| ≤ 3) →
    IsMinOn potential (Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3)) minimum →
    let gap := Finset.univ.inf' Finset.univ_nonempty
      (fun who => minimum who - quittingSoloReward reward who who)
    0 < gap ∧ ∃ point time,
      point ∈ Math.lowerBoxBoundary (fun who => quittingSoloReward reward who who)
        (fun who => max (minimum who) 1) ∧
      IsMinOn potential (Math.lowerBoxBoundary (fun who => quittingSoloReward reward who who)
        (fun who => max (minimum who) 1)) point ∧
      time ∈ Set.Ioo (0 : ℝ) 2 ∧
      fderiv ℝ potential point (point - minimum) ≤ -gap / 2 ∧
      2 • point - minimum ∈ Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3) ∧
      3 * gap ≤ iteratedFDeriv ℝ 3 potential (minimum + time • (point - minimum))
        (fun _ => point - minimum) ∧
      (∀ rate ∈ Set.Icc (0 : ℝ) 2, minimum + rate • (point - minimum) ∈
        Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3))

/-- In the bounded nonnegative-singleton Fin4 class, the identical produced
polynomial has total degree at least three, is not multi-affine, and satisfies
both packet minimum conditions at every global minimum on the original box. -/
theorem quittingGame_noUniformPayoff_iff_noSureRoot_and_restricted_rationalPotential
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who)
    (hpositive : ∃ who, 0 < reward (quittingSingletonTerminal who) who) :
    (¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      ¬ HasQuittingPunishmentVectorNashRootWithSureQuitter reward ∧
        ∃ tolerance : ℚ, 0 < tolerance ∧ tolerance ≤ 1 / 4 ∧
          ∃ expression : RationalPolynomial 4,
            (quittingFloorFreeRobustChargedRelation reward (tolerance : ℝ)
              3).IsPotential (fun state => evalReal state.1 expression) ∧
            3 ≤ expression.toMvPolynomial.totalDegree ∧
            ¬ (∀ coordinate, expression.toMvPolynomial.degreeOf coordinate ≤ 1) ∧
            QuittingRationalPolynomialAdaptiveMinimumConditions reward expression := by
  have hnormal : ∀ player, IsQuittingNormalPlayer reward player :=
    fun player => isQuittingNormalPlayer_of_singleton_nonneg reward player (hsingleton player)
  have hsolo : ∀ who, 0 ≤ quittingSoloReward reward who who := hsingleton
  have hcharacterization :=
    quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential
      reward 1 hreward hnormal hpositive
  constructor
  · intro hnoUniform
    obtain ⟨hnoSureRoot, tolerance, htolerance, htoleranceMax, expression, hpotential⟩ :=
      hcharacterization.mp hnoUniform
    have hrobust : (quittingFloorFreeRobustChargedRelation reward (tolerance : ℝ)
        3).IsPotential (fun state => evalReal state.1 expression) := by
      exact (rationalPotential_iff_of_box_eq reward (tolerance : ℝ) expression
        (by norm_num : (1 : ℝ) + 2 = 3)).mp hpotential
    have hexact : IsQuittingFullExactRootPotential reward 3
        (fun point => evalReal point expression) :=
      isQuittingFullExactRootPotential_of_robustPotential reward
        (by exact_mod_cast htolerance.le)
        (fun terminal player => (hreward terminal player).trans (by norm_num))
        (fun point => evalReal point expression) hrobust
    have hdegree : 3 ≤ expression.toMvPolynomial.totalDegree := by
      by_contra hnot
      have hsmall : expression.toMvPolynomial.totalDegree ≤ 2 := by omega
      exact not_isQuittingFullExactRootPotential_rational_totalDegree_le_two
        hreward hsolo expression hsmall hexact
    have hnotAffine : ¬ (∀ coordinate, expression.toMvPolynomial.degreeOf coordinate ≤ 1) := by
      intro haffine
      exact not_isQuittingFullExactRootPotential_rational_multiAffine
        hreward hsolo expression haffine hexact
    have hminimumConditions : QuittingRationalPolynomialAdaptiveMinimumConditions
        reward expression := by
      intro minimum hminimum hmin
      exact hexact.directionalThirdDerivative hreward hsolo Set.univ isOpen_univ
        (by intro point _; trivial) (contDiff_evalReal expression 3).contDiffOn
        minimum hminimum hmin
    exact ⟨hnoSureRoot, tolerance, htolerance, htoleranceMax, expression,
      hrobust, hdegree, hnotAffine, hminimumConditions⟩
  · rintro ⟨hnoSureRoot, tolerance, htolerance, htoleranceMax, expression,
      hrobust, _, _, _⟩
    apply hcharacterization.mpr
    refine ⟨hnoSureRoot, tolerance, htolerance, htoleranceMax, expression, ?_⟩
    exact (rationalPotential_iff_of_box_eq reward (tolerance : ℝ) expression
      (by norm_num : (1 : ℝ) + 2 = 3)).mpr hrobust

/-- The exact polynomial-certificate restriction without its redundant
minimum-condition conjunct. The same table and positive rational tolerance remain. -/
theorem quittingGame_noUniformPayoff_iff_noSureRoot_and_higherDegree_nonMultiAffine
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who)
    (hpositive : ∃ who, 0 < reward (quittingSingletonTerminal who) who) :
    (¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      ¬ HasQuittingPunishmentVectorNashRootWithSureQuitter reward ∧
        ∃ tolerance : ℚ, 0 < tolerance ∧ tolerance ≤ 1 / 4 ∧
          ∃ expression : RationalPolynomial 4,
            (quittingFloorFreeRobustChargedRelation reward (tolerance : ℝ)
              3).IsPotential (fun state => evalReal state.1 expression) ∧
            3 ≤ expression.toMvPolynomial.totalDegree ∧
            ¬ (∀ coordinate, expression.toMvPolynomial.degreeOf coordinate ≤ 1) := by
  constructor
  · intro hnoUniform
    obtain ⟨hnoSureRoot, tolerance, htolerance, htoleranceMax, expression,
        hrobust, hdegree, hnotAffine, _⟩ :=
      (quittingGame_noUniformPayoff_iff_noSureRoot_and_restricted_rationalPotential
        reward hreward hsingleton hpositive).mp hnoUniform
    exact ⟨hnoSureRoot, tolerance, htolerance, htoleranceMax, expression,
      hrobust, hdegree, hnotAffine⟩
  · rintro ⟨hnoSureRoot, tolerance, htolerance, htoleranceMax, expression, hrobust, _, _⟩
    apply (quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential
      reward 1 hreward
      (fun player => isQuittingNormalPlayer_of_singleton_nonneg reward player (hsingleton player))
      hpositive).mpr
    refine ⟨hnoSureRoot, tolerance, htolerance, htoleranceMax, expression, ?_⟩
    exact (rationalPotential_iff_of_box_eq reward (tolerance : ℝ) expression
      (by norm_num : (1 : ℝ) + 2 = 3)).mpr hrobust

end GameTheory
