import UniformEquilibrium.Diagnostics.Quitting.FinFourBoundedSinglePivotNormalization
import UniformEquilibrium.Quitting.Projective.RestrictedPolynomialForwardCharacterization

/-! # A decision-preserving bounded single-pivot polynomial obstruction

The polynomial characterization is called afresh after actual normalization
and common positive scaling. No rationality of the reward table is assumed.
The certificate and all restrictions concern one identical produced polynomial.
-/

noncomputable section

namespace GameTheory

open Math.Interval Math.Interval.RationalPolynomial

/-- The packet's bounded single-pivot right-hand side, retaining the same
polynomial's degree, multi-affinity, and every-global-minimum restrictions. -/
def IsQuittingBoundedSinglePivotPolynomialObstruction
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (pivot : Fin 4) (scale : ℝ) : Prop :=
  0 < scale ∧
  (∀ terminal who, |reward terminal who| ≤ 1) ∧
  (∀ who, reward (quittingSingletonTerminal who) who = if who = pivot then scale else 0) ∧
  ¬ HasQuittingPunishmentVectorNashRootWithSureQuitter reward ∧
  ∃ tolerance : ℚ, 0 < tolerance ∧ tolerance ≤ 1 / 4 ∧
    ∃ expression : RationalPolynomial 4,
      (quittingFloorFreeRobustChargedRelation reward (tolerance : ℝ)
        3).IsPotential (fun state => evalReal state.1 expression) ∧
      3 ≤ expression.toMvPolynomial.totalDegree ∧
      ¬ (∀ coordinate, expression.toMvPolynomial.degreeOf coordinate ≤ 1) ∧
      QuittingRationalPolynomialAdaptiveMinimumConditions reward expression

/-- Bare arbitrary-real-table no-UE data produce the literal scaled normalized
table, its positive reciprocal integer scale, and a fresh rational certificate. -/
theorem exists_finFourBoundedSinglePivotPolynomialObstruction_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ pivot : Fin 4, ∃ divisor : ℕ, 1 ≤ divisor ∧
      IsQuittingBoundedSinglePivotPolynomialObstruction
        (fun terminal who => (1 / (divisor : ℝ)) *
          quittingSinglePivotNormalizedReward reward pivot terminal who)
        pivot (1 / (divisor : ℝ)) := by
  obtain ⟨pivot, divisor, hdivisor, _, hbound, hsingleton, hscaledNot⟩ :=
    exists_finFourBoundedSinglePivotNormalization_of_no_uniformPayoff reward hnot
  let table := fun terminal who => (1 / (divisor : ℝ)) *
    quittingSinglePivotNormalizedReward reward pivot terminal who
  change ∀ who, table (quittingSingletonTerminal who) who =
    if who = pivot then 1 / (divisor : ℝ) else 0 at hsingleton
  have hdivisorPos : (0 : ℝ) < divisor := by exact_mod_cast (by omega : 0 < divisor)
  have hscale : 0 < 1 / (divisor : ℝ) := one_div_pos.mpr hdivisorPos
  have hnonnegative : ∀ who, 0 ≤ table (quittingSingletonTerminal who) who := by
    intro who
    rw [hsingleton who]
    split_ifs <;> positivity
  have hpositive : ∃ who, 0 < table (quittingSingletonTerminal who) who := by
    refine ⟨pivot, ?_⟩
    rw [hsingleton pivot, ite_eq_left rfl]
    exact hscale
  have hcertificate :=
    (quittingGame_noUniformPayoff_iff_noSureRoot_and_restricted_rationalPotential
      table hbound hnonnegative hpositive).mp hscaledNot
  exact ⟨pivot, divisor, hdivisor, hscale, hbound, hsingleton, hcertificate⟩

/-- Forgetting the additional table and polynomial restrictions returns the
actual no-UE conclusion by the original characterization's converse. -/
theorem IsQuittingBoundedSinglePivotPolynomialObstruction.no_uniformPayoff
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {pivot : Fin 4} {scale : ℝ}
    (h : IsQuittingBoundedSinglePivotPolynomialObstruction reward pivot scale) :
    ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨hscale, hbound, hsingleton, hcertificate⟩ := h
  have hnonnegative : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who := by
    intro who
    rw [hsingleton who]
    split_ifs <;> positivity
  have hpositive : ∃ who, 0 < reward (quittingSingletonTerminal who) who := by
    refine ⟨pivot, ?_⟩
    rw [hsingleton pivot, ite_eq_left rfl]
    exact hscale
  exact (quittingGame_noUniformPayoff_iff_noSureRoot_and_restricted_rationalPotential
    reward hbound hnonnegative hpositive).mpr hcertificate

/-- Existence of any real Fin4 counterexample is equivalent to the existence
of the bounded scaled-single-pivot obstruction. This constructs neither a
counterexample nor an equilibrium, and assumes no rational reward table. -/
theorem exists_finFour_no_uniformPayoff_iff_exists_boundedSinglePivotPolynomialObstruction :
    (∃ reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      ¬ ∃ payoff : Payoff (Fin 4),
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
    ∃ reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      ∃ pivot : Fin 4, ∃ scale : ℝ,
        IsQuittingBoundedSinglePivotPolynomialObstruction reward pivot scale := by
  constructor
  · rintro ⟨reward, hnot⟩
    obtain ⟨pivot, divisor, _, hcertificate⟩ :=
      exists_finFourBoundedSinglePivotPolynomialObstruction_of_no_uniformPayoff reward hnot
    exact ⟨_, pivot, 1 / (divisor : ℝ), hcertificate⟩
  · rintro ⟨reward, pivot, scale, hcertificate⟩
    exact ⟨reward, hcertificate.no_uniformPayoff⟩

end GameTheory
