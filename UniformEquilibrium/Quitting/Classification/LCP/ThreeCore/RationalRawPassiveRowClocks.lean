import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.RawPassiveRowInverseCriterion
import UniformEquilibrium.Quitting.Cycles.RationalSingletonClockProducer

/-! # Rational clocks from the literal strict passive-row criterion

Only singleton rewards are required to be rational. The strict inverse test
produces a labeling and the existing right cycle; its literal rate formulas
then compute rational coarse hazards. Passive-row inheritance preserves those
hazards, so the checked rational calendar producer supplies actual independent
finite clocks against all behavioral replacements. Nonsingleton rewards may
be arbitrary real numbers within the supplied rational reward bound.

The arithmetic rate function below is executable. The inverse classification
selects a labeling existentially; no canonical executable labeling search or
bit-complexity estimate is asserted here.
-/

namespace GameTheory.PassiveRowInverseCriterion

open QuittingLCPClassification Math.LinearProgramming
open scoped BigOperators

/-- The three existing right-cycle formulas evaluated in exact rational arithmetic.
Singleton indices are owner first, receiver second. -/
def rationalRightHazard (rationalSingleton : Fin 3 → Fin 3 → ℚ) : Fin 3 → ℚ :=
  let negativeZero := rationalSingleton 0 0 - rationalSingleton 1 0
  let positiveZero := rationalSingleton 2 0 - rationalSingleton 0 0
  let negativeOne := rationalSingleton 1 1 - rationalSingleton 2 1
  let positiveOne := rationalSingleton 0 1 - rationalSingleton 1 1
  let negativeTwo := rationalSingleton 2 2 - rationalSingleton 0 2
  let positiveTwo := rationalSingleton 1 2 - rationalSingleton 2 2
  let determinantGap := positiveZero * positiveOne * positiveTwo -
    negativeZero * negativeOne * negativeTwo
  ![determinantGap /
      (positiveZero * positiveOne * positiveTwo +
        positiveZero * positiveOne * negativeTwo + negativeZero * positiveOne * negativeTwo),
    determinantGap /
      (positiveZero * positiveOne * positiveTwo +
        negativeZero * positiveOne * positiveTwo + negativeZero * negativeOne * positiveTwo),
    determinantGap /
      (positiveZero * positiveOne * positiveTwo +
        positiveZero * negativeOne * positiveTwo + positiveZero * negativeOne * negativeTwo)]

/-- Casting the rational arithmetic gives exactly the existing real rates. -/
theorem rationalRightHazard_cast
    (reward : QuittingReward3) (rationalSingleton : Fin 3 → Fin 3 → ℚ)
    (hsingleton : ∀ owner who, quittingSoloReward reward owner who =
      (rationalSingleton owner who : ℝ)) (phase : Fin 3) :
    (rationalRightHazard rationalSingleton phase : ℝ) =
      ![rightAlpha reward, rightBeta reward, rightGamma reward] phase := by
  fin_cases phase <;>
    simp [rationalRightHazard, rightAlpha, rightBeta, rightGamma, rightDelta,
      rightP, rightQ, rightR, rightS, rightT, rightU, hsingleton]

variable {players : ℕ}
variable (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players))
variable (deleted : Fin players → Prop) [DecidablePred deleted]

local notation "Child" => {who : Fin players // ¬ deleted who}

/-- The raw strict inverse test produces an ambient certificate and rational
hazards. Neither a child cycle nor rational hazard witnesses are hypotheses. -/
theorem exists_rationalBalancedCertificate_of_raw_strictInverse_triple
    (rationalSingleton : Fin players → Fin players → ℚ)
    (hsingleton : ∀ owner who, quittingSoloReward reward owner who =
      (rationalSingleton owner who : ℝ))
    (hcard : Fintype.card Child = 3)
    (hdet : (childMatrix reward deleted).det ≠ 0)
    (hinverse : ∀ row column : Child, 0 < (childMatrix reward deleted)⁻¹ row column)
    (houtside : ∀ outside, deleted outside →
      ∀ inside : Child, 0 ≤ inverseWeight reward deleted outside inside) :
    ∃ (certificate : BalancedSingletonCycleCertificate (L := 3) reward)
      (hazard : Fin 3 → ℚ),
      (∀ phase, certificate.hazard phase = (hazard phase : ℝ)) ∧
      (∀ who, deleted who → ∀ phase, who ≠ certificate.owner phase) := by
  have hpositive : HasStrictlyPositiveInverse
      (normalizedSoloMatrix (quittingDeleteReward reward deleted)) := ⟨hdet, hinverse⟩
  obtain ⟨label, ⟨cycle⟩⟩ := exists_rightSingletonCycle_of_strictlyPositiveInverse
    reward deleted hcard hpositive
  let childReward := quittingDeleteReward reward deleted
  let labeledReward := quittingRewardReindex label childReward
  let labeledSingleton : Fin 3 → Fin 3 → ℚ := fun owner who =>
    rationalSingleton (label.symm owner).1 (label.symm who).1
  have hlabeled : ∀ owner who, quittingSoloReward labeledReward owner who =
      (labeledSingleton owner who : ℝ) := by
    intro owner who
    have hreindex : quittingSoloReward labeledReward owner who =
        quittingSoloReward childReward (label.symm owner) (label.symm who) := by
      simp [labeledReward, quittingSoloReward, quittingCoalitionEquiv]
    rw [hreindex]
    have hchild : quittingSoloReward childReward (label.symm owner) (label.symm who) =
        quittingSoloReward reward (label.symm owner).1 (label.symm who).1 :=
      quittingDeleteReward_singletonTerminal reward deleted
        (label.symm owner) (label.symm who)
    exact hchild.trans (hsingleton (label.symm owner).1 (label.symm who).1)
  let child := RightSingletonCycle.toBalancedCertificate_reindex childReward label cycle
  let rows := factorization reward deleted hdet houtside
  let certificate := rows.certificate child
  let hazard := rationalRightHazard labeledSingleton
  have hcast : ∀ phase, certificate.hazard phase = (hazard phase : ℝ) := by
    intro phase
    change ![rightAlpha labeledReward, rightBeta labeledReward, rightGamma labeledReward]
      phase = (rationalRightHazard labeledSingleton phase : ℝ)
    exact (rationalRightHazard_cast labeledReward labeledSingleton hlabeled phase).symm
  refine ⟨certificate, hazard, hcast, ?_⟩
  intro who hout phase heq
  have hnot : ¬ deleted (certificate.owner phase) := (child.owner phase).2
  exact hnot (heq ▸ hout)

/-- One certificate and its fixed target are produced before the accuracy.
Every rational accuracy then gives exact rational marginal masses, the same
source calendar's full terminal semantic pair, behavioral regret and delivery
bounds, passive Never laws, and the packet's literal three-phase date bound. -/
theorem exists_rationalClocks_of_raw_strictInverse_triple
    (rationalSingleton : Fin players → Fin players → ℚ)
    (hsingleton : ∀ owner who, quittingSoloReward reward owner who =
      (rationalSingleton owner who : ℝ))
    (hcard : Fintype.card Child = 3)
    (hdet : (childMatrix reward deleted).det ≠ 0)
    (hinverse : ∀ row column : Child, 0 < (childMatrix reward deleted)⁻¹ row column)
    (houtside : ∀ outside, deleted outside →
      ∀ inside : Child, 0 ≤ inverseWeight reward deleted outside inside) :
    ∃ (certificate : BalancedSingletonCycleCertificate (L := 3) reward)
      (hazard : Fin 3 → ℚ),
      ∃ hcast : ∀ phase, certificate.hazard phase = (hazard phase : ℝ),
      ∀ (M η : ℚ) (hη : 0 < η) (hηM : η ≤ M)
        (_hreward : ∀ terminal who, |reward terminal who| ≤ (M : ℝ)),
        let data := certificate.rationalClockData hazard hcast
        let turns := data.turns M η (hη.trans_le hηM) hη
          (certificate.rationalClockData_survivalBound_lt_one hazard hcast)
        let δ := η / (4 * M)
        ∃ mixed : Fin players → PMF (Option (Fin (turns * data.period δ))),
          (∀ who choice, (mixed who choice).toReal = (data.mass δ turns who choice : ℝ)) ∧
          (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
            quittingBehaviorStoppingLaw reward
              (certificate.rationalFiniteProfile (δ : ℝ) turns who)) ∧
          quittingTerminalSemanticPair reward
              (quittingFiniteDeadlineTimingProfile reward (turns * data.period δ) mixed) =
            quittingTerminalSemanticPair reward
              (certificate.rationalFiniteProfile (δ : ℝ) turns) ∧
          (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) (η : ℝ)
            (quittingFiniteDeadlineTimingProfile reward (turns * data.period δ) mixed) ∧
          (∀ who, |quittingTerminalPayoff reward
              (quittingFiniteDeadlineTimingProfile reward (turns * data.period δ) mixed) who -
              certificate.coarse certificate.initial who| ≤ (η : ℝ) / 6) ∧
          (∀ who, deleted who → mixed who = PMF.pure none) ∧
          ((turns * data.period δ : ℕ) : ℝ) ≤ (turns : ℝ) *
            (3 + (4 * (M : ℝ) / (η : ℝ)) *
              ∑ phase, Math.rationalArcOdds (certificate.hazard phase)) := by
  obtain ⟨certificate, hazard, hcast, howners⟩ :=
    exists_rationalBalancedCertificate_of_raw_strictInverse_triple
      reward deleted rationalSingleton hsingleton hcard hdet hinverse houtside
  refine ⟨certificate, hazard, hcast, ?_⟩
  intro M η hη hηM hreward
  obtain ⟨mixed, hmass, hlaws, hpair, hnash, hdelivery, hnever, hdates⟩ :=
    certificate.exists_rationalClocks_isTerminalNash_and_delivery
      hazard hcast hη hηM hreward
  refine ⟨mixed, hmass, hlaws, hpair, hnash, hdelivery, ?_, hdates⟩
  intro who hout
  exact hnever who (howners who hout)

end GameTheory.PassiveRowInverseCriterion
