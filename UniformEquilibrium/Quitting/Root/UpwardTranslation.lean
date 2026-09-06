import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix
import UniformEquilibrium.Quitting.Boundary.Repair.SupportEnlargementAlternative

/-! # Upward translation of quitting root payoff annotations -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Common upward translation of a payoff annotation. -/
def quittingPayoffUpwardTranslate (tail : Payoff ι) (δ : ℝ) : Payoff ι :=
  fun who ↦ tail who + 2 * δ

private theorem endpointDifference_upwardTranslate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (δ : ℝ) :
    quittingRootEndpointDifference reward (quittingPayoffUpwardTranslate tail δ)
        root who =
      quittingRootEndpointDifference reward tail root who -
        2 * δ * quittingRootOpponentContinueMass root who := by
  unfold quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_continuation_invariant reward
    (quittingPayoffUpwardTranslate tail δ) tail root who]
  have hcongr : quittingRootContinuePayoff reward
      (quittingPayoffUpwardTranslate tail δ) root who =
      quittingRootContinuePayoff reward
        (Function.update tail who (tail who + 2 * δ)) root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp [quittingPayoffUpwardTranslate]
  rw [hcongr, quittingRootContinuePayoff_update_add]
  ring

/-- Upward translation turns support-local δ-Nash into ordinary mixed-root
regret bounded by three times δ times row absorption. -/
theorem coordinateNashDefect_upwardTranslate_le_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) {δ : ℝ}
    (hδ : 0 < δ)
    (hsupport : IsQuittingRootSupportApproxNash reward tail δ root) :
    quittingRootCoordinateNashDefect reward
        (quittingPayoffUpwardTranslate tail δ) root who ≤
      3 * δ * quittingRootAbsorptionMass root := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart]
  rw [endpointDifference_upwardTranslate]
  let difference := quittingRootEndpointDifference reward tail root who
  let opponentMass := quittingRootOpponentContinueMass root who
  let quitProbability := (root who true).toReal
  let continueProbability := (root who false).toReal
  have hq0 : 0 ≤ quitProbability := ENNReal.toReal_nonneg
  have hc0 : 0 ≤ continueProbability := ENNReal.toReal_nonneg
  have hm0 : 0 ≤ opponentMass := quittingRootOpponentContinueMass_nonneg root who
  have hm1 : opponentMass ≤ 1 := quittingRootOpponentContinueMass_le_one root who
  have hqAbs : quitProbability ≤ quittingRootAbsorptionMass root :=
    quittingQuitProbability_le_absorptionMass root who
  by_cases hshift : 0 ≤ difference - 2 * δ * opponentMass
  · rw [max_eq_left hshift, max_eq_right (by linarith : -(difference -
        2 * δ * opponentMass) ≤ 0), mul_zero, add_zero]
    change continueProbability * (difference - 2 * δ * opponentMass) ≤ _
    by_cases hzeroShift : difference - 2 * δ * opponentMass = 0
    · rw [hzeroShift, mul_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hδ.le)
        (quittingRootAbsorptionMass_nonneg root)
    by_cases hc : continueProbability = 0
    · rw [hc, zero_mul]
      exact mul_nonneg (mul_nonneg (by norm_num) hδ.le)
        (quittingRootAbsorptionMass_nonneg root)
    · have hcpos : 0 < continueProbability :=
        lt_of_le_of_ne hc0 (Ne.symm hc)
      have hold : difference ≤ δ := (hsupport who).2 hcpos
      have hmhalf : opponentMass < 1 / 2 := by
        have hshiftPos : 0 < difference - 2 * δ * opponentMass :=
          lt_of_le_of_ne hshift (Ne.symm hzeroShift)
        nlinarith
      have haHalf : 1 / 2 < quittingRootAbsorptionMass root := by
        dsimp only [opponentMass] at hmhalf
        rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass] at hmhalf
        have hopponent := quittingRootOpponentAbsorptionMass_le_absorptionMass root who
        linarith
      have hc1 : continueProbability ≤ 1 := by
        linarith [quittingRoot_continueProbability_add_quitProbability root who]
      nlinarith
  · have hshift' : difference - 2 * δ * opponentMass ≤ 0 := le_of_not_ge hshift
    rw [max_eq_right hshift', max_eq_left (by linarith :
      0 ≤ -(difference - 2 * δ * opponentMass))]
    change continueProbability * 0 +
      quitProbability * (-(difference - 2 * δ * opponentMass)) ≤ _
    rw [mul_zero, zero_add]
    by_cases hq : quitProbability = 0
    · rw [hq, zero_mul]
      exact mul_nonneg (mul_nonneg (by norm_num) hδ.le)
        (quittingRootAbsorptionMass_nonneg root)
    · have hqpos : 0 < quitProbability := lt_of_le_of_ne hq0 (Ne.symm hq)
      have hold : -δ ≤ difference := (hsupport who).1 hqpos
      have hgap : -(difference - 2 * δ * opponentMass) ≤ 3 * δ := by
        nlinarith
      calc
        quitProbability * (-(difference - 2 * δ * opponentMass)) ≤
            quitProbability * (3 * δ) :=
          mul_le_mul_of_nonneg_left hgap hq0
        _ ≤ quittingRootAbsorptionMass root * (3 * δ) :=
          mul_le_mul_of_nonneg_right hqAbs (by positivity)
        _ = _ := by ring

omit [DecidableEq ι] in
/-- Translating every payoff coordinate upward by `2 * δ` creates exactly
`2 * δ` times the current absorption mass as the Bellman residual. -/
theorem quittingPayoffUpwardTranslate_sub_successor_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current next : Payoff ι) (root : ι → PMF Bool) (who : ι) (δ : ℝ)
    (hpolicy : next who = quittingRootSuccessorPayoff reward current root who) :
    quittingPayoffUpwardTranslate next δ who -
        quittingRootSuccessorPayoff reward
          (quittingPayoffUpwardTranslate current δ) root who =
      2 * δ * quittingRootAbsorptionMass root := by
  have htail := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    reward (quittingPayoffUpwardTranslate current δ) current root who
  dsimp only [quittingPayoffUpwardTranslate] at hpolicy htail ⊢
  have hc := quittingStationaryContinueMass_nonneg root
  have hc1 := quittingStationaryContinueMass_le_one root
  unfold quittingRootAbsorptionMass
  nlinarith

end GameTheory

