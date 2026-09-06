import UniformEquilibrium.Quitting.Root.UpwardTranslation

/-! # Vector translation of root payoffs and ordinary Nash regret -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {player : Type} [Fintype player] [DecidableEq player]

/-- Coordinatewise translation of a payoff vector. -/
def quittingPayoffVectorTranslate (value shift : Payoff player) : Payoff player :=
  fun who ↦ value who + shift who

omit [DecidableEq player] in
/-- A root successor reads only the translated player's coordinate, with
coefficient equal to the joint Continue mass. -/
theorem quittingRootSuccessorPayoff_vectorTranslate
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (value shift : Payoff player) (root : player → PMF Bool) (who : player) :
    quittingRootSuccessorPayoff reward
        (quittingPayoffVectorTranslate value shift) root who =
      quittingRootSuccessorPayoff reward value root who +
        quittingStationaryContinueMass root * shift who := by
  have hdifference := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    reward (quittingPayoffVectorTranslate value shift) value root who
  dsimp only [quittingPayoffVectorTranslate] at hdifference
  linarith

omit [DecidableEq player] in
/-- Translating both endpoints gives an exact absorption-relative Bellman
residual identity. -/
theorem quittingPayoffVectorTranslate_residual_eq
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (source target shift : Payoff player) (root : player → PMF Bool)
    (who : player) :
    quittingPayoffVectorTranslate target shift who -
        quittingRootSuccessorPayoff reward
          (quittingPayoffVectorTranslate source shift) root who =
      (target who - quittingRootSuccessorPayoff reward source root who) +
        quittingRootAbsorptionMass root * shift who := by
  rw [quittingRootSuccessorPayoff_vectorTranslate]
  unfold quittingPayoffVectorTranslate quittingRootAbsorptionMass
  ring

/-- Pure Quit is invariant under an arbitrary coordinatewise tail
translation. -/
theorem quittingRootQuitPayoff_vectorTranslate
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (value shift : Payoff player) (root : player → PMF Bool) (who : player) :
    quittingRootQuitPayoff reward (quittingPayoffVectorTranslate value shift)
        root who = quittingRootQuitPayoff reward value root who :=
  quittingRootQuitPayoff_continuation_invariant reward _ _ root who

/-- Pure Continue changes by opponent Continue mass times the translated
coordinate. -/
theorem quittingRootContinuePayoff_vectorTranslate
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (value shift : Payoff player) (root : player → PMF Bool) (who : player) :
    quittingRootContinuePayoff reward
        (quittingPayoffVectorTranslate value shift) root who =
      quittingRootContinuePayoff reward value root who +
        quittingRootOpponentContinueMass root who * shift who := by
  have hcongr : quittingRootContinuePayoff reward
      (quittingPayoffVectorTranslate value shift) root who =
      quittingRootContinuePayoff reward
        (Function.update value who (value who + shift who)) root who := by
    unfold quittingRootContinuePayoff
    apply quittingRootExpectedPayoff_continuation_congr
    simp [quittingPayoffVectorTranslate]
  rw [hcongr, quittingRootContinuePayoff_update_add]

/-- A nonnegative coordinate shift of size at most `shiftBound` increases
ordinary coordinate Nash regret by at most absorption times `shiftBound`. -/
theorem quittingRootCoordinateNashDefect_vectorTranslate_le
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (value shift : Payoff player) (root : player → PMF Bool) (who : player)
    (shiftBound : ℝ) (hshiftNonneg : 0 ≤ shift who)
    (hshiftBound : shift who ≤ shiftBound) :
    quittingRootCoordinateNashDefect reward
        (quittingPayoffVectorTranslate value shift) root who ≤
      quittingRootCoordinateNashDefect reward value root who +
        quittingRootAbsorptionMass root * shiftBound := by
  let quit := quittingRootQuitPayoff reward value root who
  let continuePayoff := quittingRootContinuePayoff reward value root who
  let successor := quittingRootSuccessorPayoff reward value root who
  let opponentContinue := quittingRootOpponentContinueMass root who
  let jointContinue := quittingStationaryContinueMass root
  let absorption := quittingRootAbsorptionMass root
  have hopponentNonneg : 0 ≤ opponentContinue :=
    quittingRootOpponentContinueMass_nonneg root who
  have habsorptionNonneg : 0 ≤ absorption :=
    quittingRootAbsorptionMass_nonneg root
  have hopponentLeOne : opponentContinue ≤ 1 :=
    quittingRootOpponentContinueMass_le_one root who
  have hcoefficient : opponentContinue - jointContinue ≤ absorption := by
    dsimp only [opponentContinue, jointContinue, absorption]
    unfold quittingRootAbsorptionMass
    linarith
  have hmax : max quit (continuePayoff + opponentContinue * shift who) ≤
      max quit continuePayoff + opponentContinue * shift who := by
    apply max_le
    · exact (le_max_left quit continuePayoff).trans
        (le_add_of_nonneg_right (mul_nonneg hopponentNonneg hshiftNonneg))
    · exact add_le_add (le_max_right quit continuePayoff) le_rfl
  have hcoefficientProduct :
      (opponentContinue - jointContinue) * shift who ≤
        absorption * shiftBound := by
    have hfirst : (opponentContinue - jointContinue) * shift who ≤
        absorption * shift who :=
      mul_le_mul_of_nonneg_right hcoefficient hshiftNonneg
    exact hfirst.trans
      (mul_le_mul_of_nonneg_left hshiftBound habsorptionNonneg)
  rw [quittingRootCoordinateNashDefect,
    quittingRootQuitPayoff_vectorTranslate,
    quittingRootContinuePayoff_vectorTranslate,
    quittingRootSuccessorPayoff_vectorTranslate]
  change max quit (continuePayoff + opponentContinue * shift who) -
      (successor + jointContinue * shift who) ≤
    max quit continuePayoff - successor + absorption * shiftBound
  linarith

end GameTheory
