/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.OrientedWitnessSwitchPureTime

/-!
# Debt-square routing to pure-time witness-switch atoms

Semantic debt is the behavioral best-response envelope minus prescribed
payoff. A large signed debt square therefore forces a large envelope square
once the prescribed-payoff square is budgeted. Combining this identity with a
fixed pure-time square budget invokes the corner-preserving pure-time adapter.

The theorem concerns one supplied literal four-profile face. It does not
produce that face from a chronological play path.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A debt square exceeding the prescribed and fixed-witness square budgets
produces an oriented pure-time rectangle atom on the same literal corners. -/
theorem exists_pureTimeWitnessSwitchRectangle_of_abs_debtCurvature
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x00 x10 x01 x11 : (quittingGame reward).BehaviorProfile)
    (observer : ι) (prescribedBound q charge eta : ℝ)
    (hcharge : 0 < charge) (heta : 0 < eta)
    (hprescribed :
      |quittingTerminalPayoff reward x11 observer -
          quittingTerminalPayoff reward x10 observer -
          quittingTerminalPayoff reward x01 observer +
          quittingTerminalPayoff reward x00 observer| ≤ prescribedBound)
    (hface : ∀ quitTime : Option ℕ,
      |quittingPureTimeDeviationPayoff reward x11 observer quitTime -
          quittingPureTimeDeviationPayoff reward x10 observer quitTime -
          quittingPureTimeDeviationPayoff reward x01 observer quitTime +
          quittingPureTimeDeviationPayoff reward x00 observer quitTime| ≤ q)
    (hcurvature : charge + prescribedBound + q + 3 * eta ≤
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward x11) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward x10) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward x01) observer +
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward x00) observer|) :
    HasQuittingPureTimeWitnessSwitchRectangle reward x11 x00 observer
        charge eta ∨
      HasQuittingPureTimeWitnessSwitchRectangle reward x10 x01 observer
        charge eta := by
  let envelopeCurvature :=
    quittingContinuationBestResponseValue reward x11 observer -
      quittingContinuationBestResponseValue reward x10 observer -
      quittingContinuationBestResponseValue reward x01 observer +
      quittingContinuationBestResponseValue reward x00 observer
  let prescribedCurvature :=
    quittingTerminalPayoff reward x11 observer -
      quittingTerminalPayoff reward x10 observer -
      quittingTerminalPayoff reward x01 observer +
      quittingTerminalPayoff reward x00 observer
  let debtCurvature :=
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward x11) observer -
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward x10) observer -
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward x01) observer +
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward x00) observer
  have hidentity : debtCurvature =
      envelopeCurvature - prescribedCurvature := by
    dsimp only [debtCurvature, envelopeCurvature, prescribedCurvature,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair]
    ring
  have habs : |debtCurvature| ≤
      |envelopeCurvature| + |prescribedCurvature| := by
    rw [hidentity]
    calc
      |envelopeCurvature - prescribedCurvature| =
          |envelopeCurvature + -prescribedCurvature| := by ring_nf
      _ ≤ |envelopeCurvature| + |-prescribedCurvature| := abs_add_le _ _
      _ = |envelopeCurvature| + |prescribedCurvature| := by rw [abs_neg]
  have hprescribed' : |prescribedCurvature| ≤ prescribedBound := by
    simpa only [prescribedCurvature] using hprescribed
  have hdebt : charge + prescribedBound + q + 3 * eta ≤
      |debtCurvature| := by
    simpa only [debtCurvature] using hcurvature
  have henvelope : charge + q + 3 * eta ≤ |envelopeCurvature| := by
    linarith
  apply exists_pureTimeWitnessSwitchRectangle_of_abs_envelopeCurvature
    reward x00 x10 x01 x11 observer q charge eta hcharge heta hface
  simpa only [envelopeCurvature] using henvelope

end GameTheory
