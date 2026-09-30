import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseWeakBoundaryProducer
import UniformEquilibrium.Quitting.Stationary.StationaryTerminalPayoffSelection

/-! # Theorem C with one fixed target carried by the stationary approximating profiles -/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

/-- Theorem C's weak half-ceiling branch, including coupling of the fixed UE
target to the original-table stationary profiles of vanishing complete regret. -/
theorem exists_stationary_uniformPayoff_targetApproximation_of_weakHalfRaw
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hraw : QuittingHalfWeakRawGuards reward) :
    ∃ target : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none target ∧
      ∀ accuracy : ℝ, 0 < accuracy →
        ∃ root : Fin 4 → PMF Bool,
          (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
          (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
            (quittingStationaryProfile reward root) ∧
          ∀ who, |quittingTerminalPayoff reward (quittingStationaryProfile reward root) who -
            target who| ≤ accuracy := by
  exact exists_uniformPayoff_stationaryTargetAcceptance_of_terminalApproximations reward
    (exists_stationary_terminalApproximation_of_weakHalfRaw reward hdet hinverse hraw)

/-- Theorem C's strict unit-ceiling/nonnegative-inverse branch, with the same
fixed-target stationary approximation conclusion for every dimension at least three. -/
theorem exists_stationary_uniformPayoff_targetApproximation_of_strictRawUnit_nonnegativeInverse
    {n : ℕ} (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hcard : 3 ≤ n) (first second : Fin n) (hdistinct : first ≠ second)
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hraw : QuittingCrossedStrictRawUnitGuards reward first second) :
    ∃ target : Payoff (Fin n),
      (quittingGame reward).IsUniformEquilibriumPayoff none target ∧
      ∀ accuracy : ℝ, 0 < accuracy →
        ∃ root : Fin n → PMF Bool,
          (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
          (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
            (quittingStationaryProfile reward root) ∧
          ∀ who, |quittingTerminalPayoff reward (quittingStationaryProfile reward root) who -
            target who| ≤ accuracy := by
  exact exists_uniformPayoff_stationaryTargetAcceptance_of_terminalApproximations reward
    (exists_stationary_terminalApproximation_of_strictRawUnit_nonnegativeInverse
      reward hcard first second hdistinct hdet hinverse hraw)

end GameTheory
