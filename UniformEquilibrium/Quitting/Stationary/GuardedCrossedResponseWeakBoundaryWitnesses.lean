import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseWeakBoundaryProducer
import UniformEquilibrium.Quitting.Stationary.StationaryUniformPayoffWitnessSelection

/-!
# Actual stationary uniform witnesses at the crossed weak boundaries

Both raw-reward branches select one fixed original-game payoff target. At
each accuracy, the same contracting stationary root supplies terminal
approximation and Nash/delivery bounds over every sufficiently long finite
horizon. No exact stationary attainment or common contraction rate is asserted.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

/-- Weak half-ceiling raw comparisons and a nonnegative singleton inverse
produce one fixed target with actual contracting stationary witnesses for
both terminal approximation and all sufficiently long finite horizons. -/
theorem exists_stationary_uniformPayoff_witnesses_of_weakHalfRaw
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
          (∀ who, |quittingTerminalPayoff reward (quittingStationaryProfile reward root) who -
            target who| ≤ accuracy) ∧
          ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
            (quittingGame reward).IsεHorizonNash none horizon accuracy
              (quittingStationaryProfile reward root) ∧
            ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
              (quittingStationaryProfile reward root) who - target who| ≤ accuracy :=
  exists_uniformPayoff_stationaryWitnesses_of_terminalApproximations reward
    (exists_stationary_terminalApproximation_of_weakHalfRaw reward hdet hinverse hraw)

/-- Strict unit-ceiling raw guards and a nonnegative singleton inverse
produce the same fixed-target stationary witness conclusion in every
dimension at least three. The requested accuracy may change the root. -/
theorem exists_stationary_uniformPayoff_witnesses_of_strictRawUnit_nonnegativeInverse
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
          (∀ who, |quittingTerminalPayoff reward (quittingStationaryProfile reward root) who -
            target who| ≤ accuracy) ∧
          ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
            (quittingGame reward).IsεHorizonNash none horizon accuracy
              (quittingStationaryProfile reward root) ∧
            ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
              (quittingStationaryProfile reward root) who - target who| ≤ accuracy :=
  exists_uniformPayoff_stationaryWitnesses_of_terminalApproximations reward
    (exists_stationary_terminalApproximation_of_strictRawUnit_nonnegativeInverse
      reward hcard first second hdistinct hdet hinverse hraw)

end GameTheory
