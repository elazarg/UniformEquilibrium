import UniformEquilibrium.Quitting.Stationary.StationaryTerminalPayoffSelection

/-!
# Fixed-target uniform witnesses from contracting stationary approximations

The existing compact payoff selection supplies the fixed target and actual
stationary terminal approximants. Restricting their family at each requested
accuracy retains one contracting root for both the terminal conclusions and
all sufficiently long finite-horizon conclusions. No uniform contraction
rate or exact stationary equilibrium attainment is asserted.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Indexed terminal acceptance keeps one actual contracting stationary root
as the witness for both terminal approximation and every sufficiently long
finite horizon, at the same specified target and requested accuracy. -/
theorem stationaryUniformPayoffWitnesses_of_terminalTargetAcceptance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (hacceptance : ∀ accuracy : ℝ, 0 < accuracy →
      ∃ root : ι → PMF Bool,
        (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
        (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
          (quittingStationaryProfile reward root) ∧
        ∀ who, |quittingTerminalPayoff reward (quittingStationaryProfile reward root) who -
          target who| ≤ accuracy) :
    ∀ accuracy : ℝ, 0 < accuracy →
      ∃ root : ι → PMF Bool,
        (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
        (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
          (quittingStationaryProfile reward root) ∧
        (∀ who, |quittingTerminalPayoff reward (quittingStationaryProfile reward root) who -
          target who| ≤ accuracy) ∧
        ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon accuracy
            (quittingStationaryProfile reward root) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingStationaryProfile reward root) who - target who| ≤ accuracy := by
  intro accuracy haccuracy
  let admissible := {root : ι → PMF Bool //
    (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
      (quittingStationaryProfile reward root) ∧
    ∀ who, |quittingTerminalPayoff reward (quittingStationaryProfile reward root) who -
      target who| ≤ accuracy}
  let profiles : admissible → (quittingGame reward).BehaviorProfile :=
    fun selected => quittingStationaryProfile reward selected.val
  have hfamily : ∀ tolerance : ℝ, 0 < tolerance →
      ∃ selected : admissible,
        (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) tolerance
          (profiles selected) ∧
        ∀ who, |quittingTerminalPayoff reward (profiles selected) who - target who| ≤
          tolerance := by
    intro tolerance htolerance
    obtain ⟨root, hcontracts, hnash, hclose⟩ :=
      hacceptance (min accuracy tolerance) (lt_min haccuracy htolerance)
    refine ⟨⟨root, hcontracts, hnash.mono (min_le_left _ _),
      fun who => (hclose who).trans (min_le_left _ _)⟩,
      hnash.mono (min_le_right _ _), fun who => (hclose who).trans (min_le_right _ _)⟩
  obtain ⟨selected, threshold, hwitnesses⟩ :=
    quittingGame_uniformPayoffWitnesses_of_terminalTargetAcceptance_family
      reward target profiles hfamily accuracy haccuracy
  exact ⟨selected.val, selected.property.1, selected.property.2.1,
    selected.property.2.2, threshold, hwitnesses⟩

/-- The existing compact payoff selection yields one fixed UE target whose
actual contracting stationary roots witness terminal approximation and all
long finite horizons simultaneously. Only the payoff target is selected by
compactness; no limiting root or cap and no exact attainment are used. -/
theorem exists_uniformPayoff_stationaryWitnesses_of_terminalApproximations
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (happroximation : ∀ accuracy : ℝ, 0 < accuracy →
      ∃ root : ι → PMF Bool,
        (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
        (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
          (quittingStationaryProfile reward root)) :
    ∃ target : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none target ∧
      ∀ accuracy : ℝ, 0 < accuracy →
        ∃ root : ι → PMF Bool,
          (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
          (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
            (quittingStationaryProfile reward root) ∧
          (∀ who, |quittingTerminalPayoff reward (quittingStationaryProfile reward root) who -
            target who| ≤ accuracy) ∧
          ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
            (quittingGame reward).IsεHorizonNash none horizon accuracy
              (quittingStationaryProfile reward root) ∧
            ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
              (quittingStationaryProfile reward root) who - target who| ≤ accuracy := by
  obtain ⟨target, huniform, hacceptance⟩ :=
    exists_uniformPayoff_stationaryTargetAcceptance_of_terminalApproximations
      reward happroximation
  exact ⟨target, huniform,
    stationaryUniformPayoffWitnesses_of_terminalTargetAcceptance reward target hacceptance⟩

end GameTheory
