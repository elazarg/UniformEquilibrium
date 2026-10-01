import UniformEquilibrium.Quitting.Stationary.SureSoloFiniteHorizon
import UniformEquilibrium.Quitting.Stationary.OneSidedWeakUnitProducer

/-! # Nonnegative sure-owner every-horizon output from actual one-sided guards

The joining-game producer is run on the original reward. Its noncontracting
branch yields all no-join inequalities internally, so the SAME stationary
sure-solo profile is exact Nash at every horizon and delivers the fixed solo
reward with M/H error. This strengthening requires a nonnegative owner singleton.
Nothing here upgrades the signed sole-owner punishment branch to stationary Nash.
-/

noncomputable section

namespace GameTheory

/-- Actual polynomial guards either yield a contracting stationary equilibrium,
or the same sure-solo profile is exact behavioral Nash at every finite horizon. -/
theorem stationaryTerminalNash_or_sureSolo_everyHorizon_of_oneSidedWeakUnitGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner passive : Fin 4) (hdistinct : owner ≠ passive)
    (hguards : QuittingOneSidedWeakUnitGuards reward owner passive)
    (howner : 0 ≤ quittingSoloReward reward owner owner) :
    (∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none value) ∨
    ((quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward (quittingInstantRoot owner)) ∧
      (∀ horizon who,
        quittingFiniteHorizonDeviationCap reward
            (quittingStationaryProfile reward (quittingInstantRoot owner)) horizon who =
          (quittingGame reward).finiteAveragePayoff none horizon
            (quittingStationaryProfile reward (quittingInstantRoot owner)) who) ∧
      (∀ horizon, 0 < horizon → ∀ who,
        |(quittingGame reward).finiteAveragePayoff none horizon
              (quittingStationaryProfile reward (quittingInstantRoot owner)) who -
            quittingSoloReward reward owner who| ≤
          quittingRewardBound reward / (horizon : ℝ)) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingSoloReward reward owner)) := by
  rcases stationaryTerminalNash_or_instantNoJoin_of_oneSidedWeakUnitGuards
    reward owner passive hdistinct hguards with hcontracting | hnoJoin
  · exact Or.inl hcontracting
  · obtain ⟨hterminal, hUE⟩ := stationaryTerminalNash_sureSolo_of_nonnegative_noJoin
      reward owner howner hnoJoin
    exact Or.inr ⟨hterminal,
      quittingFiniteHorizonDeviationCap_sureSolo_eq owner reward howner hnoJoin,
      fun horizon hhorizon who => abs_quittingFiniteAveragePayoff_sureSolo_sub_le
        owner reward horizon hhorizon (quittingRewardBound reward)
        (abs_reward_le_quittingRewardBound reward) who, hUE⟩

/-- Sixteen raw reward comparisons and the owner singleton sign supply the
every-horizon alternative without a favorable root, no-join certificate,
punishment plan, prescribed payoff, or degree hypothesis. -/
theorem stationaryTerminalNash_or_sureSolo_everyHorizon_of_oneSidedWeakUnitRawGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner passive : Fin 4) (hdistinct : owner ≠ passive)
    (hraw : QuittingOneSidedWeakUnitRawGuards reward owner passive)
    (howner : 0 ≤ quittingSoloReward reward owner owner) :
    (∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none value) ∨
    ((quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward (quittingInstantRoot owner)) ∧
      (∀ horizon who,
        quittingFiniteHorizonDeviationCap reward
            (quittingStationaryProfile reward (quittingInstantRoot owner)) horizon who =
          (quittingGame reward).finiteAveragePayoff none horizon
            (quittingStationaryProfile reward (quittingInstantRoot owner)) who) ∧
      (∀ horizon, 0 < horizon → ∀ who,
        |(quittingGame reward).finiteAveragePayoff none horizon
              (quittingStationaryProfile reward (quittingInstantRoot owner)) who -
            quittingSoloReward reward owner who| ≤
          quittingRewardBound reward / (horizon : ℝ)) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingSoloReward reward owner)) :=
  stationaryTerminalNash_or_sureSolo_everyHorizon_of_oneSidedWeakUnitGuards
    reward owner passive hdistinct
      (oneSidedWeakUnitGuards_of_raw reward owner passive hdistinct hraw) howner

end GameTheory
