import UniformEquilibrium.Quitting.Examples.AdaptiveChildEquilibriumExtensionNoGo
import UniformEquilibrium.Quitting.Root.OneDateNeverHorizonNash

/-! # One internally selected nearby profile works for every accuracy

The profile, interior active probabilities and terminal payoff are selected once.
The reward radius and paired deletion floor are the original neighborhood choices.
Only the finite-horizon payoff-delivery threshold depends on accuracy.
-/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

theorem nearbyProfile_exactHorizonNash_of_terminalNash
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ)
    (hnash : (quittingGame table).IsεAsymptoticNash (quittingTerminalPayoff table) 0
      (nearbyProfile table probability)) (horizon : ℕ) :
    (quittingGame table).IsεHorizonNash none horizon 0
      (nearbyProfile table probability) :=
  quittingOneDateThenNeverProfile_exactHorizonNash table (nearbyRoot probability) hnash horizon

theorem nearbyProfile_sameProfile_uniformPayoffWitness
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ)
    (hnash : (quittingGame table).IsεAsymptoticNash (quittingTerminalPayoff table) 0
      (nearbyProfile table probability)) :
    ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
      ∀ horizon : ℕ, threshold ≤ horizon →
        (quittingGame table).IsεHorizonNash none horizon accuracy
          (nearbyProfile table probability) ∧
        ∀ who, |(quittingGame table).finiteAveragePayoff none horizon
            (nearbyProfile table probability) who -
          quittingTerminalPayoff table (nearbyProfile table probability) who| ≤ accuracy :=
  quittingOneDateThenNeverProfile_sameProfile_uniformPayoffWitness
    table (nearbyRoot probability) hnash

theorem exists_nearby_oneDate_sameProfile_horizon_equilibrium
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hsmall : delta < 1 / 8)
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta) :
    ∃ probability : Fin 3 → ℝ,
      (∀ active, 1 / 4 < probability active ∧ probability active < 3 / 4) ∧
      (quittingGame table).IsεAsymptoticNash (quittingTerminalPayoff table) 0
        (nearbyProfile table probability) ∧
      (∀ horizon : ℕ, (quittingGame table).IsεHorizonNash none horizon 0
        (nearbyProfile table probability)) ∧
      (∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
        ∀ horizon : ℕ, threshold ≤ horizon →
          (quittingGame table).IsεHorizonNash none horizon accuracy
            (nearbyProfile table probability) ∧
          ∀ who, |(quittingGame table).finiteAveragePayoff none horizon
              (nearbyProfile table probability) who -
            quittingTerminalPayoff table (nearbyProfile table probability) who| ≤ accuracy) ∧
      (quittingGame table).IsUniformEquilibriumPayoff none
        (quittingTerminalPayoff table (nearbyProfile table probability)) := by
  obtain ⟨probability, hbox, hnash, _⟩ :=
    exists_nearby_oneDate_exactTerminalNash_and_uniformPayoff table hdelta hsmall hclose
  have hwitness := nearbyProfile_sameProfile_uniformPayoffWitness table probability hnash
  refine ⟨probability, hbox, hnash,
    nearbyProfile_exactHorizonNash_of_terminalNash table probability hnash, hwitness, ?_⟩
  intro accuracy haccuracy
  obtain ⟨threshold, hthreshold⟩ := hwitness accuracy haccuracy
  exact ⟨nearbyProfile table probability, threshold, hthreshold⟩

/-- The radius is unchanged; the interior root is produced inside each nearby table. -/
theorem exists_solved_open_neighborhood_sameProfile_horizon_equilibrium_floor :
    ∃ constant radius : ℝ, 0 < constant ∧ 0 < radius ∧
      ∀ table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      (∀ terminal player, |table terminal player - reward terminal player| < radius) →
      (∀ parent : (quittingGame table).BehaviorProfile, ∀ deleted : Fin 4,
        constant ≤ quittingTerminalExploitability table parent +
          quittingTerminalExploitability (nearbyChildReward table deleted)
            (nearbyRestrictedProfile table deleted parent)) ∧
      ∃ probability : Fin 3 → ℝ,
        (∀ active, 1 / 4 < probability active ∧ probability active < 3 / 4) ∧
        (quittingGame table).IsεAsymptoticNash (quittingTerminalPayoff table) 0
          (nearbyProfile table probability) ∧
        (∀ horizon : ℕ, (quittingGame table).IsεHorizonNash none horizon 0
          (nearbyProfile table probability)) ∧
        (∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
          ∀ horizon : ℕ, threshold ≤ horizon →
            (quittingGame table).IsεHorizonNash none horizon accuracy
              (nearbyProfile table probability) ∧
            ∀ who, |(quittingGame table).finiteAveragePayoff none horizon
                (nearbyProfile table probability) who -
              quittingTerminalPayoff table (nearbyProfile table probability) who| ≤ accuracy) ∧
        (quittingGame table).IsUniformEquilibriumPayoff none
          (quittingTerminalPayoff table (nearbyProfile table probability)) := by
  obtain ⟨constant, radius, hc, hr, hsmall, hfloor⟩ :=
    exists_open_reward_neighborhood_paired_floor
  refine ⟨constant, radius, hc, hr, ?_⟩
  intro table hclose
  refine ⟨hfloor table hclose, ?_⟩
  obtain ⟨delta, hdelta, hlt, hbound⟩ := exists_reward_distance_lt table hclose
  exact exists_nearby_oneDate_sameProfile_horizon_equilibrium table hdelta
    (hlt.trans_le hsmall) hbound

end GameTheory.AdaptiveChildCenter
