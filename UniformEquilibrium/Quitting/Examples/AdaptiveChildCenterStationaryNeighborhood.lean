import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenter
import UniformEquilibrium.Quitting.Root.RewardStability
import UniformEquilibrium.Quitting.Stationary.SingleAnchorArbitraryCompletion

/-! # The alternative stationary single-anchor producer on the half-unit neighborhood

This delegates the source semantic handoff at delta < 1/2. It does not replace
the separately checked interior one-date-then-Never construction at delta < 1/8.
-/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

theorem reward_anchor_membership : QuittingSingleAnchorMembershipReward reward 3 := by
  intro terminal
  simp [reward]

/-- Every complementary mixed point, not merely a selected induced Nash point. -/
theorem nearby_singleAnchorQuitValue_lower
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {delta : ℝ}
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta)
    (point : mixedPolytope (quittingBinaryForm (quittingSingleAnchorFree (3 : Fin 4))).sig) :
    1 - delta ≤ quittingSingleAnchorQuitValue table 3 point := by
  have hdelta : 0 ≤ delta := (abs_nonneg _).trans (hclose (quittingSingletonTerminal 3) 3)
  have hvalue := abs_quittingRootExpectedPayoff_sub_of_reward_and_tail_close
    table reward 0 0 (Function.update (quittingSingleAnchorRoot 3 point) 3 (PMF.pure true)) 3
    (fun terminal => hclose terminal 3) (by simpa using hdelta)
  change |quittingSingleAnchorQuitValue table 3 point -
    quittingSingleAnchorQuitValue reward 3 point| ≤ delta at hvalue
  rw [quittingSingleAnchorQuitValue_eq_one_of_membership
    reward 3 point reward_anchor_membership] at hvalue
  linarith [abs_le.mp hvalue]

theorem nearby_anchorExcludingReward_le
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {delta : ℝ}
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (hnot : (3 : Fin 4) ∉ terminal.1) :
    table terminal 3 ≤ delta := by
  have hvalue := hclose terminal 3
  have hzero : reward terminal 3 = 0 := by simp [reward, hnot]
  rw [hzero, sub_zero] at hvalue
  exact (abs_le.mp hvalue).2

/-- The actual anchor dominates at ANY complementary point throughout delta < 1/2. -/
theorem nearby_singleAnchorInducedDominance
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {delta : ℝ}
    (hsmall : delta < 1 / 2)
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta)
    (point : mixedPolytope (quittingBinaryForm (quittingSingleAnchorFree (3 : Fin 4))).sig) :
    QuittingSingleAnchorInducedDominance table 3 point := by
  have hquit := nearby_singleAnchorQuitValue_lower table hclose point
  constructor
  · linarith
  · intro terminal hnot
    linarith [nearby_anchorExcludingReward_le table hclose terminal hnot]

/-- The induced finite game constructs its Nash point internally. The SAME
actual stationary profile supplies exact terminal Nash and a fixed UE payoff. -/
theorem exists_nearby_stationary_exactTerminalNash_and_uniformPayoff
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {delta : ℝ}
    (hsmall : delta < 1 / 2)
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta) :
    ∃ point ∈ quittingPersistentBaseNashSet table {3}
        (quittingSingleAnchorFree (3 : Fin 4)),
      QuittingSingleAnchorInducedDominance table 3 point ∧
      let root := quittingSingleAnchorRoot 3 point
      (quittingGame table).IsεAsymptoticNash (quittingTerminalPayoff table) 0
          (quittingStationaryProfile table root) ∧
        (quittingGame table).IsUniformEquilibriumPayoff none
          (quittingTerminalPayoff table (quittingStationaryProfile table root)) := by
  obtain ⟨point, hpoint⟩ := quittingPersistentBaseNashSet_nonempty table {3}
    (quittingSingleAnchorFree (3 : Fin 4))
  have hdominates := nearby_singleAnchorInducedDominance table hsmall hclose point
  exact ⟨point, hpoint, hdominates,
    exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorPoint
      table 3 point hpoint hdominates⟩

end GameTheory.AdaptiveChildCenter
