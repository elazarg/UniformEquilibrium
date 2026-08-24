/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.ChargedSoloBlockerRepayment
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourOffMinimumChargedBlockerGate

/-!
# Source-native charged solo blocker repayment

The off-minimum gate now selects an outsider attaining the finite maximum
joining gain.  This module composes that actual gate with the compact uniform
blocker gap and the anchored exact-orbit repayment theorem.

The result controls one payoff annotation coordinate.  It does not produce
blocker support, collision mass, payoff near-return, or a uniform payoff.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

namespace FinFourChargedSoloBlockerGate

/-- The gate's synthetic blocker tail belongs to the canonical compact floor
carrier used by the exact-orbit extension. -/
theorem blockerTail_mem_punishmentFloorForwardCarrier
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (gate : FinFourChargedSoloBlockerGate reward witness minimumDebt charge
      owner blocker) :
    finFourSoloBlockerTail reward gate.source.1 owner blocker
        (gate.hazard true).toReal ∈
      quittingPunishmentFloorForwardCarrier reward := by
  have hsourceBox := quittingTerminalSemanticCarrier_mem_box reward gate.source
    (abs_reward_le_quittingRewardBound reward) gate.source_mem
  constructor
  · intro who
    exact (neg_quittingRewardBound_le_quittingPunishmentValue reward who).trans
      (gate.blocker_tail_floor who)
  · intro who
    by_cases hwho : who = blocker
    · subst who
      calc
        finFourSoloBlockerTail reward gate.source.1 owner blocker
            (gate.hazard true).toReal blocker =
            finFourSoloBlockerThreshold reward owner blocker
              (gate.hazard true).toReal := by
          simp [finFourSoloBlockerTail]
        _ ≤ gate.source.1 blocker := gate.threshold_le_tail
        _ ≤ quittingRewardBound reward := hsourceBox.1.2 blocker
    · simpa only [finFourSoloBlockerTail, Function.update_of_ne hwho] using
        hsourceBox.1.2 who

/-- The literal first root of every gate extends to an exact infinite floor
orbit without changing the source tail or the selected root. -/
theorem exists_anchoredExactOrbit
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (gate : FinFourChargedSoloBlockerGate reward witness minimumDebt charge
      owner blocker) :
    ∃ orbit : QuittingPunishmentFloorInfiniteOrbit reward,
      orbit.value 0 = finFourSoloBlockerTail reward gate.source.1 owner blocker
          (gate.hazard true).toReal ∧
        orbit.roots 0 = gate.root := by
  exact exists_quittingPunishmentFloorInfiniteOrbit_anchored
    (finFourSoloBlockerTail reward gate.source.1 owner blocker
      (gate.hazard true).toReal) gate.root
      gate.blockerTail_mem_punishmentFloorForwardCarrier
      gate.blocker_tail_floor gate.blocker_tail_exact

private theorem root_eq_soloMixedRoot
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (gate : FinFourChargedSoloBlockerGate reward witness minimumDebt charge
      owner blocker) :
    gate.root = quittingSoloMixedRoot owner gate.hazard := by
  rw [gate.root_eq_solo]
  funext who
  by_cases hwho : who = owner
  · subst who
    simp [quittingSoloStationaryRoot, quittingSoloMixedRoot]
  · simp [quittingSoloStationaryRoot, quittingSoloMixedRoot,
      quittingAllContinueRoot, Function.update_of_ne hwho]

/-- **Actual gate to premium-or-repayment.**  The maximizing blocker selected
by the off-minimum gate receives the compact uniform gap.  Hence either its
pair row has a fixed premium, or every exact floor orbit retaining the gate's
literal first row repays a fixed amount in that blocker coordinate. -/
theorem pairPremium_or_every_exactRepayment
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (gate : FinFourChargedSoloBlockerGate reward witness minimumDebt charge
      owner blocker)
    (hcharge : 0 < charge) :
    ∃ gap : ℝ, 0 < gap ∧
      (quittingSingletonCollisionReward reward owner blocker -
            quittingSoloReward reward owner blocker ≥ gap / 2 ∨
        ∀ orbit : QuittingPunishmentFloorInfiniteOrbit reward,
          orbit.value 0 = finFourSoloBlockerTail reward gate.source.1
              owner blocker (gate.hazard true).toReal →
          orbit.roots 0 = gate.root →
          orbit.value 1 blocker =
              (1 - (gate.hazard true).toReal) *
                  quittingSoloReward reward blocker blocker +
                (gate.hazard true).toReal *
                  quittingSingletonCollisionReward reward owner blocker ∧
            ∃ limit : Payoff (Fin 4),
              (∀ who, Tendsto (fun time => orbit.value time who) atTop
                (nhds (limit who))) ∧
              charge / 8 * gap / 2 ≤
                limit blocker - orbit.value 1 blocker ∧
              ∃ time, 1 ≤ time ∧
                charge / 8 * gap / 4 ≤
                  orbit.value time blocker - orbit.value 1 blocker) := by
  let M := finFourOffMinimumRewardBound reward
  have hM : 0 < M := finFourOffMinimumRewardBound_pos reward
  have hnot := witness.not_exists_uniformEquilibriumPayoff
  obtain ⟨residual⟩ :=
    nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff
      reward (abs_reward_le_finFourOffMinimumRewardBound reward) hnot
  let alpha := charge / 8
  let beta := 1 - witness.terminalGap / (4 * M)
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    positivity
  have hab : alpha ≤ beta := by
    exact gate.charge_le_rate.trans gate.rate_le
  have hbeta : beta ≤ 1 := by
    dsimp only [beta]
    have hratio : 0 < witness.terminalGap / (4 * M) :=
      div_pos witness.terminalGap_pos (mul_pos (by norm_num) hM)
    linarith
  obtain ⟨gap, hgap, huniform⟩ :=
    residual.exists_pos_uniformSoloBlockerGap hnot halpha hab hbeta
  refine ⟨gap, hgap, ?_⟩
  have hrateMem : (gate.hazard true).toReal ∈ Set.Icc alpha beta :=
    ⟨gate.charge_le_rate, gate.rate_le⟩
  have hgapMax := huniform owner (gate.hazard true).toReal hrateMem
  obtain ⟨other, hotherNe, hotherMax⟩ :=
    exists_finFourSoloBlockerGain_eq_max reward owner
      (gate.hazard true).toReal
  have hotherLe := gate.blocker_maximizes_joining_gap other hotherNe
  have hgain : gap ≤ finFourSoloBlockerGain reward owner blocker
      (gate.hazard true).toReal := by
    calc
      gap ≤ finFourSoloBlockerMax reward owner
          (gate.hazard true).toReal := hgapMax
      _ = finFourSoloBlockerGain reward owner other
          (gate.hazard true).toReal := hotherMax.symm
      _ = finFourSoloJoiningGap reward owner other
          (gate.hazard true).toReal := by
        rfl
      _ ≤ finFourSoloJoiningGap reward owner blocker
          (gate.hazard true).toReal := hotherLe
      _ = finFourSoloBlockerGain reward owner blocker
          (gate.hazard true).toReal := by
        rfl
  have hrateLtOne : (gate.hazard true).toReal < 1 := by
    have hratio : 0 < witness.terminalGap / (4 * M) :=
      div_pos witness.terminalGap_pos (mul_pos (by norm_num) hM)
    calc
      (gate.hazard true).toReal ≤
          1 - witness.terminalGap / (4 * M) := by
        simpa only [M] using gate.rate_le
      _ < 1 := by linarith
  have htail :
      finFourSoloBlockerTail reward gate.source.1 owner blocker
          (gate.hazard true).toReal blocker =
        (((1 - (gate.hazard true).toReal) *
              quittingSoloReward reward blocker blocker +
            (gate.hazard true).toReal *
              quittingSingletonCollisionReward reward owner blocker) -
          (gate.hazard true).toReal *
            quittingSoloReward reward owner blocker) /
          (1 - (gate.hazard true).toReal) := by
    simp only [finFourSoloBlockerTail, Function.update_self]
    rfl
  have hsplit := chargedSoloBlocker_pairPremium_or_every_exactRepayment
    witness
    (finFourSoloBlockerTail reward gate.source.1 owner blocker
      (gate.hazard true).toReal)
    owner blocker gate.owner_ne_blocker.symm gate.hazard halpha hgap
      gate.charge_le_rate hrateLtOne hgain htail
  rcases hsplit with hpremium | hrepayment
  · exact Or.inl hpremium
  · right
    intro orbit horbitValue horbitRoot
    apply hrepayment orbit horbitValue
    rw [horbitRoot]
    exact gate.root_eq_soloMixedRoot

end FinFourChargedSoloBlockerGate

end GameTheory
