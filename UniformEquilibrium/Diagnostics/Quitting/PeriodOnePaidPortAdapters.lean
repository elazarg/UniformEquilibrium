/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.PeriodOneOffMinimumPaidPort
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Quitting.Cycles.OwnerSingletonCyclicConcentration

/-! # Terminal-law and semantic-cluster adapters for period-one paid ports -/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℕ → ℝ} {source : PeriodOneVanishingHazardSource reward error}

omit [Nontrivial ι] in
/-- Quit at date zero from stationary roots converging coordinatewise to all
Continue has terminal law converging to the quitter's singleton. -/
theorem stationaryProfile_quitNow_terminalOutcomeMass_tendsto_singleton
    (root : ℕ → ι → PMF Bool) (payer : ι)
    (hcontinue : ∀ who, Tendsto (fun index ↦ (root index who false).toReal)
      atTop (nhds 1)) :
    Tendsto (fun index ↦ quittingTerminalOutcomeMass reward
      (Function.update (quittingStationaryProfile reward (root index)) payer
        (quittingPureTimeBehaviorStrategy reward payer (some 0)))) atTop
      (nhds (quittingSingletonTerminalOutcomeMass payer)) := by
  have hopponent : Tendsto (fun index ↦ quittingRootOpponentContinueMass
      (root index) payer) atTop (nhds 1) := by
    simp_rw [quittingRootOpponentContinueMass,
      quittingStationaryContinueMass_eq_prod_continueProbability]
    have hprod := tendsto_finsetProd (M := ℝ) (α := ℕ)
      (f := fun who index ↦
        ((Function.update (root index) payer (PMF.pure false)) who false).toReal)
      (x := atTop) (a := fun _ ↦ 1) Finset.univ (fun who _ ↦ by
        by_cases hwho : who = payer
        · subst who
          simp
        · simpa [Function.update_of_ne hwho] using hcontinue who)
    simpa using hprod
  have hliveRoot (index : ℕ) :
      quittingProfileLiveRoot reward
        (Function.update (quittingStationaryProfile reward (root index)) payer
          (quittingPureTimeBehaviorStrategy reward payer (some 0))) 0 =
        Function.update (root index) payer (PMF.pure true) := by
    rw [congrFun (quittingProfileLiveRoot_update_eq_rootSequenceUpdate reward
      (quittingStationaryProfile reward (root index)) payer
      (quittingPureTimeBehaviorStrategy reward payer (some 0))) 0]
    funext who
    simp [quittingRootSequenceUpdate, quittingBehaviorLiveHazard,
      quittingPureTimeBehaviorStrategy, quittingProfileLiveRoot_stationary]
  rw [tendsto_pi_nhds]
  intro outcome
  cases outcome with
  | none =>
      simpa [quittingTerminalOutcomeMass, quittingSingletonTerminalOutcomeMass] using
        tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun index ↦
          (quittingLiveMassLimit_update_pureTimeBehaviorStrategy_some_eq_zero
            reward (quittingStationaryProfile reward (root index)) payer 0).symm)
  | some terminal =>
      by_cases hpayer : payer ∈ terminal.val
      · rw [show quittingSingletonTerminalOutcomeMass payer (some terminal) =
            if terminal = quittingSingletonTerminal payer then 1 else 0 by
          rfl]
        by_cases hterminal : terminal = quittingSingletonTerminal payer
        · subst terminal
          rw [if_pos rfl]
          simp_rw [quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at reward
            (quittingStationaryProfile reward (root _)) payer 0
            (quittingSingletonTerminal payer)
            (Finset.mem_singleton_self payer)]
          simp_rw [quittingStageCoalitionMass, quittingLiveMass_zero, one_mul,
            quittingLiveRowCoalitionMass_eq_rootCoalitionMass, hliveRoot]
          change Tendsto (fun index ↦ quittingRootCoalitionMass
            (Function.update (root index) payer (PMF.pure true))
            {payer}) atTop (nhds 1)
          simp_rw [quittingRootCoalitionMass_singleton_eq_opponentContinue_mul_quit]
          simpa [quittingRootOpponentContinueMass]
            using hopponent
        · simp only [if_neg hterminal]
          simp_rw [quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at reward
            (quittingStationaryProfile reward (root _)) payer 0 terminal hpayer]
          have hother : ∃ other ∈ terminal.val, other ≠ payer := by
            by_contra hnot
            push Not at hnot
            apply hterminal
            apply Subtype.ext
            exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hpayer, hnot⟩
          obtain ⟨other, hotherMem, hotherNe⟩ := hother
          have hupper : Tendsto
              (fun index ↦ 1 - (root index other false).toReal)
              atTop (nhds 0) := by
            simpa using (hcontinue other).const_sub 1
          have ht : Tendsto (fun index ↦ quittingStageCoalitionMass reward
              (Function.update (quittingStationaryProfile reward (root index)) payer
                (quittingPureTimeBehaviorStrategy reward payer (some 0))) 0 terminal)
              atTop (nhds 0) :=
            tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
            hupper
            (fun index ↦ quittingStageCoalitionMass_nonneg reward _ 0 terminal)
            (fun index ↦ by
              rw [show (1 - (root index other false).toReal) =
                  (root index other true).toReal by
                rw [pmfBool_false_toReal]
                ring]
              rw [quittingStageCoalitionMass, quittingLiveMass_zero, one_mul,
                quittingLiveRowCoalitionMass_eq_rootCoalitionMass, hliveRoot]
              simpa [hotherNe] using
                quittingRootCoalitionMass_le_quitProbability_of_mem
                  (Function.update (root index) payer (PMF.pure true))
                  terminal.val (marked := other) hotherMem)
          simpa using ht
      · simp_rw [quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before reward
          (quittingStationaryProfile reward (root _)) payer 0 terminal hpayer]
        have hne : terminal ≠ quittingSingletonTerminal payer := by
          intro heq
          subst terminal
          exact hpayer (Finset.mem_singleton_self payer)
        simp [quittingSingletonTerminalOutcomeMass, hne]

namespace PeriodOneNormalizedSourceLimit

/-- The generic stationary-root result applied to a literal retained source. -/
theorem subsetProfile_quitNow_terminalOutcomeMass_tendsto_singleton
    (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι) (payer : ι) :
    Tendsto (fun index ↦ quittingTerminalOutcomeMass reward
      (Function.update (limit.subsetProfile retained index) payer
        (quittingPureTimeBehaviorStrategy reward payer (some 0)))) atTop
      (nhds (quittingSingletonTerminalOutcomeMass payer)) := by
  simpa only [subsetProfile] using
    stationaryProfile_quitNow_terminalOutcomeMass_tendsto_singleton
      (reward := reward) (limit.subsetRoot retained) payer
      (fun who ↦ (limit.subsetRoot_continueLimits retained who).2.1)

omit [Nontrivial ι] in
/-- The actual final Quit-now child of a literal paid-cap chain has terminal
law converging to the fixed payer's singleton. -/
theorem LiteralStationaryPaidCapChain.finalTarget_terminalOutcomeMass_tendsto_singleton
    {start : ℕ → (quittingGame reward).BehaviorProfile} {steps : ℕ}
    (chain : LiteralStationaryPaidCapChain start steps) :
    Tendsto (fun index ↦ quittingTerminalOutcomeMass reward
      (chain.profile steps index)) atTop
      (nhds (quittingSingletonTerminalOutcomeMass chain.port.payer)) := by
  apply (stationaryProfile_quitNow_terminalOutcomeMass_tendsto_singleton
    (reward := reward) chain.lastRoot chain.port.payer
    chain.lastRoot_continue_tendsto).congr'
  filter_upwards [chain.eventually_chain] with index hchain
  have hstep : steps - 1 < steps := Nat.sub_lt chain.steps_pos zero_lt_one
  have hlast : steps - 1 + 1 = steps := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    chain.steps_pos.ne')
  have hedge := (hchain (steps - 1) hstep).1
  rw [hlast] at hedge
  rw [hedge, chain.last_source_eq index, chain.last_mover_eq]
  simp

end PeriodOneNormalizedSourceLimit

omit [Nontrivial ι] in
/-- Every convergent semantic subsequence of a paid port has the singleton
cap coordinate, and every point of its global minimum face has the packet's
full cap gap above that cluster coordinate. -/
theorem StationaryOffMinimumQuitNowPort.cluster_cap_eq_and_minimumFace_gap
    {root : ℕ → ι → PMF Bool} (port : StationaryOffMinimumQuitNowPort reward root)
    (select : ℕ → ℕ) (hselect : StrictMono select)
    (cluster : QuittingTerminalSemanticPair ι)
    (hcluster : Tendsto (fun index ↦ quittingTerminalSemanticPair reward
      (quittingStationaryProfile reward (root (select index)))) atTop (nhds cluster)) :
    cluster.2 port.payer = quittingSoloReward reward port.payer port.payer ∧
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum candidate =
          quittingTerminalSemanticDebtSum port.minimum →
        quittingTerminalSemanticDebtSum port.minimum ≤
          candidate.2 port.payer - cluster.2 port.payer := by
  have hcapCluster : Tendsto (fun index ↦
      quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward (root (select index))) port.payer)
      atTop (nhds (cluster.2 port.payer)) := by
    have hprojection := (continuous_apply port.payer).tendsto cluster.2 |>.comp
      (continuous_snd.tendsto cluster |>.comp hcluster)
    change Tendsto (fun index ↦
      (quittingTerminalSemanticPair reward
        (quittingStationaryProfile reward (root (select index)))).2 port.payer)
      atTop (nhds (cluster.2 port.payer))
    convert hprojection using 1
    funext index
    rfl
  have hcapSolo := port.cap_tendsto.comp hselect.tendsto_atTop
  have heq : cluster.2 port.payer = quittingSoloReward reward port.payer port.payer :=
    tendsto_nhds_unique hcapCluster hcapSolo
  refine ⟨heq, ?_⟩
  intro candidate hcandidate hminimum
  rw [heq]
  have hmargin := minimumTerminalSemantic_singletonMargin candidate hcandidate
    (fun other hother ↦ by rw [hminimum]; exact port.minimum_le other hother)
    (by rw [hminimum]; exact port.minimum_pos) port.payer
  rw [← hminimum]
  change quittingTerminalSemanticDebtSum candidate ≤
    candidate.2 port.payer - reward (quittingSingletonTerminal port.payer) port.payer
  exact hmargin

end GameTheory
