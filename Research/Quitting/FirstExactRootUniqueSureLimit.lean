/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedWitnessRegimes

/-!
# Unique-sure limit of a positive-debt exact-root prefix

This is the finite-dimensional core of the vanishing-survival arm.  It keeps
the semantic debt vector explicit: a positive total floor and the canonical
opponent-survival upper bounds rule out two sure quitters.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- At a zero-survival root, a nonnegative prefix-debt vector with a
positive total floor and the exact semantic survival bounds has a unique sure
quitter.  Every outsider debt is zero, so the unique sure quitter carries the
entire floor. -/
theorem uniqueSureQuitter_of_positive_prefixDebtFloor
    (root : ι → PMF Bool)
    (sourceDebt prefixDebt : ι → ℝ) {floor : ℝ}
    (hfloor : 0 < floor)
    (hsurvival : quittingStationaryContinueMass root = 0)
    (hprefixNonneg : ∀ player, 0 ≤ prefixDebt player)
    (hprefixBound : ∀ player,
      prefixDebt player ≤
        quittingRootOpponentContinueMass root player * sourceDebt player)
    (htotalFloor : floor ≤ ∑ player, prefixDebt player) :
    ∃ owner : ι,
      root owner = PMF.pure true ∧
      (∀ other, other ≠ owner → root other ≠ PMF.pure true) ∧
      (∀ other, other ≠ owner → prefixDebt other = 0) ∧
      floor ≤ prefixDebt owner := by
  obtain ⟨owner, howner⟩ :=
    quittingRootHasSureQuitter_of_stationaryContinueMass_eq_zero root hsurvival
  have hzero_of_other_sure : ∀ {first second : ι}, first ≠ second →
      root second = PMF.pure true →
      quittingRootOpponentContinueMass root first = 0 := by
    intro first second hne hsecond
    have hle := quittingRootOpponentContinueMass_le_continueProbability_of_ne
      root hne.symm
    rw [hsecond] at hle
    simp only [PMF.pure_apply, Bool.false_eq_true, ↓reduceIte,
      ENNReal.toReal_zero] at hle
    exact le_antisymm hle (quittingRootOpponentContinueMass_nonneg root first)
  have hunique : ∀ other, other ≠ owner → root other ≠ PMF.pure true := by
    intro other hne hother
    have hallZero : ∀ player, prefixDebt player = 0 := by
      intro player
      let sure : ι := if player = owner then other else owner
      have hsureNe : player ≠ sure := by
        dsimp only [sure]
        split_ifs with hp
        · simpa [hp] using hne.symm
        · exact hp
      have hsure : root sure = PMF.pure true := by
        dsimp only [sure]
        split_ifs
        · exact hother
        · exact howner
      have hmass := hzero_of_other_sure hsureNe hsure
      have hupper := hprefixBound player
      rw [hmass, zero_mul] at hupper
      exact le_antisymm hupper (hprefixNonneg player)
    have hsumZero : (∑ player, prefixDebt player) = 0 := by
      simp [hallZero]
    rw [hsumZero] at htotalFloor
    linarith
  have houtside : ∀ other, other ≠ owner → prefixDebt other = 0 := by
    intro other hne
    have hmass := hzero_of_other_sure hne howner
    have hupper := hprefixBound other
    rw [hmass, zero_mul] at hupper
    exact le_antisymm hupper (hprefixNonneg other)
  have hsumOwner : (∑ player, prefixDebt player) = prefixDebt owner := by
    rw [Finset.sum_eq_single owner]
    · intro other _ hne
      exact houtside other hne
    · simp
  exact ⟨owner, howner, hunique, houtside, hsumOwner ▸ htotalFloor⟩

/-- Semantic-pair adapter for the limit theorem.  The debt nonnegativity and
survival bounds are discharged from actual carrier membership and exact root
Nash, rather than supplied as standalone scalar assumptions. -/
theorem uniqueSureQuitter_of_terminalSemanticPrefix_positiveDebtFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) {floor : ℝ}
    (hfloor : 0 < floor)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hsurvival : quittingStationaryContinueMass root = 0)
    (htotalFloor : floor ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPrefix reward root pair)) :
    ∃ owner : ι,
      root owner = PMF.pure true ∧
      (∀ other, other ≠ owner → root other ≠ PMF.pure true) ∧
      (∀ other, other ≠ owner →
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) other = 0) ∧
      floor ≤ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) owner := by
  have hprefixCarrier :=
    quittingTerminalSemanticPrefix_mem_carrier reward root pair hpair
  apply uniqueSureQuitter_of_positive_prefixDebtFloor root
    (fun player ↦ quittingTerminalSemanticDebt pair player)
    (fun player ↦ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPrefix reward root pair) player)
    hfloor hsurvival
  · exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      hprefixCarrier
  · intro player
    rw [quittingTerminalSemanticDebt_prefix_eq_blockAct reward pair root player
      (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair player)
      hnash]
    exact Math.SurvivalWeightedObstruction.Block.act_le_survival_mul_debt
      (quittingTerminalSemanticDebtBlock reward pair root player) ()
      (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair player)
  · exact htotalFloor

/-- Sequence-facing form of the unique-sure conclusion.  Coordinatewise
convergence of the actual prefixed semantic debts transports the zero outsider
debts back to the finite sources, while the owner eventually retains half the
strict limiting floor. -/
theorem eventually_ownerDebt_and_outsiderDebt_tendsto_zero_of_uniqueSureLimit
    (root : ι → PMF Bool)
    (sourceDebt limitDebt : ι → ℝ)
    (prefixDebt : ℕ → ι → ℝ) {floor : ℝ}
    (hfloor : 0 < floor)
    (hsurvival : quittingStationaryContinueMass root = 0)
    (hlimitNonneg : ∀ player, 0 ≤ limitDebt player)
    (hlimitBound : ∀ player,
      limitDebt player ≤
        quittingRootOpponentContinueMass root player * sourceDebt player)
    (htotalFloor : floor ≤ ∑ player, limitDebt player)
    (hprefixTendsto : ∀ player,
      Tendsto (fun index ↦ prefixDebt index player) atTop
        (nhds (limitDebt player))) :
    ∃ owner : ι,
      root owner = PMF.pure true ∧
      (∀ other, other ≠ owner → root other ≠ PMF.pure true) ∧
      (∀ other, other ≠ owner →
        Tendsto (fun index ↦ prefixDebt index other) atTop (nhds 0)) ∧
      ∀ᶠ index in atTop, floor / 2 ≤ prefixDebt index owner := by
  obtain ⟨owner, howner, hunique, houtside, hownerFloor⟩ :=
    uniqueSureQuitter_of_positive_prefixDebtFloor root sourceDebt
      limitDebt hfloor hsurvival hlimitNonneg hlimitBound htotalFloor
  refine ⟨owner, howner, hunique, ?_, ?_⟩
  · intro other hne
    simpa [houtside other hne] using hprefixTendsto other
  · have hhalf : floor / 2 < limitDebt owner := by linarith
    exact ((tendsto_order.1 (hprefixTendsto owner)).1 _ hhalf).mono fun _ hlt => hlt.le

end GameTheory
