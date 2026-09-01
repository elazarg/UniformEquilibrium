/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.MinimumFiberSupportDrop
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualReachPaidFirstDisagreement

/-!
# Quantitative paid rows along Fin4 full-replacement clusters

A supplied positive-minimum tangent frontier, active mover, and compact
full-replacement cluster select one fixed nonmover.  Along the cluster's
literal actual target subsequence, that observer eventually has enough
unrestricted continuation debt to produce a paid first-disagreement row with
actual stopping-law support and explicit one-sided and joint reach floors.

This is a static endpoint compiler.  The full replacement is horizontal, not
chronological, and the result supplies no paid-port consumer, renewal, Nash
profile, or uniform-equilibrium conclusion.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

namespace QuittingPositiveMinimumDebtTangentFamily

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}

/-- One fixed endpoint observer and an eventual family of quantitative paid
rows on the supplied full-replacement subsequence.  The row may vary with the
rank; the observer and every displayed constant do not. -/
structure FinFourFullReplacementQuantitativePaidPort
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (endpoint : FullReplacementCluster frontier mover) (M : ℝ) where
  observer : Fin 4
  observer_ne_mover : observer ≠ mover.1
  clusterDebt_ge_third :
    quittingTerminalSemanticDebtSum frontier.base / 3 ≤
      quittingTerminalSemanticDebt endpoint.cluster observer
  startRank : ℕ
  targetDebt_ge_quarter : ∀ rank, startRank ≤ rank →
    quittingTerminalSemanticDebt
        (frontier.fullReplacementPair mover (endpoint.subseq rank)) observer ≥
      quittingTerminalSemanticDebtSum frontier.base / 4
  row : ∀ rank (_ : startRank ≤ rank),
    QuittingPaidFirstDisagreementRow reward
      (frontier.fullReplacementProfile mover (endpoint.subseq rank))
      observer (quittingTerminalSemanticDebtSum frontier.base / 16)
  row_sourceWitness_mem : ∀ rank (hrank : startRank ≤ rank),
    (row rank hrank).sourceWitness ∈
      (quittingBehaviorStoppingLaw reward
        ((frontier.fullReplacementProfile mover (endpoint.subseq rank)) observer)).support
  ownSurvival_floor : ∀ rank (hrank : startRank ≤ rank),
    quittingTerminalSemanticDebtSum frontier.base / 4 ≤
      4 * M * quittingHazardSurvival
        (quittingBehaviorLiveHazard reward
          ((frontier.fullReplacementProfile mover (endpoint.subseq rank)) observer))
        (row rank hrank).start
  opponentReach_floor : ∀ rank (hrank : startRank ≤ rank),
    quittingTerminalSemanticDebtSum frontier.base / 4 ≤
      8 * M * (row rank hrank).liveMass
  jointReach_floor : ∀ rank (hrank : startRank ≤ rank),
    (quittingTerminalSemanticDebtSum frontier.base / 4) ^ 2 ≤
      32 * M * M * quittingSurvivalPrefix
        (quittingProfileLiveRoot reward
          (frontier.fullReplacementProfile mover (endpoint.subseq rank)))
        (row rank hrank).start

/-- The target profiles retain the frontier's literal source, subsequence,
mover, and selected full-replacement strategy. -/
theorem fullReplacementProfile_subseq_eq_update
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (endpoint : FullReplacementCluster frontier mover) (rank : ℕ) :
    frontier.fullReplacementProfile mover (endpoint.subseq rank) =
      Function.update (frontier.source (endpoint.subseq rank)) mover.1
        (frontier.replacement mover (endpoint.subseq rank)) := rfl

/-- Every supplied Fin4 full-replacement cluster has a fixed nonmover whose
actual target profiles eventually carry quantitative paid rows. -/
theorem nonempty_finFourFullReplacementQuantitativePaidPort
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (endpoint : FullReplacementCluster frontier mover) (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (FinFourFullReplacementQuantitativePaidPort frontier mover endpoint M) := by
  let debt : Fin 4 → ℝ := fun who ↦
    quittingTerminalSemanticDebt endpoint.cluster who
  obtain ⟨other, hother⟩ :=
    Fintype.exists_ne_of_one_lt_card (by decide : 1 < Fintype.card (Fin 4)) mover.1
  have hopponents : (Finset.univ.erase mover.1).Nonempty := by
    exact ⟨other, Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩⟩
  obtain ⟨observer, hobserverMem, hobserverMax⟩ :=
    Finset.exists_max_image (Finset.univ.erase mover.1) debt hopponents
  have hobserverNe : observer ≠ mover.1 := (Finset.mem_erase.mp hobserverMem).1
  have hsumLe :
      (∑ who ∈ Finset.univ.erase mover.1, debt who) ≤ 3 * debt observer := by
    have hbound := (Finset.univ.erase mover.1).sum_le_card_nsmul
      debt (debt observer) (fun who hwho ↦ hobserverMax who hwho)
    simpa [nsmul_eq_mul] using hbound
  have hmoverZero : debt mover.1 = 0 := endpoint.mover_debt_eq_zero
  have hsumErase :
      (∑ who ∈ Finset.univ.erase mover.1, debt who) =
        quittingTerminalSemanticDebtSum endpoint.cluster := by
    change (∑ who ∈ Finset.univ.erase mover.1, debt who) =
      ∑ who, debt who
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ mover.1), hmoverZero, add_zero]
  have hminimum :
      quittingTerminalSemanticDebtSum frontier.base ≤
        quittingTerminalSemanticDebtSum endpoint.cluster :=
    frontier.base_minimum endpoint.cluster endpoint.cluster_mem
  have hclusterThird :
      quittingTerminalSemanticDebtSum frontier.base / 3 ≤ debt observer := by
    rw [hsumErase] at hsumLe
    linarith
  have hdebtTendsto : Tendsto (fun rank ↦
      quittingTerminalSemanticDebt
        (frontier.fullReplacementPair mover (endpoint.subseq rank)) observer)
      atTop (nhds (debt observer)) :=
    (continuous_quittingTerminalSemanticDebt observer).tendsto endpoint.cluster
      |>.comp endpoint.fullReplacement_tendsto
  have hquarterLt :
      quittingTerminalSemanticDebtSum frontier.base / 4 < debt observer := by
    linarith [frontier.base_positive, hclusterThird]
  have heventually : ∀ᶠ rank in atTop,
      quittingTerminalSemanticDebtSum frontier.base / 4 <
        quittingTerminalSemanticDebt
          (frontier.fullReplacementPair mover (endpoint.subseq rank)) observer :=
    hdebtTendsto.eventually_const_lt hquarterLt
  rw [eventually_atTop] at heventually
  obtain ⟨startRank, hstartRank⟩ := heventually
  have hrows : ∀ rank (hrank : startRank ≤ rank),
      ∃ row : QuittingPaidFirstDisagreementRow reward
          (frontier.fullReplacementProfile mover (endpoint.subseq rank))
          observer (quittingTerminalSemanticDebtSum frontier.base / 16),
        row.sourceWitness ∈
            (quittingBehaviorStoppingLaw reward
              ((frontier.fullReplacementProfile mover
                (endpoint.subseq rank)) observer)).support ∧
        quittingTerminalSemanticDebtSum frontier.base / 4 ≤
          4 * M * quittingHazardSurvival
            (quittingBehaviorLiveHazard reward
              ((frontier.fullReplacementProfile mover
                (endpoint.subseq rank)) observer)) row.start ∧
        quittingTerminalSemanticDebtSum frontier.base / 4 ≤
          8 * M * row.liveMass ∧
        (quittingTerminalSemanticDebtSum frontier.base / 4) ^ 2 ≤
          32 * M * M * quittingSurvivalPrefix
            (quittingProfileLiveRoot reward
              (frontier.fullReplacementProfile mover (endpoint.subseq rank)))
            row.start := by
    intro rank hrank
    have hdebt : quittingTerminalSemanticDebtSum frontier.base / 4 ≤
        quittingContinuationBestResponseValue reward
            (frontier.fullReplacementProfile mover (endpoint.subseq rank)) observer -
          quittingTerminalPayoff reward
            (frontier.fullReplacementProfile mover (endpoint.subseq rank)) observer := by
      exact (hstartRank rank hrank).le
    have hpositive : 0 < quittingTerminalSemanticDebtSum frontier.base / 4 := by
      exact div_pos frontier.base_positive (by norm_num)
    have hrow := positiveDebt_exists_actualJointReach_paidRow_mem_support
      reward (frontier.fullReplacementProfile mover (endpoint.subseq rank)) observer
      M (quittingTerminalSemanticDebtSum frontier.base / 4)
      hreward hpositive hdebt
    have hgain : quittingTerminalSemanticDebtSum frontier.base / 4 / 4 =
        quittingTerminalSemanticDebtSum frontier.base / 16 := by ring
    rw [hgain] at hrow
    simpa [pow_two] using hrow
  let selectedRow : ∀ rank (hrank : startRank ≤ rank),
      QuittingPaidFirstDisagreementRow reward
        (frontier.fullReplacementProfile mover (endpoint.subseq rank))
        observer (quittingTerminalSemanticDebtSum frontier.base / 16) :=
    fun rank hrank ↦ (hrows rank hrank).choose
  have hselected := fun rank hrank ↦ (hrows rank hrank).choose_spec
  refine ⟨{
    observer := observer
    observer_ne_mover := hobserverNe
    clusterDebt_ge_third := hclusterThird
    startRank := startRank
    targetDebt_ge_quarter := fun rank hrank ↦ (hstartRank rank hrank).le
    row := selectedRow
    row_sourceWitness_mem := fun rank hrank ↦ (hselected rank hrank).1
    ownSurvival_floor := fun rank hrank ↦ (hselected rank hrank).2.1
    opponentReach_floor := fun rank hrank ↦ (hselected rank hrank).2.2.1
    jointReach_floor := fun rank hrank ↦ (hselected rank hrank).2.2.2
  }⟩

/-- A positive minimum terminal-semantic debt source supplies one tangent
frontier, active mover, full-replacement cluster, and its quantitative paid
port.  The existential choices are branch-local; no downstream consumption
or common residual across different selected objects is asserted. -/
theorem nonempty_finFourFullReplacementQuantitativePaidPort_of_positiveMinimum
    (hminimum : HasPositiveMinimumTerminalSemanticDebt reward) (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (Σ frontier : QuittingPositiveMinimumDebtTangentFamily reward,
      Σ mover : {who // who ∈ frontier.positiveDebtSupport},
        Σ endpoint : FullReplacementCluster frontier mover,
          FinFourFullReplacementQuantitativePaidPort frontier mover endpoint M) := by
  obtain ⟨frontier⟩ := nonempty_positiveMinimumDebtTangentFamily hminimum
  obtain ⟨who, hwho⟩ := frontier.positiveDebtSupport_nonempty
  let mover : {who // who ∈ frontier.positiveDebtSupport} := ⟨who, hwho⟩
  obtain ⟨endpoint⟩ := frontier.exists_fullReplacementEndpointCluster mover
  obtain ⟨port⟩ := nonempty_finFourFullReplacementQuantitativePaidPort
    frontier mover endpoint M hreward
  exact ⟨⟨frontier, mover, endpoint, port⟩⟩

end QuittingPositiveMinimumDebtTangentFamily

end GameTheory
