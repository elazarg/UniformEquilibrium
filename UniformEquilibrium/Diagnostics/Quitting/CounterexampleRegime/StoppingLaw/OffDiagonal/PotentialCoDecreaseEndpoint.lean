/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.PositiveTotalSlopeEndpoint

/-!
# Full-reset endpoints of a flat potential co-decrease

Every selected stopping-law reset ray has a compact full-reset endpoint
cluster, without any sign assumption on its total tangent slope.  Convexity
of opponents' debt coordinates makes the limiting tangent a coordinatewise
lower bound for the full endpoint debt change, while own-coordinate affinity
makes the mover coordinate exact.  The retained vanishing-regret endpoint
selection makes the mover's debt zero at every full-reset cluster,
independently of total slope and of the minimum-fiber question.

If the tangent column is flat, has no entry into the inactive debt support,
and has the exact vanishing-regret diagonal, then any such endpoint cluster
which remains on the minimum-total-debt fiber has exactly the tangent debt
change.  No inactive debt then appears, and the positive debt support
strictly decreases.  In the potential co-decrease arm, the stored second
debtor also strictly decreases.

The minimum-fiber hypothesis is essential.  This module does not consume the
positive convexity defect of an off-minimum endpoint.  Repeating the rank
descent requires a new base-parameterized extraction after each endpoint.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingCounterexampleStoppingLawFrontier

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {regime : QuittingCounterexampleRegime reward}

/-- Compact full-reset endpoint data for an arbitrary supplied active mover.
Unlike `PositiveTotalSlopeEndpointCluster`, this structure has no positive
total-slope or total-debt-separation field. -/
structure FullResetEndpointCluster
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) where
  cluster : QuittingTerminalSemanticPair ι
  subseq : ℕ → ℕ
  cluster_mem : cluster ∈ quittingTerminalSemanticCarrier reward
  subseq_strictMono : StrictMono subseq
  sourceSubseq_strictMono : StrictMono (frontier.subseq ∘ subseq)
  fullReset_tendsto : Tendsto (fun rank ↦
      frontier.fullResetPair mover (subseq rank)) atTop (nhds cluster)
  coordinate_excess : ∀ observer,
    frontier.tangent mover observer ≤
      quittingTerminalSemanticDebtChange frontier.base cluster observer
  mover_excess_eq :
    quittingTerminalSemanticDebtChange frontier.base cluster mover.1 =
      frontier.tangent mover mover.1

/-- Every supplied mover has a compact full-reset endpoint cluster retaining
coordinatewise tangent domination and exact own-coordinate change. -/
theorem exists_fullResetEndpointCluster
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) :
    Nonempty (FullResetEndpointCluster frontier mover) := by
  let endpoint : ℕ → QuittingTerminalSemanticPair ι :=
    fun rank ↦ frontier.fullResetPair mover rank
  have hendpointMem : ∀ rank,
      endpoint rank ∈ quittingTerminalSemanticCarrier reward := by
    intro rank
    exact quittingTerminalSemanticPair_mem_carrier reward
      (frontier.fullResetProfile mover rank)
  obtain ⟨cluster, hcluster, subseq, hsubseq, hendpoint⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).tendsto_subseq
      hendpointMem
  have hsource : Tendsto (fun rank ↦ frontier.sourcePair (subseq rank))
      atTop (nhds frontier.base) := by
    unfold sourcePair
    exact frontier.profiles_tendsto.comp
      ((frontier.subseq_strictMono.comp hsubseq).tendsto_atTop)
  have hcoordinate : ∀ observer,
      frontier.tangent mover observer ≤
        quittingTerminalSemanticDebtChange frontier.base cluster observer := by
    intro observer
    have hleft := (frontier.tangent_tendsto mover observer).comp
      hsubseq.tendsto_atTop
    have hright : Tendsto (fun rank ↦
        quittingTerminalSemanticDebtChange
          (frontier.sourcePair (subseq rank))
          (frontier.fullResetPair mover (subseq rank)) observer)
        atTop (nhds
          (quittingTerminalSemanticDebtChange frontier.base cluster observer)) := by
      unfold quittingTerminalSemanticDebtChange
      exact ((continuous_quittingTerminalSemanticDebt observer).tendsto cluster
        |>.comp hendpoint).sub
          ((continuous_quittingTerminalSemanticDebt observer).tendsto frontier.base
            |>.comp hsource)
    exact le_of_tendsto_of_tendsto hleft hright
      (Eventually.of_forall fun rank ↦
        frontier.normalizedDebtDirection_le_fullResetDebtChange
          mover observer (subseq rank))
  have hmoverEq :
      quittingTerminalSemanticDebtChange frontier.base cluster mover.1 =
        frontier.tangent mover mover.1 := by
    have hleft := (frontier.tangent_tendsto mover mover.1).comp
      hsubseq.tendsto_atTop
    have hright : Tendsto (fun rank ↦
        quittingTerminalSemanticDebtChange
          (frontier.sourcePair (subseq rank))
          (frontier.fullResetPair mover (subseq rank)) mover.1)
        atTop (nhds
          (quittingTerminalSemanticDebtChange frontier.base cluster mover.1)) := by
      unfold quittingTerminalSemanticDebtChange
      exact ((continuous_quittingTerminalSemanticDebt mover.1).tendsto cluster
        |>.comp hendpoint).sub
          ((continuous_quittingTerminalSemanticDebt mover.1).tendsto frontier.base
            |>.comp hsource)
    have heq : (fun rank ↦
        quittingStoppingLawNormalizedDebtDirection reward
          (frontier.profiles (frontier.subseq (subseq rank))) mover.1
          (frontier.bestResponse mover (frontier.subseq (subseq rank)))
          (frontier.lambda (frontier.subseq (subseq rank)))
          (frontier.lambda_pos (frontier.subseq (subseq rank))).le
          (frontier.lambda_le_one (frontier.subseq (subseq rank))) mover.1) =
        (fun rank ↦ quittingTerminalSemanticDebtChange
          (frontier.sourcePair (subseq rank))
          (frontier.fullResetPair mover (subseq rank)) mover.1) := by
      funext rank
      exact frontier.normalizedDebtDirection_self_eq_fullResetDebtChange
        mover (subseq rank)
    change Tendsto (fun rank ↦
      quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq (subseq rank))) mover.1
        (frontier.bestResponse mover (frontier.subseq (subseq rank)))
        (frontier.lambda (frontier.subseq (subseq rank)))
        (frontier.lambda_pos (frontier.subseq (subseq rank))).le
        (frontier.lambda_le_one (frontier.subseq (subseq rank))) mover.1)
      atTop (nhds (frontier.tangent mover mover.1)) at hleft
    rw [heq] at hleft
    exact (tendsto_nhds_unique hleft hright).symm
  refine ⟨⟨cluster, subseq, hcluster, hsubseq,
    frontier.subseq_strictMono.comp hsubseq, ?_, hcoordinate, hmoverEq⟩⟩
  change Tendsto (endpoint ∘ subseq) atTop (nhds cluster)
  exact hendpoint

namespace FullResetEndpointCluster

variable {frontier : QuittingCounterexampleStoppingLawFrontier regime}
  {mover : {who // who ∈ frontier.active}}

/-- On a flat minimum-fiber endpoint, every coordinatewise convexity
inequality is an equality.  The nonnegative coordinate defects have zero
sum. -/
theorem debtChange_eq_tangent_of_flat_of_minimumFiber
    (endpoint : FullResetEndpointCluster frontier mover)
    (hflat : ∑ observer, frontier.tangent mover observer = 0)
    (hminimumFiber :
      quittingTerminalSemanticDebtSum endpoint.cluster =
        quittingTerminalSemanticDebtSum frontier.base) :
    ∀ observer,
      quittingTerminalSemanticDebtChange frontier.base endpoint.cluster observer =
        frontier.tangent mover observer := by
  let defect : ι → ℝ := fun observer ↦
    quittingTerminalSemanticDebtChange frontier.base endpoint.cluster observer -
      frontier.tangent mover observer
  have hdefectNonneg : ∀ observer, 0 ≤ defect observer := by
    intro observer
    dsimp only [defect]
    exact sub_nonneg.mpr (endpoint.coordinate_excess observer)
  have hdefectSum : ∑ observer, defect observer = 0 := by
    dsimp only [defect]
    rw [Finset.sum_sub_distrib]
    unfold quittingTerminalSemanticDebtChange
    rw [Finset.sum_sub_distrib]
    unfold quittingTerminalSemanticDebtSum at hminimumFiber
    rw [hminimumFiber, sub_self, hflat, sub_zero]
  intro observer
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun who _ ↦ hdefectNonneg who)).mp hdefectSum observer
      (Finset.mem_univ observer)
  dsimp only [defect] at hzero
  linarith

/-- Exact vanishing-regret extraction makes the mover's debt vanish at every
full-reset endpoint cluster, independently of total slope or fiber. -/
theorem mover_debt_eq_zero
    (endpoint : FullResetEndpointCluster frontier mover) :
    quittingTerminalSemanticDebt endpoint.cluster mover.1 = 0 := by
  have hchange := endpoint.mover_excess_eq
  have hexactDiagonal := frontier.tangent_diagonal_eq mover
  unfold quittingTerminalSemanticDebtChange at hchange
  linarith

/-- A flat no-entry endpoint on the minimum fiber, with exact mover
diagonal, has positive debt support properly contained in the base active
support. -/
theorem positiveDebtSupport_ssubset_of_exactDiagonal_of_flat_of_noEntry_of_minimumFiber
    (endpoint : FullResetEndpointCluster frontier mover)
    (hflat : ∑ observer, frontier.tangent mover observer = 0)
    (hnoEntry :
      ¬ HasQuittingStoppingLawFlatSupportEntry
        frontier.base frontier.active frontier.tangent)
    (hminimumFiber :
      quittingTerminalSemanticDebtSum endpoint.cluster =
        quittingTerminalSemanticDebtSum frontier.base) :
    (Finset.univ.filter fun who ↦
        0 < quittingTerminalSemanticDebt endpoint.cluster who) ⊂
      frontier.active := by
  have hchange := endpoint.debtChange_eq_tangent_of_flat_of_minimumFiber
    hflat hminimumFiber
  have hmoverZero := endpoint.mover_debt_eq_zero
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro observer hobserver
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hobserver
    by_contra hinactive
    have hbaseNonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward frontier.base_mem observer
    have hbaseZero :
        quittingTerminalSemanticDebt frontier.base observer = 0 := by
      apply le_antisymm
      · exact le_of_not_gt (fun hpositive ↦
          hinactive ((frontier.active_iff observer).2 hpositive))
      · exact hbaseNonneg
    have htangentNonneg : 0 ≤ frontier.tangent mover observer :=
      frontier.tangent_inactive_nonneg mover observer hbaseZero
    have htangentNonpos : frontier.tangent mover observer ≤ 0 := by
      apply le_of_not_gt
      intro hpositive
      apply hnoEntry
      exact ⟨mover.1, mover.2, observer, hbaseZero, by
        simpa [quittingActiveDebtTangentExtension, mover.2] using hpositive⟩
    have htangentZero : frontier.tangent mover observer = 0 :=
      le_antisymm htangentNonpos htangentNonneg
    have hchangeObserver := hchange observer
    unfold quittingTerminalSemanticDebtChange at hchangeObserver
    rw [hbaseZero, htangentZero] at hchangeObserver
    exact (ne_of_gt hobserver) (by simpa using hchangeObserver)
  · intro heq
    have hmoverMem : mover.1 ∈
        Finset.univ.filter fun who ↦
          0 < quittingTerminalSemanticDebt endpoint.cluster who := by
      rw [heq]
      exact mover.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmoverMem
    linarith

/-- The support deflation lowers the finite cardinal rank. -/
theorem positiveDebtSupport_card_lt_of_exactDiagonal_of_flat_of_noEntry_of_minimumFiber
    (endpoint : FullResetEndpointCluster frontier mover)
    (hflat : ∑ observer, frontier.tangent mover observer = 0)
    (hnoEntry :
      ¬ HasQuittingStoppingLawFlatSupportEntry
        frontier.base frontier.active frontier.tangent)
    (hminimumFiber :
      quittingTerminalSemanticDebtSum endpoint.cluster =
        quittingTerminalSemanticDebtSum frontier.base) :
    (Finset.univ.filter fun who ↦
        0 < quittingTerminalSemanticDebt endpoint.cluster who).card <
      frontier.active.card :=
  Finset.card_lt_card
    (endpoint.positiveDebtSupport_ssubset_of_exactDiagonal_of_flat_of_noEntry_of_minimumFiber
      hflat hnoEntry hminimumFiber)

end FullResetEndpointCluster

/-- In the potential arm, the selected mover has a full-reset endpoint
cluster.  If such a cluster lies on the minimum-total-debt fiber and its
diagonal came from vanishing-regret extraction, then active support strictly
deflates and the stored second debtor strictly decreases. -/
theorem exists_potentialCoDecrease_fullResetEndpointCluster
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (hpotential : HasQuittingStoppingLawFlatPotentialCoDecrease
      frontier.active frontier.tangent)
    (hflat : ∀ mover, ∑ observer, frontier.tangent mover observer = 0)
    (hnoEntry :
      ¬ HasQuittingStoppingLawFlatSupportEntry
        frontier.base frontier.active frontier.tangent) :
    ∃ mover : {who // who ∈ frontier.active},
      ∃ other ∈ frontier.active.erase mover.1,
      frontier.tangent mover other < 0 ∧
      Nonempty (FullResetEndpointCluster frontier mover) ∧
      ∀ endpoint : FullResetEndpointCluster frontier mover,
        quittingTerminalSemanticDebtSum endpoint.cluster =
            quittingTerminalSemanticDebtSum frontier.base →
          (Finset.univ.filter fun who ↦
              0 < quittingTerminalSemanticDebt endpoint.cluster who) ⊂
              frontier.active ∧
            quittingTerminalSemanticDebt endpoint.cluster other <
              quittingTerminalSemanticDebt frontier.base other := by
  rcases hpotential with
    ⟨_potential, mover, hmover, other, hother, _hnonneg, _hseparation,
      _hmax, _hmoverLoss, hotherDecrease⟩
  let activeMover : {who // who ∈ frontier.active} := ⟨mover, hmover⟩
  have htangentOther : frontier.tangent activeMover other < 0 := by
    simpa [activeMover, quittingActiveDebtTangentExtension, hmover] using
      hotherDecrease
  refine ⟨activeMover, other, hother, ?_,
    frontier.exists_fullResetEndpointCluster activeMover, ?_⟩
  · exact htangentOther
  · intro endpoint hminimumFiber
    have hsupport :=
      endpoint.positiveDebtSupport_ssubset_of_exactDiagonal_of_flat_of_noEntry_of_minimumFiber
        (hflat activeMover) hnoEntry hminimumFiber
    have hchange := endpoint.debtChange_eq_tangent_of_flat_of_minimumFiber
      (hflat activeMover) hminimumFiber other
    have hdecrease :
        quittingTerminalSemanticDebt endpoint.cluster other <
          quittingTerminalSemanticDebt frontier.base other := by
      unfold quittingTerminalSemanticDebtChange at hchange
      linarith [htangentOther]
    exact ⟨hsupport, hdecrease⟩

/-- The flat no-entry potential arm needs at least three active debtors.  With
at most two, its selected mover and same-column co-decreased debtor exhaust
the active support; both tangent entries are negative and every inactive
entry is zero, contradicting flatness. -/
theorem three_le_active_card_of_flatPotentialCoDecrease_of_noEntry
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (hpotential : HasQuittingStoppingLawFlatPotentialCoDecrease
      frontier.active frontier.tangent)
    (hflat : ∀ mover, ∑ observer, frontier.tangent mover observer = 0)
    (hnoEntry :
      ¬ HasQuittingStoppingLawFlatSupportEntry
        frontier.base frontier.active frontier.tangent) :
    3 ≤ frontier.active.card := by
  rcases hpotential with
    ⟨_potential, mover, hmover, other, hother, _hnonneg, _hseparation,
      _hmax, _hmoverLoss, hotherDecrease⟩
  let activeMover : {who // who ∈ frontier.active} := ⟨mover, hmover⟩
  have hotherMem : other ∈ frontier.active := (Finset.mem_erase.mp hother).2
  have hotherNe : other ≠ mover := (Finset.mem_erase.mp hother).1
  have hmoverNe : mover ≠ other := Ne.symm hotherNe
  have htangentOther : frontier.tangent activeMover other < 0 := by
    simpa [activeMover, quittingActiveDebtTangentExtension, hmover] using
      hotherDecrease
  have htangentMover : frontier.tangent activeMover mover < 0 := by
    rw [frontier.tangent_diagonal_eq activeMover]
    linarith [(frontier.active_iff mover).1 hmover]
  by_contra hcard
  have hcardLe : frontier.active.card ≤ 2 := by omega
  have hpairSubset : ({mover, other} : Finset ι) ⊆ frontier.active := by
    intro who hwho
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
    rcases hwho with rfl | rfl
    · exact hmover
    · exact hotherMem
  have hpairCard : ({mover, other} : Finset ι).card = 2 :=
    Finset.card_pair hmoverNe
  have hactiveEq : ({mover, other} : Finset ι) = frontier.active := by
    apply Finset.eq_of_subset_of_card_le hpairSubset
    rw [hpairCard]
    exact hcardLe
  have htangentInactive : ∀ observer ∉ ({mover, other} : Finset ι),
      frontier.tangent activeMover observer = 0 := by
    intro observer hobserver
    have hinactive : observer ∉ frontier.active := by
      simpa [← hactiveEq] using hobserver
    have hbaseNonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward frontier.base_mem observer
    have hbaseZero :
        quittingTerminalSemanticDebt frontier.base observer = 0 := by
      apply le_antisymm
      · exact le_of_not_gt (fun hpositive ↦
          hinactive ((frontier.active_iff observer).2 hpositive))
      · exact hbaseNonneg
    have htangentNonneg : 0 ≤ frontier.tangent activeMover observer :=
      frontier.tangent_inactive_nonneg activeMover observer hbaseZero
    have htangentNonpos : frontier.tangent activeMover observer ≤ 0 := by
      apply le_of_not_gt
      intro hpositive
      apply hnoEntry
      exact ⟨mover, hmover, observer, hbaseZero, by
        simpa [quittingActiveDebtTangentExtension, hmover] using hpositive⟩
    exact le_antisymm htangentNonpos htangentNonneg
  have hpairSum :
      (∑ observer ∈ ({mover, other} : Finset ι),
          frontier.tangent activeMover observer) = 0 := by
    rw [Finset.sum_subset (Finset.subset_univ _) (fun observer _ hobserver ↦
      htangentInactive observer hobserver)]
    exact hflat activeMover
  rw [Finset.sum_pair hmoverNe] at hpairSum
  linarith

/-- At active-support rank at most two, flatness and absence of support entry
force the normalized positive charged-circulation arm.  The potential arm is
excluded by `three_le_active_card_of_flatPotentialCoDecrease_of_noEntry`. -/
theorem has_flatChargedCirculation_of_active_card_le_two_of_flat_of_noEntry
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (hcard : frontier.active.card ≤ 2)
    (hflat : ∀ mover, ∑ observer, frontier.tangent mover observer = 0)
    (hnoEntry :
      ¬ HasQuittingStoppingLawFlatSupportEntry
        frontier.base frontier.active frontier.tangent) :
    HasQuittingStoppingLawFlatChargedCirculation
      frontier.active frontier.tangent := by
  rcases frontier.exhaustive_branch with hpositive |
      ⟨_hflat, hentry⟩ |
      ⟨_hflat, _hnoEntry, hcirculation⟩ |
      ⟨_hflat, _hnoEntry, _hnoCirculation, hpotential⟩
  · obtain ⟨mover, hmover⟩ := hpositive
    rw [hflat mover] at hmover
    exact False.elim ((lt_irrefl 0) hmover)
  · exact False.elim (hnoEntry hentry)
  · exact hcirculation
  · have hthree :=
      frontier.three_le_active_card_of_flatPotentialCoDecrease_of_noEntry
        hpotential hflat hnoEntry
    omega

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
