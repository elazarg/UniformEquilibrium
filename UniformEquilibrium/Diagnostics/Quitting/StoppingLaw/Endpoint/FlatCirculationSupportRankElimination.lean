/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.UniformExistenceBoundary

/-!
# Elimination of flat circulation from finite support-rank termination

For an arbitrary active mover of a flat positive-minimum tangent family, every
literal full-replacement cluster has one of two exclusive outcomes.  A cluster
on the minimum-total-debt fiber permits re-extraction with strictly smaller
positive-debt support.  A cluster off that fiber carries an eventually paid
first-disagreement row along its actual source/reset subsequence.

Strong induction on the positive-debt-support cardinality therefore removes
flat charged circulation as a terminal exit of the support-rank argument.  The
resulting conditional uniform-payoff capstone needs only positive-slope,
support-entry, and paid-row consumers.  It does not construct any of those
three consumers.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingPositiveMinimumDebtTangentFamily

namespace FullReplacementCluster

variable {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
  {mover : {who // who ∈ frontier.positiveDebtSupport}}

/-- The minimum-fiber arm for a literal full-replacement cluster: the cluster
can be used as the base of a fresh tangent family whose positive-debt support
is a strict subset of the old support, hence has smaller cardinality. -/
def HasMinimumFiberSupportRankDescent
    (endpoint : FullReplacementCluster frontier mover) : Prop :=
  quittingTerminalSemanticDebtSum endpoint.cluster =
    quittingTerminalSemanticDebtSum frontier.base ∧
    ∃ next : QuittingPositiveMinimumDebtTangentFamily reward,
      next.base = endpoint.cluster ∧
        next.positiveDebtSupport ⊂ frontier.positiveDebtSupport ∧
          next.positiveDebtSupport.card < frontier.positiveDebtSupport.card

/-- The off-minimum arm for a literal full-replacement cluster: the actual
source/reset subsequence eventually carries a fixed positive-gain paid row for
an observer distinct from the mover. -/
def HasOffMinimumPaidFirstDisagreement
    (endpoint : FullReplacementCluster frontier mover) : Prop :=
  quittingTerminalSemanticDebtSum frontier.base <
      quittingTerminalSemanticDebtSum endpoint.cluster ∧
    ∃ observer : ι, ∃ gain : ℝ,
      observer ≠ mover.1 ∧ 0 < gain ∧
        ∀ᶠ rank in atTop,
          Nonempty (QuittingPaidFirstDisagreementRow reward
            (frontier.fullReplacementProfile mover (endpoint.subseq rank))
            observer gain)

/-- **Arbitrary-mover endpoint dichotomy.**  Under global flatness and absence
of inactive-support entry, every literal full-replacement cluster lies in
exactly one of the minimum-fiber rank-descent and off-minimum paid-row arms. -/
theorem minimumFiberSupportRankDescent_xor_offMinimumPaidFirstDisagreement
    (endpoint : FullReplacementCluster frontier mover)
    (hflat : ∀ source, ∑ observer, frontier.tangent source observer = 0)
    (hnoEntry : ¬HasQuittingStoppingLawFlatSupportEntry
      frontier.base frontier.positiveDebtSupport frontier.tangent) :
    Xor endpoint.HasMinimumFiberSupportRankDescent
      endpoint.HasOffMinimumPaidFirstDisagreement := by
  have hfloor := frontier.base_minimum endpoint.cluster endpoint.cluster_mem
  rw [xor_def]
  rcases hfloor.eq_or_lt with hsame | hseparated
  · left
    have hminimumFiber := hsame.symm
    refine ⟨⟨hminimumFiber, ?_⟩, ?_⟩
    · exact exists_reextractedFrontier_of_minimumFiberEndpoint
        frontier endpoint hflat hnoEntry hminimumFiber
    · rintro ⟨hstrict, _⟩
      rw [hminimumFiber] at hstrict
      exact (lt_irrefl _ hstrict)
  · right
    refine ⟨⟨hseparated, ?_⟩, ?_⟩
    · exact endpoint.exists_eventually_paidFirstDisagreement
        (hflat mover) hseparated
    · rintro ⟨hminimumFiber, _⟩
      rw [hminimumFiber] at hseparated
      exact (lt_irrefl _ hseparated)

end FullReplacementCluster

/-- A finite support-rank argument has terminated at positive total slope,
flat support entry, or an off-minimum literal endpoint carrying an eventually
paid first-disagreement row.  There is no separate circulation exit. -/
def HasQuittingStoppingLawReducedSupportRankAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ frontier : QuittingPositiveMinimumDebtTangentFamily reward,
    (∃ mover, 0 < ∑ observer, frontier.tangent mover observer) ∨
    ((∀ mover, ∑ observer, frontier.tangent mover observer = 0) ∧
      HasQuittingStoppingLawFlatSupportEntry
        frontier.base frontier.positiveDebtSupport frontier.tangent) ∨
    ∃ mover : {who // who ∈ frontier.positiveDebtSupport},
      ∃ endpoint : FullReplacementCluster frontier mover,
        endpoint.HasOffMinimumPaidFirstDisagreement

/-- **Reduced finite support-rank termination.**  Re-extraction along an
arbitrary active mover in either flat no-entry branch strictly lowers the
support rank or reaches the existing paid-row exit.  Thus charged circulation
is not a fourth terminal alternative. -/
theorem reducedSupportRankAlternative
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward) :
    HasQuittingStoppingLawReducedSupportRankAlternative reward := by
  classical
  generalize hrank : frontier.positiveDebtSupport.card = rank
  induction rank using Nat.strong_induction_on generalizing frontier with
  | h rank ih =>
      have continue_of_flat_noEntry
          (hflat : ∀ mover, ∑ observer, frontier.tangent mover observer = 0)
          (hnoEntry : ¬HasQuittingStoppingLawFlatSupportEntry
            frontier.base frontier.positiveDebtSupport frontier.tangent) :
          HasQuittingStoppingLawReducedSupportRankAlternative reward := by
        obtain ⟨who, hwho⟩ := frontier.positiveDebtSupport_nonempty
        let mover : {who // who ∈ frontier.positiveDebtSupport} := ⟨who, hwho⟩
        obtain ⟨endpoint⟩ :=
          frontier.exists_fullReplacementEndpointCluster mover
        have hdichotomy :=
          endpoint.minimumFiberSupportRankDescent_xor_offMinimumPaidFirstDisagreement
            hflat hnoEntry
        rw [xor_def] at hdichotomy
        rcases hdichotomy with hminimum | hpaid
        · obtain ⟨⟨_hminimumFiber, next, _hnextBase, _hnextSubset,
              hnextCard⟩,
              _hnotPaid⟩ := hminimum
          apply ih next.positiveDebtSupport.card
          · exact hnextCard.trans_eq hrank
          · rfl
        · exact ⟨frontier, Or.inr (Or.inr
            ⟨mover, endpoint, hpaid.1⟩)⟩
      rcases frontier.exhaustiveAlternative with hpositive | hentry |
          hcirculation | hpotential
      · exact ⟨frontier, Or.inl hpositive⟩
      · exact ⟨frontier, Or.inr (Or.inl hentry)⟩
      · exact continue_of_flat_noEntry hcirculation.1 hcirculation.2.1
      · exact continue_of_flat_noEntry hpotential.1 hpotential.2.1

/-- Every positive global minimum of terminal semantic debt reaches the
reduced three-exit support-rank alternative. -/
theorem reducedSupportRankAlternative_of_positiveMinimumDebt
    (hminimum : HasPositiveMinimumTerminalSemanticDebt reward) :
    HasQuittingStoppingLawReducedSupportRankAlternative reward := by
  let frontier := (nonempty_positiveMinimumDebtTangentFamily hminimum).some
  exact frontier.reducedSupportRankAlternative

end QuittingPositiveMinimumDebtTangentFamily

/-- **Three-consumer conditional capstone.**  The reduced support-rank theorem
deletes the charged-circulation producer from the existing conditional
uniform-payoff argument. -/
theorem exists_uniformEquilibriumPayoff_of_reducedSupportRankExitConsumers
    [Nonempty ι]
    (hpositiveSlope :
      ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward),
        (∃ mover, 0 < ∑ observer, frontier.tangent mover observer) →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hsupportEntry :
      ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward),
        HasQuittingStoppingLawFlatSupportEntry
          frontier.base frontier.positiveDebtSupport frontier.tangent →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hpaid : PaidFirstDisagreementUniformPayoffConsumer reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  have hminimum :=
    (not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
      reward).1 hno
  let first := (nonempty_positiveMinimumDebtTangentFamily hminimum).some
  obtain ⟨frontier, hpositive | hentry | hpaidExit⟩ :=
    first.reducedSupportRankAlternative
  · exact hno
      (quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
        reward (hpositiveSlope frontier hpositive))
  · exact hno
      (quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
        reward (hsupportEntry frontier hentry.2))
  · obtain ⟨mover, endpoint, hseparated, observer, gain, hobserver, hgain,
        hrows⟩ := hpaidExit
    exact hno (hpaid frontier mover endpoint hseparated
      observer gain hobserver hgain hrows)

end GameTheory
