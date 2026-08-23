/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.ChargedCirculationChattering
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.PositiveMinimumDebtTangentFamily

/-!
# A frozen balanced reset packet for a stopping-law charged circulation

The flat charged-circulation branch of the stopping-law frontier is stated for
limiting normalized debt chords.  The circulation itself is therefore not yet
a chronological word in the semantic carrier.

This module closes the first, purely finite, part of that gap.  Integer
rounding balances the limiting circulation.  Since all active movers were
extracted from one common profile sequence and one common reset scale, one late
index realizes every rounded column by an actual legal stopping-law reset from
the same semantic source.  The aggregate actual debt displacement is `O(1/N)`
and its aggregate mover charge is `1 - O(1/N)`.

No sequential composition is claimed.  The reset profiles in one packet share
a source; applying one changes the source for the next.  A nonlinear
composition estimate or a source-reprojection theorem is still required to
turn this finite star-shaped packet into a chronological semantic return.
-/

noncomputable section

namespace GameTheory

open Filter Finset Math.Probability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {witness : QuittingTerminalExploitabilityWitness reward}

namespace QuittingPositiveMinimumDebtTangentFamily

/-- The literal normalized debt chord at one selected common-source index. -/
def frozenDebtDirection
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (mover : {who // who ∈ frontier.positiveDebtSupport})
    (observer : ι) : ℝ :=
  quittingStoppingLawNormalizedDebtDirection reward
    (frontier.source rank) mover.1
    (frontier.replacement mover rank)
    (frontier.scale rank)
    (frontier.scale_pos rank).le
    (frontier.scale_le_one rank) observer

/-- The actual mover charge of a normalized stopping-law chord. -/
def frozenGain
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (mover : {who // who ∈ frontier.positiveDebtSupport}) : ℝ :=
  -frontier.frozenDebtDirection rank mover mover.1

/-- **A balanced reset packet is local on every frozen prefix.**

The circulation mass is retained explicitly. For every positive scale, one
late common source supports all `N` microcycles. Every partial microcycle and
every number of completed microcycles up to `N` has `O(1/N)` aggregate actual
debt displacement, while the completed rounded packet keeps charge
`1 - O(1/N)`.

The prefix estimate is still frozen at the selected source. It is the exact
input needed by a separate nonlinear reset-cube or reprojection argument; this
It does not assert chronological executability by itself. -/
theorem exists_frozenBalancedResetPacket
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.positiveDebtSupport frontier.tangent) :
    ∃ mass : {who // who ∈ frontier.positiveDebtSupport} → ℝ,
      (∀ mover, 0 ≤ mass mover) ∧
      (∀ observer,
        ∑ mover, mass mover * frontier.tangent mover observer = 0) ∧
      (∑ mover, mass mover * (-frontier.tangent mover mover.1) = 1) ∧
      ∀ N : ℕ, 0 < N →
        ∃ rank : ℕ, N ≤ rank ∧
          (∀ completed : ℕ, completed ≤ N →
            ∀ partialCount : {who // who ∈ frontier.positiveDebtSupport} → ℕ,
              (∀ mover,
                partialCount mover ≤ chatteringCount mass N mover) →
              ∀ observer,
                |∑ mover,
                    chatteringPrefixCoefficient mass N completed partialCount
                        mover *
                      frontier.frozenDebtDirection rank mover observer| ≤
                  ((∑ mover, |frontier.tangent mover observer|) +
                      ∑ mover,
                        mass mover * |frontier.tangent mover observer| +
                    2 * ∑ mover, mass mover) / N) ∧
          1 - ((∑ mover, |frontier.tangent mover mover.1|) +
                ∑ mover, mass mover) / N ≤
            ∑ mover, chatteringCoefficient mass N mover *
              frontier.frozenGain rank mover := by
  dsimp [HasQuittingStoppingLawFlatChargedCirculation] at hcirculation
  rcases hcirculation with ⟨mass, hmass, hbalance, hcharge⟩
  have hbalance' : ∀ observer,
      ∑ mover, mass mover * frontier.tangent mover observer = 0 := by
    intro observer
    simpa [quittingActiveDebtTangentExtension] using hbalance observer
  have hcharge' :
      ∑ mover, mass mover * (-frontier.tangent mover mover.1) = 1 := by
    simpa [quittingActiveDebtTangentGain,
      quittingActiveDebtTangentExtension] using hcharge
  refine ⟨mass, hmass, hbalance', hcharge', ?_⟩
  intro N hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hscale : 0 < (1 : ℝ) / N := div_pos zero_lt_one hNreal
  have hclose : ∀ᶠ rank in atTop,
      ∀ mover : {who // who ∈ frontier.positiveDebtSupport}, ∀ observer,
        |frontier.frozenDebtDirection rank mover observer -
            frontier.tangent mover observer| ≤ 1 / N := by
    rw [Filter.eventually_all]
    intro mover
    rw [Filter.eventually_all]
    intro observer
    have htendsto := frontier.tangent_tendsto mover observer
    have hball := htendsto.eventually
      (Metric.ball_mem_nhds (frontier.tangent mover observer) hscale)
    filter_upwards [hball] with rank hrank
    exact (by simpa [frozenDebtDirection, Real.dist_eq] using hrank.le)
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.1 hclose
  let rank := max N threshold
  have hrankN : N ≤ rank := le_max_left _ _
  have hcloseRank : ∀ mover : {who // who ∈ frontier.positiveDebtSupport}, ∀ observer,
      |frontier.frozenDebtDirection rank mover observer -
          frontier.tangent mover observer| ≤ 1 / N :=
    hthreshold rank (le_max_right _ _)
  refine ⟨rank, hrankN, ?_, ?_⟩
  · intro completed hcompleted partialCount hpartial observer
    exact abs_sum_chatteringPrefixCoefficient_mul_perturbed_column_le
      (fun mover observer ↦ frontier.tangent mover observer)
      (fun mover observer ↦ frontier.frozenDebtDirection rank mover observer)
      mass N completed hN hcompleted partialCount hpartial hmass observer
      (hbalance' observer) (fun mover ↦ hcloseRank mover observer)
  · have hgainClose : ∀ mover,
        |frontier.frozenGain rank mover -
            (-frontier.tangent mover mover.1)| ≤ 1 / N := by
      intro mover
      rw [frozenGain, neg_sub_neg, abs_sub_comm]
      exact hcloseRank mover mover.1
    have hchargeBound :=
      abs_sum_chatteringCoefficient_mul_perturbed_charge_sub_one_le
        (fun mover ↦ -frontier.tangent mover mover.1)
        (fun mover ↦ frontier.frozenGain rank mover) mass N hN hmass
        hcharge' hgainClose
    have hlower := neg_le_of_abs_le hchargeBound
    have habs : (∑ mover, |-frontier.tangent mover mover.1|) =
        ∑ mover, |frontier.tangent mover mover.1| := by
      apply Finset.sum_congr rfl
      intro mover _
      rw [abs_neg]
    rw [habs] at hlower
    let error : ℝ := ((∑ mover, |frontier.tangent mover mover.1|) +
      ∑ mover, mass mover) / N
    let approximation : ℝ := ∑ mover,
      chatteringCoefficient mass N mover * frontier.frozenGain rank mover
    change -error ≤ approximation - 1 at hlower
    change 1 - error ≤ approximation
    linarith

end QuittingPositiveMinimumDebtTangentFamily
end GameTheory
