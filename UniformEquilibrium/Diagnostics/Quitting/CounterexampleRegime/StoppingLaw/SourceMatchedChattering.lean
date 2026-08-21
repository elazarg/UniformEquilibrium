/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.ChargedCirculationChattering
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.Frontier

/-!
# Source-matched chattering for a stopping-law charged circulation

The flat charged-circulation branch of the stopping-law frontier is stated for
limiting normalized debt chords.  The circulation itself is therefore not yet
a chronological word in the semantic carrier.

This module closes the first, purely finite, part of that gap.  Integer
chattering rounds the limiting circulation.  Since all active movers were
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
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleStoppingLawFrontier

/-- The literal normalized debt chord at one selected common-source index. -/
def actualDebtDirection
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (mover : {who // who ∈ frontier.active})
    (observer : ι) : ℝ :=
  quittingStoppingLawNormalizedDebtDirection reward
    (frontier.profiles (frontier.subseq rank)) mover.1
    (frontier.bestResponse mover (frontier.subseq rank))
    (frontier.lambda (frontier.subseq rank))
    (frontier.lambda_pos (frontier.subseq rank)).le
    (frontier.lambda_le_one (frontier.subseq rank)) observer

/-- The actual mover charge of a normalized stopping-law chord. -/
def actualGain
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (mover : {who // who ∈ frontier.active}) : ℝ :=
  -frontier.actualDebtDirection rank mover mover.1

/-- **A limiting charged circulation has finite source-matched probes.**

For one fixed circulation witness, `budget` is independent of `N`.  At every
positive integer scale there is one late source index and one natural-number
multiplicity for every active mover such that:

* all actual reset chords are based at that same source profile;
* the rounded aggregate debt displacement is at most `O(1/N)` in every
  coordinate; and
* the rounded aggregate actual mover charge is at least `1 - O(1/N)`.

This is a finite star packet, not a sequentially executable word. -/
theorem exists_sourceMatchedChattering
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.active frontier.tangent) :
    ∃ budget : ℝ, 0 ≤ budget ∧ ∀ N : ℕ, 0 < N →
      ∃ rank : ℕ, N ≤ rank ∧
        ∃ count : {who // who ∈ frontier.active} → ℕ,
          (∀ observer,
            |∑ mover, ((count mover : ℝ) / N) *
                frontier.actualDebtDirection rank mover observer| ≤
              ((∑ mover, |frontier.tangent mover observer|) + budget) / N) ∧
          1 - ((∑ mover, |frontier.tangent mover mover.1|) + budget) / N ≤
            ∑ mover, ((count mover : ℝ) / N) *
              frontier.actualGain rank mover := by
  dsimp [HasQuittingStoppingLawFlatChargedCirculation] at hcirculation
  rcases hcirculation with ⟨mass, hmass, hbalance, hcharge⟩
  let budget : ℝ := ∑ mover, mass mover
  have hbudget : 0 ≤ budget :=
    Finset.sum_nonneg fun mover _ ↦ hmass mover
  refine ⟨budget, hbudget, ?_⟩
  intro N hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hscale : 0 < (1 : ℝ) / N := div_pos zero_lt_one hNreal
  have hclose : ∀ᶠ rank in atTop,
      ∀ mover : {who // who ∈ frontier.active}, ∀ observer,
        |frontier.actualDebtDirection rank mover observer -
            frontier.tangent mover observer| ≤ 1 / N := by
    rw [Filter.eventually_all]
    intro mover
    rw [Filter.eventually_all]
    intro observer
    have htendsto := frontier.tangent_tendsto mover observer
    have hball := htendsto.eventually
      (Metric.ball_mem_nhds (frontier.tangent mover observer) hscale)
    filter_upwards [hball] with rank hrank
    exact (by simpa [actualDebtDirection, Real.dist_eq] using hrank.le)
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.1 hclose
  let rank := max N threshold
  have hrankN : N ≤ rank := le_max_left _ _
  have hcloseRank : ∀ mover : {who // who ∈ frontier.active}, ∀ observer,
      |frontier.actualDebtDirection rank mover observer -
          frontier.tangent mover observer| ≤ 1 / N :=
    hthreshold rank (le_max_right _ _)
  have hbalance' : ∀ observer,
      ∑ mover, mass mover * frontier.tangent mover observer = 0 := by
    intro observer
    simpa [quittingActiveDebtTangentExtension] using hbalance observer
  have hcharge' :
      ∑ mover, mass mover * (-frontier.tangent mover mover.1) = 1 := by
    simpa [quittingActiveDebtTangentGain,
      quittingActiveDebtTangentExtension] using hcharge
  let count : {who // who ∈ frontier.active} → ℕ :=
    chatteringCount mass N
  have hcoefficientNonneg : ∀ mover,
      0 ≤ chatteringCoefficient mass N mover := by
    intro mover
    positivity
  have hcoefficientLe : ∀ mover,
      chatteringCoefficient mass N mover ≤ mass mover := by
    intro mover
    exact chatteringCoefficient_le mass N hN mover (hmass mover)
  have hperturb : ∀ observer,
      |∑ mover, chatteringCoefficient mass N mover *
          (frontier.actualDebtDirection rank mover observer -
            frontier.tangent mover observer)| ≤ budget / N := by
    intro observer
    calc
      |∑ mover, chatteringCoefficient mass N mover *
          (frontier.actualDebtDirection rank mover observer -
            frontier.tangent mover observer)| ≤
          ∑ mover, |chatteringCoefficient mass N mover *
            (frontier.actualDebtDirection rank mover observer -
              frontier.tangent mover observer)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ mover, mass mover * (1 / N) := by
        apply Finset.sum_le_sum
        intro mover _
        rw [abs_mul, abs_of_nonneg (hcoefficientNonneg mover)]
        exact mul_le_mul (hcoefficientLe mover)
          (hcloseRank mover observer) (abs_nonneg _) (hmass mover)
      _ = budget / N := by
        rw [← Finset.sum_mul]
        simp only [budget]
        ring
  have hround : ∀ observer,
      |∑ mover, chatteringCoefficient mass N mover *
          frontier.tangent mover observer| ≤
        (∑ mover, |frontier.tangent mover observer|) / N := by
    intro observer
    exact abs_sum_chatteringCoefficient_mul_column_le
      (fun mover observer ↦ frontier.tangent mover observer)
      mass N hN hmass observer (hbalance' observer)
  have hactual : ∀ observer,
      |∑ mover, chatteringCoefficient mass N mover *
          frontier.actualDebtDirection rank mover observer| ≤
        ((∑ mover, |frontier.tangent mover observer|) + budget) / N := by
    intro observer
    have hdecompose :
        (∑ mover, chatteringCoefficient mass N mover *
            frontier.actualDebtDirection rank mover observer) =
          (∑ mover, chatteringCoefficient mass N mover *
            frontier.tangent mover observer) +
          ∑ mover, chatteringCoefficient mass N mover *
            (frontier.actualDebtDirection rank mover observer -
              frontier.tangent mover observer) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro mover _
      ring
    rw [hdecompose]
    calc
      |(∑ mover, chatteringCoefficient mass N mover *
            frontier.tangent mover observer) +
          ∑ mover, chatteringCoefficient mass N mover *
            (frontier.actualDebtDirection rank mover observer -
              frontier.tangent mover observer)| ≤
          |∑ mover, chatteringCoefficient mass N mover *
            frontier.tangent mover observer| +
          |∑ mover, chatteringCoefficient mass N mover *
            (frontier.actualDebtDirection rank mover observer -
              frontier.tangent mover observer)| := abs_add_le _ _
      _ ≤ (∑ mover, |frontier.tangent mover observer|) / N +
          budget / N := add_le_add (hround observer) (hperturb observer)
      _ = ((∑ mover, |frontier.tangent mover observer|) + budget) / N := by
        ring
  have hgainPerturb :
      |(∑ mover, chatteringCoefficient mass N mover *
          frontier.actualGain rank mover) -
        ∑ mover, chatteringCoefficient mass N mover *
          (-frontier.tangent mover mover.1)| ≤ budget / N := by
    have hrewrite :
        (∑ mover, chatteringCoefficient mass N mover *
            frontier.actualGain rank mover) -
          ∑ mover, chatteringCoefficient mass N mover *
            (-frontier.tangent mover mover.1) =
          ∑ mover, chatteringCoefficient mass N mover *
            (-(frontier.actualDebtDirection rank mover mover.1 -
              frontier.tangent mover mover.1)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro mover _
      simp only [actualGain]
      ring
    rw [hrewrite]
    calc
      |∑ mover, chatteringCoefficient mass N mover *
          (-(frontier.actualDebtDirection rank mover mover.1 -
            frontier.tangent mover mover.1))| ≤
          ∑ mover, |chatteringCoefficient mass N mover *
            (-(frontier.actualDebtDirection rank mover mover.1 -
              frontier.tangent mover mover.1))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ mover, mass mover * (1 / N) := by
        apply Finset.sum_le_sum
        intro mover _
        rw [abs_mul, abs_neg,
          abs_of_nonneg (hcoefficientNonneg mover)]
        exact mul_le_mul (hcoefficientLe mover)
          (hcloseRank mover mover.1) (abs_nonneg _) (hmass mover)
      _ = budget / N := by
        rw [← Finset.sum_mul]
        simp only [budget]
        ring
  have hroundCharge :
      1 - (∑ mover, |-frontier.tangent mover mover.1|) / N ≤
        ∑ mover, chatteringCoefficient mass N mover *
          (-frontier.tangent mover mover.1) := by
    have herror := abs_sum_chatteringCoefficient_mul_charge_sub_one_le
      (fun mover : {who // who ∈ frontier.active} ↦
        -frontier.tangent mover mover.1)
      mass N hN hmass hcharge'
    have hlower := neg_le_of_abs_le herror
    linarith
  have hactualCharge :
      1 - ((∑ mover, |frontier.tangent mover mover.1|) + budget) / N ≤
        ∑ mover, chatteringCoefficient mass N mover *
          frontier.actualGain rank mover := by
    have hgainLower := neg_le_of_abs_le hgainPerturb
    have habs : (∑ mover, |-frontier.tangent mover mover.1|) =
        ∑ mover, |frontier.tangent mover mover.1| := by
      apply Finset.sum_congr rfl
      intro mover _
      rw [abs_neg]
    rw [habs] at hroundCharge
    linarith
  refine ⟨rank, hrankN, count, ?_, ?_⟩
  · intro observer
    simpa only [count, ← chatteringCoefficient_eq_count_div] using
      hactual observer
  · simpa only [count, ← chatteringCoefficient_eq_count_div] using
      hactualCharge

end QuittingCounterexampleStoppingLawFrontier
end GameTheory
