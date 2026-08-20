/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.Frontier
import UniformEquilibrium.Quitting.Debt.Dynamic.SemanticChronology

/-!
# Counterexample-tail semantic chronology

The production semantic-chronology owner identifies exact dynamic-debt edges
and finite chains with literal terminal semantics.  Here those interfaces are
applied to the counterexample seam: fixed-time projective limits first give
carrier membership, and a separate chronological limit gives the
all-Continue self-loop pair.  No interchange of the two limits is used.

Consequently the stopping-law frontier minimum is bounded above by the debt
sum of every tail row and by the limiting self-loop debt sum.  These are only
one-sided comparisons: the finite exact-D selector minimizes a maximum debt
coordinate over finite zero-boundary chains, whereas the frontier minimizes
total semantic debt over the full carrier.  Nothing here identifies either
tail point as a minimizer.
-/

noncomputable section

namespace GameTheory

open Filter Set StochasticGame Math.Probability Math.ProbabilityMassFunction
open Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The selected projective tail and its all-Continue limit -/

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

/-- Each fixed-time projective exact-D tail point is a literal point of the
terminal-semantic carrier.  The finite cutoff limit is taken with `time`
fixed. -/
theorem dynamicDebtSemanticPair_tail_mem_carrier (time : ℕ) :
    quittingDynamicDebtSemanticPair (seam.tail time) ∈
      quittingTerminalSemanticCarrier reward := by
  letI : Nonempty ι := regime.nonempty_players
  have hpoint : Tendsto (fun family ↦
      quittingFiniteMinMaxDynamicDebtTail reward (seam.subseq family) time)
      atTop (nhds (seam.tail time)) := by
    exact ((continuous_apply time).tendsto seam.tail).comp
      seam.projective_limit
  have hsemantic : Tendsto (fun family ↦ quittingDynamicDebtSemanticPair
      (quittingFiniteMinMaxDynamicDebtTail reward
        (seam.subseq family) time)) atTop
      (nhds (quittingDynamicDebtSemanticPair (seam.tail time))) :=
    (continuous_quittingDynamicDebtSemanticPair.tendsto
      (seam.tail time)).comp hpoint
  have hcutoff : ∀ᶠ family in atTop, time < seam.subseq family := by
    filter_upwards
      [seam.subseq_strict.tendsto_atTop.eventually_ge_atTop (time + 1)]
      with family hfamily
    omega
  have hfinite : ∀ᶠ family in atTop,
      quittingDynamicDebtSemanticPair
          (quittingFiniteMinMaxDynamicDebtTail reward
            (seam.subseq family) time) ∈
        quittingTerminalSemanticCarrier reward := by
    filter_upwards [hcutoff] with family htime
    unfold quittingFiniteMinMaxDynamicDebtTail
    rw [quittingFiniteNashBellmanPathDynamicDebtSemanticPair_eq_completion
      reward (seam.subseq family)
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward (seam.subseq family))
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
        reward (seam.subseq family)) time htime]
    apply subset_closure
    exact ⟨quittingRootSequenceProfile reward
        (quittingFiniteNashBellmanPathRoots (seam.subseq family)
          (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
            reward (seam.subseq family))) time, rfl⟩
  exact isClosed_closure.mem_of_tendsto hsemantic hfinite

/-- Every chronological tail edge is a state-matched terminal-semantic
prefix between literal carrier points, with exact root Nash at the displayed
root and a nonnegative successor debt. -/
theorem dynamicDebtSemanticPair_tail_chronology (time : ℕ) :
    quittingDynamicDebtSemanticPair (seam.tail time) ∈
        quittingTerminalSemanticCarrier reward ∧
      quittingDynamicDebtSemanticPair (seam.tail (time + 1)) ∈
        quittingTerminalSemanticCarrier reward ∧
      quittingDynamicDebtSemanticPair (seam.tail time) =
        quittingTerminalSemanticPrefix reward
          (quittingRootOfSimplex (seam.tail time).1.2)
          (quittingDynamicDebtSemanticPair (seam.tail (time + 1))) ∧
      IsεQuittingRootNash reward (seam.tail (time + 1)).1.1 0
        (quittingRootOfSimplex (seam.tail time).1.2) := by
  have hchronology := quittingDynamicDebtEdge_semanticPrefixChronology
    reward (seam.tail time) (seam.tail (time + 1)) (seam.tail_edge time)
      (seam.tail_mem (time + 1)).2.1
  exact ⟨seam.dynamicDebtSemanticPair_tail_mem_carrier time,
    seam.dynamicDebtSemanticPair_tail_mem_carrier (time + 1),
    hchronology.1, hchronology.2.1⟩

/-- The all-Continue limiting value/debt pair, with its debt reinterpreted as
the gap between prescribed value and augmented envelope. -/
def limitDynamicDebtSemanticPair : QuittingTerminalSemanticPair ι :=
  (seam.limit.value, seam.limit.value + seam.limit.debt)

@[simp]
theorem limitDynamicDebtSemanticPair_debt (who : ι) :
    quittingTerminalSemanticDebt seam.limitDynamicDebtSemanticPair who =
      seam.limit.debt who := by
  simp [limitDynamicDebtSemanticPair, quittingTerminalSemanticDebt]

/-- The chronological tail semantic pairs converge to the all-Continue
semantic pair.  This is a second, separate limit after fixed-time carrier
membership has already been proved. -/
theorem dynamicDebtSemanticPair_tail_tendsto :
    Tendsto (fun time ↦ quittingDynamicDebtSemanticPair (seam.tail time))
      atTop (nhds seam.limitDynamicDebtSemanticPair) := by
  have hvalue : Tendsto (fun time ↦ (seam.tail time).1.1) atTop
      (nhds seam.limit.value) :=
    tendsto_pi_nhds.2 seam.value_tendsto
  have hcap : Tendsto
      (fun time ↦ quittingDynamicDebtCap (seam.tail time)) atTop
      (nhds (seam.limit.value + seam.limit.debt)) := by
    apply tendsto_pi_nhds.2
    intro who
    simpa [quittingDynamicDebtCap_apply] using
      (seam.value_tendsto who).add (seam.debt_tendsto who)
  change Tendsto
    (fun time ↦ ((seam.tail time).1.1,
      quittingDynamicDebtCap (seam.tail time))) atTop
    (nhds (seam.limit.value, seam.limit.value + seam.limit.debt))
  simpa only [nhds_prod_eq] using hvalue.prodMk hcap

/-- The all-Continue chronological limit is itself a literal point of the
closed terminal-semantic carrier. -/
theorem limitDynamicDebtSemanticPair_mem_carrier :
    seam.limitDynamicDebtSemanticPair ∈
      quittingTerminalSemanticCarrier reward := by
  exact isClosed_closure.mem_of_tendsto
    seam.dynamicDebtSemanticPair_tail_tendsto
      (Filter.Eventually.of_forall
        seam.dynamicDebtSemanticPair_tail_mem_carrier)

/-- The limiting semantic carrier point is a literal all-Continue prefix
fixed point, inherited from the exact dynamic-debt self-loop. -/
theorem limitDynamicDebtSemanticPair_allContinue_prefix :
    seam.limitDynamicDebtSemanticPair =
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot
        seam.limitDynamicDebtSemanticPair := by
  have h := quittingDynamicDebtSemanticPair_eq_prefix reward
    (((seam.limit.value, quittingAllContinueSimplexRoot), seam.limit.debt) :
      QuittingDebtPoint ι)
    (((seam.limit.value, quittingAllContinueSimplexRoot), seam.limit.debt) :
      QuittingDebtPoint ι) seam.limit.exactSelfLoop
  have hpair : quittingDynamicDebtSemanticPair
      (((seam.limit.value, quittingAllContinueSimplexRoot), seam.limit.debt) :
        QuittingDebtPoint ι) = seam.limitDynamicDebtSemanticPair := by
    apply Prod.ext
    · rfl
    · funext who
      simp [quittingDynamicDebtSemanticPair, quittingDynamicDebtCap_apply,
        limitDynamicDebtSemanticPair]
  rw [hpair] at h
  simpa [quittingRootOfSimplex_allContinueSimplexRoot] using h

/-- The limiting all-Continue root is exact Nash against the limiting
prescribed value. -/
theorem limitDynamicDebtSemanticPair_allContinue_nash :
    IsεQuittingRootNash reward seam.limitDynamicDebtSemanticPair.1 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
  have h := quittingDynamicDebtEdge_exactNash reward
    (((seam.limit.value, quittingAllContinueSimplexRoot), seam.limit.debt) :
      QuittingDebtPoint ι)
    (((seam.limit.value, quittingAllContinueSimplexRoot), seam.limit.debt) :
      QuittingDebtPoint ι) seam.limit.exactSelfLoop
  simpa [limitDynamicDebtSemanticPair,
    quittingRootOfSimplex_allContinueSimplexRoot] using h

end QuittingCounterexampleSeamWitness

namespace QuittingCounterexampleStoppingLawFrontier

variable (frontier : QuittingCounterexampleStoppingLawFrontier regime)

/-- The independent frontier minimum is no larger than the total exact debt
of any chronological projective-tail point.  This does not assert equality.
-/
theorem baseDebtSum_le_seamTailDebtSum (time : ℕ) :
    quittingTerminalSemanticDebtSum frontier.base ≤
      ∑ who, (frontier.seam.tail time).2 who := by
  have h := frontier.base_minimum
    (quittingDynamicDebtSemanticPair (frontier.seam.tail time))
    (frontier.seam.dynamicDebtSemanticPair_tail_mem_carrier time)
  simpa [quittingTerminalSemanticDebtSum] using h

/-- The independent frontier minimum is no larger than the total debt of the
all-Continue chronological limit.  Again, no minimizer identification or
reverse inequality is claimed. -/
theorem baseDebtSum_le_seamLimitDebtSum :
    quittingTerminalSemanticDebtSum frontier.base ≤
      ∑ who, frontier.seam.limit.debt who := by
  have h := frontier.base_minimum
    frontier.seam.limitDynamicDebtSemanticPair
    frontier.seam.limitDynamicDebtSemanticPair_mem_carrier
  simpa [quittingTerminalSemanticDebtSum] using h

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
