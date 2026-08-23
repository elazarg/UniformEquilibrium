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
applied to the counterexample dynamic tail: fixed-time projective limits give
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
variable {witness : QuittingTerminalExploitabilityWitness reward}

namespace QuittingCounterexampleDynamicTailWitness

variable (tailWitness : QuittingCounterexampleDynamicTailWitness witness)

/-- Each fixed-time projective exact-D tail point is a literal point of the
terminal-semantic carrier.  The finite cutoff limit is taken with `time`
fixed. -/
theorem dynamicDebtSemanticPair_tail_mem_carrier (time : ℕ) :
    quittingDynamicDebtSemanticPair (tailWitness.tail time) ∈
      quittingTerminalSemanticCarrier reward := by
  letI : Nonempty ι := witness.nonempty_players
  have hpoint : Tendsto (fun family ↦
      quittingFiniteMinMaxDynamicDebtTail reward (tailWitness.subseq family) time)
      atTop (nhds (tailWitness.tail time)) := by
    exact ((continuous_apply time).tendsto tailWitness.tail).comp
      tailWitness.projective_limit
  have hsemantic : Tendsto (fun family ↦ quittingDynamicDebtSemanticPair
      (quittingFiniteMinMaxDynamicDebtTail reward
        (tailWitness.subseq family) time)) atTop
      (nhds (quittingDynamicDebtSemanticPair (tailWitness.tail time))) :=
    (continuous_quittingDynamicDebtSemanticPair.tendsto
      (tailWitness.tail time)).comp hpoint
  have hcutoff : ∀ᶠ family in atTop, time < tailWitness.subseq family := by
    filter_upwards
      [tailWitness.subseq_strict.tendsto_atTop.eventually_ge_atTop (time + 1)]
      with family hfamily
    omega
  have hfinite : ∀ᶠ family in atTop,
      quittingDynamicDebtSemanticPair
          (quittingFiniteMinMaxDynamicDebtTail reward
            (tailWitness.subseq family) time) ∈
        quittingTerminalSemanticCarrier reward := by
    filter_upwards [hcutoff] with family htime
    unfold quittingFiniteMinMaxDynamicDebtTail
    rw [quittingFiniteNashBellmanPathDynamicDebtSemanticPair_eq_completion
      reward (tailWitness.subseq family)
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward (tailWitness.subseq family))
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
        reward (tailWitness.subseq family)) time htime]
    apply subset_closure
    exact ⟨quittingRootSequenceProfile reward
        (quittingFiniteNashBellmanPathRoots (tailWitness.subseq family)
          (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
            reward (tailWitness.subseq family))) time, rfl⟩
  exact isClosed_closure.mem_of_tendsto hsemantic hfinite

/-- Every chronological tail edge is a state-matched terminal-semantic
prefix between literal carrier points, with exact root Nash at the displayed
root and a nonnegative successor debt. -/
theorem dynamicDebtSemanticPair_tail_chronology (time : ℕ) :
    quittingDynamicDebtSemanticPair (tailWitness.tail time) ∈
        quittingTerminalSemanticCarrier reward ∧
      quittingDynamicDebtSemanticPair (tailWitness.tail (time + 1)) ∈
        quittingTerminalSemanticCarrier reward ∧
      quittingDynamicDebtSemanticPair (tailWitness.tail time) =
        quittingTerminalSemanticPrefix reward
          (quittingRootOfSimplex (tailWitness.tail time).1.2)
          (quittingDynamicDebtSemanticPair (tailWitness.tail (time + 1))) ∧
      IsεQuittingRootNash reward (tailWitness.tail (time + 1)).1.1 0
        (quittingRootOfSimplex (tailWitness.tail time).1.2) := by
  have hchronology := quittingDynamicDebtEdge_semanticPrefixChronology
    reward (tailWitness.tail time) (tailWitness.tail (time + 1)) (tailWitness.tail_edge time)
      (tailWitness.tail_mem (time + 1)).2.1
  exact ⟨tailWitness.dynamicDebtSemanticPair_tail_mem_carrier time,
    tailWitness.dynamicDebtSemanticPair_tail_mem_carrier (time + 1),
    hchronology.1, hchronology.2.1⟩

/-- The all-Continue limiting value/debt pair, with its debt reinterpreted as
the gap between prescribed value and augmented envelope. -/
def limitDynamicDebtSemanticPair : QuittingTerminalSemanticPair ι :=
  (tailWitness.limit.value, tailWitness.limit.value + tailWitness.limit.debt)

@[simp]
theorem limitDynamicDebtSemanticPair_debt (who : ι) :
    quittingTerminalSemanticDebt tailWitness.limitDynamicDebtSemanticPair who =
      tailWitness.limit.debt who := by
  simp [limitDynamicDebtSemanticPair, quittingTerminalSemanticDebt]

/-- The chronological tail semantic pairs converge to the all-Continue
semantic pair.  This is a second, separate limit after fixed-time carrier
membership has already been proved. -/
theorem dynamicDebtSemanticPair_tail_tendsto :
    Tendsto (fun time ↦ quittingDynamicDebtSemanticPair (tailWitness.tail time))
      atTop (nhds tailWitness.limitDynamicDebtSemanticPair) := by
  have hvalue : Tendsto (fun time ↦ (tailWitness.tail time).1.1) atTop
      (nhds tailWitness.limit.value) :=
    tendsto_pi_nhds.2 tailWitness.value_tendsto
  have hcap : Tendsto
      (fun time ↦ quittingDynamicDebtCap (tailWitness.tail time)) atTop
      (nhds (tailWitness.limit.value + tailWitness.limit.debt)) := by
    apply tendsto_pi_nhds.2
    intro who
    simpa [quittingDynamicDebtCap_apply] using
      (tailWitness.value_tendsto who).add (tailWitness.debt_tendsto who)
  change Tendsto
    (fun time ↦ ((tailWitness.tail time).1.1,
      quittingDynamicDebtCap (tailWitness.tail time))) atTop
    (nhds (tailWitness.limit.value, tailWitness.limit.value + tailWitness.limit.debt))
  simpa only [nhds_prod_eq] using hvalue.prodMk hcap

/-- The all-Continue chronological limit is itself a literal point of the
closed terminal-semantic carrier. -/
theorem limitDynamicDebtSemanticPair_mem_carrier :
    tailWitness.limitDynamicDebtSemanticPair ∈
      quittingTerminalSemanticCarrier reward := by
  exact isClosed_closure.mem_of_tendsto
    tailWitness.dynamicDebtSemanticPair_tail_tendsto
      (Filter.Eventually.of_forall
        tailWitness.dynamicDebtSemanticPair_tail_mem_carrier)

/-- The limiting semantic carrier point is a literal all-Continue prefix
fixed point, inherited from the exact dynamic-debt self-loop. -/
theorem limitDynamicDebtSemanticPair_allContinue_prefix :
    tailWitness.limitDynamicDebtSemanticPair =
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot
        tailWitness.limitDynamicDebtSemanticPair := by
  have h := quittingDynamicDebtSemanticPair_eq_prefix reward
    (((tailWitness.limit.value, quittingAllContinueSimplexRoot), tailWitness.limit.debt) :
      QuittingDebtPoint ι)
    (((tailWitness.limit.value, quittingAllContinueSimplexRoot), tailWitness.limit.debt) :
      QuittingDebtPoint ι) tailWitness.limit.exactSelfLoop
  have hpair : quittingDynamicDebtSemanticPair
      (((tailWitness.limit.value, quittingAllContinueSimplexRoot), tailWitness.limit.debt) :
        QuittingDebtPoint ι) = tailWitness.limitDynamicDebtSemanticPair := by
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
    IsεQuittingRootNash reward tailWitness.limitDynamicDebtSemanticPair.1 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
  have h := quittingDynamicDebtEdge_exactNash reward
    (((tailWitness.limit.value, quittingAllContinueSimplexRoot), tailWitness.limit.debt) :
      QuittingDebtPoint ι)
    (((tailWitness.limit.value, quittingAllContinueSimplexRoot), tailWitness.limit.debt) :
      QuittingDebtPoint ι) tailWitness.limit.exactSelfLoop
  simpa [limitDynamicDebtSemanticPair,
    quittingRootOfSimplex_allContinueSimplexRoot] using h

end QuittingCounterexampleDynamicTailWitness

namespace QuittingCounterexampleStoppingLawFrontier

variable (frontier : QuittingCounterexampleStoppingLawFrontier witness)
variable (tailWitness : QuittingCounterexampleDynamicTailWitness witness)

/-- The independent frontier minimum is no larger than the total exact debt
of any chronological projective-tail point.  This does not assert equality.
-/
theorem baseDebtSum_le_dynamicTailDebtSum (time : ℕ) :
    quittingTerminalSemanticDebtSum frontier.base ≤
      ∑ who, (tailWitness.tail time).2 who := by
  have h := frontier.base_minimum
    (quittingDynamicDebtSemanticPair (tailWitness.tail time))
    (tailWitness.dynamicDebtSemanticPair_tail_mem_carrier time)
  simpa [quittingTerminalSemanticDebtSum] using h

/-- The independent frontier minimum is no larger than the total debt of the
all-Continue chronological limit.  Again, no minimizer identification or
reverse inequality is claimed. -/
theorem baseDebtSum_le_dynamicTailLimitDebtSum :
    quittingTerminalSemanticDebtSum frontier.base ≤
      ∑ who, tailWitness.limit.debt who := by
  have h := frontier.base_minimum
    tailWitness.limitDynamicDebtSemanticPair
    tailWitness.limitDynamicDebtSemanticPair_mem_carrier
  simpa [quittingTerminalSemanticDebtSum] using h

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
