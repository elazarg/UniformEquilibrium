/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.WeakPathConvergence
import UniformEquilibrium.Quitting.Classification.Existence.RowPerfectionClosed

/-!
# Sequential perfection at weak limits of absorption paths

This module separates the jump-row part of weak-limit closure from the two
continuous-clock conditions.  The jump theorem consumes exactly the enhanced
source-jump approximation supplied by absorption-path compactness; plain weak
convergence does not expose the approximating jump times or product rows.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact player perfection at every nonterminal jump of a weak limit follows
from vanishing source perfection once every limit jump is realized by
convergent source jump rows. -/
theorem playerJumpRowsPerfect_of_sourceApproximatedWeakLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (errors : ℕ → ℝ) (paths : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) (player : ι)
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (herrors : Tendsto errors atTop (nhds 0))
    (hweak : WeaklyConvergesAbsorptionPaths paths limit)
    (hjumps : HasSourceApproximationsForLimitJumps paths limit)
    (hperfect : ∀ index,
      IsPlayerSequentiallyPerfectAbsorptionPath reward (paths index)
        player (errors index)) :
    ∀ time ∈ pathJumps limit.1, pathTotal limit.1 time < 1 →
      QuittingPlayerRowεPerfect reward
        (absorptionPathPayoff reward limit time)
        (absorptionPathJumpRoot limit time) player 0 := by
  intro time htime htotal
  let approximation := Classical.choice (hjumps time htime)
  have hsourceTotal : Tendsto (fun index ↦
      pathTotal (paths index).1 (approximation.sourceTimes index)) atTop
      (nhds (pathTotal limit.1 time)) := by
    unfold pathTotal
    exact tendsto_finsetSum Finset.univ fun coalition _ ↦
      approximation.values_tendsto coalition
  have hsourceNonterminal : ∀ᶠ index in atTop,
      pathTotal (paths index).1 (approximation.sourceTimes index) < 1 :=
    hsourceTotal.eventually (Iio_mem_nhds htotal)
  have hpayoff : Tendsto (fun index ↦
      absorptionPathPayoff reward (paths index)
        (approximation.sourceTimes index)) atTop
      (nhds (absorptionPathPayoff reward limit time)) := by
    apply absorptionPathPayoff_tendsto_of_value_tendsto reward
      (times := approximation.sourceTimes) (time := time)
    · exact fun index ↦ (approximation.source_jump index).1
    · exact htime.1
    · exact htotal
    · intro coalition
      exact (tendsto_pi_nhds.mp
        (hweak.tendsto_value_one hlimitBounded)) coalition
    · exact approximation.values_tendsto
  rw [← quittingRootOfSimplex_simplexOfRoot
    (absorptionPathJumpRoot limit time)]
  apply quittingPlayerRowεPerfect_of_tendsto reward player errors
    (fun index ↦ absorptionPathPayoff reward (paths index)
      (approximation.sourceTimes index))
    (fun index ↦ quittingSimplexOfRoot
      (absorptionPathJumpRoot (paths index) (approximation.sourceTimes index)))
    herrors hpayoff approximation.roots_tendsto
  filter_upwards [hsourceNonterminal] with index hnonterminal
  rw [quittingRootOfSimplex_simplexOfRoot]
  exact (hperfect index).1 (approximation.sourceTimes index)
    (approximation.source_jump index) hnonterminal

end GameTheory.QuittingAbsorptionPath
