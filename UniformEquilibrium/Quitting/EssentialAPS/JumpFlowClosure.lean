/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.ProperSingletonFlowClosure
import UniformEquilibrium.Quitting.Root.ExactSuccessorClosure

/-! # One singleton-flow segment before one exact product-root jump -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- One proper viable singleton segment may precede one exact product-root
jump from a supplied uniform-payoff continuation. -/
theorem isUniformEquilibriumPayoff_singletonArc_before_rootSuccessor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (rootTail : Payoff ι) (root : ι → PMF Bool)
    (hrootTail : (quittingGame reward).IsUniformEquilibriumPayoff none rootTail)
    (hrootNash : IsεQuittingRootNash reward rootTail 0 root)
    (owner : ι) (p : ℝ) (source : Payoff ι)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (harc : source = quittingSingletonArcPayoff p
      (quittingSoloReward reward owner)
      (quittingRootSuccessorPayoff reward rootTail root))
    (hactive : source owner = quittingSoloReward reward owner owner)
    (hsourceViable : QuittingEssentialAPSViable reward source)
    (hjumpViable : QuittingEssentialAPSViable reward
      (quittingRootSuccessorPayoff reward rootTail root)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none source := by
  apply isUniformEquilibriumPayoff_singletonArc_of_viable_proper
    reward owner p source (quittingRootSuccessorPayoff reward rootTail root)
    hp harc hactive hsourceViable hjumpViable
  exact isUniformEquilibriumPayoff_rootSuccessor_of_isZeroRootNash
    reward rootTail root hrootTail hrootNash

end GameTheory
