/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanFactory

/-!
# State matching obstruction for clipped reset edges

The floor-clipped reset certificate has a fixed tail simplex coordinate:
every such edge has tail `(target, quittingAllContinueSimplexRoot)`. A state
whose stored root has positive absorption cannot equal any such tail, because
the all-Continue root has zero absorption.

This is a state-space obstruction, independent of compactness or closedness.
It identifies the missing datum in any chronological reset argument: the next
target must be selected with the preceding root simplex coordinate, rather
than merely with a fresh all-Continue tail.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace ClippedStateMatchingObstruction

omit [DecidableEq ι] in
/-- A Nash--Bellman state with positive absorption in its stored root cannot
be identified with an all-Continue tail, independently of its payoff
coordinate. This is the exact state-matching obstruction used by clipped
reset edges. -/
theorem state_ne_allContinueTail_of_positiveAbsorption
    (state : QuittingNashBellmanPoint ι)
    (hpositive : 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex state.2))
    (target : Payoff ι) :
    state ≠ (target, quittingAllContinueSimplexRoot) := by
  intro hstate
  have hroot : state.2 = quittingAllContinueSimplexRoot :=
    congrArg Prod.snd hstate
  rw [hroot, quittingRootOfSimplex_allContinueSimplexRoot,
    quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability] at hpositive
  simp [quittingAllContinueRoot] at hpositive

end ClippedStateMatchingObstruction

end GameTheory
