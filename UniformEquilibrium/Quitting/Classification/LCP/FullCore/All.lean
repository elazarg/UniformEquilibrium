/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockChargedReturn
import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockJointBlockEquilibrium
import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockRationalPolyhedralBlock
import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockReducedSingletonLassoBarrier
import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockGlobalContraction
import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockSharperBound
import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockIntegerTablePeriodThree

/-!
# Four-player full-core classification results

This umbrella exports exact carrier dynamics for the displayed four-player
deadlock matrix, the universal contraction theorem for every reward completion
with that normalized singleton matrix, and an exact period-three uniform payoff
for the literal integer-table completion. The latter theorem does not include a
stationary-exclusion result.
-/
