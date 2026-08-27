/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.LiteralNoGo
import Research.Quitting.FinFourProducerAtlas.MonodromyImpossible
import Research.Quitting.FinFourProducerAtlas.PureNonsingletonCollisionScreening
import Research.Quitting.FinFourProducerAtlas.SemanticCoverage
import Research.Quitting.FinFourProducerAtlas.StrongConcentratedPacketConsumer

/-!
# Exhaustive source-preserving producer atlas on four players

The atlas has six source-distinct tagged leaves, a four-node semantic
normalization, and an additive owner-clock compression to three directed
obligations.  The weak concentrated-singleton node now has a source-attached
strong packet and an exact strategic-versus-collision-minimum contraction.
Pure collision screening sends every nonsingleton minimum atom into the same
consumer without a tail split or near-minimum selected row.
The same-stage monodromy leaf is impossible, so the exact coverage residual
contracts to four nonmonodromy tags.  The other coverage theorems and the
narrowly scoped local-exactification no-go are split into modules under
`Research.Quitting.FinFourProducerAtlas`.  No recursive descent or
uniform-payoff completion is asserted here.
-/
