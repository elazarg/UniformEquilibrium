/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.LiteralNoGo
import Research.Quitting.FinFourProducerAtlas.SemanticCoverage
import Research.Quitting.FinFourProducerAtlas.StrongConcentratedPacketConsumer

/-!
# Exhaustive source-preserving producer atlas on four players

The atlas has six source-distinct tagged leaves, a four-node semantic
normalization, and an additive owner-clock compression to three directed
obligations.  The weak concentrated-singleton node now has a source-attached
strong packet and an exact strategic-versus-collision-minimum contraction.
The other coverage theorems and the narrowly scoped local-exactification no-go
are split into modules under `Research.Quitting.FinFourProducerAtlas`.  No
recursive descent or uniform-payoff completion is asserted here.
-/
