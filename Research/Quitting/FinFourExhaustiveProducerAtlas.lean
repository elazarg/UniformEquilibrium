/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.CanonicalPairMinimumEndpointSupportRankHandoff
import Research.Quitting.FinFourProducerAtlas.ForcedPair
import Research.Quitting.FinFourProducerAtlas.ForcedPairMinimumTailConsumer
import Research.Quitting.FinFourProducerAtlas.LiteralNoGo
import Research.Quitting.FinFourProducerAtlas.MaximalPrefixRayDichotomy
import Research.Quitting.FinFourProducerAtlas.MinimumReturnForcedPair
import Research.Quitting.FinFourProducerAtlas.NormalizedReturn
import Research.Quitting.FinFourProducerAtlas.MonodromyImpossible
import Research.Quitting.FinFourProducerAtlas.PureNonsingletonCollisionScreening
import Research.Quitting.FinFourProducerAtlas.SemanticCoverage
import Research.Quitting.FinFourProducerAtlas.StrictEndpointNormalizedReturn
import Research.Quitting.FinFourProducerAtlas.StrongConcentratedPacketConsumer

/-!
# Exhaustive source-preserving producer atlas on four players

The atlas has six source-distinct tagged leaves, a four-node semantic
normalization, and an additive owner-clock compression to three directed
obligations.  The weak concentrated-singleton node now has a source-attached
strong packet and an exact strategic-versus-collision-minimum contraction.
Every weak singleton core also has a direct forced-pair collision residual
with an exact tail-escape-versus-minimum-tail paid dichotomy.  For singleton
minimum atoms, one chronology and table outsider fixed before every resolution
produce a cofinal moving packet whose collision residual is minimum-tail and
has one fixed paid label.
The resulting actual forced-pair family has a derived normalized passport:
its enlarged-slice minimum either returns to the global minimum and reaches
the three-role chord, or is a strict inert point with only all Continue as an
exact cap--Nash root.
The same family also has one canonical maximal-prefix semantic ray.  Its
scalar limit either returns the whole source to the minimum and reaches the
three-role consumer, or leaves a strict ray stall with invariant normalized
debt and support, vanishing future canonical charge, and a sharp retained-law
limit alternative.
In the minimum-return arm, the literal paid endpoint either stays on the
minimum fibre and makes a one-time support-rank handoff through its actual
half-mixture, or converges to a strictly off-minimum endpoint.  The stored
concentrated packet refines the same joint compactification subsequence.
The strict endpoint is normalized on a further refinement of that same
cluster: its normalized minimum either supplies the maintained strategic or
collision residual, or is an off-minimum unique-all-Continue inert point.
Pure collision screening sends every nonsingleton minimum atom into the same
consumer without a tail split or near-minimum selected row.
The same-stage monodromy leaf is impossible, so the exact coverage residual
contracts to four nonmonodromy tags.  The other coverage theorems and the
narrowly scoped local-exactification no-go are split into modules under
`Research.Quitting.FinFourProducerAtlas`.  No renewable canonical-pair rank
descent, normalized-inert or strict-stall consumer, or uniform-payoff
completion is asserted here.
-/
