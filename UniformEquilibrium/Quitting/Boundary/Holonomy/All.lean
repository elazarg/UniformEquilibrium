/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.Compactness
import UniformEquilibrium.Quitting.Boundary.Holonomy.RealizedTangent
import UniformEquilibrium.Quitting.Boundary.Holonomy.AllTailRepairValue
import UniformEquilibrium.Quitting.Boundary.Holonomy.BehavioralTailEvaluation
import UniformEquilibrium.Quitting.Boundary.Holonomy.BehavioralTailRepairValue
import UniformEquilibrium.Quitting.Boundary.Holonomy.BehavioralTailGainDensity
import UniformEquilibrium.Quitting.Boundary.Holonomy.InfiniteBehavioralTailEvaluation
import UniformEquilibrium.Quitting.Boundary.Holonomy.AggregatePrefixConsumption
import UniformEquilibrium.Quitting.Boundary.Holonomy.AggregateTerminalAnchor
import UniformEquilibrium.Quitting.Boundary.Holonomy.QuantitativeAggregateTerminalAnchor
import UniformEquilibrium.Quitting.Boundary.Holonomy.Transport
import UniformEquilibrium.Quitting.Boundary.Holonomy.TransportGraph

/-!
# Boundary holonomy for finite quitting blocks

Public umbrella for the finite-boundary-holonomy family.

The source-retaining branch packages actual finite root blocks and proves
compactness at fixed cutoff or fixed last stage.  The coefficient branch gives
affine and max-affine residual cocycles, self-similarity, absorbed-mass tangent
normal forms, realized first-order bounds, and compact coordinate
subsequences.

These are complementary interfaces.  Fixed-cutoff compactness retains the
strategic source but does not cover escaping block length.  Tangent-coordinate
compactness covers coefficient projections but does not prove that the
limiting coordinates are realized by a strategic block, retain a source path,
or admit a strategic decoder.

The directed-transport adapter embeds prescribed and best-response summaries
as generic max-affine labels. It preserves evaluation and realized block
composition, exposes the actual opponent-survival slope and its unit bound,
and records that Bellman transport runs from a block's exit back to its entry.
The source-matched transport graph retains literal entry and exit times;
strict time descent excludes nonempty closed walks, so every finite graph of
unquotiented chronological blocks has a playerwise lax best-response section.

The fixed-prefix repair interface evaluates a bounded prescribed/best-response
boundary pair through the affine/max-affine holonomy.  Its gain modulus is
uniform over every pair in the boundary box and therefore survives an infimum
over any one source-independent tail family.  It does not construct or certify
the pairs as tails.  The behavioral-tail adapter identifies prescribed payoff
through an actual phase switch and the finite all-behavior envelope through the
same holonomy.  The corresponding infinite-tail envelope identity remains a
separate theorem: the infinite adapter proves it by realizing the early
Bellman branch and approximating the attached tail's behavioral supremum.  It
identifies same-tail holonomy gain, and hence its infimum over tails, with
literal terminal exploitability of the phase-switch profile.

The boundary-pair modulus transports the three-cap semantic density theorem
through every actual finite prefix.  Consequently finite elementary capped
tails and arbitrary behavioral tails have exactly the same repair-value
infimum; neither infimum is assumed attained and elementary code length may
depend on the requested accuracy.

For the complete canonical aggregate-minimizing prefix, physical Never reads
the exact dynamic-debt vector.  Hence its all-tail repair value is at most the
aggregate optimum, while quantitative marked-owner selection charges that
optimum to a separated terminal packet.  A positive canonical prefix floor
therefore forces an explicit positive packet scale; this is normalization for,
not construction of, a calibrated replacement.

The behavioral-tail repair value specializes the abstract fixed family to the
prescribed/envelope pair co-realized by each actual tail and inherits the same
Lipschitz and buffered repair/obstruction laws.  The aggregate terminal anchor
keeps the marked packet on the optimizer controlled by the calibrated
prepend-loss theorem; it is intentionally distinct from the min--max anchor.
-/
