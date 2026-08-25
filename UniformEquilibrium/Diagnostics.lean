/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import UniformEquilibrium.Diagnostics.Uniform.Consequences
import UniformEquilibrium.Diagnostics.Uniform.PaddedDuplicateLotterySeparation
import UniformEquilibrium.Diagnostics.Uniform.HiddenFiberSpanCounterexample
import UniformEquilibrium.Diagnostics.Uniform.NonexistenceCertificate
import UniformEquilibrium.Diagnostics.PrivateRecommendationTargetAbsorbingLift
import UniformEquilibrium.Diagnostics.Quitting.All
import UniformEquilibrium.Diagnostics.Quitting.Collision.SparePlayerCancellation

/-!
# Integrated diagnostics umbrella

This umbrella owns the exhaustive diagnostics inventory.  Production modules
should import the narrow declaration files they use; `UniformEquilibrium` is
the production umbrella and deliberately does not pull this inventory in.
-/
