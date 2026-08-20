/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Fink.LimitIndexedCalendar

/-!
# Vanishing-discount compactness and calendars for Fink fixed points

This is the reader-facing umbrella for the Fink vanishing-discount limit
development.  Its declarations are organized sequentially in:

* `LimitCore`: compactness, harmonic-support structure, and subsequences;
* `LimitStationary`: endpoint continuity, stationary/interior compilers, and
  the fast fixed-point family;
* `LimitCorrectedTarget`: scheduled corrected-target calculus; and
* `LimitIndexedCalendar`: indexed calendars and public capstones.

The development extracts convergent subsequences from bounded discounted
Fink fixed points and exposes conditional compilers for uniform-equilibrium
payoffs.  It does not assert the unresolved stabilization or
excessive-function selection needed for the general multiplayer conjecture.
-/
