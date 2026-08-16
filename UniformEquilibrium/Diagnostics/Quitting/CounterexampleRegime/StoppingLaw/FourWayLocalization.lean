/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.ThreeWayLocalization

/-!
# Compatibility import for the former four-way localization module

The canonical exhaustive result is now `threeWayLocalization`. This module
retains only the old import path for source links and downstream imports; the
counterexample-regime umbrella reaches that result transitively through this
compatibility import. It defines no prescribed-comparison branch or legacy
four-way theorem.
-/
