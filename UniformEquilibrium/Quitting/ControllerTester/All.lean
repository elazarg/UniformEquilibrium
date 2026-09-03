/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.ControllerTester.ForwardLedger
import UniformEquilibrium.Quitting.ControllerTester.FiniteHorizonExploitability
import UniformEquilibrium.Quitting.ControllerTester.TesterFlowDuality
import UniformEquilibrium.Quitting.ControllerTester.ControllerValue
import UniformEquilibrium.Quitting.ControllerTester.FiniteWordValue
import UniformEquilibrium.Quitting.ControllerTester.FunctionBarrierDuality
import UniformEquilibrium.Quitting.ControllerTester.BarrierDuality
import UniformEquilibrium.Quitting.ControllerTester.UniformHorizonValue

/-!
# Controller--tester value and barrier duality

This umbrella exposes the exact forward ledger, unrestricted behavioral
finite-horizon tester, compact and finite-word controller values, box-local
function barrier, closed invariant barrier, and uniform-horizon value.
-/
