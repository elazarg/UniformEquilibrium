/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import Maths.Recursion.TransferSummary
import MathUE.MaxAffineStoppingValue

/-! The generic transfer-summary algebra lives in `Maths.Recursion.TransferSummary`.

This project module retains only the bridge to the project-owned stopping-system
interface; keeping the bridge here avoids duplicating the upstream algebra.
-/

namespace Maths.TransferSummary.MaxAffineSummary

/-- `Math.MaxAffineStopping.System.Φ` is the max-affine action at the system's
coefficients `(A, T, P)`. -/
theorem apply_mk_eq_Φ (s : Math.MaxAffineStopping.System) (w : ℝ) :
    (mk s.A s.T s.P).apply w = s.Φ w := rfl

end Maths.TransferSummary.MaxAffineSummary
