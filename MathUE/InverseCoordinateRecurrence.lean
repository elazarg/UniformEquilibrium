/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import Maths.Recursion.InverseCoordinate
import Maths.Recursion.TransferSummary

/-! The inverse-coordinate recurrence is provided by
`Maths.Recursion.InverseCoordinate`. This project module retains the one
compatibility theorem that identifies its affine step with the generic
transfer-summary action.
-/

namespace Maths.InverseCoordinate

/-- The unbundled affine step is the action of a bundled affine summary. -/
theorem affineStep_eq_apply (c d x : ℝ) :
    affineStep c d x = (_root_.Maths.TransferSummary.AffineSummary.mk d c).apply x :=
  add_comm (c * x) d

end Maths.InverseCoordinate
