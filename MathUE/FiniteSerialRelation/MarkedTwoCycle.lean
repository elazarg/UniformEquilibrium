/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.FiniteSerialRelation

/-!
# The two-cycle part of a marked rooted lasso

The four-point marked-lasso classification has seventeen constructors.  This
decoder returns the literal cycle pair on the eight constructors whose cycle
has length two and returns `none` on the nine longer-cycle constructors.
-/

namespace Math.FiniteSerialRelation

variable {State : Type} [DecidableEq State]
variable {R : State → State → Prop} {root marker : State}

/-- Decode the literal cycle pair on exactly the two-cycle marked lasso
constructors. -/
def MarkedRootedLasso.twoCyclePair?
    (geometry : MarkedRootedLasso R root marker) : Option (Finset State) :=
  match geometry with
  | .rootedTwo_next geometry _ => some {root, geometry.next}
  | .rootedTwo_outside geometry _ => some {root, geometry.next}
  | .rootedThree_first _ _ => none
  | .rootedThree_second _ _ => none
  | .rootedThree_outside _ _ => none
  | .rootedFour_first _ _ => none
  | .rootedFour_second _ _ => none
  | .rootedFour_third _ _ => none
  | .oneToTwo_entry geometry _ => some {geometry.entry, geometry.other}
  | .oneToTwo_other geometry _ => some {geometry.entry, geometry.other}
  | .oneToTwo_outside geometry _ => some {geometry.entry, geometry.other}
  | .oneToThree_entry _ _ => none
  | .oneToThree_second _ _ => none
  | .oneToThree_third _ _ => none
  | .twoToTwo_first geometry _ => some {geometry.entry, geometry.other}
  | .twoToTwo_entry geometry _ => some {geometry.entry, geometry.other}
  | .twoToTwo_other geometry _ => some {geometry.entry, geometry.other}

/-- The complementary nine marked constructors, whose literal cycle has
length three or four. -/
def MarkedRootedLasso.HasLongCycle
    (geometry : MarkedRootedLasso R root marker) : Prop :=
  match geometry with
  | .rootedTwo_next _ _ => False
  | .rootedTwo_outside _ _ => False
  | .rootedThree_first _ _ => True
  | .rootedThree_second _ _ => True
  | .rootedThree_outside _ _ => True
  | .rootedFour_first _ _ => True
  | .rootedFour_second _ _ => True
  | .rootedFour_third _ _ => True
  | .oneToTwo_entry _ _ => False
  | .oneToTwo_other _ _ => False
  | .oneToTwo_outside _ _ => False
  | .oneToThree_entry _ _ => True
  | .oneToThree_second _ _ => True
  | .oneToThree_third _ _ => True
  | .twoToTwo_first _ _ => False
  | .twoToTwo_entry _ _ => False
  | .twoToTwo_other _ _ => False

/-- The decoder returns `none` exactly on the nine long-cycle marked
constructors. -/
theorem MarkedRootedLasso.twoCyclePair?_eq_none_iff_hasLongCycle
    (geometry : MarkedRootedLasso R root marker) :
    geometry.twoCyclePair? = none ↔ geometry.HasLongCycle := by
  cases geometry <;> simp [MarkedRootedLasso.twoCyclePair?,
    MarkedRootedLasso.HasLongCycle]

/-- In the `rootedTwo_next` constructor the decoded cycle pair is literally
the root/marker pair. -/
theorem MarkedRootedLasso.rootedTwoNext_twoCyclePair?_eq_root_marker
    (geometry : RootedTwoCycle R root) (marker_eq : marker = geometry.next) :
    (MarkedRootedLasso.rootedTwo_next geometry marker_eq).twoCyclePair? =
      some {root, marker} := by
  simp [MarkedRootedLasso.twoCyclePair?, marker_eq]

end Math.FiniteSerialRelation
