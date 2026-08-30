/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Finset.Basic

/-! # Labelled terminal outcomes of a quitting game -/

namespace GameTheory

/-- Terminal outcomes consist of Never and one atom for every nonempty
quitting coalition. -/
abbrev QuittingTerminalOutcome (ι : Type) :=
  Option {S : Finset ι // S.Nonempty}

end GameTheory
