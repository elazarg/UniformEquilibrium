/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorInfiniteOrbit

/-!
# Finite segments of an infinite punishment-floor orbit

Every finite interval of one exact punishment-floor orbit is itself an exact
finite prefix, anchored at the interval's first value.  This is the literal
chronology adapter needed when recurrence is observed away from time zero.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingPunishmentFloorInfiniteOrbit

/-- The finite interval of length `horizon` starting at `start`, with the
original roots and payoff values retained literally. -/
def toFiniteSegment
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (start horizon : ℕ) : QuittingPunishmentFloorFinitePrefix reward where
  roots time := orbit.roots (start + time)
  value time := orbit.value (start + time)
  horizon := horizon
  value_mem := fun time _ ↦ orbit.value_mem (start + time)
  anchor_floor := by
    intro who
    rw [Nat.add_zero]
    exact quittingPunishmentValue_le_finitePrefixValue
      (orbit.toFinitePrefix start) start le_rfl who
  policy := by
    intro time _
    simpa only [Nat.add_assoc] using orbit.policy (start + time)
  exactNash := fun time _ ↦ orbit.exactNash (start + time)

@[simp] theorem toFiniteSegment_value_zero
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (start horizon : ℕ) :
    (orbit.toFiniteSegment start horizon).value 0 = orbit.value start := by
  simp [toFiniteSegment]

@[simp] theorem toFiniteSegment_value_horizon
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (start horizon : ℕ) :
    (orbit.toFiniteSegment start horizon).value horizon =
      orbit.value (start + horizon) := rfl

@[simp] theorem toFiniteSegment_roots
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (start horizon time : ℕ) :
    (orbit.toFiniteSegment start horizon).roots time =
      orbit.roots (start + time) := rfl

end QuittingPunishmentFloorInfiniteOrbit

end GameTheory
