/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Circulant.ColliderCompletion
import UniformEquilibrium.Quitting.Classification.Circulant.ColliderClosure

/-!
# The distant pocket and the collider-completion family, against the regime

`UniformEquilibrium/Quitting/Classification/Circulant/ColliderClosure.lean`
supplies a uniform-equilibrium payoff for the distant pocket, the one sign
pattern of the five-player collider completion left open by
`UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/Circulant/ColliderCompletion.lean`,
without reference to `QuittingCounterexampleRegime`. This module reads that
payoff against the regime, and closes the whole family.

## Main results

* `isEmpty_counterexampleRegime_colliderDistantPocket` — the distant pocket
  carries no counterexample regime
* `isEmpty_counterexampleRegime_colliderReward` — no five-player collider
  completion with vanishing distance-zero margin, nonnegative solo self value,
  and nonpositive joint value carries a counterexample regime
-/

noncomputable section

namespace GameTheory
namespace CirculantColliderCompletion

variable {s low : ℝ} {m : ZMod 5 → ℝ}

/-- The distant pocket, as emptiness of the counterexample regime. -/
theorem isEmpty_counterexampleRegime_colliderDistantPocket
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ 0)
    (hm1 : 0 ≤ m 1) (hm2 : m 2 < 0) (hm3 : m 3 < 0) (hm4 : 0 ≤ m 4)
    (hsum : 0 < m 1 + m 2 + m 3 + m 4) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) :=
  isEmpty_quittingCounterexampleRegime_of_exists_uniformEquilibriumPayoff _
    (exists_uniformEquilibriumPayoff_colliderDistantPocket hm0 hs hlow hm1 hm2
      hm3 hm4 hsum)

/-- **The collider-completion family carries no counterexample regime.**  Every
five-player collider completion whose margin at distance zero vanishes, whose
solo self value is nonnegative and whose joint value is nonpositive has an
ordinary uniform-equilibrium payoff.  No sign pattern, screen, or regime
hypothesis is left over. -/
theorem isEmpty_counterexampleRegime_colliderReward
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) := by
  rcases isEmpty_counterexampleRegime_or_distantPocket hm0 hs hlow with
    hempty | ⟨hsum, hm2, hm3, hm4, hm1⟩
  · exact hempty
  · exact isEmpty_counterexampleRegime_colliderDistantPocket hm0 hs hlow hm1 hm2
      hm3 hm4 hsum

end CirculantColliderCompletion
end GameTheory
