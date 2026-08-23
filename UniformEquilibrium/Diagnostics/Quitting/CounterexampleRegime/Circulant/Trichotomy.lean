/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.UniformPayoffBridge
import UniformEquilibrium.Quitting.Classification.Circulant.Trichotomy

/-!
# Rotation-symmetric quitting tables of nonpositive surplus, against the regime

The circulant trichotomy of
`UniformEquilibrium/Quitting/Classification/Circulant/Trichotomy.lean` is
stated without reference to `QuittingCounterexampleRegime`.  This module reads
its two surplus branches against the regime, for a general group of players
and for the five-player case.

## Main results

* `isEmpty_counterexampleRegime_of_circulant_surplus_nonpos`
* `isEmpty_counterexampleRegime_of_circulant_surplus_eq_zero`
* `isEmpty_counterexampleRegime_of_pentagonCirculant_surplus_nonpos`
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {m : ι → ℝ}

/-- A circulant table of nonpositive surplus is in no counterexample
regime. -/
theorem isEmpty_counterexampleRegime_of_circulant_surplus_nonpos
    [Nontrivial ι] (h : HasCirculantSoloMatrix reward m)
    (hσ : (∑ d, m d) ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  isEmpty_quittingCounterexampleRegime_of_exists_uniformEquilibriumPayoff _
    (exists_uniformEquilibriumPayoff_of_circulant_surplus_nonpos h hσ)

/-- A circulant table of vanishing surplus is in no counterexample regime, by
the homogeneous branch. -/
theorem isEmpty_counterexampleRegime_of_circulant_surplus_eq_zero
    [Nontrivial ι] (h : HasCirculantSoloMatrix reward m)
    (hσ : (∑ d, m d) = 0) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  isEmpty_quittingCounterexampleRegime_of_exists_uniformEquilibriumPayoff _
    (exists_uniformEquilibriumPayoff_of_circulant_surplus_eq_zero h hσ)

section FivePlayers

/-- A five-player circulant table of nonpositive surplus is in no
counterexample regime. -/
theorem isEmpty_counterexampleRegime_of_pentagonCirculant_surplus_nonpos
    {reward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5)}
    {margin : ZMod 5 → ℝ} (h : HasCirculantSoloMatrix reward margin)
    (hσ : (∑ d, margin d) ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  isEmpty_quittingCounterexampleRegime_of_exists_uniformEquilibriumPayoff _
    (exists_uniformEquilibriumPayoff_of_pentagonCirculant_surplus_nonpos h hσ)

end FivePlayers

end QuittingLCPClassification
end GameTheory
