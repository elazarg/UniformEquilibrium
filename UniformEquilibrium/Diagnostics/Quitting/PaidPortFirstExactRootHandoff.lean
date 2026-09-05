/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.PeriodOneOffMinimumPaidPort
import UniformEquilibrium.Diagnostics.Quitting.FirstExactRootStationaryDichotomy

/-! # A paid stationary port supplies the first exact-root cap-pin source -/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {root : ℕ → ι → PMF Bool}

/-- The same root family and fixed payer supply the cap-pin source. Its
positive reward bound is derived from the finite reward table. -/
def StationaryOffMinimumQuitNowPort.toCapPinSource
    (port : StationaryOffMinimumQuitNowPort reward root) :
    StationaryQuitNowCapPinSource reward where
  tailRoot := root
  player := port.payer
  gamma := port.gain
  bound := max 1 (quittingRewardBound reward)
  gamma_pos := port.gain_pos
  bound_pos := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  reward_bound := fun terminal who ↦
    (abs_reward_le_quittingRewardBound reward terminal who).trans (le_max_right _ _)
  pin := by
    filter_upwards [port.eventually_paid] with index hp
    refine ⟨?_, hp.1⟩
    unfold quittingTerminalDeviationDebt
    rw [← hp.1]
    exact hp.2.1
  cap_limit := port.cap_tendsto

@[simp] theorem StationaryOffMinimumQuitNowPort.toCapPinSource_profile
    (port : StationaryOffMinimumQuitNowPort reward root) (index : ℕ) :
    port.toCapPinSource.profile index = quittingStationaryProfile reward (root index) := rfl

/-- Any exact roots over this actual port source enter the checked first-root
survival-or-sure-owner dichotomy, without a minimum-ancestry assumption. -/
theorem StationaryOffMinimumQuitNowPort.firstExactRoot_dichotomy
    (port : StationaryOffMinimumQuitNowPort reward root)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (newRoot : ℕ → ι → PMF Bool)
    (hnash : ∀ index, IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward (quittingStationaryProfile reward (root index))).1
        0 (newRoot index)) :
    Nonempty (FirstStationaryRootDichotomy port.toCapPinSource newRoot) :=
  port.toCapPinSource.firstExactRoot_dichotomy hno newRoot hnash

end GameTheory
