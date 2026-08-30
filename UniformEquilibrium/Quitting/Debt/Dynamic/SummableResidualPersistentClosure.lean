/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.SummableResidualNashBellmanSpine

/-!
# Persistent summable-residual Nash--Bellman spines

A supplied summable-residual spine with two persistent marginal labels yields
a uniform-equilibrium payoff by passing to late suffixes.

This is a conditional consumer of a supplied spine.  This module does not
construct persistent labels or produce unbounded exact-block hazard capacity.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingSummableResidualNashBellmanSpine

/-- The suffix of a summable-residual spine. -/
def tail (spine : QuittingSummableResidualNashBellmanSpine reward)
    (start : ℕ) : QuittingSummableResidualNashBellmanSpine reward where
  roots time := spine.roots (start + time)
  value time := spine.value (start + time)
  bellmanError time := spine.bellmanError (start + time)
  nashError time := spine.nashError (start + time)
  value_bounded := by
    obtain ⟨bound, hbound⟩ := spine.value_bounded
    exact ⟨bound, fun time who => hbound (start + time) who⟩
  bellmanError_nonneg time := spine.bellmanError_nonneg (start + time)
  nashError_nonneg time := spine.nashError_nonneg (start + time)
  bellmanError_summable := by
    have hshift : Summable (fun time => spine.bellmanError (time + start)) :=
      (summable_nat_add_iff start).2 spine.bellmanError_summable
    simpa [Nat.add_comm] using hshift
  nashError_summable := by
    have hshift : Summable (fun time => spine.nashError (time + start)) :=
      (summable_nat_add_iff start).2 spine.nashError_summable
    simpa [Nat.add_comm] using hshift
  bellman time who := by
    simpa [Nat.add_assoc] using spine.bellman (start + time) who
  nash time := by
    simpa [Nat.add_assoc] using spine.nash (start + time)

theorem hasTwoPersistentQuittingMarginals_tail
    (spine : QuittingSummableResidualNashBellmanSpine reward)
    (hpersistent : HasTwoPersistentQuittingMarginals spine.roots)
    (start : ℕ) :
    HasTwoPersistentQuittingMarginals (spine.tail start).roots := by
  obtain ⟨first, second, hne, hfirst, hsecond⟩ := hpersistent
  refine ⟨first, second, hne, ?_, ?_⟩
  · intro hsummable
    apply hfirst
    apply (summable_nat_add_iff start).1
    change Summable (fun time =>
      quittingMarginalQuitHazard spine.roots first (start + time)) at hsummable
    simpa [Nat.add_comm] using hsummable
  · intro hsummable
    apply hsecond
    apply (summable_nat_add_iff start).1
    change Summable (fun time =>
      quittingMarginalQuitHazard spine.roots second (start + time)) at hsummable
    simpa [Nat.add_comm] using hsummable

theorem tendsto_tail_residualLedger_zero
    (spine : QuittingSummableResidualNashBellmanSpine reward) :
    Tendsto (fun start =>
      2 * (∑' time, (spine.tail start).bellmanError time) +
        ∑' time, (spine.tail start).nashError time) atTop (nhds 0) := by
  have _hbellman : Summable spine.bellmanError :=
    spine.bellmanError_summable
  have _hnash : Summable spine.nashError := spine.nashError_summable
  have hbellman : Tendsto
      (fun start => ∑' time, spine.bellmanError (start + time))
      atTop (nhds 0) := by
    simpa [Nat.add_comm] using tendsto_sum_nat_add spine.bellmanError
  have hnash : Tendsto
      (fun start => ∑' time, spine.nashError (start + time))
      atTop (nhds 0) := by
    simpa [Nat.add_comm] using tendsto_sum_nat_add spine.nashError
  simpa [tail] using (hbellman.const_mul 2).add hnash

/-- One summable-residual spine with two persistent labels already gives a
uniform-equilibrium payoff: sufficiently late suffixes have arbitrarily small
total residual ledger. -/
theorem exists_uniformEquilibriumPayoff_of_twoPersistent
    (spine : QuittingSummableResidualNashBellmanSpine reward)
    (hpersistent : HasTwoPersistentQuittingMarginals spine.roots) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_summableResidualSpines
  intro eta heta
  have heventually : ∀ᶠ start : ℕ in atTop,
      2 * (∑' time, (spine.tail start).bellmanError time) +
          ∑' time, (spine.tail start).nashError time < eta :=
    (tendsto_order.1 spine.tendsto_tail_residualLedger_zero).2 eta heta
  obtain ⟨start, hstart⟩ := heventually.exists
  exact ⟨spine.tail start, hstart.le,
    spine.hasTwoPersistentQuittingMarginals_tail hpersistent start⟩

end QuittingSummableResidualNashBellmanSpine
end GameTheory
