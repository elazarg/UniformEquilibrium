/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.AbnormalPlayers
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryLimitGeometry
import UniformEquilibrium.Quitting.Debt.Dynamic.PunishmentFloorViolation

/-!
# Punishment floors on summable exact Nash--Bellman tails

A bounded exact Nash--Bellman tail with summable joint absorption converges to
an all-Continue boundary whose coordinates dominate the corresponding
singleton rewards.  A value below its behavioral punishment floor, however,
propagates forward and cannot increase.  These two facts exclude every
punishment-floor violation by a normal player.

The tail is supplied as literal values and product roots.  No dynamic-debt
annotation, compact selector, or source-generation hypothesis is used.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A canonical exact Nash--Bellman spine gives an exact edge between each
pair of consecutive displayed values. -/
theorem IsCanonicalExactQuittingNashBellmanSpine.isQuittingNashBellmanEdge
    {value : ℕ → Payoff ι} {roots : ℕ → ι → PMF Bool}
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (time : ℕ) :
    IsQuittingNashBellmanEdge reward
      (value time, quittingSimplexOfRoot (roots time))
      (value (time + 1), quittingSimplexOfRoot (roots (time + 1))) := by
  constructor
  · simpa only [quittingRootOfSimplex_simplexOfRoot] using hspine.2.1 time
  · simpa only [quittingRootOfSimplex_simplexOfRoot,
      isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash] using
        hspine.2.2 time

/-- A punishment-floor violation along an exact Nash--Bellman spine persists
and bounds every later displayed value by the first violating value. -/
theorem IsCanonicalExactQuittingNashBellmanSpine.value_le_of_punishmentValue_violation
    {value : ℕ → Payoff ι} {roots : ℕ → ι → PMF Bool}
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (who : ι) {start : ℕ}
    (hviolation : value start who < quittingPunishmentValue reward who) :
    ∀ time, start ≤ time → value time who ≤ value start who := by
  intro time htime
  induction time, htime using Nat.le_induction with
  | base => exact le_rfl
  | succ time _ ih =>
      have hcurrent : value time who < quittingPunishmentValue reward who :=
        lt_of_le_of_lt ih hviolation
      exact (successorValue_le_current_of_punishmentValue_violation
        (value time, quittingSimplexOfRoot (roots time))
        (value (time + 1), quittingSimplexOfRoot (roots (time + 1)))
        (hspine.isQuittingNashBellmanEdge time) who hcurrent).trans ih

/-- Every normal player stays above the behavioral punishment floor at every
date of a bounded exact Nash--Bellman spine with summable joint absorption. -/
theorem IsCanonicalExactQuittingNashBellmanSpine.punishmentValue_le_of_normal_of_summable_absorption
    {value : ℕ → Payoff ι} {roots : ℕ → ι → PMF Bool}
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (who : ι) (hnormal : IsQuittingNormalPlayer reward who) (time : ℕ) :
    quittingPunishmentValue reward who ≤ value time who := by
  obtain ⟨boundary, hboundary, -⟩ :=
    exists_quittingAnnotationBoundary_of_summableAbsorption
      reward roots value hspine.2.1 (abs_reward_le_quittingRewardBound reward)
      hspine.1 hcharge
  have hsingleton : reward (quittingSingletonTerminal who) who ≤ boundary who :=
    quittingSingletonReward_le_annotationBoundary reward roots value
      hspine.2.1 hspine.2.2 boundary hboundary hcharge who
  by_contra hfloor
  push Not at hfloor
  have hlater : ∀ offset,
      value (time + offset) who ≤ value time who := by
    intro offset
    exact hspine.value_le_of_punishmentValue_violation who hfloor
      (time + offset) (Nat.le_add_right time offset)
  have hboundaryLe : boundary who ≤ value time who := by
    apply le_of_tendsto'
      ((hboundary who).comp (tendsto_add_atTop_nat time))
    intro offset
    simpa [Nat.add_comm] using hlater offset
  unfold IsQuittingNormalPlayer quittingSoloSelfPayoff at hnormal
  exact (not_lt_of_ge (hnormal.trans hsingleton))
    (lt_of_le_of_lt hboundaryLe hfloor)

/-- If every player is normal, every displayed value of a summable exact
Nash--Bellman spine lies coordinatewise above the punishment vector. -/
theorem IsCanonicalExactQuittingNashBellmanSpine.punishmentValue_le_of_all_normal_and_summable
    {value : ℕ → Payoff ι} {roots : ℕ → ι → PMF Bool}
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (hnormal : ∀ who, IsQuittingNormalPlayer reward who) :
    ∀ time who, quittingPunishmentValue reward who ≤ value time who := by
  intro time who
  exact hspine.punishmentValue_le_of_normal_of_summable_absorption
    hcharge who (hnormal who) time

end GameTheory
