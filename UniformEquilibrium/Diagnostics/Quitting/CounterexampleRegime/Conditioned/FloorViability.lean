/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Ballisticity
import UniformEquilibrium.Quitting.Cycles.ConditionedFloorViability

/-!
# Conditioned punishment-floor viability at a counterexample seam

This adapter applies the generic conditioned-floor accounting to the canonical
dynamic-debt tail selected by a counterexample seam. It identifies the exact
phantom-plateau slack that funds any punishment-floor violation and records
the survival cost of affine repair.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleDynamicTailWitness

variable {regime : QuittingCounterexampleRegime reward}
    (seam : QuittingCounterexampleDynamicTailWitness regime)

/-- The optimized tail value after removing the positive-survival phantom
boundary and conditioning on eventual absorption. -/
def conditionedTailValue (time : ℕ) : Payoff ι :=
  quittingTailConditionedValue
    (quittingDynamicDebtTailRoots seam.tail)
    (fun date ↦ (seam.tail date).1.1) seam.limit.value time

/-- The conditioned annotation is the honest terminal delivery divided by
the remaining eventual-absorption probability. -/
theorem conditionedTailValue_eq_terminalValue_div (time : ℕ) :
    seam.conditionedTailValue time = fun who ↦
      quittingRootSequenceTerminalValue reward
          (quittingDynamicDebtTailRoots seam.tail) who time /
        quittingTailEventualAbsorption
          (quittingDynamicDebtTailRoots seam.tail) time := by
  apply quittingTailConditionedValue_eq_terminalValue_div
    (reward := reward)
  · exact fun date ↦ (seam.tail_edge date).1.1
  · exact seam.value_tendsto

/-- The conditioned floor deficit of the canonical counterexample tail is
bounded by the corresponding strict slack at its phantom plateau. -/
theorem eventualAbsorption_mul_conditionedPunishmentDeficit_le
    (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time) :
    quittingTailEventualAbsorption
          (quittingDynamicDebtTailRoots seam.tail) time *
        (quittingPunishmentValue reward who -
          seam.conditionedTailValue time who) ≤
      quittingJointSurvivalLimit
          (quittingDynamicDebtTailRoots seam.tail) time *
        (seam.limit.value who - quittingPunishmentValue reward who) := by
  exact quittingTailEventualAbsorption_mul_conditionedFloorDeficit_le
    (quittingDynamicDebtTailRoots seam.tail)
    (fun date ↦ (seam.tail date).1.1) seam.limit.value
    (quittingPunishmentValue reward) time who hpositive
    (seam.punishmentValue_le_tailValue time who)

/-- Every coordinate on the tight plateau face remains punishment-rational
after conditioning, at every date where eventual absorption is positive. -/
theorem punishmentValue_le_conditionedTailValue_of_limit_tight
    (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (htight : seam.limit.value who = quittingPunishmentValue reward who) :
    quittingPunishmentValue reward who ≤
      seam.conditionedTailValue time who := by
  exact floor_le_quittingTailConditionedValue_of_boundary_eq_floor
    (quittingDynamicDebtTailRoots seam.tail)
    (fun date ↦ (seam.tail date).1.1) seam.limit.value
    (quittingPunishmentValue reward) time who hpositive
    htight (seam.punishmentValue_le_tailValue time who)

/-- A conditioned punishment-floor violation forces strict plateau slack in
the same coordinate. -/
theorem punishmentValue_lt_limitValue_of_conditionedTailValue_lt
    (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hviolation : seam.conditionedTailValue time who <
      quittingPunishmentValue reward who) :
    quittingPunishmentValue reward who < seam.limit.value who := by
  exact boundary_gt_floor_of_quittingTailConditionedValue_lt_floor
    (quittingDynamicDebtTailRoots seam.tail)
    (fun date ↦ (seam.tail date).1.1) seam.limit.value
    (quittingPunishmentValue reward) time who hpositive
    (seam.punishmentValue_le_tailValue time who) hviolation

/-- At each conditionable date, either the whole conditioned vector is above
the punishment floor, or one explicit violating coordinate is funded by
strict phantom-plateau slack and satisfies the quantitative deficit budget. -/
theorem conditionedTail_floor_or_strictPlateauSlack
    (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time) :
    (∀ who, quittingPunishmentValue reward who ≤
        seam.conditionedTailValue time who) ∨
      ∃ who,
        seam.conditionedTailValue time who <
            quittingPunishmentValue reward who ∧
          quittingPunishmentValue reward who < seam.limit.value who ∧
          quittingTailEventualAbsorption
                (quittingDynamicDebtTailRoots seam.tail) time *
              (quittingPunishmentValue reward who -
                seam.conditionedTailValue time who) ≤
            quittingJointSurvivalLimit
                (quittingDynamicDebtTailRoots seam.tail) time *
              (seam.limit.value who -
                quittingPunishmentValue reward who) := by
  classical
  by_cases hall : ∀ who, quittingPunishmentValue reward who ≤
      seam.conditionedTailValue time who
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨who, hviolation⟩ := hall
    exact Or.inr ⟨who, hviolation,
      seam.punishmentValue_lt_limitValue_of_conditionedTailValue_lt
        time who hpositive hviolation,
      seam.eventualAbsorption_mul_conditionedPunishmentDeficit_le
        time who hpositive⟩

/-- Although conditioning can cross the punishment floor, every conditioned
state admits a common strictly positive affine move toward the phantom
boundary that restores all punishment coordinates simultaneously. -/
theorem exists_pos_scale_conditionedTailAffineShrink_floor
    (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time) :
    ∃ scale : ℝ, 0 < scale ∧ scale ≤ 1 ∧ ∀ who,
      quittingPunishmentValue reward who ≤
        quittingConditionedAffineShrink seam.limit.value
          (seam.conditionedTailValue time) scale who := by
  apply exists_pos_scale_floor_le_quittingConditionedAffineShrink
  · exact seam.punishmentValue_le_limitValue
  · intro who htight
    exact seam.punishmentValue_le_conditionedTailValue_of_limit_tight
      time who hpositive htight

/-- **No-free-lunch for a viable affine shrink of the canonical tail.**
Suppose every conditioned date is defined and a unit-interval scale is
transported by exact coefficient matching.  The putative rescaled absorption
weights `scale_t * alpha_t` leave at least `1 - scale_0` survival after every
finite horizon.  Thus any nontrivial initial shrink toward the floor-safe
phantom boundary recreates a positive Never component. -/
theorem one_sub_scale_zero_le_conditionedTailAffineShrink_survival
    (scale : ℕ → ℝ)
    (hscale : ∀ time, scale time ∈ Set.Icc 0 1)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (htransport : ∀ time,
      (1 - scale time *
          quittingTailConditionedAbsorptionWeight
            (quittingDynamicDebtTailRoots seam.tail) time) *
          (1 - scale (time + 1)) =
        1 - scale time)
    (fuel : ℕ) :
    1 - scale 0 ≤
      ∏ time ∈ Finset.range fuel,
        (1 - scale time *
          quittingTailConditionedAbsorptionWeight
            (quittingDynamicDebtTailRoots seam.tail) time) := by
  let alpha : ℕ → ℝ := fun time ↦
    quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail) time
  have halpha : ∀ time, alpha time ∈ Set.Icc 0 1 := by
    intro time
    exact (quittingTailConditionedWeights_mem_unitInterval
      (quittingDynamicDebtTailRoots seam.tail) time
      (hpositive (time + 1)).le (hpositive time)).1
  apply one_sub_scale_zero_le_quittingConditionedAffineShrink_survival
    alpha scale
  · intro time
    constructor
    · exact mul_nonneg (hscale time).1 (halpha time).1
    · calc
        scale time * alpha time ≤ 1 * alpha time :=
          mul_le_mul_of_nonneg_right (hscale time).2 (halpha time).1
        _ ≤ 1 := by simpa using (halpha time).2
  · exact fun time ↦ (hscale time).1
  · exact htransport

/-- If the phantom plateau is the punishment vector coordinatewise, the
entire conditioned tail is floor-admissible wherever conditioning is
defined. -/
theorem punishmentValue_le_conditionedTailValue_of_limit_eq_punishment
    (hboundary : seam.limit.value = quittingPunishmentValue reward)
    (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (who : ι) :
    quittingPunishmentValue reward who ≤
      seam.conditionedTailValue time who := by
  apply seam.punishmentValue_le_conditionedTailValue_of_limit_tight
    time who hpositive
  exact congrFun hboundary who

end QuittingCounterexampleDynamicTailWitness

end GameTheory
