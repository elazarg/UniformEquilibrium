/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Frozen.RadialResetCube
import UniformEquilibrium.Quitting.Debt.Dynamic.ExactChronologicalData

/-!
# Executable singleton data read from frozen common-source reset profiles

A schedule of active reset movers determines an executable product-root
sequence: at time `t`, use the live root of the scheduled mover's literal
frozen common-source radial reset profile.  The canonical reached-tail values and
debts therefore have exact prescribed and direct-debt recursion.  An optional
singleton projection is also recorded below.

This is the first producer field of chronological debt shadowing.  It does not
identify the resulting tail debt with a frozen reset-cube vertex or chord.
Such an identification would require the missing sequential reprojection
estimate: consecutive scheduled roots come from alternative whole profiles,
not from shifts of one reset profile.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.Probability.DiscreteHazard

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {witness : QuittingTerminalExploitabilityWitness reward}

namespace QuittingPositiveMinimumDebtTangentFamily

/-- The complete product root read at `time` from the scheduled literal
frozen common-source radial reset profile. -/
def frozenRadialScheduledRoot
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.positiveDebtSupport}) (time : ℕ) : ι → PMF Bool :=
  quittingProfileLiveRoot reward
    (frontier.frozenRadialResetProfile rank (schedule time)
      (weight (schedule time)) (hweight0 (schedule time))
      (hweight1 (schedule time))) time

/-- The scheduled mover's live marginal in its literal radial reset profile.
All other players are subsequently purified to Continue by
`frozenRadialSingletonRoot`. -/
def frozenRadialSingletonMarginal
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.positiveDebtSupport}) (time : ℕ) : PMF Bool :=
  frontier.frozenRadialScheduledRoot rank weight hweight0 hweight1
    schedule time (schedule time).1

/-- The executable singleton-purified root obtained from the scheduled reset
profile at one live time. -/
def frozenRadialSingletonRoot
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.positiveDebtSupport}) (time : ℕ) : ι → PMF Bool :=
  quittingSoloMixedRoot (schedule time).1
    (frontier.frozenRadialSingletonMarginal rank weight
      hweight0 hweight1 schedule time)

/-- The retained marginal is exactly the stopping-law mixture of the common
source hazard and its frozen common-source reset hazard at the same live time. -/
theorem frozenRadialSingletonMarginal_eq_convexMix
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.positiveDebtSupport}) (time : ℕ) :
    frontier.frozenRadialSingletonMarginal rank weight
        hweight0 hweight1 schedule time =
      BooleanHazard.convexMix
        (quittingBehaviorLiveHazard reward
          (frontier.source rank (schedule time).1))
        (quittingBehaviorLiveHazard reward
          (frontier.frozenRadialInnerResetStrategy rank (schedule time)))
        (weight (schedule time)) (hweight0 (schedule time))
        (hweight1 (schedule time)) time := by
  unfold frozenRadialSingletonMarginal
    frozenRadialScheduledRoot frozenRadialResetProfile
    quittingProfileLiveRoot
  rw [Function.update_self]
  rfl

@[simp]
theorem frozenRadialSingletonRoot_owner
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.positiveDebtSupport}) (time : ℕ) :
    frontier.frozenRadialSingletonRoot rank weight hweight0 hweight1
        schedule time (schedule time).1 =
      frontier.frozenRadialSingletonMarginal rank weight
        hweight0 hweight1 schedule time := by
  simp [frozenRadialSingletonRoot]

/-- Every nonscheduled player literally Continues at the produced root. -/
theorem frozenRadialSingletonRoot_of_ne
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.positiveDebtSupport}) (time : ℕ)
    (who : ι) (hne : who ≠ (schedule time).1) :
    frontier.frozenRadialSingletonRoot rank weight hweight0 hweight1
        schedule time who = PMF.pure false := by
  exact quittingSoloMixedRoot_of_ne hne _

/-- Canonical reached-tail values and debts of the executable scheduled
product roots.  No claim equates them with the frozen whole-profile endpoint
semantics. -/
def frozenRadialChronologicalData
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.positiveDebtSupport}) :
    QuittingChronologicalDebtData ι :=
  QuittingChronologicalDebtData.exactOfRoots reward
    (frontier.frozenRadialScheduledRoot rank weight
      hweight0 hweight1 schedule)

@[simp]
theorem frozenRadialChronologicalData_root
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.positiveDebtSupport}) (time : ℕ) :
    (frontier.frozenRadialChronologicalData rank weight
      hweight0 hweight1 schedule).root time =
      frontier.frozenRadialScheduledRoot rank weight
        hweight0 hweight1 schedule time := rfl

/-- The frozen common-source executable chronology has no prescribed-payoff
forcing: its candidate values are its literal reached-tail values. -/
@[simp]
theorem frozenRadialChronologicalData_prescribedDefect
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.positiveDebtSupport}) (time : ℕ) :
    (frontier.frozenRadialChronologicalData rank weight
      hweight0 hweight1 schedule).prescribedDefect reward time = 0 := by
  exact QuittingChronologicalDebtData.exactOfRoots_prescribedDefect
    reward _ time

/-- Its direct debt forcing is also exactly zero, because the candidate debt
is the literal reached-tail exploitability. -/
@[simp]
theorem frozenRadialChronologicalData_directDebtDefect
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.positiveDebtSupport}) (time : ℕ) :
    (frontier.frozenRadialChronologicalData rank weight
      hweight0 hweight1 schedule).directDebtDefect reward time = 0 := by
  exact QuittingChronologicalDebtData.exactOfRoots_directDebtDefect
    reward _ time

end QuittingPositiveMinimumDebtTangentFamily

end GameTheory
