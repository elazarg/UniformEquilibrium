/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.SourceMatchedRadialResetCube
import UniformEquilibrium.Quitting.Debt.Dynamic.ExactChronologicalData

/-!
# Executable singleton data read from source-matched reset profiles

A schedule of active reset movers determines an executable product-root
sequence: at time `t`, use the live root of the scheduled mover's literal
source-matched radial reset profile.  The canonical reached-tail values and
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

namespace QuittingCounterexampleStoppingLawFrontier

/-- The complete product root read at `time` from the scheduled literal
source-matched radial reset profile. -/
def sourceMatchedRadialScheduledRoot
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.active}) (time : ℕ) : ι → PMF Bool :=
  quittingProfileLiveRoot reward
    (frontier.sourceMatchedRadialResetProfile rank (schedule time)
      (weight (schedule time)) (hweight0 (schedule time))
      (hweight1 (schedule time))) time

/-- The scheduled mover's live marginal in its literal radial reset profile.
All other players are subsequently purified to Continue by
`sourceMatchedRadialSingletonRoot`. -/
def sourceMatchedRadialSingletonMarginal
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.active}) (time : ℕ) : PMF Bool :=
  frontier.sourceMatchedRadialScheduledRoot rank weight hweight0 hweight1
    schedule time (schedule time).1

/-- The executable singleton-purified root obtained from the scheduled reset
profile at one live time. -/
def sourceMatchedRadialSingletonRoot
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.active}) (time : ℕ) : ι → PMF Bool :=
  quittingSoloMixedRoot (schedule time).1
    (frontier.sourceMatchedRadialSingletonMarginal rank weight
      hweight0 hweight1 schedule time)

/-- The retained marginal is exactly the stopping-law mixture of the common
source hazard and its source-matched reset hazard at the same live time. -/
theorem sourceMatchedRadialSingletonMarginal_eq_convexMix
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.active}) (time : ℕ) :
    frontier.sourceMatchedRadialSingletonMarginal rank weight
        hweight0 hweight1 schedule time =
      BooleanHazard.convexMix
        (quittingBehaviorLiveHazard reward
          (frontier.profiles (frontier.subseq rank) (schedule time).1))
        (quittingBehaviorLiveHazard reward
          (frontier.sourceMatchedInnerResetStrategy rank (schedule time)))
        (weight (schedule time)) (hweight0 (schedule time))
        (hweight1 (schedule time)) time := by
  unfold sourceMatchedRadialSingletonMarginal
    sourceMatchedRadialScheduledRoot sourceMatchedRadialResetProfile
    quittingProfileLiveRoot
  rw [Function.update_self]
  rfl

@[simp]
theorem sourceMatchedRadialSingletonRoot_owner
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.active}) (time : ℕ) :
    frontier.sourceMatchedRadialSingletonRoot rank weight hweight0 hweight1
        schedule time (schedule time).1 =
      frontier.sourceMatchedRadialSingletonMarginal rank weight
        hweight0 hweight1 schedule time := by
  simp [sourceMatchedRadialSingletonRoot]

/-- Every nonscheduled player literally Continues at the produced root. -/
theorem sourceMatchedRadialSingletonRoot_of_ne
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.active}) (time : ℕ)
    (who : ι) (hne : who ≠ (schedule time).1) :
    frontier.sourceMatchedRadialSingletonRoot rank weight hweight0 hweight1
        schedule time who = PMF.pure false := by
  exact quittingSoloMixedRoot_of_ne hne _

/-- Canonical reached-tail values and debts of the executable scheduled
product roots.  No claim equates them with the frozen whole-profile endpoint
semantics. -/
def sourceMatchedRadialChronologicalData
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.active}) :
    QuittingChronologicalDebtData ι :=
  QuittingChronologicalDebtData.exactOfRoots reward
    (frontier.sourceMatchedRadialScheduledRoot rank weight
      hweight0 hweight1 schedule)

@[simp]
theorem sourceMatchedRadialChronologicalData_root
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.active}) (time : ℕ) :
    (frontier.sourceMatchedRadialChronologicalData rank weight
      hweight0 hweight1 schedule).root time =
      frontier.sourceMatchedRadialScheduledRoot rank weight
        hweight0 hweight1 schedule time := rfl

/-- The source-matched executable chronology has no prescribed-payoff
forcing: its candidate values are its literal reached-tail values. -/
@[simp]
theorem sourceMatchedRadialChronologicalData_prescribedDefect
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.active}) (time : ℕ) :
    (frontier.sourceMatchedRadialChronologicalData rank weight
      hweight0 hweight1 schedule).prescribedDefect reward time = 0 := by
  exact QuittingChronologicalDebtData.exactOfRoots_prescribedDefect
    reward _ time

/-- Its direct debt forcing is also exactly zero, because the candidate debt
is the literal reached-tail exploitability. -/
@[simp]
theorem sourceMatchedRadialChronologicalData_directDebtDefect
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (schedule : ℕ → {who // who ∈ frontier.active}) (time : ℕ) :
    (frontier.sourceMatchedRadialChronologicalData rank weight
      hweight0 hweight1 schedule).directDebtDefect reward time = 0 := by
  exact QuittingChronologicalDebtData.exactOfRoots_directDebtDefect
    reward _ time

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
