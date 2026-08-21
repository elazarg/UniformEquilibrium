/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart

/-!
# Real hazard rows as quitting roots

Many papers specify a quitting profile as real probabilities in `[0,1]`, whereas the
stochastic-game semantics uses product roots `ι → PMF Bool`.  This file is the common adapter.
It sends each real hazard to its Bernoulli root, records the exact one-stage payoff bridge,
and defines the profile's tail payoff through the production terminal semantics.
-/

noncomputable section

namespace GameTheory

open Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A real quitting-hazard row, with every coordinate certified to lie in `[0,1]`. -/
abbrev QuittingHazardRow (ι : Type) := ι → Set.Icc (0 : ℝ) 1

/-- A time-indexed sequence of real quitting-hazard rows. -/
abbrev QuittingHazardProfile (ι : Type) := ℕ → QuittingHazardRow ι

/-- Convert a real hazard row into the corresponding product root of Bernoulli laws. -/
def quittingRootOfHazardRow (row : QuittingHazardRow ι) : ι → PMF Bool :=
  rootOfHazard (fun who => (row who : ℝ))
    (fun who => (row who).property.1) (fun who => (row who).property.2)

omit [Fintype ι] [DecidableEq ι] in
/-- The root constructed from a hazard row has exactly the prescribed quit probabilities. -/
@[simp] theorem quittingRootOfHazardRow_true_toReal
    (row : QuittingHazardRow ι) (who : ι) :
    ((quittingRootOfHazardRow row who) true).toReal = (row who : ℝ) := by
  simp [quittingRootOfHazardRow, rootOfHazard]

omit [Fintype ι] [DecidableEq ι] in
/-- Its Continue probability is one minus the prescribed hazard. -/
@[simp] theorem quittingRootOfHazardRow_false_toReal
    (row : QuittingHazardRow ι) (who : ι) :
    ((quittingRootOfHazardRow row who) false).toReal = 1 - (row who : ℝ) := by
  simp [quittingRootOfHazardRow, rootOfHazard]

omit [Fintype ι] [DecidableEq ι] in
/-- Reading real hazards back from the product root returns the original row. -/
@[simp] theorem hazardOfRoot_quittingRootOfHazardRow
    (row : QuittingHazardRow ι) :
    hazardOfRoot (quittingRootOfHazardRow row) = fun who => (row who : ℝ) := by
  funext who
  exact quittingRootOfHazardRow_true_toReal row who

/-- The probability that at least one player quits in a real hazard row. -/
def quittingHazardRowExitProbability (row : QuittingHazardRow ι) : ℝ :=
  1 - ∏ who, (1 - (row who : ℝ))

omit [DecidableEq ι] in
/-- Exit probability is one minus the production root's all-Continue mass. -/
theorem quittingHazardRowExitProbability_eq
    (row : QuittingHazardRow ι) :
    quittingHazardRowExitProbability row =
      1 - quittingStationaryContinueMass (quittingRootOfHazardRow row) := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [quittingHazardRowExitProbability]

/-- Probability that exactly `coalition` quits in a real hazard row. -/
def quittingHazardCoalitionProbability
    (row : QuittingHazardRow ι) (coalition : Finset ι) : ℝ :=
  coalitionMass (fun who => (row who : ℝ)) coalition

/-- Coalition probability is the production coalition mass of the associated root. -/
theorem quittingHazardCoalitionProbability_eq
    (row : QuittingHazardRow ι) (coalition : Finset ι) :
    quittingHazardCoalitionProbability row coalition =
      coalitionMass (hazardOfRoot (quittingRootOfHazardRow row)) coalition := by
  rw [hazardOfRoot_quittingRootOfHazardRow]
  rfl

/-- The one-stage payoff of a real hazard row with an all-Continue continuation vector. -/
def quittingHazardOneStagePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (row : QuittingHazardRow ι) : Payoff ι :=
  fun who => quittingRootExpectedPayoff reward continuation
    (quittingRootOfHazardRow row) who

/-- The real-row one-stage payoff is the exact coalition average plus the all-Continue
continuation term. -/
theorem quittingHazardOneStagePayoff_eq_coalitionSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (row : QuittingHazardRow ι) (who : ι) :
    quittingHazardOneStagePayoff reward continuation row who =
      ∑ coalition : Finset ι,
        quittingHazardCoalitionProbability row coalition *
          quittingStageCoalitionPayoff reward continuation coalition who := by
  rw [quittingHazardOneStagePayoff,
    quittingRootExpectedPayoff_eq_sum_coalitionMass]
  simp only [quittingHazardCoalitionProbability,
    hazardOfRoot_quittingRootOfHazardRow]

/-- Convert a time-indexed real hazard profile into production product roots. -/
def quittingRootsOfHazardProfile
    (profile : QuittingHazardProfile ι) : ℕ → ι → PMF Bool :=
  fun time => quittingRootOfHazardRow (profile time)

/-- Tail payoff of a real hazard profile, using the stochastic-game terminal semantics in
which nonabsorption has payoff zero. -/
def quittingHazardTailPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : QuittingHazardProfile ι) (start : ℕ) : Payoff ι :=
  fun who => quittingRootSequenceTerminalValue reward
    (quittingRootsOfHazardProfile profile) who start

omit [DecidableEq ι] in
/-- The tail payoff is the absolutely convergent series of survival-weighted absorbing
contributions. -/
theorem quittingHazardTailPayoff_eq_tsum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : QuittingHazardProfile ι) (start : ℕ) (who : ι) :
    quittingHazardTailPayoff reward profile start who =
      ∑' offset, quittingJointSurvivalWeight
          (quittingRootsOfHazardProfile profile) start offset *
        quittingRootAbsorbingContribution reward
          (quittingRootOfHazardRow (profile (start + offset))) who := by
  exact quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution
    reward (quittingRootsOfHazardProfile profile) who start

end GameTheory
