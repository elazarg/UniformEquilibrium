/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Instances.Real.Lemmas
import UniformEquilibrium.Quitting.Root.ForcedContinuePayoffDisplacement

/-!
# Finite variation of forced-Continue child payoff displacement

If source and child Bellman sequences differ by forcing one fixed owner to
Continue at every new root, then summable forced-root absorption and summable
owner Quit probability make every coordinate's adjacent payoff-displacement
increments absolutely summable.  Only the increments are asserted summable;
the displacement values themselves need not be.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Minimal-hypothesis finite variation: summability of the two literal
charges appearing in the sharp one-step estimate implies summability of the
absolute displacement increments. -/
theorem summable_abs_terminalChildPayoffDisplacement_increment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source child : ℕ → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : ∀ time player, |source time player| ≤ M)
    (hchild : ∀ time player, |child time player| ≤ M)
    (hsourceNext : ∀ time, source (time + 1) =
      quittingRootSuccessorPayoff reward (source time) (roots time))
    (hchildNext : ∀ time, child (time + 1) =
      quittingRootSuccessorPayoff reward (child time)
        (Function.update (roots time) owner (PMF.pure false)))
    (hforcedAbsorption : Summable (fun time =>
      quittingRootAbsorptionMass
        (Function.update (roots time) owner (PMF.pure false))))
    (hownerHazard : Summable (fun time =>
      ((roots time owner) true).toReal)) :
    Summable (fun time =>
      |(child (time + 1) who - source (time + 1) who) -
        (child time who - source time who)|) := by
  have hM : 0 ≤ M :=
    (abs_nonneg (source 0 who)).trans (hsource 0 who)
  have hfirst : Summable (fun time =>
      2 * M * quittingRootAbsorptionMass
        (Function.update (roots time) owner (PMF.pure false))) :=
    hforcedAbsorption.mul_left (2 * M)
  have hsecond : Summable (fun time =>
      2 * M * ((roots time owner) true).toReal) :=
    hownerHazard.mul_left (2 * M)
  apply (hfirst.add hsecond).of_nonneg_of_le
  · intro time
    exact abs_nonneg _
  · intro time
    exact abs_terminalChildPayoffDisplacement_next_sub_le
      reward (source time) (child time) (source (time + 1))
        (child (time + 1)) (roots time) owner who hreward
        (hsource time) (hchild time) (hsourceNext time) (hchildNext time)

/-- Absolute summability of adjacent displacement increments gives a finite
real limit for the full displacement sequence. -/
theorem exists_tendsto_terminalChildPayoffDisplacement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source child : ℕ → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : ∀ time player, |source time player| ≤ M)
    (hchild : ∀ time player, |child time player| ≤ M)
    (hsourceNext : ∀ time, source (time + 1) =
      quittingRootSuccessorPayoff reward (source time) (roots time))
    (hchildNext : ∀ time, child (time + 1) =
      quittingRootSuccessorPayoff reward (child time)
        (Function.update (roots time) owner (PMF.pure false)))
    (hforcedAbsorption : Summable (fun time =>
      quittingRootAbsorptionMass
        (Function.update (roots time) owner (PMF.pure false))))
    (hownerHazard : Summable (fun time =>
      ((roots time owner) true).toReal)) :
    ∃ limit : ℝ, Tendsto
      (fun time => child time who - source time who) atTop (nhds limit) := by
  have hincrements :=
    summable_abs_terminalChildPayoffDisplacement_increment
      reward source child roots owner who hreward hsource hchild
        hsourceNext hchildNext hforcedAbsorption hownerHazard
  have hdist : Summable (fun time =>
      dist (child time who - source time who)
        (child (time + 1) who - source (time + 1) who)) := by
    apply hincrements.congr
    intro time
    rw [Real.dist_eq, abs_sub_comm]
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)

end GameTheory
