/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.RetainedTailFiniteTimingRealization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence

/-!
# Final-stage coalition mass of a finite timing law

The behavioral realization of independent finite timing laws has a literal
last-stage coalition atom.  At the final displayed date, members of the
coalition must choose that date and every nonmember must choose `Never`.
This module identifies the actual behavioral stage mass with that finite
product exactly.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.Probability.DiscreteHazard

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Survival of one finite timing-law realization through its whole word is
exactly its declared `Never` mass. -/
theorem quittingFiniteDeadlineTimingProfile_hazardSurvival_eq_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    quittingHazardSurvival
        (quittingBehaviorLiveHazard reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed who))
        deadline =
      (mixed who none).toReal := by
  have hstack := quittingRetainedTailMixedTimingRootStack_ownSurvival_eq_none
    reward deadline mixed who
  unfold quittingLiteralRootStackOwnSurvival
    quittingRetainedTailMixedTimingRootStack at hstack
  rw [List.map_ofFn, List.prod_ofFn] at hstack
  rw [quittingHazardSurvival_eq_prod, ← Fin.prod_univ_eq_prod_range]
  simpa only [Function.comp_apply, quittingBehaviorLiveHazard,
    quittingProfileLiveRoot] using hstack

/-- The actual behavioral mass of a final-stage coalition factors into the
selected boundary atoms of its members and the `Never` atoms of its
nonmembers. -/
theorem quittingStageCoalitionMass_finiteDeadlineTimingProfile_boundary_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (boundary : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (boundary + 1)))
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingFiniteDeadlineTimingProfile reward (boundary + 1) mixed)
        boundary terminal =
      (∏ who ∈ terminal.val,
        (mixed who (some (Fin.last boundary))).toReal) *
      ∏ who ∈ terminal.valᶜ, (mixed who none).toReal := by
  rw [quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro who _
    have hbehavior := quittingBehaviorStoppingLaw_compactStoppingLawProfile
      reward (fun player => quittingFiniteDeadlineTimingLaw (mixed player)) who
    change (quittingBehaviorStoppingLaw reward
      (quittingFiniteDeadlineTimingProfile reward (boundary + 1) mixed who)
        (some boundary)).toReal = _
    rw [show quittingFiniteDeadlineTimingProfile reward (boundary + 1) mixed =
        quittingCompactStoppingLawProfile reward
          (fun player => quittingFiniteDeadlineTimingLaw (mixed player)) by rfl]
    rw [hbehavior]
    have hatom := quittingFiniteDeadlineTimingLaw_apply_some
      (mixed who) (Fin.last boundary)
    exact congrArg ENNReal.toReal hatom
  · apply Finset.prod_congr rfl
    intro who _
    exact quittingFiniteDeadlineTimingProfile_hazardSurvival_eq_none
      reward (boundary + 1) mixed who

end GameTheory
