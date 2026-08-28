/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.SourceFaithfulMinimumLawCausalization

/-!
# Retaining an arbitrary smaller resolution through source-faithful causalization

A source-faithful minimum causalization records a marked-stage mass floor
`lambda` before its newly selected exact cap--Nash word.  Its joint Continue
product tends to one.  Consequently every strictly smaller requested scale is
eventually retained after the complete word.  The existing `lambda / 2`
field is therefore only a convenient canonical specialization, not a loss
forced by the construction.

This is the quantitative renewal fact needed when a minimum-law endpoint is
causalized repeatedly: one may choose successive resolutions decreasing
arbitrarily slowly, and hence keep them all above any fixed lower floor below
the first resolution.  No recursive source or strategic consumer is asserted
in this module.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingSourceFaithfulMinimumCausalization

/-- Every requested resolution strictly below the incoming marked-mass floor
is eventually retained by the same literal marked atom after the exact
cap--Nash prefix word. -/
theorem eventually_requestedResolution_le_shiftedMarkMass
    {point : QuittingTerminalSemanticLawPoint ι}
    {terminal : {S : Finset ι // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda requested : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda)
    (hrequested : requested < lambda) :
    ∀ᶠ rank in atTop,
      requested ≤ quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward
          (causal.roots rank) (profiles rank))
        (rank + 1 + mark rank) terminal := by
  have hscaled : Tendsto (fun rank ↦
      quittingCapNashStackContinueProduct (causal.roots rank) * lambda)
      atTop (nhds lambda) := by
    simpa using causal.continueProduct_tendsto_one.mul_const lambda
  have heventually : ∀ᶠ rank in atTop,
      requested <
        quittingCapNashStackContinueProduct (causal.roots rank) * lambda :=
    hscaled.eventually (Ioi_mem_nhds hrequested)
  filter_upwards [heventually] with rank hstrict
  rw [causal.shifted_mark_mass_eq rank]
  exact hstrict.le.trans
    (mul_le_mul_of_nonneg_left (causal.marked_mass_floor rank)
      (quittingCapNashStackContinueProduct_nonneg (causal.roots rank)))

/-- Positive smaller resolutions are eventually available with both their
positivity proof and their literal shifted-stage mass bound. -/
theorem eventually_positiveRequestedResolution
    {point : QuittingTerminalSemanticLawPoint ι}
    {terminal : {S : Finset ι // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda requested : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda)
    (hrequestedPos : 0 < requested)
    (hrequestedLt : requested < lambda) :
    ∀ᶠ rank in atTop,
      0 < requested ∧
        requested ≤ quittingStageCoalitionMass reward
          (quittingLiteralRootStackProfile reward
            (causal.roots rank) (profiles rank))
          (rank + 1 + mark rank) terminal := by
  filter_upwards [
    causal.eventually_requestedResolution_le_shiftedMarkMass hrequestedLt]
      with rank hmass
  exact ⟨hrequestedPos, hmass⟩

end QuittingSourceFaithfulMinimumCausalization

end GameTheory
