/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.Atom.ExactPrefixChronology
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashChronology

/-!
# Charge of exact-prefix atom stacks

When two players have positive debt at the stopping-law minimum, joint
survival through the increasingly long exact-prefix atom stacks tends to one.
The unweighted sum of their literal one-row absorption hazards consequently
tends to zero.  Thus these access stacks cannot themselves supply unbounded
exact prefix charge.

This does not rule out appending a separate positive exact edge followed by
an admissible return.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem continueMass_pos_of_mem_of_continueProduct_pos
    (roots : List (ι → PMF Bool))
    (hproduct : 0 < quittingCapNashStackContinueProduct roots) :
    ∀ root ∈ roots, 0 < quittingStationaryContinueMass root := by
  induction roots with
  | nil => simp
  | cons head tail ih =>
      rw [quittingCapNashStackContinueProduct_cons] at hproduct
      have hheadNonneg := quittingStationaryContinueMass_nonneg head
      have htailNonneg := quittingCapNashStackContinueProduct_nonneg tail
      have hheadPos : 0 < quittingStationaryContinueMass head := by
        by_contra hnot
        have hzero : quittingStationaryContinueMass head = 0 :=
          le_antisymm (le_of_not_gt hnot) hheadNonneg
        rw [hzero, zero_mul] at hproduct
        exact (lt_irrefl 0) hproduct
      have htailPos : 0 < quittingCapNashStackContinueProduct tail := by
        by_contra hnot
        have hzero : quittingCapNashStackContinueProduct tail = 0 :=
          le_antisymm (le_of_not_gt hnot) htailNonneg
        rw [hzero, mul_zero] at hproduct
        exact (lt_irrefl 0) hproduct
      intro root hroot
      simp only [List.mem_cons] at hroot
      rcases hroot with rfl | hroot
      · exact hheadPos
      · exact ih htailPos root hroot

namespace QuittingStoppingLawAtomExactPrefixChronology

/-- With two distinct active debtors, the total literal absorption charge of
the exact access stack tends to zero. -/
theorem absorptionSum_tendsto_zero_of_twoActive
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    (chronology : QuittingStoppingLawAtomExactPrefixChronology frontier)
    {first second : ι} (hfirst : first ∈ frontier.active)
    (hsecond : second ∈ frontier.active) (hne : first ≠ second) :
    Tendsto (fun rank ↦
      quittingCapNashStackAbsorptionSum (chronology.roots rank))
      atTop (nhds 0) := by
  have hsurvival := chronology.jointSurvival_tendsto_one_of_twoActive
    hfirst hsecond hne
  have hproduct : Tendsto (fun rank ↦
      quittingCapNashStackContinueProduct (chronology.roots rank))
      atTop (nhds 1) := by
    simpa only [quittingCapNashStackContinueProduct,
      quittingLiteralRootStackJointSurvival] using hsurvival
  have hlog : Tendsto (fun rank ↦
      -Real.log (quittingCapNashStackContinueProduct
        (chronology.roots rank))) atTop (nhds 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      hproduct
    simpa using this.neg
  apply squeeze_zero'
  · exact Eventually.of_forall fun rank ↦
      quittingCapNashStackAbsorptionSum_nonneg (chronology.roots rank)
  · filter_upwards [hproduct.eventually (Ioi_mem_nhds zero_lt_one)] with
      rank hpositive
    exact capNashStack_absorptionSum_le_neg_log_continueProduct
      (chronology.roots rank)
      (continueMass_pos_of_mem_of_continueProduct_pos
        (chronology.roots rank) hpositive)
  · exact hlog

end QuittingStoppingLawAtomExactPrefixChronology

end GameTheory
