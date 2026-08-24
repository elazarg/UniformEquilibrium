/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.FiniteSerialRelation.MarkedTwoCycle
import UniformEquilibrium.Diagnostics.Quitting.Collision.PreemptionGeometry
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportHardPrincipalDispatch
import UniformEquilibrium.Quitting.Classification.PreemptionGateDictionary

/-!
# Two-cycle lasso alignment with the hard principal

Reciprocal strict preemption edges make the literal two-cycle pair a
nonprojective principal.  Hence, in the final four-player hard residual, that
same pair enters the checked card-two crossing dispatch.

The actual terminal witness produces a marked lasso, but does not force its
cycle to have length two.  The final source theorem therefore returns either
an aligned two-cycle hard pair or one of the nine longer-cycle constructors.
It does not produce a chronology or an equilibrium.
-/

noncomputable section

namespace GameTheory

open Finset Math.LinearProgramming QuittingLCPClassification
open Math.FiniteSerialRelation

namespace QuittingLCPClassification

variable {iota : Type} [DecidableEq iota]

/-- A zero-diagonal two-by-two matrix with both off-diagonal entries strictly
negative is not projective Q. -/
theorem not_isProjectiveQMatrix_pair_of_reciprocal_neg
    (matrix : iota → iota → ℝ) {first second : iota}
    (hne : first ≠ second)
    (hfirstDiag : matrix first first = 0)
    (hsecondDiag : matrix second second = 0)
    (hfirstSecond : matrix first second < 0)
    (hsecondFirst : matrix second first < 0) :
    ¬IsProjectiveQMatrix (principalMatrix matrix {first, second}) := by
  intro hprojective
  let first' : ({first, second} : Finset iota) := ⟨first, by simp⟩
  let second' : ({first, second} : Finset iota) := ⟨second, by simp⟩
  obtain ⟨solution⟩ := hprojective (fun _ => -1)
  have hfirst := solution.residual_nonneg first'
  have hsecond := solution.residual_nonneg second'
  change 0 ≤ solution.cemetery * (-1) +
    ∑ owner : ({first, second} : Finset iota),
      solution.singleton owner * matrix first owner.1 at hfirst
  change 0 ≤ solution.cemetery * (-1) +
    ∑ owner : ({first, second} : Finset iota),
      solution.singleton owner * matrix second owner.1 at hsecond
  have hfirstNeSecond : first' ≠ second' := by
    intro heq
    exact hne (congrArg Subtype.val heq)
  have huniv : (Finset.univ : Finset ({first, second} : Finset iota)) =
      {first', second'} := by
    ext owner
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    have hmem : owner.1 = first ∨ owner.1 = second := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using owner.2
    rcases hmem with hfirstOwner | hsecondOwner
    · exact Or.inl (Subtype.ext hfirstOwner)
    · exact Or.inr (Subtype.ext hsecondOwner)
  have sum_pair (f : ({first, second} : Finset iota) → ℝ) :
      (∑ owner, f owner) = f first' + f second' := by
    change Finset.sum
      (Finset.univ : Finset ({first, second} : Finset iota)) f = _
    rw [huniv]
    simp [hfirstNeSecond]
  rw [sum_pair] at hfirst hsecond
  dsimp only [first', second'] at hfirst hsecond
  simp only [hfirstDiag, mul_zero, zero_add] at hfirst
  simp only [hsecondDiag, mul_zero, add_zero] at hsecond
  have hcemetery : solution.cemetery = 0 := by
    have hproduct : solution.singleton second' * matrix first second ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (solution.singleton_nonneg second') hfirstSecond.le
    dsimp only [second'] at hproduct
    apply le_antisymm _ solution.cemetery_nonneg
    nlinarith
  have hfirstWeight : solution.singleton first' = 0 := by
    have hproduct : solution.singleton first' * matrix second first ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (solution.singleton_nonneg first') hsecondFirst.le
    have hzero : solution.singleton first' * matrix second first = 0 := by
      simp only [hcemetery, zero_mul, zero_add] at hsecond
      exact le_antisymm hproduct (by simpa [first'] using hsecond)
    exact (mul_eq_zero.mp hzero).resolve_right hsecondFirst.ne
  have hsecondWeight : solution.singleton second' = 0 := by
    have hproduct : solution.singleton second' * matrix first second ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (solution.singleton_nonneg second') hfirstSecond.le
    have hzero : solution.singleton second' * matrix first second = 0 := by
      simp only [hcemetery, zero_mul, zero_add] at hfirst
      exact le_antisymm hproduct (by simpa [second'] using hfirst)
    exact (mul_eq_zero.mp hzero).resolve_right hfirstSecond.ne
  have htotal := solution.total
  rw [sum_pair] at htotal
  dsimp only [first', second'] at hfirstWeight hsecondWeight
  rw [hcemetery, hfirstWeight, hsecondWeight] at htotal
  norm_num at htotal

end QuittingLCPClassification

/-- The exact finite output attached to a marked two-cycle from the final
four-player hard residual. -/
def FinFourQuantitativeFullSupportHardResidual.HasAlignedTwoCycleHardPair
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    {certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap}
    (geometry : MarkedRootedLasso
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner certificate.collider) : Prop :=
  ∃ players : Finset (Fin 4),
    geometry.twoCyclePair? = some players ∧
      ¬IsProjectiveQMatrix
        (principalMatrix (normalizedSoloMatrix reward) players) ∧
      Nonempty (FinFourHardCardTwoCrossing residual players)

namespace FinFourQuantitativeFullSupportHardResidual

private theorem alignedPair_of_reciprocalPreemption
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    {first second : Fin 4}
    (forward : QuittingSoloPreempts reward residual.witness.terminalGap
      first second)
    (backward : QuittingSoloPreempts reward residual.witness.terminalGap
      second first) :
    ¬IsProjectiveQMatrix
        (principalMatrix (normalizedSoloMatrix reward) {first, second}) ∧
      Nonempty (FinFourHardCardTwoCrossing residual {first, second}) := by
  have hsecondFirst :=
    (quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg reward
      residual.witness.terminalGap first second).mp forward |>.2
  have hfirstSecond :=
    (quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg reward
      residual.witness.terminalGap second first).mp backward |>.2
  have hsecondFirstNeg : normalizedSoloMatrix reward second first < 0 := by
    linarith [residual.witness.terminalGap_pos]
  have hfirstSecondNeg : normalizedSoloMatrix reward first second < 0 := by
    linarith [residual.witness.terminalGap_pos]
  have hne : first ≠ second := forward.1.symm
  have hnot := not_isProjectiveQMatrix_pair_of_reciprocal_neg
    (normalizedSoloMatrix reward) hne
      (normalizedSoloMatrix_diagonal reward first)
      (normalizedSoloMatrix_diagonal reward second)
      hfirstSecondNeg hsecondFirstNeg
  exact ⟨hnot, residual.cardTwoCrossing (Finset.card_pair hne) hnot⟩

/-- Every one of the eight marked two-cycle constructors aligns its literal
cycle pair with the checked hard card-two crossing.  The other nine
constructors are exactly the long-cycle predicate. -/
theorem alignedTwoCycleHardPair_or_hasLongCycle
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    {certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap}
    (geometry : MarkedRootedLasso
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner certificate.collider) :
    residual.HasAlignedTwoCycleHardPair geometry ∨ geometry.HasLongCycle := by
  cases geometry with
  | rootedTwo_next geometry _ =>
      left
      obtain ⟨hnot, hcrossing⟩ :=
        residual.alignedPair_of_reciprocalPreemption
          geometry.forward geometry.backward
      exact ⟨{certificate.owner, geometry.next}, rfl, hnot, hcrossing⟩
  | rootedTwo_outside geometry _ =>
      left
      obtain ⟨hnot, hcrossing⟩ :=
        residual.alignedPair_of_reciprocalPreemption
          geometry.forward geometry.backward
      exact ⟨{certificate.owner, geometry.next}, rfl, hnot, hcrossing⟩
  | rootedThree_first _ _ => exact Or.inr trivial
  | rootedThree_second _ _ => exact Or.inr trivial
  | rootedThree_outside _ _ => exact Or.inr trivial
  | rootedFour_first _ _ => exact Or.inr trivial
  | rootedFour_second _ _ => exact Or.inr trivial
  | rootedFour_third _ _ => exact Or.inr trivial
  | oneToTwo_entry geometry _ =>
      left
      obtain ⟨hnot, hcrossing⟩ :=
        residual.alignedPair_of_reciprocalPreemption
          geometry.cycle_forward geometry.cycle_backward
      exact ⟨{geometry.entry, geometry.other}, rfl, hnot, hcrossing⟩
  | oneToTwo_other geometry _ =>
      left
      obtain ⟨hnot, hcrossing⟩ :=
        residual.alignedPair_of_reciprocalPreemption
          geometry.cycle_forward geometry.cycle_backward
      exact ⟨{geometry.entry, geometry.other}, rfl, hnot, hcrossing⟩
  | oneToTwo_outside geometry _ =>
      left
      obtain ⟨hnot, hcrossing⟩ :=
        residual.alignedPair_of_reciprocalPreemption
          geometry.cycle_forward geometry.cycle_backward
      exact ⟨{geometry.entry, geometry.other}, rfl, hnot, hcrossing⟩
  | oneToThree_entry _ _ => exact Or.inr trivial
  | oneToThree_second _ _ => exact Or.inr trivial
  | oneToThree_third _ _ => exact Or.inr trivial
  | twoToTwo_first geometry _ =>
      left
      obtain ⟨hnot, hcrossing⟩ :=
        residual.alignedPair_of_reciprocalPreemption
          geometry.cycle_forward geometry.cycle_backward
      exact ⟨{geometry.entry, geometry.other}, rfl, hnot, hcrossing⟩
  | twoToTwo_entry geometry _ =>
      left
      obtain ⟨hnot, hcrossing⟩ :=
        residual.alignedPair_of_reciprocalPreemption
          geometry.cycle_forward geometry.cycle_backward
      exact ⟨{geometry.entry, geometry.other}, rfl, hnot, hcrossing⟩
  | twoToTwo_other geometry _ =>
      left
      obtain ⟨hnot, hcrossing⟩ :=
        residual.alignedPair_of_reciprocalPreemption
          geometry.cycle_forward geometry.cycle_backward
      exact ⟨{geometry.entry, geometry.other}, rfl, hnot, hcrossing⟩

/-- In the `rootedTwo_next` constructor, the aligned pair is literally the
collision owner/collider pair. -/
theorem rootedTwoNext_ownerCollider_alignment
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap)
    (geometry : RootedTwoCycle
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner)
    (marker_eq : certificate.collider = geometry.next) :
    let marked := MarkedRootedLasso.rootedTwo_next geometry marker_eq
    marked.twoCyclePair? = some {certificate.owner, certificate.collider} ∧
      ¬IsProjectiveQMatrix (principalMatrix (normalizedSoloMatrix reward)
        {certificate.owner, certificate.collider}) ∧
      Nonempty (FinFourHardCardTwoCrossing residual
        {certificate.owner, certificate.collider}) := by
  dsimp only
  constructor
  · exact MarkedRootedLasso.rootedTwoNext_twoCyclePair?_eq_root_marker
      geometry marker_eq
  · rw [marker_eq]
    exact residual.alignedPair_of_reciprocalPreemption
      geometry.forward geometry.backward

/-- The actual final residual produces a marked collision geometry for which
the two-cycle hard-pair alignment is derived, or whose constructor is one of
the nine long-cycle cases.  No two-cycle hypothesis is added to the source. -/
theorem exists_collisionGeometry_with_alignedTwoCycleHardPair_or_long
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    ∃ certificate : QuittingImmediateSingletonCollision reward
        residual.witness.terminalGap,
      ∃ geometry : MarkedRootedLasso
          (QuittingSoloPreempts reward residual.witness.terminalGap)
          certificate.owner certificate.collider,
        residual.HasAlignedTwoCycleHardPair geometry ∨
          geometry.HasLongCycle := by
  obtain ⟨certificate, ⟨geometry⟩⟩ :=
    residual.witness.exists_collisionAnchoredPreemptionGeometry_of_card_eq_four
      (by norm_num)
  exact ⟨certificate, geometry,
    residual.alignedTwoCycleHardPair_or_hasLongCycle geometry⟩

end FinFourQuantitativeFullSupportHardResidual

end GameTheory
