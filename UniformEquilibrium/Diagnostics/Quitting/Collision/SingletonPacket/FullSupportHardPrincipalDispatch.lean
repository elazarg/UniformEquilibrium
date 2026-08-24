/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportHardPrincipalSize
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.SupportThreeFourSignGraph

/-!
# Finite dispatch inside the full-support nonprojective principal

A two-coordinate nonprojective principal has two strictly negative reciprocal
singleton effects.  Full packet support supplies an outside positive helper
for each harmed row.  For a three-coordinate principal, either such a helper
escapes through the unique outsider, or the internal crossings form a strict
three-cycle; nonprojectivity then forces its cyclic determinant to be
nonpositive.
-/

noncomputable section

namespace GameTheory

open Finset Math.LinearProgramming QuittingLCPClassification
open QuittingLCPClassification.ThreeByThreeZeroDiagonalQ
open QuittingLCPClassification.FinFourQuantitativeFullSupportHardResidual

/-- Exact crossed singleton data forced by a two-coordinate nonprojective
principal of the final full-support residual.  The two positive helpers lie
outside the failed principal, but they need not be distinct. -/
structure FinFourHardCardTwoCrossing
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (players : Finset (Fin 4)) where
  first : Fin 4
  second : Fin 4
  firstHelper : Fin 4
  secondHelper : Fin 4
  first_ne_second : first ≠ second
  players_eq : players = {first, second}
  firstHelper_outside : firstHelper ∉ players
  secondHelper_outside : secondHelper ∉ players
  first_harmed : normalizedSoloMatrix reward first second < 0
  second_harmed : normalizedSoloMatrix reward second first < 0
  first_helped : 0 < normalizedSoloMatrix reward first firstHelper
  second_helped : 0 < normalizedSoloMatrix reward second secondHelper

/-- The exact source-alignment obstruction in a card-three hard principal:
one internal negative column can be compensated only through the unique
outside packet atom. -/
structure FinFourHardCardThreeExternalHelper
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (players : Finset (Fin 4)) where
  outsider : Fin 4
  owner : Fin 4
  harmed : Fin 4
  complement_eq : playersᶜ = {outsider}
  owner_mem : owner ∈ players
  harmed_mem : harmed ∈ players
  harmed_by_owner : normalizedSoloMatrix reward harmed owner < 0
  helped_by_outsider : 0 < normalizedSoloMatrix reward harmed outsider

/-- If every negative column of a card-three hard principal is compensated
internally, the principal has a cyclic sign orientation.  Its determinant is
nonpositive, exactly opposite to the checked three-player standard-Q
compiler chamber. -/
structure FinFourHardCardThreeCyclicBoundary
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (players : Finset (Fin 4)) where
  label : players ≃ Fin 3
  orientation :
    let matrix := reindexMatrix label
      (principalMatrix (normalizedSoloMatrix reward) players)
    ForwardOrientation matrix ∨ ReverseOrientation matrix
  determinant_nonpos :
    let matrix := reindexMatrix label
      (principalMatrix (normalizedSoloMatrix reward) players)
    cycleDeterminant matrix ≤ 0

/-- Exhaustive finite shape of the principal obstruction after projective
Q-bar has been removed from the final four-player residual. -/
def HasFinFourHardPrincipalDispatch
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) : Prop :=
  (∃ players, Nonempty (FinFourHardCardTwoCrossing residual players)) ∨
    ∃ players,
      Nonempty (FinFourHardCardThreeExternalHelper reward players) ∨
        Nonempty (FinFourHardCardThreeCyclicBoundary reward players)

namespace FinFourQuantitativeFullSupportHardResidual

private theorem negative_offDiagonal_of_pair_nonprojective
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {first second : Fin 4}
    (hnot : ¬IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) {first, second})) :
    normalizedSoloMatrix reward first second < 0 ∧
      normalizedSoloMatrix reward second first < 0 := by
  let players : Finset (Fin 4) := {first, second}
  let matrix := principalMatrix (normalizedSoloMatrix reward) players
  have hhomogeneous : ¬HasHomogeneousSimplexSolution matrix := by
    intro hhomogeneous
    exact hnot ((isProjectiveQMatrix_iff_standard_or_homogeneous _).2
      (Or.inr hhomogeneous))
  have hdiag : ∀ player, matrix player player = 0 := by
    intro player
    exact normalizedSoloMatrix_diagonal reward player.1
  have negativeColumn (owner : players) :
      ∃ harmed, matrix harmed owner < 0 :=
    exists_negative_entry_in_column_of_noHomogeneous matrix hdiag
      hhomogeneous owner
  constructor
  · obtain ⟨harmed, hharmed⟩ := negativeColumn ⟨second, by simp [players]⟩
    have hlabel : harmed.1 = first ∨ harmed.1 = second := by
      have hmem : harmed.1 ∈ ({first, second} : Finset (Fin 4)) :=
        harmed.2
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    rcases hlabel with hfirst | hsecond
    · simpa [matrix, principalMatrix, hfirst] using hharmed
    · rw [show harmed = ⟨second, by simp [players]⟩ from
        Subtype.ext hsecond] at hharmed
      simp [matrix, principalMatrix, normalizedSoloMatrix_diagonal] at hharmed
  · obtain ⟨harmed, hharmed⟩ := negativeColumn ⟨first, by simp [players]⟩
    have hlabel : harmed.1 = first ∨ harmed.1 = second := by
      have hmem : harmed.1 ∈ ({first, second} : Finset (Fin 4)) :=
        harmed.2
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    rcases hlabel with hfirst | hsecond
    · rw [show harmed = ⟨first, by simp [players]⟩ from
        Subtype.ext hfirst] at hharmed
      simp [matrix, principalMatrix, normalizedSoloMatrix_diagonal] at hharmed
    · simpa [matrix, principalMatrix, hsecond] using hharmed

/-- A card-two hard principal is an actual mutually harmful pair with one
outside positive singleton helper for each receiver row. -/
theorem cardTwoCrossing
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    {players : Finset (Fin 4)} (hcard : players.card = 2)
    (hnot : ¬IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) players)) :
    Nonempty (FinFourHardCardTwoCrossing residual players) := by
  obtain ⟨first, second, hne, hplayers⟩ := Finset.card_eq_two.mp hcard
  have hnotPair : ¬IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) {first, second}) := by
    rwa [hplayers] at hnot
  obtain ⟨hfirstHarmed, hsecondHarmed⟩ :=
    negative_offDiagonal_of_pair_nonprojective hnotPair
  have hfirstMem : first ∈ residual.packet.support := by
    rw [residual.packet_support_eq_univ]
    exact Finset.mem_univ first
  have hsecondMem : second ∈ residual.packet.support := by
    rw [residual.packet_support_eq_univ]
    exact Finset.mem_univ second
  have hfirstRawSolo : quittingSoloReward reward second first <
      quittingSoloReward reward first first := by
    rw [normalizedSoloMatrix_eq_soloReward_sub] at hfirstHarmed
    linarith
  have hfirstRaw : reward (quittingSingletonTerminal second) first <
      reward (quittingSingletonTerminal first) first := by
    simpa only [quittingSoloReward, quittingSingletonTerminal] using
      hfirstRawSolo
  have hsecondRawSolo : quittingSoloReward reward first second <
      quittingSoloReward reward second second := by
    rw [normalizedSoloMatrix_eq_soloReward_sub] at hsecondHarmed
    linarith
  have hsecondRaw : reward (quittingSingletonTerminal first) second <
      reward (quittingSingletonTerminal second) second := by
    simpa only [quittingSoloReward, quittingSingletonTerminal] using
      hsecondRawSolo
  obtain ⟨firstHelper, _hfirstHelperMem, hfirstHelperNe, hfirstHelp⟩ :=
    residual.packet.exists_supported_helper_of_singleton_lt_solo
      hsecondMem hfirstRaw
  obtain ⟨secondHelper, _hsecondHelperMem, hsecondHelperNe, hsecondHelp⟩ :=
    residual.packet.exists_supported_helper_of_singleton_lt_solo
      hfirstMem hsecondRaw
  have hfirstHelperNeFirst : firstHelper ≠ first := by
    intro heq
    subst firstHelper
    exact (lt_irrefl _ hfirstHelp)
  have hsecondHelperNeSecond : secondHelper ≠ second := by
    intro heq
    subst secondHelper
    exact (lt_irrefl _ hsecondHelp)
  refine ⟨{
    first := first
    second := second
    firstHelper := firstHelper
    secondHelper := secondHelper
    first_ne_second := hne
    players_eq := hplayers
    firstHelper_outside := ?_
    secondHelper_outside := ?_
    first_harmed := hfirstHarmed
    second_harmed := hsecondHarmed
    first_helped := ?_
    second_helped := ?_ }⟩
  · rw [hplayers]
    simp [hfirstHelperNeFirst, hfirstHelperNe]
  · rw [hplayers]
    simp [hsecondHelperNe, hsecondHelperNeSecond]
  · rw [normalizedSoloMatrix_eq_soloReward_sub]
    have : quittingSoloReward reward first first <
        quittingSoloReward reward firstHelper first := by
      simpa only [quittingSoloReward, quittingSingletonTerminal] using
        hfirstHelp
    linarith
  · rw [normalizedSoloMatrix_eq_soloReward_sub]
    have : quittingSoloReward reward second second <
        quittingSoloReward reward secondHelper second := by
      simpa only [quittingSoloReward, quittingSingletonTerminal] using
        hsecondHelp
    linarith

/-- A card-three hard principal either exposes the precise missing outside
source alignment, or lands in the cyclic chamber with nonpositive determinant
and therefore outside the existing three-player compiler. -/
theorem cardThree_externalHelper_or_cyclicBoundary
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    {players : Finset (Fin 4)} (hcard : players.card = 3)
    (hnot : ¬IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) players)) :
    Nonempty (FinFourHardCardThreeExternalHelper reward players) ∨
      Nonempty (FinFourHardCardThreeCyclicBoundary reward players) := by
  let matrix := principalMatrix (normalizedSoloMatrix reward) players
  have hhomogeneous : ¬HasHomogeneousSimplexSolution matrix := by
    intro hhomogeneous
    exact hnot ((isProjectiveQMatrix_iff_standard_or_homogeneous _).2
      (Or.inr hhomogeneous))
  have hdiag : ∀ player, matrix player player = 0 := by
    intro player
    exact normalizedSoloMatrix_diagonal reward player.1
  have negativeColumn (owner : players) :
      ∃ harmed, matrix harmed owner < 0 :=
    exists_negative_entry_in_column_of_noHomogeneous matrix hdiag
      hhomogeneous owner
  have hcomplementCard : playersᶜ.card = 1 := by
    rw [Finset.card_compl, hcard]
    norm_num
  obtain ⟨outsider, hcomplement⟩ :=
    Finset.card_eq_one.mp hcomplementCard
  by_cases hexternal : ∃ owner harmed : players,
      matrix harmed owner < 0 ∧
        0 < normalizedSoloMatrix reward harmed.1 outsider
  · left
    obtain ⟨owner, harmed, hnegative, hpositive⟩ := hexternal
    exact ⟨{
      outsider := outsider
      owner := owner.1
      harmed := harmed.1
      complement_eq := hcomplement
      owner_mem := owner.2
      harmed_mem := harmed.2
      harmed_by_owner := hnegative
      helped_by_outsider := hpositive }⟩
  · right
    have hcrossed : HasInternalCrossedRows matrix := by
      intro owner
      obtain ⟨harmed, hnegative⟩ := negativeColumn owner
      have hrawSolo : quittingSoloReward reward owner.1 harmed.1 <
          quittingSoloReward reward harmed.1 harmed.1 := by
        change normalizedSoloMatrix reward harmed.1 owner.1 < 0 at hnegative
        rw [normalizedSoloMatrix_eq_soloReward_sub] at hnegative
        linarith
      have hraw : reward (quittingSingletonTerminal owner.1) harmed.1 <
          reward (quittingSingletonTerminal harmed.1) harmed.1 := by
        simpa only [quittingSoloReward, quittingSingletonTerminal] using
          hrawSolo
      have hownerSupport : owner.1 ∈ residual.packet.support := by
        rw [residual.packet_support_eq_univ]
        exact Finset.mem_univ owner.1
      obtain ⟨helper, _hhelperSupport, hhelperOwner, hhelp⟩ :=
        residual.packet.exists_supported_helper_of_singleton_lt_solo
          hownerSupport hraw
      have hhelperHarmed : helper ≠ harmed.1 := by
        intro heq
        subst helper
        exact (lt_irrefl _ hhelp)
      have hhelpMatrix : 0 < normalizedSoloMatrix reward harmed.1 helper := by
        rw [normalizedSoloMatrix_eq_soloReward_sub]
        have : quittingSoloReward reward harmed.1 harmed.1 <
            quittingSoloReward reward helper harmed.1 := by
          simpa only [quittingSoloReward, quittingSingletonTerminal] using
            hhelp
        linarith
      have hhelperMem : helper ∈ players := by
        by_contra hhelperOutside
        have hhelperComplement : helper ∈ playersᶜ := by
          exact Finset.mem_compl.mpr hhelperOutside
        have hhelperEq : helper = outsider := by
          rw [hcomplement] at hhelperComplement
          simpa using hhelperComplement
        apply hexternal
        refine ⟨owner, harmed, hnegative, ?_⟩
        rwa [hhelperEq] at hhelpMatrix
      let helperIn : players := ⟨helper, hhelperMem⟩
      refine ⟨harmed, helperIn, ?_, ?_, ?_, hnegative, ?_⟩
      · intro heq
        subst harmed
        rw [hdiag owner] at hnegative
        linarith
      · exact fun heq ↦ hhelperOwner (congrArg Subtype.val heq)
      · exact fun heq ↦ hhelperHarmed (congrArg Subtype.val heq)
      · exact hhelpMatrix
    have hcardSubtype : Fintype.card players = 3 := by
      simpa using hcard
    obtain ⟨label, horientation⟩ :=
      ThreePointCrossedRows.exists_cyclicLabeling_of_card_eq_three
        matrix hcardSubtype hcrossed
    let labelled := reindexMatrix label matrix
    have hdiagLabelled : ∀ player, labelled player player = 0 := by
      intro player
      simp [labelled, reindexMatrix, hdiag]
    have hnotStandard : ¬IsStandardQMatrix labelled := by
      intro hstandard
      have hback := isStandardQMatrix_reindexMatrix label.symm
        labelled hstandard
      have hmatrix : reindexMatrix label.symm labelled = matrix := by
        funext receiver owner
        simp [labelled, reindexMatrix]
      rw [hmatrix] at hback
      exact hnot ((isProjectiveQMatrix_iff_standard_or_homogeneous _).2
        (Or.inl hback))
    have hdeterminant : cycleDeterminant labelled ≤ 0 := by
      by_contra hnotNonpos
      have hpositive : 0 < cycleDeterminant labelled :=
        lt_of_not_ge hnotNonpos
      apply hnotStandard
      rcases horientation with hforward | hreverse
      · exact
          (standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_forward
            labelled hdiagLabelled hforward).mpr hpositive |>.1
      · exact
          (standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_reverse
            labelled hdiagLabelled hreverse).mpr hpositive |>.1
    exact ⟨{
      label := label
      orientation := horientation
      determinant_nonpos := hdeterminant }⟩

/-- **Final finite principal dispatch.**  Every quantitative full-support hard
residual has either a mutually harmful two-player principal with outside
positive helpers, or a three-player principal whose exact remaining issue is
an outside helper or a cyclic nonpositive determinant. -/
theorem hardPrincipalDispatch
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    HasFinFourHardPrincipalDispatch residual := by
  obtain ⟨players, hcard, hnot⟩ :=
    exists_nonprojectivePrincipal_card_two_or_three residual
  rcases hcard with htwo | hthree
  · left
    exact ⟨players, residual.cardTwoCrossing htwo hnot⟩
  · right
    exact ⟨players,
      residual.cardThree_externalHelper_or_cyclicBoundary hthree hnot⟩

end FinFourQuantitativeFullSupportHardResidual

end GameTheory
