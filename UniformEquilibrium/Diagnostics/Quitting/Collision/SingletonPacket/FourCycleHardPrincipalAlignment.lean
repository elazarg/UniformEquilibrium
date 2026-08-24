/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.ThreeCycleLassoHardPrincipalIncidence

/-!
# Rooted four-cycle alignment with a proper hard principal

On a literal rooted four-cycle, a selected card-two hard principal already
has reciprocal negative singleton entries and therefore yields a strict
two-cycle at a possibly smaller positive margin.  A selected card-three hard
principal either has its literal omitted vertex as an external helper or its
cyclic orientation yields a strict three-cycle, again at a new margin.

This is finite same-table incidence.  It does not retain the terminal gap on
new edges and does not construct a stopping law or an equilibrium.
-/

noncomputable section

namespace GameTheory

open Finset Math.LinearProgramming QuittingLCPClassification
open QuittingLCPClassification.ThreeByThreeZeroDiagonalQ
open QuittingLCPClassification.FinFourQuantitativeFullSupportHardResidual
open Math.FiniteSerialRelation
open QuittingSureSetOwnerRepair

/-- A shorter strict two-cycle on exactly a selected hard pair. -/
structure FinFourHardPairShortTwoCycle
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (players : Finset (Fin 4)) where
  margin : ℝ
  margin_pos : 0 < margin
  geometryRoot : Fin 4
  geometry : RootedTwoCycle (QuittingSoloPreempts reward margin) geometryRoot
  players_eq : players = {geometryRoot, geometry.next}

/-- A shorter strict three-cycle on exactly a selected hard triple. -/
structure FinFourHardTripleShortThreeCycle
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (players : Finset (Fin 4)) where
  margin : ℝ
  margin_pos : 0 < margin
  first : Fin 4
  second : Fin 4
  third : Fin 4
  second_ne_first : second ≠ first
  third_ne_first : third ≠ first
  third_ne_second : third ≠ second
  players_eq : players = {first, second, third}
  first_edge : QuittingSoloPreempts reward margin first second
  second_edge : QuittingSoloPreempts reward margin second third
  closing_edge : QuittingSoloPreempts reward margin third first

namespace FinFourQuantitativeFullSupportHardResidual

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}

private theorem preempts_of_normalized_neg
    {owner receiver : Fin 4}
    (hne : owner ≠ receiver)
    (hneg : normalizedSoloMatrix reward receiver owner < 0) :
    ∃ margin, 0 < margin ∧ QuittingSoloPreempts reward margin owner receiver := by
  let margin := -normalizedSoloMatrix reward receiver owner / 2
  have hmargin : 0 < margin := by dsimp [margin]; linarith
  refine ⟨margin, hmargin, ?_⟩
  apply (quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg reward
    margin owner receiver).2
  refine ⟨hne.symm, ?_⟩
  dsimp [margin]
  linarith

private theorem preempts_mono {small large : ℝ} {owner receiver : Fin 4}
    (hle : small ≤ large)
    (hpreempts : QuittingSoloPreempts reward large owner receiver) :
    QuittingSoloPreempts reward small owner receiver := by
  exact ⟨hpreempts.1, by linarith [hpreempts.2]⟩

/-- Reciprocal negativity on a card-two hard principal is itself a strict
two-cycle at a new positive margin.  No adjacency assumption is needed. -/
theorem cardTwoCrossing_shortTwoCycle
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    {players : Finset (Fin 4)}
    (crossing : FinFourHardCardTwoCrossing residual players) :
    Nonempty (FinFourHardPairShortTwoCycle (reward := reward) players) := by
  obtain ⟨firstMargin, hfirstMargin, hfirstEdge⟩ :=
    preempts_of_normalized_neg (reward := reward) crossing.first_ne_second
      crossing.second_harmed
  obtain ⟨secondMargin, hsecondMargin, hsecondEdge⟩ :=
    preempts_of_normalized_neg (reward := reward) crossing.first_ne_second.symm
      crossing.first_harmed
  let margin := min firstMargin secondMargin
  have hmargin : 0 < margin := lt_min hfirstMargin hsecondMargin
  have hfirst : QuittingSoloPreempts reward margin crossing.first
      crossing.second := by
    exact preempts_mono (min_le_left _ _) hfirstEdge
  have hsecond : QuittingSoloPreempts reward margin crossing.second
      crossing.first := by
    exact preempts_mono (min_le_right _ _) hsecondEdge
  let geometry : RootedTwoCycle (QuittingSoloPreempts reward margin)
      crossing.first := {
    next := crossing.second
    next_ne_root := crossing.first_ne_second.symm
    forward := hfirst
    backward := hsecond }
  exact ⟨{
    margin := margin
    margin_pos := hmargin
    geometry := geometry
    geometryRoot := crossing.first
    players_eq := crossing.players_eq }⟩

private theorem cyclicBoundary_shortThreeCycle
    {players : Finset (Fin 4)}
    (boundary : FinFourHardCardThreeCyclicBoundary reward players) :
    Nonempty (FinFourHardTripleShortThreeCycle (reward := reward) players) := by
  let matrix := reindexMatrix boundary.label
    (principalMatrix (normalizedSoloMatrix reward) players)
  let p0 : Fin 4 := (boundary.label.symm 0).1
  let p1 : Fin 4 := (boundary.label.symm 1).1
  let p2 : Fin 4 := (boundary.label.symm 2).1
  have hp01 : p0 ≠ p1 := by
    intro heq
    have heq' : boundary.label.symm 0 = boundary.label.symm 1 :=
      Subtype.ext heq
    exact (by norm_num : (0 : Fin 3) ≠ 1) (boundary.label.symm.injective heq')
  have hp02 : p0 ≠ p2 := by
    intro heq
    have heq' : boundary.label.symm 0 = boundary.label.symm 2 :=
      Subtype.ext heq
    exact (by norm_num : (0 : Fin 3) ≠ 2) (boundary.label.symm.injective heq')
  have hp12 : p1 ≠ p2 := by
    intro heq
    have heq' : boundary.label.symm 1 = boundary.label.symm 2 :=
      Subtype.ext heq
    exact (by norm_num : (1 : Fin 3) ≠ 2) (boundary.label.symm.injective heq')
  have hplayers : players = {p0, p1, p2} := by
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le
    · intro who hwho
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
      rcases hwho with hwho | hwho | hwho <;> subst who <;>
        exact Subtype.property _
    · have hcard : players.card = 3 := by
        have := Fintype.card_congr boundary.label
        simpa using this
      rw [hcard]
      simp [hp01, hp02, hp12]
  rcases boundary.orientation with hforward | hreverse
  · obtain ⟨margin01, hmargin01, hedge01⟩ :=
      preempts_of_normalized_neg (reward := reward)
        hp01.symm
        (by simpa [matrix, reindexMatrix, principalMatrix] using hforward.1)
    obtain ⟨margin12, hmargin12, hedge12⟩ :=
      preempts_of_normalized_neg (reward := reward)
        hp12.symm
        (by simpa [matrix, reindexMatrix, principalMatrix] using
          hforward.2.2.2.1)
    obtain ⟨margin20, hmargin20, hedge20⟩ :=
      preempts_of_normalized_neg (reward := reward)
        hp02
        (by simpa [matrix, reindexMatrix, principalMatrix] using
          hforward.2.2.2.2.1)
    let margin := min margin01 (min margin12 margin20)
    have hmargin : 0 < margin :=
      lt_min hmargin01 (lt_min hmargin12 hmargin20)
    exact ⟨{
      margin := margin
      margin_pos := hmargin
      first := p1
      second := p0
      third := p2
      second_ne_first := hp01
      third_ne_first := hp12.symm
      third_ne_second := hp02.symm
      players_eq := by
        rw [hplayers]
        ext who
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      first_edge := preempts_mono (min_le_left _ _) hedge01
      second_edge := preempts_mono
        ((min_le_right _ _).trans (min_le_right _ _)) hedge20
      closing_edge := preempts_mono
        ((min_le_right _ _).trans (min_le_left _ _)) hedge12 }⟩
  · obtain ⟨margin10, hmargin10, hedge10⟩ :=
      preempts_of_normalized_neg (reward := reward)
        hp01
        (by simpa [matrix, reindexMatrix, principalMatrix] using
          hreverse.2.2.1)
    obtain ⟨margin21, hmargin21, hedge21⟩ :=
      preempts_of_normalized_neg (reward := reward)
        hp12
        (by simpa [matrix, reindexMatrix, principalMatrix] using
          hreverse.2.2.2.2.2)
    obtain ⟨margin02, hmargin02, hedge02⟩ :=
      preempts_of_normalized_neg (reward := reward)
        hp02.symm
        (by simpa [matrix, reindexMatrix, principalMatrix] using
          hreverse.2.1)
    let margin := min margin10 (min margin21 margin02)
    have hmargin : 0 < margin :=
      lt_min hmargin10 (lt_min hmargin21 hmargin02)
    exact ⟨{
      margin := margin
      margin_pos := hmargin
      first := p0
      second := p1
      third := p2
      second_ne_first := hp01.symm
      third_ne_first := hp02.symm
      third_ne_second := hp12.symm
      players_eq := hplayers
      first_edge := preempts_mono (min_le_left _ _) hedge10
      second_edge := preempts_mono
        ((min_le_right _ _).trans (min_le_left _ _)) hedge21
      closing_edge := preempts_mono
        ((min_le_right _ _).trans (min_le_right _ _)) hedge02 }⟩

/-- The selected proper hard principal on a rooted four-cycle yields either a
shorter strict cycle or a literal card-three external helper. -/
def HasFourCycleHardPrincipalAlignment
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (players : Finset (Fin 4)) : Prop :=
  (∃ _crossing : FinFourHardCardTwoCrossing residual players,
    Nonempty (FinFourHardPairShortTwoCycle (reward := reward) players)) ∨
    Nonempty (FinFourHardCardThreeExternalHelper reward players) ∨
      ∃ _boundary : FinFourHardCardThreeCyclicBoundary reward players,
        Nonempty (FinFourHardTripleShortThreeCycle (reward := reward) players)

theorem fourCycleHardPrincipalAlignment
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (players : Finset (Fin 4))
    (hcard : players.card = 2 ∨ players.card = 3)
    (hnot : ¬IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) players)) :
    residual.HasFourCycleHardPrincipalAlignment players := by
  rcases hcard with htwo | hthree
  · left
    obtain ⟨crossing⟩ := residual.cardTwoCrossing htwo hnot
    exact ⟨crossing, residual.cardTwoCrossing_shortTwoCycle crossing⟩
  · right
    rcases residual.cardThree_externalHelper_or_cyclicBoundary hthree hnot with
      hexternal | hcyclic
    · exact Or.inl hexternal
    · right
      obtain ⟨boundary⟩ := hcyclic
      exact ⟨boundary, cyclicBoundary_shortThreeCycle boundary⟩

/-- If the selected hard pair is the literal collision owner/collider pair,
the terminal toggle is either a strengthened owner leave or an outsider
join.  The strengthening uses the actual negative singleton entry and need
not preserve that entry's margin as the terminal gap. -/
theorem ownerColliderHardPair_strongLeave_or_outsiderJoin
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap)
    (crossing : FinFourHardCardTwoCrossing residual
      {certificate.owner, certificate.collider}) :
    (∃ epsilon, 0 < epsilon ∧
      epsilon = -normalizedSoloMatrix reward certificate.owner
        certificate.collider ∧
      quittingSetReward reward {certificate.owner, certificate.collider}
            certificate.owner + residual.witness.terminalGap + epsilon ≤
        quittingSoloReward reward certificate.owner certificate.owner) ∨
      ∃ outsider ∉
          ({certificate.owner, certificate.collider} : Finset (Fin 4)),
        quittingSetReward reward {certificate.owner, certificate.collider}
              outsider + residual.witness.terminalGap ≤
          quittingSetReward reward
            (insert outsider {certificate.owner, certificate.collider})
            outsider := by
  have hownerMem : certificate.owner ∈
      ({crossing.first, crossing.second} : Finset (Fin 4)) := by
    rw [← crossing.players_eq]
    simp
  have hcolliderMem : certificate.collider ∈
      ({crossing.first, crossing.second} : Finset (Fin 4)) := by
    rw [← crossing.players_eq]
    simp
  have hownerLabel : certificate.owner = crossing.first ∨
      certificate.owner = crossing.second := by simpa using hownerMem
  have hcolliderLabel : certificate.collider = crossing.first ∨
      certificate.collider = crossing.second := by simpa using hcolliderMem
  have hnegative : normalizedSoloMatrix reward certificate.owner
      certificate.collider < 0 := by
    rcases hownerLabel with howner | howner <;>
      rcases hcolliderLabel with hcollider | hcollider
    · exact (certificate.collider_ne_owner (hcollider.trans howner.symm)).elim
    · simpa [howner, hcollider] using crossing.first_harmed
    · simpa [howner, hcollider] using crossing.second_harmed
    · exact (certificate.collider_ne_owner (hcollider.trans howner.symm)).elim
  rcases residual.witness.exists_leave_or_join_gain
      ({certificate.owner, certificate.collider} : Finset (Fin 4)) with
    hleave | hjoin
  · obtain ⟨member, hmember, hgain⟩ := hleave
    have hlabel : member = certificate.owner ∨
        member = certificate.collider := by simpa using hmember
    rcases hlabel with howner | hcollider
    · subst member
      left
      let epsilon := -normalizedSoloMatrix reward certificate.owner
        certificate.collider
      have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
      have herase :
          ({certificate.owner, certificate.collider} : Finset (Fin 4)).erase
              certificate.owner = {certificate.collider} := by
        ext who
        simp [Ne.symm certificate.collider_ne_owner]
      rw [herase, quittingSetReward_singleton_eq_soloReward] at hgain
      have hmatrix := normalizedSoloMatrix_eq_soloReward_sub reward
        certificate.owner certificate.collider
      refine ⟨epsilon, hepsilon, rfl, ?_⟩
      dsimp [epsilon]
      linarith
    · subst member
      have herase :
          ({certificate.owner, certificate.collider} : Finset (Fin 4)).erase
              certificate.collider = {certificate.owner} := by
        rw [Finset.pair_comm, Finset.erase_insert]
        simpa using certificate.collider_ne_owner
      rw [herase, quittingSetReward_singleton_eq_soloReward,
        quittingSetReward_pair_right] at hgain
      linarith [certificate.collider_gain_floor,
        residual.witness.terminalGap_pos]
  · exact Or.inr hjoin

/-- Exact marker position in one of the three rooted-four constructors. -/
inductive FinFourRootedFourColliderPosition
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap)
    (geometry : RootedFourCycle
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner) : Prop where
  | first (collider_eq : certificate.collider = geometry.first)
  | second (collider_eq : certificate.collider = geometry.second)
  | third (collider_eq : certificate.collider = geometry.third)

/-- Source-retaining output on a rooted four-cycle constructor. -/
structure FinFourMarkedFourCycleHardPrincipalAlignment
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap) where
  geometry : RootedFourCycle
    (QuittingSoloPreempts reward residual.witness.terminalGap)
    certificate.owner
  colliderPosition : FinFourRootedFourColliderPosition residual certificate geometry
  hardPlayers : Finset (Fin 4)
  hardCard : hardPlayers.card = 2 ∨ hardPlayers.card = 3
  hardNot : ¬IsProjectiveQMatrix
    (principalMatrix (normalizedSoloMatrix reward) hardPlayers)
  alignment : residual.HasFourCycleHardPrincipalAlignment hardPlayers

/-- The fourteen marked constructors whose periodic cycle is not length
four. -/
def MarkedRootedLasso.HasNonFourCycle
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    {certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap}
    (geometry : MarkedRootedLasso
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner certificate.collider) : Prop :=
  match geometry with
  | .rootedFour_first _ _ => False
  | .rootedFour_second _ _ => False
  | .rootedFour_third _ _ => False
  | _ => True

/-- **Three-constructor source dispatch.**  The rooted four-cycle constructors
retain their exact collision-marker position and enter the selected
hard-principal shortening/helper theorem.  The other fourteen constructors
are characterized separately. -/
theorem markedFourCycleHardPrincipalAlignment_or_nonFour
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap)
    (marked : MarkedRootedLasso
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner certificate.collider) :
    Nonempty
        (FinFourMarkedFourCycleHardPrincipalAlignment residual certificate) ∨
      MarkedRootedLasso.HasNonFourCycle residual marked := by
  have finish
      (geometry : RootedFourCycle
        (QuittingSoloPreempts reward residual.witness.terminalGap)
        certificate.owner)
      (position : FinFourRootedFourColliderPosition residual certificate geometry) :
      Nonempty
        (FinFourMarkedFourCycleHardPrincipalAlignment residual certificate) := by
    obtain ⟨hardPlayers, hardCard, hardNot⟩ :=
      exists_nonprojectivePrincipal_card_two_or_three residual
    exact ⟨{
      geometry := geometry
      colliderPosition := position
      hardPlayers := hardPlayers
      hardCard := hardCard
      hardNot := hardNot
      alignment := residual.fourCycleHardPrincipalAlignment
        hardPlayers hardCard hardNot }⟩
  cases marked with
  | rootedFour_first geometry marker_eq =>
      exact Or.inl (finish geometry (.first marker_eq))
  | rootedFour_second geometry marker_eq =>
      exact Or.inl (finish geometry (.second marker_eq))
  | rootedFour_third geometry marker_eq =>
      exact Or.inl (finish geometry (.third marker_eq))
  | rootedTwo_next _ _ => exact Or.inr trivial
  | rootedTwo_outside _ _ => exact Or.inr trivial
  | rootedThree_first _ _ => exact Or.inr trivial
  | rootedThree_second _ _ => exact Or.inr trivial
  | rootedThree_outside _ _ => exact Or.inr trivial
  | oneToTwo_entry _ _ => exact Or.inr trivial
  | oneToTwo_other _ _ => exact Or.inr trivial
  | oneToTwo_outside _ _ => exact Or.inr trivial
  | oneToThree_entry _ _ => exact Or.inr trivial
  | oneToThree_second _ _ => exact Or.inr trivial
  | oneToThree_third _ _ => exact Or.inr trivial
  | twoToTwo_first _ _ => exact Or.inr trivial
  | twoToTwo_entry _ _ => exact Or.inr trivial
  | twoToTwo_other _ _ => exact Or.inr trivial

end FinFourQuantitativeFullSupportHardResidual

end GameTheory
