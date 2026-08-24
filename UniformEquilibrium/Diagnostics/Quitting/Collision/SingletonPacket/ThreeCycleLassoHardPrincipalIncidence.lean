/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.TwoCycleLassoHardPairAlignment
import
  UniformEquilibrium.Quitting.Classification.LCP.ThreeByThreeZeroDiagonalQ
import UniformEquilibrium.Quitting.Classification.LCP.PrincipalRestriction

/-!
# Three-cycle incidence with a proper hard principal

This file is finite singleton-matrix bookkeeping.  A literal strict
three-cycle in the four-player full-support residual either has a positive
helper in its unique outside column, is itself a negative-determinant hard
triple, or forces every selected proper hard principal through the outsider.

The output is not a stopping law, chronology, or equilibrium compiler.
-/

noncomputable section

namespace GameTheory

open Finset Math.LinearProgramming QuittingLCPClassification
open QuittingLCPClassification.ThreeByThreeZeroDiagonalQ
open QuittingLCPClassification.FinFourQuantitativeFullSupportHardResidual
open Math.FiniteSerialRelation

/-- Four distinct labels, three of which carry a directed strict-preemption
cycle at the terminal gap. -/
structure FinFourStrictPreemptionThreeCycle
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (gap : ℝ) where
  first : Fin 4
  second : Fin 4
  third : Fin 4
  outsider : Fin 4
  second_ne_first : second ≠ first
  third_ne_first : third ≠ first
  third_ne_second : third ≠ second
  outsider_ne_first : outsider ≠ first
  outsider_ne_second : outsider ≠ second
  outsider_ne_third : outsider ≠ third
  first_edge : QuittingSoloPreempts reward gap first second
  second_edge : QuittingSoloPreempts reward gap second third
  closing_edge : QuittingSoloPreempts reward gap third first

namespace FinFourStrictPreemptionThreeCycle

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {gap : ℝ}

/-- The literal three cycle. -/
def players (cycle : FinFourStrictPreemptionThreeCycle (reward := reward) gap) :
    Finset (Fin 4) :=
  {cycle.first, cycle.second, cycle.third}

theorem players_card
    (cycle : FinFourStrictPreemptionThreeCycle (reward := reward) gap) :
    cycle.players.card = 3 := by
  simp [players, Ne.symm cycle.second_ne_first,
    Ne.symm cycle.third_ne_first, Ne.symm cycle.third_ne_second]

theorem players_compl_eq
    (cycle : FinFourStrictPreemptionThreeCycle (reward := reward) gap) :
    cycle.playersᶜ = {cycle.outsider} := by
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro who hwho
    have hwhoEq : who = cycle.outsider := by simpa using hwho
    subst who
    simp [players, cycle.outsider_ne_first, cycle.outsider_ne_second,
      cycle.outsider_ne_third]
  · rw [Finset.card_compl, cycle.players_card]
    norm_num

/-- Ordered vertices of the cycle. -/
def vertex (cycle : FinFourStrictPreemptionThreeCycle (reward := reward) gap) :
    Fin 3 → Fin 4
  | 0 => cycle.first
  | 1 => cycle.second
  | 2 => cycle.third

theorem vertex_injective
    (cycle : FinFourStrictPreemptionThreeCycle (reward := reward) gap) :
    Function.Injective cycle.vertex := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [vertex, cycle.second_ne_first, cycle.third_ne_first,
      cycle.third_ne_second, Ne.symm cycle.second_ne_first,
      Ne.symm cycle.third_ne_first, Ne.symm cycle.third_ne_second]

theorem vertex_mem_players
    (cycle : FinFourStrictPreemptionThreeCycle (reward := reward) gap)
    (i : Fin 3) : cycle.vertex i ∈ cycle.players := by
  fin_cases i <;> simp [vertex, players]

/-- The order-preserving equivalence from the three-cycle principal to
`Fin 3`. -/
def label (cycle : FinFourStrictPreemptionThreeCycle (reward := reward) gap) :
    cycle.players ≃ Fin 3 :=
  (Equiv.ofBijective
    (fun i : Fin 3 => (⟨cycle.vertex i, cycle.vertex_mem_players i⟩ :
      cycle.players))
    ⟨fun _ _ h => cycle.vertex_injective (congrArg Subtype.val h), by
      intro who
      have hmem : who.1 = cycle.first ∨ who.1 = cycle.second ∨
          who.1 = cycle.third := by
        simpa only [players, Finset.mem_insert, Finset.mem_singleton] using
          who.2
      rcases hmem with hfirst | hsecond | hthird
      · exact ⟨0, Subtype.ext hfirst.symm⟩
      · exact ⟨1, Subtype.ext hsecond.symm⟩
      · exact ⟨2, Subtype.ext hthird.symm⟩⟩).symm

@[simp] theorem label_symm_zero
    (cycle : FinFourStrictPreemptionThreeCycle (reward := reward) gap) :
    (cycle.label.symm 0).1 = cycle.first := rfl

@[simp] theorem label_symm_one
    (cycle : FinFourStrictPreemptionThreeCycle (reward := reward) gap) :
    (cycle.label.symm 1).1 = cycle.second := rfl

@[simp] theorem label_symm_two
    (cycle : FinFourStrictPreemptionThreeCycle (reward := reward) gap) :
    (cycle.label.symm 2).1 = cycle.third := rfl

end FinFourStrictPreemptionThreeCycle

namespace FinFourQuantitativeFullSupportHardResidual

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}

private theorem weighted_normalizedSoloMatrix_nonneg
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (receiver : Fin 4) :
    0 ≤ ∑ owner, residual.packet.mass owner *
      normalizedSoloMatrix reward receiver owner := by
  have hmass : 0 < residual.packet.mass receiver := by
    rw [← residual.packet.mem_support_iff,
      residual.packet_support_eq_univ]
    exact Finset.mem_univ receiver
  have hmix := residual.packet.mix_ge_target receiver
  rw [residual.packet.positive_mass_pins_target receiver hmass] at hmix
  have hsum := residual.packet.mass_sum
  simp_rw [normalizedSoloMatrix_eq_soloReward_sub]
  calc
    0 ≤ quittingSingletonMixture reward residual.packet.mass receiver -
        quittingSoloReward reward receiver receiver :=
      sub_nonneg.mpr hmix
    _ = ∑ owner,
        residual.packet.mass owner *
          (quittingSoloReward reward owner receiver -
            quittingSoloReward reward receiver receiver) := by
      unfold quittingSingletonMixture
      have heq :
          (∑ owner, residual.packet.mass owner *
              (reward (quittingSingletonTerminal owner) receiver -
                reward (quittingSingletonTerminal receiver) receiver)) =
            (∑ owner, residual.packet.mass owner *
              reward (quittingSingletonTerminal owner) receiver) -
              reward (quittingSingletonTerminal receiver) receiver := by
        calc
          _ = ∑ owner,
              (residual.packet.mass owner *
                  reward (quittingSingletonTerminal owner) receiver -
                residual.packet.mass owner *
                  reward (quittingSingletonTerminal receiver) receiver) := by
            apply Finset.sum_congr rfl
            intro owner _
            ring
          _ = (∑ owner, residual.packet.mass owner *
                reward (quittingSingletonTerminal owner) receiver) -
              ∑ owner, residual.packet.mass owner *
                reward (quittingSingletonTerminal receiver) receiver := by
            exact Finset.sum_sub_distrib
              (fun owner : Fin 4 => residual.packet.mass owner *
                reward (quittingSingletonTerminal owner) receiver)
              (fun owner : Fin 4 => residual.packet.mass owner *
                reward (quittingSingletonTerminal receiver) receiver)
          _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]
      simpa only [quittingSoloReward, quittingSingletonTerminal] using heq.symm

private theorem reverseOrientation_of_no_outside_help
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (cycle : FinFourStrictPreemptionThreeCycle (reward := reward)
      residual.witness.terminalGap)
    (houtside : ∀ receiver ∈ cycle.players,
      normalizedSoloMatrix reward receiver cycle.outsider ≤ 0) :
    ReverseOrientation
      (reindexMatrix cycle.label
        (principalMatrix (normalizedSoloMatrix reward) cycle.players)) := by
  let M := normalizedSoloMatrix reward
  have hmass (who : Fin 4) : 0 < residual.packet.mass who := by
    rw [← residual.packet.mem_support_iff,
      residual.packet_support_eq_univ]
    exact Finset.mem_univ who
  have huniv : (Finset.univ : Finset (Fin 4)) =
      {cycle.first, cycle.second, cycle.third, cycle.outsider} := by
    apply Eq.symm
    apply (Finset.card_eq_iff_eq_univ _).mp
    simp [Ne.symm cycle.second_ne_first, Ne.symm cycle.third_ne_first,
      Ne.symm cycle.third_ne_second, Ne.symm cycle.outsider_ne_first,
      Ne.symm cycle.outsider_ne_second, Ne.symm cycle.outsider_ne_third]
  have hfirstNeg : M cycle.second cycle.first < 0 := by
    have hle := (quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg reward
      residual.witness.terminalGap cycle.first cycle.second).mp
        cycle.first_edge |>.2
    linarith [residual.witness.terminalGap_pos]
  have hsecondNeg : M cycle.third cycle.second < 0 := by
    have hle := (quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg reward
      residual.witness.terminalGap cycle.second cycle.third).mp
        cycle.second_edge |>.2
    linarith [residual.witness.terminalGap_pos]
  have hclosingNeg : M cycle.first cycle.third < 0 := by
    have hle := (quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg reward
      residual.witness.terminalGap cycle.third cycle.first).mp
        cycle.closing_edge |>.2
    linarith [residual.witness.terminalGap_pos]
  have haverage_eq (receiver : Fin 4) :
      (∑ owner, residual.packet.mass owner * M receiver owner) =
        residual.packet.mass cycle.first * M receiver cycle.first +
          (residual.packet.mass cycle.second * M receiver cycle.second +
            (residual.packet.mass cycle.third * M receiver cycle.third +
              residual.packet.mass cycle.outsider *
                M receiver cycle.outsider)) := by
    rw [huniv]
    rw [Finset.sum_insert (by
      simp [Ne.symm cycle.second_ne_first, Ne.symm cycle.third_ne_first,
        Ne.symm cycle.outsider_ne_first])]
    rw [Finset.sum_insert (by
      simp [Ne.symm cycle.third_ne_second,
        Ne.symm cycle.outsider_ne_second])]
    rw [Finset.sum_insert (by
      simp [Ne.symm cycle.outsider_ne_third])]
    rw [Finset.sum_singleton]
  have hfirstSecond : 0 < M cycle.first cycle.second := by
    by_contra hnot
    have havg := residual.weighted_normalizedSoloMatrix_nonneg cycle.first
    have hdiag : M cycle.first cycle.first = 0 :=
      normalizedSoloMatrix_diagonal reward cycle.first
    rw [haverage_eq, hdiag, mul_zero, zero_add] at havg
    have hout := houtside cycle.first (by simp [FinFourStrictPreemptionThreeCycle.players])
    nlinarith [mul_neg_of_pos_of_neg (hmass cycle.third) hclosingNeg,
      mul_nonpos_of_nonneg_of_nonpos
        (residual.packet.mass_nonneg cycle.second) (le_of_not_gt hnot),
      mul_nonpos_of_nonneg_of_nonpos
        (residual.packet.mass_nonneg cycle.outsider) hout]
  have hsecondThird : 0 < M cycle.second cycle.third := by
    by_contra hnot
    have havg := residual.weighted_normalizedSoloMatrix_nonneg cycle.second
    have hdiag : M cycle.second cycle.second = 0 :=
      normalizedSoloMatrix_diagonal reward cycle.second
    rw [haverage_eq, hdiag, mul_zero] at havg
    have hout := houtside cycle.second (by simp [FinFourStrictPreemptionThreeCycle.players])
    nlinarith [mul_neg_of_pos_of_neg (hmass cycle.first) hfirstNeg,
      mul_nonpos_of_nonneg_of_nonpos
        (residual.packet.mass_nonneg cycle.third) (le_of_not_gt hnot),
      mul_nonpos_of_nonneg_of_nonpos
        (residual.packet.mass_nonneg cycle.outsider) hout]
  have hthirdFirst : 0 < M cycle.third cycle.first := by
    by_contra hnot
    have havg := residual.weighted_normalizedSoloMatrix_nonneg cycle.third
    have hdiag : M cycle.third cycle.third = 0 :=
      normalizedSoloMatrix_diagonal reward cycle.third
    rw [haverage_eq, hdiag, mul_zero] at havg
    have hout := houtside cycle.third (by simp [FinFourStrictPreemptionThreeCycle.players])
    nlinarith [mul_neg_of_pos_of_neg (hmass cycle.second) hsecondNeg,
      mul_nonpos_of_nonneg_of_nonpos
        (residual.packet.mass_nonneg cycle.first) (le_of_not_gt hnot),
      mul_nonpos_of_nonneg_of_nonpos
        (residual.packet.mass_nonneg cycle.outsider) hout]
  exact ⟨hfirstSecond, hclosingNeg, hfirstNeg, hsecondThird,
    hthirdFirst, hsecondNeg⟩

private theorem hasHomogeneous_iff_cycleDeterminant_eq_zero_of_reverse
    (matrix : Fin 3 → Fin 3 → ℝ)
    (hdiag : ∀ i, matrix i i = 0)
    (horientation : ReverseOrientation matrix) :
    HasHomogeneousSimplexSolution matrix ↔ cycleDeterminant matrix = 0 := by
  let swapped := reindexMatrix swapOneTwo matrix
  have hforward : ForwardOrientation swapped :=
    forward_reindex_of_reverse matrix horientation
  have hdiagSwapped : ∀ i, swapped i i = 0 := by
    intro i
    simp [swapped, reindexMatrix, hdiag]
  have heq : swapped = directedCycleMatrix
      (-swapped 0 1) (swapped 0 2) (swapped 1 0)
      (-swapped 1 2) (-swapped 2 0) (swapped 2 1) := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [directedCycleMatrix, hdiagSwapped]
  rcases hforward with ⟨h01, h02, h10, h12, h20, h21⟩
  have hhomSwapped :
      HasHomogeneousSimplexSolution swapped ↔
        cycleGap (-swapped 0 1) (swapped 0 2) (swapped 1 0)
          (-swapped 1 2) (-swapped 2 0) (swapped 2 1) = 0 := by
    constructor
    · intro hhom
      apply (directedCycleMatrix_hasHomogeneous_iff
        (neg_pos.mpr h01) h02 h10 (neg_pos.mpr h12) (neg_pos.mpr h20) h21).1
      rwa [← heq]
    · intro hgap
      have hhom := (directedCycleMatrix_hasHomogeneous_iff
        (neg_pos.mpr h01) h02 h10 (neg_pos.mpr h12) (neg_pos.mpr h20) h21).2
          hgap
      rwa [heq]
  have hgapDet :
      cycleGap (-swapped 0 1) (swapped 0 2) (swapped 1 0)
          (-swapped 1 2) (-swapped 2 0) (swapped 2 1) =
        cycleDeterminant swapped := by
    simp [cycleGap, cycleDeterminant]
    ring
  have hdetSwap : cycleDeterminant swapped = cycleDeterminant matrix := by
    simp [swapped, reindexMatrix, cycleDeterminant]
    ring
  calc
    HasHomogeneousSimplexSolution matrix ↔
        HasHomogeneousSimplexSolution swapped :=
      (singletonLCPFeasible_reindexMatrix_iff swapOneTwo matrix).symm
    _ ↔ _ := hhomSwapped
    _ ↔ _ := by rw [hgapDet, hdetSwap]

private theorem isProjective_of_reverseOrientation_cycleDeterminant_nonneg
    (matrix : Fin 3 → Fin 3 → ℝ)
    (hdiag : ∀ i, matrix i i = 0)
    (horientation : ReverseOrientation matrix)
    (hdet : 0 ≤ cycleDeterminant matrix) :
    IsProjectiveQMatrix matrix := by
  by_cases hzero : cycleDeterminant matrix = 0
  · apply (isProjectiveQMatrix_iff_standard_or_homogeneous matrix).2
    exact Or.inr
      ((hasHomogeneous_iff_cycleDeterminant_eq_zero_of_reverse
        matrix hdiag horientation).2 hzero)
  · have hpos : 0 < cycleDeterminant matrix := lt_of_le_of_ne hdet (Ne.symm hzero)
    have hstandard :=
      (standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_reverse
        matrix hdiag horientation).2 hpos |>.1
    exact (isProjectiveQMatrix_iff_standard_or_homogeneous matrix).2
      (Or.inl hstandard)

private theorem not_projective_of_reverseOrientation_cycleDeterminant_neg
    (matrix : Fin 3 → Fin 3 → ℝ)
    (hdiag : ∀ i, matrix i i = 0)
    (horientation : ReverseOrientation matrix)
    (hdet : cycleDeterminant matrix < 0) :
    ¬IsProjectiveQMatrix matrix := by
  have hnoHomogeneous : ¬HasHomogeneousSimplexSolution matrix := by
    rw [hasHomogeneous_iff_cycleDeterminant_eq_zero_of_reverse
      matrix hdiag horientation]
    exact hdet.ne
  intro hprojective
  have hstandard :=
    ((isProjectiveQMatrix_iff_standard_or_homogeneous matrix).1
      hprojective).resolve_right hnoHomogeneous
  have hpos :=
    (standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_reverse
      matrix hdiag horientation).1 ⟨hstandard, hnoHomogeneous⟩
  linarith

/-- Exhaustive same-label incidence for one literal strict three-cycle and
one selected proper hard principal. -/
def HasThreeCycleHardPrincipalIncidence
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (cycle : FinFourStrictPreemptionThreeCycle (reward := reward)
      residual.witness.terminalGap)
    (hardPlayers : Finset (Fin 4)) : Prop :=
  Nonempty (FinFourHardCardThreeExternalHelper reward cycle.players) ∨
    (∃ _boundary : FinFourHardCardThreeCyclicBoundary reward cycle.players,
      let matrix := reindexMatrix cycle.label
        (principalMatrix (normalizedSoloMatrix reward) cycle.players)
      cycleDeterminant matrix < 0 ∧
        ¬IsProjectiveQMatrix
          (principalMatrix (normalizedSoloMatrix reward) cycle.players)) ∨
    (cycle.outsider ∈ hardPlayers ∧
      IsProjectiveQMatrix
        (principalMatrix (normalizedSoloMatrix reward) cycle.players))

/-- Full packet support completes the three internal reverse signs.  The
determinant then separates a literal outside helper, a hard literal triple,
or a projective literal triple forcing the selected hard principal through
the unique outsider. -/
theorem threeCycleHardPrincipalIncidence
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (cycle : FinFourStrictPreemptionThreeCycle (reward := reward)
      residual.witness.terminalGap)
    (hardPlayers : Finset (Fin 4))
    (hardCard : hardPlayers.card = 2 ∨ hardPlayers.card = 3)
    (hardNot : ¬IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) hardPlayers)) :
    residual.HasThreeCycleHardPrincipalIncidence cycle hardPlayers := by
  let matrix := reindexMatrix cycle.label
    (principalMatrix (normalizedSoloMatrix reward) cycle.players)
  by_cases hhelper : ∃ receiver ∈ cycle.players,
      0 < normalizedSoloMatrix reward receiver cycle.outsider
  · left
    obtain ⟨receiver, hreceiver, hpositive⟩ := hhelper
    have hlabel : receiver = cycle.first ∨ receiver = cycle.second ∨
        receiver = cycle.third := by
      simpa only [FinFourStrictPreemptionThreeCycle.players,
        Finset.mem_insert, Finset.mem_singleton] using hreceiver
    rcases hlabel with hfirst | hsecond | hthird
    · subst receiver
      exact ⟨{
        outsider := cycle.outsider
        owner := cycle.third
        harmed := cycle.first
        complement_eq := cycle.players_compl_eq
        owner_mem := by simp [FinFourStrictPreemptionThreeCycle.players]
        harmed_mem := by simp [FinFourStrictPreemptionThreeCycle.players]
        harmed_by_owner := by
          have hle :=
            (quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg reward
              residual.witness.terminalGap cycle.third cycle.first).mp
              cycle.closing_edge |>.2
          linarith [residual.witness.terminalGap_pos]
        helped_by_outsider := hpositive }⟩
    · subst receiver
      exact ⟨{
        outsider := cycle.outsider
        owner := cycle.first
        harmed := cycle.second
        complement_eq := cycle.players_compl_eq
        owner_mem := by simp [FinFourStrictPreemptionThreeCycle.players]
        harmed_mem := by simp [FinFourStrictPreemptionThreeCycle.players]
        harmed_by_owner := by
          have hle :=
            (quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg reward
              residual.witness.terminalGap cycle.first cycle.second).mp
              cycle.first_edge |>.2
          linarith [residual.witness.terminalGap_pos]
        helped_by_outsider := hpositive }⟩
    · subst receiver
      exact ⟨{
        outsider := cycle.outsider
        owner := cycle.second
        harmed := cycle.third
        complement_eq := cycle.players_compl_eq
        owner_mem := by simp [FinFourStrictPreemptionThreeCycle.players]
        harmed_mem := by simp [FinFourStrictPreemptionThreeCycle.players]
        harmed_by_owner := by
          have hle :=
            (quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg reward
              residual.witness.terminalGap cycle.second cycle.third).mp
              cycle.second_edge |>.2
          linarith [residual.witness.terminalGap_pos]
        helped_by_outsider := hpositive }⟩
  · right
    have houtside : ∀ receiver ∈ cycle.players,
        normalizedSoloMatrix reward receiver cycle.outsider ≤ 0 := by
      push Not at hhelper
      exact hhelper
    have horientation := residual.reverseOrientation_of_no_outside_help
      cycle houtside
    have hdiag : ∀ i, matrix i i = 0 := by
      intro i
      simp [matrix, reindexMatrix, principalMatrix,
        normalizedSoloMatrix_diagonal]
    by_cases hdet : cycleDeterminant matrix < 0
    · left
      have hnotMatrix :=
        not_projective_of_reverseOrientation_cycleDeterminant_neg
          matrix hdiag horientation hdet
      have hnotLiteral : ¬IsProjectiveQMatrix
          (principalMatrix (normalizedSoloMatrix reward) cycle.players) := by
        intro hprojective
        exact hnotMatrix
          ((isProjectiveQMatrix_reindexMatrix_iff cycle.label _).2 hprojective)
      exact ⟨{
        label := cycle.label
        orientation := Or.inr horientation
        determinant_nonpos := hdet.le }, hdet, hnotLiteral⟩
    · right
      have hdetNonneg : 0 ≤ cycleDeterminant matrix := le_of_not_gt hdet
      have hprojectiveMatrix :=
        isProjective_of_reverseOrientation_cycleDeterminant_nonneg
          matrix hdiag horientation hdetNonneg
      have hprojectiveLiteral : IsProjectiveQMatrix
          (principalMatrix (normalizedSoloMatrix reward) cycle.players) := by
        exact (isProjectiveQMatrix_reindexMatrix_iff cycle.label _).mp
          hprojectiveMatrix
      refine ⟨?_, hprojectiveLiteral⟩
      by_contra houtHard
      have hsubset : hardPlayers ⊆ cycle.players := by
        intro who hwho
        by_contra houtCycle
        have hcomp : who ∈ cycle.playersᶜ := by simpa using houtCycle
        rw [cycle.players_compl_eq] at hcomp
        have : who = cycle.outsider := by simpa using hcomp
        exact houtHard (this ▸ hwho)
      rcases hardCard with htwo | hthree
      · obtain ⟨crossing⟩ := residual.cardTwoCrossing htwo hardNot
        have hfirstHard : crossing.first ∈ hardPlayers := by
          exact crossing.players_eq.symm.le (by simp)
        have hsecondHard : crossing.second ∈ hardPlayers := by
          exact crossing.players_eq.symm.le (by simp)
        have hfirstMem := hsubset hfirstHard
        have hsecondMem := hsubset hsecondHard
        have hnoReciprocal {first second : Fin 4}
            (hfirst : first ∈ cycle.players)
            (hsecond : second ∈ cycle.players)
            (hne : first ≠ second) :
            ¬(normalizedSoloMatrix reward first second < 0 ∧
              normalizedSoloMatrix reward second first < 0) := by
          have hfirstLabel : first = cycle.first ∨ first = cycle.second ∨
              first = cycle.third := by
            simpa only [FinFourStrictPreemptionThreeCycle.players,
              Finset.mem_insert, Finset.mem_singleton] using hfirst
          have hsecondLabel : second = cycle.first ∨ second = cycle.second ∨
              second = cycle.third := by
            simpa only [FinFourStrictPreemptionThreeCycle.players,
              Finset.mem_insert, Finset.mem_singleton] using hsecond
          have h01 : 0 < normalizedSoloMatrix reward cycle.first cycle.second := by
            simpa [matrix, reindexMatrix, principalMatrix] using horientation.1
          have h02 : normalizedSoloMatrix reward cycle.first cycle.third < 0 := by
            simpa [matrix, reindexMatrix, principalMatrix] using
              horientation.2.1
          have h10 : normalizedSoloMatrix reward cycle.second cycle.first < 0 := by
            simpa [matrix, reindexMatrix, principalMatrix] using
              horientation.2.2.1
          have h12 : 0 < normalizedSoloMatrix reward cycle.second cycle.third := by
            simpa [matrix, reindexMatrix, principalMatrix] using
              horientation.2.2.2.1
          have h20 : 0 < normalizedSoloMatrix reward cycle.third cycle.first := by
            simpa [matrix, reindexMatrix, principalMatrix] using
              horientation.2.2.2.2.1
          have h21 : normalizedSoloMatrix reward cycle.third cycle.second < 0 := by
            simpa [matrix, reindexMatrix, principalMatrix] using
              horientation.2.2.2.2.2
          rintro ⟨hforward, hbackward⟩
          rcases hfirstLabel with hff | hfs | hft <;>
            rcases hsecondLabel with hsf | hss | hst <;>
            subst_vars <;> try exact (hne rfl).elim
          all_goals linarith [h01, h02, h10, h12, h20, h21]
        exact hnoReciprocal hfirstMem hsecondMem crossing.first_ne_second
          ⟨crossing.first_harmed, crossing.second_harmed⟩
      · have heq : hardPlayers = cycle.players := by
          apply Finset.eq_of_subset_of_card_le hsubset
          rw [cycle.players_card, hthree]
        rw [heq] at hardNot
        exact hardNot hprojectiveLiteral

/-- Exact owner/collider incidence of the six marked length-three lasso
constructors. -/
inductive FinFourMarkedThreeCycleRoles
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap)
    (cycle : FinFourStrictPreemptionThreeCycle (reward := reward)
      residual.witness.terminalGap) : Prop where
  | ownerOutside
      (owner_eq : certificate.owner = cycle.outsider)
      (collider_mem : certificate.collider ∈ cycle.players)
  | colliderOutside
      (owner_mem : certificate.owner ∈ cycle.players)
      (collider_eq : certificate.collider = cycle.outsider)
  | bothInside
      (owner_mem : certificate.owner ∈ cycle.players)
      (collider_mem : certificate.collider ∈ cycle.players)

/-- Source-retaining output for a marked length-three constructor. -/
structure FinFourMarkedThreeCycleHardPrincipalIncidence
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap) where
  cycle : FinFourStrictPreemptionThreeCycle (reward := reward)
    residual.witness.terminalGap
  hardPlayers : Finset (Fin 4)
  hardCard : hardPlayers.card = 2 ∨ hardPlayers.card = 3
  hardNot : ¬IsProjectiveQMatrix
    (principalMatrix (normalizedSoloMatrix reward) hardPlayers)
  incidence : residual.HasThreeCycleHardPrincipalIncidence cycle hardPlayers
  roles : FinFourMarkedThreeCycleRoles residual certificate cycle

/-- The eleven marked constructors which do not have cycle length three. -/
def MarkedRootedLasso.HasNonThreeCycle
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    {certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap}
    (geometry : MarkedRootedLasso
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner certificate.collider) : Prop :=
  match geometry with
  | .rootedThree_first _ _ => False
  | .rootedThree_second _ _ => False
  | .rootedThree_outside _ _ => False
  | .oneToThree_entry _ _ => False
  | .oneToThree_second _ _ => False
  | .oneToThree_third _ _ => False
  | _ => True

private theorem exists_outside_three
    (first second third : Fin 4)
    (hsecond : second ≠ first) (hthirdFirst : third ≠ first)
    (hthirdSecond : third ≠ second) :
    ∃ outsider, outsider ≠ first ∧ outsider ≠ second ∧ outsider ≠ third := by
  let players : Finset (Fin 4) := {first, second, third}
  have hcard : players.card = 3 := by
    simp [players, Ne.symm hsecond, Ne.symm hthirdFirst,
      Ne.symm hthirdSecond]
  have hcompCard : playersᶜ.card = 1 := by
    rw [Finset.card_compl, hcard]
    norm_num
  obtain ⟨outsider, hcomp⟩ := Finset.card_eq_one.mp hcompCard
  have houtside : outsider ∈ playersᶜ := by rw [hcomp]; simp
  simp only [Finset.mem_compl, players, Finset.mem_insert,
    Finset.mem_singleton, not_or] at houtside
  exact ⟨outsider, houtside.1, houtside.2.1, houtside.2.2⟩

/-- **Six-constructor source dispatch.**  Every marked length-three geometry
enters the same-table hard-principal incidence theorem with its exact
owner/collider role.  The other eleven constructors are characterized
separately and receive no output. -/
theorem markedThreeCycleHardPrincipalIncidence_or_nonThree
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap)
    (geometry : MarkedRootedLasso
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner certificate.collider) :
    Nonempty
        (FinFourMarkedThreeCycleHardPrincipalIncidence residual certificate) ∨
      MarkedRootedLasso.HasNonThreeCycle residual geometry := by
  have finish
      (cycle : FinFourStrictPreemptionThreeCycle (reward := reward)
        residual.witness.terminalGap)
      (roles : FinFourMarkedThreeCycleRoles residual certificate cycle) :
      Nonempty
        (FinFourMarkedThreeCycleHardPrincipalIncidence residual certificate) := by
    obtain ⟨hardPlayers, hardCard, hardNot⟩ :=
      exists_nonprojectivePrincipal_card_two_or_three residual
    exact ⟨{
      cycle := cycle
      hardPlayers := hardPlayers
      hardCard := hardCard
      hardNot := hardNot
      incidence := residual.threeCycleHardPrincipalIncidence
        cycle hardPlayers hardCard hardNot
      roles := roles }⟩
  cases geometry with
  | rootedTwo_next _ _ => exact Or.inr trivial
  | rootedTwo_outside _ _ => exact Or.inr trivial
  | rootedFour_first _ _ => exact Or.inr trivial
  | rootedFour_second _ _ => exact Or.inr trivial
  | rootedFour_third _ _ => exact Or.inr trivial
  | oneToTwo_entry _ _ => exact Or.inr trivial
  | oneToTwo_other _ _ => exact Or.inr trivial
  | oneToTwo_outside _ _ => exact Or.inr trivial
  | twoToTwo_first _ _ => exact Or.inr trivial
  | twoToTwo_entry _ _ => exact Or.inr trivial
  | twoToTwo_other _ _ => exact Or.inr trivial
  | rootedThree_first rooted marker_eq =>
      left
      obtain ⟨outsider, houtRoot, houtFirst, houtSecond⟩ :=
        exists_outside_three certificate.owner rooted.first rooted.second
          rooted.first_ne_root rooted.second_ne_root rooted.second_ne_first
      let cycle : FinFourStrictPreemptionThreeCycle
          (reward := reward) residual.witness.terminalGap := {
        first := certificate.owner
        second := rooted.first
        third := rooted.second
        outsider := outsider
        second_ne_first := rooted.first_ne_root
        third_ne_first := rooted.second_ne_root
        third_ne_second := rooted.second_ne_first
        outsider_ne_first := houtRoot
        outsider_ne_second := houtFirst
        outsider_ne_third := houtSecond
        first_edge := rooted.first_edge
        second_edge := rooted.second_edge
        closing_edge := rooted.closing_edge }
      exact finish cycle (.bothInside (by simp [cycle,
        FinFourStrictPreemptionThreeCycle.players]) (by
          rw [marker_eq]
          simp [cycle, FinFourStrictPreemptionThreeCycle.players]))
  | rootedThree_second rooted marker_eq =>
      left
      obtain ⟨outsider, houtRoot, houtFirst, houtSecond⟩ :=
        exists_outside_three certificate.owner rooted.first rooted.second
          rooted.first_ne_root rooted.second_ne_root rooted.second_ne_first
      let cycle : FinFourStrictPreemptionThreeCycle
          (reward := reward) residual.witness.terminalGap := {
        first := certificate.owner
        second := rooted.first
        third := rooted.second
        outsider := outsider
        second_ne_first := rooted.first_ne_root
        third_ne_first := rooted.second_ne_root
        third_ne_second := rooted.second_ne_first
        outsider_ne_first := houtRoot
        outsider_ne_second := houtFirst
        outsider_ne_third := houtSecond
        first_edge := rooted.first_edge
        second_edge := rooted.second_edge
        closing_edge := rooted.closing_edge }
      exact finish cycle (.bothInside (by simp [cycle,
        FinFourStrictPreemptionThreeCycle.players]) (by
          rw [marker_eq]
          simp [cycle, FinFourStrictPreemptionThreeCycle.players]))
  | rootedThree_outside rooted marker_outside =>
      left
      have houtside : certificate.collider ≠ certificate.owner ∧
          certificate.collider ≠ rooted.first ∧
          certificate.collider ≠ rooted.second := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
          marker_outside
      let cycle : FinFourStrictPreemptionThreeCycle
          (reward := reward) residual.witness.terminalGap := {
        first := certificate.owner
        second := rooted.first
        third := rooted.second
        outsider := certificate.collider
        second_ne_first := rooted.first_ne_root
        third_ne_first := rooted.second_ne_root
        third_ne_second := rooted.second_ne_first
        outsider_ne_first := houtside.1
        outsider_ne_second := houtside.2.1
        outsider_ne_third := houtside.2.2
        first_edge := rooted.first_edge
        second_edge := rooted.second_edge
        closing_edge := rooted.closing_edge }
      exact finish cycle (.colliderOutside (by simp [cycle,
        FinFourStrictPreemptionThreeCycle.players]) rfl)
  | oneToThree_entry tail marker_eq =>
      left
      let cycle : FinFourStrictPreemptionThreeCycle
          (reward := reward) residual.witness.terminalGap := {
        first := tail.entry
        second := tail.second
        third := tail.third
        outsider := certificate.owner
        second_ne_first := tail.second_ne_entry
        third_ne_first := tail.third_ne_entry
        third_ne_second := tail.third_ne_second
        outsider_ne_first := Ne.symm tail.entry_ne_root
        outsider_ne_second := Ne.symm tail.second_ne_root
        outsider_ne_third := Ne.symm tail.third_ne_root
        first_edge := tail.first_cycle_edge
        second_edge := tail.second_cycle_edge
        closing_edge := tail.closing_edge }
      exact finish cycle (.ownerOutside rfl (by
        rw [marker_eq]
        simp [cycle, FinFourStrictPreemptionThreeCycle.players]))
  | oneToThree_second tail marker_eq =>
      left
      let cycle : FinFourStrictPreemptionThreeCycle
          (reward := reward) residual.witness.terminalGap := {
        first := tail.entry
        second := tail.second
        third := tail.third
        outsider := certificate.owner
        second_ne_first := tail.second_ne_entry
        third_ne_first := tail.third_ne_entry
        third_ne_second := tail.third_ne_second
        outsider_ne_first := Ne.symm tail.entry_ne_root
        outsider_ne_second := Ne.symm tail.second_ne_root
        outsider_ne_third := Ne.symm tail.third_ne_root
        first_edge := tail.first_cycle_edge
        second_edge := tail.second_cycle_edge
        closing_edge := tail.closing_edge }
      exact finish cycle (.ownerOutside rfl (by
        rw [marker_eq]
        simp [cycle, FinFourStrictPreemptionThreeCycle.players]))
  | oneToThree_third tail marker_eq =>
      left
      let cycle : FinFourStrictPreemptionThreeCycle
          (reward := reward) residual.witness.terminalGap := {
        first := tail.entry
        second := tail.second
        third := tail.third
        outsider := certificate.owner
        second_ne_first := tail.second_ne_entry
        third_ne_first := tail.third_ne_entry
        third_ne_second := tail.third_ne_second
        outsider_ne_first := Ne.symm tail.entry_ne_root
        outsider_ne_second := Ne.symm tail.second_ne_root
        outsider_ne_third := Ne.symm tail.third_ne_root
        first_edge := tail.first_cycle_edge
        second_edge := tail.second_cycle_edge
        closing_edge := tail.closing_edge }
      exact finish cycle (.ownerOutside rfl (by
        rw [marker_eq]
        simp [cycle, FinFourStrictPreemptionThreeCycle.players]))

end FinFourQuantitativeFullSupportHardResidual

end GameTheory
