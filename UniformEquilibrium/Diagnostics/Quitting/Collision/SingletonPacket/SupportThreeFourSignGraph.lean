/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.SupportThreeFour
import UniformEquilibrium.Quitting.Classification.LCP.ThreeByThreeZeroDiagonalQ

/-!
# Finite sign graphs behind three- and four-point packet support

On three labels, one strict crossed row for every owner column forces one of
the two directed three-cycle sign orientations.  Applied to a support-three
counterexample packet, this gives an exact alternative: either a crossing
uses the unique outsider, or the support principal has a relabelled cyclic
sign orientation.  The existing three-dimensional LCP theorem then reduces
the standard-Q, nonhomogeneous screen to positivity of one determinant.

The analogous four-label conclusion is false.  A concrete zero-diagonal sign
table has a crossed row for every owner column but has two negative entries
in one row.  Every cyclic open-sign skeleton has at most one negative entry
per row, and relabeling preserves this obstruction.
-/

noncomputable section

namespace GameTheory

open Finset QuittingLCPClassification
open QuittingLCPClassification.ThreeByThreeZeroDiagonalQ
open Math.LinearProgramming

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

/-- Every owner column has a negative entry in a row which has a positive
entry in a different owner column. -/
def HasInternalCrossedRows (M : alpha → alpha → Real) : Prop :=
  ∀ owner, ∃ harmed helper,
    harmed ≠ owner ∧ helper ≠ owner ∧ helper ≠ harmed ∧
      M harmed owner < 0 ∧ 0 < M harmed helper

namespace ThreePointCrossedRows

private theorem forward_or_reverse
    (M : Fin 3 → Fin 3 → Real)
    (hcrossed : HasInternalCrossedRows M) :
    ForwardOrientation M ∨ ReverseOrientation M := by
  obtain ⟨harmed0, helper0, hharmed0, hhelper0, hpair0, hneg0, hpos0⟩ :=
    hcrossed 0
  obtain ⟨harmed1, helper1, hharmed1, hhelper1, hpair1, hneg1, hpos1⟩ :=
    hcrossed 1
  obtain ⟨harmed2, helper2, hharmed2, hhelper2, hpair2, hneg2, hpos2⟩ :=
    hcrossed 2
  fin_cases harmed0 <;> fin_cases helper0 <;>
    fin_cases harmed1 <;> fin_cases helper1 <;>
    fin_cases harmed2 <;> fin_cases helper2 <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      ne_eq, not_true_eq_false] at * <;>
    first
    | exact Or.inl ⟨hneg1, hpos1, hpos2, hneg2, hneg0, hpos0⟩
    | exact Or.inr ⟨hpos2, hneg2, hneg0, hpos0, hpos1, hneg1⟩
    | linarith

omit [DecidableEq alpha] in
/-- Coordinate-free three-label form: internal crossed rows force a
relabelled strict directed-cycle orientation. -/
theorem exists_cyclicLabeling_of_card_eq_three
    (M : alpha → alpha → Real)
    (hcard : Fintype.card alpha = 3)
    (hcrossed : HasInternalCrossedRows M) :
    ∃ label : alpha ≃ Fin 3,
      ForwardOrientation (reindexMatrix label M) ∨
        ReverseOrientation (reindexMatrix label M) := by
  let label : alpha ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  let N := reindexMatrix label M
  have hcrossedN : HasInternalCrossedRows N := by
    intro owner
    obtain ⟨harmed, helper, hharmed, hhelper, hpair, hneg, hpos⟩ :=
      hcrossed (label.symm owner)
    refine ⟨label harmed, label helper, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun heq ↦ hharmed (label.injective (by simpa using heq))
    · exact fun heq ↦ hhelper (label.injective (by simpa using heq))
    · exact fun heq ↦ hpair (label.injective heq)
    · simpa [N, reindexMatrix] using hneg
    · simpa [N, reindexMatrix] using hpos
  exact ⟨label, forward_or_reverse N hcrossedN⟩

end ThreePointCrossedRows

variable {reward : {S : Finset alpha // S.Nonempty} → Payoff alpha}

/-- The coherent support-three branch: a relabelled strict cyclic sign
orientation together with its exact determinant form of the existing LCP
screen. -/
structure QuittingSupportThreeCyclicSignScreen
    (packet : QuittingNormalizedSingletonSourcePacket reward) where
  label : packet.support ≃ Fin 3
  orientation :
    ForwardOrientation
        (reindexMatrix label
          (principalMatrix (normalizedSoloMatrix reward) packet.support)) ∨
      ReverseOrientation
        (reindexMatrix label
          (principalMatrix (normalizedSoloMatrix reward) packet.support))
  lcp_screen :
    let matrix := reindexMatrix label
      (principalMatrix (normalizedSoloMatrix reward) packet.support)
    IsStandardQMatrix matrix ∧ ¬HasHomogeneousSimplexSolution matrix ↔
      0 < cycleDeterminant matrix

namespace QuittingTerminalExploitabilityWitness

/-- **Support-three sign-graph dispatch.**  Either a forced crossed row uses
the unique outsider, or all three owner columns assemble into a relabelled
strict cycle carrying the exact three-dimensional determinant screen. -/
theorem supportThree_cyclicSignScreen_or_outsiderCrossing
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hplayers : Fintype.card alpha = 4)
    (hsupport : packet.support.card = 3) :
    ∃ outsider, packet.supportᶜ = {outsider} ∧
      (Nonempty (QuittingSupportThreeCyclicSignScreen packet) ∨
        ∃ (owner : alpha) (row : QuittingPacketCrossedRow packet owner),
          row.harmed = outsider) := by
  obtain ⟨outsider, houtside, hrows⟩ :=
    witness.exists_supportThree_crossedRow_dispatch packet hplayers hsupport
  refine ⟨outsider, houtside, ?_⟩
  by_cases hexternal :
      ∃ (owner : alpha) (row : QuittingPacketCrossedRow packet owner),
        row.harmed = outsider
  · exact Or.inr hexternal
  · left
    have hcrossed : HasInternalCrossedRows
        (principalMatrix (normalizedSoloMatrix reward) packet.support) := by
      intro owner
      obtain ⟨row, hrow⟩ := hrows owner.1 owner.2
      have hinternal : packet.support = {owner.1, row.harmed, row.helper} := by
        rcases hrow with hout | hin
        · exact False.elim (hexternal ⟨owner.1, row, hout⟩)
        · exact hin
      have hharmedMem : row.harmed ∈ packet.support := by
        apply hinternal.symm ▸
          (show row.harmed ∈ ({owner.1, row.harmed, row.helper} : Finset alpha) by
            simp)
      let harmed : packet.support := ⟨row.harmed, hharmedMem⟩
      let helper : packet.support := ⟨row.helper, row.helper_mem⟩
      refine ⟨harmed, helper, ?_, ?_, ?_, row.matrix_crossing.1,
        row.matrix_crossing.2⟩
      · exact fun heq ↦ row.harmed_ne_owner (congrArg Subtype.val heq)
      · exact fun heq ↦ row.helper_ne_owner (congrArg Subtype.val heq)
      · exact fun heq ↦ row.helper_ne_harmed (congrArg Subtype.val heq)
    have hcardSubtype : Fintype.card packet.support = 3 := by
      rw [Fintype.card_coe]
      exact hsupport
    have hdiag : ∀ who : packet.support,
        principalMatrix (normalizedSoloMatrix reward) packet.support who who = 0 := by
      intro who
      exact normalizedSoloMatrix_diagonal reward who.1
    obtain ⟨label, horientation⟩ :=
      ThreePointCrossedRows.exists_cyclicLabeling_of_card_eq_three
        (principalMatrix (normalizedSoloMatrix reward) packet.support)
        hcardSubtype hcrossed
    let matrix := reindexMatrix label
      (principalMatrix (normalizedSoloMatrix reward) packet.support)
    have hdiagMatrix : ∀ who, matrix who who = 0 := by
      intro who
      simp [matrix, reindexMatrix, hdiag]
    have hscreen : IsStandardQMatrix matrix ∧
        ¬HasHomogeneousSimplexSolution matrix ↔
          0 < cycleDeterminant matrix := by
      rcases horientation with hforward | hreverse
      · exact
          standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_forward
            matrix hdiagMatrix hforward
      · exact
          standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_reverse
            matrix hdiagMatrix hreverse
    exact ⟨⟨label, horientation, hscreen⟩⟩

end QuittingTerminalExploitabilityWitness

/-! ## Four-label obstruction to cyclic open-sign coherence -/

namespace FourPointCrossedRowsNoCyclicSign

abbrev Player := Fin 4

open QuittingSureSetOwnerRepair

/-- The finite matrix skeleton of the cyclic open-sign producer.  The total
sum condition is omitted: this is only a necessary part of that producer. -/
structure CyclicOpenSignSkeleton (M : Player → Player → Real) where
  gamma : Player → Real
  cyclic : ∀ who phase, M who phase = gamma (phase - who)
  gamma_zero : gamma 0 = 0
  first_neg : gamma 1 < 0
  later_nonneg : ∀ index : Player, 2 ≤ index.val → 0 ≤ gamma index

/-- A cyclic open-sign row contains at most one strictly negative entry. -/
theorem CyclicOpenSignSkeleton.negative_unique
    {M : Player → Player → Real}
    (skeleton : CyclicOpenSignSkeleton M)
    {who first second : Player}
    (hfirst : M who first < 0) (hsecond : M who second < 0) :
    first = second := by
  have offset_eq_one (phase : Player) (hneg : M who phase < 0) :
      (phase - who).val = 1 := by
    rw [skeleton.cyclic] at hneg
    by_cases hone : (phase - who).val = 1
    · exact hone
    by_cases hzero : (phase - who).val = 0
    · have hoffset : phase - who = 0 := Fin.ext hzero
      rw [hoffset, skeleton.gamma_zero] at hneg
      linarith
    · have hlater : 2 ≤ (phase - who).val := by
        omega
      linarith [skeleton.later_nonneg (phase - who) hlater]
  apply sub_left_injective (b := who)
  apply Fin.ext
  rw [offset_eq_one first hfirst, offset_eq_one second hsecond]

/-- A minimal zero-diagonal four-label table with a crossed row in every
owner column but two negative entries in row `2`. -/
def matrix : Player → Player → Real := fun who owner ↦
  if who = 0 then ![0, -1, 1, 1] owner
  else if who = 1 then ![1, 0, -1, 1] owner
  else if who = 2 then ![-1, 3, 0, -1] owner
  else ![1, 1, 1, 0] owner

theorem matrix_diagonal (who : Player) : matrix who who = 0 := by
  fin_cases who <;> simp +decide [matrix]

theorem matrix_hasInternalCrossedRows : HasInternalCrossedRows matrix := by
  intro owner
  fin_cases owner
  · exact ⟨2, 1, by decide, by decide, by decide, by simp +decide [matrix],
      by simp +decide [matrix]⟩
  · exact ⟨0, 2, by decide, by decide, by decide, by simp +decide [matrix],
      by simp +decide [matrix]⟩
  · exact ⟨1, 0, by decide, by decide, by decide, by simp +decide [matrix],
      by simp +decide [matrix]⟩
  · exact ⟨2, 1, by decide, by decide, by decide, by simp +decide [matrix],
      by simp +decide [matrix]⟩

/-- Realize the sign table as singleton terminal rewards. -/
def tableReward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who ↦ matrix who (Classical.choose terminal.2)

private theorem tableReward_singleton (owner who : Player) :
    tableReward (quittingSingletonTerminal owner) who = matrix who owner := by
  unfold tableReward quittingSingletonTerminal
  congr 1
  have hmem := Classical.choose_spec (Finset.singleton_nonempty owner)
  simpa using hmem

def mass (_owner : Player) : Real := 1 / 4

private theorem mass_sum : ∑ owner, mass owner = 1 := by
  simp [mass]

private theorem singletonMixture_nonneg (who : Player) :
    0 ≤ quittingSingletonMixture tableReward mass who := by
  unfold quittingSingletonMixture
  simp_rw [tableReward_singleton]
  fin_cases who <;>
    simp +decide [Fin.sum_univ_succ, mass, matrix] <;>
    norm_num

/-- The sign table is realized by an actual normalized packet with full
support, not only by an abstract matrix. -/
def packet : QuittingNormalizedSingletonSourcePacket tableReward where
  mass := mass
  target := fun _ ↦ 0
  mass_nonneg := fun _ ↦ by norm_num [mass]
  mass_sum := mass_sum
  mix_ge_target := singletonMixture_nonneg
  solo_le_target := fun who ↦ by
    rw [tableReward_singleton, matrix_diagonal]
  punishment_le_target := fun who ↦ by
    calc
      quittingPunishmentValue tableReward who ≤
          max (quittingSetReward tableReward {who} who) 0 :=
        quittingPunishmentValue_le_max_solo tableReward who
      _ = 0 := by
        rw [quittingSetReward_singleton_eq_soloReward]
        change max (tableReward (quittingSingletonTerminal who) who) 0 = 0
        rw [tableReward_singleton, matrix_diagonal]
        simp
  positive_mass_pins_target := fun owner _ ↦ by
    rw [tableReward_singleton, matrix_diagonal]

theorem packet_support : packet.support = Finset.univ := by
  ext owner
  simp [QuittingNormalizedSingletonSourcePacket.support, packet, mass]

theorem normalizedSoloMatrix_tableReward :
    normalizedSoloMatrix tableReward = matrix := by
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  funext who owner
  simp only [quittingProjectiveLCPMatrix]
  rw [show tableReward (quittingProjectiveSingletonTerminal owner) who =
      matrix who owner by
        exact tableReward_singleton owner who,
    show tableReward (quittingProjectiveSingletonTerminal who) who =
      matrix who who by
        exact tableReward_singleton who who,
    matrix_diagonal, sub_zero]

/-- No relabeling turns the crossed-row table into even the sign skeleton
required by the cyclic open-sign producer. -/
theorem not_exists_relabelledCyclicOpenSignSkeleton :
    ¬∃ label : Player ≃ Player,
      Nonempty (CyclicOpenSignSkeleton (reindexMatrix label matrix)) := by
  rintro ⟨label, ⟨skeleton⟩⟩
  have hfirst : reindexMatrix label matrix (label 2) (label 0) < 0 := by
    simp [reindexMatrix, matrix]
  have hsecond : reindexMatrix label matrix (label 2) (label 3) < 0 := by
    simp [reindexMatrix, matrix]
  have heq := skeleton.negative_unique hfirst hsecond
  exact (by decide : (0 : Player) ≠ 3) (label.injective heq)

/-- Packet-level boundary: full packet support and a crossed row in every
column still do not imply a relabelled cyclic open-sign skeleton. -/
theorem fullSupportPacket_crossed_but_not_cyclicOpenSign :
    packet.support = Finset.univ ∧
      HasInternalCrossedRows (normalizedSoloMatrix tableReward) ∧
      ¬∃ label : Player ≃ Player,
        Nonempty (CyclicOpenSignSkeleton
          (reindexMatrix label (normalizedSoloMatrix tableReward))) := by
  rw [normalizedSoloMatrix_tableReward]
  exact ⟨packet_support, matrix_hasInternalCrossedRows,
    not_exists_relabelledCyclicOpenSignSkeleton⟩

end FourPointCrossedRowsNoCyclicSign

end GameTheory
