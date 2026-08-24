/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.SupportThreeFourSignGraph
import UniformEquilibrium.Quitting.Classification.LCP.CopositiveQBridge

/-!
# The full-support LCP screen does not force cyclic sign coherence

The existing full-support packet counterexample to cyclic open-sign coherence
already lies in the exact ambient matrix chamber forced by the unconditional
counterexample-facing LCP gate: its normalized singleton matrix is textbook
standard `Q` and has no homogeneous simplex solution.

Thus adding the standard-`Q`/nonhomogeneous screen to full packet support and
internal crossed rows does not recover a cyclic producer.  Further progress
has to use nonsingleton rewards or genuinely semantic source data.
-/

noncomputable section

namespace GameTheory

open Finset Math.LinearProgramming QuittingLCPClassification
open QuittingSureSetOwnerRepair

namespace FourPointCrossedRowsNoCyclicSign

/-- The quadratic form of the full-support sign barrier is a sum of three
nonnegative pair products on the nonnegative orthant. -/
theorem matrix_quadratic_eq (z : Player → Real) :
    (∑ i, z i * ∑ j, z j * matrix i j) =
      2 * (z 0 * z 3 + z 1 * z 2 + z 1 * z 3) := by
  simp [Fin.sum_univ_succ, matrix]
  ring

/-- The full-support sign barrier matrix is copositive. -/
theorem matrix_copositive : IsCopositive matrix := by
  intro z hz
  rw [matrix_quadratic_eq]
  have h03 : 0 ≤ z 0 * z 3 := mul_nonneg (hz 0) (hz 3)
  have h12 : 0 ≤ z 1 * z 2 := mul_nonneg (hz 1) (hz 2)
  have h13 : 0 ≤ z 1 * z 3 := mul_nonneg (hz 1) (hz 3)
  nlinarith

/-- The full-support sign barrier has no homogeneous simplex-LCP solution. -/
theorem matrix_noHomogeneous : ¬SingletonLCPFeasible matrix := by
  rintro ⟨lam, hres, hcomp⟩
  have h0 := lam.property.1 0
  have h1 := lam.property.1 1
  have h2 := lam.property.1 2
  have h3 := lam.property.1 3
  have hsum := lam.property.2
  have hr0 := hres 0
  have hr1 := hres 1
  have hr2 := hres 2
  have hr3 := hres 3
  have hc0 := hcomp 0
  have hc1 := hcomp 1
  have hc2 := hcomp 2
  have hc3 := hcomp 3
  simp [singletonLCPResidual, wsum, dotProduct, Fin.sum_univ_succ,
    matrix] at hr0 hr1 hr2 hr3 hc0 hc1 hc2 hc3 hsum
  let a : Real := lam.val 0
  let b : Real := lam.val 1
  let c : Real := lam.val 2
  let d : Real := lam.val 3
  change 0 ≤ a at h0
  change 0 ≤ b at h1
  change 0 ≤ c at h2
  change 0 ≤ d at h3
  change b ≤ c + d at hr0
  change 0 ≤ a + (-c + d) at hr1
  change a + d ≤ b * 3 at hr2
  change a = 0 ∨ -b + (c + d) = 0 at hc0
  change b = 0 ∨ a + (-c + d) = 0 at hc1
  change c = 0 ∨ -a + (b * 3 + -d) = 0 at hc2
  change d = 0 ∨ a + (b + c) = 0 at hc3
  change a + (b + (c + d)) = 1 at hsum
  have hd : d = 0 := by
    by_contra hne
    have hpos : 0 < d := lt_of_le_of_ne h3 (Ne.symm hne)
    have hzero : a + b + c = 0 := by
      have := hc3.resolve_left hne
      linarith
    have hz0 : a = 0 := by nlinarith
    have hz1 : b = 0 := by nlinarith
    have hz2 : c = 0 := by nlinarith
    nlinarith [hr2, hsum]
  have hb : 0 < b := by
    by_contra hnot
    have hb0 : b = 0 := le_antisymm (le_of_not_gt hnot) h1
    have ha0 : a = 0 := by nlinarith [hr2]
    have hc0' : c = 0 := by nlinarith [hr1]
    nlinarith [hsum]
  have hac : a = c := by
    have heq := hc1.resolve_left hb.ne'
    nlinarith [heq, hd]
  have ha : 0 < a := by
    nlinarith [hr0, hd, hac]
  have hcb : c = b := by
    have heq := hc0.resolve_left ha.ne'
    nlinarith [heq, hd]
  have ha3b : a = 3 * b := by
    have hc : 0 < c := by nlinarith [hac]
    have heq := hc2.resolve_left hc.ne'
    nlinarith [heq, hd]
  nlinarith

/-- The full-support sign barrier is textbook standard `Q`. -/
theorem matrix_standardQ : IsStandardQMatrix matrix := by
  apply isStandardQMatrix_of_copositive_of_isR0Matrix matrix matrix_copositive
  exact (isR0Matrix_iff_not_singletonLCPFeasible matrix).2 matrix_noHomogeneous


/-! ## Strengthening the barrier into the full recursive normal core -/

/-- Change only the last row of the earlier sign barrier, giving it a
distinct negative blocker while preserving positive uniform row averages. -/
def fullCoreMatrix : Player → Player → Real := fun who owner ↦
  if who = 3 then ![-1, 1, 1, 0] owner else matrix who owner

theorem fullCoreMatrix_diagonal (who : Player) : fullCoreMatrix who who = 0 := by
  fin_cases who <;> simp +decide [fullCoreMatrix, matrix]

theorem fullCoreMatrix_hasInternalCrossedRows :
    HasInternalCrossedRows fullCoreMatrix := by
  intro owner
  fin_cases owner
  · exact ⟨2, 1, by decide, by decide, by decide,
      by simp +decide [fullCoreMatrix, matrix],
      by simp +decide [fullCoreMatrix, matrix]⟩
  · exact ⟨0, 2, by decide, by decide, by decide,
      by simp +decide [fullCoreMatrix, matrix],
      by simp +decide [fullCoreMatrix, matrix]⟩
  · exact ⟨1, 0, by decide, by decide, by decide,
      by simp +decide [fullCoreMatrix, matrix],
      by simp +decide [fullCoreMatrix, matrix]⟩
  · exact ⟨2, 1, by decide, by decide, by decide,
      by simp +decide [fullCoreMatrix, matrix],
      by simp +decide [fullCoreMatrix, matrix]⟩

/-- Row `2` still has two negative entries, so relabeling cannot produce a
cyclic open-sign skeleton. -/
theorem fullCoreMatrix_not_exists_relabelledCyclicOpenSignSkeleton :
    ¬∃ label : Player ≃ Player,
      Nonempty (CyclicOpenSignSkeleton
        (reindexMatrix label fullCoreMatrix)) := by
  rintro ⟨label, ⟨skeleton⟩⟩
  have hfirst : reindexMatrix label fullCoreMatrix (label 2) (label 0) < 0 := by
    simp [reindexMatrix, fullCoreMatrix, matrix]
  have hsecond : reindexMatrix label fullCoreMatrix (label 2) (label 3) < 0 := by
    simp [reindexMatrix, fullCoreMatrix, matrix]
  have heq := skeleton.negative_unique hfirst hsecond
  exact (by decide : (0 : Player) ≠ 3) (label.injective heq)

theorem fullCoreMatrix_quadratic_eq (z : Player → Real) :
    (∑ i, z i * ∑ j, z j * fullCoreMatrix i j) =
      2 * (z 1 * z 2 + z 1 * z 3) := by
  simp [Fin.sum_univ_succ, fullCoreMatrix, matrix]
  ring

theorem fullCoreMatrix_copositive : IsCopositive fullCoreMatrix := by
  intro z hz
  rw [fullCoreMatrix_quadratic_eq]
  have h12 : 0 ≤ z 1 * z 2 := mul_nonneg (hz 1) (hz 2)
  have h13 : 0 ≤ z 1 * z 3 := mul_nonneg (hz 1) (hz 3)
  nlinarith

theorem fullCoreMatrix_noHomogeneous :
    ¬SingletonLCPFeasible fullCoreMatrix := by
  rintro ⟨lam, hres, hcomp⟩
  have h0 := lam.property.1 0
  have h1 := lam.property.1 1
  have h2 := lam.property.1 2
  have h3 := lam.property.1 3
  have hsum := lam.property.2
  have hr0 := hres 0
  have hr1 := hres 1
  have hr2 := hres 2
  have henergy :
      (∑ i, lam.val i * singletonLCPResidual fullCoreMatrix lam i) = 0 := by
    exact Finset.sum_eq_zero fun i _ => hcomp i
  have henergy' :
      2 * (lam.val 1 * lam.val 2 + lam.val 1 * lam.val 3) = 0 := by
    rw [← fullCoreMatrix_quadratic_eq lam.val]
    exact henergy
  simp [singletonLCPResidual, wsum, dotProduct, Fin.sum_univ_succ,
    fullCoreMatrix, matrix] at hr0 hr1 hr2 hsum
  let a : Real := lam.val 0
  let b : Real := lam.val 1
  let c : Real := lam.val 2
  let d : Real := lam.val 3
  change 0 ≤ a at h0
  change 0 ≤ b at h1
  change 0 ≤ c at h2
  change 0 ≤ d at h3
  change b ≤ c + d at hr0
  change 0 ≤ a + (-c + d) at hr1
  change a + d ≤ b * 3 at hr2
  change 2 * (b * c + b * d) = 0 at henergy'
  change a + (b + (c + d)) = 1 at hsum
  by_cases hb : b = 0
  · have ha : a = 0 := by nlinarith [hr2]
    have hd : d = 0 := by nlinarith [hr2]
    have hc : c = 0 := by nlinarith [hr1]
    nlinarith
  · have hbpos : 0 < b := lt_of_le_of_ne h1 (Ne.symm hb)
    have hc : c = 0 := by nlinarith [henergy']
    have hd : d = 0 := by nlinarith [henergy']
    nlinarith [hr0]

theorem fullCoreMatrix_standardQ : IsStandardQMatrix fullCoreMatrix := by
  apply isStandardQMatrix_of_copositive_of_isR0Matrix
    fullCoreMatrix fullCoreMatrix_copositive
  exact (isR0Matrix_iff_not_singletonLCPFeasible fullCoreMatrix).2
    fullCoreMatrix_noHomogeneous

theorem fullCoreMatrix_exists_distinct_nonpos (who : Player) :
    ∃ owner, owner ≠ who ∧ fullCoreMatrix who owner ≤ 0 := by
  fin_cases who
  · exact ⟨1, by decide, by simp +decide [fullCoreMatrix, matrix]⟩
  · exact ⟨2, by decide, by simp +decide [fullCoreMatrix, matrix]⟩
  · exact ⟨0, by decide, by simp +decide [fullCoreMatrix, matrix]⟩
  · exact ⟨0, by decide, by simp +decide [fullCoreMatrix]⟩

private theorem fullCoreMatrix_mem_normalLayer_all :
    ∀ time who, who ∈ normalLayer fullCoreMatrix time := by
  intro time
  induction time with
  | zero => simp
  | succ time ih =>
      intro who
      apply (mem_normalLayer_succ fullCoreMatrix time who).2
      obtain ⟨owner, hne, hentry⟩ :=
        fullCoreMatrix_exists_distinct_nonpos who
      exact ⟨ih who, owner, ih owner, hne, hentry⟩

theorem fullCoreMatrix_normalLayer_eq_univ (time : Nat) :
    normalLayer fullCoreMatrix time = Finset.univ := by
  exact Finset.eq_univ_of_forall (fullCoreMatrix_mem_normalLayer_all time)

theorem fullCoreMatrix_normalCore_eq_univ :
    normalCore fullCoreMatrix = Finset.univ := by
  ext who
  simp [normalCore, fullCoreMatrix_normalLayer_eq_univ]

/-- Realize the full-core barrier as literal singleton rewards. -/
def fullCoreReward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who => fullCoreMatrix who (Classical.choose terminal.2)

private theorem fullCoreReward_singleton (owner who : Player) :
    fullCoreReward (quittingSingletonTerminal owner) who =
      fullCoreMatrix who owner := by
  unfold fullCoreReward quittingSingletonTerminal
  congr 1
  have hmem := Classical.choose_spec (Finset.singleton_nonempty owner)
  simpa using hmem

private theorem fullCoreSingletonMixture_nonneg (who : Player) :
    0 ≤ quittingSingletonMixture fullCoreReward mass who := by
  unfold quittingSingletonMixture
  simp_rw [fullCoreReward_singleton]
  fin_cases who
  · norm_num [Fin.sum_univ_succ, mass, fullCoreMatrix, matrix]
  · norm_num [Fin.sum_univ_succ, mass, fullCoreMatrix, matrix]
  · simp +decide [Fin.sum_univ_succ, mass, fullCoreMatrix, matrix]
    norm_num
  · simp +decide [Fin.sum_univ_succ, mass, fullCoreMatrix]

private theorem fullCoreMass_sum : ∑ owner, mass owner = 1 := by
  simp [mass]

def fullCorePacket : QuittingNormalizedSingletonSourcePacket fullCoreReward where
  mass := mass
  target := fun _ => 0
  mass_nonneg := fun _ => by norm_num [mass]
  mass_sum := fullCoreMass_sum
  mix_ge_target := fullCoreSingletonMixture_nonneg
  solo_le_target := fun who => by
    rw [fullCoreReward_singleton, fullCoreMatrix_diagonal]
  punishment_le_target := fun who => by
    calc
      quittingPunishmentValue fullCoreReward who ≤
          max (quittingSetReward fullCoreReward {who} who) 0 :=
        quittingPunishmentValue_le_max_solo fullCoreReward who
      _ = 0 := by
        rw [quittingSetReward_singleton_eq_soloReward]
        change max (fullCoreReward (quittingSingletonTerminal who) who) 0 = 0
        rw [fullCoreReward_singleton, fullCoreMatrix_diagonal]
        simp
  positive_mass_pins_target := fun owner _ => by
    rw [fullCoreReward_singleton, fullCoreMatrix_diagonal]

theorem fullCorePacket_support : fullCorePacket.support = Finset.univ := by
  ext owner
  simp [QuittingNormalizedSingletonSourcePacket.support, fullCorePacket, mass]

theorem normalizedSoloMatrix_fullCoreReward :
    normalizedSoloMatrix fullCoreReward = fullCoreMatrix := by
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  funext who owner
  simp only [quittingProjectiveLCPMatrix]
  rw [show fullCoreReward (quittingProjectiveSingletonTerminal owner) who =
      fullCoreMatrix who owner by exact fullCoreReward_singleton owner who,
    show fullCoreReward (quittingProjectiveSingletonTerminal who) who =
      fullCoreMatrix who who by exact fullCoreReward_singleton who who,
    fullCoreMatrix_diagonal, sub_zero]

/-- **Sharp full-support LCP/sign barrier.**  An actual normalized singleton
source packet can simultaneously have full support, internal crossed rows,
the exact standard-`Q`/nonhomogeneous ambient matrix screen, and no cyclic
open-sign skeleton under any relabeling. -/
theorem fullSupportPacket_standardQ_nonhomogeneous_but_not_cyclic :
    fullCorePacket.support = Finset.univ ∧
      HasInternalCrossedRows (normalizedSoloMatrix fullCoreReward) ∧
      normalCore (normalizedSoloMatrix fullCoreReward) = Finset.univ ∧
      IsStandardQMatrix (normalizedSoloMatrix fullCoreReward) ∧
      ¬HasHomogeneousSimplexSolution
        (normalizedSoloMatrix fullCoreReward) ∧
      ¬∃ label : Player ≃ Player,
        Nonempty (CyclicOpenSignSkeleton
          (reindexMatrix label
            (normalizedSoloMatrix fullCoreReward))) := by
  rw [normalizedSoloMatrix_fullCoreReward]
  exact ⟨fullCorePacket_support, fullCoreMatrix_hasInternalCrossedRows,
    fullCoreMatrix_normalCore_eq_univ, fullCoreMatrix_standardQ,
    fullCoreMatrix_noHomogeneous,
    fullCoreMatrix_not_exists_relabelledCyclicOpenSignSkeleton⟩

end FourPointCrossedRowsNoCyclicSign

end GameTheory
