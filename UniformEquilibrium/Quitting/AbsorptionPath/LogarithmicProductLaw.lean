/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.LogarithmicBlockDiscretization
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation
import UniformEquilibrium.Quitting.Root.HazardProfileBridge

/-!
# Product laws from logarithmic block hazards

This module is the finite probability-law part of logarithmic absorption-path
discretization.  The input is a nonnegative row of integrated hazards.  The
output is an actual product root whose coordinate hazards are
`1 - exp (-A i)`.  We prove its exact Continue mass, its exact singleton
atoms, and comparison with any singleton law lying between the standard
exponential lower bound and the integrated hazards.

No continuous path, derivative, or Snell identity is assumed here.
-/

noncomputable section

namespace GameTheory

open Math.PMFProduct Real
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Bernoulli hazard row obtained from integrated logarithmic hazards. -/
def logarithmicProductHazardRow
    (A : ι → ℝ) (hA : ∀ who, 0 ≤ A who) : QuittingHazardRow ι :=
  fun who => ⟨1 - exp (-A who), by
    constructor
    · rw [sub_nonneg, exp_le_one_iff]
      linarith [hA who]
    · linarith [exp_pos (-A who)]⟩

/-- The actual independent product root associated to integrated hazards. -/
def logarithmicProductRoot
    (A : ι → ℝ) (hA : ∀ who, 0 ≤ A who) : ι → PMF Bool :=
  quittingRootOfHazardRow (logarithmicProductHazardRow A hA)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem logarithmicProductRoot_true_toReal
    (A : ι → ℝ) (hA : ∀ who, 0 ≤ A who) (who : ι) :
    ((logarithmicProductRoot A hA who) true).toReal =
      1 - exp (-A who) := by
  simp [logarithmicProductRoot, logarithmicProductHazardRow]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem logarithmicProductRoot_false_toReal
    (A : ι → ℝ) (hA : ∀ who, 0 ≤ A who) (who : ι) :
    ((logarithmicProductRoot A hA who) false).toReal = exp (-A who) := by
  simp [logarithmicProductRoot, logarithmicProductHazardRow]

omit [DecidableEq ι] in
/-- The joint Continue mass of the logarithmic product root is exactly the
exponential of minus the total integrated hazard. -/
theorem quittingStationaryContinueMass_logarithmicProductRoot
    (A : ι → ℝ) (hA : ∀ who, 0 ≤ A who) :
    quittingStationaryContinueMass (logarithmicProductRoot A hA) =
      exp (-(∑ who, A who)) := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp only [logarithmicProductRoot_false_toReal]
  exact (exp_neg_sum_eq_prod_exp_neg A).symm

/-- The singleton atom of the logarithmic product root has the advertised
closed form. -/
theorem quittingRootCoalitionMass_singleton_logarithmicProductRoot
    (A : ι → ℝ) (hA : ∀ who, 0 ≤ A who) (owner : ι) :
    quittingRootCoalitionMass (logarithmicProductRoot A hA) {owner} =
      logarithmicBlockUniqueMass (A owner) (∑ who, A who) := by
  unfold quittingRootCoalitionMass logarithmicBlockUniqueMass
    quittingRootQuitRates coalitionMass
  simp only [Finset.prod_singleton, logarithmicProductRoot_true_toReal,
    sub_sub_cancel]
  have hexp : (∏ who ∈ ({owner} : Finset ι)ᶜ, exp (-A who)) =
      exp (-(∑ who ∈ ({owner} : Finset ι)ᶜ, A who)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib]
  rw [hexp]
  have hsum : ∑ who, A who = A owner + ∑ who ∈ ({owner} : Finset ι)ᶜ, A who := by
    rw [← Finset.sum_add_sum_compl ({owner} : Finset ι)]
    simp
  congr 1
  rw [hsum]
  ring_nf

/-- Exact opponent-deleted Continue mass. -/
theorem quittingFixedOpponentsContinueMass_logarithmicProductRoot
    (A : ι → ℝ) (hA : ∀ who, 0 ≤ A who) (who : ι) :
    quittingStationaryContinueMass
        (Function.update (logarithmicProductRoot A hA) who (PMF.pure false)) =
      exp (-(∑ other ∈ Finset.univ.erase who, A other)) := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ who)]
  simp only [Function.update_self, PMF.pure_apply, if_true,
    ENNReal.toReal_one, mul_one]
  have hproduct :
      (∏ other ∈ Finset.univ.erase who,
          ((Function.update (logarithmicProductRoot A hA) who
            (PMF.pure false) other) false).toReal) =
        ∏ other ∈ Finset.univ.erase who, exp (-A other) := by
    apply Finset.prod_congr rfl
    intro other hother
    have hne : other ≠ who := (Finset.mem_erase.mp hother).1
    simp [Function.update_of_ne hne, logarithmicProductRoot_false_toReal]
  rw [hproduct, ← Real.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib]

omit [Fintype ι] in
/-- Deleting one coordinate of a logarithmic product root is the same as
setting that coordinate's integrated hazard to zero before constructing the
root. -/
theorem update_logarithmicProductRoot_pure_false
    (A : ι → ℝ) (hA : ∀ who, 0 ≤ A who) (who : ι) :
    Function.update (logarithmicProductRoot A hA) who (PMF.pure false) =
      logarithmicProductRoot (Function.update A who 0) (fun other => by
        by_cases hother : other = who
        · subst other
          simp
        · simpa [Function.update_of_ne hother] using hA other) := by
  funext other
  apply PMF.ext
  intro action
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  by_cases hother : other = who
  · subst other
    cases action <;> simp [Function.update_self]
  · cases action <;>
      simp [Function.update_of_ne hother,
        logarithmicProductRoot_true_toReal,
        logarithmicProductRoot_false_toReal]

/-- The total hazard after deleting `who` is the sum over the erased
finite set. -/
theorem sum_update_zero_eq_sum_erase
    (A : ι → ℝ) (who : ι) :
    ∑ other, Function.update A who 0 other =
      ∑ other ∈ Finset.univ.erase who, A other := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ who)]
  simp [Finset.erase_eq]

omit [DecidableEq ι] in
/-- A bounded singleton observable changes by at most its bound times the
singleton `L1` discrepancy. -/
theorem abs_sum_singletonReward_sub_le
    (source target : ι → ℝ) (payoff : ι → ℝ) {M : ℝ}
    (hpayoff : ∀ owner, |payoff owner| ≤ M) :
    |(∑ owner, source owner * payoff owner) -
        ∑ owner, target owner * payoff owner| ≤
      M * ∑ owner, |source owner - target owner| := by
  rw [← Finset.sum_sub_distrib]
  have hrewrite :
      (∑ owner, (source owner * payoff owner - target owner * payoff owner)) =
        ∑ owner, (source owner - target owner) * payoff owner := by
    apply Finset.sum_congr rfl
    intro owner _
    ring
  rw [hrewrite]
  calc
    |∑ owner, (source owner - target owner) * payoff owner| ≤
        ∑ owner, |(source owner - target owner) * payoff owner| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ owner, M * |source owner - target owner| := by
      apply Finset.sum_le_sum
      intro owner _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hpayoff owner) (abs_nonneg _)
    _ = M * ∑ owner, |source owner - target owner| := by
      rw [Finset.mul_sum]

/-- One full product block is close to any continuum singleton block law
with the standard common lower and upper bounds.  Collision coalitions are
retained explicitly and paid by `h^2/2`. -/
theorem abs_logarithmicProductRootContribution_sub_singletonLaw_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (A source : ι → ℝ) {h M : ℝ}
    (hA : ∀ owner, 0 ≤ A owner)
    (hsum : ∑ owner, A owner = h)
    (hsourceLower : ∀ owner, exp (-h) * A owner ≤ source owner)
    (hsourceUpper : ∀ owner, source owner ≤ A owner)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (who : ι) :
    |quittingRootAbsorbingContribution reward
          (logarithmicProductRoot A hA) who -
        ∑ owner, source owner * reward (quittingSingletonTerminal owner) who| ≤
      M * (h * (1 - exp (-h)) + h ^ 2 / 2) := by
  let root := logarithmicProductRoot A hA
  let target : ι → ℝ := fun owner =>
    quittingRootCoalitionMass root {owner}
  have htargetBounds : ∀ owner,
      exp (-h) * A owner ≤ target owner ∧ target owner ≤ A owner := by
    intro owner
    dsimp only [target, root]
    rw [quittingRootCoalitionMass_singleton_logarithmicProductRoot, ← hsum]
    exact logarithmicBlockUniqueMass_bounds A hA
      (fun j => Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ j)) owner
  have hl1 : ∑ owner, |source owner - target owner| ≤
      h * (1 - exp (-h)) := by
    have h := sum_abs_sub_of_between_same_nonneg A source target
      (by simpa [hsum] using hsourceLower)
      hsourceUpper
      (fun owner => by simpa [hsum] using (htargetBounds owner).1)
      (fun owner => (htargetBounds owner).2)
    simpa [hsum] using h
  have hsingle := abs_sum_singletonReward_sub_le source target
    (fun owner => reward (quittingSingletonTerminal owner) who)
    (fun owner => hreward (quittingSingletonTerminal owner) who)
  have hcollision :=
    QuittingFiniteRootWindow.abs_rootCollisionRewardContribution_le
    reward root who hreward
  have hcollisionMass : quittingRootCollisionMass root ≤ h ^ 2 / 2 := by
    unfold quittingRootCollisionMass quittingRootQuitRates root
    simp only [logarithmicProductRoot_true_toReal]
    exact collisionMass_logarithmicBlock_le_sq A h hA hsum
  have hcollisionScaled :
      |QuittingFiniteRootWindow.rootCollisionRewardContribution
          reward root who| ≤ M * (h ^ 2 / 2) :=
    hcollision.trans (mul_le_mul_of_nonneg_left hcollisionMass
      (quittingRewardCoordinateBound_nonneg_of_player reward who hreward))
  rw [QuittingFiniteRootWindow.quittingRootAbsorbingContribution_eq_singleton_add_collision]
  change |(∑ owner, target owner * reward (quittingSingletonTerminal owner) who) +
      QuittingFiniteRootWindow.rootCollisionRewardContribution reward root who -
      ∑ owner, source owner * reward (quittingSingletonTerminal owner) who| ≤ _
  have hsingle' :
      |(∑ owner, target owner * reward (quittingSingletonTerminal owner) who) -
          ∑ owner, source owner * reward (quittingSingletonTerminal owner) who| ≤
        M * (h * (1 - exp (-h))) := by
    rw [abs_sub_comm]
    exact hsingle.trans (mul_le_mul_of_nonneg_left hl1
      (quittingRewardCoordinateBound_nonneg_of_player reward who hreward))
  calc
    |_ + _ - _| ≤
        |(∑ owner, target owner * reward (quittingSingletonTerminal owner) who) -
          ∑ owner, source owner * reward (quittingSingletonTerminal owner) who| +
          |QuittingFiniteRootWindow.rootCollisionRewardContribution reward root who| := by
      rw [show
        (∑ owner, target owner * reward (quittingSingletonTerminal owner) who) +
            QuittingFiniteRootWindow.rootCollisionRewardContribution reward root who -
            ∑ owner, source owner * reward (quittingSingletonTerminal owner) who =
          ((∑ owner, target owner * reward (quittingSingletonTerminal owner) who) -
            ∑ owner, source owner * reward (quittingSingletonTerminal owner) who) +
            QuittingFiniteRootWindow.rootCollisionRewardContribution reward root who by
        ring]
      exact abs_add_le _ _
    _ ≤ M * (h * (1 - exp (-h))) + M * (h ^ 2 / 2) :=
      add_le_add hsingle' hcollisionScaled
    _ = M * (h * (1 - exp (-h)) + h ^ 2 / 2) := by ring

/-- Opponent-only version of the one-block comparison.  The selected player
is forced to Continue in the actual product root; the supplied source law
has no atom at that player. -/
theorem abs_logarithmicProductOpponentContribution_sub_singletonLaw_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (A source : ι → ℝ) (who : ι) {H M : ℝ}
    (hA : ∀ owner, 0 ≤ A owner)
    (hsourceWho : source who = 0)
    (hsum : ∑ owner ∈ Finset.univ.erase who, A owner = H)
    (hsourceLower : ∀ owner, owner ≠ who →
      exp (-H) * A owner ≤ source owner)
    (hsourceUpper : ∀ owner, owner ≠ who → source owner ≤ A owner)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootAbsorbingContribution reward
          (Function.update (logarithmicProductRoot A hA) who (PMF.pure false)) who -
        ∑ owner, source owner * reward (quittingSingletonTerminal owner) who| ≤
      M * (H * (1 - exp (-H)) + H ^ 2 / 2) := by
  let deletedA := Function.update A who 0
  have hdeletedA : ∀ owner, 0 ≤ deletedA owner := by
    intro owner
    by_cases howner : owner = who
    · subst owner
      simp [deletedA]
    · simpa [deletedA, Function.update_of_ne howner] using hA owner
  have hdeletedSum : ∑ owner, deletedA owner = H := by
    simpa [deletedA, sum_update_zero_eq_sum_erase] using hsum
  have hsourceLower' : ∀ owner, exp (-H) * deletedA owner ≤ source owner := by
    intro owner
    by_cases howner : owner = who
    · subst owner
      simp [deletedA, hsourceWho]
    · simpa [deletedA, Function.update_of_ne howner] using
        hsourceLower owner howner
  have hsourceUpper' : ∀ owner, source owner ≤ deletedA owner := by
    intro owner
    by_cases howner : owner = who
    · subst owner
      simp [deletedA, hsourceWho]
    · simpa [deletedA, Function.update_of_ne howner] using
        hsourceUpper owner howner
  rw [update_logarithmicProductRoot_pure_false A hA who]
  exact abs_logarithmicProductRootContribution_sub_singletonLaw_le
    reward deletedA source hdeletedA hdeletedSum hsourceLower' hsourceUpper'
      hreward who

end GameTheory
