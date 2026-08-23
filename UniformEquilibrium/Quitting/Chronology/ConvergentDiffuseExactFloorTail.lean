/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearAlgebra.FiniteConvexStrictSeparation
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanQuitEndpointLimit
import UniformEquilibrium.Quitting.Chronology.SummableExactTailTerminalGap
import UniformEquilibrium.Quitting.Chronology.StrictCovectorRootStep
import UniformEquilibrium.Quitting.Classification.LCP.HomogeneousProductionNormalDispatch

/-!
# Convergent diffuse exact quitting tails

This module isolates a source-independent late-tail obstruction.  The input is
only a convergent sequence of literal product roots and values, exact
Nash--Bellman evaluation, the punishment floor, and a diffuse but recurrent
absorption clock.  No summability or homogeneous witness is supplied.

Late active owners must lie on one boundary-tight singleton face.  Unless a
homogeneous witness on that face already solves the game, strict finite
separation supplies one covector which pays a fixed fraction of every late
absorption charge.  Telescoping then proves summability and positive suffix
survival.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Primitive data for a convergent diffuse exact tail above the behavioral
punishment floor.  In particular, summability is not an input. -/
structure QuittingConvergentDiffuseExactFloorTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  boundary : Payoff ι
  bellman : ∀ time,
    value time = quittingRootSuccessorPayoff reward (value (time + 1)) (roots time)
  endpointNash : ∀ time,
    IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time)
  value_tendsto : ∀ who,
    Tendsto (fun time ↦ value time who) atTop (nhds (boundary who))
  solo_le_boundary : ∀ who,
    reward (quittingSingletonTerminal who) who ≤ boundary who
  absorption_tendsto_zero : Tendsto
    (fun time ↦ quittingRootAbsorptionMass (roots time)) atTop (nhds 0)
  arbitrarilyLate_positiveAbsorption : ∀ cutoff, ∃ time, cutoff ≤ time ∧
    0 < quittingRootAbsorptionMass (roots time)
  punishmentFloor : ∀ time who,
    quittingPunishmentValue reward who ≤ value time who

namespace QuittingConvergentDiffuseExactFloorTail

variable (tail : QuittingConvergentDiffuseExactFloorTail reward)

/-- The finite set of owners whose boundary value equals their singleton
self-payoff. -/
def tightOwnerFinset : Finset ι := by
  classical
  exact Finset.univ.filter fun owner ↦
    tail.boundary owner = reward (quittingSingletonTerminal owner) owner

/-- Owners tight at the limiting boundary. -/
abbrev TightOwner := {owner : ι // owner ∈ tail.tightOwnerFinset}

omit [Nonempty ι] in
/-- The punishment floor passes to the limiting boundary. -/
theorem punishmentValue_le_boundary (who : ι) :
    quittingPunishmentValue reward who ≤ tail.boundary who := by
  apply ge_of_tendsto (tail.value_tendsto who)
  exact Eventually.of_forall fun time ↦ tail.punishmentFloor time who

omit [Nonempty ι] in
/-- Every tight boundary owner is punishment-normal. -/
theorem tightOwner_punishmentValue_le_singleton (owner : tail.TightOwner) :
    quittingPunishmentValue reward owner.1 ≤
      reward (quittingSingletonTerminal owner.1) owner.1 := by
  have htight : tail.boundary owner.1 =
      reward (quittingSingletonTerminal owner.1) owner.1 := by
    exact (Finset.mem_filter.1 owner.property).2
  exact (tail.punishmentValue_le_boundary owner.1).trans_eq htight

omit [Nonempty ι] in
/-- Convergence of the finitely many value coordinates gives one global
absolute bound. -/
theorem exists_valueBound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ time who, |tail.value time who| ≤ M := by
  have hbounded : ∀ who, Bornology.IsBounded
      (Set.range fun time ↦ tail.value time who) := fun who ↦
    Metric.isBounded_range_of_tendsto _ (tail.value_tendsto who)
  choose radius hradius using fun who ↦ (hbounded who).subset_closedBall 0
  let M := ∑ who, max 0 (radius who)
  refine ⟨M, Finset.sum_nonneg fun _ _ ↦ le_max_left _ _, ?_⟩
  intro time who
  have hmem := hradius who ⟨time, rfl⟩
  have habs : |tail.value time who| ≤ radius who := by
    simpa [Real.dist_eq] using hmem
  calc
    |tail.value time who| ≤ max 0 (radius who) := habs.trans (le_max_right _ _)
    _ ≤ M := Finset.single_le_sum
      (fun owner _ ↦ le_max_left (0 : ℝ) (radius owner)) (Finset.mem_univ who)

omit [Nonempty ι] in
/-- Exact endpoint indifference identifies the current value with the
pure-Quit endpoint whenever the owner has positive Quit probability. -/
theorem value_eq_quitPayoff_of_quit_pos (who : ι) (time : ℕ)
    (hquit : 0 < (tail.roots time who true).toReal) :
    tail.value time who = quittingRootQuitPayoff reward
      (tail.value (time + 1)) (tail.roots time) who := by
  symm
  calc
    quittingRootQuitPayoff reward (tail.value (time + 1))
        (tail.roots time) who =
        quittingRootSuccessorPayoff reward (tail.value (time + 1))
          (tail.roots time) who :=
      quittingRootQuitPayoff_eq_successor_of_quitProbability_pos
        reward (tail.value (time + 1)) (tail.roots time) who
          ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
            reward (tail.value (time + 1)) (tail.roots time)).1
              (tail.endpointNash time)) hquit
    _ = tail.value time who := (congrFun (tail.bellman time) who).symm

omit [Nonempty ι] in
/-- An active owner's displayed value is close to its singleton self-payoff,
with error controlled only by opponent absorption. -/
theorem abs_value_sub_singleton_le_of_quit_pos (who : ι) (time : ℕ)
    (hquit : 0 < (tail.roots time who true).toReal) :
    |tail.value time who - reward (quittingSingletonTerminal who) who| ≤
      2 * quittingRewardBound reward *
        quittingRootOpponentAbsorptionMass (tail.roots time) who := by
  rw [tail.value_eq_quitPayoff_of_quit_pos who time hquit]
  exact
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (tail.value (time + 1)) (tail.roots time) who
        (quittingRewardBound reward) (abs_reward_le_quittingRewardBound reward)

omit [Nonempty ι] in
/-- After one cutoff, every physically active owner lies on the boundary-tight
face.  This uses diffuseness, not summability. -/
theorem eventually_active_mem_tightOwnerFinset :
    ∀ᶠ time : ℕ in atTop, ∀ owner,
      tail.roots time owner ≠ PMF.pure false → owner ∈ tail.tightOwnerFinset := by
  have hcoordinate : ∀ owner, ∀ᶠ time : ℕ in atTop,
      tail.roots time owner ≠ PMF.pure false →
        tail.boundary owner = reward (quittingSingletonTerminal owner) owner := by
    intro owner
    by_cases htight : tail.boundary owner =
        reward (quittingSingletonTerminal owner) owner
    · exact Eventually.of_forall fun _ _ ↦ htight
    · let gap := |tail.boundary owner -
        reward (quittingSingletonTerminal owner) owner|
      have hgap : 0 < gap := abs_pos.mpr (sub_ne_zero.mpr htight)
      have hvalue : ∀ᶠ time : ℕ in atTop,
          |tail.value time owner - tail.boundary owner| < gap / 3 := by
        have htends := (tail.value_tendsto owner).sub_const (tail.boundary owner)
        have habs : Tendsto (fun time ↦
            |tail.value time owner - tail.boundary owner|) atTop (nhds 0) := by
          simpa only [sub_self, abs_zero] using htends.abs
        exact (tendsto_order.1 habs).2 (gap / 3) (by linarith)
      have habsorption : ∀ᶠ time : ℕ in atTop,
          2 * quittingRewardBound reward *
              quittingRootAbsorptionMass (tail.roots time) < gap / 3 := by
        have htends := tail.absorption_tendsto_zero.const_mul
          (2 * quittingRewardBound reward)
        exact (tendsto_order.1 htends).2 (gap / 3) (by linarith)
      filter_upwards [hvalue, habsorption] with time hvalueTime habsTime hactive
      have hquit : 0 < (tail.roots time owner true).toReal := by
        have hne : (tail.roots time owner true).toReal ≠ 0 := by
          intro hzero
          apply hactive
          exact Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
            (tail.roots time owner) hzero
        exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
      have hendpoint := tail.abs_value_sub_singleton_le_of_quit_pos owner time hquit
      have hopponent := quittingRootOpponentAbsorptionMass_le_absorptionMass
        (tail.roots time) owner
      have hrewardNonneg : 0 ≤ 2 * quittingRewardBound reward := by
        exact mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)
      have hendpoint' : |tail.value time owner -
          reward (quittingSingletonTerminal owner) owner| < gap / 3 := by
        exact (hendpoint.trans <|
          mul_le_mul_of_nonneg_left hopponent hrewardNonneg).trans_lt habsTime
      have htriangle := abs_sub_le
        (tail.boundary owner) (tail.value time owner)
        (reward (quittingSingletonTerminal owner) owner)
      dsimp only [gap] at hgap hvalueTime hendpoint' htriangle
      rw [abs_sub_comm (tail.boundary owner) (tail.value time owner)] at htriangle
      linarith
  filter_upwards [(eventually_all_finite Set.finite_univ).2
    (fun owner _ ↦ hcoordinate owner)] with time htime owner howner
  simpa [tightOwnerFinset] using htime owner (Set.mem_univ owner) howner

/-- Extend a weight on boundary-tight owners by zero. -/
def extendTightWeight (weight : tail.TightOwner → ℝ) : ι → ℝ := fun owner ↦
  if h : tail.boundary owner =
      reward (quittingSingletonTerminal owner) owner then
    weight ⟨owner, by simpa [tightOwnerFinset] using h⟩ else 0

omit [Nonempty ι] in
@[simp] theorem extendTightWeight_apply
    (weight : tail.TightOwner → ℝ) (owner : tail.TightOwner) :
    tail.extendTightWeight weight owner.1 = weight owner := by
  unfold extendTightWeight
  have htight : tail.boundary owner.1 =
      reward (quittingSingletonTerminal owner.1) owner.1 :=
    (Finset.mem_filter.1 owner.property).2
  rw [dif_pos htight]

/-- Zero extension of a tight-owner simplex remains an ambient simplex. -/
def extendTightSimplex (weight : stdSimplex ℝ tail.TightOwner) :
    stdSimplex ℝ ι := by
  classical
  refine ⟨tail.extendTightWeight weight.val, ?_, ?_⟩
  · intro owner
    by_cases htight : tail.boundary owner =
        reward (quittingSingletonTerminal owner) owner
    · have hmem : owner ∈ tail.tightOwnerFinset := by
        simpa [tightOwnerFinset] using htight
      simpa [extendTightWeight, htight] using weight.property.1 ⟨owner, hmem⟩
    · simp [extendTightWeight, htight]
  · calc
      (∑ owner, tail.extendTightWeight weight.val owner) =
          ∑ owner ∈ tail.tightOwnerFinset,
            tail.extendTightWeight weight.val owner := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro owner _ howner
        have hnotTight : ¬tail.boundary owner =
            reward (quittingSingletonTerminal owner) owner := by
          simpa [tightOwnerFinset] using howner
        simp [extendTightWeight, hnotTight]
      _ = ∑ owner : tail.TightOwner,
          tail.extendTightWeight weight.val owner.1 := by
        exact Finset.sum_subtype tail.tightOwnerFinset
          (fun _ ↦ Iff.rfl) (tail.extendTightWeight weight.val : ι → ℝ)
      _ = ∑ owner : tail.TightOwner, weight.val owner := by
        apply Finset.sum_congr rfl
        intro owner _
        exact tail.extendTightWeight_apply weight.val owner
      _ = 1 := weight.property.2

omit [Nonempty ι] in
/-- Zero extension preserves weighted finite sums. -/
theorem sum_extendTightWeight_mul
    (weight : tail.TightOwner → ℝ) (f : ι → ℝ) :
    (∑ owner, tail.extendTightWeight weight owner * f owner) =
      ∑ owner : tail.TightOwner, weight owner * f owner.1 := by
  calc
    (∑ owner, tail.extendTightWeight weight owner * f owner) =
        ∑ owner ∈ tail.tightOwnerFinset,
          tail.extendTightWeight weight owner * f owner := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro owner _ howner
      have hnotTight : ¬tail.boundary owner =
          reward (quittingSingletonTerminal owner) owner := by
        simpa [tightOwnerFinset] using howner
      simp [extendTightWeight, hnotTight]
    _ = ∑ owner : tail.TightOwner,
        tail.extendTightWeight weight owner.1 * f owner.1 := by
      exact Finset.sum_subtype tail.tightOwnerFinset (fun _ ↦ Iff.rfl) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro owner _
      rw [tail.extendTightWeight_apply]

omit [Nonempty ι] in
/-- Unless the game is already solved, all boundary-tight singleton drift
columns have one strict separator. -/
theorem exists_strictCovector_on_tightOwners_of_no_uniformPayoff
    (hnoUE : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ covector : Payoff ι, ∃ margin : ℝ,
      0 < margin ∧
      (∑ who, covector who ^ 2) + margin ^ 2 = 1 ∧
      ∀ owner : tail.TightOwner,
        margin ≤ quittingCovectorPairing covector (fun who ↦
          tail.boundary who -
            reward (quittingSingletonTerminal owner.1) who) := by
  let column : tail.TightOwner → ι → ℝ := fun owner who ↦
    tail.boundary who - reward (quittingSingletonTerminal owner.1) who
  have hnot : ¬ ∃ weight : tail.TightOwner → ℝ,
      (∀ owner, 0 ≤ weight owner) ∧ (∑ owner, weight owner) = 1 ∧
      ∀ who, (∑ owner, weight owner * column owner who) = 0 := by
    rintro ⟨weight, hweight, hmass, hzero⟩
    let tightSimplex : stdSimplex ℝ tail.TightOwner := ⟨weight, hweight, hmass⟩
    let ambient := tail.extendTightSimplex tightSimplex
    have hbary : ∀ who, (∑ owner, ambient.val owner *
        reward (quittingSingletonTerminal owner) who) = tail.boundary who := by
      intro who
      change (∑ owner, tail.extendTightWeight weight owner *
        reward (quittingSingletonTerminal owner) who) = _
      rw [tail.sum_extendTightWeight_mul]
      have hz := hzero who
      unfold column at hz
      simp_rw [mul_sub] at hz
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul] at hz
      linarith
    apply hnoUE
    apply exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal
      reward ambient
    · intro who
      rw [singletonLCPResidual_normalizedSoloMatrix_eq_singletonBarycenter]
      change 0 ≤ (∑ owner, ambient.val owner *
        reward (quittingSingletonTerminal owner) who) - _
      rw [hbary who]
      exact sub_nonneg.mpr (tail.solo_le_boundary who)
    · intro who
      by_cases htight : tail.boundary who =
          reward (quittingSingletonTerminal who) who
      · rw [singletonLCPResidual_normalizedSoloMatrix_eq_singletonBarycenter]
        change ambient.val who * ((∑ owner, ambient.val owner *
          reward (quittingSingletonTerminal owner) who) - _) = 0
        rw [hbary who, htight, sub_self, mul_zero]
      · have hambient : ambient.val who = 0 := by
          simp [ambient, extendTightSimplex, extendTightWeight, htight]
        rw [hambient, zero_mul]
    · intro owner howner
      have htight : tail.boundary owner =
          reward (quittingSingletonTerminal owner) owner := by
        by_contra hnotTight
        have : ambient.val owner = 0 := by
          simp [ambient, extendTightSimplex, extendTightWeight, hnotTight]
        linarith
      exact tail.punishmentValue_le_boundary owner |>.trans_eq htight
  simpa only [column, quittingCovectorPairing] using
    Math.LinearAlgebra.exists_euclideanUnit_strictConvexSeparator_fintype
      column hnot

omit [Nonempty ι] in
/-- Arbitrarily late positive absorption makes the boundary-tight face
nonempty. -/
theorem tightOwner_nonempty : Nonempty tail.TightOwner := by
  obtain ⟨supportCutoff, hsupport⟩ :=
    Filter.eventually_atTop.1 tail.eventually_active_mem_tightOwnerFinset
  obtain ⟨time, htime, habsorption⟩ :=
    tail.arbitrarilyLate_positiveAbsorption supportCutoff
  obtain ⟨owner, howner⟩ :=
    exists_quitProbability_pos_of_absorptionMass_pos (tail.roots time) habsorption
  have hnotPure : tail.roots time owner ≠ PMF.pure false := by
    intro hpure
    rw [hpure] at howner
    simp at howner
  exact ⟨⟨owner, hsupport time htime owner hnotPure⟩⟩

omit [Nonempty ι] [DecidableEq ι] in
private theorem quitProbability_le_absorptionMass
    (root : ι → PMF Bool) (who : ι) :
    (root who true).toReal ≤ quittingRootAbsorptionMass root := by
  have hcontinue :=
    quittingStationaryContinueMass_le_ownContinueProbability root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  unfold quittingRootAbsorptionMass
  linarith

omit [Nonempty ι] in
/-- On the no-uniform-payoff branch, one covector pays a fixed fraction of
every sufficiently late absorption charge. -/
theorem exists_eventual_strictCovectorCharge_of_no_uniformPayoff
    (hnoUE : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ covector : Payoff ι, ∃ margin : ℝ, ∃ cutoff : ℕ,
      0 < margin ∧
      (∑ who, covector who ^ 2) + margin ^ 2 = 1 ∧
      ∀ time, cutoff ≤ time →
        margin / 2 * quittingRootAbsorptionMass (tail.roots time) ≤
          quittingCovectorPairing covector
            (tail.value (time + 1) - tail.value time) := by
  obtain ⟨covector, margin, hmarginPos, hunit, hcolumns⟩ :=
    tail.exists_strictCovector_on_tightOwners_of_no_uniformPayoff hnoUE
  obtain ⟨valueBound, _hvalueBoundNonneg, hvalueBound⟩ := tail.exists_valueBound
  let M := max (quittingRewardBound reward) valueBound
  let total : ℕ → ℝ := fun time ↦
    ∑ owner, quittingRootQuitRates (tail.roots time) owner
  let closeness : ℕ → ℝ := fun time ↦
    ∑ who, |tail.value (time + 1) who - tail.boundary who|
  have hquitTendsto : ∀ owner, Tendsto
      (fun time ↦ quittingRootQuitRates (tail.roots time) owner)
      atTop (nhds 0) := by
    intro owner
    apply squeeze_zero
    · exact fun _ ↦ ENNReal.toReal_nonneg
    · exact fun time ↦
        quitProbability_le_absorptionMass (tail.roots time) owner
    · exact tail.absorption_tendsto_zero
  have htotal : Tendsto total atTop (nhds 0) := by
    unfold total
    simpa using tendsto_finsetSum Finset.univ fun who _ ↦ hquitTendsto who
  have hclose : Tendsto closeness atTop (nhds 0) := by
    unfold closeness
    convert tendsto_finsetSum Finset.univ (fun who _ ↦ by
      have hshift := (tail.value_tendsto who).comp (tendsto_add_atTop_nat 1)
      have hsub := hshift.sub_const (tail.boundary who)
      simpa only [sub_self, abs_zero] using hsub.abs) using 1 <;>
        simp
  have hsmall : ∀ᶠ time in atTop,
      (∑ who, |covector who|) *
        (closeness time + 2 * M * total time) ≤ margin / 2 := by
    have htends : Tendsto (fun time ↦
        (∑ who, |covector who|) *
          (closeness time + 2 * M * total time)) atTop (nhds 0) := by
      simpa only [mul_zero, add_zero] using
        (hclose.add (htotal.const_mul (2 * M))).const_mul
          (∑ who, |covector who|)
    filter_upwards [(tendsto_order.1 htends).2 (margin / 2) (by linarith)]
      with time htime
    exact htime.le
  obtain ⟨supportCutoff, hsupport⟩ :=
    Filter.eventually_atTop.1 tail.eventually_active_mem_tightOwnerFinset
  obtain ⟨smallCutoff, hsmallCutoff⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨covector, margin, max supportCutoff smallCutoff,
    hmarginPos, hunit, ?_⟩
  intro time htime
  have hsupportTime := hsupport time ((le_max_left _ _).trans htime)
  have hsmallTime := hsmallCutoff time ((le_max_right _ _).trans htime)
  let root := tail.roots time
  have htotalNonneg : 0 ≤ total time :=
    Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
  by_cases htotalZero : total time = 0
  · have habs : quittingRootAbsorptionMass root = 0 := by
      apply le_antisymm
      · exact (quittingRootAbsorptionMass_le_sum_quitRates root).trans_eq
          htotalZero
      · exact quittingRootAbsorptionMass_nonneg root
    have hroot : root = fun _ ↦ PMF.pure false := by
      funext owner
      apply Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      have hle : quittingRootQuitRates root owner ≤
          ∑ who, quittingRootQuitRates root who :=
        Finset.single_le_sum
          (fun who _ ↦ (ENNReal.toReal_nonneg :
            0 ≤ quittingRootQuitRates root who)) (Finset.mem_univ owner)
      change quittingRootQuitRates root owner ≤ total time at hle
      exact le_antisymm (hle.trans_eq htotalZero) ENNReal.toReal_nonneg
    rw [habs, mul_zero]
    have hbellman := tail.bellman time
    have hroot' : root = quittingAllContinueRoot := by
      funext owner
      simpa [quittingAllContinueRoot] using congrFun hroot owner
    change tail.value time =
      quittingRootSuccessorPayoff reward (tail.value (time + 1)) root at hbellman
    rw [hroot', quittingRootSuccessorPayoff_allContinueRoot_eq] at hbellman
    rw [hbellman]
    simp [quittingCovectorPairing]
  · have htotalPos : 0 < total time :=
      lt_of_le_of_ne htotalNonneg (Ne.symm htotalZero)
    let weights := quittingNormalizedQuitRates root htotalPos
    let mixture : Payoff ι := fun who ↦ tail.boundary who -
      ∑ owner, weights owner * reward (quittingSingletonTerminal owner) who
    have hseparator : margin ≤ quittingCovectorPairing covector mixture := by
      apply strictSeparator_le_singletonMixturePairing reward tail.boundary
        covector weights
      · exact quittingNormalizedQuitRates_nonneg root htotalPos
      · exact sum_quittingNormalizedQuitRates root htotalPos
      · intro owner howner
        have hratePos : 0 < quittingRootQuitRates root owner := by
          rw [quitRate_eq_sum_mul_normalizedQuitRate root htotalPos owner]
          exact mul_pos htotalPos howner
        have hnotPure : root owner ≠ PMF.pure false := by
          intro hpure
          unfold quittingRootQuitRates at hratePos
          rw [hpure] at hratePos
          simp at hratePos
        have htight := hsupportTime owner hnotPure
        exact hcolumns ⟨owner, htight⟩
    apply strictCovector_mul_absorptionMass_le_bellmanDrift
      reward (tail.value time) (tail.value (time + 1)) tail.boundary
        mixture covector root weights (κ := margin) (M := M)
        (ε := closeness time) (tail.bellman time) hmarginPos
    · intro terminal who
      exact (abs_reward_le_quittingRewardBound reward terminal who).trans
        (le_max_left _ _)
    · intro who
      exact (hvalueBound (time + 1) who).trans (le_max_right _ _)
    · intro who
      exact (Finset.single_le_sum (fun other _ ↦ abs_nonneg
        (tail.value (time + 1) other - tail.boundary other))
        (Finset.mem_univ who))
    · exact quitRate_eq_sum_mul_normalizedQuitRate root htotalPos
    · exact fun _ ↦ rfl
    · exact hseparator
    · simpa only [M, total, closeness, root] using hsmallTime

omit [Nonempty ι] in
/-- Package the exact tail for terminal semantics once summability has been
derived. -/
def toSummableExactValueTail
    (hsummable : Summable (fun time ↦
      quittingRootAbsorptionMass (tail.roots time))) :
    QuittingSummableExactValueTail reward where
  roots := tail.roots
  value := tail.value
  boundary := tail.boundary
  bellman := tail.bellman
  value_tendsto := tail.value_tendsto
  absorption_summable := hsummable

omit [Nonempty ι] in
/-- **General strict-covector/positive-survival alternative.**  For every
supplied convergent diffuse exact floor tail, either the game is already
solved or one normalized covector controls all late finite and infinite
horizons.  Summability and positive suffix survival are conclusions. -/
theorem uniformPayoff_or_exists_strictCovectorPositiveSurvival :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
    ∃ covector : Payoff ι, ∃ margin : ℝ, ∃ cutoff : ℕ,
      0 < margin ∧
      (∑ who, covector who ^ 2) + margin ^ 2 = 1 ∧
      Nonempty tail.TightOwner ∧
      (∀ owner : tail.TightOwner,
        quittingPunishmentValue reward owner.1 ≤
          reward (quittingSingletonTerminal owner.1) owner.1) ∧
      (∀ᶠ time : ℕ in atTop, ∀ owner,
        tail.roots time owner ≠ PMF.pure false →
          owner ∈ tail.tightOwnerFinset) ∧
      (∀ start finish, cutoff ≤ start → start ≤ finish →
        margin / 2 * (∑ time ∈ Finset.Ico start finish,
          quittingRootAbsorptionMass (tail.roots time)) ≤
        quittingCovectorPairing covector
          (tail.value finish - tail.value start)) ∧
      Summable (fun time ↦ quittingRootAbsorptionMass (tail.roots time)) ∧
      (∀ start, cutoff ≤ start →
        margin / 2 * (∑' offset,
          quittingRootAbsorptionMass (tail.roots (start + offset))) ≤
        quittingCovectorPairing covector
          (tail.boundary - tail.value start)) ∧
      Tendsto (fun start ↦ quittingJointSurvivalLimit tail.roots start)
        atTop (nhds 1) ∧
      ∀ᶠ start in atTop, 0 < quittingJointSurvivalLimit tail.roots start := by
  by_cases hUE : ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff
  · exact Or.inl hUE
  · right
    obtain ⟨covector, margin, cutoff, hmargin, hunit, hstep⟩ :=
      tail.exists_eventual_strictCovectorCharge_of_no_uniformPayoff hUE
    have hslope : 0 < margin / 2 := by linarith
    have hshift : Summable (fun offset ↦
        quittingRootAbsorptionMass (tail.roots (cutoff + offset))) :=
      summable_charge_natAdd_of_tendsto_strictCovector
        tail.value tail.boundary
        (fun time ↦ quittingRootAbsorptionMass (tail.roots time))
        covector cutoff hslope
        (fun time ↦ quittingRootAbsorptionMass_nonneg _)
        tail.value_tendsto hstep
    have hsummable : Summable (fun time ↦
        quittingRootAbsorptionMass (tail.roots time)) := by
      have hshift' : Summable (fun offset ↦
          quittingRootAbsorptionMass (tail.roots (offset + cutoff))) := by
        simpa [Nat.add_comm] using hshift
      exact (summable_nat_add_iff cutoff).1 hshift'
    let semanticTail := tail.toSummableExactValueTail hsummable
    have hsurvival := semanticTail.jointSurvivalLimit_tendsto_one
    change Tendsto (fun start ↦ quittingJointSurvivalLimit tail.roots start)
      atTop (nhds 1) at hsurvival
    have hpositive : ∀ᶠ start in atTop,
        0 < quittingJointSurvivalLimit tail.roots start := by
      filter_upwards [(tendsto_order.1 hsurvival).1 (1 / 2 : ℝ) (by norm_num)]
        with start hstart
      linarith
    refine ⟨covector, margin, cutoff, hmargin, hunit,
      tail.tightOwner_nonempty,
      tail.tightOwner_punishmentValue_le_singleton,
      tail.eventually_active_mem_tightOwnerFinset, ?_, hsummable, ?_,
      hsurvival, hpositive⟩
    · intro start finish hstart hfinish
      exact strictCovector_mul_sum_le_pairing_sub
        tail.value
        (fun time ↦ quittingRootAbsorptionMass (tail.roots time))
        covector (margin / 2) cutoff start finish hstart hfinish hstep
    · intro start hstart
      apply strictCovector_mul_tsum_le_pairing_limit
        tail.value tail.boundary
        (fun time ↦ quittingRootAbsorptionMass (tail.roots time))
        covector cutoff start hstart hslope
        (fun time ↦ quittingRootAbsorptionMass_nonneg _)
        tail.value_tendsto hstep

end QuittingConvergentDiffuseExactFloorTail

end GameTheory
