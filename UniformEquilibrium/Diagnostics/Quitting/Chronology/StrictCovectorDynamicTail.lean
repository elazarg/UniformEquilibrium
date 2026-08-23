/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearAlgebra.FiniteConvexStrictSeparation
import UniformEquilibrium.Diagnostics.Quitting.Chronology.Conditioned.Diffuse.Closure
import UniformEquilibrium.Diagnostics.Quitting.Chronology.AbsorptionClockBallisticity
import UniformEquilibrium.Diagnostics.Quitting.Debt.DynamicTailTerminalGap
import UniformEquilibrium.Quitting.Chronology.StrictCovectorRootStep
import UniformEquilibrium.Quitting.Chronology.ConvergentDiffuseExactFloorTail
import UniformEquilibrium.Quitting.Classification.LCP.HomogeneousProductionNormalDispatch
import UniformEquilibrium.Quitting.Classification.Existence.PositiveAbsorptionStationarySplice

/-!
# A strict covector on the canonical dynamic tail

The active face is the subtype of owners whose limiting value equals their
singleton self-payoff.  A zero convex drift on that face is an ambient
homogeneous witness supported on punishment-normal owners and therefore
already solves the game.  Otherwise finite strict separation supplies one
covector for every late row.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open QuittingLCPClassification
open Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {witness : QuittingTerminalExploitabilityWitness reward}

/-- The finite set of owners tight at the limiting value. -/
def QuittingPositiveDebtDynamicTailWitness.tightOwnerFinset
    (seam : QuittingPositiveDebtDynamicTailWitness witness) : Finset ι := by
  classical
  exact Finset.univ.filter fun owner ↦
    seam.limit.value owner =
      reward (quittingSingletonTerminal owner) owner

/-- Owners tight at the limiting value of a canonical dynamic tail. -/
abbrev QuittingPositiveDebtDynamicTailWitness.TightOwner
    (seam : QuittingPositiveDebtDynamicTailWitness witness) :=
  {owner : ι // owner ∈ seam.tightOwnerFinset}

namespace QuittingPositiveDebtDynamicTailWitness

variable (seam : QuittingPositiveDebtDynamicTailWitness witness)

/-- A nonplateau canonical dynamic tail is an instance of the general
convergent diffuse exact floor-tail interface. -/
def toConvergentDiffuseExactFloorTail
    (hpositive : ∀ cutoff, ∃ time, cutoff ≤ time ∧
      0 < quittingRootAbsorptionMass
        (quittingDynamicDebtTailRoots seam.tail time)) :
    QuittingConvergentDiffuseExactFloorTail reward where
  roots := quittingDynamicDebtTailRoots seam.tail
  value := fun time ↦ (seam.tail time).1.1
  boundary := seam.limit.value
  bellman := fun time ↦ (seam.tail_edge time).1.1
  endpointNash := fun time ↦ (seam.tail_edge time).1.2
  value_tendsto := seam.value_tendsto
  solo_le_boundary := seam.limit.soloReward_le_value
  absorption_tendsto_zero := seam.rootAbsorptionMass_tendsto_zero
  arbitrarilyLate_positiveAbsorption := hpositive
  punishmentFloor := seam.punishmentValue_le_tailValue

/-- Extend a weight on limiting tight owners by zero. -/
def extendTightWeight
    (weight : seam.TightOwner → ℝ) : ι → ℝ := fun owner ↦
  if h : seam.limit.value owner =
      reward (quittingSingletonTerminal owner) owner then
    weight ⟨owner, by simpa [tightOwnerFinset] using h⟩ else 0

omit [Nonempty ι] in
@[simp] theorem extendTightWeight_apply
    (weight : seam.TightOwner → ℝ) (owner : seam.TightOwner) :
    seam.extendTightWeight weight owner.1 = weight owner := by
  unfold extendTightWeight
  have htight : seam.limit.value owner.1 =
      reward (quittingSingletonTerminal owner.1) owner.1 := by
    have hmem := owner.property
    unfold tightOwnerFinset at hmem
    exact (Finset.mem_filter.mp hmem).2
  rw [dif_pos htight]

/-- Zero extension of a tight-owner simplex remains an ambient simplex. -/
def extendTightSimplex
    (weight : stdSimplex ℝ seam.TightOwner) :
    stdSimplex ℝ ι := by
  classical
  refine ⟨seam.extendTightWeight weight.val, ?_, ?_⟩
  · intro owner
    by_cases htight : seam.limit.value owner =
        reward (quittingSingletonTerminal owner) owner
    · have hmem : owner ∈ seam.tightOwnerFinset := by
        simpa [tightOwnerFinset] using htight
      simpa [extendTightWeight, htight] using weight.property.1 ⟨owner, hmem⟩
    · simp [extendTightWeight, htight]
  · calc
      (∑ owner, seam.extendTightWeight weight.val owner) =
          ∑ owner ∈ seam.tightOwnerFinset,
            seam.extendTightWeight weight.val owner := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro owner _ howner
        have hnotTight : ¬ seam.limit.value owner =
            reward (quittingSingletonTerminal owner) owner := by
          simpa [tightOwnerFinset] using howner
        simp [extendTightWeight, hnotTight]
      _ = ∑ owner : seam.TightOwner,
          seam.extendTightWeight weight.val owner.1 := by
        exact Finset.sum_subtype
          seam.tightOwnerFinset
          (fun _ ↦ Iff.rfl) (seam.extendTightWeight weight.val : ι → ℝ)
      _ = ∑ owner : seam.TightOwner, weight.val owner := by
        apply Finset.sum_congr rfl
        intro owner _
        exact seam.extendTightWeight_apply weight.val owner
      _ = 1 := weight.property.2

omit [Nonempty ι] in
@[simp] theorem extendTightSimplex_apply
    (weight : stdSimplex ℝ seam.TightOwner)
    (owner : seam.TightOwner) :
    (seam.extendTightSimplex weight).val owner.1 = weight.val owner := by
  simp [extendTightSimplex]

omit [Nonempty ι] in
/-- Zero extension preserves weighted finite sums. -/
theorem sum_extendTightWeight_mul
    (weight : seam.TightOwner → ℝ) (f : ι → ℝ) :
    (∑ owner, seam.extendTightWeight weight owner * f owner) =
      ∑ owner : seam.TightOwner, weight owner * f owner.1 := by
  calc
    (∑ owner, seam.extendTightWeight weight owner * f owner) =
        ∑ owner ∈ seam.tightOwnerFinset,
          seam.extendTightWeight weight owner * f owner := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro owner _ howner
      have hnotTight : ¬ seam.limit.value owner =
          reward (quittingSingletonTerminal owner) owner := by
        simpa [tightOwnerFinset] using howner
      simp [extendTightWeight, hnotTight]
    _ = ∑ owner : seam.TightOwner,
        seam.extendTightWeight weight owner.1 * f owner.1 := by
      exact Finset.sum_subtype seam.tightOwnerFinset (fun _ ↦ Iff.rfl) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro owner _
      rw [seam.extendTightWeight_apply]

omit [Nonempty ι] in
/-- Every limiting tight owner is punishment-normal. -/
theorem tightOwner_punishmentValue_le_singleton (owner : seam.TightOwner) :
    quittingPunishmentValue reward owner.1 ≤
      reward (quittingSingletonTerminal owner.1) owner.1 := by
  have htight : seam.limit.value owner.1 =
      reward (quittingSingletonTerminal owner.1) owner.1 := by
    have hmem := owner.property
    unfold tightOwnerFinset at hmem
    exact (Finset.mem_filter.mp hmem).2
  exact (seam.punishmentValue_le_limitValue owner.1).trans_eq htight

omit [Nonempty ι] in
/-- After one cutoff every physically active owner belongs to the limiting
tight-owner face. -/
theorem eventually_active_mem_tightOwnerFinset :
    ∀ᶠ time : ℕ in atTop, ∀ owner,
      quittingDynamicDebtTailRoots seam.tail time owner ≠ PMF.pure false →
        owner ∈ seam.tightOwnerFinset := by
  filter_upwards [seam.eventually_active_implies_limitValue_eq_singleton]
    with time htime owner howner
  simpa [tightOwnerFinset] using htime owner howner

omit [Nonempty ι] in
/-- Unless the game is already solved, the limiting tight-owner singleton
drifts have one strict covector with a common positive margin. -/
theorem exists_strictCovector_on_tightOwners_of_no_uniformPayoff
    (hnoUE : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ covector : Payoff ι, ∃ margin : ℝ,
      0 < margin ∧
      (∑ who, covector who ^ 2) + margin ^ 2 = 1 ∧
      ∀ owner : seam.TightOwner,
        margin ≤ quittingCovectorPairing covector (fun who ↦
          seam.limit.value who -
            reward (quittingSingletonTerminal owner.1) who) := by
  let column : seam.TightOwner → ι → ℝ := fun owner who ↦
    seam.limit.value who - reward (quittingSingletonTerminal owner.1) who
  have hnot : ¬ ∃ weight : seam.TightOwner → ℝ,
      (∀ owner, 0 ≤ weight owner) ∧ (∑ owner, weight owner) = 1 ∧
      ∀ who, (∑ owner, weight owner * column owner who) = 0 := by
    rintro ⟨weight, hweight, hmass, hzero⟩
    let tightSimplex : stdSimplex ℝ seam.TightOwner := ⟨weight, hweight, hmass⟩
    let ambient := seam.extendTightSimplex tightSimplex
    have hbary : ∀ who, (∑ owner, ambient.val owner *
        reward (quittingSingletonTerminal owner) who) =
        seam.limit.value who := by
      intro who
      change (∑ owner, seam.extendTightWeight weight owner *
        reward (quittingSingletonTerminal owner) who) = _
      rw [seam.sum_extendTightWeight_mul]
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
      simpa [quittingSoloReward, quittingSingletonTerminal] using
        seam.limit.soloReward_le_value who
    · intro who
      by_cases htight : seam.limit.value who =
          reward (quittingSingletonTerminal who) who
      · rw [singletonLCPResidual_normalizedSoloMatrix_eq_singletonBarycenter]
        change ambient.val who * ((∑ owner, ambient.val owner *
          reward (quittingSingletonTerminal owner) who) - _) = 0
        rw [hbary who, htight, sub_self, mul_zero]
      · have hambient : ambient.val who = 0 := by
          simp [ambient, extendTightSimplex, extendTightWeight, htight]
        rw [hambient, zero_mul]
    · intro owner howner
      have htight : seam.limit.value owner =
          reward (quittingSingletonTerminal owner) owner := by
        by_contra hnotTight
        have : ambient.val owner = 0 := by
          simp [ambient, extendTightSimplex, extendTightWeight, hnotTight]
        linarith
      simpa [quittingSoloReward, quittingSingletonTerminal, htight] using
        seam.punishmentValue_le_limitValue owner
  simpa only [column, quittingCovectorPairing] using
    Math.LinearAlgebra.exists_euclideanUnit_strictConvexSeparator_fintype
      column hnot

omit [Nonempty ι] in
/-- On the no-uniform-payoff branch, one covector pays a fixed fraction of
every sufficiently late canonical absorption charge. -/
theorem exists_eventual_strictCovectorCharge_of_no_uniformPayoff
    (hnoUE : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ covector : Payoff ι, ∃ margin : ℝ, ∃ cutoff : ℕ,
      0 < margin ∧
      (∑ who, covector who ^ 2) + margin ^ 2 = 1 ∧
      ∀ time, cutoff ≤ time →
        margin / 2 * quittingRootAbsorptionMass
          (quittingDynamicDebtTailRoots seam.tail time) ≤
        quittingCovectorPairing covector
          ((seam.tail (time + 1)).1.1 - (seam.tail time).1.1) := by
  obtain ⟨covector, margin, hmarginPos, hunit, hcolumns⟩ :=
    seam.exists_strictCovector_on_tightOwners_of_no_uniformPayoff hnoUE
  let total : ℕ → ℝ := fun time ↦
    ∑ owner, quittingRootQuitRates
      (quittingDynamicDebtTailRoots seam.tail time) owner
  let closeness : ℕ → ℝ := fun time ↦
    ∑ who, |(seam.tail (time + 1)).1.1 who - seam.limit.value who|
  have htotal : Tendsto total atTop (nhds 0) := by
    unfold total
    simpa [quittingRootQuitRates] using
      tendsto_finsetSum Finset.univ (fun who _ ↦
      seam.quitProbability_tendsto_zero who)
  have hclose : Tendsto closeness atTop (nhds 0) := by
    unfold closeness
    convert tendsto_finsetSum Finset.univ (fun who _ ↦ by
      have hshift := (seam.value_tendsto who).comp (tendsto_add_atTop_nat 1)
      have hsub := hshift.sub_const (seam.limit.value who)
      simpa only [sub_self] using hsub.abs) using 1 <;>
        simp
  let M := quittingRewardBound reward
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
    Filter.eventually_atTop.1 seam.eventually_active_implies_limitValue_eq_singleton
  obtain ⟨smallCutoff, hsmallCutoff⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨covector, margin, max supportCutoff smallCutoff,
    hmarginPos, hunit, ?_⟩
  intro time htime
  have hsupportTime := hsupport time ((le_max_left _ _).trans htime)
  have hsmallTime := hsmallCutoff time ((le_max_right _ _).trans htime)
  let root := quittingDynamicDebtTailRoots seam.tail time
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
    have hbellman := (seam.tail_edge time).1.1
    change (seam.tail time).1.1 =
      quittingRootSuccessorPayoff reward (seam.tail (time + 1)).1.1 root
      at hbellman
    have hroot' : root = quittingAllContinueRoot := by
      funext owner
      simpa [quittingAllContinueRoot] using congrFun hroot owner
    rw [hroot', quittingRootSuccessorPayoff_allContinueRoot_eq] at hbellman
    rw [hbellman]
    simp [quittingCovectorPairing]
  · have htotalPos : 0 < total time :=
      lt_of_le_of_ne htotalNonneg (Ne.symm htotalZero)
    let weights := quittingNormalizedQuitRates root htotalPos
    let mixture : Payoff ι := fun who ↦ seam.limit.value who -
      ∑ owner, weights owner * reward (quittingSingletonTerminal owner) who
    have hseparator : margin ≤ quittingCovectorPairing covector mixture := by
      apply strictSeparator_le_singletonMixturePairing reward seam.limit.value
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
        let tightOwner : seam.TightOwner := ⟨owner, by
          simpa [tightOwnerFinset] using htight⟩
        exact hcolumns tightOwner
    apply strictCovector_mul_absorptionMass_le_bellmanDrift
      reward (seam.tail time).1.1 (seam.tail (time + 1)).1.1
        seam.limit.value mixture covector root weights
        (seam.tail_edge time).1.1 hmarginPos
        (abs_reward_le_quittingRewardBound reward)
    · intro who
      exact abs_le.mpr ⟨(seam.tail_mem (time + 1)).1.1 who,
        (seam.tail_mem (time + 1)).1.2 who⟩
    · intro who
      exact (Finset.single_le_sum (fun other _ ↦ abs_nonneg
        ((seam.tail (time + 1)).1.1 other - seam.limit.value other))
        (Finset.mem_univ who))
    · exact quitRate_eq_sum_mul_normalizedQuitRate root htotalPos
    · exact fun _ ↦ rfl
    · exact hseparator
    · simpa only [M, total, closeness, root] using hsmallTime

omit [Nonempty ι] in
/-- Arbitrarily late positive-absorption rows make the limiting tight-owner
face nonempty. -/
theorem tightOwner_nonempty_of_arbitrarilyLateAbsorption
    (hpositive : ∀ cutoff, ∃ time, cutoff ≤ time ∧
      0 < quittingRootAbsorptionMass
        (quittingDynamicDebtTailRoots seam.tail time)) :
    Nonempty seam.TightOwner := by
  obtain ⟨supportCutoff, hsupport⟩ :=
    Filter.eventually_atTop.1 seam.eventually_active_implies_limitValue_eq_singleton
  obtain ⟨time, htime, habsorption⟩ := hpositive supportCutoff
  obtain ⟨owner, howner⟩ := exists_quitProbability_pos_of_absorptionMass_pos
    (quittingDynamicDebtTailRoots seam.tail time) habsorption
  have hnotPure : quittingDynamicDebtTailRoots seam.tail time owner ≠
      PMF.pure false := by
    intro hpure
    rw [hpure] at howner
    simp at howner
  have htight := hsupport time htime owner hnotPure
  exact ⟨⟨owner, by simpa [tightOwnerFinset] using htight⟩⟩

omit [Nonempty ι] in
/-- The source-independent theorem specializes to every nonplateau canonical
dynamic tail.  In this formulation summability is displayed as a conclusion,
even though the canonical source also supplies it independently. -/
theorem uniformPayoff_or_exists_generalStrictCovectorPositiveSurvival
    (hpositive : ∀ cutoff, ∃ time, cutoff ≤ time ∧
      0 < quittingRootAbsorptionMass
        (quittingDynamicDebtTailRoots seam.tail time)) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
    ∃ covector : Payoff ι, ∃ margin : ℝ, ∃ cutoff : ℕ,
      0 < margin ∧
      (∑ who, covector who ^ 2) + margin ^ 2 = 1 ∧
      (∀ start finish, cutoff ≤ start → start ≤ finish →
        margin / 2 * (∑ time ∈ Finset.Ico start finish,
          quittingRootAbsorptionMass
            (quittingDynamicDebtTailRoots seam.tail time)) ≤
        quittingCovectorPairing covector
          ((seam.tail finish).1.1 - (seam.tail start).1.1)) ∧
      Summable (fun time ↦ quittingRootAbsorptionMass
        (quittingDynamicDebtTailRoots seam.tail time)) ∧
      (∀ start, cutoff ≤ start →
        margin / 2 * (∑' offset,
          quittingRootAbsorptionMass
            (quittingDynamicDebtTailRoots seam.tail (start + offset))) ≤
        quittingCovectorPairing covector
          (seam.limit.value - (seam.tail start).1.1)) ∧
      Tendsto (fun start ↦ quittingJointSurvivalLimit
        (quittingDynamicDebtTailRoots seam.tail) start) atTop (nhds 1) ∧
      ∀ᶠ start in atTop, 0 < quittingJointSurvivalLimit
        (quittingDynamicDebtTailRoots seam.tail) start := by
  let generalTail := seam.toConvergentDiffuseExactFloorTail hpositive
  rcases generalTail.uniformPayoff_or_exists_strictCovectorPositiveSurvival with
    hUE | ⟨covector, margin, cutoff, hmargin, hunit, _hnonempty,
      _hnormal, _hsupport, hfinite, hsummable, hinfinite, hsurvival,
      hsurvivalPositive⟩
  · exact Or.inl hUE
  · exact Or.inr ⟨covector, margin, cutoff, hmargin, hunit,
      hfinite, hsummable, hinfinite, hsurvival, hsurvivalPositive⟩

omit [Nonempty ι] in
/-- **Canonical strict-covector/positive-survival alternative.**  Either the
game is already solved, or one normalized covector controls every sufficiently
late horizon and every infinite residual tail of the actual dynamic witness.
The literal suffix survival probabilities converge to one and are eventually
strictly positive. -/
theorem uniformPayoff_or_exists_strictCovectorPositiveSurvival :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
    ∃ covector : Payoff ι, ∃ margin : ℝ, ∃ cutoff : ℕ,
      0 < margin ∧
      (∑ who, covector who ^ 2) + margin ^ 2 = 1 ∧
      (∀ start finish, cutoff ≤ start → start ≤ finish →
        margin / 2 * (∑ time ∈ Finset.Ico start finish,
          quittingRootAbsorptionMass
            (quittingDynamicDebtTailRoots seam.tail time)) ≤
        quittingCovectorPairing covector
          ((seam.tail finish).1.1 - (seam.tail start).1.1)) ∧
      (∀ start, cutoff ≤ start →
        margin / 2 * (∑' offset,
          quittingRootAbsorptionMass
            (quittingDynamicDebtTailRoots seam.tail (start + offset))) ≤
        quittingCovectorPairing covector
          (seam.limit.value - (seam.tail start).1.1)) ∧
      Tendsto (fun start ↦ quittingJointSurvivalLimit
        (quittingDynamicDebtTailRoots seam.tail) start) atTop (nhds 1) ∧
      ∀ᶠ start in atTop, 0 < quittingJointSurvivalLimit
        (quittingDynamicDebtTailRoots seam.tail) start := by
  by_cases hUE : ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff
  · exact Or.inl hUE
  · right
    obtain ⟨covector, margin, cutoff, hmargin, hunit, hstep⟩ :=
      seam.exists_eventual_strictCovectorCharge_of_no_uniformPayoff hUE
    have hsurvival := seam.toSummableExactValueTail.jointSurvivalLimit_tendsto_one
    change Tendsto (fun start ↦ quittingJointSurvivalLimit
      (quittingDynamicDebtTailRoots seam.tail) start) atTop (nhds 1)
      at hsurvival
    have hpositive : ∀ᶠ start in atTop,
        0 < quittingJointSurvivalLimit
          (quittingDynamicDebtTailRoots seam.tail) start := by
      filter_upwards [(tendsto_order.1 hsurvival).1 (1 / 2 : ℝ) (by norm_num)]
        with start hstart
      linarith
    refine ⟨covector, margin, cutoff, hmargin, hunit, ?_, ?_,
      hsurvival, hpositive⟩
    · intro start finish hstart hfinish
      exact strictCovector_mul_sum_le_pairing_sub
        (fun time ↦ (seam.tail time).1.1)
        (fun time ↦ quittingRootAbsorptionMass
          (quittingDynamicDebtTailRoots seam.tail time))
        covector (margin / 2) cutoff start finish hstart hfinish hstep
    · intro start hstart
      apply strictCovector_mul_tsum_le_pairing_limit
        (fun time ↦ (seam.tail time).1.1) seam.limit.value
        (fun time ↦ quittingRootAbsorptionMass
          (quittingDynamicDebtTailRoots seam.tail time))
        covector cutoff start hstart (by linarith)
        (fun time ↦ quittingRootAbsorptionMass_nonneg _)
        seam.value_tendsto hstep

end QuittingPositiveDebtDynamicTailWitness

end GameTheory
