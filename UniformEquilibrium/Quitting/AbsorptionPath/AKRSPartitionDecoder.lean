/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.AKRSPartitionSmallCell
import UniformEquilibrium.Quitting.AbsorptionPath.ChronologicalRootSequenceTail
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Root.TailStability

/-!
# Payoff decoder for the canonical AKRS partition

The independent cell rows have the same exact survival weights as the source
path cells.  Their coordinatewise productization errors therefore telescope
to one uniform suffix-payoff bound.  This is the literal quantitative decoder
needed downstream; it does not assert full weak convergence of path laws.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingAbsorptionPath

/-- The absorbing payoff contribution prescribed by one literal path cell. -/
def partitionPathCellAbsorbingContribution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι)) (resolution stage : ℕ)
    (player : ι) : ℝ :=
  ∑ terminal : {S : Finset ι // S.Nonempty},
    pathCellLaw path.1 (partitionCut path resolution stage)
      (partitionCut path resolution (stage + 1)) terminal.1 *
        reward terminal player

/-- Uniform coefficient converting the per-coordinate productization error
into one payoff-coordinate error. -/
def partitionDecoderPayoffErrorCoefficient
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (resolution : ℕ) : ℝ :=
  Fintype.card {S : Finset ι // S.Nonempty} *
    quittingRewardBound reward * agkrsSmallCellCoordinateConstant ι *
      partitionSmallCellError resolution

/-- One decoded row's absorbing payoff contribution differs from its source
cell contribution by at most the uniform coefficient times cell absorption. -/
theorem abs_partitionCellRoot_absorbingContribution_sub_pathCell_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) (player : ι) :
    |quittingRootAbsorbingContribution reward
          (partitionCellRoot path hpathTotal hnoTerminalJump resolution
            hresolution hcollision stage) player -
        partitionPathCellAbsorbingContribution reward path resolution stage
          player| ≤
      partitionDecoderPayoffErrorCoefficient reward resolution *
        pathCellAbsorption path.1 (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1)) := by
  let cellAbsorption := pathCellAbsorption path.1
    (partitionCut path resolution stage)
    (partitionCut path resolution (stage + 1))
  have habsorptionNonneg : 0 ≤ cellAbsorption := by
    unfold cellAbsorption
    rw [← partitionCellRoot_absorption_exact path hpathTotal
      hnoTerminalJump resolution hresolution hcollision stage]
    exact quittingRootAbsorptionMass_nonneg _
  have hcoordinateConstant : 0 ≤ agkrsSmallCellCoordinateConstant ι := by
    unfold agkrsSmallCellCoordinateConstant
    exact_mod_cast Nat.zero_le (2 ^ Fintype.card ι)
  have herrorNonneg : 0 ≤ partitionSmallCellError resolution :=
    (partitionSmallCellError_pos resolution hresolution).le
  have hcoordinateUpperNonneg : 0 ≤
      agkrsSmallCellCoordinateConstant ι *
        partitionSmallCellError resolution * cellAbsorption :=
    mul_nonneg (mul_nonneg hcoordinateConstant herrorNonneg)
      habsorptionNonneg
  rw [quittingRootAbsorbingContribution_eq_sum_nonemptyCoalitionMass]
  unfold partitionPathCellAbsorbingContribution
  change |(∑ terminal : {S : Finset ι // S.Nonempty},
      quittingRootCoalitionMass
          (partitionCellRoot path hpathTotal hnoTerminalJump resolution
            hresolution hcollision stage) terminal.1 * reward terminal player) -
    ∑ terminal : {S : Finset ι // S.Nonempty},
      pathCellLaw path.1 (partitionCut path resolution stage)
        (partitionCut path resolution (stage + 1)) terminal.1 *
          reward terminal player| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ terminal : {S : Finset ι // S.Nonempty},
          |quittingRootCoalitionMass
              (partitionCellRoot path hpathTotal hnoTerminalJump resolution
                hresolution hcollision stage) terminal.1 * reward terminal player -
            pathCellLaw path.1 (partitionCut path resolution stage)
              (partitionCut path resolution (stage + 1)) terminal.1 *
                reward terminal player| := by
      simpa only using Finset.abs_sum_le_sum_abs
        (fun terminal : {S : Finset ι // S.Nonempty} ↦
          quittingRootCoalitionMass
              (partitionCellRoot path hpathTotal hnoTerminalJump resolution
                hresolution hcollision stage) terminal.1 * reward terminal player -
            pathCellLaw path.1 (partitionCut path resolution stage)
              (partitionCut path resolution (stage + 1)) terminal.1 *
                reward terminal player) Finset.univ
    _ ≤ ∑ _terminal : {S : Finset ι // S.Nonempty},
        (agkrsSmallCellCoordinateConstant ι *
          partitionSmallCellError resolution * cellAbsorption) *
            quittingRewardBound reward := by
      apply Finset.sum_le_sum
      intro terminal _
      rw [← sub_mul, abs_mul]
      exact mul_le_mul
        (partitionCellRoot_coalition_coordinate_error path hpathTotal
          hnoTerminalJump resolution hresolution hcollision stage terminal.1
          terminal.2)
        (abs_reward_le_quittingRewardBound reward terminal player)
        (abs_nonneg _) hcoordinateUpperNonneg
    _ = partitionDecoderPayoffErrorCoefficient reward resolution *
        pathCellAbsorption path.1 (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1)) := by
      unfold partitionDecoderPayoffErrorCoefficient cellAbsorption
      rw [Finset.sum_const, Finset.card_univ]
      ring

/-- At every suffix entrance, finite survival-weighted payoff-law errors are
bounded by one common resolution coefficient. -/
theorem sum_range_partitionDecoderWeightedPayoffError_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (start fuel : ℕ) (player : ι) :
    (∑ offset ∈ Finset.range fuel,
      quittingJointSurvivalWeight
          (partitionCellRoots path hpathTotal hnoTerminalJump resolution
            hresolution hcollision) start offset *
        |quittingRootAbsorbingContribution reward
              (partitionCellRoot path hpathTotal hnoTerminalJump resolution
                hresolution hcollision (start + offset)) player -
          partitionPathCellAbsorbingContribution reward path resolution
            (start + offset) player|) ≤
      partitionDecoderPayoffErrorCoefficient reward resolution := by
  let roots := partitionCellRoots path hpathTotal hnoTerminalJump resolution
    hresolution hcollision
  let coefficient := partitionDecoderPayoffErrorCoefficient reward resolution
  let cellAbsorption := fun stage ↦ pathCellAbsorption path.1
    (partitionCut path resolution stage)
    (partitionCut path resolution (stage + 1))
  have hcoefficientNonneg : 0 ≤ coefficient := by
    unfold coefficient partitionDecoderPayoffErrorCoefficient
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (quittingRewardBound_nonneg reward))
        (by
          unfold agkrsSmallCellCoordinateConstant
          exact_mod_cast Nat.zero_le (2 ^ Fintype.card ι)))
      (partitionSmallCellError_pos resolution hresolution).le
  have habsorption (stage : ℕ) :
      cellAbsorption stage = 1 - quittingStationaryContinueMass (roots stage) := by
    unfold cellAbsorption roots partitionCellRoots
    rw [← partitionCellRoot_absorption_exact path hpathTotal hnoTerminalJump
      resolution hresolution hcollision stage]
    rfl
  calc
    _ ≤ ∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight roots start offset *
          (coefficient * cellAbsorption (start + offset)) := by
      apply Finset.sum_le_sum
      intro offset _
      apply mul_le_mul_of_nonneg_left
      · exact abs_partitionCellRoot_absorbingContribution_sub_pathCell_le
          reward path hpathTotal hnoTerminalJump resolution hresolution
          hcollision (start + offset) player
      · exact quittingJointSurvivalWeight_nonneg roots start offset
    _ = coefficient * (∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight roots start offset *
          cellAbsorption (start + offset)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro offset _
      ring
    _ = coefficient * (1 -
        quittingJointSurvivalWeight roots start fuel) := by
      have hsum := sum_quittingJointSurvivalWeight_mul_one_sub_continueMass
        roots start fuel
      congr 1
      rw [← hsum]
      apply Finset.sum_congr rfl
      intro offset _
      rw [habsorption]
    _ ≤ coefficient := by
      have hsurvivalNonneg :=
        quittingJointSurvivalWeight_nonneg roots start fuel
      nlinarith

/-- The infinite survival-weighted difference between decoded cell rewards
and literal path-cell rewards is uniformly bounded at every suffix entrance. -/
theorem tsum_partitionDecoderWeightedPayoffError_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (start : ℕ) (player : ι) :
    (∑' offset : ℕ,
      quittingJointSurvivalWeight
          (partitionCellRoots path hpathTotal hnoTerminalJump resolution
            hresolution hcollision) start offset *
        |quittingRootAbsorbingContribution reward
              (partitionCellRoot path hpathTotal hnoTerminalJump resolution
                hresolution hcollision (start + offset)) player -
          partitionPathCellAbsorbingContribution reward path resolution
            (start + offset) player|) ≤
      partitionDecoderPayoffErrorCoefficient reward resolution := by
  apply Real.tsum_le_of_sum_range_le
  · intro offset
    exact mul_nonneg
      (quittingJointSurvivalWeight_nonneg _ start offset) (abs_nonneg _)
  · intro fuel
    exact sum_range_partitionDecoderWeightedPayoffError_le reward path
      hpathTotal hnoTerminalJump resolution hresolution hcollision start fuel
      player

/-- The literal path-cell payoff series, using exactly the decoder's survival
weights but the source cell law at every row. -/
def partitionPathSuffixPayoffSeries
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (start : ℕ) (player : ι) : ℝ :=
  ∑' offset : ℕ,
    quittingJointSurvivalWeight
        (partitionCellRoots path hpathTotal hnoTerminalJump resolution
          hresolution hcollision) start offset *
      partitionPathCellAbsorbingContribution reward path resolution
        (start + offset) player

/-- The actual decoded suffix payoff is uniformly close to the literal
path-cell payoff series at every calendar row. -/
theorem abs_partitionCellRoots_terminalValue_sub_pathSuffixSeries_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (start : ℕ) (player : ι) :
    |quittingRootSequenceTerminalValue reward
          (partitionCellRoots path hpathTotal hnoTerminalJump resolution
            hresolution hcollision) player start -
        partitionPathSuffixPayoffSeries reward path hpathTotal hnoTerminalJump
          resolution hresolution hcollision start player| ≤
      partitionDecoderPayoffErrorCoefficient reward resolution := by
  let roots := partitionCellRoots path hpathTotal hnoTerminalJump resolution
    hresolution hcollision
  let actual := fun offset : ℕ ↦
    quittingJointSurvivalWeight roots start offset *
      quittingRootAbsorbingContribution reward (roots (start + offset)) player
  let reference := fun offset : ℕ ↦
    quittingJointSurvivalWeight roots start offset *
      partitionPathCellAbsorbingContribution reward path resolution
        (start + offset) player
  let difference := fun offset : ℕ ↦ actual offset - reference offset
  have hactual : Summable actual := by
    exact summable_quittingJointSurvivalWeight_mul_quittingRootAbsorbingContribution
      reward roots player start
  have hdiffNorm : Summable fun offset : ℕ ↦ |difference offset| := by
    apply summable_of_sum_range_le
      (c := partitionDecoderPayoffErrorCoefficient reward resolution)
    · intro offset
      exact abs_nonneg _
    · intro fuel
      calc
        (∑ offset ∈ Finset.range fuel,
            |difference offset|) =
            ∑ offset ∈ Finset.range fuel,
              quittingJointSurvivalWeight roots start offset *
                |quittingRootAbsorbingContribution reward
                    (roots (start + offset)) player -
                  partitionPathCellAbsorbingContribution reward path resolution
                    (start + offset) player| := by
          apply Finset.sum_congr rfl
          intro offset _
          unfold difference actual reference
          rw [← mul_sub, abs_mul, abs_of_nonneg
            (quittingJointSurvivalWeight_nonneg roots start offset)]
        _ ≤ partitionDecoderPayoffErrorCoefficient reward resolution := by
          simpa only [roots, partitionCellRoots] using
            sum_range_partitionDecoderWeightedPayoffError_le reward path
              hpathTotal hnoTerminalJump resolution hresolution hcollision start
              fuel player
  have hdiff : Summable difference := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using hdiffNorm
  have hdiffNormNorm : Summable fun offset : ℕ ↦ ‖difference offset‖ := by
    simpa only [Real.norm_eq_abs] using hdiffNorm
  have hreference : Summable reference := by
    have h := hactual.sub hdiff
    simpa only [actual, reference, difference] using h.congr fun offset ↦ by ring
  rw [quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution]
  unfold partitionPathSuffixPayoffSeries
  change abs ((∑' offset, actual offset) - ∑' offset, reference offset) ≤ _
  have htsumSub : (∑' offset, difference offset) =
      (∑' offset, actual offset) - ∑' offset, reference offset := by
    simpa only [difference] using hactual.tsum_sub hreference
  rw [← htsumSub]
  calc
    abs (∑' offset, difference offset) ≤
        ∑' offset, |difference offset| := by
      change ‖∑' offset, difference offset‖ ≤
        ∑' offset, ‖difference offset‖
      exact norm_tsum_le_tsum_norm hdiffNormNorm
    _ = ∑' offset : ℕ,
        quittingJointSurvivalWeight roots start offset *
          |quittingRootAbsorbingContribution reward
              (roots (start + offset)) player -
            partitionPathCellAbsorbingContribution reward path resolution
              (start + offset) player| := by
      congr 1
      funext offset
      unfold difference actual reference
      rw [← mul_sub, abs_mul, abs_of_nonneg
        (quittingJointSurvivalWeight_nonneg roots start offset)]
    _ ≤ partitionDecoderPayoffErrorCoefficient reward resolution := by
      simpa only [roots, partitionCellRoots] using
        tsum_partitionDecoderWeightedPayoffError_le reward path hpathTotal
          hnoTerminalJump resolution hresolution hcollision start player

/-- Global survival of the decoded rows is exactly the remaining mass at the
corresponding recursive cut. -/
theorem quittingRootSequenceSurvival_partitionCellRoots
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) :
    quittingRootSequenceSurvival
        (partitionCellRoots path hpathTotal hnoTerminalJump resolution
          hresolution hcollision) stage =
      1 - partitionCut path resolution stage := by
  unfold quittingRootSequenceSurvival
  rw [quittingJointSurvivalWeight_eq_quittingSurvivalPrefix]
  simpa only [Nat.zero_add] using
    quittingSurvivalPrefix_partitionCellRoots path hpathTotal hnoTerminalJump
      resolution hresolution hcollision stage

/-- Conditional decoded survival between two cuts is the ratio of their
remaining clock masses. -/
theorem quittingJointSurvivalWeight_partitionCellRoots_eq_cut_ratio
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (start offset : ℕ) :
    quittingJointSurvivalWeight
        (partitionCellRoots path hpathTotal hnoTerminalJump resolution
          hresolution hcollision) start offset =
      (1 - partitionCut path resolution (start + offset)) /
        (1 - partitionCut path resolution start) := by
  let roots := partitionCellRoots path hpathTotal hnoTerminalJump resolution
    hresolution hcollision
  have hresolutionTwo : 2 ≤ resolution := by omega
  have hstartOne := partitionCut_lt_one path hpathTotal hnoTerminalJump
    resolution hresolutionTwo start
  have hfactor := quittingJointSurvivalWeight_add roots 0 start offset
  have hfactor' :
      1 - partitionCut path resolution (start + offset) =
        (1 - partitionCut path resolution start) *
          quittingJointSurvivalWeight roots start offset := by
    calc
      1 - partitionCut path resolution (start + offset) =
          quittingRootSequenceSurvival roots (start + offset) := by
        symm
        exact quittingRootSequenceSurvival_partitionCellRoots path hpathTotal
          hnoTerminalJump resolution hresolution hcollision (start + offset)
      _ = quittingRootSequenceSurvival roots start *
          quittingJointSurvivalWeight roots start offset := by
        simpa only [quittingRootSequenceSurvival, Nat.zero_add] using hfactor
      _ = (1 - partitionCut path resolution start) *
          quittingJointSurvivalWeight roots start offset := by
        rw [quittingRootSequenceSurvival_partitionCellRoots path hpathTotal
          hnoTerminalJump resolution hresolution hcollision start]
  apply (eq_div_iff (sub_ne_zero.mpr hstartOne.ne')).2
  rw [mul_comm]
  exact hfactor'.symm

/-- Finite prefixes of the literal path-cell payoff series telescope exactly
to the normalized coordinate increment between their endpoint cuts. -/
theorem sum_range_partitionPathCellContribution_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (start fuel : ℕ) (player : ι) :
    (∑ offset ∈ Finset.range fuel,
      quittingJointSurvivalWeight
          (partitionCellRoots path hpathTotal hnoTerminalJump resolution
            hresolution hcollision) start offset *
        partitionPathCellAbsorbingContribution reward path resolution
          (start + offset) player) =
      ∑ terminal : {S : Finset ι // S.Nonempty},
        ((path.1.leftValue (partitionCut path resolution (start + fuel))
              terminal -
            path.1.leftValue (partitionCut path resolution start) terminal) *
          reward terminal player) /
            (1 - partitionCut path resolution start) := by
  let roots := partitionCellRoots path hpathTotal hnoTerminalJump resolution
    hresolution hcollision
  let cuts := partitionCut path resolution
  have hresolutionTwo : 2 ≤ resolution := by omega
  have hstartOne : cuts start < 1 :=
    partitionCut_lt_one path hpathTotal hnoTerminalJump resolution
      hresolutionTwo start
  have hpoint (offset : ℕ) :
      quittingJointSurvivalWeight roots start offset *
          partitionPathCellAbsorbingContribution reward path resolution
            (start + offset) player =
        ∑ terminal : {S : Finset ι // S.Nonempty},
          ((path.1.leftValue (cuts (start + offset + 1)) terminal -
              path.1.leftValue (cuts (start + offset)) terminal) *
            reward terminal player) / (1 - cuts start) := by
    rw [quittingJointSurvivalWeight_partitionCellRoots_eq_cut_ratio path
      hpathTotal hnoTerminalJump resolution hresolution hcollision]
    unfold partitionPathCellAbsorbingContribution
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro terminal _
    rw [pathCellLaw_nonempty path.1
      (cuts (start + offset)) (cuts (start + offset + 1)) terminal]
    have hcurrentOne : cuts (start + offset) < 1 :=
      partitionCut_lt_one path hpathTotal hnoTerminalJump resolution
        hresolutionTwo (start + offset)
    dsimp [cuts] at hstartOne hcurrentOne ⊢
    have hstartDenominator :
        1 - partitionCut path resolution start ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr hstartOne)
    have hcurrentDenominator :
        1 - partitionCut path resolution (start + offset) ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr hcurrentOne)
    field_simp [hstartDenominator, hcurrentDenominator]
  change
    (∑ offset ∈ Finset.range fuel,
      quittingJointSurvivalWeight roots start offset *
        partitionPathCellAbsorbingContribution reward path resolution
          (start + offset) player) =
      ∑ terminal : {S : Finset ι // S.Nonempty},
        ((path.1.leftValue (cuts (start + fuel)) terminal -
            path.1.leftValue (cuts start) terminal) *
          reward terminal player) / (1 - cuts start)
  have hsum :
      (∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight roots start offset *
          partitionPathCellAbsorbingContribution reward path resolution
            (start + offset) player) =
        ∑ offset ∈ Finset.range fuel,
          ∑ terminal : {S : Finset ι // S.Nonempty},
            ((path.1.leftValue (cuts (start + offset + 1)) terminal -
                path.1.leftValue (cuts (start + offset)) terminal) *
              reward terminal player) / (1 - cuts start) := by
    apply Finset.sum_congr rfl
    intro offset _
    exact hpoint offset
  rw [hsum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro terminal _
  calc
    (∑ offset ∈ Finset.range fuel,
        ((path.1.leftValue (cuts (start + offset + 1)) terminal -
            path.1.leftValue (cuts (start + offset)) terminal) *
          reward terminal player) / (1 - cuts start)) =
        ((∑ offset ∈ Finset.range fuel,
            (path.1.leftValue (cuts (start + offset + 1)) terminal -
              path.1.leftValue (cuts (start + offset)) terminal)) *
          reward terminal player) / (1 - cuts start) := by
      rw [Finset.sum_mul, Finset.sum_div]
    _ = ((path.1.leftValue (cuts (start + fuel)) terminal -
            path.1.leftValue (cuts start) terminal) *
          reward terminal player) / (1 - cuts start) := by
      have htelescope := Finset.sum_range_sub
        (fun offset => path.1.leftValue (cuts (start + offset)) terminal) fuel
      rw [show
        (∑ offset ∈ Finset.range fuel,
            (path.1.leftValue (cuts (start + offset + 1)) terminal -
              path.1.leftValue (cuts (start + offset)) terminal)) =
          path.1.leftValue (cuts (start + fuel)) terminal -
            path.1.leftValue (cuts start) terminal by
        simpa only [Nat.add_assoc, Nat.add_zero] using htelescope]

/-- Immediately before a boundary, the remaining path mass has this
normalized payoff.  This is the literal path quantity computed by the cell
decoder's suffix series. -/
def absorptionPathPreBoundaryPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι)) (time : ℝ) : Payoff ι :=
  fun player =>
    (∑ terminal : {S : Finset ι // S.Nonempty},
      (path.1.value 1 terminal - path.1.leftValue time terminal) *
        reward terminal player) / (1 - time)

omit [Nonempty ι] in
/-- If total mass is bounded by one and no jump is terminal, then clock one
has no coordinate jump: every terminal value equals its left limit. -/
theorem value_one_eq_leftValue_one_of_noTerminalTotalJump
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (terminal : {S : Finset ι // S.Nonempty}) :
    path.1.value 1 terminal = path.1.leftValue 1 terminal := by
  have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have htotalOne : pathTotal path.1 1 = 1 := by
    exact le_antisymm (hpathTotal 1 hone) (path.property.1 1 hone)
  have hjumpZero : pathJump path.1 1 terminal = 0 := by
    by_contra hjumpNonzero
    have hjump : (1 : ℝ) ∈ pathJumps path.1 :=
      ⟨hone, terminal, hjumpNonzero⟩
    have hterminal := hnoTerminalJump 1 hjump
    linarith
  unfold pathJump at hjumpZero
  linarith

/-- The survival-weighted literal path-cell contributions form a summable
series at every decoder suffix. -/
theorem summable_partitionPathCellContribution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (start : ℕ) (player : ι) :
    Summable fun offset : ℕ =>
      quittingJointSurvivalWeight
          (partitionCellRoots path hpathTotal hnoTerminalJump resolution
            hresolution hcollision) start offset *
        partitionPathCellAbsorbingContribution reward path resolution
          (start + offset) player := by
  let roots := partitionCellRoots path hpathTotal hnoTerminalJump resolution
    hresolution hcollision
  let actual := fun offset : ℕ =>
    quittingJointSurvivalWeight roots start offset *
      quittingRootAbsorbingContribution reward (roots (start + offset)) player
  let reference := fun offset : ℕ =>
    quittingJointSurvivalWeight roots start offset *
      partitionPathCellAbsorbingContribution reward path resolution
        (start + offset) player
  let difference := fun offset : ℕ => actual offset - reference offset
  have hactual : Summable actual := by
    exact
      summable_quittingJointSurvivalWeight_mul_quittingRootAbsorbingContribution
        reward roots player start
  have hdiffNorm : Summable fun offset : ℕ => |difference offset| := by
    apply summable_of_sum_range_le
      (c := partitionDecoderPayoffErrorCoefficient reward resolution)
    · intro offset
      exact abs_nonneg _
    · intro fuel
      calc
        (∑ offset ∈ Finset.range fuel, |difference offset|) =
            ∑ offset ∈ Finset.range fuel,
              quittingJointSurvivalWeight roots start offset *
                |quittingRootAbsorbingContribution reward
                    (roots (start + offset)) player -
                  partitionPathCellAbsorbingContribution reward path resolution
                    (start + offset) player| := by
          apply Finset.sum_congr rfl
          intro offset _
          unfold difference actual reference
          rw [← mul_sub, abs_mul, abs_of_nonneg
            (quittingJointSurvivalWeight_nonneg roots start offset)]
        _ ≤ partitionDecoderPayoffErrorCoefficient reward resolution := by
          simpa only [roots, partitionCellRoots] using
            sum_range_partitionDecoderWeightedPayoffError_le reward path
              hpathTotal hnoTerminalJump resolution hresolution hcollision start
              fuel player
  have hdiff : Summable difference := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using hdiffNorm
  have hreference : Summable reference := by
    have h := hactual.sub hdiff
    simpa only [actual, reference, difference] using h.congr fun offset => by ring
  simpa only [roots, reference, partitionCellRoots] using hreference

omit [Nonempty ι] in
/-- Along every shifted decoder suffix, each coordinate left limit converges
to its left limit at clock one. -/
theorem tendsto_leftValue_partitionCut_add
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 2 ≤ resolution)
    (start : ℕ) (terminal : {S : Finset ι // S.Nonempty}) :
    Tendsto
      (fun fuel => path.1.leftValue
        (partitionCut path resolution (start + fuel)) terminal)
      atTop (nhds (path.1.leftValue 1 terminal)) := by
  have hcutTendsto : Tendsto
      (fun fuel => partitionCut path resolution (start + fuel))
      atTop (nhds 1) := by
    have hcuts := tendsto_partitionCut_one path hpathTotal resolution
      (by omega : 1 ≤ resolution)
    have hraw := hcuts.comp (tendsto_add_atTop_nat start)
    refine hraw.congr' (Filter.Eventually.of_forall fun fuel => ?_)
    simp only [Function.comp_apply, Nat.add_comm]
  have hcutWithin : Tendsto
      (fun fuel => partitionCut path resolution (start + fuel)) atTop
      (nhdsWithin 1 (Set.Icc (0 : ℝ) 1 \ {1})) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hcutTendsto, Filter.Eventually.of_forall fun fuel => ?_⟩
    have hmem := partitionCut_mem_Icc path hpathTotal resolution
      (by omega : 1 ≤ resolution) (start + fuel)
    have hlt := partitionCut_lt_one path hpathTotal hnoTerminalJump resolution
      hresolution (start + fuel)
    exact ⟨hmem, by simp only [Set.mem_singleton_iff]; exact hlt.ne⟩
  have hvalueTendsto : Tendsto
      (fun fuel => path.1.value
        (partitionCut path resolution (start + fuel)) terminal)
      atTop (nhds (path.1.leftValue 1 terminal)) := by
    have hraw :=
      (path.1.left_limit terminal 1 (by norm_num)).comp hcutWithin
    refine hraw.congr' (Filter.Eventually.of_forall fun fuel => ?_)
    rfl
  let leftAtCut := fun fuel => path.1.leftValue
    (partitionCut path resolution (start + fuel)) terminal
  have hleftShift : Tendsto (fun fuel => leftAtCut (fuel + 2)) atTop
      (nhds (path.1.leftValue 1 terminal)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hvalueTendsto
      tendsto_const_nhds
    · exact Filter.Eventually.of_forall fun fuel => by
        have hcurrentMem := partitionCut_mem_Icc path hpathTotal resolution
          (by omega : 1 ≤ resolution) (start + fuel)
        have hlaterMem := partitionCut_mem_Icc path hpathTotal resolution
          (by omega : 1 ≤ resolution) (start + (fuel + 2))
        have hcurrentOne := partitionCut_lt_one path hpathTotal
          hnoTerminalJump resolution hresolution (start + fuel)
        have hprobeStrict := (partitionProbe_mem_Ioo resolution hresolution
          ⟨hcurrentMem.1, hcurrentOne⟩).1
        have hprobeLe := partitionProbe_partitionCut_le_add_two path hpathTotal
          resolution (by omega : 1 ≤ resolution) (start + fuel)
        have hcutStrict :
            partitionCut path resolution (start + fuel) <
              partitionCut path resolution (start + (fuel + 2)) := by
          rw [show start + (fuel + 2) = start + fuel + 2 by omega]
          exact hprobeStrict.trans_le hprobeLe
        exact path.1.value_le_leftValue_of_lt terminal hcurrentMem hlaterMem
          hcutStrict
    · exact Filter.Eventually.of_forall fun fuel => by
        have hlaterMem := partitionCut_mem_Icc path hpathTotal resolution
          (by omega : 1 ≤ resolution) (start + (fuel + 2))
        exact path.1.leftValue_mono terminal hlaterMem
          (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) hlaterMem.2
  apply (tendsto_add_atTop_iff_nat 2).1
  simpa only [leftAtCut, Nat.add_assoc] using hleftShift

/-- The literal path-cell suffix series is exactly the normalized path payoff
immediately before its entrance cut. -/
theorem partitionPathSuffixPayoffSeries_eq_preBoundaryPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (start : ℕ) (player : ι) :
    partitionPathSuffixPayoffSeries reward path hpathTotal hnoTerminalJump
        resolution hresolution hcollision start player =
      absorptionPathPreBoundaryPayoff reward path
        (partitionCut path resolution start) player := by
  let roots := partitionCellRoots path hpathTotal hnoTerminalJump resolution
    hresolution hcollision
  let cuts := partitionCut path resolution
  let reference := fun offset : ℕ =>
    quittingJointSurvivalWeight roots start offset *
      partitionPathCellAbsorbingContribution reward path resolution
        (start + offset) player
  have hreference : Summable reference := by
    simpa only [reference, roots, partitionCellRoots] using
      summable_partitionPathCellContribution reward path hpathTotal
        hnoTerminalJump resolution hresolution hcollision start player
  have hleftTendsto (terminal : {S : Finset ι // S.Nonempty}) :
      Tendsto
        (fun fuel => path.1.leftValue (cuts (start + fuel)) terminal)
        atTop (nhds (path.1.leftValue 1 terminal)) := by
    simpa only [cuts] using
      tendsto_leftValue_partitionCut_add path hpathTotal hnoTerminalJump
        resolution (by omega : 2 ≤ resolution) start terminal
  have hnormalizedTendsto : Tendsto
      (fun fuel =>
        ∑ terminal : {S : Finset ι // S.Nonempty},
          ((path.1.leftValue (cuts (start + fuel)) terminal -
              path.1.leftValue (cuts start) terminal) *
            reward terminal player) / (1 - cuts start))
      atTop
      (nhds (∑ terminal : {S : Finset ι // S.Nonempty},
        ((path.1.leftValue 1 terminal -
            path.1.leftValue (cuts start) terminal) *
          reward terminal player) / (1 - cuts start))) := by
    simpa only using tendsto_finsetSum Finset.univ fun terminal _ =>
      (((hleftTendsto terminal).sub tendsto_const_nhds).mul_const
        (reward terminal player)).div_const (1 - cuts start)
  have hpartialTendsto : Tendsto
      (fun fuel => ∑ offset ∈ Finset.range fuel, reference offset)
      atTop
      (nhds (∑ terminal : {S : Finset ι // S.Nonempty},
        ((path.1.leftValue 1 terminal -
            path.1.leftValue (cuts start) terminal) *
          reward terminal player) / (1 - cuts start))) := by
    refine hnormalizedTendsto.congr'
      (Filter.Eventually.of_forall fun fuel => ?_)
    have hfinite := sum_range_partitionPathCellContribution_eq reward path
      hpathTotal hnoTerminalJump resolution hresolution hcollision start fuel
      player
    simpa only [reference, roots, cuts, partitionCellRoots] using hfinite.symm
  have htarget :
      (∑ terminal : {S : Finset ι // S.Nonempty},
        ((path.1.leftValue 1 terminal -
            path.1.leftValue (cuts start) terminal) *
          reward terminal player) / (1 - cuts start)) =
        absorptionPathPreBoundaryPayoff reward path (cuts start) player := by
    unfold absorptionPathPreBoundaryPayoff
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro terminal _
    rw [value_one_eq_leftValue_one_of_noTerminalTotalJump path hpathTotal
      hnoTerminalJump terminal]
  rw [htarget] at hpartialTendsto
  unfold partitionPathSuffixPayoffSeries
  change (∑' offset, reference offset) = _
  exact tendsto_nhds_unique hreference.hasSum.tendsto_sum_nat hpartialTendsto

/-- Every decoded suffix payoff is uniformly close to the literal path payoff
immediately before its entrance cut. -/
theorem abs_partitionCellRoots_terminalValue_sub_preBoundaryPayoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (start : ℕ) (player : ι) :
    |quittingRootSequenceTerminalValue reward
          (partitionCellRoots path hpathTotal hnoTerminalJump resolution
            hresolution hcollision) player start -
        absorptionPathPreBoundaryPayoff reward path
          (partitionCut path resolution start) player| ≤
      partitionDecoderPayoffErrorCoefficient reward resolution := by
  rw [← partitionPathSuffixPayoffSeries_eq_preBoundaryPayoff reward path
    hpathTotal hnoTerminalJump resolution hresolution hcollision start player]
  exact abs_partitionCellRoots_terminalValue_sub_pathSuffixSeries_le reward
    path hpathTotal hnoTerminalJump resolution hresolution hcollision start
    player

omit [Nonempty ι] in
/-- Support-local endpoint optimality transfers to a nearby continuation
vector with one additive copy of the coordinatewise tail error. -/
theorem supportApproxNash_of_tail_close
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target tail : Payoff ι} {root : ι → PMF Bool} {ε δ : ℝ}
    (hsource : IsQuittingRootSupportApproxNash reward target ε root)
    (hclose : ∀ player, |target player - tail player| ≤ δ) :
    IsQuittingRootSupportApproxNash reward tail (ε + δ) root := by
  intro player
  have hgap :=
    (abs_quittingRootEndpointDifference_sub_le_tail
      reward tail target root player).trans (by
        simpa only [abs_sub_comm] using hclose player)
  have hgapBounds := abs_le.mp hgap
  constructor
  · intro hquit
    have hsourceLower := (hsource player).1 hquit
    linarith
  · intro hcontinue
    have hsourceUpper := (hsource player).2 hcontinue
    linarith

omit [Nonempty ι] in
/-- A copied jump cell's post-cell pre-boundary payoff is exactly the path
continuation immediately after the jump. -/
theorem absorptionPathPreBoundaryPayoff_eq_of_copiedJumpCell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    {start stop : ℝ}
    (hstart : start ∈ Set.Icc (0 : ℝ) 1)
    (hstop : stop ∈ Set.Icc (0 : ℝ) 1)
    (hstartStop : start < stop)
    (hstopBoundary : stop ∈ partitionBoundaryTimes path)
    (hstopTotal : stop = pathTotal path.1 start)
    (htotalOne : pathTotal path.1 start < 1) :
    absorptionPathPreBoundaryPayoff reward path stop =
      absorptionPathPayoff reward path start := by
  have hleftTotal :
      pathLeftTotal path.1 stop = pathTotal path.1 start := by
    rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary,
      hstopTotal]
  have hcoordinate (terminal : {S : Finset ι // S.Nonempty}) :
      path.1.value start terminal = path.1.leftValue stop terminal :=
    path.1.value_eq_leftValue_of_lt_of_total_eq hstart hstop hstartStop
      hleftTotal terminal
  unfold absorptionPathPreBoundaryPayoff absorptionPathPayoff
  rw [if_pos hstart, if_pos htotalOne]
  funext player
  have hnumerator :
      (∑ terminal : {S : Finset ι // S.Nonempty},
        (path.1.value 1 terminal - path.1.leftValue stop terminal) *
          reward terminal player) =
        ∑ terminal : {S : Finset ι // S.Nonempty},
          (path.1.value 1 terminal - path.1.value start terminal) *
            reward terminal player := by
    apply Finset.sum_congr rfl
    intro terminal _
    rw [hcoordinate terminal]
  rw [hnumerator, hstopTotal]

/-- A literally copied jump row is support-perfect against the decoded
post-row suffix up to the uniform decoder payoff error. -/
theorem partitionCellRoot_supportApproxNash_of_copiedJump
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hperfect : IsSequentiallyPerfectAbsorptionPath reward path 0)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ)
    (hjump : partitionCut path resolution stage ∈ pathJumps path.1)
    (hstopTotal : partitionCut path resolution (stage + 1) =
      pathTotal path.1 (partitionCut path resolution stage))
    (hroot : partitionCellRoot path hpathTotal hnoTerminalJump resolution
      hresolution hcollision stage =
        absorptionPathJumpRoot path (partitionCut path resolution stage)) :
    IsQuittingRootSupportApproxNash reward
      (quittingRootSequenceTailVector reward
        (partitionCellRoots path hpathTotal hnoTerminalJump resolution
          hresolution hcollision) (stage + 1))
      (partitionDecoderPayoffErrorCoefficient reward resolution)
      (partitionCellRoot path hpathTotal hnoTerminalJump resolution
        hresolution hcollision stage) := by
  let roots := partitionCellRoots path hpathTotal hnoTerminalJump resolution
    hresolution hcollision
  let start := partitionCut path resolution stage
  let stop := partitionCut path resolution (stage + 1)
  have hresolutionOne : 1 ≤ resolution := by omega
  have hresolutionTwo : 2 ≤ resolution := by omega
  have hstartMem := partitionCut_mem_Icc path hpathTotal resolution
    hresolutionOne stage
  have hstopMem := partitionCut_mem_Icc path hpathTotal resolution
    hresolutionOne (stage + 1)
  have hstartBoundary := partitionCut_mem_partitionBoundaryTimes path
    hpathTotal resolution hresolutionOne stage
  have hstopBoundary := partitionCut_mem_partitionBoundaryTimes path
    hpathTotal resolution hresolutionOne (stage + 1)
  have hstartOne := partitionCut_lt_one path hpathTotal hnoTerminalJump
    resolution hresolutionTwo stage
  have hstartStop : start < stop := by
    rw [show stop = partitionCut path resolution (stage + 1) by rfl,
      show start = partitionCut path resolution stage by rfl,
      partitionCut_succ]
    exact lt_nextPartitionCut path hpathTotal resolution hresolutionTwo
      ⟨hstartMem.1, hstartOne⟩ hstartBoundary
  have htotalOne : pathTotal path.1 start < 1 := by
    exact hnoTerminalJump start (by simpa only [start] using hjump)
  have hpathPayoff :
      absorptionPathPreBoundaryPayoff reward path stop =
        absorptionPathPayoff reward path start :=
    absorptionPathPreBoundaryPayoff_eq_of_copiedJumpCell reward path
      (by simpa only [start] using hstartMem)
      (by simpa only [stop] using hstopMem) hstartStop
      (by simpa only [stop] using hstopBoundary)
      (by simpa only [start, stop] using hstopTotal) htotalOne
  have hsource : IsQuittingRootSupportApproxNash reward
      (absorptionPathPayoff reward path start) 0
      (absorptionPathJumpRoot path start) := by
    simpa only [start] using copiedJumpRoot_supportApproxNash reward path
      hperfect hnoTerminalJump hjump
  have hclose : ∀ player,
      |absorptionPathPayoff reward path start player -
        quittingRootSequenceTailVector reward roots (stage + 1) player| ≤
          partitionDecoderPayoffErrorCoefficient reward resolution := by
    intro player
    have htail :=
      abs_partitionCellRoots_terminalValue_sub_preBoundaryPayoff_le reward
        path hpathTotal hnoTerminalJump resolution hresolution hcollision
        (stage + 1) player
    rw [← hpathPayoff]
    simpa only [quittingRootSequenceTailVector, roots, stop, abs_sub_comm]
      using htail
  rw [hroot]
  simpa only [start, roots, zero_add] using
    supportApproxNash_of_tail_close hsource hclose


end QuittingAbsorptionPath
end GameTheory
