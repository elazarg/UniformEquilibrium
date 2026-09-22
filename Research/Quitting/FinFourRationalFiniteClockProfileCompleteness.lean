/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import MathUE.SimplexApproximation
import GameTheory.Math.Probability.Simplex
import Research.Quitting.FinFourRationalFiniteClockProfile

/-!
# Completeness of the rational Fin4 finite-clock upper search

The proof-free upper checker enumerates rational finite-clock product laws.
This module proves the missing completeness direction.  At one fixed clock,
residual-floor approximation gives rational simplex coordinates with a common
positive denominator.  Never is the residual coordinate, so a zero auxiliary
after-support coordinate stays literally zero.  Finite payoff, deviation,
cap, and exploitability formulas are continuous in these coordinates.  A
strict real upper margin therefore survives at some rational approximant,
which the executable enumeration discovers at a finite stage.

No larger clock, supplied semantic pair, or noncomputable search operator is
used.  The constructed witness is discovered by the existing explicit
`checkedCandidateAt` enumeration.
-/

noncomputable section

namespace GameTheory

open Math.ProbabilityMassFunction
open scoped BigOperators Topology

namespace FinFourRationalFiniteClockProfileCompleteness

/-- One actual real Fin4 finite-clock product profile, presented in the exact
coordinate face used by the rational checker. -/
structure RealFiniteClockProfile
    (reward : RationalFinFourRewardCode) where
  clockBound : ℕ
  clockBound_pos : 0 < clockBound
  weight : Fin 4 → FiniteClockAtom clockBound → ℝ
  weight_simplex : ∀ player,
    weight player ∈ GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound)
  auxiliary_eq_zero : ∀ player,
    weight player (finiteClockAuxAtom clockBound) = 0

namespace RealFiniteClockProfile

/-- Package finite complete stopping laws as the exact coordinate source used
by rational approximation. -/
def ofStoppingLaws {reward : RationalFinFourRewardCode}
    (clock : ℕ) (hclock : 0 < clock)
    (laws : Fin 4 → PMF (Option ℕ))
    (hlaws : ∀ player, IsFiniteClockStoppingLaw clock (laws player)) :
    RealFiniteClockProfile reward where
  clockBound := clock
  clockBound_pos := hclock
  weight := fun player ↦ finiteClockLawCoordinates clock (laws player)
  weight_simplex player :=
    finiteClockLawCoordinates_mem_stdSimplex clock (laws player)
  auxiliary_eq_zero player :=
    finiteClockLawCoordinates_aux_eq_zero clock (laws player) (hlaws player)

/-- Literal behavioral profile decoded from the real finite-clock product
coordinates. -/
def toBehaviorProfile {reward : RationalFinFourRewardCode}
    (profile : RealFiniteClockProfile reward) :
    (quittingGame reward.realReward).BehaviorProfile :=
  finiteClockDecodedProfile reward.realReward profile.clockBound
    profile.weight profile.weight_simplex

/-- The coordinate source packaged from finite stopping laws decodes back to
their canonical behavioral profile exactly. -/
theorem toBehaviorProfile_ofStoppingLaws
    (reward : RationalFinFourRewardCode)
    (clock : ℕ) (hclock : 0 < clock)
    (laws : Fin 4 → PMF (Option ℕ))
    (hlaws : ∀ player, IsFiniteClockStoppingLaw clock (laws player)) :
    (ofStoppingLaws (reward := reward) clock hclock laws hlaws).toBehaviorProfile =
      quittingStoppingLawProfile reward.realReward laws := by
  unfold toBehaviorProfile ofStoppingLaws finiteClockDecodedProfile
    finiteClockDecodedLaws
  congr 1
  funext player
  exact finiteClockDecodeLaw_coordinates clock (laws player) (hlaws player)

end RealFiniteClockProfile

variable {clockBound : ℕ}

/-- Common-denominator rational approximation of one real marginal.  Never is
the residual coordinate. -/
def rationalMass
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (level : ℕ) (player : Fin 4) (atom : FiniteClockAtom clockBound) : ℚ :=
  (Math.SimplexApproximation.residualFloorCounts none (weight player)
      (level + 1) atom : ℚ) /
    (level + 1)

/-- Proof-free rational code obtained from the residual-floor approximant.
Reducibility exposes its clock bound to dependent atom arguments. -/
@[reducible] def rationalCode
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (level : ℕ) : RationalFinFourFiniteClockProfileCode where
  clockBound := clockBound
  rows player := List.ofFn fun index : Fin (clockBound + 2) ↦
    rationalMass weight level player (finSuccEquivLast index)

@[simp] theorem rationalCode_clockBound
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ) (level : ℕ) :
    (rationalCode weight level).clockBound = clockBound := rfl

theorem atomIndex_lt (code : RationalFinFourFiniteClockProfileCode)
    (atom : FiniteClockAtom code.clockBound) :
    code.atomIndex atom < code.clockBound + 2 := by
  cases atom with
  | none => simp [RationalFinFourFiniteClockProfileCode.atomIndex]
  | some time =>
      simp [RationalFinFourFiniteClockProfileCode.atomIndex]
      omega

theorem finSuccEquivLast_atomIndex
    (code : RationalFinFourFiniteClockProfileCode)
    (atom : FiniteClockAtom code.clockBound) :
    finSuccEquivLast ⟨code.atomIndex atom, atomIndex_lt code atom⟩ = atom := by
  cases atom with
  | none =>
      rw [show ⟨code.atomIndex none, atomIndex_lt code none⟩ =
          Fin.last (code.clockBound + 1) by apply Fin.ext; rfl]
      exact finSuccEquivLast_last
  | some time =>
      rw [show ⟨code.atomIndex (some time), atomIndex_lt code (some time)⟩ =
          Fin.castSucc time by apply Fin.ext; rfl]
      exact finSuccEquivLast_castSucc time

theorem rationalCode_mass
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (level : ℕ) (player : Fin 4) (atom : FiniteClockAtom clockBound) :
    (rationalCode weight level).mass player atom =
      rationalMass weight level player atom := by
  have hindex := atomIndex_lt (rationalCode weight level) atom
  have hindex' :
      (rationalCode weight level).atomIndex atom < clockBound + 2 := by
    simpa using hindex
  unfold RationalFinFourFiniteClockProfileCode.mass
  change ((List.ofFn fun index : Fin (clockBound + 2) ↦
    rationalMass weight level player (finSuccEquivLast index))[
      (rationalCode weight level).atomIndex atom]?).getD 0 = _
  rw [List.getElem?_ofFn, dite_eq_left hindex', Option.getD_some]
  congr 1
  exact finSuccEquivLast_atomIndex (rationalCode weight level) atom

/-- Residual-floor approximation preserves a zero non-Never coordinate
exactly. -/
theorem rationalMass_eq_zero_of_ne_none
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (level : ℕ) (player : Fin 4) (atom : FiniteClockAtom clockBound)
    (hatom : atom ≠ none) (hzero : weight player atom = 0) :
    rationalMass weight level player atom = 0 := by
  unfold rationalMass
  rw [Math.SimplexApproximation.residualFloorCounts_ne hatom, hzero]
  norm_num

/-- If every non-Never source coordinate vanishes, the residual coordinate
retains unit mass exactly. -/
theorem rationalMass_none_eq_one_of_nonNever_eq_zero
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (level : ℕ) (player : Fin 4)
    (hzero : ∀ atom, atom ≠ none → weight player atom = 0) :
    rationalMass weight level player none = 1 := by
  unfold rationalMass
  rw [Math.SimplexApproximation.residualFloorCounts_self]
  have hsum :
      ∑ atom ∈ (Finset.univ.erase none : Finset (FiniteClockAtom clockBound)),
          ⌊((level + 1 : ℕ) : ℝ) * weight player atom⌋₊ = 0 := by
    apply Finset.sum_eq_zero
    intro atom hatom
    rw [hzero atom (Finset.ne_of_mem_erase hatom)]
    norm_num
  rw [hsum]
  have hden : (((level + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  simpa only [Nat.sub_zero, Nat.cast_add, Nat.cast_one] using
    (div_self hden)

/-- A pure-Never source marginal remains literally pure Never in every
residual-floor rational code. -/
theorem rationalCode_mass_eq_pureNever
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (level : ℕ) (player : Fin 4)
    (hzero : ∀ atom, atom ≠ none → weight player atom = 0)
    (atom : FiniteClockAtom clockBound) :
    (rationalCode weight level).mass player atom =
      if atom = none then 1 else 0 := by
  rw [rationalCode_mass]
  by_cases hatom : atom = none
  · subst atom
    rw [ite_eq_left rfl]
    exact rationalMass_none_eq_one_of_nonNever_eq_zero weight level player hzero
  · rw [ite_eq_right hatom]
    exact rationalMass_eq_zero_of_ne_none weight level player atom hatom
      (hzero atom hatom)

theorem rationalMass_nonneg
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (level : ℕ) (player : Fin 4) (atom : FiniteClockAtom clockBound) :
    0 ≤ rationalMass weight level player atom := by
  unfold rationalMass
  positivity

theorem rationalMass_sum_eq_one
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound))
    (level : ℕ) (player : Fin 4) :
    ∑ atom : FiniteClockAtom clockBound,
      rationalMass weight level player atom = 1 := by
  have hsumNat :
      ∑ atom : FiniteClockAtom clockBound,
          Math.SimplexApproximation.residualFloorCounts none
            (weight player) (level + 1) atom = level + 1 :=
    Math.SimplexApproximation.sum_residualFloorCounts none
      (GameTheory.Math.Probability.mem_simplexWeights.mp (hweight player)).1
        (GameTheory.Math.Probability.mem_simplexWeights.mp (hweight player)).2
        (level + 1)
  have hsumRat :
      ∑ atom : FiniteClockAtom clockBound,
          (Math.SimplexApproximation.residualFloorCounts none
            (weight player) (level + 1) atom : ℚ) = (level + 1 : ℚ) := by
    exact_mod_cast hsumNat
  simp only [rationalMass, ← Finset.sum_div, hsumRat]
  exact div_self (by positivity)

theorem rationalMass_auxiliary_eq_zero
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0)
    (level : ℕ) (player : Fin 4) :
    rationalMass weight level player (finiteClockAuxAtom clockBound) = 0 := by
  have hne : finiteClockAuxAtom clockBound ≠
      (none : FiniteClockAtom clockBound) := by
    simp [finiteClockAuxAtom]
  rw [rationalMass,
    Math.SimplexApproximation.residualFloorCounts_ne hne]
  simp [haux player]

theorem rationalCode_valid
    (hclock : 0 < clockBound)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound))
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0)
    (level : ℕ) :
    (rationalCode weight level).Valid := by
  refine ⟨hclock, fun player ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · simp
  · intro atom
    rw [rationalCode_mass]
    exact rationalMass_nonneg weight level player atom
  · rw [rationalCode_mass]
    exact rationalMass_auxiliary_eq_zero weight haux level player
  · simp only [rationalCode_mass]
    exact rationalMass_sum_eq_one weight hweight level player

theorem rationalMass_abs_sub_le
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound))
    (level : ℕ) (player : Fin 4) (atom : FiniteClockAtom clockBound) :
    |(rationalMass weight level player atom : ℝ) - weight player atom| ≤
      (Fintype.card (FiniteClockAtom clockBound) : ℝ) / (level + 1) := by
  let count := Math.SimplexApproximation.residualFloorCounts none
    (weight player) (level + 1) atom
  have hcount :
      |(count : ℝ) - (level + 1 : ℝ) * weight player atom| ≤
        (Fintype.card (FiniteClockAtom clockBound) : ℝ) :=
    by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Math.SimplexApproximation.residualFloorCounts_abs_error_le_card none
          (GameTheory.Math.Probability.mem_simplexWeights.mp (hweight player)).1
            (GameTheory.Math.Probability.mem_simplexWeights.mp (hweight player)).2
            (level + 1) atom
  have hdenom : (0 : ℝ) < level + 1 := by positivity
  change |((count : ℚ) / (level + 1) : ℚ) -
    weight player atom| ≤ _
  norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_add, Rat.cast_one, Nat.cast_add, Nat.cast_one]
  change |(count : ℝ) / (level + 1 : ℝ) - weight player atom| ≤
    (Fintype.card (FiniteClockAtom clockBound) : ℝ) /
      (level + 1 : ℝ)
  rw [show (count : ℝ) / (level + 1) - weight player atom =
      ((count : ℝ) - (level + 1 : ℝ) * weight player atom) /
        (level + 1) by field_simp,
    abs_div, abs_of_pos hdenom]
  exact div_le_div_of_nonneg_right hcount hdenom.le

theorem rationalMass_tendsto
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound))
    (player : Fin 4) (atom : FiniteClockAtom clockBound) :
    Filter.Tendsto
      (fun level ↦ (rationalMass weight level player atom : ℝ))
      Filter.atTop (nhds (weight player atom)) := by
  have hbound : Filter.Tendsto
      (fun level : ℕ ↦
        (Fintype.card (FiniteClockAtom clockBound) : ℝ) /
          (level + 1)) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (Fintype.card (FiniteClockAtom clockBound) : ℝ)
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hbound ε hε
  exact ⟨N, fun level hlevel ↦ by
    rw [Real.dist_eq]
    exact (rationalMass_abs_sub_le weight hweight level player atom).trans_lt
      (by
        have h := hN level hlevel
        rw [Real.dist_eq, sub_zero,
          abs_of_nonneg (by positivity :
            0 ≤ (Fintype.card (FiniteClockAtom clockBound) : ℝ) /
              (level + 1))] at h
        exact h)⟩

theorem rationalMass_family_tendsto
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound)) :
    Filter.Tendsto
      (fun level player atom ↦
        (rationalMass weight level player atom : ℝ))
      Filter.atTop (nhds weight) := by
  apply tendsto_pi_nhds.2
  intro player
  apply tendsto_pi_nhds.2
  exact rationalMass_tendsto weight hweight player

/-! ## Continuous finite-clock semantic formulas -/

/-- Real on-profile payoff polynomial in finite-clock marginal masses. -/
def realPayoff (reward : RationalFinFourRewardCode) (clockBound : ℕ)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (observer : Fin 4) : ℝ :=
  ∑ choices : Fin 4 → FiniteClockAtom clockBound,
    (∏ player, weight player (choices player)) *
      finiteStoppingTimesOutcomeValue reward.realReward
        (finiteClockJointStoppingTimes clockBound choices) observer

/-- Real payoff polynomial for one pure date-or-Never deviation. -/
def realDeviationPayoff (reward : RationalFinFourRewardCode)
    (clockBound : ℕ)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (player : Fin 4) (candidate : FiniteClockAtom clockBound) : ℝ :=
  ∑ choices : Fin 4 → FiniteClockAtom clockBound,
    (∏ opponent ∈ Finset.univ.erase player,
      weight opponent (choices opponent)) *
        (if choices player = candidate then
          finiteStoppingTimesOutcomeValue reward.realReward
            (finiteClockJointStoppingTimes clockBound choices) player
        else 0)

/-- Finite maximum of pure date-or-Never deviation polynomials. -/
def realCap (reward : RationalFinFourRewardCode) (clockBound : ℕ)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (player : Fin 4) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun candidate ↦
    realDeviationPayoff reward clockBound weight player candidate

/-- Finite maximum of positive player gaps in real finite-clock coordinates. -/
def realExploitability (reward : RationalFinFourRewardCode)
    (clockBound : ℕ)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun player ↦
    max 0 (realCap reward clockBound weight player -
      realPayoff reward clockBound weight player)

theorem continuous_realPayoff (reward : RationalFinFourRewardCode)
    (clockBound : ℕ) (observer : Fin 4) :
    Continuous fun weight : Fin 4 → FiniteClockAtom clockBound → ℝ ↦
      realPayoff reward clockBound weight observer := by
  unfold realPayoff
  apply continuous_finsetSum
  intro choices _
  apply Continuous.mul
  · apply continuous_finsetProd
    intro player _
    exact (continuous_apply (choices player)).comp (continuous_apply player)
  · exact continuous_const

theorem continuous_realDeviationPayoff
    (reward : RationalFinFourRewardCode) (clockBound : ℕ)
    (player : Fin 4) (candidate : FiniteClockAtom clockBound) :
    Continuous fun weight : Fin 4 → FiniteClockAtom clockBound → ℝ ↦
      realDeviationPayoff reward clockBound weight player candidate := by
  unfold realDeviationPayoff
  apply continuous_finsetSum
  intro choices _
  apply Continuous.mul
  · apply continuous_finsetProd
    intro opponent _
    exact (continuous_apply (choices opponent)).comp
      (continuous_apply opponent)
  · exact continuous_const

theorem continuous_realCap (reward : RationalFinFourRewardCode)
    (clockBound : ℕ) (player : Fin 4) :
    Continuous fun weight : Fin 4 → FiniteClockAtom clockBound → ℝ ↦
      realCap reward clockBound weight player := by
  unfold realCap
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro candidate _
  exact continuous_realDeviationPayoff reward clockBound player candidate

theorem continuous_realExploitability
    (reward : RationalFinFourRewardCode) (clockBound : ℕ) :
    Continuous fun weight : Fin 4 → FiniteClockAtom clockBound → ℝ ↦
      realExploitability reward clockBound weight := by
  unfold realExploitability
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro player _
  exact continuous_const.max
    ((continuous_realCap reward clockBound player).sub
      (continuous_realPayoff reward clockBound player))

theorem realPayoff_eq_terminalPayoff
    (reward : RationalFinFourRewardCode) (clockBound : ℕ)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound))
    (observer : Fin 4) :
    realPayoff reward clockBound weight observer =
      quittingTerminalPayoff reward.realReward
        (finiteClockDecodedProfile reward.realReward clockBound weight hweight)
        observer := by
  exact (quittingTerminalPayoff_finiteClockDecodedProfile_eq_sum
    reward.realReward clockBound weight hweight observer).symm

theorem realDeviationPayoff_eq_terminalPayoff_update
    (reward : RationalFinFourRewardCode) (clockBound : ℕ)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound))
    (player : Fin 4) (candidate : FiniteClockAtom clockBound) :
    realDeviationPayoff reward clockBound weight player candidate =
      quittingTerminalPayoff reward.realReward
        (Function.update
          (finiteClockDecodedProfile reward.realReward clockBound weight hweight)
          player
          (quittingPureTimeBehaviorStrategy reward.realReward player
            (finiteClockAtomToStoppingTime clockBound candidate))) player := by
  exact (quittingTerminalPayoff_finiteClockDecodedProfile_update_eq_sum
    reward.realReward clockBound weight hweight player candidate).symm

theorem realCap_eq_continuationBestResponseValue
    (reward : RationalFinFourRewardCode) (clockBound : ℕ)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound))
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0)
    (player : Fin 4) :
    realCap reward clockBound weight player =
      quittingContinuationBestResponseValue reward.realReward
        (finiteClockDecodedProfile reward.realReward clockBound weight hweight)
        player := by
  apply le_antisymm
  · unfold realCap
    apply Finset.sup'_le Finset.univ_nonempty
    intro candidate _
    rw [realDeviationPayoff_eq_terminalPayoff_update]
    exact quittingTerminalPayoff_update_pureTime_le_continuationBestResponseValue
      reward.realReward
      (finiteClockDecodedProfile reward.realReward clockBound weight hweight)
      player (finiteClockAtomToStoppingTime clockBound candidate)
  · obtain ⟨candidate, hcandidate⟩ :=
      exists_finiteClockCandidate_payoff_eq_continuationBestResponseValue
        reward.realReward clockBound weight hweight haux player
    rw [← hcandidate,
      ← realDeviationPayoff_eq_terminalPayoff_update]
    exact Finset.le_sup'
      (fun choice ↦ realDeviationPayoff reward clockBound weight player choice)
      (Finset.mem_univ candidate)

theorem realExploitability_eq_terminalExploitability
    (reward : RationalFinFourRewardCode) (clockBound : ℕ)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound))
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0) :
    realExploitability reward clockBound weight =
      quittingTerminalExploitability reward.realReward
        (finiteClockDecodedProfile reward.realReward clockBound weight hweight) := by
  unfold realExploitability quittingTerminalExploitability
    QuittingBoundaryHolonomy.finitePlayerMax
  congr 1
  funext player
  rw [realCap_eq_continuationBestResponseValue reward clockBound weight
    hweight haux player,
    realPayoff_eq_terminalPayoff reward clockBound weight hweight player]

/-! ## Strict-margin completeness and finite enumeration discovery -/

theorem real_rationalMass_mem_stdSimplex
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound))
    (level : ℕ) (player : Fin 4) :
    (fun atom ↦ (rationalMass weight level player atom : ℝ)) ∈
      GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound) := by
  refine GameTheory.Math.Probability.mem_simplexWeights.mpr ⟨?_, ?_⟩
  · intro atom
    norm_cast
    exact rationalMass_nonneg weight level player atom
  · change ∑ atom : FiniteClockAtom clockBound,
      (rationalMass weight level player atom : ℝ) = 1
    exact_mod_cast rationalMass_sum_eq_one weight hweight level player

theorem real_rationalMass_auxiliary_eq_zero
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0)
    (level : ℕ) (player : Fin 4) :
    (rationalMass weight level player
      (finiteClockAuxAtom clockBound) : ℝ) = 0 := by
  exact_mod_cast rationalMass_auxiliary_eq_zero weight haux level player

/-- Same-clock rational upper witness produced from a strict real finite-clock
upper margin. -/
structure RationalUpperWitness
    (reward : RationalFinFourRewardCode) (target : ℚ)
    (source : RealFiniteClockProfile reward) where
  code : RationalFinFourFiniteClockProfileCode
  same_clock : code.clockBound = source.clockBound
  verifies_upper : code.verifiesUpper reward target = true

/-- Real cast of the residual-floor approximants attached to a source. -/
def rationalApproximant {reward : RationalFinFourRewardCode}
    (source : RealFiniteClockProfile reward) (level : ℕ) :
    Fin 4 → FiniteClockAtom source.clockBound → ℝ :=
  fun player atom ↦ (rationalMass source.weight level player atom : ℝ)

theorem rationalApproximant_tendsto
    {reward : RationalFinFourRewardCode}
    (source : RealFiniteClockProfile reward) :
    Filter.Tendsto (rationalApproximant source) Filter.atTop
      (nhds source.weight) :=
  rationalMass_family_tendsto source.weight source.weight_simplex

theorem realExploitability_rationalApproximant_tendsto
    (reward : RationalFinFourRewardCode)
    (source : RealFiniteClockProfile reward) :
    Filter.Tendsto
      (fun level ↦ realExploitability reward source.clockBound
        (rationalApproximant source level)) Filter.atTop
      (nhds (realExploitability reward source.clockBound source.weight)) := by
  have hcontinuous : ContinuousAt
      (fun weight : Fin 4 → FiniteClockAtom source.clockBound → ℝ ↦
        realExploitability reward source.clockBound weight)
      source.weight :=
    (continuous_realExploitability reward source.clockBound).continuousAt
  have h := hcontinuous.tendsto.comp (rationalApproximant_tendsto source)
  simpa only [Function.comp_def] using h

theorem exists_rationalApproximant_exploitability_lt
    (reward : RationalFinFourRewardCode) (target : ℚ)
    (source : RealFiniteClockProfile reward)
    (hbelow : quittingTerminalExploitability reward.realReward
      source.toBehaviorProfile < (target : ℝ)) :
    ∃ level, realExploitability reward source.clockBound
      (rationalApproximant source level) < (target : ℝ) := by
  have hbelowFormula :
      realExploitability reward source.clockBound source.weight <
        (target : ℝ) := by
    rw [realExploitability_eq_terminalExploitability reward
      source.clockBound source.weight source.weight_simplex
      source.auxiliary_eq_zero]
    exact hbelow
  exact ((tendsto_order.1
      (realExploitability_rationalApproximant_tendsto reward source)).2
      (target : ℝ) hbelowFormula).exists

theorem rationalCode_realMass
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (level : ℕ) :
    (rationalCode weight level).realMass =
      fun player atom ↦ (rationalMass weight level player atom : ℝ) := by
  funext player atom
  change ((rationalCode weight level).mass player atom : ℝ) = _
  rw [rationalCode_mass]

theorem cast_rationalCode_exploitability_eq_realExploitability
    (reward : RationalFinFourRewardCode) (hclock : 0 < clockBound)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound))
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0)
    (level : ℕ) :
    ((rationalCode weight level).exploitability reward : ℝ) =
      realExploitability reward clockBound
        (fun player atom ↦
          (rationalMass weight level player atom : ℝ)) := by
  let code := rationalCode weight level
  have hvalid : code.Valid :=
    rationalCode_valid hclock weight hweight haux level
  have hformulaCode :
      (code.exploitability reward : ℝ) =
        realExploitability reward code.clockBound code.realMass := by
    rw [code.cast_exploitability_eq_quittingTerminalExploitability
      reward hvalid]
    symm
    simpa only [RationalFinFourFiniteClockProfileCode.toBehaviorProfile] using
      realExploitability_eq_terminalExploitability reward code.clockBound
        code.realMass (code.realMass_mem_stdSimplex hvalid)
        (code.realMass_aux_eq_zero hvalid)
  simpa only [code, rationalCode_clockBound, rationalCode_realMass] using
    hformulaCode

theorem rationalCode_verifiesUpper_of_realExploitability_lt
    (reward : RationalFinFourRewardCode) (target : ℚ)
    (hclock : 0 < clockBound)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound))
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0)
    (level : ℕ)
    (hbelow : realExploitability reward clockBound
      (fun player atom ↦
        (rationalMass weight level player atom : ℝ)) < (target : ℝ)) :
    (rationalCode weight level).verifiesUpper reward target = true := by
  have hvalid := rationalCode_valid hclock weight hweight haux level
  have hcastBelow :
      ((rationalCode weight level).exploitability reward : ℝ) <
        (target : ℝ) := by
    rw [cast_rationalCode_exploitability_eq_realExploitability reward
      hclock weight hweight haux level]
    exact hbelow
  have hratBelow :
      (rationalCode weight level).exploitability reward < target := by
    exact_mod_cast hcastBelow
  exact ((rationalCode weight level).verifiesUpper_eq_true_iff
    reward target).2 ⟨hvalid, hratBelow⟩

theorem nonempty_rationalUpperWitness
    (reward : RationalFinFourRewardCode) (target : ℚ)
    (source : RealFiniteClockProfile reward)
    (hbelow : quittingTerminalExploitability reward.realReward
      source.toBehaviorProfile < (target : ℝ)) :
    Nonempty (RationalUpperWitness reward target source) := by
  obtain ⟨level, hlevel⟩ :=
    exists_rationalApproximant_exploitability_lt reward target source hbelow
  let code := rationalCode source.weight level
  have hverified : code.verifiesUpper reward target = true :=
    rationalCode_verifiesUpper_of_realExploitability_lt reward target
      source.clockBound_pos source.weight source.weight_simplex
      source.auxiliary_eq_zero level hlevel
  exact ⟨⟨code, rfl, hverified⟩⟩

/-- Every strict real finite-clock upper witness for an arbitrary rational
reward table is found at a finite stage of the explicit rational enumeration. -/
theorem exists_checkedCandidateAt_of_realFiniteClockProfile
    (reward : RationalFinFourRewardCode) (target : ℚ)
    (source : RealFiniteClockProfile reward)
    (hbelow : quittingTerminalExploitability reward.realReward
      source.toBehaviorProfile < (target : ℝ)) :
    ∃ stage code,
      RationalFinFourFiniteClockProfileCode.checkedCandidateAt
          reward target stage = some code ∧
        code.clockBound = source.clockBound := by
  obtain ⟨witness⟩ :=
    nonempty_rationalUpperWitness reward target source hbelow
  obtain ⟨stage, hstage⟩ :=
    RationalFinFourFiniteClockProfileCode.exists_checkedCandidateAt_of_verifiesUpper
      reward target witness.code witness.verifies_upper
  exact ⟨stage, witness.code, hstage, witness.same_clock⟩

/-- Rational discovery preserves a prescribed pure-Never marginal of the real
finite-clock source exactly, rather than only in the limit. -/
theorem exists_checkedCandidateAt_of_realFiniteClockProfile_preserving_pureNever
    (reward : RationalFinFourRewardCode) (target : ℚ)
    (source : RealFiniteClockProfile reward)
    (hbelow : quittingTerminalExploitability reward.realReward
      source.toBehaviorProfile < (target : ℝ))
    (player : Fin 4)
    (hpureNever : ∀ atom, atom ≠ none → source.weight player atom = 0) :
    ∃ stage code,
      RationalFinFourFiniteClockProfileCode.checkedCandidateAt
          reward target stage = some code ∧
        code.clockBound = source.clockBound ∧
        ∀ atom, code.mass player atom = if atom = none then 1 else 0 := by
  obtain ⟨level, hlevel⟩ :=
    exists_rationalApproximant_exploitability_lt reward target source hbelow
  let code := rationalCode source.weight level
  have hverified : code.verifiesUpper reward target = true :=
    rationalCode_verifiesUpper_of_realExploitability_lt reward target
      source.clockBound_pos source.weight source.weight_simplex
      source.auxiliary_eq_zero level hlevel
  obtain ⟨stage, hstage⟩ :=
    RationalFinFourFiniteClockProfileCode.exists_checkedCandidateAt_of_verifiesUpper
      reward target code hverified
  refine ⟨stage, code, hstage, rfl, ?_⟩
  intro atom
  exact rationalCode_mass_eq_pureNever source.weight level player
    hpureNever atom

theorem target_pos_of_realFiniteClockProfile
    (reward : RationalFinFourRewardCode) (target : ℚ)
    (source : RealFiniteClockProfile reward)
    (hbelow : quittingTerminalExploitability reward.realReward
      source.toBehaviorProfile < (target : ℝ)) :
    0 < target := by
  exact_mod_cast
    (lt_of_le_of_lt
      (quittingTerminalExploitability_nonneg reward.realReward
        source.toBehaviorProfile) hbelow)

/-- Existing finite-clock stopping-law witnesses for an arbitrary rational
reward table feed the same-clock rational upper enumeration directly. Thus the
coordinate presentation above does not restrict which valid finite-clock
product profiles are covered. -/
theorem exists_checkedCandidateAt_of_finiteClockStoppingLaws
    (reward : RationalFinFourRewardCode) (target : ℚ)
    (clock : ℕ) (hclock : 0 < clock)
    (laws : Fin 4 → PMF (Option ℕ))
    (hlaws : ∀ player, IsFiniteClockStoppingLaw clock (laws player))
    (hbelow : quittingTerminalExploitability reward.realReward
      (quittingStoppingLawProfile reward.realReward laws) < (target : ℝ)) :
    ∃ stage code,
      RationalFinFourFiniteClockProfileCode.checkedCandidateAt
          reward target stage = some code ∧
        code.clockBound = clock := by
  let source := RealFiniteClockProfile.ofStoppingLaws
    (reward := reward) clock hclock laws hlaws
  have hsourceProfile : source.toBehaviorProfile =
      quittingStoppingLawProfile reward.realReward laws :=
    RealFiniteClockProfile.toBehaviorProfile_ofStoppingLaws
      reward clock hclock laws hlaws
  have hbelowSource :
      quittingTerminalExploitability reward.realReward
        source.toBehaviorProfile < (target : ℝ) := by
    rw [hsourceProfile]
    exact hbelow
  simpa only [source, RealFiniteClockProfile.ofStoppingLaws] using
    exists_checkedCandidateAt_of_realFiniteClockProfile
      reward target source hbelowSource

/-- Same-clock rational discovery preserves any finite-clock source player
whose complete stopping law is prescribed to be deterministic Never. -/
theorem exists_checkedCandidateAt_of_finiteClockStoppingLaws_preserving_pureNever
    (reward : RationalFinFourRewardCode) (target : ℚ)
    (clock : ℕ) (hclock : 0 < clock)
    (laws : Fin 4 → PMF (Option ℕ))
    (hlaws : ∀ player, IsFiniteClockStoppingLaw clock (laws player))
    (hbelow : quittingTerminalExploitability reward.realReward
      (quittingStoppingLawProfile reward.realReward laws) < (target : ℝ))
    (player : Fin 4) (hpureNever : laws player = PMF.pure none) :
    ∃ stage code,
      RationalFinFourFiniteClockProfileCode.checkedCandidateAt
          reward target stage = some code ∧
        code.clockBound = clock ∧
        ∀ atom, code.mass player atom = if atom = none then 1 else 0 := by
  let source := RealFiniteClockProfile.ofStoppingLaws
    (reward := reward) clock hclock laws hlaws
  have hsourceProfile : source.toBehaviorProfile =
      quittingStoppingLawProfile reward.realReward laws :=
    RealFiniteClockProfile.toBehaviorProfile_ofStoppingLaws
      reward clock hclock laws hlaws
  have hbelowSource :
      quittingTerminalExploitability reward.realReward
        source.toBehaviorProfile < (target : ℝ) := by
    rw [hsourceProfile]
    exact hbelow
  have hsourcePureNever : ∀ atom, atom ≠ none →
      source.weight player atom = 0 := by
    change ∀ atom : FiniteClockAtom clock, atom ≠ none →
      finiteClockLawCoordinates clock (laws player) atom = 0
    intro atom hatom
    rw [hpureNever]
    unfold finiteClockLawCoordinates finiteClockEncodeLaw toVector
    rw [PMF.pure_map]
    rw [stoppingTimeToFiniteClockAtom_none]
    rw [PMF.pure_apply_of_ne none atom hatom]
    rfl
  simpa only [source, RealFiniteClockProfile.ofStoppingLaws] using
    exists_checkedCandidateAt_of_realFiniteClockProfile_preserving_pureNever
      reward target source hbelowSource player hsourcePureNever

end FinFourRationalFiniteClockProfileCompleteness

end GameTheory
