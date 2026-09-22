/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourRationalFiniteClockChildUpper
import Research.Quitting.FinFourRationalFiniteClockProfileCompleteness

/-!
# Completeness of the rational Fin4 child-only upper search

The child-only checker masks one deterministic-Never owner and maximizes the
three surviving exact cap-minus-payoff coordinates. This module applies the
existing residual-floor approximation to that finite maximum. The rational
approximants use the same clock as the real source and retain the owner's
pure-Never marginal exactly at every denominator.

This first layer is normalization-free and formula-level. It neither changes
the existing raw-code enumeration nor introduces a separate Fin3 payload.
-/

noncomputable section

namespace GameTheory

open Math.ProbabilityMassFunction
open scoped Topology

namespace FinFourRationalFiniteClockChildUpperCompleteness

open FinFourRationalFiniteClockProfileCompleteness

variable {clockBound : ℕ}

/-- Real finite-clock version of the masked survivor maximum checked by the
exact rational child-only search. -/
def realChildExploitability (reward : RationalFinFourRewardCode)
    (clockBound : ℕ) (owner : Fin 4)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun player =>
    if player = owner then 0 else
      max 0
        (realCap reward clockBound weight player -
          realPayoff reward clockBound weight player)

theorem continuous_realChildExploitability
    (reward : RationalFinFourRewardCode) (clockBound : ℕ) (owner : Fin 4) :
    Continuous fun weight : Fin 4 → FiniteClockAtom clockBound → ℝ =>
      realChildExploitability reward clockBound owner weight := by
  unfold realChildExploitability
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro player _
  by_cases hplayer : player = owner
  · simpa only [ite_eq_left hplayer] using
      (continuous_const : Continuous fun _ :
        Fin 4 → FiniteClockAtom clockBound → ℝ => (0 : ℝ))
  · simpa only [ite_eq_right hplayer, Pi.sub_apply, Pi.zero_apply] using
      continuous_const.max
        ((continuous_realCap reward clockBound player).sub
          (continuous_realPayoff reward clockBound player))

/-- The masked real survivor maximum converges along the existing
residual-floor rational approximants. -/
theorem realChildExploitability_rationalApproximant_tendsto
    (reward : RationalFinFourRewardCode) (owner : Fin 4)
    (source : RealFiniteClockProfile reward) :
    Filter.Tendsto
      (fun level => realChildExploitability reward source.clockBound owner
        (rationalApproximant source level)) Filter.atTop
      (nhds (realChildExploitability reward source.clockBound owner
        source.weight)) := by
  have hcontinuous : ContinuousAt
      (fun weight : Fin 4 → FiniteClockAtom source.clockBound → ℝ =>
        realChildExploitability reward source.clockBound owner weight)
      source.weight :=
    (continuous_realChildExploitability reward source.clockBound owner).continuousAt
  have h := hcontinuous.tendsto.comp (rationalApproximant_tendsto source)
  simpa only [Function.comp_def] using h

theorem exists_rationalApproximant_childExploitability_lt
    (reward : RationalFinFourRewardCode) (owner : Fin 4) (target : ℚ)
    (source : RealFiniteClockProfile reward)
    (hbelow : realChildExploitability reward source.clockBound owner
      source.weight < (target : ℝ)) :
    ∃ level, realChildExploitability reward source.clockBound owner
      (rationalApproximant source level) < (target : ℝ) := by
  exact ((tendsto_order.1
      (realChildExploitability_rationalApproximant_tendsto
        reward owner source)).2 (target : ℝ) hbelow).exists

/-- Casting an existing residual-floor code gives exactly the corresponding
real masked survivor maximum. -/
theorem cast_rationalCode_childExploitability_eq_realChildExploitability
    (reward : RationalFinFourRewardCode) (hclock : 0 < clockBound)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈
        GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound))
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0)
    (owner : Fin 4) (level : ℕ) :
    ((rationalCode weight level).childExploitability reward owner : ℝ) =
      realChildExploitability reward clockBound owner
        (fun player atom =>
          (rationalMass weight level player atom : ℝ)) := by
  let code := rationalCode weight level
  have hvalid : code.Valid :=
    rationalCode_valid hclock weight hweight haux level
  have hgap (player : Fin 4) :
      (code.playerGap reward player : ℝ) =
        max 0
          (realCap reward code.clockBound code.realMass player -
            realPayoff reward code.clockBound code.realMass player) := by
    unfold RationalFinFourFiniteClockProfileCode.playerGap
    rw [code.cast_playerGap_eq_terminalPlayerGap reward hvalid player,
      realCap_eq_continuationBestResponseValue reward code.clockBound
        code.realMass (code.realMass_mem_stdSimplex hvalid)
        (code.realMass_aux_eq_zero hvalid) player,
      realPayoff_eq_terminalPayoff reward code.clockBound code.realMass
        (code.realMass_mem_stdSimplex hvalid) player]
    rfl
  have hformula : (code.childExploitability reward owner : ℝ) =
      realChildExploitability reward code.clockBound owner code.realMass := by
    unfold RationalFinFourFiniteClockProfileCode.childExploitability
      realChildExploitability
    apply le_antisymm
    · obtain ⟨player, -, hplayer⟩ :=
        Finset.exists_mem_eq_sup' Finset.univ_nonempty fun player : Fin 4 =>
          if player = owner then 0 else code.playerGap reward player
      rw [hplayer]
      by_cases howner : player = owner
      · subst player
        have hleft :
            (if owner = owner then (0 : ℚ) else code.playerGap reward owner) = 0 :=
          ite_eq_left rfl
        rw [hleft]
        simp only [Rat.cast_zero]
        have hzero := Finset.le_sup'
          (fun candidate : Fin 4 =>
            if candidate = owner then 0 else
              max 0
                (realCap reward code.clockBound code.realMass candidate -
                  realPayoff reward code.clockBound code.realMass candidate))
          (Finset.mem_univ owner)
        simpa only [ite_eq_left rfl, ite_true] using hzero
      · rw [ite_eq_right howner, hgap player]
        simpa only [ite_eq_right howner] using
          (Finset.le_sup'
            (fun candidate : Fin 4 =>
              if candidate = owner then 0 else
                max 0
                  (realCap reward code.clockBound code.realMass candidate -
                    realPayoff reward code.clockBound code.realMass candidate))
            (Finset.mem_univ player))
    · apply Finset.sup'_le Finset.univ_nonempty
      intro player _
      by_cases howner : player = owner
      · subst player
        rw [ite_eq_left rfl]
        have hzero : (0 : ℚ) ≤ code.childExploitability reward owner := by
          unfold RationalFinFourFiniteClockProfileCode.childExploitability
          have hle := Finset.le_sup'
            (fun candidate : Fin 4 =>
              (if candidate = owner then 0 else
                code.playerGap reward candidate : ℚ))
            (Finset.mem_univ owner)
          simpa only [ite_eq_left rfl, ite_true] using hle
        exact_mod_cast hzero
      · rw [ite_eq_right howner, ← hgap player]
        exact_mod_cast code.playerGap_le_childExploitability
          reward owner player howner
  simpa only [code, rationalCode_clockBound, rationalCode_realMass] using hformula

/-- One existing residual-floor approximant passes the exact child checker
whenever its real masked maximum is below the rational threshold and the real
source owner is pure Never. -/
theorem rationalCode_verifiesChildUpper_of_realChildExploitability_lt
    (reward : RationalFinFourRewardCode) (target : ℚ)
    (hclock : 0 < clockBound)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈
        GameTheory.Math.Probability.simplexWeights (FiniteClockAtom clockBound))
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0)
    (owner : Fin 4)
    (hpureNever : ∀ atom, atom ≠ none → weight owner atom = 0)
    (level : ℕ)
    (hbelow : realChildExploitability reward clockBound owner
      (fun player atom =>
        (rationalMass weight level player atom : ℝ)) < (target : ℝ)) :
    (rationalCode weight level).verifiesChildUpper
      reward owner target = true := by
  have hvalid := rationalCode_valid hclock weight hweight haux level
  have hpure : (rationalCode weight level).PureNeverAt owner := by
    intro atom hatom
    rw [rationalCode_mass_eq_pureNever weight level owner hpureNever atom,
      ite_eq_right hatom]
  have hcastBelow :
      ((rationalCode weight level).childExploitability reward owner : ℝ) <
        (target : ℝ) := by
    rw [cast_rationalCode_childExploitability_eq_realChildExploitability
      reward hclock weight hweight haux owner level]
    exact hbelow
  have hrationalBelow :
      (rationalCode weight level).childExploitability reward owner < target := by
    exact_mod_cast hcastBelow
  exact ((rationalCode weight level).verifiesChildUpper_eq_true_iff
    reward owner target).2 ⟨hvalid, hpure, hrationalBelow⟩

/-- Every strict real child-only upper witness with a pure-Never owner is found
at a finite stage of the existing raw-code enumeration, with the same clock
and the owner marginal still literally pure Never. -/
theorem exists_checkedChildCandidateAt_of_realFiniteClockProfile
    (reward : RationalFinFourRewardCode) (owner : Fin 4) (target : ℚ)
    (source : RealFiniteClockProfile reward)
    (hpureNever : ∀ atom, atom ≠ none → source.weight owner atom = 0)
    (hbelow : realChildExploitability reward source.clockBound owner
      source.weight < (target : ℝ)) :
    ∃ stage code,
      RationalFinFourFiniteClockProfileCode.checkedChildCandidateAt
          reward owner target stage = some code ∧
        code.clockBound = source.clockBound ∧
        ∀ atom, code.mass owner atom = if atom = none then 1 else 0 := by
  obtain ⟨level, hlevel⟩ :=
    exists_rationalApproximant_childExploitability_lt
      reward owner target source hbelow
  let code := rationalCode source.weight level
  have hverified : code.verifiesChildUpper reward owner target = true :=
    rationalCode_verifiesChildUpper_of_realChildExploitability_lt
      reward target source.clockBound_pos source.weight source.weight_simplex
      source.auxiliary_eq_zero owner hpureNever level hlevel
  obtain ⟨stage, hstage⟩ :=
    code.exists_checkedChildCandidateAt_of_verifiesChildUpper
      reward owner target hverified
  refine ⟨stage, code, hstage, rfl, ?_⟩
  intro atom
  exact rationalCode_mass_eq_pureNever source.weight level owner
    hpureNever atom

end FinFourRationalFiniteClockChildUpperCompleteness

end GameTheory
