/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.FiniteClockCoordinates
import Research.Quitting.EscapeAwareQuantileClockHierarchy
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Exact polynomial presentation of finite-clock semantic centers

This file presents the literal finite-clock terminal semantic center by a
finite family of multivariate polynomial equalities and inequalities.
Variables record marginal masses, prescribed payoffs, and unrestricted
behavioral caps.  The cap graph lists the finitely many payoff-distinct pure
deviations `0, ..., clockBound` and `Never`: inequalities make the cap an
upper bound, while one product equation forces a tight candidate.

The coefficient ring is abstract.  In particular, taking `R = Rat` and
`coeff = Rat.castHom Real` gives polynomials with rational coefficients whose
real feasible semantic image is proved exactly equal to the literal
finite-clock reachable set.  The proof retains independent marginal-product
provenance and the separate Never atom, and uses checked pure-time extremality
only to identify the finite maximum with the unrestricted behavioral cap.

Mathlib currently supplies polynomial syntax but no semialgebraic-set or
real-closed-field quantifier-elimination interface used here.  Accordingly,
this file proves exact soundness and completeness of the finite polynomial
system, but does not assert CAD decidability or a checked external certificate
verifier.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def finiteStoppingTimesOutcomeValue
    {R : Type*} [Zero R]
    (reward : {S : Finset ι // S.Nonempty} → ι → R)
    (choices : ι → Option ℕ) (observer : ι) : R := by
  classical
  exact if hfinite : ∃ time, ∃ player, choices player = some time then
      let first := Nat.find hfinite
      reward ⟨Finset.univ.filter fun player => choices player = some first,
        by
          obtain ⟨player, hplayer⟩ := Nat.find_spec hfinite
          exact ⟨player, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hplayer⟩⟩⟩
        observer
    else 0

theorem finiteStoppingTimesOutcomeValue_eq_terminalPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (choices : ι → Option ℕ) (observer : ι) :
    finiteStoppingTimesOutcomeValue reward choices observer =
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) observer := by
  classical
  by_cases hfinite : ∃ time, ∃ player, choices player = some time
  · let first := Nat.find hfinite
    obtain ⟨anchor, hanchor⟩ := Nat.find_spec hfinite
    have hbefore : ∀ time < first, ∀ player,
        choices player ≠ some time := by
      intro time htime player heq
      exact Nat.not_le_of_lt htime
        (Nat.find_min' hfinite ⟨player, heq⟩)
    have hcoalition :
        (Finset.univ.filter fun player => choices player = some first).Nonempty :=
      ⟨anchor, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hanchor⟩⟩
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
      reward choices observer first hcoalition hbefore]
    rw [QuittingSureSetOwnerRepair.quittingSetReward_of_nonempty
      reward hcoalition observer]
    simp [finiteStoppingTimesOutcomeValue, hfinite, first]
  · have hallNever : ∀ player, choices player = none := by
      intro player
      cases hchoice : choices player with
      | none => rfl
      | some time => exact (hfinite ⟨time, player, hchoice⟩).elim
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_zero_of_allNever
      reward choices hallNever observer]
    simp [finiteStoppingTimesOutcomeValue, hfinite]

inductive FiniteClockCenterVar (ι : Type) (clockBound : ℕ) : Type where
  | mass (player : ι)
      (atom : FiniteClockAtom clockBound) : FiniteClockCenterVar ι clockBound
  | payoff (player : ι) : FiniteClockCenterVar ι clockBound
  | cap (player : ι) : FiniteClockCenterVar ι clockBound
deriving DecidableEq

def finiteClockJointStoppingTimes (clockBound : ℕ)
    (choices : ι → FiniteClockAtom clockBound) : ι → Option ℕ :=
  fun player => finiteClockAtomToStoppingTime clockBound (choices player)

def finiteClockSimplexSumPoly
    {R : Type*} [CommRing R] (clockBound : ℕ) (player : ι) :
    MvPolynomial (FiniteClockCenterVar ι clockBound) R :=
  (∑ atom : FiniteClockAtom clockBound,
    MvPolynomial.X (FiniteClockCenterVar.mass player atom)) -
      MvPolynomial.C 1

def finiteClockMassPoly
    {R : Type*} [CommRing R] (clockBound : ℕ) (player : ι)
    (atom : FiniteClockAtom clockBound) :
    MvPolynomial (FiniteClockCenterVar ι clockBound) R :=
  MvPolynomial.X (FiniteClockCenterVar.mass player atom)

def finiteClockOnProfilePayoffPoly
    {R : Type*} [CommRing R]
    (reward : {S : Finset ι // S.Nonempty} → ι → R)
    (clockBound : ℕ) (observer : ι) :
    MvPolynomial (FiniteClockCenterVar ι clockBound) R :=
  ∑ choices : ι → FiniteClockAtom clockBound,
    (∏ player,
      MvPolynomial.X (FiniteClockCenterVar.mass player (choices player))) *
        MvPolynomial.C (finiteStoppingTimesOutcomeValue reward
          (finiteClockJointStoppingTimes clockBound choices) observer)

def finiteClockDeviationPayoffPoly
    {R : Type*} [CommRing R]
    (reward : {S : Finset ι // S.Nonempty} → ι → R)
    (clockBound : ℕ) (player : ι)
    (candidate : FiniteClockAtom clockBound) :
    MvPolynomial (FiniteClockCenterVar ι clockBound) R :=
  ∑ choices : ι → FiniteClockAtom clockBound,
    (∏ opponent ∈ Finset.univ.erase player,
      MvPolynomial.X (FiniteClockCenterVar.mass opponent (choices opponent))) *
        MvPolynomial.C (if choices player = candidate then
          finiteStoppingTimesOutcomeValue reward
            (finiteClockJointStoppingTimes clockBound choices) player
          else 0)

def finiteClockPayoffConsistencyPoly
    {R : Type*} [CommRing R]
    (reward : {S : Finset ι // S.Nonempty} → ι → R)
    (clockBound : ℕ) (player : ι) :
    MvPolynomial (FiniteClockCenterVar ι clockBound) R :=
  MvPolynomial.X (FiniteClockCenterVar.payoff player) -
    finiteClockOnProfilePayoffPoly reward clockBound player

def finiteClockCapUpperPoly
    {R : Type*} [CommRing R]
    (reward : {S : Finset ι // S.Nonempty} → ι → R)
    (clockBound : ℕ) (player : ι)
    (candidate : FiniteClockAtom clockBound) :
    MvPolynomial (FiniteClockCenterVar ι clockBound) R :=
  MvPolynomial.X (FiniteClockCenterVar.cap player) -
    finiteClockDeviationPayoffPoly reward clockBound player candidate

def finiteClockCapTightPoly
    {R : Type*} [CommRing R]
    (reward : {S : Finset ι // S.Nonempty} → ι → R)
    (clockBound : ℕ) (player : ι) :
    MvPolynomial (FiniteClockCenterVar ι clockBound) R :=
  ∏ candidate : FiniteClockAtom clockBound,
    finiteClockCapUpperPoly reward clockBound player candidate

def SatisfiesFiniteClockCenterPolynomials
    {R S : Type*} [CommRing R] [Field S] [LinearOrder S]
    [IsStrictOrderedRing S]
    (coeff : R →+* S)
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ)
    (assign : FiniteClockCenterVar ι clockBound → S) : Prop :=
  (∀ player, MvPolynomial.eval₂ coeff assign
      (finiteClockSimplexSumPoly clockBound player) = 0) ∧
    (∀ player atom, 0 ≤ MvPolynomial.eval₂ coeff assign
      (finiteClockMassPoly clockBound player atom)) ∧
    (∀ player, MvPolynomial.eval₂ coeff assign
      (finiteClockMassPoly clockBound player
        (finiteClockAuxAtom clockBound)) = 0) ∧
    (∀ player, MvPolynomial.eval₂ coeff assign
      (finiteClockPayoffConsistencyPoly reward clockBound player) = 0) ∧
    (∀ player candidate, 0 ≤ MvPolynomial.eval₂ coeff assign
      (finiteClockCapUpperPoly reward clockBound player candidate)) ∧
    (∀ player, MvPolynomial.eval₂ coeff assign
      (finiteClockCapTightPoly reward clockBound player) = 0)

def finiteClockCenterWeight
    {S : Type*} (clockBound : ℕ)
    (assign : FiniteClockCenterVar ι clockBound → S)
    (player : ι) (atom : FiniteClockAtom clockBound) : S :=
  assign (FiniteClockCenterVar.mass player atom)

def finiteClockCenterPair
    {S : Type*} (clockBound : ℕ)
    (assign : FiniteClockCenterVar ι clockBound → S) :
    (ι → S) × (ι → S) :=
  (⟨fun player => assign (FiniteClockCenterVar.payoff player),
    fun player => assign (FiniteClockCenterVar.cap player)⟩)

omit [DecidableEq ι] in
theorem map_finiteStoppingTimesOutcomeValue
    {R S : Type*} [CommRing R] [CommRing S] (coeff : R →+* S)
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (choices : ι → Option ℕ) (observer : ι) :
    coeff (finiteStoppingTimesOutcomeValue reward choices observer) =
      finiteStoppingTimesOutcomeValue
        (fun terminal player => coeff (reward terminal player))
        choices observer := by
  classical
  simp only [finiteStoppingTimesOutcomeValue]
  split <;> simp

omit [Fintype ι] [DecidableEq ι] in
theorem eval₂_finiteClockSimplexSumPoly
    {R S : Type*} [CommRing R] [CommRing S] (coeff : R →+* S)
    (clockBound : ℕ)
    (assign : FiniteClockCenterVar ι clockBound → S)
    (player : ι) :
    MvPolynomial.eval₂ coeff assign
        (finiteClockSimplexSumPoly clockBound player) =
      (∑ atom : FiniteClockAtom clockBound,
        assign (FiniteClockCenterVar.mass player atom)) - 1 := by
  simp [finiteClockSimplexSumPoly]

theorem eval₂_finiteClockOnProfilePayoffPoly
    {R S : Type*} [CommRing R] [CommRing S] (coeff : R →+* S)
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ)
    (assign : FiniteClockCenterVar ι clockBound → S)
    (observer : ι) :
    MvPolynomial.eval₂ coeff assign
        (finiteClockOnProfilePayoffPoly reward clockBound observer) =
      ∑ choices : ι → FiniteClockAtom clockBound,
        (∏ player,
          assign (FiniteClockCenterVar.mass player (choices player))) *
          finiteStoppingTimesOutcomeValue
            (fun terminal player => coeff (reward terminal player))
            (finiteClockJointStoppingTimes clockBound choices) observer := by
  classical
  simp only [finiteClockOnProfilePayoffPoly, MvPolynomial.eval₂_sum]
  refine Finset.sum_congr rfl fun choices _ => ?_
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod,
    MvPolynomial.eval₂_C]
  simp only [MvPolynomial.eval₂_X]
  rw [map_finiteStoppingTimesOutcomeValue coeff]

theorem eval₂_finiteClockDeviationPayoffPoly
    {R S : Type*} [CommRing R] [CommRing S] (coeff : R →+* S)
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ)
    (assign : FiniteClockCenterVar ι clockBound → S)
    (player : ι) (candidate : FiniteClockAtom clockBound) :
    MvPolynomial.eval₂ coeff assign
        (finiteClockDeviationPayoffPoly reward clockBound player candidate) =
      ∑ choices : ι → FiniteClockAtom clockBound,
        (∏ opponent ∈ Finset.univ.erase player,
          assign (FiniteClockCenterVar.mass opponent (choices opponent))) *
          (if choices player = candidate then
            finiteStoppingTimesOutcomeValue
              (fun terminal who => coeff (reward terminal who))
              (finiteClockJointStoppingTimes clockBound choices) player
          else 0) := by
  classical
  simp only [finiteClockDeviationPayoffPoly, MvPolynomial.eval₂_sum]
  refine Finset.sum_congr rfl fun choices _ => ?_
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod,
    MvPolynomial.eval₂_C]
  simp only [MvPolynomial.eval₂_X]
  split_ifs <;> simp [map_finiteStoppingTimesOutcomeValue]

def finiteClockAtomLaws (clockBound : ℕ)
    (weight : ι → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound)) :
    ι → PMF (FiniteClockAtom clockBound) :=
  fun player => ofVector (weight player) (hweight player)

def finiteClockDecodedLaws (clockBound : ℕ)
    (weight : ι → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound)) :
    ι → PMF (Option ℕ) :=
  fun player => finiteClockDecodeLaw clockBound
    (weight player) (hweight player)

def finiteClockDecodedProfile
    (reward : {T : Finset ι // T.Nonempty} → Payoff ι)
    (clockBound : ℕ)
    (weight : ι → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound)) :
    (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawProfile reward
    (finiteClockDecodedLaws clockBound weight hweight)

theorem quittingTerminalPayoff_finiteClockDecodedProfile_eq_sum
    (reward : {T : Finset ι // T.Nonempty} → Payoff ι)
    (clockBound : ℕ)
    (weight : ι → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound))
    (observer : ι) :
    quittingTerminalPayoff reward
        (finiteClockDecodedProfile reward clockBound weight hweight) observer =
      ∑ choices : ι → FiniteClockAtom clockBound,
        (∏ player, weight player (choices player)) *
          finiteStoppingTimesOutcomeValue reward
            (finiteClockJointStoppingTimes clockBound choices) observer := by
  let atomLaws := finiteClockAtomLaws clockBound weight hweight
  let decodedLaws := finiteClockDecodedLaws clockBound weight hweight
  rw [finiteClockDecodedProfile,
    quittingTerminalPayoff_stoppingLawProfile_eq_expect]
  have hproduct : pmfPi decodedLaws =
      (pmfPi atomLaws).map
        (finiteClockJointStoppingTimes clockBound) := by
    change pmfPi (fun player =>
        (atomLaws player).map (finiteClockAtomToStoppingTime clockBound)) = _
    exact (pmfPi_push_coordwise atomLaws
      (fun _ => finiteClockAtomToStoppingTime clockBound)).symm
  rw [hproduct]
  let value : (ι → Option ℕ) → ℝ := fun choices =>
    quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) observer
  have hexpect : Math.Probability.expect
        ((pmfPi atomLaws).map
          (finiteClockJointStoppingTimes clockBound)) value =
      Math.Probability.expect (pmfPi atomLaws) fun choices =>
        value (finiteClockJointStoppingTimes clockBound choices) := by
    simpa [Math.ProbabilityMassFunction.pushforward] using
      expect_pushforward_of_bounded
        (pmfPi atomLaws) (finiteClockJointStoppingTimes clockBound) value
        (fun choices =>
          abs_quittingTerminalPayoff_le_quittingRewardBound
            reward _ observer)
  change Math.Probability.expect
      ((pmfPi atomLaws).map
        (finiteClockJointStoppingTimes clockBound)) value = _
  rw [hexpect, Math.Probability.expect_eq_sum]
  refine Finset.sum_congr rfl fun choices _ => ?_
  rw [pmfPi_apply, ENNReal.toReal_prod]
  simp only [atomLaws, finiteClockAtomLaws, ofVector_toReal]
  rw [finiteStoppingTimesOutcomeValue_eq_terminalPayoff]

theorem quittingTerminalPayoff_finiteClockDecodedProfile_update_eq_sum
    (reward : {T : Finset ι // T.Nonempty} → Payoff ι)
    (clockBound : ℕ)
    (weight : ι → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound))
    (player : ι) (candidate : FiniteClockAtom clockBound) :
    quittingTerminalPayoff reward
        (Function.update
          (finiteClockDecodedProfile reward clockBound weight hweight) player
          (quittingPureTimeBehaviorStrategy reward player
            (finiteClockAtomToStoppingTime clockBound candidate))) player =
      ∑ choices : ι → FiniteClockAtom clockBound,
        (∏ opponent ∈ Finset.univ.erase player,
          weight opponent (choices opponent)) *
          (if choices player = candidate then
            finiteStoppingTimesOutcomeValue reward
              (finiteClockJointStoppingTimes clockBound choices) player
          else 0) := by
  let atomLaws := finiteClockAtomLaws clockBound weight hweight
  let decodedLaws := finiteClockDecodedLaws clockBound weight hweight
  let atomModified := Function.update atomLaws player (PMF.pure candidate)
  let decodedModified := quittingPureDeviationStoppingLaws decodedLaws player
    (finiteClockAtomToStoppingTime clockBound candidate)
  rw [finiteClockDecodedProfile,
    quittingTerminalPayoff_update_stoppingLawProfile_pureTime_eq_expect]
  have hfamily : decodedModified = fun who =>
      (atomModified who).map (finiteClockAtomToStoppingTime clockBound) := by
    funext who
    by_cases hwho : who = player
    · subst who
      simp only [decodedModified, quittingPureDeviationStoppingLaws,
        atomModified, Function.update_self, if_pos]
      exact (PMF.pure_map
        (finiteClockAtomToStoppingTime clockBound) candidate).symm
    · simp [decodedModified, quittingPureDeviationStoppingLaws,
        atomModified, decodedLaws, finiteClockDecodedLaws,
        finiteClockDecodeLaw, atomLaws, finiteClockAtomLaws, hwho]
  have hproduct : pmfPi decodedModified =
      (pmfPi atomModified).map
        (finiteClockJointStoppingTimes clockBound) := by
    rw [hfamily]
    exact (pmfPi_push_coordwise atomModified
      (fun _ => finiteClockAtomToStoppingTime clockBound)).symm
  change Math.Probability.expect (pmfPi decodedModified) _ = _
  rw [hproduct]
  let value : (ι → Option ℕ) → ℝ := fun choices =>
    quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) player
  have hexpect : Math.Probability.expect
        ((pmfPi atomModified).map
          (finiteClockJointStoppingTimes clockBound)) value =
      Math.Probability.expect (pmfPi atomModified) fun choices =>
        value (finiteClockJointStoppingTimes clockBound choices) := by
    simpa [Math.ProbabilityMassFunction.pushforward] using
      expect_pushforward_of_bounded
        (pmfPi atomModified) (finiteClockJointStoppingTimes clockBound) value
        (fun choices =>
          abs_quittingTerminalPayoff_le_quittingRewardBound reward _ player)
  change Math.Probability.expect
      ((pmfPi atomModified).map
        (finiteClockJointStoppingTimes clockBound)) value = _
  rw [hexpect, Math.Probability.expect_eq_sum]
  refine Finset.sum_congr rfl fun choices _ => ?_
  rw [pmfPi_apply_update_family, ENNReal.toReal_mul,
    ENNReal.toReal_prod]
  simp only [PMF.pure_apply, atomLaws, finiteClockAtomLaws,
    ofVector_toReal]
  rw [finiteStoppingTimesOutcomeValue_eq_terminalPayoff]
  by_cases hchoice : choices player = candidate
  · simp [hchoice, value]
  · simp [hchoice]

def replaceStoppingTimeCoordinate (player : ι) (target : Option ℕ)
    (choices : ι → Option ℕ) : ι → Option ℕ :=
  Function.update choices player target

theorem pmfPi_quittingPureDeviation_eq_map
    (laws : ι → PMF (Option ℕ)) (player : ι)
    (source target : Option ℕ) :
    pmfPi (quittingPureDeviationStoppingLaws laws player target) =
      (pmfPi (quittingPureDeviationStoppingLaws laws player source)).map
        (replaceStoppingTimeCoordinate player target) := by
  let coordinateMap : ι → Option ℕ → Option ℕ := fun who choice =>
    if who = player then target else choice
  have hfamily : quittingPureDeviationStoppingLaws laws player target =
      fun who =>
        (quittingPureDeviationStoppingLaws laws player source who).map
          (coordinateMap who) := by
    funext who
    by_cases hwho : who = player
    · subst who
      simp only [quittingPureDeviationStoppingLaws, if_pos]
      rw [PMF.pure_map]
      simp [coordinateMap]
    · simp only [quittingPureDeviationStoppingLaws, if_neg hwho]
      have hmap : coordinateMap who = id := by
        funext choice
        simp [coordinateMap, hwho]
      rw [hmap, PMF.map_id]
  rw [hfamily]
  calc
    _ = (pmfPi (quittingPureDeviationStoppingLaws laws player source)).map
        (fun choices who => coordinateMap who (choices who)) := by
      simpa [Math.ProbabilityMassFunction.pushforward] using
        (pmfPi_push_coordwise
          (quittingPureDeviationStoppingLaws laws player source)
          coordinateMap).symm
    _ = _ := by
      congr 1
      funext choices who
      simp [coordinateMap, replaceStoppingTimeCoordinate, Function.update]

omit [Fintype ι] [DecidableEq ι] in
theorem expect_eq_of_eq_on_support {Sample : Type*}
    (law : PMF Sample) (first second : Sample → ℝ)
    (heq : ∀ sample, law sample ≠ 0 → first sample = second sample) :
    Math.Probability.expect law first =
      Math.Probability.expect law second := by
  unfold Math.Probability.expect
  apply tsum_congr
  intro sample
  by_cases hsample : law sample = 0
  · simp [hsample]
  · rw [heq sample hsample]

theorem quittingTerminalPayoff_update_some_eq_clockBound_of_supported
    (reward : {T : Finset ι // T.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (clockBound time : ℕ)
    (htime : clockBound ≤ time)
    (hsupport : ∀ player choice, laws player choice ≠ 0 →
      choice = none ∨ ∃ date < clockBound, choice = some date)
    (player : ι) :
    quittingTerminalPayoff reward
        (Function.update (quittingStoppingLawProfile reward laws) player
          (quittingPureTimeBehaviorStrategy reward player (some time))) player =
      quittingTerminalPayoff reward
        (Function.update (quittingStoppingLawProfile reward laws) player
          (quittingPureTimeBehaviorStrategy reward player
            (some clockBound))) player := by
  by_cases heq : time = clockBound
  · subst time
    rfl
  have hlt : clockBound < time := lt_of_le_of_ne htime (Ne.symm heq)
  rw [quittingTerminalPayoff_update_stoppingLawProfile_pureTime_eq_expect,
    quittingTerminalPayoff_update_stoppingLawProfile_pureTime_eq_expect]
  let sourceLaws :=
    quittingPureDeviationStoppingLaws laws player (some clockBound)
  let targetLaws := quittingPureDeviationStoppingLaws laws player (some time)
  let shift := replaceStoppingTimeCoordinate player (some time)
  have hproduct : pmfPi targetLaws = (pmfPi sourceLaws).map shift :=
    pmfPi_quittingPureDeviation_eq_map laws player (some clockBound) (some time)
  rw [hproduct]
  let value : (ι → Option ℕ) → ℝ := fun choices =>
    quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) player
  have hpush : Math.Probability.expect ((pmfPi sourceLaws).map shift) value =
      Math.Probability.expect (pmfPi sourceLaws) fun choices =>
        value (shift choices) := by
    simpa [Math.ProbabilityMassFunction.pushforward] using
      expect_pushforward_of_bounded (pmfPi sourceLaws) shift value
        (fun choices =>
          abs_quittingTerminalPayoff_le_quittingRewardBound reward _ player)
  rw [hpush]
  symm
  apply expect_eq_of_eq_on_support
  intro choices hchoices
  have hfactors : ∀ who,
      (quittingPureDeviationStoppingLaws laws player (some clockBound) who)
        (choices who) ≠ 0 := by
    rw [pmfPi_apply] at hchoices
    exact fun who => (Finset.prod_ne_zero_iff.mp hchoices) who
      (Finset.mem_univ who)
  have hplayer : choices player = some clockBound := by
    have hpure := hfactors player
    simp [quittingPureDeviationStoppingLaws] at hpure
    exact hpure
  have hothers : ∀ who, who ≠ player →
      choices who = none ∨
        ∃ date < clockBound, choices who = some date := by
    intro who hwho
    apply hsupport who (choices who)
    have hfactor := hfactors who
    simpa [quittingPureDeviationStoppingLaws, hwho] using hfactor
  have hmove :=
    quittingTerminalPayoff_pureStoppingTimeProfile_update_some_eq_of_others_lt
      reward choices player player hlt hothers
  have hsource : Function.update choices player (some clockBound) = choices := by
    rw [← hplayer]
    exact Function.update_eq_self player choices
  calc
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) player =
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward
          (Function.update choices player (some clockBound))) player := by
        exact congrArg (fun draw => quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward draw) player) hsource.symm
    _ = quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward
          (Function.update choices player (some time))) player := hmove
    _ = value (shift choices) := by
      rfl

theorem quittingTerminalPayoff_finiteClockDecodedProfile_update_eq_candidate
    (reward : {T : Finset ι // T.Nonempty} → Payoff ι)
    (clockBound : ℕ)
    (weight : ι → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound))
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0)
    (player : ι) (choice : Option ℕ) :
    quittingTerminalPayoff reward
        (Function.update
          (finiteClockDecodedProfile reward clockBound weight hweight) player
          (quittingPureTimeBehaviorStrategy reward player choice)) player =
      quittingTerminalPayoff reward
        (Function.update
          (finiteClockDecodedProfile reward clockBound weight hweight) player
          (quittingPureTimeBehaviorStrategy reward player
            (finiteClockAtomToStoppingTime clockBound
              (stoppingTimeToFiniteClockAtom clockBound choice)))) player := by
  cases choice with
  | none => rfl
  | some time =>
      by_cases htime : time < clockBound
      · rw [finiteClockAtomToStoppingTime_encode_of_lt
          clockBound time htime]
      · have hsupport : ∀ who choice,
            finiteClockDecodedLaws clockBound weight hweight who choice ≠ 0 →
            choice = none ∨
              ∃ date < clockBound, choice = some date := by
          intro who target htarget
          exact finiteClockDecodeLaw_support clockBound
            (weight who) (hweight who) (haux who) target htarget
        have hlate :=
          quittingTerminalPayoff_update_some_eq_clockBound_of_supported
            reward (finiteClockDecodedLaws clockBound weight hweight)
            clockBound time (Nat.le_of_not_gt htime) hsupport player
        simpa [finiteClockDecodedProfile, stoppingTimeToFiniteClockAtom,
          htime, finiteClockAuxAtom, finiteClockAtomToStoppingTime] using hlate

theorem quittingContinuationBestResponseValue_finiteClockDecodedProfile_eq_of_maxGraph
    (reward : {T : Finset ι // T.Nonempty} → Payoff ι)
    (clockBound : ℕ)
    (weight : ι → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound))
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0)
    (player : ι) (cap : ℝ)
    (hupper : ∀ candidate,
      quittingTerminalPayoff reward
        (Function.update
          (finiteClockDecodedProfile reward clockBound weight hweight) player
          (quittingPureTimeBehaviorStrategy reward player
            (finiteClockAtomToStoppingTime clockBound candidate))) player ≤ cap)
    (htight : ∃ candidate,
      quittingTerminalPayoff reward
        (Function.update
          (finiteClockDecodedProfile reward clockBound weight hweight) player
          (quittingPureTimeBehaviorStrategy reward player
            (finiteClockAtomToStoppingTime clockBound candidate))) player = cap) :
    quittingContinuationBestResponseValue reward
      (finiteClockDecodedProfile reward clockBound weight hweight) player = cap := by
  let value : Option ℕ → ℝ := fun choice =>
    quittingTerminalPayoff reward
      (Function.update
        (finiteClockDecodedProfile reward clockBound weight hweight) player
        (quittingPureTimeBehaviorStrategy reward player choice)) player
  have hbdd : BddAbove (Set.range value) := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro result ⟨choice, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le_quittingRewardBound reward _ player)
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty value)
    rintro result ⟨choice, rfl⟩
    dsimp [value]
    rw [quittingTerminalPayoff_finiteClockDecodedProfile_update_eq_candidate
      reward clockBound weight hweight haux player choice]
    exact hupper (stoppingTimeToFiniteClockAtom clockBound choice)
  · obtain ⟨candidate, hcand⟩ := htight
    rw [← hcand]
    exact le_csSup hbdd (Set.mem_range_self
      (finiteClockAtomToStoppingTime clockBound candidate))

theorem finiteClockCenterWeight_mem_stdSimplex
    {R : Type*} [CommRing R] (coeff : R →+* ℝ)
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ)
    (assign : FiniteClockCenterVar ι clockBound → ℝ)
    (hsolution : SatisfiesFiniteClockCenterPolynomials
      coeff reward clockBound assign) (player : ι) :
    finiteClockCenterWeight clockBound assign player ∈
      stdSimplex ℝ (FiniteClockAtom clockBound) := by
  constructor
  · intro atom
    have hnonneg := hsolution.2.1 player atom
    simpa [finiteClockMassPoly, finiteClockCenterWeight] using hnonneg
  · have hsum := hsolution.1 player
    rw [eval₂_finiteClockSimplexSumPoly] at hsum
    dsimp [finiteClockCenterWeight]
    linarith

theorem finiteClockCenterWeight_aux_eq_zero
    {R : Type*} [CommRing R] (coeff : R →+* ℝ)
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ)
    (assign : FiniteClockCenterVar ι clockBound → ℝ)
    (hsolution : SatisfiesFiniteClockCenterPolynomials
      coeff reward clockBound assign) (player : ι) :
    finiteClockCenterWeight clockBound assign player
      (finiteClockAuxAtom clockBound) = 0 := by
  have haux := hsolution.2.2.1 player
  simpa [finiteClockMassPoly, finiteClockCenterWeight] using haux

theorem finiteClockCenterPair_eq_terminalSemanticPair_of_satisfies
    [Nonempty ι]
    {R : Type*} [CommRing R] (coeff : R →+* ℝ)
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ)
    (assign : FiniteClockCenterVar ι clockBound → ℝ)
    (hsolution : SatisfiesFiniteClockCenterPolynomials
      coeff reward clockBound assign) :
    finiteClockCenterPair clockBound assign =
      quittingTerminalSemanticPair
        (fun terminal player => coeff (reward terminal player))
        (finiteClockDecodedProfile
          (fun terminal player => coeff (reward terminal player))
          clockBound (finiteClockCenterWeight clockBound assign)
          (finiteClockCenterWeight_mem_stdSimplex
            coeff reward clockBound assign hsolution)) := by
  let realReward : {T : Finset ι // T.Nonempty} → Payoff ι :=
    fun terminal player => coeff (reward terminal player)
  let weight := finiteClockCenterWeight clockBound assign
  have hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound) :=
    finiteClockCenterWeight_mem_stdSimplex
      coeff reward clockBound assign hsolution
  have haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0 :=
    finiteClockCenterWeight_aux_eq_zero
      coeff reward clockBound assign hsolution
  have hpayoff : ∀ player,
      assign (FiniteClockCenterVar.payoff player) =
        quittingTerminalPayoff realReward
          (finiteClockDecodedProfile realReward clockBound weight hweight)
          player := by
    intro player
    have hconstraint := hsolution.2.2.2.1 player
    unfold finiteClockPayoffConsistencyPoly at hconstraint
    rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X,
      eval₂_finiteClockOnProfilePayoffPoly] at hconstraint
    have hsemantic :=
      quittingTerminalPayoff_finiteClockDecodedProfile_eq_sum
        realReward clockBound weight hweight player
    dsimp [realReward, weight, finiteClockCenterWeight] at hsemantic
    rw [← hsemantic] at hconstraint
    linarith
  have hcap : ∀ player,
      assign (FiniteClockCenterVar.cap player) =
        quittingContinuationBestResponseValue realReward
          (finiteClockDecodedProfile realReward clockBound weight hweight)
          player := by
    intro player
    have hdeviation : ∀ candidate,
        MvPolynomial.eval₂ coeff assign
            (finiteClockDeviationPayoffPoly reward clockBound
              player candidate) =
          quittingTerminalPayoff realReward
            (Function.update
              (finiteClockDecodedProfile realReward clockBound weight hweight)
              player
              (quittingPureTimeBehaviorStrategy realReward player
                (finiteClockAtomToStoppingTime clockBound candidate)))
            player := by
      intro candidate
      rw [eval₂_finiteClockDeviationPayoffPoly]
      symm
      exact quittingTerminalPayoff_finiteClockDecodedProfile_update_eq_sum
        realReward clockBound weight hweight player candidate
    have hupper : ∀ candidate,
        quittingTerminalPayoff realReward
          (Function.update
            (finiteClockDecodedProfile realReward clockBound weight hweight)
            player
            (quittingPureTimeBehaviorStrategy realReward player
              (finiteClockAtomToStoppingTime clockBound candidate)))
          player ≤ assign (FiniteClockCenterVar.cap player) := by
      intro candidate
      have hconstraint := hsolution.2.2.2.2.1 player candidate
      unfold finiteClockCapUpperPoly at hconstraint
      rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X,
        hdeviation candidate] at hconstraint
      linarith
    have htightEval := hsolution.2.2.2.2.2 player
    unfold finiteClockCapTightPoly at htightEval
    rw [MvPolynomial.eval₂_prod] at htightEval
    obtain ⟨candidate, -, hcand⟩ :=
      (Finset.prod_eq_zero_iff.mp htightEval)
    have htight : quittingTerminalPayoff realReward
          (Function.update
            (finiteClockDecodedProfile realReward clockBound weight hweight)
            player
            (quittingPureTimeBehaviorStrategy realReward player
              (finiteClockAtomToStoppingTime clockBound candidate)))
          player = assign (FiniteClockCenterVar.cap player) := by
      unfold finiteClockCapUpperPoly at hcand
      rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X,
        hdeviation candidate] at hcand
      linarith
    symm
    exact
      quittingContinuationBestResponseValue_finiteClockDecodedProfile_eq_of_maxGraph
        realReward clockBound weight hweight haux player
        (assign (FiniteClockCenterVar.cap player)) hupper ⟨candidate, htight⟩
  apply Prod.ext
  · funext player
    exact hpayoff player
  · funext player
    exact hcap player

def finiteClockSemanticAssignment
    (reward : {T : Finset ι // T.Nonempty} → Payoff ι)
    (clockBound : ℕ)
    (weight : ι → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound)) :
    FiniteClockCenterVar ι clockBound → ℝ
  | .mass player atom => weight player atom
  | .payoff player => quittingTerminalPayoff reward
      (finiteClockDecodedProfile reward clockBound weight hweight) player
  | .cap player => quittingContinuationBestResponseValue reward
      (finiteClockDecodedProfile reward clockBound weight hweight) player

theorem quittingTerminalPayoff_update_pureTime_le_continuationBestResponseValue
    (reward : {T : Finset ι // T.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (player : ι) (choice : Option ℕ) :
    quittingTerminalPayoff reward
        (Function.update profile player
          (quittingPureTimeBehaviorStrategy reward player choice)) player ≤
      quittingContinuationBestResponseValue reward profile player := by
  let value : Option ℕ → ℝ := fun target =>
    quittingTerminalPayoff reward
      (Function.update profile player
        (quittingPureTimeBehaviorStrategy reward player target)) player
  have hbdd : BddAbove (Set.range value) := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro result ⟨target, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le_quittingRewardBound reward _ player)
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  exact le_csSup hbdd (Set.mem_range_self choice)

theorem exists_finiteClockCandidate_payoff_eq_continuationBestResponseValue
    (reward : {T : Finset ι // T.Nonempty} → Payoff ι)
    (clockBound : ℕ)
    (weight : ι → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound))
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0)
    (player : ι) :
    ∃ candidate : FiniteClockAtom clockBound,
      quittingTerminalPayoff reward
          (Function.update
            (finiteClockDecodedProfile reward clockBound weight hweight) player
            (quittingPureTimeBehaviorStrategy reward player
              (finiteClockAtomToStoppingTime clockBound candidate))) player =
        quittingContinuationBestResponseValue reward
          (finiteClockDecodedProfile reward clockBound weight hweight)
          player := by
  let candidateValue : FiniteClockAtom clockBound → ℝ := fun candidate =>
    quittingTerminalPayoff reward
      (Function.update
        (finiteClockDecodedProfile reward clockBound weight hweight) player
        (quittingPureTimeBehaviorStrategy reward player
          (finiteClockAtomToStoppingTime clockBound candidate))) player
  obtain ⟨best, -, hbest⟩ := Finset.exists_max_image Finset.univ
    candidateValue Finset.univ_nonempty
  have hcap :=
    quittingContinuationBestResponseValue_finiteClockDecodedProfile_eq_of_maxGraph
      reward clockBound weight hweight haux player (candidateValue best)
      (fun candidate => hbest candidate (Finset.mem_univ candidate))
      ⟨best, rfl⟩
  exact ⟨best, hcap.symm⟩

theorem satisfiesFiniteClockCenterPolynomials_semanticAssignment
    {R : Type*} [CommRing R] (coeff : R →+* ℝ)
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ)
    (weight : ι → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound))
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0) :
    SatisfiesFiniteClockCenterPolynomials coeff reward clockBound
      (finiteClockSemanticAssignment
        (fun terminal player => coeff (reward terminal player))
        clockBound weight hweight) := by
  let realReward : {T : Finset ι // T.Nonempty} → Payoff ι :=
    fun terminal player => coeff (reward terminal player)
  let assign := finiteClockSemanticAssignment realReward
    clockBound weight hweight
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro player
    rw [eval₂_finiteClockSimplexSumPoly]
    change (∑ atom, weight player atom) - 1 = 0
    exact sub_eq_zero.mpr (hweight player).2
  · intro player atom
    simpa [finiteClockMassPoly, finiteClockSemanticAssignment] using
      (hweight player).1 atom
  · intro player
    simpa [finiteClockMassPoly, finiteClockSemanticAssignment] using
      haux player
  · intro player
    unfold finiteClockPayoffConsistencyPoly
    rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X,
      eval₂_finiteClockOnProfilePayoffPoly]
    simp only [finiteClockSemanticAssignment]
    change quittingTerminalPayoff realReward
        (finiteClockDecodedProfile realReward clockBound weight hweight)
        player - _ = 0
    rw [quittingTerminalPayoff_finiteClockDecodedProfile_eq_sum
      realReward clockBound weight hweight player]
    dsimp [realReward]
    exact sub_self _
  · intro player candidate
    unfold finiteClockCapUpperPoly
    rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X,
      eval₂_finiteClockDeviationPayoffPoly]
    simp only [finiteClockSemanticAssignment]
    change 0 ≤ quittingContinuationBestResponseValue realReward
        (finiteClockDecodedProfile realReward clockBound weight hweight)
        player - _
    rw [← quittingTerminalPayoff_finiteClockDecodedProfile_update_eq_sum
      realReward clockBound weight hweight player candidate]
    exact sub_nonneg.mpr
      (quittingTerminalPayoff_update_pureTime_le_continuationBestResponseValue
        realReward
        (finiteClockDecodedProfile realReward clockBound weight hweight)
        player (finiteClockAtomToStoppingTime clockBound candidate))
  · intro player
    obtain ⟨candidate, hcand⟩ :=
      exists_finiteClockCandidate_payoff_eq_continuationBestResponseValue
        realReward clockBound weight hweight haux player
    unfold finiteClockCapTightPoly
    rw [MvPolynomial.eval₂_prod]
    apply Finset.prod_eq_zero_iff.mpr
    refine ⟨candidate, Finset.mem_univ candidate, ?_⟩
    unfold finiteClockCapUpperPoly
    rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X,
      eval₂_finiteClockDeviationPayoffPoly]
    simp only [finiteClockSemanticAssignment]
    rw [← quittingTerminalPayoff_finiteClockDecodedProfile_update_eq_sum
      realReward clockBound weight hweight player candidate]
    exact sub_eq_zero.mpr hcand.symm

def finiteClockPolynomialSemanticImage
    {R : Type*} [CommRing R] (coeff : R →+* ℝ)
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ) : Set (QuittingTerminalSemanticPair ι) :=
  {pair | ∃ assign : FiniteClockCenterVar ι clockBound → ℝ,
    SatisfiesFiniteClockCenterPolynomials
      coeff reward clockBound assign ∧
    pair = finiteClockCenterPair clockBound assign}

theorem finiteClockPolynomialSemanticImage_eq_reachable
    [Nonempty ι]
    {R : Type*} [CommRing R] (coeff : R →+* ℝ)
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ) :
    finiteClockPolynomialSemanticImage coeff reward clockBound =
      quittingFiniteClockSemanticReachable
        (fun terminal player => coeff (reward terminal player)) clockBound := by
  let realReward : {T : Finset ι // T.Nonempty} → Payoff ι :=
    fun terminal player => coeff (reward terminal player)
  ext pair
  constructor
  · rintro ⟨assign, hsolution, rfl⟩
    let weight := finiteClockCenterWeight clockBound assign
    have hweight : ∀ player,
        weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound) :=
      finiteClockCenterWeight_mem_stdSimplex
        coeff reward clockBound assign hsolution
    have haux : ∀ player,
        weight player (finiteClockAuxAtom clockBound) = 0 :=
      finiteClockCenterWeight_aux_eq_zero
        coeff reward clockBound assign hsolution
    let laws := finiteClockDecodedLaws clockBound weight hweight
    have hlaws : ∀ player, IsFiniteClockStoppingLaw clockBound (laws player) := by
      intro player choice hchoice
      exact finiteClockDecodeLaw_support clockBound
        (weight player) (hweight player) (haux player) choice hchoice
    refine ⟨laws, hlaws, ?_⟩
    exact finiteClockCenterPair_eq_terminalSemanticPair_of_satisfies
      coeff reward clockBound assign hsolution
  · rintro ⟨laws, hlaws, rfl⟩
    let weight : ι → FiniteClockAtom clockBound → ℝ := fun player =>
      finiteClockLawCoordinates clockBound (laws player)
    have hweight : ∀ player,
        weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound) :=
      fun player => finiteClockLawCoordinates_mem_stdSimplex
        clockBound (laws player)
    have haux : ∀ player,
        weight player (finiteClockAuxAtom clockBound) = 0 :=
      fun player => finiteClockLawCoordinates_aux_eq_zero
        clockBound (laws player) (hlaws player)
    let assign := finiteClockSemanticAssignment realReward
      clockBound weight hweight
    have hsolution : SatisfiesFiniteClockCenterPolynomials
        coeff reward clockBound assign :=
      satisfiesFiniteClockCenterPolynomials_semanticAssignment
        coeff reward clockBound weight hweight haux
    refine ⟨assign, hsolution, ?_⟩
    have hlawsExact : finiteClockDecodedLaws clockBound weight hweight = laws := by
      funext player
      exact finiteClockDecodeLaw_coordinates
        clockBound (laws player) (hlaws player)
    have hprofile : finiteClockDecodedProfile realReward
        clockBound weight hweight = quittingStoppingLawProfile realReward laws := by
      unfold finiteClockDecodedProfile
      rw [hlawsExact]
    unfold finiteClockCenterPair assign finiteClockSemanticAssignment
    change quittingTerminalSemanticPair realReward
        (quittingStoppingLawProfile realReward laws) =
      quittingTerminalSemanticPair realReward
        (finiteClockDecodedProfile realReward clockBound weight hweight)
    rw [hprofile]

theorem rationalFiniteClockPolynomialSemanticImage_eq_reachable
    [Nonempty ι]
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (clockBound : ℕ) :
    finiteClockPolynomialSemanticImage (Rat.castHom ℝ) reward clockBound =
      quittingFiniteClockSemanticReachable
        (fun terminal player => (reward terminal player : ℝ)) clockBound := by
  simpa using finiteClockPolynomialSemanticImage_eq_reachable
    (ι := ι) (Rat.castHom ℝ) reward clockBound

end GameTheory
