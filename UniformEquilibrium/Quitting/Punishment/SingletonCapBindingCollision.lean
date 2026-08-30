/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.Simplex
import MathUE.PMFProduct.Bool
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium

/-!
# Singleton-cap binding collisions

Fix a declared cap dominating every coordinate's own singleton terminal
reward.  A solo probe row is an exact root Nash against that cap precisely
when the probing coordinate has vanishing cap defect and every other
coordinate's affine joining slope is nonpositive at the selected rate.

If all Continue is the unique exact root at the cap, no absorbing solo probe
can exist.  Every binding coordinate therefore admits a distinct binding
coordinate that strictly gains by joining its probe.  These are finite root
and cap facts; no ray, limiting profile, or behavioral realization is used.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Cap defect and collision gain -/

/-- The amount by which a declared cap exceeds one coordinate's own solo
terminal reward. -/
def quittingSingletonCapDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (who : ι) : ℝ :=
  cap who - reward (quittingSingletonTerminal who) who

/-- The amount `other` gains by quitting together with `owner` rather than
letting `owner` quit alone. -/
def quittingSingletonCollisionGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner other : ι) : ℝ :=
  quittingSingletonCollisionReward reward owner other -
    quittingSoloReward reward owner other

/-! ## Endpoint differences at the solo probe row -/

/-- Against a declared cap, the probing coordinate's endpoint difference at
its own solo row is minus its cap defect. -/
theorem quittingRootEndpointDifference_soloStationaryRoot_owner_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (owner : ι) (hazard : PMF Bool) :
    quittingRootEndpointDifference reward cap
        (quittingSoloStationaryRoot owner hazard) owner =
      -quittingSingletonCapDefect reward cap owner := by
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_soloStationaryRoot_owner,
    quittingRootContinuePayoff_soloStationaryRoot_owner,
    quittingSoloReward_self, quittingSingletonCapDefect]
  ring

/-- Against a declared cap, any other coordinate's endpoint difference at an
arbitrary Boolean solo row is its affine joining slope. -/
theorem quittingRootEndpointDifference_soloStationaryRoot_other_cap_pmf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) {owner other : ι} (hne : other ≠ owner)
    (hazard : PMF Bool) :
    quittingRootEndpointDifference reward cap
        (quittingSoloStationaryRoot owner hazard) other =
      (hazard true).toReal *
          quittingSingletonCollisionGain reward owner other -
        (hazard false).toReal *
          quittingSingletonCapDefect reward cap other := by
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_soloStationaryRoot_other reward hne,
    quittingRootContinuePayoff_soloStationaryRoot_other reward hne,
    quittingSoloReward_self, quittingSingletonCollisionGain,
    quittingSingletonCapDefect]
  ring

/-- Bernoulli-coordinate form of the arbitrary-PMF solo affine identity. -/
theorem quittingRootEndpointDifference_soloStationaryRoot_other_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) {owner other : ι} (hne : other ≠ owner)
    (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingRootEndpointDifference reward cap
        (quittingSoloStationaryRoot owner
          (bernoulliBool rate hrate0 hrate1)) other =
      rate * quittingSingletonCollisionGain reward owner other -
        (1 - rate) * quittingSingletonCapDefect reward cap other := by
  rw [quittingRootEndpointDifference_soloStationaryRoot_other_cap_pmf
    reward cap hne, bernoulliBool_true_toReal,
    bernoulliBool_false_toReal]

/-! ## The solo probe is an exact root Nash -/

/-- The solo probe row is an exact root Nash against a declared cap when the
probing coordinate binds and every other coordinate's affine joining slope
is nonpositive. -/
theorem isεQuittingRootNash_soloStationaryRoot_bernoulli
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (owner : ι)
    (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1)
    (howner : quittingSingletonCapDefect reward cap owner = 0)
    (hother : ∀ other, other ≠ owner →
      rate * quittingSingletonCollisionGain reward owner other ≤
        (1 - rate) * quittingSingletonCapDefect reward cap other) :
    IsεQuittingRootNash reward cap 0
      (quittingSoloStationaryRoot owner
        (bernoulliBool rate hrate0 hrate1)) := by
  rw [← isεQuittingRootEndpointNash_iff_isεQuittingRootNash]
  intro who
  by_cases hwho : who = owner
  · subst who
    rw [quittingRootEndpointDifference_soloStationaryRoot_owner_cap, howner]
    constructor <;> simp
  · have hslope := hother who hwho
    have hcontinueMass :
        (quittingSoloStationaryRoot owner
          (bernoulliBool rate hrate0 hrate1) who false).toReal = 1 := by
      rw [quittingSoloStationaryRoot_apply_other hwho]
      simp
    have hquitMass :
        (quittingSoloStationaryRoot owner
          (bernoulliBool rate hrate0 hrate1) who true).toReal = 0 := by
      rw [quittingSoloStationaryRoot_apply_other hwho]
      simp
    rw [quittingRootEndpointDifference_soloStationaryRoot_other_cap
      reward cap hwho rate hrate0 hrate1]
    refine ⟨?_, ?_⟩
    · rw [hcontinueMass, one_mul]
      linarith
    · rw [hquitMass, zero_mul]
      norm_num

/-! ## Positivity of the collision gain -/

/-- If all Continue is the unique exact root at a cap dominating every solo
terminal reward, each binding coordinate admits a distinct binding
coordinate that strictly gains by joining its probe. -/
theorem exists_quittingSingletonCollisionGain_pos_of_unique_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι)
    (hcap : ∀ who, reward (quittingSingletonTerminal who) who ≤ cap who)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (owner : ι)
    (howner : quittingSingletonCapDefect reward cap owner = 0) :
    ∃ other, other ≠ owner ∧
      quittingSingletonCapDefect reward cap other = 0 ∧
      0 < quittingSingletonCollisionGain reward owner other := by
  classical
  by_contra hnone
  push Not at hnone
  have hdefectNonneg : ∀ who,
      0 ≤ quittingSingletonCapDefect reward cap who :=
    fun who => sub_nonneg.mpr (hcap who)
  have hdefectPos : ∀ other, other ≠ owner →
      0 < quittingSingletonCollisionGain reward owner other →
      0 < quittingSingletonCapDefect reward cap other := by
    intro other hne hgain
    rcases (hdefectNonneg other).lt_or_eq with hpositive | hzero
    · exact hpositive
    · exact absurd hgain (not_lt.2 (hnone other hne hzero.symm))
  let safe : ι → ℝ := fun who =>
    if 0 < quittingSingletonCollisionGain reward owner who ∧ who ≠ owner then
      quittingSingletonCapDefect reward cap who /
        (quittingSingletonCapDefect reward cap who +
          quittingSingletonCollisionGain reward owner who)
    else 1
  have hsafePos : ∀ who, 0 < safe who := by
    intro who
    by_cases hcase :
        0 < quittingSingletonCollisionGain reward owner who ∧ who ≠ owner
    · rw [show safe who = _ from if_pos hcase]
      exact div_pos (hdefectPos who hcase.2 hcase.1)
        (by linarith [hdefectPos who hcase.2 hcase.1, hcase.1])
    · rw [show safe who = _ from if_neg hcase]
      norm_num
  have hnonempty : (Finset.univ : Finset ι).Nonempty :=
    ⟨owner, Finset.mem_univ owner⟩
  set floor : ℝ := Finset.univ.inf' hnonempty safe with hfloor
  have hfloorPos : 0 < floor := by
    rw [hfloor, Finset.lt_inf'_iff]
    exact fun who _ => hsafePos who
  have hfloorLe : ∀ who, floor ≤ safe who :=
    fun who => Finset.inf'_le safe (Finset.mem_univ who)
  have hsafeOwner : safe owner = 1 := if_neg (by simp)
  have hfloorOne : floor ≤ 1 := hsafeOwner ▸ hfloorLe owner
  set rate : ℝ := floor / 2 with hrate
  have hrate0 : 0 ≤ rate := by positivity
  have hratePos : 0 < rate := by positivity
  have hrateHalf : rate ≤ 1 / 2 := by rw [hrate]; linarith
  have hrate1 : rate ≤ 1 := by linarith
  have hslope : ∀ other, other ≠ owner →
      rate * quittingSingletonCollisionGain reward owner other ≤
        (1 - rate) * quittingSingletonCapDefect reward cap other := by
    intro other hne
    by_cases hgain : 0 < quittingSingletonCollisionGain reward owner other
    · have hcase :
          0 < quittingSingletonCollisionGain reward owner other ∧
            other ≠ owner := ⟨hgain, hne⟩
      have hdefect := hdefectPos other hne hgain
      have hsum : 0 < quittingSingletonCapDefect reward cap other +
          quittingSingletonCollisionGain reward owner other := by
        linarith
      have hsafeOther : safe other =
          quittingSingletonCapDefect reward cap other /
            (quittingSingletonCapDefect reward cap other +
              quittingSingletonCollisionGain reward owner other) :=
        if_pos hcase
      have hle : rate ≤ quittingSingletonCapDefect reward cap other /
          (quittingSingletonCapDefect reward cap other +
            quittingSingletonCollisionGain reward owner other) := by
        rw [← hsafeOther]
        have hbound := hfloorLe other
        rw [hrate]
        linarith
      rw [le_div_iff₀ hsum] at hle
      linarith
    · have hgain' : quittingSingletonCollisionGain reward owner other ≤ 0 :=
        not_lt.1 hgain
      have hleft :
          rate * quittingSingletonCollisionGain reward owner other ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hrate0 hgain'
      have hright : 0 ≤ (1 - rate) *
          quittingSingletonCapDefect reward cap other :=
        mul_nonneg (by linarith) (hdefectNonneg other)
      linarith
  have hnash := isεQuittingRootNash_soloStationaryRoot_bernoulli
    reward cap owner rate hrate0 hrate1 howner hslope
  have hallContinue := hunique _ hnash
  have hcoordinate := congrFun hallContinue owner
  rw [quittingSoloStationaryRoot_apply_owner] at hcoordinate
  have hmass := congrArg
    (fun marginal : PMF Bool => (marginal true).toReal) hcoordinate
  simp only [bernoulliBool_true_toReal, quittingAllContinueRoot,
    PMF.pure_apply, if_neg (by decide : ¬(true = false)),
    ENNReal.toReal_zero] at hmass
  linarith

/-! ## Interior indifference -/

omit [Fintype ι] in
/-- A strictly interior indifference rate and positive collision gain force a
strictly positive cap defect. -/
theorem quittingSingletonCapDefect_pos_of_interior_indifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (owner other : ι) (rate : ℝ)
    (hrate0 : 0 < rate) (hrate1 : rate < 1)
    (hgain : 0 < quittingSingletonCollisionGain reward owner other)
    (hindifference :
      (1 - rate) * quittingSingletonCapDefect reward cap other =
        rate * quittingSingletonCollisionGain reward owner other) :
    0 < quittingSingletonCapDefect reward cap other := by
  have hproduct :
      0 < rate * quittingSingletonCollisionGain reward owner other :=
    mul_pos hrate0 hgain
  nlinarith [hindifference, hproduct]

end GameTheory
