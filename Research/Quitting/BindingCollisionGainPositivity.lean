/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.Simplex
import MathUE.PMFProduct.Bool
import Research.Quitting.ForwardExactCapTailFlow
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium

/-!
# Collision gains forced by a unique all-Continue root at a cap

Fix a declared cap dominating every coordinate's own solo terminal reward.
The solo probe row at which one coordinate quits at a small positive rate and
every other coordinate continues surely is an exact root Nash against that cap
precisely when the probing coordinate has vanishing cap defect and every other
coordinate's affine joining slope is nonpositive at that rate.

If all Continue is the *unique* exact root at the cap, no such probe can
exist.  Every coordinate with vanishing cap defect therefore admits another
coordinate that both has vanishing cap defect and strictly gains by joining
the probe.  Two consequences follow for a forward exact-cap ray: the binding
face of the limiting cap is never a singleton, and on a binding face of
exactly two coordinates each of the two strictly gains by joining the other.

The probe uses no maximum-absorption or perturbation argument.  It is a single
exact root at the same cap, so it needs no localization and no ray time.
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
    reward cap hne, bernoulliBool_true_toReal, bernoulliBool_false_toReal]

/-! ## The solo probe is an exact root Nash -/

/-- The solo probe row is an exact root Nash against a declared cap exactly
when the probing coordinate has vanishing cap defect and every other
coordinate's affine joining slope is nonpositive. -/
theorem isεQuittingRootNash_soloStationaryRoot_bernoulli
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (owner : ι)
    (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1)
    (howner : quittingSingletonCapDefect reward cap owner = 0)
    (hother : ∀ other, other ≠ owner →
      rate * quittingSingletonCollisionGain reward owner other ≤
        (1 - rate) * quittingSingletonCapDefect reward cap other) :
    IsεQuittingRootNash reward cap 0
      (quittingSoloStationaryRoot owner (bernoulliBool rate hrate0 hrate1)) := by
  rw [← isεQuittingRootEndpointNash_iff_isεQuittingRootNash]
  intro who
  by_cases hwho : who = owner
  · subst who
    rw [quittingRootEndpointDifference_soloStationaryRoot_owner_cap, howner]
    constructor <;> simp
  · have hslope := hother who hwho
    have hcontinueMass :
        (quittingSoloStationaryRoot owner (bernoulliBool rate hrate0 hrate1)
          who false).toReal = 1 := by
      rw [quittingSoloStationaryRoot_apply_other hwho]
      simp
    have hquitMass :
        (quittingSoloStationaryRoot owner (bernoulliBool rate hrate0 hrate1)
          who true).toReal = 0 := by
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

/-- **The sign lemma.**  If all Continue is the unique exact root at a cap
dominating every solo terminal reward, then every coordinate with vanishing
cap defect admits another coordinate that also has vanishing cap defect and
strictly gains by quitting together with it. -/
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
  have hdefectNonneg : ∀ who, 0 ≤ quittingSingletonCapDefect reward cap who :=
    fun who ↦ sub_nonneg.mpr (hcap who)
  have hdefectPos : ∀ other, other ≠ owner →
      0 < quittingSingletonCollisionGain reward owner other →
      0 < quittingSingletonCapDefect reward cap other := by
    intro other hne hgain
    rcases (hdefectNonneg other).lt_or_eq with hpositive | hzero
    · exact hpositive
    · exact absurd hgain (not_lt.2 (hnone other hne hzero.symm))
  -- a positive rate at which no other coordinate wants to join
  let safe : ι → ℝ := fun who ↦
    if 0 < quittingSingletonCollisionGain reward owner who ∧ who ≠ owner then
      quittingSingletonCapDefect reward cap who /
        (quittingSingletonCapDefect reward cap who +
          quittingSingletonCollisionGain reward owner who)
    else 1
  have hsafePos : ∀ who, 0 < safe who := by
    intro who
    by_cases hcase : 0 < quittingSingletonCollisionGain reward owner who ∧
        who ≠ owner
    · rw [show safe who = _ from if_pos hcase]
      exact div_pos (hdefectPos who hcase.2 hcase.1)
        (by linarith [hdefectPos who hcase.2 hcase.1, hcase.1])
    · rw [show safe who = _ from if_neg hcase]
      norm_num
  have hnonempty : (Finset.univ : Finset ι).Nonempty := ⟨owner, Finset.mem_univ owner⟩
  set floor : ℝ := Finset.univ.inf' hnonempty safe with hfloor
  have hfloorPos : 0 < floor := by
    rw [hfloor, Finset.lt_inf'_iff]
    exact fun who _ ↦ hsafePos who
  have hfloorLe : ∀ who, floor ≤ safe who :=
    fun who ↦ Finset.inf'_le safe (Finset.mem_univ who)
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
    · have hcase : 0 < quittingSingletonCollisionGain reward owner other ∧
          other ≠ owner := ⟨hgain, hne⟩
      have hdefect := hdefectPos other hne hgain
      have hsum : 0 < quittingSingletonCapDefect reward cap other +
          quittingSingletonCollisionGain reward owner other := by linarith
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
      have hleft : rate * quittingSingletonCollisionGain reward owner other ≤ 0 :=
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
  have hmass := congrArg (fun marginal : PMF Bool ↦ (marginal true).toReal)
    hcoordinate
  simp only [bernoulliBool_true_toReal, quittingAllContinueRoot,
    PMF.pure_apply, if_neg (by decide : ¬(true = false)), ENNReal.toReal_zero]
    at hmass
  linarith

/-! ## Consequences for the binding face of a forward exact-cap ray -/

namespace QuittingForwardExactCapTail

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Membership in the binding face is exactly a vanishing cap defect. -/
theorem mem_bindingFinset_iff_capDefect_eq_zero
    (tail : QuittingForwardExactCapTail reward) (who : ι) :
    who ∈ tail.bindingFinset ↔
      quittingSingletonCapDefect reward tail.capLimit who = 0 := by
  rw [bindingFinset, Finset.mem_filter, quittingSingletonCapDefect,
    sub_eq_zero]
  simp only [Finset.mem_univ, true_and]

/-- With a unique all-Continue root at the limiting cap, every binding
coordinate has another binding coordinate that strictly gains by joining
it. -/
theorem exists_binding_collisionGain_pos_of_unique_allContinue
    (tail : QuittingForwardExactCapTail reward)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward tail.capLimit 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    {owner : ι} (howner : owner ∈ tail.bindingFinset) :
    ∃ other ∈ tail.bindingFinset, other ≠ owner ∧
      0 < quittingSingletonCollisionGain reward owner other := by
  obtain ⟨other, hne, hdefect, hgain⟩ :=
    exists_quittingSingletonCollisionGain_pos_of_unique_allContinue
      reward tail.capLimit tail.singleton_le_capLimit hunique owner
      ((tail.mem_bindingFinset_iff_capDefect_eq_zero owner).1 howner)
  exact ⟨other, (tail.mem_bindingFinset_iff_capDefect_eq_zero other).2 hdefect,
    hne, hgain⟩

/-- **The binding face is never a singleton** under a unique all-Continue
root at the limiting cap. -/
theorem bindingFinset_card_ne_one_of_unique_allContinue
    (tail : QuittingForwardExactCapTail reward)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward tail.capLimit 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    tail.bindingFinset.card ≠ 1 := by
  intro hcard
  obtain ⟨owner, hsingleton⟩ := Finset.card_eq_one.1 hcard
  have howner : owner ∈ tail.bindingFinset := by
    rw [hsingleton]
    exact Finset.mem_singleton_self owner
  obtain ⟨other, hother, hne, -⟩ :=
    tail.exists_binding_collisionGain_pos_of_unique_allContinue hunique howner
  rw [hsingleton, Finset.mem_singleton] at hother
  exact hne hother

/-- **On a binding pair each coordinate strictly gains by joining the
other.**  This is the sign fact the finite-cap face computation consumes. -/
theorem quittingSingletonCollisionGain_pos_of_bindingFinset_card_eq_two
    (tail : QuittingForwardExactCapTail reward)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward tail.capLimit 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (hcard : tail.bindingFinset.card = 2)
    {owner other : ι} (howner : owner ∈ tail.bindingFinset)
    (hother : other ∈ tail.bindingFinset) (hne : other ≠ owner) :
    0 < quittingSingletonCollisionGain reward owner other := by
  classical
  obtain ⟨witness, hwitness, hwitnessNe, hgain⟩ :=
    tail.exists_binding_collisionGain_pos_of_unique_allContinue hunique howner
  have hwitnessEq : witness = other := by
    by_contra hdifferent
    have hsubset : ({owner, other, witness} : Finset ι) ⊆ tail.bindingFinset := by
      intro player hplayer
      simp only [Finset.mem_insert, Finset.mem_singleton] at hplayer
      rcases hplayer with hcase | hcase | hcase
      · exact hcase ▸ howner
      · exact hcase ▸ hother
      · exact hcase ▸ hwitness
    have hthree : ({owner, other, witness} : Finset ι).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨Ne.symm hne, Ne.symm hwitnessNe⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          exact fun heq ↦ hdifferent heq.symm),
        Finset.card_singleton]
    have hle := Finset.card_le_card hsubset
    omega
  exact hwitnessEq ▸ hgain

end QuittingForwardExactCapTail

/-! ## The cap defect at a strictly interior indifference rate -/

omit [Fintype ι] in
/-- A strictly interior indifference rate together with a strictly positive
collision gain forces a strictly positive cap defect.  This is the step that
turns the sign lemma into positivity of the own defect at a finite cap. -/
theorem quittingSingletonCapDefect_pos_of_interior_indifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (owner other : ι) (rate : ℝ)
    (hrate0 : 0 < rate) (hrate1 : rate < 1)
    (hgain : 0 < quittingSingletonCollisionGain reward owner other)
    (hindifference :
      (1 - rate) * quittingSingletonCapDefect reward cap other =
        rate * quittingSingletonCollisionGain reward owner other) :
    0 < quittingSingletonCapDefect reward cap other := by
  have hproduct : 0 < rate * quittingSingletonCollisionGain reward owner other :=
    mul_pos hrate0 hgain
  nlinarith [hindifference, hproduct]

end GameTheory
