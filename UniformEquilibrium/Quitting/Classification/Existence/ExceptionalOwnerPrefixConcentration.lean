/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.DivergentExceptionalOwnerHazard
import UniformEquilibrium.Quitting.Classification.Existence.QuietWindowStationaryRepair
import UniformEquilibrium.Quitting.Paths.LiveChainDominationCap

/-!
# Prefix concentration at a divergent exceptional-owner source

The positive deleted survival and vanishing owner survival of a divergent
exceptional source separate the two competing geometric clocks.  Consequently
the survival-weighted probability that an opponent absorbs before the owner
vanishes over the entire repeated prefix.  The existing quiet-window estimate
then concentrates the source plan's initial payoff on the owner's singleton
reward.

This file records the probabilistic and payoff consequences only.  It does not
assert that the singleton stationary repair is an equilibrium; that final step
also needs the owner's Never-deviation inequality.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Two repeated Bernoulli clocks separate when the first clock has a positive
survival limit but the second clock's survival vanishes.  In that regime the
first clock's one-row hazard is negligible relative to the combined hazard. -/
theorem tendsto_firstHazard_div_combinedHazard_zero
    (first second : ℕ → ℝ) (horizon : ℕ → ℕ) (limit : ℝ)
    (hfirst0 : ∀ n, 0 ≤ first n) (hfirst1 : ∀ n, first n ≤ 1)
    (hsecond0 : ∀ n, 0 ≤ second n) (hsecond1 : ∀ n, second n ≤ 1)
    (hhorizon : ∀ n, horizon n ≠ 0)
    (hhorizonTop : Tendsto horizon atTop atTop)
    (hlimit0 : 0 < limit) (hlimit1 : limit ≤ 1)
    (hfirstPow : Tendsto (fun n ↦ first n ^ horizon n) atTop (nhds limit))
    (hsecondPow : Tendsto (fun n ↦ second n ^ horizon n) atTop (nhds 0)) :
    Tendsto (fun n ↦ (1 - first n) / (1 - first n * second n))
      atTop (nhds 0) := by
  have hfirst : Tendsto first atTop (nhds 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    by_cases hlarge : 1 < ε
    · refine ⟨0, fun n _ ↦ ?_⟩
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hfirst1 n))]
      linarith [hfirst0 n]
    · have hεone : ε ≤ 1 := le_of_not_gt hlarge
      let base : ℝ := 1 - ε
      have hbase0 : 0 ≤ base := by dsimp [base]; linarith
      have hbase1 : base < 1 := by dsimp [base]; linarith
      have hbasePow : Tendsto (fun fuel : ℕ ↦ base ^ fuel)
          atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
      have hfirstLower : ∀ᶠ n in atTop,
          limit / 2 < first n ^ horizon n :=
        (tendsto_order.1 hfirstPow).1 (limit / 2) (by linarith)
      have hbaseUpper : ∀ᶠ n in atTop,
          base ^ horizon n < limit / 2 := by
        exact (tendsto_order.1 (hbasePow.comp hhorizonTop)).2
          (limit / 2) (by linarith)
      obtain ⟨threshold, hthreshold⟩ :=
        Filter.eventually_atTop.1 (hfirstLower.and hbaseUpper)
      refine ⟨threshold, fun n hn ↦ ?_⟩
      obtain ⟨hlower, hupper⟩ := hthreshold n hn
      have hbaseLt : base < first n := by
        by_contra hnot
        have hpowers := pow_le_pow_left₀ (hfirst0 n) (le_of_not_gt hnot)
          (horizon n)
        linarith
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hfirst1 n))]
      dsimp only [base] at hbaseLt
      linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (4 / ε)
  have hkReal : (0 : ℝ) < k := by
    have : (0 : ℝ) < 4 / ε := by positivity
    linarith
  have hk0 : k ≠ 0 := by
    exact_mod_cast (ne_of_gt hkReal)
  have hεk : 4 < ε * k := by
    have hεne : ε ≠ 0 := ne_of_gt hε
    calc
      4 = ε * (4 / ε) := by field_simp
      _ < ε * k := mul_lt_mul_of_pos_left hk hε
  let geometric : ℕ → ℝ := fun n ↦
    ∑ exponent ∈ Finset.range k, first n ^ exponent
  have hgeometric : Tendsto geometric atTop (nhds k) := by
    unfold geometric
    convert tendsto_finsetSum (s := Finset.range k)
      (fun exponent _ ↦ hfirst.pow exponent) using 1
    simp
  have hlimitHalf0 : 0 < limit / 2 := by linarith
  have hthreshold0 : 0 < (limit / 2) ^ k := pow_pos hlimitHalf0 k
  have hthreshold1 : (limit / 2) ^ k ≤ 1 := by
    exact pow_le_one₀ hlimitHalf0.le (by linarith)
  have hfirstEventually : ∀ᶠ n in atTop, 1 / 2 < first n :=
    (tendsto_order.1 hfirst).1 (1 / 2) (by norm_num)
  have hgeometricEventually : ∀ᶠ n in atTop, k / 2 < geometric n :=
    (tendsto_order.1 hgeometric).1 (k / 2) (by linarith)
  have hfirstPowEventually : ∀ᶠ n in atTop,
      limit / 2 < first n ^ horizon n :=
    (tendsto_order.1 hfirstPow).1 (limit / 2) (by linarith)
  have hsecondPowEventually : ∀ᶠ n in atTop,
      second n ^ horizon n < (limit / 2) ^ k :=
    (tendsto_order.1 hsecondPow).2 _ hthreshold0
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.1
    (hfirstEventually.and (hgeometricEventually.and
      (hfirstPowEventually.and hsecondPowEventually)))
  refine ⟨threshold, fun n hn ↦ ?_⟩
  obtain ⟨hfirstHalf, hgeom, hfirstPower, hsecondPower⟩ :=
    hthreshold n hn
  have hcombined0 : 0 ≤ 1 - first n * second n := by
    have hmul : first n * second n ≤ 1 := by
      calc
        first n * second n ≤ 1 * second n :=
          mul_le_mul_of_nonneg_right (hfirst1 n) (hsecond0 n)
        _ ≤ 1 := by simpa using hsecond1 n
    linarith
  by_cases hcombined : 1 - first n * second n = 0
  · have hfirstEq : first n = 1 := by
      nlinarith [hfirst0 n, hfirst1 n, hsecond0 n, hsecond1 n]
    simp [hfirstEq, hε]
  · have hcombinedPos : 0 < 1 - first n * second n :=
      lt_of_le_of_ne hcombined0 (Ne.symm hcombined)
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg (by linarith [hfirst1 n])
      hcombined0)]
    rw [div_lt_iff₀ hcombinedPos]
    by_contra hnot
    have hbad : ε * (1 - first n * second n) ≤ 1 - first n := by
      exact le_of_not_gt hnot
    have hclock : ε * first n * (1 - second n) ≤ 1 - first n := by
      have hdecomp : 1 - first n * second n =
          (1 - first n) + first n * (1 - second n) := by ring
      have hnonneg : 0 ≤ 1 - first n := by linarith [hfirst1 n]
      nlinarith
    have hsecondLt : second n < 1 := by
      by_contra hnotSecond
      have hsecondEq : second n = 1 := le_antisymm (hsecond1 n)
        (le_of_not_gt hnotSecond)
      rw [hsecondEq, one_pow] at hsecondPower
      linarith
    have hgeom0 : 0 ≤ geometric n := by
      apply Finset.sum_nonneg
      intro exponent _
      positivity
    have hcoefficient : 1 < ε * first n * geometric n := by
      have hfirstScaled : ε * (1 / 2 : ℝ) < ε * first n :=
        mul_lt_mul_of_pos_left hfirstHalf hε
      have hkHalf : 0 < (k : ℝ) / 2 := by positivity
      have hfirstTimesK :
          (ε * (1 / 2 : ℝ)) * (k / 2) <
            (ε * first n) * (k / 2) :=
        mul_lt_mul_of_pos_right hfirstScaled hkHalf
      have hfirstPos : 0 < ε * first n :=
        mul_pos hε (lt_trans (by norm_num) hfirstHalf)
      have htimesGeom : (ε * first n) * (k / 2) <
          (ε * first n) * geometric n :=
        mul_lt_mul_of_pos_left hgeom hfirstPos
      nlinarith
    have hclockScaled : ε * first n * (1 - second n) * geometric n ≤
        (1 - first n) * geometric n :=
      mul_le_mul_of_nonneg_right hclock hgeom0
    have hstrict : 1 - second n < (1 - first n) * geometric n := by
      calc
        1 - second n < (ε * first n * geometric n) * (1 - second n) := by
          nlinarith
        _ = ε * first n * (1 - second n) * geometric n := by ring
        _ ≤ (1 - first n) * geometric n := hclockScaled
    have hgeomIdentity : (1 - first n) * geometric n = 1 - first n ^ k := by
      have hidentity := geom_sum_mul (first n) k
      dsimp only [geometric]
      nlinarith
    have hpowLt : first n ^ k < second n := by
      rw [hgeomIdentity] at hstrict
      linarith
    have hpowPower : (first n ^ k) ^ horizon n <
        second n ^ horizon n :=
      pow_lt_pow_left₀ hpowLt (by positivity) (hhorizon n)
    have hreorder : (first n ^ k) ^ horizon n =
        (first n ^ horizon n) ^ k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hreorder] at hpowPower
    have hlowerPower : (limit / 2) ^ k <
        (first n ^ horizon n) ^ k :=
      pow_lt_pow_left₀ hfirstPower hlimitHalf0.le hk0
    linarith

/-- For a divergent exceptional source, the opponents' one-row hazard is
negligible compared with the joint one-row absorption hazard. -/
theorem QuittingUniqueExceptionalOwnerSource.tendsto_ownerOpponentHazardRatio_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward)
    (hhorizon : Tendsto
      (fun n ↦ source.family.horizon (source.selected n)) atTop atTop) :
    Tendsto (fun n ↦
      (1 - quittingStationaryFixedOpponentsContinueMass
          (source.family.root (source.selected n)) source.owner) /
        (1 - quittingStationaryFixedOpponentsContinueMass
            (source.family.root (source.selected n)) source.owner *
          (source.family.root
            (source.selected n) source.owner false).toReal))
      atTop (nhds 0) := by
  let first : ℕ → ℝ := fun n ↦
    quittingStationaryFixedOpponentsContinueMass
      (source.family.root (source.selected n)) source.owner
  let second : ℕ → ℝ := fun n ↦
    (source.family.root (source.selected n) source.owner false).toReal
  let horizon : ℕ → ℕ := fun n ↦
    source.family.horizon (source.selected n) + 1
  have hhorizonShift : Tendsto horizon atTop atTop := by
    have hadd := (tendsto_add_atTop_nat 1).comp hhorizon
    simpa [horizon, Function.comp_def, Nat.add_comm] using hadd
  have hlimit1 : source.deletedLimit ≤ 1 := by
    apply le_of_tendsto' source.ownerDeleted_tendsto
    intro n
    exact (source.family.prefixDeletedSurvival_mem_Icc
      (source.selected n) source.owner).2
  have hfirstPow : Tendsto (fun n ↦ first n ^ horizon n)
      atTop (nhds source.deletedLimit) := by
    simpa [first, horizon,
      source.family.prefixDeletedSurvival_eq_pow] using
        source.ownerDeleted_tendsto
  have hsecondPow : Tendsto (fun n ↦ second n ^ horizon n)
      atTop (nhds 0) := by
    simpa [second, horizon] using
      source.ownerPrefixSurvival_tendsto_zero.congr'
        (Filter.Eventually.of_forall fun n ↦
          source.ownerPrefixSurvival_eq_pow n)
  exact tendsto_firstHazard_div_combinedHazard_zero
    first second horizon source.deletedLimit
    (fun n ↦ quittingStationaryFixedOpponentsContinueMass_nonneg _ _)
    (fun n ↦ quittingStationaryFixedOpponentsContinueMass_le_one _ _)
    (fun _ ↦ ENNReal.toReal_nonneg)
    (fun n ↦ by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top
        ((source.family.root (source.selected n) source.owner).coe_le_one false))
    (fun n ↦ by simp [horizon]) hhorizonShift source.deletedLimit_pos
    hlimit1 hfirstPow hsecondPow

/-- Total survival-weighted probability that an opponent of the exceptional
owner absorbs during the selected repeated prefix. -/
def QuittingUniqueExceptionalOwnerSource.ownerPrefixOpponentCharge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward) (n : ℕ) : ℝ :=
  let index := source.selected n
  let roots := quittingStationaryPrefixFamilyPlan source.family index
  ∑ time ∈ Finset.range (source.family.horizon index + 1),
    quittingJointSurvivalWeight roots 0 time *
      quittingRootOpponentAbsorptionMass (roots time) source.owner

/-- The prefix opponent charge is the elementary geometric competing-clock
sum at the selected stationary row. -/
theorem QuittingUniqueExceptionalOwnerSource.ownerPrefixOpponentCharge_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward) (n : ℕ) :
    source.ownerPrefixOpponentCharge n =
      ∑ time ∈ Finset.range
          (source.family.horizon (source.selected n) + 1),
        (quittingStationaryFixedOpponentsContinueMass
              (source.family.root (source.selected n)) source.owner *
            (source.family.root
              (source.selected n) source.owner false).toReal) ^ time *
          (1 - quittingStationaryFixedOpponentsContinueMass
            (source.family.root (source.selected n)) source.owner) := by
  classical
  unfold QuittingUniqueExceptionalOwnerSource.ownerPrefixOpponentCharge
  apply Finset.sum_congr rfl
  intro time htime
  have htimeLe : time ≤ source.family.horizon (source.selected n) + 1 :=
    (Finset.mem_range.mp htime).le
  have htimeRoot : time ≤ source.family.horizon (source.selected n) :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp htime)
  rw [quittingJointSurvivalWeight_stationaryPrefixFamilyPlan
    source.family (source.selected n) time htimeLe]
  rw [quittingStationaryPrefixFamilyPlan_eq_root
    source.family (source.selected n) time htimeRoot]
  rw [quittingStationaryContinueMass_eq_deletedContinueMass_mul_own
    _ source.owner]
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass quittingRootDeletedContinueMass
    quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  rfl

/-- The competing-clock charge is the opponent/joint hazard ratio times the
probability that the repeated prefix absorbs. -/
theorem QuittingUniqueExceptionalOwnerSource.ownerPrefixOpponentCharge_eq_ratio
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward) (n : ℕ) :
    source.ownerPrefixOpponentCharge n =
      ((1 - quittingStationaryFixedOpponentsContinueMass
            (source.family.root (source.selected n)) source.owner) /
          (1 - quittingStationaryFixedOpponentsContinueMass
              (source.family.root (source.selected n)) source.owner *
            (source.family.root
              (source.selected n) source.owner false).toReal)) *
        (1 - source.family.prefixJointSurvival (source.selected n)) := by
  rw [source.ownerPrefixOpponentCharge_eq]
  unfold QuittingDiffuseStationaryPrefixFamily.prefixJointSurvival
  rw [quittingJointSurvivalWeight_eq_prod]
  simp only [Finset.prod_const, Finset.card_range]
  rw [quittingStationaryContinueMass_eq_deletedContinueMass_mul_own
    _ source.owner]
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass quittingRootDeletedContinueMass
  let d := quittingStationaryContinueMass
    (Function.update (source.family.root (source.selected n))
      source.owner (PMF.pure false))
  let c := (source.family.root
    (source.selected n) source.owner false).toReal
  let N := source.family.horizon (source.selected n) + 1
  change (∑ time ∈ Finset.range N, (d * c) ^ time * (1 - d)) =
    ((1 - d) / (1 - d * c)) * (1 - (d * c) ^ N)
  have hd0 : 0 ≤ d := quittingStationaryContinueMass_nonneg _
  have hd1 : d ≤ 1 := quittingStationaryContinueMass_le_one _
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hc1 : c ≤ 1 := by
    dsimp only [c]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      ((source.family.root (source.selected n) source.owner).coe_le_one false)
  by_cases hden : 1 - d * c = 0
  · have hd : d = 1 := by nlinarith
    simp [hd]
  · rw [← Finset.sum_mul]
    have hgeom := geom_sum_mul (d * c) N
    field_simp [hden]
    nlinarith

/-- The total probability charge of opponent absorption before the owner over
the entire selected prefix tends to zero.  This is stronger than the one-row
hazard conclusion: it controls a window whose length diverges. -/
theorem QuittingUniqueExceptionalOwnerSource.tendsto_ownerPrefixOpponentCharge_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward)
    (hhorizon : Tendsto
      (fun n ↦ source.family.horizon (source.selected n)) atTop atTop) :
    Tendsto source.ownerPrefixOpponentCharge atTop (nhds 0) := by
  have hratio := source.tendsto_ownerOpponentHazardRatio_zero hhorizon
  have habsorption : Tendsto (fun n ↦
      1 - source.family.prefixJointSurvival (source.selected n))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub source.joint_tendsto_zero
  have hproduct := hratio.mul habsorption
  norm_num at hproduct
  exact hproduct.congr' (Filter.Eventually.of_forall fun n ↦
    (source.ownerPrefixOpponentCharge_eq_ratio n).symm)

/-- The actual source plan's initial terminal value converges coordinatewise
to the exceptional owner's singleton reward.  This consumes the whole-prefix
charge theorem and the existing quiet-window payoff estimate. -/
theorem QuittingUniqueExceptionalOwnerSource.tendsto_initialValue_soloReward
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward)
    (hhorizon : Tendsto
      (fun n ↦ source.family.horizon (source.selected n)) atTop atTop)
    (who : ι) :
    Tendsto (fun n ↦ quittingStationaryPrefixFamilyValue source.family
      (source.selected n) 0 who) atTop
      (nhds (quittingSoloReward reward source.owner who)) := by
  let M := quittingRewardBound reward
  let bound : ℕ → ℝ := fun n ↦
    4 * M * source.ownerPrefixOpponentCharge n +
      2 * M * source.family.prefixJointSurvival (source.selected n)
  have hbound : Tendsto bound atTop (nhds 0) := by
    have hcharge :=
      (source.tendsto_ownerPrefixOpponentCharge_zero hhorizon).const_mul
        (4 * M)
    have hjoint := source.joint_tendsto_zero.const_mul (2 * M)
    simpa [bound] using hcharge.add hjoint
  have habs : Tendsto (fun n ↦
      |quittingStationaryPrefixFamilyValue source.family
          (source.selected n) 0 who -
        quittingSoloReward reward source.owner who|) atTop (nhds 0) := by
    apply squeeze_zero (g := bound)
    · intro n
      exact abs_nonneg _
    · intro n
      have hwindow :=
        abs_quittingRootSequenceTerminalValue_sub_soloReward_le_window
          reward
          (quittingStationaryPrefixFamilyPlan source.family
            (source.selected n)) source.owner who
          (abs_reward_le_quittingRewardBound reward)
          (source.family.horizon (source.selected n) + 1) 0
      have hprefix : quittingJointSurvivalWeight
          (quittingStationaryPrefixFamilyPlan source.family
            (source.selected n)) 0
          (source.family.horizon (source.selected n) + 1) =
          source.family.prefixJointSurvival (source.selected n) := by
        rw [quittingJointSurvivalWeight_stationaryPrefixFamilyPlan
          source.family (source.selected n)
          (source.family.horizon (source.selected n) + 1) le_rfl]
        unfold QuittingDiffuseStationaryPrefixFamily.prefixJointSurvival
        rw [quittingJointSurvivalWeight_eq_prod]
        simp
      rw [hprefix] at hwindow
      simpa [bound, M,
        QuittingUniqueExceptionalOwnerSource.ownerPrefixOpponentCharge,
        quittingStationaryPrefixFamilyValue,
        quittingRootSequenceTailVector] using hwindow
    · exact hbound
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa [Real.dist_eq] using habs

/-- The source sequence's global Nash inequality supplies the immediate-Quit
cap at the first repeated row, with its literal `2 * error` tolerance. -/
theorem QuittingUniqueExceptionalOwnerSource.fixedOpponentsQuitValue_le_initialValue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward) (n : ℕ)
    (who : ι) :
    quittingStationaryFixedOpponentsQuitValue reward
        (source.family.root (source.selected n)) who ≤
      quittingStationaryPrefixFamilyValue source.family
          (source.selected n) 0 who +
        2 * source.family.error (source.selected n) := by
  let roots := quittingStationaryPrefixFamilyPlan source.family
    (source.selected n)
  have hreach : 0 < quittingJointSurvivalWeight roots 0 0 := by
    simp [roots]
  have hendpoint :=
    isεQuittingRootEndpointNash_tailVector_of_isεQuittingRootSequenceNash
      reward roots (source.family.nash (source.selected n)) 0 hreach
  have hregret :=
    quittingLedgerQuitRegret_le_of_isεQuittingRootEndpointNash
      reward roots who 0 hendpoint
  unfold quittingLedgerQuitRegret at hregret
  simp only [quittingJointSurvivalWeight_zero_fuel, div_one] at hregret
  have hroot : roots 0 = source.family.root (source.selected n) :=
    quittingStationaryPrefixFamilyPlan_eq_root source.family
      (source.selected n) 0 (by omega)
  change quittingStationaryFixedOpponentsQuitValue reward (roots 0) who -
      quittingRootSequenceTerminalValue reward roots who 0 ≤
      2 * source.family.error (source.selected n) at hregret
  rw [hroot] at hregret
  change quittingStationaryFixedOpponentsQuitValue reward
        (source.family.root (source.selected n)) who -
      quittingStationaryPrefixFamilyValue source.family
        (source.selected n) 0 who ≤
      2 * source.family.error (source.selected n) at hregret
  linarith

/-- Error scale consumed by the solo-stationary fallback: twice the natural
quiet-window scale `2 * charge + terminal survival`. -/
def QuittingUniqueExceptionalOwnerSource.ownerPrefixFallbackScale
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward) (n : ℕ) : ℝ :=
  4 * source.ownerPrefixOpponentCharge n +
    2 * source.family.prefixJointSurvival (source.selected n)

theorem QuittingUniqueExceptionalOwnerSource.ownerPrefixFallbackScale_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward) (n : ℕ) :
    0 ≤ source.ownerPrefixFallbackScale n := by
  unfold QuittingUniqueExceptionalOwnerSource.ownerPrefixFallbackScale
  have hcharge : 0 ≤ source.ownerPrefixOpponentCharge n := by
    unfold QuittingUniqueExceptionalOwnerSource.ownerPrefixOpponentCharge
    apply Finset.sum_nonneg
    intro time _
    exact mul_nonneg (quittingJointSurvivalWeight_nonneg _ 0 time)
      (quittingRootOpponentAbsorptionMass_nonneg _ _)
  have hjoint :=
    source.family.prefixJointSurvival_mem_Icc (source.selected n) |>.1
  linarith

theorem QuittingUniqueExceptionalOwnerSource.tendsto_ownerPrefixFallbackScale_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward)
    (hhorizon : Tendsto
      (fun n ↦ source.family.horizon (source.selected n)) atTop atTop) :
    Tendsto source.ownerPrefixFallbackScale atTop (nhds 0) := by
  have hcharge :=
    (source.tendsto_ownerPrefixOpponentCharge_zero hhorizon).const_mul 4
  have hjoint := source.joint_tendsto_zero.const_mul 2
  change Tendsto (fun n ↦ 4 * source.ownerPrefixOpponentCharge n +
    2 * source.family.prefixJointSurvival (source.selected n)) atTop (nhds 0)
  simpa using hcharge.add hjoint

/-- Quantitative form of initial-value concentration, normalized at exactly
the scale accepted by the exceptional solo-stationary fallback. -/
theorem QuittingUniqueExceptionalOwnerSource.abs_initialValue_sub_soloReward_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward) (n : ℕ)
    (who : ι) :
    |quittingStationaryPrefixFamilyValue source.family
        (source.selected n) 0 who -
      quittingSoloReward reward source.owner who| ≤
        quittingRewardBound reward * source.ownerPrefixFallbackScale n := by
  have hwindow :=
    abs_quittingRootSequenceTerminalValue_sub_soloReward_le_window
      reward
      (quittingStationaryPrefixFamilyPlan source.family (source.selected n))
      source.owner who (abs_reward_le_quittingRewardBound reward)
      (source.family.horizon (source.selected n) + 1) 0
  have hprefix : quittingJointSurvivalWeight
      (quittingStationaryPrefixFamilyPlan source.family (source.selected n)) 0
      (source.family.horizon (source.selected n) + 1) =
      source.family.prefixJointSurvival (source.selected n) := by
    rw [quittingJointSurvivalWeight_stationaryPrefixFamilyPlan
      source.family (source.selected n)
      (source.family.horizon (source.selected n) + 1) le_rfl]
    unfold QuittingDiffuseStationaryPrefixFamily.prefixJointSurvival
    rw [quittingJointSurvivalWeight_eq_prod]
    simp
  rw [hprefix] at hwindow
  change |quittingStationaryPrefixFamilyValue source.family
      (source.selected n) 0 who -
      quittingSoloReward reward source.owner who| ≤ _ at hwindow
  calc
    _ ≤ 4 * quittingRewardBound reward *
          source.ownerPrefixOpponentCharge n +
        2 * quittingRewardBound reward *
          source.family.prefixJointSurvival (source.selected n) := by
      simpa [QuittingUniqueExceptionalOwnerSource.ownerPrefixOpponentCharge]
        using hwindow
    _ = quittingRewardBound reward * source.ownerPrefixFallbackScale n := by
      unfold QuittingUniqueExceptionalOwnerSource.ownerPrefixFallbackScale
      ring

/-- The fallback scale dominates the current row's opponent hazard because
the stage-zero term occurs in the prefix charge. -/
theorem QuittingUniqueExceptionalOwnerSource.ownerOpponentHazard_le_fallbackScale
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward) (n : ℕ) :
    1 - quittingStationaryFixedOpponentsContinueMass
        (source.family.root (source.selected n)) source.owner ≤
      source.ownerPrefixFallbackScale n := by
  let roots := quittingStationaryPrefixFamilyPlan source.family
    (source.selected n)
  have hwindow : 0 < source.family.horizon (source.selected n) + 1 := by omega
  have hmem : 0 ∈ Finset.range
      (source.family.horizon (source.selected n) + 1) :=
    Finset.mem_range.mpr hwindow
  have hcharge0 : ∀ time ∈ Finset.range
      (source.family.horizon (source.selected n) + 1),
      0 ≤ quittingJointSurvivalWeight roots 0 time *
        quittingRootOpponentAbsorptionMass (roots time) source.owner := by
    intro time _
    exact mul_nonneg (quittingJointSurvivalWeight_nonneg _ 0 time)
      (quittingRootOpponentAbsorptionMass_nonneg _ _)
  have hsingle := Finset.single_le_sum hcharge0 hmem
  have hroot : roots 0 = source.family.root (source.selected n) :=
    quittingStationaryPrefixFamilyPlan_eq_root source.family
      (source.selected n) 0 (by omega)
  rw [quittingJointSurvivalWeight_zero_fuel, one_mul, hroot] at hsingle
  have hcharge : quittingRootOpponentAbsorptionMass
      (source.family.root (source.selected n)) source.owner ≤
      source.ownerPrefixOpponentCharge n := by
    simpa [QuittingUniqueExceptionalOwnerSource.ownerPrefixOpponentCharge,
      roots] using hsingle
  have hchargeNonneg : 0 ≤ source.ownerPrefixOpponentCharge n :=
    (quittingRootOpponentAbsorptionMass_nonneg _ _).trans hcharge
  have hjoint :=
    source.family.prefixJointSurvival_mem_Icc (source.selected n) |>.1
  change quittingRootOpponentAbsorptionMass
      (source.family.root (source.selected n)) source.owner ≤ _
  unfold QuittingUniqueExceptionalOwnerSource.ownerPrefixFallbackScale
  linarith

/-- At every selected row where the exceptional owner has positive Quit
probability, the source's initial Nash and concentration estimates compile to
a solo stationary approximate equilibrium.  Nonnegativity of the owner's
solo self-payoff is the remaining strategic hypothesis. -/
theorem QuittingUniqueExceptionalOwnerSource.isεAsymptoticNash_soloStationary
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward)
    (hsoloSelf : 0 ≤ quittingSoloReward reward source.owner source.owner)
    (n : ℕ)
    (hpositive : 0 <
      (source.family.root (source.selected n) source.owner true).toReal) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (2 * source.family.error (source.selected n) +
        4 * quittingRewardBound reward * source.ownerPrefixFallbackScale n)
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot source.owner
          (source.family.root (source.selected n) source.owner))) := by
  let root := source.family.root (source.selected n)
  let value := quittingStationaryPrefixFamilyValue source.family
    (source.selected n) 0
  let β := 2 * source.family.error (source.selected n)
  let M := quittingRewardBound reward
  let η := source.ownerPrefixFallbackScale n
  have hβ : 0 ≤ β := by
    dsimp only [β]
    exact mul_nonneg (by norm_num)
      (source.family.error_pos (source.selected n)).le
  have hη : 0 ≤ η := by
    exact source.ownerPrefixFallbackScale_nonneg n
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  apply isεAsymptoticNash_soloStationary_of_tail_bounds_of_hazard
    reward root value source.owner hβ hη
      (abs_reward_le_quittingRewardBound reward)
  · exact source.ownerOpponentHazard_le_fallbackScale n
  · exact hpositive
  · intro who
    have hconcentration := source.abs_initialValue_sub_soloReward_le n who
    change |value who - quittingSoloReward reward source.owner who| ≤
      2 * M * η
    change |value who - quittingSoloReward reward source.owner who| ≤
      M * η at hconcentration
    nlinarith [mul_nonneg hM hη]
  · have hconcentration :=
      source.abs_initialValue_sub_soloReward_le n source.owner
    change -M * η ≤ value source.owner + β
    change |value source.owner -
        quittingSoloReward reward source.owner source.owner| ≤ M * η
      at hconcentration
    have hlower := (abs_le.mp hconcentration).1
    nlinarith
  · intro who hne
    exact source.fixedOpponentsQuitValue_le_initialValue n who

/-- A divergent exceptional-owner source closes branch `S.1` whenever the
exceptional owner's singleton self-payoff is nonnegative.  Thus the genuine
remaining unique-owner obstruction is the negative-solo-owner regime, not
probabilistic isolation or spectator Quit deviations. -/
theorem QuittingUniqueExceptionalOwnerSource.stationaryεEquilibriumExistence_of_nonnegSolo
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward)
    (hhorizon : Tendsto
      (fun n ↦ source.family.horizon (source.selected n)) atTop atTop)
    (hsoloSelf : 0 ≤ quittingSoloReward reward source.owner source.owner) :
    QuittingStationaryεEquilibriumExistence reward := by
  intro target htarget
  let totalError : ℕ → ℝ := fun n ↦
    2 * source.family.error (source.selected n) +
      4 * quittingRewardBound reward * source.ownerPrefixFallbackScale n
  have hsourceError : Tendsto (fun n ↦
      2 * source.family.error (source.selected n)) atTop (nhds 0) := by
    simpa using (source.family.error_tendsto_zero.comp
      source.selected_strictMono.tendsto_atTop).const_mul 2
  have hfallbackError : Tendsto (fun n ↦
      4 * quittingRewardBound reward * source.ownerPrefixFallbackScale n)
      atTop (nhds 0) := by
    simpa using
      (source.tendsto_ownerPrefixFallbackScale_zero hhorizon).const_mul
        (4 * quittingRewardBound reward)
  have htotalError : Tendsto totalError atTop (nhds 0) := by
    simpa [totalError] using hsourceError.add hfallbackError
  have hsmall : ∀ᶠ n in atTop, totalError n < target :=
    (tendsto_order.1 htotalError).2 target htarget
  obtain ⟨n, hpositive, herror⟩ :=
    (source.eventually_ownerQuitProbability_pos.and hsmall).exists
  refine ⟨quittingSoloStationaryRoot source.owner
    (source.family.root (source.selected n) source.owner), ?_⟩
  have hnash := source.isεAsymptoticNash_soloStationary hsoloSelf n hpositive
  exact hnash.mono (le_of_lt (by simpa [totalError] using herror))

/-- Exact residual after consuming a divergent exceptional-owner source: it
either yields the stationary branch, or its unique owner has strictly negative
singleton self-payoff. -/
theorem QuittingUniqueExceptionalOwnerSource.stationary_or_negativeSolo
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward)
    (hhorizon : Tendsto
      (fun n ↦ source.family.horizon (source.selected n)) atTop atTop) :
    QuittingStationaryεEquilibriumExistence reward ∨
      quittingSoloReward reward source.owner source.owner < 0 := by
  by_cases hsolo : 0 ≤ quittingSoloReward reward source.owner source.owner
  · exact Or.inl
      (source.stationaryεEquilibriumExistence_of_nonnegSolo hhorizon hsolo)
  · exact Or.inr (lt_of_not_ge hsolo)

end GameTheory
