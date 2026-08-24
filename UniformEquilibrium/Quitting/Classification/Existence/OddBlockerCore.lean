/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Stationary.HeterogeneousConstrainedFaceNash
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler

/-!
# A three-player odd blocker core with arbitrary outside coordinates

This file proves the first odd-blocker-core escape.  Three distinct core
players have passive Continue faces and cyclic strict Quit faces.  Every
other player's reward coordinate is unrestricted.  A constrained stationary
Nash construction, compact limit, and the odd three-cycle exclude boundary
rates for the core.  The resulting gain-complementary product root is compiled
to an exact terminal Nash profile against arbitrary behavioral deviations and
to a uniform-equilibrium payoff.

The source predicate below is stated in the polynomial stationary-face
language.  It is literal reward-table data: `sigmaValue`, `excludedValue`, and
`continueMassExcl` are finite Bernoulli sums.  A separate rowwise adapter from
the simpler coalition inequalities remains useful, but is not assumed by the
consumer theorem proved here.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The three-core source predicate -/

/-- Stationary-face form of a passive strict three-cycle blocker core.
Outside-player reward coordinates are not mentioned and are unrestricted. -/
structure IsStrictThreeBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (first second third : ι) : Prop where
  first_ne_second : first ≠ second
  second_ne_third : second ≠ third
  third_ne_first : third ≠ first
  passive_first : ∀ hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    excludedValue (weightOfReward reward) hazard first =
      (1 - continueMassExcl hazard first) * baseline first
  passive_second : ∀ hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    excludedValue (weightOfReward reward) hazard second =
      (1 - continueMassExcl hazard second) * baseline second
  passive_third : ∀ hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    excludedValue (weightOfReward reward) hazard third =
      (1 - continueMassExcl hazard third) * baseline third
  first_lower : ∀ hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    hazard second = 0 →
      baseline first < sigmaValue (weightOfReward reward) hazard first
  first_upper : ∀ hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    hazard second = 1 →
      sigmaValue (weightOfReward reward) hazard first < baseline first
  second_lower : ∀ hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    hazard third = 0 →
      baseline second < sigmaValue (weightOfReward reward) hazard second
  second_upper : ∀ hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    hazard third = 1 →
      sigmaValue (weightOfReward reward) hazard second < baseline second
  third_lower : ∀ hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    hazard first = 0 →
      baseline third < sigmaValue (weightOfReward reward) hazard third
  third_upper : ∀ hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    hazard first = 1 →
      sigmaValue (weightOfReward reward) hazard third < baseline third

/-- The three structured players. -/
def threeBlockerCore (first second third : ι) : Finset ι :=
  {first, second, third}

/-- The vanishing lower constraint is imposed exactly on the structured
three-player core. -/
def threeCoreLower (first second third : ι) (epsilon : ℝ) (who : ι) : ℝ :=
  if who ∈ threeBlockerCore first second third then epsilon else 0

omit [Fintype ι] in
@[simp] theorem threeCoreLower_first
    (first second third : ι) (epsilon : ℝ) :
    threeCoreLower first second third epsilon first = epsilon := by
  simp [threeCoreLower, threeBlockerCore]

omit [Fintype ι] in
@[simp] theorem threeCoreLower_second
    (first second third : ι) (epsilon : ℝ) :
    threeCoreLower first second third epsilon second = epsilon := by
  simp [threeCoreLower, threeBlockerCore]

omit [Fintype ι] in
@[simp] theorem threeCoreLower_third
    (first second third : ι) (epsilon : ℝ) :
    threeCoreLower first second third epsilon third = epsilon := by
  simp [threeCoreLower, threeBlockerCore]

omit [Fintype ι] in
theorem threeCoreLower_nonneg
    (first second third : ι) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (who : ι) :
    0 ≤ threeCoreLower first second third epsilon who := by
  simp only [threeCoreLower]
  split_ifs
  · exact hepsilon
  · exact le_rfl

omit [Fintype ι] in
theorem threeCoreLower_le_one
    (first second third : ι) {epsilon : ℝ} (hepsilon : epsilon ≤ 1) (who : ι) :
    threeCoreLower first second third epsilon who ≤ 1 := by
  simp only [threeCoreLower]
  split_ifs
  · exact hepsilon
  · norm_num

/-! ## Elementary face and compactness lemmas -/

/-- The positive vanishing constraint used in the compact construction. -/
def oddCoreEpsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem oddCoreEpsilon_pos (n : ℕ) : 0 < oddCoreEpsilon n := by
  unfold oddCoreEpsilon
  positivity

theorem oddCoreEpsilon_le_one (n : ℕ) : oddCoreEpsilon n ≤ 1 := by
  unfold oddCoreEpsilon
  apply (div_le_one (by positivity)).2
  exact_mod_cast (show (1 : ℕ) ≤ n + 1 by omega)

theorem oddCoreEpsilon_tendsto_zero :
    Tendsto oddCoreEpsilon atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- One positive opponent hazard makes the deleted Continue product strictly
smaller than one. -/
theorem continueMassExcl_lt_one_of_positive_opponent
    (hazard : ι → ℝ) (hhazard0 : ∀ who, 0 ≤ hazard who)
    (hhazard1 : ∀ who, hazard who ≤ 1)
    {who other : ι} (hne : other ≠ who) (hpositive : 0 < hazard other) :
    continueMassExcl hazard who < 1 := by
  unfold continueMassExcl
  apply Math.Finset.prod_lt_one_of_mem
    (Finset.univ.erase who) (fun player => 1 - hazard player) other
  · simp [hne]
  · intro player _ _
    linarith [hhazard1 player]
  · intro player _ _
    linarith [hhazard0 player]
  · linarith

/-- Passive continuation rewrites the face numerator as opponent absorption
times the Quit-endpoint excess over baseline. -/
theorem quittingFaceNumerator_eq_absorption_mul_sub_of_passive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (hazard : ι → ℝ) (who : ι)
    (hpassive : excludedValue (weightOfReward reward) hazard who =
      (1 - continueMassExcl hazard who) * baseline who) :
    quittingFaceNumerator (weightOfReward reward) hazard who =
      (1 - continueMassExcl hazard who) *
        (sigmaValue (weightOfReward reward) hazard who - baseline who) := by
  unfold quittingFaceNumerator
  rw [hpassive]
  ring

/-- A strict lower Quit face gives positive stationary gain whenever some
opponent has positive hazard. -/
theorem quittingFaceNumerator_pos_of_passive_of_sigma_gt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (hazard : ι → ℝ) (who : ι)
    (hcontracts : continueMassExcl hazard who < 1)
    (hpassive : excludedValue (weightOfReward reward) hazard who =
      (1 - continueMassExcl hazard who) * baseline who)
    (hsigma : baseline who <
      sigmaValue (weightOfReward reward) hazard who) :
    0 < quittingFaceNumerator (weightOfReward reward) hazard who := by
  rw [quittingFaceNumerator_eq_absorption_mul_sub_of_passive
    reward baseline hazard who hpassive]
  exact mul_pos (sub_pos.mpr hcontracts) (sub_pos.mpr hsigma)

/-- A strict upper Quit face gives negative stationary gain whenever some
opponent has positive hazard. -/
theorem quittingFaceNumerator_neg_of_passive_of_sigma_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (hazard : ι → ℝ) (who : ι)
    (hcontracts : continueMassExcl hazard who < 1)
    (hpassive : excludedValue (weightOfReward reward) hazard who =
      (1 - continueMassExcl hazard who) * baseline who)
    (hsigma : sigmaValue (weightOfReward reward) hazard who <
      baseline who) :
    quittingFaceNumerator (weightOfReward reward) hazard who < 0 := by
  rw [quittingFaceNumerator_eq_absorption_mul_sub_of_passive
    reward baseline hazard who hpassive]
  exact mul_neg_of_pos_of_neg (sub_pos.mpr hcontracts) (sub_neg.mpr hsigma)

omit [Fintype ι] [DecidableEq ι] in
/-- Positive auxiliary gain forces the constrained coordinate to the upper
endpoint. -/
theorem eq_one_of_constrainedFaceNash_of_pos
    {lower : ι → ℝ} {hazard : ι → ℝ} {gain : ι → ℝ} (who : ι)
    (hlower1 : lower who ≤ 1) (hhazard1 : hazard who ≤ 1)
    (hbest : ∀ rate, lower who ≤ rate → rate ≤ 1 →
      rate * gain who ≤ hazard who * gain who)
    (hgain : 0 < gain who) :
    hazard who = 1 := by
  have h := hbest 1 hlower1 le_rfl
  nlinarith

omit [Fintype ι] [DecidableEq ι] in
/-- Negative auxiliary gain forces the constrained coordinate to its lower
endpoint. -/
theorem eq_lower_of_constrainedFaceNash_of_neg
    {lower : ι → ℝ} {hazard : ι → ℝ} {gain : ι → ℝ} (who : ι)
    (hhazard0 : lower who ≤ hazard who)
    (hbest : ∀ rate, lower who ≤ rate → rate ≤ 1 →
      rate * gain who ≤ hazard who * gain who)
    (hlower1 : lower who ≤ 1) (hgain : gain who < 0) :
    hazard who = lower who := by
  have h := hbest (lower who) le_rfl hlower1
  nlinarith

/-! ## The compact odd-core construction -/

/-- Complete source-to-consumer output for the strict three-blocker core. -/
structure ThreeBlockerCoreStationaryCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (first second third : ι) where
  root : ι → PMF Bool
  value : Payoff ι
  first_hazard_pos : 0 < hazardOfRoot root first
  first_hazard_lt_one : hazardOfRoot root first < 1
  second_hazard_pos : 0 < hazardOfRoot root second
  second_hazard_lt_one : hazardOfRoot root second < 1
  third_hazard_pos : 0 < hazardOfRoot root third
  third_hazard_lt_one : hazardOfRoot root third < 1
  first_value : value first = baseline first
  second_value : value second = baseline second
  third_value : value third = baseline third
  fixedPoint : value = quittingRootSuccessorPayoff reward value root
  endpointNash : IsεQuittingRootEndpointNash reward value 0 root
  jointlyContracts : quittingStationaryContinueMass root < 1
  opponentsContract : ∀ who,
    quittingStationaryFixedOpponentsContinueMass root who < 1
  terminalPayoff_eq : quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) = value
  terminalNash : (quittingGame reward).IsεAsymptoticNash
    (quittingTerminalPayoff reward) 0
    (quittingStationaryProfile reward root)
  uniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none value

/-- **Three-player odd blocker core with arbitrary calibrators.**  A strict
passive cyclic core on three distinct players has a stationary exact terminal
Nash profile against arbitrary unilateral behavioral replacement.  No
condition is imposed on any outside player's payoff coordinate. -/
theorem exists_stationaryCertificate_of_strictThreeBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (first second third : ι)
    (hcore : IsStrictThreeBlockerCore reward baseline first second third) :
    Nonempty (ThreeBlockerCoreStationaryCertificate
      reward baseline first second third) := by
  letI : Nonempty ι := ⟨first⟩
  let lower : ℕ → ι → ℝ := fun n =>
    threeCoreLower first second third (oddCoreEpsilon n)
  have hlower0 : ∀ n who, 0 ≤ lower n who := fun n who =>
    threeCoreLower_nonneg first second third (oddCoreEpsilon_pos n).le who
  have hlower1 : ∀ n who, lower n who ≤ 1 := fun n who =>
    threeCoreLower_le_one first second third (oddCoreEpsilon_le_one n) who
  have hexists : ∀ n, ∃ hazard : ι → ℝ,
      (∀ who, lower n who ≤ hazard who) ∧
      (∀ who, hazard who ≤ 1) ∧
      ∀ who rate, lower n who ≤ rate → rate ≤ 1 →
        rate * quittingFaceNumerator (weightOfReward reward) hazard who ≤
          hazard who *
            quittingFaceNumerator (weightOfReward reward) hazard who := fun n =>
    exists_heterogeneousStationaryFaceNash reward (lower n) (hlower1 n)
  choose hazard hhazardLower hhazardUpper hbest using hexists
  have hhazard0 : ∀ n who, 0 ≤ hazard n who := fun n who =>
    (hlower0 n who).trans (hhazardLower n who)
  let cubeHazard : ℕ → ι → Set.Icc (0 : ℝ) 1 := fun n who =>
    ⟨hazard n who, hhazard0 n who, hhazardUpper n who⟩
  obtain ⟨limitCube, subsequence, hsubsequence, hcubeLimit⟩ :=
    CompactSpace.tendsto_subseq cubeHazard
  let limit : ι → ℝ := fun who => (limitCube who).val
  have hsubsequenceAtTop : Tendsto subsequence atTop atTop :=
    hsubsequence.tendsto_atTop
  have hepsilonLimit : Tendsto (fun n => oddCoreEpsilon (subsequence n))
      atTop (nhds 0) :=
    oddCoreEpsilon_tendsto_zero.comp hsubsequenceAtTop
  have hhazardLimit : Tendsto (fun n => hazard (subsequence n))
      atTop (nhds limit) := by
    rw [tendsto_pi_nhds]
    intro who
    have hprojection : Continuous
        (fun point : ι → Set.Icc (0 : ℝ) 1 => (point who).val) :=
      continuous_subtype_val.comp (continuous_apply who)
    have hcoordinate : Tendsto
        (fun n => (cubeHazard (subsequence n) who).val)
        atTop (nhds (limitCube who).val) := by
      simpa only [Function.comp_def] using
        (hprojection.tendsto limitCube).comp hcubeLimit
    simpa only [cubeHazard, limit] using hcoordinate
  have hhazardLimitCoord : ∀ who, Tendsto
      (fun n => hazard (subsequence n) who) atTop (nhds (limit who)) := by
    intro who
    exact tendsto_pi_nhds.mp hhazardLimit who
  have hlimit0 : ∀ who, 0 ≤ limit who := fun who => (limitCube who).property.1
  have hlimit1 : ∀ who, limit who ≤ 1 := fun who => (limitCube who).property.2
  have hsigmaLimit : ∀ who, Tendsto
      (fun n => sigmaValue (weightOfReward reward)
        (hazard (subsequence n)) who)
      atTop (nhds (sigmaValue (weightOfReward reward) limit who)) := by
    intro who
    exact ((continuous_sigmaValue (weightOfReward reward) who).tendsto limit).comp
      hhazardLimit
  have hlimitLower : ∀ who, Tendsto
      (fun n => lower (subsequence n) who) atTop (nhds 0) := by
    intro who
    by_cases hmem : who ∈ threeBlockerCore first second third
    · simpa [lower, threeCoreLower, hmem] using hepsilonLimit
    · simp [lower, threeCoreLower, hmem]
  have hcontractAt : ∀ n who,
      continueMassExcl (hazard (subsequence n)) who < 1 := by
    intro n who
    by_cases hwho : who = first
    · subst who
      exact continueMassExcl_lt_one_of_positive_opponent
        (hazard (subsequence n)) (hhazard0 (subsequence n))
        (hhazardUpper (subsequence n)) hcore.first_ne_second.symm
        ((oddCoreEpsilon_pos (subsequence n)).trans_le (by
          simpa [lower] using hhazardLower (subsequence n) second))
    · exact continueMassExcl_lt_one_of_positive_opponent
        (hazard (subsequence n)) (hhazard0 (subsequence n))
        (hhazardUpper (subsequence n)) (Ne.symm hwho)
        ((oddCoreEpsilon_pos (subsequence n)).trans_le (by
          simpa [lower] using hhazardLower (subsequence n) first))
  have hforceOne : ∀ owner blocker,
      (∀ h, (∀ who, 0 ≤ h who) → (∀ who, h who ≤ 1) →
        h blocker = 0 → baseline owner <
          sigmaValue (weightOfReward reward) h owner) →
      (∀ h, (∀ who, 0 ≤ h who) → (∀ who, h who ≤ 1) →
        excludedValue (weightOfReward reward) h owner =
          (1 - continueMassExcl h owner) * baseline owner) →
      limit blocker = 0 → limit owner = 1 := by
    intro owner blocker hlowerFace hpassive hblocker
    have hstrict : baseline owner <
        sigmaValue (weightOfReward reward) limit owner :=
      hlowerFace limit hlimit0 hlimit1 hblocker
    have heventuallySigma : ∀ᶠ n in atTop, baseline owner <
        sigmaValue (weightOfReward reward) (hazard (subsequence n)) owner :=
      (tendsto_order.1 (hsigmaLimit owner)).1 _ hstrict
    have heventuallyOne : ∀ᶠ n in atTop,
        hazard (subsequence n) owner = 1 := by
      filter_upwards [heventuallySigma] with n hsigma
      apply eq_one_of_constrainedFaceNash_of_pos owner
        (hlower1 (subsequence n) owner) (hhazardUpper (subsequence n) owner)
      · exact hbest (subsequence n) owner
      · exact quittingFaceNumerator_pos_of_passive_of_sigma_gt
          reward baseline (hazard (subsequence n)) owner
          (hcontractAt n owner)
          (hpassive (hazard (subsequence n))
            (hhazard0 (subsequence n)) (hhazardUpper (subsequence n))) hsigma
    exact tendsto_nhds_unique (hhazardLimitCoord owner)
      (tendsto_const_nhds.congr' (heventuallyOne.mono fun n hn => hn.symm))
  have hforceZero : ∀ owner blocker,
      (∀ h, (∀ who, 0 ≤ h who) → (∀ who, h who ≤ 1) →
        h blocker = 1 →
          sigmaValue (weightOfReward reward) h owner < baseline owner) →
      (∀ h, (∀ who, 0 ≤ h who) → (∀ who, h who ≤ 1) →
        excludedValue (weightOfReward reward) h owner =
          (1 - continueMassExcl h owner) * baseline owner) →
      limit blocker = 1 → limit owner = 0 := by
    intro owner blocker hupperFace hpassive hblocker
    have hstrict : sigmaValue (weightOfReward reward) limit owner <
        baseline owner := hupperFace limit hlimit0 hlimit1 hblocker
    have heventuallySigma : ∀ᶠ n in atTop,
        sigmaValue (weightOfReward reward) (hazard (subsequence n)) owner <
          baseline owner :=
      (tendsto_order.1 (hsigmaLimit owner)).2 _ hstrict
    have heventuallyLower : ∀ᶠ n in atTop,
        hazard (subsequence n) owner = lower (subsequence n) owner := by
      filter_upwards [heventuallySigma] with n hsigma
      apply eq_lower_of_constrainedFaceNash_of_neg owner
        (hhazardLower (subsequence n) owner)
        (hbest (subsequence n) owner) (hlower1 (subsequence n) owner)
      exact quittingFaceNumerator_neg_of_passive_of_sigma_lt
        reward baseline (hazard (subsequence n)) owner
        (hcontractAt n owner)
        (hpassive (hazard (subsequence n))
          (hhazard0 (subsequence n)) (hhazardUpper (subsequence n))) hsigma
    have hsameLimit : Tendsto (fun n => hazard (subsequence n) owner)
        atTop (nhds 0) :=
      (hlimitLower owner).congr'
        (heventuallyLower.mono fun n hn => hn.symm)
    exact tendsto_nhds_unique (hhazardLimitCoord owner) hsameLimit
  have hfirstZeroToThirdOne : limit first = 0 → limit third = 1 :=
    hforceOne third first hcore.third_lower hcore.passive_third
  have hthirdOneToSecondZero : limit third = 1 → limit second = 0 :=
    hforceZero second third hcore.second_upper hcore.passive_second
  have hsecondZeroToFirstOne : limit second = 0 → limit first = 1 :=
    hforceOne first second hcore.first_lower hcore.passive_first
  have hfirst_ne_zero : limit first ≠ 0 := by
    intro hfirst
    have hthird := hfirstZeroToThirdOne hfirst
    have hsecond := hthirdOneToSecondZero hthird
    have hfirstOne := hsecondZeroToFirstOne hsecond
    linarith
  have hsecond_ne_zero : limit second ≠ 0 := by
    intro hsecond
    have hfirst := hsecondZeroToFirstOne hsecond
    have hthirdZero := hforceZero third first hcore.third_upper
      hcore.passive_third hfirst
    have hsecondOne := hforceOne second third hcore.second_lower
      hcore.passive_second hthirdZero
    linarith
  have hthird_ne_zero : limit third ≠ 0 := by
    intro hthird
    have hsecondOne := hforceOne second third hcore.second_lower
      hcore.passive_second hthird
    have hfirstZero := hforceZero first second hcore.first_upper
      hcore.passive_first hsecondOne
    have hthirdOne := hfirstZeroToThirdOne hfirstZero
    linarith
  have hfirstPos : 0 < limit first := lt_of_le_of_ne (hlimit0 first) hfirst_ne_zero.symm
  have hsecondPos : 0 < limit second :=
    lt_of_le_of_ne (hlimit0 second) hsecond_ne_zero.symm
  have hthirdPos : 0 < limit third := lt_of_le_of_ne (hlimit0 third) hthird_ne_zero.symm
  have hfirstLt : limit first < 1 := by
    apply lt_of_le_of_ne (hlimit1 first)
    intro hfirst
    have hthirdZero := hforceZero third first hcore.third_upper
      hcore.passive_third hfirst
    exact hthird_ne_zero hthirdZero
  have hsecondLt : limit second < 1 := by
    apply lt_of_le_of_ne (hlimit1 second)
    intro hsecond
    have hfirstZero := hforceZero first second hcore.first_upper
      hcore.passive_first hsecond
    exact hfirst_ne_zero hfirstZero
  have hthirdLt : limit third < 1 := by
    apply lt_of_le_of_ne (hlimit1 third)
    intro hthird
    have hsecondZero := hforceZero second third hcore.second_upper
      hcore.passive_second hthird
    exact hsecond_ne_zero hsecondZero
  have hgainLimit : ∀ who, Tendsto
      (fun n => quittingFaceNumerator (weightOfReward reward)
        (hazard (subsequence n)) who)
      atTop (nhds (quittingFaceNumerator
        (weightOfReward reward) limit who)) := by
    intro who
    exact ((continuous_quittingFaceNumerator
      (weightOfReward reward) who).tendsto limit).comp hhazardLimit
  have hcoreGainZero : ∀ owner,
      0 < limit owner → limit owner < 1 →
      quittingFaceNumerator (weightOfReward reward) limit owner = 0 := by
    intro owner hownerPos hownerLt
    apply le_antisymm
    · by_contra hnot
      have hgainPos : 0 < quittingFaceNumerator
          (weightOfReward reward) limit owner := lt_of_not_ge hnot
      have heventuallyGain : ∀ᶠ n in atTop,
          0 < quittingFaceNumerator (weightOfReward reward)
            (hazard (subsequence n)) owner :=
        (tendsto_order.1 (hgainLimit owner)).1 0 hgainPos
      have heventuallyOne : ∀ᶠ n in atTop,
          hazard (subsequence n) owner = 1 := by
        filter_upwards [heventuallyGain] with n hgain
        exact eq_one_of_constrainedFaceNash_of_pos owner
          (hlower1 (subsequence n) owner)
          (hhazardUpper (subsequence n) owner)
          (hbest (subsequence n) owner) hgain
      have honeLimit : Tendsto (fun n => hazard (subsequence n) owner)
          atTop (nhds 1) :=
        tendsto_const_nhds.congr'
          (heventuallyOne.mono fun n hn => hn.symm)
      have : limit owner = 1 :=
        tendsto_nhds_unique (hhazardLimitCoord owner) honeLimit
      linarith
    · by_contra hnot
      have hgainNeg : quittingFaceNumerator
          (weightOfReward reward) limit owner < 0 := lt_of_not_ge hnot
      have heventuallyGain : ∀ᶠ n in atTop,
          quittingFaceNumerator (weightOfReward reward)
            (hazard (subsequence n)) owner < 0 :=
        (tendsto_order.1 (hgainLimit owner)).2 0 hgainNeg
      have heventuallyLower : ∀ᶠ n in atTop,
          hazard (subsequence n) owner = lower (subsequence n) owner := by
        filter_upwards [heventuallyGain] with n hgain
        exact eq_lower_of_constrainedFaceNash_of_neg owner
          (hhazardLower (subsequence n) owner)
          (hbest (subsequence n) owner)
          (hlower1 (subsequence n) owner) hgain
      have hzeroLimit : Tendsto (fun n => hazard (subsequence n) owner)
          atTop (nhds 0) :=
        (hlimitLower owner).congr'
          (heventuallyLower.mono fun n hn => hn.symm)
      have : limit owner = 0 :=
        tendsto_nhds_unique (hhazardLimitCoord owner) hzeroLimit
      linarith
  have hfirstGain : quittingFaceNumerator
      (weightOfReward reward) limit first = 0 :=
    hcoreGainZero first hfirstPos hfirstLt
  have hsecondGain : quittingFaceNumerator
      (weightOfReward reward) limit second = 0 :=
    hcoreGainZero second hsecondPos hsecondLt
  have hthirdGain : quittingFaceNumerator
      (weightOfReward reward) limit third = 0 :=
    hcoreGainZero third hthirdPos hthirdLt
  have hlimitBestOutside : ∀ who,
      who ∉ threeBlockerCore first second third →
      (1 - limit who) *
          quittingFaceNumerator (weightOfReward reward) limit who ≤ 0 ∧
        0 ≤ limit who *
          quittingFaceNumerator (weightOfReward reward) limit who := by
    intro who houtside
    have hlowerWho : ∀ n, lower n who = 0 := by
      intro n
      simp [lower, threeCoreLower, houtside]
    have heventuallyContinue : ∀ n,
        (1 - hazard (subsequence n) who) *
            quittingFaceNumerator (weightOfReward reward)
              (hazard (subsequence n)) who ≤ 0 := by
      intro n
      have h := hbest (subsequence n) who 1
        (hlower1 (subsequence n) who) le_rfl
      nlinarith
    have heventuallyQuit : ∀ n,
        0 ≤ hazard (subsequence n) who *
          quittingFaceNumerator (weightOfReward reward)
            (hazard (subsequence n)) who := by
      intro n
      have h := hbest (subsequence n) who 0
        (by rw [hlowerWho]) (by norm_num)
      simpa using h
    have hcontinueLimit : Tendsto
        (fun n => (1 - hazard (subsequence n) who) *
          quittingFaceNumerator (weightOfReward reward)
            (hazard (subsequence n)) who)
        atTop (nhds ((1 - limit who) *
          quittingFaceNumerator (weightOfReward reward) limit who)) :=
      ((tendsto_const_nhds.sub (hhazardLimitCoord who)).mul (hgainLimit who))
    have hquitLimit : Tendsto
        (fun n => hazard (subsequence n) who *
          quittingFaceNumerator (weightOfReward reward)
            (hazard (subsequence n)) who)
        atTop (nhds (limit who *
          quittingFaceNumerator (weightOfReward reward) limit who)) :=
      (hhazardLimitCoord who).mul (hgainLimit who)
    constructor
    · exact le_of_tendsto' hcontinueLimit heventuallyContinue
    · exact ge_of_tendsto' hquitLimit heventuallyQuit
  have hlimitComplementary : ∀ who,
      (1 - limit who) *
          quittingFaceNumerator (weightOfReward reward) limit who ≤ 0 ∧
        0 ≤ limit who *
          quittingFaceNumerator (weightOfReward reward) limit who := by
    intro who
    by_cases hfirst : who = first
    · subst who
      simp [hfirstGain]
    · by_cases hsecond : who = second
      · subst who
        simp [hsecondGain]
      · by_cases hthird : who = third
        · subst who
          simp [hthirdGain]
        · exact hlimitBestOutside who (by
            simp [threeBlockerCore, hfirst, hsecond, hthird])
  let root := rootOfHazard limit hlimit0 hlimit1
  have hgainComplementary : IsQuittingStationaryGainComplementary reward root := by
    intro who
    rw [stationaryGain_rootOfHazard_eq_faceNumerator
      reward limit hlimit0 hlimit1 who]
    simpa [root, rootOfHazard] using hlimitComplementary who
  have hlimitContracts : ∀ who, continueMassExcl limit who < 1 := by
    intro who
    by_cases hwho : who = first
    · subst who
      exact continueMassExcl_lt_one_of_positive_opponent limit hlimit0 hlimit1
        hcore.first_ne_second.symm hsecondPos
    · exact continueMassExcl_lt_one_of_positive_opponent limit hlimit0 hlimit1
        (Ne.symm hwho) hfirstPos
  have hopponents : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    intro who
    rw [show quittingStationaryFixedOpponentsContinueMass root who =
        continueMassExcl limit who by
      exact fixedOpponentsContinueMass_rootOfHazard_eq_continueMassExcl
        limit hlimit0 hlimit1 who]
    exact hlimitContracts who
  have habsorption : 0 < quittingRootAbsorptionMass root := by
    exact rootAbsorptionMass_rootOfHazard_pos_of_coordinate
      limit hlimit0 hlimit1 hfirstPos
  have hjoint : quittingStationaryContinueMass root < 1 := by
    calc
      quittingStationaryContinueMass root ≤ (root first false).toReal :=
        quittingStationaryContinueMass_le_ownContinueProbability root first
      _ < 1 := by simp [root, rootOfHazard, hfirstPos]
  let value : Payoff ι := fun who =>
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) who
  have hfixed : value = quittingRootSuccessorPayoff reward value root := by
    funext who
    simpa [value, quittingRootSuccessorPayoff] using
      quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root who
  have hendpoint : IsεQuittingRootEndpointNash reward value 0 root := by
    exact (isQuittingStationaryGainComplementary_iff_endpointNash
      reward root habsorption).mp hgainComplementary
  have hterminal : quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) = value := rfl
  have hnash :=
    isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
      reward root value hjoint hfixed hendpoint hopponents
  have huniform :=
    isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
      reward root value hjoint hfixed hendpoint hopponents
  have hcoreValue : ∀ who,
      (who = first ∨ who = second ∨ who = third) →
      value who = baseline who := by
    intro who hwho
    have hgainZero : quittingStationaryGain reward root who = 0 := by
      rw [stationaryGain_rootOfHazard_eq_faceNumerator
        reward limit hlimit0 hlimit1 who]
      rcases hwho with rfl | rfl | rfl
      · exact hfirstGain
      · exact hsecondGain
      · exact hthirdGain
    have hpassive : excludedValue (weightOfReward reward) limit who =
        (1 - continueMassExcl limit who) * baseline who := by
      rcases hwho with rfl | rfl | rfl
      · exact hcore.passive_first limit hlimit0 hlimit1
      · exact hcore.passive_second limit hlimit0 hlimit1
      · exact hcore.passive_third limit hlimit0 hlimit1
    have hsigma : sigmaValue (weightOfReward reward) limit who =
        baseline who := by
      have hface : quittingFaceNumerator
          (weightOfReward reward) limit who = 0 := by
        rw [← stationaryGain_rootOfHazard_eq_faceNumerator
          reward limit hlimit0 hlimit1 who]
        exact hgainZero
      rw [quittingFaceNumerator_eq_absorption_mul_sub_of_passive
        reward baseline limit who hpassive] at hface
      have hcontract := hlimitContracts who
      nlinarith
    have hquitValue : quittingStationaryFixedOpponentsQuitValue reward root who =
        baseline who := by
      have hfixedQuit := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (fun _ => root) who value 0
      have hsigmaBridge := quittingRootQuitPayoff_eq_sigmaValue
        reward value root who
      rw [show hazardOfRoot root = limit by simp [root]] at hsigmaBridge
      simpa [quittingStationaryFixedOpponentsQuitValue, hsigma] using
        hfixedQuit.symm.trans hsigmaBridge
    have hidentity := (quittingStationaryGain_identities reward root who).2.1
    rw [hgainZero, mul_zero] at hidentity
    dsimp only [value]
    rw [hquitValue] at hidentity
    nlinarith
  have hfirstValue : value first = baseline first :=
    hcoreValue first (Or.inl rfl)
  have hsecondValue : value second = baseline second :=
    hcoreValue second (Or.inr (Or.inl rfl))
  have hthirdValue : value third = baseline third :=
    hcoreValue third (Or.inr (Or.inr rfl))
  exact ⟨{
    root := root
    value := value
    first_hazard_pos := by simpa [root] using hfirstPos
    first_hazard_lt_one := by simpa [root] using hfirstLt
    second_hazard_pos := by simpa [root] using hsecondPos
    second_hazard_lt_one := by simpa [root] using hsecondLt
    third_hazard_pos := by simpa [root] using hthirdPos
    third_hazard_lt_one := by simpa [root] using hthirdLt
    first_value := hfirstValue
    second_value := hsecondValue
    third_value := hthirdValue
    fixedPoint := hfixed
    endpointNash := hendpoint
    jointlyContracts := hjoint
    opponentsContract := hopponents
    terminalPayoff_eq := hterminal
    terminalNash := hnash
    uniformEquilibriumPayoff := huniform }⟩

/-- Headline uniform-payoff consequence of the strict three-blocker-core
source conditions. -/
theorem isUniformEquilibriumPayoff_of_strictThreeBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (first second third : ι)
    (hcore : IsStrictThreeBlockerCore reward baseline first second third) :
    ∃ value : Payoff ι,
      value first = baseline first ∧
      value second = baseline second ∧
      value third = baseline third ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  let certificate := (exists_stationaryCertificate_of_strictThreeBlockerCore
    reward baseline first second third hcore).some
  exact ⟨certificate.value, certificate.first_value,
    certificate.second_value, certificate.third_value,
    certificate.uniformEquilibriumPayoff⟩

end GameTheory
