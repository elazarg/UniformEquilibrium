/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.CyclicContraction
import UniformEquilibrium.Quitting.Classification.Existence.OddBlockerCore

/-!
# Arbitrary finite odd blocker cores

This file extends the three-player odd blocker construction to a core indexed
by `Fin n`.  The blocker of phase `k` is the next phase `finRotate n k`.
Only payoff coordinates in the embedded core are constrained; every outside
coordinate remains unrestricted and is selected by the constrained stationary
Nash limit.
-/

noncomputable section

namespace GameTheory

open Filter Set Math Math.Probability Math.PMFProduct
open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The players in a finitely indexed blocker core. -/
def finiteOddBlockerPlayers {n : ℕ} (core : Fin n ↪ ι) : Finset ι :=
  Finset.univ.map core

/-- Stationary-face source for one strictly switching odd blocker cycle.
The embedding is an explicit cyclic indexing: the blocker of `core phase` is
`core (finRotate n phase)`.  No outside payoff coordinate is mentioned. -/
structure IsStrictFiniteOddBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (n : ℕ) (core : Fin n ↪ ι) : Prop where
  three_le : 3 ≤ n
  odd_card : Odd n
  passive : ∀ phase hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    excludedValue (weightOfReward reward) hazard (core phase) =
      (1 - continueMassExcl hazard (core phase)) * baseline (core phase)
  lower : ∀ phase hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    hazard (core (finRotate n phase)) = 0 →
      baseline (core phase) <
        sigmaValue (weightOfReward reward) hazard (core phase)
  upper : ∀ phase hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    hazard (core (finRotate n phase)) = 1 →
      sigmaValue (weightOfReward reward) hazard (core phase) <
        baseline (core phase)

/-- The vanishing lower constraint is imposed exactly on the embedded core. -/
def finiteOddCoreLower {n : ℕ} (core : Fin n ↪ ι)
    (epsilon : ℝ) (who : ι) : ℝ :=
  if who ∈ finiteOddBlockerPlayers core then epsilon else 0

omit [Fintype ι] in
@[simp] theorem finiteOddCoreLower_core {n : ℕ} (core : Fin n ↪ ι)
    (epsilon : ℝ) (phase : Fin n) :
    finiteOddCoreLower core epsilon (core phase) = epsilon := by
  simp [finiteOddCoreLower, finiteOddBlockerPlayers]

omit [Fintype ι] in
theorem finiteOddCoreLower_nonneg {n : ℕ} (core : Fin n ↪ ι)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (who : ι) :
    0 ≤ finiteOddCoreLower core epsilon who := by
  simp only [finiteOddCoreLower]
  split_ifs
  · exact hepsilon
  · exact le_rfl

omit [Fintype ι] in
theorem finiteOddCoreLower_le_one {n : ℕ} (core : Fin n ↪ ι)
    {epsilon : ℝ} (hepsilon : epsilon ≤ 1) (who : ι) :
    finiteOddCoreLower core epsilon who ≤ 1 := by
  simp only [finiteOddCoreLower]
  split_ifs
  · exact hepsilon
  · norm_num

omit [Fintype ι] [DecidableEq ι] in
/-- Alternating zero and one backwards around an odd cyclic indexing is
impossible.  This is the finite combinatorial step missing from the literal
three-core construction. -/
theorem ne_zero_of_odd_finRotate_boundary_alternation
    {n : ℕ} (hodd : Odd n) (value : Fin n → ℝ)
    (zero_to_one : ∀ phase,
      value (finRotate n phase) = 0 → value phase = 1)
    (one_to_zero : ∀ phase,
      value (finRotate n phase) = 1 → value phase = 0) :
    ∀ phase, value phase ≠ 0 := by
  intro phase hphase
  let previous : Fin n → Fin n := (finRotate n).symm
  have hpreviousZero : ∀ target,
      value target = 0 → value (previous target) = 1 := by
    intro target hzero
    apply zero_to_one
    change value (finRotate n ((finRotate n).symm target)) = 0
    simpa only [Equiv.apply_symm_apply] using hzero
  have hpreviousOne : ∀ target,
      value target = 1 → value (previous target) = 0 := by
    intro target hone
    apply one_to_zero
    change value (finRotate n ((finRotate n).symm target)) = 1
    simpa only [Equiv.apply_symm_apply] using hone
  have halternates : ∀ k,
      (Even k → value (previous^[k] phase) = 0) ∧
        (Odd k → value (previous^[k] phase) = 1) := by
    intro k
    induction k with
    | zero =>
        constructor
        · intro _
          simpa using hphase
        · intro hzeroOdd
          obtain ⟨witness, hwitness⟩ := hzeroOdd
          omega
    | succ k ih =>
        constructor
        · intro heven
          have hkodd : Odd k := by
            obtain ⟨witness, hwitness⟩ := heven
            refine ⟨witness - 1, ?_⟩
            omega
          rw [Function.iterate_succ_apply']
          exact hpreviousOne _ (ih.2 hkodd)
        · intro hoddSucc
          have hkeven : Even k := by
            obtain ⟨witness, hwitness⟩ := hoddSucc
            refine ⟨witness, ?_⟩
            omega
          rw [Function.iterate_succ_apply']
          exact hpreviousZero _ (ih.1 hkeven)
  have hreturn : previous^[n] phase = phase := by
    calc
      previous^[n] phase =
          (finRotate n)^[n] (previous^[n] phase) := by
        symm
        exact Math.iterate_finRotate_period _
      _ = phase := by
        exact (Function.LeftInverse.iterate
          (finRotate n).apply_symm_apply n) phase
  have hone := (halternates n).2 hodd
  rw [hreturn, hphase] at hone
  norm_num at hone

omit [Fintype ι] [DecidableEq ι] in
/-- Once zero is excluded, the opposite boundary is excluded by one more
backward blocker step. -/
theorem lt_one_of_odd_finRotate_boundary_alternation
    {n : ℕ} (hodd : Odd n) (value : Fin n → ℝ)
    (hvalue1 : ∀ phase, value phase ≤ 1)
    (zero_to_one : ∀ phase,
      value (finRotate n phase) = 0 → value phase = 1)
    (one_to_zero : ∀ phase,
      value (finRotate n phase) = 1 → value phase = 0) :
    ∀ phase, value phase < 1 := by
  have hneZero := ne_zero_of_odd_finRotate_boundary_alternation
    hodd value zero_to_one one_to_zero
  intro phase
  apply lt_of_le_of_ne (hvalue1 phase)
  intro hone
  let previous : Fin n := (finRotate n).symm phase
  have hprevious : value previous = 0 := by
    apply one_to_zero
    change value (finRotate n ((finRotate n).symm phase)) = 1
    simpa only [Equiv.apply_symm_apply] using hone
  exact hneZero previous hprevious

/-- Complete stationary and all-behavior output for an arbitrary finite odd
blocker core. -/
structure FiniteOddBlockerCoreStationaryCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (n : ℕ) (core : Fin n ↪ ι) where
  root : ι → PMF Bool
  value : Payoff ι
  core_hazard_pos : ∀ phase, 0 < hazardOfRoot root (core phase)
  core_hazard_lt_one : ∀ phase, hazardOfRoot root (core phase) < 1
  core_value : ∀ phase, value (core phase) = baseline (core phase)
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

/-- **Finite odd blocker core with arbitrary outside coordinates.**  An
embedded strict passive blocker cycle of odd length at least three has a
stationary exact terminal Nash profile.  Every embedded core hazard is
interior and every core payoff is its baseline. -/
theorem exists_stationaryCertificate_of_strictFiniteOddBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (n : ℕ) (core : Fin n ↪ ι)
    (hcore : IsStrictFiniteOddBlockerCore reward baseline n core) :
    Nonempty (FiniteOddBlockerCoreStationaryCertificate
      reward baseline n core) := by
  have hn : 3 ≤ n := hcore.three_le
  let phase0 : Fin n := ⟨0, by omega⟩
  let phase1 : Fin n := ⟨1, by omega⟩
  letI : Nonempty ι := ⟨core phase0⟩
  have hphase01 : phase0 ≠ phase1 := by
    intro heq
    have := congrArg Fin.val heq
    simp [phase0, phase1] at this
  have hcore01 : core phase0 ≠ core phase1 := fun heq =>
    hphase01 (core.injective heq)
  let lower : ℕ → ι → ℝ := fun index =>
    finiteOddCoreLower core (oddCoreEpsilon index)
  have hlower0 : ∀ index who, 0 ≤ lower index who := fun index who =>
    finiteOddCoreLower_nonneg core (oddCoreEpsilon_pos index).le who
  have hlower1 : ∀ index who, lower index who ≤ 1 := fun index who =>
    finiteOddCoreLower_le_one core (oddCoreEpsilon_le_one index) who
  have hexists : ∀ index, ∃ hazard : ι → ℝ,
      (∀ who, lower index who ≤ hazard who) ∧
      (∀ who, hazard who ≤ 1) ∧
      ∀ who rate, lower index who ≤ rate → rate ≤ 1 →
        rate * quittingFaceNumerator (weightOfReward reward) hazard who ≤
          hazard who *
            quittingFaceNumerator (weightOfReward reward) hazard who :=
    fun index =>
      exists_heterogeneousStationaryFaceNash reward
        (lower index) (hlower1 index)
  choose hazard hhazardLower hhazardUpper hbest using hexists
  have hhazard0 : ∀ index who, 0 ≤ hazard index who := fun index who =>
    (hlower0 index who).trans (hhazardLower index who)
  let cubeHazard : ℕ → ι → Set.Icc (0 : ℝ) 1 := fun index who =>
    ⟨hazard index who, hhazard0 index who, hhazardUpper index who⟩
  obtain ⟨limitCube, subsequence, hsubsequence, hcubeLimit⟩ :=
    CompactSpace.tendsto_subseq cubeHazard
  let limit : ι → ℝ := fun who => (limitCube who).val
  have hsubsequenceAtTop : Tendsto subsequence atTop atTop :=
    hsubsequence.tendsto_atTop
  have hepsilonLimit : Tendsto
      (fun index => oddCoreEpsilon (subsequence index)) atTop (nhds 0) :=
    oddCoreEpsilon_tendsto_zero.comp hsubsequenceAtTop
  have hhazardLimit : Tendsto (fun index => hazard (subsequence index))
      atTop (nhds limit) := by
    rw [tendsto_pi_nhds]
    intro who
    have hprojection : Continuous
        (fun point : ι → Set.Icc (0 : ℝ) 1 => (point who).val) :=
      continuous_subtype_val.comp (continuous_apply who)
    have hcoordinate : Tendsto
        (fun index => (cubeHazard (subsequence index) who).val)
        atTop (nhds (limitCube who).val) := by
      simpa only [Function.comp_def] using
        (hprojection.tendsto limitCube).comp hcubeLimit
    simpa only [cubeHazard, limit] using hcoordinate
  have hhazardLimitCoord : ∀ who, Tendsto
      (fun index => hazard (subsequence index) who)
      atTop (nhds (limit who)) := by
    intro who
    exact tendsto_pi_nhds.mp hhazardLimit who
  have hlimit0 : ∀ who, 0 ≤ limit who := fun who =>
    (limitCube who).property.1
  have hlimit1 : ∀ who, limit who ≤ 1 := fun who =>
    (limitCube who).property.2
  have hsigmaLimit : ∀ who, Tendsto
      (fun index => sigmaValue (weightOfReward reward)
        (hazard (subsequence index)) who)
      atTop (nhds (sigmaValue (weightOfReward reward) limit who)) := by
    intro who
    exact ((continuous_sigmaValue
      (weightOfReward reward) who).tendsto limit).comp hhazardLimit
  have hlimitLower : ∀ who, Tendsto
      (fun index => lower (subsequence index) who) atTop (nhds 0) := by
    intro who
    by_cases hmem : who ∈ finiteOddBlockerPlayers core
    · simpa [lower, finiteOddCoreLower, hmem] using hepsilonLimit
    · simp [lower, finiteOddCoreLower, hmem]
  have hcontractAt : ∀ index who,
      continueMassExcl (hazard (subsequence index)) who < 1 := by
    intro index who
    by_cases hwho : who = core phase0
    · subst who
      exact continueMassExcl_lt_one_of_positive_opponent
        (hazard (subsequence index)) (hhazard0 (subsequence index))
        (hhazardUpper (subsequence index)) hcore01.symm
        ((oddCoreEpsilon_pos (subsequence index)).trans_le (by
          simpa [lower] using
            hhazardLower (subsequence index) (core phase1)))
    · exact continueMassExcl_lt_one_of_positive_opponent
        (hazard (subsequence index)) (hhazard0 (subsequence index))
        (hhazardUpper (subsequence index)) (Ne.symm hwho)
        ((oddCoreEpsilon_pos (subsequence index)).trans_le (by
          simpa [lower] using
            hhazardLower (subsequence index) (core phase0)))
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
    have heventuallySigma : ∀ᶠ index in atTop, baseline owner <
        sigmaValue (weightOfReward reward)
          (hazard (subsequence index)) owner :=
      (tendsto_order.1 (hsigmaLimit owner)).1 _ hstrict
    have heventuallyOne : ∀ᶠ index in atTop,
        hazard (subsequence index) owner = 1 := by
      filter_upwards [heventuallySigma] with index hsigma
      apply eq_one_of_constrainedFaceNash_of_pos owner
        (hlower1 (subsequence index) owner)
        (hhazardUpper (subsequence index) owner)
      · exact hbest (subsequence index) owner
      · exact quittingFaceNumerator_pos_of_passive_of_sigma_gt
          reward baseline (hazard (subsequence index)) owner
          (hcontractAt index owner)
          (hpassive (hazard (subsequence index))
            (hhazard0 (subsequence index))
            (hhazardUpper (subsequence index))) hsigma
    exact tendsto_nhds_unique (hhazardLimitCoord owner)
      (tendsto_const_nhds.congr'
        (heventuallyOne.mono fun _ equality => equality.symm))
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
    have heventuallySigma : ∀ᶠ index in atTop,
        sigmaValue (weightOfReward reward)
          (hazard (subsequence index)) owner < baseline owner :=
      (tendsto_order.1 (hsigmaLimit owner)).2 _ hstrict
    have heventuallyLower : ∀ᶠ index in atTop,
        hazard (subsequence index) owner =
          lower (subsequence index) owner := by
      filter_upwards [heventuallySigma] with index hsigma
      apply eq_lower_of_constrainedFaceNash_of_neg owner
        (hhazardLower (subsequence index) owner)
        (hbest (subsequence index) owner)
        (hlower1 (subsequence index) owner)
      exact quittingFaceNumerator_neg_of_passive_of_sigma_lt
        reward baseline (hazard (subsequence index)) owner
        (hcontractAt index owner)
        (hpassive (hazard (subsequence index))
          (hhazard0 (subsequence index))
          (hhazardUpper (subsequence index))) hsigma
    have hsameLimit : Tendsto
        (fun index => hazard (subsequence index) owner)
        atTop (nhds 0) :=
      (hlimitLower owner).congr'
        (heventuallyLower.mono fun _ equality => equality.symm)
    exact tendsto_nhds_unique (hhazardLimitCoord owner) hsameLimit
  let coreLimit : Fin n → ℝ := fun phase => limit (core phase)
  have hzeroToOne : ∀ phase,
      coreLimit (finRotate n phase) = 0 → coreLimit phase = 1 := by
    intro phase
    exact hforceOne (core phase) (core (finRotate n phase))
      (hcore.lower phase) (hcore.passive phase)
  have honeToZero : ∀ phase,
      coreLimit (finRotate n phase) = 1 → coreLimit phase = 0 := by
    intro phase
    exact hforceZero (core phase) (core (finRotate n phase))
      (hcore.upper phase) (hcore.passive phase)
  have hcoreNeZero : ∀ phase, coreLimit phase ≠ 0 :=
    ne_zero_of_odd_finRotate_boundary_alternation
      hcore.odd_card coreLimit hzeroToOne honeToZero
  have hcorePos : ∀ phase, 0 < limit (core phase) := by
    intro phase
    exact lt_of_le_of_ne (hlimit0 (core phase)) (hcoreNeZero phase).symm
  have hcoreLt : ∀ phase, limit (core phase) < 1 := by
    exact lt_one_of_odd_finRotate_boundary_alternation hcore.odd_card
      coreLimit (fun phase => hlimit1 (core phase)) hzeroToOne honeToZero
  have hgainLimit : ∀ who, Tendsto
      (fun index => quittingFaceNumerator (weightOfReward reward)
        (hazard (subsequence index)) who)
      atTop (nhds (quittingFaceNumerator
        (weightOfReward reward) limit who)) := by
    intro who
    exact ((continuous_quittingFaceNumerator
      (weightOfReward reward) who).tendsto limit).comp hhazardLimit
  have hcoreGainZero : ∀ phase,
      quittingFaceNumerator (weightOfReward reward)
        limit (core phase) = 0 := by
    intro phase
    apply le_antisymm
    · by_contra hnot
      have hgainPos : 0 < quittingFaceNumerator
          (weightOfReward reward) limit (core phase) := lt_of_not_ge hnot
      have heventuallyGain : ∀ᶠ index in atTop,
          0 < quittingFaceNumerator (weightOfReward reward)
            (hazard (subsequence index)) (core phase) :=
        (tendsto_order.1 (hgainLimit (core phase))).1 0 hgainPos
      have heventuallyOne : ∀ᶠ index in atTop,
          hazard (subsequence index) (core phase) = 1 := by
        filter_upwards [heventuallyGain] with index hgain
        exact eq_one_of_constrainedFaceNash_of_pos (core phase)
          (hlower1 (subsequence index) (core phase))
          (hhazardUpper (subsequence index) (core phase))
          (hbest (subsequence index) (core phase)) hgain
      have honeLimit : Tendsto
          (fun index => hazard (subsequence index) (core phase))
          atTop (nhds 1) :=
        tendsto_const_nhds.congr'
          (heventuallyOne.mono fun _ equality => equality.symm)
      have hone : limit (core phase) = 1 :=
        tendsto_nhds_unique (hhazardLimitCoord (core phase)) honeLimit
      linarith [hcoreLt phase]
    · by_contra hnot
      have hgainNeg : quittingFaceNumerator
          (weightOfReward reward) limit (core phase) < 0 := lt_of_not_ge hnot
      have heventuallyGain : ∀ᶠ index in atTop,
          quittingFaceNumerator (weightOfReward reward)
            (hazard (subsequence index)) (core phase) < 0 :=
        (tendsto_order.1 (hgainLimit (core phase))).2 0 hgainNeg
      have heventuallyLower : ∀ᶠ index in atTop,
          hazard (subsequence index) (core phase) =
            lower (subsequence index) (core phase) := by
        filter_upwards [heventuallyGain] with index hgain
        exact eq_lower_of_constrainedFaceNash_of_neg (core phase)
          (hhazardLower (subsequence index) (core phase))
          (hbest (subsequence index) (core phase))
          (hlower1 (subsequence index) (core phase)) hgain
      have hzeroLimit : Tendsto
          (fun index => hazard (subsequence index) (core phase))
          atTop (nhds 0) :=
        (hlimitLower (core phase)).congr'
          (heventuallyLower.mono fun _ equality => equality.symm)
      have hzero : limit (core phase) = 0 :=
        tendsto_nhds_unique (hhazardLimitCoord (core phase)) hzeroLimit
      exact (hcoreNeZero phase) hzero
  have hlimitBestOutside : ∀ who,
      who ∉ finiteOddBlockerPlayers core →
      (1 - limit who) *
          quittingFaceNumerator (weightOfReward reward) limit who ≤ 0 ∧
        0 ≤ limit who *
          quittingFaceNumerator (weightOfReward reward) limit who := by
    intro who houtside
    have hlowerWho : ∀ index, lower index who = 0 := by
      intro index
      simp [lower, finiteOddCoreLower, houtside]
    have hcontinue : ∀ index,
        (1 - hazard (subsequence index) who) *
            quittingFaceNumerator (weightOfReward reward)
              (hazard (subsequence index)) who ≤ 0 := by
      intro index
      have h := hbest (subsequence index) who 1
        (hlower1 (subsequence index) who) le_rfl
      nlinarith
    have hquit : ∀ index,
        0 ≤ hazard (subsequence index) who *
          quittingFaceNumerator (weightOfReward reward)
            (hazard (subsequence index)) who := by
      intro index
      have h := hbest (subsequence index) who 0
        (by rw [hlowerWho]) (by norm_num)
      simpa using h
    have hcontinueLimit : Tendsto
        (fun index => (1 - hazard (subsequence index) who) *
          quittingFaceNumerator (weightOfReward reward)
            (hazard (subsequence index)) who)
        atTop (nhds ((1 - limit who) *
          quittingFaceNumerator (weightOfReward reward) limit who)) :=
      ((tendsto_const_nhds.sub (hhazardLimitCoord who)).mul
        (hgainLimit who))
    have hquitLimit : Tendsto
        (fun index => hazard (subsequence index) who *
          quittingFaceNumerator (weightOfReward reward)
            (hazard (subsequence index)) who)
        atTop (nhds (limit who *
          quittingFaceNumerator (weightOfReward reward) limit who)) :=
      (hhazardLimitCoord who).mul (hgainLimit who)
    exact ⟨le_of_tendsto' hcontinueLimit hcontinue,
      ge_of_tendsto' hquitLimit hquit⟩
  have hlimitComplementary : ∀ who,
      (1 - limit who) *
          quittingFaceNumerator (weightOfReward reward) limit who ≤ 0 ∧
        0 ≤ limit who *
          quittingFaceNumerator (weightOfReward reward) limit who := by
    intro who
    by_cases hmem : who ∈ finiteOddBlockerPlayers core
    · rw [finiteOddBlockerPlayers, Finset.mem_map] at hmem
      obtain ⟨phase, _, hphase⟩ := hmem
      subst who
      simp [hcoreGainZero phase]
    · exact hlimitBestOutside who hmem
  let root := rootOfHazard limit hlimit0 hlimit1
  have hgainComplementary : IsQuittingStationaryGainComplementary reward root := by
    intro who
    rw [stationaryGain_rootOfHazard_eq_faceNumerator
      reward limit hlimit0 hlimit1 who]
    simpa [root, rootOfHazard] using hlimitComplementary who
  have hlimitContracts : ∀ who, continueMassExcl limit who < 1 := by
    intro who
    by_cases hwho : who = core phase0
    · subst who
      exact continueMassExcl_lt_one_of_positive_opponent limit hlimit0 hlimit1
        hcore01.symm (hcorePos phase1)
    · exact continueMassExcl_lt_one_of_positive_opponent limit hlimit0 hlimit1
        (Ne.symm hwho) (hcorePos phase0)
  have hopponents : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    intro who
    rw [show quittingStationaryFixedOpponentsContinueMass root who =
        continueMassExcl limit who by
      exact fixedOpponentsContinueMass_rootOfHazard_eq_continueMassExcl
        limit hlimit0 hlimit1 who]
    exact hlimitContracts who
  have habsorption : 0 < quittingRootAbsorptionMass root :=
    rootAbsorptionMass_rootOfHazard_pos_of_coordinate
      limit hlimit0 hlimit1 (hcorePos phase0)
  have hjoint : quittingStationaryContinueMass root < 1 := by
    calc
      quittingStationaryContinueMass root ≤ (root (core phase0) false).toReal :=
        quittingStationaryContinueMass_le_ownContinueProbability
          root (core phase0)
      _ < 1 := by simp [root, rootOfHazard, hcorePos phase0]
  let value : Payoff ι := fun who =>
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) who
  have hfixed : value = quittingRootSuccessorPayoff reward value root := by
    funext who
    simpa [value, quittingRootSuccessorPayoff] using
      quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root who
  have hendpoint : IsεQuittingRootEndpointNash reward value 0 root :=
    (isQuittingStationaryGainComplementary_iff_endpointNash
      reward root habsorption).mp hgainComplementary
  have hterminal : quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) = value := rfl
  have hnash :=
    isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
      reward root value hjoint hfixed hendpoint hopponents
  have huniform :=
    isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
      reward root value hjoint hfixed hendpoint hopponents
  have hcoreValue : ∀ phase,
      value (core phase) = baseline (core phase) := by
    intro phase
    have hgainZero : quittingStationaryGain reward root (core phase) = 0 := by
      rw [stationaryGain_rootOfHazard_eq_faceNumerator
        reward limit hlimit0 hlimit1 (core phase)]
      exact hcoreGainZero phase
    have hpassive : excludedValue (weightOfReward reward)
        limit (core phase) =
          (1 - continueMassExcl limit (core phase)) *
            baseline (core phase) :=
      hcore.passive phase limit hlimit0 hlimit1
    have hsigma : sigmaValue (weightOfReward reward)
        limit (core phase) = baseline (core phase) := by
      have hface : quittingFaceNumerator (weightOfReward reward)
          limit (core phase) = 0 := by
        rw [← stationaryGain_rootOfHazard_eq_faceNumerator
          reward limit hlimit0 hlimit1 (core phase)]
        exact hgainZero
      rw [quittingFaceNumerator_eq_absorption_mul_sub_of_passive
        reward baseline limit (core phase) hpassive] at hface
      nlinarith [hlimitContracts (core phase)]
    have hquitValue : quittingStationaryFixedOpponentsQuitValue
        reward root (core phase) = baseline (core phase) := by
      have hfixedQuit := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (fun _ => root) (core phase) value 0
      have hsigmaBridge := quittingRootQuitPayoff_eq_sigmaValue
        reward value root (core phase)
      rw [show hazardOfRoot root = limit by simp [root]] at hsigmaBridge
      simpa [quittingStationaryFixedOpponentsQuitValue, hsigma] using
        hfixedQuit.symm.trans hsigmaBridge
    have hidentity :=
      (quittingStationaryGain_identities reward root (core phase)).2.1
    rw [hgainZero, mul_zero] at hidentity
    dsimp only [value]
    rw [hquitValue] at hidentity
    nlinarith
  exact ⟨{
    root := root
    value := value
    core_hazard_pos := by
      intro phase
      simpa [root] using hcorePos phase
    core_hazard_lt_one := by
      intro phase
      simpa [root] using hcoreLt phase
    core_value := hcoreValue
    fixedPoint := hfixed
    endpointNash := hendpoint
    jointlyContracts := hjoint
    opponentsContract := hopponents
    terminalPayoff_eq := hterminal
    terminalNash := hnash
    uniformEquilibriumPayoff := huniform }⟩

/-- Headline uniform-payoff consequence of a finite strictly switching odd
blocker core. -/
theorem isUniformEquilibriumPayoff_of_strictFiniteOddBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (n : ℕ) (core : Fin n ↪ ι)
    (hcore : IsStrictFiniteOddBlockerCore reward baseline n core) :
    ∃ value : Payoff ι,
      (∀ phase, value (core phase) = baseline (core phase)) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  let certificate :=
    (exists_stationaryCertificate_of_strictFiniteOddBlockerCore
      reward baseline n core hcore).some
  exact ⟨certificate.value, certificate.core_value,
    certificate.uniformEquilibriumPayoff⟩

end GameTheory
