/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.FiniteOddBlockerCore

/-!
# Finite odd blocker cores with interval continuation rows

This module replaces the constant passive continuation value in a finite odd
blocker core by lower and upper bounds on its normalized continuation value.
Only coordinates in the embedded core are constrained.  All outside reward
coordinates remain unrestricted.
-/

noncomputable section

namespace GameTheory

open Filter Set Math Math.Probability Math.PMFProduct
open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Stationary-face source for an odd blocker core whose continuation rewards
lie in a player-dependent interval.  The bounds are division-free: they bound
`excludedValue` by opponent absorption times the interval endpoints. -/
structure IsStrictFiniteOddIntervalBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (n : ℕ) (continueLower continueUpper : Fin n → ℝ)
    (core : Fin n ↪ ι) : Prop where
  three_le : 3 ≤ n
  odd_card : Odd n
  continue_lower : ∀ phase hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
      (1 - continueMassExcl hazard (core phase)) * continueLower phase ≤
        excludedValue (weightOfReward reward) hazard (core phase)
  continue_upper : ∀ phase hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
      excludedValue (weightOfReward reward) hazard (core phase) ≤
        (1 - continueMassExcl hazard (core phase)) * continueUpper phase
  lower : ∀ phase hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    hazard (core (finRotate n phase)) = 0 →
      continueUpper phase <
        sigmaValue (weightOfReward reward) hazard (core phase)
  upper : ∀ phase hazard,
    (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
    hazard (core (finRotate n phase)) = 1 →
      sigmaValue (weightOfReward reward) hazard (core phase) <
        continueLower phase

/-- Complete stationary and all-behavior output for an odd interval blocker
core.  The core values are endogenous; `core_gain_zero` records equality of
their pure Quit and normalized Continue endpoints. -/
structure FiniteOddIntervalBlockerCoreStationaryCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (n : ℕ) (core : Fin n ↪ ι) where
  root : ι → PMF Bool
  value : Payoff ι
  core_hazard_pos : ∀ phase, 0 < hazardOfRoot root (core phase)
  core_hazard_lt_one : ∀ phase, hazardOfRoot root (core phase) < 1
  core_gain_zero : ∀ phase,
    quittingStationaryGain reward root (core phase) = 0
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

/-- An embedded odd blocker core with a strict continuation interval sandwich
has a stationary exact terminal Nash profile against arbitrary unilateral
behavioral replacement.  Every core hazard is strictly between zero and one;
outside payoff coordinates are unrestricted. -/
theorem exists_stationaryCertificate_of_strictFiniteOddIntervalBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (n : ℕ) (continueLower continueUpper : Fin n → ℝ)
    (core : Fin n ↪ ι)
    (hcore : IsStrictFiniteOddIntervalBlockerCore reward
      n continueLower continueUpper core) :
    Nonempty (FiniteOddIntervalBlockerCoreStationaryCertificate
      reward n core) := by
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
  have hforceOne : ∀ phase,
      limit (core (finRotate n phase)) = 0 →
        limit (core phase) = 1 := by
    intro phase hblocker
    have hstrict : continueUpper phase <
        sigmaValue (weightOfReward reward) limit (core phase) :=
      hcore.lower phase limit hlimit0 hlimit1 hblocker
    have heventuallySigma : ∀ᶠ index in atTop, continueUpper phase <
        sigmaValue (weightOfReward reward)
          (hazard (subsequence index)) (core phase) :=
      (tendsto_order.1 (hsigmaLimit (core phase))).1 _ hstrict
    have heventuallyOne : ∀ᶠ index in atTop,
        hazard (subsequence index) (core phase) = 1 := by
      filter_upwards [heventuallySigma] with index hsigma
      apply eq_one_of_constrainedFaceNash_of_pos (core phase)
        (hlower1 (subsequence index) (core phase))
        (hhazardUpper (subsequence index) (core phase))
      · exact hbest (subsequence index) (core phase)
      · have hcontinue := hcore.continue_upper phase
          (hazard (subsequence index))
          (hhazard0 (subsequence index))
          (hhazardUpper (subsequence index))
        unfold quittingFaceNumerator
        have hmass : 0 < 1 - continueMassExcl
            (hazard (subsequence index)) (core phase) :=
          sub_pos.mpr (hcontractAt index (core phase))
        nlinarith [mul_pos hmass (sub_pos.mpr hsigma)]
    exact tendsto_nhds_unique (hhazardLimitCoord (core phase))
      (tendsto_const_nhds.congr'
        (heventuallyOne.mono fun _ equality => equality.symm))
  have hforceZero : ∀ phase,
      limit (core (finRotate n phase)) = 1 →
        limit (core phase) = 0 := by
    intro phase hblocker
    have hstrict : sigmaValue (weightOfReward reward) limit (core phase) <
        continueLower phase :=
      hcore.upper phase limit hlimit0 hlimit1 hblocker
    have heventuallySigma : ∀ᶠ index in atTop,
        sigmaValue (weightOfReward reward)
          (hazard (subsequence index)) (core phase) < continueLower phase :=
      (tendsto_order.1 (hsigmaLimit (core phase))).2 _ hstrict
    have heventuallyLower : ∀ᶠ index in atTop,
        hazard (subsequence index) (core phase) =
          lower (subsequence index) (core phase) := by
      filter_upwards [heventuallySigma] with index hsigma
      apply eq_lower_of_constrainedFaceNash_of_neg (core phase)
        (hhazardLower (subsequence index) (core phase))
        (hbest (subsequence index) (core phase))
        (hlower1 (subsequence index) (core phase))
      have hcontinue := hcore.continue_lower phase
        (hazard (subsequence index))
        (hhazard0 (subsequence index))
        (hhazardUpper (subsequence index))
      unfold quittingFaceNumerator
      have hmass : 0 < 1 - continueMassExcl
          (hazard (subsequence index)) (core phase) :=
        sub_pos.mpr (hcontractAt index (core phase))
      nlinarith [mul_pos hmass (sub_pos.mpr hsigma)]
    have hsameLimit : Tendsto
        (fun index => hazard (subsequence index) (core phase))
        atTop (nhds 0) :=
      (hlimitLower (core phase)).congr'
        (heventuallyLower.mono fun _ equality => equality.symm)
    exact tendsto_nhds_unique (hhazardLimitCoord (core phase)) hsameLimit
  let coreLimit : Fin n → ℝ := fun phase => limit (core phase)
  have hzeroToOne : ∀ phase,
      coreLimit (finRotate n phase) = 0 → coreLimit phase = 1 :=
    hforceOne
  have honeToZero : ∀ phase,
      coreLimit (finRotate n phase) = 1 → coreLimit phase = 0 :=
    hforceZero
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
  exact ⟨{
    root := root
    value := value
    core_hazard_pos := by
      intro phase
      simpa [root] using hcorePos phase
    core_hazard_lt_one := by
      intro phase
      simpa [root] using hcoreLt phase
    core_gain_zero := by
      intro phase
      rw [stationaryGain_rootOfHazard_eq_faceNumerator
        reward limit hlimit0 hlimit1 (core phase)]
      exact hcoreGainZero phase
    fixedPoint := hfixed
    endpointNash := hendpoint
    jointlyContracts := hjoint
    opponentsContract := hopponents
    terminalPayoff_eq := hterminal
    terminalNash := hnash
    uniformEquilibriumPayoff := huniform }⟩

/-- Headline unrestricted-behavior uniform-payoff consequence of a finite odd
interval blocker core. -/
theorem isUniformEquilibriumPayoff_of_strictFiniteOddIntervalBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (n : ℕ) (continueLower continueUpper : Fin n → ℝ)
    (core : Fin n ↪ ι)
    (hcore : IsStrictFiniteOddIntervalBlockerCore reward
      n continueLower continueUpper core) :
    ∃ value : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  let certificate :=
    (exists_stationaryCertificate_of_strictFiniteOddIntervalBlockerCore
      reward n continueLower continueUpper core hcore).some
  exact ⟨certificate.value, certificate.uniformEquilibriumPayoff⟩

end GameTheory
