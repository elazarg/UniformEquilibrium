/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.PMFProduct.CollisionMass
import UniformEquilibrium.ProofView.Concepts.Existence.CompactNash
import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.NormalCorePunishmentNormal
import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.NormalTerminalGapFullSupportCompactLimit
import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.NormalTerminalGapFullSupportLift
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.AmbientCarrierElimination
import UniformEquilibrium.Quitting.Boundary.Analytic.WeightedContinueMassBound
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import UniformEquilibrium.Quitting.Stationary.Gain
import UniformEquilibrium.Quitting.Stationary.FaceNumerator
import UniformEquilibrium.Quitting.Stationary.FullRateStationaryVerifier
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# Constrained stationary roots for the normal terminal-gap lift

For `0 < epsilon < 1`, each stationary quit rate is restricted to
`[epsilon, 1]`.  A player's repeated-row terminal payoff is fractional linear
in its own rate.  Its preference sign is the division-free face numerator

`(1 - c_{-i}) * Sigma_i - A_i`.

We therefore apply the repository's compact barycentric Nash theorem to the
auxiliary payoff `q_i` times this numerator.  The numerator ignores `q_i`, so
this auxiliary payoff is affine in the player's own coordinate and has
exactly the same constrained best replies as the repeated-row payoff.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open ThreeCoreAmbientCarrierElimination

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A finite simplex barycenter of points in `[epsilon, 1]` stays in that
interval. -/
def constrainedRateBarycenter (epsilon : ℝ) (_hepsilon : epsilon ≤ 1)
    (n : ℕ) (weight : stdSimplex ℝ (Fin (n + 1)))
    (point : Fin (n + 1) → Set.Icc epsilon 1) : Set.Icc epsilon 1 := by
  refine ⟨∑ action, weight.val action * (point action).val, ?_, ?_⟩
  · calc
      epsilon = ∑ action, weight.val action * epsilon := by
        rw [← Finset.sum_mul, weight.property.2, one_mul]
      _ ≤ ∑ action, weight.val action * (point action).val := by
        exact Finset.sum_le_sum fun action _ =>
          mul_le_mul_of_nonneg_left (point action).property.1
            (weight.property.1 action)
  · calc
      (∑ action, weight.val action * (point action).val) ≤
          ∑ action, weight.val action * 1 := by
        exact Finset.sum_le_sum fun action _ =>
          mul_le_mul_of_nonneg_left (point action).property.2
            (weight.property.1 action)
      _ = 1 := by
        rw [← Finset.sum_mul, weight.property.2, one_mul]

/-- The interval barycenter depends continuously on its simplex weights. -/
theorem continuous_constrainedRateBarycenter
    (epsilon : ℝ) (hepsilon : epsilon ≤ 1) (n : ℕ)
    (point : Fin (n + 1) → Set.Icc epsilon 1) :
    Continuous fun weight : stdSimplex ℝ (Fin (n + 1)) =>
      constrainedRateBarycenter epsilon hepsilon n weight point := by
  apply Continuous.subtype_mk
  apply continuous_finsetSum
  intro action _
  exact ((continuous_apply action).comp continuous_subtype_val).mul continuous_const

/-- The face numerator ignores the selected player's own hazard coordinate. -/
theorem quittingFaceNumerator_update_self
    (r : Finset ι → ι → ℝ) (hazard : ι → ℝ) (who : ι) (rate : ℝ) :
    quittingFaceNumerator r (Function.update hazard who rate) who =
      quittingFaceNumerator r hazard who := by
  unfold quittingFaceNumerator
  rw [continueMassExcl_update_self', sigmaValue_update_self,
    excludedValue_update_self]

/-- Two hazard rows agreeing off the selected player have the same face
numerator at that player. -/
theorem quittingFaceNumerator_congr_off_self
    (r : Finset ι → ι → ℝ) (first second : ι → ℝ) (who : ι)
    (hagree : ∀ other, other ≠ who → first other = second other) :
    quittingFaceNumerator r first who = quittingFaceNumerator r second who := by
  have hrow : first = Function.update second who (first who) := by
    funext other
    by_cases hother : other = who
    · subst other
      simp
    · rw [Function.update_of_ne hother]
      exact hagree other hother
  rw [hrow, quittingFaceNumerator_update_self]

/-- The auxiliary compact game whose Nash roots are constrained stationary
best replies. -/
def normalTerminalGapConstrainedGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (epsilon : ℝ) (hepsilon : epsilon ≤ 1) : CompactBarycentricGame where
  Player := ι
  Strategy := fun _ => Set.Icc epsilon 1
  compactStrategy := fun _ => inferInstance
  nonemptyStrategy := fun _ => ⟨⟨epsilon, le_rfl, hepsilon⟩⟩
  payoff := fun profile who =>
    (profile who).val * quittingFaceNumerator (weightOfReward reward)
      (fun player => (profile player).val) who
  payoffContinuous := fun who => by
    have hprofile : Continuous
        (fun profile : ∀ _ : ι, Set.Icc epsilon 1 =>
          fun player => (profile player).val) := by
      apply continuous_pi
      intro player
      exact continuous_subtype_val.comp (continuous_apply player)
    exact (continuous_subtype_val.comp (continuous_apply who)).mul
      ((continuous_quittingFaceNumerator (weightOfReward reward) who).comp
        hprofile)
  barycenter := fun _ n weight point =>
    constrainedRateBarycenter epsilon hepsilon n weight point
  barycenterContinuous := fun _ n point =>
    continuous_constrainedRateBarycenter epsilon hepsilon n point
  payoffBarycentric := by
    intro profile who n weight point
    let hazard : ι → ℝ := fun player => (profile player).val
    let coefficient := quittingFaceNumerator (weightOfReward reward) hazard who
    have hcoefficient : ∀ action,
        quittingFaceNumerator (weightOfReward reward)
          (fun player =>
            ((Function.update profile who (point action)) player).val) who =
          coefficient := by
      intro action
      have hrow : (fun player =>
          ((Function.update profile who (point action)) player).val) =
          Function.update hazard who (point action).val := by
        funext player
        by_cases hplayer : player = who
        · subst player
          simp [hazard]
        · simp [hazard, Function.update_of_ne hplayer]
      rw [hrow, quittingFaceNumerator_update_self]
    have hbaryCoefficient :
        quittingFaceNumerator (weightOfReward reward)
          (fun player =>
            ((Function.update profile who
              (constrainedRateBarycenter epsilon hepsilon n weight point))
                player).val) who = coefficient := by
      have hrow : (fun player =>
          ((Function.update profile who
            (constrainedRateBarycenter epsilon hepsilon n weight point))
              player).val) =
          Function.update hazard who
            (constrainedRateBarycenter epsilon hepsilon n weight point).val := by
        funext player
        by_cases hplayer : player = who
        · subst player
          simp [hazard]
        · simp [hazard, Function.update_of_ne hplayer]
      rw [hrow, quittingFaceNumerator_update_self]
    simp only [Function.update_self]
    rw [hbaryCoefficient]
    change
      (constrainedRateBarycenter epsilon hepsilon n weight point).val *
          coefficient =
        ∑ action, weight action *
          ((point action).val *
            quittingFaceNumerator (weightOfReward reward)
              (fun player =>
                ((Function.update profile who (point action)) player).val) who)
    simp_rw [hcoefficient]
    unfold constrainedRateBarycenter
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro action _
    rw [show weight action = weight.val action by rfl]
    ring

/-- A constrained stationary auxiliary Nash root exists at every nonempty
interval `[epsilon, 1]`. -/
theorem exists_constrainedStationaryFaceNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {epsilon : ℝ} (hepsilon : epsilon ≤ 1) :
    ∃ hazard : ι → ℝ,
      (∀ who, epsilon ≤ hazard who) ∧
      (∀ who, hazard who ≤ 1) ∧
      ∀ who rate, epsilon ≤ rate → rate ≤ 1 →
        rate * quittingFaceNumerator (weightOfReward reward) hazard who ≤
          hazard who *
            quittingFaceNumerator (weightOfReward reward) hazard who := by
  obtain ⟨profile, hnash⟩ :=
    (normalTerminalGapConstrainedGame reward epsilon hepsilon).exists_nash
  let hazard : ι → ℝ := fun who => (profile who).val
  refine ⟨hazard, fun who => (profile who).property.1,
    fun who => (profile who).property.2, ?_⟩
  intro who rate hrate0 hrate1
  let deviation : Set.Icc epsilon 1 := ⟨rate, hrate0, hrate1⟩
  have hbest := hnash who deviation
  dsimp only [normalTerminalGapConstrainedGame] at hbest
  simp only [Function.update_self] at hbest
  let deviatedHazard : ι → ℝ := fun player =>
    ((Function.update profile who deviation) player).val
  have hcoefficient : quittingFaceNumerator (weightOfReward reward)
      deviatedHazard who = quittingFaceNumerator (weightOfReward reward)
        hazard who := by
    apply quittingFaceNumerator_congr_off_self
    intro other hother
    have hupdate : Function.update profile who deviation other = profile other :=
      @Function.update_of_ne ι (fun _ => Set.Icc epsilon 1)
        (normalTerminalGapConstrainedGame reward epsilon hepsilon).decidablePlayer
        other who hother deviation profile
    exact congrArg Subtype.val hupdate
  change deviation.val * quittingFaceNumerator (weightOfReward reward)
      deviatedHazard who ≤
    (profile who).val * quittingFaceNumerator (weightOfReward reward)
      hazard who at hbest
  rw [hcoefficient] at hbest
  simpa only [deviation, hazard] using hbest

/-- At a constrained face Nash root, every nonsaturated coordinate has
nonpositive face numerator. -/
theorem quittingFaceNumerator_nonpos_of_constrainedNash_of_lt_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {epsilon : ℝ} {hazard : ι → ℝ}
    (hbest : ∀ who rate, epsilon ≤ rate → rate ≤ 1 →
      rate * quittingFaceNumerator (weightOfReward reward) hazard who ≤
        hazard who * quittingFaceNumerator (weightOfReward reward) hazard who)
    (hepsilon : epsilon ≤ 1) (who : ι) (hhazard : hazard who < 1) :
    quittingFaceNumerator (weightOfReward reward) hazard who ≤ 0 := by
  have h := hbest who 1 hepsilon le_rfl
  nlinarith

/-- At a constrained face Nash root, every coordinate strictly above the
lower face has nonnegative face numerator. -/
theorem quittingFaceNumerator_nonneg_of_constrainedNash_of_lower_lt
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {epsilon : ℝ} {hazard : ι → ℝ}
    (hbest : ∀ who rate, epsilon ≤ rate → rate ≤ 1 →
      rate * quittingFaceNumerator (weightOfReward reward) hazard who ≤
        hazard who * quittingFaceNumerator (weightOfReward reward) hazard who)
    (hepsilon : epsilon ≤ 1) (who : ι) (hhazard : epsilon < hazard who) :
    0 ≤ quittingFaceNumerator (weightOfReward reward) hazard who := by
  have h := hbest who epsilon le_rfl hepsilon
  nlinarith

/-! ## Bridge to literal stationary roots -/

/-- The fixed-opponent Continue mass of a hazard-converted root is the
corresponding product over all coordinates except the selected player. -/
theorem quittingStationaryFixedOpponentsContinueMass_rootOfHazard
    (hazard : ι → ℝ) (hhazard0 : ∀ who, 0 ≤ hazard who)
    (hhazard1 : ∀ who, hazard who ≤ 1) (who : ι) :
    quittingStationaryFixedOpponentsContinueMass
        (rootOfHazard hazard hhazard0 hhazard1) who =
      continueMassExcl hazard who := by
  let root := rootOfHazard hazard hhazard0 hhazard1
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  change (∏ player, ((Function.update root who (PMF.pure false)) player
    (quittingAllContinueAction player)).toReal) = _
  rw [← Finset.mul_prod_erase Finset.univ
    (fun player => ((Function.update root who (PMF.pure false)) player
      (quittingAllContinueAction player)).toReal) (Finset.mem_univ who)]
  simp only [quittingAllContinueAction, Function.update_self, PMF.pure_apply,
    if_true, ENNReal.toReal_one, one_mul, continueMassExcl]
  apply Finset.prod_congr rfl
  intro other hother
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hother)]
  simp [root, rootOfHazard]

/-- A common positive lower hazard makes every fixed-opponent row strictly
contracting as soon as the player type has at least two elements. -/
theorem quittingStationaryFixedOpponentsContinueMass_rootOfHazard_lt_one
    [Nontrivial ι]
    (hazard : ι → ℝ) (hhazard0 : ∀ who, 0 ≤ hazard who)
    (hhazard1 : ∀ who, hazard who ≤ 1)
    (hhazardPos : ∀ who, 0 < hazard who) (who : ι) :
    quittingStationaryFixedOpponentsContinueMass
        (rootOfHazard hazard hhazard0 hhazard1) who < 1 := by
  rw [quittingStationaryFixedOpponentsContinueMass_rootOfHazard]
  obtain ⟨other, hother⟩ := exists_ne who
  unfold continueMassExcl
  apply Math.Finset.prod_lt_one_of_mem
    (Finset.univ.erase who) (fun player => 1 - hazard player) other
  · simp [hother]
  · intro player _ _
    linarith [hhazard1 player]
  · intro player _ _
    linarith [hhazard0 player]
  · linarith [hhazardPos other]

/-- A positive hazard coordinate makes the literal converted root absorb
with positive one-stage probability. -/
theorem quittingRootAbsorptionMass_rootOfHazard_pos
    (hazard : ι → ℝ) (hhazard0 : ∀ who, 0 ≤ hazard who)
    (hhazard1 : ∀ who, hazard who ≤ 1)
    {who : ι} (hhazardPos : 0 < hazard who) :
    0 < quittingRootAbsorptionMass
      (rootOfHazard hazard hhazard0 hhazard1) := by
  let root := rootOfHazard hazard hhazard0 hhazard1
  have hmass : quittingStationaryFixedOpponentsContinueMass root who ≤ 1 :=
    quittingStationaryContinueMass_le_one
      (Function.update root who (PMF.pure false))
  have hidentity := quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul
    root who
  have hcontinue : (root who false).toReal = 1 - hazard who := by
    simp [root, rootOfHazard]
  rw [hcontinue] at hidentity
  have hmassNonneg : 0 ≤
      quittingStationaryFixedOpponentsContinueMass root who :=
    quittingStationaryContinueMass_nonneg
      (Function.update root who (PMF.pure false))
  have hownNonneg : 0 ≤ 1 - hazard who := by
    linarith [hhazard1 who]
  have hproduct :
      (1 - hazard who) *
          quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    calc
      (1 - hazard who) *
          quittingStationaryFixedOpponentsContinueMass root who ≤
          (1 - hazard who) * 1 :=
        mul_le_mul_of_nonneg_left hmass hownNonneg
      _ < 1 := by linarith
  rw [hidentity]
  linarith

/-- The real-hazard face numerator is exactly the game-facing stationary
gain of the corresponding Boolean product root. -/
theorem quittingStationaryGain_rootOfHazard_eq_faceNumerator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hazard : ι → ℝ) (hhazard0 : ∀ who, 0 ≤ hazard who)
    (hhazard1 : ∀ who, hazard who ≤ 1) (who : ι) :
    quittingStationaryGain reward
        (rootOfHazard hazard hhazard0 hhazard1) who =
      quittingFaceNumerator (weightOfReward reward) hazard who := by
  let root := rootOfHazard hazard hhazard0 hhazard1
  have hrootHazard : hazardOfRoot root = hazard :=
    hazardOfRoot_rootOfHazard hazard hhazard0 hhazard1
  have hquit : quittingStationaryFixedOpponentsQuitValue reward root who =
      sigmaValue (weightOfReward reward) hazard who := by
    have hfixed := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward (fun _ => root) who (0 : Payoff ι) 0
    have hsigma := quittingRootQuitPayoff_eq_sigmaValue
      reward (0 : Payoff ι) root who
    simpa [quittingStationaryFixedOpponentsQuitValue, hrootHazard] using
      hfixed.symm.trans hsigma
  have hcontinue :
      quittingStationaryFixedOpponentsContinueReward reward root who =
        excludedValue (weightOfReward reward) hazard who := by
    have hfixed := quittingRootContinuePayoff_eq_fixedOpponents
      reward (fun _ => root) who (0 : Payoff ι) 0
    have hgamma := quittingRootContinuePayoff_eq_gammaValue
      reward (0 : Payoff ι) root who
    have hvalue : quittingRootContinuePayoff reward (0 : Payoff ι) root who =
        quittingStationaryFixedOpponentsContinueReward reward root who := by
      simpa [quittingStationaryFixedOpponentsContinueReward,
        quittingStationaryFixedOpponentsContinueMass] using hfixed
    rw [hvalue] at hgamma
    simpa [gammaValue, hrootHazard] using hgamma
  have hmass : quittingStationaryFixedOpponentsContinueMass root who =
      continueMassExcl hazard who :=
    quittingStationaryFixedOpponentsContinueMass_rootOfHazard
      hazard hhazard0 hhazard1 who
  unfold quittingStationaryGain quittingFaceNumerator
  rw [hquit, hcontinue, hmass]

/-- A nonpositive face numerator gives a nonpositive exact endpoint
difference at the actual stationary terminal payoff, provided the root has
positive one-stage absorption. -/
theorem stationaryEndpointDifference_nonpos_of_faceNumerator_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hazard : ι → ℝ) (hhazard0 : ∀ who, 0 ≤ hazard who)
    (hhazard1 : ∀ who, hazard who ≤ 1)
    (habsorption : 0 < quittingRootAbsorptionMass
      (rootOfHazard hazard hhazard0 hhazard1))
    (who : ι)
    (hnumerator : quittingFaceNumerator
      (weightOfReward reward) hazard who ≤ 0) :
    quittingRootEndpointDifference reward
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward
            (rootOfHazard hazard hhazard0 hhazard1)) player)
        (rootOfHazard hazard hhazard0 hhazard1) who ≤ 0 := by
  have hidentity := (quittingStationaryGain_identities reward
    (rootOfHazard hazard hhazard0 hhazard1) who).1
  rw [quittingStationaryGain_rootOfHazard_eq_faceNumerator
    reward hazard hhazard0 hhazard1 who] at hidentity
  nlinarith

/-- Pointwise stationary gain complementarity bounds the complete behavioral
unilateral cap.  The cap includes arbitrary history-dependent deviations. -/
theorem quittingStationaryFullRateUnilateralCap_le_of_gain_signs
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hcontinue : (root who false).toReal *
      quittingStationaryGain reward root who ≤ 0)
    (hquit : 0 ≤ (root who true).toReal *
      quittingStationaryGain reward root who) :
    quittingStationaryFullRateUnilateralCap reward root who ≤
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) who := by
  let value := quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) who
  let quitValue := quittingStationaryFixedOpponentsQuitValue reward root who
  let continueReward :=
    quittingStationaryFixedOpponentsContinueReward reward root who
  let continueMass := quittingStationaryFixedOpponentsContinueMass root who
  have hidentities := quittingStationaryGain_identities reward root who
  have hquitValue : quitValue ≤ value := by
    have hidentity := hidentities.2.1
    dsimp only [quitValue, value] at hidentity ⊢
    nlinarith
  have hnever : quittingStationaryNeverValue continueReward continueMass ≤ value := by
    have hidentity := hidentities.2.2
    have hdenominator : 0 < 1 - continueMass := sub_pos.mpr hcontracts
    unfold quittingStationaryNeverValue
    rw [div_le_iff₀ hdenominator]
    dsimp only [continueReward, continueMass, value] at hidentity ⊢
    nlinarith
  rw [quittingStationaryFullRateUnilateralCap_of_lt reward root who hcontracts]
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
  exact max_le hquitValue hnever

/-- A terminal exploitability gap must select a coordinate on the lower face
of a constrained stationary Nash root.  Moreover its unrestricted behavioral
gain is already visible in the checked full-rate unilateral cap. -/
theorem exists_lowerFace_fullRateGain_of_terminalGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {epsilon gap : ℝ} (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon ≤ 1) (hgap : 0 < gap)
    (hazard : ι → ℝ) (hhazardLower : ∀ who, epsilon ≤ hazard who)
    (hhazardUpper : ∀ who, hazard who ≤ 1)
    (hbest : ∀ who rate, epsilon ≤ rate → rate ≤ 1 →
      rate * quittingFaceNumerator (weightOfReward reward) hazard who ≤
        hazard who * quittingFaceNumerator
          (weightOfReward reward) hazard who)
    (hcontracts : ∀ who,
      quittingStationaryFixedOpponentsContinueMass
        (rootOfHazard hazard
          (fun who => hepsilon0.le.trans (hhazardLower who))
          hhazardUpper) who < 1)
    (habsorption : 0 < quittingRootAbsorptionMass
      (rootOfHazard hazard
        (fun who => hepsilon0.le.trans (hhazardLower who))
        hhazardUpper))
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    ∃ who,
      hazard who = epsilon ∧
      quittingTerminalPayoff reward
          (quittingStationaryProfile reward
            (rootOfHazard hazard
              (fun who => hepsilon0.le.trans (hhazardLower who))
              hhazardUpper)) who + gap ≤
        quittingStationaryFullRateUnilateralCap reward
          (rootOfHazard hazard
            (fun who => hepsilon0.le.trans (hhazardLower who))
            hhazardUpper) who := by
  let root := rootOfHazard hazard
    (fun who => hepsilon0.le.trans (hhazardLower who)) hhazardUpper
  obtain ⟨who, deviation, himprove⟩ :=
    hexploit (quittingStationaryProfile reward root)
  have hbound := quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap
    reward root who deviation
  have hcapGain : quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) who + gap ≤
        quittingStationaryFullRateUnilateralCap reward root who :=
    himprove.trans hbound
  have hlower : hazard who = epsilon := by
    apply le_antisymm
    · by_contra hnot
      have hstrict : epsilon < hazard who := lt_of_not_ge hnot
      have hnumerator :=
        quittingFaceNumerator_nonneg_of_constrainedNash_of_lower_lt
          hbest hepsilon1 who hstrict
      have hgain : 0 ≤ quittingStationaryGain reward root who := by
        rw [quittingStationaryGain_rootOfHazard_eq_faceNumerator
          reward hazard (fun player => hepsilon0.le.trans (hhazardLower player))
            hhazardUpper who]
        exact hnumerator
      have hquit : 0 ≤ (root who true).toReal *
          quittingStationaryGain reward root who :=
        mul_nonneg ENNReal.toReal_nonneg hgain
      have hcontinue : (root who false).toReal *
          quittingStationaryGain reward root who ≤ 0 := by
        by_cases hsaturated : hazard who = 1
        · have hfalse : (root who false).toReal = 0 := by
            simp [root, rootOfHazard, hsaturated]
          rw [hfalse, zero_mul]
        · have hlt : hazard who < 1 :=
            lt_of_le_of_ne (hhazardUpper who) hsaturated
          have hnumeratorNonpos :=
            quittingFaceNumerator_nonpos_of_constrainedNash_of_lt_one
              hbest hepsilon1 who hlt
          have hgainNonpos : quittingStationaryGain reward root who ≤ 0 := by
            rw [quittingStationaryGain_rootOfHazard_eq_faceNumerator
              reward hazard (fun player => hepsilon0.le.trans (hhazardLower player))
                hhazardUpper who]
            exact hnumeratorNonpos
          exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg hgainNonpos
      have hcap := quittingStationaryFullRateUnilateralCap_le_of_gain_signs
        reward root who (hcontracts who) habsorption hcontinue hquit
      linarith
    · exact hhazardLower who
  exact ⟨who, hlower, hcapGain⟩

/-! ## Quantitative lower-face estimate -/

/-- At the lower coordinate selected by the unrestricted terminal gap, the
one-stage absorption denominator is `O(epsilon)` with the sharp payoff-range
constant used by the normal terminal-gap lift. -/
theorem denominator_le_of_lowerFace_fullRateGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {epsilon gap bound : ℝ} (hepsilon : 0 < epsilon) (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hazard : ι → ℝ) (hhazard0 : ∀ player, 0 ≤ hazard player)
    (hhazard1 : ∀ player, hazard player ≤ 1)
    (who : ι) (hselected : hazard who = epsilon)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass
      (rootOfHazard hazard hhazard0 hhazard1) who < 1)
    (hnumerator : quittingFaceNumerator
      (weightOfReward reward) hazard who ≤ 0)
    (hgain : quittingTerminalPayoff reward
          (quittingStationaryProfile reward
            (rootOfHazard hazard hhazard0 hhazard1)) who + gap ≤
        quittingStationaryFullRateUnilateralCap reward
          (rootOfHazard hazard hhazard0 hhazard1) who) :
    1 - continueMassExcl hazard who +
        epsilon * continueMassExcl hazard who ≤
      2 * bound * epsilon / gap := by
  let root := rootOfHazard hazard hhazard0 hhazard1
  let beta := quittingStationaryFixedOpponentsContinueMass root who
  let quitValue := quittingStationaryFixedOpponentsQuitValue reward root who
  let continueReward :=
    quittingStationaryFixedOpponentsContinueReward reward root who
  let value := quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) who
  have hbeta : beta = continueMassExcl hazard who := by
    exact quittingStationaryFixedOpponentsContinueMass_rootOfHazard
      hazard hhazard0 hhazard1 who
  have hdelta : 0 < 1 - beta := sub_pos.mpr hcontracts
  have hbetaNonneg : 0 ≤ beta :=
    quittingStationaryContinueMass_nonneg
      (Function.update root who (PMF.pure false))
  have hdenominator : 0 < 1 - beta + epsilon * beta := by
    positivity
  have hrootQuit : (root who true).toReal = epsilon := by
    simp [root, rootOfHazard, hselected]
  have hrootContinue : (root who false).toReal = 1 - epsilon := by
    simp [root, rootOfHazard, hselected]
  have habsorption :=
    quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul root who
  rw [hrootContinue] at habsorption
  have habsorption' : quittingRootAbsorptionMass root =
      1 - beta + epsilon * beta := by
    rw [habsorption]
    dsimp only [beta]
    ring
  have hbalance :=
    quittingRootAbsorptionMass_mul_stationaryTerminalValue reward root who
  rw [hrootQuit, hrootContinue] at hbalance
  have hvalue :
      value = constrainedStationaryValue epsilon quitValue continueReward beta := by
    unfold constrainedStationaryValue
    apply (eq_div_iff hdenominator.ne').2
    rw [← habsorption']
    simpa [value, quitValue, continueReward, mul_comm] using hbalance
  have hface : (1 - beta) * quitValue - continueReward ≤ 0 := by
    have hface' := hnumerator
    rw [← quittingStationaryGain_rootOfHazard_eq_faceNumerator
      reward hazard hhazard0 hhazard1 who] at hface'
    simpa [quittingStationaryGain, beta, quitValue, continueReward] using hface'
  have hquitLeNever : quitValue ≤ continueReward / (1 - beta) := by
    rw [le_div_iff₀ hdelta]
    linarith
  have hcap : quittingStationaryFullRateUnilateralCap reward root who =
      continueReward / (1 - beta) := by
    rw [quittingStationaryFullRateUnilateralCap_of_lt reward root who hcontracts]
    unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
      quittingStationaryNeverValue
    simpa [beta, quitValue, continueReward] using
      (max_eq_right hquitLeNever)
  have hgain' : gap ≤ continueReward / (1 - beta) - value := by
    rw [hcap] at hgain
    simpa [root, value] using (sub_le_sub_right hgain value)
  have hidentity := neverValue_sub_constrainedStationaryValue_eq_one_sub
    epsilon quitValue continueReward beta hdelta.ne' hdenominator.ne'
  rw [← hvalue] at hidentity
  have hscaledGain : gap ≤
      epsilon * (continueReward / (1 - beta) - quitValue) /
        (1 - beta + epsilon * beta) := by
    rw [← hidentity]
    exact hgain'
  have hquitBound : |quitValue| ≤ bound := by
    have hboundNonneg : 0 ≤ bound :=
      (abs_nonneg (reward (quittingSingletonTerminal who) who)).trans
        (hreward (quittingSingletonTerminal who) who)
    unfold quitValue quittingStationaryFixedOpponentsQuitValue
      quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    apply abs_quittingRootExpectedPayoff_le_bound reward (0 : Payoff ι)
      (Function.update root who (PMF.pure true)) who hreward
    intro player
    simpa using hboundNonneg
  let neverRoot := Function.update root who (PMF.pure false)
  have hneverMass : quittingStationaryContinueMass neverRoot = beta := rfl
  have hneverContribution :
      quittingRootAbsorbingContribution reward neverRoot who = continueReward := rfl
  have hneverValue : quittingTerminalPayoff reward
      (quittingStationaryProfile reward neverRoot) who =
        continueReward / (1 - beta) := by
    rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div
      reward neverRoot who]
    · rw [hneverMass, hneverContribution]
    · simpa [hneverMass] using hcontracts
  have hneverBound : |continueReward / (1 - beta)| ≤ bound := by
    rw [← hneverValue]
    exact abs_quittingTerminalPayoff_le reward
      (quittingStationaryProfile reward neverRoot) who hreward
  have hrange : continueReward / (1 - beta) - quitValue ≤ 2 * bound := by
    have hneverUpper := le_of_abs_le hneverBound
    have hquitLower := neg_le_of_abs_le hquitBound
    linarith
  have hbound := denominator_le_two_mul_bound_mul_epsilon_div_gap
    hepsilon hgap hdenominator hscaledGain hrange
  simpa [hbeta] using hbound

/-- A uniform terminal exploitability gap cannot exceed the diameter of a
coordinatewise bounded terminal reward table. -/
theorem terminalExploitabilityGap_le_two_mul_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap bound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    gap ≤ 2 * bound := by
  obtain ⟨who, deviation, himprove⟩ :=
    hexploit (quittingAlwaysContinueProfile reward)
  have hbase := abs_quittingTerminalPayoff_le reward
    (quittingAlwaysContinueProfile reward) who hreward
  have hdeviation := abs_quittingTerminalPayoff_le reward
    (Function.update (quittingAlwaysContinueProfile reward) who deviation)
      who hreward
  have hbaseLower := neg_le_of_abs_le hbase
  have hdeviationUpper := le_of_abs_le hdeviation
  linarith

/-- **Quantitative constrained-root producer.**  At every sufficiently small
lower cutoff, terminal exploitability produces a literal stationary product
root whose total hazard is `O(epsilon)`, whose normalized direction has the
exact full-support floor, and whose actual stationary endpoint differences
are all nonpositive. -/
theorem exists_quantitative_normalTerminalGap_root
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap bound epsilon : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hsmall :
      (1 + (2 * bound / gap) * (Fintype.card ι - 1)) * epsilon ≤ 1 / 2) :
    ∃ root : ι → PMF Bool,
      0 < quittingStationaryTotalHazard root ∧
      quittingStationaryTotalHazard root ≤
        (1 + (2 * bound / gap) * (Fintype.card ι - 1)) * epsilon ∧
      quittingStationaryTotalHazard root ≤ 1 / 2 ∧
      (∀ who,
        1 / (1 + (2 * bound / gap) * (Fintype.card ι - 1)) ≤
          (root who true).toReal /
            quittingStationaryTotalHazard root) ∧
      ∀ who,
        quittingRootEndpointDifference reward
            (fun player => quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) player)
            root who ≤ 0 := by
  let coefficient := 2 * bound / gap
  let totalBound := 1 + coefficient * (Fintype.card ι - 1)
  have hgapBound : gap ≤ 2 * bound :=
    terminalExploitabilityGap_le_two_mul_bound reward hreward hexploit
  have hboundPos : 0 < bound := by linarith
  have hcoefficientNonneg : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  have htotalBoundPos : 0 < totalBound := by
    dsimp only [totalBound]
    obtain ⟨first, second, hne⟩ := exists_pair_ne ι
    have hcardNat : 1 < Fintype.card ι :=
      Fintype.one_lt_card_iff.mpr ⟨first, second, hne⟩
    have hcardReal : (1 : ℝ) < Fintype.card ι := by
      exact_mod_cast hcardNat
    have hcardNonneg : (0 : ℝ) ≤ Fintype.card ι - 1 := by
      exact sub_nonneg.mpr hcardReal.le
    positivity
  obtain ⟨hazard, hhazardLower, hhazardUpper, hbest⟩ :=
    exists_constrainedStationaryFaceNash reward hepsilon1.le
  have hhazard0 : ∀ who, 0 ≤ hazard who := fun who =>
    hepsilon0.le.trans (hhazardLower who)
  have hhazardPos : ∀ who, 0 < hazard who := fun who =>
    hepsilon0.trans_le (hhazardLower who)
  let root := rootOfHazard hazard hhazard0 hhazardUpper
  have hcontracts : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    intro who
    exact quittingStationaryFixedOpponentsContinueMass_rootOfHazard_lt_one
      hazard hhazard0 hhazardUpper hhazardPos who
  have habsorption : 0 < quittingRootAbsorptionMass root :=
    quittingRootAbsorptionMass_rootOfHazard_pos hazard hhazard0 hhazardUpper
      (hhazardPos (Classical.choice inferInstance))
  obtain ⟨selected, hselected, hselectedGain⟩ :=
    exists_lowerFace_fullRateGain_of_terminalGap reward hepsilon0
      hepsilon1.le hgap hazard hhazardLower hhazardUpper hbest hcontracts
        habsorption hexploit
  have hselectedNumerator : quittingFaceNumerator
      (weightOfReward reward) hazard selected ≤ 0 := by
    apply quittingFaceNumerator_nonpos_of_constrainedNash_of_lt_one
      hbest hepsilon1.le selected
    simpa [hselected] using hepsilon1
  have hdenominator := denominator_le_of_lowerFace_fullRateGain
    reward hepsilon0 hgap hreward hazard hhazard0 hhazardUpper selected
      hselected (hcontracts selected) hselectedNumerator hselectedGain
  have hopponents : ∀ who, who ≠ selected →
      hazard who ≤ coefficient * epsilon := by
    intro who hwho
    have hcoordinate := Math.PMFProduct.coordinate_le_one_sub_prod_one_sub
      hazard (Finset.univ.erase selected)
      (fun player _ => hhazard0 player)
      (fun player _ => hhazardUpper player)
      (show who ∈ Finset.univ.erase selected by simp [hwho])
    have hdelta : 1 - continueMassExcl hazard selected ≤
        1 - continueMassExcl hazard selected +
          epsilon * continueMassExcl hazard selected := by
      have hmassNonneg : 0 ≤ continueMassExcl hazard selected := by
        rw [← quittingStationaryFixedOpponentsContinueMass_rootOfHazard
          hazard hhazard0 hhazardUpper selected]
        exact quittingStationaryContinueMass_nonneg
          (Function.update root selected (PMF.pure false))
      exact le_add_of_nonneg_right (mul_nonneg hepsilon0.le hmassNonneg)
    calc
      hazard who ≤ 1 - continueMassExcl hazard selected := by
        simpa [continueMassExcl] using hcoordinate
      _ ≤ 1 - continueMassExcl hazard selected +
          epsilon * continueMassExcl hazard selected := hdelta
      _ ≤ 2 * bound * epsilon / gap := hdenominator
      _ = coefficient * epsilon := by
        dsimp only [coefficient]
        ring
  have hsum : ∑ who, hazard who ≤ totalBound * epsilon := by
    have h := sum_hazard_le_of_selected_eq_and_opponents_le
      hazard selected epsilon coefficient hselected hopponents
    simpa [totalBound] using h
  have hsumPos : 0 < ∑ who, hazard who := by
    have hsingle : hazard selected ≤ ∑ who, hazard who :=
      Finset.single_le_sum (fun who _ => (hhazard0 who))
        (Finset.mem_univ selected)
    linarith [hhazardLower selected]
  have htotal : quittingStationaryTotalHazard root = ∑ who, hazard who := by
    unfold quittingStationaryTotalHazard
    simp [root, rootOfHazard]
  have hrootTotalPos : 0 < quittingStationaryTotalHazard root := by
    rwa [htotal]
  have hrootHalf : quittingStationaryTotalHazard root ≤ 1 / 2 := by
    rw [htotal]
    exact hsum.trans (by simpa [totalBound, coefficient] using hsmall)
  have hhazardLtOne : ∀ who, hazard who < 1 := by
    intro who
    have hcoordinate : hazard who ≤ ∑ player, hazard player :=
      Finset.single_le_sum (fun player _ => hhazard0 player)
        (Finset.mem_univ who)
    rw [← htotal] at hcoordinate
    linarith [hrootHalf]
  have hendpoint : ∀ who,
      quittingRootEndpointDifference reward
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player)
          root who ≤ 0 := by
    intro who
    have hnumerator :=
      quittingFaceNumerator_nonpos_of_constrainedNash_of_lt_one
        hbest hepsilon1.le who (hhazardLtOne who)
    exact stationaryEndpointDifference_nonpos_of_faceNumerator_nonpos
      reward hazard hhazard0 hhazardUpper habsorption who hnumerator
  refine ⟨root, hrootTotalPos, ?_, hrootHalf, ?_, hendpoint⟩
  · rw [htotal]
    simpa [totalBound, coefficient] using hsum
  intro who
  have hfloor := normalized_hazard_ge_inv hazard epsilon totalBound
    hepsilon0 htotalBoundPos hhazardLower hsum who
  change 1 / totalBound ≤
    (root who true).toReal / quittingStationaryTotalHazard root
  rw [htotal]
  simpa [root, rootOfHazard] using hfloor

/-- **Normal terminal-gap full-support lift.**  If a bounded finite quitting
game has a uniform positive terminal exploitability gap and every player is
punishment-normal, then the game has a normalized singleton source packet
with literal full support.  The displayed mass floor keeps the exact generic
coordinate bound supplied by the caller. -/
theorem exists_fullSupport_normalizedSingletonSourcePacket_of_normal_terminalGap
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap bound : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who) :
    ∃ packet : QuittingNormalizedSingletonSourcePacket reward,
      packet.support = Finset.univ ∧
      ∀ who,
        1 / (1 + (2 * bound / gap) * (Fintype.card ι - 1)) ≤
          packet.mass who := by
  let coefficient := 2 * bound / gap
  let totalBound := 1 + coefficient * (Fintype.card ι - 1)
  have hgapBound : gap ≤ 2 * bound :=
    terminalExploitabilityGap_le_two_mul_bound reward hreward hexploit
  have hboundPos : 0 < bound := by linarith
  have hcoefficientNonneg : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  obtain ⟨first, second, hne⟩ := exists_pair_ne ι
  have hcardNat : 1 < Fintype.card ι :=
    Fintype.one_lt_card_iff.mpr ⟨first, second, hne⟩
  have hcardReal : (1 : ℝ) < Fintype.card ι := by
    exact_mod_cast hcardNat
  have hcardNonneg : (0 : ℝ) ≤ Fintype.card ι - 1 :=
    sub_nonneg.mpr hcardReal.le
  have htotalBoundOne : 1 ≤ totalBound := by
    dsimp only [totalBound]
    exact le_add_of_nonneg_right
      (mul_nonneg hcoefficientNonneg hcardNonneg)
  have htotalBoundPos : 0 < totalBound := zero_lt_one.trans_le htotalBoundOne
  let epsilon : ℕ → ℝ := fun n =>
    (1 / (2 * totalBound)) * (1 / ((n : ℝ) + 1))
  have hepsilon0 : ∀ n, 0 < epsilon n := by
    intro n
    dsimp only [epsilon]
    positivity
  have hrateLeOne : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    apply (div_le_one (by positivity)).2
    norm_num
  have hsmall : ∀ n, totalBound * epsilon n ≤ 1 / 2 := by
    intro n
    have hidentity : totalBound * epsilon n =
        (1 / 2) * (1 / ((n : ℝ) + 1)) := by
      dsimp only [epsilon]
      field_simp [htotalBoundPos.ne']
    rw [hidentity]
    simpa using mul_le_mul_of_nonneg_left (hrateLeOne n)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hepsilon1 : ∀ n, epsilon n < 1 := by
    intro n
    have hscale : epsilon n ≤ totalBound * epsilon n := by
      exact (le_mul_iff_one_le_left (hepsilon0 n)).2 htotalBoundOne
    linarith [hsmall n]
  have hrootExists : ∀ n, ∃ root : ι → PMF Bool,
      0 < quittingStationaryTotalHazard root ∧
      quittingStationaryTotalHazard root ≤ totalBound * epsilon n ∧
      quittingStationaryTotalHazard root ≤ 1 / 2 ∧
      (∀ who, 1 / totalBound ≤
        (root who true).toReal / quittingStationaryTotalHazard root) ∧
      ∀ who,
        quittingRootEndpointDifference reward
            (fun player => quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) player)
            root who ≤ 0 := by
    intro n
    simpa [totalBound, coefficient] using
      (exists_quantitative_normalTerminalGap_root reward hgap hreward
        hexploit (hepsilon0 n) (hepsilon1 n) (by
          simpa [totalBound, coefficient] using hsmall n))
  let roots : ℕ → ι → PMF Bool := fun n => Classical.choose (hrootExists n)
  have hroots : ∀ n,
      0 < quittingStationaryTotalHazard (roots n) ∧
      quittingStationaryTotalHazard (roots n) ≤ totalBound * epsilon n ∧
      quittingStationaryTotalHazard (roots n) ≤ 1 / 2 ∧
      (∀ who, 1 / totalBound ≤
        ((roots n) who true).toReal /
          quittingStationaryTotalHazard (roots n)) ∧
      ∀ who,
        quittingRootEndpointDifference reward
            (fun player => quittingTerminalPayoff reward
              (quittingStationaryProfile reward (roots n)) player)
            (roots n) who ≤ 0 := fun n => Classical.choose_spec (hrootExists n)
  have hepsilonVanish : Tendsto epsilon atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))
        atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [epsilon, mul_comm] using
      hbase.const_mul (1 / (2 * totalBound))
  have htotalVanish : Tendsto
      (fun n => quittingStationaryTotalHazard (roots n))
      atTop (nhds 0) := by
    have hupper : Tendsto (fun n => totalBound * epsilon n)
        atTop (nhds 0) := by
      simpa using hepsilonVanish.const_mul totalBound
    exact squeeze_zero
      (fun n => (hroots n).1.le)
      (fun n => (hroots n).2.1)
      hupper
  obtain ⟨packet, hsupport, hmass⟩ :=
    exists_fullSupport_normalizedSingletonSourcePacket_of_vanishingRoots
      reward roots (one_div_pos.mpr htotalBoundPos)
      (fun n => (hroots n).1)
      (fun n => (hroots n).2.2.1)
      htotalVanish
      (fun n who => by
        rw [quittingStationaryHazardDirection_apply]
        exact (hroots n).2.2.2.1 who)
      (fun n who => (hroots n).2.2.2.2 who)
      hnormal
  refine ⟨packet, hsupport, ?_⟩
  intro who
  simpa [totalBound, coefficient] using hmass who

/-! ## Four-player full-core composition -/

/-- A terminal-exploitability witness on four players yields, for every
supplied coordinate bound, a quantitatively full-support normalized singleton
packet.  The same reward table has full normal core, and hence every player is
punishment-normal. -/
theorem QuittingTerminalExploitabilityWitness.fullSupport_fullNormalCore_of_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    {bound : ℝ} (hreward : ∀ S who, |reward S who| ≤ bound) :
    QuittingLCPClassification.normalCore
        (QuittingLCPClassification.normalizedSoloMatrix reward) =
          Finset.univ ∧
      (∀ who, IsQuittingNormalPlayer reward who) ∧
      ∃ packet : QuittingNormalizedSingletonSourcePacket reward,
        packet.support = Finset.univ ∧
        0 < 1 / (1 + (2 * bound / witness.terminalGap) * 3) ∧
        ∀ who,
          1 / (1 + (2 * bound / witness.terminalGap) * 3) ≤
            packet.mass who := by
  have hnot := witness.not_exists_uniformEquilibriumPayoff
  have hcore :=
    normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
      reward (by norm_num) hnot
  have hnormal : ∀ who, IsQuittingNormalPlayer reward who :=
    QuittingLCPClassification.all_punishmentNormal_of_normalCore_eq_univ
      reward hcore
  have hgapBound : witness.terminalGap ≤ 2 * bound :=
    terminalExploitabilityGap_le_two_mul_bound reward hreward
      witness.terminalExploitability
  have hboundPos : 0 < bound := by
    linarith [witness.terminalGap_pos]
  have hfloorPos :
      0 < 1 / (1 + (2 * bound / witness.terminalGap) * 3) := by
    apply one_div_pos.mpr
    have hratioPos : 0 < 2 * bound / witness.terminalGap := by
      exact div_pos (mul_pos (by norm_num) hboundPos)
        witness.terminalGap_pos
    linarith
  obtain ⟨packet, hsupport, hmass⟩ :=
    exists_fullSupport_normalizedSingletonSourcePacket_of_normal_terminalGap
      reward witness.terminalGap_pos hreward witness.terminalExploitability
        hnormal
  refine ⟨hcore, hnormal, packet, hsupport, hfloorPos, ?_⟩
  intro who
  convert hmass who using 1
  all_goals norm_num

/-- In the four-player no-uniform-payoff branch, the terminal witness, full
normal core, all-player punishment normality, and the quantitative
full-support packet can be chosen for the same reward table. -/
theorem exists_quantitative_fullSupport_fullNormalCore_of_finFour_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ S who, |reward S who| ≤ bound)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ witness : QuittingTerminalExploitabilityWitness reward,
      QuittingLCPClassification.normalCore
          (QuittingLCPClassification.normalizedSoloMatrix reward) =
            Finset.univ ∧
        (∀ who, IsQuittingNormalPlayer reward who) ∧
        ∃ packet : QuittingNormalizedSingletonSourcePacket reward,
          packet.support = Finset.univ ∧
          0 < 1 / (1 + (2 * bound / witness.terminalGap) * 3) ∧
          ∀ who,
            1 / (1 + (2 * bound / witness.terminalGap) * 3) ≤
              packet.mass who := by
  obtain ⟨gap, hgap, hexploit⟩ :=
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).mp hnot
  let witness : QuittingTerminalExploitabilityWitness reward := {
    terminalGap := gap
    terminalGap_pos := hgap
    terminalExploitability := hexploit }
  exact ⟨witness, witness.fullSupport_fullNormalCore_of_finFour hreward⟩

/-- Every four-player quitting table either has a uniform-equilibrium payoff
or lies in the quantitatively full-support, full-normal-core,
punishment-normal residual.  The coordinate bound is supplied by the caller,
so the theorem preserves an exact maximum-coordinate bound when one is used. -/
theorem uniformPayoff_or_quantitative_fullSupport_fullNormalCore_of_finFour
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ S who, |reward S who| ≤ bound) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
    ∃ witness : QuittingTerminalExploitabilityWitness reward,
      QuittingLCPClassification.normalCore
          (QuittingLCPClassification.normalizedSoloMatrix reward) =
            Finset.univ ∧
        (∀ who, IsQuittingNormalPlayer reward who) ∧
        ∃ packet : QuittingNormalizedSingletonSourcePacket reward,
          packet.support = Finset.univ ∧
          0 < 1 / (1 + (2 * bound / witness.terminalGap) * 3) ∧
          ∀ who,
            1 / (1 + (2 * bound / witness.terminalGap) * 3) ≤
              packet.mass who := by
  by_cases hpayoff : ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff
  · exact Or.inl hpayoff
  · exact Or.inr
      (exists_quantitative_fullSupport_fullNormalCore_of_finFour_of_no_uniformPayoff
        reward hreward hpayoff)

/-- **Four-player support transition.**  A support-two normalized singleton
packet either already belongs to a game with a uniform-equilibrium payoff, or
the same reward table has a full-support packet and the normalized solo
matrix has full normal core. -/
theorem uniformPayoff_or_fullSupportFullNormalCore_of_finFour_support_card_two
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupportCard : packet.support.card = 2) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
    ∃ packet' : QuittingNormalizedSingletonSourcePacket reward,
      packet'.support = Finset.univ ∧
      QuittingLCPClassification.normalCore
        (QuittingLCPClassification.normalizedSoloMatrix reward) =
          Finset.univ := by
  by_cases hpayoff : ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff
  · exact Or.inl hpayoff
  · right
    obtain ⟨gap, hgap, hexploit⟩ :=
      (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
        reward).mp hpayoff
    let witness : QuittingTerminalExploitabilityWitness reward := {
      terminalGap := gap
      terminalGap_pos := hgap
      terminalExploitability := hexploit }
    obtain ⟨first, second, hne, hsupport⟩ :=
      Finset.card_eq_two.mp hsupportCard
    have hnormal : ∀ who, quittingPunishmentValue reward who ≤
        reward (quittingSingletonTerminal who) who :=
      witness.all_normal_of_finFour_support_eq_pair packet hne hsupport
    obtain ⟨packet', hpacketSupport, _hmass⟩ :=
      exists_fullSupport_normalizedSingletonSourcePacket_of_normal_terminalGap
        reward hgap (abs_reward_le_quittingRewardBound reward) hexploit hnormal
    have hcore :=
      normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
        reward (by norm_num) hpayoff
    exact ⟨packet', hpacketSupport, hcore⟩

end GameTheory
