/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.PoincareMirandaCube
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler
import UniformEquilibrium.Quitting.Stationary.FaceNumerator

/-!
# Exact stationary equilibria from conditional face gaps

This file gives a positive, source-data criterion for a finite quitting game.
On an arbitrary rectangular hazard box, each player's division-free stationary
face numerator is assigned to one coordinate by a permutation.  A strict
positive sign on the lower face and a weak negative sign on the upper face
produce a positive common zero by Poincare--Miranda.  At that zero, every
player's pure-Quit and pure-Continue endpoints coincide at the endogenous
value `sigmaValue`.

The resulting product row is an exact terminal Nash equilibrium against every
behavioral unilateral deviation and implements its value as a uniform-
equilibrium payoff.  This is a special face class, not a producer for arbitrary
quitting games.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open Math.Topology Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Affine normalization of a coordinatewise real box by the unit cube. -/
def affineHazardBox
    (lower upper point : ι → ℝ) (who : ι) : ℝ :=
  lower who + (upper who - lower who) * point who

omit [Fintype ι] [DecidableEq ι] in
/-- Affine normalization of a finite box is continuous. -/
theorem continuous_affineHazardBox (lower upper : ι → ℝ) :
    Continuous (affineHazardBox lower upper) := by
  apply continuous_pi
  intro who
  exact continuous_const.add (continuous_const.mul (continuous_apply who))

private def conditionalFaceField
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ι → ℝ) (blocker : Equiv.Perm ι)
    (point : ι → ℝ) (coordinate : ι) : ℝ :=
  quittingFaceNumerator (weightOfReward reward)
    (affineHazardBox lower upper point) (blocker.symm coordinate)

private lemma continuous_conditionalFaceField
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ι → ℝ) (blocker : Equiv.Perm ι) :
    Continuous (conditionalFaceField reward lower upper blocker) := by
  apply continuous_pi
  intro coordinate
  exact (continuous_quittingFaceNumerator
    (weightOfReward reward) (blocker.symm coordinate)).comp
      (continuous_affineHazardBox lower upper)

omit [Fintype ι] [DecidableEq ι] in
private lemma affineHazardBox_mem
    {lower upper point : ι → ℝ}
    (hgap : ∀ who, lower who < upper who)
    (hpoint : point ∈ Icc (fun _ => 0) (fun _ => 1)) :
    affineHazardBox lower upper point ∈ Icc lower upper := by
  constructor
  · intro who
    unfold affineHazardBox
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr (hgap who).le)
      (hpoint.1 who))
  · intro who
    unfold affineHazardBox
    nlinarith [hpoint.2 who, hgap who]

omit [Fintype ι] [DecidableEq ι] in
private lemma affineHazardBox_lower_face
    {lower upper point : ι → ℝ} {coordinate : ι}
    (hface : point coordinate = 0) :
    affineHazardBox lower upper point coordinate = lower coordinate := by
  simp [affineHazardBox, hface]

omit [Fintype ι] [DecidableEq ι] in
private lemma affineHazardBox_upper_face
    {lower upper point : ι → ℝ} {coordinate : ι}
    (hface : point coordinate = 1) :
    affineHazardBox lower upper point coordinate = upper coordinate := by
  simp [affineHazardBox, hface]

/-- Division-free face signs on an arbitrary coordinatewise hazard box
produce a zero strictly above every lower face.  The upper bounds may bind. -/
theorem exists_hazard_quittingFaceNumerator_eq_zero_of_faceGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ι → ℝ) (blocker : Equiv.Perm ι)
    (hgap : ∀ who, lower who < upper who)
    (hlowerFace : ∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = lower (blocker who) →
        0 < quittingFaceNumerator (weightOfReward reward) hazard who)
    (hupperFace : ∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = upper (blocker who) →
        quittingFaceNumerator (weightOfReward reward) hazard who ≤ 0) :
    ∃ hazard : ι → ℝ,
      (∀ who, lower who < hazard who) ∧
        (∀ who, hazard who ≤ upper who) ∧
          ∀ who,
            quittingFaceNumerator (weightOfReward reward) hazard who = 0 := by
  obtain ⟨point, hpoint, hpointPos, hzero⟩ :=
    exists_cube_zero_pos_of_opposite_face_signs
      (conditionalFaceField reward lower upper blocker)
      (continuous_conditionalFaceField reward lower upper blocker)
      (fun point hpoint coordinate hface => by
        let hazard := affineHazardBox lower upper point
        let who := blocker.symm coordinate
        have hcoordinate : blocker who = coordinate :=
          blocker.apply_symm_apply coordinate
        exact hlowerFace hazard (affineHazardBox_mem hgap hpoint) who (by
          rw [hcoordinate]
          exact affineHazardBox_lower_face hface))
      (fun point hpoint coordinate hface => by
        let hazard := affineHazardBox lower upper point
        let who := blocker.symm coordinate
        have hcoordinate : blocker who = coordinate :=
          blocker.apply_symm_apply coordinate
        exact hupperFace hazard (affineHazardBox_mem hgap hpoint) who (by
          rw [hcoordinate]
          exact affineHazardBox_upper_face hface))
  let hazard := affineHazardBox lower upper point
  refine ⟨hazard, fun who => ?_, fun who => ?_, fun who => ?_⟩
  · dsimp [hazard, affineHazardBox]
    exact lt_add_of_pos_right _ (mul_pos (sub_pos.mpr (hgap who)) (hpointPos who))
  · exact (affineHazardBox_mem hgap hpoint).2 who
  · have hwho := hzero (blocker who)
    simpa only [conditionalFaceField, blocker.symm_apply_apply, hazard] using hwho

/-- Strict signs on both face families refine the preceding zero to the open
box. -/
theorem exists_hazard_quittingFaceNumerator_eq_zero_of_strictFaceGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ι → ℝ) (blocker : Equiv.Perm ι)
    (hgap : ∀ who, lower who < upper who)
    (hlowerFace : ∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = lower (blocker who) →
        0 < quittingFaceNumerator (weightOfReward reward) hazard who)
    (hupperFace : ∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = upper (blocker who) →
        quittingFaceNumerator (weightOfReward reward) hazard who < 0) :
    ∃ hazard : ι → ℝ,
      (∀ who, lower who < hazard who) ∧
        (∀ who, hazard who < upper who) ∧
          ∀ who,
            quittingFaceNumerator (weightOfReward reward) hazard who = 0 := by
  obtain ⟨point, _hpoint, hinterior, hzero⟩ :=
    exists_cube_zero_interior_of_strict_opposite_face_signs
      (conditionalFaceField reward lower upper blocker)
      (continuous_conditionalFaceField reward lower upper blocker)
      (fun point hpoint coordinate hface => by
        let hazard := affineHazardBox lower upper point
        let who := blocker.symm coordinate
        have hcoordinate : blocker who = coordinate :=
          blocker.apply_symm_apply coordinate
        exact hlowerFace hazard (affineHazardBox_mem hgap hpoint) who (by
          rw [hcoordinate]
          exact affineHazardBox_lower_face hface))
      (fun point hpoint coordinate hface => by
        let hazard := affineHazardBox lower upper point
        let who := blocker.symm coordinate
        have hcoordinate : blocker who = coordinate :=
          blocker.apply_symm_apply coordinate
        exact hupperFace hazard (affineHazardBox_mem hgap hpoint) who (by
          rw [hcoordinate]
          exact affineHazardBox_upper_face hface))
  let hazard := affineHazardBox lower upper point
  refine ⟨hazard, fun who => ?_, fun who => ?_, fun who => ?_⟩
  · dsimp [hazard, affineHazardBox]
    exact lt_add_of_pos_right _
      (mul_pos (sub_pos.mpr (hgap who)) (hinterior who).1)
  · dsimp [hazard, affineHazardBox]
    nlinarith [hgap who, (hinterior who).2]
  · have hwho := hzero (blocker who)
    simpa only [conditionalFaceField, blocker.symm_apply_apply, hazard] using hwho

/-- The complete stationary certificate extracted from conditional face
gaps.  Its equilibrium claims quantify over arbitrary behavioral unilateral
deviations. -/
structure QuittingConditionalFaceGapStationaryCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ι → ℝ) where
  hazard : ι → ℝ
  lower_lt_hazard : ∀ who, lower who < hazard who
  hazard_le_upper : ∀ who, hazard who ≤ upper who
  faceNumerator_eq : ∀ who,
    quittingFaceNumerator (weightOfReward reward) hazard who = 0
  hazard_nonneg : ∀ who, 0 ≤ hazard who
  hazard_le_one : ∀ who, hazard who ≤ 1
  value : Payoff ι
  value_eq_sigmaValue : ∀ who,
    value who = sigmaValue (weightOfReward reward) hazard who
  quitEndpoint_eq : ∀ who,
    quittingRootQuitPayoff reward value
      (rootOfHazard hazard hazard_nonneg hazard_le_one) who = value who
  continueEndpoint_eq : ∀ who,
    quittingRootContinuePayoff reward value
      (rootOfHazard hazard hazard_nonneg hazard_le_one) who = value who
  fixedPoint : value = quittingRootSuccessorPayoff reward value
    (rootOfHazard hazard hazard_nonneg hazard_le_one)
  endpointNash : IsεQuittingRootEndpointNash reward value 0
    (rootOfHazard hazard hazard_nonneg hazard_le_one)
  jointlyContracts : quittingStationaryContinueMass
    (rootOfHazard hazard hazard_nonneg hazard_le_one) < 1
  opponentsContract : ∀ who,
    quittingStationaryFixedOpponentsContinueMass
      (rootOfHazard hazard hazard_nonneg hazard_le_one) who < 1
  terminalPayoff_eq : quittingTerminalPayoff reward
    (quittingStationaryProfile reward
      (rootOfHazard hazard hazard_nonneg hazard_le_one)) = value
  terminalNash : (quittingGame reward).IsεAsymptoticNash
    (quittingTerminalPayoff reward) 0
    (quittingStationaryProfile reward
      (rootOfHazard hazard hazard_nonneg hazard_le_one))
  uniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none value

/-- A positive division-free common zero compiles to a complete exact
stationary certificate. -/
def quittingConditionalFaceGapStationaryCertificateOfFaceNumeratorZero
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper hazard : ι → ℝ)
    (hlower : ∀ who, 0 ≤ lower who)
    (hupper : ∀ who, upper who ≤ 1)
    (hlowerHazard : ∀ who, lower who < hazard who)
    (hhazardUpper : ∀ who, hazard who ≤ upper who)
    (hnumerator : ∀ who,
      quittingFaceNumerator (weightOfReward reward) hazard who = 0) :
    QuittingConditionalFaceGapStationaryCertificate reward lower upper := by
  have hnonneg : ∀ who, 0 ≤ hazard who := fun who =>
    (hlower who).trans (hlowerHazard who).le
  have hleOne : ∀ who, hazard who ≤ 1 := fun who =>
    (hhazardUpper who).trans (hupper who)
  let value : Payoff ι := fun who =>
    sigmaValue (weightOfReward reward) hazard who
  let root := rootOfHazard hazard hnonneg hleOne
  have hquit : ∀ who,
      quittingRootQuitPayoff reward value root who = value who := by
    intro who
    rw [quittingRootQuitPayoff_eq_sigmaValue]
    simp [root, value]
  have hcontinue : ∀ who,
      quittingRootContinuePayoff reward value root who = value who := by
    intro who
    rw [quittingRootContinuePayoff_eq_gammaValue]
    rw [show hazardOfRoot root = hazard by simp [root]]
    exact gammaValue_sigmaValue_eq_of_quittingFaceNumerator_eq_zero
      (weightOfReward reward) hazard who (hnumerator who)
  have hfixed : value = quittingRootSuccessorPayoff reward value root := by
    funext who
    rw [quittingRootSuccessorPayoff_eq_endpointMix, hquit who, hcontinue who]
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    calc
      value who = ((root who false).toReal + (root who true).toReal) * value who := by
        rw [hsum, one_mul]
      _ = (root who true).toReal * value who +
          (root who false).toReal * value who := by ring
  have hendpoint : IsεQuittingRootEndpointNash reward value 0 root := by
    intro who
    simp [quittingRootEndpointDifference, hquit who, hcontinue who]
  have hpositive : ∀ who, 0 < hazard who := fun who =>
    (hlower who).trans_lt (hlowerHazard who)
  have hjoint : quittingStationaryContinueMass root < 1 := by
    let who : ι := Classical.choice (inferInstance : Nonempty ι)
    calc
      quittingStationaryContinueMass root ≤ (root who false).toReal :=
        quittingStationaryContinueMass_le_ownContinueProbability root who
      _ < 1 := by simp [root, rootOfHazard, hpositive who]
  have hopponents : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    intro who
    obtain ⟨other, hother⟩ := exists_ne who
    unfold quittingStationaryFixedOpponentsContinueMass
    calc
      quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) ≤
          (Function.update root who (PMF.pure false) other false).toReal :=
        quittingStationaryContinueMass_le_ownContinueProbability _ other
      _ = (root other false).toReal := by rw [Function.update_of_ne hother]
      _ < 1 := by simp [root, rootOfHazard, hpositive other]
  have hterminal := quittingTerminalPayoff_stationary_eq_of_fixedPoint
    reward root value hjoint hfixed
  have hnash :=
    isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
      reward root value hjoint hfixed hendpoint hopponents
  have huniform :=
    isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
      reward root value hjoint hfixed hendpoint hopponents
  exact {
    hazard := hazard
    lower_lt_hazard := hlowerHazard
    hazard_le_upper := hhazardUpper
    faceNumerator_eq := hnumerator
    hazard_nonneg := hnonneg
    hazard_le_one := hleOne
    value := value
    value_eq_sigmaValue := fun _ => rfl
    quitEndpoint_eq := hquit
    continueEndpoint_eq := hcontinue
    fixedPoint := hfixed
    endpointNash := hendpoint
    jointlyContracts := hjoint
    opponentsContract := hopponents
    terminalPayoff_eq := hterminal
    terminalNash := hnash
    uniformEquilibriumPayoff := huniform }

/-- Conditional face gaps on a positive hazard box produce an exact stationary
equilibrium and its endogenous uniform-equilibrium payoff. -/
theorem exists_stationaryCertificate_of_conditionalFaceGap [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ι → ℝ) (blocker : Equiv.Perm ι)
    (hlower : ∀ who, 0 ≤ lower who)
    (hgap : ∀ who, lower who < upper who)
    (hupper : ∀ who, upper who ≤ 1)
    (hlowerFace : ∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = lower (blocker who) →
        0 < quittingFaceNumerator (weightOfReward reward) hazard who)
    (hupperFace : ∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = upper (blocker who) →
        quittingFaceNumerator (weightOfReward reward) hazard who ≤ 0) :
    Nonempty
      (QuittingConditionalFaceGapStationaryCertificate reward lower upper) := by
  obtain ⟨hazard, hlowerHazard, hhazardUpper, hnumerator⟩ :=
    exists_hazard_quittingFaceNumerator_eq_zero_of_faceGap
      reward lower upper blocker hgap hlowerFace hupperFace
  exact ⟨quittingConditionalFaceGapStationaryCertificateOfFaceNumeratorZero
    reward lower upper hazard hlower hupper hlowerHazard hhazardUpper hnumerator⟩

/-- Strict upper-face signs produce a complete stationary certificate whose
hazard lies in the open box. -/
theorem exists_stationaryCertificate_of_strictConditionalFaceGap
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ι → ℝ) (blocker : Equiv.Perm ι)
    (hlower : ∀ who, 0 ≤ lower who)
    (hgap : ∀ who, lower who < upper who)
    (hupper : ∀ who, upper who ≤ 1)
    (hlowerFace : ∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = lower (blocker who) →
        0 < quittingFaceNumerator (weightOfReward reward) hazard who)
    (hupperFace : ∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = upper (blocker who) →
        quittingFaceNumerator (weightOfReward reward) hazard who < 0) :
    ∃ certificate :
        QuittingConditionalFaceGapStationaryCertificate reward lower upper,
      ∀ who, certificate.hazard who < upper who := by
  obtain ⟨hazard, hlowerHazard, hhazardUpper, hnumerator⟩ :=
    exists_hazard_quittingFaceNumerator_eq_zero_of_strictFaceGap
      reward lower upper blocker hgap hlowerFace hupperFace
  let certificate :=
    quittingConditionalFaceGapStationaryCertificateOfFaceNumeratorZero
    reward lower upper hazard hlower hupper hlowerHazard
      (fun who => (hhazardUpper who).le) hnumerator
  refine ⟨certificate, ?_⟩
  simpa only [certificate,
    quittingConditionalFaceGapStationaryCertificateOfFaceNumeratorZero] using
      hhazardUpper

/-- Direct exact stationary-payoff and behavioral terminal-Nash capstone for
conditional face gaps. -/
theorem exists_stationaryTerminalNash_of_conditionalFaceGap [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ι → ℝ) (blocker : Equiv.Perm ι)
    (hlower : ∀ who, 0 ≤ lower who)
    (hgap : ∀ who, lower who < upper who)
    (hupper : ∀ who, upper who ≤ 1)
    (hlowerFace : ∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = lower (blocker who) →
        0 < quittingFaceNumerator (weightOfReward reward) hazard who)
    (hupperFace : ∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = upper (blocker who) →
        quittingFaceNumerator (weightOfReward reward) hazard who ≤ 0) :
    ∃ (value : Payoff ι) (root : ι → PMF Bool),
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) = value ∧
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) 0
          (quittingStationaryProfile reward root) := by
  let certificate := (exists_stationaryCertificate_of_conditionalFaceGap
    reward lower upper blocker hlower hgap hupper hlowerFace hupperFace).some
  exact ⟨certificate.value,
    rootOfHazard certificate.hazard certificate.hazard_nonneg certificate.hazard_le_one,
    certificate.terminalPayoff_eq, certificate.terminalNash⟩

/-- Direct uniform-payoff capstone for conditional face gaps. -/
theorem exists_uniformEquilibriumPayoff_of_conditionalFaceGap [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ι → ℝ) (blocker : Equiv.Perm ι)
    (hlower : ∀ who, 0 ≤ lower who)
    (hgap : ∀ who, lower who < upper who)
    (hupper : ∀ who, upper who ≤ 1)
    (hlowerFace : ∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = lower (blocker who) →
        0 < quittingFaceNumerator (weightOfReward reward) hazard who)
    (hupperFace : ∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = upper (blocker who) →
        quittingFaceNumerator (weightOfReward reward) hazard who ≤ 0) :
    ∃ value : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  let certificate := (exists_stationaryCertificate_of_conditionalFaceGap
    reward lower upper blocker hlower hgap hupper hlowerFace hupperFace).some
  exact ⟨certificate.value, certificate.uniformEquilibriumPayoff⟩

end GameTheory
