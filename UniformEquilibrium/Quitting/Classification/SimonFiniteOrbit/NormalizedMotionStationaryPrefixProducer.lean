/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PositiveAbsorptionStationarySplice
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.CompactQuantitativeAlternatives
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.SurvivalCrossingRepair
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchResiduals
import UniformEquilibrium.Quitting.Stationary.BestResponse
import UniformEquilibrium.Quitting.Terminal.TargetTail.DiagonalTargetTailSemantics

/-!
# Normalized motion produces a stationary-prefix equilibrium

A rational support-local product row whose one-stage successor moves by less
than its error times its absorption mass has an absorbing stationary payoff
within that error of the displayed continuation.  Repeating the row over a
carefully chosen exposure window and then punishing a largest-hazard player
produces the corrected stationarily generated branch.

The final contrapositive removes the previously supplied normalized-motion
clause from the corrected Simon compact alternative.  It does not prove the
positive-solo clause or the full finite-orbit alternative.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Actual rational support-local rows with positive absorption and
arbitrarily small strict normalized successor motion. -/
def HasArbitrarilySmallQuittingNormalizedMotionRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ upper : ℝ, 0 < upper →
    ∃ (error : ℝ) (tail : Payoff ι) (root : ι → PMF Bool),
      0 < error ∧ error < upper ∧
        QuittingSimonRationalPayoffAt reward error tail ∧
        IsQuittingRootSupportApproxNash reward tail error root ∧
        0 < quittingRootAbsorptionMass root ∧
        ∀ who,
          |quittingRootSuccessorPayoff reward tail root who - tail who| <
            error * quittingRootAbsorptionMass root

/-- Failure of the instant branch supplies one positive scale at which no
rational support-local row has a sure quitter. -/
theorem exists_pos_noSure_support_scale_of_not_instant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hinstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward) :
    ∃ scale : ℝ, 0 < scale ∧
      SuppliedQuittingSimonNoSureQuitterAt reward scale := by
  classical
  by_contra hscale
  apply hinstant
  intro ε hε
  have hquarter : 0 < ε / 4 := by linarith
  have hnot : ¬SuppliedQuittingSimonNoSureQuitterAt reward (ε / 4) := by
    intro hs
    exact hscale ⟨ε / 4, hquarter, hs⟩
  simp only [SuppliedQuittingSimonNoSureQuitterAt, not_forall, not_not] at hnot
  obtain ⟨tail, root, hrational, hsupport, hsure⟩ := hnot
  obtain ⟨quitter, hquitter⟩ := hsure
  obtain ⟨punishRow, hpunish, hnash⟩ :=
    exists_oneStagePunishedProfile_of_rational_support_sureQuitter
      (η := ε / 4) (δ := ε / 4) reward tail root quitter hquarter.le
      hquarter hrational hsupport hquitter
  refine ⟨quitter, root, punishRow, hquitter, ?_, ?_⟩
  · exact hpunish.trans (by linarith)
  · exact hnash.mono (by linarith)

omit [DecidableEq ι] in
/-- The stationary conditional payoff linearizes the successor displacement
by the one-stage absorption mass. -/
theorem quittingRootSuccessorPayoff_sub_tail_eq_absorption_mul_stationary_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    quittingRootSuccessorPayoff reward tail root who - tail who =
      quittingRootAbsorptionMass root *
        (quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who - tail who) := by
  have hcontinue : quittingStationaryContinueMass root < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  have hstationary :=
    quittingTerminalPayoff_stationary_eq_absorbingContribution_div
      reward root who hcontinue
  rw [quittingRootSuccessorPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  unfold quittingRootAbsorptionMass
  rw [hstationary]
  have hne : 1 - quittingStationaryContinueMass root ≠ 0 := by
    linarith
  field_simp [hne]
  ring

omit [DecidableEq ι] in
/-- Strict normalized motion puts the stationary conditional payoff within
the displayed error, coordinate by coordinate. -/
theorem abs_stationaryPayoff_sub_tail_lt_of_normalizedMotion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {error : ℝ} (habsorption : 0 < quittingRootAbsorptionMass root)
    (hmotion :
      |quittingRootSuccessorPayoff reward tail root who - tail who| <
        error * quittingRootAbsorptionMass root) :
    |quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who - tail who| < error := by
  rw [quittingRootSuccessorPayoff_sub_tail_eq_absorption_mul_stationary_sub
    reward tail root who habsorption, abs_mul,
    abs_of_pos habsorption] at hmotion
  nlinarith

/-- A stationary pure quit-time value, measured from a fixed point of its
affine recursion, has the exact finite geometric ledger used below. -/
theorem quittingStationaryPureTimeValue_sub_eq_pow_mul_sub_sum
    (quitValue continueReward continueMass fixed quitProbability gap : ℝ)
    (hquit : quitValue - fixed = (1 - quitProbability) * gap)
    (hcontinue : continueReward + continueMass * fixed - fixed =
      -quitProbability * gap) :
    ∀ steps : ℕ,
      quittingStationaryPureTimeValue quitValue continueReward continueMass
          steps - fixed =
        continueMass ^ steps * (1 - quitProbability) * gap -
          quitProbability * gap *
            ∑ time ∈ Finset.range steps, continueMass ^ time := by
  intro steps
  induction steps with
  | zero => simpa [quittingStationaryPureTimeValue] using hquit
  | succ steps ih =>
      rw [quittingStationaryPureTimeValue, geom_sum_succ, pow_succ]
      have hvalue :
          quittingStationaryPureTimeValue quitValue continueReward
              continueMass steps =
            fixed +
              (continueMass ^ steps * (1 - quitProbability) * gap -
                quitProbability * gap *
                  ∑ time ∈ Finset.range steps, continueMass ^ time) := by
        linarith
      rw [hvalue]
      linear_combination hcontinue

/-- The geometric exposure paid by a hazard no larger than the missing
opponent mass is at most one. -/
theorem quitProbability_mul_geomSum_le_one
    {quitProbability continueMass : ℝ}
    (hcontinue0 : 0 ≤ continueMass)
    (hdominated : quitProbability ≤ 1 - continueMass) (steps : ℕ) :
    quitProbability *
        (∑ time ∈ Finset.range steps, continueMass ^ time) ≤ 1 := by
  have hsum0 : 0 ≤ ∑ time ∈ Finset.range steps, continueMass ^ time := by
    positivity
  have hmul := mul_le_mul_of_nonneg_right hdominated hsum0
  have hgeom : (1 - continueMass) *
      (∑ time ∈ Finset.range steps, continueMass ^ time) =
        1 - continueMass ^ steps := by
    have h := geom_sum_mul continueMass steps
    calc
      _ = -((∑ time ∈ Finset.range steps, continueMass ^ time) *
          (continueMass - 1)) := by ring
      _ = -(continueMass ^ steps - 1) := by rw [h]
      _ = _ := by ring
  rw [hgeom] at hmul
  have hpow0 : 0 ≤ continueMass ^ steps := pow_nonneg hcontinue0 steps
  linarith

/-- Changing the continuation from `tail` to the absorbing stationary payoff
changes the endpoint difference only through the opponent-Continue mass. -/
theorem quittingRootEndpointDifference_stationary_sub_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootEndpointDifference reward
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player) root who -
        quittingRootEndpointDifference reward tail root who =
      -quittingStationaryFixedOpponentsContinueMass root who *
        (quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who - tail who) := by
  unfold quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward (fun _ => root) who _ 0,
    quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward (fun _ => root) who _ 0,
    quittingRootContinuePayoff_eq_fixedOpponents
      reward (fun _ => root) who _ 0,
    quittingRootContinuePayoff_eq_fixedOpponents
      reward (fun _ => root) who _ 0]
  unfold quittingStationaryFixedOpponentsContinueMass
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- Excluding a sure quitter makes every displayed Quit probability strictly
less than one. -/
theorem quitProbability_lt_one_of_noSureQuitter
    (root : ι → PMF Bool) (hnoSure : ¬QuittingRootHasSureQuitter root)
    (who : ι) :
    (root who true).toReal < 1 := by
  have hle : (root who true).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one,
      ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by simp)]
    exact PMF.coe_le_one _ _
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hfalse : (root who false).toReal = 0 := by linarith
  apply hnoSure
  exact ⟨who, (pmf_eq_pure_true_iff_apply_false_eq_zero (root who)).mpr
    ((ENNReal.toReal_eq_zero_iff (root who false)).mp hfalse |>.resolve_right
      (PMF.apply_ne_top _ _))⟩

/-- The stationary conditional endpoint gap inherits both support-local
bounds, at the cost of the normalized-motion displacement. -/
theorem stationaryEndpointDifference_bounds_of_normalizedMotion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {error distance : ℝ}
    (hdistance :
      |quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who - tail who| < distance)
    (hsupport : IsQuittingRootSupportApproxNash reward tail error root)
    (hcontinue : 0 < (root who false).toReal) :
    quittingRootEndpointDifference reward
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) player) root who <
      error + distance ∧
      (0 < (root who true).toReal →
        -quittingRootEndpointDifference reward
            (fun player => quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) player) root who <
          error + distance) := by
  have hmass0 : 0 ≤ quittingStationaryFixedOpponentsContinueMass root who :=
    quittingStationaryFixedOpponentsContinueMass_nonneg root who
  have hmass1 : quittingStationaryFixedOpponentsContinueMass root who ≤ 1 :=
    quittingStationaryFixedOpponentsContinueMass_le_one root who
  have hshift :
      quittingRootEndpointDifference reward
            (fun player => quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) player) root who -
          quittingRootEndpointDifference reward tail root who =
        -quittingStationaryFixedOpponentsContinueMass root who *
          (quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who - tail who) :=
    quittingRootEndpointDifference_stationary_sub_tail reward tail root who
  have habsUpper := (abs_lt.mp hdistance).2
  have habsLower := (abs_lt.mp hdistance).1
  constructor
  · have hlocal := (hsupport who).2 hcontinue
    nlinarith [mul_nonneg hmass0 (sub_nonneg.mpr hmass1)]
  · intro hquit
    have hlocal := (hsupport who).1 hquit
    nlinarith [mul_nonneg hmass0 (sub_nonneg.mpr hmass1)]

/-- Exact pure-time ledger for one player around the absorbing stationary
payoff of the repeated row. -/
theorem quittingStationaryPureTimeValue_sub_stationaryPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (steps : ℕ) :
    quittingStationaryPureTimeValue
          (quittingStationaryFixedOpponentsQuitValue reward root who)
          (quittingStationaryFixedOpponentsContinueReward reward root who)
          (quittingStationaryFixedOpponentsContinueMass root who) steps -
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who =
      quittingStationaryFixedOpponentsContinueMass root who ^ steps *
          (1 - (root who true).toReal) *
            quittingRootEndpointDifference reward
              (fun player => quittingTerminalPayoff reward
                (quittingStationaryProfile reward root) player) root who -
        (root who true).toReal *
            quittingRootEndpointDifference reward
              (fun player => quittingTerminalPayoff reward
                (quittingStationaryProfile reward root) player) root who *
          ∑ time ∈ Finset.range steps,
            quittingStationaryFixedOpponentsContinueMass root who ^ time := by
  let stationary : Payoff ι := fun player =>
    quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) player
  let gap := quittingRootEndpointDifference reward stationary root who
  have hquit := quittingRootQuitPayoff_sub_successorPayoff
    reward stationary root who
  have hcontinue := quittingRootContinuePayoff_sub_successorPayoff
    reward stationary root who
  have hfixed : quittingRootSuccessorPayoff reward stationary root who =
      stationary who := by
    unfold quittingRootSuccessorPayoff
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
    dsimp only [stationary]
    exact (quittingTerminalPayoff_stationary_affine reward root who).symm
  rw [hfixed] at hquit hcontinue
  rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward (fun _ => root) who stationary 0] at hquit
  rw [quittingRootContinuePayoff_eq_fixedOpponents
      reward (fun _ => root) who stationary 0] at hcontinue
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hfalse : (root who false).toReal = 1 - (root who true).toReal := by
    linarith
  rw [hfalse] at hquit
  simpa only [quittingStationaryFixedOpponentsQuitValue,
    quittingStationaryFixedOpponentsContinueReward,
    quittingStationaryFixedOpponentsContinueMass, stationary, gap] using
      (quittingStationaryPureTimeValue_sub_eq_pow_mul_sub_sum
        _ _ _ _ _ gap hquit hcontinue steps)

/-- A nonselected player's finite pure quit times gain less than the inherited
support error when its hazard is bounded by missing opponent mass. -/
theorem quittingStationaryPureTimeValue_sub_lt_of_localGap
    {quitValue continueReward continueMass fixed quitProbability gap error : ℝ}
    (hformula : ∀ steps : ℕ,
      quittingStationaryPureTimeValue quitValue continueReward continueMass
          steps - fixed =
        continueMass ^ steps * (1 - quitProbability) * gap -
          quitProbability * gap *
            ∑ time ∈ Finset.range steps, continueMass ^ time)
    (hquit0 : 0 ≤ quitProbability) (hquit1 : quitProbability ≤ 1)
    (hmass0 : 0 ≤ continueMass) (hmass1 : continueMass ≤ 1)
    (hdominated : quitProbability ≤ 1 - continueMass)
    (hgapUpper : gap < error)
    (hgapLower : 0 < quitProbability → -gap < error)
    (herror : 0 < error) (steps : ℕ) :
    quittingStationaryPureTimeValue quitValue continueReward continueMass
        steps - fixed < error := by
  rw [hformula steps]
  have hpow0 : 0 ≤ continueMass ^ steps := pow_nonneg hmass0 steps
  have hpow1 : continueMass ^ steps ≤ 1 := pow_le_one₀ hmass0 hmass1
  have hsum0 : 0 ≤ ∑ time ∈ Finset.range steps, continueMass ^ time := by
    positivity
  by_cases hgap : 0 ≤ gap
  · have hfirst :
        continueMass ^ steps * (1 - quitProbability) * gap ≤ gap := by
      have hremain : 0 ≤ 1 - quitProbability := sub_nonneg.mpr hquit1
      nlinarith [mul_nonneg hpow0 hremain,
        mul_nonneg (sub_nonneg.mpr hpow1) hremain]
    have hsecond : 0 ≤ quitProbability * gap *
        (∑ time ∈ Finset.range steps, continueMass ^ time) := by positivity
    linarith
  · have hgapNeg : gap < 0 := lt_of_not_ge hgap
    have hfirst :
        continueMass ^ steps * (1 - quitProbability) * gap ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hpow0 (sub_nonneg.mpr hquit1)) hgapNeg.le
    by_cases hquit : quitProbability = 0
    · rw [hquit]
      simp only [zero_mul, sub_zero]
      nlinarith
    · have hquitPos : 0 < quitProbability := lt_of_le_of_ne hquit0 (Ne.symm hquit)
      have hgeom := quitProbability_mul_geomSum_le_one hmass0
        hdominated steps
      have hlower := hgapLower hquitPos
      nlinarith

/-- The same local-gap estimate includes the explicit stationary Never
alternative in the contracting case. -/
theorem quittingStationaryNeverValue_sub_lt_of_localGap
    {continueReward continueMass fixed quitProbability gap error : ℝ}
    (hbalance : continueReward + continueMass * fixed - fixed =
      -quitProbability * gap)
    (hquit0 : 0 ≤ quitProbability)
    (_hmass0 : 0 ≤ continueMass) (hmass1 : continueMass < 1)
    (hdominated : quitProbability ≤ 1 - continueMass)
    (hgapLower : 0 < quitProbability → -gap < error)
    (herror : 0 < error) :
    quittingStationaryNeverValue continueReward continueMass - fixed < error := by
  have hdenom : 0 < 1 - continueMass := sub_pos.mpr hmass1
  have hnever :
      quittingStationaryNeverValue continueReward continueMass - fixed =
        quitProbability * (-gap) / (1 - continueMass) := by
    unfold quittingStationaryNeverValue
    field_simp [hdenom.ne']
    nlinarith
  rw [hnever]
  by_cases hquit : quitProbability = 0
  · rw [hquit]
    simpa using herror
  · have hquitPos : 0 < quitProbability := lt_of_le_of_ne hquit0 (Ne.symm hquit)
    have hratio : quitProbability / (1 - continueMass) ≤ 1 := by
      exact (div_le_one hdenom).mpr hdominated
    have hratio0 : 0 ≤ quitProbability / (1 - continueMass) := by positivity
    have hlower := hgapLower hquitPos
    rw [div_eq_mul_inv]
    have heq : quitProbability * (-gap) * (1 - continueMass)⁻¹ =
        (quitProbability / (1 - continueMass)) * (-gap) := by ring
    rw [heq]
    by_cases hgap : 0 ≤ -gap
    · nlinarith [mul_nonneg (sub_nonneg.mpr hratio) hgap]
    · have hnegative :
          (quitProbability / (1 - continueMass)) * (-gap) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hratio0 (le_of_not_ge hgap)
      exact hnegative.trans_lt herror

/-- Over a selected player's finite exposure window, the local error is paid
at most once per prescribed Quit hazard. -/
theorem quittingStationaryPureTimeValue_sub_lt_mul_exposure
    {quitValue continueReward continueMass fixed quitProbability gap error : ℝ}
    (hformula : ∀ steps : ℕ,
      quittingStationaryPureTimeValue quitValue continueReward continueMass
          steps - fixed =
        continueMass ^ steps * (1 - quitProbability) * gap -
          quitProbability * gap *
            ∑ time ∈ Finset.range steps, continueMass ^ time)
    (hquit0 : 0 ≤ quitProbability) (hquit1 : quitProbability ≤ 1)
    (hmass0 : 0 ≤ continueMass) (hmass1 : continueMass ≤ 1)
    (hgapUpper : gap < error)
    (hgapLower : 0 < quitProbability → -gap < error)
    (herror : 0 < error) {steps window : ℕ} (hsteps : steps < window)
    (hexposure : 1 ≤ (window : ℝ) * quitProbability) :
    quittingStationaryPureTimeValue quitValue continueReward continueMass
        steps - fixed < (window : ℝ) * quitProbability * error := by
  rw [hformula steps]
  have hpow0 : 0 ≤ continueMass ^ steps := pow_nonneg hmass0 steps
  have hpow1 : continueMass ^ steps ≤ 1 := pow_le_one₀ hmass0 hmass1
  have hsum0 : 0 ≤ ∑ time ∈ Finset.range steps, continueMass ^ time := by
    positivity
  have hsumLe :
      (∑ time ∈ Finset.range steps, continueMass ^ time) ≤ (steps : ℝ) := by
    calc
      _ ≤ ∑ _time ∈ Finset.range steps, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro time _
        exact pow_le_one₀ hmass0 hmass1
      _ = (steps : ℝ) := by simp
  have hwindow0 : 0 ≤ (window : ℝ) := Nat.cast_nonneg window
  have hquitExposure : 0 < quitProbability := by
    by_contra hnot
    have : quitProbability = 0 := le_antisymm (le_of_not_gt hnot) hquit0
    rw [this, mul_zero] at hexposure
    norm_num at hexposure
  by_cases hgap : 0 ≤ gap
  · have hfirst :
        continueMass ^ steps * (1 - quitProbability) * gap ≤ gap := by
      have hremain : 0 ≤ 1 - quitProbability := sub_nonneg.mpr hquit1
      nlinarith [mul_nonneg hpow0 hremain,
        mul_nonneg (sub_nonneg.mpr hpow1) hremain]
    have hsecond : 0 ≤ quitProbability * gap *
        (∑ time ∈ Finset.range steps, continueMass ^ time) := by positivity
    have htarget : error ≤ (window : ℝ) * quitProbability * error := by
      nlinarith
    calc
      continueMass ^ steps * (1 - quitProbability) * gap -
          quitProbability * gap *
            (∑ time ∈ Finset.range steps, continueMass ^ time) ≤
          continueMass ^ steps * (1 - quitProbability) * gap :=
        sub_le_self _ hsecond
      _ ≤ gap := hfirst
      _ < error := hgapUpper
      _ ≤ (window : ℝ) * quitProbability * error := htarget
  · have hgapNeg : gap < 0 := lt_of_not_ge hgap
    have hfirst :
        continueMass ^ steps * (1 - quitProbability) * gap ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hpow0 (sub_nonneg.mpr hquit1)) hgapNeg.le
    have hstepsCast : (steps : ℝ) < window := by exact_mod_cast hsteps
    have hlower := hgapLower hquitExposure
    have hpositive : 0 < quitProbability * (-gap) := mul_pos hquitExposure (by linarith)
    nlinarith

/-! ## Finite stationary-prefix stopping bounds -/

/-- Before the live boundary, a deterministic finite quit time against a
constant root is the corresponding stationary pure-time value. -/
theorem quittingFiniteTerminalPureTimeValue_const_castSucc
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (terminalValue : ℝ) :
    ∀ (start fuel : ℕ) (choice : Fin fuel),
      quittingFiniteTerminalPureTimeValue reward (fun _ => root) who
          terminalValue start fuel choice.castSucc =
        quittingStationaryPureTimeValue
          (quittingStationaryFixedOpponentsQuitValue reward root who)
          (quittingStationaryFixedOpponentsContinueReward reward root who)
          (quittingStationaryFixedOpponentsContinueMass root who) choice.val := by
  intro start fuel
  induction fuel generalizing start with
  | zero => exact fun choice => Fin.elim0 choice
  | succ fuel ih =>
      intro choice
      refine Fin.cases ?_ (fun later => ?_) choice
      · rfl
      · rw [quittingFiniteTerminalPureTimeValue]
        simp only [Fin.castSucc_succ, Fin.cases_succ]
        rw [quittingStationaryPureTimeValue.eq_def, ih (start + 1) later]
        rfl

/-- Continuing through a constant prefix and receiving its stationary payoff
at the boundary has the exact finite geometric ledger. -/
theorem quittingFiniteTerminalPureTimeValue_const_last_sub_stationary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ∀ (start fuel : ℕ),
    quittingFiniteTerminalPureTimeValue reward (fun _ => root) who
          (quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who)
          start fuel (Fin.last fuel) -
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who =
      -(root who true).toReal *
        quittingRootEndpointDifference reward
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player) root who *
        ∑ time ∈ Finset.range fuel,
          quittingStationaryFixedOpponentsContinueMass root who ^ time := by
  intro start fuel
  let fixed := quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) who
  let gap := quittingRootEndpointDifference reward
    (fun player => quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) player) root who
  have hfixed : quittingRootSuccessorPayoff reward
      (fun player => quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) root who = fixed := by
    unfold quittingRootSuccessorPayoff
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
    dsimp only [fixed]
    exact (quittingTerminalPayoff_stationary_affine reward root who).symm
  have hcontinueSource := quittingRootContinuePayoff_sub_successorPayoff
    reward
      (fun player => quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) root who
  rw [hfixed, quittingRootContinuePayoff_eq_fixedOpponents
    reward (fun _ => root) who
      (fun player => quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) 0] at hcontinueSource
  have hcontinue :
      quittingStationaryFixedOpponentsContinueReward reward root who +
          quittingStationaryFixedOpponentsContinueMass root who * fixed - fixed =
        -(root who true).toReal * gap := by
    simpa only [quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass, fixed, gap] using
        hcontinueSource
  induction fuel generalizing start with
  | zero => simp [quittingFiniteTerminalPureTimeValue]
  | succ fuel ih =>
      rw [show Fin.last (fuel + 1) = (Fin.last fuel).succ by rfl,
        quittingFiniteTerminalPureTimeValue, Fin.cases_succ, geom_sum_succ]
      have hrewrite :
          quittingFiniteTerminalPureTimeValue reward (fun _ => root) who fixed
              (start + 1) fuel (Fin.last fuel) =
            fixed - (root who true).toReal * gap *
              ∑ time ∈ Finset.range fuel,
                quittingStationaryFixedOpponentsContinueMass root who ^ time := by
        have := ih (start + 1)
        dsimp only [fixed, gap] at this ⊢
        linarith
      rw [hrewrite]
      change quittingStationaryFixedOpponentsContinueReward reward root who +
          quittingStationaryFixedOpponentsContinueMass root who *
            (fixed - (root who true).toReal * gap *
              ∑ time ∈ Finset.range fuel,
                quittingStationaryFixedOpponentsContinueMass root who ^ time) -
          fixed = _
      linear_combination hcontinue

/-- The finite stopping problem of a nonselected player inherits the local
support error when the marked player's hazard lies among its opponents. -/
theorem quittingFiniteTerminalBestResponseValue_const_lt_of_localGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {error : ℝ}
    (hquit0 : 0 ≤ (root who true).toReal)
    (hquit1 : (root who true).toReal ≤ 1)
    (hmass0 : 0 ≤ quittingStationaryFixedOpponentsContinueMass root who)
    (hmass1 : quittingStationaryFixedOpponentsContinueMass root who ≤ 1)
    (hdominated : (root who true).toReal ≤
      1 - quittingStationaryFixedOpponentsContinueMass root who)
    (hgapUpper : quittingRootEndpointDifference reward
      (fun player => quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) root who < error)
    (hgapLower : 0 < (root who true).toReal →
      -quittingRootEndpointDifference reward
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) player) root who < error)
    (herror : 0 < error) (fuel : ℕ) :
    quittingFiniteTerminalBestResponseValue reward (fun _ => root) who
        (quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who) 0 fuel <
      quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who + error := by
  obtain ⟨choice, hchoice⟩ :=
    exists_quittingFiniteTerminalPureTimeValue_eq_bestResponse
      reward (fun _ => root) who
        (quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who) 0 fuel
  rw [← hchoice]
  by_cases hlast : choice = Fin.last fuel
  · subst choice
    have hlastEq :=
      quittingFiniteTerminalPureTimeValue_const_last_sub_stationary
        reward root who 0 fuel
    by_cases hquit : (root who true).toReal = 0
    · have hgain :
          -(root who true).toReal *
              quittingRootEndpointDifference reward
                (fun player => quittingTerminalPayoff reward
                  (quittingStationaryProfile reward root) player) root who *
              (∑ time ∈ Finset.range fuel,
                quittingStationaryFixedOpponentsContinueMass root who ^ time) = 0 := by
          rw [hquit]
          ring
      linarith
    · have hquitPos : 0 < (root who true).toReal :=
        lt_of_le_of_ne hquit0 (Ne.symm hquit)
      have hgeom := quitProbability_mul_geomSum_le_one hmass0 hdominated fuel
      have hlower := hgapLower hquitPos
      have hsum0 : 0 ≤ ∑ time ∈ Finset.range fuel,
          quittingStationaryFixedOpponentsContinueMass root who ^ time := by
        positivity
      let ratio := (root who true).toReal *
        (∑ time ∈ Finset.range fuel,
          quittingStationaryFixedOpponentsContinueMass root who ^ time)
      have hratio0 : 0 ≤ ratio := mul_nonneg hquit0 hsum0
      have hratio1 : ratio ≤ 1 := hgeom
      have hgain :
          -(root who true).toReal *
              quittingRootEndpointDifference reward
                (fun player => quittingTerminalPayoff reward
                  (quittingStationaryProfile reward root) player) root who *
              (∑ time ∈ Finset.range fuel,
                quittingStationaryFixedOpponentsContinueMass root who ^ time) <
            error := by
        rw [show -(root who true).toReal *
              quittingRootEndpointDifference reward
                (fun player => quittingTerminalPayoff reward
                  (quittingStationaryProfile reward root) player) root who *
              (∑ time ∈ Finset.range fuel,
                quittingStationaryFixedOpponentsContinueMass root who ^ time) =
            ratio *
              (-quittingRootEndpointDifference reward
                (fun player => quittingTerminalPayoff reward
                  (quittingStationaryProfile reward root) player) root who) by
              simp only [ratio]
              ring]
        by_cases hgap : 0 ≤ -quittingRootEndpointDifference reward
            (fun player => quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) player) root who
        · exact (mul_le_of_le_one_left hgap hratio1).trans_lt hlower
        · have hnonpos := mul_nonpos_of_nonneg_of_nonpos hratio0
            (le_of_not_ge hgap)
          exact hnonpos.trans_lt herror
      linarith
  · obtain ⟨earlier, hearlier⟩ := choice.eq_castSucc_of_ne_last hlast
    subst choice
    rw [quittingFiniteTerminalPureTimeValue_const_castSucc]
    have hpure := quittingStationaryPureTimeValue_sub_lt_of_localGap
      (quittingStationaryPureTimeValue_sub_stationaryPayoff reward root who)
      hquit0 hquit1 hmass0 hmass1 hdominated hgapUpper hgapLower herror
      earlier.val
    linarith

/-- Over the marked exposure window, its finite stopping value is bounded by
the window length times its prescribed Quit hazard and the local error. -/
theorem quittingFiniteTerminalBestResponseValue_const_lt_mul_exposure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {error : ℝ}
    (hquit0 : 0 ≤ (root who true).toReal)
    (hquit1 : (root who true).toReal ≤ 1)
    (hmass0 : 0 ≤ quittingStationaryFixedOpponentsContinueMass root who)
    (hmass1 : quittingStationaryFixedOpponentsContinueMass root who ≤ 1)
    (hgapUpper : quittingRootEndpointDifference reward
      (fun player => quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) root who < error)
    (hgapLower : 0 < (root who true).toReal →
      -quittingRootEndpointDifference reward
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) player) root who < error)
    (herror : 0 < error) {fuel window : ℕ} (hfuel : fuel ≤ window)
    (hexposure : 1 ≤ (window : ℝ) * (root who true).toReal) :
    quittingFiniteTerminalBestResponseValue reward (fun _ => root) who
        (quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who) 0 fuel <
      quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who +
        (window : ℝ) * (root who true).toReal * error := by
  obtain ⟨choice, hchoice⟩ :=
    exists_quittingFiniteTerminalPureTimeValue_eq_bestResponse
      reward (fun _ => root) who
        (quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who) 0 fuel
  rw [← hchoice]
  by_cases hlast : choice = Fin.last fuel
  · subst choice
    have hlastEq :=
      quittingFiniteTerminalPureTimeValue_const_last_sub_stationary
        reward root who 0 fuel
    have hsumLe :
        (∑ time ∈ Finset.range fuel,
          quittingStationaryFixedOpponentsContinueMass root who ^ time) ≤
            (fuel : ℝ) := by
      calc
        _ ≤ ∑ _time ∈ Finset.range fuel, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro time _
          exact pow_le_one₀ hmass0 hmass1
        _ = (fuel : ℝ) := by simp
    have hfuelCast : (fuel : ℝ) ≤ window := by exact_mod_cast hfuel
    by_cases hgap : 0 ≤ quittingRootEndpointDifference reward
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) player) root who
    · have hnonpos :
          -(root who true).toReal *
              quittingRootEndpointDifference reward
                (fun player => quittingTerminalPayoff reward
                  (quittingStationaryProfile reward root) player) root who *
              (∑ time ∈ Finset.range fuel,
                quittingStationaryFixedOpponentsContinueMass root who ^ time) ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hquit0) hgap)
            (by positivity)
      have htarget : 0 < (window : ℝ) * (root who true).toReal * error := by
        nlinarith
      linarith
    · have hgapNeg := lt_of_not_ge hgap
      have hquitPos : 0 < (root who true).toReal := by nlinarith
      have hlower := hgapLower hquitPos
      have hsum0 : 0 ≤ ∑ time ∈ Finset.range fuel,
          quittingStationaryFixedOpponentsContinueMass root who ^ time := by
        positivity
      have hwindowPos : 0 < (window : ℝ) := by
        have hwindowNe : window ≠ 0 := by
          intro hzero
          subst window
          norm_num at hexposure
        exact_mod_cast Nat.pos_of_ne_zero hwindowNe
      have hsumWindow :
          (∑ time ∈ Finset.range fuel,
            quittingStationaryFixedOpponentsContinueMass root who ^ time) ≤
              (window : ℝ) := hsumLe.trans hfuelCast
      have hscaleLe := mul_le_mul_of_nonneg_left hsumWindow
        (mul_nonneg hquit0 (by linarith : 0 ≤
          -quittingRootEndpointDifference reward
            (fun player => quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) player) root who))
      have hstrict := mul_lt_mul_of_pos_left hlower hquitPos
      have hstrictWindow := mul_lt_mul_of_pos_right hstrict hwindowPos
      have hgain :
          -(root who true).toReal *
              quittingRootEndpointDifference reward
                (fun player => quittingTerminalPayoff reward
                  (quittingStationaryProfile reward root) player) root who *
              (∑ time ∈ Finset.range fuel,
                quittingStationaryFixedOpponentsContinueMass root who ^ time) <
            (window : ℝ) * (root who true).toReal * error := by
        calc
          _ = ((root who true).toReal *
                (-quittingRootEndpointDifference reward
                  (fun player => quittingTerminalPayoff reward
                    (quittingStationaryProfile reward root) player) root who)) *
              (∑ time ∈ Finset.range fuel,
                quittingStationaryFixedOpponentsContinueMass root who ^ time) := by ring
          _ ≤ ((root who true).toReal *
                (-quittingRootEndpointDifference reward
                  (fun player => quittingTerminalPayoff reward
                    (quittingStationaryProfile reward root) player) root who)) *
              (window : ℝ) := hscaleLe
          _ < ((root who true).toReal * error) * (window : ℝ) := hstrictWindow
          _ = _ := by ring
      linarith
  · obtain ⟨earlier, hearlier⟩ := choice.eq_castSucc_of_ne_last hlast
    subst choice
    rw [quittingFiniteTerminalPureTimeValue_const_castSucc]
    have hearlierWindow : earlier.val < window := lt_of_lt_of_le earlier.isLt hfuel
    have hpure := quittingStationaryPureTimeValue_sub_lt_mul_exposure
      (quittingStationaryPureTimeValue_sub_stationaryPayoff reward root who)
      hquit0 hquit1 hmass0 hmass1 hgapUpper hgapLower herror
      hearlierWindow hexposure
    linarith

/-! ## Exposure-window selection -/

/-- The ceiling of `scale / hazard` gives a window with controlled total
exposure and the standard exponential survival envelope. -/
theorem exists_exposureWindow
    {hazard scale : ℝ} (hhazard : 0 < hazard) (hhazard1 : hazard ≤ 1)
    (hscale : 2 ≤ scale) :
    ∃ window : ℕ,
      1 < window ∧
        scale ≤ (window : ℝ) * hazard ∧
        (window : ℝ) * hazard < scale + 1 ∧
        (1 - hazard) ^ window ≤ Real.exp (-scale) := by
  let window := ⌈scale / hazard⌉₊
  have hratio0 : 0 ≤ scale / hazard := by positivity
  have hlower : scale / hazard ≤ (window : ℝ) := Nat.le_ceil _
  have hupper : (window : ℝ) < scale / hazard + 1 :=
    Nat.ceil_lt_add_one hratio0
  have hexposureLower : scale ≤ (window : ℝ) * hazard := by
    apply (div_le_iff₀ hhazard).mp at hlower
    simpa [mul_comm] using hlower
  have hexposureUpper : (window : ℝ) * hazard < scale + 1 := by
    have := mul_lt_mul_of_pos_right hupper hhazard
    field_simp [hhazard.ne'] at this
    linarith
  have hwindow : 1 < window := by
    have htwo : (2 : ℝ) ≤ window := by
      calc
        (2 : ℝ) ≤ scale := hscale
        _ ≤ (window : ℝ) * hazard := hexposureLower
        _ ≤ (window : ℝ) := by
          exact mul_le_of_le_one_right (Nat.cast_nonneg window) hhazard1
    exact_mod_cast htwo
  have hbase0 : 0 ≤ 1 - hazard := sub_nonneg.mpr hhazard1
  have hpow : (1 - hazard) ^ window ≤
      Real.exp (-((window : ℝ) * hazard)) := by
    have hone := Real.one_sub_le_exp_neg hazard
    have hpow' := pow_le_pow_left₀ hbase0 hone window
    calc
      (1 - hazard) ^ window ≤ Real.exp (-hazard) ^ window := hpow'
      _ = Real.exp ((window : ℝ) * (-hazard)) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp (-((window : ℝ) * hazard)) := by
        congr 1
        ring
  have hexp : Real.exp (-((window : ℝ) * hazard)) ≤ Real.exp (-scale) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hexposureLower)
  exact ⟨window, hwindow, hexposureLower, hexposureUpper, hpow.trans hexp⟩

/-- A real exposure scale can make the exponential survival envelope smaller
than any prescribed positive target. -/
theorem exists_scale_ge_two_exp_neg_lt {target : ℝ} (htarget : 0 < target) :
    ∃ scale : ℝ, 2 ≤ scale ∧ Real.exp (-scale) < target := by
  let scale := max 2 (1 - Real.log target)
  have hscale : 2 ≤ scale := le_max_left _ _
  have hlog : 1 - Real.log target ≤ scale := le_max_right _ _
  have hlt : -scale < Real.log target := by linarith
  have hexp := Real.exp_lt_exp.mpr hlt
  rw [Real.exp_log htarget] at hexp
  exact ⟨scale, hscale, hexp⟩

/-! ## The stationary-prefix producer -/

/-- One rational support-local row with sufficiently small normalized motion
produces a stationary-prefix equilibrium at the displayed accuracy. -/
theorem exists_stationaryPrefix_punishment_nash_of_normalizedMotionRow
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {error scale equilibriumError punishmentError : ℝ}
    (herror : 0 < error) (hscale : 2 ≤ scale)
    (hpunishmentError : 0 < punishmentError)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (hrational : QuittingSimonRationalPayoffAt reward error tail)
    (hsupport : IsQuittingRootSupportApproxNash reward tail error root)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hmotion : ∀ who,
      |quittingRootSuccessorPayoff reward tail root who - tail who| <
        error * quittingRootAbsorptionMass root)
    (hnoSure : ¬QuittingRootHasSureQuitter root)
    (hsmall : 2 * error * (scale + 3) +
        4 * quittingRewardBound reward * Real.exp (-scale) < equilibriumError) :
    ∃ (horizon : ℕ) (who : ι) (punishment : ℕ → ι → PMF Bool),
      1 < horizon ∧
      IsQuittingRootSequencePunishmentWithin reward who punishmentError
        punishment ∧
      IsεQuittingRootSequenceNash reward
        (equilibriumError + punishmentError)
        (quittingStationaryPrefixThenRoots root horizon punishment) := by
  classical
  let M := quittingRewardBound reward
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hreward : ∀ terminal player, |reward terminal player| ≤ M :=
    abs_reward_le_quittingRewardBound reward
  obtain ⟨positive, hpositive⟩ :=
    exists_quitProbability_pos_of_absorptionMass_pos root habsorption
  obtain ⟨who, _hmem, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset ι) (fun player => (root player true).toReal)
      Finset.univ_nonempty
  have hwhoPos : 0 < (root who true).toReal := by
    exact hpositive.trans_le (hmax positive (Finset.mem_univ positive))
  have hwhoLe : (root who true).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (root who) true)
  obtain ⟨window, hwindow, hexposureLower, hexposureUpper, hdecay⟩ :=
    exists_exposureWindow hwhoPos hwhoLe hscale
  let horizon := window
  let switch := horizon + 1
  have hswitchExposure : 1 ≤ (switch : ℝ) * (root who true).toReal := by
    have hwindowSwitch : (window : ℝ) ≤ switch := by
      simp [switch, horizon]
    have := mul_le_mul_of_nonneg_right hwindowSwitch hwhoPos.le
    exact (le_trans (by linarith : 1 ≤ scale) hexposureLower).trans this
  have hswitchUpper :
      (switch : ℝ) * (root who true).toReal < scale + 2 := by
    have hcast : (switch : ℝ) = window + 1 := by simp [switch, horizon]
    rw [hcast, add_mul]
    nlinarith

  have hcontinueWho : (root who false).toReal = 1 - (root who true).toReal := by
    linarith [quittingRoot_continueProbability_add_quitProbability root who]
  have hdecaySwitch : (root who false).toReal ^ switch ≤ Real.exp (-scale) := by
    rw [hcontinueWho]
    have hbase0 : 0 ≤ 1 - (root who true).toReal := sub_nonneg.mpr hwhoLe
    have hbase1 : 1 - (root who true).toReal ≤ 1 := by linarith
    have hpow : (1 - (root who true).toReal) ^ switch ≤
        (1 - (root who true).toReal) ^ window := by
      apply pow_le_pow_of_le_one hbase0 hbase1
      simp [switch, horizon]
    exact hpow.trans hdecay
  let stationary : Payoff ι := fun player =>
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) player
  have hstationaryClose : ∀ player, |stationary player - tail player| < error := by
    intro player
    exact abs_stationaryPayoff_sub_tail_lt_of_normalizedMotion
      reward tail root player habsorption (hmotion player)
  have hcontinuePos : ∀ player, 0 < (root player false).toReal := by
    intro player
    have hquit := quitProbability_lt_one_of_noSureQuitter root hnoSure player
    linarith [quittingRoot_continueProbability_add_quitProbability root player]
  have hgap : ∀ player,
      quittingRootEndpointDifference reward stationary root player < 2 * error ∧
      (0 < (root player true).toReal →
        -quittingRootEndpointDifference reward stationary root player < 2 * error) := by
    intro player
    have hbounds := stationaryEndpointDifference_bounds_of_normalizedMotion
      reward tail root player (hstationaryClose player) hsupport
        (hcontinuePos player)
    dsimp only [stationary]
    constructor
    · linarith [hbounds.1]
    · intro hquit
      linarith [hbounds.2 hquit]
  obtain ⟨punishmentRoot, hpunishmentRoot⟩ :=
    exists_stationaryRoot_cap_lt_punishmentValue_add
      reward who hpunishmentError
  let punishment : ℕ → ι → PMF Bool := fun _ => punishmentRoot
  have hpunish : IsQuittingRootSequencePunishmentWithin reward who
      punishmentError punishment := by
    intro hazard
    exact (quittingRootSequenceHazardTerminalValue_const_le_cap
      reward punishmentRoot who hazard).trans hpunishmentRoot.le
  let plan : ℕ → ι → PMF Bool := fun _ => root
  let spliced := quittingPhaseSwitchRoots plan punishment switch
  have hspliced :
      quittingStationaryPrefixThenRoots root horizon punishment = spliced := by
    rw [quittingStationaryPrefixThenRoots_eq_phaseSwitch]
  refine ⟨horizon, who, punishment, hwindow, hpunish, ?_⟩
  rw [hspliced]
  intro player hazard
  have hquit0 : 0 ≤ (root player true).toReal := ENNReal.toReal_nonneg
  have hquit1 : (root player true).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (root player) true)
  have hmass0 : 0 ≤ quittingStationaryFixedOpponentsContinueMass root player :=
    quittingStationaryFixedOpponentsContinueMass_nonneg root player
  have hmass1 : quittingStationaryFixedOpponentsContinueMass root player ≤ 1 :=
    quittingStationaryFixedOpponentsContinueMass_le_one root player
  have hdecomp := quittingRootSequenceHazardTerminalValue_phaseSwitch_eq_finite
    reward plan punishment switch player hazard
  have hprescribed :=
    abs_quittingRootSequenceTerminalValue_sub_le_of_prefix_eq
      reward spliced plan player switch hreward (fun time htime =>
        quittingPhaseSwitchRoots_of_lt plan punishment htime)
  have hplanEq : quittingRootSequenceTerminalValue reward plan player 0 =
      stationary player := rfl
  rw [hplanEq] at hprescribed
  have hjoint : quittingJointSurvivalWeight plan 0 switch ≤
      (root who false).toReal ^ switch :=
    quittingJointSurvivalWeight_const_le_pow_continue root who switch
  have hprescribedLower : stationary player -
      2 * M * Real.exp (-scale) ≤
        quittingRootSequenceTerminalValue reward spliced player 0 := by
    have hscaled : 2 * M * quittingJointSurvivalWeight plan 0 switch ≤
        2 * M * Real.exp (-scale) := by
      exact mul_le_mul_of_nonneg_left (hjoint.trans hdecaySwitch)
        (mul_nonneg (by norm_num) hM)
    have hnegative := neg_le_of_abs_le hprescribed
    linarith
  by_cases hplayer : player = who
  · subst player
    have hplanBest :=
      quittingFiniteTerminalBestResponseValue_const_lt_mul_exposure
        reward root who hquit0 hquit1 hmass0 hmass1 (hgap who).1
          (hgap who).2 (by linarith : 0 < 2 * error)
          (show switch ≤ switch from le_rfl) hswitchExposure
    have htail :
        quittingRootSequenceHazardTerminalValue reward punishment who
            (fun offset => hazard (switch + offset)) 0 <
          stationary who + 2 * error + punishmentError := by
      have hcap := hpunish (fun offset => hazard (switch + offset))
      have hir := hrational who
      have hclose := (abs_lt.mp (hstationaryClose who)).1
      linarith
    let boundary := quittingRootSequenceHazardTerminalValue reward punishment who
      (fun offset => hazard (switch + offset)) 0
    have hfiniteMono := quittingFiniteTerminalHazardValue_mono_terminal
      reward plan who hazard (show boundary ≤ stationary who +
        (2 * error + punishmentError) by
          dsimp only [boundary]
          linarith) 0 switch
    have hadd := quittingFiniteTerminalHazardValue_add reward plan who hazard
      (stationary who) (2 * error + punishmentError) 0 switch
    have hsurvival1 : quittingFiniteFullSurvivalWeight plan who hazard 0 switch ≤ 1 :=
      (quittingFiniteFullSurvivalWeight_le_opponentSurvivalWeight
        plan who hazard 0 switch).trans
          (quittingOpponentSurvivalWeight_le_one plan who 0 switch)
    have hboundaryError0 : 0 ≤ 2 * error + punishmentError := by linarith
    have hdev : quittingRootSequenceHazardTerminalValue reward spliced who hazard 0 <
        stationary who + (switch : ℝ) * (root who true).toReal *
          (2 * error) + (2 * error + punishmentError) := by
      rw [hdecomp]
      have hbase := quittingFiniteTerminalHazardValue_le_bestResponse
        reward plan who hazard (stationary who) 0 switch
      rw [hadd] at hfiniteMono
      have hscaled := mul_le_mul_of_nonneg_right hsurvival1 hboundaryError0
      linarith
    have hlocal :
        (switch : ℝ) * (root who true).toReal * (2 * error) + 2 * error <
          2 * error * (scale + 3) := by
      nlinarith
    change quittingRootSequenceHazardTerminalValue reward spliced who hazard 0 ≤
      quittingRootSequenceTerminalValue reward spliced who 0 +
        (equilibriumError + punishmentError)
    have hexp0 : 0 ≤ Real.exp (-scale) := Real.exp_nonneg _
    have hdecayNonneg : 0 ≤ 2 * quittingRewardBound reward *
        Real.exp (-scale) := by positivity
    linarith
  · have hmarked : who ≠ player := Ne.symm hplayer
    have hopponent : quittingOpponentSurvivalWeight plan player 0 switch ≤
        (root who false).toReal ^ switch :=
      quittingOpponentSurvivalWeight_const_le_pow_continue
        root player who hmarked switch
    have hdominated : (root player true).toReal ≤
        1 - quittingStationaryFixedOpponentsContinueMass root player := by
      have hdeleted := quittingRootDeletedContinueMass_le_of_ne
        root (who := player) hmarked
      have hmaxPlayer := hmax player (Finset.mem_univ player)
      rw [hcontinueWho] at hdeleted
      change (root player true).toReal ≤
        1 - quittingRootDeletedContinueMass root player
      linarith
    have hplanBest :=
      quittingFiniteTerminalBestResponseValue_const_lt_of_localGap
        reward root player hquit0 hquit1 hmass0 hmass1 hdominated
          (hgap player).1 (hgap player).2 (by linarith : 0 < 2 * error) switch
    let boundary := quittingRootSequenceHazardTerminalValue reward punishment player
      (fun offset => hazard (switch + offset)) 0
    have hboundaryAbs : |boundary - stationary player| ≤ 2 * M := by
      have htailBound := abs_quittingRootSequenceTerminalValue_le
        reward (quittingRootSequenceUpdate punishment player
          (fun offset => hazard (switch + offset))) player 0 hM hreward
      have hstationaryBound := abs_quittingTerminalPayoff_le reward
        (quittingStationaryProfile reward root) player hreward
      have hboundaryBound : |boundary| ≤ M := by
        simpa only [boundary, quittingRootSequenceHazardTerminalValue] using
          htailBound
      calc
        |boundary - stationary player| ≤ |boundary| + |stationary player| :=
          abs_sub _ _
        _ ≤ M + M := add_le_add hboundaryBound hstationaryBound
        _ = 2 * M := by ring
    have hadd := quittingFiniteTerminalHazardValue_add reward plan player hazard
      (stationary player) (boundary - stationary player) 0 switch
    have hsurvival : quittingFiniteFullSurvivalWeight plan player hazard 0 switch ≤
        Real.exp (-scale) :=
      (quittingFiniteFullSurvivalWeight_le_opponentSurvivalWeight
        plan player hazard 0 switch).trans
          (hopponent.trans hdecaySwitch)
    have hsurvival0 := quittingFiniteFullSurvivalWeight_nonneg
      plan player hazard 0 switch
    have hboundaryTerm : quittingFiniteFullSurvivalWeight plan player hazard 0 switch *
        (boundary - stationary player) ≤ 2 * M * Real.exp (-scale) := by
      have hupper := (abs_le.mp hboundaryAbs).2
      have hfirst := mul_le_mul_of_nonneg_left hupper hsurvival0
      have hsecond :
          quittingFiniteFullSurvivalWeight plan player hazard 0 switch *
              (2 * M) ≤ Real.exp (-scale) * (2 * M) :=
        mul_le_mul_of_nonneg_right hsurvival (mul_nonneg (by norm_num) hM)
      calc
        _ ≤ quittingFiniteFullSurvivalWeight plan player hazard 0 switch *
            (2 * M) := hfirst
        _ ≤ Real.exp (-scale) * (2 * M) := hsecond
        _ = 2 * M * Real.exp (-scale) := by ring
    have hdev : quittingRootSequenceHazardTerminalValue reward spliced player
        hazard 0 < stationary player + 2 * error +
          2 * M * Real.exp (-scale) := by
      rw [hdecomp]
      change quittingFiniteTerminalHazardValue reward plan player hazard boundary
          0 switch < _
      have hbase := quittingFiniteTerminalHazardValue_le_bestResponse
        reward plan player hazard (stationary player) 0 switch
      have hboundaryRewrite : boundary = stationary player +
          (boundary - stationary player) := by ring
      rw [hboundaryRewrite, hadd]
      linarith
    change quittingRootSequenceHazardTerminalValue reward spliced player hazard 0 ≤
      quittingRootSequenceTerminalValue reward spliced player 0 +
        (equilibriumError + punishmentError)
    have hexp0 : 0 ≤ Real.exp (-scale) := Real.exp_nonneg _
    have hscaleNonneg : 0 ≤ scale + 3 := by linarith
    nlinarith

/-- Arbitrarily small source-faithful normalized-motion rows close the
corrected stationarily generated branch whenever the instant branch fails. -/
theorem stationarilyGenerated_of_arbitrarilySmallNormalizedMotionRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hinstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward)
    (hsource : HasArbitrarilySmallQuittingNormalizedMotionRows reward) :
    QuittingStationarilyGeneratedApproximateEquilibria reward := by
  classical
  obtain ⟨noSureScale, hnoSureScalePos, hnoSureScale⟩ :=
    exists_pos_noSure_support_scale_of_not_instant reward hinstant
  intro punishmentError hpunishmentError equilibriumError hequilibriumError
  let M := quittingRewardBound reward
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hdenom : 0 < 8 * (4 * M + 1) := by linarith
  have htarget : 0 < equilibriumError / (8 * (4 * M + 1)) :=
    div_pos hequilibriumError hdenom
  obtain ⟨scale, hscale, hdecay⟩ :=
    exists_scale_ge_two_exp_neg_lt htarget
  have hscaleDenom : 0 < 8 * (scale + 3) := by linarith
  have hmotionTarget : 0 < equilibriumError / (8 * (scale + 3)) :=
    div_pos hequilibriumError hscaleDenom
  let upper := min noSureScale (equilibriumError / (8 * (scale + 3)))
  have hupper : 0 < upper := lt_min hnoSureScalePos hmotionTarget
  obtain ⟨error, tail, root, herror, herrorUpper, hrational, hsupport,
      habsorption, hmotion⟩ := hsource upper hupper
  obtain ⟨player, _hplayer⟩ :=
    exists_quitProbability_pos_of_absorptionMass_pos root habsorption
  letI : Nonempty ι := ⟨player⟩
  have herrorNoSure : error ≤ noSureScale := by
    exact herrorUpper.le.trans (min_le_left _ _)
  have hnoSure : ¬QuittingRootHasSureQuitter root :=
    hnoSureScale tail root (hrational.mono herrorNoSure)
      (hsupport.mono herrorNoSure)
  have herrorMotion : error < equilibriumError / (8 * (scale + 3)) :=
    herrorUpper.trans_le (min_le_right _ _)
  have hmotionSmall : 2 * error * (scale + 3) < equilibriumError / 4 := by
    have hmul := mul_lt_mul_of_pos_right herrorMotion (by linarith : 0 < scale + 3)
    have hcancel : equilibriumError / (8 * (scale + 3)) * (scale + 3) =
        equilibriumError / 8 := by
      field_simp
    rw [hcancel] at hmul
    linarith
  have hdecaySmall : 4 * M * Real.exp (-scale) < equilibriumError / 8 := by
    have hmul := mul_lt_mul_of_pos_left hdecay (by linarith : 0 < 4 * M + 1)
    have hleft : 4 * M * Real.exp (-scale) ≤
        (4 * M + 1) * Real.exp (-scale) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
    have hcancel : (4 * M + 1) *
        (equilibriumError / (8 * (4 * M + 1))) = equilibriumError / 8 := by
      field_simp
    rw [hcancel] at hmul
    exact hleft.trans_lt hmul
  have hsmall : 2 * error * (scale + 3) +
      4 * quittingRewardBound reward * Real.exp (-scale) < equilibriumError := by
    dsimp only [M] at hdecaySmall
    linarith
  obtain ⟨horizon, who, punishment, hhorizon, hpunish, hnash⟩ :=
    exists_stationaryPrefix_punishment_nash_of_normalizedMotionRow
      reward herror hscale hpunishmentError tail root hrational hsupport
        habsorption hmotion hnoSure hsmall
  exact ⟨root, horizon, who, punishment, hhorizon, hpunish, hnash⟩

/-! ## Fixed-scale contrapositive -/

/-- At scale `rate`, every rational support-local row has normalized motion
at least `rate` in some coordinate.  The predicate does not assert that any
such row exists. -/
def HasQuittingNormalizedMotionLowerBoundAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (rate : ℝ) : Prop :=
  ∀ tail root,
    QuittingSimonRationalPayoffAt reward rate tail →
      IsQuittingRootSupportApproxNash reward tail rate root →
        ∃ who,
          rate * quittingRootAbsorptionMass root ≤
            |quittingRootSuccessorPayoff reward tail root who - tail who|

/-- If neither the instant nor the corrected stationarily generated branch
exists, one fixed positive scale obstructs every rational support-local row.
This is a lower bound only; it carries no feasibility assertion. -/
theorem exists_normalizedMotionLowerBound_of_not_branches
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hinstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward)
    (hgenerated : ¬QuittingStationarilyGeneratedApproximateEquilibria reward) :
    ∃ rate : ℝ, 0 < rate ∧ rate < 1 ∧
      HasQuittingNormalizedMotionLowerBoundAt reward rate := by
  classical
  by_contra hlower
  push Not at hlower
  apply hgenerated
  apply stationarilyGenerated_of_arbitrarilySmallNormalizedMotionRows
    reward hinstant
  intro upper hupper
  let rate := min (upper / 2) (1 / 2 : ℝ)
  have hrate : 0 < rate := lt_min (by linarith) (by norm_num)
  have hrateUpper : rate < upper :=
    (min_le_left (upper / 2) (1 / 2 : ℝ)).trans_lt (by linarith)
  have hrateOne : rate < 1 :=
    (min_le_right (upper / 2) (1 / 2 : ℝ)).trans_lt (by norm_num)
  have hnot := hlower rate hrate hrateOne
  unfold HasQuittingNormalizedMotionLowerBoundAt at hnot
  push Not at hnot
  obtain ⟨tail, root, hrational, hsupport, hmotion⟩ := hnot
  have habsorption : 0 < quittingRootAbsorptionMass root := by
    have hnonneg := quittingRootAbsorptionMass_nonneg root
    refine lt_of_le_of_ne hnonneg fun hzero => ?_
    have hzero' : quittingRootAbsorptionMass root = 0 := hzero.symm
    let who : ι := Classical.choice inferInstance
    have hwho := hmotion who
    rw [hzero', mul_zero] at hwho
    exact (not_lt_of_ge (abs_nonneg _)) hwho
  exact ⟨rate, tail, root, hrate, hrateUpper, hrational, hsupport,
    habsorption, hmotion⟩

/-- Corrected compact-row trichotomy: the instant branch, the stationarily
generated branch, or a fixed positive normalized-motion obstruction. -/
theorem instant_or_stationarilyGenerated_or_normalizedMotionLowerBound
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingInstantPunishmentεEquilibriumExistence reward ∨
      QuittingStationarilyGeneratedApproximateEquilibria reward ∨
      ∃ rate : ℝ, 0 < rate ∧ rate < 1 ∧
        HasQuittingNormalizedMotionLowerBoundAt reward rate := by
  by_cases hinstant : QuittingInstantPunishmentεEquilibriumExistence reward
  · exact Or.inl hinstant
  · by_cases hgenerated :
        QuittingStationarilyGeneratedApproximateEquilibria reward
    · exact Or.inr (Or.inl hgenerated)
    · exact Or.inr (Or.inr
        (exists_normalizedMotionLowerBound_of_not_branches
          reward hinstant hgenerated))

end GameTheory
