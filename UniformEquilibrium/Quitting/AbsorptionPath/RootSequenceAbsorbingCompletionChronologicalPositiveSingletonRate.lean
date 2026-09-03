/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.ChronologicalMarkedRootSequenceSingletonDerivativeSupport
import UniformEquilibrium.Quitting.AbsorptionPath.RootSequenceAbsorbingCompletionChronologicalSingletonLowerBound
import UniformEquilibrium.Quitting.Classification.Existence.ActiveOpponentDeviationTelescope
import UniformEquilibrium.Quitting.Classification.Existence.GlobalRefusalLedger

/-!
# Positive singleton-rate equality for chronological absorbing-completion limits

At a nonterminal time of the actual chronological source limit, a positive
right derivative in one player's singleton coordinate forces the continuation
payoff to equal that player's singleton reward.  The upper bound is proved by
localizing a positive singleton-mass window, controlling its collision mass
quadratically, and charging the remaining low-opponent dates to the finite
refusal telescope.  The matching lower bound comes from the adjacent-cut
theorem in `RootSequenceAbsorbingCompletionChronologicalSingletonLowerBound`.

This module proves the active continuous-clock equality for the same decoded
chronological path.  It does not reprove the jump-row component: the final
bundle imports and consumes the already checked chronological jump theorem.
It does not construct a well-supported absorbing sequence or assert the AKRS
trichotomy.
-/

noncomputable section

namespace GameTheory

open Filter Finset MeasureTheory Set
open Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingAbsorptionPath

omit [Nonempty ι] in
/-- A positive lower right derivative gives a quantitative lower bound along
every sequence which approaches through the open right neighborhood. -/
theorem eventually_rate_mul_sub_lt_coalitionCDF_sub_of_pathRightDerivative_gt
    (law : ProbabilityMeasure (QuittingChronologicalEvent reward))
    (coalition : {S : Finset ι // S.Nonempty}) {time rate : ℝ}
    (hrate : rate < pathRightDerivative (chronologicalCadlagPath law) time coalition)
    (point : ℕ → ℝ)
    (hpoint : Tendsto point atTop (nhdsWithin time (Ioo time 1))) :
    ∀ᶠ rank in atTop,
      rate * (point rank - time) <
        chronologicalCoalitionCDF law coalition (point rank) -
          chronologicalCoalitionCDF law coalition time := by
  let rightFilter := nhdsWithin time (Ioo time 1)
  let quotient := fun s : ℝ ↦
    (chronologicalCoalitionCDF law coalition s -
      chronologicalCoalitionCDF law coalition time) / (s - time)
  have hnonneg : ∀ᶠ s in rightFilter, 0 ≤ quotient s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact div_nonneg
      (sub_nonneg.mpr <| ProbabilityTheory.monotone_cdf
        (chronologicalCoalitionClockLaw law coalition) hs.1.le)
      (sub_nonneg.mpr hs.1.le)
  have hquotient : ∀ᶠ s in rightFilter, rate < quotient s := by
    apply eventually_lt_of_lt_liminf
    · change rate < Filter.liminf quotient rightFilter at hrate
      exact hrate
    · exact isBoundedUnder_of_eventually_ge hnonneg
  have hpointMem : ∀ᶠ rank in atTop, point rank ∈ Ioo time 1 :=
    hpoint self_mem_nhdsWithin
  have hpointQuotient : ∀ᶠ rank in atTop, rate < quotient (point rank) :=
    hpoint hquotient
  filter_upwards [hpointMem, hpointQuotient] with rank hrank hquotientRank
  exact (lt_div_iff₀ (sub_pos.mpr hrank.1)).mp hquotientRank

omit [Nonempty ι] in
/-- Along a controlled right sequence, the collision CDF increment is
little-o of the clock displacement. -/
theorem eventually_collisionCDF_sub_lt_coefficient_mul_sub_of_controlledRightSequence
    {roots : ℕ → ℕ → ι → PMF Bool}
    (certificates : ∀ rank,
      QuittingFiniteRootSequenceAbsorption (roots rank))
    (law : ProbabilityMeasure (QuittingChronologicalEvent reward))
    (hlaw : Tendsto
      (fun rank ↦ (certificates rank).chronologicalLaw reward)
      atTop (nhds law))
    {time : ℝ}
    (htimeContinuous : ContinuousAt (chronologicalClockCDF law) time)
    (controlled : MathUE.HasClockGap.ControlledRightSequence
      (chronologicalClockCDF law) time 1)
    {coefficient : ℝ} (hcoefficient : 0 < coefficient) :
    ∀ᶠ rank in atTop,
      chronologicalCollisionCDF law (controlled.point rank) -
          chronologicalCollisionCDF law time <
        coefficient * (controlled.point rank - time) := by
  let ratio := fun rank : ℕ ↦
    4 * (Fintype.card ι).choose 2 *
      (controlled.point rank - time) / (1 - controlled.point rank)
  have hratio : Tendsto ratio atTop (nhds 0) := by
    have htimeTendsto : Tendsto (fun _ : ℕ ↦ time) atTop (nhds time) :=
      tendsto_const_nhds
    have honeTendsto : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hnumerator : Tendsto
        (fun rank ↦ controlled.point rank - time) atTop (nhds 0) := by
      simpa only [sub_self] using controlled.tendsto.sub htimeTendsto
    have hdenominator : Tendsto
        (fun rank ↦ 1 - controlled.point rank) atTop (nhds (1 - time)) :=
      honeTendsto.sub controlled.tendsto
    have htime_ne_one : time ≠ 1 := by
      exact ne_of_lt (controlled.point_mem 0 |>.1.trans
        (controlled.point_mem 0 |>.2))
    have hquotient := hnumerator.div hdenominator
      (sub_ne_zero.mpr htime_ne_one.symm)
    change Tendsto
      (fun rank ↦ (controlled.point rank - time) /
        (1 - controlled.point rank)) atTop
      (nhds (0 / (1 - time))) at hquotient
    have hquotient' : Tendsto
        (fun rank ↦ (controlled.point rank - time) /
          (1 - controlled.point rank)) atTop (nhds 0) := by
      simpa only [zero_div] using hquotient
    have hscaled := Filter.Tendsto.const_mul
      (4 * (Fintype.card ι).choose 2 : ℝ) hquotient'
    convert hscaled using 1
    · funext rank
      dsimp only [ratio]
      field_simp [(sub_pos.mpr (controlled.point_mem rank).2).ne']
    · norm_num
  have hratioSmall : ∀ᶠ rank in atTop, ratio rank < coefficient :=
    hratio.eventually_lt_const hcoefficient
  filter_upwards [hratioSmall] with rank hsmall
  let point := controlled.point rank
  have hpoint : point ∈ Ioo time 1 := controlled.point_mem rank
  have hquadratic :=
    one_sub_upper_mul_collisionCDF_sub_le_choose_mul_clockCDF_sub_sq_of_tendsto
      certificates law hlaw hpoint.1.le hpoint.2 htimeContinuous
        (controlled.continuousAt rank)
  have hclockLe :
      chronologicalClockCDF law point - chronologicalClockCDF law time ≤
        2 * (point - time) := controlled.distribution_sub_le_two_mul rank
  have hclockNonneg :
      0 ≤ chronologicalClockCDF law point -
        chronologicalClockCDF law time :=
    sub_nonneg.mpr <| ProbabilityTheory.monotone_cdf
      (chronologicalClockLaw law) hpoint.1.le
  have hsquare :
      (chronologicalClockCDF law point - chronologicalClockCDF law time) ^ 2 ≤
        (2 * (point - time)) ^ 2 := by nlinarith
  have hchoose : (0 : ℝ) ≤ (Fintype.card ι).choose 2 := by positivity
  have hmass :
      (1 - point) *
          (chronologicalCollisionCDF law point -
            chronologicalCollisionCDF law time) ≤
        4 * (Fintype.card ι).choose 2 * (point - time) ^ 2 := by
    calc
      _ ≤ (Fintype.card ι).choose 2 *
          (chronologicalClockCDF law point -
            chronologicalClockCDF law time) ^ 2 := hquadratic
      _ ≤ (Fintype.card ι).choose 2 * (2 * (point - time)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare hchoose
      _ = 4 * (Fintype.card ι).choose 2 * (point - time) ^ 2 := by ring
  have hwidth : 0 < point - time := sub_pos.mpr hpoint.1
  have hdenominator : 0 < 1 - point := sub_pos.mpr hpoint.2
  have hcollisionLe :
      chronologicalCollisionCDF law point -
        chronologicalCollisionCDF law time ≤ ratio rank * (point - time) := by
    have hdiv :
        chronologicalCollisionCDF law point -
            chronologicalCollisionCDF law time ≤
          4 * (Fintype.card ι).choose 2 * (point - time) ^ 2 /
            (1 - point) := by
      apply (le_div_iff₀ hdenominator).2
      simpa only [mul_comm] using hmass
    dsimp only [ratio, point]
    calc
      _ ≤ 4 * (Fintype.card ι).choose 2 *
          (controlled.point rank - time) ^ 2 /
            (1 - controlled.point rank) := hdiv
      _ = (4 * (Fintype.card ι).choose 2 *
          (controlled.point rank - time) /
            (1 - controlled.point rank)) *
          (controlled.point rank - time) := by
            field_simp
  exact hcollisionLe.trans_lt <|
    mul_lt_mul_of_pos_right hsmall hwidth

namespace QuittingFiniteRootSequenceAbsorption

variable {roots : ℕ → ι → PMF Bool}

omit [Nonempty ι] in
/-- One coalition CDF increment of a finite chronological law is exactly the
sum of the source stage masses whose clocks enter the half-open interval. -/
theorem chronologicalCoalitionCDF_sub_eq_sum_stageCoalitionMass_Ioc
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {lower upper : ℝ} (hlowerUpper : lower ≤ upper) (hupper : upper ≤ 1)
    (coalition : {S : Finset ι // S.Nonempty}) :
    chronologicalCoalitionCDF (certificate.chronologicalLaw reward)
          coalition upper -
        chronologicalCoalitionCDF (certificate.chronologicalLaw reward)
          coalition lower =
      ∑ stage ∈ Finset.range (certificate.cutoff + 1),
        if quittingRootSequenceClock roots stage ∈ Ioc lower upper then
          quittingRootSequenceStageCoalitionMass roots stage coalition else 0 := by
  rw [chronologicalCoalitionCDF_eq_clockCoalitionEvent_real _ _ hupper,
    certificate.chronologicalLaw_clockCoalitionEvent_real_eq_value,
    chronologicalCoalitionCDF_eq_clockCoalitionEvent_real _ _
      (hlowerUpper.trans hupper),
    certificate.chronologicalLaw_clockCoalitionEvent_real_eq_value]
  unfold QuittingFiniteRootSequenceAbsorption.value
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro stage _
  by_cases hlower : quittingRootSequenceClock roots stage ≤ lower
  · rw [if_pos hlower, if_pos (hlower.trans hlowerUpper)]
    simp [hlower]
  · by_cases hupperClock : quittingRootSequenceClock roots stage ≤ upper
    · rw [if_neg hlower, if_pos hupperClock]
      simp [hlower, hupperClock]
    · rw [if_neg hlower, if_neg hupperClock]
      simp [hupperClock]

end QuittingFiniteRootSequenceAbsorption

end QuittingAbsorptionPath

omit [Nonempty ι] in
/-- The probability that one selected player quits together with at least one
opponent is bounded by the root's total collision mass. -/
theorem quitProbability_mul_opponentAbsorptionMass_le_collisionMass
    (root : ι → PMF Bool) (who : ι) :
    (root who true).toReal * quittingRootOpponentAbsorptionMass root who ≤
      quittingRootCollisionMass root := by
  let rate : ι → ℝ := quittingRootQuitRates root
  let others : Finset ι := Finset.univ.erase who
  have hrate0 : ∀ player, 0 ≤ rate player := fun _ ↦ ENNReal.toReal_nonneg
  have hrate1 : ∀ player, rate player ≤ 1 := fun player ↦
    ENNReal.toReal_mono ENNReal.one_ne_top ((root player).coe_le_one true)
  have hwhoNot : who ∉ others := by simp [others]
  have huniv : (Finset.univ : Finset ι) = insert who others :=
    (Finset.insert_erase (Finset.mem_univ who)).symm
  have hcollisionRest : 0 ≤ collisionMassFormulaOn rate others :=
    collisionMassFormulaOn_nonneg rate others
      (fun player hplayer ↦ hrate0 player)
      (fun player hplayer ↦ hrate1 player)
  have hcontinue : 0 ≤ 1 - rate who := sub_nonneg.mpr (hrate1 who)
  have hformula : collisionMass rate =
      (1 - rate who) * collisionMassFormulaOn rate others +
        rate who * (1 - ∏ player ∈ others, (1 - rate player)) := by
    rw [collisionMass_eq_one_sub_continueMass_sub_singletonMass]
    change collisionMassFormulaOn rate Finset.univ = _
    rw [huniv, collisionMassFormulaOn_insert rate hwhoNot]
  rw [quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  change rate who * (1 - ∏ player ∈ others, (1 - rate player)) ≤
    collisionMass rate
  rw [hformula]
  exact le_add_of_nonneg_left (mul_nonneg hcontinue hcollisionRest)

omit [Nonempty ι] in
/-- A finite singleton window is paid either by selected refusal charge on
low-opponent dates or by collision charge on the rejected dates. -/
theorem threshold_mul_singletonStageMass_sum_le_selectedRefusal_add_collision
    (roots : ℕ → ι → PMF Bool) (who : ι) (dates : Finset ℕ)
    {threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    threshold * ∑ stage ∈ dates,
        QuittingAbsorptionPath.quittingRootSequenceStageCoalitionMass
          roots stage (quittingSingletonTerminal who) ≤
      ∑ stage ∈ dates,
        if quittingRootOpponentAbsorptionMass (roots stage) who ≤ threshold then
          threshold *
            (QuittingAbsorptionPath.quittingRootSequenceSurvival roots stage *
              (roots stage who true).toReal)
        else
          QuittingAbsorptionPath.quittingRootSequenceSurvival roots stage *
            quittingRootCollisionMass (roots stage) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro stage _
  by_cases hgood :
      quittingRootOpponentAbsorptionMass (roots stage) who ≤ threshold
  · rw [if_pos hgood]
    have hsingleton := quittingRootCoalitionMass_le_quitProbability_of_mem
      (roots stage) {who} who (by simp)
    change threshold *
        (QuittingAbsorptionPath.quittingRootSequenceSurvival roots stage *
          quittingRootCoalitionMass (roots stage) {who}) ≤ _
    apply mul_le_mul_of_nonneg_left
    · exact mul_le_mul_of_nonneg_left hsingleton
        (QuittingAbsorptionPath.quittingRootSequenceSurvival_nonneg roots stage)
    · exact hthreshold
  · rw [if_neg hgood]
    have hbad : threshold <
        quittingRootOpponentAbsorptionMass (roots stage) who :=
      lt_of_not_ge hgood
    have hsingleton := quittingRootCoalitionMass_le_quitProbability_of_mem
      (roots stage) {who} who (by simp)
    have hsingleton0 := quittingRootCoalitionMass_nonneg (roots stage) {who}
    have hopponent0 := quittingRootOpponentAbsorptionMass_nonneg
      (roots stage) who
    have hroot : threshold * quittingRootCoalitionMass (roots stage) {who} ≤
        quittingRootCollisionMass (roots stage) := by
      calc
        threshold * quittingRootCoalitionMass (roots stage) {who} ≤
            quittingRootOpponentAbsorptionMass (roots stage) who *
              quittingRootCoalitionMass (roots stage) {who} :=
          mul_le_mul_of_nonneg_right hbad.le hsingleton0
        _ ≤ quittingRootOpponentAbsorptionMass (roots stage) who *
              (roots stage who true).toReal :=
          mul_le_mul_of_nonneg_left hsingleton hopponent0
        _ = (roots stage who true).toReal *
              quittingRootOpponentAbsorptionMass (roots stage) who := by ring
        _ ≤ quittingRootCollisionMass (roots stage) :=
          quitProbability_mul_opponentAbsorptionMass_le_collisionMass
            (roots stage) who
    change threshold *
        (QuittingAbsorptionPath.quittingRootSequenceSurvival roots stage *
          quittingRootCoalitionMass (roots stage) {who}) ≤ _
    calc
      threshold *
          (QuittingAbsorptionPath.quittingRootSequenceSurvival roots stage *
            quittingRootCoalitionMass (roots stage) {who}) =
          QuittingAbsorptionPath.quittingRootSequenceSurvival roots stage *
            (threshold * quittingRootCoalitionMass (roots stage) {who}) := by ring
      _ ≤ QuittingAbsorptionPath.quittingRootSequenceSurvival roots stage *
            quittingRootCollisionMass (roots stage) :=
        mul_le_mul_of_nonneg_left hroot
          (QuittingAbsorptionPath.quittingRootSequenceSurvival_nonneg roots stage)

omit [Nonempty ι] in
/-- In one finite chronological window, singleton mass is paid by selected
refusal charge on low-opponent dates plus the whole collision mass of the
window. -/
theorem threshold_mul_singletonCDFIncrement_le_selectedRefusal_add_collisionCDFIncrement
    {roots : ℕ → ι → PMF Bool}
    (certificate :
      QuittingAbsorptionPath.QuittingFiniteRootSequenceAbsorption roots)
    (who : ι) {lower upper threshold : ℝ}
    (hlowerUpper : lower ≤ upper) (hupper : upper ≤ 1)
    (hthreshold : 0 ≤ threshold) :
    threshold *
        (QuittingAbsorptionPath.chronologicalCoalitionCDF
            (certificate.chronologicalLaw reward)
              (quittingSingletonTerminal who) upper -
          QuittingAbsorptionPath.chronologicalCoalitionCDF
            (certificate.chronologicalLaw reward)
              (quittingSingletonTerminal who) lower) ≤
      (∑ stage ∈ Finset.range (certificate.cutoff + 1),
        if QuittingAbsorptionPath.quittingRootSequenceClock roots stage ∈
              Ioc lower upper ∧
            quittingRootOpponentAbsorptionMass (roots stage) who ≤ threshold then
          threshold *
            (QuittingAbsorptionPath.quittingRootSequenceSurvival roots stage *
              (roots stage who true).toReal)
        else 0) +
      (QuittingAbsorptionPath.chronologicalCollisionCDF
          (certificate.chronologicalLaw reward) upper -
        QuittingAbsorptionPath.chronologicalCollisionCDF
          (certificate.chronologicalLaw reward) lower) := by
  classical
  let dates := (Finset.range (certificate.cutoff + 1)).filter fun stage ↦
    QuittingAbsorptionPath.quittingRootSequenceClock roots stage ∈
      Ioc lower upper
  have hpaid := threshold_mul_singletonStageMass_sum_le_selectedRefusal_add_collision
    roots who dates hthreshold
  have hsingleton :
      QuittingAbsorptionPath.chronologicalCoalitionCDF
            (certificate.chronologicalLaw reward)
              (quittingSingletonTerminal who) upper -
          QuittingAbsorptionPath.chronologicalCoalitionCDF
            (certificate.chronologicalLaw reward)
              (quittingSingletonTerminal who) lower =
        ∑ stage ∈ dates,
          QuittingAbsorptionPath.quittingRootSequenceStageCoalitionMass
            roots stage (quittingSingletonTerminal who) := by
    rw [certificate.chronologicalCoalitionCDF_sub_eq_sum_stageCoalitionMass_Ioc
      hlowerUpper hupper]
    simp only [dates, Finset.sum_filter]
  rw [hsingleton]
  apply hpaid.trans
  have hcollision :
      (∑ stage ∈ dates,
        QuittingAbsorptionPath.quittingRootSequenceSurvival roots stage *
          quittingRootCollisionMass (roots stage)) =
        QuittingAbsorptionPath.chronologicalCollisionCDF
            (certificate.chronologicalLaw reward) upper -
          QuittingAbsorptionPath.chronologicalCollisionCDF
            (certificate.chronologicalLaw reward) lower := by
    rw [certificate.chronologicalCollisionCDF_sub_eq_sum
      hlowerUpper hupper]
    simp only [dates, Finset.sum_filter]
  have hselected :
      (∑ stage ∈ Finset.range (certificate.cutoff + 1),
        if QuittingAbsorptionPath.quittingRootSequenceClock roots stage ∈
              Ioc lower upper ∧
            quittingRootOpponentAbsorptionMass (roots stage) who ≤ threshold then
          threshold *
            (QuittingAbsorptionPath.quittingRootSequenceSurvival roots stage *
              (roots stage who true).toReal)
        else 0) =
      ∑ stage ∈ dates,
        if quittingRootOpponentAbsorptionMass (roots stage) who ≤ threshold then
          threshold *
            (QuittingAbsorptionPath.quittingRootSequenceSurvival roots stage *
              (roots stage who true).toReal)
        else 0 := by
    simp only [dates, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro stage _
    by_cases hwindow :
        QuittingAbsorptionPath.quittingRootSequenceClock roots stage ∈
          Ioc lower upper <;>
      by_cases hgood :
        quittingRootOpponentAbsorptionMass (roots stage) who ≤ threshold <;>
      simp [hwindow, hgood]
  rw [hselected, ← hcollision, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro stage hstage
  have hwindow :
      QuittingAbsorptionPath.quittingRootSequenceClock roots stage ∈
        Ioc lower upper := Finset.mem_filter.mp hstage |>.2
  by_cases hgood :
      quittingRootOpponentAbsorptionMass (roots stage) who ≤ threshold
  · rw [if_pos hgood]
    simp only [hgood, if_true]
    exact le_add_of_nonneg_right <|
      mul_nonneg
        (QuittingAbsorptionPath.quittingRootSequenceSurvival_nonneg roots stage)
        (quittingRootCollisionMass_nonneg (roots stage))
  · rw [if_neg hgood]
    simp only [hgood, if_false, zero_add]
    exact le_rfl

omit [Nonempty ι] in
/-- One source window with linear singleton mass, sublinear collision mass,
a uniform positive continuation gap, and Nash error smaller than its selected
refusal charge is impossible. -/
theorem false_of_positiveSingletonWindow_and_smallNashError
    {roots : ℕ → ι → PMF Bool}
    (certificate :
      QuittingAbsorptionPath.QuittingFiniteRootSequenceAbsorption roots)
    (who : ι) {lower upper threshold rate delta error : ℝ}
    (hlowerUpper : lower ≤ upper) (hupper : upper ≤ 1)
    (hthreshold : 0 < threshold)
    (hdelta : 0 < delta)
    (hnash : IsεQuittingRootSequenceNash reward error roots)
    (hsingleton : rate * (upper - lower) ≤
      QuittingAbsorptionPath.chronologicalCoalitionCDF
          (certificate.chronologicalLaw reward)
            (quittingSingletonTerminal who) upper -
        QuittingAbsorptionPath.chronologicalCoalitionCDF
          (certificate.chronologicalLaw reward)
            (quittingSingletonTerminal who) lower)
    (hcollision :
      QuittingAbsorptionPath.chronologicalCollisionCDF
          (certificate.chronologicalLaw reward) upper -
        QuittingAbsorptionPath.chronologicalCollisionCDF
          (certificate.chronologicalLaw reward) lower ≤
      threshold * rate * (upper - lower) / 2)
    (herror : error < delta * rate * (upper - lower) / 2)
    (hgap : ∀ stage ∈ Finset.range (certificate.cutoff + 1),
      QuittingAbsorptionPath.quittingRootSequenceClock roots stage ∈
          Ioc lower upper →
        quittingRootOpponentAbsorptionMass (roots stage) who ≤ threshold →
        delta ≤
          quittingRootSequenceTerminalValue reward roots who stage -
            quittingRootQuitPayoff reward
              (quittingRootSequenceTailVector reward roots (stage + 1))
              (roots stage) who) : False := by
  classical
  let selected := (Finset.range (certificate.cutoff + 1)).filter fun stage ↦
    QuittingAbsorptionPath.quittingRootSequenceClock roots stage ∈
        Ioc lower upper ∧
      quittingRootOpponentAbsorptionMass (roots stage) who ≤ threshold
  let refusal := ∑ stage ∈ selected,
    quittingJointSurvivalWeight roots 0 stage *
      (roots stage who true).toReal
  have hwindow :=
    threshold_mul_singletonCDFIncrement_le_selectedRefusal_add_collisionCDFIncrement
      (reward := reward) (roots := roots)
      certificate who hlowerUpper hupper hthreshold.le
  have hselected :
      (∑ stage ∈ Finset.range (certificate.cutoff + 1),
        if QuittingAbsorptionPath.quittingRootSequenceClock roots stage ∈
              Ioc lower upper ∧
            quittingRootOpponentAbsorptionMass (roots stage) who ≤ threshold then
          threshold *
            (QuittingAbsorptionPath.quittingRootSequenceSurvival roots stage *
              (roots stage who true).toReal)
        else 0) = threshold * refusal := by
    rw [Finset.mul_sum]
    simp only [selected, Finset.sum_filter,
      QuittingAbsorptionPath.quittingRootSequenceSurvival]
  rw [hselected] at hwindow
  have hrefusalLower : rate * (upper - lower) / 2 ≤ refusal := by
    have hscaled :
        threshold * rate * (upper - lower) ≤
          threshold * refusal + threshold * rate * (upper - lower) / 2 := by
      calc
        threshold * rate * (upper - lower) =
            threshold * (rate * (upper - lower)) := by ring
        _ ≤ threshold *
            (QuittingAbsorptionPath.chronologicalCoalitionCDF
                (certificate.chronologicalLaw reward)
                  (quittingSingletonTerminal who) upper -
              QuittingAbsorptionPath.chronologicalCoalitionCDF
                (certificate.chronologicalLaw reward)
                  (quittingSingletonTerminal who) lower) :=
          mul_le_mul_of_nonneg_left hsingleton hthreshold.le
        _ ≤ threshold * refusal +
            (QuittingAbsorptionPath.chronologicalCollisionCDF
                (certificate.chronologicalLaw reward) upper -
              QuittingAbsorptionPath.chronologicalCollisionCDF
                (certificate.chronologicalLaw reward) lower) := hwindow
        _ ≤ threshold * refusal +
            threshold * rate * (upper - lower) / 2 :=
          add_le_add (le_refl _) hcollision
    nlinarith
  have hfinite := delta_mul_finiteRefusalCharge_le_of_nash
    reward roots hnash hdelta who selected fun stage hstage ↦ by
      have hmem := Finset.mem_filter.mp hstage
      exact hgap stage hmem.1
        (hmem.2.1) (hmem.2.2)
  have : delta * rate * (upper - lower) / 2 ≤ error := by
    calc
      delta * rate * (upper - lower) / 2 =
          delta * (rate * (upper - lower) / 2) := by ring
      _ ≤ delta * refusal := mul_le_mul_of_nonneg_left hrefusalLower hdelta.le
      _ ≤ error := by simpa [refusal] using hfinite
  linarith

omit [DecidableEq ι] [Nonempty ι] in
/-- Every post-stage continuation value in a finite source window stays
within twice the reward bound times the window's conditional absorption
mass of the value at the window entrance. -/
theorem abs_quittingRootSequenceTailVector_sub_later_le_two_mul_one_sub_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingRootSequenceTailVector reward roots start who -
        quittingRootSequenceTailVector reward roots (start + fuel) who| ≤
      2 * bound *
        (1 - quittingJointSurvivalWeight roots start fuel) := by
  let survival := quittingJointSurvivalWeight roots start fuel
  let intercept := ∑ offset ∈ Finset.range fuel,
    quittingJointSurvivalWeight roots start offset *
      quittingRootAbsorbingContribution reward (roots (start + offset)) who
  let value := fun stage ↦
    quittingRootSequenceTerminalValue reward roots who stage
  have hdecomposition : value start = intercept + survival * value (start + fuel) := by
    exact eq_sum_jointSurvivalWeight_mul_absorbingContribution_add
      reward roots who value
        (isQuittingLivePrescribedValue_quittingRootSequenceTerminalValue
          reward roots who) start fuel
  have hintercept : |intercept| ≤ bound * (1 - survival) := by
    calc
      |intercept| ≤ ∑ offset ∈ Finset.range fuel,
          |quittingJointSurvivalWeight roots start offset *
            quittingRootAbsorbingContribution
              reward (roots (start + offset)) who| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ offset ∈ Finset.range fuel,
          bound *
            (quittingJointSurvivalWeight roots start offset *
              quittingRootAbsorptionMass (roots (start + offset))) := by
        apply Finset.sum_le_sum
        intro offset _
        rw [abs_mul, abs_of_nonneg
          (quittingJointSurvivalWeight_nonneg roots start offset)]
        have hcontribution :=
          abs_quittingRootAbsorbingContribution_le_mul_absorptionMass
            reward (roots (start + offset)) who hreward
        calc
          quittingJointSurvivalWeight roots start offset *
              |quittingRootAbsorbingContribution
                reward (roots (start + offset)) who| ≤
              quittingJointSurvivalWeight roots start offset *
                (bound * quittingRootAbsorptionMass
                  (roots (start + offset))) :=
            mul_le_mul_of_nonneg_left hcontribution
              (quittingJointSurvivalWeight_nonneg roots start offset)
          _ = bound *
              (quittingJointSurvivalWeight roots start offset *
                quittingRootAbsorptionMass (roots (start + offset))) := by ring
      _ = bound * (1 - survival) := by
        rw [← Finset.mul_sum,
          sum_jointSurvivalWeight_mul_absorptionMass roots start fuel]
  have hfar : |value (start + fuel)| ≤ bound :=
    abs_quittingRootSequenceTerminalValue_le reward roots who (start + fuel)
      hbound hreward
  have hsurvivalLe : survival ≤ 1 :=
    quittingJointSurvivalWeight_le_one roots start fuel
  change |value start - value (start + fuel)| ≤ _
  rw [hdecomposition]
  calc
    |intercept + survival * value (start + fuel) - value (start + fuel)| =
        |intercept + (survival - 1) * value (start + fuel)| := by ring_nf
    _ ≤ |intercept| + |(survival - 1) * value (start + fuel)| :=
      abs_add_le _ _
    _ ≤ bound * (1 - survival) +
        (1 - survival) * bound := by
      apply add_le_add hintercept
      rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hsurvivalLe)]
      have heq : -(survival - 1) = 1 - survival := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hfar
        (sub_nonneg.mpr hsurvivalLe)
    _ = 2 * bound * (1 - survival) := by ring

omit [DecidableEq ι] [Nonempty ι] in
/-- Conditional survival between two ordered stages is the ratio of their
global source survivals. -/
theorem quittingJointSurvivalWeight_eq_survival_div
    (roots : ℕ → ι → PMF Bool) {earlier later : ℕ}
    (hearlierLater : earlier ≤ later)
    (hearlierPositive :
      0 < QuittingAbsorptionPath.quittingRootSequenceSurvival roots earlier) :
    quittingJointSurvivalWeight roots earlier (later - earlier) =
      QuittingAbsorptionPath.quittingRootSequenceSurvival roots later /
        QuittingAbsorptionPath.quittingRootSequenceSurvival roots earlier := by
  obtain ⟨fuel, rfl⟩ := Nat.exists_eq_add_of_le hearlierLater
  rw [Nat.add_sub_cancel_left]
  have hfactor := quittingJointSurvivalWeight_add roots 0 earlier fuel
  have hfactor' :
      QuittingAbsorptionPath.quittingRootSequenceSurvival roots
          (earlier + fuel) =
        QuittingAbsorptionPath.quittingRootSequenceSurvival roots earlier *
          quittingJointSurvivalWeight roots earlier fuel := by
    simpa [QuittingAbsorptionPath.quittingRootSequenceSurvival] using hfactor
  apply (eq_div_iff hearlierPositive.ne').2
  rw [mul_comm]
  exact hfactor'.symm

omit [DecidableEq ι] [Nonempty ι] in
/-- Tail vectors at any two stages whose source clocks lie in the same
subterminal interval are uniformly close, independently of the number of
intervening stages. -/
theorem abs_quittingRootSequenceTailVector_sub_le_clockDiameter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {earlier later : ℕ}
    (hearlierLater : earlier ≤ later) {lower upper bound : ℝ}
    (hupper : upper < 1)
    (hearlierLower : lower ≤
      QuittingAbsorptionPath.quittingRootSequenceClock roots earlier)
    (hlaterUpper :
      QuittingAbsorptionPath.quittingRootSequenceClock roots later ≤ upper)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingRootSequenceTailVector reward roots earlier who -
        quittingRootSequenceTailVector reward roots later who| ≤
      2 * bound * ((upper - lower) / (1 - upper)) := by
  let survivalEarlier :=
    QuittingAbsorptionPath.quittingRootSequenceSurvival roots earlier
  let survivalLater :=
    QuittingAbsorptionPath.quittingRootSequenceSurvival roots later
  have hclockOrder :=
    QuittingAbsorptionPath.monotone_quittingRootSequenceClock roots
      hearlierLater
  have hsurvivalEarlierPositive : 0 < survivalEarlier := by
    dsimp only [survivalEarlier]
    unfold QuittingAbsorptionPath.quittingRootSequenceClock at hlaterUpper
    have hsurvivalLater : 1 - upper ≤
        QuittingAbsorptionPath.quittingRootSequenceSurvival roots later := by
      linarith
    have hsurvivalOrder :=
      QuittingAbsorptionPath.antitone_quittingRootSequenceSurvival roots
        hearlierLater
    linarith
  obtain ⟨fuel, rfl⟩ := Nat.exists_eq_add_of_le hearlierLater
  have htail :=
    abs_quittingRootSequenceTailVector_sub_later_le_two_mul_one_sub_survival
      reward roots who earlier fuel hbound hreward
  have hratio := quittingJointSurvivalWeight_eq_survival_div roots
    (Nat.le_add_right earlier fuel) hsurvivalEarlierPositive
  rw [Nat.add_sub_cancel_left] at hratio
  rw [hratio] at htail
  apply htail.trans
  have hdenominator : 0 < 1 - upper := sub_pos.mpr hupper
  have hsurvivalLower : 1 - upper ≤ survivalEarlier := by
    dsimp only [survivalEarlier]
    unfold QuittingAbsorptionPath.quittingRootSequenceClock at hlaterUpper
    have hsurvivalOrder :=
      QuittingAbsorptionPath.antitone_quittingRootSequenceSurvival roots
        (Nat.le_add_right earlier fuel)
    linarith
  have hclockDiameter :
      QuittingAbsorptionPath.quittingRootSequenceClock roots
          (earlier + fuel) -
        QuittingAbsorptionPath.quittingRootSequenceClock roots earlier ≤
          upper - lower := by
    linarith
  have hratioBound :
      1 - survivalLater / survivalEarlier ≤
        (upper - lower) / (1 - upper) := by
    have hidentity :
        1 - survivalLater / survivalEarlier =
          (QuittingAbsorptionPath.quittingRootSequenceClock roots
              (earlier + fuel) -
            QuittingAbsorptionPath.quittingRootSequenceClock roots earlier) /
              survivalEarlier := by
      rw [one_sub_div hsurvivalEarlierPositive.ne']
      congr 1
      dsimp only [survivalEarlier, survivalLater]
      unfold QuittingAbsorptionPath.quittingRootSequenceClock
      ring
    rw [hidentity]
    apply div_le_div₀
    · exact sub_nonneg.mpr <| hearlierLower.trans <|
        QuittingAbsorptionPath.monotone_quittingRootSequenceClock roots
          (Nat.le_add_right earlier fuel) |>.trans hlaterUpper
    · exact hclockDiameter
    · exact hdenominator
    · exact hsurvivalLower
  have hcoefficient : 0 ≤ 2 * bound := by positivity
  exact mul_le_mul_of_nonneg_left hratioBound hcoefficient

omit [DecidableEq ι] [Nonempty ι] in
/-- The same clock-diameter estimate without prescribing the order of the
two source stages. -/
theorem abs_quittingRootSequenceTailVector_sub_le_of_clocks_mem_Icc
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (first second : ℕ)
    {lower upper bound : ℝ} (hupper : upper < 1)
    (hfirst : QuittingAbsorptionPath.quittingRootSequenceClock roots first ∈
      Icc lower upper)
    (hsecond : QuittingAbsorptionPath.quittingRootSequenceClock roots second ∈
      Icc lower upper)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingRootSequenceTailVector reward roots first who -
        quittingRootSequenceTailVector reward roots second who| ≤
      2 * bound * ((upper - lower) / (1 - upper)) := by
  rcases le_total first second with horder | horder
  · exact abs_quittingRootSequenceTailVector_sub_le_clockDiameter
      reward roots who horder hupper hfirst.1 hsecond.2 hbound hreward
  · rw [abs_sub_comm]
    exact abs_quittingRootSequenceTailVector_sub_le_clockDiameter
      reward roots who horder hupper hsecond.1 hfirst.2 hbound hreward

end GameTheory

namespace GameTheory

open Filter Finset Set
open QuittingAbsorptionPath
open QuittingAbsorptionPath.QuittingFiniteRootSequenceAbsorption
open scoped Topology

namespace QuittingRootSequenceAbsorbingCompletionDiagonal

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : QuittingRootSequenceVanishingNashFamily reward}
    {diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source}

namespace ChronologicalLimit

/-- A strict sequence of actual completed source windows carrying the exact
simultaneous estimates used by positive singleton-rate refusal. -/
structure PositiveSingletonRefusalWindowSequence
    (limit : diagonal.ChronologicalLimit) (who : ι) (time rate threshold gap : ℝ)
    where
  rank : ℕ → ℕ
  rank_strictMono : StrictMono rank
  upper : ℕ → ℝ
  upper_mem : ∀ index, upper index ∈ Ioo time 1
  upper_tendsto : Tendsto upper atTop (nhds time)
  singleton_increment : ∀ index,
    rate * (upper index - time) ≤
      QuittingAbsorptionPath.chronologicalCoalitionCDF
          (diagonal.chronologicalLaw (limit.subsequence (rank index)))
            (quittingSingletonTerminal who) (upper index) -
        QuittingAbsorptionPath.chronologicalCoalitionCDF
          (diagonal.chronologicalLaw (limit.subsequence (rank index)))
            (quittingSingletonTerminal who) time
  collision_increment : ∀ index,
    QuittingAbsorptionPath.chronologicalCollisionCDF
          (diagonal.chronologicalLaw (limit.subsequence (rank index)))
            (upper index) -
        QuittingAbsorptionPath.chronologicalCollisionCDF
          (diagonal.chronologicalLaw (limit.subsequence (rank index))) time ≤
      threshold * rate * (upper index - time) / 2
  nash_error : ∀ index,
    diagonal.completedError (limit.subsequence (rank index)) <
      gap * rate * (upper index - time) / 2
  stage_gap : ∀ index stage,
    stage ∈ Finset.range (Nat.succ
      (diagonal.completion (limit.subsequence (rank index))).cutoff) →
    QuittingAbsorptionPath.quittingRootSequenceClock
        (diagonal.completedRoots (limit.subsequence (rank index))) stage ∈
      Ioc time (upper index) →
    quittingRootOpponentAbsorptionMass
        (diagonal.completedRoots (limit.subsequence (rank index)) stage) who ≤
      threshold →
    gap ≤
      quittingRootSequenceTerminalValue reward
          (diagonal.completedRoots (limit.subsequence (rank index))) who stage -
        quittingRootQuitPayoff reward
          (quittingRootSequenceTailVector reward
            (diagonal.completedRoots (limit.subsequence (rank index)))
              (stage + 1))
          (diagonal.completedRoots (limit.subsequence (rank index)) stage) who

omit [Nonempty ι] in
/-- A positive singleton refusal-window sequence contradicts the exact Nash
certificates of its actual completed source roots. -/
theorem PositiveSingletonRefusalWindowSequence.false
    {limit : diagonal.ChronologicalLimit} {who : ι}
    {time rate threshold gap : ℝ}
    (windows : PositiveSingletonRefusalWindowSequence (diagonal := diagonal) limit
      who time rate threshold gap)
    (hthreshold : 0 < threshold) (hgap : 0 < gap) : False := by
  let rank := ChronologicalLimit.subsequence limit (windows.rank 0)
  let roots := diagonal.completedRoots rank
  let certificate := (diagonal.completion rank).finiteAbsorptionCertificate
  exact false_of_positiveSingletonWindow_and_smallNashError
    (reward := reward) (roots := roots) certificate who
    (windows.upper_mem 0).1.le (windows.upper_mem 0).2.le
    hthreshold hgap (diagonal.nash rank)
    (windows.singleton_increment 0)
    (windows.collision_increment 0) (windows.nash_error 0)
    (windows.stage_gap 0)

/-- The quantitative source theorem needed by the positive singleton-rate
argument.  The four-gap margin pays one tail approximation, one within-window
tail displacement, and the quit-endpoint error, leaving the displayed gap for
the finite refusal telescope. -/
theorem nonempty_positiveSingletonRefusalWindowSequence
    (limit : diagonal.ChronologicalLimit) (who : ι) {time rate threshold gap : ℝ}
    (htime : time ∈ QuittingAbsorptionPath.pathTimes limit.path)
    (htime_ne_one : time ≠ 1)
    (hrate : 0 < rate) (hthreshold : 0 < threshold) (hgap : 0 < gap)
    (hrateDerivative : rate <
      QuittingAbsorptionPath.pathRightDerivative limit.path time
        (quittingSingletonTerminal who))
    (hpayoffMargin :
      reward (quittingSingletonTerminal who) who + 4 * gap ≤
        QuittingAbsorptionPath.absorptionPathPayoff
          reward limit.absorptionPath time who)
    (hendpoint : 2 * quittingRewardBound reward * threshold ≤ gap) :
    Nonempty (PositiveSingletonRefusalWindowSequence
      (diagonal := diagonal) limit who time rate threshold gap) := by
  classical
  let distribution := QuittingAbsorptionPath.chronologicalClockCDF limit.law
  have htime_lt_one : time < 1 :=
    lt_of_le_of_ne htime.1.2 htime_ne_one
  have hdistributionPath (point : ℝ) (hpoint : point ≤ 1) :
      QuittingAbsorptionPath.pathTotal limit.path point =
        distribution point := by
    exact
      QuittingAbsorptionPath.pathTotal_chronologicalCadlagPath_eq_chronologicalClockCDF
        limit.law hpoint
  have hfixed : distribution time = time := by
    rw [← hdistributionPath time htime.1.2]
    exact htime.2
  have hdomination (point : ℝ) (hpoint : point < 1) :
      point ≤ distribution point := by
    by_cases hpoint_nonneg : 0 ≤ point
    · rw [← hdistributionPath point hpoint.le]
      exact limit.le_pathTotal point ⟨hpoint_nonneg, hpoint.le⟩
    · exact (not_le.mp hpoint_nonneg).le.trans
        (ProbabilityTheory.cdf_nonneg _ point)
  have hcontinuousTime : ContinuousAt distribution time :=
    MathUE.HasClockGap.continuousAt_of_fixedPoint
      (ProbabilityTheory.monotone_cdf
        (QuittingAbsorptionPath.chronologicalClockLaw limit.law))
      (fun point ↦
        (ProbabilityTheory.cdf
          (QuittingAbsorptionPath.chronologicalClockLaw limit.law))
            |>.right_continuous point)
      hdomination htime_lt_one hfixed
  let controlled := Classical.choice <|
    MathUE.HasClockGap.nonempty_controlledRightSequence
      limit.hasClockGap_chronologicalClockCDF
      (ProbabilityTheory.monotone_cdf
        (QuittingAbsorptionPath.chronologicalClockLaw limit.law))
      (fun point ↦
        (ProbabilityTheory.cdf
          (QuittingAbsorptionPath.chronologicalClockLaw limit.law))
            |>.right_continuous point)
      hdomination
      (fun point ↦ ProbabilityTheory.cdf_le_one _ point)
      htime_lt_one hfixed
  let certificates := fun rank : ℕ ↦
    (diagonal.completion (limit.subsequence rank)).finiteAbsorptionCertificate
  have hsingletonEventually : ∀ᶠ index in atTop,
      rate * (controlled.point index - time) <
        QuittingAbsorptionPath.chronologicalCoalitionCDF limit.law
            (quittingSingletonTerminal who) (controlled.point index) -
          QuittingAbsorptionPath.chronologicalCoalitionCDF limit.law
            (quittingSingletonTerminal who) time := by
    exact
      QuittingAbsorptionPath.eventually_rate_mul_sub_lt_coalitionCDF_sub_of_pathRightDerivative_gt
        limit.law (quittingSingletonTerminal who) hrateDerivative
          controlled.point (tendsto_nhdsWithin_iff.mpr
            ⟨controlled.tendsto,
              Filter.Eventually.of_forall controlled.point_mem⟩)
  have hcollisionEventually : ∀ᶠ index in atTop,
      QuittingAbsorptionPath.chronologicalCollisionCDF limit.law
            (controlled.point index) -
          QuittingAbsorptionPath.chronologicalCollisionCDF limit.law time <
        (threshold * rate / 4) * (controlled.point index - time) := by
    apply
      eventually_collisionCDF_sub_lt_coefficient_mul_sub_of_controlledRightSequence
        certificates limit.law limit.law_tendsto hcontinuousTime controlled
    positivity
  let tailDiameter := fun index : ℕ ↦
    2 * quittingRewardBound reward *
      ((controlled.point index - time) / (1 - controlled.point index))
  have htailDiameter : Tendsto tailDiameter atTop (nhds 0) := by
    have htimeTendsto : Tendsto (fun _ : ℕ ↦ time) atTop (nhds time) :=
      tendsto_const_nhds
    have honeTendsto : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hnumerator : Tendsto
        (fun index ↦ controlled.point index - time) atTop (nhds 0) := by
      simpa only [sub_self] using controlled.tendsto.sub htimeTendsto
    have hdenominator : Tendsto
        (fun index ↦ 1 - controlled.point index) atTop
          (nhds (1 - time)) := honeTendsto.sub controlled.tendsto
    have hquotient := hnumerator.div hdenominator
      (sub_ne_zero.mpr htime_ne_one.symm)
    change Tendsto
      (fun index ↦ (controlled.point index - time) /
        (1 - controlled.point index)) atTop
      (nhds (0 / (1 - time))) at hquotient
    have hquotient' : Tendsto
        (fun index ↦ (controlled.point index - time) /
          (1 - controlled.point index)) atTop (nhds 0) := by
      simpa only [zero_div] using hquotient
    have hscaled := hquotient'.const_mul (2 * quittingRewardBound reward)
    rw [mul_zero] at hscaled
    exact hscaled
  have hdiameterEventually : ∀ᶠ index in atTop,
      tailDiameter index < gap / 2 :=
    htailDiameter.eventually_lt_const (half_pos hgap)
  obtain ⟨windowStart, hwindowStart⟩ := Filter.eventually_atTop.1
    (hsingletonEventually.and <|
      hcollisionEventually.and hdiameterEventually)
  let upper := fun index : ℕ ↦ controlled.point (windowStart + index)
  have hupper_mem (index : ℕ) : upper index ∈ Ioo time 1 :=
    controlled.point_mem (windowStart + index)
  have hupper_tendsto : Tendsto upper atTop (nhds time) := by
    apply controlled.tendsto.comp
    exact (strictMono_nat_of_lt_succ fun index ↦ by omega).tendsto_atTop
  have hwindow (index : ℕ) :
      rate * (upper index - time) <
          QuittingAbsorptionPath.chronologicalCoalitionCDF limit.law
              (quittingSingletonTerminal who) (upper index) -
            QuittingAbsorptionPath.chronologicalCoalitionCDF limit.law
              (quittingSingletonTerminal who) time ∧
        QuittingAbsorptionPath.chronologicalCollisionCDF limit.law
              (upper index) -
            QuittingAbsorptionPath.chronologicalCollisionCDF limit.law time <
          (threshold * rate / 4) * (upper index - time) ∧
        tailDiameter (windowStart + index) < gap / 2 := by
    exact hwindowStart (windowStart + index) (Nat.le_add_right _ _)
  let approximation := Classical.choice <|
    limit.nonempty_chronologicalPathTimeAdjacentCutLimit htime htime_ne_one
  let roots := fun sourceRank : ℕ ↦
    diagonal.completedRoots
      (limit.subsequence (approximation.rank sourceRank))
  let laws := fun sourceRank : ℕ ↦
    diagonal.chronologicalLaw
      (limit.subsequence (approximation.rank sourceRank))
  let sourceCertificates := fun sourceRank : ℕ ↦
    (diagonal.completion
      (limit.subsequence (approximation.rank sourceRank)))
        |>.finiteAbsorptionCertificate
  have hlaws : Tendsto laws atTop (nhds limit.law) := by
    exact limit.law_tendsto.comp
      approximation.rank_strictMono.tendsto_atTop
  have htailVector :=
    limit.tailVector_tendsto_absorptionPathPayoff_of_cumulativeSubsequenceCuts
      htime htime_ne_one approximation.rank approximation.cut
      approximation.rank_strictMono approximation.clock_tendsto
      approximation.cumulative_tendsto
  have htail := (tendsto_pi_nhds.mp htailVector) who
  have herror : Tendsto (fun sourceRank ↦
      diagonal.completedError
        (limit.subsequence (approximation.rank sourceRank))) atTop (nhds 0) :=
    diagonal.completedError_tendsto_zero.comp
      ((limit.subsequence_strictMono.comp approximation.rank_strictMono)
        |>.tendsto_atTop)
  have hsourceEventually (index : ℕ) : ∀ᶠ sourceRank in atTop,
      rate * (upper index - time) ≤
          QuittingAbsorptionPath.chronologicalCoalitionCDF
              (laws sourceRank) (quittingSingletonTerminal who) (upper index) -
            QuittingAbsorptionPath.chronologicalCoalitionCDF
              (laws sourceRank) (quittingSingletonTerminal who) time ∧
        QuittingAbsorptionPath.chronologicalCollisionCDF
              (laws sourceRank) (upper index) -
            QuittingAbsorptionPath.chronologicalCollisionCDF
              (laws sourceRank) time ≤
          threshold * rate * (upper index - time) / 2 ∧
        diagonal.completedError
              (limit.subsequence (approximation.rank sourceRank)) <
          gap * rate * (upper index - time) / 2 ∧
        |quittingRootSequenceTailVector reward (roots sourceRank)
              (approximation.cut sourceRank) who -
            QuittingAbsorptionPath.absorptionPathPayoff
              reward limit.absorptionPath time who| < gap / 2 ∧
        QuittingAbsorptionPath.quittingRootSequenceClock
              (roots sourceRank) (approximation.cut sourceRank) < upper index ∧
        2 * quittingRewardBound reward *
              ((upper index - min time
                  (QuittingAbsorptionPath.quittingRootSequenceClock
                    (roots sourceRank) (approximation.cut sourceRank))) /
                (1 - upper index)) < gap := by
    have hupperContinuous : ContinuousAt distribution (upper index) :=
      controlled.continuousAt (windowStart + index)
    have hsingletonUpper :=
      QuittingAbsorptionPath.tendsto_chronologicalCoalitionCDF_of_clockCDF_continuousAt
        hlaws (hupper_mem index).2.le hupperContinuous
          (quittingSingletonTerminal who)
    have hsingletonTime :=
      QuittingAbsorptionPath.tendsto_chronologicalCoalitionCDF_of_clockCDF_continuousAt
        hlaws htime.1.2 hcontinuousTime (quittingSingletonTerminal who)
    have hsingletonSource := hsingletonUpper.sub hsingletonTime
    have hsingletonLimit := hsingletonSource.eventually_const_lt (hwindow index).1
    have hcollisionUpper :=
      QuittingAbsorptionPath.tendsto_chronologicalCollisionCDF_of_clockCDF_continuousAt
        hlaws (hupper_mem index).2.le hupperContinuous
    have hcollisionTime :=
      QuittingAbsorptionPath.tendsto_chronologicalCollisionCDF_of_clockCDF_continuousAt
        hlaws htime.1.2 hcontinuousTime
    have hcollisionSource := hcollisionUpper.sub hcollisionTime
    have hwidth : 0 < upper index - time := sub_pos.mpr (hupper_mem index).1
    have hcollisionLimit :
        QuittingAbsorptionPath.chronologicalCollisionCDF limit.law
              (upper index) -
            QuittingAbsorptionPath.chronologicalCollisionCDF limit.law time <
          threshold * rate * (upper index - time) / 2 := by
      have hsmall := (hwindow index).2.1
      nlinarith [mul_pos hthreshold hrate]
    have hcollisionFinite :=
      hcollisionSource.eventually_lt_const hcollisionLimit
    have herrorTarget : 0 < gap * rate * (upper index - time) / 2 := by
      positivity
    have herrorFinite := herror.eventually_lt_const herrorTarget
    have htailFinite := htail.eventually
      (Metric.ball_mem_nhds _ (half_pos hgap))
    have hclockFinite := approximation.clock_tendsto.eventually_lt_const
      (hupper_mem index).1
    let localDiameter := fun sourceRank : ℕ ↦
      2 * quittingRewardBound reward *
        ((upper index - min time
            (QuittingAbsorptionPath.quittingRootSequenceClock
              (roots sourceRank) (approximation.cut sourceRank))) /
          (1 - upper index))
    have hminClock : Tendsto (fun sourceRank ↦ min time
        (QuittingAbsorptionPath.quittingRootSequenceClock
          (roots sourceRank) (approximation.cut sourceRank))) atTop
        (nhds time) := by
      have hclock : Tendsto (fun sourceRank ↦
          QuittingAbsorptionPath.quittingRootSequenceClock
            (roots sourceRank) (approximation.cut sourceRank)) atTop
          (nhds time) := by
        simpa only [roots] using approximation.clock_tendsto
      have htimeConst : Tendsto (fun _ : ℕ ↦ time) atTop (nhds time) :=
        tendsto_const_nhds
      simpa only [min_self] using htimeConst.min hclock
    have hlocalDiameter : Tendsto localDiameter atTop
        (nhds (tailDiameter (windowStart + index))) := by
      have hupperConst : Tendsto (fun _ : ℕ ↦ upper index) atTop
          (nhds (upper index)) := tendsto_const_nhds
      have honeConst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
        tendsto_const_nhds
      have hnumerator := hupperConst.sub hminClock
      have hdenominator : Tendsto (fun _ : ℕ ↦ 1 - upper index) atTop
          (nhds (1 - upper index)) := honeConst.sub hupperConst
      have hquotient := hnumerator.div hdenominator
        (sub_ne_zero.mpr (hupper_mem index).2.ne.symm)
      change Tendsto (fun sourceRank ↦
        (upper index - min time
          (QuittingAbsorptionPath.quittingRootSequenceClock
            (roots sourceRank) (approximation.cut sourceRank))) /
          (1 - upper index)) atTop
        (nhds ((upper index - time) / (1 - upper index))) at hquotient
      have hscaled := hquotient.const_mul (2 * quittingRewardBound reward)
      simpa only [localDiameter, tailDiameter, upper] using hscaled
    have hdiameterLimit : tailDiameter (windowStart + index) < gap :=
      (hwindow index).2.2.trans (half_lt_self hgap)
    have hdiameterFinite := hlocalDiameter.eventually_lt_const hdiameterLimit
    filter_upwards [hsingletonLimit, hcollisionFinite, herrorFinite,
      htailFinite, hclockFinite, hdiameterFinite] with sourceRank
      hsingletonRank hcollisionRank herrorRank htailRank hclockRank
      hdiameterRank
    exact ⟨hsingletonRank.le, hcollisionRank.le, herrorRank,
      by simpa only [Real.dist_eq] using htailRank,
      hclockRank, hdiameterRank⟩
  obtain ⟨sourceRank, hsourceRank_strict, hsource⟩ :=
    Filter.extraction_forall_of_eventually hsourceEventually
  let finalRank := approximation.rank ∘ sourceRank
  refine ⟨{
    rank := finalRank
    rank_strictMono := approximation.rank_strictMono.comp hsourceRank_strict
    upper := upper
    upper_mem := hupper_mem
    upper_tendsto := hupper_tendsto
    singleton_increment := ?_
    collision_increment := ?_
    nash_error := ?_
    stage_gap := ?_
  }⟩
  · intro index
    simpa only [finalRank, Function.comp_apply, laws] using (hsource index).1
  · intro index
    simpa only [finalRank, Function.comp_apply, laws] using (hsource index).2.1
  · intro index
    simpa only [finalRank, Function.comp_apply] using (hsource index).2.2.1
  · intro index stage hstage hstageClock hopponent
    let sourceIndex := sourceRank index
    let sourceRoots := roots sourceIndex
    let base := approximation.cut sourceIndex
    have hbaseClock :
        QuittingAbsorptionPath.quittingRootSequenceClock sourceRoots base ∈
          Icc (min time
            (QuittingAbsorptionPath.quittingRootSequenceClock sourceRoots base))
            (upper index) := by
      exact ⟨min_le_right _ _, (hsource index).2.2.2.2.1.le⟩
    have hstageClock' :
        QuittingAbsorptionPath.quittingRootSequenceClock sourceRoots stage ∈
          Icc (min time
            (QuittingAbsorptionPath.quittingRootSequenceClock sourceRoots base))
            (upper index) := by
      exact ⟨(min_le_left _ _).trans hstageClock.1.le, hstageClock.2⟩
    have htailDistance :=
      abs_quittingRootSequenceTailVector_sub_le_of_clocks_mem_Icc
        reward sourceRoots who stage base (hupper_mem index).2
        hstageClock' hbaseClock (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward)
    have htailDistance' :
        |quittingRootSequenceTailVector reward sourceRoots stage who -
            quittingRootSequenceTailVector reward sourceRoots base who| < gap :=
      htailDistance.trans_lt (hsource index).2.2.2.2.2
    have hbaseTail := (hsource index).2.2.2.1
    have htailLower :
        QuittingAbsorptionPath.absorptionPathPayoff
              reward limit.absorptionPath time who - 3 * gap / 2 <
          quittingRootSequenceTailVector reward sourceRoots stage who := by
      have hbaseLower := (abs_lt.mp hbaseTail).1
      have hstageLower := (abs_lt.mp htailDistance').1
      linarith
    have hquitEndpoint :=
      abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
        reward
        (quittingRootSequenceTailVector reward sourceRoots (stage + 1))
        (sourceRoots stage) who (quittingRewardBound reward)
        (abs_reward_le_quittingRewardBound reward)
    have hquitUpper :
        quittingRootQuitPayoff reward
              (quittingRootSequenceTailVector reward sourceRoots (stage + 1))
              (sourceRoots stage) who ≤
          reward (quittingSingletonTerminal who) who + gap := by
      have habsUpper := (abs_le.mp hquitEndpoint).2
      have hfactor : 0 ≤ 2 * quittingRewardBound reward :=
        mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)
      have hscaled :
          (2 * quittingRewardBound reward) *
              quittingRootOpponentAbsorptionMass (sourceRoots stage) who ≤
            (2 * quittingRewardBound reward) * threshold :=
        mul_le_mul_of_nonneg_left hopponent hfactor
      linarith
    change gap ≤
      quittingRootSequenceTailVector reward sourceRoots stage who -
        quittingRootQuitPayoff reward
          (quittingRootSequenceTailVector reward sourceRoots (stage + 1))
          (sourceRoots stage) who
    linarith

/-- Positive singleton rate rules out continuation payoff strictly above the
corresponding singleton reward. -/
theorem absorptionPathPayoff_le_singletonReward_of_pathRightDerivative_pos
    (limit : diagonal.ChronologicalLimit) (who : ι) {time : ℝ}
    (htime : time ∈ QuittingAbsorptionPath.pathTimes limit.path)
    (htime_ne_one : time ≠ 1)
    (hderivative : 0 <
      QuittingAbsorptionPath.pathRightDerivative limit.path time
        (quittingSingletonTerminal who)) :
    QuittingAbsorptionPath.absorptionPathPayoff
        reward limit.absorptionPath time who ≤
      reward (quittingSingletonTerminal who) who := by
  by_contra hnot
  have hstrict : reward (quittingSingletonTerminal who) who <
      QuittingAbsorptionPath.absorptionPathPayoff
        reward limit.absorptionPath time who := lt_of_not_ge hnot
  let difference :=
    QuittingAbsorptionPath.absorptionPathPayoff
        reward limit.absorptionPath time who -
      reward (quittingSingletonTerminal who) who
  let gap := difference / 4
  let rate :=
    QuittingAbsorptionPath.pathRightDerivative limit.path time
        (quittingSingletonTerminal who) / 2
  let threshold := gap / (2 * (quittingRewardBound reward + 1))
  have hdifference : 0 < difference := by
    dsimp only [difference]
    linarith
  have hgap : 0 < gap := by
    dsimp only [gap]
    positivity
  have hrate : 0 < rate := by
    dsimp only [rate]
    positivity
  have hrateDerivative : rate <
      QuittingAbsorptionPath.pathRightDerivative limit.path time
        (quittingSingletonTerminal who) := by
    dsimp only [rate]
    linarith
  have hbound := quittingRewardBound_nonneg reward
  have hdenominator : 0 < 2 * (quittingRewardBound reward + 1) := by
    positivity
  have hthreshold : 0 < threshold := by
    dsimp only [threshold]
    positivity
  have hmargin : reward (quittingSingletonTerminal who) who + 4 * gap ≤
      QuittingAbsorptionPath.absorptionPathPayoff
        reward limit.absorptionPath time who := by
    dsimp only [gap, difference]
    linarith
  have hcoefficient :
      2 * quittingRewardBound reward ≤
        2 * (quittingRewardBound reward + 1) := by linarith
  have hendpoint :
      2 * quittingRewardBound reward * threshold ≤ gap := by
    have hscaled :
        gap * (2 * quittingRewardBound reward) ≤
          gap * (2 * (quittingRewardBound reward + 1)) :=
      mul_le_mul_of_nonneg_left hcoefficient hgap.le
    have hdivided := div_le_div_of_nonneg_right hscaled hdenominator.le
    dsimp only [threshold]
    calc
      2 * quittingRewardBound reward *
          (gap / (2 * (quittingRewardBound reward + 1))) =
          (gap * (2 * quittingRewardBound reward)) /
            (2 * (quittingRewardBound reward + 1)) := by ring
      _ ≤ (gap * (2 * (quittingRewardBound reward + 1))) /
            (2 * (quittingRewardBound reward + 1)) := hdivided
      _ = gap := by field_simp
  let windows := Classical.choice <|
    limit.nonempty_positiveSingletonRefusalWindowSequence who htime
      htime_ne_one hrate hthreshold hgap hrateDerivative hmargin hendpoint
  exact windows.false hthreshold hgap

/-- Literal positive singleton-rate equality at every nonterminal clock point
of the actual chronological source limit. -/
theorem absorptionPathPayoff_eq_singletonReward_of_pathRightDerivative_pos
    (limit : diagonal.ChronologicalLimit) (who : ι) {time : ℝ}
    (htime : time ∈ QuittingAbsorptionPath.pathTimes limit.path)
    (htime_ne_one : time ≠ 1)
    (hderivative : 0 <
      QuittingAbsorptionPath.pathRightDerivative limit.path time
        (quittingSingletonTerminal who)) :
    QuittingAbsorptionPath.absorptionPathPayoff
        reward limit.absorptionPath time who =
      reward (quittingSingletonTerminal who) who := by
  apply le_antisymm
  · exact limit.absorptionPathPayoff_le_singletonReward_of_pathRightDerivative_pos
      who htime htime_ne_one hderivative
  · exact limit.singletonReward_le_absorptionPathPayoff who htime htime_ne_one

/-- The chronological path selected from the actual completed source is
sequentially perfect: jump rows are exact endpoint-Nash rows, every
nonterminal continuation payoff dominates the corresponding singleton reward,
and a positive singleton right derivative forces equality. -/
theorem isSequentiallyPerfectAbsorptionPath
    (limit : diagonal.ChronologicalLimit) :
    QuittingAbsorptionPath.IsSequentiallyPerfectAbsorptionPath
      reward limit.absorptionPath 0 := by
  intro who
  constructor
  · intro time htime htotal
    exact limit.jumpPlayerPerfect who htime htotal
  · intro time htime htime_ne_one
    constructor
    · simpa only [sub_zero, quittingSingletonTerminal] using
        limit.singletonReward_le_absorptionPathPayoff who htime htime_ne_one
    · intro hderivative
      simpa only [add_zero, quittingSingletonTerminal] using
        limit.absorptionPathPayoff_le_singletonReward_of_pathRightDerivative_pos
          who htime htime_ne_one hderivative

end ChronologicalLimit

end QuittingRootSequenceAbsorbingCompletionDiagonal

end GameTheory
