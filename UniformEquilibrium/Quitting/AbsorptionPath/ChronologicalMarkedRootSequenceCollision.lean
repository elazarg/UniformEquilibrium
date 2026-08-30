/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.ChronologicalMarkedRootSequenceJump
import UniformEquilibrium.Quitting.AbsorptionPath.CollisionConcentration

/-!
# Quadratic collision bounds for chronological root-sequence laws

The mass carried by nonsingleton coalitions in a finite chronological clock
window is quadratically small relative to the total clock increment.  The
estimate passes to weak limits at continuity endpoints of the limiting total
clock CDF.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Finset MeasureTheory Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Nonempty coalitions containing at least two players. -/
def chronologicalCollisionCoalitions :
    Finset {S : Finset ι // S.Nonempty} :=
  Finset.univ.filter fun coalition ↦ 2 ≤ coalition.1.card

/-- Cumulative chronological mass carried by nonsingleton coalitions. -/
def chronologicalCollisionCDF
    (law : ProbabilityMeasure (QuittingChronologicalEvent reward))
    (time : ℝ) : ℝ :=
  ∑ coalition ∈ chronologicalCollisionCoalitions,
    chronologicalCoalitionCDF law coalition time

omit [Nonempty ι] in
theorem sum_stageCoalitionMass_collision
    (roots : ℕ → ι → PMF Bool) (stage : ℕ) :
    (∑ coalition ∈ chronologicalCollisionCoalitions,
      quittingRootSequenceStageCoalitionMass roots stage coalition) =
      quittingRootSequenceSurvival roots stage *
        quittingRootCollisionMass (roots stage) := by
  rw [quittingRootCollisionMass_eq_sum_coalitionMass, Finset.mul_sum]
  apply Finset.sum_bij (fun coalition _ ↦ coalition.1)
  · intro coalition hcoalition
    simpa [chronologicalCollisionCoalitions] using hcoalition
  · intro first _ second _ heq
    exact Subtype.ext heq
  · intro coalition hcoalition
    have hcard : 2 ≤ coalition.card := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hcoalition
    let marked : {S : Finset ι // S.Nonempty} :=
      ⟨coalition, Finset.card_pos.mp (zero_lt_two.trans_le hcard)⟩
    refine ⟨marked, ?_, rfl⟩
    simpa [chronologicalCollisionCoalitions, marked] using hcard
  · intro coalition _
    rfl

omit [Nonempty ι] in
theorem sum_stageCoalitionMass_eq_survival_mul_absorptionMass
    (roots : ℕ → ι → PMF Bool) (stage : ℕ) :
    (∑ coalition : {S : Finset ι // S.Nonempty},
      quittingRootSequenceStageCoalitionMass roots stage coalition) =
      quittingRootSequenceSurvival roots stage *
        quittingRootAbsorptionMass (roots stage) := by
  rw [sum_quittingRootSequenceStageCoalitionMass,
    quittingRootSequenceSurvival_succ]
  unfold quittingRootAbsorptionMass
  ring

namespace QuittingFiniteRootSequenceAbsorption

variable {roots : ℕ → ι → PMF Bool}

omit [Nonempty ι] in
private theorem value_sub_value_eq_sum_Ioc
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {lower upper : ℝ} (hlowerUpper : lower ≤ upper)
    (coalition : {S : Finset ι // S.Nonempty}) :
    certificate.value upper coalition - certificate.value lower coalition =
      ∑ stage ∈ Finset.range (certificate.cutoff + 1),
        if quittingRootSequenceClock roots stage ∈ Ioc lower upper then
          quittingRootSequenceStageCoalitionMass roots stage coalition else 0 := by
  unfold value
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro stage _
  by_cases hlower : quittingRootSequenceClock roots stage ≤ lower
  · rw [if_pos hlower, if_pos (hlower.trans hlowerUpper)]
    simp [hlower]
  · by_cases hupper : quittingRootSequenceClock roots stage ≤ upper
    · rw [if_neg hlower, if_pos hupper]
      simp [hlower, hupper]
    · rw [if_neg hlower, if_neg hupper]
      simp [hupper]

omit [Nonempty ι] in
/-- Exact finite-window expansion of the nonsingleton chronological mass. -/
theorem chronologicalCollisionCDF_sub_eq_sum
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {lower upper : ℝ} (hlowerUpper : lower ≤ upper)
    (hupper : upper ≤ 1) :
    chronologicalCollisionCDF (certificate.chronologicalLaw reward) upper -
        chronologicalCollisionCDF (certificate.chronologicalLaw reward) lower =
      ∑ stage ∈ Finset.range (certificate.cutoff + 1),
        if quittingRootSequenceClock roots stage ∈ Ioc lower upper then
          quittingRootSequenceSurvival roots stage *
            quittingRootCollisionMass (roots stage) else 0 := by
  unfold chronologicalCollisionCDF
  rw [← Finset.sum_sub_distrib]
  simp_rw [chronologicalCoalitionCDF_eq_clockCoalitionEvent_real
      (certificate.chronologicalLaw reward) _ hupper,
    certificate.chronologicalLaw_clockCoalitionEvent_real_eq_value]
  simp_rw [chronologicalCoalitionCDF_eq_clockCoalitionEvent_real
      (certificate.chronologicalLaw reward) _ (hlowerUpper.trans hupper),
    certificate.chronologicalLaw_clockCoalitionEvent_real_eq_value,
    certificate.value_sub_value_eq_sum_Ioc hlowerUpper]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro stage _
  by_cases hclock :
      quittingRootSequenceClock roots stage ∈ Ioc lower upper
  · simp only [if_pos hclock]
    exact sum_stageCoalitionMass_collision roots stage
  · simp [hclock]

omit [Nonempty ι] in
/-- Exact finite-window expansion of the total chronological clock mass. -/
theorem chronologicalClockCDF_sub_eq_sum
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {lower upper : ℝ} (hlowerUpper : lower ≤ upper) :
    chronologicalClockCDF (certificate.chronologicalLaw reward) upper -
        chronologicalClockCDF (certificate.chronologicalLaw reward) lower =
      ∑ stage ∈ Finset.range (certificate.cutoff + 1),
        if quittingRootSequenceClock roots stage ∈ Ioc lower upper then
          quittingRootSequenceSurvival roots stage *
            quittingRootAbsorptionMass (roots stage) else 0 := by
  simp_rw [chronologicalClockCDF_eq_clockEvent_real,
    certificate.chronologicalLaw_clockEvent_real_eq_pathTotal]
  change (∑ coalition, certificate.value upper coalition) -
      (∑ coalition, certificate.value lower coalition) = _
  rw [← Finset.sum_sub_distrib]
  simp_rw [certificate.value_sub_value_eq_sum_Ioc hlowerUpper]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro stage _
  by_cases hclock :
      quittingRootSequenceClock roots stage ∈ Ioc lower upper
  · simp only [if_pos hclock]
    exact sum_stageCoalitionMass_eq_survival_mul_absorptionMass roots stage
  · simp [hclock]

omit [Nonempty ι] in
/-- The finite nonsingleton mass in a chronological clock window is
quadratically bounded by its total clock increment. -/
theorem one_sub_upper_mul_collisionCDF_sub_le_choose_mul_clockCDF_sub_sq
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {lower upper : ℝ} (hlowerUpper : lower ≤ upper)
    (hupper : upper < 1) :
    (1 - upper) *
        (chronologicalCollisionCDF
            (certificate.chronologicalLaw reward) upper -
          chronologicalCollisionCDF
            (certificate.chronologicalLaw reward) lower) ≤
      (Fintype.card ι).choose 2 *
        (chronologicalClockCDF
            (certificate.chronologicalLaw reward) upper -
          chronologicalClockCDF
            (certificate.chronologicalLaw reward) lower) ^ 2 := by
  rw [certificate.chronologicalCollisionCDF_sub_eq_sum
      hlowerUpper hupper.le,
    certificate.chronologicalClockCDF_sub_eq_sum hlowerUpper]
  let collision := fun stage : ℕ ↦
    if quittingRootSequenceClock roots stage ∈ Ioc lower upper then
      quittingRootSequenceSurvival roots stage *
        quittingRootCollisionMass (roots stage) else 0
  let total := fun stage : ℕ ↦
    if quittingRootSequenceClock roots stage ∈ Ioc lower upper then
      quittingRootSequenceSurvival roots stage *
        quittingRootAbsorptionMass (roots stage) else 0
  have htotal_nonneg (stage : ℕ) : 0 ≤ total stage := by
    dsimp only [total]
    split
    · exact mul_nonneg (quittingRootSequenceSurvival_nonneg roots stage)
        (quittingRootAbsorptionMass_nonneg (roots stage))
    · exact le_rfl
  have hstage (stage : ℕ) :
      (1 - upper) * collision stage ≤
        (Fintype.card ι).choose 2 * (total stage) ^ 2 := by
    dsimp only [collision, total]
    by_cases hclock :
        quittingRootSequenceClock roots stage ∈ Ioc lower upper
    · simp only [if_pos hclock]
      let survival := quittingRootSequenceSurvival roots stage
      let collisionMass := quittingRootCollisionMass (roots stage)
      let absorptionMass := quittingRootAbsorptionMass (roots stage)
      have hsurvival : 0 ≤ survival :=
        quittingRootSequenceSurvival_nonneg roots stage
      have hcollision : 0 ≤ collisionMass :=
        quittingRootCollisionMass_nonneg (roots stage)
      have hsurvivalLower : 1 - upper ≤ survival := by
        have hclockUpper := hclock.2
        unfold quittingRootSequenceClock at hclockUpper
        dsimp only [survival]
        linarith
      have hroot : collisionMass ≤
          (Fintype.card ι).choose 2 * absorptionMass ^ 2 := by
        exact quittingRootCollisionMass_le_choose_card_mul_absorption_sq
          (roots stage)
      calc
        (1 - upper) * (survival * collisionMass) =
            survival * ((1 - upper) * collisionMass) := by ring
        _ ≤ survival * (survival * collisionMass) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hsurvivalLower hcollision) hsurvival
        _ = survival ^ 2 * collisionMass := by ring
        _ ≤ survival ^ 2 *
            ((Fintype.card ι).choose 2 * absorptionMass ^ 2) := by
          exact mul_le_mul_of_nonneg_left hroot (sq_nonneg survival)
        _ = (Fintype.card ι).choose 2 *
            (survival * absorptionMass) ^ 2 := by ring
    · simp [hclock]
  change (1 - upper) *
      (∑ stage ∈ Finset.range (certificate.cutoff + 1), collision stage) ≤
    (Fintype.card ι).choose 2 *
      (∑ stage ∈ Finset.range (certificate.cutoff + 1), total stage) ^ 2
  calc
    (1 - upper) *
        (∑ stage ∈ Finset.range (certificate.cutoff + 1), collision stage) =
        ∑ stage ∈ Finset.range (certificate.cutoff + 1),
          (1 - upper) * collision stage := by rw [Finset.mul_sum]
    _ ≤ ∑ stage ∈ Finset.range (certificate.cutoff + 1),
        (Fintype.card ι).choose 2 * (total stage) ^ 2 := by
      exact Finset.sum_le_sum fun stage _ ↦ hstage stage
    _ = (Fintype.card ι).choose 2 *
        (∑ stage ∈ Finset.range (certificate.cutoff + 1),
          (total stage) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (Fintype.card ι).choose 2 *
        (∑ stage ∈ Finset.range (certificate.cutoff + 1), total stage) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_sq_le_sq_sum_of_nonneg fun stage _ ↦
          htotal_nonneg stage
      · positivity

end QuittingFiniteRootSequenceAbsorption

omit [Nonempty ι] in
/-- Continuity of the total clock CDF forces continuity of every coalition
coordinate CDF at the same path time. -/
theorem continuousAt_chronologicalCoalitionCDF_of_clockCDF
    (law : ProbabilityMeasure (QuittingChronologicalEvent reward))
    {time : ℝ} (htime : time ≤ 1)
    (hcontinuous : ContinuousAt (chronologicalClockCDF law) time)
    (coalition : {S : Finset ι // S.Nonempty}) :
    ContinuousAt (chronologicalCoalitionCDF law coalition) time := by
  have hclockSingleton :
      (chronologicalClockLaw law : Measure ℝ) ({time} : Set ℝ) = 0 := by
    change ContinuousAt
      (ProbabilityTheory.cdf (chronologicalClockLaw law : Measure ℝ)) time
      at hcontinuous
    rw [← ProbabilityTheory.measure_cdf
        (chronologicalClockLaw law : Measure ℝ),
      StieltjesFunction.measure_singleton,
      hcontinuous.continuousWithinAt.leftLim_eq, sub_self,
      ENNReal.ofReal_zero]
  have hclockFiber :
      (law : Measure (QuittingChronologicalEvent reward))
        {event | chronologicalEventClock event = time} = 0 := by
    unfold chronologicalClockLaw at hclockSingleton
    change Measure.map chronologicalEventClock
      (law : Measure (QuittingChronologicalEvent reward)) {time} = 0
      at hclockSingleton
    rw [Measure.map_apply continuous_chronologicalEventClock.measurable
      (measurableSet_singleton time)] at hclockSingleton
    rw [show {event : QuittingChronologicalEvent reward |
        chronologicalEventClock event = time} =
      chronologicalEventClock ⁻¹' ({time} : Set ℝ) by
        ext event
        simp]
    exact hclockSingleton
  have hcoalitionFiber :
      (law : Measure (QuittingChronologicalEvent reward))
        (chronologicalClockCoalitionFiber time coalition) = 0 := by
    exact measure_mono_null
      (show chronologicalClockCoalitionFiber
          (reward := reward) time coalition ⊆
          {event | chronologicalEventClock event = time} by
        intro event hevent
        exact hevent.1)
      hclockFiber
  have hjump :=
    pathJump_chronologicalCadlagPath_eq_clockCoalitionFiber_real
      law time htime coalition
  unfold Measure.real at hjump
  rw [hcoalitionFiber, ENNReal.toReal_zero] at hjump
  change chronologicalCoalitionCDF law coalition time -
      Function.leftLim (chronologicalCoalitionCDF law coalition) time = 0
    at hjump
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · apply (ProbabilityTheory.monotone_cdf
      (chronologicalCoalitionClockLaw law coalition))
        |>.continuousWithinAt_Iio_iff_leftLim_eq.mpr
    exact (sub_eq_zero.mp hjump).symm
  · exact (ProbabilityTheory.cdf
      (chronologicalCoalitionClockLaw law coalition)).right_continuous time
        |>.mono Ioi_subset_Ici_self

omit [Nonempty ι] in
/-- Coalition CDF coordinates converge at continuity points of the limiting
total clock CDF. -/
theorem tendsto_chronologicalCoalitionCDF_of_clockCDF_continuousAt
    {index : Type*} {limitFilter : Filter index} [limitFilter.NeBot]
    {laws : index → ProbabilityMeasure (QuittingChronologicalEvent reward)}
    {law : ProbabilityMeasure (QuittingChronologicalEvent reward)}
    (hlaw : Tendsto laws limitFilter (nhds law))
    {time : ℝ} (htime : time ≤ 1)
    (hcontinuous : ContinuousAt (chronologicalClockCDF law) time)
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun rank ↦ chronologicalCoalitionCDF
      (laws rank) coalition time) limitFilter
      (nhds (chronologicalCoalitionCDF law coalition time)) := by
  let coordinateLaws := fun rank ↦
    chronologicalCoalitionClockLaw (laws rank) coalition
  have hcoordinateLaws : Tendsto coordinateLaws limitFilter
      (nhds (chronologicalCoalitionClockLaw law coalition)) := by
    exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      laws law hlaw (continuous_chronologicalCoalitionClock coalition)
  exact MathUE.HasClockGap.cdf_tendsto_of_tendsto_of_continuousAt
    hcoordinateLaws
    (continuousAt_chronologicalCoalitionCDF_of_clockCDF
      law htime hcontinuous coalition)

omit [DecidableEq ι] [Nonempty ι] in
/-- The total clock CDF converges at each continuity point of its weak
limit. -/
theorem tendsto_chronologicalClockCDF_of_continuousAt
    {index : Type*} {limitFilter : Filter index} [limitFilter.NeBot]
    {laws : index → ProbabilityMeasure (QuittingChronologicalEvent reward)}
    {law : ProbabilityMeasure (QuittingChronologicalEvent reward)}
    (hlaw : Tendsto laws limitFilter (nhds law))
    {time : ℝ} (hcontinuous : ContinuousAt
      (chronologicalClockCDF law) time) :
    Tendsto (fun rank ↦ chronologicalClockCDF (laws rank) time)
      limitFilter (nhds (chronologicalClockCDF law time)) := by
  let clockLaws := fun rank ↦ chronologicalClockLaw (laws rank)
  have hclockLaws : Tendsto clockLaws limitFilter
      (nhds (chronologicalClockLaw law)) := by
    exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      laws law hlaw continuous_chronologicalEventClock
  exact MathUE.HasClockGap.cdf_tendsto_of_tendsto_of_continuousAt
    hclockLaws hcontinuous

omit [Nonempty ι] in
/-- The nonsingleton chronological CDF converges at continuity points of the
limiting total clock CDF. -/
theorem tendsto_chronologicalCollisionCDF_of_clockCDF_continuousAt
    {index : Type*} {limitFilter : Filter index} [limitFilter.NeBot]
    {laws : index → ProbabilityMeasure (QuittingChronologicalEvent reward)}
    {law : ProbabilityMeasure (QuittingChronologicalEvent reward)}
    (hlaw : Tendsto laws limitFilter (nhds law))
    {time : ℝ} (htime : time ≤ 1)
    (hcontinuous : ContinuousAt (chronologicalClockCDF law) time) :
    Tendsto (fun rank ↦ chronologicalCollisionCDF (laws rank) time)
      limitFilter (nhds (chronologicalCollisionCDF law time)) := by
  unfold chronologicalCollisionCDF
  exact tendsto_finsetSum chronologicalCollisionCoalitions fun coalition _ ↦
    tendsto_chronologicalCoalitionCDF_of_clockCDF_continuousAt
      hlaw htime hcontinuous coalition

omit [Nonempty ι] in
/-- The finite quadratic collision-window inequality is closed under weak
convergence at fixed continuity endpoints of the limiting clock CDF. -/
theorem one_sub_upper_mul_collisionCDF_sub_le_choose_mul_clockCDF_sub_sq_of_tendsto
    {roots : ℕ → ℕ → ι → PMF Bool}
    (certificates : ∀ rank,
      QuittingFiniteRootSequenceAbsorption (roots rank))
    (law : ProbabilityMeasure (QuittingChronologicalEvent reward))
    (hlaw : Tendsto
      (fun rank ↦ (certificates rank).chronologicalLaw reward)
      atTop (nhds law))
    {lower upper : ℝ} (hlowerUpper : lower ≤ upper)
    (hupper : upper < 1)
    (hlowerContinuous : ContinuousAt (chronologicalClockCDF law) lower)
    (hupperContinuous : ContinuousAt (chronologicalClockCDF law) upper) :
    (1 - upper) *
        (chronologicalCollisionCDF law upper -
          chronologicalCollisionCDF law lower) ≤
      (Fintype.card ι).choose 2 *
        (chronologicalClockCDF law upper -
          chronologicalClockCDF law lower) ^ 2 := by
  have hcollisionLower :=
    tendsto_chronologicalCollisionCDF_of_clockCDF_continuousAt
      hlaw (hlowerUpper.trans hupper.le) hlowerContinuous
  have hcollisionUpper :=
    tendsto_chronologicalCollisionCDF_of_clockCDF_continuousAt
      hlaw hupper.le hupperContinuous
  have hclockLower := tendsto_chronologicalClockCDF_of_continuousAt
    hlaw hlowerContinuous
  have hclockUpper := tendsto_chronologicalClockCDF_of_continuousAt
    hlaw hupperContinuous
  apply le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul (hcollisionUpper.sub hcollisionLower))
    (tendsto_const_nhds.mul ((hclockUpper.sub hclockLower).pow 2))
  exact Filter.Eventually.of_forall fun rank ↦
    (certificates rank)
      |>.one_sub_upper_mul_collisionCDF_sub_le_choose_mul_clockCDF_sub_sq
        hlowerUpper hupper

end GameTheory.QuittingAbsorptionPath
