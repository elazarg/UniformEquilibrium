/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.ChronologicalMarkedRootSequenceLaw

/-!
# Jumps and dominant clock windows of chronological root-sequence laws

The jump of a chronological CDF coordinate is exactly the marked-law mass on
the corresponding clock--coalition fiber.  For a finite root sequence, any
open clock window carrying more mass than its width contains one positive
stage which accounts for the whole window up to a simultaneous nonnegative
coalition residual smaller than the window width.

This is finite source algebra.  It does not take weak limits, select limiting
roots, or prove absorption-path axioms A3--A4.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Finset MeasureTheory Set
open scoped ENNReal Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Events occurring at one exact clock and carrying one coalition mark. -/
def chronologicalClockCoalitionFiber
    (time : ℝ) (coalition : {S : Finset ι // S.Nonempty}) :
    Set (QuittingChronologicalEvent reward) :=
  {event | chronologicalEventClock event = time} ∩
    chronologicalCoalitionEvent coalition

/-- Events whose clocks lie in one open interval. -/
def chronologicalOpenClockWindow (lower upper : ℝ) :
    Set (QuittingChronologicalEvent reward) :=
  chronologicalEventClock ⁻¹' Ioo lower upper

/-- Events in one open clock interval carrying one coalition mark. -/
def chronologicalOpenClockCoalitionWindow
    (lower upper : ℝ) (coalition : {S : Finset ι // S.Nonempty}) :
    Set (QuittingChronologicalEvent reward) :=
  chronologicalOpenClockWindow lower upper ∩
    chronologicalCoalitionEvent coalition

omit [DecidableEq ι] [Nonempty ι] in
theorem isClosed_chronologicalClockCoalitionFiber
    (time : ℝ) (coalition : {S : Finset ι // S.Nonempty}) :
    IsClosed (chronologicalClockCoalitionFiber
      (reward := reward) time coalition) := by
  exact (isClosed_singleton.preimage continuous_chronologicalEventClock).inter
    (isClopen_chronologicalCoalitionEvent coalition).1

omit [DecidableEq ι] [Nonempty ι] in
theorem measurableSet_chronologicalClockCoalitionFiber
    (time : ℝ) (coalition : {S : Finset ι // S.Nonempty}) :
    MeasurableSet (chronologicalClockCoalitionFiber
      (reward := reward) time coalition) :=
  (isClosed_chronologicalClockCoalitionFiber time coalition).measurableSet

omit [DecidableEq ι] [Nonempty ι] in
theorem isOpen_chronologicalOpenClockWindow (lower upper : ℝ) :
    IsOpen (chronologicalOpenClockWindow
      (reward := reward) lower upper) :=
  isOpen_Ioo.preimage continuous_chronologicalEventClock

omit [DecidableEq ι] [Nonempty ι] in
theorem measurableSet_chronologicalOpenClockWindow (lower upper : ℝ) :
    MeasurableSet (chronologicalOpenClockWindow
      (reward := reward) lower upper) :=
  (isOpen_chronologicalOpenClockWindow lower upper).measurableSet

omit [DecidableEq ι] [Nonempty ι] in
theorem isOpen_chronologicalOpenClockCoalitionWindow
    (lower upper : ℝ) (coalition : {S : Finset ι // S.Nonempty}) :
    IsOpen (chronologicalOpenClockCoalitionWindow
      (reward := reward) lower upper coalition) :=
  (isOpen_chronologicalOpenClockWindow lower upper).inter
    (isClopen_chronologicalCoalitionEvent coalition).2

omit [DecidableEq ι] [Nonempty ι] in
theorem measurableSet_chronologicalOpenClockCoalitionWindow
    (lower upper : ℝ) (coalition : {S : Finset ι // S.Nonempty}) :
    MeasurableSet (chronologicalOpenClockCoalitionWindow
      (reward := reward) lower upper coalition) :=
  (isOpen_chronologicalOpenClockCoalitionWindow
    lower upper coalition).measurableSet

omit [Nonempty ι] in
private theorem chronologicalCoalitionClock_preimage_singleton
    (time : ℝ) (htime : time ≤ 1)
    (coalition : {S : Finset ι // S.Nonempty}) :
    chronologicalCoalitionClock (reward := reward) coalition ⁻¹' {time} =
      chronologicalClockCoalitionFiber time coalition := by
  ext event
  unfold chronologicalCoalitionClock chronologicalClockCoalitionFiber
    chronologicalCoalitionEvent
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff]
  by_cases hmark : event.2.2.2 = ⟨coalition⟩
  · simp [hmark]
  · simp [hmark, show (2 : ℝ) ≠ time by linarith]

omit [Nonempty ι] in
/-- On the path interval, a chronological CDF jump is exactly the mass of
the corresponding exact clock--coalition fiber. -/
theorem pathJump_chronologicalCadlagPath_eq_clockCoalitionFiber_real
    (law : ProbabilityMeasure (QuittingChronologicalEvent reward))
    (time : ℝ) (htime : time ≤ 1)
    (coalition : {S : Finset ι // S.Nonempty}) :
    pathJump (chronologicalCadlagPath law) time coalition =
      (law : Measure (QuittingChronologicalEvent reward)).real
        (chronologicalClockCoalitionFiber time coalition) := by
  let clockLaw := chronologicalCoalitionClockLaw law coalition
  have hnonneg :
      0 ≤ ProbabilityTheory.cdf (clockLaw : Measure ℝ) time -
        Function.leftLim (ProbabilityTheory.cdf
          (clockLaw : Measure ℝ)) time := by
    exact sub_nonneg.mpr
      (ProbabilityTheory.monotone_cdf (clockLaw : Measure ℝ)
        |>.leftLim_le le_rfl)
  change ProbabilityTheory.cdf (clockLaw : Measure ℝ) time -
      Function.leftLim (ProbabilityTheory.cdf
        (clockLaw : Measure ℝ)) time = _
  rw [← ENNReal.toReal_ofReal hnonneg,
    ← StieltjesFunction.measure_singleton,
    ProbabilityTheory.measure_cdf]
  unfold clockLaw chronologicalCoalitionClockLaw
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ProbabilityMeasure.map_apply _ _ (A := {time})
      (measurableSet_singleton time),
    chronologicalCoalitionClock_preimage_singleton time htime coalition]
  exact ProbabilityMeasure.measureReal_eq_coe_coeFn law _

omit [DecidableEq ι] [Nonempty ι] in
/-- Coalition marks partition every open clock window. -/
theorem sum_openClockCoalitionWindow_real_eq_openClockWindow_real
    (law : ProbabilityMeasure (QuittingChronologicalEvent reward))
    (lower upper : ℝ) :
    (∑ coalition : {S : Finset ι // S.Nonempty},
      (law : Measure (QuittingChronologicalEvent reward)).real
        (chronologicalOpenClockCoalitionWindow lower upper coalition)) =
      (law : Measure (QuittingChronologicalEvent reward)).real
        (chronologicalOpenClockWindow lower upper) := by
  let events := fun coalition : {S : Finset ι // S.Nonempty} ↦
    chronologicalOpenClockCoalitionWindow
      (reward := reward) lower upper coalition
  have hdisjoint : Set.PairwiseDisjoint
      ((Finset.univ : Finset {S : Finset ι // S.Nonempty}) :
        Set {S : Finset ι // S.Nonempty}) events := by
    intro first _ second _ hne
    change Disjoint (events first) (events second)
    rw [Set.disjoint_left]
    intro event hfirst hsecond
    apply hne
    have hmark :
        (⟨first⟩ : QuittingChronologicalCoalitionMark ι) = ⟨second⟩ :=
      hfirst.2.symm.trans hsecond.2
    exact congrArg QuittingChronologicalCoalitionMark.coalition hmark
  have hunion :
      (⋃ coalition ∈ (Finset.univ :
        Finset {S : Finset ι // S.Nonempty}), events coalition) =
        chronologicalOpenClockWindow lower upper := by
    ext event
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_const]
    constructor
    · rintro ⟨coalition, hcoalition⟩
      exact hcoalition.1
    · intro hclock
      refine ⟨event.2.2.2.coalition, hclock, ?_⟩
      change event.2.2.2 = ⟨event.2.2.2.coalition⟩
      cases event.2.2.2
      rfl
  have hmeasure := measure_biUnion_finset hdisjoint
    (fun coalition _ ↦
      (measurableSet_chronologicalOpenClockCoalitionWindow
        (reward := reward) lower upper coalition))
    (μ := (law : Measure (QuittingChronologicalEvent reward)))
  rw [hunion] at hmeasure
  unfold Measure.real
  calc
    (∑ coalition : {S : Finset ι // S.Nonempty},
        ((law : Measure (QuittingChronologicalEvent reward))
          (events coalition)).toReal) =
        (∑ coalition : {S : Finset ι // S.Nonempty},
          (law : Measure (QuittingChronologicalEvent reward))
            (events coalition)).toReal := by
      rw [ENNReal.toReal_sum]
      intro coalition _
      exact measure_ne_top _ _
    _ = ((law : Measure (QuittingChronologicalEvent reward))
        (chronologicalOpenClockWindow lower upper)).toReal :=
      congrArg ENNReal.toReal hmeasure.symm

namespace QuittingFiniteRootSequenceAbsorption

variable {roots : ℕ → ι → PMF Bool}

omit [Nonempty ι] in
/-- One coalition's mass in a finite chronological open clock window is the
sum of its canonical stage masses whose pre-stage clocks lie in the window. -/
theorem chronologicalLaw_openClockCoalitionWindow_real_eq_sum
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    (lower upper : ℝ)
    (coalition : {S : Finset ι // S.Nonempty}) :
    (certificate.chronologicalLaw reward :
      Measure (QuittingChronologicalEvent reward)).real
        (chronologicalOpenClockCoalitionWindow lower upper coalition) =
      ∑ stage ∈ Finset.range (certificate.cutoff + 1),
        if quittingRootSequenceClock roots stage ∈ Ioo lower upper then
          quittingRootSequenceStageCoalitionMass roots stage coalition else 0 := by
  change ((PMF.map (certificate.chronologicalEventAt reward)
    certificate.chronologicalIndexPMF).toMeasure
      (chronologicalOpenClockCoalitionWindow lower upper coalition)).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _
    (measurable_of_finite _)
    (measurableSet_chronologicalOpenClockCoalitionWindow
      lower upper coalition)]
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · rw [show (∑ index : certificate.ChronologicalIndex,
        ((certificate.chronologicalEventAt reward ⁻¹'
          chronologicalOpenClockCoalitionWindow lower upper coalition).indicator
            certificate.chronologicalIndexPMF index).toReal) =
        ∑ stage : Fin (certificate.cutoff + 1),
          ∑ mark : QuittingChronologicalCoalitionMark ι,
            ((certificate.chronologicalEventAt reward ⁻¹'
              chronologicalOpenClockCoalitionWindow lower upper coalition).indicator
                certificate.chronologicalIndexPMF (stage, mark)).toReal by
      rw [Fintype.sum_prod_type]]
    rw [← Fin.sum_univ_eq_sum_range
      (fun stage : ℕ ↦
        if quittingRootSequenceClock roots stage ∈ Ioo lower upper then
          quittingRootSequenceStageCoalitionMass roots stage coalition else 0)
      (certificate.cutoff + 1)]
    apply Finset.sum_congr rfl
    intro stage _
    rw [Fintype.sum_eq_single ⟨coalition⟩]
    · by_cases hclock :
          quittingRootSequenceClock roots stage ∈ Ioo lower upper
      · have hmem : (stage, ⟨coalition⟩) ∈
            certificate.chronologicalEventAt reward ⁻¹'
              chronologicalOpenClockCoalitionWindow
                lower upper coalition := by
          exact ⟨hclock, rfl⟩
        rw [Set.indicator_of_mem hmem,
          certificate.chronologicalIndexPMF_toReal, if_pos hclock]
        rfl
      · have hnot : (stage, ⟨coalition⟩) ∉
            certificate.chronologicalEventAt reward ⁻¹'
              chronologicalOpenClockCoalitionWindow
                lower upper coalition := by
          intro hmem
          exact hclock hmem.1
        rw [Set.indicator_of_notMem hnot, ENNReal.toReal_zero, if_neg hclock]
    · intro mark hne
      have hcoalition : mark.coalition ≠ coalition := by
        intro heq
        apply hne
        cases mark
        simp_all
      have hnot : (stage, mark) ∉
          certificate.chronologicalEventAt reward ⁻¹'
            chronologicalOpenClockCoalitionWindow lower upper coalition := by
        intro hmem
        have hmark := hmem.2
        change mark = ⟨coalition⟩ at hmark
        exact hne hmark
      rw [Set.indicator_of_notMem hnot]
      exact ENNReal.toReal_zero
  · intro index _
    simp only [Set.indicator]
    split
    · exact PMF.apply_ne_top certificate.chronologicalIndexPMF index
    · exact ENNReal.zero_ne_top

omit [Nonempty ι] in
/-- The total finite chronological mass in an open clock window is the sum
of the total masses of the source stages whose clocks lie in that window. -/
theorem chronologicalLaw_openClockWindow_real_eq_sum
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    (lower upper : ℝ) :
    (certificate.chronologicalLaw reward :
      Measure (QuittingChronologicalEvent reward)).real
        (chronologicalOpenClockWindow lower upper) =
      ∑ stage ∈ Finset.range (certificate.cutoff + 1),
        if quittingRootSequenceClock roots stage ∈ Ioo lower upper then
          ∑ coalition : {S : Finset ι // S.Nonempty},
            quittingRootSequenceStageCoalitionMass roots stage coalition
        else 0 := by
  rw [← sum_openClockCoalitionWindow_real_eq_openClockWindow_real]
  simp_rw [certificate.chronologicalLaw_openClockCoalitionWindow_real_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro stage _
  by_cases hclock :
      quittingRootSequenceClock roots stage ∈ Ioo lower upper
  · simp [hclock]
  · simp [hclock]

omit [Nonempty ι] in
private theorem sum_range_stageTotal_eq_clock
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ) :
    (∑ stage ∈ Finset.range horizon,
      ∑ coalition : {S : Finset ι // S.Nonempty},
        quittingRootSequenceStageCoalitionMass roots stage coalition) =
      quittingRootSequenceClock roots horizon := by
  rw [Finset.sum_comm]
  exact sum_quittingRootSequenceCumulativeCoalitionMass roots horizon

/-- A single positive source stage accounts for an open chronological clock
window up to simultaneous nonnegative coalition residuals. -/
structure QuittingFiniteDominantClockWindowStage
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ℝ) where
  stage : ℕ
  stage_le_cutoff : stage ≤ certificate.cutoff
  clock_mem : quittingRootSequenceClock roots stage ∈ Ioo lower upper
  stageTotal_pos :
    0 < ∑ coalition : {S : Finset ι // S.Nonempty},
      quittingRootSequenceStageCoalitionMass roots stage coalition
  residual : {S : Finset ι // S.Nonempty} → ℝ
  window_eq_stage_add_residual : ∀ coalition,
    (certificate.chronologicalLaw reward :
      Measure (QuittingChronologicalEvent reward)).real
        (chronologicalOpenClockCoalitionWindow lower upper coalition) =
      quittingRootSequenceStageCoalitionMass roots stage coalition +
        residual coalition
  residual_nonneg : ∀ coalition, 0 ≤ residual coalition
  sum_residual_lt_width :
    (∑ coalition, residual coalition) < upper - lower
  cumulative_eq_lowerCDF_add_residual : ∀ coalition,
    quittingRootSequenceCumulativeCoalitionMass roots stage coalition =
      chronologicalCoalitionCDF (certificate.chronologicalLaw reward)
          coalition lower + residual coalition

omit [Nonempty ι] in
/-- If an open finite clock window carries more mass than its width, its
rightmost positive stage dominates every coalition coordinate at once. -/
theorem exists_dominantClockWindowStage_of_width_lt_real
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {lower upper : ℝ} (hlowerUpper : lower < upper)
    (hwidth : upper - lower <
      (certificate.chronologicalLaw reward :
        Measure (QuittingChronologicalEvent reward)).real
          (chronologicalOpenClockWindow lower upper)) :
    Nonempty (QuittingFiniteDominantClockWindowStage
      certificate reward lower upper) := by
  classical
  let stageTotal := fun stage : ℕ ↦
    ∑ coalition : {S : Finset ι // S.Nonempty},
      quittingRootSequenceStageCoalitionMass roots stage coalition
  let inWindow := fun stage : ℕ ↦
    quittingRootSequenceClock roots stage ∈ Ioo lower upper
  let active := (Finset.range (certificate.cutoff + 1)).filter
    fun stage ↦ inWindow stage ∧ 0 < stageTotal stage
  have hstageTotal_nonneg (stage : ℕ) : 0 ≤ stageTotal stage := by
    exact Finset.sum_nonneg fun coalition _ ↦
      quittingRootSequenceStageCoalitionMass_nonneg roots stage coalition
  have hsum_pos : 0 < ∑ stage ∈ Finset.range (certificate.cutoff + 1),
      if inWindow stage then stageTotal stage else 0 := by
    rw [← certificate.chronologicalLaw_openClockWindow_real_eq_sum
      (reward := reward) lower upper]
    linarith
  have hactive : active.Nonempty := by
    rw [Finset.sum_pos_iff_of_nonneg] at hsum_pos
    · obtain ⟨stage, hstage, hpos⟩ := hsum_pos
      by_cases hwindow : inWindow stage
      · exact ⟨stage, Finset.mem_filter.mpr
          ⟨hstage, hwindow, by simpa [hwindow] using hpos⟩⟩
      · simp [hwindow] at hpos
    · intro stage _
      by_cases hwindow : inWindow stage
      · simp [hwindow, hstageTotal_nonneg stage]
      · simp [hwindow]
  let selected := active.max' hactive
  have hselectedActive : selected ∈ active := active.max'_mem hactive
  have hselectedRange : selected ∈
      Finset.range (certificate.cutoff + 1) :=
    (Finset.mem_filter.mp hselectedActive).1
  have hselectedWindow : inWindow selected :=
    (Finset.mem_filter.mp hselectedActive).2.1
  have hselectedPos : 0 < stageTotal selected :=
    (Finset.mem_filter.mp hselectedActive).2.2
  have hselectedLe : selected ≤ certificate.cutoff := by
    have := Finset.mem_range.mp hselectedRange
    omega
  have hlater_zero {stage : ℕ}
      (hstageRange : stage ∈ Finset.range (certificate.cutoff + 1))
      (hstageWindow : inWindow stage) (hselectedStage : selected < stage) :
      stageTotal stage = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hpos
      have hstageActive : stage ∈ active :=
        Finset.mem_filter.mpr ⟨hstageRange, hstageWindow, hpos⟩
      exact (not_le_of_gt hselectedStage) (active.le_max' stage hstageActive)
    · exact hstageTotal_nonneg stage
  let residualTotal :=
    ∑ stage ∈ (Finset.range (certificate.cutoff + 1)).erase selected,
      if inWindow stage then stageTotal stage else 0
  have hresidualTotal_lt : residualTotal < upper - lower := by
    let firstSet := (Finset.range (certificate.cutoff + 1)).filter inWindow
    have hfirstSet : firstSet.Nonempty := by
      exact ⟨selected, Finset.mem_filter.mpr
        ⟨hselectedRange, hselectedWindow⟩⟩
    let first := firstSet.min' hfirstSet
    have hfirstMem : first ∈ firstSet := firstSet.min'_mem hfirstSet
    have hfirstRange : first ∈ Finset.range (certificate.cutoff + 1) :=
      (Finset.mem_filter.mp hfirstMem).1
    have hfirstWindow : inWindow first :=
      (Finset.mem_filter.mp hfirstMem).2
    have hfirstSelected : first ≤ selected :=
      firstSet.min'_le selected (Finset.mem_filter.mpr
        ⟨hselectedRange, hselectedWindow⟩)
    let comparison := fun stage : ℕ ↦
      if stage ∈ Finset.Ico first selected then stageTotal stage else 0
    have hcomparison_nonneg (stage : ℕ) : 0 ≤ comparison stage := by
      unfold comparison
      split
      · exact hstageTotal_nonneg stage
      · exact le_rfl
    have hpointwise {stage : ℕ}
        (hstage : stage ∈
          (Finset.range (certificate.cutoff + 1)).erase selected) :
        (if inWindow stage then stageTotal stage else 0) ≤ comparison stage := by
      have hstageRange := (Finset.mem_erase.mp hstage).2
      have hstageNe := (Finset.mem_erase.mp hstage).1
      by_cases hwindow : inWindow stage
      · have hfirstStage : first ≤ stage :=
          firstSet.min'_le stage (Finset.mem_filter.mpr
            ⟨hstageRange, hwindow⟩)
        rcases lt_or_gt_of_ne hstageNe with hstageSelected | hselectedStage
        · simp [hwindow, comparison, Finset.mem_Ico, hfirstStage,
            hstageSelected]
        · rw [hlater_zero hstageRange hwindow hselectedStage]
          simp only [if_pos hwindow]
          exact hcomparison_nonneg stage
      · rw [if_neg hwindow]
        exact hcomparison_nonneg stage
    have hcomparison :
        (∑ stage ∈ (Finset.range (certificate.cutoff + 1)).erase selected,
          comparison stage) =
          ∑ stage ∈ Finset.Ico first selected, stageTotal stage := by
      calc
        (∑ stage ∈ (Finset.range (certificate.cutoff + 1)).erase selected,
            comparison stage) =
            ∑ stage ∈ Finset.Ico first selected, comparison stage := by
          symm
          apply Finset.sum_subset
          · intro stage hstage
            have hstageBounds := Finset.mem_Ico.mp hstage
            apply Finset.mem_erase.mpr
            constructor
            · exact hstageBounds.2.ne
            · apply Finset.mem_range.mpr
              omega
          · intro stage _ hnotIco
            change comparison stage = 0
            unfold comparison
            rw [if_neg hnotIco]
        _ = ∑ stage ∈ Finset.Ico first selected, stageTotal stage := by
          apply Finset.sum_congr rfl
          intro stage hstage
          unfold comparison
          rw [if_pos hstage]
    calc
      residualTotal ≤
          ∑ stage ∈ (Finset.range (certificate.cutoff + 1)).erase selected,
            comparison stage := by
        apply Finset.sum_le_sum
        intro stage hstage
        exact hpointwise hstage
      _ = ∑ stage ∈ Finset.Ico first selected, stageTotal stage := hcomparison
      _ = quittingRootSequenceClock roots selected -
          quittingRootSequenceClock roots first := by
        unfold stageTotal
        rw [Finset.sum_Ico_eq_sub _ hfirstSelected,
          sum_range_stageTotal_eq_clock,
          sum_range_stageTotal_eq_clock]
      _ < upper - lower := by
        exact sub_lt_sub hselectedWindow.2 hfirstWindow.1
  let residual := fun coalition : {S : Finset ι // S.Nonempty} ↦
    ∑ stage ∈ (Finset.range (certificate.cutoff + 1)).erase selected,
      if inWindow stage then
        quittingRootSequenceStageCoalitionMass roots stage coalition else 0
  have hwindow_eq (coalition : {S : Finset ι // S.Nonempty}) :
      (certificate.chronologicalLaw reward :
        Measure (QuittingChronologicalEvent reward)).real
          (chronologicalOpenClockCoalitionWindow lower upper coalition) =
        quittingRootSequenceStageCoalitionMass roots selected coalition +
          residual coalition := by
    rw [certificate.chronologicalLaw_openClockCoalitionWindow_real_eq_sum]
    have hsplit := Finset.sum_erase_add
      (Finset.range (certificate.cutoff + 1))
      (fun stage ↦ if inWindow stage then
        quittingRootSequenceStageCoalitionMass roots stage coalition else 0)
      hselectedRange
    rw [if_pos hselectedWindow] at hsplit
    exact hsplit.symm.trans (add_comm _ _)
  have hresidual_nonneg
      (coalition : {S : Finset ι // S.Nonempty}) :
      0 ≤ residual coalition := by
    apply Finset.sum_nonneg
    intro stage _
    split
    · exact quittingRootSequenceStageCoalitionMass_nonneg roots stage coalition
    · exact le_rfl
  have hsum_residual : (∑ coalition, residual coalition) = residualTotal := by
    unfold residual residualTotal
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro stage _
    by_cases hwindow : inWindow stage
    · simp [hwindow, stageTotal]
    · simp [hwindow]
  have hcumulative (coalition : {S : Finset ι // S.Nonempty}) :
      quittingRootSequenceCumulativeCoalitionMass roots selected coalition =
        chronologicalCoalitionCDF (certificate.chronologicalLaw reward)
            coalition lower + residual coalition := by
    have hlower_le_one : lower ≤ 1 :=
      hselectedWindow.1.le.trans
        (quittingRootSequenceClock_le_one roots selected)
    rw [chronologicalCoalitionCDF_eq_clockCoalitionEvent_real _ _ hlower_le_one,
      certificate.chronologicalLaw_clockCoalitionEvent_real_eq_value]
    unfold QuittingFiniteRootSequenceAbsorption.value
      quittingRootSequenceCumulativeCoalitionMass residual
    let full := Finset.range (certificate.cutoff + 1)
    have hprefix :
        (∑ stage ∈ Finset.range selected,
          quittingRootSequenceStageCoalitionMass roots stage coalition) =
        ∑ stage ∈ full,
          if stage < selected then
            quittingRootSequenceStageCoalitionMass roots stage coalition else 0 := by
      calc
        _ = ∑ stage ∈ full.filter (fun stage ↦ stage < selected),
            quittingRootSequenceStageCoalitionMass roots stage coalition := by
          apply Finset.sum_congr
          · ext stage
            simp [full]
            omega
          · intro stage _
            rfl
        _ = _ := by rw [Finset.sum_filter]
    have herase :
        (∑ stage ∈ full.erase selected,
          if inWindow stage then
            quittingRootSequenceStageCoalitionMass roots stage coalition else 0) =
        ∑ stage ∈ full,
          if stage = selected then 0 else
            if inWindow stage then
              quittingRootSequenceStageCoalitionMass roots stage coalition else 0 := by
      calc
        _ = ∑ stage ∈ full.erase selected,
            if stage = selected then 0 else
              if inWindow stage then
                quittingRootSequenceStageCoalitionMass roots stage coalition else 0 := by
          apply Finset.sum_congr rfl
          intro stage hstage
          rw [if_neg (Finset.ne_of_mem_erase hstage)]
        _ = _ := by
          apply Finset.sum_subset (Finset.erase_subset selected full)
          intro stage hstageFull hstageErase
          have heq : stage = selected := by
            by_contra hne
            exact hstageErase (Finset.mem_erase.mpr ⟨hne, hstageFull⟩)
          simp [heq]
    rw [hprefix, herase, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro current hcurrent
    have hcurrentRange : current ∈ Finset.range (certificate.cutoff + 1) :=
      hcurrent
    rcases lt_trichotomy current selected with hbefore | heq | hafter
    · have hclockLe : quittingRootSequenceClock roots current ≤
          quittingRootSequenceClock roots selected :=
        monotone_quittingRootSequenceClock roots hbefore.le
      by_cases hlower : quittingRootSequenceClock roots current ≤ lower
      · have hnotWindow : ¬inWindow current := by
          intro hwindow
          exact (not_lt_of_ge hlower) hwindow.1
        simp [hbefore, hbefore.ne, hlower, hnotWindow]
      · have hwindow : inWindow current := by
          exact ⟨lt_of_not_ge hlower,
            hclockLe.trans_lt hselectedWindow.2⟩
        simp [hbefore, hbefore.ne, hlower, hwindow]
    · subst current
      simp [not_le_of_gt hselectedWindow.1]
    · have hclockGt : lower < quittingRootSequenceClock roots current :=
        hselectedWindow.1.trans_le
          (monotone_quittingRootSequenceClock roots hafter.le)
      by_cases hwindow : inWindow current
      · have hzero := hlater_zero hcurrentRange hwindow hafter
        have hcoordinateZero :
            quittingRootSequenceStageCoalitionMass roots current coalition = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun terminal _ ↦ quittingRootSequenceStageCoalitionMass_nonneg
              roots current terminal)).mp hzero coalition (Finset.mem_univ coalition)
        simp [not_lt_of_ge hafter.le, hafter.ne', not_le_of_gt hclockGt,
          hwindow, hcoordinateZero]
      · simp [not_lt_of_ge hafter.le, hafter.ne', not_le_of_gt hclockGt,
          hwindow]
  exact ⟨{
    stage := selected
    stage_le_cutoff := hselectedLe
    clock_mem := hselectedWindow
    stageTotal_pos := hselectedPos
    residual := residual
    window_eq_stage_add_residual := hwindow_eq
    residual_nonneg := hresidual_nonneg
    sum_residual_lt_width := hsum_residual.trans_lt hresidualTotal_lt
    cumulative_eq_lowerCDF_add_residual := hcumulative
  }⟩

end QuittingFiniteRootSequenceAbsorption

end GameTheory.QuittingAbsorptionPath
