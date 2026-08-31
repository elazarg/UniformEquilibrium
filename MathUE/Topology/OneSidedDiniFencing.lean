/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IsLUB

/-!
# One-sided Dini fencing

A right-continuous real function with left limits and no upward jumps cannot
cross a linear barrier when arbitrarily small positive right slopes are
excluded at every point.  The asymmetric statement is designed for càdlàg
coordinate differences; it is game-independent.
-/

noncomputable section

namespace Math.Topology

open Filter Set

/-- A one-sided fencing lemma for a right-continuous function whose jumps
can only move downward.  Unlike the continuous Mathlib fencing theorem, the
left-limit hypothesis is deliberately asymmetric: this is the exact shape
needed after subtracting the incident singleton coordinate from a càdlàg
coalition coordinate. -/
theorem endpoint_le_of_rightContinuous_leftLimit_noUpwardJump_liminfSlope_nonpos
    {f left : ℝ → ℝ} {start stop bound : ℝ}
    (hstartStop : start ≤ stop)
    (hstart : f start ≤ bound)
    (hright : ∀ point ∈ Set.Ico start stop,
      Tendsto f (nhdsWithin point (Set.Icc point stop)) (nhds (f point)))
    (hleft : ∀ point ∈ Set.Ioc start stop,
      Tendsto f (nhdsWithin point (Set.Ico start point)) (nhds (left point)))
    (hjump : ∀ point ∈ Set.Ioc start stop, f point ≤ left point)
    (hslope : ∀ point ∈ Set.Ico start stop, ∀ rate : ℝ, 0 < rate →
      ∃ᶠ later in nhdsWithin point (Set.Ioo point stop),
        slope f point later < rate) :
    f stop ≤ bound := by
  rcases hstartStop.eq_or_lt with rfl | hstartStop
  · exact hstart
  by_contra hnot
  have hboundStop : bound < f stop := lt_of_not_ge hnot
  let rate : ℝ := (f stop - bound) / (2 * (stop - start))
  have hratePos : 0 < rate := by
    dsimp only [rate]
    positivity
  let barrier : ℝ → ℝ := fun point ↦
    bound + rate * (point - start)
  let safe : Set ℝ :=
    {point | point ∈ Set.Icc start stop ∧ f point ≤ barrier point}
  have hstartSafe : start ∈ safe := by
    refine ⟨⟨le_rfl, hstartStop.le⟩, ?_⟩
    simpa only [barrier, sub_self, mul_zero, add_zero] using hstart
  have hsafeNonempty : safe.Nonempty := ⟨start, hstartSafe⟩
  have hsafeUpper : ∀ point ∈ safe, point ≤ stop :=
    fun point hpoint ↦ hpoint.1.2
  have hsafeBdd : BddAbove safe := ⟨stop, hsafeUpper⟩
  let frontier := sSup safe
  have hfrontierLower : start ≤ frontier :=
    le_csSup hsafeBdd hstartSafe
  have hfrontierUpper : frontier ≤ stop :=
    csSup_le hsafeNonempty hsafeUpper
  have hfrontierSafe : frontier ∈ safe := by
    by_cases hmem : frontier ∈ safe
    · exact hmem
    · obtain ⟨approach, _happroachMono, happroachTendsto,
          happroachSafe⟩ :=
        exists_seq_tendsto_sSup hsafeNonempty hsafeBdd
      have happroachLt (stage : ℕ) : approach stage < frontier := by
        exact lt_of_le_of_ne
          (le_csSup hsafeBdd (happroachSafe stage)) <| by
            intro heq
            exact hmem (heq ▸ happroachSafe stage)
      have hfrontierStrict : start < frontier := by
        exact lt_of_le_of_ne hfrontierLower <| by
          intro heq
          exact hmem (heq ▸ hstartSafe)
      have hfrontierMem : frontier ∈ Set.Ioc start stop :=
        ⟨hfrontierStrict, hfrontierUpper⟩
      have happroachWithin : Tendsto approach atTop
          (nhdsWithin frontier (Set.Ico start frontier)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨happroachTendsto,
          Filter.Eventually.of_forall fun stage ↦
            ⟨(happroachSafe stage).1.1, happroachLt stage⟩⟩
      have hfTendsto : Tendsto (fun stage ↦ f (approach stage)) atTop
          (nhds (left frontier)) :=
        (hleft frontier hfrontierMem).comp happroachWithin
      have hbarrierTendsto :
          Tendsto (fun stage ↦ barrier (approach stage)) atTop
            (nhds (barrier frontier)) := by
        exact (continuousAt_const.add
          (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))).tendsto.comp
            happroachTendsto
      have hleftLe : left frontier ≤ barrier frontier :=
        le_of_tendsto_of_tendsto hfTendsto hbarrierTendsto <|
          Filter.Eventually.of_forall fun stage ↦ (happroachSafe stage).2
      exact ⟨⟨hfrontierLower, hfrontierUpper⟩,
        (hjump frontier hfrontierMem).trans hleftLe⟩
  have hfrontierEq : frontier = stop := by
    apply le_antisymm hfrontierUpper
    by_contra hnotLe
    have hfrontierStop : frontier < stop := lt_of_not_ge hnotLe
    have hfrontierIco : frontier ∈ Set.Ico start stop :=
      ⟨hfrontierLower, hfrontierStop⟩
    have hexistsLater : ∃ later ∈ Set.Ioc frontier stop,
        f later ≤ barrier later := by
      rcases (hfrontierSafe.2).lt_or_eq with hstrict | heq
      · have hrightFilter :
            nhdsWithin frontier (Set.Ioo frontier stop) ≤
              nhdsWithin frontier (Set.Icc frontier stop) :=
          nhdsWithin_mono frontier fun point hpoint ↦
            ⟨hpoint.1.le, hpoint.2.le⟩
        have hbarrierContinuous : ContinuousAt barrier frontier := by
          dsimp only [barrier]
          fun_prop
        have hcontinuous : Tendsto
            (fun point ↦ (f point, barrier point))
            (nhdsWithin frontier (Set.Ioo frontier stop))
            (nhds (f frontier, barrier frontier)) := by
          exact Filter.Tendsto.prodMk_nhds
            ((hright frontier hfrontierIco).mono_left hrightFilter)
            (hbarrierContinuous.tendsto.mono_left inf_le_left)
        have heventually : ∀ᶠ point in
            nhdsWithin frontier (Set.Ioo frontier stop),
              f point < barrier point :=
          hcontinuous <|
            (isOpen_lt continuous_fst continuous_snd).mem_nhds hstrict
        letI : (nhdsWithin frontier (Set.Ioo frontier stop)).NeBot :=
          left_nhdsWithin_Ioo_neBot hfrontierStop
        obtain ⟨later, hlaterStrict, hlaterMem⟩ :=
          (heventually.and self_mem_nhdsWithin).exists
        exact ⟨later, ⟨hlaterMem.1, hlaterMem.2.le⟩, hlaterStrict.le⟩
      · have hfrequent := hslope frontier hfrontierIco rate hratePos
        obtain ⟨later, hlaterSlope, hlaterMem⟩ :=
          (hfrequent.and_eventually self_mem_nhdsWithin).exists
        have hlaterIoc : later ∈ Set.Ioc frontier stop :=
          ⟨hlaterMem.1, hlaterMem.2.le⟩
        have hbarrierSlope :
            slope barrier frontier later = rate := by
          rw [slope_def_field]
          apply (div_eq_iff (sub_ne_zero.mpr hlaterMem.1.ne')).2
          dsimp only [barrier]
          ring
        have hle : f later ≤ barrier later := by
          have hslopeLe : slope f frontier later ≤
              slope barrier frontier later := by
            rw [hbarrierSlope]
            exact hlaterSlope.le
          rw [slope_def_field, slope_def_field,
            div_le_div_iff_of_pos_right (sub_pos.mpr hlaterMem.1), heq,
            sub_le_sub_iff_right] at hslopeLe
          exact hslopeLe
        exact ⟨later, hlaterIoc, hle⟩
    obtain ⟨later, hlaterMem, hlaterSafe⟩ := hexistsLater
    have hlaterFullSafe : later ∈ safe := by
      exact ⟨⟨hfrontierLower.trans hlaterMem.1.le, hlaterMem.2⟩,
        hlaterSafe⟩
    have hlaterLe : later ≤ frontier := le_csSup hsafeBdd hlaterFullSafe
    exact (not_le_of_gt hlaterMem.1) hlaterLe
  have hstopBarrier : f stop ≤ barrier stop := by
    simpa only [hfrontierEq] using hfrontierSafe.2
  have hbarrierStop : barrier stop < f stop := by
    dsimp only [barrier, rate]
    have hstopStartPos : 0 < stop - start := sub_pos.mpr hstartStop
    field_simp [ne_of_gt hstopStartPos]
    linarith
  exact (not_le_of_gt hbarrierStop) hstopBarrier

end Math.Topology

