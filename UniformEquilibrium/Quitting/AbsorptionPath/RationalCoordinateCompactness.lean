/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.WeakPathConvergence
import UniformEquilibrium.Quitting.AbsorptionPath.ClockGapConstantTotalComponents

/-!
# Rational-coordinate compactness for unit-bounded absorption paths

This module extracts one common subsequence on which every coalition
coordinate converges at every rational clock time.  It is the compact product
step in the Helly reconstruction of a weak absorption-path limit.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def clippedRationalTime (time : ℚ) : ℝ :=
  max 0 (min 1 (time : ℝ))

private theorem clippedRationalTime_mem_Icc (time : ℚ) :
    clippedRationalTime time ∈ Icc (0 : ℝ) 1 := by
  unfold clippedRationalTime
  constructor <;> simp

private theorem clippedRationalTime_mono : Monotone clippedRationalTime := by
  intro first second htime
  unfold clippedRationalTime
  gcongr

/-- Every rational-time coalition coordinate of a unit-bounded path, stored
in the compact unit interval. -/
def absorptionPathRationalSample (path : AbsorptionPath (ι := ι)) :
    {coalition : Finset ι // coalition.Nonempty} → ℚ → Icc (0 : ℝ) 1 :=
  fun coalition time ↦
    ⟨path.1.value (clippedRationalTime time) coalition,
      path.1.value_mem _ (clippedRationalTime_mem_Icc time) coalition⟩

/-- A sequence of absorption paths admits one strict subsequence on which all
rational-time coalition coordinates converge simultaneously. -/
theorem exists_rationalSample_tendsto_subsequence
    (sequence : ℕ → AbsorptionPath (ι := ι)) :
    ∃ (sample : {coalition : Finset ι // coalition.Nonempty} →
          ℚ → Icc (0 : ℝ) 1)
        (subsequence : ℕ → ℕ),
      StrictMono subsequence ∧
        Tendsto (absorptionPathRationalSample ∘ sequence ∘ subsequence)
          atTop (nhds sample) := by
  exact CompactSpace.tendsto_subseq (absorptionPathRationalSample ∘ sequence)

/-- Monotonicity and the clock lower/unit upper total bounds required of
rational data before right-continuous reconstruction. -/
def IsUnitBoundedAbsorptionRationalSample
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1) : Prop :=
  (∀ coalition, Monotone (fun time ↦ (sample coalition time : ℝ))) ∧
    (∀ time : ℚ, (time : ℝ) ∈ Icc 0 1 →
      (time : ℝ) ≤ ∑ coalition, (sample coalition time : ℝ)) ∧
    (∀ time : ℚ,
      ∑ coalition, (sample coalition time : ℝ) ≤ 1) ∧
    (∀ coalition (time : ℚ), 1 ≤ time →
      sample coalition time = sample coalition 1)

private theorem rationalSample_coordinate_tendsto
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    {subsequence : ℕ → ℕ}
    (hconverges :
      Tendsto (absorptionPathRationalSample ∘ sequence ∘ subsequence)
        atTop (nhds sample))
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℚ) :
    Tendsto (fun rank ↦
      ((absorptionPathRationalSample
        (sequence (subsequence rank)) coalition time : Icc (0 : ℝ) 1) : ℝ))
      atTop (nhds (sample coalition time : ℝ)) := by
  have hcoalition := (tendsto_pi_nhds.mp hconverges) coalition
  have htime := (tendsto_pi_nhds.mp hcoalition) time
  simpa only [Function.comp_def] using
    continuous_subtype_val.continuousAt.tendsto.comp htime

/-- Unit total-mass bounds and coordinate monotonicity pass to a simultaneous
rational-coordinate subsequential limit. -/
theorem isUnitBoundedAbsorptionRationalSample_of_tendsto
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    {subsequence : ℕ → ℕ}
    (hselectedBounded : ∀ rank,
      HasUnitBoundedTotalMass (sequence (subsequence rank)))
    (hconverges :
      Tendsto (absorptionPathRationalSample ∘ sequence ∘ subsequence)
        atTop (nhds sample)) :
    IsUnitBoundedAbsorptionRationalSample sample := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro coalition first second htime
    apply le_of_tendsto_of_tendsto
      (rationalSample_coordinate_tendsto hconverges coalition first)
      (rationalSample_coordinate_tendsto hconverges coalition second)
    exact Eventually.of_forall fun rank ↦
      (sequence (subsequence rank)).1.monotone coalition
        (clippedRationalTime_mem_Icc first)
        (clippedRationalTime_mem_Icc second)
        (clippedRationalTime_mono htime)
  · intro time htime
    have hsum : Tendsto (fun rank ↦
        ∑ coalition,
          ((absorptionPathRationalSample
            (sequence (subsequence rank)) coalition time :
              Icc (0 : ℝ) 1) : ℝ)) atTop
        (nhds (∑ coalition, (sample coalition time : ℝ))) :=
      tendsto_finsetSum Finset.univ fun coalition _ ↦
        rationalSample_coordinate_tendsto hconverges coalition time
    exact ge_of_tendsto' hsum fun rank ↦ by
      simpa only [absorptionPathRationalSample, clippedRationalTime,
        max_eq_right htime.1, min_eq_right htime.2, pathTotal] using
        (sequence (subsequence rank)).property.1 (time : ℝ) htime
  · intro time
    have hsum : Tendsto (fun rank ↦
        ∑ coalition,
          ((absorptionPathRationalSample
            (sequence (subsequence rank)) coalition time :
              Icc (0 : ℝ) 1) : ℝ)) atTop
        (nhds (∑ coalition, (sample coalition time : ℝ))) :=
      tendsto_finsetSum Finset.univ fun coalition _ ↦
        rationalSample_coordinate_tendsto hconverges coalition time
    exact le_of_tendsto' hsum fun rank ↦ by
      simpa only [absorptionPathRationalSample, pathTotal] using
        hselectedBounded rank (clippedRationalTime time)
          (clippedRationalTime_mem_Icc time)
  · intro coalition time htime
    apply Subtype.ext
    have htimeReal : (1 : ℝ) ≤ (time : ℝ) := by exact_mod_cast htime
    apply tendsto_nhds_unique
      (rationalSample_coordinate_tendsto hconverges coalition time)
    refine Filter.Tendsto.congr' (Eventually.of_forall fun rank ↦ ?_)
      (rationalSample_coordinate_tendsto hconverges coalition 1)
    simp [absorptionPathRationalSample, clippedRationalTime,
      min_eq_left htimeReal]

/-- The monotone upper rational envelope used before taking a canonical
right-continuous representative. -/
noncomputable def absorptionRationalSampleUpperEnvelope
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℝ) : ℝ :=
  ⨅ rational : {rational : ℚ // time < rational},
    (sample coalition rational : ℝ)

omit [Fintype ι] [DecidableEq ι] in
private theorem absorptionRationalSampleUpperEnvelope_nonneg
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℝ) :
    0 ≤ absorptionRationalSampleUpperEnvelope sample coalition time := by
  have : Nonempty {rational : ℚ // time < rational} := by
    obtain ⟨rational, hrational⟩ := exists_rat_gt time
    exact ⟨⟨rational, hrational⟩⟩
  rw [absorptionRationalSampleUpperEnvelope]
  exact le_ciInf fun rational ↦ (sample coalition rational).property.1

omit [Fintype ι] [DecidableEq ι] in
private theorem absorptionRationalSampleUpperEnvelope_le_one
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℝ) :
    absorptionRationalSampleUpperEnvelope sample coalition time ≤ 1 := by
  obtain ⟨rational, hrational⟩ := exists_rat_gt time
  rw [absorptionRationalSampleUpperEnvelope]
  exact (ciInf_le
    ⟨0, fun value ↦ by
      rintro ⟨other, rfl⟩
      exact (sample coalition other).property.1⟩
    ⟨rational, hrational⟩).trans (sample coalition rational).property.2

omit [Fintype ι] [DecidableEq ι] in
private theorem absorptionRationalSampleUpperEnvelope_monotone
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (coalition : {coalition : Finset ι // coalition.Nonempty}) :
    Monotone (absorptionRationalSampleUpperEnvelope sample coalition) := by
  intro first second htime
  obtain ⟨upperRational, hupperRational⟩ := exists_rat_gt second
  letI : Nonempty {rational : ℚ // second < rational} :=
    ⟨⟨upperRational, hupperRational⟩⟩
  rw [absorptionRationalSampleUpperEnvelope,
    absorptionRationalSampleUpperEnvelope]
  refine le_ciInf fun rational ↦ ?_
  calc
    (⨅ firstRational : {value : ℚ // first < value},
        (sample coalition firstRational : ℝ)) ≤
        (sample coalition rational.1 : ℝ) := ciInf_le
          (show BddBelow (Set.range
              (fun firstRational : {value : ℚ // first < value} ↦
                (sample coalition firstRational : ℝ))) from
            ⟨0, by
              rintro _ ⟨other, rfl⟩
              exact (sample coalition other).property.1⟩)
          ⟨rational.1, htime.trans_lt rational.2⟩
    _ = (sample coalition rational : ℝ) := rfl

/-- The right-continuous real-time representative reconstructed from a
rational coordinate sample, extended by zero before clock zero. -/
noncomputable def absorptionRationalSampleValue
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (time : ℝ) (coalition : {coalition : Finset ι // coalition.Nonempty}) : ℝ :=
  if 0 ≤ time then
    Function.rightLim
      (absorptionRationalSampleUpperEnvelope sample coalition) time
  else 0

omit [Fintype ι] [DecidableEq ι] in
private theorem absorptionRationalSampleRightLim_nonneg
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℝ) :
    0 ≤ Function.rightLim
      (absorptionRationalSampleUpperEnvelope sample coalition) time := by
  exact (absorptionRationalSampleUpperEnvelope_nonneg
      sample coalition time).trans
    (Monotone.le_rightLim
      (absorptionRationalSampleUpperEnvelope_monotone sample coalition)
      le_rfl)

omit [Fintype ι] [DecidableEq ι] in
private theorem absorptionRationalSampleRightLim_le_one
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℝ) :
    Function.rightLim
      (absorptionRationalSampleUpperEnvelope sample coalition) time ≤ 1 := by
  calc
    Function.rightLim
        (absorptionRationalSampleUpperEnvelope sample coalition) time ≤
      absorptionRationalSampleUpperEnvelope sample coalition (time + 1) :=
        Monotone.rightLim_le
          (absorptionRationalSampleUpperEnvelope_monotone sample coalition)
          (lt_add_one time)
    _ ≤ 1 := absorptionRationalSampleUpperEnvelope_le_one
      sample coalition (time + 1)

omit [Fintype ι] [DecidableEq ι] in
private theorem absorptionRationalSampleValue_monotone
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (coalition : {coalition : Finset ι // coalition.Nonempty}) :
    Monotone (fun time ↦ absorptionRationalSampleValue
      sample time coalition) := by
  intro first second htime
  change (if 0 ≤ first then Function.rightLim
      (absorptionRationalSampleUpperEnvelope sample coalition) first else 0) ≤
    (if 0 ≤ second then Function.rightLim
      (absorptionRationalSampleUpperEnvelope sample coalition) second else 0)
  split_ifs with hfirst hsecond
  · exact Monotone.rightLim
      (absorptionRationalSampleUpperEnvelope_monotone sample coalition) htime
  · exact (hsecond (hfirst.trans htime)).elim
  · exact absorptionRationalSampleRightLim_nonneg sample coalition second
  · exact le_rfl

/-- The left-limit field corresponding to the reconstructed real-time
coordinate, with the empty pre-zero limit normalized to zero. -/
noncomputable def absorptionRationalSampleLeftValue
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (time : ℝ) (coalition : {coalition : Finset ι // coalition.Nonempty}) : ℝ :=
  if time = 0 then 0 else
    Function.leftLim
      (fun point ↦ absorptionRationalSampleValue sample point coalition) time

omit [Fintype ι] [DecidableEq ι] in
private theorem absorptionRationalSampleValue_continuousWithinAt_Ici
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℝ) (htime : 0 ≤ time) :
    Tendsto (fun point ↦ absorptionRationalSampleValue
        sample point coalition)
      (nhdsWithin time (Ici time))
      (nhds (absorptionRationalSampleValue sample time coalition)) := by
  have hright := continuousWithinAt_rightLim_Ici
    (Monotone.tendsto_rightLim
      (absorptionRationalSampleUpperEnvelope_monotone sample coalition) time)
  rw [absorptionRationalSampleValue, if_pos htime]
  refine Filter.Tendsto.congr' ?_ hright
  filter_upwards [self_mem_nhdsWithin] with point hpoint
  simp only [absorptionRationalSampleValue,
    if_pos (htime.trans hpoint)]

omit [Fintype ι] [DecidableEq ι] in
private theorem absorptionRationalSampleValue_right_continuous
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℝ) (htime : time ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun point ↦ absorptionRationalSampleValue
        sample point coalition)
      (nhdsWithin time (Icc time 1))
      (nhds (absorptionRationalSampleValue sample time coalition)) :=
  (absorptionRationalSampleValue_continuousWithinAt_Ici
    sample coalition time htime.1).mono_left
      (nhdsWithin_mono time fun _ hpoint ↦ hpoint.1)

omit [Fintype ι] [DecidableEq ι] in
private theorem absorptionRationalSampleValue_left_limit
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℝ) (htime : time ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun point ↦ absorptionRationalSampleValue
        sample point coalition)
      (nhdsWithin time (Icc 0 time \ {time}))
      (nhds (absorptionRationalSampleLeftValue sample time coalition)) := by
  by_cases hzero : time = 0
  · subst time
    have hempty : Icc (0 : ℝ) 0 \ {0} = ∅ := by
      ext point
      constructor
      · intro hpoint
        exact (hpoint.2 (le_antisymm hpoint.1.2 hpoint.1.1)).elim
      · intro hpoint
        exact hpoint.elim
    simp only [hempty, nhdsWithin_empty, tendsto_bot]
  · simp only [absorptionRationalSampleLeftValue, if_neg hzero]
    apply (Monotone.tendsto_leftLim
      (absorptionRationalSampleValue_monotone sample coalition) time).mono_left
    apply nhdsWithin_mono
    intro point hpoint
    exact lt_of_le_of_ne hpoint.1.2 hpoint.2

/-- Rational limit data reconstructs a coordinatewise monotone càdlàg path.
The absorption-path closure conditions are separate downstream obligations. -/
noncomputable def cadlagPathOfAbsorptionRationalSample
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1) : CadlagPath (ι := ι) where
  value := absorptionRationalSampleValue sample
  leftValue := absorptionRationalSampleLeftValue sample
  value_mem := by
    intro time htime coalition
    simp only [absorptionRationalSampleValue, if_pos htime.1]
    exact ⟨absorptionRationalSampleRightLim_nonneg sample coalition time,
      absorptionRationalSampleRightLim_le_one sample coalition time⟩
  monotone := by
    intro coalition first _ second _ htime
    exact absorptionRationalSampleValue_monotone sample coalition htime
  right_continuous := absorptionRationalSampleValue_right_continuous sample
  left_limit := absorptionRationalSampleValue_left_limit sample
  left_zero := by
    intro coalition
    simp [absorptionRationalSampleLeftValue]

omit [DecidableEq ι] in
private theorem absorptionRationalSample_le_upperEnvelope
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (rational : ℚ) (time : ℝ) (htime : (rational : ℝ) ≤ time) :
    (sample coalition rational : ℝ) ≤
      absorptionRationalSampleUpperEnvelope sample coalition time := by
  obtain ⟨upperRational, hupperRational⟩ := exists_rat_gt time
  letI : Nonempty {value : ℚ // time < value} :=
    ⟨⟨upperRational, hupperRational⟩⟩
  rw [absorptionRationalSampleUpperEnvelope]
  refine le_ciInf fun upperRational ↦ hsample.1 coalition ?_
  exact_mod_cast (htime.trans_lt upperRational.2).le

omit [Fintype ι] [DecidableEq ι] in
private theorem absorptionRationalSampleUpperEnvelope_le
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℝ) (rational : ℚ) (htime : time < rational) :
    absorptionRationalSampleUpperEnvelope sample coalition time ≤
      (sample coalition rational : ℝ) := by
  rw [absorptionRationalSampleUpperEnvelope]
  exact ciInf_le
    (show BddBelow (Set.range
        (fun upperRational : {value : ℚ // time < value} ↦
          (sample coalition upperRational : ℝ))) from
      ⟨0, by
        rintro _ ⟨other, rfl⟩
        exact (sample coalition other).property.1⟩)
    ⟨rational, htime⟩

omit [DecidableEq ι] in
/-- A rational coordinate at or before a nonnegative real time is below the
reconstructed post-time value. -/
theorem absorptionRationalSample_le_reconstructedValue
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (rational : ℚ) (time : ℝ) (htime : 0 ≤ time)
    (hrational : (rational : ℝ) ≤ time) :
    (sample coalition rational : ℝ) ≤
      absorptionRationalSampleValue sample time coalition := by
  rw [absorptionRationalSampleValue, if_pos htime]
  exact (absorptionRationalSample_le_upperEnvelope hsample coalition
      rational time hrational).trans
    (Monotone.le_rightLim
      (absorptionRationalSampleUpperEnvelope_monotone sample coalition)
      le_rfl)

omit [Fintype ι] [DecidableEq ι] in
/-- A rational coordinate strictly after a nonnegative real time is above the
reconstructed post-time value. -/
theorem reconstructedValue_le_absorptionRationalSample
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℝ) (rational : ℚ) (htime : 0 ≤ time)
    (hrational : time < (rational : ℝ)) :
    absorptionRationalSampleValue sample time coalition ≤
      (sample coalition rational : ℝ) := by
  rw [absorptionRationalSampleValue, if_pos htime]
  let between : ℝ := (time + (rational : ℝ)) / 2
  have htimeBetween : time < between := by
    dsimp only [between]
    linarith
  have hbetweenRational : between < (rational : ℝ) := by
    dsimp only [between]
    linarith
  exact (Monotone.rightLim_le
      (absorptionRationalSampleUpperEnvelope_monotone sample coalition)
      htimeBetween).trans
    (absorptionRationalSampleUpperEnvelope_le sample coalition between
      rational hbetweenRational)

omit [DecidableEq ι] in
/-- The reconstructed endpoint coordinate is exactly the rational endpoint
coordinate when the rational sample is constant after clock one. -/
theorem reconstructedValue_one_eq_absorptionRationalSample_one
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (coalition : {coalition : Finset ι // coalition.Nonempty}) :
    absorptionRationalSampleValue sample 1 coalition =
      (sample coalition 1 : ℝ) := by
  apply le_antisymm
  · calc
      absorptionRationalSampleValue sample 1 coalition ≤
          (sample coalition 2 : ℝ) :=
        reconstructedValue_le_absorptionRationalSample sample coalition 1 2
          (by norm_num) (by norm_num)
      _ = (sample coalition 1 : ℝ) := by rw [hsample.2.2.2 coalition 2 (by norm_num)]
  · exact absorptionRationalSample_le_reconstructedValue hsample coalition
      (1 : ℚ) (1 : ℝ) (by norm_num) (by norm_num)

private theorem rationalSample_coordinate_tendsto_value
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    {subsequence : ℕ → ℕ}
    (hconverges :
      Tendsto (absorptionPathRationalSample ∘ sequence ∘ subsequence)
        atTop (nhds sample))
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℚ) (htime : (time : ℝ) ∈ Icc 0 1) :
    Tendsto (fun rank ↦
      (sequence (subsequence rank)).1.value time coalition) atTop
      (nhds (sample coalition time : ℝ)) := by
  simpa only [absorptionPathRationalSample, clippedRationalTime,
    max_eq_right htime.1, min_eq_right htime.2] using
    rationalSample_coordinate_tendsto hconverges coalition time

omit [Fintype ι] [DecidableEq ι] in
private theorem exists_rationalSample_above_lower_of_leftContinuous
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℝ) (htime : 0 < time)
    (hleft : Function.leftLim
      (fun point ↦ absorptionRationalSampleValue sample point coalition) time =
        absorptionRationalSampleValue sample time coalition)
    {lower : ℝ}
    (hlower : lower < absorptionRationalSampleValue sample time coalition) :
    ∃ rational : ℚ, (rational : ℝ) ∈ Ioo 0 time ∧
      lower < (sample coalition rational : ℝ) := by
  have htendsto := Monotone.tendsto_leftLim
    (absorptionRationalSampleValue_monotone sample coalition) time
  rw [hleft] at htendsto
  have heventLower := htendsto.eventually (Ioi_mem_nhds hlower)
  obtain ⟨point, hpointLower, hpoint⟩ :=
    (heventLower.and (Ioo_mem_nhdsLT htime)).exists
  obtain ⟨rational, hpointRational, hrationalTime⟩ :=
    exists_rat_btwn hpoint.2
  exact ⟨rational, ⟨hpoint.1.trans hpointRational, hrationalTime⟩,
    hpointLower.trans_le
      (reconstructedValue_le_absorptionRationalSample sample coalition point
        rational hpoint.1.le hpointRational)⟩

omit [DecidableEq ι] in
private theorem exists_rationalSample_below_upper_of_rightContinuous
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℝ) (htimeNonneg : 0 ≤ time) (htime : time < 1)
    {upper : ℝ}
    (hupper : absorptionRationalSampleValue sample time coalition < upper) :
    ∃ rational : ℚ, (rational : ℝ) ∈ Ioo time 1 ∧
      (sample coalition rational : ℝ) < upper := by
  have htendsto :=
    (absorptionRationalSampleValue_continuousWithinAt_Ici
      sample coalition time htimeNonneg)
  have hsubset : Ioi time ⊆ Ici time := by
    intro point hpoint
    simpa only [mem_Ioi, mem_Ici] using hpoint.le
  have htendstoRight := htendsto.mono_left (nhdsWithin_mono time hsubset)
  have heventUpper := htendstoRight.eventually (Iio_mem_nhds hupper)
  obtain ⟨point, hpointUpper, hpoint⟩ :=
    (heventUpper.and (Ioo_mem_nhdsGT htime)).exists
  have htimePoint : time < point := hpoint.1
  have hpointNonneg : 0 ≤ point := htimeNonneg.trans htimePoint.le
  obtain ⟨rational, htimeRational, hrationalPoint⟩ :=
    exists_rat_btwn htimePoint
  refine ⟨rational, ⟨htimeRational, hrationalPoint.trans hpoint.2⟩, ?_⟩
  exact (absorptionRationalSample_le_reconstructedValue hsample coalition
      rational point hpointNonneg hrationalPoint.le).trans_lt
    hpointUpper

/-- Simultaneous convergence of rational coordinates implies convergence at
every continuity point of the reconstructed càdlàg coordinate. -/
theorem tendsto_reconstructedValue_of_not_jump
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    {subsequence : ℕ → ℕ}
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (hconverges :
      Tendsto (absorptionPathRationalSample ∘ sequence ∘ subsequence)
        atTop (nhds sample))
    (coalition : {coalition : Finset ι // coalition.Nonempty})
    (time : ℝ) (htime : time ∈ Icc (0 : ℝ) 1)
    (hnotJump : pathJump (cadlagPathOfAbsorptionRationalSample sample)
      time coalition = 0) :
    Tendsto (fun rank ↦
      (sequence (subsequence rank)).1.value time coalition) atTop
      (nhds ((cadlagPathOfAbsorptionRationalSample sample).value
        time coalition)) := by
  have hvalueLeft :
      (cadlagPathOfAbsorptionRationalSample sample).value time coalition =
        (cadlagPathOfAbsorptionRationalSample sample).leftValue
          time coalition := by
    exact sub_eq_zero.mp hnotJump
  rw [tendsto_order]
  constructor
  · intro lower hlower
    by_cases hzero : time = 0
    · subst time
      have hlimitZero :
          (cadlagPathOfAbsorptionRationalSample sample).value 0 coalition = 0 :=
        hvalueLeft.trans
          ((cadlagPathOfAbsorptionRationalSample sample).left_zero coalition)
      rw [hlimitZero] at hlower
      filter_upwards [] with rank
      exact hlower.trans_le
        ((sequence (subsequence rank)).1.value_mem 0 (by norm_num)
          coalition).1
    · have htimePos : 0 < time := lt_of_le_of_ne htime.1 (Ne.symm hzero)
      have hleft : Function.leftLim
          (fun point ↦ absorptionRationalSampleValue sample point coalition)
            time =
          absorptionRationalSampleValue sample time coalition := by
        simpa only [cadlagPathOfAbsorptionRationalSample,
          absorptionRationalSampleLeftValue, if_neg hzero] using
          hvalueLeft.symm
      obtain ⟨rational, hrationalTime, hlowerRational⟩ :=
        exists_rationalSample_above_lower_of_leftContinuous
          coalition time htimePos hleft hlower
      have hrationalMem : (rational : ℝ) ∈ Icc 0 1 :=
        ⟨hrationalTime.1.le, hrationalTime.2.le.trans htime.2⟩
      have hevent :=
        (rationalSample_coordinate_tendsto_value hconverges coalition
          rational hrationalMem).eventually (Ioi_mem_nhds hlowerRational)
      filter_upwards [hevent] with rank hrank
      exact hrank.trans_le ((sequence (subsequence rank)).1.monotone
        coalition hrationalMem htime hrationalTime.2.le)
  · intro upper hupper
    by_cases hone : time = 1
    · subst time
      have htendsto := rationalSample_coordinate_tendsto_value hconverges
        coalition 1 (by norm_num)
      rw [← reconstructedValue_one_eq_absorptionRationalSample_one
        hsample coalition] at htendsto
      simpa using htendsto.eventually (Iio_mem_nhds hupper)
    · have htimeLt : time < 1 := lt_of_le_of_ne htime.2 hone
      obtain ⟨rational, htimeRational, hrationalUpper⟩ :=
        exists_rationalSample_below_upper_of_rightContinuous hsample
          coalition time htime.1 htimeLt hupper
      have hrationalMem : (rational : ℝ) ∈ Icc 0 1 :=
        ⟨htime.1.trans htimeRational.1.le, htimeRational.2.le⟩
      have hevent :=
        (rationalSample_coordinate_tendsto_value hconverges coalition
          rational hrationalMem).eventually (Iio_mem_nhds hrationalUpper)
      filter_upwards [hevent] with rank hrank
      exact ((sequence (subsequence rank)).1.monotone coalition htime
        hrationalMem htimeRational.1.le).trans_lt hrank

omit [DecidableEq ι] in
/-- The reconstructed rational-envelope path retains the unit upper bound on
total cumulative mass at every clock time. -/
theorem pathTotal_cadlagPathOfAbsorptionRationalSample_le_one
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (time : ℝ) (htime : time ∈ Icc (0 : ℝ) 1) :
    pathTotal (cadlagPathOfAbsorptionRationalSample sample) time ≤ 1 := by
  unfold pathTotal
  by_cases hone : time = 1
  · subst time
    simpa only [cadlagPathOfAbsorptionRationalSample,
      reconstructedValue_one_eq_absorptionRationalSample_one hsample] using
      hsample.2.2.1 1
  · have htimeLt : time < 1 := lt_of_le_of_ne htime.2 hone
    obtain ⟨rational, htimeRational, hrationalOne⟩ :=
      exists_rat_btwn htimeLt
    calc
      (∑ coalition,
          (cadlagPathOfAbsorptionRationalSample sample).value
            time coalition) ≤
          ∑ coalition, (sample coalition rational : ℝ) :=
        Finset.sum_le_sum fun coalition _ ↦
          reconstructedValue_le_absorptionRationalSample sample coalition
            time rational htime.1 htimeRational
      _ ≤ 1 := hsample.2.2.1 rational

omit [DecidableEq ι] in
/-- The reconstructed rational-envelope path retains the lower clock bound
on total cumulative mass at every clock time. -/
theorem clock_le_pathTotal_cadlagPathOfAbsorptionRationalSample
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (time : ℝ) (htime : time ∈ Icc (0 : ℝ) 1) :
    time ≤ pathTotal (cadlagPathOfAbsorptionRationalSample sample) time := by
  unfold pathTotal
  by_contra hnot
  have htotalLt :
      (∑ coalition,
        (cadlagPathOfAbsorptionRationalSample sample).value
          time coalition) < time := lt_of_not_ge hnot
  obtain ⟨rational, htotalRational, hrationalTime⟩ :=
    exists_rat_btwn htotalLt
  have htotalNonneg : 0 ≤ ∑ coalition,
      (cadlagPathOfAbsorptionRationalSample sample).value
        time coalition :=
    Finset.sum_nonneg fun coalition _ ↦
      (cadlagPathOfAbsorptionRationalSample sample).value_mem
        time htime coalition |>.1
  have hrationalMem : (rational : ℝ) ∈ Icc 0 1 :=
    ⟨htotalNonneg.trans htotalRational.le,
      hrationalTime.le.trans htime.2⟩
  have hsampleTotal := hsample.2.1 rational hrationalMem
  have hsampleLe : (∑ coalition, (sample coalition rational : ℝ)) ≤
      ∑ coalition,
        (cadlagPathOfAbsorptionRationalSample sample).value
          time coalition :=
    Finset.sum_le_sum fun coalition _ ↦
      absorptionRationalSample_le_reconstructedValue hsample coalition
        rational time htime.1 hrationalTime.le
  linarith

/-- The clock-gap law is closed under rational-sample convergence to the
reconstructed càdlàg path. -/
theorem hasClockGapOn_pathTotal_cadlagPathOfAbsorptionRationalSample
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    {subsequence : ℕ → ℕ}
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (hconverges :
      Tendsto (absorptionPathRationalSample ∘ sequence ∘ subsequence)
        atTop (nhds sample)) :
    MathUE.HasClockGapOn
      (pathTotal (cadlagPathOfAbsorptionRationalSample sample)) (Icc 0 1) := by
  let limit := cadlagPathOfAbsorptionRationalSample sample
  intro time later htime hlater htimeLater hlaterGap
  rcases htimeLater.eq_or_lt with rfl | htimeLater
  · rfl
  · have hdense : Dense ((pathJumps limit)ᶜ) :=
      (countable_pathJumps limit).dense_compl ℝ
    obtain ⟨upper, hupperNotJump, hupper⟩ :=
      hdense.exists_between hlaterGap
    have hupperMem : upper ∈ Icc (0 : ℝ) 1 :=
      ⟨hlater.1.trans hupper.1.le,
        hupper.2.le.trans
          (pathTotal_cadlagPathOfAbsorptionRationalSample_le_one
            hsample time htime)⟩
    have htimeUpper : time < upper := htimeLater.trans hupper.1
    obtain ⟨approach, _happroachStrictAnti, happroachMem,
        happroachTendsto⟩ :=
      hdense.exists_seq_strictAnti_tendsto_of_lt (α := ℝ) htimeUpper
    have htotalTendsto_of_notJump {point : ℝ}
        (hpoint : point ∈ Icc (0 : ℝ) 1)
        (hpointNotJump : point ∉ pathJumps limit) :
        Tendsto (fun rank ↦
          pathTotal (sequence (subsequence rank)).1 point) atTop
          (nhds (pathTotal limit point)) := by
      unfold pathTotal
      apply tendsto_finsetSum
      intro coalition _
      apply tendsto_reconstructedValue_of_not_jump hsample hconverges
        coalition point hpoint
      by_contra hcoalition
      exact hpointNotJump ⟨hpoint, coalition, hcoalition⟩
    have hupperTendsto :=
      htotalTendsto_of_notJump hupperMem hupperNotJump
    have heq (stage : ℕ) :
        pathTotal limit upper = pathTotal limit (approach stage) := by
      have happroachIcc : approach stage ∈ Icc (0 : ℝ) 1 :=
        ⟨htime.1.trans (happroachMem stage).1.1.le,
          (happroachMem stage).1.2.le.trans hupperMem.2⟩
      have happroachTendsto :=
        htotalTendsto_of_notJump happroachIcc (happroachMem stage).2
      have hlimitMonotone : pathTotal limit time ≤
          pathTotal limit (approach stage) :=
        monotoneOn_pathTotal limit htime happroachIcc
          (happroachMem stage).1.1.le
      have hstrict : upper < pathTotal limit (approach stage) :=
        hupper.2.trans_le hlimitMonotone
      have heventually : ∀ᶠ rank in atTop,
          pathTotal (sequence (subsequence rank)).1 upper =
            pathTotal (sequence (subsequence rank)).1 (approach stage) := by
        filter_upwards [happroachTendsto.eventually_const_lt hstrict]
          with rank hrank
        exact pathTotal_eq_of_le_of_lt_pathTotal
          (sequence (subsequence rank)) happroachIcc hupperMem
            (happroachMem stage).1.2.le hrank
      have hupperToApproach : Tendsto (fun rank ↦
          pathTotal (sequence (subsequence rank)).1 upper) atTop
          (nhds (pathTotal limit (approach stage))) :=
        happroachTendsto.congr'
          (heventually.mono fun _ hrank ↦ hrank.symm)
      exact tendsto_nhds_unique hupperTendsto hupperToApproach
    have happroachWithin : Tendsto approach atTop
        (nhdsWithin time (Icc time 1)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨happroachTendsto,
        Filter.Eventually.of_forall fun stage ↦
          ⟨(happroachMem stage).1.1.le,
            (happroachMem stage).1.2.le.trans hupperMem.2⟩⟩
    have hright : Tendsto (fun stage ↦ pathTotal limit (approach stage))
        atTop (nhds (pathTotal limit time)) := by
      unfold pathTotal
      apply tendsto_finsetSum
      intro coalition _
      exact (limit.right_continuous coalition time htime).comp
        happroachWithin
    have hupperEq : pathTotal limit upper = pathTotal limit time := by
      have hconstant : Tendsto (fun _ : ℕ ↦ pathTotal limit upper) atTop
          (nhds (pathTotal limit upper)) := tendsto_const_nhds
      have hconstantLimit : Tendsto
          (fun _ : ℕ ↦ pathTotal limit upper) atTop
          (nhds (pathTotal limit time)) :=
        hright.congr' (Filter.Eventually.of_forall fun stage ↦ (heq stage).symm)
      exact tendsto_nhds_unique hconstant hconstantLimit
    apply le_antisymm
    · exact (monotoneOn_pathTotal limit hlater hupperMem hupper.1.le).trans_eq
        hupperEq
    · exact monotoneOn_pathTotal limit htime hlater htimeLater.le

/-- The reconstructed path has constant total mass on each component outside
its jump and continuous-clock boundary sets. -/
theorem hasConstantTotalOnGapComponents_cadlagPathOfAbsorptionRationalSample
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    {subsequence : ℕ → ℕ}
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (hconverges :
      Tendsto (absorptionPathRationalSample ∘ sequence ∘ subsequence)
        atTop (nhds sample)) :
    HasConstantTotalOnGapComponents
      (cadlagPathOfAbsorptionRationalSample sample) :=
  hasConstantTotalOnGapComponents_of_clockGap
    (cadlagPathOfAbsorptionRationalSample sample)
    (clock_le_pathTotal_cadlagPathOfAbsorptionRationalSample hsample)
    (pathTotal_cadlagPathOfAbsorptionRationalSample_le_one hsample)
    (hasClockGapOn_pathTotal_cadlagPathOfAbsorptionRationalSample
      hsample hconverges)

/-- Rational-sample convergence is weak convergence to the reconstructed
càdlàg path. -/
theorem weaklyConvergesToCadlag_of_rationalSample_tendsto
    {sequence : ℕ → AbsorptionPath (ι := ι)}
    {sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1}
    {subsequence : ℕ → ℕ}
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (hconverges :
      Tendsto (absorptionPathRationalSample ∘ sequence ∘ subsequence)
        atTop (nhds sample)) :
    WeaklyConvergesAbsorptionPathsToCadlag (sequence ∘ subsequence)
      (cadlagPathOfAbsorptionRationalSample sample) := by
  intro time htime hnotJump
  rw [tendsto_pi_nhds]
  intro coalition
  apply tendsto_reconstructedValue_of_not_jump hsample hconverges
    coalition time htime
  by_contra hcoalition
  exact hnotJump ⟨htime, coalition, hcoalition⟩

end GameTheory.QuittingAbsorptionPath
