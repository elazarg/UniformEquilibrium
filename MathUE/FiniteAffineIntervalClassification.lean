/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.FiniteAffineIntervalFeasibility

/-!
# Finite affine interval obstruction classification

This module extracts the size-at-most-two obstruction behind finite affine
interval feasibility.  It then classifies a system made of phase rows and
the two rows of one bounded affine closing seam: the only possibilities are
a phase singleton, a phase--phase crossing, or a phase--seam crossing.

The module also records the scalar box calculation used before applying the
classification.  Exact propagation by reward-bounded affine maps preserves
the symmetric reward interval, so the induced canonical box rows are
nonpositive at both normalized endpoints and can be deleted.
-/

noncomputable section

namespace Math

variable {κ : Type*}

/-- One affine row is positive throughout the normalized unit interval. -/
def IsAffineIntervalSingletonObstruction
    (lower upper : κ → ℝ) (index : κ) : Prop :=
  0 < lower index ∧ 0 < upper index

/-- A lower-bound row and an upper-bound row cross in the infeasible
orientation.  Each row separately has a feasible endpoint. -/
def IsAffineIntervalCrossing
    (lower upper : κ → ℝ) (lowerIndex upperIndex : κ) : Prop :=
  0 < lower lowerIndex ∧ upper lowerIndex ≤ 0 ∧
    lower upperIndex ≤ 0 ∧ 0 < upper upperIndex ∧
    upper lowerIndex * lower upperIndex <
      lower lowerIndex * upper upperIndex

/-- Failure of finite affine interval feasibility has a certificate using
either one everywhere-positive row or two crossed rows. -/
theorem not_finiteAffineIntervalFeasible_iff_exists_obstruction
    [Fintype κ] (lower upper : κ → ℝ) :
    ¬IsFiniteAffineIntervalFeasible lower upper ↔
      (∃ index, IsAffineIntervalSingletonObstruction lower upper index) ∨
        ∃ lowerIndex upperIndex,
          IsAffineIntervalCrossing lower upper lowerIndex upperIndex := by
  classical
  rw [finiteAffineIntervalFeasible_iff]
  constructor
  · intro hcriterion
    unfold FiniteAffineIntervalCriterion at hcriterion
    by_cases hendpoint : ∀ index, lower index ≤ 0 ∨ upper index ≤ 0
    · right
      have hcrossFailure : ¬∀ lowerIndex upperIndex,
          0 < lower lowerIndex → upper lowerIndex ≤ 0 →
          lower upperIndex ≤ 0 → 0 < upper upperIndex →
          lower lowerIndex * upper upperIndex ≤
            upper lowerIndex * lower upperIndex := by
        exact fun hcross => hcriterion ⟨hendpoint, hcross⟩
      push Not at hcrossFailure
      obtain ⟨lowerIndex, upperIndex, hlowerPos, hlowerUpper,
          hupperLower, hupperPos, hcross⟩ := hcrossFailure
      exact ⟨lowerIndex, upperIndex, hlowerPos, hlowerUpper,
        hupperLower, hupperPos, hcross⟩
    · left
      push Not at hendpoint
      obtain ⟨index, hlower, hupper⟩ := hendpoint
      exact ⟨index, hlower, hupper⟩
  · intro hobstruction hcriterion
    rcases hobstruction with hsingle | hcross
    · obtain ⟨index, hlower, hupper⟩ := hsingle
      rcases hcriterion.1 index with hlowerNonpos | hupperNonpos
      · exact (not_lt_of_ge hlowerNonpos) hlower
      · exact (not_lt_of_ge hupperNonpos) hupper
    · obtain ⟨lowerIndex, upperIndex, hlowerPos, hlowerUpper,
          hupperLower, hupperPos, hcross⟩ := hcross
      exact (not_le_of_gt hcross) (hcriterion.2 lowerIndex upperIndex
        hlowerPos hlowerUpper hupperLower hupperPos)

/-! ## Redundant endpoint rows -/

/-- Appending a finite family of rows which is nonpositive at both endpoints
does not change affine interval feasibility. -/
theorem finiteAffineIntervalFeasible_sum_iff_of_right_nonpositive
    {β : Type*} [Fintype β]
    (lower upper : κ → ℝ) (extraLower extraUpper : β → ℝ)
    (hextraLower : ∀ index, extraLower index ≤ 0)
    (hextraUpper : ∀ index, extraUpper index ≤ 0) :
    IsFiniteAffineIntervalFeasible
        (Sum.elim lower extraLower) (Sum.elim upper extraUpper) ↔
      IsFiniteAffineIntervalFeasible lower upper := by
  constructor
  · rintro ⟨weight, hweight0, hweight1, hrow⟩
    exact ⟨weight, hweight0, hweight1, fun index => hrow (Sum.inl index)⟩
  · rintro ⟨weight, hweight0, hweight1, hrow⟩
    refine ⟨weight, hweight0, hweight1, ?_⟩
    rintro (index | index)
    · exact hrow index
    · exact add_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (by linarith) (hextraLower index))
        (mul_nonpos_of_nonneg_of_nonpos hweight0 (hextraUpper index))

/-! ## Exact reward-bounded propagation -/

/-- One scalar affine Bellman step. -/
def scalarAffineStep (offset slope value : ℝ) : ℝ :=
  offset + slope * value

/-- Exact backward propagation through a list of scalar affine steps. -/
def scalarAffinePropagation
    (offset slope : κ → ℝ) : List κ → ℝ → ℝ
  | [], value => value
  | index :: rest, value =>
      scalarAffineStep (offset index) (slope index)
        (scalarAffinePropagation offset slope rest value)

/-- Constant term of an exactly propagated affine word. -/
def scalarAffinePropagationOffset
    (offset slope : κ → ℝ) : List κ → ℝ
  | [] => 0
  | index :: rest =>
      offset index + slope index *
        scalarAffinePropagationOffset offset slope rest

/-- Slope of an exactly propagated affine word. -/
def scalarAffinePropagationSlope (slope : κ → ℝ) : List κ → ℝ
  | [] => 1
  | index :: rest =>
      slope index * scalarAffinePropagationSlope slope rest

/-- Exact propagation is the affine map given by its recursively aggregated
constant term and slope. -/
theorem scalarAffinePropagation_eq_aggregate
    (offset slope : κ → ℝ) (indices : List κ) (value : ℝ) :
    scalarAffinePropagation offset slope indices value =
      scalarAffinePropagationOffset offset slope indices +
        scalarAffinePropagationSlope slope indices * value := by
  induction indices with
  | nil => simp [scalarAffinePropagation, scalarAffinePropagationOffset,
      scalarAffinePropagationSlope]
  | cons index rest ih =>
      simp only [scalarAffinePropagation, scalarAffinePropagationOffset,
        scalarAffinePropagationSlope, scalarAffineStep, ih]
      ring

/-- The aggregate slope of a word of unit-interval slopes remains in the
unit interval. -/
theorem scalarAffinePropagationSlope_mem_unitInterval
    (slope : κ → ℝ) (hslope0 : ∀ index, 0 ≤ slope index)
    (hslope1 : ∀ index, slope index ≤ 1) (indices : List κ) :
    0 ≤ scalarAffinePropagationSlope slope indices ∧
      scalarAffinePropagationSlope slope indices ≤ 1 := by
  induction indices with
  | nil => simp [scalarAffinePropagationSlope]
  | cons index rest ih =>
      simp only [scalarAffinePropagationSlope]
      exact ⟨mul_nonneg (hslope0 index) ih.1,
        mul_le_one₀ (hslope1 index) ih.1 ih.2⟩

/-- Reward bounds are stable under affine aggregation, with the sharp
aggregate factor `1 - aggregateSlope`. -/
theorem abs_scalarAffinePropagationOffset_le_bound
    {M : ℝ} (offset slope : κ → ℝ)
    (hslope0 : ∀ index, 0 ≤ slope index)
    (hoffset : ∀ index, |offset index| ≤ M * (1 - slope index))
    (indices : List κ) :
    |scalarAffinePropagationOffset offset slope indices| ≤
      M * (1 - scalarAffinePropagationSlope slope indices) := by
  induction indices with
  | nil => simp [scalarAffinePropagationOffset,
      scalarAffinePropagationSlope]
  | cons index rest ih =>
      calc
        |scalarAffinePropagationOffset offset slope (index :: rest)| ≤
            |offset index| +
              |slope index *
                scalarAffinePropagationOffset offset slope rest| := by
              simpa [scalarAffinePropagationOffset] using
                abs_add_le (offset index)
                  (slope index *
                    scalarAffinePropagationOffset offset slope rest)
        _ ≤ M * (1 - slope index) +
              slope index *
                (M * (1 - scalarAffinePropagationSlope slope rest)) := by
            apply add_le_add (hoffset index)
            rw [abs_mul, abs_of_nonneg (hslope0 index)]
            exact mul_le_mul_of_nonneg_left ih (hslope0 index)
        _ = M *
              (1 - scalarAffinePropagationSlope slope (index :: rest)) := by
            simp only [scalarAffinePropagationSlope]
            ring

/-- A reward-bounded affine Bellman step preserves the symmetric reward
interval. -/
theorem abs_scalarAffineStep_le_bound
    {M offset slope value : ℝ}
    (hslope0 : 0 ≤ slope) (_hslope1 : slope ≤ 1)
    (hoffset : |offset| ≤ M * (1 - slope))
    (hvalue : |value| ≤ M) :
    |scalarAffineStep offset slope value| ≤ M := by
  calc
    |scalarAffineStep offset slope value| ≤
        |offset| + |slope * value| := by
          simpa [scalarAffineStep] using abs_add_le offset (slope * value)
    _ ≤ M * (1 - slope) + slope * M := by
      gcongr
      rw [abs_mul, abs_of_nonneg hslope0]
      exact mul_le_mul_of_nonneg_left hvalue hslope0
    _ = M := by ring

/-- Every exactly propagated scalar value stays in the canonical reward box.
The list can be any finite subword, so this also controls all intermediate
suffix values. -/
theorem abs_scalarAffinePropagation_le_bound
    {M : ℝ} (offset slope : κ → ℝ)
    (hslope0 : ∀ index, 0 ≤ slope index)
    (hslope1 : ∀ index, slope index ≤ 1)
    (hoffset : ∀ index, |offset index| ≤ M * (1 - slope index))
    (indices : List κ) {value : ℝ} (hvalue : |value| ≤ M) :
    |scalarAffinePropagation offset slope indices value| ≤ M := by
  induction indices with
  | nil => exact hvalue
  | cons index rest ih =>
      exact abs_scalarAffineStep_le_bound
        (hslope0 index) (hslope1 index) (hoffset index) ih

/-- The two orientations of a symmetric payoff-box row. -/
inductive SymmetricAffineBoxSide
  | lower
  | upper
  deriving DecidableEq, Fintype

/-- A box row for one propagated value, written in nonpositive form. -/
def scalarAffinePropagationBoxRow
    (M : ℝ) (offset slope : κ → ℝ) (indices : List κ)
    (side : SymmetricAffineBoxSide) (value : ℝ) : ℝ :=
  match side with
  | .lower => -M - scalarAffinePropagation offset slope indices value
  | .upper => scalarAffinePropagation offset slope indices value - M

/-- Every canonical box row generated by exact affine propagation is
nonpositive throughout the cut interval. -/
theorem scalarAffinePropagationBoxRow_nonpositive
    {M : ℝ} (offset slope : κ → ℝ)
    (hslope0 : ∀ index, 0 ≤ slope index)
    (hslope1 : ∀ index, slope index ≤ 1)
    (hoffset : ∀ index, |offset index| ≤ M * (1 - slope index))
    (indices : List κ) (side : SymmetricAffineBoxSide)
    {value : ℝ} (hvalue : |value| ≤ M) :
    scalarAffinePropagationBoxRow M offset slope indices side value ≤ 0 := by
  have hbound := abs_scalarAffinePropagation_le_bound offset slope
    hslope0 hslope1 hoffset indices hvalue
  have hinterval :
      -M ≤ scalarAffinePropagation offset slope indices value ∧
        scalarAffinePropagation offset slope indices value ≤ M :=
    (abs_le).mp hbound
  cases side <;> simp only [scalarAffinePropagationBoxRow] <;> linarith

/-- In particular, exact canonical box rows are nonpositive at both
normalization endpoints. -/
theorem scalarAffinePropagationBoxRow_endpoints_nonpositive
    {M : ℝ} (hM : 0 ≤ M) (offset slope : κ → ℝ)
    (hslope0 : ∀ index, 0 ≤ slope index)
    (hslope1 : ∀ index, slope index ≤ 1)
    (hoffset : ∀ index, |offset index| ≤ M * (1 - slope index))
    (indices : List κ) (side : SymmetricAffineBoxSide) :
    scalarAffinePropagationBoxRow M offset slope indices side (-M) ≤ 0 ∧
      scalarAffinePropagationBoxRow M offset slope indices side M ≤ 0 := by
  constructor
  · apply scalarAffinePropagationBoxRow_nonpositive offset slope
      hslope0 hslope1 hoffset indices side
    simp [abs_of_nonneg hM]
  · apply scalarAffinePropagationBoxRow_nonpositive offset slope
      hslope0 hslope1 hoffset indices side
    simp [abs_of_nonneg hM]

/-- Appending any finite selection of canonical boxes for exactly propagated
values does not change feasibility of the original endpoint rows. -/
theorem finiteAffineIntervalFeasible_with_propagatedBoxes_iff
    {γ β : Type*} [Fintype γ] [Fintype β]
    {M : ℝ} (hM : 0 ≤ M) (offset slope : κ → ℝ)
    (hslope0 : ∀ index, 0 ≤ slope index)
    (hslope1 : ∀ index, slope index ≤ 1)
    (hoffset : ∀ index, |offset index| ≤ M * (1 - slope index))
    (phaseLower phaseUpper : γ → ℝ) (indices : β → List κ)
    (side : β → SymmetricAffineBoxSide) :
    IsFiniteAffineIntervalFeasible
        (Sum.elim phaseLower fun box =>
          scalarAffinePropagationBoxRow M offset slope
            (indices box) (side box) (-M))
        (Sum.elim phaseUpper fun box =>
          scalarAffinePropagationBoxRow M offset slope
            (indices box) (side box) M) ↔
      IsFiniteAffineIntervalFeasible phaseLower phaseUpper := by
  apply finiteAffineIntervalFeasible_sum_iff_of_right_nonpositive
  · intro box
    exact (scalarAffinePropagationBoxRow_endpoints_nonpositive
      hM offset slope hslope0 hslope1 hoffset
      (indices box) (side box)).1
  · intro box
    exact (scalarAffinePropagationBoxRow_endpoints_nonpositive
      hM offset slope hslope0 hslope1 hoffset
      (indices box) (side box)).2

/-! ## Closing seams -/

/-- The two signs of the closing mismatch between a cut value and an affine
return map. -/
inductive AffineClosingSeamSide
  | cutMinusReturn
  | returnMinusCut
  deriving DecidableEq, Fintype

/-- One of the two closing-seam rows at a scalar cut value. -/
def affineClosingSeamRow
    (offset slope error : ℝ) (side : AffineClosingSeamSide)
    (value : ℝ) : ℝ :=
  match side with
  | .cutMinusReturn => value - scalarAffineStep offset slope value - error
  | .returnMinusCut => scalarAffineStep offset slope value - value - error

/-- Left endpoint of a closing-seam row on the symmetric reward interval. -/
def affineClosingSeamLower
    (M offset slope error : ℝ) (side : AffineClosingSeamSide) : ℝ :=
  affineClosingSeamRow offset slope error side (-M)

/-- Right endpoint of a closing-seam row on the symmetric reward interval. -/
def affineClosingSeamUpper
    (M offset slope error : ℝ) (side : AffineClosingSeamSide) : ℝ :=
  affineClosingSeamRow offset slope error side M

/-- A bounded scalar affine return map has a fixed point in the symmetric
reward interval. -/
theorem exists_affine_fixedPoint_mem_symmetricInterval
    {M offset slope : ℝ} (hM : 0 ≤ M)
    (hslope0 : 0 ≤ slope) (hslope1 : slope ≤ 1)
    (hoffset : |offset| ≤ M * (1 - slope)) :
    ∃ value, value ∈ Set.Icc (-M) M ∧
      scalarAffineStep offset slope value = value := by
  rcases hslope1.eq_or_lt with hslopeEq | hslopeLt
  · subst slope
    have hoffsetZero : offset = 0 := by
      have : |offset| ≤ 0 := by simpa using hoffset
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg offset))
    exact ⟨0, by simp [hM], by simp [scalarAffineStep, hoffsetZero]⟩
  · let value := offset / (1 - slope)
    have hden : 0 < 1 - slope := by linarith
    have habs : |value| ≤ M := by
      dsimp only [value]
      rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
      exact hoffset
    have hmem : value ∈ Set.Icc (-M) M := (abs_le.mp habs)
    refine ⟨value, hmem, ?_⟩
    dsimp only [value, scalarAffineStep]
    field_simp
    ring

/-- Every point of a symmetric interval is the affine image of a unit
weight, including the degenerate interval at `M = 0`. -/
theorem exists_unitWeight_eq_of_mem_symmetricInterval
    {M value : ℝ} (hM : 0 ≤ M) (hvalue : value ∈ Set.Icc (-M) M) :
    ∃ weight, 0 ≤ weight ∧ weight ≤ 1 ∧
      (1 - weight) * (-M) + weight * M = value := by
  rcases hM.eq_or_lt with hMzero | hMpos
  · subst M
    have hvalueZero : value = 0 := by simpa using hvalue
    exact ⟨0, by simp [hvalueZero]⟩
  · let weight := (value + M) / (2 * M)
    have hden : 0 < 2 * M := by positivity
    have hweight0 : 0 ≤ weight := by
      exact div_nonneg (by linarith [hvalue.1]) hden.le
    have hweight1 : weight ≤ 1 := by
      rw [div_le_one hden]
      linarith [hvalue.2]
    refine ⟨weight, hweight0, hweight1, ?_⟩
    dsimp only [weight]
    field_simp
    ring

/-- The two closing-seam rows of a reward-bounded affine return map are
jointly feasible for every nonnegative seam error. -/
theorem affineClosingSeam_feasible
    {M offset slope error : ℝ} (hM : 0 ≤ M)
    (hslope0 : 0 ≤ slope) (hslope1 : slope ≤ 1)
    (hoffset : |offset| ≤ M * (1 - slope)) (herror : 0 ≤ error) :
    IsFiniteAffineIntervalFeasible
      (affineClosingSeamLower M offset slope error)
      (affineClosingSeamUpper M offset slope error) := by
  obtain ⟨value, hvalue, hfixed⟩ :=
    exists_affine_fixedPoint_mem_symmetricInterval
      hM hslope0 hslope1 hoffset
  obtain ⟨weight, hweight0, hweight1, hweight⟩ :=
    exists_unitWeight_eq_of_mem_symmetricInterval hM hvalue
  refine ⟨weight, hweight0, hweight1, ?_⟩
  intro side
  have haffine :
      (1 - weight) * affineClosingSeamLower M offset slope error side +
          weight * affineClosingSeamUpper M offset slope error side =
        affineClosingSeamRow offset slope error side value := by
    rw [← hweight]
    cases side <;>
      simp only [affineClosingSeamLower, affineClosingSeamUpper,
        affineClosingSeamRow, scalarAffineStep] <;>
      ring
  rw [haffine]
  cases side <;>
    simp only [affineClosingSeamRow, hfixed, sub_self, zero_sub] <;>
    linarith

/-- The affine closing seam obtained by exactly composing any finite word of
reward-bounded affine steps is jointly feasible. -/
theorem scalarAffinePropagationClosingSeam_feasible
    {M error : ℝ} (hM : 0 ≤ M) (offset slope : κ → ℝ)
    (hslope0 : ∀ index, 0 ≤ slope index)
    (hslope1 : ∀ index, slope index ≤ 1)
    (hoffset : ∀ index, |offset index| ≤ M * (1 - slope index))
    (herror : 0 ≤ error) (indices : List κ) :
    IsFiniteAffineIntervalFeasible
      (affineClosingSeamLower M
        (scalarAffinePropagationOffset offset slope indices)
        (scalarAffinePropagationSlope slope indices) error)
      (affineClosingSeamUpper M
        (scalarAffinePropagationOffset offset slope indices)
        (scalarAffinePropagationSlope slope indices) error) := by
  have hslopeAggregate := scalarAffinePropagationSlope_mem_unitInterval
    slope hslope0 hslope1 indices
  exact affineClosingSeam_feasible hM hslopeAggregate.1 hslopeAggregate.2
    (abs_scalarAffinePropagationOffset_le_bound
      offset slope hslope0 hoffset indices) herror

/-! ## Phase/seam classification -/

/-- Endpoint arrays obtained by appending the two closing-seam rows to a
finite family of phase rows. -/
def phaseClosingSeamLower
    (phaseLower : κ → ℝ) (M offset slope error : ℝ) :
    Sum κ AffineClosingSeamSide → ℝ :=
  Sum.elim phaseLower (affineClosingSeamLower M offset slope error)

def phaseClosingSeamUpper
    (phaseUpper : κ → ℝ) (M offset slope error : ℝ) :
    Sum κ AffineClosingSeamSide → ℝ :=
  Sum.elim phaseUpper (affineClosingSeamUpper M offset slope error)

/-- A phase row which is positive throughout the cut interval. -/
def HasPhaseSingletonObstruction
    (phaseLower phaseUpper : κ → ℝ) : Prop :=
  ∃ index,
    IsAffineIntervalSingletonObstruction phaseLower phaseUpper index

/-- Two phase rows which cross. -/
def HasPhasePhaseCrossing
    (phaseLower phaseUpper : κ → ℝ) : Prop :=
  ∃ lowerIndex upperIndex,
    IsAffineIntervalCrossing phaseLower phaseUpper lowerIndex upperIndex

/-- One phase row crosses one of the two closing-seam rows, in either
orientation. -/
def HasPhaseClosingSeamCrossing
    (phaseLower phaseUpper : κ → ℝ)
    (M offset slope error : ℝ) : Prop :=
  let lower := phaseClosingSeamLower phaseLower M offset slope error
  let upper := phaseClosingSeamUpper phaseUpper M offset slope error
  (∃ phase seam,
      IsAffineIntervalCrossing lower upper (Sum.inl phase) (Sum.inr seam)) ∨
    ∃ seam phase,
      IsAffineIntervalCrossing lower upper (Sum.inr seam) (Sum.inl phase)

/-- **Exact scalar phase/seam classification.**  Once exact nonseam
propagation has reduced the problem to one cut scalar, a reward-bounded
closing affine map leaves exactly three possible minimal infeasibility
patterns: one phase row, two crossed phase rows, or a phase--seam crossing. -/
theorem not_phaseClosingSeamFeasible_iff
    [Fintype κ] (phaseLower phaseUpper : κ → ℝ)
    {M offset slope error : ℝ} (hM : 0 ≤ M)
    (hslope0 : 0 ≤ slope) (hslope1 : slope ≤ 1)
    (hoffset : |offset| ≤ M * (1 - slope)) (herror : 0 ≤ error) :
    (¬IsFiniteAffineIntervalFeasible
      (phaseClosingSeamLower phaseLower M offset slope error)
      (phaseClosingSeamUpper phaseUpper M offset slope error)) ↔
      HasPhaseSingletonObstruction phaseLower phaseUpper ∨
        HasPhasePhaseCrossing phaseLower phaseUpper ∨
          HasPhaseClosingSeamCrossing phaseLower phaseUpper
            M offset slope error := by
  classical
  let lower := phaseClosingSeamLower phaseLower M offset slope error
  let upper := phaseClosingSeamUpper phaseUpper M offset slope error
  have hseam := affineClosingSeam_feasible
    hM hslope0 hslope1 hoffset herror
  have hseamCriterion :=
    (finiteAffineIntervalFeasible_iff _ _).mp hseam
  rw [not_finiteAffineIntervalFeasible_iff_exists_obstruction]
  constructor
  · intro hobstruction
    rcases hobstruction with ⟨index, hsingle⟩ | ⟨lowerIndex, upperIndex, hcross⟩
    · rcases index with phase | seam
      · exact Or.inl ⟨phase, hsingle⟩
      · exfalso
        rcases hseamCriterion.1 seam with hlower | hupper
        · exact (not_lt_of_ge hlower) hsingle.1
        · exact (not_lt_of_ge hupper) hsingle.2
    · rcases lowerIndex with lowerPhase | lowerSeam <;>
        rcases upperIndex with upperPhase | upperSeam
      · exact Or.inr (Or.inl ⟨lowerPhase, upperPhase, hcross⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨lowerPhase, upperSeam, hcross⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨lowerSeam, upperPhase, hcross⟩))
      · exfalso
        exact (not_le_of_gt hcross.2.2.2.2) (hseamCriterion.2
          lowerSeam upperSeam hcross.1 hcross.2.1 hcross.2.2.1
          hcross.2.2.2.1)
  · intro hclassified
    rcases hclassified with hsingle | hphaseCross | hphaseSeam
    · obtain ⟨phase, hphase⟩ := hsingle
      exact Or.inl ⟨Sum.inl phase, hphase⟩
    · obtain ⟨lowerPhase, upperPhase, hcross⟩ := hphaseCross
      exact Or.inr ⟨Sum.inl lowerPhase, Sum.inl upperPhase, hcross⟩
    · rcases hphaseSeam with hforward | hbackward
      · obtain ⟨phase, seam, hcross⟩ := hforward
        exact Or.inr ⟨Sum.inl phase, Sum.inr seam, hcross⟩
      · obtain ⟨seam, phase, hcross⟩ := hbackward
        exact Or.inr ⟨Sum.inr seam, Sum.inl phase, hcross⟩

/-- Direct exact-propagation form of the phase/seam classification.  The
closing affine parameters are computed from an arbitrary finite word of
reward-bounded scalar steps. -/
theorem not_phasePropagationClosingSeamFeasible_iff
    {σ : Type*} (phaseLower phaseUpper : κ → ℝ)
    [Fintype κ] {M error : ℝ} (hM : 0 ≤ M)
    (offset slope : σ → ℝ)
    (hslope0 : ∀ index, 0 ≤ slope index)
    (hslope1 : ∀ index, slope index ≤ 1)
    (hoffset : ∀ index, |offset index| ≤ M * (1 - slope index))
    (herror : 0 ≤ error) (indices : List σ) :
    (¬IsFiniteAffineIntervalFeasible
      (phaseClosingSeamLower phaseLower M
        (scalarAffinePropagationOffset offset slope indices)
        (scalarAffinePropagationSlope slope indices) error)
      (phaseClosingSeamUpper phaseUpper M
        (scalarAffinePropagationOffset offset slope indices)
        (scalarAffinePropagationSlope slope indices) error)) ↔
      HasPhaseSingletonObstruction phaseLower phaseUpper ∨
        HasPhasePhaseCrossing phaseLower phaseUpper ∨
          HasPhaseClosingSeamCrossing phaseLower phaseUpper M
            (scalarAffinePropagationOffset offset slope indices)
            (scalarAffinePropagationSlope slope indices) error := by
  have hslopeAggregate := scalarAffinePropagationSlope_mem_unitInterval
    slope hslope0 hslope1 indices
  exact not_phaseClosingSeamFeasible_iff phaseLower phaseUpper hM
    hslopeAggregate.1 hslopeAggregate.2
    (abs_scalarAffinePropagationOffset_le_bound
      offset slope hslope0 hoffset indices) herror

/-- Full exact-propagation normal form.  Even if arbitrary intermediate
canonical box rows are retained, infeasibility is equivalent to the same
three phase/seam obstruction types; the box rows contribute no certificate. -/
theorem not_phasePropagationClosingSeamWithBoxesFeasible_iff
    {σ β : Type*} [Fintype κ] [Fintype β]
    (phaseLower phaseUpper : κ → ℝ)
    {M error : ℝ} (hM : 0 ≤ M) (offset slope : σ → ℝ)
    (hslope0 : ∀ index, 0 ≤ slope index)
    (hslope1 : ∀ index, slope index ≤ 1)
    (hoffset : ∀ index, |offset index| ≤ M * (1 - slope index))
    (herror : 0 ≤ error) (indices : List σ)
    (boxIndices : β → List σ) (boxSide : β → SymmetricAffineBoxSide) :
    let aggregateOffset :=
      scalarAffinePropagationOffset offset slope indices
    let aggregateSlope := scalarAffinePropagationSlope slope indices
    (¬IsFiniteAffineIntervalFeasible
      (Sum.elim
        (phaseClosingSeamLower phaseLower M
          aggregateOffset aggregateSlope error)
        (fun box => scalarAffinePropagationBoxRow M offset slope
          (boxIndices box) (boxSide box) (-M)))
      (Sum.elim
        (phaseClosingSeamUpper phaseUpper M
          aggregateOffset aggregateSlope error)
        (fun box => scalarAffinePropagationBoxRow M offset slope
          (boxIndices box) (boxSide box) M))) ↔
      HasPhaseSingletonObstruction phaseLower phaseUpper ∨
        HasPhasePhaseCrossing phaseLower phaseUpper ∨
          HasPhaseClosingSeamCrossing phaseLower phaseUpper M
            aggregateOffset aggregateSlope error := by
  dsimp only
  rw [finiteAffineIntervalFeasible_with_propagatedBoxes_iff
    hM offset slope hslope0 hslope1 hoffset
    (phaseClosingSeamLower phaseLower M
      (scalarAffinePropagationOffset offset slope indices)
      (scalarAffinePropagationSlope slope indices) error)
    (phaseClosingSeamUpper phaseUpper M
      (scalarAffinePropagationOffset offset slope indices)
      (scalarAffinePropagationSlope slope indices) error)
    boxIndices boxSide]
  exact not_phasePropagationClosingSeamFeasible_iff
    phaseLower phaseUpper hM offset slope hslope0 hslope1
      hoffset herror indices

end Math
