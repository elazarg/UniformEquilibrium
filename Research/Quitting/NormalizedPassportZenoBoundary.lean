/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Research.Quitting.NormalizedPassportSingleDensityToll

/-!
# Scalar Zeno boundary and a conditional density rank

The concrete scalar system in this file realizes the normalized-passport
ledger, the all-root absorption toll, and saturated half-density transitions
at every finite stage while its debt remains strictly above a named tail debt.
It is an abstract compact scalar prefix system, not a quitting game.

The final section proves that a renewable absolute density floor would turn
the same half-density transition into a strict natural-valued rank.  No such
renewable source or floor is produced for the Fin4 construction here.
-/

noncomputable section

namespace Math

open Set

/-- Scalar points with marked mass between zero and the initial mass. -/
abbrev NormalizedPassportZenoPoint (massBound : ℝ) := Set.Icc (0 : ℝ) massBound

/-- Scalar product-root absorption parameters. -/
abbrev NormalizedPassportZenoAbsorption := Set.Icc (0 : ℝ) 1

namespace NormalizedPassportZeno

variable {minimumDebt sourceDebt massBound gap : ℝ}

/-- Constant whole debt on the scalar system. -/
def debt (_point : NormalizedPassportZenoPoint massBound) : ℝ := sourceDebt

/-- Constant named tail debt on the scalar system. -/
def tailDebt (_point : NormalizedPassportZenoPoint massBound) : ℝ := minimumDebt

/-- Marked-mass coordinate. -/
def markedMass (point : NormalizedPassportZenoPoint massBound) : ℝ := point

/-- Gain coordinate with one fixed density. -/
def actualGain (point : NormalizedPassportZenoPoint massBound) : ℝ :=
  gap * point

/-- Scalar prefix action with joint Continue mass `1 - absorption`. -/
def prefixAction
    (absorption : NormalizedPassportZenoAbsorption)
    (point : NormalizedPassportZenoPoint massBound) :
    NormalizedPassportZenoPoint massBound :=
  ⟨(1 - (absorption : ℝ)) * (point : ℝ), by
    constructor
    · exact mul_nonneg (by linarith [absorption.property.2]) point.property.1
    · exact (mul_le_of_le_one_left point.property.1
        (by linarith [absorption.property.1])).trans point.property.2⟩

/-- Scalar root defect. -/
def rootDefect
    (absorption : NormalizedPassportZenoAbsorption)
    (_point : NormalizedPassportZenoPoint massBound) : ℝ :=
  (absorption : ℝ) * sourceDebt

/-- Composition of two scalar absorption parameters. -/
def combine
    (first second : NormalizedPassportZenoAbsorption) :
    NormalizedPassportZenoAbsorption :=
  ⟨1 - (1 - (first : ℝ)) * (1 - (second : ℝ)), by
    constructor
    · have hfirst : 0 ≤ 1 - (first : ℝ) := by linarith [first.property.2]
      have hsecond : 0 ≤ 1 - (second : ℝ) := by linarith [second.property.2]
      have hfirstLe : 1 - (first : ℝ) ≤ 1 := by linarith [first.property.1]
      have hsecondLe : 1 - (second : ℝ) ≤ 1 := by linarith [second.property.1]
      nlinarith [mul_nonneg hfirst hsecond,
        mul_le_one₀ hfirstLe hsecond hsecondLe]
    · nlinarith [mul_nonneg
        (by linarith [first.property.2] : 0 ≤ 1 - (first : ℝ))
        (by linarith [second.property.2] : 0 ≤ 1 - (second : ℝ))]⟩

/-- Prefixing is continuous jointly in absorption and scalar point. -/
theorem continuous_prefixAction :
    Continuous (fun pair : NormalizedPassportZenoAbsorption ×
        NormalizedPassportZenoPoint massBound ↦ prefixAction pair.1 pair.2) := by
  apply Continuous.subtype_mk
  fun_prop

/-- Scalar prefix composition is literal. -/
theorem prefixAction_prefixAction
    (first second : NormalizedPassportZenoAbsorption)
    (point : NormalizedPassportZenoPoint massBound) :
    prefixAction first (prefixAction second point) =
      prefixAction (combine first second) point := by
  apply Subtype.ext
  simp only [prefixAction, combine]
  ring

/-- Exact whole-debt prefix ledger. -/
theorem debt_prefix_eq_continue_mul_add_defect
    (absorption : NormalizedPassportZenoAbsorption)
    (point : NormalizedPassportZenoPoint massBound) :
    debt (sourceDebt := sourceDebt) (prefixAction absorption point) =
      (1 - (absorption : ℝ)) * debt (sourceDebt := sourceDebt) point +
        rootDefect (sourceDebt := sourceDebt) absorption point := by
  simp only [debt, rootDefect]
  ring

/-- Root defect obeys the literal two-prefix composition ledger: the inner
defect is discounted by survival through the outer prefix. -/
theorem rootDefect_combine
    (first second : NormalizedPassportZenoAbsorption)
    (point : NormalizedPassportZenoPoint massBound) :
    rootDefect (sourceDebt := sourceDebt) (combine first second) point =
      rootDefect (sourceDebt := sourceDebt) first
          (prefixAction second point) +
        (1 - (first : ℝ)) *
          rootDefect (sourceDebt := sourceDebt) second point := by
  simp only [rootDefect, combine]
  ring

/-- Expanded debt ledger after two literal prefixes. -/
theorem debt_prefix_prefix_eq_continue_mul_add_defects
    (first second : NormalizedPassportZenoAbsorption)
    (point : NormalizedPassportZenoPoint massBound) :
    debt (sourceDebt := sourceDebt)
        (prefixAction first (prefixAction second point)) =
      (1 - (first : ℝ)) * (1 - (second : ℝ)) *
          debt (sourceDebt := sourceDebt) point +
        rootDefect (sourceDebt := sourceDebt) first
          (prefixAction second point) +
        (1 - (first : ℝ)) *
          rootDefect (sourceDebt := sourceDebt) second point := by
  simp only [debt, rootDefect]
  ring

/-- Exact marked-mass prefix scaling. -/
theorem markedMass_prefix
    (absorption : NormalizedPassportZenoAbsorption)
    (point : NormalizedPassportZenoPoint massBound) :
    markedMass (prefixAction absorption point) =
      (1 - (absorption : ℝ)) * markedMass point := rfl

/-- Exact actual-gain prefix scaling. -/
theorem actualGain_prefix
    (absorption : NormalizedPassportZenoAbsorption)
    (point : NormalizedPassportZenoPoint massBound) :
    actualGain (gap := gap) (prefixAction absorption point) =
      (1 - (absorption : ℝ)) * actualGain (gap := gap) point := by
  simp only [actualGain, prefixAction]
  ring

/-- The all-root barrier is attained with equality. -/
theorem rootDefect_eq_debt_mul_absorption
    (absorption : NormalizedPassportZenoAbsorption)
    (point : NormalizedPassportZenoPoint massBound) :
    rootDefect (sourceDebt := sourceDebt) absorption point =
      debt (sourceDebt := sourceDebt) point * (absorption : ℝ) := by
  simp only [rootDefect, debt]
  ring

/-- For positive source debt, only zero absorption has zero scalar defect. -/
theorem rootDefect_eq_zero_iff
    (hsourceDebt : 0 < sourceDebt)
    (absorption : NormalizedPassportZenoAbsorption)
    (point : NormalizedPassportZenoPoint massBound) :
    rootDefect (sourceDebt := sourceDebt) absorption point = 0 ↔
      (absorption : ℝ) = 0 := by
  simp only [rootDefect, mul_eq_zero]
  exact or_iff_left (ne_of_gt hsourceDebt)

/-- The compact scalar carrier. -/
theorem isCompact_univ :
    IsCompact (Set.univ : Set (NormalizedPassportZenoPoint massBound)) := by
  letI : CompactSpace (NormalizedPassportZenoPoint massBound) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact CompactSpace.isCompact_univ

/-- The geometric half-mass chain. -/
def chain
    (hmass : 0 < massBound) (rank : ℕ) :
    NormalizedPassportZenoPoint massBound :=
  ⟨massBound * (1 / 2 : ℝ) ^ rank, by
    constructor
    · positivity
    · calc
        massBound * (1 / 2 : ℝ) ^ rank ≤ massBound * 1 := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_one₀ (by norm_num) (by norm_num)) hmass.le
        _ = massBound := mul_one _⟩

/-- Every finite chain mass is positive. -/
theorem chain_markedMass_pos
    (hmass : 0 < massBound) (rank : ℕ) :
    0 < markedMass (chain hmass rank) := by
  simp only [markedMass, chain]
  positivity

/-- Every finite chain gain is positive. -/
theorem chain_actualGain_pos
    (hmass : 0 < massBound) (hgap : 0 < gap) (rank : ℕ) :
    0 < actualGain (gap := gap) (chain hmass rank) := by
  simp only [actualGain]
  exact mul_pos hgap (chain_markedMass_pos hmass rank)

/-- One half-absorption prefix is exactly the next chain point. -/
theorem chain_succ_eq_prefix_half
    (hmass : 0 < massBound) (rank : ℕ) :
    chain hmass (rank + 1) =
      prefixAction (⟨1 / 2, by norm_num⟩ : NormalizedPassportZenoAbsorption)
        (chain hmass rank) := by
  apply Subtype.ext
  simp only [chain, prefixAction, pow_succ]
  ring

/-- Canonical half-density based at one scalar source point. -/
def canonicalDensity
    (point : NormalizedPassportZenoPoint massBound) : ℝ :=
  markedMass point / (2 * sourceDebt)

/-- Scalar normalized slice generated by a displayed source point. -/
def canonicalSlice
    (sourcePoint candidate : NormalizedPassportZenoPoint massBound) : Prop :=
  canonicalDensity (sourceDebt := sourceDebt) sourcePoint *
      debt (sourceDebt := sourceDebt) candidate ≤
      markedMass candidate ∧
    markedMass candidate ≤ markedMass sourcePoint

/-- The next Zeno point lies in the current canonical slice. -/
theorem chain_succ_mem_canonicalSlice
    (hsourceDebt : 0 < sourceDebt)
    (hmass : 0 < massBound) (rank : ℕ) :
    canonicalSlice (sourceDebt := sourceDebt) (chain hmass rank)
      (chain hmass (rank + 1)) := by
  constructor
  · simp only [canonicalDensity, debt, markedMass, chain, pow_succ]
    field_simp [ne_of_gt hsourceDebt]
    norm_num
  · simp only [markedMass, chain, pow_succ]
    have hnonneg : 0 ≤ massBound * (1 / 2 : ℝ) ^ rank := by positivity
    nlinarith

/-- The next Zeno point saturates the current half-density constraint. -/
theorem chain_succ_slack_eq_zero
    (hsourceDebt : 0 < sourceDebt)
    (hmass : 0 < massBound) (rank : ℕ) :
    markedMass (chain hmass (rank + 1)) -
        canonicalDensity (sourceDebt := sourceDebt) (chain hmass rank) *
          debt (sourceDebt := sourceDebt) (chain hmass (rank + 1)) = 0 := by
  simp only [canonicalDensity, debt, markedMass, chain, pow_succ]
  field_simp [ne_of_gt hsourceDebt]
  ring

/-- Debt is constant, so the next saturated point is a debt minimizer of the
current scalar canonical slice. -/
theorem chain_succ_minimal
    (hmass : 0 < massBound) (rank : ℕ) :
    ∀ candidate : NormalizedPassportZenoPoint massBound,
      canonicalSlice (sourceDebt := sourceDebt) (chain hmass rank) candidate →
        debt (sourceDebt := sourceDebt) (chain hmass (rank + 1)) ≤
          debt (sourceDebt := sourceDebt) candidate := by
  intro candidate _
  rfl

/-- One literal Zeno step is simultaneously a feasible canonical-slice
point, saturated, and debt-minimal in that slice. -/
theorem chain_succ_is_saturated_minimizer
    (hsourceDebt : 0 < sourceDebt)
    (hmass : 0 < massBound) (rank : ℕ) :
    canonicalSlice (sourceDebt := sourceDebt) (chain hmass rank)
        (chain hmass (rank + 1)) ∧
      markedMass (chain hmass (rank + 1)) -
          canonicalDensity (sourceDebt := sourceDebt) (chain hmass rank) *
            debt (sourceDebt := sourceDebt) (chain hmass (rank + 1)) = 0 ∧
      ∀ candidate : NormalizedPassportZenoPoint massBound,
        canonicalSlice (sourceDebt := sourceDebt) (chain hmass rank) candidate →
          debt (sourceDebt := sourceDebt) (chain hmass (rank + 1)) ≤
            debt (sourceDebt := sourceDebt) candidate :=
  ⟨chain_succ_mem_canonicalSlice hsourceDebt hmass rank,
    chain_succ_slack_eq_zero hsourceDebt hmass rank,
    chain_succ_minimal hmass rank⟩

/-- Every finite Zeno stage remains strictly above the named tail debt while
retaining positive mass and gain. -/
theorem chain_strictDebt_and_positivePassport
    (hdebt : minimumDebt < sourceDebt)
    (hmass : 0 < massBound) (hgap : 0 < gap) (rank : ℕ) :
    tailDebt (minimumDebt := minimumDebt) (chain hmass rank) <
        debt (sourceDebt := sourceDebt) (chain hmass rank) ∧
      0 < markedMass (chain hmass rank) ∧
      0 < actualGain (gap := gap) (chain hmass rank) :=
  ⟨hdebt, chain_markedMass_pos hmass rank,
    chain_actualGain_pos hmass hgap rank⟩

end NormalizedPassportZeno

/-! ## Conditional renewable absolute-floor rank -/

/-- Abstract executable sources with one positive density and a renewable
absolute floor. -/
structure RenewableNormalizedPassportDensity (Source : Type*) where
  density : Source → ℝ
  floor : ℝ
  floor_pos : 0 < floor
  floor_le_density : ∀ source, floor ≤ density source

namespace RenewableNormalizedPassportDensity

variable {Source : Type*}

theorem density_pos
    (data : RenewableNormalizedPassportDensity Source) (source : Source) :
    0 < data.density source :=
  data.floor_pos.trans_le (data.floor_le_density source)

/-- Some geometric half-density iterate lies strictly below the absolute
floor. -/
theorem exists_halfPow_mul_density_lt_floor
    (data : RenewableNormalizedPassportDensity Source) (source : Source) :
    ∃ rank : ℕ,
      (1 / 2 : ℝ) ^ rank * data.density source < data.floor := by
  have htarget : 0 < data.floor / data.density source :=
    div_pos data.floor_pos (data.density_pos source)
  obtain ⟨rank, hrank⟩ := exists_pow_lt_of_lt_one htarget
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨rank, ?_⟩
  exact (lt_div_iff₀ (data.density_pos source)).mp hrank

/-- First geometric half-density iterate lying below the absolute floor. -/
def rank (data : RenewableNormalizedPassportDensity Source)
    (source : Source) : ℕ :=
  Nat.find (data.exists_halfPow_mul_density_lt_floor source)

theorem halfPow_rank_mul_density_lt_floor
    (data : RenewableNormalizedPassportDensity Source) (source : Source) :
    (1 / 2 : ℝ) ^ data.rank source * data.density source < data.floor :=
  Nat.find_spec (data.exists_halfPow_mul_density_lt_floor source)

/-- Every executable source has positive rank because its density is at
least the renewable floor. -/
theorem rank_pos
    (data : RenewableNormalizedPassportDensity Source) (source : Source) :
    0 < data.rank source := by
  exact (Nat.find_pos
    (data.exists_halfPow_mul_density_lt_floor source)).2 (by
      simp only [pow_zero, one_mul, not_lt]
      exact data.floor_le_density source)

/-- A regenerated source with at most half the incoming density has strictly
smaller natural-valued rank. -/
theorem rank_lt_of_density_le_half
    (data : RenewableNormalizedPassportDensity Source)
    {source next : Source}
    (hhalf : data.density next ≤ data.density source / 2) :
    data.rank next < data.rank source := by
  let currentRank := data.rank source
  have hcurrentPos : 0 < currentRank := data.rank_pos source
  have hcurrent := data.halfPow_rank_mul_density_lt_floor source
  have hrankEq : currentRank = (currentRank - 1) + 1 := by omega
  have hpow : (1 / 2 : ℝ) ^ currentRank =
      (1 / 2 : ℝ) ^ (currentRank - 1) * (1 / 2 : ℝ) := by
    calc
      (1 / 2 : ℝ) ^ currentRank =
          (1 / 2 : ℝ) ^ ((currentRank - 1) + 1) :=
        congrArg (fun exponent : ℕ ↦ (1 / 2 : ℝ) ^ exponent) hrankEq
      _ = (1 / 2 : ℝ) ^ (currentRank - 1) * (1 / 2 : ℝ) :=
        pow_succ _ _
  have hnext : (1 / 2 : ℝ) ^ (currentRank - 1) * data.density next <
      data.floor := by
    calc
      (1 / 2 : ℝ) ^ (currentRank - 1) * data.density next ≤
          (1 / 2 : ℝ) ^ (currentRank - 1) *
            (data.density source / 2) :=
        mul_le_mul_of_nonneg_left hhalf (pow_nonneg (by norm_num) _)
      _ = (1 / 2 : ℝ) ^ currentRank * data.density source := by
        rw [hpow]
        ring
      _ < data.floor := hcurrent
  have hleast : data.rank next ≤ currentRank - 1 :=
    Nat.find_min' (data.exists_halfPow_mul_density_lt_floor next) hnext
  dsimp only [currentRank] at hcurrentPos hleast ⊢
  omega

end RenewableNormalizedPassportDensity

end Math
