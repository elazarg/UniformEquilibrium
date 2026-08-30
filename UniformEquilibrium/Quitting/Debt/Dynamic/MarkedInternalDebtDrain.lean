/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.SequenceVariation
import UniformEquilibrium.Quitting.Debt.Dynamic.ChronologicalSeamReduction
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

/-!
# Marked internal terminal-debt drain

This module specializes the game-independent marked positive-part telescope to
literal terminal semantic debt along variable-length exact prefix blocks.
Block seams are controlled coordinatewise in prescribed payoff and response
cap.  The resulting total-debt seam cost is the number of players times the
common coordinate bound.

The conclusions account for internal debt drain only.  They do not construct
the blocks, select marks, or supply the drift and seam hypotheses.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingVariableLengthSeamBlocksNat

variable (blocks : QuittingVariableLengthSeamBlocksNat reward)

/-- Total debt at the entrance of a variable-length block. -/
def totalDebtEntrance (block : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum (blocks.candidate block 0)

/-- Total debt at a selected internal mark. -/
def totalDebtMarked (mark : ℕ → ℕ) (block : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum (blocks.candidate block (mark block))

/-- Total debt at the endpoint of a variable-length block. -/
def totalDebtEndpoint (block : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum
    (blocks.candidate block (blocks.length block))

/-- One player's debt at the entrance of a variable-length block. -/
def coordinateDebtEntrance (who : ι) (block : ℕ) : ℝ :=
  quittingTerminalSemanticDebt (blocks.candidate block 0) who

/-- One player's debt at a selected internal mark. -/
def coordinateDebtMarked (who : ι) (mark : ℕ → ℕ) (block : ℕ) : ℝ :=
  quittingTerminalSemanticDebt (blocks.candidate block (mark block)) who

/-- One player's debt at the endpoint of a variable-length block. -/
def coordinateDebtEndpoint (who : ι) (block : ℕ) : ℝ :=
  quittingTerminalSemanticDebt
    (blocks.candidate block (blocks.length block)) who

/-- Positive total-debt drain between a selected mark and its block endpoint. -/
def positiveInternalDebtDrain (mark : ℕ → ℕ) (block : ℕ) : ℝ :=
  max (blocks.totalDebtMarked mark block - blocks.totalDebtEndpoint block) 0

/-- Positive marked-to-endpoint drain in one player's debt coordinate. -/
def positiveInternalCoordinateDebtDrain
    (who : ι) (mark : ℕ → ℕ) (block : ℕ) : ℝ :=
  max (blocks.coordinateDebtMarked who mark block -
    blocks.coordinateDebtEndpoint who block) 0

/-- Positive total-debt drop across one literal row of a block. -/
def positiveRowDebtDrop (block offset : ℕ) : ℝ :=
  max (quittingTerminalSemanticDebtSum (blocks.candidate block offset) -
    quittingTerminalSemanticDebtSum (blocks.candidate block (offset + 1))) 0

/-- Positive drop in one player's debt across one literal row of a block. -/
def positiveRowCoordinateDebtDrop (who : ι) (block offset : ℕ) : ℝ :=
  max (quittingTerminalSemanticDebt (blocks.candidate block offset) who -
    quittingTerminalSemanticDebt (blocks.candidate block (offset + 1)) who) 0

/-- Coordinatewise payoff/cap seam control bounds the signed total-debt seam.
The factor `card ι` is literal: one common seam allowance is paid per player. -/
theorem neg_card_mul_seam_le_totalDebtEntrance_succ_sub_endpoint
    (seam : ℕ → ℝ)
    (hseam : ∀ block who, blocks.totalBlockSeamNat who block ≤ seam block)
    (block : ℕ) :
    -((Fintype.card ι : ℝ) * seam block) ≤
      blocks.totalDebtEntrance (block + 1) -
        blocks.totalDebtEndpoint block := by
  have hLipschitz := abs_quittingTerminalSemanticDebtSum_sub_le
    (blocks.candidate (block + 1) 0)
    (blocks.candidate block (blocks.length block))
  have hcoordinate :
      (∑ who, (|(blocks.candidate (block + 1) 0).1 who -
          (blocks.candidate block (blocks.length block)).1 who| +
        |(blocks.candidate (block + 1) 0).2 who -
          (blocks.candidate block (blocks.length block)).2 who|)) ≤
        (Fintype.card ι : ℝ) * seam block := by
    calc
      _ = ∑ who, blocks.totalBlockSeamNat who block := by
        apply Finset.sum_congr rfl
        intro who _
        unfold totalBlockSeamNat prescribedBlockSeamNat capBlockSeamNat
        congr 1
        · exact abs_sub_comm _ _
        · exact abs_sub_comm _ _
      _ ≤ ∑ _who : ι, seam block :=
        Finset.sum_le_sum fun who _ => hseam block who
      _ = (Fintype.card ι : ℝ) * seam block := by simp
  have habs :
      |blocks.totalDebtEntrance (block + 1) -
          blocks.totalDebtEndpoint block| ≤
        (Fintype.card ι : ℝ) * seam block :=
    hLipschitz.trans hcoordinate
  exact neg_le_of_abs_le habs

/-- The literal payoff/cap seam for one player controls that player's signed
debt seam. -/
theorem neg_seam_le_coordinateDebtEntrance_succ_sub_endpoint
    (who : ι) (seam : ℕ → ℝ)
    (hseam : ∀ block, blocks.totalBlockSeamNat who block ≤ seam block)
    (block : ℕ) :
    -seam block ≤ blocks.coordinateDebtEntrance who (block + 1) -
      blocks.coordinateDebtEndpoint who block := by
  have hLipschitz := abs_quittingTerminalSemanticDebt_sub_le
    (blocks.candidate (block + 1) 0)
    (blocks.candidate block (blocks.length block)) who
  have hcoordinate :
      |(blocks.candidate (block + 1) 0).1 who -
          (blocks.candidate block (blocks.length block)).1 who| +
        |(blocks.candidate (block + 1) 0).2 who -
          (blocks.candidate block (blocks.length block)).2 who| =
      blocks.totalBlockSeamNat who block := by
    unfold totalBlockSeamNat prescribedBlockSeamNat capBlockSeamNat
    rw [abs_sub_comm
      ((blocks.candidate (block + 1) 0).1 who)
      ((blocks.candidate block (blocks.length block)).1 who)]
    rw [abs_sub_comm
      ((blocks.candidate (block + 1) 0).2 who)
      ((blocks.candidate block (blocks.length block)).2 who)]
  have habs :
      |blocks.coordinateDebtEntrance who (block + 1) -
          blocks.coordinateDebtEndpoint who block| ≤ seam block := by
    unfold coordinateDebtEntrance coordinateDebtEndpoint
    exact hLipschitz.trans (hcoordinate.le.trans (hseam block))
  exact neg_le_of_abs_le habs

/-- Finite-prefix account for one marked debt coordinate. -/
theorem sum_positiveInternalCoordinateDebtDrain_ge
    (who : ι) (mark : ℕ → ℕ) (exposure residual seam : ℕ → ℝ)
    (rate : ℝ)
    (_hmark : ∀ block, mark block ≤ blocks.length block)
    (hdrift : ∀ block,
      rate * exposure block - residual block ≤
        blocks.coordinateDebtMarked who mark block -
          blocks.coordinateDebtEntrance who block)
    (hseam : ∀ block, blocks.totalBlockSeamNat who block ≤ seam block)
    (horizon : ℕ) :
    rate * (∑ block ∈ Finset.range horizon, exposure block) -
          (∑ block ∈ Finset.range horizon, residual block) +
        blocks.coordinateDebtEntrance who 0 -
          blocks.coordinateDebtEntrance who horizon -
          (∑ block ∈ Finset.range horizon, seam block) ≤
      ∑ block ∈ Finset.range horizon,
        blocks.positiveInternalCoordinateDebtDrain who mark block := by
  simpa [positiveInternalCoordinateDebtDrain] using
    (Math.sum_positivePart_markedDrain_ge
      (blocks.coordinateDebtEntrance who)
      (blocks.coordinateDebtMarked who mark)
      (blocks.coordinateDebtEndpoint who) exposure residual seam rate hdrift
      (blocks.neg_seam_le_coordinateDebtEntrance_succ_sub_endpoint
        who seam hseam) horizon)

/-- A uniform bound on one entrance-debt row removes its signed boundary term
at cost `bound`. -/
theorem sum_positiveInternalCoordinateDebtDrain_ge_of_bounded
    (who : ι) (mark : ℕ → ℕ) (exposure residual seam : ℕ → ℝ)
    (rate bound : ℝ)
    (_hmark : ∀ block, mark block ≤ blocks.length block)
    (hdrift : ∀ block,
      rate * exposure block - residual block ≤
        blocks.coordinateDebtMarked who mark block -
          blocks.coordinateDebtEntrance who block)
    (hseam : ∀ block, blocks.totalBlockSeamNat who block ≤ seam block)
    (hdebtBound : ∀ block,
      blocks.coordinateDebtEntrance who block ≤ bound)
    (horizon : ℕ) :
    rate * (∑ block ∈ Finset.range horizon, exposure block) -
          (∑ block ∈ Finset.range horizon, residual block) - bound -
          (∑ block ∈ Finset.range horizon, seam block) ≤
      ∑ block ∈ Finset.range horizon,
        blocks.positiveInternalCoordinateDebtDrain who mark block := by
  have hentrance : ∀ block,
      0 ≤ blocks.coordinateDebtEntrance who block ∧
        blocks.coordinateDebtEntrance who block ≤ bound := by
    intro block
    exact ⟨blocks.debt_nonneg block 0 (Nat.zero_le _) who,
      hdebtBound block⟩
  simpa [positiveInternalCoordinateDebtDrain] using
    (Math.sum_positivePart_markedDrain_ge_of_bounded
      (blocks.coordinateDebtEntrance who)
      (blocks.coordinateDebtMarked who mark)
      (blocks.coordinateDebtEndpoint who) exposure residual seam rate bound
      hdrift
      (blocks.neg_seam_le_coordinateDebtEntrance_succ_sub_endpoint
        who seam hseam) hentrance horizon)

/-- If the selected coordinate enters every block at zero debt, its boundary
term vanishes rather than merely being bounded. -/
theorem sum_positiveInternalCoordinateDebtDrain_ge_of_entrance_eq_zero
    (who : ι) (mark : ℕ → ℕ) (exposure residual seam : ℕ → ℝ)
    (rate : ℝ)
    (_hmark : ∀ block, mark block ≤ blocks.length block)
    (hdrift : ∀ block,
      rate * exposure block - residual block ≤
        blocks.coordinateDebtMarked who mark block -
          blocks.coordinateDebtEntrance who block)
    (hseam : ∀ block, blocks.totalBlockSeamNat who block ≤ seam block)
    (hentranceZero : ∀ block,
      blocks.coordinateDebtEntrance who block = 0)
    (horizon : ℕ) :
    rate * (∑ block ∈ Finset.range horizon, exposure block) -
          (∑ block ∈ Finset.range horizon, residual block) -
          (∑ block ∈ Finset.range horizon, seam block) ≤
      ∑ block ∈ Finset.range horizon,
        blocks.positiveInternalCoordinateDebtDrain who mark block := by
  have haccount := blocks.sum_positiveInternalCoordinateDebtDrain_ge
    who mark exposure residual seam rate _hmark hdrift hseam horizon
  rw [hentranceZero 0, hentranceZero horizon] at haccount
  linarith

/-- Finite-prefix total-debt account for marked block drift. -/
theorem sum_positiveInternalDebtDrain_ge
    (mark : ℕ → ℕ) (exposure residual seam : ℕ → ℝ) (rate : ℝ)
    (_hmark : ∀ block, mark block ≤ blocks.length block)
    (hdrift : ∀ block,
      rate * exposure block - residual block ≤
        blocks.totalDebtMarked mark block - blocks.totalDebtEntrance block)
    (hseam : ∀ block who, blocks.totalBlockSeamNat who block ≤ seam block)
    (horizon : ℕ) :
    rate * (∑ block ∈ Finset.range horizon, exposure block) -
          (∑ block ∈ Finset.range horizon, residual block) +
        blocks.totalDebtEntrance 0 - blocks.totalDebtEntrance horizon -
          (Fintype.card ι : ℝ) *
            (∑ block ∈ Finset.range horizon, seam block) ≤
      ∑ block ∈ Finset.range horizon,
        blocks.positiveInternalDebtDrain mark block := by
  simpa [totalDebtEntrance, totalDebtMarked, totalDebtEndpoint,
    positiveInternalDebtDrain, Finset.mul_sum] using
    (Math.sum_positivePart_markedDrain_ge
      blocks.totalDebtEntrance (blocks.totalDebtMarked mark)
      blocks.totalDebtEndpoint exposure residual
      (fun block => (Fintype.card ι : ℝ) * seam block) rate hdrift
      (blocks.neg_card_mul_seam_le_totalDebtEntrance_succ_sub_endpoint
        seam hseam) horizon)

/-- Bounded entrance debts remove the signed boundary term at cost
`card ι * bound`. -/
theorem sum_positiveInternalDebtDrain_ge_of_bounded
    (mark : ℕ → ℕ) (exposure residual seam : ℕ → ℝ)
    (rate bound : ℝ)
    (_hmark : ∀ block, mark block ≤ blocks.length block)
    (hdrift : ∀ block,
      rate * exposure block - residual block ≤
        blocks.totalDebtMarked mark block - blocks.totalDebtEntrance block)
    (hseam : ∀ block who, blocks.totalBlockSeamNat who block ≤ seam block)
    (hdebtBound : ∀ block who,
      quittingTerminalSemanticDebt (blocks.candidate block 0) who ≤ bound)
    (horizon : ℕ) :
    rate * (∑ block ∈ Finset.range horizon, exposure block) -
          (∑ block ∈ Finset.range horizon, residual block) -
        (Fintype.card ι : ℝ) * bound -
          (Fintype.card ι : ℝ) *
            (∑ block ∈ Finset.range horizon, seam block) ≤
      ∑ block ∈ Finset.range horizon,
        blocks.positiveInternalDebtDrain mark block := by
  have hentrance : ∀ block,
      0 ≤ blocks.totalDebtEntrance block ∧
        blocks.totalDebtEntrance block ≤ (Fintype.card ι : ℝ) * bound := by
    intro block
    constructor
    · unfold totalDebtEntrance quittingTerminalSemanticDebtSum
      exact Finset.sum_nonneg fun who _ =>
        blocks.debt_nonneg block 0 (Nat.zero_le _) who
    · unfold totalDebtEntrance quittingTerminalSemanticDebtSum
      calc
        (∑ who, quittingTerminalSemanticDebt
            (blocks.candidate block 0) who) ≤ ∑ _who : ι, bound :=
          Finset.sum_le_sum fun who _ => hdebtBound block who
        _ = (Fintype.card ι : ℝ) * bound := by simp
  simpa [positiveInternalDebtDrain, Finset.mul_sum] using
    (Math.sum_positivePart_markedDrain_ge_of_bounded
      blocks.totalDebtEntrance (blocks.totalDebtMarked mark)
      blocks.totalDebtEndpoint exposure residual
      (fun block => (Fintype.card ι : ℝ) * seam block) rate
      ((Fintype.card ι : ℝ) * bound) hdrift
      (blocks.neg_card_mul_seam_le_totalDebtEntrance_succ_sub_endpoint
        seam hseam) hentrance horizon)

/-- Under nonsummable exposure and summable residual/seam errors, marked
positive internal total-debt drain cannot be summable. -/
theorem not_summable_positiveInternalDebtDrain
    (mark : ℕ → ℕ) (exposure residual seam : ℕ → ℝ)
    (rate bound : ℝ) (hrate : 0 < rate)
    (_hmark : ∀ block, mark block ≤ blocks.length block)
    (hdrift : ∀ block,
      rate * exposure block - residual block ≤
        blocks.totalDebtMarked mark block - blocks.totalDebtEntrance block)
    (hseam : ∀ block who, blocks.totalBlockSeamNat who block ≤ seam block)
    (hdebtBound : ∀ block who,
      quittingTerminalSemanticDebt (blocks.candidate block 0) who ≤ bound)
    (hexposure : ∀ block, 0 ≤ exposure block)
    (hexposureDiverges : ¬Summable exposure)
    (hresidual : ∀ block, 0 ≤ residual block)
    (hresidualSummable : Summable residual)
    (hseamNonneg : ∀ block, 0 ≤ seam block)
    (hseamSummable : Summable seam) :
    ¬Summable (blocks.positiveInternalDebtDrain mark) := by
  have hentrance : ∀ block,
      0 ≤ blocks.totalDebtEntrance block ∧
        blocks.totalDebtEntrance block ≤ (Fintype.card ι : ℝ) * bound := by
    intro block
    constructor
    · unfold totalDebtEntrance quittingTerminalSemanticDebtSum
      exact Finset.sum_nonneg fun who _ =>
        blocks.debt_nonneg block 0 (Nat.zero_le _) who
    · unfold totalDebtEntrance quittingTerminalSemanticDebtSum
      calc
        (∑ who, quittingTerminalSemanticDebt
            (blocks.candidate block 0) who) ≤ ∑ _who : ι, bound :=
          Finset.sum_le_sum fun who _ => hdebtBound block who
        _ = (Fintype.card ι : ℝ) * bound := by simp
  change ¬Summable (fun block =>
    max (blocks.totalDebtMarked mark block - blocks.totalDebtEndpoint block) 0)
  exact Math.not_summable_positivePart_markedDrain
      blocks.totalDebtEntrance (blocks.totalDebtMarked mark)
      blocks.totalDebtEndpoint exposure residual
      (fun block => (Fintype.card ι : ℝ) * seam block) rate
      ((Fintype.card ι : ℝ) * bound) hrate hdrift
      (blocks.neg_card_mul_seam_le_totalDebtEntrance_succ_sub_endpoint
        seam hseam) hentrance hexposure hexposureDiverges hresidual
      hresidualSummable
      (fun block => mul_nonneg (Nat.cast_nonneg _) (hseamNonneg block))
      (Summable.mul_left (Fintype.card ι : ℝ) hseamSummable)

/-- Under the same drift and summability hypotheses, the literal finite
partial sums of total marked drain diverge to `+∞`. -/
theorem tendsto_sum_positiveInternalDebtDrain_atTop
    (mark : ℕ → ℕ) (exposure residual seam : ℕ → ℝ)
    (rate bound : ℝ) (hrate : 0 < rate)
    (hmark : ∀ block, mark block ≤ blocks.length block)
    (hdrift : ∀ block,
      rate * exposure block - residual block ≤
        blocks.totalDebtMarked mark block - blocks.totalDebtEntrance block)
    (hseam : ∀ block who, blocks.totalBlockSeamNat who block ≤ seam block)
    (hdebtBound : ∀ block who,
      quittingTerminalSemanticDebt (blocks.candidate block 0) who ≤ bound)
    (hexposure : ∀ block, 0 ≤ exposure block)
    (hexposureDiverges : ¬Summable exposure)
    (hresidual : ∀ block, 0 ≤ residual block)
    (hresidualSummable : Summable residual)
    (hseamNonneg : ∀ block, 0 ≤ seam block)
    (hseamSummable : Summable seam) :
    Filter.Tendsto
      (fun horizon => ∑ block ∈ Finset.range horizon,
        blocks.positiveInternalDebtDrain mark block)
      Filter.atTop Filter.atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun block => le_max_right _ _)).1
  exact blocks.not_summable_positiveInternalDebtDrain
    mark exposure residual seam rate bound hrate hmark hdrift hseam
    hdebtBound hexposure hexposureDiverges hresidual hresidualSummable
    hseamNonneg hseamSummable

/-- Every positive loss in the drift rate is attained infinitely often by
marked positive internal total-debt drain. -/
theorem frequently_positiveInternalDebtDrain_ge
    (mark : ℕ → ℕ) (exposure residual seam : ℕ → ℝ)
    (rate bound : ℝ)
    (_hmark : ∀ block, mark block ≤ blocks.length block)
    (hdrift : ∀ block,
      rate * exposure block - residual block ≤
        blocks.totalDebtMarked mark block - blocks.totalDebtEntrance block)
    (hseam : ∀ block who, blocks.totalBlockSeamNat who block ≤ seam block)
    (hdebtBound : ∀ block who,
      quittingTerminalSemanticDebt (blocks.candidate block 0) who ≤ bound)
    (hexposure : ∀ block, 0 ≤ exposure block)
    (hexposureDiverges : ¬Summable exposure)
    (hresidual : ∀ block, 0 ≤ residual block)
    (hresidualSummable : Summable residual)
    (hseamNonneg : ∀ block, 0 ≤ seam block)
    (hseamSummable : Summable seam)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Filter.Frequently (fun block =>
      (rate - epsilon) * exposure block ≤
        blocks.positiveInternalDebtDrain mark block) Filter.atTop := by
  have hentrance : ∀ block,
      0 ≤ blocks.totalDebtEntrance block ∧
        blocks.totalDebtEntrance block ≤ (Fintype.card ι : ℝ) * bound := by
    intro block
    constructor
    · unfold totalDebtEntrance quittingTerminalSemanticDebtSum
      exact Finset.sum_nonneg fun who _ =>
        blocks.debt_nonneg block 0 (Nat.zero_le _) who
    · unfold totalDebtEntrance quittingTerminalSemanticDebtSum
      calc
        (∑ who, quittingTerminalSemanticDebt
            (blocks.candidate block 0) who) ≤ ∑ _who : ι, bound :=
          Finset.sum_le_sum fun who _ => hdebtBound block who
        _ = (Fintype.card ι : ℝ) * bound := by simp
  simpa [positiveInternalDebtDrain] using
    (Math.frequently_positivePart_markedDrain_ge
      blocks.totalDebtEntrance (blocks.totalDebtMarked mark)
      blocks.totalDebtEndpoint exposure residual
      (fun block => (Fintype.card ι : ℝ) * seam block) rate
      ((Fintype.card ι : ℝ) * bound) hdrift
      (blocks.neg_card_mul_seam_le_totalDebtEntrance_succ_sub_endpoint
        seam hseam) hentrance hexposure hexposureDiverges hresidual
      hresidualSummable
      (fun block => mul_nonneg (Nat.cast_nonneg _) (hseamNonneg block))
      (Summable.mul_left (Fintype.card ι : ℝ) hseamSummable)
      epsilon hepsilon)

/-- Every indexed row after the mark is one of the stored literal exact
terminal-semantic prefix steps. -/
theorem markedRow_exact_step
    (mark : ℕ → ℕ) (block offset : ℕ)
    (hmark : mark block ≤ blocks.length block)
    (hoffset : offset < blocks.length block - mark block) :
    blocks.candidate block (mark block + offset) =
      quittingTerminalSemanticPrefix reward
        (blocks.roots block (mark block + offset))
        (blocks.candidate block (mark block + offset + 1)) := by
  exact blocks.exact_step block (mark block + offset) (by omega)

/-- The marked-to-endpoint drain is localized on the positive drops of the
literal exact rows after the mark. -/
theorem positiveInternalDebtDrain_le_sum_positiveRowDebtDrop
    (mark : ℕ → ℕ) (block : ℕ)
    (hmark : mark block ≤ blocks.length block) :
    blocks.positiveInternalDebtDrain mark block ≤
      ∑ offset ∈ Finset.range (blocks.length block - mark block),
        blocks.positiveRowDebtDrop block (mark block + offset) := by
  simpa [positiveInternalDebtDrain, totalDebtMarked, totalDebtEndpoint,
    positiveRowDebtDrop, Nat.add_assoc, Nat.add_sub_of_le hmark] using
    (Math.positivePart_sub_le_sum_positivePart_succDrops
      (fun offset =>
        quittingTerminalSemanticDebtSum (blocks.candidate block offset))
      (mark block) (blocks.length block - mark block))

/-- One marked coordinate drain is localized on positive coordinate drops
across the stored literal exact rows after the mark. -/
theorem positiveInternalCoordinateDebtDrain_le_sum_positiveRowCoordinateDebtDrop
    (who : ι) (mark : ℕ → ℕ) (block : ℕ)
    (hmark : mark block ≤ blocks.length block) :
    blocks.positiveInternalCoordinateDebtDrain who mark block ≤
      ∑ offset ∈ Finset.range (blocks.length block - mark block),
        blocks.positiveRowCoordinateDebtDrop who block
          (mark block + offset) := by
  simpa [positiveInternalCoordinateDebtDrain, coordinateDebtMarked,
    coordinateDebtEndpoint, positiveRowCoordinateDebtDrop, Nat.add_assoc,
    Nat.add_sub_of_le hmark] using
    (Math.positivePart_sub_le_sum_positivePart_succDrops
      (fun offset => quittingTerminalSemanticDebt
        (blocks.candidate block offset) who)
      (mark block) (blocks.length block - mark block))

/-- Under nonsummable exposure and summable errors, the cumulative positive
coordinate drops along all literal exact rows after the block marks diverge to
`+∞`.  Thus total marked drain cannot disappear when it is resolved first by
row and then by player coordinate. -/
theorem tendsto_sum_positiveRowCoordinateDebtDrop_atTop
    (mark : ℕ → ℕ) (exposure residual seam : ℕ → ℝ)
    (rate bound : ℝ) (hrate : 0 < rate)
    (hmark : ∀ block, mark block ≤ blocks.length block)
    (hdrift : ∀ block,
      rate * exposure block - residual block ≤
        blocks.totalDebtMarked mark block - blocks.totalDebtEntrance block)
    (hseam : ∀ block who, blocks.totalBlockSeamNat who block ≤ seam block)
    (hdebtBound : ∀ block who,
      quittingTerminalSemanticDebt (blocks.candidate block 0) who ≤ bound)
    (hexposure : ∀ block, 0 ≤ exposure block)
    (hexposureDiverges : ¬Summable exposure)
    (hresidual : ∀ block, 0 ≤ residual block)
    (hresidualSummable : Summable residual)
    (hseamNonneg : ∀ block, 0 ≤ seam block)
    (hseamSummable : Summable seam) :
    Filter.Tendsto
      (fun horizon => ∑ block ∈ Finset.range horizon,
        ∑ offset ∈ Finset.range (blocks.length block - mark block),
          ∑ who, blocks.positiveRowCoordinateDebtDrop who block
            (mark block + offset))
      Filter.atTop Filter.atTop := by
  have hrow (block offset : ℕ) :
      blocks.positiveRowDebtDrop block offset ≤
        ∑ who, blocks.positiveRowCoordinateDebtDrop who block offset := by
    unfold positiveRowDebtDrop positiveRowCoordinateDebtDrop
    unfold quittingTerminalSemanticDebtSum
    rw [← Finset.sum_sub_distrib]
    apply max_le
    · exact Finset.sum_le_sum fun who _ => le_max_left _ _
    · exact Finset.sum_nonneg fun who _ => le_max_right _ _
  have hblock (block : ℕ) :
      blocks.positiveInternalDebtDrain mark block ≤
        ∑ offset ∈ Finset.range (blocks.length block - mark block),
          ∑ who, blocks.positiveRowCoordinateDebtDrop who block
            (mark block + offset) := by
    calc
      blocks.positiveInternalDebtDrain mark block ≤
          ∑ offset ∈ Finset.range (blocks.length block - mark block),
            blocks.positiveRowDebtDrop block (mark block + offset) :=
        blocks.positiveInternalDebtDrain_le_sum_positiveRowDebtDrop
          mark block (hmark block)
      _ ≤ ∑ offset ∈ Finset.range (blocks.length block - mark block),
          ∑ who, blocks.positiveRowCoordinateDebtDrop who block
            (mark block + offset) :=
        Finset.sum_le_sum fun offset _ => hrow block (mark block + offset)
  apply Filter.tendsto_atTop_mono fun horizon =>
    Finset.sum_le_sum fun block _ => hblock block
  exact blocks.tendsto_sum_positiveInternalDebtDrain_atTop
    mark exposure residual seam rate bound hrate hmark hdrift hseam
    hdebtBound hexposure hexposureDiverges hresidual hresidualSummable
    hseamNonneg hseamSummable

end QuittingVariableLengthSeamBlocksNat

end GameTheory
