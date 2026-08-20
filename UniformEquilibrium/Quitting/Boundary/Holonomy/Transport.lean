/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DirectedTransport.MaxAffine.Paths
import UniformEquilibrium.Quitting.Boundary.Holonomy.Basic

/-!
# Directed-transport labels of realized quitting boundary blocks

The affine prescribed-payoff and max-affine best-response summaries of a
quitting block embed exactly into `Math.MaxAffineTransport.Label`. Evaluation
and chronological block composition are preserved coefficient by coefficient.

A boundary summary transports a terminal value at the block's exit back to a
value at its entry. Thus a graph of these Bellman transports is naturally
oriented from block exits to block entries, opposite to forward game time.
The adapter does not identify coefficient-compatible seams with realizable or
splice-admissible seams.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

namespace QuittingAffineSummary

/-- The generic affine summary underlying a quitting prescribed-payoff map. -/
def toTransferSummary (summary : QuittingAffineSummary) :
    Math.TransferSummary.AffineSummary :=
  ⟨summary.intercept, summary.survival⟩

/-- A prescribed-payoff summary as a floorless max-affine label. -/
def toLabel (summary : QuittingAffineSummary) :
    Math.MaxAffineTransport.Label :=
  Math.MaxAffineTransport.Label.ofAffine summary.toTransferSummary

@[simp] theorem toTransferSummary_apply
    (summary : QuittingAffineSummary) (point : ℝ) :
    summary.toTransferSummary.apply point = summary.eval point := rfl

@[simp] theorem toLabel_floor (summary : QuittingAffineSummary) :
    summary.toLabel.floor = ⊥ := rfl

@[simp] theorem toLabel_shift (summary : QuittingAffineSummary) :
    summary.toLabel.shift = summary.intercept := rfl

@[simp] theorem toLabel_slope (summary : QuittingAffineSummary) :
    summary.toLabel.slope = summary.survival := rfl

@[simp] theorem toLabel_apply
    (summary : QuittingAffineSummary) (point : ℝ) :
    summary.toLabel.apply point = summary.eval point := rfl

theorem toTransferSummary_compose
    (outer inner : QuittingAffineSummary) :
    (outer.compose inner).toTransferSummary =
      outer.toTransferSummary.comp inner.toTransferSummary := by
  ext <;> rfl

theorem toLabel_compose (outer inner : QuittingAffineSummary) :
    (outer.compose inner).toLabel = outer.toLabel.comp inner.toLabel := by
  rw [toLabel, toLabel, toLabel, toTransferSummary_compose]
  exact Math.MaxAffineTransport.Label.ofAffine_comp _ _

@[simp] theorem toLabel_mul (outer inner : QuittingAffineSummary) :
    (outer * inner).toLabel = outer.toLabel.comp inner.toLabel :=
  toLabel_compose outer inner

end QuittingAffineSummary

namespace QuittingMaxAffineSummary

/-- The generic finite-floor summary underlying a quitting best-response map. -/
def toTransferSummary (summary : QuittingMaxAffineSummary) :
    Math.TransferSummary.MaxAffineSummary :=
  ⟨summary.early, summary.tail, summary.survival⟩

/-- A quitting best-response summary as a generic max-affine label. -/
def toLabel (summary : QuittingMaxAffineSummary) :
    Math.MaxAffineTransport.Label :=
  Math.MaxAffineTransport.Label.ofMaxAffine summary.toTransferSummary

@[simp] theorem toTransferSummary_apply
    (summary : QuittingMaxAffineSummary) (point : ℝ) :
    summary.toTransferSummary.apply point = summary.eval point := rfl

@[simp] theorem toLabel_floor (summary : QuittingMaxAffineSummary) :
    summary.toLabel.floor = (summary.early : WithBot ℝ) := rfl

@[simp] theorem toLabel_shift (summary : QuittingMaxAffineSummary) :
    summary.toLabel.shift = summary.tail := rfl

@[simp] theorem toLabel_slope (summary : QuittingMaxAffineSummary) :
    summary.toLabel.slope = summary.survival := rfl

@[simp] theorem toLabel_apply
    (summary : QuittingMaxAffineSummary) (point : ℝ) :
    summary.toLabel.apply point = summary.eval point := rfl

theorem toTransferSummary_compose
    (outer inner : QuittingMaxAffineSummary) :
    (outer.compose inner).toTransferSummary =
      outer.toTransferSummary.comp inner.toTransferSummary := by
  ext <;> rfl

theorem toLabel_compose (outer inner : QuittingMaxAffineSummary) :
    (outer.compose inner).toLabel = outer.toLabel.comp inner.toLabel := by
  rw [toLabel, toLabel, toLabel, toTransferSummary_compose]
  exact Math.MaxAffineTransport.Label.ofMaxAffine_comp _ _

@[simp] theorem toLabel_mul (outer inner : QuittingMaxAffineSummary) :
    (outer * inner).toLabel = outer.toLabel.comp inner.toLabel :=
  toLabel_compose outer inner

end QuittingMaxAffineSummary

namespace QuittingBoundaryHolonomy

/-- The generic floorless label for one player's prescribed-payoff map. -/
def prescribedLabel (holonomy : QuittingBoundaryHolonomy ι) (who : ι) :
    Math.MaxAffineTransport.Label :=
  (holonomy.prescribed who).toLabel

/-- The generic label for one player's unilateral best-response map. -/
def bestResponseLabel (holonomy : QuittingBoundaryHolonomy ι) (who : ι) :
    Math.MaxAffineTransport.Label :=
  (holonomy.bestResponse who).toLabel

@[simp] theorem prescribedLabel_apply
    (holonomy : QuittingBoundaryHolonomy ι) (who : ι) (point : ℝ) :
    (holonomy.prescribedLabel who).apply point =
      (holonomy.prescribed who).eval point := rfl

@[simp] theorem bestResponseLabel_apply
    (holonomy : QuittingBoundaryHolonomy ι) (who : ι) (point : ℝ) :
    (holonomy.bestResponseLabel who).apply point =
      (holonomy.bestResponse who).eval point := rfl

theorem prescribedLabel_compose
    (outer inner : QuittingBoundaryHolonomy ι) (who : ι) :
    (outer.compose inner).prescribedLabel who =
      (outer.prescribedLabel who).comp (inner.prescribedLabel who) := by
  exact QuittingAffineSummary.toLabel_compose _ _

theorem bestResponseLabel_compose
    (outer inner : QuittingBoundaryHolonomy ι) (who : ι) :
    (outer.compose inner).bestResponseLabel who =
      (outer.bestResponseLabel who).comp (inner.bestResponseLabel who) := by
  exact QuittingMaxAffineSummary.toLabel_compose _ _

@[simp] theorem prescribedLabel_mul
    (outer inner : QuittingBoundaryHolonomy ι) (who : ι) :
    (outer * inner).prescribedLabel who =
      (outer.prescribedLabel who).comp (inner.prescribedLabel who) :=
  prescribedLabel_compose outer inner who

@[simp] theorem bestResponseLabel_mul
    (outer inner : QuittingBoundaryHolonomy ι) (who : ι) :
    (outer * inner).bestResponseLabel who =
      (outer.bestResponseLabel who).comp (inner.bestResponseLabel who) :=
  bestResponseLabel_compose outer inner who

end QuittingBoundaryHolonomy

namespace QuittingAnchoredBoundaryBlock

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable [Nonempty ι]

/-- The backward prescribed-payoff transport label of a realized block. -/
def prescribedLabel
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) (who : ι) :
    Math.MaxAffineTransport.Label :=
  block.holonomy.prescribedLabel who

/-- The backward best-response transport label of a realized block. -/
def bestResponseLabel
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) (who : ι) :
    Math.MaxAffineTransport.Label :=
  block.holonomy.bestResponseLabel who

@[simp] theorem prescribedLabel_apply
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor)
    (who : ι) (terminalValue : ℝ) :
    (block.prescribedLabel who).apply terminalValue =
      quittingFiniteTerminalHazardValue reward anchor.roots who
        (fun time => anchor.roots time who) terminalValue
        block.start block.length := by
  exact block.prescribed_eval who terminalValue

@[simp] theorem bestResponseLabel_apply
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor)
    (who : ι) (terminalValue : ℝ) :
    (block.bestResponseLabel who).apply terminalValue =
      quittingFiniteTerminalBestResponseValue reward anchor.roots who
        terminalValue block.start block.length := by
  exact block.bestResponse_eval who terminalValue

@[simp] theorem bestResponseLabel_slope
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) (who : ι) :
    (block.bestResponseLabel who).slope =
      quittingOpponentSurvivalWeight anchor.roots who
        block.start block.length := by
  exact quittingFiniteBoundaryHolonomy_bestResponse_survival
    reward anchor.roots block.start block.extra who

theorem bestResponseLabel_slope_nonneg
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) (who : ι) :
    0 ≤ (block.bestResponseLabel who).slope := by
  rw [bestResponseLabel_slope]
  exact quittingOpponentSurvivalWeight_nonneg _ _ _ _

theorem bestResponseLabel_slope_le_one
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) (who : ι) :
    (block.bestResponseLabel who).slope ≤ 1 := by
  rw [bestResponseLabel_slope]
  exact quittingOpponentSurvivalWeight_le_one _ _ _ _

/-- Concatenation of adjacent realized blocks is generic label composition. -/
theorem prescribedLabel_concat
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : QuittingAnchoredBoundaryBlock anchor)
    (hadjacent : inner.start = outer.start + outer.length) (who : ι) :
    (outer.concat inner hadjacent).prescribedLabel who =
      (outer.prescribedLabel who).comp (inner.prescribedLabel who) := by
  change (outer.concat inner hadjacent).holonomy.prescribedLabel who =
    (outer.holonomy.prescribedLabel who).comp
      (inner.holonomy.prescribedLabel who)
  rw [holonomy_concat, QuittingBoundaryHolonomy.prescribedLabel_mul]

/-- Concatenation of adjacent realized blocks preserves best-response labels. -/
theorem bestResponseLabel_concat
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : QuittingAnchoredBoundaryBlock anchor)
    (hadjacent : inner.start = outer.start + outer.length) (who : ι) :
    (outer.concat inner hadjacent).bestResponseLabel who =
      (outer.bestResponseLabel who).comp (inner.bestResponseLabel who) := by
  change (outer.concat inner hadjacent).holonomy.bestResponseLabel who =
    (outer.holonomy.bestResponseLabel who).comp
      (inner.holonomy.bestResponseLabel who)
  rw [holonomy_concat, QuittingBoundaryHolonomy.bestResponseLabel_mul]

end QuittingAnchoredBoundaryBlock

end GameTheory

end
