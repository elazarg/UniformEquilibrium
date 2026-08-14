import Research.Quitting.BlockPair.K11.ConditionalData
import Mathlib.Logic.Equiv.Fin.Rotate

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

/-- Scalar version of the named ordered numerator recurrence. -/
def scalarNumeratorAux (immediate survival : ℕ → ℝ) :
    ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | fuel + 1 =>
      let previous := scalarNumeratorAux immediate survival fuel
      (previous.1 + previous.2 * immediate fuel,
        previous.2 * survival fuel)

/-- The final named step appends one immediate/survival pair. -/
theorem scalarNumeratorAux_append
    (immediate survival : ℕ → ℝ) (fuel : ℕ) :
    scalarNumeratorAux immediate survival (fuel + 1) =
      let previous := scalarNumeratorAux immediate survival fuel
      (previous.1 + previous.2 * immediate fuel,
        previous.2 * survival fuel) := by
  rfl

theorem realProduct_eq_fintypeProduct {count : ℕ}
    (factor : Fin count → ℝ) :
    BlockPairCharts.realProduct factor = ∏ index, factor index := by
  induction count with
  | zero => simp [BlockPairCharts.realProduct]
  | succ count inductionHypothesis =>
      rw [BlockPairCharts.realProduct, Fin.prod_univ_castSucc,
        inductionHypothesis]

theorem scalarNumeratorAux_survival_eq_realProduct
    (immediate survival : ℕ → ℝ) (fuel : ℕ) :
    (scalarNumeratorAux immediate survival fuel).2 =
      BlockPairCharts.realProduct fun index : Fin fuel ↦
        survival index.val := by
  induction fuel with
  | zero => simp [scalarNumeratorAux, BlockPairCharts.realProduct]
  | succ fuel inductionHypothesis =>
      rw [scalarNumeratorAux_append]
      simp only
      rw [BlockPairCharts.realProduct, inductionHypothesis]
      rfl

/-- An ordered numerator fold can be decomposed at its first phase without
expanding the remaining prefix. -/
theorem scalarNumeratorAux_prepend
    (immediate survival : ℕ → ℝ) (fuel : ℕ) :
    scalarNumeratorAux immediate survival (fuel + 1) =
      let tail := scalarNumeratorAux
        (fun offset ↦ immediate (offset + 1))
        (fun offset ↦ survival (offset + 1)) fuel
      (immediate 0 + survival 0 * tail.1,
        survival 0 * tail.2) := by
  induction fuel with
  | zero => simp [scalarNumeratorAux]
  | succ fuel inductionHypothesis =>
      rw [scalarNumeratorAux_append, inductionHypothesis]
      simp only [scalarNumeratorAux]
      ring

end GameTheory.BlockPairK11.ConditionalData
