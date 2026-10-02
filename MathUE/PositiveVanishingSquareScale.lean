import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

/-! # A canonical positive square-root scale above a vanishing error

Unlike sparse calendars, this scale keeps every original sequence index and
dominates the error by its square, including at zero-error indices.
-/

noncomputable section

open Filter Topology

namespace Math

def positiveVanishingSquareScale (error : ℕ → ℝ) (index : ℕ) : ℝ :=
  Real.sqrt (max (error index) (1 / ((index : ℝ) + 1)))

theorem positiveVanishingSquareScale_pos (error : ℕ → ℝ) (index : ℕ) :
    0 < positiveVanishingSquareScale error index := by
  apply Real.sqrt_pos.2
  exact lt_of_lt_of_le (by positivity : 0 < 1 / ((index : ℝ) + 1))
    (le_max_right _ _)

theorem positiveVanishingSquareScale_sq (error : ℕ → ℝ) (index : ℕ) :
    positiveVanishingSquareScale error index ^ 2 =
      max (error index) (1 / ((index : ℝ) + 1)) := by
  apply Real.sq_sqrt
  exact le_trans (by positivity : 0 ≤ 1 / ((index : ℝ) + 1)) (le_max_right _ _)

theorem error_le_positiveVanishingSquareScale_sq (error : ℕ → ℝ) (index : ℕ) :
    error index ≤ positiveVanishingSquareScale error index ^ 2 := by
  rw [positiveVanishingSquareScale_sq]
  exact le_max_left _ _

theorem tendsto_positiveVanishingSquareScale (error : ℕ → ℝ)
    (herror : Tendsto error atTop (nhds 0)) :
    Tendsto (positiveVanishingSquareScale error) atTop (nhds 0) := by
  have htail : Tendsto (fun index : ℕ => 1 / ((index : ℝ) + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun index => Real.sqrt (max (error index) (1 / ((index : ℝ) + 1))))
    atTop (nhds 0)
  simpa only [max_self, Real.sqrt_zero] using
    (herror.max htail).sqrt

theorem eventually_positiveVanishingSquareScale_lt_one (error : ℕ → ℝ)
    (herror : Tendsto error atTop (nhds 0)) :
    ∀ᶠ index in atTop, positiveVanishingSquareScale error index < 1 :=
  (tendsto_order.1 (tendsto_positiveVanishingSquareScale error herror)).2 1 zero_lt_one

end Math
