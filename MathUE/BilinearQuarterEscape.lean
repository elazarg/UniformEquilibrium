import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Escape in a quarter-weighted bilinear square

This is the scalar computation in Sorin (1986), Proposition 15, pp158--159.
The input is ordinary endpoint-maximality in a bilinear square and numerical
coordinate bounds. Activity of the improving corner is proved internally.
No corner improvement, maximizing orbit, feasibility of pairs of independent
coordinate bounds, or continuation-equilibrium certificate is an input.
-/

noncomputable section

namespace Math.BilinearQuarter

/-- Independent square interpolation; false indexes the first endpoint. -/
def interpolate (value : Bool → Bool → ℝ) (s t : ℝ) : ℝ :=
  s * t * value false false + s * (1 - t) * value false true +
    (1 - s) * t * value true false + (1 - s) * (1 - t) * value true true

/-- The first coordinate, with the fixed current-stage corner values. -/
def row (value : Bool → Bool → ℝ) (s t : ℝ) : ℝ :=
  (3 / 4) * (4 * s * t + 5 * (1 - s) * t + (1 - s) * (1 - t)) +
    (1 / 4) * interpolate value s t

/-- The second coordinate, with the transposed current-stage corner values. -/
def column (value : Bool → Bool → ℝ) (s t : ℝ) : ℝ :=
  (3 / 4) * (4 * s * t + 5 * s * (1 - t) + (1 - s) * (1 - t)) +
    (1 / 4) * interpolate value s t

theorem row_affine (value : Bool → Bool → ℝ) (s t : ℝ) :
    row value s t = s * row value 1 t + (1 - s) * row value 0 t := by
  unfold row interpolate
  ring

theorem column_affine (value : Bool → Bool → ℝ) (s t : ℝ) :
    column value s t = t * column value s 1 + (1 - t) * column value s 0 := by
  unfold column interpolate
  ring

/-- Scalar player exchange needs no payoff-map or strategy lift. -/
theorem row_transpose (value : Bool → Bool → ℝ) (s t : ℝ) :
    row (fun i j => value j i) t s = column value s t := by
  unfold row column interpolate
  ring

theorem column_transpose (value : Bool → Bool → ℝ) (s t : ℝ) :
    column (fun i j => value j i) t s = row value s t := by
  unfold row column interpolate
  ring

private theorem left_eq_of_endpoint_max
    {weight left right value : ℝ} (hweight : weight ∈ Set.Icc (0 : ℝ) 1)
    (hpositive : 0 < weight)
    (hblend : value = weight * left + (1 - weight) * right)
    (hleft : left ≤ value) (hright : right ≤ value) : value = left := by
  have hnonneg := mul_nonneg (sub_nonneg.mpr hweight.2) (sub_nonneg.mpr hright)
  have hzero : weight * (value - left) = 0 := by
    nlinarith [mul_nonneg hweight.1 (sub_nonneg.mpr hleft)]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hpositive.ne')

/-- Endpoint Nash inequalities internally select a positively weighted corner
whose positive escape product is at least four times the root product.
Only the five scalar corner bounds actually used by the printed calculation
are required. Both orientations of the selected corner are returned. -/
theorem active_corner_fourfold_escape
    (a b : Bool → Bool → ℝ) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ha01 : a false true ≤ 5) (ha11 : a true true ≤ 5)
    (hb01 : 1 ≤ b false true) (hb11 : 1 ≤ b true true)
    (hb10 : b true false ≤ 5)
    (hrow0 : row a 0 t ≤ row a s t) (hrow1 : row a 1 t ≤ row a s t)
    (hcolumn0 : column b s 0 ≤ column b s t)
    (hcolumn1 : column b s 1 ≤ column b s t)
    (hfeasible : row a s t + column b s t ≤ 8)
    (hrow : 4 < row a s t) (hcolumn : 1 < column b s t) :
    (0 < s * t ∧ 4 < a false false ∧ 1 < b false false ∧
      4 * (row a s t - 4) * (column b s t - 1) ≤
        (a false false - 4) * (b false false - 1)) ∨
    (0 < (1 - s) * t ∧ 4 < b true false ∧ 1 < a true false ∧
      4 * (row a s t - 4) * (column b s t - 1) ≤
        (b true false - 4) * (a true false - 1)) := by
  let x := row a s t - 4
  let y := column b s t - 1
  have hx : 0 < x := sub_pos.mpr hrow
  have hy : 0 < y := sub_pos.mpr hcolumn
  have hy3 : y < 3 := by dsimp [y]; linarith
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := le_antisymm (le_of_not_gt hnot) ht.1
    have ha := mul_nonneg hs.1 (sub_nonneg.mpr ha01)
    have hb := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr ha11)
    norm_num [row, interpolate, htzero] at hrow
    nlinarith [hs.1, hs.2]
  have hslt : s < 1 := by
    by_contra hnot
    have hsone : s = 1 := le_antisymm hs.2 (le_of_not_gt hnot)
    have hfour : 4 ≤ column b s 0 := by
      rw [hsone]
      norm_num [column, interpolate]
      linarith
    linarith
  have hrowZero : row a s t = row a 0 t := by
    apply left_eq_of_endpoint_max
      (weight := 1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      (sub_pos.mpr hslt) _ hrow0 hrow1
    rw [row_affine]
    ring
  have hcolumnOne : column b s t = column b s 1 :=
    left_eq_of_endpoint_max ht htpos (column_affine b s t) hcolumn1 hcolumn0
  have heq1 : 16 + 4 * x =
      3 * (5 * t + (1 - t)) + t * a true false + (1 - t) * a true true := by
    dsimp [x]
    rw [hrowZero]
    unfold row interpolate
    ring
  have heq2 : 4 + 4 * y =
      12 * s + s * b false false + (1 - s) * b true false := by
    dsimp [y]
    rw [hcolumnOne]
    unfold column interpolate
    ring
  have ha3 : 1 + 4 * x ≤ a true false := by
    have hbound := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha11)
    have hresidual := mul_nonneg (sub_nonneg.mpr ht.2)
      (show 0 ≤ 8 + 4 * x by linarith)
    have hscaled : 0 ≤ t * (a true false - (1 + 4 * x)) := by nlinarith
    have hnonneg := nonneg_of_mul_nonneg_right hscaled htpos
    linarith
  by_cases hszero : s = 0
  · right
    have hb3 : b true false = 4 + 4 * y := by rw [hszero] at heq2; nlinarith
    refine ⟨by rw [hszero]; simpa using htpos, by linarith, by linarith, ?_⟩
    have hproduct := mul_le_mul_of_nonneg_left
      (show 4 * x ≤ a true false - 1 by linarith)
      (show 0 ≤ b true false - 4 by linarith)
    change 4 * x * y ≤ _
    rw [hb3] at hproduct ⊢
    nlinarith [mul_pos hx hy]
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hszero)
    have hrowOne : row a s t = row a 1 t :=
      left_eq_of_endpoint_max hs hspos (row_affine a s t) hrow1 hrow0
    have heq4 : 16 + 4 * x =
        12 * t + t * a false false + (1 - t) * a false true := by
      dsimp [x]
      rw [hrowOne]
      unfold row interpolate
      ring
    have heq5 : 4 + 4 * y ≥
        3 + 12 * s + s * b false true + (1 - s) * b true true := by
      have h := hcolumn0
      have hvalue : column b s t = 1 + y := by dsimp [y]; ring
      rw [hvalue] at h
      unfold column interpolate at h
      nlinarith
    have hbound := add_nonneg
      (mul_nonneg hs.1 (sub_nonneg.mpr hb01))
      (mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hb11))
    have heq6 : 4 ≤ s * b false false + (1 - s) * b true false := by
      nlinarith
    have hsbound : s ≤ y / 3 := by nlinarith
    have ha1 : 4 + 4 * x ≤ a false false := by
      have hbound := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha01)
      have hresidual := mul_nonneg (sub_nonneg.mpr ht.2)
        (show 0 ≤ 11 + 4 * x by linarith)
      have hscaled : 0 ≤ t * (a false false - (4 + 4 * x)) := by nlinarith
      have hnonneg := nonneg_of_mul_nonneg_right hscaled htpos
      linarith
    by_cases hb1 : 1 + y ≤ b false false
    · left
      refine ⟨mul_pos hspos htpos, by linarith, by linarith, ?_⟩
      have hfirst := mul_le_mul_of_nonneg_left
        (show 4 * x ≤ a false false - 4 by linarith)
        (show 0 ≤ b false false - 1 by linarith)
      have hsecond := mul_le_mul_of_nonneg_left
        (show y ≤ b false false - 1 by linarith) (show 0 ≤ 4 * x by linarith)
      change 4 * x * y ≤ _
      calc
        4 * x * y ≤ (4 * x) * (b false false - 1) := hsecond
        _ = (b false false - 1) * (4 * x) := mul_comm _ _
        _ ≤ (b false false - 1) * (a false false - 4) := hfirst
        _ = (a false false - 4) * (b false false - 1) := mul_comm _ _
    · have hb1lt : b false false < 1 + y := lt_of_not_ge hb1
      have hgap := mul_pos hspos (sub_pos.mpr hb1lt)
      have hcoefficient : 0 < 13 + y - b true false := by linarith
      have hscale := mul_le_mul_of_nonneg_right hsbound hcoefficient.le
      have hcleared : 0 < (3 - y) * (b true false - (4 + y)) := by nlinarith
      have hb3 : 4 + y < b true false := by
        by_contra hnot
        have hnonpos := mul_nonpos_of_nonneg_of_nonpos
          (show 0 ≤ 3 - y by linarith) (sub_nonpos.mpr (le_of_not_gt hnot))
        linarith
      right
      refine ⟨mul_pos (sub_pos.mpr hslt) htpos, by linarith, by linarith, ?_⟩
      have hfirst := mul_le_mul_of_nonneg_left
        (show 4 * x ≤ a true false - 1 by linarith)
        (show 0 ≤ b true false - 4 by linarith)
      have hsecond := mul_le_mul_of_nonneg_left
        (show y ≤ b true false - 4 by linarith) (show 0 ≤ 4 * x by linarith)
      change 4 * x * y ≤ _
      calc
        4 * x * y ≤ (4 * x) * (b true false - 4) := hsecond
        _ = (b true false - 4) * (4 * x) := mul_comm _ _
        _ ≤ (b true false - 4) * (a true false - 1) := hfirst

/-- Fourfold growth is strict improvement whenever the root escape product
is positive. This retains the closed-boundary cases of the source estimate. -/
theorem escape_strict_of_fourfold
    {x y next : ℝ} (hx : 0 < x) (hy : 0 < y) (hnext : 4 * x * y ≤ next) :
    x * y < next := by
  nlinarith [mul_pos hx hy]

end Math.BilinearQuarter
