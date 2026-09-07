import MathUE.Polynomial.OrderedRealSignDiagram
import MathUE.Polynomial.InfinitySign

/-!
# Complete local sign-row reconstruction

Executable row transformations insert the new polynomial's column on one old
cell. Their realizations identify exactly the roots inserted into that cell.
-/

namespace MathUE.OrderedRealSignDiagram

open Set SignType RealSignCell

/-- The old open cell, either unsplit or split at one new root. -/
def localCells (lower upper : Option ℝ) : Option ℝ → List (Set ℝ)
  | none => [openCell lower upper]
  | some c => [openCell lower (some c), {c}, openCell (some c) upper]

/-- Local reconstruction includes correct signs and exact coverage of the new
polynomial's roots, not merely the existence of some suitable cut. -/
def LocalRealizes (p : Polynomial ℝ) (polynomials : List (Polynomial ℝ))
    (lower upper : Option ℝ) (rows : List (List SignType)) : Prop :=
  ∃ root : Option ℝ,
    (∀ c, root = some c → c ∈ openCell lower upper) ∧
    (∀ x ∈ openCell lower upper, p.eval x = 0 ↔ root = some x) ∧
    RowsOn (p :: polynomials) (localCells lower upper root) rows

/-- An increasing cell crosses zero exactly for negative/positive boundary signs. -/
def increasingCrossing (left right : SignType) : Bool :=
  decide (left = .neg) && decide (right = .pos)

/-- A decreasing cell crosses zero exactly for positive/negative boundary signs. -/
def decreasingCrossing (left right : SignType) : Bool :=
  decide (left = .pos) && decide (right = .neg)

/-- Executable increasing-cell reconstruction from the two boundary signs. -/
def increasingCellRows (left right : SignType) (row : List SignType) :
    List (List SignType) :=
  if increasingCrossing left right then rootSplitRows row .neg .pos
  else [increasingNoRootSign left :: row]

/-- Executable decreasing-cell reconstruction from the two boundary signs. -/
def decreasingCellRows (left right : SignType) (row : List SignType) :
    List (List SignType) :=
  if decreasingCrossing left right then rootSplitRows row .pos .neg
  else [decreasingNoRootSign left :: row]

theorem LocalRealizes.of_no_root {p : Polynomial ℝ} {polynomials : List (Polynomial ℝ)}
    {lower upper : Option ℝ} {row : List SignType} {newSign : SignType}
    (hrow : RowOn polynomials (openCell lower upper) row)
    (hn : ∀ x ∈ openCell lower upper, p.eval x ≠ 0)
    (hsign : SignOn p newSign (openCell lower upper)) :
    LocalRealizes p polynomials lower upper [newSign :: row] := by
  refine ⟨none, by simp, ?_, List.Forall₂.cons (List.Forall₂.cons hsign hrow) .nil⟩
  intro x hx
  simp [hn x hx]

theorem LocalRealizes.of_root {p : Polynomial ℝ} {polynomials : List (Polynomial ℝ)}
    {lower upper : Option ℝ} {row : List SignType} {c : ℝ} {before after : SignType}
    (hrow : RowOn polynomials (openCell lower upper) row)
    (hc : c ∈ openCell lower upper) (hz : p.eval c = 0)
    (hunique : ∀ x ∈ openCell lower upper, p.eval x = 0 ↔ x = c)
    (hleft : SignOn p before (openCell lower (some c)))
    (hright : SignOn p after (openCell (some c) upper)) :
    LocalRealizes p polynomials lower upper (rootSplitRows row before after) := by
  refine ⟨some c, ?_, ?_, List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ .nil))⟩
  · intro x hx
    have hcx : c = x := Option.some.inj hx
    exact hcx ▸ hc
  · intro x hx
    simpa only [Option.some.injEq, eq_comm] using hunique x hx
  · exact List.Forall₂.cons hleft
      (hrow.mono (fun _ hx => ⟨hx.1, below_of_lt hx.2 hc.2⟩))
  · apply List.Forall₂.cons
    · intro x hx
      have hxc : x = c := hx
      subst x
      exact sign_eq_zero_iff.mpr hz
    · exact hrow.mono (fun x hx => (show x = c from hx) ▸ hc)
  · exact List.Forall₂.cons hright
      (hrow.mono (fun _ hx => ⟨above_of_lt hc.1 hx.1, hx.2⟩))

theorem localRealizes_increasing_of_cases (p : Polynomial ℝ)
    {polynomials : List (Polynomial ℝ)} {lower upper : Option ℝ} {row : List SignType}
    {left right : SignType}
    (hrow : RowOn polynomials (openCell lower upper) row)
    (hm : StrictMonoOn p.eval (openCell lower upper))
    (hroot : increasingCrossing left right = true ↔
      ∃ c ∈ openCell lower upper, p.eval c = 0)
    (hno : increasingCrossing left right = false →
      SignOn p (increasingNoRootSign left) (openCell lower upper)) :
    LocalRealizes p polynomials lower upper (increasingCellRows left right row) := by
  cases hcross : increasingCrossing left right with
  | false =>
      rw [increasingCellRows, hcross]
      apply LocalRealizes.of_no_root hrow
      · intro x hx hz
        have := hroot.mpr ⟨x, hx, hz⟩
        simp only [hcross, Bool.false_eq_true] at this
      · exact hno hcross
  | true =>
      rw [increasingCellRows, hcross]
      obtain ⟨c, hc, hz⟩ := hroot.mp hcross
      apply LocalRealizes.of_root hrow hc hz
      · intro x hx
        simpa only [hz] using hm.eq_iff_eq hx hc
      · intro x hx
        have hxc : x ∈ openCell lower upper := ⟨hx.1, below_of_lt hx.2 hc.2⟩
        apply sign_eq_neg_one_iff.mpr
        simpa only [hz] using hm hxc hc hx.2
      · intro x hx
        have hxc : x ∈ openCell lower upper := ⟨above_of_lt hc.1 hx.1, hx.2⟩
        apply sign_eq_one_iff.mpr
        simpa only [hz] using hm hc hxc hx.1

theorem localRealizes_decreasing_of_cases (p : Polynomial ℝ)
    {polynomials : List (Polynomial ℝ)} {lower upper : Option ℝ} {row : List SignType}
    {left right : SignType}
    (hrow : RowOn polynomials (openCell lower upper) row)
    (hm : StrictAntiOn p.eval (openCell lower upper))
    (hroot : decreasingCrossing left right = true ↔
      ∃ c ∈ openCell lower upper, p.eval c = 0)
    (hno : decreasingCrossing left right = false →
      SignOn p (decreasingNoRootSign left) (openCell lower upper)) :
    LocalRealizes p polynomials lower upper (decreasingCellRows left right row) := by
  cases hcross : decreasingCrossing left right with
  | false =>
      rw [decreasingCellRows, hcross]
      apply LocalRealizes.of_no_root hrow
      · intro x hx hz
        have := hroot.mpr ⟨x, hx, hz⟩
        simp only [hcross, Bool.false_eq_true] at this
      · exact hno hcross
  | true =>
      rw [decreasingCellRows, hcross]
      obtain ⟨c, hc, hz⟩ := hroot.mp hcross
      apply LocalRealizes.of_root hrow hc hz
      · intro x hx
        simpa only [hz, eq_comm] using hm.eq_iff_eq hx hc
      · intro x hx
        have hxc : x ∈ openCell lower upper := ⟨hx.1, below_of_lt hx.2 hc.2⟩
        apply sign_eq_one_iff.mpr
        simpa only [hz] using hm hxc hc hx.2
      · intro x hx
        have hxc : x ∈ openCell lower upper := ⟨above_of_lt hc.1 hx.1, hx.2⟩
        apply sign_eq_neg_one_iff.mpr
        simpa only [hz] using hm hc hxc hx.1

/-- Complete bounded increasing-cell reconstruction, including endpoint roots and no-root cases. -/
theorem reconstruct_bounded_increasing (p : Polynomial ℝ)
    {polynomials : List (Polynomial ℝ)} {row : List SignType} {a b : ℝ}
    (hab : a < b) (hd : ∀ x ∈ Ioo a b, 0 < p.derivative.eval x)
    (hrow : RowOn polynomials (Ioo a b) row) :
    LocalRealizes p polynomials (some a) (some b)
      (increasingCellRows (sign (p.eval a)) (sign (p.eval b)) row) := by
  have hm := polynomial_strictMonoOn_of_derivative_pos p hd
  have hroot : increasingCrossing (sign (p.eval a)) (sign (p.eval b)) = true ↔
      ∃ c ∈ Ioo a b, p.eval c = 0 := by
    simpa only [increasingCrossing, Bool.and_eq_true, decide_eq_true_eq,
      SignType.neg_eq_neg_one, SignType.pos_eq_one, sign_eq_neg_one_iff, sign_eq_one_iff]
      using (exists_root_iff_of_strictMonoOn hab p.continuous.continuousOn hm).symm
  apply localRealizes_increasing_of_cases p (lower := some a) (upper := some b)
    hrow (hm.mono Ioo_subset_Icc_self) hroot
  intro hfalse x hx
  apply polynomial_increasing_noRoot_sign p hd
  · intro y hy hz
    have := hroot.mpr ⟨y, hy, hz⟩
    simp only [hfalse, Bool.false_eq_true] at this
  · exact hx

/-- Complete bounded decreasing-cell reconstruction. -/
theorem reconstruct_bounded_decreasing (p : Polynomial ℝ)
    {polynomials : List (Polynomial ℝ)} {row : List SignType} {a b : ℝ}
    (hab : a < b) (hd : ∀ x ∈ Ioo a b, p.derivative.eval x < 0)
    (hrow : RowOn polynomials (Ioo a b) row) :
    LocalRealizes p polynomials (some a) (some b)
      (decreasingCellRows (sign (p.eval a)) (sign (p.eval b)) row) := by
  have hm := polynomial_strictAntiOn_of_derivative_neg p hd
  have hroot : decreasingCrossing (sign (p.eval a)) (sign (p.eval b)) = true ↔
      ∃ c ∈ Ioo a b, p.eval c = 0 := by
    simpa only [decreasingCrossing, Bool.and_eq_true, decide_eq_true_eq,
      SignType.neg_eq_neg_one, SignType.pos_eq_one, sign_eq_neg_one_iff, sign_eq_one_iff]
      using (exists_root_iff_of_strictAntiOn hab p.continuous.continuousOn hm).symm
  apply localRealizes_decreasing_of_cases p (lower := some a) (upper := some b)
    hrow (hm.mono Ioo_subset_Icc_self) hroot
  intro hfalse x hx
  apply polynomial_decreasing_noRoot_sign p hd
  · intro y hy hz
    have := hroot.mpr ⟨y, hy, hz⟩
    simp only [hfalse, Bool.false_eq_true] at this
  · exact hx

theorem openCell_right (a : ℝ) : openCell (some a) none = Ioi a := by
  ext x
  simp [openCell, Above, Below]

theorem openCell_left (b : ℝ) : openCell none (some b) = Iio b := by
  ext x
  simp [openCell, Above, Below]

theorem openCell_whole : openCell none none = (univ : Set ℝ) := by
  ext x
  simp [openCell, Above, Below]

/-- Complete right-ray increasing reconstruction, using the positive sign at infinity. -/
theorem reconstruct_right_increasing (p : Polynomial ℝ)
    {polynomials : List (Polynomial ℝ)} {row : List SignType} {a : ℝ}
    (hd : ∀ x ∈ Ioi a, 0 < p.derivative.eval x)
    (hrow : RowOn polynomials (Ioi a) row) :
    LocalRealizes p polynomials (some a) none
      (increasingCellRows (sign (p.eval a)) .pos row) := by
  have hm : StrictMonoOn p.eval (Ici a) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici a) p.continuous.continuousOn
    simpa only [interior_Ici, Polynomial.deriv] using hd
  have hroot : increasingCrossing (sign (p.eval a)) .pos = true ↔
      ∃ c ∈ openCell (some a) none, p.eval c = 0 := by
    simpa [increasingCrossing, openCell_right, SignType.neg_eq_neg_one,
      sign_eq_neg_one_iff] using (polynomial_right_root_iff_of_derivative_pos p hd).symm
  apply localRealizes_increasing_of_cases p (lower := some a) (upper := none)
    (by simpa only [openCell_right] using hrow) (hm.mono (fun _ hx => hx.1.le)) hroot
  intro hfalse x hx
  apply polynomial_increasing_noRoot_sign p (b := x + 1)
  · intro y hy
    exact hd y hy.1
  · intro y hy hz
    have := hroot.mpr ⟨y, ⟨hy.1, trivial⟩, hz⟩
    simp only [hfalse, Bool.false_eq_true] at this
  · exact ⟨hx.1, by linarith⟩

/-- Complete right-ray decreasing reconstruction, using the negative sign at infinity. -/
theorem reconstruct_right_decreasing (p : Polynomial ℝ)
    {polynomials : List (Polynomial ℝ)} {row : List SignType} {a : ℝ}
    (hd : ∀ x ∈ Ioi a, p.derivative.eval x < 0)
    (hrow : RowOn polynomials (Ioi a) row) :
    LocalRealizes p polynomials (some a) none
      (decreasingCellRows (sign (p.eval a)) .neg row) := by
  have hm : StrictAntiOn p.eval (Ici a) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici a) p.continuous.continuousOn
    simpa only [interior_Ici, Polynomial.deriv] using hd
  have hroot : decreasingCrossing (sign (p.eval a)) .neg = true ↔
      ∃ c ∈ openCell (some a) none, p.eval c = 0 := by
    simpa [decreasingCrossing, openCell_right, SignType.pos_eq_one,
      sign_eq_one_iff] using (polynomial_right_root_iff_of_derivative_neg p hd).symm
  apply localRealizes_decreasing_of_cases p (lower := some a) (upper := none)
    (by simpa only [openCell_right] using hrow) (hm.mono (fun _ hx => hx.1.le)) hroot
  intro hfalse x hx
  apply polynomial_decreasing_noRoot_sign p (b := x + 1)
  · intro y hy
    exact hd y hy.1
  · intro y hy hz
    have := hroot.mpr ⟨y, ⟨hy.1, trivial⟩, hz⟩
    simp only [hfalse, Bool.false_eq_true] at this
  · exact ⟨hx.1, by linarith⟩

/-- Complete left-ray increasing reconstruction, using the negative sign at infinity. -/
theorem reconstruct_left_increasing (p : Polynomial ℝ)
    {polynomials : List (Polynomial ℝ)} {row : List SignType} {b : ℝ}
    (hd : ∀ x ∈ Iio b, 0 < p.derivative.eval x)
    (hrow : RowOn polynomials (Iio b) row) :
    LocalRealizes p polynomials none (some b)
      (increasingCellRows .neg (sign (p.eval b)) row) := by
  have hm : StrictMonoOn p.eval (Iic b) := by
    apply strictMonoOn_of_deriv_pos (convex_Iic b) p.continuous.continuousOn
    simpa only [interior_Iic, Polynomial.deriv] using hd
  have hroot : increasingCrossing .neg (sign (p.eval b)) = true ↔
      ∃ c ∈ openCell none (some b), p.eval c = 0 := by
    simpa [increasingCrossing, openCell_left, SignType.pos_eq_one,
      sign_eq_one_iff] using (polynomial_left_root_iff_of_derivative_pos p hd).symm
  apply localRealizes_increasing_of_cases p (lower := none) (upper := some b)
    (by simpa only [openCell_left] using hrow) (hm.mono (fun _ hx => hx.2.le)) hroot
  intro hfalse x hx
  have hb : p.eval b ≤ 0 := by
    by_contra hneg
    have h := (polynomial_left_root_iff_of_derivative_pos p hd).mpr (lt_of_not_ge hneg)
    have hcross := hroot.mpr (by simpa only [openCell_left] using h)
    simp only [hfalse, Bool.false_eq_true] at hcross
  have hxb := hm hx.2.le (mem_Iic.mpr (le_refl b)) hx.2
  exact sign_eq_neg_one_iff.mpr (lt_of_lt_of_le hxb hb)

/-- Complete left-ray decreasing reconstruction, using the positive sign at infinity. -/
theorem reconstruct_left_decreasing (p : Polynomial ℝ)
    {polynomials : List (Polynomial ℝ)} {row : List SignType} {b : ℝ}
    (hd : ∀ x ∈ Iio b, p.derivative.eval x < 0)
    (hrow : RowOn polynomials (Iio b) row) :
    LocalRealizes p polynomials none (some b)
      (decreasingCellRows .pos (sign (p.eval b)) row) := by
  have hm : StrictAntiOn p.eval (Iic b) := by
    apply strictAntiOn_of_deriv_neg (convex_Iic b) p.continuous.continuousOn
    simpa only [interior_Iic, Polynomial.deriv] using hd
  have hroot : decreasingCrossing .pos (sign (p.eval b)) = true ↔
      ∃ c ∈ openCell none (some b), p.eval c = 0 := by
    simpa [decreasingCrossing, openCell_left, SignType.neg_eq_neg_one,
      sign_eq_neg_one_iff] using (polynomial_left_root_iff_of_derivative_neg p hd).symm
  apply localRealizes_decreasing_of_cases p (lower := none) (upper := some b)
    (by simpa only [openCell_left] using hrow) (hm.mono (fun _ hx => hx.2.le)) hroot
  intro hfalse x hx
  have hb : 0 ≤ p.eval b := by
    by_contra hneg
    have h := (polynomial_left_root_iff_of_derivative_neg p hd).mpr (lt_of_not_ge hneg)
    have hcross := hroot.mpr (by simpa only [openCell_left] using h)
    simp only [hfalse, Bool.false_eq_true] at hcross
  have hxb := hm hx.2.le (mem_Iic.mpr (le_refl b)) hx.2
  exact sign_eq_one_iff.mpr (lt_of_le_of_lt hb hxb)

/-- A globally increasing polynomial contributes exactly one root and three rows. -/
theorem reconstruct_whole_increasing (p : Polynomial ℝ)
    {polynomials : List (Polynomial ℝ)} {row : List SignType}
    (hd : ∀ x : ℝ, 0 < p.derivative.eval x) (hrow : RowOn polynomials univ row) :
    LocalRealizes p polynomials none none (increasingCellRows .neg .pos row) := by
  have hm : StrictMono p.eval := strictMono_of_deriv_pos (fun x => by simpa using hd x)
  apply localRealizes_increasing_of_cases p (lower := none) (upper := none)
    (by simpa only [openCell_whole] using hrow) (hm.strictMonoOn _)
  · obtain ⟨c, hz, _⟩ := polynomial_exists_wholeLine_increasing_root p hd
    exact ⟨fun _ => ⟨c, ⟨trivial, trivial⟩, hz⟩, fun _ => rfl⟩
  · intro hfalse
    contradiction

/-- A globally decreasing polynomial contributes exactly one root and three rows. -/
theorem reconstruct_whole_decreasing (p : Polynomial ℝ)
    {polynomials : List (Polynomial ℝ)} {row : List SignType}
    (hd : ∀ x : ℝ, p.derivative.eval x < 0) (hrow : RowOn polynomials univ row) :
    LocalRealizes p polynomials none none (decreasingCellRows .pos .neg row) := by
  have hm : StrictAnti p.eval := strictAnti_of_deriv_neg (fun x => by simpa using hd x)
  apply localRealizes_decreasing_of_cases p (lower := none) (upper := none)
    (by simpa only [openCell_whole] using hrow) (hm.strictAntiOn _)
  · obtain ⟨c, hz, _⟩ := polynomial_exists_wholeLine_decreasing_root p hd
    exact ⟨fun _ => ⟨c, ⟨trivial, trivial⟩, hz⟩, fun _ => rfl⟩
  · intro hfalse
    contradiction

/-- One executable dispatcher for bounded cells, either ray, and the whole line.
Missing boundary signs are inferred from the derivative's direction. -/
def reconstructCellRows (direction : SignType) (left right : Option SignType)
    (row : List SignType) : List (List SignType) :=
  match direction with
  | .neg => decreasingCellRows (left.getD .pos) (right.getD .neg) row
  | _ => increasingCellRows (left.getD .neg) (right.getD .pos) row

/-- The dispatcher reconstructs every nonempty old open cell whenever its derivative
column has a fixed nonzero sign. The output covers exactly the new roots in that cell. -/
theorem reconstruct_cell (p : Polynomial ℝ)
    {polynomials : List (Polynomial ℝ)} {row : List SignType}
    {lower upper : Option ℝ} {direction : SignType}
    (hcell : (openCell lower upper).Nonempty) (hdirection : direction ≠ 0)
    (hderivative : SignOn p.derivative direction (openCell lower upper))
    (hrow : RowOn polynomials (openCell lower upper) row) :
    LocalRealizes p polynomials lower upper
      (reconstructCellRows direction (lower.map (fun a => sign (p.eval a)))
        (upper.map (fun b => sign (p.eval b))) row) := by
  cases direction with
  | zero => exact False.elim (hdirection rfl)
  | neg =>
      have hd : ∀ x ∈ openCell lower upper, p.derivative.eval x < 0 :=
        fun x hx => sign_eq_neg_one_iff.mp (hderivative x hx)
      cases lower with
      | none =>
          cases upper with
          | none =>
              simpa [reconstructCellRows] using reconstruct_whole_decreasing p
                (fun x => hd x ⟨trivial, trivial⟩)
                (by simpa only [openCell_whole] using hrow)
          | some b =>
              simpa [reconstructCellRows] using reconstruct_left_decreasing p
                (by simpa only [openCell_left] using hd)
                (by simpa only [openCell_left] using hrow)
      | some a =>
          cases upper with
          | none =>
              simpa [reconstructCellRows] using reconstruct_right_decreasing p
                (by simpa only [openCell_right] using hd)
                (by simpa only [openCell_right] using hrow)
          | some b =>
              obtain ⟨x, hx⟩ := hcell
              simpa [reconstructCellRows] using
                reconstruct_bounded_decreasing p (lt_trans hx.1 hx.2) hd hrow
  | pos =>
      have hd : ∀ x ∈ openCell lower upper, 0 < p.derivative.eval x :=
        fun x hx => sign_eq_one_iff.mp (hderivative x hx)
      cases lower with
      | none =>
          cases upper with
          | none =>
              simpa [reconstructCellRows] using reconstruct_whole_increasing p
                (fun x => hd x ⟨trivial, trivial⟩)
                (by simpa only [openCell_whole] using hrow)
          | some b =>
              simpa [reconstructCellRows] using reconstruct_left_increasing p
                (by simpa only [openCell_left] using hd)
                (by simpa only [openCell_left] using hrow)
      | some a =>
          cases upper with
          | none =>
              simpa [reconstructCellRows] using reconstruct_right_increasing p
                (by simpa only [openCell_right] using hd)
                (by simpa only [openCell_right] using hrow)
          | some b =>
              obtain ⟨x, hx⟩ := hcell
              simpa [reconstructCellRows] using
                reconstruct_bounded_increasing p (lt_trans hx.1 hx.2) hd hrow

/-- The open cells only, in their original order; singleton cut cells are omitted. -/
def openCellsFrom (lower : Option ℝ) : List ℝ → List (Set ℝ)
  | [] => [openCell lower none]
  | c :: cuts => openCell lower (some c) :: openCellsFrom (some c) cuts

theorem OrderedFrom.above_of_mem {lower : Option ℝ} {cuts : List ℝ}
    (h : OrderedFrom lower cuts) {c : ℝ} (hc : c ∈ cuts) : Above lower c := by
  induction cuts generalizing lower with
  | nil => cases hc
  | cons d cuts ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h.1
      · exact above_of_lt h.1 (ih h.2 hc)

theorem mem_cellsFrom_of_mem_openCellsFrom {lower : Option ℝ} {cuts : List ℝ}
    {cell : Set ℝ} (hcell : cell ∈ openCellsFrom lower cuts) :
    cell ∈ cellsFrom lower cuts := by
  induction cuts generalizing lower with
  | nil => exact hcell
  | cons c cuts ih =>
      rcases List.mem_cons.mp hcell with rfl | hcell
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih hcell))

/-- No cut lies in any of the open cells of its own ordered decomposition. -/
theorem not_mem_cuts_of_mem_openCell {lower : Option ℝ} {cuts : List ℝ}
    (hcuts : OrderedFrom lower cuts) {cell : Set ℝ}
    (hcell : cell ∈ openCellsFrom lower cuts) {x : ℝ} (hx : x ∈ cell) : x ∉ cuts := by
  induction cuts generalizing lower with
  | nil => simp
  | cons c cuts ih =>
      rcases List.mem_cons.mp hcell with rfl | hcell
      · intro hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact lt_irrefl _ hx.2
        · exact lt_asymm hx.2 (hcuts.2.above_of_mem hmem)
      · intro hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · have hcx := (cellsFrom_cover hcuts.2 _).mp
            ⟨cell, mem_cellsFrom_of_mem_openCellsFrom hcell, hx⟩
          exact lt_irrefl _ hcx
        · exact ih hcuts.2 hcell hmem

/-- Reduced root coverage forces every nonzero input polynomial's open-cell sign to be
nonzero. Applied to the derivative, this supplies the dispatcher's direction hypothesis. -/
theorem interval_sign_ne_zero_of_root_coverage {cuts : List ℝ}
    {polynomials : List (Polynomial ℝ)} {p : Polynomial ℝ} {cell : Set ℝ} {s : SignType}
    (hcuts : OrderedFrom none cuts)
    (hroots : ∀ x, x ∈ cuts ↔ ∃ q ∈ polynomials, q ≠ 0 ∧ q.eval x = 0)
    (hp : p ∈ polynomials) (hpzero : p ≠ 0)
    (hcell : cell ∈ openCellsFrom none cuts) (hsign : SignOn p s cell) : s ≠ 0 := by
  obtain ⟨x, hx⟩ := cellsFrom_nonempty hcuts cell
    (mem_cellsFrom_of_mem_openCellsFrom hcell)
  intro hs
  have hzero : p.eval x = 0 := sign_eq_zero_iff.mp ((hsign x hx).trans hs)
  exact not_mem_cuts_of_mem_openCell hcuts hcell hx
    ((hroots x).mpr ⟨p, hp, hpzero, hzero⟩)

/-- Reconstruction on a reduced source diagram derives the nonzero derivative sign
from its root invariant and the selected polynomial's positive degree. -/
theorem reconstruct_cell_of_root_coverage (p : Polynomial ℝ)
    {sourcePolynomials polynomials : List (Polynomial ℝ)} {cuts : List ℝ}
    {lower upper : Option ℝ} {direction : SignType} {row : List SignType}
    (hcuts : OrderedFrom none cuts)
    (hroots : ∀ x, x ∈ cuts ↔ ∃ q ∈ sourcePolynomials, q ≠ 0 ∧ q.eval x = 0)
    (hmember : p.derivative ∈ sourcePolynomials) (hdegree : 0 < p.natDegree)
    (hcell : openCell lower upper ∈ openCellsFrom none cuts)
    (hderivative : SignOn p.derivative direction (openCell lower upper))
    (hrow : RowOn polynomials (openCell lower upper) row) :
    LocalRealizes p polynomials lower upper
      (reconstructCellRows direction (lower.map (fun a => sign (p.eval a)))
        (upper.map (fun b => sign (p.eval b))) row) := by
  apply reconstruct_cell p
  · exact cellsFrom_nonempty hcuts _ (mem_cellsFrom_of_mem_openCellsFrom hcell)
  · exact interval_sign_ne_zero_of_root_coverage hcuts hroots hmember
      (Polynomial.derivative_ne_zero.mpr hdegree.ne') hcell hderivative
  · exact hderivative
  · exact hrow

end MathUE.OrderedRealSignDiagram
