import MathUE.Polynomial.RealSignCell
import Mathlib.Data.Sign.Defs
import Mathlib.Data.List.Forall2
import Mathlib.Topology.Instances.Sign

/-!
# Ordered real cells and sign-diagram realization

Finite ordered cuts determine nonempty alternating open cells and singleton
cells. This file proves their coverage and local merge correctness. It does not
produce sign diagrams from arbitrary polynomial families.
-/

namespace MathUE.OrderedRealSignDiagram

open Set

/-- A missing lower endpoint denotes negative infinity. -/
def Above : Option ℝ → ℝ → Prop
  | none, _ => True
  | some a, x => a < x

/-- A missing upper endpoint denotes positive infinity. -/
def Below : Option ℝ → ℝ → Prop
  | none, _ => True
  | some b, x => x < b

/-- An open real interval, allowing either endpoint to be infinite. -/
def openCell (lower upper : Option ℝ) : Set ℝ :=
  {x | Above lower x ∧ Below upper x}

/-- The cuts strictly increase, and the first cut lies above the lower endpoint. -/
def OrderedFrom : Option ℝ → List ℝ → Prop
  | _, [] => True
  | lower, c :: cuts => Above lower c ∧ OrderedFrom (some c) cuts

/-- Alternating open intervals and singleton cut cells, ending at positive infinity. -/
def cellsFrom (lower : Option ℝ) : List ℝ → List (Set ℝ)
  | [] => [openCell lower none]
  | c :: cuts => openCell lower (some c) :: {c} :: cellsFrom (some c) cuts

theorem above_of_lt {lower : Option ℝ} {c x : ℝ}
    (hc : Above lower c) (hcx : c < x) : Above lower x := by
  cases lower with
  | none => trivial
  | some a => exact lt_trans hc hcx

theorem below_of_lt {upper : Option ℝ} {x c : ℝ}
    (hxc : x < c) (hc : Below upper c) : Below upper x := by
  cases upper with
  | none => trivial
  | some b => exact lt_trans hxc hc

theorem openCell_right_nonempty (lower : Option ℝ) :
    (openCell lower none).Nonempty := by
  cases lower with
  | none => exact ⟨0, trivial, trivial⟩
  | some a => exact ⟨a + 1, by dsimp [openCell, Above, Below]; constructor; linarith; trivial⟩

theorem openCell_left_nonempty {lower : Option ℝ} {c : ℝ}
    (hc : Above lower c) : (openCell lower (some c)).Nonempty := by
  cases lower with
  | none => exact ⟨c - 1, by dsimp [openCell, Above, Below]; constructor; trivial; linarith⟩
  | some a =>
      exact ⟨(a + c) / 2, by dsimp [openCell, Above, Below, Above] at *; constructor <;>
        linarith⟩

@[simp]
theorem cellsFrom_length (lower : Option ℝ) (cuts : List ℝ) :
    (cellsFrom lower cuts).length = 2 * cuts.length + 1 := by
  induction cuts generalizing lower with
  | nil => rfl
  | cons c cuts ih => simp only [cellsFrom, List.length_cons, ih]; omega

theorem cellsFrom_nonempty {lower : Option ℝ} {cuts : List ℝ}
    (hcuts : OrderedFrom lower cuts) :
    ∀ cell ∈ cellsFrom lower cuts, cell.Nonempty := by
  induction cuts generalizing lower with
  | nil =>
      intro cell hcell
      have : cell = openCell lower none := by simpa only [cellsFrom, List.mem_singleton] using hcell
      subst cell
      exact openCell_right_nonempty lower
  | cons c cuts ih =>
      intro cell hcell
      rcases List.mem_cons.mp hcell with rfl | hcell
      · exact openCell_left_nonempty hcuts.1
      rcases List.mem_cons.mp hcell with rfl | hcell
      · exact singleton_nonempty c
      · exact ih hcuts.2 cell hcell

/-- The cells cover exactly the part of the real line above their initial lower bound. -/
theorem cellsFrom_cover {lower : Option ℝ} {cuts : List ℝ}
    (hcuts : OrderedFrom lower cuts) (x : ℝ) :
    (∃ cell ∈ cellsFrom lower cuts, x ∈ cell) ↔ Above lower x := by
  induction cuts generalizing lower with
  | nil => simp [cellsFrom, openCell, Below]
  | cons c cuts ih =>
      have hdecomp :
          (∃ cell ∈ cellsFrom lower (c :: cuts), x ∈ cell) ↔
            x ∈ openCell lower (some c) ∨ x = c ∨
              ∃ cell ∈ cellsFrom (some c) cuts, x ∈ cell := by
        simp [cellsFrom]
      rw [hdecomp, ih hcuts.2]
      constructor
      · rintro (hx | rfl | hx)
        · exact hx.1
        · exact hcuts.1
        · exact above_of_lt hcuts.1 hx
      · intro hx
        rcases lt_trichotomy x c with hxc | rfl | hcx
        · exact Or.inl ⟨hx, hxc⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hcx)

/-- Splitting an interval at an interior cut is an exact three-cell partition. -/
theorem openCell_split {lower upper : Option ℝ} {c : ℝ}
    (hc : c ∈ openCell lower upper) :
    openCell lower upper =
      openCell lower (some c) ∪ {c} ∪ openCell (some c) upper := by
  ext x
  constructor
  · intro hx
    rcases lt_trichotomy x c with hxc | rfl | hcx
    · exact Or.inl (Or.inl ⟨hx.1, hxc⟩)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨hcx, hx.2⟩
  · rintro ((hx | rfl) | hx)
    · exact ⟨hx.1, below_of_lt hx.2 hc.2⟩
    · exact hc
    · exact ⟨above_of_lt hc.1 hx.1, hx.2⟩

/-- The left and middle pieces of an interval split cannot overlap. -/
theorem openCell_disjoint_point (lower : Option ℝ) (c : ℝ) :
    Disjoint (openCell lower (some c)) ({c} : Set ℝ) := by
  rw [Set.disjoint_left]
  rintro x hx rfl
  exact lt_irrefl _ hx.2

/-- The middle and right pieces of an interval split cannot overlap. -/
theorem point_disjoint_openCell (upper : Option ℝ) (c : ℝ) :
    Disjoint ({c} : Set ℝ) (openCell (some c) upper) := by
  rw [Set.disjoint_left]
  rintro x rfl hx
  exact lt_irrefl _ hx.1

/-- The two open pieces of an interval split cannot overlap. -/
theorem openCell_disjoint_openCell (lower upper : Option ℝ) (c : ℝ) :
    Disjoint (openCell lower (some c)) (openCell (some c) upper) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact lt_asymm hx.2 hy.1

/-- The ordered cells are pairwise disjoint, including singleton cells. -/
theorem cellsFrom_pairwise_disjoint {lower : Option ℝ} {cuts : List ℝ}
    (hcuts : OrderedFrom lower cuts) : (cellsFrom lower cuts).Pairwise Disjoint := by
  induction cuts generalizing lower with
  | nil => simp [cellsFrom]
  | cons c cuts ih =>
      apply List.Pairwise.cons
      · intro cell hcell
        rcases List.mem_cons.mp hcell with rfl | hcell
        · exact openCell_disjoint_point lower c
        · rw [Set.disjoint_left]
          intro x hx hy
          have hcx := (cellsFrom_cover hcuts.2 x).mp ⟨cell, hcell, hy⟩
          exact lt_asymm hx.2 hcx
      · apply List.Pairwise.cons
        · intro cell hcell
          rw [Set.disjoint_left]
          rintro x rfl hx
          have hcx := (cellsFrom_cover hcuts.2 _).mp ⟨cell, hcell, hx⟩
          exact lt_irrefl _ hcx
        · exact ih hcuts.2

/-- Every point in the lower ray belongs to exactly one cell of the decomposition. -/
theorem cellsFrom_existsUnique {lower : Option ℝ} {cuts : List ℝ}
    (hcuts : OrderedFrom lower cuts) {x : ℝ} (hx : Above lower x) :
    ∃! cell, cell ∈ cellsFrom lower cuts ∧ x ∈ cell := by
  obtain ⟨cell, hcell, hxcell⟩ := (cellsFrom_cover hcuts x).mpr hx
  refine ⟨cell, ⟨hcell, hxcell⟩, ?_⟩
  rintro other ⟨hother, hxother⟩
  by_contra hne
  have hd := (cellsFrom_pairwise_disjoint hcuts).set_pairwise hother hcell hne
  exact Set.disjoint_left.mp hd hxother hxcell

/-- One polynomial has the stated sign at every point of a cell. -/
def SignOn (p : Polynomial ℝ) (sign : SignType) (cell : Set ℝ) : Prop :=
  ∀ x ∈ cell, SignType.sign (p.eval x) = sign

/-- A row has one correct sign for each polynomial, in the given order. -/
def RowOn (polynomials : List (Polynomial ℝ)) (cell : Set ℝ)
    (row : List SignType) : Prop :=
  List.Forall₂ (fun p sign => SignOn p sign cell) polynomials row

/-- All rows correctly describe their corresponding cells, with exact dimensions. -/
def RowsOn (polynomials : List (Polynomial ℝ)) (cells : List (Set ℝ))
    (rows : List (List SignType)) : Prop :=
  List.Forall₂ (RowOn polynomials) cells rows

/-- A geometric realization records actual ordered cuts and all their row signs. -/
def RealizesFrom (lower : Option ℝ) (cuts : List ℝ)
    (polynomials : List (Polynomial ℝ)) (rows : List (List SignType)) : Prop :=
  OrderedFrom lower cuts ∧ RowsOn polynomials (cellsFrom lower cuts) rows

/-- A sign diagram is realized by some finite ordered cut list over the whole line. -/
def Realizes (polynomials : List (Polynomial ℝ)) (rows : List (List SignType)) : Prop :=
  ∃ cuts, RealizesFrom none cuts polynomials rows

/-- Reduced diagrams have exactly the roots of the nonzero input polynomials as cuts. -/
def ReducedRealizes (polynomials : List (Polynomial ℝ))
    (rows : List (List SignType)) : Prop :=
  ∃ cuts, RealizesFrom none cuts polynomials rows ∧
    ∀ x, x ∈ cuts ↔ ∃ p ∈ polynomials, p ≠ 0 ∧ p.eval x = 0

theorem RowOn.length_eq {polynomials : List (Polynomial ℝ)} {cell : Set ℝ}
    {row : List SignType} (hrow : RowOn polynomials cell row) :
    row.length = polynomials.length := (List.Forall₂.length_eq hrow).symm

theorem RealizesFrom.length_eq {lower : Option ℝ} {cuts : List ℝ}
    {polynomials : List (Polynomial ℝ)} {rows : List (List SignType)}
    (h : RealizesFrom lower cuts polynomials rows) :
    rows.length = 2 * cuts.length + 1 := by
  rw [← h.2.length_eq, cellsFrom_length]

theorem RealizesFrom.row_length {lower : Option ℝ} {cuts : List ℝ}
    {polynomials : List (Polynomial ℝ)} {rows : List (List SignType)}
    (h : RealizesFrom lower cuts polynomials rows) :
    ∀ row ∈ rows, row.length = polynomials.length := by
  have aux : ∀ {cells rows}, RowsOn polynomials cells rows →
      ∀ row ∈ rows, row.length = polynomials.length := by
    intro cells rows hrows row hmem
    induction hrows with
    | nil => cases hmem
    | @cons cell first cells rows hrow hrows ih =>
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hrow.length_eq
        · exact ih hmem
  exact aux h.2

theorem RowOn.mono {polynomials : List (Polynomial ℝ)} {cell smaller : Set ℝ}
    {row : List SignType} (h : RowOn polynomials cell row) (hsub : smaller ⊆ cell) :
    RowOn polynomials smaller row :=
  h.imp fun _ _ hp x hx => hp x (hsub hx)

theorem RowOn.union {polynomials : List (Polynomial ℝ)} {left right : Set ℝ}
    {row : List SignType} (hl : RowOn polynomials left row)
    (hr : RowOn polynomials right row) : RowOn polynomials (left ∪ right) row :=
  List.Forall₂.mp (fun _ _ hleft hright x hx => hx.elim (hleft x) (hright x)) hl hr

theorem RowOn.eq_map_at {polynomials : List (Polynomial ℝ)} {cell : Set ℝ}
    {row : List SignType} (h : RowOn polynomials cell row) {x : ℝ} (hx : x ∈ cell) :
    row = polynomials.map (fun p => SignType.sign (p.eval x)) := by
  induction h with
  | nil => rfl
  | cons hp htail ih => exact congrArg₂ List.cons (hp x hx).symm ih

theorem endpoint_mem_closure_left {lower : Option ℝ} {c : ℝ}
    (hc : Above lower c) : c ∈ closure (openCell lower (some c)) := by
  cases lower with
  | none =>
      have heq : openCell none (some c) = Iio c := by ext x; simp [openCell, Above, Below]
      rw [heq, closure_Iio]
      exact self_mem_Iic
  | some a =>
      change a < c at hc
      have heq : openCell (some a) (some c) = Ioo a c := rfl
      rw [heq, closure_Ioo hc.ne]
      exact right_mem_Icc.mpr hc.le

theorem endpoint_mem_closure_right {upper : Option ℝ} {c : ℝ}
    (hc : Below upper c) : c ∈ closure (openCell (some c) upper) := by
  cases upper with
  | none =>
      have heq : openCell (some c) none = Ioi c := by ext x; simp [openCell, Above, Below]
      rw [heq, closure_Ioi]
      exact self_mem_Ici
  | some b =>
      change c < b at hc
      have heq : openCell (some c) (some b) = Ioo c b := rfl
      rw [heq, closure_Ioo hc.ne]
      exact left_mem_Icc.mpr hc.le

/-- A polynomial nonzero at a boundary has there the constant sign of the adjacent cell. -/
theorem SignOn.at_boundary {p : Polynomial ℝ} {sign : SignType} {cell : Set ℝ}
    (h : SignOn p sign cell) {c : ℝ} (hc : c ∈ closure cell)
    (hp : p = 0 ∨ p.eval c ≠ 0) : SignType.sign (p.eval c) = sign := by
  rcases hp with rfl | hp
  · obtain ⟨x, hx⟩ := closure_nonempty_iff.mp ⟨c, hc⟩
    simpa only [Polynomial.eval_zero] using h x hx
  · have hcont : ContinuousAt (fun x : ℝ => SignType.sign (p.eval x)) c :=
      (continuousAt_sign_of_ne_zero hp).comp (f := p.eval) p.continuousAt
    exact hcont.continuousWithinAt.eq_const_of_mem_closure hc h

/-- A removable cut is not a root of any retained nonzero polynomial. -/
def RemovableAt (polynomials : List (Polynomial ℝ)) (c : ℝ) : Prop :=
  ∀ p ∈ polynomials, p = 0 ∨ p.eval c ≠ 0

theorem RowOn.at_boundary {polynomials : List (Polynomial ℝ)} {row : List SignType}
    {cell : Set ℝ} (h : RowOn polynomials cell row) {c : ℝ}
    (hc : c ∈ closure cell) (hp : RemovableAt polynomials c) :
    RowOn polynomials {c} row := by
  induction h with
  | nil => exact .nil
  | @cons p sign ps signs hhead htail ih =>
      apply List.Forall₂.cons
      · intro x hx
        have hxc : x = c := hx
        subst x
        exact hhead.at_boundary hc (hp p (List.mem_cons_self))
      · exact ih (fun p hmem => hp p (List.mem_cons_of_mem _ hmem))

/-- Removing an interior cut merges all three cells without changing any retained sign. -/
theorem RowOn.merge_openCell {lower upper : Option ℝ} {c : ℝ}
    {polynomials : List (Polynomial ℝ)} {leftRow pointRow rightRow : List SignType}
    (hc : c ∈ openCell lower upper) (hp : RemovableAt polynomials c)
    (hl : RowOn polynomials (openCell lower (some c)) leftRow)
    (hm : RowOn polynomials {c} pointRow)
    (hr : RowOn polynomials (openCell (some c) upper) rightRow) :
    RowOn polynomials (openCell lower upper) leftRow ∧
      pointRow = leftRow ∧ rightRow = leftRow := by
  have hlc := hl.at_boundary (endpoint_mem_closure_left hc.1) hp
  have hrc := hr.at_boundary (endpoint_mem_closure_right hc.2) hp
  have heqm : pointRow = leftRow :=
    (hm.eq_map_at (mem_singleton c)).trans (hlc.eq_map_at (mem_singleton c)).symm
  have heqr : rightRow = leftRow :=
    (hrc.eq_map_at (mem_singleton c)).trans (hlc.eq_map_at (mem_singleton c)).symm
  refine ⟨?_, heqm, heqr⟩
  rw [openCell_split hc]
  exact (hl.union hlc).union (heqr ▸ hr)

/-- Executable row operation deleting the first point row and following interval row. -/
def eraseFirstCutRows : List (List SignType) → List (List SignType)
  | left :: _ :: _ :: rows => left :: rows
  | rows => rows

/-- The part of a cell list after its first interval does not depend on the lower bound. -/
def followingCells : List ℝ → List (Set ℝ)
  | [] => []
  | c :: cuts => {c} :: cellsFrom (some c) cuts

theorem cellsFrom_eq (lower : Option ℝ) (cuts : List ℝ) :
    cellsFrom lower cuts = openCell lower cuts.head? :: followingCells cuts := by
  cases cuts <;> rfl

theorem OrderedFrom.erase_first {lower : Option ℝ} {c : ℝ} {cuts : List ℝ}
    (h : OrderedFrom lower (c :: cuts)) : OrderedFrom lower cuts := by
  cases cuts with
  | nil => trivial
  | cons d cuts => exact ⟨above_of_lt h.1 h.2.1, h.2.2⟩

theorem OrderedFrom.first_mem_openCell {lower : Option ℝ} {c : ℝ} {cuts : List ℝ}
    (h : OrderedFrom lower (c :: cuts)) : c ∈ openCell lower cuts.head? := by
  refine ⟨h.1, ?_⟩
  cases cuts with
  | nil => trivial
  | cons d cuts => exact h.2.1

/-- Deleting the first removable cut preserves the full ordered sign realization. -/
theorem RealizesFrom.erase_first {lower : Option ℝ} {c : ℝ} {cuts : List ℝ}
    {polynomials : List (Polynomial ℝ)} {rows : List (List SignType)}
    (h : RealizesFrom lower (c :: cuts) polynomials rows)
    (hp : RemovableAt polynomials c) :
    RealizesFrom lower cuts polynomials (eraseFirstCutRows rows) := by
  refine ⟨h.1.erase_first, ?_⟩
  have hrows := h.2
  rw [cellsFrom, cellsFrom_eq] at hrows
  cases hrows with
  | cons hl hrows =>
      cases hrows with
      | cons hm hrows =>
          cases hrows with
          | cons hr hrows =>
              rw [cellsFrom_eq]
              exact List.Forall₂.cons
                (hl.merge_openCell h.1.first_mem_openCell hp hm hr).1 hrows

/-- Executable deletion at any cut position; unchanged when the index is out of range. -/
def eraseCutRows : ℕ → List (List SignType) → List (List SignType)
  | 0, rows => eraseFirstCutRows rows
  | n + 1, left :: point :: rows => left :: point :: eraseCutRows n rows
  | _ + 1, rows => rows

/-- Deleting any selected removable cut preserves every surviving polynomial sign. -/
theorem RealizesFrom.erase_cut {lower : Option ℝ} {cuts : List ℝ}
    {polynomials : List (Polynomial ℝ)} {rows : List (List SignType)}
    (h : RealizesFrom lower cuts polynomials rows) {index : ℕ} {c : ℝ}
    (hindex : cuts[index]? = some c) (hp : RemovableAt polynomials c) :
    RealizesFrom lower (cuts.eraseIdx index) polynomials (eraseCutRows index rows) := by
  induction index generalizing lower cuts rows with
  | zero =>
      cases cuts with
      | nil => simp at hindex
      | cons d cuts =>
          have hdc : d = c := by simpa using hindex
          subst d
          exact h.erase_first hp
  | succ index ih =>
      cases cuts with
      | nil => simp at hindex
      | cons d cuts =>
          have htailIndex : cuts[index]? = some c := by simpa using hindex
          have hrows := h.2
          cases hrows with
          | cons hleft hrows =>
              cases hrows with
              | cons hpoint hrows =>
                  have htail := ih ⟨h.1.2, hrows⟩ htailIndex
                  exact ⟨⟨h.1.1, htail.1⟩,
                    List.Forall₂.cons hleft (List.Forall₂.cons hpoint htail.2)⟩

/-- Three replacement rows when a new polynomial has one interior root. -/
def rootSplitRows (row : List SignType) (leftSign rightSign : SignType) :
    List (List SignType) := [leftSign :: row, SignType.zero :: row, rightSign :: row]

/-- A positive derivative and opposite endpoint signs construct the three new
rows, while retaining every old polynomial's sign in all three new cells. -/
theorem exists_increasing_root_rows (p : Polynomial ℝ)
    {polynomials : List (Polynomial ℝ)} {row : List SignType} {a b : ℝ}
    (hab : a < b) (hd : ∀ x ∈ Ioo a b, 0 < p.derivative.eval x)
    (ha : p.eval a < 0) (hb : 0 < p.eval b)
    (hrow : RowOn polynomials (Ioo a b) row) :
    ∃ c ∈ Ioo a b,
      RowsOn (p :: polynomials) [Ioo a c, {c}, Ioo c b]
        (rootSplitRows row .neg .pos) := by
  obtain ⟨c, hc, hz, hsigns⟩ :=
    RealSignCell.polynomial_exists_increasing_root_split p hab hd ha hb
  refine ⟨c, hc, List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ List.Forall₂.nil))⟩
  · apply List.Forall₂.cons
    · intro x hx
      apply sign_eq_neg_one_iff.mpr
      exact ((hsigns x ⟨hx.1.le, (lt_trans hx.2 hc.2).le⟩).1).mpr hx.2
    · exact hrow.mono (fun x hx => ⟨hx.1, lt_trans hx.2 hc.2⟩)
  · apply List.Forall₂.cons
    · intro x hx
      have hxc : x = c := hx
      subst x
      exact sign_eq_zero_iff.mpr hz
    · exact hrow.mono (fun x hx => (show x = c from hx) ▸ hc)
  · apply List.Forall₂.cons
    · intro x hx
      apply sign_eq_one_iff.mpr
      exact ((hsigns x ⟨(lt_trans hc.1 hx.1).le, hx.2.le⟩).2.2).mpr hx.1
    · exact hrow.mono (fun x hx => ⟨lt_trans hc.1 hx.1, hx.2⟩)

/-- The decreasing version inserts the positive/zero/negative sign rows. -/
theorem exists_decreasing_root_rows (p : Polynomial ℝ)
    {polynomials : List (Polynomial ℝ)} {row : List SignType} {a b : ℝ}
    (hab : a < b) (hd : ∀ x ∈ Ioo a b, p.derivative.eval x < 0)
    (ha : 0 < p.eval a) (hb : p.eval b < 0)
    (hrow : RowOn polynomials (Ioo a b) row) :
    ∃ c ∈ Ioo a b,
      RowsOn (p :: polynomials) [Ioo a c, {c}, Ioo c b]
        (rootSplitRows row .pos .neg) := by
  obtain ⟨c, hc, hz, hsigns⟩ :=
    RealSignCell.polynomial_exists_decreasing_root_split p hab hd ha hb
  refine ⟨c, hc, List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ List.Forall₂.nil))⟩
  · apply List.Forall₂.cons
    · intro x hx
      apply sign_eq_one_iff.mpr
      exact ((hsigns x ⟨hx.1.le, (lt_trans hx.2 hc.2).le⟩).2.2).mpr hx.2
    · exact hrow.mono (fun x hx => ⟨hx.1, lt_trans hx.2 hc.2⟩)
  · apply List.Forall₂.cons
    · intro x hx
      have hxc : x = c := hx
      subst x
      exact sign_eq_zero_iff.mpr hz
    · exact hrow.mono (fun x hx => (show x = c from hx) ▸ hc)
  · apply List.Forall₂.cons
    · intro x hx
      apply sign_eq_neg_one_iff.mpr
      exact ((hsigns x ⟨(lt_trans hc.1 hx.1).le, hx.2.le⟩).1).mpr hx.1
    · exact hrow.mono (fun x hx => ⟨lt_trans hc.1 hx.1, hx.2⟩)

/-- The empty polynomial family has one whole-line cell and one empty row. -/
theorem reducedRealizes_empty : ReducedRealizes [] [[]] := by
  refine ⟨[], ⟨trivial, List.Forall₂.cons List.Forall₂.nil List.Forall₂.nil⟩, ?_⟩
  simp

end MathUE.OrderedRealSignDiagram
