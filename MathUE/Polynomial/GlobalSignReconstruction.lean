import MathUE.Polynomial.LocalSignReconstruction
import MathUE.Polynomial.SignDiagramCondensation

/-!
# Traversing local root insertions

This executable traversal consumes derivative-first sign rows and the selected
polynomial's signs at old cuts. Its geometric theorem identifies every new cut.
-/

namespace MathUE.OrderedRealSignDiagram

open Set

/-- Insert a polynomial column, using the derivative as the first input column.
Point signs are consumed in cut order; malformed inputs return an empty list. -/
def reconstructRows (left : Option SignType) :
    List SignType → List (List SignType) → List (List SignType)
  | [], [direction :: row] => reconstructCellRows direction left none row
  | pointSign :: signs, (direction :: row) :: (_ :: point) :: rest =>
      reconstructCellRows direction left (some pointSign) row ++
        (pointSign :: point) :: reconstructRows (some pointSign) signs rest
  | _, _ => []

theorem cellsFrom_insert_local (lower : Option ℝ) (c : ℝ) (cuts : List ℝ)
    (root : Option ℝ) :
    cellsFrom lower (root.toList ++ c :: cuts) =
      localCells lower (some c) root ++ {c} :: cellsFrom (some c) cuts := by
  cases root <;> rfl

theorem orderedFrom_insert_local {lower : Option ℝ} {c : ℝ} {cuts : List ℝ}
    {root : Option ℝ} (hc : Above lower c) (htail : OrderedFrom (some c) cuts)
    (hroot : ∀ r, root = some r → r ∈ openCell lower (some c)) :
    OrderedFrom lower (root.toList ++ c :: cuts) := by
  cases root with
  | none => exact ⟨hc, htail⟩
  | some r => exact ⟨(hroot r rfl).1, (hroot r rfl).2, htail⟩

/-- Glue one reconstructed interval to its right cut and an already reconstructed tail. -/
theorem LocalRealizes.prepend {p : Polynomial ℝ} {polynomials : List (Polynomial ℝ)}
    {lower : Option ℝ} {c : ℝ} {cuts : List ℝ}
    {localRows tailRows : List (List SignType)} {pointRow : List SignType}
    (hl : LocalRealizes p polynomials lower (some c) localRows)
    (hc : Above lower c) (hp : RowOn (p :: polynomials) {c} pointRow)
    (ht : RealizesFrom (some c) cuts (p :: polynomials) tailRows) :
    ∃ newCuts, RealizesFrom lower newCuts (p :: polynomials)
        (localRows ++ pointRow :: tailRows) ∧
      ∀ x, x ∈ newCuts ↔ x = c ∨ x ∈ cuts ∨
        x ∈ openCell lower (some c) ∧ p.eval x = 0 := by
  obtain ⟨root, hroot, hzero, hrows⟩ := hl
  refine ⟨root.toList ++ c :: cuts, ?_, ?_⟩
  · refine ⟨orderedFrom_insert_local hc ht.1 hroot, ?_⟩
    rw [cellsFrom_insert_local]
    exact List.rel_append hrows (List.Forall₂.cons hp ht.2)
  · intro x
    simp only [List.mem_append, List.mem_cons, Option.mem_toList]
    constructor
    · rintro (hx | hx | hx)
      · exact Or.inr (Or.inr ⟨hroot x hx, (hzero x (hroot x hx)).mpr hx⟩)
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
    · rintro (hx | hx | ⟨hx, hz⟩)
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
      · exact Or.inl ((hzero x hx).mp hz)

/-- The last local interval is already a complete realization of its lower ray. -/
theorem LocalRealizes.last {p : Polynomial ℝ} {polynomials : List (Polynomial ℝ)}
    {lower : Option ℝ} {rows : List (List SignType)}
    (hl : LocalRealizes p polynomials lower none rows) :
    ∃ cuts, RealizesFrom lower cuts (p :: polynomials) rows ∧
      ∀ x, x ∈ cuts ↔ Above lower x ∧ p.eval x = 0 := by
  obtain ⟨root, hroot, hzero, hrows⟩ := hl
  refine ⟨root.toList, ?_, ?_⟩
  · cases root with
    | none => exact ⟨trivial, hrows⟩
    | some c => exact ⟨⟨(hroot c rfl).1, trivial⟩, hrows⟩
  · intro x
    rw [Option.mem_toList]
    constructor
    · intro hx
      exact ⟨(hroot x hx).1, (hzero x (hroot x hx)).mpr hx⟩
    · rintro ⟨hx, hz⟩
      exact (hzero x ⟨hx, trivial⟩).mp hz

/-- Reconstruct a complete lower-ray diagram. The derivative-root coverage hypothesis
will be supplied by the reduced recursive diagram, not by a numerical root oracle. -/
theorem RealizesFrom.reconstruct {p : Polynomial ℝ}
    {polynomials : List (Polynomial ℝ)} {lower : Option ℝ} {cuts : List ℝ}
    {rows : List (List SignType)}
    (h : RealizesFrom lower cuts (p.derivative :: polynomials) rows)
    (hderivative : ∀ x, Above lower x → p.derivative.eval x = 0 → x ∈ cuts) :
    ∃ newCuts, RealizesFrom lower newCuts (p :: polynomials)
        (reconstructRows (lower.map (fun x => SignType.sign (p.eval x)))
          (cuts.map (fun x => SignType.sign (p.eval x))) rows) ∧
      ∀ x, x ∈ newCuts ↔ x ∈ cuts ∨ Above lower x ∧ p.eval x = 0 := by
  induction cuts generalizing lower rows with
  | nil =>
      have hrows := h.2
      cases hrows with
      | cons hrow hrest =>
          cases hrest
          cases hrow with
          | @cons _ direction _ row hd hr =>
              have hn : direction ≠ 0 := by
                intro hz
                obtain ⟨x, hx⟩ := openCell_right_nonempty lower
                have := hderivative x hx.1 (sign_eq_zero_iff.mp ((hd x hx).trans hz))
                exact List.not_mem_nil this
              obtain ⟨newCuts, hnew, hmem⟩ :=
                (reconstruct_cell p (openCell_right_nonempty lower) hn hd hr).last
              exact ⟨newCuts, hnew, by simpa using hmem⟩
  | cons c cuts ih =>
      have hrows := h.2
      cases hrows with
      | cons hrow hrest =>
          cases hrest with
          | @cons _ pointRow _ tail hpoint htail =>
              cases hrow with
              | @cons _ direction _ row hd hr =>
                  cases hpoint with
                  | @cons _ pointDirection _ point _ hp =>
                      have htailDerivative : ∀ x, Above (some c) x →
                          p.derivative.eval x = 0 → x ∈ cuts := by
                        intro x hx hz
                        rcases List.mem_cons.mp
                          (hderivative x (above_of_lt h.1.1 hx) hz) with hxc | hxc
                        · exact False.elim (lt_irrefl c (hxc ▸ hx))
                        · exact hxc
                      obtain ⟨tailCuts, htailRealizes, htailMem⟩ :=
                        ih ⟨h.1.2, htail⟩ htailDerivative
                      have hn : direction ≠ 0 := by
                        intro hz
                        obtain ⟨x, hx⟩ := openCell_left_nonempty h.1.1
                        have hzero := sign_eq_zero_iff.mp ((hd x hx).trans hz)
                        exact not_mem_cuts_of_mem_openCell h.1 List.mem_cons_self hx
                          (hderivative x hx.1 hzero)
                      have hlocal := reconstruct_cell p (openCell_left_nonempty h.1.1)
                        hn hd hr
                      have hpointNew : RowOn (p :: polynomials) {c}
                          (SignType.sign (p.eval c) :: point) := by
                        apply List.Forall₂.cons _ hp
                        intro x hx
                        exact congrArg (fun y => SignType.sign (p.eval y)) hx
                      obtain ⟨newCuts, hnew, hmem⟩ :=
                        hlocal.prepend h.1.1 hpointNew htailRealizes
                      refine ⟨newCuts, hnew, ?_⟩
                      intro x
                      rw [hmem, htailMem]
                      simp only [List.mem_cons]
                      constructor
                      · rintro (hx | (hx | ⟨hx, hz⟩) | ⟨hx, hz⟩)
                        · exact Or.inl (Or.inl hx)
                        · exact Or.inl (Or.inr hx)
                        · exact Or.inr ⟨above_of_lt h.1.1 hx, hz⟩
                        · exact Or.inr ⟨hx.1, hz⟩
                      · rintro ((hx | hx) | ⟨hx, hz⟩)
                        · exact Or.inl hx
                        · exact Or.inr (Or.inl (Or.inl hx))
                        · rcases lt_trichotomy x c with hxc | hxc | hcx
                          · exact Or.inr (Or.inr ⟨⟨hx, hxc⟩, hz⟩)
                          · exact Or.inl hxc
                          · exact Or.inr (Or.inl (Or.inr ⟨hcx, hz⟩))

/-- The global traversal followed by condensation has exactly the selected and
retained polynomial roots as cuts. Derivative-root coverage is derived here. -/
theorem reconstruct_reduced {p : Polynomial ℝ} {polynomials : List (Polynomial ℝ)}
    {cuts : List ℝ} {rows : List (List SignType)}
    (h : RealizesFrom none cuts (p.derivative :: polynomials) rows)
    (hroots : ∀ x, x ∈ cuts ↔
      ∃ q ∈ p.derivative :: polynomials, q ≠ 0 ∧ q.eval x = 0)
    (hdegree : 0 < p.natDegree) (hn : ∀ q ∈ polynomials, q ≠ 0) :
    ReducedRealizes (p :: polynomials)
      (condenseRows (reconstructRows none
        (cuts.map (fun x => SignType.sign (p.eval x))) rows)) := by
  have hp : p ≠ 0 := by
    intro hz
    simp only [hz, Polynomial.natDegree_zero] at hdegree
    omega
  have hd : p.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hdegree.ne'
  obtain ⟨newCuts, hnew, hmem⟩ := h.reconstruct (fun x _ hz =>
    (hroots x).mpr ⟨p.derivative, List.mem_cons_self, hd, hz⟩)
  apply hnew.condense_reduced
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact hn q hq
  · intro q hq x hz
    apply (hmem x).mpr
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr ⟨trivial, hz⟩
    · exact Or.inl ((hroots x).mpr
        ⟨q, List.mem_cons_of_mem _ hq, hn q hq, hz⟩)

end MathUE.OrderedRealSignDiagram
