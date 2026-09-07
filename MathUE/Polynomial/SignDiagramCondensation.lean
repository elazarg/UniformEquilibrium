import MathUE.Polynomial.OrderedRealSignDiagram
import MathUE.Polynomial.TaggedRowCondensation

/-!
# Removing auxiliary-only cuts from real sign diagrams

The executable pass retains exactly the point rows containing a zero sign.
Its geometric correctness uses continuity to merge adjacent open cells.
-/

namespace MathUE.OrderedRealSignDiagram

/-- Delete point rows with no zero entry and merge their adjacent interval rows. -/
def condenseRows : List (List SignType) → List (List SignType)
  | left :: point :: rest =>
      let tail := condenseRows rest
      if 0 ∈ point then left :: point :: tail else left :: tail.drop 1
  | rows => rows

theorem RowOn.contains_zero_iff {polynomials : List (Polynomial ℝ)}
    {point : List SignType} {c : ℝ} (h : RowOn polynomials {c} point) :
    0 ∈ point ↔ ∃ p ∈ polynomials, p.eval c = 0 := by
  rw [h.eq_map_at (Set.mem_singleton c)]
  simp [List.mem_map, sign_eq_zero_iff]

theorem RowOn.removable_of_no_zero {polynomials : List (Polynomial ℝ)}
    {point : List SignType} {c : ℝ} (h : RowOn polynomials {c} point)
    (hn : ¬ 0 ∈ point) : RemovableAt polynomials c := by
  intro p hp
  exact Or.inr fun hz => hn (h.contains_zero_iff.mpr ⟨p, hp, hz⟩)

/-- Condensation preserves signs and retains exactly the original cuts that are
roots of a retained polynomial. No nonzero-polynomial hypothesis is needed here. -/
theorem RealizesFrom.condense {lower : Option ℝ} {cuts : List ℝ}
    {polynomials : List (Polynomial ℝ)} {rows : List (List SignType)}
    (h : RealizesFrom lower cuts polynomials rows) :
    ∃ newCuts, RealizesFrom lower newCuts polynomials (condenseRows rows) ∧
      ∀ x, x ∈ newCuts ↔ x ∈ cuts ∧ ∃ p ∈ polynomials, p.eval x = 0 := by
  induction cuts generalizing lower rows with
  | nil =>
      have hrows := h.2
      cases hrows with
      | cons hrow hrest =>
          cases hrest
          exact ⟨[], h, by simp⟩
  | cons c cuts ih =>
      have hrows := h.2
      cases hrows with
      | @cons _ left _ rest hleft hrest =>
          cases hrest with
          | @cons _ point _ tail hpoint htail =>
              obtain ⟨newCuts, hnew, hmem⟩ := ih ⟨h.1.2, htail⟩
              have haug : RealizesFrom lower (c :: newCuts) polynomials
                  (left :: point :: condenseRows tail) :=
                ⟨⟨h.1.1, hnew.1⟩,
                  List.Forall₂.cons hleft (List.Forall₂.cons hpoint hnew.2)⟩
              by_cases hz : 0 ∈ point
              · refine ⟨c :: newCuts, ?_, ?_⟩
                · simpa only [condenseRows, if_pos hz] using haug
                · intro x
                  have hroot := hpoint.contains_zero_iff.mp hz
                  simp only [List.mem_cons, hmem]
                  constructor
                  · rintro (rfl | ⟨hx, hp⟩)
                    · exact ⟨Or.inl rfl, hroot⟩
                    · exact ⟨Or.inr hx, hp⟩
                  · rintro ⟨rfl | hx, hp⟩
                    · exact Or.inl rfl
                    · exact Or.inr ⟨hx, hp⟩
              · refine ⟨newCuts, ?_, ?_⟩
                · have herase := haug.erase_first (hpoint.removable_of_no_zero hz)
                  have hlength := hnew.length_eq
                  cases heq : condenseRows tail with
                  | nil => simp only [heq, List.length_nil] at hlength; omega
                  | cons first rest =>
                      simpa only [condenseRows, if_neg hz, heq, List.drop_succ_cons,
                        List.drop_zero, eraseFirstCutRows] using herase
                · intro x
                  rw [hmem]
                  constructor
                  · rintro ⟨hx, hp⟩
                    exact ⟨List.mem_cons_of_mem _ hx, hp⟩
                  · rintro ⟨hx, hp⟩
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact False.elim (hz (hpoint.contains_zero_iff.mpr hp))
                    · exact ⟨hx, hp⟩

/-- If all retained polynomials are nonzero and their roots were already cuts,
condensation produces the exact reduced root-cut invariant. -/
theorem RealizesFrom.condense_reduced {cuts : List ℝ}
    {polynomials : List (Polynomial ℝ)} {rows : List (List SignType)}
    (h : RealizesFrom none cuts polynomials rows)
    (hn : ∀ p ∈ polynomials, p ≠ 0)
    (hcover : ∀ p ∈ polynomials, ∀ x, p.eval x = 0 → x ∈ cuts) :
    ReducedRealizes polynomials (condenseRows rows) := by
  obtain ⟨newCuts, hnew, hmem⟩ := h.condense
  refine ⟨newCuts, hnew, ?_⟩
  intro x
  rw [hmem]
  constructor
  · rintro ⟨_, p, hp, hz⟩
    exact ⟨p, hp, hn p hp, hz⟩
  · rintro ⟨p, hp, _, hz⟩
    exact ⟨hcover p hp x hz, p, hp, hz⟩

/-- Restrict a row to an initial subfamily, preserving its original column order. -/
theorem RowOn.take_columns {retained auxiliary : List (Polynomial ℝ)}
    {cell : Set ℝ} {row : List SignType}
    (h : RowOn (retained ++ auxiliary) cell row) :
    RowOn retained cell (row.take retained.length) := by
  simpa only [List.take_left, RowOn] using List.forall₂_take retained.length h

theorem RowsOn.take_columns {retained auxiliary : List (Polynomial ℝ)}
    {cells : List (Set ℝ)} {rows : List (List SignType)}
    (h : RowsOn (retained ++ auxiliary) cells rows) :
    RowsOn retained cells (rows.map (fun row => row.take retained.length)) := by
  exact List.forall₂_map_right_iff.mpr (h.imp fun _ _ hp => hp.take_columns)

/-- Project away an auxiliary suffix and discard exactly the auxiliary-only cuts. -/
theorem ReducedRealizes.project_and_condense
    {retained auxiliary : List (Polynomial ℝ)} {rows : List (List SignType)}
    (h : ReducedRealizes (retained ++ auxiliary) rows)
    (hn : ∀ p ∈ retained, p ≠ 0) :
    ReducedRealizes retained
      (condenseRows (rows.map (fun row => row.take retained.length))) := by
  obtain ⟨cuts, hrealizes, hroots⟩ := h
  apply RealizesFrom.condense_reduced ⟨hrealizes.1, hrealizes.2.take_columns⟩ hn
  intro p hp x hz
  exact (hroots x).mpr ⟨p, List.mem_append_left _ hp, hn p hp, hz⟩

/-- Forgetting payloads commutes exactly with alternating-row condensation. -/
theorem map_fst_condenseTaggedRows :
    ∀ rows : List (List SignType × α),
      (condenseTaggedRows rows).map Prod.fst = condenseRows (rows.map Prod.fst)
  | [] => rfl
  | [left] => rfl
  | left :: point :: rest => by
      rw [condenseTaggedRows]
      by_cases hzero : 0 ∈ point.1
      · simp only [if_pos hzero, List.map_cons]
        rw [map_fst_condenseTaggedRows rest]
        change _ = if 0 ∈ point.1 then _ else _
        rw [if_pos hzero]
      · simp only [if_neg hzero, List.map_cons, List.map_drop]
        rw [map_fst_condenseTaggedRows rest]
        change _ = if 0 ∈ point.1 then _ else _
        rw [if_neg hzero]

end MathUE.OrderedRealSignDiagram
