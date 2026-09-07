import MathUE.Polynomial.RemainderCutSignInference
import MathUE.Polynomial.GlobalSignReconstruction
import Mathlib.Data.List.Sort

/-!
# Reconstruct sign diagrams from pseudo-remainders

Remainder signs label the selected polynomial at retained divisor roots.
Tagged condensation preserves those labels in geometric cut order. The executable
reconstruction then inserts the selected polynomial's roots and removes
auxiliary cuts; its correctness includes the exact reduced root-cut invariant.
-/

namespace MathUE.OrderedRealSignDiagram

theorem OrderedFrom.pairwise {lower : Option ℝ} {cuts : List ℝ}
    (h : OrderedFrom lower cuts) : cuts.Pairwise (· < ·) := by
  induction cuts generalizing lower with
  | nil => exact .nil
  | cons c cuts ih =>
      exact .cons (fun _ hx => h.2.above_of_mem hx) (ih h.2)

theorem RowsOn.pointEntries {lower : Option ℝ} {cuts : List ℝ}
    {polynomials : List (Polynomial ℝ)} {rows : List (List SignType)}
    (h : RowsOn polynomials (cellsFrom lower cuts) rows) :
    List.Forall₂ (fun c row => RowOn polynomials {c} row) cuts (pointEntries rows) := by
  induction cuts generalizing lower rows with
  | nil =>
      cases h with
      | cons _ ht => cases ht; exact .nil
  | cons c cuts ih =>
      cases h with
      | cons _ ht =>
          cases ht with
          | cons hp ht => exact .cons hp (ih ht)

theorem pointEntries_map (f : α → β) (rows : List α) :
    pointEntries (rows.map f) = (pointEntries rows).map f := by
  induction rows using pointEntries.induct with
  | case1 left point rest ih => simp only [List.map_cons, pointEntries, ih]
  | case2 rows h =>
      cases rows with
      | nil => rfl
      | cons left rest =>
          cases rest with
          | nil => rfl
          | cons point tail => exact False.elim (h left point tail rfl)

/-- A point annotation is required to be correct only when a divisor vanishes. -/
def CorrectRootAnnotation (p : Polynomial ℝ) (divisors : List (Polynomial ℝ))
    (c : ℝ) (entry : List SignType × Option SignType) : Prop :=
  RowOn divisors {c} entry.1 ∧
    (0 ∈ entry.1 → entry.2 = some (SignType.sign (p.eval c)))

theorem filter_correctRootAnnotations {p : Polynomial ℝ}
    {divisors : List (Polynomial ℝ)} {cuts : List ℝ}
    {entries : List (List SignType × Option SignType)}
    (keep : ℝ → Bool)
    (hkeep : ∀ c ∈ cuts, keep c = true ↔ ∃ d ∈ divisors, d.eval c = 0)
    (h : List.Forall₂ (CorrectRootAnnotation p divisors) cuts entries) :
    List.Forall₂ (fun c entry => entry.2 = some (SignType.sign (p.eval c)))
      (cuts.filter keep) (entries.filter (fun entry => decide (0 ∈ entry.1))) := by
  induction h with
  | nil => exact .nil
  | @cons c entry cuts entries hc ht ih =>
      have iht := ih (fun d hd => hkeep d (List.mem_cons_of_mem _ hd))
      by_cases hz : 0 ∈ entry.1
      · have hr := (hkeep c List.mem_cons_self).mpr (hc.1.contains_zero_iff.mp hz)
        simp only [List.filter_cons, hr, hz, decide_true, ite_true]
        exact .cons (hc.2 hz) iht
      · have hr : keep c = false := Bool.eq_false_iff.mpr fun hr =>
          hz (hc.1.contains_zero_iff.mpr ((hkeep c List.mem_cons_self).mp hr))
        simpa only [List.filter_cons, hr, hz, decide_false,
          Bool.false_eq_true, ite_false] using iht

/-- Tagged condensation preserves point annotations in the actual retained cut order. -/
theorem condense_correctRootAnnotations {p : Polynomial ℝ}
    {divisors : List (Polynomial ℝ)} {lower : Option ℝ} {cuts : List ℝ}
    {rows : List (List SignType × Option SignType)}
    (h : RealizesFrom lower cuts divisors (rows.map Prod.fst))
    (hannotations : List.Forall₂ (CorrectRootAnnotation p divisors)
      cuts (pointEntries rows)) :
    ∃ newCuts, RealizesFrom lower newCuts divisors
        ((condenseTaggedRows rows).map Prod.fst) ∧
      (∀ x, x ∈ newCuts ↔ x ∈ cuts ∧ ∃ d ∈ divisors, d.eval x = 0) ∧
      (pointEntries (condenseTaggedRows rows)).map Prod.snd =
        newCuts.map (fun c => some (SignType.sign (p.eval c))) := by
  classical
  obtain ⟨newCuts, hnew, hmem⟩ := h.condense
  refine ⟨newCuts, ?_, hmem, ?_⟩
  · simpa only [map_fst_condenseTaggedRows] using hnew
  · let keep : ℝ → Bool := fun c => decide (∃ d ∈ divisors, d.eval c = 0)
    have heq : newCuts = cuts.filter keep :=
      hnew.1.pairwise.eq_of_mem_iff (h.1.pairwise.filter keep) (by
        intro x
        simpa only [List.mem_filter, keep, decide_eq_true_eq] using hmem x)
    have hpairs := filter_correctRootAnnotations keep
      (fun _ _ => by simp only [keep, decide_eq_true_eq]) hannotations
    rw [pointPayloads_condenseTaggedRows, heq]
    have hmaps : ∀ {cs : List ℝ} {es : List (List SignType × Option SignType)},
        List.Forall₂ (fun c entry => entry.2 = some (SignType.sign (p.eval c))) cs es →
          es.map Prod.snd = cs.map (fun c => some (SignType.sign (p.eval c))) := by
      intro cs es hcs
      induction hcs with
      | nil => rfl
      | cons hp _ ih => exact congrArg₂ List.cons hp ih
    exact hmaps hpairs

/-- Project divisor columns and infer the selected polynomial's sign from the
aligned remainder suffix. Interval annotations may be absent and are ignored. -/
def inferAndProjectRows (divisorCount : ℕ) (rows : List (List SignType)) :
    List (List SignType × Option SignType) :=
  rows.map (fun row =>
    (row.take divisorCount, inferRootSign (row.take divisorCount) (row.drop divisorCount)))

theorem RowOn.drop_columns {divisors remainders : List (Polynomial ℝ)}
    {cell : Set ℝ} {row : List SignType}
    (h : RowOn (divisors ++ remainders) cell row) :
    RowOn remainders cell (row.drop divisors.length) := by
  simpa only [List.drop_left, RowOn] using List.forall₂_drop divisors.length h

theorem inferAndProjectRows_annotations {p : Polynomial ℝ}
    {divisors remainders : List (Polynomial ℝ)} {lower : Option ℝ} {cuts : List ℝ}
    {rows : List (List SignType)}
    (hpaired : AlignedRootSigns p divisors remainders)
    (hrows : RowsOn (divisors ++ remainders) (cellsFrom lower cuts) rows) :
    List.Forall₂ (CorrectRootAnnotation p divisors) cuts
      (pointEntries (inferAndProjectRows divisors.length rows)) := by
  rw [inferAndProjectRows, pointEntries_map]
  apply List.forall₂_map_right_iff.mpr
  apply hrows.pointEntries.imp
  intro c row hrow
  refine ⟨hrow.take_columns, ?_⟩
  intro hz
  exact (inferRootSign_point_rows hpaired hrow.take_columns hrow.drop_columns).mpr
    (hrow.take_columns.contains_zero_iff.mp hz)

/-- The actual projection/inference/condensation pipeline prepares a reduced divisor
diagram and computes all required selected-polynomial boundary signs. -/
theorem prepare_reconstruction {p : Polynomial ℝ}
    {divisors remainders : List (Polynomial ℝ)} {rows : List (List SignType)}
    (hpaired : AlignedRootSigns p divisors remainders)
    (h : ReducedRealizes (divisors ++ remainders) rows)
    (hn : ∀ d ∈ divisors, d ≠ 0) :
    ∃ cuts, RealizesFrom none cuts divisors
        ((condenseTaggedRows (inferAndProjectRows divisors.length rows)).map Prod.fst) ∧
      (∀ x, x ∈ cuts ↔ ∃ d ∈ divisors, d ≠ 0 ∧ d.eval x = 0) ∧
      (pointEntries (condenseTaggedRows (inferAndProjectRows divisors.length rows))).map
        Prod.snd = cuts.map (fun c => some (SignType.sign (p.eval c))) := by
  obtain ⟨oldCuts, hrealizes, hroots⟩ := h
  have hproject : RealizesFrom none oldCuts divisors
      ((inferAndProjectRows divisors.length rows).map Prod.fst) := by
    refine ⟨hrealizes.1, ?_⟩
    simpa only [inferAndProjectRows, List.map_map, Function.comp_def] using
      hrealizes.2.take_columns
  obtain ⟨cuts, hnew, hmem, hlabels⟩ := condense_correctRootAnnotations hproject
    (inferAndProjectRows_annotations hpaired hrealizes.2)
  refine ⟨cuts, hnew, ?_, hlabels⟩
  intro x
  rw [hmem]
  constructor
  · rintro ⟨_, d, hd, hz⟩
    exact ⟨d, hd, hn d hd, hz⟩
  · rintro ⟨d, hd, _, hz⟩
    exact ⟨(hroots x).mpr ⟨d, List.mem_append_left _ hd, hn d hd, hz⟩, d, hd, hz⟩

/-- Complete row reconstruction from a derivative/retained/remainder diagram.
The default sign is used only on malformed inputs; correctness proves every
retained point annotation is present. No real data occurs in this algorithm. -/
def reconstructFromRemainderRows (divisorCount : ℕ) (rows : List (List SignType)) :
    List (List SignType) :=
  let prepared := condenseTaggedRows (inferAndProjectRows divisorCount rows)
  condenseRows (reconstructRows none
    ((pointEntries prepared).map (fun entry => entry.2.getD 0)) (prepared.map Prod.fst))

/-- The actual executable inference/condensation/traversal pipeline reconstructs
the selected polynomial and all retained columns, with the exact root-cut invariant. -/
theorem reconstructFromRemainderRows_correct {p : Polynomial ℝ}
    {polynomials remainders : List (Polynomial ℝ)} {rows : List (List SignType)}
    (hpaired : AlignedRootSigns p (p.derivative :: polynomials) remainders)
    (h : ReducedRealizes ((p.derivative :: polynomials) ++ remainders) rows)
    (hdegree : 0 < p.natDegree) (hn : ∀ q ∈ polynomials, q ≠ 0) :
    ReducedRealizes (p :: polynomials)
      (reconstructFromRemainderRows (polynomials.length + 1) rows) := by
  have hdivisors : ∀ d ∈ p.derivative :: polynomials, d ≠ 0 := by
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Polynomial.derivative_ne_zero.mpr hdegree.ne'
    · exact hn d hd
  obtain ⟨cuts, hrealizes, hroots, hlabels⟩ := prepare_reconstruction hpaired h hdivisors
  have hsigns := congrArg (List.map (fun s : Option SignType => s.getD 0)) hlabels
  simp only [List.map_map, Function.comp_def, Option.getD_some] at hsigns
  unfold reconstructFromRemainderRows
  dsimp only
  rw [← List.length_cons (a := p.derivative), hsigns]
  exact reconstruct_reduced hrealizes hroots hdegree hn

section DensePseudoRemainders

open Math.DensePolynomial

variable {A : Type*} [Zero A] [One A] [Add A] [Neg A] [Mul A]

/-- Literal dense pseudo-remainders discharge the reconstruction sign identities.
All coefficient operations may be raw syntax; only their real evaluator obeys ring laws. -/
theorem reconstructFromPseudoRemainderRows_correct (e : Evaluator A ℝ)
    (selected : Math.DensePolynomial A) (retained : List (Math.DensePolynomial A))
    (hdegree : 1 < selected.length) (hselected : e (leadingCoeff selected) ≠ 0)
    (hleading : ∀ d ∈ derivative selected :: retained, e (leadingCoeff d) ≠ 0)
    {rows : List (List SignType)}
    (h : ReducedRealizes
      (((derivative selected :: retained).map (toPolynomial e)) ++
        ((derivative selected :: retained).map
          (fun d => toPolynomial e (pseudoDivide selected d).remainder))) rows) :
    ReducedRealizes (toPolynomial e selected :: retained.map (toPolynomial e))
      (reconstructFromRemainderRows (retained.length + 1) rows) := by
  have hd : 0 < (toPolynomial e selected).natDegree := by
    rw [toPolynomial_natDegree_eq e selected hselected]
    omega
  have hn : ∀ q ∈ retained.map (toPolynomial e), q ≠ 0 := by
    intro q hq
    obtain ⟨d, hdmem, rfl⟩ := List.mem_map.mp hq
    intro hz
    have hc := toPolynomial_coeff_length_sub_one e d
    rw [hz, Polynomial.coeff_zero] at hc
    exact hleading d (List.mem_cons_of_mem _ hdmem) hc.symm
  have hpaired := alignedRootSigns_pseudoRemainders e selected
    (derivative selected :: retained) hleading
  simp only [List.map_cons, toPolynomial_derivative, List.map_map,
    Function.comp_def] at hpaired h
  simpa only [List.length_map] using
    reconstructFromRemainderRows_correct hpaired h hd hn

end DensePseudoRemainders

end MathUE.OrderedRealSignDiagram
