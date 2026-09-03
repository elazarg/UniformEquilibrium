/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.CopositiveQCorollaries

/-!
# Four-vertex integral tournament selection

A four-vertex integral tournament with no sink contains a directed triangle
and a fourth vertex which beats two cyclically consecutive vertices of that
triangle.  The result is recorded by a relabelling, so downstream constructions
can use literal edge equalities without repeating finite tournament casework.
-/

noncomputable section

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι]

/-- A relabelling of a four-vertex tournament in which vertices `0,1,2` form
the directed cycle `1 → 0 → 2 → 1`, while the outsider `3` beats `0` and `1`.
-/
structure FinFourIntegralTournamentCycleOutsider (A : ι → ι → ℝ) where
  relabel : Fin 4 ≃ ι
  one_beats_zero : A (relabel 1) (relabel 0) = 1
  two_beats_one : A (relabel 2) (relabel 1) = 1
  zero_beats_two : A (relabel 0) (relabel 2) = 1
  outsider_beats_zero : A (relabel 3) (relabel 0) = 1
  outsider_beats_one : A (relabel 3) (relabel 1) = 1

private def finFourBoolTournamentEdge
    (edge01 edge02 edge03 edge12 edge13 edge23 : Bool) :
    Fin 4 → Fin 4 → Bool :=
  ![![false, edge01, edge02, edge03],
    ![!edge01, false, edge12, edge13],
    ![!edge02, !edge12, false, edge23],
    ![!edge03, !edge13, !edge23, false]]

/-- One checked relabelling table for the sixty-four orientations on four
labelled vertices.  Values on orientations with a sink are immaterial. -/
private def finFourBoolTournamentRelabel
    (edge01 edge02 edge03 edge12 edge13 edge23 : Bool) : Fin 4 → Fin 4 :=
  match edge01, edge02, edge03, edge12, edge13, edge23 with
  | false, false, false, false, false, false => ![0, 1, 2, 3]
  | false, false, false, false, false, true => ![0, 1, 2, 3]
  | false, false, false, false, true, false => ![0, 1, 2, 3]
  | false, false, false, false, true, true => ![0, 1, 2, 3]
  | false, false, false, true, false, false => ![0, 1, 2, 3]
  | false, false, false, true, false, true => ![0, 1, 2, 3]
  | false, false, false, true, true, false => ![0, 1, 2, 3]
  | false, false, false, true, true, true => ![0, 1, 2, 3]
  | false, false, true, false, false, false => ![0, 1, 3, 2]
  | false, false, true, false, false, true => ![0, 1, 3, 2]
  | false, false, true, false, true, false => ![3, 0, 2, 1]
  | false, false, true, false, true, true => ![0, 1, 2, 3]
  | false, false, true, true, false, false => ![0, 2, 3, 1]
  | false, false, true, true, false, true => ![3, 0, 1, 2]
  | false, false, true, true, true, false => ![0, 2, 3, 1]
  | false, false, true, true, true, true => ![0, 1, 2, 3]
  | false, true, false, false, false, false => ![0, 1, 2, 3]
  | false, true, false, false, false, true => ![0, 1, 2, 3]
  | false, true, false, false, true, false => ![2, 0, 1, 3]
  | false, true, false, false, true, true => ![0, 3, 2, 1]
  | false, true, false, true, false, false => ![0, 1, 2, 3]
  | false, true, false, true, false, true => ![2, 0, 3, 1]
  | false, true, false, true, true, false => ![0, 1, 2, 3]
  | false, true, false, true, true, true => ![0, 3, 2, 1]
  | false, true, true, false, false, false => ![1, 2, 0, 3]
  | false, true, true, false, false, true => ![1, 3, 0, 2]
  | false, true, true, false, true, false => ![2, 3, 1, 0]
  | false, true, true, false, true, true => ![0, 1, 2, 3]
  | false, true, true, true, false, false => ![0, 1, 2, 3]
  | false, true, true, true, false, true => ![3, 2, 1, 0]
  | false, true, true, true, true, false => ![0, 1, 2, 3]
  | false, true, true, true, true, true => ![0, 1, 2, 3]
  | true, false, false, false, false, false => ![0, 1, 2, 3]
  | true, false, false, false, false, true => ![0, 1, 2, 3]
  | true, false, false, false, true, false => ![1, 0, 3, 2]
  | true, false, false, false, true, true => ![0, 3, 1, 2]
  | true, false, false, true, false, false => ![0, 2, 1, 3]
  | true, false, false, true, false, true => ![1, 0, 2, 3]
  | true, false, false, true, true, false => ![0, 2, 1, 3]
  | true, false, false, true, true, true => ![0, 3, 1, 2]
  | true, false, true, false, false, false => ![0, 1, 2, 3]
  | true, false, true, false, false, true => ![0, 1, 2, 3]
  | true, false, true, false, true, false => ![3, 1, 2, 0]
  | true, false, true, false, true, true => ![0, 1, 2, 3]
  | true, false, true, true, false, false => ![2, 1, 0, 3]
  | true, false, true, true, false, true => ![1, 3, 2, 0]
  | true, false, true, true, true, false => ![2, 3, 0, 1]
  | true, false, true, true, true, true => ![0, 1, 2, 3]
  | true, true, false, false, false, false => ![0, 1, 2, 3]
  | true, true, false, false, false, true => ![0, 1, 2, 3]
  | true, true, false, false, true, false => ![1, 2, 3, 0]
  | true, true, false, false, true, true => ![3, 1, 0, 2]
  | true, true, false, true, false, false => ![0, 1, 2, 3]
  | true, true, false, true, false, true => ![2, 1, 3, 0]
  | true, true, false, true, true, false => ![0, 1, 2, 3]
  | true, true, false, true, true, true => ![3, 2, 0, 1]
  | true, true, true, false, false, false => ![0, 1, 2, 3]
  | true, true, true, false, false, true => ![0, 1, 2, 3]
  | true, true, true, false, true, false => ![1, 2, 3, 0]
  | true, true, true, false, true, true => ![0, 1, 2, 3]
  | true, true, true, true, false, false => ![0, 1, 2, 3]
  | true, true, true, true, false, true => ![1, 3, 2, 0]
  | true, true, true, true, true, false => ![0, 1, 2, 3]
  | true, true, true, true, true, true => ![0, 1, 2, 3]

private theorem finFourBoolTournament_selection :
    ∀ edge01 edge02 edge03 edge12 edge13 edge23 : Bool,
      let edge := finFourBoolTournamentEdge
        edge01 edge02 edge03 edge12 edge13 edge23
      let relabel := finFourBoolTournamentRelabel
        edge01 edge02 edge03 edge12 edge13 edge23
      (∀ i, ∃ j, i ≠ j ∧ edge i j = true) →
      Function.Bijective relabel ∧
        edge (relabel 1) (relabel 0) = true ∧
        edge (relabel 2) (relabel 1) = true ∧
        edge (relabel 0) (relabel 2) = true ∧
        edge (relabel 3) (relabel 0) = true ∧
        edge (relabel 3) (relabel 1) = true := by
  intro edge01 edge02 edge03 edge12 edge13 edge23
  fin_cases edge01 <;> fin_cases edge02 <;> fin_cases edge03 <;>
    fin_cases edge12 <;> fin_cases edge13 <;> fin_cases edge23 <;> decide

private theorem exists_finFourIntegralTournamentCycleOutsider_fin
    {A : Fin 4 → Fin 4 → ℝ} (hA : IsIntegralTournament A)
    (hunit : FractionalTournamentHasUnitOutneighbor A) :
    Nonempty (FinFourIntegralTournamentCycleOutsider A) := by
  classical
  let edge : Fin 4 → Fin 4 → Bool := fun i j => decide (A i j = 1)
  have hedge_true (i j : Fin 4) : edge i j = true ↔ A i j = 1 := by
    simp [edge]
  have hedge_false (i j : Fin 4) : edge i j = false ↔ A i j ≠ 1 := by
    simp [edge]
  have hdiag : ∀ i, edge i i = false := by
    intro i
    rw [hedge_false]
    rw [hA.1.1 i]
    norm_num
  have hopposite : ∀ i j, i ≠ j → edge i j = !(edge j i) := by
    intro i j hij
    by_cases hedge : A i j = 1
    · have hreverse : A j i = 0 := by
        nlinarith [hA.1.2.2 i j hij]
      simp [edge, hedge, hreverse]
    · have hzero : A i j = 0 := (hA.2 i j).resolve_right hedge
      have hreverse : A j i = 1 := by
        nlinarith [hA.1.2.2 i j hij]
      simp [edge, hzero, hreverse]
  have hunitEdge : ∀ i, ∃ j, i ≠ j ∧ edge i j = true := by
    intro i
    obtain ⟨j, hij, hedge⟩ := hunit i
    exact ⟨j, hij, (hedge_true i j).2 hedge⟩
  have hedge_eq : edge = finFourBoolTournamentEdge
      (edge 0 1) (edge 0 2) (edge 0 3) (edge 1 2) (edge 1 3) (edge 2 3) := by
    funext i j
    fin_cases i <;> fin_cases j
    · simpa [finFourBoolTournamentEdge] using hdiag 0
    · simp [finFourBoolTournamentEdge]
    · simp [finFourBoolTournamentEdge]
    · simp [finFourBoolTournamentEdge]
    · simpa [finFourBoolTournamentEdge] using hopposite 1 0 (by decide)
    · simpa [finFourBoolTournamentEdge] using hdiag 1
    · simp [finFourBoolTournamentEdge]
    · simp [finFourBoolTournamentEdge]
    · simpa [finFourBoolTournamentEdge] using hopposite 2 0 (by decide)
    · simpa [finFourBoolTournamentEdge] using hopposite 2 1 (by decide)
    · simpa [finFourBoolTournamentEdge] using hdiag 2
    · simp [finFourBoolTournamentEdge]
    · simpa [finFourBoolTournamentEdge] using hopposite 3 0 (by decide)
    · simpa [finFourBoolTournamentEdge] using hopposite 3 1 (by decide)
    · simpa [finFourBoolTournamentEdge] using hopposite 3 2 (by decide)
    · simpa [finFourBoolTournamentEdge] using hdiag 3
  have hunitCanonical : ∀ i, ∃ j, i ≠ j ∧
      finFourBoolTournamentEdge
        (edge 0 1) (edge 0 2) (edge 0 3)
        (edge 1 2) (edge 1 3) (edge 2 3) i j = true := by
    simpa [← hedge_eq] using hunitEdge
  let relabel := finFourBoolTournamentRelabel
    (edge 0 1) (edge 0 2) (edge 0 3)
    (edge 1 2) (edge 1 3) (edge 2 3)
  obtain ⟨hbijective, h10, h21, h02, h30, h31⟩ :=
    finFourBoolTournament_selection
      (edge 0 1) (edge 0 2) (edge 0 3)
      (edge 1 2) (edge 1 3) (edge 2 3) hunitCanonical
  rw [← hedge_eq] at h10 h21 h02 h30 h31
  let e : Fin 4 ≃ Fin 4 := Equiv.ofBijective relabel hbijective
  refine ⟨{
    relabel := e
    one_beats_zero := ?_
    two_beats_one := ?_
    zero_beats_two := ?_
    outsider_beats_zero := ?_
    outsider_beats_one := ?_ }⟩
  · exact (hedge_true _ _).1 h10
  · exact (hedge_true _ _).1 h21
  · exact (hedge_true _ _).1 h02
  · exact (hedge_true _ _).1 h30
  · exact (hedge_true _ _).1 h31

/-- Every four-vertex integral tournament with a unit out-neighbour at each
vertex has a directed triangle and an outsider beating two consecutive
vertices, recorded after one bijective relabelling. -/
theorem exists_finFourIntegralTournamentCycleOutsider
    {A : ι → ι → ℝ} (hcard : Fintype.card ι = 4)
    (hA : IsIntegralTournament A)
    (hunit : FractionalTournamentHasUnitOutneighbor A) :
    Nonempty (FinFourIntegralTournamentCycleOutsider A) := by
  let e : Fin 4 ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let B : Fin 4 → Fin 4 → ℝ := fun i j => A (e i) (e j)
  have hB : IsIntegralTournament B := isIntegralTournament_comp hA e e.injective
  have hBunit : FractionalTournamentHasUnitOutneighbor B := by
    intro i
    obtain ⟨j, hij, hedge⟩ := hunit (e i)
    refine ⟨e.symm j, ?_, ?_⟩
    · intro heq
      apply hij
      simpa using congrArg e heq
    · simpa [B]
  let selected := Classical.choice
    (exists_finFourIntegralTournamentCycleOutsider_fin hB hBunit)
  refine ⟨{
    relabel := selected.relabel.trans e
    one_beats_zero := ?_
    two_beats_one := ?_
    zero_beats_two := ?_
    outsider_beats_zero := ?_
    outsider_beats_one := ?_ }⟩
  · exact selected.one_beats_zero
  · exact selected.two_beats_one
  · exact selected.zero_beats_two
  · exact selected.outsider_beats_zero
  · exact selected.outsider_beats_one

end Math.LinearProgramming
