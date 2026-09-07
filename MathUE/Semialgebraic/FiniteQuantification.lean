import MathUE.Semialgebraic.PolynomialMap

/-! Finite discrete quantifiers and last-coordinate block projection. -/

namespace MathUE.IsSemialgebraic

theorem forall_finset {n : ℕ} {ι : Type*} (indices : Finset ι)
    (predicate : ι → (Fin n → ℝ) → Prop)
    (h : ∀ index ∈ indices, IsSemialgebraic {point | predicate index point}) :
    IsSemialgebraic {point | ∀ index ∈ indices, predicate index point} := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using
      (univ : IsSemialgebraic (Set.univ : Set (Fin n → ℝ)))
  | @insert index indices hnot ih =>
      have hi := h index (Finset.mem_insert_self _ _)
      have hs := ih (fun other hother => h other (Finset.mem_insert_of_mem hother))
      convert hi.inter hs using 1
      ext point
      simp only [Set.mem_setOf_eq, Finset.forall_mem_insert, Set.mem_inter_iff]

theorem exists_finset {n : ℕ} {ι : Type*} (indices : Finset ι)
    (predicate : ι → (Fin n → ℝ) → Prop)
    (h : ∀ index ∈ indices, IsSemialgebraic {point | predicate index point}) :
    IsSemialgebraic {point | ∃ index ∈ indices, predicate index point} := by
  have hneg := forall_finset indices (fun index point => ¬ predicate index point)
    (fun index hi => h index hi |>.compl)
  convert hneg.compl using 1
  ext point
  simp

/-- Existentially remove a last coordinate block, preserving the first block's order. -/
theorem exists_last_coordinates {n k : ℕ} {set : Set (Fin (n + k) → ℝ)}
    (h : IsSemialgebraic set) :
    IsSemialgebraic {environment : Fin n → ℝ | ∃ witnesses : Fin k → ℝ,
      Fin.append environment witnesses ∈ set} := by
  have himage := h.image_polynomialMap
    (fun index : Fin n => MvPolynomial.X (Fin.castAdd k index))
  convert himage using 1
  ext environment
  constructor
  · rintro ⟨witnesses, hw⟩
    refine ⟨Fin.append environment witnesses, hw, ?_⟩
    funext index
    simp only [evaluatePolynomialMap, MvPolynomial.eval_X, Fin.append_left]
  · rintro ⟨point, hp, heq⟩
    refine ⟨fun index => point (Fin.natAdd n index), ?_⟩
    have hfirst : environment = fun index => point (Fin.castAdd k index) := by
      funext index
      have hi := congrFun heq.symm index
      simpa only [evaluatePolynomialMap, MvPolynomial.eval_X] using hi
    rw [hfirst, Fin.append_castAdd_natAdd]
    exact hp

/-- Universally quantify a last coordinate block, leaving the first block untouched. -/
theorem forall_last_coordinates {n k : ℕ} {set : Set (Fin (n + k) → ℝ)}
    (h : IsSemialgebraic set) :
    IsSemialgebraic {environment : Fin n → ℝ | ∀ witnesses : Fin k → ℝ,
      Fin.append environment witnesses ∈ set} := by
  have hresult := h.compl.exists_last_coordinates.compl
  convert hresult using 1
  ext environment
  simp

end MathUE.IsSemialgebraic
