import MathUE.RealQuantifierElimination.RealCoefficientReification
import MathUE.RealQuantifierElimination.QuantifierElimination

/-!
# Projection of real-coefficient semialgebraic sets

The actual rational-syntax eliminator is applied with fixed real coefficient
parameters. Projection and universal quantification preserve semialgebraicity
for any finite block of coordinates.
-/

namespace MathUE

open RealQuantifierElimination

namespace IsSemialgebraic

/-- Projection along one real coordinate, using the actual proved eliminator. -/
theorem exists_first {n : ℕ} {set : Set (Fin (n + 1) → ℝ)}
    (h : IsSemialgebraic set) :
    IsSemialgebraic {environment : Fin n → ℝ | ∃ value : ℝ,
      Fin.cons value environment ∈ set} := by
  obtain ⟨formula, hformula⟩ := h
  obtain ⟨k, parameters, rationalFormula, hreification⟩ := formula.exists_rationalReification
  let reordered : QuantifierFreeFormula ((n + k) + 1) :=
    rationalFormula.rename (Fin.cast (Nat.add_right_comm n 1 k))
  have hequivalent : ∀ environment : Fin n → ℝ,
      (∃ value, Fin.cons value environment ∈ set) ↔
        ∃ value, QuantifierFreeFormula.HoldsAt reordered
          (Fin.cons value (Fin.append environment parameters)) := by
    intro environment
    apply exists_congr
    intro value
    have hrename := QuantifierFreeFormula.holdsAt_rename
      (Fin.cast (Nat.add_right_comm n 1 k)) rationalFormula
      (Fin.cons value (Fin.append environment parameters))
    have henv : Fin.append (Fin.cons value environment) parameters =
        Fin.cons value (Fin.append environment parameters) ∘
          Fin.cast (Nat.add_right_comm n 1 k) :=
      Fin.append_cons value environment parameters
    rw [← henv] at hrename
    constructor
    · intro hx
      have hr : RealPolynomialSignFormula.HoldsAt formula (Fin.cons value environment) :=
        (hformula (Fin.cons value environment)).mp hx
      have hq : QuantifierFreeFormula.HoldsAt rationalFormula
          (Fin.append (Fin.cons value environment) parameters) :=
        (hreification (Fin.cons value environment)).mpr hr
      exact hrename.mpr hq
    · intro hx
      have hq : QuantifierFreeFormula.HoldsAt rationalFormula
          (Fin.append (Fin.cons value environment) parameters) := hrename.mp hx
      exact (hformula (Fin.cons value environment)).mpr
        ((hreification (Fin.cons value environment)).mp hq)
  exact of_rational_presentation parameters (eliminateOneVariable reordered)
    (fun environment => (hequivalent environment).trans
      (eliminateOneVariable_holdsAt_iff reordered (Fin.append environment parameters)).symm)

/-- Universal quantification also preserves semialgebraicity, by complement and projection. -/
theorem forall_first {n : ℕ} {set : Set (Fin (n + 1) → ℝ)}
    (h : IsSemialgebraic set) :
    IsSemialgebraic {environment : Fin n → ℝ | ∀ value : ℝ,
      Fin.cons value environment ∈ set} := by
  have hresult := h.compl.exists_first.compl
  convert hresult using 1
  ext environment
  simp

/-- Projection along an arbitrary finite block of coordinates preserves semialgebraicity. -/
theorem exists_coordinates {n k : ℕ} {set : Set (Fin (k + n) → ℝ)}
    (h : IsSemialgebraic set) :
    IsSemialgebraic {environment : Fin n → ℝ | ∃ witnesses : Fin k → ℝ,
      Fin.append witnesses environment ∈ set} := by
  induction k with
  | zero =>
      have hresult := h.preimage_coordinates (Fin.cast (Nat.zero_add n))
      convert hresult using 1
      ext environment
      constructor
      · rintro ⟨witnesses, hw⟩
        have heq : witnesses = Fin.elim0 := Subsingleton.elim _ _
        simpa only [heq, Fin.elim0_append, Set.mem_setOf_eq] using hw
      · intro he
        exact ⟨Fin.elim0, by simpa only [Fin.elim0_append, Set.mem_setOf_eq] using he⟩
  | succ k ih =>
      have hreordered := h.preimage_coordinates (Fin.cast (Nat.add_right_comm k 1 n))
      have hresult := ih hreordered.exists_first
      convert hresult using 1
      ext environment
      constructor
      · rintro ⟨witnesses, hw⟩
        refine ⟨fun i => witnesses i.succ, witnesses 0, ?_⟩
        have heq : Fin.cons (witnesses 0) (fun i => witnesses i.succ) = witnesses := by
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
        change Fin.cons (witnesses 0)
          (Fin.append (fun i => witnesses i.succ) environment) ∘
            Fin.cast (Nat.add_right_comm k 1 n) ∈ set
        rw [← Fin.append_cons, heq]
        exact hw
      · rintro ⟨witnesses, value, hw⟩
        refine ⟨Fin.cons value witnesses, ?_⟩
        rw [Fin.append_cons]
        exact hw

/-- Universal quantification of any finite block preserves semialgebraicity. -/
theorem forall_coordinates {n k : ℕ} {set : Set (Fin (k + n) → ℝ)}
    (h : IsSemialgebraic set) :
    IsSemialgebraic {environment : Fin n → ℝ | ∀ witnesses : Fin k → ℝ,
      Fin.append witnesses environment ∈ set} := by
  have hresult := h.compl.exists_coordinates.compl
  convert hresult using 1
  ext environment
  simp

/-- The ordinary set image under deletion of a finite initial coordinate block
is semialgebraic; this is the set-theoretic projection form of the theorem. -/
theorem image_coordinate_projection {n k : ℕ} {set : Set (Fin (k + n) → ℝ)}
    (h : IsSemialgebraic set) :
    IsSemialgebraic ((fun point : Fin (k + n) → ℝ =>
      fun index : Fin n => point (Fin.natAdd k index)) '' set) := by
  have hresult := h.exists_coordinates
  convert hresult using 1
  ext environment
  constructor
  · rintro ⟨point, hp, rfl⟩
    refine ⟨fun i => point (Fin.castAdd n i), ?_⟩
    simpa only [Fin.append_castAdd_natAdd] using hp
  · rintro ⟨witnesses, hw⟩
    refine ⟨Fin.append witnesses environment, hw, ?_⟩
    funext i
    exact Fin.append_right witnesses environment i

end IsSemialgebraic

end MathUE
