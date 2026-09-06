import MathUE.LinearProgramming.PivotRepairMassPolytope

noncomputable section

namespace Math.LinearProgramming

/-- Replace only the relaxed first-tail-atom coordinate of a repair mass. -/
def pivotRepairMassWithFirstAtom {deadline : ℕ}
    (mass : PivotRepairMass deadline) (firstAtom : ℝ) : PivotRepairMass deadline :=
  Function.update mass (Sum.inr PivotRepairTailCoordinate.firstAtom) firstAtom

@[simp] theorem pivotRepairHead_withFirstAtom {deadline : ℕ}
    (mass : PivotRepairMass deadline) (firstAtom : ℝ) (time : Fin deadline) :
    pivotRepairHead (pivotRepairMassWithFirstAtom mass firstAtom) time =
      pivotRepairHead mass time := by
  simp [pivotRepairHead, pivotRepairMassWithFirstAtom]

@[simp] theorem pivotRepairLate_withFirstAtom {deadline : ℕ}
    (mass : PivotRepairMass deadline) (firstAtom : ℝ) :
    pivotRepairLate (pivotRepairMassWithFirstAtom mass firstAtom) =
      pivotRepairLate mass := by
  simp [pivotRepairLate, pivotRepairMassWithFirstAtom]

@[simp] theorem pivotRepairNever_withFirstAtom {deadline : ℕ}
    (mass : PivotRepairMass deadline) (firstAtom : ℝ) :
    pivotRepairNever (pivotRepairMassWithFirstAtom mass firstAtom) =
      pivotRepairNever mass := by
  simp [pivotRepairNever, pivotRepairMassWithFirstAtom]

@[simp] theorem pivotRepairFirstAtom_withFirstAtom {deadline : ℕ}
    (mass : PivotRepairMass deadline) (firstAtom : ℝ) :
    pivotRepairFirstAtom (pivotRepairMassWithFirstAtom mass firstAtom) = firstAtom := by
  simp [pivotRepairFirstAtom, pivotRepairMassWithFirstAtom]

/-- Updating the first atom inside `[0, late]` preserves every literal mass constraint. -/
theorem isPivotRepairMassFeasible_withFirstAtom {deadline : ℕ}
    {mass : PivotRepairMass deadline} (hmass : IsPivotRepairMassFeasible mass)
    {firstAtom : ℝ} (hfirst : 0 ≤ firstAtom)
    (hle : firstAtom ≤ pivotRepairLate mass) :
    IsPivotRepairMassFeasible (pivotRepairMassWithFirstAtom mass firstAtom) := by
  rcases hmass with ⟨hhead, hlate, hnever, hsum, -, -⟩
  exact ⟨by simpa using hhead, by simpa using hlate, by simpa using hnever,
    by simpa using hsum, by simpa using hfirst, by simpa using hle⟩

end Math.LinearProgramming
