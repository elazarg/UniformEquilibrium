import MathUE.ProbabilityMassFunction
import MathUE.ProbabilityMassFunction.FiniteSumExpectation
import MathUE.ProbabilityMassFunction.IndicatorExpectation

/-! # Moving one atom of an arbitrary probability mass function

The replacement is an actual deterministic pushforward. Its source mass may
be zero or one; no residual-law division is used.
-/

noncomputable section

namespace Math.ProbabilityMassFunction

open Math.Probability

/-- Move the complete mass at `source` to `target`, retaining every other atom. -/
def pmfMoveAtom {Ω : Type*} (law : PMF Ω) (source target : Ω) : PMF Ω := by
  classical
  exact law.map (fun point => if point = source then target else point)

theorem pmfMoveAtom_source {Ω : Type*}
    (law : PMF Ω) (source target : Ω) (hdifferent : source ≠ target) :
    pmfMoveAtom law source target source = 0 := by
  classical
  rw [pmfMoveAtom, PMF.map_apply]
  calc
    _ = ∑' _ : Ω, (0 : ENNReal) := by
      apply tsum_congr
      intro point
      by_cases hpoint : point = source
      · simp [hpoint, hdifferent]
      · simp [hpoint, Ne.symm hpoint]
    _ = 0 := tsum_zero

theorem pmfMoveAtom_target {Ω : Type*}
    (law : PMF Ω) (source target : Ω) (hdifferent : source ≠ target) :
    pmfMoveAtom law source target target = law source + law target := by
  classical
  rw [pmfMoveAtom, PMF.map_apply]
  calc
    (∑' point, if target = (if point = source then target else point)
        then law point else 0) =
        ∑' point, ((if point = source then law source else 0) +
          (if point = target then law target else 0)) := by
      apply tsum_congr
      intro point
      by_cases hsource : point = source
      · simp [hsource, hdifferent]
      · by_cases htarget : point = target
        · simp [htarget, Ne.symm hdifferent]
        · simp [hsource, htarget, Ne.symm htarget]
    _ = law source + law target := by
      rw [ENNReal.tsum_add, tsum_ite_eq, tsum_ite_eq]

theorem pmfMoveAtom_apply_of_ne {Ω : Type*}
    (law : PMF Ω) (source target point : Ω)
    (hsource : point ≠ source) (htarget : point ≠ target) :
    pmfMoveAtom law source target point = law point := by
  classical
  rw [pmfMoveAtom, PMF.map_apply]
  rw [tsum_eq_single point]
  · simp [hsource]
  · intro other hother
    by_cases hotherSource : other = source
    · simp [hotherSource, htarget]
    · simp [hotherSource, Ne.symm hother]

/-- The exact expectation gain from a one-atom move, for every bounded
observable on an arbitrary discrete sample type. -/
theorem expect_pmfMoveAtom_sub {Ω : Type*}
    (law : PMF Ω) (source target : Ω) (f : Ω → ℝ) {bound : ℝ}
    (hbound : ∀ point, |f point| ≤ bound) :
    expect (pmfMoveAtom law source target) f - expect law f =
      (law source).toReal * (f target - f source) := by
  classical
  rw [pmfMoveAtom, expect_map]
  have hmoved : ∀ point, |f (if point = source then target else point)| ≤ bound := by
    intro point
    exact hbound _
  rw [← expect_sub_of_abs_bounds law
    (fun point => f (if point = source then target else point)) f hmoved hbound]
  calc
    expect law (fun point => f (if point = source then target else point) - f point) =
        expect law (fun point => (f target - f source) *
          (if point = source then 1 else 0)) := by
      congr 1
      funext point
      by_cases hpoint : point = source <;> simp [hpoint]
    _ = (f target - f source) * (law source).toReal := by
      rw [expect_const_mul, expect_singletonIndicator]
    _ = (law source).toReal * (f target - f source) := mul_comm _ _

/-- Delaying a finite atom to the adjacent date leaves the Never atom unchanged. -/
theorem pmfMoveAtom_adjacent_none (law : PMF (Option ℕ)) (time : ℕ) :
    pmfMoveAtom law (some time) (some (time + 1)) none = law none := by
  apply pmfMoveAtom_apply_of_ne <;> simp

theorem pmfMoveAtom_adjacent_other (law : PMF (Option ℕ)) (time other : ℕ)
    (hsource : other ≠ time) (htarget : other ≠ time + 1) :
    pmfMoveAtom law (some time) (some (time + 1)) (some other) = law (some other) := by
  apply pmfMoveAtom_apply_of_ne
  · simpa using hsource
  · simpa using htarget

end Math.ProbabilityMassFunction
