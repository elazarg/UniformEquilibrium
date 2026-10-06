import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

/-! # A circle has no closed continuous logarithm

Covering uniqueness identifies every logarithmic lift of the explicit scaled
circle with its initial value plus the straight `2*pi*I` lift. The endpoint
displacement is nonzero. No Jordan curve theorem or planar image contraction
is asserted, and no integer-valued winding invariant is supplied as a premise.
-/

noncomputable section

namespace Math.Topology

/-- The explicit one-turn logarithmic increment on the unit interval. -/
def complexCircleLogIncrement : C(unitInterval, ℂ) where
  toFun time := (time.val : ℂ) * (2 * Real.pi * Complex.I)
  continuous_toFun := by fun_prop

/-- The projected explicit path closes after one turn. -/
theorem scaled_circle_exponential_endpoints (scale : ℂ) :
    scale * Complex.exp (complexCircleLogIncrement 0) =
      scale * Complex.exp (complexCircleLogIncrement 1) := by
  simp [complexCircleLogIncrement, Complex.exp_two_pi_mul_I]

/-- Every logarithm of a scaled circle is the explicit lift plus its initial value.
No nonzero-scale premise is necessary: existence of the logarithm already forces it. -/
theorem circle_logarithm_eq_initial_add (scale : ℂ) (lifted : C(unitInterval, ℂ))
    (hlift : ∀ time, Complex.exp (lifted time) =
      scale * Complex.exp (complexCircleLogIncrement time)) :
    ∀ time, lifted time = lifted 0 + complexCircleLogIncrement time := by
  let explicit : C(unitInterval, ℂ) :=
    ⟨fun time => lifted 0 + complexCircleLogIncrement time,
      continuous_const.add complexCircleLogIncrement.continuous⟩
  have hzero : Complex.exp (lifted 0) = scale := by
    simpa [complexCircleLogIncrement] using hlift 0
  have hprojection :
      (fun z : ℂ => (⟨z.exp, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) ∘ lifted =
      (fun z : ℂ => (⟨z.exp, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) ∘ explicit := by
    funext time
    apply Subtype.ext
    change Complex.exp (lifted time) =
      Complex.exp (lifted 0 + complexCircleLogIncrement time)
    rw [Complex.exp_add, hzero, hlift]
  have hinitial : lifted 0 = explicit 0 := by
    simp [explicit, complexCircleLogIncrement]
  have hequal := Complex.isCoveringMap_exp.eq_of_comp_eq
    lifted.continuous explicit.continuous hprojection 0 hinitial
  intro time
  exact congrFun hequal time

/-- The actual lift displacement of one positively oriented turn. -/
theorem circle_logarithm_endpoint (scale : ℂ) (lifted : C(unitInterval, ℂ))
    (hlift : ∀ time, Complex.exp (lifted time) =
      scale * Complex.exp (complexCircleLogIncrement time)) :
    lifted 1 = lifted 0 + 2 * Real.pi * Complex.I := by
  simpa [complexCircleLogIncrement] using circle_logarithm_eq_initial_add scale lifted hlift 1

/-- There is no closed continuous logarithm of a scaled one-turn circle. -/
theorem not_exists_closed_circle_logarithm (scale : ℂ) :
    ¬∃ lifted : C(unitInterval, ℂ),
      (∀ time, Complex.exp (lifted time) =
        scale * Complex.exp (complexCircleLogIncrement time)) ∧ lifted 0 = lifted 1 := by
  rintro ⟨lifted, hlift, hclosed⟩
  have hend := circle_logarithm_endpoint scale lifted hlift
  have hzero : (2 : ℂ) * Real.pi * Complex.I = 0 := by
    have h := hclosed.trans hend
    exact add_left_cancel (show lifted 0 + 2 * Real.pi * Complex.I = lifted 0 + 0 by
      simpa only [add_zero] using h.symm)
  have hnonzero : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  exact hnonzero hzero

end Math.Topology
