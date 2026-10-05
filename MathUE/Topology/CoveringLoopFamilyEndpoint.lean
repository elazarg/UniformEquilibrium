import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.LocallyConstant.Basic

/-! # Lifted endpoints of continuous families of based loops

A covering map lifts a continuous loop family from one fixed point. Its terminal
value varies continuously in the discrete fiber, hence locally constantly.
No connectedness or local connectedness of the parameter space is required.
This supplies a concrete invariant, not a prescribed winding-number callback.
-/

noncomputable section

namespace Math.Topology

open unitInterval

variable {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace A] {projection : E → X}

namespace CoveringLoopFamily

/-- One path in a jointly continuous family. -/
def slice (family : C(unitInterval × A, X)) (parameter : A) : C(unitInterval, X) :=
  family.comp ((ContinuousMap.id unitInterval).prodMk (.const unitInterval parameter))

/-- The actual endpoint of the lifted family, retained in its covering fiber. -/
def endpoint (cover : IsCoveringMap projection) (base : X)
    (start : projection ⁻¹' {base}) (family : C(unitInterval × A, X))
    (hzero : ∀ parameter, family (0, parameter) = base)
    (hone : ∀ parameter, family (1, parameter) = base) :
    C(A, projection ⁻¹' {base}) := by
  have hstart : projection start.val = base := start.property
  let initial : C(A, E) := .const A start.val
  have hinitial : ∀ parameter, family (0, parameter) = projection (initial parameter) :=
    fun parameter => (hzero parameter).trans hstart.symm
  let lifted : C(unitInterval × A, E) := cover.liftHomotopy family initial hinitial
  have hend : ∀ parameter, projection (lifted (1, parameter)) = base := by
    intro parameter
    exact (congrFun (cover.liftHomotopy_lifts family initial hinitial)
      (1, parameter)).trans (hone parameter)
  exact ⟨fun parameter => ⟨lifted (1, parameter), hend parameter⟩,
    (lifted.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk hend⟩

/-- Evaluation agrees with the canonical lift of the selected path. -/
theorem endpoint_val (cover : IsCoveringMap projection) (base : X)
    (start : projection ⁻¹' {base}) (family : C(unitInterval × A, X))
    (hzero : ∀ parameter, family (0, parameter) = base)
    (hone : ∀ parameter, family (1, parameter) = base) (parameter : A) :
    (endpoint cover base start family hzero hone parameter).val =
      cover.liftPath (slice family parameter) start.val
        ((hzero parameter).trans
          (show projection start.val = base from start.property).symm) 1 := rfl

/-- Continuity into the discrete covering fiber makes the endpoint locally constant. -/
theorem endpoint_isLocallyConstant (cover : IsCoveringMap projection) (base : X)
    (start : projection ⁻¹' {base}) (family : C(unitInterval × A, X))
    (hzero : ∀ parameter, family (0, parameter) = base)
    (hone : ∀ parameter, family (1, parameter) = base) :
    IsLocallyConstant (endpoint cover base start family hzero hone) := by
  let : DiscreteTopology (projection ⁻¹' {base}) := (cover base).discreteTopology_fiber
  exact (IsLocallyConstant.iff_continuous _).mpr
    (endpoint cover base start family hzero hone).continuous

/-- Endpoint-fixed homotopic slices have the same actual lifted endpoint. -/
theorem endpoint_eq_of_homotopicRel (cover : IsCoveringMap projection) (base : X)
    (start : projection ⁻¹' {base}) (family : C(unitInterval × A, X))
    (hzero : ∀ parameter, family (0, parameter) = base)
    (hone : ∀ parameter, family (1, parameter) = base) (first last : A)
    (hhomotopic : (slice family first).HomotopicRel (slice family last) {0, 1}) :
    endpoint cover base start family hzero hone first =
      endpoint cover base start family hzero hone last := by
  apply Subtype.ext
  simp only [endpoint_val]
  exact cover.liftPath_apply_one_eq_of_homotopicRel hhomotopic start.val
    ((hzero first).trans (show projection start.val = base from start.property).symm)
    ((hzero last).trans (show projection start.val = base from start.property).symm)

/-- A constant member of the loop family lifts to the constant path at the start. -/
theorem endpoint_eq_start_of_constant (cover : IsCoveringMap projection) (base : X)
    (start : projection ⁻¹' {base}) (family : C(unitInterval × A, X))
    (hzero : ∀ parameter, family (0, parameter) = base)
    (hone : ∀ parameter, family (1, parameter) = base) (parameter : A)
    (hconstant : slice family parameter = .const unitInterval base) :
    endpoint cover base start family hzero hone parameter = start := by
  apply Subtype.ext
  rw [endpoint_val]
  have hstart : projection start.val = base := start.property
  have hconstantLift := cover.liftPath_const (e := start.val) hstart.symm
  have hend := congrArg (fun lifted : C(unitInterval, E) => lifted 1) hconstantLift
  simpa only [hconstant, ContinuousMap.const_apply] using hend

end CoveringLoopFamily

end Math.Topology
