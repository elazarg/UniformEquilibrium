/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Viability.ControlledIntegralTrajectory
import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQSupportCorrespondence

/-!
# Principal-Q controlled trajectories

This module states the viability trajectory used in the standard-Q branch of
the absorption-path construction.  It keeps the paper's clock literally:

`q'(t) = t⁻¹ (R z(t) - q(t))`,

with `q(t)` on the nonnegative boundary and `z(t)` supported on the zero face
of `q(t)`.  The integral formulation permits measurable controls and does not
silently strengthen the classical viability conclusion to differentiability
at every time.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Math Math.LinearProgramming Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The time-scaled residual dynamics in the paper's viability equation. -/
def principalQPaperDynamics (M : ι → ι → ℝ) (time : ℝ)
    (q : ι → ℝ) (z : stdSimplex ℝ ι) : ι → ℝ :=
  time⁻¹ • fun i => singletonLCPResidual M z i - q i

/-- The admissible controls at a paper time: simplex weights supported on the
current zero face.  The clock does not change admissibility. -/
def principalQPaperControls (_time : ℝ) (q : ι → ℝ) :
    Set (stdSimplex ℝ ι) :=
  principalQSupportControls q

/-- An integral solution of the paper's controlled viability equation on
`[start, finish]`. -/
abbrev PrincipalQControlledTrajectory
    (M : ι → ι → ℝ) (start finish : ℝ) (initial : ι → ℝ) :=
  Viability.ControlledIntegralTrajectory nonnegativeBoundary
    principalQPaperControls (principalQPaperDynamics M) start finish initial

omit [DecidableEq ι] in
@[simp] theorem principalQPaperDynamics_apply
    (M : ι → ι → ℝ) (time : ℝ) (q : ι → ℝ)
    (z : stdSimplex ℝ ι) (i : ι) :
    principalQPaperDynamics M time q z i =
      time⁻¹ * (singletonLCPResidual M z i - q i) := by
  rfl

omit [DecidableEq ι] in
/-- The paper dynamics are the autonomous principal-Q velocity divided by the
current clock (using Lean's totalized division also at zero). -/
theorem principalQPaperDynamics_eq_div
    (M : ι → ι → ℝ) (time : ℝ)
    (q : ι → ℝ) (z : stdSimplex ℝ ι) :
    principalQPaperDynamics M time q z = fun i =>
      (singletonLCPResidual M z i - q i) / time := by
  funext i
  simp [principalQPaperDynamics, div_eq_mul_inv, mul_comm]

omit [DecidableEq ι] in
/-- A support-compatible control produces a velocity in the corrected
principal-Q velocity fiber before clock scaling. -/
theorem principalQVelocity_mem_of_paperControl
    (M : ι → ι → ℝ) (time : ℝ) (q : ι → ℝ)
    (z : stdSimplex ℝ ι) (hz : z ∈ principalQPaperControls time q) :
    (fun i => singletonLCPResidual M z i - q i) ∈
      principalQVelocities M q := by
  exact ⟨z, hz, rfl⟩

end GameTheory.QuittingLCPClassification
