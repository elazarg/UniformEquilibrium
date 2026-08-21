/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQBoundaryDirection

/-!
# Finite principal-Q boundary Euler chains

The principal-face direction can be refreshed after every Euler step.  Thus,
for every positive mesh bound and every finite length, there is a chain on the
nonnegative boundary whose controls are supported on the current zero face and
whose step sizes are smaller than the mesh.

This is the finite polygonal input to a corrected viability construction.  It
does not assert a positive lower bound on step sizes, divergence of accumulated
time, or convergence to a differential-inclusion solution; those are exactly
the compactness/non-Zeno facts still needed beyond the invalid closed-graph
argument in the published proof.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Math.LinearProgramming

/-- One refreshed Euler step from `q` to `q'`, with a simplex control on the
zero face of `q` and a step size below `stepBound`. -/
def IsBoundaryEulerStep {ι : Type} [Fintype ι]
    (M : ι → ι → ℝ) (stepBound : ℝ) (q q' : ι → ℝ) : Prop :=
  ∃ direction : NonnegativeBoundaryDirection M q, ∃ α : ℝ,
    0 < α ∧ α < stepBound ∧ α < 1 ∧
      q' = fun i =>
        (1 - α) * q i + α * singletonLCPResidual M direction.weight i

/-- A length-`n` Euler chain, recursively refreshed at every boundary point. -/
def IsBoundaryEulerChain {ι : Type} [Fintype ι]
    (M : ι → ι → ℝ) (stepBound : ℝ) : ℕ → (ι → ℝ) → Prop
  | 0, q => IsNonnegativeBoundary q
  | n + 1, q => IsNonnegativeBoundary q ∧ ∃ q' : ι → ℝ,
      IsBoundaryEulerStep M stepBound q q' ∧
        IsBoundaryEulerChain M stepBound n q'

/-- Complete projective-Q control on every principal face supplies arbitrarily
long finite boundary Euler chains at every positive mesh. -/
theorem exists_boundaryEulerChain
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (n : ℕ) (q : ι → ℝ)
    (hq : IsNonnegativeBoundary q) :
    IsBoundaryEulerChain M stepBound n q := by
  induction n generalizing q with
  | zero => exact hq
  | succ n ih =>
      obtain ⟨direction⟩ :=
        exists_nonnegativeBoundaryDirection M hdiag hQ q hq
      obtain ⟨α, hα, hαbound, hαone, hnext⟩ :=
        direction.exists_boundary_step hq hstepBound
      let q' : ι → ℝ := fun i =>
        (1 - α) * q i + α * singletonLCPResidual M direction.weight i
      refine ⟨hq, q', ?_, ih q' hnext⟩
      exact ⟨direction, α, hα, hαbound, hαone, rfl⟩

end GameTheory.QuittingLCPClassification
