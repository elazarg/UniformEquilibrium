/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import GameTheory.Math.Probability.FinDist
import MathUE.PMFProduct

/-!
# Finite-carrier PMFs as finite-support laws

On a finite carrier, a Mathlib `PMF` has finite support and therefore defines
the canonical `GameTheory.Math.Probability.FinDist`. This is the narrow
representation bridge used when a proof is most naturally carried out with
Mathlib's PMF calculus and execution is delegated to GameTheory's finite-law
runner.
-/

noncomputable section

namespace Math.Probability

open GameTheory.Math.Probability

variable {α β : Type*}

/-- Regard a PMF on a finite carrier as a canonical finite-support law. -/
def finDistOfPMF [Finite α] (μ : PMF α) : FinDist α :=
  ⟨μ, Set.toFinite _⟩

@[simp]
theorem toPMF_finDistOfPMF [Finite α] (μ : PMF α) :
    (finDistOfPMF μ).toPMF = μ :=
  rfl

@[simp]
theorem finDistOfPMF_toPMF [Finite α] (μ : FinDist α) :
    finDistOfPMF μ.toPMF = μ := by
  exact FinDist.ext rfl

@[simp]
theorem finDistOfPMF_pure [Finite α] (a : α) :
    finDistOfPMF (PMF.pure a) = FinDist.pure a := by
  exact FinDist.ext rfl

@[simp]
theorem finDistOfPMF_bind [Finite α] [Finite β]
    (μ : PMF α) (f : α → PMF β) :
    finDistOfPMF (μ.bind f) =
      FinDist.bind (finDistOfPMF μ) (fun a => finDistOfPMF (f a)) := by
  exact FinDist.ext rfl

@[simp]
theorem expect_finDistOfPMF [Finite α] (μ : PMF α) (observable : α → ℝ) :
    FinDist.expect (finDistOfPMF μ) observable = expect μ observable :=
  rfl

end Math.Probability
