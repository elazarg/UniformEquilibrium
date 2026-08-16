/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability
import UniformEquilibrium.ProofView.Concepts.Equilibrium.SolutionConcepts
import UniformEquilibrium.ProofView.Concepts.Equilibrium.StrictNashProperties

/-!
# Approximate (ε-Nash) Equilibrium

An ε-Nash equilibrium is a strategy profile where no player can improve their
expected utility by more than ε through unilateral deviation. This relaxation
is fundamental in computational game theory and convergence arguments.

## Main definitions

* `KernelGame.IsεNash` — ε-Nash equilibrium
* `KernelGame.IsεBestResponse` — ε-best response

## Main results

* `IsεNash.of_isNash` — every Nash equilibrium is ε-Nash for all ε ≥ 0
* `isNash_iff_isεNash_zero` — Nash ↔ 0-Nash
* `IsεNash.mono` — monotonicity: ε-Nash implies ε'-Nash for ε ≤ ε'
* `IsεNash.add` — if σ is ε₁-Nash and each player's deviation gains at most ε₂
    from reindexing, the combined bound holds
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι] (G : KernelGame ι)

open Classical in
/-- A strategy profile `σ` is an ε-Nash equilibrium if no player can improve
    their expected utility by more than `ε` through unilateral deviation. -/
def IsεNash (ε : ℝ) (σ : Profile G) : Prop :=
  ∀ (who : ι) (s' : G.Strategy who),
    G.eu σ who + ε ≥ G.eu (Function.update σ who s') who

open Classical in
/-- `s` is an ε-best response for `who` against opponents fixed by `σ`. -/
def IsεBestResponse (ε : ℝ) (who : ι) (σ : Profile G) (s : G.Strategy who) : Prop :=
  ∀ (s' : G.Strategy who),
    G.eu (Function.update σ who s) who + ε ≥
      G.eu (Function.update σ who s') who

/-- Every Nash equilibrium is an ε-Nash equilibrium for any ε ≥ 0. -/
theorem IsεNash.of_isNash {σ : Profile G} (hN : G.IsNash σ) {ε : ℝ} (hε : ε ≥ 0) :
    G.IsεNash ε σ := by
  intro who s'
  have h := hN who s'
  linarith

/-- A 0-Nash equilibrium is exactly a Nash equilibrium. -/
theorem isNash_iff_isεNash_zero {σ : Profile G} :
    G.IsNash σ ↔ G.IsεNash 0 σ := by
  constructor
  · exact fun h => IsεNash.of_isNash G h (le_refl 0)
  · intro h who s'
    have := h who s'
    linarith

/-- ε-Nash is monotone in ε. -/
theorem IsεNash.mono {σ : Profile G} {ε₁ ε₂ : ℝ} (h : G.IsεNash ε₁ σ) (hle : ε₁ ≤ ε₂) :
    G.IsεNash ε₂ σ := by
  intro who s'
  have := h who s'
  linarith

/-- ε-best-response characterization of ε-Nash. -/
theorem isεNash_iff_εBestResponse {ε : ℝ} {σ : Profile G} :
    G.IsεNash ε σ ↔ ∀ who, G.IsεBestResponse ε who σ (σ who) := by
  classical
  constructor
  · intro h who s'
    have := h who s'
    simp only [Function.update_eq_self] at *
    exact this
  · intro h who s'
    have := h who s'
    simp only [Function.update_eq_self] at this
    exact this

/-- A strict Nash equilibrium is ε-Nash for any ε ≥ 0. -/
theorem IsStrictNash.isεNash {σ : Profile G} (h : G.IsStrictNash σ) {ε : ℝ} (hε : ε ≥ 0) :
    G.IsεNash ε σ :=
  IsεNash.of_isNash G h.isNash hε

end KernelGame

end GameTheory
