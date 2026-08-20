/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.MaxAffineTransport
import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic

/-!
# Max-affine transport for anchored solo-periodic renewal

The renewal law of an anchored solo-periodic schedule is exact positive-slope
transport along its phases, with the spectator coordinate held fixed.  The
phase label has survival slope `1 - hazard` and hazard-weighted terminal shift.
-/

noncomputable section

open Math Math.MaxAffineTransport

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- The phase graph of an anchored solo-periodic schedule: the edge of a phase
runs from the next phase to it, in the direction the renewal law computes. -/
def quittingAnchoredRenewalGraph (m : ℕ) : EdgeGraph (Fin m) (Fin m) where
  source phase := finRotate m phase
  target phase := phase

@[simp] theorem source_quittingAnchoredRenewalGraph (phase : Fin m) :
    (quittingAnchoredRenewalGraph m).source phase = finRotate m phase := rfl

@[simp] theorem target_quittingAnchoredRenewalGraph (phase : Fin m) :
    (quittingAnchoredRenewalGraph m).target phase = phase := rfl

/-- The renewal label in one fixed spectator coordinate. -/
def quittingAnchoredRenewalLabel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (who : ι) (phase : Fin m) : Label :=
  ⟨⊥, hazard phase * reward (quittingSingletonTerminal (w phase)) who, 1 - hazard phase⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem slope_quittingAnchoredRenewalLabel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (who : ι) (phase : Fin m) :
    (quittingAnchoredRenewalLabel reward w hazard who phase).slope = 1 - hazard phase := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem apply_quittingAnchoredRenewalLabel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (who : ι) (phase : Fin m) (x : ℝ) :
    (quittingAnchoredRenewalLabel reward w hazard who phase).apply x =
      hazard phase * reward (quittingSingletonTerminal (w phase)) who +
        (1 - hazard phase) * x :=
  Label.apply_mk_bot _ _ x

omit [Fintype ι] [DecidableEq ι] in
theorem slope_quittingAnchoredRenewalLabel_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) {hazard : Fin m → ℝ} (h1 : ∀ k, hazard k ≤ 1) (who : ι)
    (phase : Fin m) :
    0 ≤ (quittingAnchoredRenewalLabel reward w hazard who phase).slope := by
  simpa using sub_nonneg.mpr (h1 phase)

/-- The on-path values at one fixed spectator coordinate are an exact section
of the renewal transport. -/
theorem isSection_quittingAnchoredRenewalTransport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (h0 : ∀ k, 0 ≤ hazard k)
    (h1 : ∀ k, hazard k ≤ 1) (who : ι) :
    (toTransport (quittingAnchoredRenewalGraph m)
        (quittingAnchoredRenewalLabel reward w hazard who)).IsSection
      fun phase ↦ quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase who := by
  intro phase
  show (quittingAnchoredRenewalLabel reward w hazard who phase).apply
      (quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 (finRotate m phase) who) =
        quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase who
  rw [apply_quittingAnchoredRenewalLabel]
  exact (quittingAnchoredCyclicOnPathValue_renewal reward w hazard h0 h1 phase who).symm

/-- The same on-path values form a lax section of the renewal labelling. -/
theorem isLaxSection_quittingAnchoredRenewalLabel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (h0 : ∀ k, 0 ≤ hazard k)
    (h1 : ∀ k, hazard k ≤ 1) (who : ι) :
    IsLaxSection (quittingAnchoredRenewalGraph m)
      (quittingAnchoredRenewalLabel reward w hazard who)
      fun phase ↦ quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase who :=
  fun phase ↦
    (isSection_quittingAnchoredRenewalTransport reward w hazard h0 h1 who phase).le

end GameTheory

end
