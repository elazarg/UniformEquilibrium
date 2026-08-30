/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import UniformEquilibrium.Quitting.Classification.Existence.RationalStationaryFaceBox

/-!
# Centered error certificates for stationary face boxes

This module packages the common table-verification seam behind a rational
Poincare--Miranda calculation.  An oriented transformed field is compared on
the whole box with the diagonal model `center - hazard`.  If the uniform
coordinate error is smaller than the corresponding half-width by a positive
margin, the required strict opposite face signs follow automatically.

The certificate still requires an exact zero-to-numerator bridge.  It does
not assert that a table-specific interval or derivative calculation exists.
-/

noncomputable section

namespace GameTheory

open Math.Topology Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Lower endpoint of a centered rational hazard box. -/
def quittingCenteredRationalBoxLower
    (center halfWidth : ι → ℚ) : ι → ℚ :=
  fun who => center who - halfWidth who

/-- Upper endpoint of a centered rational hazard box. -/
def quittingCenteredRationalBoxUpper
    (center halfWidth : ι → ℚ) : ι → ℚ :=
  fun who => center who + halfWidth who

/-- A whole-box error certificate reducing transformed-field face signs to
one diagonal approximation bound.  The field is oriented so that its model
is `center - hazard`: positive on lower faces and negative on upper faces. -/
structure QuittingCenteredStationaryFaceCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  center : ι → ℚ
  halfWidth : ι → ℚ
  margin : ι → ℚ
  field : (ι → ℝ) → ι → ℝ
  lower_nonneg : ∀ who, 0 ≤ center who - halfWidth who
  upper_le_one : ∀ who, center who + halfWidth who ≤ 1
  halfWidth_pos : ∀ who, 0 < halfWidth who
  margin_pos : ∀ who, 0 < margin who
  continuous_field : Continuous field
  diagonal_error : ∀ hazard ∈
      Icc
        (quittingRationalBoxLower
          (quittingCenteredRationalBoxLower center halfWidth))
        (quittingRationalBoxUpper
          (quittingCenteredRationalBoxUpper center halfWidth)),
    ∀ who,
      |field hazard who - ((center who : ℝ) - hazard who)| ≤
        (halfWidth who : ℝ) - margin who
  zero_to_numerator : ∀ hazard ∈
      Icc
        (quittingRationalBoxLower
          (quittingCenteredRationalBoxLower center halfWidth))
        (quittingRationalBoxUpper
          (quittingCenteredRationalBoxUpper center halfWidth)),
    (∀ who, field hazard who = 0) → ∀ who,
      quittingFaceNumerator (weightOfReward reward) hazard who = 0

namespace QuittingCenteredStationaryFaceCertificate

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A centered diagonal-error certificate supplies the generic rational face
box expected by the stationary closure compiler. -/
def toRationalStationaryFaceBox
    (certificate : QuittingCenteredStationaryFaceCertificate reward) :
    QuittingRationalStationaryFaceBox reward where
  lower := quittingCenteredRationalBoxLower
    certificate.center certificate.halfWidth
  upper := quittingCenteredRationalBoxUpper
    certificate.center certificate.halfWidth
  field := certificate.field
  lower_nonneg := certificate.lower_nonneg
  upper_le_one := certificate.upper_le_one
  lower_lt_upper := by
    intro who
    dsimp only [quittingCenteredRationalBoxLower,
      quittingCenteredRationalBoxUpper]
    linarith [certificate.halfWidth_pos who]
  continuous_field := certificate.continuous_field
  lower_face_sign := by
    intro hazard hhazard who hface
    have herror := certificate.diagonal_error hazard hhazard who
    have hlower := (abs_le.mp herror).1
    change hazard who =
      ((certificate.center who - certificate.halfWidth who : ℚ) : ℝ) at hface
    have hcast :
        ((certificate.center who - certificate.halfWidth who : ℚ) : ℝ) =
          (certificate.center who : ℝ) - certificate.halfWidth who := by
      norm_num
    rw [hcast] at hface
    rw [hface] at hlower
    have hmargin : 0 < (certificate.margin who : ℝ) := by
      exact_mod_cast certificate.margin_pos who
    linarith
  upper_face_sign := by
    intro hazard hhazard who hface
    have herror := certificate.diagonal_error hazard hhazard who
    have hupper := (abs_le.mp herror).2
    change hazard who =
      ((certificate.center who + certificate.halfWidth who : ℚ) : ℝ) at hface
    have hcast :
        ((certificate.center who + certificate.halfWidth who : ℚ) : ℝ) =
          (certificate.center who : ℝ) + certificate.halfWidth who := by
      norm_num
    rw [hcast] at hface
    rw [hface] at hupper
    have hmargin : 0 < (certificate.margin who : ℝ) := by
      exact_mod_cast certificate.margin_pos who
    linarith
  zero_to_numerator := certificate.zero_to_numerator

/-- The centered error certificate therefore compiles to an exact stationary
all-behavior certificate. -/
theorem nonempty_stationaryCertificate [Nontrivial ι]
    (certificate : QuittingCenteredStationaryFaceCertificate reward) :
    Nonempty (QuittingConditionalFaceGapStationaryCertificate reward
      (quittingRationalBoxLower
        (quittingCenteredRationalBoxLower
          certificate.center certificate.halfWidth))
      (quittingRationalBoxUpper
        (quittingCenteredRationalBoxUpper
          certificate.center certificate.halfWidth))) :=
  certificate.toRationalStationaryFaceBox.nonempty_stationaryCertificate

/-- Literal uniform-payoff consumer for a supplied centered certificate. -/
theorem exists_uniformEquilibriumPayoff [Nontrivial ι]
    (certificate : QuittingCenteredStationaryFaceCertificate reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  certificate.toRationalStationaryFaceBox.exists_uniformEquilibriumPayoff

end QuittingCenteredStationaryFaceCertificate

end GameTheory
