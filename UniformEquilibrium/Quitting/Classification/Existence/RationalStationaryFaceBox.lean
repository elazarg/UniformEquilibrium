/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.ConditionalFaceGap

/-!
# Rational stationary face boxes

This file supplies the generic closure interface needed by exact rational
face calculations.  A continuous, possibly preconditioned vector field has
strict opposite signs on the faces of a rational box.  Poincare--Miranda
produces an interior zero.  A supplied zero-transport proof converts that zero
to the genuine quitting face numerators, after which the existing stationary
all-behavior compiler applies.

The interface does not prove the face signs or the zero-transport statement
for any particular reward table.
-/

noncomputable section

namespace GameTheory

open Math.Topology Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Cast the lower endpoint of a rational coordinate box to reals. -/
def quittingRationalBoxLower (lower : ι → ℚ) : ι → ℝ :=
  fun who => lower who

/-- Cast the upper endpoint of a rational coordinate box to reals. -/
def quittingRationalBoxUpper (upper : ι → ℚ) : ι → ℝ :=
  fun who => upper who

/-- Executable interface for a rational box and a continuous transformed
face field.  `zero_to_numerator` is the exact algebraic bridge (for example,
invertibility of a rational preconditioning matrix) back to the actual
quitting face numerators. -/
structure QuittingRationalStationaryFaceBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  lower : ι → ℚ
  upper : ι → ℚ
  field : (ι → ℝ) → ι → ℝ
  lower_nonneg : ∀ who, 0 ≤ lower who
  upper_le_one : ∀ who, upper who ≤ 1
  lower_lt_upper : ∀ who, lower who < upper who
  continuous_field : Continuous field
  lower_face_sign : ∀ hazard ∈
      Icc (quittingRationalBoxLower lower) (quittingRationalBoxUpper upper),
    ∀ who, hazard who = quittingRationalBoxLower lower who →
      0 < field hazard who
  upper_face_sign : ∀ hazard ∈
      Icc (quittingRationalBoxLower lower) (quittingRationalBoxUpper upper),
    ∀ who, hazard who = quittingRationalBoxUpper upper who →
      field hazard who < 0
  zero_to_numerator : ∀ hazard ∈
      Icc (quittingRationalBoxLower lower) (quittingRationalBoxUpper upper),
    (∀ who, field hazard who = 0) → ∀ who,
      quittingFaceNumerator (weightOfReward reward) hazard who = 0

namespace QuittingRationalStationaryFaceBox

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

private theorem real_gap
    (box : QuittingRationalStationaryFaceBox reward) (who : ι) :
    quittingRationalBoxLower box.lower who <
      quittingRationalBoxUpper box.upper who := by
  change ((box.lower who : ℚ) : ℝ) < ((box.upper who : ℚ) : ℝ)
  exact_mod_cast box.lower_lt_upper who

private theorem affine_mem
    (box : QuittingRationalStationaryFaceBox reward)
    {point : ι → ℝ} (hpoint : point ∈ Icc (fun _ => 0) (fun _ => 1)) :
    affineHazardBox (quittingRationalBoxLower box.lower)
        (quittingRationalBoxUpper box.upper) point ∈
      Icc (quittingRationalBoxLower box.lower)
        (quittingRationalBoxUpper box.upper) := by
  constructor
  · intro who
    unfold affineHazardBox
    exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr (box.real_gap who).le) (hpoint.1 who))
  · intro who
    unfold affineHazardBox
    nlinarith [hpoint.2 who, box.real_gap who]

/-- Strict rational-box face signs produce an interior zero of the transformed
field and hence an exact zero of every quitting face numerator. -/
theorem exists_faceNumeratorZero
    (box : QuittingRationalStationaryFaceBox reward) :
    ∃ hazard : ι → ℝ,
      (∀ who, quittingRationalBoxLower box.lower who < hazard who) ∧
        (∀ who, hazard who < quittingRationalBoxUpper box.upper who) ∧
          ∀ who, quittingFaceNumerator
            (weightOfReward reward) hazard who = 0 := by
  let pullback : (ι → ℝ) → ι → ℝ := fun point =>
    box.field (affineHazardBox (quittingRationalBoxLower box.lower)
      (quittingRationalBoxUpper box.upper) point)
  have hpullback : Continuous pullback :=
    box.continuous_field.comp
      (continuous_affineHazardBox _ _)
  obtain ⟨point, hpoint, hinterior, hzero⟩ :=
    exists_cube_zero_interior_of_strict_opposite_face_signs
      pullback hpullback
      (fun point hpoint who hface => by
        apply box.lower_face_sign _ (box.affine_mem hpoint) who
        simp [affineHazardBox, hface])
      (fun point hpoint who hface => by
        apply box.upper_face_sign _ (box.affine_mem hpoint) who
        simp [affineHazardBox, hface])
  let hazard := affineHazardBox (quittingRationalBoxLower box.lower)
    (quittingRationalBoxUpper box.upper) point
  refine ⟨hazard, fun who => ?_, fun who => ?_, ?_⟩
  · dsimp [hazard, affineHazardBox]
    exact lt_add_of_pos_right _
      (mul_pos (sub_pos.mpr (box.real_gap who)) (hinterior who).1)
  · dsimp [hazard, affineHazardBox]
    nlinarith [box.real_gap who, (hinterior who).2]
  · apply box.zero_to_numerator hazard (box.affine_mem hpoint)
    simpa only [pullback, hazard] using hzero

/-- The rational-box zero feeds the existing full behavioral stationary
certificate. -/
theorem nonempty_stationaryCertificate [Nontrivial ι]
    (box : QuittingRationalStationaryFaceBox reward) :
    Nonempty (QuittingConditionalFaceGapStationaryCertificate reward
      (quittingRationalBoxLower box.lower)
      (quittingRationalBoxUpper box.upper)) := by
  obtain ⟨hazard, hlower, hupper, hzero⟩ := box.exists_faceNumeratorZero
  refine ⟨quittingConditionalFaceGapStationaryCertificateOfFaceNumeratorZero
    reward (quittingRationalBoxLower box.lower)
      (quittingRationalBoxUpper box.upper) hazard ?_ ?_
        hlower (fun who => (hupper who).le) hzero⟩
  · intro who
    change (0 : ℝ) ≤ ((box.lower who : ℚ) : ℝ)
    exact_mod_cast box.lower_nonneg who
  · intro who
    change ((box.upper who : ℚ) : ℝ) ≤ (1 : ℝ)
    exact_mod_cast box.upper_le_one who

/-- In particular, the rational face box supplies a fixed uniform-equilibrium
payoff. -/
theorem exists_uniformEquilibriumPayoff [Nontrivial ι]
    (box : QuittingRationalStationaryFaceBox reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨certificate⟩ := box.nonempty_stationaryCertificate
  exact ⟨certificate.value, certificate.uniformEquilibriumPayoff⟩

end QuittingRationalStationaryFaceBox

end GameTheory
