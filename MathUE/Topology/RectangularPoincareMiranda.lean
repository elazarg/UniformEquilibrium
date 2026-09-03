import MathUE.Topology.PoincareMirandaCube

/-!
# Poincare--Miranda on coordinate rectangles

The unit-cube theorem is transported to an arbitrary finite coordinate
rectangle.  A displacement estimate on the symmetric unit cube is also
recorded in the orientation used by interval Newton enclosures.
-/

noncomputable section

open Function Set

namespace Math
namespace Topology

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise affine transport from the unit cube to a rectangle. -/
def rectangularPoint (lower upper y : ι → ℝ) : ι → ℝ :=
  fun coordinate =>
    lower coordinate + (upper coordinate - lower coordinate) * y coordinate

omit [Fintype ι] in
theorem continuous_rectangularPoint (lower upper : ι → ℝ) :
    Continuous (rectangularPoint lower upper) := by
  apply continuous_pi
  intro coordinate
  exact continuous_const.add
    (continuous_const.mul (continuous_apply coordinate))

omit [Fintype ι] in
theorem rectangularPoint_mem_Icc
    {lower upper y : ι → ℝ}
    (hlowerUpper : ∀ coordinate, lower coordinate < upper coordinate)
    (hy : y ∈ Icc (fun _ => 0) (fun _ => 1)) :
    rectangularPoint lower upper y ∈ Icc lower upper := by
  constructor <;> intro coordinate
  · dsimp [rectangularPoint]
    have hwidth : 0 ≤ upper coordinate - lower coordinate :=
      (sub_pos.mpr (hlowerUpper coordinate)).le
    nlinarith [mul_nonneg hwidth (hy.1 coordinate)]
  · dsimp [rectangularPoint]
    have hwidth : 0 ≤ upper coordinate - lower coordinate :=
      (sub_pos.mpr (hlowerUpper coordinate)).le
    have hmul := mul_le_mul_of_nonneg_left (hy.2 coordinate) hwidth
    nlinarith

/-- Poincare--Miranda on a coordinate rectangle, for a field which is
negative on every lower face and positive on every upper face. -/
theorem exists_rectangular_zero_of_strict_face_signs
    (lower upper : ι → ℝ) (field : (ι → ℝ) → ι → ℝ)
    (hlowerUpper : ∀ coordinate, lower coordinate < upper coordinate)
    (hfield : Continuous field)
    (hlower : ∀ x ∈ Icc lower upper, ∀ coordinate,
      x coordinate = lower coordinate → field x coordinate < 0)
    (hupper : ∀ x ∈ Icc lower upper, ∀ coordinate,
      x coordinate = upper coordinate → 0 < field x coordinate) :
    ∃ x ∈ Icc lower upper,
      (∀ coordinate,
        lower coordinate < x coordinate ∧ x coordinate < upper coordinate) ∧
      ∀ coordinate, field x coordinate = 0 := by
  let pulledBack : (ι → ℝ) → ι → ℝ :=
    fun y coordinate => -field (rectangularPoint lower upper y) coordinate
  have hpulledBack : Continuous pulledBack := by
    exact continuous_neg.comp
      (hfield.comp (continuous_rectangularPoint lower upper))
  have hpulledBackLower :
      ∀ y ∈ Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1),
        ∀ coordinate, y coordinate = 0 → 0 < pulledBack y coordinate := by
    intro y hy coordinate hcoordinate
    have hmem := rectangularPoint_mem_Icc hlowerUpper hy
    have hface : rectangularPoint lower upper y coordinate =
        lower coordinate := by
      simp [rectangularPoint, hcoordinate]
    exact neg_pos.mpr (hlower _ hmem coordinate hface)
  have hpulledBackUpper :
      ∀ y ∈ Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1),
        ∀ coordinate, y coordinate = 1 → pulledBack y coordinate < 0 := by
    intro y hy coordinate hcoordinate
    have hmem := rectangularPoint_mem_Icc hlowerUpper hy
    have hface : rectangularPoint lower upper y coordinate =
        upper coordinate := by
      simp [rectangularPoint, hcoordinate]
    exact neg_lt_zero.mpr (hupper _ hmem coordinate hface)
  obtain ⟨y, hy, hyInterior, hyZero⟩ :=
    exists_cube_zero_interior_of_strict_opposite_face_signs
      pulledBack hpulledBack hpulledBackLower hpulledBackUpper
  refine ⟨rectangularPoint lower upper y,
    rectangularPoint_mem_Icc hlowerUpper hy, ?_, ?_⟩
  · intro coordinate
    dsimp [rectangularPoint]
    have hwidth : 0 < upper coordinate - lower coordinate :=
      sub_pos.mpr (hlowerUpper coordinate)
    constructor
    · nlinarith [mul_pos hwidth (hyInterior coordinate).1]
    · have hmul := mul_lt_mul_of_pos_left
        (hyInterior coordinate).2 hwidth
      nlinarith
  · intro coordinate
    have hzero := hyZero coordinate
    dsimp [pulledBack] at hzero
    linarith

/-- A continuous field on the symmetric unit cube has an interior zero when
the displacement from the identity is uniformly bounded by a constant
strictly below one. -/
theorem exists_symmetric_unit_cube_zero_of_displacement_bound
    (field : (ι → ℝ) → ι → ℝ) (bound : ℝ)
    (hfield : Continuous field) (hbound : bound < 1)
    (hdisplacement :
      ∀ x ∈ Icc (fun _ : ι => (-1 : ℝ)) (fun _ => 1),
        ∀ coordinate, |x coordinate - field x coordinate| ≤ bound) :
    ∃ x ∈ Icc (fun _ : ι => (-1 : ℝ)) (fun _ => 1),
      (∀ coordinate, -1 < x coordinate ∧ x coordinate < 1) ∧
      ∀ coordinate, field x coordinate = 0 := by
  apply exists_rectangular_zero_of_strict_face_signs
    (fun _ : ι => (-1 : ℝ)) (fun _ => 1) field
  · intro coordinate
    norm_num
  · exact hfield
  · intro x hx coordinate hface
    have habs := hdisplacement x hx coordinate
    have hge := (abs_le.mp habs).1
    rw [hface] at hge
    linarith
  · intro x hx coordinate hface
    have habs := hdisplacement x hx coordinate
    have hle := (abs_le.mp habs).2
    rw [hface] at hle
    linarith

end Topology
end Math

end
