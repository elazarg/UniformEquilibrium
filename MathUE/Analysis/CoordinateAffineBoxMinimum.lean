import MathUE.Analysis.LowerBoxBoundarySmoothDrift

/-! # Coordinate-affine functions attain box minima at vertices -/

noncomputable section

namespace Math

open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Affinity along every coordinate line, without restricting interaction order. -/
def IsCoordinateAffine (function : (ι → ℝ) → ℝ) : Prop :=
  ∀ point coordinate, ∃ offset slope : ℝ, ∀ value : ℝ,
    function (Function.update point coordinate value) = offset + slope * value

omit [Fintype ι] in
/-- Arbitrary endpoint interpolation on a single coordinate line. -/
theorem IsCoordinateAffine.update_interpolate
    {function : (ι → ℝ) → ℝ} (haffine : IsCoordinateAffine function)
    (point : ι → ℝ) (coordinate : ι) (lower upper weight : ℝ) :
    function (Function.update point coordinate ((1 - weight) * upper + weight * lower)) =
      (1 - weight) * function (Function.update point coordinate upper) +
        weight * function (Function.update point coordinate lower) := by
  obtain ⟨offset, slope, hline⟩ := haffine point coordinate
  rw [hline, hline, hline]
  ring

/-- A coordinate finite difference is exactly its derivative times displacement. -/
theorem IsCoordinateAffine.update_sub_eq_derivative
    {function : (ι → ℝ) → ℝ} (haffine : IsCoordinateAffine function)
    (point : ι → ℝ) (derivative : (ι → ℝ) →L[ℝ] ℝ)
    (hdiff : HasFDerivAt function derivative point) (coordinate : ι) (value : ℝ) :
    function (Function.update point coordinate value) - function point =
      (value - point coordinate) * derivative (Pi.single coordinate 1) := by
  obtain ⟨offset, slope, hline⟩ := haffine point coordinate
  have hfunction : (fun value => function (Function.update point coordinate value)) =
      (fun value => offset + slope * value) := funext hline
  have hlineDerivative : HasDerivAt
      (fun value => function (Function.update point coordinate value)) slope
      (point coordinate) := by
    rw [hfunction]
    simpa using ((hasDerivAt_id (point coordinate)).const_mul slope).const_add offset
  have hdiff' : HasFDerivAt function derivative
      (Function.update point coordinate (point coordinate)) := by simpa using hdiff
  have hcomposition := hdiff'.comp_hasDerivAt (point coordinate)
    (hasDerivAt_update point coordinate (point coordinate))
  have hslope : derivative (Pi.single coordinate 1) = slope :=
    hcomposition.unique hlineDerivative
  have hself := hline (point coordinate)
  simp only [Function.update_eq_self] at hself
  rw [hslope, hline value, hself]
  ring

omit [Fintype ι] in
/-- Moving one coordinate to an endpoint can never increase a coordinate-affine
function. The endpoint choice is produced from the actual affine slope. -/
theorem IsCoordinateAffine.exists_endpoint_le
    {function : (ι → ℝ) → ℝ} (haffine : IsCoordinateAffine function)
    (point : ι → ℝ) (coordinate : ι) (lower upper : ℝ)
    (hpoint : point coordinate ∈ Set.Icc lower upper) :
    ∃ endpoint, (endpoint = lower ∨ endpoint = upper) ∧
      function (Function.update point coordinate endpoint) ≤ function point := by
  obtain ⟨offset, slope, hline⟩ := haffine point coordinate
  have hself := hline (point coordinate)
  simp only [Function.update_eq_self] at hself
  by_cases hslope : 0 ≤ slope
  · refine ⟨lower, Or.inl rfl, ?_⟩
    rw [hline, hself]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpoint.1 hslope)
  · refine ⟨upper, Or.inr rfl, ?_⟩
    rw [hline, hself]
    exact add_le_add le_rfl (mul_le_mul_of_nonpos_left hpoint.2 (le_of_not_ge hslope))

/-- Every supplied global box minimum can be moved to a vertex while preserving
its value. No strictness or derivative assumption is needed. -/
theorem IsCoordinateAffine.exists_vertex_minimum
    {function : (ι → ℝ) → ℝ} (haffine : IsCoordinateAffine function)
    (lower upper minimum : ι → ℝ)
    (hminimum : minimum ∈ Set.Icc lower upper)
    (hmin : IsMinOn function (Set.Icc lower upper) minimum) :
    ∃ vertex ∈ Set.Icc lower upper,
      (∀ coordinate, vertex coordinate = lower coordinate ∨ vertex coordinate = upper coordinate) ∧
      IsMinOn function (Set.Icc lower upper) vertex := by
  have hwidth : lower ≤ upper := hminimum.1.trans hminimum.2
  have hstep : ∀ coordinates : Finset ι, ∃ point ∈ Set.Icc lower upper,
      function point = function minimum ∧
      (∀ coordinate ∈ coordinates,
        point coordinate = lower coordinate ∨ point coordinate = upper coordinate) := by
    intro coordinates
    induction coordinates using Finset.induction_on with
    | empty => exact ⟨minimum, hminimum, rfl, by simp⟩
    | @insert coordinate coordinates hnew hinduction =>
      obtain ⟨point, hpoint, hvalue, hvertices⟩ := hinduction
      obtain ⟨endpoint, hendpoint, hendpointValue⟩ :=
        haffine.exists_endpoint_le point coordinate (lower coordinate) (upper coordinate)
          ⟨hpoint.1 coordinate, hpoint.2 coordinate⟩
      let next := Function.update point coordinate endpoint
      have hnext : next ∈ Set.Icc lower upper := by
        constructor <;> intro other
        · by_cases heq : other = coordinate
          · subst other
            rcases hendpoint with rfl | rfl <;> simp [next, hwidth coordinate]
          · simpa [next, heq] using hpoint.1 other
        · by_cases heq : other = coordinate
          · subst other
            rcases hendpoint with rfl | rfl <;> simp [next, hwidth coordinate]
          · simpa [next, heq] using hpoint.2 other
      have hnextValue : function next = function minimum :=
        le_antisymm (hendpointValue.trans hvalue.le) (hmin hnext)
      refine ⟨next, hnext, hnextValue, ?_⟩
      intro other hother
      rcases Finset.mem_insert.mp hother with heq | hother
      · subst other
        simpa [next] using hendpoint
      · have hne : other ≠ coordinate := by
          intro heq
          subst other
          exact hnew hother
        simpa [next, hne] using hvertices other hother
  obtain ⟨vertex, hvertex, hvalue, hvertices⟩ := hstep Finset.univ
  refine ⟨vertex, hvertex, fun coordinate => hvertices coordinate (Finset.mem_univ _), ?_⟩
  intro point hpoint
  rw [hvalue]
  exact hmin hpoint

end Math
