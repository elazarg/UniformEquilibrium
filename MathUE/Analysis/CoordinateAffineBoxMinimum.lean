import MathUE.Analysis.LowerBoxBoundarySmoothDrift
import MathUE.Probability.FiniteIndependentMixture
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! # Box minima of coordinate-affine functions

Coordinate-affine functions attain box minima at vertices. An interior box
minimum forces global constancy, without a continuity or derivative premise.
-/

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

private theorem IsCoordinateAffine.eq_const_of_eq_on_vertices
    {function : (ι → ℝ) → ℝ} (haffine : IsCoordinateAffine function)
    (lower upper : ι → ℝ) (hwidth : ∀ i, lower i < upper i) (value : ℝ)
    (hvertices : ∀ vertex : ι → ℝ,
      (∀ i, vertex i = lower i ∨ vertex i = upper i) → function vertex = value) :
    ∀ point, function point = value := by
  have hstep : ∀ active : Finset ι, ∀ point : ι → ℝ,
      (∀ i, i ∉ active → point i = lower i ∨ point i = upper i) →
        function point = value := by
    intro active
    induction active using Finset.induction_on with
    | empty =>
        intro point hpoint
        exact hvertices point (fun i => hpoint i (by simp))
    | @insert i active hnot ih =>
        intro point hpoint
        have hendpoint (endpoint : ℝ)
            (hend : endpoint = lower i ∨ endpoint = upper i) :
            function (Function.update point i endpoint) = value := by
          apply ih
          intro j hj
          by_cases heq : j = i
          · subst j
            simpa only [Function.update_self] using hend
          · simpa only [Function.update_of_ne heq] using
              hpoint j (by simp only [Finset.mem_insert, not_or]; exact ⟨heq, hj⟩)
        have hupper := hendpoint (upper i) (Or.inr rfl)
        have hlower := hendpoint (lower i) (Or.inl rfl)
        let weight := (upper i - point i) / (upper i - lower i)
        have hvalue : (1 - weight) * upper i + weight * lower i = point i := by
          dsimp [weight]
          field_simp [ne_of_gt (sub_pos.mpr (hwidth i))]
          ring
        have hinterpolate := haffine.update_interpolate point i
          (lower i) (upper i) weight
        rw [hvalue, Function.update_eq_self, hupper, hlower] at hinterpolate
        calc
          function point = (1 - weight) * value + weight * value := hinterpolate
          _ = value := by ring
  intro point
  exact hstep Finset.univ point (by simp)

/-- An interior minimum on a box forces a coordinate-affine function to be globally constant. -/
theorem IsCoordinateAffine.eq_const_of_isMinOn_box
    {function : (ι → ℝ) → ℝ} (haffine : IsCoordinateAffine function)
    (lower upper minimum : ι → ℝ)
    (hlower : ∀ i, lower i < minimum i) (hupper : ∀ i, minimum i < upper i)
    (hmin : IsMinOn function (Set.Icc lower upper) minimum) :
    ∀ point, function point = function minimum := by
  classical
  let weight : ι → ℝ := fun i => (upper i - minimum i) / (upper i - lower i)
  have hwidth (i : ι) : lower i < upper i := (hlower i).trans (hupper i)
  have hweightPos (i : ι) : 0 < weight i :=
    div_pos (sub_pos.mpr (hupper i)) (sub_pos.mpr (hwidth i))
  have hweightLt (i : ι) : weight i < 1 := by
    dsimp [weight]
    apply (div_lt_one (sub_pos.mpr (hwidth i))).mpr
    linarith [hlower i]
  let laws : ι → GameTheory.Math.Probability.FinDist ℝ := fun i =>
    GameTheory.Math.Probability.FinDist.mix (weight i) (hweightPos i).le
      (hweightLt i).le (GameTheory.Math.Probability.FinDist.pure (lower i))
      (GameTheory.Math.Probability.FinDist.pure (upper i))
  have hbary (i : ι) : (laws i).expect id = minimum i := by
    dsimp [laws]
    rw [GameTheory.Math.Probability.FinDist.expect_mix]
    simp only [GameTheory.Math.Probability.FinDist.expect_pure, id_eq]
    dsimp [weight]
    field_simp [ne_of_gt (sub_pos.mpr (hwidth i))]
    ring
  have haverage : function minimum =
      (GameTheory.Math.Probability.FinDist.pi laws).expect function := by
    have h := GameTheory.Math.Probability.FinDist.expect_pi_eq_of_separatelyAffine
      (fun (_ : ι) (law : GameTheory.Math.Probability.FinDist ℝ) => law.expect id)
      function laws (by
        intro i point law
        obtain ⟨offset, slope, hline⟩ := haffine point i
        rw [hline]
        have hexpand :
            law.expect (fun x => function (Function.update point i x)) =
              offset + slope * law.expect id := by
          simp_rw [hline]
          rw [GameTheory.Math.Probability.FinDist.expect_add,
            GameTheory.Math.Probability.FinDist.expect_const]
          have hmul := law.expect_mul_const id slope
          simpa only [id_eq, mul_comm] using congrArg (offset + ·) hmul
        exact hexpand.symm)
    have hprofile : (fun i => (laws i).expect id) = minimum := funext hbary
    rwa [hprofile] at h
  have hsupport (vertex : ι → ℝ) :
      vertex ∈ (GameTheory.Math.Probability.FinDist.pi laws).support ↔
        ∀ i, vertex i = lower i ∨ vertex i = upper i := by
    rw [GameTheory.Math.Probability.FinDist.mem_support_pi]
    apply forall_congr'
    intro i
    exact GameTheory.Math.Probability.FinDist.mem_support_mix_pure_iff
      (weight i) (hweightPos i).le (hweightLt i).le
      (hweightPos i) (hweightLt i) (lower i) (upper i) (vertex i)
  have hvertices : ∀ vertex : ι → ℝ,
      (∀ i, vertex i = lower i ∨ vertex i = upper i) →
        function vertex = function minimum := by
    intro vertex hvertex
    have hnegative :
        (GameTheory.Math.Probability.FinDist.pi laws).expect (fun x => -function x) =
          -function minimum := by
      have h := (GameTheory.Math.Probability.FinDist.pi laws).expect_mul_const function (-1)
      simpa only [mul_neg_one, ← haverage] using h
    have heq := (GameTheory.Math.Probability.FinDist.pi laws).eq_of_expect_eq_of_le
      (fun x => -function x) (-function minimum) (by
        intro x hx
        apply neg_le_neg
        apply hmin
        have hx' := (hsupport x).mp hx
        constructor <;> intro i
        · rcases hx' i with heq | heq
          · exact heq.ge
          · exact (hwidth i).le.trans_eq heq.symm
        · rcases hx' i with heq | heq
          · exact heq.le.trans (hwidth i).le
          · exact heq.le) hnegative ((hsupport vertex).mpr hvertex)
    exact neg_injective heq
  exact haffine.eq_const_of_eq_on_vertices lower upper hwidth (function minimum) hvertices

/-- A local minimum forces a coordinate-affine function to be globally constant. -/
theorem IsCoordinateAffine.eq_const_of_isLocalMin
    {function : (ι → ℝ) → ℝ} (haffine : IsCoordinateAffine function)
    (minimum : ι → ℝ) (hmin : IsLocalMin function minimum) :
    ∀ point, function point = function minimum := by
  change {point | function minimum ≤ function point} ∈ nhds minimum at hmin
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hmin
  apply haffine.eq_const_of_isMinOn_box
    (fun i => minimum i - radius / 2) (fun i => minimum i + radius / 2) minimum
  · intro i
    linarith
  · intro i
    linarith
  · intro point hpoint
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hradius]
    intro i
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hpoint.1 i, hpoint.2 i]

end Math
