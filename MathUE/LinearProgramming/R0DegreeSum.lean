import MathUE.LinearProgramming.R0Degree
import MathUE.LinearProgramming.RootDegreeSum

/-!
# Computing R0 degree from the actual roots at one regular test offset

R0 supplies a single large scalar chart containing every test root. The
existing local root-sum theorem applies on its central region. The injective
chart and its explicit inverse transport the entire finite root set back to
ambient LCP coordinates, retaining both its exact membership and its signed
sum. No finiteness premise or chosen subset of roots is supplied.

The root set may be empty. Dimension zero is included: its empty-coordinate
vector is represented in the singleton cube, and its principal determinant
is one.
-/

noncomputable section

namespace Math.LinearProgramming

open Set Math.Topology

variable {n : ℕ}

private theorem exists_central_cubePoint_of_nonneg_lt_half
    (radius : ℝ) (hradius : 0 < radius) (root : Fin n → ℝ)
    (hnonneg : ∀ who, 0 ≤ root who) (hbound : ∀ who, root who < radius / 2) :
    ∃ point : UnitCube (Fin n), point ∈ diagonalCentralRegion n ∧
      rectangularCubePoint (fun _ => 0 - radius) (fun _ => 0 + radius) point = root := by
  let coordinate : Fin n → ℝ := fun who => (root who + radius) / (2 * radius)
  have hden : 0 < 2 * radius := by positivity
  have hcentral (who : Fin n) : 1 / 4 < coordinate who ∧ coordinate who < 3 / 4 := by
    dsimp only [coordinate]
    constructor
    · apply (lt_div_iff₀ hden).mpr
      nlinarith [hnonneg who]
    · apply (div_lt_iff₀ hden).mpr
      nlinarith [hbound who]
  let point : UnitCube (Fin n) := fun who => ⟨coordinate who, by
    constructor <;> linarith [(hcentral who).1, (hcentral who).2]⟩
  refine ⟨point, hcentral, ?_⟩
  funext who
  dsimp [rectangularCubePoint, rectangularPoint, point, coordinate]
  field_simp [hradius.ne']; ring

/-- One regular test offset computes the canonical R0 integer by a finite sum
over exactly all actual standard-LCP roots. Empty root sets and dimension
zero are allowed, and regularity is imposed only at this test offset. -/
theorem exists_finset_r0Degree_eq_sum_sign_det
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix)
    (offset : Fin n → ℝ)
    (hstrict : ∀ root, IsStandardLCPSolution matrix offset root →
      ∀ who, root who = 0 → 0 < lcpResidual matrix offset root who)
    (hnonsingular : ∀ root, IsStandardLCPSolution matrix offset root →
      (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0) :
    ∃ roots : Finset (Fin n → ℝ),
      (∀ root, root ∈ roots ↔ IsStandardLCPSolution matrix offset root) ∧
      r0Degree matrix hR0 =
        ∑ root ∈ roots,
          (SignType.sign (matrix.toSquareBlockProp (fun who => 0 < root who)).det : ℤ) := by
  classical
  obtain ⟨radius, hradius, hfamily⟩ :=
    exists_radius_lcpMinBoxProblem_localDegree_eq_r0Degree matrix hR0
      (∑ who, |offset who|)
  obtain ⟨hisolating, hbound, hdegree⟩ := hfamily offset (fun who =>
    Finset.single_le_sum (fun coordinate _ => abs_nonneg (offset coordinate))
      (Finset.mem_univ who))
  let actual := lcpMinBoxProblem matrix offset 0 radius hradius
  let chart := rectangularCubePoint (fun _ : Fin n => 0 - radius) (fun _ => 0 + radius)
  have hsource (point : UnitCube (Fin n)) (hpoint : point ∈ diagonalCentralRegion n) :
      actual.IsSolution point ↔ IsStandardLCPSolution matrix offset (chart point) := by
    have hinterior (who : Fin n) : 0 < (point who : ℝ) ∧ (point who : ℝ) < 1 := by
      have h := hpoint who
      constructor <;> linarith
    have hequivalence := actual.isSolution_iff_gain_eq_zero_of_coordinateInterior
      point hinterior
    have hgain : actual.gain point = -lcpMinMap matrix offset (chart point) := rfl
    rw [hgain, neg_eq_zero, lcpMinMap_eq_zero_iff] at hequivalence
    exact hequivalence
  have hchart : Function.Injective chart := by
    intro first second hequal
    funext who
    apply Subtype.ext
    have hcoordinate := congrFun hequal who
    dsimp [chart, rectangularCubePoint, rectangularPoint] at hcoordinate
    have hwidth : (0 + radius) - (0 - radius) ≠ 0 := by linarith
    exact mul_left_cancel₀ hwidth (add_left_cancel hcoordinate)
  obtain ⟨cubeRoots, hcubeRoots, hsum⟩ :=
    exists_finset_lcpMinBoxProblem_localDegree_eq_sum_sign_det matrix offset 0
      radius hradius (diagonalCentralRegion n) hisolating (fun _ hroot => hroot.2)
      (fun point hpoint =>
        hstrict (chart point) ((hsource point hpoint.2).mp hpoint.1))
      (fun point hpoint =>
        hnonsingular (chart point) ((hsource point hpoint.2).mp hpoint.1))
  have hmem (point : UnitCube (Fin n)) :
      point ∈ cubeRoots ↔ actual.IsSolution point ∧ point ∈ diagonalCentralRegion n := by
    change point ∈ (↑cubeRoots : Set (UnitCube (Fin n))) ↔ _
    rw [hcubeRoots]
    rfl
  refine ⟨cubeRoots.image chart, ?_, ?_⟩
  · intro root
    constructor
    · intro hroot
      obtain ⟨point, hpoint, rfl⟩ := Finset.mem_image.mp hroot
      have hpoint' := (hmem point).mp hpoint
      exact (hsource point hpoint'.2).mp hpoint'.1
    · intro hroot
      obtain ⟨point, hpoint, hchartPoint⟩ :=
        exists_central_cubePoint_of_nonneg_lt_half radius hradius root
          hroot.weight_nonneg (hbound root hroot)
      apply Finset.mem_image.mpr
      refine ⟨point, (hmem point).mpr ⟨?_, hpoint⟩, hchartPoint⟩
      apply (hsource point hpoint).mpr
      simpa only [chart, hchartPoint] using hroot
  · rw [Finset.sum_image]
    · exact hdegree.symm.trans hsum
    · intro first _hfirst second _hsecond hequal
      exact hchart hequal

end Math.LinearProgramming
