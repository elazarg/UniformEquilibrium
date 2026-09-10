import MathUE.Topology.KuhnFloorCompleteSimplex
import Research.Topology.KuhnExternalCubePrism

/-! # Floor-pulled versus actual fine box labels -/

noncomputable section

namespace Math

open Classical

variable {n : ℕ}

/-- The coarse box label pulled to the factor-refined grid by coordinate floor. -/
def boxComplementarityFloorPullbackBoundaryLabeling
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k) :
    KuhnCubeBoundaryLabeling n (p * k) :=
  Math.SpernerCube.toKuhnCubeBoundaryLabeling
    (floorPullbackSpernerCube
      (boxComplementaritySpernerCube problem p hp) k hk)

@[simp] theorem boxComplementarityFloorPullbackBoundaryLabeling_label
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (vertex : Fin n → Fin (p * k + 1)) :
    (boxComplementarityFloorPullbackBoundaryLabeling
      problem p k hp hk).label vertex =
      boxComplementarityFinLabel problem p
        (fun who ↦ kuhnFloorCoordinate p k (vertex who)) := by
  rfl

/-- The discrete prism comparing the floor-pulled coarse labels with the
actual labels of the same problem on the fine grid. -/
def boxComplementarityFloorRefinementPrism
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k) :
    KuhnPrismSpatialBoundaryLabeling n (p * k) (Nat.mul_pos hp hk) :=
  externalCubeLabelPrism (Nat.mul_pos hp hk)
    (boxComplementarityFloorPullbackBoundaryLabeling problem p k hp hk)
    (boxComplementarityKuhnCubeBoundaryLabeling
      problem (p * k) (Nat.mul_pos hp hk))

@[simp] theorem boxComplementarityFloorRefinementPrism_left_end
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (vertex : Fin n → Fin (p * k + 1)) :
    (boxComplementarityFloorRefinementPrism problem p k hp hk).label
      (kuhnPrismEndVertex (p * k) (Nat.mul_pos hp hk) 0 vertex) =
        boxComplementarityFinLabel problem p
          (fun who ↦ kuhnFloorCoordinate p k (vertex who)) := by
  rw [boxComplementarityFloorRefinementPrism,
    externalCubeLabelPrism_left_end]
  rfl

@[simp] theorem boxComplementarityFloorRefinementPrism_right_end
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (vertex : Fin n → Fin (p * k + 1)) :
    (boxComplementarityFloorRefinementPrism problem p k hp hk).label
      (kuhnPrismEndVertex (p * k) (Nat.mul_pos hp hk)
        (Fin.last (p * k)) vertex) =
          boxComplementarityFinLabel problem (p * k) vertex := by
  rw [boxComplementarityFloorRefinementPrism,
    externalCubeLabelPrism_right_end]
  rfl

/-- Flooring any fine-grid point changes its represented unit-cube point by
at most one coarse mesh width, independently of the refinement factor. -/
theorem dist_boxComplementarityGridPoint_kuhnFloor_le_one_div
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (vertex : Fin n → Fin (p * k + 1)) :
    dist (boxComplementarityGridPoint (p * k) vertex)
      (boxComplementarityGridPoint p
        (fun who ↦ kuhnFloorCoordinate p k (vertex who))) ≤
      1 / (p : ℝ) := by
  rw [dist_pi_le_iff (by positivity : 0 ≤ (1 : ℝ) / p)]
  intro who
  change dist (((vertex who).1 : ℝ) / ((p * k : ℕ) : ℝ))
      (((kuhnFloorCoordinate p k (vertex who)).1 : ℝ) / (p : ℝ)) ≤
    1 / (p : ℝ)
  simp only [kuhnFloorCoordinate_val]
  have hscale : ((((vertex who).1 / k : ℕ) : ℝ) / p) =
      ((((vertex who).1 / k) * k : ℕ) : ℝ) / (p * k) := by
    push_cast
    field_simp [Nat.ne_of_gt hp, Nat.ne_of_gt hk]
  have hmesh : (1 : ℝ) / p = (k : ℝ) / (p * k) := by
    field_simp [Nat.ne_of_gt hp, Nat.ne_of_gt hk]
  rw [hscale, hmesh, Real.dist_eq]
  push_cast
  have hlower : (vertex who).1 / k * k ≤ (vertex who).1 :=
    Nat.div_mul_le_self _ _
  have hupper : (vertex who).1 ≤ (vertex who).1 / k * k + k := by
    have hmod := Nat.mod_lt (vertex who).1 hk
    calc
      (vertex who).1 = k * ((vertex who).1 / k) + (vertex who).1 % k := by
        exact (Nat.div_add_mod (vertex who).1 k).symm
      _ ≤ k * ((vertex who).1 / k) + k := by omega
      _ = (vertex who).1 / k * k + k := by
        rw [Nat.mul_comm k]
  rw [abs_of_nonneg]
  · rw [← sub_div]
    apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < p * k)).2
    exact_mod_cast (Nat.sub_le_iff_le_add'.2 hupper)
  · apply sub_nonneg.mpr
    apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < p * k)).2
    exact_mod_cast hlower

end Math
