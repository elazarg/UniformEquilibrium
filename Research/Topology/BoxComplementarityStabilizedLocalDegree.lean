import Research.Topology.BoxComplementarityFloorRefinementSignedTransport
import Research.Topology.BoxComplementarityLocalSignedHomotopy

/-!
# Stabilized whole-cube-normalized degree for box complementarity

The literal geometric-times-label count stabilizes to `rawLocalDegree`.
The public `localDegree` multiplies this by `(-1)^n`, so its whole-cube
normalization is one. Identification with ambient Brouwer degree and
invertible-affine local comparison remain separate obligations.
-/

noncomputable section

namespace Math

open Classical Set

variable {n : ℕ}

private def BoxComplementarityProblem.localSignedCountThreshold
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) : ℕ :=
  (problem.eventually_localSignedCount_eq region hisolating).choose

private theorem BoxComplementarityProblem.localSignedCount_eq_of_threshold_le
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region)
    (p q : ℕ) (hpThreshold : problem.localSignedCountThreshold region hisolating ≤ p)
    (hqThreshold : problem.localSignedCountThreshold region hisolating ≤ q)
    (hp : 0 < p) (hq : 0 < q) :
    boxComplementarityLocalSignedCount problem p hp region =
      boxComplementarityLocalSignedCount problem q hq region :=
  (problem.eventually_localSignedCount_eq region hisolating).choose_spec
    p q hpThreshold hqThreshold hp hq

/-- The raw eventual integer value of the literal signed count on an isolating region. -/
def BoxComplementarityProblem.rawLocalDegree
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) : ℤ :=
  boxComplementarityLocalSignedCount problem
    (problem.localSignedCountThreshold region hisolating + 1)
    (Nat.zero_lt_succ _) region

/-- Every sufficiently fine positive grid computes the raw stabilized signed count. -/
theorem BoxComplementarityProblem.eventually_localSignedCount_eq_rawLocalDegree
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) :
    ∃ threshold, ∀ p, threshold ≤ p → ∀ hp : 0 < p,
      boxComplementarityLocalSignedCount problem p hp region =
        problem.rawLocalDegree region hisolating := by
  refine ⟨problem.localSignedCountThreshold region hisolating, ?_⟩
  intro p hpThreshold hp
  unfold rawLocalDegree
  exact problem.localSignedCount_eq_of_threshold_le region hisolating p
    (problem.localSignedCountThreshold region hisolating + 1)
    hpThreshold (Nat.le_add_right _ 1) hp (Nat.zero_lt_succ _)

/-- Whole-cube-normalized complementarity degree. The scalar records the
orientation calibration; no ambient-degree identification is asserted. -/
def BoxComplementarityProblem.localDegree
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) : ℤ :=
  (-1 : ℤ) ^ n * problem.rawLocalDegree region hisolating

/-- Every sufficiently fine signed count computes the normalized degree
after the explicit dimension-dependent orientation calibration. -/
theorem BoxComplementarityProblem.eventually_normalizedLocalSignedCount_eq_localDegree
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) :
    ∃ threshold, ∀ p, threshold ≤ p → ∀ hp : 0 < p,
      (-1 : ℤ) ^ n * boxComplementarityLocalSignedCount problem p hp region =
        problem.localDegree region hisolating := by
  obtain ⟨threshold, hcount⟩ :=
    problem.eventually_localSignedCount_eq_rawLocalDegree region hisolating
  refine ⟨threshold, fun p hpThreshold hp => ?_⟩
  rw [localDegree, hcount p hpThreshold hp]

/-- A continuous family with one common isolating region has the same stabilized
local degree at its two endpoints. -/
theorem IsContinuousBoxComplementarityFamily.localDegree_endpoints_eq
    {family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n)}
    (hcontinuous : IsContinuousBoxComplementarityFamily (Fin n) family)
    (region : Set (UnitCube (Fin n)))
    (hisolating : ∀ parameter, (family parameter).IsIsolating region) :
    (family 0).localDegree region (hisolating 0) =
      (family 1).localDegree region (hisolating 1) := by
  obtain ⟨leftThreshold, hleft⟩ :=
    (family 0).eventually_normalizedLocalSignedCount_eq_localDegree region (hisolating 0)
  obtain ⟨rightThreshold, hright⟩ :=
    (family 1).eventually_normalizedLocalSignedCount_eq_localDegree region (hisolating 1)
  obtain ⟨homotopyThreshold, hhomotopy⟩ :=
    hcontinuous.eventually_localSignedCount_endpoints_eq region hisolating
  let p := max (max leftThreshold rightThreshold) homotopyThreshold + 1
  have hp : 0 < p := Nat.zero_lt_succ _
  have hleftThreshold : leftThreshold ≤ p :=
    (le_max_left _ rightThreshold).trans
      ((le_max_left _ homotopyThreshold).trans (Nat.le_add_right _ 1))
  have hrightThreshold : rightThreshold ≤ p :=
    (le_max_right leftThreshold _).trans
      ((le_max_left _ homotopyThreshold).trans (Nat.le_add_right _ 1))
  have hhomotopyThreshold : homotopyThreshold ≤ p :=
    (le_max_right (max leftThreshold rightThreshold) _).trans
      (Nat.le_add_right _ 1)
  exact (hleft p hleftThreshold hp).symm.trans
    ((congrArg (fun value : ℤ => (-1 : ℤ) ^ n * value)
      (hhomotopy p hhomotopyThreshold hp)).trans (hright p hrightThreshold hp))

/-- Exact mesh-one reduction for the raw stabilized count. -/
theorem BoxComplementarityProblem.rawLocalDegree_univ_eq_resolution_one
    (problem : BoxComplementarityProblem (Fin n)) :
    problem.rawLocalDegree univ (by simp [IsIsolating]) =
      boxComplementarityLocalSignedCount problem 1 (by omega) univ := by
  obtain ⟨threshold, hcount⟩ :=
    problem.eventually_localSignedCount_eq_rawLocalDegree univ (by simp [IsIsolating])
  exact (hcount (threshold + 1) (by omega) (by omega)).symm.trans
    (boxComplementarityLocalSignedCount_univ_eq_resolution_one problem _ (by omega))

/-- The public degree is the calibrated mesh-one count on the whole cube. -/
theorem BoxComplementarityProblem.localDegree_univ_eq_resolution_one
    (problem : BoxComplementarityProblem (Fin n)) :
    problem.localDegree univ (by simp [IsIsolating]) =
      (-1 : ℤ) ^ n * boxComplementarityLocalSignedCount problem 1 (by omega) univ := by
  rw [localDegree, rawLocalDegree_univ_eq_resolution_one]

end Math
