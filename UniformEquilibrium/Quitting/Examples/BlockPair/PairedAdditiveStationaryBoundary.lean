import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientSameProfile
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientAmbientDegree
import Mathlib.Order.Interval.Set.Infinite

/-! # Singular additive paired rewards and their upper-boundary stationary fiber

Both displayed matrices are singular and R0. The quotient has degree zero,
whereas the actual entire nonzero clipped fixed fiber has ambient degree one.
Every upper-face point retains its original independent stationary profile
and unrestricted terminal Nash. No isolated-root or regularity premise occurs.
-/

noncomputable section

namespace GameTheory.PairedAdditiveStationaryBoundary

open Set Math.Topology Math.LinearProgramming QuittingLCPClassification
open QuittingFinFourEndpointRows

def matrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, -1 / 2, -1 / 2;
     -1, 0, -1 / 2, -1 / 2;
     -1 / 2, -1 / 2, 0, -1;
     -1 / 2, -1 / 2, -1, 0]

def reward (terminal : {S : Finset (Fin 4) // S.Nonempty}) : Payoff (Fin 4) :=
  fun who => ∑ owner ∈ terminal.1, matrix who owner

def block : Fin 4 → Fin 2 := ![0, 0, 1, 1]

def representative : Fin 2 → Fin 4 := ![0, 2]

theorem block_representative (coordinate : Fin 2) :
    block (representative coordinate) = coordinate := by
  fin_cases coordinate <;> rfl

theorem own_singleton (who : Fin 4) :
    reward (quittingSingletonTerminal who) who = 0 := by
  fin_cases who <;> norm_num [reward, matrix, quittingSingletonTerminal]

theorem singletonMatrix_eq : quittingSingletonMatrix reward = matrix := by
  ext who owner
  have hdiagonal : matrix who who = 0 := by
    fin_cases who <;> norm_num [matrix, Matrix.of_apply]
  simp only [quittingSingletonMatrix, reward, Finset.sum_singleton, hdiagonal, sub_zero]

theorem matrix_kernel : matrix.mulVec ![1, 1, -1, -1] = 0 := by
  ext who
  fin_cases who <;> norm_num [matrix, Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem matrix_det_zero : matrix.det = 0 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [matrix, Matrix.of_apply, Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove,
    Matrix.submatrix]

/-- Singularity is not the failure of R0: no nonnegative homogeneous root survives. -/
theorem matrix_isR0 : IsR0Matrix matrix := by
  intro root hroot who
  have hz0 := hroot.weight_nonneg 0
  have hz1 := hroot.weight_nonneg 1
  have hz2 := hroot.weight_nonneg 2
  have hz3 := hroot.weight_nonneg 3
  have h0 := hroot.residual_nonneg 0
  have h1 := hroot.residual_nonneg 1
  norm_num [lcpResidual, matrix, Matrix.of_apply, Fin.sum_univ_succ] at h0 h1
  fin_cases who
  · change root 0 = 0
    linarith
  · change root 1 = 0
    linarith
  · change root 2 = 0
    linarith
  · change root 3 = 0
    linarith

def quotientMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![-1, -1; -1, -1]

theorem actual_quotientMatrix :
    quittingResponseQuotientMatrix reward block representative = quotientMatrix := by
  ext row column
  unfold quittingResponseQuotientMatrix quittingSingletonBlockRowSum
  rw [singletonMatrix_eq]
  fin_cases row <;> fin_cases column <;>
    norm_num [block, representative, quotientMatrix, matrix, Matrix.of_apply, Fin.sum_univ_succ]

theorem quotientMatrix_det_zero : quotientMatrix.det = 0 := by
  norm_num [quotientMatrix, Matrix.of_apply, Matrix.det_fin_two]

theorem quotientMatrix_isR0 : IsR0Matrix quotientMatrix := by
  intro root hroot who
  have hz0 := hroot.weight_nonneg 0
  have hz1 := hroot.weight_nonneg 1
  have h0 := hroot.residual_nonneg 0
  norm_num [lcpResidual, quotientMatrix, Matrix.of_apply, Fin.sum_univ_succ] at h0
  fin_cases who
  · change root 0 = 0
    linarith
  · change root 1 = 0
    linarith

theorem quotientMatrix_not_solvable_neg_one :
    ¬StandardLCPSolvable quotientMatrix (-1) := by
  rintro ⟨root, hroot⟩
  have hz0 := hroot.weight_nonneg 0
  have hz1 := hroot.weight_nonneg 1
  have h0 := hroot.residual_nonneg 0
  norm_num [lcpResidual, quotientMatrix, Matrix.of_apply, Fin.sum_univ_succ] at h0
  linarith

theorem quotientMatrix_degree_zero :
    r0Degree quotientMatrix quotientMatrix_isR0 = 0 := by
  by_contra hdegree
  exact quotientMatrix_not_solvable_neg_one
    (isStandardQ_of_r0Degree_ne_zero quotientMatrix quotientMatrix_isR0 hdegree (-1))

private theorem quit_0 (hazard : Fin 4 → ℝ) :
    pureQuitEndpointRowSum reward hazard 0 = -hazard 1 - hazard 2 / 2 - hazard 3 / 2 := by
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, weightOfReward,
    reward, matrix, Matrix.of_apply]
  ring

private theorem quit_1 (hazard : Fin 4 → ℝ) :
    pureQuitEndpointRowSum reward hazard 1 = -hazard 0 - hazard 2 / 2 - hazard 3 / 2 := by
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, weightOfReward,
    reward, matrix, Matrix.of_apply]
  ring

private theorem quit_2 (hazard : Fin 4 → ℝ) :
    pureQuitEndpointRowSum reward hazard 2 = -hazard 0 / 2 - hazard 1 / 2 - hazard 3 := by
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, weightOfReward,
    reward, matrix, Matrix.of_apply]
  ring

private theorem quit_3 (hazard : Fin 4 → ℝ) :
    pureQuitEndpointRowSum reward hazard 3 = -hazard 0 / 2 - hazard 1 / 2 - hazard 2 := by
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, weightOfReward,
    reward, matrix, Matrix.of_apply]
  ring

private theorem excluded_0 (hazard : Fin 4 → ℝ) :
    excludedEndpointRowSum reward hazard 0 = -hazard 1 - hazard 2 / 2 - hazard 3 / 2 := by
  norm_num +decide [excludedEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, weightOfReward,
    reward, matrix, Matrix.of_apply]
  ring

private theorem excluded_1 (hazard : Fin 4 → ℝ) :
    excludedEndpointRowSum reward hazard 1 = -hazard 0 - hazard 2 / 2 - hazard 3 / 2 := by
  norm_num +decide [excludedEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, weightOfReward,
    reward, matrix, Matrix.of_apply]
  ring

private theorem excluded_2 (hazard : Fin 4 → ℝ) :
    excludedEndpointRowSum reward hazard 2 = -hazard 0 / 2 - hazard 1 / 2 - hazard 3 := by
  norm_num +decide [excludedEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, weightOfReward,
    reward, matrix, Matrix.of_apply]
  ring

private theorem excluded_3 (hazard : Fin 4 → ℝ) :
    excludedEndpointRowSum reward hazard 3 = -hazard 0 / 2 - hazard 1 / 2 - hazard 2 := by
  norm_num +decide [excludedEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, weightOfReward,
    reward, matrix, Matrix.of_apply]
  ring

/-- Both actual endpoint contributions are the same linear form, for signed hazards too. -/
theorem endpoints_eq_mulVec (hazard : Fin 4 → ℝ) (who : Fin 4) :
    sigmaValue (weightOfReward reward) hazard who = matrix.mulVec hazard who ∧
      excludedValue (weightOfReward reward) hazard who = matrix.mulVec hazard who := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum, excludedValue_eq_excludedEndpointRowSum]
  fin_cases who
  · change pureQuitEndpointRowSum reward hazard 0 = matrix.mulVec hazard 0 ∧
      excludedEndpointRowSum reward hazard 0 = matrix.mulVec hazard 0
    rw [quit_0, excluded_0]
    norm_num [matrix, Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · change pureQuitEndpointRowSum reward hazard 1 = matrix.mulVec hazard 1 ∧
      excludedEndpointRowSum reward hazard 1 = matrix.mulVec hazard 1
    rw [quit_1, excluded_1]
    norm_num [matrix, Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · change pureQuitEndpointRowSum reward hazard 2 = matrix.mulVec hazard 2 ∧
      excludedEndpointRowSum reward hazard 2 = matrix.mulVec hazard 2
    rw [quit_2, excluded_2]
    norm_num [matrix, Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · change pureQuitEndpointRowSum reward hazard 3 = matrix.mulVec hazard 3 ∧
      excludedEndpointRowSum reward hazard 3 = matrix.mulVec hazard 3
    rw [quit_3, excluded_3]
    norm_num [matrix, Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

/-- Exact representative-independent residuals on the whole signed block space. -/
theorem displacement_eq (point : Fin 2 → ℝ) (who : Fin 4) :
    quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) who =
      if block who = 0 then (1 - point 0) * (1 - point 1) ^ 2 * (point 0 + point 1)
      else (1 - point 0) ^ 2 * (1 - point 1) * (point 0 + point 1) := by
  unfold quittingDiscountedDisplacement
  rw [(endpoints_eq_mulVec _ who).1, (endpoints_eq_mulVec _ who).2]
  fin_cases who
  · change (1 - (1 - (0 : ℝ)) *
        continueMassExcl (quittingBlockLift block point) 0) *
        matrix.mulVec (quittingBlockLift block point) 0 -
        matrix.mulVec (quittingBlockLift block point) 0 = _
    unfold continueMassExcl
    rw [show (Finset.univ : Finset (Fin 4)).erase 0 = {1, 2, 3} by decide]
    norm_num [quittingBlockLift, block, matrix, Matrix.of_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring
  · change (1 - (1 - (0 : ℝ)) *
        continueMassExcl (quittingBlockLift block point) 1) *
        matrix.mulVec (quittingBlockLift block point) 1 -
        matrix.mulVec (quittingBlockLift block point) 1 = _
    unfold continueMassExcl
    rw [show (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} by decide]
    norm_num [quittingBlockLift, block, matrix, Matrix.of_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring
  · change (1 - (1 - (0 : ℝ)) *
        continueMassExcl (quittingBlockLift block point) 2) *
        matrix.mulVec (quittingBlockLift block point) 2 -
        matrix.mulVec (quittingBlockLift block point) 2 = _
    unfold continueMassExcl
    rw [show (Finset.univ : Finset (Fin 4)).erase 2 = {0, 1, 3} by decide]
    norm_num [quittingBlockLift, block, matrix, Matrix.of_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring
  · change (1 - (1 - (0 : ℝ)) *
        continueMassExcl (quittingBlockLift block point) 3) *
        matrix.mulVec (quittingBlockLift block point) 3 -
        matrix.mulVec (quittingBlockLift block point) 3 = _
    unfold continueMassExcl
    rw [show (Finset.univ : Finset (Fin 4)).erase 3 = {0, 1, 2} by decide]
    norm_num [quittingBlockLift, block, matrix, Matrix.of_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring

theorem responseInvariant : QuittingResponseInvariantOnUnitCube reward block := by
  intro point _hpoint first second hblock
  rw [displacement_eq, displacement_eq, hblock]

theorem quotientResponse_eq (point : Fin 2 → ℝ) :
    quittingQuotientResponse reward block representative point =
      ![(1 - point 0) * (1 - point 1) ^ 2 * (point 0 + point 1),
        (1 - point 0) ^ 2 * (1 - point 1) * (point 0 + point 1)] := by
  ext coordinate
  unfold quittingQuotientResponse
  rw [displacement_eq]
  fin_cases coordinate <;> norm_num [block, representative]

/-- Both upper faces consist of actual quotient fixed points. -/
theorem fixedPoint_of_upper_face (point : Fin 2 → ℝ)
    (hpoint : ∀ coordinate, 0 ≤ point coordinate ∧ point coordinate ≤ 1)
    (hface : point 0 = 1 ∨ point 1 = 1) :
    quittingQuotientStationaryClippedMap reward block representative point = point := by
  apply (quittingQuotientStationaryClippedMap_eq_self_iff reward block representative point
    (fun coordinate => (hpoint coordinate).1)
    (fun coordinate => (hpoint coordinate).2)).mpr
  have hzero (who : Fin 4) :
      quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) who = 0 := by
    rw [displacement_eq]
    rcases hface with hface | hface <;> simp [hface]
  intro coordinate
  rw [hzero]
  exact ⟨fun _ => le_rfl, fun _ _ => rfl, fun _ => le_rfl⟩

def facePoint (rate : ℝ) : Fin 2 → ℝ := ![1, rate]

theorem facePoint_mem_cube (rate : ℝ) (hzero : 0 ≤ rate) (hone : rate ≤ 1) :
    ∀ coordinate, 0 ≤ facePoint rate coordinate ∧ facePoint rate coordinate ≤ 1 := by
  intro coordinate
  fin_cases coordinate
  · norm_num [facePoint]
  · exact ⟨hzero, hone⟩

theorem facePoint_fixed (rate : ℝ) (hzero : 0 ≤ rate) (hone : rate ≤ 1) :
    quittingQuotientStationaryClippedMap reward block representative (facePoint rate) =
      facePoint rate :=
  fixedPoint_of_upper_face _ (facePoint_mem_cube rate hzero hone) (Or.inl rfl)

theorem facePoint_ne_zero (rate : ℝ) : facePoint rate ≠ 0 := by
  intro hzero
  have h := congrFun hzero 0
  norm_num [facePoint] at h

def faceRoot (rate : ℝ) (hzero : 0 ≤ rate) (hone : rate ≤ 1) : Fin 4 → PMF Bool :=
  rootOfHazard (quittingBlockLift block (facePoint rate))
    (fun who => (facePoint_mem_cube rate hzero hone (block who)).1)
    (fun who => (facePoint_mem_cube rate hzero hone (block who)).2)

theorem faceRoot_hazards (rate : ℝ) (hzero : 0 ≤ rate) (hone : rate ≤ 1) :
    hazardOfRoot (faceRoot rate hzero hone) = ![1, 1, rate, rate] := by
  have hroundtrip := hazardOfRoot_rootOfHazard
    (quittingBlockLift block (facePoint rate))
    (fun who => (facePoint_mem_cube rate hzero hone (block who)).1)
    (fun who => (facePoint_mem_cube rate hzero hone (block who)).2)
  change hazardOfRoot (faceRoot rate hzero hone) =
    quittingBlockLift block (facePoint rate) at hroundtrip
  calc
    _ = quittingBlockLift block (facePoint rate) := hroundtrip
    _ = ![1, 1, rate, rate] := by
      ext who
      fin_cases who <;> rfl

/-- The original independent root at any point of either upper face. -/
def upperFaceRoot (point : Fin 2 → ℝ)
    (hpoint : ∀ coordinate, 0 ≤ point coordinate ∧ point coordinate ≤ 1) :
    Fin 4 → PMF Bool :=
  rootOfHazard (quittingBlockLift block point)
    (fun who => (hpoint (block who)).1) (fun who => (hpoint (block who)).2)

/-- Every point of BOTH upper faces retains its original stationary profile,
full terminal Nash and all long-horizon witnesses at the same actual target. -/
theorem upperFaceRoot_terminalNash_sameProfileUniform
    (point : Fin 2 → ℝ)
    (hpoint : ∀ coordinate, 0 ≤ point coordinate ∧ point coordinate ≤ 1)
    (hface : point 0 = 1 ∨ point 1 = 1) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward (upperFaceRoot point hpoint)) ∧
      ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
        ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon accuracy
            (quittingStationaryProfile reward (upperFaceRoot point hpoint)) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingStationaryProfile reward (upperFaceRoot point hpoint)) who -
            quittingTerminalPayoff reward
              (quittingStationaryProfile reward (upperFaceRoot point hpoint)) who| ≤ accuracy := by
  have hnonzero : point ≠ 0 := by
    intro hzero
    rcases hface with hface | hface
    · have hcoordinate := congrFun hzero 0
      change point 0 = 0 at hcoordinate
      linarith
    · have hcoordinate := congrFun hzero 1
      change point 1 = 0 at hcoordinate
      linarith
  apply terminalNash_and_sameProfileUniform_of_nonzero_quotientFixedPoint_singletonSign
    reward block representative block_representative responseInvariant point
    hnonzero (fixedPoint_of_upper_face point hpoint hface) (upperFaceRoot point hpoint)
    (hazardOfRoot_rootOfHazard _ _ _)
  intro who _hsingleton
  simpa only [own_singleton] using (le_rfl : (0 : ℝ) ≤ 0)

/-- Every original player's unrestricted cap at either upper face equals its
actual prescribed payoff; this includes the two proper-support endpoints. -/
theorem upperFaceRoot_completeCap_eq_payoff
    (point : Fin 2 → ℝ)
    (hpoint : ∀ coordinate, 0 ≤ point coordinate ∧ point coordinate ≤ 1)
    (hface : point 0 = 1 ∨ point 1 = 1) (who : Fin 4) :
    quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward (upperFaceRoot point hpoint)) who =
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward (upperFaceRoot point hpoint)) who := by
  let profile := quittingStationaryProfile reward (upperFaceRoot point hpoint)
  have hnash := (upperFaceRoot_terminalNash_sameProfileUniform point hpoint hface).1
  apply le_antisymm
  · unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, Set.mem_range_self (profile who)⟩
    · rintro achieved ⟨deviation, rfl⟩
      simpa only [add_zero] using hnash who deviation
  · have hself := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile who (profile who)
    simpa only [Function.update_eq_self] using hself

/-- The SAME actual stationary profile is exact terminal Nash and supplies all
long-horizon witnesses at its own fixed payoff, including the proper-support endpoint. -/
theorem faceRoot_terminalNash_sameProfileUniform
    (rate : ℝ) (hzero : 0 ≤ rate) (hone : rate ≤ 1) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward (faceRoot rate hzero hone)) ∧
      ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
        ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon accuracy
            (quittingStationaryProfile reward (faceRoot rate hzero hone)) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingStationaryProfile reward (faceRoot rate hzero hone)) who -
            quittingTerminalPayoff reward
              (quittingStationaryProfile reward (faceRoot rate hzero hone)) who| ≤ accuracy := by
  exact upperFaceRoot_terminalNash_sameProfileUniform (facePoint rate)
    (facePoint_mem_cube rate hzero hone) (Or.inl rfl)

/-- The all-behavioral cap equals the prescribed actual payoff for every original player. -/
theorem faceRoot_completeCap_eq_payoff
    (rate : ℝ) (hzero : 0 ≤ rate) (hone : rate ≤ 1) (who : Fin 4) :
    quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward (faceRoot rate hzero hone)) who =
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward (faceRoot rate hzero hone)) who := by
  exact upperFaceRoot_completeCap_eq_payoff (facePoint rate)
    (facePoint_mem_cube rate hzero hone) (Or.inl rfl) who

/-- An infinite upper-face family lies in the actual absorbing quotient fixed fiber. -/
theorem nonzeroFixedPointSet_infinite :
    (quittingQuotientNonzeroFixedPointSet reward block representative).Infinite := by
  apply Set.infinite_of_injOn_mapsTo (f := facePoint) (s := Icc (0 : ℝ) 1)
  · intro first _hfirst second _hsecond hequal
    exact congrFun hequal 1
  · intro rate hrate
    exact ⟨facePoint_ne_zero rate, facePoint_fixed rate hrate.1 hrate.2⟩
  · exact Set.Icc_infinite (by norm_num)

/-- Literal upper-face roots accumulate at the proper-support point (1,0). -/
theorem exists_facePoint_near_properSupport (distance : ℝ) (hdistance : 0 < distance) :
    ∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      facePoint rate ≠ facePoint 0 ∧ dist (facePoint rate) (facePoint 0) < distance := by
  let rate := min (distance / 2) (1 / 2)
  have hpositive : 0 < rate := lt_min (by linarith) (by norm_num)
  have hunit : rate ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hclose : rate < distance := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨rate, hpositive, hunit, ?_, ?_⟩
  · intro hequal
    have hzero : rate = 0 := congrFun hequal 1
    exact hpositive.ne' hzero
  · rw [dist_eq_norm]
    apply (pi_norm_lt_iff hdistance).mpr
    intro coordinate
    fin_cases coordinate
    · simpa [facePoint] using hdistance
    · simpa [facePoint, Real.norm_eq_abs, abs_of_pos hpositive] using hclose

/-- Full fixed-box normalization uses the expanded signed ambient domain. -/
theorem total_fixedBox_degree_one :
    ambientDegree (quittingQuotientFixedPointField reward block representative)
      quittingQuotientOmega 0 isOpen_quittingQuotientOmega isBounded_quittingQuotientOmega
      (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
      (quittingQuotientFixedPointField_ne_zero_on_frontier_omega reward block representative) =
        1 :=
  quittingQuotientFixedPointField_ambientDegree_omega_eq_one reward block representative

/-- The annulus retains the entire nonzero fiber; no individual root indices are assumed. -/
theorem exists_omegaAnnulus_entireNonzero_degree_one :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 / 2 ∧
      (∀ point : Fin 2 → ℝ, ‖point‖ ≤ radius →
        quittingQuotientStationaryClippedMap reward block representative point = point →
          point = 0) ∧
      ∃ hfrontier : ∀ point ∈ frontier (quittingQuotientOmegaAnnulus (k := 2) radius),
          quittingQuotientFixedPointField reward block representative point ≠ 0,
        ({point | quittingQuotientFixedPointField reward block representative point = 0} ∩
          quittingQuotientOmegaAnnulus radius) =
            quittingQuotientNonzeroFixedPointSet reward block representative ∧
        ambientDegree (quittingQuotientFixedPointField reward block representative)
          (quittingQuotientOmegaAnnulus radius) 0
          (isOpen_quittingQuotientOmegaAnnulus radius)
          (isBounded_quittingQuotientOmegaAnnulus radius)
          (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
          hfrontier = 1 := by
  have hR0 : IsR0Matrix (quittingResponseQuotientMatrix reward block representative) := by
    rw [actual_quotientMatrix]
    exact quotientMatrix_isR0
  have hdegree :
      r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 = 0 := by
    simpa only [actual_quotientMatrix] using quotientMatrix_degree_zero
  obtain ⟨radius, hradius, hsmall, hisolation, hfrontier, hfiber, hactualDegree⟩ :=
    exists_quittingQuotientOmegaAnnulus_ambientDegree_eq_one_sub_r0Degree
      reward block representative block_representative hR0
  refine ⟨radius, hradius, hsmall, hisolation, hfrontier, hfiber, ?_⟩
  simpa only [hdegree, sub_zero] using hactualDegree

end GameTheory.PairedAdditiveStationaryBoundary
