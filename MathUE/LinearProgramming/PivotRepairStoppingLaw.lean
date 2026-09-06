import MathUE.LinearProgramming.PivotRepairMassPolytope
import MathUE.ProbabilityMassFunction.GeometricPivotStoppingLaw
import MathUE.ProbabilityMassFunction.FiniteStoppingTimeMenu

/-! # Actual stopping-law realizations of feasible pivot repair masses -/

noncomputable section

namespace Math.LinearProgramming

open _root_.Math.Probability
open scoped BigOperators

/-- Finite provisional masses: the head stays at its displayed dates, all
late finite mass is placed at the deadline, and Never is retained. -/
def pivotRepairFiniteClockMass {deadline : ℕ} (mass : PivotRepairMass deadline) :
    Option (Fin (deadline + 1)) → ℝ
  | none => pivotRepairNever mass
  | some time => if htime : time.val < deadline then pivotRepairHead mass ⟨time.val, htime⟩
      else pivotRepairLate mass

theorem pivotRepairFiniteClockMass_nonneg {deadline : ℕ}
    (mass : PivotRepairMass deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (choice : Option (Fin (deadline + 1))) :
    0 ≤ pivotRepairFiniteClockMass mass choice := by
  cases choice with
  | none => exact hfeasible.2.2.1
  | some time =>
      dsimp only [pivotRepairFiniteClockMass]
      split_ifs
      · exact hfeasible.1 _
      · exact hfeasible.2.1

theorem sum_pivotRepairFiniteClockMass {deadline : ℕ}
    (mass : PivotRepairMass deadline) (hfeasible : IsPivotRepairMassFeasible mass) :
    (∑ choice, pivotRepairFiniteClockMass mass choice) = 1 := by
  rw [Fintype.sum_option, Fin.sum_univ_castSucc]
  simpa [pivotRepairFiniteClockMass, add_comm, add_left_comm, add_assoc]
    using hfeasible.2.2.2.1

/-- The finite provisional masses form a literal normalized PMF. The
relaxed first-atom coordinate is not silently treated as probability mass. -/
def pivotRepairFiniteClockLaw {deadline : ℕ}
    (mass : PivotRepairMass deadline) (hfeasible : IsPivotRepairMassFeasible mass) :
    PMF (Option (Fin (deadline + 1))) :=
  PMF.ofFintype (fun choice ↦ ENNReal.ofReal (pivotRepairFiniteClockMass mass choice)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun choice _ ↦ pivotRepairFiniteClockMass_nonneg mass hfeasible choice),
      sum_pivotRepairFiniteClockMass mass hfeasible, ENNReal.ofReal_one])

/-- Actual complete provisional law on the original stopping-time space. -/
def pivotRepairProvisionalStoppingLaw {deadline : ℕ}
    (mass : PivotRepairMass deadline) (hfeasible : IsPivotRepairMassFeasible mass) :
    PMF (Option ℕ) :=
  (pivotRepairFiniteClockLaw mass hfeasible).map (finiteStoppingTimeDecode (deadline + 1))

private theorem finiteStoppingTimeDecode_injective (bound : ℕ) :
    Function.Injective (finiteStoppingTimeDecode bound) := by
  intro first second heq
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some second => simp [finiteStoppingTimeDecode] at heq
  | some first =>
      cases second with
      | none => simp [finiteStoppingTimeDecode] at heq
      | some second =>
          apply congrArg some
          apply Fin.ext
          simpa [finiteStoppingTimeDecode] using heq

theorem pivotRepairProvisionalStoppingLaw_apply_decode {deadline : ℕ}
    (mass : PivotRepairMass deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (choice : Option (Fin (deadline + 1))) :
    pivotRepairProvisionalStoppingLaw mass hfeasible
        (finiteStoppingTimeDecode (deadline + 1) choice) =
      ENNReal.ofReal (pivotRepairFiniteClockMass mass choice) := by
  rw [pivotRepairProvisionalStoppingLaw, PMF.map_apply, tsum_eq_single choice]
  · simp [pivotRepairFiniteClockLaw]
  · intro source hsource
    rw [if_neg]
    intro heq
    exact hsource ((finiteStoppingTimeDecode_injective (deadline + 1) heq).symm)

@[simp] theorem pivotRepairProvisionalStoppingLaw_none_toReal {deadline : ℕ}
    (mass : PivotRepairMass deadline) (hfeasible : IsPivotRepairMassFeasible mass) :
    (pivotRepairProvisionalStoppingLaw mass hfeasible none).toReal = pivotRepairNever mass := by
  have h := pivotRepairProvisionalStoppingLaw_apply_decode mass hfeasible none
  rw [show finiteStoppingTimeDecode (deadline + 1) none = none by rfl] at h
  rw [h, ENNReal.toReal_ofReal (pivotRepairFiniteClockMass_nonneg mass hfeasible none)]
  rfl

theorem pivotRepairProvisionalStoppingLaw_head_toReal {deadline : ℕ}
    (mass : PivotRepairMass deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (time : Fin deadline) :
    (pivotRepairProvisionalStoppingLaw mass hfeasible (some time.val)).toReal =
      pivotRepairHead mass time := by
  have h := pivotRepairProvisionalStoppingLaw_apply_decode mass hfeasible (some time.castSucc)
  change pivotRepairProvisionalStoppingLaw mass hfeasible (some time.val) = _ at h
  rw [h, ENNReal.toReal_ofReal
    (pivotRepairFiniteClockMass_nonneg mass hfeasible (some time.castSucc))]
  simp [pivotRepairFiniteClockMass, time.isLt]

@[simp] theorem pivotRepairProvisionalStoppingLaw_deadline_toReal {deadline : ℕ}
    (mass : PivotRepairMass deadline) (hfeasible : IsPivotRepairMassFeasible mass) :
    (pivotRepairProvisionalStoppingLaw mass hfeasible (some deadline)).toReal =
      pivotRepairLate mass := by
  have h := pivotRepairProvisionalStoppingLaw_apply_decode mass hfeasible (some (Fin.last deadline))
  change pivotRepairProvisionalStoppingLaw mass hfeasible (some deadline) = _ at h
  rw [h, ENNReal.toReal_ofReal
    (pivotRepairFiniteClockMass_nonneg mass hfeasible (some (Fin.last deadline)))]
  simp [pivotRepairFiniteClockMass]

theorem pivotRepairProvisionalStoppingLaw_some_of_gt {deadline : ℕ}
    (mass : PivotRepairMass deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    {time : ℕ} (htime : deadline < time) :
    pivotRepairProvisionalStoppingLaw mass hfeasible (some time) = 0 := by
  rw [pivotRepairProvisionalStoppingLaw, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro choice
  rw [if_neg]
  cases choice with
  | none => simp [finiteStoppingTimeDecode]
  | some chosen =>
      simp only [finiteStoppingTimeDecode, Option.map_some, Option.some.injEq]
      have hchosen := chosen.isLt
      omega

theorem pivotRepairProvisionalStoppingLaw_lateFiniteMass {deadline : ℕ}
    (hdeadline : 0 < deadline) (mass : PivotRepairMass deadline)
    (hfeasible : IsPivotRepairMassFeasible mass) :
    stoppingLawLateFiniteMass (pivotRepairProvisionalStoppingLaw mass hfeasible) (deadline - 1) =
      pivotRepairLate mass := by
  rw [stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead,
    pivotRepairProvisionalStoppingLaw_none_toReal]
  have hhead : stoppingLawFiniteHeadMass
      (pivotRepairProvisionalStoppingLaw mass hfeasible) (deadline - 1) =
      ∑ time, pivotRepairHead mass time := by
    unfold stoppingLawFiniteHeadMass
    rw [show deadline - 1 + 1 = deadline by omega, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro time _
    exact pivotRepairProvisionalStoppingLaw_head_toReal mass hfeasible time
  rw [hhead]
  linarith [hfeasible.2.2.2.1]

/-- Integrating the actual provisional law gives exactly the displayed
finite affine combination, for any real-valued stopping-time observable. -/
theorem expect_pivotRepairProvisionalStoppingLaw {deadline : ℕ}
    (mass : PivotRepairMass deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (value : Option ℕ → ℝ) :
    expect (pivotRepairProvisionalStoppingLaw mass hfeasible) value =
      (∑ time, pivotRepairHead mass time * value (some time.val)) +
        pivotRepairLate mass * value (some deadline) + pivotRepairNever mass * value none := by
  rw [pivotRepairProvisionalStoppingLaw, expect_map, expect_eq_sum]
  simp only [pivotRepairFiniteClockLaw, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (pivotRepairFiniteClockMass_nonneg mass hfeasible _)]
  rw [Fintype.sum_option, Fin.sum_univ_castSucc]
  simp [pivotRepairFiniteClockMass, finiteStoppingTimeDecode, add_comm, add_left_comm]

/-- Censoring the provisional deadline atom to Never gives exactly the
unconditional early affine contribution. -/
theorem expect_censor_pivotRepairProvisionalStoppingLaw {deadline : ℕ}
    (hdeadline : 0 < deadline) (mass : PivotRepairMass deadline)
    (hfeasible : IsPivotRepairMassFeasible mass) (value : Option ℕ → ℝ) :
    expect (censorLateFiniteStoppingLaw
      (pivotRepairProvisionalStoppingLaw mass hfeasible) (deadline - 1)) value =
      (∑ time, pivotRepairHead mass time * value (some time.val)) +
        (pivotRepairLate mass + pivotRepairNever mass) * value none := by
  rw [censorLateFiniteStoppingLaw, expect_map, expect_pivotRepairProvisionalStoppingLaw]
  have hhead (time : Fin deadline) :
      censorLateFiniteStoppingOutcome (deadline - 1) (some time.val) = some time.val := by
    simp [censorLateFiniteStoppingOutcome, show time.val ≤ deadline - 1 by omega]
  simp only [hhead]
  simp only [censorLateFiniteStoppingOutcome,
    show ¬ deadline ≤ deadline - 1 by omega, if_false]
  ring

private theorem first_atom_div_late_positive {deadline : ℕ}
    (mass : PivotRepairMass deadline) {firstAtom : ℝ}
    (hpositive : 0 < firstAtom) (hle : firstAtom ≤ pivotRepairLate mass) :
    0 < firstAtom / pivotRepairLate mass :=
  div_pos hpositive (hpositive.trans_le hle)

private theorem first_atom_div_late_le_one {deadline : ℕ}
    (mass : PivotRepairMass deadline) {firstAtom : ℝ}
    (hpositive : 0 < firstAtom) (hle : firstAtom ≤ pivotRepairLate mass) :
    firstAtom / pivotRepairLate mass ≤ 1 :=
  (div_le_one (hpositive.trans_le hle)).mpr hle

/-- An actual geometric law realizing the feasible head, late, and Never
masses with any requested strictly positive first atom below the late mass.
The requested atom may approximate, rather than equal, the LP coordinate. -/
def pivotRepairGeometricStoppingLaw {deadline : ℕ}
    (mass : PivotRepairMass deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (firstAtom : ℝ) (hpositive : 0 < firstAtom) (hle : firstAtom ≤ pivotRepairLate mass) :
    PMF (Option ℕ) :=
  geometricPivotStoppingLaw (pivotRepairProvisionalStoppingLaw mass hfeasible) deadline
    (firstAtom / pivotRepairLate mass) (first_atom_div_late_positive mass hpositive hle)
    (first_atom_div_late_le_one mass hpositive hle)

@[simp] theorem pivotRepairGeometricStoppingLaw_none_toReal {deadline : ℕ}
    (mass : PivotRepairMass deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (firstAtom : ℝ) (hpositive : 0 < firstAtom) (hle : firstAtom ≤ pivotRepairLate mass) :
    (pivotRepairGeometricStoppingLaw mass hfeasible firstAtom hpositive hle none).toReal =
      pivotRepairNever mass := by
  simp [pivotRepairGeometricStoppingLaw]

theorem pivotRepairGeometricStoppingLaw_head_toReal {deadline : ℕ}
    (mass : PivotRepairMass deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (firstAtom : ℝ) (hpositive : 0 < firstAtom) (hle : firstAtom ≤ pivotRepairLate mass)
    (time : Fin deadline) :
    (pivotRepairGeometricStoppingLaw mass hfeasible firstAtom hpositive hle
      (some time.val)).toReal = pivotRepairHead mass time := by
  rw [pivotRepairGeometricStoppingLaw, geometricPivotStoppingLaw_some_of_lt _ _ _ _ _ time.isLt]
  exact pivotRepairProvisionalStoppingLaw_head_toReal mass hfeasible time

theorem pivotRepairGeometricStoppingLaw_lateFiniteMass {deadline : ℕ}
    (hdeadline : 0 < deadline) (mass : PivotRepairMass deadline)
    (hfeasible : IsPivotRepairMassFeasible mass) (firstAtom : ℝ)
    (hpositive : 0 < firstAtom) (hle : firstAtom ≤ pivotRepairLate mass) :
    stoppingLawLateFiniteMass
      (pivotRepairGeometricStoppingLaw mass hfeasible firstAtom hpositive hle) (deadline - 1) =
      pivotRepairLate mass := by
  rw [pivotRepairGeometricStoppingLaw, geometricPivotStoppingLaw_lateFiniteMass _ hdeadline]
  exact pivotRepairProvisionalStoppingLaw_lateFiniteMass hdeadline mass hfeasible

theorem pivotRepairGeometricStoppingLaw_add_apply_toReal {deadline : ℕ}
    (hdeadline : 0 < deadline) (mass : PivotRepairMass deadline)
    (hfeasible : IsPivotRepairMassFeasible mass) (firstAtom : ℝ)
    (hpositive : 0 < firstAtom) (hle : firstAtom ≤ pivotRepairLate mass) (offset : ℕ) :
    (pivotRepairGeometricStoppingLaw mass hfeasible firstAtom hpositive hle
      (some (deadline + offset))).toReal =
      firstAtom * (1 - firstAtom / pivotRepairLate mass) ^ offset := by
  rw [pivotRepairGeometricStoppingLaw, geometricPivotStoppingLaw_add_apply_toReal _ hdeadline,
    pivotRepairProvisionalStoppingLaw_lateFiniteMass hdeadline mass hfeasible]
  have hlate : pivotRepairLate mass ≠ 0 := ne_of_gt (hpositive.trans_le hle)
  field_simp

theorem pivotRepairGeometricStoppingLaw_sum_Ico_add {deadline : ℕ}
    (hdeadline : 0 < deadline) (mass : PivotRepairMass deadline)
    (hfeasible : IsPivotRepairMassFeasible mass) (firstAtom : ℝ)
    (hpositive : 0 < firstAtom) (hle : firstAtom ≤ pivotRepairLate mass) (offset : ℕ) :
    (∑ time ∈ Finset.Ico deadline (deadline + offset),
      (pivotRepairGeometricStoppingLaw mass hfeasible firstAtom hpositive hle (some time)).toReal) =
      pivotRepairLate mass * (1 - (1 - firstAtom / pivotRepairLate mass) ^ offset) := by
  rw [pivotRepairGeometricStoppingLaw, geometricPivotStoppingLaw_sum_Ico_add _ hdeadline,
    pivotRepairProvisionalStoppingLaw_lateFiniteMass hdeadline mass hfeasible]

end Math.LinearProgramming
