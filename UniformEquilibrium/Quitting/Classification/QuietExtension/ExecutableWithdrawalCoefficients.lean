import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalResponseCoefficients
import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalRaw
import Mathlib.Data.Rat.BigOperators

/-! # Executable rational source rows and finite withdrawal floors

Only actual finite reward coordinates enter these computations. The real cast
lemmas identify the canonical source definitions, including empty passive families.
-/

namespace GameTheory.ExecutableWithdrawal

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev Reward (ι : Type) :=
  {A : Finset (Option ι) // A.Nonempty} → Option ι → ℚ

noncomputable def toReal (reward : Reward ι) :
    {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ :=
  fun coalition who => (reward coalition who : ℝ)

/-- The canonical some-label embedding, used without a noncomputable data choice. -/
def childCoalition (A : Finset ι) : Finset (Option ι) :=
  A.map ⟨some, Option.some_injective ι⟩

omit [Fintype ι] [DecidableEq ι] in
theorem childCoalition_eq (A : Finset ι) :
    childCoalition A = cappedClockChildCoalition A := rfl

def singleton (reward : Reward ι) (i : ι) : ℚ :=
  reward ⟨{some i}, Finset.singleton_nonempty _⟩ (some i)

def passive (reward : Reward ι) (i : ι)
    (B : {A : Finset ι // A.Nonempty ∧ i ∉ A}) : ℚ :=
  reward ⟨childCoalition B.1, Finset.map_nonempty.mpr B.2.1⟩ (some i)

def finiteFloor (reward : Reward ι) (i : ι) (alternative : ℚ) : ℚ :=
  (insert alternative (Finset.univ.image (passive reward i))).min'
    (Finset.insert_nonempty _ _)

theorem finiteFloor_cast (reward : Reward ι) (i : ι) (alternative : ℚ) :
    (finiteFloor reward i alternative : ℝ) =
      (insert (alternative : ℝ)
        (Finset.univ.image (fun B => (passive reward i B : ℝ)))).min'
          (Finset.insert_nonempty _ _) := by
  classical
  unfold finiteFloor
  rw [(Rat.cast_mono (K := ℝ)).map_finset_min']
  simp only [Finset.image_insert, Finset.image_image, Function.comp_def]

def ownNever (reward : Reward ι) (i : ι) : ℚ := max (singleton reward i) 0

def patientFloor (reward : Reward ι) (i : ι) : ℚ :=
  finiteFloor reward i (ownNever reward i)

def zeroFloor (reward : Reward ι) (i : ι) : ℚ := finiteFloor reward i 0

omit [Fintype ι] [DecidableEq ι] in
theorem ownNever_cast (reward : Reward ι) (i : ι) :
    (ownNever reward i : ℝ) = patientWithdrawalOwnNeverAlternative (toReal reward) i := by
  simp only [ownNever, singleton, Rat.cast_max, Rat.cast_zero,
    patientWithdrawalOwnNeverAlternative, toReal]

theorem patientFloor_cast (reward : Reward ι) (i : ι) :
    (patientFloor reward i : ℝ) = patientWithdrawalFloor (toReal reward) i := by
  unfold patientFloor
  rw [finiteFloor_cast, ownNever_cast]
  rfl

theorem zeroFloor_cast (reward : Reward ι) (i : ι) :
    (zeroFloor reward i : ℝ) = deadlineWithdrawalZeroFloor (toReal reward) i := by
  unfold zeroFloor
  rw [finiteFloor_cast, Rat.cast_zero]
  rfl

def zeroGain (reward : Reward ι) (i : ι) (A : Finset ι) (hA : A.Nonempty) : ℚ :=
  if i ∈ A then
    if hrest : (A.erase i).Nonempty then
      reward ⟨childCoalition (A.erase i), Finset.map_nonempty.mpr hrest⟩ (some i) -
        reward ⟨childCoalition A, Finset.map_nonempty.mpr hA⟩ (some i)
    else zeroFloor reward i - singleton reward i
  else 0

theorem zeroGain_cast (reward : Reward ι) (i : ι) (A : Finset ι) (hA : A.Nonempty) :
    (zeroGain reward i A hA : ℝ) = deadlineWithdrawalGainFloor (toReal reward) i A hA := by
  unfold zeroGain deadlineWithdrawalGainFloor
  split_ifs
  · exact Rat.cast_sub _ _
  · simp only [Rat.cast_sub, zeroFloor_cast, singleton, toReal]
  · exact Rat.cast_zero

def restartGain (reward : Reward ι) (floor : ℚ) (i : ι)
    (A : Finset ι) (hA : A.Nonempty) : ℚ :=
  zeroGain reward i A hA + if A = {i} then floor - zeroFloor reward i else 0

theorem restartGain_cast (reward : Reward ι) (floor : ℚ) (i : ι)
    (A : Finset ι) (hA : A.Nonempty) :
    (restartGain reward floor i A hA : ℝ) =
      deadlineSecurityGainFloorWithRestart (toReal reward) floor i A hA := by
  simp only [restartGain, Rat.cast_add, zeroGain_cast, deadlineSecurityGainFloorWithRestart]
  split_ifs <;> simp only [Rat.cast_sub, Rat.cast_zero, zeroFloor_cast]

def advanceCoefficient (reward : Reward ι) : WithdrawalResponseRow ι → ι → ℚ
  | none, i => singleton reward i
  | some (false, A), i =>
      singleton reward i - reward ⟨childCoalition A.1, Finset.map_nonempty.mpr A.2⟩ (some i)
  | some (true, A), i =>
      reward ⟨childCoalition (insert i A.1),
        Finset.map_nonempty.mpr (Finset.insert_nonempty i A.1)⟩ (some i) -
      reward ⟨childCoalition A.1, Finset.map_nonempty.mpr A.2⟩ (some i)

def outsideCoefficient (reward : Reward ι) : WithdrawalResponseRow ι → ℚ
  | none => reward ⟨{none}, Finset.singleton_nonempty _⟩ none
  | some (false, A) =>
      reward ⟨{none}, Finset.singleton_nonempty _⟩ none -
      reward ⟨childCoalition A.1, Finset.map_nonempty.mpr A.2⟩ none
  | some (true, A) =>
      reward ⟨insert none (childCoalition A.1), Finset.insert_nonempty _ _⟩ none -
      reward ⟨childCoalition A.1, Finset.map_nonempty.mpr A.2⟩ none

omit [Fintype ι] in
theorem advanceCoefficient_cast (reward : Reward ι) (row : WithdrawalResponseRow ι)
    (i : ι) :
    (advanceCoefficient reward row i : ℝ) =
      withdrawalAdvanceCoefficient (toReal reward) row i := by
  cases row with
  | none => rfl
  | some row =>
      rcases row with ⟨side, A⟩
      cases side <;> exact Rat.cast_sub _ _

omit [Fintype ι] in
theorem outsideCoefficient_cast (reward : Reward ι) (row : WithdrawalResponseRow ι) :
    (outsideCoefficient reward row : ℝ) =
      withdrawalOutsideCoefficient (toReal reward) row := by
  cases row with
  | none => rfl
  | some row =>
      rcases row with ⟨side, A⟩
      cases side <;> exact Rat.cast_sub _ _

end GameTheory.ExecutableWithdrawal
