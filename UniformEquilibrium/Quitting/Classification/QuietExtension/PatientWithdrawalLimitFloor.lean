import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalPayoffLimit
import UniformEquilibrium.Quitting.Paths.CommonStoppingCalendarRetiming

/-! # The patient singleton floor from actual terminal payoff limits -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The limiting patient operation, when activated, obtains at least the
literal patient floor. Its opponent-Never branch obtains the own alternative,
and every other branch obtains an actual passive nonempty coalition reward. -/
theorem patientWithdrawalFloor_le_terminalPayoffLimit_of_not_before
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hbefore : ¬ quittingStoppingTimeValue (times i) < (time : WithTop ℕ)) :
    patientWithdrawalFloor reward i ≤
      patientWithdrawalTerminalPayoffLimit reward times (some time) i := by
  let : Nonempty ι := ⟨i⟩
  rw [patientWithdrawalTerminalPayoffLimit, ite_eq_right hbefore]
  by_cases hall : ∀ j, j ≠ i → times j = none
  · rw [ite_eq_left hall]
    exact patientWithdrawalFloor_le_ownNeverAlternative reward i
  · rw [ite_eq_right hall]
    let updated := Function.update times i none
    have hclocks : deadlinePrivateChildClocks times i none = quietParentClocks updated := by
      funext player
      cases player with
      | none => rfl
      | some j => by_cases hj : j = i <;>
          simp [deadlinePrivateChildClocks, quietParentClocks, updated, hj]
    rw [hclocks]
    induction hfirst : quittingEarliestStoppingValue updated using WithTop.recTopCoe with
    | top =>
        have hnever := (quittingEarliestStoppingValue_eq_top_iff updated).mp hfirst
        exact (hall (fun j hj => by simpa [updated, hj] using hnever j)).elim
    | coe first =>
        let B := quittingEarliestStoppingCoalition updated
        have hB : B.Nonempty := quittingEarliestStoppingCoalition_nonempty updated
        have hi : i ∉ B := by
          intro hmem
          have hvalue : quittingStoppingTimeValue (updated i) = (first : WithTop ℕ) := by
            simpa [B, quittingEarliestStoppingCoalition, hfirst] using hmem
          simp [updated, quittingStoppingTimeValue] at hvalue
        have houtcome := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
          updated first hfirst
        simpa only [quittingPureClockTerminalPayoff, houtcome] using
          patientWithdrawalFloor_le_passiveReward reward i B hB hi

/-- The terminal limiting gain of the separately legal patient experiment. -/
def patientWithdrawalTerminalGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) : ℝ :=
  patientWithdrawalTerminalPayoffLimit reward times deadline i -
    quittingPureClockTerminalPayoff reward (quietParentClocks times) (some i)

/-- A Never outsider replica does not activate patient withdrawal. -/
theorem patientWithdrawalTerminalGain_none
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (i : ι) :
    patientWithdrawalTerminalGain reward times none i = 0 := by
  simp [patientWithdrawalTerminalGain, patientWithdrawalTerminalPayoffLimit]

/-- When the owner is the sole first quitter, every earlier or tied deadline
activates the literal patient singleton gain floor. -/
theorem patientWithdrawalTerminalGain_singleton_ge_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (time first : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (hsingleton : quittingEarliestStoppingCoalition times = {i})
    (htime : time ≤ first) :
    patientWithdrawalGainFloor reward i {i} (Finset.singleton_nonempty i) ≤
      patientWithdrawalTerminalGain reward times (some time) i := by
  let : Nonempty ι := ⟨i⟩
  have hbefore : ¬ quittingStoppingTimeValue (times i) < (time : WithTop ℕ) := by
    apply not_lt.mpr
    have hle : quittingEarliestStoppingValue times ≤
        quittingStoppingTimeValue (times i) := Finset.inf_le (Finset.mem_univ i)
    rw [hfirst] at hle
    exact (WithTop.coe_le_coe.mpr htime).trans hle
  have hfloor := patientWithdrawalFloor_le_terminalPayoffLimit_of_not_before
    reward times time i hbefore
  have houtcome := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq times first hfirst
  have hcoalition : cappedClockChildCoalition ({i} : Finset ι) = {some i} := by
    simp [cappedClockChildCoalition]
    rfl
  rw [patientWithdrawalGainFloor, deadlineSecurityGainFloor_singletonWithRestart,
    patientWithdrawalTerminalGain]
  simpa [quittingPureClockTerminalPayoff, houtcome, hsingleton, hcoalition] using
    sub_le_sub_right hfloor
      (reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i))

end GameTheory
