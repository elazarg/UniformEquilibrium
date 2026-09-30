import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalRestartPointwiseCore
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMixedBehavioral

/-! # Evaluated security specialization of the common restart payoff interface -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The all-evaluation singleton floor selected from the literal reward table. -/
def deadlineSecurityGainFloor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (A : Finset ι) (hA : A.Nonempty) : ℝ :=
  deadlineSecurityGainFloorWithRestart reward
    (min (deadlineWithdrawalSecurityFloor reward i) 0) i A hA

omit [Nonempty ι] in
/-- The raw-table evaluated plan delegates to the common restart payoff interface. -/
theorem deadlineSecurityGainFloor_singleton
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (i : ι) :
    deadlineSecurityGainFloor reward i {i} (Finset.singleton_nonempty i) =
      min (deadlineWithdrawalSecurityFloor reward i) 0 -
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) := by
  exact deadlineSecurityGainFloor_singletonWithRestart reward
    (min (deadlineWithdrawalSecurityFloor reward i) 0) i

/-- The raw-table evaluated plan delegates to the common restart payoff interface. -/
theorem deadlineSecurityActualEvaluatedChildGain_none
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ) (i : ι) :
    deadlineSecurityActualEvaluatedChildGain reward evaluation times none i = 0 := by
  exact deadlineSecurityActualEvaluatedChildGain_noneWithRestart reward
    (deadlineSecurityEvaluatedRestartFamily reward i) evaluation times i

/-- The raw-table evaluated plan delegates to the common restart payoff interface. -/
theorem deadlineSecurityActualEvaluatedChildGain_of_ne
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hne : times i ≠ some time) :
    deadlineSecurityActualEvaluatedChildGain reward evaluation times (some time) i = 0 := by
  exact deadlineSecurityActualEvaluatedChildGain_of_neWithRestart reward
    (deadlineSecurityEvaluatedRestartFamily reward i) evaluation times time i hne

/-- The raw-table evaluated plan delegates to the common restart payoff interface. -/
theorem deadlineSecurityActualEvaluatedChildGain_singleton_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ))
    (hcoalition : quittingEarliestStoppingCoalition times = {i}) :
    evaluation time * deadlineSecurityGainFloor reward i {i}
        (Finset.singleton_nonempty i) ≤
      deadlineSecurityActualEvaluatedChildGain reward evaluation times (some time) i := by
  exact deadlineSecurityActualEvaluatedChildGain_singleton_floorWithRestart reward
    (deadlineSecurityEvaluatedRestartFamily reward i)
    (min (deadlineWithdrawalSecurityFloor reward i) 0)
    evaluation times time i hfirst hcoalition
    (fun date opponents hown hfuture => deadlineSecurityEvaluatedRestartFamily_floor
      reward i date evaluation hnonneg hantitone opponents hown hfuture)

/-- The raw-table evaluated plan delegates to the common restart payoff interface. -/
theorem deadlineSecurityActualEvaluatedChildGain_eq_withdrawal_of_blocker
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ) (time : ℕ) (i blocker : ι)
    (hclock : times i = some time) (hne : blocker ≠ i)
    (hblocker : quittingStoppingTimeValue (times blocker) ≤ (time : WithTop ℕ)) :
    deadlineSecurityActualEvaluatedChildGain reward evaluation times (some time) i =
      deadlineWithdrawalActualEvaluatedChildGain reward evaluation times (some time) i := by
  exact deadlineSecurityActualEvaluatedChildGain_eq_withdrawal_of_blockerWithRestart reward
    (deadlineSecurityEvaluatedRestartFamily reward i)
    evaluation times time i blocker hclock hne hblocker
    (fun date chosen hchosen => deadlineSecurityEvaluatedRestartFamily_before
      reward i date chosen hchosen)

/-- The raw-table evaluated plan delegates to the common restart payoff interface. -/
theorem deadlineSecurityActualEvaluatedChildGain_tie_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ)) :
    evaluation time * deadlineSecurityGainFloor reward i
        (quittingEarliestStoppingCoalition times)
        (quittingEarliestStoppingCoalition_nonempty times) ≤
      deadlineSecurityActualEvaluatedChildGain reward evaluation times (some time) i := by
  exact deadlineSecurityActualEvaluatedChildGain_tie_floorWithRestart reward
    (deadlineSecurityEvaluatedRestartFamily reward i)
    (min (deadlineWithdrawalSecurityFloor reward i) 0)
    evaluation hnonneg hantitone times time i hfirst
    (fun date chosen hchosen => deadlineSecurityEvaluatedRestartFamily_before
      reward i date chosen hchosen)
    (fun date opponents hown hfuture => deadlineSecurityEvaluatedRestartFamily_floor
      reward i date evaluation hnonneg hantitone opponents hown hfuture)

/-- The raw-table evaluated plan delegates to the common restart payoff interface. -/
theorem deadlineSecurityActualEvaluatedChildGain_of_first_lt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hafter : quittingEarliestStoppingValue times < (time : WithTop ℕ)) :
    deadlineSecurityActualEvaluatedChildGain reward evaluation times (some time) i = 0 := by
  exact deadlineSecurityActualEvaluatedChildGain_of_first_ltWithRestart reward
    (deadlineSecurityEvaluatedRestartFamily reward i) evaluation times time i hafter
    (fun date chosen hchosen => deadlineSecurityEvaluatedRestartFamily_before
      reward i date chosen hchosen)

end GameTheory
