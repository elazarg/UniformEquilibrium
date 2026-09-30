import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalRaw
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalProductLaw

/-!
# Actual private patient-withdrawal clock laws

Every finite delay is a literal complete private replacement. It observes
only the owner's original clock and an independently sampled outsider replica.
The payoff limit is separate from the weak limit of these clock laws.
-/

noncomputable section

namespace GameTheory

open _root_.Math Math.PMFProduct

variable {ι : Type}

/-- Keep earlier own clocks; otherwise restart strictly after the deadline
when the singleton reward is nonnegative, and use Never when it is negative.
The delay parameter is offset by one so every restart is strictly later. -/
def patientWithdrawalClock
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (delay : ℕ) (source deadline : Option ℕ) : Option ℕ :=
  match deadline with
  | none => source
  | some time =>
      if quittingStoppingTimeValue source < (time : WithTop ℕ) then source
      else if 0 ≤ reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
        then some (time + delay + 1) else none

theorem patientWithdrawalClock_none
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (delay : ℕ) (source : Option ℕ) :
    patientWithdrawalClock reward i delay source none = source := rfl

theorem patientWithdrawalClock_some_of_before
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (delay : ℕ) (source : Option ℕ) (time : ℕ)
    (hbefore : quittingStoppingTimeValue source < (time : WithTop ℕ)) :
    patientWithdrawalClock reward i delay source (some time) = source := by
  simp [patientWithdrawalClock, hbefore]

theorem patientWithdrawalClock_some_of_nonnegativeSingleton
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (delay : ℕ) (source : Option ℕ) (time : ℕ)
    (hbefore : ¬ quittingStoppingTimeValue source < (time : WithTop ℕ))
    (hsingleton : 0 ≤
      reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)) :
    patientWithdrawalClock reward i delay source (some time) =
      some (time + delay + 1) := by
  simp [patientWithdrawalClock, hbefore, hsingleton]

theorem patientWithdrawalClock_some_of_negativeSingleton
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (delay : ℕ) (source : Option ℕ) (time : ℕ)
    (hbefore : ¬ quittingStoppingTimeValue source < (time : WithTop ℕ))
    (hsingleton :
      reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) < 0) :
    patientWithdrawalClock reward i delay source (some time) = none := by
  simp [patientWithdrawalClock, hbefore, not_le.mpr hsingleton]

variable [Fintype ι] [DecidableEq ι]

/-- One separate unilateral patient experiment, with outsider Never. -/
def patientWithdrawalParentClocks
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (delay : ℕ) (i : ι) :
    Option ι → Option ℕ :=
  deadlinePrivateChildClocks times i
    (patientWithdrawalClock reward i delay (times i) deadline)

/-- The legal private replacement samples only the owner's original law and
an independent outsider replica; there is no observation of opponent clocks. -/
def patientWithdrawalPrivateReplacementLaw
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (delay : ℕ) (sourceLaw outsideLaw : PMF (Option ℕ)) : PMF (Option ℕ) :=
  sourceLaw.bind fun source => outsideLaw.map
    (fun deadline => patientWithdrawalClock reward i delay source deadline)

/-- Applying the private patient operation to one coordinate of the coupled
sample gives exactly the product with the owner's actual replacement law.
The different child response experiments do not form a correlated profile. -/
theorem patientWithdrawalPrivateReplacement_childProduct
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (delay : ℕ) :
    (pmfPi childLaws).bind (fun times => outsideLaw.map fun deadline =>
      Function.update times i (patientWithdrawalClock reward i delay (times i) deadline)) =
      pmfPi (Function.update childLaws i
        (patientWithdrawalPrivateReplacementLaw reward i delay (childLaws i) outsideLaw)) := by
  have h := pmfPi_bind_privateClockKernel childLaws i
    (fun source => outsideLaw.map fun deadline =>
      patientWithdrawalClock reward i delay source deadline)
  simpa only [patientWithdrawalPrivateReplacementLaw, PMF.map_comp,
    Function.comp_def] using h

end GameTheory
