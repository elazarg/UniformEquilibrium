import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalMixedRestartCore
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMixedMarginal

/-! # Evaluated security specialization of the shared private mixed-restart core -/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The reward-selected evaluated restart delegates to the shared private-law core. -/
theorem deadlineSecurityMixedPrivateReplacement_integratedGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    max advanceWeight withdrawalWeight *
      (quittingStoppingLawEvaluatedPayoff reward evaluation
          (deadlineSecurityMixedChildParentStoppingLaws reward childLaws outsideLaw i
            advanceWeight withdrawalWeight hadvance hwithdrawal) (some i) -
        quittingStoppingLawEvaluatedPayoff reward evaluation
          (quietParentStoppingLaws childLaws) (some i)) =
      expect (cappedClockIndependentSample childLaws outsideLaw)
        (fun sample => advanceWeight *
            cappedClockActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i +
          withdrawalWeight *
            deadlineSecurityActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i) := by
  exact deadlineSecurityMixedPrivateReplacement_integratedGainWithRestart reward
    (deadlineSecurityEvaluatedRestartFamily reward i)
      evaluation evaluation_nonneg evaluation_antitone childLaws outsideLaw i
      advanceWeight withdrawalWeight hadvance hwithdrawal

end GameTheory
