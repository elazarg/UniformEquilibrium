import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineTimingGame
import UniformEquilibrium.Quitting.Root.FiniteRootWordSequenceBridge

/-! # The actual chronological root word of a finite timing profile

The profile identity retains every history, the empty calendar, and the literal
all-Continue tail. Payoff and full-cap consumers may simply apply congrArg.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The chronological root word of a mixed finite timing profile. -/
def quittingFiniteDeadlineTimingRootWord
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    List (ι → PMF Bool) :=
  List.ofFn fun time : Fin deadline =>
    quittingProfileLiveRoot reward
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) time.val

omit [DecidableEq ι] in
@[simp]
theorem quittingFiniteDeadlineTimingRootWord_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    (quittingFiniteDeadlineTimingRootWord reward deadline mixed).length = deadline := by
  exact List.length_ofFn

omit [DecidableEq ι] in
/-- A mixed finite timing profile is literally its chronological root word
followed by all-Continue.  This is a profile equality, not only a payoff
identity. -/
theorem quittingFiniteDeadlineTimingProfile_eq_literalRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingFiniteDeadlineTimingProfile reward deadline mixed =
      quittingLiteralRootStackProfile reward
        (quittingFiniteDeadlineTimingRootWord reward deadline mixed)
        (quittingAlwaysContinueProfile reward) := by
  let profile := quittingFiniteDeadlineTimingProfile reward deadline mixed
  let roots := quittingProfileLiveRoot reward profile
  have hcanonical : profile = quittingRootSequenceProfile reward roots 0 := by
    funext who time history
    simp only [quittingRootSequenceProfile, Nat.zero_add, roots, profile,
      quittingProfileLiveRoot, quittingFiniteDeadlineTimingProfile,
      quittingCompactStoppingLawProfile, quittingStoppingLawBehaviorStrategy]
    rfl
  have htail : quittingRootSequenceProfile reward roots deadline =
      quittingAlwaysContinueProfile reward := by
    funext who time history
    change roots (deadline + time) who = PMF.pure false
    have hall := quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
      reward deadline mixed (show deadline ≤ deadline + time by omega)
    change roots (deadline + time) = quittingAllContinueRoot at hall
    rw [hall]
    rfl
  change profile = quittingLiteralRootStackProfile reward
    (List.ofFn fun time : Fin deadline => roots time.val)
    (quittingAlwaysContinueProfile reward)
  rw [hcanonical]
  have hstack := quittingRootSequenceProfile_eq_literalRootStack
    reward roots 0 deadline
  simp only [Nat.zero_add] at hstack
  rw [hstack, htail]

end GameTheory
