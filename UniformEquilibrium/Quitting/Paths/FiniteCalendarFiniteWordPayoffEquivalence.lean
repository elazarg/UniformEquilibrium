import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Root.FiniteRootWordSequenceBridge

/-! # Exact finite-word representation of finite-calendar quitting payoffs

A finite timing profile is its chronological word of live product roots followed
by the literal all-Continue profile.  Consequently the finite-calendar raw
payoff image, the finite-root-word payoff image with zero tail, and the actual
behavioral terminal-payoff image satisfy exactly the same predicates.  No
continuity or cap-preservation statement is used here.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The chronological root word of a mixed finite timing profile. -/
def quittingFiniteDeadlineTimingRootWord
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    List (ι → PMF Bool) :=
  List.ofFn fun time : Fin deadline =>
    quittingProfileLiveRoot reward
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) time.val

omit [DecidableEq ι] [Nonempty ι] in
@[simp]
theorem quittingFiniteDeadlineTimingRootWord_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    (quittingFiniteDeadlineTimingRootWord reward deadline mixed).length = deadline := by
  exact List.length_ofFn

/-- The chronological root word obtained directly from a finite-calendar raw
point by decoding each player's simplex coordinate. -/
def quittingFiniteCalendarRootWord
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    List (ι → PMF Bool) :=
  quittingFiniteDeadlineTimingRootWord reward deadline fun who =>
    Math.ProbabilityMassFunction.stdSimplexEquiv.symm (x who)

omit [DecidableEq ι] [Nonempty ι] in
@[simp]
theorem quittingFiniteCalendarRootWord_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    (quittingFiniteCalendarRootWord reward deadline x).length = deadline := by
  exact quittingFiniteDeadlineTimingRootWord_length reward deadline _

omit [DecidableEq ι] [Nonempty ι] in
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

/-- Every finite-calendar raw payoff is the zero-tail payoff of an explicitly
produced finite chronological root word of the same deadline. -/
theorem quittingFiniteCalendarRawPayoff_eq_finiteRootWordPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    quittingFiniteCalendarRawPayoff reward deadline x =
      quittingFiniteRootWordPayoff reward
        (quittingFiniteCalendarRootWord reward deadline x) 0 := by
  let mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline) := fun who =>
    Math.ProbabilityMassFunction.stdSimplexEquiv.symm (x who)
  have hmap := quittingFiniteDeadlineTimingPayoffMap_stdSimplexEquiv
    reward deadline mixed
  have hrecover :
      (fun who => Math.ProbabilityMassFunction.stdSimplexEquiv (mixed who)) = x := by
    funext who
    exact Math.ProbabilityMassFunction.stdSimplexEquiv.apply_symm_apply (x who)
  rw [hrecover] at hmap
  rw [quittingFiniteCalendarRawPayoff_eq_timingPayoffMap, hmap,
    quittingFiniteDeadlineTimingProfile_eq_literalRootStack]
  rw [quittingTerminalPayoff_literalRootStack_eq_wordPayoff]
  have hzero : quittingTerminalPayoff reward
      (quittingAlwaysContinueProfile reward) = 0 := by
    funext who
    exact quittingTerminalPayoff_quittingAlwaysContinue reward who
  dsimp only [mixed]
  unfold quittingFiniteCalendarRootWord
  rw [hzero]

/-- Every predicate on payoff vectors holds on all finite root words with zero
tail exactly when it holds on every actual behavioral terminal payoff. -/
theorem forall_finiteRootWordPayoff_iff_forall_actualTerminalPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (predicate : Payoff ι → Prop) :
    (∀ roots : List (ι → PMF Bool),
      predicate (quittingFiniteRootWordPayoff reward roots 0)) ↔
      ∀ profile : (quittingGame reward).BehaviorProfile,
        predicate (fun observer => quittingTerminalPayoff reward profile observer) := by
  constructor
  · intro hword
    apply (forall_finiteCalendarRawPayoff_iff_forall_actualTerminalPayoff
      reward predicate).mp
    intro x
    rw [quittingFiniteCalendarRawPayoff_eq_finiteRootWordPayoff]
    exact hword _
  · intro hactual roots
    have hprofile := hactual
      (quittingLiteralRootStackProfile reward roots
        (quittingAlwaysContinueProfile reward))
    rw [quittingTerminalPayoff_literalRootStack_eq_wordPayoff] at hprofile
    have hzero : quittingTerminalPayoff reward
        (quittingAlwaysContinueProfile reward) = 0 := by
      funext who
      exact quittingTerminalPayoff_quittingAlwaysContinue reward who
    rwa [hzero] at hprofile

/-- The finite-calendar raw payoff image and the finite-root-word zero-tail
payoff image satisfy exactly the same predicates. -/
theorem forall_finiteCalendarRawPayoff_iff_forall_finiteRootWordPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (predicate : Payoff ι → Prop) :
    (∀ x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction
        (Fintype.card ι * (Fintype.card ι + 1))),
      predicate (quittingFiniteCalendarRawPayoff reward _ x)) ↔
      ∀ roots : List (ι → PMF Bool),
        predicate (quittingFiniteRootWordPayoff reward roots 0) := by
  rw [forall_finiteCalendarRawPayoff_iff_forall_actualTerminalPayoff,
    forall_finiteRootWordPayoff_iff_forall_actualTerminalPayoff]

end GameTheory
