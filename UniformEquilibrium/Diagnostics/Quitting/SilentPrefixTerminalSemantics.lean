import UniformEquilibrium.Quitting.Paths.RootSequenceSilentPrefix
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveMinimumTwoCutPaidSplice
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryTailSemanticReduction

/-!
# Terminal semantics of a silent root-sequence prefix

The prefix preserves payoff and acts on the unrestricted cap by taking the
coordinatewise maximum with singleton quitting reward.  These semantic facts
sit above the low root-word construction because the literal suffix-pair API
is owned by the diagnostics two-cut layer.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Terminal payoff depends only on the canonical live-root word. -/
theorem quittingTerminalPayoff_eq_of_profileLiveRoot_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (hroots : quittingProfileLiveRoot reward first =
      quittingProfileLiveRoot reward second) (who : ι) :
    quittingTerminalPayoff reward first who =
      quittingTerminalPayoff reward second who := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot, hroots]

/-- The unrestricted behavioral cap depends only on the opponents' canonical
live-root word.  Equality of the full words is a convenient sufficient form. -/
theorem quittingContinuationBestResponseValue_eq_of_profileLiveRoot_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (hroots : quittingProfileLiveRoot reward first =
      quittingProfileLiveRoot reward second) (who : ι) :
    quittingContinuationBestResponseValue reward first who =
      quittingContinuationBestResponseValue reward second who := by
  rw [quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot,
    quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot,
    hroots]

/-- Complete terminal semantics depend only on the canonical live-root word. -/
theorem quittingTerminalSemanticPair_eq_of_profileLiveRoot_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (hroots : quittingProfileLiveRoot reward first =
      quittingProfileLiveRoot reward second) :
    quittingTerminalSemanticPair reward first =
      quittingTerminalSemanticPair reward second := by
  apply Prod.ext
  · funext who
    exact quittingTerminalPayoff_eq_of_profileLiveRoot_eq
      reward first second hroots who
  · funext who
    exact quittingContinuationBestResponseValue_eq_of_profileLiveRoot_eq
      reward first second hroots who

/-- Updating the canonical live-root profile by a literal behavioral strategy
has the same terminal payoff as updating the supplied source profile. -/
theorem quittingTerminalPayoff_update_rootSequenceProfile_profileLiveRoot_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover observer : ι)
    (deviation : (quittingGame reward).BehaviorStrategy mover) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingRootSequenceProfile reward
            (quittingProfileLiveRoot reward profile) 0)
          mover deviation) observer =
      quittingTerminalPayoff reward
        (Function.update profile mover deviation) observer := by
  apply quittingTerminalPayoff_eq_of_profileLiveRoot_eq
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero]

/-- The same literal update has the complete semantic pair of the update made
directly to the supplied source profile. -/
theorem quittingTerminalSemanticPair_update_rootSequenceProfile_profileLiveRoot_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (deviation : (quittingGame reward).BehaviorStrategy mover) :
    quittingTerminalSemanticPair reward
        (Function.update
          (quittingRootSequenceProfile reward
            (quittingProfileLiveRoot reward profile) 0)
          mover deviation) =
      quittingTerminalSemanticPair reward
        (Function.update profile mover deviation) := by
  apply quittingTerminalSemanticPair_eq_of_profileLiveRoot_eq
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero]

/-- In particular, the updated source and canonical profile have the same
unrestricted behavioral debt at every coordinate. -/
theorem quittingTerminalSemanticDebt_update_rootSequenceProfile_profileLiveRoot_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover observer : ι)
    (deviation : (quittingGame reward).BehaviorStrategy mover) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update
            (quittingRootSequenceProfile reward
              (quittingProfileLiveRoot reward profile) 0)
            mover deviation)) observer =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover deviation)) observer := by
  rw [quittingTerminalSemanticPair_update_rootSequenceProfile_profileLiveRoot_eq]

/-- Canonical live-root reading preserves the full terminal semantic pair. -/
theorem quittingTerminalSemanticPair_rootSequenceProfile_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward
          (quittingProfileLiveRoot reward profile) 0) =
      quittingTerminalSemanticPair reward profile := by
  apply Prod.ext
  · funext who
    exact (quittingTerminalPayoff_eq_rootSequence_profileLiveRoot
      reward profile who).symm
  · funext who
    change quittingContinuationBestResponseValue reward
        (quittingRootSequenceProfile reward
          (quittingProfileLiveRoot reward profile) 0) who =
      quittingContinuationBestResponseValue reward profile who
    simpa [quittingRootSequenceBestResponseValue] using
      (quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot
        reward profile who).symm

/-- The semantic pair after the silent row is the source profile's pair. -/
theorem quittingRootSequenceTerminalSemanticPairAt_silentPrefix_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingRootSequenceTerminalSemanticPairAt reward
        (quittingSilentPrefixRoots (quittingProfileLiveRoot reward profile)) 1 =
      quittingTerminalSemanticPair reward profile := by
  unfold quittingRootSequenceTerminalSemanticPairAt
  rw [show (1 : ℕ) = 0 + 1 from rfl,
    quittingRootSequenceProfile_silentPrefix_succ,
    quittingTerminalSemanticPair_rootSequenceProfile_profileLiveRoot]

/-- Semantic pairs at every later cut shift by one under the silent prefix. -/
theorem quittingRootSequenceTerminalSemanticPairAt_silentPrefix_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cut : ℕ) :
    quittingRootSequenceTerminalSemanticPairAt reward
        (quittingSilentPrefixRoots roots) (cut + 1) =
      quittingRootSequenceTerminalSemanticPairAt reward roots cut := by
  unfold quittingRootSequenceTerminalSemanticPairAt
  rw [quittingRootSequenceProfile_silentPrefix_succ]

/-- The silent parent keeps payoff and raises each cap only to singleton reward. -/
theorem quittingRootSequenceTerminalSemanticPairAt_silentPrefix_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingRootSequenceTerminalSemanticPairAt reward
        (quittingSilentPrefixRoots (quittingProfileLiveRoot reward profile)) 0 =
      ((quittingTerminalSemanticPair reward profile).1,
        fun who => max (reward (quittingSingletonTerminal who) who)
          ((quittingTerminalSemanticPair reward profile).2 who)) := by
  rw [quittingRootSequenceTerminalSemanticPairAt_eq_prefix,
    quittingSilentPrefixRoots_zero, quittingTerminalSemanticPrefix_allContinue_eq,
    quittingRootSequenceTerminalSemanticPairAt_silentPrefix_one]

/-- The silent parent has exactly the source profile's terminal payoffs. -/
theorem quittingTerminalPayoff_rootSequence_silentPrefix_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
        (quittingRootSequenceProfile reward
          (quittingSilentPrefixRoots
            (quittingProfileLiveRoot reward profile)) 0) who =
      quittingTerminalPayoff reward profile who :=
  congrFun (congrArg Prod.fst
    (quittingRootSequenceTerminalSemanticPairAt_silentPrefix_zero
      reward profile)) who

end GameTheory
