import UniformEquilibrium.Quitting.Root.FiniteDeadlineWordRealization
import UniformEquilibrium.Quitting.Root.FiniteRootWordSequenceBridge
import UniformEquilibrium.Quitting.Terminal.StoppingLawCanonicalization

/-! # Exact finite-menu realization of arbitrary literal root words -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The chronological root sequence obtained from a finite word by padding it forever
with the all-Continue root. -/
def quittingFiniteWordRootSequence :
    List (ι → PMF Bool) → ℕ → ι → PMF Bool
  | [], _ => quittingAllContinueRoot
  | root :: _, 0 => root
  | _ :: roots, time + 1 => quittingFiniteWordRootSequence roots time

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingFiniteWordRootSequence_nil
    (time : ℕ) :
    quittingFiniteWordRootSequence ([] : List (ι → PMF Bool)) time =
      quittingAllContinueRoot := by
  cases time <;> rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingFiniteWordRootSequence_cons_zero
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool)) :
    quittingFiniteWordRootSequence (root :: roots) 0 = root := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingFiniteWordRootSequence_cons_succ
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool)) (time : ℕ) :
    quittingFiniteWordRootSequence (root :: roots) (time + 1) =
      quittingFiniteWordRootSequence roots time := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem quittingFiniteWordRootSequence_eq_allContinue_of_length_le
    (roots : List (ι → PMF Bool)) {time : ℕ} (htime : roots.length ≤ time) :
    quittingFiniteWordRootSequence roots time = quittingAllContinueRoot := by
  induction roots generalizing time with
  | nil => simp
  | cons root roots ih =>
      cases time with
      | zero => simp at htime
      | succ time =>
          rw [quittingFiniteWordRootSequence_cons_succ]
          exact ih (by simpa using htime)

omit [DecidableEq ι] in
/-- The padded chronological sequence is literally the original finite root stack over
the all-Continue continuation. -/
theorem quittingRootSequenceProfile_finiteWord_eq_literalRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) :
    quittingRootSequenceProfile reward (quittingFiniteWordRootSequence roots) 0 =
      quittingLiteralRootStackProfile reward roots
        (quittingAlwaysContinueProfile reward) := by
  induction roots with
  | nil =>
      funext player time history
      rfl
  | cons root roots ih =>
      rw [quittingRootSequenceProfile_eq_rootThenContinuation,
        quittingLiteralRootStackProfile_cons]
      simp only [quittingFiniteWordRootSequence_cons_zero, Nat.zero_add]
      congr 1
      have hshift : quittingRootSequenceProfile reward
          (quittingFiniteWordRootSequence (root :: roots)) 1 =
        quittingRootSequenceProfile reward (quittingFiniteWordRootSequence roots) 0 := by
        funext player time history
        simp [quittingRootSequenceProfile, Nat.add_comm]
      rw [hshift, ih]

omit [Fintype ι] [DecidableEq ι] in
theorem quittingTruncatedRoots_finiteWordRootSequence_of_length_le
    (roots : List (ι → PMF Bool)) (deadline : ℕ)
    (hdeadline : roots.length ≤ deadline) :
    quittingTruncatedRoots (quittingFiniteWordRootSequence roots) deadline =
      quittingFiniteWordRootSequence roots := by
  funext time player
  by_cases htime : time < deadline
  · rw [quittingTruncatedRoots_of_lt _ htime]
  · rw [quittingTruncatedRoots_of_le _ (Nat.le_of_not_gt htime)]
    have hall := quittingFiniteWordRootSequence_eq_allContinue_of_length_le
      roots (hdeadline.trans (Nat.le_of_not_gt htime))
    rw [hall]

/-- Every literal finite root word over the all-Continue tail has an exact realization
by independent laws on any date-or-Never menu whose deadline contains the word.  The
realization preserves the complete prescribed/cap semantic pair, not only menu replies. -/
theorem exists_finiteDeadlineTimingProfile_literalRootStack_exact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (deadline : ℕ)
    (hdeadline : roots.length ≤ deadline) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        quittingBehaviorStoppingLaw reward
          (quittingLiteralRootStackProfile reward roots
            (quittingAlwaysContinueProfile reward) who)) ∧
      quittingTerminalSemanticPair reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) =
        quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward roots
            (quittingAlwaysContinueProfile reward)) := by
  let sequence := quittingFiniteWordRootSequence roots
  obtain ⟨mixed, hmixed⟩ :=
    exists_finiteDeadlineTimingLaws_of_truncatedRoots reward sequence deadline
  have htruncated : quittingTruncatedRoots sequence deadline = sequence :=
    quittingTruncatedRoots_finiteWordRootSequence_of_length_le roots deadline hdeadline
  have hprofile : quittingRootSequenceProfile reward sequence 0 =
      quittingLiteralRootStackProfile reward roots
        (quittingAlwaysContinueProfile reward) :=
    quittingRootSequenceProfile_finiteWord_eq_literalRootStack reward roots
  have hlaws : ∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
      quittingBehaviorStoppingLaw reward
        (quittingLiteralRootStackProfile reward roots
          (quittingAlwaysContinueProfile reward) who) := by
    intro who
    simpa only [htruncated, hprofile] using hmixed who
  have hcompact : (fun who => quittingFiniteDeadlineTimingLaw (mixed who)) =
      quittingCompactStoppingLawsOfProfile reward
        (quittingLiteralRootStackProfile reward roots
          (quittingAlwaysContinueProfile reward)) := by
    funext who
    unfold quittingCompactStoppingLawsOfProfile
    apply congrArg Math.Probability.CompactStoppingLaw.ofPMF
    simpa [quittingFiniteDeadlineTimingLaw] using hlaws who
  refine ⟨mixed, hlaws, ?_⟩
  rw [quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile reward
    (quittingLiteralRootStackProfile reward roots
      (quittingAlwaysContinueProfile reward))]
  simp only [quittingFiniteDeadlineTimingProfile, hcompact]

end GameTheory
