/-
Word action of root prefixes on quitting terminal semantics.

Splicing a single product root in front of a behavior profile acts on the
finite-dimensional terminal semantic pair by the explicit prefix map, and on
the complete terminal outcome law by the explicit affine law prefix.  Both
actions are functorial in the obvious way, so splicing a whole *word* of roots
acts by the corresponding fold.  The head of the word is the row played first.

Two consequences are recorded.  First, the semantic pair and the outcome law
of a word-prefixed profile are computed from the tail's pair and law alone, by
folding the finite-dimensional prefix maps over the word.  Second, deleting an
arbitrary window of rows -- replacing it by the all-Continue word of the same
length -- is semantically invisible whenever the tail's best-response envelope
already dominates every singleton quitting reward, and is invisible on the
outcome law unconditionally.
-/
import FableTimeEscapeRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The word of roots spliced in front of a profile -/

/-- Splice a whole word of product roots in front of a behavior profile.  The
head of the word is the row played at date zero. -/
def fableRootWordProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  word.foldr (quittingRootThenContinuationProfile reward) tail

omit [DecidableEq ι] in
@[simp] theorem fableRootWordProfile_nil
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile) :
    fableRootWordProfile reward [] tail = tail := rfl

omit [DecidableEq ι] in
@[simp] theorem fableRootWordProfile_cons
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (word : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) :
    fableRootWordProfile reward (root :: word) tail =
      quittingRootThenContinuationProfile reward root
        (fableRootWordProfile reward word tail) := rfl

/-! ## The semantic pair action of a word -/

/-- **Word action on terminal semantic pairs.**  The literal semantic pair of a
word-prefixed profile is the fold of the finite-dimensional one-root prefix
maps over the word, applied to the tail's semantic pair. -/
theorem fableRootWordProfile_semanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward (fableRootWordProfile reward word tail) =
      word.foldr (quittingTerminalSemanticPrefix reward)
        (quittingTerminalSemanticPair reward tail) := by
  induction word with
  | nil => rfl
  | cons root rest ih =>
      rw [fableRootWordProfile_cons,
        quittingTerminalSemanticPair_rootThenContinuation, ih, List.foldr_cons]

/-! ## The outcome law action of a word -/

/-- **Word action on the complete terminal outcome law.**  The literal terminal
outcome law of a word-prefixed profile is the fold of the explicit affine
one-root law prefix over the word, applied to the tail's law. -/
theorem fableRootWordProfile_outcomeMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalOutcomeMass reward (fableRootWordProfile reward word tail) =
      word.foldr quittingTerminalOutcomeLawPrefix
        (quittingTerminalOutcomeMass reward tail) := by
  induction word with
  | nil => rfl
  | cons root rest ih =>
      rw [fableRootWordProfile_cons, ← quittingTerminalOutcomeLawPrefix_outcomeMass,
        ih, List.foldr_cons]

/-! ## Replicated all-Continue words are the all-Continue iterate -/

omit [DecidableEq ι] in
/-- A word consisting of `stages` copies of the all-Continue root splices to
exactly the `stages`-fold all-Continue prefix iterate. -/
theorem fableRootWordProfile_replicate_allContinueRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile) (stages : ℕ) :
    fableRootWordProfile reward
        (List.replicate stages (quittingAllContinueRoot : ι → PMF Bool)) tail =
      quittingAllContinuePrefixIterate reward tail stages := by
  induction stages with
  | zero => rfl
  | succ stages ih =>
      show quittingRootThenContinuationProfile reward quittingAllContinueRoot
        (fableRootWordProfile reward
          (List.replicate stages (quittingAllContinueRoot : ι → PMF Bool)) tail) = _
      rw [ih]
      rfl

/-! ## Window deletion -/

/-- **Semantic window deletion.**  Replacing an arbitrary word of rows by the
all-Continue word of the same length leaves the terminal semantic pair
literally unchanged, provided the tail's best-response envelope already
dominates every singleton quitting reward. -/
theorem fableRootWordProfile_windowDeletion_pair_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who ≤
      quittingContinuationBestResponseValue reward tail who) :
    quittingTerminalSemanticPair reward
        (fableRootWordProfile reward
          (List.replicate word.length (quittingAllContinueRoot : ι → PMF Bool)) tail) =
      quittingTerminalSemanticPair reward tail := by
  rw [fableRootWordProfile_replicate_allContinueRoot]
  exact quittingTerminalSemanticPair_allContinuePrefixIterate_eq
    reward tail hsolo word.length

/-- **Law window deletion.**  Replacing an arbitrary word of rows by the
all-Continue word of the same length leaves the complete terminal outcome law
literally unchanged.  No envelope hypothesis is used. -/
theorem fableRootWordProfile_windowDeletion_outcomeMass_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalOutcomeMass reward
        (fableRootWordProfile reward
          (List.replicate word.length (quittingAllContinueRoot : ι → PMF Bool)) tail) =
      quittingTerminalOutcomeMass reward tail := by
  rw [fableRootWordProfile_replicate_allContinueRoot]
  exact quittingTerminalOutcomeMass_allContinuePrefix_eq reward tail word.length

/-! ## The total-debt comparison -/

/-- The total-debt infimum over executable behavior profiles lies below the
total semantic debt of any tail's semantic pair.  This is the anchor of the
window-deletion comparison: the hypotheses of the deletion statement are
carried, but the bound itself needs neither of them. -/
theorem fableRootWordProfile_deleteWindow_debtSum_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalDebtSumInf reward ≤
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward tail) := by
  rw [← quittingTerminalDebtSum_eq_terminalSemanticDebtSum (reward := reward) tail]
  exact quittingTerminalDebtSumInf_le (reward := reward) tail

/-- **Window-deletion debt comparison.**  The total-debt infimum lies below the
tail's total semantic debt, and deleting an arbitrary window -- replacing it by
the all-Continue word of the same length -- changes that total semantic debt not
at all, under the envelope domination hypothesis. -/
theorem fableRootWordProfile_deleteWindow_debtSum_comparison
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who ≤
      quittingContinuationBestResponseValue reward tail who) :
    quittingTerminalDebtSumInf reward ≤
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward tail) ∧
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (fableRootWordProfile reward
            (List.replicate word.length (quittingAllContinueRoot : ι → PMF Bool)) tail)) =
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward tail) :=
  ⟨fableRootWordProfile_deleteWindow_debtSum_ge reward tail,
    congrArg quittingTerminalSemanticDebtSum
      (fableRootWordProfile_windowDeletion_pair_eq reward word tail hsolo)⟩

end GameTheory
