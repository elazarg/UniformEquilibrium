/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.DeadlineBoundedPureTimeCap
import UniformEquilibrium.Quitting.Terminal.StoppingLawCanonicalization

/-!
# Finite-clock stopping-law canonicalization

Canonical reconstruction of a supplied finite-clock profile is deadline
bounded and preserves its complete terminal semantic pair.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability _root_.Math.Probability.DiscreteHazard
open _root_.Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A common finite clock bound for all complete stopping laws induced by a
behavior profile.  The `Never` atom remains allowed. -/
def HasQuittingFiniteClockBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (clockBound : ℕ) : Prop :=
  ∀ (who : ι) (choice : Option ℕ),
    quittingBehaviorStoppingLaw reward (profile who) choice ≠ 0 →
      choice = none ∨ ∃ time ≤ clockBound, choice = some time

/-- A behavior profile has some common finite stopping-law clock bound. -/
def IsQuittingFiniteClockProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : Prop :=
  ∃ clockBound, HasQuittingFiniteClockBound reward profile clockBound

private theorem stoppingLaw_toScalarHazard_toBoolean_eq_pure_false_of_mass_zero
    (law : PMF (Option ℕ)) (time : ℕ)
    (hmass : law (some time) = 0) :
    (StoppingLaw.toScalarHazard law).toBoolean time = PMF.pure false := by
  apply Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
  simp [ScalarHazard.toBoolean, StoppingLaw.toScalarHazard,
    StoppingLaw.finiteMass, hmass]

/-- Canonicalization from finite-clock stopping laws is deadline bounded and
preserves the complete terminal semantic pair. -/
theorem finiteClock_canonicalized_deadlineBounded_and_semantic_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (clockBound : ℕ)
    (hclock : HasQuittingFiniteClockBound reward profile clockBound) :
    QuittingDeadlineBounded reward
        (quittingStoppingLawCanonicalizeOn reward profile Finset.univ)
        clockBound ∧
      quittingTerminalSemanticPair reward
          (quittingStoppingLawCanonicalizeOn reward profile Finset.univ) =
        quittingTerminalSemanticPair reward profile := by
  constructor
  · intro who time htime
    unfold quittingProfileLiveRoot quittingStoppingLawCanonicalizeOn
    simp only [Finset.mem_univ, if_true]
    unfold quittingStoppingLawBehaviorStrategy
    apply stoppingLaw_toScalarHazard_toBoolean_eq_pure_false_of_mass_zero
    by_contra hmass
    rcases hclock who (some time) hmass with hnever | ⟨date, hdate, heq⟩
    · simp at hnever
    · cases Option.some.inj heq
      omega
  · rw [quittingStoppingLawCanonicalizeOn_univ_eq_compactStoppingLawProfile]
    exact (quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile
      reward profile).symm

end GameTheory
