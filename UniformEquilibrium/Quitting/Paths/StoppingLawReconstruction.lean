/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.Bool
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingLaw

/-!
# Behavioral reconstruction from a complete stopping law

This module owns the canonical conditional-hazard realization of one complete
live-spine stopping law and its exact stopping-law roundtrip.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open Math.Probability Math.Probability.DiscreteHazard

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- A complete stopping law supported on the first `clockBound` finite dates,
with `none` retained as an additional exact atom. -/
def IsFiniteClockStoppingLaw (clockBound : ℕ)
    (law : PMF (Option ℕ)) : Prop :=
  ∀ choice, law choice ≠ 0 →
    choice = none ∨ ∃ time < clockBound, choice = some time

/-- The canonical behavioral realization of an arbitrary complete stopping
law. -/
def quittingStoppingLawBehaviorStrategy
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota) (law : PMF (Option Nat)) :
    (quittingGame reward).BehaviorStrategy who :=
  fun time _history => (StoppingLaw.toScalarHazard law).toBoolean time

/-- Literal profile reconstructed independently from one complete stopping law
per player. -/
def quittingStoppingLawProfile
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (laws : iota → PMF (Option ℕ)) :
    (quittingGame reward).BehaviorProfile :=
  fun who => quittingStoppingLawBehaviorStrategy reward who (laws who)

omit [DecidableEq iota] in
@[simp] theorem quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota) (law : PMF (Option Nat)) :
    quittingBehaviorStoppingLaw reward
        (quittingStoppingLawBehaviorStrategy reward who law) = law := by
  unfold quittingBehaviorStoppingLaw quittingHazardStoppingLaw
    quittingStoppingLawBehaviorStrategy quittingBehaviorLiveHazard
  rw [ScalarHazard.toScalar_toBoolean,
    StoppingLaw.stoppingLaw_toScalarHazard]

omit [DecidableEq iota] in
@[simp] theorem quittingBehaviorStoppingLaw_stoppingLawProfile
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (laws : iota → PMF (Option ℕ)) (who : iota) :
    quittingBehaviorStoppingLaw reward
        (quittingStoppingLawProfile reward laws who) = laws who := by
  exact quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy
    reward who (laws who)

omit [DecidableEq iota] in
/-- A reconstructed finite clock is literally all Continue at every date at
or after its finite support bound. -/
theorem quittingStoppingLawProfile_liveHazard_eq_allContinue_of_le
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (clockBound : ℕ) (laws : iota → PMF (Option ℕ))
    (hlaws : ∀ who, IsFiniteClockStoppingLaw clockBound (laws who))
    {time : ℕ} (htime : clockBound ≤ time) :
    quittingProfileLiveRoot reward (quittingStoppingLawProfile reward laws) time =
      quittingAllContinueRoot := by
  funext who
  have hfinite : StoppingLaw.finiteMass (laws who) time = 0 := by
    unfold StoppingLaw.finiteMass
    have hzero : laws who (some time) = 0 := by
      by_contra hne
      rcases hlaws who (some time) hne with hnever | ⟨other, hother, heq⟩
      · cases hnever
      · simp only [Option.some.injEq] at heq
        subst other
        omega
    rw [hzero]
    rfl
  change (StoppingLaw.toScalarHazard (laws who)).toBoolean time = PMF.pure false
  apply Math.PMFProduct.eq_pure_false_of_true_toReal_eq_zero
  simp [ScalarHazard.toBoolean, StoppingLaw.toScalarHazard, hfinite]

end GameTheory
