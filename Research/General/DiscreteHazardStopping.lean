/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.BehaviorStoppingLaw
import MathUE.Probability.DiscreteHazardMixture

/-!
# Experimental discrete hazard stopping laws

This is a game-independent façade over the Boolean hazard construction that
currently lives in the quitting-game development.  A `BooleanHazard` is just a
sequence of Bernoulli laws: `true` means stop and `false` means continue.

The file deliberately keeps the implementation delegated to the production
construction.  Its purpose is to test the API which a later extraction into a
probability module should expose, without changing production dependencies.
-/

noncomputable section

namespace MathExperiments
namespace DiscreteHazard

open Filter Math.Probability Math.ProbabilityMassFunction

/-- A discrete-time Boolean hazard: `true` is stopping and `false` is
continuing. -/
abbrev BooleanHazard := ℕ → PMF Bool

/-- Survival through the first `cutoff` decision dates. -/
abbrev survival (hazard : BooleanHazard) (cutoff : ℕ) : ℝ :=
  GameTheory.quittingHazardSurvival hazard cutoff

/-- Mass of never stopping. -/
abbrev neverMass (hazard : BooleanHazard) : ℝ :=
  GameTheory.quittingHazardNeverMass hazard

/-- Mass of first stopping at a specified date. -/
abbrev stopMass (hazard : BooleanHazard) (time : ℕ) : ℝ :=
  GameTheory.quittingHazardStopMass hazard time

/-- The law on stopping dates, with `none` denoting never stopping. -/
abbrev stoppingLaw (hazard : BooleanHazard) : PMF (Option ℕ) :=
  GameTheory.quittingHazardStoppingLaw hazard

/-- The scalar stop probability visible in a Boolean hazard. -/
def stopProbability (hazard : BooleanHazard) (time : ℕ) : ℝ :=
  (hazard time true).toReal

/-- The scalar continuation probability visible in a Boolean hazard. -/
def continueProbability (hazard : BooleanHazard) (time : ℕ) : ℝ :=
  (hazard time false).toReal

theorem continue_add_stop (hazard : BooleanHazard) (time : ℕ) :
    continueProbability hazard time + stopProbability hazard time = 1 :=
  GameTheory.quittingHazard_continue_add_quit hazard time

theorem continue_nonneg (hazard : BooleanHazard) (time : ℕ) :
    0 ≤ continueProbability hazard time :=
  GameTheory.quittingHazard_continue_nonneg hazard time

theorem stop_nonneg (hazard : BooleanHazard) (time : ℕ) :
    0 ≤ stopProbability hazard time :=
  GameTheory.quittingHazard_quit_nonneg hazard time

theorem continue_le_one (hazard : BooleanHazard) (time : ℕ) :
    continueProbability hazard time ≤ 1 :=
  GameTheory.quittingHazard_continue_le_one hazard time

theorem survival_zero (hazard : BooleanHazard) : survival hazard 0 = 1 :=
  GameTheory.quittingHazardSurvival_zero hazard

theorem survival_succ (hazard : BooleanHazard) (cutoff : ℕ) :
    survival hazard (cutoff + 1) =
      survival hazard cutoff * continueProbability hazard cutoff :=
  GameTheory.quittingHazardSurvival_succ hazard cutoff

theorem survival_antitone (hazard : BooleanHazard) : Antitone (survival hazard) :=
  GameTheory.antitone_quittingHazardSurvival hazard

theorem neverMass_nonneg (hazard : BooleanHazard) : 0 ≤ neverMass hazard :=
  GameTheory.quittingHazardNeverMass_nonneg hazard

theorem neverMass_le_survival (hazard : BooleanHazard) (cutoff : ℕ) :
    neverMass hazard ≤ survival hazard cutoff :=
  GameTheory.quittingHazardNeverMass_le_survival hazard cutoff

theorem tendsto_survival_neverMass (hazard : BooleanHazard) :
    Tendsto (survival hazard) atTop (nhds (neverMass hazard)) :=
  GameTheory.tendsto_quittingHazardSurvival_neverMass hazard

theorem stopMass_nonneg (hazard : BooleanHazard) (time : ℕ) :
    0 ≤ stopMass hazard time :=
  GameTheory.quittingHazardStopMass_nonneg hazard time

theorem stopMass_eq_survival_sub_succ (hazard : BooleanHazard) (time : ℕ) :
    stopMass hazard time = survival hazard time - survival hazard (time + 1) :=
  GameTheory.quittingHazardStopMass_eq_survival_sub_succ hazard time

theorem sum_stopMass (hazard : BooleanHazard) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff, stopMass hazard time) = 1 - survival hazard cutoff :=
  GameTheory.sum_quittingHazardStopMass hazard cutoff

theorem hasSum_stopMass (hazard : BooleanHazard) :
    HasSum (stopMass hazard) (1 - neverMass hazard) :=
  GameTheory.hasSum_quittingHazardStopMass hazard

@[simp] theorem stoppingLaw_none_toReal (hazard : BooleanHazard) :
    (stoppingLaw hazard none).toReal = neverMass hazard :=
  GameTheory.quittingHazardStoppingLaw_none_toReal hazard

@[simp] theorem stoppingLaw_some_toReal (hazard : BooleanHazard) (time : ℕ) :
    (stoppingLaw hazard (some time)).toReal = stopMass hazard time :=
  GameTheory.quittingHazardStoppingLaw_some_toReal hazard time

theorem stoppingLaw_toReal_tsum_one (hazard : BooleanHazard) :
    ∑' choice : Option ℕ, (stoppingLaw hazard choice).toReal = 1 :=
  GameTheory.quittingHazardStoppingLaw_toReal_tsum_one hazard

theorem stoppingLaw_expect (hazard : BooleanHazard) (value : Option ℕ → ℝ)
    {M : ℝ} (hvalue : ∀ choice, |value choice| ≤ M) :
    expect (stoppingLaw hazard) value =
      neverMass hazard * value none +
        ∑' time : ℕ, stopMass hazard time * value (some time) :=
  GameTheory.quittingHazardStoppingLaw_expect hazard value hvalue

/-- A scalar stop-probability sequence together with its probability bounds. -/
structure ScalarHazard where
  stop : ℕ → ℝ
  stop_nonneg : ∀ time, 0 ≤ stop time
  stop_le_one : ∀ time, stop time ≤ 1

/-- Turn a scalar hazard into the corresponding Boolean Bernoulli hazard. -/
def ScalarHazard.toBoolean (hazard : ScalarHazard) : BooleanHazard :=
  fun time => Math.Probability.DiscreteHazard.booleanCoin (hazard.stop time)
    (hazard.stop_nonneg time) (hazard.stop_le_one time)

theorem ScalarHazard.toBoolean_stopProbability (hazard : ScalarHazard) (time : ℕ) :
    stopProbability hazard.toBoolean time = hazard.stop time := by
  exact Math.Probability.DiscreteHazard.booleanCoin_true_toReal (hazard.stop time)
    (hazard.stop_nonneg time) (hazard.stop_le_one time)

theorem ScalarHazard.toBoolean_continueProbability (hazard : ScalarHazard) (time : ℕ) :
    continueProbability hazard.toBoolean time = 1 - hazard.stop time := by
  linarith [continue_add_stop hazard.toBoolean time,
    ScalarHazard.toBoolean_stopProbability hazard time]

namespace ScalarHazard

/-- Scalar survival through the first `cutoff` decision dates.  This is the
direct finite-product presentation, independent of the Boolean encoding. -/
def survival (hazard : ScalarHazard) (cutoff : ℕ) : ℝ :=
  ∏ time ∈ Finset.range cutoff, (1 - hazard.stop time)

/-- Scalar mass of first stopping at `time`. -/
def stopMass (hazard : ScalarHazard) (time : ℕ) : ℝ :=
  hazard.survival time * hazard.stop time

/-- Scalar never-stop mass.  Its implementation delegates the countable
normalization proof to the Boolean PMF construction. -/
abbrev neverMass (hazard : ScalarHazard) : ℝ :=
  DiscreteHazard.neverMass hazard.toBoolean

/-- The stopping-time law associated to a scalar hazard. -/
abbrev stoppingLaw (hazard : ScalarHazard) : PMF (Option ℕ) :=
  DiscreteHazard.stoppingLaw hazard.toBoolean

theorem survival_eq_boolean (hazard : ScalarHazard) (cutoff : ℕ) :
    hazard.survival cutoff = DiscreteHazard.survival hazard.toBoolean cutoff := by
  unfold survival DiscreteHazard.survival GameTheory.quittingHazardSurvival
  apply Finset.prod_congr rfl
  intro time _
  simpa only [continueProbability, Nat.zero_add] using
    (hazard.toBoolean_continueProbability time).symm

theorem stopMass_eq_boolean (hazard : ScalarHazard) (time : ℕ) :
    hazard.stopMass time = DiscreteHazard.stopMass hazard.toBoolean time := by
  rw [stopMass, survival_eq_boolean]
  unfold DiscreteHazard.stopMass GameTheory.quittingHazardStopMass
  rw [Math.Probability.DiscreteHazard.ScalarHazard.stopMass]
  congr 1
  · exact Math.Probability.DiscreteHazard.BooleanHazard.survival_eq_scalar
      hazard.toBoolean time
  · exact (hazard.toBoolean_stopProbability time).symm

theorem survival_zero (hazard : ScalarHazard) : hazard.survival 0 = 1 := by
  simp [survival]

theorem survival_succ (hazard : ScalarHazard) (cutoff : ℕ) :
    hazard.survival (cutoff + 1) =
      hazard.survival cutoff * (1 - hazard.stop cutoff) := by
  simp [survival, Finset.prod_range_succ]

theorem survival_nonneg (hazard : ScalarHazard) (cutoff : ℕ) :
    0 ≤ hazard.survival cutoff := by
  rw [survival_eq_boolean]
  exact GameTheory.quittingHazardSurvival_nonneg hazard.toBoolean cutoff

theorem survival_le_one (hazard : ScalarHazard) (cutoff : ℕ) :
    hazard.survival cutoff ≤ 1 := by
  rw [survival_eq_boolean]
  exact GameTheory.quittingHazardSurvival_le_one hazard.toBoolean cutoff

theorem survival_antitone (hazard : ScalarHazard) : Antitone hazard.survival := by
  intro m n hmn
  rw [survival_eq_boolean, survival_eq_boolean]
  exact DiscreteHazard.survival_antitone hazard.toBoolean hmn

theorem stopMass_nonneg (hazard : ScalarHazard) (time : ℕ) :
    0 ≤ hazard.stopMass time := by
  rw [stopMass_eq_boolean]
  exact DiscreteHazard.stopMass_nonneg hazard.toBoolean time

theorem stopMass_eq_survival_sub_succ (hazard : ScalarHazard) (time : ℕ) :
    hazard.stopMass time = hazard.survival time - hazard.survival (time + 1) := by
  rw [stopMass_eq_boolean, survival_eq_boolean, survival_eq_boolean]
  exact DiscreteHazard.stopMass_eq_survival_sub_succ hazard.toBoolean time

theorem sum_stopMass (hazard : ScalarHazard) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff, hazard.stopMass time) =
      1 - hazard.survival cutoff := by
  rw [show (∑ time ∈ Finset.range cutoff, hazard.stopMass time) =
      ∑ time ∈ Finset.range cutoff, DiscreteHazard.stopMass hazard.toBoolean time by
    apply Finset.sum_congr rfl
    intro time _
    exact hazard.stopMass_eq_boolean time,
    hazard.survival_eq_boolean]
  exact DiscreteHazard.sum_stopMass hazard.toBoolean cutoff

theorem hasSum_stopMass (hazard : ScalarHazard) :
    HasSum hazard.stopMass (1 - hazard.neverMass) := by
  rw [show hazard.stopMass = DiscreteHazard.stopMass hazard.toBoolean by
    funext time
    exact hazard.stopMass_eq_boolean time]
  exact DiscreteHazard.hasSum_stopMass hazard.toBoolean

@[simp] theorem stoppingLaw_none_toReal (hazard : ScalarHazard) :
    (hazard.stoppingLaw none).toReal = hazard.neverMass :=
  DiscreteHazard.stoppingLaw_none_toReal hazard.toBoolean

@[simp] theorem stoppingLaw_some_toReal (hazard : ScalarHazard) (time : ℕ) :
    (hazard.stoppingLaw (some time)).toReal = hazard.stopMass time := by
  rw [DiscreteHazard.stoppingLaw_some_toReal, ← hazard.stopMass_eq_boolean]

theorem stoppingLaw_expect (hazard : ScalarHazard) (value : Option ℕ → ℝ)
    {M : ℝ} (hvalue : ∀ choice, |value choice| ≤ M) :
    expect hazard.stoppingLaw value =
      hazard.neverMass * value none +
        ∑' time : ℕ, hazard.stopMass time * value (some time) := by
  rw [DiscreteHazard.stoppingLaw_expect hazard.toBoolean value hvalue]
  congr 1
  apply tsum_congr
  intro time
  rw [hazard.stopMass_eq_boolean]

end ScalarHazard

/-- Deterministically attach a mark to every finite stopping date. -/
def markedStoppingLaw {Mark : Type} (hazard : BooleanHazard) (mark : ℕ → Mark) :
    PMF (Option (ℕ × Mark)) :=
  (stoppingLaw hazard).map (Option.map fun time => (time, mark time))

@[simp] theorem markedStoppingLaw_none_toReal {Mark : Type} (hazard : BooleanHazard)
    (mark : ℕ → Mark) :
    (markedStoppingLaw hazard mark none).toReal = neverMass hazard := by
  rw [markedStoppingLaw, PMF.map_apply]
  simp

@[simp] theorem markedStoppingLaw_some_toReal {Mark : Type} (hazard : BooleanHazard)
    (mark : ℕ → Mark) (time : ℕ) :
    (markedStoppingLaw hazard mark (some (time, mark time))).toReal =
      stopMass hazard time := by
  rw [markedStoppingLaw, PMF.map_apply]
  simp

/-- Expectations under a deterministically marked law reduce to the unmarked
stopping law.  This is the interface needed when a stopping action has a
time-dependent terminal label. -/
theorem markedStoppingLaw_expect {Mark : Type} (hazard : BooleanHazard)
    (mark : ℕ → Mark) (value : Option (ℕ × Mark) → ℝ) :
    expect (markedStoppingLaw hazard mark) value =
      expect (stoppingLaw hazard)
        (fun choice => value (Option.map (fun time => (time, mark time)) choice)) := by
  rw [markedStoppingLaw, expect_map]

namespace ScalarHazard

/-- Deterministically mark the finite atoms of a scalar stopping law. -/
abbrev markedStoppingLaw {Mark : Type} (hazard : ScalarHazard) (mark : ℕ → Mark) :
    PMF (Option (ℕ × Mark)) :=
  DiscreteHazard.markedStoppingLaw hazard.toBoolean mark

@[simp] theorem markedStoppingLaw_none_toReal {Mark : Type} (hazard : ScalarHazard)
    (mark : ℕ → Mark) :
    (hazard.markedStoppingLaw mark none).toReal = hazard.neverMass :=
  DiscreteHazard.markedStoppingLaw_none_toReal hazard.toBoolean mark

@[simp] theorem markedStoppingLaw_some_toReal {Mark : Type} (hazard : ScalarHazard)
    (mark : ℕ → Mark) (time : ℕ) :
    (hazard.markedStoppingLaw mark (some (time, mark time))).toReal =
      hazard.stopMass time := by
  rw [DiscreteHazard.markedStoppingLaw_some_toReal, ← hazard.stopMass_eq_boolean]

theorem markedStoppingLaw_expect {Mark : Type} (hazard : ScalarHazard)
    (mark : ℕ → Mark) (value : Option (ℕ × Mark) → ℝ) :
    expect (hazard.markedStoppingLaw mark) value =
      expect hazard.stoppingLaw
        (fun choice => value (Option.map (fun time => (time, mark time)) choice)) :=
  DiscreteHazard.markedStoppingLaw_expect hazard.toBoolean mark value

end ScalarHazard

end DiscreteHazard
end MathExperiments

/-! ## Evaluation audit -/
