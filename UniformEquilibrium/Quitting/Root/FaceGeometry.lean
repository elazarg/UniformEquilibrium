/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.Bool
import UniformEquilibrium.Quitting.Root.SuccessorCertificate
import UniformEquilibrium.Quitting.Stationary.LiveMass

/-!
# Exact face geometry of a quitting-game root

Unit opponent Continue mass forces every displayed opponent marginal to be
pure Continue.  On that face, the selected player's pure endpoints reduce to
its singleton quitting reward and its declared continuation payoff.  The
zero-exercise-premium face therefore gives singleton domination, with equality
when exact root Nash and positive own Quit mass provide the reverse endpoint
inequality.

Two distinct unit opponent-Continue faces determine the all-Continue root.
These facts concern only a finite root and its continuation payoff; no
terminal semantic carrier or minimum-debt hypothesis is involved.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Positive immediate-exercise premium at a quitting root. -/
def quittingRootExercisePremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) : ℝ :=
  max 0 (quittingRootEndpointDifference reward tail root who)

theorem quittingRootExercisePremium_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    0 ≤ quittingRootExercisePremium reward tail root who :=
  le_max_left _ _

/-- An opponent's displayed Quit probability is bounded by the absorption
hazard seen after forcing the selected player to Continue. -/
theorem quittingRoot_quitProbability_le_opponentAbsorptionMass_of_ne
    (root : ι → PMF Bool) {who other : ι} (hne : other ≠ who) :
    (root other true).toReal ≤
      quittingRootOpponentAbsorptionMass root who := by
  have hcontinue :=
    quittingRootOpponentContinueMass_le_continueProbability_of_ne root hne
  have hsum := quittingRoot_continueProbability_add_quitProbability root other
  rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass] at hcontinue
  linarith

/-- Unit opponent survival forces every displayed opponent to Continue
purely. -/
theorem quittingRoot_opponents_pureContinue_of_opponentContinueMass_eq_one
    (root : ι → PMF Bool) (who : ι)
    (hface : quittingRootOpponentContinueMass root who = 1) :
    ∀ other, other ≠ who → root other = PMF.pure false := by
  have habs : quittingRootOpponentAbsorptionMass root who = 0 := by
    have hcomplement :=
      quittingRootOpponentContinueMass_eq_one_sub_absorptionMass root who
    linarith
  intro other hne
  have hle :=
    quittingRoot_quitProbability_le_opponentAbsorptionMass_of_ne root hne
  rw [habs] at hle
  have htrueReal : (root other true).toReal = 0 :=
    le_antisymm hle ENNReal.toReal_nonneg
  exact Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
    (root other) htrueReal

/-- When every displayed opponent Continues purely, the selected player's
two endpoints are its singleton reward and its declared continuation
coordinate. -/
theorem quittingRoot_endpoints_eq_singleton_tail_of_opponents_pureContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hpure : ∀ other, other ≠ who → root other = PMF.pure false) :
    quittingRootQuitPayoff reward tail root who =
        reward (quittingSingletonTerminal who) who ∧
      quittingRootContinuePayoff reward tail root who = tail who := by
  constructor
  · unfold quittingRootQuitPayoff
    have hroot : Function.update root who (PMF.pure true) =
        Function.update (quittingAllContinueRoot : ι → PMF Bool) who
          (PMF.pure true) := by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp
      · simp only [Function.update_of_ne hplayer]
        simpa [quittingAllContinueRoot] using hpure player hplayer
    rw [hroot]
    exact quittingRootQuitPayoff_allContinueRoot reward tail who
  · unfold quittingRootContinuePayoff
    have hroot : Function.update root who (PMF.pure false) =
        (quittingAllContinueRoot : ι → PMF Bool) := by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp [quittingAllContinueRoot]
      · rw [Function.update_of_ne hplayer]
        simpa [quittingAllContinueRoot] using hpure player hplayer
    rw [hroot]
    have hself :
        Function.update (quittingAllContinueRoot : ι → PMF Bool) who
            (PMF.pure false) = quittingAllContinueRoot := by
      exact Function.update_eq_self who quittingAllContinueRoot
    rw [← hself]
    simpa only [quittingRootContinuePayoff] using
      (quittingRootContinuePayoff_allContinueRoot reward tail who)

/-- The exact unit-survival, zero-premium face forces the singleton quitting
reward below the declared continuation coordinate. -/
theorem quittingRoot_singleton_le_of_face
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hface : quittingRootOpponentContinueMass root who = 1 ∧
      quittingRootExercisePremium reward tail root who = 0) :
    reward (quittingSingletonTerminal who) who ≤ tail who := by
  have hpure :=
    quittingRoot_opponents_pureContinue_of_opponentContinueMass_eq_one
      root who hface.1
  have hendpoints :=
    quittingRoot_endpoints_eq_singleton_tail_of_opponents_pureContinue
      reward tail root who hpure
  have hpremium : quittingRootEndpointDifference reward tail root who ≤ 0 :=
    max_eq_left_iff.mp (by
      simpa [quittingRootExercisePremium] using hface.2.symm)
  simpa [quittingRootEndpointDifference, hendpoints.1, hendpoints.2] using
    hpremium

/-- On the exact face, the reverse endpoint inequality upgrades singleton
domination to equality. -/
theorem quittingRoot_singleton_eq_of_face_of_endpointDifference_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hface : quittingRootOpponentContinueMass root who = 1 ∧
      quittingRootExercisePremium reward tail root who = 0)
    (hdiff : 0 ≤ quittingRootEndpointDifference reward tail root who) :
    reward (quittingSingletonTerminal who) who = tail who := by
  have hpure :=
    quittingRoot_opponents_pureContinue_of_opponentContinueMass_eq_one
      root who hface.1
  have hendpoints :=
    quittingRoot_endpoints_eq_singleton_tail_of_opponents_pureContinue
      reward tail root who hpure
  have hpremium : quittingRootEndpointDifference reward tail root who ≤ 0 :=
    max_eq_left_iff.mp (by
      simpa [quittingRootExercisePremium] using hface.2.symm)
  have hzero : quittingRootEndpointDifference reward tail root who = 0 :=
    le_antisymm hpremium hdiff
  simpa [quittingRootEndpointDifference, hendpoints.1, hendpoints.2,
    sub_eq_zero] using hzero

/-- At an exact Nash root, positive own Quit mass supplies the reverse
endpoint inequality needed for singleton equality on the exact face. -/
theorem quittingRoot_singleton_eq_of_face_of_quit_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (who : ι)
    (hface : quittingRootOpponentContinueMass root who = 1 ∧
      quittingRootExercisePremium reward tail root who = 0)
    (hquit : 0 < (root who true).toReal) :
    reward (quittingSingletonTerminal who) who = tail who := by
  have hendpoint : IsεQuittingRootEndpointNash reward tail 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).mpr hnash
  have hdiff : 0 ≤ quittingRootEndpointDifference reward tail root who := by
    have hproduct := (hendpoint who).2
    simp only [neg_zero] at hproduct
    exact nonneg_of_mul_nonneg_left
      (by simpa [mul_comm] using hproduct) hquit
  exact quittingRoot_singleton_eq_of_face_of_endpointDifference_nonneg
    reward tail root who hface hdiff

/-- Unit opponent-survival faces at two distinct coordinates force the
entire displayed root to be all-Continue. -/
theorem quittingRoot_eq_allContinue_of_two_opponentContinueMass_eq_one
    (root : ι → PMF Bool) {first second : ι}
    (hdistinct : first ≠ second)
    (hfirst : quittingRootOpponentContinueMass root first = 1)
    (hsecond : quittingRootOpponentContinueMass root second = 1) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  funext player
  by_cases hplayer : player = first
  · subst player
    have hpure :=
      quittingRoot_opponents_pureContinue_of_opponentContinueMass_eq_one
        root second hsecond first hdistinct
    simpa [quittingAllContinueRoot] using hpure
  · have hpure :=
      quittingRoot_opponents_pureContinue_of_opponentContinueMass_eq_one
        root first hfirst player hplayer
    simpa [quittingAllContinueRoot] using hpure

end GameTheory
