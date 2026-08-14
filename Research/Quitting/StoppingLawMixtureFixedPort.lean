/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEqualityStratum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawDebtConvexity

/-!
# Fixed terminal ports under stopping-law mixtures

Complete stopping-law mixing is projective at internal dates: affine
survival and stopping fluxes are divided to recover the live conditional
hazard.  At time zero the survival denominator is one, so the root hazard is
affine without a denominator.  In particular, equal endpoint roots remain
equal along the mixture.

Combining this root fact with payoff affinity and debt rigidity gives an
exact fixed-port theorem.  If two one-player endpoint profiles have the same
terminal payoff/root/debt port and lie on a common minimum-total-debt fiber,
then their whole stopping-law segment has that same port.  The zero-debt face
is an important specialization requiring no separate minimum hypothesis.

This is a conditional repair chart: it preserves a fixed port once two
distinct realizations in the same port fiber have been found.  It does not
produce those two realizations or preserve an entire marked cylinder.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.ProbabilityMassFunction
open Math.Probability.DiscreteHazard
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The reconstructed conditional hazard satisfies the exact homogeneous
flux equation, including on zero-survival rows. -/
theorem scalarHazard_convexMix_stop_mul_mixedSurvival
    (source target : ScalarHazard) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) (time : ℕ) :
    (ScalarHazard.convexMix source target lambda hlambda0 hlambda1).stop time *
        ScalarHazard.mixedSurvival source target lambda time =
      ScalarHazard.mixedStopMass source target lambda time := by
  by_cases hzero : ScalarHazard.mixedSurvival source target lambda time = 0
  · have hnonneg := ScalarHazard.mixedStopMass_nonneg source target lambda
      hlambda0 hlambda1 time
    have hle := ScalarHazard.mixedStopMass_le_mixedSurvival source target lambda
      hlambda0 hlambda1 time
    rw [hzero] at hle ⊢
    have hmass : ScalarHazard.mixedStopMass source target lambda time = 0 := by
      linarith
    rw [hmass]
    ring
  · rw [show (ScalarHazard.convexMix source target lambda
          hlambda0 hlambda1).stop time =
        ScalarHazard.mixedStopMass source target lambda time /
          ScalarHazard.mixedSurvival source target lambda time by
      simp [ScalarHazard.convexMix, hzero]]
    field_simp

/-- At the initial date the survival denominator is one, so the mixed hazard
itself—not only its stopping flux—is affine. -/
theorem scalarHazard_convexMix_stop_zero_eq_chord
    (source target : ScalarHazard) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (ScalarHazard.convexMix source target lambda hlambda0 hlambda1).stop 0 =
      (1 - lambda) * source.stop 0 + lambda * target.stop 0 := by
  simpa [ScalarHazard.mixedSurvival, ScalarHazard.mixedStopMass,
    ScalarHazard.stopMass, ScalarHazard.survival_zero] using
    scalarHazard_convexMix_stop_mul_mixedSurvival source target lambda
      hlambda0 hlambda1 0

/-- More generally, a common conditional hazard at a positive mixed-survival
date is a projective face and is preserved exactly by law mixing. -/
theorem scalarHazard_convexMix_stop_eq_of_endpoint_stop_eq
    (source target : ScalarHazard) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) (time : ℕ)
    (hsurvival : ScalarHazard.mixedSurvival source target lambda time ≠ 0)
    (hstop : source.stop time = target.stop time) :
    (ScalarHazard.convexMix source target lambda hlambda0 hlambda1).stop time =
      source.stop time := by
  have hflux := scalarHazard_convexMix_stop_mul_mixedSurvival source target lambda
    hlambda0 hlambda1 time
  have hmass : ScalarHazard.mixedStopMass source target lambda time =
      ScalarHazard.mixedSurvival source target lambda time * source.stop time := by
    simp only [ScalarHazard.mixedStopMass, ScalarHazard.mixedSurvival,
      ScalarHazard.stopMass, hstop]
    ring
  rw [hmass] at hflux
  have hproduct :
      ((ScalarHazard.convexMix source target lambda hlambda0 hlambda1).stop time -
          source.stop time) *
        ScalarHazard.mixedSurvival source target lambda time = 0 := by
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hsurvival)

/-- Equal time-zero Boolean roots remain literally equal under complete
stopping-law mixing. -/
theorem booleanHazard_convexMix_zero_eq_of_eq
    (source target : BooleanHazard) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hroot : source 0 = target 0) :
    BooleanHazard.convexMix source target lambda hlambda0 hlambda1 0 =
      source 0 := by
  have htargetTrue :
      (target 0 true).toReal = (source 0 true).toReal := by
    rw [← hroot]
  have htrue :
      (BooleanHazard.convexMix source target lambda
          hlambda0 hlambda1 0 true).toReal =
        (source 0 true).toReal := by
    have hchord := scalarHazard_convexMix_stop_zero_eq_chord
      source.toScalar target.toScalar lambda hlambda0 hlambda1
    rw [← BooleanHazard.toScalar_convexMix] at hchord
    change (BooleanHazard.convexMix source target lambda
        hlambda0 hlambda1 0 true).toReal =
      (1 - lambda) * (source 0 true).toReal +
        lambda * (target 0 true).toReal at hchord
    change (target 0 true).toReal = (source 0 true).toReal at htargetTrue
    rw [htargetTrue] at hchord
    nlinarith
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro action
  cases action with
  | false =>
      have hmixedSum := continue_add_stop
        (BooleanHazard.convexMix source target lambda hlambda0 hlambda1) 0
      have hsourceSum := continue_add_stop source 0
      unfold continueProbability stopProbability at hmixedSum hsourceSum
      linarith
  | true => exact htrue

/-- The payoff/root/debt coordinates of a behavioral tail at its terminal
port.  The raw Boolean product root is equivalent to the simplex root used by
`QuittingDebtPoint`; keeping it raw avoids an irrelevant representation
conversion in this experiment. -/
abbrev QuittingBehaviorTerminalPort (ι : Type) [Fintype ι] :=
  (Payoff ι × (ι → PMF Bool)) × Payoff ι

def quittingBehaviorTerminalPort
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    QuittingBehaviorTerminalPort ι :=
  ((fun observer => quittingTerminalPayoff reward profile observer,
      quittingProfileLiveRoot reward profile 0),
    fun observer => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) observer)

/-- If the moved player's two endpoint hazards agree at time zero, the full
product root at the terminal port is fixed by their stopping-law mixture. -/
theorem quittingProfileLiveRoot_zero_stoppingLawMixture_eq_of_endpoint_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hroot : quittingBehaviorLiveHazard reward source 0 =
      quittingBehaviorLiveHazard reward target 0) :
    quittingProfileLiveRoot reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1)) 0 =
      quittingProfileLiveRoot reward
        (Function.update profile mover source) 0 := by
  funext player
  unfold quittingProfileLiveRoot
  by_cases hplayer : player = mover
  · subst player
    simp only [Function.update_self,
      quittingStoppingLawMixtureBehaviorStrategy]
    exact booleanHazard_convexMix_zero_eq_of_eq
      (quittingBehaviorLiveHazard reward source)
      (quittingBehaviorLiveHazard reward target)
      lambda hlambda0 hlambda1 hroot
  · simp only [Function.update_of_ne hplayer]

/-- **Fixed minimum-fiber terminal port.**

Suppose two endpoint strategies for one mover have the same time-zero root,
terminal payoff vector, and semantic-debt vector.  If the source is a global
minimum of total terminal debt, the complete stopping-law segment has exactly
the same payoff/root/debt port at every mixture weight. -/
theorem quittingBehaviorTerminalPort_stoppingLawMixture_eq_of_minimumFiber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hroot : quittingBehaviorLiveHazard reward source 0 =
      quittingBehaviorLiveHazard reward target 0)
    (hpayoff : ∀ observer,
      quittingTerminalPayoff reward
          (Function.update profile mover target) observer =
        quittingTerminalPayoff reward
          (Function.update profile mover source) observer)
    (hdebt : ∀ observer,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) observer =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) observer) :
    quittingBehaviorTerminalPort reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1)) =
      quittingBehaviorTerminalPort reward
        (Function.update profile mover source) := by
  let sourcePair := quittingTerminalSemanticPair reward
    (Function.update profile mover source)
  let mixedPair := quittingTerminalSemanticPair reward
    (Function.update profile mover
      (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
        lambda hlambda0 hlambda1))
  have hmixedMinimum : quittingTerminalSemanticDebtSum sourcePair ≤
      quittingTerminalSemanticDebtSum mixedPair := by
    apply hminimum
    dsimp only [mixedPair]
    exact quittingTerminalSemanticPair_mem_carrier reward _
  have hmixedDebtLe : ∀ observer,
      quittingTerminalSemanticDebt mixedPair observer ≤
        quittingTerminalSemanticDebt sourcePair observer := by
    intro observer
    have hconvex := quittingTerminalSemanticDebt_stoppingLawMixture_le
      reward profile mover observer source target lambda hlambda0 hlambda1
        hM hreward
    dsimp only [mixedPair, sourcePair]
    rw [hdebt observer] at hconvex
    nlinarith
  have hmixedPayoff : ∀ observer,
      quittingTerminalPayoff reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1)) observer =
        quittingTerminalPayoff reward
          (Function.update profile mover source) observer := by
    intro observer
    rw [quittingTerminalPayoff_stoppingLawMixture_eq,
      hpayoff observer]
    ring
  have hmixedDebt : ∀ observer,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                lambda hlambda0 hlambda1))) observer =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) observer := by
    intro observer
    dsimp only [mixedPair, sourcePair] at hmixedDebtLe hmixedMinimum
    apply le_antisymm (hmixedDebtLe observer)
    by_contra hnot
    have hstrict : quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                lambda hlambda0 hlambda1))) observer <
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) observer :=
      lt_of_not_ge hnot
    have hsumStrict : quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                lambda hlambda0 hlambda1))) <
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) := by
      unfold quittingTerminalSemanticDebtSum
      apply Finset.sum_lt_sum
      · intro candidate _hcandidate
        exact hmixedDebtLe candidate
      · exact ⟨observer, Finset.mem_univ observer, hstrict⟩
    exact (not_lt_of_ge hmixedMinimum) hsumStrict
  have hmixedRoot :=
    quittingProfileLiveRoot_zero_stoppingLawMixture_eq_of_endpoint_eq
      reward profile mover source target lambda hlambda0 hlambda1 hroot
  unfold quittingBehaviorTerminalPort
  apply Prod.ext
  · apply Prod.ext
    · funext observer
      exact hmixedPayoff observer
    · exact hmixedRoot
  · funext observer
    exact hmixedDebt observer

/-- On the common zero-debt face, the same fixed-port conclusion needs no
separate global-minimum hypothesis. -/
theorem quittingBehaviorTerminalPort_stoppingLawMixture_eq_on_zeroDebtFace
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hroot : quittingBehaviorLiveHazard reward source 0 =
      quittingBehaviorLiveHazard reward target 0)
    (hpayoff : ∀ observer,
      quittingTerminalPayoff reward
          (Function.update profile mover target) observer =
        quittingTerminalPayoff reward
          (Function.update profile mover source) observer)
    (hsourceDebt : ∀ observer, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile mover source)) observer = 0)
    (htargetDebt : ∀ observer, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile mover target)) observer = 0) :
    quittingBehaviorTerminalPort reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1)) =
      quittingBehaviorTerminalPort reward
        (Function.update profile mover source) := by
  have hmixedPayoff : ∀ observer,
      quittingTerminalPayoff reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1)) observer =
        quittingTerminalPayoff reward
          (Function.update profile mover source) observer := by
    intro observer
    rw [quittingTerminalPayoff_stoppingLawMixture_eq,
      hpayoff observer]
    ring
  have hmixedDebt : ∀ observer, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1))) observer = 0 := by
    intro observer
    have hupper := quittingTerminalSemanticDebt_stoppingLawMixture_le
      reward profile mover observer source target lambda hlambda0 hlambda1
        hM hreward
    rw [hsourceDebt observer, htargetDebt observer] at hupper
    have hnonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward
      (quittingTerminalSemanticPair_mem_carrier reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1))) observer
    apply le_antisymm
    · nlinarith
    · exact hnonneg
  have hmixedRoot :=
    quittingProfileLiveRoot_zero_stoppingLawMixture_eq_of_endpoint_eq
      reward profile mover source target lambda hlambda0 hlambda1 hroot
  unfold quittingBehaviorTerminalPort
  apply Prod.ext
  · apply Prod.ext
    · funext observer
      exact hmixedPayoff observer
    · exact hmixedRoot
  · funext observer
    change quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1))) observer =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover source)) observer
    rw [hmixedDebt observer, hsourceDebt observer]

end GameTheory
