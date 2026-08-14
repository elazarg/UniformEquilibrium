/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawDebtConvexity
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawMinimumTransfer
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalPacketSimpleFallbackCounterexample

/-!
# Witness strata for stopping-law mixture directions

A complete stopping-law mixture is affine for every fixed unilateral
deviation, but a best-response value is a supremum of those affine functions.
This file isolates the resulting geometry.

For a player different from the player whose stopping law is mixed:

* the convexity defect of the best-response envelope is bounded by the
  weighted endpoint regrets of **any one common deviation**;
* a deviation which is optimal at both endpoints remains optimal on the
  whole mixture segment, so the best-response value and semantic debt are
  exactly affine there; and
* an approximately common endpoint witness gives a quantitative approximate
  affine chart.

Thus the nonlinearity is localized: it is precisely the cost of switching
active best-response witnesses.  No attainment is assumed; this matters for
general time-varying quitting profiles, where the pure-time supremum need not
be attained.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The convexity defect along a stopping-law mixture is no larger than the
weighted endpoint regrets of any fixed common deviation.  This is the exact
certificate behind the phrase "a witness switch is the only nonlinearity". -/
theorem quittingContinuationBestResponseValue_stoppingLawMixture_chordGap_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (1 - lambda) * quittingContinuationBestResponseValue reward
          (Function.update profile mover source) observer +
        lambda * quittingContinuationBestResponseValue reward
          (Function.update profile mover target) observer -
      quittingContinuationBestResponseValue reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1)) observer ≤
    (1 - lambda) *
        (quittingContinuationBestResponseValue reward
            (Function.update profile mover source) observer -
          quittingTerminalPayoff reward
            (Function.update (Function.update profile mover source)
              observer deviation) observer) +
      lambda *
        (quittingContinuationBestResponseValue reward
            (Function.update profile mover target) observer -
          quittingTerminalPayoff reward
            (Function.update (Function.update profile mover target)
              observer deviation) observer) := by
  let mixed := quittingStoppingLawMixtureBehaviorStrategy reward mover
    source target lambda hlambda0 hlambda1
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update profile observer deviation) mover observer
      source target lambda hlambda0 hlambda1
  have hcommuteSource :
      Function.update (Function.update profile observer deviation) mover source =
        Function.update (Function.update profile mover source) observer deviation :=
    Function.update_comm hne deviation source profile
  have hcommuteTarget :
      Function.update (Function.update profile observer deviation) mover target =
        Function.update (Function.update profile mover target) observer deviation :=
    Function.update_comm hne deviation target profile
  have hcommuteMixed :
      Function.update (Function.update profile observer deviation) mover mixed =
        Function.update (Function.update profile mover mixed) observer deviation :=
    Function.update_comm hne deviation mixed profile
  dsimp only [mixed] at hcommuteMixed
  rw [hcommuteMixed, hcommuteSource, hcommuteTarget] at haffine
  have hlower :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1))
        observer deviation
  nlinarith

/-- If one deviation is best at both endpoints, it stays best throughout the
complete stopping-law mixture segment.  Equivalently, the best-response
envelope is exactly affine on this common-witness stratum. -/
theorem quittingContinuationBestResponseValue_stoppingLawMixture_eq_of_commonWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hsource : quittingTerminalPayoff reward
        (Function.update (Function.update profile mover source)
          observer deviation) observer =
      quittingContinuationBestResponseValue reward
        (Function.update profile mover source) observer)
    (htarget : quittingTerminalPayoff reward
        (Function.update (Function.update profile mover target)
          observer deviation) observer =
      quittingContinuationBestResponseValue reward
        (Function.update profile mover target) observer) :
    quittingContinuationBestResponseValue reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1)) observer =
      (1 - lambda) * quittingContinuationBestResponseValue reward
          (Function.update profile mover source) observer +
        lambda * quittingContinuationBestResponseValue reward
          (Function.update profile mover target) observer := by
  have hupper :=
    quittingContinuationBestResponseValue_stoppingLawMixture_le
      reward profile mover observer source target lambda hlambda0 hlambda1
  have hdefect :=
    quittingContinuationBestResponseValue_stoppingLawMixture_chordGap_le
      reward profile mover observer hne source target deviation lambda
        hlambda0 hlambda1
  rw [hsource, htarget] at hdefect
  linarith

/-- A common `epsilon`-witness at the endpoints gives an explicit approximate
affinity estimate.  The two endpoint errors are weighted by their actual
mixture masses, so there is no per-date accumulation. -/
theorem quittingContinuationBestResponseValue_stoppingLawMixture_chordGap_le_of_commonApproxWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (sourceError targetError : ℝ)
    (hsource : quittingContinuationBestResponseValue reward
          (Function.update profile mover source) observer ≤
        quittingTerminalPayoff reward
            (Function.update (Function.update profile mover source)
              observer deviation) observer + sourceError)
    (htarget : quittingContinuationBestResponseValue reward
          (Function.update profile mover target) observer ≤
        quittingTerminalPayoff reward
            (Function.update (Function.update profile mover target)
              observer deviation) observer + targetError) :
    (1 - lambda) * quittingContinuationBestResponseValue reward
          (Function.update profile mover source) observer +
        lambda * quittingContinuationBestResponseValue reward
          (Function.update profile mover target) observer -
      quittingContinuationBestResponseValue reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1)) observer ≤
      (1 - lambda) * sourceError + lambda * targetError := by
  have hcertificate :=
    quittingContinuationBestResponseValue_stoppingLawMixture_chordGap_le
      reward profile mover observer hne source target deviation lambda
        hlambda0 hlambda1
  have hsourceRegret :
      quittingContinuationBestResponseValue reward
          (Function.update profile mover source) observer -
        quittingTerminalPayoff reward
          (Function.update (Function.update profile mover source)
            observer deviation) observer ≤ sourceError := by
    linarith
  have htargetRegret :
      quittingContinuationBestResponseValue reward
          (Function.update profile mover target) observer -
        quittingTerminalPayoff reward
          (Function.update (Function.update profile mover target)
            observer deviation) observer ≤ targetError := by
    linarith
  have hsourceWeight : 0 ≤ 1 - lambda := sub_nonneg.mpr hlambda1
  have hweightedSource :=
    mul_le_mul_of_nonneg_left hsourceRegret hsourceWeight
  have hweightedTarget :=
    mul_le_mul_of_nonneg_left htargetRegret hlambda0
  linarith

/-- On a common-witness stratum, the observer's full semantic-debt coordinate
is affine as well: both the best-response envelope and prescribed payoff are
affine along the stopping-law mixture. -/
theorem quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_commonWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hsource : quittingTerminalPayoff reward
        (Function.update (Function.update profile mover source)
          observer deviation) observer =
      quittingContinuationBestResponseValue reward
        (Function.update profile mover source) observer)
    (htarget : quittingTerminalPayoff reward
        (Function.update (Function.update profile mover target)
          observer deviation) observer =
      quittingContinuationBestResponseValue reward
        (Function.update profile mover target) observer) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1))) observer =
      (1 - lambda) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) observer +
        lambda * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) observer := by
  have hbest :=
    quittingContinuationBestResponseValue_stoppingLawMixture_eq_of_commonWitness
      reward profile mover observer hne source target deviation lambda
        hlambda0 hlambda1 hsource htarget
  have hpayoff := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile mover observer source target lambda hlambda0 hlambda1
  dsimp only [quittingTerminalSemanticDebt,
    quittingTerminalSemanticPair] at hbest hpayoff ⊢
  linarith

/-- Zero semantic debt is preserved coordinatewise along every legal
stopping-law mixture.  Convexity gives the upper bound zero, while literal
deviation debt is always nonnegative.  In particular, zero-slack Nash faces
are safe along this direction even though positive debt coordinates need not
be affine. -/
theorem quittingTerminalSemanticDebt_stoppingLawMixture_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hsource : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover source)) observer = 0)
    (htarget : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover target)) observer = 0) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1))) observer = 0 := by
  have hupper := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward profile mover observer source target lambda hlambda0 hlambda1
  rw [hsource, htarget] at hupper
  have hlower := quittingTerminalDeviationDebt_nonneg reward
    (Function.update profile mover
      (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
        lambda hlambda0 hlambda1)) observer
  dsimp only [quittingTerminalDeviationDebt, quittingTerminalSemanticDebt,
    quittingTerminalSemanticPair] at hupper hlower ⊢
  exact le_antisymm (by linarith) hlower

/-- If both endpoint profiles have zero debt for every player, the complete
stopping-law mixture also has zero debt for every player. -/
theorem quittingStoppingLawMixture_preserves_zeroDebtFace
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hsource : ∀ observer, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover source)) observer = 0)
    (htarget : ∀ observer, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover target)) observer = 0) :
    ∀ observer, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1))) observer = 0 := by
  intro observer
  exact quittingTerminalSemanticDebt_stoppingLawMixture_eq_zero
    reward profile mover observer source target lambda hlambda0 hlambda1
      (hsource observer) (htarget observer)

/-- On the common zero-debt face, both halves of the terminal semantic pair
are affine.  Payoff affinity is unconditional; envelope affinity follows
because endpoint and mixture envelopes coincide with their prescribed
payoffs.  This is a genuine affine chart for the terminal value/envelope
coordinates, though not for every root or marked-stage coordinate. -/
theorem quittingTerminalSemanticPair_stoppingLawMixture_affine_on_zeroDebtFace
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hsource : ∀ observer, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover source)) observer = 0)
    (htarget : ∀ observer, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover target)) observer = 0) :
    ∀ observer,
      quittingTerminalPayoff reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1)) observer =
        (1 - lambda) * quittingTerminalPayoff reward
            (Function.update profile mover source) observer +
          lambda * quittingTerminalPayoff reward
            (Function.update profile mover target) observer ∧
      quittingContinuationBestResponseValue reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1)) observer =
        (1 - lambda) * quittingContinuationBestResponseValue reward
            (Function.update profile mover source) observer +
          lambda * quittingContinuationBestResponseValue reward
            (Function.update profile mover target) observer := by
  intro observer
  have hpayoff := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile mover observer source target lambda hlambda0 hlambda1
  refine ⟨hpayoff, ?_⟩
  have hmixed := quittingStoppingLawMixture_preserves_zeroDebtFace
    reward profile mover source target lambda hlambda0 hlambda1 hsource htarget
      observer
  have hs := hsource observer
  have ht := htarget observer
  dsimp only [quittingTerminalSemanticDebt,
    quittingTerminalSemanticPair] at hmixed hs ht
  nlinarith

/-- A second exact affine stratum comes from minimum-fiber rigidity.  If the
source is a global minimum of total debt and the endpoint lies on the same
minimum-total-debt fiber, then coordinatewise convexity cannot be strict in
any coordinate: a strict coordinate would make the mixed total debt smaller
than the minimum.  Hence every debt coordinate equals its chord, without
assuming a common attained best-response witness. -/
theorem quittingTerminalSemanticDebt_stoppingLawMixture_eq_chord_of_minimumFiber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hendpointFiber : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (Function.update profile mover target)) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (Function.update profile mover source))) :
    ∀ observer,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                lambda hlambda0 hlambda1))) observer =
        (1 - lambda) * quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover source)) observer +
          lambda * quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover target)) observer := by
  let sourcePair := quittingTerminalSemanticPair reward
    (Function.update profile mover source)
  let endpointPair := quittingTerminalSemanticPair reward
    (Function.update profile mover target)
  let mixedPair := quittingTerminalSemanticPair reward
    (Function.update profile mover
      (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
        lambda hlambda0 hlambda1))
  have hmixedMem : mixedPair ∈ quittingTerminalSemanticCarrier reward := by
    dsimp only [mixedPair]
    exact quittingTerminalSemanticPair_mem_carrier reward _
  have hminimumMixed : quittingTerminalSemanticDebtSum sourcePair ≤
      quittingTerminalSemanticDebtSum mixedPair := by
    exact hminimum mixedPair hmixedMem
  have hchord : ∀ observer,
      quittingTerminalSemanticDebt mixedPair observer ≤
        (1 - lambda) * quittingTerminalSemanticDebt sourcePair observer +
          lambda * quittingTerminalSemanticDebt endpointPair observer := by
    intro observer
    dsimp only [mixedPair, sourcePair, endpointPair]
    exact quittingTerminalSemanticDebt_stoppingLawMixture_le
      reward profile mover observer source target lambda hlambda0 hlambda1
  have hchordSum :
      (∑ observer,
          ((1 - lambda) * quittingTerminalSemanticDebt sourcePair observer +
            lambda * quittingTerminalSemanticDebt endpointPair observer)) =
        quittingTerminalSemanticDebtSum sourcePair := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    change (1 - lambda) * quittingTerminalSemanticDebtSum sourcePair +
        lambda * quittingTerminalSemanticDebtSum endpointPair =
      quittingTerminalSemanticDebtSum sourcePair
    dsimp only [sourcePair, endpointPair]
    rw [hendpointFiber]
    ring
  intro observer
  apply le_antisymm (hchord observer)
  by_contra hnot
  have hstrict : quittingTerminalSemanticDebt mixedPair observer <
      (1 - lambda) * quittingTerminalSemanticDebt sourcePair observer +
        lambda * quittingTerminalSemanticDebt endpointPair observer :=
    lt_of_not_ge hnot
  have hsumStrict : quittingTerminalSemanticDebtSum mixedPair <
      ∑ candidate,
        ((1 - lambda) * quittingTerminalSemanticDebt sourcePair candidate +
          lambda * quittingTerminalSemanticDebt endpointPair candidate) := by
    unfold quittingTerminalSemanticDebtSum
    apply Finset.sum_lt_sum
    · intro candidate _
      exact hchord candidate
    · exact ⟨observer, Finset.mem_univ observer, hstrict⟩
  rw [hchordSum] at hsumStrict
  exact (not_lt_of_ge hminimumMixed) hsumStrict

/-! ## A literal two-player witness-switch kink -/

namespace StoppingLawMixtureKink

/-- Only simultaneous quitting is rewarded.  The observer is `true`, while
the moved player is `false`. -/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun _ => if quitters.1 = Finset.univ then 1 else 0

def baseProfile : (quittingGame reward).BehaviorProfile :=
  quittingAlwaysContinueProfile reward

def source : (quittingGame reward).BehaviorStrategy false :=
  quittingPureTimeBehaviorStrategy reward false (some 0)

def target : (quittingGame reward).BehaviorStrategy false :=
  quittingPureTimeBehaviorStrategy reward false (some 1)

def sourceProfile : (quittingGame reward).BehaviorProfile :=
  Function.update baseProfile false source

def targetProfile : (quittingGame reward).BehaviorProfile :=
  Function.update baseProfile false target

theorem source_liveRow_zero (observerAction : Bool) :
    Function.update (quittingProfileLiveRoot reward sourceProfile 0) true
        (PMF.pure observerAction) =
      (fun who : Bool => PMF.pure (if who then observerAction else true)) := by
  funext who
  cases who <;>
    simp [quittingProfileLiveRoot, sourceProfile, source, baseProfile,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard]

theorem target_liveRow_zero (observerAction : Bool) :
    Function.update (quittingProfileLiveRoot reward targetProfile 0) true
        (PMF.pure observerAction) =
      (fun who : Bool => PMF.pure (if who then observerAction else false)) := by
  funext who
  cases who <;>
    simp [quittingProfileLiveRoot, targetProfile, target, baseProfile,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard]

theorem target_liveRow_one (observerAction : Bool) :
    Function.update (quittingProfileLiveRoot reward targetProfile 1) true
        (PMF.pure observerAction) =
      (fun who : Bool => PMF.pure (if who then observerAction else true)) := by
  funext who
  cases who <;>
    simp [quittingProfileLiveRoot, targetProfile, target, baseProfile,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard]

theorem abs_reward_le_one
    (terminal : {S : Finset Bool // S.Nonempty}) (player : Bool) :
    |reward terminal player| ≤ 1 := by
  unfold reward
  split <;> norm_num

theorem source_continueReward_zero :
    quittingFixedOpponentsContinueReward reward
      (quittingProfileLiveRoot reward sourceProfile) true 0 = 0 := by
  unfold quittingFixedOpponentsContinueReward
  rw [source_liveRow_zero false]
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [Math.PMFProduct.pmfPi_pure, expect_pure]
  have hsingleton : ({false} : Finset Bool) ≠ {true, false} := by decide
  simp [quittingRootPayoff, reward, hsingleton]

theorem source_continueMass_zero :
    quittingFixedOpponentsContinueMass
      (quittingProfileLiveRoot reward sourceProfile) true 0 = 0 := by
  unfold quittingFixedOpponentsContinueMass
  rw [source_liveRow_zero false]
  unfold quittingStationaryContinueMass
  rw [Math.PMFProduct.pmfPi_apply]
  simp [quittingAllContinueAction]

theorem target_quitValue_zero :
    quittingFixedOpponentsQuitValue reward
      (quittingProfileLiveRoot reward targetProfile) true 0 = 0 := by
  unfold quittingFixedOpponentsQuitValue
  rw [target_liveRow_zero true]
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [Math.PMFProduct.pmfPi_pure, expect_pure]
  have hsingleton : ({true} : Finset Bool) ≠ {true, false} := by decide
  simp [quittingRootPayoff, reward, hsingleton]

theorem target_continueReward_zero :
    quittingFixedOpponentsContinueReward reward
      (quittingProfileLiveRoot reward targetProfile) true 0 = 0 := by
  unfold quittingFixedOpponentsContinueReward
  rw [target_liveRow_zero false]
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [Math.PMFProduct.pmfPi_pure, expect_pure]
  simp [quittingRootPayoff]

theorem target_continueMass_one :
    quittingFixedOpponentsContinueMass
      (quittingProfileLiveRoot reward targetProfile) true 0 = 1 := by
  unfold quittingFixedOpponentsContinueMass
  rw [target_liveRow_zero false]
  unfold quittingStationaryContinueMass
  rw [Math.PMFProduct.pmfPi_apply]
  simp [quittingAllContinueAction]

theorem target_one_continueReward_zero :
    quittingFixedOpponentsContinueReward reward
      (quittingProfileLiveRoot reward targetProfile) true 1 = 0 := by
  unfold quittingFixedOpponentsContinueReward
  rw [target_liveRow_one false]
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [Math.PMFProduct.pmfPi_pure, expect_pure]
  have hsingleton : ({false} : Finset Bool) ≠ {true, false} := by decide
  simp [quittingRootPayoff, reward, hsingleton]

theorem target_one_continueMass_zero :
    quittingFixedOpponentsContinueMass
      (quittingProfileLiveRoot reward targetProfile) true 1 = 0 := by
  unfold quittingFixedOpponentsContinueMass
  rw [target_liveRow_one false]
  unfold quittingStationaryContinueMass
  rw [Math.PMFProduct.pmfPi_apply]
  simp [quittingAllContinueAction]

/-- At the source endpoint the observer matches the mover at date zero and
gets payoff one. -/
theorem source_match_payoff :
    quittingTerminalPayoff reward
        (Function.update sourceProfile true
          (quittingPureTimeBehaviorStrategy reward true (some 0))) true = 1 := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
  unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [QuittingTerminalPacketSimpleFallbackCounterexample.expect_pmfPi_bool]
  simp [expect_eq_sum, quittingProfileLiveRoot, sourceProfile, source,
    baseProfile, quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
    quittingRootPayoff, reward]

/-- At the target endpoint the observer instead matches the mover at date
one and again gets payoff one. -/
theorem target_match_payoff :
    quittingTerminalPayoff reward
        (Function.update targetProfile true
          (quittingPureTimeBehaviorStrategy reward true (some 1))) true = 1 := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  unfold quittingRootSequencePureTimeTerminalValue
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
  simp only [quittingPureTimeHazard_some_of_ne (by norm_num : 0 ≠ 1),
    PMF.pure_apply, if_neg (by decide : (true : Bool) ≠ false),
    ENNReal.toReal_zero, if_true, ENNReal.toReal_one, zero_mul, one_mul,
    zero_add]
  unfold quittingFixedOpponentsContinueReward
    quittingFixedOpponentsContinueMass
  have hrow0 :
      Function.update (quittingProfileLiveRoot reward targetProfile 0) true
          (PMF.pure false) =
        (fun _ : Bool => PMF.pure false) := by
    funext who
    cases who <;>
      simp [quittingProfileLiveRoot, targetProfile, target, baseProfile,
        quittingPureTimeBehaviorStrategy, quittingPureTimeHazard]
  rw [hrow0]
  have hab0 : quittingRootAbsorbingContribution reward
      (fun _ : Bool => PMF.pure false) true = 0 := by
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    rw [QuittingTerminalPacketSimpleFallbackCounterexample.expect_pmfPi_bool]
    simp [quittingRootPayoff]
  have hsurvival0 : quittingStationaryContinueMass
      (fun _ : Bool => PMF.pure false) = 1 := by
    simp [quittingStationaryContinueMass, Math.PMFProduct.pmfPi_apply,
      quittingAllContinueAction]
  rw [hab0, hsurvival0]
  simp only [zero_add, one_mul]
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
  simp only [quittingPureTimeHazard_some_self, PMF.pure_apply, if_true,
    ENNReal.toReal_one, one_mul]
  unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [QuittingTerminalPacketSimpleFallbackCounterexample.expect_pmfPi_bool]
  simp [expect_eq_sum, quittingProfileLiveRoot, targetProfile, target,
    baseProfile, quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
    quittingRootPayoff, reward]

theorem source_bestResponse_eq_one :
    quittingContinuationBestResponseValue reward sourceProfile true = 1 := by
  apply le_antisymm
  · exact (le_abs_self _).trans
      (abs_quittingContinuationBestResponseValue_le reward sourceProfile true
        (by norm_num) abs_reward_le_one)
  · rw [← source_match_payoff]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward sourceProfile true
        (quittingPureTimeBehaviorStrategy reward true (some 0))

theorem target_bestResponse_eq_one :
    quittingContinuationBestResponseValue reward targetProfile true = 1 := by
  apply le_antisymm
  · exact (le_abs_self _).trans
      (abs_quittingContinuationBestResponseValue_le reward targetProfile true
        (by norm_num) abs_reward_le_one)
  · rw [← target_match_payoff]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward targetProfile true
        (quittingPureTimeBehaviorStrategy reward true (some 1))

def sourcePureValue (choice : Option ℕ) : ℝ :=
  quittingTerminalPayoff reward
    (Function.update sourceProfile true
      (quittingPureTimeBehaviorStrategy reward true choice)) true

def targetPureValue (choice : Option ℕ) : ℝ :=
  quittingTerminalPayoff reward
    (Function.update targetProfile true
      (quittingPureTimeBehaviorStrategy reward true choice)) true

theorem sourcePureValue_eq_indicator (choice : Option ℕ) :
    sourcePureValue choice = if choice = some 0 then 1 else 0 := by
  cases choice with
  | none =>
      rw [show sourcePureValue none =
          quittingRootSequencePureTimeTerminalValue reward
            (quittingProfileLiveRoot reward sourceProfile) true none 0 by
        exact quittingTerminalPayoff_update_pureTimeBehaviorStrategy
          reward sourceProfile true none]
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
      simp only [quittingPureTimeHazard_none, PMF.pure_apply,
        if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
        if_true, ENNReal.toReal_one, zero_mul, one_mul]
      rw [source_continueReward_zero, source_continueMass_zero]
      simp
  | some time =>
      cases time with
      | zero => simpa [sourcePureValue] using source_match_payoff
      | succ time =>
          rw [show sourcePureValue (some (time + 1)) =
              quittingRootSequencePureTimeTerminalValue reward
                (quittingProfileLiveRoot reward sourceProfile) true
                  (some (time + 1)) 0 by
            exact quittingTerminalPayoff_update_pureTimeBehaviorStrategy
              reward sourceProfile true (some (time + 1))]
          unfold quittingRootSequencePureTimeTerminalValue
          rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
          simp only [quittingPureTimeHazard_some_of_ne (by omega : 0 ≠ time + 1),
            PMF.pure_apply, if_neg (by decide : (true : Bool) ≠ false),
            ENNReal.toReal_zero, if_true, ENNReal.toReal_one, zero_mul,
            one_mul]
          rw [source_continueReward_zero, source_continueMass_zero]
          norm_num

theorem targetPureValue_eq_indicator (choice : Option ℕ) :
    targetPureValue choice = if choice = some 1 then 1 else 0 := by
  cases choice with
  | none =>
      rw [show targetPureValue none =
          quittingRootSequencePureTimeTerminalValue reward
            (quittingProfileLiveRoot reward targetProfile) true none 0 by
        exact quittingTerminalPayoff_update_pureTimeBehaviorStrategy
          reward targetProfile true none]
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
      simp only [quittingPureTimeHazard_none, PMF.pure_apply,
        if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
        if_true, ENNReal.toReal_one, zero_mul, one_mul]
      rw [target_continueReward_zero, target_continueMass_one]
      simp only [zero_add, one_mul]
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
      simp only [quittingPureTimeHazard_none, PMF.pure_apply,
        if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
        if_true, ENNReal.toReal_one, zero_mul, one_mul]
      rw [target_one_continueReward_zero, target_one_continueMass_zero]
      simp
  | some time =>
      cases time with
      | zero =>
          rw [show targetPureValue (some 0) =
              quittingRootSequencePureTimeTerminalValue reward
                (quittingProfileLiveRoot reward targetProfile) true
                  (some 0) 0 by
            exact quittingTerminalPayoff_update_pureTimeBehaviorStrategy
              reward targetProfile true (some 0)]
          rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
            target_quitValue_zero]
          norm_num
      | succ time =>
          cases time with
          | zero => simpa [targetPureValue] using target_match_payoff
          | succ time =>
              rw [show targetPureValue (some (time + 2)) =
                  quittingRootSequencePureTimeTerminalValue reward
                    (quittingProfileLiveRoot reward targetProfile) true
                      (some (time + 2)) 0 by
                exact quittingTerminalPayoff_update_pureTimeBehaviorStrategy
                  reward targetProfile true (some (time + 2))]
              unfold quittingRootSequencePureTimeTerminalValue
              rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
              simp only [quittingPureTimeHazard_some_of_ne
                  (by omega : 0 ≠ time + 2),
                PMF.pure_apply, if_neg (by decide : (true : Bool) ≠ false),
                ENNReal.toReal_zero, if_true, ENNReal.toReal_one, zero_mul,
                one_mul]
              rw [target_continueReward_zero, target_continueMass_one]
              simp only [zero_add, one_mul]
              rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
              simp only [quittingPureTimeHazard_some_of_ne
                  (by omega : 1 ≠ time + 2),
                PMF.pure_apply, if_neg (by decide : (true : Bool) ≠ false),
                ENNReal.toReal_zero, if_true, ENNReal.toReal_one, zero_mul,
                one_mul]
              rw [target_one_continueReward_zero,
                target_one_continueMass_zero]
              norm_num

theorem expect_singletonIndicator_eq {Ω : Type} [DecidableEq Ω]
    (law : PMF Ω) (atom : Ω) :
    expect law (fun choice => if choice = atom then (1 : ℝ) else 0) =
      (law atom).toReal := by
  unfold expect
  rw [tsum_eq_single atom]
  · simp
  · intro other hne
    simp [hne]

/-- Against the date-zero endpoint, an arbitrary observer strategy earns
exactly its own stopping-law atom at date zero. -/
theorem source_payoff_eq_stoppingLaw_zero
    (strategy : (quittingGame reward).BehaviorStrategy true) :
    quittingTerminalPayoff reward
        (Function.update sourceProfile true strategy) true =
      (quittingBehaviorStoppingLaw reward strategy (some 0)).toReal := by
  rw [quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
    reward sourceProfile true strategy (by norm_num) abs_reward_le_one]
  change expect (quittingBehaviorStoppingLaw reward strategy) sourcePureValue = _
  have hvalue : sourcePureValue =
      (fun choice => if choice = some 0 then (1 : ℝ) else 0) := by
    funext choice
    exact sourcePureValue_eq_indicator choice
  rw [hvalue]
  exact expect_singletonIndicator_eq _ _

/-- Against the date-one endpoint, an arbitrary observer strategy earns
exactly its own stopping-law atom at date one. -/
theorem target_payoff_eq_stoppingLaw_one
    (strategy : (quittingGame reward).BehaviorStrategy true) :
    quittingTerminalPayoff reward
        (Function.update targetProfile true strategy) true =
      (quittingBehaviorStoppingLaw reward strategy (some 1)).toReal := by
  rw [quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
    reward targetProfile true strategy (by norm_num) abs_reward_le_one]
  change expect (quittingBehaviorStoppingLaw reward strategy) targetPureValue = _
  have hvalue : targetPureValue =
      (fun choice => if choice = some 1 then (1 : ℝ) else 0) := by
    funext choice
    exact targetPureValue_eq_indicator choice
  rw [hvalue]
  exact expect_singletonIndicator_eq _ _

theorem source_add_target_payoff_le_one
    (strategy : (quittingGame reward).BehaviorStrategy true) :
    quittingTerminalPayoff reward
          (Function.update sourceProfile true strategy) true +
        quittingTerminalPayoff reward
          (Function.update targetProfile true strategy) true ≤ 1 := by
  rw [source_payoff_eq_stoppingLaw_zero,
    target_payoff_eq_stoppingLaw_one]
  let law := quittingBehaviorStoppingLaw reward strategy
  have hfinite := (pmf_toReal_summable law).sum_le_tsum
    ({some 0, some 1} : Finset (Option ℕ))
      (fun choice _ => ENNReal.toReal_nonneg)
  rw [pmf_toReal_tsum_one] at hfinite
  simpa [law, add_comm] using hfinite

def mixedStrategy (lambda : ℝ) (hlambda0 : 0 ≤ lambda)
    (hlambda1 : lambda ≤ 1) :
    (quittingGame reward).BehaviorStrategy false :=
  quittingStoppingLawMixtureBehaviorStrategy reward false source target
    lambda hlambda0 hlambda1

def mixedProfile (lambda : ℝ) (hlambda0 : 0 ≤ lambda)
    (hlambda1 : lambda ≤ 1) : (quittingGame reward).BehaviorProfile :=
  Function.update baseProfile false (mixedStrategy lambda hlambda0 hlambda1)

theorem mixed_pureValue_eq
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (choice : Option ℕ) :
    quittingTerminalPayoff reward
        (Function.update (mixedProfile lambda hlambda0 hlambda1) true
          (quittingPureTimeBehaviorStrategy reward true choice)) true =
      (1 - lambda) * sourcePureValue choice +
        lambda * targetPureValue choice := by
  let deviation := quittingPureTimeBehaviorStrategy reward true choice
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update baseProfile true deviation) false true
      source target lambda hlambda0 hlambda1
  have hsource :
      Function.update (Function.update baseProfile true deviation) false source =
        Function.update sourceProfile true deviation := by
    simpa [sourceProfile] using
      (Function.update_comm (by decide : true ≠ false)
        deviation source baseProfile)
  have htarget :
      Function.update (Function.update baseProfile true deviation) false target =
        Function.update targetProfile true deviation := by
    simpa [targetProfile] using
      (Function.update_comm (by decide : true ≠ false)
        deviation target baseProfile)
  have hmixed :
      Function.update (Function.update baseProfile true deviation) false
          (mixedStrategy lambda hlambda0 hlambda1) =
        Function.update (mixedProfile lambda hlambda0 hlambda1) true deviation := by
    simpa [mixedProfile, mixedStrategy] using
      (Function.update_comm (by decide : true ≠ false)
        deviation (mixedStrategy lambda hlambda0 hlambda1) baseProfile)
  dsimp only [mixedStrategy] at hmixed
  rw [hmixed, hsource, htarget] at haffine
  exact haffine

/-- The minimal genuine kink.  The observer chooses which of the mover's two
possible deterministic dates to match, hence the exact envelope
`max (1-lambda) lambda`. -/
theorem mixed_bestResponse_eq_max
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingContinuationBestResponseValue reward
        (mixedProfile lambda hlambda0 hlambda1) true =
      max (1 - lambda) lambda := by
  apply le_antisymm
  · unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact Set.range_nonempty _
    rintro payoff ⟨deviation, rfl⟩
    have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
      reward (Function.update baseProfile true deviation) false true
        source target lambda hlambda0 hlambda1
    have hsource :
        Function.update (Function.update baseProfile true deviation) false source =
          Function.update sourceProfile true deviation := by
      simpa [sourceProfile] using
        (Function.update_comm (by decide : true ≠ false)
          deviation source baseProfile)
    have htarget :
        Function.update (Function.update baseProfile true deviation) false target =
          Function.update targetProfile true deviation := by
      simpa [targetProfile] using
        (Function.update_comm (by decide : true ≠ false)
          deviation target baseProfile)
    have hmixed :
        Function.update (Function.update baseProfile true deviation) false
            (mixedStrategy lambda hlambda0 hlambda1) =
          Function.update (mixedProfile lambda hlambda0 hlambda1) true
            deviation := by
      simpa [mixedProfile, mixedStrategy] using
        (Function.update_comm (by decide : true ≠ false)
          deviation (mixedStrategy lambda hlambda0 hlambda1) baseProfile)
    dsimp only [mixedStrategy] at hmixed
    rw [hmixed, hsource, htarget] at haffine
    let sourcePayoff := quittingTerminalPayoff reward
      (Function.update sourceProfile true deviation) true
    let targetPayoff := quittingTerminalPayoff reward
      (Function.update targetProfile true deviation) true
    have hsourceNonneg : 0 ≤ sourcePayoff := by
      dsimp only [sourcePayoff]
      rw [source_payoff_eq_stoppingLaw_zero]
      exact ENNReal.toReal_nonneg
    have htargetNonneg : 0 ≤ targetPayoff := by
      dsimp only [targetPayoff]
      rw [target_payoff_eq_stoppingLaw_one]
      exact ENNReal.toReal_nonneg
    have hmass : sourcePayoff + targetPayoff ≤ 1 := by
      exact source_add_target_payoff_le_one deviation
    let peak := max (1 - lambda) lambda
    have hsourceWeight : 1 - lambda ≤ peak := le_max_left _ _
    have htargetWeight : lambda ≤ peak := le_max_right _ _
    have hpeakNonneg : 0 ≤ peak := hlambda0.trans htargetWeight
    have hsourceScaled :=
      mul_le_mul_of_nonneg_right hsourceWeight hsourceNonneg
    have htargetScaled :=
      mul_le_mul_of_nonneg_right htargetWeight htargetNonneg
    have hmassScaled := mul_le_mul_of_nonneg_left hmass hpeakNonneg
    dsimp only [sourcePayoff, targetPayoff, peak] at hsourceScaled htargetScaled hmassScaled ⊢
    rw [haffine]
    nlinarith
  · apply max_le
    · have hlower :=
        quittingTerminalPayoff_update_le_continuationBestResponseValue
          reward (mixedProfile lambda hlambda0 hlambda1) true
            (quittingPureTimeBehaviorStrategy reward true (some 0))
      rw [mixed_pureValue_eq, sourcePureValue_eq_indicator,
        targetPureValue_eq_indicator] at hlower
      simpa using hlower
    · have hlower :=
        quittingTerminalPayoff_update_le_continuationBestResponseValue
          reward (mixedProfile lambda hlambda0 hlambda1) true
            (quittingPureTimeBehaviorStrategy reward true (some 1))
      rw [mixed_pureValue_eq, sourcePureValue_eq_indicator,
        targetPureValue_eq_indicator] at hlower
      simpa using hlower

theorem mixed_midpoint_bestResponse_eq_half :
    quittingContinuationBestResponseValue reward
        (mixedProfile (1 / 2) (by norm_num) (by norm_num)) true = 1 / 2 := by
  rw [mixed_bestResponse_eq_max]
  norm_num

/-- Strict failure of affinity at the midpoint, despite both endpoint
best-response values being one. -/
theorem mixed_midpoint_strictly_below_endpointChord :
    quittingContinuationBestResponseValue reward
        (mixedProfile (1 / 2) (by norm_num) (by norm_num)) true <
      (1 / 2 : ℝ) *
          quittingContinuationBestResponseValue reward sourceProfile true +
        (1 / 2 : ℝ) *
          quittingContinuationBestResponseValue reward targetProfile true := by
  rw [mixed_midpoint_bestResponse_eq_half, source_bestResponse_eq_one,
    target_bestResponse_eq_one]
  norm_num

end StoppingLawMixtureKink

end GameTheory
