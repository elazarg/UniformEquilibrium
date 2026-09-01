/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.Probability.StoppingLawCapBandRedistribution
import UniformEquilibrium.Quitting.Paths.StoppingLawBadMassSelection
import UniformEquilibrium.Quitting.Terminal.StoppingLawCanonicalization
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Quitting-game cap-band redistribution

This module turns the generic cap-band pushforward into a literal unilateral
quitting-game response.  The finite cut is chosen from the source stopping
law itself.  The construction is conditional on one supplied actual source
profile and makes no compactness, renewal, or equilibrium claim.
-/

noncomputable section

namespace GameTheory

open StochasticGame _root_.Math.Probability
open _root_.Math.Probability.DiscreteHazard
open _root_.Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- Deterministic stopping-time payoff against the literal source opponents. -/
abbrev quittingCapBandClockValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι) :
    Option ℕ → ℝ :=
  fun choice => quittingTerminalPayoff reward
    (Function.update profile mover
      (quittingPureTimeBehaviorStrategy reward mover choice)) mover

/-- The mover's complete live-spine stopping law at the source profile. -/
abbrev quittingCapBandSourceLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι) :
    PMF (Option ℕ) :=
  quittingBehaviorStoppingLaw reward (profile mover)

/-- Finite prefix data selected from positive source mass outside a near-cap
band.  The selected receiver is not moved below `cut`, every earlier bad atom
has zero source mass, and the total bad mass is controlled by the source
survival through the cut. -/
structure QuittingCapBandFiniteCut
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (epsilon : ℝ) where
  receiver : Option ℕ
  cut : ℕ
  receiver_near_cap :
    quittingContinuationBestResponseValue reward profile mover - epsilon / 2 <
      quittingCapBandClockValue reward profile mover receiver
  receiver_not_before : ∀ earlier, earlier < cut → receiver ≠ some earlier
  bad_zero_before : ∀ earlier, earlier < cut →
    stoppingLawOutsideCapBand
        (quittingCapBandClockValue reward profile mover)
          (quittingContinuationBestResponseValue reward profile mover)
          epsilon (some earlier) →
      quittingCapBandSourceLaw reward profile mover (some earlier) = 0
  badMass_pos :
    0 < stoppingLawOutsideCapBandMass
      (quittingCapBandSourceLaw reward profile mover)
      (quittingCapBandClockValue reward profile mover)
      (quittingContinuationBestResponseValue reward profile mover) epsilon
  badMass_le_sourceSurvival :
    stoppingLawOutsideCapBandMass
        (quittingCapBandSourceLaw reward profile mover)
        (quittingCapBandClockValue reward profile mover)
        (quittingContinuationBestResponseValue reward profile mover) epsilon ≤
      StoppingLaw.survival
        (quittingCapBandSourceLaw reward profile mover) cut
  cut_origin :
    ((∀ time,
        stoppingLawOutsideCapBand
            (quittingCapBandClockValue reward profile mover)
            (quittingContinuationBestResponseValue reward profile mover)
            epsilon (some time) →
          quittingCapBandSourceLaw reward profile mover (some time) = 0) ∧
      ∃ receiverTime,
        receiver = some receiverTime ∧ cut = receiverTime) ∨
    ∃ first,
      stoppingLawOutsideCapBand
          (quittingCapBandClockValue reward profile mover)
          (quittingContinuationBestResponseValue reward profile mover)
          epsilon (some first) ∧
      0 < (quittingCapBandSourceLaw reward profile mover (some first)).toReal ∧
      (∀ earlier, earlier < first →
        stoppingLawOutsideCapBand
            (quittingCapBandClockValue reward profile mover)
            (quittingContinuationBestResponseValue reward profile mover)
            epsilon (some earlier) →
          quittingCapBandSourceLaw reward profile mover (some earlier) = 0) ∧
      cut = receiver.elim first (fun receiverTime ↦ min first receiverTime)

namespace QuittingCapBandFiniteCut

omit [Nontrivial ι] in
/-- Positive bad mass and its survival floor make the complete source law
live through the selected cut. -/
theorem sourceSurvival_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon) :
    0 < StoppingLaw.survival
      (quittingCapBandSourceLaw reward profile mover) data.cut :=
  data.badMass_pos.trans_le data.badMass_le_sourceSurvival

/-- Complete stopping law obtained by redirecting every bad source clock to
the selected near-cap receiver. -/
def targetLaw
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon) :
    PMF (Option ℕ) :=
  stoppingLawCapBandPushforward
    (quittingCapBandSourceLaw reward profile mover)
    (quittingCapBandClockValue reward profile mover)
    (quittingContinuationBestResponseValue reward profile mover)
    epsilon data.receiver

/-- Canonical behavior strategy realizing the redirected stopping law. -/
def targetStrategy
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon) :
    (quittingGame reward).BehaviorStrategy mover :=
  quittingStoppingLawBehaviorStrategy reward mover data.targetLaw

/-- Literal unilateral target profile. -/
def targetProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon) :
    (quittingGame reward).BehaviorProfile :=
  Function.update profile mover data.targetStrategy

omit [Nontrivial ι] in
/-- The target strategy has exactly the redirected complete stopping law. -/
@[simp] theorem behaviorStoppingLaw_targetStrategy
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon) :
    quittingBehaviorStoppingLaw reward data.targetStrategy = data.targetLaw := by
  unfold targetStrategy
  exact quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy
    reward mover data.targetLaw

omit [Nontrivial ι] in
/-- The canonical target uses the literal source hazard at every live row
strictly before the selected cut. -/
theorem liveHazard_targetStrategy_eq_of_lt
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon)
    {time : ℕ} (htime : time < data.cut) :
    quittingBehaviorLiveHazard reward data.targetStrategy time =
      quittingBehaviorLiveHazard reward (profile mover) time := by
  let sourceHazard := quittingBehaviorLiveHazard reward (profile mover)
  have htimeSurvival : 0 < StoppingLaw.survival
      (quittingCapBandSourceLaw reward profile mover) time := by
    exact data.sourceSurvival_pos.trans_le
      (StoppingLaw.survival_antitone
        (quittingCapBandSourceLaw reward profile mover) htime.le)
  have hscalarSurvival :
      0 < (BooleanHazard.toScalar sourceHazard).survival 0 time := by
    change 0 < StoppingLaw.survival
      (BooleanHazard.toScalar sourceHazard).stoppingLaw time at htimeSurvival
    simpa using htimeSurvival
  change (StoppingLaw.toScalarHazard data.targetLaw).toBoolean time =
    sourceHazard time
  exact stoppingLawCapBandPushforward_toBoolean_apply_eq_of_lt
    sourceHazard (quittingCapBandClockValue reward profile mover)
    (quittingContinuationBestResponseValue reward profile mover)
    epsilon data.receiver data.cut time data.bad_zero_before
      data.receiver_not_before htime hscalarSurvival

omit [Nontrivial ι] in
/-- Updating to the target strategy changes no player's canonical live root
before the selected cut. -/
theorem profileLiveRoot_target_eq_of_lt
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon)
    {time : ℕ} (htime : time < data.cut) :
    quittingProfileLiveRoot reward data.targetProfile time =
      quittingProfileLiveRoot reward profile time := by
  funext player
  unfold targetProfile quittingProfileLiveRoot
  by_cases hplayer : player = mover
  · subst player
    rw [Function.update_self]
    exact data.liveHazard_targetStrategy_eq_of_lt htime
  · rw [Function.update_of_ne hplayer]

omit [Nontrivial ι] in
/-- The mover's unrestricted behavioral cap is invariant under its own
cap-band redistribution. -/
theorem target_bestResponseValue_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon) :
    quittingContinuationBestResponseValue reward data.targetProfile mover =
      quittingContinuationBestResponseValue reward profile mover := by
  unfold targetProfile
  exact quittingContinuationBestResponseValue_update_self _ _ _ _

omit [Nontrivial ι] in
/-- The target payoff is the redirected law's exact average of the source
opponents' deterministic stopping-time values. -/
theorem target_payoff_eq_expect
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon) :
    quittingTerminalPayoff reward data.targetProfile mover =
      expect data.targetLaw
        (quittingCapBandClockValue reward profile mover) := by
  unfold targetProfile targetStrategy quittingCapBandClockValue
  exact quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect
    reward profile mover mover data.targetLaw

omit [Nontrivial ι] in
/-- The source payoff is the original stopping law's exact average of the
same deterministic stopping-time values. -/
theorem source_payoff_eq_expect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) :
    quittingTerminalPayoff reward profile mover =
      expect (quittingCapBandSourceLaw reward profile mover)
        (quittingCapBandClockValue reward profile mover) := by
  exact quittingTerminalPayoff_eq_expect_behaviorStoppingLaw_pureTime
    reward profile mover mover

omit [Nontrivial ι] in
/-- The target mover's literal terminal debt is at most the cap-band width. -/
theorem target_terminalSemanticDebt_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon M : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon)
    (hepsilon : 0 < epsilon)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward data.targetProfile) mover ≤
        epsilon := by
  have hvalue : ∀ choice,
      |quittingCapBandClockValue reward profile mover choice| ≤ M := by
    intro choice
    exact abs_quittingTerminalPayoff_le reward _ mover hreward
  have hbound := stoppingLawCapBandPushforward_debt_le
    (quittingCapBandSourceLaw reward profile mover)
    (quittingCapBandClockValue reward profile mover)
    (quittingContinuationBestResponseValue reward profile mover)
    epsilon M data.receiver hepsilon hvalue data.receiver_near_cap
  change quittingContinuationBestResponseValue reward data.targetProfile mover -
      quittingTerminalPayoff reward data.targetProfile mover ≤ epsilon
  rw [data.target_bestResponseValue_eq, data.target_payoff_eq_expect]
  exact hbound

omit [Nontrivial ι] in
/-- The mover's payoff gain is at least its source debt minus the cap-band
width. -/
theorem sourceDebt_sub_epsilon_le_target_payoffGain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon M : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon)
    (hepsilon : 0 < epsilon)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) mover - epsilon ≤
      quittingTerminalPayoff reward data.targetProfile mover -
        quittingTerminalPayoff reward profile mover := by
  have hvalue : ∀ choice,
      |quittingCapBandClockValue reward profile mover choice| ≤ M := by
    intro choice
    exact abs_quittingTerminalPayoff_le reward _ mover hreward
  have hgain := stoppingLawCapBandPushforward_gain_ge_debt_sub
    (quittingCapBandSourceLaw reward profile mover)
    (quittingCapBandClockValue reward profile mover)
    (quittingContinuationBestResponseValue reward profile mover)
    epsilon M data.receiver hepsilon hvalue data.receiver_near_cap
  change (quittingContinuationBestResponseValue reward profile mover -
        quittingTerminalPayoff reward profile mover) - epsilon ≤
      quittingTerminalPayoff reward data.targetProfile mover -
        quittingTerminalPayoff reward profile mover
  rw [data.target_payoff_eq_expect,
    source_payoff_eq_expect reward profile mover]
  unfold stoppingLawSourceCapDebt at hgain
  exact hgain

omit [Nontrivial ι] in
/-- The source mover debt is bounded by the band width plus twice the reward
bound times the source mass outside the band. -/
theorem source_terminalSemanticDebt_le_epsilon_add_two_mul_badMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (epsilon M : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) mover ≤
      epsilon + 2 * M * stoppingLawOutsideCapBandMass
        (quittingCapBandSourceLaw reward profile mover)
        (quittingCapBandClockValue reward profile mover)
        (quittingContinuationBestResponseValue reward profile mover)
        epsilon := by
  have hM := quittingRewardCoordinateBound_nonneg_of_player
    reward mover hreward
  have hvalue : ∀ choice,
      |quittingCapBandClockValue reward profile mover choice| ≤ M := by
    intro choice
    exact abs_quittingTerminalPayoff_le reward _ mover hreward
  have hvalueCap : ∀ choice,
      quittingCapBandClockValue reward profile mover choice ≤
        quittingContinuationBestResponseValue reward profile mover := by
    intro choice
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile mover _
  have hcap := abs_quittingContinuationBestResponseValue_le
    reward profile mover hreward
  have hbound := stoppingLawSourceCapDebt_le_epsilon_add_two_mul_badMass
    (quittingCapBandSourceLaw reward profile mover)
    (quittingCapBandClockValue reward profile mover)
    (quittingContinuationBestResponseValue reward profile mover)
    epsilon M hM hepsilon hcap hvalue hvalueCap
  change quittingContinuationBestResponseValue reward profile mover -
      quittingTerminalPayoff reward profile mover ≤ _
  rw [source_payoff_eq_expect reward profile mover]
  unfold stoppingLawSourceCapDebt at hbound
  exact hbound

omit [Nontrivial ι] in
/-- Exact own-cap transport: the mover's target debt is its source debt minus
the realized payoff gain. -/
theorem target_terminalSemanticDebt_eq_source_sub_payoffGain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward data.targetProfile) mover =
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) mover -
        (quittingTerminalPayoff reward data.targetProfile mover -
          quittingTerminalPayoff reward profile mover) := by
  change quittingContinuationBestResponseValue reward data.targetProfile mover -
      quittingTerminalPayoff reward data.targetProfile mover =
    (quittingContinuationBestResponseValue reward profile mover -
      quittingTerminalPayoff reward profile mover) -
        (quittingTerminalPayoff reward data.targetProfile mover -
          quittingTerminalPayoff reward profile mover)
  rw [data.target_bestResponseValue_eq]
  ring

omit [Nontrivial ι] in
/-- Because the target and source have the same live prefix, the realized
payoff gain is at most twice the reward bound times the literal source joint
reach of the selected cut. -/
theorem target_payoffGain_le_two_mul_jointReach
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon M : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalPayoff reward data.targetProfile mover -
        quittingTerminalPayoff reward profile mover ≤
      2 * M * quittingJointSurvivalWeight
        (quittingProfileLiveRoot reward profile) 0 data.cut := by
  have hbound := abs_quittingRootSequenceTerminalValue_sub_le_of_prefix_eq
    reward (quittingProfileLiveRoot reward data.targetProfile)
      (quittingProfileLiveRoot reward profile) mover data.cut hreward
      (fun time htime => data.profileLiveRoot_target_eq_of_lt htime)
  rw [← quittingTerminalPayoff_eq_rootSequence_profileLiveRoot
      reward data.targetProfile mover,
    ← quittingTerminalPayoff_eq_rootSequence_profileLiveRoot
      reward profile mover] at hbound
  exact (le_abs_self _).trans hbound

omit [Nontrivial ι] in
/-- Combining the cap-near gain floor with prefix stability gives a literal
joint-reach lower bound without assuming finite support of the source law. -/
theorem sourceDebt_sub_epsilon_le_two_mul_jointReach
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover : ι} {epsilon M : ℝ}
    (data : QuittingCapBandFiniteCut reward profile mover epsilon)
    (hepsilon : 0 < epsilon)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) mover - epsilon ≤
      2 * M * quittingJointSurvivalWeight
        (quittingProfileLiveRoot reward profile) 0 data.cut :=
  (data.sourceDebt_sub_epsilon_le_target_payoffGain hepsilon hreward).trans
    (data.target_payoffGain_le_two_mul_jointReach hreward)

end QuittingCapBandFiniteCut

private theorem pmf_eq_zero_of_toReal_eq_zero
    {Omega : Type*} (law : PMF Omega) (point : Omega)
    (hzero : (law point).toReal = 0) : law point = 0 := by
  rcases (ENNReal.toReal_eq_zero_iff (law point)).mp hzero with hzero | htop
  · exact hzero
  · exact False.elim (PMF.apply_ne_top law point htop)

omit [Nontrivial ι] in
/-- Source debt strictly above the band width selects a finite live-prefix
cut and a receiver within half the band width of the exact behavioral cap. -/
theorem exists_quittingCapBandFiniteCut
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (epsilon M : ℝ)
    (hM : 0 < M) (hepsilon : 0 < epsilon)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hband : epsilon < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) mover) :
    Nonempty (QuittingCapBandFiniteCut reward profile mover epsilon) := by
  classical
  let value := quittingCapBandClockValue reward profile mover
  let cap := quittingContinuationBestResponseValue reward profile mover
  let source := quittingCapBandSourceLaw reward profile mover
  have hvalue : ∀ choice, |value choice| ≤ M := by
    intro choice
    exact abs_quittingTerminalPayoff_le reward _ mover hreward
  have hvalueCap : ∀ choice, value choice ≤ cap := by
    intro choice
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile mover _
  have hcap : |cap| ≤ M :=
    abs_quittingContinuationBestResponseValue_le reward profile mover hreward
  have hsourcePayoff : expect source value =
      quittingTerminalPayoff reward profile mover := by
    exact (quittingTerminalPayoff_eq_expect_behaviorStoppingLaw_pureTime
      reward profile mover mover).symm
  have hsourceDebt : stoppingLawSourceCapDebt source value cap =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) mover := by
    unfold stoppingLawSourceCapDebt quittingTerminalSemanticDebt
      quittingTerminalSemanticPair
    rw [hsourcePayoff]
  have hmassPos : 0 < stoppingLawOutsideCapBandMass source value cap epsilon := by
    apply stoppingLawOutsideCapBandMass_pos source value cap epsilon M hM
      hepsilon.le hcap hvalue hvalueCap
    rwa [hsourceDebt]
  have hsup : cap = sSup (Set.range value) := by
    unfold cap value quittingCapBandClockValue
      quittingContinuationBestResponseValue
    exact sSup_range_quittingTerminalPayoff_update_eq_pureTime
      reward profile mover
  have hrange : (Set.range value).Nonempty :=
    ⟨value none, Set.mem_range_self none⟩
  have hnear : cap - epsilon / 2 < sSup (Set.range value) := by
    rw [← hsup]
    linarith
  obtain ⟨_, ⟨receiver, rfl⟩, hreceiverNear⟩ :=
    exists_lt_of_lt_csSup hrange hnear
  let bad : Option ℕ → Prop :=
    stoppingLawOutsideCapBand value cap epsilon
  let hazard := quittingBehaviorLiveHazard reward (profile mover)
  have hsourceLaw : quittingHazardStoppingLaw hazard = source := rfl
  have hselection := quittingStoppingLaw_exists_leastBad_survival_lowerBound
    hazard bad
  rcases hselection with hnever | ⟨first, hfirstBad, hfirstPos,
      hzeroBefore, hmassLe⟩
  · obtain ⟨witness, hwitnessSupport, hwitnessBad⟩ :=
      exists_mem_support_stoppingLawOutsideCapBand source value cap epsilon
        hmassPos
    have hwitnessNone : witness = none := by
      cases witness with
      | none => rfl
      | some time =>
          have hstopZero := hnever.2 time hwitnessBad
          have hlawZero : source (some time) = 0 := by
            apply pmf_eq_zero_of_toReal_eq_zero source (some time)
            simpa [source, hazard] using hstopZero
          exact False.elim
            ((PMF.mem_support_iff source (some time)).mp hwitnessSupport
              hlawZero)
    have hnoneBad : bad none := by simpa [hwitnessNone] using hwitnessBad
    have hreceiverNotNone : receiver ≠ none := by
      intro hreceiverNone
      subst receiver
      unfold bad stoppingLawOutsideCapBand at hnoneBad
      linarith
    obtain ⟨receiverTime, hreceiverEq⟩ := Option.ne_none_iff_exists.mp
      hreceiverNotNone
    subst receiver
    refine ⟨⟨some receiverTime, receiverTime, hreceiverNear, ?_, ?_,
      hmassPos, ?_, ?_⟩⟩
    · intro earlier hearlier heq
      simp only [Option.some.injEq] at heq
      omega
    · intro earlier hearlier hearlierBad
      have hstopZero := hnever.2 earlier hearlierBad
      apply pmf_eq_zero_of_toReal_eq_zero source (some earlier)
      simpa [source, hazard] using hstopZero
    · have hneverLe : quittingHazardNeverMass hazard ≤
          StoppingLaw.survival source receiverTime := by
        have hsurvival := quittingHazardNeverMass_le_survival
          hazard receiverTime
        simpa [source, hazard,
          stoppingLawSurvival_quittingBehaviorStoppingLaw] using hsurvival
      have hbadMassLe : stoppingLawOutsideCapBandMass
          source value cap epsilon ≤ quittingHazardNeverMass hazard := by
        rw [← hsourceLaw]
        simpa [stoppingLawOutsideCapBandMass, bad, source, value, cap]
          using hnever.1
      exact hbadMassLe.trans hneverLe
    · left
      refine ⟨?_, ⟨receiverTime, rfl, rfl⟩⟩
      intro time htimeBad
      have hstopZero := hnever.2 time htimeBad
      apply pmf_eq_zero_of_toReal_eq_zero source (some time)
      simpa [source, hazard] using hstopZero
  · cases receiver with
    | none =>
        refine ⟨⟨none, first, hreceiverNear, ?_, ?_, hmassPos, ?_, ?_⟩⟩
        · intro earlier _ heq
          simp at heq
        · intro earlier hearlier hearlierBad
          have hstopZero := hzeroBefore earlier hearlier hearlierBad
          apply pmf_eq_zero_of_toReal_eq_zero source (some earlier)
          simpa [source, hazard] using hstopZero
        · have hmassLe' : stoppingLawOutsideCapBandMass
              source value cap epsilon ≤ quittingHazardSurvival hazard first := by
            rw [← hsourceLaw]
            simpa [stoppingLawOutsideCapBandMass, bad, source, value, cap]
              using hmassLe
          simpa [source, hazard,
            stoppingLawSurvival_quittingBehaviorStoppingLaw] using hmassLe'
        · right
          refine ⟨first, hfirstBad, ?_, ?_, by simp⟩
          · simpa [source, hazard] using hfirstPos
          · intro earlier hearlier hearlierBad
            have hstopZero := hzeroBefore earlier hearlier hearlierBad
            apply pmf_eq_zero_of_toReal_eq_zero source (some earlier)
            simpa [source, hazard] using hstopZero
    | some receiverTime =>
        let cut := min first receiverTime
        refine ⟨⟨some receiverTime, cut, hreceiverNear, ?_, ?_, hmassPos,
          ?_, ?_⟩⟩
        · intro earlier hearlier heq
          simp only [Option.some.injEq] at heq
          have hcutLe : cut ≤ receiverTime := Nat.min_le_right _ _
          omega
        · intro earlier hearlier hearlierBad
          have hcutLe : cut ≤ first := Nat.min_le_left _ _
          have hstopZero := hzeroBefore earlier
            (hearlier.trans_le hcutLe) hearlierBad
          apply pmf_eq_zero_of_toReal_eq_zero source (some earlier)
          simpa [source, hazard] using hstopZero
        · have hcutLe : cut ≤ first := Nat.min_le_left _ _
          have hmassLe' : stoppingLawOutsideCapBandMass
              source value cap epsilon ≤ quittingHazardSurvival hazard first := by
            rw [← hsourceLaw]
            simpa [stoppingLawOutsideCapBandMass, bad, source, value, cap]
              using hmassLe
          have hmassSource : stoppingLawOutsideCapBandMass
              source value cap epsilon ≤ StoppingLaw.survival source first := by
            simpa [source, hazard,
              stoppingLawSurvival_quittingBehaviorStoppingLaw] using hmassLe'
          have hantitone := StoppingLaw.survival_antitone source hcutLe
          exact hmassSource.trans hantitone
        · right
          refine ⟨first, hfirstBad, ?_, ?_, by simp [cut]⟩
          · simpa [source, hazard] using hfirstPos
          · intro earlier hearlier hearlierBad
            have hstopZero := hzeroBefore earlier hearlier hearlierBad
            apply pmf_eq_zero_of_toReal_eq_zero source (some earlier)
            simpa [source, hazard] using hstopZero

end GameTheory
