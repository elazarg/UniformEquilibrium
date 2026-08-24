/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.ArbitraryNeverExtraction
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedPositiveLiveLimit
import UniformEquilibrium.Quitting.Chronology.SummableExactTailTerminalGap
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryLimitGeometry

/-!
# The survival boundary of a compact support--Bellman spine

The compact spine extracted from approximate equilibria has an exact Bellman
recursion and support-local approximate optimality, but its displayed values
are not automatically the terminal values of its root sequence.  This file
gives the exhaustive semantic split.

If joint survival vanishes after every restart, the existing uniqueness
theorem identifies the displayed values with actual suffix payoffs and gives
the well-supported absorbing branch.  Otherwise one suffix has positive
limiting survival.  Its joint absorption clock is summable, the displayed
values converge to a boundary vector, and the exact discrepancy is

`displayed = actual terminal payoff + survival limit * boundary`.

The actual terminal payoffs of later suffixes tend to zero, whereas the
boundary need not.  Support optimality only forces each singleton reward
below the corresponding boundary coordinate plus the support tolerance.  A
one-player regression realizes a nonzero phantom boundary, so the second arm
cannot be silently decoded as the first or as a stationary/generated branch.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Positive limiting joint survival forces summability of the entire
one-stage joint absorption clock. -/
theorem summable_quittingRootAbsorptionMass_of_jointSurvivalLimit_pos
    (roots : ℕ → ι → PMF Bool) (start : ℕ)
    (hpositive : 0 < quittingJointSurvivalLimit roots start) :
    Summable (fun time ↦ quittingRootAbsorptionMass (roots time)) := by
  let charge : ℕ → ℝ := fun offset ↦
    quittingRootAbsorptionMass (roots (start + offset))
  have hchargeNonneg : ∀ offset, 0 ≤ charge offset := by
    intro offset
    exact sub_nonneg.mpr
      (quittingStationaryContinueMass_le_one (roots (start + offset)))
  have htail : Summable charge := by
    apply summable_of_sum_range_le (c := 1 / quittingJointSurvivalLimit roots start)
      hchargeNonneg
    intro fuel
    have hweighted :
        quittingJointSurvivalLimit roots start *
            (∑ offset ∈ Finset.range fuel, charge offset) ≤
          1 - quittingJointSurvivalWeight roots start fuel := by
      rw [Finset.mul_sum]
      calc
        (∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalLimit roots start * charge offset) ≤
            ∑ offset ∈ Finset.range fuel,
              quittingJointSurvivalWeight roots start offset *
                (1 - quittingStationaryContinueMass
                  (roots (start + offset))) := by
          apply Finset.sum_le_sum
          intro offset _
          apply mul_le_mul_of_nonneg_right
          · exact le_quittingJointSurvivalWeight_of_tendsto roots start
              (tendsto_quittingJointSurvivalLimit roots start) offset
          · exact hchargeNonneg offset
        _ = 1 - quittingJointSurvivalWeight roots start fuel :=
          sum_quittingJointSurvivalWeight_mul_one_sub_continueMass
            roots start fuel
    apply (le_div_iff₀ hpositive).2
    calc
      (∑ offset ∈ Finset.range fuel, charge offset) *
          quittingJointSurvivalLimit roots start =
          quittingJointSurvivalLimit roots start *
            (∑ offset ∈ Finset.range fuel, charge offset) := by ring
      _ ≤ 1 - quittingJointSurvivalWeight roots start fuel := hweighted
      _ ≤ 1 := by
        linarith [quittingJointSurvivalWeight_nonneg roots start fuel]
  have hshift : Summable (fun offset ↦
      quittingRootAbsorptionMass (roots (offset + start))) := by
    simpa [charge, Nat.add_comm] using htail
  exact (summable_nat_add_iff
    (f := fun time ↦ quittingRootAbsorptionMass (roots time)) start).1 hshift

omit [DecidableEq ι] in
/-- Every row in a positive-survival suffix has positive one-stage joint
Continue mass. -/
theorem quittingStationaryContinueMass_pos_of_jointSurvivalLimit_pos
    (roots : ℕ → ι → PMF Bool) (start offset : ℕ)
    (hpositive : 0 < quittingJointSurvivalLimit roots start) :
    0 < quittingStationaryContinueMass (roots (start + offset)) := by
  have hlower := le_quittingJointSurvivalWeight_of_tendsto roots start
    (tendsto_quittingJointSurvivalLimit roots start) (offset + 1)
  have hproduct : 0 < quittingJointSurvivalWeight roots start (offset + 1) :=
    hpositive.trans_le hlower
  rw [quittingJointSurvivalWeight_succ] at hproduct
  exact pos_of_mul_pos_right hproduct
    (quittingJointSurvivalWeight_nonneg roots start offset)

/-- Support-local optimality on a positive-survival Bellman suffix forces
each singleton reward below the limiting annotation, up to the support
tolerance. -/
theorem quittingSingletonReward_le_boundary_add_of_positiveSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (δ M : ℝ) (start : ℕ)
    (hpositive : 0 < quittingJointSurvivalLimit roots start)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hvalue : ∀ time who, |value time who| ≤ M)
    (hsupport : ∀ time,
      IsQuittingRootSupportApproxNash reward
        (value (time + 1)) δ (roots time))
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (boundary : Payoff ι)
    (hboundary : ∀ who,
      Tendsto (fun time ↦ value time who) atTop (nhds (boundary who)))
    (who : ι) :
    reward (quittingSingletonTerminal who) who ≤ boundary who + δ := by
  have hchargeZero : Tendsto (fun time ↦
      quittingRootAbsorptionMass (roots time)) atTop (nhds 0) :=
    hcharge.tendsto_atTop_zero
  have htime : Tendsto (fun offset ↦ start + offset) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat start
  have hopponentZero : Tendsto (fun offset ↦
      quittingRootOpponentAbsorptionMass (roots (start + offset)) who)
      atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun _ ↦ quittingRootOpponentAbsorptionMass_nonneg _ _
    · exact fun offset ↦
        quittingRootOpponentAbsorptionMass_le_absorptionMass
          (roots (start + offset)) who
    · exact hchargeZero.comp htime
  have hvalueTail : Tendsto (fun offset ↦ value (start + offset + 1) who)
      atTop (nhds (boundary who)) := by
    have htimeSucc : Tendsto (fun offset ↦ start + offset + 1) atTop atTop := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        tendsto_add_atTop_nat (start + 1)
    exact (hboundary who).comp htimeSucc
  have hlower : Tendsto (fun offset ↦
      reward (quittingSingletonTerminal who) who -
        4 * M * quittingRootOpponentAbsorptionMass
          (roots (start + offset)) who) atTop
      (nhds (reward (quittingSingletonTerminal who) who)) := by
    simpa using tendsto_const_nhds.sub
      (hopponentZero.const_mul (4 * M))
  have hupper : Tendsto (fun offset ↦
      value (start + offset + 1) who + δ) atTop
      (nhds (boundary who + δ)) := by
    exact hvalueTail.add_const δ
  apply le_of_tendsto_of_tendsto' hlower hupper
  intro offset
  let time := start + offset
  have hjoint : 0 < quittingStationaryContinueMass (roots time) := by
    exact quittingStationaryContinueMass_pos_of_jointSurvivalLimit_pos
      roots start offset hpositive
  have hcontinue : 0 < (roots time who false).toReal :=
    hjoint.trans_le
      (quittingStationaryContinueMass_le_ownContinueProbability
        (roots time) who)
  have hsupportContinue := (hsupport time who).2 hcontinue
  rw [quittingRootEndpointDifference] at hsupportContinue
  have hquit :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (value (time + 1)) (roots time) who M hreward
  have hcontinueEstimate :=
    abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
      reward (value (time + 1))
        (Function.update (roots time) who (PMF.pure false)) who M hreward
        (hvalue (time + 1) who)
  change
    |quittingRootContinuePayoff reward (value (time + 1)) (roots time) who -
        value (time + 1) who| ≤
      2 * M * quittingRootOpponentAbsorptionMass (roots time) who
    at hcontinueEstimate
  linarith [abs_le.mp hquit |>.1, abs_le.mp hcontinueEstimate |>.2]

/-- The precise positive-survival residual of a bounded support--Bellman
spine.  It retains the source spine and records the semantic boundary rather
than replacing it by an unrelated stationary root. -/
structure QuittingSupportBellmanPositiveSurvivalBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ) where
  value : ℕ → Payoff ι
  roots : ℕ → ι → PMF Bool
  start : ℕ
  survival_pos : 0 < quittingJointSurvivalLimit roots start
  value_bound : ∀ time who,
    |value time who| ≤ quittingRewardBound reward
  bellman : ∀ time, value time =
    quittingRootSuccessorPayoff reward (value (time + 1)) (roots time)
  support : ∀ time,
    IsQuittingRootSupportApproxNash reward (value (time + 1)) δ (roots time)
  absorption_summable :
    Summable (fun time ↦ quittingRootAbsorptionMass (roots time))
  boundary : Payoff ι
  value_tendsto : ∀ who,
    Tendsto (fun time ↦ value time who) atTop (nhds (boundary who))
  boundary_bound : ∀ who,
    |boundary who| ≤ quittingRewardBound reward
  value_eq_terminal_add_boundary : ∀ time,
    value time = fun who ↦
      quittingRootSequenceTerminalValue reward roots who time +
        quittingJointSurvivalLimit roots time * boundary who
  tail_survival_tendsto_one : Tendsto (fun cutoff ↦
    quittingJointSurvivalLimit roots (start + cutoff)) atTop (nhds 1)
  terminal_tail_tendsto_zero : ∀ who,
    Tendsto (fun cutoff ↦
      quittingRootSequenceTerminalValue reward roots who (start + cutoff))
      atTop (nhds 0)
  singleton_le_boundary_add : ∀ who,
    reward (quittingSingletonTerminal who) who ≤ boundary who + δ

/-- A positive-survival bounded support--Bellman spine has the exact phantom
boundary structure recorded above. -/
theorem exists_quittingSupportBellmanPositiveSurvivalBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool) (δ : ℝ)
    (start : ℕ)
    (hpositive : 0 < quittingJointSurvivalLimit roots start)
    (hvalue : ∀ time who,
      |value time who| ≤ quittingRewardBound reward)
    (hbellman : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hsupport : ∀ time,
      IsQuittingRootSupportApproxNash reward
        (value (time + 1)) δ (roots time)) :
    Nonempty (QuittingSupportBellmanPositiveSurvivalBoundary reward δ) := by
  have hcharge :=
    summable_quittingRootAbsorptionMass_of_jointSurvivalLimit_pos
      roots start hpositive
  obtain ⟨boundary, hboundary, _hmodulus⟩ :=
    exists_quittingAnnotationBoundary_of_summableAbsorption
      reward roots value hbellman
      (abs_reward_le_quittingRewardBound reward) hvalue hcharge
  refine ⟨{
    value := value
    roots := roots
    start := start
    survival_pos := hpositive
    value_bound := hvalue
    bellman := hbellman
    support := hsupport
    absorption_summable := hcharge
    boundary := boundary
    value_tendsto := hboundary
    boundary_bound := ?_
    value_eq_terminal_add_boundary := ?_
    tail_survival_tendsto_one := ?_
    terminal_tail_tendsto_zero := ?_
    singleton_le_boundary_add := ?_ }⟩
  · intro who
    exact le_of_tendsto (hboundary who).abs
      (Filter.Eventually.of_forall fun time ↦ hvalue time who)
  · intro time
    exact quittingValuePath_eq_terminalValue_add_survivalLimit_mul
      reward roots value hbellman boundary hboundary time
  · exact tendsto_quittingJointSurvivalLimit_tail_one_of_pos
      roots start hpositive
  · intro who
    exact
      tendsto_quittingRootSequenceTerminalValue_tail_zero_of_survivalLimit_pos
        reward roots who start (abs_reward_le_quittingRewardBound reward)
        hpositive
  · intro who
    exact quittingSingletonReward_le_boundary_add_of_positiveSurvival
      reward roots value δ (quittingRewardBound reward) start hpositive
      (abs_reward_le_quittingRewardBound reward) hvalue hsupport hcharge
      boundary hboundary who

namespace QuittingSupportBellmanPositiveSurvivalBoundary

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {δ : ℝ}
variable (datum : QuittingSupportBellmanPositiveSurvivalBoundary reward δ)

/-- Forgetting support-local information gives exactly the source expected by
the checked unrestricted terminal-gap analysis. -/
def toSummableExactValueTail : QuittingSummableExactValueTail reward where
  roots := datum.roots
  value := datum.value
  boundary := datum.boundary
  bellman := datum.bellman
  value_tendsto := datum.value_tendsto
  absorption_summable := datum.absorption_summable

/-- Actual prescribed terminal payoffs of later executable suffixes converge
to zero. -/
theorem suffixTerminalPayoff_tendsto_zero (who : ι) :
    Tendsto (fun start ↦ quittingTerminalPayoff reward
      (datum.toSummableExactValueTail.suffixProfile start) who)
      atTop (nhds 0) :=
  datum.toSummableExactValueTail.terminalPayoff_tendsto_zero who

/-- Actual unrestricted exploitability of later executable suffixes converges
to the positive part of the literal singleton reward. -/
theorem suffixGain_tendsto_max_singleton (who : ι) :
    Tendsto (fun start ↦
      datum.toSummableExactValueTail.suffixGain start who) atTop
      (nhds (max 0 (reward (quittingSingletonTerminal who) who))) :=
  datum.toSummableExactValueTail.suffixGain_tendsto_max_solo who

/-- The annotation-to-terminal discrepancy converges to the retained phantom
boundary.  This is an identity about the actual executable suffix profiles,
not an identification of their payoffs with the annotations. -/
theorem annotation_sub_suffixTerminalPayoff_tendsto_boundary (who : ι) :
    Tendsto (fun start ↦ datum.value start who -
      quittingTerminalPayoff reward
        (datum.toSummableExactValueTail.suffixProfile start) who)
      atTop (nhds (datum.boundary who)) := by
  simpa using (datum.value_tendsto who).sub
    (datum.suffixTerminalPayoff_tendsto_zero who)

/-- Support-local optimality makes a singleton reward which exceeds the
support tolerance force a strictly positive phantom coordinate. -/
theorem boundary_pos_of_tolerance_lt_singleton (who : ι)
    (hsolo : δ < reward (quittingSingletonTerminal who) who) :
    0 < datum.boundary who := by
  linarith [datum.singleton_le_boundary_add who]

/-- If a player's actual unrestricted suffix gain exceeds `ε`, that suffix
is not an `ε` terminal Nash profile. -/
theorem not_suffixProfile_isTerminalNash_of_lt_suffixGain
    (start : ℕ) (who : ι) (ε : ℝ) (hε : 0 ≤ ε)
    (hgain : ε < datum.toSummableExactValueTail.suffixGain start who) :
    ¬ (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (datum.toSummableExactValueTail.suffixProfile start) := by
  intro hnash
  let tail := datum.toSummableExactValueTail
  have hbest : tail.suffixBestResponseValue start who ≤
      quittingTerminalPayoff reward (tail.suffixProfile start) who + ε := by
    unfold QuittingSummableExactValueTail.suffixBestResponseValue
      quittingContinuationBestResponseValue
    refine csSup_le ⟨_, Set.mem_range_self ((tail.suffixProfile start) who)⟩ ?_
    rintro payoff ⟨deviation, rfl⟩
    exact hnash who deviation
  have hdiff : tail.suffixBestResponseValue start who -
      quittingTerminalPayoff reward (tail.suffixProfile start) who ≤ ε :=
    by linarith [hbest]
  have hgainUpper : tail.suffixGain start who ≤ ε := by
    unfold QuittingSummableExactValueTail.suffixGain
    exact max_le hε hdiff
  exact (not_lt_of_ge hgainUpper) hgain

/-- A positive singleton reward creates a fixed late-suffix unrestricted
deviation gap: every sufficiently late executable suffix fails terminal Nash
at half that reward. -/
theorem eventually_not_suffixProfile_isTerminalNash_of_singleton_pos
    (who : ι)
    (hsolo : 0 < reward (quittingSingletonTerminal who) who) :
    ∃ threshold, ∀ start, threshold ≤ start →
      ¬ (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        (reward (quittingSingletonTerminal who) who / 2)
        (datum.toSummableExactValueTail.suffixProfile start) := by
  have hgain : Tendsto (fun start ↦
      datum.toSummableExactValueTail.suffixGain start who) atTop
      (nhds (reward (quittingSingletonTerminal who) who)) := by
    simpa [max_eq_right hsolo.le] using
      datum.suffixGain_tendsto_max_singleton who
  have heventually : ∀ᶠ start in atTop,
      reward (quittingSingletonTerminal who) who / 2 <
        datum.toSummableExactValueTail.suffixGain start who :=
    (tendsto_order.1 hgain).1 _ (by linarith)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 heventually
  refine ⟨threshold, fun start hstart ↦ ?_⟩
  exact datum.not_suffixProfile_isTerminalNash_of_lt_suffixGain
    start who _ (by linarith) (hthreshold start hstart)

/-- A positive singleton reward is witnessed by actual behavioral deviations,
not only by the best-response supremum: sufficiently late suffixes admit a
deviation improving the prescribed terminal payoff by more than half the
singleton reward. -/
theorem eventually_exists_suffixDeviation_gain_gt_half_singleton
    (who : ι)
    (hsolo : 0 < reward (quittingSingletonTerminal who) who) :
    ∃ threshold, ∀ start, threshold ≤ start →
      ∃ deviation : (quittingGame reward).BehaviorStrategy who,
        quittingTerminalPayoff reward
            (datum.toSummableExactValueTail.suffixProfile start) who +
            reward (quittingSingletonTerminal who) who / 2 <
          quittingTerminalPayoff reward
            (Function.update
              (datum.toSummableExactValueTail.suffixProfile start)
              who deviation) who := by
  let solo := reward (quittingSingletonTerminal who) who
  let tail := datum.toSummableExactValueTail
  have hgain : Tendsto (fun start ↦ tail.suffixGain start who) atTop
      (nhds solo) := by
    simpa [tail, solo, max_eq_right hsolo.le] using
      datum.suffixGain_tendsto_max_singleton who
  have heventually : ∀ᶠ start in atTop,
      3 * solo / 4 < tail.suffixGain start who :=
    (tendsto_order.1 hgain).1 _ (by dsimp [solo]; linarith)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 heventually
  refine ⟨threshold, fun start hstart ↦ ?_⟩
  have hlate := hthreshold start hstart
  have hdiff : 3 * solo / 4 <
      tail.suffixBestResponseValue start who -
        quittingTerminalPayoff reward (tail.suffixProfile start) who := by
    unfold QuittingSummableExactValueTail.suffixGain at hlate
    by_cases hnonpos : tail.suffixBestResponseValue start who -
        quittingTerminalPayoff reward (tail.suffixProfile start) who ≤ 0
    · rw [max_eq_left hnonpos] at hlate
      dsimp [solo] at hlate
      linarith
    · rwa [max_eq_right (le_of_not_ge hnonpos)] at hlate
  have hquarter : 0 < solo / 4 := by
    dsimp [solo]
    linarith
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub reward
      (tail.suffixProfile start) who hquarter
  change tail.suffixBestResponseValue start who - solo / 4 ≤
    quittingTerminalPayoff reward
      (Function.update (tail.suffixProfile start) who deviation) who
    at hdeviation
  refine ⟨deviation, ?_⟩
  dsimp [tail, solo] at hdiff hdeviation ⊢
  linarith

/-- The complete checked defect carried by a positive singleton coordinate of
a phantom spine.  It combines the annotation mismatch with an actual
unrestricted suffix-deviation gap. -/
structure PositiveSingletonSuffixDefect
    (datum : QuittingSupportBellmanPositiveSurvivalBoundary reward δ) where
  who : ι
  singleton_pos : 0 < reward (quittingSingletonTerminal who) who
  annotation_terminal_tendsto : Tendsto (fun start ↦
    datum.value start who - quittingTerminalPayoff reward
      (datum.toSummableExactValueTail.suffixProfile start) who)
    atTop (nhds (datum.boundary who))
  gain_tendsto_singleton : Tendsto (fun start ↦
    datum.toSummableExactValueTail.suffixGain start who) atTop
    (nhds (reward (quittingSingletonTerminal who) who))
  boundary_pos_of_above_tolerance :
    δ < reward (quittingSingletonTerminal who) who →
      0 < datum.boundary who
  eventually_not_halfSingleton_terminalNash :
    ∃ threshold, ∀ start, threshold ≤ start →
      ¬ (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        (reward (quittingSingletonTerminal who) who / 2)
        (datum.toSummableExactValueTail.suffixProfile start)
  eventually_exists_halfSingleton_deviation :
    ∃ threshold, ∀ start, threshold ≤ start →
      ∃ deviation : (quittingGame reward).BehaviorStrategy who,
        quittingTerminalPayoff reward
            (datum.toSummableExactValueTail.suffixProfile start) who +
            reward (quittingSingletonTerminal who) who / 2 <
          quittingTerminalPayoff reward
            (Function.update
              (datum.toSummableExactValueTail.suffixProfile start)
              who deviation) who

/-- Every positive singleton coordinate canonically supplies the full phantom
suffix defect certificate. -/
def positiveSingletonSuffixDefectOf (who : ι)
    (hsolo : 0 < reward (quittingSingletonTerminal who) who) :
    datum.PositiveSingletonSuffixDefect where
  who := who
  singleton_pos := hsolo
  annotation_terminal_tendsto :=
    datum.annotation_sub_suffixTerminalPayoff_tendsto_boundary who
  gain_tendsto_singleton := by
    simpa [max_eq_right hsolo.le] using
      datum.suffixGain_tendsto_max_singleton who
  boundary_pos_of_above_tolerance :=
    datum.boundary_pos_of_tolerance_lt_singleton who
  eventually_not_halfSingleton_terminalNash :=
    datum.eventually_not_suffixProfile_isTerminalNash_of_singleton_pos
      who hsolo
  eventually_exists_halfSingleton_deviation :=
    datum.eventually_exists_suffixDeviation_gain_gt_half_singleton
      who hsolo

/-- At the level of actual suffix semantics, a phantom residual either closes
the nonpositive-solo game at payoff zero or carries a positive singleton
defect certificate. -/
theorem zero_isUniformEquilibriumPayoff_or_nonempty_positiveSingletonSuffixDefect
    [Nonempty ι] :
    (quittingGame reward).IsUniformEquilibriumPayoff none (0 : Payoff ι) ∨
      Nonempty datum.PositiveSingletonSuffixDefect := by
  by_cases hsolo : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ 0
  · exact Or.inl
      (QuittingSummableExactValueTail.zero_isUniformEquilibriumPayoff_of_nonpositive_solo
        datum.toSummableExactValueTail hsolo)
  · right
    push Not at hsolo
    obtain ⟨who, hwho⟩ := hsolo
    exact ⟨datum.positiveSingletonSuffixDefectOf who hwho⟩

/-- The positive-survival residual has a complete actual-semantic fork.  If
all singleton self-rewards are nonpositive, its late suffixes yield the
checked zero uniform payoff.  Otherwise some actual unrestricted suffix gain
stays bounded away from zero. -/
theorem zero_isUniformEquilibriumPayoff_or_exists_persistent_positiveSuffixGap
    [Nonempty ι] :
    (quittingGame reward).IsUniformEquilibriumPayoff none (0 : Payoff ι) ∨
      ∃ who, 0 < reward (quittingSingletonTerminal who) who ∧
        ∃ threshold, ∀ start, threshold ≤ start →
          ¬ (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward)
            (reward (quittingSingletonTerminal who) who / 2)
            (datum.toSummableExactValueTail.suffixProfile start) := by
  by_cases hsolo : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ 0
  · exact Or.inl
      (QuittingSummableExactValueTail.zero_isUniformEquilibriumPayoff_of_nonpositive_solo
        datum.toSummableExactValueTail hsolo)
  · right
    push Not at hsolo
    obtain ⟨who, hwho⟩ := hsolo
    exact ⟨who, hwho,
      datum.eventually_not_suffixProfile_isTerminalNash_of_singleton_pos
        who hwho⟩

end QuittingSupportBellmanPositiveSurvivalBoundary

/-- The semantic alternatives for a bounded exact support--Bellman spine are
exhaustive: either every restart absorbs and the roots form an actual
well-supported absorbing sequence, or one restart retains the precise
positive-survival boundary datum. -/
theorem
    quittingWellSupportedAbsorbingSequenceAt_or_exists_positiveSurvivalBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool) (δ : ℝ)
    (hvalue : ∀ time who,
      |value time who| ≤ quittingRewardBound reward)
    (hbellman : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hsupport : ∀ time,
      IsQuittingRootSupportApproxNash reward
        (value (time + 1)) δ (roots time)) :
    QuittingWellSupportedAbsorbingSequenceAt reward δ ∨
      Nonempty (QuittingSupportBellmanPositiveSurvivalBoundary reward δ) := by
  by_cases hvanish : ∀ start, quittingJointSurvivalLimit roots start = 0
  · left
    apply
      quittingWellSupportedAbsorbingSequenceAt_of_boundedSupportBellmanSpine_of_jointSurvival
        reward value roots
    · intro start
      simpa [hvanish start] using
        tendsto_quittingJointSurvivalLimit roots start
    · exact abs_reward_le_quittingRewardBound reward
    · exact hvalue
    · exact hbellman
    · exact hsupport
  · right
    push Not at hvanish
    obtain ⟨start, hstart⟩ := hvanish
    have hpositive : 0 < quittingJointSurvivalLimit roots start :=
      lt_of_le_of_ne (quittingJointSurvivalLimit_nonneg roots start)
        (Ne.symm hstart)
    exact exists_quittingSupportBellmanPositiveSurvivalBoundary
      reward value roots δ start hpositive hvalue hbellman hsupport

namespace QuittingLCPClassification

/-- Applying the exhaustive semantic split to the compact-spine arm of the
source-faithful arbitrary-never extraction.  The last disjunct is a phantom
boundary, not a stationary or generated equilibrium witness. -/
theorem
    QuittingPayoffTable.lowSurvivalPrefix_or_wellSupported_or_positiveSurvivalBoundary
    (table : QuittingPayoffTable ι)
    (hequilibrium : table.ApproximateEquilibriumExistence)
    (δ u : ℝ) (hδ : 0 < δ) (hu : 0 < u) :
    (∃ horizon,
      QuittingLowSurvivalApproximatePrefixAt table.zeroNeverReward u
        (u * quittingSimonReachedPrefixThreshold δ *
          quittingSimonReachedPrefixDisplacement
            (ι := ι) (quittingRewardBound table.zeroNeverReward) δ horizon / 2)
        horizon) ∨
      QuittingWellSupportedAbsorbingSequenceAt table.zeroNeverReward δ ∨
      Nonempty (QuittingSupportBellmanPositiveSurvivalBoundary
        table.zeroNeverReward δ) := by
  obtain hpref | ⟨value, roots, hvalue, hbellman, hsupport⟩ :=
    table.lowSurvivalPrefix_or_exists_boundedSupportBellmanSpine
      hequilibrium δ u hδ hu
  · exact Or.inl hpref
  · exact Or.inr
      (quittingWellSupportedAbsorbingSequenceAt_or_exists_positiveSurvivalBoundary
        table.zeroNeverReward value roots δ hvalue hbellman hsupport)

/-- The source-faithful compactification with the phantom arm resolved as far
as actual unrestricted terminal semantics permit.  The final disjunct is a
genuine persistent suffix defect, not an equilibrium witness. -/
theorem QuittingPayoffTable.lowSurvivalPrefix_or_wellSupported_or_zeroPayoff_or_suffixDefect
    [Nonempty ι]
    (table : QuittingPayoffTable ι)
    (hequilibrium : table.ApproximateEquilibriumExistence)
    (δ u : ℝ) (hδ : 0 < δ) (hu : 0 < u) :
    (∃ horizon,
      QuittingLowSurvivalApproximatePrefixAt table.zeroNeverReward u
        (u * quittingSimonReachedPrefixThreshold δ *
          quittingSimonReachedPrefixDisplacement
            (ι := ι) (quittingRewardBound table.zeroNeverReward) δ horizon / 2)
        horizon) ∨
      QuittingWellSupportedAbsorbingSequenceAt table.zeroNeverReward δ ∨
      (quittingGame table.zeroNeverReward).IsUniformEquilibriumPayoff
        none (0 : Payoff ι) ∨
      ∃ datum : QuittingSupportBellmanPositiveSurvivalBoundary
          table.zeroNeverReward δ,
        Nonempty datum.PositiveSingletonSuffixDefect := by
  obtain hpref | hwell | hboundary :=
    table.lowSurvivalPrefix_or_wellSupported_or_positiveSurvivalBoundary
      hequilibrium δ u hδ hu
  · exact Or.inl hpref
  · exact Or.inr (Or.inl hwell)
  · obtain ⟨datum⟩ := hboundary
    rcases
        datum.zero_isUniformEquilibriumPayoff_or_nonempty_positiveSingletonSuffixDefect
      with hzero | hdefect
    · exact Or.inr (Or.inr (Or.inl hzero))
    · exact Or.inr (Or.inr (Or.inr ⟨datum, hdefect⟩))

end QuittingLCPClassification

namespace CompactSpineSurvivalBoundaryRegression

open StationaryPrefixEndpointDecouplingRegression

/-- The constant all-Continue roots used to realize the phantom arm. -/
def roots : ℕ → PUnit → PMF Bool := fun _ ↦ quittingAllContinueRoot

/-- The all-Continue sequence has unit limiting survival after every
restart. -/
theorem survivalLimit_eq_one (start : ℕ) :
    quittingJointSurvivalLimit roots start = 1 := by
  have hweight : quittingJointSurvivalWeight roots start = fun _ ↦ 1 := by
    funext fuel
    simp [roots, quittingJointSurvivalWeight_eq_prod,
      quittingStationaryContinueMass_eq_prod_continueProbability,
      quittingAllContinueRoot]
  apply tendsto_nhds_unique
    (tendsto_quittingJointSurvivalLimit roots start)
  rw [hweight]
  exact tendsto_const_nhds

/-- The positive-survival arm is genuinely semantic: an exact bounded
support--Bellman spine can have positive survival after every restart while
its displayed value differs from its production terminal payoff.  Hence no
unconditional adapter may identify the compact annotation with the actual
suffix payoff. -/
theorem exists_positiveSurvival_supportBellmanSpine_with_terminal_mismatch :
    ∃ (value : ℕ → Payoff PUnit) (roots : ℕ → PUnit → PMF Bool),
      (∀ time who, |value time who| ≤ quittingRewardBound reward) ∧
      (∀ time, value time =
        quittingRootSuccessorPayoff reward (value (time + 1)) (roots time)) ∧
      (∀ time, IsQuittingRootSupportApproxNash reward
        (value (time + 1)) 0 (roots time)) ∧
      (∀ start, 0 < quittingJointSurvivalLimit roots start) ∧
      value 0 PUnit.unit ≠
        quittingRootSequenceTerminalValue reward roots PUnit.unit 0 := by
  refine ⟨value, roots, ?_, ?_, ?_, ?_, ?_⟩
  · intro time who
    simp [value, rewardBound_eq_one]
  · intro time
    change value time = quittingRootSuccessorPayoff reward
      (value (time + 1)) quittingAllContinueRoot
    rw [quittingRootSuccessorPayoff_allContinueRoot_eq]
    rfl
  · intro time who
    have hendpoint : IsεQuittingRootEndpointNash reward
        (value (time + 1)) 0 quittingAllContinueRoot := by
      simpa [limit] using limit.endpointNash time
    constructor
    · intro hquit
      simp [roots, quittingAllContinueRoot] at hquit
    · intro _
      simpa [roots, quittingAllContinueRoot] using (hendpoint who).1
  · intro start
    rw [survivalLimit_eq_one]
    norm_num
  · rw [quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
      reward roots PUnit.unit 0 (fun _ _ ↦ rfl)]
    norm_num [value]

end CompactSpineSurvivalBoundaryRegression

end GameTheory
