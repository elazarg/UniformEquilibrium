/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.RawPassiveRowInverseCriterion
import UniformEquilibrium.Quitting.Cycles.CyclicFiniteMenu
import UniformEquilibrium.Quitting.Cycles.RationalSingletonFiniteCalendar
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineSignedHorizonError

/-!
# Retained finite quiet witnesses at the weak inverse boundary

The strict perturbations retain the original outside-row weights. Their actual
finite chronological calendars are realized by independent date-or-Never laws.
Reward robustness transports these same profiles to the original table; deleted
players retain literal Never, hence AlwaysContinue at every history.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem finiteTiming_pure_none_of_law_none {deadline : ℕ}
    (mixed : PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnever : (quittingFiniteDeadlineTimingLaw mixed).toPMF = PMF.pure none) :
    mixed = PMF.pure none := by
  have hmass : mixed none = 1 := by
    have heq := congrArg
      (fun law : PMF Math.Probability.CompactStoppingTime =>
        law (⊤ : Math.Probability.CompactStoppingTime)) hnever
    exact (quittingFiniteDeadlineTimingLaw_none mixed).symm.trans
      (heq.trans (PMF.pure_apply_self _))
  have hsupport := (mixed.apply_eq_one_iff none).mp hmass
  by_contra hnot
  obtain ⟨choice, hchoice, hmassChoice⟩ :=
    Math.ProbabilityMassFunction.exists_ne_of_ne_pure mixed hnot
  have hmem : choice ∈ mixed.support := by
    simpa only [PMF.mem_support_iff] using hmassChoice
  rw [hsupport] at hmem
  exact hchoice (by simpa using hmem)

/-- A balanced source whose owners avoid the deleted set has actual finite
independent timing laws with literal Never outside and complete terminal Nash. -/
theorem BalancedSingletonCycleCertificate.exists_quiet_finiteTiming_terminalNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (certificate : BalancedSingletonCycleCertificate (L := 3) reward)
    (deleted : ι → Prop)
    (howners : ∀ phase, ¬ deleted (certificate.owner phase))
    (accuracy : ℝ) (haccuracy : 0 < accuracy) :
    ∃ (deadline : ℕ) (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)),
      0 < deadline ∧
      (∀ who, deleted who → mixed who = PMF.pure none) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) := by
  let M := quittingRewardBound reward + 1
  have hM : 0 < M := by
    dsimp [M]
    linarith [quittingRewardBound_nonneg reward]
  have hreward : ∀ terminal who, |reward terminal who| ≤ M :=
    fun terminal who => (abs_reward_le_quittingRewardBound reward terminal who).trans
      (by dsimp [M]; linarith)
  let η := min accuracy M
  have hη : 0 < η := lt_min haccuracy hM
  have hηM : η ≤ M := min_le_right _ _
  have hηaccuracy : η ≤ accuracy := min_le_left _ _
  have hproduct (who : ι) :
      0 ≤ ∏ phase : Fin 3,
        if who = certificate.owner phase then 1 else 1 - certificate.hazard phase := by
    apply Finset.prod_nonneg
    intro phase _
    split_ifs
    · norm_num
    · exact (sub_pos.mpr (certificate.hazard_lt_one phase)).le
  have hcap : 0 ≤ certificate.opponentProductCap :=
    (hproduct (certificate.owner certificate.initial)).trans
      (certificate.opponent_product_le_cap _)
  have htolerance : 0 < η / (6 * M) := div_pos hη (by positivity)
  obtain ⟨turns, hturns⟩ := exists_pow_lt_of_lt_one htolerance
    certificate.opponentProductCap_lt_one
  let K := turns + 1
  have hK : 0 < K := Nat.succ_pos _
  have hcut : ∀ who,
      (∏ phase : Fin 3,
        if who = certificate.owner phase then 1 else 1 - certificate.hazard phase) ^ K ≤
        η / (6 * M) := by
    intro who
    apply (pow_le_pow_left₀ (hproduct who)
      (certificate.opponent_product_le_cap who) K).trans
    dsimp [K]
    rw [pow_succ]
    exact (mul_le_of_le_one_right (pow_nonneg hcap _)
      certificate.opponentProductCap_lt_one.le).trans hturns.le
  let mesh := η / (4 * M)
  let deadline := K * certificate.rationalPeriod mesh
  have hdeadline : 0 < deadline := Nat.mul_pos hK
    (Nat.zero_lt_of_lt (certificate.rationalInitial mesh).isLt)
  obtain ⟨mixed, hlaws, hpair, _⟩ := exists_finiteDeadlineTimingProfile_cyclicFinite_exact
    reward (certificate.rationalRoot mesh) (certificate.rationalInitial mesh) deadline
  have hsource := certificate.rationalFiniteProfile_isTerminalNash_and_delivery_le
    hreward hη hηM K hcut
  have hpay := congrArg Prod.fst hpair
  have hbest := congrArg Prod.snd hpair
  change quittingTerminalPayoff reward _ =
    quittingTerminalPayoff reward (certificate.rationalFiniteProfile mesh K) at hpay
  change quittingContinuationBestResponseValue reward _ =
    quittingContinuationBestResponseValue reward
      (certificate.rationalFiniteProfile mesh K) at hbest
  refine ⟨deadline, mixed, hdeadline, ?_, ?_⟩
  · intro who hdeleted
    apply finiteTiming_pure_none_of_law_none
    rw [hlaws who]
    have hquiet : certificate.rationalFiniteProfile mesh K who =
        quittingPureTimeBehaviorStrategy reward who none := by
      funext time history
      exact certificate.rationalFiniteProfile_outside_continue mesh K who
        (fun phase heq => howners phase (heq ▸ hdeleted)) time history
    change quittingBehaviorStoppingLaw reward
      (certificate.rationalFiniteProfile mesh K who) = PMF.pure none
    rw [hquiet, quittingBehaviorStoppingLaw_pureTime_never]
  · intro who deviation
    have hreply := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (quittingFiniteDeadlineTimingProfile reward deadline mixed) who deviation
    rw [hbest] at hreply
    rw [hpay]
    apply hreply.trans
    unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, certificate.rationalFiniteProfile mesh K who, rfl⟩
    · rintro value ⟨response, rfl⟩
      exact (hsource.1 who response).trans (add_le_add_right hηaccuracy _)

/-- Weak inverse data produce actual original-table finite timing laws at every
terminal accuracy, retaining Never on every deleted coordinate. -/
theorem exists_quiet_finiteTiming_terminalNash_of_nonnegativeInverse_passiveRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (hcard : Fintype.card {who : ι // ¬ deleted who} = 3)
    (hdet : Matrix.det
      (Matrix.of (normalizedSoloMatrix (quittingDeleteReward reward deleted))) ≠ 0)
    (hinverse : ∀ row column : {who : ι // ¬ deleted who},
      0 ≤ (Matrix.of
        (normalizedSoloMatrix (quittingDeleteReward reward deleted)))⁻¹ row column)
    (rows : PassiveSingletonRowFactorization reward deleted)
    (accuracy : ℝ) (haccuracy : 0 < accuracy) :
    ∃ (deadline : ℕ) (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)),
      0 < deadline ∧
      (∀ who, deleted who → mixed who = PMF.pure none) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) := by
  obtain ⟨epsilon, _, hclose, certificate, howners⟩ :=
    exists_strictPerturb_balancedCertificate_of_nonnegativeInverse_passiveRows
      reward deleted hcard hdet hinverse rows (accuracy / 4) (by linarith)
  obtain ⟨deadline, mixed, hdeadline, hquiet, hnash⟩ :=
    certificate.exists_quiet_finiteTiming_terminalNash deleted howners
      (accuracy / 2) (by linarith)
  have hstable := IsεAsymptoticNash.of_reward_close
    (rows.perturb epsilon) reward
      (quittingFiniteDeadlineTimingProfile (rows.perturb epsilon) deadline mixed)
      (by linarith : 0 ≤ accuracy / 4) hclose hnash
  refine ⟨deadline, mixed, hdeadline, hquiet, ?_⟩
  exact hstable.mono (by ring_nf; exact le_rfl)

/-- One fixed original-game target with actual finite date-or-Never witnesses.
Terminal regret and delivery are bounded before applying the literal signed
horizon cutoff. No uniform calendar-size bound over a weak family is asserted. -/
def QuietFiniteTimingUniformWitnesses
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) (target : Payoff ι) : Prop :=
  ∀ accuracy : ℝ, 0 < accuracy →
    ∃ (deadline : ℕ) (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)),
      0 < deadline ∧
      (∀ who, deleted who → mixed who = PMF.pure none) ∧
      (∀ who, deleted who →
        quittingFiniteDeadlineTimingProfile reward deadline mixed who =
          quittingAlwaysContinueStrategy reward who) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
        (accuracy / 2) (quittingFiniteDeadlineTimingProfile reward deadline mixed) ∧
      (∀ who, |quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who - target who| ≤
        accuracy / 2) ∧
      ∀ M : ℝ, (∀ terminal who, |reward terminal who| ≤ M) →
        ∀ horizon : ℕ,
          max 1 (Nat.ceil (4 * M * (deadline + 1) / accuracy)) ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon accuracy
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who - target who| ≤
              accuracy

/-- The retained finite laws directly witness uniform equilibrium at the same
fixed target; the supplied cutoff is used without another selection. -/
theorem QuietFiniteTimingUniformWitnesses.isUniformEquilibriumPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {deleted : ι → Prop} {target : Payoff ι}
    (witnesses : QuietFiniteTimingUniformWitnesses reward deleted target) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  intro accuracy haccuracy
  obtain ⟨deadline, mixed, _, _, _, _, _, hhorizon⟩ := witnesses accuracy haccuracy
  have hreward : ∀ terminal who,
      |reward terminal who| ≤ quittingRewardBound reward + 1 := by
    intro terminal who
    linarith [abs_reward_le_quittingRewardBound reward terminal who]
  exact ⟨quittingFiniteDeadlineTimingProfile reward deadline mixed,
    max 1 (Nat.ceil
      (4 * (quittingRewardBound reward + 1) * (deadline + 1) / accuracy)),
    hhorizon (quittingRewardBound reward + 1) hreward⟩

/-- Broad weak inverse hypotheses select one fixed original-game target before
accuracy, retaining actual finite timing laws, terminal bounds and quiet outsiders. -/
theorem exists_quietFiniteTimingUniformWitnesses_of_nonnegativeInverse_passiveRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (hcard : Fintype.card {who : ι // ¬ deleted who} = 3)
    (hdet : Matrix.det
      (Matrix.of (normalizedSoloMatrix (quittingDeleteReward reward deleted))) ≠ 0)
    (hinverse : ∀ row column : {who : ι // ¬ deleted who},
      0 ≤ (Matrix.of
        (normalizedSoloMatrix (quittingDeleteReward reward deleted)))⁻¹ row column)
    (rows : PassiveSingletonRowFactorization reward deleted) :
    ∃ target : Payoff ι,
      target ∈ Set.Icc (fun _ => -quittingRewardBound reward)
        (fun _ => quittingRewardBound reward) ∧
      QuietFiniteTimingUniformWitnesses reward deleted target := by
  let error : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have herrorPositive : ∀ n, 0 < error n := by
    intro n
    dsimp [error]
    positivity
  have hexists := fun n =>
    exists_quiet_finiteTiming_terminalNash_of_nonnegativeInverse_passiveRows
      reward deleted hcard hdet hinverse rows (error n) (herrorPositive n)
  choose deadlines mixed hdeadlines hquiet hnash using hexists
  let profiles := fun n => quittingFiniteDeadlineTimingProfile reward (deadlines n) (mixed n)
  have hlimit : Tendsto error atTop (nhds 0) := by
    simpa [error] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨target, hmem, haccept⟩ :=
    quittingGame_exists_terminalTargetAcceptance_of_terminalNash_family
      reward error profiles hlimit hnash
  refine ⟨target, hmem, ?_⟩
  intro accuracy haccuracy
  obtain ⟨selected, hselectedNash, hselectedTarget⟩ :=
    haccept (accuracy / 2) (by linarith)
  refine ⟨deadlines selected, mixed selected, hdeadlines selected, hquiet selected,
    ?_, hselectedNash, hselectedTarget, ?_⟩
  · intro who hdeleted
    exact quittingFiniteDeadlineTimingProfile_eq_alwaysContinue_of_pure_none
      reward (deadlines selected) (mixed selected) who (hquiet selected who hdeleted)
  · intro M hreward
    exact finiteDeadlineTiming_uniformPayoffWitness_of_terminal_bounds
      reward target (deadlines selected) (mixed selected)
        haccuracy hselectedNash hselectedTarget hreward

namespace PassiveRowInverseCriterion

/-- The literal raw nonnegative inverse and outside-row tests retain finite
quiet witnesses in the original game, with a fixed target before accuracy. -/
theorem exists_quietFiniteTimingUniformWitnesses_of_raw_nonnegativeInverse_triple
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (hcard : Fintype.card {who : ι // ¬ deleted who} = 3)
    (hdet : (childMatrix reward deleted).det ≠ 0)
    (hinverse : ∀ row column : {who : ι // ¬ deleted who},
      0 ≤ (childMatrix reward deleted)⁻¹ row column)
    (houtside : ∀ outside, deleted outside →
      ∀ inside : {who : ι // ¬ deleted who},
        0 ≤ inverseWeight reward deleted outside inside) :
    ∃ target : Payoff ι,
      target ∈ Set.Icc (fun _ => -quittingRewardBound reward)
        (fun _ => quittingRewardBound reward) ∧
      QuietFiniteTimingUniformWitnesses reward deleted target := by
  exact exists_quietFiniteTimingUniformWitnesses_of_nonnegativeInverse_passiveRows
    reward deleted hcard hdet hinverse (factorization reward deleted hdet houtside)

end PassiveRowInverseCriterion

end GameTheory
