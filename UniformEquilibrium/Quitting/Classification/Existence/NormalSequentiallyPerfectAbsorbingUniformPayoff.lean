/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Classification.AbnormalPlayers
import UniformEquilibrium.Quitting.Classification.Existence.WellSupportedAbsorbingSequence
import UniformEquilibrium.Quitting.Paths.QuitEndpointOpponentBound
import UniformEquilibrium.Quitting.Paths.SupportWitnessAbsorptionBridge

/-!
# Normal sequentially perfect absorbing sources yield uniform payoffs

A supplied sequentially row-perfect completely absorbing root sequence, or its
checked equivalent well-supported formulation, is compiled into terminal
approximate Nash profiles under all-player punishment normality. The compiler
uses a bounded delayed scan after the first support-survival crossing. It does
not produce the source sequence or prove a stationary equilibrium.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- At a normal player's row, being below the punishment floor by `r0`
forces a uniform amount of opponent absorption. -/
theorem opponentAbsorptionMass_gt_of_normal_of_rowPerfect_of_not_individualRational
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ)
    {M r0 η : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hη : η ≤ r0 / 2)
    (hnormal : IsQuittingNormalPlayer reward who)
    (hperfect : QuittingPlayerRowεPerfect reward
      (quittingRootSequenceTailVector reward roots (time + 1))
      (roots time) who η)
    (hbad : quittingRootSequenceTerminalValue reward roots who time <
      quittingPunishmentValue reward who - r0) :
    r0 / (2 * max 1 (2 * M)) <
      quittingRootOpponentAbsorptionMass (roots time) who := by
  have hB : 0 < max 1 (2 * M) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hB2M : 2 * M ≤ max 1 (2 * M) := le_max_right _ _
  have hopp0 : 0 ≤ quittingRootOpponentAbsorptionMass (roots time) who :=
    quittingRootOpponentAbsorptionMass_nonneg _ _
  have hquit := hperfect.1
  rw [← quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector]
    at hquit
  have hnormal' : quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who := by
    simpa only [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
      quittingSingletonTerminal] using hnormal
  have hgap : r0 / 2 <
      reward (quittingSingletonTerminal who) who -
        quittingRootQuitPayoff reward
          (quittingRootSequenceTailVector reward roots (time + 1))
          (roots time) who := by
    linarith
  have habs :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (quittingRootSequenceTailVector reward roots (time + 1))
        (roots time) who M hreward
  have hgapAbs : r0 / 2 <
      |quittingRootQuitPayoff reward
          (quittingRootSequenceTailVector reward roots (time + 1))
          (roots time) who - reward (quittingSingletonTerminal who) who| := by
    have hneg := neg_le_abs
      (quittingRootQuitPayoff reward
        (quittingRootSequenceTailVector reward roots (time + 1))
        (roots time) who - reward (quittingSingletonTerminal who) who)
    linarith
  have hscaled : r0 / 2 <
      max 1 (2 * M) * quittingRootOpponentAbsorptionMass (roots time) who := by
    calc
      r0 / 2 < 2 * M * quittingRootOpponentAbsorptionMass (roots time) who :=
        hgapAbs.trans_le habs
      _ ≤ max 1 (2 * M) *
          quittingRootOpponentAbsorptionMass (roots time) who :=
        mul_le_mul_of_nonneg_right hB2M hopp0
  apply (div_lt_iff₀ (show 0 < 2 * max 1 (2 * M) by positivity)).2
  nlinarith

omit [Nonempty ι] in
/-- A support-local sequence accumulates at most one `δ` of ledger charge per
additional row. -/
theorem quittingLedger_add_le_of_supportApproxNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward roots δ) :
    quittingLedger reward roots who (start + fuel) ≤
      quittingLedger reward roots who start + fuel * δ := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [Nat.add_succ, quittingLedger_succ]
      have hstage := quittingLedgerStageAdvantage_le_delta_mul_ownQuitProbability
        reward roots who (start + fuel) (hsupport (start + fuel))
      have hquit : ((roots (start + fuel) who) true).toReal ≤ 1 :=
        ENNReal.toReal_mono ENNReal.one_ne_top
          (PMF.coe_le_one (roots (start + fuel) who) true)
      have hcharge : quittingLedgerStageAdvantage reward roots who (start + fuel) ≤ δ :=
        hstage.trans (mul_le_of_le_one_right hδ hquit)
      push_cast
      linarith

omit [Nonempty ι] in
/-- Uniform opponent absorption on a finite block gives the expected
geometric bound on deleted survival. -/
theorem quittingOpponentSurvivalWeight_le_pow_of_absorption_gt
    (roots : ℕ → ι → PMF Bool) (who : ι) (start length : ℕ)
    {c : ℝ}
    (habsorption : ∀ offset < length,
      c < quittingRootOpponentAbsorptionMass (roots (start + offset)) who) :
    quittingOpponentSurvivalWeight roots who start length ≤ (1 - c) ^ length := by
  unfold quittingOpponentSurvivalWeight
  have hfactor : ∀ offset ∈ Finset.range length,
      quittingFixedOpponentsContinueMass roots who (start + offset) ≤ 1 - c := by
    intro offset hoffset
    have hmass := habsorption offset (Finset.mem_range.mp hoffset)
    change quittingRootOpponentContinueMass (roots (start + offset)) who ≤ 1 - c
    rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass]
    linarith
  calc
    (∏ offset ∈ Finset.range length,
        quittingFixedOpponentsContinueMass roots who (start + offset)) ≤
        ∏ _offset ∈ Finset.range length, (1 - c) := by
      apply Finset.prod_le_prod
      · intro offset hoffset
        exact quittingStationaryContinueMass_nonneg
          (Function.update (roots (start + offset)) who (PMF.pure false))
      · exact hfactor
    _ = (1 - c) ^ length := by simp

/-- The finite delayed switch selected after the first support-survival
crossing.  Its final branch either reaches the selected player's punishment
floor or clears every player's deleted-survival clock. -/
structure NormalSupportDelayedSwitch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (δ ledgerCap threshold r0 : ℝ) (length : ℕ) where
  target : ι
  initial : ℕ
  switch : ℕ
  initial_eq : initial = quittingSupportSurvivalSwitchIndex roots threshold
  initial_le_switch : initial ≤ switch
  switch_le : switch ≤ initial + length
  ledger_le : ∀ who index, index ≤ switch →
    quittingLedger reward roots who index ≤ ledgerCap + (length + 1) * δ
  quitRegret_le : ∀ who stage, stage < switch →
    quittingLedgerQuitRegret reward roots who stage ≤ δ
  targetJointReach_le : quittingJointSurvivalWeight roots 0 switch ≤ threshold
  otherReach_le : ∀ who, who ≠ target →
    quittingOpponentSurvivalWeight roots who 0 switch ≤ threshold
  branch :
    quittingPunishmentValue reward target ≤
        quittingRootSequenceTerminalValue reward roots target switch + r0 ∨
      ∀ who, quittingOpponentSurvivalWeight roots who 0 switch ≤ threshold

/-- Complete absorption and normality select a bounded delayed switch with
the two exact branches consumed by the phase-switch theorems. -/
theorem exists_normalSupportDelayedSwitch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    {η δ ledgerCap threshold r0 M : ℝ} {length : ℕ}
    (hδ : 0 ≤ δ) (hledgerCap : 0 < ledgerCap)
    (hthreshold : 0 < threshold)
    (hscale : δ ≤ ledgerCap * threshold)
    (hη : η ≤ r0 / 2)
    (hpower : (1 - r0 / (2 * max 1 (2 * M))) ^ length ≤ threshold)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward roots δ)
    (hperfect : ∀ time, QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward roots (time + 1))
      (roots time) η)
    (habsorbing : IsCompletelyAbsorbing roots)
    (hnormal : ∀ who, IsQuittingNormalPlayer reward who) :
    Nonempty (NormalSupportDelayedSwitch reward roots δ ledgerCap threshold r0 length) := by
  have hexists : ∃ cutoff, ∃ who,
      quittingHazardSurvival (quittingRootSequenceOwnHazard roots who) cutoff ≤
        threshold :=
    exists_ownSurvival_crossing_of_completelyAbsorbing
      roots hthreshold habsorbing
  let initial := quittingSupportSurvivalSwitchIndex roots threshold
  obtain ⟨hledgerInitial, _hregretInitial, target, hjointInitial, hotherInitial⟩ :=
    quittingSupportApproxNash_survivalSwitchPackage
      reward roots hδ hledgerCap hthreshold hscale hsupport hexists
  have hregret : ∀ who stage, quittingLedgerQuitRegret reward roots who stage ≤ δ :=
    fun who stage => quittingLedgerQuitRegret_le_of_supportApproxNash
      reward roots who stage hδ hsupport
  have hledgerExtended : ∀ (cutoff : ℕ), cutoff ≤ initial + length →
      ∀ who index, index ≤ cutoff →
        quittingLedger reward roots who index ≤ ledgerCap + (length + 1) * δ := by
    intro cutoff hcutoff who index hindex
    by_cases hindexInitial : index ≤ initial
    · have hbase := hledgerInitial who index (by simpa [initial] using hindexInitial)
      have hlength0 : (0 : ℝ) ≤ length := by positivity
      nlinarith
    · have hinitialIndex : initial ≤ index := Nat.le_of_lt (Nat.lt_of_not_ge hindexInitial)
      obtain ⟨fuel, rfl⟩ := Nat.exists_eq_add_of_le hinitialIndex
      have hfuel : fuel ≤ length := by omega
      have hadd := quittingLedger_add_le_of_supportApproxNash
        reward roots who initial fuel hδ hsupport
      have hbase := hledgerInitial who initial (by simp [initial])
      have hcast : (fuel : ℝ) ≤ length := by exact_mod_cast hfuel
      nlinarith
  have hjointExtended : ∀ cutoff, initial ≤ cutoff →
      quittingJointSurvivalWeight roots 0 cutoff ≤ threshold := by
    intro cutoff hcutoff
    exact (antitone_quittingJointSurvivalWeight roots 0 hcutoff).trans
      (by simpa [initial] using hjointInitial)
  have hotherExtended : ∀ cutoff, initial ≤ cutoff → ∀ who, who ≠ target →
      quittingOpponentSurvivalWeight roots who 0 cutoff ≤ threshold := by
    intro cutoff hcutoff who hwho
    exact (antitone_quittingOpponentSurvivalWeight roots who 0 hcutoff).trans
      (by simpa [initial] using hotherInitial who hwho)
  by_cases hgood : ∃ offset, offset < length ∧
      quittingPunishmentValue reward target ≤
        quittingRootSequenceTerminalValue reward roots target (initial + offset) + r0
  · obtain ⟨offset, hoffset, hgood⟩ := hgood
    refine ⟨{
      target := target
      initial := initial
      switch := initial + offset
      initial_eq := rfl
      initial_le_switch := Nat.le_add_right _ _
      switch_le := by omega
      ledger_le := hledgerExtended (initial + offset) (by omega)
      quitRegret_le := fun who stage _ => hregret who stage
      targetJointReach_le := hjointExtended _ (Nat.le_add_right _ _)
      otherReach_le := hotherExtended _ (Nat.le_add_right _ _)
      branch := Or.inl hgood }⟩
  · have hallBad : ∀ offset < length,
        quittingRootSequenceTerminalValue reward roots target (initial + offset) <
          quittingPunishmentValue reward target - r0 := by
      intro offset hoffset
      have hnot := hgood
      simp only [not_exists, not_and, not_le] at hnot
      exact lt_sub_iff_add_lt.mpr (hnot offset hoffset)
    have habsorption : ∀ offset < length,
        r0 / (2 * max 1 (2 * M)) <
          quittingRootOpponentAbsorptionMass (roots (initial + offset)) target := by
      intro offset hoffset
      exact opponentAbsorptionMass_gt_of_normal_of_rowPerfect_of_not_individualRational
        reward roots target (initial + offset) hreward hη
          (hnormal target) (hperfect (initial + offset) target)
          (hallBad offset hoffset)
    have hsuffix : quittingOpponentSurvivalWeight roots target initial length ≤
        threshold :=
      (quittingOpponentSurvivalWeight_le_pow_of_absorption_gt
        roots target initial length habsorption).trans hpower
    have htargetReach : quittingOpponentSurvivalWeight roots target 0
        (initial + length) ≤ threshold := by
      rw [quittingOpponentSurvivalWeight_add]
      have hprefix0 := quittingOpponentSurvivalWeight_nonneg roots target 0 initial
      have hprefix1 := quittingOpponentSurvivalWeight_le_one roots target 0 initial
      have hsuffix0 := quittingOpponentSurvivalWeight_nonneg roots target initial length
      have hsuffix' : quittingOpponentSurvivalWeight roots target (0 + initial) length ≤
          threshold := by simpa using hsuffix
      have hsuffix0' : 0 ≤
          quittingOpponentSurvivalWeight roots target (0 + initial) length := by
        simpa using hsuffix0
      nlinarith
    refine ⟨{
      target := target
      initial := initial
      switch := initial + length
      initial_eq := rfl
      initial_le_switch := Nat.le_add_right _ _
      switch_le := le_rfl
      ledger_le := hledgerExtended (initial + length) le_rfl
      quitRegret_le := fun who stage _ => hregret who stage
      targetJointReach_le := hjointExtended _ (Nat.le_add_right _ _)
      otherReach_le := hotherExtended _ (Nat.le_add_right _ _)
      branch := Or.inr (fun who => by
        by_cases hwho : who = target
        · simpa [hwho] using htargetReach
        · exact hotherExtended _ (Nat.le_add_right _ _) who hwho) }⟩

omit [Nonempty ι] in
/-- A normal delayed switch produces a terminal approximate equilibrium.
The good branch constructs a target-closed tail and extends it to one
same-tail cap for every player; the all-bad branch uses the explicit
all-Continue tail. -/
theorem exists_isεAsymptoticNash_of_normalSupportDelayedSwitch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    {δ ledgerCap threshold r0 ζ M ε : ℝ} {length : ℕ}
    (hswitch : NormalSupportDelayedSwitch
      reward roots δ ledgerCap threshold r0 length)
    (hδ : 0 ≤ δ) (hthreshold : 0 ≤ threshold)
    (hr0 : 0 ≤ r0) (hζ : 0 < ζ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (herror : ledgerCap + (length + 2) * δ + r0 + ζ +
      threshold * (7 * M) ≤ ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile := by
  have hM : 0 ≤ M :=
    (abs_nonneg (reward (quittingSingletonTerminal hswitch.target) hswitch.target)).trans
      (hreward (quittingSingletonTerminal hswitch.target) hswitch.target)
  rcases hswitch.branch with hgood | hallBad
  · obtain ⟨tail, hclosed, htailValue⟩ :=
      exists_quittingTargetClosedTail_le_of_punishmentValue_le
        reward hswitch.target
          (quittingRootSequenceTerminalValue reward roots hswitch.target
            hswitch.switch + r0)
          hζ hgood
    obtain ⟨punishCap, hcapTarget, hpunish, hcapBound⟩ :=
      exists_quittingPhaseSwitchPunishCap_of_targetClosedTail_of_coordinateBound
        reward tail hswitch.target hreward hclosed
    have hcontinuation : punishCap hswitch.target + 0 ≤
        quittingRootSequenceTerminalValue reward roots hswitch.target
          hswitch.switch + (r0 + ζ) := by
      rw [hcapTarget]
      linarith
    have htargetError :
        (ledgerCap + (length + 1) * δ) + δ + (r0 + ζ) +
          threshold * (2 * M) ≤ ε := by
      have hnonneg : 0 ≤ threshold * (5 * M) := by positivity
      nlinarith
    have hotherError : ∀ who, who ≠ hswitch.target →
        (ledgerCap + (length + 1) * δ) + δ +
            threshold * (5 * M) +
          threshold * (max (punishCap who + 0) 0 + M) ≤ ε := by
      intro who _
      have hcapMax : max (punishCap who) 0 ≤ M :=
        max_le (hcapBound who) hM
      have htail : max (punishCap who + 0) 0 + M ≤ 2 * M := by
        simpa only [add_zero, two_mul] using add_le_add hcapMax (le_refl M)
      have hscaled := mul_le_mul_of_nonneg_left htail hthreshold
      nlinarith
    refine ⟨quittingPhaseSwitchProfile reward roots tail hswitch.switch, ?_⟩
    exact isεAsymptoticNash_quittingPhaseSwitchProfile_marked
      (reward := reward) (plan := roots) (punish := tail)
      (switch := hswitch.switch) (target := hswitch.target)
      (ledgerCap := ledgerCap + (length + 1) * δ)
      (quitRegretCap := δ) (continuationSlack := r0 + ζ)
      (targetJointReach := threshold) (otherReach := threshold)
      (punishError := 0) (bound := M) (punishCap := punishCap)
      hM hδ (by positivity) hreward hswitch.ledger_le hswitch.quitRegret_le
      (fun who hazard => by simpa using hpunish who hazard)
      hcontinuation hswitch.targetJointReach_le hswitch.otherReach_le
      htargetError hotherError
  · let punish : ℕ → ι → PMF Bool := fun _ => quittingAllContinueRoot
    let punishCap : ι → ℝ := fun _ => M
    let planError := ledgerCap + (length + 2) * δ + threshold * (5 * M)
    have hplan : ∀ who (g : ℕ → PMF Bool),
        quittingRootSequenceHazardTerminalValue reward
            (quittingTruncatedRoots roots hswitch.switch) who g 0 ≤
          quittingRootSequenceTerminalValue reward
              (quittingTruncatedRoots roots hswitch.switch) who 0 + planError := by
      intro who g
      have hcap :=
        quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le
          reward roots who hswitch.switch hM hδ hreward
          (hswitch.ledger_le who) (hswitch.quitRegret_le who) (hallBad who) g
      change _ ≤ _ + (ledgerCap + (length + 2) * δ + threshold * (5 * M))
      convert hcap using 1
      ring
    have hpunish : ∀ who (g : ℕ → PMF Bool),
        quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
          punishCap who + 0 := by
      intro who g
      have hmax :=
        quittingRootSequenceHazardTerminalValue_quittingAllContinueRoots_le_max
          reward who g
      have hsolo := hreward (quittingSingletonTerminal who) who
      have hsoloLe : reward (quittingSingletonTerminal who) who ≤ M :=
        (le_abs_self _).trans hsolo
      have hmaxLe : max 0 (reward (quittingSingletonTerminal who) who) ≤ M :=
        max_le hM hsoloLe
      change quittingRootSequenceHazardTerminalValue reward
          (fun _ => quittingAllContinueRoot) who g 0 ≤ M + 0
      linarith
    have hfinalError : ∀ who,
        planError + threshold * (max (punishCap who + 0) 0 + M) ≤ ε := by
      intro who
      have hmax : max (punishCap who + 0) 0 = M := by simp [punishCap, hM]
      simp only [hmax]
      dsimp only [planError]
      nlinarith
    refine ⟨quittingPhaseSwitchProfile reward roots punish hswitch.switch, ?_⟩
    exact isεAsymptoticNash_quittingPhaseSwitchProfile
      (reward := reward) (plan := roots) (punish := punish)
      (switch := hswitch.switch) (planError := planError)
      (punishError := 0) (survivalCap := threshold) (bound := M)
      (punishCap := punishCap) hM hreward hplan hpunish hallBad hfinalError

/-- Playerwise normality and branch S.3 produce terminal approximate Nash
profiles at every requested positive error. -/
theorem exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnormal : ∀ who, IsQuittingNormalPlayer reward who)
    (hS3 : QuittingSequentiallyεPerfectAbsorbingExistence reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile := by
  let M := quittingRewardBound reward
  let B := max 1 (2 * M)
  let d := min (1 / 4 : ℝ) (ε / (8 * (3 + 7 * M)))
  have hM : 0 ≤ M := by exact quittingRewardBound_nonneg reward
  have hB : 0 < B := by
    exact lt_of_lt_of_le zero_lt_one (by simp [B])
  have hcoefficient : 0 < 3 + 7 * M := by positivity
  have hd0 : 0 < d := by simp only [d]; positivity
  have hdQuarter : d ≤ 1 / 4 := min_le_left _ _
  have hdError : d ≤ ε / (8 * (3 + 7 * M)) := min_le_right _ _
  have hd1 : d < 1 := lt_of_le_of_lt hdQuarter (by norm_num)
  have hdB : d < B := hd1.trans_le (by simp [B])
  let c := d / (2 * B)
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := by
    apply (div_lt_iff₀ (show 0 < 2 * B by positivity)).2
    nlinarith
  have hbase0 : 0 ≤ 1 - c := by linarith
  have hbase1 : 1 - c < 1 := by linarith
  have hpowTendsto : Tendsto (fun length : ℕ => (1 - c) ^ length)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
  have heventually : ∀ᶠ length : ℕ in atTop, (1 - c) ^ length < d :=
    (tendsto_order.1 hpowTendsto).2 d hd0
  obtain ⟨length, hlength⟩ := heventually.exists
  let A : ℝ := length + 2
  have hA : 0 < A := by dsimp only [A]; positivity
  let η := min (d / 4) (min (d * d / 4) (ε / (16 * A)))
  have hη0 : 0 < η := by simp only [η]; positivity
  have hηd : η ≤ d / 4 := min_le_left _ _
  have hηdd : η ≤ d * d / 4 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hηError : η ≤ ε / (16 * A) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hηHalf : η ≤ d / 2 := by linarith
  have hscale : 2 * η ≤ d * d := by nlinarith
  have hdynamic : A * (2 * η) ≤ ε / 8 := by
    have hscaled := mul_le_mul_of_nonneg_left hηError hA.le
    have hden : 0 < 16 * A := by positivity
    have hcancel : A * (ε / (16 * A)) = ε / 16 := by
      field_simp
    rw [hcancel] at hscaled
    nlinarith
  have hbaseError : d * (3 + 7 * M) ≤ ε / 8 := by
    have hscaled := mul_le_mul_of_nonneg_right hdError hcoefficient.le
    have hcancel : (ε / (8 * (3 + 7 * M))) * (3 + 7 * M) = ε / 8 := by
      field_simp
    rw [hcancel] at hscaled
    exact hscaled
  obtain ⟨roots, habsorbing, hperfect⟩ := hS3 η hη0
  have hsupport : IsQuittingRootSequenceSupportApproxNash reward roots (2 * η) :=
    fun time => supportApproxNash_of_quittingRowεPerfect (hperfect time)
  obtain ⟨hswitch⟩ := exists_normalSupportDelayedSwitch
    (reward := reward) (roots := roots)
    (hδ := mul_nonneg (by norm_num) hη0.le)
    (hledgerCap := hd0) (hthreshold := hd0)
    (hscale := hscale) (hη := hηHalf)
    (hpower := by simpa [c, B] using hlength.le)
    (hreward := abs_reward_le_quittingRewardBound reward)
    (hsupport := hsupport) (hperfect := hperfect)
    (habsorbing := habsorbing) (hnormal := hnormal)
  have herror : d + (length + 2) * (2 * η) + d + d +
      d * (7 * M) ≤ ε := by
    have hdynamic' : ((length : ℝ) + 2) * (2 * η) ≤ ε / 8 := by
      simpa [A] using hdynamic
    nlinarith
  exact exists_isεAsymptoticNash_of_normalSupportDelayedSwitch
    (reward := reward) (roots := roots) (hswitch := hswitch)
    (hδ := mul_nonneg (by norm_num) hη0.le) (hthreshold := hd0.le)
    (hr0 := hd0.le) (hζ := hd0)
    (hreward := abs_reward_le_quittingRewardBound reward)
    (herror := by simpa [M] using herror)

/-- The support-local formulation of the completely absorbing branch yields
terminal approximate Nash profiles at every positive error under all-player
punishment normality. -/
theorem exists_terminalNash_of_all_normal_of_wellSupportedAbsorbing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnormal : ∀ who, IsQuittingNormalPlayer reward who)
    (hwellSupported : QuittingWellSupportedAbsorbingSequenceExistence reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile :=
  exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing
    reward hnormal
      (quittingSequentiallyεPerfectAbsorbingExistence_of_wellSupported hwellSupported) hε

/-- The direct normal-S.3 compiler: all-player punishment normality and a
literal sequentially perfect completely absorbing source yield one fixed
uniform-equilibrium payoff against unrestricted behavioral deviations. -/
theorem exists_uniformEquilibriumPayoff_of_all_normal_of_sequentiallyPerfectAbsorbing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnormal : ∀ who, IsQuittingNormalPlayer reward who)
    (hS3 : QuittingSequentiallyεPerfectAbsorbingExistence reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
    reward fun _ hε =>
      exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing
        reward hnormal hS3 hε

/-- The equivalent well-supported completely absorbing source formulation
also yields one fixed uniform-equilibrium payoff under all-player normality. -/
theorem exists_uniformEquilibriumPayoff_of_all_normal_of_wellSupportedAbsorbing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnormal : ∀ who, IsQuittingNormalPlayer reward who)
    (hwellSupported : QuittingWellSupportedAbsorbingSequenceExistence reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_all_normal_of_sequentiallyPerfectAbsorbing
    reward hnormal
      (quittingSequentiallyεPerfectAbsorbingExistence_of_wellSupported hwellSupported)

end GameTheory

