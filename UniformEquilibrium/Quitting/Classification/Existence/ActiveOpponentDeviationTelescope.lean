/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.QuietWindowStationaryRepair
import UniformEquilibrium.Quitting.Cycles.InfinitePureTimeExtremality
import UniformEquilibrium.Quitting.RewardBound

/-!
# The active-opponent deviation telescope

Case 2 of the block analysis of Solan and Vieille, *Quitting games*, Math.
Oper. Res. 26 (2001), Section 2.5.4, in this development's root-sequence
vocabulary, with the source's block decomposition replaced by a supremum
argument over the deviation-gap sequence.

Call a root sequence **`ρ`-active for a player** when, from every stage and
over every horizon, the plan's survival plus its survival-weighted opponent
absorption is at least `ρ`.  Along the deviation ledger, the gap between a
pure-time deviation's value and the plan's value accrues, at each stage, the
deviator's own quit weight times an edge which one-stage perfectness bounds
by `2 εr` plus the opponent continue mass times the next gap.  Summing with
survival weights, the coefficient collected by the supremum of the gaps is
exactly one minus the plan's survival minus its survival-weighted opponent
absorption — at most `1 - ρ` under activity — while the row tolerances total
at most `2 εr` because own quit weights are dominated by absorption, which
telescopes.  The supremum therefore solves to at most `3 εr / ρ`.

Together with infinite pure-time extremality this bounds every hazard
deviation, so a sequence that is `ρ`-active for every player is a global
`3 εr / ρ` root-sequence equilibrium.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Survival-weight bookkeeping -/

omit [DecidableEq ι] in
/-- Appending one stage to a joint survival weight. -/
theorem quittingJointSurvivalWeight_succ_right
    (roots : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    quittingJointSurvivalWeight roots start (fuel + 1) =
      quittingJointSurvivalWeight roots start fuel *
        quittingStationaryContinueMass (roots (start + fuel)) := by
  rw [quittingJointSurvivalWeight_eq_prod,
    quittingJointSurvivalWeight_eq_prod, Finset.prod_range_succ]

omit [DecidableEq ι] in
/-- Survival-weighted absorption telescopes to the lost survival. -/
theorem sum_jointSurvivalWeight_mul_absorptionMass
    (roots : ℕ → ι → PMF Bool) (start : ℕ) :
    ∀ fuel, (∑ offset ∈ Finset.range fuel,
      quittingJointSurvivalWeight roots start offset *
        quittingRootAbsorptionMass (roots (start + offset))) =
      1 - quittingJointSurvivalWeight roots start fuel := by
  intro fuel
  induction fuel with
  | zero =>
      simp
  | succ fuel ih =>
      rw [Finset.sum_range_succ, ih,
        quittingJointSurvivalWeight_succ_right]
      unfold quittingRootAbsorptionMass
      ring

omit [DecidableEq ι] in
/-- Under a per-stage absorption floor, joint survival decays
geometrically. -/
theorem quittingJointSurvivalWeight_le_pow
    (roots : ℕ → ι → PMF Bool) {δ : ℝ} (hδ1 : δ ≤ 1)
    (hfloor : ∀ n, δ ≤ quittingRootAbsorptionMass (roots n)) (start : ℕ) :
    ∀ fuel, quittingJointSurvivalWeight roots start fuel ≤ (1 - δ) ^ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      simp
  | succ fuel ih =>
      rw [quittingJointSurvivalWeight_succ_right, pow_succ]
      have hmass0 : 0 ≤ quittingStationaryContinueMass (roots (start + fuel)) :=
        quittingStationaryContinueMass_nonneg _
      have hmass : quittingStationaryContinueMass (roots (start + fuel)) ≤
          1 - δ := by
        have hstage := hfloor (start + fuel)
        unfold quittingRootAbsorptionMass at hstage
        linarith
      exact mul_le_mul ih hmass hmass0 (pow_nonneg (by linarith) fuel)

omit [DecidableEq ι] in
/-- One player's quit probability is dominated by the joint absorption
mass. -/
theorem quitProbability_le_absorptionMass (root : ι → PMF Bool) (who : ι) :
    (root who true).toReal ≤ quittingRootAbsorptionMass root := by
  have hcontinue :=
    quittingStationaryContinueMass_le_ownContinueProbability root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  unfold quittingRootAbsorptionMass
  linarith

/-- One player's quit weight times its opponents' continue mass is exactly
the joint absorption minus the opponent absorption. -/
theorem quitWeight_mul_opponentContinueMass_eq
    (root : ι → PMF Bool) (who : ι) :
    (root who true).toReal *
      quittingStationaryContinueMass
        (Function.update root who (PMF.pure false)) =
      quittingRootAbsorptionMass root -
        quittingRootOpponentAbsorptionMass root who := by
  have hfactor := quittingStationaryContinueMass_eq_forcedContinue_mul_own
    root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hopAbs : quittingRootOpponentAbsorptionMass root who =
      1 - quittingStationaryContinueMass
        (Function.update root who (PMF.pure false)) := rfl
  unfold quittingRootAbsorptionMass
  rw [hopAbs, hfactor]
  have hcontinue : (root who false).toReal =
      1 - (root who true).toReal := by linarith
  rw [hcontinue]
  ring

/-! ## The one-stage edge bound -/

/-- **The edge bound.**  At a stage away from the deviation's quit date, the
deviator's quit weight times the deviation's edge over quitting now is at
most that quit weight times `2 εr` plus the opponent continue mass times any
upper bound for the next stage's gap.  Perfectness clause 2 caps the
opponent-absorption drift; clause 3 caps the value of quitting now from
below whenever the quit weight is positive. -/
theorem quitWeight_mul_pureTimeEdge_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (roots : ℕ → ι → PMF Bool) (who : ι) (quitTime : Option ℕ) (time : ℕ)
    {εr bound : ℝ} (hne : quitTime ≠ some time)
    (hperfect : QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward roots (time + 1)) (roots time)
      εr)
    (hnext : quittingRootSequencePureTimeTerminalValue reward roots who
        quitTime (time + 1) -
      quittingRootSequenceTerminalValue reward roots who (time + 1) ≤
        bound) :
    (roots time who true).toReal *
      (quittingRootSequencePureTimeTerminalValue reward roots who quitTime
          time -
        quittingFixedOpponentsQuitValue reward roots who time) ≤
      (roots time who true).toReal *
        (2 * εr + quittingFixedOpponentsContinueMass roots who time * bound) := by
  by_cases hq : roots time who true = 0
  · simp [hq]
  · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    have hrecursion :=
      quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector reward
        roots who time
    have hquitLower : quittingRootSequenceTerminalValue reward roots who
        time - εr ≤ quittingFixedOpponentsQuitValue reward roots who time := by
      have hclause := (hperfect who).2.2.1 hq
      rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward roots who
        (quittingRootSequenceTailVector reward roots (time + 1)) time,
        ← hrecursion] at hclause
      linarith
    have hcontinueUpper : quittingFixedOpponentsContinueReward reward roots
        who time +
        quittingFixedOpponentsContinueMass roots who time *
          quittingRootSequenceTerminalValue reward roots who (time + 1) ≤
        quittingRootSequenceTerminalValue reward roots who time + εr := by
      have hclause := (hperfect who).2.1
      rw [quittingRootContinuePayoff_eq_fixedOpponents reward roots who
        (quittingRootSequenceTailVector reward roots (time + 1)) time,
        ← hrecursion] at hclause
      exact hclause
    have hstep := quittingRootSequencePureTimeTerminalValue_continue_step
      reward roots who quitTime time hne
    have hmass0 : 0 ≤ quittingFixedOpponentsContinueMass roots who time :=
      quittingStationaryContinueMass_nonneg _
    have hscaled := mul_le_mul_of_nonneg_left hnext hmass0
    rw [hstep]
    linarith

/-! ## The supremum telescope -/

/-- **The active telescope** (Solan and Vieille, *Quitting games*, Math.
Oper. Res. 26 (2001), Section 2.5.4).  Along a root sequence with a
per-stage absorption floor whose every row is one-stage `εr`-perfect against
the plan's own continuation, a player for whom the sequence is `ρ`-active
gains at most `3 εr / ρ` by any deterministic pure-time deviation. -/
theorem quittingRootSequencePureTimeTerminalValue_le_of_active
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {εr δ ρ : ℝ} (hεr : 0 ≤ εr) (hδ0 : 0 < δ) (hρ0 : 0 < ρ)
    (hfloor : ∀ n, δ ≤ quittingRootAbsorptionMass (roots n))
    (hperfect : ∀ n, QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward roots (n + 1)) (roots n) εr)
    (hactive : ∀ start fuel,
      ρ ≤ quittingJointSurvivalWeight roots start fuel +
        ∑ t ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots start t *
            quittingRootOpponentAbsorptionMass (roots (start + t)) who) :
    ∀ quitTime : Option ℕ,
      quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0 ≤
        quittingRootSequenceTerminalValue reward roots who 0 + 3 * εr / ρ := by
  have hδ1 : δ ≤ 1 := by
    have h0 := hfloor 0
    have h1 : quittingRootAbsorptionMass (roots 0) ≤ 1 := by
      unfold quittingRootAbsorptionMass
      linarith [quittingStationaryContinueMass_nonneg (roots 0)]
    linarith
  have hρ1 : ρ ≤ 1 := by
    have hstart := hactive 0 0
    simpa using hstart
  let M := quittingRewardBound reward
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hreward : ∀ terminal player, |reward terminal player| ≤ M :=
    abs_reward_le_quittingRewardBound reward
  intro quitTime
  -- the nonnegative gap sequence of this deviation and its supremum
  set gap : ℕ → ℝ := fun time =>
    max (quittingRootSequencePureTimeTerminalValue reward roots who quitTime
        time -
      quittingRootSequenceTerminalValue reward roots who time) 0 with hgapdef
  have hgapRaw : ∀ time,
      quittingRootSequencePureTimeTerminalValue reward roots who quitTime
          time -
        quittingRootSequenceTerminalValue reward roots who time ≤
        gap time := fun time => le_max_left _ _
  have hgap0 : ∀ time, 0 ≤ gap time := fun time => le_max_right _ _
  have hgapBound : ∀ time, gap time ≤ 2 * M := by
    intro time
    have hplan := abs_quittingRootSequenceTerminalValue_le reward roots who
      time hM hreward
    have hdev : |quittingRootSequencePureTimeTerminalValue reward roots who
        quitTime time| ≤ M := by
      unfold quittingRootSequencePureTimeTerminalValue
        quittingRootSequenceHazardTerminalValue
      exact abs_quittingRootSequenceTerminalValue_le reward _ who time hM
        hreward
    obtain ⟨hplan₁, hplan₂⟩ := abs_le.mp hplan
    obtain ⟨hdev₁, hdev₂⟩ := abs_le.mp hdev
    apply max_le _ (by linarith)
    linarith
  have hbdd : BddAbove (Set.range gap) := by
    refine ⟨2 * M, ?_⟩
    rintro value ⟨time, rfl⟩
    exact hgapBound time
  have hrange : (Set.range gap).Nonempty := ⟨gap 0, 0, rfl⟩
  set supGap := sSup (Set.range gap) with hsupdef
  have hsup0 : 0 ≤ supGap :=
    le_trans (hgap0 0) (le_csSup hbdd ⟨0, rfl⟩)
  have hsupAt : ∀ time, gap time ≤ supGap := fun time =>
    le_csSup hbdd ⟨time, rfl⟩
  -- the windowed estimate from any stage, any horizon avoiding the quit date
  have hestimate : ∀ tstar fuel,
      (∀ offset, offset < fuel → quitTime ≠ some (tstar + offset)) →
      quittingRootSequencePureTimeTerminalValue reward roots who quitTime
          tstar -
        quittingRootSequenceTerminalValue reward roots who tstar ≤
        2 * εr + supGap * (1 - ρ) +
          quittingJointSurvivalWeight roots tstar fuel *
            (quittingRootSequencePureTimeTerminalValue reward roots who
                quitTime (tstar + fuel) -
              quittingRootSequenceTerminalValue reward roots who
                (tstar + fuel)) := by
    intro tstar fuel hne
    have hunroll := quittingPureTimeDeviationLedger_window_sum reward roots
      who quitTime fuel tstar hne
    have htermwise : ∀ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight roots tstar offset *
          ((roots (tstar + offset) who true).toReal *
            (quittingRootSequencePureTimeTerminalValue reward roots who
                quitTime (tstar + offset) -
              quittingFixedOpponentsQuitValue reward roots who
                (tstar + offset))) ≤
        quittingJointSurvivalWeight roots tstar offset *
          ((roots (tstar + offset) who true).toReal *
            (2 * εr + quittingFixedOpponentsContinueMass roots who
              (tstar + offset) * supGap)) := by
      intro offset hoffset
      apply mul_le_mul_of_nonneg_left _
        (quittingJointSurvivalWeight_nonneg roots tstar offset)
      apply quitWeight_mul_pureTimeEdge_le roots who quitTime
        (tstar + offset) (hne offset (Finset.mem_range.mp hoffset))
        (hperfect (tstar + offset))
      exact le_trans (hgapRaw (tstar + offset + 1)) (hsupAt _)
    have hsumBound := Finset.sum_le_sum htermwise
    -- split the dominating sum into the `2 εr` part and the `supGap` part
    have hsplit : (∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight roots tstar offset *
          ((roots (tstar + offset) who true).toReal *
            (2 * εr + quittingFixedOpponentsContinueMass roots who
              (tstar + offset) * supGap))) =
        2 * εr * (∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots tstar offset *
            (roots (tstar + offset) who true).toReal) +
        supGap * (∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots tstar offset *
            ((roots (tstar + offset) who true).toReal *
              quittingFixedOpponentsContinueMass roots who
                (tstar + offset))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro offset _
      ring
    have hquitPart : (∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight roots tstar offset *
          (roots (tstar + offset) who true).toReal) ≤ 1 := by
      have hdominate : ∀ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots tstar offset *
            (roots (tstar + offset) who true).toReal ≤
          quittingJointSurvivalWeight roots tstar offset *
            quittingRootAbsorptionMass (roots (tstar + offset)) := by
        intro offset _
        exact mul_le_mul_of_nonneg_left
          (quitProbability_le_absorptionMass _ who)
          (quittingJointSurvivalWeight_nonneg roots tstar offset)
      calc (∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots tstar offset *
            (roots (tstar + offset) who true).toReal) ≤
          ∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight roots tstar offset *
              quittingRootAbsorptionMass (roots (tstar + offset)) :=
            Finset.sum_le_sum hdominate
        _ = 1 - quittingJointSurvivalWeight roots tstar fuel :=
            sum_jointSurvivalWeight_mul_absorptionMass roots tstar fuel
        _ ≤ 1 := by
            linarith [quittingJointSurvivalWeight_nonneg roots tstar fuel]
    have hcontractPart : (∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight roots tstar offset *
          ((roots (tstar + offset) who true).toReal *
            quittingFixedOpponentsContinueMass roots who
              (tstar + offset))) ≤ 1 - ρ := by
      have hpointwise : ∀ offset,
          (roots (tstar + offset) who true).toReal *
            quittingFixedOpponentsContinueMass roots who (tstar + offset) =
          quittingRootAbsorptionMass (roots (tstar + offset)) -
            quittingRootOpponentAbsorptionMass (roots (tstar + offset))
              who := by
        intro offset
        exact quitWeight_mul_opponentContinueMass_eq
          (roots (tstar + offset)) who
      have hrewriteSum : (∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots tstar offset *
            ((roots (tstar + offset) who true).toReal *
              quittingFixedOpponentsContinueMass roots who
                (tstar + offset))) =
          (∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight roots tstar offset *
              quittingRootAbsorptionMass (roots (tstar + offset))) -
          (∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight roots tstar offset *
              quittingRootOpponentAbsorptionMass (roots (tstar + offset))
                who) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro offset _
        rw [hpointwise offset]
        ring
      rw [hrewriteSum, sum_jointSurvivalWeight_mul_absorptionMass roots tstar]
      have hactivity := hactive tstar fuel
      linarith
    have hgapPart : supGap * (∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight roots tstar offset *
          ((roots (tstar + offset) who true).toReal *
            quittingFixedOpponentsContinueMass roots who
              (tstar + offset))) ≤ supGap * (1 - ρ) :=
      mul_le_mul_of_nonneg_left hcontractPart hsup0
    have hεrPart : 2 * εr * (∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight roots tstar offset *
          (roots (tstar + offset) who true).toReal) ≤ 2 * εr := by
      have hquitPos : 0 ≤ ∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots tstar offset *
            (roots (tstar + offset) who true).toReal :=
        Finset.sum_nonneg fun offset _ => mul_nonneg
          (quittingJointSurvivalWeight_nonneg roots tstar offset)
          ENNReal.toReal_nonneg
      nlinarith
    rw [hunroll]
    rw [hsplit] at hsumBound
    linarith
  -- every gap is dominated by `3 εr + supGap (1 - ρ)`
  have hkey : ∀ tstar, gap tstar ≤ 3 * εr + supGap * (1 - ρ) := by
    intro tstar
    have hRHS0 : 0 ≤ 3 * εr + supGap * (1 - ρ) := by
      have hproduct := mul_nonneg hsup0 (by linarith : (0 : ℝ) ≤ 1 - ρ)
      linarith
    rcases hcase : quitTime with _ | target
    · -- never quit: push the horizon to infinity
      apply max_le _ hRHS0
      refine le_of_forall_pos_le_add fun slack hslack => ?_
      have hshrunk : 0 < slack / (2 * M + 1) := by positivity
      obtain ⟨fuel, hfuel⟩ := exists_pow_lt_of_lt_one hshrunk
        (by linarith : 1 - δ < 1)
      have hwindow := hestimate tstar fuel (fun offset _ => by simp [hcase])
      have hjsw0 := quittingJointSurvivalWeight_nonneg roots tstar fuel
      have hjswPow := quittingJointSurvivalWeight_le_pow roots hδ1 hfloor
        tstar fuel
      have hendGap : quittingRootSequencePureTimeTerminalValue reward roots
          who quitTime (tstar + fuel) -
          quittingRootSequenceTerminalValue reward roots who
            (tstar + fuel) ≤ 2 * M :=
        le_trans (hgapRaw _) (hgapBound _)
      have hboundary : quittingJointSurvivalWeight roots tstar fuel *
          (quittingRootSequencePureTimeTerminalValue reward roots who
              quitTime (tstar + fuel) -
            quittingRootSequenceTerminalValue reward roots who
              (tstar + fuel)) ≤ (1 - δ) ^ fuel * (2 * M) := by
        calc quittingJointSurvivalWeight roots tstar fuel *
            (quittingRootSequencePureTimeTerminalValue reward roots who
                quitTime (tstar + fuel) -
              quittingRootSequenceTerminalValue reward roots who
                (tstar + fuel)) ≤
            quittingJointSurvivalWeight roots tstar fuel * (2 * M) :=
              mul_le_mul_of_nonneg_left hendGap hjsw0
          _ ≤ (1 - δ) ^ fuel * (2 * M) :=
              mul_le_mul_of_nonneg_right hjswPow (by linarith)
      have hpow : (1 - δ) ^ fuel * (2 * M) ≤ slack := by
        have hcancel : slack / (2 * M + 1) * (2 * M + 1) = slack :=
          div_mul_cancel₀ slack (by linarith : (2 : ℝ) * M + 1 ≠ 0)
        have hpow0 : (0 : ℝ) ≤ (1 - δ) ^ fuel := pow_nonneg (by linarith) _
        have hmul := mul_le_mul_of_nonneg_right hfuel.le
          (by linarith : (0 : ℝ) ≤ 2 * M)
        have hshrunk0 : 0 ≤ slack / (2 * M + 1) := hshrunk.le
        calc (1 - δ) ^ fuel * (2 * M) ≤
            slack / (2 * M + 1) * (2 * M) := hmul
          _ ≤ slack := by linarith
      linarith
    · rcases le_or_gt tstar target with horder | horder
      · -- quit at `target`: anchor the window at the quit date
        apply max_le _ hRHS0
        have hne : ∀ offset, offset < target - tstar →
            quitTime ≠ some (tstar + offset) := by
          intro offset hoffset heq
          rw [hcase] at heq
          have : target = tstar + offset := Option.some.inj heq
          omega
        have hwindow := hestimate tstar (target - tstar) hne
        have hindex : tstar + (target - tstar) = target := by omega
        rw [hindex] at hwindow
        have hanchor : quittingRootSequencePureTimeTerminalValue reward
            roots who quitTime target -
            quittingRootSequenceTerminalValue reward roots who target ≤
            εr := by
          rw [hcase]
          rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
          have hclause := (hperfect target who).1
          have hrecursion :=
            quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
              reward roots who target
          rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward roots
            who (quittingRootSequenceTailVector reward roots (target + 1))
            target, ← hrecursion] at hclause
          linarith
        have hjsw0 := quittingJointSurvivalWeight_nonneg roots tstar
          (target - tstar)
        have hjsw1 := quittingJointSurvivalWeight_le_one roots tstar
          (target - tstar)
        have hboundary : quittingJointSurvivalWeight roots tstar
            (target - tstar) *
            (quittingRootSequencePureTimeTerminalValue reward roots who
                quitTime target -
              quittingRootSequenceTerminalValue reward roots who target) ≤
            εr := by
          calc quittingJointSurvivalWeight roots tstar (target - tstar) *
              (quittingRootSequencePureTimeTerminalValue reward roots who
                  quitTime target -
                quittingRootSequenceTerminalValue reward roots who
                  target) ≤
              quittingJointSurvivalWeight roots tstar (target - tstar) *
                εr := mul_le_mul_of_nonneg_left hanchor hjsw0
            _ ≤ 1 * εr := mul_le_mul_of_nonneg_right hjsw1 hεr
            _ = εr := one_mul εr
        linarith
      · -- the quit date already passed: the hazard never quits again
        apply max_le _ hRHS0
        refine le_of_forall_pos_le_add fun slack hslack => ?_
        have hshrunk : 0 < slack / (2 * M + 1) := by positivity
        obtain ⟨fuel, hfuel⟩ := exists_pow_lt_of_lt_one hshrunk
          (by linarith : 1 - δ < 1)
        have hne : ∀ offset, offset < fuel →
            quitTime ≠ some (tstar + offset) := by
          intro offset _ heq
          rw [hcase] at heq
          have : target = tstar + offset := Option.some.inj heq
          omega
        have hwindow := hestimate tstar fuel hne
        have hjsw0 := quittingJointSurvivalWeight_nonneg roots tstar fuel
        have hjswPow := quittingJointSurvivalWeight_le_pow roots hδ1 hfloor
          tstar fuel
        have hendGap : quittingRootSequencePureTimeTerminalValue reward
            roots who quitTime (tstar + fuel) -
            quittingRootSequenceTerminalValue reward roots who
              (tstar + fuel) ≤ 2 * M :=
          le_trans (hgapRaw _) (hgapBound _)
        have hboundary : quittingJointSurvivalWeight roots tstar fuel *
            (quittingRootSequencePureTimeTerminalValue reward roots who
                quitTime (tstar + fuel) -
              quittingRootSequenceTerminalValue reward roots who
                (tstar + fuel)) ≤ (1 - δ) ^ fuel * (2 * M) := by
          calc quittingJointSurvivalWeight roots tstar fuel *
              (quittingRootSequencePureTimeTerminalValue reward roots who
                  quitTime (tstar + fuel) -
                quittingRootSequenceTerminalValue reward roots who
                  (tstar + fuel)) ≤
              quittingJointSurvivalWeight roots tstar fuel * (2 * M) :=
                mul_le_mul_of_nonneg_left hendGap hjsw0
            _ ≤ (1 - δ) ^ fuel * (2 * M) :=
                mul_le_mul_of_nonneg_right hjswPow (by linarith)
        have hpow : (1 - δ) ^ fuel * (2 * M) ≤ slack := by
          have hcancel : slack / (2 * M + 1) * (2 * M + 1) = slack :=
            div_mul_cancel₀ slack (by linarith : (2 : ℝ) * M + 1 ≠ 0)
          have hpow0 : (0 : ℝ) ≤ (1 - δ) ^ fuel := pow_nonneg (by linarith) _
          have hmul := mul_le_mul_of_nonneg_right hfuel.le
            (by linarith : (0 : ℝ) ≤ 2 * M)
          have hshrunk0 : 0 ≤ slack / (2 * M + 1) := hshrunk.le
          calc (1 - δ) ^ fuel * (2 * M) ≤
              slack / (2 * M + 1) * (2 * M) := hmul
            _ ≤ slack := by linarith
        linarith
  -- solve the supremum inequality
  have hsupSolve : supGap ≤ 3 * εr / ρ := by
    have hsupIneq : supGap ≤ 3 * εr + supGap * (1 - ρ) := by
      apply csSup_le hrange
      rintro value ⟨time, rfl⟩
      exact hkey time
    have hmul : supGap * ρ ≤ 3 * εr := by nlinarith
    rw [le_div_iff₀ hρ0]
    linarith
  have hzero := le_trans (hgapRaw 0) (le_trans (hsupAt 0) hsupSolve)
  linarith

/-! ## Global activity gives the sequence equilibrium -/

/-- A root sequence with a per-stage absorption floor, perfect rows, and
`ρ`-activity for every player is a global `3 εr / ρ` root-sequence
equilibrium: pure-time extremality extends the pure-time caps to every
hazard deviation. -/
theorem isεQuittingRootSequenceNash_of_active
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (roots : ℕ → ι → PMF Bool)
    {εr δ ρ : ℝ} (hεr : 0 ≤ εr) (hδ0 : 0 < δ) (hρ0 : 0 < ρ)
    (hfloor : ∀ n, δ ≤ quittingRootAbsorptionMass (roots n))
    (hperfect : ∀ n, QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward roots (n + 1)) (roots n) εr)
    (hactive : ∀ (who : ι) (start fuel : ℕ),
      ρ ≤ quittingJointSurvivalWeight roots start fuel +
        ∑ t ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots start t *
            quittingRootOpponentAbsorptionMass (roots (start + t)) who) :
    IsεQuittingRootSequenceNash reward (3 * εr / ρ) roots := by
  intro who hazard
  refine le_of_forall_pos_le_add fun slack hslack => ?_
  obtain ⟨quitTime, hquitTime⟩ :=
    exists_quittingRootSequencePureTimeTerminalValue_ge_sub reward roots who
      hazard hslack
  have hpure := quittingRootSequencePureTimeTerminalValue_le_of_active roots
    who hεr hδ0 hρ0 hfloor hperfect (hactive who) quitTime
  linarith

end GameTheory
