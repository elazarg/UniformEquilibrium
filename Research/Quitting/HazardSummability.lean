/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DivergentChargeRecurrence
import Research.Quitting.SoloTailStoppingVerification
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchDeviationCap
import UniformEquilibrium.Quitting.Paths.OpponentClockDichotomy
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# Summability of the hazards of an exact solo quitting tail

A root sequence carries two independent charges: its *joint* absorption charge
`quittingRootSequenceAbsorptionCharge`, the one-date probability that somebody
quits, and, for each coordinate, the *opponent* clock charge
`quittingOpponentClockCharge`, the one-date probability that somebody other
than that coordinate quits.  Divergence of the first kills the phantom;
divergence of the second closes the refusal deviation.  This file assembles
the two with the stopping bounds of
`Research/Quitting/SoloTailStoppingVerification.lean`.

* **No phantom**
  (`quittingValue_eq_rootSequenceTerminalValue_of_not_summable`): a bounded
  value sequence obeying the exact policy recursion of a root sequence whose
  joint absorption charge diverges *is* that root sequence's honest terminal
  payoff.  The declared boundary is transported by the joint survival product,
  which vanishes.
* **Refusal cap under a divergent clock**
  (`quittingRootSequencePureTimeTerminalValue_none_le_value_of_divergentClock`).
* **Verification**
  (`isεAsymptoticNash_rootSequenceProfile_of_exactSoloTail`): an exact solo
  root sequence with divergent joint charge and divergent clocks is an exact
  terminal equilibrium of the quitting game at its own prescribed payoff.
* **Hazard summability**
  (`summable_absorptionCharge_or_lonelySoloist_of_exactSoloTail`): under a
  positive terminal exploitability gap, an exact solo root sequence has
  summable joint absorption charge unless some coordinate's opponent clock is
  summable.  `summable_absorptionCharge_or_lonelyNegativeSoloist` sharpens the
  exceptional branch to a strictly negative singleton reward: a lonely soloist
  is cofinally the designated quitter
  (`exists_isQuittingSoloRoot_of_not_summable_absorptionCharge`), which floors
  its prescribed value at its own singleton reward and caps refusal
  (`quittingRootSequencePureTimeTerminalValue_none_le_value_of_cofinalSolo`).
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## The joint absorption charge of a root sequence -/

/-- One-date probability that somebody quits at the root sequence's root. -/
def quittingRootSequenceAbsorptionCharge (roots : ℕ → ι → PMF Bool)
    (time : ℕ) : ℝ :=
  quittingRootAbsorptionMass (roots time)

omit [DecidableEq ι] in
theorem quittingRootSequenceAbsorptionCharge_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    0 ≤ quittingRootSequenceAbsorptionCharge roots time := by
  have hmass := quittingStationaryContinueMass_le_one (roots time)
  unfold quittingRootSequenceAbsorptionCharge quittingRootAbsorptionMass
  linarith

omit [DecidableEq ι] in
theorem quittingRootSequenceAbsorptionCharge_le_one
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    quittingRootSequenceAbsorptionCharge roots time ≤ 1 := by
  have hmass := quittingStationaryContinueMass_nonneg (roots time)
  unfold quittingRootSequenceAbsorptionCharge quittingRootAbsorptionMass
  linarith

/-- Joint survival across the window of `length` dates beginning at `start`. -/
def quittingRootSequenceJointSurvival (roots : ℕ → ι → PMF Bool)
    (start length : ℕ) : ℝ :=
  Math.survivalProduct
    (fun time => 1 - quittingRootSequenceAbsorptionCharge roots time)
    start length

omit [DecidableEq ι] in
theorem quittingRootSequenceJointSurvival_nonneg
    (roots : ℕ → ι → PMF Bool) (start length : ℕ) :
    0 ≤ quittingRootSequenceJointSurvival roots start length :=
  Math.survivalProduct_nonneg _
    (fun time => by
      have := quittingRootSequenceAbsorptionCharge_le_one roots time
      linarith) start length

omit [DecidableEq ι] in
/-- The joint survival peels its first factor. -/
theorem quittingRootSequenceJointSurvival_succ_left
    (roots : ℕ → ι → PMF Bool) (start length : ℕ) :
    quittingRootSequenceJointSurvival roots start (length + 1) =
      (1 - quittingRootSequenceAbsorptionCharge roots start) *
        quittingRootSequenceJointSurvival roots (start + 1) length := by
  unfold quittingRootSequenceJointSurvival
  rw [show length + 1 = 1 + length from by omega, Math.survivalProduct_add]
  congr 1
  simpa using Math.survivalProduct_succ
    (fun time => 1 - quittingRootSequenceAbsorptionCharge roots time) start 0

/-! ## The declared boundary is transported by joint survival -/

omit [DecidableEq ι] in
/-- One date of the exact policy recursion, written as an affine update with
the joint survival coefficient. -/
theorem quittingRootSuccessorPayoff_eq_absorbingContribution_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward tail root who =
      quittingRootAbsorbingContribution reward root who +
        (1 - quittingRootAbsorptionMass root) * tail who := by
  have hstep := quittingRootSuccessorPayoff_sub_tail reward tail root who
  linarith [hstep]

omit [DecidableEq ι] in
/-- **Boundary transport.**  The displacement between a prescribed value
sequence and the root sequence's honest terminal payoff is multiplied by the
joint survival product of the intervening window: it is a pure boundary term,
carrying no information about the rewards received inside the window. -/
theorem quittingValue_sub_rootSequenceTerminalValue_eq_jointSurvival_mul
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (who : ι) (start length : ℕ) :
    value start who -
        quittingRootSequenceTerminalValue reward roots who start =
      quittingRootSequenceJointSurvival roots start length *
        (value (start + length) who -
          quittingRootSequenceTerminalValue reward roots who
            (start + length)) := by
  induction length generalizing start with
  | zero => simp [quittingRootSequenceJointSurvival]
  | succ length ih =>
      have hvalue : value start who =
          quittingRootAbsorbingContribution reward (roots start) who +
            (1 - quittingRootSequenceAbsorptionCharge roots start) *
              value (start + 1) who := by
        conv_lhs => rw [hpolicy start]
        exact quittingRootSuccessorPayoff_eq_absorbingContribution_add reward
          (value (start + 1)) (roots start) who
      have hterminal :
          quittingRootSequenceTerminalValue reward roots who start =
            quittingRootAbsorbingContribution reward (roots start) who +
              (1 - quittingRootSequenceAbsorptionCharge roots start) *
                quittingRootSequenceTerminalValue reward roots who
                  (start + 1) := by
        conv_lhs =>
          rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff]
        exact quittingRootSuccessorPayoff_eq_absorbingContribution_add reward
          (fun _ => quittingRootSequenceTerminalValue reward roots who
            (start + 1)) (roots start) who
      rw [show start + (length + 1) = start + 1 + length from by omega,
        quittingRootSequenceJointSurvival_succ_left, hvalue, hterminal]
      linear_combination
        (1 - quittingRootSequenceAbsorptionCharge roots start) *
          ih (start + 1)

omit [DecidableEq ι] in
/-- **No phantom.**  A bounded value sequence obeying the exact policy
recursion of a root sequence whose joint absorption charge is not summable is
that root sequence's honest terminal payoff: almost-sure absorption leaves the
declared boundary no room. -/
theorem quittingValue_eq_rootSequenceTerminalValue_of_not_summable
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {bound : ℝ} (hbounded : ∀ time player, |value time player| ≤ bound)
    {rewardBound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hdiverges : ¬ Summable (quittingRootSequenceAbsorptionCharge roots))
    (who : ι) (start : ℕ) :
    value start who =
      quittingRootSequenceTerminalValue reward roots who start := by
  have hrewardBound0 : 0 ≤ rewardBound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal who) who)
  have hdisplacement : ∀ length,
      |value start who -
          quittingRootSequenceTerminalValue reward roots who start| ≤
        quittingRootSequenceJointSurvival roots start length *
          (bound + rewardBound) := by
    intro length
    rw [quittingValue_sub_rootSequenceTerminalValue_eq_jointSurvival_mul roots
      value hpolicy who start length, abs_mul,
      abs_of_nonneg (quittingRootSequenceJointSurvival_nonneg roots start
        length)]
    refine mul_le_mul_of_nonneg_left ?_
      (quittingRootSequenceJointSurvival_nonneg roots start length)
    have hleft := hbounded (start + length) who
    have hright := abs_quittingRootSequenceTerminalValue_le reward roots who
      (start + length) hrewardBound0 hreward
    have hleftAbs := abs_le.1 hleft
    have hrightAbs := abs_le.1 hright
    rw [abs_le]
    constructor <;> linarith [hleftAbs.1, hleftAbs.2, hrightAbs.1, hrightAbs.2]
  have hsurvival : Tendsto
      (fun length => quittingRootSequenceJointSurvival roots start length)
      atTop (nhds 0) :=
    Math.tendsto_prod_one_sub_zero_of_not_summable
      (quittingRootSequenceAbsorptionCharge roots)
      (quittingRootSequenceAbsorptionCharge_nonneg roots)
      (quittingRootSequenceAbsorptionCharge_le_one roots) hdiverges start
  have hlimit : Tendsto
      (fun length => quittingRootSequenceJointSurvival roots start length *
        (bound + rewardBound)) atTop (nhds 0) := by
    simpa using hsurvival.mul (tendsto_const_nhds
      (x := bound + rewardBound) (f := atTop (α := ℕ)))
  have hzero : |value start who -
      quittingRootSequenceTerminalValue reward roots who start| ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlimit hdisplacement
  have habs := abs_nonneg (value start who -
    quittingRootSequenceTerminalValue reward roots who start)
  have := abs_eq_zero.1 (le_antisymm hzero habs)
  linarith

/-! ## Capping the refusal deviation -/

/-- **Refusal cap under a divergent clock.**  If the coordinate's opponents
absorb almost surely, refusal is capped by the prescribed value. -/
theorem quittingRootSequencePureTimeTerminalValue_none_le_value_of_divergentClock
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {bound : ℝ} (hbounded : ∀ time player, |value time player| ≤ bound)
    {rewardBound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (who : ι)
    (hwindow : ∀ time, QuittingSoloDeviationDate roots who time)
    (hclock : ¬ Summable (quittingOpponentClockCharge roots who)) :
    quittingRootSequencePureTimeTerminalValue reward roots who none 0 ≤
      value 0 who := by
  have hrewardBound0 : 0 ≤ rewardBound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal who) who)
  have hshifted : ¬ Summable
      (fun offset => quittingOpponentClockCharge roots who (0 + offset)) := by
    simpa using hclock
  have hsurvival : Tendsto (quittingOpponentSurvivalWeight roots who 0) atTop
      (nhds 0) :=
    tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge roots who
      0 hshifted
  have hstep : ∀ length,
      quittingRootSequencePureTimeTerminalValue reward roots who none 0 -
          value 0 who ≤
        quittingOpponentSurvivalWeight roots who 0 length *
          (rewardBound + bound) := by
    intro length
    have hmain := quittingRootSequencePureTimeTerminalValue_none_sub_value_le
      roots value (fun _ => 0) hpolicy hnash (fun _ => le_rfl) who 0 length
      (fun offset _ => hwindow (0 + offset))
    have hnever : |quittingRootSequencePureTimeTerminalValue reward roots who
        none (0 + length)| ≤ rewardBound :=
      abs_quittingRootSequenceTerminalValue_le reward
        (quittingRootSequenceUpdate roots who (quittingPureTimeHazard none))
        who (0 + length) hrewardBound0 hreward
    have hvalue := hbounded (0 + length) who
    have hneverAbs := abs_le.1 hnever
    have hvalueAbs := abs_le.1 hvalue
    have hfactor :
        quittingRootSequencePureTimeTerminalValue reward roots who none
            (0 + length) - value (0 + length) who ≤ rewardBound + bound := by
      linarith [hneverAbs.2, hvalueAbs.1]
    have hweight := quittingOpponentSurvivalWeight_nonneg roots who 0 length
    have hscaled := mul_le_mul_of_nonneg_left hfactor hweight
    simp only [quittingDeviatorSlackBudget, mul_zero, Finset.sum_const_zero,
      add_zero] at hmain
    linarith
  have hlimit : Tendsto
      (fun length => quittingOpponentSurvivalWeight roots who 0 length *
        (rewardBound + bound)) atTop (nhds 0) := by
    simpa using hsurvival.mul (tendsto_const_nhds
      (x := rewardBound + bound) (f := atTop (α := ℕ)))
  have hnonpos :
      quittingRootSequencePureTimeTerminalValue reward roots who none 0 -
        value 0 who ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlimit hstep
  linarith

/-! ## The verification theorem -/

/-- **Deviation cap.**  Given the deviation window shape at every date, the
exact stopping cap at every finite date, and a refusal cap, every unilateral
behavioral deviation of `who` against the root-sequence profile is capped by
`who`'s prescribed value. -/
theorem quittingTerminalPayoff_update_rootSequenceProfile_le_value
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (who : ι)
    (hwindow : ∀ time, QuittingSoloDeviationDate roots who time)
    (hrefusal : quittingRootSequencePureTimeTerminalValue reward roots who
      none 0 ≤ value 0 who)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update (quittingRootSequenceProfile reward roots 0) who
          deviation) who ≤ value 0 who := by
  refine (quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy reward
    (quittingRootSequenceProfile reward roots 0) who deviation).trans ?_
  refine csSup_le (Set.range_nonempty _) ?_
  rintro payoff ⟨quitTime, rfl⟩
  simp only [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  cases quitTime with
  | none => exact hrefusal
  | some quitTime =>
      have hcap := quittingRootSequencePureTimeTerminalValue_le_value_of_exact
        roots value hpolicy hnash who 0 quitTime
        (fun offset _ => hwindow (0 + offset))
      simpa using hcap

/-- **Verification theorem.**  An exact solo root sequence whose joint
absorption charge diverges and whose every coordinate has a divergent opponent
clock is an exact terminal equilibrium of the quitting game, delivering its own
prescribed payoff. -/
theorem isεAsymptoticNash_rootSequenceProfile_of_exactSoloTail
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {bound : ℝ} (hbounded : ∀ time player, |value time player| ≤ bound)
    {rewardBound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) (owner time))
    (hjoint : ¬ Summable (quittingRootSequenceAbsorptionCharge roots))
    (hclock : ∀ who, ¬ Summable (quittingOpponentClockCharge roots who)) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingRootSequenceProfile reward roots 0) := by
  intro who deviation
  have hhonest := quittingValue_eq_rootSequenceTerminalValue_of_not_summable
    roots value hpolicy hbounded hreward hjoint who 0
  have hwindow : ∀ time, QuittingSoloDeviationDate roots who time :=
    fun time => quittingSoloDeviationDate_of_isQuittingSoloRoot (hsolo time) who
  have hrefusal :=
    quittingRootSequencePureTimeTerminalValue_none_le_value_of_divergentClock
      roots value hpolicy hnash hbounded hreward who hwindow (hclock who)
  have hcap := quittingTerminalPayoff_update_rootSequenceProfile_le_value roots
    value hpolicy hnash who hwindow hrefusal deviation
  have hprofile : quittingTerminalPayoff reward
      (quittingRootSequenceProfile reward roots 0) who = value 0 who :=
    hhonest.symm
  rw [hprofile, add_zero]
  exact hcap

/-! ## Hazard summability -/

/-! ## The lonely branch -/

/-- Refusal, unrolled: the ledger collected over the first `fuel` dates plus
the surviving stake times the refusal value from there. -/
theorem quittingRootSequencePureTimeTerminalValue_none_eq_ledger_add_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (fuel : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who none 0 =
      quittingLiveLedgerAccum reward roots who 0 fuel +
        quittingOpponentSurvivalWeight roots who 0 fuel *
          quittingRootSequencePureTimeTerminalValue reward roots who none
            fuel := by
  induction fuel with
  | zero => simp [quittingLiveLedgerAccum, quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hstep :=
        quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents
          reward roots who fuel
      have hledger : quittingLiveLedgerAccum reward roots who 0 (fuel + 1) =
          quittingLiveLedgerAccum reward roots who 0 fuel +
            quittingOpponentSurvivalWeight roots who 0 fuel *
              quittingFixedOpponentsContinueReward reward roots who fuel := by
        rw [quittingLiveLedgerAccum, Finset.sum_range_succ,
          ← quittingLiveLedgerAccum, Nat.zero_add]
      rw [hledger, quittingOpponentSurvivalWeight_succ, Nat.zero_add, ih, hstep]
      ring

/-- **The surviving stake in refusal vanishes.**  The ledger converges to the
refusal value, so the residual term of the unrolling tends to zero.  No
summability of the opponent clock is needed: the ledger's convergence is the
definition of the refusal value. -/
theorem tendsto_survivalWeight_mul_refusalValue_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    Tendsto (fun fuel => quittingOpponentSurvivalWeight roots who 0 fuel *
        quittingRootSequencePureTimeTerminalValue reward roots who none fuel)
      atTop (nhds 0) := by
  have hledger := tendsto_quittingLiveLedgerAccum reward roots who
  have hconst : Tendsto (fun _ : ℕ =>
      quittingRootSequencePureTimeTerminalValue reward roots who none 0) atTop
      (nhds (quittingRootSequencePureTimeTerminalValue reward roots who
        none 0)) := tendsto_const_nhds
  have hdiff := hconst.sub hledger
  simp only [sub_self] at hdiff
  refine hdiff.congr fun fuel => ?_
  have hunroll :=
    quittingRootSequencePureTimeTerminalValue_none_eq_ledger_add_survival reward
      roots who fuel
  linarith

/-- At a date whose only possible quitter is `who`, exact root Nash floors
`who`'s prescribed value at its own singleton reward: quitting alone is
available and meets no collision. -/
theorem quittingSoloReward_le_value_of_isQuittingSoloRoot
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {who : ι} {time : ℕ} (hsolo : IsQuittingSoloRoot (roots time) who) :
    quittingSoloReward reward who who ≤ value time who := by
  have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash reward
    (value (time + 1)) (roots time) who
    ((isεQuittingRootEndpointNash_iff_isεQuittingRootNash reward
      (value (time + 1)) 0 (roots time)).1 (hnash time))
  rw [hsolo.quitPayoff_owner reward (value (time + 1))] at hquit
  rw [hpolicy time]
  exact hquit

/-- **Refusal cap in the lonely branch.**  If `who` is the sole possible
quitter at arbitrarily late dates and its own singleton reward is nonnegative,
then refusing to quit is capped by `who`'s prescribed value.

The late solo dates floor `who`'s prescribed value at a nonnegative number,
while the surviving stake in the refusal unrolling vanishes, so the refusal
displacement is squeezed to zero.  Neither the opponent clock's summability
nor a bound on the value sequence enters. -/
theorem quittingRootSequencePureTimeTerminalValue_none_le_value_of_cofinalSolo
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (who : ι)
    (hwindow : ∀ time, QuittingSoloDeviationDate roots who time)
    (hcofinal : ∀ start, ∃ time, start ≤ time ∧
      IsQuittingSoloRoot (roots time) who)
    (hnonneg : 0 ≤ quittingSoloReward reward who who) :
    quittingRootSequencePureTimeTerminalValue reward roots who none 0 ≤
      value 0 who := by
  by_contra hcontra
  push Not at hcontra
  set gap := quittingRootSequencePureTimeTerminalValue reward roots who none 0 -
    value 0 who with hgap
  have hgapPos : 0 < gap := by rw [hgap]; linarith
  obtain ⟨start, hstart⟩ := eventually_atTop.1
    ((tendsto_order.1 (tendsto_survivalWeight_mul_refusalValue_zero reward roots
      who)).2 gap hgapPos)
  obtain ⟨time, htime, hsolo⟩ := hcofinal start
  have hstep := quittingRootSequencePureTimeTerminalValue_none_sub_value_le roots
    value (fun _ => 0) hpolicy hnash (fun _ => le_rfl) who 0 time
    (fun offset _ => hwindow (0 + offset))
  simp only [quittingDeviatorSlackBudget, mul_zero, Finset.sum_const_zero,
    add_zero, Nat.zero_add] at hstep
  have hvalue : 0 ≤ value time who :=
    hnonneg.trans (quittingSoloReward_le_value_of_isQuittingSoloRoot roots value
      hpolicy hnash hsolo)
  have hweight := quittingOpponentSurvivalWeight_nonneg roots who 0 time
  have hlate := hstart time htime
  nlinarith [hstep, hvalue, hweight, hlate]

/-- At a solo date whose designated quitter is not `who`, `who`'s opponent
clock charge is the whole joint absorption charge. -/
theorem quittingOpponentClockCharge_eq_absorptionCharge_of_ne
    (roots : ℕ → ι → PMF Bool) {owner who : ι} {time : ℕ}
    (hsolo : IsQuittingSoloRoot (roots time) owner) (hne : who ≠ owner) :
    quittingOpponentClockCharge roots who time =
      quittingRootSequenceAbsorptionCharge roots time := by
  have hpure : roots time who = PMF.pure false := hsolo who hne
  have hupdate : Function.update (roots time) who (PMF.pure false) =
      roots time := by
    rw [← hpure]
    exact Function.update_eq_self who (roots time)
  rw [quittingOpponentClockCharge_eq_one_sub,
    quittingFixedOpponentsContinueMass, hupdate]
  rfl

/-- **The lonely soloist is cofinally the designated quitter.**  If the joint
absorption charge diverges while `who`'s opponent clock is summable, then at
arbitrarily late dates `who` is the only coordinate that may quit: on every
suffix where it is not, the two charges agree termwise. -/
theorem exists_isQuittingSoloRoot_of_not_summable_absorptionCharge
    (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι)
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) (owner time)) (who : ι)
    (hjoint : ¬ Summable (quittingRootSequenceAbsorptionCharge roots))
    (hclock : Summable (quittingOpponentClockCharge roots who))
    (start : ℕ) :
    ∃ time, start ≤ time ∧ IsQuittingSoloRoot (roots time) who := by
  by_contra hcontra
  push Not at hcontra
  refine hjoint ?_
  have hagree : ∀ offset : ℕ,
      quittingOpponentClockCharge roots who (offset + start) =
        quittingRootSequenceAbsorptionCharge roots (offset + start) := by
    intro offset
    have hne : who ≠ owner (offset + start) := by
      intro heq
      refine hcontra (offset + start) (by omega) ?_
      rw [heq]
      exact hsolo (offset + start)
    exact quittingOpponentClockCharge_eq_absorptionCharge_of_ne roots
      (hsolo (offset + start)) hne
  have hshift : Summable fun offset =>
      quittingRootSequenceAbsorptionCharge roots (offset + start) :=
    ((summable_nat_add_iff start).2 hclock).congr hagree
  exact (summable_nat_add_iff start).1 hshift

/-- **Hazard summability, sharpened exceptional branch.**  Under a positive
terminal exploitability gap, an exact solo root sequence has summable joint
absorption charge unless some coordinate is a lonely soloist -- its opponent
clock summable -- with a strictly negative singleton reward. -/
theorem summable_absorptionCharge_or_lonelyNegativeSoloist
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {bound : ℝ} (hbounded : ∀ time player, |value time player| ≤ bound)
    {rewardBound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) (owner time))
    {gap : ℝ} (hgapPos : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    Summable (quittingRootSequenceAbsorptionCharge roots) ∨
      ∃ who, Summable (quittingOpponentClockCharge roots who) ∧
        quittingSoloReward reward who who < 0 := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hjoint, hbranch⟩ := hcontra
  have hhonest := fun (who : ι) =>
    quittingValue_eq_rootSequenceTerminalValue_of_not_summable roots value
      hpolicy hbounded hreward hjoint who 0
  have hwindow : ∀ (who : ι) time, QuittingSoloDeviationDate roots who time :=
    fun who time =>
      quittingSoloDeviationDate_of_isQuittingSoloRoot (hsolo time) who
  have hrefusal : ∀ who : ι,
      quittingRootSequencePureTimeTerminalValue reward roots who none 0 ≤
        value 0 who := by
    intro who
    by_cases hsummable : Summable (quittingOpponentClockCharge roots who)
    · exact quittingRootSequencePureTimeTerminalValue_none_le_value_of_cofinalSolo
        roots value hpolicy hnash who (hwindow who)
        (exists_isQuittingSoloRoot_of_not_summable_absorptionCharge roots owner
          hsolo who hjoint hsummable) (hbranch who hsummable)
    · exact
        quittingRootSequencePureTimeTerminalValue_none_le_value_of_divergentClock
          roots value hpolicy hnash hbounded hreward who (hwindow who) hsummable
  obtain ⟨who, deviation, hbeat⟩ :=
    hexploit (quittingRootSequenceProfile reward roots 0)
  have hcap := quittingTerminalPayoff_update_rootSequenceProfile_le_value roots
    value hpolicy hnash who (hwindow who) (hrefusal who) deviation
  have hprofile : quittingTerminalPayoff reward
      (quittingRootSequenceProfile reward roots 0) who = value 0 who :=
    (hhonest who).symm
  rw [hprofile] at hbeat
  linarith

/-- **Hazard summability.**  Under a positive terminal exploitability gap, an
exact solo root sequence has summable joint absorption charge unless some
coordinate's opponent clock is summable -- the lonely soloist, which carries
all the divergence by itself. -/
theorem summable_absorptionCharge_or_lonelySoloist_of_exactSoloTail
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {bound : ℝ} (hbounded : ∀ time player, |value time player| ≤ bound)
    {rewardBound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) (owner time))
    {gap : ℝ} (hgapPos : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    Summable (quittingRootSequenceAbsorptionCharge roots) ∨
      ∃ who, Summable (quittingOpponentClockCharge roots who) := by
  rcases summable_absorptionCharge_or_lonelyNegativeSoloist roots value owner
    hpolicy hnash hbounded hreward hsolo hgapPos hexploit with
    hsummable | ⟨who, hclock, -⟩
  · exact Or.inl hsummable
  · exact Or.inr ⟨who, hclock⟩

end GameTheory
