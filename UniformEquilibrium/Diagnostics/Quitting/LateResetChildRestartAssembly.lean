import UniformEquilibrium.Diagnostics.Quitting.LateResetChildCapPinExit
import UniformEquilibrium.Quitting.Root.CoherentPureTimeCapClock
import UniformEquilibrium.Quitting.Root.LateResetFixedOutsiderHalfGap

/-! # Late reset child restart assembly -/

noncomputable section
namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The fixed response selected at one late child, including its literal
copied-response equation and half-gap gain at every later actual child. -/
structure LateFixedOutsiderTransport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (start : ℕ) (who : ι) (seed : Option ℕ) (gap : ℝ) : Prop where
  seedBound : seed = none ∨ ∃ time ≤ start, seed = some time
  seedCap : quittingTerminalPayoff reward
      (Function.update
        (quittingPureTimeCapChild reward (profiles start) owner start) who
        (quittingPureTimeBehaviorStrategy reward who seed)) who =
    quittingContinuationBestResponseValue reward
      (quittingPureTimeCapChild reward (profiles start) owner start) who
  seedDebt : gap ≤ quittingTerminalDeviationDebt reward
    (quittingPureTimeCapChild reward (profiles start) owner start) who
  later : ∀ fuel,
    let shiftedRoots := fun offset =>
      quittingForcedOwnerContinueRoot roots owner (start + offset)
    let word := quittingReversePrefixRootStack shiftedRoots fuel
    let response := quittingCopyLiteralRootStackThenDeviation reward word who
      (quittingPureTimeBehaviorStrategy reward who seed)
    quittingTerminalPayoff reward
          (Function.update
            (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
              (start + fuel)) who response) who -
        quittingTerminalPayoff reward
          (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
            (start + fuel)) who =
      quittingLiteralRootStackJointSurvival word *
        (quittingTerminalPayoff reward
            (Function.update
              (quittingPureTimeCapChild reward (profiles start) owner start) who
              (quittingPureTimeBehaviorStrategy reward who seed)) who -
          quittingTerminalPayoff reward
            (quittingPureTimeCapChild reward (profiles start) owner start) who) ∧
    gap / 2 ≤ quittingTerminalPayoff reward
          (Function.update
            (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
              (start + fuel)) who response) who -
        quittingTerminalPayoff reward
          (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
            (start + fuel)) who ∧
    gap / 2 ≤ quittingTerminalDeviationDebt reward
      (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
        (start + fuel)) who

/-- A sufficiently late fixed half-gap response seeds a coherent cap clock on
the same shifted literal children.  Its reset branch consists of actual child
cap pins, each of which gives the canonical exact-root debt and absorption
exit. -/
theorem HasTerminalExploitabilityGap.exists_late_childRestart_capPinDichotomy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap M : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (hgap : 0 < gap) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hnested : ∀ depth, profiles (depth + 1) =
      quittingRootThenContinuationProfile reward (roots depth)
        (profiles depth))
    (hexact : ∀ depth, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles depth) player)
      0 (roots depth))
    (hpositive : ∀ depth, 0 < quittingStationaryContinueMass (roots depth))
    (hhazard : Summable (fun depth =>
      ∑ player, (roots depth player true).toReal))
    (hbase : quittingTerminalPayoff reward
        (quittingPureTimeCapChild reward (profiles 0) owner 0) owner =
      quittingContinuationBestResponseValue reward (profiles 0) owner)
    (minimumStart : ℕ) :
    ∃ (start : ℕ) (who : ι) (seed : Option ℕ)
        (choices : ℕ → Option ℕ),
      minimumStart ≤ start ∧ who ≠ owner ∧
      LateFixedOutsiderTransport reward profiles roots owner
        start who seed gap ∧
      let children := fun offset => quittingPureTimeCapChild reward
        (profiles (start + offset)) owner (start + offset)
      quittingTerminalPayoff reward
          (Function.update (children 0) who
            (quittingPureTimeBehaviorStrategy reward who seed)) who =
        quittingContinuationBestResponseValue reward (children 0) who ∧
      (∀ offset, gap / 2 ≤
        quittingTerminalDeviationDebt reward (children offset) who) ∧
      choices 0 = seed ∧
      (∀ offset, quittingTerminalPayoff reward
          (Function.update (children offset) who
            (quittingPureTimeBehaviorStrategy reward who (choices offset))) who =
        quittingContinuationBestResponseValue reward (children offset) who) ∧
      (∀ offset, choices (offset + 1) = some 0 ∨
        choices (offset + 1) = (choices offset).map Nat.succ) ∧
      ((∃ cutoff, ∀ offset, cutoff ≤ offset →
          choices (offset + 1) = (choices offset).map Nat.succ) ∨
        ((∀ cutoff, ∃ offset, cutoff ≤ offset ∧
            choices (offset + 1) = some 0) ∧
          ∀ᶠ offset in atTop,
            choices (offset + 1) = some 0 →
              LateResetChildCapPin reward (children (offset + 1)) who
                  (gap / 2) ∧
                quittingTerminalPayoff reward (children (offset + 1)) who ≤
                  reward (quittingSingletonTerminal who) who -
                    3 * (gap / 2) / 4 ∧
                ∀ exactRoot : ι → PMF Bool,
                  IsεQuittingRootNash reward
                      (fun player => quittingTerminalPayoff reward
                        (children (offset + 1)) player) 0 exactRoot →
                    min (gap / 2 / 2) ((gap / 2) ^ 2 / (16 * M)) ≤
                        quittingTerminalDebtSum reward (children (offset + 1)) -
                          quittingTerminalDebtSum reward
                            (quittingRootThenContinuationProfile reward exactRoot
                              (children (offset + 1))) ∧
                      min 1 (gap / 2 / (16 * M)) ≤
                        quittingRootAbsorptionMass exactRoot)) := by
  obtain ⟨start, who, seed, hstart, hwho, hseedBound, hseedCap,
      hseedDebt, hfuture⟩ :=
    hexploit.exists_late_fixedOutsider_halfGap reward hgap profiles roots owner
      hnested hexact hpositive hhazard hbase minimumStart
  let children := fun offset => quittingPureTimeCapChild reward
    (profiles (start + offset)) owner (start + offset)
  let forcedRoots := fun offset =>
    quittingForcedOwnerContinueRoot roots owner (start + offset)
  have hchildNested : ∀ offset, children (offset + 1) =
      quittingRootThenContinuationProfile reward (forcedRoots offset)
        (children offset) := by
    intro offset
    dsimp only [children, forcedRoots, quittingForcedOwnerContinueRoot]
    rw [show start + (offset + 1) = start + offset + 1 by omega,
      hnested (start + offset)]
    exact update_quittingRootThenContinuationProfile_pureTime_succ_eq
      reward (roots (start + offset)) (profiles (start + offset)) owner
        (start + offset)
  obtain ⟨choices, hchoicesZero, hchoicesCap, hchoicesStep⟩ :=
    exists_coherentPureTimeCapClock_of_nested reward children forcedRoots who
      seed hchildNested (by simpa [children] using hseedCap)
  have hdebt : ∀ offset, gap / 2 ≤
      quittingTerminalDeviationDebt reward (children offset) who := by
    intro offset
    simpa [children] using (hfuture offset).2.2
  have hopponent : Tendsto (fun offset =>
      quittingRootOpponentContinueMass (forcedRoots offset) who) atTop
      (nhds 1) := by
    have h :=
      (tendsto_forcedContinue_opponentSurvival_one_of_summable_marginalHazard
        roots owner who hhazard).comp (tendsto_add_atTop_nat start)
    convert h using 1
    funext offset
    simp only [Function.comp_apply, forcedRoots,
      quittingForcedOwnerContinueRoot, add_comm]
  have habsorption : Tendsto (fun offset =>
      quittingRootOpponentAbsorptionMass (forcedRoots offset) who) atTop
      (nhds 0) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hdifference := hone.sub hopponent
    convert hdifference using 1
    · funext offset
      rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass]
      ring
    · norm_num
  have hpins :=
    eventually_resetChild_everyExactRoot_debtDrop_and_absorptionFloor
      reward children forcedRoots who hM (half_pos hgap) hreward hchildNested
        habsorption (Eventually.of_forall fun offset => hdebt (offset + 1))
  let transport : LateFixedOutsiderTransport reward profiles roots owner
      start who seed gap := ⟨hseedBound, hseedCap, hseedDebt, hfuture⟩
  refine ⟨start, who, seed, choices, hstart, hwho, transport, ?_⟩
  dsimp only
  refine ⟨by simpa [children] using hseedCap, hdebt, hchoicesZero,
    hchoicesCap, hchoicesStep, ?_⟩
  rcases quittingCapClock_eventually_shift_or_cofinally_reset
      choices hchoicesStep with hshift | hreset
  · exact Or.inl hshift
  · refine Or.inr ⟨hreset, ?_⟩
    filter_upwards [hpins] with offset hpin
    intro hresetChoice
    apply hpin
    unfold ImmediateQuitAttainsTerminalCap
    simpa [hresetChoice] using hchoicesCap (offset + 1)

end GameTheory
