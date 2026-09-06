import UniformEquilibrium.Quitting.Root.NestedCapChildFixedDebtor
import UniformEquilibrium.Quitting.Paths.InfiniteJointSurvivalDebt

/-! # Fixed outsider responses with the literal infinite-survival floor -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual infinite joint-survival product is positive and works at every
starting depth. One outsider and one cap response are fixed before every
later child, retaining both the exact copied gain and its window/infinite floors. -/
theorem HasTerminalExploitabilityGap.exists_infiniteSurvival_fixedOutsiderResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap) (hgap : 0 < gap)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hnested : ∀ depth, profiles (depth + 1) =
      quittingRootThenContinuationProfile reward (roots depth) (profiles depth))
    (hexact : ∀ depth, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles depth) player) 0 (roots depth))
    (hpositive : ∀ depth, 0 < quittingStationaryContinueMass (roots depth))
    (hsummable : Summable (fun depth => ∑ player, (roots depth player true).toReal))
    (hbase : quittingTerminalPayoff reward
        (quittingPureTimeCapChild reward (profiles 0) owner 0) owner =
      quittingContinuationBestResponseValue reward (profiles 0) owner) :
    0 < quittingInfiniteJointSurvival roots ∧
      0 < quittingInfiniteJointSurvival roots * gap ∧
      ∀ start, ∃ (who : ι) (choice : Option ℕ),
        who ≠ owner ∧
        (choice = none ∨ ∃ time ≤ start, choice = some time) ∧
        quittingTerminalPayoff reward
            (Function.update (quittingPureTimeCapChild reward (profiles start) owner start)
              who (quittingPureTimeBehaviorStrategy reward who choice)) who =
          quittingContinuationBestResponseValue reward
            (quittingPureTimeCapChild reward (profiles start) owner start) who ∧
        gap ≤ quittingTerminalDeviationDebt reward
          (quittingPureTimeCapChild reward (profiles start) owner start) who ∧
        ∀ fuel,
          let shiftedRoots := fun offset =>
            quittingForcedOwnerContinueRoot roots owner (start + offset)
          let word := quittingReversePrefixRootStack shiftedRoots fuel
          let response := quittingCopyLiteralRootStackThenDeviation reward word who
            (quittingPureTimeBehaviorStrategy reward who choice)
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
                    (quittingPureTimeCapChild reward (profiles start) owner start)
                    who (quittingPureTimeBehaviorStrategy reward who choice)) who -
                quittingTerminalPayoff reward
                  (quittingPureTimeCapChild reward (profiles start) owner start) who) ∧
          quittingLiteralRootStackJointSurvival word * gap ≤
            quittingTerminalDeviationDebt reward
              (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
                (start + fuel)) who ∧
          quittingInfiniteJointSurvival roots * gap ≤
            quittingTerminalDeviationDebt reward
              (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
                (start + fuel)) who := by
  have hinfinite := quittingInfiniteJointSurvival_pos_of_summable_marginalHazard
    roots hsummable hpositive
  refine ⟨hinfinite, mul_pos hinfinite hgap, fun start => ?_⟩
  obtain ⟨who, choice, hwho, hchoice, hcap, hdebt, hfuture⟩ :=
    hexploit.exists_fixedOutsiderResponse_for_all_capChildren reward hgap
      profiles roots owner hnested hexact hpositive hbase
      (quittingInfiniteJointSurvival_le_prefix roots) start
  refine ⟨who, choice, hwho, hchoice, hcap, hdebt, fun fuel => ?_⟩
  dsimp only
  refine ⟨(hfuture fuel).1, ?_, (hfuture fuel).2⟩
  let word := quittingReversePrefixRootStack
    (fun offset => quittingForcedOwnerContinueRoot roots owner (start + offset)) fuel
  let response := quittingCopyLiteralRootStackThenDeviation reward word who
    (quittingPureTimeBehaviorStrategy reward who choice)
  have hbaseGain : gap ≤ quittingTerminalPayoff reward
          (Function.update (quittingPureTimeCapChild reward (profiles start) owner start)
            who (quittingPureTimeBehaviorStrategy reward who choice)) who -
        quittingTerminalPayoff reward
          (quittingPureTimeCapChild reward (profiles start) owner start) who := by
    rw [hcap]
    exact hdebt
  have hscaled := mul_le_mul_of_nonneg_left hbaseGain
    (quittingLiteralRootStackJointSurvival_nonneg word)
  have hcapBound := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
      (start + fuel)) who response
  have hgain := (hfuture fuel).1
  change quittingTerminalPayoff reward
      (Function.update
        (quittingPureTimeCapChild reward (profiles (start + fuel)) owner (start + fuel))
        who response) who -
      quittingTerminalPayoff reward
        (quittingPureTimeCapChild reward (profiles (start + fuel)) owner (start + fuel)) who =
    quittingLiteralRootStackJointSurvival word * _ at hgain
  unfold quittingTerminalDeviationDebt
  change quittingLiteralRootStackJointSurvival word * gap ≤ _
  linarith

end GameTheory
