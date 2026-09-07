import UniformEquilibrium.Quitting.Root.NestedCapChildInfiniteSurvivalDebtor

/-! # Late fixed outsider with a half-gap floor -/

noncomputable section
namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- After choosing the starting child sufficiently late, one actual terminal
gap witness copied through every later forced-owner root retains at least half
the game-level gap.  The child, label, and response are selected once before
the later depth. -/
theorem HasTerminalExploitabilityGap.exists_late_fixedOutsider_halfGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (hgap : 0 < gap)
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
    ∃ (start : ℕ) (who : ι) (choice : Option ℕ),
      minimumStart ≤ start ∧ who ≠ owner ∧
      (choice = none ∨ ∃ time ≤ start, choice = some time) ∧
      quittingTerminalPayoff reward
          (Function.update
            (quittingPureTimeCapChild reward (profiles start) owner start) who
            (quittingPureTimeBehaviorStrategy reward who choice)) who =
        quittingContinuationBestResponseValue reward
          (quittingPureTimeCapChild reward (profiles start) owner start) who ∧
      gap ≤ quittingTerminalDeviationDebt reward
        (quittingPureTimeCapChild reward (profiles start) owner start) who ∧
      ∀ fuel,
        let shiftedRoots := fun offset =>
          quittingForcedOwnerContinueRoot roots owner (start + offset)
        let word := quittingReversePrefixRootStack shiftedRoots fuel
        let response := quittingCopyLiteralRootStackThenDeviation
          reward word who (quittingPureTimeBehaviorStrategy reward who choice)
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
                (quittingPureTimeCapChild reward (profiles start) owner start)
                who) ∧
        gap / 2 ≤ quittingTerminalPayoff reward
              (Function.update
                (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
                  (start + fuel)) who response) who -
            quittingTerminalPayoff reward
              (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
                (start + fuel)) who ∧
        gap / 2 ≤ quittingTerminalDeviationDebt reward
          (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
            (start + fuel)) who := by
  have hlate :=
    eventually_one_sub_le_jointSurvivalWindow_of_summable_marginalHazard
      roots hhazard (show 0 < (1 / 2 : ℝ) by norm_num)
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.1 hlate
  let start := max cutoff minimumStart
  have hminimum : minimumStart ≤ start := le_max_right _ _
  have hstart := hcutoff start (le_max_left _ _)
  obtain ⟨who, choice, hwho, hchoice, hcap, hdebt, hfuture⟩ :=
    hexploit.exists_fixedOutsiderResponse_for_all_capChildren reward hgap
      profiles roots owner hnested hexact hpositive hbase
      (fun horizon => Finset.prod_nonneg fun _ _ =>
        quittingStationaryContinueMass_nonneg _) start
  refine ⟨start, who, choice, hminimum, hwho, hchoice, hcap, hdebt,
    fun fuel => ?_⟩
  dsimp only
  refine ⟨(hfuture fuel).1, ?_⟩
  let shiftedRoots := fun offset => roots (start + offset)
  let word := quittingReversePrefixRootStack
    (fun offset => quittingForcedOwnerContinueRoot roots owner (start + offset))
    fuel
  have horiginal : (1 / 2 : ℝ) ≤
      ∏ offset ∈ Finset.range fuel,
        quittingStationaryContinueMass (shiftedRoots offset) := by
    have := hstart fuel
    simp only [shiftedRoots]
    norm_num at this ⊢
    exact this
  have hforced : (1 / 2 : ℝ) ≤
      quittingLiteralRootStackJointSurvival word := by
    refine horiginal.trans ?_
    simpa [word, shiftedRoots, quittingForcedOwnerContinueRoot,
      quittingLiteralRootStackJointSurvival_reversePrefixRootStack] using
      quittingJointSurvivalPrefix_le_forcedContinueWindow
        shiftedRoots owner 0 fuel
  have hbaseGain : gap ≤ quittingTerminalPayoff reward
          (Function.update
            (quittingPureTimeCapChild reward (profiles start) owner start) who
            (quittingPureTimeBehaviorStrategy reward who choice)) who -
        quittingTerminalPayoff reward
          (quittingPureTimeCapChild reward (profiles start) owner start) who := by
    rw [hcap]
    exact hdebt
  have hscaled := mul_le_mul hforced hbaseGain hgap.le
    (quittingLiteralRootStackJointSurvival_nonneg word)
  have hgain := (hfuture fuel).1
  have hgainFloor : gap / 2 ≤ quittingTerminalPayoff reward
          (Function.update
            (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
              (start + fuel)) who
            (quittingCopyLiteralRootStackThenDeviation reward word who
              (quittingPureTimeBehaviorStrategy reward who choice))) who -
        quittingTerminalPayoff reward
          (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
            (start + fuel)) who := by
    rw [hgain]
    nlinarith
  constructor
  · exact hgainFloor
  · have hcapBound :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward
        (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
          (start + fuel)) who
        (quittingCopyLiteralRootStackThenDeviation reward word who
          (quittingPureTimeBehaviorStrategy reward who choice))
    unfold quittingTerminalDeviationDebt
    change gap / 2 ≤ _
    change quittingTerminalPayoff reward
        (Function.update
          (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
            (start + fuel)) who
          (quittingCopyLiteralRootStackThenDeviation reward word who
            (quittingPureTimeBehaviorStrategy reward who choice))) who - _ =
        quittingLiteralRootStackJointSurvival word * _ at hgain
    linarith

end GameTheory
