import UniformEquilibrium.Diagnostics.Quitting.DeadlinePaidFirstDisagreement
import UniformEquilibrium.Diagnostics.Quitting.FinFourActualPrefixHazard
import UniformEquilibrium.Quitting.Paths.InfiniteJointSurvivalDebt
import UniformEquilibrium.Quitting.Root.CapChildDeadlineAbsorption

/-!
# Positive-survival exact cap clocks and their actual paid children

The source assumptions supply the hazard and survival conclusions. A fixed
owner and initial source persist through every literal reverse prefix.
-/

noncomputable section
namespace GameTheory

open Math.Probability

/-- The original positive-survival exact recursion itself supplies the
summable hazard clock, positive literal infinite survival, and persistent
owner cap/debt floor.  None of these conclusions is accepted as source data. -/
theorem finFour_positiveSurvival_exactCapClock_source
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → Fin 4 → PMF Bool) (owner : Fin 4) {gamma : ℝ}
    (hnested : ∀ depth, profiles (depth + 1) =
      quittingRootThenContinuationProfile reward (roots depth)
        (profiles depth))
    (hexact : ∀ depth, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles depth) player)
      0 (roots depth))
    (hpositive : ∀ depth, 0 < quittingStationaryContinueMass (roots depth))
    (hbase : quittingTerminalPayoff reward
        (Function.update (profiles 0) owner
          (quittingPureTimeBehaviorStrategy reward owner (some 0))) owner =
      quittingContinuationBestResponseValue reward (profiles 0) owner)
    (hgamma : gamma ≤
      quittingTerminalDeviationDebt reward (profiles 0) owner)
    (hgamma0 : 0 ≤ gamma) :
    let infiniteSurvival := quittingInfiniteJointSurvival roots
    Summable (fun depth =>
        ∑ player, (roots depth player true).toReal) ∧
      0 < infiniteSurvival ∧
      ∀ depth,
        quittingTerminalPayoff reward
            (Function.update (profiles depth) owner
              (quittingPureTimeBehaviorStrategy reward owner (some depth))) owner =
          quittingContinuationBestResponseValue reward (profiles depth) owner ∧
        infiniteSurvival * gamma ≤
          quittingTerminalDeviationDebt reward (profiles depth) owner := by
  dsimp only
  have hsummable :=
    finFour_summable_actualExactPrefix_hazard_of_no_uniformPayoff
      reward hnot profiles roots hnested hexact
  have hinfinite :=
    quittingInfiniteJointSurvival_pos_of_summable_marginalHazard
      roots hsummable hpositive
  have hactual := quittingReversePrefixProfile_eq_of_nested
    reward profiles roots hnested
  have hcontinue : ∀ depth, 0 < (roots depth owner false).toReal :=
    fun depth => (hpositive depth).trans_le
      (quittingStationaryContinueMass_le_ownContinueProbability
        (roots depth) owner)
  have hclock := quitting_pureTimeCap_literalPrefix_transport
    reward roots (profiles 0) owner hbase
      (fun depth => by rw [hactual depth]; exact hexact depth) hcontinue
  refine ⟨hsummable, hinfinite, fun depth => ?_⟩
  constructor
  · rw [← hactual depth]
    exact (hclock depth).1
  · rw [← hactual depth]
    exact quitting_pureTimeCap_debt_ge_infiniteJointSurvival_mul
      reward roots (profiles 0) owner hbase
        (fun time => by rw [hactual time]; exact hexact time)
        hcontinue hgamma hgamma0 depth

/-- The positive-survival source and a fixed initial owner determine one
literal infinite-survival floor.  Every resulting literal cap child realizes
that owner's floor, terminates by its deadline, and jointly selects the
bounded cap recipient and prescribed-support source of a paid row. -/
theorem finFour_positiveSurvival_capChild_paidRow_source
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {gap M : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (hgap : 0 < gap) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → Fin 4 → PMF Bool) (owner : Fin 4) {gamma : ℝ}
    (hnested : ∀ depth, profiles (depth + 1) =
      quittingRootThenContinuationProfile reward (roots depth)
        (profiles depth))
    (hexact : ∀ depth, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles depth) player)
      0 (roots depth))
    (hpositive : ∀ depth, 0 < quittingStationaryContinueMass (roots depth))
    (hbase : quittingTerminalPayoff reward
        (quittingPureTimeCapChild reward (profiles 0) owner 0) owner =
      quittingContinuationBestResponseValue reward (profiles 0) owner)
    (hgamma : gamma ≤
      quittingTerminalDeviationDebt reward (profiles 0) owner)
    (hgamma0 : 0 ≤ gamma) :
    let infiniteSurvival := quittingInfiniteJointSurvival roots
    Summable (fun depth => ∑ player, (roots depth player true).toReal) ∧
      0 < infiniteSurvival ∧
      ∀ depth,
        quittingTerminalPayoff reward
            (quittingPureTimeCapChild reward (profiles depth) owner depth) owner =
          quittingContinuationBestResponseValue reward (profiles depth) owner ∧
        infiniteSurvival * gamma ≤
          quittingTerminalDeviationDebt reward (profiles depth) owner ∧
        quittingTerminalPayoff reward
              (quittingPureTimeCapChild reward (profiles depth) owner depth) owner -
            quittingTerminalPayoff reward (profiles depth) owner =
          quittingTerminalDeviationDebt reward (profiles depth) owner ∧
        infiniteSurvival * gamma ≤
          quittingTerminalPayoff reward
              (quittingPureTimeCapChild reward (profiles depth) owner depth) owner -
            quittingTerminalPayoff reward (profiles depth) owner ∧
        quittingTerminalDeviationDebt reward
          (quittingPureTimeCapChild reward (profiles depth) owner depth) owner = 0 ∧
        quittingLiveMass reward
          (quittingPureTimeCapChild reward (profiles depth) owner depth)
          (depth + 1) = 0 ∧
        ∃ observer, observer ≠ owner ∧
          ∃ source receiving : Option ℕ,
            source ∈ (quittingBehaviorStoppingLaw reward
              ((quittingPureTimeCapChild reward (profiles depth) owner depth)
                observer)).support ∧
            (receiving = none ∨
              ∃ time ≤ depth, receiving = some time) ∧
            quittingPureTimeDeviationPayoff reward
                (quittingPureTimeCapChild reward (profiles depth) owner depth)
                observer receiving =
              quittingContinuationBestResponseValue reward
                (quittingPureTimeCapChild reward (profiles depth) owner depth)
                observer ∧
            gap ≤ quittingTerminalDeviationDebt reward
              (quittingPureTimeCapChild reward (profiles depth) owner depth) observer ∧
            gap ≤ quittingPureTimeDeviationPayoff reward
                (quittingPureTimeCapChild reward (profiles depth) owner depth)
                observer receiving -
              quittingTerminalPayoff reward
                (quittingPureTimeCapChild reward (profiles depth) owner depth) observer ∧
            gap ≤ quittingPureTimeDeviationPayoff reward
                (quittingPureTimeCapChild reward (profiles depth) owner depth)
                observer receiving -
              quittingPureTimeDeviationPayoff reward
                (quittingPureTimeCapChild reward (profiles depth) owner depth)
                observer source ∧
            ∃ row : QuittingPaidFirstDisagreementRow reward
                (quittingPureTimeCapChild reward (profiles depth) owner depth)
                observer gap,
              row.sourceWitness = source ∧
                row.receivingWitness = receiving ∧
                row.start ≤ depth ∧ gap / (2 * M) ≤ row.liveMass := by
  dsimp only
  have hnot :=
    quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
      reward hgap hexploit
  have hsource := finFour_positiveSurvival_exactCapClock_source
    reward hnot profiles roots owner hnested hexact hpositive hbase hgamma hgamma0
  refine ⟨hsource.1, hsource.2.1, fun depth => ?_⟩
  have hattains := hsource.2.2 depth |>.1
  have hdebtFloor := hsource.2.2 depth |>.2
  have hchild :=
    quittingPureTimeCapChild_owner_zeroDebt_and_deadlineAbsorption
      reward profiles roots owner hnested hexact hpositive hbase depth
  have hgain := quittingPureTimeCapChild_ownerGain_eq_debt
    reward (profiles depth) owner depth hattains
  obtain ⟨observer, hne, source, receiving, hsourceSupport,
      hreceivingBound, hreceivingCap, hobserverDebt, hreceivingGain, hedge, row, hrowSource,
      hrowReceiving, hrowStart, hrowReach⟩ :=
    hexploit.exists_deadline_paidFirstDisagreement reward hgap hM hreward
      (quittingPureTimeCapChild reward (profiles depth) owner depth)
      owner depth hchild.1
      (quittingPureTimeCapChild_sure_owner_at_deadline
        reward (profiles depth) owner depth)
  refine ⟨hattains, hdebtFloor, hgain, ?_, hchild.1, hchild.2,
    observer, hne, source, receiving, hsourceSupport, hreceivingBound,
    hreceivingCap, hobserverDebt, hreceivingGain, hedge, row,
    hrowSource, hrowReceiving, hrowStart, hrowReach⟩
  rw [hgain]
  exact hdebtFloor

end GameTheory
