import MathUE.PMFProduct.FiniteFubini
import MathUE.ProbabilityMassFunction.Simplex
import UniformEquilibrium.Diagnostics.Quitting.PureCoalitionOneDateNeverAdapters

/-!
# Four-player premark residual and deleted-reach regression

This exact two-stage example separates marked joint reach from a nonmover's
deleted reach.  The marked outsider toggle has gain `epsilon`, but its mover
retains debt `1 - epsilon`; another player's complete behavioral cap changes
by one even though the marked joint reach is `epsilon`.

The example is a finite regression only.  It supplies neither a source
producer nor a positive-gap table, renewal, Nash, or uniform equilibrium.
-/

noncomputable section

namespace GameTheory
namespace FinFourPremarkDeletedReachRegression

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
  QuittingSureSetOwnerRepair

abbrev Player := Fin 4

abbrev left : Player := 0
abbrev right : Player := 1
abbrev mover : Player := 2
abbrev observer : Player := 3

private theorem pair_ne_observerSingleton :
    ({left, right} : Finset Player) ≠ {observer} := by decide

private theorem moverTriple_ne_observerSingleton :
    ({left, right, mover} : Finset Player) ≠ {observer} := by decide

private theorem moverTriple_ne_pair :
    ({left, right, mover} : Finset Player) ≠ {left, right} := by decide

private theorem observerTriple_ne_observerSingleton :
    ({left, right, observer} : Finset Player) ≠ {observer} := by decide

private theorem observerTriple_ne_pair :
    ({left, right, observer} : Finset Player) ≠ {left, right} := by decide

private theorem observerTriple_ne_moverTriple :
    ({left, right, observer} : Finset Player) ≠ {left, right, mover} := by decide

private theorem moverSingleton_ne_pair :
    ({mover} : Finset Player) ≠ {left, right} := by decide

private theorem moverSingleton_ne_moverTriple :
    ({mover} : Finset Player) ≠ {left, right, mover} := by decide

private theorem moverSingleton_ne_observerTriple :
    ({mover} : Finset Player) ≠ {left, right, observer} := by decide

private theorem leftMover_ne_observerSingleton :
    ({left, mover} : Finset Player) ≠ {observer} := by decide

private theorem leftMover_ne_pair :
    ({left, mover} : Finset Player) ≠ {left, right} := by decide

private theorem leftMover_ne_moverTriple :
    ({left, mover} : Finset Player) ≠ {left, right, mover} := by decide

private theorem leftMover_ne_observerTriple :
    ({left, mover} : Finset Player) ≠ {left, right, observer} := by decide

private theorem leftMover_ne_moverObserver :
    ({left, mover} : Finset Player) ≠ {mover, observer} := by decide

private theorem rightMover_ne_observerSingleton :
    ({right, mover} : Finset Player) ≠ {observer} := by decide

private theorem rightMover_ne_pair :
    ({right, mover} : Finset Player) ≠ {left, right} := by decide

private theorem rightMover_ne_moverTriple :
    ({right, mover} : Finset Player) ≠ {left, right, mover} := by decide

private theorem rightMover_ne_observerTriple :
    ({right, mover} : Finset Player) ≠ {left, right, observer} := by decide

private theorem rightMover_ne_moverObserver :
    ({right, mover} : Finset Player) ≠ {mover, observer} := by decide

private theorem observerMover_eq_moverObserver :
    ({observer, mover} : Finset Player) = {mover, observer} := by decide

private theorem moverObserver_ne_pair :
    ({mover, observer} : Finset Player) ≠ {left, right} := by decide

private theorem moverObserver_ne_moverTriple :
    ({mover, observer} : Finset Player) ≠ {left, right, mover} := by decide

private theorem moverObserver_ne_observerTriple :
    ({mover, observer} : Finset Player) ≠ {left, right, observer} := by decide

@[simp] private theorem quittingQuitters_onlyObserverAction :
    quittingQuitters (![false, false, false, true] : Player → Bool) =
      {observer} := by decide

@[simp] private theorem onlyObserverAction_nonempty :
    ∃ who : Player, (![false, false, false, true] : Player → Bool) who = true := by
  exact ⟨observer, rfl⟩

@[simp] private theorem allContinueAction_not_nonempty :
    ¬ ∃ who : Player,
      (![false, false, false, false] : Player → Bool) who = true := by decide

@[simp] private theorem quittingQuitters_allContinueAction :
    quittingQuitters (![false, false, false, false] : Player → Bool) = ∅ := by decide

@[simp] private theorem moverOnlyAction_nonempty :
    ∃ who : Player,
      (![false, false, true, false] : Player → Bool) who = true := by
  exact ⟨mover, rfl⟩

@[simp] private theorem moverObserverAction_nonempty :
    ∃ who : Player,
      (![false, false, true, true] : Player → Bool) who = true := by
  exact ⟨mover, rfl⟩

@[simp] private theorem quittingQuitters_moverOnlyAction :
    quittingQuitters (![false, false, true, false] : Player → Bool) =
      {mover} := by decide

@[simp] private theorem quittingQuitters_moverObserverAction :
    quittingQuitters (![false, false, true, true] : Player → Bool) =
      {mover, observer} := by decide

/-- The displayed reward table; every unlisted coordinate is `-1`. -/
def reward (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : ℝ :=
  if terminal.1 = {observer} then 0
  else if terminal.1 = {left, right} then 0
  else if terminal.1 = {left, right, mover} then
    if who = mover ∨ who = observer then 1 else 0
  else if terminal.1 = {left, right, observer} then
    if who = observer then -1 else 0
  else if terminal.1 = {mover} then
    if who = mover then 1 else 0
  else if terminal.1 = {mover, observer} then
    if who = mover then 1 else 0
  else -1

theorem abs_reward_le_one (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : |reward terminal who| ≤ 1 := by
  simp only [reward]
  split_ifs <;> norm_num

/-- Player `3`'s date-zero coin, with Quit probability `1 - epsilon`. -/
def observerEarlyCoin (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) : PMF Bool :=
  bernoulliBool (1 - epsilon) (by linarith) (by linarith)

/-- At date zero only player `3` has a nonzero Quit probability. -/
def earlyRoot (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) : Player → PMF Bool := fun who =>
  if who = observer then observerEarlyCoin epsilon hepsilon0 hepsilon1
  else PMF.pure false

/-- Date-zero early hazard, followed by a pure coalition at date one and
perpetual continuation afterwards. -/
def twoStageProfile (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) (coalition : Finset Player) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward
    (earlyRoot epsilon hepsilon0 hepsilon1)
    (quittingPureCoalitionOneDateNeverProfile reward coalition)

/-- The source with marked pair `{0,1}`. -/
def sourceProfile (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) : (quittingGame reward).BehaviorProfile :=
  twoStageProfile epsilon hepsilon0 hepsilon1 {left, right}

/-- The marked outsider join, producing `{0,1,2}` at date one. -/
def markedProfile (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) : (quittingGame reward).BehaviorProfile :=
  twoStageProfile epsilon hepsilon0 hepsilon1 {left, right, mover}

/-- The incoming sibling, producing `{0,1,3}` at date one. -/
def incomingProfile (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) : (quittingGame reward).BehaviorProfile :=
  twoStageProfile epsilon hepsilon0 hepsilon1 {left, right, observer}

theorem reward_observer_singleton :
    reward (quittingSingletonTerminal observer) observer = 0 := by
  norm_num [reward, quittingSingletonTerminal, observer, left, right, mover]

theorem earlyRoot_expectedPayoff
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) (continuation : Payoff Player)
    (who : Player) :
    quittingRootExpectedPayoff reward continuation
        (earlyRoot epsilon hepsilon0 hepsilon1) who =
      epsilon * continuation who := by
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [earlyRoot, observerEarlyCoin, reward, quittingRootPayoff,
    expect_eq_sum, observer, left, right, mover]

theorem twoStageProfile_terminalPayoff
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) (coalition : Finset Player)
    (hcoalition : coalition.Nonempty) (who : Player) :
    quittingTerminalPayoff reward
        (twoStageProfile epsilon hepsilon0 hepsilon1 coalition) who =
      epsilon * quittingSetReward reward coalition who := by
  rw [twoStageProfile, quittingTerminalPayoff_rootThenContinuation_eq,
    earlyRoot_expectedPayoff]
  congr 1
  exact quittingTerminalPayoff_pureCoalitionOneDateNever
    reward coalition hcoalition who

theorem source_payoff_mover
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingTerminalPayoff reward
        (sourceProfile epsilon hepsilon0 hepsilon1) mover = 0 := by
  rw [sourceProfile, twoStageProfile_terminalPayoff]
  · norm_num [quittingSetReward, reward, left, right, mover, observer]
  · simp [left]

theorem marked_payoff_mover
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingTerminalPayoff reward
        (markedProfile epsilon hepsilon0 hepsilon1) mover = epsilon := by
  rw [markedProfile, twoStageProfile_terminalPayoff]
  · simp [quittingSetReward, reward, left, right, mover, observer,
      moverTriple_ne_observerSingleton, moverTriple_ne_pair]
  · simp [left]

theorem source_payoff_observer
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingTerminalPayoff reward
        (sourceProfile epsilon hepsilon0 hepsilon1) observer = 0 := by
  rw [sourceProfile, twoStageProfile_terminalPayoff]
  · norm_num [quittingSetReward, reward, left, right, mover, observer]
  · simp [left]

theorem marked_payoff_observer
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingTerminalPayoff reward
        (markedProfile epsilon hepsilon0 hepsilon1) observer = epsilon := by
  rw [markedProfile, twoStageProfile_terminalPayoff]
  · simp [quittingSetReward, reward, left, right, mover, observer,
      moverTriple_ne_observerSingleton, moverTriple_ne_pair]
  · simp [left]

theorem incoming_payoff_observer
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingTerminalPayoff reward
        (incomingProfile epsilon hepsilon0 hepsilon1) observer = -epsilon := by
  rw [incomingProfile, twoStageProfile_terminalPayoff]
  · simp [quittingSetReward, reward, left, right, mover, observer,
      observerTriple_ne_observerSingleton, observerTriple_ne_pair,
      observerTriple_ne_moverTriple]
  · simp [left]

theorem earlyRoot_continueMass
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingStationaryContinueMass
        (earlyRoot epsilon hepsilon0 hepsilon1) = epsilon := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [show (Finset.univ : Finset Player) = {left, right, mover, observer} by
    decide]
  simp [earlyRoot, observerEarlyCoin, observer, left, right, mover]

theorem earlyRoot_deletedObserverContinueMass
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingFixedOpponentsContinueMass
        (fun _ => earlyRoot epsilon hepsilon0 hepsilon1) observer 0 = 1 := by
  unfold quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [show (Finset.univ : Finset Player) = {left, right, mover, observer} by
    decide]
  simp [earlyRoot, observer, left, right, mover]

/-- The marked date has joint reach `epsilon`. -/
theorem source_liveMass_one
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingLiveMass reward
        (sourceProfile epsilon hepsilon0 hepsilon1) 1 = epsilon := by
  rw [show (1 : ℕ) = 0 + 1 by omega, quittingLiveMass_succ,
    quittingLiveMass_zero, one_mul]
  change quittingStationaryContinueMass
      (earlyRoot epsilon hepsilon0 hepsilon1) = epsilon
  exact earlyRoot_continueMass epsilon hepsilon0 hepsilon1

/-- Deleting player `3` leaves reach one through the marked prefix. -/
theorem source_observerDeletedReach_one
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward
          (sourceProfile epsilon hepsilon0 hepsilon1)) observer 0 1 = 1 := by
  simp only [quittingOpponentSurvivalWeight, Finset.prod_range_succ,
    Finset.prod_range_zero, Nat.zero_add, one_mul]
  unfold quittingFixedOpponentsContinueMass
  rw [sourceProfile, twoStageProfile,
    quittingProfileLiveRoot_rootThenContinuation_zero]
  exact earlyRoot_deletedObserverContinueMass epsilon hepsilon0 hepsilon1

/-- The terminal carrying the marked pair. -/
def pairTerminal : {coalition : Finset Player // coalition.Nonempty} :=
  ⟨{left, right}, by simp [left]⟩

private theorem purePair_stageCoalitionMass_zero_one :
    quittingStageCoalitionMass reward
        (quittingPureCoalitionOneDateNeverProfile reward {left, right})
        0 pairTerminal = 1 := by
  unfold quittingPureCoalitionOneDateNeverProfile
    quittingOneDateThenNeverProfile
  rw [quittingStageCoalitionMass_rootThenContinuation_zero]
  change quittingRootCoalitionMass
      (quittingPureSetRoot {left, right}) {left, right} = 1
  unfold quittingRootCoalitionMass quittingRootQuitRates coalitionMass
    quittingPureSetRoot quittingSetAction
  rw [show ({left, right} : Finset Player)ᶜ = {mover, observer} by decide]
  simp [PMF.pure_apply, left, right, mover, observer]

private theorem source_pairTerminal_stageMass
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingStageCoalitionMass reward
        (sourceProfile epsilon hepsilon0 hepsilon1) 1 pairTerminal =
      epsilon := by
  rw [sourceProfile, twoStageProfile,
    show (1 : ℕ) = 0 + 1 by omega,
    quittingStageCoalitionMass_rootThenContinuation_succ,
    earlyRoot_continueMass, purePair_stageCoalitionMass_zero_one, mul_one]

private theorem stageCoalitionMass_le_terminalOutcomeMass
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {coalition : Finset Player // coalition.Nonempty}) :
    quittingStageCoalitionMass reward profile time terminal ≤
      quittingTerminalOutcomeMass reward profile (some terminal) := by
  change quittingStageCoalitionMass reward profile time terminal ≤
    quittingAbsorbedMassLimit reward profile terminal
  rw [← tsum_quittingStageCoalitionMass reward profile terminal]
  exact (hasSum_quittingStageCoalitionMass reward profile terminal).summable.le_tsum
    time (fun other _ =>
      quittingStageCoalitionMass_nonneg reward profile other terminal)

/-- The source puts at least `epsilon` terminal mass on the marked pair. -/
theorem source_pairTerminal_mass_lower
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    epsilon ≤ quittingTerminalOutcomeMass reward
        (sourceProfile epsilon hepsilon0 hepsilon1) (some pairTerminal) := by
  calc
    epsilon = quittingStageCoalitionMass reward
        (sourceProfile epsilon hepsilon0 hepsilon1) 1 pairTerminal :=
      (source_pairTerminal_stageMass epsilon hepsilon0 hepsilon1).symm
    _ ≤ quittingTerminalOutcomeMass reward
        (sourceProfile epsilon hepsilon0 hepsilon1) (some pairTerminal) :=
      stageCoalitionMass_le_terminalOutcomeMass
        (sourceProfile epsilon hepsilon0 hepsilon1) 1 pairTerminal

/-- The marked pair has positive terminal mass for every displayed parameter. -/
theorem source_pairTerminal_mass_pos
    (epsilon : ℝ) (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon < 1) :
    0 < quittingTerminalOutcomeMass reward
        (sourceProfile epsilon hepsilon0.le hepsilon1.le)
        (some pairTerminal) := by
  exact hepsilon0.trans_le
    (source_pairTerminal_mass_lower epsilon hepsilon0.le hepsilon1.le)

/-- Changing player `3`'s displayed first-stage hazard back to Continue gives
the canonical one-row padding of the same pure coalition. -/
theorem twoStageProfile_eq_update_padded
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) (coalition : Finset Player) :
    twoStageProfile epsilon hepsilon0 hepsilon1 coalition =
      Function.update
        (oneDateProductPaddedOneDateProfile reward 1
          (quittingPureSetRoot coalition)) observer
        ((twoStageProfile epsilon hepsilon0 hepsilon1 coalition) observer) := by
  funext who time history
  by_cases hwho : who = observer
  · subst who
    rw [Function.update_self]
  · rw [Function.update_of_ne hwho]
    cases time with
    | zero =>
        simp [twoStageProfile, oneDateProductPaddedOneDateProfile,
          quittingAllContinuePrefixIterate,
          quittingRootThenContinuationProfile, earlyRoot, hwho,
          quittingAllContinueRoot]
    | succ time => rfl

theorem observer_cap_eq_padded
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) (coalition : Finset Player) :
    quittingContinuationBestResponseValue reward
        (twoStageProfile epsilon hepsilon0 hepsilon1 coalition) observer =
      quittingContinuationBestResponseValue reward
        (oneDateProductPaddedOneDateProfile reward 1
          (quittingPureSetRoot coalition)) observer := by
  rw [twoStageProfile_eq_update_padded,
    quittingContinuationBestResponseValue_update_self]

private theorem source_quitEndpoint_observer :
    oneDateProductQuitEndpoint reward
        (quittingPureSetRoot {left, right}) observer = -1 := by
  rw [oneDateProductQuitEndpoint_eq,
    quittingRootQuitPayoff_pureSetRoot_eq_insert]
  rw [show insert observer ({left, right} : Finset Player) =
    {left, right, observer} by decide]
  simp [quittingSetReward, reward, left, right, mover, observer,
    observerTriple_ne_observerSingleton, observerTriple_ne_pair,
    observerTriple_ne_moverTriple]

private theorem source_continueEndpoint_observer :
    oneDateProductContinueEndpoint reward
        (quittingPureSetRoot {left, right}) observer = 0 := by
  rw [oneDateProductContinueEndpoint_eq,
    quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
      (0 : Payoff Player) ({left, right} : Finset Player) observer
      (by decide)]
  rw [show ({left, right} : Finset Player).erase observer =
    {left, right} by decide]
  simp [quittingSetReward, reward, left, right, observer,
    pair_ne_observerSingleton]

private theorem source_oppContinue_observer :
    oneDateProductOppContinue
        (quittingPureSetRoot {left, right}) observer = 0 := by
  apply oneDateProductOppContinue_eq_zero_of_sureQuitter
      (quitter := left)
  · decide
  · simp [quittingPureSetRoot, quittingSetAction, left]

private theorem marked_quitEndpoint_observer :
    oneDateProductQuitEndpoint reward
        (quittingPureSetRoot {left, right, mover}) observer = -1 := by
  rw [oneDateProductQuitEndpoint_eq,
    quittingRootQuitPayoff_pureSetRoot_eq_insert]
  rw [show insert observer ({left, right, mover} : Finset Player) =
    Finset.univ by decide]
  have hneObserver : (Finset.univ : Finset Player) ≠ {observer} := by decide
  have hnePair : (Finset.univ : Finset Player) ≠ {left, right} := by decide
  have hneMover : (Finset.univ : Finset Player) ≠
      {left, right, mover} := by decide
  have hneObserverTriple : (Finset.univ : Finset Player) ≠
      {left, right, observer} := by decide
  have hneMoverSolo : (Finset.univ : Finset Player) ≠ {mover} := by decide
  have hneMoverObserver : (Finset.univ : Finset Player) ≠
      {mover, observer} := by decide
  simp [quittingSetReward, reward, hneObserver, hnePair, hneMover,
    hneObserverTriple, hneMoverSolo, hneMoverObserver]

private theorem marked_continueEndpoint_observer :
    oneDateProductContinueEndpoint reward
        (quittingPureSetRoot {left, right, mover}) observer = 1 := by
  rw [oneDateProductContinueEndpoint_eq,
    quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
      (0 : Payoff Player) ({left, right, mover} : Finset Player) observer
      (by decide)]
  rw [show ({left, right, mover} : Finset Player).erase observer =
    {left, right, mover} by decide]
  simp [quittingSetReward, reward, left, right, mover, observer,
    moverTriple_ne_observerSingleton, moverTriple_ne_pair]

private theorem marked_oppContinue_observer :
    oneDateProductOppContinue
        (quittingPureSetRoot {left, right, mover}) observer = 0 := by
  apply oneDateProductOppContinue_eq_zero_of_sureQuitter
      (quitter := left)
  · decide
  · simp [quittingPureSetRoot, quittingSetAction, left]

theorem source_cap_observer
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingContinuationBestResponseValue reward
        (sourceProfile epsilon hepsilon0 hepsilon1) observer = 0 := by
  rw [sourceProfile, observer_cap_eq_padded,
    oneDateProductQuittingContinuationBestResponseValue_paddedOneDateProfile
      reward (by omega : 0 < (1 : ℕ))]
  rw [reward_observer_singleton, source_quitEndpoint_observer,
    source_continueEndpoint_observer, source_oppContinue_observer]
  norm_num

theorem marked_cap_observer
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingContinuationBestResponseValue reward
        (markedProfile epsilon hepsilon0 hepsilon1) observer = 1 := by
  rw [markedProfile, observer_cap_eq_padded,
    oneDateProductQuittingContinuationBestResponseValue_paddedOneDateProfile
      reward (by omega : 0 < (1 : ℕ))]
  rw [reward_observer_singleton, marked_quitEndpoint_observer,
    marked_continueEndpoint_observer, marked_oppContinue_observer]
  norm_num

theorem twoStage_mover_quitNow_payoff
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) (coalition : Finset Player) :
    quittingPureTimeDeviationPayoff reward
        (twoStageProfile epsilon hepsilon0 hepsilon1 coalition)
        mover (some 0) = 1 := by
  rw [quittingPureTimeDeviationPayoff,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
  unfold quittingFixedOpponentsQuitValue
  rw [twoStageProfile, quittingProfileLiveRoot_rootThenContinuation_zero]
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  have h23Pair : ({mover, observer} : Finset Player) ≠
      {left, right} := by decide
  have h23MoverTriple : ({mover, observer} : Finset Player) ≠
      {left, right, mover} := by decide
  have h23ObserverTriple : ({mover, observer} : Finset Player) ≠
      {left, right, observer} := by decide
  have h2Pair : ({mover} : Finset Player) ≠ {left, right} := by decide
  have h2MoverTriple : ({mover} : Finset Player) ≠
      {left, right, mover} := by decide
  have h2ObserverTriple : ({mover} : Finset Player) ≠
      {left, right, observer} := by decide
  simp [earlyRoot, observerEarlyCoin, reward, quittingRootPayoff,
    expect_eq_sum, observer, left, right, mover, h23Pair,
    h23MoverTriple, h23ObserverTriple, h2Pair, h2MoverTriple,
    h2ObserverTriple]

/-- The mover can obtain one by quitting at date zero, and no table entry
exceeds one, so its complete behavioral cap is exactly one. -/
theorem twoStage_cap_mover
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) (coalition : Finset Player) :
    quittingContinuationBestResponseValue reward
        (twoStageProfile epsilon hepsilon0 hepsilon1 coalition) mover = 1 := by
  apply le_antisymm
  · exact (le_abs_self _).trans
      (abs_quittingContinuationBestResponseValue_le reward
        (twoStageProfile epsilon hepsilon0 hepsilon1 coalition) mover
        abs_reward_le_one)
  · rw [← twoStage_mover_quitNow_payoff epsilon hepsilon0 hepsilon1 coalition]
    unfold quittingPureTimeDeviationPayoff
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (twoStageProfile epsilon hepsilon0 hepsilon1 coalition) mover
        (quittingPureTimeBehaviorStrategy reward mover (some 0))

theorem source_cap_mover
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingContinuationBestResponseValue reward
        (sourceProfile epsilon hepsilon0 hepsilon1) mover = 1 := by
  exact twoStage_cap_mover epsilon hepsilon0 hepsilon1 {left, right}

theorem marked_cap_mover
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingContinuationBestResponseValue reward
        (markedProfile epsilon hepsilon0 hepsilon1) mover = 1 := by
  exact twoStage_cap_mover epsilon hepsilon0 hepsilon1 {left, right, mover}

/-- The marked outsider join gains exactly the marked reach `epsilon`. -/
theorem marked_mover_gain
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingTerminalPayoff reward
          (markedProfile epsilon hepsilon0 hepsilon1) mover -
        quittingTerminalPayoff reward
          (sourceProfile epsilon hepsilon0 hepsilon1) mover = epsilon := by
  rw [marked_payoff_mover, source_payoff_mover]
  ring

theorem source_debt_mover
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (sourceProfile epsilon hepsilon0 hepsilon1)) mover = 1 := by
  change quittingContinuationBestResponseValue reward
      (sourceProfile epsilon hepsilon0 hepsilon1) mover -
    quittingTerminalPayoff reward
      (sourceProfile epsilon hepsilon0 hepsilon1) mover = 1
  rw [source_cap_mover,
    source_payoff_mover]
  norm_num

/-- The marked update leaves the mover with the exact premark residual
`1 - epsilon`; the pair passport does not force it to vanish. -/
theorem marked_debt_mover
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (markedProfile epsilon hepsilon0 hepsilon1)) mover = 1 - epsilon := by
  change quittingContinuationBestResponseValue reward
      (markedProfile epsilon hepsilon0 hepsilon1) mover -
    quittingTerminalPayoff reward
      (markedProfile epsilon hepsilon0 hepsilon1) mover = 1 - epsilon
  rw [marked_cap_mover,
    marked_payoff_mover]

theorem marked_debt_mover_pos
    (epsilon : ℝ) (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon < 1) :
    0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (markedProfile epsilon hepsilon0.le hepsilon1.le)) mover := by
  rw [marked_debt_mover]
  linarith

theorem source_debt_eq_markedGain_add_markedDebt
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (sourceProfile epsilon hepsilon0 hepsilon1)) mover =
      (quittingTerminalPayoff reward
          (markedProfile epsilon hepsilon0 hepsilon1) mover -
        quittingTerminalPayoff reward
          (sourceProfile epsilon hepsilon0 hepsilon1) mover) +
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (markedProfile epsilon hepsilon0 hepsilon1)) mover := by
  rw [source_debt_mover, marked_mover_gain, marked_debt_mover]
  ring

theorem marked_debt_observer
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (markedProfile epsilon hepsilon0 hepsilon1)) observer =
      1 - epsilon := by
  change quittingContinuationBestResponseValue reward
      (markedProfile epsilon hepsilon0 hepsilon1) observer -
    quittingTerminalPayoff reward
      (markedProfile epsilon hepsilon0 hepsilon1) observer = 1 - epsilon
  rw [marked_cap_observer,
    marked_payoff_observer]

/-- The nonmover cap changes by one while the marked reach is only
`epsilon`. -/
theorem observer_cap_change_eq_one
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingContinuationBestResponseValue reward
          (markedProfile epsilon hepsilon0 hepsilon1) observer -
        quittingContinuationBestResponseValue reward
          (sourceProfile epsilon hepsilon0 hepsilon1) observer = 1 := by
  rw [marked_cap_observer, source_cap_observer]
  norm_num

/-- The incoming `{0,1,3}` sibling to the source pair gives player `3`
exact gain `epsilon`. -/
theorem incoming_to_source_gain_observer
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    quittingTerminalPayoff reward
          (sourceProfile epsilon hepsilon0 hepsilon1) observer -
        quittingTerminalPayoff reward
          (incomingProfile epsilon hepsilon0 hepsilon1) observer = epsilon := by
  rw [source_payoff_observer, incoming_payoff_observer]
  ring

/-- Immediate pure quitting by player `2`, with every opponent perpetually
continuing. -/
def zeroDebtProfile : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward
    (quittingPureSetRoot ({mover} : Finset Player))

theorem zeroDebtProfile_payoff (who : Player) :
    quittingTerminalPayoff reward zeroDebtProfile who =
      if who = mover then 1 else 0 := by
  rw [zeroDebtProfile, quittingTerminalPayoff_pureSetRoot]
  fin_cases who <;>
    simp (disch := decide) [quittingSetReward, reward,
      mover, observer, left, right, moverSingleton_ne_pair,
      moverSingleton_ne_moverTriple, moverSingleton_ne_observerTriple]

theorem zeroDebtProfile_debt (who : Player) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward zeroDebtProfile) who = 0 := by
  rw [zeroDebtProfile, quittingTerminalSemanticDebt_pureSetRoot_eq]
  fin_cases who <;>
    simp (disch := decide) [quittingSetReward, reward,
      mover, observer, left, right, moverSingleton_ne_pair,
      moverSingleton_ne_moverTriple, moverSingleton_ne_observerTriple,
      leftMover_ne_observerSingleton, leftMover_ne_pair,
      leftMover_ne_moverTriple, leftMover_ne_observerTriple,
      leftMover_ne_moverObserver, rightMover_ne_observerSingleton,
      rightMover_ne_pair, rightMover_ne_moverTriple,
      rightMover_ne_observerTriple, rightMover_ne_moverObserver,
      observerMover_eq_moverObserver, moverObserver_ne_pair,
      moverObserver_ne_moverTriple, moverObserver_ne_observerTriple];
    norm_num

/-- The table is not a positive-gap counterexample: this displayed profile
has payoff and cap `(0,0,1,0)` and total debt zero. -/
theorem zeroDebtProfile_semantics :
    (∀ who, quittingTerminalPayoff reward zeroDebtProfile who =
        if who = mover then 1 else 0) ∧
      (∀ who, quittingContinuationBestResponseValue reward
        zeroDebtProfile who = if who = mover then 1 else 0) ∧
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward zeroDebtProfile) = 0 := by
  constructor
  · exact zeroDebtProfile_payoff
  constructor
  · intro who
    have hdebt := zeroDebtProfile_debt who
    change quittingContinuationBestResponseValue reward zeroDebtProfile who -
        quittingTerminalPayoff reward zeroDebtProfile who = 0 at hdebt
    rw [sub_eq_zero] at hdebt
    rw [hdebt, zeroDebtProfile_payoff]
  · unfold quittingTerminalSemanticDebtSum
    simp [zeroDebtProfile_debt]

/-- Exact finite regression passport for `0 < epsilon < 1`. -/
theorem deletedReach_regression
    (epsilon : ℝ) (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon < 1) :
    quittingLiveMass reward
          (sourceProfile epsilon hepsilon0.le hepsilon1.le) 1 = epsilon ∧
      quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward
            (sourceProfile epsilon hepsilon0.le hepsilon1.le))
          observer 0 1 = 1 ∧
      quittingContinuationBestResponseValue reward
          (sourceProfile epsilon hepsilon0.le hepsilon1.le) mover = 1 ∧
      quittingContinuationBestResponseValue reward
          (markedProfile epsilon hepsilon0.le hepsilon1.le) mover = 1 ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (sourceProfile epsilon hepsilon0.le hepsilon1.le)) mover = 1 ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (markedProfile epsilon hepsilon0.le hepsilon1.le)) mover =
        1 - epsilon ∧
      quittingContinuationBestResponseValue reward
          (sourceProfile epsilon hepsilon0.le hepsilon1.le) observer = 0 ∧
      quittingContinuationBestResponseValue reward
          (markedProfile epsilon hepsilon0.le hepsilon1.le) observer = 1 ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (markedProfile epsilon hepsilon0.le hepsilon1.le)) observer =
        1 - epsilon ∧
      quittingTerminalPayoff reward
          (sourceProfile epsilon hepsilon0.le hepsilon1.le) observer -
        quittingTerminalPayoff reward
          (incomingProfile epsilon hepsilon0.le hepsilon1.le) observer =
        epsilon := by
  exact ⟨source_liveMass_one epsilon hepsilon0.le hepsilon1.le,
    source_observerDeletedReach_one epsilon hepsilon0.le hepsilon1.le,
    source_cap_mover epsilon hepsilon0.le hepsilon1.le,
    marked_cap_mover epsilon hepsilon0.le hepsilon1.le,
    source_debt_mover epsilon hepsilon0.le hepsilon1.le,
    marked_debt_mover epsilon hepsilon0.le hepsilon1.le,
    source_cap_observer epsilon hepsilon0.le hepsilon1.le,
    marked_cap_observer epsilon hepsilon0.le hepsilon1.le,
    marked_debt_observer epsilon hepsilon0.le hepsilon1.le,
    incoming_to_source_gain_observer epsilon hepsilon0.le hepsilon1.le⟩

/-- The observer cap changes by one at arbitrarily small positive marked
reach.  This is the literal finite-family obstruction to controlling the
nonmover cap by a constant multiple of marked reach. -/
theorem exists_arbitrarilySmallMarkedReach_with_unitObserverCapChange
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1),
      0 < epsilon ∧ epsilon < 1 ∧ epsilon < delta ∧
      quittingLiveMass reward
          (sourceProfile epsilon hepsilon0 hepsilon1) 1 = epsilon ∧
      quittingContinuationBestResponseValue reward
          (markedProfile epsilon hepsilon0 hepsilon1) observer -
        quittingContinuationBestResponseValue reward
          (sourceProfile epsilon hepsilon0 hepsilon1) observer = 1 := by
  let epsilon : ℝ := min delta 1 / 2
  have hmin : 0 < min delta 1 := lt_min hdelta zero_lt_one
  have hepsilon0 : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hepsilon1 : epsilon < 1 := by
    dsimp [epsilon]
    nlinarith [min_le_right delta 1]
  have hepsilonDelta : epsilon < delta := by
    dsimp [epsilon]
    nlinarith [min_le_left delta 1]
  refine ⟨epsilon, hepsilon0.le, hepsilon1.le, hepsilon0, hepsilon1,
    hepsilonDelta, ?_, ?_⟩
  · exact source_liveMass_one epsilon hepsilon0.le hepsilon1.le
  · rw [marked_cap_observer epsilon hepsilon0.le hepsilon1.le,
      source_cap_observer epsilon hepsilon0.le hepsilon1.le]
    norm_num

end FinFourPremarkDeletedReachRegression
end GameTheory
