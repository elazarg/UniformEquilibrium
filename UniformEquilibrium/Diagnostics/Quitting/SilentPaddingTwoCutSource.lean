import UniformEquilibrium.Diagnostics.Quitting.SilentPrefixTerminalSemantics
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Quitting.Cycles.CyclicGreenDebt
import UniformEquilibrium.Quitting.Stationary.ReturnedBlockTangentObstruction

/-!
# Silent-padding source for a positive-hazard two-cut block

A positive coordinate of a supplied terminal law has a finite window carrying
any smaller positive mass.  Prefixing the source's canonical live-root word
by one all-Continue row turns that window into a two-cut block with entry
reach one.  The construction is spatial: the artificial mark is only an
ordering witness and is not a strategic event or a chronological atom.

The source profile, positive law coordinate, and positive global carrier
minimum are supplied.  No source sequence, return, renewal, chronology, Nash
profile, or uniform-equilibrium payoff is constructed here.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem quittingJointContinueMass_eq_stationaryContinueMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingJointContinueMass reward profile time =
      quittingStationaryContinueMass
        (quittingProfileLiveRoot reward profile time) := by
  rw [quittingJointContinueMass_eq_product,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  rfl

/-- One date's coalition mass is bounded by total marginal quit probability. -/
theorem quittingStageCoalitionMass_le_sum_liveRootQuitRates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward profile time terminal ≤
      ∑ who, quittingRootQuitRates
        (quittingProfileLiveRoot reward profile time) who := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  have hcoalition := quittingRootCoalitionMass_nonneg
    (quittingProfileLiveRoot reward profile time) terminal.val
  have hlive := quittingLiveMass_le_one reward profile time
  have habsorb := quittingRootCoalitionMass_le_absorptionMass_of_nonempty
    (quittingProfileLiveRoot reward profile time) terminal.val
    terminal.property
  have hrates := quittingRootAbsorptionMass_le_sum_quitRates
    (quittingProfileLiveRoot reward profile time)
  nlinarith

/-- A law coordinate above a threshold has a positive finite window above it. -/
theorem exists_positive_finite_stageCoalitionMass_window_gt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {threshold : ℝ}
    (hlaw : threshold < quittingAbsorbedMassLimit reward profile terminal) :
    ∃ window : ℕ, 0 < window ∧
      threshold < ∑ time ∈ Finset.range window,
        quittingStageCoalitionMass reward profile time terminal := by
  have hsum := hasSum_quittingStageCoalitionMass reward profile terminal
  obtain ⟨cutoff, hcutoff⟩ :=
    (hsum.tendsto_sum_nat.eventually_const_lt hlaw).exists
  refine ⟨cutoff + 1, Nat.succ_pos cutoff, ?_⟩
  have hlast := quittingStageCoalitionMass_nonneg reward profile cutoff terminal
  rw [Finset.sum_range_succ]
  linarith

/-- The same finite law window has at least that much total marginal hazard. -/
theorem finite_stageCoalitionMass_window_lt_sum_liveRootQuitRates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {threshold : ℝ} (window : ℕ)
    (hwindow : threshold < ∑ time ∈ Finset.range window,
      quittingStageCoalitionMass reward profile time terminal) :
    threshold < ∑ time ∈ Finset.range window,
      ∑ who, quittingRootQuitRates
        (quittingProfileLiveRoot reward profile time) who := by
  have hdominate := Finset.sum_le_sum
    (f := fun time => quittingStageCoalitionMass reward profile time terminal)
    (g := fun time => ∑ who, quittingRootQuitRates
      (quittingProfileLiveRoot reward profile time) who)
    (s := Finset.range window)
    (fun time _ => quittingStageCoalitionMass_le_sum_liveRootQuitRates
      reward profile time terminal)
  linarith

/-- Select a positive finite window with both law mass and hazard above the threshold. -/
theorem exists_positive_finite_lawMass_and_hazard_window_gt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {threshold : ℝ}
    (hlaw : threshold < quittingAbsorbedMassLimit reward profile terminal) :
    ∃ window : ℕ, 0 < window ∧
      threshold < ∑ time ∈ Finset.range window,
        quittingStageCoalitionMass reward profile time terminal ∧
      threshold < ∑ time ∈ Finset.range window,
        ∑ who, quittingRootQuitRates
          (quittingProfileLiveRoot reward profile time) who := by
  obtain ⟨window, hpos, hmass⟩ :=
    exists_positive_finite_stageCoalitionMass_window_gt
      reward profile terminal hlaw
  exact ⟨window, hpos, hmass,
    finite_stageCoalitionMass_window_lt_sum_liveRootQuitRates
      reward profile terminal window hmass⟩

/-- Silent-prefix realization of a supplied positive-hazard window. -/
def quittingSilentPaddingTwoCutBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {threshold : ℝ} (hthreshold : 0 < threshold)
    (window : ℕ) (hwindow : 0 < window)
    (hhazard : threshold < ∑ time ∈ Finset.range window,
      ∑ who, quittingRootQuitRates
        (quittingProfileLiveRoot reward profile time) who)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    QuittingUniformlyReachedPostMarkTwoCutBlock reward where
  roots := quittingSilentPrefixRoots (quittingProfileLiveRoot reward profile)
  entryCut := 1
  exitCut := window + 1
  entryCut_lt_exitCut := Nat.succ_lt_succ hwindow
  minimum := minimum
  minimum_mem := hminimumMem
  minimum_le := hminimumLe
  minimum_pos := hminimumPos
  markedRow := 0
  markedRow_lt_entryCut := Nat.zero_lt_one
  hazardFloor := threshold
  hazardFloor_pos := hthreshold
  totalMarginalHazard_ge := by
    show threshold ≤ ∑ offset ∈ Finset.range (window + 1 - 1),
      ∑ who, ((quittingSilentPrefixRoots
        (quittingProfileLiveRoot reward profile) (1 + offset)) who true).toReal
    have hshift : ∑ offset ∈ Finset.range (window + 1 - 1),
          ∑ who, ((quittingSilentPrefixRoots
            (quittingProfileLiveRoot reward profile) (1 + offset))
              who true).toReal =
        ∑ time ∈ Finset.range window,
          ∑ who, quittingRootQuitRates
            (quittingProfileLiveRoot reward profile time) who := by
      simp only [Nat.add_sub_cancel]
      refine Finset.sum_congr rfl fun offset _ => ?_
      rw [Nat.add_comm 1 offset]
      rfl
    rw [hshift]
    exact hhazard.le
  reachFloor := 1
  reachFloor_pos := one_pos
  entryReach_ge := by
    show (1 : ℝ) ≤ quittingJointSurvivalWeight
      (quittingSilentPrefixRoots
        (quittingProfileLiveRoot reward profile)) 0 1
    rw [quittingJointSurvivalWeight_succ]
    simp only [quittingJointSurvivalWeight_zero_fuel, zero_add,
      quittingSilentPrefixRoots_zero,
      quittingStationaryContinueMass_allContinueRoot, one_mul]
    exact le_rfl

section Fields

variable (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
  (profile : (quittingGame reward).BehaviorProfile)
  {threshold : ℝ} (hthreshold : 0 < threshold)
  (window : ℕ) (hwindow : 0 < window)
  (hhazard : threshold < ∑ time ∈ Finset.range window,
    ∑ who, quittingRootQuitRates
      (quittingProfileLiveRoot reward profile time) who)
  (minimum : QuittingTerminalSemanticPair ι)
  (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
  (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate)
  (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)

@[simp] theorem quittingSilentPaddingTwoCutBlock_roots :
    (quittingSilentPaddingTwoCutBlock reward profile hthreshold window hwindow
      hhazard minimum hminimumMem hminimumLe hminimumPos).roots =
      quittingSilentPrefixRoots (quittingProfileLiveRoot reward profile) := rfl

@[simp] theorem quittingSilentPaddingTwoCutBlock_markedRow :
    (quittingSilentPaddingTwoCutBlock reward profile hthreshold window hwindow
      hhazard minimum hminimumMem hminimumLe hminimumPos).markedRow = 0 := rfl

@[simp] theorem quittingSilentPaddingTwoCutBlock_entryCut :
    (quittingSilentPaddingTwoCutBlock reward profile hthreshold window hwindow
      hhazard minimum hminimumMem hminimumLe hminimumPos).entryCut = 1 := rfl

@[simp] theorem quittingSilentPaddingTwoCutBlock_exitCut :
    (quittingSilentPaddingTwoCutBlock reward profile hthreshold window hwindow
      hhazard minimum hminimumMem hminimumLe hminimumPos).exitCut = window + 1 := rfl

@[simp] theorem quittingSilentPaddingTwoCutBlock_hazardFloor :
    (quittingSilentPaddingTwoCutBlock reward profile hthreshold window hwindow
      hhazard minimum hminimumMem hminimumLe hminimumPos).hazardFloor =
      threshold := rfl

@[simp] theorem quittingSilentPaddingTwoCutBlock_reachFloor :
    (quittingSilentPaddingTwoCutBlock reward profile hthreshold window hwindow
      hhazard minimum hminimumMem hminimumLe hminimumPos).reachFloor = 1 := rfl

@[simp] theorem quittingSilentPaddingTwoCutBlock_minimum :
    (quittingSilentPaddingTwoCutBlock reward profile hthreshold window hwindow
      hhazard minimum hminimumMem hminimumLe hminimumPos).minimum = minimum := rfl

end Fields

/-- Construct the block directly from a positive coordinate of the source law. -/
theorem exists_quittingSilentPaddingTwoCutBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    {threshold : ℝ} (hthreshold : 0 < threshold)
    (hlaw : threshold < quittingAbsorbedMassLimit reward profile terminal)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ window : ℕ, 0 < window ∧
      ∃ block : QuittingUniformlyReachedPostMarkTwoCutBlock reward,
        block.roots = quittingSilentPrefixRoots
            (quittingProfileLiveRoot reward profile) ∧
          block.markedRow = 0 ∧ block.entryCut = 1 ∧
          block.exitCut = window + 1 ∧ block.hazardFloor = threshold ∧
          block.reachFloor = 1 ∧ block.minimum = minimum := by
  obtain ⟨window, hpos, -, hhazard⟩ :=
    exists_positive_finite_lawMass_and_hazard_window_gt
      reward profile terminal hlaw
  exact ⟨window, hpos,
    quittingSilentPaddingTwoCutBlock reward profile hthreshold window hpos
      hhazard minimum hminimumMem hminimumLe hminimumPos,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [DecidableEq ι] in
theorem quittingLiveMass_rootSequence_silentPrefix_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward
        (quittingRootSequenceProfile reward
          (quittingSilentPrefixRoots
            (quittingProfileLiveRoot reward profile)) 0) (time + 1) =
      quittingLiveMass reward profile time := by
  induction time with
  | zero =>
      rw [quittingLiveMass_succ,
        quittingJointContinueMass_eq_stationaryContinueMass,
        quittingProfileLiveRoot_quittingRootSequenceProfile_zero,
        quittingSilentPrefixRoots_zero,
        quittingStationaryContinueMass_allContinueRoot]
      simp
  | succ time ih =>
      rw [quittingLiveMass_succ,
        quittingJointContinueMass_eq_stationaryContinueMass,
        quittingProfileLiveRoot_quittingRootSequenceProfile_zero,
        quittingSilentPrefixRoots_succ, ih, quittingLiveMass_succ,
        quittingJointContinueMass_eq_stationaryContinueMass]

/-- The silent row carries no terminal coalition mass. -/
theorem quittingStageCoalitionMass_rootSequence_silentPrefix_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingRootSequenceProfile reward
          (quittingSilentPrefixRoots
            (quittingProfileLiveRoot reward profile)) 0) 0 terminal = 0 := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero,
    quittingSilentPrefixRoots_zero]
  have hnonneg := quittingRootCoalitionMass_nonneg
    (quittingAllContinueRoot : ι → PMF Bool) terminal.val
  have hle := quittingRootCoalitionMass_le_absorptionMass_of_nonempty
    (quittingAllContinueRoot : ι → PMF Bool) terminal.val terminal.property
  rw [quittingRootAbsorptionMass_allContinueRoot] at hle
  have hzero : quittingRootCoalitionMass
      (quittingAllContinueRoot : ι → PMF Bool) terminal.val = 0 :=
    le_antisymm hle hnonneg
  rw [hzero, mul_zero]

/-- Later coalition masses shift by one under the silent prefix. -/
theorem quittingStageCoalitionMass_rootSequence_silentPrefix_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) (time : ℕ) :
    quittingStageCoalitionMass reward
        (quittingRootSequenceProfile reward
          (quittingSilentPrefixRoots
            (quittingProfileLiveRoot reward profile)) 0) (time + 1) terminal =
      quittingStageCoalitionMass reward profile time terminal := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero,
    quittingSilentPrefixRoots_succ,
    quittingLiveMass_rootSequence_silentPrefix_succ]

/-- The silent prefix preserves every coordinate of the terminal law. -/
theorem quittingAbsorbedMassLimit_rootSequence_silentPrefix_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMassLimit reward
        (quittingRootSequenceProfile reward
          (quittingSilentPrefixRoots
            (quittingProfileLiveRoot reward profile)) 0) terminal =
      quittingAbsorbedMassLimit reward profile terminal := by
  have hpadded := hasSum_quittingStageCoalitionMass reward
    (quittingRootSequenceProfile reward
      (quittingSilentPrefixRoots (quittingProfileLiveRoot reward profile)) 0)
    terminal
  have hsplit := hpadded.summable.tsum_eq_zero_add
  rw [hpadded.tsum_eq,
    quittingStageCoalitionMass_rootSequence_silentPrefix_zero] at hsplit
  rw [hsplit, zero_add]
  have hshift : ∀ time, quittingStageCoalitionMass reward
      (quittingRootSequenceProfile reward
        (quittingSilentPrefixRoots
          (quittingProfileLiveRoot reward profile)) 0) (time + 1) terminal =
    quittingStageCoalitionMass reward profile time terminal :=
    quittingStageCoalitionMass_rootSequence_silentPrefix_succ
      reward profile terminal
  simp only [hshift]
  exact tsum_quittingStageCoalitionMass reward profile terminal

/-- The silent prefix preserves the complete terminal outcome law, including
the Never coordinate. -/
theorem quittingTerminalOutcomeMass_rootSequence_silentPrefix_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass reward
        (quittingRootSequenceProfile reward
          (quittingSilentPrefixRoots
            (quittingProfileLiveRoot reward profile)) 0) outcome =
      quittingTerminalOutcomeMass reward profile outcome := by
  cases outcome with
  | some terminal =>
      exact quittingAbsorbedMassLimit_rootSequence_silentPrefix_eq
        reward profile terminal
  | none =>
      have hpadded := (quittingTerminalOutcomeMass_mem_stdSimplex reward
        (quittingRootSequenceProfile reward
          (quittingSilentPrefixRoots
            (quittingProfileLiveRoot reward profile)) 0)).2
      have hsource :=
        (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).2
      rw [Fintype.sum_option] at hpadded hsource
      have hfinite :
          (∑ terminal, quittingTerminalOutcomeMass reward
            (quittingRootSequenceProfile reward
              (quittingSilentPrefixRoots
                (quittingProfileLiveRoot reward profile)) 0)
              (some terminal)) =
            ∑ terminal, quittingTerminalOutcomeMass reward profile
              (some terminal) := by
        apply Finset.sum_congr rfl
        intro terminal _
        exact quittingAbsorbedMassLimit_rootSequence_silentPrefix_eq
          reward profile terminal
      linarith

/-- Singleton rewards lie a full minimum-debt margin below minimum caps. -/
theorem singletonReward_add_minimumDebtSum_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) (who : ι) :
    reward (quittingSingletonTerminal who) who +
        quittingTerminalSemanticDebtSum minimum ≤ minimum.2 who := by
  have hmargin := minimumTerminalSemantic_singletonMargin
    (reward := reward) minimum hminimumMem hminimumLe hminimumPos who
  linarith

/-- A profile sufficiently close in caps to the minimum clears singleton rewards. -/
theorem singletonReward_lt_terminalCap_of_near_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hnear : ∀ who, minimum.2 who - quittingTerminalSemanticDebtSum minimum <
      (quittingTerminalSemanticPair reward profile).2 who) (who : ι) :
    reward (quittingSingletonTerminal who) who <
      (quittingTerminalSemanticPair reward profile).2 who := by
  have hmargin := singletonReward_add_minimumDebtSum_le reward minimum
    hminimumMem hminimumLe hminimumPos who
  have hclose := hnear who
  linarith

/-- Under the minimum margin, the silent parent has the source semantic pair. -/
theorem quittingRootSequenceTerminalSemanticPairAt_silentPrefix_zero_eq_of_near_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hnear : ∀ who, minimum.2 who - quittingTerminalSemanticDebtSum minimum <
      (quittingTerminalSemanticPair reward profile).2 who) :
    quittingRootSequenceTerminalSemanticPairAt reward
        (quittingSilentPrefixRoots (quittingProfileLiveRoot reward profile)) 0 =
      quittingTerminalSemanticPair reward profile := by
  rw [quittingRootSequenceTerminalSemanticPairAt_silentPrefix_zero]
  apply Prod.ext
  · rfl
  · funext who
    exact max_eq_right (singletonReward_lt_terminalCap_of_near_minimum
      reward profile minimum hminimumMem hminimumLe hminimumPos hnear who).le

section BlockIdentities

variable (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
  (profile : (quittingGame reward).BehaviorProfile)
  {threshold : ℝ} (hthreshold : 0 < threshold)
  (window : ℕ) (hwindow : 0 < window)
  (hhazard : threshold < ∑ time ∈ Finset.range window,
    ∑ who, quittingRootQuitRates
      (quittingProfileLiveRoot reward profile time) who)
  (minimum : QuittingTerminalSemanticPair ι)
  (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
  (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate)
  (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)

/-- The block entry is exactly the source's complete semantic pair. -/
theorem quittingSilentPaddingTwoCutBlock_entryPair_eq :
    (quittingSilentPaddingTwoCutBlock reward profile hthreshold window hwindow
      hhazard minimum hminimumMem hminimumLe hminimumPos).entryPair =
      quittingTerminalSemanticPair reward profile :=
  quittingRootSequenceTerminalSemanticPairAt_silentPrefix_one reward profile

/-- The silent row makes entry reach exactly one, not merely at least the
stored reach floor. -/
theorem quittingSilentPaddingTwoCutBlock_entryReach_eq_one :
    quittingJointSurvivalWeight
        (quittingSilentPaddingTwoCutBlock reward profile hthreshold window
          hwindow hhazard minimum hminimumMem hminimumLe hminimumPos).roots
        0
        (quittingSilentPaddingTwoCutBlock reward profile hthreshold window
          hwindow hhazard minimum hminimumMem hminimumLe hminimumPos).entryCut =
      1 := by
  change quittingJointSurvivalWeight
      (quittingSilentPrefixRoots (quittingProfileLiveRoot reward profile))
      0 1 = 1
  rw [quittingJointSurvivalWeight_succ]
  simp only [quittingJointSurvivalWeight_zero_fuel, zero_add,
    quittingSilentPrefixRoots_zero,
    quittingStationaryContinueMass_allContinueRoot, one_mul]

/-- The block exit is exactly the source canonical suffix at the window end. -/
theorem quittingSilentPaddingTwoCutBlock_exitPair_eq :
    (quittingSilentPaddingTwoCutBlock reward profile hthreshold window hwindow
      hhazard minimum hminimumMem hminimumLe hminimumPos).exitPair =
      quittingRootSequenceTerminalSemanticPairAt reward
        (quittingProfileLiveRoot reward profile) window :=
  quittingRootSequenceTerminalSemanticPairAt_silentPrefix_succ reward
    (quittingProfileLiveRoot reward profile) window

/-- The block entry profile is the source's canonical live-root profile. -/
theorem quittingSilentPaddingTwoCutBlock_entryProfile_eq :
    (quittingSilentPaddingTwoCutBlock reward profile hthreshold window hwindow
      hhazard minimum hminimumMem hminimumLe hminimumPos).entryProfile =
      quittingRootSequenceProfile reward
        (quittingProfileLiveRoot reward profile) 0 :=
  quittingRootSequenceProfile_silentPrefix_succ reward
    (quittingProfileLiveRoot reward profile) 0

/-- The block parent has exactly the source's terminal payoff. -/
theorem quittingSilentPaddingTwoCutBlock_parentPayoff_eq (who : ι) :
    quittingTerminalPayoff reward
        (quittingSilentPaddingTwoCutBlock reward profile hthreshold window
          hwindow hhazard minimum hminimumMem hminimumLe hminimumPos).parentProfile
        who =
      quittingTerminalPayoff reward profile who :=
  quittingTerminalPayoff_rootSequence_silentPrefix_eq reward profile who

/-- The near-minimum margin makes the block parent's full pair equal the source pair. -/
theorem quittingSilentPaddingTwoCutBlock_parentPair_eq_of_near_minimum
    (hnear : ∀ who, minimum.2 who - quittingTerminalSemanticDebtSum minimum <
      (quittingTerminalSemanticPair reward profile).2 who) :
    quittingTerminalSemanticPair reward
        (quittingSilentPaddingTwoCutBlock reward profile hthreshold window
          hwindow hhazard minimum hminimumMem hminimumLe hminimumPos).parentProfile =
      quittingTerminalSemanticPair reward profile :=
  quittingRootSequenceTerminalSemanticPairAt_silentPrefix_zero_eq_of_near_minimum
    reward profile minimum hminimumMem hminimumLe hminimumPos hnear

/-- Every terminal-law coordinate of the block parent equals the source coordinate. -/
theorem quittingSilentPaddingTwoCutBlock_parentLaw_eq
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMassLimit reward
        (quittingSilentPaddingTwoCutBlock reward profile hthreshold window
          hwindow hhazard minimum hminimumMem hminimumLe hminimumPos).parentProfile
        terminal =
      quittingAbsorbedMassLimit reward profile terminal :=
  quittingAbsorbedMassLimit_rootSequence_silentPrefix_eq reward profile terminal

/-- The block parent preserves the complete source law, including Never. -/
theorem quittingSilentPaddingTwoCutBlock_parentOutcomeLaw_eq
    (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass reward
        (quittingSilentPaddingTwoCutBlock reward profile hthreshold window
          hwindow hhazard minimum hminimumMem hminimumLe hminimumPos).parentProfile
        outcome =
      quittingTerminalOutcomeMass reward profile outcome :=
  quittingTerminalOutcomeMass_rootSequence_silentPrefix_eq
    reward profile outcome

end BlockIdentities

/--
An actual Fin4 source profile with a positive law atom yields a silent-padded
two-cut block, exact source semantic and law identities, and the checked
off-minimum-or-paid-splice alternative.  The source profile and atom are
supplied; this theorem does not produce them.
-/
theorem exists_finFour_silentPaddingTwoCutBlock_with_paidSpliceAlternative
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset (Fin 4) // S.Nonempty})
    {threshold : ℝ} (hthreshold : 0 < threshold)
    (hlaw : threshold < quittingAbsorbedMassLimit reward profile terminal)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hnear : ∀ who, minimum.2 who - quittingTerminalSemanticDebtSum minimum <
      (quittingTerminalSemanticPair reward profile).2 who) :
    ∃ window : ℕ, 0 < window ∧
      threshold < ∑ time ∈ Finset.range window,
        quittingStageCoalitionMass reward profile time terminal ∧
      ∃ block : QuittingUniformlyReachedPostMarkTwoCutBlock reward,
        block.roots = quittingSilentPrefixRoots
            (quittingProfileLiveRoot reward profile) ∧
          block.markedRow = 0 ∧ block.entryCut = 1 ∧
          block.exitCut = window + 1 ∧ block.hazardFloor = threshold ∧
          block.reachFloor = 1 ∧
          quittingJointSurvivalWeight block.roots 0 block.entryCut = 1 ∧
          block.minimum = minimum ∧
          block.entryPair = quittingTerminalSemanticPair reward profile ∧
          block.exitPair = quittingRootSequenceTerminalSemanticPairAt reward
            (quittingProfileLiveRoot reward profile) window ∧
          quittingTerminalSemanticPair reward block.parentProfile =
            quittingTerminalSemanticPair reward profile ∧
          (∀ terminal', quittingAbsorbedMassLimit reward block.parentProfile terminal' =
            quittingAbsorbedMassLimit reward profile terminal') ∧
          (∀ outcome, quittingTerminalOutcomeMass reward block.parentProfile outcome =
            quittingTerminalOutcomeMass reward profile outcome) ∧
          (quittingTerminalSemanticDebtSum block.exitPair ≥
              quittingTerminalSemanticDebtSum block.minimum +
                (Real.exp block.hazardFloor - 1) / 2 *
                  quittingTerminalSemanticDebtSum block.minimum ∨
            ∃ payer : Fin 4,
              ∃ deviation : (quittingGame reward).BehaviorStrategy payer,
                quittingTerminalPayoff reward
                    (Function.update block.entryProfile payer deviation) payer -
                    quittingTerminalPayoff reward block.entryProfile payer >
                  block.coerciveConstant / 16 ∧
                quittingTerminalSemanticDebt
                    (quittingTerminalSemanticPair reward
                      (Function.update block.entryProfile payer deviation)) payer ≤
                  block.coerciveConstant / 16 ∧
                quittingTerminalPayoff reward
                    (Function.update block.entryProfile payer deviation) payer =
                  quittingTerminalPayoff reward
                    (Function.update profile payer deviation) payer ∧
                quittingTerminalSemanticPair reward
                    (Function.update block.entryProfile payer deviation) =
                  quittingTerminalSemanticPair reward
                    (Function.update profile payer deviation) ∧
                quittingTerminalSemanticDebt
                    (quittingTerminalSemanticPair reward
                      (Function.update block.entryProfile payer deviation)) payer =
                  quittingTerminalSemanticDebt
                    (quittingTerminalSemanticPair reward
                      (Function.update profile payer deviation)) payer ∧
                block.paidSpliceProfile payer deviation =
                  Function.update block.parentProfile payer
                    (block.paidSpliceDeviation payer deviation) ∧
                quittingTerminalPayoff reward
                      (block.paidSpliceProfile payer deviation) payer -
                    quittingTerminalPayoff reward block.parentProfile payer >
                  block.coerciveConstant / 16 ∧
                quittingTerminalSemanticDebt
                      (quittingTerminalSemanticPair reward profile) payer -
                    quittingTerminalSemanticDebt
                      (quittingTerminalSemanticPair reward
                        (block.paidSpliceProfile payer deviation)) payer =
                  quittingTerminalPayoff reward
                      (block.paidSpliceProfile payer deviation) payer -
                    quittingTerminalPayoff reward profile payer ∧
                quittingProfileLiveRoot reward
                    (block.paidSpliceProfile payer deviation) 0 =
                  (quittingAllContinueRoot : Fin 4 → PMF Bool)) := by
  obtain ⟨window, hwindow, hmass, hhazard⟩ :=
    exists_positive_finite_lawMass_and_hazard_window_gt
      reward profile terminal hlaw
  let block := quittingSilentPaddingTwoCutBlock reward profile hthreshold window
    hwindow hhazard minimum hminimumMem hminimumLe hminimumPos
  have hentry : block.entryPair = quittingTerminalSemanticPair reward profile :=
    quittingSilentPaddingTwoCutBlock_entryPair_eq reward profile hthreshold window
      hwindow hhazard minimum hminimumMem hminimumLe hminimumPos
  have hexit : block.exitPair =
      quittingRootSequenceTerminalSemanticPairAt reward
        (quittingProfileLiveRoot reward profile) window :=
    quittingSilentPaddingTwoCutBlock_exitPair_eq reward profile hthreshold window
      hwindow hhazard minimum hminimumMem hminimumLe hminimumPos
  have hparent : quittingTerminalSemanticPair reward block.parentProfile =
      quittingTerminalSemanticPair reward profile :=
    quittingSilentPaddingTwoCutBlock_parentPair_eq_of_near_minimum reward profile
      hthreshold window hwindow hhazard minimum hminimumMem hminimumLe
      hminimumPos hnear
  have hlawExact : ∀ terminal',
      quittingAbsorbedMassLimit reward block.parentProfile terminal' =
        quittingAbsorbedMassLimit reward profile terminal' := fun terminal' =>
    quittingSilentPaddingTwoCutBlock_parentLaw_eq reward profile hthreshold window
      hwindow hhazard minimum hminimumMem hminimumLe hminimumPos terminal'
  have hreachExact : quittingJointSurvivalWeight block.roots 0 block.entryCut = 1 :=
    quittingSilentPaddingTwoCutBlock_entryReach_eq_one reward profile hthreshold
      window hwindow hhazard minimum hminimumMem hminimumLe hminimumPos
  have houtcomeLawExact : ∀ outcome,
      quittingTerminalOutcomeMass reward block.parentProfile outcome =
        quittingTerminalOutcomeMass reward profile outcome := fun outcome =>
    quittingSilentPaddingTwoCutBlock_parentOutcomeLaw_eq reward profile
      hthreshold window hwindow hhazard minimum hminimumMem hminimumLe
      hminimumPos outcome
  refine ⟨window, hwindow, hmass, block, rfl, rfl, rfl, rfl, rfl, rfl,
    hreachExact, rfl, hentry, hexit, hparent, hlawExact, houtcomeLawExact, ?_⟩
  rcases block.finFour_offMinimum_or_exists_paidSplice with
    hoff | ⟨payer, deviation, hgain, hdebt, hupdate, hparentGain,
      hparentDebt, hliteral⟩
  · exact Or.inl hoff
  · have hreach : block.reachFloor = 1 := rfl
    rw [hreach, one_mul] at hparentGain
    change quittingTerminalPayoff reward
          (block.paidSpliceProfile payer deviation) payer -
        quittingTerminalPayoff reward block.parentProfile payer >
          block.coerciveConstant / 16 at hparentGain
    change quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward block.parentProfile) payer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (block.paidSpliceProfile payer deviation)) payer =
        quittingTerminalPayoff reward
            (block.paidSpliceProfile payer deviation) payer -
          quittingTerminalPayoff reward block.parentProfile payer at hparentDebt
    have hsourcePayoff : quittingTerminalPayoff reward block.parentProfile payer =
        quittingTerminalPayoff reward profile payer :=
      quittingSilentPaddingTwoCutBlock_parentPayoff_eq reward profile
        hthreshold window hwindow hhazard minimum hminimumMem hminimumLe
        hminimumPos payer
    have hentryUpdatePayoff : quittingTerminalPayoff reward
          (Function.update block.entryProfile payer deviation) payer =
        quittingTerminalPayoff reward
          (Function.update profile payer deviation) payer := by
      rw [quittingSilentPaddingTwoCutBlock_entryProfile_eq]
      exact
        quittingTerminalPayoff_update_rootSequenceProfile_profileLiveRoot_eq
          reward profile payer payer deviation
    have hentryUpdatePair : quittingTerminalSemanticPair reward
          (Function.update block.entryProfile payer deviation) =
        quittingTerminalSemanticPair reward
          (Function.update profile payer deviation) := by
      rw [quittingSilentPaddingTwoCutBlock_entryProfile_eq]
      exact
        quittingTerminalSemanticPair_update_rootSequenceProfile_profileLiveRoot_eq
          reward profile payer deviation
    have hentryUpdateDebt : quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update block.entryProfile payer deviation)) payer =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile payer deviation)) payer := by
      rw [hentryUpdatePair]
    refine Or.inr ⟨payer, deviation, hgain, hdebt, hentryUpdatePayoff,
      hentryUpdatePair, hentryUpdateDebt, hupdate, hparentGain, ?_, ?_⟩
    · rw [hparent, hsourcePayoff] at hparentDebt
      exact hparentDebt
    · exact hliteral 0 Nat.zero_lt_one

end GameTheory
