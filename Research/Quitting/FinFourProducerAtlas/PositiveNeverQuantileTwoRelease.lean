import Research.Quitting.EscapeAwareQuantileClockHierarchy
import Research.Quitting.SameStageEndpointMonodromy
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.FiniteClockFreshRelease
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashChronology
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalization
import UniformEquilibrium.Quitting.Paths.BehaviorSupportedPureTimeReplacement

/-!
# Positive-Never quantile compression with two fresh releases

This is a compiler for one supplied executable profile with positive joint
Never mass and two supplied terminal-table gains.  At every cofinal quantile
level it reconstructs a finite stopping calendar, chooses an exact cap--Nash
word, and releases two distinct players at the first fresh row.  The resulting
profiles are horizontal behavioral replacements; they are not temporal Nash
rows and no source producer is constructed here.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability QuittingSureSetOwnerRepair
open scoped Topology

/-- Supplied data for two profitable releases from one positive-Never profile. -/
structure FinFourPositiveNeverReleaseInput
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) where
  profile : (quittingGame reward).BehaviorProfile
  owner : Fin 4
  outsider : Fin 4
  outsider_ne_owner : outsider ≠ owner
  neverProduct_pos : 0 < ∏ who,
    (quittingBehaviorStoppingLaw reward (profile who) none).toReal
  ownerSingletonGain : ℝ
  ownerSingletonGain_pos : 0 < ownerSingletonGain
  ownerSingletonGain_le_reward :
    ownerSingletonGain ≤ reward (quittingSingletonTerminal owner) owner
  outsiderPairGain : ℝ
  outsiderPairGain_pos : 0 < outsiderPairGain
  outsiderPairGain_le_rewardGap :
    outsiderPairGain ≤
      reward ⟨{owner, outsider}, by simp⟩ outsider -
        reward (quittingSingletonTerminal owner) outsider
  minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) ≤
      quittingTerminalSemanticDebtSum candidate
  debt_eq_inf : quittingTerminalDebtSum reward profile =
    quittingTerminalDebtSumInf reward
  debtInf_pos : 0 < quittingTerminalDebtSumInf reward

namespace FinFourPositiveNeverReleaseInput

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}

/-- The exact product of the supplied marginal Never masses. -/
def neverProduct (data : FinFourPositiveNeverReleaseInput reward) : ℝ :=
  ∏ who, (quittingBehaviorStoppingLaw reward (data.profile who) none).toReal

/-- The cofinal compressed stopping laws. -/
def compressedLaws (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    Fin 4 → PMF (Option ℕ) :=
  quittingQuantileClockCompressedLaws reward data.profile (rank + 1)

/-- The cofinal finite-clock reconstruction. -/
def compressedProfile
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingQuantileClockCompressedProfile reward data.profile (rank + 1)

/-- A clock bound strictly beyond every finite compressed clock. -/
def clockBound (_data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) : ℕ :=
  quantileClockSupport (Fin 4) (rank + 1)

/-- One exact cap--Nash word of increasing length against the literal
compressed suffix. -/
def roots (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    List (Fin 4 → PMF Bool) :=
  Classical.choose
    (exists_quittingCapNashRootStack reward (data.compressedProfile rank) (rank + 1))

theorem roots_length (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    (data.roots rank).length = rank + 1 :=
  (Classical.choose_spec
    (exists_quittingCapNashRootStack reward (data.compressedProfile rank) (rank + 1))).1

theorem roots_nash (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    IsQuittingCapNashRootStack reward (data.roots rank) (data.compressedProfile rank) :=
  (Classical.choose_spec
    (exists_quittingCapNashRootStack reward (data.compressedProfile rank) (rank + 1))).2

/-- The literal fresh-row two-release datum at one compressed level. -/
def release (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    QuittingPositiveNeverTwoRelease reward :=
  quittingPositiveNeverTwoRelease_of_isFiniteClock
    (data.compressedLaws rank) (data.clockBound rank)
    (fun who => quittingQuantileClockCompressedLaws_isFiniteClock
      reward data.profile (rank + 1) who)
    data.owner data.outsider data.outsider_ne_owner

@[simp]
theorem release_sourceProfile
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    (data.release rank).sourceProfile = data.compressedProfile rank := rfl

@[simp]
theorem release_mark (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    (data.release rank).mark = data.clockBound rank := rfl

@[simp]
theorem release_owner (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    (data.release rank).owner = data.owner := rfl

@[simp]
theorem release_outsider
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    (data.release rank).outsider = data.outsider := rfl

@[simp]
theorem release_singletonProfile
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    (data.release rank).singletonProfile =
      quittingLiteralOneDateProfile reward (data.compressedProfile rank)
        data.owner (data.clockBound rank) true := rfl

@[simp]
theorem release_pairProfile
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    (data.release rank).pairProfile =
      quittingLiteralOneDateProfile reward (data.release rank).singletonProfile
        data.outsider (data.clockBound rank) true := rfl

/-- The exact cap-prefixed compressed source. -/
def sourceProfile (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward (data.roots rank) (data.compressedProfile rank)

/-- The first cap-prefixed release, with a pure owner singleton at the fresh row. -/
def singletonProfile
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward (data.roots rank) (data.release rank).singletonProfile

/-- The second cap-prefixed release, with a pure owner-outsider pair at the
same fresh row. -/
def pairProfile (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward (data.roots rank) (data.release rank).pairProfile

/-- The actual fresh date after the common cap word. -/
def stage (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) : ℕ :=
  (data.roots rank).length + data.clockBound rank

/-- Joint Continue survival of the selected exact cap--Nash word. -/
def survival (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) : ℝ :=
  quittingCapNashStackContinueProduct (data.roots rank)

/-- Unconditional reach of the fresh compressed row after the common word. -/
def reach (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) : ℝ :=
  data.survival rank * data.neverProduct

theorem compressedLaws_isFiniteClock
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) (who : Fin 4) :
    IsFiniteClockStoppingLaw (data.clockBound rank) (data.compressedLaws rank who) :=
  quittingQuantileClockCompressedLaws_isFiniteClock
    reward data.profile (rank + 1) who

@[simp]
theorem compressedLaws_none
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) (who : Fin 4) :
    data.compressedLaws rank who none =
      quittingBehaviorStoppingLaw reward (data.profile who) none := by
  exact quittingQuantileClockCompressedLaws_none
    reward data.profile (rank + 1) who

/-- Every compressed fresh row has exactly the original joint Never reach. -/
theorem compressed_liveMass_fresh_eq_neverProduct
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    quittingLiveMass reward (data.compressedProfile rank) (data.clockBound rank) =
      data.neverProduct := by
  change quittingLiveMass reward
      (quittingStoppingLawProfile reward (data.compressedLaws rank))
        (data.clockBound rank) = data.neverProduct
  rw [quittingLiveMass_stoppingLawProfile_eq_prod_none_of_isFiniteClock
    (data.clockBound rank) (data.compressedLaws rank)
    (data.compressedLaws_isFiniteClock rank)]
  apply Finset.prod_congr rfl
  intro who _
  rw [data.compressedLaws_none rank who]

/-- The compressed semantic pairs converge to the supplied profile's exact
semantic pair. -/
theorem compressedSemanticPair_tendsto
    (data : FinFourPositiveNeverReleaseInput reward) :
    Tendsto (fun rank => quittingTerminalSemanticPair reward
        (data.compressedProfile rank)) atTop
      (nhds (quittingTerminalSemanticPair reward data.profile)) :=
  tendsto_quittingQuantileClockCompressed_semanticPair reward data.profile

/-- Total debt of the compressed suffixes converges to the supplied global
minimum value. -/
theorem compressedDebt_tendsto_inf
    (data : FinFourPositiveNeverReleaseInput reward) :
    Tendsto (fun rank => quittingTerminalDebtSum reward
        (data.compressedProfile rank)) atTop
      (nhds (quittingTerminalDebtSumInf reward)) := by
  have h := continuous_quittingTerminalSemanticDebtSum.tendsto
      (quittingTerminalSemanticPair reward data.profile) |>.comp
    data.compressedSemanticPair_tendsto
  change Tendsto (fun rank => quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (data.compressedProfile rank))) atTop
    (nhds (quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward data.profile))) at h
  rw [← data.debt_eq_inf]
  simpa only [quittingTerminalDebtSum_eq_terminalSemanticDebtSum] using h

/-- Global minimality and exact cap--Nash scaling force the selected word
survivals to converge to one. -/
theorem survival_tendsto_one
    (data : FinFourPositiveNeverReleaseInput reward) :
    Tendsto data.survival atTop (nhds 1) := by
  have hlower : Tendsto (fun rank =>
      quittingTerminalDebtSumInf reward /
        quittingTerminalDebtSum reward (data.compressedProfile rank)) atTop
      (nhds 1) := by
    have hconstant : Tendsto
        (fun _ : ℕ => quittingTerminalDebtSumInf reward) atTop
        (nhds (quittingTerminalDebtSumInf reward)) := tendsto_const_nhds
    have hquotient := hconstant.div data.compressedDebt_tendsto_inf
      data.debtInf_pos.ne'
    convert hquotient using 1
    · rfl
    · rw [div_self data.debtInf_pos.ne']
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
  · intro rank
    exact capNashStack_continueProduct_lowerBound
      (reward := reward) (data.roots rank) (data.compressedProfile rank)
        data.debtInf_pos (data.roots_nash rank)
  · intro rank
    exact quittingCapNashStackContinueProduct_le_one (data.roots rank)

/-- Exact total-debt scaling along each selected word. -/
theorem sourceDebt_eq_survival_mul
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    quittingTerminalDebtSum reward (data.sourceProfile rank) =
      data.survival rank *
        quittingTerminalDebtSum reward (data.compressedProfile rank) := by
  exact quittingTerminalDebtSum_capNashRootStack_eq
    (reward := reward) (data.roots rank) (data.compressedProfile rank)
      (data.roots_nash rank)

/-- The cap-prefixed source profiles return to the same global minimum debt. -/
theorem sourceDebt_tendsto_inf
    (data : FinFourPositiveNeverReleaseInput reward) :
    Tendsto (fun rank => quittingTerminalDebtSum reward
        (data.sourceProfile rank)) atTop
      (nhds (quittingTerminalDebtSumInf reward)) := by
  have h := data.survival_tendsto_one.mul data.compressedDebt_tendsto_inf
  convert h using 1
  · funext rank
    exact data.sourceDebt_eq_survival_mul rank
  · simp

/-- The unconditional fresh-row reach converges to the exact supplied joint
Never mass. -/
theorem reach_tendsto_neverProduct
    (data : FinFourPositiveNeverReleaseInput reward) :
    Tendsto data.reach atTop (nhds data.neverProduct) := by
  change Tendsto (fun rank => data.survival rank * data.neverProduct) atTop
    (nhds data.neverProduct)
  simpa using data.survival_tendsto_one.mul_const data.neverProduct

/-- Eventually the literal fresh row retains the packet's conservative
quarter of the positive joint Never mass. -/
theorem eventually_neverProduct_div_four_le_reach
    (data : FinFourPositiveNeverReleaseInput reward) :
    ∀ᶠ rank in atTop, data.neverProduct / 4 ≤ data.reach rank := by
  have hhalf : data.neverProduct / 2 < data.neverProduct := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    have hq : 0 < data.neverProduct := by
      exact data.neverProduct_pos
    have hscaled := mul_lt_mul_of_pos_left
      (show (1 : ℝ) < 2 by norm_num) hq
    simpa only [mul_one] using hscaled
  have heventually :=
    (tendsto_order.1 data.reach_tendsto_neverProduct).1 _ hhalf
  filter_upwards [heventually] with rank hrank
  linarith [data.neverProduct_pos]

private theorem literalRootStackProfile_apply_eq_of_tail
    (roots : List (Fin 4 → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile) (who : Fin 4)
    (htail : first who = second who) :
    quittingLiteralRootStackProfile reward roots first who =
      quittingLiteralRootStackProfile reward roots second who := by
  induction roots with
  | nil => simpa
  | cons root roots ih =>
      simp only [quittingLiteralRootStackProfile_cons]
      funext time history
      cases time with
      | zero => rfl
      | succ time => exact congrFun (congrFun ih time) _

private theorem update_eq_target_of_opponent_eq
    (source target : (quittingGame reward).BehaviorProfile) (who : Fin 4)
    (hopponent : ∀ other ≠ who, target other = source other) :
    Function.update source who (target who) = target := by
  funext other
  by_cases hother : other = who
  · subst other
    simp
  · rw [Function.update_of_ne hother]
    exact (hopponent other hother).symm

private theorem literalRootStackProfile_eq_update_of_tail_update
    (roots : List (Fin 4 → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile) (who : Fin 4)
    (hsecond : second = Function.update first who (second who)) :
    quittingLiteralRootStackProfile reward roots second =
      Function.update (quittingLiteralRootStackProfile reward roots first) who
        (quittingLiteralRootStackProfile reward roots second who) := by
  funext other
  by_cases hother : other = who
  · subst other
    simp
  · rw [Function.update_of_ne hother]
    apply literalRootStackProfile_apply_eq_of_tail
    rw [hsecond, Function.update_of_ne hother]

/-- The first prefixed profile is one literal complete behavioral replacement. -/
theorem source_to_singleton_ancestry
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    IsQuittingBehaviorReplacementAncestry
      (data.sourceProfile rank) (data.singletonProfile rank) := by
  have h := isQuittingBehaviorReplacementAncestry_update
    (data.sourceProfile rank) data.owner
      (data.singletonProfile rank data.owner)
  have heq : data.singletonProfile rank =
      Function.update (data.sourceProfile rank) data.owner
        (data.singletonProfile rank data.owner) := by
    apply literalRootStackProfile_eq_update_of_tail_update
    symm
    apply update_eq_target_of_opponent_eq
    intro other hother
    simp [QuittingPositiveNeverTwoRelease.singletonProfile,
      quittingLiteralOneDateProfile, hother]
  rwa [← heq] at h

/-- The second prefixed profile is one literal complete behavioral replacement. -/
theorem singleton_to_pair_ancestry
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    IsQuittingBehaviorReplacementAncestry
      (data.singletonProfile rank) (data.pairProfile rank) := by
  have h := isQuittingBehaviorReplacementAncestry_update
    (data.singletonProfile rank) data.outsider
      (data.pairProfile rank data.outsider)
  have heq : data.pairProfile rank =
      Function.update (data.singletonProfile rank) data.outsider
        (data.pairProfile rank data.outsider) := by
    apply literalRootStackProfile_eq_update_of_tail_update
    symm
    apply update_eq_target_of_opponent_eq
    intro other hother
    simp [QuittingPositiveNeverTwoRelease.pairProfile,
      quittingLiteralOneDateProfile, hother]
  rwa [← heq] at h

/-- The first prefixed gain is exactly prefix survival times Never reach
times the owner's singleton reward. -/
theorem singletonGain_eq
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    quittingTerminalPayoff reward (data.singletonProfile rank) data.owner -
        quittingTerminalPayoff reward (data.sourceProfile rank) data.owner =
      quittingCapNashStackContinueProduct (data.roots rank) *
        (data.neverProduct *
          reward (quittingSingletonTerminal data.owner) data.owner) := by
  rw [sourceProfile, singletonProfile,
    quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul]
  congr 1
  have h := (data.release rank).singletonPayoff_sub_sourcePayoff_eq
  have h' :
      quittingTerminalPayoff reward (data.release rank).singletonProfile data.owner -
          quittingTerminalPayoff reward (data.compressedProfile rank) data.owner =
        quittingLiveMass reward (data.compressedProfile rank) (data.clockBound rank) *
          reward (quittingSingletonTerminal data.owner) data.owner := by
    simpa using h
  rw [h', data.compressed_liveMass_fresh_eq_neverProduct rank]

/-- The singleton gain in reach-normalized form. -/
theorem singletonGain_eq_reach_mul_reward
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    quittingTerminalPayoff reward (data.singletonProfile rank) data.owner -
        quittingTerminalPayoff reward (data.sourceProfile rank) data.owner =
      data.reach rank *
        reward (quittingSingletonTerminal data.owner) data.owner := by
  rw [data.singletonGain_eq rank]
  unfold reach survival
  ring

/-- The unprefixed first target assigns exactly the joint Never mass to the
pure owner singleton at the fresh row. -/
theorem release_singletonStageMass_eq_neverProduct
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    quittingStageCoalitionMass reward (data.release rank).singletonProfile
        (data.clockBound rank) (quittingSingletonTerminal data.owner) =
      data.neverProduct := by
  have hroot : quittingProfileLiveRoot reward
      (data.release rank).singletonProfile (data.clockBound rank) =
        quittingPureSetRoot ({data.owner} : Finset (Fin 4)) := by
    simpa using (data.release rank).singletonProfile_root_eq_pureSingleton
  have hlive : quittingLiveMass reward
      (data.release rank).singletonProfile (data.clockBound rank) =
        data.neverProduct := by
    calc
      _ = quittingLiveMass reward (data.compressedProfile rank)
          (data.clockBound rank) := by
        simpa using
          (quittingLiveMass_literalOneDateProfile_eq reward
            (data.compressedProfile rank) data.owner (data.clockBound rank) true)
      _ = data.neverProduct := data.compressed_liveMass_fresh_eq_neverProduct rank
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    hroot, hlive]
  change data.neverProduct * quittingRootCoalitionMass
      (quittingPureSetRoot ({data.owner} : Finset (Fin 4))) {data.owner} =
    data.neverProduct
  have hmass : quittingRootCoalitionMass
      (quittingPureSetRoot ({data.owner} : Finset (Fin 4))) {data.owner} = 1 := by
    rw [quittingRootCoalitionMass_eq_pmfPi]
    simp [quittingPureSetRoot, quittingSetAction, quittingCoalitionAction]
  rw [hmass, mul_one]

/-- The cap-prefixed first target carries exactly the retained fresh-row
reach at the shifted date. -/
theorem singletonStageMass_eq_reach
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    quittingStageCoalitionMass reward (data.singletonProfile rank)
        (data.stage rank) (quittingSingletonTerminal data.owner) =
      data.reach rank := by
  rw [singletonProfile, stage,
    quittingStageCoalitionMass_literalRootStack_add_length,
    data.release_singletonStageMass_eq_neverProduct rank]
  rfl

private theorem quittingAllContinueProfileSpine_add'
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : ℕ) :
    quittingAllContinueProfileSpine reward profile (first + second) =
      quittingAllContinueProfileSpine reward
        (quittingAllContinueProfileSpine reward profile first) second := by
  induction second with
  | zero => simp [quittingAllContinueProfileSpine]
  | succ second ih =>
      rw [Nat.add_succ]
      simp only [quittingAllContinueProfileSpine]
      rw [ih]

/-- The first prefixed release is a pure owner singleton at the literal
shifted fresh date. -/
theorem singletonProfile_root_at_stage_eq_pureSingleton
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    quittingProfileLiveRoot reward (data.singletonProfile rank)
        (data.stage rank) =
      quittingPureSetRoot ({data.owner} : Finset (Fin 4)) := by
  rw [← quittingProfileSpineRoot_eq_profileLiveRoot]
  unfold quittingProfileSpineRoot singletonProfile stage
  rw [quittingAllContinueProfileSpine_add',
    quittingAllContinueProfileSpine_literalRootStackProfile_length]
  change quittingProfileSpineRoot reward (data.release rank).singletonProfile
      (data.clockBound rank) = _
  rw [quittingProfileSpineRoot_eq_profileLiveRoot]
  simpa only [release_mark, release_owner] using
    (data.release rank).singletonProfile_root_eq_pureSingleton

/-- The live mass at the shifted singleton row is exactly the retained reach. -/
theorem singletonLiveMass_at_stage_eq_reach
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    quittingLiveMass reward (data.singletonProfile rank) (data.stage rank) =
      data.reach rank := by
  rw [← data.singletonStageMass_eq_reach rank,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    data.singletonProfile_root_at_stage_eq_pureSingleton rank]
  have hmass : quittingRootCoalitionMass
      (quittingPureSetRoot ({data.owner} : Finset (Fin 4))) {data.owner} = 1 := by
    rw [quittingRootCoalitionMass_eq_pmfPi]
    simp [quittingPureSetRoot, quittingSetAction, quittingCoalitionAction]
  have hmass' : quittingRootCoalitionMass
      (quittingPureSetRoot ({data.owner} : Finset (Fin 4)))
        (quittingSingletonTerminal data.owner).val = 1 := by
    simpa only [quittingSingletonTerminal] using hmass
  rw [hmass', mul_one]

/-- The actual second release represented at the shifted fresh date. -/
def movingMark
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    QuittingActualReachedScreenedEndpointMark reward where
  sourceProfile := data.singletonProfile rank
  mover := data.outsider
  other := data.owner
  mark := data.stage rank
  selectedAction := true
  other_ne_mover := data.outsider_ne_owner.symm
  source_mover_opposite := by
    rw [data.singletonProfile_root_at_stage_eq_pureSingleton rank]
    simp [quittingPureSetRoot, quittingSetAction, data.outsider_ne_owner]
  source_other_quits := by
    rw [data.singletonProfile_root_at_stage_eq_pureSingleton rank]
    simp [quittingPureSetRoot, quittingSetAction]
  selected_endpoint_gain_nonneg := by
    rw [data.singletonProfile_root_at_stage_eq_pureSingleton rank]
    change 0 ≤ quittingRootExpectedPayoff reward _
          (Function.update (quittingPureSetRoot {data.owner})
            data.outsider (PMF.pure true)) data.outsider -
        quittingRootSuccessorPayoff reward _
          (quittingPureSetRoot {data.owner}) data.outsider
    rw [quittingRootExpectedPayoff_update_sub_successorPayoff,
      QuittingPositiveNeverTwoRelease.quittingRootEndpointDifference_pureSingleton_outsider
        _ data.owner data.outsider data.outsider_ne_owner]
    have hcoefficient :
        ((PMF.pure true : PMF Bool) true).toReal -
            ((quittingPureSetRoot ({data.owner} : Finset (Fin 4))
              data.outsider) true).toReal = 1 := by
      simp [quittingPureSetRoot, quittingSetAction, data.outsider_ne_owner]
    rw [hcoefficient, one_mul]
    exact data.outsiderPairGain_pos.le.trans data.outsiderPairGain_le_rewardGap

/-- The shifted mark's local gap is the fixed pair-minus-singleton table gap. -/
theorem movingMark_localEndpointGap_eq
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    (data.movingMark rank).localEndpointGap =
      reward ⟨{data.owner, data.outsider}, by simp⟩ data.outsider -
        reward (quittingSingletonTerminal data.owner) data.outsider := by
  unfold QuittingActualReachedScreenedEndpointMark.localEndpointGap movingMark
  rw [data.singletonProfile_root_at_stage_eq_pureSingleton rank]
  change quittingRootExpectedPayoff reward _
        (Function.update (quittingPureSetRoot {data.owner})
          data.outsider (PMF.pure true)) data.outsider -
      quittingRootSuccessorPayoff reward _
        (quittingPureSetRoot {data.owner}) data.outsider = _
  rw [quittingRootExpectedPayoff_update_sub_successorPayoff,
    QuittingPositiveNeverTwoRelease.quittingRootEndpointDifference_pureSingleton_outsider
      _ data.owner data.outsider data.outsider_ne_owner]
  have hcoefficient :
      ((PMF.pure true : PMF Bool) true).toReal -
          ((quittingPureSetRoot ({data.owner} : Finset (Fin 4))
            data.outsider) true).toReal = 1 := by
    simp [quittingPureSetRoot, quittingSetAction, data.outsider_ne_owner]
  rw [hcoefficient, one_mul]

/-- The shifted mark has the pure singleton as its nonempty host. -/
def movingMarkPureHost
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    QuittingActualReachedScreenedEndpointMark.PurePairData
      (data.movingMark rank) where
  coalition := {data.owner}
  coalition_nonempty := Finset.singleton_nonempty data.owner
  source_root_eq := data.singletonProfile_root_at_stage_eq_pureSingleton rank

/-- Eventually the first actual replacement gain has the conservative
positive floor inherited from the supplied singleton table gain. -/
theorem eventually_ownerGain_floor
    (data : FinFourPositiveNeverReleaseInput reward) :
    ∀ᶠ rank in atTop,
      data.neverProduct * data.ownerSingletonGain / 4 ≤
        quittingTerminalPayoff reward (data.singletonProfile rank) data.owner -
          quittingTerminalPayoff reward (data.sourceProfile rank) data.owner := by
  filter_upwards [data.eventually_neverProduct_div_four_le_reach]
    with rank hreach
  rw [data.singletonGain_eq_reach_mul_reward rank]
  calc
    data.neverProduct * data.ownerSingletonGain / 4 =
        (data.neverProduct / 4) * data.ownerSingletonGain := by ring
    _ ≤ data.reach rank * data.ownerSingletonGain :=
      mul_le_mul_of_nonneg_right hreach data.ownerSingletonGain_pos.le
    _ ≤ data.reach rank *
        reward (quittingSingletonTerminal data.owner) data.owner :=
      mul_le_mul_of_nonneg_left data.ownerSingletonGain_le_reward
        (mul_nonneg (quittingCapNashStackContinueProduct_nonneg (data.roots rank))
          data.neverProduct_pos.le)

/-- The second prefixed gain is exactly prefix survival times Never reach
times the pair-minus-singleton reward gap. -/
theorem pairGain_eq
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    quittingTerminalPayoff reward (data.pairProfile rank) data.outsider -
        quittingTerminalPayoff reward (data.singletonProfile rank) data.outsider =
      quittingCapNashStackContinueProduct (data.roots rank) *
        (data.neverProduct *
          (reward ⟨{data.owner, data.outsider}, by simp⟩ data.outsider -
            reward (quittingSingletonTerminal data.owner) data.outsider)) := by
  have hgap : 0 ≤ reward
      ⟨{data.owner, data.outsider}, by simp⟩ data.outsider -
        reward (quittingSingletonTerminal data.owner) data.outsider :=
    data.outsiderPairGain_pos.le.trans data.outsiderPairGain_le_rewardGap
  rw [singletonProfile, pairProfile,
    quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul]
  congr 1
  have h := (data.release rank).pairPayoff_sub_singletonPayoff_eq hgap
  have hlive : quittingLiveMass reward
      (data.release rank).singletonProfile (data.release rank).mark =
        data.neverProduct := by
    calc
      _ = quittingLiveMass reward (data.compressedProfile rank)
          (data.clockBound rank) := by
        simpa using
          (quittingLiveMass_literalOneDateProfile_eq reward
            (data.compressedProfile rank) data.owner (data.clockBound rank) true)
      _ = data.neverProduct := data.compressed_liveMass_fresh_eq_neverProduct rank
  rw [hlive] at h
  simpa using h

/-- The pair gain in reach-normalized form. -/
theorem pairGain_eq_reach_mul_rewardGap
    (data : FinFourPositiveNeverReleaseInput reward) (rank : ℕ) :
    quittingTerminalPayoff reward (data.pairProfile rank) data.outsider -
        quittingTerminalPayoff reward (data.singletonProfile rank) data.outsider =
      data.reach rank *
        (reward ⟨{data.owner, data.outsider}, by simp⟩ data.outsider -
          reward (quittingSingletonTerminal data.owner) data.outsider) := by
  rw [data.pairGain_eq rank]
  unfold reach survival
  ring

/-- Eventually the second actual replacement gain has the conservative
positive floor inherited from the supplied pair table gap. -/
theorem eventually_outsiderGain_floor
    (data : FinFourPositiveNeverReleaseInput reward) :
    ∀ᶠ rank in atTop,
      data.neverProduct * data.outsiderPairGain / 4 ≤
        quittingTerminalPayoff reward (data.pairProfile rank) data.outsider -
          quittingTerminalPayoff reward (data.singletonProfile rank) data.outsider := by
  filter_upwards [data.eventually_neverProduct_div_four_le_reach]
    with rank hreach
  rw [data.pairGain_eq_reach_mul_rewardGap rank]
  calc
    data.neverProduct * data.outsiderPairGain / 4 =
        (data.neverProduct / 4) * data.outsiderPairGain := by ring
    _ ≤ data.reach rank * data.outsiderPairGain :=
      mul_le_mul_of_nonneg_right hreach data.outsiderPairGain_pos.le
    _ ≤ data.reach rank *
        (reward ⟨{data.owner, data.outsider}, by simp⟩ data.outsider -
          reward (quittingSingletonTerminal data.owner) data.outsider) :=
      mul_le_mul_of_nonneg_left data.outsiderPairGain_le_rewardGap
        (mul_nonneg (quittingCapNashStackContinueProduct_nonneg (data.roots rank))
          data.neverProduct_pos.le)

end FinFourPositiveNeverReleaseInput

end GameTheory
