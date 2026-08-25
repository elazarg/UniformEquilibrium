/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Probability.Distributions.Geometric
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreementOrientation
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum
import UniformEquilibrium.Quitting.Terminal.StrategicallyPrecompactWatchdogProperBoundary

/-!
# Positive debt does not make literal terminal semantics closed

A two-player rational quitting table has executable semantic pairs of debt
`1 + 1 / n` converging to a positive-debt carrier point which is not realized
by any behavioral profile.  The nonattainment theorem ranges over arbitrary
behavioral profiles and arbitrary unilateral behavioral deviations.

The same table has an executable zero-debt pair.  Thus the example rules out
attainment from pointwise positive debt alone, but says nothing about a fiber
whose globally minimum debt is positive.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct
open scoped Topology

namespace PositiveDebtTerminalSemanticNonattainment

abbrev Player := Bool
abbrev clock : Player := false
abbrev atom : Player := true

theorem player_card : Fintype.card Player = 2 := by
  decide

def clockTerminal : {S : Finset Player // S.Nonempty} :=
  ⟨{clock}, by simp⟩

def jointTerminal : {S : Finset Player // S.Nonempty} :=
  ⟨{clock, atom}, by simp⟩

theorem jointTerminal_ne_clockTerminal : jointTerminal ≠ clockTerminal := by
  decide

/-- The clock loses one when it Quits alone.  The tester earns one exactly
when it Quits simultaneously with the clock. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who =>
    if terminal = clockTerminal then
      if who = clock then -1 else 0
    else if terminal = jointTerminal then
      if who = atom then 1 else 0
    else 0

theorem reward_bound (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : |reward terminal who| ≤ 1 := by
  unfold reward
  split_ifs <;> norm_num

theorem terminalPayoff_clock_eq_neg_clockMass
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile clock =
      -quittingTerminalOutcomeMass reward profile (some clockTerminal) := by
  rw [← congrFun (quittingTerminalRewardMoment_outcomeMass reward profile)
    clock]
  unfold quittingTerminalRewardMoment
  rw [Finset.sum_eq_single (some clockTerminal)]
  · simp [quittingTerminalOutcomeReward, reward, clockTerminal, clock]
  · intro outcome _houtcome hne
    cases outcome with
    | none => simp [quittingTerminalOutcomeReward]
    | some terminal =>
        have hterminal : terminal ≠ clockTerminal := by
          intro heq
          subst terminal
          exact hne rfl
        simp [quittingTerminalOutcomeReward, reward, hterminal, clock, atom]
  · simp

theorem terminalPayoff_atom_eq_jointMass
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile atom =
      quittingTerminalOutcomeMass reward profile (some jointTerminal) := by
  rw [← congrFun (quittingTerminalRewardMoment_outcomeMass reward profile)
    atom]
  unfold quittingTerminalRewardMoment
  rw [Finset.sum_eq_single (some jointTerminal)]
  · simp [quittingTerminalOutcomeReward, reward,
      jointTerminal_ne_clockTerminal, atom]
  · intro outcome _houtcome hne
    cases outcome with
    | none => simp [quittingTerminalOutcomeReward]
    | some terminal =>
        have hterminal : terminal ≠ jointTerminal := by
          intro heq
          subst terminal
          exact hne rfl
        simp [quittingTerminalOutcomeReward, reward, hterminal, clock, atom]
  · simp

theorem terminalPayoff_clock_le_zero
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile clock ≤ 0 := by
  rw [terminalPayoff_clock_eq_neg_clockMass]
  exact neg_nonpos.mpr
    ((quittingTerminalOutcomeMass_mem_stdSimplex reward profile).1 _)

theorem terminalPayoff_atom_nonneg
    (profile : (quittingGame reward).BehaviorProfile) :
    0 ≤ quittingTerminalPayoff reward profile atom := by
  rw [terminalPayoff_atom_eq_jointMass]
  exact (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).1 _

theorem terminalPayoff_atom_le_one
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile atom ≤ 1 := by
  rw [terminalPayoff_atom_eq_jointMass]
  let mass := quittingTerminalOutcomeMass reward profile
  have hsimplex := quittingTerminalOutcomeMass_mem_stdSimplex reward profile
  have hle : mass (some jointTerminal) ≤ ∑ outcome, mass outcome :=
    Finset.single_le_sum (fun outcome _ => hsimplex.1 outcome)
      (Finset.mem_univ (some jointTerminal))
  change mass (some jointTerminal) ≤ 1
  rw [← hsimplex.2]
  exact hle

theorem continuationBestResponse_atom_le_one
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingContinuationBestResponseValue reward profile atom ≤ 1 := by
  unfold quittingContinuationBestResponseValue
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨deviation, rfl⟩
  exact terminalPayoff_atom_le_one _

/-- Purely continuing gives both players terminal payoff zero. -/
theorem terminalPayoff_allContinue (who : Player) :
    quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) who =
      0 := by
  exact quittingTerminalPayoff_quittingAlwaysContinue reward who

/-- The semantic pair which is the nonattained positive-debt limit. -/
def limitPair : QuittingTerminalSemanticPair Player :=
  (fun who => if who = clock then -1 else 0, fun _ => 0)

@[simp] theorem limitPair_payoff_clock : limitPair.1 clock = -1 := by
  simp [limitPair, clock]

@[simp] theorem limitPair_payoff_atom : limitPair.1 atom = 0 := by
  simp [limitPair, clock, atom]

@[simp] theorem limitPair_cap (who : Player) : limitPair.2 who = 0 := by
  simp [limitPair]

theorem opponentSurvivalWeight_atom_eq_clockHazardSurvival
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) atom 0 time =
      quittingHazardSurvival
        (quittingBehaviorLiveHazard reward (profile clock)) time := by
  unfold quittingOpponentSurvivalWeight quittingHazardSurvival
    quittingFixedOpponentsContinueMass
  apply Finset.prod_congr rfl
  intro offset hoffset
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [quittingProfileLiveRoot, quittingBehaviorLiveHazard, clock, atom]
  rw [Nat.zero_add]

/-- If the tester chooses one deterministic Quit date, its payoff is exactly
the atom of the clock's complete stopping law at that date. -/
theorem terminalPayoff_update_atom_pureTime_eq_stoppingLawAtom
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingTerminalPayoff reward
        (Function.update profile atom
          (quittingPureTimeBehaviorStrategy reward atom (some time))) atom =
      (quittingBehaviorStoppingLaw reward (profile clock) (some time)).toReal := by
  rw [terminalPayoff_atom_eq_jointMass,
    quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
      reward profile atom time jointTerminal (by simp [jointTerminal, atom])]
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_update_pureTime_some_eq_opponentSurvivalWeight]
  rw [quittingBehaviorStoppingLaw_some_toReal,
    quittingHazardStopMass_eq_survival_mul_stop]
  congr 1
  · exact opponentSurvivalWeight_atom_eq_clockHazardSurvival profile time
  · unfold quittingRootCoalitionMass quittingRootQuitRates
      Math.PMFProduct.coalitionMass
    have hjoint : jointTerminal.val = (Finset.univ : Finset Player) := by
      decide
    have hclockComplement : ({clock} : Finset Player)ᶜ = {atom} := by
      decide
    rw [hjoint]
    simp [quittingPureTimeBehaviorStrategy, quittingPureTimeHazard, clock,
      atom, hclockComplement, quittingProfileLiveRoot,
      quittingBehaviorLiveHazard]

theorem terminalPayoff_update_atom_never_eq_zero
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward
        (Function.update profile atom
          (quittingPureTimeBehaviorStrategy reward atom none)) atom = 0 := by
  rw [terminalPayoff_atom_eq_jointMass,
    quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero
      reward profile atom jointTerminal (by simp [jointTerminal, atom])]

/-- Uniform law on the first `n + 1` finite dates, with no Never atom. -/
def uniformClockLaw (n : ℕ) : PMF (Option ℕ) :=
  (PMF.uniformOfFintype (Fin (n + 1))).map
    (fun time => some time.val)

@[simp] theorem uniformClockLaw_none (n : ℕ) :
    uniformClockLaw n none = 0 := by
  rw [uniformClockLaw, PMF.map_apply, tsum_fintype]
  simp

theorem uniformClockLaw_some_of_lt (n time : ℕ) (htime : time < n + 1) :
    uniformClockLaw n (some time) =
      ((n + 1 : ℕ) : ENNReal)⁻¹ := by
  rw [uniformClockLaw, PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single ⟨time, htime⟩]
  · simp
  · intro other _hother hne
    simp only [Option.some.injEq]
    have hval : time ≠ other.val := by
      intro heq
      apply hne
      exact Fin.ext heq.symm
    simp [hval]
  · simp

theorem uniformClockLaw_some_of_le (n time : ℕ) (htime : n + 1 ≤ time) :
    uniformClockLaw n (some time) = 0 := by
  rw [uniformClockLaw, PMF.map_apply, tsum_fintype]
  apply Finset.sum_eq_zero
  intro other _hother
  simp only [Option.some.injEq]
  have hne : time ≠ other.val := by omega
  simp [hne]

theorem uniformClockLaw_some_toReal_le (n time : ℕ) :
    (uniformClockLaw n (some time)).toReal ≤ 1 / (n + 1 : ℝ) := by
  by_cases htime : time < n + 1
  · rw [uniformClockLaw_some_of_lt n time htime]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    norm_num only [Nat.cast_add, Nat.cast_one, one_div]
    exact le_refl ((n : ℝ) + 1)⁻¹
  · rw [uniformClockLaw_some_of_le n time (by omega)]
    positivity

theorem uniformClockLaw_zero_toReal (n : ℕ) :
    (uniformClockLaw n (some 0)).toReal = 1 / (n + 1 : ℝ) := by
  rw [uniformClockLaw_some_of_lt n 0 (by omega)]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  norm_num only [Nat.cast_add, Nat.cast_one, one_div]

def clockStrategy (n : ℕ) :
    (quittingGame reward).BehaviorStrategy clock :=
  quittingStoppingLawBehaviorStrategy reward clock (uniformClockLaw n)

def profile (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update (quittingAlwaysContinueProfile reward) clock
    (clockStrategy n)

@[simp] theorem profile_clock (n : ℕ) :
    profile n clock = clockStrategy n := by
  simp [profile]

@[simp] theorem profile_atom (n : ℕ) :
    profile n atom = quittingAlwaysContinueStrategy reward atom := by
  funext time history
  rfl

theorem profile_clockStoppingLaw (n : ℕ) :
    quittingBehaviorStoppingLaw reward (profile n clock) = uniformClockLaw n := by
  simp [clockStrategy]

theorem terminalPayoff_update_clock_never_eq_zero
    (base : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward
        (Function.update base clock
          (quittingPureTimeBehaviorStrategy reward clock none)) clock = 0 := by
  rw [terminalPayoff_clock_eq_neg_clockMass,
    quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero
      reward base clock clockTerminal (by simp [clockTerminal])]
  norm_num

theorem continuationBestResponse_clock_eq_zero
    (base : (quittingGame reward).BehaviorProfile) :
    quittingContinuationBestResponseValue reward base clock = 0 := by
  unfold quittingContinuationBestResponseValue
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨deviation, rfl⟩
    exact terminalPayoff_clock_le_zero _
  · apply le_csSup
      (bddAbove_range_quittingTerminalPayoff_update reward base clock)
    exact ⟨quittingPureTimeBehaviorStrategy reward clock none,
      terminalPayoff_update_clock_never_eq_zero base⟩

theorem terminalPayoff_update_allContinue_clock_some_eq_neg_one
    (time : ℕ) :
    quittingTerminalPayoff reward
        (Function.update (quittingAlwaysContinueProfile reward) clock
          (quittingPureTimeBehaviorStrategy reward clock (some time))) clock =
      -1 := by
  rw [terminalPayoff_clock_eq_neg_clockMass,
    quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
      reward (quittingAlwaysContinueProfile reward) clock time clockTerminal
        (by simp [clockTerminal])]
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_update_pureTime_some_eq_opponentSurvivalWeight]
  unfold quittingOpponentSurvivalWeight quittingFixedOpponentsContinueMass
    quittingRootCoalitionMass quittingRootQuitRates
    Math.PMFProduct.coalitionMass
  have hclockComplement : ({clock} : Finset Player)ᶜ = {atom} := by
    decide
  simp [quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingAlwaysContinueProfile,
    quittingProfileLiveRoot, quittingPureTimeBehaviorStrategy,
    quittingPureTimeHazard, clockTerminal, clock, hclockComplement,
    StochasticGame.stationaryBehaviorProfile, PMF.pure_apply]
  change ((PMF.pure (false : Bool) false).toReal ^ time) *
      (1 - (PMF.pure (false : Bool) true).toReal) = 1
  simp [PMF.pure_apply]

theorem terminalPayoff_update_allContinue_clock_none_eq_zero :
    quittingTerminalPayoff reward
        (Function.update (quittingAlwaysContinueProfile reward) clock
          (quittingPureTimeBehaviorStrategy reward clock none)) clock = 0 := by
  exact terminalPayoff_update_clock_never_eq_zero _

theorem profile_payoff_clock (n : ℕ) :
    quittingTerminalPayoff reward (profile n) clock = -1 := by
  rw [profile, quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime,
    show quittingBehaviorStoppingLaw reward (clockStrategy n) =
        uniformClockLaw n by simp [clockStrategy]]
  rw [uniformClockLaw, Math.Probability.expect_map]
  have hvalue : (fun time : Fin (n + 1) =>
      quittingTerminalPayoff reward
        (Function.update (quittingAlwaysContinueProfile reward) clock
          (quittingPureTimeBehaviorStrategy reward clock (some time.val)))
        clock) = fun _ => -1 := by
    funext time
    exact terminalPayoff_update_allContinue_clock_some_eq_neg_one time.val
  rw [hvalue, Math.Probability.expect_eq_sum]
  simp [PMF.uniformOfFintype_apply]
  have htoReal : ((n : ENNReal) + 1).toReal = (n : ℝ) + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
  rw [htoReal]
  field_simp

theorem profile_payoff_atom (n : ℕ) :
    quittingTerminalPayoff reward (profile n) atom = 0 := by
  have hnever : quittingPureTimeBehaviorStrategy reward atom none =
      quittingAlwaysContinueStrategy reward atom := by
    funext time history
    rfl
  have hsame : Function.update (profile n) atom
      (quittingPureTimeBehaviorStrategy reward atom none) = profile n := by
    funext who
    by_cases hwho : who = atom
    · subst who
      simp [hnever, profile_atom]
    · simp [Function.update_of_ne hwho]
  rw [← hsame]
  exact terminalPayoff_update_atom_never_eq_zero (profile n)

theorem profile_cap_atom (n : ℕ) :
    quittingContinuationBestResponseValue reward (profile n) atom =
      1 / (n + 1 : ℝ) := by
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  let values : Set ℝ := Set.range fun choice : Option ℕ =>
    quittingTerminalPayoff reward
      (Function.update (profile n) atom
        (quittingPureTimeBehaviorStrategy reward atom choice)) atom
  have hbound : ∀ value ∈ values, value ≤ 1 / (n + 1 : ℝ) := by
    rintro _ ⟨choice, rfl⟩
    cases choice with
    | none =>
        dsimp only
        rw [terminalPayoff_update_atom_never_eq_zero]
        positivity
    | some time =>
        dsimp only
        rw [terminalPayoff_update_atom_pureTime_eq_stoppingLawAtom,
          profile_clockStoppingLaw]
        exact uniformClockLaw_some_toReal_le n time
  have hbdd : BddAbove values := ⟨1 / (n + 1 : ℝ), hbound⟩
  change sSup values = _
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) hbound
  · apply le_csSup hbdd
    refine ⟨some 0, ?_⟩
    dsimp only
    rw [terminalPayoff_update_atom_pureTime_eq_stoppingLawAtom,
      profile_clockStoppingLaw, uniformClockLaw_zero_toReal]

/-- Exact semantic pair of the `n`th diffuse finite clock. -/
def approximatingPair (n : ℕ) : QuittingTerminalSemanticPair Player :=
  (fun who => if who = clock then -1 else 0,
    fun who => if who = clock then 0 else 1 / (n + 1 : ℝ))

theorem profile_semanticPair (n : ℕ) :
    quittingTerminalSemanticPair reward (profile n) = approximatingPair n := by
  unfold quittingTerminalSemanticPair
  apply Prod.ext
  · funext who
    cases who
    · exact profile_payoff_clock n
    · simpa [approximatingPair, clock] using profile_payoff_atom n
  · funext who
    cases who
    · simpa [approximatingPair, clock] using
        continuationBestResponse_clock_eq_zero (profile n)
    · simpa [approximatingPair, clock] using profile_cap_atom n

theorem approximatingPair_debtSum (n : ℕ) :
    quittingTerminalSemanticDebtSum (approximatingPair n) =
      1 + 1 / (n + 1 : ℝ) := by
  unfold quittingTerminalSemanticDebtSum quittingTerminalSemanticDebt
  rw [Fintype.sum_bool]
  norm_num [approximatingPair, clock, atom]
  ring

theorem tendsto_one_div_succ :
    Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

theorem approximatingPair_tendsto_limitPair :
    Tendsto approximatingPair atTop (nhds limitPair) := by
  have hpayoff : Tendsto (fun n => (approximatingPair n).1) atTop
      (nhds limitPair.1) := by
    apply tendsto_pi_nhds.2
    intro who
    cases who <;> simp [approximatingPair, limitPair, clock]
  have hcap : Tendsto (fun n => (approximatingPair n).2) atTop
      (nhds limitPair.2) := by
    apply tendsto_pi_nhds.2
    intro who
    cases who
    · simp [approximatingPair, limitPair, clock]
    · simpa [approximatingPair, limitPair, clock] using tendsto_one_div_succ
  simpa only [Prod.eta] using hpayoff.prodMk_nhds hcap

theorem profile_semanticPair_tendsto_limitPair :
    Tendsto (fun n => quittingTerminalSemanticPair reward (profile n))
      atTop (nhds limitPair) := by
  simpa only [profile_semanticPair] using approximatingPair_tendsto_limitPair

theorem limitPair_mem_carrier :
    limitPair ∈ quittingTerminalSemanticCarrier reward := by
  change limitPair ∈ closure (quittingAttainableTerminalSemanticPairs reward)
  apply isClosed_closure.mem_of_tendsto profile_semanticPair_tendsto_limitPair
  exact Filter.Eventually.of_forall fun n => subset_closure
    ⟨profile n, rfl⟩

theorem continuationBestResponse_atom_allContinue_eq_zero :
    quittingContinuationBestResponseValue reward
      (quittingAlwaysContinueProfile reward) atom = 0 := by
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  let values : Set ℝ := Set.range fun choice : Option ℕ =>
    quittingTerminalPayoff reward
      (Function.update (quittingAlwaysContinueProfile reward) atom
        (quittingPureTimeBehaviorStrategy reward atom choice)) atom
  have hzero : ∀ value ∈ values, value = 0 := by
    rintro _ ⟨choice, rfl⟩
    cases choice with
    | none =>
        dsimp only
        exact terminalPayoff_update_atom_never_eq_zero _
    | some time =>
        dsimp only
        rw [terminalPayoff_update_atom_pureTime_eq_stoppingLawAtom]
        rw [quittingBehaviorStoppingLaw_some_toReal,
          quittingHazardStopMass_eq_survival_mul_stop]
        apply mul_eq_zero_of_right
        change ((PMF.pure (false : Bool) true).toReal) = 0
        simp [PMF.pure_apply]
  change sSup values = 0
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    intro value hvalue
    exact (hzero value hvalue).le
  · apply le_csSup ⟨0, fun value hvalue => (hzero value hvalue).le⟩
    exact ⟨none, hzero _ ⟨none, rfl⟩⟩

theorem allContinue_semanticPair_eq_zero :
    quittingTerminalSemanticPair reward
        (quittingAlwaysContinueProfile reward) =
      ((0 : Payoff Player), (0 : Payoff Player)) := by
  unfold quittingTerminalSemanticPair
  apply Prod.ext <;> funext who
  · exact terminalPayoff_allContinue who
  · cases who
    · exact continuationBestResponse_clock_eq_zero _
    · exact continuationBestResponse_atom_allContinue_eq_zero

/-- Explicit zero-debt fence: the table's global minimum over executable
profiles is zero, attained by all-Continue play. -/
theorem globalMinimumDebt_eq_zero :
    IsGreatest
      {lower : ℝ | ∀ candidate ∈ quittingAttainableTerminalSemanticPairs reward,
        lower ≤ quittingTerminalSemanticDebtSum candidate} 0 := by
  constructor
  · intro candidate hcandidate
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalSemanticDebt_nonneg_of_attainable reward hcandidate who
  · intro lower hlower
    have hzero := hlower
      (quittingTerminalSemanticPair reward
        (quittingAlwaysContinueProfile reward))
      ⟨quittingAlwaysContinueProfile reward, rfl⟩
    rw [allContinue_semanticPair_eq_zero] at hzero
    simpa [quittingTerminalSemanticDebtSum,
      quittingTerminalSemanticDebt] using hzero

/-- Unit mass on the clock-only terminal event forces a positive atom in the
clock's own complete stopping law. -/
theorem exists_clockStoppingLawAtom_pos_of_clockMass_eq_one
    (profile : (quittingGame reward).BehaviorProfile)
    (hmass : quittingTerminalOutcomeMass reward profile
      (some clockTerminal) = 1) :
    ∃ time : ℕ,
      0 < (quittingBehaviorStoppingLaw reward
        (profile clock) (some time)).toReal := by
  have htsum :
      ∑' time,
          quittingStageCoalitionMass reward profile time clockTerminal = 1 := by
    rw [tsum_quittingStageCoalitionMass]
    exact hmass
  have hexistsStage : ∃ time : ℕ,
      0 < quittingStageCoalitionMass reward profile time clockTerminal := by
    by_contra hnot
    push Not at hnot
    have hzero : (fun time =>
        quittingStageCoalitionMass reward profile time clockTerminal) = 0 := by
      funext time
      apply le_antisymm
      · exact hnot time
      · exact quittingStageCoalitionMass_nonneg
          reward profile time clockTerminal
    rw [hzero] at htsum
    have htsumZero : tsum (0 : ℕ → ℝ) = 0 := tsum_zero
    rw [htsumZero] at htsum
    norm_num at htsum
  obtain ⟨time, hstage⟩ := hexistsStage
  refine ⟨time, ?_⟩
  have hlive : 0 < quittingLiveMass reward profile time := by
    unfold quittingStageCoalitionMass at hstage
    nlinarith [quittingLiveRowCoalitionMass_nonneg
      reward profile time clockTerminal]
  have hliveLe : quittingLiveMass reward profile time ≤
      quittingLiveMass reward
        (quittingOpponentOnlyProfile reward profile atom) time := by
    have hle := quittingLiveMass_update_le_opponentOnly
      reward profile atom (profile atom) time
    simpa only [Function.update_eq_self] using hle
  have hsurvival : 0 < quittingHazardSurvival
      (quittingBehaviorLiveHazard reward (profile clock)) time := by
    rw [← opponentSurvivalWeight_atom_eq_clockHazardSurvival profile time,
      quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass]
    exact hlive.trans_le hliveLe
  have hquit : 0 <
      (quittingBehaviorLiveHazard reward (profile clock) time true).toReal := by
    simpa only [quittingProfileLiveRoot, quittingBehaviorLiveHazard] using
      positive_profileLiveRoot_quit_of_positive_stageCoalitionMass
        reward profile time clockTerminal clock (by simp [clockTerminal]) hstage
  rw [quittingBehaviorStoppingLaw_some_toReal,
    quittingHazardStopMass_eq_survival_mul_stop]
  positivity

theorem jointMass_eq_zero_of_clockMass_eq_one
    (profile : (quittingGame reward).BehaviorProfile)
    (hmass : quittingTerminalOutcomeMass reward profile
      (some clockTerminal) = 1) :
    quittingTerminalOutcomeMass reward profile (some jointTerminal) = 0 := by
  let mass := quittingTerminalOutcomeMass reward profile
  have hsimplex := quittingTerminalOutcomeMass_mem_stdSimplex reward profile
  have hsubset : ({some clockTerminal, some jointTerminal} :
      Finset (QuittingTerminalOutcome Player)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hpairLe :
      ∑ outcome ∈ ({some clockTerminal, some jointTerminal} :
          Finset (QuittingTerminalOutcome Player)), mass outcome ≤
        ∑ outcome, mass outcome := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun outcome _ _ => hsimplex.1 outcome)
  have hjointNonneg := hsimplex.1 (some jointTerminal)
  have hdistinct : (some clockTerminal : QuittingTerminalOutcome Player) ≠
      some jointTerminal := by
    intro heq
    exact jointTerminal_ne_clockTerminal (Option.some.inj heq).symm
  change mass (some clockTerminal) = 1 at hmass
  rw [hsimplex.2] at hpairLe
  simp [hdistinct, hmass] at hpairLe
  exact le_antisymm (by linarith) hjointNonneg

/-- The face forced by prescribed clock payoff `-1`.  The endpoint `alpha =
0` is excluded for every literal profile, although it lies in the closure. -/
def facePair (alpha : ℝ) : QuittingTerminalSemanticPair Player :=
  (fun who => if who = clock then -1 else 0,
    fun who => if who = clock then 0 else alpha)

def profileOfClockLaw (law : PMF (Option ℕ)) :
    (quittingGame reward).BehaviorProfile :=
  Function.update (quittingAlwaysContinueProfile reward) clock
    (quittingStoppingLawBehaviorStrategy reward clock law)

@[simp] theorem profileOfClockLaw_clockStoppingLaw (law : PMF (Option ℕ)) :
    quittingBehaviorStoppingLaw reward (profileOfClockLaw law clock) = law := by
  simp [profileOfClockLaw]

theorem profileOfClockLaw_payoff_clock_of_none_eq_zero
    (law : PMF (Option ℕ)) (hnone : (law none).toReal = 0) :
    quittingTerminalPayoff reward (profileOfClockLaw law) clock = -1 := by
  rw [profileOfClockLaw,
    quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime,
    quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy]
  let hazard := quittingBehaviorLiveHazard reward
    (quittingStoppingLawBehaviorStrategy reward clock law)
  let value : Option ℕ → ℝ := fun choice =>
    quittingTerminalPayoff reward
      (Function.update (quittingAlwaysContinueProfile reward) clock
        (quittingPureTimeBehaviorStrategy reward clock choice)) clock
  have hvalueBound : ∀ choice, |value choice| ≤ 1 := by
    intro choice
    cases choice with
    | none =>
        have hvalue : value none = 0 :=
          terminalPayoff_update_allContinue_clock_none_eq_zero
        rw [hvalue]
        norm_num
    | some time =>
        have hvalue : value (some time) = -1 :=
          terminalPayoff_update_allContinue_clock_some_eq_neg_one time
        rw [hvalue]
        norm_num
  have hstopping : quittingHazardStoppingLaw hazard = law := by
    change quittingBehaviorStoppingLaw reward
      (quittingStoppingLawBehaviorStrategy reward clock law) = law
    simp
  have hnever : quittingHazardNeverMass hazard = 0 := by
    rw [← quittingHazardStoppingLaw_none_toReal, hstopping, hnone]
  have hsum : ∑' time, quittingHazardStopMass hazard time = 1 := by
    have htotal := (hasSum_quittingHazardStopMass hazard).tsum_eq
    rw [hnever] at htotal
    linarith
  change Math.Probability.expect law value = -1
  rw [← hstopping,
    quittingHazardStoppingLaw_expect hazard value hvalueBound, hnever]
  simp_rw [show ∀ time, value (some time) = -1 by
    intro time
    exact terminalPayoff_update_allContinue_clock_some_eq_neg_one time]
  rw [zero_mul, zero_add]
  simp_rw [mul_neg, mul_one]
  rw [tsum_neg, hsum]

theorem profileOfClockLaw_payoff_atom (law : PMF (Option ℕ)) :
    quittingTerminalPayoff reward (profileOfClockLaw law) atom = 0 := by
  have hnever : quittingPureTimeBehaviorStrategy reward atom none =
      quittingAlwaysContinueStrategy reward atom := by
    funext time history
    rfl
  have hprofileAtom : profileOfClockLaw law atom =
      quittingAlwaysContinueStrategy reward atom := by
    simp [profileOfClockLaw, clock, atom]
    funext time history
    rfl
  have hsame : Function.update (profileOfClockLaw law) atom
      (quittingPureTimeBehaviorStrategy reward atom none) =
        profileOfClockLaw law := by
    funext who
    by_cases hwho : who = atom
    · subst who
      simp [hnever, hprofileAtom]
    · simp [Function.update_of_ne hwho]
  rw [← hsame]
  exact terminalPayoff_update_atom_never_eq_zero _

theorem profileOfClockLaw_cap_atom
    (law : PMF (Option ℕ)) (alpha : ℝ)
    (hupper : ∀ time, (law (some time)).toReal ≤ alpha)
    (hattain : ∃ time, (law (some time)).toReal = alpha) :
    quittingContinuationBestResponseValue reward (profileOfClockLaw law) atom =
      alpha := by
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  let values : Set ℝ := Set.range fun choice : Option ℕ =>
    quittingTerminalPayoff reward
      (Function.update (profileOfClockLaw law) atom
        (quittingPureTimeBehaviorStrategy reward atom choice)) atom
  have hbound : ∀ value ∈ values, value ≤ alpha := by
    rintro _ ⟨choice, rfl⟩
    cases choice with
    | none =>
        dsimp only
        rw [terminalPayoff_update_atom_never_eq_zero]
        obtain ⟨time, htime⟩ := hattain
        rw [← htime]
        exact ENNReal.toReal_nonneg
    | some time =>
        dsimp only
        rw [terminalPayoff_update_atom_pureTime_eq_stoppingLawAtom,
          profileOfClockLaw_clockStoppingLaw]
        exact hupper time
  have hbdd : BddAbove values := ⟨alpha, hbound⟩
  change sSup values = alpha
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) hbound
  · apply le_csSup hbdd
    obtain ⟨time, htime⟩ := hattain
    refine ⟨some time, ?_⟩
    dsimp only
    rw [terminalPayoff_update_atom_pureTime_eq_stoppingLawAtom,
      profileOfClockLaw_clockStoppingLaw, htime]

theorem facePair_mem_attainable_of_stoppingLaw
    (law : PMF (Option ℕ)) (alpha : ℝ)
    (hnone : (law none).toReal = 0)
    (hupper : ∀ time, (law (some time)).toReal ≤ alpha)
    (hattain : ∃ time, (law (some time)).toReal = alpha) :
    facePair alpha ∈ quittingAttainableTerminalSemanticPairs reward := by
  refine ⟨profileOfClockLaw law, ?_⟩
  unfold quittingTerminalSemanticPair facePair
  apply Prod.ext
  · funext who
    cases who
    · change quittingTerminalPayoff reward (profileOfClockLaw law) clock = -1
      exact profileOfClockLaw_payoff_clock_of_none_eq_zero law hnone
    · change quittingTerminalPayoff reward (profileOfClockLaw law) atom = 0
      exact profileOfClockLaw_payoff_atom law
  · funext who
    cases who
    · change quittingContinuationBestResponseValue reward
          (profileOfClockLaw law) clock = 0
      exact continuationBestResponse_clock_eq_zero _
    · change quittingContinuationBestResponseValue reward
          (profileOfClockLaw law) atom = alpha
      exact profileOfClockLaw_cap_atom law alpha hupper hattain

/-- A PMF wrapper around the current geometric measure. -/
def geometricNatLaw (probability : unitInterval) : PMF ℕ :=
  (ProbabilityTheory.geometricMeasure probability).toPMF

theorem geometricNatLaw_apply (probability : unitInterval)
    (hprobability : probability ≠ 0) (time : ℕ) :
    geometricNatLaw probability time = ENNReal.ofReal
      ((1 - probability : ℝ) ^ time * probability) := by
  rw [geometricNatLaw, MeasureTheory.Measure.toPMF_apply,
    ProbabilityTheory.geometricMeasure_singleton hprobability]

def geometricClockLaw (alpha : ℝ) (halphaPos : 0 < alpha)
    (halphaLe : alpha ≤ 1) : PMF (Option ℕ) :=
  let probability : unitInterval := ⟨alpha, halphaPos.le, halphaLe⟩
  (geometricNatLaw probability).map some

@[simp] theorem geometricClockLaw_none
    (alpha : ℝ) (halphaPos : 0 < alpha) (halphaLe : alpha ≤ 1) :
    geometricClockLaw alpha halphaPos halphaLe none = 0 := by
  rw [geometricClockLaw, PMF.map_apply]
  simp

theorem geometricClockLaw_some_toReal
    (alpha : ℝ) (halphaPos : 0 < alpha) (halphaLe : alpha ≤ 1)
    (time : ℕ) :
    (geometricClockLaw alpha halphaPos halphaLe (some time)).toReal =
      (1 - alpha) ^ time * alpha := by
  let probability : unitInterval := ⟨alpha, halphaPos.le, halphaLe⟩
  have hprobability : probability ≠ 0 := by
    intro heq
    exact halphaPos.ne' (congrArg Subtype.val heq)
  change (((geometricNatLaw probability).map some) (some time)).toReal = _
  rw [PMF.map_apply, tsum_eq_single time]
  · rw [if_pos rfl, geometricNatLaw_apply probability hprobability]
    rw [ENNReal.toReal_ofReal]
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr halphaLe) time)
      halphaPos.le
  · intro other hne
    simp [hne.symm]

theorem geometricClockLaw_some_toReal_le
    (alpha : ℝ) (halphaPos : 0 < alpha) (halphaLe : alpha ≤ 1)
    (time : ℕ) :
    (geometricClockLaw alpha halphaPos halphaLe (some time)).toReal ≤ alpha := by
  rw [geometricClockLaw_some_toReal]
  have hbase0 : 0 ≤ 1 - alpha := sub_nonneg.mpr halphaLe
  have hbase1 : 1 - alpha ≤ 1 := by linarith
  exact mul_le_of_le_one_left halphaPos.le (pow_le_one₀ hbase0 hbase1)

theorem geometricClockLaw_zero_toReal
    (alpha : ℝ) (halphaPos : 0 < alpha) (halphaLe : alpha ≤ 1) :
    (geometricClockLaw alpha halphaPos halphaLe (some 0)).toReal = alpha := by
  rw [geometricClockLaw_some_toReal]
  ring

/-- Every point of the open face is literally attained. -/
theorem facePair_mem_attainable
    (alpha : ℝ) (halphaPos : 0 < alpha) (halphaLe : alpha ≤ 1) :
    facePair alpha ∈ quittingAttainableTerminalSemanticPairs reward := by
  apply facePair_mem_attainable_of_stoppingLaw
      (geometricClockLaw alpha halphaPos halphaLe) alpha
  · simp
  · exact geometricClockLaw_some_toReal_le alpha halphaPos halphaLe
  · exact ⟨0, geometricClockLaw_zero_toReal alpha halphaPos halphaLe⟩

theorem semanticPair_eq_facePair_of_payoff_clock_eq_neg_one
    (profile : (quittingGame reward).BehaviorProfile)
    (hpayoff : quittingTerminalPayoff reward profile clock = -1) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      quittingTerminalSemanticPair reward profile = facePair alpha := by
  have hclockMass : quittingTerminalOutcomeMass reward profile
      (some clockTerminal) = 1 := by
    rw [terminalPayoff_clock_eq_neg_clockMass] at hpayoff
    linarith
  obtain ⟨time, htime⟩ :=
    exists_clockStoppingLawAtom_pos_of_clockMass_eq_one profile hclockMass
  let alpha := quittingContinuationBestResponseValue reward profile atom
  have halphaPos : 0 < alpha := by
    have hdeviation :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile atom
          (quittingPureTimeBehaviorStrategy reward atom (some time))
    rw [terminalPayoff_update_atom_pureTime_eq_stoppingLawAtom] at hdeviation
    exact htime.trans_le hdeviation
  have halphaLe : alpha ≤ 1 := continuationBestResponse_atom_le_one profile
  refine ⟨alpha, halphaPos, halphaLe, ?_⟩
  unfold quittingTerminalSemanticPair facePair
  apply Prod.ext
  · funext who
    cases who
    · change quittingTerminalPayoff reward profile clock = -1
      exact hpayoff
    · change quittingTerminalPayoff reward profile atom = 0
      rw [terminalPayoff_atom_eq_jointMass,
        jointMass_eq_zero_of_clockMass_eq_one profile hclockMass]
  · funext who
    cases who
    · change quittingContinuationBestResponseValue reward profile clock = 0
      exact continuationBestResponse_clock_eq_zero profile
    · change quittingContinuationBestResponseValue reward profile atom = alpha
      rfl

/-- On the exact clock-payoff face, the attainable set is precisely the open
one-parameter face with positive atom cap. -/
theorem attainable_inter_clock_payoff_face :
    quittingAttainableTerminalSemanticPairs reward ∩
        {pair | pair.1 clock = -1} =
      facePair '' Set.Ioc 0 1 := by
  ext pair
  constructor
  · rintro ⟨⟨profile, hprofile⟩, hclock⟩
    have hpayoff : quittingTerminalPayoff reward profile clock = -1 :=
      (congrArg
        (fun value : QuittingTerminalSemanticPair Player => value.1 clock)
        hprofile).trans hclock
    obtain ⟨alpha, halphaPos, halphaLe, hface⟩ :=
      semanticPair_eq_facePair_of_payoff_clock_eq_neg_one profile hpayoff
    exact ⟨alpha, ⟨halphaPos, halphaLe⟩, hface.symm.trans hprofile⟩
  · rintro ⟨alpha, ⟨halphaPos, halphaLe⟩, rfl⟩
    constructor
    · exact facePair_mem_attainable alpha halphaPos halphaLe
    · rfl

/-- No behavioral profile realizes the positive-debt limit pair.  The
candidate and the profitable deviation are unrestricted behavioral objects;
the deterministic quit time is extracted only after inspecting the
candidate's complete stopping law. -/
theorem limitPair_not_mem_attainable :
    limitPair ∉ quittingAttainableTerminalSemanticPairs reward := by
  rintro ⟨profile, hpair⟩
  have hclockPayoff := congrArg
    (fun pair : QuittingTerminalSemanticPair Player => pair.1 clock) hpair
  change quittingTerminalPayoff reward profile clock = -1 at hclockPayoff
  have hclockMass : quittingTerminalOutcomeMass reward profile
      (some clockTerminal) = 1 := by
    rw [terminalPayoff_clock_eq_neg_clockMass] at hclockPayoff
    linarith
  obtain ⟨time, htime⟩ :=
    exists_clockStoppingLawAtom_pos_of_clockMass_eq_one profile hclockMass
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile atom
        (quittingPureTimeBehaviorStrategy reward atom (some time))
  rw [terminalPayoff_update_atom_pureTime_eq_stoppingLawAtom] at hdeviation
  have hcap := congrArg
    (fun pair : QuittingTerminalSemanticPair Player => pair.2 atom) hpair
  change quittingContinuationBestResponseValue reward profile atom = 0 at hcap
  linarith

theorem limitPair_debtSum :
    quittingTerminalSemanticDebtSum limitPair = 1 := by
  unfold quittingTerminalSemanticDebtSum quittingTerminalSemanticDebt
  rw [Fintype.sum_bool]
  norm_num [limitPair, clock, atom]

/-- The literal attained image remains nonclosed after restricting to the
positive-debt half-space `D ≥ 1`. -/
theorem attainable_inter_debt_ge_one_not_closed :
    ¬ IsClosed (quittingAttainableTerminalSemanticPairs reward ∩
      {pair | 1 ≤ quittingTerminalSemanticDebtSum pair}) := by
  intro hclosed
  have hmem : ∀ n, approximatingPair n ∈
      quittingAttainableTerminalSemanticPairs reward ∩
        {pair | 1 ≤ quittingTerminalSemanticDebtSum pair} := by
    intro n
    constructor
    · exact ⟨profile n, profile_semanticPair n⟩
    · change 1 ≤ quittingTerminalSemanticDebtSum (approximatingPair n)
      rw [approximatingPair_debtSum]
      have hnonneg : (0 : ℝ) ≤ 1 / (n + 1 : ℝ) := by positivity
      linarith
  have hlimit := hclosed.mem_of_tendsto approximatingPair_tendsto_limitPair
    (Filter.Eventually.of_forall hmem)
  exact limitPair_not_mem_attainable hlimit.1

end PositiveDebtTerminalSemanticNonattainment

namespace OnePlayerTerminalSemanticMinimality

/-- The unique nonempty quitting coalition in the canonical one-player
game. -/
def terminal : {S : Finset Unit // S.Nonempty} :=
  ⟨{()}, by simp⟩

theorem terminal_eq (S : {S : Finset Unit // S.Nonempty}) : S = terminal := by
  apply Subtype.ext
  have hunit : () ∈ S.1 := by
    obtain ⟨who, hwho⟩ := S.2
    simpa [Subsingleton.elim who ()] using hwho
  exact Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hunit, fun who _ => Subsingleton.elim who ()⟩

local instance : Unique {S : Finset Unit // S.Nonempty} where
  default := terminal
  uniq := terminal_eq

/-- The one-player table's only terminal reward coordinate. -/
def rho (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit) : ℝ :=
  reward terminal ()

/-- Updating the unique player erases every dependence on the original
profile, including its full behavioral chronology. -/
theorem update_eq
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit)
    (first second : (quittingGame reward).BehaviorProfile)
    (deviation : (quittingGame reward).BehaviorStrategy ()) :
    Function.update first () deviation = Function.update second () deviation := by
  funext who
  have hwho : who = () := Subsingleton.elim _ _
  subst who
  simp

/-- In a one-player game, the unrestricted behavioral cap is independent of
the candidate profile and equals the better of quitting and Never. -/
theorem cap_eq
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingContinuationBestResponseValue reward profile () =
      max (rho reward) 0 := by
  let canonical := quittingStationaryProfile reward
    (QuittingSureSetOwnerRepair.quittingPureSetRoot (∅ : Finset Unit))
  have hinvariant : quittingContinuationBestResponseValue reward profile () =
      quittingContinuationBestResponseValue reward canonical () := by
    unfold quittingContinuationBestResponseValue
    apply congrArg sSup
    apply congrArg Set.range
    funext deviation
    rw [update_eq reward profile canonical deviation]
  rw [hinvariant, show canonical = quittingStationaryProfile reward
    (QuittingSureSetOwnerRepair.quittingPureSetRoot (∅ : Finset Unit)) from rfl,
    quittingContinuationBestResponseValue_pureSetRoot_eq]
  simp [rho, terminal, QuittingSureSetOwnerRepair.quittingSetReward]

/-- An arbitrary one-player behavioral profile is summarized by its eventual
quitting probability. -/
theorem payoff_eq
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile () =
      quittingTerminalOutcomeMass reward profile (some terminal) * rho reward := by
  have hmom := congrFun
    (quittingTerminalRewardMoment_outcomeMass reward profile) ()
  have hdefault : (default : {S : Finset Unit // S.Nonempty}) = terminal :=
    terminal_eq _
  simpa [quittingTerminalRewardMoment, quittingTerminalOutcomeReward, rho,
    hdefault] using hmom.symm

theorem mass_mem_Icc
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalOutcomeMass reward profile (some terminal) ∈
      Set.Icc (0 : ℝ) 1 :=
  mem_Icc_of_mem_stdSimplex
    (quittingTerminalOutcomeMass_mem_stdSimplex reward profile) _

/-- The closed semantic segment parametrized by eventual quitting
probability. -/
def semanticPair
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit) (p : ℝ) :
    QuittingTerminalSemanticPair Unit :=
  (fun _ => p * rho reward, fun _ => max (rho reward) 0)

/-- A literal behavioral realization of a prescribed eventual quitting
probability: quit at date zero in the target branch and Never in the source
branch. -/
def realization
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  let base := quittingAlwaysContinueProfile reward
  Function.update base ()
    (quittingStoppingLawMixtureBehaviorStrategy reward () (base ())
      (quittingPureTimeBehaviorStrategy reward () (some 0)) p hp0 hp1)

theorem realization_payoff
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingTerminalPayoff reward (realization reward p hp0 hp1) () =
      p * rho reward := by
  let base := quittingAlwaysContinueProfile reward
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward base () () (base ())
      (quittingPureTimeBehaviorStrategy reward () (some 0)) p hp0 hp1
  have htarget := quittingTerminalPayoff_update_pureSetRoot_quitNow
    reward (∅ : Finset Unit) ()
  rw [quittingStationaryProfile_pureSetRoot_empty] at htarget
  change quittingTerminalPayoff reward (realization reward p hp0 hp1) () = _
  change quittingTerminalPayoff reward (realization reward p hp0 hp1) () =
    (1 - p) * quittingTerminalPayoff reward
      (Function.update base () (base ())) () +
    p * quittingTerminalPayoff reward
      (Function.update base ()
        (quittingPureTimeBehaviorStrategy reward () (some 0))) () at haffine
  rw [Function.update_eq_self, quittingTerminalPayoff_quittingAlwaysContinue,
    htarget] at haffine
  simpa [rho, terminal, QuittingSureSetOwnerRepair.quittingSetReward] using haffine

theorem realization_semanticPair
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingTerminalSemanticPair reward (realization reward p hp0 hp1) =
      semanticPair reward p := by
  apply Prod.ext
  · funext who
    have hwho : who = () := Subsingleton.elim _ _
    subst who
    exact realization_payoff reward p hp0 hp1
  · funext who
    have hwho : who = () := Subsingleton.elim _ _
    subst who
    exact cap_eq reward (realization reward p hp0 hp1)

theorem profile_semanticPair_eq
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward profile = semanticPair reward
      (quittingTerminalOutcomeMass reward profile (some terminal)) := by
  apply Prod.ext
  · funext who
    have hwho : who = () := Subsingleton.elim _ _
    subst who
    exact payoff_eq reward profile
  · funext who
    have hwho : who = () := Subsingleton.elim _ _
    subst who
    exact cap_eq reward profile

/-- Every one-player table has exactly the closed semantic segment indexed by
eventual quitting probability. -/
theorem attainable_eq_closed_segment
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit) :
    quittingAttainableTerminalSemanticPairs reward =
      semanticPair reward '' Set.Icc 0 1 := by
  ext pair
  constructor
  · rintro ⟨profile, rfl⟩
    refine ⟨quittingTerminalOutcomeMass reward profile (some terminal),
      mass_mem_Icc reward profile, ?_⟩
    exact (profile_semanticPair_eq reward profile).symm
  · rintro ⟨p, ⟨hp0, hp1⟩, rfl⟩
    exact ⟨realization reward p hp0 hp1,
      realization_semanticPair reward p hp0 hp1⟩

theorem continuous_semanticPair
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit) :
    Continuous (semanticPair reward) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro who
    exact continuous_id.mul continuous_const
  · exact continuous_const

/-- Therefore one player cannot witness nonclosedness of the attained
terminal-semantic image. -/
theorem attainable_isClosed
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit) :
    IsClosed (quittingAttainableTerminalSemanticPairs reward) := by
  rw [attainable_eq_closed_segment]
  exact (isCompact_Icc.image (continuous_semanticPair reward)).isClosed

end OnePlayerTerminalSemanticMinimality

end GameTheory
