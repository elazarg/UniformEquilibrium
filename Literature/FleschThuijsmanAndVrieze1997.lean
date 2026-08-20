import UniformEquilibrium.Quitting.Classification.PlayerReindex
import UniformEquilibrium.Quitting.Examples.FTV.CyclicAdmissibleCycle
import UniformEquilibrium.Quitting.Paths.InfinitePathCompiler
import UniformEquilibrium.Quitting.Root.ApproximateFirstBranch
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler
import UniformEquilibrium.Quitting.Stationary.FullRateStationaryVerifier
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Flesch--Thuijsman--Vrieze (1997)

J. Flesch, F. Thuijsman and O. J. Vrieze, *Cyclic Markov Equilibria in
Stochastic Games*, International Journal of Game Theory 26 (1997), 303--314.
DOI: `10.1007/BF01263273`.  Public author-hosted copy:
`https://dke.maastrichtuniversity.nl/f.thuijsman/cyclic%20Markov%20equilibria.pdf`.

The paper studies one three-player recursive repeated game with one live action
profile.  `false` denotes Top, Left, and Near; `true` denotes Bottom, Right, and
Far.  The all-`false` row is the unique nonabsorbing row and has stage payoff
zero.  Every other row absorbs with the displayed terminal reward.

The repository's quitting-game terminal payoff is the exact adapter for this
recursive game: on every realized path the limiting average is the terminal
reward, or zero if absorption never occurs.  The checked finite-average
convergence statements below make the corresponding expected-average limit
explicit.  Claims not yet discharged by the imported interfaces remain
`sorry`, immediately preceded by the precise missing proof boundary.
-/

noncomputable section

namespace Literature.FleschThuijsmanAndVrieze1997

open Filter Set
open GameTheory GameTheory.StochasticGame
open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

abbrev Player := GameTheory.FTVCyclicMinimality.Player
abbrev Hazard := Set.Icc (0 : ℝ) 1

/-! ## Section 1: model and equilibrium notion

The paper starts with a finite stochastic game: at each state the players
independently choose actions, receive a state-and-action dependent stage reward,
and move according to a state-and-action dependent transition law.  Strategies
are behavioral and condition on the complete observed history.  A stationary
strategy depends only on the current state; a pure stationary strategy selects
one action at every state.  A Markov strategy may also depend on the stage.

For player `i`, initial state `s`, and profile `σ`, the paper evaluates the
payoff sequence by

`E_{s,σ}[liminf_{T→∞} T⁻¹ ∑_{m=1}^T Rᵢ_m]`.

A limiting-average `ε`-equilibrium is a profile whose payoff, from every initial
state, is within `ε` of every unilateral behavioral deviation.  An absorbing
state is never left.  A game is recursive when every nonabsorbing state has
stage payoff zero, and is a repeated game with absorbing states when it has one
nonabsorbing state.  The example below has all four properties used later:
finite actions, perfect monitoring, recursion, and one live state.
-/

/-! ## Section 2: the three-player game Γ -/

/-- The paper's terminal reward table, with `true` denoting the second action. -/
def terminalReward (action : Player → Bool) : Payoff Player :=
  GameTheory.FTVCyclicMinimality.terminalReward action

@[simp] theorem terminalReward_TLN :
    terminalReward ![false, false, false] = ![0, 0, 0] := by
  rfl

@[simp] theorem terminalReward_BLN :
    terminalReward ![true, false, false] = ![1, 3, 0] := by
  rfl

@[simp] theorem terminalReward_TRN :
    terminalReward ![false, true, false] = ![0, 1, 3] := by
  rfl

@[simp] theorem terminalReward_TLF :
    terminalReward ![false, false, true] = ![3, 0, 1] := by
  rfl

@[simp] theorem terminalReward_BRN :
    terminalReward ![true, true, false] = ![1, 0, 1] := by
  rfl

@[simp] theorem terminalReward_BLF :
    terminalReward ![true, false, true] = ![0, 1, 1] := by
  rfl

@[simp] theorem terminalReward_TRF :
    terminalReward ![false, true, true] = ![1, 1, 0] := by
  rfl

@[simp] theorem terminalReward_BRF :
    terminalReward ![true, true, true] = ![0, 0, 0] := by
  rfl

/-- The quitter-set presentation used by the repository is exactly the paper's
seven absorbing rows. -/
theorem ftvReward_quitters (action : Player → Bool)
    (h : (quittingQuitters action).Nonempty) :
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        ⟨quittingQuitters action, h⟩ =
      terminalReward action := by
  exact GameTheory.FTVCyclicAdmissibleCycle.ftvReward_quitters action h

/-- A Boolean coin whose `true` mass is the supplied hazard. -/
def coin (p : Hazard) : PMF Bool :=
  GameTheory.QuittingBoundedSurgeryDescentCounterexample.coin
    p.1 p.2.1 p.2.2

@[simp] theorem coin_true_toReal (p : Hazard) :
    (coin p true).toReal = p.1 := by
  exact GameTheory.QuittingBoundedSurgeryDescentCounterexample.coin_true_toReal
    p.1 p.2.1 p.2.2

@[simp] theorem coin_false_toReal (p : Hazard) :
    (coin p false).toReal = 1 - p.1 := by
  exact GameTheory.QuittingBoundedSurgeryDescentCounterexample.coin_false_toReal
    p.1 p.2.1 p.2.2

@[simp] theorem expect_coin (p : Hazard) (f : Bool → ℝ) :
    expect (coin p) f = p.1 * f true + (1 - p.1) * f false := by
  rw [expect_eq_sum, Fintype.sum_bool, coin_true_toReal,
    coin_false_toReal]

/-- A Markov profile is the paper's sequence of quit probabilities, indexed
from repository time zero rather than paper stage one. -/
abbrev MarkovProfile := ℕ → Player → Hazard

/-- The product root played at one date of a paper Markov profile. -/
def markovRoot (profile : MarkovProfile) (time : ℕ) :
    Player → PMF Bool :=
  fun who => coin (profile time who)

/-- The behavior-profile adapter for a paper Markov profile.  Histories after
absorption are irrelevant, and before absorption there is only one history. -/
def markovBehaviorProfile (profile : MarkovProfile) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  quittingRootSequenceProfile GameTheory.FTVCyclicAdmissibleCycle.ftvReward
    (markovRoot profile) 0

/-- Exact terminal `ε`-equilibrium for a paper Markov profile. -/
def IsMarkovEpsilonEquilibrium (ε : ℝ)
    (profile : MarkovProfile) : Prop :=
  (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
    (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) ε
    (markovBehaviorProfile profile)

/-- Read an arbitrary behavior profile on the unique live public history as
a paper Markov hazard sequence. -/
def markovization
    (profile :
      (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile) :
    MarkovProfile :=
  fun time who =>
    let marginal := quittingProfileLiveRoot
      GameTheory.FTVCyclicAdmissibleCycle.ftvReward profile time who
    ⟨(marginal true).toReal,
      ENNReal.toReal_nonneg,
      by
        have hsum := pmf_toReal_sum_one marginal
        rw [Fintype.sum_bool] at hsum
        have hfalse : 0 ≤ (marginal false).toReal := ENNReal.toReal_nonneg
        linarith⟩

/-- Markovization reproduces exactly the original live-path product roots. -/
theorem markovRoot_markovization
    (profile :
      (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile) :
    markovRoot (markovization profile) =
      quittingProfileLiveRoot
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward profile := by
  funext time who
  let marginal := quittingProfileLiveRoot
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward profile time who
  change coin (markovization profile time who) = marginal
  ext action
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  cases action with
  | false =>
      rw [coin_false_toReal]
      have hsum := pmf_toReal_sum_one marginal
      rw [Fintype.sum_bool] at hsum
      change 1 - (marginal true).toReal = (marginal false).toReal
      linarith
  | true =>
      rw [coin_true_toReal]
      change (marginal true).toReal = (marginal true).toReal
      rfl

/-- The behavior profile generated by the Markovization has the same live-root
sequence as the original profile. -/
theorem quittingProfileLiveRoot_markovization
    (profile :
      (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile) :
    quittingProfileLiveRoot GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (markovBehaviorProfile (markovization profile)) =
      quittingProfileLiveRoot
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward profile := by
  calc
    quittingProfileLiveRoot GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (markovBehaviorProfile (markovization profile)) =
      markovRoot (markovization profile) := by
        simp [markovBehaviorProfile]
    _ = quittingProfileLiveRoot
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward profile :=
      markovRoot_markovization profile

/-- Markovization preserves the prescribed terminal payoff vector. -/
theorem quittingTerminalPayoff_markovization
    (profile :
      (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile) :
    quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (markovBehaviorProfile (markovization profile)) =
      quittingTerminalPayoff
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward profile := by
  funext who
  calc
    quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (markovBehaviorProfile (markovization profile)) who =
      quittingRootSequenceTerminalValue
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (quittingProfileLiveRoot GameTheory.FTVCyclicAdmissibleCycle.ftvReward
(markovBehaviorProfile (markovization profile))) who 0 :=
      quittingTerminalPayoff_eq_rootSequence_profileLiveRoot
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward _ who
    _ = quittingRootSequenceTerminalValue
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (quittingProfileLiveRoot GameTheory.FTVCyclicAdmissibleCycle.ftvReward
profile) who 0 := by
      rw [quittingProfileLiveRoot_markovization]
    _ = quittingTerminalPayoff
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward profile who :=
      (quittingTerminalPayoff_eq_rootSequence_profileLiveRoot
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward profile who).symm

/-- Markovization preserves every unilateral terminal value and hence every
terminal `ε`-equilibrium inequality. -/
theorem isMarkovEpsilonEquilibrium_markovization
    (profile :
      (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile)
    {ε : ℝ}
    (h : (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward)
      ε profile) :
    IsMarkovEpsilonEquilibrium ε (markovization profile) := by
  intro who deviation
  calc
    quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (Function.update
(markovBehaviorProfile (markovization profile))
who deviation) who =
      quittingRootSequenceHazardTerminalValue
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (quittingProfileLiveRoot GameTheory.FTVCyclicAdmissibleCycle.ftvReward
(markovBehaviorProfile (markovization profile))) who
        (quittingBehaviorLiveHazard
GameTheory.FTVCyclicAdmissibleCycle.ftvReward deviation) 0 :=
      quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward _ who deviation
    _ = quittingRootSequenceHazardTerminalValue
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (quittingProfileLiveRoot GameTheory.FTVCyclicAdmissibleCycle.ftvReward
profile) who
        (quittingBehaviorLiveHazard
GameTheory.FTVCyclicAdmissibleCycle.ftvReward deviation) 0 := by
      rw [quittingProfileLiveRoot_markovization]
    _ = quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (Function.update profile who deviation) who :=
      (quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward profile who deviation).symm
    _ ≤ quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        profile who + ε := h who deviation
    _ = quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (markovBehaviorProfile (markovization profile)) who + ε := by
      rw [quittingTerminalPayoff_markovization]


/-- A stationary mixed profile is one hazard for each player. -/
abbrev StationaryProfile := Player → Hazard

/-- The product root of a paper stationary profile. -/
def stationaryRoot (profile : StationaryProfile) :
    Player → PMF Bool :=
  fun who => coin (profile who)

/-- The repository behavior profile generated by a paper stationary profile. -/
def stationaryBehaviorProfile (profile : StationaryProfile) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  quittingStationaryProfile GameTheory.FTVCyclicAdmissibleCycle.ftvReward
    (stationaryRoot profile)

/-- Exact terminal `ε`-equilibrium for a paper stationary profile. -/
def IsStationaryEpsilonEquilibrium (ε : ℝ)
    (profile : StationaryProfile) : Prop :=
  (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
    (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) ε
    (stationaryBehaviorProfile profile)

/-! For a Markov strategy triple `θ`, the paper writes `q_θ(a)` for the
probability of eventual absorption at absorbing row `a`, and
`γᵢ(θ)=∑_a q_θ(a)rᵢ(a)`.  The formula remains valid when total absorption
probability is below one because the never-absorbing payoff is zero.  This is
exactly the stopping-law definition underlying `quittingTerminalPayoff`.
-/

/-! ## Section 3: analysis -/

/-! ### The pure stationary best-reply reduction

The paper uses the unconditional fact that against stationary opponents a pure
stationary best reply exists. In this one-live-state game the two
outcome-relevant pure stationary alternatives are immediate Quit and Never
quit. The theorem below retains that restriction in its type. -/

/-! The contracting case is the two-endpoint stationary Snell calculation.  On
the saturated face, all opponents continue forever, so the full-rate cap is the
maximum of zero and the player's singleton reward. -/
/-- Against stationary opponents, immediate Quit or Never is a best reply. -/
theorem pureStationaryBestReply
    (root : Player → PMF Bool) (who : Player) :
    ∃ choice : Option ℕ,
      (choice = none ∨ choice = some 0) ∧
        ∀ deviation :
          (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorStrategy who,
          quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
              (Function.update
                (quittingStationaryProfile
                  GameTheory.FTVCyclicAdmissibleCycle.ftvReward root)
                who deviation) who ≤
            quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
              (Function.update
                (quittingStationaryProfile
                  GameTheory.FTVCyclicAdmissibleCycle.ftvReward root)
                who
                (quittingPureTimeBehaviorStrategy
                  GameTheory.FTVCyclicAdmissibleCycle.ftvReward who choice)) who := by
  classical
  let reward := GameTheory.FTVCyclicAdmissibleCycle.ftvReward
  by_cases hcontracts :
      quittingStationaryFixedOpponentsContinueMass root who < 1
  · obtain ⟨choice, hchoice, hattains⟩ :=
      exists_quitNow_or_never_terminalPayoff_eq_unilateralCap
        reward root who hcontracts
    refine ⟨choice, hchoice, fun deviation ↦ ?_⟩
    calc
      quittingTerminalPayoff reward
          (Function.update (quittingStationaryProfile reward root) who
            deviation) who ≤
          quittingStationaryUnilateralCap reward root who :=
        quittingTerminalPayoff_update_stationary_le_unilateralCap
          reward root who deviation hcontracts
      _ = quittingTerminalPayoff reward
          (Function.update (quittingStationaryProfile reward root) who
            (quittingPureTimeBehaviorStrategy reward who choice)) who :=
        hattains.symm
  · have hmass : quittingStationaryFixedOpponentsContinueMass root who = 1 := by
      have hle : quittingStationaryFixedOpponentsContinueMass root who ≤ 1 :=
        quittingStationaryContinueMass_le_one
          (Function.update root who (PMF.pure false))
      exact le_antisymm hle (not_lt.mp hcontracts)
    by_cases hsolo : reward (quittingSingletonTerminal who) who ≤ 0
    · refine ⟨none, Or.inl rfl, fun deviation ↦ ?_⟩
      have hcap := quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap
        reward root who deviation
      rw [quittingStationaryFullRateUnilateralCap_of_not_lt
        reward root who hcontracts, max_eq_left hsolo] at hcap
      calc
        quittingTerminalPayoff reward
            (Function.update (quittingStationaryProfile reward root) who
              deviation) who ≤ 0 := hcap
        _ = quittingTerminalPayoff reward
            (Function.update (quittingStationaryProfile reward root) who
              (quittingPureTimeBehaviorStrategy reward who none)) who := by
          rw [update_stationaryProfile_eq_update_alwaysContinue_of_fixedMass_eq_one
            reward root who _ hmass]
          rw [show quittingPureTimeBehaviorStrategy reward who none =
              quittingAlwaysContinueStrategy reward who by
            funext time history
            rfl]
          have hupdate : Function.update (quittingAlwaysContinueProfile reward) who
              (quittingAlwaysContinueStrategy reward who) =
                quittingAlwaysContinueProfile reward := by
            apply Function.update_eq_self
          rw [hupdate, quittingTerminalPayoff_quittingAlwaysContinue]
    · refine ⟨some 0, Or.inr rfl, fun deviation ↦ ?_⟩
      have hcap := quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap
        reward root who deviation
      rw [quittingStationaryFullRateUnilateralCap_of_not_lt
        reward root who hcontracts,
        max_eq_right (le_of_not_ge hsolo)] at hcap
      calc
        quittingTerminalPayoff reward
            (Function.update (quittingStationaryProfile reward root) who
              deviation) who ≤ reward (quittingSingletonTerminal who) who := hcap
        _ = quittingTerminalPayoff reward
            (Function.update (quittingStationaryProfile reward root) who
              (quittingPureTimeBehaviorStrategy reward who (some 0))) who := by
          rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
            quittingProfileLiveRoot_stationary,
            quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
          have hclose :=
            abs_quittingFixedOpponentsQuitValue_sub_continueMass_mul_solo_le
              reward (fun _ ↦ root) who 0 (quittingRewardBound reward)
              (quittingRewardBound_nonneg reward)
              (fun terminal ↦ abs_reward_le_quittingRewardBound reward terminal who)
          change |quittingFixedOpponentsQuitValue reward (fun _ ↦ root) who 0 -
              quittingStationaryFixedOpponentsContinueMass root who *
                reward (quittingSingletonTerminal who) who| ≤
            quittingRewardBound reward *
              (1 - quittingStationaryFixedOpponentsContinueMass root who) at hclose
          rw [hmass, one_mul, sub_self, mul_zero] at hclose
          have hzero : quittingFixedOpponentsQuitValue reward (fun _ ↦ root) who 0 -
              reward (quittingSingletonTerminal who) who = 0 :=
            abs_eq_zero.mp (le_antisymm hclose (abs_nonneg _))
          linarith

/-- Under strict opponent contraction the selected Snell cap is attained by
literal `Never` or immediate Quit; the restriction is retained in the theorem
type rather than erased behind an unrestricted `Option ℕ` witness. -/
theorem stationary_bestReply_is_quitNow_or_never_of_contracting
    (root : Player → PMF Bool) (who : Player)
    (hcontracts :
      quittingStationaryFixedOpponentsContinueMass root who < 1) :
    ∃ choice : Option ℕ,
      (choice = none ∨ choice = some 0) ∧
        quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
            (Function.update
              (quittingStationaryProfile
                GameTheory.FTVCyclicAdmissibleCycle.ftvReward root)
              who
              (quittingPureTimeBehaviorStrategy
                GameTheory.FTVCyclicAdmissibleCycle.ftvReward who choice)) who =
          quittingStationaryUnilateralCap
            GameTheory.FTVCyclicAdmissibleCycle.ftvReward root who := by
  let quitValue := quittingStationaryFixedOpponentsQuitValue
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward root who
  let continueReward := quittingStationaryFixedOpponentsContinueReward
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward root who
  let continueMass := quittingStationaryFixedOpponentsContinueMass root who
  by_cases hnever : quitValue ≤
      quittingStationaryNeverValue continueReward continueMass
  · refine ⟨none, Or.inl rfl, ?_⟩
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingProfileLiveRoot_stationary,
      quittingRootSequencePureTimeTerminalValue_const
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward root who hcontracts]
    change quittingStationaryNeverValue continueReward continueMass =
      quittingStationarySelectedCap quitValue continueReward continueMass
    exact (max_eq_right hnever).symm
  · refine ⟨some 0, Or.inr rfl, ?_⟩
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingProfileLiveRoot_stationary,
      quittingRootSequencePureTimeTerminalValue_const
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward root who hcontracts]
    change quittingStationaryPureTimeValue
        quitValue continueReward continueMass 0 =
      quittingStationarySelectedCap quitValue continueReward continueMass
    rw [quittingStationaryPureTimeValue]
    exact (max_eq_left (le_of_not_ge hnever)).symm

/-! The following formulas are the paper's one-stage stationary calculations,
expanded from the exact product root. -/

theorem stationaryRoot_quitPayoff_zero
    (profile : StationaryProfile) (value : Payoff Player) :
    quittingRootQuitPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        value (stationaryRoot profile) 0 = 1 - (profile 2).1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [stationaryRoot, GameTheory.FTVCyclicMinimality.terminalReward,
    expect_coin, expect_pure, Matrix.cons_val_two]
  all_goals ring

theorem stationaryRoot_quitPayoff_one
    (profile : StationaryProfile) (value : Payoff Player) :
    quittingRootQuitPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        value (stationaryRoot profile) 1 = 1 - (profile 0).1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [stationaryRoot, GameTheory.FTVCyclicMinimality.terminalReward,
    expect_coin, expect_pure, Matrix.cons_val_two]

theorem stationaryRoot_quitPayoff_two
    (profile : StationaryProfile) (value : Payoff Player) :
    quittingRootQuitPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        value (stationaryRoot profile) 2 = 1 - (profile 1).1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [stationaryRoot, GameTheory.FTVCyclicMinimality.terminalReward,
    expect_coin, expect_pure, Matrix.cons_val_two]
  all_goals ring

theorem stationaryRoot_continuePayoff_zero
    (profile : StationaryProfile) (value : Payoff Player) :
    quittingRootContinuePayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        value (stationaryRoot profile) 0 =
      (1 - (profile 1).1) * (1 - (profile 2).1) * value 0 +
        3 * (1 - (profile 1).1) * (profile 2).1 +
          (profile 1).1 * (profile 2).1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [stationaryRoot, GameTheory.FTVCyclicMinimality.terminalReward,
    expect_coin, expect_pure, Matrix.cons_val_two]
  all_goals ring

theorem stationaryRoot_continuePayoff_one
    (profile : StationaryProfile) (value : Payoff Player) :
    quittingRootContinuePayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        value (stationaryRoot profile) 1 =
      (1 - (profile 0).1) * (1 - (profile 2).1) * value 1 +
        3 * (profile 0).1 * (1 - (profile 2).1) +
          (profile 0).1 * (profile 2).1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [stationaryRoot, GameTheory.FTVCyclicMinimality.terminalReward,
    expect_coin, expect_pure, Matrix.cons_val_two]
  all_goals ring

theorem stationaryRoot_continuePayoff_two
    (profile : StationaryProfile) (value : Payoff Player) :
    quittingRootContinuePayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        value (stationaryRoot profile) 2 =
      (1 - (profile 0).1) * (1 - (profile 1).1) * value 2 +
        3 * (1 - (profile 0).1) * (profile 1).1 +
          (profile 0).1 * (profile 1).1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [stationaryRoot, GameTheory.FTVCyclicMinimality.terminalReward,
    expect_coin, expect_pure, Matrix.cons_val_two]
  all_goals ring

/-! ### Lemma 3.1: no stationary equilibrium -/

/-- The scalar conditions extracted in the paper's proof of Lemma 3.1.  The
boundary implications are the successive pure-best-reply implications.  The
three polynomial equations are the interior indifference equations after
clearing their positive absorption denominators. -/
structure StationaryNecessaryConditions (x y z : ℝ) : Prop where
  x_nonneg : 0 ≤ x
  x_le_one : x ≤ 1
  y_nonneg : 0 ≤ y
  y_le_one : y ≤ 1
  z_nonneg : 0 ≤ z
  z_le_one : z ≤ 1
  y_eq_one_of_x_eq_zero : x = 0 → y = 1
  z_eq_zero_of_y_eq_one : y = 1 → z = 0
  x_eq_one_of_z_eq_zero : z = 0 → x = 1
  y_eq_zero_of_x_eq_one : x = 1 → y = 0
  z_eq_one_of_y_eq_zero : y = 0 → z = 1
  x_eq_zero_of_z_eq_one : z = 1 → x = 0
  player_zero_indifference : 0 < x → x < 1 →
    y * (z ^ 2 + 1) = z ^ 2 + 2 * z
  player_one_indifference : 0 < y → y < 1 →
    z * (x ^ 2 + 1) = x ^ 2 + 2 * x
  player_two_indifference : 0 < z → z < 1 →
    x * (y ^ 2 + 1) = y ^ 2 + 2 * y

/-- The contradiction `y > z > x > y` in Lemma 3.1, including the two
boundary cycles, is fully formalized. -/
theorem not_exists_stationaryNecessaryConditions :
    ¬ ∃ x y z : ℝ, StationaryNecessaryConditions x y z := by
  rintro ⟨x, y, z, h⟩
  by_cases hx0 : x = 0
  · have hy1 := h.y_eq_one_of_x_eq_zero hx0
    have hz0 := h.z_eq_zero_of_y_eq_one hy1
    have hx1 := h.x_eq_one_of_z_eq_zero hz0
    linarith
  by_cases hx1 : x = 1
  · have hy0 := h.y_eq_zero_of_x_eq_one hx1
    have hz1 := h.z_eq_one_of_y_eq_zero hy0
    have hx0' := h.x_eq_zero_of_z_eq_one hz1
    linarith
  have hxpos : 0 < x := lt_of_le_of_ne h.x_nonneg (Ne.symm hx0)
  have hxlt : x < 1 := lt_of_le_of_ne h.x_le_one hx1
  have hy0 : y ≠ 0 := by
    intro hy0
    have hz1 := h.z_eq_one_of_y_eq_zero hy0
    exact hx0 (h.x_eq_zero_of_z_eq_one hz1)
  have hy1 : y ≠ 1 := by
    intro hy1
    have hz0 := h.z_eq_zero_of_y_eq_one hy1
    exact hx1 (h.x_eq_one_of_z_eq_zero hz0)
  have hz0 : z ≠ 0 := by
    intro hz0
    exact hx1 (h.x_eq_one_of_z_eq_zero hz0)
  have hz1 : z ≠ 1 := by
    intro hz1
    exact hx0 (h.x_eq_zero_of_z_eq_one hz1)
  have hypos : 0 < y := lt_of_le_of_ne h.y_nonneg (Ne.symm hy0)
  have hylt : y < 1 := lt_of_le_of_ne h.y_le_one hy1
  have hzpos : 0 < z := lt_of_le_of_ne h.z_nonneg (Ne.symm hz0)
  have hzlt : z < 1 := lt_of_le_of_ne h.z_le_one hz1
  have hy_gt_z : z < y := by
    have hprod : 0 < z * (1 - z) * (z + 1) :=
      mul_pos (mul_pos hzpos (sub_pos.mpr hzlt)) (by linarith)
    nlinarith [h.player_zero_indifference hxpos hxlt]
  have hz_gt_x : x < z := by
    have hprod : 0 < x * (1 - x) * (x + 1) :=
      mul_pos (mul_pos hxpos (sub_pos.mpr hxlt)) (by linarith)
    nlinarith [h.player_one_indifference hypos hylt]
  have hx_gt_y : y < x := by
    have hprod : 0 < y * (1 - y) * (y + 1) :=
      mul_pos (mul_pos hypos (sub_pos.mpr hylt)) (by linarith)
    nlinarith [h.player_two_indifference hzpos hzlt]
  linarith

/-! The proof below combines the generic stationary payoff fixed point and
endpoint-Nash characterization with the table's six boundary implications and
three interior indifference equations. -/
theorem stationaryEquilibrium_implies_necessaryConditions
    (profile : StationaryProfile)
    (h : IsStationaryEpsilonEquilibrium 0 profile) :
    StationaryNecessaryConditions
      (profile 0).1 (profile 1).1 (profile 2).1 := by
  let reward := GameTheory.FTVCyclicAdmissibleCycle.ftvReward
  let root := stationaryRoot profile
  let value : Payoff Player := fun who ↦
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) who
  have hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root) := by
    simpa [IsStationaryEpsilonEquilibrium, stationaryBehaviorProfile,
      reward, root] using h
  have hroot :=
    (isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary
      reward root).mp hnash |>.1
  let x : ℝ := (profile 0).1
  let y : ℝ := (profile 1).1
  let z : ℝ := (profile 2).1
  let d0 : ℝ := 1 - z -
    ((1 - y) * (1 - z) * value 0 + 3 * (1 - y) * z + y * z)
  let d1 : ℝ := 1 - x -
    ((1 - x) * (1 - z) * value 1 + 3 * x * (1 - z) + x * z)
  let d2 : ℝ := 1 - y -
    ((1 - x) * (1 - y) * value 2 + 3 * (1 - x) * y + x * y)
  have hd0 : quittingRootEndpointDifference reward value root 0 = d0 := by
    rw [quittingRootEndpointDifference]
    simpa [reward, root, x, y, z, d0] using
      congrArg₂ (· - ·)
        (stationaryRoot_quitPayoff_zero profile value)
        (stationaryRoot_continuePayoff_zero profile value)
  have hd1 : quittingRootEndpointDifference reward value root 1 = d1 := by
    rw [quittingRootEndpointDifference]
    simpa [reward, root, x, y, z, d1] using
      congrArg₂ (· - ·)
        (stationaryRoot_quitPayoff_one profile value)
        (stationaryRoot_continuePayoff_one profile value)
  have hd2 : quittingRootEndpointDifference reward value root 2 = d2 := by
    rw [quittingRootEndpointDifference]
    simpa [reward, root, x, y, z, d2] using
      congrArg₂ (· - ·)
        (stationaryRoot_quitPayoff_two profile value)
        (stationaryRoot_continuePayoff_two profile value)
  have he0 : (1 - x) * d0 ≤ 0 ∧ 0 ≤ x * d0 := by
    have hzero := hroot 0
    simp only [neg_zero] at hzero
    change (root 0 false).toReal *
          quittingRootEndpointDifference reward value root 0 ≤ 0 ∧
        0 ≤ (root 0 true).toReal *
          quittingRootEndpointDifference reward value root 0 at hzero
    rw [hd0] at hzero
    simpa [root, stationaryRoot, x] using hzero
  have he1 : (1 - y) * d1 ≤ 0 ∧ 0 ≤ y * d1 := by
    have hone := hroot 1
    simp only [neg_zero] at hone
    change (root 1 false).toReal *
          quittingRootEndpointDifference reward value root 1 ≤ 0 ∧
        0 ≤ (root 1 true).toReal *
          quittingRootEndpointDifference reward value root 1 at hone
    rw [hd1] at hone
    simpa [root, stationaryRoot, y] using hone
  have he2 : (1 - z) * d2 ≤ 0 ∧ 0 ≤ z * d2 := by
    have htwo := hroot 2
    simp only [neg_zero] at htwo
    change (root 2 false).toReal *
          quittingRootEndpointDifference reward value root 2 ≤ 0 ∧
        0 ≤ (root 2 true).toReal *
          quittingRootEndpointDifference reward value root 2 at htwo
    rw [hd2] at htwo
    simpa [root, stationaryRoot, z] using htwo
  have hv0 : value 0 =
      x * (1 - z) + (1 - x) *
        ((1 - y) * (1 - z) * value 0 + 3 * (1 - y) * z + y * z) := by
    calc
      value 0 = quittingRootSuccessorPayoff reward value root 0 :=
        quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root 0
      _ = _ := by
        rw [quittingRootSuccessorPayoff_eq_endpointMix]
        simp only [root, stationaryRoot, coin_true_toReal, coin_false_toReal]
        rw [show quittingRootQuitPayoff reward value (stationaryRoot profile) 0 =
              1 - z by simpa [reward, z] using
                stationaryRoot_quitPayoff_zero profile value,
          show quittingRootContinuePayoff reward value (stationaryRoot profile) 0 =
              (1 - y) * (1 - z) * value 0 + 3 * (1 - y) * z + y * z by
            simpa [reward, y, z] using
              stationaryRoot_continuePayoff_zero profile value]
  have hv1 : value 1 =
      y * (1 - x) + (1 - y) *
        ((1 - x) * (1 - z) * value 1 + 3 * x * (1 - z) + x * z) := by
    calc
      value 1 = quittingRootSuccessorPayoff reward value root 1 :=
        quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root 1
      _ = _ := by
        rw [quittingRootSuccessorPayoff_eq_endpointMix]
        simp only [root, stationaryRoot, coin_true_toReal, coin_false_toReal]
        rw [show quittingRootQuitPayoff reward value (stationaryRoot profile) 1 =
              1 - x by simpa [reward, x] using
                stationaryRoot_quitPayoff_one profile value,
          show quittingRootContinuePayoff reward value (stationaryRoot profile) 1 =
              (1 - x) * (1 - z) * value 1 + 3 * x * (1 - z) + x * z by
            simpa [reward, x, z] using
              stationaryRoot_continuePayoff_one profile value]
  have hv2 : value 2 =
      z * (1 - y) + (1 - z) *
        ((1 - x) * (1 - y) * value 2 + 3 * (1 - x) * y + x * y) := by
    calc
      value 2 = quittingRootSuccessorPayoff reward value root 2 :=
        quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root 2
      _ = _ := by
        rw [quittingRootSuccessorPayoff_eq_endpointMix]
        simp only [root, stationaryRoot, coin_true_toReal, coin_false_toReal]
        rw [show quittingRootQuitPayoff reward value (stationaryRoot profile) 2 =
              1 - y by simpa [reward, y] using
                stationaryRoot_quitPayoff_two profile value,
          show quittingRootContinuePayoff reward value (stationaryRoot profile) 2 =
              (1 - x) * (1 - y) * value 2 + 3 * (1 - x) * y + x * y by
            simpa [reward, x, y] using
              stationaryRoot_continuePayoff_two profile value]
  have hx0 : 0 ≤ x := (profile 0).2.1
  have hx1 : x ≤ 1 := (profile 0).2.2
  have hy0 : 0 ≤ y := (profile 1).2.1
  have hy1 : y ≤ 1 := (profile 1).2.2
  have hz0 : 0 ≤ z := (profile 2).2.1
  have hz1 : z ≤ 1 := (profile 2).2.2
  have hnotAllZero : ¬(x = 0 ∧ y = 0 ∧ z = 0) := by
    rintro ⟨hx, hy, hz⟩
    have hrootAll : root = quittingAllContinueRoot := by
      funext who
      apply Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      fin_cases who
      · simpa [root, stationaryRoot, x] using hx
      · simpa [root, stationaryRoot, y] using hy
      · simpa [root, stationaryRoot, z] using hz
    have hprofileAll : quittingStationaryProfile reward root =
        quittingAlwaysContinueProfile reward := by
      rw [hrootAll]
      rfl
    have hvalueZero : value 0 = 0 := by
      change quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) 0 = 0
      rw [hprofileAll]
      exact quittingTerminalPayoff_quittingAlwaysContinue reward 0
    dsimp [d0] at he0
    rw [hx, hy, hz, hvalueZero] at he0
    norm_num at he0
  have hxyImpliesZ (hx : x = 0) (hy : y < 1) : z = 0 := by
    have hydiff : 0 < 1 - y := sub_pos.mpr hy
    have hd1nonpos : d1 ≤ 0 := by
      by_contra hpositive
      have : 0 < (1 - y) * d1 :=
        mul_pos hydiff (lt_of_not_ge hpositive)
      linarith [he1.1]
    have hweighted : 1 ≤ (1 - z) * value 1 := by
      dsimp [d1] at hd1nonpos
      rw [hx] at hd1nonpos
      linarith
    have hvaluePos : 0 < value 1 := by
      by_contra hnonpos
      have hfactor : 0 ≤ 1 - z := sub_nonneg.mpr hz1
      have := mul_nonpos_of_nonneg_of_nonpos hfactor (le_of_not_gt hnonpos)
      linarith
    have hbalance : z * value 1 = y * d1 := by
      dsimp [d1]
      rw [hx] at hv1 ⊢
      linear_combination hv1
    have hleft : 0 ≤ z * value 1 := mul_nonneg hz0 hvaluePos.le
    have hright : y * d1 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hy0 hd1nonpos
    have hproduct : z * value 1 = 0 := by linarith
    exact (mul_eq_zero.mp hproduct).resolve_right hvaluePos.ne'
  have hyzImpliesX (hy : y = 0) (hz : z < 1) : x = 0 := by
    have hzdiff : 0 < 1 - z := sub_pos.mpr hz
    have hd2nonpos : d2 ≤ 0 := by
      by_contra hpositive
      have : 0 < (1 - z) * d2 :=
        mul_pos hzdiff (lt_of_not_ge hpositive)
      linarith [he2.1]
    have hweighted : 1 ≤ (1 - x) * value 2 := by
      dsimp [d2] at hd2nonpos
      rw [hy] at hd2nonpos
      linarith
    have hvaluePos : 0 < value 2 := by
      by_contra hnonpos
      have hfactor : 0 ≤ 1 - x := sub_nonneg.mpr hx1
      have := mul_nonpos_of_nonneg_of_nonpos hfactor (le_of_not_gt hnonpos)
      linarith
    have hbalance : x * value 2 = z * d2 := by
      dsimp [d2]
      rw [hy] at hv2 ⊢
      linear_combination hv2
    have hleft : 0 ≤ x * value 2 := mul_nonneg hx0 hvaluePos.le
    have hright : z * d2 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hz0 hd2nonpos
    have hproduct : x * value 2 = 0 := by linarith
    exact (mul_eq_zero.mp hproduct).resolve_right hvaluePos.ne'
  have hzxImpliesY (hz : z = 0) (hx : x < 1) : y = 0 := by
    have hxdiff : 0 < 1 - x := sub_pos.mpr hx
    have hd0nonpos : d0 ≤ 0 := by
      by_contra hpositive
      have : 0 < (1 - x) * d0 :=
        mul_pos hxdiff (lt_of_not_ge hpositive)
      linarith [he0.1]
    have hweighted : 1 ≤ (1 - y) * value 0 := by
      dsimp [d0] at hd0nonpos
      rw [hz] at hd0nonpos
      linarith
    have hvaluePos : 0 < value 0 := by
      by_contra hnonpos
      have hfactor : 0 ≤ 1 - y := sub_nonneg.mpr hy1
      have := mul_nonpos_of_nonneg_of_nonpos hfactor (le_of_not_gt hnonpos)
      linarith
    have hbalance : y * value 0 = x * d0 := by
      dsimp [d0]
      rw [hz] at hv0 ⊢
      linear_combination hv0
    have hleft : 0 ≤ y * value 0 := mul_nonneg hy0 hvaluePos.le
    have hright : x * d0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hx0 hd0nonpos
    have hproduct : y * value 0 = 0 := by linarith
    exact (mul_eq_zero.mp hproduct).resolve_right hvaluePos.ne'
  refine
    { x_nonneg := hx0
      x_le_one := hx1
      y_nonneg := hy0
      y_le_one := hy1
      z_nonneg := hz0
      z_le_one := hz1
      y_eq_one_of_x_eq_zero := ?_
      z_eq_zero_of_y_eq_one := ?_
      x_eq_one_of_z_eq_zero := ?_
      y_eq_zero_of_x_eq_one := ?_
      z_eq_one_of_y_eq_zero := ?_
      x_eq_zero_of_z_eq_one := ?_
      player_zero_indifference := ?_
      player_one_indifference := ?_
      player_two_indifference := ?_ }
  · change x = 0 → y = 1
    intro hx
    apply le_antisymm hy1
    by_contra hylt
    have hz := hxyImpliesZ hx (lt_of_not_ge hylt)
    have hy := hzxImpliesY hz (by linarith)
    exact hnotAllZero ⟨hx, hy, hz⟩
  · change y = 1 → z = 0
    intro hy
    have hd2neg : d2 < 0 := by
      dsimp [d2]
      rw [hy]
      ring_nf
      linarith only [hx1]
    by_cases hzZero : z = 0
    · exact hzZero
    · have hzpos : 0 < z := lt_of_le_of_ne hz0 (Ne.symm hzZero)
      have : z * d2 < 0 := mul_neg_of_pos_of_neg hzpos hd2neg
      linarith [he2.2]
  · change z = 0 → x = 1
    intro hz
    apply le_antisymm hx1
    by_contra hxlt
    have hy := hzxImpliesY hz (lt_of_not_ge hxlt)
    have hx := hyzImpliesX hy (by linarith)
    exact hnotAllZero ⟨hx, hy, hz⟩
  · change x = 1 → y = 0
    intro hx
    have hd1neg : d1 < 0 := by
      dsimp [d1]
      rw [hx]
      ring_nf
      linarith only [hz1]
    by_cases hyZero : y = 0
    · exact hyZero
    · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hyZero)
      have : y * d1 < 0 := mul_neg_of_pos_of_neg hypos hd1neg
      linarith [he1.2]
  · change y = 0 → z = 1
    intro hy
    apply le_antisymm hz1
    by_contra hzlt
    have hx := hyzImpliesX hy (lt_of_not_ge hzlt)
    have hz := hxyImpliesZ hx (by linarith)
    exact hnotAllZero ⟨hx, hy, hz⟩
  · change z = 1 → x = 0
    intro hz
    have hd0neg : d0 < 0 := by
      dsimp [d0]
      rw [hz]
      ring_nf
      linarith only [hy1]
    by_cases hxZero : x = 0
    · exact hxZero
    · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxZero)
      have : x * d0 < 0 := mul_neg_of_pos_of_neg hxpos hd0neg
      linarith [he0.2]
  · change 0 < x → x < 1 → y * (z ^ 2 + 1) = z ^ 2 + 2 * z
    intro hxp hxlt
    have hd0nonpos : d0 ≤ 0 := by
      by_contra hpositive
      have : 0 < (1 - x) * d0 :=
        mul_pos (sub_pos.mpr hxlt) (lt_of_not_ge hpositive)
      linarith [he0.1]
    have hd0nonneg : 0 ≤ d0 := by
      by_contra hnegative
      have : x * d0 < 0 := mul_neg_of_pos_of_neg hxp (lt_of_not_ge hnegative)
      linarith [he0.2]
    have hd0zero : d0 = 0 := le_antisymm hd0nonpos hd0nonneg
    have hcontinue :
        (1 - y) * (1 - z) * value 0 + 3 * (1 - y) * z + y * z =
          1 - z := by
      dsimp [d0] at hd0zero
      linarith
    have hvalue : value 0 = 1 - z := by
      rw [hcontinue] at hv0
      calc
        value 0 = x * (1 - z) + (1 - x) * (1 - z) := hv0
        _ = 1 - z := by ring
    dsimp [d0] at hd0zero
    rw [hvalue] at hd0zero
    linear_combination hd0zero
  · change 0 < y → y < 1 → z * (x ^ 2 + 1) = x ^ 2 + 2 * x
    intro hyp hylt
    have hd1nonpos : d1 ≤ 0 := by
      by_contra hpositive
      have : 0 < (1 - y) * d1 :=
        mul_pos (sub_pos.mpr hylt) (lt_of_not_ge hpositive)
      linarith [he1.1]
    have hd1nonneg : 0 ≤ d1 := by
      by_contra hnegative
      have : y * d1 < 0 := mul_neg_of_pos_of_neg hyp (lt_of_not_ge hnegative)
      linarith [he1.2]
    have hd1zero : d1 = 0 := le_antisymm hd1nonpos hd1nonneg
    have hcontinue :
        (1 - x) * (1 - z) * value 1 + 3 * x * (1 - z) + x * z =
          1 - x := by
      dsimp [d1] at hd1zero
      linarith
    have hvalue : value 1 = 1 - x := by
      rw [hcontinue] at hv1
      calc
        value 1 = y * (1 - x) + (1 - y) * (1 - x) := hv1
        _ = 1 - x := by ring
    dsimp [d1] at hd1zero
    rw [hvalue] at hd1zero
    linear_combination hd1zero
  · change 0 < z → z < 1 → x * (y ^ 2 + 1) = y ^ 2 + 2 * y
    intro hzp hzlt
    have hd2nonpos : d2 ≤ 0 := by
      by_contra hpositive
      have : 0 < (1 - z) * d2 :=
        mul_pos (sub_pos.mpr hzlt) (lt_of_not_ge hpositive)
      linarith [he2.1]
    have hd2nonneg : 0 ≤ d2 := by
      by_contra hnegative
      have : z * d2 < 0 := mul_neg_of_pos_of_neg hzp (lt_of_not_ge hnegative)
      linarith [he2.2]
    have hd2zero : d2 = 0 := le_antisymm hd2nonpos hd2nonneg
    have hcontinue :
        (1 - x) * (1 - y) * value 2 + 3 * (1 - x) * y + x * y =
          1 - y := by
      dsimp [d2] at hd2zero
      linarith
    have hvalue : value 2 = 1 - y := by
      rw [hcontinue] at hv2
      calc
        value 2 = z * (1 - y) + (1 - z) * (1 - y) := hv2
        _ = 1 - y := by ring
    dsimp [d2] at hd2zero
    rw [hvalue] at hd2zero
    linear_combination hd2zero

/-- **Lemma 3.1.** There is no stationary equilibrium in `Γ`. -/
theorem lemma3_1 :
    ¬ ∃ profile : StationaryProfile,
      IsStationaryEpsilonEquilibrium 0 profile := by
  rintro ⟨profile, hprofile⟩
  apply not_exists_stationaryNecessaryConditions
  exact ⟨(profile 0).1, (profile 1).1, (profile 2).1,
    stationaryEquilibrium_implies_necessaryConditions profile hprofile⟩

/-! ### Theorem 3.2: stationary approximate equilibria -/

/-- A stationary profile is an approximate equilibrium at one positive,
possibly large, error. -/
theorem exists_positive_stationaryEpsilonEquilibrium :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ profile : StationaryProfile,
        IsStationaryEpsilonEquilibrium ε profile := by
  let zeroHazard : Hazard := ⟨0, by norm_num⟩
  let profile : StationaryProfile := fun _ => zeroHazard
  let M := quittingRewardBound GameTheory.FTVCyclicAdmissibleCycle.ftvReward
  have hM : 0 < M := by
    have hthree := GameTheory.FTVCyclicAdmissibleCycle.three_le_quittingRewardBound
    dsimp [M]
    linarith
  refine ⟨2 * M, by positivity, profile, ?_⟩
  intro who deviation
  have hdev := abs_quittingTerminalPayoff_le_quittingRewardBound
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward
    (Function.update (stationaryBehaviorProfile profile) who deviation) who
  have hbase := abs_quittingTerminalPayoff_le_quittingRewardBound
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward
    (stationaryBehaviorProfile profile) who
  have hdev_le :
      quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
          (Function.update (stationaryBehaviorProfile profile) who deviation) who ≤
        M := by
    exact (le_abs_self _).trans (by simpa [M] using hdev)
  have hbase_le :
      -M ≤ quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
          (stationaryBehaviorProfile profile) who := by
    exact (abs_le.mp (by simpa [M] using hbase)).1
  linarith

/-- The literal printed all-positive-`ε` statement is false. -/
theorem theorem3_2_printed_refuted :
    ¬ (∀ ε : ℝ, 0 < ε →
      ¬ ∃ profile : StationaryProfile,
        IsStationaryEpsilonEquilibrium ε profile) := by
  rintro h
  obtain ⟨ε, hε, profile, hprofile⟩ :=
    exists_positive_stationaryEpsilonEquilibrium
  exact (h ε hε) ⟨profile, hprofile⟩

/-! The proof takes stationary `ε`-equilibria with `ε ↓ 0`, extracts a
convergent subsequence, and separates an absorbing limit from the singular
all-Continue limit.  The current API has the pointwise payoff formulas but not
that two-case compactness package. -/

/-- Corrected, proof-supported form of Theorem 3.2: stationary equilibria fail
below one positive threshold. -/
theorem theorem3_2_corrected :
    ∃ threshold : ℝ, 0 < threshold ∧
      ∀ ε : ℝ, 0 < ε → ε < threshold →
        ¬ ∃ profile : StationaryProfile,
          IsStationaryEpsilonEquilibrium ε profile := by
  sorry

/-! ### Theorem 3.3: the cyclic Markov equilibrium -/

/-- The periodic profile generated by the paper's three rows, from an arbitrary
initial phase. -/
def cyclicPhaseProfile (phase : Fin 3) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  quittingCyclicContinuationBlockProfile
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward 2
    GameTheory.FTVCyclicAdmissibleCycle.ftvBlock phase

/-- The three phase rows have the exact quit probabilities displayed in
Theorem 3.3. -/
theorem phaseRoot_quitProbability (c who : Player) :
    (GameTheory.FTVCyclicAdmissibleCycle.phaseRoot c who true).toReal =
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardQuitProb c who := by
  exact GameTheory.FTVCyclicAdmissibleCycle.phaseRoot_quitProbability c who

/-- Every phase shift of the displayed cycle is an exact terminal equilibrium,
against all behavioral deviations. -/
theorem cyclicPhaseProfile_isEquilibrium (phase : Fin 3) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) 0
      (cyclicPhaseProfile phase) := by
  exact isZeroAsymptoticNash_quittingCyclicContinuationBlockProfile
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward
    GameTheory.FTVCyclicMinimality.namedTarget 2
    GameTheory.FTVCyclicAdmissibleCycle.ftvBlock
    GameTheory.FTVCyclicAdmissibleCycle.ftvBlock_isQuittingCyclicContinuationBlock
    GameTheory.FTVCyclicAdmissibleCycle.isQuittingCycleAdmissible_ftvBlockCycle
    phase

/-- The terminal payoff of a phase shift is the corresponding promise vector. -/
theorem quittingTerminalPayoff_cyclicPhaseProfile (phase : Fin 3) :
    quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (cyclicPhaseProfile phase) =
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise phase := by
  have hvalue :=
    eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
      GameTheory.FTVCyclicAdmissibleCycle.ftvReward
      (quittingCyclicContinuationBlockCycle 2
        GameTheory.FTVCyclicAdmissibleCycle.ftvBlock)
      (quittingCyclicContinuationBlockValue 2
        GameTheory.FTVCyclicAdmissibleCycle.ftvBlock)
      (quittingCyclicContinuationBlock_policy
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        GameTheory.FTVCyclicMinimality.namedTarget 2
        GameTheory.FTVCyclicAdmissibleCycle.ftvBlock
        GameTheory.FTVCyclicAdmissibleCycle.ftvBlock_isQuittingCyclicContinuationBlock)
      (quittingCyclicContinuationBlock_prod_continueMass_lt_one
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        GameTheory.FTVCyclicMinimality.namedTarget 2
        GameTheory.FTVCyclicAdmissibleCycle.ftvBlock
        GameTheory.FTVCyclicAdmissibleCycle.ftvBlock_isQuittingCyclicContinuationBlock)
  rw [cyclicPhaseProfile, quittingCyclicContinuationBlockProfile,
    quittingTerminalPayoff_cyclicBehaviorProfile, ← hvalue]
  fin_cases phase <;> rfl

/-- The phase-zero profile is the explicit profile of Theorem 3.3. -/
def cyclicProfile :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  cyclicPhaseProfile 0

/-- **Theorem 3.3.** The displayed cyclic Markov profile is an equilibrium and
has reward `(1,2,1)`.  The checked Nash statement allows every behavioral
unilateral deviation, matching the paper's equilibrium notion. -/
theorem theorem3_3 :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
        (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) 0
        cyclicProfile ∧
      quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
          cyclicProfile =
        GameTheory.FTVCyclicMinimality.namedTarget := by
  constructor
  · exact cyclicPhaseProfile_isEquilibrium 0
  · simpa [cyclicProfile, cyclicPhaseProfile,
      GameTheory.FTVCyclicAdmissibleCycle.ftvCyclicProfile] using
      GameTheory.FTVCyclicAdmissibleCycle.quittingTerminalPayoff_ftvCyclicProfile

/-- The expected finite-horizon averages of the displayed profile converge
coordinatewise to `(1,2,1)`. -/
theorem tendsto_cyclicProfile_payoff (who : Player) :
    Tendsto
      (fun horizon : ℕ =>
        (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).finiteAveragePayoff
          none horizon cyclicProfile who)
      atTop (nhds (GameTheory.FTVCyclicMinimality.namedTarget who)) := by
  simpa [cyclicProfile, cyclicPhaseProfile,
    GameTheory.FTVCyclicAdmissibleCycle.ftvCyclicProfile] using
    GameTheory.FTVCyclicAdmissibleCycle.tendsto_finiteAveragePayoff_ftvCyclicProfile
      who

/-- The paper's tail beginning at stage `l`; only `l mod 3` matters. -/
def cyclicTailProfile (l : ℕ) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  cyclicPhaseProfile (Fin.ofNat 3 l)

/-- The post-Theorem-3.3 observation that every tail triple is again an
exact Markov equilibrium. -/
theorem cyclicTailProfile_isEquilibrium (l : ℕ) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) 0
      (cyclicTailProfile l) := by
  exact cyclicPhaseProfile_isEquilibrium (Fin.ofNat 3 l)

/-! The paper next repeats each active phase for `n` stages, with one hazard
`α` satisfying `(1-α)^n=1/2`.  Proving the claim in the current semantic API
requires a length-`3n` value word and its exact endpoint inequalities at every
intermediate stage.  The imported three-phase certificate contracts each
whole block but does not supply those intermediate promises.  This is the
precise missing adapter for the following statement. -/

def blockRoot (n : ℕ) (α : Hazard) (time : ℕ) : Player → PMF Bool :=
  fun who =>
    if who = Fin.ofNat 3 (time / n) then coin α else PMF.pure false

/-- The paper's block-repeated extension of Theorem 3.3. -/
theorem blockRepeatedEquilibrium
    (n : ℕ) (hn : 0 < n) (α : Hazard)
    (hα : (1 - α.1) ^ n = (1 / 2 : ℝ)) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) 0
      (quittingRootSequenceProfile
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (blockRoot n α) 0) := by
  sorry

/-! ### Theorem 3.4: all equilibria are cyclic -/

/-- At every stage, some player has positive quit probability. -/
def HasActivePlayerAtEveryStage (profile : MarkovProfile) : Prop :=
  ∀ time, ∃ who, 0 < (profile time who).1

/-- A precise form of "exactly one positive hazard, and the active players
appear cyclically in the order 1,2,3".  Consecutive stages may keep the same
owner; every run is eventually followed by the cyclic successor. -/
def HasCyclicSupport (profile : MarkovProfile) : Prop :=
  ∃ owner : ℕ → Player,
    (∀ time who, 0 < (profile time who).1 ↔ who = owner time) ∧
    (∀ time, owner (time + 1) = owner time ∨
      owner (time + 1) = GameTheory.FTVCyclicMinimality.nextThree (owner time)) ∧
    (∀ time, ∃ later, time < later ∧
      owner later = GameTheory.FTVCyclicMinimality.nextThree (owner time))

/-! Existing checked results cover a strict finite-period subcase:
`ExactCyclicPacket.existsUnique_activeRole` gives one active role per live
phase, `ExactCyclicPacket.period_ge_three` rules out periods one and two, and
`three_phase_rigidity` identifies the unique period-three packet anchored at
`(1,2,1)`.  They do not imply the paper's assertion for arbitrary aperiodic
Markov equilibria.  The missing proof is the six-step tail argument on pages
310--312, including the decreasing-minimum contradiction and the eventual
cyclic handoff. -/

/-- **Theorem 3.4.** Every normalized Markov equilibrium has cyclic support. -/
theorem theorem3_4 (profile : MarkovProfile)
    (hnonempty : HasActivePlayerAtEveryStage profile)
    (hequilibrium : IsMarkovEpsilonEquilibrium 0 profile) :
    HasCyclicSupport profile := by
  sorry

/-- Checked special case used in the period-three part of the paper's picture:
every live phase of an exact cyclic packet has a unique active player. -/
theorem exactCyclicPacket_existsUnique_activeRole
    {K : ℕ} [NeZero K]
    (packet : GameTheory.FTVCyclicMinimality.ExactCyclicPacket K)
    (phase : Fin K) :
    ∃! who : Player, 0 < packet.quitProb phase who := by
  exact packet.existsUnique_activeRole phase

/-- Checked lower bound for finite exact cyclic packets. -/
theorem exactCyclicPacket_period_ge_three
    {K : ℕ} [NeZero K]
    (packet : GameTheory.FTVCyclicMinimality.ExactCyclicPacket K) :
    3 ≤ K := by
  exact packet.period_ge_three

/-! ### Theorem 3.5: equilibrium reward set -/

/-- Equilibrium rewards in the paper's game.  Behavioral profiles are used in
this definition because every behavior profile is outcome-equivalent on the
unique live history to a Markov sequence. -/
def EquilibriumRewards : Set (Payoff Player) :=
  {payoff | ∃ profile :
      (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile,
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) 0
      profile ∧
    quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
      profile = payoff}

/-- The same reward set quantified directly over paper Markov profiles. -/
def MarkovEquilibriumRewards : Set (Payoff Player) :=
  {payoff | ∃ profile : MarkovProfile,
    IsMarkovEpsilonEquilibrium 0 profile ∧
      quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (markovBehaviorProfile profile) = payoff}

/-- In the one-live-state game, arbitrary behavioral equilibrium rewards and
paper Markov equilibrium rewards coincide.  The proof preserves both the
prescribed terminal payoff and every unilateral terminal value. -/
theorem equilibriumRewards_eq_markov :
    EquilibriumRewards = MarkovEquilibriumRewards := by
  apply Set.Subset.antisymm
  · rintro payoff ⟨profile, hequilibrium, hpayoff⟩
    refine ⟨markovization profile,
      isMarkovEpsilonEquilibrium_markovization profile hequilibrium, ?_⟩
    rw [quittingTerminalPayoff_markovization, hpayoff]
  · rintro payoff ⟨profile, hequilibrium, hpayoff⟩
    exact ⟨markovBehaviorProfile profile, hequilibrium, hpayoff⟩


/-- The set printed in Theorem 3.5. -/
def RewardRegion : Set (Payoff Player) :=
  {payoff |
    1 ≤ payoff 0 ∧ 1 ≤ payoff 1 ∧ 1 ≤ payoff 2 ∧
      payoff 0 + payoff 1 + payoff 2 = 4 ∧
      (payoff 0 = 1 ∨ payoff 1 = 1 ∨ payoff 2 = 1)}

/-- Divide a paper hazard by two. -/
def halfHazard (α : Hazard) : Hazard :=
  ⟨α.1 / 2, by
    constructor
    · linarith [α.2.1]
    · linarith [α.2.2]⟩

/-- A root at which only `owner` may quit. -/
def soloRoot (owner : Player) (p : Hazard) : Player → PMF Bool :=
  fun who => if who = owner then coin p else PMF.pure false

/-- The first row in the paper's construction of the edge reward with
parameter `α`; its active hazard is `α/2`. -/
def edgeRoot (owner : Player) (α : Hazard) : Player → PMF Bool :=
  soloRoot owner (halfHazard α)

/-- The reward produced by the first perturbed row followed by the standard
cycle at the successor phase. -/
def edgeTarget (owner : Player) (α : Hazard) : Payoff Player :=
  (halfHazard α).1 • GameTheory.FTVCyclicMinimality.soloReward owner +
    (1 - (halfHazard α).1) •
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise
        (GameTheory.FTVCyclicMinimality.nextThree owner)

/-- The profile used for the sufficiency half of Theorem 3.5. -/
def edgeProfile (owner : Player) (α : Hazard) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  quittingRootThenContinuationProfile
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward
    (edgeRoot owner α)
    (cyclicPhaseProfile (GameTheory.FTVCyclicMinimality.nextThree owner))

/-- Expected payoff of a row with one possible quitter. -/
theorem quittingRootSuccessorPayoff_soloRoot
    (owner : Player) (p : Hazard) (tail : Payoff Player) :
    quittingRootSuccessorPayoff
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward tail
        (soloRoot owner p) =
      p.1 • GameTheory.FTVCyclicMinimality.soloReward owner +
        (1 - p.1) • tail := by
  funext who
  change quittingRootExpectedPayoff
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward tail
      (soloRoot owner p) who = _
  unfold quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  fin_cases owner <;> fin_cases who <;>
    simp [soloRoot,
      GameTheory.FTVCyclicMinimality.terminalReward,
      GameTheory.FTVCyclicMinimality.soloReward,
      Matrix.cons_val_two, expect_pure]

/-- Endpoint differences at the perturbed first row. -/
theorem endpointDifference_edgeRoot
    (owner : Player) (α : Hazard) (who : Player) :
    quittingRootEndpointDifference
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise
          (GameTheory.FTVCyclicMinimality.nextThree owner))
        (edgeRoot owner α) who =
      if who = owner then 0
      else if who = GameTheory.FTVCyclicMinimality.nextThree owner then
        -(3 * α.1 / 2)
      else α.1 - 1 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3,
    Math.PMFProduct.expect_pmfPi_fin3]
  fin_cases owner <;> fin_cases who <;>
    simp [edgeRoot, soloRoot, halfHazard,
      GameTheory.FTVCyclicMinimality.terminalReward,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise,
      GameTheory.FTVCyclicMinimality.nextThree,
      Matrix.cons_val_two, expect_pure] <;> ring

/-- The perturbed first row is exact endpoint Nash against the successor
promise for every `α∈[0,1]`. -/
theorem isZeroEndpointNash_edgeRoot
    (owner : Player) (α : Hazard) :
    IsεQuittingRootEndpointNash
      GameTheory.FTVCyclicAdmissibleCycle.ftvReward
      (GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise
        (GameTheory.FTVCyclicMinimality.nextThree owner))
      0 (edgeRoot owner α) := by
  intro who
  rw [endpointDifference_edgeRoot]
  fin_cases owner <;> fin_cases who <;>
    simp [edgeRoot, soloRoot, halfHazard,
      GameTheory.FTVCyclicMinimality.nextThree] <;>
    nlinarith [α.2.1, α.2.2]

/-- The perturbed-first-row construction is an exact equilibrium. -/
theorem edgeProfile_isEquilibrium (owner : Player) (α : Hazard) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) 0
      (edgeProfile owner α) := by
  have h :=
    isεAsymptoticNash_quittingRootThenContinuation_of_endpointNash_target_close
      GameTheory.FTVCyclicAdmissibleCycle.ftvReward
      (edgeRoot owner α)
      (cyclicPhaseProfile
        (GameTheory.FTVCyclicMinimality.nextThree owner))
      (GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise
        (GameTheory.FTVCyclicMinimality.nextThree owner))
      (η := 0) (ε := 0) (δ := 0) (by norm_num) (by norm_num)
      (isZeroEndpointNash_edgeRoot owner α)
      (cyclicPhaseProfile_isEquilibrium
        (GameTheory.FTVCyclicMinimality.nextThree owner))
      (by
        intro who
        rw [quittingTerminalPayoff_cyclicPhaseProfile]
        norm_num)
  simpa [edgeProfile] using h

/-- The construction realizes its displayed edge target. -/
theorem quittingTerminalPayoff_edgeProfile
    (owner : Player) (α : Hazard) :
    quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (edgeProfile owner α) =
      edgeTarget owner α := by
  funext who
  rw [edgeProfile, quittingTerminalPayoff_rootThenContinuation_eq,
    quittingTerminalPayoff_cyclicPhaseProfile]
  change quittingRootSuccessorPayoff
      GameTheory.FTVCyclicAdmissibleCycle.ftvReward
      (GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise
        (GameTheory.FTVCyclicMinimality.nextThree owner))
      (soloRoot owner (halfHazard α)) who = _
  rw [quittingRootSuccessorPayoff_soloRoot]
  rfl

@[simp] theorem edgeTarget_zero (α : Hazard) :
    edgeTarget 0 α = ![1, 1 + α.1, 2 - α.1] := by
  funext who
  fin_cases who <;>
    simp [edgeTarget, halfHazard,
      GameTheory.FTVCyclicMinimality.soloReward,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise,
      GameTheory.FTVCyclicMinimality.nextThree] <;> ring

@[simp] theorem edgeTarget_one (α : Hazard) :
    edgeTarget 1 α = ![2 - α.1, 1, 1 + α.1] := by
  funext who
  fin_cases who <;>
    simp [edgeTarget, halfHazard,
      GameTheory.FTVCyclicMinimality.soloReward,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise,
      GameTheory.FTVCyclicMinimality.nextThree] <;> ring

@[simp] theorem edgeTarget_two (α : Hazard) :
    edgeTarget 2 α = ![1 + α.1, 2 - α.1, 1] := by
  funext who
  fin_cases who <;>
    simp [edgeTarget, halfHazard,
      GameTheory.FTVCyclicMinimality.soloReward,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise,
      GameTheory.FTVCyclicMinimality.nextThree] <;> ring

/-- Every displayed edge target is feasible. -/
theorem edgeTarget_mem_equilibriumRewards
    (owner : Player) (α : Hazard) :
    edgeTarget owner α ∈ EquilibriumRewards := by
  exact ⟨edgeProfile owner α,
    edgeProfile_isEquilibrium owner α,
    quittingTerminalPayoff_edgeProfile owner α⟩

/-- The paper's construction proves the full sufficiency half of Theorem 3.5. -/
theorem rewardRegion_subset_equilibriumRewards :
    RewardRegion ⊆ EquilibriumRewards := by
  intro payoff hpayoff
  rcases hpayoff with ⟨h0, h1, h2, hsum, hface⟩
  rcases hface with hu | hv | hw
  · let α : Hazard := ⟨payoff 1 - 1, by
      constructor <;> linarith⟩
    have htarget : edgeTarget 0 α = payoff := by
      rw [edgeTarget_zero]
      funext who
      fin_cases who <;> simp [α] <;> linarith
    simpa only [htarget] using edgeTarget_mem_equilibriumRewards 0 α
  · let α : Hazard := ⟨payoff 2 - 1, by
      constructor <;> linarith⟩
    have htarget : edgeTarget 1 α = payoff := by
      rw [edgeTarget_one]
      funext who
      fin_cases who <;> simp [α] <;> linarith
    simpa only [htarget] using edgeTarget_mem_equilibriumRewards 1 α
  · let α : Hazard := ⟨payoff 0 - 1, by
      constructor <;> linarith⟩
    have htarget : edgeTarget 2 α = payoff := by
      rw [edgeTarget_two]
      funext who
      fin_cases who <;> simp [α] <;> linarith
    simpa only [htarget] using edgeTarget_mem_equilibriumRewards 2 α

/-! By `equilibriumRewards_eq_markov`, the
behavior-to-Markov semantic reduction is now closed.  The remaining necessity
proof is the paper's six-step tail argument from Theorem 3.4 followed by the
first-active-run payoff accounting: one coordinate is `1`, the other two are at
least `1`, and the total reward is `4`. -/
theorem theorem3_5_necessity :
    EquilibriumRewards ⊆ RewardRegion := by
  sorry

/-- **Theorem 3.5.** The feasible equilibrium rewards are exactly the three
closed edges printed in the paper. -/
theorem theorem3_5 :
    EquilibriumRewards = RewardRegion := by
  apply Set.Subset.antisymm
  · exact theorem3_5_necessity
  · exact rewardRegion_subset_equilibriumRewards

/-! ## Final remark

After Theorem 3.5 the paper remarks, without proof, that every `2×2×2`
recursive repeated game with one nonabsorbing row has an `ε`-equilibrium.
Relabeling the live actions as Continue identifies this class with arbitrary
three-player quitting reward tables.  The repository now proves the stronger
uniform-equilibrium-payoff theorem for every three-player quitting game and
converts it to terminal `ε`-Nash profiles at every positive error. -/
/-- The paper's final existence remark, discharged by the repository's general
three-player uniform-payoff theorem and terminal selection. -/
theorem finalExistenceRemark
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile := by
  obtain ⟨target, htarget⟩ :=
    quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three
      (ι := Player) (by simp [Player]) reward
  exact quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff
    reward target htarget ε hε

end Literature.FleschThuijsmanAndVrieze1997
