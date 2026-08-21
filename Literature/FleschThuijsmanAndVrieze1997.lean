import UniformEquilibrium.Quitting.Classification.PlayerReindex
import UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed
import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic
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

abbrev Player := FTV.CyclicMinimality.Player
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
  FTV.CyclicMinimality.terminalReward action

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
    FTV.CyclicAdmissibleCycle.ftvReward
        ⟨quittingQuitters action, h⟩ =
      terminalReward action := by
  exact FTV.CyclicAdmissibleCycle.ftvReward_quitters action h

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
    (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  quittingRootSequenceProfile FTV.CyclicAdmissibleCycle.ftvReward
    (markovRoot profile) 0

/-- Exact terminal `ε`-equilibrium for a paper Markov profile. -/
def IsMarkovEpsilonEquilibrium (ε : ℝ)
    (profile : MarkovProfile) : Prop :=
  (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
    (quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward) ε
    (markovBehaviorProfile profile)

/-- Read an arbitrary behavior profile on the unique live public history as
a paper Markov hazard sequence. -/
def markovization
    (profile :
      (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).BehaviorProfile) :
    MarkovProfile :=
  fun time who =>
    let marginal := quittingProfileLiveRoot
      FTV.CyclicAdmissibleCycle.ftvReward profile time who
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
      (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).BehaviorProfile) :
    markovRoot (markovization profile) =
      quittingProfileLiveRoot
        FTV.CyclicAdmissibleCycle.ftvReward profile := by
  funext time who
  let marginal := quittingProfileLiveRoot
    FTV.CyclicAdmissibleCycle.ftvReward profile time who
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
      (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).BehaviorProfile) :
    quittingProfileLiveRoot FTV.CyclicAdmissibleCycle.ftvReward
        (markovBehaviorProfile (markovization profile)) =
      quittingProfileLiveRoot
        FTV.CyclicAdmissibleCycle.ftvReward profile := by
  calc
    quittingProfileLiveRoot FTV.CyclicAdmissibleCycle.ftvReward
        (markovBehaviorProfile (markovization profile)) =
      markovRoot (markovization profile) := by
        simp [markovBehaviorProfile]
    _ = quittingProfileLiveRoot
        FTV.CyclicAdmissibleCycle.ftvReward profile :=
      markovRoot_markovization profile

/-- Markovization preserves the prescribed terminal payoff vector. -/
theorem quittingTerminalPayoff_markovization
    (profile :
      (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).BehaviorProfile) :
    quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
        (markovBehaviorProfile (markovization profile)) =
      quittingTerminalPayoff
        FTV.CyclicAdmissibleCycle.ftvReward profile := by
  funext who
  calc
    quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
        (markovBehaviorProfile (markovization profile)) who =
      quittingRootSequenceTerminalValue
        FTV.CyclicAdmissibleCycle.ftvReward
        (quittingProfileLiveRoot FTV.CyclicAdmissibleCycle.ftvReward
(markovBehaviorProfile (markovization profile))) who 0 :=
      quittingTerminalPayoff_eq_rootSequence_profileLiveRoot
        FTV.CyclicAdmissibleCycle.ftvReward _ who
    _ = quittingRootSequenceTerminalValue
        FTV.CyclicAdmissibleCycle.ftvReward
        (quittingProfileLiveRoot FTV.CyclicAdmissibleCycle.ftvReward
profile) who 0 := by
      rw [quittingProfileLiveRoot_markovization]
    _ = quittingTerminalPayoff
        FTV.CyclicAdmissibleCycle.ftvReward profile who :=
      (quittingTerminalPayoff_eq_rootSequence_profileLiveRoot
        FTV.CyclicAdmissibleCycle.ftvReward profile who).symm

/-- Markovization preserves every unilateral terminal value and hence every
terminal `ε`-equilibrium inequality. -/
theorem isMarkovEpsilonEquilibrium_markovization
    (profile :
      (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).BehaviorProfile)
    {ε : ℝ}
    (h : (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward)
      ε profile) :
    IsMarkovEpsilonEquilibrium ε (markovization profile) := by
  intro who deviation
  calc
    quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
        (Function.update
(markovBehaviorProfile (markovization profile))
who deviation) who =
      quittingRootSequenceHazardTerminalValue
        FTV.CyclicAdmissibleCycle.ftvReward
        (quittingProfileLiveRoot FTV.CyclicAdmissibleCycle.ftvReward
(markovBehaviorProfile (markovization profile))) who
        (quittingBehaviorLiveHazard
FTV.CyclicAdmissibleCycle.ftvReward deviation) 0 :=
      quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
        FTV.CyclicAdmissibleCycle.ftvReward _ who deviation
    _ = quittingRootSequenceHazardTerminalValue
        FTV.CyclicAdmissibleCycle.ftvReward
        (quittingProfileLiveRoot FTV.CyclicAdmissibleCycle.ftvReward
profile) who
        (quittingBehaviorLiveHazard
FTV.CyclicAdmissibleCycle.ftvReward deviation) 0 := by
      rw [quittingProfileLiveRoot_markovization]
    _ = quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
        (Function.update profile who deviation) who :=
      (quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
        FTV.CyclicAdmissibleCycle.ftvReward profile who deviation).symm
    _ ≤ quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
        profile who + ε := h who deviation
    _ = quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
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
    (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  quittingStationaryProfile FTV.CyclicAdmissibleCycle.ftvReward
    (stationaryRoot profile)

/-- Exact terminal `ε`-equilibrium for a paper stationary profile. -/
def IsStationaryEpsilonEquilibrium (ε : ℝ)
    (profile : StationaryProfile) : Prop :=
  (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
    (quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward) ε
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
          (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).BehaviorStrategy who,
          quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
              (Function.update
                (quittingStationaryProfile
                  FTV.CyclicAdmissibleCycle.ftvReward root)
                who deviation) who ≤
            quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
              (Function.update
                (quittingStationaryProfile
                  FTV.CyclicAdmissibleCycle.ftvReward root)
                who
                (quittingPureTimeBehaviorStrategy
                  FTV.CyclicAdmissibleCycle.ftvReward who choice)) who := by
  classical
  let reward := FTV.CyclicAdmissibleCycle.ftvReward
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
        quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
            (Function.update
              (quittingStationaryProfile
                FTV.CyclicAdmissibleCycle.ftvReward root)
              who
              (quittingPureTimeBehaviorStrategy
                FTV.CyclicAdmissibleCycle.ftvReward who choice)) who =
          quittingStationaryUnilateralCap
            FTV.CyclicAdmissibleCycle.ftvReward root who := by
  let quitValue := quittingStationaryFixedOpponentsQuitValue
    FTV.CyclicAdmissibleCycle.ftvReward root who
  let continueReward := quittingStationaryFixedOpponentsContinueReward
    FTV.CyclicAdmissibleCycle.ftvReward root who
  let continueMass := quittingStationaryFixedOpponentsContinueMass root who
  by_cases hnever : quitValue ≤
      quittingStationaryNeverValue continueReward continueMass
  · refine ⟨none, Or.inl rfl, ?_⟩
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingProfileLiveRoot_stationary,
      quittingRootSequencePureTimeTerminalValue_const
        FTV.CyclicAdmissibleCycle.ftvReward root who hcontracts]
    change quittingStationaryNeverValue continueReward continueMass =
      quittingStationarySelectedCap quitValue continueReward continueMass
    exact (max_eq_right hnever).symm
  · refine ⟨some 0, Or.inr rfl, ?_⟩
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingProfileLiveRoot_stationary,
      quittingRootSequencePureTimeTerminalValue_const
        FTV.CyclicAdmissibleCycle.ftvReward root who hcontracts]
    change quittingStationaryPureTimeValue
        quitValue continueReward continueMass 0 =
      quittingStationarySelectedCap quitValue continueReward continueMass
    rw [quittingStationaryPureTimeValue]
    exact (max_eq_left (le_of_not_ge hnever)).symm

/-! The following formulas are the paper's one-stage stationary calculations,
expanded from the exact product root. -/

theorem stationaryRoot_quitPayoff_zero
    (profile : StationaryProfile) (value : Payoff Player) :
    quittingRootQuitPayoff FTV.CyclicAdmissibleCycle.ftvReward
        value (stationaryRoot profile) 0 = 1 - (profile 2).1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [stationaryRoot, FTV.CyclicMinimality.terminalReward,
    expect_coin, expect_pure, Matrix.cons_val_two]
  all_goals ring

theorem stationaryRoot_quitPayoff_one
    (profile : StationaryProfile) (value : Payoff Player) :
    quittingRootQuitPayoff FTV.CyclicAdmissibleCycle.ftvReward
        value (stationaryRoot profile) 1 = 1 - (profile 0).1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [stationaryRoot, FTV.CyclicMinimality.terminalReward,
    expect_coin, expect_pure, Matrix.cons_val_two]

theorem stationaryRoot_quitPayoff_two
    (profile : StationaryProfile) (value : Payoff Player) :
    quittingRootQuitPayoff FTV.CyclicAdmissibleCycle.ftvReward
        value (stationaryRoot profile) 2 = 1 - (profile 1).1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [stationaryRoot, FTV.CyclicMinimality.terminalReward,
    expect_coin, expect_pure, Matrix.cons_val_two]
  all_goals ring

theorem stationaryRoot_continuePayoff_zero
    (profile : StationaryProfile) (value : Payoff Player) :
    quittingRootContinuePayoff FTV.CyclicAdmissibleCycle.ftvReward
        value (stationaryRoot profile) 0 =
      (1 - (profile 1).1) * (1 - (profile 2).1) * value 0 +
        3 * (1 - (profile 1).1) * (profile 2).1 +
          (profile 1).1 * (profile 2).1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [stationaryRoot, FTV.CyclicMinimality.terminalReward,
    expect_coin, expect_pure, Matrix.cons_val_two]
  all_goals ring

theorem stationaryRoot_continuePayoff_one
    (profile : StationaryProfile) (value : Payoff Player) :
    quittingRootContinuePayoff FTV.CyclicAdmissibleCycle.ftvReward
        value (stationaryRoot profile) 1 =
      (1 - (profile 0).1) * (1 - (profile 2).1) * value 1 +
        3 * (profile 0).1 * (1 - (profile 2).1) +
          (profile 0).1 * (profile 2).1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [stationaryRoot, FTV.CyclicMinimality.terminalReward,
    expect_coin, expect_pure, Matrix.cons_val_two]
  all_goals ring

theorem stationaryRoot_continuePayoff_two
    (profile : StationaryProfile) (value : Payoff Player) :
    quittingRootContinuePayoff FTV.CyclicAdmissibleCycle.ftvReward
        value (stationaryRoot profile) 2 =
      (1 - (profile 0).1) * (1 - (profile 1).1) * value 2 +
        3 * (1 - (profile 0).1) * (profile 1).1 +
          (profile 0).1 * (profile 1).1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [stationaryRoot, FTV.CyclicMinimality.terminalReward,
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
  let reward := FTV.CyclicAdmissibleCycle.ftvReward
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

/-- One-stage absorption probability of a stationary hazard triple. -/
private def stationaryAbsorptionDenominator (profile : StationaryProfile) : ℝ :=
  1 - (1 - (profile 0).1) * (1 - (profile 1).1) * (1 - (profile 2).1)

/-- Unconditional one-stage absorbing payoff of a stationary hazard triple. -/
private def stationaryPayoffNumerator (profile : StationaryProfile) : Payoff Player :=
  ![(profile 0).1 * (1 - (profile 2).1) +
      (1 - (profile 0).1) *
        (3 * (profile 2).1 - 2 * (profile 1).1 * (profile 2).1),
    (profile 1).1 * (1 - (profile 0).1) +
      (1 - (profile 1).1) *
        (3 * (profile 0).1 - 2 * (profile 0).1 * (profile 2).1),
    (profile 2).1 * (1 - (profile 1).1) +
      (1 - (profile 2).1) *
        (3 * (profile 1).1 - 2 * (profile 0).1 * (profile 1).1)]

@[simp] private theorem stationaryPayoffNumerator_zero
    (profile : StationaryProfile) :
    stationaryPayoffNumerator profile 0 =
      (profile 0).1 * (1 - (profile 2).1) +
        (1 - (profile 0).1) *
          (3 * (profile 2).1 - 2 * (profile 1).1 * (profile 2).1) := by
  rfl

@[simp] private theorem stationaryPayoffNumerator_one
    (profile : StationaryProfile) :
    stationaryPayoffNumerator profile 1 =
      (profile 1).1 * (1 - (profile 0).1) +
        (1 - (profile 1).1) *
          (3 * (profile 0).1 - 2 * (profile 0).1 * (profile 2).1) := by
  rfl

@[simp] private theorem stationaryPayoffNumerator_two
    (profile : StationaryProfile) :
    stationaryPayoffNumerator profile 2 =
      (profile 2).1 * (1 - (profile 1).1) +
        (1 - (profile 2).1) *
          (3 * (profile 1).1 - 2 * (profile 0).1 * (profile 1).1) := by
  rfl

/-- Absorption probability when one designated player always Continues. -/
private def stationaryOpponentAbsorptionDenominator
    (profile : StationaryProfile) : Payoff Player :=
  ![(profile 1).1 + (profile 2).1 - (profile 1).1 * (profile 2).1,
    (profile 0).1 + (profile 2).1 - (profile 0).1 * (profile 2).1,
    (profile 0).1 + (profile 1).1 - (profile 0).1 * (profile 1).1]

/-- Unconditional payoff when one designated player always Continues. -/
private def stationaryNeverNumerator (profile : StationaryProfile) : Payoff Player :=
  ![3 * (profile 2).1 - 2 * (profile 1).1 * (profile 2).1,
    3 * (profile 0).1 - 2 * (profile 0).1 * (profile 2).1,
    3 * (profile 1).1 - 2 * (profile 0).1 * (profile 1).1]

private theorem stationaryContinueMass_formula (profile : StationaryProfile) :
    quittingStationaryContinueMass (stationaryRoot profile) =
      1 - stationaryAbsorptionDenominator profile := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [stationaryRoot, stationaryAbsorptionDenominator, Fin.prod_univ_three]

private theorem stationaryPayoffNumerator_formula
    (profile : StationaryProfile) (who : Player) :
    quittingRootAbsorbingContribution FTV.CyclicAdmissibleCycle.ftvReward
        (stationaryRoot profile) who =
      stationaryPayoffNumerator profile who := by
  fin_cases who <;>
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff <;>
    rw [Math.PMFProduct.expect_pmfPi_fin3] <;>
    simp [stationaryRoot, stationaryPayoffNumerator,
      FTV.CyclicMinimality.terminalReward, expect_coin,
      Matrix.cons_val_two] <;> ring

private theorem stationaryOpponentContinueMass_formula
    (profile : StationaryProfile) (who : Player) :
    quittingStationaryFixedOpponentsContinueMass
        (stationaryRoot profile) who =
      1 - stationaryOpponentAbsorptionDenominator profile who := by
  fin_cases who <;>
    simp [quittingStationaryFixedOpponentsContinueMass,
      quittingFixedOpponentsContinueMass,
      quittingStationaryContinueMass_eq_prod_continueProbability,
      stationaryRoot, stationaryOpponentAbsorptionDenominator,
      Fin.prod_univ_three] <;> ring

private theorem stationaryNeverNumerator_formula
    (profile : StationaryProfile) (who : Player) :
    quittingStationaryFixedOpponentsContinueReward
        FTV.CyclicAdmissibleCycle.ftvReward (stationaryRoot profile) who =
      stationaryNeverNumerator profile who := by
  fin_cases who <;>
    unfold quittingStationaryFixedOpponentsContinueReward
      quittingFixedOpponentsContinueReward
      quittingRootAbsorbingContribution quittingRootExpectedPayoff <;>
    rw [Math.PMFProduct.expect_pmfPi_fin3] <;>
    simp [stationaryRoot, stationaryNeverNumerator,
      FTV.CyclicMinimality.terminalReward, expect_coin,
      Matrix.cons_val_two] <;> ring

/-- The two division-free inequalities used in the paper's compactness
argument: immediate Quit and Never are both within the Nash tolerance. -/
private theorem stationaryEquilibrium_divisionFreeInequalities
    (profile : StationaryProfile) (ε : ℝ)
    (hnash : IsStationaryEpsilonEquilibrium ε profile) (who : Player) :
    quittingRootQuitPayoff FTV.CyclicAdmissibleCycle.ftvReward
          (fun player ↦ quittingTerminalPayoff
            FTV.CyclicAdmissibleCycle.ftvReward
            (stationaryBehaviorProfile profile) player)
          (stationaryRoot profile) who ≤
        quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
            (stationaryBehaviorProfile profile) who + ε ∧
      stationaryNeverNumerator profile who ≤
        stationaryOpponentAbsorptionDenominator profile who *
          (quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
            (stationaryBehaviorProfile profile) who + ε) := by
  let reward := FTV.CyclicAdmissibleCycle.ftvReward
  let root := stationaryRoot profile
  let value : Payoff Player := fun player ↦
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) player
  have hnash' : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingStationaryProfile reward root) := by
    simpa [IsStationaryEpsilonEquilibrium, stationaryBehaviorProfile,
      reward, root] using hnash
  have hrootNash := isεQuittingRootNash_of_isεAsymptoticNash_stationary
    reward root ε hnash'
  have hquit := quittingRootQuitPayoff_le_successor_add_of_isεNash
    reward value ε root who hrootNash
  have hfixed : quittingRootSuccessorPayoff reward value root who = value who := by
    exact (quittingTerminalPayoff_stationary_eq_rootExpectedPayoff
      reward root who).symm
  rw [hfixed] at hquit
  have hcap :=
    (isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le
      reward root ε).mp hnash' who
  constructor
  · simpa [reward, root, value, stationaryBehaviorProfile] using hquit
  · by_cases hcontracts :
        quittingStationaryFixedOpponentsContinueMass root who < 1
    · rw [quittingStationaryFullRateUnilateralCap_of_lt
          reward root who hcontracts,
        quittingStationaryUnilateralCap,
        quittingStationarySelectedCap] at hcap
      have hnever : quittingStationaryNeverValue
          (quittingStationaryFixedOpponentsContinueReward reward root who)
          (quittingStationaryFixedOpponentsContinueMass root who) ≤
          value who + ε := (le_max_right _ _).trans hcap
      have hdenom : 0 <
          1 - quittingStationaryFixedOpponentsContinueMass root who :=
        sub_pos.mpr hcontracts
      rw [quittingStationaryNeverValue,
        div_le_iff₀ hdenom] at hnever
      have hopponentDenominator :
          stationaryOpponentAbsorptionDenominator profile who =
            1 - quittingStationaryFixedOpponentsContinueMass root who := by
        have hmassFormula :=
          stationaryOpponentContinueMass_formula profile who
        change quittingStationaryFixedOpponentsContinueMass root who = _
          at hmassFormula
        linarith
      rw [← stationaryNeverNumerator_formula profile who,
        hopponentDenominator]
      simpa [reward, root, value, stationaryBehaviorProfile, mul_comm] using hnever
    · have hmass :
          quittingStationaryFixedOpponentsContinueMass root who = 1 := by
        exact le_antisymm
          (quittingStationaryFixedOpponentsContinueMass_le_one root who)
          (not_lt.mp hcontracts)
      have hreward :
          quittingStationaryFixedOpponentsContinueReward reward root who = 0 :=
        quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
          reward hmass
      have hopponentDenominator :
          stationaryOpponentAbsorptionDenominator profile who = 0 := by
        have := stationaryOpponentContinueMass_formula profile who
        rw [hmass] at this
        linarith
      rw [← stationaryNeverNumerator_formula profile who,
        hopponentDenominator, hreward]
      norm_num

/-- The normalized first-order quit masses cannot satisfy all six limiting
best-reply inequalities.  This is the algebraic core of the singular case. -/
private theorem not_singularStationaryLimit
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1)
    (hq0 : 1 - (a + 3 * c) ≤ 0)
    (hq1 : 1 - (3 * a + b) ≤ 0)
    (hq2 : 1 - (3 * b + c) ≤ 0)
    (hn0 : 3 * c - (b + c) * (a + 3 * c) ≤ 0)
    (hn1 : 3 * a - (a + c) * (3 * a + b) ≤ 0)
    (hn2 : 3 * b - (a + b) * (3 * b + c) ≤ 0) : False := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

private theorem normalizedHazardSum_close
    (x y z D : ℝ)
    (hx0 : 0 ≤ x) (_hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (_hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hD : D = 1 - (1 - x) * (1 - y) * (1 - z))
    (hDpos : 0 < D) (hxD : x ≤ D) (hyD : y ≤ D) (_hzD : z ≤ D) :
    0 ≤ x / D + y / D + z / D - 1 ∧
      x / D + y / D + z / D - 1 ≤ 2 * (x + y + z) := by
  have hDx : D * (x / D) = x := by field_simp
  have hDy : D * (y / D) = y := by field_simp
  have hDz : D * (z / D) = z := by field_simp
  have hxy : x * y ≤ D * y := mul_le_mul_of_nonneg_right hxD hy0
  have hxz : x * z ≤ D * z := mul_le_mul_of_nonneg_right hxD hz0
  have hyz : y * z ≤ D * z := mul_le_mul_of_nonneg_right hyD hz0
  have hcollision : 0 ≤ x * y + x * z + y * z - x * y * z := by
    nlinarith [mul_nonneg (mul_nonneg hx0 hy0) (sub_nonneg.mpr hz1),
      mul_nonneg hx0 hz0, mul_nonneg hy0 hz0]
  have hidentity :
      D * (x / D + y / D + z / D - 1) =
        x * y + x * z + y * z - x * y * z := by
    nlinarith
  have hcollisionUpper :
      x * y + x * z + y * z - x * y * z ≤ D * (y + 2 * z) := by
    nlinarith [mul_nonneg (mul_nonneg hx0 hy0) hz0]
  have hcoarse : y + 2 * z ≤ 2 * (x + y + z) := by linarith
  have hscaledCoarse := mul_le_mul_of_nonneg_left hcoarse hDpos.le
  constructor
  · nlinarith
  · apply le_of_mul_le_mul_left _ hDpos
    calc
      D * (x / D + y / D + z / D - 1) =
          x * y + x * z + y * z - x * y * z := hidentity
      _ ≤ D * (y + 2 * z) := hcollisionUpper
      _ ≤ D * (2 * (x + y + z)) := hscaledCoarse

/-- A stationary profile is an approximate equilibrium at one positive,
possibly large, error. -/
theorem exists_positive_stationaryEpsilonEquilibrium :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ profile : StationaryProfile,
        IsStationaryEpsilonEquilibrium ε profile := by
  let zeroHazard : Hazard := ⟨0, by norm_num⟩
  let profile : StationaryProfile := fun _ => zeroHazard
  let M := quittingRewardBound FTV.CyclicAdmissibleCycle.ftvReward
  have hM : 0 < M := by
    have hthree := FTV.CyclicAdmissibleCycle.three_le_quittingRewardBound
    dsimp [M]
    linarith
  refine ⟨2 * M, by positivity, profile, ?_⟩
  intro who deviation
  have hdev := abs_quittingTerminalPayoff_le_quittingRewardBound
    FTV.CyclicAdmissibleCycle.ftvReward
    (Function.update (stationaryBehaviorProfile profile) who deviation) who
  have hbase := abs_quittingTerminalPayoff_le_quittingRewardBound
    FTV.CyclicAdmissibleCycle.ftvReward
    (stationaryBehaviorProfile profile) who
  have hdev_le :
      quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
          (Function.update (stationaryBehaviorProfile profile) who deviation) who ≤
        M := by
    exact (le_abs_self _).trans (by simpa [M] using hdev)
  have hbase_le :
      -M ≤ quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
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
all-Continue limit.  Closed endpoint complementarity handles the absorbing
case; normalized first-order quit masses and six limiting deviation bounds
exclude the singular case. -/

/-- Corrected form of Theorem 3.2: stationary equilibria fail
below one positive threshold. -/
theorem theorem3_2_corrected :
    ∃ threshold : ℝ, 0 < threshold ∧
      ∀ ε : ℝ, 0 < ε → ε < threshold →
        ¬ ∃ profile : StationaryProfile,
          IsStationaryEpsilonEquilibrium ε profile := by
  by_contra hthreshold
  push Not at hthreshold
  have hscale (n : ℕ) : 0 < (1 / (n + 1 : ℝ)) := by positivity
  choose ε hεpos hεlt profile hprofile using
    fun n : ℕ ↦ hthreshold (1 / (n + 1 : ℝ)) (hscale n)
  have hε : Tendsto ε atTop (nhds 0) := by
    apply squeeze_zero (fun n ↦ hεpos n |>.le) (fun n ↦ hεlt n |>.le)
    exact (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop (nhds 0))
  obtain ⟨limit, φ, hφ, hprofileLimit⟩ :=
    CompactSpace.tendsto_subseq profile
  have hφTop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hεsub : Tendsto (ε ∘ φ) atTop (nhds 0) := hε.comp hφTop
  have hprofileSub : Tendsto (profile ∘ φ) atTop (nhds limit) :=
    hprofileLimit
  let p : ℕ → StationaryProfile := profile ∘ φ
  let error : ℕ → ℝ := ε ∘ φ
  let value : ℕ → Payoff Player := fun n who ↦
    quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
      (stationaryBehaviorProfile (p n)) who
  let denominator : ℕ → ℝ := fun n ↦
    stationaryAbsorptionDenominator (p n)
  have hp : Tendsto p atTop (nhds limit) := hprofileSub
  have herr : Tendsto error atTop (nhds 0) := hεsub
  have hcoord (who : Player) :
      Tendsto (fun n ↦ ((p n) who).1) atTop (nhds ((limit who).1)) := by
    exact ((continuous_subtype_val.comp (continuous_apply who)).tendsto limit).comp hp
  have hdenominator_nonneg (n : ℕ) : 0 ≤ denominator n := by
    have hmass := quittingStationaryContinueMass_le_one
      (stationaryRoot (p n))
    rw [stationaryContinueMass_formula] at hmass
    change 0 ≤ stationaryAbsorptionDenominator (p n)
    linarith
  have herror_lt_one (n : ℕ) : error n < 1 := by
    have hbound := hεlt (φ n)
    have hone : (1 / ((φ n : ℝ) + 1)) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      norm_num
    exact hbound.trans_le hone
  have hdenominator_pos (n : ℕ) : 0 < denominator n := by
    apply lt_of_le_of_ne (hdenominator_nonneg n)
    intro hzero
    have hdenominatorZero : denominator n = 0 := hzero.symm
    have hmass : quittingStationaryContinueMass
        (stationaryRoot (p n)) = 1 := by
      rw [stationaryContinueMass_formula]
      linarith
    have hroot : stationaryRoot (p n) = quittingAllContinueRoot := by
      funext who
      exact eq_pure_false_of_quittingStationaryContinueMass_eq_one hmass who
    have hbehavior : stationaryBehaviorProfile (p n) =
        quittingAlwaysContinueProfile FTV.CyclicAdmissibleCycle.ftvReward := by
      rw [stationaryBehaviorProfile, hroot]
      rfl
    have hvalueZero : value n 0 = 0 := by
      change quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
        (stationaryBehaviorProfile (p n)) 0 = 0
      rw [hbehavior]
      exact quittingTerminalPayoff_quittingAlwaysContinue
        FTV.CyclicAdmissibleCycle.ftvReward 0
    have hzeroHazard : ((p n) 2).1 = 0 := by
      have hpure := congrArg (fun marginal : PMF Bool ↦
        (marginal true).toReal)
        (eq_pure_false_of_quittingStationaryContinueMass_eq_one hmass 2)
      simpa [stationaryRoot] using hpure
    have hquit :=
      (stationaryEquilibrium_divisionFreeInequalities
        (p n) (error n) (hprofile (φ n)) 0).1
    rw [stationaryRoot_quitPayoff_zero (p n) (value n),
      hzeroHazard] at hquit
    change 1 - 0 ≤ value n 0 + error n at hquit
    rw [hvalueZero] at hquit
    linarith [herror_lt_one n]
  have hcoordinate_le_denominator (n : ℕ) (who : Player) :
      ((p n) who).1 ≤ denominator n := by
    have hmass := quittingStationaryContinueMass_le_ownContinueProbability
      (stationaryRoot (p n)) who
    rw [stationaryContinueMass_formula] at hmass
    have hcontinue :
        ((stationaryRoot (p n) who) false).toReal = 1 - ((p n) who).1 := by
      simp [stationaryRoot]
    rw [hcontinue] at hmass
    change ((p n) who).1 ≤ stationaryAbsorptionDenominator (p n)
    linarith
  have hbalance (n : ℕ) (who : Player) :
      denominator n * value n who = stationaryPayoffNumerator (p n) who := by
    have h := one_sub_continueMass_mul_quittingTerminalPayoff_stationary
      FTV.CyclicAdmissibleCycle.ftvReward (stationaryRoot (p n)) who
    rw [stationaryContinueMass_formula,
      stationaryPayoffNumerator_formula] at h
    simpa [denominator, value, stationaryBehaviorProfile] using h
  by_cases hlimitZero : ∀ who, (limit who).1 = 0
  · let normalized : ℕ → StationaryProfile := fun n who ↦
      ⟨((p n) who).1 / denominator n, by
        constructor
        · exact div_nonneg ((p n) who).2.1 (hdenominator_nonneg n)
        · exact (div_le_one (hdenominator_pos n)).2
            (hcoordinate_le_denominator n who)⟩
    obtain ⟨weightLimit, ψ, hψ, hnormalizedLimit⟩ :=
      CompactSpace.tendsto_subseq normalized
    have hψTop : Tendsto ψ atTop atTop := hψ.tendsto_atTop
    have herrZero : Tendsto (error ∘ ψ) atTop (nhds 0) :=
      herr.comp hψTop
    have hnormalizedCoord (who : Player) :
        Tendsto (fun n ↦ ((normalized (ψ n)) who).1) atTop
          (nhds ((weightLimit who).1)) := by
      exact ((continuous_subtype_val.comp (continuous_apply who)).tendsto
        weightLimit).comp hnormalizedLimit
    have hpZeroCoord (who : Player) :
        Tendsto ((fun n ↦ ((p n) who).1) ∘ ψ) atTop (nhds 0) := by
      have hcomp := (hcoord who).comp hψTop
      simpa only [hlimitZero who] using hcomp
    have hdenominatorZero : Tendsto (denominator ∘ ψ) atTop (nhds 0) := by
      have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
        tendsto_const_nhds
      have h := hone.sub ((hone.sub (hpZeroCoord 0)).mul
        ((hone.sub (hpZeroCoord 1)).mul (hone.sub (hpZeroCoord 2))))
      change Tendsto (fun n ↦
        1 - (1 - (((p ∘ ψ) n) 0).1) * (1 - (((p ∘ ψ) n) 1).1) *
          (1 - (((p ∘ ψ) n) 2).1)) atTop (nhds 0)
      have h' := h
      norm_num only [sub_zero, one_mul, sub_self] at h'
      convert h' using 1
      funext n
      simp only [Function.comp_apply]
      ring
    have hhazardSumZero : Tendsto (fun n ↦
        (((p ∘ ψ) n) 0).1 + (((p ∘ ψ) n) 1).1 +
          (((p ∘ ψ) n) 2).1)
        atTop (nhds 0) := by
      have h := ((hpZeroCoord 0).add (hpZeroCoord 1)).add (hpZeroCoord 2)
      norm_num only [zero_add] at h
      simpa only [Function.comp_apply] using h
    have hnormalizedClose (n : ℕ) :
        0 ≤ ((normalized (ψ n)) 0).1 + ((normalized (ψ n)) 1).1 +
            ((normalized (ψ n)) 2).1 - 1 ∧
          ((normalized (ψ n)) 0).1 + ((normalized (ψ n)) 1).1 +
              ((normalized (ψ n)) 2).1 - 1 ≤
            2 * (((p (ψ n)) 0).1 + ((p (ψ n)) 1).1 +
              ((p (ψ n)) 2).1) := by
      simpa only [normalized] using normalizedHazardSum_close
        ((p (ψ n)) 0).1 ((p (ψ n)) 1).1 ((p (ψ n)) 2).1
        (denominator (ψ n))
        ((p (ψ n)) 0).2.1 ((p (ψ n)) 0).2.2
        ((p (ψ n)) 1).2.1 ((p (ψ n)) 1).2.2
        ((p (ψ n)) 2).2.1 ((p (ψ n)) 2).2.2
        rfl (hdenominator_pos (ψ n))
        (hcoordinate_le_denominator (ψ n) 0)
        (hcoordinate_le_denominator (ψ n) 1)
        (hcoordinate_le_denominator (ψ n) 2)
    have hnormalizedGapZero : Tendsto (fun n ↦
        ((normalized (ψ n)) 0).1 + ((normalized (ψ n)) 1).1 +
          ((normalized (ψ n)) 2).1 - 1) atTop (nhds 0) := by
      apply squeeze_zero
      · exact fun n ↦ (hnormalizedClose n).1
      · exact fun n ↦ (hnormalizedClose n).2
      · simpa using hhazardSumZero.const_mul 2
    have hnormalizedSumOne : Tendsto (fun n ↦
        ((normalized (ψ n)) 0).1 + ((normalized (ψ n)) 1).1 +
          ((normalized (ψ n)) 2).1) atTop (nhds 1) := by
      simpa only [sub_add_cancel, zero_add] using hnormalizedGapZero.add_const 1
    have hweightSum : (weightLimit 0).1 + (weightLimit 1).1 +
        (weightLimit 2).1 = 1 := by
      have hsumLimit := ((hnormalizedCoord 0).add
        (hnormalizedCoord 1)).add (hnormalizedCoord 2)
      exact tendsto_nhds_unique hsumLimit hnormalizedSumOne
    let a : ℝ := (weightLimit 0).1
    let b : ℝ := (weightLimit 1).1
    let c : ℝ := (weightLimit 2).1
    have ha : 0 ≤ a := (weightLimit 0).2.1
    have hb : 0 ≤ b := (weightLimit 1).2.1
    have hc : 0 ≤ c := (weightLimit 2).2.1
    have habc : a + b + c = 1 := hweightSum
    have hvalueFormula (n : ℕ) (who : Player) :
        value n who = stationaryPayoffNumerator (p n) who / denominator n := by
      apply (eq_div_iff (hdenominator_pos n).ne').2
      simpa [mul_comm] using hbalance n who
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hvalueZeroLimit : Tendsto (fun n ↦ value (ψ n) 0) atTop
        (nhds (a + 3 * c)) := by
      have hexpression := (hnormalizedCoord 0).mul
        (hone.sub (hpZeroCoord 2)) |>.add
          ((hone.sub (hpZeroCoord 0)).mul
            ((hnormalizedCoord 2).const_mul (3 : ℝ) |>.sub
              ((hpZeroCoord 1).mul (hnormalizedCoord 2) |>.const_mul (2 : ℝ))))
      norm_num only [sub_zero, one_mul, mul_one, zero_mul, sub_zero,
        add_zero] at hexpression
      convert hexpression using 1
      · funext n
        rw [hvalueFormula]
        simp only [normalized, stationaryPayoffNumerator,
          Matrix.cons_val_zero, Function.comp_apply]
        field_simp [(hdenominator_pos (ψ n)).ne']
    have hvalueOneLimit : Tendsto (fun n ↦ value (ψ n) 1) atTop
        (nhds (3 * a + b)) := by
      have hexpression := (hnormalizedCoord 1).mul
        (hone.sub (hpZeroCoord 0)) |>.add
          ((hone.sub (hpZeroCoord 1)).mul
            ((hnormalizedCoord 0).const_mul (3 : ℝ) |>.sub
              ((hpZeroCoord 2).mul (hnormalizedCoord 0) |>.const_mul (2 : ℝ))))
      norm_num only [sub_zero, one_mul, mul_one, zero_mul, sub_zero,
        add_zero] at hexpression
      convert hexpression using 1
      · funext n
        rw [hvalueFormula]
        simp only [normalized, stationaryPayoffNumerator,
          Matrix.cons_val_one, Matrix.cons_val_zero, Function.comp_apply]
        field_simp [(hdenominator_pos (ψ n)).ne']
      · simp only [a, b]
        ring
    have hvalueTwoLimit : Tendsto (fun n ↦ value (ψ n) 2) atTop
        (nhds (3 * b + c)) := by
      have hexpression := (hnormalizedCoord 2).mul
        (hone.sub (hpZeroCoord 1)) |>.add
          ((hone.sub (hpZeroCoord 2)).mul
            ((hnormalizedCoord 1).const_mul (3 : ℝ) |>.sub
              ((hpZeroCoord 0).mul (hnormalizedCoord 1) |>.const_mul (2 : ℝ))))
      norm_num only [sub_zero, one_mul, mul_one, zero_mul, sub_zero,
        add_zero] at hexpression
      convert hexpression using 1
      · funext n
        rw [hvalueFormula]
        simp [normalized, stationaryPayoffNumerator,
          Matrix.cons_val_two, Function.comp_apply]
        field_simp [(hdenominator_pos (ψ n)).ne']
      · simp only [b, c]
        ring
    have hquitZero (n : ℕ) :
        1 - (((p ∘ ψ) n) 2).1 - value (ψ n) 0 - (error ∘ ψ) n ≤ 0 := by
      have hquit := (stationaryEquilibrium_divisionFreeInequalities
        (p (ψ n)) (error (ψ n)) (hprofile (φ (ψ n))) 0).1
      rw [stationaryRoot_quitPayoff_zero (p (ψ n)) (value (ψ n))] at hquit
      change 1 - (((p ∘ ψ) n) 2).1 ≤
        value (ψ n) 0 + (error ∘ ψ) n at hquit
      linarith
    have hquitOne (n : ℕ) :
        1 - (((p ∘ ψ) n) 0).1 - value (ψ n) 1 - (error ∘ ψ) n ≤ 0 := by
      have hquit := (stationaryEquilibrium_divisionFreeInequalities
        (p (ψ n)) (error (ψ n)) (hprofile (φ (ψ n))) 1).1
      rw [stationaryRoot_quitPayoff_one (p (ψ n)) (value (ψ n))] at hquit
      change 1 - (((p ∘ ψ) n) 0).1 ≤
        value (ψ n) 1 + (error ∘ ψ) n at hquit
      linarith
    have hquitTwo (n : ℕ) :
        1 - (((p ∘ ψ) n) 1).1 - value (ψ n) 2 - (error ∘ ψ) n ≤ 0 := by
      have hquit := (stationaryEquilibrium_divisionFreeInequalities
        (p (ψ n)) (error (ψ n)) (hprofile (φ (ψ n))) 2).1
      rw [stationaryRoot_quitPayoff_two (p (ψ n)) (value (ψ n))] at hquit
      change 1 - (((p ∘ ψ) n) 1).1 ≤
        value (ψ n) 2 + (error ∘ ψ) n at hquit
      linarith
    have hq0 : 1 - (a + 3 * c) ≤ 0 := by
      have hlimit := le_of_tendsto'
        (((hone.sub (hpZeroCoord 2)).sub hvalueZeroLimit).sub herrZero)
        hquitZero
      norm_num only [sub_zero] at hlimit
      exact hlimit
    have hq1 : 1 - (3 * a + b) ≤ 0 := by
      have hlimit := le_of_tendsto'
        (((hone.sub (hpZeroCoord 0)).sub hvalueOneLimit).sub herrZero)
        hquitOne
      norm_num only [sub_zero] at hlimit
      exact hlimit
    have hq2 : 1 - (3 * b + c) ≤ 0 := by
      have hlimit := le_of_tendsto'
        (((hone.sub (hpZeroCoord 1)).sub hvalueTwoLimit).sub herrZero)
        hquitTwo
      norm_num only [sub_zero] at hlimit
      exact hlimit
    have hneverScaled (n : ℕ) (who : Player) :
        stationaryNeverNumerator (p (ψ n)) who / denominator (ψ n) ≤
          stationaryOpponentAbsorptionDenominator (p (ψ n)) who /
            denominator (ψ n) * (value (ψ n) who + error (ψ n)) := by
      have hnever := (stationaryEquilibrium_divisionFreeInequalities
        (p (ψ n)) (error (ψ n)) (hprofile (φ (ψ n))) who).2
      have hdiv := div_le_div_of_nonneg_right hnever
        (hdenominator_pos (ψ n)).le
      calc
        stationaryNeverNumerator (p (ψ n)) who / denominator (ψ n) ≤
            (stationaryOpponentAbsorptionDenominator (p (ψ n)) who *
              (value (ψ n) who + error (ψ n))) / denominator (ψ n) := hdiv
        _ = stationaryOpponentAbsorptionDenominator (p (ψ n)) who /
              denominator (ψ n) * (value (ψ n) who + error (ψ n)) := by
          ring
    have hneverZero (n : ℕ) :
        ((normalized (ψ n)) 2).1 * (3 - 2 * (((p ∘ ψ) n) 1).1) -
            (((normalized (ψ n)) 1).1 + ((normalized (ψ n)) 2).1 -
              (((p ∘ ψ) n) 1).1 * ((normalized (ψ n)) 2).1) *
              (value (ψ n) 0 + (error ∘ ψ) n) ≤ 0 := by
      apply sub_nonpos.mpr
      have hscaled := hneverScaled n 0
      have hleft :
          ((normalized (ψ n)) 2).1 * (3 - 2 * (((p ∘ ψ) n) 1).1) =
            stationaryNeverNumerator (p (ψ n)) 0 / denominator (ψ n) := by
        simp [normalized, stationaryNeverNumerator, Function.comp_apply]
        field_simp [(hdenominator_pos (ψ n)).ne']
      have hright :
          ((normalized (ψ n)) 1).1 + ((normalized (ψ n)) 2).1 -
              (((p ∘ ψ) n) 1).1 * ((normalized (ψ n)) 2).1 =
            stationaryOpponentAbsorptionDenominator (p (ψ n)) 0 /
              denominator (ψ n) := by
        simp [normalized, stationaryOpponentAbsorptionDenominator,
          Function.comp_apply]
        field_simp [(hdenominator_pos (ψ n)).ne']
      rw [hleft, hright]
      simpa only [Function.comp_apply] using hscaled
    have hthree : Tendsto (fun _ : ℕ ↦ (3 : ℝ)) atTop (nhds 3) :=
      tendsto_const_nhds
    have hneverZeroLimit : Tendsto (fun n ↦
        ((normalized (ψ n)) 2).1 * (3 - 2 * (((p ∘ ψ) n) 1).1) -
          (((normalized (ψ n)) 1).1 + ((normalized (ψ n)) 2).1 -
            (((p ∘ ψ) n) 1).1 * ((normalized (ψ n)) 2).1) *
            (value (ψ n) 0 + (error ∘ ψ) n)) atTop
        (nhds (3 * c - (b + c) * (a + 3 * c))) := by
      have hlimit := (hnormalizedCoord 2).mul
        (hthree.sub ((hpZeroCoord 1).const_mul (2 : ℝ))) |>.sub
          (((hnormalizedCoord 1).add (hnormalizedCoord 2) |>.sub
            ((hpZeroCoord 1).mul (hnormalizedCoord 2))).mul
              (hvalueZeroLimit.add herrZero))
      norm_num only [mul_zero, sub_zero, zero_mul, add_zero] at hlimit
      convert hlimit using 1
      · funext n
        simp only [Function.comp_apply]
      · simp only [a, b, c]
        ring
    have hn0 : 3 * c - (b + c) * (a + 3 * c) ≤ 0 :=
      le_of_tendsto' hneverZeroLimit hneverZero
    have hneverOne (n : ℕ) :
        ((normalized (ψ n)) 0).1 * (3 - 2 * (((p ∘ ψ) n) 2).1) -
            (((normalized (ψ n)) 0).1 + ((normalized (ψ n)) 2).1 -
              (((p ∘ ψ) n) 2).1 * ((normalized (ψ n)) 0).1) *
              (value (ψ n) 1 + (error ∘ ψ) n) ≤ 0 := by
      apply sub_nonpos.mpr
      have hscaled := hneverScaled n 1
      have hleft :
          ((normalized (ψ n)) 0).1 * (3 - 2 * (((p ∘ ψ) n) 2).1) =
            stationaryNeverNumerator (p (ψ n)) 1 / denominator (ψ n) := by
        simp [normalized, stationaryNeverNumerator, Function.comp_apply]
        field_simp [(hdenominator_pos (ψ n)).ne']
      have hright :
          ((normalized (ψ n)) 0).1 + ((normalized (ψ n)) 2).1 -
              (((p ∘ ψ) n) 2).1 * ((normalized (ψ n)) 0).1 =
            stationaryOpponentAbsorptionDenominator (p (ψ n)) 1 /
              denominator (ψ n) := by
        simp [normalized, stationaryOpponentAbsorptionDenominator,
          Function.comp_apply]
        field_simp [(hdenominator_pos (ψ n)).ne']
      rw [hleft, hright]
      simpa only [Function.comp_apply] using hscaled
    have hneverOneLimit : Tendsto (fun n ↦
        ((normalized (ψ n)) 0).1 * (3 - 2 * (((p ∘ ψ) n) 2).1) -
          (((normalized (ψ n)) 0).1 + ((normalized (ψ n)) 2).1 -
            (((p ∘ ψ) n) 2).1 * ((normalized (ψ n)) 0).1) *
            (value (ψ n) 1 + (error ∘ ψ) n)) atTop
        (nhds (3 * a - (a + c) * (3 * a + b))) := by
      have hlimit := (hnormalizedCoord 0).mul
        (hthree.sub ((hpZeroCoord 2).const_mul (2 : ℝ))) |>.sub
          (((hnormalizedCoord 0).add (hnormalizedCoord 2) |>.sub
            ((hpZeroCoord 2).mul (hnormalizedCoord 0))).mul
              (hvalueOneLimit.add herrZero))
      norm_num only [mul_zero, sub_zero, zero_mul, add_zero] at hlimit
      convert hlimit using 1
      · funext n
        simp only [Function.comp_apply]
      · simp only [a, b, c]
        ring
    have hn1 : 3 * a - (a + c) * (3 * a + b) ≤ 0 :=
      le_of_tendsto' hneverOneLimit hneverOne
    have hneverTwo (n : ℕ) :
        ((normalized (ψ n)) 1).1 * (3 - 2 * (((p ∘ ψ) n) 0).1) -
            (((normalized (ψ n)) 0).1 + ((normalized (ψ n)) 1).1 -
              (((p ∘ ψ) n) 0).1 * ((normalized (ψ n)) 1).1) *
              (value (ψ n) 2 + (error ∘ ψ) n) ≤ 0 := by
      apply sub_nonpos.mpr
      have hscaled := hneverScaled n 2
      have hleft :
          ((normalized (ψ n)) 1).1 * (3 - 2 * (((p ∘ ψ) n) 0).1) =
            stationaryNeverNumerator (p (ψ n)) 2 / denominator (ψ n) := by
        simp [normalized, stationaryNeverNumerator, Function.comp_apply,
          Matrix.cons_val_two]
        field_simp [(hdenominator_pos (ψ n)).ne']
      have hright :
          ((normalized (ψ n)) 0).1 + ((normalized (ψ n)) 1).1 -
              (((p ∘ ψ) n) 0).1 * ((normalized (ψ n)) 1).1 =
            stationaryOpponentAbsorptionDenominator (p (ψ n)) 2 /
              denominator (ψ n) := by
        simp [normalized, stationaryOpponentAbsorptionDenominator,
          Function.comp_apply, Matrix.cons_val_two]
        field_simp [(hdenominator_pos (ψ n)).ne']
      rw [hleft, hright]
      simpa only [Function.comp_apply] using hscaled
    have hneverTwoLimit : Tendsto (fun n ↦
        ((normalized (ψ n)) 1).1 * (3 - 2 * (((p ∘ ψ) n) 0).1) -
          (((normalized (ψ n)) 0).1 + ((normalized (ψ n)) 1).1 -
            (((p ∘ ψ) n) 0).1 * ((normalized (ψ n)) 1).1) *
            (value (ψ n) 2 + (error ∘ ψ) n)) atTop
        (nhds (3 * b - (a + b) * (3 * b + c))) := by
      have hlimit := (hnormalizedCoord 1).mul
        (hthree.sub ((hpZeroCoord 0).const_mul (2 : ℝ))) |>.sub
          (((hnormalizedCoord 0).add (hnormalizedCoord 1) |>.sub
            ((hpZeroCoord 0).mul (hnormalizedCoord 1))).mul
              (hvalueTwoLimit.add herrZero))
      norm_num only [mul_zero, sub_zero, zero_mul, add_zero] at hlimit
      convert hlimit using 1
      · funext n
        simp only [Function.comp_apply]
      · simp only [a, b, c]
        ring
    have hn2 : 3 * b - (a + b) * (3 * b + c) ≤ 0 :=
      le_of_tendsto' hneverTwoLimit hneverTwo
    exact not_singularStationaryLimit a b c ha hb hc habc
      hq0 hq1 hq2 hn0 hn1 hn2
  · have hdenominatorLimit : Tendsto denominator atTop
        (nhds (stationaryAbsorptionDenominator limit)) := by
      have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
        tendsto_const_nhds
      have hlimit := hone.sub ((hone.sub (hcoord 0)).mul
        ((hone.sub (hcoord 1)).mul (hone.sub (hcoord 2))))
      convert hlimit using 1
      · funext n
        simp only [denominator, stationaryAbsorptionDenominator]
        ring
      · simp only [stationaryAbsorptionDenominator]
        ring
    push Not at hlimitZero
    obtain ⟨active, hactive⟩ := hlimitZero
    have hlimitCoordinate_le :
        (limit active).1 ≤ stationaryAbsorptionDenominator limit := by
      have hresidual := (hcoord active).sub hdenominatorLimit
      have hbound : ∀ n, ((p n) active).1 - denominator n ≤ 0 :=
        fun n ↦ sub_nonpos.mpr (hcoordinate_le_denominator n active)
      exact sub_nonpos.mp (le_of_tendsto' hresidual hbound)
    have hlimitCoordinate_pos : 0 < (limit active).1 :=
      lt_of_le_of_ne (limit active).2.1 (Ne.symm hactive)
    have hlimitDenominator_pos : 0 < stationaryAbsorptionDenominator limit :=
      hlimitCoordinate_pos.trans_le hlimitCoordinate_le
    have hlimitAbsorbs :
        quittingStationaryContinueMass (stationaryRoot limit) < 1 := by
      rw [stationaryContinueMass_formula]
      exact sub_lt_self 1 hlimitDenominator_pos
    let limitValue : Payoff Player := fun who ↦
      quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
        (stationaryBehaviorProfile limit) who
    have hlimitValueFormula (who : Player) :
        limitValue who = stationaryPayoffNumerator limit who /
          stationaryAbsorptionDenominator limit := by
      change quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
        (quittingStationaryProfile FTV.CyclicAdmissibleCycle.ftvReward
          (stationaryRoot limit)) who = _
      rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div
        FTV.CyclicAdmissibleCycle.ftvReward (stationaryRoot limit) who
        hlimitAbsorbs]
      rw [stationaryContinueMass_formula,
        stationaryPayoffNumerator_formula]
      congr 1
      ring
    have hnumeratorLimit (who : Player) : Tendsto
        (fun n ↦ stationaryPayoffNumerator (p n) who) atTop
        (nhds (stationaryPayoffNumerator limit who)) := by
      have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
        tendsto_const_nhds
      fin_cases who
      · have hlimit := (hcoord 0).mul (hone.sub (hcoord 2)) |>.add
          ((hone.sub (hcoord 0)).mul
            ((hcoord 2).const_mul (3 : ℝ) |>.sub
              ((hcoord 1).mul (hcoord 2) |>.const_mul (2 : ℝ))))
        change Tendsto (fun n ↦ stationaryPayoffNumerator (p n) 0) atTop
          (nhds (stationaryPayoffNumerator limit 0))
        simpa only [stationaryPayoffNumerator_zero, mul_assoc] using hlimit
      · have hlimit := (hcoord 1).mul (hone.sub (hcoord 0)) |>.add
          ((hone.sub (hcoord 1)).mul
            ((hcoord 0).const_mul (3 : ℝ) |>.sub
              ((hcoord 0).mul (hcoord 2) |>.const_mul (2 : ℝ))))
        change Tendsto (fun n ↦ stationaryPayoffNumerator (p n) 1) atTop
          (nhds (stationaryPayoffNumerator limit 1))
        simpa only [stationaryPayoffNumerator_one, mul_assoc] using hlimit
      · have hlimit := (hcoord 2).mul (hone.sub (hcoord 1)) |>.add
          ((hone.sub (hcoord 2)).mul
            ((hcoord 1).const_mul (3 : ℝ) |>.sub
              ((hcoord 0).mul (hcoord 1) |>.const_mul (2 : ℝ))))
        change Tendsto (fun n ↦ stationaryPayoffNumerator (p n) 2) atTop
          (nhds (stationaryPayoffNumerator limit 2))
        simpa only [stationaryPayoffNumerator_two, mul_assoc] using hlimit
    have hvalueFormulaNonzero (n : ℕ) (who : Player) :
        value n who = stationaryPayoffNumerator (p n) who / denominator n := by
      apply (eq_div_iff (hdenominator_pos n).ne').2
      simpa [mul_comm] using hbalance n who
    have hvalueLimit (who : Player) : Tendsto (fun n ↦ value n who) atTop
        (nhds (limitValue who)) := by
      have hquotient := (hnumeratorLimit who).div hdenominatorLimit
        hlimitDenominator_pos.ne'
      rw [hlimitValueFormula who]
      convert hquotient using 1
      funext n
      exact hvalueFormulaNonzero n who
    have hvaluesLimit : Tendsto value atTop (nhds limitValue) := by
      rw [tendsto_pi_nhds]
      exact hvalueLimit
    let simplexRoot : ℕ → QuittingRootSimplex Player := fun n who ↦
      stdSimplexEquiv (stationaryRoot (p n) who)
    let limitSimplexRoot : QuittingRootSimplex Player := fun who ↦
      stdSimplexEquiv (stationaryRoot limit who)
    have hrootOfSimplex (n : ℕ) :
        quittingRootOfSimplex (simplexRoot n) = stationaryRoot (p n) := by
      funext who
      exact (stdSimplexEquiv (α := Bool)).symm_apply_apply
        (stationaryRoot (p n) who)
    have hlimitRootOfSimplex :
        quittingRootOfSimplex limitSimplexRoot = stationaryRoot limit := by
      funext who
      exact (stdSimplexEquiv (α := Bool)).symm_apply_apply
        (stationaryRoot limit who)
    have hsimplexRoot : Tendsto simplexRoot atTop (nhds limitSimplexRoot) := by
      rw [tendsto_pi_nhds]
      intro who
      rw [tendsto_subtype_rng, tendsto_pi_nhds]
      intro action
      have hcoordinate : ∀ n,
          ((simplexRoot n who : stdSimplex ℝ Bool) : Bool → ℝ) action =
            (stationaryRoot (p n) who action).toReal := by
        intro n
        exact congrFun (coe_stdSimplexEquiv_apply
          (stationaryRoot (p n) who)) action
      have hlimitCoordinate :
          ((limitSimplexRoot who : stdSimplex ℝ Bool) : Bool → ℝ) action =
            (stationaryRoot limit who action).toReal := by
        exact congrFun (coe_stdSimplexEquiv_apply
          (stationaryRoot limit who)) action
      have hbase : Tendsto
          (fun n ↦ (stationaryRoot (p n) who action).toReal) atTop
          (nhds ((stationaryRoot limit who action).toReal)) := by
        cases action with
        | false =>
            have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
              tendsto_const_nhds
            simpa [stationaryRoot] using hone.sub (hcoord who)
        | true => simpa [stationaryRoot] using hcoord who
      have hactual := hbase.congr'
        (Filter.Eventually.of_forall fun n ↦ (hcoordinate n).symm)
      convert hactual using 1
      · rfl
      · exact congrArg nhds hlimitCoordinate
    have hendpointApprox (n : ℕ) :
        IsεQuittingRootEndpointNash FTV.CyclicAdmissibleCycle.ftvReward
          (value n) (error n) (quittingRootOfSimplex (simplexRoot n)) := by
      rw [hrootOfSimplex]
      apply (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
        FTV.CyclicAdmissibleCycle.ftvReward (value n) (error n)
          (stationaryRoot (p n))).2
      apply isεQuittingRootNash_of_isεAsymptoticNash_stationary
      simpa [p, error, value, IsStationaryEpsilonEquilibrium,
        stationaryBehaviorProfile] using hprofile (φ n)
    have hendpointLimit :
        IsεQuittingRootEndpointNash FTV.CyclicAdmissibleCycle.ftvReward
          limitValue 0 (stationaryRoot limit) := by
      have hclosed := isεQuittingRootEndpointNash_of_tendsto
        FTV.CyclicAdmissibleCycle.ftvReward error value simplexRoot herr
        hvaluesLimit hsimplexRoot
        (Filter.Eventually.of_forall hendpointApprox)
      rwa [hlimitRootOfSimplex] at hclosed
    have hboundary : IsQuittingStationaryBoundaryAdmissible
        FTV.CyclicAdmissibleCycle.ftvReward (stationaryRoot limit)
          limitValue := by
      intro who hmass
      have hotherZero (other : Player) (hne : other ≠ who) :
          (limit other).1 = 0 := by
        have hpure :=
          opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
            (stationaryRoot limit) who hmass other hne
        have hprob := congrArg (fun marginal : PMF Bool ↦
          (marginal true).toReal) hpure
        simpa [stationaryRoot] using hprob
      rw [FTV.CyclicAdmissibleCycle.ftvReward_singletonTerminal,
        FTV.CyclicMinimality.soloReward_self]
      norm_num only [max_eq_right]
      fin_cases who
      · change 1 ≤ limitValue 0
        have hzeroOne : (limit 1).1 = 0 := hotherZero 1 (by decide)
        have hzeroTwo : (limit 2).1 = 0 := hotherZero 2 (by decide)
        have hdenominator : stationaryAbsorptionDenominator limit =
            (limit 0).1 := by
          simp [stationaryAbsorptionDenominator, hzeroOne, hzeroTwo]
        have hpositive : 0 < (limit 0).1 := by
          rwa [hdenominator] at hlimitDenominator_pos
        rw [hlimitValueFormula, stationaryPayoffNumerator_zero,
          hzeroOne, hzeroTwo, hdenominator]
        field_simp [hpositive.ne']
        all_goals norm_num
      · change 1 ≤ limitValue 1
        have hzeroZero : (limit 0).1 = 0 := hotherZero 0 (by decide)
        have hzeroTwo : (limit 2).1 = 0 := hotherZero 2 (by decide)
        have hdenominator : stationaryAbsorptionDenominator limit =
            (limit 1).1 := by
          simp [stationaryAbsorptionDenominator, hzeroZero, hzeroTwo]
        have hpositive : 0 < (limit 1).1 := by
          rwa [hdenominator] at hlimitDenominator_pos
        rw [hlimitValueFormula, stationaryPayoffNumerator_one,
          hzeroZero, hzeroTwo, hdenominator]
        field_simp [hpositive.ne']
        all_goals norm_num
      · change 1 ≤ limitValue 2
        have hzeroZero : (limit 0).1 = 0 := hotherZero 0 (by decide)
        have hzeroOne : (limit 1).1 = 0 := hotherZero 1 (by decide)
        have hdenominator : stationaryAbsorptionDenominator limit =
            (limit 2).1 := by
          simp [stationaryAbsorptionDenominator, hzeroZero, hzeroOne]
        have hpositive : 0 < (limit 2).1 := by
          rwa [hdenominator] at hlimitDenominator_pos
        rw [hlimitValueFormula, stationaryPayoffNumerator_two,
          hzeroZero, hzeroOne, hdenominator]
        field_simp [hpositive.ne']
        all_goals norm_num
    have hfixed : limitValue = quittingRootSuccessorPayoff
        FTV.CyclicAdmissibleCycle.ftvReward limitValue
          (stationaryRoot limit) := by
      funext who
      exact quittingTerminalPayoff_stationary_eq_rootExpectedPayoff
        FTV.CyclicAdmissibleCycle.ftvReward (stationaryRoot limit) who
    have hexact :
        (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
          (quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward) 0
          (stationaryBehaviorProfile limit) := by
      apply (isZeroAsymptoticNash_stationary_iff_boundary_of_fixedPoint_endpointNash
        FTV.CyclicAdmissibleCycle.ftvReward (stationaryRoot limit)
          limitValue hlimitAbsorbs hfixed hendpointLimit).2
      exact hboundary
    exact lemma3_1 ⟨limit, hexact⟩

/-! ### Theorem 3.3: the cyclic Markov equilibrium -/

/-- The periodic profile generated by the paper's three rows, from an arbitrary
initial phase. -/
def cyclicPhaseProfile (phase : Fin 3) :
    (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  quittingCyclicContinuationBlockProfile
    FTV.CyclicAdmissibleCycle.ftvReward 2
    FTV.CyclicAdmissibleCycle.ftvBlock phase

/-- The three phase rows have the exact quit probabilities displayed in
Theorem 3.3. -/
theorem phaseRoot_quitProbability (c who : Player) :
    (FTV.CyclicAdmissibleCycle.phaseRoot c who true).toReal =
      FTV.CyclicMinimality.ExactCyclicPacket.standardQuitProb c who := by
  exact FTV.CyclicAdmissibleCycle.phaseRoot_quitProbability c who

/-- Every phase shift of the displayed cycle is an exact terminal equilibrium,
against all behavioral deviations. -/
theorem cyclicPhaseProfile_isEquilibrium (phase : Fin 3) :
    (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward) 0
      (cyclicPhaseProfile phase) := by
  exact isZeroAsymptoticNash_quittingCyclicContinuationBlockProfile
    FTV.CyclicAdmissibleCycle.ftvReward
    FTV.CyclicMinimality.namedTarget 2
    FTV.CyclicAdmissibleCycle.ftvBlock
    FTV.CyclicAdmissibleCycle.ftvBlock_isQuittingCyclicContinuationBlock
    FTV.CyclicAdmissibleCycle.isQuittingCycleAdmissible_ftvBlockCycle
    phase

/-- The terminal payoff of a phase shift is the corresponding promise vector. -/
theorem quittingTerminalPayoff_cyclicPhaseProfile (phase : Fin 3) :
    quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
        (cyclicPhaseProfile phase) =
      FTV.CyclicMinimality.ExactCyclicPacket.standardPromise phase := by
  have hvalue :=
    eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
      FTV.CyclicAdmissibleCycle.ftvReward
      (quittingCyclicContinuationBlockCycle 2
        FTV.CyclicAdmissibleCycle.ftvBlock)
      (quittingCyclicContinuationBlockValue 2
        FTV.CyclicAdmissibleCycle.ftvBlock)
      (quittingCyclicContinuationBlock_policy
        FTV.CyclicAdmissibleCycle.ftvReward
        FTV.CyclicMinimality.namedTarget 2
        FTV.CyclicAdmissibleCycle.ftvBlock
        FTV.CyclicAdmissibleCycle.ftvBlock_isQuittingCyclicContinuationBlock)
      (quittingCyclicContinuationBlock_prod_continueMass_lt_one
        FTV.CyclicAdmissibleCycle.ftvReward
        FTV.CyclicMinimality.namedTarget 2
        FTV.CyclicAdmissibleCycle.ftvBlock
        FTV.CyclicAdmissibleCycle.ftvBlock_isQuittingCyclicContinuationBlock)
  rw [cyclicPhaseProfile, quittingCyclicContinuationBlockProfile,
    quittingTerminalPayoff_cyclicBehaviorProfile, ← hvalue]
  fin_cases phase <;> rfl

/-- The phase-zero profile is the explicit profile of Theorem 3.3. -/
def cyclicProfile :
    (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  cyclicPhaseProfile 0

/-- **Theorem 3.3.** The displayed cyclic Markov profile is an equilibrium and
has reward `(1,2,1)`.  The checked Nash statement allows every behavioral
unilateral deviation, matching the paper's equilibrium notion. -/
theorem theorem3_3 :
    (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
        (quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward) 0
        cyclicProfile ∧
      quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
          cyclicProfile =
        FTV.CyclicMinimality.namedTarget := by
  constructor
  · exact cyclicPhaseProfile_isEquilibrium 0
  · simpa [cyclicProfile, cyclicPhaseProfile,
      FTV.CyclicAdmissibleCycle.ftvCyclicProfile] using
      FTV.CyclicAdmissibleCycle.quittingTerminalPayoff_ftvCyclicProfile

/-- The expected finite-horizon averages of the displayed profile converge
coordinatewise to `(1,2,1)`. -/
theorem tendsto_cyclicProfile_payoff (who : Player) :
    Tendsto
      (fun horizon : ℕ =>
        (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).finiteAveragePayoff
          none horizon cyclicProfile who)
      atTop (nhds (FTV.CyclicMinimality.namedTarget who)) := by
  simpa [cyclicProfile, cyclicPhaseProfile,
    FTV.CyclicAdmissibleCycle.ftvCyclicProfile] using
    FTV.CyclicAdmissibleCycle.tendsto_finiteAveragePayoff_ftvCyclicProfile
      who

/-- The paper's tail beginning at stage `l`; only `l mod 3` matters. -/
def cyclicTailProfile (l : ℕ) :
    (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  cyclicPhaseProfile (Fin.ofNat 3 l)

/-- The post-Theorem-3.3 observation that every tail triple is again an
exact Markov equilibrium. -/
theorem cyclicTailProfile_isEquilibrium (l : ℕ) :
    (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward) 0
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

/-! With `r` dates left in one owner's block, the continuation is the
survival-weighted segment from that owner's solo reward to the next cyclic
promise. -/
private def blockContinuation (owner : Player) (α : Hazard)
    (remaining : ℕ) : Payoff Player :=
  fun who =>
    (1 - (1 - α.1) ^ remaining) *
        FTV.CyclicMinimality.soloReward owner who +
      (1 - α.1) ^ remaining *
        FTV.CyclicMinimality.ExactCyclicPacket.standardPromise
          (FTV.CyclicMinimality.nextThree owner) who

private theorem blockRoot_eq_soloMixedRoot
    (n : ℕ) (α : Hazard) (time : ℕ) :
    blockRoot n α time =
      quittingSoloMixedRoot (Fin.ofNat 3 (time / n)) (coin α) := by
  funext who
  by_cases hwho : who = Fin.ofNat 3 (time / n)
  · subst who
    simp [blockRoot, quittingSoloMixedRoot]
  · rw [show blockRoot n α time who = PMF.pure false by
          unfold blockRoot
          split
          · rename_i heq
            exact (hwho (by simpa using heq)).elim
          · rfl,
        show quittingSoloMixedRoot (Fin.ofNat 3 (time / n)) (coin α) who =
            PMF.pure false by
          rw [quittingSoloMixedRoot,
            Function.update_of_ne (by simpa using hwho)]
          rfl]

private theorem blockContinuation_zero (owner : Player) (α : Hazard) :
    blockContinuation owner α 0 =
      FTV.CyclicMinimality.ExactCyclicPacket.standardPromise
        (FTV.CyclicMinimality.nextThree owner) := by
  funext who
  simp [blockContinuation]

private theorem blockContinuation_succ
    (owner : Player) (α : Hazard) (remaining : ℕ) :
    blockContinuation owner α (remaining + 1) =
      quittingRootSuccessorPayoff
        FTV.CyclicAdmissibleCycle.ftvReward
        (blockContinuation owner α remaining)
        (quittingSoloMixedRoot owner (coin α)) := by
  funext who
  rw [quittingRootSuccessorPayoff_soloMixedRoot,
    FTV.CyclicAdmissibleCycle.ftvReward_singletonTerminal]
  simp only [coin_true_toReal, coin_false_toReal]
  simp [blockContinuation, pow_succ]
  ring

private theorem blockContinuation_self
    (owner : Player) (α : Hazard) (remaining : ℕ) :
    blockContinuation owner α remaining owner = 1 := by
  fin_cases owner <;>
    simp [blockContinuation,
      FTV.CyclicMinimality.soloReward,
      FTV.CyclicMinimality.ExactCyclicPacket.standardPromise,
      FTV.CyclicMinimality.nextThree]

private theorem blockContinuation_rootNash
    (n : ℕ) (hn : 0 < n) (owner : Player) (α : Hazard)
    (hα : (1 - α.1) ^ n = (1 / 2 : ℝ))
    (remaining : ℕ) (hremaining : remaining < n) :
    IsεQuittingRootEndpointNash
      FTV.CyclicAdmissibleCycle.ftvReward
      (blockContinuation owner α remaining) 0
      (quittingSoloMixedRoot owner (coin α)) := by
  apply isZeroQuittingRootEndpointNash_soloMixedRoot
  · rw [FTV.CyclicAdmissibleCycle.ftvReward_singletonTerminal]
    rw [FTV.CyclicMinimality.soloReward_self,
      blockContinuation_self]
  · intro who hwho
    rw [FTV.CyclicAdmissibleCycle.ftvReward_singletonTerminal who,
      FTV.CyclicAdmissibleCycle.ftvReward_singletonTerminal owner]
    have hq0 : 0 ≤ 1 - α.1 := sub_nonneg.mpr α.2.2
    have hq1 : 1 - α.1 ≤ 1 := by linarith [α.2.1]
    have hpow0 : 0 ≤ (1 - α.1) ^ remaining := pow_nonneg hq0 remaining
    have hpow1 : (1 - α.1) ^ remaining ≤ 1 := by
      exact pow_le_one₀ hq0 hq1
    have hhalfPow : (1 / 2 : ℝ) ≤ (1 - α.1) ^ remaining := by
      rw [← hα]
      exact pow_le_pow_of_le_one hq0 hq1 hremaining.le
    have hhalfQ : (1 / 2 : ℝ) ≤ 1 - α.1 := by
      rw [← hα]
      exact pow_le_of_le_one hq0 hq1 (Nat.ne_of_gt hn)
    have hhalfProduct : (1 / 2 : ℝ) ≤
        (1 - α.1) * (1 - α.1) ^ remaining := by
      rw [← pow_succ', ← hα]
      exact pow_le_pow_of_le_one hq0 hq1 (by omega)
    fin_cases owner <;> fin_cases who <;>
      simp_all [blockContinuation,
        FTV.CyclicAdmissibleCycle.ftvReward,
        FTV.CyclicMinimality.terminalReward,
        FTV.CyclicMinimality.soloReward,
        FTV.CyclicMinimality.ExactCyclicPacket.standardPromise,
        FTV.CyclicMinimality.nextThree,
        coin_true_toReal, coin_false_toReal] <;>
      nlinarith

private theorem nextThree_ofNat (k : ℕ) :
    FTV.CyclicMinimality.nextThree (Fin.ofNat 3 k) =
      Fin.ofNat 3 (k + 1) := by
  generalize howner : Fin.ofNat 3 k = owner
  fin_cases owner <;>
    apply Fin.ext <;>
    simp_all [FTV.CyclicMinimality.nextThree, Fin.ext_iff,
      Nat.add_mod]

private theorem blockContinuation_full
    (n : ℕ) (owner : Player) (α : Hazard)
    (hα : (1 - α.1) ^ n = (1 / 2 : ℝ)) :
    blockContinuation owner α n =
      FTV.CyclicMinimality.ExactCyclicPacket.standardPromise owner := by
  rw [FTV.CyclicAdmissibleCycle.standardPromise_recursion]
  funext who
  simp only [blockContinuation, hα, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem div_succ_eq_of_mod_succ_lt
    {time n : ℕ} (hn : 0 < n) (h : time % n + 1 < n) :
    (time + 1) / n = time / n := by
  apply Nat.succ_div_of_mod_ne_zero
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n),
    Nat.mod_eq_of_lt h]
  omega

private theorem mod_succ_eq_of_mod_succ_lt
    {time n : ℕ} (hn : 0 < n) (h : time % n + 1 < n) :
    (time + 1) % n = time % n + 1 := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n),
    Nat.mod_eq_of_lt h]

private theorem div_succ_eq_of_mod_succ_eq
    {time n : ℕ} (hn : 0 < n) (h : time % n + 1 = n) :
    (time + 1) / n = time / n + 1 := by
  by_cases hone : n = 1
  · subst n
    simp
  have hn : 1 < n := by omega
  apply Nat.succ_div_of_mod_eq_zero
  rw [Nat.add_mod, Nat.mod_eq_of_lt hn, h, Nat.mod_self]

private theorem mod_succ_eq_zero_of_mod_succ_eq
    {time n : ℕ} (hn : 0 < n) (h : time % n + 1 = n) :
    (time + 1) % n = 0 := by
  by_cases hone : n = 1
  · subst n
    exact Nat.mod_one _
  have hn : 1 < n := by omega
  rw [Nat.add_mod, Nat.mod_eq_of_lt hn, h, Nat.mod_self]

private def blockValue (n : ℕ) (α : Hazard) (time : ℕ) : Payoff Player :=
  blockContinuation (Fin.ofNat 3 (time / n)) α (n - time % n)

private theorem blockValue_policy
    (n : ℕ) (hn : 0 < n) (α : Hazard)
    (hα : (1 - α.1) ^ n = (1 / 2 : ℝ)) (time : ℕ) :
    blockValue n α time =
      quittingRootSuccessorPayoff
        FTV.CyclicAdmissibleCycle.ftvReward
        (blockValue n α (time + 1)) (blockRoot n α time) := by
  rw [blockRoot_eq_soloMixedRoot]
  have hmod : time % n < n := Nat.mod_lt time hn
  rcases lt_or_eq_of_le (show time % n + 1 ≤ n by omega) with hinterior | hboundary
  · rw [blockValue, blockValue,
      div_succ_eq_of_mod_succ_lt hn hinterior,
      mod_succ_eq_of_mod_succ_lt hn hinterior]
    rw [show n - time % n = n - (time % n + 1) + 1 by omega]
    exact blockContinuation_succ
      (Fin.ofNat 3 (time / n)) α (n - (time % n + 1))
  · rw [blockValue, blockValue,
      div_succ_eq_of_mod_succ_eq hn hboundary,
      mod_succ_eq_zero_of_mod_succ_eq hn hboundary]
    calc
      blockContinuation (Fin.ofNat 3 (time / n)) α (n - time % n) =
          blockContinuation (Fin.ofNat 3 (time / n)) α (0 + 1) := by
            congr 2
            omega
      _ = quittingRootSuccessorPayoff
          FTV.CyclicAdmissibleCycle.ftvReward
          (blockContinuation (Fin.ofNat 3 (time / n)) α 0)
          (quittingSoloMixedRoot (Fin.ofNat 3 (time / n)) (coin α)) :=
            blockContinuation_succ _ _ _
      _ = quittingRootSuccessorPayoff
          FTV.CyclicAdmissibleCycle.ftvReward
          (blockContinuation (Fin.ofNat 3 (time / n + 1)) α n)
          (quittingSoloMixedRoot (Fin.ofNat 3 (time / n)) (coin α)) := by
            rw [blockContinuation_zero, blockContinuation_full n _ α hα,
              nextThree_ofNat]

private theorem blockValue_endpointNash
    (n : ℕ) (hn : 0 < n) (α : Hazard)
    (hα : (1 - α.1) ^ n = (1 / 2 : ℝ)) (time : ℕ) :
    IsεQuittingRootEndpointNash
      FTV.CyclicAdmissibleCycle.ftvReward
      (blockValue n α (time + 1)) 0 (blockRoot n α time) := by
  rw [blockRoot_eq_soloMixedRoot]
  have hmod : time % n < n := Nat.mod_lt time hn
  rcases lt_or_eq_of_le (show time % n + 1 ≤ n by omega) with hinterior | hboundary
  · rw [blockValue, div_succ_eq_of_mod_succ_lt hn hinterior,
      mod_succ_eq_of_mod_succ_lt hn hinterior]
    exact blockContinuation_rootNash n hn (Fin.ofNat 3 (time / n)) α hα
      (n - (time % n + 1)) (by omega)
  · rw [blockValue, div_succ_eq_of_mod_succ_eq hn hboundary,
      mod_succ_eq_zero_of_mod_succ_eq hn hboundary,
      Nat.sub_zero,
      blockContinuation_full n _ α hα, ← nextThree_ofNat,
      ← blockContinuation_zero]
    exact blockContinuation_rootNash n hn (Fin.ofNat 3 (time / n)) α hα 0 hn

private theorem blockValue_rootNash
    (n : ℕ) (hn : 0 < n) (α : Hazard)
    (hα : (1 - α.1) ^ n = (1 / 2 : ℝ)) (time : ℕ) :
    IsεQuittingRootNash
      FTV.CyclicAdmissibleCycle.ftvReward
      (blockValue n α (time + 1)) 0 (blockRoot n α time) := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  exact blockValue_endpointNash n hn α hα time

private theorem blockRoot_mod_period
    (n : ℕ) (α : Hazard) (time : ℕ) :
    blockRoot n α (time % (n * 3)) = blockRoot n α time := by
  unfold blockRoot
  rw [Nat.mod_mul_right_div_self]
  have howner : Fin.ofNat 3 (time / n % 3) = Fin.ofNat 3 (time / n) := by
    apply Fin.ext
    simp
  rw [howner]

private theorem blockValue_mod_period
    (n : ℕ) (α : Hazard) (time : ℕ) :
    blockValue n α (time % (n * 3)) = blockValue n α time := by
  unfold blockValue
  rw [Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]
  have howner : Fin.ofNat 3 (time / n % 3) = Fin.ofNat 3 (time / n) := by
    apply Fin.ext
    simp
  rw [howner]

private def blockCycle (n : ℕ) (α : Hazard) :
    Fin (n * 3) → Player → PMF Bool :=
  fun phase => blockRoot n α phase.val

private def blockCycleValue (n : ℕ) (α : Hazard) :
    Fin (n * 3) → Payoff Player :=
  fun phase => blockValue n α phase.val

private theorem blockCycle_policy
    (n : ℕ) (hn : 0 < n) (α : Hazard)
    (hα : (1 - α.1) ^ n = (1 / 2 : ℝ)) (phase : Fin (n * 3)) :
    blockCycleValue n α phase =
      quittingRootSuccessorPayoff
        FTV.CyclicAdmissibleCycle.ftvReward
        (blockCycleValue n α (finRotate (n * 3) phase))
        (blockCycle n α phase) := by
  letI : NeZero (n * 3) := ⟨by omega⟩
  have hstep := blockValue_policy n hn α hα phase.val
  unfold blockCycleValue blockCycle
  rw [finRotate_apply]
  have hval : ((phase + 1 : Fin (n * 3))).val =
      (phase.val + 1) % (n * 3) := by
    simp [Fin.val_add]
  rw [hval]
  rwa [blockValue_mod_period]

private theorem blockCycle_rootNash
    (n : ℕ) (hn : 0 < n) (α : Hazard)
    (hα : (1 - α.1) ^ n = (1 / 2 : ℝ)) (phase : Fin (n * 3)) :
    IsεQuittingRootNash
      FTV.CyclicAdmissibleCycle.ftvReward
      (blockCycleValue n α (finRotate (n * 3) phase)) 0
      (blockCycle n α phase) := by
  letI : NeZero (n * 3) := ⟨by omega⟩
  have hstep := blockValue_rootNash n hn α hα phase.val
  unfold blockCycleValue blockCycle
  rw [finRotate_apply]
  have hval : ((phase + 1 : Fin (n * 3))).val =
      (phase.val + 1) % (n * 3) := by
    simp [Fin.val_add]
  rw [hval]
  rwa [blockValue_mod_period]

private theorem blockCycle_admissible (n : ℕ) (α : Hazard) :
    IsQuittingCycleAdmissible
      FTV.CyclicAdmissibleCycle.ftvReward (blockCycle n α) := by
  intro who
  right
  rw [FTV.CyclicAdmissibleCycle.ftvReward_singletonTerminal,
    FTV.CyclicMinimality.soloReward_self]
  norm_num

private theorem blockCycle_absorbs
    (n : ℕ) (hn : 0 < n) (α : Hazard)
    (hα : (1 - α.1) ^ n = (1 / 2 : ℝ)) :
    (∏ phase : Fin (n * 3),
      quittingStationaryContinueMass (blockCycle n α phase)) < 1 := by
  have hαpos : 0 < α.1 := by
    by_contra hnot
    have hzero : α.1 = 0 := le_antisymm (le_of_not_gt hnot) α.2.1
    rw [hzero] at hα
    norm_num at hα
  let origin : Fin (n * 3) := ⟨0, by positivity⟩
  refine Math.Finset.prod_lt_one_of_mem Finset.univ _ origin
    (Finset.mem_univ origin)
    (fun phase _ _ => quittingStationaryContinueMass_nonneg
      (blockCycle n α phase))
    (fun phase _ _ => quittingStationaryContinueMass_le_one
      (blockCycle n α phase)) ?_
  rw [blockCycle, show origin.val = 0 by rfl, blockRoot_eq_soloMixedRoot,
    quittingStationaryContinueMass_soloMixedRoot, coin_false_toReal]
  linarith

private theorem blockCyclicProfile_eq
    (n : ℕ) (hn : 0 < n) (α : Hazard) :
    quittingCyclicBehaviorProfile
      FTV.CyclicAdmissibleCycle.ftvReward (blockCycle n α)
        (⟨0, by positivity⟩ : Fin (n * 3)) =
      quittingRootSequenceProfile
        FTV.CyclicAdmissibleCycle.ftvReward (blockRoot n α) 0 := by
  have hroots : quittingCyclicRootSequence (blockCycle n α)
      (⟨0, by positivity⟩ : Fin (n * 3)) = blockRoot n α := by
    funext time
    unfold quittingCyclicRootSequence quittingCyclicOrbit blockCycle
    simp only [zero_add]
    exact blockRoot_mod_period n α time
  rw [quittingCyclicBehaviorProfile, hroots]

/-- The paper's block-repeated extension of Theorem 3.3. -/
theorem blockRepeatedEquilibrium
    (n : ℕ) (hn : 0 < n) (α : Hazard)
    (hα : (1 - α.1) ^ n = (1 / 2 : ℝ)) :
    (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward) 0
      (quittingRootSequenceProfile
        FTV.CyclicAdmissibleCycle.ftvReward
        (blockRoot n α) 0) := by
  have hcompiled :=
    isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_admissible
      FTV.CyclicAdmissibleCycle.ftvReward
      (blockCycle n α) (blockCycleValue n α)
      (⟨0, by positivity⟩ : Fin (n * 3))
      (blockCycle_policy n hn α hα)
      (blockCycle_rootNash n hn α hα)
      (blockCycle_absorbs n hn α hα)
      (blockCycle_admissible n α)
  rwa [blockCyclicProfile_eq n hn α] at hcompiled

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
      owner (time + 1) = FTV.CyclicMinimality.nextThree (owner time)) ∧
    (∀ time, ∃ later, time < later ∧
      owner later = FTV.CyclicMinimality.nextThree (owner time))

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
    (packet : FTV.CyclicMinimality.ExactCyclicPacket K)
    (phase : Fin K) :
    ∃! who : Player, 0 < packet.quitProb phase who := by
  exact packet.existsUnique_activeRole phase

/-- Checked lower bound for finite exact cyclic packets. -/
theorem exactCyclicPacket_period_ge_three
    {K : ℕ} [NeZero K]
    (packet : FTV.CyclicMinimality.ExactCyclicPacket K) :
    3 ≤ K := by
  exact packet.period_ge_three

/-! ### Theorem 3.5: equilibrium reward set -/

/-- Equilibrium rewards in the paper's game.  Behavioral profiles are used in
this definition because every behavior profile is outcome-equivalent on the
unique live history to a Markov sequence. -/
def EquilibriumRewards : Set (Payoff Player) :=
  {payoff | ∃ profile :
      (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).BehaviorProfile,
    (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward) 0
      profile ∧
    quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
      profile = payoff}

/-- The same reward set quantified directly over paper Markov profiles. -/
def MarkovEquilibriumRewards : Set (Payoff Player) :=
  {payoff | ∃ profile : MarkovProfile,
    IsMarkovEpsilonEquilibrium 0 profile ∧
      quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
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
  (halfHazard α).1 • FTV.CyclicMinimality.soloReward owner +
    (1 - (halfHazard α).1) •
      FTV.CyclicMinimality.ExactCyclicPacket.standardPromise
        (FTV.CyclicMinimality.nextThree owner)

/-- The profile used for the sufficiency half of Theorem 3.5. -/
def edgeProfile (owner : Player) (α : Hazard) :
    (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  quittingRootThenContinuationProfile
    FTV.CyclicAdmissibleCycle.ftvReward
    (edgeRoot owner α)
    (cyclicPhaseProfile (FTV.CyclicMinimality.nextThree owner))

/-- Expected payoff of a row with one possible quitter. -/
theorem quittingRootSuccessorPayoff_soloRoot
    (owner : Player) (p : Hazard) (tail : Payoff Player) :
    quittingRootSuccessorPayoff
        FTV.CyclicAdmissibleCycle.ftvReward tail
        (soloRoot owner p) =
      p.1 • FTV.CyclicMinimality.soloReward owner +
        (1 - p.1) • tail := by
  funext who
  change quittingRootExpectedPayoff
    FTV.CyclicAdmissibleCycle.ftvReward tail
      (soloRoot owner p) who = _
  unfold quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  fin_cases owner <;> fin_cases who <;>
    simp [soloRoot,
      FTV.CyclicMinimality.terminalReward,
      FTV.CyclicMinimality.soloReward,
      Matrix.cons_val_two, expect_pure]

/-- Endpoint differences at the perturbed first row. -/
theorem endpointDifference_edgeRoot
    (owner : Player) (α : Hazard) (who : Player) :
    quittingRootEndpointDifference
        FTV.CyclicAdmissibleCycle.ftvReward
        (FTV.CyclicMinimality.ExactCyclicPacket.standardPromise
          (FTV.CyclicMinimality.nextThree owner))
        (edgeRoot owner α) who =
      if who = owner then 0
      else if who = FTV.CyclicMinimality.nextThree owner then
        -(3 * α.1 / 2)
      else α.1 - 1 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3,
    Math.PMFProduct.expect_pmfPi_fin3]
  fin_cases owner <;> fin_cases who <;>
    simp [edgeRoot, soloRoot, halfHazard,
      FTV.CyclicMinimality.terminalReward,
      FTV.CyclicMinimality.ExactCyclicPacket.standardPromise,
      FTV.CyclicMinimality.nextThree,
      Matrix.cons_val_two, expect_pure] <;> ring

/-- The perturbed first row is exact endpoint Nash against the successor
promise for every `α∈[0,1]`. -/
theorem isZeroEndpointNash_edgeRoot
    (owner : Player) (α : Hazard) :
    IsεQuittingRootEndpointNash
      FTV.CyclicAdmissibleCycle.ftvReward
      (FTV.CyclicMinimality.ExactCyclicPacket.standardPromise
        (FTV.CyclicMinimality.nextThree owner))
      0 (edgeRoot owner α) := by
  intro who
  rw [endpointDifference_edgeRoot]
  fin_cases owner <;> fin_cases who <;>
    simp [edgeRoot, soloRoot, halfHazard,
      FTV.CyclicMinimality.nextThree] <;>
    nlinarith [α.2.1, α.2.2]

/-- The perturbed-first-row construction is an exact equilibrium. -/
theorem edgeProfile_isEquilibrium (owner : Player) (α : Hazard) :
    (quittingGame FTV.CyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward) 0
      (edgeProfile owner α) := by
  have h :=
    isεAsymptoticNash_quittingRootThenContinuation_of_endpointNash_target_close
      FTV.CyclicAdmissibleCycle.ftvReward
      (edgeRoot owner α)
      (cyclicPhaseProfile
        (FTV.CyclicMinimality.nextThree owner))
      (FTV.CyclicMinimality.ExactCyclicPacket.standardPromise
        (FTV.CyclicMinimality.nextThree owner))
      (η := 0) (ε := 0) (δ := 0) (by norm_num) (by norm_num)
      (isZeroEndpointNash_edgeRoot owner α)
      (cyclicPhaseProfile_isEquilibrium
        (FTV.CyclicMinimality.nextThree owner))
      (by
        intro who
        rw [quittingTerminalPayoff_cyclicPhaseProfile]
        norm_num)
  simpa [edgeProfile] using h

/-- The construction realizes its displayed edge target. -/
theorem quittingTerminalPayoff_edgeProfile
    (owner : Player) (α : Hazard) :
    quittingTerminalPayoff FTV.CyclicAdmissibleCycle.ftvReward
        (edgeProfile owner α) =
      edgeTarget owner α := by
  funext who
  rw [edgeProfile, quittingTerminalPayoff_rootThenContinuation_eq,
    quittingTerminalPayoff_cyclicPhaseProfile]
  change quittingRootSuccessorPayoff
      FTV.CyclicAdmissibleCycle.ftvReward
      (FTV.CyclicMinimality.ExactCyclicPacket.standardPromise
        (FTV.CyclicMinimality.nextThree owner))
      (soloRoot owner (halfHazard α)) who = _
  rw [quittingRootSuccessorPayoff_soloRoot]
  rfl

@[simp] theorem edgeTarget_zero (α : Hazard) :
    edgeTarget 0 α = ![1, 1 + α.1, 2 - α.1] := by
  funext who
  fin_cases who <;>
    simp [edgeTarget, halfHazard,
      FTV.CyclicMinimality.soloReward,
      FTV.CyclicMinimality.ExactCyclicPacket.standardPromise,
      FTV.CyclicMinimality.nextThree] <;> ring

@[simp] theorem edgeTarget_one (α : Hazard) :
    edgeTarget 1 α = ![2 - α.1, 1, 1 + α.1] := by
  funext who
  fin_cases who <;>
    simp [edgeTarget, halfHazard,
      FTV.CyclicMinimality.soloReward,
      FTV.CyclicMinimality.ExactCyclicPacket.standardPromise,
      FTV.CyclicMinimality.nextThree] <;> ring

@[simp] theorem edgeTarget_two (α : Hazard) :
    edgeTarget 2 α = ![1 + α.1, 2 - α.1, 1] := by
  funext who
  fin_cases who <;>
    simp [edgeTarget, halfHazard,
      FTV.CyclicMinimality.soloReward,
      FTV.CyclicMinimality.ExactCyclicPacket.standardPromise,
      FTV.CyclicMinimality.nextThree] <;> ring

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
