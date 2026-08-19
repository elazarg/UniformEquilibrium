import UniformEquilibrium.Quitting.Examples.FTV.CyclicAdmissibleCycle
import UniformEquilibrium.Quitting.Root.ApproximateFirstBranch
import UniformEquilibrium.Quitting.Stationary.BestResponse

/-!
# Flesch--Thuijsman--Vrieze (1997)

J. Flesch, F. Thuijsman and O. J. Vrieze, *Cyclic Markov Equilibria in
Stochastic Games*, International Journal of Game Theory 26 (1997), 303--314.

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
def paperTerminalReward (action : Player → Bool) : Payoff Player :=
  GameTheory.FTVCyclicMinimality.terminalReward action

@[simp] theorem paperTerminalReward_TLN :
    paperTerminalReward ![false, false, false] = ![0, 0, 0] := by
  rfl

@[simp] theorem paperTerminalReward_BLN :
    paperTerminalReward ![true, false, false] = ![1, 3, 0] := by
  rfl

@[simp] theorem paperTerminalReward_TRN :
    paperTerminalReward ![false, true, false] = ![0, 1, 3] := by
  rfl

@[simp] theorem paperTerminalReward_TLF :
    paperTerminalReward ![false, false, true] = ![3, 0, 1] := by
  rfl

@[simp] theorem paperTerminalReward_BRN :
    paperTerminalReward ![true, true, false] = ![1, 0, 1] := by
  rfl

@[simp] theorem paperTerminalReward_BLF :
    paperTerminalReward ![true, false, true] = ![0, 1, 1] := by
  rfl

@[simp] theorem paperTerminalReward_TRF :
    paperTerminalReward ![false, true, true] = ![1, 1, 0] := by
  rfl

@[simp] theorem paperTerminalReward_BRF :
    paperTerminalReward ![true, true, true] = ![0, 0, 0] := by
  rfl

/-- The quitter-set presentation used by the repository is exactly the paper's
seven absorbing rows. -/
theorem ftvReward_quitters (action : Player → Bool)
    (h : (quittingQuitters action).Nonempty) :
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        ⟨quittingQuitters action, h⟩ =
      paperTerminalReward action := by
  exact GameTheory.FTVCyclicAdmissibleCycle.ftvReward_quitters action h

/-- A Boolean coin whose `true` mass is the supplied hazard. -/
def paperCoin (p : Hazard) : PMF Bool :=
  GameTheory.QuittingBoundedSurgeryDescentCounterexample.coin
    p.1 p.2.1 p.2.2

@[simp] theorem paperCoin_true_toReal (p : Hazard) :
    (paperCoin p true).toReal = p.1 := by
  exact GameTheory.QuittingBoundedSurgeryDescentCounterexample.coin_true_toReal
    p.1 p.2.1 p.2.2

@[simp] theorem paperCoin_false_toReal (p : Hazard) :
    (paperCoin p false).toReal = 1 - p.1 := by
  exact GameTheory.QuittingBoundedSurgeryDescentCounterexample.coin_false_toReal
    p.1 p.2.1 p.2.2

@[simp] theorem expect_paperCoin (p : Hazard) (f : Bool → ℝ) :
    expect (paperCoin p) f = p.1 * f true + (1 - p.1) * f false := by
  rw [expect_eq_sum, Fintype.sum_bool, paperCoin_true_toReal,
    paperCoin_false_toReal]

/-- A Markov profile is the paper's sequence of quit probabilities, indexed
from repository time zero rather than paper stage one. -/
abbrev PaperMarkovProfile := ℕ → Player → Hazard

/-- The product root played at one date of a paper Markov profile. -/
def paperMarkovRoot (profile : PaperMarkovProfile) (time : ℕ) :
    Player → PMF Bool :=
  fun who => paperCoin (profile time who)

/-- The behavior-profile adapter for a paper Markov profile.  Histories after
absorption are irrelevant, and before absorption there is only one history. -/
def paperMarkovBehaviorProfile (profile : PaperMarkovProfile) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  quittingRootSequenceProfile GameTheory.FTVCyclicAdmissibleCycle.ftvReward
    (paperMarkovRoot profile) 0

/-- Exact terminal `ε`-equilibrium for a paper Markov profile. -/
def IsPaperMarkovEpsilonEquilibrium (ε : ℝ)
    (profile : PaperMarkovProfile) : Prop :=
  (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
    (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) ε
    (paperMarkovBehaviorProfile profile)

/-- A stationary mixed profile is one hazard for each player. -/
abbrev PaperStationaryProfile := Player → Hazard

/-- The product root of a paper stationary profile. -/
def paperStationaryRoot (profile : PaperStationaryProfile) :
    Player → PMF Bool :=
  fun who => paperCoin (profile who)

/-- The repository behavior profile generated by a paper stationary profile. -/
def paperStationaryBehaviorProfile (profile : PaperStationaryProfile) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  quittingStationaryProfile GameTheory.FTVCyclicAdmissibleCycle.ftvReward
    (paperStationaryRoot profile)

/-- Exact terminal `ε`-equilibrium for a paper stationary profile. -/
def IsPaperStationaryEpsilonEquilibrium (ε : ℝ)
    (profile : PaperStationaryProfile) : Prop :=
  (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
    (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) ε
    (paperStationaryBehaviorProfile profile)

/-! For a Markov strategy triple `θ`, the paper writes `q_θ(a)` for the
probability of eventual absorption at absorbing row `a`, and
`γᵢ(θ)=∑_a q_θ(a)rᵢ(a)`.  The formula remains valid when total absorption
probability is below one because the never-absorbing payoff is zero.  This is
exactly the stopping-law definition underlying `quittingTerminalPayoff`.
-/

/-! ## Section 3: analysis -/

/-! ### The pure stationary best-reply reduction

The paper cites the standard fact that against stationary opponents some pure
stationary best reply exists.  In this one-live-state game the two pure choices
are Quit immediately and Never quit.  The imported stationary Snell-cap theorem
proves the stronger behavioral statement whenever the opponents absorb with
positive probability. -/

theorem stationary_bestReply_is_quitNow_or_never
    (root : Player → PMF Bool) (who : Player)
    (hcontracts :
      quittingStationaryFixedOpponentsContinueMass root who < 1) :
    ∃ choice : Option ℕ,
      quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
          (Function.update
            (quittingStationaryProfile
              GameTheory.FTVCyclicAdmissibleCycle.ftvReward root)
            who
            (quittingPureTimeBehaviorStrategy
              GameTheory.FTVCyclicAdmissibleCycle.ftvReward who choice)) who =
        quittingStationaryUnilateralCap
          GameTheory.FTVCyclicAdmissibleCycle.ftvReward root who := by
  exact exists_pureTimeBehaviorStrategy_terminalPayoff_eq_unilateralCap
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward root who hcontracts

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

/-! The generic stationary files already provide the exact payoff fixed point,
root-Nash extraction, pure-time best-response cap, and stationary gain
factorization.  What is not yet assembled is the table-specific computation
that converts those generic inequalities, including the zero-absorption corner,
into every field of `StationaryNecessaryConditions`.  That explicit adapter is
the sole `sorry` used by Lemma 3.1 below. -/
theorem stationaryEquilibrium_implies_necessaryConditions
    (profile : PaperStationaryProfile)
    (h : IsPaperStationaryEpsilonEquilibrium 0 profile) :
    StationaryNecessaryConditions
      (profile 0).1 (profile 1).1 (profile 2).1 := by
  sorry

/-- **Lemma 3.1.** There is no stationary equilibrium in `Γ`. -/
theorem paper_lemma3_1 :
    ¬ ∃ profile : PaperStationaryProfile,
      IsPaperStationaryEpsilonEquilibrium 0 profile := by
  rintro ⟨profile, hprofile⟩
  apply not_exists_stationaryNecessaryConditions
  exact ⟨(profile 0).1, (profile 1).1, (profile 2).1,
    stationaryEquilibrium_implies_necessaryConditions profile hprofile⟩

/-! ### Theorem 3.2: a positive stationary exploitability gap

The proof takes stationary `ε`-equilibria with `ε ↓ 0`, extracts a convergent
subsequence of their three hazards, and separates an absorbing limit from the
all-Continue limit.  The absorbing case passes equilibrium inequalities to an
exact stationary equilibrium.  At the recurrent limit, one cyclic singleton
absorption mass is selected as maximal and the paper obtains a strict pure
deviation in either subcase.

The current stationary API has the pointwise payoff and best-response formulas,
but no packaged continuity theorem across the singular all-Continue root.  The
missing proof is exactly that two-case compactness argument; it is not inferred
from Lemma 3.1, since terminal stationary payoff is discontinuous at the
all-Continue root. -/
def NoSmallStationaryEpsilonEquilibrium : Prop :=
  ∃ threshold : ℝ, 0 < threshold ∧
    ∀ ε : ℝ, 0 < ε → ε < threshold →
      ¬ ∃ profile : PaperStationaryProfile,
        IsPaperStationaryEpsilonEquilibrium ε profile

/-- **Theorem 3.2.** Stationary `ε`-equilibria fail for every sufficiently
small positive `ε`. -/
theorem paper_theorem3_2 : NoSmallStationaryEpsilonEquilibrium := by
  sorry

/-! The abstract's phrase "stationary ε-equilibria (ε > 0) do not exist" cannot
literally quantify over every positive `ε`: bounded payoffs make every profile
an `ε`-equilibrium once `ε` is large enough.  The following checked refutation
uses the repository's canonical reward bound, without choosing the sharp bound
`3` for this table. -/
def AbstractAllPositiveStationaryImpossibility : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ¬ ∃ profile : PaperStationaryProfile,
      IsPaperStationaryEpsilonEquilibrium ε profile

/-- A stationary profile is an approximate equilibrium at one positive, possibly
large, error. -/
theorem exists_positive_stationaryEpsilonEquilibrium :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ profile : PaperStationaryProfile,
        IsPaperStationaryEpsilonEquilibrium ε profile := by
  let zeroHazard : Hazard := ⟨0, by norm_num⟩
  let profile : PaperStationaryProfile := fun _ => zeroHazard
  let M := quittingRewardBound GameTheory.FTVCyclicAdmissibleCycle.ftvReward
  have hM : 0 < M := by
    have hthree := GameTheory.FTVCyclicAdmissibleCycle.three_le_quittingRewardBound
    dsimp [M]
    linarith
  refine ⟨2 * M, by positivity, profile, ?_⟩
  intro who deviation
  have hdev := abs_quittingTerminalPayoff_le_quittingRewardBound
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward
    (Function.update (paperStationaryBehaviorProfile profile) who deviation) who
  have hbase := abs_quittingTerminalPayoff_le_quittingRewardBound
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward
    (paperStationaryBehaviorProfile profile) who
  have hdev_le :
      quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
          (Function.update (paperStationaryBehaviorProfile profile) who deviation) who ≤
        M := by
    exact (le_abs_self _).trans (by simpa [M] using hdev)
  have hbase_le :
      -M ≤ quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
          (paperStationaryBehaviorProfile profile) who := by
    exact (abs_le.mp (by simpa [M] using hbase)).1
  linarith

/-- Refutation of the abstract's literal all-positive-`ε` reading. -/
theorem not_abstractAllPositiveStationaryImpossibility :
    ¬ AbstractAllPositiveStationaryImpossibility := by
  rintro h
  obtain ⟨ε, hε, profile, hprofile⟩ :=
    exists_positive_stationaryEpsilonEquilibrium
  exact (h ε hε) ⟨profile, hprofile⟩

/-! ### Theorem 3.3: the cyclic Markov equilibrium -/

/-- The paper's phase-`c` row: only player `c` quits, with probability `1/2`. -/
def paperPhaseRoot (c : Player) : Player → PMF Bool :=
  GameTheory.FTVCyclicAdmissibleCycle.phaseRoot c

/-- The periodic profile generated by the paper's three rows, from an arbitrary
initial phase. -/
def paperCyclicPhaseProfile (phase : Fin 3) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  quittingCyclicContinuationBlockProfile
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward 2
    GameTheory.FTVCyclicAdmissibleCycle.ftvBlock phase

/-- The three phase rows have the exact quit probabilities displayed in
Theorem 3.3. -/
theorem paperPhaseRoot_quitProbability (c who : Player) :
    (paperPhaseRoot c who true).toReal =
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardQuitProb c who := by
  exact GameTheory.FTVCyclicAdmissibleCycle.phaseRoot_quitProbability c who

/-- Every phase shift of the displayed cycle is an exact terminal equilibrium,
against all behavioral deviations. -/
theorem paperCyclicPhaseProfile_isEquilibrium (phase : Fin 3) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) 0
      (paperCyclicPhaseProfile phase) := by
  exact isZeroAsymptoticNash_quittingCyclicContinuationBlockProfile
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward
    GameTheory.FTVCyclicMinimality.namedTarget 2
    GameTheory.FTVCyclicAdmissibleCycle.ftvBlock
    GameTheory.FTVCyclicAdmissibleCycle.ftvBlock_isQuittingCyclicContinuationBlock
    GameTheory.FTVCyclicAdmissibleCycle.isQuittingCycleAdmissible_ftvBlockCycle
    phase

/-- The terminal payoff of a phase shift is the corresponding promise vector. -/
theorem quittingTerminalPayoff_paperCyclicPhaseProfile (phase : Fin 3) :
    quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (paperCyclicPhaseProfile phase) =
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
  rw [paperCyclicPhaseProfile, quittingCyclicContinuationBlockProfile,
    quittingTerminalPayoff_cyclicBehaviorProfile, ← hvalue]
  fin_cases phase <;> rfl

/-- The phase-zero profile is the explicit profile of Theorem 3.3. -/
def paperCyclicProfile :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  paperCyclicPhaseProfile 0

/-- **Theorem 3.3.** The displayed cyclic Markov profile is an equilibrium and
has reward `(1,2,1)`.  The checked Nash statement allows every behavioral
unilateral deviation, a stronger deviation class than the paper needs. -/
theorem paper_theorem3_3 :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
        (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) 0
        paperCyclicProfile ∧
      quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
          paperCyclicProfile =
        GameTheory.FTVCyclicMinimality.namedTarget := by
  constructor
  · exact paperCyclicPhaseProfile_isEquilibrium 0
  · simpa [paperCyclicProfile, paperCyclicPhaseProfile,
      GameTheory.FTVCyclicAdmissibleCycle.ftvCyclicProfile] using
      GameTheory.FTVCyclicAdmissibleCycle.quittingTerminalPayoff_ftvCyclicProfile

/-- The expected finite-horizon averages of the displayed profile converge
coordinatewise to `(1,2,1)`. -/
theorem tendsto_paperCyclicProfile_payoff (who : Player) :
    Tendsto
      (fun horizon : ℕ =>
        (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).finiteAveragePayoff
          none horizon paperCyclicProfile who)
      atTop (nhds (GameTheory.FTVCyclicMinimality.namedTarget who)) := by
  simpa [paperCyclicProfile, paperCyclicPhaseProfile,
    GameTheory.FTVCyclicAdmissibleCycle.ftvCyclicProfile] using
    GameTheory.FTVCyclicAdmissibleCycle.tendsto_finiteAveragePayoff_ftvCyclicProfile
      who

/-- The paper's tail beginning at stage `l`; only `l mod 3` matters. -/
def paperCyclicTailProfile (l : ℕ) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  paperCyclicPhaseProfile (Fin.ofNat 3 l)

/-- The post-Theorem-3.3 observation that every tail triple is again an
exact Markov equilibrium. -/
theorem paperCyclicTailProfile_isEquilibrium (l : ℕ) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) 0
      (paperCyclicTailProfile l) := by
  exact paperCyclicPhaseProfile_isEquilibrium (Fin.ofNat 3 l)

/-! The paper next repeats each active phase for `n` stages, with one hazard
`α` satisfying `(1-α)^n=1/2`.  Proving the claim in the current semantic API
requires a length-`3n` value word and its exact endpoint inequalities at every
intermediate stage.  The imported three-phase certificate contracts each
whole block but does not supply those intermediate promises.  This is the
precise missing adapter for the following statement. -/

def paperBlockRoot (n : ℕ) (α : Hazard) (time : ℕ) : Player → PMF Bool :=
  fun who =>
    if who = Fin.ofNat 3 (time / n) then paperCoin α else PMF.pure false

/-- The paper's block-repeated extension of Theorem 3.3. -/
def PaperBlockRepeatedEquilibriumClaim : Prop :=
  ∀ n : ℕ, 0 < n → ∀ α : Hazard,
    (1 - α.1) ^ n = (1 / 2 : ℝ) →
      (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
        (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) 0
        (quittingRootSequenceProfile
          GameTheory.FTVCyclicAdmissibleCycle.ftvReward
          (paperBlockRoot n α) 0)

theorem paper_blockRepeatedEquilibrium : PaperBlockRepeatedEquilibriumClaim := by
  sorry

/-! ### Theorem 3.4: all equilibria are cyclic -/

/-- The paper removes stages at which every player surely continues. -/
def PaperHasNoEmptyStage (profile : PaperMarkovProfile) : Prop :=
  ∀ time, ∃ who, 0 < (profile time who).1

/-- A precise form of "exactly one positive hazard, and the active players
appear cyclically in the order 1,2,3".  Consecutive stages may keep the same
owner; every run is eventually followed by the cyclic successor. -/
def PaperHasCyclicSupport (profile : PaperMarkovProfile) : Prop :=
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
theorem paper_theorem3_4 (profile : PaperMarkovProfile)
    (hnonempty : PaperHasNoEmptyStage profile)
    (hequilibrium : IsPaperMarkovEpsilonEquilibrium 0 profile) :
    PaperHasCyclicSupport profile := by
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
def PaperFeasibleEquilibriumRewards : Set (Payoff Player) :=
  {payoff | ∃ profile :
      (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile,
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) 0
      profile ∧
    quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
      profile = payoff}

/-- The set printed in Theorem 3.5. -/
def PaperRewardRegion : Set (Payoff Player) :=
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
def paperSoloRoot (owner : Player) (p : Hazard) : Player → PMF Bool :=
  fun who => if who = owner then paperCoin p else PMF.pure false

/-- The first row in the paper's construction of the edge reward with
parameter `α`; its active hazard is `α/2`. -/
def paperEdgeRoot (owner : Player) (α : Hazard) : Player → PMF Bool :=
  paperSoloRoot owner (halfHazard α)

/-- The reward produced by the first perturbed row followed by the standard
cycle at the successor phase. -/
def paperEdgeTarget (owner : Player) (α : Hazard) : Payoff Player :=
  (halfHazard α).1 • GameTheory.FTVCyclicMinimality.soloReward owner +
    (1 - (halfHazard α).1) •
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise
        (GameTheory.FTVCyclicMinimality.nextThree owner)

/-- The profile used for the sufficiency half of Theorem 3.5. -/
def paperEdgeProfile (owner : Player) (α : Hazard) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).BehaviorProfile :=
  quittingRootThenContinuationProfile
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward
    (paperEdgeRoot owner α)
    (paperCyclicPhaseProfile (GameTheory.FTVCyclicMinimality.nextThree owner))

/-- Expected payoff of a row with one possible quitter. -/
theorem quittingRootSuccessorPayoff_paperSoloRoot
    (owner : Player) (p : Hazard) (tail : Payoff Player) :
    quittingRootSuccessorPayoff
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward tail
        (paperSoloRoot owner p) =
      p.1 • GameTheory.FTVCyclicMinimality.soloReward owner +
        (1 - p.1) • tail := by
  funext who
  change quittingRootExpectedPayoff
    GameTheory.FTVCyclicAdmissibleCycle.ftvReward tail
      (paperSoloRoot owner p) who = _
  unfold quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  fin_cases owner <;> fin_cases who <;>
    simp [paperSoloRoot, paperTerminalReward,
      GameTheory.FTVCyclicMinimality.terminalReward,
      GameTheory.FTVCyclicMinimality.soloReward,
      Matrix.cons_val_two, expect_pure] <;> ring

/-- Endpoint differences at the perturbed first row. -/
theorem endpointDifference_paperEdgeRoot
    (owner : Player) (α : Hazard) (who : Player) :
    quittingRootEndpointDifference
        GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise
          (GameTheory.FTVCyclicMinimality.nextThree owner))
        (paperEdgeRoot owner α) who =
      if who = owner then 0
      else if who = GameTheory.FTVCyclicMinimality.nextThree owner then
        -(3 * α.1 / 2)
      else α.1 - 1 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3,
    Math.PMFProduct.expect_pmfPi_fin3]
  fin_cases owner <;> fin_cases who <;>
    simp [paperEdgeRoot, paperSoloRoot, halfHazard, paperTerminalReward,
      GameTheory.FTVCyclicMinimality.terminalReward,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise,
      GameTheory.FTVCyclicMinimality.nextThree,
      Matrix.cons_val_two, expect_pure] <;> ring

/-- The perturbed first row is exact endpoint Nash against the successor
promise for every `α∈[0,1]`. -/
theorem isZeroEndpointNash_paperEdgeRoot
    (owner : Player) (α : Hazard) :
    IsεQuittingRootEndpointNash
      GameTheory.FTVCyclicAdmissibleCycle.ftvReward
      (GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise
        (GameTheory.FTVCyclicMinimality.nextThree owner))
      0 (paperEdgeRoot owner α) := by
  intro who
  rw [endpointDifference_paperEdgeRoot]
  fin_cases owner <;> fin_cases who <;>
    simp [paperEdgeRoot, paperSoloRoot, halfHazard,
      GameTheory.FTVCyclicMinimality.nextThree] <;>
    nlinarith [α.2.1, α.2.2]

/-- The perturbed-first-row construction is an exact equilibrium. -/
theorem paperEdgeProfile_isEquilibrium (owner : Player) (α : Hazard) :
    (quittingGame GameTheory.FTVCyclicAdmissibleCycle.ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward) 0
      (paperEdgeProfile owner α) := by
  have h :=
    isεAsymptoticNash_quittingRootThenContinuation_of_endpointNash_target_close
      GameTheory.FTVCyclicAdmissibleCycle.ftvReward
      (paperEdgeRoot owner α)
      (paperCyclicPhaseProfile
        (GameTheory.FTVCyclicMinimality.nextThree owner))
      (GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise
        (GameTheory.FTVCyclicMinimality.nextThree owner))
      (η := 0) (ε := 0) (δ := 0) (by norm_num) (by norm_num)
      (isZeroEndpointNash_paperEdgeRoot owner α)
      (paperCyclicPhaseProfile_isEquilibrium
        (GameTheory.FTVCyclicMinimality.nextThree owner))
      (by
        intro who
        rw [quittingTerminalPayoff_paperCyclicPhaseProfile]
        norm_num)
  simpa [paperEdgeProfile] using h

/-- The construction realizes its displayed edge target. -/
theorem quittingTerminalPayoff_paperEdgeProfile
    (owner : Player) (α : Hazard) :
    quittingTerminalPayoff GameTheory.FTVCyclicAdmissibleCycle.ftvReward
        (paperEdgeProfile owner α) =
      paperEdgeTarget owner α := by
  funext who
  rw [paperEdgeProfile, quittingTerminalPayoff_rootThenContinuation_eq,
    quittingTerminalPayoff_paperCyclicPhaseProfile]
  change quittingRootSuccessorPayoff
      GameTheory.FTVCyclicAdmissibleCycle.ftvReward
      (GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise
        (GameTheory.FTVCyclicMinimality.nextThree owner))
      (paperSoloRoot owner (halfHazard α)) who = _
  rw [quittingRootSuccessorPayoff_paperSoloRoot]
  rfl

@[simp] theorem paperEdgeTarget_zero (α : Hazard) :
    paperEdgeTarget 0 α = ![1, 1 + α.1, 2 - α.1] := by
  funext who
  fin_cases who <;>
    simp [paperEdgeTarget, halfHazard,
      GameTheory.FTVCyclicMinimality.soloReward,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise,
      GameTheory.FTVCyclicMinimality.nextThree] <;> ring

@[simp] theorem paperEdgeTarget_one (α : Hazard) :
    paperEdgeTarget 1 α = ![2 - α.1, 1, 1 + α.1] := by
  funext who
  fin_cases who <;>
    simp [paperEdgeTarget, halfHazard,
      GameTheory.FTVCyclicMinimality.soloReward,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise,
      GameTheory.FTVCyclicMinimality.nextThree] <;> ring

@[simp] theorem paperEdgeTarget_two (α : Hazard) :
    paperEdgeTarget 2 α = ![1 + α.1, 2 - α.1, 1] := by
  funext who
  fin_cases who <;>
    simp [paperEdgeTarget, halfHazard,
      GameTheory.FTVCyclicMinimality.soloReward,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise,
      GameTheory.FTVCyclicMinimality.nextThree] <;> ring

/-- Every displayed edge target is feasible. -/
theorem paperEdgeTarget_mem_feasible
    (owner : Player) (α : Hazard) :
    paperEdgeTarget owner α ∈ PaperFeasibleEquilibriumRewards := by
  exact ⟨paperEdgeProfile owner α,
    paperEdgeProfile_isEquilibrium owner α,
    quittingTerminalPayoff_paperEdgeProfile owner α⟩

/-- The paper's construction proves the full sufficiency half of Theorem 3.5. -/
theorem paperRewardRegion_subset_feasible :
    PaperRewardRegion ⊆ PaperFeasibleEquilibriumRewards := by
  intro payoff hpayoff
  rcases hpayoff with ⟨h0, h1, h2, hsum, hface⟩
  rcases hface with hu | hv | hw
  · let α : Hazard := ⟨payoff 1 - 1, by
      constructor <;> linarith⟩
    have htarget : paperEdgeTarget 0 α = payoff := by
      rw [paperEdgeTarget_zero]
      funext who
      fin_cases who <;> simp [α] <;> linarith
    simpa only [htarget] using paperEdgeTarget_mem_feasible 0 α
  · let α : Hazard := ⟨payoff 2 - 1, by
      constructor <;> linarith⟩
    have htarget : paperEdgeTarget 1 α = payoff := by
      rw [paperEdgeTarget_one]
      funext who
      fin_cases who <;> simp [α] <;> linarith
    simpa only [htarget] using paperEdgeTarget_mem_feasible 1 α
  · let α : Hazard := ⟨payoff 0 - 1, by
      constructor <;> linarith⟩
    have htarget : paperEdgeTarget 2 α = payoff := by
      rw [paperEdgeTarget_two]
      funext who
      fin_cases who <;> simp [α] <;> linarith
    simpa only [htarget] using paperEdgeTarget_mem_feasible 2 α

/-! The necessity half uses Theorem 3.4: once the first active run is fixed,
one coordinate equals `1`, the other two are at least `1`, and the row-sum
identity gives total reward `4`.  The imported exposed-face lemmas prove the
row-sum part for finite exact packets, but the arbitrary-equilibrium cyclic
support theorem remains open above.  Consequently this implication has exactly
the same missing six-step tail argument, and no additional hidden gap. -/
theorem paper_theorem3_5_necessity :
    PaperFeasibleEquilibriumRewards ⊆ PaperRewardRegion := by
  sorry

/-- **Theorem 3.5.** The feasible equilibrium rewards are exactly the three
closed edges printed in the paper. -/
theorem paper_theorem3_5 :
    PaperFeasibleEquilibriumRewards = PaperRewardRegion := by
  apply Set.Subset.antisymm
  · exact paper_theorem3_5_necessity
  · exact paperRewardRegion_subset_feasible

/-! ## Final remark

After Theorem 3.5 the paper states, without giving the analysis, that the same
method yields `ε`-equilibria in every `2×2×2` recursive repeated game with one
nonabsorbing row.  Relabeling each player's live action as Continue identifies
that class with arbitrary three-player quitting reward tables.  The repository
has no theorem establishing this full three-player existence statement, and
the paper supplies no proof to formalize. -/
def PaperFinalExistenceRemark : Prop :=
  ∀ reward : {S : Finset Player // S.Nonempty} → Payoff Player,
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile

theorem paper_finalExistenceRemark : PaperFinalExistenceRemark := by
  sorry

end Literature.FleschThuijsmanAndVrieze1997
