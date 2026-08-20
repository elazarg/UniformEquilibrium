import Mathlib

/-!
# Robert Samuel Simon, *The structure of non-zero-sum stochastic games* (2007)

R. S. Simon, *The structure of non-zero-sum stochastic games*, Advances in
Applied Mathematics **38**(1), 1--26 (2007), DOI
`10.1016/j.aam.2006.07.002`.

This statement-level formalization follows the definitions and named claims in
paper order.  The primary article supplied in
`ephemeral/literature/incoming/ScienceDirect_articles_05Aug2026_00-15-50.605.zip`
is the reference text followed here.  Unproved paper claims end in `sorry`.

The paper's probability laws and conditional laws are represented by explicit
bundles whose fields say that cylinder probabilities follow the game's actual
transition PMFs.  Thus none of the expected values below is an unconstrained
oracle.  The Cech-homology interface in Section 5 is likewise paper-local.

Simon's Theorem 3 supplies the substantive cyclic-orbit implication used for
the exceptional branch S.3 of Ashkenazi-Golan--Krasikov--Rainer--Solan.  Under
failure of their stationary and instant branches, exhaustive case analysis
fixes that structural alternative; their cited Solan--Vieille result supplies
the evaluation bridge.  Theorem 3 does not literally print their three-way
classification.
-/

namespace Literature.Simon2007

open MeasureTheory Set Filter CategoryTheory
open scoped BigOperators ENNReal Topology

noncomputable section

/-! ## 2. The model -/

/-- A payoff vector has one real coordinate for each player. -/
abbrev Payoff (N : Type) := N → ℝ

/-- `Δ(A)` is the type of countably additive probability mass functions on `A`. -/
abbrev Delta (A : Type) := PMF A

/-- The state, player, action, transition, and initial-state data of a stochastic game. -/
structure StochasticGameForm where
  State : Type
  Player : Type
  [countableState : Countable State]
  [finitePlayer : Fintype Player]
  [nonemptyPlayer : Nonempty Player]
  Action : Player → State → Type
  [finiteAction : ∀ n s, Fintype (Action n s)]
  [nonemptyAction : ∀ n s, Nonempty (Action n s)]
  transition : (s : State) → ((n : Player) → Action n s) → PMF State
  initial : State

attribute [instance] StochasticGameForm.countableState
attribute [instance] StochasticGameForm.finitePlayer
attribute [instance] StochasticGameForm.nonemptyPlayer
attribute [instance] StochasticGameForm.finiteAction
attribute [instance] StochasticGameForm.nonemptyAction

/-- The same game form restarted from a specified state. -/
def StochasticGameForm.restartAt (F : StochasticGameForm) (s : F.State) :
    StochasticGameForm where
  State := F.State
  Player := F.Player
  Action := F.Action
  transition := F.transition
  initial := s

/-- A possible finite history starts at the initial state and uses only positive transitions. -/
inductive HistoryTo (F : StochasticGameForm) : F.State → Type
  | root : HistoryTo F F.initial
  | snoc {s : F.State} (h : HistoryTo F s)
      (a : (n : F.Player) → F.Action n s) (t : F.State)
      (positive : 0 < F.transition s a t) : HistoryTo F t

/-- `H_ω` is the set of possible finite histories. -/
abbrev FiniteHistory (F : StochasticGameForm) := (s : F.State) × HistoryTo F s

/-- The terminal state of a finite history. -/
def FiniteHistory.terminal {F : StochasticGameForm} (h : FiniteHistory F) : F.State := h.1

/-- The number of action stages in a finite history. -/
def HistoryTo.length {F : StochasticGameForm} {s : F.State} : HistoryTo F s → ℕ
  | .root => 0
  | .snoc h _ _ _ => h.length + 1

/-- Transporting the terminal-state index does not change history length. -/
theorem HistoryTo.length_transport {F : StochasticGameForm} {s t : F.State}
    (e : s = t) (h : HistoryTo F s) : (e ▸ h).length = h.length := by
  cases e
  rfl

/-- The number of action stages in a finite history. -/
def FiniteHistory.length {F : StochasticGameForm} (h : FiniteHistory F) : ℕ := h.2.length

/-- Append an action profile and a positive-probability successor to a finite history. -/
def FiniteHistory.snoc {F : StochasticGameForm} (h : FiniteHistory F)
    (a : (n : F.Player) → F.Action n h.terminal) (t : F.State)
    (positive : 0 < F.transition h.terminal a t) : FiniteHistory F :=
  ⟨t, .snoc h.2 a t positive⟩

/-- `H_∞` consists of full state/action histories starting at `ŝ` along positive transitions. -/
structure InfiniteHistory (F : StochasticGameForm) where
  state : ℕ → F.State
  action : (i : ℕ) → (n : F.Player) → F.Action n (state i)
  starts : state 0 = F.initial
  positive : ∀ i, 0 < F.transition (state i) (action i) (state (i + 1))

/-- The `i`-stage truncation of a possible infinite history. -/
def InfiniteHistory.prefixTo {F : StochasticGameForm} (h : InfiniteHistory F) :
    (i : ℕ) → HistoryTo F (h.state i)
  | 0 => h.starts.symm ▸ .root
  | i + 1 => .snoc (h.prefixTo i) (h.action i) (h.state (i + 1)) (h.positive i)

/-- The canonical projection from an infinite history to `H_i`. -/
def InfiniteHistory.prefix {F : StochasticGameForm} (h : InfiniteHistory F)
    (i : ℕ) : FiniteHistory F := ⟨h.state i, h.prefixTo i⟩

/-- The clopen cylinder `O_h` of infinite extensions of a finite history `h`. -/
def Cylinder {F : StochasticGameForm} (h : FiniteHistory F) : Set (InfiniteHistory F) :=
  {ω | ω.prefix h.length = h}

/-- The cylinder topology used on `H_∞`. -/
instance historyTopologicalSpace (F : StochasticGameForm) :
    TopologicalSpace (InfiniteHistory F) :=
  TopologicalSpace.generateFrom {U | ∃ h : FiniteHistory F, U = Cylinder h}

/-- The sigma algebra on `H_∞` generated by finite-history cylinders. -/
instance historyMeasurableSpace (F : StochasticGameForm) :
    MeasurableSpace (InfiniteHistory F) :=
  MeasurableSpace.generateFrom {U | ∃ h : FiniteHistory F, U = Cylinder h}

/-- A Borel probability on the history space is a probability measure on its Borel sigma algebra. -/
def IsHistoryBorelProbability (F : StochasticGameForm)
    (μ : Measure (InfiniteHistory F)) : Prop :=
  BorelSpace (InfiniteHistory F) ∧ IsProbabilityMeasure μ

/-- Simon's regularity condition for a Borel probability on infinite histories. -/
def IsRegularHistoryProbability (F : StochasticGameForm)
    (μ : Measure (InfiniteHistory F)) : Prop :=
  IsHistoryBorelProbability F μ ∧ ∀ A, MeasurableSet A → ∀ ε : ℝ, 0 < ε →
    ∃ C O, IsClosed C ∧ IsOpen O ∧ C ⊆ A ∧ A ⊆ O ∧
      μ (O \ C) ≤ ENNReal.ofReal ε

/-- A normal stochastic game has bounded Borel payoffs on full state/action histories. -/
structure NormalStochasticGame extends StochasticGameForm where
  payoff : Player → InfiniteHistory toStochasticGameForm → ℝ
  payoffMeasurable : ∀ n, Measurable (payoff n)
  payoffBound : ℝ
  payoffBound_nonneg : 0 ≤ payoffBound
  payoff_bounded : ∀ n h, |payoff n h| ≤ payoffBound
  payoffDifferenceBound : ℝ
  payoffDifferenceBound_one : 1 ≤ payoffDifferenceBound
  payoff_difference : ∀ n h h', |payoff n h - payoff n h'| < payoffDifferenceBound

/-- The average of a bounded stage-reward presentation through the first `i` stages. -/
def StageRewardAverage (G : NormalStochasticGame)
    (w : (s : G.State) → ((n : G.Player) → G.Action n s) → Payoff G.Player)
    (h : InfiniteHistory G.toStochasticGameForm) (n : G.Player) (i : ℕ) : ℝ :=
  if i = 0 then 0 else (i : ℝ)⁻¹ * ∑ k ∈ Finset.range i, w (h.state k) (h.action k) n

/--
A normal stochastic game is limit-average when each payoff lies between the liminf and
limsup of the averages of one bounded state/action stage-reward function.
-/
def IsLimitAverage (G : NormalStochasticGame) : Prop :=
  ∃ w : (s : G.State) → ((n : G.Player) → G.Action n s) → Payoff G.Player,
    (∃ B : ℝ, ∀ s a n, |w s a n| ≤ B) ∧ ∀ n h,
      liminf (fun i => StageRewardAverage G w h n i) atTop ≤ G.payoff n h ∧
      G.payoff n h ≤ limsup (fun i => StageRewardAverage G w h n i) atTop

/-- A strategy assigns a probability distribution on the current finite action set. -/
structure Strategy (G : NormalStochasticGame) (n : G.Player) where
  play : (h : FiniteHistory G.toStochasticGameForm) → PMF (G.Action n h.terminal)

/-- A strategy profile consists of one behavioral strategy for each player. -/
abbrev Profile (G : NormalStochasticGame) := (n : G.Player) → Strategy G n

/-- A strategy is stationary when it depends only on the present state. -/
def Strategy.IsStationary {G : NormalStochasticGame} {n : G.Player}
    (strategy : Strategy G n) : Prop :=
  ∃ stationary : (s : G.State) → PMF (G.Action n s),
    ∀ h, strategy.play h = stationary h.terminal

/-- A profile is stationary when each player's strategy is stationary. -/
def Profile.IsStationary {G : NormalStochasticGame} (profile : Profile G) : Prop :=
  ∀ n, (profile n).IsStationary

/-- The profile obtained by replacing player `n`'s strategy by `τ`. -/
def Profile.replace (G : NormalStochasticGame) (profile : Profile G)
    (n : G.Player) (τ : Strategy G n) : Profile G := by
  classical
  exact fun k => if h : k = n then h ▸ τ else profile k

/-- A behavioral strategy in the game restarted from `s`. -/
structure RestartStrategy (G : NormalStochasticGame) (s : G.State) (n : G.Player) where
  play : (h : FiniteHistory (G.toStochasticGameForm.restartAt s)) →
    PMF (G.Action n h.terminal)

/-- A behavioral profile in the game restarted from `s`. -/
abbrev RestartProfile (G : NormalStochasticGame) (s : G.State) :=
  (n : G.Player) → RestartStrategy G s n

/-- Replace player `n`'s strategy in a restarted profile. -/
def RestartProfile.replace (G : NormalStochasticGame) {s : G.State}
    (profile : RestartProfile G s) (n : G.Player) (tau : RestartStrategy G s n) :
    RestartProfile G s := by
  classical
  exact fun k => if h : k = n then h ▸ tau else profile k

/-- The initial finite history `(ŝ)`. -/
def InitialHistory (G : NormalStochasticGame) : FiniteHistory G.toStochasticGameForm :=
  ⟨G.initial, .root⟩

/-- The root history of the game restarted from `s`. -/
def RestartInitialHistory (G : NormalStochasticGame) (s : G.State) :
    FiniteHistory (G.toStochasticGameForm.restartAt s) :=
  ⟨s, .root⟩

/-- A history restarted at the original initial state, viewed as an original history. -/
def RestartHistoryAtInitial.toOriginal (G : NormalStochasticGame)
    (omega : InfiniteHistory (G.toStochasticGameForm.restartAt G.initial)) :
    InfiniteHistory G.toStochasticGameForm where
  state := omega.state
  action := omega.action
  starts := omega.starts
  positive := omega.positive

/-- A profile's probability of a one-step extension from `h`. -/
def OneStepProbability (G : NormalStochasticGame) (profile : Profile G)
    (h : FiniteHistory G.toStochasticGameForm)
    (a : (n : G.Player) → G.Action n h.terminal) (t : G.State) : ℝ≥0∞ := by
  classical
  exact G.transition h.terminal a t * ∏ n, (profile n).play h (a n)

/-- A restarted profile's probability of a one-step extension. -/
def RestartOneStepProbability (G : NormalStochasticGame) {s : G.State}
    (profile : RestartProfile G s)
    (h : FiniteHistory (G.toStochasticGameForm.restartAt s))
    (a : (n : G.Player) → G.Action n h.terminal) (t : G.State) : ℝ≥0∞ := by
  classical
  exact G.transition h.terminal a t * ∏ n, (profile n).play h (a n)

/--
The induced-law data from Kolmogorov extension: every start law is a probability,
is supported on the chosen cylinder, has the stated one-step cylinder masses,
and conditions recursively to the law from the extended history.
-/
structure InducedLawSemantics (G : NormalStochasticGame) where
  lawFrom : Profile G → FiniteHistory G.toStochasticGameForm →
    Measure (InfiniteHistory G.toStochasticGameForm)
  probability : ∀ profile h, IsProbabilityMeasure (lawFrom profile h)
  borelCompatible :
    historyMeasurableSpace G.toStochasticGameForm =
      @borel (InfiniteHistory G.toStochasticGameForm)
        (historyTopologicalSpace G.toStochasticGameForm)
  regular : ∀ profile h A, MeasurableSet A → ∀ ε : ℝ, 0 < ε →
    ∃ C O, IsClosed C ∧ IsOpen O ∧ C ⊆ A ∧ A ⊆ O ∧
      lawFrom profile h (O \ C) ≤ ENNReal.ofReal ε
  supported : ∀ profile h, lawFrom profile h (Cylinder h) = 1
  oneStep : ∀ profile h a t positive,
    lawFrom profile h (Cylinder (h.snoc a t positive)) =
      OneStepProbability G profile h a t
  condition : ∀ profile h a t positive,
    (lawFrom profile h).restrict (Cylinder (h.snoc a t positive)) =
      OneStepProbability G profile h a t • lawFrom profile (h.snoc a t positive)

/-- Kolmogorov extension and regularity provide the induced laws used by the paper. -/
theorem inducedLawSemantics_exists (G : NormalStochasticGame) :
    Nonempty (InducedLawSemantics G) := by
  sorry

/--
The payoff extension and actual induced laws for every state-restarted game.  Simon's
state value `chi^n(s)` uses these restarted games; such an extension is extra data because
the printed `V^n` was initially typed only on histories starting at the designated state.
-/
structure RestartSemantics (G : NormalStochasticGame) where
  payoff : (s : G.State) → G.Player →
    InfiniteHistory (G.toStochasticGameForm.restartAt s) → ℝ
  payoffMeasurable : ∀ s n, Measurable (payoff s n)
  payoffBounded : ∀ s n omega, |payoff s n omega| ≤ G.payoffBound
  payoffDifference : ∀ (s t) n
    (omega : InfiniteHistory (G.toStochasticGameForm.restartAt s))
    (omega' : InfiniteHistory (G.toStochasticGameForm.restartAt t)),
      |payoff s n omega - payoff t n omega'| < G.payoffDifferenceBound
  payoffAtInitial : ∀ n omega,
    payoff G.initial n omega = G.payoff n (RestartHistoryAtInitial.toOriginal G omega)
  lawFrom : (s : G.State) → RestartProfile G s →
    FiniteHistory (G.toStochasticGameForm.restartAt s) →
      Measure (InfiniteHistory (G.toStochasticGameForm.restartAt s))
  probability : ∀ s profile h, IsProbabilityMeasure (lawFrom s profile h)
  supported : ∀ s profile h, lawFrom s profile h (Cylinder h) = 1
  oneStep : ∀ s profile h a t positive,
    lawFrom s profile h (Cylinder (h.snoc a t positive)) =
      RestartOneStepProbability G profile h a t
  condition : ∀ s profile h a t positive,
    (lawFrom s profile h).restrict (Cylinder (h.snoc a t positive)) =
      RestartOneStepProbability G profile h a t •
        lawFrom s profile (h.snoc a t positive)

/-- Expected payoff in the explicitly supplied game restarted at state `s`. -/
def RestartExpectedPayoffWith (G : NormalStochasticGame) (R : RestartSemantics G)
    (s : G.State) (profile : RestartProfile G s) (n : G.Player) : ℝ :=
  integral (R.lawFrom s profile (RestartInitialHistory G s))
    (fun omega => R.payoff s n omega)

/-- The printed restart value `chi^n(s) = inf_sigma sup_tau V_s^n(sigma|tau^n)`. -/
def RestartMinMaxValue (G : NormalStochasticGame) (R : RestartSemantics G)
    (n : G.Player) (s : G.State) : ℝ :=
  sInf (range fun profile : RestartProfile G s =>
    sSup (range fun tau : RestartStrategy G s n =>
      RestartExpectedPayoffWith G R s (profile.replace G n tau) n))

/--
The paper's complete semantics consists of derivable initial-history laws plus an explicitly
supplied payoff extension and laws for each state-restarted game.  The last two fields record
the compatibility the paper uses between the restart value at a state and continuation play
after every original history ending at that state; this compatibility is not derivable from a
bare history-dependent payoff function.
-/
structure StochasticSemantics (G : NormalStochasticGame) extends InducedLawSemantics G where
  restart : RestartSemantics G
  continuationPunishment : ∀ ε : ℝ, 0 < ε → ∀ n h,
    ∃ profile : Profile G, ∀ tau : Strategy G n,
      (∫ omega, G.payoff n omega ∂lawFrom (profile.replace G n tau) h) ≤
        RestartMinMaxValue G restart n h.terminal + ε
  continuationSecurity : ∀ ε : ℝ, 0 < ε → ∀ n h (profile : Profile G),
    ∃ tau : Strategy G n,
      RestartMinMaxValue G restart n h.terminal - ε ≤
        ∫ omega, G.payoff n omega ∂lawFrom (profile.replace G n tau) h

/-- A filtration is an increasing family of sub-sigma-algebras. -/
abbrev HistoryFiltration (G : NormalStochasticGame) :=
  MeasureTheory.Filtration ℕ (historyMeasurableSpace G.toStochasticGameForm)

/-- The Borel probability `μ_σ` induced from the initial history. -/
def InducedMeasure (G : NormalStochasticGame) (S : StochasticSemantics G)
    (profile : Profile G) : Measure (InfiniteHistory G.toStochasticGameForm) :=
  S.lawFrom profile (InitialHistory G)

/-- The expected payoff from a specified finite history. -/
def ExpectedPayoffFrom (G : NormalStochasticGame) (S : StochasticSemantics G)
    (h : FiniteHistory G.toStochasticGameForm) (profile : Profile G)
    (n : G.Player) : ℝ :=
  ∫ ω, G.payoff n ω ∂S.lawFrom profile h

/-- The paper's expected payoff `Vⁿ(σ)` from the initial state. -/
def ExpectedPayoff (G : NormalStochasticGame) (S : StochasticSemantics G)
    (profile : Profile G) (n : G.Player) : ℝ :=
  ExpectedPayoffFrom G S (InitialHistory G) profile n

/-- A profile is an `ε`-equilibrium when no unilateral behavioral deviation gains over `ε`. -/
def IsEpsilonEquilibrium (G : NormalStochasticGame) (S : StochasticSemantics G)
    (ε : ℝ) (profile : Profile G) : Prop :=
  ∀ n (τ : Strategy G n),
    ExpectedPayoff G S (profile.replace G n τ) n ≤ ExpectedPayoff G S profile n + ε

/-- Approximate equilibria exist if an `ε`-equilibrium exists for every positive `ε`. -/
def HasApproximateEquilibria (G : NormalStochasticGame)
    (S : StochasticSemantics G) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ profile, IsEpsilonEquilibrium G S ε profile

/-- A zero-sum game has value `r` for `n` in the approximate-equilibrium sense. -/
def HasValue (G : NormalStochasticGame) (S : StochasticSemantics G)
    (n : G.Player) (r : ℝ) : Prop :=
  Fintype.card G.Player = 2 ∧ (∀ h, ∑ k, G.payoff k h = 0) ∧
    ∀ ε : ℝ, 0 < ε →
    ∃ profile, IsEpsilonEquilibrium G S ε profile ∧
      |ExpectedPayoff G S profile n - r| ≤ ε

/-- A two-player game is zero-sum when its two payoff coordinates always sum to zero. -/
def IsZeroSum (G : NormalStochasticGame) : Prop :=
  Fintype.card G.Player = 2 ∧ ∀ h, ∑ n, G.payoff n h = 0

/-- The number `|N|` of players. -/
def PlayerCount (G : NormalStochasticGame) : ℕ := Fintype.card G.Player

/-! ### 2.3. Perfection -/

/-- The continuation payoff `v_σⁿ(h)`, defined using the induced law from `h`. -/
def ContinuationValue (G : NormalStochasticGame) (S : StochasticSemantics G)
    (profile : Profile G) (n : G.Player)
    (h : FiniteHistory G.toStochasticGameForm) : ℝ :=
  ExpectedPayoffFrom G S h profile n

/-- Expected payoff in the game restarted at state `s`. -/
def RestartExpectedPayoff (G : NormalStochasticGame) (S : StochasticSemantics G)
    (s : G.State) (profile : RestartProfile G s) (n : G.Player) : ℝ :=
  RestartExpectedPayoffWith G S.restart s profile n

/--
The state min-max value `χⁿ(s) = inf_σ sup_τ V_sⁿ(σ|τⁿ)`, derived from the
explicit state-restarted payoff and path-law semantics.
-/
def MinMaxValue (G : NormalStochasticGame) (S : StochasticSemantics G)
    (n : G.Player) (s : G.State) : ℝ :=
  RestartMinMaxValue G S.restart n s

/-- `w_σᶠ(h)(aⁿ)`: expected next-history value after forcing player `n`'s action. -/
def OneStageValue (G : NormalStochasticGame) (profile : Profile G)
    (n : G.Player) (h : FiniteHistory G.toStochasticGameForm)
    (f : FiniteHistory G.toStochasticGameForm → ℝ)
    (own : G.Action n h.terminal) : ℝ := by
  classical
  let rows := (k : G.Player) → G.Action k h.terminal
  exact ∑ a : rows, if a n = own then
    (∏ k ∈ Finset.univ.erase n, ((profile k).play h (a k)).toReal) *
      ∑' t : G.State, (G.transition h.terminal a t).toReal *
        if positive : 0 < G.transition h.terminal a t then
          f (h.snoc a t positive)
        else 0
    else 0

/-- The jump value `j_σⁿ(h)`, maximizing expected next-state min-max value. -/
def JumpValue (G : NormalStochasticGame) (S : StochasticSemantics G)
    (profile : Profile G) (n : G.Player)
    (h : FiniteHistory G.toStochasticGameForm) : ℝ :=
  sSup (range fun own : G.Action n h.terminal =>
    OneStageValue G profile n h (fun h' => MinMaxValue G S n h'.terminal) own)

/-- An action lies in the positive support of `σⁿ(h)`. -/
def PositiveSupport (G : NormalStochasticGame) (profile : Profile G)
    (n : G.Player) (h : FiniteHistory G.toStochasticGameForm)
    (a : G.Action n h.terminal) : Prop :=
  0 < (profile n).play h a

/-- The event that some finite truncation lies outside the good set `B ⊆ H_ω`. -/
def ReachesOutside (G : NormalStochasticGame)
    (B : Set (FiniteHistory G.toStochasticGameForm)) :
    Set (InfiniteHistory G.toStochasticGameForm) :=
  {ω | ∃ i, ω.prefix i ∉ B}

/--
The paper's `ε`-perfection conditions for a particular witness `rⁿ` and good set `B`.
All inequalities are imposed on `B`, while reaching `H_ω \ B` has probability at most `ε`.
-/
def EpsilonPerfectWithWitness (G : NormalStochasticGame)
    (S : StochasticSemantics G) (ε : ℝ) (profile : Profile G)
    (r : G.Player → FiniteHistory G.toStochasticGameForm → ℝ)
    (B : Set (FiniteHistory G.toStochasticGameForm)) : Prop :=
  InducedMeasure G S profile (ReachesOutside G B) ≤ ENNReal.ofReal ε ∧
    ∀ n h, h ∈ B →
      r n h ≥ JumpValue G S profile n h - ε ∧
      r n h - ContinuationValue G S profile n h ≤ ε ∧
      ∀ a, PositiveSupport G profile n h a →
        OneStageValue G profile n h (r n) a - r n h ≤ ε

/-- A strategy profile is `ε`-perfect if suitable witnesses `rⁿ` and `B` exist. -/
def EpsilonPerfect (G : NormalStochasticGame) (S : StochasticSemantics G)
    (ε : ℝ) (profile : Profile G) : Prop :=
  ∃ r B, EpsilonPerfectWithWitness G S ε profile r B

/-- `ε`-self-perfection uses the same perfection witness `rⁿ = v_σⁿ`. -/
def EpsilonSelfPerfect (G : NormalStochasticGame) (S : StochasticSemantics G)
    (ε : ℝ) (profile : Profile G) : Prop :=
  ∃ B, EpsilonPerfectWithWitness G S ε profile
    (fun n h => ContinuationValue G S profile n h) B

/-- Increasing the error tolerance preserves self-perfection. -/
theorem EpsilonSelfPerfect.mono (G : NormalStochasticGame) (S : StochasticSemantics G)
    {ε δ : ℝ} (hεδ : ε ≤ δ) {profile : Profile G}
    (h : EpsilonSelfPerfect G S ε profile) : EpsilonSelfPerfect G S δ profile := by
  rcases h with ⟨B, hmeasure, hlocal⟩
  refine ⟨B, le_trans hmeasure (ENNReal.ofReal_le_ofReal hεδ), ?_⟩
  intro n history hhistory
  rcases hlocal n history hhistory with ⟨hjump, hcontinuation, haction⟩
  refine ⟨by linarith, by linarith, ?_⟩
  intro action hpositive
  exact le_trans (haction action hpositive) hεδ

/-- A stochastic game is perfect if it has an `ε`-perfect profile for every positive `ε`. -/
def IsPerfect (G : NormalStochasticGame) (S : StochasticSemantics G) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ profile, EpsilonPerfect G S ε profile

/-- A stochastic game is self-perfect if it has an `ε`-self-perfect profile for every `ε > 0`. -/
def IsSelfPerfect (G : NormalStochasticGame) (S : StochasticSemantics G) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ profile, EpsilonSelfPerfect G S ε profile

/-- Simon [16]: approximate equilibria in a normal stochastic game imply perfection. -/
theorem approximate_equilibria_imply_perfect (G : NormalStochasticGame)
    (S : StochasticSemantics G) : HasApproximateEquilibria G S → IsPerfect G S := by
  sorry

/-! ## 3. From perfection to approximate equilibria -/

/--
A function `f : H_ω → ℝᴺ` is viable if, from every finite history, one profile can
hold every unilateral deviator to `f(h)ⁿ + ε` in conditional expected payoff.
-/
def Viable (G : NormalStochasticGame) (S : StochasticSemantics G)
    (f : FiniteHistory G.toStochasticGameForm → Payoff G.Player) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ h, ∃ profile : Profile G, ∀ n (τ : Strategy G n),
    ExpectedPayoffFrom G S h (profile.replace G n τ) n ≤ f h n + ε

/-- A finite history is reached with positive probability under a profile. -/
def ReachedWithPositiveProbability (G : NormalStochasticGame)
    (S : StochasticSemantics G) (profile : Profile G)
    (h : FiniteHistory G.toStochasticGameForm) : Prop :=
  0 < InducedMeasure G S profile (Cylinder h)

/--
A profile is `δ`-viable if its continuation value dominates a viable function up to `δ`
at every finite history that it reaches with positive probability.
-/
def EpsilonViable (G : NormalStochasticGame) (S : StochasticSemantics G)
    (δ : ℝ) (profile : Profile G) : Prop :=
  ∃ f, Viable G S f ∧ ∀ n h, ReachedWithPositiveProbability G S profile h →
    ContinuationValue G S profile n h ≥ f h n - δ

/-- Increasing the error tolerance preserves viability of a profile. -/
theorem EpsilonViable.mono (G : NormalStochasticGame) (S : StochasticSemantics G)
    {ε δ : ℝ} (hεδ : ε ≤ δ) {profile : Profile G}
    (h : EpsilonViable G S ε profile) : EpsilonViable G S δ profile := by
  rcases h with ⟨f, hf, hbound⟩
  refine ⟨f, hf, ?_⟩
  intro n history hreached
  exact le_trans (by linarith : f history n - δ ≤ f history n - ε)
    (hbound n history hreached)

/-- `W_σⁿ(h)` is player `n`'s cumulative one-stage action advantage along `h`. -/
def HistoryTo.cumulativeAdvantage (G : NormalStochasticGame)
    (S : StochasticSemantics G) (profile : Profile G) (n : G.Player) :
    {s : G.State} → HistoryTo G.toStochasticGameForm s → ℝ
  | _, .root => 0
  | _, @HistoryTo.snoc _ s h a t _positive =>
      h.cumulativeAdvantage G S profile n +
        OneStageValue G profile n ⟨s, h⟩
          (fun h' => ContinuationValue G S profile n h') (a n) -
        ContinuationValue G S profile n ⟨s, h⟩

/-- A zero-stage history has no accumulated action advantage. -/
theorem HistoryTo.cumulativeAdvantage_eq_zero_of_length_eq_zero
    (G : NormalStochasticGame) (S : StochasticSemantics G) (profile : Profile G)
    (n : G.Player) {s : G.State} (h : HistoryTo G.toStochasticGameForm s)
    (hlength : h.length = 0) : h.cumulativeAdvantage G S profile n = 0 := by
  cases h with
  | root => rfl
  | snoc h a t positive => simp [HistoryTo.length] at hlength

/-- The paper's cumulative advantage `W_σⁿ(h)` on a finite history. -/
def CumulativeAdvantage (G : NormalStochasticGame) (S : StochasticSemantics G)
    (profile : Profile G) (n : G.Player)
    (h : FiniteHistory G.toStochasticGameForm) : ℝ :=
  h.2.cumulativeAdvantage G S profile n

/-- The event that a reached finite history has `W_σⁿ(h) > ε`. -/
def AdvantageCrossingEvent (G : NormalStochasticGame) (S : StochasticSemantics G)
    (profile : Profile G) (n : G.Player) (ε : ℝ) :
    Set (InfiniteHistory G.toStochasticGameForm) :=
  {ω | ∃ i, CumulativeAdvantage G S profile n (ω.prefix i) > ε}

/--
Theorem 1.  If `0 < ε ≤ 1`, `σ` is `ε`-self-perfect and `ε`-viable, and
each player's `W`-crossing event has probability at most `ε`, then the game has a
`3 (M |N| + 2) ε`-equilibrium.
-/
theorem theorem1 (G : NormalStochasticGame) (S : StochasticSemantics G)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (profile : Profile G)
    (hperfect : EpsilonSelfPerfect G S ε profile)
    (hviable : EpsilonViable G S ε profile)
    (hcross : ∀ n, InducedMeasure G S profile
      (AdvantageCrossingEvent G S profile n ε) ≤ ENNReal.ofReal ε) :
    ∃ equilibrium, IsEpsilonEquilibrium G S
      (3 * (G.payoffDifferenceBound * PlayerCount G + 2) * ε) equilibrium := by
  sorry

/-- Question 1.  Does Theorem 1 remain true if only the viability hypothesis is dropped? -/
def Question1 : Prop :=
  ∀ (G : NormalStochasticGame) (S : StochasticSemantics G) (ε : ℝ),
    0 < ε → ε ≤ 1 → ∀ profile : Profile G,
      EpsilonSelfPerfect G S ε profile →
      (∀ n, InducedMeasure G S profile
        (AdvantageCrossingEvent G S profile n ε) ≤ ENNReal.ofReal ε) →
      ∃ equilibrium, IsEpsilonEquilibrium G S
        (3 * (G.payoffDifferenceBound * PlayerCount G + 2) * ε) equilibrium

/-!
The unnumbered three-player fair-coin example on p. 7 explains why statistical punishment
is triggered by a small open event: playing `L` through every finite stage is always possible
under the prescribed half--half behavior, while the strong law places the payoff-changing
infinite histories inside an arbitrarily small open cover.
-/

/-! ### 3.2. Discrete decision processes -/

/--
A discrete decision process alternates between countable `X`-states and countable `Y_x`
actions, follows actual probability transitions, and carries a uniformly bounded harmonic value.
-/
structure DiscreteDecisionProcess where
  X : Type
  [countableX : Countable X]
  Y : X → Type
  [countableY : ∀ x, Countable (Y x)]
  choose : (x : X) → PMF (Y x)
  move : (x : X) → Y x → PMF X
  initial : X
  valueX : X → ℝ
  valueY : (x : X) → Y x → ℝ
  harmonicX : ∀ x,
    valueX x = ∑' y, (choose x y).toReal * valueY x y
  harmonicY : ∀ x y,
    valueY x y = ∑' z, (move x y z).toReal * valueX z
  valueDifferenceBound : ℝ
  valueDifferenceBound_one : 1 ≤ valueDifferenceBound
  valueDifference : ∀ (x x' : X) (y : Y x) (y' : Y x'),
    |valueX x - valueX x'| ≤ valueDifferenceBound ∧
    |valueY x y - valueX x'| ≤ valueDifferenceBound ∧
    |valueY x y - valueY x' y'| ≤ valueDifferenceBound

attribute [instance] DiscreteDecisionProcess.countableX
attribute [instance] DiscreteDecisionProcess.countableY

/-- A possible infinite path `x₀,y₁,x₂,y₃,…` of a decision process. -/
structure DDPPath (P : DiscreteDecisionProcess) where
  x : ℕ → P.X
  y : (i : ℕ) → P.Y (x i)
  movePositive : ∀ i, 0 < P.move (x i) (y i) (x (i + 1))

/-- A possible finite decision-process path containing `k` chosen actions. -/
structure DDPFinitePath (P : DiscreteDecisionProcess) (k : ℕ) where
  x : Fin (k + 1) → P.X
  y : (i : Fin k) → P.Y (x i.castSucc)
  movePositive : ∀ i, 0 < P.move (x i.castSucc) (y i) (x i.succ)

/-- Finite possible paths form a countable type when states and actions are countable. -/
instance ddpFinitePathCountable (P : DiscreteDecisionProcess) (k : ℕ) :
    Countable (DDPFinitePath P k) :=
  (show Function.Injective
      (fun h : DDPFinitePath P k =>
        (h.x, fun i => Sigma.mk (h.x i.castSucc) (h.y i))) from by
      intro a b hab
      cases a with
      | mk ax ay ap =>
        cases b with
        | mk bx byy bp =>
          simp only [Prod.mk.injEq] at hab
          cases hab.1
          have : ay = byy := by
            funext i
            exact eq_of_heq (Sigma.mk.inj_iff.mp (congrFun hab.2 i) |>.2)
          cases this
          rfl).countable

/-- The `k`-action prefix of a possible infinite decision-process path. -/
def DDPPath.prefix (P : DiscreteDecisionProcess) (p : DDPPath P)
    (k : ℕ) : DDPFinitePath P k where
  x i := p.x i
  y i := p.y i
  movePositive i := p.movePositive i

/-- The advantage read from a finite path containing `l+1` chosen actions. -/
def DDPFinitePath.advantage (P : DiscreteDecisionProcess) {l : ℕ}
    (h : DDPFinitePath P (l + 1)) : ℝ :=
  ∑ i : Fin (l + 1),
    (P.valueY (h.x i.castSucc) (h.y i) - P.valueX (h.x i.castSucc))

/-- The cylinder determined by a finite decision-process path. -/
def DDPCylinder (P : DiscreteDecisionProcess) {k : ℕ}
    (h : DDPFinitePath P k) : Set (DDPPath P) :=
  {p | p.prefix P k = h}

/-- The product probability of a finite decision-process path. -/
def DDPFinitePath.probability (P : DiscreteDecisionProcess) {k : ℕ}
    (h : DDPFinitePath P k) : ℝ≥0∞ :=
  ∏ i, P.choose (h.x i.castSucc) (h.y i) *
    P.move (h.x i.castSucc) (h.y i) (h.x i.succ)

/-- The cylinder probability after the first action has been forced rather than sampled. -/
def DDPFinitePath.afterActionProbability (P : DiscreteDecisionProcess) {k : ℕ}
    (h : DDPFinitePath P (k + 1)) : ℝ≥0∞ :=
  P.move (h.x 0) (h.y 0) (h.x 1) * ∏ i : Fin k,
    let j : Fin (k + 1) := i.succ
    P.choose (h.x j.castSucc) (h.y j) * P.move (h.x j.castSucc) (h.y j) (h.x j.succ)

/-- The cylinder sigma algebra on infinite decision-process paths. -/
instance ddpPathMeasurableSpace (P : DiscreteDecisionProcess) :
    MeasurableSpace (DDPPath P) :=
  MeasurableSpace.generateFrom {U | ∃ k, ∃ h : DDPFinitePath P k, U = DDPCylinder P h}

/-- Every finite-path cylinder belongs to the generated path sigma algebra. -/
theorem measurableSet_ddpCylinder (P : DiscreteDecisionProcess) {k : ℕ}
    (h : DDPFinitePath P k) : MeasurableSet (DDPCylinder P h) :=
  MeasurableSpace.measurableSet_generateFrom ⟨k, h, rfl⟩

/--
The induced path law and the laws obtained after forcing a start/action, constrained by all
finite-cylinder products and by support at the prescribed first state and action.
-/
structure DDPSemantics (P : DiscreteDecisionProcess) where
  law : Measure (DDPPath P)
  probability : IsProbabilityMeasure law
  lawSupport : law {p | p.x 0 = P.initial} = 1
  cylinder : ∀ k (h : DDPFinitePath P k),
    h.x 0 = P.initial → law (DDPCylinder P h) = h.probability P
  fromState : P.X → Measure (DDPPath P)
  fromStateProbability : ∀ x, IsProbabilityMeasure (fromState x)
  fromStateSupport : ∀ x, fromState x {p | p.x 0 = x} = 1
  fromStateCylinder : ∀ x k (h : DDPFinitePath P k), h.x 0 = x →
    fromState x (DDPCylinder P h) = h.probability P
  lawFromInitial : law = fromState P.initial
  afterAction : (x : P.X) → P.Y x → Measure (DDPPath P)
  afterActionProbability : ∀ x y, IsProbabilityMeasure (afterAction x y)
  afterActionSupport : ∀ x y,
    afterAction x y {p | p.x 0 = x ∧ HEq (p.y 0) y} = 1
  afterActionMove : ∀ x y z,
    afterAction x y {p | p.x 1 = z} = P.move x y z
  afterActionCylinder : ∀ x y k (h : DDPFinitePath P (k + 1)),
    h.x 0 = x → HEq (h.y 0) y →
      afterAction x y (DDPCylinder P h) = h.afterActionProbability P

/-- Ionescu--Tulcea extension supplies the path, start, and forced-action laws of a DDP. -/
theorem ddpSemantics_exists (P : DiscreteDecisionProcess) : Nonempty (DDPSemantics P) := by
  sorry

/-- The finite cumulative advantage through the action indexed by `l`. -/
def DDPAdvantage (P : DiscreteDecisionProcess) (p : DDPPath P) (l : ℕ) : ℝ :=
  Finset.sum (Finset.range (l + 1)) fun i =>
    P.valueY (p.x i) (p.y i) - P.valueX (p.x i)

@[simp]
theorem DDPFinitePath.advantage_prefix (P : DiscreteDecisionProcess) (p : DDPPath P)
    (l : ℕ) : (p.prefix P (l + 1)).advantage P = DDPAdvantage P p l := by
  rw [DDPFinitePath.advantage, DDPAdvantage]
  change (∑ i : Fin (l + 1),
    (P.valueY (p.x i) (p.y i) - P.valueX (p.x i))) = _
  rw [
    Fin.sum_univ_eq_sum_range (fun i =>
      P.valueY (p.x i) (p.y i) - P.valueX (p.x i))]

/-- Crossing events are measurable in the finite-cylinder sigma algebra. -/
theorem measurableSet_ddpAdvantage_crossing (P : DiscreteDecisionProcess) (ε : ℝ) :
    MeasurableSet {p | ∃ l, DDPAdvantage P p l ≥ ε} := by
  let E : Set (DDPPath P) := ⋃ l, ⋃ h : DDPFinitePath P (l + 1),
    if h.advantage P ≥ ε then DDPCylinder P h else ∅
  have hE : {p | ∃ l, DDPAdvantage P p l ≥ ε} = E := by
    ext p
    simp only [E, mem_setOf_eq, mem_iUnion, mem_ite_empty_right]
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨l, p.prefix P (l + 1), ?_, rfl⟩
      simpa using hl
    · rintro ⟨l, h, hh, hp⟩
      refine ⟨l, ?_⟩
      change p.prefix P (l + 1) = h at hp
      rw [← hp] at hh
      simpa using hh
  rw [hE]
  exact MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun h => by
    split_ifs
    · exact measurableSet_ddpCylinder P h
    · exact MeasurableSet.empty

/-- The probability that a cumulative advantage ever reaches `ε`. -/
def PositiveCrossingProbability (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (ε : ℝ) : ℝ≥0∞ :=
  S.law {p | ∃ l, DDPAdvantage P p l ≥ ε}

/--
A process generated by a game/profile/player is linked by a measurable path map whose law
is the DDP law and whose finite cumulative advantages equal the player's `W` process.
-/
structure GeneratedDecisionProcess (G : NormalStochasticGame)
    (GS : StochasticSemantics G) (profile : Profile G) (n : G.Player)
    (P : DiscreteDecisionProcess) (PS : DDPSemantics P) where
  pathMap : InfiniteHistory G.toStochasticGameForm → DDPPath P
  measurable_pathMap : Measurable pathMap
  pathMap_starts : ∀ ω, (pathMap ω).x 0 = P.initial
  law_eq : Measure.map pathMap (InducedMeasure G GS profile) = PS.law
  valueDifferenceBound_le : P.valueDifferenceBound ≤ G.payoffDifferenceBound
  valueX_eq : ∀ ω i,
    P.valueX (pathMap ω |>.x i) = ContinuationValue G GS profile n (ω.prefix i)
  valueY_eq : ∀ ω i,
    P.valueY (pathMap ω |>.x i) (pathMap ω |>.y i) =
      OneStageValue G profile n (ω.prefix i)
        (fun h => ContinuationValue G GS profile n h) (ω.action i n)
  advantage_eq : ∀ ω l,
    DDPAdvantage P (pathMap ω) l =
      CumulativeAdvantage G GS profile n (ω.prefix (l + 1))

/-!
The unnumbered observation on p. 10 embeds a Markov chain as a DDP by taking `Y_x` to be
the positive-probability successors of `x` and making the transition after each such label a
Dirac mass.  This explains why DDP variation loses no generality from martingale variation.
-/

/--
Corollary 1.  A generated DDP for each player with positive crossing probability at most
`ε`, together with `ε`-self-perfection and `ε`-viability, yields the same equilibrium
constant as Theorem 1.
-/
theorem corollary1 (G : NormalStochasticGame) (GS : StochasticSemantics G)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (profile : Profile G)
    (hperfect : EpsilonSelfPerfect G GS ε profile)
    (hviable : EpsilonViable G GS ε profile)
    (hprocess : ∀ n : G.Player, ∃ (P : DiscreteDecisionProcess)
      (PS : DDPSemantics P), Nonempty (GeneratedDecisionProcess G GS profile n P PS) ∧
        PositiveCrossingProbability P PS ε ≤ ENNReal.ofReal ε) :
    ∃ equilibrium, IsEpsilonEquilibrium G GS
      (3 * ε * (G.payoffDifferenceBound * PlayerCount G + 2)) equilibrium := by
  have hcross : ∀ n, InducedMeasure G GS profile
      (AdvantageCrossingEvent G GS profile n ε) ≤ ENNReal.ofReal ε := by
    intro n
    rcases hprocess n with ⟨P, PS, ⟨generated⟩, hprobability⟩
    let A : Set (DDPPath P) := {p | ∃ l, DDPAdvantage P p l ≥ ε}
    have hA : MeasurableSet A := measurableSet_ddpAdvantage_crossing P ε
    have hsubset : AdvantageCrossingEvent G GS profile n ε ⊆ generated.pathMap ⁻¹' A := by
      rintro omega ⟨i, hi⟩
      rcases i with _ | l
      · have hzero : CumulativeAdvantage G GS profile n (omega.prefix 0) = 0 :=
          HistoryTo.cumulativeAdvantage_eq_zero_of_length_eq_zero G GS profile n
            (omega.prefix 0).2 (by
              exact HistoryTo.length_transport omega.starts.symm HistoryTo.root)
        rw [hzero] at hi
        linarith
      · exact ⟨l, by
          rw [generated.advantage_eq]
          exact hi.le⟩
    calc
      InducedMeasure G GS profile (AdvantageCrossingEvent G GS profile n ε) ≤
          InducedMeasure G GS profile (generated.pathMap ⁻¹' A) := measure_mono hsubset
      _ = Measure.map generated.pathMap (InducedMeasure G GS profile) A :=
        (Measure.map_apply generated.measurable_pathMap hA).symm
      _ = PS.law A := by rw [generated.law_eq]
      _ = PositiveCrossingProbability P PS ε := rfl
      _ ≤ ENNReal.ofReal ε := hprobability
  obtain ⟨equilibrium, hequilibrium⟩ :=
    theorem1 G GS hε hε1 profile hperfect hviable hcross
  refine ⟨equilibrium, ?_⟩
  convert hequilibrium using 1
  ring

/-- Total variation `w̄(p) = Σ |v(y_{i+1}) - v(x_i)|`, possibly infinite. -/
def DDPTotalVariation (P : DiscreteDecisionProcess) (p : DDPPath P) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal |P.valueY (p.x i) (p.y i) - P.valueX (p.x i)|

/-- A decision process is `δ`-balanced when every chosen-action value is within `δ`. -/
def IsBalanced (P : DiscreteDecisionProcess) (δ : ℝ) : Prop :=
  ∀ x y, |P.valueY x y - P.valueX x| ≤ δ

/-- The probability that the absolute cumulative advantage ever reaches `ε`. -/
def AbsoluteCrossingProbability (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (ε : ℝ) : ℝ≥0∞ :=
  S.law {p | ∃ l, |DDPAdvantage P p l| ≥ ε}

/-- The expected total variation of the decision process under its induced path law. -/
def ExpectedDDPVariation (P : DiscreteDecisionProcess) (S : DDPSemantics P) : ℝ≥0∞ :=
  ∫⁻ p, DDPTotalVariation P p ∂S.law

/--
Proposition 1.  If a DDP is `δ`-balanced, has expected total variation at most `B > 0`,
and `0 < δ ≤ ε²ρ/B` for positive `ε,ρ`, then its absolute crossing probability
is at most `ρ`.
-/
theorem proposition1 (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    {δ ε ρ B : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hρ : 0 < ρ) (hB : 0 < B)
    (hbalanced : IsBalanced P δ)
    (hvariation : ExpectedDDPVariation P S ≤ ENNReal.ofReal B)
    (hsmall : δ ≤ ε ^ 2 * ρ / B) :
    AbsoluteCrossingProbability P S ε ≤ ENNReal.ofReal ρ := by
  sorry

/-! ### 3.3. Rank -/

/-- The event that, after the initial state, the first return to `A` is at `z`. -/
def FirstReturnAt (P : DiscreteDecisionProcess) (A : Set P.X) (z : P.X) :
    Set (DDPPath P) :=
  {p | ∃ k, 0 < k ∧ p.x k = z ∧ z ∈ A ∧ ∀ i, 0 < i → i < k → p.x i ∉ A}

/-- The event that the process returns to `A` after its initial state. -/
def ReturnsTo (P : DiscreteDecisionProcess) (A : Set P.X) : Set (DDPPath P) :=
  ⋃ z ∈ A, FirstReturnAt P A z

/-- The probability `q_y^A` of returning to `A` after forcing action `y` at `x`. -/
def ReturnProbability (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (A : Set P.X) (x : P.X) (y : P.Y x) : ℝ≥0∞ :=
  S.afterAction x y (ReturnsTo P A)

/-- The probability `q_y^{A,z}` that the first return to `A` is at `z`. -/
def FirstReturnProbability (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (A : Set P.X) (x : P.X) (y : P.Y x) (z : P.X) : ℝ≥0∞ :=
  S.afterAction x y (FirstReturnAt P A z)

/-- A lower bound for all values in a decision process. -/
def IsDDPValueLowerBound (P : DiscreteDecisionProcess) (L : ℝ) : Prop :=
  (∀ x, L ≤ P.valueX x) ∧ ∀ x y, L ≤ P.valueY x y

/-- An upper bound for all values in a decision process. -/
def IsDDPValueUpperBound (P : DiscreteDecisionProcess) (U : ℝ) : Prop :=
  (∀ x, P.valueX x ≤ U) ∧ ∀ x y, P.valueY x y ≤ U

/--
The return values `r_y^A`: for positive return probability they are the conditional
expectation at first return; for zero return probability they lie between global value bounds.
-/
structure ReturnValueData (P : DiscreteDecisionProcess) (S : DDPSemantics P) where
  lower : ℝ
  upper : ℝ
  lowerBound : IsDDPValueLowerBound P lower
  upperBound : IsDDPValueUpperBound P upper
  value : (A : Set P.X) → (x : P.X) → P.Y x → ℝ
  positiveEquation : ∀ A x y, 0 < ReturnProbability P S A x y →
    value A x y =
      (∑' z, (FirstReturnProbability P S A x y z).toReal * P.valueX z) /
        (ReturnProbability P S A x y).toReal
  zeroBounds : ∀ A x y, ReturnProbability P S A x y = 0 →
    lower ≤ value A x y ∧ value A x y ≤ upper

/-- A state is varied if one of its actions has a value different from the state value. -/
def IsVaried (P : DiscreteDecisionProcess) (x : P.X) : Prop :=
  ∃ y, P.valueY x y ≠ P.valueX x

/-- The sets `A₁,…,Aₙ` partition precisely the varied states. -/
def PartitionsVariedStates (P : DiscreteDecisionProcess) {n : ℕ}
    (A : Fin n → Set P.X) : Prop :=
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
    ∀ x, IsVaried P x ↔ ∃ i, x ∈ A i

/-- A rank-`n` partition has action-independent return value within every partition cell. -/
def IsRankPartition (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (R : ReturnValueData P S) {n : ℕ} (A : Fin n → Set P.X) : Prop :=
  PartitionsVariedStates P A ∧ ∀ i x, x ∈ A i →
    ∃ r : ℝ, ∀ y : P.Y x, R.value (A i) x y = r

/-- An explicit partition witnessing that the process has a rank partition of size `n`. -/
structure RankPartitionWitness (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (R : ReturnValueData P S) (n : ℕ) where
  cell : Fin n → Set P.X
  valid : IsRankPartition P S R cell

/-- The process has rank exactly `n`: it has an `n`-cell witness and none with fewer cells. -/
def HasProcessRank (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (R : ReturnValueData P S) (n : ℕ) : Prop :=
  Nonempty (RankPartitionWitness P S R n) ∧
    ∀ m, Nonempty (RankPartitionWitness P S R m) → n ≤ m

/-- The process has rank at most `k`, witnessed by an actual finite rank partition. -/
def HasProcessRankAtMost (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (R : ReturnValueData P S) (k : ℕ) : Prop :=
  ∃ n, n ≤ k ∧ Nonempty (RankPartitionWitness P S R n)

/-- A finite rank witness has a least size, hence an exact rank no larger than the witness. -/
theorem exists_processRank_of_rankAtMost (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (R : ReturnValueData P S) {k : ℕ} (h : HasProcessRankAtMost P S R k) :
    ∃ n, n ≤ k ∧ HasProcessRank P S R n := by
  classical
  rcases h with ⟨m, hmk, hm⟩
  let hexists : ∃ n, Nonempty (RankPartitionWitness P S R n) := ⟨m, hm⟩
  let n := Nat.find hexists
  have hn : Nonempty (RankPartitionWitness P S R n) := Nat.find_spec hexists
  have hleast : ∀ q, Nonempty (RankPartitionWitness P S R q) → n ≤ q := by
    intro q hq
    exact Nat.find_min' hexists hq
  exact ⟨n, (hleast m hm).trans hmk, hn, hleast⟩

/-- Proposition 2.  A rank-`n` DDP has expected total variation at most `2nM`. -/
theorem proposition2 (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (R : ReturnValueData P S) {n : ℕ} (hrank : HasProcessRank P S R n) :
    ExpectedDDPVariation P S ≤
      ENNReal.ofReal (2 * n * P.valueDifferenceBound) := by
  sorry

/-- The interior indices of the `2n+1`-state nearest-neighbor process. -/
abbrev Example1Interior (n : ℕ) :=
  {i : Fin (2 * n + 1) // 0 < i.val ∧ i.val < 2 * n}

/-- The predecessor of an interior nearest-neighbor index. -/
def Example1Interior.pred {n : ℕ} (i : Example1Interior n) : Fin (2 * n + 1) :=
  ⟨i.val - 1, by omega⟩

/-- The successor of an interior nearest-neighbor index. -/
def Example1Interior.succ {n : ℕ} (i : Example1Interior n) : Fin (2 * n + 1) :=
  ⟨i.val + 1, by omega⟩

/-- The right absorbing endpoint of Example 1. -/
def Example1RightEndpoint (n : ℕ) : Fin (2 * n + 1) :=
  ⟨2 * n, by omega⟩

/-- The full transition/value data of Example 1. -/
structure Example1Data (n : ℕ) (hn : 0 < n) where
  process : DiscreteDecisionProcess
  semantics : DDPSemantics process
  label : Fin (2 * n + 1) ≃ process.X
  initial : process.initial = label ⟨n, by omega⟩
  left : (i : Example1Interior n) → process.Y (label i)
  right : (i : Example1Interior n) → process.Y (label i)
  allInteriorActions : ∀ (i : Example1Interior n) (y : process.Y (label i)),
    y = left i ∨ y = right i
  chooseLeft : ∀ i : Example1Interior n,
    process.choose (label i) (left i) = (2 : ℝ≥0∞)⁻¹
  chooseRight : ∀ i : Example1Interior n,
    process.choose (label i) (right i) = (2 : ℝ≥0∞)⁻¹
  moveLeft : ∀ i : Example1Interior n,
    process.move (label i) (left i) = PMF.pure (label (Example1Interior.pred i))
  moveRight : ∀ i : Example1Interior n,
    process.move (label i) (right i) = PMF.pure (label (Example1Interior.succ i))
  leftAbsorbing : ∀ y : process.Y (label 0),
    process.move (label 0) y = PMF.pure (label 0)
  rightAbsorbing : ∀ y : process.Y (label (Example1RightEndpoint n)),
    process.move (label (Example1RightEndpoint n)) y =
      PMF.pure (label (Example1RightEndpoint n))
  value : ∀ i,
    process.valueX (label i) = ((i.val : ℝ) - n) / n

/--
Example 1.  The specified symmetric walk has crossing probability `1/2` and expected
total variation at least `n/2`, showing that Proposition 2 needs rank or similar structure.
-/
def Example1 (n : ℕ) : Prop :=
  ∀ hn : 0 < n, ∃ D : Example1Data n hn,
    PositiveCrossingProbability D.process D.semantics 1 = (2 : ℝ≥0∞)⁻¹ ∧
    ENNReal.ofReal ((n : ℝ) / 2) ≤ ExpectedDDPVariation D.process D.semantics

/-! ### 3.4. Chain reduction -/

/-- A controlled path permits every chosen action and requires only possible stochastic moves. -/
structure ControlledDDPPath (P : DiscreteDecisionProcess) (start : P.X) where
  x : ℕ → P.X
  y : (i : ℕ) → P.Y (x i)
  starts : x 0 = start
  movePositive : ∀ i, 0 < P.move (x i) (y i) (x (i + 1))

/-- An actual-process path also uses only actions of positive prescribed probability. -/
structure PrescribedDDPPath (P : DiscreteDecisionProcess) (start : P.X)
    extends ControlledDDPPath P start where
  choosePositive : ∀ i, 0 < P.choose (toControlledDDPPath.x i) (toControlledDDPPath.y i)

/-- The process eventually exits `B` from the specified start under its fixed Markov law. -/
def EventuallyExits (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (B : Set P.X) (x : P.X) : Prop :=
  S.fromState x {p | ∃ i, p.x i ∉ B} = 1

/-- A removable set consists of non-varied states and is left almost surely from each visit. -/
def Removable (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (B : Set P.X) : Prop :=
  (∀ x ∈ B, ¬IsVaried P x) ∧ ∀ x ∈ B, EventuallyExits P S B x

/-- Every visit of the original process to `A ∪ {s}`, including an initial visit, begins at `s`. -/
def EveryVisitBeginsAt (P : DiscreteDecisionProcess) (A : Set P.X) (s : P.X) : Prop :=
  ∀ (p : PrescribedDDPPath P P.initial) i, p.x i ∈ A ∪ {s} →
    (i = 0 ∨ p.x (i - 1) ∉ A ∪ {s}) → p.x i = s

/-- Every controlled path starting in `A` visits `A \ T` at most `m` times. -/
def AtMostVisits (P : DiscreteDecisionProcess) (A T : Set P.X) (m : ℕ) : Prop := by
  classical
  exact ∀ start, start ∈ A → ∀ p : ControlledDDPPath P start, ∀ k,
    (Finset.filter (fun i => p.x i ∈ A \ T) (Finset.range k)).card ≤ m

/-- The event that the first state in `X \ T` reached after the initial state is `z`. -/
def FirstOutsideTAt (P : DiscreteDecisionProcess) (T : Set P.X) (z : P.X) :
    Set (DDPPath P) :=
  {p | ∃ k, 0 < k ∧ p.x k = z ∧ z ∉ T ∧ ∀ i, 0 < i → i < k → p.x i ∈ T}

/-- An action is completing when the first subsequent state outside `T` lies outside `A`. -/
def CompletingAction (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (A T : Set P.X) (x : P.X) (y : P.Y x) : Prop :=
  S.afterAction x y (⋃ z ∈ A, FirstOutsideTAt P T z) = 0

/--
The explicit sets `A_s`, visit bounds, deterministic return targets, and completing-action
alternative witnessing that the disjoint sets `S,T` are chain reducible.
-/
structure ChainReducibilityWitness (P : DiscreteDecisionProcess) (PS : DDPSemantics P)
    (S T : Set P.X) where
  disjoint : Disjoint S T
  removable : Removable P PS T
  chainSet : P.X → Set P.X
  omitsRoot : ∀ s ∈ S, s ∉ chainSet s
  everyVisitBeginsAtRoot : ∀ s ∈ S, EveryVisitBeginsAt P (chainSet s) s
  visitBound : P.X → ℕ
  visitBound_positive : ∀ s ∈ S, 0 < visitBound s
  boundedVisits : ∀ s ∈ S, AtMostVisits P (chainSet s) T (visitBound s)
  actionStructure : ∀ s ∈ S, ∀ x ∈ chainSet s \ T, ∀ y : P.Y x,
    CompletingAction P PS (chainSet s) T x y ∨ ∃ z ∈ chainSet s \ T,
      PS.afterAction x y (FirstOutsideTAt P T z) = 1

/-- `S,T` are chain reducible when the paper's explicit chain witness exists. -/
def ChainReducible (P : DiscreteDecisionProcess) (PS : DDPSemantics P)
    (S T : Set P.X) : Prop :=
  Nonempty (ChainReducibilityWitness P PS S T)

/--
A composite action list starts at `s`, follows the deterministic `n(y)` first-return targets
inside `A \ T`, and ends in a completing action.
-/
def IsCompositeActionList (P : DiscreteDecisionProcess) (PS : DDPSemantics P)
    (A T : Set P.X) (s : P.X) (actions : List ((z : P.X) × P.Y z)) : Prop :=
  ∃ first rest, actions = first :: rest ∧ first.1 = s ∧
    (∀ z ∈ actions, z.1 = s ∨ z.1 ∈ A \ T) ∧
    List.IsChain
      (fun u v => PS.afterAction u.1 u.2 (FirstOutsideTAt P T v.1) = 1)
      actions ∧
    ∃ initialActions last, actions = initialActions ++ [last] ∧
      CompletingAction P PS A T last.1 last.2

/-- The retained state set of the chain reduction. -/
def ChainRetainedStates (P : DiscreteDecisionProcess) (PS : DDPSemantics P)
    {S T : Set P.X} (W : ChainReducibilityWitness P PS S T) : Set P.X :=
  (T ∪ ⋃ s ∈ S, W.chainSet s)ᶜ

/-- The event that the first positive-time visit to the retained set is at `z`. -/
def FirstRetainedAt (P : DiscreteDecisionProcess) (K : Set P.X) (z : P.X) :
    Set (DDPPath P) :=
  {p | ∃ k, 0 < k ∧ p.x k = z ∧ z ∈ K ∧
    ∀ i, 0 < i → i < k → p.x i ∉ K}

/--
The permitted reduced actions: a composite chain at a root in `S`, and the unchanged
single original action at every other retained state.
-/
def IsChainReductionAction (P : DiscreteDecisionProcess) (PS : DDPSemantics P)
    {S T : Set P.X} (W : ChainReducibilityWitness P PS S T) (x : P.X)
    (actions : List ((z : P.X) × P.Y z)) : Prop := by
  classical
  exact if hx : x ∈ S then
      IsCompositeActionList P PS (W.chainSet x) T x actions
    else
      ∃ y : P.Y x, actions = [⟨x, y⟩]

/--
A chain reduction has exactly the paper's retained states and actions.  Its action PMF is the
product along a composite chain, and its transition is the first retained-state distribution
after the final completing action.
-/
structure ChainReductionData (P : DiscreteDecisionProcess) (PS : DDPSemantics P)
    (S T : Set P.X) where
  witness : ChainReducibilityWitness P PS S T
  reduced : DiscreteDecisionProcess
  semantics : DDPSemantics reduced
  kept : reduced.X → P.X
  kept_injective : Function.Injective kept
  kept_range : range kept = ChainRetainedStates P PS witness
  initial_eq : kept reduced.initial = P.initial
  composite : (x : reduced.X) → reduced.Y x →
    List ((z : P.X) × P.Y z)
  composite_valid : ∀ x y,
    IsChainReductionAction P PS witness (kept x) (composite x y)
  composite_complete : ∀ x actions,
    IsChainReductionAction P PS witness (kept x) actions →
      ∃! y, composite x y = actions
  composite_probability : ∀ x y,
    reduced.choose x y = ((composite x y).map fun z => P.choose z.1 z.2).prod
  exitTransition : ∀ x y z initialActions last,
    composite x y = initialActions ++ [last] →
      reduced.move x y z =
        PS.afterAction last.1 last.2
          (FirstRetainedAt P (ChainRetainedStates P PS witness) (kept z))
  valueX_eq : ∀ x, reduced.valueX x = P.valueX (kept x)
  valueDifferenceBound_le : reduced.valueDifferenceBound ≤ P.valueDifferenceBound
  telescopes : ∀ x y,
    reduced.valueY x y - reduced.valueX x =
      ((composite x y).map fun z => P.valueY z.1 z.2 - P.valueX z.1).sum

/--
Lemma 1.  If a chain reduction is `δ`-balanced, then for every `ε > 0` the original
probability of `sup W_i > ε+δ` is at most the reduced probability of `sup W_i > ε`.
-/
theorem lemma1 (P : DiscreteDecisionProcess) (PS : DDPSemantics P)
    (S T : Set P.X) (R : ChainReductionData P PS S T) {δ : ℝ}
    (hδ : 0 < δ) (hbalanced : IsBalanced R.reduced δ) :
    ∀ ε : ℝ, 0 < ε →
      PS.law {p | ∃ i, DDPAdvantage P p i > ε + δ} ≤
        R.semantics.law {p | ∃ i, DDPAdvantage R.reduced p i > ε} := by
  sorry

/--
Theorem 2.  A fixed positive rank bound on `ε`-balanced generated chain reductions,
available with `ε`-self-perfect and `ε`-viable profiles for every `ε > 0`, implies
existence of approximate equilibria.
-/
theorem theorem2 (G : NormalStochasticGame) (GS : StochasticSemantics G)
    (k : ℕ) (hk : 0 < k)
    (h : ∀ ε : ℝ, 0 < ε → ∃ profile : Profile G,
      EpsilonSelfPerfect G GS ε profile ∧ EpsilonViable G GS ε profile ∧
      ∀ n : G.Player, ∃ (P : DiscreteDecisionProcess) (PS : DDPSemantics P)
        (_generated : GeneratedDecisionProcess G GS profile n P PS)
        (S T : Set P.X) (CR : ChainReductionData P PS S T)
        (RV : ReturnValueData CR.reduced CR.semantics),
          IsBalanced CR.reduced ε ∧
            HasProcessRankAtMost CR.reduced CR.semantics RV k) :
    HasApproximateEquilibria G GS := by
  intro target htarget
  let C : ℝ := G.payoffDifferenceBound * PlayerCount G + 2
  have hplayers : 0 < PlayerCount G := Fintype.card_pos
  have hC : 0 < C := by
    dsimp [C, PlayerCount]
    have hM := G.payoffDifferenceBound_one
    positivity
  let e : ℝ := min (1 / 2) (target / (6 * C))
  have he : 0 < e := by
    dsimp [e]
    exact lt_min (by norm_num) (div_pos htarget (mul_pos (by norm_num) hC))
  have he1 : e ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  have heTarget : 3 * e * C ≤ target := by
    have heBound : e ≤ target / (6 * C) := min_le_right _ _
    rw [le_div_iff₀ (mul_pos (by norm_num) hC)] at heBound
    nlinarith
  let B : ℝ := 2 * k * G.payoffDifferenceBound
  have hB : 0 < B := by
    dsimp [B]
    have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
    have hM : 0 < G.payoffDifferenceBound := lt_of_lt_of_le zero_lt_one
      G.payoffDifferenceBound_one
    positivity
  let d : ℝ := min (e / 4) (e ^ 3 / (8 * B))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (div_pos he (by norm_num))
      (div_pos (pow_pos he 3) (mul_pos (by norm_num) hB))
  have hde : d ≤ e := le_trans (min_le_left _ _) (by linarith [he])
  have hdHalf : d < e / 2 :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith [he])
  have hdSmall : d ≤ (e / 2) ^ 2 * e / B := by
    have hdBound : d ≤ e ^ 3 / (8 * B) := min_le_right _ _
    rw [le_div_iff₀ (mul_pos (by norm_num) hB)] at hdBound
    rw [le_div_iff₀ hB]
    nlinarith [sq_nonneg e, pow_pos he 3]
  rcases h d hd with ⟨profile, hperfect, hviable, hreductions⟩
  have hprocess : ∀ n : G.Player, ∃ (P : DiscreteDecisionProcess)
      (PS : DDPSemantics P), Nonempty (GeneratedDecisionProcess G GS profile n P PS) ∧
        PositiveCrossingProbability P PS e ≤ ENNReal.ofReal e := by
    intro n
    rcases hreductions n with ⟨P, PS, generated, S, T, CR, RV, hbalanced, hrankAtMost⟩
    rcases exists_processRank_of_rankAtMost CR.reduced CR.semantics RV hrankAtMost with
      ⟨rank, hrankk, hrank⟩
    have hvariation : ExpectedDDPVariation CR.reduced CR.semantics ≤ ENNReal.ofReal B := by
      refine (proposition2 CR.reduced CR.semantics RV hrank).trans ?_
      apply ENNReal.ofReal_le_ofReal
      have hrankReal : (rank : ℝ) ≤ k := by exact_mod_cast hrankk
      have hbound : CR.reduced.valueDifferenceBound ≤ G.payoffDifferenceBound :=
        CR.valueDifferenceBound_le.trans generated.valueDifferenceBound_le
      have hrankNonnegative : (0 : ℝ) ≤ rank := Nat.cast_nonneg rank
      have hReducedNonnegative : 0 ≤ CR.reduced.valueDifferenceBound :=
        (zero_le_one.trans CR.reduced.valueDifferenceBound_one)
      dsimp [B]
      nlinarith
    have habsolute := proposition1 CR.reduced CR.semantics
      hd (half_pos he) he hB hbalanced hvariation hdSmall
    have htransfer := lemma1 P PS S T CR hd hbalanced (e / 2) (half_pos he)
    refine ⟨P, PS, ⟨generated⟩, ?_⟩
    change PS.law {p | ∃ l, DDPAdvantage P p l ≥ e} ≤ ENNReal.ofReal e
    calc
      PS.law {p | ∃ l, DDPAdvantage P p l ≥ e} ≤
          PS.law {p | ∃ l, DDPAdvantage P p l > e / 2 + d} := by
        apply measure_mono
        rintro p ⟨l, hl⟩
        exact ⟨l, by linarith⟩
      _ ≤ CR.semantics.law {p | ∃ l, DDPAdvantage CR.reduced p l > e / 2} :=
        htransfer
      _ ≤ CR.semantics.law {p | ∃ l, |DDPAdvantage CR.reduced p l| ≥ e / 2} := by
        apply measure_mono
        rintro p ⟨l, hl⟩
        refine ⟨l, ?_⟩
        rw [abs_of_pos (lt_trans (half_pos he) hl)]
        exact hl.le
      _ ≤ ENNReal.ofReal e := habsolute
  obtain ⟨equilibrium, hequilibrium⟩ := corollary1 G GS he he1 profile
    (hperfect.mono G GS hde) (hviable.mono G GS hde) hprocess
  refine ⟨equilibrium, ?_⟩
  intro n deviation
  exact (hequilibrium n deviation).trans (by
    dsimp [C] at heTarget
    linarith)

/-- The full transition/value and three-state chain-reduction data of Example 2. -/
structure Example2Data (n : ℕ) (hn : 0 < n) where
  process : DiscreteDecisionProcess
  semantics : DDPSemantics process
  label : Fin (n + 1) ⊕ Unit ≃ process.X
  initial : process.initial = label (Sum.inl 0)
  left : (i : Fin n) → process.Y (label (Sum.inl i.castSucc))
  right : (i : Fin n) → process.Y (label (Sum.inl i.castSucc))
  allInteriorActions : ∀ (i : Fin n)
    (y : process.Y (label (Sum.inl i.castSucc))), y = left i ∨ y = right i
  chooseLeft : ∀ i : Fin n,
    process.choose (label (Sum.inl i.castSucc)) (left i) = (2 : ℝ≥0∞)⁻¹
  chooseRight : ∀ i : Fin n,
    process.choose (label (Sum.inl i.castSucc)) (right i) = (2 : ℝ≥0∞)⁻¹
  moveLeftB : ∀ i : Fin n,
    process.move (label (Sum.inl i.castSucc)) (left i) (label (Sum.inr ())) =
      ENNReal.ofReal (1 / ((2 : ℝ) ^ n - 1))
  moveLeftX0 : ∀ i : Fin n,
    process.move (label (Sum.inl i.castSucc)) (left i) (label (Sum.inl 0)) =
      ENNReal.ofReal (((2 : ℝ) ^ n - 2) / ((2 : ℝ) ^ n - 1))
  moveLeftOther : ∀ (i : Fin n) (z : process.X),
    z ≠ label (Sum.inr ()) → z ≠ label (Sum.inl 0) →
      process.move (label (Sum.inl i.castSucc)) (left i) z = 0
  moveRight : ∀ i : Fin n,
    process.move (label (Sum.inl i.castSucc)) (right i) =
      PMF.pure (label (Sum.inl i.succ))
  bAbsorbing : ∀ y : process.Y (label (Sum.inr ())),
    process.move (label (Sum.inr ())) y = PMF.pure (label (Sum.inr ()))
  xnAbsorbing : ∀ y : process.Y (label (Sum.inl (Fin.last n))),
    process.move (label (Sum.inl (Fin.last n))) y =
      PMF.pure (label (Sum.inl (Fin.last n)))
  valueB : process.valueX (label (Sum.inr ())) = 1
  valueX : ∀ i,
    process.valueX (label (Sum.inl i)) =
      (1 - (2 : ℝ) ^ i.val) / ((2 : ℝ) ^ n - 1)
  S : Set process.X
  T : Set process.X
  reduction : ChainReductionData process semantics S T
  reducedStates : Nonempty (reduction.reduced.X ≃ Fin 3)

/--
Example 2.  The specified process has original expected variation at least `n/2`, whereas
its three-state chain reduction has expected variation exactly `1`.
-/
def Example2 (n : ℕ) : Prop :=
  ∀ hn : 0 < n, ∃ D : Example2Data n hn,
    ENNReal.ofReal ((n : ℝ) / 2) ≤ ExpectedDDPVariation D.process D.semantics ∧
      ExpectedDDPVariation D.reduction.reduced D.reduction.semantics = 1

/-! ### 3.5. Markov chains and total variation -/

/-- A finite-state, possibly time-inhomogeneous Markov chain with harmonic `[0,1]` values. -/
structure MarkovChain where
  State : Type
  [finiteState : Fintype State]
  [nonemptyState : Nonempty State]
  transition : ℕ → State → PMF State
  initial : State
  value : State → ℕ → Set.Icc (0 : ℝ) 1
  harmonic : ∀ x i,
    (value x i : ℝ) = ∑' y, (transition i x y).toReal * value y (i + 1)

attribute [instance] MarkovChain.finiteState
attribute [instance] MarkovChain.nonemptyState

/-- A possible infinite path of a Markov chain. -/
structure MarkovPath (P : MarkovChain) where
  state : ℕ → P.State
  starts : state 0 = P.initial
  positive : ∀ i, 0 < P.transition i (state i) (state (i + 1))

/-- The sigma algebra generated by finite Markov-path coordinate cylinders. -/
instance markovPathMeasurableSpace (P : MarkovChain) : MeasurableSpace (MarkovPath P) :=
  MeasurableSpace.generateFrom
    {U | ∃ (k : ℕ) (x : Fin (k + 1) → P.State),
      U = {p | ∀ i : Fin (k + 1), p.state i = x i}}

/-- The induced Markov path law, constrained by its finite-dimensional cylinder products. -/
structure MarkovSemantics (P : MarkovChain) where
  law : Measure (MarkovPath P)
  probability : IsProbabilityMeasure law
  cylinder : ∀ (k : ℕ) (x : Fin (k + 1) → P.State), x 0 = P.initial →
    law {p | ∀ i : Fin (k + 1), p.state i = x i} =
      ∏ i : Fin k, P.transition i (x i.castSucc) (x i.succ)

/-- Ionescu--Tulcea extension supplies the Markov path law with these cylinder probabilities. -/
theorem markovSemantics_exists (P : MarkovChain) : Nonempty (MarkovSemantics P) := by
  sorry

/-- Time homogeneity means that the transition law is independent of the stage. -/
def TimeHomogeneous (P : MarkovChain) : Prop :=
  ∃ transition : P.State → PMF P.State, ∀ i, P.transition i = transition

/-- The pathwise total variation of the time-dependent harmonic value, possibly infinite. -/
def MarkovVariation (P : MarkovChain) (p : MarkovPath P) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal
    |(P.value (p.state (i + 1)) (i + 1) : ℝ) - P.value (p.state i) i|

/-- The expected total variation under the induced Markov path law. -/
def ExpectedMarkovVariation (P : MarkovChain) (S : MarkovSemantics P) : ℝ≥0∞ :=
  ∫⁻ p, MarkovVariation P p ∂S.law

/-- Lemma 2.  A time-homogeneous finite Markov chain has expected variation at most `|X|`. -/
theorem lemma2 (P : MarkovChain) (S : MarkovSemantics P)
    (h : TimeHomogeneous P) :
    ExpectedMarkovVariation P S ≤ Fintype.card P.State := by
  sorry

/-- Conjecture 1.  Lemma 2's `|X|` bound should hold without time homogeneity. -/
def Conjecture1 : Prop :=
  ∀ (P : MarkovChain) (S : MarkovSemantics P),
    ExpectedMarkovVariation P S ≤ Fintype.card P.State

/-! ## 4. Quitting games -/

/-- A quitting game assigns a payoff vector to each nonempty coalition of simultaneous quitters. -/
structure QuittingGame where
  Player : Type
  [finitePlayer : Fintype Player]
  [nonemptyPlayer : Nonempty Player]
  reward : {A : Finset Player // A.Nonempty} → Payoff Player

attribute [instance] QuittingGame.finitePlayer
attribute [instance] QuittingGame.nonemptyPlayer

/-- A one-stage quitting row gives each player's conditional probability of quitting. -/
abbrev QuitRow (G : QuittingGame) := G.Player → Set.Icc (0 : ℝ) 1

/-- A quitting strategy profile is a sequence of conditional one-stage quitting rows. -/
abbrev QuitProfile (G : QuittingGame) := ℕ → QuitRow G

/-- The probability `q(p)` that at least one player quits in a row. -/
def QuitProbability (G : QuittingGame) (p : QuitRow G) : ℝ :=
  1 - ∏ n, (1 - (p n : ℝ))

/-- The one-row quitting probability lies in the unit interval. -/
theorem quitProbability_mem_Icc (G : QuittingGame) (p : QuitRow G) :
    QuitProbability G p ∈ Set.Icc (0 : ℝ) 1 := by
  have hfactor0 : ∀ n ∈ Finset.univ, 0 ≤ 1 - (p n : ℝ) := by
    intro n _
    exact sub_nonneg.mpr (p n).property.2
  have hfactor1 : ∀ n ∈ Finset.univ, 1 - (p n : ℝ) ≤ 1 := by
    intro n _
    linarith [(p n).property.1]
  constructor
  · exact sub_nonneg.mpr (Finset.prod_le_one hfactor0 hfactor1)
  · have := Finset.prod_nonneg hfactor0
    simp only [QuitProbability]
    linarith

/-- The probability that exactly the coalition `A` quits in a row. -/
def CoalitionProbability (G : QuittingGame) (p : QuitRow G)
    (A : Finset G.Player) : ℝ := by
  classical
  exact (∏ n ∈ A, (p n : ℝ)) *
    ∏ n ∈ Finset.univ.filter (fun n => n ∉ A), (1 - (p n : ℝ))

/-- The expected one-stage payoff `f(r,p)` with continuation vector `r`. -/
def QuittingOneStagePayoff (G : QuittingGame) (r : Payoff G.Player)
    (p : QuitRow G) : Payoff G.Player :=
  fun n => (1 - QuitProbability G p) * r n +
    ∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
      CoalitionProbability G p A * G.reward ⟨A, hA⟩ n
    else 0

/-- The tail payoff `r_i(p)` of a quitting profile, conditional on reaching stage `i`. -/
def QuitTailPayoff (G : QuittingGame) (p : QuitProfile G) (i : ℕ) : Payoff G.Player :=
  fun n => ∑' k,
    (Finset.prod (Finset.range k) fun j => 1 - QuitProbability G (p (i + j))) *
      ∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
        CoalitionProbability G (p (i + k)) A * G.reward ⟨A, hA⟩ n
      else 0

/-- The expected payoff of a quitting profile; nontermination contributes the paper's payoff `0`. -/
def QuitPayoff (G : QuittingGame) (p : QuitProfile G) : Payoff G.Player :=
  QuitTailPayoff G p 0

/-- Replace one player's entire quitting-probability sequence. -/
def QuitProfile.replace (G : QuittingGame) (p : QuitProfile G)
    (n : G.Player) (q : ℕ → Set.Icc (0 : ℝ) 1) : QuitProfile G := by
  classical
  exact fun i k => if k = n then q i else p i k

/-- A quitting profile is an `ε`-equilibrium against every unilateral sequence deviation. -/
def IsQuitEpsilonEquilibrium (G : QuittingGame) (ε : ℝ) (p : QuitProfile G) : Prop :=
  ∀ n (q : ℕ → Set.Icc (0 : ℝ) 1),
    QuitPayoff G (p.replace G n q) n ≤ QuitPayoff G p n + ε

/-- Approximate equilibria exist when a quitting `ε`-equilibrium exists for every `ε > 0`. -/
def HasQuitApproximateEquilibria (G : QuittingGame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ p : QuitProfile G, IsQuitEpsilonEquilibrium G ε p

/-- `M ≥ 1` is strictly larger than every difference between quitting-game payoffs. -/
def IsQuittingPayoffDifferenceBound (G : QuittingGame) (M : ℝ) : Prop :=
  1 ≤ M ∧ (∀ A B n, |G.reward A n - G.reward B n| < M) ∧
    ∀ A n, |G.reward A n| < M

/-- Every finite quitting table has a strict payoff-difference bound. -/
theorem exists_quittingPayoffDifferenceBound (G : QuittingGame) :
    ∃ M : ℝ, IsQuittingPayoffDifferenceBound G M := by
  classical
  let total : ℝ := ∑ A : {A : Finset G.Player // A.Nonempty}, ∑ n, |G.reward A n|
  have hentry : ∀ A n, |G.reward A n| ≤ total := by
    intro A n
    refine (Finset.single_le_sum (fun i _ => abs_nonneg (G.reward A i))
      (Finset.mem_univ n)).trans ?_
    exact Finset.single_le_sum
      (fun B _ => Finset.sum_nonneg fun i _ => abs_nonneg (G.reward B i))
      (Finset.mem_univ A)
  have htotal : 0 ≤ total := Finset.sum_nonneg fun C _ =>
    Finset.sum_nonneg fun i _ => abs_nonneg (G.reward C i)
  refine ⟨1 + 2 * total, by linarith, ?_, ?_⟩
  · intro A B n
    calc
      |G.reward A n - G.reward B n| ≤ |G.reward A n| + |G.reward B n| := abs_sub _ _
      _ ≤ total + total := add_le_add (hentry A n) (hentry B n)
      _ < 1 + 2 * total := by linarith
  · intro A n
    exact lt_of_le_of_lt (hentry A n) (by linarith)

/-! ### 4.2. Correspondences and orbits -/

/-- A correspondence `F : X → Y` is represented by its set-valued fibers. -/
abbrev Correspondence (X Y : Type) := X → Set Y

/-- The restriction `F|A` of a correspondence to a subset of its domain. -/
def Correspondence.restrict {X Y : Type} (F : Correspondence X Y)
    (A : Set X) : Correspondence X Y := by
  classical
  exact fun x => if x ∈ A then F x else ∅

/-- The domain of a correspondence is the set of points with nonempty fiber. -/
def Correspondence.domain {X Y : Type} (F : Correspondence X Y) : Set X :=
  {x | (F x).Nonempty}

/-- The image of a correspondence is the union of all its fibers. -/
def Correspondence.image {X Y : Type} (F : Correspondence X Y) : Set Y :=
  ⋃ x, F x

/-- An infinite orbit satisfies `x_{i+1} ∈ F(x_i)` at every stage. -/
def IsInfiniteOrbit {X : Type} (F : Correspondence X X) (x : ℕ → X) : Prop :=
  ∀ i, x (i + 1) ∈ F (x i)

/-- A finite orbit of length `k` satisfies the correspondence relation at each adjacent pair. -/
def IsFiniteOrbit {X : Type} (F : Correspondence X X) {k : ℕ}
    (x : Fin (k + 1) → X) : Prop :=
  ∀ i : Fin k, x i.succ ∈ F (x i.castSucc)

/-- `none` denotes an infinite segment; `some k` denotes a segment with exactly `k` points. -/
def SegmentIndex (length : Option ℕ) (i : ℕ) : Prop :=
  ∀ k, length = some k → i < k

/-- `none` denotes infinitely many segments; `some L` denotes exactly `L` segments. -/
def ActiveSegment (count : Option ℕ) (j : ℕ) : Prop :=
  ∀ L, count = some L → j < L

/--
An extended orbit is made of finite or infinite orbit segments, stitched at a finite endpoint
or by convergence of an infinite segment to the next segment's first point.
-/
structure ExtendedOrbitData {X : Type} [TopologicalSpace X]
    (F : Correspondence X X) where
  segmentCount : Option ℕ
  segmentCountPositive : ∀ L, segmentCount = some L → 0 < L
  segmentLength : ℕ → Option ℕ
  segmentLengthPositive : ∀ j, ActiveSegment segmentCount j → ∀ k,
    segmentLength j = some k → 0 < k
  point : ℕ → ℕ → X
  step : ∀ j, ActiveSegment segmentCount j → ∀ i,
    SegmentIndex (segmentLength j) (i + 1) → point j (i + 1) ∈ F (point j i)
  finiteStitch : ∀ j, ActiveSegment segmentCount (j + 1) → ∀ k,
    segmentLength j = some k → point j (k - 1) = point (j + 1) 0
  infiniteStitch : ∀ j, ActiveSegment segmentCount (j + 1) →
    segmentLength j = none → Tendsto (point j) atTop (nhds (point (j + 1) 0))

/--
Unbounded total variation means that finite partial sums exceed every real bound.
-/
def HasUnboundedExtendedVariation {N : Type} [Fintype N]
    {F : Correspondence (Payoff N) (Payoff N)} (x : ExtendedOrbitData F) : Prop := by
  classical
  exact ∀ B : ℝ, ∃ J I : ℕ, B ≤
    Finset.sum (Finset.range J) (fun j =>
      Finset.sum (Finset.range I) fun i =>
        if ActiveSegment x.segmentCount j ∧ SegmentIndex (x.segmentLength j) (i + 1)
        then ‖x.point j (i + 1) - x.point j i‖ else 0)

/-- The one-stage quitting game `Γ_r` pays `r` if every player continues. -/
def QuittingStageGame (G : QuittingGame) (r : Payoff G.Player) :
    (G.Player → Bool) → Payoff G.Player := by
  classical
  exact fun action n =>
    let A := Finset.univ.filter fun k => action k = true
    if hA : A.Nonempty then G.reward ⟨A, hA⟩ n else r n

/-- Force player `n`'s quit probability in a one-stage row. -/
def QuitRow.replace (G : QuittingGame) (p : QuitRow G) (n : G.Player)
    (q : Set.Icc (0 : ℝ) 1) : QuitRow G := by
  classical
  exact fun k => if k = n then q else p k

/-- Forcing one player to continue cannot increase the probability that somebody quits. -/
theorem quitProbability_replace_zero_le (G : QuittingGame) (p : QuitRow G)
    (n : G.Player) : QuitProbability G (p.replace G n 0) ≤ QuitProbability G p := by
  simp only [QuitProbability]
  apply sub_le_sub_left
  apply Finset.prod_le_prod
  · intro i hi
    exact sub_nonneg.mpr (p i).property.2
  · intro i hi
    by_cases hin : i = n
    · subst i
      simpa [QuitRow.replace] using (p n).property.1
    · simp [QuitRow.replace, hin]

/-- `aⁿ(p)` is player `n`'s expected payoff when she is forced to quit. -/
def ForcedQuitPayoff (G : QuittingGame) (p : QuitRow G) (n : G.Player) : ℝ :=
  QuittingOneStagePayoff G 0 (p.replace G n 1) n

/-- `bⁿ(r,p)` is player `n`'s expected payoff when she is forced to continue. -/
def ForcedContinuePayoff (G : QuittingGame) (r : Payoff G.Player)
    (p : QuitRow G) (n : G.Player) : ℝ :=
  QuittingOneStagePayoff G r (p.replace G n 0) n

/--
`E_ε(r)` consists exactly of rows satisfying the two endpoint best-response conditions:
positive quit support compares `aⁿ(p)` with `bⁿ(r,p)`, and positive continue support
compares `bⁿ(r,p)` with `aⁿ(p)`.
-/
def EpsilonRow (G : QuittingGame) (ε : ℝ) :
    Correspondence (Payoff G.Player) (QuitRow G) :=
  fun r => {p |
    (∀ n, 0 < (p n : ℝ) → ForcedQuitPayoff G p n ≥
      ForcedContinuePayoff G r p n - ε) ∧
    ∀ n, (p n : ℝ) < 1 → ForcedContinuePayoff G r p n ≥
      ForcedQuitPayoff G p n - ε}

/-- Increasing the one-stage error weakens the endpoint best-response conditions. -/
theorem EpsilonRow.mono (G : QuittingGame) {δ ε : ℝ} (hδε : δ ≤ ε)
    (r : Payoff G.Player) : EpsilonRow G δ r ⊆ EpsilonRow G ε r := by
  rintro p ⟨hquit, hcontinue⟩
  constructor
  · intro n hn
    exact le_trans (by linarith : ForcedContinuePayoff G r p n - ε ≤
      ForcedContinuePayoff G r p n - δ) (hquit n hn)
  · intro n hn
    exact le_trans (by linarith : ForcedQuitPayoff G p n - ε ≤
      ForcedQuitPayoff G p n - δ) (hcontinue n hn)

/-- `F_ε(r) = {f(r,p) | p ∈ E_ε(r)}`. -/
def FRow (G : QuittingGame) (ε : ℝ) :
    Correspondence (Payoff G.Player) (Payoff G.Player) :=
  fun r => {QuittingOneStagePayoff G r p | p ∈ EpsilonRow G ε r}

/-- Increasing the one-stage error enlarges the quitting payoff correspondence. -/
theorem FRow.mono (G : QuittingGame) {δ ε : ℝ} (hδε : δ ≤ ε) (r : Payoff G.Player) :
    FRow G δ r ⊆ FRow G ε r := by
  rintro y ⟨p, hp, rfl⟩
  refine ⟨p, ⟨?_, ?_⟩, rfl⟩
  · intro n hquit
    exact le_trans (by linarith : ForcedContinuePayoff G r p n - ε ≤
      ForcedContinuePayoff G r p n - δ) (hp.1 n hquit)
  · intro n hcontinue
    exact le_trans (by linarith : ForcedQuitPayoff G p n - ε ≤
      ForcedQuitPayoff G p n - δ) (hp.2 n hcontinue)

/-! ### 4.3. Normal players, instant equilibria, and stationary equilibria -/

/-- A vector is feasible if it lies in the convex hull of the quitting payoffs and zero. -/
def Feasible (G : QuittingGame) (r : Payoff G.Player) : Prop :=
  r ∈ convexHull ℝ (range G.reward ∪ {0})

/-- The quitting-game min-max `χⁿ = inf_p sup_q Vⁿ(p|qⁿ)`, derived from payoffs. -/
def MinMaxQuit (G : QuittingGame) (n : G.Player) : ℝ :=
  ⨅ p : QuitProfile G, ⨆ q : ℕ → Set.Icc (0 : ℝ) 1,
    QuitPayoff G (p.replace G n q) n

/-- A vector is `ε`-rational if every coordinate is at least its min-max minus `ε`. -/
def IsRational (G : QuittingGame) (ε : ℝ) (r : Payoff G.Player) : Prop :=
  ∀ n, r n ≥ MinMaxQuit G n - ε

/-- The solo-quitting payoff `vⁿ = v({n})ⁿ`. -/
def SoloPayoff (G : QuittingGame) (n : G.Player) : ℝ :=
  G.reward ⟨{n}, Finset.singleton_nonempty n⟩ n

/-- A player is normal when `v({n})ⁿ ≥ χⁿ`. -/
def IsNormalPlayer (G : QuittingGame) (n : G.Player) : Prop :=
  SoloPayoff G n ≥ MinMaxQuit G n

/-- The paper's vector `v` has coordinate `vⁱ = v({i})ⁱ`. -/
def SoloPayoffVector (G : QuittingGame) : Payoff G.Player :=
  SoloPayoff G

/-- Lemma 3.  An abnormal `j` has `vʲ < 0`, and `v({i})ʲ ≥ χʲ` for every `i ≠ j`. -/
theorem lemma3 (G : QuittingGame) (j : G.Player) (h : ¬IsNormalPlayer G j) :
    SoloPayoff G j < 0 ∧ ∀ i, i ≠ j →
      G.reward ⟨{i}, Finset.singleton_nonempty i⟩ j ≥ MinMaxQuit G j := by
  sorry

/-- Reverse and periodically repeat a finite block of quitting rows. -/
def ReverseCycleProfile (G : QuittingGame) (k : ℕ) (_hk : 0 < k)
    (p : ℕ → QuitRow G) : QuitProfile G :=
  fun i => p (k - 1 - i % k)

/--
Lemma 4.  Reversing and repeating a block whose continuation vectors return within `δ`
produces tail vectors within `δ/ρ`; `E_ε` membership degrades only to
`E_{ε+δ/ρ}`.
-/
theorem lemma4 (G : QuittingGame) {k : ℕ} (hk : 0 < k)
    (p : ℕ → QuitRow G) (s : ℕ → Payoff G.Player) {ρ δ ε : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hprob : ρ = 1 - ∏ j ∈ Finset.range k, 1 - QuitProbability G (p j))
    (hstep : ∀ j < k, s (j + 1) = QuittingOneStagePayoff G (s j) (p j))
    (hclose : ‖s 0 - s k‖ ≤ δ) :
    let cycle := ReverseCycleProfile G k hk p
    (∀ m i, (m - 1) * k < i → i ≤ m * k →
      ‖QuitTailPayoff G cycle i - s (m * k - i)‖ ≤ δ / ρ) ∧
    ((∀ j < k, p j ∈ EpsilonRow G ε (s j)) →
      ∀ i, cycle i ∈ EpsilonRow G (ε + δ / ρ) (QuitTailPayoff G cycle (i + 1))) := by
  sorry

/-- A quitting game has stationary approximate equilibria in the paper's sense. -/
def HasStationaryApproximateEquilibria (G : QuittingGame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ p : QuitRow G,
    IsQuitEpsilonEquilibrium G ε (fun _ => p)

/-- The first-stage row followed by a specified punishment profile. -/
def InstantProfile (G : QuittingGame) (p : QuitRow G)
    (punishment : QuitProfile G) : QuitProfile G
  | 0 => p
  | i + 1 => punishment i

/--
A quitting game has instant approximate equilibria when some player quits surely at stage
one and, if she did not, stage-two punishment holds her to `χʲ+ε` in a `2ε`-equilibrium.
-/
def HasInstantApproximateEquilibria (G : QuittingGame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (p : QuitRow G) (j : G.Player)
    (punishment : QuitProfile G), (p j : ℝ) = 1 ∧
      (∀ q : ℕ → Set.Icc (0 : ℝ) 1,
        QuitPayoff G (punishment.replace G j q) j ≤ MinMaxQuit G j + ε) ∧
      IsQuitEpsilonEquilibrium G (2 * ε) (InstantProfile G p punishment)

/-- Stationary approximate equilibria are, in particular, quitting-game equilibria. -/
theorem HasStationaryApproximateEquilibria.hasQuitApproximateEquilibria
    (G : QuittingGame) (h : HasStationaryApproximateEquilibria G) :
    HasQuitApproximateEquilibria G := by
  intro ε hε
  rcases h ε hε with ⟨p, hp⟩
  exact ⟨fun _ => p, hp⟩

/-- The instant construction supplies approximate equilibria after halving the input error. -/
theorem HasInstantApproximateEquilibria.hasQuitApproximateEquilibria
    (G : QuittingGame) (h : HasInstantApproximateEquilibria G) :
    HasQuitApproximateEquilibria G := by
  intro ε hε
  rcases h (ε / 2) (half_pos hε) with ⟨p, j, punishment, _hj, _hpunish, hequilibrium⟩
  refine ⟨InstantProfile G p punishment, ?_⟩
  convert hequilibrium using 1
  ring

/--
Lemma 5.  Without stationary or instant approximate equilibria there is a positive normal
solo payoff, every normal solo quitter harms another normal player, and one uniform `ρ`
controls both motion and quitting probability.

The printed part (2a) has the free vector `x`; the hypothesis and proof use `r`, so the
statement below records the repaired norm `‖r-y‖`.
-/
theorem lemma5 (G : QuittingGame)
    (hstationary : ¬HasStationaryApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    (∃ l, IsNormalPlayer G l ∧ 0 < SoloPayoff G l) ∧
    (∀ j, IsNormalPlayer G j → ∃ k, k ≠ j ∧ IsNormalPlayer G k ∧
      G.reward ⟨{j}, Finset.singleton_nonempty j⟩ k < SoloPayoff G k) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ r p,
      IsRational G ρ r → p ∈ EpsilonRow G ρ r →
      let y := QuittingOneStagePayoff G r p
      ρ * QuitProbability G p ≤ ‖r - y‖ ∧ QuitProbability G p ≤ 1 - ρ := by
  sorry

/-! ### 4.4. Equivalences -/

/--
Divergence of `Σ_i q(p_i)` is expressed by unbounded finite partial sums.
-/
def HasUnboundedQuitMass (G : QuittingGame) (p : QuitProfile G) : Prop :=
  ∀ B : ℝ, ∃ k, B ≤ ∑ i ∈ Finset.range k, QuitProbability G (p i)

/--
Proposition 3.  For `0 < ε ≤ 1`, `0 < δ < ε⁴/(2M³)`, an `ε`-rational
`F_δ` profile with unbounded quit mass is a `3ε`-equilibrium.  Here `M` is explicitly
the paper's payoff-difference bound.
-/
theorem proposition3 (G : QuittingGame) {M ε δ : ℝ}
    (hM : IsQuittingPayoffDifferenceBound G M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hsmall : δ < ε ^ 4 / (2 * M ^ 3)) (p : QuitProfile G)
    (hrational : ∀ i, IsRational G ε (QuitTailPayoff G p i))
    (hmass : HasUnboundedQuitMass G p)
    (horbit : ∀ i, QuitTailPayoff G p i ∈ FRow G δ (QuitTailPayoff G p (i + 1))) :
    IsQuitEpsilonEquilibrium G (3 * ε) p := by
  sorry

/-- A periodic repetition of a positive-length block of quitting rows. -/
def CycleProfile (G : QuittingGame) (k : ℕ) (hk : 0 < k)
    (block : Fin k → QuitRow G) : QuitProfile G :=
  fun i => block ⟨i % k, Nat.mod_lt i hk⟩

/-- A positive-mass finite quitting block has unbounded mass when repeated periodically. -/
theorem CycleProfile.hasUnboundedQuitMass (G : QuittingGame) {k : ℕ} (hk : 0 < k)
    (block : Fin k → QuitRow G) (hpositive : ∃ i, 0 < QuitProbability G (block i)) :
    HasUnboundedQuitMass G (CycleProfile G k hk block) := by
  let cycle := CycleProfile G k hk block
  let blockMass : ℝ := ∑ i ∈ Finset.range k, QuitProbability G (cycle i)
  have hnonnegative : ∀ i, 0 ≤ QuitProbability G (cycle i) := fun i =>
    (quitProbability_mem_Icc G (cycle i)).1
  have hblockMass : 0 < blockMass := by
    apply Finset.sum_pos' (fun i _ => hnonnegative i)
    rcases hpositive with ⟨i, hi⟩
    refine ⟨i, Finset.mem_range.mpr i.2, ?_⟩
    simpa [cycle, CycleProfile, Nat.mod_eq_of_lt i.2] using hi
  have hsum : ∀ m : ℕ,
      (∑ i ∈ Finset.range (m * k), QuitProbability G (cycle i)) = m * blockMass := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
      rw [Nat.succ_mul, Finset.sum_range_add, hm]
      have hperiod : ∀ i, cycle (m * k + i) = cycle i := by
        intro i
        simp only [cycle, CycleProfile]
        apply congrArg block
        apply Fin.ext
        simp [Nat.add_comm]
      simp_rw [hperiod]
      dsimp [blockMass]
      push_cast
      ring
  intro bound
  obtain ⟨m, hm⟩ := exists_nat_gt (bound / blockMass)
  refine ⟨m * k, ?_⟩
  rw [hsum]
  rw [div_lt_iff₀ hblockMass] at hm
  exact hm.le

/-- Theorem 3(ii): cyclic `ε`-rational `F_ε` tails with positive quit mass in the period. -/
def CyclicOrbitCondition (G : QuittingGame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (k : ℕ) (hk : 0 < k) (block : Fin k → QuitRow G),
    let p := CycleProfile G k hk block
    (∀ i, QuitTailPayoff G p i ∈ FRow G ε (QuitTailPayoff G p (i + 1))) ∧
    (∀ i, IsRational G ε (QuitTailPayoff G p i)) ∧
    ∃ i : Fin k, 0 < QuitProbability G (block i)

/-- The cyclic clause of Theorem 3 yields approximate equilibria via Proposition 3. -/
theorem CyclicOrbitCondition.hasQuitApproximateEquilibria
    (G : QuittingGame) (h : CyclicOrbitCondition G) : HasQuitApproximateEquilibria G := by
  intro target htarget
  rcases exists_quittingPayoffDifferenceBound G with ⟨M, hM⟩
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM.1
  let e : ℝ := min (target / 3) 1
  have he : 0 < e := lt_min (div_pos htarget (by norm_num)) zero_lt_one
  have he1 : e ≤ 1 := min_le_right _ _
  have h3e : 3 * e ≤ target := by
    have := min_le_left (target / 3) 1
    linarith
  let δ : ℝ := min (e / 2) (e ^ 4 / (4 * M ^ 3))
  have hδ : 0 < δ := lt_min (div_pos he (by norm_num))
    (div_pos (pow_pos he 4) (mul_pos (by norm_num) (pow_pos hMpos 3)))
  have hδε : δ ≤ e := (min_le_left _ _).trans (by linarith [he])
  have hδsmall : δ < e ^ 4 / (2 * M ^ 3) := by
    have hbound := min_le_right (e / 2) (e ^ 4 / (4 * M ^ 3))
    have hpow : 0 < M ^ 3 := pow_pos hMpos 3
    dsimp [δ]
    exact hbound.trans_lt (div_lt_div_of_pos_left (pow_pos he 4)
      (mul_pos (by norm_num) hpow) (by nlinarith))
  rcases h δ hδ with ⟨k, hk, block, horbit, hrational, hpositive⟩
  let profile := CycleProfile G k hk block
  have hequilibrium : IsQuitEpsilonEquilibrium G (3 * e) profile := by
    apply proposition3 G hM he he1 hδ hδsmall profile
    · intro i n
      exact le_trans (by linarith : MinMaxQuit G n - e ≤ MinMaxQuit G n - δ)
        (hrational i n)
    · exact CycleProfile.hasUnboundedQuitMass G hk block hpositive
    · exact horbit
  refine ⟨profile, ?_⟩
  intro n deviation
  exact (hequilibrium n deviation).trans (by linarith)

/-- A vector lies within `ε` of the feasible vectors. -/
def NearFeasible (G : QuittingGame) (ε : ℝ) (r : Payoff G.Player) : Prop :=
  ∃ z, Feasible G z ∧ ‖r - z‖ ≤ ε

/-- The total variation of a finite vector sequence. -/
def FiniteOrbitVariation {N : Type} [Fintype N] {k : ℕ}
    (x : Fin (k + 1) → Payoff N) : ℝ :=
  ∑ i : Fin k, ‖x i.succ - x i.castSucc‖

/-- Theorem 3(iii): arbitrarily large finite near-feasible, rational `F_ε` orbits. -/
def FiniteNearOrbitCondition (G : QuittingGame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ B : ℝ, 1 < B → ∃ (k : ℕ)
    (x : Fin (k + 1) → Payoff G.Player),
      IsFiniteOrbit (FRow G ε) x ∧
      (∀ i, IsRational G ε (x i) ∧ NearFeasible G ε (x i)) ∧
      B ≤ FiniteOrbitVariation x

/--
Unbounded variation of an infinite orbit uses finite partial sums, not a real `tsum`.
-/
def HasUnboundedVariation {N : Type} [Fintype N] (x : ℕ → Payoff N) : Prop :=
  ∀ B : ℝ, ∃ k, B ≤ ∑ i ∈ Finset.range k, ‖x (i + 1) - x i‖

/-- Theorem 3(iv): infinite `ε`-rational `F_ε` orbits of unbounded variation. -/
def InfiniteOrbitCondition (G : QuittingGame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x : ℕ → Payoff G.Player,
    IsInfiniteOrbit (FRow G ε) x ∧ (∀ i, IsRational G ε (x i)) ∧
      HasUnboundedVariation x

/-- Theorem 3(v): infinite extended `ε`-rational `F_ε` orbits of unbounded variation. -/
def ExtendedOrbitCondition (G : QuittingGame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x : ExtendedOrbitData (FRow G ε),
    (∀ j, ActiveSegment x.segmentCount j → ∀ i,
      SegmentIndex (x.segmentLength j) i → IsRational G ε (x.point j i)) ∧
    HasUnboundedExtendedVariation x

/-- Five propositions are equivalent when every pair in the displayed chain is equivalent. -/
def EquivalentFive (A B C D E : Prop) : Prop :=
  (A ↔ B) ∧ (B ↔ C) ∧ (C ↔ D) ∧ (D ↔ E)

/--
Theorem 3.  For a quitting game with neither stationary nor instant approximate equilibria,
clauses (i)--(v) are equivalent.
-/
theorem theorem3 (G : QuittingGame)
    (hstationary : ¬HasStationaryApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    EquivalentFive (HasQuitApproximateEquilibria G) (CyclicOrbitCondition G)
      (FiniteNearOrbitCondition G) (InfiniteOrbitCondition G) (ExtendedOrbitCondition G) := by
  sorry

/-!
The remark after Theorem 3 records that Solan--Vieille had proved `(iv) → (i),(ii)`
when every solo payoff is positive, and that Solan showed the minimal cycle length in
clause (ii) may depend on `ε`.
-/

/--
Lemma 6.  For normal players and `0 < ε ≤ 1`, an
`F_{ε²/(2M)}` step preserves `3ε`-rationality and otherwise raises the coordinate by
at least `ε²/(2M)`.
-/
theorem lemma6 (G : QuittingGame) {M ε : ℝ}
    (hM : IsQuittingPayoffDifferenceBound G M) (hnormal : ∀ n, IsNormalPlayer G n)
    (hstationary : ¬HasStationaryApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hε : 0 < ε) (hε1 : ε ≤ 1) {r s : Payoff G.Player}
    (hstep : s ∈ FRow G (ε ^ 2 / (2 * M)) r) :
    ∀ n,
      (r n ≥ MinMaxQuit G n - 3 * ε → s n ≥ MinMaxQuit G n - 3 * ε) ∧
      (r n < MinMaxQuit G n - 3 * ε → s n ≥ r n + ε ^ 2 / (2 * M)) := by
  sorry

/-- A scalar process with positive drift below a preserved threshold eventually stays above it. -/
theorem eventually_ge_of_drift_below {u : ℕ → ℝ} {threshold step : ℝ}
    (hstep : 0 < step)
    (h : ∀ i, (threshold ≤ u i → threshold ≤ u (i + 1)) ∧
      (u i < threshold → u i + step ≤ u (i + 1))) :
    ∃ N, ∀ i, N ≤ i → threshold ≤ u i := by
  have hpersist : ∀ {i}, threshold ≤ u i → ∀ j, i ≤ j → threshold ≤ u j := by
    intro i hi j hij
    induction j, hij using Nat.le_induction with
    | base => exact hi
    | succ j hij hj => exact (h j).1 hj
  by_cases hreach : ∃ i, threshold ≤ u i
  · rcases hreach with ⟨i, hi⟩
    exact ⟨i, hpersist hi⟩
  · push Not at hreach
    have hgrowth : ∀ i, u 0 + i * step ≤ u i := by
      intro i
      induction i with
      | zero => simp
      | succ i hi =>
        have hdrift := (h i).2 (hreach i)
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith
    obtain ⟨N, hN⟩ := exists_nat_gt ((threshold - u 0) / step)
    have hlarge : threshold < u 0 + N * step := by
      rw [div_lt_iff₀ hstep] at hN
      nlinarith
    nlinarith [hgrowth N, hreach N, hlarge]

/-- Removing a finite prefix preserves unbounded total variation. -/
theorem HasUnboundedVariation.tail {N : Type} [Fintype N]
    {x : ℕ → Payoff N} (h : HasUnboundedVariation x) (start : ℕ) :
    HasUnboundedVariation (fun i => x (start + i)) := by
  intro bound
  let increment : ℕ → ℝ := fun i => ‖x (i + 1) - x i‖
  let prefixVariation : ℝ := ∑ i ∈ Finset.range start, increment i
  rcases h (bound + prefixVariation) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hmono : (∑ i ∈ Finset.range k, increment i) ≤
      ∑ i ∈ Finset.range (start + k), increment i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.le_add_left k start))
    intro i _ _
    exact norm_nonneg _
  have hbound := hk.trans hmono
  rw [Finset.sum_range_add] at hbound
  dsimp [prefixVariation, increment] at hbound ⊢
  simp only [Nat.add_assoc] at hbound
  simpa [Nat.add_assoc] using (show bound ≤
    ∑ i ∈ Finset.range k, ‖x (start + (i + 1)) - x (start + i)‖ by
      linarith)

/-- The unqualified infinite-orbit condition used in Corollary 2. -/
def InfiniteUnrestrictedOrbitCondition (G : QuittingGame) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ x : ℕ → Payoff G.Player,
    IsInfiniteOrbit (FRow G δ) x ∧ HasUnboundedVariation x

/--
Corollary 2.  If all players are normal and there are neither instant nor stationary
approximate equilibria, existence is equivalent to an unbounded `F_δ` orbit for every `δ>0`.
-/
theorem corollary2 (G : QuittingGame) (hnormal : ∀ n, IsNormalPlayer G n)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hstationary : ¬HasStationaryApproximateEquilibria G) :
    HasQuitApproximateEquilibria G ↔ InfiniteUnrestrictedOrbitCondition G := by
  have hfive := theorem3 G hstationary hinstant
  have hEquiv : HasQuitApproximateEquilibria G ↔ InfiniteOrbitCondition G :=
    hfive.1.trans (hfive.2.1.trans hfive.2.2.1)
  constructor
  · intro hequilibrium δ hδ
    rcases hEquiv.mp hequilibrium δ hδ with ⟨x, horbit, _hrational, hvariation⟩
    exact ⟨x, horbit, hvariation⟩
  · intro hunrestricted
    apply hEquiv.mpr
    intro ε hε
    rcases exists_quittingPayoffDifferenceBound G with ⟨M, hM⟩
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM.1
    let a : ℝ := min (ε / 3) (1 / 2)
    have ha : 0 < a := lt_min (div_pos hε (by norm_num)) (by norm_num)
    have ha1 : a ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
    have h3a : 3 * a ≤ ε := by
      have := min_le_left (ε / 3) (1 / 2)
      linarith
    let δ : ℝ := a ^ 2 / (2 * M)
    have hδ : 0 < δ := div_pos (sq_pos_of_pos ha) (mul_pos (by norm_num) hMpos)
    have hδε : δ ≤ ε := by
      rw [div_le_iff₀ (mul_pos (by norm_num) hMpos)]
      have haHalf := min_le_right (ε / 3) (1 / 2)
      have haEps := min_le_left (ε / 3) (1 / 2)
      nlinarith [sq_nonneg a, hM.1]
    rcases hunrestricted δ hδ with ⟨x, horbit, hvariation⟩
    have heventual : ∀ n : G.Player, ∃ cutoff, ∀ i, cutoff ≤ i →
        MinMaxQuit G n - 3 * a ≤ x i n := by
      intro n
      apply eventually_ge_of_drift_below hδ
      intro i
      exact lemma6 G hM hnormal hstationary hinstant ha ha1 (horbit i) n
    choose cutoff hcutoff using heventual
    let start := ∑ n, cutoff n
    have hcutoffStart : ∀ n, cutoff n ≤ start := by
      intro n
      exact Finset.single_le_sum (fun i _ => Nat.zero_le (cutoff i)) (Finset.mem_univ n)
    let y : ℕ → Payoff G.Player := fun i => x (start + i)
    refine ⟨y, ?_, ?_, ?_⟩
    · intro i
      apply FRow.mono G hδε
      simpa [y, Nat.add_assoc] using horbit (start + i)
    · intro i n
      have hfloor := hcutoff n (start + i)
        ((hcutoffStart n).trans (Nat.le_add_right start i))
      dsimp [y]
      linarith
    · exact hvariation.tail start

/-! ## 5. Escape games -/

/-- `W = {r | rʲ ≤ vʲ for some player j}`. -/
def WSet (G : QuittingGame) : Set (Payoff G.Player) :=
  {r | ∃ j, r j ≤ SoloPayoff G j}

/-- The closed line segment joining two payoff vectors. -/
def PayoffSegment (G : QuittingGame) (x y : Payoff G.Player) :
    Set (Payoff G.Player) :=
  segment ℝ x y

/--
The witness `Q,ē` in the definition of an escape game, including near-feasibility,
boundary escape along actual line segments, strict `F₀` escape, and `F_ē` closure.
-/
structure EscapeWitness (G : QuittingGame) where
  Q : Set (Payoff G.Player)
  ebar : ℝ
  ebar_positive : 0 < ebar
  Q_closed : IsClosed Q
  nearFeasible : ∀ x ∈ Q, ∃ z, Feasible G z ∧ ‖x - z‖ ≤ 1
  meetsBoundary : (Q ∩ frontier (WSet G)).Nonempty
  boundaryEscape : ∀ x ∈ Q ∩ frontier (WSet G), ∃ y,
    (∀ j, y j > SoloPayoff G j) ∧ PayoffSegment G x y ⊆ Q
  strictEscape : ∀ x ∈ Q \ WSet G, ∀ y ∈ FRow G 0 x, y ≠ x →
    ∀ j, y j > SoloPayoff G j + ebar
  closedUnder : ∀ x ∈ Q, ∀ y ∈ FRow G ebar x, y ∈ Q

/-- A quitting game is an escape game when all players are normal and an escape witness exists. -/
def IsEscapeGame (G : QuittingGame) : Prop :=
  (∀ n, IsNormalPlayer G n) ∧ Nonempty (EscapeWitness G)

/-! ### 5.2. The spanning property -/

/-- The paper writes `C̄` for the topological closure of `C`. -/
abbrev TopologicalClosure {X : Type} [TopologicalSpace X] (C : Set X) :=
  closure C

/-- The paper writes `∂C` for the topological boundary of `C`. -/
abbrev TopologicalBoundary {X : Type} [TopologicalSpace X] (C : Set X) :=
  frontier C

/--
A compact `n`-manifold with boundary is locally modeled by the closed `n`-disk, with the
marked point sent either to its interior center or to its sphere boundary.
-/
def IsCompactManifoldWithBoundary {n : ℕ} (C : Set (Fin n → ℝ)) : Prop :=
  IsCompact C ∧ ∀ x ∈ C, ∃ (V : Set (Fin n → ℝ)) (hxV : x ∈ V), V ⊆ C ∧
    ∃ e : V ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1,
      e ⟨x, hxV⟩ = ⟨0, by simp⟩ ∨ ‖(e ⟨x, hxV⟩ : Fin n → ℝ)‖ = 1

/-- The boundary inclusion into the ambient Euclidean space with an interior point removed. -/
def BoundaryToPunctured {n : ℕ} (C : Set (Fin n → ℝ)) (x : Fin n → ℝ)
    (hx : x ∉ frontier C) : C(frontier C, {y : Fin n → ℝ // y ≠ x}) where
  toFun y := ⟨y, fun hy => hx (hy ▸ y.2)⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/--
A paper-local reduced Cech-homology functor with coefficients in a nontrivial compact
Abelian group.  Its maps are functorial continuous-map induced homomorphisms.
-/
structure CechHomologyCore where
  Coeff : Type
  [coeffGroup : AddCommGroup Coeff]
  [coeffTopology : TopologicalSpace Coeff]
  [coeffTopologicalGroup : IsTopologicalAddGroup Coeff]
  [coeffCompact : CompactSpace Coeff]
  [coeffNontrivial : Nontrivial Coeff]
  fundamentalCoefficient : Coeff
  fundamentalCoefficient_ne_zero : fundamentalCoefficient ≠ 0
  reduced : (d : ℕ) → (X : Type) → [TopologicalSpace X] → AddCommGrpCat
  fundamentalBoundaryClass : ∀ {n : ℕ} (C : Set (Fin n → ℝ)),
    IsCompactManifoldWithBoundary C → reduced (n - 1) (frontier C)
  fundamentalBoundaryClass_ne_zero : ∀ {n : ℕ} (C : Set (Fin n → ℝ))
    (hC : IsCompactManifoldWithBoundary C), fundamentalBoundaryClass C hC ≠ 0
  induced : ∀ {d : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y],
    C(X, Y) → (reduced d X ⟶ reduced d Y)
  map_id : ∀ (d : ℕ) (X : Type) [tX : TopologicalSpace X],
    @induced d X X tX tX (ContinuousMap.id X) = 𝟙 (reduced d X)
  map_comp : ∀ {d : ℕ} {X Y Z : Type} [tX : TopologicalSpace X]
    [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)),
      @induced d X Z tX tZ (g.comp f) =
        @induced d X Y tX tY f ≫ @induced d Y Z tY tZ g
  /-- The boundary fundamental class remains nonzero after deleting an interior point. -/
  puncturedBoundaryClass_ne_zero : ∀ {n : ℕ} (C : Set (Fin n → ℝ))
    (hC : IsCompactManifoldWithBoundary C) (x : Fin n → ℝ), x ∈ C →
      (hx : x ∉ frontier C) →
      (induced (BoundaryToPunctured C x hx)).hom (fundamentalBoundaryClass C hC) ≠ 0

attribute [instance] CechHomologyCore.coeffGroup
attribute [instance] CechHomologyCore.coeffTopology
attribute [instance] CechHomologyCore.coeffTopologicalGroup
attribute [instance] CechHomologyCore.coeffCompact
attribute [instance] CechHomologyCore.coeffNontrivial

/-- The graph of a correspondence as a topological subspace of the product. -/
abbrev CorrespondenceGraph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : Correspondence X Y) :=
  {p : X × Y // p.2 ∈ F p.1}

/-- The graph of a correspondence restricted over a subset of its domain. -/
abbrev RestrictedGraph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : Correspondence X Y) (A : Set X) :=
  {p : CorrespondenceGraph F // p.1.1 ∈ A}

/-- The oriented nonzero boundary fundamental class in reduced degree `n-1`. -/
structure BoundaryClassData (H : CechHomologyCore) {n : ℕ}
    (C : Set (Fin n → ℝ)) where
  manifold : IsCompactManifoldWithBoundary C
  boundaryClass : H.reduced (n - 1) (frontier C)
  isFundamental : boundaryClass = H.fundamentalBoundaryClass C manifold

/--
The class `z ∈ H̃_{n-1}(F|∂Ū)` witnessing the spanning property, with the
projection and inclusion maps and their two required homology equations.
-/
structure SpanningWitness (H : CechHomologyCore) {n : ℕ} {Y : Type}
    [TopologicalSpace Y] (F : Correspondence (Fin n → ℝ) Y)
    (U : Set (Fin n → ℝ)) (boundary : BoundaryClassData H (closure U)) where
  projection : C(RestrictedGraph F (frontier (closure U)), frontier (closure U))
  projection_eq : ∀ p, (projection p : Fin n → ℝ) = p.1.1.1
  inclusion : C(RestrictedGraph F (frontier (closure U)), CorrespondenceGraph F)
  inclusion_eq : ∀ p, inclusion p = p.1
  cycle : H.reduced (n - 1) (RestrictedGraph F (frontier (closure U)))
  projection_cycle : (H.induced projection).hom cycle = boundary.boundaryClass
  inclusion_cycle : (H.induced inclusion).hom cycle = 0

/--
A compact correspondence has the spanning property for nonempty open bounded `U` when
its restricted boundary graph carries Simon's Cech-homology witness.
-/
def SpanningProperty (H : CechHomologyCore) {n : ℕ} {Y : Type}
    [TopologicalSpace Y] (F : Correspondence (Fin n → ℝ) Y)
    (U : Set (Fin n → ℝ)) : Prop :=
  U.Nonempty ∧ IsOpen U ∧ Bornology.IsBounded U ∧
    IsCompact {p : (Fin n → ℝ) × Y | p.2 ∈ F p.1} ∧
    ∃ boundary : BoundaryClassData H (closure U),
      Nonempty (SpanningWitness H F U boundary)

/-- A spanning correspondence has a nonempty fiber over every point of `U`. -/
theorem spanning_has_nonempty_fiber (H : CechHomologyCore) {n : ℕ} {Y : Type}
    [TopologicalSpace Y] (F : Correspondence (Fin n → ℝ) Y)
    (U : Set (Fin n → ℝ)) (h : SpanningProperty H F U) :
    ∀ x ∈ U, (F x).Nonempty := by
  rintro x hxU
  rcases h with ⟨_hU, hUopen, _hUbounded, _hGraphCompact, boundary, ⟨witness⟩⟩
  have hxClosure : x ∈ closure U := subset_closure hxU
  have hxInterior : x ∈ interior (closure U) := by
    rw [mem_interior_iff_mem_nhds]
    exact mem_of_superset (hUopen.mem_nhds hxU) subset_closure
  have hxNotFrontier : x ∉ frontier (closure U) := by
    rw [frontier]
    exact fun hx => hx.2 hxInterior
  by_contra hxFiber
  have hgraphAvoids : ∀ p : CorrespondenceGraph F, p.1.1 ≠ x := by
    intro p hp
    apply hxFiber
    refine ⟨p.1.2, ?_⟩
    simpa [hp] using p.2
  let graphProjection :
      C(CorrespondenceGraph F, {y : Fin n → ℝ // y ≠ x}) :=
    { toFun := fun p => ⟨p.1.1, hgraphAvoids p⟩
      continuous_toFun :=
        (continuous_fst.comp continuous_subtype_val).subtype_mk hgraphAvoids }
  let boundaryProjection := BoundaryToPunctured (closure U) x hxNotFrontier
  have hmaps : graphProjection.comp witness.inclusion =
      boundaryProjection.comp witness.projection := by
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    funext i
    change (witness.inclusion p).1.1 i = (witness.projection p : Fin n → ℝ) i
    rw [witness.inclusion_eq, witness.projection_eq]
  have hzero :
      (H.induced (graphProjection.comp witness.inclusion)).hom witness.cycle = 0 := by
    rw [H.map_comp]
    simp [witness.inclusion_cycle]
  have hnonzero :
      (H.induced (boundaryProjection.comp witness.projection)).hom witness.cycle ≠ 0 := by
    rw [H.map_comp]
    change (H.induced boundaryProjection).hom
      ((H.induced witness.projection).hom witness.cycle) ≠ 0
    rw [witness.projection_cycle]
    rw [boundary.isFundamental]
    exact H.puncturedBoundaryClass_ne_zero (closure U) boundary.manifold x hxClosure
      hxNotFrontier
  rw [hmaps] at hzero
  exact hnonzero hzero

/-- Two graph points lie in the same connected component of `F|C`. -/
def SameGraphComponent {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : Correspondence X Y) (C : Set X) (p q : X × Y) : Prop :=
  ∃ K : Set (X × Y), _root_.IsConnected K ∧ p ∈ K ∧ q ∈ K ∧
    ∀ z ∈ K, z.1 ∈ C ∧ z.2 ∈ F z.1

/--
The Čech theory used by Simon, including the compact connected restriction theorem
quoted from Simon--Spież--Toruńczyk.  The core records functoriality and the punctured
fundamental-class fact; this additional field is the precise external continuity result
needed for Lemma 7.
-/
structure CechHomologyTheory extends CechHomologyCore where
  compactConnectedRestriction : ∀ {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (F : Correspondence (Fin n → ℝ) Y) (U C : Set (Fin n → ℝ)),
      SpanningProperty toCechHomologyCore F U →
      _root_.IsConnected C → IsCompact C → C ⊆ U →
      ∃ K : Set ((Fin n → ℝ) × Y),
        _root_.IsConnected K ∧
        (∀ z ∈ K, z.1 ∈ C ∧ z.2 ∈ F z.1) ∧
        ∀ x ∈ C, ∃ y, (x, y) ∈ K

instance : Coe CechHomologyTheory CechHomologyCore :=
  ⟨CechHomologyTheory.toCechHomologyCore⟩

/--
Lemma 7.  If `F` spans an open bounded `U` and `C ⊆ U` is compact connected, then
fibers over any `x,y ∈ C` contain points in one connected component of `F|C`.
-/
theorem lemma7 (H : CechHomologyTheory) {n : ℕ} {Y : Type}
    [TopologicalSpace Y] (F : Correspondence (Fin n → ℝ) Y)
    (U C : Set (Fin n → ℝ)) (hspan : SpanningProperty H F U)
    (hC : _root_.IsConnected C ∧ IsCompact C) (hCU : C ⊆ U) :
    ∀ x ∈ C, ∀ y ∈ C, ∃ z₁ ∈ F x, ∃ z₂ ∈ F y,
      SameGraphComponent F C (x, z₁) (y, z₂) := by
  rcases H.compactConnectedRestriction F U C hspan hC.1 hC.2 hCU with
    ⟨K, hKconnected, hKgraph, hKfiber⟩
  intro x hx y hy
  rcases hKfiber x hx with ⟨z₁, hz₁⟩
  rcases hKfiber y hy with ⟨z₂, hz₂⟩
  exact ⟨z₁, (hKgraph (x, z₁) hz₁).2, z₂, (hKgraph (y, z₂) hz₂).2,
    K, hKconnected, hz₁, hz₂, hKgraph⟩

/--
The Brouwer illustration: a disk self-map fixing its boundary is surjective; likewise the
two projections of the diagonal-boundary correspondence described in the paper span the disk.
-/
def BrouwerSpanningIllustration (n : ℕ) : Prop :=
  ∀ f : Metric.closedBall (0 : Fin n → ℝ) 1 →
      Metric.closedBall (0 : Fin n → ℝ) 1,
    Continuous f →
    (∀ x : Metric.closedBall (0 : Fin n → ℝ) 1,
      ‖(x : Fin n → ℝ)‖ = 1 → f x = x) → Function.Surjective f

/-- The first-coordinate correspondence carried by the image of a disk map into a product. -/
def FirstImageCorrespondence {n : ℕ}
    (f : Metric.closedBall (0 : Fin n → ℝ) 1 →
      (Fin n → ℝ) × (Fin n → ℝ)) :
    Correspondence (Fin n → ℝ) (Fin n → ℝ) :=
  fun x => {y | ∃ z, f z = (x, y)}

/-- The second-coordinate correspondence carried by the same disk-map image. -/
def SecondImageCorrespondence {n : ℕ}
    (f : Metric.closedBall (0 : Fin n → ℝ) 1 →
      (Fin n → ℝ) × (Fin n → ℝ)) :
    Correspondence (Fin n → ℝ) (Fin n → ℝ) :=
  fun y => {x | ∃ z, f z = (x, y)}

/--
The second Brouwer illustration: a continuous disk map equal to `(x,x)` on the sphere has
an image correspondence spanning the open disk in either coordinate.
-/
def DiagonalBoundarySpanningIllustration (H : CechHomologyTheory) (n : ℕ) : Prop :=
  ∀ f : Metric.closedBall (0 : Fin n → ℝ) 1 →
      (Fin n → ℝ) × (Fin n → ℝ),
    Continuous f →
    (∀ x : Metric.closedBall (0 : Fin n → ℝ) 1,
      ‖(x : Fin n → ℝ)‖ = 1 →
        f x = ((x : Fin n → ℝ), (x : Fin n → ℝ))) →
    SpanningProperty H (FirstImageCorrespondence f) (Metric.ball 0 1) ∧
      SpanningProperty H (SecondImageCorrespondence f) (Metric.ball 0 1)

/-! ### 5.3. The structure theorem -/

/-- A homotopy is a continuous map `X × [0,1] → Y`. -/
def IsHomotopy {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X → Set.Icc (0 : ℝ) 1 → Y) : Prop :=
  Continuous fun p : X × Set.Icc (0 : ℝ) 1 => h p.1 p.2

/-- A homotopy in a real vector space is straight-line when it interpolates its endpoints. -/
def IsStraightLineHomotopy {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup Y] [Module ℝ Y] (h : X → Set.Icc (0 : ℝ) 1 → Y) : Prop :=
  IsHomotopy h ∧ ∀ x t,
    h x t = (t : ℝ) • h x 1 + (1 - (t : ℝ)) • h x 0

/-- Finite players and finite nonempty action sets for one-shot matrix games. -/
structure MatrixGameForm where
  Player : Type
  [finitePlayer : Fintype Player]
  [nonemptyPlayer : Nonempty Player]
  Action : Player → Type
  [finiteAction : ∀ n, Fintype (Action n)]
  [nonemptyAction : ∀ n, Nonempty (Action n)]

attribute [instance] MatrixGameForm.finitePlayer
attribute [instance] MatrixGameForm.nonemptyPlayer
attribute [instance] MatrixGameForm.finiteAction
attribute [instance] MatrixGameForm.nonemptyAction

/-- `X` is the finite-dimensional space of payoff matrices with vector entries. -/
abbrev MatrixParameterSpace (D : MatrixGameForm) :=
  ((n : D.Player) → D.Action n) → Payoff D.Player

/-- `Ã = ∏_j Δ(Aʲ)` is the product of actual finite mixed-strategy simplices. -/
abbrev MixedStrategySpace (D : MatrixGameForm) :=
  (n : D.Player) → stdSimplex ℝ (D.Action n)

/-- The probability of a pure action profile under a mixed-strategy profile. -/
def PureProfileProbability (D : MatrixGameForm) (p : MixedStrategySpace D)
    (a : (n : D.Player) → D.Action n) : ℝ :=
  ∏ n, (p n : D.Action n → ℝ) (a n)

/-- The expected matrix-game payoff of a mixed-strategy profile. -/
def MatrixExpectedPayoff (D : MatrixGameForm) (x : MatrixParameterSpace D)
    (p : MixedStrategySpace D) : Payoff D.Player := by
  classical
  exact fun n => ∑ a, PureProfileProbability D p a * x a n

/-- Unilateral replacement in the product mixed-strategy simplex. -/
def MixedStrategySpace.replace (D : MatrixGameForm) (p : MixedStrategySpace D)
    (n : D.Player) (q : stdSimplex ℝ (D.Action n)) : MixedStrategySpace D := by
  classical
  exact fun k => if h : k = n then h ▸ q else p k

/-- A mixed profile is a Nash equilibrium of the one-stage matrix game `G_x`. -/
def IsMatrixNash (D : MatrixGameForm) (x : MatrixParameterSpace D)
    (p : MixedStrategySpace D) : Prop :=
  ∀ n (q : stdSimplex ℝ (D.Action n)),
    MatrixExpectedPayoff D x (p.replace D n q) n ≤ MatrixExpectedPayoff D x p n

/-- `E ⊆ X × Ã` is the equilibrium correspondence of all payoff matrices. -/
def MatrixEquilibriumCorrespondence (D : MatrixGameForm) :
    Correspondence (MatrixParameterSpace D) (MixedStrategySpace D) :=
  fun x => {p | IsMatrixNash D x p}

/-- The graph of the matrix equilibrium correspondence as a subset of `X × Ã`. -/
def MatrixEquilibriumGraph (D : MatrixGameForm) :
    Set (MatrixParameterSpace D × MixedStrategySpace D) :=
  {p | p.2 ∈ MatrixEquilibriumCorrespondence D p.1}

/-- A concrete norm on the finite-dimensional matrix parameter space. -/
def MatrixNorm (D : MatrixGameForm) (x : MatrixParameterSpace D) : ℝ := by
  classical
  exact ∑ a, ∑ n, |x a n|

/--
The Kohlberg--Mertens structure theorem in the modified form recalled by Simon: a
straight-line homotopy starts over each `x`, ends with image exactly `E`, and escapes over
every compact base set uniformly in `t` as `‖x‖ → ∞`.
-/
def KohlbergMertensStatement : Prop :=
  ∀ D : MatrixGameForm, ∃ H : MatrixParameterSpace D →
    Set.Icc (0 : ℝ) 1 → MatrixParameterSpace D × MixedStrategySpace D,
    IsHomotopy H ∧
    (∀ x t,
      (H x t).1 = (t : ℝ) • (H x 1).1 + (1 - (t : ℝ)) • (H x 0).1 ∧
      ∀ n a, ((H x t).2 n : D.Action n → ℝ) a =
        (t : ℝ) * ((H x 1).2 n : D.Action n → ℝ) a +
        (1 - (t : ℝ)) * ((H x 0).2 n : D.Action n → ℝ) a) ∧
    (∀ x, (H x 0).1 = x) ∧
    range (fun x => H x 1) = MatrixEquilibriumGraph D ∧
    ∀ C : Set (MatrixParameterSpace D), IsCompact C → ∃ R : ℝ, 0 < R ∧
      ∀ x, R < MatrixNorm D x → ∀ t, (H x t).1 ∉ C

/-- The Kohlberg--Mertens structure theorem recalled in Section 5.3. -/
theorem kohlbergMertensStructureTheorem : KohlbergMertensStatement := by
  sorry

/-! ### 5.4. Finitely repeated quitting games -/

/-- A behavioral profile in the `k`-stage quitting game `Γ_x^k`. -/
abbrev RepeatedQuitProfile (G : QuittingGame) (k : ℕ) := Fin k → QuitRow G

/-- The recursive expected payoff `f^k(x,p)` of the `k`-stage quitting game. -/
def RepeatedPayoff (G : QuittingGame) :
    (k : ℕ) → Payoff G.Player → RepeatedQuitProfile G k → Payoff G.Player
  | 0, x, _ => x
  | k + 1, x, p =>
      QuittingOneStagePayoff G
        (RepeatedPayoff G k x fun i => p i.succ) (p 0)

/-- Unilateral replacement in a finite repeated quitting profile. -/
def RepeatedQuitProfile.replace (G : QuittingGame) {k : ℕ}
    (p : RepeatedQuitProfile G k) (n : G.Player)
    (q : Fin k → Set.Icc (0 : ℝ) 1) : RepeatedQuitProfile G k := by
  classical
  exact fun i j => if j = n then q i else p i j

/-- `E^k(x)` is the equilibrium correspondence of the finitely repeated games `Γ_x^k`. -/
def RepeatedEquilibriumCorrespondence (G : QuittingGame) (k : ℕ) :
    Correspondence (Payoff G.Player) (RepeatedQuitProfile G k) :=
  fun x => {p | ∀ n (q : Fin k → Set.Icc (0 : ℝ) 1),
    RepeatedPayoff G k x (p.replace G n q) n ≤ RepeatedPayoff G k x p n}

/-- `F^k(x) = {f^k(x,p) | p ∈ E^k(x)}`. -/
def RepeatedF (G : QuittingGame) (k : ℕ) :
    Correspondence (Payoff G.Player) (Payoff G.Player) :=
  fun x => {RepeatedPayoff G k x p | p ∈ RepeatedEquilibriumCorrespondence G k x}

/-- The `k`-fold iteration of a correspondence. -/
def Correspondence.iterate {X : Type} (F : Correspondence X X) :
    ℕ → Correspondence X X
  | 0 => fun x => {x}
  | k + 1 => fun x => ⋃ y ∈ F x, F.iterate k y

/-- A player's mixed quitting probability makes each coalition probability affine. -/
theorem coalitionProbability_replace_affine (G : QuittingGame) (p : QuitRow G)
    (n : G.Player) (q : Set.Icc (0 : ℝ) 1) (A : Finset G.Player) :
    CoalitionProbability G (p.replace G n q) A =
      (q : ℝ) * CoalitionProbability G (p.replace G n 1) A +
        (1 - (q : ℝ)) * CoalitionProbability G (p.replace G n 0) A := by
  classical
  have hprod_mem (s : Finset G.Player) (hs : n ∈ s)
      (a : Set.Icc (0 : ℝ) 1) :
      (∏ x ∈ s, (↑(if x = n then a else p x) : ℝ)) =
        (a : ℝ) * ∏ x ∈ s.erase n, (p x : ℝ) := by
    calc
      _ = (↑(if n = n then a else p n) : ℝ) *
          ∏ x ∈ s.erase n, (↑(if x = n then a else p x) : ℝ) :=
        (Finset.mul_prod_erase s
          (fun x => (↑(if x = n then a else p x) : ℝ)) hs).symm
      _ = _ := by
        simp only [if_pos]
        congr 1
        apply Finset.prod_congr rfl
        intro x hx
        simp [Finset.mem_erase.mp hx |>.1]
  have hprod_not_mem (s : Finset G.Player) (hs : n ∉ s)
      (a : Set.Icc (0 : ℝ) 1) :
      (∏ x ∈ s, (↑(if x = n then a else p x) : ℝ)) =
        ∏ x ∈ s, (p x : ℝ) := by
    apply Finset.prod_congr rfl
    intro x hx
    by_cases hxn : x = n
    · exact (hs (hxn ▸ hx)).elim
    · simp [hxn]
  have hcprod_mem (s : Finset G.Player) (hs : n ∈ s)
      (a : Set.Icc (0 : ℝ) 1) :
      (∏ x ∈ s, (1 - (↑(if x = n then a else p x) : ℝ))) =
        (1 - (a : ℝ)) * ∏ x ∈ s.erase n, (1 - (p x : ℝ)) := by
    calc
      _ = (1 - (↑(if n = n then a else p n) : ℝ)) *
          ∏ x ∈ s.erase n, (1 - (↑(if x = n then a else p x) : ℝ)) :=
        (Finset.mul_prod_erase s
          (fun x => 1 - (↑(if x = n then a else p x) : ℝ)) hs).symm
      _ = _ := by
        simp only [if_pos]
        congr 1
        apply Finset.prod_congr rfl
        intro x hx
        simp [Finset.mem_erase.mp hx |>.1]
  have hcprod_not_mem (s : Finset G.Player) (hs : n ∉ s)
      (a : Set.Icc (0 : ℝ) 1) :
      (∏ x ∈ s, (1 - (↑(if x = n then a else p x) : ℝ))) =
        ∏ x ∈ s, (1 - (p x : ℝ)) := by
    apply Finset.prod_congr rfl
    intro x hx
    by_cases hxn : x = n
    · exact (hs (hxn ▸ hx)).elim
    · simp [hxn]
  by_cases hnA : n ∈ A
  · have hncomp : n ∉ Finset.univ.filter (fun x => x ∉ A) := by simp [hnA]
    simp only [CoalitionProbability, QuitRow.replace]
    rw [hprod_mem A hnA, hprod_mem A hnA, hprod_mem A hnA]
    rw [hcprod_not_mem _ hncomp, hcprod_not_mem _ hncomp, hcprod_not_mem _ hncomp]
    norm_num
    ring
  · have hncomp : n ∈ Finset.univ.filter (fun x => x ∉ A) := by simp [hnA]
    simp only [CoalitionProbability, QuitRow.replace]
    rw [hprod_not_mem A hnA, hprod_not_mem A hnA, hprod_not_mem A hnA]
    rw [hcprod_mem _ hncomp, hcprod_mem _ hncomp, hcprod_mem _ hncomp]
    norm_num
    ring

/-- Every exact-quitter coalition has nonnegative probability. -/
theorem coalitionProbability_nonneg (G : QuittingGame) (p : QuitRow G)
    (A : Finset G.Player) : 0 ≤ CoalitionProbability G p A := by
  classical
  simp only [CoalitionProbability]
  apply mul_nonneg
  · exact Finset.prod_nonneg fun n _ => (p n).property.1
  · exact Finset.prod_nonneg fun n _ => sub_nonneg.mpr (p n).property.2

/-- Exact-quitter coalition probabilities sum to one. -/
theorem coalitionProbability_sum (G : QuittingGame) (p : QuitRow G) :
    ∑ A ∈ Finset.univ.powerset, CoalitionProbability G p A = 1 := by
  classical
  simp only [CoalitionProbability]
  have hcomp : ∀ A : Finset G.Player,
      Finset.univ.filter (fun n => n ∉ A) = Finset.univ \ A := by
    intro A
    ext n
    simp
  simp_rw [hcomp]
  rw [← Finset.prod_add (fun n => (p n : ℝ))
    (fun n => 1 - (p n : ℝ)) Finset.univ]
  simp

/-- The total probability of nonempty quitting coalitions lies in `[0,1]`. -/
theorem nonemptyCoalitionProbability_sum_mem_Icc (G : QuittingGame) (p : QuitRow G) :
    (∑ A ∈ Finset.univ.powerset, if A.Nonempty then CoalitionProbability G p A else 0) ∈
      Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun A _ => by
      split_ifs
      · exact coalitionProbability_nonneg G p A
      · exact le_rfl
  · calc
      (∑ A ∈ Finset.univ.powerset,
          if A.Nonempty then CoalitionProbability G p A else 0) ≤
          ∑ A ∈ Finset.univ.powerset, CoalitionProbability G p A := by
        apply Finset.sum_le_sum
        intro A hA
        split_ifs
        · exact le_rfl
        · exact coalitionProbability_nonneg G p A
      _ = 1 := coalitionProbability_sum G p

/-- The expected contribution of nonempty coalitions stays within a uniform payoff bound. -/
theorem quittingRewardPart_mem_Icc (G : QuittingGame) (p : QuitRow G)
    (n : G.Player) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ A, |G.reward A n| ≤ M) :
    (∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
      CoalitionProbability G p A * G.reward ⟨A, hA⟩ n else 0) ∈ Set.Icc (-M) M := by
  let mass : ℝ := ∑ A ∈ Finset.univ.powerset,
    if A.Nonempty then CoalitionProbability G p A else 0
  have hmass := nonemptyCoalitionProbability_sum_mem_Icc G p
  change mass ∈ Set.Icc (0 : ℝ) 1 at hmass
  constructor
  · calc
      -M ≤ -M * mass := by
        simpa using mul_le_mul_of_nonpos_left hmass.2 (neg_nonpos.mpr hM)
      _ = ∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
          CoalitionProbability G p A * (-M) else 0 := by
        simp only [mass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A hA
        split_ifs <;> ring
      _ ≤ ∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
          CoalitionProbability G p A * G.reward ⟨A, hA⟩ n else 0 := by
        apply Finset.sum_le_sum
        intro A hA
        split_ifs with hnonempty
        · apply mul_le_mul_of_nonneg_left
          · exact (neg_le_of_abs_le (hbound ⟨A, hnonempty⟩))
          · exact coalitionProbability_nonneg G p A
        · exact le_rfl
  · calc
      (∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
          CoalitionProbability G p A * G.reward ⟨A, hA⟩ n else 0) ≤
          ∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
            CoalitionProbability G p A * M else 0 := by
        apply Finset.sum_le_sum
        intro A hA
        split_ifs with hnonempty
        · apply mul_le_mul_of_nonneg_left
          · exact (le_of_abs_le (hbound ⟨A, hnonempty⟩))
          · exact coalitionProbability_nonneg G p A
        · exact le_rfl
      _ = M * mass := by
        simp only [mass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A hA
        split_ifs <;> ring
      _ ≤ M := by nlinarith [mul_le_mul_of_nonneg_left hmass.2 hM]

/-- A nonempty coalition has zero probability in the all-continue row. -/
theorem coalitionProbability_zero_of_nonempty (G : QuittingGame)
    (A : Finset G.Player) (hA : A.Nonempty) :
    CoalitionProbability G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) A = 0 := by
  classical
  simp only [CoalitionProbability]
  rcases hA with ⟨n, hn⟩
  have hprod : (∏ i ∈ A, (((fun _ => (0 : Set.Icc (0 : ℝ) 1)) i : ℝ))) = 0 := by
    apply Finset.prod_eq_zero hn
    norm_num
  rw [hprod, zero_mul]

/-- If every player continues, the one-stage payoff is the continuation vector. -/
theorem quittingOneStagePayoff_zero (G : QuittingGame) (r : Payoff G.Player) :
    QuittingOneStagePayoff G r (fun _ => (0 : Set.Icc (0 : ℝ) 1)) = r := by
  funext n
  simp only [QuittingOneStagePayoff]
  have hq : QuitProbability G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) = 0 := by
    simp [QuitProbability]
  rw [hq]
  norm_num
  apply Finset.sum_eq_zero
  intro A hA
  split_ifs with hnonempty
  · rw [coalitionProbability_zero_of_nonempty G A hnonempty]
    simp
  · rfl

/-- A one-stage payoff is the affine combination of its forced-quit endpoints. -/
theorem quittingOneStagePayoff_replace_affine (G : QuittingGame)
    (r : Payoff G.Player) (p : QuitRow G) (n : G.Player)
    (q : Set.Icc (0 : ℝ) 1) :
    QuittingOneStagePayoff G r (p.replace G n q) n =
      (q : ℝ) * ForcedQuitPayoff G p n +
        (1 - (q : ℝ)) * ForcedContinuePayoff G r p n := by
  classical
  let rewardPart (a : Set.Icc (0 : ℝ) 1) : ℝ :=
    ∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
      CoalitionProbability G (p.replace G n a) A * G.reward ⟨A, hA⟩ n else 0
  have hcontinue (a : Set.Icc (0 : ℝ) 1) :
      1 - QuitProbability G (p.replace G n a) =
        CoalitionProbability G (p.replace G n a) ∅ := by
    simp [QuitProbability, CoalitionProbability]
  have hempty : CoalitionProbability G (p.replace G n 1) ∅ = 0 := by
    simp only [CoalitionProbability, QuitRow.replace, Finset.prod_empty, one_mul]
    have hn : n ∈ Finset.univ.filter (fun x => x ∉ (∅ : Finset G.Player)) := by simp
    apply Finset.prod_eq_zero hn
    norm_num
  have hreward : rewardPart q = (q : ℝ) * rewardPart 1 +
      (1 - (q : ℝ)) * rewardPart 0 := by
    simp only [rewardPart]
    calc
      _ = ∑ A ∈ Finset.univ.powerset,
          ((q : ℝ) * (if hA : A.Nonempty then
              CoalitionProbability G (p.replace G n 1) A * G.reward ⟨A, hA⟩ n
            else 0) +
          (1 - (q : ℝ)) * (if hA : A.Nonempty then
              CoalitionProbability G (p.replace G n 0) A * G.reward ⟨A, hA⟩ n
            else 0)) := by
        apply Finset.sum_congr rfl
        intro A hA
        split_ifs with hnonempty
        · rw [coalitionProbability_replace_affine G p n q A]
          ring
        · ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  change (1 - QuitProbability G (p.replace G n q)) * r n + rewardPart q = _
  simp only [ForcedQuitPayoff, ForcedContinuePayoff, QuittingOneStagePayoff]
  change _ = (q : ℝ) *
      ((1 - QuitProbability G (p.replace G n 1)) * (0 : Payoff G.Player) n +
        rewardPart 1) +
      (1 - (q : ℝ)) *
        ((1 - QuitProbability G (p.replace G n 0)) * r n + rewardPart 0)
  rw [hcontinue q, hcontinue 1, hcontinue 0]
  rw [coalitionProbability_replace_affine G p n q ∅, hempty, hreward]
  simp only [zero_mul]
  ring

/-- The two endpoint conditions in `E₀(r)` imply optimality against every mixed deviation. -/
theorem quittingOneStagePayoff_deviation_le (G : QuittingGame)
    (r : Payoff G.Player) (p : QuitRow G) (hp : p ∈ EpsilonRow G 0 r)
    (n : G.Player) (q : Set.Icc (0 : ℝ) 1) :
    QuittingOneStagePayoff G r (p.replace G n q) n ≤
      QuittingOneStagePayoff G r p n := by
  have hself : p.replace G n (p n) = p := by
    funext k
    by_cases hkn : k = n
    · subst k
      simp [QuitRow.replace]
    · simp [QuitRow.replace, hkn]
  have hcurrent := quittingOneStagePayoff_replace_affine G r p n (p n)
  rw [hself] at hcurrent
  rw [quittingOneStagePayoff_replace_affine G r p n q, hcurrent]
  rcases hp with ⟨hquit, hcontinue⟩
  by_cases hp0 : (p n : ℝ) = 0
  · have hb := hcontinue n (by rw [hp0]; norm_num)
    rw [hp0]
    norm_num at hb ⊢
    calc
      (q : ℝ) * ForcedQuitPayoff G p n +
          (1 - (q : ℝ)) * ForcedContinuePayoff G r p n ≤
          (q : ℝ) * ForcedContinuePayoff G r p n +
            (1 - (q : ℝ)) * ForcedContinuePayoff G r p n :=
        add_le_add (mul_le_mul_of_nonneg_left hb q.property.1) le_rfl
      _ = ForcedContinuePayoff G r p n := by ring
  · have ha := hquit n (lt_of_le_of_ne (p n).property.1 (Ne.symm hp0))
    by_cases hp1 : (p n : ℝ) = 1
    · have hq0 := q.property.1
      rw [hp1]
      norm_num at ha ⊢
      calc
        (q : ℝ) * ForcedQuitPayoff G p n +
            (1 - (q : ℝ)) * ForcedContinuePayoff G r p n ≤
            (q : ℝ) * ForcedQuitPayoff G p n +
              (1 - (q : ℝ)) * ForcedQuitPayoff G p n :=
          add_le_add le_rfl
            (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr q.property.2))
        _ = ForcedQuitPayoff G p n := by ring
    · have hb := hcontinue n (lt_of_le_of_ne (p n).property.2 hp1)
      norm_num at ha hb
      have heq : ForcedQuitPayoff G p n = ForcedContinuePayoff G r p n :=
        le_antisymm hb ha
      rw [heq]
      have hq : (q : ℝ) * ForcedContinuePayoff G r p n +
          (1 - (q : ℝ)) * ForcedContinuePayoff G r p n =
          ForcedContinuePayoff G r p n := by ring
      have hp : (p n : ℝ) * ForcedContinuePayoff G r p n +
          (1 - (p n : ℝ)) * ForcedContinuePayoff G r p n =
          ForcedContinuePayoff G r p n := by ring
      rw [hq, hp]

/-- A one-stage payoff is monotone in the player's continuation coordinate. -/
theorem quittingOneStagePayoff_mono (G : QuittingGame) (r s : Payoff G.Player)
    (p : QuitRow G) (n : G.Player) (h : r n ≤ s n) :
    QuittingOneStagePayoff G r p n ≤ QuittingOneStagePayoff G s p n := by
  simp only [QuittingOneStagePayoff]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left h
    have hq : 1 - QuitProbability G p = ∏ i, (1 - (p i : ℝ)) := by
      simp [QuitProbability]
    rw [hq]
    exact Finset.prod_nonneg fun i _ => sub_nonneg.mpr (p i).property.2
  · exact le_rfl

/-- A repeated payoff is monotone in the player's terminal continuation coordinate. -/
theorem repeatedPayoff_mono (G : QuittingGame) (k : ℕ) (r s : Payoff G.Player)
    (p : RepeatedQuitProfile G k) (n : G.Player) (h : r n ≤ s n) :
    RepeatedPayoff G k r p n ≤ RepeatedPayoff G k s p n := by
  induction k with
  | zero => simpa [RepeatedPayoff] using h
  | succ k ih =>
      simp only [RepeatedPayoff]
      apply quittingOneStagePayoff_mono
      exact ih (fun i => p i.succ)

/-- The change in one-stage payoff is survival probability times continuation change. -/
theorem quittingOneStagePayoff_sub (G : QuittingGame) (r s : Payoff G.Player)
    (p : QuitRow G) (n : G.Player) :
    QuittingOneStagePayoff G r p n - QuittingOneStagePayoff G s p n =
      (1 - QuitProbability G p) * (r n - s n) := by
  simp only [QuittingOneStagePayoff]
  ring

/-- The probability that play survives all `k` rows of a repeated profile. -/
def RepeatedSurvivalProbability (G : QuittingGame) :
    (k : ℕ) → RepeatedQuitProfile G k → ℝ
  | 0, _ => 1
  | k + 1, p =>
      (1 - QuitProbability G (p 0)) *
        RepeatedSurvivalProbability G k (fun i => p i.succ)

/-- Repeated payoff differences scale by the probability of reaching the terminal vector. -/
theorem repeatedPayoff_sub (G : QuittingGame) (k : ℕ) (r s : Payoff G.Player)
    (p : RepeatedQuitProfile G k) (n : G.Player) :
    RepeatedPayoff G k r p n - RepeatedPayoff G k s p n =
      RepeatedSurvivalProbability G k p * (r n - s n) := by
  induction k with
  | zero => simp [RepeatedPayoff, RepeatedSurvivalProbability]
  | succ k ih =>
      simp only [RepeatedPayoff]
      rw [quittingOneStagePayoff_sub]
      rw [ih]
      simp only [RepeatedSurvivalProbability]
      ring

/--
If every player continues with positive probability in every row, finite survival is positive.
-/
theorem repeatedSurvivalProbability_pos (G : QuittingGame) (k : ℕ)
    (p : RepeatedQuitProfile G k) (h : ∀ i n, (p i n : ℝ) < 1) :
    0 < RepeatedSurvivalProbability G k p := by
  induction k with
  | zero => simp [RepeatedSurvivalProbability]
  | succ k ih =>
      simp only [RepeatedSurvivalProbability]
      apply mul_pos
      · have heq : 1 - QuitProbability G (p 0) =
            ∏ n, (1 - (p 0 n : ℝ)) := by
          simp [QuitProbability]
        rw [heq]
        exact Finset.prod_pos fun n _ => sub_pos.mpr (h 0 n)
      · apply ih
        exact fun i n => h i.succ n

/-- Optimality against all mixed deviations is equivalent to the two support conditions. -/
theorem mem_epsilonRow_zero_of_deviation_le (G : QuittingGame)
    (r : Payoff G.Player) (p : QuitRow G)
    (h : ∀ n q, QuittingOneStagePayoff G r (p.replace G n q) n ≤
      QuittingOneStagePayoff G r p n) :
    p ∈ EpsilonRow G 0 r := by
  have hself : ∀ n, p.replace G n (p n) = p := by
    intro n
    funext k
    by_cases hkn : k = n
    · subst k
      simp [QuitRow.replace]
    · simp [QuitRow.replace, hkn]
  constructor
  · intro n hn
    have hzero := h n 0
    rw [quittingOneStagePayoff_replace_affine] at hzero
    have hcurrent := quittingOneStagePayoff_replace_affine G r p n (p n)
    rw [hself n] at hcurrent
    norm_num at hzero
    rw [hcurrent] at hzero
    norm_num
    nlinarith
  · intro n hn
    have hone := h n 1
    rw [quittingOneStagePayoff_replace_affine] at hone
    have hcurrent := quittingOneStagePayoff_replace_affine G r p n (p n)
    rw [hself n] at hcurrent
    norm_num at hone
    rw [hcurrent] at hone
    norm_num
    nlinarith

/-- Add one last-stage row after a finite repeated quitting profile. -/
def RepeatedQuitProfile.appendLast (G : QuittingGame) {k : ℕ}
    (p : RepeatedQuitProfile G k) (r : QuitRow G) : RepeatedQuitProfile G (k + 1) :=
  Fin.snoc p r

/-- The last entry of a profile with an appended row is that row. -/
@[simp]
theorem RepeatedQuitProfile.appendLast_last (G : QuittingGame) {k : ℕ}
    (p : RepeatedQuitProfile G k) (r : QuitRow G) :
    p.appendLast G r (Fin.last k) = r := by
  simp [RepeatedQuitProfile.appendLast]

/-- Appending a row preserves every earlier entry. -/
@[simp]
theorem RepeatedQuitProfile.appendLast_castSucc (G : QuittingGame) {k : ℕ}
    (p : RepeatedQuitProfile G k) (r : QuitRow G) (i : Fin k) :
    p.appendLast G r i.castSucc = p i := by
  simp [RepeatedQuitProfile.appendLast]

/-- A nonempty profile with an appended row retains its first entry. -/
@[simp]
theorem RepeatedQuitProfile.appendLast_zero (G : QuittingGame) {k : ℕ}
    (p : RepeatedQuitProfile G (k + 1)) (r : QuitRow G) :
    p.appendLast G r 0 = p 0 := by
  simp [RepeatedQuitProfile.appendLast]

/-- Removing the first row commutes with appending a last row. -/
theorem RepeatedQuitProfile.appendLast_tail (G : QuittingGame) {k : ℕ}
    (p : RepeatedQuitProfile G (k + 1)) (r : QuitRow G) :
    (fun i : Fin (k + 1) => p.appendLast G r i.succ) =
      RepeatedQuitProfile.appendLast G (fun i : Fin k => p i.succ) r := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [RepeatedQuitProfile.appendLast]
  · rw [show j.castSucc.succ = j.succ.castSucc by rfl]
    rw [RepeatedQuitProfile.appendLast_castSucc]
    rw [RepeatedQuitProfile.appendLast_castSucc]

/-- Appending a last row replaces the repeated game's terminal vector by its row payoff. -/
theorem repeatedPayoff_appendLast (G : QuittingGame) (k : ℕ)
    (x : Payoff G.Player) (p : RepeatedQuitProfile G k) (r : QuitRow G) :
    RepeatedPayoff G (k + 1) x (p.appendLast G r) =
      RepeatedPayoff G k (QuittingOneStagePayoff G x r) p := by
  induction k with
  | zero =>
      funext n
      have hrow : p.appendLast G r 0 = r := by
        rw [show (0 : Fin 1) = Fin.last 0 by rfl]
        exact p.appendLast_last G r
      simp only [RepeatedPayoff, hrow]
  | succ k ih =>
      change QuittingOneStagePayoff G
        (RepeatedPayoff G (k + 1) x
          (fun i => RepeatedQuitProfile.appendLast G p r i.succ))
        (RepeatedQuitProfile.appendLast G p r 0) =
        QuittingOneStagePayoff G
          (RepeatedPayoff G k (QuittingOneStagePayoff G x r) (fun i => p i.succ))
          (p 0)
      rw [RepeatedQuitProfile.appendLast_zero]
      rw [RepeatedQuitProfile.appendLast_tail]
      rw [ih]

/-- Appending a row commutes with unilateral replacement, split at the last stage. -/
theorem RepeatedQuitProfile.appendLast_replace (G : QuittingGame) {k : ℕ}
    (p : RepeatedQuitProfile G k) (r : QuitRow G) (n : G.Player)
    (q : Fin (k + 1) → Set.Icc (0 : ℝ) 1) :
    (p.appendLast G r).replace G n q =
      (p.replace G n (fun i => q i.castSucc)).appendLast G
        (r.replace G n (q (Fin.last k))) := by
  funext i j
  refine Fin.lastCases ?_ (fun t => ?_) i
  · simp [RepeatedQuitProfile.replace, RepeatedQuitProfile.appendLast, QuitRow.replace]
  · simp [RepeatedQuitProfile.replace, RepeatedQuitProfile.appendLast]

/-- Every nonempty repeated profile is its initial segment followed by its last row. -/
theorem RepeatedQuitProfile.appendLast_init_last (G : QuittingGame) {k : ℕ}
    (p : RepeatedQuitProfile G (k + 1)) :
    RepeatedQuitProfile.appendLast G (Fin.init p) (p (Fin.last k)) = p := by
  change Fin.snoc (Fin.init p) (p (Fin.last k)) = p
  exact Fin.snoc_init_self (q := p)

/-- Replacing a player's quit probability by its current value leaves a row unchanged. -/
theorem QuitRow.replace_self (G : QuittingGame) (p : QuitRow G) (n : G.Player) :
    p.replace G n (p n) = p := by
  funext j
  by_cases hj : j = n
  · subst j
    simp [QuitRow.replace]
  · simp [QuitRow.replace, hj]

/-- Replacing one player's finite sequence by its current sequence leaves the profile unchanged. -/
theorem RepeatedQuitProfile.replace_self (G : QuittingGame) {k : ℕ}
    (p : RepeatedQuitProfile G k) (n : G.Player) :
    p.replace G n (fun i => p i n) = p := by
  funext i j
  by_cases hj : j = n
  · subst j
    simp [RepeatedQuitProfile.replace]
  · simp [RepeatedQuitProfile.replace, hj]

/-- The initial segment of a repeated equilibrium is an equilibrium at the last-row payoff. -/
theorem RepeatedEquilibriumCorrespondence.init (G : QuittingGame) {k : ℕ}
    (x : Payoff G.Player) (p : RepeatedQuitProfile G (k + 1))
    (hp : p ∈ RepeatedEquilibriumCorrespondence G (k + 1) x) :
    Fin.init p ∈ RepeatedEquilibriumCorrespondence G k
      (QuittingOneStagePayoff G x (p (Fin.last k))) := by
  intro n q
  let r : QuitRow G := p (Fin.last k)
  let qFull : Fin (k + 1) → Set.Icc (0 : ℝ) 1 := Fin.snoc q (r n)
  have hdecomp : RepeatedQuitProfile.appendLast G (Fin.init p) r = p := by
    exact p.appendLast_init_last G
  have hequilibrium := hp n qFull
  rw [← hdecomp] at hequilibrium
  rw [RepeatedQuitProfile.appendLast_replace] at hequilibrium
  have hqinit : (fun i : Fin k => qFull i.castSucc) = q := by
    funext i
    simp [qFull]
  have hqlast : qFull (Fin.last k) = r n := by simp [qFull]
  rw [hqinit, hqlast, QuitRow.replace_self] at hequilibrium
  rw [repeatedPayoff_appendLast, repeatedPayoff_appendLast] at hequilibrium
  exact hequilibrium

/-- With positive finite survival, the last row of a repeated equilibrium lies in `E₀`. -/
theorem RepeatedEquilibriumCorrespondence.last_mem_epsilonRow_zero
    (G : QuittingGame) {k : ℕ} (x : Payoff G.Player)
    (p : RepeatedQuitProfile G (k + 1))
    (hp : p ∈ RepeatedEquilibriumCorrespondence G (k + 1) x)
    (hnoSure : ∀ i n, (p i n : ℝ) < 1) :
    p (Fin.last k) ∈ EpsilonRow G 0 x := by
  let pInit : RepeatedQuitProfile G k := Fin.init p
  let r : QuitRow G := p (Fin.last k)
  let y : Payoff G.Player := QuittingOneStagePayoff G x r
  have hdecomp : RepeatedQuitProfile.appendLast G pInit r = p := by
    exact p.appendLast_init_last G
  have hsurvival : 0 < RepeatedSurvivalProbability G k pInit := by
    apply repeatedSurvivalProbability_pos
    intro i n
    exact hnoSure i.castSucc n
  apply mem_epsilonRow_zero_of_deviation_le
  intro n q
  let qFull : Fin (k + 1) → Set.Icc (0 : ℝ) 1 :=
    Fin.snoc (fun i => pInit i n) q
  have hequilibrium := hp n qFull
  rw [← hdecomp] at hequilibrium
  rw [RepeatedQuitProfile.appendLast_replace] at hequilibrium
  have hqinit : (fun i : Fin k => qFull i.castSucc) = fun i => pInit i n := by
    funext i
    simp [qFull]
  have hqlast : qFull (Fin.last k) = q := by simp [qFull]
  rw [hqinit, hqlast, RepeatedQuitProfile.replace_self] at hequilibrium
  rw [repeatedPayoff_appendLast, repeatedPayoff_appendLast] at hequilibrium
  change RepeatedPayoff G k (QuittingOneStagePayoff G x (r.replace G n q)) pInit n ≤
    RepeatedPayoff G k y pInit n at hequilibrium
  have hdifference := repeatedPayoff_sub G k
    (QuittingOneStagePayoff G x (r.replace G n q)) y pInit n
  have hproduct : RepeatedSurvivalProbability G k pInit *
      (QuittingOneStagePayoff G x (r.replace G n q) n - y n) ≤ 0 := by
    rw [← hdifference]
    linarith
  change QuittingOneStagePayoff G x (r.replace G n q) n ≤ y n
  nlinarith

/-- An equilibrium can be extended by a last-stage equilibrium for its terminal vector. -/
theorem RepeatedEquilibriumCorrespondence.appendLast (G : QuittingGame) {k : ℕ}
    (x y : Payoff G.Player) (p : RepeatedQuitProfile G k) (r : QuitRow G)
    (hy : y = QuittingOneStagePayoff G x r)
    (hp : p ∈ RepeatedEquilibriumCorrespondence G k y)
    (hr : r ∈ EpsilonRow G 0 x) :
    p.appendLast G r ∈ RepeatedEquilibriumCorrespondence G (k + 1) x := by
  intro n q
  let qInit : Fin k → Set.Icc (0 : ℝ) 1 := fun i => q i.castSucc
  let qLast : Set.Icc (0 : ℝ) 1 := q (Fin.last k)
  have hlocal := quittingOneStagePayoff_deviation_le G x r hr n qLast
  have hterminal : QuittingOneStagePayoff G x (r.replace G n qLast) n ≤ y n := by
    simpa only [hy] using hlocal
  rw [RepeatedQuitProfile.appendLast_replace]
  rw [repeatedPayoff_appendLast, repeatedPayoff_appendLast]
  calc
    RepeatedPayoff G k (QuittingOneStagePayoff G x (r.replace G n qLast))
        (p.replace G n qInit) n ≤
        RepeatedPayoff G k y (p.replace G n qInit) n :=
      repeatedPayoff_mono G k _ _ _ n hterminal
    _ ≤ RepeatedPayoff G k y p n := hp n qInit
    _ = RepeatedPayoff G k (QuittingOneStagePayoff G x r) p n := by rw [← hy]

/-- `F^k` contains the `k`th iterate of `F₀`. -/
theorem repeatedF_contains_iterate (G : QuittingGame) (k : ℕ) (x : Payoff G.Player) :
    (FRow G 0).iterate k x ⊆ RepeatedF G k x := by
  induction k generalizing x with
  | zero =>
      intro z hz
      simp only [Correspondence.iterate, Set.mem_singleton_iff] at hz
      subst z
      let p : RepeatedQuitProfile G 0 := fun i => Fin.elim0 i
      refine ⟨p, ?_, ?_⟩
      · intro n q
        simp [RepeatedPayoff]
      · rfl
  | succ k ih =>
      intro z hz
      simp only [Correspondence.iterate, Set.mem_iUnion] at hz
      rcases hz with ⟨y, hy, hzk⟩
      rcases hy with ⟨r, hr, hyr⟩
      rcases ih y hzk with ⟨p, hp, hzp⟩
      refine ⟨p.appendLast G r, ?_, ?_⟩
      · exact RepeatedEquilibriumCorrespondence.appendLast G x y p r hyr.symm hp hr
      · rw [repeatedPayoff_appendLast, hyr, hzp]

/-- Where no finite-game equilibrium quits surely, `F^k` equals the `k`th iterate of `F₀`. -/
theorem repeatedF_eq_iterate_of_no_sure_quit (G : QuittingGame) (k : ℕ)
    (x : Payoff G.Player)
    (h : ∀ p ∈ RepeatedEquilibriumCorrespondence G k x, ∀ i n, (p i n : ℝ) < 1) :
    RepeatedF G k x = (FRow G 0).iterate k x := by
  apply Set.Subset.antisymm
  · induction k generalizing x with
    | zero =>
        rintro z ⟨p, _hp, hpay⟩
        simp only [Correspondence.iterate, Set.mem_singleton_iff]
        simpa [RepeatedPayoff] using hpay.symm
    | succ k ih =>
        rintro z ⟨p, hp, hpay⟩
        let pInit : RepeatedQuitProfile G k := Fin.init p
        let r : QuitRow G := p (Fin.last k)
        let y : Payoff G.Player := QuittingOneStagePayoff G x r
        have hr : r ∈ EpsilonRow G 0 x := by
          exact RepeatedEquilibriumCorrespondence.last_mem_epsilonRow_zero G x p hp
            (h p hp)
        have hpInit : pInit ∈ RepeatedEquilibriumCorrespondence G k y := by
          exact RepeatedEquilibriumCorrespondence.init G x p hp
        have hprefixNoSure :
            ∀ q ∈ RepeatedEquilibriumCorrespondence G k y,
              ∀ i n, (q i n : ℝ) < 1 := by
          intro q hq i n
          have hqFull : RepeatedQuitProfile.appendLast G q r ∈
              RepeatedEquilibriumCorrespondence G (k + 1) x := by
            exact RepeatedEquilibriumCorrespondence.appendLast G x y q r rfl hq hr
          simpa only [RepeatedQuitProfile.appendLast_castSucc] using
            h (RepeatedQuitProfile.appendLast G q r) hqFull i.castSucc n
        have hpayout : RepeatedPayoff G k y pInit ∈ RepeatedF G k y :=
          ⟨pInit, hpInit, rfl⟩
        have hiter : RepeatedPayoff G k y pInit ∈ (FRow G 0).iterate k y := by
          exact ih y hprefixNoSure hpayout
        have hz : RepeatedPayoff G k y pInit = z := by
          rw [← hpay]
          rw [← p.appendLast_init_last G]
          rw [repeatedPayoff_appendLast]
        simp only [Correspondence.iterate, Set.mem_iUnion]
        refine ⟨y, ⟨r, hr, rfl⟩, ?_⟩
        rwa [hz] at hiter
  · exact repeatedF_contains_iterate G k x

/-- Two points lie in one connected component of the repeated-equilibrium graph over `D`. -/
def SameRepeatedEquilibriumComponent (G : QuittingGame) (k : ℕ)
    (D : Set (Payoff G.Player))
    (a b : Payoff G.Player × RepeatedQuitProfile G k) : Prop :=
  ∃ C : Set (Payoff G.Player × RepeatedQuitProfile G k),
    _root_.IsConnected C ∧ a ∈ C ∧ b ∈ C ∧ ∀ z ∈ C,
      z.1 ∈ D ∧ z.2 ∈ RepeatedEquilibriumCorrespondence G k z.1

/--
Lemma 8, with the printed endpoint typo repaired.  The paper prints `(x,pʸ)` at the
second endpoint, but membership and the proof require `(y,pʸ)`, which is stated here.
-/
theorem lemma8 (G : QuittingGame) {k : ℕ} (hk : 1 ≤ k)
    (D : Set (Payoff G.Player)) (hD : _root_.IsConnected D ∧ IsCompact D)
    (hnoSure : ∀ z ∈ D, ∀ p ∈ RepeatedEquilibriumCorrespondence G k z,
      ∀ i n, (p i n : ℝ) < 1) :
    ∀ x ∈ D, ∀ y ∈ D, ∃ px ∈ RepeatedEquilibriumCorrespondence G k x,
      ∃ py ∈ RepeatedEquilibriumCorrespondence G k y,
        SameRepeatedEquilibriumComponent G k D (x, px) (y, py) := by
  sorry

/-! ### 5.5. Escape games have approximate equilibria -/

/-- The band `T` used in the escape-game proof. -/
def EscapeBand (G : QuittingGame) (ε : ℝ) : Set (Payoff G.Player) :=
  {x | (∀ n, SoloPayoff G n ≤ x n) ∧
    ∃ j, x j ≤ SoloPayoff G j + ε}

/-- A one-stage row in which only `j` may quit, with probability at most `δ`. -/
def IsSmallSoloRow (G : QuittingGame) (δ : ℝ) (j : G.Player)
    (p : QuitRow G) : Prop :=
  (p j : ℝ) ≤ δ ∧ ∀ k, k ≠ j → (p k : ℝ) = 0

/--
`Ḽ_δ = F₀ ∪ ⋃_j Ḽ_{j,δ}`, where the added moves start in `T`, use only
player `j`, and have `0 ≤ pʲ ≤ δ`.
-/
def RestrictedEscapeCorrespondence (G : QuittingGame) (δ ε : ℝ) :
    Correspondence (Payoff G.Player) (Payoff G.Player) :=
  fun x => FRow G 0 x ∪ {y | ∃ (j : G.Player) (p : QuitRow G),
    x ∈ EscapeBand G ε ∧ x j ≤ SoloPayoff G j + ε ∧
      IsSmallSoloRow G δ j p ∧ y = QuittingOneStagePayoff G x p}

/-- The uniform `ρ` conclusion of Lemma 5(2). -/
def IsUniformRho (G : QuittingGame) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ ∀ r p, IsRational G ρ r →
    p ∈ EpsilonRow G ρ r →
    let y := QuittingOneStagePayoff G r p
    ρ * QuitProbability G p ≤ ‖r - y‖ ∧ QuitProbability G p ≤ 1 - ρ

/--
Lemma 9.  In the fixed exceptional escape game, sufficiently high continuation vectors have
only the all-continue equilibrium in `E₀`.
-/
theorem lemma9 (G : QuittingGame) (_hEscape : IsEscapeGame G)
    (hstationary : ¬HasStationaryApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, (∀ j, x j ≥ B) →
      EpsilonRow G 0 x = {fun _ => (0 : Set.Icc (0 : ℝ) 1)} := by
  classical
  obtain ⟨M, hM⟩ := exists_quittingPayoffDifferenceBound G
  have hM0 : 0 ≤ M := hM.1.trans' zero_le_one
  obtain ⟨_hnormal, _hcross, ρ, hρ0, hρ1, hρuniform⟩ :=
    lemma5 G hstationary hinstant
  let valueMass : ℝ := ∑ n, |MinMaxQuit G n|
  have hvalueMass0 : 0 ≤ valueMass := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hminmax : ∀ n, MinMaxQuit G n ≤ valueMass := by
    intro n
    exact (le_abs_self _).trans (Finset.single_le_sum
      (fun i _ => abs_nonneg (MinMaxQuit G i)) (Finset.mem_univ n))
  let B : ℝ := 1 + valueMass + M + (2 * M + 1) / ρ
  have hnumerator : 0 < 2 * M + 1 := by linarith
  have hquotient : 0 < (2 * M + 1) / ρ := div_pos hnumerator hρ0
  have hB0 : 0 < B := by dsimp [B]; linarith
  have hBvalue : valueMass < B := by dsimp [B]; linarith
  have hBpayoff : M < B := by dsimp [B]; linarith
  have hBthreshold : (2 * M + 1) / ρ < B := by dsimp [B]; linarith
  refine ⟨B, hB0, ?_⟩
  intro x hx
  have hxrational : IsRational G ρ x := by
    intro n
    have hxn := hx n
    have hmn := hminmax n
    linarith
  apply Set.Subset.antisymm
  · intro p hp
    have hpρ : p ∈ EpsilonRow G ρ x :=
      EpsilonRow.mono G (le_of_lt hρ0) x hp
    have hquitBound := (hρuniform x p hxrational hpρ).2
    have hpzero : p = fun _ => (0 : Set.Icc (0 : ℝ) 1) := by
      funext n
      apply Subtype.ext
      change (p n : ℝ) = 0
      by_contra hnzero
      have hnpositive : 0 < (p n : ℝ) :=
        lt_of_le_of_ne (p n).property.1 (Ne.symm hnzero)
      have hendpoint := hp.1 n hnpositive
      norm_num at hendpoint
      have hrewardQuit := quittingRewardPart_mem_Icc G (p.replace G n 1) n hM0
        (fun A => (le_of_lt (hM.2.2 A n)))
      have hforcedQuit : ForcedQuitPayoff G p n ≤ M := by
        simpa [ForcedQuitPayoff, QuittingOneStagePayoff] using hrewardQuit.2
      have hrewardContinue := quittingRewardPart_mem_Icc G (p.replace G n 0) n hM0
        (fun A => (le_of_lt (hM.2.2 A n)))
      have hsurvival : ρ ≤ 1 - QuitProbability G (p.replace G n 0) := by
        have hbase : ρ ≤ 1 - QuitProbability G p := by linarith
        have hmonotone := quitProbability_replace_zero_le G p n
        linarith
      have hxn0 : 0 ≤ x n := le_trans (le_of_lt hB0) (hx n)
      have hscaled : ρ * x n ≤
          (1 - QuitProbability G (p.replace G n 0)) * x n :=
        mul_le_mul_of_nonneg_right hsurvival hxn0
      have hforcedContinue : ρ * x n - M ≤ ForcedContinuePayoff G x p n := by
        simp only [ForcedContinuePayoff, QuittingOneStagePayoff]
        calc
          ρ * x n - M ≤
              (1 - QuitProbability G (p.replace G n 0)) * x n - M :=
            sub_le_sub_right hscaled M
          _ ≤ (1 - QuitProbability G (p.replace G n 0)) * x n +
              ∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
                CoalitionProbability G (p.replace G n 0) A * G.reward ⟨A, hA⟩ n
              else 0 := by linarith [hrewardContinue.1]
      have hxthreshold : (2 * M + 1) / ρ < x n := hBthreshold.trans_le (hx n)
      have hlarge : M < ρ * x n - M := by
        have := (div_lt_iff₀ hρ0).mp hxthreshold
        linarith
      linarith
    exact Set.mem_singleton_iff.mpr hpzero
  · rintro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    constructor
    · intro n hn
      norm_num at hn
    · intro n hn
      have hrewardQuit := quittingRewardPart_mem_Icc G
        (QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) n 1) n hM0
        (fun A => (le_of_lt (hM.2.2 A n)))
      have hforcedQuit :
          ForcedQuitPayoff G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) n ≤ M := by
        simpa [ForcedQuitPayoff, QuittingOneStagePayoff] using hrewardQuit.2
      have hforcedContinue :
          ForcedContinuePayoff G x (fun _ => (0 : Set.Icc (0 : ℝ) 1)) n = x n := by
        rw [ForcedContinuePayoff]
        rw [QuitRow.replace_self]
        rw [quittingOneStagePayoff_zero]
      rw [hforcedContinue]
      norm_num
      have hxn := hx n
      linarith

/-- Every active point of an extended orbit lies in `A`. -/
def ExtendedOrbitStaysIn {X : Type} [TopologicalSpace X]
    {F : Correspondence X X} (x : ExtendedOrbitData F) (A : Set X) : Prop :=
  ∀ j, ActiveSegment x.segmentCount j → ∀ i,
    SegmentIndex (x.segmentLength j) i → x.point j i ∈ A

/--
Lemma 10.  For `δ=ε/(10M|N|)`, `Ḽ_δ ⊆ F_ε`; extended restricted orbits
preserve the `ε`-rational region, `Q`, and `Q \ (W ∪ T)` as stated.
-/
theorem lemma10 (G : QuittingGame) (E : EscapeWitness G) {M ρ ε : ℝ}
    (hM : IsQuittingPayoffDifferenceBound G M) (hρ : IsUniformRho G ρ)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hstationary : ¬HasStationaryApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hε : 0 < ε) (hεe : ε < E.ebar) (hερ : ε < ρ) :
    let δ := ε / (10 * M * Fintype.card G.Player)
    (∀ x, RestrictedEscapeCorrespondence G δ ε x ⊆ FRow G ε x) ∧
    (∀ x : ExtendedOrbitData (RestrictedEscapeCorrespondence G δ ε),
      x.point 0 0 ∈ {r | IsRational G ε r} →
        ExtendedOrbitStaysIn x {r | IsRational G ε r}) ∧
    (∀ x : ExtendedOrbitData (RestrictedEscapeCorrespondence G δ ε),
      x.point 0 0 ∈ E.Q → ExtendedOrbitStaysIn x E.Q) ∧
    ∀ x : ExtendedOrbitData (RestrictedEscapeCorrespondence G δ ε),
      x.point 0 0 ∈ E.Q \ (WSet G ∪ EscapeBand G ε) →
        ExtendedOrbitStaysIn x (E.Q \ (WSet G ∪ EscapeBand G ε)) := by
  sorry

/-- A critical point lies on `∂W` and has the two solo coordinates and strict cross-payoff. -/
def IsCriticalPoint (G : QuittingGame) (x : Payoff G.Player) : Prop :=
  x ∈ frontier (WSet G) ∧ ∃ j k, j ≠ k ∧ x j = SoloPayoff G j ∧
    x k = SoloPayoff G k ∧
    G.reward ⟨{j}, Finset.singleton_nonempty j⟩ k < SoloPayoff G k

/--
Lemma 11.  From every point of `T` there is a finite `Ḽ_δ` orbit staying in `T`
and ending at a critical point.
-/
theorem lemma11 (G : QuittingGame) (E : EscapeWitness G) {M ρ ε : ℝ}
    (hM : IsQuittingPayoffDifferenceBound G M)
    (hρ : IsUniformRho G ρ) (hnormal : ∀ n, IsNormalPlayer G n)
    (hstationary : ¬HasStationaryApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) (hε : 0 < ε)
    (hεe : ε < E.ebar) (hερ : ε < ρ) :
    let δ := ε / (10 * M * Fintype.card G.Player)
    ∀ x ∈ EscapeBand G ε, ∃ (k : ℕ)
      (z : Fin (k + 1) → Payoff G.Player), z 0 = x ∧
        IsFiniteOrbit (RestrictedEscapeCorrespondence G δ ε) z ∧
        (∀ i, z i ∈ EscapeBand G ε) ∧
        IsCriticalPoint G (z ⟨k, Nat.lt_succ_self k⟩) := by
  sorry

/-- Theorem 4.  Every escape game has approximate equilibria. -/
theorem theorem4 (G : QuittingGame) (h : IsEscapeGame G) :
    HasQuitApproximateEquilibria G := by
  sorry

/-! ### Printed defects resolved in the statements

The following choices repair defects in the printed paper rather than change its mathematics:

* perfection uses the printed one-sided comparisons `rⁿ-v_σⁿ ≤ ε` and
  `w_σ^{rⁿ}(aⁿ)-rⁿ ≤ ε`, together with one common good set `B` to resolve the
  sentence's inconsistent player quantifier;
* the printed negative indices in `W_i` are replaced by the surrounding formula
  `v(y_{j+1})-v(x_j)`;
* the DDP definition's `x ∈ S`, the completing action's `y ∈ A_x`, and the reversed
  inequality in Proposition 1's proof are read as `x ∈ X`, `y ∈ Y_x`, and
  `|r_i| ≤ δ` respectively;
* both occurrences of `b(p,r)` in `E_ε` are read in the just-defined order `b(r,p)`;
* Lemma 5(2a)'s free vector `x` is the continuation vector `r`;
* extended variation starts with genuine adjacent pairs, and stitching is required only when
  there is a next segment; and
* Lemma 8's second endpoint is `(y,pʸ)`, as its membership clause and proof require, rather
  than the printed repeated first coordinate `(x,pʸ)`.
-/


end
end Literature.Simon2007
