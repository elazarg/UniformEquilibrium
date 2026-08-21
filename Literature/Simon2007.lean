import Mathlib
import UniformEquilibrium.ProofView.Concepts.Stochastic.Core.Probability.InfinitePlayMeasure
import
  UniformEquilibrium.ProofView.Concepts.Stochastic.Transform.ActionLegality.DependentActionPadding

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

open MeasureTheory Set Filter CategoryTheory ProbabilityTheory
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
theorem ApproximateEquilibriaImplyPerfect :
  ∀ (G : NormalStochasticGame) (S : StochasticSemantics G),
    HasApproximateEquilibria G S → IsPerfect G S := by
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

/-! ### The production stochastic-game presentation of a DDP -/

/-- A supported local action, used only to totalize incorrectly tagged padded actions. -/
private noncomputable def DiscreteDecisionProcess.fallbackAction
    (P : DiscreteDecisionProcess) (x : P.X) (_ : PUnit) : P.Y x :=
  Classical.choose (P.choose x).support_nonempty

/-- The stage payoff attached to the sampled action in the one-player presentation. -/
private def DiscreteDecisionProcess.paddedStagePayoff
    (P : DiscreteDecisionProcess) (x : P.X) (action : ∀ _ : PUnit, P.Y x)
    (_ : PUnit) : ℝ :=
  P.valueY x (action PUnit.unit)

/-- The transition of the one-player presentation is the DDP move law. -/
private def DiscreteDecisionProcess.paddedTransition
    (P : DiscreteDecisionProcess) (x : P.X) (action : ∀ _ : PUnit, P.Y x) : PMF P.X :=
  P.move x (action PUnit.unit)

/-- The state-independent-action stochastic game obtained by sigma-padding the DDP's
state-dependent action family. -/
private abbrev DiscreteDecisionProcess.paddedGame
    (P : DiscreteDecisionProcess) : GameTheory.StochasticGame PUnit :=
  GameTheory.StochasticGame.DependentAction.game
    (fun x : P.X => fun _ : PUnit => P.Y x)
    P.fallbackAction P.paddedStagePayoff P.paddedTransition 0 (by norm_num) (by norm_num)

private instance DiscreteDecisionProcess.countablePaddedState
    (P : DiscreteDecisionProcess) : Countable P.paddedGame.State := by
  change Countable P.X
  infer_instance

private instance DiscreteDecisionProcess.countablePaddedAction
    (P : DiscreteDecisionProcess) (who : PUnit) : Countable (P.paddedGame.Act who) := by
  change Countable (Σ state, P.Y state)
  infer_instance

/-- At a padded-game history, sample the DDP's local action at the current state. -/
private def DiscreteDecisionProcess.paddedPolicy
    (P : DiscreteDecisionProcess) (_ : PUnit) (t : ℕ) (history : P.paddedGame.Hist t) :
    PMF (P.Y history.2) :=
  P.choose history.2

/-- The canonical padded behavior profile attaches the current-state tag to every sampled
local action. -/
private def DiscreteDecisionProcess.paddedProfile
    (P : DiscreteDecisionProcess) : P.paddedGame.BehaviorProfile :=
  GameTheory.StochasticGame.DependentAction.liftBehaviorProfile
    (fun x : P.X => fun _ : PUnit => P.Y x)
    P.fallbackAction P.paddedStagePayoff P.paddedTransition 0 (by norm_num) (by norm_num)
    P.paddedPolicy

/-- DDP states carry the discrete sigma algebra. -/
private instance ddpStateMeasurableSpace (P : DiscreteDecisionProcess) :
    MeasurableSpace P.X := ⊤

/-- An infinite path `x₀,y₁,x₂,y₃,…`; zero-mass transitions occur on null paths. -/
structure DDPPath (P : DiscreteDecisionProcess) where
  x : ℕ → P.X
  y : (i : ℕ) → P.Y (x i)

/-- A finite decision-process path containing `k` chosen actions. -/
structure DDPFinitePath (P : DiscreteDecisionProcess) (k : ℕ) where
  x : Fin (k + 1) → P.X
  y : (i : Fin k) → P.Y (x i.castSucc)

/-- Finite possible paths form a countable type when states and actions are countable. -/
instance ddpFinitePathCountable (P : DiscreteDecisionProcess) (k : ℕ) :
    Countable (DDPFinitePath P k) :=
  (show Function.Injective
      (fun h : DDPFinitePath P k =>
        (h.x, fun i => Sigma.mk (h.x i.castSucc) (h.y i))) from by
      intro a b hab
      cases a with
      | mk ax ay =>
        cases b with
        | mk bx byy =>
          simp only [Prod.mk.injEq] at hab
          cases hab.1
          have : ay = byy := by
            funext i
            exact eq_of_heq (Sigma.mk.inj_iff.mp (congrFun hab.2 i) |>.2)
          cases this
          rfl).countable

/-- Finite DDP paths carry the discrete sigma algebra. -/
private instance ddpFinitePathMeasurableSpace (P : DiscreteDecisionProcess) (k : ℕ) :
    MeasurableSpace (DDPFinitePath P k) := ⊤

/-- The `k`-action prefix of a possible infinite decision-process path. -/
def DDPPath.prefix (P : DiscreteDecisionProcess) (p : DDPPath P)
    (k : ℕ) : DDPFinitePath P k where
  x i := p.x i
  y i := p.y i

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

/-- Sampling the first action restores its missing factor in forced-action probability. -/
private theorem DDPFinitePath.probability_eq_choose_mul_afterActionProbability
    (P : DiscreteDecisionProcess) {k : ℕ} (h : DDPFinitePath P (k + 1)) :
    h.probability P = P.choose (h.x 0) (h.y 0) * h.afterActionProbability P := by
  rw [DDPFinitePath.probability, DDPFinitePath.afterActionProbability]
  rw [Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
  ac_rfl

/-- The cylinder sigma algebra on infinite decision-process paths. -/
instance ddpPathMeasurableSpace (P : DiscreteDecisionProcess) :
    MeasurableSpace (DDPPath P) :=
  MeasurableSpace.generateFrom {U | ∃ k, ∃ h : DDPFinitePath P k, U = DDPCylinder P h}

/-- Every finite-path cylinder belongs to the generated path sigma algebra. -/
theorem measurableSet_ddpCylinder (P : DiscreteDecisionProcess) {k : ℕ}
    (h : DDPFinitePath P k) : MeasurableSet (DDPCylinder P h) :=
  MeasurableSpace.measurableSet_generateFrom ⟨k, h, rfl⟩

/-- Every finite-prefix projection is measurable for the cylinder sigma algebra. -/
private theorem DDPPath.measurable_prefix (P : DiscreteDecisionProcess) (k : ℕ) :
    Measurable (fun p : DDPPath P => p.prefix P k) := by
  apply measurable_to_countable'
  intro h
  change MeasurableSet (DDPCylinder P h)
  exact measurableSet_ddpCylinder P h

/-- One sampled DDP stage records the current state and the action selected there. -/
private abbrev DDPStage (P : DiscreteDecisionProcess) := (x : P.X) × P.Y x

/-- Reindex a finite exact stage string as a prefix on `Finset.Iic`. -/
private def DiscreteDecisionProcess.stagePrefixOfFin
    (P : DiscreteDecisionProcess) {k : ℕ}
    (stage : Fin (k + 1) → DDPStage P) : ∀ _ : Finset.Iic k, DDPStage P :=
  fun i => stage ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩

/-- Evaluate a one-coordinate independent product law at its unique coordinate. -/
private theorem pmfPi_map_eval_punit {A : PUnit → Type} [∀ i, Countable (A i)]
    (law : ∀ i, PMF (A i)) :
    (Math.PMFProduct.pmfPi law).map (fun action => action PUnit.unit) = law PUnit.unit := by
  classical
  ext action
  rw [PMF.map_apply]
  rw [tsum_eq_single (fun _ => action)]
  · simp [Math.PMFProduct.pmfPi_apply]
  · intro other hother
    rw [if_neg]
    intro heval
    apply hother
    funext i
    cases i
    exact heval.symm

/-- A one-coordinate product law is the image of its factor under the constant function. -/
private theorem pmfPi_const_punit_eq_map {A : Type} [Countable A] (law : PMF A) :
    Math.PMFProduct.pmfPi (fun _ : PUnit => law) =
      law.map (fun action => fun _ : PUnit => action) := by
  let eval : (PUnit → A) → A := fun action => action PUnit.unit
  let constant : A → PUnit → A := fun action _ => action
  have hinverse : constant ∘ eval = id := by
    funext action
    apply funext
    intro i
    cases i
    rfl
  calc
    Math.PMFProduct.pmfPi (fun _ : PUnit => law) =
        (Math.PMFProduct.pmfPi (fun _ : PUnit => law)).map (constant ∘ eval) := by
      rw [hinverse, PMF.map_id]
    _ = ((Math.PMFProduct.pmfPi (fun _ : PUnit => law)).map eval).map constant := by
      rw [PMF.map_comp]
    _ = law.map constant := by
      rw [pmfPi_map_eval_punit]

/-- The joint law obtained by binding and remembering the first coordinate has the expected
point masses. -/
private theorem pmf_bind_map_pair_apply {A B : Type} (law : PMF A) (next : A → PMF B)
    (a : A) (b : B) :
    (law.bind fun x => (next x).map fun y => (x, y)) (a, b) = law a * next a b := by
  classical
  rw [PMF.bind_apply]
  rw [tsum_eq_single a]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single b]
    · simp
    · intro other hother
      rw [if_neg]
      intro h
      exact hother (congrArg Prod.snd h).symm
  · intro other hother
    simp [PMF.map_apply]
    exact Or.inr (fun h => (hother h.symm).elim)

/-- Encode one local action as the unique player's correctly tagged padded joint action. -/
private def DiscreteDecisionProcess.encodePaddedJointAction
    (P : DiscreteDecisionProcess) (x : P.X) (action : P.Y x) :
    P.paddedGame.JointAct :=
  fun who => GameTheory.StochasticGame.DependentAction.embed
    (fun state : P.X => fun _ : PUnit => P.Y state) x who action

/-- Read the unique player's padded action as a local action at the current state. -/
private def DiscreteDecisionProcess.decodePaddedJointAction
    (P : DiscreteDecisionProcess) (x : P.X) (action : P.paddedGame.JointAct) : P.Y x :=
  GameTheory.StochasticGame.DependentAction.decode
    (fun state : P.X => fun _ : PUnit => P.Y state) P.fallbackAction x PUnit.unit
      (action PUnit.unit)

/-- Encoding and then decoding a local action is the identity. -/
@[simp] private theorem DiscreteDecisionProcess.decodePaddedJointAction_encode
    (P : DiscreteDecisionProcess) (x : P.X) (action : P.Y x) :
    P.decodePaddedJointAction x (P.encodePaddedJointAction x action) = action := by
  exact GameTheory.StochasticGame.DependentAction.decode_embed
    (fun state : P.X => fun _ : PUnit => P.Y state) P.fallbackAction x PUnit.unit action

/-- Attaching and then decoding the current-state tag preserves the local action law. -/
private theorem DiscreteDecisionProcess.map_decode_embed_choice
    (P : DiscreteDecisionProcess) (x : P.X) :
    ((P.choose x).map
        (GameTheory.StochasticGame.DependentAction.embed
          (fun state : P.X => fun _ : PUnit => P.Y state) x PUnit.unit)).map
      (GameTheory.StochasticGame.DependentAction.decode
        (fun state : P.X => fun _ : PUnit => P.Y state) P.fallbackAction x PUnit.unit) =
        P.choose x := by
  rw [PMF.map_comp]
  have hcomp :
      GameTheory.StochasticGame.DependentAction.decode
          (fun state : P.X => fun _ : PUnit => P.Y state) P.fallbackAction x PUnit.unit ∘
        GameTheory.StochasticGame.DependentAction.embed
          (fun state : P.X => fun _ : PUnit => P.Y state) x PUnit.unit = id := by
    funext action
    exact GameTheory.StochasticGame.DependentAction.decode_embed
      (fun state : P.X => fun _ : PUnit => P.Y state) P.fallbackAction x PUnit.unit action
  rw [hcomp, PMF.map_id]

/-- Decode a padded stochastic-game stage back to the corresponding DDP stage. -/
private def DiscreteDecisionProcess.decodePaddedStage (P : DiscreteDecisionProcess)
    (stage : P.paddedGame.StageOutcome) : DDPStage P :=
  ⟨stage.1, P.decodePaddedJointAction stage.1 stage.2⟩

/-- Encode one DDP stage as a correctly tagged padded stochastic-game stage. -/
private def DiscreteDecisionProcess.encodePaddedStage (P : DiscreteDecisionProcess)
    (stage : DDPStage P) : P.paddedGame.StageOutcome :=
  ⟨stage.1, P.encodePaddedJointAction stage.1 stage.2⟩

/-- Decoding an encoded DDP stage is the identity. -/
@[simp] private theorem DiscreteDecisionProcess.decodePaddedStage_encode
    (P : DiscreteDecisionProcess) (stage : DDPStage P) :
    P.decodePaddedStage (P.encodePaddedStage stage) = stage := by
  cases stage
  simp [DiscreteDecisionProcess.decodePaddedStage,
    DiscreteDecisionProcess.encodePaddedStage]

/-- On an encoded legal joint action, the padded game's transition is exactly the DDP move
law. -/
private theorem DiscreteDecisionProcess.paddedGame_transition_encode
    (P : DiscreteDecisionProcess) (x : P.X) (action : P.Y x) :
    P.paddedGame.transition x (P.encodePaddedJointAction x action) =
      P.move x action := by
  convert GameTheory.StochasticGame.DependentAction.game_transition_embed
    (fun state : P.X => fun _ : PUnit => P.Y state)
    P.fallbackAction P.paddedStagePayoff P.paddedTransition 0 (by norm_num) (by norm_num)
    x (fun _ : PUnit => action) using 1
  · congr
  · rfl

/-- Decode every stage of a padded stochastic-game play. -/
private def DiscreteDecisionProcess.decodePaddedPlay (P : DiscreteDecisionProcess)
    (play : P.paddedGame.Play) : ℕ → DDPStage P :=
  fun i => P.decodePaddedStage (play i)

/-- Decode a finite production prefix coordinatewise. -/
private def DiscreteDecisionProcess.decodePaddedCoords
    (P : DiscreteDecisionProcess) (t : ℕ)
    (coords : ∀ _ : Finset.Iic t, P.paddedGame.StageOutcome) :
    ∀ _ : Finset.Iic t, DDPStage P :=
  fun i => P.decodePaddedStage (coords i)

/-- Encode a finite DDP prefix coordinatewise. -/
private def DiscreteDecisionProcess.encodePaddedCoords
    (P : DiscreteDecisionProcess) (t : ℕ)
    (coords : ∀ _ : Finset.Iic t, DDPStage P) :
    ∀ _ : Finset.Iic t, P.paddedGame.StageOutcome :=
  fun i => P.encodePaddedStage (coords i)

/-- Append one DDP stage to a finite coordinate prefix. -/
private def DiscreteDecisionProcess.extendDDPCoords
    (P : DiscreteDecisionProcess) {t : ℕ}
    (coords : ∀ _ : Finset.Iic t, DDPStage P) (next : DDPStage P) :
    ∀ _ : Finset.Iic (t + 1), DDPStage P :=
  fun i => if h : i.1 ≤ t then coords ⟨i.1, Finset.mem_Iic.mpr h⟩ else next

/-- Splitting off the last coordinate is inverse to extending a finite DDP prefix. -/
private def DiscreteDecisionProcess.extendDDPCoordsEquiv
    (P : DiscreteDecisionProcess) (t : ℕ) :
    ((∀ _ : Finset.Iic t, DDPStage P) × DDPStage P) ≃
      (∀ _ : Finset.Iic (t + 1), DDPStage P) where
  toFun pair := P.extendDDPCoords pair.1 pair.2
  invFun coords :=
    (fun i => coords ⟨i.1, Finset.mem_Iic.mpr (by
      exact (Finset.mem_Iic.mp i.2).trans (Nat.le_succ t))⟩,
      coords ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩)
  left_inv pair := by
    apply Prod.ext
    · funext i
      simp [DiscreteDecisionProcess.extendDDPCoords, Finset.mem_Iic.mp i.2]
    · simp [DiscreteDecisionProcess.extendDDPCoords]
  right_inv coords := by
    funext i
    by_cases hi : i.1 ≤ t
    · simp [DiscreteDecisionProcess.extendDDPCoords, hi]
    · have hit : i.1 = t + 1 := by
        have := Finset.mem_Iic.mp i.2
        omega
      rw [show i = ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩ from Subtype.ext hit]
      simp [DiscreteDecisionProcess.extendDDPCoords]

/-- Coordinatewise decoding is a left inverse to coordinatewise encoding. -/
@[simp] private theorem DiscreteDecisionProcess.decodePaddedCoords_encode
    (P : DiscreteDecisionProcess) (t : ℕ)
    (coords : ∀ _ : Finset.Iic t, DDPStage P) :
    P.decodePaddedCoords t (P.encodePaddedCoords t coords) = coords := by
  funext i
  exact P.decodePaddedStage_encode (coords i)

/-- Encoding commutes with extending a finite coordinate prefix. -/
private theorem DiscreteDecisionProcess.encodePaddedCoords_extend
    (P : DiscreteDecisionProcess) {t : ℕ}
    (coords : ∀ _ : Finset.Iic t, DDPStage P) (next : DDPStage P) :
    P.encodePaddedCoords (t + 1) (P.extendDDPCoords coords next) =
      P.paddedGame.extendCoords (P.encodePaddedCoords t coords) (P.encodePaddedStage next) := by
  funext i
  by_cases hi : i.1 ≤ t <;>
    simp [DiscreteDecisionProcess.encodePaddedCoords,
      DiscreteDecisionProcess.extendDDPCoords,
      GameTheory.StochasticGame.extendCoords, hi]

/-- The stage alphabet is countable and carries its discrete sigma algebra. -/
private instance ddpStageMeasurableSpace (P : DiscreteDecisionProcess) :
    MeasurableSpace (DDPStage P) := ⊤

private theorem DiscreteDecisionProcess.measurable_decodePaddedPlay
    (P : DiscreteDecisionProcess) : Measurable P.decodePaddedPlay := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_of_countable P.decodePaddedStage).comp (measurable_pi_apply i)

private theorem DiscreteDecisionProcess.measurable_decodePaddedCoords
    (P : DiscreteDecisionProcess) (t : ℕ) : Measurable (P.decodePaddedCoords t) :=
  measurable_of_countable _

/-- The unique padded action coordinate decodes to the DDP's local choice law. -/
private theorem DiscreteDecisionProcess.map_decodePaddedJointAction_stageActionDist
    (P : DiscreteDecisionProcess) {t : ℕ} (history : P.paddedGame.Hist t) :
    (P.paddedGame.stageActionDist P.paddedProfile history).map
        (P.decodePaddedJointAction history.2) = P.choose history.2 := by
  let eval : P.paddedGame.JointAct → P.paddedGame.Act PUnit.unit :=
    fun action => action PUnit.unit
  let decode : P.paddedGame.Act PUnit.unit → P.Y history.2 :=
    GameTheory.StochasticGame.DependentAction.decode
      (fun state : P.X => fun _ : PUnit => P.Y state) P.fallbackAction history.2 PUnit.unit
  have heval :
      (P.paddedGame.stageActionDist P.paddedProfile history).map eval =
        P.paddedProfile PUnit.unit t history := by
    exact pmfPi_map_eval_punit (fun i => P.paddedProfile i t history)
  calc
    (P.paddedGame.stageActionDist P.paddedProfile history).map
        (P.decodePaddedJointAction history.2) =
        ((P.paddedGame.stageActionDist P.paddedProfile history).map eval).map decode := by
      rw [PMF.map_comp]
      rfl
    _ = (P.paddedProfile PUnit.unit t history).map decode := by rw [heval]
    _ = ((P.choose history.2).map
        (GameTheory.StochasticGame.DependentAction.embed
          (fun state : P.X => fun _ : PUnit => P.Y state) history.2 PUnit.unit)).map
            decode := rfl
    _ = P.choose history.2 := P.map_decode_embed_choice history.2

/-- The lifted one-player action law is exactly the image of the local DDP choice law under
the correctly tagged joint-action encoding. -/
private theorem DiscreteDecisionProcess.stageActionDist_paddedProfile_eq_map_encode
    (P : DiscreteDecisionProcess) {t : ℕ} (history : P.paddedGame.Hist t) :
    P.paddedGame.stageActionDist P.paddedProfile history =
      (P.choose history.2).map (P.encodePaddedJointAction history.2) := by
  change Math.PMFProduct.pmfPi
      (fun who : PUnit => (P.choose history.2).map
        (GameTheory.StochasticGame.DependentAction.embed
          (fun state : P.X => fun _ : PUnit => P.Y state) history.2 who)) = _
  have hfamily :
      (fun who : PUnit => (P.choose history.2).map
        (GameTheory.StochasticGame.DependentAction.embed
          (fun state : P.X => fun _ : PUnit => P.Y state) history.2 who)) =
      fun _ : PUnit => (P.choose history.2).map
        (GameTheory.StochasticGame.DependentAction.embed
          (fun state : P.X => fun _ : PUnit => P.Y state) history.2 PUnit.unit) := by
    funext who
    cases who
    rfl
  rw [hfamily, pmfPi_const_punit_eq_map, PMF.map_comp]
  rfl

/-- Draw the action at the initial state. -/
private def DiscreteDecisionProcess.initialStagePMF (P : DiscreteDecisionProcess)
    (x : P.X) : PMF (DDPStage P) :=
  (P.choose x).map fun y => ⟨x, y⟩

/-- The production game's initial stage law is the encoded DDP initial-stage law. -/
private theorem DiscreteDecisionProcess.initialPMF_paddedProfile_eq_map_encode
    (P : DiscreteDecisionProcess) (x : P.X) :
    P.paddedGame.initialPMF P.paddedProfile x =
      (P.initialStagePMF x).map P.encodePaddedStage := by
  rw [GameTheory.StochasticGame.initialPMF]
  rw [P.stageActionDist_paddedProfile_eq_map_encode]
  rw [DiscreteDecisionProcess.initialStagePMF, PMF.map_comp, PMF.map_comp]
  rfl

/-- Decoding the production game's initial stage recovers the DDP's initial-stage law. -/
private theorem DiscreteDecisionProcess.map_decodePaddedStage_initialPMF
    (P : DiscreteDecisionProcess) (x : P.X) :
    (P.paddedGame.initialPMF P.paddedProfile x).map P.decodePaddedStage =
      P.initialStagePMF x := by
  let history := P.paddedGame.emptyHist x
  have hdecode :
      (P.paddedGame.stageActionDist P.paddedProfile history).map
          (P.decodePaddedJointAction x) = P.choose x := by
    simpa only [history, GameTheory.StochasticGame.emptyHist] using
      P.map_decodePaddedJointAction_stageActionDist history
  rw [GameTheory.StochasticGame.initialPMF, PMF.map_comp]
  change (P.paddedGame.stageActionDist P.paddedProfile history).map
      (fun action => (⟨x, P.decodePaddedJointAction x action⟩ : DDPStage P)) =
        P.initialStagePMF x
  change (P.paddedGame.stageActionDist P.paddedProfile history).map
      ((fun action : P.Y x => (⟨x, action⟩ : DDPStage P)) ∘
        P.decodePaddedJointAction x) = P.initialStagePMF x
  rw [← PMF.map_comp, hdecode]
  rfl

/-- Move from the current state/action and then draw the action at the next state. -/
private def DiscreteDecisionProcess.stepStagePMF (P : DiscreteDecisionProcess)
    (stage : DDPStage P) : PMF (DDPStage P) :=
  (P.move stage.1 stage.2).bind fun x =>
    (P.choose x).map fun y => ⟨x, y⟩

/-- On an encoded DDP prefix, the production one-step law is exactly the image of the local
stage-transition law under stage encoding. -/
private theorem DiscreteDecisionProcess.stepPMF_encodePaddedCoords
    (P : DiscreteDecisionProcess) (t : ℕ)
    (coords : ∀ _ : Finset.Iic t, DDPStage P) :
    P.paddedGame.stepPMF P.paddedProfile t (P.encodePaddedCoords t coords) =
      (P.stepStagePMF (coords ⟨t, Finset.mem_Iic.mpr le_rfl⟩)).map
        P.encodePaddedStage := by
  let current := coords ⟨t, Finset.mem_Iic.mpr le_rfl⟩
  rw [GameTheory.StochasticGame.stepPMF]
  change (P.paddedGame.transition current.1 (P.encodePaddedJointAction current.1 current.2)).bind
      (fun state => (P.paddedGame.stageActionDist P.paddedProfile
        (P.paddedGame.histOfCoords (P.encodePaddedCoords t coords) state)).map
          fun action => (state, action)) = _
  rw [P.paddedGame_transition_encode]
  rw [DiscreteDecisionProcess.stepStagePMF, PMF.map_bind]
  apply congrArg (PMF.bind (P.move current.1 current.2))
  funext state
  rw [P.stageActionDist_paddedProfile_eq_map_encode]
  rw [PMF.map_comp, PMF.map_comp]
  rfl

/-- The finite DDP coordinate law generated by an arbitrary initial sampled-stage law. -/
private def DiscreteDecisionProcess.ddpCoordsDistFromStagePMF
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) :
    (t : ℕ) → PMF (∀ _ : Finset.Iic t, DDPStage P) :=
  fun t => Nat.rec (initial.map fun stage (_ : Finset.Iic 0) => stage)
    (fun n previous => previous.bind fun coords =>
      (P.stepStagePMF (coords ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).map
        (P.extendDDPCoords coords)) t

/-- The production coordinate family from an encoded initial law is exactly the encoded
finite DDP coordinate family. -/
private theorem DiscreteDecisionProcess.coordsDistFromStagePMF_eq_map_encode
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) : ∀ t,
    P.paddedGame.coordsDistFromStagePMF P.paddedProfile
        (initial.map P.encodePaddedStage) t =
      (P.ddpCoordsDistFromStagePMF initial t).map (P.encodePaddedCoords t) := by
  intro t
  induction t with
  | zero =>
      rw [GameTheory.StochasticGame.coordsDistFromStagePMF]
      rw [DiscreteDecisionProcess.ddpCoordsDistFromStagePMF]
      change ((initial.map P.encodePaddedStage).map
          (fun stage (_ : Finset.Iic 0) => stage)) =
        (initial.map (fun stage (_ : Finset.Iic 0) => stage)).map
          (P.encodePaddedCoords 0)
      rw [PMF.map_comp, PMF.map_comp]
      rfl
  | succ t ih =>
      rw [P.paddedGame.coordsDistFromStagePMF_succ]
      rw [DiscreteDecisionProcess.ddpCoordsDistFromStagePMF]
      rw [ih, PMF.bind_map, PMF.map_bind]
      apply congrArg (PMF.bind (P.ddpCoordsDistFromStagePMF initial t))
      funext coords
      change (P.paddedGame.stepPMF P.paddedProfile t (P.encodePaddedCoords t coords)).map
          (P.paddedGame.extendCoords (P.encodePaddedCoords t coords)) =
        ((P.stepStagePMF (coords ⟨t, Finset.mem_Iic.mpr le_rfl⟩)).map
          (P.extendDDPCoords coords)).map (P.encodePaddedCoords (t + 1))
      rw [P.stepPMF_encodePaddedCoords, PMF.map_comp, PMF.map_comp]
      congr 1
      funext next
      exact (P.encodePaddedCoords_extend coords next).symm

/-- The production infinite-play law from an arbitrary encoded DDP stage law, decoded back to
DDP stages. -/
private def DiscreteDecisionProcess.productionRawLawWithInitial
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) :
    Measure (ℕ → DDPStage P) :=
  (P.paddedGame.infinitePlayMeasureFromStagePMF P.paddedProfile
    (initial.map P.encodePaddedStage)).map P.decodePaddedPlay

private instance DiscreteDecisionProcess.isProbabilityMeasure_productionRawLawWithInitial
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) :
    IsProbabilityMeasure (P.productionRawLawWithInitial initial) := by
  unfold DiscreteDecisionProcess.productionRawLawWithInitial
  exact Measure.isProbabilityMeasure_map P.measurable_decodePaddedPlay.aemeasurable

/-- Every finite marginal of the arbitrary-initial decoded production law is the finite DDP
coordinate recursion. -/
private theorem DiscreteDecisionProcess.map_frestrictLe_productionRawLawWithInitial
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) (t : ℕ) :
    (P.productionRawLawWithInitial initial).map
        (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) t) =
      (P.ddpCoordsDistFromStagePMF initial t).toMeasure := by
  rw [DiscreteDecisionProcess.productionRawLawWithInitial]
  rw [Measure.map_map
    (Preorder.measurable_frestrictLe (X := fun _ : ℕ => DDPStage P) t)
    P.measurable_decodePaddedPlay]
  have hcommute :
      Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) t ∘ P.decodePaddedPlay =
        P.decodePaddedCoords t ∘
          Preorder.frestrictLe (π := fun _ : ℕ => P.paddedGame.StageOutcome) t := rfl
  rw [hcommute]
  rw [← Measure.map_map (P.measurable_decodePaddedCoords t)
    (Preorder.measurable_frestrictLe (X := fun _ : ℕ => P.paddedGame.StageOutcome) t)]
  rw [P.paddedGame.map_frestrictLe_infinitePlayMeasureFromStagePMF]
  rw [PMF.toMeasure_map (P.decodePaddedCoords t) _ (P.measurable_decodePaddedCoords t)]
  rw [P.coordsDistFromStagePMF_eq_map_encode initial t]
  rw [PMF.map_comp]
  have hleftInverse :
      P.decodePaddedCoords t ∘ P.encodePaddedCoords t = id := by
    funext coords
    exact P.decodePaddedCoords_encode t coords
  rw [hleftInverse, PMF.map_id]

/-- The finite DDP coordinate recursion has the usual initial mass times transition-product
point probabilities. -/
private theorem DiscreteDecisionProcess.ddpCoordsDistFromStagePMF_apply
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) : ∀ (k : ℕ)
    (stage : Fin (k + 1) → DDPStage P),
    P.ddpCoordsDistFromStagePMF initial k (P.stagePrefixOfFin stage) =
      initial (stage 0) *
        ∏ i : Fin k, P.stepStagePMF (stage i.castSucc) (stage i.succ) := by
  intro k
  induction k with
  | zero =>
      intro stage
      let e : DDPStage P ≃ (∀ _ : Finset.Iic 0, DDPStage P) :=
        { toFun := fun value _ => value
          invFun := fun values => values default
          left_inv := fun _ => rfl
          right_inv := fun values => by
            funext i
            rw [show i = default from Subsingleton.elim _ _] }
      change (initial.map e) (P.stagePrefixOfFin stage) = _
      rw [Math.ProbabilityMassFunction.map_equiv_apply]
      have hinverse : e.symm (P.stagePrefixOfFin stage) = stage 0 := by
        rfl
      rw [hinverse]
      simp
  | succ k ih =>
      intro stage
      let old : Fin (k + 1) → DDPStage P := Fin.init stage
      let previous := P.ddpCoordsDistFromStagePMF initial k
      let nextLaw : (∀ _ : Finset.Iic k, DDPStage P) → PMF (DDPStage P) :=
        fun coords => P.stepStagePMF (coords ⟨k, Finset.mem_Iic.mpr le_rfl⟩)
      let joint := previous.bind fun coords =>
        (nextLaw coords).map fun next => (coords, next)
      have hdist :
          P.ddpCoordsDistFromStagePMF initial (k + 1) =
            joint.map (P.extendDDPCoordsEquiv k) := by
        rw [DiscreteDecisionProcess.ddpCoordsDistFromStagePMF]
        change previous.bind (fun coords =>
            (nextLaw coords).map (P.extendDDPCoords coords)) =
          joint.map (P.extendDDPCoordsEquiv k)
        dsimp only [joint]
        rw [PMF.map_bind]
        apply congrArg (PMF.bind previous)
        funext coords
        rw [PMF.map_comp]
        rfl
      have hinverse :
          (P.extendDDPCoordsEquiv k).symm (P.stagePrefixOfFin stage) =
            (P.stagePrefixOfFin old, stage (Fin.last (k + 1))) := by
        apply Prod.ext
        · funext i
          rfl
        · rfl
      rw [hdist, Math.ProbabilityMassFunction.map_equiv_apply, hinverse]
      rw [pmf_bind_map_pair_apply]
      change P.ddpCoordsDistFromStagePMF initial k (P.stagePrefixOfFin old) *
          P.stepStagePMF
            (P.stagePrefixOfFin old ⟨k, Finset.mem_Iic.mpr le_rfl⟩)
            (stage (Fin.last (k + 1))) = _
      rw [ih old]
      rw [Fin.prod_univ_castSucc]
      dsimp only [old, Fin.init]
      simp only [DiscreteDecisionProcess.stagePrefixOfFin, Fin.castSucc_zero,
        Fin.succ_castSucc, Fin.succ_last]
      have hcurrent : Fin.init stage ⟨k, by omega⟩ = stage (Fin.last k).castSucc := by
        rfl
      have hnext : stage (Fin.last (k + 1)) = stage (Fin.last k.succ) := by
        rfl
      rw [hcurrent, hnext]
      ring

/-- The arbitrary-initial decoded production law has the DDP's exact finite-cylinder
probabilities. -/
private theorem DiscreteDecisionProcess.productionRawLawWithInitial_exactStageCylinder
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) (k : ℕ)
    (stage : Fin (k + 1) → DDPStage P) :
    P.productionRawLawWithInitial initial
        {w : ℕ → DDPStage P | ∀ i : Fin (k + 1), w i = stage i} =
      initial (stage 0) *
        ∏ i : Fin k, P.stepStagePMF (stage i.castSucc) (stage i.succ) := by
  have hevent :
      {w : ℕ → DDPStage P | ∀ i : Fin (k + 1), w i = stage i} =
        Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) k ⁻¹'
          {P.stagePrefixOfFin stage} := by
    ext w
    simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      funext i
      exact h ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩
    · intro h i
      exact congrFun h ⟨i.1, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp i.2)⟩
  rw [hevent]
  rw [← Measure.map_apply
    (Preorder.measurable_frestrictLe (X := fun _ : ℕ => DDPStage P) k)
    (measurableSet_singleton (P.stagePrefixOfFin stage))]
  rw [P.map_frestrictLe_productionRawLawWithInitial initial k]
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  exact P.ddpCoordsDistFromStagePMF_apply initial k stage

/-- The initial-stage law evaluates to the action-selection probability. -/
private theorem DiscreteDecisionProcess.initialStagePMF_apply
    (P : DiscreteDecisionProcess) (x : P.X) (y : P.Y x) :
    P.initialStagePMF x ⟨x, y⟩ = P.choose x y := by
  classical
  rw [DiscreteDecisionProcess.initialStagePMF, PMF.map_apply]
  rw [tsum_eq_single y]
  · simp
  · intro other hother
    rw [if_neg]
    intro heq
    have : other = y := eq_of_heq (Sigma.mk.inj_iff.mp heq.symm).2
    exact hother this

/-- An initial-stage law has no mass on a different state fiber. -/
private theorem DiscreteDecisionProcess.initialStagePMF_apply_of_ne
    (P : DiscreteDecisionProcess) {x z : P.X} (y : P.Y z) (h : x ≠ z) :
    P.initialStagePMF x ⟨z, y⟩ = 0 := by
  classical
  rw [DiscreteDecisionProcess.initialStagePMF, PMF.map_apply]
  calc
    _ = ∑' _action : P.Y x, (0 : ℝ≥0∞) := by
      apply tsum_congr
      intro action
      rw [if_neg]
      intro heq
      exact h (Sigma.mk.inj_iff.mp heq).1.symm
    _ = 0 := tsum_zero

/-- A stage transition has the product of its move and next-action probabilities. -/
private theorem DiscreteDecisionProcess.stepStagePMF_apply
    (P : DiscreteDecisionProcess) (x : P.X) (y : P.Y x)
    (z : P.X) (next : P.Y z) :
    P.stepStagePMF ⟨x, y⟩ ⟨z, next⟩ = P.move x y z * P.choose z next := by
  rw [DiscreteDecisionProcess.stepStagePMF, PMF.bind_apply]
  change (∑' state, P.move x y state * P.initialStagePMF state ⟨z, next⟩) = _
  calc
    _ = P.move x y z * P.initialStagePMF z ⟨z, next⟩ := by
      apply tsum_eq_single z
      intro other hother
      rw [P.initialStagePMF_apply_of_ne next hother]
      simp
    _ = P.move x y z * P.choose z next := by rw [P.initialStagePMF_apply]

/-- The homogeneous Ionescu--Tulcea kernel associated with the DDP stage transition. -/
private def DiscreteDecisionProcess.stageKernel (P : DiscreteDecisionProcess) (n : ℕ) :
    Kernel (∀ _ : Finset.Iic n, DDPStage P) (DDPStage P) where
  toFun history :=
    (P.stepStagePMF (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure
  measurable' := Measurable.of_discrete

private instance DiscreteDecisionProcess.isMarkovKernel_stageKernel
    (P : DiscreteDecisionProcess) (n : ℕ) : IsMarkovKernel (P.stageKernel n) :=
  ⟨fun _ => PMF.toMeasure.isProbabilityMeasure _⟩

/-- Evaluation of one abstract Ionescu--Tulcea step on a finite history. -/
private theorem partialTraj_succ_self_apply_ddp {Stage : ℕ → Type*}
    [∀ n, MeasurableSpace (Stage n)]
    {kernel : (n : ℕ) → Kernel (∀ i : Finset.Iic n, Stage i) (Stage (n + 1))}
    [∀ n, IsMarkovKernel (kernel n)] (n : ℕ) (coords : ∀ i : Finset.Iic n, Stage i) :
    Kernel.partialTraj kernel n (n + 1) coords =
      (kernel n coords).map fun next =>
        IicProdIoc n (n + 1) (coords, MeasurableEquiv.piSingleton n next) := by
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _ measurable_IicProdIoc,
    Kernel.prod_apply, Kernel.id_apply,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton n).measurable,
    Measure.dirac_prod, Measure.map_map measurable_IicProdIoc (by fun_prop),
    Measure.map_map (by fun_prop) (MeasurableEquiv.piSingleton n).measurable]
  rfl

/-- One local transition-kernel step is the finite DDP coordinate extension. -/
private theorem DiscreteDecisionProcess.stageKernel_partialTraj_succ_self
    (P : DiscreteDecisionProcess) (n : ℕ)
    (coords : ∀ _ : Finset.Iic n, DDPStage P) :
    Kernel.partialTraj (X := fun _ : ℕ => DDPStage P) P.stageKernel n (n + 1) coords =
      ((P.stepStagePMF (coords ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).map
        (P.extendDDPCoords coords)).toMeasure := by
  have hfg : (fun next : DDPStage P =>
      IicProdIoc (X := fun _ : ℕ => DDPStage P) n (n + 1)
        (coords, MeasurableEquiv.piSingleton
          (X := fun _ : ℕ => DDPStage P) n next)) = P.extendDDPCoords coords := by
    funext next i
    by_cases hi : i.1 ≤ n
    · simp [IicProdIoc, DiscreteDecisionProcess.extendDDPCoords, hi]
    · have hlast : i.1 = n + 1 := by
        have := Finset.mem_Iic.mp i.2
        omega
      rw [show i = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ from Subtype.ext hlast]
      simp [IicProdIoc, MeasurableEquiv.piSingleton,
        DiscreteDecisionProcess.extendDDPCoords]
  refine (partialTraj_succ_self_apply_ddp
    (Stage := fun _ : ℕ => DDPStage P) (kernel := P.stageKernel) n coords).trans ?_
  change Measure.map (fun next : DDPStage P =>
      IicProdIoc (X := fun _ : ℕ => DDPStage P) n (n + 1)
        (coords, MeasurableEquiv.piSingleton
          (X := fun _ : ℕ => DDPStage P) n next))
      (P.stepStagePMF (coords ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure = _
  rw [hfg]
  exact PMF.toMeasure_map (P.extendDDPCoords coords)
    (P.stepStagePMF (coords ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
    (measurable_of_countable _)

/-- The singleton-coordinate start measure used by the local transition kernel. -/
private def DiscreteDecisionProcess.stageKernelStartMeasure
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) :
    Measure (∀ _ : Finset.Iic 0, DDPStage P) :=
  initial.toMeasure.map
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => DDPStage P)).symm

/-- The local transition kernel and the finite DDP recursion have the same marginals. -/
private theorem DiscreteDecisionProcess.bind_partialTraj_stageKernel_eq_ddpCoords
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) (t : ℕ) :
    Measure.bind (P.stageKernelStartMeasure initial)
        (Kernel.partialTraj (X := fun _ : ℕ => DDPStage P) P.stageKernel 0 t) =
      (P.ddpCoordsDistFromStagePMF initial t).toMeasure := by
  induction t with
  | zero =>
      rw [Kernel.partialTraj_self]
      have hid : (⇑(Kernel.id (α := ∀ _ : Finset.Iic 0, DDPStage P))) =
          Measure.dirac := by
        funext coords
        exact Kernel.id_apply coords
      rw [hid, Measure.bind_dirac]
      unfold DiscreteDecisionProcess.stageKernelStartMeasure
        DiscreteDecisionProcess.ddpCoordsDistFromStagePMF
      exact PMF.toMeasure_map (fun stage (_ : Finset.Iic 0) => stage) initial
        (measurable_of_countable _)
  | succ t ih =>
      have heq : Kernel.partialTraj (X := fun _ : ℕ => DDPStage P)
          P.stageKernel 0 (t + 1) =
          Kernel.partialTraj (X := fun _ : ℕ => DDPStage P)
              P.stageKernel t (t + 1) ∘ₖ
            Kernel.partialTraj (X := fun _ : ℕ => DDPStage P) P.stageKernel 0 t :=
        Kernel.partialTraj_succ_eq_comp (Nat.zero_le t)
      have hcomp :
          (⇑(Kernel.partialTraj (X := fun _ : ℕ => DDPStage P)
              P.stageKernel t (t + 1) ∘ₖ
            Kernel.partialTraj (X := fun _ : ℕ => DDPStage P) P.stageKernel 0 t)) =
          fun coords => Measure.bind
            (Kernel.partialTraj (X := fun _ : ℕ => DDPStage P)
              P.stageKernel 0 t coords)
            (Kernel.partialTraj (X := fun _ : ℕ => DDPStage P)
              P.stageKernel t (t + 1)) :=
        funext fun coords => Kernel.comp_apply _ _ coords
      rw [heq, hcomp,
        ← Measure.bind_bind (Kernel.measurable _).aemeasurable
          (Kernel.measurable _).aemeasurable, ih]
      have hfun :
          (⇑(Kernel.partialTraj (X := fun _ : ℕ => DDPStage P)
            P.stageKernel t (t + 1))) =
            fun coords => ((P.stepStagePMF
              (coords ⟨t, Finset.mem_Iic.mpr le_rfl⟩)).map
                (P.extendDDPCoords coords)).toMeasure :=
        funext (P.stageKernel_partialTraj_succ_self t)
      rw [hfun, GameTheory.StochasticGame.measureBind_toMeasure_eq]
      rfl

/-- Every finite marginal of the local transition-kernel trajectory is the finite DDP
coordinate recursion. -/
private theorem DiscreteDecisionProcess.map_frestrictLe_stageKernelTrajMeasure
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) (t : ℕ) :
    (Kernel.trajMeasure (X := fun _ : ℕ => DDPStage P)
        initial.toMeasure P.stageKernel).map
        (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) t) =
      (P.ddpCoordsDistFromStagePMF initial t).toMeasure := by
  unfold Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop)]
  rw [Kernel.traj_map_frestrictLe]
  exact P.bind_partialTraj_stageKernel_eq_ddpCoords initial t

/-- The decoded production law is exactly the local transition-kernel trajectory law. -/
private theorem DiscreteDecisionProcess.productionRawLawWithInitial_eq_stageKernelTrajMeasure
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) :
    P.productionRawLawWithInitial initial =
      Kernel.trajMeasure (X := fun _ : ℕ => DDPStage P)
        initial.toMeasure P.stageKernel := by
  let finiteLaw : (n : ℕ) → Measure (∀ _ : Finset.Iic n, DDPStage P) :=
    fun n => (P.ddpCoordsDistFromStagePMF initial n).toMeasure
  have hprojective : ∀ a b : ℕ, ∀ hab : a ≤ b,
      (finiteLaw b).map (Preorder.frestrictLe₂ (π := fun _ : ℕ => DDPStage P) hab) =
        finiteLaw a := by
    intro a b hab
    dsimp only [finiteLaw]
    rw [← P.map_frestrictLe_productionRawLawWithInitial initial b]
    rw [Measure.map_map (Preorder.measurable_frestrictLe₂ hab)
      (Preorder.measurable_frestrictLe b)]
    rw [Preorder.frestrictLe₂_comp_frestrictLe hab]
    exact P.map_frestrictLe_productionRawLawWithInitial initial a
  let family : (I : Finset ℕ) → Measure (∀ i : I, DDPStage P) :=
    MeasureTheory.inducedFamily (X := fun _ : ℕ => DDPStage P) finiteLaw
  have hfamily : IsProjectiveMeasureFamily
      (α := fun _ : ℕ => DDPStage P) family := by
    dsimp only [family]
    exact MeasureTheory.isProjectiveMeasureFamily_inducedFamily
      (X := fun _ : ℕ => DDPStage P) finiteLaw hprojective
  letI : ∀ I, IsFiniteMeasure (family I) := fun I => by
    dsimp only [family, finiteLaw, MeasureTheory.inducedFamily]
    infer_instance
  have hproduction : IsProjectiveLimit (P.productionRawLawWithInitial initial)
      family :=
    (MeasureTheory.isProjectiveLimit_nat_iff hfamily _).2 fun n => by
      change (P.productionRawLawWithInitial initial).map
          (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n) =
        MeasureTheory.inducedFamily (X := fun _ : ℕ => DDPStage P)
          finiteLaw (Finset.Iic n)
      rw [MeasureTheory.inducedFamily_Iic]
      exact P.map_frestrictLe_productionRawLawWithInitial initial n
  have hkernel : IsProjectiveLimit
      (Kernel.trajMeasure (X := fun _ : ℕ => DDPStage P)
        initial.toMeasure P.stageKernel)
      family :=
    (MeasureTheory.isProjectiveLimit_nat_iff hfamily _).2 fun n => by
      change (Kernel.trajMeasure (X := fun _ : ℕ => DDPStage P)
          initial.toMeasure P.stageKernel).map
          (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n) =
        MeasureTheory.inducedFamily (X := fun _ : ℕ => DDPStage P)
          finiteLaw (Finset.Iic n)
      rw [MeasureTheory.inducedFamily_Iic]
      exact P.map_frestrictLe_stageKernelTrajMeasure initial n
  exact hproduction.unique hkernel

/-- The martingale-difference contribution attached to one sampled DDP stage. -/
private def DDPStage.increment (P : DiscreteDecisionProcess) (stage : DDPStage P) : ℝ :=
  P.valueY stage.1 stage.2 - P.valueX stage.1

/-- Every sampled-stage increment is bounded by the process's displayed value bound. -/
private theorem DDPStage.norm_increment_le (P : DiscreteDecisionProcess)
    (stage : DDPStage P) :
    ‖stage.increment P‖ ≤ P.valueDifferenceBound := by
  simpa only [DDPStage.increment, Real.norm_eq_abs] using
    (P.valueDifference stage.1 stage.1 stage.2 stage.2).2.1

/-- A bounded real function is summable against the real weights of a PMF. -/
private theorem PMF.summable_toReal_mul_of_norm_le {A : Type*}
    (p : PMF A) (f : A → ℝ) {C : ℝ} (hf : ∀ a, ‖f a‖ ≤ C) :
    Summable fun a => (p a).toReal * f a := by
  have hweights : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; simp)
  apply Summable.of_norm_bounded (hweights.mul_right C)
  intro a
  rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hf a) ENNReal.toReal_nonneg

/-- The real weights of a PMF sum to one. -/
private theorem PMF.tsum_toReal {A : Type*} (p : PMF A) :
    ∑' a, (p a).toReal = 1 := by
  have h := ENNReal.tsum_toReal_eq (f := fun a => p a)
    (PMF.apply_ne_top p)
  rw [PMF.tsum_coe] at h
  simpa using h.symm

/-- Harmonicity at an `X`-state says that the sampled decision increment has mean zero. -/
private theorem DiscreteDecisionProcess.tsum_choose_mul_increment_eq_zero
    (P : DiscreteDecisionProcess) (x : P.X) :
    ∑' y, (P.choose x y).toReal *
      (P.valueY x y - P.valueX x) = 0 := by
  have hvalueY : ∀ y : P.Y x,
      ‖P.valueY x y‖ ≤ ‖P.valueX x‖ + P.valueDifferenceBound := by
    intro y
    calc
      ‖P.valueY x y‖ ≤ ‖P.valueY x y - P.valueX x‖ + ‖P.valueX x‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (P.valueY x y - P.valueX x) (P.valueX x)
      _ ≤ P.valueDifferenceBound + ‖P.valueX x‖ := by
        gcongr
        simpa only [Real.norm_eq_abs] using
          (P.valueDifference x x y y).2.1
      _ = ‖P.valueX x‖ + P.valueDifferenceBound := by ring
  have hweightedValue := PMF.summable_toReal_mul_of_norm_le
    (P.choose x) (fun y => P.valueY x y) hvalueY
  have hweights : Summable fun y => (P.choose x y).toReal :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; simp)
  simp_rw [mul_sub]
  rw [hweightedValue.tsum_sub (hweights.mul_right (P.valueX x))]
  rw [← P.harmonicX x]
  rw [Summable.tsum_mul_right (P.valueX x) hweights]
  rw [PMF.tsum_toReal (P.choose x)]
  ring

/-- Under the stage kernel, the next sampled decision increment has conditional mean zero. -/
private theorem DiscreteDecisionProcess.integral_increment_stageKernel_eq_zero
    (P : DiscreteDecisionProcess) (n : ℕ)
    (history : ∀ _ : Finset.Iic n, DDPStage P) :
    ∫ stage, stage.increment P ∂P.stageKernel n history = 0 := by
  let current := history ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  have hintegrable : Integrable (DDPStage.increment P)
      (P.stepStagePMF current).toMeasure := by
    letI : IsProbabilityMeasure (P.stepStagePMF current).toMeasure :=
      PMF.toMeasure.isProbabilityMeasure _
    exact Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable
      P.valueDifferenceBound
      (ae_of_all _ fun stage => stage.norm_increment_le P)
  have hsummable : Summable fun stage : DDPStage P =>
      (P.stepStagePMF current stage).toReal * stage.increment P :=
    PMF.summable_toReal_mul_of_norm_le (P.stepStagePMF current)
      (DDPStage.increment P) (fun stage => stage.norm_increment_le P)
  change ∫ stage, stage.increment P ∂(P.stepStagePMF current).toMeasure = 0
  rw [PMF.integral_eq_tsum _ _ hintegrable]
  simp only [smul_eq_mul]
  rw [hsummable.tsum_sigma]
  have hzero : ∀ x, (∑' y : P.Y x,
      (P.stepStagePMF current ⟨x, y⟩).toReal *
        DDPStage.increment P ⟨x, y⟩) = 0 := by
    intro x
    have hinner : Summable fun y : P.Y x =>
        (P.choose x y).toReal * (P.valueY x y - P.valueX x) :=
      PMF.summable_toReal_mul_of_norm_le (P.choose x)
        (fun y => P.valueY x y - P.valueX x) (fun y => by
          simpa only [Real.norm_eq_abs] using
            (P.valueDifference x x y y).2.1)
    simp_rw [P.stepStagePMF_apply, ENNReal.toReal_mul, DDPStage.increment]
    simp_rw [mul_assoc]
    rw [Summable.tsum_mul_left (P.move current.1 current.2 x).toReal hinner]
    rw [P.tsum_choose_mul_increment_eq_zero x, mul_zero]
  simp_rw [hzero]
  simp

/-- Harmonicity makes the sampled `Y`-value invariant under one complete DDP step. -/
private theorem DiscreteDecisionProcess.integral_valueY_stageKernel
    (P : DiscreteDecisionProcess) (n : ℕ)
    (history : ∀ _ : Finset.Iic n, DDPStage P) :
    ∫ next, P.valueY next.1 next.2 ∂P.stageKernel n history =
      P.valueY (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1
        (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 := by
  let current := history ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  have hbound : ∀ next : DDPStage P,
      ‖P.valueY next.1 next.2‖ ≤
        ‖P.valueY current.1 current.2‖ + P.valueDifferenceBound := by
    intro next
    calc
      ‖P.valueY next.1 next.2‖ ≤
          ‖P.valueY next.1 next.2 - P.valueY current.1 current.2‖ +
            ‖P.valueY current.1 current.2‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (P.valueY next.1 next.2 - P.valueY current.1 current.2)
            (P.valueY current.1 current.2)
      _ ≤ P.valueDifferenceBound + ‖P.valueY current.1 current.2‖ := by
        gcongr
        simpa only [Real.norm_eq_abs, abs_sub_comm] using
          (P.valueDifference current.1 next.1 current.2 next.2).2.2
      _ = _ := by ring
  have hintegrable : Integrable (fun next : DDPStage P => P.valueY next.1 next.2)
      (P.stepStagePMF current).toMeasure := by
    letI : IsProbabilityMeasure (P.stepStagePMF current).toMeasure :=
      PMF.toMeasure.isProbabilityMeasure _
    exact Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable
      (‖P.valueY current.1 current.2‖ + P.valueDifferenceBound)
      (ae_of_all _ hbound)
  have hsummable : Summable fun next : DDPStage P =>
      (P.stepStagePMF current next).toReal * P.valueY next.1 next.2 :=
    PMF.summable_toReal_mul_of_norm_le (P.stepStagePMF current)
      (fun next => P.valueY next.1 next.2) hbound
  change (∫ next, P.valueY next.1 next.2 ∂(P.stepStagePMF current).toMeasure) = _
  rw [PMF.integral_eq_tsum _ _ hintegrable]
  simp only [smul_eq_mul]
  rw [hsummable.tsum_sigma]
  have hinner (x : P.X) :
      (∑' y : P.Y x,
        (P.stepStagePMF current ⟨x, y⟩).toReal * P.valueY x y) =
        (P.move current.1 current.2 x).toReal * P.valueX x := by
    have hvalueBound : ∀ y : P.Y x,
        ‖P.valueY x y‖ ≤ ‖P.valueX x‖ + P.valueDifferenceBound := by
      intro y
      calc
        ‖P.valueY x y‖ ≤ ‖P.valueY x y - P.valueX x‖ + ‖P.valueX x‖ := by
          simpa only [sub_add_cancel] using
            norm_add_le (P.valueY x y - P.valueX x) (P.valueX x)
        _ ≤ P.valueDifferenceBound + ‖P.valueX x‖ := by
          gcongr
          simpa only [Real.norm_eq_abs] using (P.valueDifference x x y y).2.1
        _ = _ := by ring
    have hsummableY : Summable fun y : P.Y x =>
        (P.choose x y).toReal * P.valueY x y :=
      PMF.summable_toReal_mul_of_norm_le (P.choose x) (P.valueY x) hvalueBound
    simp_rw [P.stepStagePMF_apply, ENNReal.toReal_mul, mul_assoc]
    rw [Summable.tsum_mul_left (P.move current.1 current.2 x).toReal hsummableY]
    rw [← P.harmonicX x]
  simp_rw [hinner]
  exact P.harmonicY current.1 current.2 |>.symm

/-- The raw infinite stage law is the decoded production stochastic-game law generated from
an arbitrary initial sampled-stage distribution. -/
private def DiscreteDecisionProcess.rawLawWithInitial
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) :
    Measure (ℕ → DDPStage P) :=
  P.productionRawLawWithInitial initial

private instance DiscreteDecisionProcess.isProbabilityMeasure_rawLawWithInitial
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) :
    IsProbabilityMeasure (P.rawLawWithInitial initial) := by
  unfold DiscreteDecisionProcess.rawLawWithInitial
  infer_instance

/-- The raw infinite stage law of the DDP started at `x`. -/
private def DiscreteDecisionProcess.rawLawFrom
    (P : DiscreteDecisionProcess) (x : P.X) : Measure (ℕ → DDPStage P) :=
  P.rawLawWithInitial (P.initialStagePMF x)

private instance DiscreteDecisionProcess.isProbabilityMeasure_rawLawFrom
    (P : DiscreteDecisionProcess) (x : P.X) :
    IsProbabilityMeasure (P.rawLawFrom x) := by
  unfold DiscreteDecisionProcess.rawLawFrom
  infer_instance

/-- The sampled-stage type is inhabited because its initial-stage PMF has nonempty support. -/
private instance ddpStageNonempty (P : DiscreteDecisionProcess) : Nonempty (DDPStage P) :=
  ⟨Classical.choose (P.initialStagePMF P.initial).support_nonempty⟩

/-- The harmonic value carried by the sampled action at raw stage `n`. -/
private def DiscreteDecisionProcess.rawStageValue
    (P : DiscreteDecisionProcess) (n : ℕ) (stage : ℕ → DDPStage P) : ℝ :=
  P.valueY (stage n).1 (stage n).2

private theorem DiscreteDecisionProcess.rawStageValue_stronglyAdapted
    (P : DiscreteDecisionProcess) :
    StronglyAdapted (Filtration.piLE (X := fun _ : ℕ => DDPStage P)) P.rawStageValue := by
  intro n
  rw [Filtration.piLE_eq_comap_frestrictLe]
  apply Measurable.stronglyMeasurable
  have hvalue : Measurable (fun stage : DDPStage P => P.valueY stage.1 stage.2) :=
    Measurable.of_discrete
  exact hvalue.comp
    ((measurable_pi_apply (X := fun _ : Finset.Iic n => DDPStage P)
      ⟨n, Finset.mem_Iic.mpr le_rfl⟩).comp
        (comap_measurable (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n)))

private theorem DiscreteDecisionProcess.integrable_rawStageValue
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) (n : ℕ) :
    Integrable (P.rawStageValue n) (P.rawLawWithInitial initial) := by
  let initialAction := Classical.choose (P.choose P.initial).support_nonempty
  have hbound (stage : ℕ → DDPStage P) :
      ‖P.rawStageValue n stage‖ ≤ ‖P.valueX P.initial‖ + P.valueDifferenceBound := by
    calc
      ‖P.rawStageValue n stage‖ ≤
          ‖P.rawStageValue n stage - P.valueX P.initial‖ + ‖P.valueX P.initial‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (P.rawStageValue n stage - P.valueX P.initial) (P.valueX P.initial)
      _ ≤ P.valueDifferenceBound + ‖P.valueX P.initial‖ := by
        gcongr
        simpa only [DiscreteDecisionProcess.rawStageValue, Real.norm_eq_abs] using
          (P.valueDifference (stage n).1 P.initial (stage n).2 initialAction).2.1
      _ = _ := by ring
  exact Integrable.of_bound
    ((P.rawStageValue_stronglyAdapted n).mono
      (Filtration.le (Filtration.piLE (X := fun _ : ℕ => DDPStage P)) n)
        |>.aestronglyMeasurable)
    (‖P.valueX P.initial‖ + P.valueDifferenceBound) (ae_of_all _ hbound)

/-- The sampled action values form a martingale under every raw initial-stage law. -/
private theorem DiscreteDecisionProcess.rawStageValue_martingale
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) :
    Martingale P.rawStageValue (Filtration.piLE (X := fun _ : ℕ => DDPStage P))
      (P.rawLawWithInitial initial) := by
  let filtration := Filtration.piLE (X := fun _ : ℕ => DDPStage P)
  apply martingale_of_condExp_sub_eq_zero_nat P.rawStageValue_stronglyAdapted
    (P.integrable_rawStageValue initial)
  intro n
  let nextValue : DDPStage P → ℝ := fun next => P.valueY next.1 next.2
  have hnext : P.rawStageValue (n + 1) =
      fun stage : ℕ → DDPStage P => nextValue (stage (n + 1)) := rfl
  have hconditional := condExp_ae_eq_integral_condDistrib
    (μ := P.rawLawWithInitial initial)
    (X := Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n)
    (Y := fun stage : ℕ → DDPStage P => stage (n + 1))
    (f := nextValue)
    (Preorder.measurable_frestrictLe (X := fun _ : ℕ => DDPStage P) n)
    (measurable_pi_apply (n + 1)).aemeasurable
    Measurable.of_discrete.stronglyMeasurable (P.integrable_rawStageValue initial (n + 1))
  have hkernel := Kernel.condDistrib_trajMeasure
    (X := fun _ : ℕ => DDPStage P) (μ₀ := initial.toMeasure)
    (κ := P.stageKernel) (a := n)
  have hkernelOnPath := ae_of_ae_map
    (Preorder.measurable_frestrictLe
      (X := fun _ : ℕ => DDPStage P) n).aemeasurable hkernel
  have hraw : Kernel.trajMeasure (X := fun _ : ℕ => DDPStage P)
      initial.toMeasure P.stageKernel = P.rawLawWithInitial initial := by
    simpa only [DiscreteDecisionProcess.rawLawWithInitial] using
      (P.productionRawLawWithInitial_eq_stageKernelTrajMeasure initial).symm
  simp only [hraw] at hkernelOnPath
  have hfiltration : filtration n = MeasurableSpace.comap
      (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n) inferInstance :=
    Filtration.piLE_eq_comap_frestrictLe n
  rw [hfiltration]
  have hsub := condExp_sub (P.integrable_rawStageValue initial (n + 1))
    (P.integrable_rawStageValue initial n)
    (MeasurableSpace.comap
      (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n) inferInstance)
  have hcurrent : (P.rawLawWithInitial initial)[P.rawStageValue n |
      MeasurableSpace.comap
        (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n) inferInstance] =
      P.rawStageValue n := by
    have hle : MeasurableSpace.comap
        (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n) inferInstance ≤
        (inferInstance : MeasurableSpace (ℕ → DDPStage P)) := by
      rw [← hfiltration]
      exact filtration.le n
    apply condExp_of_stronglyMeasurable hle
    · rw [← hfiltration]
      exact P.rawStageValue_stronglyAdapted n
    · exact P.integrable_rawStageValue initial n
  rw [hcurrent] at hsub
  rw [hnext] at hsub
  rw [hnext]
  filter_upwards [hsub, hconditional, hkernelOnPath] with stage hsub' hconditional' hkernel'
  rw [hsub']
  change (P.rawLawWithInitial initial)[fun path => nextValue (path (n + 1)) |
      MeasurableSpace.comap
        (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n) inferInstance] stage -
      P.rawStageValue n stage = 0
  have hconditionalPoint :
      (P.rawLawWithInitial initial)[fun path => nextValue (path (n + 1)) |
        MeasurableSpace.comap
          (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n) inferInstance] stage =
        ∫ next, nextValue next ∂
          (condDistrib (fun path : ℕ → DDPStage P => path (n + 1))
            (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n)
            (P.rawLawWithInitial initial)) (Preorder.frestrictLe n stage) := hconditional'
  rw [hconditionalPoint]
  change (condDistrib (fun path : ℕ → DDPStage P => path (n + 1))
      (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n)
      (P.rawLawWithInitial initial))
      (Preorder.frestrictLe n stage) =
        P.stageKernel n (Preorder.frestrictLe n stage) at hkernel'
  rw [hkernel', P.integral_valueY_stageKernel]
  simp [DiscreteDecisionProcess.rawStageValue]

/-- The raw state-coordinate process is adapted to the finite-coordinate filtration. -/
private theorem DiscreteDecisionProcess.rawState_adapted
    (P : DiscreteDecisionProcess) :
    Adapted (Filtration.piLE (X := fun _ : ℕ => DDPStage P))
      (fun n stage => (stage n).1) := by
  intro n
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact Measurable.of_discrete.comp
    ((measurable_pi_apply (X := fun _ : Finset.Iic n => DDPStage P)
      ⟨n, Finset.mem_Iic.mpr le_rfl⟩).comp
        (comap_measurable (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n)))

/-- Cumulative sampled-stage increments through stage `n` on the raw trajectory space. -/
private def DiscreteDecisionProcess.rawAdvantage
    (P : DiscreteDecisionProcess) (stage : ℕ → DDPStage P) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), DDPStage.increment P (stage i)

/-- The raw cumulative advantage is strongly adapted to the finite-coordinate filtration. -/
private theorem DiscreteDecisionProcess.rawAdvantage_stronglyAdapted
    (P : DiscreteDecisionProcess) :
    StronglyAdapted (Filtration.piLE (X := fun _ : ℕ => DDPStage P))
      (fun n stage => P.rawAdvantage stage n) := by
  intro n
  change StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => DDPStage P) n]
    (fun stage => ∑ i ∈ Finset.range (n + 1), DDPStage.increment P (stage i))
  have hsum : StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => DDPStage P) n]
      (∑ i ∈ Finset.range (n + 1),
        fun stage : ℕ → DDPStage P => DDPStage.increment P (stage i)) := by
    refine Finset.stronglyMeasurable_sum (M := ℝ)
      (f := fun i (stage : ℕ → DDPStage P) => DDPStage.increment P (stage i))
      (Finset.range (n + 1)) ?_
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Filtration.piLE_eq_comap_frestrictLe]
    apply Measurable.stronglyMeasurable
    have hincrement : Measurable (DDPStage.increment P) :=
      Measurable.of_discrete
    exact hincrement.comp
      ((measurable_pi_apply (X := fun _ : Finset.Iic n => DDPStage P)
          ⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ hi)⟩).comp
        (comap_measurable
          (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n)))
  convert hsum using 1
  ext stage
  simp only [Finset.sum_apply]

/-- The next raw cumulative-advantage increment is the next sampled-stage increment. -/
private theorem DiscreteDecisionProcess.rawAdvantage_succ_sub
    (P : DiscreteDecisionProcess) (stage : ℕ → DDPStage P) (n : ℕ) :
    P.rawAdvantage stage (n + 1) - P.rawAdvantage stage n =
      DDPStage.increment P (stage (n + 1)) := by
  rw [DiscreteDecisionProcess.rawAdvantage, DiscreteDecisionProcess.rawAdvantage]
  rw [Finset.sum_range_succ]
  ring

/-- A finite raw cumulative advantage is bounded by the number of sampled increments. -/
private theorem DiscreteDecisionProcess.norm_rawAdvantage_le
    (P : DiscreteDecisionProcess) (stage : ℕ → DDPStage P) (n : ℕ) :
    ‖P.rawAdvantage stage n‖ ≤ (n + 1) * P.valueDifferenceBound := by
  rw [DiscreteDecisionProcess.rawAdvantage]
  calc
    ‖∑ i ∈ Finset.range (n + 1), DDPStage.increment P (stage i)‖ ≤
        ∑ i ∈ Finset.range (n + 1), ‖DDPStage.increment P (stage i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (n + 1), P.valueDifferenceBound := by
      gcongr with i hi
      exact (stage i).norm_increment_le P
    _ = (n + 1) * P.valueDifferenceBound := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      rfl

/-- Every finite raw cumulative advantage is integrable. -/
private theorem DiscreteDecisionProcess.integrable_rawAdvantage
    (P : DiscreteDecisionProcess) (n : ℕ) :
    Integrable (fun stage => P.rawAdvantage stage n) (P.rawLawFrom P.initial) := by
  exact Integrable.of_bound
    ((P.rawAdvantage_stronglyAdapted n).mono
      (Filtration.le (Filtration.piLE (X := fun _ : ℕ => DDPStage P)) n)
        |>.aestronglyMeasurable)
    ((n + 1) * P.valueDifferenceBound)
    (ae_of_all _ fun stage => P.norm_rawAdvantage_le stage n)

/-- The raw cumulative advantages form the martingale used in Proposition 1. -/
private theorem DiscreteDecisionProcess.rawAdvantage_martingale
    (P : DiscreteDecisionProcess) :
    Martingale (fun n stage => P.rawAdvantage stage n)
      (Filtration.piLE (X := fun _ : ℕ => DDPStage P))
      (P.rawLawFrom P.initial) := by
  let filtration := Filtration.piLE (X := fun _ : ℕ => DDPStage P)
  apply martingale_of_condExp_sub_eq_zero_nat P.rawAdvantage_stronglyAdapted
    P.integrable_rawAdvantage
  intro n
  have hdifference :
      ((fun stage : ℕ → DDPStage P => P.rawAdvantage stage (n + 1)) -
        fun stage => P.rawAdvantage stage n) =
      fun stage => DDPStage.increment P (stage (n + 1)) := by
    funext stage
    exact P.rawAdvantage_succ_sub stage n
  have hincrement : Integrable
      (fun stage : ℕ → DDPStage P => DDPStage.increment P (stage (n + 1)))
      (P.rawLawFrom P.initial) := by
    apply Integrable.congr
      ((P.integrable_rawAdvantage (n + 1)).sub (P.integrable_rawAdvantage n))
    exact ae_of_all _ fun stage => P.rawAdvantage_succ_sub stage n
  have hconditional := condExp_ae_eq_integral_condDistrib
    (μ := P.rawLawFrom P.initial)
    (X := Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n)
    (Y := fun stage : ℕ → DDPStage P => stage (n + 1))
    (f := DDPStage.increment P)
    (Preorder.measurable_frestrictLe
      (X := fun _ : ℕ => DDPStage P) n)
    (measurable_pi_apply (n + 1)).aemeasurable
    Measurable.of_discrete.stronglyMeasurable hincrement
  have hkernel := Kernel.condDistrib_trajMeasure
    (X := fun _ : ℕ => DDPStage P)
    (μ₀ := (P.initialStagePMF P.initial).toMeasure)
    (κ := P.stageKernel) (a := n)
  have hkernelOnPath := ae_of_ae_map
    (Preorder.measurable_frestrictLe
      (X := fun _ : ℕ => DDPStage P) n).aemeasurable hkernel
  have hraw : Kernel.trajMeasure (X := fun _ : ℕ => DDPStage P)
      (P.initialStagePMF P.initial).toMeasure P.stageKernel = P.rawLawFrom P.initial := by
    simpa only [DiscreteDecisionProcess.rawLawFrom,
      DiscreteDecisionProcess.rawLawWithInitial] using
      (P.productionRawLawWithInitial_eq_stageKernelTrajMeasure
        (P.initialStagePMF P.initial)).symm
  simp only [hraw] at hkernelOnPath
  rw [show filtration n =
      MeasurableSpace.comap
        (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n) inferInstance by
    exact Filtration.piLE_eq_comap_frestrictLe n]
  filter_upwards [hconditional, hkernelOnPath] with stage hconditional' hkernel'
  rw [hdifference]
  rw [hconditional']
  change (condDistrib (fun path : ℕ → DDPStage P => path (n + 1))
      (Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) n)
      (P.rawLawFrom P.initial))
      (Preorder.frestrictLe n stage) =
        P.stageKernel n (Preorder.frestrictLe n stage) at hkernel'
  rw [hkernel', P.integral_increment_stageKernel_eq_zero]
  rfl

/-- Squaring an integrable square-integrable real martingale gives a submartingale. -/
private theorem martingale_square_submartingale
    {Omega : Type*} {m : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration ℕ m} {f : ℕ → Omega → ℝ} [IsFiniteMeasure mu]
    (hf : Martingale f F mu)
    (hsq : ∀ n, Integrable (fun w => (f n w) ^ 2) mu) :
    Submartingale (fun n w => (f n w) ^ 2) F mu := by
  refine ⟨fun n => (hf.stronglyMeasurable n).pow 2, ?_, hsq⟩
  intro i j hij
  have hjensen := (even_two.convexOn_pow (𝕜 := ℝ)).map_condExp_le_univ
    (F.le i) (continuous_id.pow 2).lowerSemicontinuous (hf.integrable j) (hsq j)
  filter_upwards [hf.2 i j hij, hjensen] with w hmart hjensen'
  rw [← hmart]
  exact hjensen'

/-- The square expectation of a real martingale is the sum of increment variances. -/
private theorem martingale_square_integral_eq
    {Omega : Type*} {m : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration ℕ m} {f : ℕ → Omega → ℝ} [IsFiniteMeasure mu]
    (hf : Martingale f F mu)
    (hsq : ∀ n, Integrable (fun w => (f n w) ^ 2) mu)
    (hcross : ∀ n, Integrable (fun w => f n w * f (n + 1) w) mu)
    (n : ℕ) :
    (∫ w, (f n w) ^ 2 ∂mu) =
      (∫ w, (f 0 w) ^ 2 ∂mu) +
        ∑ i ∈ Finset.range n, ∫ w, (f (i + 1) w - f i w) ^ 2 ∂mu := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero]
  | succ n ih =>
      have hmul :
          (∫ w, f n w * f (n + 1) w ∂mu) = ∫ w, (f n w) ^ 2 ∂mu := by
        calc
          _ = ∫ w, mu[fun z => f n z * f (n + 1) z | F n] w ∂mu :=
            (integral_condExp (F.le n)).symm
          _ = ∫ w, f n w * mu[f (n + 1) | F n] w ∂mu := by
            apply integral_congr_ae
            exact condExp_mul_of_stronglyMeasurable_left (m := F n)
              (hf.stronglyMeasurable n) (hcross n) (hf.integrable (n + 1))
          _ = ∫ w, (f n w) ^ 2 ∂mu := by
            apply integral_congr_ae
            filter_upwards [hf.2 n (n + 1) n.le_succ] with w hw
            rw [hw, pow_two]
      have hincrement :
          (∫ w, (f (n + 1) w - f n w) ^ 2 ∂mu) =
            (∫ w, (f (n + 1) w) ^ 2 ∂mu) -
              2 * (∫ w, f n w * f (n + 1) w ∂mu) +
                ∫ w, (f n w) ^ 2 ∂mu := by
        have hpoint : (fun w => (f (n + 1) w - f n w) ^ 2) =
            fun w => (f (n + 1) w) ^ 2 -
              2 * (f n w * f (n + 1) w) + (f n w) ^ 2 := by
          funext w
          ring
        rw [hpoint]
        change (∫ w, (((fun z => (f (n + 1) z) ^ 2) -
          (fun z => 2 * (f n z * f (n + 1) z))) +
            fun z => (f n z) ^ 2) w ∂mu) = _
        calc
          _ = (∫ w, ((fun z => (f (n + 1) z) ^ 2) -
                (fun z => 2 * (f n z * f (n + 1) z))) w ∂mu) +
              ∫ w, (f n w) ^ 2 ∂mu :=
            integral_add ((hsq (n + 1)).sub ((hcross n).const_mul 2)) (hsq n)
          _ = _ := by
            have hsub := integral_sub (hsq (n + 1)) ((hcross n).const_mul 2)
            have hmul2 := integral_const_mul (μ := mu) (r := 2)
              (f := fun w => f n w * f (n + 1) w)
            change (∫ w, (f (n + 1) w) ^ 2 -
              2 * (f n w * f (n + 1) w) ∂mu) +
                ∫ w, (f n w) ^ 2 ∂mu = _
            rw [hsub, hmul2]
      rw [Finset.sum_range_succ]
      calc
        (∫ w, (f (n + 1) w) ^ 2 ∂mu) =
            (∫ w, (f n w) ^ 2 ∂mu) +
              ∫ w, (f (n + 1) w - f n w) ^ 2 ∂mu := by
                rw [hincrement, hmul]
                ring
        _ = ((∫ w, (f 0 w) ^ 2 ∂mu) +
              ∑ i ∈ Finset.range n,
                ∫ w, (f (i + 1) w - f i w) ^ 2 ∂mu) +
              ∫ w, (f (n + 1) w - f n w) ^ 2 ∂mu := by rw [ih]
        _ = _ := by ring

/-- An exact finite stage cylinder is the preimage of its finite prefix. -/
private theorem DiscreteDecisionProcess.rawStageCylinder_eq_prefixPreimage
    (P : DiscreteDecisionProcess) (k : ℕ)
    (stage : Fin (k + 1) → DDPStage P) :
    {w | ∀ i : Fin (k + 1), w i = stage i} =
      Preorder.frestrictLe (π := fun _ : ℕ => DDPStage P) k ⁻¹'
        {P.stagePrefixOfFin stage} := by
  ext w
  simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff]
  constructor
  · intro h
    funext i
    exact h ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩
  · intro h i
    have hi := congrFun h ⟨i.1, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp i.2)⟩
    exact hi

/-- Exact finite raw-stage cylinders are measurable. -/
private theorem DiscreteDecisionProcess.measurableSet_rawStageCylinder
    (P : DiscreteDecisionProcess) (k : ℕ)
    (stage : Fin (k + 1) → DDPStage P) :
    MeasurableSet {w : ℕ → DDPStage P | ∀ i : Fin (k + 1), w i = stage i} := by
  rw [P.rawStageCylinder_eq_prefixPreimage k stage]
  exact (measurableSet_singleton (P.stagePrefixOfFin stage)).preimage
    (Preorder.measurable_frestrictLe (X := fun _ : ℕ => DDPStage P) k)

/-- A raw DDP law has the expected exact finite-stage cylinder products. -/
private theorem DiscreteDecisionProcess.rawLawWithInitial_exactStageCylinder
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) : ∀ (k : ℕ)
    (stage : Fin (k + 1) → DDPStage P),
    P.rawLawWithInitial initial
        {w : ℕ → DDPStage P | ∀ i : Fin (k + 1), w i = stage i} =
      initial (stage 0) *
        ∏ i : Fin k, P.stepStagePMF (stage i.castSucc) (stage i.succ) := by
  exact P.productionRawLawWithInitial_exactStageCylinder initial

/-- The state-started raw DDP law has the corresponding finite-stage products. -/
private theorem DiscreteDecisionProcess.rawLawFrom_exactStageCylinder
    (P : DiscreteDecisionProcess) (start : P.X) (k : ℕ)
    (stage : Fin (k + 1) → DDPStage P) :
    P.rawLawFrom start
        {w : ℕ → DDPStage P | ∀ i : Fin (k + 1), w i = stage i} =
      P.initialStagePMF start (stage 0) *
        ∏ i : Fin k, P.stepStagePMF (stage i.castSucc) (stage i.succ) := by
  exact P.rawLawWithInitial_exactStageCylinder (P.initialStagePMF start) k stage

/-- Exact initial-stage cylinders form a generating pi-system on raw trajectories. -/
private def DiscreteDecisionProcess.rawStagePrefixSets
    (P : DiscreteDecisionProcess) : Set (Set (ℕ → DDPStage P)) :=
  {U | ∃ k, ∃ stage : Fin (k + 1) → DDPStage P,
    U = {w | ∀ i : Fin (k + 1), w i = stage i}}

private theorem DiscreteDecisionProcess.isPiSystem_rawStagePrefixSets
    (P : DiscreteDecisionProcess) : IsPiSystem P.rawStagePrefixSets := by
  intro U hU V hV hnonempty
  rcases hU with ⟨k, stage, rfl⟩
  rcases hV with ⟨l, other, rfl⟩
  rcases hnonempty with ⟨w, hwStage, hwOther⟩
  simp only [mem_setOf_eq] at hwStage hwOther
  rcases le_total k l with hkl | hlk
  · refine ⟨l, other, ?_⟩
    ext u
    simp only [mem_inter_iff, mem_setOf_eq]
    constructor
    · exact fun h => h.2
    · intro huOther
      refine ⟨?_, huOther⟩
      intro i
      calc
        u i = other ⟨i.1, by omega⟩ := huOther ⟨i.1, by omega⟩
        _ = w i := (hwOther ⟨i.1, by omega⟩).symm
        _ = stage i := hwStage i
  · refine ⟨k, stage, ?_⟩
    ext u
    simp only [mem_inter_iff, mem_setOf_eq]
    constructor
    · exact fun h => h.1
    · intro huStage
      refine ⟨huStage, ?_⟩
      intro i
      calc
        u i = stage ⟨i.1, by omega⟩ := huStage ⟨i.1, by omega⟩
        _ = w i := (hwStage ⟨i.1, by omega⟩).symm
        _ = other i := hwOther i

private theorem DiscreteDecisionProcess.generateFrom_rawStagePrefixSets
    (P : DiscreteDecisionProcess) :
    (inferInstance : MeasurableSpace (ℕ → DDPStage P)) =
      MeasurableSpace.generateFrom P.rawStagePrefixSets := by
  apply le_antisymm
  · have hid : @Measurable (ℕ → DDPStage P) (ℕ → DDPStage P)
        (MeasurableSpace.generateFrom P.rawStagePrefixSets)
        (MeasurableSpace.pi : MeasurableSpace (ℕ → DDPStage P)) id := by
      refine @measurable_pi_lambda (ℕ → DDPStage P) ℕ (fun _ => DDPStage P)
        (MeasurableSpace.generateFrom P.rawStagePrefixSets) (fun _ => inferInstance) id ?_
      intro i
      apply @measurable_to_countable' (DDPStage P) (ℕ → DDPStage P)
        inferInstance inferInstance (MeasurableSpace.generateFrom P.rawStagePrefixSets)
        (f := fun w => w i)
      intro z
      have heq : (fun w : ℕ → DDPStage P => w i) ⁻¹' {z} =
          ⋃ (stage : Fin (i + 1) → DDPStage P) (_ : stage (Fin.last i) = z),
            {w : ℕ → DDPStage P |
              ∀ j : Fin (i + 1), w j = stage j} := by
        ext w
        simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_setOf_eq]
        constructor
        · intro hw
          let stage : Fin (i + 1) → DDPStage P := fun j => w j
          refine ⟨stage, ?_, fun _j => rfl⟩
          simpa [stage] using hw
        · rintro ⟨stage, hstage, hw⟩
          simpa [← hstage] using hw (Fin.last i)
      rw [heq]
      exact MeasurableSet.iUnion fun stage => MeasurableSet.iUnion fun _hstage =>
        MeasurableSpace.measurableSet_generateFrom ⟨i, stage, rfl⟩
    exact hid
  · apply (MeasurableSpace.generateFrom_le_iff _).2
    rintro U ⟨k, stage, rfl⟩
    exact P.measurableSet_rawStageCylinder k stage

/-- Forget a finite raw prefix and restart the trajectory at stage `i`. -/
private def DiscreteDecisionProcess.rawShift (P : DiscreteDecisionProcess)
    (i : ℕ) (stage : ℕ → DDPStage P) : ℕ → DDPStage P :=
  fun j => stage (i + j)

private theorem DiscreteDecisionProcess.measurable_rawShift
    (P : DiscreteDecisionProcess) (i : ℕ) : Measurable (P.rawShift i) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_pi_apply (i + j)

/-- Splice an exact prefix to a restarted exact tail, identifying their common stage. -/
private def DiscreteDecisionProcess.spliceRawStages
    (P : DiscreteDecisionProcess) {i k : ℕ}
    (initialStages : Fin (i + 1) → DDPStage P) (tail : Fin (k + 1) → DDPStage P)
    (_overlap : initialStages (Fin.last i) = tail 0) : Fin (i + k + 1) → DDPStage P :=
  fun j => if h : j.1 ≤ i then initialStages ⟨j.1, by omega⟩
    else tail ⟨j.1 - i, by omega⟩

@[simp] private theorem DiscreteDecisionProcess.spliceRawStages_prefix
    (P : DiscreteDecisionProcess) {i k : ℕ}
    (initialStages : Fin (i + 1) → DDPStage P) (tail : Fin (k + 1) → DDPStage P)
    (overlap : initialStages (Fin.last i) = tail 0) (j : Fin (i + 1)) :
    P.spliceRawStages initialStages tail overlap ⟨j.1, by omega⟩ = initialStages j := by
  change (if h : j.1 ≤ i then initialStages ⟨j.1, by omega⟩
    else tail ⟨j.1 - i, by omega⟩) = initialStages j
  rw [dif_pos (by omega)]

@[simp] private theorem DiscreteDecisionProcess.spliceRawStages_tail
    (P : DiscreteDecisionProcess) {i k : ℕ}
    (initialStages : Fin (i + 1) → DDPStage P) (tail : Fin (k + 1) → DDPStage P)
    (overlap : initialStages (Fin.last i) = tail 0) (j : Fin (k + 1)) :
    P.spliceRawStages initialStages tail overlap ⟨i + j.1, by omega⟩ = tail j := by
  by_cases hj : j = 0
  · subst j
    change (if h : i ≤ i then initialStages ⟨i, by omega⟩
      else tail ⟨i - i, by omega⟩) = tail 0
    rw [dif_pos le_rfl]
    calc
      initialStages ⟨i, by omega⟩ = initialStages (Fin.last i) := by congr
      _ = tail 0 := overlap
  · change (if h : i + j.1 ≤ i then initialStages ⟨i + j.1, by omega⟩
      else tail ⟨i + j.1 - i, by omega⟩) = tail j
    have hjpos : 0 < j.1 := by
      exact Nat.pos_of_ne_zero fun hz => hj (Fin.ext hz)
    rw [dif_neg (by omega)]
    apply congrArg tail
    apply Fin.ext
    exact Nat.add_sub_cancel_left i j.1

/-- The transition product of a spliced raw string factors at the restart stage. -/
private theorem DiscreteDecisionProcess.prod_stepStagePMF_spliceRawStages
    (P : DiscreteDecisionProcess) {i k : ℕ}
    (initialStages : Fin (i + 1) → DDPStage P) (tail : Fin (k + 1) → DDPStage P)
    (overlap : initialStages (Fin.last i) = tail 0) :
    (∏ j : Fin (i + k),
        P.stepStagePMF
          (P.spliceRawStages initialStages tail overlap j.castSucc)
          (P.spliceRawStages initialStages tail overlap j.succ)) =
      (∏ j : Fin i, P.stepStagePMF (initialStages j.castSucc) (initialStages j.succ)) *
        ∏ j : Fin k, P.stepStagePMF (tail j.castSucc) (tail j.succ) := by
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _hj
    have hleft : P.spliceRawStages initialStages tail overlap
        (Fin.castAdd k j).castSucc = initialStages j.castSucc := by
      rw [show (Fin.castAdd k j).castSucc = ⟨j.1, by omega⟩ by
        apply Fin.ext; rfl]
      exact P.spliceRawStages_prefix initialStages tail overlap j.castSucc
    have hright : P.spliceRawStages initialStages tail overlap
        (Fin.castAdd k j).succ = initialStages j.succ := by
      rw [show (Fin.castAdd k j).succ = ⟨j.1 + 1, by omega⟩ by
        apply Fin.ext; rfl]
      exact P.spliceRawStages_prefix initialStages tail overlap j.succ
    rw [hleft, hright]
  · apply Finset.prod_congr rfl
    intro j _hj
    have hleft : P.spliceRawStages initialStages tail overlap
        (Fin.natAdd i j).castSucc = tail j.castSucc := by
      rw [show (Fin.natAdd i j).castSucc = ⟨i + j.1, by omega⟩ by
        apply Fin.ext; rfl]
      exact P.spliceRawStages_tail initialStages tail overlap j.castSucc
    have hright : P.spliceRawStages initialStages tail overlap
        (Fin.natAdd i j).succ = tail j.succ := by
      rw [show (Fin.natAdd i j).succ = ⟨i + (j.1 + 1), by omega⟩ by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_natAdd]
        omega]
      exact P.spliceRawStages_tail initialStages tail overlap j.succ
    rw [hleft, hright]

/-- A fixed raw prefix followed by a shifted fixed tail is their spliced string. -/
private theorem DiscreteDecisionProcess.inter_shift_rawStageCylinder_eq_splice
    (P : DiscreteDecisionProcess) {i k : ℕ}
    (initialStages : Fin (i + 1) → DDPStage P) (tail : Fin (k + 1) → DDPStage P)
    (overlap : initialStages (Fin.last i) = tail 0) :
    {w : ℕ → DDPStage P | ∀ j : Fin (i + 1), w j = initialStages j} ∩
        P.rawShift i ⁻¹' {w | ∀ j : Fin (k + 1), w j = tail j} =
      {w | ∀ j : Fin (i + k + 1),
        w j = P.spliceRawStages initialStages tail overlap j} := by
  ext w
  simp only [mem_inter_iff, mem_setOf_eq, mem_preimage]
  constructor
  · rintro ⟨hinitial, htail⟩ j
    by_cases hj : j.1 ≤ i
    · rw [P.spliceRawStages_prefix initialStages tail overlap ⟨j.1, by omega⟩]
      exact hinitial ⟨j.1, by omega⟩
    · let q : Fin (k + 1) := ⟨j.1 - i, by omega⟩
      have hindex : i + q.1 = j.1 := by
        dsimp only [q]
        omega
      calc
        w j = w (i + q.1) := by rw [hindex]
        _ = tail q := htail q
        _ = P.spliceRawStages initialStages tail overlap j := by
          rw [show j = ⟨i + q.1, by omega⟩ by apply Fin.ext; exact hindex.symm]
          exact (P.spliceRawStages_tail initialStages tail overlap q).symm
  · intro hspliced
    constructor
    · intro j
      calc
        w j = P.spliceRawStages initialStages tail overlap ⟨j.1, by omega⟩ :=
          hspliced ⟨j.1, by omega⟩
        _ = initialStages j := P.spliceRawStages_prefix initialStages tail overlap j
    · intro j
      change w (i + j.1) = tail j
      calc
        w (i + j.1) =
            P.spliceRawStages initialStages tail overlap ⟨i + j.1, by omega⟩ :=
          hspliced ⟨i + j.1, by omega⟩
        _ = tail j := P.spliceRawStages_tail initialStages tail overlap j

/-- Incompatible fixed prefix and shifted-tail cylinders are disjoint. -/
private theorem DiscreteDecisionProcess.inter_shift_rawStageCylinder_eq_empty
    (P : DiscreteDecisionProcess) {i k : ℕ}
    (initialStages : Fin (i + 1) → DDPStage P) (tail : Fin (k + 1) → DDPStage P)
    (overlap : initialStages (Fin.last i) ≠ tail 0) :
    {w : ℕ → DDPStage P | ∀ j : Fin (i + 1), w j = initialStages j} ∩
        P.rawShift i ⁻¹' {w | ∀ j : Fin (k + 1), w j = tail j} = ∅ := by
  ext w
  simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, mem_empty_iff_false, iff_false,
    not_and]
  intro hinitial htail
  apply overlap
  calc
    initialStages (Fin.last i) = w i := (hinitial (Fin.last i)).symm
    _ = tail 0 := by simpa [DiscreteDecisionProcess.rawShift] using htail 0

/-- Bundle a raw sequence of sampled stages as a DDP path. -/
private def DDPPath.ofRaw (P : DiscreteDecisionProcess)
    (stage : ℕ → DDPStage P) : DDPPath P where
  x i := (stage i).1
  y i := (stage i).2

/-- Extend a `k`-action path by an arbitrary sampled action at its final state. -/
private def DDPFinitePath.extendWithFinalStage
    (P : DiscreteDecisionProcess) {k : ℕ} (h : DDPFinitePath P k)
    (last : DDPStage P) : Fin (k + 1) → DDPStage P :=
  Fin.lastCases last fun i => ⟨h.x i.castSucc, h.y i⟩

/-- The complete action string obtained by supplying the unconstrained final action. -/
private def DDPFinitePath.actionsWithFinal
    (P : DiscreteDecisionProcess) {k : ℕ} (h : DDPFinitePath P k)
    (last : P.Y (h.x (Fin.last k))) : (i : Fin (k + 1)) → P.Y (h.x i) :=
  Fin.lastCases last h.y

@[simp] private theorem DDPFinitePath.actionsWithFinal_castSucc
    (P : DiscreteDecisionProcess) {k : ℕ} (h : DDPFinitePath P k)
    (last : P.Y (h.x (Fin.last k))) (i : Fin k) :
    h.actionsWithFinal P last i.castSucc = h.y i := by
  simp [DDPFinitePath.actionsWithFinal]

@[simp] private theorem DDPFinitePath.actionsWithFinal_last
    (P : DiscreteDecisionProcess) {k : ℕ} (h : DDPFinitePath P k)
    (last : P.Y (h.x (Fin.last k))) :
    h.actionsWithFinal P last (Fin.last k) = last := by
  simp [DDPFinitePath.actionsWithFinal]

/-- The exact sampled stage string obtained by supplying the final action. -/
private def DDPFinitePath.stagesWithFinal
    (P : DiscreteDecisionProcess) {k : ℕ} (h : DDPFinitePath P k)
    (last : P.Y (h.x (Fin.last k))) : Fin (k + 1) → DDPStage P :=
  fun i => ⟨h.x i, h.actionsWithFinal P last i⟩

/-- A correctly based final sampled stage is the stage string built from its action. -/
private theorem DDPFinitePath.extendWithFinalStage_mk
    (P : DiscreteDecisionProcess) {k : ℕ} (h : DDPFinitePath P k)
    (last : P.Y (h.x (Fin.last k))) :
    h.extendWithFinalStage P ⟨h.x (Fin.last k), last⟩ =
      h.stagesWithFinal P last := by
  funext i
  induction i using Fin.lastCases with
  | last =>
      simp [DDPFinitePath.extendWithFinalStage,
        DDPFinitePath.stagesWithFinal]
  | cast i =>
      simp [DDPFinitePath.extendWithFinalStage,
        DDPFinitePath.stagesWithFinal]

/-- Splitting successive factors from a full string leaves the final factor outside. -/
private theorem prod_start_mul_successors {M : Type*} [CommMonoid M] {k : ℕ}
    (a : Fin (k + 1) → M) (b : Fin k → M) :
    a 0 * ∏ i : Fin k, b i * a i.succ =
      (∏ i : Fin k, a i.castSucc * b i) * a (Fin.last k) := by
  calc
    a 0 * ∏ i : Fin k, b i * a i.succ =
        (a 0 * ∏ i : Fin k, a i.succ) * ∏ i : Fin k, b i := by
      rw [Finset.prod_mul_distrib]
      ac_rfl
    _ = (∏ i : Fin (k + 1), a i) * ∏ i : Fin k, b i := by
      rw [Fin.prod_univ_succ]
    _ = ((∏ i : Fin k, a i.castSucc) * a (Fin.last k)) *
        ∏ i : Fin k, b i := by
      rw [Fin.prod_univ_castSucc]
    _ = (∏ i : Fin k, a i.castSucc * b i) * a (Fin.last k) := by
      rw [Finset.prod_mul_distrib]
      ac_rfl

/-- The exact raw probability of a finite DDP path and a specified final action. -/
private theorem DiscreteDecisionProcess.rawLawFrom_stagesWithFinal
    (P : DiscreteDecisionProcess) (start : P.X) {k : ℕ}
    (h : DDPFinitePath P k) (hstart : h.x 0 = start)
    (last : P.Y (h.x (Fin.last k))) :
    P.rawLawFrom start
        {stage | ∀ i : Fin (k + 1), stage i = h.stagesWithFinal P last i} =
      h.probability P * P.choose (h.x (Fin.last k)) last := by
  rw [P.rawLawFrom_exactStageCylinder]
  have hinitial :
      P.initialStagePMF start (h.stagesWithFinal P last 0) =
        P.choose (h.x 0) (h.actionsWithFinal P last 0) := by
    rw [← hstart]
    exact P.initialStagePMF_apply _ _
  rw [hinitial]
  have hstep : ∀ i : Fin k,
      P.stepStagePMF (h.stagesWithFinal P last i.castSucc)
          (h.stagesWithFinal P last i.succ) =
        P.move (h.x i.castSucc) (h.y i) (h.x i.succ) *
          P.choose (h.x i.succ) (h.actionsWithFinal P last i.succ) := by
    intro i
    change P.stepStagePMF
        ⟨h.x i.castSucc, h.actionsWithFinal P last i.castSucc⟩
        ⟨h.x i.succ, h.actionsWithFinal P last i.succ⟩ = _
    rw [show h.actionsWithFinal P last i.castSucc = h.y i by
      simp [DDPFinitePath.actionsWithFinal]]
    exact P.stepStagePMF_apply _ _ _ _
  simp_rw [hstep]
  simpa only [DDPFinitePath.probability,
    DDPFinitePath.actionsWithFinal_castSucc,
    DDPFinitePath.actionsWithFinal_last] using
      prod_start_mul_successors
        (fun i => P.choose (h.x i) (h.actionsWithFinal P last i))
        (fun i => P.move (h.x i.castSucc) (h.y i) (h.x i.succ))

/-- The raw DDP law after forcing the initial state and action. -/
private def DiscreteDecisionProcess.rawLawAfterAction
    (P : DiscreteDecisionProcess) (x : P.X) (y : P.Y x) :
    Measure (ℕ → DDPStage P) :=
  P.rawLawWithInitial (PMF.pure ⟨x, y⟩)

private instance DiscreteDecisionProcess.isProbabilityMeasure_rawLawAfterAction
    (P : DiscreteDecisionProcess) (x : P.X) (y : P.Y x) :
    IsProbabilityMeasure (P.rawLawAfterAction x y) := by
  unfold DiscreteDecisionProcess.rawLawAfterAction
  infer_instance

/-- Optional stopping at a bounded first return preserves the forced initial action value. -/
private theorem DiscreteDecisionProcess.integral_stoppedValue_hittingBtwn_eq
    (P : DiscreteDecisionProcess) (x : P.X) (y : P.Y x)
    (A : Set P.X) (N : ℕ) :
    (∫ stage, stoppedValue P.rawStageValue
      (fun stage => ((hittingBtwn
        (fun (n : ℕ) (path : ℕ → DDPStage P) => (path n).1) A 1 N stage : ℕ) : ℕ∞))
        stage ∂P.rawLawAfterAction x y) = P.valueY x y := by
  let rawState : ℕ → (ℕ → DDPStage P) → P.X := fun n stage => (stage n).1
  let tau : (ℕ → DDPStage P) → ℕ∞ := fun stage =>
    ((hittingBtwn rawState A (1 : ℕ) N stage : ℕ) : ℕ∞)
  have htau : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => DDPStage P)) tau := by
    exact P.rawState_adapted.isStoppingTime_hittingBtwn MeasurableSet.of_discrete
  have htau_le (stage : ℕ → DDPStage P) : tau stage ≤ (N : ℕ∞) := by
    change ((hittingBtwn rawState A (1 : ℕ) N stage : ℕ) : ℕ∞) ≤ (N : ℕ∞)
    exact_mod_cast
      (hittingBtwn_le (u := rawState) (s := A) (n := 1) (m := N) stage)
  have hzero_le (stage : ℕ → DDPStage P) : (0 : ℕ∞) ≤ tau stage := bot_le
  have hm := P.rawStageValue_martingale (PMF.pure (⟨x, y⟩ : DDPStage P))
  have hforward := hm.submartingale.expected_stoppedValue_mono
    (isStoppingTime_const _ 0) htau hzero_le htau_le
  have hbackward := hm.neg.submartingale.expected_stoppedValue_mono
    (isStoppingTime_const _ 0) htau hzero_le htau_le
  have hstopped :
      (∫ stage, stoppedValue P.rawStageValue tau stage ∂P.rawLawAfterAction x y) =
        ∫ stage, P.rawStageValue 0 stage ∂P.rawLawAfterAction x y := by
    change (∫ stage, stoppedValue P.rawStageValue tau stage ∂
      P.rawLawWithInitial (PMF.pure (⟨x, y⟩ : DDPStage P))) =
        ∫ stage, P.rawStageValue 0 stage ∂
          P.rawLawWithInitial (PMF.pure (⟨x, y⟩ : DDPStage P))
    simp only [stoppedValue_const] at hforward hbackward
    change (∫ stage, -P.rawStageValue 0 stage ∂
      P.rawLawWithInitial (PMF.pure (⟨x, y⟩ : DDPStage P))) ≤
        ∫ stage, -stoppedValue P.rawStageValue tau stage ∂
          P.rawLawWithInitial (PMF.pure (⟨x, y⟩ : DDPStage P)) at hbackward
    rw [integral_neg, integral_neg] at hbackward
    linarith
  have hsupport : P.rawLawAfterAction x y
      {stage : ℕ → DDPStage P | stage 0 = (⟨x, y⟩ : DDPStage P)} = 1 := by
    rw [DiscreteDecisionProcess.rawLawAfterAction]
    have hformula := P.rawLawWithInitial_exactStageCylinder
      (PMF.pure (⟨x, y⟩ : DDPStage P)) 0
      (fun _ : Fin 1 => (⟨x, y⟩ : DDPStage P))
    simpa [PMF.pure_apply] using hformula
  have hset : MeasurableSet
      {stage : ℕ → DDPStage P | stage 0 = (⟨x, y⟩ : DDPStage P)} :=
    show MeasurableSet ((fun stage : ℕ → DDPStage P => stage 0) ⁻¹'
      {(⟨x, y⟩ : DDPStage P)}) from
        (measurable_pi_apply 0) (measurableSet_singleton (⟨x, y⟩ : DDPStage P))
  have hae : ∀ᵐ stage ∂P.rawLawAfterAction x y,
      P.rawStageValue 0 stage = P.valueY x y := by
    have hmem : ∀ᵐ stage ∂P.rawLawAfterAction x y,
        stage ∈ {stage : ℕ → DDPStage P | stage 0 = (⟨x, y⟩ : DDPStage P)} :=
      (ae_mem_iff_measure_eq hset.nullMeasurableSet).2 (by
        rw [hsupport]
        letI : IsProbabilityMeasure (P.rawLawAfterAction x y) :=
          P.isProbabilityMeasure_rawLawAfterAction x y
        rw [measure_univ])
    filter_upwards [hmem] with stage hstage
    change P.valueY (stage 0).1 (stage 0).2 = P.valueY x y
    exact congrArg (fun current : DDPStage P => P.valueY current.1 current.2) hstage
  rw [show (fun stage => ((hittingBtwn
      (fun (n : ℕ) (path : ℕ → DDPStage P) => (path n).1) A 1 N stage : ℕ) : ℕ∞)) =
      tau by rfl]
  rw [hstopped, integral_congr_ae hae]
  letI : IsProbabilityMeasure (P.rawLawAfterAction x y) :=
    P.isProbabilityMeasure_rawLawAfterAction x y
  simp

/-- Exact-prefix mass factors from every exact event after restarting at its last stage. -/
private theorem DiscreteDecisionProcess.rawLawWithInitial_inter_shiftCylinder
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) {i k : ℕ}
    (initialStages : Fin (i + 1) → DDPStage P) (tail : Fin (k + 1) → DDPStage P) :
    P.rawLawWithInitial initial
        (P.rawShift i ⁻¹' {w | ∀ j : Fin (k + 1), w j = tail j} ∩
          {w | ∀ j : Fin (i + 1), w j = initialStages j}) =
      P.rawLawWithInitial initial
          {w | ∀ j : Fin (i + 1), w j = initialStages j} *
        P.rawLawAfterAction (initialStages (Fin.last i)).1
          (initialStages (Fin.last i)).2
          {w | ∀ j : Fin (k + 1), w j = tail j} := by
  classical
  by_cases hoverlap : initialStages (Fin.last i) = tail 0
  · rw [inter_comm, P.inter_shift_rawStageCylinder_eq_splice initialStages tail hoverlap]
    rw [P.rawLawWithInitial_exactStageCylinder,
      P.rawLawWithInitial_exactStageCylinder]
    rw [DiscreteDecisionProcess.rawLawAfterAction,
      P.rawLawWithInitial_exactStageCylinder]
    rw [PMF.pure_apply, if_pos hoverlap.symm, one_mul]
    have hzero : P.spliceRawStages initialStages tail hoverlap 0 = initialStages 0 := by
      exact P.spliceRawStages_prefix initialStages tail hoverlap 0
    rw [hzero]
    rw [P.prod_stepStagePMF_spliceRawStages initialStages tail hoverlap]
    ring
  · rw [inter_comm, P.inter_shift_rawStageCylinder_eq_empty initialStages tail hoverlap]
    rw [measure_empty, zero_eq_mul]
    right
    rw [DiscreteDecisionProcess.rawLawAfterAction,
      P.rawLawWithInitial_exactStageCylinder]
    rw [PMF.pure_apply, if_neg (Ne.symm hoverlap), zero_mul]

/-- Restricting to a finite raw prefix and shifting gives its mass times the restarted law. -/
private theorem DiscreteDecisionProcess.map_rawShift_restrict_rawStageCylinder
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) {i : ℕ}
    (initialStages : Fin (i + 1) → DDPStage P) :
    Measure.map (P.rawShift i)
        ((P.rawLawWithInitial initial).restrict
          {w | ∀ j : Fin (i + 1), w j = initialStages j}) =
      P.rawLawWithInitial initial
          {w | ∀ j : Fin (i + 1), w j = initialStages j} •
        P.rawLawAfterAction (initialStages (Fin.last i)).1
          (initialStages (Fin.last i)).2 := by
  apply ext_of_generate_finite P.rawStagePrefixSets
    P.generateFrom_rawStagePrefixSets P.isPiSystem_rawStagePrefixSets
  · intro U hU
    rcases hU with ⟨k, tail, rfl⟩
    rw [Measure.map_apply (P.measurable_rawShift i)
      (P.measurableSet_rawStageCylinder k tail)]
    rw [Measure.restrict_apply
      ((P.measurable_rawShift i) (P.measurableSet_rawStageCylinder k tail))]
    rw [Measure.smul_apply, smul_eq_mul]
    exact P.rawLawWithInitial_inter_shiftCylinder initial initialStages tail
  · rw [Measure.map_apply (P.measurable_rawShift i) MeasurableSet.univ]
    simp only [preimage_univ]
    rw [Measure.restrict_apply MeasurableSet.univ]
    rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    simp

/-- The restart factorization holds for every measurable tail event, not only cylinders. -/
private theorem DiscreteDecisionProcess.rawLawWithInitial_inter_shift
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) {i : ℕ}
    (initialStages : Fin (i + 1) → DDPStage P) {E : Set (ℕ → DDPStage P)}
    (hE : MeasurableSet E) :
    P.rawLawWithInitial initial
        (P.rawShift i ⁻¹' E ∩
          {w | ∀ j : Fin (i + 1), w j = initialStages j}) =
      P.rawLawWithInitial initial
          {w | ∀ j : Fin (i + 1), w j = initialStages j} *
        P.rawLawAfterAction (initialStages (Fin.last i)).1
          (initialStages (Fin.last i)).2 E := by
  have hmeasure := congrArg (fun mu : Measure (ℕ → DDPStage P) => mu E)
    (P.map_rawShift_restrict_rawStageCylinder initial initialStages)
  rw [Measure.map_apply (P.measurable_rawShift i) hE] at hmeasure
  rw [Measure.restrict_apply ((P.measurable_rawShift i) hE)] at hmeasure
  rw [Measure.smul_apply, smul_eq_mul] at hmeasure
  exact hmeasure

/-- At a deterministic time, the future law depends only on the current sampled stage. -/
private theorem DiscreteDecisionProcess.rawLawWithInitial_inter_shift_stageAt
    (P : DiscreteDecisionProcess) (initial : PMF (DDPStage P)) (i : ℕ)
    (current : DDPStage P) {E : Set (ℕ → DDPStage P)} (hE : MeasurableSet E) :
    P.rawLawWithInitial initial
        (P.rawShift i ⁻¹' E ∩ {w | w i = current}) =
      P.rawLawWithInitial initial {w | w i = current} *
        P.rawLawAfterAction current.1 current.2 E := by
  classical
  let Prefix := {stage : Fin (i + 1) → DDPStage P // stage (Fin.last i) = current}
  let C : Prefix → Set (ℕ → DDPStage P) := fun stage =>
    {w | ∀ j : Fin (i + 1), w j = stage.1 j}
  have hpairwise : Pairwise (Function.onFun Disjoint C) := by
    intro stage other hne
    rw [Function.onFun, disjoint_left]
    intro w hwStage hwOther
    apply hne
    apply Subtype.ext
    funext j
    exact (hwStage j).symm.trans (hwOther j)
  have hunion : {w : ℕ → DDPStage P | w i = current} = ⋃ stage : Prefix, C stage := by
    ext w
    simp only [mem_setOf_eq, mem_iUnion, C]
    constructor
    · intro hw
      let stage : Fin (i + 1) → DDPStage P := fun j => w j
      refine ⟨⟨stage, ?_⟩, fun _j => rfl⟩
      simpa [stage] using hw
    · rintro ⟨stage, hw⟩
      calc
        w i = stage.1 (Fin.last i) := hw (Fin.last i)
        _ = current := stage.2
  have hinter : P.rawShift i ⁻¹' E ∩ {w : ℕ → DDPStage P | w i = current} =
      ⋃ stage : Prefix, P.rawShift i ⁻¹' E ∩ C stage := by
    rw [hunion, inter_iUnion]
  have hpairwiseInter : Pairwise
      (Function.onFun Disjoint fun stage : Prefix => P.rawShift i ⁻¹' E ∩ C stage) := by
    intro stage other hne
    exact (hpairwise hne).mono inter_subset_right inter_subset_right
  have hmeasurableC (stage : Prefix) : MeasurableSet (C stage) :=
    P.measurableSet_rawStageCylinder i stage.1
  have hmeasurableInter (stage : Prefix) :
      MeasurableSet (P.rawShift i ⁻¹' E ∩ C stage) :=
    ((P.measurable_rawShift i) hE).inter (hmeasurableC stage)
  rw [hinter, measure_iUnion hpairwiseInter hmeasurableInter]
  rw [hunion, measure_iUnion hpairwise hmeasurableC]
  calc
    (∑' stage : Prefix,
        P.rawLawWithInitial initial (P.rawShift i ⁻¹' E ∩ C stage)) =
        ∑' stage : Prefix,
          P.rawLawWithInitial initial (C stage) *
            P.rawLawAfterAction current.1 current.2 E := by
      apply tsum_congr
      intro stage
      rw [P.rawLawWithInitial_inter_shift initial stage.1 hE]
      rw [show stage.1 (Fin.last i) = current from stage.2]
    _ = (∑' stage : Prefix, P.rawLawWithInitial initial (C stage)) *
        P.rawLawAfterAction current.1 current.2 E := ENNReal.tsum_mul_right

/-- A forced first action removes exactly its action-selection factor. -/
private theorem DiscreteDecisionProcess.rawLawAfterAction_stagesWithFinal
    (P : DiscreteDecisionProcess) (x : P.X) (y : P.Y x) {k : ℕ}
    (h : DDPFinitePath P (k + 1)) (hstart : h.x 0 = x)
    (haction : HEq (h.y 0) y) (last : P.Y (h.x (Fin.last (k + 1)))) :
    P.rawLawAfterAction x y
        {stage | ∀ i : Fin (k + 2), stage i = h.stagesWithFinal P last i} =
      h.afterActionProbability P * P.choose (h.x (Fin.last (k + 1))) last := by
  rw [DiscreteDecisionProcess.rawLawAfterAction,
    P.rawLawWithInitial_exactStageCylinder]
  have hfirst : h.stagesWithFinal P last 0 = (⟨x, y⟩ : DDPStage P) := by
    apply Sigma.ext hstart
    have hzero : h.actionsWithFinal P last 0 = h.y 0 := by
      simpa using h.actionsWithFinal_castSucc P last (0 : Fin (k + 1))
    simpa [DDPFinitePath.stagesWithFinal, hzero] using haction
  rw [PMF.pure_apply, if_pos hfirst, one_mul]
  have hstep : ∀ i : Fin (k + 1),
      P.stepStagePMF (h.stagesWithFinal P last i.castSucc)
          (h.stagesWithFinal P last i.succ) =
        P.move (h.x i.castSucc) (h.y i) (h.x i.succ) *
          P.choose (h.x i.succ) (h.actionsWithFinal P last i.succ) := by
    intro i
    change P.stepStagePMF
        ⟨h.x i.castSucc, h.actionsWithFinal P last i.castSucc⟩
        ⟨h.x i.succ, h.actionsWithFinal P last i.succ⟩ = _
    rw [show h.actionsWithFinal P last i.castSucc = h.y i by
      simp [DDPFinitePath.actionsWithFinal]]
    exact P.stepStagePMF_apply _ _ _ _
  simp_rw [hstep]
  rw [Fin.prod_univ_succ]
  change
    (P.move (h.x 0) (h.y 0) (h.x 1) *
        P.choose (h.x 1) (h.actionsWithFinal P last 1)) *
        (∏ i : Fin k,
          P.move (h.x i.succ.castSucc) (h.y i.succ) (h.x i.succ.succ) *
            P.choose (h.x i.succ.succ)
              (h.actionsWithFinal P last i.succ.succ)) = _
  have htail :
      P.choose (h.x (Fin.succ 0)) (h.actionsWithFinal P last (Fin.succ 0)) *
          ∏ i : Fin k,
            P.move (h.x i.succ.castSucc) (h.y i.succ) (h.x i.succ.succ) *
              P.choose (h.x i.succ.succ)
                (h.actionsWithFinal P last i.succ.succ) =
        (∏ i : Fin k,
          P.choose (h.x i.succ.castSucc) (h.y i.succ) *
            P.move (h.x i.succ.castSucc) (h.y i.succ) (h.x i.succ.succ)) *
          P.choose (h.x (Fin.last (k + 1))) last := by
    convert prod_start_mul_successors
        (fun i : Fin (k + 1) =>
          P.choose (h.x i.succ) (h.actionsWithFinal P last i.succ))
        (fun i : Fin k =>
          P.move (h.x i.succ.castSucc) (h.y i.succ) (h.x i.succ.succ)) using 1
    all_goals
      simp only [DDPFinitePath.actionsWithFinal_castSucc,
        DDPFinitePath.actionsWithFinal_last, Fin.succ_castSucc,
        Fin.succ_last, Nat.succ_eq_add_one]
    · congr 1
  rw [DDPFinitePath.afterActionProbability]
  calc
    _ = P.move (h.x 0) (h.y 0) (h.x 1) *
        (P.choose (h.x 1) (h.actionsWithFinal P last 1) *
          ∏ i : Fin k,
            P.move (h.x i.succ.castSucc) (h.y i.succ) (h.x i.succ.succ) *
              P.choose (h.x i.succ.succ)
                (h.actionsWithFinal P last i.succ.succ)) := by rw [mul_assoc]
    _ = P.move (h.x 0) (h.y 0) (h.x 1) *
        ((∏ i : Fin k,
          P.choose (h.x i.succ.castSucc) (h.y i.succ) *
            P.move (h.x i.succ.castSucc) (h.y i.succ) (h.x i.succ.succ)) *
          P.choose (h.x (Fin.last (k + 1))) last) := by
            congr 1
    _ = _ := by rw [mul_assoc]

/-- Equality of all state coordinates and sampled-action stages determines a finite DDP path. -/
private theorem DDPFinitePath.ext_of_stages
    (P : DiscreteDecisionProcess) {k : ℕ} {a b : DDPFinitePath P k}
    (hx : ∀ i, a.x i = b.x i)
    (hstage : ∀ i : Fin k,
      (⟨a.x i.castSucc, a.y i⟩ : DDPStage P) = ⟨b.x i.castSucc, b.y i⟩) :
    a = b := by
  cases a with
  | mk ax ay =>
      cases b with
      | mk bx byy =>
          have hxeq : ax = bx := funext hx
          subst bx
          have hyeq : ay = byy := by
            funext i
            exact eq_of_heq (Sigma.mk.inj_iff.mp (hstage i)).2
          subst byy
          rfl

/-- Agreement of two infinite paths through a later prefix implies agreement earlier. -/
private theorem DDPPath.prefix_eq_of_prefix_eq_of_le
    (P : DiscreteDecisionProcess) {p q : DDPPath P} {k l : ℕ}
    (hkl : k ≤ l) (h : p.prefix P l = q.prefix P l) :
    p.prefix P k = q.prefix P k := by
  apply DDPFinitePath.ext_of_stages P
  · intro i
    let j : Fin (l + 1) := Fin.castLE (Nat.add_le_add_right hkl 1) i
    have hj := congrArg (fun r : DDPFinitePath P l => r.x j) h
    simpa [j, DDPPath.prefix] using hj
  · intro i
    let j : Fin l := Fin.castLE hkl i
    have hj := congrArg (fun r : DDPFinitePath P l =>
      (⟨r.x j.castSucc, r.y j⟩ : DDPStage P)) h
    simpa [j, DDPPath.prefix] using hj

/-- A raw stage sequence belongs to a DDP cylinder exactly when its constrained prefix agrees. -/
private theorem DDPPath.preimage_ddpCylinder_eq_iUnion
    (P : DiscreteDecisionProcess) {k : ℕ} (h : DDPFinitePath P k) :
    DDPPath.ofRaw P ⁻¹' DDPCylinder P h =
      ⋃ last : DDPStage P,
        {stage | last.1 = h.x (Fin.last k) ∧ ∀ i : Fin (k + 1),
          stage i = h.extendWithFinalStage P last i} := by
  ext stage
  simp only [mem_preimage, mem_iUnion, mem_setOf_eq]
  constructor
  · intro hp
    change (DDPPath.ofRaw P stage).prefix P k = h at hp
    subst h
    refine ⟨stage k, ?_, ?_⟩
    · rfl
    · intro i
      induction i using Fin.lastCases with
      | last =>
          simp [DDPFinitePath.extendWithFinalStage, DDPPath.prefix,
            DDPPath.ofRaw]
      | cast i =>
          simp [DDPFinitePath.extendWithFinalStage, DDPPath.prefix,
            DDPPath.ofRaw]
  · rintro ⟨last, hlast, hp⟩
    change (DDPPath.ofRaw P stage).prefix P k = h
    apply DDPFinitePath.ext_of_stages P
    · intro i
      induction i using Fin.lastCases with
      | last =>
          change (stage k).1 = h.x (Fin.last k)
          have hcoord : (stage k).1 = last.1 := by
            simpa [DDPFinitePath.extendWithFinalStage] using
              congrArg Sigma.fst (hp (Fin.last k))
          exact hcoord.trans hlast
      | cast i =>
          change (stage i).1 = h.x i.castSucc
          simpa [DDPFinitePath.extendWithFinalStage] using
            congrArg Sigma.fst (hp i.castSucc)
    · intro i
      change stage i = ⟨h.x i.castSucc, h.y i⟩
      simpa [DDPFinitePath.extendWithFinalStage] using hp i.castSucc

/-- The raw preimage of every DDP cylinder is measurable. -/
private theorem DDPPath.measurableSet_preimage_ddpCylinder
    (P : DiscreteDecisionProcess) {k : ℕ} (h : DDPFinitePath P k) :
    MeasurableSet (DDPPath.ofRaw P ⁻¹' DDPCylinder P h) := by
  rw [DDPPath.preimage_ddpCylinder_eq_iUnion]
  apply MeasurableSet.iUnion
  intro last
  by_cases hlast : last.1 = h.x (Fin.last k)
  · have heq : {stage : ℕ → DDPStage P |
        last.1 = h.x (Fin.last k) ∧ ∀ i : Fin (k + 1),
        stage i = h.extendWithFinalStage P last i} =
        {stage : ℕ → DDPStage P | ∀ i : Fin (k + 1),
          stage i = h.extendWithFinalStage P last i} := by
      ext stage
      simp [hlast]
    rw [heq]
    exact P.measurableSet_rawStageCylinder k (h.extendWithFinalStage P last)
  · have heq : {stage : ℕ → DDPStage P |
        last.1 = h.x (Fin.last k) ∧ ∀ i : Fin (k + 1),
        stage i = h.extendWithFinalStage P last i} = ∅ := by
      ext stage
      simp [hlast]
    rw [heq]
    exact MeasurableSet.empty

/-- The raw-to-DDP path map is measurable for the finite-cylinder sigma algebra. -/
private theorem DDPPath.measurable_ofRaw (P : DiscreteDecisionProcess) :
    Measurable (DDPPath.ofRaw P) := by
  apply measurable_generateFrom
  intro U hU
  rcases hU with ⟨k, h, rfl⟩
  exact DDPPath.measurableSet_preimage_ddpCylinder P h

/-- The raw law assigns each finite DDP cylinder its displayed product probability. -/
private theorem DiscreteDecisionProcess.rawLawFrom_ddpCylinder
    (P : DiscreteDecisionProcess) (start : P.X) {k : ℕ}
    (h : DDPFinitePath P k) (hstart : h.x 0 = start) :
    P.rawLawFrom start (DDPPath.ofRaw P ⁻¹' DDPCylinder P h) = h.probability P := by
  rw [DDPPath.preimage_ddpCylinder_eq_iUnion]
  have hmeasurable : ∀ last : DDPStage P,
      MeasurableSet {stage : ℕ → DDPStage P | last.1 = h.x (Fin.last k) ∧
        ∀ i : Fin (k + 1), stage i = h.extendWithFinalStage P last i} := by
    intro last
    by_cases hlast : last.1 = h.x (Fin.last k)
    · have heq : {stage : ℕ → DDPStage P | last.1 = h.x (Fin.last k) ∧
          ∀ i : Fin (k + 1), stage i = h.extendWithFinalStage P last i} =
          {stage : ℕ → DDPStage P | ∀ i : Fin (k + 1),
            stage i = h.extendWithFinalStage P last i} := by
        ext stage
        simp [hlast]
      rw [heq]
      exact P.measurableSet_rawStageCylinder k (h.extendWithFinalStage P last)
    · have heq : {stage : ℕ → DDPStage P | last.1 = h.x (Fin.last k) ∧
          ∀ i : Fin (k + 1), stage i = h.extendWithFinalStage P last i} = ∅ := by
        ext stage
        simp [hlast]
      rw [heq]
      exact MeasurableSet.empty
  have hdisjoint : Pairwise (Function.onFun Disjoint fun last : DDPStage P =>
      {stage : ℕ → DDPStage P | last.1 = h.x (Fin.last k) ∧
        ∀ i : Fin (k + 1), stage i = h.extendWithFinalStage P last i}) := by
    intro first second hne
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro stage hfirst hsecond
    have hfirstLast := hfirst.2 (Fin.last k)
    have hsecondLast := hsecond.2 (Fin.last k)
    have : first = second := by
      simpa [DDPFinitePath.extendWithFinalStage] using
        hfirstLast.symm.trans hsecondLast
    exact hne this
  rw [measure_iUnion hdisjoint hmeasurable]
  rw [ENNReal.tsum_sigma']
  rw [tsum_eq_single (h.x (Fin.last k))]
  · have heq (last : P.Y (h.x (Fin.last k))) :
        {stage : ℕ → DDPStage P |
          (⟨h.x (Fin.last k), last⟩ : DDPStage P).1 = h.x (Fin.last k) ∧
          ∀ i : Fin (k + 1),
            stage i = h.extendWithFinalStage P ⟨h.x (Fin.last k), last⟩ i} =
        {stage : ℕ → DDPStage P | ∀ i : Fin (k + 1),
          stage i = h.stagesWithFinal P last i} := by
      ext stage
      simp [h.extendWithFinalStage_mk P]
    calc
      (∑' last : P.Y (h.x (Fin.last k)),
          P.rawLawFrom start
            {stage : ℕ → DDPStage P |
              (⟨h.x (Fin.last k), last⟩ : DDPStage P).1 = h.x (Fin.last k) ∧
              ∀ i : Fin (k + 1),
                stage i = h.extendWithFinalStage P
                  ⟨h.x (Fin.last k), last⟩ i}) =
          ∑' last : P.Y (h.x (Fin.last k)),
            P.rawLawFrom start
              {stage : ℕ → DDPStage P | ∀ i : Fin (k + 1),
                stage i = h.stagesWithFinal P last i} := by
            apply tsum_congr
            intro last
            rw [heq last]
      _ = ∑' last : P.Y (h.x (Fin.last k)),
          h.probability P * P.choose (h.x (Fin.last k)) last := by
            apply tsum_congr
            intro last
            rw [P.rawLawFrom_stagesWithFinal start h hstart]
      _ = h.probability P := by
            rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  · intro state hstate
    have heq (last : P.Y state) :
        {stage : ℕ → DDPStage P |
          (⟨state, last⟩ : DDPStage P).1 = h.x (Fin.last k) ∧
          ∀ i : Fin (k + 1),
            stage i = h.extendWithFinalStage P ⟨state, last⟩ i} = ∅ := by
      ext stage
      simp [hstate]
    simp_rw [heq]
    simp

/-- A forced-action raw law assigns the displayed forced-action cylinder probability. -/
private theorem DiscreteDecisionProcess.rawLawAfterAction_ddpCylinder
    (P : DiscreteDecisionProcess) (x : P.X) (y : P.Y x) {k : ℕ}
    (h : DDPFinitePath P (k + 1)) (hstart : h.x 0 = x)
    (haction : HEq (h.y 0) y) :
    P.rawLawAfterAction x y (DDPPath.ofRaw P ⁻¹' DDPCylinder P h) =
      h.afterActionProbability P := by
  rw [DDPPath.preimage_ddpCylinder_eq_iUnion]
  have hmeasurable : ∀ last : DDPStage P,
      MeasurableSet {stage : ℕ → DDPStage P |
        last.1 = h.x (Fin.last (k + 1)) ∧
          ∀ i : Fin (k + 2), stage i = h.extendWithFinalStage P last i} := by
    intro last
    by_cases hlast : last.1 = h.x (Fin.last (k + 1))
    · have heq : {stage : ℕ → DDPStage P |
          last.1 = h.x (Fin.last (k + 1)) ∧
            ∀ i : Fin (k + 2), stage i = h.extendWithFinalStage P last i} =
          {stage : ℕ → DDPStage P | ∀ i : Fin (k + 2),
            stage i = h.extendWithFinalStage P last i} := by
        ext stage
        simp [hlast]
      rw [heq]
      exact P.measurableSet_rawStageCylinder (k + 1) (h.extendWithFinalStage P last)
    · have heq : {stage : ℕ → DDPStage P |
          last.1 = h.x (Fin.last (k + 1)) ∧
            ∀ i : Fin (k + 2), stage i = h.extendWithFinalStage P last i} = ∅ := by
        ext stage
        simp [hlast]
      rw [heq]
      exact MeasurableSet.empty
  have hdisjoint : Pairwise (Function.onFun Disjoint fun last : DDPStage P =>
      {stage : ℕ → DDPStage P | last.1 = h.x (Fin.last (k + 1)) ∧
        ∀ i : Fin (k + 2), stage i = h.extendWithFinalStage P last i}) := by
    intro first second hne
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro stage hfirst hsecond
    have hfirstLast := hfirst.2 (Fin.last (k + 1))
    have hsecondLast := hsecond.2 (Fin.last (k + 1))
    have : first = second := by
      simpa [DDPFinitePath.extendWithFinalStage] using
        hfirstLast.symm.trans hsecondLast
    exact hne this
  rw [measure_iUnion hdisjoint hmeasurable]
  rw [ENNReal.tsum_sigma']
  rw [tsum_eq_single (h.x (Fin.last (k + 1)))]
  · have heq (last : P.Y (h.x (Fin.last (k + 1)))) :
        {stage : ℕ → DDPStage P |
          (⟨h.x (Fin.last (k + 1)), last⟩ : DDPStage P).1 =
              h.x (Fin.last (k + 1)) ∧
            ∀ i : Fin (k + 2), stage i = h.extendWithFinalStage P
              ⟨h.x (Fin.last (k + 1)), last⟩ i} =
          {stage : ℕ → DDPStage P | ∀ i : Fin (k + 2),
            stage i = h.stagesWithFinal P last i} := by
      ext stage
      simp [h.extendWithFinalStage_mk P]
    calc
      (∑' last : P.Y (h.x (Fin.last (k + 1))),
          P.rawLawAfterAction x y
            {stage : ℕ → DDPStage P |
              (⟨h.x (Fin.last (k + 1)), last⟩ : DDPStage P).1 =
                  h.x (Fin.last (k + 1)) ∧
                ∀ i : Fin (k + 2), stage i = h.extendWithFinalStage P
                  ⟨h.x (Fin.last (k + 1)), last⟩ i}) =
          ∑' last : P.Y (h.x (Fin.last (k + 1))),
            P.rawLawAfterAction x y
              {stage : ℕ → DDPStage P | ∀ i : Fin (k + 2),
                stage i = h.stagesWithFinal P last i} := by
            apply tsum_congr
            intro last
            rw [heq last]
      _ = ∑' last : P.Y (h.x (Fin.last (k + 1))),
          h.afterActionProbability P * P.choose (h.x (Fin.last (k + 1))) last := by
            apply tsum_congr
            intro last
            rw [P.rawLawAfterAction_stagesWithFinal x y h hstart haction last]
      _ = h.afterActionProbability P := by
            rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  · intro state hstate
    have heq (last : P.Y state) :
        {stage : ℕ → DDPStage P |
          (⟨state, last⟩ : DDPStage P).1 = h.x (Fin.last (k + 1)) ∧
            ∀ i : Fin (k + 2),
              stage i = h.extendWithFinalStage P ⟨state, last⟩ i} = ∅ := by
      ext stage
      simp [hstate]
    simp_rw [heq]
    simp

/-- On a forced-action cylinder, averaging the unconstrained final action gives its state value. -/
private theorem DiscreteDecisionProcess.integral_rawStageValue_ddpCylinder
    (P : DiscreteDecisionProcess) (x : P.X) (y : P.Y x) {k : ℕ}
    (h : DDPFinitePath P (k + 1)) (hstart : h.x 0 = x)
    (haction : HEq (h.y 0) y) :
    (∫ stage in DDPPath.ofRaw P ⁻¹' DDPCylinder P h,
        P.rawStageValue (k + 1) stage ∂P.rawLawAfterAction x y) =
      (h.afterActionProbability P).toReal * P.valueX (h.x (Fin.last (k + 1))) := by
  classical
  let C : P.Y (h.x (Fin.last (k + 1))) → Set (ℕ → DDPStage P) := fun last =>
    {stage | ∀ i : Fin (k + 2), stage i = h.stagesWithFinal P last i}
  have hevent : DDPPath.ofRaw P ⁻¹' DDPCylinder P h = ⋃ last, C last := by
    rw [DDPPath.preimage_ddpCylinder_eq_iUnion]
    ext stage
    simp only [mem_iUnion, mem_setOf_eq, C]
    constructor
    · rintro ⟨⟨state, last⟩, hstate, hstage⟩
      change state = h.x (Fin.last (k + 1)) at hstate
      subst state
      refine ⟨last, ?_⟩
      simpa [h.extendWithFinalStage_mk P] using hstage
    · rintro ⟨last, hstage⟩
      refine ⟨⟨h.x (Fin.last (k + 1)), last⟩, rfl, ?_⟩
      simpa [h.extendWithFinalStage_mk P] using hstage
  have hmeasurable (last : P.Y (h.x (Fin.last (k + 1)))) : MeasurableSet (C last) :=
    P.measurableSet_rawStageCylinder (k + 1) (h.stagesWithFinal P last)
  have hpairwise : Pairwise (Function.onFun Disjoint C) := by
    intro first second hne
    rw [Function.onFun, Set.disjoint_left]
    intro stage hfirst hsecond
    apply hne
    have hfinal := (hfirst (Fin.last (k + 1))).symm.trans
      (hsecond (Fin.last (k + 1)))
    exact eq_of_heq (by simpa using (Sigma.mk.inj_iff.mp hfinal).2)
  have hintegrable : Integrable (P.rawStageValue (k + 1))
      (P.rawLawAfterAction x y) := by
    exact P.integrable_rawStageValue (PMF.pure (⟨x, y⟩ : DDPStage P)) (k + 1)
  rw [hevent, integral_iUnion hmeasurable hpairwise hintegrable.integrableOn]
  have hcylinder (last : P.Y (h.x (Fin.last (k + 1)))) :
      (∫ stage in C last, P.rawStageValue (k + 1) stage
          ∂P.rawLawAfterAction x y) =
        (h.afterActionProbability P *
          P.choose (h.x (Fin.last (k + 1))) last).toReal *
            P.valueY (h.x (Fin.last (k + 1))) last := by
    calc
      (∫ stage in C last, P.rawStageValue (k + 1) stage
          ∂P.rawLawAfterAction x y) =
          ∫ _stage in C last, P.valueY (h.x (Fin.last (k + 1))) last
            ∂P.rawLawAfterAction x y := by
              apply integral_congr_ae
              filter_upwards [ae_restrict_mem (hmeasurable last)] with stage hstage
              change P.valueY (stage (k + 1)).1 (stage (k + 1)).2 = _
              simpa [C, DDPFinitePath.stagesWithFinal] using
                congrArg (fun current : DDPStage P =>
                  P.valueY current.1 current.2) (hstage (Fin.last (k + 1)))
      _ = (P.rawLawAfterAction x y (C last)).toReal *
          P.valueY (h.x (Fin.last (k + 1))) last := by
            rw [integral_const, Measure.real_def, Measure.restrict_apply_univ]
            rfl
      _ = _ := by
        rw [show P.rawLawAfterAction x y (C last) =
            h.afterActionProbability P *
              P.choose (h.x (Fin.last (k + 1))) last from
          P.rawLawAfterAction_stagesWithFinal x y h hstart haction last]
  simp_rw [hcylinder, ENNReal.toReal_mul]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  congr 1
  exact P.harmonicX (h.x (Fin.last (k + 1))) |>.symm

/-- The one-step finite path with prescribed initial state, action, and successor. -/
private def DDPFinitePath.firstStep (P : DiscreteDecisionProcess)
    (x : P.X) (y : P.Y x) (z : P.X) : DDPFinitePath P 1 where
  x i := Fin.cases x (fun _ => z) i
  y i := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact y

@[simp] private theorem DDPFinitePath.firstStep_x_zero
    (P : DiscreteDecisionProcess) (x : P.X) (y : P.Y x) (z : P.X) :
    (DDPFinitePath.firstStep P x y z).x 0 = x := rfl

@[simp] private theorem DDPFinitePath.firstStep_x_one
    (P : DiscreteDecisionProcess) (x : P.X) (y : P.Y x) (z : P.X) :
    (DDPFinitePath.firstStep P x y z).x 1 = z := by
  rfl

/-- A one-step cylinder fixes exactly its initial state/action and successor state. -/
private theorem DDPFinitePath.mem_firstStepCylinder_iff
    (P : DiscreteDecisionProcess) (x : P.X) (y : P.Y x) (z : P.X)
    (p : DDPPath P) :
    p ∈ DDPCylinder P (DDPFinitePath.firstStep P x y z) ↔
      p.x 0 = x ∧ HEq (p.y 0) y ∧ p.x 1 = z := by
  change p.prefix P 1 = DDPFinitePath.firstStep P x y z ↔ _
  constructor
  · intro hp
    have hx0 := congrArg (fun q : DDPFinitePath P 1 => q.x 0) hp
    have hx1 := congrArg (fun q : DDPFinitePath P 1 => q.x 1) hp
    have hstage := congrArg (fun q : DDPFinitePath P 1 =>
      (⟨q.x 0, q.y 0⟩ : DDPStage P)) hp
    refine ⟨?_, ?_, ?_⟩
    · simpa [DDPPath.prefix] using hx0
    · exact (Sigma.mk.inj_iff.mp hstage).2
    · simpa [DDPPath.prefix] using hx1
  · rintro ⟨hx0, hy0, hx1⟩
    apply DDPFinitePath.ext_of_stages P
    · intro i
      fin_cases i
      · simpa [DDPPath.prefix] using hx0
      · simpa [DDPPath.prefix] using hx1
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact Sigma.ext hx0 hy0

/-- Fixing the initial DDP state and action is measurable in the cylinder sigma algebra. -/
private theorem measurableSet_ddpInitialStateAction
    (P : DiscreteDecisionProcess) (x : P.X) (y : P.Y x) :
    MeasurableSet {p : DDPPath P | p.x 0 = x ∧ HEq (p.y 0) y} := by
  have heq : {p : DDPPath P | p.x 0 = x ∧ HEq (p.y 0) y} =
      ⋃ z : P.X, DDPCylinder P (DDPFinitePath.firstStep P x y z) := by
    ext p
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨hx, hy⟩
      refine ⟨p.x 1, ?_⟩
      exact (DDPFinitePath.mem_firstStepCylinder_iff P x y (p.x 1) p).2
        ⟨hx, hy, rfl⟩
    · rintro ⟨z, hz⟩
      have hp := (DDPFinitePath.mem_firstStepCylinder_iff P x y z p).1 hz
      exact ⟨hp.1, hp.2.1⟩
  rw [heq]
  exact MeasurableSet.iUnion fun z => measurableSet_ddpCylinder P
    (DDPFinitePath.firstStep P x y z)

/-- The zero-action finite path at a prescribed state. -/
private def DDPFinitePath.atState
    (P : DiscreteDecisionProcess) (x : P.X) : DDPFinitePath P 0 where
  x _ := x
  y i := Fin.elim0 i

/-- A zero-action cylinder fixes exactly the initial state. -/
private theorem DDPFinitePath.mem_atStateCylinder_iff
    (P : DiscreteDecisionProcess) (x : P.X) (p : DDPPath P) :
    p ∈ DDPCylinder P (DDPFinitePath.atState P x) ↔ p.x 0 = x := by
  change p.prefix P 0 = DDPFinitePath.atState P x ↔ _
  constructor
  · intro hp
    have hx := congrArg (fun q : DDPFinitePath P 0 => q.x 0) hp
    simpa [DDPPath.prefix, DDPFinitePath.atState] using hx
  · intro hx
    apply DDPFinitePath.ext_of_stages P
    · intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa [DDPPath.prefix, DDPFinitePath.atState] using hx
    · intro i
      exact Fin.elim0 i

/-- Fixing the initial DDP state is measurable. -/
private theorem measurableSet_ddpInitialState
    (P : DiscreteDecisionProcess) (x : P.X) :
    MeasurableSet {p : DDPPath P | p.x 0 = x} := by
  have heq : {p : DDPPath P | p.x 0 = x} =
      DDPCylinder P (DDPFinitePath.atState P x) := by
    ext p
    exact (DDPFinitePath.mem_atStateCylinder_iff P x p).symm
  rw [heq]
  exact measurableSet_ddpCylinder P (DDPFinitePath.atState P x)

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
  let fromState : P.X → Measure (DDPPath P) := fun x =>
    Measure.map (DDPPath.ofRaw P) (P.rawLawFrom x)
  let afterAction : (x : P.X) → P.Y x → Measure (DDPPath P) := fun x y =>
    Measure.map (DDPPath.ofRaw P) (P.rawLawAfterAction x y)
  have hfromProbability (x : P.X) : IsProbabilityMeasure (fromState x) := by
    exact Measure.isProbabilityMeasure_map (DDPPath.measurable_ofRaw P).aemeasurable
  have hafterProbability (x : P.X) (y : P.Y x) :
      IsProbabilityMeasure (afterAction x y) := by
    exact Measure.isProbabilityMeasure_map (DDPPath.measurable_ofRaw P).aemeasurable
  have hfromCylinder (x : P.X) (k : ℕ) (h : DDPFinitePath P k)
      (hstart : h.x 0 = x) :
      fromState x (DDPCylinder P h) = h.probability P := by
    change Measure.map (DDPPath.ofRaw P) (P.rawLawFrom x) (DDPCylinder P h) = _
    rw [Measure.map_apply (DDPPath.measurable_ofRaw P)
      (measurableSet_ddpCylinder P h)]
    exact P.rawLawFrom_ddpCylinder x h hstart
  have hafterCylinder (x : P.X) (y : P.Y x) (k : ℕ)
      (h : DDPFinitePath P (k + 1)) (hstart : h.x 0 = x)
      (haction : HEq (h.y 0) y) :
      afterAction x y (DDPCylinder P h) = h.afterActionProbability P := by
    change Measure.map (DDPPath.ofRaw P) (P.rawLawAfterAction x y)
      (DDPCylinder P h) = _
    rw [Measure.map_apply (DDPPath.measurable_ofRaw P)
      (measurableSet_ddpCylinder P h)]
    exact P.rawLawAfterAction_ddpCylinder x y h hstart haction
  have hfromSupport (x : P.X) : fromState x {p | p.x 0 = x} = 1 := by
    have heq : {p : DDPPath P | p.x 0 = x} =
        DDPCylinder P (DDPFinitePath.atState P x) := by
      ext p
      exact (DDPFinitePath.mem_atStateCylinder_iff P x p).symm
    rw [heq]
    simpa [DDPFinitePath.probability] using
      hfromCylinder x 0 (DDPFinitePath.atState P x) rfl
  have hafterSupport (x : P.X) (y : P.Y x) :
      afterAction x y {p | p.x 0 = x ∧ HEq (p.y 0) y} = 1 := by
    change Measure.map (DDPPath.ofRaw P) (P.rawLawAfterAction x y)
      {p | p.x 0 = x ∧ HEq (p.y 0) y} = 1
    rw [Measure.map_apply (DDPPath.measurable_ofRaw P)
      (measurableSet_ddpInitialStateAction P x y)]
    have heq : DDPPath.ofRaw P ⁻¹'
          {p : DDPPath P | p.x 0 = x ∧ HEq (p.y 0) y} =
        {stage : ℕ → DDPStage P | ∀ _ : Fin 1, stage 0 = (⟨x, y⟩ : DDPStage P)} := by
      ext stage
      simp only [mem_preimage, mem_setOf_eq]
      constructor
      · rintro ⟨hx, hy⟩ i
        exact Sigma.ext hx hy
      · intro hs
        have hstage := hs 0
        exact ⟨congrArg Sigma.fst hstage,
          (Sigma.mk.inj_iff.mp hstage).2⟩
    rw [heq, DiscreteDecisionProcess.rawLawAfterAction]
    simpa [PMF.pure_apply] using
      P.rawLawWithInitial_exactStageCylinder (PMF.pure (⟨x, y⟩ : DDPStage P))
        0 (fun _ : Fin 1 => (⟨x, y⟩ : DDPStage P))
  have hafterMove (x : P.X) (y : P.Y x) (z : P.X) :
      afterAction x y {p | p.x 1 = z} = P.move x y z := by
    let support : Set (DDPPath P) := {p | p.x 0 = x ∧ HEq (p.y 0) y}
    let successor : Set (DDPPath P) := {p | p.x 1 = z}
    let step := DDPFinitePath.firstStep P x y z
    have hstepStart : step.x 0 = x := rfl
    have hstepAction : HEq (step.y 0) y := by rfl
    have hstepProbability : step.afterActionProbability P = P.move x y z := by
      simp [step, DDPFinitePath.firstStep, DDPFinitePath.afterActionProbability]
      exact congrArg (P.move x y)
        (DDPFinitePath.firstStep_x_one P x y z)
    have hcylinder : afterAction x y (DDPCylinder P step) = P.move x y z := by
      rw [hafterCylinder x y 0 step hstepStart hstepAction, hstepProbability]
    have hcylinderSet : DDPCylinder P step = support ∩ successor := by
      ext p
      rw [DDPFinitePath.mem_firstStepCylinder_iff]
      simp only [support, successor, mem_inter_iff, mem_setOf_eq]
      tauto
    letI : IsProbabilityMeasure (afterAction x y) := hafterProbability x y
    have hsupport : afterAction x y support = 1 := hafterSupport x y
    have hsupportMeasurable : MeasurableSet support :=
      measurableSet_ddpInitialStateAction P x y
    have hsupportComplement : afterAction x y supportᶜ = 0 := by
      rw [measure_compl hsupportMeasurable (by rw [hsupport]; simp)]
      rw [measure_univ, hsupport]
      simp
    have hsupportAE : ∀ᵐ p ∂afterAction x y, p ∈ support := by
      rw [ae_iff]
      simpa only [Set.compl_def, mem_setOf_eq] using hsupportComplement
    calc
      afterAction x y {p | p.x 1 = z} = afterAction x y (support ∩ successor) := by
        apply measure_congr
        filter_upwards [hsupportAE] with p hp
        change (p.x 1 = z) = (p ∈ support ∧ p.x 1 = z)
        apply propext
        exact (and_iff_right hp).symm
      _ = afterAction x y (DDPCylinder P step) := by rw [hcylinderSet]
      _ = P.move x y z := hcylinder
  refine ⟨{
    law := fromState P.initial
    probability := hfromProbability P.initial
    lawSupport := hfromSupport P.initial
    cylinder := fun k h hstart => hfromCylinder P.initial k h hstart
    fromState := fromState
    fromStateProbability := hfromProbability
    fromStateSupport := hfromSupport
    fromStateCylinder := hfromCylinder
    lawFromInitial := rfl
    afterAction := afterAction
    afterActionProbability := hafterProbability
    afterActionSupport := hafterSupport
    afterActionMove := hafterMove
    afterActionCylinder := hafterCylinder
  }⟩

/-- Finite DDP cylinders form a π-system: intersecting compatible prefixes keeps the longer one. -/
private theorem isPiSystem_ddpCylinders (P : DiscreteDecisionProcess) :
    IsPiSystem {U | ∃ k, ∃ h : DDPFinitePath P k, U = DDPCylinder P h} := by
  rintro _ ⟨k, h, rfl⟩ _ ⟨l, g, rfl⟩ ⟨p, hp, pg⟩
  by_cases hkl : k ≤ l
  · refine ⟨l, g, ?_⟩
    ext q
    simp only [mem_inter_iff]
    constructor
    · exact fun hq => hq.2
    · intro hqg
      refine ⟨?_, hqg⟩
      change q.prefix P k = h
      have hlate : q.prefix P l = p.prefix P l := hqg.trans pg.symm
      exact (DDPPath.prefix_eq_of_prefix_eq_of_le P hkl hlate).trans hp
  · have hlk : l ≤ k := Nat.le_of_not_ge hkl
    refine ⟨k, h, ?_⟩
    ext q
    simp only [mem_inter_iff]
    constructor
    · exact fun hq => hq.1
    · intro hqh
      refine ⟨hqh, ?_⟩
      change q.prefix P l = g
      have hlate : q.prefix P k = p.prefix P k := hqh.trans hp.symm
      exact (DDPPath.prefix_eq_of_prefix_eq_of_le P hlk hlate).trans pg

/-- Cylinder probabilities uniquely determine the DDP law carried by a semantics bundle. -/
private theorem DDPSemantics.law_eq_rawLaw (P : DiscreteDecisionProcess)
    (S : DDPSemantics P) :
    S.law = Measure.map (DDPPath.ofRaw P) (P.rawLawFrom P.initial) := by
  let canonical := Measure.map (DDPPath.ofRaw P) (P.rawLawFrom P.initial)
  letI : IsProbabilityMeasure S.law := S.probability
  letI : IsProbabilityMeasure canonical :=
    Measure.isProbabilityMeasure_map (DDPPath.measurable_ofRaw P).aemeasurable
  let support : Set (DDPPath P) := {p | p.x 0 = P.initial}
  have hcanonicalSupport : canonical support = 1 := by
    have heq : support = DDPCylinder P (DDPFinitePath.atState P P.initial) := by
      ext p
      exact (DDPFinitePath.mem_atStateCylinder_iff P P.initial p).symm
    rw [heq]
    dsimp only [canonical]
    rw [Measure.map_apply (DDPPath.measurable_ofRaw P)
      (measurableSet_ddpCylinder P (DDPFinitePath.atState P P.initial))]
    simpa [DDPFinitePath.probability] using
      P.rawLawFrom_ddpCylinder P.initial (DDPFinitePath.atState P P.initial) rfl
  have cylinder_zero_of_wrong_start (mu : Measure (DDPPath P))
      [IsProbabilityMeasure mu] (hsupport : mu support = 1)
      {k : ℕ} (h : DDPFinitePath P k) (hwrong : h.x 0 ≠ P.initial) :
      mu (DDPCylinder P h) = 0 := by
    have hsupportMeasurable : MeasurableSet support :=
      measurableSet_ddpInitialState P P.initial
    have hsupportComplement : mu supportᶜ = 0 := by
      rw [measure_compl hsupportMeasurable (by rw [hsupport]; simp)]
      rw [measure_univ, hsupport]
      simp
    apply nonpos_iff_eq_zero.mp
    exact calc
      mu (DDPCylinder P h) ≤ mu supportᶜ := by
        apply measure_mono
        intro p hp
        simp only [support, mem_compl_iff, mem_setOf_eq]
        intro hpstart
        apply hwrong
        change p.prefix P k = h at hp
        have hx := congrArg (fun q : DDPFinitePath P k => q.x 0) hp
        simpa [DDPPath.prefix, hpstart] using hx.symm
      _ = 0 := hsupportComplement
  apply ext_of_generate_finite
    {U | ∃ k, ∃ h : DDPFinitePath P k, U = DDPCylinder P h}
    rfl (isPiSystem_ddpCylinders P)
  · intro U hU
    rcases hU with ⟨k, h, rfl⟩
    by_cases hstart : h.x 0 = P.initial
    · rw [S.cylinder k h hstart]
      rw [Measure.map_apply (DDPPath.measurable_ofRaw P)
        (measurableSet_ddpCylinder P h)]
      exact (P.rawLawFrom_ddpCylinder P.initial h hstart).symm
    · rw [cylinder_zero_of_wrong_start S.law S.lawSupport h hstart]
      exact (cylinder_zero_of_wrong_start canonical hcanonicalSupport h hstart).symm
  · simp

/-- Cylinder semantics also uniquely determine every state-restarted DDP law. -/
private theorem DDPSemantics.fromState_eq_rawLaw (P : DiscreteDecisionProcess)
    (S : DDPSemantics P) (start : P.X) :
    S.fromState start = Measure.map (DDPPath.ofRaw P) (P.rawLawFrom start) := by
  let canonical := Measure.map (DDPPath.ofRaw P) (P.rawLawFrom start)
  letI : IsProbabilityMeasure (S.fromState start) := S.fromStateProbability start
  letI : IsProbabilityMeasure canonical :=
    Measure.isProbabilityMeasure_map (DDPPath.measurable_ofRaw P).aemeasurable
  let support : Set (DDPPath P) := {p | p.x 0 = start}
  have hcanonicalSupport : canonical support = 1 := by
    have heq : support = DDPCylinder P (DDPFinitePath.atState P start) := by
      ext p
      exact (DDPFinitePath.mem_atStateCylinder_iff P start p).symm
    rw [heq]
    dsimp only [canonical]
    rw [Measure.map_apply (DDPPath.measurable_ofRaw P)
      (measurableSet_ddpCylinder P (DDPFinitePath.atState P start))]
    simpa [DDPFinitePath.probability] using
      P.rawLawFrom_ddpCylinder start (DDPFinitePath.atState P start) rfl
  have cylinder_zero_of_wrong_start (mu : Measure (DDPPath P))
      [IsProbabilityMeasure mu] (hsupport : mu support = 1)
      {k : ℕ} (h : DDPFinitePath P k) (hwrong : h.x 0 ≠ start) :
      mu (DDPCylinder P h) = 0 := by
    have hsupportMeasurable : MeasurableSet support :=
      measurableSet_ddpInitialState P start
    have hsupportComplement : mu supportᶜ = 0 := by
      rw [measure_compl hsupportMeasurable (by rw [hsupport]; simp)]
      rw [measure_univ, hsupport]
      simp
    apply nonpos_iff_eq_zero.mp
    exact calc
      mu (DDPCylinder P h) ≤ mu supportᶜ := by
        apply measure_mono
        intro p hp
        simp only [support, mem_compl_iff, mem_setOf_eq]
        intro hpstart
        apply hwrong
        change p.prefix P k = h at hp
        have hx := congrArg (fun q : DDPFinitePath P k => q.x 0) hp
        simpa [DDPPath.prefix, hpstart] using hx.symm
      _ = 0 := hsupportComplement
  apply ext_of_generate_finite
    {U | ∃ k, ∃ h : DDPFinitePath P k, U = DDPCylinder P h}
    rfl (isPiSystem_ddpCylinders P)
  · intro U hU
    rcases hU with ⟨k, h, rfl⟩
    by_cases hstart : h.x 0 = start
    · rw [S.fromStateCylinder start k h hstart]
      rw [Measure.map_apply (DDPPath.measurable_ofRaw P)
        (measurableSet_ddpCylinder P h)]
      exact (P.rawLawFrom_ddpCylinder start h hstart).symm
    · rw [cylinder_zero_of_wrong_start (S.fromState start)
        (S.fromStateSupport start) h hstart]
      exact (cylinder_zero_of_wrong_start canonical hcanonicalSupport h hstart).symm
  · simp

/-- Cylinder semantics uniquely determine every forced-first-action DDP law. -/
private theorem DDPSemantics.afterAction_eq_rawLaw (P : DiscreteDecisionProcess)
    (S : DDPSemantics P) (x : P.X) (y : P.Y x) :
    S.afterAction x y = Measure.map (DDPPath.ofRaw P) (P.rawLawAfterAction x y) := by
  classical
  let canonical := Measure.map (DDPPath.ofRaw P) (P.rawLawAfterAction x y)
  let support : Set (DDPPath P) := {p | p.x 0 = x ∧ HEq (p.y 0) y}
  letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
  letI : IsProbabilityMeasure canonical :=
    Measure.isProbabilityMeasure_map (DDPPath.measurable_ofRaw P).aemeasurable
  have hcanonicalSupport : canonical support = 1 := by
    dsimp only [canonical, support]
    rw [Measure.map_apply (DDPPath.measurable_ofRaw P)
      (measurableSet_ddpInitialStateAction P x y)]
    have heq : DDPPath.ofRaw P ⁻¹'
          {p : DDPPath P | p.x 0 = x ∧ HEq (p.y 0) y} =
        {stage : ℕ → DDPStage P |
          ∀ _ : Fin 1, stage 0 = (⟨x, y⟩ : DDPStage P)} := by
      ext stage
      simp only [mem_preimage, mem_setOf_eq]
      constructor
      · rintro ⟨hx, hy⟩ i
        exact Sigma.ext hx hy
      · intro hs
        have hstage := hs 0
        exact ⟨congrArg Sigma.fst hstage, (Sigma.mk.inj_iff.mp hstage).2⟩
    rw [heq, DiscreteDecisionProcess.rawLawAfterAction]
    simpa [PMF.pure_apply] using
      P.rawLawWithInitial_exactStageCylinder (PMF.pure (⟨x, y⟩ : DDPStage P))
        0 (fun _ : Fin 1 => (⟨x, y⟩ : DDPStage P))
  have cylinder_zero_of_wrong_support (mu : Measure (DDPPath P))
      [IsProbabilityMeasure mu] (hsupport : mu support = 1)
      {k : ℕ} (h : DDPFinitePath P (k + 1))
      (hwrong : h.x 0 ≠ x ∨ ¬HEq (h.y 0) y) :
      mu (DDPCylinder P h) = 0 := by
    have hsupportMeasurable : MeasurableSet support :=
      measurableSet_ddpInitialStateAction P x y
    have hsupportComplement : mu supportᶜ = 0 := by
      rw [measure_compl hsupportMeasurable (by rw [hsupport]; simp)]
      rw [measure_univ, hsupport]
      simp
    apply nonpos_iff_eq_zero.mp
    exact calc
      mu (DDPCylinder P h) ≤ mu supportᶜ := by
        apply measure_mono
        intro p hp
        simp only [support, mem_compl_iff, mem_setOf_eq]
        rintro ⟨hpstart, hpaction⟩
        change p.prefix P (k + 1) = h at hp
        have hx := congrArg (fun q : DDPFinitePath P (k + 1) => q.x 0) hp
        have hstage := congrArg (fun q : DDPFinitePath P (k + 1) =>
          (⟨q.x 0, q.y 0⟩ : DDPStage P)) hp
        rcases hwrong with hstart | haction
        · apply hstart
          simpa [DDPPath.prefix, hpstart] using hx.symm
        · apply haction
          exact (Sigma.mk.inj_iff.mp hstage.symm).2.trans hpaction
      _ = 0 := hsupportComplement
  have zeroCylinder_eq_initialState {h : DDPFinitePath P 0} :
      DDPCylinder P h = {p | p.x 0 = h.x 0} := by
    ext p
    change p.prefix P 0 = h ↔ p.x 0 = h.x 0
    constructor
    · intro hp
      exact congrArg (fun q : DDPFinitePath P 0 => q.x 0) hp
    · intro hp
      apply DDPFinitePath.ext_of_stages P
      · intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        exact hp
      · exact fun i => Fin.elim0 i
  have zeroCylinder_measure (mu : Measure (DDPPath P)) [IsProbabilityMeasure mu]
      (hsupport : mu support = 1) (h : DDPFinitePath P 0) :
      mu (DDPCylinder P h) = if h.x 0 = x then 1 else 0 := by
    split_ifs with hstart
    · apply le_antisymm (by
        calc
          mu (DDPCylinder P h) ≤ mu Set.univ := measure_mono (subset_univ _)
          _ = 1 := measure_univ)
      calc
        1 = mu support := hsupport.symm
        _ ≤ mu (DDPCylinder P h) := by
          apply measure_mono
          intro p hp
          rw [zeroCylinder_eq_initialState]
          exact hstart.trans hp.1.symm |>.symm
    · apply nonpos_iff_eq_zero.mp
      calc
        mu (DDPCylinder P h) ≤ mu supportᶜ := by
          apply measure_mono
          intro p hp
          simp only [support, mem_compl_iff, mem_setOf_eq]
          intro hs
          apply hstart
          rw [zeroCylinder_eq_initialState] at hp
          exact hp.symm.trans hs.1
        _ = 0 := by
          rw [measure_compl (measurableSet_ddpInitialStateAction P x y)
            (by rw [hsupport]; simp)]
          rw [measure_univ, hsupport]
          simp
  apply ext_of_generate_finite
    {U | ∃ k, ∃ h : DDPFinitePath P k, U = DDPCylinder P h}
    rfl (isPiSystem_ddpCylinders P)
  · intro U hU
    rcases hU with ⟨k, h, rfl⟩
    cases k with
    | zero =>
        rw [zeroCylinder_measure (S.afterAction x y) (S.afterActionSupport x y) h]
        rw [zeroCylinder_measure canonical hcanonicalSupport h]
    | succ k =>
        by_cases hstart : h.x 0 = x
        · by_cases haction : HEq (h.y 0) y
          · rw [S.afterActionCylinder x y k h hstart haction]
            rw [Measure.map_apply (DDPPath.measurable_ofRaw P)
              (measurableSet_ddpCylinder P h)]
            exact (P.rawLawAfterAction_ddpCylinder x y h hstart haction).symm
          · rw [cylinder_zero_of_wrong_support (S.afterAction x y)
              (S.afterActionSupport x y) h (Or.inr haction)]
            exact (cylinder_zero_of_wrong_support canonical hcanonicalSupport h
              (Or.inr haction)).symm
        · rw [cylinder_zero_of_wrong_support (S.afterAction x y)
            (S.afterActionSupport x y) h (Or.inl hstart)]
          exact (cylinder_zero_of_wrong_support canonical hcanonicalSupport h
            (Or.inl hstart)).symm
  · simp

/-- A forced-action cylinder with the wrong initial state or action has zero mass. -/
private theorem DDPSemantics.afterAction_cylinder_eq_zero_of_wrong
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (x : P.X) (y : P.Y x) {k : ℕ} (h : DDPFinitePath P (k + 1))
    (hwrong : h.x 0 ≠ x ∨ ¬HEq (h.y 0) y) :
    S.afterAction x y (DDPCylinder P h) = 0 := by
  let support : Set (DDPPath P) := {p | p.x 0 = x ∧ HEq (p.y 0) y}
  letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
  have hsupportMeasurable : MeasurableSet support :=
    measurableSet_ddpInitialStateAction P x y
  have hsupportComplement : S.afterAction x y supportᶜ = 0 := by
    rw [measure_compl hsupportMeasurable (by rw [S.afterActionSupport]; simp)]
    rw [measure_univ, S.afterActionSupport]
    simp
  apply nonpos_iff_eq_zero.mp
  exact calc
    S.afterAction x y (DDPCylinder P h) ≤ S.afterAction x y supportᶜ := by
      apply measure_mono
      intro p hp
      simp only [support, mem_compl_iff, mem_setOf_eq]
      rintro ⟨hpstart, hpaction⟩
      change p.prefix P (k + 1) = h at hp
      have hx := congrArg (fun q : DDPFinitePath P (k + 1) => q.x 0) hp
      have hstage := congrArg (fun q : DDPFinitePath P (k + 1) =>
        (⟨q.x 0, q.y 0⟩ : DDPStage P)) hp
      rcases hwrong with hstart | haction
      · apply hstart
        simpa [DDPPath.prefix, hpstart] using hx.symm
      · apply haction
        exact (Sigma.mk.inj_iff.mp hstage.symm).2.trans hpaction
    _ = 0 := hsupportComplement

/-- A wrong forced-action cylinder has zero mass under the raw law. -/
private theorem DiscreteDecisionProcess.rawLawAfterAction_ddpCylinder_eq_zero_of_wrong
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (x : P.X) (y : P.Y x) {k : ℕ} (h : DDPFinitePath P (k + 1))
    (hwrong : h.x 0 ≠ x ∨ ¬HEq (h.y 0) y) :
    P.rawLawAfterAction x y (DDPPath.ofRaw P ⁻¹' DDPCylinder P h) = 0 := by
  have hcanonical := congrArg (fun mu : Measure (DDPPath P) => mu (DDPCylinder P h))
    (S.afterAction_eq_rawLaw P x y)
  rw [Measure.map_apply (DDPPath.measurable_ofRaw P) (measurableSet_ddpCylinder P h)]
    at hcanonical
  rw [← hcanonical]
  exact S.afterAction_cylinder_eq_zero_of_wrong P x y h hwrong

/-- A wrong forced-action cylinder also has zero raw-law integral. -/
private theorem DiscreteDecisionProcess.integral_rawStageValue_ddpCylinder_eq_zero_of_wrong
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (x : P.X) (y : P.Y x) {k : ℕ} (h : DDPFinitePath P (k + 1))
    (hwrong : h.x 0 ≠ x ∨ ¬HEq (h.y 0) y) :
    (∫ stage in DDPPath.ofRaw P ⁻¹' DDPCylinder P h,
      P.rawStageValue (k + 1) stage ∂P.rawLawAfterAction x y) = 0 := by
  apply setIntegral_measure_zero
  exact P.rawLawAfterAction_ddpCylinder_eq_zero_of_wrong S x y h hwrong

/-- A state-started cylinder with the wrong initial state has zero mass. -/
private theorem DDPSemantics.fromState_cylinder_eq_zero_of_wrong
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (x : P.X) {k : ℕ} (h : DDPFinitePath P k) (hwrong : h.x 0 ≠ x) :
    S.fromState x (DDPCylinder P h) = 0 := by
  let support : Set (DDPPath P) := {p | p.x 0 = x}
  letI : IsProbabilityMeasure (S.fromState x) := S.fromStateProbability x
  have hsupportMeasurable : MeasurableSet support := measurableSet_ddpInitialState P x
  have hsupportComplement : S.fromState x supportᶜ = 0 := by
    rw [measure_compl hsupportMeasurable (by rw [S.fromStateSupport]; simp)]
    rw [measure_univ, S.fromStateSupport]
    simp
  apply nonpos_iff_eq_zero.mp
  exact calc
    S.fromState x (DDPCylinder P h) ≤ S.fromState x supportᶜ := by
      apply measure_mono
      intro p hp
      simp only [support, mem_compl_iff, mem_setOf_eq]
      intro hpstart
      apply hwrong
      change p.prefix P k = h at hp
      have hx := congrArg (fun q : DDPFinitePath P k => q.x 0) hp
      simpa [DDPPath.prefix, hpstart] using hx.symm
    _ = 0 := hsupportComplement

/-- A wrong state-started cylinder has zero mass under the raw law. -/
private theorem DiscreteDecisionProcess.rawLawFrom_ddpCylinder_eq_zero_of_wrong
    (P : DiscreteDecisionProcess) (S : DDPSemantics P) (start : P.X)
    {k : ℕ} (h : DDPFinitePath P k) (hwrong : h.x 0 ≠ start) :
    P.rawLawFrom start (DDPPath.ofRaw P ⁻¹' DDPCylinder P h) = 0 := by
  have hcanonical := congrArg (fun mu : Measure (DDPPath P) => mu (DDPCylinder P h))
    (S.fromState_eq_rawLaw P start)
  rw [Measure.map_apply (DDPPath.measurable_ofRaw P) (measurableSet_ddpCylinder P h)]
    at hcanonical
  rw [← hcanonical]
  exact S.fromState_cylinder_eq_zero_of_wrong P start h hwrong

/-- A zero-action DDP cylinder fixes only its initial state. -/
private theorem ddpCylinder_zero_eq_initialState (P : DiscreteDecisionProcess)
    (h : DDPFinitePath P 0) : DDPCylinder P h = {p | p.x 0 = h.x 0} := by
  ext p
  change p.prefix P 0 = h ↔ p.x 0 = h.x 0
  constructor
  · intro hp
    exact congrArg (fun q : DDPFinitePath P 0 => q.x 0) hp
  · intro hp
    apply DDPFinitePath.ext_of_stages P
    · intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact hp
    · exact fun i => Fin.elim0 i

/-- A forced-action law gives its initial-state zero cylinder mass one. -/
private theorem DDPSemantics.afterAction_zeroCylinder_eq_one
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (x : P.X) (y : P.Y x) (h : DDPFinitePath P 0) (hstart : h.x 0 = x) :
    S.afterAction x y (DDPCylinder P h) = 1 := by
  letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
  rw [ddpCylinder_zero_eq_initialState]
  apply le_antisymm (by
    calc
      S.afterAction x y {p | p.x 0 = h.x 0} ≤ S.afterAction x y Set.univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ)
  calc
    1 = S.afterAction x y {p | p.x 0 = x ∧ HEq (p.y 0) y} :=
      (S.afterActionSupport x y).symm
    _ ≤ S.afterAction x y {p | p.x 0 = h.x 0} := by
      apply measure_mono
      rintro p ⟨hp, _hy⟩
      exact hstart.trans hp.symm |>.symm

/-- A forced-action law gives a wrong initial-state zero cylinder mass zero. -/
private theorem DDPSemantics.afterAction_zeroCylinder_eq_zero
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (x : P.X) (y : P.Y x) (h : DDPFinitePath P 0) (hstart : h.x 0 ≠ x) :
    S.afterAction x y (DDPCylinder P h) = 0 := by
  rw [ddpCylinder_zero_eq_initialState]
  have hsubset : {p : DDPPath P | p.x 0 = h.x 0} ⊆
      {p | p.x 0 = x ∧ HEq (p.y 0) y}ᶜ := by
    intro p hp
    simp only [mem_setOf_eq, mem_compl_iff]
    intro hs
    exact hstart (hp.symm.trans hs.1)
  apply nonpos_iff_eq_zero.mp
  calc
    S.afterAction x y {p | p.x 0 = h.x 0} ≤
        S.afterAction x y {p | p.x 0 = x ∧ HEq (p.y 0) y}ᶜ :=
      measure_mono hsubset
    _ = 0 := by
      rw [measure_compl (measurableSet_ddpInitialStateAction P x y)
        (by rw [S.afterActionSupport]; simp)]
      letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
      rw [measure_univ, S.afterActionSupport]
      simp

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

/-- Each finite cumulative advantage is measurable in the cylinder sigma algebra. -/
private theorem DDPAdvantage.measurable (P : DiscreteDecisionProcess) (l : ℕ) :
    Measurable (DDPAdvantage P · l) := by
  have hmeasurable : Measurable (fun h : DDPFinitePath P (l + 1) => h.advantage P) :=
    Measurable.of_discrete
  convert hmeasurable.comp (DDPPath.measurable_prefix P (l + 1)) using 1
  funext p
  exact (DDPFinitePath.advantage_prefix P p l).symm

/-- Each individual value increment is measurable in the cylinder sigma algebra. -/
private theorem DDPPath.measurable_increment (P : DiscreteDecisionProcess) (i : ℕ) :
    Measurable (fun p : DDPPath P =>
      P.valueY (p.x i) (p.y i) - P.valueX (p.x i)) := by
  cases i with
  | zero => simpa [DDPAdvantage] using DDPAdvantage.measurable P 0
  | succ i =>
      have heq : (fun p : DDPPath P =>
          P.valueY (p.x (i + 1)) (p.y (i + 1)) - P.valueX (p.x (i + 1))) =
          fun p => DDPAdvantage P p (i + 1) - DDPAdvantage P p i := by
        funext p
        simp only [DDPAdvantage, Finset.sum_range_succ]
        ring
      rw [heq]
      exact (DDPAdvantage.measurable P (i + 1)).sub (DDPAdvantage.measurable P i)

/-- Total variation is measurable as a countable sum of measurable increments. -/
private theorem DDPTotalVariation.measurable (P : DiscreteDecisionProcess) :
    Measurable (DDPTotalVariation P) := by
  apply Measurable.tsum
  intro i
  exact (DDPPath.measurable_increment P i).abs.ennreal_ofReal

/-- Absolute cumulative-advantage crossing is a measurable event. -/
private theorem measurableSet_ddpAbsoluteAdvantage_crossing
    (P : DiscreteDecisionProcess) (epsilon : ℝ) :
    MeasurableSet {p | ∃ l, |DDPAdvantage P p l| ≥ epsilon} := by
  rw [show {p | ∃ l, |DDPAdvantage P p l| ≥ epsilon} =
      ⋃ l, {p | epsilon ≤ |DDPAdvantage P p l|} by ext; simp]
  exact MeasurableSet.iUnion fun l =>
    ((DDPAdvantage.measurable P l).abs measurableSet_Ici)

/-- On raw sampled stages, the displayed and raw cumulative advantages coincide. -/
@[simp] private theorem DiscreteDecisionProcess.advantage_ofRaw
    (P : DiscreteDecisionProcess) (stage : ℕ → DDPStage P) (l : ℕ) :
    DDPAdvantage P (DDPPath.ofRaw P stage) l = P.rawAdvantage stage l := rfl

/-- On raw sampled stages, the displayed total variation is the increment sum. -/
@[simp] private theorem DiscreteDecisionProcess.totalVariation_ofRaw
    (P : DiscreteDecisionProcess) (stage : ℕ → DDPStage P) :
    DDPTotalVariation P (DDPPath.ofRaw P stage) =
      ∑' i, ENNReal.ofReal |DDPStage.increment P (stage i)| := rfl

/-- Total absolute increment through time `n` on the raw trajectory space. -/
private def DiscreteDecisionProcess.rawPartialVariation
    (P : DiscreteDecisionProcess) (stage : ℕ → DDPStage P) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), |DDPStage.increment P (stage i)|

/-- A finite raw variation is measurable and nonnegative. -/
private theorem DiscreteDecisionProcess.measurable_rawPartialVariation
    (P : DiscreteDecisionProcess) (n : ℕ) :
    Measurable (fun stage => P.rawPartialVariation stage n) := by
  refine Finset.measurable_sum (f := fun i (stage : ℕ → DDPStage P) =>
    |DDPStage.increment P (stage i)|) (Finset.range (n + 1)) ?_
  intro i _hi
  have hincrement : Measurable (DDPStage.increment P) := Measurable.of_discrete
  exact (hincrement.comp
    (measurable_pi_apply (X := fun _ : ℕ => DDPStage P) i)).abs

private theorem DiscreteDecisionProcess.rawPartialVariation_nonneg
    (P : DiscreteDecisionProcess) (stage : ℕ → DDPStage P) (n : ℕ) :
    0 ≤ P.rawPartialVariation stage n := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- A finite raw variation is bounded by the displayed increment bound. -/
private theorem DiscreteDecisionProcess.rawPartialVariation_le
    (P : DiscreteDecisionProcess) (stage : ℕ → DDPStage P) (n : ℕ) :
    P.rawPartialVariation stage n ≤ (n + 1) * P.valueDifferenceBound := by
  calc
    P.rawPartialVariation stage n ≤
        ∑ _i ∈ Finset.range (n + 1), P.valueDifferenceBound := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa only [Real.norm_eq_abs] using (stage i).norm_increment_le P
    _ = (n + 1) * P.valueDifferenceBound := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      rfl

/-- Every finite raw variation is integrable. -/
private theorem DiscreteDecisionProcess.integrable_rawPartialVariation
    (P : DiscreteDecisionProcess) (n : ℕ) :
    Integrable (fun stage => P.rawPartialVariation stage n) (P.rawLawFrom P.initial) := by
  apply Integrable.of_bound (P.measurable_rawPartialVariation n).aestronglyMeasurable
    ((n + 1) * P.valueDifferenceBound)
  exact ae_of_all _ fun stage => by
    rw [Real.norm_eq_abs, abs_of_nonneg (P.rawPartialVariation_nonneg stage n)]
    exact P.rawPartialVariation_le stage n

/-- Finite raw cumulative-advantage squares are integrable. -/
private theorem DiscreteDecisionProcess.integrable_rawAdvantage_sq
    (P : DiscreteDecisionProcess) (n : ℕ) :
    Integrable (fun stage => (P.rawAdvantage stage n) ^ 2)
      (P.rawLawFrom P.initial) := by
  apply Integrable.of_bound
    (((P.rawAdvantage_stronglyAdapted n).mono
      (Filtration.le (Filtration.piLE (X := fun _ : ℕ => DDPStage P)) n)).pow 2
        |>.aestronglyMeasurable)
    (((n + 1) * P.valueDifferenceBound) ^ 2)
  exact ae_of_all _ fun stage => by
    change ‖P.rawAdvantage stage n ^ 2‖ ≤ _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (P.norm_rawAdvantage_le stage n) 2

/-- Products at two successive times of the raw martingale are integrable. -/
private theorem DiscreteDecisionProcess.integrable_rawAdvantage_mul_succ
    (P : DiscreteDecisionProcess) (n : ℕ) :
    Integrable (fun stage => P.rawAdvantage stage n * P.rawAdvantage stage (n + 1))
      (P.rawLawFrom P.initial) := by
  apply Integrable.of_bound
    ((((P.rawAdvantage_stronglyAdapted n).mono
      (Filtration.le (Filtration.piLE (X := fun _ : ℕ => DDPStage P)) n)).mul
      ((P.rawAdvantage_stronglyAdapted (n + 1)).mono
        (Filtration.le (Filtration.piLE (X := fun _ : ℕ => DDPStage P)) (n + 1))))
          |>.aestronglyMeasurable)
    (((n + 1) * P.valueDifferenceBound) * ((n + 2) * P.valueDifferenceBound))
  exact ae_of_all _ fun stage => by
    change ‖P.rawAdvantage stage n * P.rawAdvantage stage (n + 1)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (P.norm_rawAdvantage_le stage n)
      (by
        calc
          ‖P.rawAdvantage stage (n + 1)‖ ≤
              ((n + 1 : ℕ) + 1) * P.valueDifferenceBound :=
            P.norm_rawAdvantage_le stage (n + 1)
          _ = (n + 2) * P.valueDifferenceBound := by
            congr 1
            rw [Nat.cast_add, Nat.cast_one]
            ring)
      (norm_nonneg _)
      (mul_nonneg (by positivity) (le_trans zero_le_one P.valueDifferenceBound_one))

/-- The squares of the raw cumulative advantages form a submartingale. -/
private theorem DiscreteDecisionProcess.rawAdvantage_square_submartingale
    (P : DiscreteDecisionProcess) :
    Submartingale (fun n stage => (P.rawAdvantage stage n) ^ 2)
      (Filtration.piLE (X := fun _ : ℕ => DDPStage P))
      (P.rawLawFrom P.initial) :=
  martingale_square_submartingale P.rawAdvantage_martingale
    P.integrable_rawAdvantage_sq

/-- Finite raw variation is bounded by the corresponding infinite variation. -/
private theorem DiscreteDecisionProcess.ofReal_rawPartialVariation_le
    (P : DiscreteDecisionProcess) (stage : ℕ → DDPStage P) (n : ℕ) :
    ENNReal.ofReal (P.rawPartialVariation stage n) ≤
      ∑' i, ENNReal.ofReal |DDPStage.increment P (stage i)| := by
  rw [DiscreteDecisionProcess.rawPartialVariation]
  rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _]
  exact ENNReal.sum_le_tsum (Finset.range (n + 1))

/-- A stage sampled from the DDP law uses a positive-probability local action almost surely. -/
private theorem DiscreteDecisionProcess.ae_choose_pos_rawLawFrom
    (P : DiscreteDecisionProcess) (start : P.X) (i : ℕ) :
    ∀ᵐ stage ∂P.rawLawFrom start, 0 < P.choose (stage i).1 (stage i).2 := by
  rw [ae_iff]
  let H := {pref : Fin (i + 1) → DDPStage P //
    ¬0 < P.choose (pref (Fin.last i)).1 (pref (Fin.last i)).2}
  let C : H → Set (ℕ → DDPStage P) := fun pref =>
    {stage | ∀ j : Fin (i + 1), stage j = pref.1 j}
  have hbad : {stage : ℕ → DDPStage P |
      ¬0 < P.choose (stage i).1 (stage i).2} = ⋃ pref, C pref := by
    ext stage
    simp only [mem_setOf_eq, mem_iUnion, C]
    constructor
    · intro hstage
      let pref : Fin (i + 1) → DDPStage P := fun j => stage j
      refine ⟨⟨pref, ?_⟩, fun _ => rfl⟩
      have hlast : stage (Fin.last i) = stage i := by
        exact congrArg stage (Fin.val_last i)
      dsimp only [pref]
      have hprob := congrArg (fun z : DDPStage P => P.choose z.1 z.2) hlast
      rw [hprob]
      exact hstage
    · rintro ⟨pref, hpref⟩
      have hlast := hpref (Fin.last i)
      change ¬0 < P.choose (stage (Fin.last i)).1 (stage (Fin.last i)).2
      have hprob := congrArg (fun z : DDPStage P => P.choose z.1 z.2) hlast
      rw [hprob]
      exact pref.2
  rw [hbad]
  apply nonpos_iff_eq_zero.mp
  calc
    P.rawLawFrom start (⋃ pref, C pref) ≤
        ∑' pref, P.rawLawFrom start (C pref) := measure_iUnion_le _
    _ = 0 := by
      have hzero (pref : H) : P.rawLawFrom start (C pref) = 0 := by
        dsimp only [C]
        rw [P.rawLawFrom_exactStageCylinder]
        have hchoose : P.choose (pref.1 (Fin.last i)).1
            (pref.1 (Fin.last i)).2 = 0 :=
          nonpos_iff_eq_zero.mp (not_lt.mp pref.2)
        cases i with
        | zero =>
            apply mul_eq_zero_of_left
            have hlast : pref.1 (Fin.last 0) = pref.1 0 := by
              apply congrArg pref.1
              exact Fin.ext rfl
            rw [hlast] at hchoose
            rcases hstage : pref.1 0 with ⟨state, action⟩
            have hprob := congrArg (fun z : DDPStage P => P.choose z.1 z.2) hstage
            by_cases hstateStart : start = state
            · subst state
              rw [P.initialStagePMF_apply, ← hprob, hchoose]
            · rw [P.initialStagePMF_apply_of_ne action hstateStart]
        | succ k =>
            apply mul_eq_zero_of_right
            apply Finset.prod_eq_zero (Finset.mem_univ (Fin.last k))
            rw [P.stepStagePMF_apply]
            apply mul_eq_zero_of_right
            have hlast : (Fin.last k).succ = Fin.last (k + 1) := Fin.ext (by simp)
            rw [hlast]
            simpa only [Nat.succ_eq_add_one] using hchoose
      simp only [hzero, tsum_zero]

/-- A decision process is `δ`-balanced when every positive-probability chosen-action value
is within `δ` of its state value. -/
def IsBalanced (P : DiscreteDecisionProcess) (δ : ℝ) : Prop :=
  ∀ x y, 0 < P.choose x y → |P.valueY x y - P.valueX x| ≤ δ

/-- The probability that the absolute cumulative advantage ever reaches `ε`. -/
def AbsoluteCrossingProbability (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (ε : ℝ) : ℝ≥0∞ :=
  S.law {p | ∃ l, |DDPAdvantage P p l| ≥ ε}

/-- The expected total variation of the decision process under its induced path law. -/
def ExpectedDDPVariation (P : DiscreteDecisionProcess) (S : DDPSemantics P) : ℝ≥0∞ :=
  ∫⁻ p, DDPTotalVariation P p ∂S.law

/-- An expected-total-variation bound controls every finite raw partial variation. -/
private theorem DiscreteDecisionProcess.integral_rawPartialVariation_le
    (P : DiscreteDecisionProcess) (S : DDPSemantics P) {B : ℝ} (hB : 0 < B)
    (hvariation : ExpectedDDPVariation P S ≤ ENNReal.ofReal B) (n : ℕ) :
    ∫ stage, P.rawPartialVariation stage n ∂P.rawLawFrom P.initial ≤ B := by
  have hfinite : ENNReal.ofReal
      (∫ stage, P.rawPartialVariation stage n ∂P.rawLawFrom P.initial) ≤
      ExpectedDDPVariation P S := by
    rw [ofReal_integral_eq_lintegral_ofReal (P.integrable_rawPartialVariation n)
      (ae_of_all _ fun stage => P.rawPartialVariation_nonneg stage n)]
    rw [ExpectedDDPVariation, S.law_eq_rawLaw]
    rw [lintegral_map (DDPTotalVariation.measurable P) (DDPPath.measurable_ofRaw P)]
    apply lintegral_mono
    intro stage
    simpa only [P.totalVariation_ofRaw] using P.ofReal_rawPartialVariation_le stage n
  exact (ENNReal.ofReal_le_ofReal_iff hB.le).mp (hfinite.trans hvariation)

/-- Orthogonality identifies the raw martingale square expectation with increment squares. -/
private theorem DiscreteDecisionProcess.integral_rawAdvantage_sq_eq_sum
    (P : DiscreteDecisionProcess) (n : ℕ) :
    (∫ stage, (P.rawAdvantage stage n) ^ 2 ∂P.rawLawFrom P.initial) =
      ∑ i ∈ Finset.range (n + 1),
        ∫ stage, (DDPStage.increment P (stage i)) ^ 2 ∂P.rawLawFrom P.initial := by
  have h := martingale_square_integral_eq P.rawAdvantage_martingale
    P.integrable_rawAdvantage_sq P.integrable_rawAdvantage_mul_succ n
  simp_rw [P.rawAdvantage_succ_sub] at h
  have hzero : ∀ stage : ℕ → DDPStage P,
      P.rawAdvantage stage 0 = DDPStage.increment P (stage 0) := by
    intro stage
    simp [DiscreteDecisionProcess.rawAdvantage]
  simp_rw [hzero] at h
  rw [Finset.sum_range_succ']
  simpa only [add_comm] using h

/-- Balance and expected variation bound every raw martingale square expectation. -/
private theorem DiscreteDecisionProcess.integral_rawAdvantage_sq_le
    (P : DiscreteDecisionProcess) (S : DDPSemantics P) {delta B : ℝ}
    (hdelta : 0 < delta) (hB : 0 < B) (hbalanced : IsBalanced P delta)
    (hvariation : ExpectedDDPVariation P S ≤ ENNReal.ofReal B) (n : ℕ) :
    ∫ stage, (P.rawAdvantage stage n) ^ 2 ∂P.rawLawFrom P.initial ≤ delta * B := by
  have habsIntegrable (i : ℕ) : Integrable
      (fun stage : ℕ → DDPStage P => |DDPStage.increment P (stage i)|)
      (P.rawLawFrom P.initial) := by
    have hincrement : Measurable (DDPStage.increment P) := Measurable.of_discrete
    apply Integrable.of_bound
      ((hincrement.comp
        (measurable_pi_apply (X := fun _ : ℕ => DDPStage P) i)).abs.aestronglyMeasurable)
      P.valueDifferenceBound
    exact ae_of_all _ fun stage => by
      rw [Real.norm_eq_abs, abs_abs]
      change |DDPStage.increment P (stage i)| ≤ P.valueDifferenceBound
      simpa only [Real.norm_eq_abs] using (stage i).norm_increment_le P
  have hsquareIntegrable (i : ℕ) : Integrable
      (fun stage : ℕ → DDPStage P => (DDPStage.increment P (stage i)) ^ 2)
      (P.rawLawFrom P.initial) := by
    have hincrement : Measurable (DDPStage.increment P) := Measurable.of_discrete
    apply Integrable.of_bound
      (((hincrement.comp
        (measurable_pi_apply (X := fun _ : ℕ => DDPStage P) i)).pow_const 2)
          |>.aestronglyMeasurable)
      (P.valueDifferenceBound ^ 2)
    exact ae_of_all _ fun stage => by
      rw [norm_pow, Real.norm_eq_abs]
      change |DDPStage.increment P (stage i)| ^ 2 ≤ P.valueDifferenceBound ^ 2
      exact pow_le_pow_left₀ (abs_nonneg _)
        (by simpa only [Real.norm_eq_abs] using (stage i).norm_increment_le P) 2
  calc
    (∫ stage, (P.rawAdvantage stage n) ^ 2 ∂P.rawLawFrom P.initial) =
        ∑ i ∈ Finset.range (n + 1),
          ∫ stage, (DDPStage.increment P (stage i)) ^ 2
            ∂P.rawLawFrom P.initial := P.integral_rawAdvantage_sq_eq_sum n
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ∫ stage, delta * |DDPStage.increment P (stage i)|
          ∂P.rawLawFrom P.initial := by
      apply Finset.sum_le_sum
      intro i _hi
      apply integral_mono_ae (hsquareIntegrable i) ((habsIntegrable i).const_mul delta)
      filter_upwards [P.ae_choose_pos_rawLawFrom P.initial i] with stage hpositive
      have hi := hbalanced (stage i).1 (stage i).2 hpositive
      calc
        (DDPStage.increment P (stage i)) ^ 2 =
            |DDPStage.increment P (stage i)| * |DDPStage.increment P (stage i)| := by
          rw [← sq_abs, pow_two]
        _ ≤ |DDPStage.increment P (stage i)| * delta :=
          mul_le_mul_of_nonneg_left hi (abs_nonneg _)
        _ = delta * |DDPStage.increment P (stage i)| := mul_comm _ _
    _ = delta *
        ∫ stage, P.rawPartialVariation stage n ∂P.rawLawFrom P.initial := by
      simp_rw [integral_const_mul]
      rw [← Finset.mul_sum]
      rw [← integral_finsetSum (Finset.range (n + 1)) fun i _ => habsIntegrable i]
      rfl
    _ ≤ delta * B := mul_le_mul_of_nonneg_left
      (P.integral_rawPartialVariation_le S hB hvariation n) hdelta.le

/-- The event that the raw cumulative advantage crosses `epsilon` by time `n`. -/
private def DiscreteDecisionProcess.rawAbsoluteCrossingUpTo
    (P : DiscreteDecisionProcess) (epsilon : ℝ) (n : ℕ) :
    Set (ℕ → DDPStage P) :=
  {stage | ∃ l, l ≤ n ∧ epsilon ≤ |P.rawAdvantage stage l|}

/-- Doob's inequality bounds each finite-horizon raw crossing event. -/
private theorem DiscreteDecisionProcess.rawAbsoluteCrossingUpTo_le
    (P : DiscreteDecisionProcess) (S : DDPSemantics P) {delta epsilon rho B : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) (hrho : 0 < rho) (hB : 0 < B)
    (hbalanced : IsBalanced P delta)
    (hvariation : ExpectedDDPVariation P S ≤ ENNReal.ofReal B)
    (hsmall : delta ≤ epsilon ^ 2 * rho / B) (n : ℕ) :
    P.rawLawFrom P.initial (P.rawAbsoluteCrossingUpTo epsilon n) ≤ ENNReal.ofReal rho := by
  let threshold : NNReal := ⟨epsilon ^ 2, sq_nonneg epsilon⟩
  let maximumEvent : Set (ℕ → DDPStage P) :=
    {stage | (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => (P.rawAdvantage stage k) ^ 2}
  have hsubset : P.rawAbsoluteCrossingUpTo epsilon n ⊆ maximumEvent := by
    rintro stage ⟨l, hl, hcross⟩
    have hlrange : l ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hl)
    have hsquare : epsilon ^ 2 ≤ (P.rawAdvantage stage l) ^ 2 := by
      calc
        epsilon ^ 2 ≤ |P.rawAdvantage stage l| ^ 2 :=
          pow_le_pow_left₀ hepsilon.le hcross 2
        _ = (P.rawAdvantage stage l) ^ 2 := sq_abs _
    exact hsquare.trans (Finset.le_sup'
      (fun k => (P.rawAdvantage stage k) ^ 2) hlrange)
  have hdoob := maximal_ineq P.rawAdvantage_square_submartingale
    (fun _ _ => sq_nonneg _) (ε := threshold) n
  change (threshold : ℝ≥0∞) * P.rawLawFrom P.initial maximumEvent ≤
    ENNReal.ofReal
      (∫ stage in maximumEvent, (P.rawAdvantage stage n) ^ 2
        ∂P.rawLawFrom P.initial) at hdoob
  have hsetIntegral :
      ∫ stage in maximumEvent, (P.rawAdvantage stage n) ^ 2
          ∂P.rawLawFrom P.initial ≤
        ∫ stage, (P.rawAdvantage stage n) ^ 2 ∂P.rawLawFrom P.initial :=
    setIntegral_le_integral (P.integrable_rawAdvantage_sq n)
      (ae_of_all _ fun stage => sq_nonneg (P.rawAdvantage stage n))
  have hdoobBound : (threshold : ℝ≥0∞) *
      P.rawLawFrom P.initial maximumEvent ≤ ENNReal.ofReal (delta * B) :=
    hdoob.trans <| (ENNReal.ofReal_le_ofReal hsetIntegral).trans <|
      ENNReal.ofReal_le_ofReal (P.integral_rawAdvantage_sq_le S hdelta hB
        hbalanced hvariation n)
  have hreal : delta * B ≤ epsilon ^ 2 * rho := by
    calc
      delta * B ≤ (epsilon ^ 2 * rho / B) * B :=
        mul_le_mul_of_nonneg_right hsmall hB.le
      _ = epsilon ^ 2 * rho := by field_simp
  have hmaximum : P.rawLawFrom P.initial maximumEvent ≤ ENNReal.ofReal rho := by
    have hmul : ENNReal.ofReal (epsilon ^ 2) *
        P.rawLawFrom P.initial maximumEvent ≤
          ENNReal.ofReal (epsilon ^ 2) * ENNReal.ofReal rho := by
      calc
        ENNReal.ofReal (epsilon ^ 2) * P.rawLawFrom P.initial maximumEvent =
            (threshold : ℝ≥0∞) * P.rawLawFrom P.initial maximumEvent := by
          rw [ENNReal.coe_nnreal_eq]
          rfl
        _ ≤ ENNReal.ofReal (delta * B) := hdoobBound
        _ ≤ ENNReal.ofReal (epsilon ^ 2 * rho) := ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (epsilon ^ 2) * ENNReal.ofReal rho :=
          ENNReal.ofReal_mul (sq_nonneg epsilon)
    have hthresholdZero : ENNReal.ofReal (epsilon ^ 2) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hepsilon))
    have hthresholdTop : ENNReal.ofReal (epsilon ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc
      P.rawLawFrom P.initial maximumEvent =
          (ENNReal.ofReal (epsilon ^ 2))⁻¹ *
            (ENNReal.ofReal (epsilon ^ 2) * P.rawLawFrom P.initial maximumEvent) :=
        (ENNReal.inv_mul_cancel_left hthresholdZero hthresholdTop).symm
      _ ≤ (ENNReal.ofReal (epsilon ^ 2))⁻¹ *
          (ENNReal.ofReal (epsilon ^ 2) * ENNReal.ofReal rho) :=
        mul_le_mul_right hmul _
      _ = ENNReal.ofReal rho :=
        ENNReal.inv_mul_cancel_left hthresholdZero hthresholdTop
  exact (measure_mono hsubset).trans hmaximum

/-- The same bound holds for ever crossing on the infinite raw trajectory. -/
private theorem DiscreteDecisionProcess.rawAbsoluteCrossing_le
    (P : DiscreteDecisionProcess) (S : DDPSemantics P) {delta epsilon rho B : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) (hrho : 0 < rho) (hB : 0 < B)
    (hbalanced : IsBalanced P delta)
    (hvariation : ExpectedDDPVariation P S ≤ ENNReal.ofReal B)
    (hsmall : delta ≤ epsilon ^ 2 * rho / B) :
    P.rawLawFrom P.initial {stage | ∃ l, epsilon ≤ |P.rawAdvantage stage l|} ≤
      ENNReal.ofReal rho := by
  have hmonotone : Monotone (P.rawAbsoluteCrossingUpTo epsilon) := by
    intro n m hnm stage
    rintro ⟨l, hl, hcross⟩
    exact ⟨l, hl.trans hnm, hcross⟩
  have hunion : (⋃ n, P.rawAbsoluteCrossingUpTo epsilon n) =
      {stage | ∃ l, epsilon ≤ |P.rawAdvantage stage l|} := by
    ext stage
    simp only [mem_iUnion, DiscreteDecisionProcess.rawAbsoluteCrossingUpTo,
      mem_setOf_eq]
    constructor
    · rintro ⟨n, l, _hl, hcross⟩
      exact ⟨l, hcross⟩
    · rintro ⟨l, hcross⟩
      exact ⟨l, l, le_rfl, hcross⟩
  rw [← hunion]
  apply le_of_tendsto' (tendsto_measure_iUnion_atTop hmonotone)
  intro n
  exact P.rawAbsoluteCrossingUpTo_le S hdelta hepsilon hrho hB hbalanced
    hvariation hsmall n

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
  rw [AbsoluteCrossingProbability, S.law_eq_rawLaw]
  rw [Measure.map_apply (DDPPath.measurable_ofRaw P)
    (measurableSet_ddpAbsoluteAdvantage_crossing P ε)]
  simpa only [Set.preimage_setOf_eq, P.advantage_ofRaw] using
    P.rawAbsoluteCrossing_le S hδ hε hρ hB hbalanced hvariation hsmall

/-! ### 3.3. Rank -/

/-- The event that, after the initial state, the first return to `A` is at `z`. -/
def FirstReturnAt (P : DiscreteDecisionProcess) (A : Set P.X) (z : P.X) :
    Set (DDPPath P) :=
  {p | ∃ k, 0 < k ∧ p.x k = z ∧ z ∈ A ∧ ∀ i, 0 < i → i < k → p.x i ∉ A}

/-- First return to `A` at `z` at the specified positive time. -/
private def FirstReturnAtTime (P : DiscreteDecisionProcess) (A : Set P.X)
    (z : P.X) (k : ℕ) : Set (DDPPath P) :=
  {p | 0 < k ∧ p.x k = z ∧ z ∈ A ∧ ∀ i, 0 < i → i < k → p.x i ∉ A}

/-- The event that the process returns to `A` after its initial state. -/
def ReturnsTo (P : DiscreteDecisionProcess) (A : Set P.X) : Set (DDPPath P) :=
  ⋃ z ∈ A, FirstReturnAt P A z

/-- Returning to `A` is equivalent to visiting it at some positive time. -/
private theorem mem_returnsTo_iff (P : DiscreteDecisionProcess) (A : Set P.X)
    (p : DDPPath P) : p ∈ ReturnsTo P A ↔ ∃ k, 0 < k ∧ p.x k ∈ A := by
  classical
  constructor
  · rw [ReturnsTo]
    simp only [mem_iUnion]
    rintro ⟨z, _hz, k, hk, hx, hz, _hbefore⟩
    exact ⟨k, hk, hx.symm ▸ hz⟩
  · intro hexists
    let k := Nat.find hexists
    have hk := Nat.find_spec hexists
    rw [ReturnsTo]
    refine mem_iUnion.2 ⟨p.x k, mem_iUnion.2 ⟨hk.2, ?_⟩⟩
    refine ⟨k, hk.1, rfl, hk.2, ?_⟩
    intro i hi hik hiA
    exact (not_lt_of_ge (Nat.find_min' hexists ⟨hi, hiA⟩)) hik

/-- State-coordinate projections are measurable in the cylinder sigma algebra. -/
private theorem DDPPath.measurable_x (P : DiscreteDecisionProcess) (i : ℕ) :
    Measurable (fun p : DDPPath P => p.x i) := by
  have hevaluation : Measurable
      (fun h : DDPFinitePath P i => h.x (Fin.last i)) := Measurable.of_discrete
  convert hevaluation.comp (DDPPath.measurable_prefix P i) using 1
  funext p
  rfl

/-- First-return events are measurable. -/
private theorem measurableSet_firstReturnAt (P : DiscreteDecisionProcess)
    (A : Set P.X) (z : P.X) : MeasurableSet (FirstReturnAt P A z) := by
  by_cases hz : z ∈ A
  · have heq : FirstReturnAt P A z = ⋃ k, if 0 < k then
        {p | p.x k = z} ∩ ⋂ i, if 0 < i ∧ i < k then {p | p.x i ∉ A} else Set.univ
      else ∅ := by
      ext p
      simp only [FirstReturnAt, mem_setOf_eq, mem_iUnion, mem_ite_empty_right,
        mem_inter_iff, mem_iInter]
      constructor
      · rintro ⟨k, hk, hx, _hz, hbefore⟩
        refine ⟨k, hk, hx, ?_⟩
        intro i
        by_cases hi : 0 < i ∧ i < k
        · simpa [hi] using hbefore i hi.1 hi.2
        · simp [hi]
      · rintro ⟨k, hk, hx, hbefore⟩
        refine ⟨k, hk, hx, hz, ?_⟩
        intro i hi hik
        simpa [hi, hik] using hbefore i
    rw [heq]
    apply MeasurableSet.iUnion
    intro k
    split_ifs
    · apply MeasurableSet.inter
      · exact (DDPPath.measurable_x P k) (measurableSet_singleton z)
      · apply MeasurableSet.iInter
        intro i
        split_ifs
        · exact (DDPPath.measurable_x P i)
            (show MeasurableSet Aᶜ from MeasurableSet.of_discrete)
        · exact MeasurableSet.univ
    · exact MeasurableSet.empty
  · have heq : FirstReturnAt P A z = ∅ := by
      ext p
      simp [FirstReturnAt, hz]
    rw [heq]
    exact MeasurableSet.empty

/-- A fixed-time first-return event is measurable. -/
private theorem measurableSet_firstReturnAtTime (P : DiscreteDecisionProcess)
    (A : Set P.X) (z : P.X) (k : ℕ) : MeasurableSet (FirstReturnAtTime P A z k) := by
  by_cases hk : 0 < k
  · by_cases hz : z ∈ A
    · have heq : FirstReturnAtTime P A z k =
          {p | p.x k = z} ∩ ⋂ i, if 0 < i ∧ i < k then {p | p.x i ∉ A} else Set.univ := by
        ext p
        simp only [FirstReturnAtTime, mem_setOf_eq, mem_inter_iff, mem_iInter]
        constructor
        · rintro ⟨_hk, hx, _hz, hbefore⟩
          refine ⟨hx, ?_⟩
          intro i
          by_cases hi : 0 < i ∧ i < k
          · simpa [hi] using hbefore i hi.1 hi.2
          · simp [hi]
        · rintro ⟨hx, hbefore⟩
          refine ⟨hk, hx, hz, ?_⟩
          intro i hi hik
          simpa [hi, hik] using hbefore i
      rw [heq]
      apply MeasurableSet.inter
      · exact (DDPPath.measurable_x P k) (measurableSet_singleton z)
      · apply MeasurableSet.iInter
        intro i
        split_ifs
        · exact (DDPPath.measurable_x P i)
            (show MeasurableSet Aᶜ from MeasurableSet.of_discrete)
        · exact MeasurableSet.univ
    · have heq : FirstReturnAtTime P A z k = ∅ := by
        ext p
        simp [FirstReturnAtTime, hz]
      rw [heq]
      exact MeasurableSet.empty
  · have heq : FirstReturnAtTime P A z k = ∅ := by
      ext p
      simp [FirstReturnAtTime, hk]
    rw [heq]
    exact MeasurableSet.empty

/-- First return at `z` is the disjoint union over its possible times. -/
private theorem firstReturnAt_eq_iUnion_time (P : DiscreteDecisionProcess)
    (A : Set P.X) (z : P.X) :
    FirstReturnAt P A z = ⋃ k, FirstReturnAtTime P A z k := by
  ext p
  simp only [FirstReturnAt, FirstReturnAtTime, mem_setOf_eq, mem_iUnion]

/-- Return to `A` at `z` strictly before the displayed horizon. -/
private def FirstReturnBefore (P : DiscreteDecisionProcess) (A : Set P.X)
    (z : P.X) (N : ℕ) : Set (DDPPath P) :=
  ⋃ k : {k : ℕ // k + 1 < N}, FirstReturnAtTime P A z (k.1 + 1)

/-- Return to `A` strictly before the displayed horizon. -/
private def ReturnsBefore (P : DiscreteDecisionProcess) (A : Set P.X)
    (N : ℕ) : Set (DDPPath P) :=
  ⋃ z, FirstReturnBefore P A z N

/-- Fixed-state return before a horizon is measurable. -/
private theorem measurableSet_firstReturnBefore (P : DiscreteDecisionProcess)
    (A : Set P.X) (z : P.X) (N : ℕ) : MeasurableSet (FirstReturnBefore P A z N) := by
  exact MeasurableSet.iUnion fun k =>
    measurableSet_firstReturnAtTime P A z (k.1 + 1)

/-- Return before a horizon is measurable. -/
private theorem measurableSet_returnsBefore (P : DiscreteDecisionProcess)
    (A : Set P.X) (N : ℕ) : MeasurableSet (ReturnsBefore P A N) := by
  exact MeasurableSet.iUnion fun z => measurableSet_firstReturnBefore P A z N

/-- A first return at a fixed state has only one time. -/
private theorem pairwise_disjoint_firstReturnAtTime (P : DiscreteDecisionProcess)
    (A : Set P.X) (z : P.X) :
    Pairwise (Function.onFun Disjoint (FirstReturnAtTime P A z)) := by
  intro k l hkl
  rw [Function.onFun, Set.disjoint_left]
  intro p hpk hpl
  rcases hpk with ⟨hk, hxk, hzk, hbeforeK⟩
  rcases hpl with ⟨hl, hxl, hzl, hbeforeL⟩
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · exact (hbeforeL k hk hlt) (hxk.symm ▸ hzk)
  · exact (hbeforeK l hl hgt) (hxl.symm ▸ hzl)

/-- Distinct first-return states remain disjoint after truncating the return time. -/
private theorem pairwise_disjoint_firstReturnBefore (P : DiscreteDecisionProcess)
    (A : Set P.X) (N : ℕ) :
    Pairwise (Function.onFun Disjoint fun z => FirstReturnBefore P A z N) := by
  intro z w hzw
  rw [Function.onFun, Set.disjoint_left]
  intro p hpz hpw
  rw [FirstReturnBefore] at hpz hpw
  simp only [mem_iUnion] at hpz hpw
  rcases hpz with ⟨k, hpk⟩
  rcases hpw with ⟨l, hpl⟩
  rcases hpk with ⟨_hk, hxk, hzk, hbeforeK⟩
  rcases hpl with ⟨_hl, hxl, hwl, hbeforeL⟩
  have htime : k.1 + 1 = l.1 + 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hbeforeL (k.1 + 1) (Nat.succ_pos k.1) hlt) (hxk.symm ▸ hzk)
    · exact (hbeforeK (l.1 + 1) (Nat.succ_pos l.1) hgt) (hxl.symm ▸ hwl)
  apply hzw
  rw [← hxk, htime, hxl]

/-- At a fixed first-return time, the sampled terminal action averages to the return-state value. -/
private theorem DiscreteDecisionProcess.integral_rawStageValue_firstReturnAtTime
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (x : P.X) (y : P.Y x) (A : Set P.X) (z : P.X) (k : ℕ) :
    (∫ stage in DDPPath.ofRaw P ⁻¹' FirstReturnAtTime P A z (k + 1),
        P.rawStageValue (k + 1) stage ∂P.rawLawAfterAction x y) =
      (S.afterAction x y (FirstReturnAtTime P A z (k + 1))).toReal * P.valueX z := by
  classical
  let H := {h : DDPFinitePath P (k + 1) //
    h.x (Fin.last (k + 1)) = z ∧ z ∈ A ∧
      ∀ i : Fin (k + 2), 0 < i.1 → i.1 < k + 1 → h.x i ∉ A}
  let C : H → Set (ℕ → DDPStage P) := fun h =>
    DDPPath.ofRaw P ⁻¹' DDPCylinder P h.1
  have hevent : DDPPath.ofRaw P ⁻¹' FirstReturnAtTime P A z (k + 1) = ⋃ h, C h := by
    ext stage
    simp only [mem_preimage, FirstReturnAtTime, mem_setOf_eq, mem_iUnion, C]
    constructor
    · rintro ⟨_hk, hlast, hz, hbefore⟩
      let h := (DDPPath.ofRaw P stage).prefix P (k + 1)
      have hgood : h.x (Fin.last (k + 1)) = z ∧ z ∈ A ∧
          ∀ i : Fin (k + 2), 0 < i.1 → i.1 < k + 1 → h.x i ∉ A := by
        refine ⟨?_, hz, ?_⟩
        · simpa [h, DDPPath.prefix] using hlast
        · intro i hi hik
          simpa [h, DDPPath.prefix] using hbefore i.1 hi hik
      exact ⟨⟨h, hgood⟩, rfl⟩
    · rintro ⟨h, hpref⟩
      change (DDPPath.ofRaw P stage).prefix P (k + 1) = h.1 at hpref
      refine ⟨Nat.succ_pos k, ?_, h.2.2.1, ?_⟩
      · have hlast := congrArg
          (fun q : DDPFinitePath P (k + 1) => q.x (Fin.last (k + 1))) hpref
        exact hlast.trans h.2.1
      · intro i hi hik
        let j : Fin (k + 2) := ⟨i, by omega⟩
        have hstate := congrArg (fun q : DDPFinitePath P (k + 1) => q.x j) hpref
        change (DDPPath.ofRaw P stage).x i = h.1.x j at hstate
        rw [hstate]
        exact h.2.2.2 j hi hik
  have hmeasurable (h : H) : MeasurableSet (C h) :=
    (DDPPath.measurable_ofRaw P) (measurableSet_ddpCylinder P h.1)
  have hpairwise : Pairwise (Function.onFun Disjoint C) := by
    intro first second hne
    rw [Function.onFun, Set.disjoint_left]
    intro stage hfirst hsecond
    apply hne
    apply Subtype.ext
    change DDPPath.ofRaw P stage ∈ DDPCylinder P first.1 at hfirst
    change DDPPath.ofRaw P stage ∈ DDPCylinder P second.1 at hsecond
    exact hfirst.symm.trans hsecond
  have hintegrable : Integrable (P.rawStageValue (k + 1))
      (P.rawLawAfterAction x y) := by
    exact P.integrable_rawStageValue (PMF.pure (⟨x, y⟩ : DDPStage P)) (k + 1)
  rw [hevent, integral_iUnion hmeasurable hpairwise hintegrable.integrableOn]
  have hcell (h : H) :
      (∫ stage in C h, P.rawStageValue (k + 1) stage
          ∂P.rawLawAfterAction x y) =
        (P.rawLawAfterAction x y (C h)).toReal * P.valueX z := by
    by_cases hstart : h.1.x 0 = x
    · by_cases haction : HEq (h.1.y 0) y
      · rw [P.integral_rawStageValue_ddpCylinder x y h.1 hstart haction]
        rw [P.rawLawAfterAction_ddpCylinder x y h.1 hstart haction]
        rw [h.2.1]
      · rw [P.integral_rawStageValue_ddpCylinder_eq_zero_of_wrong S x y h.1
          (Or.inr haction)]
        rw [P.rawLawAfterAction_ddpCylinder_eq_zero_of_wrong S x y h.1
          (Or.inr haction)]
        simp
    · rw [P.integral_rawStageValue_ddpCylinder_eq_zero_of_wrong S x y h.1
        (Or.inl hstart)]
      rw [P.rawLawAfterAction_ddpCylinder_eq_zero_of_wrong S x y h.1
        (Or.inl hstart)]
      simp
  simp_rw [hcell]
  rw [tsum_mul_right]
  congr 1
  have hcanonical := congrArg
    (fun mu : Measure (DDPPath P) => mu (FirstReturnAtTime P A z (k + 1)))
    (S.afterAction_eq_rawLaw P x y)
  rw [Measure.map_apply (DDPPath.measurable_ofRaw P)
    (measurableSet_firstReturnAtTime P A z (k + 1))] at hcanonical
  rw [hcanonical, hevent, measure_iUnion hpairwise hmeasurable]
  exact (ENNReal.tsum_toReal_eq fun h =>
    measure_ne_top (P.rawLawAfterAction x y) (C h)).symm

/-- Before the horizon, bounded hitting stops exactly at the displayed first-return time. -/
private theorem DiscreteDecisionProcess.stoppedValue_eq_on_firstReturnAtTime
    (P : DiscreteDecisionProcess) (A : Set P.X) (N : ℕ)
    (z : P.X) (k : {k : ℕ // k + 1 < N}) (stage : ℕ → DDPStage P)
    (hstage : stage ∈ DDPPath.ofRaw P ⁻¹' FirstReturnAtTime P A z (k.1 + 1)) :
    stoppedValue P.rawStageValue
        (fun path => ((hittingBtwn
          (fun (n : ℕ) (path : ℕ → DDPStage P) => (path n).1) A 1 N path : ℕ) : ℕ∞))
        stage = P.rawStageValue (k.1 + 1) stage := by
  let rawState : ℕ → (ℕ → DDPStage P) → P.X := fun n path => (path n).1
  let tau := hittingBtwn rawState A (1 : ℕ) N stage
  change DDPPath.ofRaw P stage ∈ FirstReturnAtTime P A z (k.1 + 1) at hstage
  rcases hstage with ⟨_hpositive, hstate, hmem, hbefore⟩
  have hhit : rawState (k.1 + 1) stage ∈ A := by
    change rawState (k.1 + 1) stage = z at hstate
    rw [hstate]
    exact hmem
  have hexists : ∃ j ∈ Set.Icc (1 : ℕ) N, rawState j stage ∈ A :=
    ⟨k.1 + 1, ⟨Nat.succ_le_succ (Nat.zero_le k.1), k.2.le⟩, hhit⟩
  have htau_le : tau ≤ k.1 + 1 :=
    hittingBtwn_le_of_mem (Nat.succ_le_succ (Nat.zero_le k.1)) k.2.le hhit
  have htau_ge : k.1 + 1 ≤ tau := by
    by_contra hnot
    have htau_lt : tau < k.1 + 1 := Nat.lt_of_not_ge hnot
    have htau_mem : rawState tau stage ∈ A := hittingBtwn_mem_set hexists
    have htau_pos : 0 < tau := lt_of_lt_of_le Nat.zero_lt_one
      (le_hittingBtwn (by omega) stage)
    exact (hbefore tau htau_pos htau_lt) htau_mem
  have htau : tau = k.1 + 1 := le_antisymm htau_le htau_ge
  simp only [stoppedValue]
  change P.rawStageValue tau stage = P.rawStageValue (k.1 + 1) stage
  rw [htau]

/-- With no return strictly before the horizon, bounded hitting stops at the horizon. -/
private theorem DiscreteDecisionProcess.stoppedValue_eq_on_not_returnsBefore
    (P : DiscreteDecisionProcess) (A : Set P.X) (N : ℕ) (hN : 1 ≤ N)
    (stage : ℕ → DDPStage P)
    (hstage : stage ∈ (DDPPath.ofRaw P ⁻¹' ReturnsBefore P A N)ᶜ) :
    stoppedValue P.rawStageValue
        (fun path => ((hittingBtwn
          (fun (n : ℕ) (path : ℕ → DDPStage P) => (path n).1) A 1 N path : ℕ) : ℕ∞))
        stage = P.rawStageValue N stage := by
  let rawState : ℕ → (ℕ → DDPStage P) → P.X := fun n path => (path n).1
  let tau := hittingBtwn rawState A (1 : ℕ) N stage
  have htau : tau = N := by
    apply le_antisymm (hittingBtwn_le stage)
    by_contra hnot
    have htau_lt : tau < N := Nat.lt_of_not_ge hnot
    have htau_mem : rawState tau stage ∈ A :=
      hittingBtwn_mem_set_of_hittingBtwn_lt htau_lt
    have htau_pos : 0 < tau := lt_of_lt_of_le Nat.zero_lt_one
      (le_hittingBtwn hN stage)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htau_pos)
    apply hstage
    change DDPPath.ofRaw P stage ∈ ReturnsBefore P A N
    rw [ReturnsBefore]
    apply mem_iUnion.2
    refine ⟨rawState tau stage, ?_⟩
    rw [FirstReturnBefore]
    apply mem_iUnion.2
    let index : {k : ℕ // k + 1 < N} := ⟨k, by omega⟩
    refine ⟨index, ?_⟩
    change DDPPath.ofRaw P stage ∈
      FirstReturnAtTime P A (rawState tau stage) (k + 1)
    refine ⟨Nat.succ_pos k, ?_, htau_mem, ?_⟩
    · change rawState (k + 1) stage = rawState tau stage
      rw [hk]
    · intro i hi hik
      have hitau : i < tau := by omega
      exact notMem_of_lt_hittingBtwn (u := rawState) (s := A) (n := 1) (m := N)
        (k := i) (ω := stage) hitau (Nat.succ_le_iff.2 hi)
  simp only [stoppedValue]
  change P.rawStageValue tau stage = P.rawStageValue N stage
  rw [htau]

/-- Bounded optional stopping splits into first returns before the horizon and the residual path. -/
private theorem DiscreteDecisionProcess.boundedFirstReturn_decomposition
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (x : P.X) (y : P.Y x) (A : Set P.X) (N : ℕ) (hN : 1 ≤ N) :
    P.valueY x y =
      (∑' z, (S.afterAction x y (FirstReturnBefore P A z N)).toReal * P.valueX z) +
        ∫ stage in (DDPPath.ofRaw P ⁻¹' ReturnsBefore P A N)ᶜ,
          P.rawStageValue N stage ∂P.rawLawAfterAction x y := by
  classical
  let rawState : ℕ → (ℕ → DDPStage P) → P.X := fun n stage => (stage n).1
  let tau : (ℕ → DDPStage P) → ℕ∞ := fun stage =>
    ((hittingBtwn rawState A (1 : ℕ) N stage : ℕ) : ℕ∞)
  let F := stoppedValue P.rawStageValue tau
  let E := DDPPath.ofRaw P ⁻¹' ReturnsBefore P A N
  have hmeasurableE : MeasurableSet E :=
    (DDPPath.measurable_ofRaw P) (measurableSet_returnsBefore P A N)
  have htauStopping : IsStoppingTime
      (Filtration.piLE (X := fun _ : ℕ => DDPStage P)) tau := by
    exact P.rawState_adapted.isStoppingTime_hittingBtwn MeasurableSet.of_discrete
  have htauBound (stage : ℕ → DDPStage P) : tau stage ≤ (N : ℕ∞) := by
    change ((hittingBtwn rawState A (1 : ℕ) N stage : ℕ) : ℕ∞) ≤ (N : ℕ∞)
    exact_mod_cast (hittingBtwn_le (u := rawState) (s := A) (n := 1) (m := N) stage)
  have hFIntegrable : Integrable F (P.rawLawAfterAction x y) := by
    exact (P.rawStageValue_martingale
      (PMF.pure (⟨x, y⟩ : DDPStage P))).submartingale.integrable_stoppedValue
        htauStopping htauBound
  have hstateSets : E =
      ⋃ z, DDPPath.ofRaw P ⁻¹' FirstReturnBefore P A z N := by
    ext stage
    simp only [E, ReturnsBefore, mem_preimage, mem_iUnion]
  have hstateMeasurable (z : P.X) :
      MeasurableSet (DDPPath.ofRaw P ⁻¹' FirstReturnBefore P A z N) :=
    (DDPPath.measurable_ofRaw P) (measurableSet_firstReturnBefore P A z N)
  have hstatePairwise : Pairwise (Function.onFun Disjoint fun z =>
      DDPPath.ofRaw P ⁻¹' FirstReturnBefore P A z N) := by
    intro z w hzw
    exact (pairwise_disjoint_firstReturnBefore P A N hzw).preimage (DDPPath.ofRaw P)
  have htimePairwise (z : P.X) : Pairwise (Function.onFun Disjoint fun
      k : {k : ℕ // k + 1 < N} =>
        DDPPath.ofRaw P ⁻¹' FirstReturnAtTime P A z (k.1 + 1)) := by
    intro first second hne
    apply Disjoint.preimage (DDPPath.ofRaw P)
    apply pairwise_disjoint_firstReturnAtTime P A z
    intro heq
    apply hne
    apply Subtype.ext
    omega
  have htimeMeasurable (z : P.X) (k : {k : ℕ // k + 1 < N}) :
      MeasurableSet (DDPPath.ofRaw P ⁻¹' FirstReturnAtTime P A z (k.1 + 1)) :=
    (DDPPath.measurable_ofRaw P)
      (measurableSet_firstReturnAtTime P A z (k.1 + 1))
  have hhitIntegral :
      (∫ stage in E, F stage ∂P.rawLawAfterAction x y) =
        ∑' z, (S.afterAction x y (FirstReturnBefore P A z N)).toReal * P.valueX z := by
    rw [hstateSets, integral_iUnion hstateMeasurable hstatePairwise
      hFIntegrable.integrableOn]
    apply tsum_congr
    intro z
    have htimeSets : DDPPath.ofRaw P ⁻¹' FirstReturnBefore P A z N =
        ⋃ k : {k : ℕ // k + 1 < N},
          DDPPath.ofRaw P ⁻¹' FirstReturnAtTime P A z (k.1 + 1) := by
      ext stage
      simp only [FirstReturnBefore, mem_preimage, mem_iUnion]
    rw [htimeSets, integral_iUnion (htimeMeasurable z) (htimePairwise z)
      hFIntegrable.integrableOn]
    have hcell (k : {k : ℕ // k + 1 < N}) :
        (∫ stage in DDPPath.ofRaw P ⁻¹' FirstReturnAtTime P A z (k.1 + 1),
            F stage ∂P.rawLawAfterAction x y) =
          (S.afterAction x y (FirstReturnAtTime P A z (k.1 + 1))).toReal *
            P.valueX z := by
      calc
        (∫ stage in DDPPath.ofRaw P ⁻¹' FirstReturnAtTime P A z (k.1 + 1),
            F stage ∂P.rawLawAfterAction x y) =
            ∫ stage in DDPPath.ofRaw P ⁻¹' FirstReturnAtTime P A z (k.1 + 1),
              P.rawStageValue (k.1 + 1) stage ∂P.rawLawAfterAction x y := by
                apply integral_congr_ae
                filter_upwards [ae_restrict_mem (htimeMeasurable z k)] with stage hstage
                exact P.stoppedValue_eq_on_firstReturnAtTime A N z k stage hstage
        _ = _ := P.integral_rawStageValue_firstReturnAtTime S x y A z k.1
    simp_rw [hcell]
    rw [tsum_mul_right]
    congr 1
    rw [FirstReturnBefore, measure_iUnion]
    · exact (ENNReal.tsum_toReal_eq fun k => by
          letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
          exact measure_ne_top _ _).symm
    · intro first second hne
      apply pairwise_disjoint_firstReturnAtTime P A z
      intro heq
      apply hne
      apply Subtype.ext
      omega
    · intro k
      exact measurableSet_firstReturnAtTime P A z (k.1 + 1)
  have hresidualIntegral :
      (∫ stage in Eᶜ, F stage ∂P.rawLawAfterAction x y) =
        ∫ stage in Eᶜ, P.rawStageValue N stage ∂P.rawLawAfterAction x y := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hmeasurableE.compl] with stage hstage
    exact P.stoppedValue_eq_on_not_returnsBefore A N hN stage hstage
  calc
    P.valueY x y = ∫ stage, F stage ∂P.rawLawAfterAction x y := by
      exact (P.integral_stoppedValue_hittingBtwn_eq x y A N).symm
    _ = (∫ stage in E, F stage ∂P.rawLawAfterAction x y) +
        ∫ stage in Eᶜ, F stage ∂P.rawLawAfterAction x y :=
      (integral_add_compl hmeasurableE hFIntegrable).symm
    _ = _ := by rw [hhitIntegral, hresidualIntegral]

/-- Centering the residual path at any state costs at most its mass times the value bound. -/
private theorem DiscreteDecisionProcess.boundedFirstReturn_centered_bound_of_uniform
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (x : P.X) (y : P.Y x) (A : Set P.X) (N : ℕ) (hN : 1 ≤ N)
    (r : ℝ) (hr : ∀ z (w : P.Y z), |P.valueY z w - r| ≤ P.valueDifferenceBound) :
    |P.valueY x y -
        (∑' z, (S.afterAction x y (FirstReturnBefore P A z N)).toReal * P.valueX z) -
        (P.rawLawAfterAction x y
          (DDPPath.ofRaw P ⁻¹' ReturnsBefore P A N)ᶜ).toReal * r| ≤
      P.valueDifferenceBound *
        (P.rawLawAfterAction x y
          (DDPPath.ofRaw P ⁻¹' ReturnsBefore P A N)ᶜ).toReal := by
  let E := (DDPPath.ofRaw P ⁻¹' ReturnsBefore P A N)ᶜ
  let mu := P.rawLawAfterAction x y
  have hrawIntegrable : Integrable (P.rawStageValue N) mu := by
    exact P.integrable_rawStageValue (PMF.pure (⟨x, y⟩ : DDPStage P)) N
  have hconstIntegrable : Integrable (fun _stage : ℕ → DDPStage P => r)
      (mu.restrict E) := integrable_const _
  have hcenter :
      (∫ stage in E, P.rawStageValue N stage - r ∂mu) =
        (∫ stage in E, P.rawStageValue N stage ∂mu) -
          (mu E).toReal * r := by
    rw [integral_sub hrawIntegrable.integrableOn hconstIntegrable]
    rw [setIntegral_const, Measure.real_def]
    rfl
  have hbound (stage : ℕ → DDPStage P) :
      ‖P.rawStageValue N stage - r‖ ≤ P.valueDifferenceBound := by
    simpa only [DiscreteDecisionProcess.rawStageValue, Real.norm_eq_abs] using
      hr (stage N).1 (stage N).2
  have hcenterBound :
      ‖∫ stage in E, P.rawStageValue N stage - r ∂mu‖ ≤
        P.valueDifferenceBound * (mu E).toReal := by
    exact norm_setIntegral_le_of_norm_le_const (measure_lt_top mu E)
      (fun stage _hstage => hbound stage)
  rw [hcenter] at hcenterBound
  have hdecomposition := P.boundedFirstReturn_decomposition S x y A N hN
  change P.valueY x y =
      (∑' z, (S.afterAction x y (FirstReturnBefore P A z N)).toReal * P.valueX z) +
        ∫ stage in E, P.rawStageValue N stage ∂mu at hdecomposition
  rw [hdecomposition]
  simpa only [add_sub_cancel_left, Real.norm_eq_abs] using hcenterBound

/-- Centering at a state value satisfies the uniform residual hypothesis automatically. -/
private theorem DiscreteDecisionProcess.boundedFirstReturn_centered_bound
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (x c : P.X) (y : P.Y x) (A : Set P.X) (N : ℕ) (hN : 1 ≤ N) :
    |P.valueY x y -
        (∑' z, (S.afterAction x y (FirstReturnBefore P A z N)).toReal * P.valueX z) -
        (P.rawLawAfterAction x y
          (DDPPath.ofRaw P ⁻¹' ReturnsBefore P A N)ᶜ).toReal * P.valueX c| ≤
      P.valueDifferenceBound *
        (P.rawLawAfterAction x y
          (DDPPath.ofRaw P ⁻¹' ReturnsBefore P A N)ᶜ).toReal := by
  apply P.boundedFirstReturn_centered_bound_of_uniform S x y A N hN (P.valueX c)
  intro z w
  simpa only using
    (P.valueDifference z c w (Classical.choose (P.choose c).support_nonempty)).2.1

/-- The raw residual mass is one minus the semantic return-before-horizon probability. -/
private theorem DiscreteDecisionProcess.rawNotReturnsBefore_toReal
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (x : P.X) (y : P.Y x) (A : Set P.X) (N : ℕ) :
    (P.rawLawAfterAction x y
      (DDPPath.ofRaw P ⁻¹' ReturnsBefore P A N)ᶜ).toReal =
        1 - (S.afterAction x y (ReturnsBefore P A N)).toReal := by
  have hmeasurable : MeasurableSet (DDPPath.ofRaw P ⁻¹' ReturnsBefore P A N) :=
    (DDPPath.measurable_ofRaw P) (measurableSet_returnsBefore P A N)
  have hcanonical := congrArg
    (fun mu : Measure (DDPPath P) => mu (ReturnsBefore P A N))
    (S.afterAction_eq_rawLaw P x y)
  rw [Measure.map_apply (DDPPath.measurable_ofRaw P)
    (measurableSet_returnsBefore P A N)] at hcanonical
  rw [measure_compl hmeasurable (measure_ne_top _ _)]
  rw [ENNReal.toReal_sub_of_le]
  · rw [show (P.rawLawAfterAction x y Set.univ).toReal = 1 by
      letI : IsProbabilityMeasure (P.rawLawAfterAction x y) :=
        P.isProbabilityMeasure_rawLawAfterAction x y
      simp]
    rw [← hcanonical]
  · exact measure_mono (subset_univ _)
  · letI : IsProbabilityMeasure (P.rawLawAfterAction x y) :=
      P.isProbabilityMeasure_rawLawAfterAction x y
    simp

/-- The finite centered bound for any uniformly close reference value. -/
private theorem DiscreteDecisionProcess.boundedFirstReturn_centered_bound_semantic_of_uniform
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (x : P.X) (y : P.Y x) (A : Set P.X) (N : ℕ) (hN : 1 ≤ N)
    (r : ℝ) (hr : ∀ z (w : P.Y z), |P.valueY z w - r| ≤ P.valueDifferenceBound) :
    |P.valueY x y -
        (∑' z, (S.afterAction x y (FirstReturnBefore P A z N)).toReal * P.valueX z) -
        (1 - (S.afterAction x y (ReturnsBefore P A N)).toReal) * r| ≤
      P.valueDifferenceBound *
        (1 - (S.afterAction x y (ReturnsBefore P A N)).toReal) := by
  simpa only [P.rawNotReturnsBefore_toReal S x y A N] using
    P.boundedFirstReturn_centered_bound_of_uniform S x y A N hN r hr

/-- The centered finite-return bound written entirely with semantic probabilities. -/
private theorem DiscreteDecisionProcess.boundedFirstReturn_centered_bound_semantic
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (x c : P.X) (y : P.Y x) (A : Set P.X) (N : ℕ) (hN : 1 ≤ N) :
    |P.valueY x y -
        (∑' z, (S.afterAction x y (FirstReturnBefore P A z N)).toReal * P.valueX z) -
        (1 - (S.afterAction x y (ReturnsBefore P A N)).toReal) * P.valueX c| ≤
      P.valueDifferenceBound *
        (1 - (S.afterAction x y (ReturnsBefore P A N)).toReal) := by
  simpa only [P.rawNotReturnsBefore_toReal S x y A N] using
    P.boundedFirstReturn_centered_bound S x c y A N hN

/-- Enlarging the horizon enlarges each truncated first-return event. -/
private theorem firstReturnBefore_mono (P : DiscreteDecisionProcess)
    (A : Set P.X) (z : P.X) : Monotone (FirstReturnBefore P A z) := by
  intro N M hNM p hp
  rw [FirstReturnBefore] at hp ⊢
  rcases mem_iUnion.1 hp with ⟨k, hpk⟩
  apply mem_iUnion.2
  exact ⟨⟨k.1, k.2.trans_le hNM⟩, hpk⟩

/-- Truncated first returns exhaust the full first-return event. -/
private theorem iUnion_firstReturnBefore (P : DiscreteDecisionProcess)
    (A : Set P.X) (z : P.X) :
    ⋃ N, FirstReturnBefore P A z N = FirstReturnAt P A z := by
  ext p
  simp only [mem_iUnion]
  constructor
  · rintro ⟨N, hp⟩
    rw [FirstReturnBefore] at hp
    rcases mem_iUnion.1 hp with ⟨k, hpk⟩
    rw [firstReturnAt_eq_iUnion_time]
    exact mem_iUnion.2 ⟨k.1 + 1, hpk⟩
  · intro hp
    rw [firstReturnAt_eq_iUnion_time] at hp
    rcases mem_iUnion.1 hp with ⟨j, hpj⟩
    rcases hpj with ⟨hj, hx, hz, hbefore⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    refine ⟨k + 2, ?_⟩
    rw [FirstReturnBefore]
    apply mem_iUnion.2
    exact ⟨⟨k, by omega⟩, Nat.succ_pos k, hx, hz, hbefore⟩

/-- Enlarging the horizon enlarges the truncated return event. -/
private theorem returnsBefore_mono (P : DiscreteDecisionProcess)
    (A : Set P.X) : Monotone (ReturnsBefore P A) := by
  intro N M hNM p hp
  rw [ReturnsBefore] at hp ⊢
  rcases mem_iUnion.1 hp with ⟨z, hpz⟩
  exact mem_iUnion.2 ⟨z, firstReturnBefore_mono P A z hNM hpz⟩

/-- Truncated returns exhaust the full return event. -/
private theorem iUnion_returnsBefore (P : DiscreteDecisionProcess) (A : Set P.X) :
    ⋃ N, ReturnsBefore P A N = ReturnsTo P A := by
  ext p
  simp only [mem_iUnion]
  constructor
  · rintro ⟨N, hp⟩
    rw [ReturnsBefore] at hp
    rcases mem_iUnion.1 hp with ⟨z, hpz⟩
    rw [ReturnsTo]
    refine mem_iUnion.2 ⟨z, mem_iUnion.2 ⟨?_, ?_⟩⟩
    · rw [FirstReturnBefore] at hpz
      rcases mem_iUnion.1 hpz with ⟨k, hpk⟩
      exact hpk.2.2.1
    · exact (iUnion_firstReturnBefore P A z).symm ▸ mem_iUnion.2 ⟨N, hpz⟩
  · intro hp
    rw [ReturnsTo] at hp
    rcases mem_iUnion.1 hp with ⟨z, hpz⟩
    rcases mem_iUnion.1 hpz with ⟨_hz, hpfirst⟩
    rw [← iUnion_firstReturnBefore P A z] at hpfirst
    rcases mem_iUnion.1 hpfirst with ⟨N, hpN⟩
    refine ⟨N, ?_⟩
    rw [ReturnsBefore]
    exact mem_iUnion.2 ⟨z, hpN⟩

/-- The return event is measurable as a countable union of first-return events. -/
private theorem measurableSet_returnsTo (P : DiscreteDecisionProcess) (A : Set P.X) :
    MeasurableSet (ReturnsTo P A) := by
  exact MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun _hz : z ∈ A =>
    measurableSet_firstReturnAt P A z

/-- Distinct first-return states define disjoint events. -/
private theorem pairwise_disjoint_firstReturnAt (P : DiscreteDecisionProcess) (A : Set P.X) :
    Pairwise (Function.onFun Disjoint (FirstReturnAt P A)) := by
  intro z w hzw
  rw [Function.onFun, disjoint_left]
  intro p hpz hpw
  rcases hpz with ⟨k, hk, hxk, hzk, hbeforeK⟩
  rcases hpw with ⟨l, hl, hxl, hwl, hbeforeL⟩
  have hkl : k = l := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hbeforeL k hk hlt) (hxk.symm ▸ hzk)
    · exact (hbeforeK l hl hgt) (hxl.symm ▸ hwl)
  apply hzw
  rw [← hxk, hkl, hxl]

/-- The probability `q_y^A` of returning to `A` after forcing action `y` at `x`. -/
def ReturnProbability (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (A : Set P.X) (x : P.X) (y : P.Y x) : ℝ≥0∞ :=
  S.afterAction x y (ReturnsTo P A)

/-- The probability `q_y^{A,z}` that the first return to `A` is at `z`. -/
def FirstReturnProbability (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (A : Set P.X) (x : P.X) (y : P.Y x) (z : P.X) : ℝ≥0∞ :=
  S.afterAction x y (FirstReturnAt P A z)

/-- The return probability is the sum of its disjoint first-return-state probabilities. -/
private theorem returnProbability_eq_tsum_firstReturnProbability
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (A : Set P.X) (x : P.X) (y : P.Y x) :
    ReturnProbability P S A x y =
      ∑' z, FirstReturnProbability P S A x y z := by
  have hunion : ReturnsTo P A = ⋃ z, FirstReturnAt P A z := by
    ext p
    simp only [ReturnsTo, mem_iUnion]
    constructor
    · rintro ⟨z, _hz, hp⟩
      exact ⟨z, hp⟩
    · rintro ⟨z, hp⟩
      rcases hp with ⟨k, hk, hx, hz, hbefore⟩
      exact ⟨z, hz, ⟨k, hk, hx, hz, hbefore⟩⟩
  change S.afterAction x y (ReturnsTo P A) =
    ∑' z, S.afterAction x y (FirstReturnAt P A z)
  rw [hunion]
  exact measure_iUnion (pairwise_disjoint_firstReturnAt P A)
    (fun z => measurableSet_firstReturnAt P A z)

/-- Fixed-state truncated return probabilities converge to the first-return probability. -/
private theorem tendsto_firstReturnBeforeProbability (P : DiscreteDecisionProcess)
    (S : DDPSemantics P) (A : Set P.X) (x : P.X) (y : P.Y x) (z : P.X) :
    Tendsto (fun N => (S.afterAction x y (FirstReturnBefore P A z N)).toReal)
      atTop (nhds (FirstReturnProbability P S A x y z).toReal) := by
  have hmeasure := tendsto_measure_iUnion_atTop
    (μ := S.afterAction x y) (firstReturnBefore_mono P A z)
  rw [iUnion_firstReturnBefore P A z] at hmeasure
  have hfinite : FirstReturnProbability P S A x y z ≠ ⊤ := by
    letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
    exact measure_ne_top _ _
  exact (ENNReal.tendsto_toReal hfinite).comp hmeasure

/-- Truncated return probabilities converge to `q_y^A`. -/
private theorem tendsto_returnsBeforeProbability (P : DiscreteDecisionProcess)
    (S : DDPSemantics P) (A : Set P.X) (x : P.X) (y : P.Y x) :
    Tendsto (fun N => (S.afterAction x y (ReturnsBefore P A N)).toReal)
      atTop (nhds (ReturnProbability P S A x y).toReal) := by
  have hmeasure := tendsto_measure_iUnion_atTop
    (μ := S.afterAction x y) (returnsBefore_mono P A)
  rw [iUnion_returnsBefore P A] at hmeasure
  have hfinite : ReturnProbability P S A x y ≠ ⊤ := by
    letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
    exact measure_ne_top _ _
  exact (ENNReal.tendsto_toReal hfinite).comp hmeasure

/-- The truncated first-return value sums converge to the full first-return value sum. -/
private theorem DiscreteDecisionProcess.tendsto_firstReturnBeforeValue
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (A : Set P.X) (x c : P.X) (y : P.Y x) :
    Tendsto
      (fun N => ∑' z,
        (S.afterAction x y (FirstReturnBefore P A z N)).toReal * P.valueX z)
      atTop
      (nhds (∑' z, (FirstReturnProbability P S A x y z).toReal * P.valueX z)) := by
  let C := ‖P.valueX c‖ + P.valueDifferenceBound
  let bound : P.X → ℝ := fun z =>
    (FirstReturnProbability P S A x y z).toReal * C
  have hreturnFinite : ReturnProbability P S A x y ≠ ⊤ := by
    letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
    exact measure_ne_top _ _
  have hprobabilitySummable : Summable fun z =>
      (FirstReturnProbability P S A x y z).toReal := by
    apply ENNReal.summable_toReal
    rw [← returnProbability_eq_tsum_firstReturnProbability P S A x y]
    exact hreturnFinite
  have hboundSummable : Summable bound := hprobabilitySummable.mul_right C
  apply tendsto_tsum_of_dominated_convergence hboundSummable
  · intro z
    exact (tendsto_firstReturnBeforeProbability P S A x y z).mul_const (P.valueX z)
  · filter_upwards with N z
    have hsubset : FirstReturnBefore P A z N ⊆ FirstReturnAt P A z := by
      intro path hpath
      rw [← iUnion_firstReturnBefore P A z]
      exact mem_iUnion.2 ⟨N, hpath⟩
    have hprobability :
        (S.afterAction x y (FirstReturnBefore P A z N)).toReal ≤
          (FirstReturnProbability P S A x y z).toReal := by
      apply ENNReal.toReal_mono
      · letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
        exact measure_ne_top _ _
      · exact measure_mono hsubset
    have hvalue : ‖P.valueX z‖ ≤ C := by
      calc
        ‖P.valueX z‖ ≤ ‖P.valueX z - P.valueX c‖ + ‖P.valueX c‖ := by
          simpa only [sub_add_cancel] using
            norm_add_le (P.valueX z - P.valueX c) (P.valueX c)
        _ ≤ P.valueDifferenceBound + ‖P.valueX c‖ := by
          gcongr
          simpa only [Real.norm_eq_abs] using
            (P.valueDifference z c
              (Classical.choose (P.choose z).support_nonempty)
              (Classical.choose (P.choose c).support_nonempty)).1
        _ = C := by simp only [C]; ring
    change ‖(S.afterAction x y (FirstReturnBefore P A z N)).toReal * P.valueX z‖ ≤
      (FirstReturnProbability P S A x y z).toReal * C
    rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul hprobability hvalue (norm_nonneg _) ENNReal.toReal_nonneg

/-- The full first-return value differs from `valueY` only on the no-return mass. -/
private theorem DiscreteDecisionProcess.firstReturn_centered_bound_of_uniform
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (A : Set P.X) (x : P.X) (y : P.Y x) (r : ℝ)
    (hr : ∀ z (w : P.Y z), |P.valueY z w - r| ≤ P.valueDifferenceBound) :
    |P.valueY x y -
        (∑' z, (FirstReturnProbability P S A x y z).toReal * P.valueX z) -
        (1 - (ReturnProbability P S A x y).toReal) * r| ≤
      P.valueDifferenceBound * (1 - (ReturnProbability P S A x y).toReal) := by
  let truncatedValue : ℕ → ℝ := fun N =>
    ∑' z, (S.afterAction x y (FirstReturnBefore P A z N)).toReal * P.valueX z
  let truncatedProbability : ℕ → ℝ := fun N =>
    (S.afterAction x y (ReturnsBefore P A N)).toReal
  have hvalue : Tendsto truncatedValue atTop
      (nhds (∑' z, (FirstReturnProbability P S A x y z).toReal * P.valueX z)) := by
    exact P.tendsto_firstReturnBeforeValue S A x x y
  have hprobability : Tendsto truncatedProbability atTop
      (nhds (ReturnProbability P S A x y).toReal) := by
    exact tendsto_returnsBeforeProbability P S A x y
  have hcenter : Tendsto
      (fun N => P.valueY x y - truncatedValue N -
        (1 - truncatedProbability N) * r)
      atTop
      (nhds (P.valueY x y -
        (∑' z, (FirstReturnProbability P S A x y z).toReal * P.valueX z) -
        (1 - (ReturnProbability P S A x y).toReal) * r)) := by
    exact (tendsto_const_nhds.sub hvalue).sub
      ((tendsto_const_nhds.sub hprobability).mul_const r)
  have hleft := hcenter.abs
  have hright : Tendsto
      (fun N => P.valueDifferenceBound * (1 - truncatedProbability N))
      atTop
      (nhds (P.valueDifferenceBound *
        (1 - (ReturnProbability P S A x y).toReal))) := by
    exact tendsto_const_nhds.mul (tendsto_const_nhds.sub hprobability)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact P.boundedFirstReturn_centered_bound_semantic_of_uniform S x y A N hN r hr

/-- The full first-return estimate centered at a state value. -/
private theorem DiscreteDecisionProcess.firstReturn_centered_bound
    (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (A : Set P.X) (x c : P.X) (y : P.Y x) :
    |P.valueY x y -
        (∑' z, (FirstReturnProbability P S A x y z).toReal * P.valueX z) -
        (1 - (ReturnProbability P S A x y).toReal) * P.valueX c| ≤
      P.valueDifferenceBound * (1 - (ReturnProbability P S A x y).toReal) := by
  apply P.firstReturn_centered_bound_of_uniform S A x y (P.valueX c)
  intro z w
  simpa only using
    (P.valueDifference z c w (Classical.choose (P.choose c).support_nonempty)).2.1

/-- A state-started law first samples the action and then follows its forced-action law. -/
private theorem DDPSemantics.fromState_eq_initialActionMixture
    (P : DiscreteDecisionProcess) (S : DDPSemantics P) (x : P.X) :
    S.fromState x = Measure.sum fun y : P.Y x =>
      (P.choose x y : ℝ≥0∞) • S.afterAction x y := by
  classical
  let mixture := Measure.sum fun y : P.Y x =>
    (P.choose x y : ℝ≥0∞) • S.afterAction x y
  change S.fromState x = mixture
  letI : IsProbabilityMeasure (S.fromState x) := S.fromStateProbability x
  have hmixtureUniv : mixture Set.univ = 1 := by
    have hafterUniv (y : P.Y x) : S.afterAction x y Set.univ = 1 := by
      letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
      exact measure_univ
    dsimp only [mixture]
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp_rw [Measure.smul_apply, hafterUniv, smul_eq_mul, mul_one]
    exact PMF.tsum_coe (P.choose x)
  apply ext_of_generate_finite
    {U | ∃ k, ∃ h : DDPFinitePath P k, U = DDPCylinder P h}
    rfl (isPiSystem_ddpCylinders P)
  · intro U hU
    rcases hU with ⟨k, h, rfl⟩
    cases k with
    | zero =>
        dsimp only [mixture]
        rw [Measure.sum_apply _ (measurableSet_ddpCylinder P h)]
        by_cases hstart : h.x 0 = x
        · rw [S.fromStateCylinder x 0 h hstart]
          simp_rw [Measure.smul_apply, smul_eq_mul,
            S.afterAction_zeroCylinder_eq_one P x _ h hstart, mul_one]
          simp only [DDPFinitePath.probability]
          rw [PMF.tsum_coe]
          simp
        · rw [S.fromState_cylinder_eq_zero_of_wrong P x h hstart]
          simp_rw [Measure.smul_apply, smul_eq_mul,
            S.afterAction_zeroCylinder_eq_zero P x _ h hstart, mul_zero]
          exact tsum_zero.symm
    | succ k =>
        dsimp only [mixture]
        rw [Measure.sum_apply _ (measurableSet_ddpCylinder P h)]
        simp_rw [Measure.smul_apply, smul_eq_mul]
        by_cases hstart : h.x 0 = x
        · cases hstart
          rw [S.fromStateCylinder (h.x 0) (k + 1) h rfl]
          have hsum : (∑' other : P.Y (h.x 0),
              (P.choose (h.x 0) other : ℝ≥0∞) *
                S.afterAction (h.x 0) other (DDPCylinder P h)) =
              (P.choose (h.x 0) (h.y 0) : ℝ≥0∞) *
                S.afterAction (h.x 0) (h.y 0) (DDPCylinder P h) := by
            apply tsum_eq_single (L := SummationFilter.unconditional _) (h.y 0)
            intro other hother
            rw [S.afterAction_cylinder_eq_zero_of_wrong P (h.x 0) other h]
            · simp
            · right
              intro heq
              exact hother (eq_of_heq heq.symm)
          rw [hsum, S.afterActionCylinder (h.x 0) (h.y 0) k h rfl (by rfl)]
          exact h.probability_eq_choose_mul_afterActionProbability P
        · rw [S.fromState_cylinder_eq_zero_of_wrong P x h hstart]
          simp_rw [S.afterAction_cylinder_eq_zero_of_wrong P x _ h (Or.inl hstart),
            mul_zero]
          exact tsum_zero.symm
  · rw [measure_univ, hmixtureUniv]

/-- The return probability from a state is the action mixture of forced-action returns. -/
private theorem DDPSemantics.fromState_returnsTo_eq_tsum
    (P : DiscreteDecisionProcess) (S : DDPSemantics P) (A : Set P.X) (x : P.X) :
    S.fromState x (ReturnsTo P A) =
      ∑' y : P.Y x, P.choose x y * ReturnProbability P S A x y := by
  rw [S.fromState_eq_initialActionMixture P x]
  rw [Measure.sum_apply _ (measurableSet_returnsTo P A)]
  simp only [Measure.smul_apply, smul_eq_mul, ReturnProbability]

/-- The paper's `m_x`: probability of no positive-time return to `A` from `x`. -/
private def NoReturnProbability (P : DiscreteDecisionProcess) (S : DDPSemantics P)
    (A : Set P.X) (x : P.X) : ℝ :=
  (S.fromState x (ReturnsTo P A)ᶜ).toReal

private theorem noReturnProbability_nonneg (P : DiscreteDecisionProcess)
    (S : DDPSemantics P) (A : Set P.X) (x : P.X) :
    0 ≤ NoReturnProbability P S A x := ENNReal.toReal_nonneg

private theorem noReturnProbability_le_one (P : DiscreteDecisionProcess)
    (S : DDPSemantics P) (A : Set P.X) (x : P.X) :
    NoReturnProbability P S A x ≤ 1 := by
  letI : IsProbabilityMeasure (S.fromState x) := S.fromStateProbability x
  rw [NoReturnProbability, ← ENNReal.toReal_one]
  apply ENNReal.toReal_mono (by simp)
  calc
    S.fromState x (ReturnsTo P A)ᶜ ≤ S.fromState x Set.univ :=
      measure_mono (subset_univ _)
    _ = 1 := measure_univ

/-- No-return probability is the action-weighted mean of forced-action no-return masses. -/
private theorem noReturnProbability_eq_tsum
    (P : DiscreteDecisionProcess) (S : DDPSemantics P) (A : Set P.X) (x : P.X) :
    NoReturnProbability P S A x =
      ∑' y : P.Y x, (P.choose x y).toReal *
        (1 - (ReturnProbability P S A x y).toReal) := by
  have hmix := congrArg (fun mu : Measure (DDPPath P) => mu (ReturnsTo P A)ᶜ)
    (S.fromState_eq_initialActionMixture P x)
  rw [Measure.sum_apply _ (measurableSet_returnsTo P A).compl] at hmix
  simp only [Measure.smul_apply, smul_eq_mul] at hmix
  have hafter_ne_top (y : P.Y x) (E : Set (DDPPath P)) :
      S.afterAction x y E ≠ ⊤ := by
    letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
    exact measure_ne_top _ _
  rw [NoReturnProbability, hmix]
  rw [ENNReal.tsum_toReal_eq (fun y => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (hafter_ne_top y _))]
  apply tsum_congr
  intro y
  rw [ENNReal.toReal_mul]
  have hcomplement : S.afterAction x y (ReturnsTo P A)ᶜ =
      1 - ReturnProbability P S A x y := by
    rw [measure_compl (measurableSet_returnsTo P A) (hafter_ne_top y _)]
    letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
    rw [measure_univ]
    rfl
  rw [hcomplement]
  rw [ENNReal.toReal_sub_of_le (by
    letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
    change S.afterAction x y (ReturnsTo P A) ≤ 1
    calc
      S.afterAction x y (ReturnsTo P A) ≤ S.afterAction x y Set.univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ) (by simp)]
  simp

/-- Last-exit mass at a sampled stage is occupation mass times its restarted no-return mass. -/
private theorem DiscreteDecisionProcess.rawLawFrom_inter_shift_noReturn_stageAt
    (P : DiscreteDecisionProcess) (S : DDPSemantics P) (start : P.X)
    (A : Set P.X) (i : ℕ) (current : DDPStage P) :
    P.rawLawFrom start
        (P.rawShift i ⁻¹' (DDPPath.ofRaw P ⁻¹' (ReturnsTo P A)ᶜ) ∩
          {stage | stage i = current}) =
      P.rawLawFrom start {stage | stage i = current} *
        (1 - ReturnProbability P S A current.1 current.2) := by
  have hreturns : MeasurableSet (ReturnsTo P A) := measurableSet_returnsTo P A
  have hraw : MeasurableSet (DDPPath.ofRaw P ⁻¹' (ReturnsTo P A)ᶜ) :=
    (DDPPath.measurable_ofRaw P) hreturns.compl
  rw [DiscreteDecisionProcess.rawLawFrom]
  rw [P.rawLawWithInitial_inter_shift_stageAt (P.initialStagePMF start) i current hraw]
  congr 1
  have hcanonical := congrArg (fun mu : Measure (DDPPath P) => mu (ReturnsTo P A)ᶜ)
    (S.afterAction_eq_rawLaw P current.1 current.2)
  rw [Measure.map_apply (DDPPath.measurable_ofRaw P) hreturns.compl] at hcanonical
  rw [← hcanonical]
  rw [measure_compl hreturns]
  · letI : IsProbabilityMeasure (S.afterAction current.1 current.2) :=
      S.afterActionProbability current.1 current.2
    rw [measure_univ]
    rfl
  · letI : IsProbabilityMeasure (S.afterAction current.1 current.2) :=
      S.afterActionProbability current.1 current.2
    exact measure_ne_top _ _

/-- Conditional on the state at a sampled stage, its action still has the displayed choice law. -/
private theorem DiscreteDecisionProcess.rawLawFrom_stage_eq_state_mul_choose
    (P : DiscreteDecisionProcess) (S : DDPSemantics P) (start : P.X)
    (i : ℕ) (x : P.X) (y : P.Y x) :
    P.rawLawFrom start {stage | stage i = (⟨x, y⟩ : DDPStage P)} =
      P.rawLawFrom start {stage | (stage i).1 = x} * P.choose x y := by
  classical
  let H := {h : DDPFinitePath P i // h.x (Fin.last i) = x}
  let C : H → Set (ℕ → DDPStage P) := fun h =>
    DDPPath.ofRaw P ⁻¹' DDPCylinder P h.1
  let D : H → Set (ℕ → DDPStage P) := fun h =>
    {stage | ∀ j : Fin (i + 1),
      stage j = h.1.extendWithFinalStage P (⟨x, y⟩ : DDPStage P) j}
  have hstateUnion : {stage : ℕ → DDPStage P | (stage i).1 = x} = ⋃ h, C h := by
    ext stage
    simp only [mem_setOf_eq, mem_iUnion, C]
    constructor
    · intro hstate
      let h := (DDPPath.ofRaw P stage).prefix P i
      refine ⟨⟨h, ?_⟩, rfl⟩
      simpa [h, DDPPath.prefix, DDPPath.ofRaw] using hstate
    · rintro ⟨h, hpref⟩
      change (DDPPath.ofRaw P stage).prefix P i = h.1 at hpref
      have hlast := congrArg (fun q : DDPFinitePath P i => q.x (Fin.last i)) hpref
      exact hlast.trans h.2
  have hactionUnion :
      {stage : ℕ → DDPStage P | stage i = (⟨x, y⟩ : DDPStage P)} = ⋃ h, D h := by
    ext stage
    simp only [mem_setOf_eq, mem_iUnion, D]
    constructor
    · intro hstage
      let h := (DDPPath.ofRaw P stage).prefix P i
      have hlast : h.x (Fin.last i) = x := by
        simpa [h, DDPPath.prefix, DDPPath.ofRaw] using congrArg Sigma.fst hstage
      refine ⟨⟨h, hlast⟩, ?_⟩
      intro j
      induction j using Fin.lastCases with
      | last => simpa [DDPFinitePath.extendWithFinalStage] using hstage
      | cast j =>
          simp [DDPFinitePath.extendWithFinalStage, h, DDPPath.prefix,
            DDPPath.ofRaw]
    · rintro ⟨h, hprefix⟩
      simpa [DDPFinitePath.extendWithFinalStage] using hprefix (Fin.last i)
  have hmeasurableC (h : H) : MeasurableSet (C h) :=
    (DDPPath.measurable_ofRaw P) (measurableSet_ddpCylinder P h.1)
  have hmeasurableD (h : H) : MeasurableSet (D h) :=
    P.measurableSet_rawStageCylinder i (h.1.extendWithFinalStage P ⟨x, y⟩)
  have hpairwiseC : Pairwise (Function.onFun Disjoint C) := by
    intro first second hne
    rw [Function.onFun, Set.disjoint_left]
    intro stage hfirst hsecond
    apply hne
    apply Subtype.ext
    exact hfirst.symm.trans hsecond
  have hpairwiseD : Pairwise (Function.onFun Disjoint D) := by
    intro first second hne
    rw [Function.onFun, Set.disjoint_left]
    intro stage hfirst hsecond
    apply hne
    apply Subtype.ext
    apply DDPFinitePath.ext_of_stages P
    · intro j
      induction j using Fin.lastCases with
      | last => exact first.2.trans second.2.symm
      | cast j =>
          have hj := (hfirst j.castSucc).symm.trans (hsecond j.castSucc)
          simpa [D, DDPFinitePath.extendWithFinalStage] using congrArg Sigma.fst hj
    · intro j
      have hj := (hfirst j.castSucc).symm.trans (hsecond j.castSucc)
      simpa [D, DDPFinitePath.extendWithFinalStage] using hj
  have hmeasure (h : H) : P.rawLawFrom start (D h) =
      P.rawLawFrom start (C h) * P.choose x y := by
    by_cases hstart : h.1.x 0 = start
    · let last : P.Y (h.1.x (Fin.last i)) :=
        _root_.cast (congrArg P.Y h.2.symm) y
      have hcurrent : (⟨x, y⟩ : DDPStage P) =
          ⟨h.1.x (Fin.last i), last⟩ := by
        apply Sigma.ext h.2.symm
        simp [last]
      have hD : D h = {stage | ∀ j : Fin (i + 1),
          stage j = h.1.stagesWithFinal P last j} := by
        ext stage
        simp only [D, mem_setOf_eq]
        rw [hcurrent, h.1.extendWithFinalStage_mk P last]
      rw [hD, P.rawLawFrom_stagesWithFinal start h.1 hstart last]
      rw [show P.choose (h.1.x (Fin.last i)) last = P.choose x y from
        congrArg (fun current : DDPStage P => P.choose current.1 current.2)
          hcurrent.symm]
      rw [P.rawLawFrom_ddpCylinder start h.1 hstart]
    · have hCzero := P.rawLawFrom_ddpCylinder_eq_zero_of_wrong S start h.1 hstart
      have hDsubset : D h ⊆ C h := by
        intro stage hstage
        change (DDPPath.ofRaw P stage).prefix P i = h.1
        apply DDPFinitePath.ext_of_stages P
        · intro j
          induction j using Fin.lastCases with
          | last =>
              have hj := congrArg Sigma.fst (hstage (Fin.last i))
              have hj' : (stage i).1 = x := by
                simpa [D, DDPFinitePath.extendWithFinalStage] using hj
              exact hj'.trans h.2.symm
          | cast j =>
              simpa [D, DDPFinitePath.extendWithFinalStage, DDPPath.prefix,
                DDPPath.ofRaw] using congrArg Sigma.fst (hstage j.castSucc)
        · intro j
          simpa [D, DDPFinitePath.extendWithFinalStage, DDPPath.prefix,
            DDPPath.ofRaw] using hstage j.castSucc
      have hDzero : P.rawLawFrom start (D h) = 0 :=
        nonpos_iff_eq_zero.mp ((measure_mono hDsubset).trans_eq hCzero)
      rw [hDzero, hCzero, zero_mul]
  rw [hactionUnion, measure_iUnion hpairwiseD hmeasurableD]
  rw [hstateUnion, measure_iUnion hpairwiseC hmeasurableC]
  simp_rw [hmeasure]
  exact ENNReal.tsum_mul_right

/-- Expected absolute increment at one time, grouped by the state sampled then. -/
private def DiscreteDecisionProcess.rawStateVariation
    (P : DiscreteDecisionProcess) (start : P.X) (i : ℕ) (x : P.X) : ℝ≥0∞ :=
  P.rawLawFrom start {stage | (stage i).1 = x} *
    ∑' y : P.Y x, P.choose x y * ENNReal.ofReal |DDPStage.increment P ⟨x, y⟩|

/-- Integrating one raw-stage increment is the sum of its statewise action averages. -/
private theorem DiscreteDecisionProcess.lintegral_rawIncrement_eq_tsum_stateVariation
    (P : DiscreteDecisionProcess) (S : DDPSemantics P) (start : P.X) (i : ℕ) :
    (∫⁻ stage, ENNReal.ofReal |DDPStage.increment P (stage i)|
        ∂P.rawLawFrom start) =
      ∑' x : P.X, P.rawStateVariation start i x := by
  have heval : Measurable (fun stage : ℕ → DDPStage P => stage i) := measurable_pi_apply i
  rw [← lintegral_map (f := fun current : DDPStage P =>
    ENNReal.ofReal |DDPStage.increment P current|) Measurable.of_discrete heval]
  rw [lintegral_countable']
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro x
  rw [DiscreteDecisionProcess.rawStateVariation, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro y
  rw [Measure.map_apply heval (measurableSet_singleton (⟨x, y⟩ : DDPStage P))]
  change ENNReal.ofReal |DDPStage.increment P ⟨x, y⟩| *
      P.rawLawFrom start {stage | stage i = (⟨x, y⟩ : DDPStage P)} = _
  rw [P.rawLawFrom_stage_eq_state_mul_choose S start i x y]
  ac_rfl

/-- Expected total variation is the sum of the statewise action averages at every time. -/
private theorem ExpectedDDPVariation.eq_tsum_rawStateVariation
    (P : DiscreteDecisionProcess) (S : DDPSemantics P) :
    ExpectedDDPVariation P S =
      ∑' index : ℕ × P.X, P.rawStateVariation P.initial index.1 index.2 := by
  rw [ExpectedDDPVariation, S.law_eq_rawLaw]
  rw [lintegral_map (DDPTotalVariation.measurable P) (DDPPath.measurable_ofRaw P)]
  simp only [P.totalVariation_ofRaw]
  rw [lintegral_tsum]
  · rw [ENNReal.tsum_prod]
    apply tsum_congr
    intro i
    exact P.lintegral_rawIncrement_eq_tsum_stateVariation S P.initial i
  · intro i
    have hincrement : Measurable (DDPStage.increment P) := Measurable.of_discrete
    exact (hincrement.comp
      (measurable_pi_apply (X := fun _ : ℕ => DDPStage P) i)).abs.ennreal_ofReal.aemeasurable

/-- A statewise variation term is the nonnegative-real lift of its real probability average. -/
private theorem DiscreteDecisionProcess.rawStateVariation_eq_ofReal
    (P : DiscreteDecisionProcess) (start : P.X) (i : ℕ) (x : P.X) :
    P.rawStateVariation start i x = ENNReal.ofReal
      ((P.rawLawFrom start {stage | (stage i).1 = x}).toReal *
        (∑' y : P.Y x, (P.choose x y).toReal *
          |DDPStage.increment P ⟨x, y⟩|)) := by
  have hweights : Summable fun y : P.Y x => (P.choose x y).toReal :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; simp)
  have hincrements : Summable fun y : P.Y x =>
      (P.choose x y).toReal * |DDPStage.increment P ⟨x, y⟩| := by
    apply Summable.of_norm_bounded (hweights.mul_right P.valueDifferenceBound)
    intro y
    rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_eq_abs, abs_abs]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using DDPStage.norm_increment_le P ⟨x, y⟩)
      ENNReal.toReal_nonneg
  rw [DiscreteDecisionProcess.rawStateVariation]
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  rw [ENNReal.ofReal_toReal]
  · rw [ENNReal.ofReal_tsum_of_nonneg
        (fun y => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)) hincrements]
    apply congrArg ((P.rawLawFrom start {stage | (stage i).1 = x}) * ·)
    apply tsum_congr
    intro y
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    rw [ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
  · letI : IsProbabilityMeasure (P.rawLawFrom start) := P.isProbabilityMeasure_rawLawFrom start
    exact measure_ne_top _ _

/-- The raw event that the displayed sampled stage is the last visit to `A`. -/
private def DiscreteDecisionProcess.rawLastExitAtStage
    (P : DiscreteDecisionProcess) (A : Set P.X) (i : ℕ) (current : DDPStage P) :
    Set (ℕ → DDPStage P) :=
  P.rawShift i ⁻¹' (DDPPath.ofRaw P ⁻¹' (ReturnsTo P A)ᶜ) ∩
    {stage | stage i = current}

/-- Occupation mass times `m_x` is the sum of last-exit masses over actions at `x`. -/
private theorem DiscreteDecisionProcess.rawLawFrom_state_mul_noReturn_eq_tsum
    (P : DiscreteDecisionProcess) (S : DDPSemantics P) (start : P.X)
    (A : Set P.X) (i : ℕ) (x : P.X) :
    (P.rawLawFrom start {stage | (stage i).1 = x}).toReal *
        NoReturnProbability P S A x =
      ∑' y : P.Y x,
        (P.rawLawFrom start (P.rawLastExitAtStage A i ⟨x, y⟩)).toReal := by
  rw [noReturnProbability_eq_tsum P S A x]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro y
  rw [DiscreteDecisionProcess.rawLastExitAtStage]
  rw [P.rawLawFrom_inter_shift_noReturn_stageAt S start A i ⟨x, y⟩]
  rw [P.rawLawFrom_stage_eq_state_mul_choose S start i x y]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  rw [ENNReal.toReal_sub_of_le]
  · simp only [ENNReal.toReal_one]
    ring_nf
  · letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
    change S.afterAction x y (ReturnsTo P A) ≤ 1
    calc
      S.afterAction x y (ReturnsTo P A) ≤ S.afterAction x y Set.univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
  · simp

/-- Last exits from `A`, indexed by their time and sampled stage, have total mass at most one. -/
private theorem DiscreteDecisionProcess.tsum_rawLastExitAtStage_le_one_ennreal
    (P : DiscreteDecisionProcess) (start : P.X) (A : Set P.X) :
    (∑' index : ℕ × {current : DDPStage P // current.1 ∈ A},
      P.rawLawFrom start (P.rawLastExitAtStage A index.1 index.2.1)) ≤ 1 := by
  classical
  let K := ℕ × {current : DDPStage P // current.1 ∈ A}
  let L : K → Set (ℕ → DDPStage P) := fun index =>
    P.rawLastExitAtStage A index.1 index.2.1
  have hmeasurable (index : K) : MeasurableSet (L index) := by
    apply MeasurableSet.inter
    · exact (P.measurable_rawShift index.1)
        ((DDPPath.measurable_ofRaw P) (measurableSet_returnsTo P A).compl)
    · exact show MeasurableSet
          ((fun stage : ℕ → DDPStage P => stage index.1) ⁻¹' {index.2.1}) from
        (measurable_pi_apply index.1) (measurableSet_singleton index.2.1)
  have hpairwise : Pairwise (Function.onFun Disjoint L) := by
    intro first second hne
    rw [Function.onFun, Set.disjoint_left]
    intro stage hfirst hsecond
    rcases hfirst with ⟨hfirstNoReturn, hfirstStage⟩
    rcases hsecond with ⟨hsecondNoReturn, hsecondStage⟩
    by_cases htime : first.1 = second.1
    · apply hne
      apply Prod.ext htime
      apply Subtype.ext
      exact hfirstStage.symm.trans (htime ▸ hsecondStage)
    · rcases lt_or_gt_of_ne htime with hlt | hgt
      · apply hfirstNoReturn
        rw [mem_returnsTo_iff]
        refine ⟨second.1 - first.1, by omega, ?_⟩
        change (stage (first.1 + (second.1 - first.1))).1 ∈ A
        rw [Nat.add_sub_of_le hlt.le]
        exact hsecondStage.symm ▸ second.2.2
      · apply hsecondNoReturn
        rw [mem_returnsTo_iff]
        refine ⟨first.1 - second.1, by omega, ?_⟩
        change (stage (second.1 + (first.1 - second.1))).1 ∈ A
        rw [Nat.add_sub_of_le hgt.le]
        exact hfirstStage.symm ▸ first.2.2
  rw [← measure_iUnion hpairwise hmeasurable]
  letI : IsProbabilityMeasure (P.rawLawFrom start) := P.isProbabilityMeasure_rawLawFrom start
  calc
    P.rawLawFrom start (⋃ index, L index) ≤ P.rawLawFrom start Set.univ :=
      measure_mono (subset_univ _)
    _ = 1 := measure_univ

/-- The real last-exit masses are summable and their sum is at most one. -/
private theorem DiscreteDecisionProcess.summable_rawLastExitAtStage_and_tsum_le_one
    (P : DiscreteDecisionProcess) (start : P.X) (A : Set P.X) :
    Summable (fun index : ℕ × {current : DDPStage P // current.1 ∈ A} =>
      (P.rawLawFrom start
        (P.rawLastExitAtStage A index.1 index.2.1)).toReal) ∧
      (∑' index : ℕ × {current : DDPStage P // current.1 ∈ A},
        (P.rawLawFrom start
          (P.rawLastExitAtStage A index.1 index.2.1)).toReal) ≤ 1 := by
  let K := ℕ × {current : DDPStage P // current.1 ∈ A}
  let L : K → Set (ℕ → DDPStage P) := fun index =>
    P.rawLastExitAtStage A index.1 index.2.1
  have hmeasure : (∑' index : K, P.rawLawFrom start (L index)) ≤ 1 := by
    simpa only [K, L] using P.tsum_rawLastExitAtStage_le_one_ennreal start A
  have hneTop : (∑' index : K, P.rawLawFrom start (L index)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) hmeasure
  have hfinite (index : K) : P.rawLawFrom start (L index) ≠ ⊤ := by
    letI : IsProbabilityMeasure (P.rawLawFrom start) := P.isProbabilityMeasure_rawLawFrom start
    exact measure_ne_top _ _
  refine ⟨ENNReal.summable_toReal hneTop, ?_⟩
  have hreal := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hmeasure
  rw [ENNReal.tsum_toReal_eq hfinite] at hreal
  simpa only [ENNReal.toReal_one, K, L] using hreal

/-- Reindex last exits by time, state in `A`, and the action sampled there. -/
private def DiscreteDecisionProcess.rawLastExitIndexEquiv
    (P : DiscreteDecisionProcess) (A : Set P.X) :
    (Σ index : ℕ × {x : P.X // x ∈ A}, P.Y index.2.1) ≃
      ℕ × {current : DDPStage P // current.1 ∈ A} where
  toFun index := ⟨index.1.1, ⟨⟨index.1.2.1, index.2⟩, index.1.2.2⟩⟩
  invFun index := ⟨⟨index.1, ⟨index.2.1.1, index.2.2⟩⟩, index.2.1.2⟩
  left_inv index := by cases index; rfl
  right_inv index := by cases index; rfl

/-- Nested state/action last-exit masses are summable and have total mass at most one. -/
private theorem DiscreteDecisionProcess.summable_nested_rawLastExit_and_tsum_le_one
    (P : DiscreteDecisionProcess) (start : P.X) (A : Set P.X) :
    Summable (fun index : ℕ × {x : P.X // x ∈ A} =>
      ∑' y : P.Y index.2.1,
        (P.rawLawFrom start
          (P.rawLastExitAtStage A index.1 ⟨index.2.1, y⟩)).toReal) ∧
      (∑' index : ℕ × {x : P.X // x ∈ A},
        ∑' y : P.Y index.2.1,
          (P.rawLawFrom start
            (P.rawLastExitAtStage A index.1 ⟨index.2.1, y⟩)).toReal) ≤ 1 := by
  let K := ℕ × {current : DDPStage P // current.1 ∈ A}
  let f : K → ℝ := fun index =>
    (P.rawLawFrom start (P.rawLastExitAtStage A index.1 index.2.1)).toReal
  let J := Σ index : ℕ × {x : P.X // x ∈ A}, P.Y index.2.1
  let g : J → ℝ := fun index =>
    (P.rawLawFrom start
      (P.rawLastExitAtStage A index.1.1 ⟨index.1.2.1, index.2⟩)).toReal
  have hf : Summable f ∧ (∑' index, f index) ≤ 1 := by
    simpa only [K, f] using P.summable_rawLastExitAtStage_and_tsum_le_one start A
  have hg : Summable g := by
    change Summable (f ∘ P.rawLastExitIndexEquiv A)
    exact (P.rawLastExitIndexEquiv A).summable_iff.2 hf.1
  refine ⟨?_, ?_⟩
  · simpa only [J, g] using hg.sigma
  · rw [← hg.tsum_sigma]
    change (∑' index : J, g index) ≤ 1
    change (∑' index : J, f (P.rawLastExitIndexEquiv A index)) ≤ 1
    rw [(P.rawLastExitIndexEquiv A).tsum_eq]
    exact hf.2

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

/-- A positive-return conditional value is within `M` of every sampled action value. -/
private theorem ReturnValueData.valueY_sub_value_le_of_positive
    {P : DiscreteDecisionProcess} {S : DDPSemantics P} (R : ReturnValueData P S)
    (A : Set P.X) (x : P.X) (y : P.Y x)
    (hq : 0 < ReturnProbability P S A x y) (z : P.X) (w : P.Y z) :
    |P.valueY z w - R.value A x y| ≤ P.valueDifferenceBound := by
  let q := (ReturnProbability P S A x y).toReal
  let a : P.X → ℝ := fun t => (FirstReturnProbability P S A x y t).toReal
  have hqFinite : ReturnProbability P S A x y ≠ ⊤ := by
    letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
    exact measure_ne_top _ _
  have hqPos : 0 < q := ENNReal.toReal_pos (ne_of_gt hq) hqFinite
  have haSummable : Summable a := by
    apply ENNReal.summable_toReal
    rw [← returnProbability_eq_tsum_firstReturnProbability P S A x y]
    exact hqFinite
  have hsumA : ∑' t, a t = q := by
    have hreal := ENNReal.tsum_toReal_eq fun t => by
      letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
      exact (show FirstReturnProbability P S A x y t ≠ ⊤ from measure_ne_top _ _)
    rw [← returnProbability_eq_tsum_firstReturnProbability P S A x y] at hreal
    simpa [a, q] using hreal.symm
  have hvalueBound (t : P.X) :
      ‖P.valueX t‖ ≤ ‖P.valueY z w‖ + P.valueDifferenceBound := by
    calc
      ‖P.valueX t‖ ≤ ‖P.valueX t - P.valueY z w‖ + ‖P.valueY z w‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (P.valueX t - P.valueY z w) (P.valueY z w)
      _ ≤ P.valueDifferenceBound + ‖P.valueY z w‖ := by
        gcongr
        simpa only [Real.norm_eq_abs, abs_sub_comm] using
          (P.valueDifference z t w
            (Classical.choose (P.choose t).support_nonempty)).2.1
      _ = _ := by ring
  have hvalueSummable : Summable fun t => a t * P.valueX t := by
    apply Summable.of_norm_bounded
      (haSummable.mul_right (‖P.valueY z w‖ + P.valueDifferenceBound))
    intro t
    rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (hvalueBound t) ENNReal.toReal_nonneg
  have hdiffSummable : Summable fun t => a t * (P.valueY z w - P.valueX t) := by
    apply Summable.of_norm_bounded (haSummable.mul_right P.valueDifferenceBound)
    intro t
    rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using
        (P.valueDifference z t w
          (Classical.choose (P.choose t).support_nonempty)).2.1)
      ENNReal.toReal_nonneg
  have hsumDiff :
      (∑' t, a t * (P.valueY z w - P.valueX t)) =
        q * P.valueY z w - ∑' t, a t * P.valueX t := by
    simp_rw [mul_sub]
    rw [(haSummable.mul_right (P.valueY z w)).tsum_sub hvalueSummable]
    rw [Summable.tsum_mul_right (P.valueY z w) haSummable, hsumA]
  have hdiffNorm :
      ‖∑' t, a t * (P.valueY z w - P.valueX t)‖ ≤
        q * P.valueDifferenceBound := by
    calc
      ‖∑' t, a t * (P.valueY z w - P.valueX t)‖ ≤
          ∑' t, ‖a t * (P.valueY z w - P.valueX t)‖ :=
        norm_tsum_le_tsum_norm hdiffSummable.norm
      _ ≤ ∑' t, a t * P.valueDifferenceBound := by
        apply Summable.tsum_le_tsum
        · intro t
          rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
          exact mul_le_mul_of_nonneg_left
            (by simpa only [Real.norm_eq_abs] using
              (P.valueDifference z t w
                (Classical.choose (P.choose t).support_nonempty)).2.1)
            ENNReal.toReal_nonneg
        · exact hdiffSummable.norm
        · exact haSummable.mul_right P.valueDifferenceBound
      _ = q * P.valueDifferenceBound := by
        rw [Summable.tsum_mul_right P.valueDifferenceBound haSummable, hsumA]
  rw [R.positiveEquation A x y hq]
  have halgebra :
      P.valueY z w - (∑' t, a t * P.valueX t) / q =
        (q * P.valueY z w - ∑' t, a t * P.valueX t) / q := by
    field_simp
  rw [halgebra, ← hsumDiff, abs_div]
  change ‖∑' t, a t * (P.valueY z w - P.valueX t)‖ / |q| ≤ _
  rw [abs_of_pos hqPos]
  calc
    ‖∑' t, a t * (P.valueY z w - P.valueX t)‖ / q ≤
        (q * P.valueDifferenceBound) / q :=
      div_le_div_of_nonneg_right hdiffNorm hqPos.le
    _ = P.valueDifferenceBound := by field_simp

/-- Positive return makes action value differ from the common conditional return value only
on the no-return mass. -/
private theorem ReturnValueData.valueY_sub_value_le_noReturn
    {P : DiscreteDecisionProcess} {S : DDPSemantics P} (R : ReturnValueData P S)
    (A : Set P.X) (x : P.X) (y : P.Y x)
    (hq : 0 < ReturnProbability P S A x y) :
    |P.valueY x y - R.value A x y| ≤
      P.valueDifferenceBound * (1 - (ReturnProbability P S A x y).toReal) := by
  have huniform : ∀ z (w : P.Y z),
      |P.valueY z w - R.value A x y| ≤ P.valueDifferenceBound :=
    R.valueY_sub_value_le_of_positive A x y hq
  have hcenter := P.firstReturn_centered_bound_of_uniform S A x y (R.value A x y)
    huniform
  have hqFinite : ReturnProbability P S A x y ≠ ⊤ := by
    letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
    exact measure_ne_top _ _
  have hqReal : (ReturnProbability P S A x y).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt hq) hqFinite)
  have hsum :
      (∑' z, (FirstReturnProbability P S A x y z).toReal * P.valueX z) =
        (ReturnProbability P S A x y).toReal * R.value A x y := by
    rw [R.positiveEquation A x y hq]
    field_simp
  rw [hsum] at hcenter
  have hcollapse : P.valueY x y -
      (ReturnProbability P S A x y).toReal * R.value A x y -
        (1 - (ReturnProbability P S A x y).toReal) * R.value A x y =
      P.valueY x y - R.value A x y := by
    ring_nf
  rw [hcollapse] at hcenter
  exact hcenter

/-- At a state with action-independent return value, mean decision variation is at most
`2M` times the state's no-return probability. -/
private theorem ReturnValueData.tsum_choose_mul_abs_increment_le
    {P : DiscreteDecisionProcess} {S : DDPSemantics P} (R : ReturnValueData P S)
    (A : Set P.X) (x : P.X) (hcommon : ∃ r : ℝ, ∀ y : P.Y x, R.value A x y = r) :
    (∑' y : P.Y x, (P.choose x y).toReal * |DDPStage.increment P ⟨x, y⟩|) ≤
      2 * P.valueDifferenceBound * NoReturnProbability P S A x := by
  let a : P.Y x → ℝ := fun y => (P.choose x y).toReal
  have haSummable : Summable a := ENNReal.summable_toReal (by
    rw [PMF.tsum_coe]
    simp)
  have hqle (y : P.Y x) : (ReturnProbability P S A x y).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    apply ENNReal.toReal_mono (by simp)
    letI : IsProbabilityMeasure (S.afterAction x y) := S.afterActionProbability x y
    calc
      ReturnProbability P S A x y ≤ S.afterAction x y Set.univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
  obtain ⟨r, hactionBound⟩ : ∃ r : ℝ, ∀ y : P.Y x,
      |P.valueY x y - r| ≤ P.valueDifferenceBound *
        (1 - (ReturnProbability P S A x y).toReal) := by
    by_cases hpositive : ∃ y : P.Y x, 0 < ReturnProbability P S A x y
    · rcases hpositive with ⟨positiveAction, hpositive⟩
      rcases hcommon with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      intro y
      by_cases hy : 0 < ReturnProbability P S A x y
      · simpa only [hr y] using R.valueY_sub_value_le_noReturn A x y hy
      · have hyzero : ReturnProbability P S A x y = 0 :=
          nonpos_iff_eq_zero.mp (not_lt.mp hy)
        have huniform := R.valueY_sub_value_le_of_positive A x positiveAction
          hpositive x y
        rw [hr positiveAction] at huniform
        simpa [hyzero] using huniform
    · refine ⟨P.valueX x, ?_⟩
      intro y
      have hyzero : ReturnProbability P S A x y = 0 :=
        nonpos_iff_eq_zero.mp (not_lt.mp (not_exists.mp hpositive y))
      simpa [hyzero] using (P.valueDifference x x y y).2.1
  let b : P.Y x → ℝ := fun y => P.valueDifferenceBound *
    (1 - (ReturnProbability P S A x y).toReal)
  have hbNonneg (y : P.Y x) : 0 ≤ b y :=
    mul_nonneg (le_trans zero_le_one P.valueDifferenceBound_one) (sub_nonneg.2 (hqle y))
  have hbLe (y : P.Y x) : b y ≤ P.valueDifferenceBound := by
    calc
      b y ≤ P.valueDifferenceBound * 1 := by
        apply mul_le_mul_of_nonneg_left _
          (le_trans zero_le_one P.valueDifferenceBound_one)
        linarith [show 0 ≤ (ReturnProbability P S A x y).toReal from
          ENNReal.toReal_nonneg]
      _ = P.valueDifferenceBound := mul_one _
  have habSummable : Summable fun y => a y * b y := by
    apply Summable.of_norm_bounded (haSummable.mul_right P.valueDifferenceBound)
    intro y
    rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg,
      Real.norm_of_nonneg (hbNonneg y)]
    exact mul_le_mul_of_nonneg_left (hbLe y) ENNReal.toReal_nonneg
  have habSum : (∑' y, a y * b y) =
      P.valueDifferenceBound * NoReturnProbability P S A x := by
    rw [noReturnProbability_eq_tsum P S A x]
    calc
      (∑' y, a y * b y) = ∑' y, P.valueDifferenceBound *
          ((P.choose x y).toReal *
            (1 - (ReturnProbability P S A x y).toReal)) := by
        apply tsum_congr
        intro y
        simp only [a, b]
        ring
      _ = _ := tsum_mul_left
  have hvalueBound (y : P.Y x) :
      ‖P.valueY x y‖ ≤ ‖r‖ + P.valueDifferenceBound := by
    calc
      ‖P.valueY x y‖ ≤ ‖P.valueY x y - r‖ + ‖r‖ := by
        simpa only [sub_add_cancel] using norm_add_le (P.valueY x y - r) r
      _ ≤ b y + ‖r‖ := by
        gcongr
        simpa only [Real.norm_eq_abs] using hactionBound y
      _ ≤ P.valueDifferenceBound + ‖r‖ := by gcongr; exact hbLe y
      _ = _ := by ring
  have hvalueSummable : Summable fun y => a y * P.valueY x y :=
    Summable.of_norm_bounded (haSummable.mul_right (‖r‖ + P.valueDifferenceBound))
      (fun y => by
        rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul_of_nonneg_left (hvalueBound y) ENNReal.toReal_nonneg)
  have hdiffSummable : Summable fun y => a y * (P.valueY x y - r) := by
    apply Summable.of_norm_bounded habSummable
    intro y
    rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using hactionBound y) ENNReal.toReal_nonneg
  have hstateEq : P.valueX x - r = ∑' y, a y * (P.valueY x y - r) := by
    simp_rw [mul_sub]
    rw [hvalueSummable.tsum_sub (haSummable.mul_right r)]
    rw [Summable.tsum_mul_right r haSummable, PMF.tsum_toReal]
    simpa only [a, one_mul] using
      congrArg (fun value : ℝ => value - r) (P.harmonicX x)
  have hstateBound : |P.valueX x - r| ≤
      P.valueDifferenceBound * NoReturnProbability P S A x := by
    rw [hstateEq]
    calc
      |∑' y, a y * (P.valueY x y - r)| ≤
          ∑' y, ‖a y * (P.valueY x y - r)‖ := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hdiffSummable.norm
      _ ≤ ∑' y, a y * b y := by
        apply Summable.tsum_le_tsum
        · intro y
          rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
          exact mul_le_mul_of_nonneg_left
            (by simpa only [Real.norm_eq_abs] using hactionBound y)
            ENNReal.toReal_nonneg
        · exact hdiffSummable.norm
        · exact habSummable
      _ = _ := habSum
  have hincrementSummable : Summable fun y =>
      a y * |DDPStage.increment P ⟨x, y⟩| := by
    apply Summable.of_norm_bounded
      (haSummable.mul_right P.valueDifferenceBound)
    intro y
    rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_eq_abs, abs_abs]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using (DDPStage.norm_increment_le P ⟨x, y⟩))
      ENNReal.toReal_nonneg
  calc
    (∑' y, a y * |DDPStage.increment P ⟨x, y⟩|) ≤
        ∑' y, a y * (b y + |P.valueX x - r|) := by
      apply Summable.tsum_le_tsum
      · intro y
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        calc
          |DDPStage.increment P ⟨x, y⟩| ≤
              |P.valueY x y - r| + |P.valueX x - r| := by
            dsimp only [DDPStage.increment]
            calc
              |P.valueY x y - P.valueX x| =
                  |(P.valueY x y - r) + (r - P.valueX x)| := by ring_nf
              _ ≤ |P.valueY x y - r| + |r - P.valueX x| := abs_add_le _ _
              _ = _ := by rw [abs_sub_comm r]
          _ ≤ b y + |P.valueX x - r| :=
            add_le_add (hactionBound y) le_rfl
      · exact hincrementSummable
      · simpa only [mul_add] using
          habSummable.add (haSummable.mul_right |P.valueX x - r|)
    _ = (∑' y, a y * b y) + |P.valueX x - r| := by
      simp_rw [mul_add]
      rw [habSummable.tsum_add (haSummable.mul_right |P.valueX x - r|)]
      rw [Summable.tsum_mul_right |P.valueX x - r| haSummable, PMF.tsum_toReal]
      simp only [one_mul]
    _ ≤ 2 * (P.valueDifferenceBound * NoReturnProbability P S A x) := by
      rw [habSum]
      linarith
    _ = 2 * P.valueDifferenceBound * NoReturnProbability P S A x := by ring

/-- Variation in one rank cell is summable, with total at most `2M`. -/
private theorem ReturnValueData.summable_state_actionVariation_and_tsum_le
    {P : DiscreteDecisionProcess} {S : DDPSemantics P} (R : ReturnValueData P S)
    (A : Set P.X) (hcommon : ∀ x, x ∈ A → ∃ r : ℝ, ∀ y : P.Y x, R.value A x y = r) :
    Summable (fun index : ℕ × {x : P.X // x ∈ A} =>
      (P.rawLawFrom P.initial {stage | (stage index.1).1 = index.2.1}).toReal *
        (∑' y : P.Y index.2.1,
          (P.choose index.2.1 y).toReal *
            |DDPStage.increment P ⟨index.2.1, y⟩|)) ∧
      (∑' index : ℕ × {x : P.X // x ∈ A},
        (P.rawLawFrom P.initial {stage | (stage index.1).1 = index.2.1}).toReal *
          (∑' y : P.Y index.2.1,
            (P.choose index.2.1 y).toReal *
              |DDPStage.increment P ⟨index.2.1, y⟩|)) ≤
        2 * P.valueDifferenceBound := by
  let lastExit : ℕ × {x : P.X // x ∈ A} → ℝ := fun index =>
    ∑' y : P.Y index.2.1,
      (P.rawLawFrom P.initial
        (P.rawLastExitAtStage A index.1 ⟨index.2.1, y⟩)).toReal
  have hlast : Summable lastExit ∧ (∑' index, lastExit index) ≤ 1 := by
    simpa only [lastExit] using P.summable_nested_rawLastExit_and_tsum_le_one P.initial A
  let variation : ℕ × {x : P.X // x ∈ A} → ℝ := fun index =>
    (P.rawLawFrom P.initial {stage | (stage index.1).1 = index.2.1}).toReal *
      (∑' y : P.Y index.2.1,
        (P.choose index.2.1 y).toReal *
          |DDPStage.increment P ⟨index.2.1, y⟩|)
  have hvariationNonneg (index : ℕ × {x : P.X // x ∈ A}) :
      0 ≤ variation index := by
    apply mul_nonneg ENNReal.toReal_nonneg
    exact tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)
  have hpoint (index : ℕ × {x : P.X // x ∈ A}) :
      variation index ≤ 2 * P.valueDifferenceBound * lastExit index := by
    calc
      variation index ≤
          (P.rawLawFrom P.initial
            {stage | (stage index.1).1 = index.2.1}).toReal *
            (2 * P.valueDifferenceBound *
              NoReturnProbability P S A index.2.1) := by
        apply mul_le_mul_of_nonneg_left
        · exact R.tsum_choose_mul_abs_increment_le A index.2.1
            (hcommon index.2.1 index.2.2)
        · exact ENNReal.toReal_nonneg
      _ = 2 * P.valueDifferenceBound *
          ((P.rawLawFrom P.initial
            {stage | (stage index.1).1 = index.2.1}).toReal *
              NoReturnProbability P S A index.2.1) := by ring
      _ = 2 * P.valueDifferenceBound * lastExit index := by
        rw [P.rawLawFrom_state_mul_noReturn_eq_tsum S P.initial A index.1 index.2.1]
  have hcoefficientNonneg : 0 ≤ 2 * P.valueDifferenceBound := by
    exact mul_nonneg (by norm_num) (le_trans zero_le_one P.valueDifferenceBound_one)
  have hright : Summable fun index => 2 * P.valueDifferenceBound * lastExit index :=
    hlast.1.mul_left (2 * P.valueDifferenceBound)
  have hvariation : Summable variation :=
    Summable.of_nonneg_of_le hvariationNonneg hpoint hright
  refine ⟨hvariation, ?_⟩
  change (∑' index, variation index) ≤ _
  calc
      (∑' index, variation index) ≤
          ∑' index, 2 * P.valueDifferenceBound * lastExit index :=
        Summable.tsum_le_tsum hpoint hvariation hright
      _ = 2 * P.valueDifferenceBound * ∑' index, lastExit index := tsum_mul_left
      _ ≤ 2 * P.valueDifferenceBound * 1 :=
        mul_le_mul_of_nonneg_left hlast.2 hcoefficientNonneg
      _ = 2 * P.valueDifferenceBound := mul_one _

/-- A time paired with a state in `A` is the subtype of time-state pairs lying over `A`. -/
private def DiscreteDecisionProcess.timeStateInSetEquiv
    (P : DiscreteDecisionProcess) (A : Set P.X) :
    ℕ × {x : P.X // x ∈ A} ≃ {index : ℕ × P.X // index.2 ∈ A} where
  toFun index := ⟨⟨index.1, index.2.1⟩, index.2.2⟩
  invFun index := ⟨index.1.1, ⟨index.1.2, index.2⟩⟩
  left_inv index := by cases index; rfl
  right_inv index := by cases index; rfl

/-- The ENNReal statewise variation accumulated in one rank cell is at most `2M`. -/
private theorem ReturnValueData.tsum_rawStateVariation_cell_le
    {P : DiscreteDecisionProcess} {S : DDPSemantics P} (R : ReturnValueData P S)
    (A : Set P.X) (hcommon : ∀ x, x ∈ A → ∃ r : ℝ, ∀ y : P.Y x, R.value A x y = r) :
    (∑' index : ℕ × {x : P.X // x ∈ A},
      P.rawStateVariation P.initial index.1 index.2.1) ≤
        ENNReal.ofReal (2 * P.valueDifferenceBound) := by
  let variation : ℕ × {x : P.X // x ∈ A} → ℝ := fun index =>
    (P.rawLawFrom P.initial {stage | (stage index.1).1 = index.2.1}).toReal *
      (∑' y : P.Y index.2.1,
        (P.choose index.2.1 y).toReal * |DDPStage.increment P ⟨index.2.1, y⟩|)
  have hreal : Summable variation ∧ (∑' index, variation index) ≤
      2 * P.valueDifferenceBound := by
    simpa only [variation] using R.summable_state_actionVariation_and_tsum_le A hcommon
  have hnonneg (index : ℕ × {x : P.X // x ∈ A}) : 0 ≤ variation index := by
    apply mul_nonneg ENNReal.toReal_nonneg
    exact tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)
  calc
    (∑' index : ℕ × {x : P.X // x ∈ A},
        P.rawStateVariation P.initial index.1 index.2.1) =
        ∑' index, ENNReal.ofReal (variation index) := by
      apply tsum_congr
      intro index
      exact P.rawStateVariation_eq_ofReal P.initial index.1 index.2.1
    _ = ENNReal.ofReal (∑' index, variation index) :=
      (ENNReal.ofReal_tsum_of_nonneg hnonneg hreal.1).symm
    _ ≤ ENNReal.ofReal (2 * P.valueDifferenceBound) :=
      ENNReal.ofReal_le_ofReal hreal.2

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
  classical
  let W : RankPartitionWitness P S R n := Classical.choice hrank.1
  let cellIndices : Fin n → Set (ℕ × P.X) := fun cell =>
    {index | index.2 ∈ W.cell cell}
  let variation : ℕ × P.X → ℝ≥0∞ := fun index =>
    P.rawStateVariation P.initial index.1 index.2
  have hunion (index : ℕ × P.X) :
      index ∈ ⋃ cell, cellIndices cell ↔ IsVaried P index.2 := by
    rw [W.valid.1.2]
    simp only [mem_iUnion, mem_setOf_eq, cellIndices]
  have hzero (index : ℕ × P.X) (hindex : index ∉ ⋃ cell, cellIndices cell) :
      variation index = 0 := by
    have hnotVaried : ¬ IsVaried P index.2 := by
      rwa [← hunion index]
    have hincrement (y : P.Y index.2) : DDPStage.increment P ⟨index.2, y⟩ = 0 := by
      rw [DDPStage.increment]
      exact sub_eq_zero.mpr (not_ne_iff.mp (not_exists.mp hnotVaried y))
    change P.rawStateVariation P.initial index.1 index.2 = 0
    rw [DiscreteDecisionProcess.rawStateVariation]
    simp_rw [hincrement]
    simp
  have hrestrict : (∑' index, variation index) =
      ∑' index : {
        index : ℕ × P.X // index ∈ ⋃ cell, cellIndices cell}, variation index.1 := by
    calc
      (∑' index, variation index) =
          ∑' index, (⋃ cell, cellIndices cell).indicator variation index := by
        apply tsum_congr
        intro index
        by_cases hindex : index ∈ ⋃ cell, cellIndices cell
        · simp [hindex]
        · simp [hindex, hzero index hindex]
      _ = _ := (tsum_subtype (⋃ cell, cellIndices cell) variation).symm
  have hcell (cell : Fin n) :
      (∑' index : cellIndices cell, variation index.1) ≤
        ENNReal.ofReal (2 * P.valueDifferenceBound) := by
    change (∑' index : {index : ℕ × P.X // index.2 ∈ W.cell cell},
      P.rawStateVariation P.initial index.1.1 index.1.2) ≤ _
    rw [← (P.timeStateInSetEquiv (W.cell cell)).tsum_eq]
    exact R.tsum_rawStateVariation_cell_le (W.cell cell) (W.valid.2 cell)
  rw [ExpectedDDPVariation.eq_tsum_rawStateVariation P S]
  change (∑' index, variation index) ≤ _
  calc
    (∑' index, variation index) =
        ∑' index : {
          index : ℕ × P.X // index ∈ ⋃ cell, cellIndices cell}, variation index.1 :=
      hrestrict
    _ ≤ ∑ cell : Fin n, ∑' index : cellIndices cell, variation index.1 :=
      ENNReal.tsum_iUnion_le variation cellIndices
    _ ≤ ∑ _cell : Fin n, ENNReal.ofReal (2 * P.valueDifferenceBound) := by
      exact Finset.sum_le_sum fun cell _ => hcell cell
    _ = ENNReal.ofReal (2 * n * P.valueDifferenceBound) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show 2 * (n : ℝ) * P.valueDifferenceBound =
          (n : ℝ) * (2 * P.valueDifferenceBound) by ring]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

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

/-- Use the discrete sigma algebra on the finite state space in the path-law construction. -/
private instance markovStateMeasurableSpace (P : MarkovChain) :
    MeasurableSpace P.State := ⊤

/-- An infinite state path; paths using zero-probability transitions have induced measure zero. -/
structure MarkovPath (P : MarkovChain) where
  state : ℕ → P.State

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

/-- The transition PMF at time `n`, viewed as an Ionescu--Tulcea kernel. -/
private def MarkovChain.stepKernel (P : MarkovChain) (n : ℕ) :
    Kernel (∀ _ : Finset.Iic n, P.State) P.State where
  toFun x := (P.transition n (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure
  measurable' := Measurable.of_discrete

private instance MarkovChain.isMarkovKernel_stepKernel (P : MarkovChain) (n : ℕ) :
    IsMarkovKernel (P.stepKernel n) :=
  ⟨fun _ => PMF.toMeasure.isProbabilityMeasure _⟩

/-- The point-mass initial distribution of the Markov chain. -/
private def MarkovChain.initialMeasure (P : MarkovChain) : Measure P.State :=
  (PMF.pure P.initial).toMeasure

private instance MarkovChain.isProbabilityMeasure_initialMeasure (P : MarkovChain) :
    IsProbabilityMeasure P.initialMeasure :=
  PMF.toMeasure.isProbabilityMeasure _

/-- The raw trajectory law supplied by the Ionescu--Tulcea theorem. -/
private def MarkovChain.rawLaw (P : MarkovChain) : Measure (ℕ → P.State) :=
  Kernel.trajMeasure (X := fun _ : ℕ => P.State) P.initialMeasure P.stepKernel

private instance MarkovChain.isProbabilityMeasure_rawLaw (P : MarkovChain) :
    IsProbabilityMeasure P.rawLaw := by
  unfold MarkovChain.rawLaw
  infer_instance

/-- The time-zero marginal of the raw law is the prescribed initial point mass. -/
private theorem MarkovChain.map_prefix_zero_rawLaw (P : MarkovChain) :
    P.rawLaw.map (Preorder.frestrictLe (π := fun _ : ℕ => P.State) 0) =
      P.initialMeasure.map
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => P.State)).symm := by
  unfold MarkovChain.rawLaw Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop)]
  rw [Kernel.traj_map_frestrictLe, Kernel.partialTraj_self]
  rw [Measure.id_comp]

/-- Reindex a `Fin (k+1)` string as an Ionescu--Tulcea prefix through time `k`. -/
private def MarkovChain.prefixOfFin (P : MarkovChain) {k : ℕ}
    (x : Fin (k + 1) → P.State) : ∀ _ : Finset.Iic k, P.State :=
  fun i => x ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩

/-- A finite coordinate cylinder is the preimage of its exact finite prefix. -/
private theorem MarkovChain.rawCylinder_eq_prefixPreimage (P : MarkovChain) (k : ℕ)
    (x : Fin (k + 1) → P.State) :
    {w | ∀ i : Fin (k + 1), w i = x i} =
      Preorder.frestrictLe (π := fun _ : ℕ => P.State) k ⁻¹' {P.prefixOfFin x} := by
  ext w
  simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff]
  constructor
  · intro h
    funext i
    exact h ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩
  · intro h i
    have hi := congrFun h ⟨i.1, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp i.2)⟩
    exact hi

/-- Raw finite coordinate cylinders are measurable in the product sigma algebra. -/
private theorem MarkovChain.measurableSet_rawCylinder (P : MarkovChain) (k : ℕ)
    (x : Fin (k + 1) → P.State) :
    MeasurableSet {w : ℕ → P.State | ∀ i : Fin (k + 1), w i = x i} := by
  rw [P.rawCylinder_eq_prefixPreimage k x]
  exact (measurableSet_singleton (P.prefixOfFin x)).preimage
    (Preorder.measurable_frestrictLe (X := fun _ : ℕ => P.State) k)

/-- The raw trajectory law has the expected finite-dimensional cylinder products. -/
private theorem MarkovChain.rawLaw_cylinder (P : MarkovChain) : ∀ (k : ℕ)
    (x : Fin (k + 1) → P.State), x 0 = P.initial →
    P.rawLaw {w : ℕ → P.State | ∀ i : Fin (k + 1), w i = x i} =
      ∏ i : Fin k, P.transition i (x i.castSucc) (x i.succ) := by
  intro k
  induction k with
  | zero =>
      intro x hx
      rw [P.rawCylinder_eq_prefixPreimage]
      rw [← Measure.map_apply
        (Preorder.measurable_frestrictLe (X := fun _ : ℕ => P.State) 0)
        (measurableSet_singleton (P.prefixOfFin x))]
      rw [P.map_prefix_zero_rawLaw]
      rw [Measure.map_apply (MeasurableEquiv.measurable _)
        (measurableSet_singleton (P.prefixOfFin x))]
      have hevent :
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => P.State)).symm ⁻¹'
              {P.prefixOfFin x} = {P.initial} := by
        ext z
        simp only [mem_preimage, mem_singleton_iff]
        have hprefix : P.prefixOfFin x (default : Finset.Iic 0) = x 0 := by
          apply congrArg x
          apply Fin.ext
          exact Nat.eq_zero_of_le_zero
            (Finset.mem_Iic.mp (default : Finset.Iic 0).2)
        constructor
        · intro hz
          have hcoord := congrFun hz (default : Finset.Iic 0)
          rw [MeasurableEquiv.piUnique_symm_apply] at hcoord
          change z = P.prefixOfFin x default at hcoord
          rw [hprefix] at hcoord
          exact hcoord.trans hx
        · intro hz
          subst z
          funext i
          have hi : i = (default : Finset.Iic 0) := Subsingleton.elim _ _
          subst i
          change P.initial = P.prefixOfFin x default
          rw [hprefix, hx]
      rw [hevent, MarkovChain.initialMeasure,
        PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
      simp
  | succ k ih =>
      intro x hx
      let old : Fin (k + 1) → P.State := Fin.init x
      let pref := P.prefixOfFin old
      let next := x (Fin.last (k + 1))
      have hrec := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ : ℕ => P.State) (κ := P.stepKernel)
        (μ₀ := P.initialMeasure) (a := k)
      have hpre :
          (fun w : ℕ → P.State =>
            (Preorder.frestrictLe (π := fun _ : ℕ => P.State) k w, w (k + 1))) ⁻¹'
              ({pref} ×ˢ {next}) =
            {w | ∀ i : Fin (k + 2), w i = x i} := by
        ext w
        simp only [mem_preimage, mem_prod, mem_singleton_iff, mem_setOf_eq]
        constructor
        · rintro ⟨hpref, hnext⟩ i
          by_cases hi : i.1 ≤ k
          · have hcoord := congrFun hpref ⟨i.1, Finset.mem_Iic.mpr hi⟩
            change w i.1 = old ⟨i.1, Nat.lt_succ_of_le hi⟩ at hcoord
            rw [hcoord]
            apply congrArg x
            apply Fin.ext
            rfl
          · have hii : i = Fin.last (k + 1) := by
              apply Fin.ext
              simp only [Fin.val_last]
              omega
            subst i
            exact hnext
        · intro hw
          constructor
          · funext i
            have hi : i.1 ≤ k := Finset.mem_Iic.mp i.2
            change w i.1 = old ⟨i.1, Nat.lt_succ_of_le hi⟩
            rw [hw ⟨i.1, by omega⟩]
            apply congrArg x
            apply Fin.ext
            rfl
          · exact hw (Fin.last (k + 1))
      have hleft :
          (P.rawLaw.map (Preorder.frestrictLe (π := fun _ : ℕ => P.State) k) ⊗ₘ
              P.stepKernel k) ({pref} ×ˢ {next}) =
            P.transition k (old (Fin.last k)) next *
              P.rawLaw {w | ∀ i : Fin (k + 1), w i = old i} := by
        rw [Measure.compProd_apply_prod (measurableSet_singleton pref)
          (measurableSet_singleton next)]
        rw [setLIntegral_congr_fun (measurableSet_singleton pref) (g := fun _ =>
          P.transition k (old (Fin.last k)) next)]
        · rw [MeasureTheory.setLIntegral_const]
          rw [Measure.map_apply
            (Preorder.measurable_frestrictLe (X := fun _ : ℕ => P.State) k)
            (measurableSet_singleton pref)]
          rw [← P.rawCylinder_eq_prefixPreimage k old]
        · intro a ha
          simp only [mem_singleton_iff] at ha
          subst a
          change (P.transition k
              (pref ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure {next} = _
          rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
          congr 2
      have hright :
          P.rawLaw.map (fun w : ℕ → P.State =>
            (Preorder.frestrictLe (π := fun _ : ℕ => P.State) k w, w (k + 1)))
              ({pref} ×ˢ {next}) =
            P.rawLaw {w | ∀ i : Fin (k + 2), w i = x i} := by
        rw [Measure.map_apply]
        · rw [hpre]
        · fun_prop
        · exact (measurableSet_singleton pref).prod (measurableSet_singleton next)
      change
        (P.rawLaw.map (Preorder.frestrictLe (π := fun _ : ℕ => P.State) k) ⊗ₘ
            P.stepKernel k) =
          P.rawLaw.map (fun w : ℕ → P.State =>
            (Preorder.frestrictLe (π := fun _ : ℕ => P.State) k w, w (k + 1))) at hrec
      rw [← hright, ← hrec, hleft, ih old]
      · rw [Fin.prod_univ_castSucc]
        have hlast : old (Fin.last k) = x (Fin.last k).castSucc := by
          rfl
        have hproduct :
            (∏ i : Fin k, P.transition i (old i.castSucc) (old i.succ)) =
              ∏ i : Fin k,
                P.transition i (x i.castSucc.castSucc) (x i.castSucc.succ) := by
          apply Finset.prod_congr rfl
          intro i _
          congr 2
        have hnext : next = x (Fin.last k).succ := by
          apply congrArg x
          apply Fin.ext
          rfl
        rw [hlast, hproduct, hnext]
        simp only [Fin.val_castSucc]
        rw [show (Fin.last k : ℕ) = k by rfl]
        rw [mul_comm]
      · change x 0 = P.initial
        exact hx

/-- Forget that a raw state sequence was constructed before it was bundled as a path. -/
private def MarkovPath.ofRaw (P : MarkovChain) (w : ℕ → P.State) : MarkovPath P :=
  ⟨w⟩

private theorem MarkovPath.measurable_ofRaw (P : MarkovChain) :
    Measurable (MarkovPath.ofRaw P) := by
  apply measurable_generateFrom
  intro U hU
  rcases hU with ⟨k, x, rfl⟩
  simpa only [MarkovPath.ofRaw, preimage_setOf_eq] using
    P.measurableSet_rawCylinder k x

/-- Every displayed Markov cylinder is measurable in the generated path sigma algebra. -/
private theorem MarkovPath.measurableSet_cylinder (P : MarkovChain) (k : ℕ)
    (x : Fin (k + 1) → P.State) :
    MeasurableSet {p : MarkovPath P | ∀ i : Fin (k + 1), p.state i = x i} :=
  MeasurableSpace.measurableSet_generateFrom ⟨k, x, rfl⟩

/-- Ionescu--Tulcea extension supplies the Markov path law with these cylinder probabilities. -/
theorem markovSemantics_exists (P : MarkovChain) : Nonempty (MarkovSemantics P) := by
  let law : Measure (MarkovPath P) := P.rawLaw.map (MarkovPath.ofRaw P)
  haveI : IsProbabilityMeasure law :=
    Measure.isProbabilityMeasure_map (MarkovPath.measurable_ofRaw P).aemeasurable
  refine ⟨{
    law := law
    probability := inferInstance
    cylinder := ?_ }⟩
  intro k x hx
  dsimp only [law]
  rw [Measure.map_apply (MarkovPath.measurable_ofRaw P)
    (MarkovPath.measurableSet_cylinder P k x)]
  simpa only [MarkovPath.ofRaw, preimage_setOf_eq] using P.rawLaw_cylinder k x hx

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

/-- Replace a quitting game's reward table while keeping its player type. -/
abbrev QuittingGame.withReward (G : QuittingGame)
    (reward : {A : Finset G.Player // A.Nonempty} → Payoff G.Player) : QuittingGame where
  Player := G.Player
  reward := reward

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

/-- If one player quits surely, somebody quits with probability one. -/
theorem quitProbability_replace_one (G : QuittingGame) (p : QuitRow G)
    (n : G.Player) : QuitProbability G (p.replace G n 1) = 1 := by
  simp only [QuitProbability]
  have hn : n ∈ Finset.univ := Finset.mem_univ n
  have hprod : (∏ i, (1 - ((p.replace G n 1) i : ℝ))) = 0 := by
    apply Finset.prod_eq_zero hn
    simp [QuitRow.replace]
  rw [hprod]
  ring

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

/-- The reward contribution of a quitting row, excluding continuation. -/
private def quittingRewardPart (G : QuittingGame) (p : QuitRow G)
    (n : G.Player) : ℝ :=
  ∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
    CoalitionProbability G p A * G.reward ⟨A, hA⟩ n else 0

/-- Decreasing a player's terminal rewards decreases each row's reward contribution. -/
private theorem quittingRewardPart_mono_reward (G : QuittingGame)
    (reward' : {A : Finset G.Player // A.Nonempty} → Payoff G.Player)
    (p : QuitRow G) (n : G.Player) (hreward : ∀ A, reward' A n ≤ G.reward A n) :
    quittingRewardPart (G.withReward reward') p n ≤ quittingRewardPart G p n := by
  classical
  apply Finset.sum_le_sum
  intro A _hA
  split_ifs with hnonempty
  · have hprob : 0 ≤ CoalitionProbability G p A := by
      simp only [CoalitionProbability]
      exact mul_nonneg
        (Finset.prod_nonneg fun i _ => (p i).property.1)
        (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (p i).property.2)
    exact mul_le_mul_of_nonneg_left (hreward ⟨A, hnonempty⟩) hprob
  · exact le_rfl

/-- The reward contribution is affine in any one player's quitting probability. -/
private theorem quittingRewardPart_replace_affine (G : QuittingGame) (p : QuitRow G)
    (j : G.Player) (q : Set.Icc (0 : ℝ) 1) (n : G.Player) :
    quittingRewardPart G (p.replace G j q) n =
      (q : ℝ) * quittingRewardPart G (p.replace G j 1) n +
        (1 - (q : ℝ)) * quittingRewardPart G (p.replace G j 0) n := by
  classical
  simp only [quittingRewardPart]
  calc
    _ = ∑ A ∈ Finset.univ.powerset,
        ((q : ℝ) * (if hA : A.Nonempty then
            CoalitionProbability G (p.replace G j 1) A * G.reward ⟨A, hA⟩ n
          else 0) +
        (1 - (q : ℝ)) * (if hA : A.Nonempty then
            CoalitionProbability G (p.replace G j 0) A * G.reward ⟨A, hA⟩ n
          else 0)) := by
      apply Finset.sum_congr rfl
      intro A hA
      split_ifs
      · rw [coalitionProbability_replace_affine]
        ring
      · ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The all-continue row gives every nonempty coalition probability zero. -/
theorem coalitionProbability_zero_of_nonempty (G : QuittingGame)
    (A : Finset G.Player) (hA : A.Nonempty) :
    CoalitionProbability G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) A = 0 := by
  classical
  simp only [CoalitionProbability]
  rcases hA with ⟨n, hn⟩
  apply mul_eq_zero_of_left
  apply Finset.prod_eq_zero hn
  norm_num

/-- The all-continue row has no immediate reward contribution. -/
private theorem quittingRewardPart_allContinue (G : QuittingGame) (n : G.Player) :
    quittingRewardPart G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) n = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro A hA
  split_ifs with hnonempty
  · rw [coalitionProbability_zero_of_nonempty G A hnonempty]
    simp
  · rfl

/-- The pure row in which exactly player `j` quits. -/
def SoloQuitRow (G : QuittingGame) (j : G.Player) : QuitRow G := by
  classical
  exact fun k => if k = j then 1 else 0

/-- The designated singleton has probability one under its pure solo-quit row. -/
theorem coalitionProbability_soloQuitRow_singleton
    (G : QuittingGame) (j : G.Player) :
    CoalitionProbability G (SoloQuitRow G j) {j} = 1 := by
  classical
  simp only [CoalitionProbability, SoloQuitRow]
  have hfirst :
      (∏ n ∈ ({j} : Finset G.Player),
        (((if n = j then (1 : Set.Icc (0 : ℝ) 1) else 0) :
          Set.Icc (0 : ℝ) 1) : ℝ)) = 1 := by
    simp
  rw [hfirst, one_mul]
  apply Finset.prod_eq_one
  intro n hn
  have hnj : n ≠ j := by simpa using hn
  simp [hnj]

/-- Every other coalition has probability zero under a pure solo-quit row. -/
theorem coalitionProbability_soloQuitRow_other
    (G : QuittingGame) (j : G.Player) (A : Finset G.Player) (hA : A ≠ {j}) :
    CoalitionProbability G (SoloQuitRow G j) A = 0 := by
  classical
  simp only [CoalitionProbability, SoloQuitRow]
  by_cases hjA : j ∈ A
  · have hexists : ∃ k ∈ A, k ≠ j := by
      by_contra hnone
      push Not at hnone
      apply hA
      apply Finset.Subset.antisymm
      · intro k hk
        exact Finset.mem_singleton.mpr (hnone k hk)
      · exact Finset.singleton_subset_iff.mpr hjA
    rcases hexists with ⟨k, hkA, hkj⟩
    apply mul_eq_zero_of_left
    apply Finset.prod_eq_zero hkA
    simp [hkj]
  · apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (show j ∈ Finset.univ.filter (fun n => n ∉ A) by simp [hjA])
    simp

/-- A pure solo-quit row contributes the corresponding singleton reward. -/
private theorem quittingRewardPart_soloQuitRow (G : QuittingGame)
    (j n : G.Player) :
    quittingRewardPart G (SoloQuitRow G j) n =
      G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n := by
  classical
  rw [quittingRewardPart]
  rw [Finset.sum_eq_single_of_mem {j} (by simp)]
  · simp [coalitionProbability_soloQuitRow_singleton]
  · intro A hA hne
    split_ifs with hnonempty
    · rw [coalitionProbability_soloQuitRow_other G j A hne]
      simp
    · rfl

/-- Replacing one coordinate of the all-continue row by one gives the solo-quit row. -/
theorem QuitRow.zero_replace_one (G : QuittingGame) (j : G.Player) :
    QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j 1 = SoloQuitRow G j := by
  funext k
  by_cases hkj : k = j
  · subst k
    simp [QuitRow.replace, SoloQuitRow]
  · simp [QuitRow.replace, SoloQuitRow, hkj]

/-- The total mass of the nonempty exact-quitter coalitions is the quitting probability. -/
private theorem nonemptyCoalitionMass_eq_quitProbability (G : QuittingGame)
    (p : QuitRow G) :
    (∑ A ∈ Finset.univ.powerset,
        if _hA : A.Nonempty then CoalitionProbability G p A else 0) =
      QuitProbability G p := by
  classical
  have hsum : ∑ A ∈ Finset.univ.powerset, CoalitionProbability G p A = 1 := by
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
  have hempty : CoalitionProbability G p ∅ = 1 - QuitProbability G p := by
    simp [CoalitionProbability, QuitProbability]
  calc
    ∑ A ∈ Finset.univ.powerset,
        (if A.Nonempty then CoalitionProbability G p A else 0) =
        (∑ A ∈ Finset.univ.powerset, CoalitionProbability G p A) -
          CoalitionProbability G p ∅ := by
      rw [← Finset.sum_filter]
      have hfilter : Finset.univ.powerset.filter (fun A => A.Nonempty) =
          Finset.univ.powerset.erase (∅ : Finset G.Player) := by
        ext A
        simp [Finset.nonempty_iff_ne_empty]
      rw [hfilter]
      have hdecomp := Finset.sum_erase_add Finset.univ.powerset
        (fun A => CoalitionProbability G p A) (by simp : (∅ : Finset G.Player) ∈
          Finset.univ.powerset)
      linarith
    _ = QuitProbability G p := by rw [hsum, hempty]; ring_nf

/-- The reward part is bounded by the quitting mass times a uniform payoff bound. -/
private theorem abs_quittingRewardPart_le (G : QuittingGame) (p : QuitRow G)
    (n : G.Player) {M : ℝ} (hbound : ∀ A, |G.reward A n| ≤ M) :
    |quittingRewardPart G p n| ≤ M * QuitProbability G p := by
  classical
  calc
    |quittingRewardPart G p n| ≤
        ∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
          |CoalitionProbability G p A * G.reward ⟨A, hA⟩ n| else 0 := by
      dsimp only [quittingRewardPart]
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        apply Finset.sum_congr rfl
        intro A hA
        split_ifs <;> simp)
    _ ≤ ∑ A ∈ Finset.univ.powerset, if A.Nonempty then
          CoalitionProbability G p A * M else 0 := by
      apply Finset.sum_le_sum
      intro A hA
      split_ifs with hnonempty
      · rw [abs_mul]
        have hprob : 0 ≤ CoalitionProbability G p A := by
          simp only [CoalitionProbability]
          exact mul_nonneg
            (Finset.prod_nonneg fun i _ => (p i).property.1)
            (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (p i).property.2)
        rw [abs_of_nonneg hprob]
        exact mul_le_mul_of_nonneg_left (hbound ⟨A, hnonempty⟩) hprob
      · exact le_rfl
    _ = M * QuitProbability G p := by
      rw [← nonemptyCoalitionMass_eq_quitProbability G p]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      split_ifs <;> ring_nf

/-- Probability that a quitting profile survives the first `k` stages after `i`. -/
private def tailSurvival (G : QuittingGame) (p : QuitProfile G)
    (i k : ℕ) : ℝ :=
  Finset.prod (Finset.range k) fun j => 1 - QuitProbability G (p (i + j))

/-- Peeling off the first survival factor agrees with shifting the tail start. -/
private theorem tailSurvival_succ (G : QuittingGame) (p : QuitProfile G)
    (i k : ℕ) :
    tailSurvival G p i (k + 1) =
      (1 - QuitProbability G (p i)) * tailSurvival G p (i + 1) k := by
  induction k with
  | zero => simp [tailSurvival]
  | succ k ih =>
      simp only [tailSurvival, Finset.prod_range_succ] at ih ⊢
      rw [ih]
      rw [show i + (k + 1) = (i + 1) + k by omega]
      ring_nf

/-- The absorption masses of a quitting tail form a summable sequence. -/
private theorem summable_tailSurvival_mul_quitProbability (G : QuittingGame)
    (p : QuitProfile G) (i : ℕ) :
    Summable fun k => tailSurvival G p i k * QuitProbability G (p (i + k)) := by
  let q : ℕ → ℝ := fun k => QuitProbability G (p (i + k))
  let survival : ℕ → ℝ := fun k => tailSurvival G p i k
  have hq : ∀ k, q k ∈ Set.Icc (0 : ℝ) 1 := fun k => quitProbability_mem_Icc G _
  have hsurvivalNonnegative : ∀ k, 0 ≤ survival k := by
    intro k
    dsimp [survival, tailSurvival]
    exact Finset.prod_nonneg fun j _ => sub_nonneg.mpr (hq j).2
  have hsurvivalSucc : ∀ k, survival (k + 1) = survival k * (1 - q k) := by
    intro k
    simp [survival, tailSurvival, q, Finset.prod_range_succ]
  have htelescoping : ∀ n, ∑ k ∈ Finset.range n, survival k * q k = 1 - survival n := by
    intro n
    induction n with
    | zero => simp [survival, tailSurvival]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, hsurvivalSucc]
        ring_nf
  have hsummable : Summable fun k => survival k * q k := by
    apply summable_of_sum_range_le (c := 1)
    · intro k
      exact mul_nonneg (hsurvivalNonnegative k) (hq k).1
    · intro n
      rw [htelescoping]
      linarith [hsurvivalNonnegative n]
  simpa only [survival, q] using hsummable

/-- Finite absorption masses telescope against survival. -/
private theorem sum_range_tailSurvival_mul_quitProbability (G : QuittingGame)
    (p : QuitProfile G) (i m : ℕ) :
    (∑ k ∈ Finset.range m,
      tailSurvival G p i k * QuitProbability G (p (i + k))) =
        1 - tailSurvival G p i m := by
  induction m with
  | zero => simp [tailSurvival]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [tailSurvival, Finset.prod_range_succ]
      ring_nf

/-- Total absorption mass is at most one. -/
private theorem tsum_tailSurvival_mul_quitProbability_le_one (G : QuittingGame)
    (p : QuitProfile G) (i : ℕ) :
    (∑' k, tailSurvival G p i k * QuitProbability G (p (i + k))) ≤ 1 := by
  have hsummable := summable_tailSurvival_mul_quitProbability G p i
  apply le_of_tendsto hsummable.hasSum.tendsto_sum_nat
  exact Filter.Eventually.of_forall fun m => by
    rw [sum_range_tailSurvival_mul_quitProbability]
    have hsurvival : 0 ≤ tailSurvival G p i m := by
      exact Finset.prod_nonneg fun j _ =>
        sub_nonneg.mpr (quitProbability_mem_Icc G _).2
    linarith

/-- If finite survival tends to zero, total absorption mass is one. -/
private theorem tsum_tailSurvival_mul_quitProbability_eq_one (G : QuittingGame)
    (p : QuitProfile G) (i : ℕ)
    (hvanish : Tendsto (tailSurvival G p i) atTop (nhds 0)) :
    (∑' k, tailSurvival G p i k * QuitProbability G (p (i + k))) = 1 := by
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · simpa only [sum_range_tailSurvival_mul_quitProbability, sub_zero] using
      tendsto_const_nhds.sub hvanish
  · intro k
    exact mul_nonneg
      (Finset.prod_nonneg fun j _ => sub_nonneg.mpr (quitProbability_mem_Icc G _).2)
      (quitProbability_mem_Icc G _).1

/-- Every quitting tail payoff series is absolutely summable. -/
private theorem summable_quitTailPayoff (G : QuittingGame) (p : QuitProfile G)
    (i : ℕ) (n : G.Player) :
    Summable fun k => tailSurvival G p i k * quittingRewardPart G (p (i + k)) n := by
  obtain ⟨M, hM⟩ := exists_quittingPayoffDifferenceBound G
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.1
  have hmass := summable_tailSurvival_mul_quitProbability G p i
  apply (hmass.mul_left M).of_norm_bounded
  intro k
  have hsurvival : 0 ≤ tailSurvival G p i k := by
    dsimp [tailSurvival]
    exact Finset.prod_nonneg fun j _ =>
      sub_nonneg.mpr (quitProbability_mem_Icc G _).2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsurvival]
  calc
    tailSurvival G p i k * |quittingRewardPart G (p (i + k)) n| ≤
        tailSurvival G p i k * (M * QuitProbability G (p (i + k))) :=
      mul_le_mul_of_nonneg_left
        (abs_quittingRewardPart_le G _ n (fun A => le_of_lt (hM.2.2 A n))) hsurvival
    _ = M * (tailSurvival G p i k * QuitProbability G (p (i + k))) := by ring_nf

/-- Pointwise decreasing one player's terminal rewards decreases that player's payoff for
every fixed quitting profile. -/
theorem quitPayoff_mono_reward (G : QuittingGame)
    (reward' : {A : Finset G.Player // A.Nonempty} → Payoff G.Player)
    (p : QuitProfile G) (n : G.Player) (hreward : ∀ A, reward' A n ≤ G.reward A n) :
    QuitPayoff (G.withReward reward') p n ≤ QuitPayoff G p n := by
  have hleft := summable_quitTailPayoff (G.withReward reward') p 0 n
  have hright := summable_quitTailPayoff G p 0 n
  change (∑' k, tailSurvival G p 0 k *
      quittingRewardPart (G.withReward reward') (p (0 + k)) n) ≤
    ∑' k, tailSurvival G p 0 k * quittingRewardPart G (p (0 + k)) n
  apply hleft.tsum_le_tsum _ hright
  intro k
  exact mul_le_mul_of_nonneg_left
    (quittingRewardPart_mono_reward G reward' (p (0 + k)) n hreward)
    (Finset.prod_nonneg fun j _ =>
      sub_nonneg.mpr (quitProbability_mem_Icc G _).2)

/-- A row replacement by its current coordinate leaves the row unchanged. -/
theorem QuitRow.replace_self (G : QuittingGame) (p : QuitRow G)
    (n : G.Player) : p.replace G n (p n) = p := by
  funext j
  by_cases hj : j = n
  · subst j
    simp [QuitRow.replace]
  · simp [QuitRow.replace, hj]

/-- Replacements at distinct coordinates commute. -/
theorem QuitRow.replace_comm (G : QuittingGame) (p : QuitRow G)
    {i j : G.Player} (hij : i ≠ j) (qi qj : Set.Icc (0 : ℝ) 1) :
    (p.replace G i qi).replace G j qj = (p.replace G j qj).replace G i qi := by
  funext n
  by_cases hni : n = i
  · subst n
    simp [QuitRow.replace, hij]
  · by_cases hnj : n = j
    · subst n
      simp [QuitRow.replace, hni]
    · simp [QuitRow.replace, hni, hnj]

/-- Survival is affine in a replaced quitting coordinate. -/
private theorem one_sub_quitProbability_replace (G : QuittingGame) (p : QuitRow G)
    (j : G.Player) (q : Set.Icc (0 : ℝ) 1) :
    1 - QuitProbability G (p.replace G j q) =
      (1 - (q : ℝ)) * (1 - QuitProbability G (p.replace G j 0)) := by
  have hempty (r : QuitRow G) :
      1 - QuitProbability G r = CoalitionProbability G r ∅ := by
    simp [QuitProbability, CoalitionProbability]
  rw [hempty, coalitionProbability_replace_affine, ← hempty, ← hempty]
  rw [quitProbability_replace_one]
  ring_nf

/-- The base row used in Lemma 3: only `i` quits, with fixed probability `a`. -/
private def rareQuitRow (G : QuittingGame) (i : G.Player)
    (a : Set.Icc (0 : ℝ) 1) : QuitRow G :=
  QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) i a

/-- The reward contribution of a rare solo quitter is its probability times its reward. -/
private theorem quittingRewardPart_rareQuitRow (G : QuittingGame)
    (i n : G.Player) (a : Set.Icc (0 : ℝ) 1) :
    quittingRewardPart G (rareQuitRow G i a) n =
      (a : ℝ) * G.reward ⟨{i}, Finset.singleton_nonempty i⟩ n := by
  rw [rareQuitRow, quittingRewardPart_replace_affine]
  rw [QuitRow.zero_replace_one, quittingRewardPart_soloQuitRow]
  have hzero : QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) i 0 =
      fun _ => (0 : Set.Icc (0 : ℝ) 1) := QuitRow.replace_self G _ i
  rw [hzero, quittingRewardPart_allContinue]
  ring_nf

/-- The survival probability of a rare solo-quitting row is `1-a`. -/
private theorem one_sub_quitProbability_rareQuitRow (G : QuittingGame)
    (i : G.Player) (a : Set.Icc (0 : ℝ) 1) :
    1 - QuitProbability G (rareQuitRow G i a) = 1 - (a : ℝ) := by
  rw [rareQuitRow, one_sub_quitProbability_replace]
  have hzero : QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) i 0 =
      fun _ => (0 : Set.Icc (0 : ℝ) 1) := QuitRow.replace_self G _ i
  rw [hzero]
  simp [QuitProbability]

/-- A unilateral row over all-continue play contributes its solo payoff. -/
private theorem quittingRewardPart_allContinue_replace (G : QuittingGame)
    (j : G.Player) (q : Set.Icc (0 : ℝ) 1) :
    quittingRewardPart G
        (QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j q) j =
      (q : ℝ) * SoloPayoff G j := by
  rw [quittingRewardPart_replace_affine, QuitRow.zero_replace_one]
  rw [quittingRewardPart_soloQuitRow]
  have hzero : QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j 0 =
      fun _ => (0 : Set.Icc (0 : ℝ) 1) := QuitRow.replace_self G _ j
  rw [hzero, quittingRewardPart_allContinue]
  simp [SoloPayoff]

/-- A unilateral row over all-continue play quits with the deviator's probability. -/
private theorem quitProbability_allContinue_replace (G : QuittingGame)
    (j : G.Player) (q : Set.Icc (0 : ℝ) 1) :
    QuitProbability G
      (QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j q) = q := by
  have hsurvival := one_sub_quitProbability_replace G
    (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j q
  have hzero : QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j 0 =
      fun _ => (0 : Set.Icc (0 : ℝ) 1) := QuitRow.replace_self G _ j
  rw [hzero] at hsurvival
  simp [QuitProbability] at hsurvival
  simp only [QuitProbability]
  rw [hsurvival]
  ring_nf

/-- If every row's reward is bounded by `C` times its quitting mass, so is the tail payoff. -/
private theorem quitPayoff_le_of_rewardPart_le (G : QuittingGame) (p : QuitProfile G)
    (n : G.Player) (C : ℝ)
    (hreward : ∀ t, quittingRewardPart G (p t) n ≤ C * QuitProbability G (p t))
    (hmass : (∑' t, tailSurvival G p 0 t * QuitProbability G (p t)) = 1) :
    QuitPayoff G p n ≤ C := by
  have hleft := summable_quitTailPayoff G p 0 n
  have habsorption := summable_tailSurvival_mul_quitProbability G p 0
  have hright : Summable fun t =>
      C * (tailSurvival G p 0 t * QuitProbability G (p (0 + t))) :=
    habsorption.mul_left C
  change (∑' t, tailSurvival G p 0 t * quittingRewardPart G (p (0 + t)) n) ≤ C
  calc
    _ ≤ ∑' t, C * (tailSurvival G p 0 t * QuitProbability G (p (0 + t))) := by
      apply hleft.tsum_le_tsum _ hright
      intro t
      have hsurvival : 0 ≤ tailSurvival G p 0 t :=
        Finset.prod_nonneg fun l _ => sub_nonneg.mpr (quitProbability_mem_Icc G _).2
      calc
        tailSurvival G p 0 t * quittingRewardPart G (p (0 + t)) n ≤
            tailSurvival G p 0 t * (C * QuitProbability G (p (0 + t))) :=
          mul_le_mul_of_nonneg_left (by simpa using hreward t) hsurvival
        _ = C * (tailSurvival G p 0 t * QuitProbability G (p (0 + t))) := by ring_nf
    _ = C := by
      rw [tsum_mul_left, show (∑' t,
        tailSurvival G p 0 t * QuitProbability G (p (0 + t))) = 1 by simpa using hmass]
      ring_nf

/-- The same bound holds with possible nonabsorption when `C` is nonnegative. -/
private theorem quitPayoff_le_of_nonnegative_rewardPart_le (G : QuittingGame)
    (p : QuitProfile G) (n : G.Player) (C : ℝ) (hC : 0 ≤ C)
    (hreward : ∀ t, quittingRewardPart G (p t) n ≤ C * QuitProbability G (p t)) :
    QuitPayoff G p n ≤ C := by
  have hleft := summable_quitTailPayoff G p 0 n
  have habsorption := summable_tailSurvival_mul_quitProbability G p 0
  have hright : Summable fun t =>
      C * (tailSurvival G p 0 t * QuitProbability G (p (0 + t))) :=
    habsorption.mul_left C
  change (∑' t, tailSurvival G p 0 t * quittingRewardPart G (p (0 + t)) n) ≤ C
  calc
    _ ≤ ∑' t, C * (tailSurvival G p 0 t * QuitProbability G (p (0 + t))) := by
      apply hleft.tsum_le_tsum _ hright
      intro t
      have hsurvival : 0 ≤ tailSurvival G p 0 t :=
        Finset.prod_nonneg fun l _ => sub_nonneg.mpr (quitProbability_mem_Icc G _).2
      calc
        tailSurvival G p 0 t * quittingRewardPart G (p (0 + t)) n ≤
            tailSurvival G p 0 t * (C * QuitProbability G (p (0 + t))) :=
          mul_le_mul_of_nonneg_left (by simpa using hreward t) hsurvival
        _ = C * (tailSurvival G p 0 t * QuitProbability G (p (0 + t))) := by ring_nf
    _ = C * (∑' t, tailSurvival G p 0 t * QuitProbability G (p (0 + t))) :=
      tsum_mul_left
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left
      (tsum_tailSurvival_mul_quitProbability_le_one G p 0) hC
    _ = C := mul_one C

/-- Every quitting payoff lies in the uniform absolute reward bound. -/
private theorem abs_quitPayoff_le (G : QuittingGame) (p : QuitProfile G)
    (n : G.Player) {M : ℝ} (hM0 : 0 ≤ M) (hbound : ∀ A, |G.reward A n| ≤ M) :
    |QuitPayoff G p n| ≤ M := by
  have hsum := summable_quitTailPayoff G p 0 n
  have hmass := summable_tailSurvival_mul_quitProbability G p 0
  change |(∑' t, tailSurvival G p 0 t * quittingRewardPart G (p (0 + t)) n)| ≤ M
  rw [← Real.norm_eq_abs]
  calc
    ‖∑' t, tailSurvival G p 0 t * quittingRewardPart G (p (0 + t)) n‖ ≤
        ∑' t, ‖tailSurvival G p 0 t * quittingRewardPart G (p (0 + t)) n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' t, M *
        (tailSurvival G p 0 t * QuitProbability G (p (0 + t))) := by
      apply hsum.norm.tsum_le_tsum _ (hmass.mul_left M)
      intro t
      rw [Real.norm_eq_abs, abs_mul]
      have hsurvival : 0 ≤ tailSurvival G p 0 t :=
        Finset.prod_nonneg fun l _ => sub_nonneg.mpr (quitProbability_mem_Icc G _).2
      rw [abs_of_nonneg hsurvival]
      calc
        tailSurvival G p 0 t * |quittingRewardPart G (p (0 + t)) n| ≤
            tailSurvival G p 0 t * (M * QuitProbability G (p (0 + t))) :=
          mul_le_mul_of_nonneg_left
            (abs_quittingRewardPart_le G _ n hbound) hsurvival
        _ = M * (tailSurvival G p 0 t * QuitProbability G (p (0 + t))) := by ring_nf
    _ = M * (∑' t, tailSurvival G p 0 t * QuitProbability G (p (0 + t))) :=
      tsum_mul_left
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left
      (tsum_tailSurvival_mul_quitProbability_le_one G p 0) hM0
    _ = M := mul_one M

/-- A uniform terminal-reward bound also bounds the quitting-game min-max value. -/
theorem abs_minMaxQuit_le_of_reward_bound (G : QuittingGame) (n : G.Player)
    {M : ℝ} (hM0 : 0 ≤ M) (hbound : ∀ A, |G.reward A n| ≤ M) :
    |MinMaxQuit G n| ≤ M := by
  classical
  let upper : QuitProfile G → ℝ := fun profile =>
    ⨆ deviation : ℕ → Set.Icc (0 : ℝ) 1,
      QuitPayoff G (profile.replace G n deviation) n
  have hpayoff (profile : QuitProfile G) : |QuitPayoff G profile n| ≤ M :=
    abs_quitPayoff_le G profile n hM0 hbound
  have hinnerAbove (profile : QuitProfile G) : BddAbove (range fun deviation :
      ℕ → Set.Icc (0 : ℝ) 1 => QuitPayoff G (profile.replace G n deviation) n) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨deviation, rfl⟩
    exact (le_abs_self _).trans (hpayoff _)
  have hlower (profile : QuitProfile G) : -M ≤ upper profile := by
    let deviation : ℕ → Set.Icc (0 : ℝ) 1 := fun i => profile i n
    have hself : profile.replace G n deviation = profile := by
      funext i j
      by_cases hj : j = n
      · subst j
        simp [QuitProfile.replace, deviation]
      · simp [QuitProfile.replace, hj]
    calc
      -M ≤ QuitPayoff G profile n := neg_le_of_abs_le (hpayoff profile)
      _ = QuitPayoff G (profile.replace G n deviation) n := by rw [hself]
      _ ≤ upper profile := le_ciSup (hinnerAbove profile) deviation
  have houterBelow : BddBelow (range upper) := by
    exact ⟨-M, by rintro _ ⟨profile, rfl⟩; exact hlower profile⟩
  rw [abs_le]
  constructor
  · change -M ≤ ⨅ profile, upper profile
    exact le_ciInf fun profile => hlower profile
  · change (⨅ profile, upper profile) ≤ M
    let profile : QuitProfile G := fun _ _ => 0
    exact (ciInf_le houterBelow profile).trans
      (ciSup_le fun deviation => (le_abs_self _).trans (hpayoff _))

/-- Pointwise decreasing one player's terminal rewards cannot increase that player's
quitting-game min-max value. -/
theorem minMaxQuit_mono_reward (G : QuittingGame)
    (reward' : {A : Finset G.Player // A.Nonempty} → Payoff G.Player)
    (n : G.Player) (hreward : ∀ A, reward' A n ≤ G.reward A n) :
    MinMaxQuit (G.withReward reward') n ≤ MinMaxQuit G n := by
  classical
  let G' := G.withReward reward'
  obtain ⟨M, hM⟩ := exists_quittingPayoffDifferenceBound G
  obtain ⟨M', hM'⟩ := exists_quittingPayoffDifferenceBound G'
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.1
  have hM0' : 0 ≤ M' := le_trans (by norm_num) hM'.1
  have hpayoff (profile : QuitProfile G) : |QuitPayoff G profile n| ≤ M :=
    abs_quitPayoff_le G profile n hM0 fun A => (hM.2.2 A n).le
  have hpayoff' (profile : QuitProfile G') : |QuitPayoff G' profile n| ≤ M' :=
    abs_quitPayoff_le G' profile n hM0' fun A => (hM'.2.2 A n).le
  let upper : QuitProfile G → ℝ := fun profile =>
    ⨆ deviation : ℕ → Set.Icc (0 : ℝ) 1,
      QuitPayoff G (profile.replace G n deviation) n
  let upper' : QuitProfile G' → ℝ := fun profile =>
    ⨆ deviation : ℕ → Set.Icc (0 : ℝ) 1,
      QuitPayoff G' (profile.replace G' n deviation) n
  have hinnerAbove (profile : QuitProfile G) : BddAbove
      (range fun deviation : ℕ → Set.Icc (0 : ℝ) 1 =>
        QuitPayoff G (profile.replace G n deviation) n) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨deviation, rfl⟩
    exact (le_abs_self _).trans (hpayoff _)
  have hinnerAbove' (profile : QuitProfile G') : BddAbove
      (range fun deviation : ℕ → Set.Icc (0 : ℝ) 1 =>
        QuitPayoff G' (profile.replace G' n deviation) n) := by
    refine ⟨M', ?_⟩
    rintro _ ⟨deviation, rfl⟩
    exact (le_abs_self _).trans (hpayoff' _)
  have hupper (profile : QuitProfile G) : upper' profile ≤ upper profile := by
    apply ciSup_mono (hinnerAbove profile)
    intro deviation
    exact quitPayoff_mono_reward G reward' (profile.replace G n deviation) n hreward
  have houterBelow' : BddBelow (range upper') := by
    refine ⟨-M', ?_⟩
    rintro _ ⟨profile, rfl⟩
    let deviation : ℕ → Set.Icc (0 : ℝ) 1 := fun _ => 0
    exact (neg_le_of_abs_le (hpayoff' (profile.replace G' n deviation))).trans
      (le_ciSup (hinnerAbove' profile) deviation)
  change (⨅ profile, upper' profile) ≤ ⨅ profile, upper profile
  exact ciInf_mono houterBelow' hupper

/-- Terminal reward coordinates together with the nonabsorption payoff zero. -/
private def quittingCoordinateValue (G : QuittingGame) (n : G.Player) :
    Option {A : Finset G.Player // A.Nonempty} → ℝ
  | none => 0
  | some A => G.reward A n

private noncomputable def quittingCoordinateRange (G : QuittingGame) (n : G.Player) :
    Finset ℝ :=
  Finset.univ.image (quittingCoordinateValue G n)

private theorem quittingCoordinateRange_nonempty (G : QuittingGame) (n : G.Player) :
    (quittingCoordinateRange G n).Nonempty := by
  classical
  refine ⟨0, Finset.mem_image.2 ⟨none, Finset.mem_univ _, ?_⟩⟩
  rfl

private noncomputable def quittingCoordinateLower (G : QuittingGame) (n : G.Player) : ℝ :=
  (quittingCoordinateRange G n).min' (quittingCoordinateRange_nonempty G n)

private noncomputable def quittingCoordinateUpper (G : QuittingGame) (n : G.Player) : ℝ :=
  (quittingCoordinateRange G n).max' (quittingCoordinateRange_nonempty G n)

private theorem quittingCoordinateValue_mem_range (G : QuittingGame) (n : G.Player)
    (v : Option {A : Finset G.Player // A.Nonempty}) :
    quittingCoordinateValue G n v ∈ quittingCoordinateRange G n := by
  classical
  exact Finset.mem_image.2 ⟨v, Finset.mem_univ v, rfl⟩

private theorem quittingCoordinateLower_le_value (G : QuittingGame) (n : G.Player)
    (v : Option {A : Finset G.Player // A.Nonempty}) :
    quittingCoordinateLower G n ≤ quittingCoordinateValue G n v := by
  exact Finset.min'_le _ _ (quittingCoordinateValue_mem_range G n v)

private theorem quittingCoordinateValue_le_upper (G : QuittingGame) (n : G.Player)
    (v : Option {A : Finset G.Player // A.Nonempty}) :
    quittingCoordinateValue G n v ≤ quittingCoordinateUpper G n := by
  exact Finset.le_max' _ _ (quittingCoordinateValue_mem_range G n v)

private theorem quittingCoordinateLower_nonpos (G : QuittingGame) (n : G.Player) :
    quittingCoordinateLower G n ≤ 0 := by
  simpa [quittingCoordinateValue] using
    quittingCoordinateLower_le_value G n none

private theorem quittingCoordinateUpper_nonneg (G : QuittingGame) (n : G.Player) :
    0 ≤ quittingCoordinateUpper G n := by
  simpa [quittingCoordinateValue] using
    quittingCoordinateValue_le_upper G n none

/-- The interval spanned by terminal rewards and zero has width below the paper's `M`. -/
private theorem quittingCoordinate_width_lt (G : QuittingGame) (n : G.Player)
    {M : ℝ} (hM : IsQuittingPayoffDifferenceBound G M) :
    quittingCoordinateUpper G n - quittingCoordinateLower G n < M := by
  classical
  obtain ⟨lowVertex, _hlowMem, hlow⟩ := Finset.mem_image.1
    (Finset.min'_mem (quittingCoordinateRange G n)
      (quittingCoordinateRange_nonempty G n))
  obtain ⟨highVertex, _hhighMem, hhigh⟩ := Finset.mem_image.1
    (Finset.max'_mem (quittingCoordinateRange G n)
      (quittingCoordinateRange_nonempty G n))
  have horder : quittingCoordinateLower G n ≤ quittingCoordinateUpper G n :=
    Finset.min'_le _ _ (Finset.max'_mem _ _)
  have hvertices :
      |quittingCoordinateValue G n highVertex - quittingCoordinateValue G n lowVertex| < M := by
    cases highVertex with
    | none =>
        cases lowVertex with
        | none => simp only [quittingCoordinateValue, sub_self, abs_zero]; linarith [hM.1]
        | some A => simpa [quittingCoordinateValue, abs_neg] using hM.2.2 A n
    | some A =>
        cases lowVertex with
        | none => simpa [quittingCoordinateValue] using hM.2.2 A n
        | some B => simpa [quittingCoordinateValue] using hM.2.1 A B n
  have hvertexOrder : quittingCoordinateValue G n lowVertex ≤
      quittingCoordinateValue G n highVertex := by
    rw [hlow, hhigh]
    exact horder
  change (quittingCoordinateRange G n).max' _ -
      (quittingCoordinateRange G n).min' _ < M
  rw [← hlow, ← hhigh]
  simpa [abs_of_nonneg (sub_nonneg.mpr hvertexOrder)] using hvertices

private theorem quittingRewardPart_le_upper_mul_quitProbability
    (G : QuittingGame) (p : QuitRow G) (n : G.Player) :
    quittingRewardPart G p n ≤
      quittingCoordinateUpper G n * QuitProbability G p := by
  classical
  rw [← nonemptyCoalitionMass_eq_quitProbability G p, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _hA
  split_ifs with hnonempty
  · rw [mul_comm (quittingCoordinateUpper G n)]
    exact mul_le_mul_of_nonneg_left
      (by simpa [quittingCoordinateValue] using
        quittingCoordinateValue_le_upper G n (some ⟨A, hnonempty⟩))
      (by
        simp only [CoalitionProbability]
        exact mul_nonneg
          (Finset.prod_nonneg fun i _ => (p i).property.1)
          (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (p i).property.2))
  · simp

private theorem quittingRewardPart_ge_lower_mul_quitProbability
    (G : QuittingGame) (p : QuitRow G) (n : G.Player) :
    quittingCoordinateLower G n * QuitProbability G p ≤ quittingRewardPart G p n := by
  classical
  rw [← nonemptyCoalitionMass_eq_quitProbability G p, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _hA
  split_ifs with hnonempty
  · rw [mul_comm (quittingCoordinateLower G n)]
    exact mul_le_mul_of_nonneg_left
      (by simpa [quittingCoordinateValue] using
        quittingCoordinateLower_le_value G n (some ⟨A, hnonempty⟩))
      (by
        simp only [CoalitionProbability]
        exact mul_nonneg
          (Finset.prod_nonneg fun i _ => (p i).property.1)
          (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (p i).property.2))
  · simp

/-- Every quitting-profile payoff lies in the interval spanned by zero and terminal rewards. -/
private theorem quitPayoff_mem_coordinateInterval (G : QuittingGame)
    (p : QuitProfile G) (n : G.Player) :
    QuitPayoff G p n ∈
      Set.Icc (quittingCoordinateLower G n) (quittingCoordinateUpper G n) := by
  have hsum := summable_quitTailPayoff G p 0 n
  have hmass := summable_tailSurvival_mul_quitProbability G p 0
  have hsurvival (t : ℕ) : 0 ≤ tailSurvival G p 0 t :=
    Finset.prod_nonneg fun i _ => sub_nonneg.mpr (quitProbability_mem_Icc G _).2
  constructor
  · change quittingCoordinateLower G n ≤
      ∑' t, tailSurvival G p 0 t * quittingRewardPart G (p (0 + t)) n
    calc
      quittingCoordinateLower G n = quittingCoordinateLower G n * 1 := by ring
      _ ≤ quittingCoordinateLower G n *
          (∑' t, tailSurvival G p 0 t * QuitProbability G (p (0 + t))) := by
        exact mul_le_mul_of_nonpos_left
          (tsum_tailSurvival_mul_quitProbability_le_one G p 0)
          (quittingCoordinateLower_nonpos G n)
      _ = ∑' t, quittingCoordinateLower G n *
          (tailSurvival G p 0 t * QuitProbability G (p (0 + t))) := tsum_mul_left.symm
      _ ≤ ∑' t, tailSurvival G p 0 t * quittingRewardPart G (p (0 + t)) n := by
        apply (hmass.mul_left (quittingCoordinateLower G n)).tsum_le_tsum _ hsum
        intro t
        calc
          quittingCoordinateLower G n *
              (tailSurvival G p 0 t * QuitProbability G (p (0 + t))) =
              tailSurvival G p 0 t *
                (quittingCoordinateLower G n * QuitProbability G (p (0 + t))) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (quittingRewardPart_ge_lower_mul_quitProbability G _ n) (hsurvival t)
  · exact quitPayoff_le_of_nonnegative_rewardPart_le G p n
      (quittingCoordinateUpper G n) (quittingCoordinateUpper_nonneg G n)
      (fun t => quittingRewardPart_le_upper_mul_quitProbability G (p t) n)

/-- Two quitting-profile payoffs differ by less than the terminal payoff diameter. -/
private theorem abs_quitPayoff_sub_lt (G : QuittingGame) (p q : QuitProfile G)
    (n : G.Player) {M : ℝ} (hM : IsQuittingPayoffDifferenceBound G M) :
    |QuitPayoff G p n - QuitPayoff G q n| < M := by
  rcases quitPayoff_mem_coordinateInterval G p n with ⟨hpLower, hpUpper⟩
  rcases quitPayoff_mem_coordinateInterval G q n with ⟨hqLower, hqUpper⟩
  have hwidth := quittingCoordinate_width_lt G n hM
  rw [abs_lt]
  constructor <;> linarith

/-- The exact-quitter coalition weights, including the empty coalition, sum to one. -/
private theorem coalitionProbability_sum_one (G : QuittingGame) (p : QuitRow G) :
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

/-- The finite probability mass function of the exact quitting coalition. -/
private noncomputable def coalitionPMF (G : QuittingGame) (p : QuitRow G) :
    PMF (Finset G.Player) := by
  classical
  apply PMF.ofFintype (fun A => ENNReal.ofReal (CoalitionProbability G p A))
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [show (∑ A, CoalitionProbability G p A) =
        ∑ A ∈ Finset.univ.powerset, CoalitionProbability G p A by simp]
    rw [coalitionProbability_sum_one, ENNReal.ofReal_one]
  · intro A _hA
    simp only [CoalitionProbability]
    exact mul_nonneg
      (Finset.prod_nonneg fun i _ => (p i).property.1)
      (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (p i).property.2)

@[simp] private theorem coalitionPMF_apply_toReal
    (G : QuittingGame) (p : QuitRow G) (A : Finset G.Player) :
    (coalitionPMF G p A).toReal = CoalitionProbability G p A := by
  classical
  rw [coalitionPMF, PMF.ofFintype_apply]
  rw [ENNReal.toReal_ofReal]
  simp only [CoalitionProbability]
  exact mul_nonneg
    (Finset.prod_nonneg fun i _ => (p i).property.1)
    (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (p i).property.2)

/-- Reindexing a PMF expectation along an injective map does not change its value. -/
private theorem PMF.tsum_map_toReal_mul_of_injective {A B : Type*}
    (μ : PMF A) (f : A → B) (hf : Function.Injective f) (v : B → ℝ) :
    (∑' b, ((μ.map f) b).toReal * v b) = ∑' a, (μ a).toReal * v (f a) := by
  classical
  have hmap (a : A) : (μ.map f) (f a) = μ a := by
    rw [PMF.map_apply, tsum_eq_single a]
    · simp
    · intro other hother
      rw [if_neg]
      exact fun h => hother (hf h.symm)
  have hsupport : Function.support (fun b => ((μ.map f) b).toReal * v b) ⊆
      Set.range f := by
    intro b hb
    by_contra hrange
    have hzero : (μ.map f) b = 0 := by
      rw [PMF.map_apply]
      calc
        (∑' a, if b = f a then μ a else 0) = ∑' _a : A, 0 := by
          apply tsum_congr
          intro a
          rw [if_neg]
          exact fun h => hrange ⟨a, h.symm⟩
        _ = 0 := tsum_zero
    apply hb
    change ((μ.map f) b).toReal * v b = 0
    rw [hzero]
    simp
  rw [← hf.tsum_eq hsupport]
  apply tsum_congr
  intro a
  rw [hmap]

/-- A one-stage payoff is the full coalition expectation, with continuation at `∅`. -/
private theorem quittingOneStagePayoff_eq_coalition_sum
    (G : QuittingGame) (r : Payoff G.Player) (p : QuitRow G) (n : G.Player) :
    QuittingOneStagePayoff G r p n =
      ∑ A ∈ Finset.univ.powerset, CoalitionProbability G p A *
        if hA : A.Nonempty then G.reward ⟨A, hA⟩ n else r n := by
  classical
  have hempty : CoalitionProbability G p ∅ = 1 - QuitProbability G p := by
    simp [CoalitionProbability, QuitProbability]
  change (1 - QuitProbability G p) * r n +
      (∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
        CoalitionProbability G p A * G.reward ⟨A, hA⟩ n else 0) = _
  symm
  calc
    (∑ A ∈ Finset.univ.powerset, CoalitionProbability G p A *
        if hA : A.Nonempty then G.reward ⟨A, hA⟩ n else r n) =
        CoalitionProbability G p ∅ * r n +
          ∑ A ∈ Finset.univ.powerset.erase ∅, CoalitionProbability G p A *
            if hA : A.Nonempty then G.reward ⟨A, hA⟩ n else r n := by
      rw [← Finset.sum_erase_add _ _ (by simp :
        (∅ : Finset G.Player) ∈ Finset.univ.powerset)]
      simp
    _ = (1 - QuitProbability G p) * r n +
          ∑ A ∈ Finset.univ.powerset.erase ∅, if hA : A.Nonempty then
            CoalitionProbability G p A * G.reward ⟨A, hA⟩ n else 0 := by
      rw [hempty]
      congr 1
      apply Finset.sum_congr rfl
      intro A hA
      have hnonempty : A.Nonempty := Finset.nonempty_iff_ne_empty.2
        (Finset.ne_of_mem_erase hA)
      simp only [hnonempty, dite_true]
    _ = (1 - QuitProbability G p) * r n +
          ∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
            CoalitionProbability G p A * G.reward ⟨A, hA⟩ n else 0 := by
      congr 1
      rw [← Finset.sum_erase_add _ _ (by simp :
        (∅ : Finset G.Player) ∈ Finset.univ.powerset)]
      simp

/-- One-stage coalition averaging preserves the terminal-coordinate interval. -/
private theorem quittingOneStagePayoff_mem_coordinateInterval
    (G : QuittingGame) (r : Payoff G.Player) (p : QuitRow G) (n : G.Player)
    (hr : r n ∈ Set.Icc (quittingCoordinateLower G n)
      (quittingCoordinateUpper G n)) :
    QuittingOneStagePayoff G r p n ∈
      Set.Icc (quittingCoordinateLower G n) (quittingCoordinateUpper G n) := by
  classical
  rw [quittingOneStagePayoff_eq_coalition_sum]
  have hprob (A : Finset G.Player) : 0 ≤ CoalitionProbability G p A := by
    simp only [CoalitionProbability]
    exact mul_nonneg
      (Finset.prod_nonneg fun i _ => (p i).property.1)
      (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (p i).property.2)
  have hvalue (A : Finset G.Player) :
      (if hA : A.Nonempty then G.reward ⟨A, hA⟩ n else r n) ∈
        Set.Icc (quittingCoordinateLower G n) (quittingCoordinateUpper G n) := by
    split_ifs with hA
    · constructor
      · simpa [quittingCoordinateValue] using
          quittingCoordinateLower_le_value G n (some ⟨A, hA⟩)
      · simpa [quittingCoordinateValue] using
          quittingCoordinateValue_le_upper G n (some ⟨A, hA⟩)
    · exact hr
  constructor
  · calc
      quittingCoordinateLower G n =
          ∑ A ∈ Finset.univ.powerset,
            CoalitionProbability G p A * quittingCoordinateLower G n := by
        rw [← Finset.sum_mul, coalitionProbability_sum_one, one_mul]
      _ ≤ ∑ A ∈ Finset.univ.powerset, CoalitionProbability G p A *
          if hA : A.Nonempty then G.reward ⟨A, hA⟩ n else r n := by
        exact Finset.sum_le_sum fun A _ =>
          mul_le_mul_of_nonneg_left (hvalue A).1 (hprob A)
  · calc
      (∑ A ∈ Finset.univ.powerset, CoalitionProbability G p A *
          if hA : A.Nonempty then G.reward ⟨A, hA⟩ n else r n) ≤
          ∑ A ∈ Finset.univ.powerset,
            CoalitionProbability G p A * quittingCoordinateUpper G n := by
        exact Finset.sum_le_sum fun A _ =>
          mul_le_mul_of_nonneg_left (hvalue A).2 (hprob A)
      _ = quittingCoordinateUpper G n := by
        rw [← Finset.sum_mul, coalitionProbability_sum_one, one_mul]

/-- Every player's min-max is at most the better of quitting alone and never quitting. -/
private theorem minMaxQuit_le_max_solo_zero (G : QuittingGame) (j : G.Player) :
    MinMaxQuit G j ≤ max (SoloPayoff G j) 0 := by
  classical
  obtain ⟨M, hM⟩ := exists_quittingPayoffDifferenceBound G
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.1
  have hpayoffBound : ∀ p : QuitProfile G, |QuitPayoff G p j| ≤ M := fun p =>
    abs_quitPayoff_le G p j hM0 (fun A => le_of_lt (hM.2.2 A j))
  have hinnerAbove : ∀ p : QuitProfile G, BddAbove (range fun q :
      ℕ → Set.Icc (0 : ℝ) 1 => QuitPayoff G (p.replace G j q) j) := by
    intro p
    refine ⟨M, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact (le_abs_self _).trans (hpayoffBound _)
  have houterBelow : BddBelow (range fun p : QuitProfile G =>
      ⨆ q : ℕ → Set.Icc (0 : ℝ) 1, QuitPayoff G (p.replace G j q) j) := by
    refine ⟨-M, ?_⟩
    rintro _ ⟨p, rfl⟩
    let q : ℕ → Set.Icc (0 : ℝ) 1 := fun _ => 0
    exact (neg_le_of_abs_le (hpayoffBound (p.replace G j q))).trans
      (le_ciSup (hinnerAbove p) q)
  let zeroProfile : QuitProfile G := fun _ _ => (0 : Set.Icc (0 : ℝ) 1)
  rw [MinMaxQuit]
  apply le_trans (ciInf_le houterBelow zeroProfile)
  apply ciSup_le
  intro q
  let deviation := zeroProfile.replace G j q
  apply quitPayoff_le_of_nonnegative_rewardPart_le G deviation j
    (max (SoloPayoff G j) 0) (le_max_right _ _)
  intro t
  have hrow : deviation t =
      QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j (q t) := rfl
  rw [hrow, quittingRewardPart_allContinue_replace]
  rw [quitProbability_allContinue_replace]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left (le_max_left (SoloPayoff G j) 0) (q t).property.1

/-- Lemma 3.  An abnormal `j` has `vʲ < 0`, and `v({i})ʲ ≥ χʲ` for every `i ≠ j`. -/
theorem lemma3 (G : QuittingGame) (j : G.Player) (h : ¬IsNormalPlayer G j) :
    SoloPayoff G j < 0 ∧ ∀ i, i ≠ j →
      G.reward ⟨{i}, Finset.singleton_nonempty i⟩ j ≥ MinMaxQuit G j := by
  classical
  have habnormal : SoloPayoff G j < MinMaxQuit G j := by
    exact lt_of_not_ge h
  obtain ⟨M, hM⟩ := exists_quittingPayoffDifferenceBound G
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.1
  have hpayoffBound : ∀ p : QuitProfile G, |QuitPayoff G p j| ≤ M := fun p =>
    abs_quitPayoff_le G p j hM0 (fun A => le_of_lt (hM.2.2 A j))
  have hinnerAbove : ∀ p : QuitProfile G, BddAbove (range fun q :
      ℕ → Set.Icc (0 : ℝ) 1 => QuitPayoff G (p.replace G j q) j) := by
    intro p
    refine ⟨M, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact (le_abs_self _).trans (hpayoffBound _)
  have houterBelow : BddBelow (range fun p : QuitProfile G =>
      ⨆ q : ℕ → Set.Icc (0 : ℝ) 1, QuitPayoff G (p.replace G j q) j) := by
    refine ⟨-M, ?_⟩
    rintro _ ⟨p, rfl⟩
    let q : ℕ → Set.Icc (0 : ℝ) 1 := fun _ => 0
    exact (neg_le_of_abs_le (hpayoffBound (p.replace G j q))).trans
      (le_ciSup (hinnerAbove p) q)
  have hminmaxZero : MinMaxQuit G j ≤ max (SoloPayoff G j) 0 :=
    minMaxQuit_le_max_solo_zero G j
  have hsoloNegative : SoloPayoff G j < 0 := by
    by_contra hnonnegative
    rw [max_eq_left (le_of_not_gt hnonnegative)] at hminmaxZero
    linarith
  refine ⟨hsoloNegative, ?_⟩
  intro i hij
  by_contra hreward
  have hrewardStrict : G.reward ⟨{i}, Finset.singleton_nonempty i⟩ j <
      MinMaxQuit G j := lt_of_not_ge hreward
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM.1
  let gap : ℝ := MinMaxQuit G j -
    max (SoloPayoff G j) (G.reward ⟨{i}, Finset.singleton_nonempty i⟩ j)
  have hgap : 0 < gap := by
    dsimp only [gap]
    exact sub_pos.mpr (max_lt habnormal hrewardStrict)
  let av : ℝ := min (1 / 2) (gap / (4 * M))
  have hav0 : 0 < av := by
    dsimp only [av]
    exact lt_min (by norm_num) (div_pos hgap (mul_pos (by norm_num) hMpos))
  have hav1 : av < 1 := (min_le_left _ _).trans_lt (by norm_num)
  let a : Set.Icc (0 : ℝ) 1 := ⟨av, le_of_lt hav0, le_of_lt hav1⟩
  let base : QuitRow G := rareQuitRow G i a
  let profile : QuitProfile G := fun _ => base
  let C : ℝ := max (SoloPayoff G j + 2 * M * av)
    (G.reward ⟨{i}, Finset.singleton_nonempty i⟩ j)
  have havGap : 2 * M * av ≤ gap / 2 := by
    have havBound := min_le_right (1 / 2) (gap / (4 * M))
    dsimp only [av]
    calc
      2 * M * av ≤ 2 * M * (gap / (4 * M)) :=
        mul_le_mul_of_nonneg_left havBound (by positivity)
      _ = gap / 2 := by field_simp; ring
  have hC : C < MinMaxQuit G j := by
    dsimp only [C]
    apply max_lt
    · have hsoloMax : SoloPayoff G j ≤
          max (SoloPayoff G j) (G.reward ⟨{i}, Finset.singleton_nonempty i⟩ j) :=
        le_max_left _ _
      dsimp only [gap] at havGap
      linarith
    · exact hrewardStrict
  have hminmaxRare : MinMaxQuit G j ≤ C := by
    rw [MinMaxQuit]
    apply le_trans (ciInf_le houterBelow profile)
    apply ciSup_le
    intro q
    let deviation := profile.replace G j q
    have hrow : ∀ t, deviation t = (base.replace G j (q t)) := fun t => rfl
    have hbasej : base j = (0 : Set.Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      simp [base, rareQuitRow, QuitRow.replace, Ne.symm hij]
    have hjzero : base.replace G j 0 = base := by
      rw [← hbasej]
      exact QuitRow.replace_self G base j
    have hcomm : base.replace G j 1 =
        (QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j 1).replace G i a := by
      exact QuitRow.replace_comm G _ hij a 1
    have hforced : quittingRewardPart G (base.replace G j 1) j ≤
        SoloPayoff G j + 2 * M * av := by
      rw [hcomm, quittingRewardPart_replace_affine]
      have hsoloi :
          (QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j 1).replace G i 0 =
            QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j 1 := by
        have hi0 :
            QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j 1 i = 0 := by
          apply Subtype.ext
          simp [QuitRow.replace, hij]
        simpa only [hi0] using QuitRow.replace_self G
          (QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j 1) i
      rw [hsoloi, QuitRow.zero_replace_one, quittingRewardPart_soloQuitRow]
      let both :=
        (QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j 1).replace G i 1
      have hbothAbs : |quittingRewardPart G both j| ≤ M := by
        calc
          |quittingRewardPart G both j| ≤ M * QuitProbability G both :=
            abs_quittingRewardPart_le G both j (fun A => le_of_lt (hM.2.2 A j))
          _ ≤ M * 1 := mul_le_mul_of_nonneg_left
            (quitProbability_mem_Icc G both).2 (le_trans (by norm_num) hM.1)
          _ = M := mul_one M
      have hboth : quittingRewardPart G both j ≤ M :=
        (le_abs_self _).trans hbothAbs
      have hsoloLower : -M < SoloPayoff G j := by
        exact (neg_lt_of_abs_lt (hM.2.2 ⟨{j}, Finset.singleton_nonempty j⟩ j))
      change av * quittingRewardPart G both j +
          (1 - av) * SoloPayoff G j ≤ SoloPayoff G j + 2 * M * av
      nlinarith [mul_nonneg (le_of_lt hav0) (le_of_lt hMpos)]
    have hrewards : ∀ t,
        quittingRewardPart G (deviation t) j ≤ C * QuitProbability G (deviation t) := by
      intro t
      rw [hrow, quittingRewardPart_replace_affine, hjzero]
      rw [quittingRewardPart_rareQuitRow]
      have hsurvival := one_sub_quitProbability_replace G base j (q t)
      rw [hjzero, one_sub_quitProbability_rareQuitRow] at hsurvival
      have hquit : QuitProbability G (base.replace G j (q t)) =
          (q t : ℝ) + (1 - (q t : ℝ)) * av := by
        change 1 - QuitProbability G (base.replace G j (q t)) =
          (1 - (q t : ℝ)) * (1 - av) at hsurvival
        linarith
      rw [hquit]
      have hforcedC : quittingRewardPart G (base.replace G j 1) j ≤ C :=
        hforced.trans (le_max_left _ _)
      have hrewardC : G.reward ⟨{i}, Finset.singleton_nonempty i⟩ j ≤ C :=
        le_max_right _ _
      have hfirst := mul_le_mul_of_nonneg_left hforcedC (q t).property.1
      have hsecondBase := mul_le_mul_of_nonneg_left hrewardC (le_of_lt hav0)
      have hsecond := mul_le_mul_of_nonneg_left hsecondBase
        (sub_nonneg.mpr (q t).property.2)
      nlinarith
    have hvanish : Tendsto (tailSurvival G deviation 0) atTop (nhds 0) := by
      apply squeeze_zero
      · intro t
        exact Finset.prod_nonneg fun l _ =>
          sub_nonneg.mpr (quitProbability_mem_Icc G _).2
      · intro t
        calc
          tailSurvival G deviation 0 t ≤
              ∏ l ∈ Finset.range t, (1 - av) := by
            apply Finset.prod_le_prod
            · intro l hl
              exact sub_nonneg.mpr (quitProbability_mem_Icc G _).2
            · intro l hl
              rw [hrow]
              have hs := one_sub_quitProbability_replace G base j (q l)
              rw [hjzero, one_sub_quitProbability_rareQuitRow] at hs
              simp only [Nat.zero_add]
              rw [hs]
              exact mul_le_of_le_one_left (sub_nonneg.mpr (le_of_lt hav1))
                (by linarith [(q l).property.1])
          _ = (1 - av) ^ t := by simp
      · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
    apply quitPayoff_le_of_rewardPart_le G deviation j C hrewards
    have hmass := tsum_tailSurvival_mul_quitProbability_eq_one G deviation 0 hvanish
    simpa using hmass
  linarith

/-- Quitting tail payoffs satisfy the one-stage Bellman recursion. -/
private theorem quitTailPayoff_eq_oneStage (G : QuittingGame) (p : QuitProfile G)
    (i : ℕ) :
    QuitTailPayoff G p i = QuittingOneStagePayoff G (QuitTailPayoff G p (i + 1)) (p i) := by
  funext n
  have hsummable := summable_quitTailPayoff G p i n
  change (∑' k, tailSurvival G p i k * quittingRewardPart G (p (i + k)) n) =
    (1 - QuitProbability G (p i)) *
        ∑' k, tailSurvival G p (i + 1) k *
          quittingRewardPart G (p ((i + 1) + k)) n + quittingRewardPart G (p i) n
  rw [hsummable.tsum_eq_zero_add]
  rw [show tailSurvival G p i 0 = 1 by simp [tailSurvival]]
  simp only [one_mul, Nat.add_zero]
  rw [← tsum_mul_left]
  rw [add_comm (quittingRewardPart G (p i) n)]
  congr 1
  apply tsum_congr
  intro k
  rw [tailSurvival_succ]
  ring_nf

/-- The payoff of a finite sequence of quitting rows followed by terminal vector `x`. -/
private def finiteQuittingPayoff (G : QuittingGame) :
    (k : ℕ) → Payoff G.Player → (ℕ → QuitRow G) → Payoff G.Player
  | 0, x, _ => x
  | k + 1, x, p =>
      QuittingOneStagePayoff G
        (finiteQuittingPayoff G k x fun i => p (i + 1)) (p 0)

/-- Iterating the Bellman recursion gives the tail payoff after a finite prefix. -/
private theorem quitTailPayoff_eq_finiteQuittingPayoff (G : QuittingGame)
    (p : QuitProfile G) (i k : ℕ) :
    QuitTailPayoff G p i =
      finiteQuittingPayoff G k (QuitTailPayoff G p (i + k)) (fun j => p (i + j)) := by
  induction k generalizing i with
  | zero => simp [finiteQuittingPayoff]
  | succ k ih =>
      rw [quitTailPayoff_eq_oneStage]
      simp only [finiteQuittingPayoff]
      congr 1
      simpa [Nat.add_assoc, Nat.add_comm 1] using ih (i + 1)

/-- Splitting off the first factor of a product over an initial segment. -/
private theorem prod_range_succ_shift (f : ℕ → ℝ) (k : ℕ) :
    Finset.prod (Finset.range (k + 1)) f =
      f 0 * Finset.prod (Finset.range k) (fun j => f (j + 1)) := by
  rw [Finset.prod_range_succ']
  ring_nf

/-- Finite quitting payoffs contract terminal-vector differences by finite survival. -/
private theorem finiteQuittingPayoff_sub (G : QuittingGame) (k : ℕ)
    (x y : Payoff G.Player) (p : ℕ → QuitRow G) (n : G.Player) :
    finiteQuittingPayoff G k x p n - finiteQuittingPayoff G k y p n =
      Finset.prod (Finset.range k) (fun j => 1 - QuitProbability G (p j)) *
        (x n - y n) := by
  induction k generalizing p with
  | zero => simp [finiteQuittingPayoff]
  | succ k ih =>
      simp only [finiteQuittingPayoff, QuittingOneStagePayoff]
      change
        ((1 - QuitProbability G (p 0)) * finiteQuittingPayoff G k x
            (fun i => p (i + 1)) n + quittingRewardPart G (p 0) n) -
          ((1 - QuitProbability G (p 0)) * finiteQuittingPayoff G k y
            (fun i => p (i + 1)) n + quittingRewardPart G (p 0) n) = _
      rw [show
        ((1 - QuitProbability G (p 0)) * finiteQuittingPayoff G k x
            (fun i => p (i + 1)) n + quittingRewardPart G (p 0) n) -
          ((1 - QuitProbability G (p 0)) * finiteQuittingPayoff G k y
            (fun i => p (i + 1)) n + quittingRewardPart G (p 0) n) =
          (1 - QuitProbability G (p 0)) *
            (finiteQuittingPayoff G k x (fun i => p (i + 1)) n -
              finiteQuittingPayoff G k y (fun i => p (i + 1)) n) by ring_nf]
      rw [ih, prod_range_succ_shift]
      ring_nf

/-- A finite quitting payoff depends only on the rows before its terminal stage. -/
private theorem finiteQuittingPayoff_congr (G : QuittingGame) (k : ℕ)
    (x : Payoff G.Player) (p q : ℕ → QuitRow G)
    (h : ∀ j < k, p j = q j) :
    finiteQuittingPayoff G k x p = finiteQuittingPayoff G k x q := by
  induction k generalizing p q with
  | zero => rfl
  | succ k ih =>
      simp only [finiteQuittingPayoff]
      rw [h 0 (by omega)]
      congr 1
      apply ih
      intro j hj
      exact h (j + 1) (by omega)

/-- Reversing the first `j` rows and iterating from `s₀` produces `sⱼ`. -/
private theorem finiteQuittingPayoff_reverse_eq (G : QuittingGame) {k : ℕ}
    (p : ℕ → QuitRow G) (s : ℕ → Payoff G.Player)
    (hstep : ∀ j < k, s (j + 1) = QuittingOneStagePayoff G (s j) (p j)) :
    ∀ j ≤ k, finiteQuittingPayoff G j (s 0) (fun i => p (j - 1 - i)) = s j := by
  intro j hj
  induction j with
  | zero => simp [finiteQuittingPayoff]
  | succ j ih =>
      simp only [finiteQuittingPayoff]
      have hrows : (fun i => p (j + 1 - 1 - (i + 1))) =
          fun i => p (j - 1 - i) := by
        funext i
        congr 1
        omega
      rw [hrows, ih (by omega)]
      simpa using (hstep j (by omega)).symm

/-- Reverse and periodically repeat a finite block of quitting rows. -/
def ReverseCycleProfile (G : QuittingGame) (k : ℕ) (_hk : 0 < k)
    (p : ℕ → QuitRow G) : QuitProfile G :=
  fun i => p (k - 1 - i % k)

/-- A reverse-cycle profile repeats after one block. -/
private theorem reverseCycleProfile_add_period (G : QuittingGame) (k : ℕ)
    (hk : 0 < k) (p : ℕ → QuitRow G) (i : ℕ) :
    ReverseCycleProfile G k hk p (i + k) = ReverseCycleProfile G k hk p i := by
  simp [ReverseCycleProfile, Nat.add_mod_right]

/-- Tail payoffs of a reverse-cycle profile repeat after one block. -/
private theorem quitTailPayoff_reverseCycle_add_period (G : QuittingGame) (k : ℕ)
    (hk : 0 < k) (p : ℕ → QuitRow G) (i : ℕ) :
    QuitTailPayoff G (ReverseCycleProfile G k hk p) (i + k) =
      QuitTailPayoff G (ReverseCycleProfile G k hk p) i := by
  funext n
  apply tsum_congr
  intro l
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    rw [show i + k + j = (i + j) + k by omega]
    rw [reverseCycleProfile_add_period]
  · apply Finset.sum_congr rfl
    intro A hA
    split_ifs
    · rw [show i + k + l = (i + l) + k by omega]
      rw [reverseCycleProfile_add_period]
    · rfl

/-- At a block boundary, a reverse-cycle profile starts with the reversed block. -/
private theorem reverseCycleProfile_mul_add (G : QuittingGame) (k : ℕ)
    (hk : 0 < k) (p : ℕ → QuitRow G) (m j : ℕ) (hj : j < k) :
    ReverseCycleProfile G k hk p (m * k + j) = p (k - 1 - j) := by
  dsimp only [ReverseCycleProfile]
  rw [show m * k + j = j + m * k by omega]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- Every block boundary of a reverse cycle has the same tail payoff. -/
private theorem quitTailPayoff_reverseCycle_mul (G : QuittingGame) (k : ℕ)
    (hk : 0 < k) (p : ℕ → QuitRow G) (m : ℕ) :
    QuitTailPayoff G (ReverseCycleProfile G k hk p) (m * k) =
      QuitTailPayoff G (ReverseCycleProfile G k hk p) 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_mul]
      rw [quitTailPayoff_reverseCycle_add_period, ih]

/-- Finite quitting recursion is nonexpansive in its terminal payoff. -/
private theorem finiteQuittingPayoff_norm_sub_le (G : QuittingGame) (k : ℕ)
    (x y : Payoff G.Player) (p : ℕ → QuitRow G) :
    ‖finiteQuittingPayoff G k x p - finiteQuittingPayoff G k y p‖ ≤ ‖x - y‖ := by
  rw [pi_norm_le_iff_of_nonempty]
  intro n
  rw [Real.norm_eq_abs]
  simp only [Pi.sub_apply]
  rw [finiteQuittingPayoff_sub, abs_mul]
  have hfactor0 : ∀ j ∈ Finset.range k,
      0 ≤ 1 - QuitProbability G (p j) := by
    intro j hj
    exact sub_nonneg.mpr (quitProbability_mem_Icc G _).2
  have hfactor1 : ∀ j ∈ Finset.range k,
      1 - QuitProbability G (p j) ≤ 1 := by
    intro j hj
    linarith [(quitProbability_mem_Icc G (p j)).1]
  have hprod0 : 0 ≤ Finset.prod (Finset.range k)
      (fun j => 1 - QuitProbability G (p j)) := Finset.prod_nonneg hfactor0
  rw [abs_of_nonneg hprod0]
  calc
    Finset.prod (Finset.range k) (fun j => 1 - QuitProbability G (p j)) *
        |x n - y n| ≤ 1 * |x n - y n| :=
      mul_le_mul_of_nonneg_right (Finset.prod_le_one hfactor0 hfactor1) (abs_nonneg _)
    _ ≤ ‖x - y‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (x - y) n

/-- Forced-continuation payoff is one-Lipschitz in the continuation vector. -/
private theorem abs_forcedContinuePayoff_sub_le (G : QuittingGame)
    (r s : Payoff G.Player) (p : QuitRow G) (n : G.Player) :
    |ForcedContinuePayoff G r p n - ForcedContinuePayoff G s p n| ≤ ‖r - s‖ := by
  change |(1 - QuitProbability G (p.replace G n 0)) * r n +
      quittingRewardPart G (p.replace G n 0) n -
    ((1 - QuitProbability G (p.replace G n 0)) * s n +
      quittingRewardPart G (p.replace G n 0) n)| ≤ _
  rw [show
    (1 - QuitProbability G (p.replace G n 0)) * r n +
        quittingRewardPart G (p.replace G n 0) n -
      ((1 - QuitProbability G (p.replace G n 0)) * s n +
        quittingRewardPart G (p.replace G n 0) n) =
      (1 - QuitProbability G (p.replace G n 0)) * (r n - s n) by ring_nf]
  rw [abs_mul]
  have hfactor0 : 0 ≤ 1 - QuitProbability G (p.replace G n 0) :=
    sub_nonneg.mpr (quitProbability_mem_Icc G _).2
  rw [abs_of_nonneg hfactor0]
  calc
    (1 - QuitProbability G (p.replace G n 0)) * |r n - s n| ≤
        1 * |r n - s n| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      linarith [(quitProbability_mem_Icc G (p.replace G n 0)).1]
    _ ≤ ‖r - s‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (r - s) n

/--
Lemma 4.  Reversing and repeating a block whose continuation vectors return within `δ`
produces tail vectors within `δ/ρ`; `E_ε` membership degrades only to
`E_{ε+δ/ρ}`.
-/
theorem lemma4 (G : QuittingGame) {k : ℕ} (hk : 0 < k)
    (p : ℕ → QuitRow G) (s : ℕ → Payoff G.Player) {ρ δ ε : ℝ}
    (hρ : 0 < ρ) (_hρ1 : ρ < 1)
    (hprob : ρ = 1 - ∏ j ∈ Finset.range k, (1 - QuitProbability G (p j)))
    (hstep : ∀ j < k, s (j + 1) = QuittingOneStagePayoff G (s j) (p j))
    (hclose : ‖s 0 - s k‖ ≤ δ) :
    let cycle := ReverseCycleProfile G k hk p
    (∀ m i, (m - 1) * k < i → i ≤ m * k →
      ‖QuitTailPayoff G cycle i - s (m * k - i)‖ ≤ δ / ρ) ∧
    ((∀ j < k, p j ∈ EpsilonRow G ε (s j)) →
      ∀ i, cycle i ∈ EpsilonRow G (ε + δ / ρ) (QuitTailPayoff G cycle (i + 1))) := by
  let cycle := ReverseCycleProfile G k hk p
  change (∀ m i, (m - 1) * k < i → i ≤ m * k →
      ‖QuitTailPayoff G cycle i - s (m * k - i)‖ ≤ δ / ρ) ∧
    ((∀ j < k, p j ∈ EpsilonRow G ε (s j)) →
      ∀ i, cycle i ∈ EpsilonRow G (ε + δ / ρ) (QuitTailPayoff G cycle (i + 1)))
  have hcycleRows : ∀ j < k, cycle j = p (k - 1 - j) := by
    intro j hj
    simpa [cycle] using reverseCycleProfile_mul_add G k hk p 0 j hj
  have hperiod : QuitTailPayoff G cycle k = QuitTailPayoff G cycle 0 := by
    simpa [cycle] using quitTailPayoff_reverseCycle_add_period G k hk p 0
  have hfixed : QuitTailPayoff G cycle 0 =
      finiteQuittingPayoff G k (QuitTailPayoff G cycle 0)
        (fun j => p (k - 1 - j)) := by
    calc
      QuitTailPayoff G cycle 0 =
          finiteQuittingPayoff G k (QuitTailPayoff G cycle k) cycle := by
        simpa using quitTailPayoff_eq_finiteQuittingPayoff G cycle 0 k
      _ = finiteQuittingPayoff G k (QuitTailPayoff G cycle 0) cycle := by rw [hperiod]
      _ = finiteQuittingPayoff G k (QuitTailPayoff G cycle 0)
          (fun j => p (k - 1 - j)) :=
        finiteQuittingPayoff_congr G k _ _ _ hcycleRows
  have hsK : finiteQuittingPayoff G k (s 0) (fun j => p (k - 1 - j)) = s k :=
    finiteQuittingPayoff_reverse_eq G p s hstep k le_rfl
  have hscaled : ρ • (QuitTailPayoff G cycle 0 - s 0) = s k - s 0 := by
    funext n
    have hpoint := finiteQuittingPayoff_sub G k (QuitTailPayoff G cycle 0)
      (s 0) (fun j => p (k - 1 - j)) n
    rw [← hfixed, hsK] at hpoint
    have hreflect := Finset.prod_range_reflect
      (fun j => 1 - QuitProbability G (p j)) k
    rw [hreflect] at hpoint
    have hproduct : Finset.prod (Finset.range k)
        (fun j => 1 - QuitProbability G (p j)) = 1 - ρ := by
      rw [hprob]
      ring_nf
    rw [hproduct] at hpoint
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linarith
  have hboundary : ‖QuitTailPayoff G cycle 0 - s 0‖ ≤ δ / ρ := by
    apply (le_div_iff₀ hρ).2
    calc
      ‖QuitTailPayoff G cycle 0 - s 0‖ * ρ =
          ‖ρ • (QuitTailPayoff G cycle 0 - s 0)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
        ring_nf
      _ = ‖s k - s 0‖ := congrArg norm hscaled
      _ = ‖s 0 - s k‖ := norm_sub_rev _ _
      _ ≤ δ := hclose
  have hfirst : ∀ m i, (m - 1) * k < i → i ≤ m * k →
      ‖QuitTailPayoff G cycle i - s (m * k - i)‖ ≤ δ / ρ := by
    intro m i hlo hi
    have hm : 0 < m := by
      by_contra hm
      have : m = 0 := Nat.eq_zero_of_not_pos hm
      subst m
      omega
    have hmk : m * k = (m - 1) * k + k := by
      rw [show m = (m - 1) + 1 by omega, add_mul]
      simp
    let j := m * k - i
    have hij : i + j = m * k := Nat.add_sub_of_le hi
    have hj : j < k := by
      dsimp only [j]
      omega
    have hiForm : i = (m - 1) * k + (k - j) := by omega
    have hrows : ∀ l < j, cycle (i + l) = p (j - 1 - l) := by
      intro l hl
      dsimp only [cycle, ReverseCycleProfile]
      rw [hiForm]
      rw [show (m - 1) * k + (k - j) + l =
        (k - j + l) + (m - 1) * k by omega]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : k - j + l < k)]
      congr 1
      omega
    have hboundaryM : QuitTailPayoff G cycle (i + j) =
        QuitTailPayoff G cycle 0 := by
      rw [hij]
      simpa [cycle] using quitTailPayoff_reverseCycle_mul G k hk p m
    have htail : QuitTailPayoff G cycle i =
        finiteQuittingPayoff G j (QuitTailPayoff G cycle 0)
          (fun l => p (j - 1 - l)) := by
      calc
        QuitTailPayoff G cycle i =
            finiteQuittingPayoff G j (QuitTailPayoff G cycle (i + j))
              (fun l => cycle (i + l)) :=
          quitTailPayoff_eq_finiteQuittingPayoff G cycle i j
        _ = finiteQuittingPayoff G j (QuitTailPayoff G cycle 0)
            (fun l => cycle (i + l)) := by rw [hboundaryM]
        _ = finiteQuittingPayoff G j (QuitTailPayoff G cycle 0)
            (fun l => p (j - 1 - l)) :=
          finiteQuittingPayoff_congr G j _ _ _ hrows
    have hsj : finiteQuittingPayoff G j (s 0) (fun l => p (j - 1 - l)) = s j :=
      finiteQuittingPayoff_reverse_eq G p s hstep j (le_of_lt hj)
    rw [show m * k - i = j by rfl, htail, ← hsj]
    exact (finiteQuittingPayoff_norm_sub_le G j _ _ _).trans hboundary
  refine ⟨hfirst, ?_⟩
  intro hp i
  let m := i / k + 1
  let j := k - 1 - i % k
  have hmod : i % k < k := Nat.mod_lt i hk
  have hdecomp : i % k + k * (i / k) = i := Nat.mod_add_div i k
  have hdecomp' : (i / k) * k + i % k = i := by
    simpa [Nat.add_comm, Nat.mul_comm] using hdecomp
  have hlower : (m - 1) * k < i + 1 := by
    dsimp only [m]
    simp only [Nat.add_sub_cancel]
    omega
  have hupper : i + 1 ≤ m * k := by
    dsimp only [m]
    rw [add_mul]
    simp only [one_mul]
    omega
  have hdiff : m * k - (i + 1) = j := by
    dsimp only [m, j]
    rw [add_mul]
    simp only [one_mul]
    omega
  have hj : j < k := by
    dsimp only [j]
    omega
  have htail : ‖QuitTailPayoff G cycle (i + 1) - s j‖ ≤ δ / ρ := by
    simpa only [hdiff] using hfirst m (i + 1) hlower hupper
  have hcycle : cycle i = p j := by
    rfl
  rw [hcycle]
  have hpj := hp j hj
  constructor
  · intro n hquit
    have hfc : |ForcedContinuePayoff G (QuitTailPayoff G cycle (i + 1)) (p j) n -
        ForcedContinuePayoff G (s j) (p j) n| ≤ δ / ρ :=
      (abs_forcedContinuePayoff_sub_le G _ _ _ _).trans htail
    rw [abs_le] at hfc
    linarith [hpj.1 n hquit]
  · intro n hcontinue
    have hfc : |ForcedContinuePayoff G (QuitTailPayoff G cycle (i + 1)) (p j) n -
        ForcedContinuePayoff G (s j) (p j) n| ≤ δ / ρ :=
      (abs_forcedContinuePayoff_sub_le G _ _ _ _).trans htail
    rw [abs_le] at hfc
    linarith [hpj.2 n hcontinue]

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

/-- A positive stationary solo-quitting probability yields the corresponding solo reward. -/
private theorem quitPayoff_constant_rareQuitRow (G : QuittingGame) (i n : G.Player)
    (a : Set.Icc (0 : ℝ) 1) (ha : 0 < (a : ℝ)) :
    QuitPayoff G (fun _ => rareQuitRow G i a) n =
      G.reward ⟨{i}, Finset.singleton_nonempty i⟩ n := by
  let profile : QuitProfile G := fun _ => rareQuitRow G i a
  have hrowProbability : ∀ t, QuitProbability G (profile t) = a := by
    intro t
    have hsurvival := one_sub_quitProbability_rareQuitRow G i a
    dsimp only [profile]
    linarith
  have hvanish : Tendsto (tailSurvival G profile 0) atTop (nhds 0) := by
    have hbaseNonnegative : 0 ≤ 1 - (a : ℝ) := sub_nonneg.mpr a.property.2
    have hbaseLess : 1 - (a : ℝ) < 1 := by linarith
    have heq : tailSurvival G profile 0 = fun k => (1 - (a : ℝ)) ^ k := by
      funext k
      simp only [tailSurvival, Nat.zero_add]
      simp_rw [hrowProbability]
      simp
    rw [heq]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) hbaseLess
  have hmass := tsum_tailSurvival_mul_quitProbability_eq_one G profile 0 hvanish
  change (∑' k, tailSurvival G profile 0 k *
      quittingRewardPart G (profile k) n) = _
  rw [show (∑' k, tailSurvival G profile 0 k *
      quittingRewardPart G (profile k) n) =
      (∑' k, G.reward ⟨{i}, Finset.singleton_nonempty i⟩ n *
        (tailSurvival G profile 0 k * QuitProbability G (profile k))) by
    apply tsum_congr
    intro k
    rw [quittingRewardPart_rareQuitRow G i n a, hrowProbability k]
    ring]
  rw [tsum_mul_left]
  simp only [Nat.zero_add] at hmass
  rw [hmass, mul_one]

/-- A nonnegative solo quitter who harms no other solo payoff yields stationary equilibria. -/
private theorem hasStationaryApproximateEquilibria_of_soloPayoff_nonnegative
    (G : QuittingGame) (j : G.Player) (hj : 0 ≤ SoloPayoff G j)
    (hcross : ∀ n, n ≠ j →
      SoloPayoff G n ≤ G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n) :
    HasStationaryApproximateEquilibria G := by
  classical
  obtain ⟨M, hM⟩ := exists_quittingPayoffDifferenceBound G
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM.1
  intro ε hε
  let av : ℝ := min (1 / 2) (ε / (4 * M))
  have hav0 : 0 < av :=
    lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hMpos))
  have hav1 : av < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have havError : 2 * M * av ≤ ε := by
    have havBound := min_le_right (1 / 2) (ε / (4 * M))
    dsimp only [av]
    calc
      2 * M * av ≤ 2 * M * (ε / (4 * M)) :=
        mul_le_mul_of_nonneg_left havBound (by positivity)
      _ = ε / 2 := by field_simp; ring
      _ ≤ ε := by linarith
  let a : Set.Icc (0 : ℝ) 1 := ⟨av, le_of_lt hav0, le_of_lt hav1⟩
  let base : QuitRow G := rareQuitRow G j a
  let profile : QuitProfile G := fun _ => base
  refine ⟨base, ?_⟩
  intro n q
  let deviation := profile.replace G n q
  have hbasePayoff : QuitPayoff G profile n =
      G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n := by
    exact quitPayoff_constant_rareQuitRow G j n a (by simpa [a] using hav0)
  by_cases hnj : n = j
  · subst n
    have hrow : ∀ t, deviation t =
        QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j (q t) := by
      intro t
      funext k
      by_cases hkj : k = j
      · subst k
        simp [deviation, profile, base, rareQuitRow, QuitProfile.replace, QuitRow.replace]
      · simp [deviation, profile, base, rareQuitRow, QuitProfile.replace,
          QuitRow.replace, hkj]
    have hreward : ∀ t,
        quittingRewardPart G (deviation t) j ≤
          SoloPayoff G j * QuitProbability G (deviation t) := by
      intro t
      rw [hrow, quittingRewardPart_allContinue_replace]
      rw [quitProbability_allContinue_replace]
      ring_nf
      exact le_rfl
    have hdeviation : QuitPayoff G deviation j ≤ SoloPayoff G j :=
      quitPayoff_le_of_nonnegative_rewardPart_le G deviation j (SoloPayoff G j) hj
        hreward
    rw [hbasePayoff]
    exact hdeviation.trans (by simp [SoloPayoff]; linarith)
  · have hbaseN : base n = (0 : Set.Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      simp [base, rareQuitRow, QuitRow.replace, hnj]
    have hnzero : base.replace G n 0 = base := by
      rw [← hbaseN]
      exact QuitRow.replace_self G base n
    have hrow : ∀ t, deviation t = base.replace G n (q t) := fun _ => rfl
    have hvanish : Tendsto (tailSurvival G deviation 0) atTop (nhds 0) := by
      apply squeeze_zero
      · intro t
        exact Finset.prod_nonneg fun l _ =>
          sub_nonneg.mpr (quitProbability_mem_Icc G _).2
      · intro t
        calc
          tailSurvival G deviation 0 t ≤
              ∏ l ∈ Finset.range t, (1 - av) := by
            apply Finset.prod_le_prod
            · intro l hl
              exact sub_nonneg.mpr (quitProbability_mem_Icc G _).2
            · intro l hl
              rw [hrow]
              have hs := one_sub_quitProbability_replace G base n (q l)
              rw [hnzero, one_sub_quitProbability_rareQuitRow] at hs
              simp only [Nat.zero_add]
              rw [hs]
              exact mul_le_of_le_one_left (sub_nonneg.mpr (le_of_lt hav1))
                (by linarith [(q l).property.1])
          _ = (1 - av) ^ t := by simp
      · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
    have hmass := tsum_tailSurvival_mul_quitProbability_eq_one G deviation 0 hvanish
    let rewardJ := G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n
    let C := rewardJ + 2 * M * av
    have hcomm : base.replace G n 1 =
        (QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) n 1).replace G j a := by
      exact QuitRow.replace_comm G _ (Ne.symm hnj) a 1
    have hforced : quittingRewardPart G (base.replace G n 1) n ≤
        SoloPayoff G n + 2 * M * av := by
      rw [hcomm, quittingRewardPart_replace_affine]
      have hsoloJZero :
          (QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) n 1).replace G j 0 =
            QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) n 1 := by
        have hjzero :
            QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) n 1 j = 0 := by
          apply Subtype.ext
          simp [QuitRow.replace, Ne.symm hnj]
        simpa only [hjzero] using QuitRow.replace_self G
          (QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) n 1) j
      rw [hsoloJZero, QuitRow.zero_replace_one, quittingRewardPart_soloQuitRow]
      let both :=
        (QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) n 1).replace G j 1
      have hbothAbs : |quittingRewardPart G both n| ≤ M := by
        calc
          |quittingRewardPart G both n| ≤ M * QuitProbability G both :=
            abs_quittingRewardPart_le G both n (fun A => le_of_lt (hM.2.2 A n))
          _ ≤ M * 1 := mul_le_mul_of_nonneg_left
            (quitProbability_mem_Icc G both).2 hM0
          _ = M := mul_one M
      have hboth : quittingRewardPart G both n ≤ M :=
        (le_abs_self _).trans hbothAbs
      have hsoloLower : -M < SoloPayoff G n :=
        neg_lt_of_abs_lt (hM.2.2 ⟨{n}, Finset.singleton_nonempty n⟩ n)
      change av * quittingRewardPart G both n +
          (1 - av) * SoloPayoff G n ≤ SoloPayoff G n + 2 * M * av
      nlinarith [mul_nonneg (le_of_lt hav0) (le_of_lt hMpos)]
    have hforcedC : quittingRewardPart G (base.replace G n 1) n ≤ C := by
      exact hforced.trans (by dsimp only [C, rewardJ]; linarith [hcross n hnj])
    have hbaseReward : quittingRewardPart G base n = av * rewardJ := by
      simpa only [base, a] using quittingRewardPart_rareQuitRow G j n a
    have hbaseC : quittingRewardPart G base n ≤ av * C := by
      rw [hbaseReward]
      dsimp only [C]
      nlinarith [mul_nonneg (le_of_lt hav0) (mul_nonneg hM0 (le_of_lt hav0))]
    have hrewards : ∀ t,
        quittingRewardPart G (deviation t) n ≤ C * QuitProbability G (deviation t) := by
      intro t
      rw [hrow, quittingRewardPart_replace_affine, hnzero]
      have hs := one_sub_quitProbability_replace G base n (q t)
      rw [hnzero, one_sub_quitProbability_rareQuitRow] at hs
      have hquit : QuitProbability G (base.replace G n (q t)) =
          (q t : ℝ) + (1 - (q t : ℝ)) * av := by
        change 1 - QuitProbability G (base.replace G n (q t)) =
          (1 - (q t : ℝ)) * (1 - av) at hs
        linarith
      rw [hquit]
      have hfirst := mul_le_mul_of_nonneg_left hforcedC (q t).property.1
      have hsecond := mul_le_mul_of_nonneg_left hbaseC
        (sub_nonneg.mpr (q t).property.2)
      nlinarith
    have hdeviation : QuitPayoff G deviation n ≤ C :=
      quitPayoff_le_of_rewardPart_le G deviation n C hrewards (by simpa using hmass)
    rw [hbasePayoff]
    dsimp only [C, rewardJ] at hdeviation
    exact hdeviation.trans (by linarith)

/-- If stationary approximate equilibria fail, some normal player has positive solo payoff. -/
private theorem exists_positive_normalPlayer_of_not_stationary
    (G : QuittingGame) (hstationary : ¬HasStationaryApproximateEquilibria G) :
    ∃ n, IsNormalPlayer G n ∧ 0 < SoloPayoff G n := by
  classical
  by_contra hpositive
  push Not at hpositive
  have hsolo : ∀ n, SoloPayoff G n ≤ 0 := by
    intro n
    by_cases hnormal : IsNormalPlayer G n
    · exact hpositive n hnormal
    · exact (lemma3 G n hnormal).1.le
  apply hstationary
  intro ε hε
  let zeroRow : QuitRow G := fun _ => (0 : Set.Icc (0 : ℝ) 1)
  refine ⟨zeroRow, ?_⟩
  intro n q
  let deviation : QuitProfile G :=
    QuitProfile.replace G (fun _ : ℕ => zeroRow) n q
  have hrow : ∀ t, deviation t = zeroRow.replace G n (q t) := fun _ => rfl
  have hreward : ∀ t,
      quittingRewardPart G (deviation t) n ≤ 0 * QuitProbability G (deviation t) := by
    intro t
    rw [hrow, quittingRewardPart_allContinue_replace]
    simpa only [zero_mul] using
      mul_nonpos_of_nonneg_of_nonpos (q t).property.1 (hsolo n)
  have hdeviation : QuitPayoff G deviation n ≤ 0 :=
    quitPayoff_le_of_nonnegative_rewardPart_le G deviation n 0 (by norm_num) hreward
  have hzeroPayoff : QuitPayoff G (fun _ => zeroRow) n = 0 := by
    change (∑' k, tailSurvival G (fun _ => zeroRow) 0 k *
      quittingRewardPart G zeroRow n) = 0
    rw [show quittingRewardPart G zeroRow n = 0 by
      simpa only [zeroRow] using quittingRewardPart_allContinue G n]
    simp
  change QuitPayoff G deviation n ≤ QuitPayoff G (fun _ => zeroRow) n + ε
  rw [hzeroPayoff]
  linarith

/-- A positive normal solo quitter must strictly harm another normal player. -/
private theorem exists_harmed_normalPlayer_of_positive
    (G : QuittingGame) (hstationary : ¬HasStationaryApproximateEquilibria G)
    (j : G.Player) (_hjnormal : IsNormalPlayer G j) (hjpositive : 0 < SoloPayoff G j) :
    ∃ n, n ≠ j ∧ IsNormalPlayer G n ∧
      G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n < SoloPayoff G n := by
  by_contra hharmed
  push Not at hharmed
  have hcross : ∀ n, n ≠ j →
      SoloPayoff G n ≤ G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n := by
    intro n hnj
    by_cases hnnormal : IsNormalPlayer G n
    · exact hharmed n hnj hnnormal
    · exact (lt_of_not_ge hnnormal).le.trans
        ((lemma3 G n hnnormal).2 j (Ne.symm hnj))
  exact hstationary
    (hasStationaryApproximateEquilibria_of_soloPayoff_nonnegative G j hjpositive.le hcross)

/-- Under failure of stationarity, a normal player harming no normal player is negative. -/
private theorem soloPayoff_negative_of_no_harmed_normalPlayer
    (G : QuittingGame) (hstationary : ¬HasStationaryApproximateEquilibria G)
    (j : G.Player)
    (hnoHarm : ∀ n, n ≠ j → IsNormalPlayer G n →
      SoloPayoff G n ≤ G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n) :
    SoloPayoff G j < 0 := by
  by_contra hjnegative
  have hjnonnegative : 0 ≤ SoloPayoff G j := le_of_not_gt hjnegative
  have hcross : ∀ n, n ≠ j →
      SoloPayoff G n ≤ G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n := by
    intro n hnj
    by_cases hnnormal : IsNormalPlayer G n
    · exact hnoHarm n hnj hnnormal
    · exact (lt_of_not_ge hnnormal).le.trans
        ((lemma3 G n hnnormal).2 j (Ne.symm hnj))
  exact hstationary
    (hasStationaryApproximateEquilibria_of_soloPayoff_nonnegative G j hjnonnegative hcross)

/-- Every normal solo quitter strictly harms another normal player. -/
def EveryNormalSoloQuitterHarmsNormal (G : QuittingGame) : Prop :=
  ∀ j, IsNormalPlayer G j → ∃ k, k ≠ j ∧ IsNormalPlayer G k ∧
    G.reward ⟨{j}, Finset.singleton_nonempty j⟩ k < SoloPayoff G k

/-- The uniform `ρ` conclusion printed in Lemma 5(2). -/
def IsUniformRho (G : QuittingGame) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ ∀ r p, IsRational G ρ r →
    p ∈ EpsilonRow G ρ r →
    let y := QuittingOneStagePayoff G r p
    ρ * QuitProbability G p ≤ ‖r - y‖ ∧ QuitProbability G p ≤ 1 - ρ

/-- Use one stationary row through stage `M`, then switch to a punishment profile. -/
def StationaryPrefixThenPunish (G : QuittingGame) (p : QuitRow G)
    (M : ℕ) (punishment : QuitProfile G) : QuitProfile G :=
  fun t => if t ≤ M then p else punishment (t - (M + 1))

/-- The punishment profile holds player `j` to `χʲ + δ`. -/
def IsPunishmentWithin (G : QuittingGame) (j : G.Player) (δ : ℝ)
    (punishment : QuitProfile G) : Prop :=
  ∀ q : ℕ → Set.Icc (0 : ℝ) 1,
    QuitPayoff G (punishment.replace G j q) j ≤ MinMaxQuit G j + δ

/-- The infimum definition of `χʲ` supplies a punishment within every positive slack. -/
private theorem exists_punishmentWithin (G : QuittingGame) (j : G.Player)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ punishment : QuitProfile G, IsPunishmentWithin G j δ punishment := by
  obtain ⟨M, hM⟩ := exists_quittingPayoffDifferenceBound G
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.1
  have hpayoffBound : ∀ profile : QuitProfile G,
      |QuitPayoff G profile j| ≤ M := fun profile =>
    abs_quitPayoff_le G profile j hM0 (fun A => le_of_lt (hM.2.2 A j))
  have hinnerAbove : ∀ profile : QuitProfile G, BddAbove (range fun deviation :
      ℕ → Set.Icc (0 : ℝ) 1 => QuitPayoff G (profile.replace G j deviation) j) := by
    intro profile
    refine ⟨M, ?_⟩
    rintro _ ⟨deviation, rfl⟩
    exact (le_abs_self _).trans (hpayoffBound _)
  have hnear : MinMaxQuit G j < MinMaxQuit G j + δ := by linarith
  rw [MinMaxQuit] at hnear
  obtain ⟨punishment, hpunishment⟩ := exists_lt_of_ciInf_lt hnear
  refine ⟨punishment, ?_⟩
  intro deviation
  exact (le_ciSup (hinnerAbove punishment) deviation).trans hpunishment.le

/-- A calibrated punishment is itself within the same slack below the min-max value. -/
private def IsCalibratedPunishmentWithin (G : QuittingGame) (j : G.Player) (δ : ℝ)
    (punishment : QuitProfile G) : Prop :=
  IsPunishmentWithin G j δ punishment ∧
    MinMaxQuit G j - δ ≤ QuitPayoff G punishment j

/-- Approximate infimum and supremum choices give a calibrated punishment profile. -/
private theorem exists_calibratedPunishmentWithin
    (G : QuittingGame) (j : G.Player) {δ : ℝ} (hδ : 0 < δ) :
    ∃ punishment : QuitProfile G, IsCalibratedPunishmentWithin G j δ punishment := by
  classical
  obtain ⟨M, hM⟩ := exists_quittingPayoffDifferenceBound G
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.1
  have hpayoffBound : ∀ profile : QuitProfile G,
      |QuitPayoff G profile j| ≤ M := fun profile =>
    abs_quitPayoff_le G profile j hM0 (fun A => le_of_lt (hM.2.2 A j))
  let upper : QuitProfile G → ℝ := fun profile =>
    ⨆ deviation : ℕ → Set.Icc (0 : ℝ) 1,
      QuitPayoff G (profile.replace G j deviation) j
  have hinnerAbove : ∀ profile : QuitProfile G, BddAbove (range fun deviation :
      ℕ → Set.Icc (0 : ℝ) 1 => QuitPayoff G (profile.replace G j deviation) j) := by
    intro profile
    refine ⟨M, ?_⟩
    rintro _ ⟨deviation, rfl⟩
    exact (le_abs_self _).trans (hpayoffBound _)
  have houterBelow : BddBelow (range upper) := by
    refine ⟨-M, ?_⟩
    rintro _ ⟨profile, rfl⟩
    let deviation : ℕ → Set.Icc (0 : ℝ) 1 := fun i => profile i j
    have hself : profile.replace G j deviation = profile := by
      funext i n
      by_cases hnj : n = j
      · subst n
        simp [QuitProfile.replace, deviation]
      · simp [QuitProfile.replace, hnj]
    calc
      -M ≤ QuitPayoff G profile j := neg_le_of_abs_le (hpayoffBound profile)
      _ = QuitPayoff G (profile.replace G j deviation) j := by rw [hself]
      _ ≤ upper profile := le_ciSup (hinnerAbove profile) deviation
  have hnear : MinMaxQuit G j < MinMaxQuit G j + δ / 2 := by linarith
  have hnearInf : (⨅ profile, upper profile) < (⨅ profile, upper profile) + δ / 2 := by
    simpa only [MinMaxQuit, upper] using hnear
  obtain ⟨base, hbase⟩ := exists_lt_of_ciInf_lt hnearInf
  have hbase' : upper base < MinMaxQuit G j + δ / 2 := by
    simpa only [MinMaxQuit, upper] using hbase
  have hminmaxLe : MinMaxQuit G j ≤ upper base := by
    rw [MinMaxQuit]
    exact ciInf_le houterBelow base
  have hsupNear : upper base - δ / 2 < upper base := by linarith
  obtain ⟨response, hresponse⟩ := exists_lt_of_lt_ciSup hsupNear
  let punishment := base.replace G j response
  have hreplace (deviation : ℕ → Set.Icc (0 : ℝ) 1) :
      punishment.replace G j deviation = base.replace G j deviation := by
    funext i n
    simp only [punishment, QuitProfile.replace]
    split_ifs <;> rfl
  refine ⟨punishment, ?_, ?_⟩
  · intro deviation
    rw [hreplace]
    exact (le_ciSup (hinnerAbove base) deviation).trans (hbase'.le.trans (by linarith))
  · have hpayoff : QuitPayoff G punishment j =
        QuitPayoff G (base.replace G j response) j := rfl
    rw [hpayoff]
    linarith

/-- Follow a supplied quitting profile for `T` stages, then start a punishment profile. -/
private def PrefixThenPunish (G : QuittingGame) (p : QuitProfile G)
    (T : ℕ) (punishment : QuitProfile G) : QuitProfile G :=
  fun i => if i < T then p i else punishment (i - T)

@[simp] private theorem PrefixThenPunish.apply_of_lt
    (G : QuittingGame) (p : QuitProfile G) (T : ℕ)
    (punishment : QuitProfile G) {i : ℕ} (hi : i < T) :
    PrefixThenPunish G p T punishment i = p i := by
  simp [PrefixThenPunish, hi]

@[simp] private theorem PrefixThenPunish.apply_add
    (G : QuittingGame) (p : QuitProfile G) (T : ℕ)
    (punishment : QuitProfile G) (i : ℕ) :
    PrefixThenPunish G p T punishment (T + i) = punishment i := by
  simp [PrefixThenPunish]

/-- A finite quitting payoff depends only on the displayed finite prefix. -/
private theorem finiteQuittingPayoff_congr_prefix (G : QuittingGame) (k : ℕ)
    (x : Payoff G.Player) (p q : QuitProfile G)
    (hpq : ∀ i, i < k → p i = q i) :
    finiteQuittingPayoff G k x p = finiteQuittingPayoff G k x q := by
  induction k generalizing p q with
  | zero => rfl
  | succ k ih =>
      simp only [finiteQuittingPayoff]
      rw [hpq 0 (by omega)]
      congr 1
      apply ih
      intro i hi
      exact hpq (i + 1) (by omega)

/-- At the switching stage, the spliced profile's tail is exactly the punishment payoff. -/
private theorem quitTailPayoff_prefixThenPunish_at_switch
    (G : QuittingGame) (p : QuitProfile G) (T : ℕ)
    (punishment : QuitProfile G) :
    QuitTailPayoff G (PrefixThenPunish G p T punishment) T =
      QuitPayoff G punishment := by
  funext n
  apply tsum_congr
  intro k
  change tailSurvival G (PrefixThenPunish G p T punishment) T k *
      quittingRewardPart G (PrefixThenPunish G p T punishment (T + k)) n =
    tailSurvival G punishment 0 k * quittingRewardPart G (punishment (0 + k)) n
  have hsurvival : tailSurvival G (PrefixThenPunish G p T punishment) T k =
      tailSurvival G punishment 0 k := by
    rw [tailSurvival, tailSurvival]
    apply Finset.prod_congr rfl
    intro i _hi
    rw [PrefixThenPunish.apply_add]
    simp
  rw [hsurvival, PrefixThenPunish.apply_add]
  simp

/-- The generated profile has the supplied finite prefix and the punishment as terminal value. -/
private theorem quitPayoff_prefixThenPunish_eq_finite
    (G : QuittingGame) (p : QuitProfile G) (T : ℕ)
    (punishment : QuitProfile G) :
    QuitPayoff G (PrefixThenPunish G p T punishment) =
      finiteQuittingPayoff G T (QuitPayoff G punishment) p := by
  rw [QuitPayoff]
  rw [quitTailPayoff_eq_finiteQuittingPayoff G
    (PrefixThenPunish G p T punishment) 0 T]
  rw [show 0 + T = T by omega, quitTailPayoff_prefixThenPunish_at_switch]
  apply finiteQuittingPayoff_congr_prefix
  intro i hi
  simp only [Nat.zero_add]
  exact PrefixThenPunish.apply_of_lt G p T punishment hi

/-- Unilateral replacement of a spliced profile splits into prefix and shifted-tail replacements. -/
private theorem PrefixThenPunish.replace (G : QuittingGame) (p : QuitProfile G)
    (T : ℕ) (punishment : QuitProfile G) (n : G.Player)
    (deviation : ℕ → Set.Icc (0 : ℝ) 1) :
    (PrefixThenPunish G p T punishment).replace G n deviation =
      PrefixThenPunish G (fun i => (p i).replace G n (deviation i)) T
        (punishment.replace G n fun i => deviation (T + i)) := by
  funext i k
  by_cases hi : i < T
  · simp [PrefixThenPunish, QuitProfile.replace, QuitRow.replace, hi]
  · have hsplit : T + (i - T) = i := by omega
    simp only [PrefixThenPunish, hi, if_false, QuitProfile.replace]
    split_ifs with hkn
    · subst k
      rw [hsplit]
    · rfl

/-- A unilateral deviation from the generated profile has the exact finite-prefix evaluation. -/
private theorem quitPayoff_prefixThenPunish_replace_eq_finite
    (G : QuittingGame) (p : QuitProfile G) (T : ℕ)
    (punishment : QuitProfile G) (n : G.Player)
    (deviation : ℕ → Set.Icc (0 : ℝ) 1) :
    QuitPayoff G ((PrefixThenPunish G p T punishment).replace G n deviation) =
      finiteQuittingPayoff G T
        (QuitPayoff G (punishment.replace G n fun i => deviation (T + i)))
        (fun i => (p i).replace G n (deviation i)) := by
  rw [PrefixThenPunish.replace]
  exact quitPayoff_prefixThenPunish_eq_finite G _ T _

/-- A unilateral mixed quitting decision is the affine mixture of its two pure endpoints. -/
private theorem quittingOneStagePayoff_replace_eq_endpoints
    (G : QuittingGame) (r : Payoff G.Player) (p : QuitRow G)
    (n : G.Player) (q : Set.Icc (0 : ℝ) 1) :
    QuittingOneStagePayoff G r (p.replace G n q) n =
      (q : ℝ) * ForcedQuitPayoff G p n +
        (1 - (q : ℝ)) * ForcedContinuePayoff G r p n := by
  change (1 - QuitProbability G (p.replace G n q)) * r n +
      quittingRewardPart G (p.replace G n q) n =
    (q : ℝ) * ((1 - QuitProbability G (p.replace G n 1)) * 0 +
      quittingRewardPart G (p.replace G n 1) n) +
    (1 - (q : ℝ)) * ((1 - QuitProbability G (p.replace G n 0)) * r n +
      quittingRewardPart G (p.replace G n 0) n)
  rw [one_sub_quitProbability_replace, quitProbability_replace_one]
  rw [quittingRewardPart_replace_affine]
  ring_nf

/-- In an `η`-equilibrium row, forcing quit gains at most `η` over its mixed value. -/
private theorem EpsilonRow.forcedQuitPayoff_le_oneStage_add
    (G : QuittingGame) {r : Payoff G.Player} {p : QuitRow G} {η : ℝ}
    (hp : p ∈ EpsilonRow G η r) (hη : 0 ≤ η) (n : G.Player) :
    ForcedQuitPayoff G p n ≤ QuittingOneStagePayoff G r p n + η := by
  have hcurrent := quittingOneStagePayoff_replace_eq_endpoints G r p n (p n)
  rw [QuitRow.replace_self] at hcurrent
  by_cases hone : (p n : ℝ) = 1
  · rw [hone] at hcurrent
    norm_num at hcurrent
    linarith
  · have hlt : (p n : ℝ) < 1 := lt_of_le_of_ne (p n).property.2 hone
    have hendpoint := hp.2 n hlt
    have hp0 := (p n).property.1
    have hp1 := (p n).property.2
    nlinarith

/-- The forced-continue increment in an `η`-equilibrium row is at most `η`. -/
private theorem EpsilonRow.forcedContinue_sub_oneStage_le
    (G : QuittingGame) {r : Payoff G.Player} {p : QuitRow G} {η : ℝ}
    (hp : p ∈ EpsilonRow G η r) (hη : 0 ≤ η) (n : G.Player) :
    ForcedContinuePayoff G r p n - QuittingOneStagePayoff G r p n ≤ η := by
  have hcurrent := quittingOneStagePayoff_replace_eq_endpoints G r p n (p n)
  rw [QuitRow.replace_self] at hcurrent
  by_cases hzero : (p n : ℝ) = 0
  · rw [hzero] at hcurrent
    norm_num at hcurrent
    linarith
  · have hpos : 0 < (p n : ℝ) := lt_of_le_of_ne (p n).property.1 (Ne.symm hzero)
    have hendpoint := hp.1 n hpos
    have hp0 := (p n).property.1
    have hp1 := (p n).property.2
    nlinarith

/-- A supported quit action lies at most `η` below its mixed row value. -/
private theorem EpsilonRow.oneStage_sub_forcedQuitPayoff_le_of_pos
    (G : QuittingGame) {r : Payoff G.Player} {p : QuitRow G} {η : ℝ}
    (hp : p ∈ EpsilonRow G η r) (hη : 0 ≤ η) (n : G.Player)
    (hpos : 0 < (p n : ℝ)) :
    QuittingOneStagePayoff G r p n - ForcedQuitPayoff G p n ≤ η := by
  have hcurrent := quittingOneStagePayoff_replace_eq_endpoints G r p n (p n)
  rw [QuitRow.replace_self] at hcurrent
  have hendpoint := hp.1 n hpos
  have hp0 := (p n).property.1
  have hp1 := (p n).property.2
  nlinarith

/-- A supported continue action lies at most `η` below its mixed row value. -/
private theorem EpsilonRow.oneStage_sub_forcedContinuePayoff_le_of_lt_one
    (G : QuittingGame) {r : Payoff G.Player} {p : QuitRow G} {η : ℝ}
    (hp : p ∈ EpsilonRow G η r) (hη : 0 ≤ η) (n : G.Player)
    (hlt : (p n : ℝ) < 1) :
    QuittingOneStagePayoff G r p n - ForcedContinuePayoff G r p n ≤ η := by
  have hcurrent := quittingOneStagePayoff_replace_eq_endpoints G r p n (p n)
  rw [QuitRow.replace_self] at hcurrent
  have hendpoint := hp.2 n hlt
  have hp0 := (p n).property.1
  have hp1 := (p n).property.2
  nlinarith

/-- Changing the continuation vector changes a forced-continue payoff by its survival factor. -/
private theorem forcedContinuePayoff_sub
    (G : QuittingGame) (r s : Payoff G.Player) (p : QuitRow G) (n : G.Player) :
    ForcedContinuePayoff G r p n - ForcedContinuePayoff G s p n =
      (1 - QuitProbability G (p.replace G n 0)) * (r n - s n) := by
  simp only [ForcedContinuePayoff, QuittingOneStagePayoff]
  ring_nf

/-- A cumulative forced-continue ledger is a supermartingale budget for every deviation. -/
private theorem finiteQuittingPayoff_replace_le_of_ledger
    (G : QuittingGame) (n : G.Player) {k : ℕ} {η K : ℝ}
    (hη : 0 ≤ η) (r : ℕ → Payoff G.Player) (p : QuitProfile G)
    (deviation : ℕ → Set.Icc (0 : ℝ) 1) (terminal : Payoff G.Player)
    (ledger : ℕ → ℝ)
    (hrow : ∀ i, i < k → p i ∈ EpsilonRow G η (r (i + 1)))
    (hvalue : ∀ i, i < k → r i = QuittingOneStagePayoff G (r (i + 1)) (p i))
    (hledger : ∀ i, i < k → ledger (i + 1) = ledger i +
      (ForcedContinuePayoff G (r (i + 1)) (p i) n - r i n))
    (hcontinueBudget : ∀ i, i ≤ k → 0 ≤ K - ledger i)
    (hquitBudget : ∀ i, i < k → η ≤ K - ledger i)
    (hterminal : terminal n ≤ r k n + K - ledger k) :
    finiteQuittingPayoff G k terminal
        (fun i => (p i).replace G n (deviation i)) n ≤
      r 0 n + K - ledger 0 := by
  induction k generalizing r p deviation ledger with
  | zero =>
      simpa [finiteQuittingPayoff] using hterminal
  | succ k ih =>
      let tail : Payoff G.Player := finiteQuittingPayoff G k terminal
        (fun i => (p (i + 1)).replace G n (deviation (i + 1)))
      have htail : tail n ≤ r 1 n + K - ledger 1 := by
        apply ih (r := fun i => r (i + 1)) (p := fun i => p (i + 1))
          (deviation := fun i => deviation (i + 1)) (ledger := fun i => ledger (i + 1))
        · intro i hi
          exact hrow (i + 1) (by omega)
        · intro i hi
          simpa only [Nat.add_assoc] using hvalue (i + 1) (by omega)
        · intro i hi
          simpa only [Nat.add_assoc] using hledger (i + 1) (by omega)
        · intro i hi
          exact hcontinueBudget (i + 1) (by omega)
        · intro i hi
          exact hquitBudget (i + 1) (by omega)
        · simpa only [Nat.add_assoc] using hterminal
      have hstage := hrow 0 (by omega)
      have hstageValue := hvalue 0 (by omega)
      have hquit : ForcedQuitPayoff G (p 0) n ≤ r 0 n + K - ledger 0 := by
        calc
          ForcedQuitPayoff G (p 0) n ≤
              QuittingOneStagePayoff G (r 1) (p 0) n + η :=
            EpsilonRow.forcedQuitPayoff_le_oneStage_add G hstage hη n
          _ = r 0 n + η := by rw [← hstageValue]
          _ ≤ r 0 n + K - ledger 0 := by
            linarith [hquitBudget 0 (by omega)]
      let survival := 1 - QuitProbability G ((p 0).replace G n 0)
      have hsurvival0 : 0 ≤ survival := by
        exact sub_nonneg.mpr (quitProbability_mem_Icc G _).2
      have hsurvival1 : survival ≤ 1 := by
        linarith [(quitProbability_mem_Icc G ((p 0).replace G n 0)).1]
      have hcontinue : ForcedContinuePayoff G tail (p 0) n ≤
          r 0 n + K - ledger 0 := by
        have htailDifference : tail n - r 1 n ≤ K - ledger 1 := by
          linarith
        have hscaled : survival * (tail n - r 1 n) ≤ K - ledger 1 := by
          exact (mul_le_mul_of_nonneg_left htailDifference hsurvival0).trans
            (mul_le_of_le_one_left (hcontinueBudget 1 (by omega)) hsurvival1)
        have hshift := forcedContinuePayoff_sub G tail (r 1) (p 0) n
        change ForcedContinuePayoff G tail (p 0) n -
          ForcedContinuePayoff G (r 1) (p 0) n =
            survival * (tail n - r 1 n) at hshift
        have hledgerZero := hledger 0 (by omega)
        linarith
      simp only [finiteQuittingPayoff]
      change QuittingOneStagePayoff G tail ((p 0).replace G n (deviation 0)) n ≤ _
      rw [quittingOneStagePayoff_replace_eq_endpoints]
      calc
        (deviation 0 : ℝ) * ForcedQuitPayoff G (p 0) n +
            (1 - (deviation 0 : ℝ)) * ForcedContinuePayoff G tail (p 0) n ≤
            (deviation 0 : ℝ) * (r 0 n + K - ledger 0) +
              (1 - (deviation 0 : ℝ)) * (r 0 n + K - ledger 0) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hquit (deviation 0).property.1)
            (mul_le_mul_of_nonneg_left hcontinue
              (sub_nonneg.mpr (deviation 0).property.2))
        _ = r 0 n + K - ledger 0 := by ring

/-- Approximate equilibria made from a stationary prefix and a min-max punishment. -/
def HasStationarilyGeneratedApproximateEquilibria (G : QuittingGame) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ (p : QuitRow G) (M : ℕ)
    (j : G.Player) (punishment : QuitProfile G),
      1 < M ∧ IsPunishmentWithin G j δ punishment ∧
      IsQuitEpsilonEquilibrium G (ε + δ)
        (StationaryPrefixThenPunish G p M punishment)

/-- A vector lies within `ε` of the feasible vectors. -/
def NearFeasible (G : QuittingGame) (ε : ℝ) (r : Payoff G.Player) : Prop :=
  ∃ z, Feasible G z ∧ ‖r - z‖ ≤ ε

/--
Lemma 5 as printed in 2007, with its free `x` repaired to `r`: excluding stationary
and instant approximate equilibria gives the sign pattern in (1) and one global `ρ` in (2).
-/
theorem lemma5 (G : QuittingGame)
    (hstationary : ¬HasStationaryApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    (∃ l, IsNormalPlayer G l ∧ 0 < SoloPayoff G l) ∧
      EveryNormalSoloQuitterHarmsNormal G ∧
      ∃ ρ, IsUniformRho G ρ := by
  sorry

/--
Simon (2012), Lemma 2.1, correcting the 2007 Lemma 5: the strategic hypothesis excludes
stationarily generated approximate equilibria, and `ρ < 1` is uniform for continuation
vectors within distance one of the feasible set.
-/
theorem lemma5_corrected_2012 (G : QuittingGame)
    (hstationary : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    (∃ l, IsNormalPlayer G l ∧ 0 < SoloPayoff G l) ∧
      EveryNormalSoloQuitterHarmsNormal G ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ r, NearFeasible G 1 r →
        IsRational G ρ r → ∀ p, p ∈ EpsilonRow G ρ r →
          let y := QuittingOneStagePayoff G r p
          ρ * QuitProbability G p ≤ ‖r - y‖ ∧ QuitProbability G p ≤ 1 - ρ := by
  sorry

/-!
Simon (2012, p. 185) explicitly says that the 2007 statement wrote "stationary
approximate equilibria" although its proof uses the stronger stationarily generated
notion. It also restores the omitted restriction to the compact set of vectors within
distance one of the feasible vectors. The local Bool example below refutes one inference
from the old proof; it does not refute the full conclusion of `lemma5`.
-/

namespace NegativeQuitterVertex

/-- The two-player table in which every terminal payoff is `(-1,1)`. -/
abbrev game : QuittingGame where
  Player := Bool
  reward := fun _ n => if n then 1 else -1

/-- The terminal payoff vector, also used as the continuation vector. -/
abbrev continuation : Payoff game.Player := fun n => if n then 1 else -1

/-- The negative-payoff player quits surely while the other player continues. -/
abbrev row : QuitRow game := SoloQuitRow game false

private theorem reward_eq_continuation
    (A : {A : Finset game.Player // A.Nonempty}) :
    game.reward A = continuation := by
  funext n
  rfl

/-- In this table, any surely absorbing row pays the fixed terminal vector. -/
private theorem oneStagePayoff_eq_continuation_of_sureQuit
    (r : Payoff game.Player) (p : QuitRow game)
    (hp : QuitProbability game p = 1) :
    QuittingOneStagePayoff game r p = continuation := by
  funext n
  simp only [QuittingOneStagePayoff]
  rw [hp]
  simp only [sub_self, zero_mul, zero_add]
  calc
    (∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
        CoalitionProbability game p A * game.reward ⟨A, hA⟩ n else 0) =
        (∑ A ∈ Finset.univ.powerset, if _hA : A.Nonempty then
          CoalitionProbability game p A else 0) * continuation n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _hA
      split_ifs with hnonempty
      · rw [reward_eq_continuation ⟨A, hnonempty⟩]
      · simp
    _ = QuitProbability game p * continuation n := by
      rw [nonemptyCoalitionMass_eq_quitProbability]
    _ = continuation n := by rw [hp, one_mul]

private theorem oneStagePayoff_allContinue :
    QuittingOneStagePayoff game continuation
      (fun _ => (0 : Set.Icc (0 : ℝ) 1)) = continuation := by
  funext n
  change (1 - QuitProbability game (fun _ => (0 : Set.Icc (0 : ℝ) 1))) *
    continuation n +
      quittingRewardPart game (fun _ => (0 : Set.Icc (0 : ℝ) 1)) n = continuation n
  rw [quittingRewardPart_allContinue]
  simp [QuitProbability]

/-- The displayed row is a fixed point of the one-stage correspondence. -/
theorem oneStagePayoff_eq_continuation :
    QuittingOneStagePayoff game continuation row = continuation := by
  apply oneStagePayoff_eq_continuation_of_sureQuit
  have h := quitProbability_replace_one game
    (fun _ => (0 : Set.Icc (0 : ℝ) 1)) false
  simpa [row, QuitRow.zero_replace_one] using h

/-- The displayed row belongs to `E₀` at the fixed continuation vector. -/
theorem row_mem_epsilonRow_zero : row ∈ EpsilonRow game 0 continuation := by
  constructor
  · intro n hn
    cases n with
    | false =>
        have hpSelf : row.replace game false 1 = row := by
          simpa [row, SoloQuitRow] using QuitRow.replace_self game row false
        have hpZero : row.replace game false 0 =
            fun _ => (0 : Set.Icc (0 : ℝ) 1) := by
          funext k
          cases k <;> simp [row, SoloQuitRow, QuitRow.replace]
        have hpSure : QuitProbability game row = 1 := by
          have h := quitProbability_replace_one game
            (fun _ => (0 : Set.Icc (0 : ℝ) 1)) false
          simpa [row, QuitRow.zero_replace_one] using h
        rw [ForcedQuitPayoff, ForcedContinuePayoff, hpSelf, hpZero]
        rw [oneStagePayoff_eq_continuation_of_sureQuit 0 row hpSure]
        rw [oneStagePayoff_allContinue]
        norm_num [continuation]
    | true => simp [row, SoloQuitRow] at hn
  · intro n hn
    cases n with
    | false => simp [row, SoloQuitRow] at hn
    | true =>
        have hpSelf : row.replace game true 0 = row := by
          simpa [row, SoloQuitRow] using QuitRow.replace_self game row true
        have hpSure : QuitProbability game (row.replace game true 1) = 1 :=
          quitProbability_replace_one game row true
        rw [ForcedContinuePayoff, ForcedQuitPayoff, hpSelf]
        rw [oneStagePayoff_eq_continuation]
        rw [oneStagePayoff_eq_continuation_of_sureQuit 0 _ hpSure]
        norm_num [continuation]

/-- At tolerance one, the continuation vector satisfies the rationality hypothesis. -/
theorem continuation_rational_one : IsRational game 1 continuation := by
  intro n
  have hminmax := minMaxQuit_le_max_solo_zero game n
  cases n with
  | false => simpa [continuation, SoloPayoff, game] using hminmax
  | true =>
      have h : MinMaxQuit game true ≤ 1 := by
        simpa [SoloPayoff, game] using hminmax
      norm_num [continuation]
      linarith

/-- The row absorbs surely. -/
theorem quitProbability_row : QuitProbability game row = 1 := by
  have h := quitProbability_replace_one game
    (fun _ => (0 : Set.Icc (0 : ℝ) 1)) false
  simpa [row, QuitRow.zero_replace_one] using h

/-- Repeating the negative fixed-point row is not a `1/2`-equilibrium. -/
theorem repeated_row_not_half_equilibrium :
    ¬IsQuitEpsilonEquilibrium game (1 / 2 : ℝ) (fun _ => row) := by
  intro hequilibrium
  let zeroProfile : QuitProfile game := fun _ _ => (0 : Set.Icc (0 : ℝ) 1)
  have hdeviation : QuitProfile.replace game (fun _ => row) false
      (fun _ => (0 : Set.Icc (0 : ℝ) 1)) = zeroProfile := by
    funext t n
    cases n <;> simp [zeroProfile, row, SoloQuitRow, QuitProfile.replace]
  have hzero : QuitPayoff game zeroProfile false = 0 := by
    change (∑' k, tailSurvival game zeroProfile 0 k *
      quittingRewardPart game (zeroProfile k) false) = 0
    have hreward : ∀ k, quittingRewardPart game (zeroProfile k) false = 0 := by
      intro k
      exact quittingRewardPart_allContinue game false
    simp_rw [hreward]
    simp
  have hbase : QuitPayoff game (fun _ => row) false = -1 := by
    have hrare : rareQuitRow game false 1 = row := by
      exact QuitRow.zero_replace_one game false
    rw [← hrare]
    simpa [game] using quitPayoff_constant_rareQuitRow game false false 1 (by norm_num)
  have hprofitable := hequilibrium false (fun _ => (0 : Set.Icc (0 : ℝ) 1))
  rw [hdeviation, hzero, hbase] at hprofitable
  norm_num at hprofitable

/-- This local witness does not satisfy Lemma 5's global nonstationarity hypothesis. -/
theorem hasStationaryApproximateEquilibria :
    HasStationaryApproximateEquilibria game := by
  apply hasStationaryApproximateEquilibria_of_soloPayoff_nonnegative game true
  · norm_num [SoloPayoff, game]
  · intro n hne
    cases n with
    | false => norm_num [SoloPayoff, game]
    | true => exact (hne rfl).elim

/--
Thus the local vertex inference used in the printed proof is false: even at a rational
`E₀` fixed point, repeating the row need not be an approximate equilibrium.  The game
itself does have another stationary equilibrium, as the preceding theorem records, so this
is not presented as a counterexample to the full conclusion of `lemma5`.
-/
theorem printed_vertex_inference_fails :
    IsRational game 1 continuation ∧ row ∈ EpsilonRow game 0 continuation ∧
      QuittingOneStagePayoff game continuation row = continuation ∧
      QuitProbability game row = 1 ∧
      ¬IsQuitEpsilonEquilibrium game (1 / 2 : ℝ) (fun _ => row) ∧
      HasStationaryApproximateEquilibria game :=
  ⟨continuation_rational_one, row_mem_epsilonRow_zero,
    oneStagePayoff_eq_continuation, quitProbability_row, repeated_row_not_half_equilibrium,
    hasStationaryApproximateEquilibria⟩

end NegativeQuitterVertex

/-! ### 4.4. Equivalences -/

/--
Divergence of `Σ_i q(p_i)` is expressed by unbounded finite partial sums.
-/
def HasUnboundedQuitMass (G : QuittingGame) (p : QuitProfile G) : Prop :=
  ∀ B : ℝ, ∃ k, B ≤ ∑ i ∈ Finset.range k, QuitProbability G (p i)

/-- The supplied rows themselves generate the displayed orbit of `F_η`. -/
def GeneratesFRowOrbit (G : QuittingGame) (η : ℝ) (p : QuitProfile G) : Prop :=
  ∀ i, p i ∈ EpsilonRow G η (QuitTailPayoff G p (i + 1))

/-- A generated row orbit has the corresponding set-valued `F_η` orbit relation. -/
theorem GeneratesFRowOrbit.tail_mem_fRow
    (G : QuittingGame) {η : ℝ} {p : QuitProfile G}
    (h : GeneratesFRowOrbit G η p) (i : ℕ) :
    QuitTailPayoff G p i ∈ FRow G η (QuitTailPayoff G p (i + 1)) := by
  refine ⟨p i, h i, ?_⟩
  exact (quitTailPayoff_eq_oneStage G p i).symm

/-- The probability that player `n` follows the prescribed continue action through stage `i`. -/
private def PlayerContinueProbability (G : QuittingGame) (p : QuitProfile G)
    (n : G.Player) (i : ℕ) : ℝ :=
  ∏ k ∈ Finset.range i, (1 - (p k n : ℝ))

/-- The probability of a union of independent quits is at most the sum of their marginals. -/
private theorem one_sub_prod_one_sub_le_sum {N : Type} (s : Finset N)
    (a : N → ℝ) (ha0 : ∀ n ∈ s, 0 ≤ a n) (ha1 : ∀ n ∈ s, a n ≤ 1) :
    1 - ∏ n ∈ s, (1 - a n) ≤ ∑ n ∈ s, a n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      rw [Finset.prod_insert hn, Finset.sum_insert hn]
      have hfactor0 : ∀ j ∈ s, 0 ≤ 1 - a j := fun j hj =>
        sub_nonneg.mpr (ha1 j (Finset.mem_insert_of_mem hj))
      have hfactor1 : ∀ j ∈ s, 1 - a j ≤ 1 := fun j hj => by
        linarith [ha0 j (Finset.mem_insert_of_mem hj)]
      have hprod0 : 0 ≤ ∏ j ∈ s, (1 - a j) := Finset.prod_nonneg hfactor0
      have hprod1 : ∏ j ∈ s, (1 - a j) ≤ 1 :=
        Finset.prod_le_one hfactor0 hfactor1
      have hrest := ih (fun j hj => ha0 j (Finset.mem_insert_of_mem hj))
        (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
      have hn0 := ha0 n (Finset.mem_insert_self n s)
      nlinarith

/-- Finite continue products are controlled by the sum of quitting probabilities. -/
private theorem prod_one_sub_mul_one_add_sum_le_one {N : Type} (s : Finset N)
    (a : N → ℝ) (ha0 : ∀ n ∈ s, 0 ≤ a n) (ha1 : ∀ n ∈ s, a n ≤ 1) :
    (∏ n ∈ s, (1 - a n)) * (1 + ∑ n ∈ s, a n) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      rw [Finset.prod_insert hn, Finset.sum_insert hn]
      have hfactor0 : ∀ j ∈ s, 0 ≤ 1 - a j := fun j hj =>
        sub_nonneg.mpr (ha1 j (Finset.mem_insert_of_mem hj))
      have hprod0 : 0 ≤ ∏ j ∈ s, (1 - a j) := Finset.prod_nonneg hfactor0
      have hsum0 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j hj =>
        ha0 j (Finset.mem_insert_of_mem hj)
      have hrest := ih (fun j hj => ha0 j (Finset.mem_insert_of_mem hj))
        (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
      have hn0 := ha0 n (Finset.mem_insert_self n s)
      have hn1 := ha1 n (Finset.mem_insert_self n s)
      have hfactor : (1 - a n) * (1 + ∑ j ∈ s, a j + a n) ≤
          1 + ∑ j ∈ s, a j := by nlinarith [mul_nonneg hn0 hsum0]
      calc
        (1 - a n) * (∏ j ∈ s, (1 - a j)) *
            (1 + (a n + ∑ j ∈ s, a j)) =
            (∏ j ∈ s, (1 - a j)) *
              ((1 - a n) * (1 + ∑ j ∈ s, a j + a n)) := by ring
        _ ≤ (∏ j ∈ s, (1 - a j)) * (1 + ∑ j ∈ s, a j) :=
          mul_le_mul_of_nonneg_left hfactor hprod0
        _ ≤ 1 := hrest

/-- Unbounded total quit mass eventually makes one player's continue probability small. -/
private theorem exists_playerContinueProbability_le
    (G : QuittingGame) {p : QuitProfile G} (hmass : HasUnboundedQuitMass G p)
    {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    ∃ (i : ℕ) (n : G.Player), PlayerContinueProbability G p n i ≤ ε / M := by
  classical
  let threshold := M / ε
  obtain ⟨i, hi⟩ := hmass (Fintype.card G.Player * threshold)
  have hquit (k : ℕ) : QuitProbability G (p k) ≤ ∑ n, (p k n : ℝ) := by
    exact one_sub_prod_one_sub_le_sum Finset.univ (fun n => (p k n : ℝ))
      (fun n _ => (p k n).property.1) (fun n _ => (p k n).property.2)
  have htotal : Fintype.card G.Player * threshold ≤
      ∑ n : G.Player, ∑ k ∈ Finset.range i, (p k n : ℝ) := by
    calc
      Fintype.card G.Player * threshold ≤
          ∑ k ∈ Finset.range i, QuitProbability G (p k) := hi
      _ ≤ ∑ k ∈ Finset.range i, ∑ n, (p k n : ℝ) := by
        exact Finset.sum_le_sum fun k _ => hquit k
      _ = ∑ n : G.Player, ∑ k ∈ Finset.range i, (p k n : ℝ) := by
        rw [Finset.sum_comm]
  have hexists : ∃ n : G.Player,
      threshold ≤ ∑ k ∈ Finset.range i, (p k n : ℝ) := by
    by_contra hall
    push Not at hall
    let n₀ : G.Player := Classical.choice inferInstance
    have hstrict : (∑ n : G.Player, ∑ k ∈ Finset.range i, (p k n : ℝ)) <
        ∑ _n : G.Player, threshold := by
      apply Finset.sum_lt_sum
      · intro n _hn
        exact (hall n).le
      · exact ⟨n₀, Finset.mem_univ n₀, hall n₀⟩
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hstrict
    exact (not_lt_of_ge htotal) hstrict
  rcases hexists with ⟨n, hn⟩
  have hproduct := prod_one_sub_mul_one_add_sum_le_one (Finset.range i)
    (fun k => (p k n : ℝ)) (fun k _ => (p k n).property.1)
      (fun k _ => (p k n).property.2)
  have hcontinue0 : 0 ≤ PlayerContinueProbability G p n i :=
    Finset.prod_nonneg fun k _ => sub_nonneg.mpr (p k n).property.2
  have hscaled : PlayerContinueProbability G p n i * threshold ≤ 1 := by
    calc
      PlayerContinueProbability G p n i * threshold ≤
          PlayerContinueProbability G p n i *
            (1 + ∑ k ∈ Finset.range i, (p k n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hcontinue0
        linarith
      _ ≤ 1 := hproduct
  refine ⟨i, n, ?_⟩
  dsimp only [threshold] at hscaled
  have hMε : 0 < M / ε := div_pos hM hε
  have hbound : PlayerContinueProbability G p n i ≤ 1 / (M / ε) := by
    exact (le_div_iff₀ hMε).2 hscaled
  convert hbound using 1
  field_simp

/-- The paper's `W_i^n`, cumulative gain from choosing Continue before stage `i`. -/
private def ContinueLedger (G : QuittingGame) (p : QuitProfile G)
    (n : G.Player) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range i,
    (ForcedContinuePayoff G (QuitTailPayoff G p (k + 1)) (p k) n -
      QuitTailPayoff G p k n)

@[simp] private theorem ContinueLedger.zero
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) :
    ContinueLedger G p n 0 = 0 := by
  simp [ContinueLedger]

private theorem ContinueLedger.succ
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (i : ℕ) :
    ContinueLedger G p n (i + 1) = ContinueLedger G p n i +
      (ForcedContinuePayoff G (QuitTailPayoff G p (i + 1)) (p i) n -
        QuitTailPayoff G p i n) := by
  rw [ContinueLedger, ContinueLedger, Finset.sum_range_succ]

/-- Before the first `ε` crossing, the next ledger value overshoots by at most `δ`. -/
private theorem ContinueLedger.succ_lt_add_of_generated
    (G : QuittingGame) {p : QuitProfile G} {δ ε : ℝ}
    (horbit : GeneratesFRowOrbit G δ p) (hδ : 0 ≤ δ)
    (n : G.Player) (i : ℕ) (hi : ContinueLedger G p n i < ε) :
    ContinueLedger G p n (i + 1) < ε + δ := by
  rw [ContinueLedger.succ]
  have hincrement := EpsilonRow.forcedContinue_sub_oneStage_le G (horbit i) hδ n
  rw [← quitTailPayoff_eq_oneStage G p i] at hincrement
  linarith

/-- A stage triggers punishment when some ledger crosses or some own survival becomes small. -/
private def IsPunishmentTrigger (G : QuittingGame) (p : QuitProfile G)
    (M ε : ℝ) (i : ℕ) : Prop :=
  ∃ n : G.Player, ε ≤ ContinueLedger G p n i ∨
    PlayerContinueProbability G p n i ≤ ε / M

/-- Unbounded quit mass makes the paper's punishment clock finite. -/
private theorem exists_punishmentTrigger
    (G : QuittingGame) {p : QuitProfile G} (hmass : HasUnboundedQuitMass G p)
    {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    ∃ i, IsPunishmentTrigger G p M ε i := by
  rcases exists_playerContinueProbability_le G hmass hM hε with ⟨i, n, hn⟩
  exact ⟨i, n, Or.inr hn⟩

/-- The first stage at which the paper's punishment clock triggers. -/
private noncomputable def firstPunishmentTrigger
    (G : QuittingGame) (p : QuitProfile G) (M ε : ℝ)
    (hexists : ∃ i, IsPunishmentTrigger G p M ε i) : ℕ := by
  classical
  exact Nat.find hexists

/-- Every ledger is below `ε` strictly before the first punishment trigger. -/
private theorem ledger_lt_of_lt_firstPunishmentTrigger
    (G : QuittingGame) {p : QuitProfile G} {M ε : ℝ}
    (hexists : ∃ i, IsPunishmentTrigger G p M ε i)
    {i : ℕ} (hi : i < firstPunishmentTrigger G p M ε hexists) (n : G.Player) :
    ContinueLedger G p n i < ε := by
  classical
  change i < Nat.find hexists at hi
  have hnot := Nat.find_min hexists hi
  rw [IsPunishmentTrigger] at hnot
  push Not at hnot
  exact (hnot n).1

/-- At the first trigger, each ledger is below `ε + δ`. -/
private theorem ledger_firstPunishmentTrigger_lt_add
    (G : QuittingGame) {p : QuitProfile G} {M δ ε : ℝ}
    (horbit : GeneratesFRowOrbit G δ p) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hexists : ∃ i, IsPunishmentTrigger G p M ε i) (n : G.Player) :
    ContinueLedger G p n (firstPunishmentTrigger G p M ε hexists) < ε + δ := by
  classical
  let T := firstPunishmentTrigger G p M ε hexists
  change ContinueLedger G p n T < ε + δ
  by_cases hzero : T = 0
  · rw [hzero, ContinueLedger.zero]
    linarith
  · obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    rw [hi]
    exact ContinueLedger.succ_lt_add_of_generated G horbit hδ n i
      (ledger_lt_of_lt_firstPunishmentTrigger G hexists (show i < T by omega) n)

/-! The finite-horizon rank-one decision process used in Proposition 3. -/

private abbrev QuittingDDPState (G : QuittingGame) := ℕ × Finset G.Player

private def IsQuittingDDPLive (T : ℕ) (state : QuittingDDPState G) : Prop :=
  state.1 < T ∧ state.2 = ∅

private noncomputable def quittingBernoulli (q : Set.Icc (0 : ℝ) 1) : PMF Bool := by
  apply PMF.ofFintype fun b =>
    if b then ENNReal.ofReal (q : ℝ) else ENNReal.ofReal (1 - (q : ℝ))
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_pos, if_false]
  rw [← ENNReal.ofReal_add q.property.1 (sub_nonneg.mpr q.property.2)]
  ring_nf
  simp

private noncomputable def quittingDDPChoose
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (state : QuittingDDPState G) : PMF Bool := by
  classical
  exact if IsQuittingDDPLive T state then quittingBernoulli (p state.1 n)
    else PMF.pure false

private noncomputable def quittingDDPMove
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (state : QuittingDDPState G) (action : Bool) : PMF (QuittingDDPState G) := by
  classical
  exact if IsQuittingDDPLive T state then
    (coalitionPMF G ((p state.1).replace G n (if action = true then 1 else 0))).map
      fun A => (state.1 + 1, A)
  else PMF.pure state

private noncomputable def quittingDDPValueX
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (state : QuittingDDPState G) : ℝ := by
  classical
  exact if hA : state.2.Nonempty then G.reward ⟨state.2, hA⟩ n
    else QuitTailPayoff G p (min state.1 T) n

private noncomputable def quittingDDPValueY
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (state : QuittingDDPState G) (action : Bool) : ℝ := by
  classical
  exact if IsQuittingDDPLive T state then
    if action = true then ForcedQuitPayoff G (p state.1) n
    else ForcedContinuePayoff G (QuitTailPayoff G p (state.1 + 1)) (p state.1) n
  else quittingDDPValueX G p n T state

private theorem quitTailPayoff_mem_coordinateInterval
    (G : QuittingGame) (p : QuitProfile G) (i : ℕ) (n : G.Player) :
    QuitTailPayoff G p i n ∈
      Set.Icc (quittingCoordinateLower G n) (quittingCoordinateUpper G n) := by
  let tail : QuitProfile G := fun k => p (i + k)
  have h := quitPayoff_mem_coordinateInterval G tail n
  simpa only [QuitPayoff, QuitTailPayoff, tail, zero_add] using h

private theorem quittingDDPValueX_mem_coordinateInterval
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (state : QuittingDDPState G) :
    quittingDDPValueX G p n T state ∈
      Set.Icc (quittingCoordinateLower G n) (quittingCoordinateUpper G n) := by
  classical
  simp only [quittingDDPValueX]
  split_ifs with hA
  · constructor
    · simpa [quittingCoordinateValue] using
        quittingCoordinateLower_le_value G n (some ⟨state.2, hA⟩)
    · simpa [quittingCoordinateValue] using
        quittingCoordinateValue_le_upper G n (some ⟨state.2, hA⟩)
  · exact quitTailPayoff_mem_coordinateInterval G p (min state.1 T) n

private theorem quittingDDPValueY_mem_coordinateInterval
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (state : QuittingDDPState G) (action : Bool) :
    quittingDDPValueY G p n T state action ∈
      Set.Icc (quittingCoordinateLower G n) (quittingCoordinateUpper G n) := by
  classical
  by_cases hlive : IsQuittingDDPLive T state
  · cases action with
    | false =>
        simp only [quittingDDPValueY, hlive, if_pos, Bool.false_eq_true, if_false]
        apply quittingOneStagePayoff_mem_coordinateInterval
        exact quitTailPayoff_mem_coordinateInterval G p (state.1 + 1) n
    | true =>
        simp only [quittingDDPValueY, hlive, if_pos]
        apply quittingOneStagePayoff_mem_coordinateInterval
        exact ⟨quittingCoordinateLower_nonpos G n, quittingCoordinateUpper_nonneg G n⟩
  · simp only [quittingDDPValueY, hlive, if_false]
    exact quittingDDPValueX_mem_coordinateInterval G p n T state

private theorem abs_sub_le_of_mem_coordinateInterval
    (G : QuittingGame) (n : G.Player) {M x y : ℝ}
    (hM : IsQuittingPayoffDifferenceBound G M)
    (hx : x ∈ Set.Icc (quittingCoordinateLower G n) (quittingCoordinateUpper G n))
    (hy : y ∈ Set.Icc (quittingCoordinateLower G n) (quittingCoordinateUpper G n)) :
    |x - y| ≤ M := by
  have hwidth := quittingCoordinate_width_lt G n hM
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

@[simp] private theorem quittingBernoulli_apply_true_toReal
    (q : Set.Icc (0 : ℝ) 1) : (quittingBernoulli q true).toReal = q := by
  rw [quittingBernoulli, PMF.ofFintype_apply]
  simp only [if_pos]
  rw [ENNReal.toReal_ofReal q.property.1]

@[simp] private theorem quittingBernoulli_apply_false_toReal
    (q : Set.Icc (0 : ℝ) 1) : (quittingBernoulli q false).toReal = 1 - q := by
  rw [quittingBernoulli, PMF.ofFintype_apply]
  simp only [Bool.false_eq_true, if_false]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr q.property.2)]

private theorem quittingDDPHarmonicX
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (state : QuittingDDPState G) :
    quittingDDPValueX G p n T state =
      ∑' action, (quittingDDPChoose G p n T state action).toReal *
        quittingDDPValueY G p n T state action := by
  classical
  by_cases hlive : IsQuittingDDPLive T state
  · have htime : min state.1 T = state.1 := min_eq_left (le_of_lt hlive.1)
    have hempty : ¬state.2.Nonempty := by
      rw [hlive.2]
      exact Finset.not_nonempty_empty
    rw [tsum_fintype, Fintype.sum_bool]
    simp only [quittingDDPChoose, hlive, if_pos, quittingDDPValueY,
      quittingBernoulli_apply_true_toReal, quittingBernoulli_apply_false_toReal]
    simp only [quittingDDPValueX, hempty, dite_false, htime]
    rw [quitTailPayoff_eq_oneStage G p state.1]
    simp only [Bool.false_eq_true, if_false]
    have haffine := quittingOneStagePayoff_replace_eq_endpoints G
      (QuitTailPayoff G p (state.1 + 1)) (p state.1) n (p state.1 n)
    rw [QuitRow.replace_self] at haffine
    exact haffine
  · rw [tsum_fintype, Fintype.sum_bool]
    simp [quittingDDPChoose, hlive, PMF.pure_apply, quittingDDPValueY]

private theorem quittingDDPValueX_nextCoalition
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) {T i : ℕ}
    (hi : i < T) (A : Finset G.Player) :
    quittingDDPValueX G p n T (i + 1, A) =
      if hA : A.Nonempty then G.reward ⟨A, hA⟩ n
      else QuitTailPayoff G p (i + 1) n := by
  classical
  simp only [quittingDDPValueX]
  split_ifs with hA
  · rfl
  · rw [min_eq_left (by omega)]

private theorem quittingDDPHarmonicY
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (state : QuittingDDPState G) (action : Bool) :
    quittingDDPValueY G p n T state action =
      ∑' next, (quittingDDPMove G p n T state action next).toReal *
        quittingDDPValueX G p n T next := by
  classical
  by_cases hlive : IsQuittingDDPLive T state
  · let row := (p state.1).replace G n (if action = true then 1 else 0)
    let advance : Finset G.Player → QuittingDDPState G :=
      fun A => (state.1 + 1, A)
    have hadvance : Function.Injective advance := by
      intro A B h
      exact congrArg Prod.snd h
    simp only [quittingDDPMove, hlive, if_pos]
    change quittingDDPValueY G p n T state action =
      ∑' next, (((coalitionPMF G row).map advance) next).toReal *
        quittingDDPValueX G p n T next
    rw [PMF.tsum_map_toReal_mul_of_injective _ _ hadvance]
    rw [tsum_fintype]
    simp_rw [coalitionPMF_apply_toReal]
    have hnext : ∀ A : Finset G.Player,
        quittingDDPValueX G p n T (advance A) =
          if hA : A.Nonempty then G.reward ⟨A, hA⟩ n
          else QuitTailPayoff G p (state.1 + 1) n := by
      intro A
      exact quittingDDPValueX_nextCoalition G p n hlive.1 A
    simp_rw [hnext]
    rw [show (∑ A, CoalitionProbability G row A *
        if hA : A.Nonempty then G.reward ⟨A, hA⟩ n
        else QuitTailPayoff G p (state.1 + 1) n) =
      ∑ A ∈ Finset.univ.powerset, CoalitionProbability G row A *
        if hA : A.Nonempty then G.reward ⟨A, hA⟩ n
        else QuitTailPayoff G p (state.1 + 1) n by simp]
    rw [← quittingOneStagePayoff_eq_coalition_sum G
      (QuitTailPayoff G p (state.1 + 1)) row n]
    cases action with
    | false =>
        simp only [quittingDDPValueY, hlive, if_pos, Bool.false_eq_true, if_false,
          row, ForcedContinuePayoff]
    | true =>
        simp only [quittingDDPValueY, hlive, if_pos, row, ForcedQuitPayoff]
        simp only [QuittingOneStagePayoff]
        rw [quitProbability_replace_one]
        ring
  · simp only [quittingDDPMove, hlive, if_false]
    rw [tsum_eq_single state]
    · simp [quittingDDPValueY, hlive]
    · intro other hother
      rw [PMF.pure_apply, if_neg hother]
      simp

/-- The rank-one process generated by one player in a finite quitting prefix. -/
private noncomputable def quittingDecisionProcess
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M) : DiscreteDecisionProcess where
  X := QuittingDDPState G
  Y := fun _ => Bool
  choose := quittingDDPChoose G p n T
  move := quittingDDPMove G p n T
  initial := (0, ∅)
  valueX := quittingDDPValueX G p n T
  valueY := quittingDDPValueY G p n T
  harmonicX := quittingDDPHarmonicX G p n T
  harmonicY := quittingDDPHarmonicY G p n T
  valueDifferenceBound := M
  valueDifferenceBound_one := hM.1
  valueDifference := by
    intro x z y w
    have hx := quittingDDPValueX_mem_coordinateInterval G p n T x
    have hz := quittingDDPValueX_mem_coordinateInterval G p n T z
    have hy := quittingDDPValueY_mem_coordinateInterval G p n T x y
    have hw := quittingDDPValueY_mem_coordinateInterval G p n T z w
    exact ⟨abs_sub_le_of_mem_coordinateInterval G n hM hx hz,
      abs_sub_le_of_mem_coordinateInterval G n hM hy hz,
      abs_sub_le_of_mem_coordinateInterval G n hM hy hw⟩

/-- Rows in the generated orbit make the associated quitting DDP support-locally balanced. -/
private theorem quittingDecisionProcess_balanced
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M) {δ : ℝ}
    (hδ : 0 ≤ δ) (horbit : GeneratesFRowOrbit G δ p) :
    IsBalanced (quittingDecisionProcess G p n T M hM) δ := by
  intro state action hpositive
  by_cases hlive : IsQuittingDDPLive T state
  · have hempty : ¬state.2.Nonempty := by
      rw [hlive.2]
      exact Finset.not_nonempty_empty
    have hvalueX : quittingDDPValueX G p n T state =
        QuitTailPayoff G p state.1 n := by
      simp only [quittingDDPValueX, hempty, dite_false,
        min_eq_left (le_of_lt hlive.1)]
    have hrow := horbit state.1
    change 0 < quittingDDPChoose G p n T state action at hpositive
    change |quittingDDPValueY G p n T state action -
      quittingDDPValueX G p n T state| ≤ δ
    rw [hvalueX, quitTailPayoff_eq_oneStage G p state.1]
    cases action with
    | false =>
        have hcontinue : (p state.1 n : ℝ) < 1 := by
          simp only [quittingDDPChoose, hlive, if_pos, quittingBernoulli,
            PMF.ofFintype_apply, Bool.false_eq_true, if_false] at hpositive
          exact sub_pos.mp (ENNReal.ofReal_pos.mp hpositive)
        simp only [quittingDDPValueY, hlive, if_pos, Bool.false_eq_true, if_false]
        rw [abs_le]
        constructor
        · have := EpsilonRow.oneStage_sub_forcedContinuePayoff_le_of_lt_one
              G hrow hδ n hcontinue
          linarith
        · exact EpsilonRow.forcedContinue_sub_oneStage_le G hrow hδ n
    | true =>
        have hquit : 0 < (p state.1 n : ℝ) := by
          simp only [quittingDDPChoose, hlive, if_pos, quittingBernoulli,
            PMF.ofFintype_apply] at hpositive
          exact ENNReal.ofReal_pos.mp hpositive
        simp only [quittingDDPValueY, hlive, if_pos]
        rw [abs_le]
        constructor
        · have := EpsilonRow.oneStage_sub_forcedQuitPayoff_le_of_pos
              G hrow hδ n hquit
          linarith
        · have := EpsilonRow.forcedQuitPayoff_le_oneStage_add G hrow hδ n
          linarith
  · change |quittingDDPValueY G p n T state action -
      quittingDDPValueX G p n T state| ≤ δ
    simp only [quittingDDPValueY, hlive, if_false, sub_self, abs_zero]
    exact hδ

private theorem PMF.mem_range_of_map_ne_zero {A B : Type*}
    (μ : PMF A) (f : A → B) {b : B} (hb : μ.map f b ≠ 0) : b ∈ Set.range f := by
  classical
  by_contra hrange
  apply hb
  rw [PMF.map_apply]
  calc
    (∑' a, if b = f a then μ a else 0) = ∑' _a : A, 0 := by
      apply tsum_congr
      intro a
      rw [if_neg]
      exact fun h => hrange ⟨a, h.symm⟩
    _ = 0 := tsum_zero

/-- States reachable at time `i` are either the current live state or an earlier terminal state. -/
private def IsQuittingDDPReachable (T i : ℕ) (state : QuittingDDPState G) : Prop :=
  (state.2 = ∅ ∧ state.1 = min i T) ∨
    (state.2.Nonempty ∧ state.1 ≤ min i T)

private theorem quittingDDPMove_reachable
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T i : ℕ)
    {state next : QuittingDDPState G} (hstate : IsQuittingDDPReachable T i state)
    (action : Bool) (hmove : quittingDDPMove G p n T state action next ≠ 0) :
    IsQuittingDDPReachable T (i + 1) next := by
  classical
  by_cases hlive : IsQuittingDDPLive T state
  · have hrange := PMF.mem_range_of_map_ne_zero
      (coalitionPMF G ((p state.1).replace G n (if action = true then 1 else 0)))
      (fun A => (state.1 + 1, A)) (by
        simpa only [quittingDDPMove, hlive, if_pos] using hmove)
    rcases hrange with ⟨A, rfl⟩
    obtain ⟨_hempty, htimeMin⟩ := hstate.resolve_right fun hterminal => by
      rw [hlive.2] at hterminal
      exact Finset.not_nonempty_empty hterminal.1
    have hiT : i < T := by
      have hminlt : min i T < T := by
        rw [← htimeMin]
        exact hlive.1
      by_contra hi
      rw [min_eq_right (le_of_not_gt hi)] at hminlt
      exact (lt_irrefl T hminlt).elim
    have htime : state.1 = i := htimeMin.trans (min_eq_left hiT.le)
    by_cases hA : A = ∅
    · left
      exact ⟨hA, by rw [htime, min_eq_left (Nat.succ_le_iff.mpr hiT)]⟩
    · right
      refine ⟨Finset.nonempty_iff_ne_empty.2 hA, ?_⟩
      rw [htime, min_eq_left (Nat.succ_le_iff.mpr hiT)]
  · have hnext : next = state := by
      have hpure : PMF.pure state next ≠ 0 := by
        simpa only [quittingDDPMove, hlive, if_false] using hmove
      rw [PMF.pure_apply] at hpure
      split at hpure
      · assumption
      · exact (hpure rfl).elim
    rw [hnext]
    rcases hstate with ⟨hempty, htime⟩ | ⟨hnonempty, htime⟩
    · left
      refine ⟨hempty, ?_⟩
      rw [htime]
      have hnotlt : ¬min i T < T := by
        intro hlt
        exact hlive ⟨by rwa [htime], hempty⟩
      have hmin : min i T = T := by omega
      rw [hmin, min_eq_right (by omega)]
    · right
      exact ⟨hnonempty, htime.trans (min_le_min_right T (Nat.le_succ i))⟩

private theorem quittingDDPMove_eq_of_terminal
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    {state next : QuittingDDPState G} (hnonempty : state.2.Nonempty)
    (action : Bool) (hmove : quittingDDPMove G p n T state action next ≠ 0) :
    next = state := by
  have hlive : ¬IsQuittingDDPLive T state := fun hlive => by
    rw [hlive.2] at hnonempty
    exact Finset.not_nonempty_empty hnonempty
  have hpure : PMF.pure state next ≠ 0 := by
    simpa only [quittingDDPMove, hlive, if_false] using hmove
  rw [PMF.pure_apply] at hpure
  split at hpure
  · assumption
  · exact (hpure rfl).elim

private theorem quittingDDPMove_true_nonempty
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T i : ℕ)
    (hi : i < T) {next : QuittingDDPState G}
    (hmove : quittingDDPMove G p n T (i, ∅) true next ≠ 0) :
    next.2.Nonempty := by
  classical
  let row := (p i).replace G n 1
  let advance : Finset G.Player → QuittingDDPState G := fun A => (i + 1, A)
  have hadvance : Function.Injective advance := fun A B h => congrArg Prod.snd h
  have hlive : IsQuittingDDPLive T (i, (∅ : Finset G.Player)) := ⟨hi, rfl⟩
  have hrange := PMF.mem_range_of_map_ne_zero (coalitionPMF G row) advance (by
    simpa only [quittingDDPMove, hlive, if_pos, row, advance] using hmove)
  rcases hrange with ⟨A, rfl⟩
  have hmap : ((coalitionPMF G row).map advance) (advance A) = coalitionPMF G row A := by
    rw [PMF.map_apply, tsum_eq_single A]
    · simp
    · intro B hBA
      rw [if_neg]
      exact fun h => hBA (hadvance h.symm)
  have hsource : coalitionPMF G row A ≠ 0 := by
    intro hzero
    apply hmove
    simpa only [quittingDDPMove, hlive, if_pos, row, advance, hmap] using hzero
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  change A = ∅ at hempty
  subst A
  apply hsource
  have hcoalition : CoalitionProbability G row ∅ = 0 := by
    simp only [CoalitionProbability, Finset.prod_empty, one_mul]
    have hfilter : Finset.univ.filter (fun j : G.Player => j ∉ (∅ : Finset G.Player)) =
        Finset.univ := by ext; simp
    rw [hfilter]
    apply Finset.prod_eq_zero (Finset.mem_univ n)
    simp [row, QuitRow.replace]
  rw [coalitionPMF, PMF.ofFintype_apply]
  rw [hcoalition]
  simp

private theorem quittingDDPFinitePath_reachable
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M) {k : ℕ}
    (path : DDPFinitePath (quittingDecisionProcess G p n T M hM) k)
    (hstart : path.x 0 = (0, ∅)) (hprobability : path.probability
      (quittingDecisionProcess G p n T M hM) ≠ 0) (j : Fin (k + 1)) :
    IsQuittingDDPReachable T j.1 (path.x j) := by
  let P := quittingDecisionProcess G p n T M hM
  have hfactor : ∀ t : Fin k,
      P.move (path.x t.castSucc) (path.y t) (path.x t.succ) ≠ 0 := by
    intro t hzero
    apply hprobability
    rw [DDPFinitePath.probability]
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    rw [hzero, mul_zero]
  have go : ∀ m (hm : m ≤ k),
      IsQuittingDDPReachable T m (path.x ⟨m, by omega⟩) := by
    intro m hm
    induction m with
    | zero =>
        change IsQuittingDDPReachable T 0 (path.x 0)
        rw [hstart]
        left
        simp
    | succ m ih =>
        apply quittingDDPMove_reachable G p n T m (ih (by omega))
          (path.y ⟨m, by omega⟩)
        change quittingDDPMove G p n T (path.x ⟨m, by omega⟩)
          (path.y ⟨m, by omega⟩) (path.x ⟨m + 1, by omega⟩) ≠ 0
        exact hfactor ⟨m, by omega⟩
  exact go j.1 (by omega)

/-- Once a positive-probability finite path is terminal, it remains at that state. -/
private theorem quittingDDPFinitePath_terminal_persists
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M) {k a b : ℕ}
    (path : DDPFinitePath (quittingDecisionProcess G p n T M hM) k)
    (hprobability : path.probability (quittingDecisionProcess G p n T M hM) ≠ 0)
    (ha : a ≤ k) (hb : b ≤ k) (hab : a ≤ b)
    (hterminal : (path.x ⟨a, by omega⟩).2.Nonempty) :
    path.x ⟨b, by omega⟩ = path.x ⟨a, by omega⟩ := by
  let P := quittingDecisionProcess G p n T M hM
  have hfactor : ∀ t : Fin k,
      P.move (path.x t.castSucc) (path.y t) (path.x t.succ) ≠ 0 := by
    intro t hzero
    apply hprobability
    rw [DDPFinitePath.probability]
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    rw [hzero, mul_zero]
  have go : ∀ d (hd : a + d ≤ k),
      path.x ⟨a + d, by omega⟩ = path.x ⟨a, by omega⟩ := by
    intro d hd
    induction d with
    | zero => rfl
    | succ d ih =>
        have hcurrent := ih (by omega)
        have hcurrentTerminal : (path.x ⟨a + d, by omega⟩).2.Nonempty := by
          rw [hcurrent]
          exact hterminal
        have hstep := quittingDDPMove_eq_of_terminal G p n T hcurrentTerminal
          (path.y ⟨a + d, by omega⟩) (hfactor ⟨a + d, by omega⟩)
        exact hstep.trans hcurrent
  have heq : a + (b - a) = b := Nat.add_sub_of_le hab
  simpa only [heq] using go (b - a) (by omega)

/-- A positive-probability prefix that remains live sampled only Continue actions. -/
private theorem quittingDDPFinitePath_action_false_of_live_end
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M) {k : ℕ}
    (path : DDPFinitePath (quittingDecisionProcess G p n T M hM) k)
    (hstart : path.x 0 = (0, ∅))
    (hprobability : path.probability (quittingDecisionProcess G p n T M hM) ≠ 0)
    (hkT : k ≤ T) (hend : path.x (Fin.last k) = (k, ∅)) (j : Fin k) :
    path.y j = false := by
  let P := quittingDecisionProcess G p n T M hM
  have hfactor : ∀ t : Fin k,
      P.move (path.x t.castSucc) (path.y t) (path.x t.succ) ≠ 0 := by
    intro t hzero
    apply hprobability
    rw [DDPFinitePath.probability]
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    rw [hzero, mul_zero]
  have hstate : path.x j.castSucc = (j.1, ∅) := by
    have hreachable := quittingDDPFinitePath_reachable G p n T M hM path hstart
      hprobability j.castSucc
    rcases hreachable with hlive | hterminal
    · apply Prod.ext
      · simpa [min_eq_left (show j.1 ≤ T by omega)] using hlive.2
      · exact hlive.1
    · exfalso
      have hpersist := quittingDDPFinitePath_terminal_persists G p n T M hM path
        hprobability (show j.1 ≤ k by omega) le_rfl (show j.1 ≤ k by omega)
        hterminal.1
      have hcoalition := congrArg Prod.snd hpersist
      have hlast : (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k := by ext; simp
      have hend' : path.x ⟨k, by omega⟩ = (k, ∅) := by rwa [hlast]
      rw [hend'] at hcoalition
      have hindex : (⟨j.1, by omega⟩ : Fin (k + 1)) = j.castSucc := by rfl
      have hempty : (path.x j.castSucc).2 = ∅ := by
        rw [← hindex]
        exact hcoalition.symm
      rw [hempty] at hterminal
      exact Finset.not_nonempty_empty hterminal.1
  by_contra hfalse
  have htrue : path.y j = true := Bool.eq_true_of_not_eq_false hfalse
  have hnextTerminal : (path.x j.succ).2.Nonempty := by
    apply quittingDDPMove_true_nonempty G p n T j.1 (by omega)
    have hjmove := hfactor j
    change quittingDDPMove G p n T (path.x j.castSucc) (path.y j)
      (path.x j.succ) ≠ 0 at hjmove
    rwa [hstate, htrue] at hjmove
  have hpersist := quittingDDPFinitePath_terminal_persists G p n T M hM path
    hprobability (show j.1 + 1 ≤ k by omega) le_rfl (show j.1 + 1 ≤ k by omega)
    hnextTerminal
  have hcoalition := congrArg Prod.snd hpersist
  have hlast : (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k := by ext; simp
  have hend' : path.x ⟨k, by omega⟩ = (k, ∅) := by rwa [hlast]
  rw [hend'] at hcoalition
  have hindex : (⟨j.1 + 1, by omega⟩ : Fin (k + 1)) = j.succ := by rfl
  have hempty : (path.x j.succ).2 = ∅ := by
    rw [← hindex]
    exact hcoalition.symm
  rw [hempty] at hnextTerminal
  exact Finset.not_nonempty_empty hnextTerminal

/-- The raw event that the quitting DDP is live and samples this player's Quit action. -/
private def QuittingDDPOwnQuitEvent
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M) (i : ℕ) :
    Set (ℕ → DDPStage (quittingDecisionProcess G p n T M hM)) :=
  {stages | (stages i).1 = (i, ∅) ∧ HEq (stages i).2 true}

private theorem measurableSet_quittingDDPOwnQuitEvent
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M) (i : ℕ) :
    MeasurableSet (QuittingDDPOwnQuitEvent G p n T M hM i) := by
  let P := quittingDecisionProcess G p n T M hM
  have heq : QuittingDDPOwnQuitEvent G p n T M hM i =
      {stages : ℕ → DDPStage P | stages i = ⟨(i, ∅), true⟩} := by
    ext stages
    simp only [QuittingDDPOwnQuitEvent, mem_setOf_eq]
    constructor
    · rintro ⟨hstate, haction⟩
      apply Sigma.ext hstate
      exact haction
    · intro hstage
      exact ⟨congrArg Sigma.fst hstage, (Sigma.mk.inj_iff.mp hstage).2⟩
  rw [heq]
  exact show MeasurableSet ((fun stages : ℕ → DDPStage P => stages i) ⁻¹'
      {(⟨(i, ∅), true⟩ : DDPStage P)}) from
    (measurable_pi_apply i)
      (measurableSet_singleton (⟨(i, ∅), true⟩ : DDPStage P))

private theorem quittingDDPOwnQuitEvent_inter_eq_zero_of_lt
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M)
    (S : DDPSemantics (quittingDecisionProcess G p n T M hM))
    {i j : ℕ} (hij : i < j) (hjT : j < T) :
    (quittingDecisionProcess G p n T M hM).rawLawFrom (0, ∅)
        (QuittingDDPOwnQuitEvent G p n T M hM i ∩
          QuittingDDPOwnQuitEvent G p n T M hM j) = 0 := by
  let P := quittingDecisionProcess G p n T M hM
  let H := {path : DDPFinitePath P j //
    path.x (Fin.last j) = (j, ∅) ∧ path.y ⟨i, hij⟩ = true}
  let C : H → Set (ℕ → DDPStage P) := fun path =>
    DDPPath.ofRaw P ⁻¹' DDPCylinder P path.1
  have hsubset : QuittingDDPOwnQuitEvent G p n T M hM i ∩
      QuittingDDPOwnQuitEvent G p n T M hM j ⊆ ⋃ path, C path := by
    rintro stages ⟨hi, hj⟩
    let path := (DDPPath.ofRaw P stages).prefix P j
    have hend : path.x (Fin.last j) = (j, ∅) := by
      simpa [path, DDPPath.prefix, DDPPath.ofRaw] using hj.1
    have haction : path.y ⟨i, hij⟩ = true := by
      have haction' : HEq (path.y ⟨i, hij⟩) true := by
        simpa [path, DDPPath.prefix, DDPPath.ofRaw] using hi.2
      exact eq_of_heq haction'
    exact mem_iUnion.2 ⟨⟨path, hend, haction⟩, rfl⟩
  have hmeasure (path : H) : P.rawLawFrom (0, ∅) (C path) = 0 := by
    by_cases hstart : path.1.x 0 = (0, ∅)
    · rw [P.rawLawFrom_ddpCylinder (0, ∅) path.1 hstart]
      by_contra hprobability
      have hfalse := quittingDDPFinitePath_action_false_of_live_end G p n T M hM
        path.1 hstart hprobability (Nat.le_of_lt hjT) path.2.1 ⟨i, hij⟩
      exact Bool.false_ne_true (hfalse.symm.trans path.2.2)
    · exact P.rawLawFrom_ddpCylinder_eq_zero_of_wrong S (0, ∅) path.1 hstart
  apply nonpos_iff_eq_zero.mp
  calc
    P.rawLawFrom (0, ∅)
        (QuittingDDPOwnQuitEvent G p n T M hM i ∩
          QuittingDDPOwnQuitEvent G p n T M hM j) ≤
        P.rawLawFrom (0, ∅) (⋃ path, C path) := measure_mono hsubset
    _ ≤ ∑' path, P.rawLawFrom (0, ∅) (C path) := measure_iUnion_le _
    _ = 0 := by simp_rw [hmeasure]; simp

private theorem quittingDDPOwnQuitEvent_pairwise_aedisjoint
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M)
    (S : DDPSemantics (quittingDecisionProcess G p n T M hM)) :
    Pairwise (Function.onFun
      (AEDisjoint ((quittingDecisionProcess G p n T M hM).rawLawFrom (0, ∅)))
      (fun i : Fin T => QuittingDDPOwnQuitEvent G p n T M hM i)) := by
  intro i j hij
  change (quittingDecisionProcess G p n T M hM).rawLawFrom (0, ∅)
    (QuittingDDPOwnQuitEvent G p n T M hM i ∩
      QuittingDDPOwnQuitEvent G p n T M hM j) = 0
  rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with hij' | hji'
  · exact quittingDDPOwnQuitEvent_inter_eq_zero_of_lt G p n T M hM S
      hij' j.2
  · rw [inter_comm]
    exact quittingDDPOwnQuitEvent_inter_eq_zero_of_lt G p n T M hM S
      hji' i.2

/-- A player can sample Quit on a live path at most once. -/
private theorem quittingDDPOwnQuitEvent_totalMass_le_one
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M)
    (S : DDPSemantics (quittingDecisionProcess G p n T M hM)) :
    ∑' i : Fin T, (quittingDecisionProcess G p n T M hM).rawLawFrom (0, ∅)
      (QuittingDDPOwnQuitEvent G p n T M hM i) ≤ 1 := by
  let P := quittingDecisionProcess G p n T M hM
  let μ := P.rawLawFrom (0, ∅)
  letI : IsProbabilityMeasure μ := P.isProbabilityMeasure_rawLawFrom (0, ∅)
  calc
    (∑' i : Fin T, μ (QuittingDDPOwnQuitEvent G p n T M hM i)) ≤
        μ Set.univ := tsum_measure_le_measure_univ
          (fun i => (measurableSet_quittingDDPOwnQuitEvent G p n T M hM i).nullMeasurableSet)
          (quittingDDPOwnQuitEvent_pairwise_aedisjoint G p n T M hM S)
    _ = 1 := measure_univ

private theorem quittingDDPRawLaw_ownQuitEvent
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M)
    (S : DDPSemantics (quittingDecisionProcess G p n T M hM))
    {i : ℕ} (hi : i < T) :
    (quittingDecisionProcess G p n T M hM).rawLawFrom (0, ∅)
        (QuittingDDPOwnQuitEvent G p n T M hM i) =
      (quittingDecisionProcess G p n T M hM).rawLawFrom (0, ∅)
          {stages | (stages i).1 = (i, ∅)} * ENNReal.ofReal (p i n : ℝ) := by
  let P := quittingDecisionProcess G p n T M hM
  have hevent : QuittingDDPOwnQuitEvent G p n T M hM i =
      {stages : ℕ → DDPStage P | stages i = ⟨(i, ∅), true⟩} := by
    ext stages
    simp only [QuittingDDPOwnQuitEvent, mem_setOf_eq]
    constructor
    · rintro ⟨hstate, haction⟩
      apply Sigma.ext hstate
      exact haction
    · intro hstage
      exact ⟨congrArg Sigma.fst hstage, (Sigma.mk.inj_iff.mp hstage).2⟩
  rw [hevent]
  have hstage := P.rawLawFrom_stage_eq_state_mul_choose S (0, ∅) i (i, ∅) true
  rw [hstage]
  congr 1
  change quittingDDPChoose G p n T (i, ∅) true = ENNReal.ofReal (p i n : ℝ)
  have hlive : IsQuittingDDPLive T (i, (∅ : Finset G.Player)) := ⟨hi, rfl⟩
  simp [quittingDDPChoose, hlive, quittingBernoulli, PMF.ofFintype_apply]

private theorem quittingDDPRawStateVariation_eq_zero_of_not_live
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T i : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M)
    (state : QuittingDDPState G) (hlive : ¬IsQuittingDDPLive T state) :
    (quittingDecisionProcess G p n T M hM).rawStateVariation (0, ∅) i state = 0 := by
  let P := quittingDecisionProcess G p n T M hM
  rw [DiscreteDecisionProcess.rawStateVariation]
  apply mul_eq_zero_of_right
  calc
    (∑' action, P.choose state action *
        ENNReal.ofReal |DDPStage.increment P ⟨state, action⟩|) =
        ∑' _action : Bool, 0 := by
      apply tsum_congr
      intro action
      have hincrement : DDPStage.increment P ⟨state, action⟩ = 0 := by
        change quittingDDPValueY G p n T state action -
          quittingDDPValueX G p n T state = 0
        simp [quittingDDPValueY, hlive]
      rw [hincrement]
      simp
    _ = 0 := tsum_zero

/-- An unreachable state has zero mass under the raw law of the quitting DDP. -/
private theorem quittingDDPRawLaw_state_eq_zero_of_unreachable
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M)
    (S : DDPSemantics (quittingDecisionProcess G p n T M hM)) (i : ℕ)
    (state : QuittingDDPState G) (hunreachable : ¬IsQuittingDDPReachable T i state) :
    (quittingDecisionProcess G p n T M hM).rawLawFrom (0, ∅)
        {stages | (stages i).1 = state} = 0 := by
  let P := quittingDecisionProcess G p n T M hM
  let H := {path : DDPFinitePath P i // path.x (Fin.last i) = state}
  let C : H → Set (ℕ → DDPStage P) := fun path =>
    DDPPath.ofRaw P ⁻¹' DDPCylinder P path.1
  have hstateUnion : {stages : ℕ → DDPStage P | (stages i).1 = state} = ⋃ path, C path := by
    ext stages
    simp only [mem_setOf_eq, mem_iUnion, C]
    constructor
    · intro hstate
      let path := (DDPPath.ofRaw P stages).prefix P i
      refine ⟨⟨path, ?_⟩, rfl⟩
      simpa [path, DDPPath.prefix, DDPPath.ofRaw] using hstate
    · rintro ⟨path, hpath⟩
      change (DDPPath.ofRaw P stages).prefix P i = path.1 at hpath
      have hlast := congrArg (fun q : DDPFinitePath P i => q.x (Fin.last i)) hpath
      exact hlast.trans path.2
  have hmeasure (path : H) : P.rawLawFrom (0, ∅) (C path) = 0 := by
    by_cases hstart : path.1.x 0 = (0, ∅)
    · rw [P.rawLawFrom_ddpCylinder (0, ∅) path.1 hstart]
      by_contra hprobability
      apply hunreachable
      have hreachable := quittingDDPFinitePath_reachable G p n T M hM path.1 hstart
        hprobability (Fin.last i)
      rw [path.2] at hreachable
      simpa [P] using hreachable
    · exact P.rawLawFrom_ddpCylinder_eq_zero_of_wrong S (0, ∅) path.1 hstart
  change P.rawLawFrom (0, ∅) {stages | (stages i).1 = state} = 0
  rw [hstateUnion]
  apply nonpos_iff_eq_zero.mp
  calc
    P.rawLawFrom (0, ∅) (⋃ path, C path) ≤ ∑' path, P.rawLawFrom (0, ∅) (C path) :=
      measure_iUnion_le _
    _ = 0 := by simp_rw [hmeasure]; simp

/-- At a live state, the Bernoulli action variation is at most twice own quit mass times `M`. -/
private theorem quittingDDP_live_actionVariation_le
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T i : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M) (hi : i < T) :
    ∑' action : Bool,
        ((quittingDecisionProcess G p n T M hM).choose (i, ∅) action).toReal *
          |DDPStage.increment (quittingDecisionProcess G p n T M hM)
            ⟨(i, ∅), action⟩| ≤ 2 * M * (p i n : ℝ) := by
  let P := quittingDecisionProcess G p n T M hM
  let q : ℝ := p i n
  let a := quittingDDPValueY G p n T (i, ∅) true
  let b := quittingDDPValueY G p n T (i, ∅) false
  let x := quittingDDPValueX G p n T (i, ∅)
  have hlive : IsQuittingDDPLive T (i, (∅ : Finset G.Player)) := ⟨hi, rfl⟩
  have hq0 : 0 ≤ q := (p i n).property.1
  have hq1 : q ≤ 1 := (p i n).property.2
  have haverage : x = q * a + (1 - q) * b := by
    have h := quittingDDPHarmonicX G p n T (i, ∅)
    rw [tsum_fintype, Fintype.sum_bool] at h
    simpa only [P, q, a, b, x, quittingDDPChoose, hlive, if_pos,
      quittingBernoulli_apply_true_toReal, quittingBernoulli_apply_false_toReal]
      using h
  have habs : |a - b| ≤ M := by
    exact abs_sub_le_of_mem_coordinateInterval G n hM
      (quittingDDPValueY_mem_coordinateInterval G p n T (i, ∅) true)
      (quittingDDPValueY_mem_coordinateInterval G p n T (i, ∅) false)
  have hscaled : (1 - q) * |a - b| ≤ M := by
    calc
      (1 - q) * |a - b| ≤ 1 * |a - b| := by
        exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ M := by simpa using habs
  change ∑' action : Bool, (quittingDDPChoose G p n T (i, ∅) action).toReal *
    |quittingDDPValueY G p n T (i, ∅) action -
      quittingDDPValueX G p n T (i, ∅)| ≤ _
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [quittingDDPChoose, hlive, if_pos, quittingBernoulli_apply_true_toReal,
    quittingBernoulli_apply_false_toReal]
  change q * |a - x| + (1 - q) * |b - x| ≤ 2 * M * q
  rw [haverage]
  rw [show b - (q * a + (1 - q) * b) = -q * (a - b) by ring]
  rw [show a - (q * a + (1 - q) * b) = (1 - q) * (a - b) by ring]
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hq0,
    abs_of_nonneg (sub_nonneg.mpr hq1)]
  calc
    q * ((1 - q) * |a - b|) + (1 - q) * (q * |a - b|) =
        2 * q * ((1 - q) * |a - b|) := by ring
    _ ≤ 2 * q * M := mul_le_mul_of_nonneg_left hscaled (by positivity)
    _ = 2 * M * q := by ring

private theorem quittingDDPRawStateVariation_live_le
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T i : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M)
    (S : DDPSemantics (quittingDecisionProcess G p n T M hM)) (hi : i < T) :
    (quittingDecisionProcess G p n T M hM).rawStateVariation (0, ∅) i (i, ∅) ≤
      ENNReal.ofReal (2 * M) *
        (quittingDecisionProcess G p n T M hM).rawLawFrom (0, ∅)
          (QuittingDDPOwnQuitEvent G p n T M hM i) := by
  let P := quittingDecisionProcess G p n T M hM
  let μ := P.rawLawFrom (0, ∅) {stages | (stages i).1 = (i, ∅)}
  let average : ℝ := ∑' action : Bool,
    (quittingDDPChoose G p n T (i, ∅) action).toReal *
      |quittingDDPValueY G p n T (i, ∅) action -
        quittingDDPValueX G p n T (i, ∅)|
  have haverage : average ≤ 2 * M * (p i n : ℝ) := by
    change (∑' action : Bool,
      (quittingDDPChoose G p n T (i, ∅) action).toReal *
        |quittingDDPValueY G p n T (i, ∅) action -
          quittingDDPValueX G p n T (i, ∅)|) ≤ 2 * M * (p i n : ℝ)
    exact quittingDDP_live_actionVariation_le G p n T i M hM hi
  have hμtop : μ ≠ ⊤ := by
    letI : IsProbabilityMeasure (P.rawLawFrom (0, ∅)) :=
      P.isProbabilityMeasure_rawLawFrom (0, ∅)
    exact measure_ne_top _ _
  rw [P.rawStateVariation_eq_ofReal]
  change ENNReal.ofReal (μ.toReal * average) ≤ _
  calc
    ENNReal.ofReal (μ.toReal * average) ≤
        ENNReal.ofReal (μ.toReal * (2 * M * (p i n : ℝ))) := by
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left haverage ENNReal.toReal_nonneg)
    _ = ENNReal.ofReal (2 * M) * (μ * ENNReal.ofReal (p i n : ℝ)) := by
      rw [show μ.toReal * (2 * M * (p i n : ℝ)) =
        (2 * M) * (μ.toReal * (p i n : ℝ)) by ring]
      rw [ENNReal.ofReal_mul (by linarith [hM.1] : 0 ≤ 2 * M)]
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      rw [ENNReal.ofReal_toReal hμtop]
    _ = ENNReal.ofReal (2 * M) * P.rawLawFrom (0, ∅)
        (QuittingDDPOwnQuitEvent G p n T M hM i) := by
      rw [quittingDDPRawLaw_ownQuitEvent G p n T M hM S hi]

private theorem quittingDDPRawStateVariation_eq_zero_of_unreachable
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T i : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M)
    (S : DDPSemantics (quittingDecisionProcess G p n T M hM))
    (state : QuittingDDPState G) (hunreachable : ¬IsQuittingDDPReachable T i state) :
    (quittingDecisionProcess G p n T M hM).rawStateVariation (0, ∅) i state = 0 := by
  rw [DiscreteDecisionProcess.rawStateVariation]
  rw [quittingDDPRawLaw_state_eq_zero_of_unreachable G p n T M hM S i state
    hunreachable]
  simp

private theorem quittingDDP_tsum_stateVariation_le
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T i : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M)
    (S : DDPSemantics (quittingDecisionProcess G p n T M hM)) :
    (∑' state : QuittingDDPState G,
      (quittingDecisionProcess G p n T M hM).rawStateVariation (0, ∅) i state) ≤
        if i < T then ENNReal.ofReal (2 * M) *
          (quittingDecisionProcess G p n T M hM).rawLawFrom (0, ∅)
            (QuittingDDPOwnQuitEvent G p n T M hM i) else 0 := by
  let P := quittingDecisionProcess G p n T M hM
  by_cases hi : i < T
  · rw [if_pos hi]
    rw [tsum_eq_single (i, ∅)]
    · exact quittingDDPRawStateVariation_live_le G p n T i M hM S hi
    · intro state hstate
      by_cases hlive : IsQuittingDDPLive T state
      · apply quittingDDPRawStateVariation_eq_zero_of_unreachable G p n T i M hM S
        intro hreachable
        rcases hreachable with hcurrent | hterminal
        · apply hstate
          apply Prod.ext
          · simpa [min_eq_left hi.le] using hcurrent.2
          · exact hcurrent.1
        · rw [hlive.2] at hterminal
          exact Finset.not_nonempty_empty hterminal.1
      · exact quittingDDPRawStateVariation_eq_zero_of_not_live G p n T i M hM state hlive
  · rw [if_neg hi]
    calc
      (∑' state : QuittingDDPState G, P.rawStateVariation (0, ∅) i state) =
          ∑' _state : QuittingDDPState G, 0 := by
        apply tsum_congr
        intro state
        by_cases hlive : IsQuittingDDPLive T state
        · apply quittingDDPRawStateVariation_eq_zero_of_unreachable G p n T i M hM S
          intro hreachable
          rcases hreachable with hcurrent | hterminal
          · have hmin : min i T = T := min_eq_right (le_of_not_gt hi)
            have htime : state.1 = T := hcurrent.2.trans hmin
            linarith [hlive.1]
          · rw [hlive.2] at hterminal
            exact Finset.not_nonempty_empty hterminal.1
        · exact quittingDDPRawStateVariation_eq_zero_of_not_live G p n T i M hM state hlive
      _ = 0 := tsum_zero
      _ ≤ 0 := le_rfl

/-- The finite quitting DDP has expected total variation at most `2M`. -/
private theorem quittingDDP_expectedVariation_le
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M)
    (S : DDPSemantics (quittingDecisionProcess G p n T M hM)) :
    ExpectedDDPVariation (quittingDecisionProcess G p n T M hM) S ≤
      ENNReal.ofReal (2 * M) := by
  let P := quittingDecisionProcess G p n T M hM
  let c := ENNReal.ofReal (2 * M)
  let mass : ℕ → ℝ≥0∞ := fun i =>
    (quittingDecisionProcess G p n T M hM).rawLawFrom (0, ∅)
      (QuittingDDPOwnQuitEvent G p n T M hM i)
  rw [ExpectedDDPVariation.eq_tsum_rawStateVariation P S]
  rw [ENNReal.tsum_prod]
  calc
    (∑' i : ℕ, ∑' state : QuittingDDPState G,
        P.rawStateVariation (0, ∅) i state) ≤
        ∑' i : ℕ, if i < T then c * mass i else 0 := by
      exact ENNReal.tsum_le_tsum fun i =>
        quittingDDP_tsum_stateVariation_le G p n T i M hM S
    _ = ∑ i ∈ Finset.range T, c * mass i := by
      rw [tsum_eq_sum (s := Finset.range T) (fun i hi => by
        rw [Finset.mem_range, not_lt] at hi
        rw [if_neg (not_lt_of_ge hi)])]
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos (Finset.mem_range.mp hi)]
    _ = ∑ i : Fin T, c * mass i := by
      exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => c * mass i) T).symm
    _ = c * ∑' i : Fin T, mass i := by
      rw [tsum_fintype, Finset.mul_sum]
    _ ≤ c * 1 := by
      gcongr
      exact quittingDDPOwnQuitEvent_totalMass_le_one G p n T M hM S
    _ = ENNReal.ofReal (2 * M) := by simp [c]

/-- The generated quitting DDP crosses an `ε` advantage with probability at most
` ε² / M²` under the numerical hypothesis of Proposition 3. -/
private theorem quittingDDP_rawAbsoluteCrossing_le
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    {M ε δ : ℝ} (hM : IsQuittingPayoffDifferenceBound G M)
    (hε : 0 < ε) (hδ : 0 < δ) (hsmall : δ < ε ^ 4 / (2 * M ^ 3))
    (horbit : GeneratesFRowOrbit G δ p)
    (S : DDPSemantics (quittingDecisionProcess G p n T M hM)) :
    (quittingDecisionProcess G p n T M hM).rawLawFrom (0, ∅)
        {stage | ∃ l, ε ≤ |(quittingDecisionProcess G p n T M hM).rawAdvantage stage l|} ≤
      ENNReal.ofReal (ε ^ 2 / M ^ 2) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM.1
  have hrho : 0 < ε ^ 2 / M ^ 2 := div_pos (sq_pos_of_pos hε) (sq_pos_of_pos hMpos)
  have hB : 0 < 2 * M := mul_pos (by norm_num) hMpos
  have hnumerical : δ ≤ ε ^ 2 * (ε ^ 2 / M ^ 2) / (2 * M) := by
    calc
      δ ≤ ε ^ 4 / (2 * M ^ 3) := hsmall.le
      _ = ε ^ 2 * (ε ^ 2 / M ^ 2) / (2 * M) := by
        field_simp
  exact DiscreteDecisionProcess.rawAbsoluteCrossing_le
    (quittingDecisionProcess G p n T M hM) S hδ hε hrho hB
      (quittingDecisionProcess_balanced G p n T M hM hδ.le horbit)
      (quittingDDP_expectedVariation_le G p n T M hM S) hnumerical

/-- The unique live prefix of length `T` in the quitting decision process. -/
private def quittingDDPLivePath
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M) :
    DDPFinitePath (quittingDecisionProcess G p n T M hM) T where
  x i := (i, ∅)
  y _i := false

/-- Each factor of the live DDP prefix is exactly the corresponding row-survival mass. -/
private theorem quittingDDPLivePath_factor
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M) (i : Fin T) :
    let path := quittingDDPLivePath G p n T M hM
    (quittingDecisionProcess G p n T M hM).choose (path.x i.castSucc) (path.y i) *
        (quittingDecisionProcess G p n T M hM).move
          (path.x i.castSucc) (path.y i) (path.x i.succ) =
      ENNReal.ofReal (1 - QuitProbability G (p i)) := by
  classical
  let row := (p i).replace G n 0
  let advance : Finset G.Player → QuittingDDPState G := fun A => (i + 1, A)
  have hadvance : Function.Injective advance := fun A B h => congrArg Prod.snd h
  have hmap : ((coalitionPMF G row).map advance) (advance ∅) = coalitionPMF G row ∅ := by
    rw [PMF.map_apply, tsum_eq_single ∅]
    · simp
    · intro A hA
      rw [if_neg]
      exact fun h => hA (hadvance h.symm)
  have hlive : IsQuittingDDPLive T (i, (∅ : Finset G.Player)) := ⟨i.2, rfl⟩
  change quittingDDPChoose G p n T (i, ∅) false *
      quittingDDPMove G p n T (i, ∅) false (i + 1, ∅) = _
  simp only [quittingDDPChoose, quittingDDPMove, hlive, if_pos,
    Bool.false_eq_true, if_false]
  change quittingBernoulli (p i n) false *
      ((coalitionPMF G row).map advance) (advance ∅) = _
  rw [hmap]
  rw [quittingBernoulli, PMF.ofFintype_apply, coalitionPMF, PMF.ofFintype_apply]
  simp only [Bool.false_eq_true, if_false]
  rw [← ENNReal.ofReal_mul (sub_nonneg.mpr (p i n).property.2)]
  congr 1
  have hempty : CoalitionProbability G row ∅ = 1 - QuitProbability G row := by
    simp [CoalitionProbability, QuitProbability]
  rw [hempty]
  have hreplace := one_sub_quitProbability_replace G (p i) n (p i n)
  rw [QuitRow.replace_self] at hreplace
  exact hreplace.symm

/-- The live DDP cylinder has the quitting profile's finite survival probability. -/
private theorem quittingDDPLivePath_probability
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M) :
    (quittingDDPLivePath G p n T M hM).probability
        (quittingDecisionProcess G p n T M hM) =
      ENNReal.ofReal (tailSurvival G p 0 T) := by
  rw [DDPFinitePath.probability]
  simp_rw [quittingDDPLivePath_factor G p n T M hM]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    simp only [tailSurvival, zero_add]
    exact Fin.prod_univ_eq_prod_range
      (fun i : ℕ => 1 - QuitProbability G (p i)) T
  · intro i _hi
    exact sub_nonneg.mpr (quitProbability_mem_Icc G (p i)).2

/-- Along the live prefix, the DDP advantage is the player's continue ledger. -/
private theorem quittingDDPLivePath_advantage
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (k : ℕ)
    (M : ℝ) (hM : IsQuittingPayoffDifferenceBound G M) :
    (quittingDDPLivePath G p n (k + 1) M hM).advantage
        (quittingDecisionProcess G p n (k + 1) M hM) =
      ContinueLedger G p n (k + 1) := by
  rw [DDPFinitePath.advantage, ContinueLedger]
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    ForcedContinuePayoff G (QuitTailPayoff G p (i + 1)) (p i) n -
      QuitTailPayoff G p i n) (k + 1)]
  apply Finset.sum_congr rfl
  intro i _hi
  have hlive : IsQuittingDDPLive (k + 1) (i, (∅ : Finset G.Player)) := ⟨i.2, rfl⟩
  have hempty : ¬(∅ : Finset G.Player).Nonempty := Finset.not_nonempty_empty
  change quittingDDPValueY G p n (k + 1) (i, ∅) false -
      quittingDDPValueX G p n (k + 1) (i, ∅) = _
  simp only [quittingDDPValueY, hlive, if_pos, Bool.false_eq_true, if_false,
    quittingDDPValueX, hempty, dite_false, min_eq_left (le_of_lt i.2)]

/-- A ledger crossing forces the live-prefix survival probability below the DDP crossing bound. -/
private theorem tailSurvival_le_of_continueLedger_crossing
    (G : QuittingGame) (p : QuitProfile G) (n : G.Player) (T : ℕ)
    {M ε δ : ℝ} (hM : IsQuittingPayoffDifferenceBound G M)
    (hε : 0 < ε) (hδ : 0 < δ) (hsmall : δ < ε ^ 4 / (2 * M ^ 3))
    (horbit : GeneratesFRowOrbit G δ p) (hledger : ε ≤ ContinueLedger G p n T) :
    tailSurvival G p 0 T ≤ ε ^ 2 / M ^ 2 := by
  rcases ddpSemantics_exists (quittingDecisionProcess G p n T M hM) with ⟨S⟩
  have hcross := quittingDDP_rawAbsoluteCrossing_le G p n T hM hε hδ hsmall horbit S
  cases T with
  | zero =>
      rw [ContinueLedger.zero] at hledger
      linarith
  | succ k =>
      let P := quittingDecisionProcess G p n (k + 1) M hM
      let path := quittingDDPLivePath G p n (k + 1) M hM
      let cylinder : Set (ℕ → DDPStage P) := DDPPath.ofRaw P ⁻¹' DDPCylinder P path
      have hsubset : cylinder ⊆
          {stage | ∃ l, ε ≤ |P.rawAdvantage stage l|} := by
        intro stage hstage
        refine ⟨k, ?_⟩
        have hadvantage : P.rawAdvantage stage k = ContinueLedger G p n (k + 1) := by
          calc
            P.rawAdvantage stage k =
                DDPAdvantage P (DDPPath.ofRaw P stage) k := rfl
            _ = ((DDPPath.ofRaw P stage).prefix P (k + 1)).advantage P :=
              (DDPFinitePath.advantage_prefix P (DDPPath.ofRaw P stage) k).symm
            _ = path.advantage P := by rw [hstage]
            _ = ContinueLedger G p n (k + 1) :=
              quittingDDPLivePath_advantage G p n k M hM
        rw [hadvantage, abs_of_nonneg (hε.le.trans hledger)]
        exact hledger
      have hcylinder : P.rawLawFrom (0, ∅) cylinder =
          ENNReal.ofReal (tailSurvival G p 0 (k + 1)) := by
        rw [P.rawLawFrom_ddpCylinder (0, ∅) path rfl]
        exact quittingDDPLivePath_probability G p n (k + 1) M hM
      have hbound : ENNReal.ofReal (tailSurvival G p 0 (k + 1)) ≤
          ENNReal.ofReal (ε ^ 2 / M ^ 2) := by
        rw [← hcylinder]
        exact (measure_mono hsubset).trans hcross
      exact (ENNReal.ofReal_le_ofReal_iff
        (div_nonneg (sq_nonneg ε) (sq_nonneg M))).mp hbound

/--
Proposition 3.  For `0 < ε ≤ 1`, `0 < δ < ε⁴/(2M³)`, an `ε`-rational
`F_δ` profile with unbounded quit mass generates a `3ε`-equilibrium.  The generated
profile follows the supplied profile up to a stopping stage and then switches to a
min-max punishment; the proposition only asserts the resulting equilibrium's existence.
Here `M` is explicitly the paper's payoff-difference bound.
-/
theorem proposition3 (G : QuittingGame) {M ε δ : ℝ}
    (hM : IsQuittingPayoffDifferenceBound G M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hsmall : δ < ε ^ 4 / (2 * M ^ 3)) (p : QuitProfile G)
    (hrational : ∀ i, IsRational G ε (QuitTailPayoff G p i))
    (hmass : HasUnboundedQuitMass G p)
    (horbit : GeneratesFRowOrbit G δ p) :
    ∃ equilibrium : QuitProfile G,
      IsQuitEpsilonEquilibrium G (3 * ε) equilibrium := by
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
    GeneratesFRowOrbit G ε p ∧
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
  obtain ⟨equilibrium, hequilibrium⟩ := by
    apply proposition3 G hM he he1 hδ hδsmall profile
    · intro i n
      exact le_trans (by linarith : MinMaxQuit G n - e ≤ MinMaxQuit G n - δ)
        (hrational i n)
    · exact CycleProfile.hasUnboundedQuitMass G hk block hpositive
    · exact horbit
  refine ⟨equilibrium, ?_⟩
  intro n deviation
  exact (hequilibrium n deviation).trans (by linarith)

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
Theorem 3 as printed in 2007: in the absence of stationary and instant approximate
equilibria, approximate equilibrium and the four orbit conditions are equivalent.
-/
theorem theorem3 (G : QuittingGame)
    (hstationary : ¬HasStationaryApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    EquivalentFive (HasQuitApproximateEquilibria G) (CyclicOrbitCondition G)
      (FiniteNearOrbitCondition G) (InfiniteOrbitCondition G)
      (ExtendedOrbitCondition G) := by
  sorry

/-- Simon (2012), Theorem 2.1, with the corrected stationarily-generated hypothesis. -/
theorem theorem3_corrected_2012 (G : QuittingGame)
    (hstationary : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    EquivalentFive (HasQuitApproximateEquilibria G) (CyclicOrbitCondition G)
      (FiniteNearOrbitCondition G) (InfiniteOrbitCondition G)
      (ExtendedOrbitCondition G) := by
  sorry

/-!
The printed proof of Theorem 3 invokes Lemma 5. Simon's 2012 correction says that this
argument requires nonexistence of stationarily generated approximate equilibria. This
repairs the proof's hypothesis; it does not by itself refute the old theorem statement.
-/

/-!
The remark after Theorem 3 records that Solan--Vieille had proved `(iv) → (i),(ii)`
when every solo payoff is positive, and that Solan showed the minimal cycle length in
clause (ii) may depend on `ε`.
-/

/-- A row payoff is the convex combination of its two own-action endpoint payoffs. -/
private theorem quittingOneStagePayoff_eq_endpointCombination
    (G : QuittingGame) (r : Payoff G.Player) (p : QuitRow G) (n : G.Player) :
    QuittingOneStagePayoff G r p n =
      (p n : ℝ) * ForcedQuitPayoff G p n +
        (1 - (p n : ℝ)) * ForcedContinuePayoff G r p n := by
  have hself : p.replace G n (p n) = p := QuitRow.replace_self G p n
  have hsurvival := one_sub_quitProbability_replace G p n (p n)
  rw [hself] at hsurvival
  have hreward := quittingRewardPart_replace_affine G p n (p n) n
  rw [hself] at hreward
  change (1 - QuitProbability G p) * r n + quittingRewardPart G p n =
    (p n : ℝ) * ((1 - QuitProbability G (p.replace G n 1)) * 0 +
      quittingRewardPart G (p.replace G n 1) n) +
    (1 - (p n : ℝ)) * ((1 - QuitProbability G (p.replace G n 0)) * r n +
      quittingRewardPart G (p.replace G n 0) n)
  rw [hsurvival, hreward]
  ring

/-- When `n` is forced to quit, only `n` quits exactly when every opponent continues. -/
private theorem coalitionProbability_forcedSolo_eq_survival
    (G : QuittingGame) (p : QuitRow G) (n : G.Player) :
    CoalitionProbability G (p.replace G n 1) {n} =
      1 - QuitProbability G (p.replace G n 0) := by
  classical
  simp only [CoalitionProbability, QuitProbability, QuitRow.replace]
  rw [Finset.prod_singleton]
  simp only [if_pos, Set.Icc.coe_one, one_mul]
  ring_nf
  have hfilter : Finset.univ.filter (fun k : G.Player => k ∉ ({n} : Finset G.Player)) =
      Finset.univ.erase n := by
    ext k
    simp [eq_comm]
  rw [hfilter]
  have hprod := Finset.mul_prod_erase Finset.univ
    (fun k : G.Player => 1 - (((if k = n then (0 : Set.Icc (0 : ℝ) 1) else p k) :
      Set.Icc (0 : ℝ) 1) : ℝ)) (Finset.mem_univ n)
  simp only [if_pos, Set.Icc.coe_zero, sub_zero, one_mul] at hprod
  rw [← hprod]
  apply Finset.prod_congr rfl
  intro k hk
  have hkn : k ≠ n := Finset.ne_of_mem_erase hk
  simp [hkn]

/-- Forced quitting loses at most `M` times the probability that an opponent also quits. -/
private theorem forcedQuitPayoff_ge_solo_sub_otherQuitMass
    (G : QuittingGame) {M : ℝ} (hM : IsQuittingPayoffDifferenceBound G M)
    (p : QuitRow G) (n : G.Player) :
    SoloPayoff G n - M * QuitProbability G (p.replace G n 0) ≤
      ForcedQuitPayoff G p n := by
  classical
  let pOne := p.replace G n 1
  let qOther := QuitProbability G (p.replace G n 0)
  let singleton : {A : Finset G.Player // A.Nonempty} :=
    ⟨{n}, Finset.singleton_nonempty n⟩
  have hqOne : QuitProbability G pOne = 1 := by
    exact quitProbability_replace_one G p n
  have hmass :
      (∑ A ∈ Finset.univ.powerset,
        if _hA : A.Nonempty then CoalitionProbability G pOne A else 0) = 1 := by
    rw [nonemptyCoalitionMass_eq_quitProbability, hqOne]
  have hsingleton : CoalitionProbability G pOne {n} = 1 - qOther := by
    exact coalitionProbability_forcedSolo_eq_survival G p n
  have hbound : ∀ A : {A : Finset G.Player // A.Nonempty},
      singleton.val ≠ A.val → SoloPayoff G n - M ≤ G.reward A n := by
    intro A hval
    have hdiff := hM.2.1 A singleton n
    have hlower := neg_lt_of_abs_lt hdiff
    dsimp only [singleton, SoloPayoff] at hlower ⊢
    linarith
  let massTerm : Finset G.Player → ℝ := fun A =>
    if _hA : A.Nonempty then CoalitionProbability G pOne A else 0
  let rewardTerm : Finset G.Player → ℝ := fun A =>
    if hA : A.Nonempty then CoalitionProbability G pOne A * G.reward ⟨A, hA⟩ n else 0
  have hnmem : ({n} : Finset G.Player) ∈ Finset.univ.powerset := by simp
  have hmassDecomp := Finset.sum_erase_add Finset.univ.powerset massTerm hnmem
  have hotherMass :
      (∑ A ∈ Finset.univ.powerset.erase {n}, massTerm A) = qOther := by
    dsimp only [massTerm] at hmassDecomp
    simp only [Finset.singleton_nonempty, dite_true] at hmassDecomp
    rw [hmass, hsingleton] at hmassDecomp
    linarith
  have hotherReward :
      qOther * (SoloPayoff G n - M) ≤
        ∑ A ∈ Finset.univ.powerset.erase {n}, rewardTerm A := by
    rw [← hotherMass, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro A hA
    have hne : A ≠ {n} := Finset.ne_of_mem_erase hA
    dsimp only [massTerm, rewardTerm]
    split_ifs with hnonempty
    · apply mul_le_mul_of_nonneg_left
        (hbound ⟨A, hnonempty⟩ (by simpa [singleton] using hne.symm))
      simp only [CoalitionProbability]
      exact mul_nonneg
        (Finset.prod_nonneg fun k _ => (pOne k).property.1)
        (Finset.prod_nonneg fun k _ => sub_nonneg.mpr (pOne k).property.2)
    · simp
  have hrewardDecomp := Finset.sum_erase_add Finset.univ.powerset rewardTerm hnmem
  have hreward :
      SoloPayoff G n - M * qOther ≤
        ∑ A ∈ Finset.univ.powerset, rewardTerm A := by
    calc
      SoloPayoff G n - M * qOther =
          (1 - qOther) * SoloPayoff G n +
            qOther * (SoloPayoff G n - M) := by ring
      _ = CoalitionProbability G pOne {n} * SoloPayoff G n +
          qOther * (SoloPayoff G n - M) := by rw [hsingleton]
      _ ≤ rewardTerm {n} +
          ∑ A ∈ Finset.univ.powerset.erase {n}, rewardTerm A := by
        have hsingleReward : rewardTerm {n} =
            CoalitionProbability G pOne {n} * SoloPayoff G n := by
          simp [rewardTerm, SoloPayoff]
        rw [hsingleReward]
        linarith
      _ = _ := by linarith
  change SoloPayoff G n - M * qOther ≤
    (1 - QuitProbability G pOne) * (0 : Payoff G.Player) n +
      quittingRewardPart G pOne n
  rw [hqOne]
  norm_num only [sub_self, zero_mul, zero_add]
  simpa only [quittingRewardPart, rewardTerm] using hreward

/--
Against fixed stationary opponents who eventually quit, the min-max is capped by the
better of quitting now and continuing until an opponent quits.
-/
private theorem minMaxQuit_le_max_forcedQuit_stationaryContinue
    (G : QuittingGame) {M : ℝ} (hM : IsQuittingPayoffDifferenceBound G M)
    (p : QuitRow G) (n : G.Player)
    (hq : 0 < QuitProbability G (p.replace G n 0)) :
    MinMaxQuit G n ≤ max (ForcedQuitPayoff G p n)
      (quittingRewardPart G (p.replace G n 0) n /
        QuitProbability G (p.replace G n 0)) := by
  let pZero := p.replace G n 0
  let qOther := QuitProbability G pZero
  let d := quittingRewardPart G pZero n / qOther
  let C := max (ForcedQuitPayoff G p n) d
  let profile : QuitProfile G := fun _ => pZero
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.1
  have hpayoffBound : ∀ z : QuitProfile G, |QuitPayoff G z n| ≤ M := fun z =>
    abs_quitPayoff_le G z n hM0 (fun A => le_of_lt (hM.2.2 A n))
  have hinnerAbove : ∀ z : QuitProfile G, BddAbove (range fun deviation :
      ℕ → Set.Icc (0 : ℝ) 1 => QuitPayoff G (z.replace G n deviation) n) := by
    intro z
    refine ⟨M, ?_⟩
    rintro _ ⟨deviation, rfl⟩
    exact (le_abs_self _).trans (hpayoffBound _)
  have houterBelow : BddBelow (range fun z : QuitProfile G =>
      ⨆ deviation : ℕ → Set.Icc (0 : ℝ) 1,
        QuitPayoff G (z.replace G n deviation) n) := by
    refine ⟨-M, ?_⟩
    rintro _ ⟨z, rfl⟩
    let deviation : ℕ → Set.Icc (0 : ℝ) 1 := fun _ => 0
    exact (neg_le_of_abs_le (hpayoffBound (z.replace G n deviation))).trans
      (le_ciSup (hinnerAbove z) deviation)
  have hpZeroSelf : pZero.replace G n 0 = pZero := by
    have hn : pZero n = (0 : Set.Icc (0 : ℝ) 1) := by
      simp [pZero, QuitRow.replace]
    rw [← hn]
    exact QuitRow.replace_self G pZero n
  have hpZeroOne : pZero.replace G n 1 = p.replace G n 1 := by
    funext k
    by_cases hkn : k = n
    · simp [pZero, QuitRow.replace, hkn]
    · simp [pZero, QuitRow.replace, hkn]
  have hforcedReward : quittingRewardPart G (pZero.replace G n 1) n =
      ForcedQuitPayoff G p n := by
    rw [hpZeroOne]
    change quittingRewardPart G (p.replace G n 1) n =
      (1 - QuitProbability G (p.replace G n 1)) * (0 : Payoff G.Player) n +
        quittingRewardPart G (p.replace G n 1) n
    rw [quitProbability_replace_one]
    norm_num
  have hqOther : qOther ∈ Set.Icc (0 : ℝ) 1 := quitProbability_mem_Icc G pZero
  have hqPositive : 0 < qOther := by simpa only [qOther, pZero] using hq
  have hdReward : quittingRewardPart G pZero n = qOther * d := by
    dsimp only [d]
    field_simp [ne_of_gt hqPositive]
  rw [MinMaxQuit]
  apply le_trans (ciInf_le houterBelow profile)
  apply ciSup_le
  intro deviation
  let deviated := profile.replace G n deviation
  have hrow : ∀ t, deviated t = pZero.replace G n (deviation t) := fun _ => rfl
  have hrewards : ∀ t,
      quittingRewardPart G (deviated t) n ≤ C * QuitProbability G (deviated t) := by
    intro t
    have hsurvival := one_sub_quitProbability_replace G pZero n (deviation t)
    rw [hpZeroSelf] at hsurvival
    have hquit : QuitProbability G (pZero.replace G n (deviation t)) =
        (deviation t : ℝ) + (1 - (deviation t : ℝ)) * qOther := by
      linarith
    rw [hrow, quittingRewardPart_replace_affine, hforcedReward, hpZeroSelf, hdReward]
    calc
      (deviation t : ℝ) * ForcedQuitPayoff G p n +
          (1 - (deviation t : ℝ)) * (qOther * d) =
          (deviation t : ℝ) * ForcedQuitPayoff G p n +
            ((1 - (deviation t : ℝ)) * qOther) * d := by ring
      _ ≤ (deviation t : ℝ) * C +
          ((1 - (deviation t : ℝ)) * qOther) * C := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (deviation t).property.1
        · exact mul_le_mul_of_nonneg_left (le_max_right _ _)
            (mul_nonneg (sub_nonneg.mpr (deviation t).property.2) hqOther.1)
      _ = C * QuitProbability G (deviated t) := by
        change _ = C * QuitProbability G (pZero.replace G n (deviation t))
        rw [hquit]
        ring
  have hvanish : Tendsto (tailSurvival G deviated 0) atTop (nhds 0) := by
    apply squeeze_zero
    · intro t
      exact Finset.prod_nonneg fun k _ =>
        sub_nonneg.mpr (quitProbability_mem_Icc G _).2
    · intro t
      calc
        tailSurvival G deviated 0 t ≤
            ∏ k ∈ Finset.range t, (1 - qOther) := by
          apply Finset.prod_le_prod
          · intro k hk
            exact sub_nonneg.mpr (quitProbability_mem_Icc G _).2
          · intro k hk
            rw [hrow]
            have hs := one_sub_quitProbability_replace G pZero n (deviation k)
            rw [hpZeroSelf] at hs
            simp only [Nat.zero_add]
            rw [hs]
            exact mul_le_of_le_one_left (sub_nonneg.mpr hqOther.2)
              (by linarith [(deviation k).property.1])
        _ = (1 - qOther) ^ t := by simp
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [hqOther.2])
        (by linarith)
  have hmass := tsum_tailSurvival_mul_quitProbability_eq_one G deviated 0 hvanish
  exact quitPayoff_le_of_rewardPart_le G deviated n C hrewards (by simpa using hmass)

/--
The quantitative core of Lemma 6: for normal players and `0 < ε ≤ 1`, an
`F_{ε²/(2M)}` step preserves `3ε`-rationality and otherwise raises the coordinate by
at least `ε²/(2M)`.  This estimate does not use either global nonexistence hypothesis.
-/
theorem lemma6_quantitative (G : QuittingGame) {M ε : ℝ}
    (hM : IsQuittingPayoffDifferenceBound G M) (hnormal : ∀ n, IsNormalPlayer G n)
    (hε : 0 < ε) (hε1 : ε ≤ 1) {r s : Payoff G.Player}
    (hstep : s ∈ FRow G (ε ^ 2 / (2 * M)) r) :
    ∀ n,
      (r n ≥ MinMaxQuit G n - 3 * ε → s n ≥ MinMaxQuit G n - 3 * ε) ∧
      (r n < MinMaxQuit G n - 3 * ε → s n ≥ r n + ε ^ 2 / (2 * M)) := by
  rcases hstep with ⟨p, hp, rfl⟩
  intro n
  let δ : ℝ := ε ^ 2 / (2 * M)
  let y : ℝ := QuittingOneStagePayoff G r p n
  let a : ℝ := ForcedQuitPayoff G p n
  let b : ℝ := ForcedContinuePayoff G r p n
  let q : ℝ := p n
  let pZero := p.replace G n 0
  let qOther : ℝ := QuitProbability G pZero
  have hMpositive : 0 < M := lt_of_lt_of_le zero_lt_one hM.1
  have hδpositive : 0 < δ := by
    exact div_pos (sq_pos_of_pos hε) (mul_pos (by norm_num) hMpositive)
  have htwodelta : 2 * δ ≤ ε := by
    have hεsquare : ε ^ 2 ≤ ε * M := by
      have hfirst := mul_nonneg hε.le (sub_nonneg.mpr hε1)
      have hsecond := mul_nonneg hε.le (sub_nonneg.mpr hM.1)
      nlinarith
    calc
      2 * δ = ε ^ 2 / M := by
        dsimp only [δ]
        field_simp [ne_of_gt hMpositive]
      _ ≤ ε := (div_le_iff₀ hMpositive).2 (by simpa [mul_comm] using hεsquare)
  have haffine : y = q * a + (1 - q) * b := by
    simpa only [y, q, a, b] using
      quittingOneStagePayoff_eq_endpointCombination G r p n
  have hqmem : q ∈ Set.Icc (0 : ℝ) 1 := (p n).property
  have hcore : y < MinMaxQuit G n - 3 * ε + δ → y < r n + δ → False := by
    intro hyLow hyMove
    have haEndpoint : a ≤ y + δ := by
      by_cases hqZero : q = 0
      · have hcontinue := hp.2 n (by dsimp only [q] at hqZero ⊢; rw [hqZero]; norm_num)
        rw [hqZero] at haffine
        norm_num at haffine
        linarith
      · by_cases hqOne : q = 1
        · rw [hqOne] at haffine
          norm_num at haffine
          linarith
        · have hcontinue := hp.2 n (lt_of_le_of_ne hqmem.2 hqOne)
          have hweighted := mul_le_mul_of_nonneg_left
            (show a ≤ b + δ by linarith)
            (sub_nonneg.mpr hqmem.2)
          have hqdelta := mul_nonneg hqmem.1 hδpositive.le
          nlinarith
    have hbEndpoint : b ≤ y + δ := by
      by_cases hqZero : q = 0
      · rw [hqZero] at haffine
        norm_num at haffine
        linarith
      · have hquit := hp.1 n (by
          dsimp only [q] at hqZero ⊢
          exact lt_of_le_of_ne (p n).property.1 (Ne.symm hqZero))
        have hweighted := mul_le_mul_of_nonneg_left
          (show b ≤ a + δ by linarith) hqmem.1
        have hremaining := mul_nonneg (sub_nonneg.mpr hqmem.2) hδpositive.le
        nlinarith
    have haLow : a < MinMaxQuit G n - 2 * ε := by
      nlinarith
    have hbLow : b < MinMaxQuit G n - 2 * ε := by
      nlinarith
    have hbMove : b < r n + 2 * δ := by
      linarith
    have hqOtherPositive : 2 * ε / M < qOther := by
      by_contra hnot
      have hqOtherLe : qOther ≤ 2 * ε / M := le_of_not_gt hnot
      have hscaled : M * qOther ≤ 2 * ε := by
        have := (le_div_iff₀ hMpositive).mp hqOtherLe
        nlinarith
      have hforced := forcedQuitPayoff_ge_solo_sub_otherQuitMass G hM p n
      have hnormaln := hnormal n
      have hforced' : SoloPayoff G n - M * qOther ≤ a := by
        simpa only [qOther, pZero, a] using hforced
      have hnormaln' : MinMaxQuit G n ≤ SoloPayoff G n := hnormaln
      nlinarith
    have hqOtherPos : 0 < qOther :=
      lt_trans (div_pos (mul_pos (by norm_num) hε) hMpositive) hqOtherPositive
    let d : ℝ := quittingRewardPart G pZero n / qOther
    have hminmaxCap : MinMaxQuit G n ≤ max a d := by
      simpa only [a, d, pZero, qOther] using
        minMaxQuit_le_max_forcedQuit_stationaryContinue G hM p n (by
          simpa only [pZero, qOther] using hqOtherPos)
    have hminmaxD : MinMaxQuit G n ≤ d := by
      by_cases had : a ≤ d
      · simpa [max_eq_right had] using hminmaxCap
      · have hda : d ≤ a := le_of_not_ge had
        rw [max_eq_left hda] at hminmaxCap
        linarith
    have hpZeroReward : quittingRewardPart G pZero n = qOther * d := by
      dsimp only [d]
      field_simp [ne_of_gt hqOtherPos]
    have hbFormula : b = (1 - qOther) * r n + qOther * d := by
      change (1 - QuitProbability G pZero) * r n + quittingRewardPart G pZero n = _
      rw [hpZeroReward]
    have hqOtherMem : qOther ∈ Set.Icc (0 : ℝ) 1 :=
      quitProbability_mem_Icc G pZero
    have hrd : r n < d := by
      by_contra hnot
      have hdr : d ≤ r n := le_of_not_gt hnot
      have hweighted := mul_le_mul_of_nonneg_left hdr
        (sub_nonneg.mpr hqOtherMem.2)
      nlinarith
    have hrb : r n < b := by
      have hproduct := mul_pos hqOtherPos (sub_pos.mpr hrd)
      nlinarith [hbFormula]
    have hqdUpper : qOther * (d - r n) < ε ^ 2 / M := by
      have hbMove' : b < r n + ε ^ 2 / M := by
        calc
          b < r n + 2 * δ := hbMove
          _ = r n + ε ^ 2 / M := by
            dsimp only [δ]
            field_simp [ne_of_gt hMpositive]
      nlinarith [hbFormula]
    have hqdLower := mul_lt_mul_of_pos_right hqOtherPositive (sub_pos.mpr hrd)
    have hfraction : (2 * ε * (d - r n)) / M < ε ^ 2 / M := by
      calc
        (2 * ε * (d - r n)) / M = (2 * ε / M) * (d - r n) := by ring
        _ < qOther * (d - r n) := hqdLower
        _ < ε ^ 2 / M := hqdUpper
    rw [div_lt_div_iff_of_pos_right hMpositive] at hfraction
    have hdClose : d < r n + ε / 2 := by
      nlinarith
    nlinarith
  constructor
  · intro hr
    by_contra hs
    have hslt : y < MinMaxQuit G n - 3 * ε := lt_of_not_ge hs
    exact hcore (by linarith) (by linarith)
  · intro hr
    by_contra hs
    have hslt : y < r n + δ := by
      dsimp only [δ, y] at hs ⊢
      exact lt_of_not_ge hs
    exact hcore (by linarith) hslt

/--
Lemma 6 as stated in the paper.  Its stationary and instant hypotheses are not needed for
the displayed one-step estimate.
-/
theorem lemma6 (G : QuittingGame) {M ε : ℝ}
    (hM : IsQuittingPayoffDifferenceBound G M) (hnormal : ∀ n, IsNormalPlayer G n)
    (_hstationary : ¬HasStationaryApproximateEquilibria G)
    (_hinstant : ¬HasInstantApproximateEquilibria G)
    (hε : 0 < ε) (hε1 : ε ≤ 1) {r s : Payoff G.Player}
    (hstep : s ∈ FRow G (ε ^ 2 / (2 * M)) r) :
    ∀ n,
      (r n ≥ MinMaxQuit G n - 3 * ε → s n ≥ MinMaxQuit G n - 3 * ε) ∧
      (r n < MinMaxQuit G n - 3 * ε → s n ≥ r n + ε ^ 2 / (2 * M)) :=
  lemma6_quantitative G hM hnormal hε hε1 hstep

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

/-- The checked deduction of Corollary 2 from the five-way equivalence and Lemma 6. -/
theorem corollary2_of_equivalentFive (G : QuittingGame)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hfive : EquivalentFive (HasQuitApproximateEquilibria G) (CyclicOrbitCondition G)
      (FiniteNearOrbitCondition G) (InfiniteOrbitCondition G) (ExtendedOrbitCondition G)) :
    HasQuitApproximateEquilibria G ↔ InfiniteUnrestrictedOrbitCondition G := by
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
      exact lemma6_quantitative G hM hnormal ha ha1 (horbit i) n
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

/-- Corollary 2 as printed in 2007. -/
theorem corollary2 (G : QuittingGame) (hnormal : ∀ n, IsNormalPlayer G n)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hstationary : ¬HasStationaryApproximateEquilibria G) :
    HasQuitApproximateEquilibria G ↔ InfiniteUnrestrictedOrbitCondition G := by
  exact corollary2_of_equivalentFive G hnormal (theorem3 G hstationary hinstant)

/-- Simon (2012), Theorem 2.2, with the corrected stationarily-generated hypothesis. -/
theorem corollary2_corrected_2012 (G : QuittingGame)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hstationary : ¬HasStationarilyGeneratedApproximateEquilibria G) :
    HasQuitApproximateEquilibria G ↔ InfiniteUnrestrictedOrbitCondition G := by
  exact corollary2_of_equivalentFive G hnormal
    (theorem3_corrected_2012 G hstationary hinstant)

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
theorem KohlbergMertensStatement :
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
      ∀ x, R < MatrixNorm D x → ∀ t, (H x t).1 ∉ C := by
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

/-- A pure solo-quit row pays the corresponding singleton reward. -/
theorem quittingOneStagePayoff_soloQuitRow (G : QuittingGame)
    (r : Payoff G.Player) (j : G.Player) :
    QuittingOneStagePayoff G r (SoloQuitRow G j) =
      G.reward ⟨{j}, Finset.singleton_nonempty j⟩ := by
  classical
  funext n
  simp only [QuittingOneStagePayoff]
  have hq : QuitProbability G (SoloQuitRow G j) = 1 := by
    simp only [QuitProbability, SoloQuitRow]
    have hprod :
        (∏ k, (1 - ((((if k = j then (1 : Set.Icc (0 : ℝ) 1) else 0) :
          Set.Icc (0 : ℝ) 1)) : ℝ))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      norm_num
    rw [hprod]
    ring
  rw [hq]
  norm_num
  rw [Finset.sum_eq_single_of_mem {j} (by simp)]
  · simp [coalitionProbability_soloQuitRow_singleton]
  · intro A hA hne
    split_ifs with hnonempty
    · rw [coalitionProbability_soloQuitRow_other G j A hne]
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

/-- Every payoff coordinate is affine in any one player's quitting probability. -/
theorem quittingOneStagePayoff_replace_affine_coord (G : QuittingGame)
    (r : Payoff G.Player) (p : QuitRow G) (n : G.Player)
    (q : Set.Icc (0 : ℝ) 1) (k : G.Player) :
    QuittingOneStagePayoff G r (p.replace G n q) k =
      (q : ℝ) * QuittingOneStagePayoff G r (p.replace G n 1) k +
        (1 - (q : ℝ)) * QuittingOneStagePayoff G r (p.replace G n 0) k := by
  classical
  let rewardPart (a : Set.Icc (0 : ℝ) 1) : ℝ :=
    ∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
      CoalitionProbability G (p.replace G n a) A * G.reward ⟨A, hA⟩ k else 0
  have hcontinue (a : Set.Icc (0 : ℝ) 1) :
      1 - QuitProbability G (p.replace G n a) =
        CoalitionProbability G (p.replace G n a) ∅ := by
    simp [QuitProbability, CoalitionProbability]
  have hreward : rewardPart q = (q : ℝ) * rewardPart 1 +
      (1 - (q : ℝ)) * rewardPart 0 := by
    simp only [rewardPart]
    calc
      _ = ∑ A ∈ Finset.univ.powerset,
          ((q : ℝ) * (if hA : A.Nonempty then
              CoalitionProbability G (p.replace G n 1) A * G.reward ⟨A, hA⟩ k
            else 0) +
          (1 - (q : ℝ)) * (if hA : A.Nonempty then
              CoalitionProbability G (p.replace G n 0) A * G.reward ⟨A, hA⟩ k
            else 0)) := by
        apply Finset.sum_congr rfl
        intro A hA
        split_ifs with hnonempty
        · rw [coalitionProbability_replace_affine G p n q A]
          ring
        · ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  change (1 - QuitProbability G (p.replace G n q)) * r k + rewardPart q = _
  simp only [QuittingOneStagePayoff]
  change _ = (q : ℝ) *
      ((1 - QuitProbability G (p.replace G n 1)) * r k + rewardPart 1) +
      (1 - (q : ℝ)) *
        ((1 - QuitProbability G (p.replace G n 0)) * r k + rewardPart 0)
  rw [hcontinue q, hcontinue 1, hcontinue 0]
  rw [coalitionProbability_replace_affine G p n q ∅, hreward]
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

/-- The added small solo-quitting moves satisfy the paper's `ε` endpoint conditions. -/
theorem restrictedEscapeCorrespondence_subset (G : QuittingGame) {M ε : ℝ}
    (hM : IsQuittingPayoffDifferenceBound G M) (hε : 0 < ε) :
    let δ := ε / (10 * M * Fintype.card G.Player)
    ∀ x, RestrictedEscapeCorrespondence G δ ε x ⊆ FRow G ε x := by
  classical
  let δ := ε / (10 * M * Fintype.card G.Player)
  have hM0 : 0 ≤ M := hM.1.trans' zero_le_one
  have hMpositive : 0 < M := lt_of_lt_of_le zero_lt_one hM.1
  have hcard : (1 : ℝ) ≤ Fintype.card G.Player := by
    exact_mod_cast Fintype.card_pos
  have hdenominator : 0 < 10 * M * (Fintype.card G.Player : ℝ) := by positivity
  have hδ0 : 0 < δ := div_pos hε hdenominator
  have hδsmall : 2 * M * δ ≤ ε := by
    dsimp [δ]
    rw [div_eq_mul_inv]
    field_simp
    nlinarith
  dsimp only
  intro x y hy
  rcases hy with hy | ⟨j, p, hxband, hxj, hp, rfl⟩
  · exact FRow.mono G (show (0 : ℝ) ≤ ε from le_of_lt hε) x hy
  · refine ⟨p, ?_, rfl⟩
    let zeroRow : QuitRow G := fun _ => (0 : Set.Icc (0 : ℝ) 1)
    have hpZero : p.replace G j 0 = zeroRow := by
      funext k
      by_cases hkj : k = j
      · subst k
        simp [QuitRow.replace, zeroRow]
      · apply Subtype.ext
        simp only [QuitRow.replace, hkj, if_false, zeroRow]
        exact hp.2 k hkj
    have hpOne : p.replace G j 1 = SoloQuitRow G j := by
      funext k
      by_cases hkj : k = j
      · subst k
        simp [QuitRow.replace, SoloQuitRow]
      · apply Subtype.ext
        simp only [QuitRow.replace, hkj, if_false, SoloQuitRow]
        exact hp.2 k hkj
    have hpFromZero : p = zeroRow.replace G j (p j) := by
      funext k
      by_cases hkj : k = j
      · subst k
        simp [QuitRow.replace]
      · apply Subtype.ext
        simp only [QuitRow.replace, hkj, if_false, zeroRow]
        exact hp.2 k hkj
    constructor
    · intro k hkpositive
      by_cases hkj : k = j
      · subst k
        have hquit : ForcedQuitPayoff G p j = SoloPayoff G j := by
          rw [ForcedQuitPayoff, hpOne, quittingOneStagePayoff_soloQuitRow]
          rfl
        have hcontinue : ForcedContinuePayoff G x p j = x j := by
          rw [ForcedContinuePayoff, hpZero, quittingOneStagePayoff_zero]
        rw [hquit, hcontinue]
        linarith
      · have hpk : (p k : ℝ) = 0 := hp.2 k hkj
        linarith
    · intro k hkcontinue
      by_cases hkj : k = j
      · subst k
        have hquit : ForcedQuitPayoff G p j = SoloPayoff G j := by
          rw [ForcedQuitPayoff, hpOne, quittingOneStagePayoff_soloQuitRow]
          rfl
        have hcontinue : ForcedContinuePayoff G x p j = x j := by
          rw [ForcedContinuePayoff, hpZero, quittingOneStagePayoff_zero]
        rw [hquit, hcontinue]
        exact le_trans (by linarith : SoloPayoff G j - ε ≤ SoloPayoff G j)
          (hxband.1 j)
      · have hpk : p k = (0 : Set.Icc (0 : ℝ) 1) := by
          apply Subtype.ext
          exact hp.2 k hkj
        have hpContinue : p.replace G k 0 = p := by
          rw [← hpk]
          exact p.replace_self G k
        let baseQuit : QuitRow G := zeroRow.replace G k 1
        have hpQuit : p.replace G k 1 = baseQuit.replace G j (p j) := by
          calc
            _ = (zeroRow.replace G j (p j)).replace G k 1 :=
              congrArg (fun row => row.replace G k 1) hpFromZero
            _ = _ := zeroRow.replace_comm G (Ne.symm hkj) (p j) 1
        have hbaseQuit : baseQuit = SoloQuitRow G k := by
          exact QuitRow.zero_replace_one G k
        have hzeroJ : zeroRow.replace G j 0 = zeroRow := by
          exact zeroRow.replace_self G j
        have hcontinueAffine : ForcedContinuePayoff G x p k =
            (p j : ℝ) * G.reward ⟨{j}, Finset.singleton_nonempty j⟩ k +
              (1 - (p j : ℝ)) * x k := by
          rw [ForcedContinuePayoff, hpContinue, hpFromZero]
          rw [quittingOneStagePayoff_replace_affine_coord]
          rw [QuitRow.zero_replace_one, hzeroJ]
          rw [quittingOneStagePayoff_soloQuitRow, quittingOneStagePayoff_zero]
          simp [QuitRow.replace]
        let bothQuit : QuitRow G := baseQuit.replace G j 1
        have hbaseZero : baseQuit.replace G j 0 = baseQuit := by
          have hbasej : baseQuit j = (0 : Set.Icc (0 : ℝ) 1) := by
            simp [baseQuit, zeroRow, QuitRow.replace, Ne.symm hkj]
          rw [← hbasej]
          exact baseQuit.replace_self G j
        have hquitAffine : ForcedQuitPayoff G p k =
            (p j : ℝ) * QuittingOneStagePayoff G 0 bothQuit k +
              (1 - (p j : ℝ)) * SoloPayoff G k := by
          rw [ForcedQuitPayoff, hpQuit]
          rw [quittingOneStagePayoff_replace_affine_coord]
          rw [hbaseZero, hbaseQuit, quittingOneStagePayoff_soloQuitRow]
          rfl
        have hsoloBound :
            -M ≤ G.reward ⟨{j}, Finset.singleton_nonempty j⟩ k :=
          neg_le_of_abs_le (le_of_lt (hM.2.2 _ k))
        have hbothReward := quittingRewardPart_mem_Icc G bothQuit k hM0
          (fun A => le_of_lt (hM.2.2 A k))
        have hbothQuitProbability : QuitProbability G bothQuit = 1 := by
          exact quitProbability_replace_one G baseQuit j
        have hbothBound : QuittingOneStagePayoff G 0 bothQuit k ≤ M := by
          simpa [QuittingOneStagePayoff, hbothQuitProbability] using hbothReward.2
        have hxsolo : SoloPayoff G k ≤ x k := hxband.1 k
        have hpj0 : 0 ≤ (p j : ℝ) := (p j).property.1
        have hpjδ : (p j : ℝ) ≤ δ := hp.1
        rw [hcontinueAffine, hquitAffine]
        have hweighted :
            (p j : ℝ) * QuittingOneStagePayoff G 0 bothQuit k +
                (1 - (p j : ℝ)) * SoloPayoff G k - ε ≤
              (p j : ℝ) * G.reward ⟨{j}, Finset.singleton_nonempty j⟩ k +
                (1 - (p j : ℝ)) * x k := by
          nlinarith [mul_nonneg (sub_nonneg.mpr (p j).property.2)
            (sub_nonneg.mpr hxsolo)]
        exact hweighted

/--
The checked content of Lemma 9, conditional on the uniform parameter claimed by the
corrected Lemma 5.
-/
theorem lemma9_of_uniformRho (G : QuittingGame) (_hEscape : IsEscapeGame G)
    {ρ : ℝ} (hρ : IsUniformRho G ρ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, (∀ j, x j ≥ B) →
      EpsilonRow G 0 x = {fun _ => (0 : Set.Icc (0 : ℝ) 1)} := by
  classical
  obtain ⟨M, hM⟩ := exists_quittingPayoffDifferenceBound G
  have hM0 : 0 ≤ M := hM.1.trans' zero_le_one
  obtain ⟨hρ0, hρ1, hρuniform⟩ := hρ
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

/-- A closed forward-invariant set contains every point of an extended orbit started in it. -/
theorem extendedOrbitStaysIn_of_closed_forwardInvariant
    {X : Type} [TopologicalSpace X] {F : Correspondence X X}
    (x : ExtendedOrbitData F) (A : Set X) (hclosed : IsClosed A)
    (hforward : ∀ a ∈ A, F a ⊆ A) (hstart : x.point 0 0 ∈ A) :
    ExtendedOrbitStaysIn x A := by
  have segment_mem : ∀ j, ActiveSegment x.segmentCount j → x.point j 0 ∈ A →
      ∀ i, SegmentIndex (x.segmentLength j) i → x.point j i ∈ A := by
    intro j hj hzero i
    induction i with
    | zero => exact fun _ => hzero
    | succ i hi =>
        intro hindex
        have hprevious : SegmentIndex (x.segmentLength j) i := by
          intro k hk
          have := hindex k hk
          omega
        exact hforward (x.point j i) (hi hprevious)
          (x.step j hj i hindex)
  have segment_start : ∀ j, ActiveSegment x.segmentCount j → x.point j 0 ∈ A := by
    intro j
    induction j with
    | zero => exact fun _ => hstart
    | succ j ih =>
        intro hjnext
        have hj : ActiveSegment x.segmentCount j := by
          intro L hL
          have := hjnext L hL
          omega
        have hall := segment_mem j hj (ih hj)
        cases hlength : x.segmentLength j with
        | none =>
            apply hclosed.mem_of_tendsto (x.infiniteStitch j hjnext hlength)
            exact Filter.Eventually.of_forall fun i => hall i (by
              intro k hk
              simp [hlength] at hk)
        | some k =>
            have hkpositive := x.segmentLengthPositive j hj k hlength
            rw [← x.finiteStitch j hjnext k hlength]
            apply hall (k - 1)
            intro l hl
            have hkl : k = l := Option.some.inj (hlength.symm.trans hl)
            subst l
            omega
  intro j hj i hi
  exact segment_mem j hj (segment_start j hj) i hi

/--
An invariant set also contains an extended orbit when every nontrivial step enters a closed
invariant core contained in that set.
-/
theorem extendedOrbitStaysIn_of_closedCore
    {X : Type} [TopologicalSpace X] [T2Space X] {F : Correspondence X X}
    (x : ExtendedOrbitData F) (A C : Set X) (hclosedC : IsClosed C)
    (hCA : C ⊆ A) (hforwardA : ∀ a ∈ A, F a ⊆ A)
    (hforwardC : ∀ c ∈ C, F c ⊆ C)
    (hcore : ∀ a ∈ A, ∀ b ∈ F a, b = a ∨ b ∈ C)
    (hstart : x.point 0 0 ∈ A) : ExtendedOrbitStaysIn x A := by
  have segment_mem : ∀ j, ActiveSegment x.segmentCount j → x.point j 0 ∈ A →
      ∀ i, SegmentIndex (x.segmentLength j) i → x.point j i ∈ A := by
    intro j hj hzero i
    induction i with
    | zero => exact fun _ => hzero
    | succ i hi =>
        intro hindex
        have hprevious : SegmentIndex (x.segmentLength j) i := by
          intro k hk
          have := hindex k hk
          omega
        exact hforwardA (x.point j i) (hi hprevious) (x.step j hj i hindex)
  have segment_start : ∀ j, ActiveSegment x.segmentCount j → x.point j 0 ∈ A := by
    intro j
    induction j with
    | zero => exact fun _ => hstart
    | succ j ih =>
        intro hjnext
        have hj : ActiveSegment x.segmentCount j := by
          intro L hL
          have := hjnext L hL
          omega
        have hjstart := ih hj
        have hall := segment_mem j hj hjstart
        cases hlength : x.segmentLength j with
        | some k =>
            have hkpositive := x.segmentLengthPositive j hj k hlength
            rw [← x.finiteStitch j hjnext k hlength]
            apply hall (k - 1)
            intro l hl
            have hkl : k = l := Option.some.inj (hlength.symm.trans hl)
            subst l
            omega
        | none =>
            by_cases hhit : ∃ i, x.point j i ∈ C
            · rcases hhit with ⟨i, hiC⟩
              have heventual : ∀ l, i ≤ l → x.point j l ∈ C := by
                intro l hil
                induction l, hil using Nat.le_induction with
                | base => exact hiC
                | succ l hil hlC =>
                    apply hforwardC (x.point j l) hlC
                    apply x.step j hj l
                    intro q hq
                    simp [hlength] at hq
              apply hCA
              apply hclosedC.mem_of_tendsto (x.infiniteStitch j hjnext hlength)
              exact Filter.eventually_atTop.mpr ⟨i, heventual⟩
            · push Not at hhit
              have hconstant : ∀ i, x.point j i = x.point j 0 := by
                intro i
                induction i with
                | zero => rfl
                | succ i hi =>
                    have hindex : SegmentIndex (x.segmentLength j) (i + 1) := by
                      intro q hq
                      simp [hlength] at hq
                    rcases hcore (x.point j i) (hall i (by
                        intro q hq
                        simp [hlength] at hq)) (x.point j (i + 1))
                      (x.step j hj i hindex) with heq | hC
                    · exact heq.trans hi
                    · exact (hhit (i + 1) hC).elim
              have hsingleton : x.point (j + 1) 0 ∈ ({x.point j 0} : Set X) := by
                apply isClosed_singleton.mem_of_tendsto
                  (x.infiniteStitch j hjnext hlength)
                exact Filter.Eventually.of_forall fun i => by simp [hconstant i]
              rw [Set.mem_singleton_iff] at hsingleton
              rw [hsingleton]
              exact hjstart
  intro j hj i hi
  exact segment_mem j hj (segment_start j hj) i hi

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
  classical
  let δ := ε / (10 * M * Fintype.card G.Player)
  have hM0 : 0 ≤ M := hM.1.trans' zero_le_one
  have hMpositive : 0 < M := lt_of_lt_of_le zero_lt_one hM.1
  have hε1 : ε < 1 := lt_of_lt_of_le hερ hρ.2.1
  have hcard : (1 : ℝ) ≤ Fintype.card G.Player := by
    exact_mod_cast Fintype.card_pos
  have hdenominator : 0 < 10 * M * (Fintype.card G.Player : ℝ) := by positivity
  have hδ0 : 0 < δ := div_pos hε hdenominator
  have hδsmall : 2 * M * δ ≤ ε := by
    dsimp [δ]
    rw [div_eq_mul_inv]
    field_simp
    nlinarith
  have hsubset : ∀ x, RestrictedEscapeCorrespondence G δ ε x ⊆ FRow G ε x := by
    exact restrictedEscapeCorrespondence_subset G hM hε
  have hrationalClosed : IsClosed {r | IsRational G ε r} := by
    have heq : {r | IsRational G ε r} =
        ⋂ n, {r | MinMaxQuit G n - ε ≤ r n} := by
      ext r
      simp [IsRational]
    rw [heq]
    exact isClosed_iInter fun n => isClosed_le continuous_const (continuous_apply n)
  have hrationalForward : ∀ r ∈ {r | IsRational G ε r},
      RestrictedEscapeCorrespondence G δ ε r ⊆ {r | IsRational G ε r} := by
    intro r hr s hs
    rcases hs with hs | ⟨j, p, hrband, hrj, hp, rfl⟩
    · let a : ℝ := ε / 3
      have ha0 : 0 < a := div_pos hε (by norm_num)
      have ha1 : a ≤ 1 := by dsimp [a]; linarith
      have herror0 : 0 ≤ a ^ 2 / (2 * M) := by positivity
      have hstep : s ∈ FRow G (a ^ 2 / (2 * M)) r :=
        FRow.mono G herror0 r hs
      intro n
      have hrA : r n ≥ MinMaxQuit G n - 3 * a := by
        dsimp [a]
        convert hr n using 1
        all_goals ring
      have hpreserve := (lemma6 G hM hnormal hstationary hinstant ha0 ha1 hstep n).1
        hrA
      dsimp [a] at hpreserve
      convert hpreserve using 1
      all_goals ring
    · let zeroRow : QuitRow G := fun _ => (0 : Set.Icc (0 : ℝ) 1)
      have hpFromZero : p = zeroRow.replace G j (p j) := by
        funext k
        by_cases hkj : k = j
        · subst k
          simp [QuitRow.replace]
        · apply Subtype.ext
          simp only [QuitRow.replace, hkj, if_false, zeroRow]
          exact (hp.2 k hkj)
      have hzeroJ : zeroRow.replace G j 0 = zeroRow := zeroRow.replace_self G j
      intro n
      have hformula : QuittingOneStagePayoff G r p n =
          (p j : ℝ) * G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n +
            (1 - (p j : ℝ)) * r n := by
        rw [hpFromZero]
        rw [quittingOneStagePayoff_replace_affine_coord]
        rw [QuitRow.zero_replace_one, hzeroJ]
        rw [quittingOneStagePayoff_soloQuitRow, quittingOneStagePayoff_zero]
        simp [QuitRow.replace]
      rw [hformula]
      have hrewards : -M ≤ G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n :=
        neg_le_of_abs_le (le_of_lt (hM.2.2 _ n))
      have hrminmax : MinMaxQuit G n ≤ r n := (hnormal n).trans (hrband.1 n)
      have hminmaxM : MinMaxQuit G n ≤ M := by
        exact (hnormal n).trans (le_trans (le_abs_self _)
          (le_of_lt (hM.2.2 ⟨{n}, Finset.singleton_nonempty n⟩ n)))
      have hweightedReward := mul_le_mul_of_nonneg_left hrewards (p j).property.1
      have hweightedContinuation := mul_le_mul_of_nonneg_left hrminmax
        (sub_nonneg.mpr (p j).property.2)
      have hpδ : (p j : ℝ) ≤ δ := hp.1
      have hscaled : 2 * M * (p j : ℝ) ≤ ε := by
        exact (mul_le_mul_of_nonneg_left hpδ (by positivity : 0 ≤ 2 * M)).trans hδsmall
      nlinarith [mul_nonneg (p j).property.1 (sub_nonneg.mpr hminmaxM)]
  have hQForward : ∀ r ∈ E.Q,
      RestrictedEscapeCorrespondence G δ ε r ⊆ E.Q := by
    intro r hr s hs
    apply E.closedUnder r hr s
    apply FRow.mono G (le_of_lt hεe) r
    exact hsubset r hs
  let core : Set (Payoff G.Player) :=
    E.Q ∩ {r | ∀ n, SoloPayoff G n + E.ebar ≤ r n}
  have hcoreClosed : IsClosed core := by
    apply E.Q_closed.inter
    have heq :
        ({r : Payoff G.Player | ∀ n, SoloPayoff G n + E.ebar ≤ r n} :
          Set (Payoff G.Player)) =
          ⋂ n, {r : Payoff G.Player | SoloPayoff G n + E.ebar ≤ r n} := by
      ext r
      simp
    rw [heq]
    exact isClosed_iInter fun n => isClosed_le continuous_const (continuous_apply n)
  have hcoreSubset : core ⊆ E.Q \ (WSet G ∪ EscapeBand G ε) := by
    rintro r ⟨hrQ, hrstrong⟩
    refine ⟨hrQ, ?_⟩
    intro hrUnion
    rcases hrUnion with hrW | hrT
    · rcases hrW with ⟨n, hn⟩
      linarith [hrstrong n, hεe]
    · rcases hrT.2 with ⟨n, hn⟩
      linarith [hrstrong n, hεe]
  have houtsideCore : ∀ r ∈ E.Q \ (WSet G ∪ EscapeBand G ε),
      ∀ s ∈ RestrictedEscapeCorrespondence G δ ε r, s = r ∨ s ∈ core := by
    rintro r ⟨hrQ, hrOutside⟩ s hs
    have hrNotBand : r ∉ EscapeBand G ε := fun hrBand => hrOutside (Or.inr hrBand)
    have hsF0 : s ∈ FRow G 0 r := by
      rcases hs with hs | ⟨j, p, hrBand, _hrj, _hp, _hs⟩
      · exact hs
      · exact (hrNotBand hrBand).elim
    by_cases hsr : s = r
    · exact Or.inl hsr
    · right
      refine ⟨hQForward r hrQ (Or.inl hsF0), ?_⟩
      intro n
      exact le_of_lt (E.strictEscape r ⟨hrQ, fun hrW => hrOutside (Or.inl hrW)⟩
        s hsF0 hsr n)
  have houtsideForward : ∀ r ∈ E.Q \ (WSet G ∪ EscapeBand G ε),
      RestrictedEscapeCorrespondence G δ ε r ⊆
        E.Q \ (WSet G ∪ EscapeBand G ε) := by
    intro r hr s hs
    rcases houtsideCore r hr s hs with rfl | hscore
    · exact hr
    · exact hcoreSubset hscore
  have hcoreForward : ∀ r ∈ core,
      RestrictedEscapeCorrespondence G δ ε r ⊆ core := by
    intro r hr s hs
    rcases houtsideCore r (hcoreSubset hr) s hs with rfl | hscore
    · exact hr
    · exact hscore
  dsimp only
  refine ⟨hsubset, ?_, ?_, ?_⟩
  · intro x hx
    exact extendedOrbitStaysIn_of_closed_forwardInvariant x _ hrationalClosed
      hrationalForward hx
  · intro x hx
    exact extendedOrbitStaysIn_of_closed_forwardInvariant x E.Q E.Q_closed hQForward hx
  · intro x hx
    exact extendedOrbitStaysIn_of_closedCore x
      (E.Q \ (WSet G ∪ EscapeBand G ε)) core hcoreClosed hcoreSubset
      houtsideForward hcoreForward houtsideCore hx

/-- A bounded sequence of affine moves reaches the first face hit by a line segment. -/
private theorem exists_affineBoundaryPath {N : Type} [Fintype N] [Nonempty N]
    (v u x : N → ℝ) {δ : ℝ} (hδ0 : 0 < δ)
    (hx : ∀ n, v n ≤ x n) (hfallStrict : ∀ n, u n < v n → v n < x n)
    (hfall : ∃ n, u n < v n) :
    ∃ (k : ℕ) (z : Fin (k + 1) → N → ℝ)
      (q : Fin k → Set.Icc (0 : ℝ) δ),
      z 0 = x ∧
      (∀ i, z i.succ = fun n => (q i : ℝ) * u n + (1 - (q i : ℝ)) * z i.castSucc n) ∧
      (∀ i n, v n ≤ z i n) ∧
      (∀ i n, z i n ≤ max (x n) (u n)) ∧
      ∃ n, z ⟨k, Nat.lt_succ_self k⟩ n = v n ∧ u n < v n := by
  classical
  let falling : Finset N := Finset.univ.filter fun n => u n < v n
  have hfalling : falling.Nonempty := by
    rcases hfall with ⟨n, hn⟩
    exact ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_univ n, hn⟩⟩
  let ratio (n : N) : ℝ := (x n - v n) / (x n - u n)
  have hratioPositive : ∀ n ∈ falling, 0 < ratio n := by
    intro n hn
    have hunv : u n < v n := (Finset.mem_filter.mp hn).2
    exact div_pos (sub_pos.mpr (hfallStrict n hunv))
      (sub_pos.mpr (hunv.trans (hfallStrict n hunv)))
  let ratios : Finset ℝ := falling.image ratio
  have hratios : ratios.Nonempty := hfalling.image ratio
  let lam : ℝ := ratios.min' hratios
  have hlammem : lam ∈ ratios := ratios.min'_mem hratios
  rcases Finset.mem_image.mp hlammem with ⟨n, hnfalling, hnlam⟩
  have hnfall : u n < v n := (Finset.mem_filter.mp hnfalling).2
  have hlam0 : 0 < lam := by
    apply lt_of_lt_of_le (hratioPositive n hnfalling)
    rw [hnlam]
  have hlam1 : lam < 1 := by
    rw [← hnlam]
    apply (div_lt_one (sub_pos.mpr (hnfall.trans (hfallStrict n hnfall)))).2
    linarith
  have hlamratio : ∀ m ∈ falling, lam ≤ ratio m := by
    intro m hm
    exact ratios.min'_le (ratio m) (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  have hinside : ∀ t ∈ Set.Icc (0 : ℝ) lam, ∀ m,
      v m ≤ t * u m + (1 - t) * x m := by
    intro t ht m
    by_cases hmfall : u m < v m
    · have hm : m ∈ falling := Finset.mem_filter.mpr ⟨Finset.mem_univ m, hmfall⟩
      have hden : 0 < x m - u m := sub_pos.mpr (hmfall.trans (hfallStrict m hmfall))
      have htle : t ≤ ratio m := ht.2.trans (hlamratio m hm)
      have hmul : t * (x m - u m) ≤ x m - v m := by
        exact (le_div_iff₀ hden).mp htle
      nlinarith
    · have huv : v m ≤ u m := le_of_not_gt hmfall
      have ht1 : t ≤ 1 := ht.2.trans (le_of_lt hlam1)
      nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr huv),
        mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (hx m))]
  have hendpoint : lam * u n + (1 - lam) * x n = v n := by
    have hden : x n - u n ≠ 0 :=
      ne_of_gt (sub_pos.mpr (hnfall.trans (hfallStrict n hnfall)))
    rw [← hnlam]
    dsimp [ratio]
    field_simp
    ring
  have hscalePositive : 0 < δ * (1 - lam) := mul_pos hδ0 (sub_pos.mpr hlam1)
  obtain ⟨k, hk⟩ := exists_nat_gt (lam / (δ * (1 - lam)))
  have hk0 : 0 < k := by
    have : 0 < (k : ℝ) := (div_pos hlam0 hscalePositive).trans hk
    exact_mod_cast this
  have hlarge : lam < (k : ℝ) * δ * (1 - lam) := by
    have := (div_lt_iff₀ hscalePositive).mp hk
    nlinarith
  let coefficient (i : Fin (k + 1)) : ℝ := (i : ℝ) * lam / k
  let z : Fin (k + 1) → N → ℝ :=
    fun i m => coefficient i * u m + (1 - coefficient i) * x m
  have hdenominator : ∀ i : Fin k, 0 < (k : ℝ) - (i : ℝ) * lam := by
    intro i
    have hi : (i : ℝ) < k := by exact_mod_cast i.isLt
    have himul : (i : ℝ) * lam ≤ i := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ i by positivity)
        (sub_nonneg.mpr (le_of_lt hlam1))]
    linarith
  let q : Fin k → Set.Icc (0 : ℝ) δ := fun i =>
    ⟨lam / ((k : ℝ) - (i : ℝ) * lam), by
      constructor
      · exact le_of_lt (div_pos hlam0 (hdenominator i))
      · apply (div_le_iff₀ (hdenominator i)).2
        have hi : (i : ℝ) ≤ k := by exact_mod_cast i.isLt.le
        have hbase : (k : ℝ) * (1 - lam) ≤ (k : ℝ) - (i : ℝ) * lam := by
          nlinarith [mul_nonneg (le_of_lt hlam0) (sub_nonneg.mpr hi)]
        have hscaled := mul_le_mul_of_nonneg_left hbase (le_of_lt hδ0)
        nlinarith⟩
  refine ⟨k, z, q, ?_, ?_, ?_, ?_, ?_⟩
  · funext m
    simp [z, coefficient]
  · intro i
    funext m
    dsimp [z, q, coefficient]
    have hkne : (k : ℝ) ≠ 0 := by positivity
    have hdene : (k : ℝ) - (i : ℝ) * lam ≠ 0 := ne_of_gt (hdenominator i)
    have hcoefficient : ((i : ℝ) + 1) * lam / k =
        lam / ((k : ℝ) - (i : ℝ) * lam) +
          (1 - lam / ((k : ℝ) - (i : ℝ) * lam)) *
            ((i : ℝ) * lam / k) := by
      field_simp [hdene, hkne]
      ring
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hcoefficient]
    ring
  · intro i m
    apply hinside (coefficient i)
    constructor
    · exact div_nonneg (mul_nonneg (by positivity) (le_of_lt hlam0)) (by positivity)
    · apply (div_le_iff₀ (show (0 : ℝ) < k by positivity)).2
      have hiNat : (i : ℕ) ≤ k := by omega
      have hi : (i : ℝ) ≤ k := by exact_mod_cast hiNat
      nlinarith [mul_nonneg (le_of_lt hlam0) (sub_nonneg.mpr hi)]
  · intro i m
    have hcoefficient := show coefficient i ∈ Set.Icc (0 : ℝ) lam by
      constructor
      · exact div_nonneg (mul_nonneg (by positivity) (le_of_lt hlam0)) (by positivity)
      · apply (div_le_iff₀ (show (0 : ℝ) < k by positivity)).2
        have hiNat : (i : ℕ) ≤ k := by omega
        have hi : (i : ℝ) ≤ k := by exact_mod_cast hiNat
        nlinarith [mul_nonneg (le_of_lt hlam0) (sub_nonneg.mpr hi)]
    have hcoefficient1 : coefficient i ≤ 1 :=
      hcoefficient.2.trans (le_of_lt hlam1)
    dsimp [z]
    by_cases hxu : x m ≤ u m
    · rw [max_eq_right hxu]
      nlinarith [mul_nonneg (sub_nonneg.mpr hcoefficient1) (sub_nonneg.mpr hxu)]
    · have hux : u m ≤ x m := le_of_not_ge hxu
      rw [max_eq_left hux]
      nlinarith [mul_nonneg hcoefficient.1 (sub_nonneg.mpr hux)]
  · refine ⟨n, ?_⟩
    refine ⟨?_, hnfall⟩
    simpa [z, coefficient, hk0.ne'] using hendpoint

/-- The quitting row in which only `j` quits, with the prescribed probability. -/
private def soloProbabilityRow (G : QuittingGame) (j : G.Player)
    (t : Set.Icc (0 : ℝ) 1) : QuitRow G :=
  QuitRow.replace G (fun _ : G.Player => (0 : Set.Icc (0 : ℝ) 1)) j t

/-- A solo-probability move is the affine segment toward the singleton reward. -/
private theorem quittingOneStagePayoff_soloProbabilityRow (G : QuittingGame)
    (x : Payoff G.Player) (j : G.Player) (t : Set.Icc (0 : ℝ) 1) :
    QuittingOneStagePayoff G x (soloProbabilityRow G j t) =
      fun n => (t : ℝ) * G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n +
        (1 - (t : ℝ)) * x n := by
  funext n
  rw [soloProbabilityRow, quittingOneStagePayoff_replace_affine_coord]
  rw [QuitRow.zero_replace_one, QuitRow.replace_self]
  rw [quittingOneStagePayoff_soloQuitRow, quittingOneStagePayoff_zero]

/-- Repeated sufficiently small solo moves reach the first face of `W` without entering `W`. -/
private theorem exists_soloBoundaryOrbit (G : QuittingGame) {delta epsilon : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) (j : G.Player)
    (x : Payoff G.Player) (hx : ∀ n, SoloPayoff G n ≤ x n)
    (hxj : x j ≤ SoloPayoff G j + epsilon)
    (hfallStrict : ∀ n, G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n < SoloPayoff G n →
      SoloPayoff G n < x n)
    (hfall : ∃ n, G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n < SoloPayoff G n) :
    ∃ (k : ℕ) (z : Fin (k + 1) → Payoff G.Player),
      z 0 = x ∧ IsFiniteOrbit (RestrictedEscapeCorrespondence G delta epsilon) z ∧
      (∀ i, z i ∈ EscapeBand G epsilon) ∧
      (∀ i, z i j ≤ x j) ∧
      ∃ n, z ⟨k, Nat.lt_succ_self k⟩ n = SoloPayoff G n ∧
        G.reward ⟨{j}, Finset.singleton_nonempty j⟩ n < SoloPayoff G n := by
  classical
  obtain ⟨k, z, q, hz0, hstep, hlower, hupper, hend⟩ :=
    exists_affineBoundaryPath (SoloPayoff G)
      (G.reward ⟨{j}, Finset.singleton_nonempty j⟩) x hdelta0 hx hfallStrict hfall
  have hband : ∀ i, z i ∈ EscapeBand G epsilon := by
    intro i
    refine ⟨hlower i, ⟨j, ?_⟩⟩
    calc
      z i j ≤ max (x j) (G.reward ⟨{j}, Finset.singleton_nonempty j⟩ j) := hupper i j
      _ = x j := max_eq_left (hx j)
      _ ≤ SoloPayoff G j + epsilon := hxj
  refine ⟨k, z, hz0, ?_, hband, ?_, hend⟩
  intro i
  let t : Set.Icc (0 : ℝ) 1 :=
    ⟨q i, (q i).property.1, (q i).property.2.trans (le_of_lt hdelta1)⟩
  let p : QuitRow G := soloProbabilityRow G j t
  right
  refine ⟨j, p, hband i.castSucc, ?_, ?_, ?_⟩
  · calc
      z i.castSucc j ≤
          max (x j) (G.reward ⟨{j}, Finset.singleton_nonempty j⟩ j) :=
        hupper i.castSucc j
      _ = x j := max_eq_left (hx j)
      _ ≤ SoloPayoff G j + epsilon := hxj
  · constructor
    · change ((soloProbabilityRow G j t) j : ℝ) ≤ delta
      simp only [soloProbabilityRow, QuitRow.replace, if_pos]
      exact (q i).property.2
    · intro n hnj
      change ((soloProbabilityRow G j t) n : ℝ) = 0
      simp [soloProbabilityRow, QuitRow.replace, hnj]
  · rw [hstep i]
    exact (quittingOneStagePayoff_soloProbabilityRow G (z i.castSucc) j t).symm
  · intro i
    calc
      z i j ≤ max (x j) (G.reward ⟨{j}, Finset.singleton_nonempty j⟩ j) := hupper i j
      _ = x j := max_eq_left (hx j)

/-- Two finite correspondence orbits with a common endpoint concatenate. -/
private theorem exists_appendFiniteOrbit {X : Type} {F : Correspondence X X}
    {A : Set X} {k l : ℕ} (z : Fin (k + 1) → X) (w : Fin (l + 1) → X)
    (hz : IsFiniteOrbit F z) (hw : IsFiniteOrbit F w)
    (hstitch : z ⟨k, Nat.lt_succ_self k⟩ = w 0)
    (hzA : ∀ i, z i ∈ A) (hwA : ∀ i, w i ∈ A) :
    ∃ c : Fin (k + l + 1) → X, c 0 = z 0 ∧ IsFiniteOrbit F c ∧
      (∀ i, c i ∈ A) ∧ c ⟨k + l, Nat.lt_succ_self (k + l)⟩ =
        w ⟨l, Nat.lt_succ_self l⟩ := by
  let c : Fin (k + l + 1) → X := fun i =>
    if h : (i : ℕ) ≤ k then z ⟨i, by omega⟩ else w ⟨(i : ℕ) - k, by omega⟩
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · simp [c]
  · intro i
    by_cases hik : (i : ℕ) < k
    · let iz : Fin k := ⟨i, hik⟩
      have hsource : c i.castSucc = z iz.castSucc := by
        dsimp only [c]
        simp only [Fin.val_castSucc]
        rw [dif_pos hik.le]
        apply congrArg z
        apply Fin.ext
        rfl
      have htarget : c i.succ = z iz.succ := by
        dsimp only [c]
        simp only [Fin.val_succ]
        rw [dif_pos (Nat.succ_le_iff.mpr hik)]
        apply congrArg z
        apply Fin.ext
        rfl
      rw [hsource, htarget]
      exact hz iz
    · have hki : k ≤ (i : ℕ) := Nat.le_of_not_gt hik
      by_cases hieq : (i : ℕ) = k
      · have hl0 : 0 < l := by omega
        let iw : Fin l := ⟨0, hl0⟩
        have hsource : c i.castSucc = z ⟨k, Nat.lt_succ_self k⟩ := by
          dsimp only [c]
          simp only [Fin.val_castSucc]
          rw [dif_pos (hieq.le)]
          apply congrArg z
          exact Fin.ext hieq
        have htarget : c i.succ = w iw.succ := by
          dsimp only [c]
          simp only [Fin.val_succ]
          rw [dif_neg (by omega)]
          apply congrArg w
          apply Fin.ext
          dsimp only [iw]
          simp only [Fin.val_succ]
          omega
        rw [hsource, htarget, hstitch]
        exact hw iw
      · have hkiStrict : k < (i : ℕ) := hki.lt_of_ne (Ne.symm hieq)
        let iw : Fin l := ⟨(i : ℕ) - k, by omega⟩
        have hsource : c i.castSucc = w iw.castSucc := by
          dsimp only [c]
          simp only [Fin.val_castSucc]
          rw [dif_neg (by omega)]
          apply congrArg w
          apply Fin.ext
          rfl
        have htarget : c i.succ = w iw.succ := by
          dsimp only [c]
          simp only [Fin.val_succ]
          rw [dif_neg (by omega)]
          apply congrArg w
          apply Fin.ext
          dsimp only [iw]
          simp only [Fin.val_succ]
          omega
        rw [hsource, htarget]
        exact hw iw
  · intro i
    by_cases hi : (i : ℕ) ≤ k
    · simpa only [c, dif_pos hi] using hzA ⟨i, by omega⟩
    · simpa only [c, dif_neg hi] using hwA ⟨(i : ℕ) - k, by omega⟩
  · by_cases hl : l = 0
    · subst l
      simpa [c] using hstitch
    · have hl0 : 0 < l := Nat.pos_of_ne_zero hl
      dsimp only [c]
      rw [dif_neg (by omega)]
      apply congrArg w
      apply Fin.ext
      simp

/-- A point weakly above every solo payoff and equal to one lies on `∂W`. -/
theorem mem_frontier_WSet_of (G : QuittingGame) (x : Payoff G.Player)
    (hx : ∀ n, SoloPayoff G n ≤ x n) (j : G.Player)
    (hxj : x j = SoloPayoff G j) : x ∈ frontier (WSet G) := by
  rw [frontier_eq_closure_inter_closure]
  constructor
  · apply subset_closure
    exact ⟨j, hxj.le⟩
  · let y : ℕ → Payoff G.Player := fun m n => x n + 1 / ((m : ℝ) + 1)
    apply mem_closure_of_tendsto (b := atTop) (f := y)
    · apply tendsto_pi_nhds.mpr
      intro n
      have ht : Tendsto (fun m : ℕ => x n + 1 / ((m : ℝ) + 1)) atTop
          (nhds (x n + 0)) :=
        tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa only [y, add_zero] using ht
    · exact Filter.Eventually.of_forall fun m => by
        rw [Set.mem_compl_iff]
        intro hm
        rcases hm with ⟨n, hn⟩
        have hpositive : 0 < 1 / ((m : ℝ) + 1) := by positivity
        dsimp only [y] at hn
        linarith [hx n]

/-- A critical point lies on `∂W` and has the two solo coordinates and strict cross-payoff. -/
def IsCriticalPoint (G : QuittingGame) (x : Payoff G.Player) : Prop :=
  x ∈ frontier (WSet G) ∧ ∃ j k, j ≠ k ∧ x j = SoloPayoff G j ∧
    x k = SoloPayoff G k ∧
    G.reward ⟨{j}, Finset.singleton_nonempty j⟩ k < SoloPayoff G k

/--
The checked orbit construction in Lemma 11, conditional on its cross-harm input from the
corrected Lemma 5.
-/
theorem lemma11_of_crossHarm (G : QuittingGame) (E : EscapeWitness G) {M ρ ε : ℝ}
    (hM : IsQuittingPayoffDifferenceBound G M)
    (hρ : IsUniformRho G ρ) (hnormal : ∀ n, IsNormalPlayer G n)
    (hcross : EveryNormalSoloQuitterHarmsNormal G) (hε : 0 < ε)
    (_hεe : ε < E.ebar) (hερ : ε < ρ) :
    let δ := ε / (10 * M * Fintype.card G.Player)
    ∀ x ∈ EscapeBand G ε, ∃ (k : ℕ)
      (z : Fin (k + 1) → Payoff G.Player), z 0 = x ∧
        IsFiniteOrbit (RestrictedEscapeCorrespondence G δ ε) z ∧
        (∀ i, z i ∈ EscapeBand G ε) ∧
        IsCriticalPoint G (z ⟨k, Nat.lt_succ_self k⟩) := by
  classical
  let delta := ε / (10 * M * Fintype.card G.Player)
  have hMpositive : 0 < M := lt_of_lt_of_le zero_lt_one hM.1
  have hcard : (1 : ℝ) ≤ Fintype.card G.Player := by
    exact_mod_cast Fintype.card_pos
  have hdenominator : 0 < 10 * M * (Fintype.card G.Player : ℝ) := by positivity
  have hdelta0 : 0 < delta := div_pos hε hdenominator
  have hdenominatorOne : 1 < 10 * M * (Fintype.card G.Player : ℝ) := by
    have hten : (10 : ℝ) ≤ 10 * M * Fintype.card G.Player := by
      calc
        (10 : ℝ) = 10 * 1 := by ring
        _ ≤ 10 * M := mul_le_mul_of_nonneg_left hM.1 (by norm_num)
        _ = 10 * M * 1 := by ring
        _ ≤ 10 * M * Fintype.card G.Player :=
          mul_le_mul_of_nonneg_left hcard (by positivity)
    linarith
  have hε1 : ε < 1 := hερ.trans_le hρ.2.1
  have hdelta1 : delta < 1 := by
    dsimp [delta]
    exact (div_lt_one hdenominator).2 (hε1.trans hdenominatorOne)
  dsimp only
  intro x hxBand
  have hfirst : ∃ (k : ℕ) (z : Fin (k + 1) → Payoff G.Player) (a : G.Player),
      z 0 = x ∧ IsFiniteOrbit (RestrictedEscapeCorrespondence G delta ε) z ∧
      (∀ i, z i ∈ EscapeBand G ε) ∧
      z ⟨k, Nat.lt_succ_self k⟩ a = SoloPayoff G a := by
    by_cases hboundary : ∃ a, x a = SoloPayoff G a
    · rcases hboundary with ⟨a, ha⟩
      let z : Fin (0 + 1) → Payoff G.Player := fun _ => x
      refine ⟨0, z, a, rfl, ?_, ?_, ha⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact hxBand
    · push Not at hboundary
      rcases hxBand.2 with ⟨j, hxj⟩
      rcases hcross j (hnormal j) with ⟨k, hkj, _hknormal, hreward⟩
      have hstrict : ∀ n, SoloPayoff G n < x n := by
        intro n
        exact (hxBand.1 n).lt_of_ne (Ne.symm (hboundary n))
      obtain ⟨m, z, hz0, hzorbit, hzband, _hzj, n, hn, _hnreward⟩ :=
        exists_soloBoundaryOrbit G hdelta0 hdelta1 j x hxBand.1 hxj
          (fun n _ => hstrict n) ⟨k, hreward⟩
      exact ⟨m, z, n, hz0, hzorbit, hzband, hn⟩
  rcases hfirst with ⟨k, z, a, hz0, hzorbit, hzband, ha⟩
  let y := z ⟨k, Nat.lt_succ_self k⟩
  by_cases hyCritical : IsCriticalPoint G y
  · exact ⟨k, z, hz0, hzorbit, hzband, hyCritical⟩
  · rcases hcross a (hnormal a) with ⟨b, hba, _hbnormal, hab⟩
    have hyBand : y ∈ EscapeBand G ε := hzband ⟨k, Nat.lt_succ_self k⟩
    have hyFrontier : y ∈ frontier (WSet G) :=
      mem_frontier_WSet_of G y hyBand.1 a ha
    have hfallStrict : ∀ n,
        G.reward ⟨{a}, Finset.singleton_nonempty a⟩ n < SoloPayoff G n →
          SoloPayoff G n < y n := by
      intro n hnfall
      have hna : n ≠ a := by
        intro hna
        subst n
        exact (lt_irrefl _ hnfall)
      apply (hyBand.1 n).lt_of_ne
      intro hne
      apply hyCritical
      exact ⟨hyFrontier, a, n, Ne.symm hna, ha, hne.symm, hnfall⟩
    have hya : y a ≤ SoloPayoff G a + ε := by linarith
    obtain ⟨l, w, hw0, hworbit, hwband, hwaUpper, n, hn, han⟩ :=
      exists_soloBoundaryOrbit G hdelta0 hdelta1 a y hyBand.1 hya
        hfallStrict ⟨b, hab⟩
    have hwa : w ⟨l, Nat.lt_succ_self l⟩ a = SoloPayoff G a := by
      apply le_antisymm
      · exact (hwaUpper ⟨l, Nat.lt_succ_self l⟩).trans_eq ha
      · exact (hwband ⟨l, Nat.lt_succ_self l⟩).1 a
    have hnLower := (hwband ⟨l, Nat.lt_succ_self l⟩).1
    have hlastCritical : IsCriticalPoint G (w ⟨l, Nat.lt_succ_self l⟩) := by
      refine ⟨mem_frontier_WSet_of G _ hnLower a hwa, a, n, ?_, hwa, hn, han⟩
      intro hanEq
      subst n
      exact (lt_irrefl _ han)
    obtain ⟨c, hc0, hcorbit, hcband, hclast⟩ :=
      exists_appendFiniteOrbit z w hzorbit hworbit (by simpa [y] using hw0.symm)
        hzband hwband
    refine ⟨k + l, c, hc0.trans hz0, hcorbit, hcband, ?_⟩
    rw [hclast]
    exact hlastCritical

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
