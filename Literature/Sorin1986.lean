import Mathlib
import GameTheory.Analysis.Payoff
import UniformEquilibrium.ProofView.Concepts.Existence.CompactNash
import UniformEquilibrium.ProofView.Concepts.Stochastic.Transform.Repeated.RealizedActionRepeatedAdapter
import UniformEquilibrium.ProofView.Concepts.Welfare.FolkTheorem.Feasible
import UniformEquilibrium.ProofView.Native.Equilibrium

/-!
# Sorin (1986), *On Repeated Games with Complete Information*

Sylvain Sorin, *On repeated games with complete information*, Mathematics of
Operations Research **11**(1), 147--160 (1986), DOI
`10.1287/moor.11.1.147`.

This file follows the supplied journal article, including its added-in-proof
qualification of Lemma 2.  The paper's discount parameter `λ` is the weight of
the current stage; the repository stochastic-game API uses the continuation
factor `β`, so the translation below is `β = 1 - λ`.

The repeated-game model is not an unconstrained payoff oracle.  A finite stage
game is compiled to the repository's one-state stochastic game with publicly
observed realized action profiles.  Its behavior profiles give a behavioral
presentation that is outcome-equivalent to the paper's mixed strategies under
perfect recall and standard signalling.

Unproved paper claims end in `sorry`.  Each such declaration states the
missing formal ingredient immediately before the claim.  Elementary
identities and the static parts of the examples are proved here.
-/

noncomputable section

namespace Literature.Sorin1986

open GameTheory Set Filter
open scoped BigOperators Topology

/-! ## 1. Notation and preliminaries -/

/-- A finite normal-form game, the paper's `G₁`. -/
structure FiniteStageGame where
  Player : Type
  [finitePlayer : Fintype Player]
  [decidablePlayer : DecidableEq Player]
  Action : Player → Type
  [finiteAction : ∀ i, Fintype (Action i)]
  [decidableAction : ∀ i, DecidableEq (Action i)]
  [nonemptyAction : ∀ i, Nonempty (Action i)]
  payoff : (∀ i, Action i) → Payoff Player

attribute [instance] FiniteStageGame.finitePlayer
attribute [instance] FiniteStageGame.decidablePlayer
attribute [instance] FiniteStageGame.finiteAction
attribute [instance] FiniteStageGame.decidableAction
attribute [instance] FiniteStageGame.nonemptyAction

/-- Deterministic kernel presentation of the one-stage game. -/
noncomputable def FiniteStageGame.kernel (G : FiniteStageGame) :
    KernelGame G.Player :=
  KernelGame.ofPureEU G.Action G.payoff

/-- A mixed one-stage profile. -/
abbrev FiniteStageGame.MixedProfile (G : FiniteStageGame) :=
  KernelGame.Profile G.kernel.mixedExtension

/-- The public-history repeated game associated with `G`. -/
abbrev FiniteStageGame.repeatedGame (G : FiniteStageGame) :=
  G.kernel.realizedActionStochasticGame

/-- A behavioral profile in the repeated game. -/
abbrev FiniteStageGame.BehaviorProfile (G : FiniteStageGame) :=
  G.repeatedGame.BehaviorProfile

/-- A behavioral strategy of one player in the repeated game. -/
abbrev FiniteStageGame.BehaviorStrategy (G : FiniteStageGame)
    (who : G.Player) :=
  G.repeatedGame.BehaviorStrategy who

/-- Positive finite horizons, the domain of the paper's `Gₙ`. -/
abbrev FiniteStageGame.Horizon (_G : FiniteStageGame) :=
  {n : ℕ // 0 < n}

/-- Discount parameters in the paper's domain `0 < λ ≤ 1`. -/
abbrev FiniteStageGame.DiscountRate (_G : FiniteStageGame) :=
  {lam : ℝ // 0 < lam ∧ lam ≤ 1}

/-- Expected one-stage payoff under a mixed profile. -/
noncomputable def FiniteStageGame.mixedPayoff (G : FiniteStageGame)
    (profile : G.MixedProfile) : Payoff G.Player :=
  G.kernel.mixedExtension.payoffVector profile

/-- The expected average payoff in the `n`-stage repetition. -/
noncomputable def FiniteStageGame.finitePayoff (G : FiniteStageGame)
    (n : ℕ) (profile : G.BehaviorProfile) : Payoff G.Player :=
  fun who => G.repeatedGame.finiteAveragePayoff PUnit.unit n profile who

/-- The paper's `λ`-discounted payoff.  Repository continuation is `1 - λ`. -/
noncomputable def FiniteStageGame.discountedPayoff (G : FiniteStageGame)
    (lam : ℝ) (profile : G.BehaviorProfile) : Payoff G.Player :=
  fun who => G.repeatedGame.discountedPayoff (1 - lam) profile PUnit.unit who


/-- Finite payoff with the paper's positive-horizon domain exposed in
the type. -/
abbrev FiniteStageGame.finitePayoffOnHorizon (G : FiniteStageGame)
    (n : G.Horizon) : G.BehaviorProfile → Payoff G.Player :=
  G.finitePayoff n.1

/-- Discounted payoff with `0 < λ ≤ 1` exposed in the type. -/
abbrev FiniteStageGame.discountedPayoffOnRate (G : FiniteStageGame)
    (lam : G.DiscountRate) : G.BehaviorProfile → Payoff G.Player :=
  G.discountedPayoff lam.1

/-- Feasible one-stage payoffs, the paper's `D₁`. -/
def FiniteStageGame.oneStageFeasiblePayoffs (G : FiniteStageGame) :
    Set (Payoff G.Player) :=
  Set.range G.mixedPayoff

/-- Nash equilibrium payoffs of the mixed one-stage game, the paper's `E₁`. -/
def FiniteStageGame.oneStageEquilibriumPayoffs (G : FiniteStageGame) :
    Set (Payoff G.Player) :=
  {v | ∃ profile : G.MixedProfile,
      G.kernel.mixedExtension.IsNash profile ∧ G.mixedPayoff profile = v}

/-- Feasible payoffs of the `n`-stage game, the paper's `Dₙ`. -/
def FiniteStageGame.finiteFeasiblePayoffs (G : FiniteStageGame) (n : ℕ) :
    Set (Payoff G.Player) :=
  Set.range (G.finitePayoff n)

/-- Nash equilibrium payoffs of the `n`-stage game, the paper's `Eₙ`. -/
def FiniteStageGame.finiteEquilibriumPayoffs (G : FiniteStageGame) (n : ℕ) :
    Set (Payoff G.Player) :=
  {v | ∃ profile : G.BehaviorProfile,
      G.repeatedGame.IsεHorizonNash PUnit.unit n 0 profile ∧
        G.finitePayoff n profile = v}

/-- Feasible payoffs of the `λ`-discounted game, the paper's `D_λ`. -/
def FiniteStageGame.discountedFeasiblePayoffs (G : FiniteStageGame) (lam : ℝ) :
    Set (Payoff G.Player) :=
  Set.range (G.discountedPayoff lam)

/-- Nash equilibrium payoffs of the `λ`-discounted game, the paper's `E_λ`. -/
def FiniteStageGame.discountedEquilibriumPayoffs
    (G : FiniteStageGame) (lam : ℝ) : Set (Payoff G.Player) :=
  {v | ∃ profile : G.BehaviorProfile,
      G.repeatedGame.IsDiscountedεNash (1 - lam) PUnit.unit 0 profile ∧
        G.discountedPayoff lam profile = v}


/-! The paper-facing wrappers below prevent accidental use of horizon
zero and of discounts outside `0 < λ ≤ 1`.  The raw definitions above
remain useful for block formulas in which a zero residual block is
represented explicitly. -/

abbrev FiniteStageGame.finiteFeasiblePayoffsOnHorizon
    (G : FiniteStageGame) (n : G.Horizon) : Set (Payoff G.Player) :=
  G.finiteFeasiblePayoffs n.1

abbrev FiniteStageGame.finiteEquilibriumPayoffsOnHorizon
    (G : FiniteStageGame) (n : G.Horizon) : Set (Payoff G.Player) :=
  G.finiteEquilibriumPayoffs n.1

abbrev FiniteStageGame.discountedFeasiblePayoffsOnRate
    (G : FiniteStageGame) (lam : G.DiscountRate) : Set (Payoff G.Player) :=
  G.discountedFeasiblePayoffs lam.1

abbrev FiniteStageGame.discountedEquilibriumPayoffsOnRate
    (G : FiniteStageGame) (lam : G.DiscountRate) : Set (Payoff G.Player) :=
  G.discountedEquilibriumPayoffs lam.1

/-- A real sequence is bounded. -/
def IsBoundedSequence (sequence : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n, |sequence n| ≤ C

/-- A Banach limit on bounded sequences, extended arbitrarily outside the
bounded sequences.  Every axiom is restricted to bounded inputs. -/
structure BanachLimit where
  eval : (ℕ → ℝ) → ℝ
  map_add : ∀ f g, IsBoundedSequence f → IsBoundedSequence g →
    eval (fun n => f n + g n) = eval f + eval g
  map_smul : ∀ c f, IsBoundedSequence f →
    eval (fun n => c * f n) = c * eval f
  positive : ∀ f, IsBoundedSequence f → (∀ n, 0 ≤ f n) → 0 ≤ eval f
  constant : ∀ c, eval (fun _ => c) = c
  shift : ∀ f, IsBoundedSequence f → eval (fun n => f (n + 1)) = eval f
  agreesWithLimit : ∀ f x, IsBoundedSequence f →
    Tendsto f atTop (𝓝 x) → eval f = x

/-- The payoff in the paper's `L`-infinitely repeated game. -/
noncomputable def FiniteStageGame.banachPayoff (G : FiniteStageGame)
    (L : BanachLimit) (profile : G.BehaviorProfile) : Payoff G.Player :=
  fun who => L.eval (fun n => G.finitePayoff (n + 1) profile who)

/-- Nash equilibrium for the Banach-limit payoff. -/
def FiniteStageGame.IsBanachNash (G : FiniteStageGame) (L : BanachLimit)
    (profile : G.BehaviorProfile) : Prop :=
  ∀ who (deviation : G.BehaviorStrategy who),
    G.banachPayoff L profile who ≥
      G.banachPayoff L (Function.update profile who deviation) who

/-- Feasible Banach-limit payoffs, the paper's `D_∞`. -/
def FiniteStageGame.banachFeasiblePayoffs (G : FiniteStageGame)
    (L : BanachLimit) : Set (Payoff G.Player) :=
  Set.range (G.banachPayoff L)

/-- Banach-limit equilibrium payoffs, the paper's `E_∞`. -/
def FiniteStageGame.banachEquilibriumPayoffs (G : FiniteStageGame)
    (L : BanachLimit) : Set (Payoff G.Player) :=
  {v | ∃ profile : G.BehaviorProfile,
      G.IsBanachNash L profile ∧ G.banachPayoff L profile = v}

/-- Pure-profile payoff vectors, the paper's finite set `F`. -/
def FiniteStageGame.purePayoffSet (G : FiniteStageGame) :
    Set (Payoff G.Player) :=
  Set.range G.payoff

/-- Correlated feasible payoffs, the paper's `C = co F`. -/
def FiniteStageGame.correlatedFeasiblePayoffs (G : FiniteStageGame) :
    Set (Payoff G.Player) :=
  convexHull ℝ G.purePayoffSet

/-- `C` is convex by construction. -/
theorem FiniteStageGame.correlatedFeasiblePayoffs_convex
    (G : FiniteStageGame) : Convex ℝ G.correlatedFeasiblePayoffs := by
  exact convex_convexHull ℝ G.purePayoffSet

/-- Mixed opponent profiles in the one-stage mixed extension. -/
abbrev FiniteStageGame.MixedOpponentProfile (G : FiniteStageGame)
    (who : G.Player) :=
  G.kernel.mixedExtension.OpponentProfile who

/-- Best pure reply against one mixed opponent profile. -/
noncomputable def FiniteStageGame.bestPureReplyValue (G : FiniteStageGame)
    (who : G.Player) (opponents : G.MixedOpponentProfile who) : ℝ :=
  ⨆ action : G.Action who,
    G.kernel.mixedExtension.eu
      (G.kernel.mixedExtension.profileWithOpponent who
        (PMF.pure action) opponents) who

/-- The paper's individual-rational level
`aᵢ = min_{τ⁻ⁱ} max_{tᵢ} Xᵢ(τ⁻ⁱ,tᵢ)`. -/
noncomputable def FiniteStageGame.individualRationalLevel
    (G : FiniteStageGame) (who : G.Player) : ℝ :=
  ⨅ opponents : G.MixedOpponentProfile who,
    G.bestPureReplyValue who opponents

/-- The paper's set `Δ` of feasible individually rational payoffs. -/
def FiniteStageGame.individuallyRationalPayoffs (G : FiniteStageGame) :
    Set (Payoff G.Player) :=
  G.correlatedFeasiblePayoffs ∩
    {v | ∀ who, G.individualRationalLevel who ≤ v who}

/-- Two sets are within `ε` in the Hausdorff sense. -/
def HausdorffClose {X : Type} [PseudoMetricSpace X]
    (ε : ℝ) (A B : Set X) : Prop :=
  (∀ x ∈ A, ∃ y ∈ B, dist x y < ε) ∧
    (∀ y ∈ B, ∃ x ∈ A, dist x y < ε)

/-- Hausdorff convergence of a sequence of sets. -/
def HausdorffConvergesAtTop {X : Type} [PseudoMetricSpace X]
    (sets : ℕ → Set X) (target : Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀, ∀ n, n₀ ≤ n → HausdorffClose ε (sets n) target

/-- Hausdorff convergence as a positive real parameter tends to zero. -/
def HausdorffConvergesAtZero {X : Type} [PseudoMetricSpace X]
    (sets : ℝ → Set X) (target : Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ lam : ℝ, 0 < lam → lam < δ → HausdorffClose ε (sets lam) target

/-- Full dimensionality in the ambient payoff space. -/
def FullDimensional {X : Type} [PseudoMetricSpace X] (S : Set X) : Prop :=
  ∃ x ∈ S, ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ⊆ S

/-! The paper first embeds `Gₙ` and `G_λ` into compact continuous games.
The regular-probability integral is represented here by its resulting compact
mixed-strategy spaces and continuous expected-payoff map. -/

/-- A compact continuous mixed game.  The inherited barycentre operation is
the finite mixing operation needed by compact Nash existence. -/
structure CompactContinuousGame extends GameTheory.CompactBarycentricGame where
  mix : ∀ i, ℝ → Strategy i → Strategy i → Strategy i
  mixContinuous : ∀ i, Continuous fun p : ℝ × (Strategy i × Strategy i) =>
    mix i p.1 p.2.1 p.2.2
  mix_zero : ∀ i x y, mix i 0 x y = y
  mix_one : ∀ i x y, mix i 1 x y = x
  payoffAffine : ∀ profile i x y t who, 0 ≤ t → t ≤ 1 →
    payoff (Function.update profile i (mix i t x y)) who =
      t * payoff (Function.update profile i x) who +
        (1 - t) * payoff (Function.update profile i y) who

/-- A mixed-profile carrier for a compact continuous game. -/
abbrev CompactContinuousGame.Profile (G : CompactContinuousGame) :=
  G.toCompactBarycentricGame.Profile

/-- Feasible payoff set of a compact continuous game. -/
def CompactContinuousGame.feasiblePayoffs (G : CompactContinuousGame) :
    Set (Payoff G.Player) :=
  Set.range G.payoff

/-- Nash equilibrium in a compact continuous game. -/
abbrev CompactContinuousGame.IsNash (G : CompactContinuousGame)
    (profile : G.Profile) : Prop :=
  G.toCompactBarycentricGame.IsNash profile

/-- Nash equilibrium payoff set of a compact continuous game. -/
abbrev CompactContinuousGame.equilibriumPayoffs (G : CompactContinuousGame) :
    Set (Payoff G.Player) :=
  G.toCompactBarycentricGame.equilibriumPayoffs

/-- Path connectedness, stated without relying on a particular library
encoding of paths. -/
def PathConnectedSet {X : Type} [TopologicalSpace X] (S : Set X) : Prop :=
  S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S,
    ∃ path : ℝ → X, Continuous path ∧ path 0 = x ∧ path 1 = y ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, path t ∈ S

/-- A closed path in a set. -/
def ClosedPathIn {X : Type} [TopologicalSpace X]
    (S : Set X) (path : ℝ → X) : Prop :=
  Continuous path ∧ path 0 = path 1 ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, path t ∈ S

/-- Null-homotopy through paths that remain in `S` and keep the base point
fixed. -/
def NullHomotopicIn {X : Type} [TopologicalSpace X]
    (S : Set X) (path : ℝ → X) : Prop :=
  ∃ H : ℝ × ℝ → X, Continuous H ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, H (s, t) ∈ S) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, H (0, t) = path t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, H (1, t) = path 0) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, H (s, 0) = path 0 ∧ H (s, 1) = path 0)

/-- The simply-connectedness notion used in Proposition 11. -/
def SimplyConnectedSet {X : Type} [TopologicalSpace X] (S : Set X) : Prop :=
  PathConnectedSet S ∧ ∀ path, ClosedPathIn S path → NullHomotopicIn S path

/-- A faithful bridge from one repeated-game evaluator to the paper's
compact mixed normal form.  `Strategy` is the compact carrier of mixed pure
contingent plans (or an equivalent realization-plan presentation), not the
behavior-strategy carrier itself.  The two transport maps record perfect
recall's mixed/behavioral equivalence, including payoff and Nash preservation. -/
structure CompactRepeatedPresentation (G : FiniteStageGame)
    (payoff : G.BehaviorProfile → Payoff G.Player)
    (isNash : G.BehaviorProfile → Prop) where
  Strategy : G.Player → Type
  [strategyTopology : ∀ who, TopologicalSpace (Strategy who)]
  [compactStrategy : ∀ who, CompactSpace (Strategy who)]
  [nonemptyStrategy : ∀ who, Nonempty (Strategy who)]
  mix : ∀ who, ℝ → Strategy who → Strategy who → Strategy who
  mixContinuous : ∀ who, Continuous fun p :
      ℝ × (Strategy who × Strategy who) =>
    mix who p.1 p.2.1 p.2.2
  mix_zero : ∀ who x y, mix who 0 x y = y
  mix_one : ∀ who x y, mix who 1 x y = x
  compactPayoff : (∀ who, Strategy who) → Payoff G.Player
  compactPayoffContinuous : ∀ observer,
    Continuous fun profile => compactPayoff profile observer
  compactPayoffAffine : ∀ profile who x y t observer, 0 ≤ t → t ≤ 1 →
    compactPayoff (Function.update profile who (mix who t x y)) observer =
      t * compactPayoff (Function.update profile who x) observer +
        (1 - t) * compactPayoff (Function.update profile who y) observer
  barycenter : ∀ who (n : ℕ),
    stdSimplex ℝ (Fin (n + 1)) →
      (Fin (n + 1) → Strategy who) → Strategy who
  barycenterContinuous : ∀ who (n : ℕ)
    (points : Fin (n + 1) → Strategy who),
    Continuous fun weights : stdSimplex ℝ (Fin (n + 1)) =>
      barycenter who n weights points
  compactPayoffBarycentric : ∀ profile who (n : ℕ)
    (weights : stdSimplex ℝ (Fin (n + 1)))
    (points : Fin (n + 1) → Strategy who),
    compactPayoff (Function.update profile who
        (barycenter who n weights points)) who =
      ∑ a, weights a *
        compactPayoff (Function.update profile who (points a)) who
  toBehavior : (∀ who, Strategy who) → G.BehaviorProfile
  fromBehavior : G.BehaviorProfile → (∀ who, Strategy who)
  payoff_toBehavior : ∀ profile,
    payoff (toBehavior profile) = compactPayoff profile
  payoff_fromBehavior : ∀ profile,
    compactPayoff (fromBehavior profile) = payoff profile
  nash_toBehavior_iff : ∀ profile,
    (∀ who deviation,
      compactPayoff profile who ≥
        compactPayoff (Function.update profile who deviation) who) ↔
      isNash (toBehavior profile)
  nash_fromBehavior_iff : ∀ profile,
    (∀ who deviation,
      compactPayoff (fromBehavior profile) who ≥
        compactPayoff
          (Function.update (fromBehavior profile) who deviation) who) ↔
      isNash profile

attribute [instance] CompactRepeatedPresentation.strategyTopology
attribute [instance] CompactRepeatedPresentation.compactStrategy
attribute [instance] CompactRepeatedPresentation.nonemptyStrategy

/-- Forget only the provenance and repeated-game transports. -/
noncomputable def CompactRepeatedPresentation.toCompactContinuousGame
    {G : FiniteStageGame} {payoff : G.BehaviorProfile → Payoff G.Player}
    {isNash : G.BehaviorProfile → Prop}
    (presentation : CompactRepeatedPresentation G payoff isNash) :
    CompactContinuousGame where
  toCompactBarycentricGame := {
    Player := G.Player
    Strategy := presentation.Strategy
    payoff := presentation.compactPayoff
    payoffContinuous := presentation.compactPayoffContinuous
    barycenter := presentation.barycenter
    barycenterContinuous := presentation.barycenterContinuous
    payoffBarycentric := presentation.compactPayoffBarycentric
  }
  mix := presentation.mix
  mixContinuous := presentation.mixContinuous
  mix_zero := presentation.mix_zero
  mix_one := presentation.mix_one
  payoffAffine := presentation.compactPayoffAffine

/-- The compact mixed presentation and behavioral evaluator have exactly the
same feasible payoff set. -/
theorem CompactRepeatedPresentation.feasiblePayoffs_eq
    {G : FiniteStageGame} {payoff : G.BehaviorProfile → Payoff G.Player}
    {isNash : G.BehaviorProfile → Prop}
    (presentation : CompactRepeatedPresentation G payoff isNash) :
    presentation.toCompactContinuousGame.feasiblePayoffs =
      Set.range payoff := by
  ext value
  constructor
  · rintro ⟨profile, rfl⟩
    exact ⟨presentation.toBehavior profile,
      presentation.payoff_toBehavior profile⟩
  · rintro ⟨profile, rfl⟩
    exact ⟨presentation.fromBehavior profile,
      presentation.payoff_fromBehavior profile⟩

/-- The bridge also identifies Nash payoff sets; in particular, no Nash
nonemptiness assumption is hidden in the reduction. -/
theorem CompactRepeatedPresentation.equilibriumPayoffs_eq
    {G : FiniteStageGame} {payoff : G.BehaviorProfile → Payoff G.Player}
    {isNash : G.BehaviorProfile → Prop}
    (presentation : CompactRepeatedPresentation G payoff isNash) :
    presentation.toCompactContinuousGame.equilibriumPayoffs =
      {v | ∃ profile, isNash profile ∧ payoff profile = v} := by
  ext value
  constructor
  · rintro ⟨profile, hprofile, rfl⟩
    refine ⟨presentation.toBehavior profile,
      (presentation.nash_toBehavior_iff profile).mp hprofile, ?_⟩
    exact presentation.payoff_toBehavior profile
  · rintro ⟨profile, hprofile, rfl⟩
    refine ⟨presentation.fromBehavior profile,
      (presentation.nash_fromBehavior_iff profile).mpr hprofile, ?_⟩
    exact presentation.payoff_fromBehavior profile

namespace FinitePresentation

open GameTheory.Math.Probability

private instance repeatedStateFinite (G : FiniteStageGame) :
    Finite G.repeatedGame.State := by
  change Finite PUnit
  infer_instance

private instance repeatedActionFintype (G : FiniteStageGame) (who : G.Player) :
    Fintype (G.repeatedGame.toNative.Action who) := by
  change Fintype (G.Action who)
  infer_instance

private instance repeatedActionNonempty (G : FiniteStageGame) (who : G.Player) :
    Nonempty (G.repeatedGame.toNative.Action who) := by
  change Nonempty (G.Action who)
  infer_instance

/-- The canonical perfect-monitoring protocol for the repeated stage game. -/
private abbrev Protocol (G : FiniteStageGame) :=
  G.repeatedGame.toNative.perfectMonitoring PUnit.unit

/-- The finite set of counterfactual information states relevant through the
chosen horizon. -/
private abbrev Sites (G : FiniteStageGame) (n : G.Horizon) (who : G.Player) :=
  G.repeatedGame.toNative.boundedInformationSites PUnit.unit n.1 who

private instance choiceFintype (G : FiniteStageGame) (n : G.Horizon)
    (who : G.Player) (info : Sites G n who) :
    Fintype ((Protocol G).Choice who info) :=
  G.repeatedGame.toNative.perfectMonitoringChoiceFintype
    PUnit.unit who info

/-- A pure contingent plan restricted to the finitely many information states
that can matter through the chosen horizon. -/
private abbrev Plan (G : FiniteStageGame) (n : G.Horizon) (who : G.Player) :=
  (info : Sites G n who) → (Protocol G).Choice who info

private instance planFintype (G : FiniteStageGame) (n : G.Horizon)
    (who : G.Player) : Fintype (Plan G n who) := by
  classical
  exact Fintype.ofEquiv ((info : Sites G n who) → G.Action who)
    (Equiv.piCongrRight fun info =>
      G.repeatedGame.toNative.actionChoiceEquiv PUnit.unit who info)

/-- One fixed legal total policy used only outside the bounded site set. -/
private noncomputable def fallback (G : FiniteStageGame) (who : G.Player) :
    (Protocol G).Policy who :=
  (G.repeatedGame.toNative.purePolicyEquiv PUnit.unit who).symm
    (fun _ => Classical.choice (G.nonemptyAction who))

/-- Extend a bounded contingent plan to a total deterministic policy. -/
private noncomputable def assemble (G : FiniteStageGame) (n : G.Horizon)
    (who : G.Player) (plan : Plan G n who) : (Protocol G).Policy who :=
  GameTheory.Protocol.InformationModel.Policy.assembleWithin
    (Protocol G) (fallback G who) (Sites G n who) plan

/-- The finite pure normal form obtained by executing assembled bounded plans
with the canonical Protocol runner. -/
private noncomputable abbrev form (G : FiniteStageGame) (n : G.Horizon) :
    GameForm G.Player where
  sig := {
    Strategy := Plan G n
    Outcome := (G.repeatedGame.toNative.toExecution PUnit.unit).History
  }
  play profile :=
    (Protocol G).run (fun who => assemble G n who (profile who)) n.1

/-- A compact strategy is a probability vector on the finite pure-plan
carrier. -/
private abbrev Strategy (G : FiniteStageGame) (n : G.Horizon)
    (who : G.Player) :=
  stdSimplex ℝ (Plan G n who)

/-- Read a simplex point as the corresponding finite-support plan law. -/
private noncomputable def law {G : FiniteStageGame} {n : G.Horizon}
    {who : G.Player} (strategy : Strategy G n who) : FinDist (Plan G n who) :=
  FinDist.ofSimplex strategy.2

/-- Convert a simplex profile coordinatewise to finite plan laws. -/
private noncomputable def laws {G : FiniteStageGame} {n : G.Horizon}
    (profile : ∀ who, Strategy G n who) :
    Profile (form G n).sig.mixed :=
  fun who => law (profile who)

/-- Embed finite plan laws into laws over total Protocol policies. -/
private noncomputable def mixedPolicies {G : FiniteStageGame}
    {n : G.Horizon} (profile : ∀ who, Strategy G n who) :
    Profile (Protocol G).strategicSignature.mixed :=
  fun who => FinDist.map (assemble G n who) (law (profile who))

private theorem form_mixed_play {G : FiniteStageGame} {n : G.Horizon}
    (profile : ∀ who, Strategy G n who) :
    (form G n).mixed.play (laws profile) =
      (Protocol G).runMixed (mixedPolicies profile) n.1 := by
  let extend : (∀ who, Plan G n who) → (∀ who, (Protocol G).Policy who) :=
    fun plans who => assemble G n who (plans who)
  have hpi : FinDist.pi (mixedPolicies profile) =
      FinDist.map extend (FinDist.pi (laws profile)) := by
    exact FinDist.pi_map (fun who => assemble G n who) (laws profile)
  have hbind := congrArg
    (fun distribution => distribution.bind fun policies =>
      (Protocol G).run policies n.1) hpi
  exact (hbind.trans (FinDist.bind_map extend (FinDist.pi (laws profile))
    (fun policies => (Protocol G).run policies n.1))).symm

private instance planNonempty (G : FiniteStageGame) (n : G.Horizon)
    (who : G.Player) : Nonempty (Plan G n who) :=
  ⟨fun info => G.repeatedGame.toNative.actionChoiceEquiv
    PUnit.unit who info (Classical.choice (G.nonemptyAction who))⟩

/-- Project an arbitrary real coefficient to the unit interval. -/
private def coefficient (t : ℝ) : ℝ := max 0 (min 1 t)

private theorem coefficient_nonneg (t : ℝ) : 0 ≤ coefficient t :=
  le_max_left _ _

private theorem coefficient_le_one (t : ℝ) : coefficient t ≤ 1 := by
  unfold coefficient
  exact max_le zero_le_one (min_le_left _ _)

private theorem coefficient_eq {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    coefficient t = t := by
  simp [coefficient, ht₀, ht₁]

/-- The usual convex combination on plan laws, extended continuously to all
real coefficients by projection to `[0,1]`. -/
private def mix {G : FiniteStageGame} {n : G.Horizon} (who : G.Player)
    (t : ℝ) (x y : Strategy G n who) : Strategy G n who := by
  let c := coefficient t
  refine ⟨c • x.1 + (1 - c) • y.1, ?_⟩
  refine ⟨fun plan => add_nonneg
    (mul_nonneg (coefficient_nonneg t) (x.2.1 plan))
    (mul_nonneg (sub_nonneg.mpr (coefficient_le_one t)) (y.2.1 plan)), ?_⟩
  change (∑ plan, (c * x.1 plan + (1 - c) * y.1 plan)) = 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    x.2.2, y.2.2]
  ring

private theorem mix_continuous {G : FiniteStageGame} {n : G.Horizon}
    (who : G.Player) : Continuous fun p :
      ℝ × (Strategy G n who × Strategy G n who) =>
        mix who p.1 p.2.1 p.2.2 := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro plan
  let domain := ℝ × (Strategy G n who × Strategy G n who)
  have hc : Continuous fun p : domain => coefficient p.1 := by
    unfold coefficient
    exact continuous_const.max (continuous_const.min continuous_fst)
  have hx : Continuous fun p : domain => p.2.1 plan :=
    (continuous_apply plan).comp
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hy : Continuous fun p : domain => p.2.2 plan :=
    (continuous_apply plan).comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  exact (hc.mul hx).add ((continuous_const.sub hc).mul hy)

private theorem mix_zero {G : FiniteStageGame} {n : G.Horizon}
    (who : G.Player) (x y : Strategy G n who) : mix who 0 x y = y := by
  ext plan
  simp [mix, coefficient]

private theorem mix_one {G : FiniteStageGame} {n : G.Horizon}
    (who : G.Player) (x y : Strategy G n who) : mix who 1 x y = x := by
  ext plan
  simp [mix, coefficient]

/-- Finite barycentres of plan laws are computed coordinatewise. -/
private def barycenter {G : FiniteStageGame} {n : G.Horizon}
    (who : G.Player) (k : ℕ) (weights : stdSimplex ℝ (Fin (k + 1)))
    (points : Fin (k + 1) → Strategy G n who) : Strategy G n who := by
  refine ⟨fun plan => ∑ a, weights a * points a plan, ?_⟩
  constructor
  · intro plan
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg (weights.2.1 a) ((points a).2.1 plan)
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp

private theorem barycenter_continuous {G : FiniteStageGame}
    {n : G.Horizon} (who : G.Player) (k : ℕ)
    (points : Fin (k + 1) → Strategy G n who) :
    Continuous fun weights : stdSimplex ℝ (Fin (k + 1)) =>
      barycenter who k weights points := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro plan
  apply continuous_finsetSum
  intro a _
  exact ((continuous_apply a).comp continuous_subtype_val).mul continuous_const

/-- The ambient weight profile underlying a compact simplex profile. -/
private def weights {G : FiniteStageGame} {n : G.Horizon}
    (profile : ∀ who, Strategy G n who) :
    Profile (form G n).sig.weights :=
  fun who plan => profile who plan

private theorem probs_laws {G : FiniteStageGame} {n : G.Horizon}
    (profile : ∀ who, Strategy G n who) :
    GameTheory.probs (form G n).sig (laws profile) = weights profile := by
  funext who plan
  exact congrFun (FinDist.prob_ofSimplex (profile who).2) plan

private theorem weights_update {G : FiniteStageGame} {n : G.Horizon}
    (profile : ∀ who, Strategy G n who) (who : G.Player)
    (strategy : Strategy G n who) :
    weights (Function.update profile who strategy) =
      Profile.update (weights profile) who strategy.1 := by
  funext i
  unfold weights
  by_cases hi : i = who
  · subst i
    simp only [Function.update_self, Profile.update_same]
    apply funext
    intro plan
    rfl
  · simp [Function.update_of_ne, Profile.update_of_ne, hi]

/-- The polynomial expected payoff of the finite mixed normal form. -/
private def compactPayoff {G : FiniteStageGame} {n : G.Horizon}
    (profile : ∀ who, Strategy G n who) : Payoff G.Player :=
  letI : ∀ who, Fintype ((form G n).sig.Strategy who) :=
    fun who => planFintype G n who
  fun observer => GameTheory.payoff (form G n)
      (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1) observer
      (weights profile)

private theorem compactPayoff_continuous {G : FiniteStageGame}
    {n : G.Horizon} (observer : G.Player) :
    Continuous fun profile : ∀ who, Strategy G n who =>
      compactPayoff profile observer := by
  letI : ∀ who, Fintype ((form G n).sig.Strategy who) :=
    fun who => planFintype G n who
  apply (GameTheory.continuous_payoff
    (F := form G n)
    (utility := G.repeatedGame.toNative.horizonUtility PUnit.unit n.1)
    observer).comp
  apply continuous_pi
  intro who
  apply continuous_pi
  intro plan
  exact (continuous_apply plan).comp
    (continuous_subtype_val.comp (continuous_apply who))

private theorem compactPayoff_affine {G : FiniteStageGame}
    {n : G.Horizon} (profile : ∀ who, Strategy G n who)
    (who : G.Player) (x y : Strategy G n who) (t : ℝ)
    (observer : G.Player) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    compactPayoff (Function.update profile who (mix who t x y)) observer =
      t * compactPayoff (Function.update profile who x) observer +
        (1 - t) * compactPayoff (Function.update profile who y) observer := by
  letI : ∀ i, Fintype ((form G n).sig.Strategy i) :=
    fun i => planFintype G n i
  let utility := G.repeatedGame.toNative.horizonUtility PUnit.unit n.1
  have h := GameTheory.payoff_update_mix
    (F := form G n)
    (utility := fun history _ => utility history observer)
    (x := weights profile) who x.1 y.1 t (1 - t)
  have hpay (z : Profile (form G n).sig.weights) :
      GameTheory.payoff (form G n)
          (fun history _ => utility history observer) who z =
        GameTheory.payoff (form G n) utility observer z := by
    rfl
  rw [compactPayoff, compactPayoff, compactPayoff,
    weights_update, weights_update, weights_update]
  change GameTheory.payoff (form G n) utility observer
      (Profile.update (weights profile) who
        (mix who t x y).1) = _
  rw [show (mix who t x y).1 = t • x.1 + (1 - t) • y.1 by
    ext plan
    simp [mix, coefficient_eq ht₀ ht₁]]
  rw [← hpay, ← hpay, ← hpay]
  exact h

private theorem compactPayoff_barycentric {G : FiniteStageGame}
    {n : G.Horizon} (profile : ∀ who, Strategy G n who)
    (who : G.Player) (k : ℕ)
    (simplexWeights : stdSimplex ℝ (Fin (k + 1)))
    (points : Fin (k + 1) → Strategy G n who) :
    compactPayoff (Function.update profile who
        (barycenter who k simplexWeights points)) who =
      ∑ a, simplexWeights a *
        compactPayoff (Function.update profile who (points a)) who := by
  letI : ∀ i, Fintype ((form G n).sig.Strategy i) :=
    fun i => planFintype G n i
  simp only [compactPayoff, weights_update]
  rw [GameTheory.payoff_update]
  simp_rw [GameTheory.payoff_update]
  let c (s : Profile (form G n).sig) : ℝ :=
    (∏ i ∈ Finset.univ.erase who, weights profile i (s i)) *
      expectedUtility
        (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1)
        who ((form G n).play s)
  change (∑ s : Profile (form G n).sig,
      (∑ a, simplexWeights a * points a (s who)) * c s) =
    ∑ a, simplexWeights a *
      ∑ s : Profile (form G n).sig, points a (s who) * c s
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem compactPayoff_eq_runMixed {G : FiniteStageGame}
    {n : G.Horizon} (profile : ∀ who, Strategy G n who)
    (observer : G.Player) :
    compactPayoff profile observer =
      expectedUtility
        (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1)
        observer ((Protocol G).runMixed (mixedPolicies profile) n.1) := by
  letI : ∀ i, Fintype ((form G n).sig.Strategy i) :=
    fun i => planFintype G n i
  calc
    compactPayoff profile observer =
        GameTheory.payoff (form G n)
          (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1)
          observer (GameTheory.probs (form G n).sig (laws profile)) := by
      rw [compactPayoff, probs_laws]
    _ = expectedUtility
        (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1)
        observer ((form G n).mixed.play (laws profile)) :=
      GameTheory.payoff_probs (laws profile) observer
    _ = _ := congrArg
      (expectedUtility
        (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1) observer)
      (form_mixed_play profile)

/-- Regard any finite law on bounded plans as its simplex point. -/
private def strategyOfLaw {G : FiniteStageGame} {n : G.Horizon}
    {who : G.Player} (distribution : FinDist (Plan G n who)) :
    Strategy G n who :=
  ⟨distribution.prob, distribution.prob_mem_stdSimplex⟩

private theorem law_strategyOfLaw {G : FiniteStageGame} {n : G.Horizon}
    {who : G.Player} (distribution : FinDist (Plan G n who)) :
    law (strategyOfLaw distribution) = distribution := by
  exact FinDist.ofSimplex_prob distribution

/-- Independently predraw a behavioral policy on every bounded information
site and record the resulting law as a simplex point. -/
private def strategyOfPolicy {G : FiniteStageGame} {n : G.Horizon}
    (who : G.Player) (policy : (Protocol G).BehavioralPolicy who) :
    Strategy G n who :=
  strategyOfLaw (FinDist.pi fun info : Sites G n who => policy info)

private theorem mixedPolicy_strategyOfPolicy {G : FiniteStageGame}
    {n : G.Horizon} (who : G.Player)
    (policy : (Protocol G).BehavioralPolicy who) :
    FinDist.map (assemble G n who) (law (strategyOfPolicy who policy)) =
      policy.toMixedWithin (Sites G n who) (fallback G who) := by
  calc
    _ = FinDist.map (assemble G n who)
        (FinDist.pi fun info : Sites G n who => policy info) :=
      congrArg (FinDist.map (assemble G n who))
        (law_strategyOfLaw
          (FinDist.pi fun info : Sites G n who => policy info))
    _ = _ := (GameTheory.Protocol.InformationModel.BehavioralPolicy.toMixedWithin_eq_map_pi
      (M := Protocol G) policy
        (Sites G n who) (fallback G who)).symm

/-- Conditional behavioral reading of a compact mixed-plan profile. -/
private def protocolBehavior {G : FiniteStageGame} {n : G.Horizon}
    (profile : ∀ who, Strategy G n who) :
    Profile (Protocol G).behavioralSignature :=
  fun who => GameTheory.Protocol.InformationModel.MixedPolicy.toBehavioral
    (M := Protocol G) (mixedPolicies profile who)

/-- Decode that Protocol profile to ordinary native public policies. -/
private def nativePublic {G : FiniteStageGame} {n : G.Horizon}
    (profile : ∀ who, Strategy G n who) :
    G.repeatedGame.toNative.PublicProfile PUnit.unit :=
  G.repeatedGame.toNative.ofBehaviorProfile PUnit.unit
    (protocolBehavior profile)

/-- Behavioral realization of a compact plan-law profile. -/
private def toBehavior {G : FiniteStageGame} {n : G.Horizon}
    (profile : ∀ who, Strategy G n who) : G.BehaviorProfile :=
  StochasticGame.NativeBridge.ofNativePublicProfile G.repeatedGame
    PUnit.unit (nativePublic profile)

/-- Compile a proof-view profile to the canonical Protocol presentation. -/
private def compiledBehavior {G : FiniteStageGame}
    (profile : G.BehaviorProfile) :
    Profile (Protocol G).behavioralSignature :=
  StochasticGame.NativeBridge.toNativeBehaviorProfile G.repeatedGame
    PUnit.unit profile

/-- Predraw a proof-view behavioral profile on all bounded sites. -/
private def fromBehavior {G : FiniteStageGame} {n : G.Horizon}
    (profile : G.BehaviorProfile) : ∀ who, Strategy G n who :=
  fun who => strategyOfPolicy who (compiledBehavior profile who)

private theorem mixedPolicies_fromBehavior {G : FiniteStageGame}
    {n : G.Horizon} (profile : G.BehaviorProfile) :
    mixedPolicies (fromBehavior (n := n) profile) =
      fun who => (compiledBehavior profile who).toMixedWithin
        (Sites G n who) (fallback G who) := by
  funext who
  exact mixedPolicy_strategyOfPolicy who (compiledBehavior profile who)

private theorem mixedPolicies_update {G : FiniteStageGame}
    {n : G.Horizon} (profile : ∀ who, Strategy G n who)
    (who : G.Player) (strategy : Strategy G n who) :
    mixedPolicies (Function.update profile who strategy) =
      Profile.update (mixedPolicies profile) who
        (FinDist.map (assemble G n who) (law strategy)) := by
  funext i
  unfold mixedPolicies
  by_cases hi : i = who
  · subst i
    simp
  · simp [Function.update_of_ne, Profile.update_of_ne, hi]

/-- Expected finite-horizon payoff of a canonical Protocol profile. -/
private def behaviorPayoff {G : FiniteStageGame} {n : G.Horizon}
    (profile : Profile (Protocol G).behavioralSignature)
    (observer : G.Player) : ℝ :=
  expectedUtility
    (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1) observer
    ((Protocol G).runBehavioral profile n.1)

private theorem compactPayoff_eq_behaviorPayoff {G : FiniteStageGame}
    {n : G.Horizon} (profile : ∀ who, Strategy G n who)
    (observer : G.Player) :
    compactPayoff profile observer =
      behaviorPayoff (n := n) (protocolBehavior profile) observer := by
  rw [compactPayoff_eq_runMixed]
  exact congrArg
    (expectedUtility
      (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1) observer)
    ((Protocol G).runMixed_toBehavioral
      (GameTheory.Protocol.InformationModel.constrainsAlike_of_perfectRecall
        (G.repeatedGame.toNative.perfectMonitoring_perfectRecall PUnit.unit))
      n.1 (mixedPolicies profile))

private theorem protocolBehavior_update {G : FiniteStageGame}
    {n : G.Horizon} (profile : ∀ who, Strategy G n who)
    (who : G.Player) (strategy : Strategy G n who) :
    protocolBehavior (Function.update profile who strategy) =
      Profile.update (protocolBehavior profile) who
        (GameTheory.Protocol.InformationModel.MixedPolicy.toBehavioral
          (M := Protocol G)
          (FinDist.map (assemble G n who) (law strategy))) := by
  funext i
  unfold protocolBehavior
  rw [mixedPolicies_update]
  by_cases hi : i = who
  · subst i
    simp
  · simp [Profile.update_of_ne, hi]

private theorem compactPayoff_update_strategyOfPolicy {G : FiniteStageGame}
    {n : G.Horizon} (profile : ∀ who, Strategy G n who)
    (who : G.Player) (deviation : (Protocol G).BehavioralPolicy who) :
    compactPayoff
        (Function.update profile who (strategyOfPolicy who deviation)) who =
      behaviorPayoff
        (n := n)
        (Profile.update (protocolBehavior profile) who deviation) who := by
  rw [compactPayoff_eq_runMixed, mixedPolicies_update,
    mixedPolicy_strategyOfPolicy]
  unfold behaviorPayoff
  exact congrArg
    (expectedUtility
      (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1) who)
    ((Protocol G).kuhn_mixed_update_toBehavioralWithin
      (G.repeatedGame.toNative.perfectMonitoring_perfectRecall PUnit.unit)
      (Sites G n) n.1
      (G.repeatedGame.toNative.boundedInformationSites_cover
        PUnit.unit n.1)
      (mixedPolicies profile) who deviation (fallback G who)).symm

private theorem compactNash_iff_protocolNash {G : FiniteStageGame}
    {n : G.Horizon} (profile : ∀ who, Strategy G n who) :
    (∀ who deviation,
      compactPayoff profile who ≥
        compactPayoff (Function.update profile who deviation) who) ↔
      G.repeatedGame.toNative.IsεHorizonNash PUnit.unit n.1 0
        (protocolBehavior profile) := by
  rw [G.repeatedGame.toNative.isεHorizonNash_iff]
  constructor
  · intro hcompact who deviation
    have hbound := hcompact who (strategyOfPolicy who deviation)
    rw [compactPayoff_eq_behaviorPayoff,
      compactPayoff_update_strategyOfPolicy] at hbound
    simpa [behaviorPayoff] using hbound
  · intro hbehavioral who deviation
    let behavioralDeviation :=
      GameTheory.Protocol.InformationModel.MixedPolicy.toBehavioral
        (M := Protocol G)
        (FinDist.map (assemble G n who) (law deviation))
    have hbound := hbehavioral who behavioralDeviation
    have hbase := compactPayoff_eq_behaviorPayoff profile who
    have hdeviation := compactPayoff_eq_behaviorPayoff
      (Function.update profile who deviation) who
    rw [protocolBehavior_update] at hdeviation
    rw [hbase, hdeviation]
    simpa [behaviorPayoff, behavioralDeviation] using hbound

private theorem nash_toBehavior_iff {G : FiniteStageGame}
    {n : G.Horizon} (profile : ∀ who, Strategy G n who) :
    (∀ who deviation,
      compactPayoff profile who ≥
        compactPayoff (Function.update profile who deviation) who) ↔
      G.repeatedGame.IsεHorizonNash PUnit.unit n.1 0
        (toBehavior profile) := by
  rw [compactNash_iff_protocolNash]
  have hprofile :
      G.repeatedGame.toNative.toBehaviorProfile PUnit.unit
          (nativePublic profile) = protocolBehavior profile := by
    unfold nativePublic
    exact G.repeatedGame.toNative.toBehaviorProfile_ofBehaviorProfile
      PUnit.unit (protocolBehavior profile)
  have hbridge :=
    StochasticGame.NativeBridge.isεHorizonNash_publicProfile_iff
      G.repeatedGame PUnit.unit n.1 0 (nativePublic profile)
  rw [hprofile] at hbridge
  exact hbridge

private theorem runMixed_fromBehavior_update_policy {G : FiniteStageGame}
    {n : G.Horizon} (profile : G.BehaviorProfile) (who : G.Player)
    (deviation : (Protocol G).BehavioralPolicy who) :
    (Protocol G).runMixed
        (mixedPolicies (Function.update (fromBehavior (n := n) profile) who
          (strategyOfPolicy who deviation))) n.1 =
      (Protocol G).runBehavioral
        (Profile.update (compiledBehavior profile) who deviation) n.1 := by
  rw [mixedPolicies_update, mixedPolicies_fromBehavior,
    mixedPolicy_strategyOfPolicy]
  let updatedBehavior :=
    Profile.update (compiledBehavior profile) who deviation
  let updatedFallback :=
    Profile.update (sig := (Protocol G).strategicSignature)
      (fallback G) who (fallback G who)
  have hpolicies :
      Profile.update (sig := (Protocol G).strategicSignature.mixed)
          (fun i => (compiledBehavior profile i).toMixedWithin
            (Sites G n i) (fallback G i)) who
          (deviation.toMixedWithin (Sites G n who) (fallback G who)) =
        fun i => (updatedBehavior i).toMixedWithin
          (Sites G n i) (updatedFallback i) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [updatedBehavior, updatedFallback]
    · simp [updatedBehavior, updatedFallback, Profile.update_of_ne, hi]
  rw [hpolicies]
  exact (Protocol G).runMixed_toMixedWithin
    (G.repeatedGame.toNative.perfectMonitoring_actsOnceWhereItMatters
      PUnit.unit)
    (Sites G n) updatedBehavior updatedFallback n.1
    (G.repeatedGame.toNative.boundedInformationSites_cover
      PUnit.unit n.1)

private theorem runMixed_fromBehavior_update_mixed {G : FiniteStageGame}
    {n : G.Horizon} (profile : G.BehaviorProfile) (who : G.Player)
    (replacement : (Protocol G).MixedPolicy who) :
    (Protocol G).runMixed
        (Profile.update (mixedPolicies (fromBehavior (n := n) profile))
          who replacement) n.1 =
      (Protocol G).runBehavioral
        (Profile.update (compiledBehavior profile) who
          (GameTheory.Protocol.InformationModel.MixedPolicy.toBehavioral
            (M := Protocol G) replacement)) n.1 := by
  rw [mixedPolicies_fromBehavior]
  exact (Protocol G).kuhn_behavioral_update_toMixedWithin
    (G.repeatedGame.toNative.perfectMonitoring_perfectRecall PUnit.unit)
    (Sites G n) n.1
    (G.repeatedGame.toNative.boundedInformationSites_cover
      PUnit.unit n.1)
    (compiledBehavior profile) (fallback G) who replacement

private theorem compactPayoff_fromBehavior_eq_behaviorPayoff
    {G : FiniteStageGame} {n : G.Horizon} (profile : G.BehaviorProfile)
    (observer : G.Player) :
    compactPayoff (fromBehavior (n := n) profile) observer =
      behaviorPayoff (n := n) (compiledBehavior profile) observer := by
  rw [compactPayoff_eq_runMixed, mixedPolicies_fromBehavior]
  unfold behaviorPayoff
  exact congrArg
    (expectedUtility
      (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1) observer)
    ((Protocol G).runMixed_toMixedWithin
      (G.repeatedGame.toNative.perfectMonitoring_actsOnceWhereItMatters
        PUnit.unit)
      (Sites G n) (compiledBehavior profile) (fallback G) n.1
      (G.repeatedGame.toNative.boundedInformationSites_cover
        PUnit.unit n.1))

private theorem compactPayoff_fromBehavior_update_policy
    {G : FiniteStageGame} {n : G.Horizon} (profile : G.BehaviorProfile)
    (who : G.Player) (deviation : (Protocol G).BehavioralPolicy who) :
    compactPayoff
        (Function.update (fromBehavior (n := n) profile) who
          (strategyOfPolicy who deviation)) who =
      behaviorPayoff (n := n)
        (Profile.update (compiledBehavior profile) who deviation) who := by
  rw [compactPayoff_eq_runMixed]
  unfold behaviorPayoff
  exact congrArg
    (expectedUtility
      (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1) who)
    (runMixed_fromBehavior_update_policy profile who deviation)

private theorem compactPayoff_fromBehavior_update_mixed
    {G : FiniteStageGame} {n : G.Horizon} (profile : G.BehaviorProfile)
    (who : G.Player) (deviation : Strategy G n who) :
    compactPayoff
        (Function.update (fromBehavior (n := n) profile) who deviation) who =
      behaviorPayoff (n := n)
        (Profile.update (compiledBehavior profile) who
          (GameTheory.Protocol.InformationModel.MixedPolicy.toBehavioral
            (M := Protocol G)
            (FinDist.map (assemble G n who) (law deviation)))) who := by
  rw [compactPayoff_eq_runMixed, mixedPolicies_update]
  unfold behaviorPayoff
  exact congrArg
    (expectedUtility
      (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1) who)
    (runMixed_fromBehavior_update_mixed profile who
      (FinDist.map (assemble G n who) (law deviation)))

private theorem compactNash_fromBehavior_iff_protocolNash
    {G : FiniteStageGame} {n : G.Horizon} (profile : G.BehaviorProfile) :
    (∀ who deviation,
      compactPayoff (fromBehavior (n := n) profile) who ≥
        compactPayoff
          (Function.update (fromBehavior (n := n) profile) who deviation)
          who) ↔
      G.repeatedGame.toNative.IsεHorizonNash PUnit.unit n.1 0
        (compiledBehavior profile) := by
  rw [G.repeatedGame.toNative.isεHorizonNash_iff]
  constructor
  · intro hcompact who deviation
    have hbound := hcompact who (strategyOfPolicy who deviation)
    rw [compactPayoff_fromBehavior_eq_behaviorPayoff,
      compactPayoff_fromBehavior_update_policy] at hbound
    simpa [behaviorPayoff] using hbound
  · intro hbehavioral who deviation
    let mixedDeviation :=
      FinDist.map (assemble G n who) (law deviation)
    have hbound := hbehavioral who
      (GameTheory.Protocol.InformationModel.MixedPolicy.toBehavioral
        (M := Protocol G) mixedDeviation)
    have hbase := compactPayoff_fromBehavior_eq_behaviorPayoff
      (n := n) profile who
    have hdeviation := compactPayoff_fromBehavior_update_mixed
      profile who deviation
    rw [hbase, hdeviation]
    simpa [behaviorPayoff, mixedDeviation] using hbound

private theorem nash_fromBehavior_iff {G : FiniteStageGame}
    {n : G.Horizon} (profile : G.BehaviorProfile) :
    (∀ who deviation,
      compactPayoff (fromBehavior (n := n) profile) who ≥
        compactPayoff
          (Function.update (fromBehavior (n := n) profile) who deviation)
          who) ↔
      G.repeatedGame.IsεHorizonNash PUnit.unit n.1 0 profile := by
  rw [compactNash_fromBehavior_iff_protocolNash]
  exact StochasticGame.NativeBridge.isεHorizonNash_toNative_iff
    G.repeatedGame PUnit.unit n.1 0 profile

private theorem payoff_toBehavior {G : FiniteStageGame} {n : G.Horizon}
    (profile : ∀ who, Strategy G n who) :
    G.finitePayoffOnHorizon n (toBehavior profile) =
      compactPayoff profile := by
  funext observer
  change G.repeatedGame.finiteAveragePayoff PUnit.unit n.1
      (toBehavior profile) observer = compactPayoff profile observer
  unfold toBehavior
  rw [← StochasticGame.NativeBridge.native_finiteAveragePayoff_eq_of_publicProfile
    G.repeatedGame PUnit.unit (nativePublic profile) n.1 observer]
  change expectedUtility
      (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1) observer
      ((Protocol G).runBehavioral
        (G.repeatedGame.toNative.toBehaviorProfile PUnit.unit
          (nativePublic profile)) n.1) = compactPayoff profile observer
  have hprofile :
      G.repeatedGame.toNative.toBehaviorProfile PUnit.unit
          (nativePublic profile) = protocolBehavior profile := by
    unfold nativePublic
    exact G.repeatedGame.toNative.toBehaviorProfile_ofBehaviorProfile
      PUnit.unit (protocolBehavior profile)
  have hbehavioral := (Protocol G).runMixed_toBehavioral
    (GameTheory.Protocol.InformationModel.constrainsAlike_of_perfectRecall
      (G.repeatedGame.toNative.perfectMonitoring_perfectRecall PUnit.unit))
    n.1 (mixedPolicies profile)
  calc
    _ = expectedUtility
        (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1) observer
        ((Protocol G).runBehavioral (protocolBehavior profile) n.1) :=
      congrArg
        (expectedUtility
          (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1) observer)
        (congrArg (fun policies =>
          (Protocol G).runBehavioral policies n.1) hprofile)
    _ = expectedUtility
        (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1) observer
        ((Protocol G).runMixed (mixedPolicies profile) n.1) :=
      congrArg
        (expectedUtility
          (G.repeatedGame.toNative.horizonUtility PUnit.unit n.1) observer)
        hbehavioral.symm
    _ = _ := (compactPayoff_eq_runMixed profile observer).symm

private theorem payoff_fromBehavior {G : FiniteStageGame} {n : G.Horizon}
    (profile : G.BehaviorProfile) :
    compactPayoff (fromBehavior (n := n) profile) =
      G.finitePayoffOnHorizon n profile := by
  funext observer
  rw [compactPayoff_eq_runMixed, mixedPolicies_fromBehavior]
  rw [(Protocol G).runMixed_toMixedWithin
    (G.repeatedGame.toNative.perfectMonitoring_actsOnceWhereItMatters
      PUnit.unit)
    (Sites G n) (compiledBehavior profile) (fallback G) n.1
    (G.repeatedGame.toNative.boundedInformationSites_cover
      PUnit.unit n.1)]
  exact StochasticGame.NativeBridge.native_finiteAveragePayoff_eq
    G.repeatedGame profile PUnit.unit n.1 observer

end FinitePresentation

abbrev FiniteCompactPresentation (G : FiniteStageGame) (n : G.Horizon) :=
  CompactRepeatedPresentation G (G.finitePayoffOnHorizon n)
    (fun profile =>
      G.repeatedGame.IsεHorizonNash PUnit.unit n.1 0 profile)

abbrev DiscountedCompactPresentation
    (G : FiniteStageGame) (lam : G.DiscountRate) :=
  CompactRepeatedPresentation G (G.discountedPayoffOnRate lam)
    (fun profile =>
      G.repeatedGame.IsDiscountedεNash
        (1 - lam.1) PUnit.unit 0 profile)

/-! These two declarations are the reduction itself.  At a finite horizon the
carrier is the simplex of laws on bounded contingent plans, and bounded Kuhn
gives the required behavioral transports.  The discounted construction still
requires a single probability law on total pure policies, rather than one
finite predraw for each horizon.  Neither declaration assumes a Nash profile
exists. -/
theorem finiteCompactPresentation_exists (G : FiniteStageGame)
    (n : G.Horizon) : Nonempty (FiniteCompactPresentation G n) := by
  exact ⟨{
    Strategy := fun who => FinitePresentation.Strategy G n who
    mix := FinitePresentation.mix
    mixContinuous := FinitePresentation.mix_continuous
    mix_zero := FinitePresentation.mix_zero
    mix_one := FinitePresentation.mix_one
    compactPayoff := FinitePresentation.compactPayoff
    compactPayoffContinuous := FinitePresentation.compactPayoff_continuous
    compactPayoffAffine := FinitePresentation.compactPayoff_affine
    barycenter := FinitePresentation.barycenter
    barycenterContinuous := FinitePresentation.barycenter_continuous
    compactPayoffBarycentric :=
      FinitePresentation.compactPayoff_barycentric
    toBehavior := FinitePresentation.toBehavior
    fromBehavior := FinitePresentation.fromBehavior
    payoff_toBehavior := FinitePresentation.payoff_toBehavior
    payoff_fromBehavior := FinitePresentation.payoff_fromBehavior
    nash_toBehavior_iff := FinitePresentation.nash_toBehavior_iff
    nash_fromBehavior_iff := FinitePresentation.nash_fromBehavior_iff
  }⟩

theorem discountedCompactPresentation_exists (G : FiniteStageGame)
    (lam : G.DiscountRate) :
    Nonempty (DiscountedCompactPresentation G lam) := by
  sorry

theorem finiteCompactPresentation_feasiblePayoffs_eq
    {G : FiniteStageGame} {n : G.Horizon}
    (presentation : FiniteCompactPresentation G n) :
    presentation.toCompactContinuousGame.feasiblePayoffs =
      G.finiteFeasiblePayoffsOnHorizon n :=
  CompactRepeatedPresentation.feasiblePayoffs_eq presentation

theorem finiteCompactPresentation_equilibriumPayoffs_eq
    {G : FiniteStageGame} {n : G.Horizon}
    (presentation : FiniteCompactPresentation G n) :
    presentation.toCompactContinuousGame.equilibriumPayoffs =
      G.finiteEquilibriumPayoffsOnHorizon n :=
  CompactRepeatedPresentation.equilibriumPayoffs_eq presentation

theorem discountedCompactPresentation_feasiblePayoffs_eq
    {G : FiniteStageGame} {lam : G.DiscountRate}
    (presentation : DiscountedCompactPresentation G lam) :
    presentation.toCompactContinuousGame.feasiblePayoffs =
      G.discountedFeasiblePayoffsOnRate lam :=
  CompactRepeatedPresentation.feasiblePayoffs_eq presentation

theorem discountedCompactPresentation_equilibriumPayoffs_eq
    {G : FiniteStageGame} {lam : G.DiscountRate}
    (presentation : DiscountedCompactPresentation G lam) :
    presentation.toCompactContinuousGame.equilibriumPayoffs =
      G.discountedEquilibriumPayoffsOnRate lam :=
  CompactRepeatedPresentation.equilibriumPayoffs_eq presentation

/-- Property (1): the continuous payoff image of the compact product strategy
space is nonempty and compact; binary mixing supplies paths. -/
theorem property_1 (G : CompactContinuousGame) :
    G.feasiblePayoffs.Nonempty ∧
      PathConnectedSet G.feasiblePayoffs ∧ IsCompact G.feasiblePayoffs := by
  have hpayoff : Continuous G.payoff :=
    continuous_pi G.payoffContinuous
  constructor
  · exact Set.range_nonempty G.payoff
  constructor
  · constructor
    · exact Set.range_nonempty G.payoff
    · rintro _ ⟨profileX, rfl⟩ _ ⟨profileY, rfl⟩
      let path : ℝ → Payoff G.Player := fun t =>
        G.payoff (fun i => G.mix i t (profileY i) (profileX i))
      have hprofile : Continuous fun t : ℝ =>
          (fun i => G.mix i t (profileY i) (profileX i)) := by
        apply continuous_pi
        intro i
        exact (G.mixContinuous i).comp
          (continuous_id.prodMk (continuous_const.prodMk continuous_const))
      refine ⟨path, hpayoff.comp hprofile, ?_, ?_, ?_⟩
      · change G.payoff (fun i => G.mix i 0 (profileY i) (profileX i)) =
          G.payoff profileX
        congr 1
        funext i
        exact G.mix_zero i (profileY i) (profileX i)
      · change G.payoff (fun i => G.mix i 1 (profileY i) (profileX i)) =
          G.payoff profileY
        congr 1
        funext i
        exact G.mix_one i (profileY i) (profileX i)
      · intro t _
        exact ⟨fun i => G.mix i t (profileY i) (profileX i), rfl⟩
  · simpa [CompactContinuousGame.feasiblePayoffs] using
      isCompact_univ.image_of_continuousOn hpayoff.continuousOn

/-- Property (2): Nash payoffs are nonempty and compact. -/
theorem property_2 (G : CompactContinuousGame) :
    G.equilibriumPayoffs.Nonempty ∧ IsCompact G.equilibriumPayoffs := by
  exact G.toCompactBarycentricGame.equilibriumPayoffs_nonempty_and_compact

/-! Properties (1) and (2) for `Gₙ` and `G_λ` now genuinely factor
through the compact-game abstraction above.  No separate nonemptiness
assumption is inserted: Nash existence is supplied only by Property (2). -/
theorem property_1_finite (G : FiniteStageGame) (n : G.Horizon) :
    (G.finiteFeasiblePayoffsOnHorizon n).Nonempty ∧
      PathConnectedSet (G.finiteFeasiblePayoffsOnHorizon n) ∧
        IsCompact (G.finiteFeasiblePayoffsOnHorizon n) := by
  obtain ⟨presentation⟩ := finiteCompactPresentation_exists G n
  rw [← finiteCompactPresentation_feasiblePayoffs_eq presentation]
  exact property_1 presentation.toCompactContinuousGame

theorem property_1_discounted
    (G : FiniteStageGame) (lam : G.DiscountRate) :
    (G.discountedFeasiblePayoffsOnRate lam).Nonempty ∧
      PathConnectedSet (G.discountedFeasiblePayoffsOnRate lam) ∧
        IsCompact (G.discountedFeasiblePayoffsOnRate lam) := by
  obtain ⟨presentation⟩ := discountedCompactPresentation_exists G lam
  rw [← discountedCompactPresentation_feasiblePayoffs_eq presentation]
  exact property_1 presentation.toCompactContinuousGame

theorem property_2_finite (G : FiniteStageGame) (n : G.Horizon) :
    (G.finiteEquilibriumPayoffsOnHorizon n).Nonempty ∧
      IsCompact (G.finiteEquilibriumPayoffsOnHorizon n) := by
  obtain ⟨presentation⟩ := finiteCompactPresentation_exists G n
  rw [← finiteCompactPresentation_equilibriumPayoffs_eq presentation]
  exact property_2 presentation.toCompactContinuousGame

theorem property_2_discounted
    (G : FiniteStageGame) (lam : G.DiscountRate) :
    (G.discountedEquilibriumPayoffsOnRate lam).Nonempty ∧
      IsCompact (G.discountedEquilibriumPayoffsOnRate lam) := by
  obtain ⟨presentation⟩ := discountedCompactPresentation_exists G lam
  rw [← discountedCompactPresentation_equilibriumPayoffs_eq presentation]
  exact property_2 presentation.toCompactContinuousGame

/-! The asymptotic feasible-payoff statements use block approximation and the
Banach-limit identification.  The corresponding general repeated-game theorem
has not been formalized in the repository. -/
theorem property_3 (G : FiniteStageGame) (L : BanachLimit) :
    HausdorffConvergesAtTop G.finiteFeasiblePayoffs
        G.correlatedFeasiblePayoffs ∧
      HausdorffConvergesAtZero G.discountedFeasiblePayoffs
        G.correlatedFeasiblePayoffs ∧
      G.banachFeasiblePayoffs L = G.correlatedFeasiblePayoffs := by
  sorry

/-! The Banach-limit Folk theorem is the unconditional second clause of
Property (4).  It is not available in the current library. -/
theorem property_4_banach (G : FiniteStageGame) (L : BanachLimit) :
    G.banachEquilibriumPayoffs L = G.individuallyRationalPayoffs := by
  sorry

/-! The vanishing-discount clause of Property (4), equivalently Lemma 2, is
stated with the paper's added-in-proof correction: `Δ` must be full
dimensional or there must be two players. -/
theorem property_4_discounted (G : FiniteStageGame)
    (hregular : FullDimensional G.individuallyRationalPayoffs ∨
      Fintype.card G.Player = 2) :
    HausdorffConvergesAtZero G.discountedEquilibriumPayoffs
      G.individuallyRationalPayoffs := by
  sorry

/-! ## 2. Study of `Gₙ` and `G_λ` -/

/-- Scalar multiplication of a payoff set. -/
def scaleSet {ι : Type} (c : ℝ) (A : Set (Payoff ι)) : Set (Payoff ι) :=
  {z | ∃ x ∈ A, z = c • x}

/-- Minkowski sum of two payoff sets. -/
def addSet {ι : Type} (A B : Set (Payoff ι)) : Set (Payoff ι) :=
  {z | ∃ x ∈ A, ∃ y ∈ B, z = x + y}

/-- `m * A` in the paper: the Minkowski sum of `m` copies of `A`. -/
def iteratedAddSet {ι : Type} (m : ℕ) (A : Set (Payoff ι)) :
    Set (Payoff ι) :=
  {z | ∃ x : Fin m → Payoff ι, (∀ k, x k ∈ A) ∧ z = ∑ k, x k}

/-! **Lemma 1(5), first inclusion.**  Pure stage profiles embed as
Dirac mixed profiles. -/
theorem lemma_1_pure_subset_D1 (G : FiniteStageGame) :
    G.purePayoffSet ⊆ G.oneStageFeasiblePayoffs := by
  rintro payoff ⟨profile, rfl⟩
  refine ⟨G.kernel.pureMixedProfile profile, ?_⟩
  change G.kernel.mixedExtension.payoffVector
      (G.kernel.pureMixedProfile profile) = G.payoff profile
  rw [G.kernel.mixedExtension_payoffVector_pureMixedProfile profile]
  funext who
  change G.kernel.eu profile who = G.payoff profile who
  simpa [FiniteStageGame.kernel] using
    (KernelGame.eu_ofPureEU G.Action G.payoff profile who)

/-! **Lemma 1(5), finite-horizon clause.**  Stationary repetition of a
mixed one-stage profile gives the same payoff at every positive horizon.
The exact public-history embedding is not yet packaged for this adapter. -/
theorem lemma_1_D1_subset_Dn (G : FiniteStageGame)
    (n : G.Horizon) :
    G.oneStageFeasiblePayoffs ⊆
      G.finiteFeasiblePayoffsOnHorizon n := by
  sorry

/-! **Lemma 1(5), discounted clause.**  The same stationary profile has
its one-stage payoff under every paper discount rate. -/
theorem lemma_1_D1_subset_Dlambda (G : FiniteStageGame)
    (lam : G.DiscountRate) :
    G.oneStageFeasiblePayoffs ⊆
      G.discountedFeasiblePayoffsOnRate lam := by
  sorry

/-! **Lemma 1(6), finite-horizon clause.**  Every expected average is a
barycenter of pure stage-payoff vectors.  A reusable convex-hull theorem
for the public-history adapter is the missing formal ingredient. -/
theorem lemma_1_Dn_subset_C (G : FiniteStageGame)
    (n : G.Horizon) :
    G.finiteFeasiblePayoffsOnHorizon n ⊆
      G.correlatedFeasiblePayoffs := by
  sorry

/-! **Lemma 1(6), discounted clause.**  The geometric weighted average
is likewise a barycenter of pure stage-payoff vectors. -/
theorem lemma_1_Dlambda_subset_C (G : FiniteStageGame)
    (lam : G.DiscountRate) :
    G.discountedFeasiblePayoffsOnRate lam ⊆
      G.correlatedFeasiblePayoffs := by
  sorry

/-- A convex set squeezed between `pure` and its convex hull is exactly
that convex hull. -/
theorem convex_eq_convexHull_iff_of_subset
    {V : Type} [AddCommGroup V] [Module ℝ V]
    {pure feasible : Set V}
    (hpure : pure ⊆ feasible)
    (hfeasible : feasible ⊆ convexHull ℝ pure) :
    Convex ℝ feasible ↔ feasible = convexHull ℝ pure := by
  constructor
  · intro hconvex
    apply Set.Subset.antisymm hfeasible
    exact convexHull_min hpure hconvex
  · rintro rfl
    exact convex_convexHull ℝ pure

/-! **Lemma 1(7), finite-horizon clause.**  This is now derived from
(5) and (6), rather than left as another paper-level gap. -/
theorem lemma_1_Dn_convex_iff (G : FiniteStageGame)
    (n : G.Horizon) :
    Convex ℝ (G.finiteFeasiblePayoffsOnHorizon n) ↔
      G.finiteFeasiblePayoffsOnHorizon n =
        G.correlatedFeasiblePayoffs := by
  apply convex_eq_convexHull_iff_of_subset
  · exact (lemma_1_pure_subset_D1 G).trans
      (lemma_1_D1_subset_Dn G n)
  · exact lemma_1_Dn_subset_C G n

/-! **Lemma 1(7), discounted clause.** -/
theorem lemma_1_Dlambda_convex_iff (G : FiniteStageGame)
    (lam : G.DiscountRate) :
    Convex ℝ (G.discountedFeasiblePayoffsOnRate lam) ↔
      G.discountedFeasiblePayoffsOnRate lam =
        G.correlatedFeasiblePayoffs := by
  apply convex_eq_convexHull_iff_of_subset
  · exact (lemma_1_pure_subset_D1 G).trans
      (lemma_1_D1_subset_Dlambda G lam)
  · exact lemma_1_Dlambda_subset_C G lam

/-! **Lemma 1(8), first finite inclusion.**  Stationary repetition of a
one-stage Nash profile resists arbitrary history-dependent deviations.
The library has the corresponding monitored theorem, but the exact
bridge from the kernel mixed extension to this stochastic adapter is not
yet exposed at this evaluator. -/
theorem lemma_1_E1_subset_En (G : FiniteStageGame)
    (n : G.Horizon) :
    G.oneStageEquilibriumPayoffs ⊆
      G.finiteEquilibriumPayoffsOnHorizon n := by
  sorry

/-! **Lemma 1(8), discounted inclusion.** -/
theorem lemma_1_E1_subset_Elambda (G : FiniteStageGame)
    (lam : G.DiscountRate) :
    G.oneStageEquilibriumPayoffs ⊆
      G.discountedEquilibriumPayoffsOnRate lam := by
  sorry

/-! **Lemma 1(8), finite individual-rationality clause.**  At every
public history a player can switch to a stagewise security strategy;
the conditional-history construction is not yet packaged. -/
theorem lemma_1_En_subset_Delta (G : FiniteStageGame)
    (n : G.Horizon) :
    G.finiteEquilibriumPayoffsOnHorizon n ⊆
      G.individuallyRationalPayoffs := by
  sorry

/-! **Lemma 1(8), discounted individual-rationality clause.** -/
theorem lemma_1_Elambda_subset_Delta (G : FiniteStageGame)
    (lam : G.DiscountRate) :
    G.discountedEquilibriumPayoffsOnRate lam ⊆
      G.individuallyRationalPayoffs := by
  sorry

/-- Aggregate finite/discounted form of Lemma 1(5)--(7).  The positive
horizon/rate witnesses prevent the zero-horizon collapse present in the
earlier branch. -/
theorem lemma_1_feasible (G : FiniteStageGame)
    (evaluation : Set (Payoff G.Player))
    (hevaluation :
      (∃ n : G.Horizon,
        evaluation = G.finiteFeasiblePayoffsOnHorizon n) ∨
      (∃ lam : G.DiscountRate,
        evaluation = G.discountedFeasiblePayoffsOnRate lam)) :
    G.purePayoffSet ⊆ G.oneStageFeasiblePayoffs ∧
      G.oneStageFeasiblePayoffs ⊆ evaluation ∧
      evaluation ⊆ G.correlatedFeasiblePayoffs ∧
      (Convex ℝ evaluation ↔
        evaluation = G.correlatedFeasiblePayoffs) := by
  rcases hevaluation with ⟨n, rfl⟩ | ⟨lam, rfl⟩
  · exact ⟨lemma_1_pure_subset_D1 G,
      lemma_1_D1_subset_Dn G n,
      lemma_1_Dn_subset_C G n,
      lemma_1_Dn_convex_iff G n⟩
  · exact ⟨lemma_1_pure_subset_D1 G,
      lemma_1_D1_subset_Dlambda G lam,
      lemma_1_Dlambda_subset_C G lam,
      lemma_1_Dlambda_convex_iff G lam⟩

/-- Aggregate finite/discounted form of Lemma 1(8), delegated to its
four source clauses. -/
theorem lemma_1_equilibrium (G : FiniteStageGame)
    (evaluation : Set (Payoff G.Player))
    (hevaluation :
      (∃ n : G.Horizon,
        evaluation = G.finiteEquilibriumPayoffsOnHorizon n) ∨
      (∃ lam : G.DiscountRate,
        evaluation = G.discountedEquilibriumPayoffsOnRate lam)) :
    G.oneStageEquilibriumPayoffs ⊆ evaluation ∧
      evaluation ⊆ G.individuallyRationalPayoffs := by
  rcases hevaluation with ⟨n, rfl⟩ | ⟨lam, rfl⟩
  · exact ⟨lemma_1_E1_subset_En G n,
      lemma_1_En_subset_Delta G n⟩
  · exact ⟨lemma_1_E1_subset_Elambda G lam,
      lemma_1_Elambda_subset_Delta G lam⟩

/-! Lemma 2 is precisely Property (4)'s vanishing-discount assertion.  The
paper's printed unrestricted statement is withdrawn by its added-in-proof
note, so no unrestricted theorem is declared. -/
theorem lemma_2 (G : FiniteStageGame)
    (hregular : FullDimensional G.individuallyRationalPayoffs ∨
      Fintype.card G.Player = 2) :
    HausdorffConvergesAtZero G.discountedEquilibriumPayoffs
      G.individuallyRationalPayoffs :=
  property_4_discounted G hregular

/-- Public monitored profiles for the realized-action presentation of the
finite stage game. -/
abbrev FiniteStageGame.StandardMonitoredProfile (G : FiniteStageGame) :=
  G.kernel.realizedActionMonitoring.MonitoredProfile

/-- A single player's public monitored strategy. -/
abbrev FiniteStageGame.StandardMonitoredStrategy
    (G : FiniteStageGame) (who : G.Player) :=
  G.kernel.realizedActionMonitoring.MonitoredStrategy who

/-- Discounted payoff of a monitored profile, transported through the
exact realized-action/stochastic profile equivalence. -/
noncomputable def FiniteStageGame.monitoredDiscountedPayoff
    (G : FiniteStageGame) (lam : ℝ)
    (profile : G.StandardMonitoredProfile) : Payoff G.Player :=
  G.discountedPayoff lam
    (GameTheory.KernelGame.RealizedActionRepeatedAdapter.toBehaviorProfile
      G.kernel profile)

/-- Discounted Nash equilibrium among public strategies. -/
def FiniteStageGame.IsMonitoredDiscountedNash
    (G : FiniteStageGame) (lam : ℝ)
    (profile : G.StandardMonitoredProfile) : Prop :=
  ∀ who (deviation : G.StandardMonitoredStrategy who),
    G.monitoredDiscountedPayoff lam
        (Function.update profile who deviation) who ≤
      G.monitoredDiscountedPayoff lam profile who

/-- Perfect public equilibrium: discounted Nash after every finite
public action history, including zero-probability histories. -/
def FiniteStageGame.IsPerfectPublicEquilibrium
    (G : FiniteStageGame) (lam : ℝ)
    (profile : G.StandardMonitoredProfile) : Prop :=
  ∀ t (history : G.kernel.realizedActionMonitoring.SignalHistory t),
    G.IsMonitoredDiscountedNash lam
      (G.kernel.realizedActionMonitoring.after profile history)

/-- Perfect-public-equilibrium payoff set at discount `lam`. -/
def FiniteStageGame.perfectPublicEquilibriumPayoffs
    (G : FiniteStageGame) (lam : ℝ) : Set (Payoff G.Player) :=
  {v | ∃ profile : G.StandardMonitoredProfile,
    G.IsPerfectPublicEquilibrium lam profile ∧
      G.monitoredDiscountedPayoff lam profile = v}

/-! Immediately after Lemma 2 the paper states that its convergence
result does not extend to perfect equilibria and cites Fudenberg--Maskin
[5].  The counterexample is not printed in this paper, so the exact
external existence claim remains an explained `sorry`; it is not
silently omitted or replaced by a weaker comment. -/
theorem reported_perfect_equilibrium_failure :
    ∃ G : FiniteStageGame,
      ¬HausdorffConvergesAtZero
        G.perfectPublicEquilibriumPayoffs
        G.individuallyRationalPayoffs := by
  sorry

/-! Lemma 3 is block concatenation.  The repository adapter has profile
transport but no theorem assembling arbitrary finite-horizon equilibrium
blocks while preserving all continuation incentives. -/
theorem lemma_3_feasible (G : FiniteStageGame)
    (n m p r : ℕ) (hn : n = m * p + r) :
    addSet (iteratedAddSet m (scaleSet (p : ℝ) (G.finiteFeasiblePayoffs p)))
        (scaleSet (r : ℝ) (G.finiteFeasiblePayoffs r)) ⊆
      scaleSet (n : ℝ) (G.finiteFeasiblePayoffs n) := by
  sorry

/-! Equilibrium-block concatenation is the strategic clause of Lemma 3. -/
theorem lemma_3_equilibrium (G : FiniteStageGame)
    (n m p r : ℕ) (hn : n = m * p + r) :
    addSet (iteratedAddSet m (scaleSet (p : ℝ) (G.finiteEquilibriumPayoffs p)))
        (scaleSet (r : ℝ) (G.finiteEquilibriumPayoffs r)) ⊆
      scaleSet (n : ℝ) (G.finiteEquilibriumPayoffs n) := by
  sorry

/-! Immediately after Lemma 3 the paper records the equal-block consequences
`Dₙ ⊆ Dₖₙ` and `Eₙ ⊆ Eₖₙ`.  Their proofs use the same monitored-profile
concatenation interface as Lemma 3. -/
theorem lemma_3_D_subset_multiple (G : FiniteStageGame)
    (n : G.Horizon) {k : ℕ} (hk : 0 < k) :
    G.finiteFeasiblePayoffsOnHorizon n ⊆
      G.finiteFeasiblePayoffs (k * n.1) := by
  sorry

theorem lemma_3_E_subset_multiple (G : FiniteStageGame)
    (n : G.Horizon) {k : ℕ} (hk : 0 < k) :
    G.finiteEquilibriumPayoffsOnHorizon n ⊆
      G.finiteEquilibriumPayoffs (k * n.1) := by
  sorry

/-! The paper then notes that a reverse inclusion for one multiplier `k > 1`
forces convexity of the corresponding finite-horizon payoff set.  The closure
under equal-weight block averages and compactness argument is not yet packaged. -/
theorem post_lemma_3_D_convex_of_reverse_multiple
    (G : FiniteStageGame) (n : G.Horizon) {k : ℕ} (hk : 1 < k)
    (hreverse : G.finiteFeasiblePayoffs (k * n.1) ⊆
      G.finiteFeasiblePayoffsOnHorizon n) :
    Convex ℝ (G.finiteFeasiblePayoffsOnHorizon n) := by
  sorry

theorem post_lemma_3_E_convex_of_reverse_multiple
    (G : FiniteStageGame) (n : G.Horizon) {k : ℕ} (hk : 1 < k)
    (hreverse : G.finiteEquilibriumPayoffs (k * n.1) ⊆
      G.finiteEquilibriumPayoffsOnHorizon n) :
    Convex ℝ (G.finiteEquilibriumPayoffsOnHorizon n) := by
  sorry

/-! ## Examples 1--6 -/

/-- Two-player payoff vector. -/
def pair (x y : ℝ) : Payoff Bool
  | false => x
  | true => y

@[simp] theorem pair_false (x y : ℝ) : pair x y false = x := rfl
@[simp] theorem pair_true (x y : ℝ) : pair x y true = y := rfl

/-- `false` is Top/Left and `true` is Bottom/Right. -/
def binaryPayoff (topLeft topRight bottomLeft bottomRight : Payoff Bool)
    (action : ∀ _ : Bool, Bool) : Payoff Bool :=
  match action false, action true with
  | false, false => topLeft
  | false, true => topRight
  | true, false => bottomLeft
  | true, true => bottomRight

/-- A two-player, two-action game from four payoff vectors. -/
def binaryGame (topLeft topRight bottomLeft bottomRight : Payoff Bool) :
    FiniteStageGame where
  Player := Bool
  Action := fun _ => Bool
  payoff := binaryPayoff topLeft topRight bottomLeft bottomRight

/-- Example 1. -/
def example1 : FiniteStageGame :=
  binaryGame (pair 1 0) (pair 0 0) (pair 0 0) (pair 0 1)

/-- Example 2. -/
def example2 : FiniteStageGame :=
  binaryGame (pair 1 0) (pair 2 2) (pair 0 0) (pair 0 1)

/-- Example 3. -/
def example3 : FiniteStageGame :=
  binaryGame (pair 1 0) (pair 1 1) (pair 0 0) (pair 1 0)

/-- Example 4, parameterized by the paper's positive integer `m`. -/
def example4 (m : ℕ) : FiniteStageGame :=
  binaryGame (pair m 0) (pair (m + 1) (m + 1))
    (pair 0 0) (pair 0 m)

/-- Example 5: payoff `e_j` when every player announces `j`, and zero
otherwise. -/
def example5 (N : ℕ) [NeZero N] : FiniteStageGame where
  Player := Fin N
  Action := fun _ => Fin N
  payoff := fun action who =>
    if _h : ∀ i, action i = action who then
      if action who = who then 1 else 0
    else 0

/-- Example 6.  Player `false` has two rows and player `true` has four
columns. -/
inductive FourColumn
  | c0 | c1 | c2 | c3
  deriving DecidableEq, Fintype

/-- Action spaces of Example 6. -/
def Example6Action : Bool → Type
  | false => Bool
  | true => FourColumn

instance example6ActionFintype : ∀ who, Fintype (Example6Action who)
  | false => inferInstanceAs (Fintype Bool)
  | true => inferInstanceAs (Fintype FourColumn)

instance example6ActionDecidableEq : ∀ who, DecidableEq (Example6Action who)
  | false => inferInstanceAs (DecidableEq Bool)
  | true => inferInstanceAs (DecidableEq FourColumn)

instance example6ActionNonempty : ∀ who, Nonempty (Example6Action who)
  | false => ⟨false⟩
  | true => ⟨FourColumn.c0⟩

/-- Payoff table of Example 6. -/
def example6Payoff (action : ∀ who, Example6Action who) : Payoff Bool :=
  let row := action false
  let column := action true
  match row, column with
  | false, FourColumn.c0 => pair 0 1
  | false, FourColumn.c1 => pair 1 1
  | false, FourColumn.c2 => pair 2 0
  | false, FourColumn.c3 => pair 3 0
  | true, FourColumn.c0 => pair 0 0
  | true, FourColumn.c1 => pair 1 0
  | true, FourColumn.c2 => pair 2 1
  | true, FourColumn.c3 => pair 3 1

/-- Example 6. -/
def example6 : FiniteStageGame where
  Player := Bool
  Action := Example6Action
  payoff := example6Payoff

/-! The following finite examples require explicit public-history profile
calculations and universal deviation bounds.  They are stated in the paper's
order; no weaker static surrogate is substituted. -/

theorem example1_half_mem_E2 :
    pair (1 / 2) (1 / 2) ∈ example1.finiteEquilibriumPayoffs 2 := by
  sorry

theorem example1_half_not_mem_D3 :
    pair (1 / 2) (1 / 2) ∉ example1.finiteFeasiblePayoffs 3 := by
  sorry

/-- The same payoff is not feasible in one stage. -/
theorem example1_half_not_mem_D1 :
    pair (1 / 2) (1 / 2) ∉ example1.oneStageFeasiblePayoffs := by
  sorry

/-! The paper also notes that no positive finite horizon convexifies Example 1.
Its Pareto-boundary argument requires a reusable characterization of equality
in the convex-hull bound, which is not yet available for the monitored
adapter. -/
theorem example1_no_finite_convexification (n : example1.Horizon) :
    example1.finiteFeasiblePayoffsOnHorizon n ≠
      example1.correlatedFeasiblePayoffs := by
  sorry

/-- Equation (11): neither `Dₙ` nor `Eₙ` is monotone in general.
The paper's Example 1 witnesses both failures for the same positive horizon. -/
theorem equation_11 :
    ∃ G : FiniteStageGame, ∃ n : G.Horizon,
      (¬G.finiteFeasiblePayoffsOnHorizon n ⊆
        G.finiteFeasiblePayoffs (n.1 + 1)) ∧
      (¬G.finiteEquilibriumPayoffsOnHorizon n ⊆
        G.finiteEquilibriumPayoffs (n.1 + 1)) := by
  sorry

theorem example2_D1_eq_C :
    example2.oneStageFeasiblePayoffs = example2.correlatedFeasiblePayoffs := by
  sorry

theorem example2_E1_eq_singleton :
    example2.oneStageEquilibriumPayoffs = {pair 2 2} := by
  sorry

theorem example2_one_one_mem_E2 :
    pair 1 1 ∈ example2.finiteEquilibriumPayoffs 2 := by
  sorry

/-- Equation (12), with the paper's positive-horizon domain explicit. -/
theorem equation_12 :
    ∃ G : FiniteStageGame, ∃ n : G.Horizon,
      G.finiteFeasiblePayoffsOnHorizon n =
          G.finiteFeasiblePayoffs (n.1 + 1) ∧
        G.finiteEquilibriumPayoffsOnHorizon n ≠
          G.finiteEquilibriumPayoffs (n.1 + 1) := by
  sorry

theorem example3_En : ∀ n, 0 < n →
    example3.finiteEquilibriumPayoffs n =
      {v | v false = 1 ∧ 0 ≤ v true ∧ v true ≤ 1} := by
  sorry

theorem example3_half_mem_D2_not_D1 :
    pair (1 / 2) (1 / 2) ∈ example3.finiteFeasiblePayoffs 2 ∧
      pair (1 / 2) (1 / 2) ∉ example3.oneStageFeasiblePayoffs := by
  sorry

/-- Equation (13), with the paper's positive-horizon domain explicit. -/
theorem equation_13 :
    ∃ G : FiniteStageGame, ∃ n : G.Horizon,
      G.finiteEquilibriumPayoffsOnHorizon n =
          G.finiteEquilibriumPayoffs (n.1 + 1) ∧
        G.finiteFeasiblePayoffsOnHorizon n ≠
          G.finiteFeasiblePayoffs (n.1 + 1) := by
  sorry

/-- Equation (14), at a positive finite horizon. -/
theorem equation_14 :
    ∃ G : FiniteStageGame, ∃ n : G.Horizon,
      ¬G.finiteEquilibriumPayoffsOnHorizon n ⊆
        convexHull ℝ G.oneStageEquilibriumPayoffs := by
  sorry

/-- Example 4 and Equation (15). -/
theorem example4_equilibrium_pattern (m : ℕ) (hm : 0 < m) :
    (∀ n, 0 < n → n < m →
      (example4 m).finiteEquilibriumPayoffs n =
        {pair (m + 1) (m + 1)}) ∧
      pair m m ∈ (example4 m).finiteEquilibriumPayoffs (m + 1) := by
  sorry

/-- Equation (15): one decreasing step at a positive horizon does not
force the next one. -/
theorem equation_15 :
    ∃ G : FiniteStageGame, ∃ n : G.Horizon,
      G.finiteEquilibriumPayoffs (n.1 + 1) ⊆
          G.finiteEquilibriumPayoffsOnHorizon n ∧
        ¬G.finiteEquilibriumPayoffs (n.1 + 2) ⊆
          G.finiteEquilibriumPayoffsOnHorizon n := by
  sorry

/-! **Example 1 revisited, page 150.**  The paper's `λ` is
the current-stage weight: playing `(1,0)` once and `(0,1)` forever
afterwards gives `(λ,1-λ)`.  Thus the displayed payoff belongs to
`E_{7/8}`, not `E_{1/8}`. -/
theorem example1_discounted_nonmonotone :
    pair (7 / 8) (1 / 8) ∈
        example1.discountedEquilibriumPayoffs (7 / 8) ∧
      pair (7 / 8) (1 / 8) ∉ example1.oneStageFeasiblePayoffs ∧
      pair (7 / 8) (1 / 8) ∉
        example1.discountedFeasiblePayoffs (3 / 4) := by
  sorry

/-- Equation (16): the discounted feasible and equilibrium nets need not be
monotone.  Example 1 revisited uses `δ = 3/4 < λ = 7/8` and supplies a
payoff in the larger-rate set that is absent from the smaller-rate set; the
inclusion direction below follows that printed witness. -/
theorem equation_16 :
    ∃ G : FiniteStageGame, ∃ δ lam : G.DiscountRate,
      δ.1 < lam.1 ∧
        (¬G.discountedFeasiblePayoffsOnRate lam ⊆
          G.discountedFeasiblePayoffsOnRate δ) ∧
        (¬G.discountedEquilibriumPayoffsOnRate lam ⊆
          G.discountedEquilibriumPayoffsOnRate δ) := by
  sorry

/-! Proposition 4 uses Fenchel's theorem that a point in the convex hull of a
connected subset of `ℝᴺ` needs at most `N` terms, followed by an infinite
geometric schedule.  That connected-Carathéodory theorem is not available in
the current dependencies. -/
theorem proposition_4 (G : FiniteStageGame) (lam : ℝ)
    (hlam : 0 < lam) (hbound : lam < 1 / (Fintype.card G.Player : ℝ)) :
    G.discountedFeasiblePayoffs lam = G.correlatedFeasiblePayoffs := by
  sorry

/-! Example 5 proves the constant `1/N` sharp. -/
theorem example5_sharp (N : ℕ) [NeZero N] (lam : ℝ)
    (hlam : 1 / (N : ℝ) < lam) :
    (fun _ : Fin N => 1 / (N : ℝ)) ∉
      (example5 N).discountedFeasiblePayoffs lam := by
  sorry

/-! Proposition 5 is a finite-horizon splice using convexity of `Dₙ`. -/
theorem proposition_5 (G : FiniteStageGame) (n : ℕ) (hn : 0 < n)
    (hconvex : Convex ℝ (G.finiteFeasiblePayoffs n)) :
    G.finiteFeasiblePayoffs (n + 1) = G.finiteFeasiblePayoffs n ∧
      ∀ m, n < m →
        G.finiteFeasiblePayoffs m = G.correlatedFeasiblePayoffs := by
  sorry

/-- Equation (19). -/
theorem equation_19 (G : FiniteStageGame) (n : ℕ) (hn : 0 < n)
    (hstable : ∀ m, n < m →
      G.finiteFeasiblePayoffs m = G.finiteFeasiblePayoffs n) :
    G.finiteFeasiblePayoffs n = G.correlatedFeasiblePayoffs := by
  sorry

/-- Equation (20), witnessed by Example 6. -/
theorem example6_D1_not_convex_D2_eq_C :
    ¬Convex ℝ example6.oneStageFeasiblePayoffs ∧
      example6.finiteFeasiblePayoffs 2 = example6.correlatedFeasiblePayoffs := by
  sorry

/-! The paper's two-by-two dichotomy follows from Proposition 5. -/
theorem two_by_two_feasible_dichotomy
    (topLeft topRight bottomLeft bottomRight : Payoff Bool) :
    let G := binaryGame topLeft topRight bottomLeft bottomRight
    G.oneStageFeasiblePayoffs = G.correlatedFeasiblePayoffs ∨
      ∀ n, 0 < n → G.finiteFeasiblePayoffs n ≠
        G.correlatedFeasiblePayoffs := by
  sorry

/-! Proposition 6 is the discounted analogue of Proposition 5. -/
theorem proposition_6 (G : FiniteStageGame) (lam : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hconvex : Convex ℝ (G.discountedFeasiblePayoffs lam)) :
    ∀ δ : ℝ, 0 < δ → δ < lam →
      G.discountedFeasiblePayoffs δ = G.correlatedFeasiblePayoffs := by
  sorry

/-- Equation (22). -/
theorem equation_22 (G : FiniteStageGame) (lam : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hstable : ∀ δ : ℝ, 0 < δ → δ < lam →
      G.discountedFeasiblePayoffs δ = G.discountedFeasiblePayoffs lam) :
    G.discountedFeasiblePayoffs lam = G.correlatedFeasiblePayoffs := by
  sorry

/-! ## Faces of the feasible polytope -/

/-- A face of a convex set, in the segment characterization used by the
paper. -/
def IsFaceOf {ι : Type} (P C : Set (Payoff ι)) : Prop :=
  P ⊆ C ∧ Convex ℝ P ∧
    ∀ x ∈ C, ∀ y ∈ C, ∀ t : ℝ, 0 < t → t < 1 →
      t • x + (1 - t) • y ∈ P → x ∈ P ∧ y ∈ P

/-- Directions generated by a set. -/
def directionSet {ι : Type} (S : Set (Payoff ι)) : Set (Payoff ι) :=
  {d | ∃ x ∈ S, ∃ y ∈ S, d = x - y}

/-- Affine dimension of a payoff set. -/
noncomputable def affineDimension {ι : Type} [Fintype ι]
    (S : Set (Payoff ι)) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (directionSet S))

/-- Boundary of a set in the topology induced on its affine hull.
This is the boundary used by the face induction in Proposition 9 and
Lemma 10.  For a lower-dimensional face, the ambient frontier is the
whole face and is therefore not an acceptable substitute. -/
noncomputable def relativeFrontier {ι : Type} [Fintype ι]
    (S : Set (Payoff ι)) : Set (Payoff ι) :=
  (fun x : affineSpan ℝ S => (x : Payoff ι)) ''
    frontier ((fun x : affineSpan ℝ S => (x : Payoff ι)) ⁻¹' S)

theorem relativeFrontier_subset_affineSpan
    {ι : Type} [Fintype ι] (S : Set (Payoff ι)) :
    relativeFrontier S ⊆ affineSpan ℝ S := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

/-! Proposition 7's maximal-gap argument and replacement of a positive-
probability continuation history have not been packaged for the repeated-game
adapter. -/
theorem proposition_7 (G : FiniteStageGame)
    (L : Set (Payoff G.Player)) (hface : IsFaceOf L G.correlatedFeasiblePayoffs)
    (hdim : affineDimension L = 1) (δ lam : ℝ)
    (hδ : 0 < δ) (hδlam : δ < lam) (hlam : lam ≤ 1)
    (hinclusion : G.discountedFeasiblePayoffs δ ∩ L ⊆
      G.discountedFeasiblePayoffs lam ∩ L) :
    L ⊆ G.discountedFeasiblePayoffs δ := by
  sorry

/-! Proposition 8 is the polytope-face induction built from Proposition 9. -/
theorem proposition_8 (G : FiniteStageGame)
    (n m : G.Horizon)
    (hsize : Fintype.card G.Player * m.1 < n.1)
    (hinclusion : G.finiteFeasiblePayoffs (n.1 + m.1) ⊆
      G.finiteFeasiblePayoffs n.1) :
    G.finiteFeasiblePayoffs (n.1 + m.1) =
      G.correlatedFeasiblePayoffs := by
  sorry

/-! Proposition 9 is the face-dimension induction. -/
theorem proposition_9 (G : FiniteStageGame)
    (P : Set (Payoff G.Player)) (p : ℕ) (n m : G.Horizon)
    (hface : IsFaceOf P G.correlatedFeasiblePayoffs)
    (hdim : affineDimension P = p)
    (hp : p < Fintype.card G.Player) (hsize : p * m.1 < n.1)
    (hinclusion : G.finiteFeasiblePayoffs (n.1 + m.1) ∩ P ⊆
      G.finiteFeasiblePayoffs n.1 ∩ P) :
    P ⊆ G.finiteFeasiblePayoffs (n.1 + m.1) := by
  sorry

/-- Distance from a point to a nonempty set, used only in Lemma 10. -/
noncomputable def distanceToSet {X : Type} [PseudoMetricSpace X]
    (x : X) (S : Set X) : ℝ :=
  sInf ((fun y => dist x y) '' S)

/-- A point maximizing distance to `K` over `P`. -/
def IsFarthestPoint {X : Type} [PseudoMetricSpace X]
    (z : X) (P K : Set X) : Prop :=
  z ∈ P ∧ K.Nonempty ∧ ∀ x ∈ P, distanceToSet x K ≤ distanceToSet z K

/-! **Lemma 10, pages 153--154.**  This is the separating-
hyperplane step inside Proposition 9.  Its induction hypothesis puts the
boundary of the face `P`, relative to `affineSpan P`, in `K`.  Using
ambient `frontier P` would make every lower-dimensional face equal its
frontier and collapse the induction.  The remaining missing ingredient is
the finite-dimensional closest-point/separation argument at this relative
level. -/
theorem lemma_10 {ι : Type} [Fintype ι]
    (P K : Set (Payoff ι)) (z : Payoff ι)
    (hP : Convex ℝ P) (hPcompact : IsCompact P)
    (hK : IsCompact K) (hKP : K ⊆ P)
    (hfrontier : relativeFrontier P ⊆ K)
    (hz : IsFarthestPoint z P K) :
    z ∈ convexHull ℝ
      (Metric.closedBall z (distanceToSet z K) ∩ K) := by
  sorry

/-! Proposition 11 is the paper's two-player winding-number argument.  The
current library has no theorem that the separately affine image of two compact
convex strategy spaces is simply connected. -/
theorem proposition_11 (G : CompactContinuousGame)
    (hplayers : Fintype.card G.Player = 2) :
    SimplyConnectedSet G.feasiblePayoffs := by
  sorry

/-! Proposition 11 specializes to both repeated evaluators through the
compact presentations, rather than remaining an unrelated generic claim. -/
theorem proposition_11_finite (G : FiniteStageGame)
    (n : G.Horizon) (hplayers : Fintype.card G.Player = 2) :
    SimplyConnectedSet (G.finiteFeasiblePayoffsOnHorizon n) := by
  obtain ⟨presentation⟩ := finiteCompactPresentation_exists G n
  rw [← finiteCompactPresentation_feasiblePayoffs_eq presentation]
  exact proposition_11 presentation.toCompactContinuousGame hplayers

theorem proposition_11_discounted (G : FiniteStageGame)
    (lam : G.DiscountRate) (hplayers : Fintype.card G.Player = 2) :
    SimplyConnectedSet (G.discountedFeasiblePayoffsOnRate lam) := by
  obtain ⟨presentation⟩ := discountedCompactPresentation_exists G lam
  rw [← discountedCompactPresentation_feasiblePayoffs_eq presentation]
  exact proposition_11 presentation.toCompactContinuousGame hplayers

/-! Corollary 12. -/
theorem corollary_12_discounted (G : FiniteStageGame)
    (hplayers : Fintype.card G.Player = 2) (δ lam : ℝ)
    (hδ : 0 < δ) (hδlam : δ < lam) (hlam1 : lam ≤ 1)
    (hinclusion : G.discountedFeasiblePayoffs δ ⊆
      G.discountedFeasiblePayoffs lam) :
    G.discountedFeasiblePayoffs δ = G.correlatedFeasiblePayoffs := by
  sorry

/-! Corollary 12, finite-horizon clause. -/
theorem corollary_12_finite (G : FiniteStageGame)
    (hplayers : Fintype.card G.Player = 2) (n m : G.Horizon)
    (hinclusion : G.finiteFeasiblePayoffs (n.1 + m.1) ⊆
      G.finiteFeasiblePayoffs n.1) :
    G.finiteFeasiblePayoffs (n.1 + m.1) =
      G.correlatedFeasiblePayoffs := by
  sorry

/-- Contractibility of the subspace `S`.  The homotopy is defined on
`[0,1] × S` and takes values in `S`; requiring an extension to all of the
ambient space would be strictly stronger than the paper's open problem. -/
def ContractibleSet {X : Type} [TopologicalSpace X] (S : Set X) : Prop :=
  ∃ center : S, ∃ H : Set.Icc (0 : ℝ) 1 × S → S, Continuous H ∧
    (∀ x : S, H (⟨0, by norm_num⟩, x) = x) ∧
    (∀ x : S, H (⟨1, by norm_num⟩, x) = center)

/-! The paper leaves both questions open for more than two players. -/
def OpenProblemHigherPlayerSimpleConnectedness : Prop :=
  ∀ G : CompactContinuousGame, 2 < Fintype.card G.Player →
    SimplyConnectedSet G.feasiblePayoffs

def OpenProblemHigherPlayerContractibility : Prop :=
  ∀ G : CompactContinuousGame, 2 < Fintype.card G.Player →
    ContractibleSet G.feasiblePayoffs

/-! ## 3. The Prisoner's Dilemma -/

/-- The paper's Prisoner's Dilemma. -/
def prisonersDilemma : FiniteStageGame :=
  binaryGame (pair 4 4) (pair 0 5) (pair 5 0) (pair 1 1)

/-- Bottom strictly dominates Top for player `false`. -/
theorem prisonersDilemma_bottom_strictly_dominates :
    ∀ column : Bool,
      binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0) (pair 1 1)
          (fun who => if who then column else true) false >
        binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0) (pair 1 1)
          (fun who => if who then column else false) false := by
  intro column
  cases column <;> norm_num [binaryPayoff]

/-- Right strictly dominates Left for player `true`. -/
theorem prisonersDilemma_right_strictly_dominates :
    ∀ row : Bool,
      binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0) (pair 1 1)
          (fun who => if who then true else row) true >
        binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0) (pair 1 1)
          (fun who => if who then false else row) true := by
  intro row
  cases row <;> norm_num [binaryPayoff]

/-! The one-stage feasible-set and equilibrium calculations require the
finite mixed-extension geometry. -/
theorem prisonersDilemma_D1_eq_C :
    prisonersDilemma.oneStageFeasiblePayoffs =
      prisonersDilemma.correlatedFeasiblePayoffs := by
  sorry

theorem prisonersDilemma_E1_eq_singleton :
    prisonersDilemma.oneStageEquilibriumPayoffs = {pair 1 1} := by
  sorry

/-- The paper's explicit description of `Δ` for the Prisoner's Dilemma. -/
theorem prisonersDilemma_individuallyRationalPayoffs :
    prisonersDilemma.individuallyRationalPayoffs =
      prisonersDilemma.correlatedFeasiblePayoffs ∩
        {v | 1 ≤ v false ∧ 1 ≤ v true} := by
  sorry

/-- Since `D₁ = C`, every positive finite repetition has feasible set `C`. -/
theorem prisonersDilemma_Dn_eq_C :
    ∀ n, 0 < n → prisonersDilemma.finiteFeasiblePayoffs n =
      prisonersDilemma.correlatedFeasiblePayoffs := by
  sorry

/-! Proposition 13 is a backward last-deviation argument using the unique
one-stage equilibrium payoff.  The repository does not yet expose the
positive-probability conditional-history induction in reusable form. -/
theorem proposition_13 (G : FiniteStageGame) (a : Payoff G.Player)
    (hunique : G.oneStageEquilibriumPayoffs = {a}) :
    ∀ n, 0 < n → G.finiteEquilibriumPayoffs n = {a} := by
  sorry

/-! The paper reports Benoit--Krishna's converse for two players: unless the
one-stage equilibrium-payoff set is a singleton, the finite-horizon
equilibrium-payoff sets converge to `Δ`.  That external theorem is not in the
current library. -/
theorem benoit_krishna_reported_converse (G : FiniteStageGame)
    (hplayers : Fintype.card G.Player = 2)
    (hnonsingleton : ∀ a, G.oneStageEquilibriumPayoffs ≠ {a}) :
    HausdorffConvergesAtTop G.finiteEquilibriumPayoffs
      G.individuallyRationalPayoffs := by
  sorry

/-- Every finite repetition of the Prisoner's Dilemma has only `(1,1)`. -/
theorem prisonersDilemma_En_eq_singleton :
    ∀ n, 0 < n →
      prisonersDilemma.finiteEquilibriumPayoffs n = {pair 1 1} := by
  intro n hn
  exact proposition_13 prisonersDilemma (pair 1 1)
    prisonersDilemma_E1_eq_singleton n hn

/-! Proposition 14's proof is the paper's uniform gain inequality and
supremum argument.  It is not implied merely by strict dominance. -/
theorem proposition_14 (lam : ℝ) (hlam : 3 / 4 < lam) (hlam1 : lam ≤ 1) :
    prisonersDilemma.discountedEquilibriumPayoffs lam = {pair 1 1} := by
  sorry

/-- The square `S` with vertices `(1,1),(1,4),(4,4),(4,1)`. -/
def prisonerSquare : Set (Payoff Bool) :=
  {v | 1 ≤ v false ∧ v false ≤ 4 ∧ 1 ≤ v true ∧ v true ≤ 4}

/-- The segment from `(4,1)` to `(19/4,1)`. -/
def prisonerHorizontalSegment : Set (Payoff Bool) :=
  {v | ∃ t ∈ Set.Icc (0 : ℝ) 1, v = pair (4 + (3 / 4) * t) 1}

/-- The segment from `(1,4)` to `(1,19/4)`. -/
def prisonerVerticalSegment : Set (Payoff Bool) :=
  {v | ∃ t ∈ Set.Icc (0 : ℝ) 1, v = pair 1 (4 + (3 / 4) * t)}

/-- The critical equilibrium-payoff set `A` in Figure 1. -/
def prisonerCriticalSet : Set (Payoff Bool) :=
  prisonerSquare ∪ (prisonerHorizontalSegment ∪ prisonerVerticalSegment)

@[simp] theorem pair_in_prisonerSquare_iff (x y : ℝ) :
    pair x y ∈ prisonerSquare ↔
      1 ≤ x ∧ x ≤ 4 ∧ 1 ≤ y ∧ y ≤ 4 := by
  rfl

/-- The four square vertices are in `S`. -/
theorem prisonerSquare_vertices :
    pair 1 1 ∈ prisonerSquare ∧ pair 1 4 ∈ prisonerSquare ∧
      pair 4 4 ∈ prisonerSquare ∧ pair 4 1 ∈ prisonerSquare := by
  norm_num [prisonerSquare]

/-- The two outer endpoints are in `A`. -/
theorem prisonerCriticalSet_outer_endpoints :
    pair (19 / 4) 1 ∈ prisonerCriticalSet ∧
      pair 1 (19 / 4) ∈ prisonerCriticalSet := by
  constructor
  · right
    left
    refine ⟨1, by norm_num, ?_⟩
    funext who
    cases who <;> norm_num [pair]
  · right
    right
    refine ⟨1, by norm_num, ?_⟩
    funext who
    cases who <;> norm_num [pair]

/-! Proposition 15 contains both an explicit equilibrium construction for all
of `A` and the multiplicative escape argument proving the reverse inclusion.
The history-dependent strategy construction and best-response continuation
selection are not yet formalized. -/
theorem proposition_15 :
    prisonersDilemma.discountedEquilibriumPayoffs (3 / 4) =
      prisonerCriticalSet := by
  sorry

/-! ## Concluding remarks -/

/-- Symmetric parameter family in concluding Remark 1. -/
def symmetricGeneralizedDilemma (α β x : ℝ) : FiniteStageGame :=
  binaryGame (pair (β - x) (β - x)) (pair (α - x) β)
    (pair β (α - x)) (pair α α)

/-- Critical current-stage discount in Remark 1. -/
def criticalDiscount (α β x : ℝ) : ℝ :=
  (β - α - x) / (β - α)

@[simp] theorem prisonersDilemma_as_generalized_payoff
    (action : ∀ _ : Bool, Bool) :
    (symmetricGeneralizedDilemma 1 5 1).payoff action =
      prisonersDilemma.payoff action := by
  change binaryPayoff (pair (5 - 1) (5 - 1)) (pair (1 - 1) 5)
      (pair 5 (1 - 1)) (pair 1 1) action =
    binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0) (pair 1 1) action
  norm_num

@[simp] theorem prisonersDilemma_criticalDiscount :
    criticalDiscount 1 5 1 = 3 / 4 := by
  norm_num [criticalDiscount]

/-! Remark 1: Proposition 14 extends to the symmetric parameter family. -/
theorem concluding_remark_1 (α β x lam : ℝ)
    (hgap : α < β - x) (hx : 0 < x)
    (hlam : criticalDiscount α β x < lam) (hlam1 : lam ≤ 1) :
    (symmetricGeneralizedDilemma α β x).discountedEquilibriumPayoffs lam =
      {pair α α} := by
  sorry

/-- The square analogue in concluding Remark 2. -/
def generalizedCriticalSquare (α β x : ℝ) : Set (Payoff Bool) :=
  {v | α ≤ v false ∧ v false ≤ β - x ∧
    α ≤ v true ∧ v true ≤ β - x}

/-- The right-hand spike analogue at the critical discount. -/
def generalizedHorizontalSegment (α β x : ℝ) : Set (Payoff Bool) :=
  {v | ∃ t ∈ Set.Icc (0 : ℝ) 1,
    v = pair ((β - x) + (x * (β - α - x) / (β - α)) * t) α}

/-- The upper spike analogue at the critical discount. -/
def generalizedVerticalSegment (α β x : ℝ) : Set (Payoff Bool) :=
  {v | ∃ t ∈ Set.Icc (0 : ℝ) 1,
    v = pair α ((β - x) + (x * (β - α - x) / (β - α)) * t)}

/-- The explicit analogue of Figure 1. -/
def generalizedCriticalSet (α β x : ℝ) : Set (Payoff Bool) :=
  generalizedCriticalSquare α β x ∪
    (generalizedHorizontalSegment α β x ∪
      generalizedVerticalSegment α β x)

/-! Remark 2 says the analogue of Proposition 15 holds under the printed
sufficient condition `β ≥ max{1 + α, 1 + 2x}`.  The proof is only announced
in the paper, and the explicit critical set is not printed there: the set
below is the Proposition 15 analogue extrapolated to the parameter family,
agreeing with Figure 1 at `α = 1`, `β = 5`, `x = 1`. -/
theorem concluding_remark_2 (α β x : ℝ)
    (hgap : α < β - x) (hx : 0 < x)
    (hβ : max (1 + α) (1 + 2 * x) ≤ β) :
    (symmetricGeneralizedDilemma α β x).discountedEquilibriumPayoffs
      (criticalDiscount α β x) = generalizedCriticalSet α β x := by
  sorry

/-- Pareto-optimal points of a feasible set. -/
def ParetoBoundary {ι : Type} (C : Set (Payoff ι)) : Set (Payoff ι) :=
  {v | v ∈ C ∧ ∀ w ∈ C, (∀ i, v i ≤ w i) → w = v}

/-! Remark 3's countably-infinite Pareto-boundary assertion requires the
unprinted family of equilibrium constructions alluded to by the author. -/
theorem concluding_remark_3 (lam : ℝ) (hlam : 1 / 2 < lam) (hlam' : lam < 3 / 4) :
    let S := prisonersDilemma.discountedEquilibriumPayoffs lam ∩
      ParetoBoundary prisonersDilemma.correlatedFeasiblePayoffs
    S.Countable ∧ S.Infinite := by
  sorry

/-- Asymmetric parameter family in concluding Remark 4. -/
def asymmetricGeneralizedDilemma (α β x y : ℝ) : FiniteStageGame :=
  binaryGame (pair (β - y) (β - y)) (pair (α - x) β)
    (pair β (α - x)) (pair α α)

/-- Critical discount in the asymmetric family. -/
def asymmetricCriticalDiscount (α β x y : ℝ) : ℝ :=
  max (β - α - x) (β - α - y) / (β - α)

/-- Discounted payoff of an alternating two-period path, starting at `u`. -/
def alternatingDiscountedPayoff (lam : ℝ)
    (u v : Payoff Bool) : Payoff Bool :=
  fun who => (u who + (1 - lam) * v who) / (2 - lam)

/-! Remark 4.  Above the critical value the usual payoff is unique.  At the
critical value, the printed alternating or stationary construction applies,
depending on the ordering of `x` and `y`. -/
theorem concluding_remark_4 (α β x y : ℝ)
    (hgap : α < β - y) (hx : 0 < x) (hy : 0 < y) :
    let G := asymmetricGeneralizedDilemma α β x y
    let lambar := asymmetricCriticalDiscount α β x y
    (∀ lam, lambar < lam → lam ≤ 1 →
      G.discountedEquilibriumPayoffs lam = {pair α α}) ∧
    (y > x →
      alternatingDiscountedPayoff lambar
          (pair β (α - x)) (pair (α - x) β) ∈
        G.discountedEquilibriumPayoffs lambar) ∧
    (x > y → pair (β - y) (β - y) ∈
      G.discountedEquilibriumPayoffs lambar) := by
  sorry

/-! Added in proof: without full dimensionality or two players, Lemma 2 is
false.  The paper cites a three-player example of Forges, Mertens and Neyman
with two-dimensional `Δ`.  The counterexample table is not printed, so its
existence is retained as an explicit external claim rather than fabricated. -/

def AddedInProofCounterexampleClaim : Prop :=
  ∃ G : FiniteStageGame,
    Fintype.card G.Player = 3 ∧
      affineDimension G.individuallyRationalPayoffs = 2 ∧
      ¬FullDimensional G.individuallyRationalPayoffs ∧
      ¬HausdorffConvergesAtZero G.discountedEquilibriumPayoffs
        G.individuallyRationalPayoffs

/-- The added-in-proof Forges--Mertens--Neyman counterexample assertion.
The cited game is external and its payoff table is absent from Sorin's paper. -/
theorem added_in_proof_counterexample :
    AddedInProofCounterexampleClaim := by
  sorry

end Literature.Sorin1986
