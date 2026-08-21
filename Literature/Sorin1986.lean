import Mathlib
import GameTheory.Analysis.Payoff
import MathUE.ProbabilityMassFunction.Simplex
import MathUE.PMFProduct.Bool
import MathUE.FixedRatioConvexity
import MathUE.FiniteEmpiricalConvexity
import UniformEquilibrium.Certificates.Public.FiniteHorizonProfileLawTransfer
import UniformEquilibrium.Certificates.Public.FixedPrefixAccounting
import UniformEquilibrium.Certificates.Public.TerminalChildLawTransfer
import UniformEquilibrium.ProofView.Concepts.Existence.CompactNash
import UniformEquilibrium.ProofView.Concepts.Stochastic.Classes.Absorbing
import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.FiniteHorizonContinuation
import UniformEquilibrium.ProofView.Concepts.Stochastic.Transform.Repeated.InitialActionAffineness
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
open scoped BigOperators ENNReal NNReal Topology

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
noncomputable abbrev FiniteStageGame.kernel (G : FiniteStageGame) :
    KernelGame G.Player :=
  KernelGame.ofPureEU G.Action G.payoff

/-- A mixed one-stage profile. -/
abbrev FiniteStageGame.MixedProfile (G : FiniteStageGame) :=
  KernelGame.Profile G.kernel.mixedExtension

/-- The public-history repeated game associated with `G`. -/
abbrev FiniteStageGame.repeatedGame (G : FiniteStageGame) :=
  G.kernel.realizedActionStochasticGame

/-- The unique state from which the repeated game starts. -/
private abbrev FiniteStageGame.repeatedInitial (G : FiniteStageGame) :
    G.repeatedGame.State :=
  PUnit.unit

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
  fun who => G.repeatedGame.discountedPayoff (1 - lam) profile G.repeatedInitial who


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

/-- Every independently mixed one-stage payoff is correlated-feasible. -/
theorem FiniteStageGame.mixedPayoff_mem_correlatedFeasiblePayoffs
    (G : FiniteStageGame) (profile : G.MixedProfile) :
    G.mixedPayoff profile ∈ G.correlatedFeasiblePayoffs := by
  letI (who : G.Player) : Fintype (G.kernel.Strategy who) :=
    G.finiteAction who
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ who, G.Action who)
    exact Finite.of_fintype _
  have h :=
    Math.ProbabilityMassFunction.coordinateExpectation_mem_convexHull_range
      (Math.PMFProduct.pmfPi profile) G.payoff
  change G.mixedPayoff profile ∈ convexHull ℝ (Set.range G.payoff)
  have heq : G.mixedPayoff profile =
      fun who ↦ Math.Probability.expect
        (Math.PMFProduct.pmfPi profile) (fun action ↦ G.payoff action who) := by
    funext who
    change G.kernel.mixedExtension.eu profile who = _
    rw [G.kernel.mixedExtension_eu]
    congr 1
    funext action
    simp [FiniteStageGame.kernel, KernelGame.eu_ofPureEU]
  rw [heq]
  exact h

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

/-- Against every mixed opponent profile, some pure reply attains at least the
paper's individual-rational level. -/
theorem FiniteStageGame.exists_pureReply_ge_individualRationalLevel
    (G : FiniteStageGame) (who : G.Player)
    (opponents : G.MixedOpponentProfile who) :
    ∃ action : G.Action who,
      G.individualRationalLevel who ≤
        G.kernel.mixedExtension.eu
          (G.kernel.mixedExtension.profileWithOpponent who
            (PMF.pure action) opponents) who := by
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ player, G.Action player)
    exact Finite.of_fintype _
  letI : Finite G.kernel.mixedExtension.Outcome :=
    G.kernel.finite_mixedExtension_outcome
  obtain ⟨C, hC⟩ :=
    G.kernel.mixedExtension.exists_eu_abs_bound_of_finite_outcome who
  have hbelow : BddBelow (Set.range fun opponent : G.MixedOpponentProfile who ↦
      G.bestPureReplyValue who opponent) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨opponent, rfl⟩
    let action : G.Action who := Classical.arbitrary (G.Action who)
    calc
      -C ≤ G.kernel.mixedExtension.eu
          (G.kernel.mixedExtension.profileWithOpponent who
            (PMF.pure action) opponent) who :=
        (abs_le.mp (hC _)).1
      _ ≤ G.bestPureReplyValue who opponent := by
        unfold FiniteStageGame.bestPureReplyValue
        have hupper : BddAbove (Set.range fun candidate : G.Action who ↦
            G.kernel.mixedExtension.eu
              (G.kernel.mixedExtension.profileWithOpponent who
                (PMF.pure candidate) opponent) who) :=
          Finite.bddAbove_range _
        exact le_ciSup hupper action
  have hlevel : G.individualRationalLevel who ≤
      G.bestPureReplyValue who opponents :=
    ciInf_le hbelow opponents
  obtain ⟨action, haction⟩ := exists_eq_ciSup_of_finite
    (f := fun action : G.Action who ↦
      G.kernel.mixedExtension.eu
        (G.kernel.mixedExtension.profileWithOpponent who
          (PMF.pure action) opponents) who)
  refine ⟨action, ?_⟩
  exact hlevel.trans_eq haction.symm

/-- The opponents' current mixed action after a repeated-game history. -/
def FiniteStageGame.opponentsAt
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) {time : ℕ} (history : G.repeatedGame.Hist time) :
    G.MixedOpponentProfile who :=
  fun opponent ↦ profile opponent.1 time history

/-- A pure current-stage best reply that reaches the paper's
individual-rational level. -/
noncomputable def FiniteStageGame.individualRationalReply
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) {time : ℕ} (history : G.repeatedGame.Hist time) :
    G.Action who :=
  Classical.choose
    (G.exists_pureReply_ge_individualRationalLevel who
      (G.opponentsAt profile who history))

theorem FiniteStageGame.individualRationalReply_spec
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) {time : ℕ} (history : G.repeatedGame.Hist time) :
    G.individualRationalLevel who ≤
      G.kernel.mixedExtension.eu
        (G.kernel.mixedExtension.profileWithOpponent who
          (PMF.pure (G.individualRationalReply profile who history))
          (G.opponentsAt profile who history)) who :=
  Classical.choose_spec
    (G.exists_pureReply_ge_individualRationalLevel who
      (G.opponentsAt profile who history))

/-- At every history, deviate to the pure current-stage reply selected above. -/
noncomputable def FiniteStageGame.individualRationalDeviation
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) : G.BehaviorStrategy who :=
  fun _time history ↦
    PMF.pure (G.individualRationalReply profile who history)

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

namespace DiscountedPresentation

open MeasureTheory
open Stochastic.Game
open StochasticGame.NativeBridge

private abbrev Native (G : FiniteStageGame) :=
  G.repeatedGame.toNative

private abbrev Protocol (G : FiniteStageGame) :=
  (Native G).perfectMonitoring PUnit.unit

/-- A total deterministic contingent plan in the native protocol. -/
private abbrev Plan (G : FiniteStageGame) (who : G.Player) :=
  (Protocol G).Policy who

private instance executionHistoryMeasurableSpace (G : FiniteStageGame) :
    MeasurableSpace ((Native G).toExecution PUnit.unit).History :=
  ⊤

private instance executionHistoryDiscreteMeasurableSpace
    (G : FiniteStageGame) :
    DiscreteMeasurableSpace
      ((Native G).toExecution PUnit.unit).History :=
  ⟨fun _ => MeasurableSet.of_discrete⟩

private instance choiceMeasurableSpace (G : FiniteStageGame)
    (who : G.Player) (info : (Protocol G).InfoState who) :
    MeasurableSpace ((Protocol G).Choice who info) :=
  ⊤

private instance choiceDiscreteMeasurableSpace (G : FiniteStageGame)
    (who : G.Player) (info : (Protocol G).InfoState who) :
    DiscreteMeasurableSpace ((Protocol G).Choice who info) :=
  ⟨fun _ => MeasurableSet.of_discrete⟩

private instance choiceTopologicalSpace (G : FiniteStageGame)
    (who : G.Player) (info : (Protocol G).InfoState who) :
    TopologicalSpace ((Protocol G).Choice who info) :=
  ⊥

private instance choiceDiscreteTopology (G : FiniteStageGame)
    (who : G.Player) (info : (Protocol G).InfoState who) :
    DiscreteTopology ((Protocol G).Choice who info) :=
  discreteTopology_bot _

private instance choiceFintype (G : FiniteStageGame)
    (who : G.Player) (info : (Protocol G).InfoState who) :
    Fintype ((Protocol G).Choice who info) :=
  Fintype.ofEquiv (G.Action who)
    ((Native G).actionChoiceEquiv PUnit.unit who info)

private instance nativeStageRecordFinite (G : FiniteStageGame) :
    Finite (Native G).StageRecord := by
  let encode : (Native G).StageRecord →
      (Native G).State ×
        ((∀ who, (Native G).Action who) × (Native G).State) :=
    fun record => (record.source, record.joint, record.target)
  apply Finite.of_injective encode
  intro first second heq
  cases first
  cases second
  cases heq
  rfl

/-- A mixed discounted strategy is an ordinary probability law on total
contingent plans. -/
private abbrev Strategy (G : FiniteStageGame) (who : G.Player) :=
  ProbabilityMeasure (Plan G who)

private instance executionHistoryMeasurableSingletonClass
    (G : FiniteStageGame) :
    MeasurableSingletonClass
      ((Native G).toExecution PUnit.unit).History :=
  ⟨fun _ => MeasurableSet.of_discrete⟩

private instance infoStateCountable (G : FiniteStageGame)
    (who : G.Player) : Countable ((Protocol G).InfoState who) := by
  letI : Countable (Native G).StageRecord := inferInstance
  letI : Countable (Native G).PublicHistory := inferInstance
  infer_instance

private noncomputable instance planInhabited (G : FiniteStageGame)
    (who : G.Player) : Inhabited (Plan G who) :=
  ⟨fun info => (Native G).actionChoiceEquiv PUnit.unit who info
    (Classical.choice (G.nonemptyAction who))⟩

private instance planCompact (G : FiniteStageGame) (who : G.Player) :
    CompactSpace (Plan G who) := by
  infer_instance

private instance planSecondCountable (G : FiniteStageGame)
    (who : G.Player) : SecondCountableTopology (Plan G who) := by
  infer_instance

private instance planPseudoMetrizable (G : FiniteStageGame)
    (who : G.Player) :
    TopologicalSpace.PseudoMetrizableSpace (Plan G who) := by
  infer_instance

private instance planOpensMeasurable (G : FiniteStageGame)
    (who : G.Player) : OpensMeasurableSpace (Plan G who) := by
  infer_instance

private instance strategyCompact (G : FiniteStageGame)
    (who : G.Player) : CompactSpace (Strategy G who) := by
  infer_instance

private instance strategyNonempty (G : FiniteStageGame)
    (who : G.Player) : Nonempty (Strategy G who) :=
  inferInstance

/-- Project a real coefficient to the unit interval. -/
private def coefficient (t : ℝ) : ℝ :=
  max 0 (min 1 t)

private theorem coefficient_nonneg (t : ℝ) : 0 ≤ coefficient t :=
  le_max_left _ _

private theorem coefficient_le_one (t : ℝ) : coefficient t ≤ 1 := by
  unfold coefficient
  exact max_le zero_le_one (min_le_left _ _)

private theorem coefficient_eq {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    coefficient t = t := by
  simp [coefficient, ht₀, ht₁]

private def nnCoefficient (t : ℝ) : ℝ≥0 :=
  ⟨coefficient t, coefficient_nonneg t⟩

private def complementCoefficient (t : ℝ) : ℝ≥0 :=
  ⟨1 - coefficient t, sub_nonneg.mpr (coefficient_le_one t)⟩

private theorem nnCoefficient_continuous : Continuous nnCoefficient := by
  apply Continuous.subtype_mk
  unfold coefficient
  exact continuous_const.max (continuous_const.min continuous_id)

private def scaleFiniteMeasure {X : Type} [MeasurableSpace X]
    (c : ℝ≥0) (law : FiniteMeasure X) : FiniteMeasure X :=
  c • law

private theorem scaleFiniteMeasure_continuous {X : Type}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] :
    Continuous fun p : ℝ≥0 × FiniteMeasure X =>
      scaleFiniteMeasure p.1 p.2 := by
  unfold scaleFiniteMeasure
  exact continuous_smul

@[simp]
private theorem scaleFiniteMeasure_zero {X : Type} [MeasurableSpace X]
    (law : FiniteMeasure X) : scaleFiniteMeasure 0 law = 0 := by
  unfold scaleFiniteMeasure
  exact zero_smul ℝ≥0 law

@[simp]
private theorem scaleFiniteMeasure_one {X : Type} [MeasurableSpace X]
    (law : FiniteMeasure X) : scaleFiniteMeasure 1 law = law := by
  unfold scaleFiniteMeasure
  exact one_smul ℝ≥0 law

private def scaleMeasure {X : Type} [MeasurableSpace X]
    (c : ℝ≥0) (law : Measure X) : Measure X :=
  c • law

@[simp]
private theorem scaleMeasure_zero {X : Type} [MeasurableSpace X]
    (law : Measure X) : scaleMeasure 0 law = 0 := by
  unfold scaleMeasure
  exact zero_smul ℝ≥0 law

@[simp]
private theorem scaleMeasure_one {X : Type} [MeasurableSpace X]
    (law : Measure X) : scaleMeasure 1 law = law := by
  unfold scaleMeasure
  exact one_smul ℝ≥0 law

private def mixedFiniteMeasure {G : FiniteStageGame} (who : G.Player)
    (t : ℝ) (x y : Strategy G who) : FiniteMeasure (Plan G who) :=
  scaleFiniteMeasure (nnCoefficient t) x.toFiniteMeasure +
    scaleFiniteMeasure (complementCoefficient t)
      y.toFiniteMeasure

/-- Convex combination of probability laws on total contingent plans. -/
private def mix {G : FiniteStageGame} (who : G.Player)
    (t : ℝ) (x y : Strategy G who) : Strategy G who := by
  let c := nnCoefficient t
  let d := complementCoefficient t
  refine ⟨scaleMeasure c x + scaleMeasure d y, ?_⟩
  constructor
  unfold scaleMeasure
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ]
  change (c : ℝ≥0∞) * 1 + (d : ℝ≥0∞) * 1 = 1
  rw [mul_one, mul_one]
  rw [← ENNReal.coe_add]
  congr 1
  apply NNReal.eq
  change coefficient t + (1 - coefficient t) = 1
  ring

private theorem toFiniteMeasure_mix {G : FiniteStageGame} (who : G.Player)
    (t : ℝ) (x y : Strategy G who) :
    (mix who t x y).toFiniteMeasure =
      mixedFiniteMeasure who t x y := by
  apply FiniteMeasure.toMeasure_injective
  simp only [mix, mixedFiniteMeasure, scaleFiniteMeasure,
    scaleMeasure,
    ProbabilityMeasure.toFiniteMeasure, FiniteMeasure.toMeasure_add,
    FiniteMeasure.toMeasure_smul]
  unfold ProbabilityMeasure.toMeasure FiniteMeasure.toMeasure
  rfl

private theorem mix_continuous {G : FiniteStageGame} (who : G.Player) :
    Continuous fun p : ℝ × (Strategy G who × Strategy G who) =>
      mix who p.1 p.2.1 p.2.2 := by
  apply continuous_induced_rng.2
  change Continuous fun p : ℝ × (Strategy G who × Strategy G who) =>
    (mix who p.1 p.2.1 p.2.2).toFiniteMeasure
  rw [show (fun p : ℝ × (Strategy G who × Strategy G who) =>
      (mix who p.1 p.2.1 p.2.2).toFiniteMeasure) =
      fun p => mixedFiniteMeasure who p.1 p.2.1 p.2.2 by
    funext p
    exact toFiniteMeasure_mix who p.1 p.2.1 p.2.2]
  unfold mixedFiniteMeasure
  have hc : Continuous fun p : ℝ × (Strategy G who × Strategy G who) =>
      nnCoefficient p.1 :=
    nnCoefficient_continuous.comp continuous_fst
  have hd : Continuous fun p : ℝ × (Strategy G who × Strategy G who) =>
      (⟨1 - coefficient p.1,
        sub_nonneg.mpr (coefficient_le_one p.1)⟩ : ℝ≥0) := by
    apply Continuous.subtype_mk
    exact continuous_const.sub
      (continuous_subtype_val.comp hc)
  have hx : Continuous fun p : ℝ × (Strategy G who × Strategy G who) =>
      p.2.1.toFiniteMeasure :=
    ProbabilityMeasure.toFiniteMeasure_continuous.comp
      (continuous_fst.comp continuous_snd)
  have hy : Continuous fun p : ℝ × (Strategy G who × Strategy G who) =>
      p.2.2.toFiniteMeasure :=
    ProbabilityMeasure.toFiniteMeasure_continuous.comp
      (continuous_snd.comp continuous_snd)
  have hleft : Continuous fun p :
      ℝ × (Strategy G who × Strategy G who) =>
      scaleFiniteMeasure (nnCoefficient p.1) p.2.1.toFiniteMeasure :=
    scaleFiniteMeasure_continuous.comp (hc.prodMk hx)
  have hright : Continuous fun p :
      ℝ × (Strategy G who × Strategy G who) =>
      scaleFiniteMeasure
        (⟨1 - coefficient p.1,
          sub_nonneg.mpr (coefficient_le_one p.1)⟩ : ℝ≥0)
        p.2.2.toFiniteMeasure :=
    scaleFiniteMeasure_continuous.comp (hd.prodMk hy)
  exact hleft.add hright

private theorem mix_zero {G : FiniteStageGame} (who : G.Player)
    (x y : Strategy G who) : mix who 0 x y = y := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [mix]
  unfold ProbabilityMeasure.toMeasure
  change scaleMeasure (nnCoefficient 0) (x : Measure (Plan G who)) +
    scaleMeasure (⟨1 - coefficient 0,
      sub_nonneg.mpr (coefficient_le_one 0)⟩ : ℝ≥0)
        (y : Measure (Plan G who)) = y
  rw [show nnCoefficient 0 = 0 by
    apply NNReal.eq
    change coefficient 0 = (0 : ℝ)
    exact coefficient_eq (by norm_num) (by norm_num)]
  rw [show (⟨1 - coefficient 0,
    sub_nonneg.mpr (coefficient_le_one 0)⟩ : ℝ≥0) = 1 by
      apply NNReal.eq
      change 1 - coefficient 0 = (1 : ℝ)
      rw [coefficient_eq (by norm_num) (by norm_num)]
      norm_num]
  unfold scaleMeasure
  ext s hs
  rw [Measure.add_apply]
  change (0 : ℝ≥0∞) * (x : Measure (Plan G who)) s +
    (1 : ℝ≥0∞) * (y : Measure (Plan G who)) s =
    (y : Measure (Plan G who)) s
  rw [zero_mul, zero_add, one_mul]

private theorem mix_one {G : FiniteStageGame} (who : G.Player)
    (x y : Strategy G who) : mix who 1 x y = x := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [mix]
  unfold ProbabilityMeasure.toMeasure
  change scaleMeasure (nnCoefficient 1) (x : Measure (Plan G who)) +
    scaleMeasure (⟨1 - coefficient 1,
      sub_nonneg.mpr (coefficient_le_one 1)⟩ : ℝ≥0)
        (y : Measure (Plan G who)) = x
  rw [show nnCoefficient 1 = 1 by
    apply NNReal.eq
    change coefficient 1 = (1 : ℝ)
    exact coefficient_eq (by norm_num) (by norm_num)]
  rw [show (⟨1 - coefficient 1,
    sub_nonneg.mpr (coefficient_le_one 1)⟩ : ℝ≥0) = 0 by
      apply NNReal.eq
      change 1 - coefficient 1 = (0 : ℝ)
      rw [coefficient_eq (by norm_num) (by norm_num)]
      norm_num]
  unfold scaleMeasure
  ext s hs
  rw [Measure.add_apply]
  change (1 : ℝ≥0∞) * (x : Measure (Plan G who)) s +
    (0 : ℝ≥0∞) * (y : Measure (Plan G who)) s =
      (x : Measure (Plan G who)) s
  rw [one_mul, zero_mul, add_zero]

/-- A finite barycenter of laws on total contingent plans. -/
private def simplexWeight {k : ℕ}
    (weights : stdSimplex ℝ (Fin (k + 1))) (a : Fin (k + 1)) : ℝ≥0 :=
  ⟨weights a, weights.2.1 a⟩

private def barycenterFiniteMeasure {G : FiniteStageGame}
    (who : G.Player) (k : ℕ)
    (weights : stdSimplex ℝ (Fin (k + 1)))
    (points : Fin (k + 1) → Strategy G who) :
    FiniteMeasure (Plan G who) :=
  ∑ a, scaleFiniteMeasure (simplexWeight weights a)
    (points a).toFiniteMeasure

private def barycenter {G : FiniteStageGame} (who : G.Player) (k : ℕ)
    (weights : stdSimplex ℝ (Fin (k + 1)))
    (points : Fin (k + 1) → Strategy G who) : Strategy G who := by
  let weight : Fin (k + 1) → ℝ≥0 := simplexWeight weights
  refine ⟨∑ a, weight a • (points a : Measure (Plan G who)), ?_⟩
  constructor
  rw [show (∑ a, weight a •
      (points a : Measure (Plan G who))) Set.univ =
      ∑ a, (weight a •
        (points a : Measure (Plan G who))) Set.univ by
    rw [Measure.coe_finsetSum]
    simp only [Finset.sum_apply]]
  simp only [Measure.smul_apply, measure_univ]
  change (∑ a, (weight a : ℝ≥0∞) * 1) = 1
  simp only [mul_one]
  norm_cast
  apply NNReal.eq
  rw [NNReal.coe_sum]
  change ∑ a, weights a = 1
  exact weights.2.2

private theorem toFiniteMeasure_barycenter {G : FiniteStageGame}
    (who : G.Player) (k : ℕ)
    (weights : stdSimplex ℝ (Fin (k + 1)))
    (points : Fin (k + 1) → Strategy G who) :
    (barycenter who k weights points).toFiniteMeasure =
      barycenterFiniteMeasure who k weights points := by
  apply FiniteMeasure.toMeasure_injective
  simp only [barycenter, barycenterFiniteMeasure,
    scaleFiniteMeasure, ProbabilityMeasure.toFiniteMeasure,
    FiniteMeasure.toMeasure_sum,
    FiniteMeasure.toMeasure_smul]
  unfold ProbabilityMeasure.toMeasure FiniteMeasure.toMeasure
  rfl

private theorem barycenter_continuous {G : FiniteStageGame}
    (who : G.Player) (k : ℕ)
    (points : Fin (k + 1) → Strategy G who) :
    Continuous fun weights : stdSimplex ℝ (Fin (k + 1)) =>
      barycenter who k weights points := by
  apply continuous_induced_rng.2
  change Continuous fun weights : stdSimplex ℝ (Fin (k + 1)) =>
    (barycenter who k weights points).toFiniteMeasure
  rw [show (fun weights : stdSimplex ℝ (Fin (k + 1)) =>
      (barycenter who k weights points).toFiniteMeasure) =
      fun weights => barycenterFiniteMeasure who k weights points by
    funext weights
    exact toFiniteMeasure_barycenter who k weights points]
  unfold barycenterFiniteMeasure
  apply continuous_finsetSum
  intro a _
  have hweight : Continuous fun weights :
      stdSimplex ℝ (Fin (k + 1)) =>
      (⟨weights a, weights.2.1 a⟩ : ℝ≥0) := by
    apply Continuous.subtype_mk
    exact (continuous_apply a).comp continuous_subtype_val
  have hlaw : Continuous fun _weights :
      stdSimplex ℝ (Fin (k + 1)) =>
      (points a).toFiniteMeasure :=
    continuous_const
  exact scaleFiniteMeasure_continuous.comp (hweight.prodMk hlaw)

/-- One fixed total pure profile, used only outside a bounded cylinder. -/
private noncomputable def fallback (G : FiniteStageGame) :
    (who : G.Player) → Plan G who :=
  fun _ => default

/-- Expected utility at one stage under a deterministic total-plan profile. -/
private def pureStagePayoff (G : FiniteStageGame) (observer : G.Player)
    (time : ℕ) (plans : (who : G.Player) → Plan G who) : ℝ :=
  ((Protocol G).run plans (time + 1)).expect
    ((Native G).latestStageUtility PUnit.unit observer)

private theorem pureStagePayoff_continuous (G : FiniteStageGame)
    (observer : G.Player) (time : ℕ) :
    Continuous (pureStagePayoff G observer time) := by
  let sites := (Native G).boundedInformationSites PUnit.unit (time + 1)
  let restrict := (Protocol G).restrictPolicies sites
  let assemble := (Protocol G).assemblePolicies sites (fallback G)
  let finitePayoff := fun draws =>
    ((Protocol G).run (assemble draws) (time + 1)).expect
      ((Native G).latestStageUtility PUnit.unit observer)
  have hrestrict : Continuous restrict := by
    unfold restrict GameTheory.Protocol.InformationModel.restrictPolicies
    fun_prop
  have hfinite : Continuous finitePayoff :=
    continuous_of_discreteTopology
  have hfactor : pureStagePayoff G observer time =
      finitePayoff ∘ restrict := by
    funext plans
    change pureStagePayoff G observer time plans =
      finitePayoff (restrict plans)
    unfold pureStagePayoff finitePayoff assemble
    rw [(Protocol G).run_assemble_restrict sites (fallback G) plans
      (time + 1)
      ((Native G).boundedInformationSites_cover PUnit.unit (time + 1))]
  rw [hfactor]
  exact hfinite.comp hrestrict

/-- A finite bound for one player's stage utility. -/
private def stageBound (G : FiniteStageGame) (observer : G.Player) : ℝ :=
  ∑ actions : (who : G.Player) → G.Action who,
    |G.payoff actions observer|

private theorem stagePayoff_le_stageBound (G : FiniteStageGame)
    (observer : G.Player) (actions : (who : G.Player) → G.Action who) :
    |G.payoff actions observer| ≤ stageBound G observer := by
  unfold stageBound
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun other => |G.payoff other observer|)
    (fun other _ => abs_nonneg (G.payoff other observer))
    (Finset.mem_univ actions)

private theorem nativeStageUtility_le_stageBound (G : FiniteStageGame)
    (observer : G.Player) (state : (Native G).State)
    (actions : (who : G.Player) → (Native G).Action who) :
    |(Native G).stageUtility state actions observer| ≤
      stageBound G observer := by
  rw [StochasticGame.toNative_stageUtility,
    KernelGame.realizedActionStochasticGame_stagePayoff]
  simpa only [FiniteStageGame.kernel, KernelGame.eu_ofPureEU] using
    stagePayoff_le_stageBound G observer actions

private theorem pureStagePayoff_le_stageBound (G : FiniteStageGame)
    (observer : G.Player) (time : ℕ)
    (plans : (who : G.Player) → Plan G who) :
    |pureStagePayoff G observer time plans| ≤ stageBound G observer := by
  unfold pureStagePayoff
  apply GameTheory.Math.Probability.FinDist.abs_expect_le_of_abs_bound
  intro history _
  exact (Native G).abs_latestStageUtility_le PUnit.unit observer
    (stageBound G observer)
    (nativeStageUtility_le_stageBound G observer) history

private theorem stageBound_nonneg (G : FiniteStageGame)
    (observer : G.Player) : 0 ≤ stageBound G observer := by
  unfold stageBound
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem discount_nonneg {G : FiniteStageGame}
    (lam : G.DiscountRate) : 0 ≤ 1 - lam.1 :=
  sub_nonneg.mpr lam.2.2

private theorem discount_lt_one {G : FiniteStageGame}
    (lam : G.DiscountRate) : 1 - lam.1 < 1 :=
  by linarith [lam.2.1]

/-- The normalized discounted payoff of one deterministic total-plan
profile. -/
private def pureDiscountedPayoff (G : FiniteStageGame)
    (lam : G.DiscountRate) (observer : G.Player)
    (plans : (who : G.Player) → Plan G who) : ℝ :=
  GameTheory.Math.normalizedDiscountedSum (1 - lam.1)
    (fun time => pureStagePayoff G observer time plans)

private theorem pureDiscountedPayoff_continuous (G : FiniteStageGame)
    (lam : G.DiscountRate) (observer : G.Player) :
    Continuous (pureDiscountedPayoff G lam observer) := by
  let discount := 1 - lam.1
  let bound := stageBound G observer
  have hdiscount0 : 0 ≤ discount := discount_nonneg lam
  have hdiscount1 : discount < 1 := discount_lt_one lam
  have hsummable : Summable fun time : ℕ => bound * discount ^ time :=
    (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound
  have hseries : Continuous fun plans : (who : G.Player) → Plan G who =>
      ∑' time : ℕ, discount ^ time *
        pureStagePayoff G observer time plans := by
    apply continuous_tsum
    · intro time
      exact continuous_const.mul
        (pureStagePayoff_continuous G observer time)
    · exact hsummable
    · intro time plans
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (pow_nonneg hdiscount0 time)]
      calc
        discount ^ time * |pureStagePayoff G observer time plans| ≤
            discount ^ time * bound :=
          mul_le_mul_of_nonneg_left
            (pureStagePayoff_le_stageBound G observer time plans)
            (pow_nonneg hdiscount0 time)
        _ = bound * discount ^ time := mul_comm _ _
  unfold pureDiscountedPayoff GameTheory.Math.normalizedDiscountedSum
  exact continuous_const.mul hseries

private theorem continuous_integrable_of_compact
    {X : Type} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X → ℝ) (hf : Continuous f) (measure : Measure X)
    [IsFiniteMeasure measure] : Integrable f measure := by
  let observable : BoundedContinuousFunction X ℝ :=
    ContinuousMap.equivBoundedOfCompact X ℝ ⟨f, hf⟩
  convert observable.integrable measure using 1
  ext x
  rfl

private theorem pureDiscountedPayoff_integrable (G : FiniteStageGame)
    (lam : G.DiscountRate) (observer : G.Player)
    (measure : Measure ((who : G.Player) → Plan G who))
    [IsFiniteMeasure measure] :
    Integrable (pureDiscountedPayoff G lam observer) measure :=
  continuous_integrable_of_compact _
    (pureDiscountedPayoff_continuous G lam observer) measure

/-- Independent product law of the players' total-plan laws. -/
private def jointLaw {G : FiniteStageGame}
    (profile : (who : G.Player) → Strategy G who) :
    ProbabilityMeasure ((who : G.Player) → Plan G who) :=
  ProbabilityMeasure.pi profile

private theorem jointLaw_continuous (G : FiniteStageGame) :
    Continuous (jointLaw (G := G)) :=
  ProbabilityMeasure.continuous_pi

private theorem integratedPureStagePayoff_eq_arbitrary
    (G : FiniteStageGame) (observer : G.Player) (time : ℕ)
    (profile : (who : G.Player) → Strategy G who) :
    (∫ plans, pureStagePayoff G observer time plans
      ∂(jointLaw profile : Measure ((who : G.Player) → Plan G who))) =
      (Native G).arbitraryPolicyMeasureStageExpectation PUnit.unit
        (fun who => (profile who : Measure (Plan G who))) observer time := by
  let laws : (Native G).ProtocolPolicyMeasureProfile PUnit.unit :=
    fun who => (profile who : Measure (Plan G who))
  letI : ∀ who, IsProbabilityMeasure (laws who) := fun who => by
    dsimp only [laws]
    infer_instance
  let sites := (Native G).boundedInformationSites PUnit.unit (time + 1)
  let restrict := (Protocol G).restrictPolicies sites
  let assemble := (Protocol G).assemblePolicies sites (fallback G)
  let draws := (Protocol G).finitePolicyMeasureDraws laws sites
  let finiteMixed := fun who =>
    GameTheory.Protocol.InformationModel.PolicyMeasure.toMixedWithin
      (M := Protocol G) (laws who) (sites who) (fallback G who)
  let observable := (Native G).latestStageUtility PUnit.unit observer
  let finitePayoff := fun restricted =>
    ((Protocol G).run (assemble restricted) (time + 1)).expect observable
  have hrestrict : Measurable restrict := by
    unfold restrict GameTheory.Protocol.InformationModel.restrictPolicies
    fun_prop
  have hfinite : StronglyMeasurable finitePayoff :=
    (measurable_of_finite finitePayoff).stronglyMeasurable
  have hfactor : pureStagePayoff G observer time =
      finitePayoff ∘ restrict := by
    funext plans
    unfold pureStagePayoff
    dsimp only [Function.comp_apply, finitePayoff, observable]
    unfold assemble
    rw [(Protocol G).run_assemble_restrict sites (fallback G) plans
      (time + 1)
      ((Native G).boundedInformationSites_cover PUnit.unit (time + 1))]
  have hmap :
      (jointLaw profile : Measure ((who : G.Player) → Plan G who)).map
          restrict = draws.toMeasure := by
    change ((Protocol G).policyProfileMeasure laws).map restrict =
      draws.toMeasure
    exact (Protocol G).policyProfileMeasure_map_restrict laws sites
  have hfiniteBound : ∀ restricted, ‖finitePayoff restricted‖ ≤
      stageBound G observer := by
    intro restricted
    rw [Real.norm_eq_abs]
    change |pureStagePayoff G observer time (assemble restricted)| ≤
      stageBound G observer
    exact pureStagePayoff_le_stageBound G observer time _
  have hobservableBound : ∀ history, ‖observable history‖ ≤
      stageBound G observer := by
    intro history
    rw [Real.norm_eq_abs]
    exact (Native G).abs_latestStageUtility_le PUnit.unit observer
      (stageBound G observer)
      (nativeStageUtility_le_stageBound G observer) history
  have hdrawRun :
      draws.bind (fun restricted =>
          (Protocol G).run (assemble restricted) (time + 1)) =
        (Protocol G).runMixed finiteMixed (time + 1) := by
    unfold finiteMixed draws
    unfold GameTheory.Protocol.InformationModel.runMixed
      GameTheory.Protocol.InformationModel.runMixedFrom
      GameTheory.Protocol.InformationModel.run
    rw [← (Protocol G).finitePolicyMeasureDraws_map_assemble
      laws sites (fallback G),
      GameTheory.Math.Probability.FinDist.bind_map]
  rw [hfactor]
  calc
    (∫ plans, finitePayoff (restrict plans)
        ∂(jointLaw profile : Measure ((who : G.Player) → Plan G who))) =
        ∫ restricted, finitePayoff restricted
          ∂((jointLaw profile :
            Measure ((who : G.Player) → Plan G who)).map restrict) :=
      (integral_map_of_stronglyMeasurable hrestrict hfinite).symm
    _ = ∫ restricted, finitePayoff restricted ∂draws.toMeasure := by
      rw [hmap]
    _ = draws.expect finitePayoff :=
      GameTheory.Math.Probability.FinDist.integral_toMeasure_eq_expect_of_bound
        draws finitePayoff hfiniteBound
    _ = ((Protocol G).runMixed finiteMixed (time + 1)).expect observable := by
      rw [← hdrawRun,
        GameTheory.Math.Probability.FinDist.expect_bind]
    _ = ∫ history, observable history
        ∂((Protocol G).runMixed finiteMixed (time + 1)).toMeasure :=
      (GameTheory.Math.Probability.FinDist.integral_toMeasure_eq_expect_of_bound
        ((Protocol G).runMixed finiteMixed (time + 1)) observable
        hobservableBound).symm
    _ = (Native G).arbitraryPolicyMeasureStageExpectation PUnit.unit
        laws observer time := by
      unfold Stochastic.Game.arbitraryPolicyMeasureStageExpectation
        GameTheory.Protocol.InformationModel.policyMeasurePrefixExpectation
      rw [(Protocol G).runPolicyMeasure_eq_runMixedWithin laws sites
        (fallback G) (time + 1)
        ((Native G).boundedInformationSites_cover PUnit.unit (time + 1))]

private theorem integratedPureDiscountedPayoff_eq_arbitrary
    (G : FiniteStageGame) (lam : G.DiscountRate)
    (observer : G.Player)
    (profile : (who : G.Player) → Strategy G who) :
    (∫ plans, pureDiscountedPayoff G lam observer plans
      ∂(jointLaw profile : Measure ((who : G.Player) → Plan G who))) =
      (Native G).arbitraryPolicyMeasureDiscountedPayoff PUnit.unit
        (1 - lam.1) (fun who =>
          (profile who : Measure (Plan G who))) observer := by
  let discount := 1 - lam.1
  let measure :=
    (jointLaw profile : Measure ((who : G.Player) → Plan G who))
  let term := fun time plans =>
    discount ^ time * pureStagePayoff G observer time plans
  have htermIntegrable : ∀ time, Integrable (term time) measure := by
    intro time
    apply continuous_integrable_of_compact
    exact continuous_const.mul
      (pureStagePayoff_continuous G observer time)
  have htermNormSummable : Summable fun time =>
      ∫ plans, ‖term time plans‖ ∂measure := by
    have hgeometric : Summable fun time : ℕ =>
        stageBound G observer * discount ^ time :=
      (summable_geometric_of_lt_one (discount_nonneg lam)
        (discount_lt_one lam)).mul_left (stageBound G observer)
    apply Summable.of_norm_bounded hgeometric
    intro time
    have hintegralNonneg : 0 ≤ ∫ plans, ‖term time plans‖ ∂measure :=
      integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hintegralNonneg]
    have hbound := norm_integral_le_of_norm_le_const
      (f := fun plans => ‖term time plans‖)
      (C := stageBound G observer * discount ^ time)
      (μ := measure)
      (Filter.Eventually.of_forall fun plans => by
        rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_eq_abs]
        dsimp only [term]
        rw [abs_mul,
          abs_of_nonneg (pow_nonneg (discount_nonneg lam) time)]
        calc
          discount ^ time *
              |pureStagePayoff G observer time plans| ≤
              discount ^ time * stageBound G observer :=
            mul_le_mul_of_nonneg_left
              (pureStagePayoff_le_stageBound G observer time plans)
              (pow_nonneg (discount_nonneg lam) time)
          _ = stageBound G observer * discount ^ time :=
            mul_comm _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg hintegralNonneg,
      probReal_univ, mul_one] at hbound
    exact hbound
  have hinterchange :=
    integral_tsum_of_summable_integral_norm htermIntegrable
      htermNormSummable
  unfold pureDiscountedPayoff
    Stochastic.Game.arbitraryPolicyMeasureDiscountedPayoff
    GameTheory.Math.normalizedDiscountedSum
  change (∫ plans, (1 - discount) * ∑' time, term time plans
      ∂measure) =
    (1 - discount) * ∑' time,
      discount ^ time *
        (Native G).arbitraryPolicyMeasureStageExpectation PUnit.unit
          (fun who => (profile who : Measure (Plan G who))) observer time
  rw [integral_const_mul]
  congr 1
  rw [← hinterchange]
  apply tsum_congr
  intro time
  rw [integral_const_mul,
    integratedPureStagePayoff_eq_arbitrary]

private def rectangleProduct {G : FiniteStageGame}
    (profile : (who : G.Player) → Strategy G who)
    (sets : (who : G.Player) → Set (Plan G who)) : ℝ≥0∞ :=
  ∏ who, (profile who : Measure (Plan G who)) (sets who)

private theorem jointLaw_pi {G : FiniteStageGame}
    (profile : (who : G.Player) → Strategy G who)
    (sets : (who : G.Player) → Set (Plan G who)) :
    (jointLaw profile : Measure ((who : G.Player) → Plan G who))
        (Set.pi Set.univ sets) = rectangleProduct profile sets := by
  unfold jointLaw rectangleProduct
  exact Measure.pi_pi (fun who =>
    (profile who : Measure (Plan G who))) sets

private theorem rectangleProduct_update {G : FiniteStageGame}
    (profile : (who : G.Player) → Strategy G who)
    (who : G.Player) (replacement : Strategy G who)
    (sets : (i : G.Player) → Set (Plan G i)) :
    rectangleProduct (Function.update profile who replacement) sets =
      (replacement : Measure (Plan G who)) (sets who) *
        ∏ i ∈ Finset.univ.erase who,
          (profile i : Measure (Plan G i)) (sets i) := by
  unfold rectangleProduct
  rw [← Finset.mul_prod_erase Finset.univ
    (fun i => ((Function.update profile who replacement) i :
      Measure (Plan G i)) (sets i)) (Finset.mem_univ who)]
  congr 1
  · rw [Function.update_self]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne]
    exact Finset.ne_of_mem_erase hi

private theorem mix_apply {G : FiniteStageGame} (who : G.Player)
    (t : ℝ) (x y : Strategy G who) (set : Set (Plan G who)) :
    (mix who t x y : Measure (Plan G who)) set =
      (nnCoefficient t : ℝ≥0∞) *
          (x : Measure (Plan G who)) set +
        (complementCoefficient t : ℝ≥0∞) *
          (y : Measure (Plan G who)) set := by
  simp only [mix]
  unfold ProbabilityMeasure.toMeasure scaleMeasure
  rw [Measure.add_apply]
  change (nnCoefficient t : ℝ≥0∞) *
      (x : Measure (Plan G who)) set +
    (complementCoefficient t : ℝ≥0∞) *
      (y : Measure (Plan G who)) set = _
  rfl

private theorem barycenter_apply {G : FiniteStageGame} (who : G.Player)
    (k : ℕ) (weights : stdSimplex ℝ (Fin (k + 1)))
    (points : Fin (k + 1) → Strategy G who)
    (set : Set (Plan G who)) :
    (barycenter who k weights points : Measure (Plan G who)) set =
      ∑ a, (simplexWeight weights a : ℝ≥0∞) *
        (points a : Measure (Plan G who)) set := by
  simp only [barycenter]
  unfold ProbabilityMeasure.toMeasure
  rw [Measure.coe_finsetSum]
  simp only [Finset.sum_apply, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul]

private theorem jointLaw_update_mix {G : FiniteStageGame}
    (profile : (who : G.Player) → Strategy G who)
    (who : G.Player) (t : ℝ) (x y : Strategy G who) :
    (jointLaw (Function.update profile who (mix who t x y)) :
        Measure ((i : G.Player) → Plan G i)) =
      scaleMeasure (nnCoefficient t)
          (jointLaw (Function.update profile who x) :
            Measure ((i : G.Player) → Plan G i)) +
        scaleMeasure
          (complementCoefficient t)
          (jointLaw (Function.update profile who y) :
            Measure ((i : G.Player) → Plan G i)) := by
  change Measure.pi (fun i =>
      ((Function.update profile who (mix who t x y)) i :
        Measure (Plan G i))) = _
  apply Measure.pi_eq
  intro sets hsets
  unfold scaleMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [jointLaw_pi, jointLaw_pi]
  change (nnCoefficient t : ℝ≥0∞) *
        rectangleProduct (Function.update profile who x) sets +
      (complementCoefficient t : ℝ≥0∞) *
        rectangleProduct (Function.update profile who y) sets =
    rectangleProduct (Function.update profile who (mix who t x y)) sets
  rw [rectangleProduct_update, rectangleProduct_update,
    rectangleProduct_update, mix_apply]
  ring

private theorem jointLaw_update_barycenter {G : FiniteStageGame}
    (profile : (who : G.Player) → Strategy G who)
    (who : G.Player) (k : ℕ)
    (weights : stdSimplex ℝ (Fin (k + 1)))
    (points : Fin (k + 1) → Strategy G who) :
    (jointLaw (Function.update profile who
        (barycenter who k weights points)) :
        Measure ((i : G.Player) → Plan G i)) =
      ∑ a, scaleMeasure (simplexWeight weights a)
        (jointLaw (Function.update profile who (points a)) :
          Measure ((i : G.Player) → Plan G i)) := by
  change Measure.pi (fun i =>
      ((Function.update profile who
        (barycenter who k weights points)) i :
        Measure (Plan G i))) = _
  apply Measure.pi_eq
  intro sets hsets
  rw [Measure.coe_finsetSum]
  simp only [Finset.sum_apply, scaleMeasure, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul]
  simp_rw [jointLaw_pi]
  change (∑ a, (simplexWeight weights a : ℝ≥0∞) *
      rectangleProduct (Function.update profile who (points a)) sets) =
    rectangleProduct
      (Function.update profile who (barycenter who k weights points)) sets
  rw [rectangleProduct_update, barycenter_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [rectangleProduct_update]
  exact (mul_assoc _ _ _).symm

/-- Expected discounted utility after independently drawing one total plan
for each player. -/
private def compactPayoff (G : FiniteStageGame) (lam : G.DiscountRate)
    (profile : (who : G.Player) → Strategy G who) : Payoff G.Player :=
  fun observer => ∫ plans, pureDiscountedPayoff G lam observer plans
    ∂(jointLaw profile : Measure ((who : G.Player) → Plan G who))

private theorem compactPayoff_continuous (G : FiniteStageGame)
    (lam : G.DiscountRate) (observer : G.Player) :
    Continuous fun profile : (who : G.Player) → Strategy G who =>
      compactPayoff G lam profile observer := by
  let observable : C((who : G.Player) → Plan G who, ℝ) :=
    ⟨pureDiscountedPayoff G lam observer,
      pureDiscountedPayoff_continuous G lam observer⟩
  exact (ProbabilityMeasure.continuous_integral_continuousMap
    observable).comp (jointLaw_continuous G)

private theorem compactPayoff_affine (G : FiniteStageGame)
    (lam : G.DiscountRate)
    (profile : (who : G.Player) → Strategy G who)
    (who : G.Player) (x y : Strategy G who) (t : ℝ)
    (observer : G.Player) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    compactPayoff G lam
        (Function.update profile who (mix who t x y)) observer =
      t * compactPayoff G lam (Function.update profile who x) observer +
        (1 - t) * compactPayoff G lam
          (Function.update profile who y) observer := by
  have hx : Integrable (pureDiscountedPayoff G lam observer)
      (jointLaw (Function.update profile who x) :
        Measure ((i : G.Player) → Plan G i)) :=
    pureDiscountedPayoff_integrable G lam observer _
  have hy : Integrable (pureDiscountedPayoff G lam observer)
      (jointLaw (Function.update profile who y) :
        Measure ((i : G.Player) → Plan G i)) :=
    pureDiscountedPayoff_integrable G lam observer _
  unfold compactPayoff
  rw [jointLaw_update_mix]
  unfold scaleMeasure
  rw [integral_add_measure (hx.smul_measure_nnreal)
    (hy.smul_measure_nnreal),
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  change coefficient t * _ + (1 - coefficient t) * _ =
    t * _ + (1 - t) * _
  rw [coefficient_eq ht₀ ht₁]

private theorem compactPayoff_barycentric (G : FiniteStageGame)
    (lam : G.DiscountRate)
    (profile : (who : G.Player) → Strategy G who)
    (who : G.Player) (k : ℕ)
    (weights : stdSimplex ℝ (Fin (k + 1)))
    (points : Fin (k + 1) → Strategy G who) :
    compactPayoff G lam
        (Function.update profile who (barycenter who k weights points)) who =
      ∑ a, weights a * compactPayoff G lam
        (Function.update profile who (points a)) who := by
  unfold compactPayoff
  rw [jointLaw_update_barycenter]
  simp only [scaleMeasure]
  rw [integral_finsetSum_measure (fun a _ =>
    (pureDiscountedPayoff_integrable G lam who
      (jointLaw (Function.update profile who (points a)) :
        Measure ((i : G.Player) → Plan G i))).smul_measure_nnreal)]
  simp only [integral_smul_nnreal_measure,
    NNReal.smul_def, smul_eq_mul, simplexWeight]
  apply Finset.sum_congr rfl
  intro a _
  rfl

/-- Fixed public pure-policy fallbacks used only on zero-mass cylinders. -/
private def publicFallback (G : FiniteStageGame) :
    (Native G).PurePublicProfile :=
  fun who => (Native G).purePolicyEquiv PUnit.unit who (fallback G who)

private def lawProfile {G : FiniteStageGame}
    (profile : (who : G.Player) → Strategy G who) :
    (Native G).ProtocolPolicyMeasureProfile PUnit.unit :=
  fun who => (profile who : Measure (Plan G who))

private instance lawProfile_isProbability {G : FiniteStageGame}
    (profile : (who : G.Player) → Strategy G who) :
    ∀ who, IsProbabilityMeasure (lawProfile profile who) :=
  fun who => by
    unfold lawProfile
    infer_instance

/-- Native conditional reading of independently drawn total plans. -/
private def nativePublic {G : FiniteStageGame}
    (profile : (who : G.Player) → Strategy G who) :
    (Native G).PublicProfile PUnit.unit :=
  (Native G).policyMeasuresToPublicBehavioralWith PUnit.unit
    (lawProfile profile) (publicFallback G)

/-- Conditioning independently drawn plans is coordinatewise in the player. -/
private theorem nativePublic_update {G : FiniteStageGame}
    (profile : (who : G.Player) → Strategy G who) (who : G.Player)
    (deviation : Strategy G who) :
    nativePublic (Function.update profile who deviation) =
      Profile.update (nativePublic profile) who
        ((Native G).ofBehavioralPolicy PUnit.unit
          (GameTheory.Protocol.InformationModel.PolicyMeasure.toBehavioralWith
            (M := Protocol G) (deviation : Measure (Plan G who))
            (fallback G who))) := by
  let initial : (Native G).State := PUnit.unit
  apply ((Native G).profileEquiv initial).injective
  change (Native G).toBehaviorProfile initial
      (nativePublic (Function.update profile who deviation)) =
    (Native G).toBehaviorProfile initial
      (Profile.update (nativePublic profile) who
        ((Native G).ofBehavioralPolicy PUnit.unit
          (GameTheory.Protocol.InformationModel.PolicyMeasure.toBehavioralWith
            (M := Protocol G) (deviation : Measure (Plan G who))
            (fallback G who))))
  rw [(Native G).toBehaviorProfile_update]
  unfold nativePublic Stochastic.Game.policyMeasuresToPublicBehavioralWith
  rw [(Native G).toBehaviorProfile_ofBehaviorProfile,
    (Native G).toBehaviorProfile_ofBehaviorProfile]
  dsimp only [initial,
    GameTheory.Protocol.InformationModel.policyMeasureBehavioralWith]
  simp only [(Native G).toBehavioralPolicy_ofBehavioralPolicy]
  funext i
  by_cases hi : i = who
  · subst i
    simp only [publicFallback, Profile.update_same]
    have hmeasure :
        lawProfile (Function.update profile who deviation) who =
          (deviation : Measure (Plan G who)) := by
      simp [lawProfile]
    exact
      GameTheory.Protocol.InformationModel.PolicyMeasure.toBehavioralWith_congr
        (M := Protocol G)
        (lawProfile (Function.update profile who deviation) who)
        (deviation : Measure (Plan G who)) (fallback G who) hmeasure
  · simp only [publicFallback, Profile.update_of_ne _ _ hi]
    have hmeasure :
        lawProfile (Function.update profile who deviation) i =
          lawProfile profile i := by
      simp [lawProfile, hi]
    exact
      GameTheory.Protocol.InformationModel.PolicyMeasure.toBehavioralWith_congr
        (M := Protocol G)
        (lawProfile (Function.update profile who deviation) i)
        (lawProfile profile i) (fallback G i) hmeasure

/-- Behavioral realization of a compact total-plan-law profile. -/
private def toBehavior {G : FiniteStageGame}
    (profile : (who : G.Player) → Strategy G who) :
    G.BehaviorProfile :=
  StochasticGame.NativeBridge.ofNativePublicProfile G.repeatedGame
    PUnit.unit (nativePublic profile)

private theorem toBehavior_update {G : FiniteStageGame}
    (profile : (who : G.Player) → Strategy G who) (who : G.Player)
    (deviation : Strategy G who) :
    let publicDeviation :=
      (Native G).ofBehavioralPolicy PUnit.unit
        (GameTheory.Protocol.InformationModel.PolicyMeasure.toBehavioralWith
          (M := Protocol G) (deviation : Measure (Plan G who))
          (fallback G who))
    toBehavior (Function.update profile who deviation) =
      Function.update (toBehavior profile) who
        (StochasticGame.NativeBridge.ofNativePublicPolicy G.repeatedGame
          publicDeviation) := by
  dsimp only
  unfold toBehavior
  rw [nativePublic_update]
  funext i
  by_cases hi : i = who
  · subst i
    simp [StochasticGame.NativeBridge.ofNativePublicProfile]
  · simp [StochasticGame.NativeBridge.ofNativePublicProfile,
      Profile.update_of_ne, Function.update_of_ne, hi]

private def compiledBehavior {G : FiniteStageGame}
    (profile : G.BehaviorProfile) :
    Profile (Protocol G).behavioralSignature :=
  StochasticGame.NativeBridge.toNativeBehaviorProfile G.repeatedGame
    PUnit.unit profile

/-- Predraw every coordinate of a proof-view behavioral profile once. -/
private def fromBehavior {G : FiniteStageGame}
    (profile : G.BehaviorProfile) :
    (who : G.Player) → Strategy G who :=
  fun who => ⟨(compiledBehavior profile who).toPureMeasure, by
    exact
      GameTheory.Protocol.InformationModel.BehavioralPolicy.toPureMeasure_isProbability
        (M := Protocol G) (compiledBehavior profile who)⟩

private theorem fromBehavior_update {G : FiniteStageGame}
    (profile : G.BehaviorProfile) (who : G.Player)
    (deviation : G.BehaviorStrategy who) :
    let publicDeviation :=
      toNativePublicPolicy G.repeatedGame PUnit.unit deviation
    let strategyDeviation : Strategy G who :=
      ⟨((Native G).toBehavioralPolicy PUnit.unit
          publicDeviation).toPureMeasure,
        GameTheory.Protocol.InformationModel.BehavioralPolicy.toPureMeasure_isProbability
          (M := Protocol G) _⟩
    fromBehavior (Function.update profile who deviation) =
      Function.update (fromBehavior profile) who strategyDeviation := by
  dsimp only
  let publicDeviation :=
    toNativePublicPolicy G.repeatedGame PUnit.unit deviation
  let protocolDeviation :=
    (Native G).toBehavioralPolicy PUnit.unit publicDeviation
  have hcompiled :
      compiledBehavior (Function.update profile who deviation) =
        Profile.update (compiledBehavior profile) who protocolDeviation := by
    unfold compiledBehavior
      StochasticGame.NativeBridge.toNativeBehaviorProfile
    rw [StochasticGame.NativeBridge.toNativePublicProfile_update,
      (Native G).toBehaviorProfile_update]
  funext i
  apply ProbabilityMeasure.toMeasure_injective
  by_cases hi : i = who
  · subst i
    have hpoint := congrFun hcompiled who
    simp only [Profile.update_same] at hpoint
    simp [fromBehavior, hpoint, protocolDeviation, publicDeviation]
  · have hpoint := congrFun hcompiled i
    simp only [Profile.update_of_ne _ _ hi] at hpoint
    simp [fromBehavior, Function.update_of_ne, hi, hpoint]

private theorem compactPayoff_eq_nativePublic {G : FiniteStageGame}
    (lam : G.DiscountRate)
    (profile : (who : G.Player) → Strategy G who)
    (observer : G.Player) :
    compactPayoff G lam profile observer =
      (Native G).behavioralDiscountedPayoff PUnit.unit (1 - lam.1)
        (nativePublic profile) observer := by
  unfold compactPayoff
  rw [integratedPureDiscountedPayoff_eq_arbitrary]
  exact ((Native G).kuhn_arbitraryPolicyMeasure_discountedPayoff
    PUnit.unit (discount_nonneg lam) (discount_lt_one lam)
    (lawProfile profile) (publicFallback G) observer
    (nativeStageUtility_le_stageBound G observer)).2

private theorem payoff_toBehavior {G : FiniteStageGame}
    (lam : G.DiscountRate)
    (profile : (who : G.Player) → Strategy G who) :
    G.discountedPayoffOnRate lam (toBehavior profile) =
      compactPayoff G lam profile := by
  funext observer
  change G.repeatedGame.discountedPayoff (1 - lam.1)
      (toBehavior profile) PUnit.unit observer =
    compactPayoff G lam profile observer
  unfold toBehavior
  rw [← StochasticGame.NativeBridge.native_behavioralDiscountedPayoff_eq_of_publicProfile
    G.repeatedGame PUnit.unit (nativePublic profile) (1 - lam.1) observer]
  exact (compactPayoff_eq_nativePublic lam profile observer).symm

private theorem arbitraryPayoff_fromBehavior_eq_policyMeasure
    {G : FiniteStageGame} (profile : G.BehaviorProfile)
    (discount : ℝ) (observer : G.Player) :
    (Native G).arbitraryPolicyMeasureDiscountedPayoff PUnit.unit discount
        (lawProfile (fromBehavior profile)) observer =
      (Native G).policyMeasureDiscountedPayoff PUnit.unit discount
        (StochasticGame.NativeBridge.toNativePublicProfile G.repeatedGame
          PUnit.unit profile) observer := by
  let protocolBehavior := (Native G).toBehaviorProfile PUnit.unit
    (StochasticGame.NativeBridge.toNativePublicProfile G.repeatedGame
      PUnit.unit profile)
  letI : ∀ who, IsProbabilityMeasure
      ((protocolBehavior who).toPureMeasure) := fun who =>
    GameTheory.Protocol.InformationModel.BehavioralPolicy.toPureMeasure_isProbability
      (M := Protocol G) (protocolBehavior who)
  have hlaws : lawProfile (fromBehavior profile) =
      fun who => (protocolBehavior who).toPureMeasure := by
    funext who
    rfl
  unfold Stochastic.Game.arbitraryPolicyMeasureDiscountedPayoff
    Stochastic.Game.policyMeasureDiscountedPayoff
    GameTheory.Math.normalizedDiscountedSum
  congr 2
  funext time
  unfold Stochastic.Game.arbitraryPolicyMeasureStageExpectation
    Stochastic.Game.policyMeasureStageExpectation
    GameTheory.Protocol.InformationModel.policyMeasurePrefixExpectation
    GameTheory.Protocol.InformationModel.pureMeasurePrefixExpectation
    GameTheory.Protocol.InformationModel.runPolicyMeasure
    GameTheory.Protocol.InformationModel.runPureMeasure
    GameTheory.Protocol.InformationModel.policyProfileMeasure
    GameTheory.Protocol.InformationModel.behavioralProfileMeasure
  rw [Measure.infinitePi_eq_pi, hlaws]

private theorem payoff_fromBehavior {G : FiniteStageGame}
    (lam : G.DiscountRate) (profile : G.BehaviorProfile) :
    compactPayoff G lam (fromBehavior profile) =
      G.discountedPayoffOnRate lam profile := by
  funext observer
  unfold compactPayoff
  rw [integratedPureDiscountedPayoff_eq_arbitrary]
  change (Native G).arbitraryPolicyMeasureDiscountedPayoff PUnit.unit
      (1 - lam.1) (lawProfile (fromBehavior profile)) observer = _
  rw [
    arbitraryPayoff_fromBehavior_eq_policyMeasure]
  rw [((Native G).kuhn_policyMeasure_discountedPayoff PUnit.unit
    (discount_nonneg lam) (discount_lt_one lam)
    (StochasticGame.NativeBridge.toNativePublicProfile G.repeatedGame
      PUnit.unit profile) observer
    (nativeStageUtility_le_stageBound G observer)).2]
  exact StochasticGame.NativeBridge.native_behavioralDiscountedPayoff_eq
    G.repeatedGame profile PUnit.unit (1 - lam.1) observer

/-- Replacing one arbitrary-law player by a behavioral deviation preserves
the deviating player's discounted payoff. -/
private theorem compactPayoff_update_behavioral {G : FiniteStageGame}
    (lam : G.DiscountRate)
    (profile : (who : G.Player) → Strategy G who) (who : G.Player)
    (deviation : G.BehaviorStrategy who) :
    let publicDeviation :=
      StochasticGame.NativeBridge.toNativePublicPolicy G.repeatedGame
        PUnit.unit deviation
    let strategyDeviation : Strategy G who :=
      ⟨((Native G).toBehavioralPolicy PUnit.unit
          publicDeviation).toPureMeasure,
        GameTheory.Protocol.InformationModel.BehavioralPolicy.toPureMeasure_isProbability
          (M := Protocol G) _⟩
    compactPayoff G lam
        (Function.update profile who strategyDeviation) who =
      G.repeatedGame.discountedPayoff (1 - lam.1)
        (Function.update (toBehavior profile) who deviation)
        PUnit.unit who := by
  dsimp only
  let publicDeviation :=
    StochasticGame.NativeBridge.toNativePublicPolicy G.repeatedGame
      PUnit.unit deviation
  let strategyDeviation : Strategy G who :=
    ⟨((Native G).toBehavioralPolicy PUnit.unit
        publicDeviation).toPureMeasure,
      GameTheory.Protocol.InformationModel.BehavioralPolicy.toPureMeasure_isProbability
        (M := Protocol G) _⟩
  have hlaws :
      lawProfile (Function.update profile who strategyDeviation) =
        Profile.update (sig := (Protocol G).policyMeasureSignature)
          (lawProfile profile) who
          ((Native G).toBehavioralPolicy PUnit.unit
            publicDeviation).toPureMeasure := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [lawProfile, strategyDeviation]
    · simp [lawProfile, hi]
  have hkuhn :=
    kuhn_arbitraryPolicyMeasure_opponents_behavioralDeviation_discountedPayoff
      (G := G.repeatedGame.toNative) PUnit.unit
      (discount_nonneg lam) (discount_lt_one lam) (lawProfile profile)
      (publicFallback G) who publicDeviation
      (nativeStageUtility_le_stageBound G who)
  unfold compactPayoff
  rw [integratedPureDiscountedPayoff_eq_arbitrary]
  change (Native G).arbitraryPolicyMeasureDiscountedPayoff PUnit.unit
      (1 - lam.1)
      (lawProfile (Function.update profile who strategyDeviation)) who = _
  rw [hlaws]
  rw [hkuhn.2]
  have hagree :=
    toNativePublicProfile_update_ofProofViewDeviation_agrees
      G.repeatedGame PUnit.unit (nativePublic profile) who deviation
  apply native_behavioralDiscountedPayoff_eq_of_coherent
    G.repeatedGame PUnit.unit
    (Function.update (toBehavior profile) who deviation)
    (Profile.update (nativePublic profile) who publicDeviation)
  simpa only [toBehavior, publicDeviation] using hagree

/-- Replacing one behavioral player by an arbitrary total-plan law preserves
the deviating player's discounted payoff. -/
private theorem compactPayoff_fromBehavior_update_arbitrary
    {G : FiniteStageGame} (lam : G.DiscountRate)
    (profile : G.BehaviorProfile) (who : G.Player)
    (deviation : Strategy G who) :
    let publicDeviation :=
      (Native G).ofBehavioralPolicy PUnit.unit
        (GameTheory.Protocol.InformationModel.PolicyMeasure.toBehavioralWith
          (M := Protocol G) (deviation : Measure (Plan G who))
          ((Native G).purePolicyEquiv PUnit.unit who |>.symm
            (publicFallback G who)))
    let proofDeviation :=
      ofNativePublicPolicy G.repeatedGame publicDeviation
    compactPayoff G lam
        (Function.update (fromBehavior profile) who deviation) who =
      G.repeatedGame.discountedPayoff (1 - lam.1)
        (Function.update profile who proofDeviation) PUnit.unit who := by
  dsimp only
  let publicProfile :=
    toNativePublicProfile G.repeatedGame PUnit.unit profile
  let protocolBehavior :=
    (Native G).toBehaviorProfile PUnit.unit publicProfile
  let publicDeviation :=
    (Native G).ofBehavioralPolicy PUnit.unit
      (GameTheory.Protocol.InformationModel.PolicyMeasure.toBehavioralWith
        (M := Protocol G) (deviation : Measure (Plan G who))
        ((Native G).purePolicyEquiv PUnit.unit who |>.symm
          (publicFallback G who)))
  let proofDeviation :=
    ofNativePublicPolicy G.repeatedGame publicDeviation
  have hlaws :
      lawProfile (Function.update (fromBehavior profile) who deviation) =
        Profile.update (sig := (Protocol G).policyMeasureSignature)
          (fun i => ((Native G).toBehavioralPolicy PUnit.unit
            (publicProfile i)).toPureMeasure) who
          (deviation : Measure (Plan G who)) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [lawProfile]
    · simp [lawProfile, fromBehavior, compiledBehavior, publicProfile,
        StochasticGame.NativeBridge.toNativeBehaviorProfile,
        Stochastic.Game.toBehaviorProfile, hi]
  have hkuhn :=
    kuhn_behavioral_opponents_arbitraryPolicyMeasureDeviation_discountedPayoff
      (G := G.repeatedGame.toNative) PUnit.unit
      (discount_nonneg lam) (discount_lt_one lam) publicProfile who
      (deviation : Measure (Plan G who)) (publicFallback G who)
      (nativeStageUtility_le_stageBound G who)
  unfold compactPayoff
  rw [integratedPureDiscountedPayoff_eq_arbitrary]
  change (Native G).arbitraryPolicyMeasureDiscountedPayoff PUnit.unit
      (1 - lam.1)
      (lawProfile (Function.update (fromBehavior profile) who deviation))
      who = _
  rw [hlaws, hkuhn.2]
  have hagree := toNativePublicProfile_update_ofNativeDeviation_agrees
    G.repeatedGame PUnit.unit profile who publicDeviation
  apply native_behavioralDiscountedPayoff_eq_of_coherent
    G.repeatedGame PUnit.unit
    (Function.update profile who proofDeviation)
    (Profile.update publicProfile who publicDeviation)
  simpa only [proofDeviation, publicProfile] using hagree

/- GameTheory's hybrid unilateral Kuhn laws preserve the opponents while the
deviating player crosses between behavioral policies and arbitrary total-plan
laws.  This is exactly what transports the full deviation quantifier below. -/
private theorem nash_toBehavior_iff {G : FiniteStageGame}
    (lam : G.DiscountRate)
    (profile : (who : G.Player) → Strategy G who) :
    (∀ who deviation,
      compactPayoff G lam profile who ≥
        compactPayoff G lam
          (Function.update profile who deviation) who) ↔
      G.repeatedGame.IsDiscountedεNash (1 - lam.1) PUnit.unit 0
        (toBehavior profile) := by
  constructor
  · intro hcompact who deviation
    let publicDeviation :=
      toNativePublicPolicy G.repeatedGame PUnit.unit deviation
    let strategyDeviation : Strategy G who :=
      ⟨((Native G).toBehavioralPolicy PUnit.unit
          publicDeviation).toPureMeasure,
        by
          exact
            GameTheory.Protocol.InformationModel.BehavioralPolicy.toPureMeasure_isProbability
              (M := Protocol G) _⟩
    have hbound := hcompact who strategyDeviation
    have hbase := congrFun (payoff_toBehavior lam profile) who
    change G.repeatedGame.discountedPayoff (1 - lam.1)
      (toBehavior profile) PUnit.unit who = _ at hbase
    have hdeviation :=
      compactPayoff_update_behavioral lam profile who deviation
    rw [← hbase, hdeviation] at hbound
    simpa only [add_zero] using hbound
  · intro hbehavior who deviation
    let publicDeviation :=
      (Native G).ofBehavioralPolicy PUnit.unit
        (GameTheory.Protocol.InformationModel.PolicyMeasure.toBehavioralWith
          (M := Protocol G) (deviation : Measure (Plan G who))
          (fallback G who))
    let proofDeviation :=
      ofNativePublicPolicy G.repeatedGame publicDeviation
    have hbound := hbehavior who proofDeviation
    have hprofile :
        toBehavior (Function.update profile who deviation) =
          Function.update (toBehavior profile) who proofDeviation := by
      simpa only [proofDeviation, publicDeviation] using
        toBehavior_update profile who deviation
    have hbase := congrFun (payoff_toBehavior lam profile) who
    change G.repeatedGame.discountedPayoff (1 - lam.1)
      (toBehavior profile) PUnit.unit who = _ at hbase
    have hdeviation := congrFun
      (payoff_toBehavior lam (Function.update profile who deviation)) who
    rw [hprofile] at hdeviation
    change G.repeatedGame.discountedPayoff (1 - lam.1)
      (Function.update (toBehavior profile) who proofDeviation)
      PUnit.unit who = _ at hdeviation
    rw [hbase, hdeviation] at hbound
    simpa only [add_zero] using hbound

private theorem nash_fromBehavior_iff {G : FiniteStageGame}
    (lam : G.DiscountRate) (profile : G.BehaviorProfile) :
    (∀ who deviation,
      compactPayoff G lam (fromBehavior profile) who ≥
        compactPayoff G lam
          (Function.update (fromBehavior profile) who deviation) who) ↔
      G.repeatedGame.IsDiscountedεNash (1 - lam.1) PUnit.unit 0
        profile := by
  constructor
  · intro hcompact who deviation
    let publicDeviation :=
      toNativePublicPolicy G.repeatedGame PUnit.unit deviation
    let strategyDeviation : Strategy G who :=
      ⟨((Native G).toBehavioralPolicy PUnit.unit
          publicDeviation).toPureMeasure,
        by
          exact
            GameTheory.Protocol.InformationModel.BehavioralPolicy.toPureMeasure_isProbability
              (M := Protocol G) _⟩
    have hbound := hcompact who strategyDeviation
    have hprofile :
        fromBehavior (Function.update profile who deviation) =
          Function.update (fromBehavior profile) who strategyDeviation := by
      simpa only [strategyDeviation, publicDeviation] using
        fromBehavior_update profile who deviation
    have hbase := congrFun (payoff_fromBehavior lam profile) who
    change compactPayoff G lam (fromBehavior profile) who =
      G.repeatedGame.discountedPayoff (1 - lam.1) profile
        PUnit.unit who at hbase
    have hdeviation := congrFun
      (payoff_fromBehavior lam (Function.update profile who deviation)) who
    rw [hprofile] at hdeviation
    change compactPayoff G lam
        (Function.update (fromBehavior profile) who strategyDeviation) who =
      G.repeatedGame.discountedPayoff (1 - lam.1)
        (Function.update profile who deviation) PUnit.unit who at hdeviation
    rw [hbase, hdeviation] at hbound
    simpa only [add_zero] using hbound
  · intro hbehavior who deviation
    let publicDeviation :=
      (Native G).ofBehavioralPolicy PUnit.unit
        (GameTheory.Protocol.InformationModel.PolicyMeasure.toBehavioralWith
          (M := Protocol G) (deviation : Measure (Plan G who))
          ((Native G).purePolicyEquiv PUnit.unit who |>.symm
            (publicFallback G who)))
    let proofDeviation :=
      ofNativePublicPolicy G.repeatedGame publicDeviation
    have hbound := hbehavior who proofDeviation
    have hbase := congrFun (payoff_fromBehavior lam profile) who
    change compactPayoff G lam (fromBehavior profile) who =
      G.repeatedGame.discountedPayoff (1 - lam.1) profile
        PUnit.unit who at hbase
    have hdeviationRaw :=
      compactPayoff_fromBehavior_update_arbitrary
        lam profile who deviation
    have hdeviation :
        compactPayoff G lam
            (Function.update (fromBehavior profile) who deviation) who =
          G.repeatedGame.discountedPayoff (1 - lam.1)
            (Function.update profile who proofDeviation) PUnit.unit who := by
      simpa only [publicDeviation, proofDeviation] using hdeviationRaw
    rw [← hbase, ← hdeviation] at hbound
    simpa only [add_zero] using hbound

end DiscountedPresentation

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
gives the required behavioral transports.  In the discounted case, the
compact weak-topology carrier, payoff transports, and Nash transports are
checked above; the last use GameTheory's hybrid unilateral Kuhn laws.  Neither
declaration assumes a Nash profile exists. -/
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
  exact ⟨{
    Strategy := DiscountedPresentation.Strategy G
    mix := DiscountedPresentation.mix
    mixContinuous := DiscountedPresentation.mix_continuous
    mix_zero := DiscountedPresentation.mix_zero
    mix_one := DiscountedPresentation.mix_one
    compactPayoff := DiscountedPresentation.compactPayoff G lam
    compactPayoffContinuous :=
      DiscountedPresentation.compactPayoff_continuous G lam
    compactPayoffAffine :=
      DiscountedPresentation.compactPayoff_affine G lam
    barycenter := DiscountedPresentation.barycenter
    barycenterContinuous :=
      DiscountedPresentation.barycenter_continuous
    compactPayoffBarycentric :=
      DiscountedPresentation.compactPayoff_barycentric G lam
    toBehavior := DiscountedPresentation.toBehavior
    fromBehavior := DiscountedPresentation.fromBehavior
    payoff_toBehavior := DiscountedPresentation.payoff_toBehavior lam
    payoff_fromBehavior := DiscountedPresentation.payoff_fromBehavior lam
    nash_toBehavior_iff :=
      DiscountedPresentation.nash_toBehavior_iff lam
    nash_fromBehavior_iff :=
      DiscountedPresentation.nash_fromBehavior_iff lam
  }⟩

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

/-- Play a prescribed independently mixed stage profile at each date,
independently of the public history. -/
private noncomputable def mixedSequenceBehavior (G : FiniteStageGame)
    (sequence : ℕ → G.MixedProfile) : G.BehaviorProfile :=
  fun who time _history => sequence time who

/-- A history-independent mixed-profile sequence has the prescribed expected
stage payoff at every date. -/
private theorem expectedStagePayoff_mixedSequenceBehavior
    (G : FiniteStageGame) (sequence : ℕ → G.MixedProfile) (time : ℕ) :
    (fun who => G.repeatedGame.expectedStagePayoff
      (mixedSequenceBehavior G sequence) PUnit.unit time who) =
      G.mixedPayoff (sequence time) := by
  letI (who : G.Player) : Finite (G.repeatedGame.Act who) :=
    @Finite.of_fintype _ (G.finiteAction who)
  letI : Fintype G.repeatedGame.State := inferInstanceAs (Fintype PUnit)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ who, G.Action who)
    exact Finite.of_fintype _
  funext who
  unfold StochasticGame.expectedStagePayoff
  rw [show (fun history => G.repeatedGame.stageEUAt
      (mixedSequenceBehavior G sequence) history who) =
      fun _history => G.mixedPayoff (sequence time) who by
    funext history
    unfold StochasticGame.stageEUAt StochasticGame.stageActionDist
    unfold mixedSequenceBehavior FiniteStageGame.mixedPayoff
      KernelGame.payoffVector
    exact (G.kernel.mixedExtension_eu (sequence time) who).symm]
  exact Math.Probability.expect_const _ _

/-! The asymptotic feasible-payoff statements use block approximation and the
Banach-limit identification.  The corresponding general repeated-game theorem
has not been formalized in the repository. -/
private theorem expectedStagePayoff_mem_correlatedFeasiblePayoffs_early
    (G : FiniteStageGame) (profile : G.BehaviorProfile) (time : ℕ) :
    (fun who ↦ G.repeatedGame.expectedStagePayoff
      profile PUnit.unit time who) ∈ G.correlatedFeasiblePayoffs := by
  letI (who : G.Player) : Finite (G.repeatedGame.Act who) :=
    @Finite.of_fintype _ (G.finiteAction who)
  letI : Fintype G.repeatedGame.State := inferInstanceAs (Fintype PUnit)
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ who, G.Action who)
    exact Finite.of_fintype _
  let payoffAt := fun history : G.repeatedGame.Hist time ↦
    G.mixedPayoff (fun who ↦ profile who time history)
  have hbar :=
    Math.ProbabilityMassFunction.coordinateExpectation_mem_convexHull_range
      (G.repeatedGame.histDist profile PUnit.unit time) payoffAt
  have hrange : Set.range payoffAt ⊆ G.correlatedFeasiblePayoffs := by
    rintro _ ⟨history, rfl⟩
    exact G.mixedPayoff_mem_correlatedFeasiblePayoffs
      (fun who ↦ profile who time history)
  have hmem := convexHull_min hrange
    G.correlatedFeasiblePayoffs_convex hbar
  dsimp only [payoffAt] at hmem
  change (fun who ↦ Math.Probability.expect
    (G.repeatedGame.histDist profile PUnit.unit time) fun history ↦
      G.repeatedGame.stageEUAt profile history who) ∈
        G.correlatedFeasiblePayoffs
  convert hmem using 1
  funext who
  congr 1
  funext history
  change Math.Probability.expect
      (Math.PMFProduct.pmfPi (fun player ↦ profile player time history))
        (fun action ↦ G.kernel.eu action who) =
    G.kernel.mixedExtension.eu
      (fun player ↦ profile player time history) who
  exact (G.kernel.mixedExtension_eu _ _).symm

/-- Property (3), finite-horizon clause: `Dₙ` converges to `C`. -/
theorem property_3_finite (G : FiniteStageGame) :
    HausdorffConvergesAtTop G.finiteFeasiblePayoffs
      G.correlatedFeasiblePayoffs := by
  let ActionProfile := ∀ who, G.Action who
  letI : Nonempty ActionProfile := inferInstance
  obtain ⟨bound, hboundAbs⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun action : ActionProfile => ‖G.payoff action‖)
  have hbound : ∀ action : ActionProfile, ‖G.payoff action‖ ≤ bound := by
    intro action
    simpa [abs_of_nonneg (norm_nonneg _)] using hboundAbs action
  have hbound0 : 0 ≤ bound := by
    exact (norm_nonneg (G.payoff (Classical.arbitrary ActionProfile))).trans
      (hbound _)
  intro ε hε
  obtain ⟨n₀, hn₀, happrox⟩ :=
    MathUE.exists_uniformAverage_close_of_mem_convexHull_range
      (fun action : ActionProfile => G.payoff action) hbound hbound0 hε
  refine ⟨n₀, fun n hn => ?_⟩
  have hnpos : 0 < n := hn₀.trans_le hn
  constructor
  · intro payoff hpayoff
    rcases hpayoff with ⟨profile, rfl⟩
    have hmem : G.finitePayoff n profile ∈
        G.correlatedFeasiblePayoffs := by
      unfold FiniteStageGame.finitePayoff
      rw [show (fun who ↦ G.repeatedGame.finiteAveragePayoff
        PUnit.unit n profile who) =
          (n : ℝ)⁻¹ • ∑ time ∈ Finset.range n,
            (fun who ↦ G.repeatedGame.expectedStagePayoff
              profile PUnit.unit time who) by
        funext who
        rw [G.repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
        simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]]
      rw [Finset.smul_sum]
      apply G.correlatedFeasiblePayoffs_convex.sum_mem
      · intro _ _
        exact inv_nonneg.mpr (Nat.cast_nonneg n)
      · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        apply mul_inv_cancel₀
        exact_mod_cast Nat.ne_of_gt hnpos
      · intro time _
        exact expectedStagePayoff_mem_correlatedFeasiblePayoffs_early
          G profile time
    refine ⟨G.finitePayoff n profile, hmem, ?_⟩
    exact (dist_self _).trans_lt hε
  · intro target htarget
    obtain ⟨sample, hsample⟩ := happrox n hn target htarget
    let stages : ℕ → G.MixedProfile := fun time =>
      if htime : time < n then
        G.kernel.pureMixedProfile (sample ⟨time, htime⟩)
      else
        G.kernel.pureMixedProfile (Classical.arbitrary ActionProfile)
    let behavior := mixedSequenceBehavior G stages
    have hstage (time : ℕ) (htime : time < n) :
        (fun who => G.repeatedGame.expectedStagePayoff
          behavior PUnit.unit time who) = G.payoff (sample ⟨time, htime⟩) := by
      rw [show behavior = mixedSequenceBehavior G stages by rfl,
        expectedStagePayoff_mixedSequenceBehavior]
      dsimp only [stages]
      rw [dif_pos htime]
      change G.kernel.mixedExtension.payoffVector
          (G.kernel.pureMixedProfile (sample ⟨time, htime⟩)) =
        G.payoff (sample ⟨time, htime⟩)
      rw [G.kernel.mixedExtension_payoffVector_pureMixedProfile]
      funext who
      change G.kernel.eu (sample ⟨time, htime⟩) who =
        G.payoff (sample ⟨time, htime⟩) who
      simp [FiniteStageGame.kernel, KernelGame.eu_ofPureEU]
    have hpayoff : G.finitePayoff n behavior =
        (n : ℝ)⁻¹ • ∑ j, G.payoff (sample j) := by
      funext who
      unfold FiniteStageGame.finitePayoff
      rw [G.repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      congr 1
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro time htime
      have htimen : time < n := Finset.mem_range.mp htime
      rw [dif_pos htimen]
      exact congrFun (hstage time htimen) who
    refine ⟨G.finitePayoff n behavior, ⟨behavior, rfl⟩, ?_⟩
    rw [hpayoff, dist_eq_norm]
    exact hsample

theorem property_3 (G : FiniteStageGame) :
    HausdorffConvergesAtTop G.finiteFeasiblePayoffs
        G.correlatedFeasiblePayoffs ∧
      HausdorffConvergesAtZero G.discountedFeasiblePayoffs
        G.correlatedFeasiblePayoffs ∧
      ∀ L : BanachLimit,
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
  simp [FiniteStageGame.kernel, KernelGame.eu_ofPureEU]

/-- The mixed profile prescribed by a behavioral profile at the unique empty
history. -/
def FiniteStageGame.initialMixedProfile
    (G : FiniteStageGame) (profile : G.BehaviorProfile) : G.MixedProfile :=
  fun who ↦ profile who 0 (G.repeatedGame.emptyHist PUnit.unit)

/-- At horizon one, the behavioral payoff is exactly the payoff of the mixed
profile prescribed at the empty history. -/
theorem finitePayoff_one_eq_mixedPayoff_initial
    (G : FiniteStageGame) (profile : G.BehaviorProfile) :
    G.finitePayoff 1 profile = G.mixedPayoff (G.initialMixedProfile profile) := by
  letI (who : G.Player) : Finite (G.repeatedGame.Act who) :=
    @Finite.of_fintype _ (G.finiteAction who)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ who, G.Action who)
    exact Finite.of_fintype _
  funext who
  unfold FiniteStageGame.finitePayoff
  rw [G.repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_one, inv_one, one_mul]
  rw [G.repeatedGame.expectedStagePayoff_zero]
  unfold StochasticGame.stageEUAt FiniteStageGame.mixedPayoff
  change Math.Probability.expect
      (Math.PMFProduct.pmfPi (G.initialMixedProfile profile))
        (fun action ↦ G.kernel.eu action who) =
    G.kernel.mixedExtension.eu (G.initialMixedProfile profile) who
  exact (G.kernel.mixedExtension_eu _ _).symm

/-! **Lemma 1(5), finite-horizon clause.**  Stationary repetition of a
mixed one-stage profile gives the same payoff at every positive horizon.
The exact public-history embedding is not yet packaged for this adapter. -/
theorem lemma_1_D1_subset_Dn (G : FiniteStageGame)
    (n : G.Horizon) :
    G.oneStageFeasiblePayoffs ⊆
      G.finiteFeasiblePayoffsOnHorizon n := by
  letI (who : G.Player) : Finite (G.kernel.Strategy who) :=
    @Finite.of_fintype _ (G.finiteAction who)
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ who, G.Action who)
    exact Finite.of_fintype _
  rintro payoff ⟨profile, rfl⟩
  let monitored :=
    G.kernel.realizedActionMonitoring.stationaryMonitoredProfile profile
  let behavior :=
    GameTheory.KernelGame.RealizedActionRepeatedAdapter.toBehaviorProfile
      G.kernel monitored
  refine ⟨behavior, ?_⟩
  funext who
  change G.repeatedGame.finiteAveragePayoff PUnit.unit n.1 behavior who =
    G.kernel.mixedExtension.payoffVector profile who
  rw [GameTheory.KernelGame.RealizedActionRepeatedAdapter.finiteAveragePayoff_toBehaviorProfile]
  exact G.kernel.realizedActionMonitoring.finiteAveragePayoff_stationaryMonitoredProfile
    (Nat.ne_of_gt n.2) profile who

/-- The one-period behavioral feasible set is the one-stage mixed feasible
set. -/
theorem finiteFeasiblePayoffs_one_eq_oneStageFeasiblePayoffs
    (G : FiniteStageGame) :
    G.finiteFeasiblePayoffs 1 = G.oneStageFeasiblePayoffs := by
  apply Set.Subset.antisymm
  · rintro payoff ⟨profile, rfl⟩
    exact ⟨G.initialMixedProfile profile,
      (finitePayoff_one_eq_mixedPayoff_initial G profile).symm⟩
  · exact lemma_1_D1_subset_Dn G ⟨1, by omega⟩

/-! **Lemma 1(5), discounted clause.**  The same stationary profile has
its one-stage payoff under every paper discount rate. -/
theorem lemma_1_D1_subset_Dlambda (G : FiniteStageGame)
    (lam : G.DiscountRate) :
    G.oneStageFeasiblePayoffs ⊆
      G.discountedFeasiblePayoffsOnRate lam := by
  letI (who : G.Player) : Finite (G.kernel.Strategy who) :=
    @Finite.of_fintype _ (G.finiteAction who)
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ who, G.Action who)
    exact Finite.of_fintype _
  rintro payoff ⟨profile, rfl⟩
  let monitored :=
    G.kernel.realizedActionMonitoring.stationaryMonitoredProfile profile
  let behavior :=
    GameTheory.KernelGame.RealizedActionRepeatedAdapter.toBehaviorProfile
      G.kernel monitored
  refine ⟨behavior, ?_⟩
  funext who
  change G.repeatedGame.discountedPayoff (1 - lam.1) behavior
      PUnit.unit who = G.kernel.mixedExtension.payoffVector profile who
  apply G.repeatedGame.discountedPayoff_of_forall_expectedStagePayoff_eq
      (β := 1 - lam.1)
  · intro time
    rw [GameTheory.KernelGame.RealizedActionRepeatedAdapter.expectedStagePayoff_toBehaviorProfile]
    exact G.kernel.realizedActionMonitoring.stageEU_stationaryMonitoredProfile
      profile time who
  · linarith [lam.2.2]
  · linarith [lam.2.1]

/-- Every period's expected payoff vector under a public monitored profile is
correlated-feasible. -/
theorem monitoredStagePayoff_mem_correlatedFeasiblePayoffs
    (G : FiniteStageGame)
    (profile : G.kernel.realizedActionMonitoring.MonitoredProfile)
    (time : ℕ) :
    (fun who ↦ G.kernel.realizedActionMonitoring.stageEU
      profile time who) ∈ G.correlatedFeasiblePayoffs := by
  letI (who : G.Player) : Fintype (G.kernel.Strategy who) :=
    G.finiteAction who
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ who, G.Action who)
    exact Finite.of_fintype _
  let M := G.kernel.realizedActionMonitoring
  let payoffAt := fun history : M.SignalHistory time ↦
    fun who ↦ G.kernel.mixedExtension.eu
      (fun player ↦ profile player time history) who
  have hbar :=
    Math.ProbabilityMassFunction.coordinateExpectation_mem_convexHull_range
      (M.signalHistoryDist profile time) payoffAt
  have hrange : Set.range payoffAt ⊆ G.correlatedFeasiblePayoffs := by
    rintro _ ⟨history, rfl⟩
    change G.mixedPayoff (fun who ↦ profile who time history) ∈
      G.correlatedFeasiblePayoffs
    exact FiniteStageGame.mixedPayoff_mem_correlatedFeasiblePayoffs
      G (fun who ↦ profile who time history)
  have hmem :
      (fun who ↦ Math.Probability.expect
        (M.signalHistoryDist profile time) (fun history ↦ payoffAt history who)) ∈
        G.correlatedFeasiblePayoffs :=
    convexHull_min hrange G.correlatedFeasiblePayoffs_convex hbar
  simpa only [KernelGame.PublicMonitoring.stageEU, M, payoffAt] using hmem

/-- The expected payoff vector in every period of the stochastic presentation
is correlated-feasible. -/
theorem expectedStagePayoff_mem_correlatedFeasiblePayoffs
    (G : FiniteStageGame) (profile : G.BehaviorProfile) (time : ℕ) :
    (fun who ↦ G.repeatedGame.expectedStagePayoff
      profile PUnit.unit time who) ∈ G.correlatedFeasiblePayoffs := by
  letI (who : G.Player) : Finite (G.kernel.Strategy who) :=
    @Finite.of_fintype _ (G.finiteAction who)
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ who, G.Action who)
    exact Finite.of_fintype _
  let monitored :=
    GameTheory.KernelGame.RealizedActionRepeatedAdapter.toMonitoredProfile
      G.kernel profile
  have hmem := monitoredStagePayoff_mem_correlatedFeasiblePayoffs
    G monitored time
  have heq :
      (fun who ↦ G.repeatedGame.expectedStagePayoff
        profile PUnit.unit time who) =
      fun who ↦ G.kernel.realizedActionMonitoring.stageEU
        monitored time who := by
    funext who
    simpa [monitored] using
      (GameTheory.KernelGame.RealizedActionRepeatedAdapter.expectedStagePayoff_toBehaviorProfile
        G.kernel monitored time who)
  rw [heq]
  exact hmem

/-! **Lemma 1(6), finite-horizon clause.**  Every expected average is a
barycenter of pure stage-payoff vectors.  A reusable convex-hull theorem
for the public-history adapter is the missing formal ingredient. -/
theorem lemma_1_Dn_subset_C (G : FiniteStageGame)
    (n : G.Horizon) :
    G.finiteFeasiblePayoffsOnHorizon n ⊆
      G.correlatedFeasiblePayoffs := by
  rintro _ ⟨profile, rfl⟩
  letI (who : G.Player) : Finite (G.repeatedGame.Act who) :=
    @Finite.of_fintype _ (G.finiteAction who)
  change (fun who ↦ G.repeatedGame.finiteAveragePayoff
    PUnit.unit n.1 profile who) ∈ G.correlatedFeasiblePayoffs
  rw [show (fun who ↦ G.repeatedGame.finiteAveragePayoff
    PUnit.unit n.1 profile who) =
      (n.1 : ℝ)⁻¹ • ∑ time ∈ Finset.range n.1,
        (fun who ↦ G.repeatedGame.expectedStagePayoff
          profile PUnit.unit time who) by
    funext who
    rw [G.repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]]
  rw [Finset.smul_sum]
  apply G.correlatedFeasiblePayoffs_convex.sum_mem
  · intro _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg n.1)
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    apply mul_inv_cancel₀
    exact_mod_cast Nat.ne_of_gt n.2
  · intro time htime
    exact expectedStagePayoff_mem_correlatedFeasiblePayoffs
      G profile time

/-! **Lemma 1(6), discounted clause.**  The geometric weighted average
is likewise a barycenter of pure stage-payoff vectors. -/
theorem lemma_1_Dlambda_subset_C (G : FiniteStageGame)
    (lam : G.DiscountRate) :
    G.discountedFeasiblePayoffsOnRate lam ⊆
      G.correlatedFeasiblePayoffs := by
  rintro _ ⟨profile, rfl⟩
  letI (who : G.Player) : Fintype (G.repeatedGame.Act who) :=
    G.finiteAction who
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  let parameter : unitInterval := ⟨lam.1, lam.2.1.le, lam.2.2⟩
  let timeLaw : PMF ℕ :=
    (ProbabilityTheory.geometricMeasure parameter).toPMF
  let actionLaw : ℕ → PMF G.repeatedGame.JointAct := fun time ↦
    (G.repeatedGame.histDist profile PUnit.unit time).bind
      (G.repeatedGame.stageActionDist profile)
  let discountedActionLaw : PMF G.repeatedGame.JointAct :=
    timeLaw.bind actionLaw
  have hhull :=
    Math.ProbabilityMassFunction.coordinateExpectation_mem_convexHull_range
      discountedActionLaw G.payoff
  change G.discountedPayoff lam.1 profile ∈
    convexHull ℝ (Set.range G.payoff)
  have heq : G.discountedPayoff lam.1 profile =
      fun who ↦ Math.Probability.expect discountedActionLaw
        (fun action ↦ G.payoff action who) := by
    funext who
    have hstage : ∀ time,
        Math.Probability.expect (actionLaw time)
          (fun action ↦ G.payoff action who) =
        G.repeatedGame.expectedStagePayoff
          profile PUnit.unit time who := by
      intro time
      rw [show actionLaw time =
        (G.repeatedGame.histDist profile PUnit.unit time).bind
          (G.repeatedGame.stageActionDist profile) by rfl]
      rw [Math.Probability.expect_bind]
      unfold StochasticGame.expectedStagePayoff StochasticGame.stageEUAt
      congr 1
      funext history
      congr 1
      funext action
      simp [FiniteStageGame.repeatedGame,
        KernelGame.realizedActionStochasticGame,
        FiniteStageGame.kernel, KernelGame.eu_ofPureEU]
    rw [show Math.Probability.expect discountedActionLaw
        (fun action ↦ G.payoff action who) =
      Math.Probability.expect timeLaw (fun time ↦
        Math.Probability.expect (actionLaw time)
          (fun action ↦ G.payoff action who)) by
      exact Math.Probability.expect_bind _ _ _]
    simp_rw [hstage]
    unfold FiniteStageGame.discountedPayoff
    unfold StochasticGame.discountedPayoff
    rw [show Math.Probability.expect timeLaw (fun time ↦
        G.repeatedGame.expectedStagePayoff profile PUnit.unit time who) =
      ∑' time : ℕ, (1 - lam.1) ^ time * lam.1 *
        G.repeatedGame.expectedStagePayoff profile PUnit.unit time who by
      unfold Math.Probability.expect timeLaw
      apply tsum_congr
      intro time
      rw [MeasureTheory.Measure.toPMF_apply]
      rw [← MeasureTheory.measureReal_def]
      rw [ProbabilityTheory.geometricMeasure_real_singleton]
      intro hzero
      have := congrArg ((↑) : unitInterval → ℝ) hzero
      simp [parameter] at this
      linarith [lam.2.1]]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro time
    ring
  rw [heq]
  exact hhull

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
  letI (who : G.Player) : Finite (G.kernel.Strategy who) :=
    @Finite.of_fintype _ (G.finiteAction who)
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ who, G.Action who)
    exact Finite.of_fintype _
  letI : Finite G.kernel.mixedExtension.Outcome :=
    G.kernel.finite_mixedExtension_outcome
  rintro payoff ⟨profile, hnash, rfl⟩
  let monitored :=
    G.kernel.realizedActionMonitoring.stationaryMonitoredProfile profile
  let behavior :=
    GameTheory.KernelGame.RealizedActionRepeatedAdapter.toBehaviorProfile
      G.kernel monitored
  refine ⟨behavior, ?_, ?_⟩
  · apply (KernelGame.RealizedActionRepeatedAdapter.isεFiniteRepeatedNash_iff_isεHorizonNash
      G.kernel monitored n.1 0).mp
    exact G.kernel.realizedActionMonitoring
      |>.stationaryMonitoredProfile_isFiniteRepeatedNash_of_isNash
        hnash n.2
  · funext who
    change G.repeatedGame.finiteAveragePayoff
      PUnit.unit n.1 behavior who = G.mixedPayoff profile who
    rw [GameTheory.KernelGame.RealizedActionRepeatedAdapter.finiteAveragePayoff_toBehaviorProfile]
    exact G.kernel.realizedActionMonitoring
      |>.finiteAveragePayoff_stationaryMonitoredProfile
        (Nat.ne_of_gt n.2) profile who

/-- At horizon one, behavioral and mixed equilibrium payoff sets coincide. -/
theorem finiteEquilibriumPayoffs_one_eq_oneStageEquilibriumPayoffs
    (G : FiniteStageGame) :
    G.finiteEquilibriumPayoffs 1 = G.oneStageEquilibriumPayoffs := by
  apply Set.Subset.antisymm
  · rintro payoff ⟨behavior, hnash, rfl⟩
    let profile := G.initialMixedProfile behavior
    refine ⟨profile, ?_, ?_⟩
    · intro who deviation
      let behaviorDeviation : G.BehaviorStrategy who :=
        fun _time _history ↦ deviation
      have hequilibrium := hnash who behaviorDeviation
      have hupdate :
          G.initialMixedProfile
              (Function.update behavior who behaviorDeviation) =
            Function.update profile who deviation := by
        funext player
        by_cases hplayer : player = who
        · subst player
          simp [FiniteStageGame.initialMixedProfile, behaviorDeviation]
        · simp [FiniteStageGame.initialMixedProfile, profile, hplayer]
      change G.finitePayoff 1 behavior who + 0 ≥
        G.finitePayoff 1
          (Function.update behavior who behaviorDeviation) who at hequilibrium
      rw [finitePayoff_one_eq_mixedPayoff_initial G behavior,
        finitePayoff_one_eq_mixedPayoff_initial G
          (Function.update behavior who behaviorDeviation), hupdate] at hequilibrium
      simpa [FiniteStageGame.mixedPayoff, profile] using hequilibrium
    · exact (finitePayoff_one_eq_mixedPayoff_initial G behavior).symm
  · exact lemma_1_E1_subset_En G ⟨1, by omega⟩

/-! **Lemma 1(8), discounted inclusion.** -/
theorem lemma_1_E1_subset_Elambda (G : FiniteStageGame)
    (lam : G.DiscountRate) :
    G.oneStageEquilibriumPayoffs ⊆
      G.discountedEquilibriumPayoffsOnRate lam := by
  letI (who : G.Player) : Finite (G.repeatedGame.Act who) :=
    @Finite.of_fintype _ (G.finiteAction who)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  letI : Subsingleton G.repeatedGame.State :=
    inferInstanceAs (Subsingleton PUnit)
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ who, G.Action who)
    exact Finite.of_fintype _
  rintro payoff ⟨profile, hnash, rfl⟩
  let behavior := G.repeatedGame.stationaryBehaviorProfile profile
  have habs : G.repeatedGame.IsAbsorbingState PUnit.unit :=
    G.repeatedGame.isAbsorbingState_of_subsingleton PUnit.unit
  have hstage : ∀ who (deviation : PMF (G.Action who)),
      G.repeatedGame.mixedStageEU PUnit.unit
          (Function.update profile who deviation) who ≤
        G.repeatedGame.mixedStageEU PUnit.unit profile who := by
    intro who deviation
    let deviation' : PMF (G.kernel.Strategy who) := deviation
    change Math.Probability.expect
        (Math.PMFProduct.pmfPi (Function.update profile who deviation'))
          (fun action ↦ G.kernel.eu action who) ≤
      Math.Probability.expect (Math.PMFProduct.pmfPi profile)
        (fun action ↦ G.kernel.eu action who)
    calc
      _ = G.kernel.mixedExtension.eu
          (Function.update profile who deviation') who :=
        (G.kernel.mixedExtension_eu
          (Function.update profile who deviation') who).symm
      _ ≤ G.kernel.mixedExtension.eu profile who := hnash who deviation'
      _ = _ := G.kernel.mixedExtension_eu profile who
  refine ⟨behavior, ?_, ?_⟩
  · exact G.repeatedGame
      |>.stationaryBehaviorProfile_isDiscountedNash_of_isAbsorbingState
        habs hstage (by linarith [lam.2.2]) (by linarith [lam.2.1])
  · funext who
    change G.repeatedGame.discountedPayoff (1 - lam.1)
      behavior PUnit.unit who = G.mixedPayoff profile who
    rw [G.repeatedGame.discountedPayoff_stationaryBehaviorProfile_of_isAbsorbingState
      habs profile (by linarith [lam.2.2]) (by linarith [lam.2.1])]
    change Math.Probability.expect (Math.PMFProduct.pmfPi profile)
        (fun action ↦ G.kernel.eu action who) =
      G.kernel.mixedExtension.eu profile who
    rw [G.kernel.mixedExtension_eu]

/-- The history-by-history pure best reply earns at least the paper's
individual-rational level in the current stage. -/
theorem stageEUAt_individualRationalDeviation_ge
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) {time : ℕ} (history : G.repeatedGame.Hist time) :
    G.individualRationalLevel who ≤
      G.repeatedGame.stageEUAt
        (Function.update profile who
          (G.individualRationalDeviation profile who)) history who := by
  letI (player : G.Player) : Fintype (G.kernel.Strategy player) :=
    G.finiteAction player
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ player, G.Action player)
    exact Finite.of_fintype _
  let current : G.MixedProfile := fun player ↦
    (Function.update profile who
      (G.individualRationalDeviation profile who)) player time history
  have hcurrent : current =
      G.kernel.mixedExtension.profileWithOpponent who
        (PMF.pure (G.individualRationalReply profile who history))
        (G.opponentsAt profile who history) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [current, FiniteStageGame.individualRationalDeviation]
      rfl
    · simp [current, KernelGame.profileWithOpponent,
        FiniteStageGame.opponentsAt, hplayer]
  have hreply := G.individualRationalReply_spec profile who history
  rw [← hcurrent] at hreply
  unfold StochasticGame.stageEUAt
  change G.individualRationalLevel who ≤
    Math.Probability.expect (Math.PMFProduct.pmfPi current)
      (fun action ↦ G.kernel.eu action who)
  rw [← G.kernel.mixedExtension_eu]
  exact hreply

/-- The selected deviation earns at least the individual-rational level in
every period. -/
theorem expectedStagePayoff_individualRationalDeviation_ge
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) (time : ℕ) :
    G.individualRationalLevel who ≤
      G.repeatedGame.expectedStagePayoff
        (Function.update profile who
          (G.individualRationalDeviation profile who))
        PUnit.unit time who := by
  letI (player : G.Player) : Finite (G.repeatedGame.Act player) :=
    @Finite.of_fintype _ (G.finiteAction player)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  unfold StochasticGame.expectedStagePayoff
  rw [← Math.Probability.expect_const
    (G.repeatedGame.histDist
      (Function.update profile who
        (G.individualRationalDeviation profile who))
      PUnit.unit time) (G.individualRationalLevel who)]
  apply Math.Probability.expect_mono
  intro history
  exact stageEUAt_individualRationalDeviation_ge
    G profile who history

/-- The deviation's positive-horizon average is at least the
individual-rational level. -/
theorem finiteAveragePayoff_individualRationalDeviation_ge
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) (horizon : G.Horizon) :
    G.individualRationalLevel who ≤
      G.repeatedGame.finiteAveragePayoff PUnit.unit horizon.1
        (Function.update profile who
          (G.individualRationalDeviation profile who)) who := by
  letI (player : G.Player) : Finite (G.repeatedGame.Act player) :=
    @Finite.of_fintype _ (G.finiteAction player)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  rw [G.repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  have hnonneg : 0 ≤ (horizon.1 : ℝ)⁻¹ := by positivity
  calc
    G.individualRationalLevel who =
        (horizon.1 : ℝ)⁻¹ * ∑ _time ∈ Finset.range horizon.1,
          G.individualRationalLevel who := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀]
      · simp
      · exact_mod_cast Nat.ne_of_gt horizon.2
    _ ≤ (horizon.1 : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon.1,
        G.repeatedGame.expectedStagePayoff
          (Function.update profile who
            (G.individualRationalDeviation profile who))
          PUnit.unit time who := by
      apply mul_le_mul_of_nonneg_left _ hnonneg
      apply Finset.sum_le_sum
      intro time _
      exact expectedStagePayoff_individualRationalDeviation_ge
        G profile who time

/-- The same deviation earns at least the individual-rational level under
every paper discount rate. -/
theorem discountedPayoff_individualRationalDeviation_ge
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) (lam : G.DiscountRate) :
    G.individualRationalLevel who ≤
      G.repeatedGame.discountedPayoff (1 - lam.1)
        (Function.update profile who
          (G.individualRationalDeviation profile who))
        PUnit.unit who := by
  letI (player : G.Player) : Finite (G.repeatedGame.Act player) :=
    @Finite.of_fintype _ (G.finiteAction player)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  obtain ⟨C, hC⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun pair : G.repeatedGame.State × G.repeatedGame.JointAct ↦
      G.repeatedGame.stagePayoff pair.1 pair.2 who)
  apply G.repeatedGame.discountedPayoff_ge_of_forall_expectedStagePayoff_ge
    (fun state action ↦ hC (state, action))
    (fun time ↦ expectedStagePayoff_individualRationalDeviation_ge
      G profile who time)
  · linarith [lam.2.2]
  · linarith [lam.2.1]

/-! **Lemma 1(8), finite individual-rationality clause.**  At every
public history a player can switch to a stagewise security strategy;
the conditional-history construction is not yet packaged. -/
theorem lemma_1_En_subset_Delta (G : FiniteStageGame)
    (n : G.Horizon) :
    G.finiteEquilibriumPayoffsOnHorizon n ⊆
      G.individuallyRationalPayoffs := by
  rintro payoff ⟨profile, hnash, rfl⟩
  constructor
  · exact lemma_1_Dn_subset_C G n ⟨profile, rfl⟩
  · intro who
    let deviation := G.individualRationalDeviation profile who
    have hequilibrium := hnash who deviation
    have hdeviation :=
      finiteAveragePayoff_individualRationalDeviation_ge
        G profile who n
    change G.individualRationalLevel who ≤
      G.finitePayoff n.1 profile who
    change G.finitePayoff n.1 profile who + 0 ≥
      G.finitePayoff n.1
        (Function.update profile who deviation) who at hequilibrium
    have hequilibrium' :
        G.repeatedGame.finiteAveragePayoff PUnit.unit n.1
            (Function.update profile who
              (G.individualRationalDeviation profile who)) who ≤
          G.finitePayoff n.1 profile who := by
      simpa [deviation, FiniteStageGame.finitePayoff] using hequilibrium
    exact hdeviation.trans hequilibrium'

/-! **Lemma 1(8), discounted individual-rationality clause.** -/
theorem lemma_1_Elambda_subset_Delta (G : FiniteStageGame)
    (lam : G.DiscountRate) :
    G.discountedEquilibriumPayoffsOnRate lam ⊆
      G.individuallyRationalPayoffs := by
  rintro payoff ⟨profile, hnash, rfl⟩
  constructor
  · exact lemma_1_Dlambda_subset_C G lam ⟨profile, rfl⟩
  · intro who
    let deviation := G.individualRationalDeviation profile who
    have hequilibrium := hnash who deviation
    have hdeviation :=
      discountedPayoff_individualRationalDeviation_ge
        G profile who lam
    change G.individualRationalLevel who ≤
      G.discountedPayoff lam.1 profile who
    change G.repeatedGame.discountedPayoff (1 - lam.1)
        profile PUnit.unit who + 0 ≥
      G.repeatedGame.discountedPayoff (1 - lam.1)
        (Function.update profile who deviation) PUnit.unit who at hequilibrium
    have hequilibrium' :
        G.repeatedGame.discountedPayoff (1 - lam.1)
            (Function.update profile who
              (G.individualRationalDeviation profile who))
            PUnit.unit who ≤
          G.discountedPayoff lam.1 profile who := by
      simpa [deviation, FiniteStageGame.discountedPayoff] using hequilibrium
    exact hdeviation.trans hequilibrium'

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

/-- If independent one-stage mixing already fills the correlated feasible
hull, then every positive finite horizon has that same feasible set. -/
theorem finiteFeasiblePayoffs_eq_correlated_of_oneStage_eq
    (G : FiniteStageGame)
    (hone : G.oneStageFeasiblePayoffs = G.correlatedFeasiblePayoffs)
    (horizon : G.Horizon) :
    G.finiteFeasiblePayoffsOnHorizon horizon =
      G.correlatedFeasiblePayoffs := by
  apply Set.Subset.antisymm
  · exact lemma_1_Dn_subset_C G horizon
  · rw [← hone]
    exact lemma_1_D1_subset_Dn G horizon

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

/-! Immediately after Lemma 2 the paper states that its convergence result
does not extend to perfect equilibria and cites Fudenberg--Maskin [5]. The
counterexample is not printed, so its existence remains unproved here. -/
theorem reported_perfect_equilibrium_failure :
    ∃ G : FiniteStageGame,
      ¬HausdorffConvergesAtZero
        G.perfectPublicEquilibriumPayoffs
        G.individuallyRationalPayoffs := by
  sorry

/-! Lemma 3 is block concatenation.  The feasible clause uses the exact
public-history dispatcher below; the equilibrium clause additionally requires
the corresponding decomposition of unilateral deviations. -/

/-- Play `prefix` for `fuel` periods and then restart `suffix` after the
realized public prefix. -/
noncomputable def FiniteStageGame.appendFiniteProfiles
    (G : FiniteStageGame) (fuel : ℕ)
    (prefixProfile suffixProfile : G.BehaviorProfile) : G.BehaviorProfile :=
  G.repeatedGame.terminalChildDispatcher fuel prefixProfile
    (fun _ => suffixProfile)

private theorem appendFiniteProfiles_agreeBefore
    (G : FiniteStageGame) (fuel : ℕ)
    (prefixProfile suffixProfile : G.BehaviorProfile) :
    G.repeatedGame.ProfilesAgreeBefore
      (G.appendFiniteProfiles fuel prefixProfile suffixProfile)
      prefixProfile fuel := by
  intro who time history htime
  exact G.repeatedGame.terminalChildDispatcher_before
    prefixProfile (fun _ => suffixProfile) htime who history

private theorem expectedStagePayoff_eq_of_profilesAgreeBefore
    (G : FiniteStageGame) {left right : G.BehaviorProfile}
    {fuel time : ℕ}
    (hagree : G.repeatedGame.ProfilesAgreeBefore left right fuel)
    (htime : time < fuel) (who : G.Player) :
    G.repeatedGame.expectedStagePayoff left G.repeatedInitial time who =
      G.repeatedGame.expectedStagePayoff right G.repeatedInitial time who := by
  unfold StochasticGame.expectedStagePayoff
  rw [G.repeatedGame.histDist_eq_of_profilesAgreeBefore
    hagree time htime.le]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro history _
  unfold StochasticGame.stageEUAt
  rw [G.repeatedGame.stageActionDist_eq_of_profilesAgreeBefore
    hagree history htime]

private theorem expectedStagePayoff_add_eq_expect_afterHistory
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (prefixLength suffixLength : ℕ) (who : G.Player) :
    G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
        (prefixLength + suffixLength) who =
      Math.Probability.expect
        (G.repeatedGame.histDist profile G.repeatedInitial prefixLength) fun base =>
          G.repeatedGame.expectedStagePayoff
            (G.repeatedGame.afterHistoryProfile profile base) base.2
            suffixLength who := by
  unfold StochasticGame.expectedStagePayoff
  rw [G.repeatedGame.histDist_add_eq_bind_histDistAfter,
    Math.Probability.expect_bind]
  apply congrArg
  funext base
  unfold StochasticGame.histDistAfter
  rw [Math.Probability.expect_map]
  rfl

private theorem appendFiniteProfiles_expectedStagePayoff_add
    (G : FiniteStageGame) (fuel time : ℕ)
    (prefixProfile suffixProfile : G.BehaviorProfile) (who : G.Player) :
    G.repeatedGame.expectedStagePayoff
        (G.appendFiniteProfiles fuel prefixProfile suffixProfile)
        G.repeatedInitial
        (fuel + time) who =
      G.repeatedGame.expectedStagePayoff suffixProfile
        G.repeatedInitial time who := by
  rw [expectedStagePayoff_add_eq_expect_afterHistory]
  have hpoint : ∀ base : G.repeatedGame.Hist fuel,
      G.repeatedGame.expectedStagePayoff
          (G.repeatedGame.afterHistoryProfile
            (G.appendFiniteProfiles fuel prefixProfile suffixProfile) base)
          base.2 time who =
        G.repeatedGame.expectedStagePayoff suffixProfile
          G.repeatedInitial time who := by
    intro base
    unfold FiniteStageGame.appendFiniteProfiles
    rw [G.repeatedGame.afterHistoryProfile_terminalChildDispatcher_canonical]
    rw [G.repeatedGame.expectedStagePayoff_canonicalTerminalChildProfile]
    cases base.2
    rfl
  simp_rw [hpoint]
  exact Math.Probability.expect_const _ _

private theorem cast_smul_finitePayoff_eq_sum
    (G : FiniteStageGame) (horizon : ℕ)
    (profile : G.BehaviorProfile) :
    (horizon : ℝ) • G.finitePayoff horizon profile =
      ∑ time ∈ Finset.range horizon,
        (fun who => G.repeatedGame.expectedStagePayoff
          profile G.repeatedInitial time who) := by
  funext who
  change (horizon : ℝ) *
      G.repeatedGame.finiteAveragePayoff PUnit.unit horizon profile who = _
  rw [G.repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simp only [Finset.sum_apply]
  by_cases hzero : horizon = 0
  · subst horizon
    simp
  · rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hzero), one_mul]

private theorem appendFiniteProfiles_weightedPayoff
    (G : FiniteStageGame) (prefixLength suffixLength : ℕ)
    (prefixProfile suffixProfile : G.BehaviorProfile) :
    ((prefixLength + suffixLength : ℕ) : ℝ) •
        G.finitePayoff (prefixLength + suffixLength)
          (G.appendFiniteProfiles prefixLength prefixProfile suffixProfile) =
      (prefixLength : ℝ) • G.finitePayoff prefixLength prefixProfile +
        (suffixLength : ℝ) • G.finitePayoff suffixLength suffixProfile := by
  rw [cast_smul_finitePayoff_eq_sum, cast_smul_finitePayoff_eq_sum,
    cast_smul_finitePayoff_eq_sum, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro time htime
    funext who
    exact expectedStagePayoff_eq_of_profilesAgreeBefore G
      (appendFiniteProfiles_agreeBefore G prefixLength
        prefixProfile suffixProfile)
      (Finset.mem_range.mp htime) who
  · apply Finset.sum_congr rfl
    intro time _
    funext who
    exact appendFiniteProfiles_expectedStagePayoff_add
      G prefixLength time prefixProfile suffixProfile who

private theorem sum_expect_comm_range {Ω : Type} [Finite Ω]
    (law : PMF Ω) (length : ℕ) (value : ℕ → Ω → ℝ) :
    (∑ time ∈ Finset.range length,
        Math.Probability.expect law (value time)) =
      Math.Probability.expect law fun outcome =>
        ∑ time ∈ Finset.range length, value time outcome := by
  letI : Fintype Ω := Fintype.ofFinite Ω
  simp only [Math.Probability.expect_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome _
  rw [Finset.mul_sum]

private theorem appendFiniteProfiles_isHorizonNash
    (G : FiniteStageGame) (prefixLength suffixLength : ℕ)
    (prefixProfile suffixProfile : G.BehaviorProfile)
    (hprefix : G.repeatedGame.IsεHorizonNash G.repeatedInitial
      prefixLength 0 prefixProfile)
    (hsuffix : G.repeatedGame.IsεHorizonNash G.repeatedInitial
      suffixLength 0 suffixProfile) :
    G.repeatedGame.IsεHorizonNash G.repeatedInitial
      (prefixLength + suffixLength) 0
      (G.appendFiniteProfiles prefixLength prefixProfile suffixProfile) := by
  intro who deviation
  simp only [add_zero]
  let joined := G.appendFiniteProfiles prefixLength prefixProfile suffixProfile
  let deviated := Function.update joined who deviation
  let prefixDeviation := Function.update prefixProfile who deviation
  have hprefixStages :
      (∑ time ∈ Finset.range prefixLength,
          G.repeatedGame.expectedStagePayoff
            deviated G.repeatedInitial time who) =
        ∑ time ∈ Finset.range prefixLength,
          G.repeatedGame.expectedStagePayoff
            prefixDeviation G.repeatedInitial time who := by
    apply Finset.sum_congr rfl
    intro time htime
    exact expectedStagePayoff_eq_of_profilesAgreeBefore G
      ((appendFiniteProfiles_agreeBefore G prefixLength
        prefixProfile suffixProfile).update who deviation)
      (Finset.mem_range.mp htime) who
  have hprefixBound :
      (∑ time ∈ Finset.range prefixLength,
          G.repeatedGame.expectedStagePayoff
            deviated G.repeatedInitial time who) ≤
        (prefixLength : ℝ) *
          G.repeatedGame.finiteAveragePayoff G.repeatedInitial
            prefixLength prefixProfile who := by
    have hnash := hprefix who deviation
    simp only [add_zero] at hnash
    have hscaled := mul_le_mul_of_nonneg_left hnash
      (Nat.cast_nonneg prefixLength : (0 : ℝ) ≤ prefixLength)
    have hdeviation := congrFun
      (cast_smul_finitePayoff_eq_sum G prefixLength prefixDeviation) who
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hdeviation
    change (prefixLength : ℝ) *
      G.repeatedGame.finiteAveragePayoff G.repeatedInitial
        prefixLength prefixDeviation who = _ at hdeviation
    rw [hprefixStages, ← hdeviation]
    exact hscaled
  let suffixLaw := G.repeatedGame.histDist deviated
    G.repeatedInitial prefixLength
  have hsuffixStage : ∀ time,
      G.repeatedGame.expectedStagePayoff deviated G.repeatedInitial
          (prefixLength + time) who =
        Math.Probability.expect suffixLaw fun base =>
          G.repeatedGame.expectedStagePayoff
            (Function.update suffixProfile who
              (G.repeatedGame.afterHistoryStrategy deviation base))
            G.repeatedInitial time who := by
    intro time
    rw [expectedStagePayoff_add_eq_expect_afterHistory]
    apply Math.ProbabilityMassFunction.expect_congr_on_support
    intro base _
    have hprofile :=
      G.repeatedGame.afterHistoryProfile_update_terminalChildDispatcher_canonical
        prefixLength prefixProfile (fun _ => suffixProfile) base who deviation
    change G.repeatedGame.afterHistoryProfile deviated base = _ at hprofile
    rw [hprofile]
    rw [G.repeatedGame.expectedStagePayoff_update_canonicalTerminalChildProfile]
    cases base.2
    rfl
  have hsuffixPointwise : ∀ base : G.repeatedGame.Hist prefixLength,
      (∑ time ∈ Finset.range suffixLength,
          G.repeatedGame.expectedStagePayoff
            (Function.update suffixProfile who
              (G.repeatedGame.afterHistoryStrategy deviation base))
            G.repeatedInitial time who) ≤
        (suffixLength : ℝ) *
          G.repeatedGame.finiteAveragePayoff G.repeatedInitial
            suffixLength suffixProfile who := by
    intro base
    have hnash := hsuffix who
      (G.repeatedGame.afterHistoryStrategy deviation base)
    simp only [add_zero] at hnash
    have hscaled := mul_le_mul_of_nonneg_left hnash
      (Nat.cast_nonneg suffixLength : (0 : ℝ) ≤ suffixLength)
    let localDeviation := Function.update suffixProfile who
      (G.repeatedGame.afterHistoryStrategy deviation base)
    have hdeviation := congrFun
      (cast_smul_finitePayoff_eq_sum G suffixLength localDeviation) who
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hdeviation
    change (suffixLength : ℝ) *
      G.repeatedGame.finiteAveragePayoff G.repeatedInitial
        suffixLength localDeviation who = _ at hdeviation
    change (∑ time ∈ Finset.range suffixLength,
      G.repeatedGame.expectedStagePayoff
        localDeviation G.repeatedInitial time who) ≤ _
    rw [← hdeviation]
    exact hscaled
  have hsuffixBound :
      (∑ time ∈ Finset.range suffixLength,
          G.repeatedGame.expectedStagePayoff deviated G.repeatedInitial
            (prefixLength + time) who) ≤
        (suffixLength : ℝ) *
          G.repeatedGame.finiteAveragePayoff G.repeatedInitial
            suffixLength suffixProfile who := by
    simp_rw [hsuffixStage]
    rw [sum_expect_comm_range]
    calc
      Math.Probability.expect suffixLaw (fun base =>
          ∑ time ∈ Finset.range suffixLength,
            G.repeatedGame.expectedStagePayoff
              (Function.update suffixProfile who
                (G.repeatedGame.afterHistoryStrategy deviation base))
              G.repeatedInitial time who) ≤
          Math.Probability.expect suffixLaw (fun _ =>
            (suffixLength : ℝ) *
              G.repeatedGame.finiteAveragePayoff G.repeatedInitial
                suffixLength suffixProfile who) := by
        apply Math.Probability.expect_mono
        exact hsuffixPointwise
      _ = _ := Math.Probability.expect_const _ _
  by_cases hzero : prefixLength + suffixLength = 0
  · have hprefixZero : prefixLength = 0 := by omega
    have hsuffixZero : suffixLength = 0 := by omega
    subst prefixLength
    subst suffixLength
    rw [G.repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff,
      G.repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    simp
  · have hdeviated := congrFun
      (cast_smul_finitePayoff_eq_sum G (prefixLength + suffixLength) deviated) who
    have hjoint := congrFun
      (appendFiniteProfiles_weightedPayoff G prefixLength suffixLength
        prefixProfile suffixProfile) who
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      Finset.sum_apply] at hdeviated hjoint
    change ((prefixLength + suffixLength : ℕ) : ℝ) *
      G.repeatedGame.finiteAveragePayoff G.repeatedInitial
        (prefixLength + suffixLength) deviated who = _ at hdeviated
    change ((prefixLength + suffixLength : ℕ) : ℝ) *
      G.repeatedGame.finiteAveragePayoff G.repeatedInitial
        (prefixLength + suffixLength) joined who = _ at hjoint
    rw [Finset.sum_range_add] at hdeviated
    have hweighted :
        ((prefixLength + suffixLength : ℕ) : ℝ) *
            G.repeatedGame.finiteAveragePayoff G.repeatedInitial
              (prefixLength + suffixLength) deviated who ≤
          ((prefixLength + suffixLength : ℕ) : ℝ) *
            G.repeatedGame.finiteAveragePayoff G.repeatedInitial
              (prefixLength + suffixLength) joined who := by
      rw [hdeviated, hjoint]
      exact add_le_add hprefixBound hsuffixBound
    have hpositive : (0 : ℝ) < ((prefixLength + suffixLength : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    nlinarith

/-- Concatenate a list of equal-length blocks in chronological order, then
play one residual profile. -/
noncomputable def FiniteStageGame.appendFiniteProfileList
    (G : FiniteStageGame) (blockLength : ℕ) :
    List G.BehaviorProfile → G.BehaviorProfile → G.BehaviorProfile
  | [], residual => residual
  | profile :: profiles, residual =>
      G.appendFiniteProfiles blockLength profile
        (G.appendFiniteProfileList blockLength profiles residual)

private theorem appendFiniteProfileList_weightedPayoff
    (G : FiniteStageGame) (blockLength residualLength : ℕ)
    (profiles : List G.BehaviorProfile) (residual : G.BehaviorProfile) :
    ((profiles.length * blockLength + residualLength : ℕ) : ℝ) •
        G.finitePayoff (profiles.length * blockLength + residualLength)
          (G.appendFiniteProfileList blockLength profiles residual) =
      (profiles.map fun profile =>
        (blockLength : ℝ) • G.finitePayoff blockLength profile).sum +
        (residualLength : ℝ) •
          G.finitePayoff residualLength residual := by
  induction profiles with
  | nil =>
      simp only [List.length_nil, zero_mul, zero_add, List.map_nil,
        List.sum_nil, zero_add, FiniteStageGame.appendFiniteProfileList]
  | cons profile profiles ih =>
      have hlength : (profile :: profiles).length * blockLength + residualLength =
          blockLength + (profiles.length * blockLength + residualLength) := by
        simp only [List.length_cons, Nat.succ_mul]
        omega
      rw [hlength, FiniteStageGame.appendFiniteProfileList,
        appendFiniteProfiles_weightedPayoff, ih]
      simp only [List.map_cons, List.sum_cons]
      abel

private theorem appendFiniteProfileList_isHorizonNash
    (G : FiniteStageGame) (blockLength residualLength : ℕ)
    (profiles : List G.BehaviorProfile) (residual : G.BehaviorProfile)
    (hprofiles : ∀ profile ∈ profiles,
      G.repeatedGame.IsεHorizonNash G.repeatedInitial
        blockLength 0 profile)
    (hresidual : G.repeatedGame.IsεHorizonNash G.repeatedInitial
      residualLength 0 residual) :
    G.repeatedGame.IsεHorizonNash G.repeatedInitial
      (profiles.length * blockLength + residualLength) 0
      (G.appendFiniteProfileList blockLength profiles residual) := by
  induction profiles generalizing residual with
  | nil =>
      simpa [FiniteStageGame.appendFiniteProfileList] using hresidual
  | cons profile profiles ih =>
      have hlength : (profile :: profiles).length * blockLength + residualLength =
          blockLength + (profiles.length * blockLength + residualLength) := by
        simp only [List.length_cons, Nat.succ_mul]
        omega
      rw [hlength, FiniteStageGame.appendFiniteProfileList]
      apply appendFiniteProfiles_isHorizonNash
      · exact hprofiles profile (by simp)
      · apply ih
        · intro candidate hcandidate
          exact hprofiles candidate (by simp [hcandidate])
        · exact hresidual

theorem lemma_3_feasible (G : FiniteStageGame)
    (n m p r : ℕ) (hn : n = m * p + r) :
    addSet (iteratedAddSet m (scaleSet (p : ℝ) (G.finiteFeasiblePayoffs p)))
        (scaleSet (r : ℝ) (G.finiteFeasiblePayoffs r)) ⊆
      scaleSet (n : ℝ) (G.finiteFeasiblePayoffs n) := by
  classical
  rintro z ⟨blockTotal, hblockTotal, residualTotal, hresidualTotal, hz⟩
  obtain ⟨blockPayoff, hblockPayoff, hblockTotalEq⟩ := hblockTotal
  have hexistsBlock : ∀ k, ∃ profile : G.BehaviorProfile,
      blockPayoff k = (p : ℝ) • G.finitePayoff p profile := by
    intro k
    obtain ⟨payoff, hpayoff, hscaled⟩ := hblockPayoff k
    obtain ⟨profile, hprofile⟩ := hpayoff
    refine ⟨profile, ?_⟩
    rw [hprofile]
    exact hscaled
  choose blockProfile hblockProfile using hexistsBlock
  obtain ⟨residualPayoff, hresidualPayoff, hresidualScaled⟩ :=
    hresidualTotal
  obtain ⟨residualProfile, hresidualProfile⟩ := hresidualPayoff
  have hresidual : residualTotal =
      (r : ℝ) • G.finitePayoff r residualProfile := by
    rw [hresidualProfile]
    exact hresidualScaled
  let profiles := List.ofFn blockProfile
  let joined := G.appendFiniteProfileList p profiles residualProfile
  have hlist :
      (profiles.map fun profile =>
        (p : ℝ) • G.finitePayoff p profile).sum =
        ∑ k, blockPayoff k := by
    dsimp only [profiles]
    rw [List.map_ofFn, List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro k _
    exact (hblockProfile k).symm
  have hweighted := appendFiniteProfileList_weightedPayoff
    G p r profiles residualProfile
  rw [show profiles.length = m by simp [profiles], hlist, ← hresidual] at hweighted
  refine ⟨G.finitePayoff n joined, ⟨joined, rfl⟩, ?_⟩
  rw [hz, hblockTotalEq, hn]
  simpa only [joined] using hweighted.symm

/-! Equilibrium-block concatenation is the strategic clause of Lemma 3. -/
theorem lemma_3_equilibrium (G : FiniteStageGame)
    (n m p r : ℕ) (hn : n = m * p + r) :
    addSet (iteratedAddSet m (scaleSet (p : ℝ) (G.finiteEquilibriumPayoffs p)))
        (scaleSet (r : ℝ) (G.finiteEquilibriumPayoffs r)) ⊆
      scaleSet (n : ℝ) (G.finiteEquilibriumPayoffs n) := by
  classical
  rintro z ⟨blockTotal, hblockTotal, residualTotal, hresidualTotal, hz⟩
  obtain ⟨blockPayoff, hblockPayoff, hblockTotalEq⟩ := hblockTotal
  have hexistsBlock : ∀ k, ∃ profile : G.BehaviorProfile,
      G.repeatedGame.IsεHorizonNash G.repeatedInitial p 0 profile ∧
        blockPayoff k = (p : ℝ) • G.finitePayoff p profile := by
    intro k
    obtain ⟨payoff, hpayoff, hscaled⟩ := hblockPayoff k
    obtain ⟨profile, hnash, hprofile⟩ := hpayoff
    refine ⟨profile, hnash, ?_⟩
    rw [hprofile]
    exact hscaled
  choose blockProfile hblockNash hblockProfile using hexistsBlock
  obtain ⟨residualPayoff, hresidualPayoff, hresidualScaled⟩ :=
    hresidualTotal
  obtain ⟨residualProfile, hresidualNash, hresidualProfile⟩ :=
    hresidualPayoff
  have hresidual : residualTotal =
      (r : ℝ) • G.finitePayoff r residualProfile := by
    rw [hresidualProfile]
    exact hresidualScaled
  let profiles := List.ofFn blockProfile
  let joined := G.appendFiniteProfileList p profiles residualProfile
  have hprofilesNash : ∀ profile ∈ profiles,
      G.repeatedGame.IsεHorizonNash G.repeatedInitial p 0 profile := by
    intro profile hprofile
    rcases List.mem_ofFn.mp hprofile with ⟨k, rfl⟩
    exact hblockNash k
  have hjointNash : G.repeatedGame.IsεHorizonNash G.repeatedInitial
      (m * p + r) 0 joined := by
    simpa only [joined, profiles, List.length_ofFn] using
      appendFiniteProfileList_isHorizonNash G p r profiles residualProfile
        hprofilesNash hresidualNash
  have hlist :
      (profiles.map fun profile =>
        (p : ℝ) • G.finitePayoff p profile).sum =
        ∑ k, blockPayoff k := by
    dsimp only [profiles]
    rw [List.map_ofFn, List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro k _
    exact (hblockProfile k).symm
  have hweighted := appendFiniteProfileList_weightedPayoff
    G p r profiles residualProfile
  rw [show profiles.length = m by simp [profiles], hlist, ← hresidual] at hweighted
  refine ⟨G.finitePayoff n joined, ?_, ?_⟩
  · refine ⟨joined, ?_, rfl⟩
    rwa [hn]
  · rw [hz, hblockTotalEq, hn]
    simpa only [joined] using hweighted.symm

/-! Repeating one positive-horizon block is the zero-residual specialization
of Lemma 3.  The same scalar-cancellation argument serves feasible and
equilibrium payoff sets. -/
private theorem subset_multiple_of_block_concatenation
    {ι : Type} (sets : ℕ → Set (Payoff ι))
    (concat : ∀ total m p r : ℕ, total = m * p + r →
      addSet (iteratedAddSet m (scaleSet (p : ℝ) (sets p)))
          (scaleSet (r : ℝ) (sets r)) ⊆
        scaleSet (total : ℝ) (sets total))
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    sets n ⊆ sets (k * n) := by
  intro z hz
  let block : Payoff ι := (n : ℝ) • z
  have hblock : block ∈ scaleSet (n : ℝ) (sets n) :=
    ⟨z, hz, rfl⟩
  have hblocks : ((k - 1 : ℕ) : ℝ) • block ∈
      iteratedAddSet (k - 1) (scaleSet (n : ℝ) (sets n)) := by
    refine ⟨fun _ => block, fun _ => hblock, ?_⟩
    ext who
    simp [Finset.sum_const, nsmul_eq_mul]
  have hjoined : ((k - 1 : ℕ) : ℝ) • block + block ∈
      addSet (iteratedAddSet (k - 1) (scaleSet (n : ℝ) (sets n)))
        (scaleSet (n : ℝ) (sets n)) :=
    ⟨((k - 1 : ℕ) : ℝ) • block, hblocks, block, hblock, rfl⟩
  have hkone : 1 ≤ k := by omega
  have hdecomp : k * n = (k - 1) * n + n := by
    calc
      k * n = ((k - 1) + 1) * n := by rw [Nat.sub_add_cancel hkone]
      _ = (k - 1) * n + n := by rw [Nat.add_mul, one_mul]
  obtain ⟨w, hw, heq⟩ :=
    concat (k * n) (k - 1) n n hdecomp hjoined
  have hkcast : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hkone).symm
  have htotal : ((k * n : ℕ) : ℝ) • z =
      ((k - 1 : ℕ) : ℝ) • block + block := by
    dsimp [block]
    ext who
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [Nat.cast_mul, hkcast]
    ring
  have hsmul : ((k * n : ℕ) : ℝ) • z =
      ((k * n : ℕ) : ℝ) • w :=
    htotal.trans heq
  have hwz : w = z := by
    apply Eq.symm
    exact smul_right_injective (Payoff ι) (by positivity) hsmul
  rwa [← hwz]

/-! Immediately after Lemma 3 the paper records the equal-block consequences
`Dₙ ⊆ Dₖₙ` and `Eₙ ⊆ Eₖₙ`.  Their proofs use the same monitored-profile
concatenation interface as Lemma 3. -/
theorem lemma_3_D_subset_multiple (G : FiniteStageGame)
    (n : G.Horizon) {k : ℕ} (hk : 0 < k) :
    G.finiteFeasiblePayoffsOnHorizon n ⊆
      G.finiteFeasiblePayoffs (k * n.1) := by
  apply subset_multiple_of_block_concatenation G.finiteFeasiblePayoffs
    (fun total m p r htotal =>
      lemma_3_feasible G total m p r htotal) n.1 k n.2 hk

theorem lemma_3_E_subset_multiple (G : FiniteStageGame)
    (n : G.Horizon) {k : ℕ} (hk : 0 < k) :
    G.finiteEquilibriumPayoffsOnHorizon n ⊆
      G.finiteEquilibriumPayoffs (k * n.1) := by
  apply subset_multiple_of_block_concatenation G.finiteEquilibriumPayoffs
    (fun total m p r htotal =>
      lemma_3_equilibrium G total m p r htotal) n.1 k n.2 hk

/-- A reverse block inclusion makes the original set stable under the fixed
ratio `1 / k`. -/
private theorem fixedRatio_mem_of_reverse_block_concatenation
    {Player : Type} (sets : ℕ → Set (Payoff Player))
    (concat : ∀ total m p r : ℕ, total = m * p + r →
      addSet (iteratedAddSet m (scaleSet (p : ℝ) (sets p)))
          (scaleSet (r : ℝ) (sets r)) ⊆
        scaleSet (total : ℝ) (sets total))
    (n k : ℕ) (hn : 0 < n) (hk : 1 < k)
    (hreverse : sets (k * n) ⊆ sets n) {x y : Payoff Player}
    (hx : x ∈ sets n) (hy : y ∈ sets n) :
    (k : ℝ)⁻¹ • x + (1 - (k : ℝ)⁻¹) • y ∈ sets n := by
  let xBlock : Payoff Player := (n : ℝ) • x
  let yBlock : Payoff Player := (n : ℝ) • y
  have hxBlock : xBlock ∈ scaleSet (n : ℝ) (sets n) :=
    ⟨x, hx, rfl⟩
  have hyBlock : yBlock ∈ scaleSet (n : ℝ) (sets n) :=
    ⟨y, hy, rfl⟩
  have hyBlocks : ((k - 1 : ℕ) : ℝ) • yBlock ∈
      iteratedAddSet (k - 1) (scaleSet (n : ℝ) (sets n)) := by
    refine ⟨fun _ ↦ yBlock, fun _ ↦ hyBlock, ?_⟩
    ext who
    simp [Finset.sum_const, nsmul_eq_mul]
  have hjoined : ((k - 1 : ℕ) : ℝ) • yBlock + xBlock ∈
      addSet (iteratedAddSet (k - 1) (scaleSet (n : ℝ) (sets n)))
        (scaleSet (n : ℝ) (sets n)) :=
    ⟨((k - 1 : ℕ) : ℝ) • yBlock, hyBlocks, xBlock, hxBlock, rfl⟩
  have hkone : 1 ≤ k := hk.le
  have hdecomp : k * n = (k - 1) * n + n := by
    calc
      k * n = ((k - 1) + 1) * n := by rw [Nat.sub_add_cancel hkone]
      _ = (k - 1) * n + n := by rw [Nat.add_mul, one_mul]
  obtain ⟨w, hw, heq⟩ :=
    concat (k * n) (k - 1) n n hdecomp hjoined
  let blend : Payoff Player :=
    (k : ℝ)⁻¹ • x + (1 - (k : ℝ)⁻¹) • y
  have hkReal : (k : ℝ) ≠ 0 := by positivity
  have htotal : ((k * n : ℕ) : ℝ) • blend =
      ((k - 1 : ℕ) : ℝ) • yBlock + xBlock := by
    ext who
    simp only [blend, xBlock, yBlock, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [Nat.cast_mul, Nat.cast_sub hkone, Nat.cast_one]
    field_simp
    ring
  have hscaled : ((k * n : ℕ) : ℝ) • blend =
      ((k * n : ℕ) : ℝ) • w := htotal.trans heq
  have hblend : blend = w :=
    smul_right_injective (Payoff Player) (by positivity) hscaled
  rw [show (k : ℝ)⁻¹ • x + (1 - (k : ℝ)⁻¹) • y = blend by rfl,
    hblend]
  exact hreverse hw

/-! The paper then notes that a reverse inclusion for one multiplier `k > 1`
forces convexity of the corresponding finite-horizon payoff set.  The closure
under a fixed nontrivial block ratio and closedness is supplied by
`MathUE.convex_of_isClosed_of_fixedRatio`. -/
theorem post_lemma_3_D_convex_of_reverse_multiple
    (G : FiniteStageGame) (n : G.Horizon) {k : ℕ} (hk : 1 < k)
    (hreverse : G.finiteFeasiblePayoffs (k * n.1) ⊆
      G.finiteFeasiblePayoffsOnHorizon n) :
    Convex ℝ (G.finiteFeasiblePayoffsOnHorizon n) := by
  apply MathUE.convex_of_isClosed_of_fixedRatio
      (property_1_finite G n).2.2.isClosed
      (c := (k : ℝ)⁻¹)
  · positivity
  · have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    rw [inv_lt_one₀ hkpos]
    exact_mod_cast hk
  · intro x hx y hy
    exact fixedRatio_mem_of_reverse_block_concatenation
      G.finiteFeasiblePayoffs
      (fun total m p r htotal ↦ lemma_3_feasible G total m p r htotal)
      n.1 k n.2 hk hreverse hx hy

theorem post_lemma_3_E_convex_of_reverse_multiple
    (G : FiniteStageGame) (n : G.Horizon) {k : ℕ} (hk : 1 < k)
    (hreverse : G.finiteEquilibriumPayoffs (k * n.1) ⊆
      G.finiteEquilibriumPayoffsOnHorizon n) :
    Convex ℝ (G.finiteEquilibriumPayoffsOnHorizon n) := by
  apply MathUE.convex_of_isClosed_of_fixedRatio
      (property_2_finite G n).2.isClosed
      (c := (k : ℝ)⁻¹)
  · positivity
  · have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    rw [inv_lt_one₀ hkpos]
    exact_mod_cast hk
  · intro x hx y hy
    exact fixedRatio_mem_of_reverse_block_concatenation
      G.finiteEquilibriumPayoffs
      (fun total m p r htotal ↦ lemma_3_equilibrium G total m p r htotal)
      n.1 k n.2 hk hreverse hx hy

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
abbrev binaryGame (topLeft topRight bottomLeft bottomRight : Payoff Bool) :
    FiniteStageGame where
  Player := Bool
  Action := fun _ => Bool
  payoff := binaryPayoff topLeft topRight bottomLeft bottomRight

/-- The independent mixed expected utility of a binary kernel, in the two
probabilities of playing `true`. -/
theorem binaryKernel_mixedEU_apply
    (topLeft topRight bottomLeft bottomRight : Payoff Bool)
    (profile : Bool → PMF Bool)
    (who : Bool) :
    (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
        (binaryPayoff topLeft topRight bottomLeft bottomRight)).mixedExtension.eu
      profile who =
      (profile false true).toReal *
          ((profile true true).toReal * bottomRight who +
            (1 - (profile true true).toReal) * bottomLeft who) +
        (1 - (profile false true).toReal) *
          ((profile true true).toReal * topRight who +
            (1 - (profile true true).toReal) * topLeft who) := by
  letI : Finite ((KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff topLeft topRight bottomLeft bottomRight)).Outcome) := by
    unfold KernelGame.ofPureEU
    infer_instance
  rw [KernelGame.mixedExtension_eu]
  simp only [KernelGame.eu_ofPureEU]
  change Math.Probability.expect (Math.PMFProduct.pmfPi profile)
      (fun action ↦ binaryPayoff topLeft topRight bottomLeft bottomRight action who) = _
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp [Math.Probability.expect_eq_sum,
    Math.PMFProduct.pmfBool_false_toReal, binaryPayoff]

/-- Paper-facing version of `binaryKernel_mixedEU_apply`. -/
theorem binaryGame_mixedPayoff_apply
    (topLeft topRight bottomLeft bottomRight : Payoff Bool)
    (profile : Bool → PMF Bool) (who : Bool) :
    (binaryGame topLeft topRight bottomLeft bottomRight).mixedPayoff profile who =
      (profile false true).toReal *
          ((profile true true).toReal * bottomRight who +
            (1 - (profile true true).toReal) * bottomLeft who) +
        (1 - (profile false true).toReal) *
          ((profile true true).toReal * topRight who +
            (1 - (profile true true).toReal) * topLeft who) :=
  binaryKernel_mixedEU_apply topLeft topRight bottomLeft bottomRight profile who

/-- Example 1. -/
abbrev example1 : FiniteStageGame :=
  binaryGame (pair 1 0) (pair 0 0) (pair 0 0) (pair 0 1)

/-- The top-left outcome is a one-stage Nash equilibrium of Example 1. -/
private theorem example1_topLeft_mem_E1 :
    pair 1 0 ∈ example1.oneStageEquilibriumPayoffs := by
  let profile : Bool → PMF Bool := fun _ ↦ PMF.pure false
  refine ⟨profile, ?_, ?_⟩
  · change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 1 0) (pair 0 0) (pair 0 0)
        (pair 0 1))).mixedExtension.IsNash profile
    intro who deviation
    cases who
    · rw [binaryKernel_mixedEU_apply, binaryKernel_mixedEU_apply]
      norm_num [example1, profile, pair]
    · rw [binaryKernel_mixedEU_apply, binaryKernel_mixedEU_apply]
      norm_num [example1, profile, pair]
  · change (binaryGame (pair 1 0) (pair 0 0) (pair 0 0)
      (pair 0 1)).mixedPayoff profile = pair 1 0
    funext who
    cases who <;> rw [binaryGame_mixedPayoff_apply] <;>
      norm_num [example1, profile, pair]

/-- The bottom-right outcome is a one-stage Nash equilibrium of Example 1. -/
private theorem example1_bottomRight_mem_E1 :
    pair 0 1 ∈ example1.oneStageEquilibriumPayoffs := by
  let profile : Bool → PMF Bool := fun _ ↦ PMF.pure true
  refine ⟨profile, ?_, ?_⟩
  · change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 1 0) (pair 0 0) (pair 0 0)
        (pair 0 1))).mixedExtension.IsNash profile
    intro who deviation
    cases who
    · rw [binaryKernel_mixedEU_apply, binaryKernel_mixedEU_apply]
      norm_num [example1, profile, pair]

    · rw [binaryKernel_mixedEU_apply, binaryKernel_mixedEU_apply]
      norm_num [example1, profile, pair]
      exact ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  · change (binaryGame (pair 1 0) (pair 0 0) (pair 0 0)
      (pair 0 1)).mixedPayoff profile = pair 0 1
    funext who
    cases who <;> rw [binaryGame_mixedPayoff_apply] <;>
      norm_num [example1, profile, pair]

/-- In Example 1, an independently mixed stage with total expected payoff one
must be one of the two pure diagonal outcomes. -/
theorem example1_mixedProfile_pure_diagonal_of_total_eq_one
    (profile : Bool → PMF Bool)
    (htotal :
      example1.mixedPayoff profile false +
        example1.mixedPayoff profile true = 1) :
    ∃ diagonal : Bool,
      profile false = PMF.pure diagonal ∧
        profile true = PMF.pure diagonal := by
  rw [binaryGame_mixedPayoff_apply, binaryGame_mixedPayoff_apply] at htotal
  norm_num [pair] at htotal
  let p := (profile false true).toReal
  let q := (profile true true).toReal
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  have hq1 : q ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  change (1 - p) * (1 - q) + p * q = 1 at htotal
  have hpq0 : p * (1 - q) = 0 := by
    nlinarith [mul_nonneg hp0 (by linarith : 0 ≤ 1 - q),
      mul_nonneg hq0 (by linarith : 0 ≤ 1 - p)]
  by_cases hp : p = 0
  · have hq : q = 0 := by nlinarith
    refine ⟨false, ?_, ?_⟩
    · exact Math.PMFProduct.eq_pure_false_of_true_toReal_eq_zero _ hp
    · exact Math.PMFProduct.eq_pure_false_of_true_toReal_eq_zero _ hq
  · have hq : q = 1 := by
      have := (mul_eq_zero.mp hpq0).resolve_left hp
      linarith
    have hp' : p = 1 := by nlinarith
    refine ⟨true, ?_, ?_⟩
    · exact Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one _ hp'
    · exact Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one _ hq

/-- At a public history, Example 1's stochastic stage expectation is its
one-stage mixed payoff at the current behavioral actions. -/
theorem example1_stageEUAt_eq_mixedPayoff
    (profile : example1.BehaviorProfile) {time : ℕ}
    (history : example1.repeatedGame.Hist time) (who : Bool) :
    example1.repeatedGame.stageEUAt profile history who =
      example1.mixedPayoff (fun player ↦ profile player time history) who := by
  letI : Finite example1.kernel.Outcome := by
    change Finite (Bool → Bool)
    exact Finite.of_fintype _
  unfold StochasticGame.stageEUAt StochasticGame.stageActionDist
  unfold FiniteStageGame.mixedPayoff KernelGame.payoffVector
  rw [example1.kernel.mixedExtension_eu]
  rfl

/-- Example 1's expected aggregate payoff is at most one in every stage. -/
theorem example1_expectedStageTotal_le_one
    (profile : example1.BehaviorProfile) (time : ℕ) :
    example1.repeatedGame.expectedStagePayoff profile PUnit.unit time false +
      example1.repeatedGame.expectedStagePayoff profile PUnit.unit time true ≤ 1 := by
  letI (player : Bool) : Finite (example1.repeatedGame.Act player) :=
    @Finite.of_fintype _ (example1.finiteAction player)
  letI : Finite example1.repeatedGame.State := inferInstanceAs (Finite PUnit)
  unfold StochasticGame.expectedStagePayoff
  rw [← Math.Probability.expect_add]
  rw [← Math.Probability.expect_const
    (example1.repeatedGame.histDist profile PUnit.unit time) (1 : ℝ)]
  apply Math.Probability.expect_mono
  intro history
  rw [example1_stageEUAt_eq_mixedPayoff,
    example1_stageEUAt_eq_mixedPayoff]
  rw [binaryGame_mixedPayoff_apply, binaryGame_mixedPayoff_apply]
  norm_num [pair]
  let p := (profile false time history true).toReal
  let q := (profile true time history true).toReal
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  have hq1 : q ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  change (1 - p) * (1 - q) + p * q ≤ 1
  nlinarith [mul_nonneg hp0 (by linarith : 0 ≤ 1 - q),
    mul_nonneg hq0 (by linarith : 0 ≤ 1 - p)]

/-- Example 2. -/
abbrev example2 : FiniteStageGame :=
  binaryGame (pair 1 0) (pair 2 2) (pair 0 0) (pair 0 1)

/-- Player `false`'s mixed payoff in Example 2. -/
theorem example2_mixedEU_false (profile : Bool → PMF Bool) :
    (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
        (pair 0 1))).mixedExtension.eu profile false =
      (1 - (profile false true).toReal) *
        (1 + (profile true true).toReal) := by
  rw [binaryKernel_mixedEU_apply]
  simp only [pair_false]
  ring

/-- Player `true`'s mixed payoff in Example 2. -/
theorem example2_mixedEU_true (profile : Bool → PMF Bool) :
    (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
        (pair 0 1))).mixedExtension.eu profile true =
      (profile true true).toReal * (2 - (profile false true).toReal) := by
  rw [binaryKernel_mixedEU_apply]
  simp only [pair_true]
  ring

/-- A pure-`false` row deviation in Example 2 earns `1 + q`. -/
theorem example2_mixedEU_update_false_pure
    (profile : Bool → PMF Bool) :
    (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
        (pair 0 1))).mixedExtension.eu
          (Function.update profile false (PMF.pure false)) false =
      1 + (profile true true).toReal := by
  rw [example2_mixedEU_false]
  change (1 - ((PMF.pure false) true).toReal) *
    (1 + (profile true true).toReal) = _
  simp

/-- A pure-`true` column deviation in Example 2 earns `2 - p`. -/
theorem example2_mixedEU_update_true_pure
    (profile : Bool → PMF Bool) :
    (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
        (pair 0 1))).mixedExtension.eu
          (Function.update profile true (PMF.pure true)) true =
      2 - (profile false true).toReal := by
  rw [example2_mixedEU_true]
  change ((PMF.pure true) true).toReal *
    (2 - (profile false true).toReal) = _
  simp

/-- An arbitrary row deviation changes only the row mixing probability. -/
theorem example2_mixedEU_update_false
    (profile : Bool → PMF Bool) (deviation : PMF Bool) :
    (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
        (pair 0 1))).mixedExtension.eu
          (Function.update profile false deviation) false =
      (1 - (deviation true).toReal) *
        (1 + (profile true true).toReal) := by
  rw [example2_mixedEU_false]
  change (1 - (deviation true).toReal) *
    (1 + (profile true true).toReal) = _
  rfl

/-- An arbitrary column deviation changes only the column mixing probability. -/
theorem example2_mixedEU_update_true
    (profile : Bool → PMF Bool) (deviation : PMF Bool) :
    (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
        (pair 0 1))).mixedExtension.eu
          (Function.update profile true deviation) true =
      (deviation true).toReal *
        (2 - (profile false true).toReal) := by
  rw [example2_mixedEU_true]
  change (deviation true).toReal *
    (2 - (profile false true).toReal) = _
  rfl

/-- Example 3. -/
def example3 : FiniteStageGame :=
  binaryGame (pair 1 0) (pair 1 1) (pair 0 0) (pair 1 0)

/-- Every correlated-feasible payoff of Example 3 has row payoff at most one
and column payoff between zero and one. -/
private theorem example3_correlated_bounds {v : Payoff Bool}
    (hv : v ∈ example3.correlatedFeasiblePayoffs) :
    v false ≤ 1 ∧ 0 ≤ v true ∧ v true ≤ 1 := by
  apply (convexHull_min (t := {w : Payoff Bool |
      w false ≤ 1 ∧ 0 ≤ w true ∧ w true ≤ 1}) ?_ ?_) hv
  · rintro _ ⟨action, rfl⟩
    change (Bool → Bool) at action
    change binaryPayoff (pair 1 0) (pair 1 1) (pair 0 0)
      (pair 1 0) action false ≤ 1 ∧
        0 ≤ binaryPayoff (pair 1 0) (pair 1 1) (pair 0 0)
          (pair 1 0) action true ∧
        binaryPayoff (pair 1 0) (pair 1 1) (pair 0 0)
          (pair 1 0) action true ≤ 1
    cases hrow : action false <;> cases hcolumn : action true <;>
      norm_num [binaryPayoff, hrow, hcolumn, pair]
  · intro x hx y hy a b ha hb hab
    rcases hx with ⟨hxrow, hxcolumn0, hxcolumn1⟩
    rcases hy with ⟨hyrow, hycolumn0, hycolumn1⟩
    constructor
    · change a * x false + b * y false ≤ 1
      nlinarith
    · constructor
      · change 0 ≤ a * x true + b * y true
        nlinarith
      · change a * x true + b * y true ≤ 1
        nlinarith

/-- The row player's one-stage security level in Example 3 is one. -/
private theorem example3_individualRationalLevel_false :
    example3.individualRationalLevel false = 1 := by
  let K := KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
    (binaryPayoff (pair 1 0) (pair 1 1) (pair 0 0) (pair 1 0))
  change (⨅ opponents : K.mixedExtension.OpponentProfile false,
      ⨆ action : Bool,
        K.mixedExtension.eu
          (K.mixedExtension.profileWithOpponent false
            (PMF.pure action) opponents) false) = 1
  have hlower (opponents : K.mixedExtension.OpponentProfile false) :
      1 ≤ ⨆ action : Bool,
        K.mixedExtension.eu
          (K.mixedExtension.profileWithOpponent false
            (PMF.pure action) opponents) false := by
    apply le_ciSup_of_le (Finite.bddAbove_range _) false
    let profile : Bool → PMF Bool :=
      K.mixedExtension.profileWithOpponent false (PMF.pure false) opponents
    change 1 ≤ K.mixedExtension.eu profile false
    rw [binaryKernel_mixedEU_apply]
    simp [profile, K, pair]
  have hbelow : BddBelow (Set.range fun opponents :
      K.mixedExtension.OpponentProfile false ↦
        ⨆ action : Bool,
          K.mixedExtension.eu
            (K.mixedExtension.profileWithOpponent false
              (PMF.pure action) opponents) false) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨opponents, rfl⟩
    exact hlower opponents
  apply le_antisymm
  · let opponents : K.mixedExtension.OpponentProfile false :=
      fun _ ↦ PMF.pure false
    apply ciInf_le_of_le hbelow opponents
    apply ciSup_le
    intro action
    let profile : Bool → PMF Bool :=
      K.mixedExtension.profileWithOpponent false (PMF.pure action) opponents
    change K.mixedExtension.eu profile false ≤ 1
    rw [binaryKernel_mixedEU_apply]
    cases action <;> simp [profile, opponents, K, pair]
  · letI : Nonempty (K.mixedExtension.OpponentProfile false) :=
      ⟨fun _ ↦ PMF.pure false⟩
    exact le_ciInf hlower

/-- Example 4, parameterized by the paper's positive integer `m`. -/
abbrev example4 (m : ℕ) : FiniteStageGame :=
  binaryGame (pair m 0) (pair (m + 1) (m + 1))
    (pair 0 0) (pair 0 m)

/-- Example 4's critical-horizon profile: play Bottom/Left initially, then
each player copies the opponent's initial action. -/
private def example4CriticalProfile (m : ℕ) :
    (example4 m).BehaviorProfile :=
  fun who time history =>
    match time with
    | 0 => PMF.pure (!who)
    | _ + 1 => PMF.pure ((history.1 0).2 (!who))

/-- If the opponent is pure in Example 4, a player's stage payoff is at most
`m` when the opponent copied that player, and at most `m+1` otherwise. -/
private theorem example4_mixedEU_le_of_opponent_pure
    (m : ℕ) (profile : Bool → PMF Bool) (who action : Bool)
    (hopponent : profile (!who) = PMF.pure action) :
    (example4 m).kernel.mixedExtension.eu profile who ≤
      if action = who then (m : ℝ) else m + 1 := by
  change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair m 0) (pair (m + 1) (m + 1))
        (pair 0 0) (pair 0 m))).mixedExtension.eu profile who ≤ _
  cases who <;> cases action <;>
    rw [binaryKernel_mixedEU_apply] <;>
    simp only [Bool.not_false, Bool.not_true] at hopponent <;>
    rw [hopponent] <;>
    norm_num [PMF.pure_apply, pair] <;>
    have hp0 : 0 ≤ (profile false true).toReal := ENNReal.toReal_nonneg <;>
    have hq0 : 0 ≤ (profile true true).toReal := ENNReal.toReal_nonneg <;>
    have hp1 : (profile false true).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _) <;>
    have hq1 : (profile true true).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _) <;>
    nlinarith

/-- A repeated stage utility at a public history is the corresponding mixed
one-stage payoff. -/
private theorem FiniteStageGame.stageEUAt_eq_mixedEU
    (G : FiniteStageGame) (profile : G.BehaviorProfile) {time : ℕ}
    (history : G.repeatedGame.Hist time) (who : G.Player) :
    G.repeatedGame.stageEUAt profile history who =
      G.kernel.mixedExtension.eu
        (fun player => profile player time history) who := by
  letI (player : G.Player) : Fintype (G.kernel.Strategy player) := by
    change Fintype (G.Action player)
    infer_instance
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ player, G.Action player)
    exact Finite.of_fintype _
  exact G.kernel.realizedAction_stageEUAt_eq_mixedExtension_eu
    profile history who

/-- Replace only one player's initial randomization by a pure action, leaving
all continuation behavior unchanged. -/
private abbrev FiniteStageGame.pinInitialAction
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) (action : G.Action who) : G.BehaviorStrategy who :=
  G.kernel.pinRealizedActionInitialAction profile who action

/-- Once the first joint action is fixed, pinning the initial action has no
effect on the continuation profile. -/
private theorem FiniteStageGame.shiftProfile_update_pinInitialAction
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) (action : G.Action who)
    (joint : ∀ player, G.Action player) :
    G.repeatedGame.shiftProfile
        (Function.update profile who
          (G.pinInitialAction profile who action))
        (PUnit.unit, joint) =
      G.repeatedGame.shiftProfile profile (PUnit.unit, joint) := by
  exact G.kernel.realizedAction_shiftProfile_update_pinInitialAction
    profile who action joint

/-- The initial joint-action law after pinning one player is the product law
with that coordinate replaced by the corresponding point mass. -/
private theorem FiniteStageGame.stageActionDist_update_pinInitialAction
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) (action : G.Action who) :
    G.repeatedGame.stageActionDist
        (Function.update profile who
          (G.pinInitialAction profile who action))
        (G.repeatedGame.emptyHist PUnit.unit) =
      Math.PMFProduct.pmfPi
        (Function.update (G.initialMixedProfile profile)
          who (PMF.pure action)) := by
  exact G.kernel.realizedAction_stageActionDist_update_pinInitialAction
    profile who action

/-- A one-stage mixed payoff is the expectation of the payoffs obtained by
pinning one player's own action. -/
private theorem FiniteStageGame.mixedEU_eq_expect_update
    (G : FiniteStageGame) (mixed : G.MixedProfile) (who : G.Player) :
    G.kernel.mixedExtension.eu mixed who =
      Math.Probability.expect (mixed who) (fun action =>
        G.kernel.mixedExtension.eu
          (Function.update mixed who (PMF.pure action)) who) := by
  letI (player : G.Player) : Fintype (G.kernel.Strategy player) := by
    change Fintype (G.Action player)
    infer_instance
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ player, G.Action player)
    exact Finite.of_fintype _
  exact G.kernel.mixedExtension_eu_eq_expect_pure_update mixed who

/-- Each stage expectation is affine in one player's initial mixed action
when all later behavior is held fixed. -/
private theorem FiniteStageGame.expectedStagePayoff_eq_expect_pinInitialAction
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) (time : ℕ) :
    G.repeatedGame.expectedStagePayoff
        profile PUnit.unit time who =
      Math.Probability.expect
        (G.initialMixedProfile profile who)
        (fun action => G.repeatedGame.expectedStagePayoff
          (Function.update profile who
            (G.pinInitialAction profile who action))
          PUnit.unit time who) := by
  letI (player : G.Player) : Fintype (G.kernel.Strategy player) := by
    change Fintype (G.Action player)
    infer_instance
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ player, G.Action player)
    exact Finite.of_fintype _
  exact G.kernel
    |>.realizedAction_expectedStagePayoff_eq_expect_pinInitialAction
      profile who time

/-- A finite repeated payoff is affine in one player's initial mixed action
when all continuation behavior is held fixed. -/
private theorem FiniteStageGame.finitePayoff_eq_expect_pinInitialAction
    (G : FiniteStageGame) (horizon : ℕ) (profile : G.BehaviorProfile)
    (who : G.Player) :
    G.finitePayoff horizon profile who =
      Math.Probability.expect (G.initialMixedProfile profile who)
        (fun action => G.finitePayoff horizon
          (Function.update profile who
            (G.pinInitialAction profile who action)) who) := by
  letI (player : G.Player) : Fintype (G.kernel.Strategy player) := by
    change Fintype (G.Action player)
    infer_instance
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ player, G.Action player)
    exact Finite.of_fintype _
  unfold FiniteStageGame.finitePayoff
  exact G.kernel
    |>.realizedAction_finiteAveragePayoff_eq_expect_pinInitialAction
      horizon profile who

/-- Example 4's stage payoffs never exceed `m+1`. -/
private theorem example4_mixedEU_le
    (m : ℕ) (mixed : Bool → PMF Bool) (who : Bool) :
    (example4 m).kernel.mixedExtension.eu mixed who ≤ m + 1 := by
  letI : Finite (example4 m).kernel.Outcome := by
    change Finite (Bool → Bool)
    exact Finite.of_fintype _
  letI : Finite (∀ player, (example4 m).kernel.Strategy player) := by
    change Finite (Bool → Bool)
    exact Finite.of_fintype _
  rw [(example4 m).kernel.mixedExtension_eu]
  calc
    _ ≤ Math.Probability.expect (Math.PMFProduct.pmfPi mixed)
        (fun _action => (m : ℝ) + 1) := by
      apply Math.Probability.expect_mono
      intro action
      simp only [FiniteStageGame.kernel, KernelGame.eu_ofPureEU]
      cases who <;> cases hrow : action false <;>
        cases hcolumn : action true <;>
        simp [binaryPayoff, hrow, hcolumn, pair] <;> positivity
    _ = _ := Math.Probability.expect_const _ _

/-- Playing Top for row or Right for column guarantees at least `m` in one
stage of Example 4. -/
private theorem example4_mixedEU_ge_of_self_pure
    (m : ℕ) (mixed : Bool → PMF Bool) (who : Bool)
    (hself : mixed who = PMF.pure who) :
    (m : ℝ) ≤ (example4 m).kernel.mixedExtension.eu mixed who := by
  change (m : ℝ) ≤ (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair m 0) (pair (m + 1) (m + 1))
        (pair 0 0) (pair 0 m))).mixedExtension.eu mixed who
  rw [binaryKernel_mixedEU_apply]
  cases who
  · change mixed false = PMF.pure false at hself
    rw [hself]
    simp [PMF.pure_apply, pair]
    have hprob : (mixed true true).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    have hprob0 : 0 ≤ (mixed true true).toReal := ENNReal.toReal_nonneg
    nlinarith
  · change mixed true = PMF.pure true at hself
    rw [hself]
    simp [PMF.pure_apply, pair]
    have hprob : (mixed false true).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    have hprob0 : 0 ≤ (mixed false true).toReal := ENNReal.toReal_nonneg
    nlinarith

/-- Playing Bottom for row or Left for column gives zero in the first stage,
regardless of the opponent's mixed action. -/
private theorem example4_mixedEU_eq_zero_of_self_wrong
    (m : ℕ) (mixed : Bool → PMF Bool) (who : Bool)
    (hself : mixed who = PMF.pure (!who)) :
    (example4 m).kernel.mixedExtension.eu mixed who = 0 := by
  change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair m 0) (pair (m + 1) (m + 1))
        (pair 0 0) (pair 0 m))).mixedExtension.eu mixed who = 0
  rw [binaryKernel_mixedEU_apply]
  cases who
  · change mixed false = PMF.pure true at hself
    rw [hself]
    simp [PMF.pure_apply, pair]
  · change mixed true = PMF.pure false at hself
    rw [hself]
    simp [PMF.pure_apply, pair]

/-- The stage expectation of every Example 4 profile is at most `m+1`. -/
private theorem example4_expectedStagePayoff_le
    (m : ℕ) (profile : (example4 m).BehaviorProfile)
    (time : ℕ) (who : Bool) :
    (example4 m).repeatedGame.expectedStagePayoff
      profile PUnit.unit time who ≤ m + 1 := by
  letI (player : Bool) : Finite ((example4 m).repeatedGame.Act player) :=
    @Finite.of_fintype _ ((example4 m).finiteAction player)
  letI : Finite (example4 m).repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  unfold StochasticGame.expectedStagePayoff
  calc
    _ ≤ Math.Probability.expect
        ((example4 m).repeatedGame.histDist profile PUnit.unit time)
        (fun _history => (m : ℝ) + 1) := by
      apply Math.Probability.expect_mono
      intro history
      rw [(example4 m).stageEUAt_eq_mixedEU]
      exact example4_mixedEU_le m _ who
    _ = _ := Math.Probability.expect_const _ _

/-- The stationary Top/Right deviation used in the earlier-horizon argument. -/
private def example4SecurityStrategy
    (m : ℕ) (who : Bool) : (example4 m).BehaviorStrategy who :=
  fun _time _history => PMF.pure who

/-- The Top/Right deviation earns at least `m` in every stage. -/
private theorem example4SecurityStrategy_expectedStagePayoff_ge
    (m : ℕ) (profile : (example4 m).BehaviorProfile)
    (time : ℕ) (who : Bool) :
    (m : ℝ) ≤ (example4 m).repeatedGame.expectedStagePayoff
      (Function.update profile who (example4SecurityStrategy m who))
      PUnit.unit time who := by
  letI (player : Bool) : Finite ((example4 m).repeatedGame.Act player) :=
    @Finite.of_fintype _ ((example4 m).finiteAction player)
  letI : Finite (example4 m).repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  unfold StochasticGame.expectedStagePayoff
  calc
    (m : ℝ) = Math.Probability.expect
        ((example4 m).repeatedGame.histDist
          (Function.update profile who (example4SecurityStrategy m who))
          PUnit.unit time) (fun _history => (m : ℝ)) :=
      (Math.Probability.expect_const _ _).symm
    _ ≤ _ := by
      apply Math.Probability.expect_mono
      intro history
      rw [(example4 m).stageEUAt_eq_mixedEU]
      apply example4_mixedEU_ge_of_self_pure
      simp [example4SecurityStrategy]
      rfl

/-- Over a positive horizon, the Top/Right deviation guarantees average
payoff at least `m`. -/
private theorem example4SecurityStrategy_finitePayoff_ge
    (m horizon : ℕ) (hhorizon : 0 < horizon)
    (profile : (example4 m).BehaviorProfile) (who : Bool) :
    (m : ℝ) ≤ (example4 m).finitePayoff horizon
      (Function.update profile who (example4SecurityStrategy m who)) who := by
  letI (player : Bool) : Finite ((example4 m).repeatedGame.Act player) :=
    @Finite.of_fintype _ ((example4 m).finiteAction player)
  letI : Finite (example4 m).repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  unfold FiniteStageGame.finitePayoff
  rw [(example4 m).repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  calc
    (m : ℝ) = (horizon : ℝ)⁻¹ *
        ∑ _time ∈ Finset.range horizon, (m : ℝ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀]
      · simp
      · exact_mod_cast Nat.ne_of_gt hhorizon
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro time _
        exact example4SecurityStrategy_expectedStagePayoff_ge
          m profile time who
      · positivity

/-- Pinning the wrong initial action makes Example 4's stage-zero payoff
zero. -/
private theorem example4_pinWrong_expectedStagePayoff_zero
    (m : ℕ) (profile : (example4 m).BehaviorProfile) (who : Bool) :
    (example4 m).repeatedGame.expectedStagePayoff
      (Function.update profile who
        ((example4 m).pinInitialAction profile who (!who)))
      PUnit.unit 0 who = 0 := by
  letI (player : Bool) : Finite ((example4 m).repeatedGame.Act player) :=
    @Finite.of_fintype _ ((example4 m).finiteAction player)
  rw [(example4 m).repeatedGame.expectedStagePayoff_zero,
    (example4 m).stageEUAt_eq_mixedEU]
  apply example4_mixedEU_eq_zero_of_self_wrong
  simp [FiniteStageGame.pinInitialAction]
  rfl

/-- At every positive horizon `n ≤ m`, pinning Bottom/Left initially yields
strictly less than the security payoff `m`. -/
private theorem example4_pinWrong_finitePayoff_lt
    (m horizon : ℕ) (hhorizon : 0 < horizon) (hle : horizon ≤ m)
    (profile : (example4 m).BehaviorProfile) (who : Bool) :
    (example4 m).finitePayoff horizon
      (Function.update profile who
        ((example4 m).pinInitialAction profile who (!who))) who < m := by
  letI (player : Bool) : Finite ((example4 m).repeatedGame.Act player) :=
    @Finite.of_fintype _ ((example4 m).finiteAction player)
  letI : Finite (example4 m).repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  obtain ⟨tail, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hhorizon)
  unfold FiniteStageGame.finitePayoff
  rw [(example4 m).repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff,
    Finset.sum_range_succ']
  rw [example4_pinWrong_expectedStagePayoff_zero]
  have hsum :
      (∑ time ∈ Finset.range tail,
        (example4 m).repeatedGame.expectedStagePayoff
          (Function.update profile who
            ((example4 m).pinInitialAction profile who (!who)))
          PUnit.unit (time + 1) who) ≤
        ∑ _time ∈ Finset.range tail, ((m : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro time _
    exact example4_expectedStagePayoff_le m _ (time + 1) who
  calc
    ((tail + 1 : ℕ) : ℝ)⁻¹ *
        ((∑ time ∈ Finset.range tail,
          (example4 m).repeatedGame.expectedStagePayoff
            (Function.update profile who
              ((example4 m).pinInitialAction profile who (!who)))
            PUnit.unit (time + 1) who) + 0) ≤
      ((tail + 1 : ℕ) : ℝ)⁻¹ *
        ∑ _time ∈ Finset.range tail, ((m : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left
      · simpa using hsum
      · positivity
    _ < (m : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hdenominator : (0 : ℝ) < ((tail + 1 : ℕ) : ℝ) := by
        positivity
      rw [inv_mul_lt_iff₀ hdenominator]
      norm_num at hle ⊢
      have hle' : (tail : ℝ) < m := by exact_mod_cast hle
      nlinarith

/-- In every Example 4 equilibrium of a positive horizon `n ≤ m`, row
starts with Top and column starts with Right with probability one. -/
private theorem example4_initialMixedProfile_eq_pure_of_horizonNash
    (m horizon : ℕ) (hhorizon : 0 < horizon) (hle : horizon ≤ m)
    (profile : (example4 m).BehaviorProfile)
    (hnash : (example4 m).repeatedGame.IsεHorizonNash
      PUnit.unit horizon 0 profile) (who : Bool) :
    (example4 m).initialMixedProfile profile who = PMF.pure who := by
  let root : PMF Bool := (example4 m).initialMixedProfile profile who
  let value : Bool → ℝ := fun action =>
    (example4 m).finitePayoff horizon
      (Function.update profile who
        ((example4 m).pinInitialAction profile who action)) who
  let baseline := (example4 m).finitePayoff horizon profile who
  change root = PMF.pure who
  have hpin (action : Bool) : value action ≤ baseline := by
    have h := hnash who
      ((example4 m).pinInitialAction profile who action)
    simpa [value, baseline, FiniteStageGame.finitePayoff] using h
  have hsecurityNash :
      (example4 m).finitePayoff horizon
          (Function.update profile who (example4SecurityStrategy m who)) who ≤
        baseline := by
    have h := hnash who (example4SecurityStrategy m who)
    simpa [baseline, FiniteStageGame.finitePayoff] using h
  have hbaseline : (m : ℝ) ≤ baseline :=
    (example4SecurityStrategy_finitePayoff_ge
      m horizon hhorizon profile who).trans hsecurityNash
  have hwrong : value (!who) < m := by
    exact example4_pinWrong_finitePayoff_lt
      m horizon hhorizon hle profile who
  have haffine : baseline = Math.Probability.expect root value := by
    exact (example4 m).finitePayoff_eq_expect_pinInitialAction
      horizon profile who
  have hsum := Math.Probability.pmf_toReal_sum_one root
  rw [Math.Probability.expect_eq_sum, Fintype.sum_bool] at haffine
  rw [Fintype.sum_bool] at hsum
  cases who
  · have hwrongMass : (root true).toReal = 0 := by
      by_contra hne
      have hpositive : 0 < (root true).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
      have hfalse := hpin false
      have htrue := hpin true
      change value true < (m : ℝ) at hwrong
      have hwrongBaseline : value true < baseline :=
        hwrong.trans_le hbaseline
      have hweightedWrong :
          (root true).toReal * value true <
            (root true).toReal * baseline :=
        mul_lt_mul_of_pos_left hwrongBaseline hpositive
      have hweightedCorrect :
          (root false).toReal * value false ≤
            (root false).toReal * baseline :=
        mul_le_mul_of_nonneg_left hfalse ENNReal.toReal_nonneg
      nlinarith
    exact Math.PMFProduct.eq_pure_false_of_true_toReal_eq_zero
      root hwrongMass
  · have hwrongMass : (root false).toReal = 0 := by
      by_contra hne
      have hpositive : 0 < (root false).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
      have hfalse := hpin false
      have htrue := hpin true
      change value false < (m : ℝ) at hwrong
      have hwrongBaseline : value false < baseline :=
        hwrong.trans_le hbaseline
      have hweightedWrong :
          (root false).toReal * value false <
            (root false).toReal * baseline :=
        mul_lt_mul_of_pos_left hwrongBaseline hpositive
      have hweightedCorrect :
          (root true).toReal * value true ≤
            (root true).toReal * baseline :=
        mul_le_mul_of_nonneg_left htrue ENNReal.toReal_nonneg
      nlinarith
    have htrueMass : (root true).toReal = 1 := by
      nlinarith
    exact Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one
      root htrueMass

/-- After the first action, the nondeviator in the critical profile copies
the deviator's initial action forever. -/
private theorem example4CriticalProfile_shift_opponent
    (m : ℕ) (who : Bool)
    (deviation : (example4 m).BehaviorStrategy who)
    (action : Bool → Bool)
    (time : ℕ) (history : (example4 m).repeatedGame.Hist time) :
    (example4 m).repeatedGame.shiftProfile
        (Function.update (example4CriticalProfile m) who deviation)
        (PUnit.unit, action) (!who) time history =
      PMF.pure (action who) := by
  unfold StochasticGame.shiftProfile
  rw [Function.update_of_ne (Bool.not_ne_self who)]
  simp [example4CriticalProfile, StochasticGame.consHist]
  rfl

/-- Conditional on the first joint action, every later expected payoff of a
deviator against the critical profile has the paper's uniform stage bound. -/
private theorem example4CriticalProfile_shift_expectedStagePayoff_le
    (m : ℕ) (who : Bool)
    (deviation : (example4 m).BehaviorStrategy who)
    (action : Bool → Bool) (time : ℕ) :
    (example4 m).repeatedGame.expectedStagePayoff
        ((example4 m).repeatedGame.shiftProfile
          (Function.update (example4CriticalProfile m) who deviation)
          (PUnit.unit, action)) PUnit.unit time who ≤
      if action who = who then (m : ℝ) else m + 1 := by
  classical
  letI (player : Bool) : Finite ((example4 m).repeatedGame.Act player) :=
    @Finite.of_fintype _ ((example4 m).finiteAction player)
  letI : Finite (example4 m).repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  let shifted := (example4 m).repeatedGame.shiftProfile
    (Function.update (example4CriticalProfile m) who deviation)
    (PUnit.unit, action)
  unfold StochasticGame.expectedStagePayoff
  rw [← Math.Probability.expect_const
    ((example4 m).repeatedGame.histDist shifted PUnit.unit time)
    (if action who = who then (m : ℝ) else m + 1)]
  apply Math.Probability.expect_mono
  intro history
  rw [(example4 m).stageEUAt_eq_mixedEU]
  apply example4_mixedEU_le_of_opponent_pure
  exact example4CriticalProfile_shift_opponent
    m who deviation action time history

/-- The `m` continuation stages after any first action contribute at most the
corresponding stage bound times `m`. -/
private theorem example4CriticalProfile_shift_totalPayoff_le
    (m : ℕ) (who : Bool)
    (deviation : (example4 m).BehaviorStrategy who)
    (action : Bool → Bool) :
    Math.Probability.expect
        ((example4 m).repeatedGame.histDist
          ((example4 m).repeatedGame.shiftProfile
            (Function.update (example4CriticalProfile m) who deviation)
            (PUnit.unit, action)) PUnit.unit m)
        (fun history => (example4 m).repeatedGame.totalPayoff who history) ≤
      (m : ℝ) * (if action who = who then (m : ℝ) else m + 1) := by
  letI (player : Bool) : Finite ((example4 m).repeatedGame.Act player) :=
    @Finite.of_fintype _ ((example4 m).finiteAction player)
  letI : Finite (example4 m).repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  rw [(example4 m).repeatedGame.expect_totalPayoff_eq_sum_expectedStagePayoff]
  calc
    (∑ time ∈ Finset.range m,
        (example4 m).repeatedGame.expectedStagePayoff
          ((example4 m).repeatedGame.shiftProfile
            (Function.update (example4CriticalProfile m) who deviation)
            (PUnit.unit, action)) PUnit.unit time who) ≤
      ∑ _time ∈ Finset.range m,
        (if action who = who then (m : ℝ) else m + 1) := by
          apply Finset.sum_le_sum
          intro time _
          exact example4CriticalProfile_shift_expectedStagePayoff_le
            m who deviation action time
    _ = (m : ℝ) * (if action who = who then (m : ℝ) else m + 1) := by
      by_cases haction : action who = who
      · simp [haction]
      · simp [haction]
        ring

/-- A first-stage joint action in the support keeps the nondeviator's
prescribed pure action. -/
private theorem example4CriticalProfile_root_opponent_eq_of_mem_support
    (m : ℕ) (who : Bool)
    (deviation : (example4 m).BehaviorStrategy who)
    (action : Bool → Bool)
    (hsupport : action ∈
      ((example4 m).repeatedGame.stageActionDist
        (Function.update (example4CriticalProfile m) who deviation)
        ((example4 m).repeatedGame.emptyHist PUnit.unit)).support) :
    action (!who) = who := by
  classical
  let mixed : Bool → PMF Bool := fun player =>
    Function.update (example4CriticalProfile m) who deviation player 0
      ((example4 m).repeatedGame.emptyHist PUnit.unit)
  have hmixed : mixed (!who) = PMF.pure who := by
    simp [mixed, example4CriticalProfile]
    rfl
  change action ∈ (Math.PMFProduct.pmfPi mixed).support at hsupport
  by_contra hne
  have hzero : Math.PMFProduct.pmfPi mixed action = 0 := by
    rw [Math.PMFProduct.pmfPi_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ (!who))
    rw [hmixed, PMF.pure_apply, if_neg hne]
  exact (PMF.mem_support_iff _ _).mp hsupport hzero

/-- At the initial stage, a supported deviating action pays `m` precisely
when it equals the player's label, and zero otherwise. -/
private theorem example4_stagePayoff_root
    (m : ℕ) (who : Bool) (action : Bool → Bool)
    (hopponent : action (!who) = who) :
    (example4 m).repeatedGame.stagePayoff PUnit.unit action who =
      if action who = who then (m : ℝ) else 0 := by
  change (example4 m).kernel.eu action who = _
  rw [KernelGame.eu_ofPureEU]
  change binaryPayoff (pair m 0) (pair (m + 1) (m + 1))
    (pair 0 0) (pair 0 m) action who = _
  cases hfalse : action false <;> cases htrue : action true <;>
    cases who <;> simp [binaryPayoff, pair, hfalse, htrue] at hopponent ⊢

/-- No unilateral deviation from the critical profile earns more than `m`
over its `m+1` stages. -/
private theorem example4CriticalProfile_deviation_bound
    (m : ℕ) (who : Bool)
    (deviation : (example4 m).BehaviorStrategy who) :
    (example4 m).repeatedGame.finiteAveragePayoff PUnit.unit (m + 1)
      (Function.update (example4CriticalProfile m) who deviation) who ≤ m := by
  letI (player : Bool) : Finite ((example4 m).repeatedGame.Act player) :=
    @Finite.of_fintype _ ((example4 m).finiteAction player)
  letI : Finite (example4 m).repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  let deviated := Function.update (example4CriticalProfile m) who deviation
  let rootLaw := (example4 m).repeatedGame.stageActionDist deviated
    ((example4 m).repeatedGame.emptyHist PUnit.unit)
  have htotal :
      Math.Probability.expect
          ((example4 m).repeatedGame.histDist deviated PUnit.unit (m + 1))
          (fun history => (example4 m).repeatedGame.totalPayoff who history) ≤
        (m : ℝ) * (m + 1) := by
    rw [(example4 m).repeatedGame.histDist_succ_shift deviated PUnit.unit m]
    rw [Math.Probability.expect_bind]
    apply Math.ProbabilityMassFunction.expect_le_of_le_on_support
    intro action haction
    rw [KernelGame.realizedActionStochasticGame_transition,
      Math.Probability.expect_bind]
    let stateValue : (example4 m).repeatedGame.State → ℝ := fun state =>
      Math.Probability.expect
        (((example4 m).repeatedGame.histDist
          ((example4 m).repeatedGame.shiftProfile deviated
            (PUnit.unit, action)) state m).map
          ((example4 m).repeatedGame.consHist (PUnit.unit, action)))
        (fun history => (example4 m).repeatedGame.totalPayoff who history)
    change Math.Probability.expect (PMF.pure PUnit.unit) stateValue ≤ _
    have hstate : Math.Probability.expect (PMF.pure PUnit.unit) stateValue =
        stateValue PUnit.unit := by
      rw [← Math.Probability.expect_const (PMF.pure PUnit.unit)
        (stateValue PUnit.unit)]
      congr 1
    rw [hstate]
    dsimp only [stateValue]
    rw [Math.Probability.expect_map]
    simp_rw [(example4 m).repeatedGame.totalPayoff_consHist]
    rw [Math.Probability.expect_add,
      Math.Probability.expect_const]
    have hopponent : action (!who) = who :=
      example4CriticalProfile_root_opponent_eq_of_mem_support
        m who deviation action haction
    have hroot := example4_stagePayoff_root m who action hopponent
    have htail := example4CriticalProfile_shift_totalPayoff_le
      m who deviation action
    change Math.Probability.expect
        ((example4 m).repeatedGame.histDist
          ((example4 m).repeatedGame.shiftProfile deviated
            (PUnit.unit, action)) PUnit.unit m)
        (fun history => (example4 m).repeatedGame.totalPayoff who history) ≤ _
      at htail
    rw [hroot]
    cases who
    · cases hactionSelf : action false <;>
        simp [hactionSelf] at htail ⊢ <;> nlinarith
    · cases hactionSelf : action true <;>
        simp [hactionSelf] at htail ⊢ <;> nlinarith
  unfold StochasticGame.finiteAveragePayoff
  calc
    ((m + 1 : ℕ) : ℝ)⁻¹ *
        Math.Probability.expect
          ((example4 m).repeatedGame.histDist deviated PUnit.unit (m + 1))
          (fun history => (example4 m).repeatedGame.totalPayoff who history) ≤
      ((m + 1 : ℕ) : ℝ)⁻¹ * ((m : ℝ) * (m + 1)) :=
        mul_le_mul_of_nonneg_left htotal (inv_nonneg.mpr (by positivity))
    _ = m := by
      have hne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      norm_num [Nat.cast_add]
      ring

/-- The on-path continuation of the critical construction plays Top/Right in
every remaining stage. -/
private def example4CriticalTailProfile (m : ℕ) :
    (example4 m).BehaviorProfile :=
  fun player _time _history => PMF.pure player

/-- The prescribed first-stage law is the pure Bottom/Left action profile. -/
private theorem example4CriticalProfile_rootLaw
    (m : ℕ) :
    (example4 m).repeatedGame.stageActionDist
        (example4CriticalProfile m)
        ((example4 m).repeatedGame.emptyHist PUnit.unit) =
      PMF.pure (fun player : Bool => !player) := by
  unfold StochasticGame.stageActionDist
  change Math.PMFProduct.pmfPi (fun player : Bool => PMF.pure (!player)) = _
  exact Math.PMFProduct.pmfPi_pure _

/-- After the prescribed Bottom/Left first action, the critical profile is
the stationary Top/Right continuation. -/
private theorem example4CriticalProfile_shift_onPath
    (m : ℕ) :
    (example4 m).repeatedGame.shiftProfile (example4CriticalProfile m)
        (PUnit.unit, fun player : Bool => !player) =
      example4CriticalTailProfile m := by
  funext player time history
  unfold StochasticGame.shiftProfile example4CriticalProfile
    example4CriticalTailProfile
  simp [StochasticGame.consHist]

/-- Every stage of the on-path continuation pays both players `m+1`. -/
private theorem example4CriticalTailProfile_expectedStagePayoff
    (m time : ℕ) (who : Bool) :
    (example4 m).repeatedGame.expectedStagePayoff
        (example4CriticalTailProfile m) PUnit.unit time who = m + 1 := by
  letI (player : Bool) : Finite ((example4 m).repeatedGame.Act player) :=
    @Finite.of_fintype _ ((example4 m).finiteAction player)
  letI : Finite (example4 m).repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  unfold StochasticGame.expectedStagePayoff
  rw [← Math.Probability.expect_const
    ((example4 m).repeatedGame.histDist
      (example4CriticalTailProfile m) PUnit.unit time) ((m : ℝ) + 1)]
  congr 1
  funext history
  rw [(example4 m).stageEUAt_eq_mixedEU]
  change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
    (binaryPayoff (pair m 0) (pair (m + 1) (m + 1))
      (pair 0 0) (pair 0 m))).mixedExtension.eu
      (fun player : Bool => PMF.pure player) who = m + 1
  rw [binaryKernel_mixedEU_apply]
  cases who <;> simp [PMF.pure_apply, pair]

/-- From stage two onward, the critical profile follows its stationary
Top/Right continuation in expectation. -/
private theorem example4CriticalProfile_expectedStagePayoff_succ
    (m time : ℕ) (who : Bool) :
    (example4 m).repeatedGame.expectedStagePayoff
        (example4CriticalProfile m) PUnit.unit (time + 1) who = m + 1 := by
  letI (player : Bool) : Finite ((example4 m).repeatedGame.Act player) :=
    @Finite.of_fintype _ ((example4 m).finiteAction player)
  letI : Finite (example4 m).repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  rw [(example4 m).repeatedGame.expectedStagePayoff_succ_shift]
  rw [example4CriticalProfile_rootLaw]
  change Math.Probability.expect
    (PMF.pure (fun player : Bool => !player) : PMF (Bool → Bool))
      (fun action => Math.Probability.expect
        ((example4 m).repeatedGame.transition PUnit.unit action)
        (fun state => (example4 m).repeatedGame.expectedStagePayoff
          ((example4 m).repeatedGame.shiftProfile (example4CriticalProfile m)
            (PUnit.unit, action)) state time who)) = m + 1
  rw [Math.Probability.expect_pure]
  rw [KernelGame.realizedActionStochasticGame_transition]
  change Math.Probability.expect (PMF.pure PUnit.unit : PMF PUnit)
    (fun state => (example4 m).repeatedGame.expectedStagePayoff
      ((example4 m).repeatedGame.shiftProfile (example4CriticalProfile m)
        (PUnit.unit, fun player : Bool => !player)) state time who) = m + 1
  rw [Math.Probability.expect_pure]
  rw [example4CriticalProfile_shift_onPath]
  exact example4CriticalTailProfile_expectedStagePayoff m time who

/-- The initial Bottom/Left stage pays both players zero. -/
private theorem example4CriticalProfile_expectedStagePayoff_zero
    (m : ℕ) (who : Bool) :
    (example4 m).repeatedGame.expectedStagePayoff
        (example4CriticalProfile m) PUnit.unit 0 who = 0 := by
  letI (player : Bool) : Finite ((example4 m).repeatedGame.Act player) :=
    @Finite.of_fintype _ ((example4 m).finiteAction player)
  rw [(example4 m).repeatedGame.expectedStagePayoff_zero]
  rw [(example4 m).stageEUAt_eq_mixedEU]
  change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
    (binaryPayoff (pair m 0) (pair (m + 1) (m + 1))
      (pair 0 0) (pair 0 m))).mixedExtension.eu
      (fun player : Bool => PMF.pure (!player)) who = 0
  rw [binaryKernel_mixedEU_apply]
  cases who <;> simp [PMF.pure_apply, pair]

/-- The critical profile averages one zero stage and `m` Top/Right stages,
so its `(m+1)`-stage payoff is `(m,m)`. -/
private theorem example4CriticalProfile_payoff
    (m : ℕ) :
    (example4 m).finitePayoff (m + 1) (example4CriticalProfile m) =
      pair m m := by
  letI (player : Bool) : Finite ((example4 m).repeatedGame.Act player) :=
    @Finite.of_fintype _ ((example4 m).finiteAction player)
  letI : Finite (example4 m).repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  funext who
  change Bool at who
  unfold FiniteStageGame.finitePayoff
  rw [(example4 m).repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  rw [Finset.sum_range_succ']
  rw [example4CriticalProfile_expectedStagePayoff_zero]
  have htail :
      (∑ time ∈ Finset.range m,
        (example4 m).repeatedGame.expectedStagePayoff
          (example4CriticalProfile m) PUnit.unit (time + 1) who) =
        ∑ _time ∈ Finset.range m, ((m : ℝ) + 1) := by
    apply Finset.sum_congr rfl
    intro time _
    exact example4CriticalProfile_expectedStagePayoff_succ m time who
  rw [htail]
  simp only [add_zero, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  change ((m + 1 : ℕ) : ℝ)⁻¹ * ((m : ℝ) * (m + 1)) = pair m m who
  cases who <;> simp only [pair_false, pair_true]
  all_goals
    have hne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num [Nat.cast_add]
    ring

/-- Example 5: payoff `e_j` when every player announces `j`, and zero
otherwise. -/
def example5 (N : ℕ) [NeZero N] : FiniteStageGame where
  Player := Fin N
  Action := fun _ => Fin N
  payoff := fun action who =>
    if _h : ∀ i, action i = action who then
      if action who = who then 1 else 0
    else 0

/-- In Example 5 the aggregate pure payoff is one exactly at unanimous
profiles, and is zero otherwise. -/
private theorem example5_sum_payoff (N : ℕ) [NeZero N]
    (action : Fin N → Fin N) :
    ∑ who, (example5 N).payoff action who =
      if ∃ label, ∀ who, action who = label then 1 else 0 := by
  classical
  change (∑ who : Fin N,
      if _h : ∀ i, action i = action who then
        if action who = who then 1 else 0
      else 0) = _
  by_cases hunanimous : ∃ label, ∀ who, action who = label
  · obtain ⟨label, hlabel⟩ := hunanimous
    rw [if_pos ⟨label, hlabel⟩]
    have hconstant (who : Fin N) : ∀ i, action i = action who := by
      intro i
      rw [hlabel i, hlabel who]
    simp_rw [dif_pos (hconstant _), hlabel]
    simp
  · rw [if_neg hunanimous]
    apply Finset.sum_eq_zero
    intro who _
    rw [dif_neg]
    intro hconstant
    exact hunanimous ⟨action who, hconstant⟩

/-- Every pure payoff in Example 5 is nonnegative. -/
private theorem example5_payoff_nonneg (N : ℕ) [NeZero N]
    (action : Fin N → Fin N) (who : Fin N) :
    0 ≤ (example5 N).payoff action who := by
  change 0 ≤ if _h : ∀ i, action i = action who then
    if action who = who then 1 else 0
  else 0
  split_ifs <;> norm_num

/-- An independent product supported on unanimous profiles has common pure
marginals, provided that there are at least two coordinates. -/
private theorem pmfPi_eq_common_pure_of_unanimous_support
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (profile : Fin N → PMF (Fin N))
    (hsupport : ∀ action ∈ (Math.PMFProduct.pmfPi profile).support,
      ∃ label, ∀ who, action who = label) :
    ∃ label, ∀ who, profile who = PMF.pure label := by
  classical
  let base : Fin N → Fin N := fun who => (profile who).support_nonempty.choose
  have hbaseSupport (who : Fin N) : base who ∈ (profile who).support :=
    (profile who).support_nonempty.choose_spec
  have hjointSupport (action : Fin N → Fin N)
      (haction : ∀ who, action who ∈ (profile who).support) :
      action ∈ (Math.PMFProduct.pmfPi profile).support := by
    rw [PMF.mem_support_iff, Math.PMFProduct.pmfPi_apply]
    exact Finset.prod_ne_zero_iff.mpr fun who _ =>
      (PMF.mem_support_iff _ _).mp (haction who)
  obtain ⟨label, hlabel⟩ := hsupport base
    (hjointSupport base hbaseSupport)
  refine ⟨label, fun who => ?_⟩
  have hsupportWho : (profile who).support = {label} := by
    apply Set.Subset.antisymm
    · intro action haction
      let zero : Fin N := ⟨0, by omega⟩
      let one : Fin N := ⟨1, by omega⟩
      let other : Fin N := if who = zero then one else zero
      have hzeroOne : zero ≠ one := by
        intro h
        have : (0 : ℕ) = 1 := by simpa [zero, one] using congrArg Fin.val h
        omega
      have hother : other ≠ who := by
        by_cases hwho : who = zero
        · simp [other, hwho, hzeroOne.symm]
        · simp [other, hwho, Ne.symm hwho]
      let updated := Function.update base who action
      have hupdatedSupport : ∀ i, updated i ∈ (profile i).support := by
        intro i
        by_cases hi : i = who
        · subst i
          simpa [updated] using haction
        · simpa [updated, hi] using hbaseSupport i
      obtain ⟨common, hcommon⟩ := hsupport updated
        (hjointSupport updated hupdatedSupport)
      have hactionCommon : action = common := by
        simpa [updated] using hcommon who
      have hotherCommon : base other = common := by
        simpa [updated, hother] using hcommon other
      rw [hactionCommon, ← hotherCommon, hlabel other]
      simp
    · intro action haction
      subst action
      rw [← hlabel who]
      exact hbaseSupport who
  have hone : profile who label = 1 :=
    (PMF.apply_eq_one_iff (profile who) label).mpr hsupportWho
  apply PMF.ext
  intro action
  by_cases ha : action = label
  · subst action
    simp [hone]
  · have hzero : profile who action = 0 := by
      rw [PMF.apply_eq_zero_iff]
      simp [hsupportWho, ha]
    simp [hzero, ha]

/-- Every correlated-feasible payoff of Example 5 is coordinatewise
nonnegative and has aggregate payoff at most one. -/
private theorem example5_correlated_bounds (N : ℕ) [NeZero N]
    {payoff : Payoff (Fin N)}
    (hpayoff : payoff ∈ (example5 N).correlatedFeasiblePayoffs) :
    (∀ who, 0 ≤ payoff who) ∧ ∑ who, payoff who ≤ 1 := by
  apply (convexHull_min (t := {v : Payoff (Fin N) |
      (∀ who, 0 ≤ v who) ∧ ∑ who, v who ≤ 1}) ?_ ?_) hpayoff
  · rintro _ ⟨action, rfl⟩
    change (Fin N → Fin N) at action
    constructor
    · exact example5_payoff_nonneg N action
    · change (∑ who : Fin N,
          if _h : ∀ i, action i = action who then
            if action who = who then 1 else 0
          else 0) ≤ 1
      have htotal := example5_sum_payoff N action
      change (∑ who : Fin N,
          if _h : ∀ i, action i = action who then
            if action who = who then 1 else 0
          else 0) = _ at htotal
      rw [htotal]
      split_ifs <;> norm_num
  · intro x hx y hy a b ha hb hab
    constructor
    · intro who
      exact add_nonneg (mul_nonneg ha (hx.1 who))
        (mul_nonneg hb (hy.1 who))
    · change (∑ who, (a * x who + b * y who)) ≤ 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      nlinarith [hx.2, hy.2]

/-- At a public history, Example 5's stage expectation is its independently
mixed one-stage payoff at the current behavioral actions. -/
private theorem example5_stageEUAt_eq_mixedPayoff
    (N : ℕ) [NeZero N] (profile : (example5 N).BehaviorProfile)
    {time : ℕ} (history : (example5 N).repeatedGame.Hist time)
    (who : Fin N) :
    (example5 N).repeatedGame.stageEUAt profile history who =
      (example5 N).mixedPayoff
        (fun player => profile player time history) who := by
  letI : Finite (example5 N).kernel.Outcome := by
    change Finite (Fin N → Fin N)
    exact Finite.of_fintype _
  unfold StochasticGame.stageEUAt StochasticGame.stageActionDist
  unfold FiniteStageGame.mixedPayoff KernelGame.payoffVector
  rw [(example5 N).kernel.mixedExtension_eu]
  rfl

/-- Equality in Example 5's aggregate mixed-payoff bound forces all players
to use the same pure action. -/
private theorem example5_mixedProfile_common_pure_of_total_eq_one
    (N : ℕ) [NeZero N] (hN : 2 ≤ N)
    (profile : (example5 N).MixedProfile)
    (htotal : ∑ who, (example5 N).mixedPayoff profile who = 1) :
    ∃ label, ∀ who, profile who = PMF.pure label := by
  letI (who : (example5 N).Player) :
      Fintype ((example5 N).kernel.Strategy who) :=
    (example5 N).finiteAction who
  letI : Finite (example5 N).kernel.Outcome := by
    change Finite (Fin N → Fin N)
    exact Finite.of_fintype _
  let joint := Math.PMFProduct.pmfPi profile
  have hmixed (who : Fin N) :
      (example5 N).mixedPayoff profile who =
        Math.Probability.expect joint
          (fun action => (example5 N).payoff action who) := by
    change (example5 N).kernel.mixedExtension.eu profile who = _
    rw [(example5 N).kernel.mixedExtension_eu]
    congr 1
    funext action
    simp [FiniteStageGame.kernel, KernelGame.eu_ofPureEU]
  have hexpect : Math.Probability.expect joint
      (fun action => ∑ who, (example5 N).payoff action who) = 1 := by
    rw [← Math.Probability.expect_sum_comm]
    simpa only [hmixed] using htotal
  apply pmfPi_eq_common_pure_of_unanimous_support N hN profile
  intro action haction
  by_contra hnot
  have hstrict : Math.Probability.expect joint
      (fun pure => ∑ who, (example5 N).payoff pure who) < 1 := by
    apply Math.Probability.expect_lt_const_of_le_of_exists_lt
    · intro pure
      have hsum := example5_sum_payoff N pure
      rw [hsum]
      split_ifs <;> norm_num
    · refine ⟨action, (PMF.mem_support_iff _ _).mp haction, ?_⟩
      have hsum := example5_sum_payoff N action
      rw [hsum, if_neg hnot]
      norm_num
  linarith

/-- If Example 5 attains the maximal aggregate discounted payoff, then its
first-stage independently mixed payoff already has aggregate one. -/
private theorem example5_initial_total_eq_one_of_discounted_total_eq_one
    (N : ℕ) [NeZero N] (rate : (example5 N).DiscountRate)
    (profile : (example5 N).BehaviorProfile)
    (htotal : ∑ who,
      (example5 N).discountedPayoffOnRate rate profile who = 1) :
    ∑ who, (example5 N).mixedPayoff
      ((example5 N).initialMixedProfile profile) who = 1 := by
  letI (who : Fin N) : Finite ((example5 N).repeatedGame.Act who) :=
    @Finite.of_fintype _ ((example5 N).finiteAction who)
  letI : Finite (example5 N).repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  let beta := 1 - rate.1
  let empty := (example5 N).repeatedGame.emptyHist PUnit.unit
  let actionLaw := (example5 N).repeatedGame.stageActionDist profile empty
  let continuation (action : (example5 N).repeatedGame.JointAct)
      (who : Fin N) :=
    (example5 N).repeatedGame.discountedPayoff beta
      ((example5 N).repeatedGame.shiftProfile
        profile (PUnit.unit, action)) PUnit.unit who
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    linarith [rate.2.2]
  have hbeta1 : beta < 1 := by
    dsimp only [beta]
    linarith [rate.2.1]
  have hbound (who : Fin N) : ∀ state action,
      |(example5 N).repeatedGame.stagePayoff state action who| ≤ 1 := by
    intro state action
    simp only [FiniteStageGame.repeatedGame,
      KernelGame.realizedActionStochasticGame,
      FiniteStageGame.kernel, KernelGame.eu_ofPureEU, example5]
    split_ifs <;> norm_num
  have htransition (action : (example5 N).repeatedGame.JointAct) :
      (example5 N).repeatedGame.transition PUnit.unit action =
        PMF.pure PUnit.unit := rfl
  have hexpectTransition (action : (example5 N).repeatedGame.JointAct)
      (f : (example5 N).repeatedGame.State → ℝ) :
      Math.Probability.expect
          ((example5 N).repeatedGame.transition PUnit.unit action) f =
        f PUnit.unit := by
    rw [htransition]
    exact Math.Probability.expect_pure f PUnit.unit
  have hinitial : (example5 N).initialMixedProfile profile =
      fun player => profile player 0 empty := rfl
  have hshift (who : Fin N) :
      (example5 N).discountedPayoffOnRate rate profile who =
        rate.1 * (example5 N).repeatedGame.stageEUAt profile empty who +
          beta * Math.Probability.expect actionLaw
            (fun action => continuation action who) := by
    have h := (example5 N).repeatedGame.discountedPayoff_shift
      (hbound who) profile PUnit.unit (β := beta) hbeta0 hbeta1
    simp_rw [hexpectTransition] at h
    simpa [FiniteStageGame.discountedPayoffOnRate,
      FiniteStageGame.discountedPayoff, beta, empty, actionLaw,
      continuation] using h
  have hcontinuation : Math.Probability.expect actionLaw
      (fun action => ∑ who, continuation action who) ≤ 1 := by
    calc
      Math.Probability.expect actionLaw
          (fun action => ∑ who, continuation action who) ≤
          Math.Probability.expect actionLaw (fun _ => (1 : ℝ)) := by
        apply Math.Probability.expect_mono
        intro action
        have hmem : (fun who => continuation action who) ∈
            (example5 N).correlatedFeasiblePayoffs := by
          apply lemma_1_Dlambda_subset_C (example5 N) rate
          exact ⟨(example5 N).repeatedGame.shiftProfile
            profile (PUnit.unit, action), rfl⟩
        exact (example5_correlated_bounds N hmem).2
      _ = 1 := Math.Probability.expect_const actionLaw 1
  have hstageLe : ∑ who,
      (example5 N).repeatedGame.stageEUAt profile empty who ≤ 1 := by
    have hmem := (example5 N).mixedPayoff_mem_correlatedFeasiblePayoffs
      ((example5 N).initialMixedProfile profile)
    have hle := (example5_correlated_bounds N hmem).2
    rw [hinitial] at hle
    calc
      (∑ who, (example5 N).repeatedGame.stageEUAt profile empty who) =
          ∑ who, (example5 N).mixedPayoff
            (fun player => profile player 0 empty) who := by
        apply Finset.sum_congr rfl
        intro who _
        exact example5_stageEUAt_eq_mixedPayoff N profile empty who
      _ ≤ 1 := hle
  have hsumShift :
      (∑ who, (example5 N).discountedPayoffOnRate rate profile who) =
        rate.1 * (∑ who,
          (example5 N).repeatedGame.stageEUAt profile empty who) +
          beta * Math.Probability.expect actionLaw
            (fun action => ∑ who, continuation action who) := by
    simp_rw [hshift]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Math.Probability.expect_sum_comm]
    rfl
  have hstageEq : ∑ who,
      (example5 N).repeatedGame.stageEUAt profile empty who = 1 := by
    rw [htotal] at hsumShift
    dsimp only [beta] at hsumShift hcontinuation
    nlinarith [rate.2.1, rate.2.2]
  rw [hinitial]
  calc
    (∑ who, (example5 N).mixedPayoff
        (fun player => profile player 0 empty) who) =
        ∑ who, (example5 N).repeatedGame.stageEUAt profile empty who := by
      apply Finset.sum_congr rfl
      intro who _
      exact (example5_stageEUAt_eq_mixedPayoff N profile empty who).symm
    _ = 1 := hstageEq

/-- Example 6.  Player `false` has two rows and player `true` has four
columns. -/
inductive FourColumn
  | c0 | c1 | c2 | c3
  deriving DecidableEq, Fintype

/-- A sum over Example 6's four columns, in table order. -/
lemma sum_fourColumn {M : Type*} [AddCommMonoid M] (f : FourColumn → M) :
    ∑ column, f column =
      f FourColumn.c0 + f FourColumn.c1 + f FourColumn.c2 + f FourColumn.c3 := by
  classical
  rw [show Finset.univ =
      {FourColumn.c0, FourColumn.c1, FourColumn.c2, FourColumn.c3} by
    ext column
    cases column <;> simp]
  simp [add_assoc]

/-- Action spaces of Example 6. -/
abbrev Example6Action : Bool → Type
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
abbrev example6 : FiniteStageGame where
  Player := Bool
  Action := Example6Action
  payoff := example6Payoff

/-- Example 6's row payoff is the mean of the column labels. -/
theorem example6_mixedPayoff_false
    (profile : ∀ who, PMF (Example6Action who)) :
    example6.mixedPayoff profile false =
      (profile true FourColumn.c1).toReal +
        2 * (profile true FourColumn.c2).toReal +
        3 * (profile true FourColumn.c3).toReal := by
  letI : Finite example6.kernel.Outcome := by
    change Finite (∀ who, Example6Action who)
    exact Finite.of_fintype _
  change example6.kernel.mixedExtension.eu profile false = _
  rw [KernelGame.mixedExtension_eu]
  simp only [KernelGame.eu_ofPureEU]
  change Math.Probability.expect (Math.PMFProduct.pmfPi profile)
      (fun action ↦ example6Payoff action false) = _
  rw [Math.PMFProduct.expect_pmfPi_boolFamily]
  simp only [Math.Probability.expect_eq_sum, Fintype.sum_bool]
  simp_rw [sum_fourColumn]
  simp [example6Payoff, Math.PMFProduct.pmfBool_false_toReal]
  ring

/-- Example 6's column payoff is the probability that row and column block
agree. -/
theorem example6_mixedPayoff_true
    (profile : ∀ who, PMF (Example6Action who)) :
    example6.mixedPayoff profile true =
      (1 - (profile false true).toReal) *
          ((profile true FourColumn.c0).toReal +
            (profile true FourColumn.c1).toReal) +
        (profile false true).toReal *
          ((profile true FourColumn.c2).toReal +
            (profile true FourColumn.c3).toReal) := by
  letI : Finite example6.kernel.Outcome := by
    change Finite (∀ who, Example6Action who)
    exact Finite.of_fintype _
  change example6.kernel.mixedExtension.eu profile true = _
  rw [KernelGame.mixedExtension_eu]
  simp only [KernelGame.eu_ofPureEU]
  change Math.Probability.expect (Math.PMFProduct.pmfPi profile)
      (fun action ↦ example6Payoff action true) = _
  rw [Math.PMFProduct.expect_pmfPi_boolFamily]
  simp only [Math.Probability.expect_eq_sum, Fintype.sum_bool]
  simp_rw [sum_fourColumn]
  simp [example6Payoff, Math.PMFProduct.pmfBool_false_toReal]
  ring

/-- Every payoff in either outer vertical strip of Example 6 is already
one-stage feasible. -/
theorem example6_outerStrip_mem_D1 (x y : ℝ)
    (hx0 : 0 ≤ x) (hx3 : x ≤ 3) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (houter : x ≤ 1 ∨ 2 ≤ x) :
    pair x y ∈ example6.oneStageFeasiblePayoffs := by
  rcases houter with hx1 | hx2
  · let weights : FourColumn → ℝ
      | FourColumn.c0 => 1 - x
      | FourColumn.c1 => x
      | FourColumn.c2 => 0
      | FourColumn.c3 => 0
    have hweights : weights ∈ stdSimplex ℝ FourColumn := by
      constructor
      · intro column
        cases column <;> simp [weights] <;> linarith
      · rw [sum_fourColumn]
        simp [weights]
    let profile : (who : Bool) → PMF (Example6Action who)
      | false => Math.ProbabilityMassFunction.bernoulliBool
          (1 - y) (by linarith) (by linarith)
      | true => Math.ProbabilityMassFunction.ofVector weights hweights
    refine ⟨profile, ?_⟩
    funext who
    cases who
    · rw [example6_mixedPayoff_false]
      simp [profile, weights, pair, ENNReal.toReal_ofReal hx0]
    · rw [example6_mixedPayoff_true]
      simp [profile, weights, pair, ENNReal.toReal_ofReal hx0,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - x)]
  · let weights : FourColumn → ℝ
      | FourColumn.c0 => 0
      | FourColumn.c1 => 0
      | FourColumn.c2 => 3 - x
      | FourColumn.c3 => x - 2
    have hweights : weights ∈ stdSimplex ℝ FourColumn := by
      constructor
      · intro column
        cases column <;> simp [weights] <;> linarith
      · rw [sum_fourColumn]
        norm_num [weights]
    let profile : (who : Bool) → PMF (Example6Action who)
      | false => Math.ProbabilityMassFunction.bernoulliBool y hy0 hy1
      | true => Math.ProbabilityMassFunction.ofVector weights hweights
    refine ⟨profile, ?_⟩
    funext who
    cases who
    · rw [example6_mixedPayoff_false]
      simp [profile, weights, pair,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ 3 - x),
        ENNReal.toReal_ofReal (by linarith : 0 ≤ x - 2)]
      ring
    · rw [example6_mixedPayoff_true]
      simp [profile, weights, pair,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ 3 - x),
        ENNReal.toReal_ofReal (by linarith : 0 ≤ x - 2)]
      norm_num

/-! The following finite examples require explicit public-history profile
calculations and universal deviation bounds.  They are stated in the paper's
order; no weaker static surrogate is substituted. -/

theorem example1_half_mem_E2 :
    pair (1 / 2) (1 / 2) ∈ example1.finiteEquilibriumPayoffs 2 := by
  obtain ⟨firstProfile, hfirstNash, hfirstPayoff⟩ :=
    lemma_1_E1_subset_En example1 ⟨1, by omega⟩ example1_topLeft_mem_E1
  obtain ⟨secondProfile, hsecondNash, hsecondPayoff⟩ :=
    lemma_1_E1_subset_En example1 ⟨1, by omega⟩ example1_bottomRight_mem_E1
  let joined := example1.appendFiniteProfiles 1 firstProfile secondProfile
  refine ⟨joined, ?_, ?_⟩
  · simpa only [joined, Nat.reduceAdd] using
      appendFiniteProfiles_isHorizonNash example1 1 1 firstProfile secondProfile
        hfirstNash hsecondNash
  · have hweighted :=
      appendFiniteProfiles_weightedPayoff example1 1 1 firstProfile secondProfile
    rw [hfirstPayoff, hsecondPayoff] at hweighted
    norm_num at hweighted
    dsimp only [joined]
    have hpairs :
        pair 1 0 + pair 0 1 =
          (2 : ℝ) • pair (1 / 2) (1 / 2) := by
      ext who
      cases who <;> norm_num [Pi.add_apply, Pi.smul_apply, pair, smul_eq_mul]
    have hsame :
        (2 : ℝ) • example1.finitePayoff 2
            (example1.appendFiniteProfiles 1 firstProfile secondProfile) =
          (2 : ℝ) • pair (1 / 2) (1 / 2) :=
      hweighted.trans hpairs
    exact smul_right_injective (Payoff Bool) (by norm_num) hsame

theorem example1_half_not_mem_D3 :
    pair (1 / 2) (1 / 2) ∉ example1.finiteFeasiblePayoffs 3 := by
  rintro ⟨profile, hpayoff⟩
  letI (player : Bool) : Finite (example1.repeatedGame.Act player) :=
    @Finite.of_fintype _ (example1.finiteAction player)
  letI : Finite example1.repeatedGame.State := inferInstanceAs (Finite PUnit)
  have hrow := congrFun hpayoff false
  have hcolumn := congrFun hpayoff true
  change example1.repeatedGame.finiteAveragePayoff PUnit.unit 3
      profile false = 1 / 2 at hrow
  change example1.repeatedGame.finiteAveragePayoff PUnit.unit 3
      profile true = 1 / 2 at hcolumn
  rw [example1.repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    at hrow hcolumn
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    at hrow hcolumn
  let rowPayoff (time : ℕ) :=
    example1.repeatedGame.expectedStagePayoff profile PUnit.unit time false
  let columnPayoff (time : ℕ) :=
    example1.repeatedGame.expectedStagePayoff profile PUnit.unit time true
  change (3 : ℝ)⁻¹ * (rowPayoff 0 + rowPayoff 1 + rowPayoff 2) = 1 / 2 at hrow
  change (3 : ℝ)⁻¹ *
    (columnPayoff 0 + columnPayoff 1 + columnPayoff 2) = 1 / 2 at hcolumn
  have htotal0 : rowPayoff 0 + columnPayoff 0 = 1 := by
    have hle0 := example1_expectedStageTotal_le_one profile 0
    have hle1 := example1_expectedStageTotal_le_one profile 1
    have hle2 := example1_expectedStageTotal_le_one profile 2
    change rowPayoff 0 + columnPayoff 0 ≤ 1 at hle0
    change rowPayoff 1 + columnPayoff 1 ≤ 1 at hle1
    change rowPayoff 2 + columnPayoff 2 ≤ 1 at hle2
    norm_num at hrow hcolumn
    nlinarith
  have htotal1 : rowPayoff 1 + columnPayoff 1 = 1 := by
    have hle0 := example1_expectedStageTotal_le_one profile 0
    have hle1 := example1_expectedStageTotal_le_one profile 1
    have hle2 := example1_expectedStageTotal_le_one profile 2
    change rowPayoff 0 + columnPayoff 0 ≤ 1 at hle0
    change rowPayoff 1 + columnPayoff 1 ≤ 1 at hle1
    change rowPayoff 2 + columnPayoff 2 ≤ 1 at hle2
    norm_num at hrow hcolumn
    nlinarith
  have htotal2 : rowPayoff 2 + columnPayoff 2 = 1 := by
    have hle0 := example1_expectedStageTotal_le_one profile 0
    have hle1 := example1_expectedStageTotal_le_one profile 1
    have hle2 := example1_expectedStageTotal_le_one profile 2
    change rowPayoff 0 + columnPayoff 0 ≤ 1 at hle0
    change rowPayoff 1 + columnPayoff 1 ≤ 1 at hle1
    change rowPayoff 2 + columnPayoff 2 ≤ 1 at hle2
    norm_num at hrow hcolumn
    nlinarith
  let history0 := example1.repeatedGame.emptyHist PUnit.unit
  let current0 : Bool → PMF Bool :=
    fun player ↦ profile player 0 history0
  have hcurrent0_total :
      example1.mixedPayoff current0 false +
        example1.mixedPayoff current0 true = 1 := by
    rw [← example1_stageEUAt_eq_mixedPayoff profile history0 false,
      ← example1_stageEUAt_eq_mixedPayoff profile history0 true]
    simpa [rowPayoff, columnPayoff, history0] using htotal0
  obtain ⟨diagonal0, hcurrent0false, hcurrent0true⟩ :=
    example1_mixedProfile_pure_diagonal_of_total_eq_one
      current0 hcurrent0_total
  let action0 : example1.repeatedGame.JointAct := fun _ ↦ diagonal0
  have haction0 :
      example1.repeatedGame.stageActionDist profile history0 =
        PMF.pure action0 := by
    unfold StochasticGame.stageActionDist
    have hcurrent : (fun player ↦ profile player 0 history0) =
        fun player ↦ PMF.pure (action0 player) := by
      funext player
      cases player
      · exact hcurrent0false
      · exact hcurrent0true
    change Math.PMFProduct.pmfPi
      (fun player : Bool ↦ profile player 0 history0) = PMF.pure action0
    rw [hcurrent]
    exact Math.PMFProduct.pmfPi_pure action0
  let history1 : example1.repeatedGame.Hist 1 :=
    (Fin.snoc history0.1 (PUnit.unit, action0), PUnit.unit)
  have hhist1 :
      example1.repeatedGame.histDist profile PUnit.unit 1 =
        PMF.pure history1 := by
    simp only [StochasticGame.histDist, PMF.pure_bind]
    rw [show example1.repeatedGame.emptyHist PUnit.unit = history0 by rfl,
      haction0, PMF.pure_bind]
    simp only [history1, history0, StochasticGame.emptyHist]
    change ((PMF.pure PUnit.unit : PMF PUnit).bind fun state ↦
      PMF.pure (history1.1, state)) = PMF.pure history1
    rw [PMF.pure_bind]
    rfl
  have hstage1_total :
      example1.repeatedGame.stageEUAt profile history1 false +
        example1.repeatedGame.stageEUAt profile history1 true = 1 := by
    have htotal := htotal1
    change example1.repeatedGame.expectedStagePayoff profile PUnit.unit 1 false +
      example1.repeatedGame.expectedStagePayoff profile PUnit.unit 1 true = 1
      at htotal
    unfold StochasticGame.expectedStagePayoff at htotal
    rw [hhist1] at htotal
    simpa using htotal
  let current1 : Bool → PMF Bool :=
    fun player ↦ profile player 1 history1
  have hcurrent1_total :
      example1.mixedPayoff current1 false +
        example1.mixedPayoff current1 true = 1 := by
    rw [← example1_stageEUAt_eq_mixedPayoff profile history1 false,
      ← example1_stageEUAt_eq_mixedPayoff profile history1 true]
    exact hstage1_total
  obtain ⟨diagonal1, hcurrent1false, hcurrent1true⟩ :=
    example1_mixedProfile_pure_diagonal_of_total_eq_one
      current1 hcurrent1_total
  let action1 : example1.repeatedGame.JointAct := fun _ ↦ diagonal1
  have haction1 :
      example1.repeatedGame.stageActionDist profile history1 =
        PMF.pure action1 := by
    unfold StochasticGame.stageActionDist
    have hcurrent : (fun player ↦ profile player 1 history1) =
        fun player ↦ PMF.pure (action1 player) := by
      funext player
      cases player
      · exact hcurrent1false
      · exact hcurrent1true
    change Math.PMFProduct.pmfPi
      (fun player : Bool ↦ profile player 1 history1) = PMF.pure action1
    rw [hcurrent]
    exact Math.PMFProduct.pmfPi_pure action1
  let history2 : example1.repeatedGame.Hist 2 :=
    (Fin.snoc history1.1 (PUnit.unit, action1), PUnit.unit)
  have hhist2 :
      example1.repeatedGame.histDist profile PUnit.unit 2 =
        PMF.pure history2 := by
    change example1.repeatedGame.histDist profile PUnit.unit (1 + 1) =
      PMF.pure history2
    rw [example1.repeatedGame.histDist_succ, hhist1, PMF.pure_bind,
      haction1, PMF.pure_bind]
    simp only [history2]
    change ((PMF.pure PUnit.unit : PMF PUnit).bind fun state ↦
      PMF.pure (history2.1, state)) = PMF.pure history2
    rw [PMF.pure_bind]
    rfl
  have hstage2_total :
      example1.repeatedGame.stageEUAt profile history2 false +
        example1.repeatedGame.stageEUAt profile history2 true = 1 := by
    have htotal := htotal2
    change example1.repeatedGame.expectedStagePayoff profile PUnit.unit 2 false +
      example1.repeatedGame.expectedStagePayoff profile PUnit.unit 2 true = 1
      at htotal
    unfold StochasticGame.expectedStagePayoff at htotal
    rw [hhist2] at htotal
    simpa using htotal
  let current2 : Bool → PMF Bool :=
    fun player ↦ profile player 2 history2
  have hcurrent2_total :
      example1.mixedPayoff current2 false +
        example1.mixedPayoff current2 true = 1 := by
    rw [← example1_stageEUAt_eq_mixedPayoff profile history2 false,
      ← example1_stageEUAt_eq_mixedPayoff profile history2 true]
    exact hstage2_total
  obtain ⟨diagonal2, hcurrent2false, hcurrent2true⟩ :=
    example1_mixedProfile_pure_diagonal_of_total_eq_one
      current2 hcurrent2_total
  have hrow0 : rowPayoff 0 = if diagonal0 then 0 else 1 := by
    change example1.repeatedGame.expectedStagePayoff
      profile PUnit.unit 0 false = _
    rw [example1.repeatedGame.expectedStagePayoff_zero,
      example1_stageEUAt_eq_mixedPayoff]
    change example1.mixedPayoff current0 false = _
    rw [binaryGame_mixedPayoff_apply, hcurrent0false, hcurrent0true]
    cases diagonal0 <;> norm_num [pair]
  have hrow1 : rowPayoff 1 = if diagonal1 then 0 else 1 := by
    change example1.repeatedGame.expectedStagePayoff
      profile PUnit.unit 1 false = _
    unfold StochasticGame.expectedStagePayoff
    rw [hhist1]
    simp only [Math.Probability.expect_pure]
    rw [example1_stageEUAt_eq_mixedPayoff]
    change example1.mixedPayoff current1 false = _
    rw [binaryGame_mixedPayoff_apply, hcurrent1false, hcurrent1true]
    cases diagonal1 <;> norm_num [pair]
  have hrow2 : rowPayoff 2 = if diagonal2 then 0 else 1 := by
    change example1.repeatedGame.expectedStagePayoff
      profile PUnit.unit 2 false = _
    unfold StochasticGame.expectedStagePayoff
    rw [hhist2]
    simp only [Math.Probability.expect_pure]
    rw [example1_stageEUAt_eq_mixedPayoff]
    change example1.mixedPayoff current2 false = _
    rw [binaryGame_mixedPayoff_apply, hcurrent2false, hcurrent2true]
    cases diagonal2 <;> norm_num [pair]
  rw [hrow0, hrow1, hrow2] at hrow
  cases diagonal0 <;> cases diagonal1 <;> cases diagonal2 <;>
    norm_num at hrow

/-- The same payoff is not feasible in one stage. -/
theorem example1_half_not_mem_D1 :
    pair (1 / 2) (1 / 2) ∉ example1.oneStageFeasiblePayoffs := by
  rintro ⟨profile, hpayoff⟩
  change (Bool → PMF Bool) at profile
  have hrow := congrFun hpayoff false
  have hcolumn := congrFun hpayoff true
  change (binaryGame (pair 1 0) (pair 0 0) (pair 0 0)
      (pair 0 1)).mixedPayoff profile false = pair (1 / 2) (1 / 2) false at hrow
  change (binaryGame (pair 1 0) (pair 0 0) (pair 0 0)
      (pair 0 1)).mixedPayoff profile true = pair (1 / 2) (1 / 2) true at hcolumn
  rw [binaryGame_mixedPayoff_apply] at hrow hcolumn
  norm_num [pair] at hrow hcolumn
  let p := (profile false true).toReal
  let q := (profile true true).toReal
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  have hq1 : q ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  change (1 - p) * (1 - q) = 1 / 2 at hrow
  change p * q = 1 / 2 at hcolumn
  nlinarith [sq_nonneg (p - q)]

/-- If Example 1 attains aggregate payoff one at every preceding stage, its
public history law remains a point mass. -/
private theorem example1_histDist_eq_pure_of_stageTotals_eq_one
    (profile : example1.BehaviorProfile) (horizon : ℕ)
    (hstage : ∀ time, time < horizon →
      example1.repeatedGame.expectedStagePayoff profile PUnit.unit time false +
        example1.repeatedGame.expectedStagePayoff profile PUnit.unit time true = 1) :
    ∀ time, time ≤ horizon → ∃ history,
      example1.repeatedGame.histDist profile PUnit.unit time = PMF.pure history := by
  intro time htime
  induction time with
  | zero =>
      exact ⟨example1.repeatedGame.emptyHist PUnit.unit, rfl⟩
  | succ time ih =>
      obtain ⟨history, hhistory⟩ := ih (by omega)
      have htime' : time < horizon := by omega
      have htotal := hstage time htime'
      unfold StochasticGame.expectedStagePayoff at htotal
      rw [hhistory] at htotal
      simp only [Math.Probability.expect_pure] at htotal
      rw [example1_stageEUAt_eq_mixedPayoff,
        example1_stageEUAt_eq_mixedPayoff] at htotal
      obtain ⟨diagonal, hfalse, htrue⟩ :=
        example1_mixedProfile_pure_diagonal_of_total_eq_one
          (fun player => profile player time history) htotal
      let action : example1.repeatedGame.JointAct := fun _ => diagonal
      let nextHistory : example1.repeatedGame.Hist (time + 1) :=
        (Fin.snoc history.1 (PUnit.unit, action), PUnit.unit)
      refine ⟨nextHistory, ?_⟩
      rw [example1.repeatedGame.histDist_succ, hhistory, PMF.pure_bind]
      have hactions : example1.repeatedGame.stageActionDist profile history =
          PMF.pure action := by
        unfold StochasticGame.stageActionDist
        have hprofile : (fun player => profile player time history) =
            fun player => PMF.pure (action player) := by
          funext player
          cases player
          · exact hfalse
          · exact htrue
        rw [hprofile]
        exact Math.PMFProduct.pmfPi_pure action
      rw [hactions, PMF.pure_bind]
      simp only [FiniteStageGame.repeatedGame,
        KernelGame.realizedActionStochasticGame, PMF.pure_bind]
      rfl

/-- On the Pareto boundary of Example 1, every expected row-stage payoff is
zero or one. -/
private theorem example1_expectedStagePayoff_false_eq_bool
    (profile : example1.BehaviorProfile) (horizon time : ℕ)
    (hstage : ∀ t, t < horizon →
      example1.repeatedGame.expectedStagePayoff profile PUnit.unit t false +
        example1.repeatedGame.expectedStagePayoff profile PUnit.unit t true = 1)
    (htime : time < horizon) :
    ∃ diagonal : Bool,
      example1.repeatedGame.expectedStagePayoff profile PUnit.unit time false =
        if diagonal then 0 else 1 := by
  obtain ⟨history, hhistory⟩ :=
    example1_histDist_eq_pure_of_stageTotals_eq_one
      profile horizon hstage time htime.le
  have htotal := hstage time htime
  unfold StochasticGame.expectedStagePayoff at htotal ⊢
  rw [hhistory] at htotal ⊢
  simp only [Math.Probability.expect_pure] at htotal ⊢
  rw [example1_stageEUAt_eq_mixedPayoff,
    example1_stageEUAt_eq_mixedPayoff] at htotal
  obtain ⟨diagonal, hfalse, htrue⟩ :=
    example1_mixedProfile_pure_diagonal_of_total_eq_one
      (fun player => profile player time history) htotal
  refine ⟨diagonal, ?_⟩
  rw [example1_stageEUAt_eq_mixedPayoff]
  rw [binaryGame_mixedPayoff_apply, hfalse, htrue]
  cases diagonal <;> norm_num [pair]

/-! The paper also notes that no positive finite horizon convexifies Example 1.
Its Pareto-boundary argument requires a reusable characterization of equality
in the convex-hull bound, which is not yet available for the monitored
adapter. -/
theorem example1_no_finite_convexification (n : example1.Horizon) :
    example1.finiteFeasiblePayoffsOnHorizon n ≠
      example1.correlatedFeasiblePayoffs := by
  intro heq
  let weight : ℝ := 1 / ((n.1 : ℝ) + 1)
  let target : Payoff Bool := pair weight (1 - weight)
  have hweight0 : 0 ≤ weight := by
    dsimp only [weight]
    positivity
  have hweight1 : weight ≤ 1 := by
    dsimp only [weight]
    have hdenom : (0 : ℝ) < (n.1 : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hdenom]
    linarith
  have hleft : pair 1 0 ∈ example1.purePayoffSet := by
    refine ⟨fun _ => false, ?_⟩
    funext who
    cases who <;> rfl
  have hright : pair 0 1 ∈ example1.purePayoffSet := by
    refine ⟨fun _ => true, ?_⟩
    funext who
    cases who <;> rfl
  have htargetC : target ∈ example1.correlatedFeasiblePayoffs := by
    have hleftHull := (subset_convexHull ℝ example1.purePayoffSet) hleft
    have hrightHull := (subset_convexHull ℝ example1.purePayoffSet) hright
    have hcomb := example1.correlatedFeasiblePayoffs_convex
      hleftHull hrightHull (a := weight) (b := 1 - weight)
      hweight0 (by linarith) (by ring)
    convert hcomb using 1
    funext who
    cases who <;> simp [target, weight]
  obtain ⟨profile, hpayoff⟩ :
      ∃ profile, example1.finitePayoff n.1 profile = target := by
    rw [← heq] at htargetC
    exact htargetC
  have htotalPayoff :
      example1.finitePayoff n.1 profile false +
        example1.finitePayoff n.1 profile true = 1 := by
    rw [hpayoff]
    simp [target]
  let stageTotal : ℕ → ℝ := fun time =>
    example1.repeatedGame.expectedStagePayoff profile PUnit.unit time false +
      example1.repeatedGame.expectedStagePayoff profile PUnit.unit time true
  have hstageLe (time : ℕ) : stageTotal time ≤ 1 :=
    example1_expectedStageTotal_le_one profile time
  have hsum : ∑ time ∈ Finset.range n.1, stageTotal time = n.1 := by
    have hfalse := congrFun
      (cast_smul_finitePayoff_eq_sum example1 n.1 profile) false
    have htrue := congrFun
      (cast_smul_finitePayoff_eq_sum example1 n.1 profile) true
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hfalse htrue
    unfold stageTotal
    rw [Finset.sum_add_distrib, ← hfalse, ← htrue]
    change (n.1 : ℝ) * example1.finitePayoff n.1 profile false +
        (n.1 : ℝ) * example1.finitePayoff n.1 profile true = _
    rw [← mul_add, htotalPayoff]
    simp
  have hstage : ∀ time, time < n.1 → stageTotal time = 1 := by
    intro time htime
    have hlossNonneg : ∀ t ∈ Finset.range n.1,
        0 ≤ 1 - stageTotal t := by
      intro t _
      linarith [hstageLe t]
    have hlossSum : ∑ t ∈ Finset.range n.1, (1 - stageTotal t) = 0 := by
      rw [Finset.sum_sub_distrib]
      simp [hsum]
    exact (sub_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg hlossNonneg).mp hlossSum
        time (Finset.mem_range.mpr htime))).symm
  have hbool : ∀ time, time < n.1 → ∃ diagonal : Bool,
      example1.repeatedGame.expectedStagePayoff profile PUnit.unit time false =
        if diagonal then 0 else 1 := by
    intro time htime
    exact example1_expectedStagePayoff_false_eq_bool
      profile n.1 time (fun t ht => hstage t ht) htime
  let diagonal : ℕ → Bool := fun time =>
    if htime : time < n.1 then Classical.choose (hbool time htime) else false
  have hdiagonal : ∀ time, time < n.1 →
      example1.repeatedGame.expectedStagePayoff profile PUnit.unit time false =
        if diagonal time then 0 else 1 := by
    intro time htime
    simpa only [diagonal, dif_pos htime] using
      Classical.choose_spec (hbool time htime)
  have hrow := congrFun hpayoff false
  have hrowSum := congrFun
    (cast_smul_finitePayoff_eq_sum example1 n.1 profile) false
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hrowSum
  rw [hrow] at hrowSum
  change (n.1 : ℝ) * weight = _ at hrowSum
  have hsumBool :
      (∑ time ∈ Finset.range n.1,
          example1.repeatedGame.expectedStagePayoff profile
            example1.repeatedInitial time false) =
        ∑ time ∈ Finset.range n.1, if diagonal time then 0 else 1 := by
    apply Finset.sum_congr rfl
    intro time htime
    simpa only [FiniteStageGame.repeatedInitial] using
      hdiagonal time (Finset.mem_range.mp htime)
  rw [hsumBool] at hrowSum
  let count := (Finset.range n.1 |>.filter fun time => ¬diagonal time).card
  have hcount : (∑ time ∈ Finset.range n.1,
      if diagonal time then (0 : ℝ) else 1) =
      count := by
    calc
      _ = ∑ time ∈ Finset.range n.1,
          if ¬diagonal time then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro time _
        by_cases h : diagonal time <;> simp [h]
      _ = count := by
        rw [Finset.sum_boole]
  rw [hcount] at hrowSum
  have hcountNonneg : (0 : ℝ) ≤ count := by positivity
  have hnpos : (0 : ℝ) < n.1 := by exact_mod_cast n.2
  have hdenom : (0 : ℝ) < n.1 + 1 := by positivity
  dsimp only [weight] at hrowSum
  by_cases hcountZero : count = 0
  · rw [hcountZero] at hrowSum
    norm_num at hrowSum
    rcases hrowSum with hnzero | hdenomZero
    · exact (Nat.ne_of_gt n.2) hnzero
    · exact (ne_of_gt hdenom) hdenomZero
  · have hcountOne : (1 : ℝ) ≤ count := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcountZero
    field_simp [ne_of_gt hdenom] at hrowSum
    have hlarge : (n.1 : ℝ) + 1 ≤
        ((n.1 : ℝ) + 1) * count :=
      by simpa using mul_le_mul_of_nonneg_left hcountOne hdenom.le
    nlinarith

/-- Equation (11): neither `Dₙ` nor `Eₙ` is monotone in general.
The paper's Example 1 witnesses both failures for the same positive horizon. -/
theorem equation_11 :
    ∃ G : FiniteStageGame, ∃ n : G.Horizon,
      (¬G.finiteFeasiblePayoffsOnHorizon n ⊆
        G.finiteFeasiblePayoffs (n.1 + 1)) ∧
      (¬G.finiteEquilibriumPayoffsOnHorizon n ⊆
        G.finiteEquilibriumPayoffs (n.1 + 1)) := by
  refine ⟨example1, ⟨2, by omega⟩, ?_, ?_⟩
  · intro hinclusion
    apply example1_half_not_mem_D3
    rcases example1_half_mem_E2 with ⟨profile, _hnash, hpayoff⟩
    exact hinclusion ⟨profile, hpayoff⟩
  · intro hinclusion
    apply example1_half_not_mem_D3
    rcases hinclusion example1_half_mem_E2 with
      ⟨profile, _hnash, hpayoff⟩
    exact ⟨profile, hpayoff⟩

theorem example2_D1_eq_C :
    example2.oneStageFeasiblePayoffs = example2.correlatedFeasiblePayoffs := by
  have hconvex : Convex ℝ example2.oneStageFeasiblePayoffs := by
    change Convex ℝ ((binaryGame (pair 1 0) (pair 2 2) (pair 0 0)
      (pair 0 1)).oneStageFeasiblePayoffs)
    rintro _ ⟨first, rfl⟩ _ ⟨second, rfl⟩ a b ha hb hab
    change (Bool → PMF Bool) at first second
    let p₁ := (first false true).toReal
    let q₁ := (first true true).toReal
    let p₂ := (second false true).toReal
    let q₂ := (second true true).toReal
    have hp₁₀ : 0 ≤ p₁ := ENNReal.toReal_nonneg
    have hq₁₀ : 0 ≤ q₁ := ENNReal.toReal_nonneg
    have hp₂₀ : 0 ≤ p₂ := ENNReal.toReal_nonneg
    have hq₂₀ : 0 ≤ q₂ := ENNReal.toReal_nonneg
    have hp₁₁ : p₁ ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    have hq₁₁ : q₁ ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    have hp₂₁ : p₂ ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    have hq₂₁ : q₂ ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    let x₁ := (1 - p₁) * (1 + q₁)
    let y₁ := q₁ * (2 - p₁)
    let x₂ := (1 - p₂) * (1 + q₂)
    let y₂ := q₂ * (2 - p₂)
    have hfirstFalse :
        (binaryGame (pair 1 0) (pair 2 2) (pair 0 0)
          (pair 0 1)).mixedPayoff first false = x₁ := by
      rw [binaryGame_mixedPayoff_apply]
      simp only [pair_false]
      dsimp [x₁, p₁, q₁]
      ring
    have hfirstTrue :
        (binaryGame (pair 1 0) (pair 2 2) (pair 0 0)
          (pair 0 1)).mixedPayoff first true = y₁ := by
      rw [binaryGame_mixedPayoff_apply]
      simp only [pair_true]
      dsimp [y₁, p₁, q₁]
      ring
    have hsecondFalse :
        (binaryGame (pair 1 0) (pair 2 2) (pair 0 0)
          (pair 0 1)).mixedPayoff second false = x₂ := by
      rw [binaryGame_mixedPayoff_apply]
      simp only [pair_false]
      dsimp [x₂, p₂, q₂]
      ring
    have hsecondTrue :
        (binaryGame (pair 1 0) (pair 2 2) (pair 0 0)
          (pair 0 1)).mixedPayoff second true = y₂ := by
      rw [binaryGame_mixedPayoff_apply]
      simp only [pair_true]
      dsimp [y₂, p₂, q₂]
      ring
    let x := a * x₁ + b * x₂
    let y := a * y₁ + b * y₂
    let s := 1 - x + y
    have hx₁₀ : 0 ≤ x₁ := by
      exact mul_nonneg (sub_nonneg.mpr hp₁₁) (by linarith)
    have hy₁₀ : 0 ≤ y₁ := by
      exact mul_nonneg hq₁₀ (by linarith)
    have hx₂₀ : 0 ≤ x₂ := by
      exact mul_nonneg (sub_nonneg.mpr hp₂₁) (by linarith)
    have hy₂₀ : 0 ≤ y₂ := by
      exact mul_nonneg hq₂₀ (by linarith)
    have hx0 : 0 ≤ x :=
      add_nonneg (mul_nonneg ha hx₁₀) (mul_nonneg hb hx₂₀)
    have hy0 : 0 ≤ y :=
      add_nonneg (mul_nonneg ha hy₁₀) (mul_nonneg hb hy₂₀)
    have hsEq : s = a * (p₁ + q₁) + b * (p₂ + q₂) := by
      dsimp [s, x, y, x₁, y₁, x₂, y₂]
      nlinarith
    have hs0 : 0 ≤ s := by
      rw [hsEq]
      exact add_nonneg (mul_nonneg ha (add_nonneg hp₁₀ hq₁₀))
        (mul_nonneg hb (add_nonneg hp₂₀ hq₂₀))
    have hs2 : s ≤ 2 := by
      rw [hsEq]
      have hsum₁ : p₁ + q₁ ≤ 2 := by linarith
      have hsum₂ : p₂ + q₂ ≤ 2 := by linarith
      calc
        a * (p₁ + q₁) + b * (p₂ + q₂) ≤ a * 2 + b * 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hsum₁ ha)
            (mul_le_mul_of_nonneg_left hsum₂ hb)
        _ = 2 := by linarith
    have hedgeLower₁ : 2 * x₁ - y₁ ≤ 2 := by
      dsimp [x₁, y₁]
      nlinarith [mul_nonneg hp₁₀ (by linarith : 0 ≤ 2 + q₁)]
    have hedgeLower₂ : 2 * x₂ - y₂ ≤ 2 := by
      dsimp [x₂, y₂]
      nlinarith [mul_nonneg hp₂₀ (by linarith : 0 ≤ 2 + q₂)]
    have hedgeLower : 2 * x - y ≤ 2 := by
      dsimp [x, y]
      nlinarith
    have hedgeUpper₁ : 2 * y₁ - x₁ ≤ 2 := by
      dsimp [x₁, y₁]
      nlinarith [mul_nonneg (sub_nonneg.mpr hq₁₁)
        (sub_nonneg.mpr (hp₁₁.trans (by norm_num : (1 : ℝ) ≤ 3)))]
    have hedgeUpper₂ : 2 * y₂ - x₂ ≤ 2 := by
      dsimp [x₂, y₂]
      nlinarith [mul_nonneg (sub_nonneg.mpr hq₂₁)
        (sub_nonneg.mpr (hp₂₁.trans (by norm_num : (1 : ℝ) ≤ 3)))]
    have hedgeUpper : 2 * y - x ≤ 2 := by
      dsimp [x, y]
      nlinarith
    let f : ℝ → ℝ := fun q ↦ q * (2 - s + q)
    have hf : Continuous f := by
      fun_prop
    obtain ⟨q, hq0, hq1, hp0, hp1, hqeq⟩ :
        ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ 0 ≤ s - q ∧ s - q ≤ 1 ∧ f q = y := by
      by_cases hs1 : s ≤ 1
      · have hyUpper : y ≤ f s := by
          calc
            y ≤ 2 * s := by
              dsimp [s]
              linarith [hedgeLower]
            _ = f s := by
              dsimp [f]
              ring
        have hyIcc : y ∈ Set.Icc (f 0) (f s) := by
          constructor
          · simpa [f] using hy0
          · exact hyUpper
        obtain ⟨q, hq, hqy⟩ :=
          intermediate_value_Icc hs0 hf.continuousOn hyIcc
        exact ⟨q, hq.1, hq.2.trans hs1, sub_nonneg.mpr hq.2,
          by linarith [hq.1], hqy⟩
      · have hs1' : 1 ≤ s := le_of_not_ge hs1
        have hyLower : f (s - 1) ≤ y := by
          calc
            f (s - 1) = s - 1 := by
              dsimp [f]
              ring
            _ ≤ y := by
              dsimp [s]
              linarith
        have hyUpper : y ≤ f 1 := by
          calc
            y ≤ 3 - s := by
              dsimp [s]
              linarith [hedgeUpper]
            _ = f 1 := by
              dsimp [f]
              ring
        have hyIcc : y ∈ Set.Icc (f (s - 1)) (f 1) :=
          ⟨hyLower, hyUpper⟩
        obtain ⟨q, hq, hqy⟩ :=
          intermediate_value_Icc (by linarith) hf.continuousOn hyIcc
        exact ⟨q, (by linarith [hq.1]), hq.2,
          (by linarith [hq.2]), (by linarith [hq.1]), hqy⟩
    let p := s - q
    let profile : Bool → PMF Bool := fun who ↦
      if who then
        Math.ProbabilityMassFunction.bernoulliBool q hq0 hq1
      else
        Math.ProbabilityMassFunction.bernoulliBool p hp0 hp1
    refine ⟨profile, ?_⟩
    funext who
    cases who
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
          (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
            (pair 0 1))).mixedExtension.eu profile false = _
      rw [example2_mixedEU_false, hfirstFalse, hsecondFalse]
      simp only [profile, Bool.false_eq_true, if_false, if_true,
        Math.ProbabilityMassFunction.bernoulliBool_true_toReal]
      change (1 - p) * (1 + q) = x
      have hxFromSY : x = 1 - s + y := by
        dsimp [s]
        ring
      rw [hxFromSY]
      dsimp [f] at hqeq
      calc
        (1 - p) * (1 + q) = 1 - s + q * (2 - s + q) := by
          dsimp [p]
          ring
        _ = 1 - s + y := by rw [hqeq]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
          (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
            (pair 0 1))).mixedExtension.eu profile true = _
      rw [example2_mixedEU_true, hfirstTrue, hsecondTrue]
      simp only [profile, if_true, Bool.false_eq_true, if_false,
        Math.ProbabilityMassFunction.bernoulliBool_true_toReal]
      change q * (2 - p) = y
      rw [show 2 - p = 2 - s + q by dsimp [p]; ring]
      simpa only [f] using hqeq
  apply Set.Subset.antisymm
  · rintro _ ⟨profile, rfl⟩
    exact FiniteStageGame.mixedPayoff_mem_correlatedFeasiblePayoffs _ profile
  · exact convexHull_min (lemma_1_pure_subset_D1 _) hconvex

theorem example2_E1_eq_singleton :
    example2.oneStageEquilibriumPayoffs = {pair 2 2} := by
  change (binaryGame (pair 1 0) (pair 2 2) (pair 0 0)
      (pair 0 1)).oneStageEquilibriumPayoffs =
    ({pair 2 2} : Set (Payoff Bool))
  apply Set.Subset.antisymm
  · rintro payoff ⟨profile, hnash, rfl⟩
    change (Bool → PMF Bool) at profile
    change (binaryGame (pair 1 0) (pair 2 2) (pair 0 0)
      (pair 0 1)).mixedPayoff profile ∈ ({pair 2 2} : Set (Payoff Bool))
    change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
        (pair 0 1))).mixedExtension.IsNash profile at hnash
    have hrow := hnash false (PMF.pure false)
    have hcolumn := hnash true (PMF.pure true)
    rw [example2_mixedEU_false, example2_mixedEU_update_false_pure] at hrow
    rw [example2_mixedEU_true, example2_mixedEU_update_true_pure] at hcolumn
    let p := (profile false true).toReal
    let q := (profile true true).toReal
    have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
    have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
    have hp1 : p ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    have hq1 : q ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    change (1 - p) * (1 + q) ≥ 1 + q at hrow
    change q * (2 - p) ≥ 2 - p at hcolumn
    have hp : p = 0 := by nlinarith
    have hq : q = 1 := by nlinarith
    apply Set.mem_singleton_iff.mpr
    funext who
    cases who <;> rw [binaryGame_mixedPayoff_apply] <;>
      norm_num [pair, p, q, hp, hq]
  · rintro _ rfl
    let profile : Bool → PMF Bool :=
      fun who ↦ PMF.pure (if who then true else false)
    refine ⟨profile, ?_, ?_⟩
    · change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
        (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
          (pair 0 1))).mixedExtension.IsNash profile
      intro who deviation
      change PMF Bool at deviation
      cases who
      · rw [example2_mixedEU_false, example2_mixedEU_update_false]
        norm_num [profile]
      · rw [example2_mixedEU_true, example2_mixedEU_update_true]
        norm_num [profile]
        exact ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    · funext who
      cases who <;> rw [binaryGame_mixedPayoff_apply] <;>
        norm_num [profile, pair]

/-- Every one-stage payoff of Example 2 lies between zero and two. -/
private theorem example2_eu_bounds
    (profile : Bool → PMF Bool) (who : Bool) :
    0 ≤ example2.kernel.mixedExtension.eu profile who ∧
      example2.kernel.mixedExtension.eu profile who ≤ 2 := by
  have hp0 : 0 ≤ (profile false true).toReal := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ (profile true true).toReal := ENNReal.toReal_nonneg
  have hp1 : (profile false true).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  have hq1 : (profile true true).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  cases who
  · change 0 ≤ (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
        (pair 0 1))).mixedExtension.eu profile false ∧
      (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
        (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
          (pair 0 1))).mixedExtension.eu profile false ≤ 2
    rw [example2_mixedEU_false]
    constructor <;> nlinarith
  · change 0 ≤ (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
        (pair 0 1))).mixedExtension.eu profile true ∧
      (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
        (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
          (pair 0 1))).mixedExtension.eu profile true ≤ 2
    rw [example2_mixedEU_true]
    constructor <;> nlinarith

/-- Example 2's two-stage strategy: Bottom/Left, then copy the opponent's
first action. -/
private def example2TwoStageProfile : example2.StandardMonitoredProfile :=
  fun who time history ↦
    match time with
    | 0 => PMF.pure (if who = true then false else true)
    | _ + 1 => PMF.pure (history 0 (!who))

/-- The prescribed two-stage path gives each player average payoff one. -/
private theorem example2TwoStageProfile_payoff (who : Bool) :
    example2.kernel.realizedActionMonitoring.finiteAveragePayoff
      2 example2TwoStageProfile who = 1 := by
  let M := example2.kernel.realizedActionMonitoring
  rw [show M.finiteAveragePayoff 2 example2TwoStageProfile who =
      2⁻¹ * (M.stageEU example2TwoStageProfile 0 who +
        M.stageEU example2TwoStageProfile 1 who) by
    simp [KernelGame.PublicMonitoring.finiteAveragePayoff,
      Finset.sum_range_succ]]
  rw [M.stageEU_zero]
  rw [M.stageEU_succ_eq_expect_afterSignal
    (C := 2) (hbd := fun profile ↦ by
      rw [abs_le]
      have hbounds := example2_eu_bounds profile who
      exact ⟨by linarith [hbounds.1], hbounds.2⟩)]
  simp only [M, KernelGame.PublicMonitoring.stageEU_zero,
    KernelGame.PublicMonitoring.afterSignal_apply]
  let initial : Bool → PMF Bool :=
    fun i ↦ example2TwoStageProfile i 0 (fun k ↦ k.elim0)
  let second : (Bool → Bool) → Bool → PMF Bool := fun signal i ↦
    example2TwoStageProfile i 1 (Fin.cons signal fun k ↦ k.elim0)
  change 2⁻¹ * (example2.kernel.mixedExtension.eu initial who +
    Math.Probability.expect (Math.PMFProduct.pmfPi initial)
      (fun signal ↦ example2.kernel.mixedExtension.eu (second signal) who)) = 1
  cases who
  · rw [example2_mixedEU_false]
    rw [Math.PMFProduct.expect_pmfPi_bool]
    simp [initial, second, example2TwoStageProfile,
      Math.Probability.expect_pure, PMF.pure_apply]
    rw [example2_mixedEU_false]
    norm_num [PMF.pure_apply]
  · rw [example2_mixedEU_true]
    rw [Math.PMFProduct.expect_pmfPi_bool]
    simp [initial, second, example2TwoStageProfile,
      Math.Probability.expect_pure, PMF.pure_apply]
    rw [example2_mixedEU_true]
    norm_num [PMF.pure_apply]

/-- No unilateral two-stage deviation earns more than total payoff two. -/
private theorem example2TwoStageProfile_deviation_bound
    (who : Bool) (deviation : example2.StandardMonitoredStrategy who) :
    example2.kernel.realizedActionMonitoring.finiteAveragePayoff 2
      (Function.update example2TwoStageProfile who deviation) who ≤ 1 := by
  letI : Finite example2.kernel.Outcome := by
    change Finite (∀ _ : Bool, Bool)
    exact Finite.of_fintype _
  let M := example2.kernel.realizedActionMonitoring
  let deviated := Function.update example2TwoStageProfile who deviation
  rw [show M.finiteAveragePayoff 2 deviated who =
      2⁻¹ * (M.stageEU deviated 0 who + M.stageEU deviated 1 who) by
    simp [KernelGame.PublicMonitoring.finiteAveragePayoff,
      Finset.sum_range_succ]]
  rw [M.stageEU_zero]
  rw [M.stageEU_succ_eq_expect_afterSignal
    (C := 2) (hbd := fun profile ↦ by
      rw [abs_le]
      have hbounds := example2_eu_bounds profile who
      exact ⟨by linarith [hbounds.1], hbounds.2⟩)]
  simp only [M, KernelGame.PublicMonitoring.stageEU_zero,
    KernelGame.PublicMonitoring.afterSignal_apply]
  let initial : Bool → PMF Bool := fun i ↦ deviated i 0 (fun k ↦ k.elim0)
  have hinitial : example2.kernel.mixedExtension.eu initial who =
      Math.Probability.expect (Math.PMFProduct.pmfPi initial)
        (fun action ↦ example2.payoff action who) := by
    rw [example2.kernel.mixedExtension_eu]
    congr 1
    funext action
    simp [example2, FiniteStageGame.kernel, binaryGame,
      KernelGame.eu_ofPureEU]
  change 2⁻¹ * (example2.kernel.mixedExtension.eu initial who +
    Math.Probability.expect (Math.PMFProduct.pmfPi initial)
      (fun signal ↦ example2.kernel.mixedExtension.eu
        (fun i ↦ deviated i 1 (Fin.cons signal fun k ↦ k.elim0)) who)) ≤ 1
  rw [hinitial, ← Math.Probability.expect_add]
  have htotal : Math.Probability.expect (Math.PMFProduct.pmfPi initial)
      (fun signal ↦ example2.payoff signal who +
        example2.kernel.mixedExtension.eu
          (fun i ↦ deviated i 1 (Fin.cons signal fun k ↦ k.elim0)) who) ≤ 2 := by
    change Bool at who
    cases who
    · rw [Math.PMFProduct.expect_pmfPi_bool]
      change (t : ℕ) → (Fin t → Bool → Bool) → PMF Bool at deviation
      simp [initial, deviated, example2TwoStageProfile,
        Math.Probability.expect_pure]
      calc
        _ ≤ Math.Probability.expect (deviation 0 (fun k ↦ k.elim0))
            (fun _ ↦ 2) := by
          apply Math.Probability.expect_mono
          intro action
          let signal : Bool → Bool := fun coordinate ↦ !coordinate && action
          let second : Bool → PMF Bool :=
            fun i ↦ Function.update example2TwoStageProfile false deviation i 1
              (Fin.cons signal fun k ↦ k.elim0)
          change binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
              (pair 0 1) signal false +
            (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
              (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
                (pair 0 1))).mixedExtension.eu second false ≤ 2
          rw [example2_mixedEU_false]
          let devAt : PMF Bool :=
            deviation 1 (Fin.cons signal fun k ↦ k.elim0)
          have hself : second false = devAt := rfl
          have hother : second true = PMF.pure action := by
            simp [second, example2TwoStageProfile, signal]
          rw [hself, hother]
          have hp0 : 0 ≤ (devAt true).toReal := ENNReal.toReal_nonneg
          have hp1 : (devAt true).toReal ≤ 1 :=
            ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
          cases action <;>
            simp [signal, binaryPayoff, pair, PMF.pure_apply] <;> nlinarith
        _ = 2 := Math.Probability.expect_const _ 2
    · rw [Math.PMFProduct.expect_pmfPi_bool]
      change (t : ℕ) → (Fin t → Bool → Bool) → PMF Bool at deviation
      simp [initial, deviated, example2TwoStageProfile,
        Math.Probability.expect_pure]
      calc
        _ ≤ Math.Probability.expect (deviation 0 (fun k ↦ k.elim0))
            (fun _ ↦ 2) := by
          apply Math.Probability.expect_mono
          intro action
          let signal : Bool → Bool := fun coordinate ↦ !coordinate || action
          let second : Bool → PMF Bool :=
            fun i ↦ Function.update example2TwoStageProfile true deviation i 1
              (Fin.cons signal fun k ↦ k.elim0)
          change binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
              (pair 0 1) signal true +
            (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
              (binaryPayoff (pair 1 0) (pair 2 2) (pair 0 0)
                (pair 0 1))).mixedExtension.eu second true ≤ 2
          rw [example2_mixedEU_true]
          let devAt : PMF Bool :=
            deviation 1 (Fin.cons signal fun k ↦ k.elim0)
          have hself : second true = devAt := rfl
          have hother : second false = PMF.pure action := by
            simp [second, example2TwoStageProfile, signal]
          rw [hself, hother]
          have hq0 : 0 ≤ (devAt true).toReal := ENNReal.toReal_nonneg
          have hq1 : (devAt true).toReal ≤ 1 :=
            ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
          cases action <;>
            simp [signal, binaryPayoff, pair, PMF.pure_apply] <;> nlinarith
        _ = 2 := Math.Probability.expect_const _ 2
  norm_num
  linarith

theorem example2_one_one_mem_E2 :
    pair 1 1 ∈ example2.finiteEquilibriumPayoffs 2 := by
  letI : Finite example2.kernel.Outcome := by
    change Finite (∀ _ : Bool, Bool)
    exact Finite.of_fintype _
  letI (who : Bool) : Finite (example2.kernel.Strategy who) := by
    change Finite Bool
    exact Finite.of_fintype _
  let behavior :=
    KernelGame.RealizedActionRepeatedAdapter.toBehaviorProfile
      example2.kernel example2TwoStageProfile
  refine ⟨behavior, ?_, ?_⟩
  · apply (KernelGame.RealizedActionRepeatedAdapter.isεFiniteRepeatedNash_iff_isεHorizonNash
      example2.kernel example2TwoStageProfile 2 0).mp
    intro who deviation
    rw [add_zero, example2TwoStageProfile_payoff]
    exact example2TwoStageProfile_deviation_bound who deviation
  · funext who
    rw [show example2.finitePayoff 2 behavior who =
        example2.kernel.realizedActionMonitoring.finiteAveragePayoff
          2 example2TwoStageProfile who from
      KernelGame.RealizedActionRepeatedAdapter.finiteAveragePayoff_toBehaviorProfile
        example2.kernel example2TwoStageProfile 2 who]
    rw [example2TwoStageProfile_payoff]
    cases who <;> rfl

/-- Equation (12), with the paper's positive-horizon domain explicit. -/
theorem equation_12 :
    ∃ G : FiniteStageGame, ∃ n : G.Horizon,
      G.finiteFeasiblePayoffsOnHorizon n =
          G.finiteFeasiblePayoffs (n.1 + 1) ∧
        G.finiteEquilibriumPayoffsOnHorizon n ≠
          G.finiteEquilibriumPayoffs (n.1 + 1) := by
  let n : example2.Horizon := ⟨1, by omega⟩
  refine ⟨example2, n, ?_, ?_⟩
  · calc
      example2.finiteFeasiblePayoffsOnHorizon n =
          example2.finiteFeasiblePayoffs 1 := rfl
      _ =
          example2.oneStageFeasiblePayoffs :=
        finiteFeasiblePayoffs_one_eq_oneStageFeasiblePayoffs example2
      _ = example2.correlatedFeasiblePayoffs := example2_D1_eq_C
      _ = example2.finiteFeasiblePayoffs 2 :=
        (finiteFeasiblePayoffs_eq_correlated_of_oneStage_eq
          example2 example2_D1_eq_C ⟨2, by omega⟩).symm
      _ = example2.finiteFeasiblePayoffs (n.1 + 1) := rfl
  · intro heq
    have hone : pair 1 1 ∈ example2.finiteEquilibriumPayoffs 1 := by
      change pair 1 1 ∈ example2.finiteEquilibriumPayoffsOnHorizon n
      rw [heq]
      simpa [n] using example2_one_one_mem_E2
    rw [finiteEquilibriumPayoffs_one_eq_oneStageEquilibriumPayoffs,
      example2_E1_eq_singleton] at hone
    have hequal : pair 1 1 = pair 2 2 := Set.mem_singleton_iff.mp hone
    have hfalse := congrFun hequal false
    norm_num [pair] at hfalse

theorem example3_En : ∀ n, 0 < n →
    example3.finiteEquilibriumPayoffs n =
      {v | v false = 1 ∧ 0 ≤ v true ∧ v true ≤ 1} := by
  intro n hn
  let horizon : example3.Horizon := ⟨n, hn⟩
  apply Set.Subset.antisymm
  · rintro v ⟨profile, hnash, rfl⟩
    have hdelta := lemma_1_En_subset_Delta example3 horizon
      ⟨profile, hnash, rfl⟩
    have hbounds := example3_correlated_bounds hdelta.1
    have hrowLower := hdelta.2 false
    rw [example3_individualRationalLevel_false] at hrowLower
    exact ⟨le_antisymm hbounds.1 hrowLower, hbounds.2⟩
  · rintro v ⟨hvrow, hvcolumn0, hvcolumn1⟩
    let p := 1 - v true
    have hp0 : 0 ≤ p := by dsimp only [p]; linarith
    have hp1 : p ≤ 1 := by dsimp only [p]; linarith
    let profile : Bool → PMF Bool := fun who ↦
      if who then PMF.pure true else
        Math.ProbabilityMassFunction.bernoulliBool p hp0 hp1
    have honeStage : v ∈ example3.oneStageEquilibriumPayoffs := by
      refine ⟨profile, ?_, ?_⟩
      · change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
          (binaryPayoff (pair 1 0) (pair 1 1) (pair 0 0)
            (pair 1 0))).mixedExtension.IsNash profile
        intro who deviation
        cases who
        · rw [binaryKernel_mixedEU_apply, binaryKernel_mixedEU_apply]
          simp only [profile, Bool.false_eq_true, if_false, if_true,
            Math.ProbabilityMassFunction.bernoulliBool_true_toReal]
          norm_num [pair]
        · rw [binaryKernel_mixedEU_apply, binaryKernel_mixedEU_apply]
          change PMF Bool at deviation
          have hdeviation0 : 0 ≤ (deviation true).toReal := ENNReal.toReal_nonneg
          have hdeviation1 : (deviation true).toReal ≤ 1 :=
            ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
          simp only [profile, if_true, Bool.false_eq_true, if_false,
            Math.ProbabilityMassFunction.bernoulliBool_true_toReal]
          norm_num [pair]
          dsimp only [p] at *
          nlinarith [mul_le_mul_of_nonneg_right hdeviation1 hvcolumn0]
      · change (binaryGame (pair 1 0) (pair 1 1) (pair 0 0)
          (pair 1 0)).mixedPayoff profile = v
        funext who
        cases who
        · rw [binaryGame_mixedPayoff_apply]
          simp only [profile, Bool.false_eq_true, if_false, if_true,
            Math.ProbabilityMassFunction.bernoulliBool_true_toReal]
          norm_num [pair]
          exact hvrow.symm
        · rw [binaryGame_mixedPayoff_apply]
          simp only [profile, if_true, Bool.false_eq_true, if_false,
            Math.ProbabilityMassFunction.bernoulliBool_true_toReal]
          norm_num [pair]
          dsimp only [p]
          ring
    exact lemma_1_E1_subset_En example3 horizon honeStage

theorem example3_half_mem_D2_not_D1 :
    pair (1 / 2) (1 / 2) ∈ example3.finiteFeasiblePayoffs 2 ∧
      pair (1 / 2) (1 / 2) ∉ example3.oneStageFeasiblePayoffs := by
  constructor
  · let topRight : (who : Bool) → Bool := fun who ↦ who
    have htopRightPure : pair 1 1 ∈ example3.purePayoffSet := by
      refine ⟨topRight, ?_⟩
      funext who
      cases who <;> rfl
    let bottomLeft : (who : Bool) → Bool
      | false => true
      | true => false
    have hbottomLeftPure : pair 0 0 ∈ example3.purePayoffSet := by
      refine ⟨bottomLeft, ?_⟩
      funext who
      cases who <;> rfl
    obtain ⟨firstProfile, hfirstPayoff⟩ :=
      lemma_1_D1_subset_Dn example3 ⟨1, by omega⟩
        (lemma_1_pure_subset_D1 example3 htopRightPure)
    obtain ⟨secondProfile, hsecondPayoff⟩ :=
      lemma_1_D1_subset_Dn example3 ⟨1, by omega⟩
        (lemma_1_pure_subset_D1 example3 hbottomLeftPure)
    let joined := example3.appendFiniteProfiles 1 firstProfile secondProfile
    refine ⟨joined, ?_⟩
    have hweighted :=
      appendFiniteProfiles_weightedPayoff example3 1 1 firstProfile secondProfile
    rw [hfirstPayoff, hsecondPayoff] at hweighted
    norm_num at hweighted
    dsimp only [joined]
    have hpairs :
        pair 1 1 + pair 0 0 =
          (2 : ℝ) • pair (1 / 2) (1 / 2) := by
      ext who
      cases who <;> norm_num [Pi.add_apply, Pi.smul_apply, pair, smul_eq_mul]
    apply smul_right_injective (Payoff Bool) (by norm_num : (2 : ℝ) ≠ 0)
    exact hweighted.trans hpairs
  · rintro ⟨profile, hpayoff⟩
    change (Bool → PMF Bool) at profile
    have hrow := congrFun hpayoff false
    have hcolumn := congrFun hpayoff true
    change (binaryGame (pair 1 0) (pair 1 1) (pair 0 0)
      (pair 1 0)).mixedPayoff profile false = pair (1 / 2) (1 / 2) false at hrow
    change (binaryGame (pair 1 0) (pair 1 1) (pair 0 0)
      (pair 1 0)).mixedPayoff profile true = pair (1 / 2) (1 / 2) true at hcolumn
    rw [binaryGame_mixedPayoff_apply] at hrow hcolumn
    norm_num [pair] at hrow hcolumn
    let p := (profile false true).toReal
    let q := (profile true true).toReal
    have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
    have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
    have hp1 : p ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    have hq1 : q ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    change p * q + (1 - p) = 1 / 2 at hrow
    change (1 - p) * q = 1 / 2 at hcolumn
    nlinarith [sq_nonneg (p - 1 / 2)]

/-- Equation (13), with the paper's positive-horizon domain explicit. -/
theorem equation_13 :
    ∃ G : FiniteStageGame, ∃ n : G.Horizon,
      G.finiteEquilibriumPayoffsOnHorizon n =
          G.finiteEquilibriumPayoffs (n.1 + 1) ∧
        G.finiteFeasiblePayoffsOnHorizon n ≠
          G.finiteFeasiblePayoffs (n.1 + 1) := by
  let n : example3.Horizon := ⟨1, by omega⟩
  refine ⟨example3, n, ?_, ?_⟩
  · change example3.finiteEquilibriumPayoffs 1 =
      example3.finiteEquilibriumPayoffs 2
    rw [example3_En 1 (by omega), example3_En 2 (by omega)]
  · intro heq
    have hpair := example3_half_mem_D2_not_D1
    apply hpair.2
    rw [← finiteFeasiblePayoffs_one_eq_oneStageFeasiblePayoffs example3]
    change pair (1 / 2) (1 / 2) ∈
      example3.finiteFeasiblePayoffsOnHorizon n
    rw [heq]
    simpa [n] using hpair.1

/-- Equation (14), at a positive finite horizon. -/
theorem equation_14 :
    ∃ G : FiniteStageGame, ∃ n : G.Horizon,
      ¬G.finiteEquilibriumPayoffsOnHorizon n ⊆
        convexHull ℝ G.oneStageEquilibriumPayoffs := by
  refine ⟨example2, ⟨2, by omega⟩, ?_⟩
  intro hinclusion
  have hone := hinclusion example2_one_one_mem_E2
  rw [example2_E1_eq_singleton] at hone
  change pair 1 1 ∈ convexHull ℝ ({pair 2 2} : Set (Payoff Bool)) at hone
  rw [convexHull_singleton] at hone
  have hequal : pair 1 1 = pair 2 2 := Set.mem_singleton_iff.mp hone
  have hfalse := congrFun hequal false
  norm_num [pair] at hfalse

/-- Example 4's critical construction gives `(m,m)` at horizon `m+1`. -/
theorem example4_critical_payoff_mem (m : ℕ) :
    pair m m ∈ (example4 m).finiteEquilibriumPayoffs (m + 1) := by
  let profile := example4CriticalProfile m
  refine ⟨profile, ?_, ?_⟩
  · intro who deviation
    simp only [add_zero]
    have hpayoff := congrFun (example4CriticalProfile_payoff m) who
    change (example4 m).repeatedGame.finiteAveragePayoff
        PUnit.unit (m + 1) profile who = pair m m who at hpayoff
    rw [hpayoff]
    have hdeviation :=
      example4CriticalProfile_deviation_bound m who deviation
    cases who <;> simpa [profile, pair] using hdeviation
  · exact example4CriticalProfile_payoff m

/-- Before the critical horizon, backward induction forces Top/Right at every
reached history and hence the constant payoff `(m+1,m+1)`. -/
private theorem example4_finitePayoff_eq_topRight_of_horizonNash
    (m : ℕ) : ∀ horizon : ℕ, ∀ profile : (example4 m).BehaviorProfile,
      0 < horizon → horizon ≤ m →
      (example4 m).repeatedGame.IsεHorizonNash
        PUnit.unit horizon 0 profile →
      (example4 m).finitePayoff horizon profile =
        pair (m + 1) (m + 1) := by
  intro horizon
  induction horizon with
  | zero =>
      intro _ hpositive
      omega
  | succ tail ih =>
      intro profile _hpositive hle hnash
      letI (player : Bool) : Fintype ((example4 m).kernel.Strategy player) := by
        change Fintype Bool
        infer_instance
      letI : Finite (example4 m).kernel.Outcome := by
        change Finite (Bool → Bool)
        exact Finite.of_fintype _
      letI (player : Bool) : Finite
          ((example4 m).repeatedGame.Act player) :=
        @Finite.of_fintype _ ((example4 m).finiteAction player)
      letI : Finite (example4 m).repeatedGame.State :=
        inferInstanceAs (Finite PUnit)
      have hcurrent : (example4 m).initialMixedProfile profile =
          fun player : Bool => PMF.pure player := by
        funext player
        exact example4_initialMixedProfile_eq_pure_of_horizonNash
          m (tail + 1) (by omega) hle profile hnash player
      have hstageZero (who : Bool) :
          (example4 m).repeatedGame.expectedStagePayoff
              profile PUnit.unit 0 who = (m : ℝ) + 1 := by
        rw [(example4 m).repeatedGame.expectedStagePayoff_zero,
          (example4 m).stageEUAt_eq_mixedEU]
        change (example4 m).kernel.mixedExtension.eu
          ((example4 m).initialMixedProfile profile) who = (m : ℝ) + 1
        rw [hcurrent]
        change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
          (binaryPayoff (pair m 0) (pair (m + 1) (m + 1))
            (pair 0 0) (pair 0 m))).mixedExtension.eu
              (fun player : Bool => PMF.pure player) who = (m : ℝ) + 1
        rw [binaryKernel_mixedEU_apply]
        cases who <;> simp [PMF.pure_apply, pair]
      by_cases htailZero : tail = 0
      · subst tail
        have hweighted := cast_smul_finitePayoff_eq_sum
          (example4 m) 1 profile
        funext who
        have hcoordinate := congrFun hweighted who
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
          Finset.sum_range_one] at hcoordinate
        rw [hstageZero] at hcoordinate
        cases who <;> simpa [pair] using hcoordinate
      · have htailPositive : 0 < tail := Nat.pos_of_ne_zero htailZero
        have htailLe : tail ≤ m := by omega
        have hnash' : (example4 m).repeatedGame.IsεHorizonNash
            PUnit.unit (1 + tail) 0 profile := by
          simpa [Nat.add_comm] using hnash
        have htailPayoff (base : (example4 m).repeatedGame.Hist 1)
            (hbase : base ∈ ((example4 m).repeatedGame.histDist
              profile PUnit.unit 1).support) :
            (example4 m).finitePayoff tail
                ((example4 m).repeatedGame.afterHistoryProfile profile base) =
              pair (m + 1) (m + 1) := by
          apply ih
          · exact htailPositive
          · exact htailLe
          · cases base.2
            exact (example4 m).kernel
              |>.realizedAction_afterHistoryProfile_isHorizonNash_of_mem_support
                profile hnash' base hbase
        have htailTotal (who : Bool) :
            (∑ time ∈ Finset.range tail,
                (example4 m).repeatedGame.expectedStagePayoff
                  profile PUnit.unit (1 + time) who) =
              (tail : ℝ) * ((m : ℝ) + 1) := by
          change (∑ time ∈ Finset.range tail,
              (example4 m).repeatedGame.expectedStagePayoff
                profile (example4 m).repeatedInitial (1 + time) who) = _
          calc
            (∑ time ∈ Finset.range tail,
                (example4 m).repeatedGame.expectedStagePayoff
                  profile (example4 m).repeatedInitial (1 + time) who) =
                ∑ time ∈ Finset.range tail,
                  Math.Probability.expect
                    ((example4 m).repeatedGame.histDist
                      profile (example4 m).repeatedInitial 1)
                    (fun base =>
                      (example4 m).repeatedGame.expectedStagePayoff
                        ((example4 m).repeatedGame.afterHistoryProfile
                          profile base) base.2 time who) := by
              apply Finset.sum_congr rfl
              intro time _
              exact expectedStagePayoff_add_eq_expect_afterHistory
                (example4 m) profile 1 time who
            _ =
            Math.Probability.expect
                ((example4 m).repeatedGame.histDist
                  profile (example4 m).repeatedInitial 1)
                (fun base => ∑ time ∈ Finset.range tail,
                  (example4 m).repeatedGame.expectedStagePayoff
                    ((example4 m).repeatedGame.afterHistoryProfile profile base)
                    base.2 time who) :=
              sum_expect_comm_range _ _ _
            _ =
                Math.Probability.expect
                  ((example4 m).repeatedGame.histDist
                    profile (example4 m).repeatedInitial 1)
                  (fun _ => (tail : ℝ) * ((m : ℝ) + 1)) := by
              apply Math.ProbabilityMassFunction.expect_congr_on_support
              intro base hbase
              cases base.2
              have hweighted := congrFun
                (cast_smul_finitePayoff_eq_sum (example4 m) tail
                  ((example4 m).repeatedGame.afterHistoryProfile profile base)) who
              simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hweighted
              rw [← hweighted, htailPayoff base hbase]
              cases who <;> simp [pair]
            _ = (tail : ℝ) * ((m : ℝ) + 1) :=
              Math.Probability.expect_const _ _
        have hweighted := cast_smul_finitePayoff_eq_sum
          (example4 m) (tail + 1) profile
        funext who
        have hcoordinate := congrFun hweighted who
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hcoordinate
        rw [Finset.sum_range_succ', hstageZero] at hcoordinate
        have htailCoordinate :
            (∑ time ∈ Finset.range tail,
                (example4 m).repeatedGame.expectedStagePayoff
                  profile PUnit.unit (time + 1) who) =
              (tail : ℝ) * ((m : ℝ) + 1) := by
          simpa [Nat.add_comm] using htailTotal who
        rw [htailCoordinate] at hcoordinate
        cases who <;> simp only [pair_false, pair_true]
        all_goals
          norm_num [Nat.cast_add] at hcoordinate ⊢
          nlinarith

/-- Example 4 and Equation (15). -/
theorem example4_equilibrium_pattern (m : ℕ) (_hm : 0 < m) :
    (∀ n, 0 < n → n ≤ m →
      (example4 m).finiteEquilibriumPayoffs n =
        {pair (m + 1) (m + 1)}) ∧
      pair m m ∈ (example4 m).finiteEquilibriumPayoffs (m + 1) := by
  constructor
  · intro n hn hnm
    apply Set.Subset.antisymm
    · rintro payoff ⟨profile, hnash, rfl⟩
      rw [example4_finitePayoff_eq_topRight_of_horizonNash
        m n profile hn hnm hnash]
      exact Set.mem_singleton _
    · rintro payoff hpayoff
      rw [Set.mem_singleton_iff] at hpayoff
      subst payoff
      let mixed : (example4 m).MixedProfile :=
        fun player => PMF.pure player
      have honeStage : pair (m + 1) (m + 1) ∈
          (example4 m).oneStageEquilibriumPayoffs := by
        refine ⟨mixed, ?_, ?_⟩
        · intro who deviation
          change PMF Bool at deviation
          change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
            (binaryPayoff (pair m 0) (pair (m + 1) (m + 1))
              (pair 0 0) (pair 0 m))).mixedExtension.eu mixed who ≥
            (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
              (binaryPayoff (pair m 0) (pair (m + 1) (m + 1))
                (pair 0 0) (pair 0 m))).mixedExtension.eu
                  (Function.update mixed who deviation) who
          rw [binaryKernel_mixedEU_apply, binaryKernel_mixedEU_apply]
          cases who <;> simp [mixed, PMF.pure_apply, pair] <;>
            have hprob0 : 0 ≤ (deviation true).toReal := ENNReal.toReal_nonneg <;>
            have hprob : (deviation true).toReal ≤ 1 :=
              ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _) <;>
            nlinarith
        · funext who
          change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
            (binaryPayoff (pair m 0) (pair (m + 1) (m + 1))
              (pair 0 0) (pair 0 m))).mixedExtension.eu mixed who = _
          rw [binaryKernel_mixedEU_apply]
          cases who <;> simp [mixed, PMF.pure_apply, pair]
      exact lemma_1_E1_subset_En (example4 m) ⟨n, hn⟩ honeStage
  · exact example4_critical_payoff_mem m

/-- Equation (15): one decreasing step at a positive horizon does not
force the next one. -/
theorem equation_15 :
    ∃ G : FiniteStageGame, ∃ n : G.Horizon,
      G.finiteEquilibriumPayoffs (n.1 + 1) ⊆
          G.finiteEquilibriumPayoffsOnHorizon n ∧
        ¬G.finiteEquilibriumPayoffs (n.1 + 2) ⊆
          G.finiteEquilibriumPayoffsOnHorizon n := by
  let n : (example4 2).Horizon := ⟨1, by omega⟩
  have hpattern := example4_equilibrium_pattern 2 (by omega)
  refine ⟨example4 2, n, ?_, ?_⟩
  · change (example4 2).finiteEquilibriumPayoffs 2 ⊆
      (example4 2).finiteEquilibriumPayoffs 1
    rw [hpattern.1 2 (by omega) (by omega),
      hpattern.1 1 (by omega) (by omega)]
  · intro hinclusion
    have hmem := hinclusion hpattern.2
    change pair (2 : ℝ) 2 ∈
      (example4 2).finiteEquilibriumPayoffs 1 at hmem
    rw [hpattern.1 1 (by omega) (by omega)] at hmem
    have hequal := Set.mem_singleton_iff.mp hmem
    have hfalse := congrFun hequal false
    norm_num [pair] at hfalse

/-! **Example 1 revisited, page 150.**  The paper's `λ` is
the current-stage weight: playing `(1,0)` once and `(0,1)` forever
afterwards gives `(λ,1-λ)`.  Thus the displayed payoff belongs to
`E_{7/8}`, not `E_{1/8}`. -/

/-- Play one of Example 1's two diagonal stage equilibria according to a
deterministic time schedule. -/
noncomputable def example1DiagonalScheduleProfile
    (schedule : ℕ → Bool) : example1.BehaviorProfile :=
  fun _ time _ ↦ PMF.pure (schedule time)

/-- A diagonal schedule earns the corresponding pure diagonal payoff at
every stage. -/
theorem example1_expectedStagePayoff_diagonalSchedule
    (schedule : ℕ → Bool) (time : ℕ) (who : Bool) :
    example1.repeatedGame.expectedStagePayoff
        (example1DiagonalScheduleProfile schedule) PUnit.unit time who =
      if schedule time then pair 0 1 who else pair 1 0 who := by
  letI (player : Bool) : Finite (example1.repeatedGame.Act player) :=
    @Finite.of_fintype _ (example1.finiteAction player)
  letI : Finite example1.repeatedGame.State := inferInstanceAs (Finite PUnit)
  unfold StochasticGame.expectedStagePayoff
  rw [← Math.Probability.expect_const
    (example1.repeatedGame.histDist
      (example1DiagonalScheduleProfile schedule) PUnit.unit time)
    (if schedule time then pair 0 1 who else pair 1 0 who)]
  congr 1
  funext history
  rw [example1_stageEUAt_eq_mixedPayoff,
    show (fun player ↦ example1DiagonalScheduleProfile schedule
      player time history) =
        example1.kernel.pureMixedProfile (fun _ ↦ schedule time) by rfl]
  change example1.kernel.mixedExtension.payoffVector
      (example1.kernel.pureMixedProfile (fun _ ↦ schedule time)) who = _
  rw [example1.kernel.mixedExtension_payoffVector_pureMixedProfile]
  cases hs : schedule time <;> cases who <;>
    norm_num [FiniteStageGame.kernel, KernelGame.eu_ofPureEU,
      binaryPayoff, hs, pair]

/-- Every diagonal schedule is discounted Nash: at every history its current
pure diagonal action is a one-stage Nash equilibrium. -/
theorem example1_diagonalSchedule_isDiscountedNash
    (schedule : ℕ → Bool) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    example1.repeatedGame.IsDiscountedεNash beta PUnit.unit 0
      (example1DiagonalScheduleProfile schedule) := by
  intro who deviation
  simp only [add_zero]
  have hbound : ∀ state action,
      |example1.repeatedGame.stagePayoff state action who| ≤ 1 := by
    intro state action
    cases who <;> cases hrow : action false <;>
      cases hcolumn : action true <;>
      norm_num [FiniteStageGame.repeatedGame,
        KernelGame.realizedActionStochasticGame,
        FiniteStageGame.kernel, KernelGame.eu_ofPureEU,
        binaryPayoff, hrow, hcolumn, pair]
  have hstage : ∀ time,
      example1.repeatedGame.expectedStagePayoff
          (Function.update (example1DiagonalScheduleProfile schedule)
            who deviation) PUnit.unit time who ≤
        example1.repeatedGame.expectedStagePayoff
          (example1DiagonalScheduleProfile schedule)
            PUnit.unit time who := by
    intro time
    letI (player : Bool) : Finite (example1.repeatedGame.Act player) :=
      @Finite.of_fintype _ (example1.finiteAction player)
    letI : Finite example1.repeatedGame.State := inferInstanceAs (Finite PUnit)
    rw [example1_expectedStagePayoff_diagonalSchedule]
    unfold StochasticGame.expectedStagePayoff
    rw [← Math.Probability.expect_const
      (example1.repeatedGame.histDist
        (Function.update (example1DiagonalScheduleProfile schedule)
          who deviation) PUnit.unit time)
      (if schedule time then pair 0 1 who else pair 1 0 who)]
    apply Math.Probability.expect_mono
    intro history
    rw [example1_stageEUAt_eq_mixedPayoff,
      binaryGame_mixedPayoff_apply]
    cases who
    · have hother :
          (Function.update (example1DiagonalScheduleProfile schedule)
            false deviation) true time history =
            PMF.pure (schedule time) := by
        simp [example1DiagonalScheduleProfile]
        rfl
      rw [hother]
      have hprob0 : 0 ≤ (deviation time history true).toReal :=
        ENNReal.toReal_nonneg
      have hprob1 : (deviation time history true).toReal ≤ 1 :=
        ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
      cases hs : schedule time
      · norm_num [Function.update_self, hs, pair, PMF.pure_apply]
      · norm_num [Function.update_self, hs, pair, PMF.pure_apply]
    · have hother :
          (Function.update (example1DiagonalScheduleProfile schedule)
            true deviation) false time history =
            PMF.pure (schedule time) := by
        simp [example1DiagonalScheduleProfile]
        rfl
      rw [hother]
      have hprob0 : 0 ≤ (deviation time history true).toReal :=
        ENNReal.toReal_nonneg
      have hprob1 : (deviation time history true).toReal ≤ 1 :=
        ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
      cases hs : schedule time
      · norm_num [Function.update_self, hs, pair, PMF.pure_apply]
      · norm_num [Function.update_self, hs, pair, PMF.pure_apply]
        convert hprob1 using 1
        rfl
  have hbetaAbs : |beta| < 1 := by rwa [abs_of_nonneg hbeta0]
  have hdeviationSummable :=
    example1.repeatedGame.summable_discounted_expectedStagePayoff
      hbound
      (Function.update (example1DiagonalScheduleProfile schedule)
        who deviation) PUnit.unit hbetaAbs
  have hprofileSummable :=
    example1.repeatedGame.summable_discounted_expectedStagePayoff
      hbound (example1DiagonalScheduleProfile schedule)
        PUnit.unit hbetaAbs
  unfold StochasticGame.discountedPayoff
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  exact hdeviationSummable.tsum_le_tsum
    (fun time ↦ mul_le_mul_of_nonneg_left
      (hstage time) (pow_nonneg hbeta0 time))
    hprofileSummable

/-- Every correlated-feasible payoff of Example 1 is nonnegative,
coordinatewise at most one, and has total payoff at most one. -/
theorem example1_correlated_bounds {v : Payoff Bool}
    (hv : v ∈ example1.correlatedFeasiblePayoffs) :
    0 ≤ v false ∧ v false ≤ 1 ∧
      0 ≤ v true ∧ v true ≤ 1 ∧
        v false + v true ≤ 1 := by
  apply (convexHull_min (t := {w : Payoff Bool |
      0 ≤ w false ∧ w false ≤ 1 ∧
        0 ≤ w true ∧ w true ≤ 1 ∧
          w false + w true ≤ 1}) ?_ ?_) hv
  · rintro _ ⟨action, rfl⟩
    change (Bool → Bool) at action
    cases hrow : action false <;> cases hcolumn : action true <;>
      norm_num [binaryPayoff, hrow, hcolumn, pair]
  · intro x hx y hy a b ha hb hab
    rcases hx with ⟨hx0, hx1, hx2, hx3, hx4⟩
    rcases hy with ⟨hy0, hy1, hy2, hy3, hy4⟩
    change 0 ≤ a * x false + b * y false ∧
      a * x false + b * y false ≤ 1 ∧
      0 ≤ a * x true + b * y true ∧
      a * x true + b * y true ≤ 1 ∧
      (a * x false + b * y false) +
        (a * x true + b * y true) ≤ 1
    constructor
    · positivity
    constructor
    · nlinarith
    constructor
    · positivity
    constructor <;> nlinarith

/-- Every player's normalized discounted payoff in Example 1 lies in
`[0,1]`. -/
theorem example1_discountedPayoff_mem_Icc
    (profile : example1.BehaviorProfile) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (who : Bool) :
    example1.repeatedGame.discountedPayoff beta profile PUnit.unit who ∈
      Set.Icc 0 1 := by
  have hbound : ∀ state action,
      |example1.repeatedGame.stagePayoff state action who| ≤ 1 := by
    intro state action
    cases who <;> cases hrow : action false <;>
      cases hcolumn : action true <;>
      norm_num [FiniteStageGame.repeatedGame,
        KernelGame.realizedActionStochasticGame,
        FiniteStageGame.kernel, KernelGame.eu_ofPureEU,
        binaryPayoff, hrow, hcolumn, pair]
  have hstage (time : ℕ) :=
    example1_correlated_bounds
      (expectedStagePayoff_mem_correlatedFeasiblePayoffs
        example1 profile time)
  constructor
  · apply example1.repeatedGame.discountedPayoff_ge_of_forall_expectedStagePayoff_ge
      hbound (fun time ↦ ?_) hbeta0 hbeta1
    cases who
    · exact (hstage time).1
    · exact (hstage time).2.2.1
  · apply example1.repeatedGame.discountedPayoff_le_of_forall_expectedStagePayoff_le
      hbound (fun time ↦ ?_) hbeta0 hbeta1
    cases who
    · exact (hstage time).2.1
    · exact (hstage time).2.2.2.1

/-- Example 1's normalized discounted aggregate payoff is at most one. -/
theorem example1_discountedTotal_le_one
    (profile : example1.BehaviorProfile) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    example1.repeatedGame.discountedPayoff beta profile PUnit.unit false +
      example1.repeatedGame.discountedPayoff beta profile PUnit.unit true ≤ 1 := by
  letI (player : Bool) : Finite (example1.repeatedGame.Act player) :=
    @Finite.of_fintype _ (example1.finiteAction player)
  letI : Finite example1.repeatedGame.State := inferInstanceAs (Finite PUnit)
  have hbound (who : Bool) : ∀ state action,
      |example1.repeatedGame.stagePayoff state action who| ≤ 1 := by
    intro state action
    cases who <;> cases hrow : action false <;>
      cases hcolumn : action true <;>
      norm_num [FiniteStageGame.repeatedGame,
        KernelGame.realizedActionStochasticGame,
        FiniteStageGame.kernel, KernelGame.eu_ofPureEU,
        binaryPayoff, hrow, hcolumn, pair]
  have hbetaAbs : |beta| < 1 := by rwa [abs_of_nonneg hbeta0]
  have hrowSummable :=
    example1.repeatedGame.summable_discounted_expectedStagePayoff
      (hbound false) profile PUnit.unit hbetaAbs
  have hcolumnSummable :=
    example1.repeatedGame.summable_discounted_expectedStagePayoff
      (hbound true) profile PUnit.unit hbetaAbs
  have hgeom : Summable (fun time : ℕ ↦ beta ^ time) :=
    summable_geometric_of_lt_one hbeta0 hbeta1
  unfold StochasticGame.discountedPayoff
  rw [← mul_add, ← hrowSummable.tsum_add hcolumnSummable]
  calc
    (1 - beta) *
        (∑' time : ℕ,
          (beta ^ time *
            example1.repeatedGame.expectedStagePayoff profile
              PUnit.unit time false +
          beta ^ time *
            example1.repeatedGame.expectedStagePayoff profile
              PUnit.unit time true)) ≤
      (1 - beta) * (∑' time : ℕ, beta ^ time) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        apply (hrowSummable.add hcolumnSummable).tsum_le_tsum _ hgeom
        intro time
        rw [← mul_add]
        exact mul_le_of_le_one_right (pow_nonneg hbeta0 time)
          (example1_expectedStageTotal_le_one profile time)
    _ = 1 := by
      rw [tsum_geometric_of_lt_one hbeta0 hbeta1]
      exact div_self (by linarith)

theorem example1_discounted_nonmonotone :
    pair (7 / 8) (1 / 8) ∈
        example1.discountedEquilibriumPayoffs (7 / 8) ∧
      pair (7 / 8) (1 / 8) ∉ example1.oneStageFeasiblePayoffs ∧
      pair (7 / 8) (1 / 8) ∉
        example1.discountedFeasiblePayoffs (3 / 4) := by
  let schedule : ℕ → Bool
    | 0 => false
    | _ + 1 => true
  let profile := example1DiagonalScheduleProfile schedule
  constructor
  · refine ⟨profile, ?_, ?_⟩
    · dsimp only [profile]
      have hnash := example1_diagonalSchedule_isDiscountedNash
        schedule (1 / 8) (by norm_num) (by norm_num)
      norm_num at hnash ⊢
      exact hnash
    · funext who
      change example1.repeatedGame.discountedPayoff (1 - 7 / 8)
        (example1DiagonalScheduleProfile schedule) PUnit.unit who = _
      unfold StochasticGame.discountedPayoff
      rw [show (∑' time : ℕ, (1 - 7 / 8) ^ time *
            example1.repeatedGame.expectedStagePayoff
              (example1DiagonalScheduleProfile schedule)
                PUnit.unit time who) =
          ∑' time : ℕ, (1 - 7 / 8) ^ time *
            (if schedule time then pair 0 1 who else pair 1 0 who) by
        apply tsum_congr
        intro time
        rw [example1_expectedStagePayoff_diagonalSchedule]]
      cases who
      · change (1 - (1 - 7 / 8)) *
          (∑' time : ℕ, (1 - 7 / 8) ^ time *
            (if schedule time then 0 else 1)) = 7 / 8
        have hsum : Summable (fun time : ℕ ↦
            (1 / 8 : ℝ) ^ time *
              (if schedule time then 0 else 1)) := by
          have hgeom : Summable (fun time : ℕ ↦ (1 / 8 : ℝ) ^ time) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          apply Summable.of_norm_bounded hgeom
          intro time
          rw [Real.norm_eq_abs, abs_of_nonneg
            (mul_nonneg (pow_nonneg (by norm_num) time) (by positivity))]
          apply mul_le_of_le_one_right (pow_nonneg (by norm_num) time)
          split <;> norm_num
        rw [show (1 - 7 / 8 : ℝ) = 1 / 8 by norm_num]
        rw [hsum.tsum_eq_zero_add]
        simp [schedule]
        norm_num
      · change (1 - (1 - 7 / 8)) *
          (∑' time : ℕ, (1 - 7 / 8) ^ time *
            (if schedule time then 1 else 0)) = 1 / 8
        have hsum : Summable (fun time : ℕ ↦
            (1 / 8 : ℝ) ^ time *
              (if schedule time then 1 else 0)) := by
          have hgeom : Summable (fun time : ℕ ↦ (1 / 8 : ℝ) ^ time) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          apply Summable.of_norm_bounded hgeom
          intro time
          rw [Real.norm_eq_abs, abs_of_nonneg
            (mul_nonneg (pow_nonneg (by norm_num) time) (by positivity))]
          apply mul_le_of_le_one_right (pow_nonneg (by norm_num) time)
          split <;> norm_num
        rw [show (1 - 7 / 8 : ℝ) = 1 / 8 by norm_num]
        rw [hsum.tsum_eq_zero_add]
        simp only [schedule, if_true, mul_one, pow_succ']
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
  · constructor
    · rintro ⟨mixed, hmixed⟩
      have htotal :
          example1.mixedPayoff mixed false +
            example1.mixedPayoff mixed true = 1 := by
        rw [congrFun hmixed false, congrFun hmixed true]
        norm_num [pair]
      obtain ⟨diagonal, hfalse, htrue⟩ :=
        example1_mixedProfile_pure_diagonal_of_total_eq_one mixed htotal
      have hrow := congrFun hmixed false
      rw [binaryGame_mixedPayoff_apply, hfalse, htrue] at hrow
      cases diagonal <;> norm_num [pair, PMF.pure_apply] at hrow
    · rintro ⟨candidate, hcandidate⟩
      letI (player : Bool) : Finite (example1.repeatedGame.Act player) :=
        @Finite.of_fintype _ (example1.finiteAction player)
      letI : Finite example1.repeatedGame.State := inferInstanceAs (Finite PUnit)
      have hrow := congrFun hcandidate false
      have hcolumn := congrFun hcandidate true
      change example1.repeatedGame.discountedPayoff (1 - 3 / 4)
        candidate PUnit.unit false = pair (7 / 8) (1 / 8) false at hrow
      change example1.repeatedGame.discountedPayoff (1 - 3 / 4)
        candidate PUnit.unit true = pair (7 / 8) (1 / 8) true at hcolumn
      norm_num [pair] at hrow hcolumn
      have hbound (who : Bool) : ∀ state action,
          |example1.repeatedGame.stagePayoff state action who| ≤ 1 := by
        intro state action
        cases who <;> cases hrowAction : action false <;>
          cases hcolumnAction : action true <;>
          norm_num [FiniteStageGame.repeatedGame,
            KernelGame.realizedActionStochasticGame,
            FiniteStageGame.kernel, KernelGame.eu_ofPureEU,
            binaryPayoff, hrowAction, hcolumnAction, pair]
      have htransition (action : example1.repeatedGame.JointAct) :
          example1.repeatedGame.transition PUnit.unit action =
            PMF.pure PUnit.unit := rfl
      have hexpectTransition (action : example1.repeatedGame.JointAct)
          (f : example1.repeatedGame.State → ℝ) :
          Math.Probability.expect
              (example1.repeatedGame.transition PUnit.unit action) f =
            f PUnit.unit := by
        rw [htransition]
        exact Math.Probability.expect_pure f PUnit.unit
      have hshiftRow := example1.repeatedGame.discountedPayoff_shift
        (hbound false) candidate PUnit.unit (β := 1 / 4)
          (by norm_num) (by norm_num)
      have hshiftColumn := example1.repeatedGame.discountedPayoff_shift
        (hbound true) candidate PUnit.unit (β := 1 / 4)
          (by norm_num) (by norm_num)
      let empty := example1.repeatedGame.emptyHist PUnit.unit
      let actionLaw := example1.repeatedGame.stageActionDist candidate empty
      let continuation (who : Bool) :=
        Math.Probability.expect actionLaw fun action ↦
          example1.repeatedGame.discountedPayoff (1 / 4)
            (example1.repeatedGame.shiftProfile
              candidate (PUnit.unit, action)) PUnit.unit who
      have hcontinuation : continuation false + continuation true ≤ 1 := by
        dsimp only [continuation]
        calc
          Math.Probability.expect actionLaw (fun action ↦
                example1.repeatedGame.discountedPayoff (1 / 4)
                  (example1.repeatedGame.shiftProfile
                    candidate (PUnit.unit, action)) PUnit.unit false) +
              Math.Probability.expect actionLaw (fun action ↦
                example1.repeatedGame.discountedPayoff (1 / 4)
                  (example1.repeatedGame.shiftProfile
                    candidate (PUnit.unit, action)) PUnit.unit true) =
            Math.Probability.expect actionLaw (fun action ↦
              example1.repeatedGame.discountedPayoff (1 / 4)
                  (example1.repeatedGame.shiftProfile
                    candidate (PUnit.unit, action)) PUnit.unit false +
                example1.repeatedGame.discountedPayoff (1 / 4)
                  (example1.repeatedGame.shiftProfile
                    candidate (PUnit.unit, action)) PUnit.unit true) := by
              rw [Math.Probability.expect_add]
          _ ≤ Math.Probability.expect actionLaw (fun _ ↦ (1 : ℝ)) := by
              apply Math.Probability.expect_mono
              intro action
              exact example1_discountedTotal_le_one
                (example1.repeatedGame.shiftProfile
                  candidate (PUnit.unit, action)) (1 / 4)
                    (by norm_num) (by norm_num)
          _ = 1 := Math.Probability.expect_const actionLaw 1
      have hstageTotal :
          example1.repeatedGame.stageEUAt candidate empty false +
            example1.repeatedGame.stageEUAt candidate empty true = 1 := by
        have hstageLe := example1_expectedStageTotal_le_one candidate 0
        rw [example1.repeatedGame.expectedStagePayoff_zero,
          example1.repeatedGame.expectedStagePayoff_zero] at hstageLe
        change example1.repeatedGame.stageEUAt candidate empty false +
          example1.repeatedGame.stageEUAt candidate empty true ≤ 1 at hstageLe
        simp_rw [hexpectTransition] at hshiftRow hshiftColumn
        norm_num at hshiftRow hshiftColumn
        have hcontinuationRaw := hcontinuation
        dsimp only [continuation, actionLaw, empty] at hcontinuationRaw
        dsimp only [empty] at hstageLe ⊢
        rw [hrow] at hshiftRow
        rw [hcolumn] at hshiftColumn
        nlinarith [hcontinuationRaw]
      let current : Bool → PMF Bool :=
        fun player ↦ candidate player 0 empty
      have hcurrentTotal :
          example1.mixedPayoff current false +
            example1.mixedPayoff current true = 1 := by
        rw [← example1_stageEUAt_eq_mixedPayoff candidate empty false,
          ← example1_stageEUAt_eq_mixedPayoff candidate empty true]
        exact hstageTotal
      obtain ⟨diagonal0, hcurrentFalse, hcurrentTrue⟩ :=
        example1_mixedProfile_pure_diagonal_of_total_eq_one
          current hcurrentTotal
      let action0 : example1.repeatedGame.JointAct := fun _ ↦ diagonal0
      have haction0 : actionLaw = PMF.pure action0 := by
        unfold actionLaw StochasticGame.stageActionDist
        have hcurrent : (fun player ↦ candidate player 0 empty) =
            fun player ↦ PMF.pure (action0 player) := by
          funext player
          cases player
          · exact hcurrentFalse
          · exact hcurrentTrue
        change Math.PMFProduct.pmfPi
          (fun player : Bool ↦ candidate player 0 empty) = PMF.pure action0
        rw [hcurrent]
        exact Math.PMFProduct.pmfPi_pure action0
      let candidate1 := example1.repeatedGame.shiftProfile
        candidate (PUnit.unit, action0)
      have hshiftRow' :
          7 / 8 = 3 / 4 *
              example1.repeatedGame.stageEUAt candidate empty false +
            1 / 4 * example1.repeatedGame.discountedPayoff
              (1 / 4) candidate1 PUnit.unit false := by
        rw [hrow] at hshiftRow
        norm_num at hshiftRow
        rw [show example1.repeatedGame.stageActionDist candidate
            (example1.repeatedGame.emptyHist PUnit.unit) = PMF.pure action0 by
          simpa [actionLaw, empty] using haction0] at hshiftRow
        simpa [candidate1, FiniteStageGame.repeatedGame,
          KernelGame.realizedActionStochasticGame, empty] using hshiftRow
      have hshiftColumn' :
          1 / 8 = 3 / 4 *
              example1.repeatedGame.stageEUAt candidate empty true +
            1 / 4 * example1.repeatedGame.discountedPayoff
              (1 / 4) candidate1 PUnit.unit true := by
        rw [hcolumn] at hshiftColumn
        norm_num at hshiftColumn
        rw [show example1.repeatedGame.stageActionDist candidate
            (example1.repeatedGame.emptyHist PUnit.unit) = PMF.pure action0 by
          simpa [actionLaw, empty] using haction0] at hshiftColumn
        simpa [candidate1, FiniteStageGame.repeatedGame,
          KernelGame.realizedActionStochasticGame, empty] using hshiftColumn
      have hcandidate1Total :
          example1.repeatedGame.discountedPayoff
              (1 / 4) candidate1 PUnit.unit false +
            example1.repeatedGame.discountedPayoff
              (1 / 4) candidate1 PUnit.unit true = 1 := by
        nlinarith [hstageTotal]
      let empty1 := example1.repeatedGame.emptyHist PUnit.unit
      have hstage1Le := example1_expectedStageTotal_le_one candidate1 0
      rw [example1.repeatedGame.expectedStagePayoff_zero,
        example1.repeatedGame.expectedStagePayoff_zero] at hstage1Le
      let actionLaw1 := example1.repeatedGame.stageActionDist candidate1 empty1
      let continuation1 (who : Bool) :=
        Math.Probability.expect actionLaw1 fun action ↦
          example1.repeatedGame.discountedPayoff (1 / 4)
            (example1.repeatedGame.shiftProfile
              candidate1 (PUnit.unit, action)) PUnit.unit who
      have hcontinuation1 : continuation1 false + continuation1 true ≤ 1 := by
        dsimp only [continuation1]
        calc
          Math.Probability.expect actionLaw1 (fun action ↦
                example1.repeatedGame.discountedPayoff (1 / 4)
                  (example1.repeatedGame.shiftProfile
                    candidate1 (PUnit.unit, action)) PUnit.unit false) +
              Math.Probability.expect actionLaw1 (fun action ↦
                example1.repeatedGame.discountedPayoff (1 / 4)
                  (example1.repeatedGame.shiftProfile
                    candidate1 (PUnit.unit, action)) PUnit.unit true) =
            Math.Probability.expect actionLaw1 (fun action ↦
              example1.repeatedGame.discountedPayoff (1 / 4)
                  (example1.repeatedGame.shiftProfile
                    candidate1 (PUnit.unit, action)) PUnit.unit false +
                example1.repeatedGame.discountedPayoff (1 / 4)
                  (example1.repeatedGame.shiftProfile
                    candidate1 (PUnit.unit, action)) PUnit.unit true) := by
              rw [Math.Probability.expect_add]
          _ ≤ Math.Probability.expect actionLaw1 (fun _ ↦ (1 : ℝ)) := by
              apply Math.Probability.expect_mono
              intro action
              exact example1_discountedTotal_le_one
                (example1.repeatedGame.shiftProfile
                  candidate1 (PUnit.unit, action)) (1 / 4)
                    (by norm_num) (by norm_num)
          _ = 1 := Math.Probability.expect_const actionLaw1 1
      have hshift1Row := example1.repeatedGame.discountedPayoff_shift
        (hbound false) candidate1 PUnit.unit (β := 1 / 4)
          (by norm_num) (by norm_num)
      have hshift1Column := example1.repeatedGame.discountedPayoff_shift
        (hbound true) candidate1 PUnit.unit (β := 1 / 4)
          (by norm_num) (by norm_num)
      have hstage1Total :
          example1.repeatedGame.stageEUAt candidate1 empty1 false +
            example1.repeatedGame.stageEUAt candidate1 empty1 true = 1 := by
        change example1.repeatedGame.stageEUAt candidate1 empty1 false +
          example1.repeatedGame.stageEUAt candidate1 empty1 true ≤ 1 at hstage1Le
        simp_rw [hexpectTransition] at hshift1Row hshift1Column
        norm_num at hshift1Row hshift1Column
        have hcontinuation1Raw := hcontinuation1
        dsimp only [continuation1, actionLaw1, empty1] at hcontinuation1Raw
        dsimp only [empty1] at hstage1Le ⊢
        nlinarith [hcandidate1Total, hcontinuation1Raw]
      let current1 : Bool → PMF Bool :=
        fun player ↦ candidate1 player 0 empty1
      have hcurrent1Total :
          example1.mixedPayoff current1 false +
            example1.mixedPayoff current1 true = 1 := by
        rw [← example1_stageEUAt_eq_mixedPayoff candidate1 empty1 false,
          ← example1_stageEUAt_eq_mixedPayoff candidate1 empty1 true]
        exact hstage1Total
      obtain ⟨diagonal1, hcurrent1False, hcurrent1True⟩ :=
        example1_mixedProfile_pure_diagonal_of_total_eq_one
          current1 hcurrent1Total
      let action1 : example1.repeatedGame.JointAct := fun _ ↦ diagonal1
      have haction1 : actionLaw1 = PMF.pure action1 := by
        unfold actionLaw1 StochasticGame.stageActionDist
        have hcurrent : (fun player ↦ candidate1 player 0 empty1) =
            fun player ↦ PMF.pure (action1 player) := by
          funext player
          cases player
          · exact hcurrent1False
          · exact hcurrent1True
        change Math.PMFProduct.pmfPi
          (fun player : Bool ↦ candidate1 player 0 empty1) = PMF.pure action1
        rw [hcurrent]
        exact Math.PMFProduct.pmfPi_pure action1
      let candidate2 := example1.repeatedGame.shiftProfile
        candidate1 (PUnit.unit, action1)
      have hshift1Row' :
          example1.repeatedGame.discountedPayoff
              (1 / 4) candidate1 PUnit.unit false =
            3 / 4 * example1.repeatedGame.stageEUAt
              candidate1 empty1 false +
            1 / 4 * example1.repeatedGame.discountedPayoff
              (1 / 4) candidate2 PUnit.unit false := by
        norm_num at hshift1Row
        rw [show example1.repeatedGame.stageActionDist candidate1
            (example1.repeatedGame.emptyHist PUnit.unit) = PMF.pure action1 by
          simpa [actionLaw1, empty1] using haction1] at hshift1Row
        simpa [candidate2, FiniteStageGame.repeatedGame,
          KernelGame.realizedActionStochasticGame, empty1] using hshift1Row
      have htailBounds := example1_discountedPayoff_mem_Icc
        candidate2 (1 / 4) (by norm_num) (by norm_num) false
      have hstageRow :
          example1.repeatedGame.stageEUAt candidate empty false =
            if diagonal0 then 0 else 1 := by
        rw [example1_stageEUAt_eq_mixedPayoff]
        change example1.mixedPayoff current false = _
        rw [binaryGame_mixedPayoff_apply, hcurrentFalse, hcurrentTrue]
        cases diagonal0 <;> norm_num [pair, PMF.pure_apply]
      have hstage1Row :
          example1.repeatedGame.stageEUAt candidate1 empty1 false =
            if diagonal1 then 0 else 1 := by
        rw [example1_stageEUAt_eq_mixedPayoff]
        change example1.mixedPayoff current1 false = _
        rw [binaryGame_mixedPayoff_apply, hcurrent1False, hcurrent1True]
        cases diagonal1 <;> norm_num [pair, PMF.pure_apply]
      rw [hstageRow] at hshiftRow'
      rw [hstage1Row] at hshift1Row'
      cases diagonal0 <;> cases diagonal1 <;> norm_num at hshiftRow' hshift1Row' ⊢ <;>
        nlinarith [htailBounds.1, htailBounds.2]

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
  let δ : example1.DiscountRate := ⟨3 / 4, by norm_num⟩
  let lam : example1.DiscountRate := ⟨7 / 8, by norm_num⟩
  refine ⟨example1, δ, lam, by norm_num [δ, lam], ?_, ?_⟩
  · intro hinclusion
    rcases example1_discounted_nonmonotone with
      ⟨⟨profile, _hnash, hpayoff⟩, _hD1, hnot⟩
    apply hnot
    apply hinclusion
    exact ⟨profile, hpayoff⟩
  · intro hinclusion
    have hmem := hinclusion example1_discounted_nonmonotone.1
    rcases hmem with ⟨profile, _hnash, hpayoff⟩
    exact example1_discounted_nonmonotone.2.2 ⟨profile, hpayoff⟩

/-! Proposition 4 uses Fenchel's theorem that a point in the convex hull of a
connected subset of `ℝᴺ` needs at most `N` terms, followed by an infinite
geometric schedule.  That connected-Carathéodory theorem is not available in
the current dependencies. -/
theorem proposition_4 (G : FiniteStageGame) (lam : ℝ)
    (hlam : 0 < lam) (hbound : lam < 1 / (Fintype.card G.Player : ℝ)) :
    G.discountedFeasiblePayoffs lam = G.correlatedFeasiblePayoffs := by
  sorry

/-! Example 5 proves the constant `1/N` sharp for the paper's discount
domain `0 < λ ≤ 1`. -/
theorem example5_sharp (N : ℕ) [NeZero N]
    (rate : (example5 N).DiscountRate)
    (hlam : 1 / (N : ℝ) < rate.1) :
    (fun _ : Fin N => 1 / (N : ℝ)) ∉
      (example5 N).discountedFeasiblePayoffsOnRate rate := by
  rintro ⟨profile, hpayoff⟩
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN : 2 ≤ N := by
    by_contra hnot
    have hNone : N = 1 := by omega
    subst N
    norm_num at hlam
    linarith [rate.2.2]
  have hNcast : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNpos)
  have htotal : ∑ who,
      (example5 N).discountedPayoffOnRate rate profile who = 1 := by
    change ∑ who, (example5 N).discountedPayoff rate.1 profile who = 1
    rw [hpayoff]
    change (∑ _who : Fin N, 1 / (N : ℝ)) = 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul]
    rw [div_eq_mul_inv, one_mul]
    exact mul_inv_cancel₀ hNcast
  have hinitialTotal :=
    example5_initial_total_eq_one_of_discounted_total_eq_one
      N rate profile htotal
  obtain ⟨label, hpure⟩ :=
    example5_mixedProfile_common_pure_of_total_eq_one
      N hN ((example5 N).initialMixedProfile profile) hinitialTotal
  let constantAction : Fin N → Fin N := fun _ => label
  have hinitialPure : (example5 N).initialMixedProfile profile =
      (example5 N).kernel.pureMixedProfile constantAction := by
    funext who
    exact hpure who
  let empty := (example5 N).repeatedGame.emptyHist PUnit.unit
  have hcurrent : (fun player => profile player 0 empty) =
      (example5 N).initialMixedProfile profile := rfl
  have hstage :
      (example5 N).repeatedGame.stageEUAt profile empty label = 1 := by
    rw [example5_stageEUAt_eq_mixedPayoff N profile empty label,
      hcurrent, hinitialPure]
    change (example5 N).kernel.mixedExtension.payoffVector
      ((example5 N).kernel.pureMixedProfile constantAction) label = 1
    rw [(example5 N).kernel.mixedExtension_payoffVector_pureMixedProfile]
    simp [constantAction, example5]
  let beta := 1 - rate.1
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    linarith [rate.2.2]
  have hbeta1 : beta < 1 := by
    dsimp only [beta]
    linarith [rate.2.1]
  letI (who : Fin N) : Finite ((example5 N).repeatedGame.Act who) :=
    @Finite.of_fintype _ ((example5 N).finiteAction who)
  letI : Finite (example5 N).repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  letI : Subsingleton (example5 N).repeatedGame.State := by
    change Subsingleton PUnit
    infer_instance
  have hbound : ∀ state action,
      |(example5 N).repeatedGame.stagePayoff state action label| ≤ 1 := by
    intro state action
    simp only [FiniteStageGame.repeatedGame,
      KernelGame.realizedActionStochasticGame,
      FiniteStageGame.kernel, KernelGame.eu_ofPureEU, example5]
    split_ifs <;> norm_num
  let actionLaw := (example5 N).repeatedGame.stageActionDist profile empty
  have htailNonneg : 0 ≤ Math.Probability.expect actionLaw fun action =>
      Math.Probability.expect
        ((example5 N).repeatedGame.transition PUnit.unit action) fun state =>
          (example5 N).repeatedGame.discountedPayoff beta
            ((example5 N).repeatedGame.shiftProfile
              profile (PUnit.unit, action)) state label := by
    apply Math.Probability.expect_nonneg
    intro action
    apply Math.Probability.expect_nonneg
    intro state
    have hstate : state = PUnit.unit := Subsingleton.elim _ _
    subst state
    have hmem : (fun who =>
        (example5 N).repeatedGame.discountedPayoff beta
          ((example5 N).repeatedGame.shiftProfile
            profile (PUnit.unit, action)) PUnit.unit who) ∈
        (example5 N).correlatedFeasiblePayoffs := by
      apply lemma_1_Dlambda_subset_C (example5 N) rate
      exact ⟨(example5 N).repeatedGame.shiftProfile
        profile (PUnit.unit, action), rfl⟩
    exact (example5_correlated_bounds N hmem).1 label
  have hshift := (example5 N).repeatedGame.discountedPayoff_shift
    hbound profile PUnit.unit (β := beta) hbeta0 hbeta1
  have hpayoffLabel := congrFun hpayoff label
  change (example5 N).repeatedGame.discountedPayoff beta
      profile PUnit.unit label = 1 / (N : ℝ) at hpayoffLabel
  dsimp only [empty, actionLaw] at htailNonneg
  rw [hstage] at hshift
  dsimp only [beta] at hshift hpayoffLabel htailNonneg
  rw [hpayoffLabel] at hshift
  nlinarith

/-! Proposition 5 is a finite-horizon splice using convexity of `Dₙ`. -/
private theorem finiteFeasiblePayoffs_succ_eq_of_convex
    (G : FiniteStageGame) (n : ℕ) (hn : 0 < n)
    (hconvex : Convex ℝ (G.finiteFeasiblePayoffs n)) :
    G.finiteFeasiblePayoffs (n + 1) = G.finiteFeasiblePayoffs n := by
  let horizon : G.Horizon := ⟨n, hn⟩
  have hC : G.finiteFeasiblePayoffs n = G.correlatedFeasiblePayoffs :=
    (lemma_1_Dn_convex_iff G horizon).mp hconvex
  apply Set.Subset.antisymm
  · intro payoff hpayoff
    rw [hC]
    exact lemma_1_Dn_subset_C G ⟨n + 1, by omega⟩ hpayoff
  · intro payoff hpayoff
    by_cases hn1 : n = 1
    · subst n
      have hD1 : G.oneStageFeasiblePayoffs =
          G.correlatedFeasiblePayoffs := by
        rw [← finiteFeasiblePayoffs_one_eq_oneStageFeasiblePayoffs]
        exact hC
      have hD2 := finiteFeasiblePayoffs_eq_correlated_of_oneStage_eq
        G hD1 ⟨2, by omega⟩
      change payoff ∈ G.finiteFeasiblePayoffsOnHorizon ⟨2, by omega⟩
      rw [hD2, ← hC]
      exact hpayoff
    · have hn2 : 1 < n := by omega
      obtain ⟨profile, hprofile⟩ := hpayoff
      let stage : ℕ → Payoff G.Player := fun time ↦
        fun who ↦ G.repeatedGame.expectedStagePayoff
          profile G.repeatedInitial time who
      let first := G.finitePayoff 1 profile
      let tail := ((n - 1 : ℕ) : ℝ)⁻¹ •
        ∑ time ∈ Finset.range (n - 1), stage (time + 1)
      have hfirstD1 : first ∈ G.oneStageFeasiblePayoffs := by
        rw [← finiteFeasiblePayoffs_one_eq_oneStageFeasiblePayoffs]
        exact ⟨profile, rfl⟩
      have hfirstDn : first ∈ G.finiteFeasiblePayoffs n :=
        lemma_1_D1_subset_Dn G horizon hfirstD1
      have htailC : tail ∈ G.correlatedFeasiblePayoffs := by
        dsimp only [tail]
        rw [Finset.smul_sum]
        apply G.correlatedFeasiblePayoffs_convex.sum_mem
        · intro _ _
          positivity
        · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          apply mul_inv_cancel₀
          exact_mod_cast (by omega : n - 1 ≠ 0)
        · intro time htime
          dsimp only [stage]
          exact expectedStagePayoff_mem_correlatedFeasiblePayoffs
            G profile (time + 1)
      have htailDn : tail ∈ G.finiteFeasiblePayoffs n := by
        rwa [hC]
      have hfirstEq : first = stage 0 := by
        dsimp only [first, stage]
        funext who
        unfold FiniteStageGame.finitePayoff
        rw [G.repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
        simp
      have hdecomp :
          (n : ℝ) • G.finitePayoff n profile =
            first + (n - 1 : ℝ) • tail := by
        rw [cast_smul_finitePayoff_eq_sum, hfirstEq]
        ext who
        simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, stage, tail]
        conv_lhs =>
          rw [show n = (n - 1) + 1 by omega]
          rw [Finset.sum_range_succ']
        simp only [Nat.cast_sub (by omega : 1 ≤ n)]
        have hnsub : (n : ℝ) - 1 ≠ 0 := by
          intro hzero
          apply hn1
          have : (n : ℝ) = 1 := by linarith
          exact_mod_cast this
        norm_num only [Nat.cast_one]
        rw [← mul_assoc, mul_inv_cancel₀ hnsub, one_mul]
        abel
      let coefficient : ℝ := (n : ℝ)⁻¹ ^ 2
      let splice := coefficient • first + (1 - coefficient) • tail
      have hcoefficient0 : 0 ≤ coefficient := by
        dsimp only [coefficient]
        positivity
      have hcoefficient1 : coefficient ≤ 1 := by
        dsimp only [coefficient]
        have hnreal : 1 ≤ (n : ℝ) := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
        have hinv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hnreal
        nlinarith [sq_nonneg ((n : ℝ)⁻¹),
          mul_self_le_mul_self (inv_nonneg.mpr (by positivity)) hinv]
      have hsplice : splice ∈ G.finiteFeasiblePayoffs n := by
        exact hconvex hfirstDn htailDn hcoefficient0
          (by linarith) (by ring)
      have hscaledFirst : first ∈
          scaleSet (1 : ℝ) (G.finiteFeasiblePayoffs 1) := by
        refine ⟨first, ?_, by simp⟩
        rw [finiteFeasiblePayoffs_one_eq_oneStageFeasiblePayoffs]
        exact hfirstD1
      have hscaledSplice : (n : ℝ) • splice ∈
          scaleSet (n : ℝ) (G.finiteFeasiblePayoffs n) :=
        ⟨splice, hsplice, rfl⟩
      have hiterated : (n : ℝ) • splice ∈
          iteratedAddSet 1
            (scaleSet (n : ℝ) (G.finiteFeasiblePayoffs n)) := by
        refine ⟨fun _ ↦ (n : ℝ) • splice, fun _ ↦ hscaledSplice, ?_⟩
        simp
      have hadd : (n : ℝ) • splice + first ∈
          addSet
            (iteratedAddSet 1
              (scaleSet (n : ℝ) (G.finiteFeasiblePayoffs n)))
            (scaleSet (1 : ℝ) (G.finiteFeasiblePayoffs 1)) :=
        ⟨(n : ℝ) • splice, hiterated, first, hscaledFirst, by simp⟩
      have hinclusion := lemma_3_feasible G (n + 1) 1 n 1 (by omega)
      have hadd' : (n : ℝ) • splice + first ∈
          addSet
            (iteratedAddSet 1
              (scaleSet (n : ℝ) (G.finiteFeasiblePayoffs n)))
            (scaleSet ((1 : ℕ) : ℝ) (G.finiteFeasiblePayoffs 1)) := by
        simpa only [Nat.cast_one] using hadd
      obtain ⟨realized, hrealized, hscaled⟩ := hinclusion hadd'
      obtain ⟨realizedProfile, hrealizedPayoff⟩ := hrealized
      refine ⟨realizedProfile, ?_⟩
      have htarget :
          (n : ℝ) • splice + first =
            (n + 1 : ℝ) • payoff := by
        rw [← hprofile]
        dsimp only [splice, coefficient]
        ext who
        have hdecompWho := congrFun hdecomp who
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          at hdecompWho ⊢
        have hnreal : (n : ℝ) ≠ 0 := by positivity
        field_simp [hnreal]
        nlinarith
      have hsame : (n + 1 : ℝ) • realized =
          (n + 1 : ℝ) • payoff := by
        norm_num [Nat.cast_add, Nat.cast_one] at hscaled ⊢
        exact hscaled.symm.trans htarget
      have hrealizedEq : realized = payoff :=
        smul_right_injective (Payoff G.Player)
          (by positivity : (n + 1 : ℝ) ≠ 0) hsame
      rw [hrealizedPayoff, hrealizedEq]

theorem proposition_5 (G : FiniteStageGame) (n : ℕ) (hn : 0 < n)
    (hconvex : Convex ℝ (G.finiteFeasiblePayoffs n)) :
    G.finiteFeasiblePayoffs (n + 1) = G.finiteFeasiblePayoffs n ∧
      ∀ m, n < m →
        G.finiteFeasiblePayoffs m = G.correlatedFeasiblePayoffs := by
  have hnext := finiteFeasiblePayoffs_succ_eq_of_convex G n hn hconvex
  have hC : G.finiteFeasiblePayoffs n = G.correlatedFeasiblePayoffs :=
    (lemma_1_Dn_convex_iff G ⟨n, hn⟩).mp hconvex
  constructor
  · exact hnext
  · intro m hm
    have hbase : G.finiteFeasiblePayoffs (n + 1) =
        G.correlatedFeasiblePayoffs := hnext.trans hC
    exact Nat.le_induction hbase (fun k hk ih ↦ by
      have hkpos : 0 < k := by omega
      have hkconvex : Convex ℝ (G.finiteFeasiblePayoffs k) := by
        rw [ih]
        exact G.correlatedFeasiblePayoffs_convex
      exact (finiteFeasiblePayoffs_succ_eq_of_convex
        G k hkpos hkconvex).trans ih) m (by omega)

/-- Equation (19). -/
theorem equation_19 (G : FiniteStageGame) (n : ℕ) (hn : 0 < n)
    (hstable : ∀ m, n < m →
      G.finiteFeasiblePayoffs m = G.finiteFeasiblePayoffs n) :
    G.finiteFeasiblePayoffs n = G.correlatedFeasiblePayoffs := by
  let horizon : G.Horizon := ⟨n, hn⟩
  have hn2 : n < 2 * n := by omega
  have hreverse : G.finiteFeasiblePayoffs (2 * n) ⊆
      G.finiteFeasiblePayoffs n := by
    rw [hstable (2 * n) hn2]
  have hconvex : Convex ℝ (G.finiteFeasiblePayoffs n) := by
    simpa only [horizon] using
      post_lemma_3_D_convex_of_reverse_multiple G horizon
        (k := 2) (by omega) hreverse
  exact (lemma_1_Dn_convex_iff G horizon).mp hconvex

/-- The convex hull of Example 6's pure payoffs lies in its displayed
rectangle `[0,3] × [0,1]`. -/
theorem example6_C_bounds {v : Payoff Bool}
    (hv : v ∈ example6.correlatedFeasiblePayoffs) :
    0 ≤ v false ∧ v false ≤ 3 ∧ 0 ≤ v true ∧ v true ≤ 1 := by
  let rectangle : Set (Payoff Bool) :=
    {w | 0 ≤ w false ∧ w false ≤ 3 ∧ 0 ≤ w true ∧ w true ≤ 1}
  have hpure : example6.purePayoffSet ⊆ rectangle := by
    rintro _ ⟨action, rfl⟩
    change 0 ≤ example6Payoff action false ∧
      example6Payoff action false ≤ 3 ∧
      0 ≤ example6Payoff action true ∧
      example6Payoff action true ≤ 1
    cases hrow : action false <;> cases hcolumn : action true <;>
      norm_num [example6Payoff, hrow, hcolumn, pair]
  have hconvex : Convex ℝ rectangle := by
    rintro first hfirst second hsecond a b ha hb hab
    rcases hfirst with ⟨hfirst0, hfirst3, hfirst0', hfirst1⟩
    rcases hsecond with ⟨hsecond0, hsecond3, hsecond0', hsecond1⟩
    change 0 ≤ (a • first + b • second) false ∧
      (a • first + b • second) false ≤ 3 ∧
      0 ≤ (a • first + b • second) true ∧
      (a • first + b • second) true ≤ 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · exact add_nonneg (mul_nonneg ha hfirst0) (mul_nonneg hb hsecond0)
    constructor
    · nlinarith [mul_nonneg ha (sub_nonneg.mpr hfirst3),
        mul_nonneg hb (sub_nonneg.mpr hsecond3)]
    constructor
    · exact add_nonneg (mul_nonneg ha hfirst0') (mul_nonneg hb hsecond0')
    · nlinarith [mul_nonneg ha (sub_nonneg.mpr hfirst1),
        mul_nonneg hb (sub_nonneg.mpr hsecond1)]
  exact convexHull_min hpure hconvex hv

/-- Appending two one-stage profiles realizes the midpoint of their payoffs
in two stages. -/
theorem midpoint_mem_D2_of_mem_D1 (G : FiniteStageGame)
    {first second : Payoff G.Player}
    (hfirst : first ∈ G.oneStageFeasiblePayoffs)
    (hsecond : second ∈ G.oneStageFeasiblePayoffs) :
    midpoint ℝ first second ∈ G.finiteFeasiblePayoffs 2 := by
  obtain ⟨firstProfile, hfirstPayoff⟩ :=
    lemma_1_D1_subset_Dn G ⟨1, by omega⟩ hfirst
  obtain ⟨secondProfile, hsecondPayoff⟩ :=
    lemma_1_D1_subset_Dn G ⟨1, by omega⟩ hsecond
  let joined := G.appendFiniteProfiles 1 firstProfile secondProfile
  refine ⟨joined, ?_⟩
  have hweighted :=
    appendFiniteProfiles_weightedPayoff G 1 1 firstProfile secondProfile
  rw [hfirstPayoff, hsecondPayoff] at hweighted
  norm_num at hweighted
  dsimp only [joined]
  apply smul_right_injective (Payoff G.Player) (by norm_num : (2 : ℝ) ≠ 0)
  change (2 : ℝ) • G.finitePayoff 2
      (G.appendFiniteProfiles 1 firstProfile secondProfile) =
    (2 : ℝ) • midpoint ℝ first second
  rw [hweighted]
  funext who
  simp [midpoint, AffineMap.lineMap_apply_module, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- In Example 6, `(0,1)` and `(3,1)` are one-stage feasible, but their
midpoint `(3/2,1)` is not. -/
theorem example6_D1_not_convex :
    ¬Convex ℝ example6.oneStageFeasiblePayoffs := by
  intro hconvex
  let leftAction : (who : Bool) → Example6Action who
    | false => false
    | true => FourColumn.c0
  let rightAction : (who : Bool) → Example6Action who
    | false => true
    | true => FourColumn.c3
  have hleft : pair 0 1 ∈ example6.oneStageFeasiblePayoffs := by
    apply lemma_1_pure_subset_D1 example6
    refine ⟨leftAction, ?_⟩
    funext who
    cases who <;> rfl
  have hright : pair 3 1 ∈ example6.oneStageFeasiblePayoffs := by
    apply lemma_1_pure_subset_D1 example6
    refine ⟨rightAction, ?_⟩
    funext who
    cases who <;> rfl
  have hmidpoint := hconvex.midpoint_mem hleft hright
  have htarget : midpoint ℝ (pair 0 1) (pair 3 1) = pair (3 / 2) 1 := by
    funext who
    cases who <;>
      norm_num [midpoint, AffineMap.lineMap_apply_module, pair,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [htarget] at hmidpoint
  rcases hmidpoint with ⟨profile, hpayoff⟩
  change ((who : Bool) → PMF (Example6Action who)) at profile
  have hrow := congrFun hpayoff false
  have hcolumn := congrFun hpayoff true
  rw [example6_mixedPayoff_false] at hrow
  rw [example6_mixedPayoff_true] at hcolumn
  norm_num [pair] at hrow hcolumn
  let p := (profile false true).toReal
  let q0 := (profile true FourColumn.c0).toReal
  let q1 := (profile true FourColumn.c1).toReal
  let q2 := (profile true FourColumn.c2).toReal
  let q3 := (profile true FourColumn.c3).toReal
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  have hq00 : 0 ≤ q0 := ENNReal.toReal_nonneg
  have hq10 : 0 ≤ q1 := ENNReal.toReal_nonneg
  have hq20 : 0 ≤ q2 := ENNReal.toReal_nonneg
  have hq30 : 0 ≤ q3 := ENNReal.toReal_nonneg
  have hqsum : q0 + q1 + q2 + q3 = 1 := by
    have hone := Math.Probability.expect_const (profile true) (1 : ℝ)
    rw [Math.Probability.expect_eq_sum, sum_fourColumn] at hone
    norm_num at hone
    exact hone
  change q1 + 2 * q2 + 3 * q3 = 3 / 2 at hrow
  change (1 - p) * (q0 + q1) + p * (q2 + q3) = 1 at hcolumn
  have hzero : (1 - p) * (q2 + q3) + p * (q0 + q1) = 0 := by
    nlinarith
  have hfirst0 : (1 - p) * (q2 + q3) = 0 := by
    have hfirst_nonneg : 0 ≤ (1 - p) * (q2 + q3) :=
      mul_nonneg (by linarith) (by linarith)
    have hsecond_nonneg : 0 ≤ p * (q0 + q1) :=
      mul_nonneg hp0 (by linarith)
    nlinarith
  have hsecond0 : p * (q0 + q1) = 0 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - p) (by linarith : 0 ≤ q2 + q3)]
  by_cases hp : p = 0
  · rw [hp] at hfirst0
    norm_num at hfirst0
    nlinarith
  · have hq01 : q0 + q1 = 0 := (mul_eq_zero.mp hsecond0).resolve_left hp
    nlinarith

/-! The second half of Equation (20) is the paper's two-stage
convexification calculation. -/
theorem example6_D2_eq_C :
    example6.finiteFeasiblePayoffs 2 =
      example6.correlatedFeasiblePayoffs := by
  apply Set.Subset.antisymm
  · exact lemma_1_Dn_subset_C example6 ⟨2, by omega⟩
  · intro payoff hpayoff
    obtain ⟨hx0, hx3, hy0, hy1⟩ := example6_C_bounds hpayoff
    let x := payoff false
    let y := payoff true
    have hpayoff_eq : payoff = pair x y := by
      funext who
      cases who <;> rfl
    rw [hpayoff_eq]
    change 0 ≤ x at hx0
    change x ≤ 3 at hx3
    change 0 ≤ y at hy0
    change y ≤ 1 at hy1
    by_cases hx1 : x ≤ 1
    · exact lemma_1_D1_subset_Dn example6 ⟨2, by omega⟩
        (example6_outerStrip_mem_D1 x y hx0 hx3 hy0 hy1 (Or.inl hx1))
    by_cases hx2 : 2 ≤ x
    · exact lemma_1_D1_subset_Dn example6 ⟨2, by omega⟩
        (example6_outerStrip_mem_D1 x y hx0 hx3 hy0 hy1 (Or.inr hx2))
    by_cases hhalf : x ≤ 3 / 2
    · have hleft : pair (2 * x - 2) y ∈
          example6.oneStageFeasiblePayoffs := by
        apply example6_outerStrip_mem_D1
        · linarith
        · linarith
        · exact hy0
        · exact hy1
        · left
          linarith
      have hright : pair 2 y ∈ example6.oneStageFeasiblePayoffs := by
        exact example6_outerStrip_mem_D1 2 y (by norm_num) (by norm_num)
          hy0 hy1 (Or.inr le_rfl)
      have hmidpoint :=
        midpoint_mem_D2_of_mem_D1 example6 hleft hright
      convert hmidpoint using 1
      funext who
      cases who <;>
        simp [midpoint, AffineMap.lineMap_apply_module, pair,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
    · have hleft : pair 1 y ∈ example6.oneStageFeasiblePayoffs := by
        apply example6_outerStrip_mem_D1 1 y <;> simp_all
      have hright : pair (2 * x - 1) y ∈
          example6.oneStageFeasiblePayoffs := by
        apply example6_outerStrip_mem_D1
        · linarith
        · linarith
        · exact hy0
        · exact hy1
        · right
          linarith
      have hmidpoint :=
        midpoint_mem_D2_of_mem_D1 example6 hleft hright
      convert hmidpoint using 1
      funext who
      cases who <;>
        simp [midpoint, AffineMap.lineMap_apply_module, pair,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Equation (20), witnessed by Example 6. -/
theorem example6_D1_not_convex_D2_eq_C :
    ¬Convex ℝ example6.oneStageFeasiblePayoffs ∧
      example6.finiteFeasiblePayoffs 2 = example6.correlatedFeasiblePayoffs := by
  exact ⟨example6_D1_not_convex, example6_D2_eq_C⟩

/-! The paper's two-by-two dichotomy follows from Proposition 5. -/
theorem two_by_two_feasible_dichotomy
    (topLeft topRight bottomLeft bottomRight : Payoff Bool) :
    let G := binaryGame topLeft topRight bottomLeft bottomRight
    G.oneStageFeasiblePayoffs = G.correlatedFeasiblePayoffs ∨
      ∀ n, 0 < n → G.finiteFeasiblePayoffs n ≠
        G.correlatedFeasiblePayoffs := by
  sorry

/-- A bounded affine recursion is realized by its normalized geometric
series.  This is the scalar telescoping step in Proposition 6. -/
private theorem discounted_sum_eq_of_affine_recurrence
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (state stage : ℕ → ℝ) (bound : ℝ)
    (hbound : ∀ time, |state time| ≤ bound)
    (hrec : ∀ time,
      state time = δ * stage time + (1 - δ) * state (time + 1)) :
    δ * ∑' time : ℕ, (1 - δ) ^ time * stage time = state 0 := by
  let beta := 1 - δ
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    linarith
  have hbeta1 : beta < 1 := by
    dsimp only [beta]
    linarith
  have hbound0 : 0 ≤ bound :=
    (abs_nonneg (state 0)).trans (hbound 0)
  have hgeom : Summable (fun time : ℕ => beta ^ time) :=
    summable_geometric_of_lt_one hbeta0 hbeta1
  let weightedState : ℕ → ℝ :=
    fun time => beta ^ time * state time
  have hweightedState : Summable weightedState := by
    apply Summable.of_norm_bounded (hgeom.mul_left bound)
    intro time
    dsimp only [weightedState]
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hbeta0]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hbound time) (pow_nonneg hbeta0 time)
  have hweightedTail : Summable (fun time => weightedState (time + 1)) :=
    hweightedState.comp_injective Nat.succ_injective
  rw [← tsum_mul_left]
  calc
    (∑' time : ℕ, δ * ((1 - δ) ^ time * stage time)) =
        ∑' time : ℕ, (weightedState time - weightedState (time + 1)) := by
      apply tsum_congr
      intro time
      have h := hrec time
      dsimp only [weightedState, beta]
      rw [pow_succ']
      calc
        δ * ((1 - δ) ^ time * stage time) =
            (1 - δ) ^ time * (δ * stage time) := by ring
        _ = (1 - δ) ^ time *
            (state time - (1 - δ) * state (time + 1)) := by
          congr 1
          linarith
        _ = (1 - δ) ^ time * state time -
            (1 - δ) * (1 - δ) ^ time * state (time + 1) := by
          ring
    _ = (∑' time : ℕ, weightedState time) -
        ∑' time : ℕ, weightedState (time + 1) :=
      hweightedState.tsum_sub hweightedTail
    _ = state 0 := by
      rw [hweightedState.tsum_eq_zero_add]
      simp [weightedState]

/-! Proposition 6 is the discounted analogue of Proposition 5. -/
theorem proposition_6 (G : FiniteStageGame) (lam : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hconvex : Convex ℝ (G.discountedFeasiblePayoffs lam)) :
    ∀ δ : ℝ, 0 < δ → δ < lam →
      G.discountedFeasiblePayoffs δ = G.correlatedFeasiblePayoffs := by
  intro δ hδ hδlam
  have hδ1 : δ ≤ 1 := (le_of_lt hδlam).trans hlam1
  let lamRate : G.DiscountRate := ⟨lam, hlam, hlam1⟩
  let deltaRate : G.DiscountRate := ⟨δ, hδ, hδ1⟩
  have hC : G.discountedFeasiblePayoffs lam =
      G.correlatedFeasiblePayoffs := by
    exact (lemma_1_Dlambda_convex_iff G lamRate).mp hconvex
  letI (who : G.Player) : Finite (G.repeatedGame.Act who) :=
    @Finite.of_fintype _ (G.finiteAction who)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  letI : Subsingleton G.repeatedGame.State :=
    inferInstanceAs (Subsingleton PUnit)
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ who, G.Action who)
    exact Finite.of_fintype _
  obtain ⟨rawBound, hrawBound⟩ :=
    Math.Probability.exists_abs_bound_of_finite
      (fun data : G.repeatedGame.State ×
          G.repeatedGame.JointAct × G.Player =>
        G.repeatedGame.stagePayoff data.1 data.2.1 data.2.2)
  let bound := max rawBound 0
  have hbound0 : 0 ≤ bound := le_max_right _ _
  have hstageBound : ∀ state action who,
      |G.repeatedGame.stagePayoff state action who| ≤ bound := by
    intro state action who
    exact (hrawBound (state, action, who)).trans (le_max_left _ _)
  have hCbound (who : G.Player) {payoff : Payoff G.Player}
      (hpayoff : payoff ∈ G.correlatedFeasiblePayoffs) :
      |payoff who| ≤ bound := by
    apply (convexHull_min (t := {v : Payoff G.Player |
      |v who| ≤ bound}) ?_ ?_) hpayoff
    · rintro _ ⟨action, rfl⟩
      simpa [FiniteStageGame.repeatedGame,
        KernelGame.realizedActionStochasticGame,
        FiniteStageGame.kernel, KernelGame.eu_ofPureEU] using
          hstageBound PUnit.unit action who
    · intro x hx y hy a b ha hb hab
      change |a * x who + b * y who| ≤ bound
      calc
        |a * x who + b * y who| ≤
            |a * x who| + |b * y who| := abs_add_le _ _
        _ = a * |x who| + b * |y who| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * bound + b * bound := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hx ha)
            (mul_le_mul_of_nonneg_left hy hb)
        _ = bound := by rw [← add_mul, hab, one_mul]
  have hdecompose (payoff : Payoff G.Player)
      (hpayoff : payoff ∈ G.correlatedFeasiblePayoffs) :
      ∃ next : Payoff G.Player,
        next ∈ G.correlatedFeasiblePayoffs ∧
          ∃ current : G.MixedProfile,
            payoff = δ • G.mixedPayoff current + (1 - δ) • next := by
    have hpayoffLam : payoff ∈ G.discountedFeasiblePayoffs lam := by
      rw [hC]
      exact hpayoff
    obtain ⟨profile, hprofile⟩ := hpayoffLam
    let empty := G.repeatedGame.emptyHist PUnit.unit
    let current := G.initialMixedProfile profile
    let actionLaw := G.repeatedGame.stageActionDist profile empty
    let continuation (action : G.repeatedGame.JointAct) :
        Payoff G.Player := fun who =>
      G.repeatedGame.discountedPayoff (1 - lam)
        (G.repeatedGame.shiftProfile profile (PUnit.unit, action))
          PUnit.unit who
    let tail : Payoff G.Player := fun who =>
      Math.Probability.expect actionLaw fun action => continuation action who
    have hcontinuation (action : G.repeatedGame.JointAct) :
        continuation action ∈ G.correlatedFeasiblePayoffs := by
      apply lemma_1_Dlambda_subset_C G lamRate
      exact ⟨G.repeatedGame.shiftProfile profile (PUnit.unit, action), rfl⟩
    have htail : tail ∈ G.correlatedFeasiblePayoffs := by
      have hhull :=
        Math.ProbabilityMassFunction.coordinateExpectation_mem_convexHull_range
          actionLaw continuation
      apply convexHull_min ?_ G.correlatedFeasiblePayoffs_convex hhull
      rintro _ ⟨action, rfl⟩
      exact hcontinuation action
    have hstage (who : G.Player) :
        G.repeatedGame.stageEUAt profile empty who =
          G.mixedPayoff current who := by
      unfold StochasticGame.stageEUAt StochasticGame.stageActionDist
      unfold FiniteStageGame.mixedPayoff KernelGame.payoffVector
      change Math.Probability.expect (Math.PMFProduct.pmfPi current)
          (fun action => G.kernel.eu action who) =
        G.kernel.mixedExtension.eu current who
      exact (G.kernel.mixedExtension_eu current who).symm
    have hbellman : payoff =
        lam • G.mixedPayoff current + (1 - lam) • tail := by
      funext who
      have hshift := G.repeatedGame.discountedPayoff_shift
        (hstageBound · · who) profile PUnit.unit
        (β := 1 - lam) (by linarith) (by linarith)
      simp_rw [show ∀ action (f : G.repeatedGame.State → ℝ),
          Math.Probability.expect
              (G.repeatedGame.transition PUnit.unit action) f =
            f PUnit.unit by
        intro action f
        have htransition : G.repeatedGame.transition PUnit.unit action =
            PMF.pure PUnit.unit := rfl
        rw [htransition]
        exact Math.Probability.expect_pure f PUnit.unit] at hshift
      have hcoordinate := congrFun hprofile who
      change G.repeatedGame.discountedPayoff (1 - lam)
        profile PUnit.unit who = payoff who at hcoordinate
      rw [← hcoordinate]
      change G.repeatedGame.discountedPayoff (1 - lam)
          profile PUnit.unit who =
        lam * G.mixedPayoff current who + (1 - lam) * tail who
      simpa [hstage who, tail, continuation, actionLaw, empty,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hshift
    by_cases hlamOne : lam = 1
    · refine ⟨payoff, hpayoff, current, ?_⟩
      have hcurrentEq : G.mixedPayoff current = payoff := by
        rw [hlamOne] at hbellman
        simpa using hbellman.symm
      rw [hcurrentEq]
      module
    · have hlamLt : lam < 1 := lt_of_le_of_ne hlam1 hlamOne
      have hδLt : δ < 1 := hδlam.trans_le hlam1
      have hdenom : 1 - δ ≠ 0 := ne_of_gt (sub_pos.mpr hδLt)
      let firstWeight := (lam - δ) / (1 - δ)
      let tailWeight := (1 - lam) / (1 - δ)
      let next := firstWeight • G.mixedPayoff current + tailWeight • tail
      have hfirst0 : 0 ≤ firstWeight := by
        dsimp only [firstWeight]
        positivity
      have htail0 : 0 ≤ tailWeight := by
        dsimp only [tailWeight]
        positivity
      have hweights : firstWeight + tailWeight = 1 := by
        dsimp only [firstWeight, tailWeight]
        field_simp [hdenom]
        ring
      have hfirstMem := G.mixedPayoff_mem_correlatedFeasiblePayoffs current
      have hnext : next ∈ G.correlatedFeasiblePayoffs :=
        G.correlatedFeasiblePayoffs_convex hfirstMem htail
          hfirst0 htail0 hweights
      refine ⟨next, hnext, current, ?_⟩
      funext who
      have hcoord := congrFun hbellman who
      dsimp only [next, firstWeight, tailWeight]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcoord ⊢
      calc
        payoff who =
            lam * G.mixedPayoff current who + (1 - lam) * tail who := hcoord
        _ = δ * G.mixedPayoff current who +
            (1 - δ) *
              ((lam - δ) / (1 - δ) * G.mixedPayoff current who +
                (1 - lam) / (1 - δ) * tail who) := by
          field_simp [hdenom]
          ring
  apply Set.Subset.antisymm
  · simpa only [deltaRate] using lemma_1_Dlambda_subset_C G deltaRate
  · intro payoff hpayoff
    let Carrier := {v : Payoff G.Player //
      v ∈ G.correlatedFeasiblePayoffs}
    let nextValue (state : Carrier) : Payoff G.Player :=
      Classical.choose (hdecompose state.1 state.2)
    have nextValue_spec (state : Carrier) :
        nextValue state ∈ G.correlatedFeasiblePayoffs ∧
          ∃ current : G.MixedProfile,
            state.1 = δ • G.mixedPayoff current +
              (1 - δ) • nextValue state :=
      Classical.choose_spec (hdecompose state.1 state.2)
    let next (state : Carrier) : Carrier :=
      ⟨nextValue state, (nextValue_spec state).1⟩
    let current (state : Carrier) : G.MixedProfile :=
      Classical.choose (nextValue_spec state).2
    have current_spec (state : Carrier) :
        state.1 = δ • G.mixedPayoff (current state) +
          (1 - δ) • (next state).1 := by
      exact Classical.choose_spec (nextValue_spec state).2
    let state : ℕ → Carrier := fun time =>
      Nat.rec ⟨payoff, hpayoff⟩ (fun _ previous => next previous) time
    let stages : ℕ → G.MixedProfile := fun time => current (state time)
    have hrec (time : ℕ) :
        (state time).1 = δ • G.mixedPayoff (stages time) +
          (1 - δ) • (state (time + 1)).1 := by
      simpa [state, stages] using current_spec (state time)
    let behavior := mixedSequenceBehavior G stages
    refine ⟨behavior, ?_⟩
    funext who
    change G.repeatedGame.discountedPayoff (1 - δ)
      behavior PUnit.unit who = payoff who
    unfold StochasticGame.discountedPayoff
    have hstage (time : ℕ) :
        G.repeatedGame.expectedStagePayoff behavior
            PUnit.unit time who =
          G.mixedPayoff (stages time) who := by
      have h := congrFun
        (expectedStagePayoff_mixedSequenceBehavior G stages time) who
      exact h
    simp_rw [hstage]
    rw [show 1 - (1 - δ) = δ by ring]
    have hscalarRec (time : ℕ) :
        (state time).1 who =
          δ * G.mixedPayoff (stages time) who +
            (1 - δ) * (state (time + 1)).1 who := by
      have h := congrFun (hrec time) who
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
    have hstateBound (time : ℕ) :
        |(state time).1 who| ≤ bound :=
      hCbound who (state time).2
    rw [discounted_sum_eq_of_affine_recurrence
      δ hδ hδ1 (fun time => (state time).1 who)
        (fun time => G.mixedPayoff (stages time) who)
        bound hstateBound hscalarRec]
    rfl

/-- Equation (22). -/
theorem equation_22 (G : FiniteStageGame) (lam : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hstable : ∀ δ : ℝ, 0 < δ → δ < lam →
      G.discountedFeasiblePayoffs δ = G.discountedFeasiblePayoffs lam) :
    G.discountedFeasiblePayoffs lam = G.correlatedFeasiblePayoffs := by
  let rate : G.DiscountRate := ⟨lam, hlam, hlam1⟩
  have hclosed : IsClosed (G.discountedFeasiblePayoffs lam) := by
    simpa only [rate] using (property_1_discounted G rate).2.2.isClosed
  apply Set.Subset.antisymm
  · simpa only [rate] using lemma_1_Dlambda_subset_C G rate
  · intro payoff hpayoff
    apply hclosed.closure_subset
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ₀, hδ₀, hclose⟩ := property_3 G |>.2.1 ε hε
    let δ := min (lam / 2) (δ₀ / 2)
    have hδ : 0 < δ := by
      dsimp only [δ]
      positivity
    have hδlam : δ < lam := by
      dsimp only [δ]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hlam)
    have hδδ₀ : δ < δ₀ := by
      dsimp only [δ]
      exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ₀)
    obtain ⟨nearby, hnearby, hdist⟩ := (hclose δ hδ hδδ₀).2 payoff hpayoff
    refine ⟨nearby, ?_, ?_⟩
    · rwa [hstable δ hδ hδlam] at hnearby
    · simpa only [dist_comm] using hdist

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
abbrev prisonersDilemma : FiniteStageGame :=
  binaryGame (pair 4 4) (pair 0 5) (pair 5 0) (pair 1 1)

/-- The row player's one-stage payoff is affine in the two defection
probabilities. -/
theorem prisonersDilemma_mixedEU_false (profile : Bool → PMF Bool) :
    (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
        (pair 1 1))).mixedExtension.eu profile false =
      4 + (profile false true).toReal - 4 * (profile true true).toReal := by
  rw [binaryKernel_mixedEU_apply]
  simp only [pair_false]
  ring

/-- The column player's one-stage payoff is affine in the two defection
probabilities. -/
theorem prisonersDilemma_mixedEU_true (profile : Bool → PMF Bool) :
    (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
        (pair 1 1))).mixedExtension.eu profile true =
      4 + (profile true true).toReal - 4 * (profile false true).toReal := by
  rw [binaryKernel_mixedEU_apply]
  simp only [pair_true]
  ring

/-- A row deviation in the Prisoner's Dilemma changes only its own defection
probability. -/
theorem prisonersDilemma_mixedEU_update_false
    (profile : Bool → PMF Bool) (deviation : PMF Bool) :
    (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
        (pair 1 1))).mixedExtension.eu
          (Function.update profile false deviation) false =
      4 + (deviation true).toReal - 4 * (profile true true).toReal := by
  rw [prisonersDilemma_mixedEU_false]
  change 4 + (deviation true).toReal - 4 * (profile true true).toReal = _
  rfl

/-- A column deviation in the Prisoner's Dilemma changes only its own
defection probability. -/
theorem prisonersDilemma_mixedEU_update_true
    (profile : Bool → PMF Bool) (deviation : PMF Bool) :
    (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
        (pair 1 1))).mixedExtension.eu
          (Function.update profile true deviation) true =
      4 + (deviation true).toReal - 4 * (profile false true).toReal := by
  rw [prisonersDilemma_mixedEU_true]
  change 4 + (deviation true).toReal - 4 * (profile false true).toReal = _
  rfl

/-- A pure Bottom deviation gives the row player payoff
`5 - 4 q`, where `q` is the column player's Bottom probability. -/
private theorem prisonersDilemma_mixedEU_update_false_pure
    (profile : Bool → PMF Bool) :
    (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
        (pair 1 1))).mixedExtension.eu
          (Function.update profile false (PMF.pure true)) false =
      5 - 4 * (profile true true).toReal := by
  rw [prisonersDilemma_mixedEU_update_false]
  change 4 + ((PMF.pure true : PMF Bool) true).toReal -
    4 * (profile true true).toReal = _
  simp
  ring

/-- A pure Right deviation gives the column player payoff
`5 - 4 p`, where `p` is the row player's Bottom probability. -/
private theorem prisonersDilemma_mixedEU_update_true_pure
    (profile : Bool → PMF Bool) :
    (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
        (pair 1 1))).mixedExtension.eu
          (Function.update profile true (PMF.pure true)) true =
      5 - 4 * (profile false true).toReal := by
  rw [prisonersDilemma_mixedEU_update_true]
  change 4 + ((PMF.pure true : PMF Bool) true).toReal -
    4 * (profile false true).toReal = _
  simp
  ring

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
  have hconvex : Convex ℝ
      ((binaryGame (pair 4 4) (pair 0 5) (pair 5 0)
        (pair 1 1)).oneStageFeasiblePayoffs) := by
    rintro _ ⟨first, rfl⟩ _ ⟨second, rfl⟩ a b ha hb hab
    change (Bool → PMF Bool) at first second
    let probability (who : Bool) :=
      a * (first who true).toReal + b * (second who true).toReal
    have hprob0 (who : Bool) : 0 ≤ probability who :=
      add_nonneg (mul_nonneg ha ENNReal.toReal_nonneg)
        (mul_nonneg hb ENNReal.toReal_nonneg)
    have hprob1 (who : Bool) : probability who ≤ 1 := by
      have hfirst : (first who true).toReal ≤ 1 :=
        ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
      have hsecond : (second who true).toReal ≤ 1 :=
        ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
      calc
        probability who ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hfirst ha)
            (mul_le_mul_of_nonneg_left hsecond hb)
        _ = 1 := by linarith
    let profile : Bool → PMF Bool := fun who ↦
      Math.ProbabilityMassFunction.bernoulliBool
        (probability who) (hprob0 who) (hprob1 who)
    refine ⟨profile, ?_⟩
    change (fun who ↦
        (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
          (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
            (pair 1 1))).mixedExtension.eu profile who) =
      a • (fun who ↦
        (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
          (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
            (pair 1 1))).mixedExtension.eu first who) +
      b • (fun who ↦
        (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
          (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
            (pair 1 1))).mixedExtension.eu second who)
    funext who
    cases who
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [prisonersDilemma_mixedEU_false,
        prisonersDilemma_mixedEU_false,
        prisonersDilemma_mixedEU_false]
      simp only [profile,
        Math.ProbabilityMassFunction.bernoulliBool_true_toReal]
      simp only [probability]
      ring_nf
      linarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [prisonersDilemma_mixedEU_true,
        prisonersDilemma_mixedEU_true,
        prisonersDilemma_mixedEU_true]
      simp only [profile,
        Math.ProbabilityMassFunction.bernoulliBool_true_toReal]
      simp only [probability]
      ring_nf
      linarith
  change (binaryGame (pair 4 4) (pair 0 5) (pair 5 0)
      (pair 1 1)).oneStageFeasiblePayoffs =
    (binaryGame (pair 4 4) (pair 0 5) (pair 5 0)
      (pair 1 1)).correlatedFeasiblePayoffs
  apply Set.Subset.antisymm
  · rintro _ ⟨profile, rfl⟩
    exact FiniteStageGame.mixedPayoff_mem_correlatedFeasiblePayoffs _ profile
  · exact convexHull_min (lemma_1_pure_subset_D1 _) hconvex

theorem prisonersDilemma_E1_eq_singleton :
    prisonersDilemma.oneStageEquilibriumPayoffs = {pair 1 1} := by
  change (binaryGame (pair 4 4) (pair 0 5) (pair 5 0)
      (pair 1 1)).oneStageEquilibriumPayoffs =
    ({pair 1 1} : Set (Payoff Bool))
  apply Set.Subset.antisymm
  · rintro _ ⟨profile, hnash, rfl⟩
    change (Bool → PMF Bool) at profile
    change (binaryGame (pair 4 4) (pair 0 5) (pair 5 0)
      (pair 1 1)).mixedPayoff profile ∈ ({pair 1 1} : Set (Payoff Bool))
    change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
      (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
        (pair 1 1))).mixedExtension.IsNash profile at hnash
    have hrow := hnash false (PMF.pure true)
    have hcolumn := hnash true (PMF.pure true)
    rw [prisonersDilemma_mixedEU_false,
      prisonersDilemma_mixedEU_update_false] at hrow
    rw [prisonersDilemma_mixedEU_true,
      prisonersDilemma_mixedEU_update_true] at hcolumn
    norm_num at hrow hcolumn
    let p := (profile false true).toReal
    let q := (profile true true).toReal
    have hp1 : p ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    have hq1 : q ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    have hrow' : 1 ≤ p := by simpa [p] using hrow
    have hcolumn' : 1 ≤ q := by simpa [q] using hcolumn
    have hp : p = 1 := by linarith
    have hq : q = 1 := by linarith
    apply Set.mem_singleton_iff.mpr
    funext who
    cases who
    · change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
          (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
            (pair 1 1))).mixedExtension.eu profile false = _
      rw [prisonersDilemma_mixedEU_false]
      norm_num [p, q, hp, hq, pair]
    · change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
          (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
            (pair 1 1))).mixedExtension.eu profile true = _
      rw [prisonersDilemma_mixedEU_true]
      norm_num [p, q, hp, hq, pair]
  · rintro _ rfl
    let profile : Bool → PMF Bool := fun _ ↦ PMF.pure true
    refine ⟨profile, ?_, ?_⟩
    · change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
        (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
          (pair 1 1))).mixedExtension.IsNash profile
      intro who deviation
      change PMF Bool at deviation
      cases who
      · rw [prisonersDilemma_mixedEU_false,
          prisonersDilemma_mixedEU_update_false]
        norm_num [profile]
        exact ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
      · rw [prisonersDilemma_mixedEU_true,
          prisonersDilemma_mixedEU_update_true]
        norm_num [profile]
        exact ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    · funext who
      cases who
      · change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
            (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
              (pair 1 1))).mixedExtension.eu profile false = _
        rw [prisonersDilemma_mixedEU_false]
        norm_num [profile, pair]
      · change (KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
            (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0)
              (pair 1 1))).mixedExtension.eu profile true = _
        rw [prisonersDilemma_mixedEU_true]
        norm_num [profile, pair]

/-- The paper's explicit description of `Δ` for the Prisoner's Dilemma. -/
theorem prisonersDilemma_individualRationalLevel (who : Bool) :
    prisonersDilemma.individualRationalLevel who = 1 := by
  let K := KernelGame.ofPureEU (fun _ : Bool ↦ Bool)
    (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0) (pair 1 1))
  change (⨅ opponents : K.mixedExtension.OpponentProfile who,
      ⨆ action : Bool,
        K.mixedExtension.eu
          (K.mixedExtension.profileWithOpponent who (PMF.pure action) opponents)
          who) = 1
  have hlower (opponents : K.mixedExtension.OpponentProfile who) :
      1 ≤ ⨆ action : Bool,
        K.mixedExtension.eu
          (K.mixedExtension.profileWithOpponent who (PMF.pure action) opponents)
          who := by
    apply le_ciSup_of_le (Finite.bddAbove_range _) true
    let profile : Bool → PMF Bool :=
      K.mixedExtension.profileWithOpponent who (PMF.pure true) opponents
    change 1 ≤ K.mixedExtension.eu profile who
    cases who
    · rw [prisonersDilemma_mixedEU_false]
      have hp : (profile false true).toReal = 1 := by
        simp [profile, K]
      have hq := ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (profile true) true)
      rw [hp]
      norm_num at hq
      linarith
    · rw [prisonersDilemma_mixedEU_true]
      have hq : (profile true true).toReal = 1 := by
        simp [profile, K]
      have hp := ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (profile false) true)
      rw [hq]
      norm_num at hp
      linarith
  have hbelow : BddBelow (Set.range fun opponents :
      K.mixedExtension.OpponentProfile who ↦
        ⨆ action : Bool,
          K.mixedExtension.eu
            (K.mixedExtension.profileWithOpponent who (PMF.pure action) opponents)
            who) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨opponents, rfl⟩
    exact hlower opponents
  apply le_antisymm
  · let opponents : K.mixedExtension.OpponentProfile who :=
      fun _ ↦ PMF.pure true
    apply ciInf_le_of_le hbelow opponents
    apply ciSup_le
    intro action
    let profile : Bool → PMF Bool :=
      K.mixedExtension.profileWithOpponent who (PMF.pure action) opponents
    change K.mixedExtension.eu profile who ≤ 1
    cases who <;> cases action
    · rw [prisonersDilemma_mixedEU_false]
      simp [profile, K, opponents]
    · rw [prisonersDilemma_mixedEU_false]
      simp [profile, K, opponents]
    · rw [prisonersDilemma_mixedEU_true]
      simp [profile, K, opponents]
    · rw [prisonersDilemma_mixedEU_true]
      simp [profile, K, opponents]
  · letI : Nonempty (K.mixedExtension.OpponentProfile who) :=
      ⟨fun _ ↦ PMF.pure false⟩
    exact le_ciInf hlower

theorem prisonersDilemma_individuallyRationalPayoffs :
    prisonersDilemma.individuallyRationalPayoffs =
      prisonersDilemma.correlatedFeasiblePayoffs ∩
        {v | 1 ≤ v false ∧ 1 ≤ v true} := by
  ext v
  constructor
  · rintro ⟨hv, hlevel⟩
    refine ⟨hv, ?_⟩
    constructor
    · simpa [prisonersDilemma_individualRationalLevel] using hlevel false
    · simpa [prisonersDilemma_individualRationalLevel] using hlevel true
  · rintro ⟨hv, hfalse, htrue⟩
    refine ⟨hv, ?_⟩
    intro who
    rw [prisonersDilemma_individualRationalLevel]
    cases who
    · exact hfalse
    · exact htrue

/-- Since `D₁ = C`, every positive finite repetition has feasible set `C`. -/
theorem prisonersDilemma_Dn_eq_C :
    ∀ n, 0 < n → prisonersDilemma.finiteFeasiblePayoffs n =
      prisonersDilemma.correlatedFeasiblePayoffs := by
  intro n hn
  exact finiteFeasiblePayoffs_eq_correlated_of_oneStage_eq
    prisonersDilemma prisonersDilemma_D1_eq_C ⟨n, hn⟩

/-- Use a prescribed mixed action initially, then switch to the stagewise
security deviation after every nonempty history. -/
private noncomputable def firstThenSecurity
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) (first : PMF (G.Action who)) :
    G.BehaviorStrategy who :=
  fun time history =>
    if time = 0 then first else
      G.individualRationalDeviation profile who time history

private theorem expectedStagePayoff_zero_eq_mixedPayoff_initial
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) :
    G.repeatedGame.expectedStagePayoff profile G.repeatedInitial 0 who =
      G.mixedPayoff (G.initialMixedProfile profile) who := by
  have h := congrFun (finitePayoff_one_eq_mixedPayoff_initial G profile) who
  unfold FiniteStageGame.finitePayoff at h
  rw [G.repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff] at h
  simpa using h

private theorem expectedStagePayoff_firstThenSecurity_ge
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) (first : PMF (G.Action who))
    {time : ℕ} (htime : 0 < time) :
    G.individualRationalLevel who ≤
      G.repeatedGame.expectedStagePayoff
        (Function.update profile who
          (firstThenSecurity G profile who first))
        G.repeatedInitial time who := by
  letI (player : G.Player) : Finite (G.repeatedGame.Act player) :=
    @Finite.of_fintype _ (G.finiteAction player)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  unfold StochasticGame.expectedStagePayoff
  rw [← Math.Probability.expect_const
    (G.repeatedGame.histDist
      (Function.update profile who
        (firstThenSecurity G profile who first))
      G.repeatedInitial time) (G.individualRationalLevel who)]
  apply Math.Probability.expect_mono
  intro history
  have hstage :
      G.repeatedGame.stageEUAt
          (Function.update profile who
            (firstThenSecurity G profile who first)) history who =
        G.repeatedGame.stageEUAt
          (Function.update profile who
            (G.individualRationalDeviation profile who)) history who := by
    unfold StochasticGame.stageEUAt StochasticGame.stageActionDist
    congr 1
    apply congrArg Math.PMFProduct.pmfPi
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [firstThenSecurity, Nat.ne_of_gt htime]
    · simp [Function.update_of_ne hplayer]
  rw [hstage]
  exact stageEUAt_individualRationalDeviation_ge G profile who history

/-- Proposition 13's backward-induction core: every positive finite-horizon
Nash profile has the unique one-stage equilibrium payoff `a`. -/
private theorem finitePayoff_eq_of_unique_security
    (G : FiniteStageGame) (a : Payoff G.Player)
    (hsecurity : ∀ who, G.individualRationalLevel who = a who)
    (hunique : G.oneStageEquilibriumPayoffs = {a}) :
    ∀ k (profile : G.BehaviorProfile),
      G.repeatedGame.IsεHorizonNash G.repeatedInitial (k + 1) 0 profile →
        G.finitePayoff (k + 1) profile = a := by
  letI (player : G.Player) : Fintype (G.kernel.Strategy player) := by
    change Fintype (G.Action player)
    infer_instance
  intro k
  induction k with
  | zero =>
      intro profile hnash
      have hmem : G.finitePayoff 1 profile ∈
          G.finiteEquilibriumPayoffs 1 := ⟨profile, by simpa using hnash, rfl⟩
      rw [finiteEquilibriumPayoffs_one_eq_oneStageEquilibriumPayoffs,
        hunique] at hmem
      exact Set.mem_singleton_iff.mp hmem
  | succ k ih =>
      intro profile hnash
      let tailLength := k + 1
      have hhorizon : k + 1 + 1 = 1 + tailLength := by
        simp [tailLength, Nat.add_comm]
      have hnash' : G.repeatedGame.IsεHorizonNash G.repeatedInitial
          (1 + tailLength) 0 profile := by
        rwa [← hhorizon]
      have htail (base : G.repeatedGame.Hist 1)
          (hbase : base ∈
            (G.repeatedGame.histDist profile G.repeatedInitial 1).support) :
          G.finitePayoff tailLength
              (G.repeatedGame.afterHistoryProfile profile base) = a := by
        apply ih
        exact G.kernel
          |>.realizedAction_afterHistoryProfile_isHorizonNash_of_mem_support
            profile hnash' base hbase
      have htailTotal (who : G.Player) :
          (∑ time ∈ Finset.range tailLength,
              G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
                (1 + time) who) =
            (tailLength : ℝ) * a who := by
        simp_rw [expectedStagePayoff_add_eq_expect_afterHistory]
        rw [sum_expect_comm_range]
        calc
          Math.Probability.expect
              (G.repeatedGame.histDist profile G.repeatedInitial 1)
              (fun base => ∑ time ∈ Finset.range tailLength,
                G.repeatedGame.expectedStagePayoff
                  (G.repeatedGame.afterHistoryProfile profile base)
                  base.2 time who) =
              Math.Probability.expect
                (G.repeatedGame.histDist profile G.repeatedInitial 1)
                (fun _ => (tailLength : ℝ) * a who) := by
            apply Math.ProbabilityMassFunction.expect_congr_on_support
            intro base hbase
            have hweighted := congrFun
              (cast_smul_finitePayoff_eq_sum G tailLength
                (G.repeatedGame.afterHistoryProfile profile base)) who
            simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hweighted
            cases base.2
            rw [← hweighted, htail base hbase]
          _ = (tailLength : ℝ) * a who :=
            Math.Probability.expect_const _ _
      let current := G.initialMixedProfile profile
      have hcurrentNash : G.kernel.mixedExtension.IsNash current := by
        intro who first
        let rootDeviation := firstThenSecurity G profile who first
        let deviated := Function.update profile who rootDeviation
        have hroot := hnash who rootDeviation
        simp only [add_zero] at hroot
        have hscaled := mul_le_mul_of_nonneg_left hroot
          (by positivity : (0 : ℝ) ≤ k + 1 + 1)
        have hdeviated := congrFun
          (cast_smul_finitePayoff_eq_sum G (k + 1 + 1) deviated) who
        have horiginal := congrFun
          (cast_smul_finitePayoff_eq_sum G (k + 1 + 1) profile) who
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hdeviated
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at horiginal
        have hscaled' : ((k + 1 + 1 : ℕ) : ℝ) *
              G.finitePayoff (k + 1 + 1) deviated who ≤
            ((k + 1 + 1 : ℕ) : ℝ) *
              G.finitePayoff (k + 1 + 1) profile who := by
          change ((k + 1 + 1 : ℕ) : ℝ) *
                G.repeatedGame.finiteAveragePayoff G.repeatedInitial
                  (k + 1 + 1) deviated who ≤
              ((k + 1 + 1 : ℕ) : ℝ) *
                G.repeatedGame.finiteAveragePayoff G.repeatedInitial
                  (k + 1 + 1) profile who
          norm_num [Nat.cast_add, deviated, rootDeviation] at hscaled ⊢
          exact hscaled
        rw [hdeviated, horiginal] at hscaled'
        have horiginalTotal :
            (∑ time ∈ Finset.range (k + 1 + 1),
                G.repeatedGame.expectedStagePayoff profile
                  G.repeatedInitial time who) =
              G.mixedPayoff current who + (tailLength : ℝ) * a who := by
          rw [show k + 1 + 1 = tailLength + 1 by simp [tailLength],
            Finset.sum_range_succ']
          rw [expectedStagePayoff_zero_eq_mixedPayoff_initial,
            show (∑ time ∈ Finset.range tailLength,
              G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
                (time + 1) who) = (tailLength : ℝ) * a who by
                simpa [Nat.add_comm] using htailTotal who]
          dsimp only [current]
          ring
        have hdeviatedLower :
            G.mixedPayoff (Function.update current who first) who +
                (tailLength : ℝ) * a who ≤
              ∑ time ∈ Finset.range (k + 1 + 1),
                G.repeatedGame.expectedStagePayoff deviated
                  G.repeatedInitial time who := by
          have hfirst :
              G.mixedPayoff (Function.update current who first) who ≤
                G.repeatedGame.expectedStagePayoff deviated
                  G.repeatedInitial 0 who := by
            rw [expectedStagePayoff_zero_eq_mixedPayoff_initial]
            have hinitial : G.initialMixedProfile deviated =
                Function.update current who first := by
              funext player
              by_cases hplayer : player = who
              · subst player
                simp [FiniteStageGame.initialMixedProfile, deviated,
                  rootDeviation, firstThenSecurity, current]
              · simp [FiniteStageGame.initialMixedProfile, deviated,
                  hplayer, current]
            rw [hinitial]
          have hlater : (tailLength : ℝ) * a who ≤
              ∑ time ∈ Finset.range tailLength,
                G.repeatedGame.expectedStagePayoff deviated
                  G.repeatedInitial (time + 1) who := by
            calc
              (tailLength : ℝ) * a who =
                  ∑ _time ∈ Finset.range tailLength, a who := by simp
              _ ≤ _ := by
                apply Finset.sum_le_sum
                intro time _
                have hstage := expectedStagePayoff_firstThenSecurity_ge
                  G profile who first (time := time + 1) (by omega)
                rw [hsecurity who] at hstage
                simpa [deviated, rootDeviation, Nat.add_comm] using hstage
          calc
            G.mixedPayoff (Function.update current who first) who +
                (tailLength : ℝ) * a who ≤
              G.repeatedGame.expectedStagePayoff deviated
                  G.repeatedInitial 0 who +
                ∑ time ∈ Finset.range tailLength,
                  G.repeatedGame.expectedStagePayoff deviated
                    G.repeatedInitial (time + 1) who :=
              add_le_add hfirst hlater
            _ = _ := by
              rw [show k + 1 + 1 = tailLength + 1 by simp [tailLength]]
              calc
                _ = (∑ time ∈ Finset.range tailLength,
                      G.repeatedGame.expectedStagePayoff deviated
                        G.repeatedInitial (time + 1) who) +
                    G.repeatedGame.expectedStagePayoff deviated
                      G.repeatedInitial 0 who := add_comm _ _
                _ = _ := (Finset.sum_range_succ'
                  (fun time => G.repeatedGame.expectedStagePayoff deviated
                    G.repeatedInitial time who) tailLength).symm
        rw [horiginalTotal] at hscaled'
        exact le_of_add_le_add_right (hdeviatedLower.trans hscaled')
      have hcurrentPayoff : G.mixedPayoff current = a := by
        have hmem : G.mixedPayoff current ∈ G.oneStageEquilibriumPayoffs :=
          ⟨current, hcurrentNash, rfl⟩
        rw [hunique] at hmem
        exact Set.mem_singleton_iff.mp hmem
      funext who
      unfold FiniteStageGame.finitePayoff
      rw [G.repeatedGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
      rw [show k + 1 + 1 = tailLength + 1 by simp [tailLength],
        Finset.sum_range_succ']
      rw [expectedStagePayoff_zero_eq_mixedPayoff_initial,
        hcurrentPayoff]
      rw [show (∑ time ∈ Finset.range tailLength,
          G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
            (time + 1) who) = (tailLength : ℝ) * a who by
        simpa [Nat.add_comm] using htailTotal who]
      have hpositive : (0 : ℝ) < tailLength + 1 := by positivity
      field_simp
      push_cast
      ring

/-! Proposition 13 is a backward last-deviation argument.  Here `a` is the
security-level vector recalled immediately before the proposition in the
paper; uniqueness of the one-stage equilibrium payoff alone is insufficient.
Positive-probability continuations inherit Nash optimality, while the
security strategy controls continuations reached only by a deviation. -/
theorem proposition_13 (G : FiniteStageGame) (a : Payoff G.Player)
    (hsecurity : ∀ who, G.individualRationalLevel who = a who)
    (hunique : G.oneStageEquilibriumPayoffs = {a}) :
    ∀ n, 0 < n → G.finiteEquilibriumPayoffs n = {a} := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  apply Set.Subset.antisymm
  · rintro payoff ⟨profile, hnash, rfl⟩
    rw [finitePayoff_eq_of_unique_security G a hsecurity hunique k profile hnash]
    exact Set.mem_singleton a
  · rintro payoff hpayoff
    rw [Set.mem_singleton_iff] at hpayoff
    subst payoff
    obtain ⟨profile, hnash, hpayoff⟩ :=
      lemma_1_E1_subset_En G ⟨k + 1, by omega⟩
        (by rw [hunique]; exact Set.mem_singleton a)
    exact ⟨profile, hnash, hpayoff⟩

/-! The paper reports Benoit--Krishna's converse for two players: unless the
one-stage equilibrium-payoff set is a singleton, the finite-horizon
equilibrium-payoff sets converge to `Δ`. The cited theorem is not proved in
this paper. -/
theorem benoit_krishna_reported_converse :
  ∀ (G : FiniteStageGame), Fintype.card G.Player = 2 →
    (∀ a, G.oneStageEquilibriumPayoffs ≠ {a}) →
    HausdorffConvergesAtTop G.finiteEquilibriumPayoffs
      G.individuallyRationalPayoffs := by
  sorry

/-- Every finite repetition of the Prisoner's Dilemma has only `(1,1)`. -/
theorem prisonersDilemma_En_eq_singleton :
    ∀ n, 0 < n →
      prisonersDilemma.finiteEquilibriumPayoffs n = {pair 1 1} := by
  intro n hn
  exact proposition_13 prisonersDilemma (pair 1 1)
    (fun who => by
      rw [prisonersDilemma_individualRationalLevel]
      cases who <;> rfl)
    prisonersDilemma_E1_eq_singleton n hn

/-- Keep the prescribed strategy before `start`, then play one fixed action. -/
private abbrev monitoredMixedProfileAt
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    {time : ℕ} (history : G.repeatedGame.Hist time) : G.MixedProfile :=
  fun player =>
    (GameTheory.KernelGame.RealizedActionRepeatedAdapter.toMonitoredProfile
      G.kernel profile) player time
        (GameTheory.KernelGame.RealizedActionRepeatedAdapter.actionHistory
          G.kernel history)

@[simp] private theorem monitoredMixedProfileAt_apply
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    {time : ℕ} (history : G.repeatedGame.Hist time) (player : G.Player) :
    monitoredMixedProfileAt G profile history player =
      profile player time history := by
  simp [monitoredMixedProfileAt,
    GameTheory.KernelGame.RealizedActionRepeatedAdapter.toMonitoredProfile,
    GameTheory.KernelGame.RealizedActionRepeatedAdapter.toMonitoredStrategy]

private theorem stageEUAt_eq_monitoredMixedProfileAt
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    {time : ℕ} (history : G.repeatedGame.Hist time) (who : G.Player) :
    G.repeatedGame.stageEUAt profile history who =
      G.kernel.mixedExtension.eu
        (monitoredMixedProfileAt G profile history) who := by
  letI : Finite G.kernel.Outcome := by
    change Finite (∀ player, G.Action player)
    exact Finite.of_fintype _
  let monitored :=
    GameTheory.KernelGame.RealizedActionRepeatedAdapter.toMonitoredProfile
      G.kernel profile
  rw [← GameTheory.KernelGame.RealizedActionRepeatedAdapter.toBehaviorProfile_toMonitoredProfile
    G.kernel profile]
  exact GameTheory.KernelGame.RealizedActionRepeatedAdapter.stageEUAt_toBehaviorProfile
    G.kernel monitored history who

private noncomputable abbrev prisonersDilemmaMixedProfileAt
    (profile : prisonersDilemma.BehaviorProfile)
    {time : ℕ} (history : prisonersDilemma.repeatedGame.Hist time) :
    Bool → PMF Bool :=
  fun player => by
    exact monitoredMixedProfileAt prisonersDilemma profile history player

private theorem prisonersDilemma_stageEUAt_eq_mixedEU
    (profile : prisonersDilemma.BehaviorProfile)
    {time : ℕ} (history : prisonersDilemma.repeatedGame.Hist time)
    (who : Bool) :
    prisonersDilemma.repeatedGame.stageEUAt profile history who =
      (KernelGame.ofPureEU (fun _ : Bool => Bool)
        (binaryPayoff (pair 4 4) (pair 0 5) (pair 5 0) (pair 1 1))).mixedExtension.eu
          (prisonersDilemmaMixedProfileAt profile history) who := by
  rw [stageEUAt_eq_monitoredMixedProfileAt]

/-- Keep the prescribed strategy before `start`, then play one fixed action. -/
private noncomputable def constantActionFrom
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) (start : ℕ) (action : G.Action who) :
    G.BehaviorStrategy who :=
  fun time history =>
    if time < start then profile who time history else PMF.pure action

private theorem update_constantActionFrom_agreeBefore
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (who : G.Player) (start : ℕ) (action : G.Action who) :
    G.repeatedGame.ProfilesAgreeBefore
      (Function.update profile who
        (constantActionFrom G profile who start action))
      profile start := by
  intro player time history htime
  by_cases hplayer : player = who
  · subst player
    simp [constantActionFrom, htime]
  · simp [Function.update_of_ne hplayer]

/-- In the Prisoner's Dilemma, permanent defection from `start` earns at
least one in every stage from `start` onward. -/
private theorem expectedStagePayoff_constantTrueFrom_ge_one
    (profile : prisonersDilemma.BehaviorProfile) (who : Bool)
    (start time : ℕ) (htime : start ≤ time) :
    1 ≤ prisonersDilemma.repeatedGame.expectedStagePayoff
      (Function.update profile who
        (constantActionFrom prisonersDilemma profile who start true))
      prisonersDilemma.repeatedInitial time who := by
  letI (player : Bool) : Finite (prisonersDilemma.repeatedGame.Act player) :=
    @Finite.of_fintype _ (prisonersDilemma.finiteAction player)
  letI (player : Bool) : DecidableEq
      (prisonersDilemma.repeatedGame.Act player) :=
    prisonersDilemma.decidableAction player
  letI : Finite prisonersDilemma.repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  unfold StochasticGame.expectedStagePayoff
  rw [← Math.Probability.expect_const
    (prisonersDilemma.repeatedGame.histDist
      (Function.update profile who
        (constantActionFrom prisonersDilemma profile who start true))
      prisonersDilemma.repeatedInitial time) 1]
  apply Math.Probability.expect_mono
  intro history
  let deviated := Function.update profile who
    (constantActionFrom prisonersDilemma profile who start true)
  let current := prisonersDilemmaMixedProfileAt profile history
  have hstage : prisonersDilemma.repeatedGame.stageEUAt
      deviated history who =
      prisonersDilemma.kernel.mixedExtension.eu
        (Function.update current who (PMF.pure true)) who := by
    rw [prisonersDilemma_stageEUAt_eq_mixedEU]
    congr 1
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [deviated, current, prisonersDilemmaMixedProfileAt,
        monitoredMixedProfileAt_apply, constantActionFrom,
        Nat.not_lt.mpr htime]
      rfl
    · simp [deviated, current, prisonersDilemmaMixedProfileAt,
        monitoredMixedProfileAt_apply, Function.update_of_ne hplayer]
  change 1 ≤ prisonersDilemma.repeatedGame.stageEUAt deviated history who
  rw [hstage]
  cases who
  · rw [prisonersDilemma_mixedEU_update_false_pure]
    have hq := ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (current true) true)
    have hq' : (current true true).toReal ≤ 1 := by simpa using hq
    linarith
  · rw [prisonersDilemma_mixedEU_update_true_pure]
    have hp := ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (current false) true)
    have hp' : (current false true).toReal ≤ 1 := by simpa using hp
    linarith

/-- The paper's `γ̄ₙ = ℙ[aₙ+bₙ-2]`, the expected aggregate surplus
over mutual defection in period `time`. -/
private noncomputable def prisonersDilemmaCooperationMass
    (profile : prisonersDilemma.BehaviorProfile) (time : ℕ) : ℝ :=
  prisonersDilemma.repeatedGame.expectedStagePayoff profile
      prisonersDilemma.repeatedInitial time false +
    prisonersDilemma.repeatedGame.expectedStagePayoff profile
      prisonersDilemma.repeatedInitial time true - 2

/-- In one period, aggregate surplus is three times the sum of the two
players' gains from switching that period to their dominant action. -/
private theorem prisonersDilemmaCooperationMass_eq_three_mul_deviationGain
    (profile : prisonersDilemma.BehaviorProfile) (time : ℕ) :
    prisonersDilemmaCooperationMass profile time = 3 *
      ((prisonersDilemma.repeatedGame.expectedStagePayoff
          (Function.update profile false
            (constantActionFrom prisonersDilemma profile false time true))
          prisonersDilemma.repeatedInitial time false -
        prisonersDilemma.repeatedGame.expectedStagePayoff profile
          prisonersDilemma.repeatedInitial time false) +
       (prisonersDilemma.repeatedGame.expectedStagePayoff
          (Function.update profile true
            (constantActionFrom prisonersDilemma profile true time true))
          prisonersDilemma.repeatedInitial time true -
        prisonersDilemma.repeatedGame.expectedStagePayoff profile
          prisonersDilemma.repeatedInitial time true)) := by
  letI (player : Bool) : Finite (prisonersDilemma.repeatedGame.Act player) :=
    @Finite.of_fintype _ (prisonersDilemma.finiteAction player)
  letI (player : Bool) : DecidableEq
      (prisonersDilemma.repeatedGame.Act player) :=
    prisonersDilemma.decidableAction player
  letI : Finite prisonersDilemma.repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  let rowDeviated := Function.update profile false
    (constantActionFrom prisonersDilemma profile false time true)
  let columnDeviated := Function.update profile true
    (constantActionFrom prisonersDilemma profile true time true)
  let law := prisonersDilemma.repeatedGame.histDist profile
    prisonersDilemma.repeatedInitial time
  have hrowLaw : prisonersDilemma.repeatedGame.histDist rowDeviated
      prisonersDilemma.repeatedInitial time = law := by
    exact prisonersDilemma.repeatedGame.histDist_eq_of_profilesAgreeBefore
      (update_constantActionFrom_agreeBefore prisonersDilemma profile
        false time true) time le_rfl
  have hcolumnLaw : prisonersDilemma.repeatedGame.histDist columnDeviated
      prisonersDilemma.repeatedInitial time = law := by
    exact prisonersDilemma.repeatedGame.histDist_eq_of_profilesAgreeBefore
      (update_constantActionFrom_agreeBefore prisonersDilemma profile
        true time true) time le_rfl
  unfold prisonersDilemmaCooperationMass StochasticGame.expectedStagePayoff
  change Math.Probability.expect law
      (fun history => prisonersDilemma.repeatedGame.stageEUAt profile history false) +
      Math.Probability.expect law
        (fun history => prisonersDilemma.repeatedGame.stageEUAt profile history true) - 2 = _
  change _ = 3 *
    ((Math.Probability.expect
          (prisonersDilemma.repeatedGame.histDist rowDeviated
            prisonersDilemma.repeatedInitial time)
          (fun history => prisonersDilemma.repeatedGame.stageEUAt
            rowDeviated history false) -
        Math.Probability.expect law
          (fun history => prisonersDilemma.repeatedGame.stageEUAt
            profile history false)) +
      (Math.Probability.expect
          (prisonersDilemma.repeatedGame.histDist columnDeviated
            prisonersDilemma.repeatedInitial time)
          (fun history => prisonersDilemma.repeatedGame.stageEUAt
            columnDeviated history true) -
        Math.Probability.expect law
          (fun history => prisonersDilemma.repeatedGame.stageEUAt
            profile history true)))
  rw [hrowLaw, hcolumnLaw]
  rw [← Math.Probability.expect_add, ← Math.Probability.expect_sub,
    ← Math.Probability.expect_sub, ← Math.Probability.expect_add,
    ← Math.Probability.expect_const law 2,
    ← Math.Probability.expect_const_mul]
  rw [← Math.Probability.expect_sub]
  apply congrArg (Math.Probability.expect law)
  funext history
  let current := prisonersDilemmaMixedProfileAt profile history
  have hrow : prisonersDilemma.repeatedGame.stageEUAt
      rowDeviated history false =
      prisonersDilemma.kernel.mixedExtension.eu
        (Function.update current false (PMF.pure true)) false := by
    rw [prisonersDilemma_stageEUAt_eq_mixedEU]
    congr 1
    funext player
    by_cases hplayer : player = false
    · subst player
      simp [rowDeviated, prisonersDilemmaMixedProfileAt,
        monitoredMixedProfileAt_apply, constantActionFrom]
      rfl
    · simp [rowDeviated, current, prisonersDilemmaMixedProfileAt,
        monitoredMixedProfileAt_apply, Function.update_of_ne hplayer]
  have hcolumn : prisonersDilemma.repeatedGame.stageEUAt
      columnDeviated history true =
      prisonersDilemma.kernel.mixedExtension.eu
        (Function.update current true (PMF.pure true)) true := by
    rw [prisonersDilemma_stageEUAt_eq_mixedEU]
    congr 1
    funext player
    by_cases hplayer : player = true
    · subst player
      simp [columnDeviated, prisonersDilemmaMixedProfileAt,
        monitoredMixedProfileAt_apply, constantActionFrom]
      rfl
    · simp [columnDeviated, current, prisonersDilemmaMixedProfileAt,
        monitoredMixedProfileAt_apply, Function.update_of_ne hplayer]
  have horiginal (who : Bool) :
      prisonersDilemma.repeatedGame.stageEUAt profile history who =
        prisonersDilemma.kernel.mixedExtension.eu current who := by
    exact prisonersDilemma_stageEUAt_eq_mixedEU profile history who
  rw [hrow, hcolumn, horiginal false, horiginal true,
    prisonersDilemma_mixedEU_false,
    prisonersDilemma_mixedEU_true]
  rw [prisonersDilemma_mixedEU_update_false_pure,
    prisonersDilemma_mixedEU_update_true_pure]
  ring

/-- The cooperation mass lies in `[0,6]`: it is three times the total
probability of Top and Left. -/
private theorem prisonersDilemmaCooperationMass_mem_Icc
    (profile : prisonersDilemma.BehaviorProfile) (time : ℕ) :
    prisonersDilemmaCooperationMass profile time ∈ Set.Icc 0 6 := by
  letI (player : Bool) : Finite (prisonersDilemma.repeatedGame.Act player) :=
    @Finite.of_fintype _ (prisonersDilemma.finiteAction player)
  letI : Finite prisonersDilemma.repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  let law := prisonersDilemma.repeatedGame.histDist profile
    prisonersDilemma.repeatedInitial time
  have hpointwise (history : prisonersDilemma.repeatedGame.Hist time) :
      0 ≤ prisonersDilemma.repeatedGame.stageEUAt profile history false +
          prisonersDilemma.repeatedGame.stageEUAt profile history true - 2 ∧
        prisonersDilemma.repeatedGame.stageEUAt profile history false +
          prisonersDilemma.repeatedGame.stageEUAt profile history true - 2 ≤ 6 := by
    let current := prisonersDilemmaMixedProfileAt profile history
    have horiginal (who : Bool) :
        prisonersDilemma.repeatedGame.stageEUAt profile history who =
          prisonersDilemma.kernel.mixedExtension.eu current who := by
      exact prisonersDilemma_stageEUAt_eq_mixedEU profile history who
    rw [horiginal false, horiginal true,
      prisonersDilemma_mixedEU_false, prisonersDilemma_mixedEU_true]
    have hp0 : 0 ≤ (current false true).toReal := ENNReal.toReal_nonneg
    have hq0 : 0 ≤ (current true true).toReal := ENNReal.toReal_nonneg
    have hp1 : (current false true).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    have hq1 : (current true true).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    constructor <;> linarith
  unfold prisonersDilemmaCooperationMass StochasticGame.expectedStagePayoff
  change Math.Probability.expect law
      (fun history => prisonersDilemma.repeatedGame.stageEUAt profile history false) +
      Math.Probability.expect law
        (fun history => prisonersDilemma.repeatedGame.stageEUAt profile history true) - 2
      ∈ Set.Icc 0 6
  rw [← Math.Probability.expect_add,
    ← Math.Probability.expect_const law 2,
    ← Math.Probability.expect_sub]
  constructor
  · rw [← Math.Probability.expect_const law 0]
    apply Math.Probability.expect_mono
    exact fun history => (hpointwise history).1
  · rw [← Math.Probability.expect_const law 6]
    apply Math.Probability.expect_mono
    exact fun history => (hpointwise history).2

/-- A root discounted Nash inequality can be cancelled through any
deterministic prefix on which the deviation agrees with the profile. -/
private theorem discountedTail_le_of_nash_of_agreeBefore
    (G : FiniteStageGame) (profile : G.BehaviorProfile)
    (hnash : G.repeatedGame.IsDiscountedεNash
      (1 - (lam : ℝ)) G.repeatedInitial 0 profile)
    (who : G.Player) (deviation : G.BehaviorStrategy who) (start : ℕ)
    (hagree : G.repeatedGame.ProfilesAgreeBefore
      (Function.update profile who deviation) profile start)
    (hlam : 0 < lam) (hlam1 : lam < 1) :
    (∑' offset : ℕ, (1 - lam) ^ offset *
        G.repeatedGame.expectedStagePayoff
          (Function.update profile who deviation) G.repeatedInitial
          (start + offset) who) ≤
      ∑' offset : ℕ, (1 - lam) ^ offset *
        G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
          (start + offset) who := by
  let beta := 1 - lam
  let deviated := Function.update profile who deviation
  have hbeta0 : 0 ≤ beta := by dsimp only [beta]; linarith
  have hbeta1 : beta < 1 := by dsimp only [beta]; linarith
  obtain ⟨bound, hbound⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun data : G.repeatedGame.State × G.repeatedGame.JointAct =>
      G.repeatedGame.stagePayoff data.1 data.2 who)
  have horiginalSummable : Summable fun time : ℕ =>
      beta ^ time * G.repeatedGame.expectedStagePayoff
        profile G.repeatedInitial time who :=
    G.repeatedGame.summable_discounted_expectedStagePayoff
      (fun state action => hbound (state, action)) profile G.repeatedInitial
      (by simpa [abs_of_nonneg hbeta0] using hbeta1)
  have hdeviatedSummable : Summable fun time : ℕ =>
      beta ^ time * G.repeatedGame.expectedStagePayoff
        deviated G.repeatedInitial time who :=
    G.repeatedGame.summable_discounted_expectedStagePayoff
      (fun state action => hbound (state, action)) deviated G.repeatedInitial
      (by simpa [abs_of_nonneg hbeta0] using hbeta1)
  have hnash' := hnash who deviation
  simp only [add_zero] at hnash'
  unfold StochasticGame.discountedPayoff at hnash'
  rw [show 1 - (1 - lam) = lam by ring] at hnash'
  change lam * (∑' time : ℕ, beta ^ time *
      G.repeatedGame.expectedStagePayoff profile G.repeatedInitial time who) ≥
    lam * (∑' time : ℕ, beta ^ time *
      G.repeatedGame.expectedStagePayoff deviated G.repeatedInitial time who) at hnash'
  have htotal : (∑' time : ℕ, beta ^ time *
      G.repeatedGame.expectedStagePayoff deviated G.repeatedInitial time who) ≤
    ∑' time : ℕ, beta ^ time *
      G.repeatedGame.expectedStagePayoff profile G.repeatedInitial time who := by
    nlinarith
  have hprefix :
      (∑ time ∈ Finset.range start, beta ^ time *
          G.repeatedGame.expectedStagePayoff deviated
            G.repeatedInitial time who) =
        ∑ time ∈ Finset.range start, beta ^ time *
          G.repeatedGame.expectedStagePayoff profile
            G.repeatedInitial time who := by
    apply Finset.sum_congr rfl
    intro time htime
    rw [expectedStagePayoff_eq_of_profilesAgreeBefore G hagree
      (Finset.mem_range.mp htime) who]
  have htailsWeighted :
      (∑' offset : ℕ, beta ^ (offset + start) *
          G.repeatedGame.expectedStagePayoff deviated
            G.repeatedInitial (offset + start) who) ≤
        ∑' offset : ℕ, beta ^ (offset + start) *
          G.repeatedGame.expectedStagePayoff profile
            G.repeatedInitial (offset + start) who := by
    rw [← hdeviatedSummable.sum_add_tsum_nat_add start,
      ← horiginalSummable.sum_add_tsum_nat_add start] at htotal
    rw [hprefix] at htotal
    linarith
  have hfactor (selected : G.BehaviorProfile) :
      (∑' offset : ℕ, beta ^ (offset + start) *
          G.repeatedGame.expectedStagePayoff selected
            G.repeatedInitial (offset + start) who) =
        beta ^ start *
          ∑' offset : ℕ, beta ^ offset *
            G.repeatedGame.expectedStagePayoff selected
              G.repeatedInitial (start + offset) who := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro offset
    rw [add_comm offset start, pow_add]
    ring
  rw [hfactor deviated, hfactor profile] at htailsWeighted
  have hbetaPow : 0 < beta ^ start := by
    positivity
  nlinarith

/-- Nash's inequality against permanent defection bounds the current gain by
the discounted future aggregate surplus above the security payoff one. -/
private theorem prisonersDilemma_deviationGain_le_futureSurplus
    (profile : prisonersDilemma.BehaviorProfile)
    (hnash : prisonersDilemma.repeatedGame.IsDiscountedεNash
      (1 - lam) prisonersDilemma.repeatedInitial 0 profile)
    (who : Bool) (start : ℕ) (hlam : 0 < lam) (hlam1 : lam < 1) :
    prisonersDilemma.repeatedGame.expectedStagePayoff
        (Function.update profile who
          (constantActionFrom prisonersDilemma profile who start true))
        prisonersDilemma.repeatedInitial start who -
      prisonersDilemma.repeatedGame.expectedStagePayoff profile
        prisonersDilemma.repeatedInitial start who ≤
      ∑' offset : ℕ, (1 - lam) ^ (offset + 1) *
        (prisonersDilemma.repeatedGame.expectedStagePayoff profile
          prisonersDilemma.repeatedInitial (start + (offset + 1)) who - 1) := by
  letI (player : Bool) : Finite (prisonersDilemma.repeatedGame.Act player) :=
    @Finite.of_fintype _ (prisonersDilemma.finiteAction player)
  letI : Finite prisonersDilemma.repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  let beta := 1 - lam
  let deviation := constantActionFrom prisonersDilemma profile who start true
  let deviated := Function.update profile who deviation
  have hbeta0 : 0 ≤ beta := by dsimp only [beta]; linarith
  have hbeta1 : beta < 1 := by dsimp only [beta]; linarith
  have htail := discountedTail_le_of_nash_of_agreeBefore
    prisonersDilemma profile hnash who deviation start
      (update_constantActionFrom_agreeBefore prisonersDilemma profile
        who start true) hlam hlam1
  change (∑' offset : ℕ, beta ^ offset *
      prisonersDilemma.repeatedGame.expectedStagePayoff deviated
        prisonersDilemma.repeatedInitial (start + offset) who) ≤
    ∑' offset : ℕ, beta ^ offset *
      prisonersDilemma.repeatedGame.expectedStagePayoff profile
        prisonersDilemma.repeatedInitial (start + offset) who at htail
  obtain ⟨bound, hbound⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun data : prisonersDilemma.repeatedGame.State ×
        prisonersDilemma.repeatedGame.JointAct =>
      prisonersDilemma.repeatedGame.stagePayoff data.1 data.2 who)
  have horiginalSummable : Summable fun offset : ℕ =>
      beta ^ offset * prisonersDilemma.repeatedGame.expectedStagePayoff
        profile prisonersDilemma.repeatedInitial (start + offset) who := by
    apply summable_pow_mul_of_abs_le
      (by simpa [abs_of_nonneg hbeta0] using hbeta1)
    intro offset
    exact prisonersDilemma.repeatedGame.abs_expectedStagePayoff_le
      (fun state action => hbound (state, action)) profile
      prisonersDilemma.repeatedInitial (start + offset)
  have hdeviatedSummable : Summable fun offset : ℕ =>
      beta ^ offset * prisonersDilemma.repeatedGame.expectedStagePayoff
        deviated prisonersDilemma.repeatedInitial (start + offset) who := by
    apply summable_pow_mul_of_abs_le
      (by simpa [abs_of_nonneg hbeta0] using hbeta1)
    intro offset
    exact prisonersDilemma.repeatedGame.abs_expectedStagePayoff_le
      (fun state action => hbound (state, action)) deviated
      prisonersDilemma.repeatedInitial (start + offset)
  rw [horiginalSummable.tsum_eq_zero_add,
    hdeviatedSummable.tsum_eq_zero_add] at htail
  simp only [pow_zero, one_mul, Nat.add_zero] at htail
  have hfutureDeviation :
      (∑' offset : ℕ, beta ^ (offset + 1)) ≤
        ∑' offset : ℕ, beta ^ (offset + 1) *
          prisonersDilemma.repeatedGame.expectedStagePayoff deviated
            prisonersDilemma.repeatedInitial (start + (offset + 1)) who := by
    have hgeom : Summable fun offset : ℕ => beta ^ (offset + 1) := by
      simpa [pow_succ'] using
        (summable_geometric_of_lt_one hbeta0 hbeta1).mul_left beta
    have hdev : Summable fun offset : ℕ => beta ^ (offset + 1) *
        prisonersDilemma.repeatedGame.expectedStagePayoff deviated
          prisonersDilemma.repeatedInitial (start + (offset + 1)) who :=
      hdeviatedSummable.comp_injective Nat.succ_injective
    exact hgeom.tsum_le_tsum (fun offset => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (expectedStagePayoff_constantTrueFrom_ge_one
          profile who start (start + (offset + 1)) (by omega))
        (pow_nonneg hbeta0 (offset + 1))) hdev
  have horiginalFuture : Summable fun offset : ℕ =>
      beta ^ (offset + 1) *
        prisonersDilemma.repeatedGame.expectedStagePayoff profile
          prisonersDilemma.repeatedInitial (start + (offset + 1)) who :=
    horiginalSummable.comp_injective Nat.succ_injective
  have hgeomFuture : Summable fun offset : ℕ => beta ^ (offset + 1) := by
    simpa [pow_succ'] using
      (summable_geometric_of_lt_one hbeta0 hbeta1).mul_left beta
  have hdifference :
      (∑' offset : ℕ, beta ^ (offset + 1) *
        (prisonersDilemma.repeatedGame.expectedStagePayoff profile
          prisonersDilemma.repeatedInitial (start + (offset + 1)) who - 1)) =
      (∑' offset : ℕ, beta ^ (offset + 1) *
        prisonersDilemma.repeatedGame.expectedStagePayoff profile
          prisonersDilemma.repeatedInitial (start + (offset + 1)) who) -
        ∑' offset : ℕ, beta ^ (offset + 1) := by
    rw [← horiginalFuture.tsum_sub hgeomFuture]
    apply tsum_congr
    intro offset
    ring
  change _ ≤ (∑' offset : ℕ, beta ^ (offset + 1) *
    (prisonersDilemma.repeatedGame.expectedStagePayoff profile
      prisonersDilemma.repeatedInitial (start + (offset + 1)) who - 1))
  rw [hdifference]
  dsimp only [deviated, deviation] at htail
  linarith

/-- A uniformly bounded sequence remains summable after geometric weighting
starting at exponent one. -/
private theorem summable_pow_succ_mul_of_abs_le
    {ratio bound : ℝ} {values : ℕ → ℝ} (hratio : |ratio| < 1)
    (hbound : ∀ index, |values index| ≤ bound) :
    Summable fun index : ℕ => ratio ^ (index + 1) * values index := by
  have hbase := summable_pow_mul_of_abs_le hratio hbound
  have hscaled := hbase.mul_left ratio
  refine hscaled.congr ?_
  intro index
  rw [pow_succ']
  ring

/-- Inequality (**) after integration: one third of today's cooperation mass
is bounded by the discounted future cooperation mass. -/
private theorem prisonersDilemma_one_third_mass_le_futureMass
    (profile : prisonersDilemma.BehaviorProfile)
    (hnash : prisonersDilemma.repeatedGame.IsDiscountedεNash
      (1 - lam) prisonersDilemma.repeatedInitial 0 profile)
    (start : ℕ) (hlam : 0 < lam) (hlam1 : lam < 1) :
    (1 / 3 : ℝ) * prisonersDilemmaCooperationMass profile start ≤
      ∑' offset : ℕ, (1 - lam) ^ (offset + 1) *
        prisonersDilemmaCooperationMass profile (start + (offset + 1)) := by
  letI (player : Bool) : Finite (prisonersDilemma.repeatedGame.Act player) :=
    @Finite.of_fintype _ (prisonersDilemma.finiteAction player)
  letI : Finite prisonersDilemma.repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  let beta := 1 - lam
  have hbeta0 : 0 ≤ beta := by dsimp only [beta]; linarith
  have hbeta1 : beta < 1 := by dsimp only [beta]; linarith
  have hrow := prisonersDilemma_deviationGain_le_futureSurplus
    profile hnash false start hlam hlam1
  have hcolumn := prisonersDilemma_deviationGain_le_futureSurplus
    profile hnash true start hlam hlam1
  let rowTerm : ℕ → ℝ := fun offset => beta ^ (offset + 1) *
    (prisonersDilemma.repeatedGame.expectedStagePayoff profile
      prisonersDilemma.repeatedInitial (start + (offset + 1)) false - 1)
  let columnTerm : ℕ → ℝ := fun offset => beta ^ (offset + 1) *
    (prisonersDilemma.repeatedGame.expectedStagePayoff profile
      prisonersDilemma.repeatedInitial (start + (offset + 1)) true - 1)
  obtain ⟨bound, hbound⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun data : prisonersDilemma.repeatedGame.State ×
        prisonersDilemma.repeatedGame.JointAct × Bool =>
      prisonersDilemma.repeatedGame.stagePayoff data.1 data.2.1 data.2.2)
  have hsurplusSummable (who : Bool) : Summable fun offset : ℕ =>
      beta ^ (offset + 1) *
        (prisonersDilemma.repeatedGame.expectedStagePayoff profile
          prisonersDilemma.repeatedInitial (start + (offset + 1)) who - 1) := by
    apply summable_pow_succ_mul_of_abs_le (bound := bound + 1)
      (by simpa [abs_of_nonneg hbeta0] using hbeta1)
    intro offset
    have hpayoff := prisonersDilemma.repeatedGame.abs_expectedStagePayoff_le
      (fun state action => hbound (state, action, who)) profile
      prisonersDilemma.repeatedInitial (start + (offset + 1))
    have htriangle := abs_sub
      (prisonersDilemma.repeatedGame.expectedStagePayoff profile
        prisonersDilemma.repeatedInitial (start + (offset + 1)) who) 1
    norm_num at htriangle
    linarith
  have hrowSummable : Summable rowTerm := by
    simpa only [rowTerm] using hsurplusSummable false
  have hcolumnSummable : Summable columnTerm := by
    simpa only [columnTerm] using hsurplusSummable true
  have hsum :
      (∑' offset, rowTerm offset) + ∑' offset, columnTerm offset =
        ∑' offset, beta ^ (offset + 1) *
          prisonersDilemmaCooperationMass profile (start + (offset + 1)) := by
    rw [← hrowSummable.tsum_add hcolumnSummable]
    apply tsum_congr
    intro offset
    dsimp only [rowTerm, columnTerm, prisonersDilemmaCooperationMass]
    ring
  have hgainIdentity :=
    prisonersDilemmaCooperationMass_eq_three_mul_deviationGain profile start
  change _ ≤ ∑' offset, beta ^ (offset + 1) *
    prisonersDilemmaCooperationMass profile (start + (offset + 1))
  rw [← hsum]
  change _ ≤ _ at hrow hcolumn
  nlinarith

/-- Above the critical current-stage weight `3/4`, inequality (**) forces the
supremum of the cooperation masses to vanish. -/
private theorem prisonersDilemmaCooperationMass_eq_zero_of_nash
    (profile : prisonersDilemma.BehaviorProfile)
    (hnash : prisonersDilemma.repeatedGame.IsDiscountedεNash
      (1 - lam) prisonersDilemma.repeatedInitial 0 profile)
    (hlam : 3 / 4 < lam) (hlam1 : lam < 1) :
    ∀ time, prisonersDilemmaCooperationMass profile time = 0 := by
  let beta := 1 - lam
  let mass : ℕ → ℝ := prisonersDilemmaCooperationMass profile
  let y := sSup (Set.range mass)
  have hlam0 : 0 < lam := by linarith
  have hbeta0 : 0 ≤ beta := by dsimp only [beta]; linarith
  have hbeta1 : beta < 1 := by dsimp only [beta]; linarith
  have hbetaQuarter : beta < 1 / 4 := by dsimp only [beta]; linarith
  have hrangeNonempty : (Set.range mass).Nonempty := Set.range_nonempty mass
  have hrangeBdd : BddAbove (Set.range mass) := by
    refine ⟨6, ?_⟩
    rintro _ ⟨time, rfl⟩
    exact (prisonersDilemmaCooperationMass_mem_Icc profile time).2
  have hmassLe (time : ℕ) : mass time ≤ y :=
    le_csSup hrangeBdd ⟨time, rfl⟩
  have hy0 : 0 ≤ y := by
    have hzero := (prisonersDilemmaCooperationMass_mem_Icc profile 0).1
    exact hzero.trans (hmassLe 0)
  have hfutureBound (start : ℕ) :
      (∑' offset : ℕ, beta ^ (offset + 1) * mass (start + (offset + 1))) ≤
        y * (beta / (1 - beta)) := by
    have hmassSummable : Summable fun offset : ℕ =>
        beta ^ (offset + 1) * mass (start + (offset + 1)) := by
      apply summable_pow_succ_mul_of_abs_le (bound := 6)
        (by simpa [abs_of_nonneg hbeta0] using hbeta1)
      intro offset
      have hmass := prisonersDilemmaCooperationMass_mem_Icc
        profile (start + (offset + 1))
      rw [abs_of_nonneg hmass.1]
      exact hmass.2
    have hySummable : Summable fun offset : ℕ => beta ^ (offset + 1) * y := by
      apply summable_pow_succ_mul_of_abs_le (bound := |y|)
        (by simpa [abs_of_nonneg hbeta0] using hbeta1)
      exact fun _ => le_rfl
    calc
      (∑' offset : ℕ, beta ^ (offset + 1) * mass (start + (offset + 1))) ≤
          ∑' offset : ℕ, beta ^ (offset + 1) * y :=
        hmassSummable.tsum_le_tsum (fun offset =>
          mul_le_mul_of_nonneg_left (hmassLe _) (pow_nonneg hbeta0 _)) hySummable
      _ = y * (beta / (1 - beta)) := by
        rw [show (∑' offset : ℕ, beta ^ (offset + 1) * y) =
            beta * ((∑' offset : ℕ, beta ^ offset) * y) by
          rw [← tsum_mul_right, ← tsum_mul_left]
          apply tsum_congr
          intro offset
          rw [pow_succ']
          ring]
        rw [tsum_geometric_of_lt_one hbeta0 hbeta1]
        field_simp [sub_ne_zero.mpr hbeta1.ne]
  have hmassUpper (time : ℕ) :
      mass time ≤ 3 * (y * (beta / (1 - beta))) := by
    have hpaper := prisonersDilemma_one_third_mass_le_futureMass
      profile hnash time hlam0 hlam1
    change (1 / 3 : ℝ) * mass time ≤ _ at hpaper
    change _ ≤ _
    nlinarith [hpaper.trans (hfutureBound time)]
  have hyUpper : y ≤ 3 * (y * (beta / (1 - beta))) :=
    csSup_le hrangeNonempty (by
      rintro _ ⟨time, rfl⟩
      exact hmassUpper time)
  have hratio : 3 * (beta / (1 - beta)) < 1 := by
    have hdenom : 0 < 1 - beta := by linarith
    rw [show 3 * (beta / (1 - beta)) = (3 * beta) / (1 - beta) by ring]
    exact (div_lt_iff₀ hdenom).2 (by nlinarith)
  have hy : y = 0 := by
    nlinarith
  intro time
  apply le_antisymm
  · simpa [hy] using hmassLe time
  · exact (prisonersDilemmaCooperationMass_mem_Icc profile time).1

private theorem prisonersDilemma_discountedPayoff_sum_eq_two_of_mass_zero
    (profile : prisonersDilemma.BehaviorProfile)
    (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam < 1)
    (hmass : ∀ time, prisonersDilemmaCooperationMass profile time = 0) :
    prisonersDilemma.discountedPayoff lam profile false +
      prisonersDilemma.discountedPayoff lam profile true = 2 := by
  letI (player : Bool) : Finite (prisonersDilemma.repeatedGame.Act player) :=
    @Finite.of_fintype _ (prisonersDilemma.finiteAction player)
  letI : Finite prisonersDilemma.repeatedGame.State :=
    inferInstanceAs (Finite PUnit)
  let beta := 1 - lam
  have hbeta0 : 0 ≤ beta := by dsimp only [beta]; linarith
  have hbeta1 : beta < 1 := by dsimp only [beta]; linarith
  obtain ⟨bound, hbound⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun data : prisonersDilemma.repeatedGame.State ×
        prisonersDilemma.repeatedGame.JointAct × Bool =>
      prisonersDilemma.repeatedGame.stagePayoff data.1 data.2.1 data.2.2)
  have hs (who : Bool) : Summable fun time : ℕ => beta ^ time *
      prisonersDilemma.repeatedGame.expectedStagePayoff profile
        prisonersDilemma.repeatedInitial time who :=
    prisonersDilemma.repeatedGame.summable_discounted_expectedStagePayoff
      (fun state action => hbound (state, action, who)) profile
      prisonersDilemma.repeatedInitial
      (by simpa [abs_of_nonneg hbeta0] using hbeta1)
  unfold FiniteStageGame.discountedPayoff StochasticGame.discountedPayoff
  rw [show 1 - (1 - lam) = lam by ring]
  change lam * (∑' time : ℕ, beta ^ time *
      prisonersDilemma.repeatedGame.expectedStagePayoff profile
        prisonersDilemma.repeatedInitial time false) +
    lam * (∑' time : ℕ, beta ^ time *
      prisonersDilemma.repeatedGame.expectedStagePayoff profile
        prisonersDilemma.repeatedInitial time true) = 2
  rw [← mul_add, ← (hs false).tsum_add (hs true)]
  have hstage (time : ℕ) :
      prisonersDilemma.repeatedGame.expectedStagePayoff profile
          prisonersDilemma.repeatedInitial time false +
        prisonersDilemma.repeatedGame.expectedStagePayoff profile
          prisonersDilemma.repeatedInitial time true = 2 := by
    have := hmass time
    unfold prisonersDilemmaCooperationMass at this
    linarith
  simp_rw [← mul_add, hstage, tsum_mul_right,
    tsum_geometric_of_lt_one hbeta0 hbeta1]
  have hne : lam ≠ 0 := ne_of_gt hlam
  change lam * ((1 - beta)⁻¹ * 2) = 2
  rw [show 1 - beta = lam by dsimp only [beta]; ring]
  field_simp

/-- With current-stage weight one, only the initial expected stage matters. -/
private theorem discountedPayoff_one_eq_mixedPayoff_initial
    (G : FiniteStageGame) (profile : G.BehaviorProfile) (who : G.Player) :
    G.discountedPayoff 1 profile who =
      G.mixedPayoff (G.initialMixedProfile profile) who := by
  unfold FiniteStageGame.discountedPayoff
  rw [show 1 - (1 : ℝ) = 0 by ring]
  unfold StochasticGame.discountedPayoff
  rw [show (∑' time : ℕ, 0 ^ time *
      G.repeatedGame.expectedStagePayoff profile G.repeatedInitial time who) =
      G.repeatedGame.expectedStagePayoff profile G.repeatedInitial 0 who by
    rw [tsum_eq_single 0]
    · simp
    · intro time htime
      have hpositive : 0 < time := Nat.pos_of_ne_zero htime
      simp [Nat.ne_of_gt hpositive]]
  simpa using expectedStagePayoff_zero_eq_mixedPayoff_initial G profile who

/-! Proposition 14's proof is the paper's uniform gain inequality and
supremum argument.  It is not implied merely by strict dominance. -/
theorem proposition_14 (lam : ℝ) (hlam : 3 / 4 < lam) (hlam1 : lam ≤ 1) :
    prisonersDilemma.discountedEquilibriumPayoffs lam = {pair 1 1} := by
  apply Set.Subset.antisymm
  · rintro payoff ⟨profile, hnash, hpayoff⟩
    have hlam0 : 0 < lam := by linarith
    have hcoordinates : payoff false = 1 ∧ payoff true = 1 := by
      by_cases hcritical : lam = 1
      · subst lam
        let current := prisonersDilemma.initialMixedProfile profile
        have hcurrentNash : prisonersDilemma.kernel.mixedExtension.IsNash current := by
          intro who deviation
          let behaviorDeviation : prisonersDilemma.BehaviorStrategy who :=
            fun _time _history => deviation
          have hequilibrium := hnash who behaviorDeviation
          simp only [add_zero] at hequilibrium
          change prisonersDilemma.discountedPayoff 1 profile who ≥
            prisonersDilemma.discountedPayoff 1
              (Function.update profile who behaviorDeviation) who at hequilibrium
          rw [discountedPayoff_one_eq_mixedPayoff_initial,
            discountedPayoff_one_eq_mixedPayoff_initial] at hequilibrium
          have hupdate : prisonersDilemma.initialMixedProfile
              (Function.update profile who behaviorDeviation) =
              Function.update current who deviation := by
            funext player
            by_cases hplayer : player = who
            · subst player
              simp [FiniteStageGame.initialMixedProfile, behaviorDeviation]
            · simp [FiniteStageGame.initialMixedProfile, current,
                Function.update_of_ne hplayer]
          rwa [hupdate] at hequilibrium
        have hmem : prisonersDilemma.mixedPayoff current ∈
            prisonersDilemma.oneStageEquilibriumPayoffs :=
          ⟨current, hcurrentNash, rfl⟩
        rw [prisonersDilemma_E1_eq_singleton] at hmem
        have hcurrent := Set.mem_singleton_iff.mp hmem
        rw [← hpayoff]
        constructor <;>
          rw [discountedPayoff_one_eq_mixedPayoff_initial, hcurrent] <;> rfl
      · have hlamLt : lam < 1 := lt_of_le_of_ne hlam1 hcritical
        have hmass := prisonersDilemmaCooperationMass_eq_zero_of_nash
          profile hnash hlam hlamLt
        have hsum := prisonersDilemma_discountedPayoff_sum_eq_two_of_mass_zero
          profile lam hlam0 hlamLt hmass
        let rate : prisonersDilemma.DiscountRate := ⟨lam, hlam0, hlam1⟩
        have hir := lemma_1_Elambda_subset_Delta prisonersDilemma rate
          ⟨profile, hnash, hpayoff⟩
        have hfalse : 1 ≤ payoff false := by
          have := hir.2 false
          simpa [prisonersDilemma_individualRationalLevel] using this
        have htrue : 1 ≤ payoff true := by
          have := hir.2 true
          simpa [prisonersDilemma_individualRationalLevel] using this
        rw [hpayoff] at hsum
        constructor <;> linarith
    apply Set.mem_singleton_iff.mpr
    funext who
    cases who
    · exact hcoordinates.1
    · exact hcoordinates.2
  · intro payoff hpayoff
    rw [Set.mem_singleton_iff] at hpayoff
    subst payoff
    let rate : prisonersDilemma.DiscountRate :=
      ⟨lam, by linarith, hlam1⟩
    exact lemma_1_E1_subset_Elambda prisonersDilemma rate
      (by rw [prisonersDilemma_E1_eq_singleton]; exact Set.mem_singleton _)

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
abbrev symmetricGeneralizedDilemma (α β x : ℝ) : FiniteStageGame :=
  binaryGame (pair (β - x) (β - x)) (pair (α - x) β)
    (pair β (α - x)) (pair α α)

/-- Critical current-stage discount in Remark 1. -/
def criticalDiscount (α β x : ℝ) : ℝ :=
  (β - α - x) / (β - α)

/-- The row payoff is affine in the two defection probabilities. -/
private theorem symmetricGeneralizedDilemma_mixedEU_false
    (α β x : ℝ) (profile : Bool → PMF Bool) :
    (symmetricGeneralizedDilemma α β x).kernel.mixedExtension.eu
        profile false =
      β - x + x * (profile false true).toReal -
        (β - α) * (profile true true).toReal := by
  rw [binaryKernel_mixedEU_apply]
  simp only [pair_false]
  ring

/-- The column payoff is affine in the two defection probabilities. -/
private theorem symmetricGeneralizedDilemma_mixedEU_true
    (α β x : ℝ) (profile : Bool → PMF Bool) :
    (symmetricGeneralizedDilemma α β x).kernel.mixedExtension.eu
        profile true =
      β - x + x * (profile true true).toReal -
        (β - α) * (profile false true).toReal := by
  rw [binaryKernel_mixedEU_apply]
  simp only [pair_true]
  ring

/-- Pure row defection substitutes probability one in the row formula. -/
private theorem symmetricGeneralizedDilemma_mixedEU_update_false_pure
    (α β x : ℝ) (profile : Bool → PMF Bool) :
    (symmetricGeneralizedDilemma α β x).kernel.mixedExtension.eu
        (Function.update profile false (PMF.pure true)) false =
      β - x + x - (β - α) * (profile true true).toReal := by
  rw [symmetricGeneralizedDilemma_mixedEU_false]
  change β - x + x * ((PMF.pure true : PMF Bool) true).toReal -
    (β - α) * (profile true true).toReal = _
  simp

/-- Pure column defection substitutes probability one in the column formula. -/
private theorem symmetricGeneralizedDilemma_mixedEU_update_true_pure
    (α β x : ℝ) (profile : Bool → PMF Bool) :
    (symmetricGeneralizedDilemma α β x).kernel.mixedExtension.eu
        (Function.update profile true (PMF.pure true)) true =
      β - x + x - (β - α) * (profile false true).toReal := by
  rw [symmetricGeneralizedDilemma_mixedEU_true]
  change β - x + x * ((PMF.pure true : PMF Bool) true).toReal -
    (β - α) * (profile false true).toReal = _
  simp

/-- The mixed action profile prescribed after one public history. -/
private noncomputable abbrev symmetricDilemmaMixedProfileAt
    (α β x : ℝ)
    (profile : (symmetricGeneralizedDilemma α β x).BehaviorProfile)
    {time : ℕ}
    (history : (symmetricGeneralizedDilemma α β x).repeatedGame.Hist time) :
    Bool → PMF Bool :=
  fun player => monitoredMixedProfileAt
    (symmetricGeneralizedDilemma α β x) profile history player

/-- Stage utility at a public history is the corresponding mixed payoff. -/
private theorem symmetricDilemma_stageEUAt_eq_mixedEU
    (α β x : ℝ)
    (profile : (symmetricGeneralizedDilemma α β x).BehaviorProfile)
    {time : ℕ}
    (history : (symmetricGeneralizedDilemma α β x).repeatedGame.Hist time)
    (who : Bool) :
    (symmetricGeneralizedDilemma α β x).repeatedGame.stageEUAt
        profile history who =
      (symmetricGeneralizedDilemma α β x).kernel.mixedExtension.eu
        (symmetricDilemmaMixedProfileAt α β x profile history) who := by
  rw [stageEUAt_eq_monitoredMixedProfileAt]

/-- Expected aggregate payoff above `(α,α)` in the generalized dilemma. -/
private noncomputable def symmetricDilemmaSurplus
    (α β x : ℝ)
    (profile : (symmetricGeneralizedDilemma α β x).BehaviorProfile)
    (time : ℕ) : ℝ :=
  (symmetricGeneralizedDilemma α β x).repeatedGame.expectedStagePayoff
      profile (symmetricGeneralizedDilemma α β x).repeatedInitial time false +
    (symmetricGeneralizedDilemma α β x).repeatedGame.expectedStagePayoff
      profile (symmetricGeneralizedDilemma α β x).repeatedInitial time true - 2 * α

/-- Permanent defection from `start` earns at least the baseline `α`. -/
private theorem expectedStagePayoff_symmetricDilemma_constantTrueFrom_ge
    (α β x : ℝ) (hαβ : α ≤ β)
    (profile : (symmetricGeneralizedDilemma α β x).BehaviorProfile)
    (who : Bool) (start time : ℕ) (htime : start ≤ time) :
    α ≤ (symmetricGeneralizedDilemma α β x).repeatedGame.expectedStagePayoff
      (Function.update profile who
        (constantActionFrom (symmetricGeneralizedDilemma α β x)
          profile who start true))
      (symmetricGeneralizedDilemma α β x).repeatedInitial time who := by
  let G := symmetricGeneralizedDilemma α β x
  letI (player : Bool) : Finite (G.repeatedGame.Act player) :=
    @Finite.of_fintype _ (G.finiteAction player)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  unfold StochasticGame.expectedStagePayoff
  let law := G.repeatedGame.histDist
    (Function.update profile who
      (constantActionFrom G profile who start true))
    G.repeatedInitial time
  refine (Math.Probability.expect_const law α).symm.trans_le ?_
  apply Math.Probability.expect_mono
  intro history
  let deviated := Function.update profile who
    (constantActionFrom G profile who start true)
  let current := symmetricDilemmaMixedProfileAt α β x profile history
  have hstage : G.repeatedGame.stageEUAt deviated history who =
      G.kernel.mixedExtension.eu
        (Function.update current who (PMF.pure true)) who := by
    rw [symmetricDilemma_stageEUAt_eq_mixedEU]
    congr 1
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [deviated, current, symmetricDilemmaMixedProfileAt,
        monitoredMixedProfileAt_apply, constantActionFrom,
        Nat.not_lt.mpr htime]
      rfl
    · simp [deviated, current, symmetricDilemmaMixedProfileAt,
        monitoredMixedProfileAt_apply, Function.update_of_ne hplayer]
  change α ≤ G.repeatedGame.stageEUAt deviated history who
  rw [hstage]
  cases who
  · rw [symmetricGeneralizedDilemma_mixedEU_update_false_pure]
    have hq0 : 0 ≤ (current true true).toReal := ENNReal.toReal_nonneg
    have hq1 : (current true true).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    nlinarith
  · rw [symmetricGeneralizedDilemma_mixedEU_update_true_pure]
    have hp0 : 0 ≤ (current false true).toReal := ENNReal.toReal_nonneg
    have hp1 : (current false true).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    nlinarith

/-- Current aggregate surplus is proportional to the two one-stage
defection gains. -/
private theorem symmetricDilemma_x_mul_surplus_eq_gap_mul_deviationGain
    (α β x : ℝ)
    (profile : (symmetricGeneralizedDilemma α β x).BehaviorProfile)
    (time : ℕ) :
    x * symmetricDilemmaSurplus α β x profile time = (β - α - x) *
      (((symmetricGeneralizedDilemma α β x).repeatedGame.expectedStagePayoff
          (Function.update profile false
            (constantActionFrom (symmetricGeneralizedDilemma α β x)
              profile false time true))
          (symmetricGeneralizedDilemma α β x).repeatedInitial time false -
        (symmetricGeneralizedDilemma α β x).repeatedGame.expectedStagePayoff
          profile (symmetricGeneralizedDilemma α β x).repeatedInitial
          time false) +
       ((symmetricGeneralizedDilemma α β x).repeatedGame.expectedStagePayoff
          (Function.update profile true
            (constantActionFrom (symmetricGeneralizedDilemma α β x)
              profile true time true))
          (symmetricGeneralizedDilemma α β x).repeatedInitial time true -
        (symmetricGeneralizedDilemma α β x).repeatedGame.expectedStagePayoff
          profile (symmetricGeneralizedDilemma α β x).repeatedInitial
      time true)) := by
  let G := symmetricGeneralizedDilemma α β x
  letI (player : Bool) : Finite (G.repeatedGame.Act player) :=
    @Finite.of_fintype _ (G.finiteAction player)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  let rowDeviated := Function.update profile false
    (constantActionFrom G profile false time true)
  let columnDeviated := Function.update profile true
    (constantActionFrom G profile true time true)
  let law := G.repeatedGame.histDist profile G.repeatedInitial time
  have hrowLaw : G.repeatedGame.histDist rowDeviated G.repeatedInitial time = law :=
    G.repeatedGame.histDist_eq_of_profilesAgreeBefore
      (update_constantActionFrom_agreeBefore G profile false time true) time le_rfl
  have hcolumnLaw :
      G.repeatedGame.histDist columnDeviated G.repeatedInitial time = law :=
    G.repeatedGame.histDist_eq_of_profilesAgreeBefore
      (update_constantActionFrom_agreeBefore G profile true time true) time le_rfl
  unfold symmetricDilemmaSurplus StochasticGame.expectedStagePayoff
  change x * (Math.Probability.expect law
      (fun history => G.repeatedGame.stageEUAt profile history false) +
      Math.Probability.expect law
        (fun history => G.repeatedGame.stageEUAt profile history true) - 2 * α) = _
  change _ = (β - α - x) *
    ((Math.Probability.expect
          (G.repeatedGame.histDist rowDeviated G.repeatedInitial time)
          (fun history => G.repeatedGame.stageEUAt rowDeviated history false) -
        Math.Probability.expect law
          (fun history => G.repeatedGame.stageEUAt profile history false)) +
      (Math.Probability.expect
          (G.repeatedGame.histDist columnDeviated G.repeatedInitial time)
          (fun history => G.repeatedGame.stageEUAt columnDeviated history true) -
        Math.Probability.expect law
          (fun history => G.repeatedGame.stageEUAt profile history true)))
  rw [hrowLaw, hcolumnLaw]
  rw [← Math.Probability.expect_add, ← Math.Probability.expect_sub,
    ← Math.Probability.expect_sub, ← Math.Probability.expect_add,
    ← Math.Probability.expect_const law (2 * α),
    ← Math.Probability.expect_sub,
    ← Math.Probability.expect_const_mul, ← Math.Probability.expect_const_mul]
  apply congrArg (Math.Probability.expect law)
  funext history
  let current := symmetricDilemmaMixedProfileAt α β x profile history
  have hrow : G.repeatedGame.stageEUAt rowDeviated history false =
      G.kernel.mixedExtension.eu
        (Function.update current false (PMF.pure true)) false := by
    rw [symmetricDilemma_stageEUAt_eq_mixedEU]
    congr 1
    funext player
    by_cases hplayer : player = false
    · subst player
      simp [rowDeviated, symmetricDilemmaMixedProfileAt,
        monitoredMixedProfileAt_apply, constantActionFrom]
      rfl
    · simp [rowDeviated, current, symmetricDilemmaMixedProfileAt,
        monitoredMixedProfileAt_apply, Function.update_of_ne hplayer]
  have hcolumn : G.repeatedGame.stageEUAt columnDeviated history true =
      G.kernel.mixedExtension.eu
        (Function.update current true (PMF.pure true)) true := by
    rw [symmetricDilemma_stageEUAt_eq_mixedEU]
    congr 1
    funext player
    by_cases hplayer : player = true
    · subst player
      simp [columnDeviated, symmetricDilemmaMixedProfileAt,
        monitoredMixedProfileAt_apply, constantActionFrom]
      rfl
    · simp [columnDeviated, current, symmetricDilemmaMixedProfileAt,
        monitoredMixedProfileAt_apply, Function.update_of_ne hplayer]
  have horiginal (who : Bool) : G.repeatedGame.stageEUAt profile history who =
      G.kernel.mixedExtension.eu current who := by
    exact symmetricDilemma_stageEUAt_eq_mixedEU α β x profile history who
  rw [hrow, hcolumn, horiginal false, horiginal true,
    symmetricGeneralizedDilemma_mixedEU_false,
    symmetricGeneralizedDilemma_mixedEU_true,
    symmetricGeneralizedDilemma_mixedEU_update_false_pure,
    symmetricGeneralizedDilemma_mixedEU_update_true_pure]
  ring

/-- Generalized-dilemma surplus lies between zero and twice the payoff gap. -/
private theorem symmetricDilemmaSurplus_mem_Icc
    (α β x : ℝ) (hgap : α < β - x)
    (profile : (symmetricGeneralizedDilemma α β x).BehaviorProfile)
    (time : ℕ) :
    symmetricDilemmaSurplus α β x profile time ∈ Set.Icc 0 (2 * (β - α - x)) := by
  let G := symmetricGeneralizedDilemma α β x
  letI (player : Bool) : Finite (G.repeatedGame.Act player) :=
    @Finite.of_fintype _ (G.finiteAction player)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  let law := G.repeatedGame.histDist profile G.repeatedInitial time
  have hpointwise (history : G.repeatedGame.Hist time) :
      0 ≤ G.repeatedGame.stageEUAt profile history false +
          G.repeatedGame.stageEUAt profile history true - 2 * α ∧
        G.repeatedGame.stageEUAt profile history false +
          G.repeatedGame.stageEUAt profile history true - 2 * α ≤
            2 * (β - α - x) := by
    let current := symmetricDilemmaMixedProfileAt α β x profile history
    have horiginal (who : Bool) : G.repeatedGame.stageEUAt profile history who =
        G.kernel.mixedExtension.eu current who := by
      exact symmetricDilemma_stageEUAt_eq_mixedEU α β x profile history who
    rw [horiginal false, horiginal true,
      symmetricGeneralizedDilemma_mixedEU_false,
      symmetricGeneralizedDilemma_mixedEU_true]
    have hp0 : 0 ≤ (current false true).toReal := ENNReal.toReal_nonneg
    have hq0 : 0 ≤ (current true true).toReal := ENNReal.toReal_nonneg
    have hp1 : (current false true).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    have hq1 : (current true true).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    constructor <;> nlinarith
  unfold symmetricDilemmaSurplus StochasticGame.expectedStagePayoff
  change Math.Probability.expect law
      (fun history => G.repeatedGame.stageEUAt profile history false) +
      Math.Probability.expect law
        (fun history => G.repeatedGame.stageEUAt profile history true) - 2 * α
      ∈ Set.Icc 0 (2 * (β - α - x))
  rw [← Math.Probability.expect_add,
    ← Math.Probability.expect_const law (2 * α),
    ← Math.Probability.expect_sub]
  constructor
  · rw [← Math.Probability.expect_const law 0]
    apply Math.Probability.expect_mono
    exact fun history => (hpointwise history).1
  · rw [← Math.Probability.expect_const law (2 * (β - α - x))]
    apply Math.Probability.expect_mono
    exact fun history => (hpointwise history).2

/-- Nash's inequality bounds a current defection gain by future surplus
above `α`. -/
private theorem symmetricDilemma_deviationGain_le_futureSurplus
    (α β x lam : ℝ) (hαβ : α ≤ β)
    (profile : (symmetricGeneralizedDilemma α β x).BehaviorProfile)
    (hnash : (symmetricGeneralizedDilemma α β x).repeatedGame.IsDiscountedεNash
      (1 - lam) (symmetricGeneralizedDilemma α β x).repeatedInitial 0 profile)
    (who : Bool) (start : ℕ) (hlam : 0 < lam) (hlam1 : lam < 1) :
    (symmetricGeneralizedDilemma α β x).repeatedGame.expectedStagePayoff
        (Function.update profile who
          (constantActionFrom (symmetricGeneralizedDilemma α β x)
            profile who start true))
        (symmetricGeneralizedDilemma α β x).repeatedInitial start who -
      (symmetricGeneralizedDilemma α β x).repeatedGame.expectedStagePayoff
        profile (symmetricGeneralizedDilemma α β x).repeatedInitial start who ≤
      ∑' offset : ℕ, (1 - lam) ^ (offset + 1) *
        ((symmetricGeneralizedDilemma α β x).repeatedGame.expectedStagePayoff
          profile (symmetricGeneralizedDilemma α β x).repeatedInitial
          (start + (offset + 1)) who - α) := by
  let G := symmetricGeneralizedDilemma α β x
  letI (player : Bool) : Finite (G.repeatedGame.Act player) :=
    @Finite.of_fintype _ (G.finiteAction player)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  let beta := 1 - lam
  let deviation := constantActionFrom G profile who start true
  let deviated := Function.update profile who deviation
  have hbeta0 : 0 ≤ beta := by dsimp only [beta]; linarith
  have hbeta1 : beta < 1 := by dsimp only [beta]; linarith
  have htail := discountedTail_le_of_nash_of_agreeBefore
    G profile hnash who deviation start
      (update_constantActionFrom_agreeBefore G profile who start true) hlam hlam1
  change (∑' offset : ℕ, beta ^ offset *
      G.repeatedGame.expectedStagePayoff deviated G.repeatedInitial
        (start + offset) who) ≤
    ∑' offset : ℕ, beta ^ offset *
      G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
        (start + offset) who at htail
  obtain ⟨bound, hbound⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun data : G.repeatedGame.State × G.repeatedGame.JointAct =>
      G.repeatedGame.stagePayoff data.1 data.2 who)
  have horiginalSummable : Summable fun offset : ℕ => beta ^ offset *
      G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
        (start + offset) who := by
    apply summable_pow_mul_of_abs_le
      (by simpa [abs_of_nonneg hbeta0] using hbeta1)
    intro offset
    exact G.repeatedGame.abs_expectedStagePayoff_le
      (fun state action => hbound (state, action)) profile
      G.repeatedInitial (start + offset)
  have hdeviatedSummable : Summable fun offset : ℕ => beta ^ offset *
      G.repeatedGame.expectedStagePayoff deviated G.repeatedInitial
        (start + offset) who := by
    apply summable_pow_mul_of_abs_le
      (by simpa [abs_of_nonneg hbeta0] using hbeta1)
    intro offset
    exact G.repeatedGame.abs_expectedStagePayoff_le
      (fun state action => hbound (state, action)) deviated
      G.repeatedInitial (start + offset)
  rw [horiginalSummable.tsum_eq_zero_add,
    hdeviatedSummable.tsum_eq_zero_add] at htail
  simp only [pow_zero, one_mul, Nat.add_zero] at htail
  have hfutureDeviation :
      (∑' offset : ℕ, beta ^ (offset + 1) * α) ≤
        ∑' offset : ℕ, beta ^ (offset + 1) *
          G.repeatedGame.expectedStagePayoff deviated G.repeatedInitial
            (start + (offset + 1)) who := by
    have hgeom : Summable fun offset : ℕ => beta ^ (offset + 1) * α := by
      apply summable_pow_succ_mul_of_abs_le (bound := |α|)
        (by simpa [abs_of_nonneg hbeta0] using hbeta1)
      exact fun _ => le_rfl
    have hdev : Summable fun offset : ℕ => beta ^ (offset + 1) *
        G.repeatedGame.expectedStagePayoff deviated G.repeatedInitial
          (start + (offset + 1)) who :=
      hdeviatedSummable.comp_injective Nat.succ_injective
    exact hgeom.tsum_le_tsum (fun offset =>
      mul_le_mul_of_nonneg_left
        (expectedStagePayoff_symmetricDilemma_constantTrueFrom_ge
          α β x hαβ profile who start (start + (offset + 1)) (by omega))
        (pow_nonneg hbeta0 (offset + 1))) hdev
  have horiginalFuture : Summable fun offset : ℕ => beta ^ (offset + 1) *
      G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
        (start + (offset + 1)) who :=
    horiginalSummable.comp_injective Nat.succ_injective
  have hbaselineFuture : Summable fun offset : ℕ =>
      beta ^ (offset + 1) * α := by
    apply summable_pow_succ_mul_of_abs_le (bound := |α|)
      (by simpa [abs_of_nonneg hbeta0] using hbeta1)
    exact fun _ => le_rfl
  have hdifference :
      (∑' offset : ℕ, beta ^ (offset + 1) *
        (G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
          (start + (offset + 1)) who - α)) =
      (∑' offset : ℕ, beta ^ (offset + 1) *
        G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
          (start + (offset + 1)) who) -
        ∑' offset : ℕ, beta ^ (offset + 1) * α := by
    rw [← horiginalFuture.tsum_sub hbaselineFuture]
    apply tsum_congr
    intro offset
    ring
  change _ ≤ (∑' offset : ℕ, beta ^ (offset + 1) *
    (G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
      (start + (offset + 1)) who - α))
  rw [hdifference]
  dsimp only [deviated, deviation] at htail
  linarith

/-- Summing the two deviation inequalities gives the paper's recursive
surplus bound. -/
private theorem symmetricDilemma_x_mul_surplus_le_futureSurplus
    (α β x lam : ℝ) (hgap : α < β - x) (hx : 0 < x)
    (profile : (symmetricGeneralizedDilemma α β x).BehaviorProfile)
    (hnash : (symmetricGeneralizedDilemma α β x).repeatedGame.IsDiscountedεNash
      (1 - lam) (symmetricGeneralizedDilemma α β x).repeatedInitial 0 profile)
    (start : ℕ) (hlam : 0 < lam) (hlam1 : lam < 1) :
    x * symmetricDilemmaSurplus α β x profile start ≤
      (β - α - x) *
        ∑' offset : ℕ, (1 - lam) ^ (offset + 1) *
          symmetricDilemmaSurplus α β x profile (start + (offset + 1)) := by
  let G := symmetricGeneralizedDilemma α β x
  letI (player : Bool) : Finite (G.repeatedGame.Act player) :=
    @Finite.of_fintype _ (G.finiteAction player)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  let beta := 1 - lam
  have hαβ : α ≤ β := by linarith
  have hbeta0 : 0 ≤ beta := by dsimp only [beta]; linarith
  have hbeta1 : beta < 1 := by dsimp only [beta]; linarith
  have hrow := symmetricDilemma_deviationGain_le_futureSurplus
    α β x lam hαβ profile hnash false start hlam hlam1
  have hcolumn := symmetricDilemma_deviationGain_le_futureSurplus
    α β x lam hαβ profile hnash true start hlam hlam1
  let rowTerm : ℕ → ℝ := fun offset => beta ^ (offset + 1) *
    (G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
      (start + (offset + 1)) false - α)
  let columnTerm : ℕ → ℝ := fun offset => beta ^ (offset + 1) *
    (G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
      (start + (offset + 1)) true - α)
  obtain ⟨bound, hbound⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun data : G.repeatedGame.State × G.repeatedGame.JointAct × Bool =>
      G.repeatedGame.stagePayoff data.1 data.2.1 data.2.2)
  have hsurplusSummable (who : Bool) : Summable fun offset : ℕ =>
      beta ^ (offset + 1) *
        (G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
          (start + (offset + 1)) who - α) := by
    apply summable_pow_succ_mul_of_abs_le (bound := bound + |α|)
      (by simpa [abs_of_nonneg hbeta0] using hbeta1)
    intro offset
    have hpayoff := G.repeatedGame.abs_expectedStagePayoff_le
      (fun state action => hbound (state, action, who)) profile
      G.repeatedInitial (start + (offset + 1))
    have htriangle := abs_sub
      (G.repeatedGame.expectedStagePayoff profile G.repeatedInitial
        (start + (offset + 1)) who) α
    linarith [le_abs_self α]
  have hrowSummable : Summable rowTerm := by
    simpa only [rowTerm] using hsurplusSummable false
  have hcolumnSummable : Summable columnTerm := by
    simpa only [columnTerm] using hsurplusSummable true
  have hsum :
      (∑' offset, rowTerm offset) + ∑' offset, columnTerm offset =
        ∑' offset, beta ^ (offset + 1) *
          symmetricDilemmaSurplus α β x profile (start + (offset + 1)) := by
    rw [← hrowSummable.tsum_add hcolumnSummable]
    apply tsum_congr
    intro offset
    dsimp only [rowTerm, columnTerm, symmetricDilemmaSurplus]
    ring
  have hgainIdentity :=
    symmetricDilemma_x_mul_surplus_eq_gap_mul_deviationGain
      α β x profile start
  change _ ≤ (β - α - x) *
    ∑' offset, beta ^ (offset + 1) *
      symmetricDilemmaSurplus α β x profile (start + (offset + 1))
  rw [← hsum]
  change _ ≤ _ at hrow hcolumn
  nlinarith

/-- Above the critical discount, the recursive bound forces all surplus to
vanish. -/
private theorem symmetricDilemmaSurplus_eq_zero_of_nash
    (α β x lam : ℝ) (hgap : α < β - x) (hx : 0 < x)
    (profile : (symmetricGeneralizedDilemma α β x).BehaviorProfile)
    (hnash : (symmetricGeneralizedDilemma α β x).repeatedGame.IsDiscountedεNash
      (1 - lam) (symmetricGeneralizedDilemma α β x).repeatedInitial 0 profile)
    (hlam : criticalDiscount α β x < lam) (hlam1 : lam < 1) :
    ∀ time, symmetricDilemmaSurplus α β x profile time = 0 := by
  let beta := 1 - lam
  let mass : ℕ → ℝ := symmetricDilemmaSurplus α β x profile
  let y := sSup (Set.range mass)
  have hd : 0 < β - α := by linarith
  have hgap0 : 0 < β - α - x := by linarith
  have hcritical0 : 0 < criticalDiscount α β x := by
    unfold criticalDiscount
    positivity
  have hlam0 : 0 < lam := hcritical0.trans hlam
  have hbeta0 : 0 ≤ beta := by dsimp only [beta]; linarith
  have hbeta1 : beta < 1 := by dsimp only [beta]; linarith
  have hrangeNonempty : (Set.range mass).Nonempty := Set.range_nonempty mass
  have hrangeBdd : BddAbove (Set.range mass) := by
    refine ⟨2 * (β - α - x), ?_⟩
    rintro _ ⟨time, rfl⟩
    exact (symmetricDilemmaSurplus_mem_Icc α β x hgap profile time).2
  have hmassLe (time : ℕ) : mass time ≤ y :=
    le_csSup hrangeBdd ⟨time, rfl⟩
  have hy0 : 0 ≤ y := by
    have hzero := (symmetricDilemmaSurplus_mem_Icc α β x hgap profile 0).1
    exact hzero.trans (hmassLe 0)
  have hfutureBound (start : ℕ) :
      (∑' offset : ℕ, beta ^ (offset + 1) * mass (start + (offset + 1))) ≤
        y * (beta / (1 - beta)) := by
    have hmassSummable : Summable fun offset : ℕ =>
        beta ^ (offset + 1) * mass (start + (offset + 1)) := by
      apply summable_pow_succ_mul_of_abs_le (bound := 2 * (β - α - x))
        (by simpa [abs_of_nonneg hbeta0] using hbeta1)
      intro offset
      have hmass := symmetricDilemmaSurplus_mem_Icc
        α β x hgap profile (start + (offset + 1))
      rw [abs_of_nonneg hmass.1]
      exact hmass.2
    have hySummable : Summable fun offset : ℕ => beta ^ (offset + 1) * y := by
      apply summable_pow_succ_mul_of_abs_le (bound := |y|)
        (by simpa [abs_of_nonneg hbeta0] using hbeta1)
      exact fun _ => le_rfl
    calc
      (∑' offset : ℕ, beta ^ (offset + 1) * mass (start + (offset + 1))) ≤
          ∑' offset : ℕ, beta ^ (offset + 1) * y :=
        hmassSummable.tsum_le_tsum (fun offset =>
          mul_le_mul_of_nonneg_left (hmassLe _) (pow_nonneg hbeta0 _)) hySummable
      _ = y * (beta / (1 - beta)) := by
        rw [show (∑' offset : ℕ, beta ^ (offset + 1) * y) =
            beta * ((∑' offset : ℕ, beta ^ offset) * y) by
          rw [← tsum_mul_right, ← tsum_mul_left]
          apply tsum_congr
          intro offset
          rw [pow_succ']
          ring]
        rw [tsum_geometric_of_lt_one hbeta0 hbeta1]
        field_simp [sub_ne_zero.mpr hbeta1.ne]
  have hmassUpper (time : ℕ) :
      x * mass time ≤
        (β - α - x) * (y * (beta / (1 - beta))) := by
    have hpaper := symmetricDilemma_x_mul_surplus_le_futureSurplus
      α β x lam hgap hx profile hnash time hlam0 hlam1
    exact hpaper.trans (mul_le_mul_of_nonneg_left
      (hfutureBound time) hgap0.le)
  have hyUpper : x * y ≤
      (β - α - x) * (y * (beta / (1 - beta))) := by
    have hyBound : y ≤
        ((β - α - x) * (y * (beta / (1 - beta)))) / x := by
      apply csSup_le hrangeNonempty
      rintro _ ⟨time, rfl⟩
      exact (le_div_iff₀ hx).2 (by
        simpa only [mul_comm] using hmassUpper time)
    simpa only [mul_comm] using (le_div_iff₀ hx).1 hyBound
  have hcontraction :
      (β - α - x) * (beta / (1 - beta)) < x := by
    have hcriticalExpanded : (β - α - x) / (β - α) < lam := by
      simpa only [criticalDiscount] using hlam
    have hdenom : 0 < 1 - beta := by linarith
    rw [show (β - α - x) * (beta / (1 - beta)) =
      ((β - α - x) * beta) / (1 - beta) by ring]
    apply (div_lt_iff₀ hdenom).2
    apply (div_lt_iff₀ hd).1 at hcriticalExpanded
    dsimp only [beta]
    nlinarith
  have hy : y = 0 := by
    nlinarith
  intro time
  apply le_antisymm
  · simpa [hy] using hmassLe time
  · exact (symmetricDilemmaSurplus_mem_Icc α β x hgap profile time).1

/-- Zero surplus makes the two discounted payoffs sum to `2α`. -/
private theorem symmetricDilemma_discountedPayoff_sum_eq_baseline_of_surplus_zero
    (α β x lam : ℝ)
    (profile : (symmetricGeneralizedDilemma α β x).BehaviorProfile)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hmass : ∀ time, symmetricDilemmaSurplus α β x profile time = 0) :
    (symmetricGeneralizedDilemma α β x).discountedPayoff lam profile false +
      (symmetricGeneralizedDilemma α β x).discountedPayoff lam profile true =
        2 * α := by
  let G := symmetricGeneralizedDilemma α β x
  letI (player : Bool) : Finite (G.repeatedGame.Act player) :=
    @Finite.of_fintype _ (G.finiteAction player)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  let beta := 1 - lam
  have hbeta0 : 0 ≤ beta := by dsimp only [beta]; linarith
  have hbeta1 : beta < 1 := by dsimp only [beta]; linarith
  obtain ⟨bound, hbound⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun data : G.repeatedGame.State × G.repeatedGame.JointAct × Bool =>
      G.repeatedGame.stagePayoff data.1 data.2.1 data.2.2)
  have hs (who : Bool) : Summable fun time : ℕ => beta ^ time *
      G.repeatedGame.expectedStagePayoff profile G.repeatedInitial time who :=
    G.repeatedGame.summable_discounted_expectedStagePayoff
      (fun state action => hbound (state, action, who)) profile G.repeatedInitial
      (by simpa [abs_of_nonneg hbeta0] using hbeta1)
  unfold FiniteStageGame.discountedPayoff StochasticGame.discountedPayoff
  rw [show 1 - (1 - lam) = lam by ring]
  change lam * (∑' time : ℕ, beta ^ time *
      G.repeatedGame.expectedStagePayoff profile G.repeatedInitial time false) +
    lam * (∑' time : ℕ, beta ^ time *
      G.repeatedGame.expectedStagePayoff profile G.repeatedInitial time true) = 2 * α
  rw [← mul_add, ← (hs false).tsum_add (hs true)]
  have hstage (time : ℕ) :
      G.repeatedGame.expectedStagePayoff profile G.repeatedInitial time false +
        G.repeatedGame.expectedStagePayoff profile G.repeatedInitial time true = 2 * α := by
    have := hmass time
    unfold symmetricDilemmaSurplus at this
    linarith
  simp_rw [← mul_add, hstage, tsum_mul_right,
    tsum_geometric_of_lt_one hbeta0 hbeta1]
  have hne : lam ≠ 0 := ne_of_gt hlam
  change lam * ((1 - beta)⁻¹ * (2 * α)) = 2 * α
  rw [show 1 - beta = lam by dsimp only [beta]; ring]
  field_simp

/-- Mutual defection is the unique one-stage equilibrium payoff. -/
private theorem symmetricGeneralizedDilemma_E1_eq_singleton
    (α β x : ℝ) (hx : 0 < x) :
    (symmetricGeneralizedDilemma α β x).oneStageEquilibriumPayoffs =
      {pair α α} := by
  apply Set.Subset.antisymm
  · rintro payoff ⟨profile, hnash, rfl⟩
    change Bool → PMF Bool at profile
    have hrow := hnash false (PMF.pure true)
    have hcolumn := hnash true (PMF.pure true)
    change (symmetricGeneralizedDilemma α β x).kernel.mixedExtension.eu
        profile false ≥
      (symmetricGeneralizedDilemma α β x).kernel.mixedExtension.eu
        (Function.update profile false (PMF.pure true)) false at hrow
    change (symmetricGeneralizedDilemma α β x).kernel.mixedExtension.eu
        profile true ≥
      (symmetricGeneralizedDilemma α β x).kernel.mixedExtension.eu
        (Function.update profile true (PMF.pure true)) true at hcolumn
    rw [symmetricGeneralizedDilemma_mixedEU_false,
      symmetricGeneralizedDilemma_mixedEU_update_false_pure] at hrow
    rw [symmetricGeneralizedDilemma_mixedEU_true,
      symmetricGeneralizedDilemma_mixedEU_update_true_pure] at hcolumn
    have hp0 : 0 ≤ (profile false true).toReal := ENNReal.toReal_nonneg
    have hq0 : 0 ≤ (profile true true).toReal := ENNReal.toReal_nonneg
    have hp1 : (profile false true).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    have hq1 : (profile true true).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
    norm_num at hrow hcolumn
    have hp : (profile false true).toReal = 1 := by nlinarith
    have hq : (profile true true).toReal = 1 := by nlinarith
    apply Set.mem_singleton_iff.mpr
    unfold FiniteStageGame.mixedPayoff KernelGame.payoffVector
    funext who
    cases who
    · rw [symmetricGeneralizedDilemma_mixedEU_false, hp, hq]
      norm_num
    · rw [symmetricGeneralizedDilemma_mixedEU_true, hp, hq]
      norm_num
  · rintro _ rfl
    let profile : Bool → PMF Bool := fun _ => PMF.pure true
    refine ⟨profile, ?_, ?_⟩
    · intro who deviation
      cases who
      · change PMF Bool at deviation
        rw [symmetricGeneralizedDilemma_mixedEU_false,
          symmetricGeneralizedDilemma_mixedEU_false]
        have hp1 : (deviation true).toReal ≤ 1 :=
          ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
        simp [profile]
        nlinarith
      · change PMF Bool at deviation
        rw [symmetricGeneralizedDilemma_mixedEU_true,
          symmetricGeneralizedDilemma_mixedEU_true]
        have hq1 : (deviation true).toReal ≤ 1 :=
          ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
        simp [profile]
        nlinarith
    · funext who
      unfold FiniteStageGame.mixedPayoff KernelGame.payoffVector
      cases who
      · rw [symmetricGeneralizedDilemma_mixedEU_false]
        norm_num [profile, pair]
      · rw [symmetricGeneralizedDilemma_mixedEU_true]
        norm_num [profile, pair]


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
  let G := symmetricGeneralizedDilemma α β x
  letI (player : Bool) : Finite (G.repeatedGame.Act player) :=
    @Finite.of_fintype _ (G.finiteAction player)
  letI : Finite G.repeatedGame.State := inferInstanceAs (Finite PUnit)
  have hd : 0 < β - α := by linarith
  have hgap0 : 0 < β - α - x := by linarith
  have hcritical0 : 0 < criticalDiscount α β x := by
    unfold criticalDiscount
    positivity
  have hlam0 : 0 < lam := hcritical0.trans hlam
  apply Set.Subset.antisymm
  · rintro payoff ⟨profile, hnash, hpayoff⟩
    have hcoordinates : payoff false = α ∧ payoff true = α := by
      by_cases hcritical : lam = 1
      · subst lam
        let current := G.initialMixedProfile profile
        have hcurrentNash : G.kernel.mixedExtension.IsNash current := by
          intro who deviation
          let behaviorDeviation : G.BehaviorStrategy who :=
            fun _time _history => deviation
          have hequilibrium := hnash who behaviorDeviation
          simp only [add_zero] at hequilibrium
          change G.discountedPayoff 1 profile who ≥
            G.discountedPayoff 1
              (Function.update profile who behaviorDeviation) who at hequilibrium
          rw [discountedPayoff_one_eq_mixedPayoff_initial,
            discountedPayoff_one_eq_mixedPayoff_initial] at hequilibrium
          have hupdate : G.initialMixedProfile
              (Function.update profile who behaviorDeviation) =
              Function.update current who deviation := by
            funext player
            by_cases hplayer : player = who
            · subst player
              simp [FiniteStageGame.initialMixedProfile, behaviorDeviation]
            · simp [FiniteStageGame.initialMixedProfile, current,
                Function.update_of_ne hplayer]
          rwa [hupdate] at hequilibrium
        have hmem : G.mixedPayoff current ∈ G.oneStageEquilibriumPayoffs :=
          ⟨current, hcurrentNash, rfl⟩
        rw [symmetricGeneralizedDilemma_E1_eq_singleton α β x hx] at hmem
        have hcurrent := Set.mem_singleton_iff.mp hmem
        rw [← hpayoff]
        constructor <;>
          rw [discountedPayoff_one_eq_mixedPayoff_initial, hcurrent] <;> rfl
      · have hlamLt : lam < 1 := lt_of_le_of_ne hlam1 hcritical
        have hmass := symmetricDilemmaSurplus_eq_zero_of_nash
          α β x lam hgap hx profile hnash hlam hlamLt
        have hsum :=
          symmetricDilemma_discountedPayoff_sum_eq_baseline_of_surplus_zero
            α β x lam profile hlam0 hlamLt hmass
        have hlower (who : Bool) : α ≤ G.discountedPayoff lam profile who := by
          let deviation := constantActionFrom G profile who 0 true
          let deviated := Function.update profile who deviation
          obtain ⟨bound, hbound⟩ := Math.Probability.exists_abs_bound_of_finite
            (fun data : G.repeatedGame.State × G.repeatedGame.JointAct =>
              G.repeatedGame.stagePayoff data.1 data.2 who)
          have hdeviation : α ≤ G.repeatedGame.discountedPayoff (1 - lam)
              deviated G.repeatedInitial who := by
            apply G.repeatedGame.discountedPayoff_ge_of_forall_expectedStagePayoff_ge
              (fun state action => hbound (state, action))
              (fun time => expectedStagePayoff_symmetricDilemma_constantTrueFrom_ge
                α β x (by linarith) profile who 0 time (by omega))
              (by linarith) (by linarith)
          have hequilibrium := hnash who deviation
          simp only [add_zero] at hequilibrium
          change G.repeatedGame.discountedPayoff (1 - lam)
              profile G.repeatedInitial who ≥
            G.repeatedGame.discountedPayoff (1 - lam)
              deviated G.repeatedInitial who at hequilibrium
          exact hdeviation.trans hequilibrium
        have hfalse : α ≤ payoff false := by
          rw [← hpayoff]
          exact hlower false
        have htrue : α ≤ payoff true := by
          rw [← hpayoff]
          exact hlower true
        rw [hpayoff] at hsum
        constructor <;> linarith
    apply Set.mem_singleton_iff.mpr
    funext who
    cases who
    · exact hcoordinates.1
    · exact hcoordinates.2
  · intro payoff hpayoff
    rw [Set.mem_singleton_iff] at hpayoff
    subst payoff
    let rate : G.DiscountRate := ⟨lam, hlam0, hlam1⟩
    exact lemma_1_E1_subset_Elambda G rate
      (by rw [symmetricGeneralizedDilemma_E1_eq_singleton α β x hx]
          exact Set.mem_singleton _)


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
    (hβ : max (1 + α) (1 + 2 * x) < β) :
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
    (x ≥ y → pair (β - y) (β - y) ∈
      G.discountedEquilibriumPayoffs lambar) := by
  sorry

/-- Added in proof: without full dimensionality or two players, Lemma 2 is
false. The paper cites this three-player Forges--Mertens--Neyman counterexample
but does not print its payoff table, so its existence remains unproved here. -/
theorem added_in_proof_counterexample :
  ∃ G : FiniteStageGame,
    Fintype.card G.Player = 3 ∧
      affineDimension G.individuallyRationalPayoffs = 2 ∧
      ¬FullDimensional G.individuallyRationalPayoffs ∧
      ¬HausdorffConvergesAtZero G.discountedEquilibriumPayoffs
        G.individuallyRationalPayoffs := by
  sorry

end Literature.Sorin1986
