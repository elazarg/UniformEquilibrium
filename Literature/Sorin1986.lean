import Mathlib
import GameTheory.Core.Mixed
import GameTheory.Repeated.MonitoringOneShot

/-!
# Sorin (1986): On Repeated Games with Complete Information

Sylvain Sorin, *On Repeated Games with Complete Information*, Mathematics of
Operations Research 11(1) (1986), 147--160.
https://doi.org/10.1287/moor.11.1.147

The paper writes `λ` for the weight of the current stage.  The library's
normalized discounted sum writes `δ` for the continuation factor, so this file
uses `δ = 1 - λ` when it invokes the library evaluator.

Standard signalling is represented by public monitoring whose signal is the
realized pure action profile.  A monitored strategy therefore maps every
finite public action history to a finite mixed action.  For finite action sets
this is the paper's behavioral-strategy model; perfect recall gives the usual
mixed/behavioral equivalence.

The paper's added-in-proof correction is part of the transcription: the
Hausdorff convergence of discounted equilibrium payoff sets is stated only
when the individually rational feasible set is full-dimensional or there are
two players.
-/

noncomputable section

namespace Literature.Sorin1986

open GameTheory GameTheory.Math.Probability
open Set Filter
open scoped BigOperators Topology

universe uι ua

/-- A finite normal-form stage game.  Finiteness and nonemptiness are supplied
as typeclass assumptions at the results that use them. -/
structure StageGame (ι : Type uι) where
  Action : ι → Type ua
  payoff : (∀ i, Action i) → ι → ℝ

namespace StageGame

variable {ι : Type uι} (G : StageGame ι)

/-- Pure stage-action profiles. -/
abbrev PureProfile := ∀ i, G.Action i

/-- Independent mixed stage-action profiles. -/
abbrev MixedProfile := ∀ i, FinDist (G.Action i)

/-- The deterministic utility game associated with the payoff table. -/
@[reducible]
def pureUtilityGame : UtilityGame ι where
  form := GameForm.deterministic
    { Strategy := G.Action
      Outcome := G.PureProfile }
    id
  utility := G.payoff

/-- The independent mixed extension of the stage game. -/
@[reducible]
def mixedUtilityGame [Fintype ι] : UtilityGame ι :=
  G.pureUtilityGame.mixed

/-- Perfect public monitoring of the realized pure action profile. -/
@[reducible]
def standardMonitoring [Fintype ι] :
    G.mixedUtilityGame.PublicMonitoring where
  Signal := G.PureProfile
  signalLaw profile := G.mixedUtilityGame.form.play profile

/-- Public histories in the paper. -/
abbrev History [Fintype ι] (t : ℕ) :=
  G.standardMonitoring.SignalHistory t

/-- Behavioral strategies with standard signalling. -/
abbrev BehaviorStrategy [Fintype ι] (who : ι) :=
  G.standardMonitoring.MonitoredStrategy who

/-- Behavioral profiles with standard signalling. -/
abbrev BehaviorProfile [Fintype ι] :=
  G.standardMonitoring.MonitoredProfile

/-- Positive finite horizons. -/
abbrev Horizon := {n : ℕ // 0 < n}

/-- Paper discount parameters `λ ∈ (0,1]`. -/
abbrev DiscountRate := {λ : ℝ // 0 < λ ∧ λ ≤ 1}

/-- Expected average payoff in the `n`-stage repeated game. -/
def finitePayoff [Fintype ι] (n : G.Horizon)
    (profile : G.BehaviorProfile) (who : ι) : ℝ :=
  (n.1 : ℝ)⁻¹ *
    ∑ t ∈ Finset.range n.1,
      G.standardMonitoring.monitoredStagePayoff profile t who

/-- Vector form of the finite-horizon payoff. -/
def finitePayoffVector [Fintype ι] (n : G.Horizon)
    (profile : G.BehaviorProfile) : ι → ℝ :=
  fun who => G.finitePayoff n profile who

/-- Normalized `λ`-discounted payoff. -/
def discountedPayoff [Fintype ι] (λ : G.DiscountRate)
    (profile : G.BehaviorProfile) (who : ι) : ℝ :=
  G.standardMonitoring.discountedPayoff (1 - λ.1) profile who

/-- Vector form of the discounted payoff. -/
def discountedPayoffVector [Fintype ι] (λ : G.DiscountRate)
    (profile : G.BehaviorProfile) : ι → ℝ :=
  fun who => G.discountedPayoff λ profile who

end StageGame

/-- A real sequence is bounded in the elementary sense needed by a Banach
limit. -/
def IsBoundedSequence (x : ℕ → ℝ) : Prop :=
  ∃ bound : ℝ, ∀ n, |x n| ≤ bound

/-- Left shift of a real sequence. -/
def sequenceShift (x : ℕ → ℝ) : ℕ → ℝ :=
  fun n => x (n + 1)

/-- The properties of the Banach limit fixed in the paper.  The function is
stored on all sequences, but every axiom is restricted to bounded sequences;
its values outside `ℓ∞` are irrelevant. -/
structure BanachLimit where
  toFun : (ℕ → ℝ) → ℝ
  map_add : ∀ {x y}, IsBoundedSequence x → IsBoundedSequence y →
    toFun (x + y) = toFun x + toFun y
  map_smul : ∀ (c : ℝ) {x}, IsBoundedSequence x →
    toFun (c • x) = c * toFun x
  nonnegative : ∀ {x}, IsBoundedSequence x →
    (∀ n, 0 ≤ x n) → 0 ≤ toFun x
  shift_invariant : ∀ {x}, IsBoundedSequence x →
    toFun (sequenceShift x) = toFun x
  map_const : ∀ c : ℝ, toFun (fun _ => c) = c

instance : CoeFun BanachLimit (fun _ => (ℕ → ℝ) → ℝ) :=
  ⟨BanachLimit.toFun⟩

namespace StageGame

variable {ι : Type uι} (G : StageGame ι)

/-- The sequence to which the paper applies its Banach limit: expected
Cesàro payoffs over horizons `1,2,...`. -/
def averagePayoffSequence [Fintype ι] (profile : G.BehaviorProfile)
    (who : ι) : ℕ → ℝ :=
  fun n => G.finitePayoff ⟨n + 1, Nat.succ_pos n⟩ profile who

/-- Payoff in the `L`-infinitely repeated game. -/
def banachPayoff [Fintype ι] (L : BanachLimit)
    (profile : G.BehaviorProfile) (who : ι) : ℝ :=
  L (G.averagePayoffSequence profile who)

/-- Vector form of the Banach-limit payoff. -/
def banachPayoffVector [Fintype ι] (L : BanachLimit)
    (profile : G.BehaviorProfile) : ι → ℝ :=
  fun who => G.banachPayoff L profile who

/-- Utility of the finite repeated game on the canonical monitored form. -/
def finiteUtility [Fintype ι] (n : G.Horizon) :
    Utility G.standardMonitoring.monitoredSignature :=
  fun profile who => G.finitePayoff n profile who

/-- Utility of the Banach-limit repeated game. -/
def banachUtility [Fintype ι] (L : BanachLimit) :
    Utility G.standardMonitoring.monitoredSignature :=
  fun profile who => G.banachPayoff L profile who

/-- Nash equilibrium in the `n`-stage game. -/
def IsFiniteNash [Fintype ι] [DecidableEq ι] (n : G.Horizon)
    (profile : G.BehaviorProfile) : Prop :=
  IsNash G.standardMonitoring.monitoredForm
    (euPreference (G.finiteUtility n)) profile

/-- Nash equilibrium in the paper's `λ`-discounted game. -/
def IsDiscountedNash [Fintype ι] [DecidableEq ι]
    (λ : G.DiscountRate) (profile : G.BehaviorProfile) : Prop :=
  G.standardMonitoring.IsDiscountedPublicNash (1 - λ.1) profile

/-- Nash equilibrium in the `L`-infinitely repeated game. -/
def IsBanachNash [Fintype ι] [DecidableEq ι] (L : BanachLimit)
    (profile : G.BehaviorProfile) : Prop :=
  IsNash G.standardMonitoring.monitoredForm
    (euPreference (G.banachUtility L)) profile

/-- Feasible payoff set of the `n`-stage game (`D_n`). -/
def finiteFeasiblePayoffs [Fintype ι] (n : G.Horizon) : Set (ι → ℝ) :=
  Set.range (G.finitePayoffVector n)

/-- Equilibrium payoff set of the `n`-stage game (`E_n`). -/
def finiteEquilibriumPayoffs [Fintype ι] [DecidableEq ι]
    (n : G.Horizon) : Set (ι → ℝ) :=
  {payoff | ∃ profile, G.IsFiniteNash n profile ∧
    G.finitePayoffVector n profile = payoff}

/-- Feasible payoff set of the `λ`-discounted game (`D_λ`). -/
def discountedFeasiblePayoffs [Fintype ι]
    (λ : G.DiscountRate) : Set (ι → ℝ) :=
  Set.range (G.discountedPayoffVector λ)

/-- Equilibrium payoff set of the `λ`-discounted game (`E_λ`). -/
def discountedEquilibriumPayoffs [Fintype ι] [DecidableEq ι]
    (λ : G.DiscountRate) : Set (ι → ℝ) :=
  {payoff | ∃ profile, G.IsDiscountedNash λ profile ∧
    G.discountedPayoffVector λ profile = payoff}

/-- Feasible payoff set of the `L`-infinitely repeated game (`D_∞`). -/
def banachFeasiblePayoffs [Fintype ι] (L : BanachLimit) : Set (ι → ℝ) :=
  Set.range (G.banachPayoffVector L)

/-- Equilibrium payoff set of the `L`-infinitely repeated game (`E_∞`). -/
def banachEquilibriumPayoffs [Fintype ι] [DecidableEq ι]
    (L : BanachLimit) : Set (ι → ℝ) :=
  {payoff | ∃ profile, G.IsBanachNash L profile ∧
    G.banachPayoffVector L profile = payoff}

/-- Pure one-stage payoff vectors (`F` in the paper). -/
def purePayoffSet : Set (ι → ℝ) :=
  Set.range G.payoff

/-- The correlated feasible polytope `C = co F`. -/
def correlatedFeasibleSet : Set (ι → ℝ) :=
  convexHull ℝ G.purePayoffSet

/-- Expected one-stage payoff of an independent mixed profile. -/
def mixedStagePayoff [Fintype ι]
    (profile : G.MixedProfile) (who : ι) : ℝ :=
  G.mixedUtilityGame.stagePayoff profile who

/-- Player `who`'s individually rational level.  The opponents choose an
independent mixed profile, and the player's own coordinate is overwritten by a
pure best response, exactly as in the displayed definition on page 148. -/
def individuallyRationalLevel [Fintype ι] [DecidableEq ι]
    (who : ι) : ℝ :=
  ⨅ opponents : G.MixedProfile,
    ⨆ own : G.Action who,
      G.mixedStagePayoff
        (Profile.update opponents who (FinDist.pure own)) who

/-- Individually rational feasible payoff set `Δ`. -/
def individuallyRationalFeasibleSet [Fintype ι] [DecidableEq ι] :
    Set (ι → ℝ) :=
  {payoff | payoff ∈ G.correlatedFeasibleSet ∧
    ∀ who, G.individuallyRationalLevel who ≤ payoff who}

end StageGame

/-- Symmetric Hausdorff `ε`-closeness, written without choosing a particular
Hausdorff-distance API. -/
def HausdorffClose {α : Type*} [PseudoMetricSpace α]
    (ε : ℝ) (first second : Set α) : Prop :=
  (∀ x ∈ first, ∃ y ∈ second, dist x y < ε) ∧
  (∀ y ∈ second, ∃ x ∈ first, dist x y < ε)

/-- Hausdorff convergence of a sequence of sets. -/
def HausdorffConvergesAtTop {α : Type*} [PseudoMetricSpace α]
    (sets : ℕ → Set α) (limit : Set α) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
    HausdorffClose ε (sets n) limit

/-- Hausdorff convergence of a family indexed by positive real parameters as
the parameter tends to zero from the right. -/
def HausdorffConvergesAtZero {α : Type*} [PseudoMetricSpace α]
    (sets : ℝ → Set α) (limit : Set α) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ λ : ℝ, 0 < λ → λ < δ → HausdorffClose ε (sets λ) limit

/-- Scalar multiplication of a payoff set. -/
def scaleSet {ι : Type*} (t : ℝ) (set : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {payoff | ∃ x ∈ set, payoff = t • x}

/-- The `m`-fold Minkowski sum `m * X` used before Lemma 3. -/
def minkowskiNSum {ι : Type*} (m : ℕ) (set : Set (ι → ℝ)) :
    Set (ι → ℝ) :=
  {payoff | ∃ points : Fin m → ι → ℝ,
    (∀ k, points k ∈ set) ∧ payoff = ∑ k, points k}

/-- Face predicate used in Propositions 7--9. -/
def IsFaceOf {ι : Type*} (face ambient : Set (ι → ℝ)) : Prop :=
  face ⊆ ambient ∧
  ∀ ⦃x y : ι → ℝ⦄, x ∈ ambient → y ∈ ambient →
    ∀ ⦃t : ℝ⦄, 0 < t → t < 1 →
      t • x + (1 - t) • y ∈ face → x ∈ face ∧ y ∈ face

/-- Affine dimension of a payoff set. -/
noncomputable def affineDimension {ι : Type*} [Fintype ι]
    (set : Set (ι → ℝ)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ set).direction

/-- A one-dimensional face. -/
def IsOneDimensionalFace {ι : Type*} [Fintype ι]
    (face ambient : Set (ι → ℝ)) : Prop :=
  IsFaceOf face ambient ∧ affineDimension face = 1

/-! ## Section 1: generic compact mixed games -/

/-- Feasible payoff set of an already-mixed normal-form game. -/
def genericFeasiblePayoffs {ι Strategy : Type*}
    (payoff : Strategy → ι → ℝ) : Set (ι → ℝ) :=
  Set.range payoff

/-- Nash payoff set for an already-mixed normal-form game, with unilateral
replacement supplied by the model. -/
def genericEquilibriumPayoffs {ι Strategy : Type*}
    (payoff : Strategy → ι → ℝ)
    (isNash : Strategy → Prop) : Set (ι → ℝ) :=
  {value | ∃ profile, isNash profile ∧ payoff profile = value}

/-- Paper property (1): a continuous image of a nonempty compact,
path-connected mixed-profile space is nonempty, compact, and path-connected. -/
theorem genericFeasiblePayoffs_nonempty_compact_pathConnected
    {ι Strategy : Type*} [TopologicalSpace Strategy]
    [Nonempty Strategy] [CompactSpace Strategy] [PathConnectedSpace Strategy]
    (payoff : Strategy → ι → ℝ) (hpayoff : Continuous payoff) :
    (genericFeasiblePayoffs payoff).Nonempty ∧
      IsCompact (genericFeasiblePayoffs payoff) ∧
      IsPathConnected (genericFeasiblePayoffs payoff) := by
  constructor
  · exact Set.range_nonempty payoff
  constructor
  · exact isCompact_univ.image_of_continuousOn hpayoff.continuousOn
  · simpa [genericFeasiblePayoffs] using
      (isPathConnected_univ.image payoff hpayoff.continuousOn)

/-! **Paper property (2).** The Nash payoff set of the compact mixed extension
is nonempty and compact.  Its proof is Nash--Glicksberg existence plus closedness
of the Nash-profile set and continuity of the payoff map.  The current game
library has finite-support mixed extensions but no weak-topology space of
regular probabilities on an arbitrary compact strategy space, so the exact
regular-probability theorem is retained here as this explained `sorry`. -/
theorem genericEquilibriumPayoffs_nonempty_compact
    {ι Strategy : Type*} [TopologicalSpace Strategy]
    [CompactSpace Strategy]
    (payoff : Strategy → ι → ℝ) (isNash : Strategy → Prop)
    (hpayoff : Continuous payoff)
    (hnash_nonempty : Set.Nonempty {profile | isNash profile})
    (hnash_closed : IsClosed {profile | isNash profile}) :
    (genericEquilibriumPayoffs payoff isNash).Nonempty ∧
      IsCompact (genericEquilibriumPayoffs payoff isNash) := by
  constructor
  · rcases hnash_nonempty with ⟨profile, hprofile⟩
    exact ⟨payoff profile, profile, hprofile, rfl⟩
  · have hcompact : IsCompact {profile | isNash profile} :=
      hnash_closed.isCompact
    simpa [genericEquilibriumPayoffs, Set.image_image] using
      hcompact.image hpayoff

end Literature.Sorin1986
