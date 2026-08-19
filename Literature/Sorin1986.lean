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


/-! The specialization of properties (1) and (2) to the two repeated
finite/disounted evaluations.  Establishing compactness directly needs the
Tychonoff topology on behavioral profiles and continuity of the infinite
geometric payoff.  Those instances are not part of the current monitoring
API, so the exact specializations are retained as explained `sorry`s. -/

theorem finiteFeasiblePayoffs_nonempty_compact_pathConnected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : StageGame ι) (n : G.Horizon) :
    (G.finiteFeasiblePayoffs n).Nonempty ∧
      IsCompact (G.finiteFeasiblePayoffs n) ∧
      IsPathConnected (G.finiteFeasiblePayoffs n) := by
  sorry

theorem discountedFeasiblePayoffs_nonempty_compact_pathConnected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : StageGame ι) (λ : G.DiscountRate) :
    (G.discountedFeasiblePayoffs λ).Nonempty ∧
      IsCompact (G.discountedFeasiblePayoffs λ) ∧
      IsPathConnected (G.discountedFeasiblePayoffs λ) := by
  sorry

theorem finiteEquilibriumPayoffs_nonempty_compact
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : StageGame ι) (n : G.Horizon) :
    (G.finiteEquilibriumPayoffs n).Nonempty ∧
      IsCompact (G.finiteEquilibriumPayoffs n) := by
  sorry

theorem discountedEquilibriumPayoffs_nonempty_compact
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : StageGame ι) (λ : G.DiscountRate) :
    (G.discountedEquilibriumPayoffs λ).Nonempty ∧
      IsCompact (G.discountedEquilibriumPayoffs λ) := by
  sorry


/-! ## Asymptotic notation and the elementary inclusions -/

namespace StageGame

variable {ι : Type uι} (G : StageGame ι)

/-- `D_n`, extended at horizon zero by the natural singleton `{0}`.  The zero
case is used only in the block formula of Lemma 3. -/
def finiteFeasiblePayoffsAt [Fintype ι] (n : ℕ) : Set (ι → ℝ) :=
  if h : 0 < n then G.finiteFeasiblePayoffs ⟨n, h⟩ else {0}

/-- `E_n`, with the same harmless zero-horizon convention as `D_n`. -/
def finiteEquilibriumPayoffsAt [Fintype ι] [DecidableEq ι]
    (n : ℕ) : Set (ι → ℝ) :=
  if h : 0 < n then G.finiteEquilibriumPayoffs ⟨n, h⟩ else {0}

/-- `D_λ`, extended by the empty set outside the paper's domain `0 < λ ≤ 1`. -/
def discountedFeasiblePayoffsAt [Fintype ι] (λ : ℝ) : Set (ι → ℝ) :=
  if h : 0 < λ ∧ λ ≤ 1 then G.discountedFeasiblePayoffs ⟨λ, h⟩ else ∅

/-- `E_λ`, extended by the empty set outside `0 < λ ≤ 1`. -/
def discountedEquilibriumPayoffsAt [Fintype ι] [DecidableEq ι]
    (λ : ℝ) : Set (ι → ℝ) :=
  if h : 0 < λ ∧ λ ≤ 1 then G.discountedEquilibriumPayoffs ⟨λ, h⟩ else ∅

@[simp]
theorem finiteFeasiblePayoffsAt_zero [Fintype ι] :
    G.finiteFeasiblePayoffsAt 0 = {0} := by
  simp [finiteFeasiblePayoffsAt]

@[simp]
theorem finiteEquilibriumPayoffsAt_zero [Fintype ι] [DecidableEq ι] :
    G.finiteEquilibriumPayoffsAt 0 = {0} := by
  simp [finiteEquilibriumPayoffsAt]

@[simp]
theorem finiteFeasiblePayoffsAt_eq [Fintype ι] {n : ℕ} (hn : 0 < n) :
    G.finiteFeasiblePayoffsAt n = G.finiteFeasiblePayoffs ⟨n, hn⟩ := by
  simp [finiteFeasiblePayoffsAt, hn]

@[simp]
theorem finiteEquilibriumPayoffsAt_eq [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 0 < n) :
    G.finiteEquilibriumPayoffsAt n = G.finiteEquilibriumPayoffs ⟨n, hn⟩ := by
  simp [finiteEquilibriumPayoffsAt, hn]

@[simp]
theorem discountedFeasiblePayoffsAt_eq [Fintype ι]
    {λ : ℝ} (hλ : 0 < λ ∧ λ ≤ 1) :
    G.discountedFeasiblePayoffsAt λ = G.discountedFeasiblePayoffs ⟨λ, hλ⟩ := by
  simp [discountedFeasiblePayoffsAt, hλ]

@[simp]
theorem discountedEquilibriumPayoffsAt_eq [Fintype ι] [DecidableEq ι]
    {λ : ℝ} (hλ : 0 < λ ∧ λ ≤ 1) :
    G.discountedEquilibriumPayoffsAt λ =
      G.discountedEquilibriumPayoffs ⟨λ, hλ⟩ := by
  simp [discountedEquilibriumPayoffsAt, hλ]


/-- Equilibrium payoffs are feasible payoffs, including the zero-horizon
convention. -/
theorem finiteEquilibriumPayoffsAt_subset_feasible
    [Fintype ι] [DecidableEq ι] (n : ℕ) :
    G.finiteEquilibriumPayoffsAt n ⊆ G.finiteFeasiblePayoffsAt n := by
  by_cases hn : 0 < n
  · rw [G.finiteEquilibriumPayoffsAt_eq hn,
      G.finiteFeasiblePayoffsAt_eq hn]
    rintro payoff ⟨profile, _, rfl⟩
    exact ⟨profile, rfl⟩
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp

/-- Discounted equilibrium payoffs are discounted feasible payoffs. -/
theorem discountedEquilibriumPayoffsAt_subset_feasible
    [Fintype ι] [DecidableEq ι] (λ : ℝ) :
    G.discountedEquilibriumPayoffsAt λ ⊆
      G.discountedFeasiblePayoffsAt λ := by
  by_cases hλ : 0 < λ ∧ λ ≤ 1
  · rw [G.discountedEquilibriumPayoffsAt_eq hλ,
      G.discountedFeasiblePayoffsAt_eq hλ]
    rintro payoff ⟨profile, _, rfl⟩
    exact ⟨profile, rfl⟩
  · simp [discountedEquilibriumPayoffsAt,
      discountedFeasiblePayoffsAt, hλ]

/-- The paper's full-dimensionality condition from the added-in-proof
correction to Lemma 2. -/
def IndividuallyRationalSetFullDimensional [Fintype ι] [DecidableEq ι] : Prop :=
  affineDimension G.individuallyRationalFeasibleSet = Fintype.card ι

end StageGame

/-- The convex-hull sandwich used in Lemma 1(7). -/
theorem convex_eq_convexHull_iff_of_subset
    {V : Type*} [AddCommGroup V] [Module ℝ V]
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

namespace StageGame

variable {ι : Type uι} (G : StageGame ι)

/-! **Property (3), page 148.** The finite and discounted feasible sets
converge to `C`, and the Banach-limit feasible set is exactly `C`.

The finite and discounted convergence proofs require the complete compact
behavioral-strategy topology and a finite-cycle approximation theorem.  The
current repeated-game library deliberately exposes only finite-history laws,
so these paper-level statements remain `sorry`. -/
theorem paper_property3_finite [Fintype ι] [DecidableEq ι] :
    HausdorffConvergesAtTop G.finiteFeasiblePayoffsAt
      G.correlatedFeasibleSet := by
  sorry

theorem paper_property3_discounted [Fintype ι] [DecidableEq ι] :
    HausdorffConvergesAtZero G.discountedFeasiblePayoffsAt
      G.correlatedFeasibleSet := by
  sorry

theorem paper_property3_banach [Fintype ι] [DecidableEq ι]
    (L : BanachLimit) :
    G.banachFeasiblePayoffs L = G.correlatedFeasibleSet := by
  sorry

/-! **Property (4), page 148: the infinitely repeated Folk theorem.**  Its
proof needs public punishment strategies on the Banach-limit evaluator, which
has not yet been connected to the library's finite-history deviation lemmas. -/
theorem paper_property4_banach [Fintype ι] [DecidableEq ι]
    (L : BanachLimit) :
    G.banachEquilibriumPayoffs L =
      G.individuallyRationalFeasibleSet := by
  sorry

/-! **Lemma 1(5)--(8), pages 148--149.**  The inclusions are stated separately
for finite and discounted repetition.  Their proofs are elementary, but the
history-pasting and stationary-embedding lemmas for the paper's exact public
mixed model are not yet in the library; these are the only missing steps. -/
theorem lemma1_pure_subset_D1 [Fintype ι] [DecidableEq ι] :
    G.purePayoffSet ⊆ G.finiteFeasiblePayoffsAt 1 := by
  sorry

theorem lemma1_D1_subset_Dn [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 0 < n) :
    G.finiteFeasiblePayoffsAt 1 ⊆ G.finiteFeasiblePayoffsAt n := by
  sorry

theorem lemma1_D1_subset_Dlambda [Fintype ι] [DecidableEq ι]
    {λ : ℝ} (hλ : 0 < λ ∧ λ ≤ 1) :
    G.finiteFeasiblePayoffsAt 1 ⊆ G.discountedFeasiblePayoffsAt λ := by
  sorry

theorem lemma1_Dn_subset_C [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 0 < n) :
    G.finiteFeasiblePayoffsAt n ⊆ G.correlatedFeasibleSet := by
  sorry

theorem lemma1_Dlambda_subset_C [Fintype ι] [DecidableEq ι]
    {λ : ℝ} (hλ : 0 < λ ∧ λ ≤ 1) :
    G.discountedFeasiblePayoffsAt λ ⊆ G.correlatedFeasibleSet := by
  sorry

theorem lemma1_Dn_convex_iff [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 0 < n) :
    Convex ℝ (G.finiteFeasiblePayoffsAt n) ↔
      G.finiteFeasiblePayoffsAt n = G.correlatedFeasibleSet := by
  apply convex_eq_convexHull_iff_of_subset
  · exact G.lemma1_pure_subset_D1 |>.trans (G.lemma1_D1_subset_Dn hn)
  · exact G.lemma1_Dn_subset_C hn

theorem lemma1_Dlambda_convex_iff [Fintype ι] [DecidableEq ι]
    {λ : ℝ} (hλ : 0 < λ ∧ λ ≤ 1) :
    Convex ℝ (G.discountedFeasiblePayoffsAt λ) ↔
      G.discountedFeasiblePayoffsAt λ = G.correlatedFeasibleSet := by
  apply convex_eq_convexHull_iff_of_subset
  · exact G.lemma1_pure_subset_D1 |>.trans
      (G.lemma1_D1_subset_Dlambda hλ)
  · exact G.lemma1_Dlambda_subset_C hλ

theorem lemma1_E1_subset_En [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 0 < n) :
    G.finiteEquilibriumPayoffsAt 1 ⊆
      G.finiteEquilibriumPayoffsAt n := by
  sorry

theorem lemma1_E1_subset_Elambda [Fintype ι] [DecidableEq ι]
    {λ : ℝ} (hλ : 0 < λ ∧ λ ≤ 1) :
    G.finiteEquilibriumPayoffsAt 1 ⊆
      G.discountedEquilibriumPayoffsAt λ := by
  sorry

theorem lemma1_En_subset_Delta [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 0 < n) :
    G.finiteEquilibriumPayoffsAt n ⊆
      G.individuallyRationalFeasibleSet := by
  sorry

theorem lemma1_Elambda_subset_Delta [Fintype ι] [DecidableEq ι]
    {λ : ℝ} (hλ : 0 < λ ∧ λ ≤ 1) :
    G.discountedEquilibriumPayoffsAt λ ⊆
      G.individuallyRationalFeasibleSet := by
  sorry

/-! **Lemma 2, corrected by the added-in-proof note on page 160.**  The printed
unqualified statement is false for three players when `Δ` has affine dimension
two.  The paper supplies no payoff table for the Forges--Mertens--Neyman
counterexample, so there is no self-contained refutation to formalize here.
The corrected theorem is retained with exactly the condition actually used in
the proof.  Its unresolved ingredients are the finite pure-cycle approximation
and public punishment construction mentioned above. -/
theorem lemma2_corrected [Fintype ι] [DecidableEq ι]
    (hcondition : G.IndividuallyRationalSetFullDimensional ∨
      Fintype.card ι = 2) :
    HausdorffConvergesAtZero G.discountedEquilibriumPayoffsAt
      G.individuallyRationalFeasibleSet := by
  sorry

end StageGame

/-! The paper's `t * X` is an `m`-fold Minkowski sum; `m = 0` gives `{0}`. -/
@[simp]
theorem minkowskiNSum_zero {ι : Type*} (set : Set (ι → ℝ)) :
    minkowskiNSum 0 set = {0} := by
  ext payoff
  constructor
  · rintro ⟨points, _, rfl⟩
    simp
  · intro h
    have hzero : payoff = 0 := by simpa using h
    subst payoff
    refine ⟨fun k => k.elim0, ?_, by simp⟩
    intro k
    exact k.elim0

/-- The right-hand side of Lemma 3 before division by `n`. -/
def blockPayoffSet {ι : Type*} (r m p : ℕ)
    (Dr Dp : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {payoff | ∃ first ∈ Dr, ∃ blocks ∈ minkowskiNSum m Dp,
    payoff = (r : ℝ) • first + (p : ℝ) • blocks}

namespace StageGame

variable {ι : Type uι} (G : StageGame ι)

/-! **Lemma 3(9), page 149.**  Concatenating one `r`-stage block and `m`
independent `p`-stage blocks gives the displayed feasible-set inclusion.
The proof is blocked only by the absent monitored-profile concatenation API. -/
theorem lemma3_feasible [Fintype ι] [DecidableEq ι]
    {n m p r : ℕ} (hn : n = m * p + r) :
    blockPayoffSet r m p (G.finiteFeasiblePayoffsAt r)
        (G.finiteFeasiblePayoffsAt p) ⊆
      scaleSet (n : ℝ) (G.finiteFeasiblePayoffsAt n) := by
  sorry

/-! **Lemma 3(10).**  The same concatenation preserves Nash equilibrium because
later blocks ignore the earlier history.  A formal proof needs the same
concatenation API plus the corresponding deviation decomposition. -/
theorem lemma3_equilibrium [Fintype ι] [DecidableEq ι]
    {n m p r : ℕ} (hn : n = m * p + r) :
    blockPayoffSet r m p (G.finiteEquilibriumPayoffsAt r)
        (G.finiteEquilibriumPayoffsAt p) ⊆
      scaleSet (n : ℝ) (G.finiteEquilibriumPayoffsAt n) := by
  sorry

/-! The immediate divisibility consequence recorded after Lemma 3. -/
theorem finiteFeasiblePayoffsAt_subset_mul [Fintype ι] [DecidableEq ι]
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    G.finiteFeasiblePayoffsAt n ⊆ G.finiteFeasiblePayoffsAt (k * n) := by
  sorry

theorem finiteEquilibriumPayoffsAt_subset_mul [Fintype ι] [DecidableEq ι]
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    G.finiteEquilibriumPayoffsAt n ⊆
      G.finiteEquilibriumPayoffsAt (k * n) := by
  sorry

end StageGame


/-! ## Examples 1--6 -/

/-- Two-player payoff vector; `false` is the row player. -/
def pair (row column : ℝ) : Bool → ℝ :=
  fun who => if who then column else row

@[simp]
theorem pair_false (row column : ℝ) : pair row column false = row := by
  simp [pair]

@[simp]
theorem pair_true (row column : ℝ) : pair row column true = column := by
  simp [pair]

/-- A two-by-two game.  `false` means Top/Left and `true` means Bottom/Right. -/
def twoByTwoGame
    (topLeft topRight bottomLeft bottomRight : Bool → ℝ) :
    StageGame Bool where
  Action _ := Bool
  payoff profile :=
    match profile false, profile true with
    | false, false => topLeft
    | false, true => topRight
    | true, false => bottomLeft
    | true, true => bottomRight

@[simp]
theorem twoByTwoGame_payoff_ff
    (topLeft topRight bottomLeft bottomRight : Bool → ℝ) :
    (twoByTwoGame topLeft topRight bottomLeft bottomRight).payoff
        (fun _ => false) = topLeft := by
  rfl

/-- Example 1. -/
def example1 : StageGame Bool :=
  twoByTwoGame (pair 1 0) (pair 0 0) (pair 0 0) (pair 0 1)

/-- Example 2. -/
def example2 : StageGame Bool :=
  twoByTwoGame (pair 1 0) (pair 2 2) (pair 0 0) (pair 0 1)

/-- Example 3. -/
def example3 : StageGame Bool :=
  twoByTwoGame (pair 1 0) (pair 1 1) (pair 0 0) (pair 1 0)

/-- Example 4, for an integer parameter `m`. -/
def example4 (m : ℕ) : StageGame Bool :=
  twoByTwoGame (pair m 0) (pair (m + 1) (m + 1))
    (pair 0 0) (pair 0 m)

/-- A sequence of sets is monotone in one of the two inclusion directions. -/
def InclusionMonotone {α : Type*} (sets : ℕ → Set α) : Prop :=
  Monotone sets ∨ Antitone sets

/-! The finite repeated-game example claims below quantify over arbitrary
history-dependent deviations.  Their explicit strategies are transcribed in
the comments, but the current monitored finite-horizon layer has no backward
induction or finite-horizon one-shot-deviation theorem.  The `sorry`s mark that
single missing proof interface, not ambiguity in the games or payoffs. -/

/-- Example 1: `(1/2,1/2)` is a two-stage equilibrium payoff.  The equilibrium
plays the two diagonal pure outcomes once each, with the second-stage order
conditioned so that no first-stage deviation is profitable. -/
theorem example1_half_mem_E2 :
    pair (1 / 2) (1 / 2) ∈ example1.finiteEquilibriumPayoffsAt 2 := by
  sorry

/-- The same payoff is not feasible in one stage. -/
theorem example1_half_not_mem_D1 :
    pair (1 / 2) (1 / 2) ∉ example1.finiteFeasiblePayoffsAt 1 := by
  sorry

/-- Pareto optimality forces pure play at each stage, so the same payoff is not
feasible in three stages. -/
theorem example1_half_not_mem_D3 :
    pair (1 / 2) (1 / 2) ∉ example1.finiteFeasiblePayoffsAt 3 := by
  sorry

/-- Statement (11): neither the feasible nor equilibrium sequence is monotone
in an inclusion direction. -/
theorem statement11 :
    ¬ InclusionMonotone example1.finiteFeasiblePayoffsAt ∧
      ¬ InclusionMonotone example1.finiteEquilibriumPayoffsAt := by
  have hD2 : pair (1 / 2) (1 / 2) ∈
      example1.finiteFeasiblePayoffsAt 2 :=
    example1.finiteEquilibriumPayoffsAt_subset_feasible 2
      example1_half_mem_E2
  constructor
  · intro h
    rcases h with h | h
    · exact example1_half_not_mem_D3 (h (by omega) hD2)
    · exact example1_half_not_mem_D1 (h (by omega) hD2)
  · intro h
    rcases h with h | h
    · have hE3 := h (show 2 ≤ 3 by omega) example1_half_mem_E2
      exact example1_half_not_mem_D3
        (example1.finiteEquilibriumPayoffsAt_subset_feasible 3 hE3)
    · have hE1 := h (show 1 ≤ 2 by omega) example1_half_mem_E2
      exact example1_half_not_mem_D1
        (example1.finiteEquilibriumPayoffsAt_subset_feasible 1 hE1)

/-- Example 1 also has `D_n ≠ C` at every positive finite horizon. -/
theorem example1_Dn_ne_C {n : ℕ} (hn : 0 < n) :
    example1.finiteFeasiblePayoffsAt n ≠
      example1.correlatedFeasibleSet := by
  sorry

/-- Duplicating a pure strategy can leave `D₁,E₁` unchanged while enlarging
later feasible sets; the paper records that a suitable duplication puts
`(1/2,1/2)` in `D₃`.  The exact duplicate-action carrier is omitted from the
paper, so this existence statement is the faithful formal content. -/
theorem example1_duplicate_strategy_remark :
    ∃ duplicated : StageGame Bool,
      duplicated.finiteFeasiblePayoffsAt 1 =
        example1.finiteFeasiblePayoffsAt 1 ∧
      duplicated.finiteEquilibriumPayoffsAt 1 =
        example1.finiteEquilibriumPayoffsAt 1 ∧
      example1.finiteFeasiblePayoffsAt 2 ⊆
        duplicated.finiteFeasiblePayoffsAt 2 ∧
      pair (1 / 2) (1 / 2) ∈ duplicated.finiteFeasiblePayoffsAt 3 := by
  sorry

/-- Example 2: the one-stage feasible set is already `C`. -/
theorem example2_D1_eq_C :
    example2.finiteFeasiblePayoffsAt 1 =
      example2.correlatedFeasibleSet := by
  sorry

/-- Example 2: the unique one-stage equilibrium payoff is `(2,2)`. -/
theorem example2_E1_eq :
    example2.finiteEquilibriumPayoffsAt 1 = {pair 2 2} := by
  sorry

/-- Example 2: `(1,1)` is a two-stage equilibrium payoff.  The first stage is
`(Bottom,Left)`; at stage two the row player chooses Bottom exactly after
Right, and the column player chooses Left exactly after Top. -/
theorem example2_one_one_mem_E2 :
    pair 1 1 ∈ example2.finiteEquilibriumPayoffsAt 2 := by
  sorry

/-- Proposition 5 and `D₁=C` imply all finite feasible sets equal `C`. -/
theorem example2_Dn_eq_C {n : ℕ} (hn : 0 < n) :
    example2.finiteFeasiblePayoffsAt n =
      example2.correlatedFeasibleSet := by
  sorry

/-- Statement (12): equality of consecutive feasible sets does not force
consecutive equilibrium sets to agree. -/
theorem statement12 :
    ∃ G : StageGame Bool,
      G.finiteFeasiblePayoffsAt 1 = G.finiteFeasiblePayoffsAt 2 ∧
      G.finiteEquilibriumPayoffsAt 1 ≠
        G.finiteEquilibriumPayoffsAt 2 := by
  refine ⟨example2, ?_, ?_⟩
  · rw [example2_D1_eq_C, example2_Dn_eq_C (n := 2) (by omega)]
  · intro h
    have hmem : pair 1 1 ∈ example2.finiteEquilibriumPayoffsAt 1 := by
      rw [h]
      exact example2_one_one_mem_E2
    rw [example2_E1_eq] at hmem
    have heq : pair 1 1 = pair 2 2 := by simpa using hmem
    have hfalse := congrFun heq false
    norm_num at hfalse

/-- Statement (14): a finite repeated equilibrium payoff need not lie in the
convex hull of the one-stage equilibrium payoffs. -/
theorem statement14 :
    ∃ G : StageGame Bool, ∃ n : ℕ,
      G.finiteEquilibriumPayoffsAt n ⊄
        convexHull ℝ (G.finiteEquilibriumPayoffsAt 1) := by
  refine ⟨example2, 2, ?_⟩
  intro h
  have hmem := h example2_one_one_mem_E2
  rw [example2_E1_eq, convexHull_singleton] at hmem
  have heq : pair 1 1 = pair 2 2 := by simpa using hmem
  have hfalse := congrFun heq false
  norm_num at hfalse

/-- Example 3: the equilibrium payoff set is the same vertical segment at
every positive finite horizon. -/
theorem example3_En_eq {n : ℕ} (hn : 0 < n) :
    example3.finiteEquilibriumPayoffsAt n =
      {payoff | ∃ x ∈ Set.Icc (0 : ℝ) 1, payoff = pair 1 x} := by
  sorry

/-- Example 3: `(1/2,1/2)` is feasible in two stages but not in one. -/
theorem example3_half_mem_D2_not_D1 :
    pair (1 / 2) (1 / 2) ∈ example3.finiteFeasiblePayoffsAt 2 ∧
      pair (1 / 2) (1 / 2) ∉ example3.finiteFeasiblePayoffsAt 1 := by
  sorry

/-- Statement (13): equality of consecutive equilibrium sets does not force
equality of consecutive feasible sets. -/
theorem statement13 :
    ∃ G : StageGame Bool,
      G.finiteEquilibriumPayoffsAt 1 =
        G.finiteEquilibriumPayoffsAt 2 ∧
      G.finiteFeasiblePayoffsAt 1 ≠ G.finiteFeasiblePayoffsAt 2 := by
  refine ⟨example3, ?_, ?_⟩
  · rw [example3_En_eq (n := 1) (by omega),
      example3_En_eq (n := 2) (by omega)]
  · intro h
    apply example3_half_mem_D2_not_D1.2
    rw [h]
    exact example3_half_mem_D2_not_D1.1

/-- Example 4: before horizon `m`, the unique equilibrium payoff is the
strict-dominance payoff `(m+1,m+1)`. -/
theorem example4_En_eq {m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    (example4 m).finiteEquilibriumPayoffsAt n =
      {pair (m + 1) (m + 1)} := by
  sorry

/-- Example 4: `(m,m)` is an equilibrium payoff at horizon `m+1`. -/
theorem example4_mm_mem {m : ℕ} (hm : 0 < m) :
    pair m m ∈ (example4 m).finiteEquilibriumPayoffsAt (m + 1) := by
  sorry

/-- Statement (15): one downward inclusion does not persist two steps. -/
theorem statement15 :
    ∃ G : StageGame Bool, ∃ n : ℕ,
      G.finiteEquilibriumPayoffsAt (n + 1) ⊆
        G.finiteEquilibriumPayoffsAt n ∧
      G.finiteEquilibriumPayoffsAt (n + 2) ⊄
        G.finiteEquilibriumPayoffsAt n := by
  sorry

/-- Example 1 revisited: `(7/8,1/8)` is an equilibrium payoff at discount
weight `7/8`. -/
theorem example1_discount_seven_eighths :
    pair (7 / 8) (1 / 8) ∈
      example1.discountedEquilibriumPayoffsAt (7 / 8) := by
  sorry

/-- The preceding payoff is neither one-stage feasible nor feasible at
current-stage weight `3/4`. -/
theorem example1_discount_separation :
    pair (7 / 8) (1 / 8) ∉ example1.finiteFeasiblePayoffsAt 1 ∧
      pair (7 / 8) (1 / 8) ∉
        example1.discountedFeasiblePayoffsAt (3 / 4) := by
  sorry

/-- Statement (16): the discounted feasible and equilibrium nets are not
monotone.  The paper proves this through the two explicit weights above. -/
theorem statement16 :
    ∃ G : StageGame Bool, ∃ low high : ℝ,
      0 < low ∧ low < high ∧ high ≤ 1 ∧
      G.discountedFeasiblePayoffsAt high ⊄
        G.discountedFeasiblePayoffsAt low ∧
      G.discountedEquilibriumPayoffsAt high ⊄
        G.discountedEquilibriumPayoffsAt low := by
  refine ⟨example1, 3 / 4, 7 / 8, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩
  · intro h
    have hhigh : pair (7 / 8) (1 / 8) ∈
        example1.discountedFeasiblePayoffsAt (7 / 8) :=
      example1.discountedEquilibriumPayoffsAt_subset_feasible
        (7 / 8) example1_discount_seven_eighths
    exact example1_discount_separation.2 (h hhigh)
  · intro h
    have hlow := h example1_discount_seven_eighths
    exact example1_discount_separation.2
      (example1.discountedEquilibriumPayoffsAt_subset_feasible
        (3 / 4) hlow)


/-! ## Convexity, stationarity, and faces -/

namespace StageGame

variable {ι : Type uι} (G : StageGame ι)

/-! **Proposition 4, page 151.**  Fenchel's connected-set refinement of
Carathéodory gives a decomposition into at most `N` points of `D₁`; the paper
then recursively codes that decomposition in the discounted stages.  Mathlib
contains Carathéodory's theorem but not the connected-set refinement in the
required form, and the standard-monitoring coding lemma is also absent. -/
theorem proposition4 [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {λ : ℝ} (hλ : 0 < λ ∧ λ ≤ 1)
    (hsmall : λ < (Fintype.card ι : ℝ)⁻¹) :
    G.discountedFeasiblePayoffsAt λ = G.correlatedFeasibleSet := by
  sorry

/-! **Proposition 5(18).**  If `D_n` is convex, then `D_{n+1}=D_n`, and all
later finite feasible sets equal `C`.  The proof in the paper is an explicit
first-stage/tail rearrangement; formalizing it needs the same finite-history
profile splicing operation as Lemma 3. -/
theorem proposition5 [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 0 < n)
    (hconvex : Convex ℝ (G.finiteFeasiblePayoffsAt n)) :
    G.finiteFeasiblePayoffsAt (n + 1) =
        G.finiteFeasiblePayoffsAt n ∧
      ∀ m, n ≤ m →
        G.finiteFeasiblePayoffsAt m = G.correlatedFeasibleSet := by
  sorry

/-! Statement (19).  Eventual stationarity at `D_n` forces `D_n=C`.  This is
a direct consequence of property (3), or of Lemma 3 plus density of rational
weights; the Hausdorff-limit uniqueness bridge is not yet packaged here. -/
theorem statement19 [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 0 < n)
    (hstationary : ∀ m, n ≤ m →
      G.finiteFeasiblePayoffsAt m = G.finiteFeasiblePayoffsAt n) :
    G.finiteFeasiblePayoffsAt n = G.correlatedFeasibleSet := by
  sorry

/-! **Proposition 6(21), page 152.**  Convexity at current-stage weight `λ`
forces every less patient feasible set `D_δ`, `0<δ<λ`, to be all of `C`.
The recursive stage decomposition is the discounted counterpart of
Proposition 5 and awaits the same splicing API. -/
theorem proposition6 [Fintype ι] [DecidableEq ι]
    {δ λ : ℝ} (hδ : 0 < δ) (hδλ : δ < λ) (hλ : λ ≤ 1)
    (hconvex : Convex ℝ (G.discountedFeasiblePayoffsAt λ)) :
    G.discountedFeasiblePayoffsAt δ = G.correlatedFeasibleSet := by
  sorry

/-! Statement (22). -/
theorem statement22 [Fintype ι] [DecidableEq ι]
    {λ : ℝ} (hλ : 0 < λ ∧ λ ≤ 1)
    (hstationary : ∀ δ : ℝ, 0 < δ → δ < λ →
      G.discountedFeasiblePayoffsAt λ =
        G.discountedFeasiblePayoffsAt δ) :
    G.discountedFeasiblePayoffsAt λ = G.correlatedFeasibleSet := by
  sorry

/-! **Proposition 7(23).**  On a one-dimensional face, a reversed inclusion
between two discounted feasible sections forces the entire face into the less
patient feasible set.  The proof is the paper's maximal-gap replacement
argument.  Its formal dependencies are a compact-section maximizer and a
history-contingent tail replacement lemma, neither currently available for the
monitoring model. -/
theorem proposition7 [Fintype ι] [DecidableEq ι]
    {face : Set (ι → ℝ)}
    (hface : IsOneDimensionalFace face G.correlatedFeasibleSet)
    {δ λ : ℝ} (hδ : 0 < δ) (hδλ : δ < λ) (hλ : λ ≤ 1)
    (hinclusion :
      G.discountedFeasiblePayoffsAt δ ∩ face ⊆
        G.discountedFeasiblePayoffsAt λ ∩ face) :
    face ⊆ G.discountedFeasiblePayoffsAt δ := by
  sorry

/-! **Proposition 8(25).** -/
theorem proposition8 [Fintype ι] [DecidableEq ι]
    {n m : ℕ} (hm : 0 < m)
    (hlarge : Fintype.card ι * m < n)
    (hinclusion : G.finiteFeasiblePayoffsAt (n + m) ⊆
      G.finiteFeasiblePayoffsAt n) :
    G.finiteFeasiblePayoffsAt (n + m) =
      G.correlatedFeasibleSet := by
  sorry

/-! **Proposition 9(26).**  This is retained at the paper's exact face
dimension and horizon threshold.  The proof needs induction over polytope
faces, Carathéodory, and finite-history tail replacement. -/
theorem proposition9 [Fintype ι] [DecidableEq ι]
    {face : Set (ι → ℝ)} {p n m : ℕ}
    (hface : IsFaceOf face G.correlatedFeasibleSet)
    (hdim : affineDimension face = p)
    (hp : p < Fintype.card ι)
    (hm : 0 < m) (hlarge : p * m < n)
    (hinclusion :
      G.finiteFeasiblePayoffsAt (n + m) ∩ face ⊆
        G.finiteFeasiblePayoffsAt n ∩ face) :
    face ⊆ G.finiteFeasiblePayoffsAt (n + m) := by
  sorry

end StageGame

/-- A point of `face` maximizing distance from `set`. -/
def IsMaximalDistancePoint {V : Type*} [PseudoMetricSpace V]
    (set face : Set V) (point : V) : Prop :=
  point ∈ face ∧
    ∀ other ∈ face,
      Metric.infDist other set ≤ Metric.infDist point set

/-! **Lemma 10, pages 153--154.**  This is the geometric lemma used inside
Proposition 9.  The paper's separating-hyperplane proof is fully specified,
but a formal proof needs a compact polytope-face package connecting relative
frontier, affine dimension, and nearest points; those interfaces are not
present in Mathlib as one theorem. -/
theorem lemma10
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {feasible face : Set V} {point : V}
    (hfaceConvex : Convex ℝ face)
    (hfeasibleCompact : IsCompact feasible)
    (hfeasibleNonempty : feasible.Nonempty)
    (hfeasibleFace : feasible ⊆ face)
    (hboundary : frontier face ⊆ feasible)
    (hpoint : IsMaximalDistancePoint feasible face point) :
    point ∈ convexHull ℝ
      (Metric.closedBall point (Metric.infDist point feasible) ∩ feasible) := by
  sorry

/-- Example 5: unanimity on label `j` pays the unit vector `e_j`; every
non-unanimous profile pays zero. -/
def unanimityGame (ι : Type*) [Fintype ι] [DecidableEq ι] : StageGame ι where
  Action _ := ι
  payoff profile who := if (∀ player, profile player = who) then 1 else 0

/-- The barycenter used in Example 5. -/
def uniformBarycenter (ι : Type*) [Fintype ι] : ι → ℝ :=
  fun _ => (Fintype.card ι : ℝ)⁻¹

/-! **Example 5.**  The strict bound in Proposition 4 is sharp.  The proof is
a first-stage mass argument for the unanimity events.  It is elementary but
requires an explicit product-law calculation for arbitrary monitored mixed
profiles, which has not been developed in this file. -/
theorem example5_sharp
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {λ : ℝ} (hλ : 0 < λ ∧ λ ≤ 1)
    (hlarge : (Fintype.card ι : ℝ)⁻¹ < λ) :
    uniformBarycenter ι ∉
      (unanimityGame ι).discountedFeasiblePayoffsAt λ := by
  sorry

/-- Example 6, with row actions `false/true` and four column actions. -/
def example6 : StageGame Bool where
  Action who := if who then Fin 4 else Bool
  payoff profile :=
    let row : Bool := cast (by simp) (profile false)
    let column : Fin 4 := cast (by simp) (profile true)
    pair column.1
      (if row = decide (column.1 < 2) then 0 else 1)

/-! The dependent casts in `example6` merely encode the displayed `2×4`
matrix.  The next two statements are the paper's direct calculations; their
proofs reduce to finite product-law algebra and are left `sorry` until a small
matrix-game evaluator is available. -/

/-- `(3/2,1)` is not one-stage feasible in Example 6. -/
theorem example6_three_halves_one_not_D1 :
    pair (3 / 2) 1 ∉ example6.finiteFeasiblePayoffsAt 1 := by
  sorry

/-- Example 6 has `D₂=C`, although `D₁` is not convex. -/
theorem example6_D2_eq_C :
    example6.finiteFeasiblePayoffsAt 2 =
      example6.correlatedFeasibleSet := by
  sorry

/-- Statement (20): convexity at horizon `n` need not descend to `n-1`. -/
theorem statement20 :
    ∃ G : StageGame Bool, ∃ n : ℕ,
      1 < n ∧ Convex ℝ (G.finiteFeasiblePayoffsAt n) ∧
        ¬ Convex ℝ (G.finiteFeasiblePayoffsAt (n - 1)) := by
  sorry

/-! The paper notes that for a two-player `2×2` game, either `D₁=C` or no
finite `D_n` equals `C`.  Its proof combines Proposition 5 with the elementary
fact that a convex `D₁` for a `2×2` table already equals `C`. -/
theorem twoByTwo_dichotomy
    (topLeft topRight bottomLeft bottomRight : Bool → ℝ) :
    let G := twoByTwoGame topLeft topRight bottomLeft bottomRight
    G.finiteFeasiblePayoffsAt 1 = G.correlatedFeasibleSet ∨
      ∀ n : ℕ, 0 < n →
        G.finiteFeasiblePayoffsAt n ≠ G.correlatedFeasibleSet := by
  sorry

/-! **Proposition 11(27), page 155.**  For two players the feasible payoff set
of any compact mixed game is simply connected.  The paper proves this by an
index argument and a loop lift through the two strategy factors.  Mathlib has
fundamental-group simple connectedness, but no theorem identifying the planar
winding-number argument with that definition, so the exact results for the two
repeated evaluations remain `sorry`. -/
theorem proposition11_finite
    (G : StageGame Bool)
    [∀ who, Fintype (G.Action who)]
    [∀ who, DecidableEq (G.Action who)]
    {n : ℕ} (hn : 0 < n) :
    IsSimplyConnected (G.finiteFeasiblePayoffsAt n) := by
  sorry

theorem proposition11_discounted
    (G : StageGame Bool)
    [∀ who, Fintype (G.Action who)]
    [∀ who, DecidableEq (G.Action who)]
    {λ : ℝ} (hλ : 0 < λ ∧ λ ≤ 1) :
    IsSimplyConnected (G.discountedFeasiblePayoffsAt λ) := by
  sorry

/-! **Corollary 12(28).**  Proposition 7 or 9 first puts the whole boundary of
`C` in the smaller feasible set; Proposition 11 then excludes a hole.  The
formal proof awaits the planar boundary/fundamental-group bridge noted above. -/
theorem corollary12_discounted
    (G : StageGame Bool)
    [∀ who, Fintype (G.Action who)]
    [∀ who, DecidableEq (G.Action who)]
    {δ λ : ℝ} (hδ : 0 < δ) (hδλ : δ < λ) (hλ : λ ≤ 1)
    (hinclusion : G.discountedFeasiblePayoffsAt δ ⊆
      G.discountedFeasiblePayoffsAt λ) :
    G.discountedFeasiblePayoffsAt δ = G.correlatedFeasibleSet := by
  sorry

theorem corollary12_finite
    (G : StageGame Bool)
    [∀ who, Fintype (G.Action who)]
    [∀ who, DecidableEq (G.Action who)]
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hinclusion : G.finiteFeasiblePayoffsAt (n + m) ⊆
      G.finiteFeasiblePayoffsAt n) :
    G.finiteFeasiblePayoffsAt (n + m) =
      G.correlatedFeasibleSet := by
  sorry

/-- The open problem at the end of Section 2. -/
def HigherPlayerSimpleConnectednessQuestion : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    2 < Fintype.card ι →
    ∀ (G : StageGame ι) (n : ℕ), 0 < n →
      IsSimplyConnected (G.finiteFeasiblePayoffsAt n)


/-! ## Section 3: the Prisoner's Dilemma -/

/-- The Prisoner's Dilemma on page 156. -/
def prisonersDilemma : StageGame Bool :=
  twoByTwoGame (pair 4 4) (pair 0 5) (pair 5 0) (pair 1 1)

/-- The paper's square `S` at the critical discount. -/
def prisonersDilemmaCriticalSquare : Set (Bool → ℝ) :=
  {payoff | payoff false ∈ Set.Icc (1 : ℝ) 4 ∧
    payoff true ∈ Set.Icc (1 : ℝ) 4}

/-- The horizontal segment from `(4,1)` to `(19/4,1)`. -/
def prisonersDilemmaHorizontalArm : Set (Bool → ℝ) :=
  {payoff | payoff true = 1 ∧ payoff false ∈ Set.Icc (4 : ℝ) (19 / 4)}

/-- The vertical segment from `(1,4)` to `(1,19/4)`. -/
def prisonersDilemmaVerticalArm : Set (Bool → ℝ) :=
  {payoff | payoff false = 1 ∧ payoff true ∈ Set.Icc (4 : ℝ) (19 / 4)}

/-- The set `A` in Figure 1 and Proposition 15. -/
def prisonersDilemmaCriticalSet : Set (Bool → ℝ) :=
  prisonersDilemmaCriticalSquare ∪
    prisonersDilemmaHorizontalArm ∪ prisonersDilemmaVerticalArm

/-- The one-stage feasible set is already the correlated feasible set.  This
is a finite convex-hull calculation; it is left `sorry` pending a reusable
`2×2` independent-product image computation. -/
theorem prisonersDilemma_D1_eq_C :
    prisonersDilemma.finiteFeasiblePayoffsAt 1 =
      prisonersDilemma.correlatedFeasibleSet := by
  sorry

/-- Hence every positive finite-horizon feasible set is `C`. -/
theorem prisonersDilemma_Dn_eq_C {n : ℕ} (hn : 0 < n) :
    prisonersDilemma.finiteFeasiblePayoffsAt n =
      prisonersDilemma.correlatedFeasibleSet := by
  have hconvex : Convex ℝ
      (prisonersDilemma.finiteFeasiblePayoffsAt 1) := by
    rw [prisonersDilemma_D1_eq_C]
    exact convex_convexHull ℝ prisonersDilemma.purePayoffSet
  exact (prisonersDilemma.proposition5 (n := 1) (by omega) hconvex).2
    n (by omega)

/-- The individually rational feasible set for the table is `C` cut by the
two lower bounds `x_i ≥ 1`.  The minmax calculation uses strict dominance and
is finite but awaits the same matrix evaluator as the preceding theorem. -/
theorem prisonersDilemma_Delta_eq :
    prisonersDilemma.individuallyRationalFeasibleSet =
      {payoff | payoff ∈ prisonersDilemma.correlatedFeasibleSet ∧
        1 ≤ payoff false ∧ 1 ≤ payoff true} := by
  sorry

/-- The unique one-stage equilibrium payoff is `(1,1)`. -/
theorem prisonersDilemma_E1_eq :
    prisonersDilemma.finiteEquilibriumPayoffsAt 1 = {pair 1 1} := by
  sorry

/-! **Proposition 13.**  If the one-stage Nash payoff set is a singleton
`{a}`, then every finite repeated Nash payoff set is the same singleton.
The proof is a last-nontrivial-stage argument, not merely subgame-perfect
backward induction.  Formalization needs finite-horizon continuation utilities
for arbitrary Nash profiles, which the monitoring library does not expose. -/
theorem proposition13
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : StageGame ι) {a : ι → ℝ}
    (hE1 : G.finiteEquilibriumPayoffsAt 1 = {a})
    {n : ℕ} (hn : 0 < n) :
    G.finiteEquilibriumPayoffsAt n = {a} := by
  sorry

/-- Every finitely repeated Prisoner's Dilemma has only `(1,1)` as a Nash
payoff. -/
theorem prisonersDilemma_En_eq {n : ℕ} (hn : 0 < n) :
    prisonersDilemma.finiteEquilibriumPayoffsAt n = {pair 1 1} :=
  proposition13 prisonersDilemma prisonersDilemma_E1_eq hn

/-! **Proposition 14.**  For current-stage weight `λ > 3/4`, every Nash payoff
is `(1,1)`.  Sorin's proof integrates a continuation inequality and takes the
supremum of expected total surplus.  The exact argument requires conditional
continuation payoffs at all positive-probability histories and a measurable
best-response selector; those interfaces are absent from the finite-support
monitoring layer. -/
theorem proposition14
    {λ : ℝ} (hλ : 3 / 4 < λ ∧ λ ≤ 1) :
    prisonersDilemma.discountedEquilibriumPayoffsAt λ = {pair 1 1} := by
  sorry

/-! **Proposition 15, first inclusion.**  Every point of `A` is achieved by an
explicit equilibrium at `λ=3/4`:

* `(4,4)` and `(1,1)` use constant play;
* `(4,1)` alternates `(5,0),(0,5),...`, and `(1,4)` is symmetric;
* a point `(4t+1-t,4s+1-s)` in the square mixes only in period one and selects
  one of those four continuations from the observed first-period outcome;
* `(4+3a/4,1)` plays `(5,0)` once and then uses `(1+3a,4)` in the square, with
  the vertical arm obtained symmetrically.

Checking these profiles against arbitrary public deviations is a finite-state
one-shot-deviation calculation.  The library theorem is available, but a
small finite-state strategy compiler from this description is not. -/
theorem proposition15_forward :
    prisonersDilemmaCriticalSet ⊆
      prisonersDilemma.discountedEquilibriumPayoffsAt (3 / 4) := by
  sorry

/-! **Proposition 15, reverse inclusion.**  The paper assumes an equilibrium
payoff `(a,b)` with `a>4`, `b>1`, defines optimal continuation payoffs after the
four first-stage outcomes, and produces another such payoff for which
`(a-4)(b-1)` grows by a factor exceeding four.  Boundedness gives the
contradiction.  Formalization needs attained continuation best responses and
the continuation-equilibrium property at every positive-probability outcome. -/
theorem proposition15_reverse :
    prisonersDilemma.discountedEquilibriumPayoffsAt (3 / 4) ⊆
      prisonersDilemmaCriticalSet := by
  sorry

/-- **Proposition 15.** `E_{3/4}=A`. -/
theorem proposition15 :
    prisonersDilemma.discountedEquilibriumPayoffsAt (3 / 4) =
      prisonersDilemmaCriticalSet :=
  Set.Subset.antisymm proposition15_reverse proposition15_forward

/-- The critical payoff set is connected and has affine dimension two, as
stated in the introduction.  This is elementary geometry of the square and
its two attached segments; the proof is deferred because no later result uses
it and a direct subtype homotopy would be substantially longer than the paper. -/
theorem prisonersDilemmaCriticalSet_connected_dimension_two :
    IsConnected prisonersDilemmaCriticalSet ∧
      affineDimension prisonersDilemmaCriticalSet = 2 := by
  sorry

/-- The critical equilibrium set differs from the individually rational
feasible set. -/
theorem prisonersDilemmaCriticalSet_ne_Delta :
    prisonersDilemmaCriticalSet ≠
      prisonersDilemma.individuallyRationalFeasibleSet := by
  sorry

/-- The finite equilibrium sets do not converge to `Δ`, as announced on page
148: they are constantly `{(1,1)}`, while `Δ` is larger. -/
theorem finiteEquilibriumPayoffs_do_not_converge_to_Delta :
    ¬ HausdorffConvergesAtTop
      prisonersDilemma.finiteEquilibriumPayoffsAt
      prisonersDilemma.individuallyRationalFeasibleSet := by
  sorry


/-! ## Concluding remarks -/

/-- The symmetric four-parameter table in concluding Remark 1. -/
def symmetricParametricGame (α β x : ℝ) : StageGame Bool :=
  twoByTwoGame
    (pair (β - x) (β - x)) (pair (α - x) β)
    (pair β (α - x)) (pair α α)

/-- Critical current-stage weight in concluding Remark 1. -/
def symmetricCriticalWeight (α β x : ℝ) : ℝ :=
  (β - α - x) / (β - α)

/-! **Concluding Remark 1.**  Under `β-x>α` and `x>0`, the analogue of
Proposition 14 has critical weight `(β-α-x)/(β-α)`.  The proof is the same
surplus recursion as Proposition 14, so it has the same missing conditional
continuation interface. -/
theorem concludingRemark1
    {α β x λ : ℝ} (hgap : α < β - x) (hx : 0 < x)
    (hλ : symmetricCriticalWeight α β x < λ ∧ λ ≤ 1) :
    (symmetricParametricGame α β x).discountedEquilibriumPayoffsAt λ =
      {pair α α} := by
  sorry

/-! **Concluding Remark 2.**  The paper says that the analogue of Proposition
15 can also be proved, at least when `β > max (1+α) (1+2x)`, but it does not
print the resulting payoff set.  No stronger formal statement is invented
here: the condition and scope are recorded at their paper location. -/
def ConcludingRemark2Condition (α β x : ℝ) : Prop :=
  max (1 + α) (1 + 2 * x) < β

/-- Weak Pareto dominance on a feasible set. -/
def ParetoDominates {ι : Type*} (better worse : ι → ℝ) : Prop :=
  (∀ who, worse who ≤ better who) ∧ ∃ who, worse who < better who

/-- Pareto boundary of a payoff set. -/
def ParetoBoundary {ι : Type*} (set : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {payoff | payoff ∈ set ∧
    ¬ ∃ better ∈ set, ParetoDominates better payoff}

/-! **Concluding Remark 3.**  For every `1/2<λ<3/4`, the equilibrium set has
countably infinitely many points on the Pareto boundary.  Sorin gives no
construction or proof in the paper, so this precise reading of “denumerably
many” is retained as an explained `sorry`. -/
theorem concludingRemark3
    {λ : ℝ} (hλ : 1 / 2 < λ ∧ λ < 3 / 4) :
    ∃ points : Set (Bool → ℝ),
      points ⊆
        prisonersDilemma.discountedEquilibriumPayoffsAt λ ∩
          ParetoBoundary prisonersDilemma.correlatedFeasibleSet ∧
      points.Countable ∧ points.Infinite := by
  sorry

/-- The asymmetric table in concluding Remark 4. -/
def asymmetricParametricGame (α β x y : ℝ) : StageGame Bool :=
  twoByTwoGame
    (pair (β - y) (β - y)) (pair (α - x) β)
    (pair β (α - x)) (pair α α)

/-- Critical current-stage weight in concluding Remark 4. -/
def asymmetricCriticalWeight (α β x y : ℝ) : ℝ :=
  max (β - α - x) (β - α - y) / (β - α)

/-- Discounted payoff of the deterministic alternating sequence
`first,second,first,second,...`. -/
def alternatingPayoff (λ : ℝ) (first second : Bool → ℝ) : Bool → ℝ :=
  (2 - λ)⁻¹ • first + ((1 - λ) / (2 - λ)) • second

/-! **Concluding Remark 4, threshold.**  Decreasing `x` or `y` preserves any
putative equilibrium above the threshold, reducing to Remark 1 and producing
a contradiction.  Formalization again needs the conditional equilibrium
comparison used in Proposition 14. -/
theorem concludingRemark4_above
    {α β x y λ : ℝ}
    (hgap : α < β - y) (hx : 0 < x) (hy : 0 < y)
    (hλ : asymmetricCriticalWeight α β x y < λ ∧ λ ≤ 1) :
    (asymmetricParametricGame α β x y).discountedEquilibriumPayoffsAt λ =
      {pair α α} := by
  sorry

/-! If `y>x`, the alternating off-diagonal sequence is an equilibrium at the
critical weight.  The paper states the strategy but not its payoff formula;
`alternatingPayoff` evaluates that sequence. -/
theorem concludingRemark4_alternating
    {α β x y : ℝ}
    (hgap : α < β - y) (hx : 0 < x) (hy : 0 < y) (hxy : x < y) :
    alternatingPayoff (asymmetricCriticalWeight α β x y)
        (pair β (α - x)) (pair (α - x) β) ∈
      (asymmetricParametricGame α β x y).discountedEquilibriumPayoffsAt
        (asymmetricCriticalWeight α β x y) := by
  sorry

/-! If `x>y`, stationary play at the upper-left outcome is an equilibrium at
the critical weight. -/
theorem concludingRemark4_stationary
    {α β x y : ℝ}
    (hgap : α < β - y) (hx : 0 < x) (hy : 0 < y) (hyx : y < x) :
    pair (β - y) (β - y) ∈
      (asymmetricParametricGame α β x y).discountedEquilibriumPayoffsAt
        (asymmetricCriticalWeight α β x y) := by
  sorry

/-! The paper closes by noting that an explicit computation of the entire
critical equilibrium set in the asymmetric game is more delicate; it makes no
claim beyond the threshold and the two displayed equilibrium constructions. -/

end Literature.Sorin1986
