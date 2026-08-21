import Literature.Simon2007
import MathUE.BonferroniProductBounds
import MathUE.LinearAlgebra.UniformNonsingularity
import MathUE.PMFProduct.TotalVariation
import MathUE.ProbabilityMassFunction.Simplex
import UniformEquilibrium.Quitting.Root.HazardProfileBridge
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEndpointDefectPolarity
import UniformEquilibrium.Quitting.Classification.Existence.QuietWindowStationaryRepair

/-!
# Robert Samuel Simon, *A Topological Approach to Quitting Games* (2012)

R. S. Simon, *A Topological Approach to Quitting Games*, Mathematics of
Operations Research **37**(1), 180--195 (2012), DOI
`10.1287/moor.1110.0524`.

This file follows the paper in order.  The 2007 paper's model, quitting-game
payoffs, one-stage correspondences, and finite/infinite/extended orbit types
are reused from `Literature.Simon2007`; the definitions introduced or changed
in 2012 are stated here rather than silently identified with their 2007
predecessors.

Two corrections made explicitly on page 185 are controlling:

* Simon 2007, Lemma 5 needs *stationarily generated* approximate equilibria,
  not merely stationary approximate equilibria;
* its uniform motion parameter is valid on a fixed compact continuation set.
  In the displayed application the continuation vector is required to lie
  within distance one of the feasible set.

The source leaves the symbol `δ` free in the definitions of stationarily
generated and instant approximate equilibria.  We therefore first define the
notions at a fixed punishment accuracy `δ`, and then use the arbitrarily-small
`δ` closure in the numbered results.  This is the quantification used by the
compactness argument immediately following Lemma 2.1; it is not hidden in
prose.

The paper uses the Euclidean two-norm on `ℝᴺ`.  Every quantitative distance,
motion, matrix, and variation statement below therefore uses the explicit
`EuclideanNorm`, `EuclideanDist`, or `EuclideanInfDist` defined
in this file.  The inherited finite-product topology is used only for purely
topological notions; in finite dimension it is the same topology.

A `sorry` below is preceded by the exact missing argument.  In particular, the
large 2007 and 2012 correspondence/orbit theorems are not treated as proved
merely because their statements already occur elsewhere in the literature
lane.
-/

namespace Literature.Simon2012

open Literature.Simon2007
open Set Filter Matrix
open scoped BigOperators ENNReal Topology

noncomputable section

/-! ## 2. The model, the question, and the challenge -/

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

/-- The Euclidean two-norm on the paper's finite-dimensional payoff space. -/
def EuclideanNorm {N : Type} [Fintype N] (x : Payoff N) : ℝ := by
  classical
  exact Real.sqrt (∑ i, (x i) ^ 2)

/-- The paper's explicit Euclidean norm is the standard finite `L²` norm. -/
theorem euclideanNorm_eq_norm_toLp {N : Type} [Fintype N]
    (x : Payoff N) :
    EuclideanNorm x = ‖WithLp.toLp 2 x‖ := by
  classical
  simp only [EuclideanNorm, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]

/-- Euclidean distance on the paper's payoff space. -/
def EuclideanDist {N : Type} [Fintype N]
    (x y : Payoff N) : ℝ :=
  EuclideanNorm (x - y)

/-- Euclidean distance from a point to a set. -/
def EuclideanInfDist {N : Type} [Fintype N]
    (x : Payoff N) (S : Set (Payoff N)) : ℝ :=
  sInf (EuclideanDist x '' S)

/-- Unbounded total variation measured in the paper's Euclidean norm. -/
def HasUnboundedExtendedVariation {N : Type} [Fintype N]
    {F : Correspondence (Payoff N) (Payoff N)}
    (orbit : ExtendedOrbitData F) : Prop := by
  classical
  exact ∀ B : ℝ, ∃ J I : ℕ, B ≤
    Finset.sum (Finset.range J) (fun j =>
      Finset.sum (Finset.range I) fun i =>
        if ActiveSegment orbit.segmentCount j ∧
            SegmentIndex (orbit.segmentLength j) (i + 1)
        then EuclideanDist
          (orbit.point j (i + 1)) (orbit.point j i)
        else 0)

/-- The all-continue row. -/
def zeroQuitRow (G : QuittingGame) : QuitRow G := fun _ => 0

/-- The probability `q(p_{-j})` that some player other than `j` quits. -/
def OthersQuitProbability (G : QuittingGame) (p : QuitRow G)
    (j : G.Player) : ℝ := by
  classical
  exact 1 - ∏ k ∈ Finset.univ.erase j, (1 - (p k : ℝ))

/--
The 2012 normalization: `M ≥ 1`, every payoff lies in `[-M/3,M/3]`, and
three times every payoff difference is bounded by `M`.
-/
def IsSimonPayoffScale (G : QuittingGame) (M : ℝ) : Prop :=
  1 ≤ M ∧
    (∀ A n, |G.reward A n| ≤ M / 3) ∧
    ∀ A B n, 3 * |G.reward A n - G.reward B n| ≤ M

/-- The standing assumption `|N| ≥ 3` made at the start of Section 2.1. -/
def HasAtLeastThreePlayers (G : QuittingGame) : Prop :=
  3 ≤ Fintype.card G.Player

/-- The graph of a set-valued correspondence. -/
def correspondenceGraph {X Y : Type} (F : Correspondence X Y) : Set (X × Y) :=
  {z | z.2 ∈ F z.1}

/-- A graph, read as a correspondence in its first coordinate. -/
def graphCorrespondence {X : Type} (J : Set (X × X)) : Correspondence X X :=
  fun x => {y | (x, y) ∈ J}

/-- `E_ε` as the subset of continuation-vector/row pairs used in the paper. -/
def EpsilonEquilibriumGraph (G : QuittingGame) (ε : ℝ) :
    Set (Payoff G.Player × QuitRow G) :=
  correspondenceGraph (EpsilonRow G ε)

/-- `F_ε` as the subset of continuation/current-payoff pairs. -/
def EpsilonPayoffGraph (G : QuittingGame) (ε : ℝ) :
    Set (Payoff G.Player × Payoff G.Player) :=
  correspondenceGraph (FRow G ε)

/-- The paper's small-step subcorrespondence `J_δ`. -/
def SmallStepGraph {N : Type} [Fintype N]
    (J : Set (Payoff N × Payoff N)) (δ : ℝ) :
    Set (Payoff N × Payoff N) :=
  {z | z ∈ J ∧ EuclideanDist z.1 z.2 ≤ δ}

/-- A cluster point in the sense stated for extended orbits on page 182. -/
def IsExtendedOrbitClusterPoint {N : Type} [Fintype N]
    {F : Correspondence (Payoff N) (Payoff N)}
    (orbit : ExtendedOrbitData F) (z : Payoff N) : Prop :=
  ∃ segment point : ℕ → ℕ,
    (∀ m, ActiveSegment orbit.segmentCount (segment m)) ∧
    (∀ m, SegmentIndex (orbit.segmentLength (segment m)) (point m)) ∧
    Tendsto (fun m => orbit.point (segment m) (point m)) atTop (nhds z) ∧
    ((orbit.segmentCount = none ∧ Tendsto segment atTop atTop) ∨
      ∃ L, orbit.segmentCount = some L ∧ 0 < L ∧
        (∀ᶠ m in atTop, segment m = L - 1) ∧ Tendsto point atTop atTop)

/-! ### 2.2. The two topological questions -/

/-- Intrinsic contractibility of a subset, with the homotopy staying in it. -/
def IsContractibleSet {X : Type} [TopologicalSpace X] (C : Set X) : Prop :=
  ∃ center : C, ∃ h : C → UnitInterval → C,
    IsHomotopy h ∧ (∀ x, h x 0 = x) ∧ ∀ x, h x 1 = center

/-- A compact convex polytope of full ambient dimension. -/
def IsFullDimensionalCompactConvexPolytope {N : Type} [Fintype N]
    (C : Set (Payoff N)) : Prop :=
  IsCompact C ∧ Convex ℝ C ∧ (interior C).Nonempty ∧
    ∃ vertices : Finset (Payoff N),
      C = convexHull ℝ (↑vertices : Set (Payoff N))

/-- The fiber `G(x) = {y | (x,y) ∈ G}`. -/
def GraphFiber {X Y : Type} (G : Set (X × Y)) (x : X) : Set Y :=
  {y | (x, y) ∈ G}

/-- The terminal image `H(C,1)`. -/
def HomotopyTerminalImage {E : Type} (C : Set E)
    (H : E → UnitInterval → E × E) : Set (E × E) :=
  {z | ∃ x ∈ C, H x 1 = z}

/-- Straight-line homotopy on the subspace `C × [0,1]`. -/
def IsStraightLineOn {N : Type} [Fintype N] (C : Set (Payoff N))
    (H : Payoff N → UnitInterval → Payoff N × Payoff N) : Prop :=
  Continuous (fun z : C × UnitInterval => H z.1 z.2) ∧
    ∀ x ∈ C, ∀ t,
      H x t = (t : ℝ) • H x 1 + (1 - (t : ℝ)) • H x 0

/--
Question 1's seven hypotheses.  The explicit nonemptiness in condition (7)
implements the usual convention that the distance to the empty set is
infinite; `EuclideanInfDist` itself is real-valued.
-/
def Question1Hypotheses {N : Type} [Fintype N] {k : ℕ}
    (C : Set (Payoff N)) (piece : Fin k → Set (Payoff N))
    (H : Payoff N → UnitInterval → Payoff N × Payoff N)
    (V : Set (Payoff N)) (G J : Set (Payoff N × Payoff N)) : Prop :=
  0 < k ∧
  IsContractibleSet C ∧
  (∀ i, IsFullDimensionalCompactConvexPolytope (piece i)) ∧
  C = ⋃ i, piece i ∧
  IsStraightLineOn C H ∧
  (∀ x ∈ C, H x 0 = (x, x)) ∧
  (∀ x ∈ frontier C, ∀ t, H x t = (x, x)) ∧
  (∀ x, (x, x) ∈ HomotopyTerminalImage C H → x ∈ frontier C) ∧
  IsCompact V ∧ frontier C ⊆ interior V ∧
  IsCompact G ∧
  (∀ z ∈ G, z.1 ∈ V) ∧
  (∀ x ∈ V, IsContractibleSet (GraphFiber G x) ∧ x ∈ GraphFiber G x) ∧
  IsCompact J ∧ HomotopyTerminalImage C H ⊆ J ∧ G ⊆ J ∧
  ∃ ω : ℝ, 0 < ω ∧ SmallStepGraph J ω ⊆ G ∧
    ∀ x ∈ V, ∀ i,
      (frontier C ∩ piece i).Nonempty →
      EuclideanInfDist x (frontier C ∩ piece i) ≤ ω →
      ∃ y ∈ GraphFiber G x,
        EuclideanInfDist y (piece i) ≤
          EuclideanInfDist x (piece i) ∧
        ω ≤ EuclideanDist x y ∧ segment ℝ x y ⊆ GraphFiber G x

/-- The conclusion asked for in Question 1. -/
def Question1Conclusion {N : Type} [Fintype N]
    (J : Set (Payoff N × Payoff N)) : Prop :=
  ∃ orbit : ExtendedOrbitData (graphCorrespondence J),
    HasUnboundedExtendedVariation orbit

/-- An affirmative answer to Question 1, uniformly in its finite dimension. -/
def Question1Affirmative : Prop :=
  ∀ (N : Type) [Fintype N] [Nonempty N] (k : ℕ)
    (C : Set (Payoff N)) (piece : Fin k → Set (Payoff N))
    (H : Payoff N → UnitInterval → Payoff N × Payoff N)
    (V : Set (Payoff N)) (G J : Set (Payoff N × Payoff N)),
      Question1Hypotheses C piece H V G J → Question1Conclusion J

/-- A star-shaped full-dimensional set, in the elementary sense used in Question 2. -/
def IsFullDimensionalStarShaped {N : Type} [Fintype N]
    (C : Set (Payoff N)) : Prop :=
  (interior C).Nonempty ∧ ∃ center ∈ C, ∀ x ∈ C, segment ℝ center x ⊆ C

/-- An extremal point of a convex fiber. -/
def IsExtremalPoint {N : Type} [Fintype N] (S : Set (Payoff N))
    (x : Payoff N) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, ∀ z ∈ S, ∀ t : UnitInterval,
    0 < (t : ℝ) → (t : ℝ) < 1 →
    x = (t : ℝ) • y + (1 - (t : ℝ)) • z → y = x ∧ z = x

/-- Question 2's terminal graph `H(G,1)`. -/
def GraphHomotopyTerminalImage {E : Type} (G : Set (E × E))
    (H : (E × E) → UnitInterval → E × E) : Set (E × E) :=
  {z | ∃ g ∈ G, H g 1 = z}

/-- The four displayed hypotheses of Question 2. -/
def Question2Hypotheses {N : Type} [Fintype N]
    (C : Set (Payoff N)) (G : Set (Payoff N × Payoff N))
    (H : (Payoff N × Payoff N) → UnitInterval → Payoff N × Payoff N) : Prop :=
  IsFullDimensionalStarShaped C ∧
  IsCompact G ∧
  (∀ g ∈ G, g.1 ∈ C) ∧
  (∀ c ∈ C, (GraphFiber G c).Nonempty ∧ Convex ℝ (GraphFiber G c)) ∧
  (∀ c ∈ C, ∀ y, IsExtremalPoint (GraphFiber G c) y → y ∈ C) ∧
  Continuous (fun z : G × UnitInterval => H z.1 z.2) ∧
  (∀ g ∈ G, g.1 ∈ frontier C → ∀ t, H g t = g) ∧
  ∀ g ∈ G, H g 0 = g

/-- An affirmative answer to the simpler Question 2. -/
def Question2Affirmative : Prop :=
  ∀ (N : Type) [Fintype N] [Nonempty N]
    (C : Set (Payoff N)) (G : Set (Payoff N × Payoff N))
    (H : (Payoff N × Payoff N) → UnitInterval → Payoff N × Payoff N),
      Question2Hypotheses C G H →
        ∃ orbit : ℕ → Payoff N,
          IsInfiniteOrbit
            (graphCorrespondence (GraphHomotopyTerminalImage G H)) orbit

/-!
The paper reports that `Question2Affirmative` is false and points to a similar
Gobbino--Simon construction, but does not print it.  The external blueprint is
Gobbino--Simon, Example 4.9: in `ℝ²`, take the square `[0,2]²` with the segment
from `(2,0)` to `(3,0)` attached, use the convex segment from `(1,1)` to `(3,0)`
as the exceptional fiber at `(2,0)`, and send the remaining square points to
`(3, dist(·, ∂[0,2]²))`.  Adapting that upper-semicontinuous correspondence to
the displayed homotopy and proving that it has only four iterations are the
missing formal obligations; no claim in the present repository supplies them.
-/

/--
The paragraph after Question 2 says that adding
`(x,y) ∈ H(C,1) → x ∈ C` makes the conclusion of Question 1 provable by the
escape-game spanning argument.  That argument is not presently proved in the
literature lane: Simon 2007's spanning lemmas remain `sorry`.
-/
def Question1NoEscapeAffirmative : Prop :=
  ∀ (N : Type) [Fintype N] [Nonempty N] (k : ℕ)
    (C : Set (Payoff N)) (piece : Fin k → Set (Payoff N))
    (H : Payoff N → UnitInterval → Payoff N × Payoff N)
    (V : Set (Payoff N)) (G J : Set (Payoff N × Payoff N)),
      Question1Hypotheses C piece H V G J →
      (∀ z ∈ HomotopyTerminalImage C H, z.1 ∈ C) →
      Question1Conclusion J

/-!
The strengthened version discussed immediately after Question 2.  The omitted
proof is the escape-game spanning construction: it needs the Cech-homology
restriction and connected-component lemmas that remain `sorry` in
`Literature.Simon2007`, so no checked topological argument is currently
available to instantiate this statement.
-/

/-! ### 2.3. The challenge and the correction to Simon 2007 -/

/-- Use a fixed row through stage `M`, then switch to the punishment profile. -/
def StationaryPrefixThenPunish (G : QuittingGame) (p : QuitRow G)
    (M : ℕ) (punishment : QuitProfile G) : QuitProfile G :=
  fun t => if t ≤ M then p else punishment (t - (M + 1))

/-- The punishment profile holds player `j` to `χʲ + δ`. -/
def IsPunishmentWithin (G : QuittingGame) (j : G.Player) (δ : ℝ)
    (punishment : QuitProfile G) : Prop :=
  ∀ q : ℕ → UnitInterval,
    QuitPayoff G (punishment.replace G j q) j ≤ MinMaxQuit G j + δ

/-- The paper's stationarily generated notion at the displayed free `δ`. -/
def HasStationarilyGeneratedApproximateEquilibriaAt
    (G : QuittingGame) (δ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (p : QuitRow G) (M : ℕ) (j : G.Player)
    (punishment : QuitProfile G),
      1 < M ∧ IsPunishmentWithin G j δ punishment ∧
      IsQuitEpsilonEquilibrium G (ε + δ)
        (StationaryPrefixThenPunish G p M punishment)

/-- Arbitrarily accurate stationarily generated approximate equilibria. -/
def HasStationarilyGeneratedApproximateEquilibria (G : QuittingGame) : Prop :=
  ∀ δ : ℝ, 0 < δ → HasStationarilyGeneratedApproximateEquilibriaAt G δ

/-- The paper's instant notion at the displayed free `δ`. -/
def HasInstantApproximateEquilibriaAt (G : QuittingGame) (δ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (p : QuitRow G) (j : G.Player)
    (punishment : QuitProfile G),
      (p j : ℝ) = 1 ∧ IsPunishmentWithin G j δ punishment ∧
      IsQuitEpsilonEquilibrium G (δ + ε) (InstantProfile G p punishment)

/-- Arbitrarily accurate instant approximate equilibria. -/
def HasInstantApproximateEquilibria (G : QuittingGame) : Prop :=
  ∀ δ : ℝ, 0 < δ → HasInstantApproximateEquilibriaAt G δ

/-- An `ε`-equilibrium remains one when its tolerance is increased. -/
theorem isQuitEpsilonEquilibrium_mono {G : QuittingGame}
    {ε ε' : ℝ} {p : QuitProfile G}
    (h : IsQuitEpsilonEquilibrium G ε p) (hle : ε ≤ ε') :
    IsQuitEpsilonEquilibrium G ε' p := by
  intro n q
  exact (h n q).trans (by linarith)

/-- A punishment bound remains valid when its tolerance is increased. -/
theorem isPunishmentWithin_mono {G : QuittingGame} {j : G.Player}
    {δ δ' : ℝ} {punishment : QuitProfile G}
    (h : IsPunishmentWithin G j δ punishment) (hle : δ ≤ δ') :
    IsPunishmentWithin G j δ' punishment := by
  intro q
  exact (h q).trans (by linarith)

/--
The 2012 instant notion is equivalent to the 2007 `2ε` formulation.  This is a
checked quantifier adapter; it does not use any paper theorem.
-/
theorem instantApproximateEquilibria_iff_simon2007 (G : QuittingGame) :
    HasInstantApproximateEquilibria G ↔
      Literature.Simon2007.HasInstantApproximateEquilibria G := by
  constructor
  · intro h δ hδ
    obtain ⟨p, j, punishment, hpj, hpunish, heq⟩ := h δ hδ δ hδ
    exact ⟨p, j, punishment, hpj, hpunish, by
      simpa [two_mul, add_comm] using heq⟩
  · intro h δ hδ ε hε
    let η := min δ ((δ + ε) / 2)
    have hη : 0 < η := lt_min hδ (div_pos (add_pos hδ hε) (by norm_num))
    obtain ⟨p, j, punishment, hpj, hpunish, heq⟩ := h η hη
    refine ⟨p, j, punishment, hpj, ?_, ?_⟩
    · exact isPunishmentWithin_mono hpunish (min_le_left _ _)
    · apply isQuitEpsilonEquilibrium_mono heq
      dsimp [η]
      have hmin := min_le_right δ ((δ + ε) / 2)
      nlinarith

/-- A vector lies within distance one of the feasible set. -/
def WithinOneOfFeasible (G : QuittingGame) (r : Payoff G.Player) : Prop :=
  ∃ z, Feasible G z ∧ EuclideanDist r z ≤ 1

/-- The corrected uniform conclusion in Lemma 2.1(2). -/
def SatisfiesCorrectedLemma2_1Parameter (G : QuittingGame) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ ∀ r p,
    WithinOneOfFeasible G r → IsRational G ρ r →
    p ∈ EpsilonRow G ρ r →
      let y := QuittingOneStagePayoff G r p
      ρ * QuitProbability G p ≤ EuclideanDist r y ∧
        QuitProbability G p ≤ 1 - ρ

/-- At the scale selected under failure of instant approximate equilibria,
no rational approximate equilibrium row has a sure quitter. -/
def ExcludesSureRationalRowAt (G : QuittingGame) (ρ : ℝ) : Prop :=
  ∀ r p j, IsRational G ρ r → p ∈ EpsilonRow G ρ r → (p j : ℝ) ≠ 1

/-- Failure of instant approximate equilibria supplies a positive excluded
sure-quitter scale. -/
theorem exists_excludedSureRationalRowScale (G : QuittingGame)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    ∃ ρ : ℝ, 0 < ρ ∧ ExcludesSureRationalRowAt G ρ := by
  have hinstant2007 : ¬Literature.Simon2007.HasInstantApproximateEquilibria G :=
    fun hold => hinstant ((instantApproximateEquilibria_iff_simon2007 G).mpr hold)
  simpa only [ExcludesSureRationalRowAt] using
    Literature.Simon2007.exists_scale_without_sure_quitter_of_not_instant
      G hinstant2007

/-- The product norm is bounded by the paper's Euclidean norm. -/
private theorem norm_le_euclideanNorm {N : Type} [Fintype N] [Nonempty N]
    (x : Payoff N) : ‖x‖ ≤ EuclideanNorm x := by
  apply (pi_norm_le_iff_of_nonneg (show 0 ≤ EuclideanNorm x by
    exact Real.sqrt_nonneg _)).2
  intro i
  rw [euclideanNorm_eq_norm_toLp]
  simpa only [Real.norm_eq_abs] using
    PiLp.norm_apply_le (WithLp.toLp 2 x) i

/-- On a nonempty finite product, the Euclidean norm is at most `card` times the max norm. -/
private theorem euclideanNorm_le_card_mul_norm {N : Type} [Fintype N] [Nonempty N]
    (x : Payoff N) :
    EuclideanNorm x ≤ (Fintype.card N : ℝ) * ‖x‖ := by
  classical
  calc
    EuclideanNorm x ≤ ∑ i, |x i| := by
      rw [EuclideanNorm]
      rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
      rw [Real.sq_sqrt]
      · simpa only [sq_abs] using
          (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
            (f := fun i => |x i|) fun _ _ => abs_nonneg _)
      · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    _ ≤ (Fintype.card N : ℝ) * ‖x‖ := by
      simpa only [Real.norm_eq_abs, nsmul_eq_mul] using
        (Pi.sum_norm_apply_le_norm (f := x))

/--
Lemma 2.1(1), the sign-pattern clause of the corrected 2007 Lemma 5.
-/
theorem lemma2_1_part1 (G : QuittingGame)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    (∃ l, IsNormalPlayer G l ∧ 0 < SoloPayoff G l) ∧
      ∀ j, IsNormalPlayer G j → ∃ k, k ≠ j ∧ IsNormalPlayer G k ∧
        G.reward ⟨{j}, Finset.singleton_nonempty j⟩ k < SoloPayoff G k := by
  have hinstant2007 : ¬Literature.Simon2007.HasInstantApproximateEquilibria G :=
    fun hold => hinstant ((instantApproximateEquilibria_iff_simon2007 G).mpr hold)
  have hcorrected :=
    Literature.Simon2007.lemma5_corrected_2012 G hgenerated hinstant2007
  exact ⟨hcorrected.1, hcorrected.2.1⟩

/--
Lemma 2.1(2), with the two corrections printed on page 185.  Simon 2007's
`lemma5` declaration cannot prove this honestly: its hypothesis excludes only
stationary equilibria and its conclusion omits `WithinOneOfFeasible`.
The corrected 2012 declaration uses the distance-one feasible neighborhood;
the only adapter here is from the product norm to the paper's Euclidean norm.
-/
theorem lemma2_1_part2 (G : QuittingGame)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    ∃ ρ, SatisfiesCorrectedLemma2_1Parameter G ρ := by
  have hinstant2007 : ¬Literature.Simon2007.HasInstantApproximateEquilibria G :=
    fun hold => hinstant ((instantApproximateEquilibria_iff_simon2007 G).mpr hold)
  obtain ⟨_, _, ρ, hρ, hρ1, hbound⟩ :=
    Literature.Simon2007.lemma5_corrected_2012 G hgenerated hinstant2007
  refine ⟨ρ, hρ, hρ1.le, ?_⟩
  intro r p hnear hrational hp
  have hnear' : Literature.Simon2007.NearFeasible G 1 r := by
    obtain ⟨z, hz, hdist⟩ := hnear
    exact ⟨z, hz, (norm_le_euclideanNorm (r - z)).trans hdist⟩
  obtain ⟨hmotion, hquit⟩ := hbound r hnear' hrational p hp
  exact ⟨hmotion.trans (norm_le_euclideanNorm (r - QuittingOneStagePayoff G r p)),
    hquit⟩

/-- Lemma 2.1, combining its two corrected clauses. -/
theorem lemma2_1 (G : QuittingGame)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    ((∃ l, IsNormalPlayer G l ∧ 0 < SoloPayoff G l) ∧
      ∀ j, IsNormalPlayer G j → ∃ k, k ≠ j ∧ IsNormalPlayer G k ∧
        G.reward ⟨{j}, Finset.singleton_nonempty j⟩ k < SoloPayoff G k) ∧
      ∃ ρ, SatisfiesCorrectedLemma2_1Parameter G ρ := by
  exact ⟨lemma2_1_part1 G hgenerated hinstant,
    lemma2_1_part2 G hgenerated hinstant⟩

/-- The unnumbered compact-set assertion in the correction paragraph after Lemma 2.1. -/
def SatisfiesCompactMotionBound (G : QuittingGame)
    (K : Set (Payoff G.Player)) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ r ∈ K, ∀ p,
    IsRational G ρ r → p ∈ EpsilonRow G ρ r →
      let y := QuittingOneStagePayoff G r p
      ρ * QuitProbability G p ≤ EuclideanDist r y ∧
        QuitProbability G p ≤ 1 - ρ

/--
The correction paragraph says the proof of the old Lemma 5(2) works on each
fixed compact continuation set, with the parameter depending on that set.
This unnumbered assertion is used below only for the singleton `{r}` in
Lemma 2.3.
-/
theorem lemma2_1_part2_compact (G : QuittingGame)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (K : Set (Payoff G.Player)) (hK : IsCompact K) :
    SatisfiesCompactMotionBound G K := by
  sorry

/-- A vector lies within Euclidean distance `ε` of the feasible vectors. -/
def NearFeasible (G : QuittingGame) (ε : ℝ)
    (r : Payoff G.Player) : Prop :=
  ∃ z, Feasible G z ∧ EuclideanDist r z ≤ ε

/-- Euclidean total variation of a finite vector sequence. -/
def FiniteOrbitVariation {N : Type} [Fintype N] {k : ℕ}
    (x : Fin (k + 1) → Payoff N) : ℝ :=
  ∑ i : Fin k, EuclideanDist (x i.succ) (x i.castSucc)

/-- Theorem 2.1(iii), with the paper's Euclidean norm. -/
def FiniteNearOrbitCondition (G : QuittingGame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ B : ℝ, 1 < B → ∃ (k : ℕ)
    (x : Fin (k + 1) → Payoff G.Player),
      IsFiniteOrbit (FRow G ε) x ∧
      (∀ i, IsRational G ε (x i) ∧ NearFeasible G ε (x i)) ∧
      B ≤ FiniteOrbitVariation x

/-- Unbounded Euclidean variation of an infinite orbit. -/
def HasUnboundedVariation {N : Type} [Fintype N]
    (x : ℕ → Payoff N) : Prop :=
  ∀ B : ℝ, ∃ k,
    B ≤ ∑ i ∈ Finset.range k, EuclideanDist (x (i + 1)) (x i)

/-- Theorem 2.1(iv), with the paper's Euclidean norm. -/
def InfiniteOrbitCondition (G : QuittingGame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x : ℕ → Payoff G.Player,
    IsInfiniteOrbit (FRow G ε) x ∧
      (∀ i, IsRational G ε (x i)) ∧ HasUnboundedVariation x

/-- Theorem 2.1(v), with the paper's Euclidean norm. -/
def ExtendedOrbitCondition (G : QuittingGame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x : ExtendedOrbitData (FRow G ε),
    (∀ j, ActiveSegment x.segmentCount j → ∀ i,
      SegmentIndex (x.segmentLength j) i → IsRational G ε (x.point j i)) ∧
    HasUnboundedExtendedVariation x

private theorem positive_card (G : QuittingGame) :
    0 < (Fintype.card G.Player : ℝ) := by
  exact_mod_cast Fintype.card_pos

private theorem one_le_card (G : QuittingGame) :
    1 ≤ (Fintype.card G.Player : ℝ) := by
  exact_mod_cast Fintype.card_pos

private theorem finiteVariation_simon2007_le_euclidean
    {N : Type} [Fintype N] [Nonempty N] {k : ℕ}
    (x : Fin (k + 1) → Payoff N) :
    Literature.Simon2007.FiniteOrbitVariation x ≤ FiniteOrbitVariation x := by
  apply Finset.sum_le_sum
  intro i _
  exact norm_le_euclideanNorm _

private theorem finiteVariation_euclidean_le_card_mul
    {N : Type} [Fintype N] [Nonempty N] {k : ℕ}
    (x : Fin (k + 1) → Payoff N) :
    FiniteOrbitVariation x ≤
      (Fintype.card N : ℝ) * Literature.Simon2007.FiniteOrbitVariation x := by
  calc
    FiniteOrbitVariation x ≤
        ∑ i : Fin k, (Fintype.card N : ℝ) * ‖x i.succ - x i.castSucc‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact euclideanNorm_le_card_mul_norm _
    _ = (Fintype.card N : ℝ) *
        Literature.Simon2007.FiniteOrbitVariation x := by
      rw [Literature.Simon2007.FiniteOrbitVariation, Finset.mul_sum]

private theorem unboundedVariation_simon2007_to_euclidean
    {N : Type} [Fintype N] [Nonempty N] {x : ℕ → Payoff N}
    (h : Literature.Simon2007.HasUnboundedVariation x) :
    HasUnboundedVariation x := by
  intro B
  obtain ⟨k, hk⟩ := h B
  refine ⟨k, hk.trans ?_⟩
  apply Finset.sum_le_sum
  intro i _
  exact norm_le_euclideanNorm _

private theorem unboundedVariation_euclidean_to_simon2007
    {N : Type} [Fintype N] [Nonempty N] {x : ℕ → Payoff N}
    (h : HasUnboundedVariation x) :
    Literature.Simon2007.HasUnboundedVariation x := by
  intro B
  let c : ℝ := Fintype.card N
  have hc : 0 < c := by
    dsimp only [c]
    exact_mod_cast Fintype.card_pos
  obtain ⟨k, hk⟩ := h (c * B)
  refine ⟨k, ?_⟩
  have hupper :
      (∑ i ∈ Finset.range k, EuclideanDist (x (i + 1)) (x i)) ≤
        c * ∑ i ∈ Finset.range k, ‖x (i + 1) - x i‖ := by
    calc
      (∑ i ∈ Finset.range k, EuclideanDist (x (i + 1)) (x i)) ≤
          ∑ i ∈ Finset.range k, c * ‖x (i + 1) - x i‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact euclideanNorm_le_card_mul_norm _
      _ = c * ∑ i ∈ Finset.range k, ‖x (i + 1) - x i‖ := by
        rw [Finset.mul_sum]
  nlinarith

private theorem unboundedExtendedVariation_simon2007_to_euclidean
    {N : Type} [Fintype N] [Nonempty N]
    {F : Correspondence (Payoff N) (Payoff N)} {x : ExtendedOrbitData F}
    (h : Literature.Simon2007.HasUnboundedExtendedVariation x) :
    HasUnboundedExtendedVariation x := by
  classical
  intro B
  obtain ⟨J, I, hJI⟩ := h B
  refine ⟨J, I, hJI.trans ?_⟩
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact norm_le_euclideanNorm _
  · exact le_rfl

private theorem unboundedExtendedVariation_euclidean_to_simon2007
    {N : Type} [Fintype N] [Nonempty N]
    {F : Correspondence (Payoff N) (Payoff N)} {x : ExtendedOrbitData F}
    (h : HasUnboundedExtendedVariation x) :
    Literature.Simon2007.HasUnboundedExtendedVariation x := by
  classical
  intro B
  let c : ℝ := Fintype.card N
  have hc : 0 < c := by
    dsimp only [c]
    exact_mod_cast Fintype.card_pos
  obtain ⟨J, I, hJI⟩ := h (c * B)
  refine ⟨J, I, ?_⟩
  have hupper :
      Finset.sum (Finset.range J) (fun j =>
        Finset.sum (Finset.range I) fun i =>
          if ActiveSegment x.segmentCount j ∧
              SegmentIndex (x.segmentLength j) (i + 1)
          then EuclideanDist (x.point j (i + 1)) (x.point j i)
          else 0) ≤
        c * Finset.sum (Finset.range J) (fun j =>
          Finset.sum (Finset.range I) fun i =>
            if ActiveSegment x.segmentCount j ∧
                SegmentIndex (x.segmentLength j) (i + 1)
            then ‖x.point j (i + 1) - x.point j i‖
            else 0) := by
    calc
      _ ≤ Finset.sum (Finset.range J) (fun j =>
          Finset.sum (Finset.range I) fun i =>
            c * if ActiveSegment x.segmentCount j ∧
                SegmentIndex (x.segmentLength j) (i + 1)
              then ‖x.point j (i + 1) - x.point j i‖
              else 0) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · exact euclideanNorm_le_card_mul_norm _
        · simp
      _ = _ := by
        rw [Finset.mul_sum]
        congr 1
        ext j
        rw [Finset.mul_sum]
  nlinarith

private theorem finiteNearOrbitCondition_iff_simon2007 (G : QuittingGame) :
    FiniteNearOrbitCondition G ↔
      Literature.Simon2007.FiniteNearOrbitCondition G := by
  let c : ℝ := Fintype.card G.Player
  have hc : 0 < c := positive_card G
  have hc1 : 1 ≤ c := one_le_card G
  constructor
  · intro h ε hε B hB
    obtain ⟨k, x, horbit, hpoints, hvariation⟩ := h ε hε (c * B) (by nlinarith)
    refine ⟨k, x, horbit, ?_, ?_⟩
    · intro i
      exact ⟨hpoints i |>.1, by
        obtain ⟨z, hz, hdist⟩ := (hpoints i).2
        exact ⟨z, hz, (norm_le_euclideanNorm _).trans hdist⟩⟩
    · have hupper := finiteVariation_euclidean_le_card_mul x
      nlinarith
  · intro h ε hε B hB
    let δ := ε / c
    have hδ : 0 < δ := div_pos hε hc
    have hδε : δ ≤ ε := by
      dsimp only [δ]
      rw [div_le_iff₀ hc]
      nlinarith
    obtain ⟨k, x, horbit, hpoints, hvariation⟩ := h δ hδ B hB
    refine ⟨k, x, ?_, ?_, hvariation.trans (finiteVariation_simon2007_le_euclidean x)⟩
    · intro i
      exact FRow.mono G hδε _ (horbit i)
    · intro i
      refine ⟨fun n => (show MinMaxQuit G n - ε ≤ MinMaxQuit G n - δ by
        linarith) |>.trans ((hpoints i).1 n), ?_⟩
      obtain ⟨z, hz, hdist⟩ := (hpoints i).2
      refine ⟨z, hz, (euclideanNorm_le_card_mul_norm _).trans ?_⟩
      change c * ‖x i - z‖ ≤ ε
      calc
        c * ‖x i - z‖ ≤ c * (ε / c) :=
          mul_le_mul_of_nonneg_left hdist hc.le
        _ = ε := by field_simp

private theorem infiniteOrbitCondition_iff_simon2007 (G : QuittingGame) :
    InfiniteOrbitCondition G ↔ Literature.Simon2007.InfiniteOrbitCondition G := by
  constructor
  · intro h ε hε
    obtain ⟨x, horbit, hrational, hvariation⟩ := h ε hε
    exact ⟨x, horbit, hrational,
      unboundedVariation_euclidean_to_simon2007 hvariation⟩
  · intro h ε hε
    obtain ⟨x, horbit, hrational, hvariation⟩ := h ε hε
    exact ⟨x, horbit, hrational,
      unboundedVariation_simon2007_to_euclidean hvariation⟩

private theorem extendedOrbitCondition_iff_simon2007 (G : QuittingGame) :
    ExtendedOrbitCondition G ↔ Literature.Simon2007.ExtendedOrbitCondition G := by
  constructor
  · intro h ε hε
    obtain ⟨x, hrational, hvariation⟩ := h ε hε
    exact ⟨x, hrational,
      unboundedExtendedVariation_euclidean_to_simon2007 hvariation⟩
  · intro h ε hε
    obtain ⟨x, hrational, hvariation⟩ := h ε hε
    exact ⟨x, hrational,
      unboundedExtendedVariation_simon2007_to_euclidean hvariation⟩

/--
Theorem 2.1.  This is the corrected Simon 2007 five-way theorem transported
from the max norm to the paper's Euclidean norm by finite-dimensional norm
comparison.  Its remaining mathematical dependency is the corrected 2007
theorem itself.
-/
theorem theorem2_1 (G : QuittingGame)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    EquivalentFive (HasQuitApproximateEquilibria G) (CyclicOrbitCondition G)
      (FiniteNearOrbitCondition G) (InfiniteOrbitCondition G)
      (ExtendedOrbitCondition G) := by
  have hgenerated2007 :
      ¬Literature.Simon2007.HasStationarilyGeneratedApproximateEquilibria G := by
    intro hold
    apply hgenerated
    intro δ hδ
    exact hold δ hδ
  have hinstant2007 : ¬Literature.Simon2007.HasInstantApproximateEquilibria G :=
    fun hold => hinstant ((instantApproximateEquilibria_iff_simon2007 G).mpr hold)
  rw [finiteNearOrbitCondition_iff_simon2007,
    infiniteOrbitCondition_iff_simon2007,
    extendedOrbitCondition_iff_simon2007]
  exact Literature.Simon2007.theorem3_corrected_2012 G hgenerated2007 hinstant2007

/--
A positive bound on differences between all payoffs, including the zero
nontermination payoff, with Simon's standing normalization `1 ≤ B`.
-/
def IsPositivePayoffDifferenceBound (G : QuittingGame) (B : ℝ) : Prop :=
  IsQuittingPayoffDifferenceBound G B

/--
Lemma 2.2.  An `F_{ε²/(2B)}` step preserves `3ε`-rationality and otherwise
raises the coordinate by at least `ε²/(2B)`.
-/
theorem lemma2_2 (G : QuittingGame) {B ε : ℝ}
    (hB : IsPositivePayoffDifferenceBound G B)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (_hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (_hinstant : ¬HasInstantApproximateEquilibria G)
    (hε : 0 < ε) (hε1 : ε ≤ 1) {r s : Payoff G.Player}
    (hstep : s ∈ FRow G (ε ^ 2 / (2 * B)) r) :
    ∀ n,
      (r n ≥ MinMaxQuit G n - 3 * ε →
        s n ≥ MinMaxQuit G n - 3 * ε) ∧
      (r n < MinMaxQuit G n - 3 * ε →
        s n ≥ r n + ε ^ 2 / (2 * B)) := by
  exact Literature.Simon2007.lemma6_quantitative
    G hB hnormal hε hε1 hstep

/-- The unqualified Euclidean infinite-orbit condition in Theorem 2.2. -/
def InfiniteUnrestrictedOrbitCondition (G : QuittingGame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x : ℕ → Payoff G.Player,
    IsInfiniteOrbit (FRow G ε) x ∧ HasUnboundedVariation x

/-- Removing a finite prefix preserves unbounded Euclidean variation. -/
theorem HasUnboundedVariation.tail {N : Type} [Fintype N]
    {x : ℕ → Payoff N} (h : HasUnboundedVariation x) (start : ℕ) :
    HasUnboundedVariation (fun i => x (start + i)) := by
  intro bound
  let increment : ℕ → ℝ := fun i => EuclideanDist (x (i + 1)) (x i)
  let prefixVariation : ℝ := ∑ i ∈ Finset.range start, increment i
  rcases h (bound + prefixVariation) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hmono : (∑ i ∈ Finset.range k, increment i) ≤
      ∑ i ∈ Finset.range (start + k), increment i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.le_add_left k start))
    intro i _ _
    exact Real.sqrt_nonneg _
  have hbound := hk.trans hmono
  rw [Finset.sum_range_add] at hbound
  dsimp only [prefixVariation, increment] at hbound ⊢
  simp only [Nat.add_assoc] at hbound
  simpa only [Nat.add_assoc] using (show bound ≤
    ∑ i ∈ Finset.range k,
      EuclideanDist (x (start + (i + 1))) (x (start + i)) by
        linarith)

/--
Theorem 2.2.  Rationality can be removed from the infinite-orbit condition by
discarding the finite prefix before every coordinate reaches its rationality
floor.
-/
theorem theorem2_2 (G : QuittingGame)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    HasQuitApproximateEquilibria G ↔
      InfiniteUnrestrictedOrbitCondition G := by
  have hfive := theorem2_1 G hgenerated hinstant
  have hequivalent : HasQuitApproximateEquilibria G ↔ InfiniteOrbitCondition G :=
    hfive.1.trans (hfive.2.1.trans hfive.2.2.1)
  constructor
  · intro hequilibrium ε hε
    obtain ⟨x, horbit, _, hvariation⟩ := hequivalent.mp hequilibrium ε hε
    exact ⟨x, horbit, hvariation⟩
  · intro hunrestricted
    apply hequivalent.mpr
    intro ε hε
    obtain ⟨B, hB⟩ := Literature.Simon2007.exists_quittingPayoffDifferenceBound G
    have hBpos : 0 < B := zero_lt_one.trans_le hB.1
    let a : ℝ := min (ε / 3) (1 / 2)
    have ha : 0 < a := lt_min (div_pos hε (by norm_num)) (by norm_num)
    have ha1 : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
    have h3a : 3 * a ≤ ε := by
      have := min_le_left (ε / 3) (1 / 2)
      linarith
    let δ : ℝ := a ^ 2 / (2 * B)
    have hδ : 0 < δ := div_pos (sq_pos_of_pos ha) (mul_pos (by norm_num) hBpos)
    have hδε : δ ≤ ε := by
      rw [div_le_iff₀ (mul_pos (by norm_num) hBpos)]
      have haHalf := min_le_right (ε / 3) (1 / 2)
      have haEps := min_le_left (ε / 3) (1 / 2)
      nlinarith [sq_nonneg a, hB.1]
    obtain ⟨x, horbit, hvariation⟩ := hunrestricted δ hδ
    have heventual : ∀ n : G.Player, ∃ cutoff, ∀ i, cutoff ≤ i →
        MinMaxQuit G n - 3 * a ≤ x i n := by
      intro n
      apply Literature.Simon2007.eventually_ge_of_drift_below hδ
      intro i
      exact lemma2_2 G hB hnormal hgenerated hinstant ha ha1 (horbit i) n
    choose cutoff hcutoff using heventual
    let start := ∑ n, cutoff n
    have hcutoffStart : ∀ n, cutoff n ≤ start := by
      intro n
      exact Finset.single_le_sum (fun i _ => Nat.zero_le (cutoff i))
        (Finset.mem_univ n)
    let y : ℕ → Payoff G.Player := fun i => x (start + i)
    refine ⟨y, ?_, ?_, ?_⟩
    · intro i
      apply FRow.mono G hδε
      simpa only [y, Nat.add_assoc] using horbit (start + i)
    · intro i n
      have hfloor := hcutoff n (start + i)
        ((hcutoffStart n).trans (Nat.le_add_right start i))
      dsimp only [y]
      linarith
    · exact hvariation.tail start

/-- The unqualified extended-orbit condition in Theorem 2.3. -/
def ExtendedUnrestrictedOrbitCondition (G : QuittingGame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ orbit : ExtendedOrbitData (FRow G ε),
    HasUnboundedExtendedVariation orbit

/-- Regard an extended orbit as an orbit of a larger correspondence. -/
private def ExtendedOrbitData.mono
    {X : Type} [TopologicalSpace X] {F H : Correspondence X X}
    (orbit : ExtendedOrbitData F) (hFH : ∀ x, F x ⊆ H x) :
    ExtendedOrbitData H where
  segmentCount := orbit.segmentCount
  segmentCountPositive := orbit.segmentCountPositive
  segmentLength := orbit.segmentLength
  segmentLengthPositive := orbit.segmentLengthPositive
  point := orbit.point
  step := fun j hj i hi => hFH _ (orbit.step j hj i hi)
  finiteStitch := orbit.finiteStitch
  infiniteStitch := orbit.infiniteStitch

private theorem ExtendedOrbitData.mono_unbounded
    {N : Type} [Fintype N]
    {F H : Correspondence (Payoff N) (Payoff N)}
    (orbit : ExtendedOrbitData F) (hFH : ∀ x, F x ⊆ H x)
    (hvariation : HasUnboundedExtendedVariation orbit) :
    HasUnboundedExtendedVariation (ExtendedOrbitData.mono orbit hFH) := by
  classical
  change ∀ B : ℝ, ∃ J I : ℕ, B ≤ _
  change ∀ B : ℝ, ∃ J I : ℕ, B ≤ _ at hvariation
  intro B
  obtain ⟨J, I, hJI⟩ := hvariation B
  exact ⟨J, I, hJI⟩

/-- Remove finitely many complete segments from an extended orbit. -/
private def ExtendedOrbitData.dropSegments
    {X : Type} [TopologicalSpace X] {F : Correspondence X X}
    (orbit : ExtendedOrbitData F) (start : ℕ)
    (hstart : ActiveSegment orbit.segmentCount start) : ExtendedOrbitData F := by
  let count := orbit.segmentCount.map fun total => total - start
  have active_shift : ∀ j, ActiveSegment count j →
      ActiveSegment orbit.segmentCount (start + j) := by
    intro j hj total htotal
    have hstartTotal := hstart total htotal
    have hcount : count = some (total - start) := by
      simp [count, htotal]
    have hjlt := hj (total - start) hcount
    omega
  refine {
    segmentCount := count
    segmentCountPositive := ?_
    segmentLength := fun j => orbit.segmentLength (start + j)
    segmentLengthPositive := ?_
    point := fun j i => orbit.point (start + j) i
    step := ?_
    finiteStitch := ?_
    infiniteStitch := ?_ }
  · intro remaining hremaining
    cases hcount : orbit.segmentCount with
    | none => simp [count, hcount] at hremaining
    | some total =>
        have hstartTotal := hstart total hcount
        have hsome : some (total - start) = some remaining := by
          simpa [count, hcount] using hremaining
        have hremainingEq : total - start = remaining := by
          exact Option.some.inj hsome
        omega
  · intro j hj k hk
    exact orbit.segmentLengthPositive (start + j) (active_shift j hj) k hk
  · intro j hj i hi
    exact orbit.step (start + j) (active_shift j hj) i hi
  · intro j hj k hk
    have hactive := active_shift (j + 1) hj
    simpa only [Nat.add_assoc] using orbit.finiteStitch (start + j) hactive k hk
  · intro j hj hk
    have hactive := active_shift (j + 1) hj
    simpa only [Nat.add_assoc] using orbit.infiniteStitch (start + j) hactive hk

@[simp] private theorem ExtendedOrbitData.dropSegments_segmentLength
    {X : Type} [TopologicalSpace X] {F : Correspondence X X}
    (orbit : ExtendedOrbitData F) (start : ℕ)
    (hstart : ActiveSegment orbit.segmentCount start) (j : ℕ) :
    (ExtendedOrbitData.dropSegments orbit start hstart).segmentLength j =
      orbit.segmentLength (start + j) := by
  rfl

@[simp] private theorem ExtendedOrbitData.dropSegments_point
    {X : Type} [TopologicalSpace X] {F : Correspondence X X}
    (orbit : ExtendedOrbitData F) (start : ℕ)
    (hstart : ActiveSegment orbit.segmentCount start) (j i : ℕ) :
    (ExtendedOrbitData.dropSegments orbit start hstart).point j i =
      orbit.point (start + j) i := by
  rfl

private theorem ExtendedOrbitData.dropSegments_active_iff
    {X : Type} [TopologicalSpace X] {F : Correspondence X X}
    (orbit : ExtendedOrbitData F) (start : ℕ)
    (hstart : ActiveSegment orbit.segmentCount start) (j : ℕ) :
    ActiveSegment
        (ExtendedOrbitData.dropSegments orbit start hstart).segmentCount j ↔
      ActiveSegment orbit.segmentCount (start + j) := by
  cases hcount : orbit.segmentCount with
  | none => simp [ActiveSegment, ExtendedOrbitData.dropSegments, hcount]
  | some total =>
      have hstartTotal : start < total := hstart total hcount
      have hnewCount :
          (ExtendedOrbitData.dropSegments orbit start hstart).segmentCount =
            some (total - start) := by
        simp [ExtendedOrbitData.dropSegments, hcount]
      constructor
      · intro hj remaining hremaining
        have htotalRemaining : total = remaining :=
          Option.some.inj hremaining
        subst remaining
        have hjlt := hj (total - start) hnewCount
        omega
      · intro hj remaining hremaining
        have hremainingEq : total - start = remaining :=
          Option.some.inj (hnewCount.symm.trans hremaining)
        subst remaining
        have hjlt := hj total rfl
        omega

private def extendedSegmentVariation
    {N : Type} [Fintype N]
    {F : Correspondence (Payoff N) (Payoff N)}
    (orbit : ExtendedOrbitData F) (j I : ℕ) : ℝ := by
  classical
  exact ∑ i ∈ Finset.range I,
    if ActiveSegment orbit.segmentCount j ∧
        SegmentIndex (orbit.segmentLength j) (i + 1)
    then EuclideanDist (orbit.point j (i + 1)) (orbit.point j i)
    else 0

private theorem extendedSegmentVariation_nonneg
    {N : Type} [Fintype N]
    {F : Correspondence (Payoff N) (Payoff N)}
    (orbit : ExtendedOrbitData F) (j I : ℕ) :
    0 ≤ extendedSegmentVariation orbit j I := by
  classical
  rw [extendedSegmentVariation]
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_rfl

private def HasBoundedSegmentVariation
    {N : Type} [Fintype N]
    {F : Correspondence (Payoff N) (Payoff N)}
    (orbit : ExtendedOrbitData F) (j : ℕ) : Prop :=
  ∃ bound : ℝ, ∀ I, extendedSegmentVariation orbit j I ≤ bound

private theorem hasBoundedSegmentVariation_of_finite
    {N : Type} [Fintype N]
    {F : Correspondence (Payoff N) (Payoff N)}
    (orbit : ExtendedOrbitData F) (j total : ℕ)
    (hlength : orbit.segmentLength j = some total) :
    HasBoundedSegmentVariation orbit j := by
  classical
  let term : ℕ → ℝ := fun i =>
    if ActiveSegment orbit.segmentCount j ∧
        SegmentIndex (orbit.segmentLength j) (i + 1)
    then EuclideanDist (orbit.point j (i + 1)) (orbit.point j i)
    else 0
  refine ⟨∑ i ∈ Finset.range total, term i, ?_⟩
  intro I
  let top := max I total
  have hI : I ≤ top := le_max_left _ _
  have htotal : total ≤ top := le_max_right _ _
  have hfirst : (∑ i ∈ Finset.range I, term i) ≤
      ∑ i ∈ Finset.range top, term i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hI)
    intro i _ _
    dsimp only [term]
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact le_rfl
  have hsecond : (∑ i ∈ Finset.range total, term i) =
      ∑ i ∈ Finset.range top, term i := by
    apply Finset.sum_subset (Finset.range_mono htotal)
    intro i hitop hinot
    have htotalLe : total ≤ i := Nat.le_of_not_gt (by simpa using hinot)
    dsimp only [term]
    rw [if_neg]
    intro hvalid
    have := hvalid.2 total hlength
    omega
  exact hfirst.trans_eq hsecond.symm

private theorem not_unbounded_of_eventually_zero_segments
    {N : Type} [Fintype N]
    {F : Correspondence (Payoff N) (Payoff N)}
    (orbit : ExtendedOrbitData F) (start : ℕ)
    (hbounded : ∀ j, j < start → HasBoundedSegmentVariation orbit j)
    (hzero : ∀ j, start ≤ j → ∀ I,
      extendedSegmentVariation orbit j I = 0) :
    ¬HasUnboundedExtendedVariation orbit := by
  classical
  let bound : ℕ → ℝ := fun j =>
    if hj : j < start then Classical.choose (hbounded j hj) else 0
  have hbound : ∀ j I, extendedSegmentVariation orbit j I ≤ bound j := by
    intro j I
    by_cases hj : j < start
    · simpa only [bound, dif_pos hj] using
        (Classical.choose_spec (hbounded j hj)) I
    · rw [hzero j (Nat.le_of_not_gt hj) I]
      simp [bound, hj]
  have hboundNonneg : ∀ j, 0 ≤ bound j := by
    intro j
    by_cases hj : j < start
    · have hzeroIndex := hbound j 0
      simpa [extendedSegmentVariation, bound, hj] using hzeroIndex
    · simp [bound, hj]
  let totalBound := ∑ j ∈ Finset.range start, bound j
  intro hvariation
  obtain ⟨J, I, hJI⟩ := hvariation (totalBound + 1)
  have hsumBound :
      (∑ j ∈ Finset.range J, extendedSegmentVariation orbit j I) ≤
        totalBound := by
    let top := max J start
    calc
      (∑ j ∈ Finset.range J, extendedSegmentVariation orbit j I) ≤
          ∑ j ∈ Finset.range J, bound j := by
        exact Finset.sum_le_sum fun j _ => hbound j I
      _ ≤ ∑ j ∈ Finset.range top, bound j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (le_max_left J start))
        intro j _ _
        exact hboundNonneg j
      _ = ∑ j ∈ Finset.range start, bound j := by
        symm
        apply Finset.sum_subset (Finset.range_mono (le_max_right J start))
        intro j _ hj
        have hstartj : start ≤ j := Nat.le_of_not_gt (by simpa using hj)
        simp [bound, Nat.not_lt_of_ge hstartj]
      _ = totalBound := rfl
  simpa only [extendedSegmentVariation] using
    (show ¬(totalBound + 1 ≤
      ∑ j ∈ Finset.range J, extendedSegmentVariation orbit j I) by
        linarith) hJI

private theorem segmentCount_eq_none_of_all_segments_bounded
    {N : Type} [Fintype N]
    {F : Correspondence (Payoff N) (Payoff N)}
    (orbit : ExtendedOrbitData F)
    (hbounded : ∀ j, ActiveSegment orbit.segmentCount j →
      HasBoundedSegmentVariation orbit j)
    (hvariation : HasUnboundedExtendedVariation orbit) :
    orbit.segmentCount = none := by
  cases hcount : orbit.segmentCount with
  | none => rfl
  | some total =>
      exfalso
      apply not_unbounded_of_eventually_zero_segments orbit total
      · intro j hj
        exact hbounded j (by simpa [ActiveSegment, hcount] using hj)
      · intro j hj I
        rw [extendedSegmentVariation]
        apply Finset.sum_eq_zero
        intro i hi
        rw [if_neg]
        intro hactive
        exact (Nat.not_lt_of_ge hj) (hactive.1 total hcount)
      · exact hvariation

private theorem finiteSegmentStepCount_unbounded
    {N : Type} [Fintype N]
    {F : Correspondence (Payoff N) (Payoff N)}
    (orbit : ExtendedOrbitData F) (size : ℕ → ℕ)
    (hcount : orbit.segmentCount = none)
    (hsize : ∀ j, orbit.segmentLength j = some (size j))
    (hvariation : HasUnboundedExtendedVariation orbit) :
    ∀ K, ∃ J, K ≤ ∑ j ∈ Finset.range J, (size j - 1) := by
  classical
  let steps : ℕ → ℕ := fun J => ∑ j ∈ Finset.range J, (size j - 1)
  have hmono : Monotone steps := by
    intro J L hJL
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hJL)
      (fun _ _ _ => Nat.zero_le _)
  by_contra hnot
  push Not at hnot
  obtain ⟨K, hK⟩ := hnot
  let values : Set ℕ := Set.range steps
  have hvaluesFinite : values.Finite := by
    apply Set.finite_Iio K |>.subset
    rintro value ⟨J, rfl⟩
    exact hK J
  have hvaluesNonempty : values.Nonempty := ⟨steps 0, ⟨0, rfl⟩⟩
  let valueFinset := hvaluesFinite.toFinset
  have hvalueFinsetNonempty : valueFinset.Nonempty := by
    obtain ⟨value, hvalue⟩ := hvaluesNonempty
    exact ⟨value, by
      simpa only [valueFinset, Set.Finite.mem_toFinset] using hvalue⟩
  let maximum := valueFinset.max' hvalueFinsetNonempty
  have hmaximumMem : maximum ∈ values := by
    have := valueFinset.max'_mem hvalueFinsetNonempty
    simpa only [maximum, valueFinset, Set.Finite.mem_toFinset] using this
  obtain ⟨start, hstart⟩ := hmaximumMem
  have heventually : ∀ j, start ≤ j → steps j = steps start := by
    intro j hj
    apply Nat.le_antisymm
    · rw [hstart]
      apply Finset.le_max'
      simpa only [valueFinset, Set.Finite.mem_toFinset] using
        (show steps j ∈ values from ⟨j, rfl⟩)
    · exact hmono hj
  have hsizeOne : ∀ j, start ≤ j → size j = 1 := by
    intro j hj
    have hnext := heventually (j + 1) (hj.trans (Nat.le_succ j))
    have hcurrent := heventually j hj
    have hrecurrence : steps (j + 1) = steps j + (size j - 1) := by
      simp [steps, Finset.sum_range_succ]
    have hpositive : 0 < size j :=
      orbit.segmentLengthPositive j (by simp [ActiveSegment, hcount])
        (size j) (hsize j)
    rw [hrecurrence, hcurrent] at hnext
    omega
  have hbounded : ∀ j, j < start → HasBoundedSegmentVariation orbit j := by
    intro j _
    exact hasBoundedSegmentVariation_of_finite orbit j (size j) (hsize j)
  apply not_unbounded_of_eventually_zero_segments orbit start hbounded
  · intro j hj I
    rw [extendedSegmentVariation]
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg]
    rintro ⟨_, hindex⟩
    have := hindex (size j) (hsize j)
    rw [hsizeOne j hj] at this
    omega
  · exact hvariation

private theorem extendedSegmentVariation_dropSegments
    {N : Type} [Fintype N]
    {F : Correspondence (Payoff N) (Payoff N)}
    (orbit : ExtendedOrbitData F) (start : ℕ)
    (hstart : ActiveSegment orbit.segmentCount start) (j I : ℕ) :
    extendedSegmentVariation
        (ExtendedOrbitData.dropSegments orbit start hstart) j I =
      extendedSegmentVariation orbit (start + j) I := by
  classical
  simp only [extendedSegmentVariation,
    ExtendedOrbitData.dropSegments_active_iff orbit start hstart j,
    ExtendedOrbitData.dropSegments_segmentLength,
    ExtendedOrbitData.dropSegments_point]

private theorem ExtendedOrbitData.dropSegments_unbounded_of_bounded_prefix
    {N : Type} [Fintype N]
    {F : Correspondence (Payoff N) (Payoff N)}
    (orbit : ExtendedOrbitData F) (start : ℕ)
    (hstart : ActiveSegment orbit.segmentCount start)
    (hbounded : ∀ j, j < start → HasBoundedSegmentVariation orbit j)
    (hvariation : HasUnboundedExtendedVariation orbit) :
    HasUnboundedExtendedVariation
      (ExtendedOrbitData.dropSegments orbit start hstart) := by
  classical
  let bound : ℕ → ℝ := fun j =>
    if hj : j < start then Classical.choose (hbounded j hj) else 0
  have hbound : ∀ j, j < start → ∀ I,
      extendedSegmentVariation orbit j I ≤ bound j := by
    intro j hj I
    simpa only [bound, dif_pos hj] using
      (Classical.choose_spec (hbounded j hj)) I
  have hboundNonneg : ∀ j, 0 ≤ bound j := by
    intro j
    by_cases hj : j < start
    · have hzero := hbound j hj 0
      simpa [extendedSegmentVariation] using hzero
    · simp [bound, hj]
  let prefixBound := ∑ j ∈ Finset.range start, bound j
  have prefix_upper : ∀ J, J ≤ start → ∀ I,
      (∑ j ∈ Finset.range J, extendedSegmentVariation orbit j I) ≤
        prefixBound := by
    intro J hJ I
    calc
      (∑ j ∈ Finset.range J, extendedSegmentVariation orbit j I) ≤
          ∑ j ∈ Finset.range J, bound j := by
        apply Finset.sum_le_sum
        intro j hj
        exact hbound j (Finset.mem_range.mp hj |>.trans_le hJ) I
      _ ≤ ∑ j ∈ Finset.range start, bound j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hJ)
        intro j _ _
        exact hboundNonneg j
      _ = prefixBound := rfl
  change ∀ B : ℝ, ∃ J I : ℕ, B ≤ _ at hvariation
  change ∀ B : ℝ, ∃ J I : ℕ, B ≤ _
  intro B
  let target := max B 0 + prefixBound + 1
  obtain ⟨J, I, hJIraw⟩ := hvariation target
  have hJI : target ≤
      ∑ j ∈ Finset.range J, extendedSegmentVariation orbit j I := by
    simpa only [extendedSegmentVariation] using hJIraw
  have hstartJ : start ≤ J := by
    by_contra hnot
    have hJstart : J ≤ start := Nat.le_of_lt (Nat.lt_of_not_ge hnot)
    have hupper := prefix_upper J hJstart I
    dsimp only [target] at hJI
    linarith [le_max_right B 0]
  have hsplit :
      (∑ j ∈ Finset.range J, extendedSegmentVariation orbit j I) =
        (∑ j ∈ Finset.range start, extendedSegmentVariation orbit j I) +
          ∑ j ∈ Finset.range (J - start),
            extendedSegmentVariation orbit (start + j) I := by
    conv_lhs => rw [← Nat.add_sub_of_le hstartJ]
    exact Finset.sum_range_add _ _ _
  have hprefix := prefix_upper start le_rfl I
  have hsuffix : B ≤ ∑ j ∈ Finset.range (J - start),
      extendedSegmentVariation orbit (start + j) I := by
    rw [hsplit] at hJI
    dsimp only [target] at hJI
    linarith [le_max_left B 0]
  refine ⟨J - start, I, ?_⟩
  change B ≤ ∑ j ∈ Finset.range (J - start),
    extendedSegmentVariation
      (ExtendedOrbitData.dropSegments orbit start hstart) j I
  simpa only [extendedSegmentVariation_dropSegments orbit start hstart] using hsuffix

/-- Start later inside an infinite first segment, retaining all later segments. -/
private def ExtendedOrbitData.dropFirstInfinitePrefix
    {X : Type} [TopologicalSpace X] {F : Correspondence X X}
    (orbit : ExtendedOrbitData F) (start : ℕ)
    (hlength : orbit.segmentLength 0 = none) : ExtendedOrbitData F where
  segmentCount := orbit.segmentCount
  segmentCountPositive := orbit.segmentCountPositive
  segmentLength := orbit.segmentLength
  segmentLengthPositive := orbit.segmentLengthPositive
  point
    | 0, i => orbit.point 0 (start + i)
    | j + 1, i => orbit.point (j + 1) i
  step := by
    intro j hj i hi
    cases j with
    | zero =>
        have hshift : SegmentIndex (orbit.segmentLength 0) (start + i + 1) := by
          intro k hk
          rw [hlength] at hk
          simp at hk
        simpa only [Nat.add_assoc] using orbit.step 0 hj (start + i) hshift
    | succ j => exact orbit.step (j + 1) hj i hi
  finiteStitch := by
    intro j hj k hk
    cases j with
    | zero => simp [hlength] at hk
    | succ j => exact orbit.finiteStitch (j + 1) hj k hk
  infiniteStitch := by
    intro j hj hk
    cases j with
    | zero =>
        have hlimit := orbit.infiniteStitch 0 hj hlength
        simpa only [Function.comp_def, Nat.add_comm] using
          hlimit.comp (tendsto_add_atTop_nat start)
    | succ j => exact orbit.infiniteStitch (j + 1) hj hk

private theorem ExtendedOrbitData.dropFirstInfinitePrefix_extended_unbounded
    {N : Type} [Fintype N]
    {F : Correspondence (Payoff N) (Payoff N)} (orbit : ExtendedOrbitData F)
    (start : ℕ) (hlength : orbit.segmentLength 0 = none)
    (hvariation : HasUnboundedExtendedVariation orbit) :
    HasUnboundedExtendedVariation
      (ExtendedOrbitData.dropFirstInfinitePrefix orbit start hlength) := by
  classical
  let shifted := ExtendedOrbitData.dropFirstInfinitePrefix orbit start hlength
  let removedVariation := ∑ i ∈ Finset.range start,
    EuclideanDist (orbit.point 0 (i + 1)) (orbit.point 0 i)
  have hremoved : 0 ≤ removedVariation := by
    dsimp only [removedVariation]
    exact Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  have hactive : ActiveSegment orbit.segmentCount 0 := by
    intro total htotal
    have := orbit.segmentCountPositive total htotal
    omega
  have hfirst : ∀ I,
      extendedSegmentVariation orbit 0 I ≤
        extendedSegmentVariation shifted 0 I + removedVariation := by
    intro I
    have hmono :
        (∑ i ∈ Finset.range I,
          EuclideanDist (orbit.point 0 (i + 1)) (orbit.point 0 i)) ≤
        ∑ i ∈ Finset.range (start + I),
          EuclideanDist (orbit.point 0 (i + 1)) (orbit.point 0 i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.le_add_left I start))
      intro i _ _
      exact Real.sqrt_nonneg _
    rw [Finset.sum_range_add] at hmono
    simpa [extendedSegmentVariation, shifted,
      ExtendedOrbitData.dropFirstInfinitePrefix, SegmentIndex, hlength,
      hactive, removedVariation, Nat.add_assoc, add_comm] using hmono
  have hlater : ∀ j I, 0 < j →
      extendedSegmentVariation orbit j I =
        extendedSegmentVariation shifted j I := by
    intro j I hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    rfl
  intro B
  let target := max B 0 + removedVariation + 1
  obtain ⟨J, I, hJIraw⟩ := hvariation target
  have hJI : target ≤
      ∑ j ∈ Finset.range J, extendedSegmentVariation orbit j I := by
    simpa only [extendedSegmentVariation] using hJIraw
  have hsum :
      (∑ j ∈ Finset.range J, extendedSegmentVariation orbit j I) ≤
        (∑ j ∈ Finset.range J, extendedSegmentVariation shifted j I) +
          removedVariation := by
    calc
      (∑ j ∈ Finset.range J, extendedSegmentVariation orbit j I) ≤
          ∑ j ∈ Finset.range J,
            (extendedSegmentVariation shifted j I +
              if j = 0 then removedVariation else 0) := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hj0 : j = 0
        · subst j
          simpa using hfirst I
        · simp only [hj0, ↓reduceIte, add_zero]
          exact (hlater j I (Nat.pos_of_ne_zero hj0)).le
      _ = (∑ j ∈ Finset.range J, extendedSegmentVariation shifted j I) +
          ∑ j ∈ Finset.range J, if j = 0 then removedVariation else 0 := by
        rw [Finset.sum_add_distrib]
      _ ≤ (∑ j ∈ Finset.range J, extendedSegmentVariation shifted j I) +
          removedVariation := by
        gcongr
        by_cases hJ : J = 0
        · simp [hJ, hremoved]
        · simp [Finset.sum_ite_eq', Nat.pos_of_ne_zero hJ]
  refine ⟨J, I, ?_⟩
  change B ≤ ∑ j ∈ Finset.range J, extendedSegmentVariation shifted j I
  dsimp only [target] at hJI
  linarith [le_max_left B 0]

private theorem exists_rational_extendedOrbit_of_firstInfinite
    (G : QuittingGame) {B a ε : ℝ}
    (hB : IsPositivePayoffDifferenceBound G B)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hsmall : a ^ 2 / (2 * B) ≤ ε)
    (orbit : ExtendedOrbitData (FRow G (a ^ 2 / (2 * B))))
    (hlength : orbit.segmentLength 0 = none)
    (hvariation : HasUnboundedExtendedVariation orbit) :
    ∃ tail : ExtendedOrbitData (FRow G ε),
      (∀ j, ActiveSegment tail.segmentCount j → ∀ i,
        SegmentIndex (tail.segmentLength j) i →
          IsRational G (3 * a) (tail.point j i)) ∧
      HasUnboundedExtendedVariation tail := by
  let δ := a ^ 2 / (2 * B)
  have hδ : 0 < δ := by
    have hBpos : 0 < B := zero_lt_one.trans_le hB.1
    exact div_pos (sq_pos_of_pos ha) (mul_pos (by norm_num) hBpos)
  have hactive : ActiveSegment orbit.segmentCount 0 := by
    intro total htotal
    have := orbit.segmentCountPositive total htotal
    omega
  have heventual : ∀ n : G.Player, ∃ cutoff, ∀ i, cutoff ≤ i →
      MinMaxQuit G n - 3 * a ≤ orbit.point 0 i n := by
    intro n
    apply Literature.Simon2007.eventually_ge_of_drift_below hδ
    intro i
    have hindex : SegmentIndex (orbit.segmentLength 0) (i + 1) := by
      simp [SegmentIndex, hlength]
    exact lemma2_2 G hB hnormal hgenerated hinstant ha ha1
      (orbit.step 0 hactive i hindex) n
  choose cutoff hcutoff using heventual
  let start := ∑ n, cutoff n
  have hcutoffStart : ∀ n, cutoff n ≤ start := by
    intro n
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (cutoff i))
      (Finset.mem_univ n)
  let shifted := ExtendedOrbitData.dropFirstInfinitePrefix orbit start hlength
  have hshiftedStart : IsRational G (3 * a) (shifted.point 0 0) := by
    intro n
    exact hcutoff n start (hcutoffStart n)
  have hrationalClosed : IsClosed {r | IsRational G (3 * a) r} := by
    have heq : {r | IsRational G (3 * a) r} =
        ⋂ n, {r | MinMaxQuit G n - 3 * a ≤ r n} := by
      ext r
      simp [IsRational]
    rw [heq]
    exact isClosed_iInter fun n => isClosed_le continuous_const (continuous_apply n)
  have hrationalForward : ∀ r ∈ {r | IsRational G (3 * a) r},
      FRow G (a ^ 2 / (2 * B)) r ⊆ {r | IsRational G (3 * a) r} := by
    intro r hr s hs n
    exact (lemma2_2 G hB hnormal hgenerated hinstant ha ha1 hs n).1 (hr n)
  have hstay : ExtendedOrbitStaysIn shifted {r | IsRational G (3 * a) r} :=
    extendedOrbitStaysIn_of_closed_forwardInvariant shifted _ hrationalClosed
      hrationalForward hshiftedStart
  let tail := ExtendedOrbitData.mono shifted fun r => FRow.mono G hsmall r
  refine ⟨tail, ?_, ?_⟩
  · intro j hj i hi
    exact hstay j hj i hi
  · apply ExtendedOrbitData.mono_unbounded
    exact ExtendedOrbitData.dropFirstInfinitePrefix_extended_unbounded orbit start
      hlength hvariation

private theorem exists_rational_extendedOrbit_of_all_finite
    (G : QuittingGame) {B a ε : ℝ}
    (hB : IsPositivePayoffDifferenceBound G B)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hsmall : a ^ 2 / (2 * B) ≤ ε)
    (orbit : ExtendedOrbitData (FRow G (a ^ 2 / (2 * B))))
    (hfinite : ∀ j, ActiveSegment orbit.segmentCount j →
      ∃ size, orbit.segmentLength j = some size)
    (hvariation : HasUnboundedExtendedVariation orbit) :
    ∃ tail : ExtendedOrbitData (FRow G ε),
      (∀ j, ActiveSegment tail.segmentCount j → ∀ i,
        SegmentIndex (tail.segmentLength j) i →
          IsRational G (3 * a) (tail.point j i)) ∧
      HasUnboundedExtendedVariation tail := by
  classical
  let δ := a ^ 2 / (2 * B)
  have hδ : 0 < δ := by
    have hBpos : 0 < B := zero_lt_one.trans_le hB.1
    exact div_pos (sq_pos_of_pos ha) (mul_pos (by norm_num) hBpos)
  have hallBounded : ∀ j, ActiveSegment orbit.segmentCount j →
      HasBoundedSegmentVariation orbit j := by
    intro j hj
    obtain ⟨size, hsize⟩ := hfinite j hj
    exact hasBoundedSegmentVariation_of_finite orbit j size hsize
  have hcount : orbit.segmentCount = none :=
    segmentCount_eq_none_of_all_segments_bounded orbit hallBounded hvariation
  have hallActive : ∀ j, ActiveSegment orbit.segmentCount j := by
    simp [ActiveSegment, hcount]
  have hsome : ∀ j, ∃ size, orbit.segmentLength j = some size :=
    fun j => hfinite j (hallActive j)
  choose size hsize using hsome
  let steps : ℕ → ℕ := fun J => ∑ j ∈ Finset.range J, (size j - 1)
  have hstepsUnbounded : ∀ K, ∃ J, K ≤ steps J := by
    simpa only [steps] using
      finiteSegmentStepCount_unbounded orbit size hcount hsize hvariation
  have hsizePositive : ∀ j, 0 < size j := by
    intro j
    exact orbit.segmentLengthPositive j (hallActive j) (size j) (hsize j)
  let threshold : G.Player → ℝ := fun n => MinMaxQuit G n - 3 * a
  have segment_growth : ∀ j,
      (∀ n, threshold n ≤ orbit.point j 0 n ∨
        orbit.point 0 0 n + (steps j : ℝ) * δ ≤ orbit.point j 0 n) →
      ∀ i, i < size j → ∀ n,
        threshold n ≤ orbit.point j i n ∨
          orbit.point 0 0 n + (steps j + i : ℕ) * δ ≤ orbit.point j i n := by
    intro j hstart i hi
    induction i with
    | zero =>
        simpa using hstart
    | succ i ih =>
        have hiPrevious : i < size j := by omega
        have hiIndex : SegmentIndex (orbit.segmentLength j) (i + 1) := by
          intro k hk
          have hkEq : size j = k := Option.some.inj ((hsize j).symm.trans hk)
          simpa [hkEq] using hi
        have hstep := orbit.step j (hallActive j) i hiIndex
        intro n
        obtain hthreshold | hgrowth := ih hiPrevious n
        · exact Or.inl ((lemma2_2 G hB hnormal hgenerated hinstant ha ha1
            hstep n).1 hthreshold)
        · by_cases hbelow : orbit.point j i n < threshold n
          · right
            have hdrift := (lemma2_2 G hB hnormal hgenerated hinstant ha ha1
              hstep n).2 hbelow
            change orbit.point j i n + δ ≤ orbit.point j (i + 1) n at hdrift
            norm_num [Nat.cast_add, Nat.cast_one] at hgrowth ⊢
            nlinarith
          · left
            exact (lemma2_2 G hB hnormal hgenerated hinstant ha ha1
              hstep n).1 (le_of_not_gt hbelow)
  have hgrowth : ∀ j i, i < size j → ∀ n,
      threshold n ≤ orbit.point j i n ∨
        orbit.point 0 0 n + (steps j + i : ℕ) * δ ≤ orbit.point j i n := by
    intro j
    induction j with
    | zero =>
        apply segment_growth 0
        intro n
        right
        simp [steps]
    | succ j ih =>
        have hlastIndex : size j - 1 < size j := by
          have := hsizePositive j
          omega
        have hlast := ih (size j - 1) hlastIndex
        apply segment_growth (j + 1)
        intro n
        have hstitch := orbit.finiteStitch j (hallActive (j + 1))
          (size j) (hsize j)
        have hstepsSucc : steps (j + 1) = steps j + (size j - 1) := by
          simp [steps, Finset.sum_range_succ]
        simpa only [hstitch, hstepsSucc] using hlast n
  have heventualBound : ∀ n : G.Player, ∃ cutoff : ℕ,
      threshold n ≤ orbit.point 0 0 n + cutoff * δ := by
    intro n
    obtain ⟨cutoff, hcutoff⟩ :=
      exists_nat_gt ((threshold n - orbit.point 0 0 n) / δ)
    refine ⟨cutoff, ?_⟩
    rw [div_lt_iff₀ hδ] at hcutoff
    nlinarith
  choose cutoff hcutoff using heventualBound
  let totalCutoff := ∑ n, cutoff n
  have hcutoffTotal : ∀ n, cutoff n ≤ totalCutoff := by
    intro n
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (cutoff i))
      (Finset.mem_univ n)
  obtain ⟨start, hstartSteps⟩ := hstepsUnbounded totalCutoff
  have hstartRational : IsRational G (3 * a) (orbit.point start 0) := by
    intro n
    obtain hthreshold | hgrowthAtStart := hgrowth start 0 (hsizePositive start) n
    · exact hthreshold
    · have hcutoffLe : (cutoff n : ℝ) ≤ steps start := by
        exact_mod_cast (hcutoffTotal n).trans hstartSteps
      have hscaled : (cutoff n : ℝ) * δ ≤ (steps start : ℝ) * δ :=
        mul_le_mul_of_nonneg_right hcutoffLe hδ.le
      norm_num at hgrowthAtStart
      nlinarith [hcutoff n, hscaled]
  have hrationalClosed : IsClosed {r | IsRational G (3 * a) r} := by
    have heq : {r | IsRational G (3 * a) r} =
        ⋂ n, {r | MinMaxQuit G n - 3 * a ≤ r n} := by
      ext r
      simp [IsRational]
    rw [heq]
    exact isClosed_iInter fun n => isClosed_le continuous_const (continuous_apply n)
  have hrationalForward : ∀ r ∈ {r | IsRational G (3 * a) r},
      FRow G (a ^ 2 / (2 * B)) r ⊆ {r | IsRational G (3 * a) r} := by
    intro r hr s hs n
    exact (lemma2_2 G hB hnormal hgenerated hinstant ha ha1 hs n).1 (hr n)
  let shifted := ExtendedOrbitData.dropSegments orbit start (hallActive start)
  have hstay : ExtendedOrbitStaysIn shifted {r | IsRational G (3 * a) r} :=
    extendedOrbitStaysIn_of_closed_forwardInvariant shifted _ hrationalClosed
      hrationalForward hstartRational
  let tail := ExtendedOrbitData.mono shifted fun r => FRow.mono G hsmall r
  refine ⟨tail, ?_, ?_⟩
  · intro j hj i hi
    exact hstay j hj i hi
  · apply ExtendedOrbitData.mono_unbounded
    apply ExtendedOrbitData.dropSegments_unbounded_of_bounded_prefix orbit start
      (hallActive start)
    · intro j _
      exact hallBounded j (hallActive j)
    · exact hvariation

/--
Theorem 2.3.  Removing rationality from an extended orbit uses Lemma 2.2 to
show eventual entry into, and permanence in, the rational region.  Infinite
segments are handled by discarding a finite prefix; when all segments are
finite, their cumulative number of genuine correspondence steps is unbounded.
-/
theorem theorem2_3 (G : QuittingGame)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    HasQuitApproximateEquilibria G ↔ ExtendedUnrestrictedOrbitCondition G := by
  classical
  have hfive := theorem2_1 G hgenerated hinstant
  have hequivalent : HasQuitApproximateEquilibria G ↔ ExtendedOrbitCondition G :=
    hfive.1.trans (hfive.2.1.trans (hfive.2.2.1.trans hfive.2.2.2))
  constructor
  · intro hequilibrium ε hε
    obtain ⟨orbit, _, hvariation⟩ := hequivalent.mp hequilibrium ε hε
    exact ⟨orbit, hvariation⟩
  · intro hunrestricted
    apply hequivalent.mpr
    intro ε hε
    obtain ⟨B, hB⟩ := Literature.Simon2007.exists_quittingPayoffDifferenceBound G
    have hBpos : 0 < B := zero_lt_one.trans_le hB.1
    let a : ℝ := min (ε / 3) (1 / 2)
    have ha : 0 < a := lt_min (div_pos hε (by norm_num)) (by norm_num)
    have ha1 : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
    have h3a : 3 * a ≤ ε := by
      have := min_le_left (ε / 3) (1 / 2)
      linarith
    let δ : ℝ := a ^ 2 / (2 * B)
    have hδ : 0 < δ := div_pos (sq_pos_of_pos ha) (mul_pos (by norm_num) hBpos)
    have hδε : δ ≤ ε := by
      rw [div_le_iff₀ (mul_pos (by norm_num) hBpos)]
      have haHalf := min_le_right (ε / 3) (1 / 2)
      have haEps := min_le_left (ε / 3) (1 / 2)
      nlinarith [sq_nonneg a, hB.1]
    obtain ⟨orbit, hvariation⟩ := hunrestricted δ hδ
    have htail : ∃ tail : ExtendedOrbitData (FRow G ε),
        (∀ j, ActiveSegment tail.segmentCount j → ∀ i,
          SegmentIndex (tail.segmentLength j) i →
            IsRational G (3 * a) (tail.point j i)) ∧
        HasUnboundedExtendedVariation tail := by
      by_cases hinfinite : ∃ j, ActiveSegment orbit.segmentCount j ∧
          orbit.segmentLength j = none
      · let first := Nat.find hinfinite
        have hfirst := Nat.find_spec hinfinite
        have hprefixFinite : ∀ j, j < first →
            ∃ size, orbit.segmentLength j = some size := by
          intro j hj
          have hjFind : j < Nat.find hinfinite := by simpa [first] using hj
          cases hlength : orbit.segmentLength j with
          | none =>
              exfalso
              exact Nat.find_min hinfinite hjFind ⟨by
                intro total htotal
                have := hfirst.1 total htotal
                omega, hlength⟩
          | some size => exact ⟨size, rfl⟩
        have hprefixBounded : ∀ j, j < first →
            HasBoundedSegmentVariation orbit j := by
          intro j hj
          obtain ⟨size, hsize⟩ := hprefixFinite j hj
          exact hasBoundedSegmentVariation_of_finite orbit j size hsize
        let shifted := ExtendedOrbitData.dropSegments orbit first hfirst.1
        have hshiftedVariation : HasUnboundedExtendedVariation shifted :=
          ExtendedOrbitData.dropSegments_unbounded_of_bounded_prefix orbit first
            hfirst.1 hprefixBounded hvariation
        have hshiftedLength : shifted.segmentLength 0 = none := by
          simpa [shifted] using hfirst.2
        exact exists_rational_extendedOrbit_of_firstInfinite G hB hnormal
          hgenerated hinstant ha ha1 hδε shifted hshiftedLength hshiftedVariation
      · push Not at hinfinite
        have hfinite : ∀ j, ActiveSegment orbit.segmentCount j →
            ∃ size, orbit.segmentLength j = some size := by
          intro j hj
          cases hlength : orbit.segmentLength j with
          | none => exact (hinfinite j hj hlength).elim
          | some size => exact ⟨size, rfl⟩
        exact exists_rational_extendedOrbit_of_all_finite G hB hnormal
          hgenerated hinstant ha ha1 hδε orbit hfinite hvariation
    obtain ⟨tail, hrational, htailVariation⟩ := htail
    refine ⟨tail, ?_, htailVariation⟩
    intro j hj i hi n
    have := hrational j hj i hi n
    linarith

/-- Lemma 2.3's pointwise small parameter. -/
def SatisfiesLemma2_3At (G : QuittingGame) (r : Payoff G.Player)
    (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ ∀ p, p ∈ EpsilonRow G ρ r →
    ρ * QuitProbability G p ≤
      EuclideanDist r (QuittingOneStagePayoff G r p)

/--
Lemma 2.3.  The quantifier is `∀ r, ∃ ρ`; a single global parameter is not
claimed.  Its proof combines the compact-set version of Lemma 2.1 with the
coordinate increase in Lemma 2.2.
-/
theorem lemma2_3 (G : QuittingGame)
    (M : ℝ) (_hM : IsSimonPayoffScale G M)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    ∀ r, ∃ ρ, SatisfiesLemma2_3At G r ρ := by
  intro r
  obtain ⟨κ, hκ, hκ1, hcompact⟩ := lemma2_1_part2_compact G hgenerated hinstant
    {r} isCompact_singleton
  obtain ⟨B, hB⟩ := Literature.Simon2007.exists_quittingPayoffDifferenceBound G
  let ε₀ : ℝ := κ / 3
  let ρ : ℝ := ε₀ ^ 2 / (2 * B)
  have hBpos : 0 < B := zero_lt_one.trans_le hB.1
  have hε₀ : 0 < ε₀ := div_pos hκ (by norm_num)
  have hε₀1 : ε₀ ≤ 1 := by
    dsimp only [ε₀]
    linarith
  have hρ : 0 < ρ := div_pos (sq_pos_of_pos hε₀) (mul_pos (by norm_num) hBpos)
  have hρ_le_κ : ρ ≤ κ := by
    have hκsquare : κ ^ 2 ≤ κ := by nlinarith
    have hdenominator : 6 ≤ 18 * B := by nlinarith [hB.1]
    dsimp only [ρ, ε₀]
    rw [div_pow]
    calc
      κ ^ 2 / 3 ^ 2 / (2 * B) = κ ^ 2 / (18 * B) := by ring
      _ ≤ κ ^ 2 / 6 := by
        exact div_le_div_of_nonneg_left (sq_nonneg κ) (by norm_num) hdenominator
      _ ≤ κ := by linarith
  refine ⟨ρ, hρ, hρ_le_κ.trans hκ1, ?_⟩
  intro p hp
  let y := QuittingOneStagePayoff G r p
  by_cases hrational : IsRational G κ r
  · have hpκ : p ∈ EpsilonRow G κ r :=
      EpsilonRow.mono G hρ_le_κ r hp
    have hmotion := hcompact r (Set.mem_singleton r) p hrational hpκ
    have hquitNonneg : 0 ≤ QuitProbability G p :=
      (quitProbability_mem_Icc G p).1
    exact (mul_le_mul_of_nonneg_right hρ_le_κ hquitNonneg).trans hmotion.1
  · simp only [IsRational, not_forall, not_le] at hrational
    obtain ⟨n, hn⟩ := hrational
    have hstep : y ∈ FRow G ρ r := ⟨p, hp, rfl⟩
    have hincrease :=
      (lemma2_2 G hB hnormal hgenerated hinstant hε₀ hε₀1 hstep n).2
        (by dsimp only [ε₀]; linarith)
    have hcoordinate : |(r - y) n| ≤ EuclideanDist r y := by
      rw [EuclideanDist, euclideanNorm_eq_norm_toLp]
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        PiLp.norm_apply_le (WithLp.toLp 2 (r - y)) n
    have hρcoordinate : ρ ≤ |(r - y) n| := by
      rw [Pi.sub_apply, abs_of_nonpos (by linarith)]
      linarith
    have hρdist : ρ ≤ EuclideanDist r y := hρcoordinate.trans hcoordinate
    have hquitUpper : QuitProbability G p ≤ 1 :=
      (quitProbability_mem_Icc G p).2
    exact (mul_le_of_le_one_right hρ.le hquitUpper).trans hρdist

/-! ## 3. The structure theorem for quitting games -/

/-- `W_j = {r | rʲ ≤ vʲ}`. -/
def Wj (G : QuittingGame) (j : G.Player) : Set (Payoff G.Player) :=
  {r | r j ≤ SoloPayoff G j}

/-- `W = ⋃_j W_j`. -/
theorem wSet_eq_iUnion (G : QuittingGame) :
    WSet G = ⋃ j, Wj G j := by
  ext r
  simp [WSet, Wj]

/-- `Ẽ₀` is the exact one-stage equilibrium graph with `q(p) < 1`. -/
def EZeroTilde (G : QuittingGame) : Set (Payoff G.Player × QuitRow G) :=
  {z | z.2 ∈ EpsilonRow G 0 z.1 ∧ QuitProbability G z.2 < 1}

/-- The map `φ : Ẽ₀ → ℝᴺ` from Section 3.2. -/
def Phi (G : QuittingGame) (M d : ℝ) : EZeroTilde G → Payoff G.Player := by
  classical
  exact fun z j =>
    QuittingOneStagePayoff G z.1.1 z.1.2 j -
      (5 * (Fintype.card G.Player : ℝ) * M / d) *
        ((z.1.2 j : ℝ) /
          (1 - (z.1.2 j : ℝ)) ^ Fintype.card G.Player) +
      M * ∑ k ∈ Finset.univ.erase j, (z.1.2 k : ℝ)

/-- The production Bernoulli root represented by a paper-local quitting row. -/
private abbrev quitRowMarginals (G : QuittingGame) (p : QuitRow G) :
    G.Player → PMF Bool :=
  GameTheory.quittingRootOfHazardRow p

@[simp] private theorem quitRowMarginals_true_toReal
    (G : QuittingGame) (p : QuitRow G) (n : G.Player) :
    ((quitRowMarginals G p n) true).toReal = (p n : ℝ) := by
  exact GameTheory.quittingRootOfHazardRow_true_toReal p n

@[simp] private theorem quitRowMarginals_false_toReal
    (G : QuittingGame) (p : QuitRow G) (n : G.Player) :
    ((quitRowMarginals G p n) false).toReal = 1 - (p n : ℝ) := by
  exact GameTheory.quittingRootOfHazardRow_false_toReal p n

@[simp] private theorem hazardOfRoot_quitRowMarginals
    (G : QuittingGame) (p : QuitRow G) :
    GameTheory.hazardOfRoot (quitRowMarginals G p) = fun n => (p n : ℝ) := by
  exact GameTheory.hazardOfRoot_quittingRootOfHazardRow p

private theorem coalitionProbability_eq_coalitionMass
    (G : QuittingGame) (p : QuitRow G) (A : Finset G.Player) :
    CoalitionProbability G p A =
      (by
        classical
        exact Math.PMFProduct.coalitionMass (fun n => (p n : ℝ)) A) := by
  classical
  simp only [CoalitionProbability]
  rw [Math.PMFProduct.coalitionMass, Finset.compl_eq_univ_sdiff]
  congr 1
  apply Finset.prod_congr
  · ext n
    simp
  · intro n hn
    rfl

private theorem quittingOneStagePayoff_eq_rootExpectedPayoff
    (G : QuittingGame) (r : Payoff G.Player) (p : QuitRow G) (n : G.Player) :
    QuittingOneStagePayoff G r p n =
      GameTheory.quittingRootExpectedPayoff G.reward r (quitRowMarginals G p) n := by
  classical
  change QuittingOneStagePayoff G r p n =
    GameTheory.quittingHazardOneStagePayoff G.reward r p n
  rw [GameTheory.quittingHazardOneStagePayoff_eq_expanded]
  unfold QuittingOneStagePayoff
  simp only [QuitProbability, GameTheory.quittingHazardRowExitProbability]
  congr 1
  apply Finset.sum_congr rfl
  intro A _
  by_cases hA : A.Nonempty
  · simp only [hA, ↓reduceDIte]
    rw [coalitionProbability_eq_coalitionMass]
    rfl
  · simp [hA]

private theorem quitRowMarginals_replace_one (G : QuittingGame)
    [DecidableEq G.Player] (p : QuitRow G) (n : G.Player) :
    quitRowMarginals G (p.replace G n 1) =
      Function.update (quitRowMarginals G p) n (PMF.pure true) := by
  classical
  funext k
  by_cases hkn : k = n
  · subst k
    rw [Function.update_self]
    apply Math.ProbabilityMassFunction.toVector_injective
    funext value
    cases value <;>
      simp [quitRowMarginals, QuitRow.replace,
        Math.ProbabilityMassFunction.toVector]
  · rw [Function.update_of_ne hkn]
    apply GameTheory.quittingRootOfHazardRow_apply_congr
    simp [QuitRow.replace, hkn]

private theorem quitRowMarginals_replace_zero (G : QuittingGame)
    [DecidableEq G.Player] (p : QuitRow G) (n : G.Player) :
    quitRowMarginals G (p.replace G n 0) =
      Function.update (quitRowMarginals G p) n (PMF.pure false) := by
  classical
  funext k
  by_cases hkn : k = n
  · subst k
    rw [Function.update_self]
    apply Math.ProbabilityMassFunction.toVector_injective
    funext value
    cases value <;>
      simp [quitRowMarginals, QuitRow.replace,
        Math.ProbabilityMassFunction.toVector]
  · rw [Function.update_of_ne hkn]
    apply GameTheory.quittingRootOfHazardRow_apply_congr
    simp [QuitRow.replace, hkn]

/-- Total variation between two Bernoulli quitting marginals is the absolute
difference of their hazards. -/
private theorem pmfTV_quitRowMarginals_apply (G : QuittingGame)
    (p q : QuitRow G) (n : G.Player) :
    Math.Probability.pmfTV (quitRowMarginals G p n)
      (quitRowMarginals G q n) = |(p n : ℝ) - (q n : ℝ)| := by
  change Math.Probability.pmfPositiveVariation (quitRowMarginals G p n)
      (quitRowMarginals G q n) = _
  rw [Math.Probability.pmfPositiveVariation_eq_half_sum_abs]
  rw [Fintype.sum_bool]
  simp only [quitRowMarginals_true_toReal, quitRowMarginals_false_toReal]
  rw [show |(1 - (p n : ℝ)) - (1 - (q n : ℝ))| =
      |(p n : ℝ) - (q n : ℝ)| by
        rw [show (1 - (p n : ℝ)) - (1 - (q n : ℝ)) =
          -((p n : ℝ) - (q n : ℝ)) by ring, abs_neg]]
  ring

/-- Forcing Quit under uniformly close rows changes the terminal expectation
by at most the product-law total-variation estimate. -/
private theorem abs_forcedQuitPayoff_sub_le_of_row_close
    (G : QuittingGame) (M t : ℝ) (hM : IsSimonPayoffScale G M)
    (p q : QuitRow G) (n : G.Player)
    (hclose : ∀ k, |(p k : ℝ) - (q k : ℝ)| ≤ t) :
    |ForcedQuitPayoff G p n - ForcedQuitPayoff G q n| ≤
      (2 * (M / 3)) * (Fintype.card G.Player : ℝ) * t := by
  classical
  let rootP := Function.update (quitRowMarginals G p) n (PMF.pure true)
  let rootQ := Function.update (quitRowMarginals G q) n (PMF.pure true)
  have ht : 0 ≤ t := (abs_nonneg ((p n : ℝ) - (q n : ℝ))).trans (hclose n)
  have hM0 : 0 ≤ M := zero_le_one.trans hM.1
  have htv :
      Math.Probability.pmfTV (Math.PMFProduct.pmfPi rootP)
          (Math.PMFProduct.pmfPi rootQ) ≤
        (Fintype.card G.Player : ℝ) * t := by
    have hproduct := Math.PMFProduct.pmfTV_pmfPi_replaceOn_le_sum
      rootP rootQ (Finset.univ : Finset G.Player)
    simp only [Finset.mem_univ, ↓reduceIte] at hproduct
    refine hproduct.trans ?_
    calc
      ∑ k, Math.Probability.pmfTV (rootP k) (rootQ k) ≤
          ∑ _k : G.Player, t := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hkn : k = n
        · subst k
          simpa [rootP, rootQ] using ht
        · simp only [rootP, rootQ]
          rw [Function.update_of_ne hkn, Function.update_of_ne hkn]
          rw [pmfTV_quitRowMarginals_apply]
          exact hclose k
      _ = (Fintype.card G.Player : ℝ) * t := by simp
  rw [ForcedQuitPayoff, ForcedQuitPayoff,
    quittingOneStagePayoff_eq_rootExpectedPayoff,
    quittingOneStagePayoff_eq_rootExpectedPayoff,
    quitRowMarginals_replace_one, quitRowMarginals_replace_one]
  change |Math.Probability.expect (Math.PMFProduct.pmfPi rootP)
      (fun action => GameTheory.quittingRootPayoff G.reward 0 action n) -
    Math.Probability.expect (Math.PMFProduct.pmfPi rootQ)
      (fun action => GameTheory.quittingRootPayoff G.reward 0 action n)| ≤ _
  calc
    _ ≤ (2 * (M / 3)) *
        Math.Probability.pmfTV (Math.PMFProduct.pmfPi rootP)
          (Math.PMFProduct.pmfPi rootQ) := by
      exact Math.Probability.abs_expect_sub_le_two_mul_pmfTV _ _ _
        (fun action => GameTheory.abs_quittingRootPayoff_le G.reward 0
          hM.2.1 (fun _ => by simp; linarith [hM.1]) action n)
    _ ≤ (2 * (M / 3)) * ((Fintype.card G.Player : ℝ) * t) :=
      mul_le_mul_of_nonneg_left htv (by positivity)
    _ = (2 * (M / 3)) * (Fintype.card G.Player : ℝ) * t := by ring

/-- At an exact equilibrium row, positive Quit support identifies the row
value with the forced-Quit endpoint. -/
private theorem oneStagePayoff_eq_forcedQuit_of_positive
    (G : QuittingGame) (beta : Payoff G.Player) (p : QuitRow G)
    (hp : p ∈ EpsilonRow G 0 beta) (hq : QuitProbability G p < 1)
    (n : G.Player) (hn : 0 < (p n : ℝ)) :
    QuittingOneStagePayoff G beta p n = ForcedQuitPayoff G p n := by
  have hpnLt : (p n : ℝ) < 1 := by
    by_contra hnot
    have hpnOne : (p n : ℝ) = 1 := le_antisymm (p n).property.2 (le_of_not_gt hnot)
    rw [quitProbability_eq_one_of_coord_eq_one G p n hpnOne] at hq
    linarith
  have hquit := hp.1 n hn
  have hcontinue := hp.2 n hpnLt
  have heq : ForcedQuitPayoff G p n = ForcedContinuePayoff G beta p n := by
    exact le_antisymm (by simpa using hcontinue) (by simpa using hquit)
  have haffine := quittingOneStagePayoff_replace_affine G beta p n (p n)
  rw [QuitRow.replace_self] at haffine
  calc
    QuittingOneStagePayoff G beta p n =
        (p n : ℝ) * ForcedQuitPayoff G p n +
          (1 - (p n : ℝ)) * ForcedContinuePayoff G beta p n := haffine
    _ = ForcedQuitPayoff G p n := by rw [← heq]; ring

/-- At an exact equilibrium row, positive Continue support identifies the row
value with the forced-Continue endpoint. -/
private theorem oneStagePayoff_eq_forcedContinue_of_lt_one
    (G : QuittingGame) (beta : Payoff G.Player) (p : QuitRow G)
    (hp : p ∈ EpsilonRow G 0 beta) (n : G.Player)
    (hn : (p n : ℝ) < 1) :
    QuittingOneStagePayoff G beta p n = ForcedContinuePayoff G beta p n := by
  have haffine := quittingOneStagePayoff_replace_affine G beta p n (p n)
  rw [QuitRow.replace_self] at haffine
  by_cases hp0 : (p n : ℝ) = 0
  · simpa [hp0] using haffine
  · have hpPos : 0 < (p n : ℝ) :=
      lt_of_le_of_ne (p n).property.1 (Ne.symm hp0)
    have hquit := hp.1 n hpPos
    have hcontinue := hp.2 n hn
    have heq : ForcedQuitPayoff G p n = ForcedContinuePayoff G beta p n := by
      exact le_antisymm (by simpa using hcontinue) (by simpa using hquit)
    calc
      QuittingOneStagePayoff G beta p n =
          (p n : ℝ) * ForcedQuitPayoff G p n +
            (1 - (p n : ℝ)) * ForcedContinuePayoff G beta p n := haffine
      _ = ForcedContinuePayoff G beta p n := by rw [heq]; ring

/-- The singular penalty increases by at least the increase in its hazard. -/
private theorem singularQuitPenalty_sub_ge_sub {N : ℕ} {u v : UnitInterval}
    (hvu : (v : ℝ) ≤ (u : ℝ)) (hu : (u : ℝ) < 1) :
    (u : ℝ) / (1 - (u : ℝ)) ^ N -
        (v : ℝ) / (1 - (v : ℝ)) ^ N ≥
      (u : ℝ) - (v : ℝ) := by
  have hv : (v : ℝ) < 1 := hvu.trans_lt hu
  have hpowU : 0 < (1 - (u : ℝ)) ^ N := pow_pos (by linarith) _
  have hpowV : 0 < (1 - (v : ℝ)) ^ N := pow_pos (by linarith) _
  have hpowUV : (1 - (u : ℝ)) ^ N ≤ (1 - (v : ℝ)) ^ N :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have huvDiv :
      (v : ℝ) / (1 - (v : ℝ)) ^ N ≤
        (v : ℝ) / (1 - (u : ℝ)) ^ N :=
    div_le_div_of_nonneg_left v.property.1 hpowU hpowUV
  have hpowOne : (1 - (u : ℝ)) ^ N ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr u.property.2) (by linarith [u.property.1])
  have hdiffDiv : (u : ℝ) - (v : ℝ) ≤
      ((u : ℝ) - (v : ℝ)) / (1 - (u : ℝ)) ^ N := by
    rw [le_div_iff₀ hpowU]
    nlinarith [mul_le_mul_of_nonneg_left hpowOne (sub_nonneg.mpr hvu)]
  calc
    (u : ℝ) / (1 - (u : ℝ)) ^ N -
          (v : ℝ) / (1 - (v : ℝ)) ^ N ≥
        (u : ℝ) / (1 - (u : ℝ)) ^ N -
          (v : ℝ) / (1 - (u : ℝ)) ^ N := by linarith
    _ = ((u : ℝ) - (v : ℝ)) / (1 - (u : ℝ)) ^ N := by ring
    _ ≥ (u : ℝ) - (v : ℝ) := hdiffDiv

/-- At a coordinate with maximal hazard change, the singular penalty controls
that hazard change by the distance between the two `φ` images. -/
private theorem maximal_hazard_sub_le_phi_norm
    (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (z w : EZeroTilde G) (j : G.Player)
    (hgt : (w.1.2 j : ℝ) < (z.1.2 j : ℝ))
    (hmax : ∀ k, |(z.1.2 k : ℝ) - (w.1.2 k : ℝ)| ≤
      (z.1.2 j : ℝ) - (w.1.2 j : ℝ)) :
    (z.1.2 j : ℝ) - (w.1.2 j : ℝ) ≤
      ‖Phi G M d z - Phi G M d w‖ := by
  classical
  let N : ℝ := Fintype.card G.Player
  let t : ℝ := (z.1.2 j : ℝ) - (w.1.2 j : ℝ)
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hM0 : 0 < M := zero_lt_one.trans_le hM.1
  have ht : 0 < t := by dsimp only [t]; linarith
  have hzjLt : (z.1.2 j : ℝ) < 1 := by
    by_contra hnot
    have hjOne : (z.1.2 j : ℝ) = 1 :=
      le_antisymm (z.1.2 j).property.2 (le_of_not_gt hnot)
    have hquit := z.2.2
    rw [quitProbability_eq_one_of_coord_eq_one G z.1.2 j hjOne] at hquit
    linarith
  have hwjLt : (w.1.2 j : ℝ) < 1 := hgt.trans hzjLt
  have hzStage := oneStagePayoff_eq_forcedQuit_of_positive G z.1.1 z.1.2
    z.2.1 z.2.2 j (by linarith [(w.1.2 j).property.1])
  have hwStage := oneStagePayoff_eq_forcedContinue_of_lt_one G w.1.1 w.1.2
    w.2.1 j hwjLt
  have hwEndpoint : ForcedQuitPayoff G w.1.2 j ≤
      ForcedContinuePayoff G w.1.1 w.1.2 j := by
    simpa using w.2.1.2 j hwjLt
  have hforced := abs_forcedQuitPayoff_sub_le_of_row_close
    G M t hM z.1.2 w.1.2 j hmax
  have hstageDiff :
      QuittingOneStagePayoff G z.1.1 z.1.2 j -
          QuittingOneStagePayoff G w.1.1 w.1.2 j ≤
        (2 * (M / 3)) * N * t := by
    rw [hzStage, hwStage]
    linarith [le_abs_self (ForcedQuitPayoff G z.1.2 j -
      ForcedQuitPayoff G w.1.2 j)]
  have hsumDiff :
      (∑ k ∈ Finset.univ.erase j, (z.1.2 k : ℝ)) -
          ∑ k ∈ Finset.univ.erase j, (w.1.2 k : ℝ) ≤ N * t := by
    calc
      (∑ k ∈ Finset.univ.erase j, (z.1.2 k : ℝ)) -
            ∑ k ∈ Finset.univ.erase j, (w.1.2 k : ℝ) =
          ∑ k ∈ Finset.univ.erase j,
            ((z.1.2 k : ℝ) - (w.1.2 k : ℝ)) := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ _k ∈ Finset.univ.erase j, t := by
        apply Finset.sum_le_sum
        intro k _
        exact (le_abs_self _).trans (hmax k)
      _ = ((Finset.univ.erase j).card : ℝ) * t := by simp
      _ ≤ N * t := by
        apply mul_le_mul_of_nonneg_right _ ht.le
        dsimp only [N]
        exact_mod_cast (Finset.card_erase_le :
          (Finset.univ.erase j).card ≤ (Finset.univ : Finset G.Player).card)
  have hpenalty := singularQuitPenalty_sub_ge_sub
    (N := Fintype.card G.Player) (u := z.1.2 j) (v := w.1.2 j)
    (by linarith) hzjLt
  have hcoefficient : 5 * N * M ≤ 5 * N * M / d := by
    rw [le_div_iff₀ hd]
    calc
      5 * N * M * d ≤ 5 * N * M * 1 :=
        mul_le_mul_of_nonneg_left hd1 (by positivity)
      _ = 5 * N * M := by ring
  have hlower : 5 * N * M * t ≤
      (5 * N * M / d) *
        ((z.1.2 j : ℝ) /
            (1 - (z.1.2 j : ℝ)) ^ Fintype.card G.Player -
          (w.1.2 j : ℝ) /
            (1 - (w.1.2 j : ℝ)) ^ Fintype.card G.Player) := by
    calc
      5 * N * M * t ≤ (5 * N * M / d) * t :=
        mul_le_mul_of_nonneg_right hcoefficient ht.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hpenalty (by positivity)
  have hphiFormula : (Phi G M d z - Phi G M d w) j =
      (QuittingOneStagePayoff G z.1.1 z.1.2 j -
        QuittingOneStagePayoff G w.1.1 w.1.2 j) -
      (5 * N * M / d) *
        ((z.1.2 j : ℝ) /
            (1 - (z.1.2 j : ℝ)) ^ Fintype.card G.Player -
          (w.1.2 j : ℝ) /
            (1 - (w.1.2 j : ℝ)) ^ Fintype.card G.Player) +
      M * ((∑ k ∈ Finset.univ.erase j, (z.1.2 k : ℝ)) -
        ∑ k ∈ Finset.univ.erase j, (w.1.2 k : ℝ)) := by
    simp only [Phi, Pi.sub_apply]
    ring
  have hsumMul := mul_le_mul_of_nonneg_left hsumDiff hM0.le
  have hphiUpper : (Phi G M d z - Phi G M d w) j ≤
      -(10 / 3 : ℝ) * (N * M * t) := by
    rw [hphiFormula]
    nlinarith [hlower]
  have hphiNeg : (Phi G M d z - Phi G M d w) j < 0 := by
    have : 0 < N * M * t := by positivity
    nlinarith
  have habs : t ≤ |(Phi G M d z - Phi G M d w) j| := by
    rw [abs_of_neg hphiNeg]
    have hNsub : 0 ≤ N - 1 := by linarith
    have hMsub : 0 ≤ M - 1 := sub_nonneg.mpr hM.1
    have hNM : 1 ≤ N * M := by
      nlinarith [mul_nonneg hNsub hMsub]
    have hscaled : t ≤ N * M * t := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hNM ht.le
    exact hscaled.trans (by nlinarith [hphiUpper])
  simpa only [t] using habs.trans (by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (norm_le_pi_norm (Phi G M d z - Phi G M d w) j))

/-- In particular, two exact-equilibrium points with different hazards have
different `φ` images. -/
private theorem phi_ne_of_maximal_hazard_increase
    (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (z w : EZeroTilde G) (j : G.Player)
    (hgt : (w.1.2 j : ℝ) < (z.1.2 j : ℝ))
    (hmax : ∀ k, |(z.1.2 k : ℝ) - (w.1.2 k : ℝ)| ≤
      (z.1.2 j : ℝ) - (w.1.2 j : ℝ)) :
    Phi G M d z ≠ Phi G M d w := by
  intro hphi
  have hcontrol := maximal_hazard_sub_le_phi_norm
    G M d hM hd hd1 z w j hgt hmax
  rw [hphi, sub_self, norm_zero] at hcontrol
  linarith

/-- Every individual hazard coordinate is nonexpansive with respect to the
`Phi` image. -/
private theorem abs_hazard_sub_le_phi_norm
    (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (z w : EZeroTilde G) (k : G.Player) :
    |(z.1.2 k : ℝ) - (w.1.2 k : ℝ)| ≤
      ‖Phi G M d z - Phi G M d w‖ := by
  classical
  by_cases hpq : z.1.2 = w.1.2
  · rw [hpq]
    simp
  · obtain ⟨j, _hj, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun i : G.Player => |(z.1.2 i : ℝ) - (w.1.2 i : ℝ)|)
      Finset.univ_nonempty
    have hmaxPos : 0 < |(z.1.2 j : ℝ) - (w.1.2 j : ℝ)| := by
      by_contra hnot
      have hmaxZero : |(z.1.2 j : ℝ) - (w.1.2 j : ℝ)| = 0 :=
        le_antisymm (le_of_not_gt hnot) (abs_nonneg _)
      apply hpq
      funext i
      apply Subtype.ext
      have hiZero : |(z.1.2 i : ℝ) - (w.1.2 i : ℝ)| = 0 :=
        le_antisymm (by simpa [hmaxZero] using hmax i (Finset.mem_univ i))
          (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hiZero)
    have hkmax := hmax k (Finset.mem_univ k)
    rcases lt_or_gt_of_ne (sub_ne_zero.mp (abs_ne_zero.mp hmaxPos.ne')) with
      hz | hw
    · have hcontrol := maximal_hazard_sub_le_phi_norm G M d hM hd hd1
        w z j hz (fun i => by
          simpa [abs_sub_comm, abs_of_neg (sub_neg.mpr hz)] using
            hmax i (Finset.mem_univ i))
      rw [norm_sub_rev] at hcontrol
      exact hkmax.trans (by
        simpa [abs_of_neg (sub_neg.mpr hz)] using hcontrol)
    · have hcontrol := maximal_hazard_sub_le_phi_norm G M d hM hd hd1
        z w j hw (fun i => by
          simpa [abs_of_pos (sub_pos.mpr hw)] using
            hmax i (Finset.mem_univ i))
      exact hkmax.trans (by
        simpa [abs_of_pos (sub_pos.mpr hw)] using hcontrol)

/-- A concrete inverse/homeomorphism package for `φ`. -/
structure PhiInverseData (G : QuittingGame) (M d : ℝ) where
  inv : Payoff G.Player → EZeroTilde G
  leftInverse : Function.LeftInverse inv (Phi G M d)
  rightInverse : Function.RightInverse inv (Phi G M d)
  continuousInv : Continuous inv

/--
Lemma 3.1: injectivity and the all-Continue fiber.  At a coordinate with
maximal hazard change, product-law total variation bounds the change in the
forced-Quit payoff, while the singular term in `φ` grows strictly faster.
-/
theorem lemma3_1 (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1) :
    Function.Injective (Phi G M d) ∧
    (∀ x, ((x, zeroQuitRow G) ∈ EZeroTilde G ↔
      ∀ j, SoloPayoff G j ≤ x j)) ∧
    ∀ x (hx : (x, zeroQuitRow G) ∈ EZeroTilde G),
      Phi G M d ⟨(x, zeroQuitRow G), hx⟩ = x := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨x, p⟩, hp⟩ ⟨⟨y, q⟩, hq⟩ hphi
    by_cases hpq : p = q
    · subst q
      apply Subtype.ext
      apply Prod.ext
      · funext j
        have hcoordinate := congrFun hphi j
        change QuittingOneStagePayoff G x p j -
              (5 * (Fintype.card G.Player : ℝ) * M / d) *
                ((p j : ℝ) / (1 - (p j : ℝ)) ^ Fintype.card G.Player) +
              M * ∑ k ∈ Finset.univ.erase j, (p k : ℝ) =
            QuittingOneStagePayoff G y p j -
              (5 * (Fintype.card G.Player : ℝ) * M / d) *
                ((p j : ℝ) / (1 - (p j : ℝ)) ^ Fintype.card G.Player) +
              M * ∑ k ∈ Finset.univ.erase j, (p k : ℝ) at hcoordinate
        have hsurvival : 0 < 1 - QuitProbability G p := by linarith [hp.2]
        simp only [QuittingOneStagePayoff] at hcoordinate
        have hmul :
            (1 - QuitProbability G p) * x j =
              (1 - QuitProbability G p) * y j := by
          linear_combination hcoordinate
        exact mul_left_cancel₀ hsurvival.ne' hmul
      · rfl
    · obtain ⟨j, _hj, hmax⟩ := Finset.exists_max_image Finset.univ
        (fun k : G.Player => |(p k : ℝ) - (q k : ℝ)|)
        Finset.univ_nonempty
      have hmaxPos : 0 < |(p j : ℝ) - (q j : ℝ)| := by
        by_contra hnot
        have hmaxZero : |(p j : ℝ) - (q j : ℝ)| = 0 :=
          le_antisymm (le_of_not_gt hnot) (abs_nonneg _)
        apply hpq
        funext k
        apply Subtype.ext
        have hkZero : |(p k : ℝ) - (q k : ℝ)| = 0 :=
          le_antisymm (by simpa [hmaxZero] using hmax k (Finset.mem_univ k))
            (abs_nonneg _)
        exact sub_eq_zero.mp (abs_eq_zero.mp hkZero)
      rcases lt_or_gt_of_ne (sub_ne_zero.mp (abs_ne_zero.mp hmaxPos.ne')) with
        hpj | hqj
      · exact (phi_ne_of_maximal_hazard_increase G M d hM hd hd1
          ⟨(y, q), hq⟩ ⟨(x, p), hp⟩ j hpj
          (fun k => by
            simpa [abs_sub_comm, abs_of_neg (sub_neg.mpr hpj)] using
              hmax k (Finset.mem_univ k)) hphi.symm).elim
      · exact (phi_ne_of_maximal_hazard_increase G M d hM hd hd1
          ⟨(x, p), hp⟩ ⟨(y, q), hq⟩ j hqj
          (fun k => by
            simpa [abs_of_pos (sub_pos.mpr hqj)] using
              hmax k (Finset.mem_univ k)) hphi).elim
  · intro x
    change (zeroQuitRow G ∈ EpsilonRow G 0 x ∧
        QuitProbability G (zeroQuitRow G) < 1) ↔ _
    constructor
    · rintro ⟨hrow, _⟩ j
      have hcontinue := hrow.2 j (by simp [zeroQuitRow])
      have hzero : (zeroQuitRow G).replace G j 0 = zeroQuitRow G :=
        QuitRow.replace_self G (zeroQuitRow G) j
      have hone : (zeroQuitRow G).replace G j 1 = SoloQuitRow G j := by
        change QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j 1 = _
        exact QuitRow.zero_replace_one G j
      rw [ForcedContinuePayoff, hzero, ForcedQuitPayoff,
        hone, quittingOneStagePayoff_soloQuitRow] at hcontinue
      change QuittingOneStagePayoff G x (fun _ => 0) j ≥ SoloPayoff G j - 0
        at hcontinue
      rw [quittingOneStagePayoff_zero] at hcontinue
      simpa using hcontinue
    · intro hx
      constructor
      · constructor
        · intro j hj
          simp [zeroQuitRow] at hj
        · intro j _hj
          have hzero : (zeroQuitRow G).replace G j 0 = zeroQuitRow G :=
            QuitRow.replace_self G (zeroQuitRow G) j
          have hone : (zeroQuitRow G).replace G j 1 = SoloQuitRow G j := by
            change QuitRow.replace G (fun _ => (0 : Set.Icc (0 : ℝ) 1)) j 1 = _
            exact QuitRow.zero_replace_one G j
          rw [ForcedContinuePayoff, hzero, ForcedQuitPayoff,
            hone, quittingOneStagePayoff_soloQuitRow]
          change QuittingOneStagePayoff G x (fun _ => 0) j ≥ SoloPayoff G j - 0
          rw [quittingOneStagePayoff_zero]
          simpa using hx j
      · simp [QuitProbability, zeroQuitRow]
  · intro x hx
    funext j
    change QuittingOneStagePayoff G x (fun _ => 0) j -
          (5 * (Fintype.card G.Player : ℝ) * M / d) *
            (((fun _ => (0 : Set.Icc (0 : ℝ) 1)) j : ℝ) /
              (1 - ((fun _ => (0 : Set.Icc (0 : ℝ) 1)) j : ℝ)) ^
                Fintype.card G.Player) +
          M * ∑ k ∈ Finset.univ.erase j,
            ((fun _ => (0 : Set.Icc (0 : ℝ) 1)) k : ℝ) = x j
    rw [quittingOneStagePayoff_zero]
    simp

/-- Continuity of the absorption probability after a continuously varying
quitting row. -/
private theorem continuous_quitProbability_comp {X : Type}
    [TopologicalSpace X] (G : QuittingGame) (p : X → QuitRow G)
    (hp : Continuous p) :
    Continuous (fun x => QuitProbability G (p x)) := by
  simp only [QuitProbability]
  apply continuous_const.sub
  apply continuous_finsetProd
  intro k _hk
  exact continuous_const.sub
    (continuous_subtype_val.comp ((continuous_apply k).comp hp))

/-- Continuity of every fixed coalition probability after a continuously
varying quitting row. -/
private theorem continuous_coalitionProbability_comp {X : Type}
    [TopologicalSpace X] (G : QuittingGame) (p : X → QuitRow G)
    (hp : Continuous p) (A : Finset G.Player) :
    Continuous (fun x => CoalitionProbability G (p x) A) := by
  simp only [CoalitionProbability]
  have hcoord (k : G.Player) :
      Continuous (fun x => ((p x) k : ℝ)) :=
    continuous_subtype_val.comp ((continuous_apply k).comp hp)
  apply (continuous_finsetProd A fun k _hk => hcoord k).mul
  apply continuous_finsetProd
  intro k _hk
  exact continuous_const.sub (hcoord k)

/-- Joint continuity of a coordinate of the one-stage payoff along
continuously varying continuation vectors and rows. -/
private theorem continuous_quittingOneStagePayoff_comp {X : Type}
    [TopologicalSpace X] (G : QuittingGame)
    (r : X → Payoff G.Player) (p : X → QuitRow G)
    (hr : Continuous r) (hp : Continuous p) (j : G.Player) :
    Continuous (fun x => QuittingOneStagePayoff G (r x) (p x) j) := by
  classical
  simp only [QuittingOneStagePayoff]
  apply ((continuous_const.sub
    (continuous_quitProbability_comp G p hp)).mul
      ((continuous_apply j).comp hr)).add
  apply continuous_finsetSum
  intro A _hA
  by_cases hA : A.Nonempty
  · simp only [hA, ↓reduceDIte]
    exact (continuous_coalitionProbability_comp G p hp A).mul continuous_const
  · simp only [hA, ↓reduceDIte]
    exact continuous_const

/-- The map `φ` is continuous on the exact-equilibrium graph below certain
absorption. -/
theorem continuous_phi (G : QuittingGame) (M d : ℝ) :
    Continuous (Phi G M d) := by
  classical
  rw [continuous_pi_iff]
  intro j
  have hcoord (k : G.Player) :
      Continuous (fun z : EZeroTilde G => (z.1.2 k : ℝ)) := by
    fun_prop
  have hstage :
      Continuous (fun z : EZeroTilde G =>
        QuittingOneStagePayoff G z.1.1 z.1.2 j) := by
    exact continuous_quittingOneStagePayoff_comp G
      (fun z : EZeroTilde G => z.1.1) (fun z => z.1.2) (by fun_prop)
        (by fun_prop) j
  have hdenom : ∀ z : EZeroTilde G,
      (1 - (z.1.2 j : ℝ)) ^ Fintype.card G.Player ≠ 0 := by
    intro z
    apply pow_ne_zero _
    apply sub_ne_zero.mpr
    intro hjOne
    have hquitOne := quitProbability_eq_one_of_coord_eq_one G z.1.2 j hjOne.symm
    linarith [z.2.2]
  have hsingular : Continuous (fun z : EZeroTilde G =>
      (z.1.2 j : ℝ) /
        (1 - (z.1.2 j : ℝ)) ^ Fintype.card G.Player) := by
    exact (hcoord j).div ((continuous_const.sub (hcoord j)).pow _) hdenom
  have hothers : Continuous (fun z : EZeroTilde G =>
      ∑ k ∈ Finset.univ.erase j, (z.1.2 k : ℝ)) := by
    apply continuous_finsetSum
    intro k _hk
    exact hcoord k
  simp only [Phi]
  exact (hstage.sub (continuous_const.mul hsingular)).add
    (continuous_const.mul hothers)

/-- The continuation vector that makes every player indifferent at a row
strictly below the sure-Quit faces. -/
private def indifferentContinuation (G : QuittingGame) (p : QuitRow G) :
    Payoff G.Player := fun j =>
  (ForcedQuitPayoff G p j -
      QuittingOneStagePayoff G 0 (p.replace G j 0) j) /
    (1 - QuitProbability G (p.replace G j 0))

/-- A row strictly below every sure-Quit face has positive survival. -/
private theorem one_sub_quitProbability_pos_of_forall_lt_one
    (G : QuittingGame) (p : QuitRow G)
    (hp : ∀ j, (p j : ℝ) < 1) :
    0 < 1 - QuitProbability G p := by
  simp only [QuitProbability, sub_sub_cancel]
  exact Finset.prod_pos fun j _hj => sub_pos.mpr (hp j)

/-- Forcing a player to Continue preserves strict survival. -/
private theorem one_sub_quitProbability_replace_zero_pos
    (G : QuittingGame) (p : QuitRow G)
    (hp : ∀ j, (p j : ℝ) < 1) (j : G.Player) :
    0 < 1 - QuitProbability G (p.replace G j 0) := by
  apply one_sub_quitProbability_pos_of_forall_lt_one
  intro k
  by_cases hkj : k = j
  · subst k
    simp [QuitRow.replace]
  · simpa [QuitRow.replace, hkj] using hp k

/-- The continuation chosen above makes the forced Quit and Continue
endpoints equal coordinatewise. -/
private theorem forcedContinue_indifferentContinuation
    (G : QuittingGame) (p : QuitRow G)
    (hp : ∀ j, (p j : ℝ) < 1) (j : G.Player) :
    ForcedContinuePayoff G (indifferentContinuation G p) p j =
      ForcedQuitPayoff G p j := by
  let s := 1 - QuitProbability G (p.replace G j 0)
  have hs : s ≠ 0 :=
    (one_sub_quitProbability_replace_zero_pos G p hp j).ne'
  change QuittingOneStagePayoff G (indifferentContinuation G p)
      (p.replace G j 0) j = ForcedQuitPayoff G p j
  rw [show QuittingOneStagePayoff G (indifferentContinuation G p)
        (p.replace G j 0) j =
      s * indifferentContinuation G p j +
        QuittingOneStagePayoff G 0 (p.replace G j 0) j by
    simp only [QuittingOneStagePayoff, Pi.zero_apply, mul_zero, zero_add, s]]
  simp only [indifferentContinuation]
  change s * ((ForcedQuitPayoff G p j -
      QuittingOneStagePayoff G 0 (p.replace G j 0) j) / s) +
    QuittingOneStagePayoff G 0 (p.replace G j 0) j = _
  rw [mul_div_cancel₀ _ hs]
  ring

/-- Increasing a player's own continuation coordinate increases that
player's forced-Continue payoff. -/
private theorem forcedContinue_mono_continuation_coord
    (G : QuittingGame) (p : QuitRow G) (r s : Payoff G.Player)
    (n : G.Player) (h : r n ≤ s n) :
    ForcedContinuePayoff G r p n ≤ ForcedContinuePayoff G s p n := by
  simp only [ForcedContinuePayoff, QuittingOneStagePayoff]
  gcongr
  exact sub_nonneg.mpr (quitProbability_mem_Icc G (p.replace G n 0)).2

private theorem forcedContinue_eq_of_continuation_coord_eq
    (G : QuittingGame) (p : QuitRow G) (r s : Payoff G.Player)
    (n : G.Player) (h : r n = s n) :
    ForcedContinuePayoff G r p n = ForcedContinuePayoff G s p n := by
  simp only [ForcedContinuePayoff, QuittingOneStagePayoff]
  rw [h]

/-- The indifference continuation realizes every strictly interior row as an
exact one-stage equilibrium with noncertain absorption. -/
private def indifferentGraphPoint (G : QuittingGame) (p : QuitRow G)
    (hp : ∀ j, (p j : ℝ) < 1) : EZeroTilde G := by
  refine ⟨(indifferentContinuation G p, p), ?_⟩
  constructor
  · constructor
    · intro j _hj
      rw [← forcedContinue_indifferentContinuation G p hp j]
      simp
    · intro j _hj
      rw [forcedContinue_indifferentContinuation G p hp j]
      simp
  · linarith [one_sub_quitProbability_pos_of_forall_lt_one G p hp]

/-- The compact row cube `[0,t]ᴺ` used in the proof of Lemma 3.2. -/
private abbrev CappedQuitRow (G : QuittingGame) (t : ℝ) :=
  {p : QuitRow G // ∀ j, (p j : ℝ) ≤ t}

/-- The paper's indifference parametrization of the exact-equilibrium graph
over a cube bounded away from the sure-Quit faces. -/
private def cappedIndifferentGraphPoint (G : QuittingGame) (t : ℝ)
    (ht : t < 1) (p : CappedQuitRow G t) : EZeroTilde G :=
  indifferentGraphPoint G p.1 fun j => (p.2 j).trans_lt ht

/-- The indifference parametrization is continuous on every capped cube. -/
private theorem continuous_cappedIndifferentGraphPoint
    (G : QuittingGame) (t : ℝ) (ht : t < 1) :
    Continuous (cappedIndifferentGraphPoint G t ht) := by
  have hp : Continuous (fun p : CappedQuitRow G t => p.1) :=
    continuous_subtype_val
  have hreplace (j : G.Player) (q : UnitInterval) :
      Continuous (fun p : CappedQuitRow G t => p.1.replace G j q) := by
    rw [continuous_pi_iff]
    intro k
    by_cases hkj : k = j
    · subst k
      simpa [QuitRow.replace] using
        (continuous_const : Continuous (fun _ : CappedQuitRow G t => q))
    · simpa [QuitRow.replace, hkj, Function.comp_def] using
        (continuous_apply k).comp hp
  have hbeta : Continuous (fun p : CappedQuitRow G t =>
      indifferentContinuation G p.1) := by
    rw [continuous_pi_iff]
    intro j
    have hforced : Continuous (fun p : CappedQuitRow G t =>
        ForcedQuitPayoff G p.1 j) := by
      simpa only [ForcedQuitPayoff] using
        (continuous_quittingOneStagePayoff_comp G (fun _ => 0)
          (fun p : CappedQuitRow G t => p.1.replace G j 1)
          continuous_const (hreplace j 1) j)
    have hzero : Continuous (fun p : CappedQuitRow G t =>
        QuittingOneStagePayoff G 0 (p.1.replace G j 0) j) := by
      exact continuous_quittingOneStagePayoff_comp G (fun _ => 0)
        (fun p : CappedQuitRow G t => p.1.replace G j 0)
        continuous_const (hreplace j 0) j
    have hsurvival : Continuous (fun p : CappedQuitRow G t =>
        1 - QuitProbability G (p.1.replace G j 0)) :=
      continuous_const.sub
        (continuous_quitProbability_comp G _ (hreplace j 0))
    have hne : ∀ p : CappedQuitRow G t,
        1 - QuitProbability G (p.1.replace G j 0) ≠ 0 := by
      intro p
      exact (one_sub_quitProbability_replace_zero_pos G p.1
        (fun k => (p.2 k).trans_lt ht) j).ne'
    change Continuous (fun p : CappedQuitRow G t =>
      (ForcedQuitPayoff G p.1 j -
          QuittingOneStagePayoff G 0 (p.1.replace G j 0) j) /
        (1 - QuitProbability G (p.1.replace G j 0)))
    exact (hforced.sub hzero).div hsurvival hne
  apply Continuous.subtype_mk
  change Continuous (fun p : CappedQuitRow G t =>
    (indifferentContinuation G p.1, p.1))
  exact hbeta.prodMk hp

/-- Forcing one player to Quit still leaves its payoff inside the paper's
reward scale. -/
private theorem abs_forcedQuitPayoff_le_scale
    (G : QuittingGame) (M : ℝ) (hM : IsSimonPayoffScale G M)
    (p : QuitRow G) (n : G.Player) :
    |ForcedQuitPayoff G p n| ≤ M / 3 := by
  classical
  rw [ForcedQuitPayoff, quittingOneStagePayoff_eq_rootExpectedPayoff]
  exact GameTheory.abs_quittingRootExpectedPayoff_le_bound G.reward 0
    (quitRowMarginals G (p.replace G n 1)) n hM.2.1 (fun _ => by
      simp only [Pi.zero_apply, abs_zero]
      linarith [hM.1])

/-- The finite-cube map `\bar φ` in the proof of Lemma 3.2. -/
private def cappedPhi (G : QuittingGame) (M d t : ℝ) (ht : t < 1) :
    CappedQuitRow G t → Payoff G.Player :=
  Phi G M d ∘ cappedIndifferentGraphPoint G t ht

/-- The finite-cube map is continuous. -/
private theorem continuous_cappedPhi
    (G : QuittingGame) (M d t : ℝ) (ht : t < 1) :
    Continuous (cappedPhi G M d t ht) :=
  (continuous_phi G M d).comp
    (continuous_cappedIndifferentGraphPoint G t ht)

/-- On positive support, the capped map's payoff term is the forced-Quit
endpoint. -/
private theorem cappedPhi_apply_of_positive
    (G : QuittingGame) (M d t : ℝ) (ht : t < 1)
    (p : CappedQuitRow G t) (j : G.Player) (hpj : 0 < (p.1 j : ℝ)) :
    cappedPhi G M d t ht p j =
      ForcedQuitPayoff G p.1 j -
        (5 * (Fintype.card G.Player : ℝ) * M / d) *
          ((p.1 j : ℝ) /
            (1 - (p.1 j : ℝ)) ^ Fintype.card G.Player) +
        M * ((∑ k, (p.1 k : ℝ)) - (p.1 j : ℝ)) := by
  classical
  change QuittingOneStagePayoff G (indifferentContinuation G p.1) p.1 j - _ + _ = _
  rw [oneStagePayoff_eq_forcedQuit_of_positive G
    (indifferentContinuation G p.1) p.1
    (indifferentGraphPoint G p.1 fun k => (p.2 k).trans_lt ht).2.1
    (indifferentGraphPoint G p.1 fun k => (p.2 k).trans_lt ht).2.2 j hpj]
  simp only [cappedIndifferentGraphPoint, indifferentGraphPoint]
  have hsum := Finset.sum_erase_add Finset.univ
    (fun k => (p.1 k : ℝ)) (Finset.mem_univ j)
  linear_combination M * hsum

/-- A cube can be chosen so that the singular term points strictly inward on
every upper face, as in the first step of Lemma 3.2. -/
private theorem exists_cappedPhi_upperFace_lt
    (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (y : Payoff G.Player) :
    ∃ t : ℝ, ∃ _ht : 0 < t, ∃ ht1 : t < 1,
      ∀ (p : CappedQuitRow G t) (j : G.Player),
        (p.1 j : ℝ) = t → cappedPhi G M d t ht1 p j < y j := by
  classical
  let N : ℝ := Fintype.card G.Player
  let S : ℝ := ∑ k, |y k|
  let a : ℝ := 1 + N * M + S
  let t : ℝ := a / (1 + a)
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos
  have hM0 : 1 ≤ M := hM.1
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hMnonneg : 0 ≤ M := zero_le_one.trans hM0
  have hP : 1 ≤ N * M := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hM0)]
  have ha : 0 < a := by dsimp only [a]; linarith
  have ht : 0 < t := div_pos ha (by linarith)
  have ht1 : t < 1 := by
    dsimp only [t]
    rw [div_lt_one (by linarith)]
    linarith
  refine ⟨t, ht, ht1, ?_⟩
  intro p j hpj
  have hjpos : 0 < (p.1 j : ℝ) := by rw [hpj]; exact ht
  rw [cappedPhi_apply_of_positive G M d t ht1 p j hjpos]
  have hforced := abs_forcedQuitPayoff_le_scale G M hM p.1 j
  have hsum : ∑ k, (p.1 k : ℝ) ≤ N := by
    calc
      ∑ k, (p.1 k : ℝ) ≤ ∑ _k : G.Player, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _hk
        exact (p.1 k).property.2
      _ = N := by simp [N]
  have hothers : (∑ k, (p.1 k : ℝ)) - (p.1 j : ℝ) ≤ N := by
    linarith [(p.1 j).property.1]
  have hyS : |y j| ≤ S := by
    dsimp only [S]
    exact Finset.single_le_sum (fun k _hk => abs_nonneg (y k))
      (Finset.mem_univ j)
  have hsub : 1 - t = 1 / (1 + a) := by
    dsimp only [t]
    field_simp
    ring
  have hsubPos : 0 < 1 - t := sub_pos.mpr ht1
  have hsubOne : 1 - t ≤ 1 := by linarith
  have hcard : Fintype.card G.Player ≠ 0 := Fintype.card_ne_zero
  have hpow : (1 - t) ^ Fintype.card G.Player ≤ 1 - t :=
    pow_le_of_le_one hsubPos.le hsubOne hcard
  have hratio : a ≤ t / (1 - t) ^ Fintype.card G.Player := by
    have hat : a = t / (1 - t) := by
      rw [hsub]
      dsimp only [t]
      field_simp
    rw [hat]
    exact div_le_div_of_nonneg_left ht.le
      (pow_pos hsubPos _) hpow
  have hcoefficient : 5 * N * M ≤ 5 * N * M / d := by
    rw [le_div_iff₀ hd]
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hN0)
      hMnonneg]
  have hsingular : 0 ≤ t / (1 - t) ^ Fintype.card G.Player :=
    div_nonneg ht.le (pow_nonneg hsubPos.le _)
  have hpenalty : 5 * N * M * a ≤
      (5 * N * M / d) *
        (t / (1 - t) ^ Fintype.card G.Player) := by
    exact mul_le_mul hcoefficient hratio
      (le_of_lt ha) (div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hN0) hMnonneg) hd.le)
  have hMa : a ≤ N * M * a := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hP (le_of_lt ha)
  have hstrict : M / 3 + N * M + S < 5 * N * M * a := by
    dsimp only [a] at hMa ⊢
    have hMN : M ≤ N * M := by nlinarith
    nlinarith
  rw [hpj]
  have hothersT : (∑ k, (p.1 k : ℝ)) - t ≤ N := by
    calc
      (∑ k, (p.1 k : ℝ)) - t =
          (∑ k, (p.1 k : ℝ)) - (p.1 j : ℝ) := by
        congr 1
        exact hpj.symm
      _ ≤ N := hothers
  have hotherMul : M * ((∑ k, (p.1 k : ℝ)) - t) ≤ M * N :=
    mul_le_mul_of_nonneg_left hothersT hMnonneg
  have hforcedUpper : ForcedQuitPayoff G p.1 j ≤ M / 3 :=
    (le_abs_self _).trans hforced
  have hyLower : -S ≤ y j := neg_le_of_abs_le hyS
  change ForcedQuitPayoff G p.1 j -
      (5 * N * M / d) *
        (t / (1 - t) ^ Fintype.card G.Player) +
      M * ((∑ k, (p.1 k : ℝ)) - t) < y j
  calc
    _ ≤ M / 3 - 5 * N * M * a + M * N := by linarith
    _ < -S := by nlinarith [hstrict]
    _ ≤ y j := hyLower

/-- The ambient closed cube used for Brouwer's theorem. -/
private def closedQuitCube (G : QuittingGame) (t : ℝ) :
    Set (Payoff G.Player) :=
  Set.univ.pi fun _ => Set.Icc 0 t

private theorem convex_closedQuitCube (G : QuittingGame) (t : ℝ) :
    Convex ℝ (closedQuitCube G t) :=
  convex_pi fun _ _ => convex_Icc 0 t

private theorem isCompact_closedQuitCube (G : QuittingGame) (t : ℝ) :
    IsCompact (closedQuitCube G t) :=
  isCompact_univ_pi fun _ => isCompact_Icc

private theorem nonempty_closedQuitCube (G : QuittingGame) {t : ℝ}
    (ht : 0 ≤ t) :
    (closedQuitCube G t).Nonempty := by
  refine ⟨0, ?_⟩
  intro j _hj
  exact ⟨le_rfl, ht⟩

/-- Convert an ambient cube point to the row subtype used by `cappedPhi`. -/
private def cappedQuitRowOfCube (G : QuittingGame) (t : ℝ)
    (_ht : 0 ≤ t) (ht1 : t ≤ 1) (p : closedQuitCube G t) :
    CappedQuitRow G t := by
  refine ⟨(fun j => ⟨p.1 j, (p.2 j (Set.mem_univ j)).1,
    (p.2 j (Set.mem_univ j)).2.trans ht1⟩), ?_⟩
  intro j
  exact (p.2 j (Set.mem_univ j)).2

private theorem continuous_cappedQuitRowOfCube
    (G : QuittingGame) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Continuous (cappedQuitRowOfCube G t ht ht1) := by
  apply Continuous.subtype_mk
  rw [continuous_pi_iff]
  intro j
  apply Continuous.subtype_mk
  simpa only [Function.comp_def] using
    (continuous_apply j).comp continuous_subtype_val

/-- The coordinatewise clipped excess map used for Brouwer's theorem. -/
private def cappedTargetMap (G : QuittingGame) (M d t : ℝ)
    (ht : 0 ≤ t) (ht1 : t < 1) (y : Payoff G.Player) :
    closedQuitCube G t → closedQuitCube G t := fun p => by
  let row := cappedQuitRowOfCube G t ht ht1.le p
  refine ⟨fun j => max 0 (min t
    (p.1 j + (cappedPhi G M d t ht1 row j - y j))), ?_⟩
  intro j _hj
  exact ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩

private theorem continuous_cappedTargetMap
    (G : QuittingGame) (M d t : ℝ) (ht : 0 ≤ t)
    (ht1 : t < 1) (y : Payoff G.Player) :
    Continuous (cappedTargetMap G M d t ht ht1 y) := by
  let row := cappedQuitRowOfCube G t ht ht1.le
  have hrow : Continuous row :=
    continuous_cappedQuitRowOfCube G t ht ht1.le
  have hphi : Continuous (fun p : closedQuitCube G t =>
      cappedPhi G M d t ht1 (row p)) :=
    (continuous_cappedPhi G M d t ht1).comp hrow
  apply Continuous.subtype_mk
  rw [continuous_pi_iff]
  intro j
  change Continuous (fun p : closedQuitCube G t =>
    max 0 (min t (p.1 j +
      (cappedPhi G M d t ht1 (row p) j - y j))))
  exact continuous_const.max (continuous_const.min
    (((continuous_apply j).comp continuous_subtype_val).add
      (((continuous_apply j).comp hphi).sub continuous_const)))

/-- Brouwer supplies a fixed point of the clipped target map. -/
private theorem exists_cappedTargetMap_fixedPoint
    (G : QuittingGame) (M d t : ℝ) (ht : 0 < t)
    (ht1 : t < 1) (y : Payoff G.Player) :
    ∃ p : closedQuitCube G t, cappedTargetMap G M d t ht.le ht1 y p = p := by
  exact brouwer_fixed_point (closedQuitCube G t)
    (convex_closedQuitCube G t) (isCompact_closedQuitCube G t)
    (nonempty_closedQuitCube G ht.le)
    ⟨cappedTargetMap G M d t ht.le ht1 y,
      continuous_cappedTargetMap G M d t ht.le ht1 y⟩

/-- A fixed point cannot lie on an upper face on which `cappedPhi` points
strictly below the target. -/
private theorem cappedTargetMap_fixedPoint_lt_upper
    (G : QuittingGame) (M d t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (y : Payoff G.Player) (p : closedQuitCube G t)
    (hfixed : cappedTargetMap G M d t ht.le ht1 y p = p)
    (hface : ∀ (q : CappedQuitRow G t) (j : G.Player),
      (q.1 j : ℝ) = t → cappedPhi G M d t ht1 q j < y j)
    (j : G.Player) : p.1 j < t := by
  let row := cappedQuitRowOfCube G t ht.le ht1.le p
  have hpUpper : p.1 j ≤ t := (p.2 j (Set.mem_univ j)).2
  by_contra hnot
  have hpEq : p.1 j = t := le_antisymm hpUpper (le_of_not_gt hnot)
  have hrowEq : (row.1 j : ℝ) = t := by
    exact hpEq
  have hbelow := hface row j hrowEq
  have hcoordinate := congrArg (fun q : closedQuitCube G t => q.1 j) hfixed
  change max 0 (min t
      (p.1 j + (cappedPhi G M d t ht1 row j - y j))) = p.1 j at hcoordinate
  have haddLt : p.1 j + (cappedPhi G M d t ht1 row j - y j) < t := by
    linarith
  have hmaxLt : max 0 (min t
      (p.1 j + (cappedPhi G M d t ht1 row j - y j))) < t := by
    apply max_lt ht
    exact (min_le_right _ _).trans_lt haddLt
  linarith

/-- At a positive coordinate of a clipped fixed point, no clipping is active,
so the capped map equals the target. -/
private theorem cappedPhi_eq_target_of_fixedPoint_positive
    (G : QuittingGame) (M d t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (y : Payoff G.Player) (p : closedQuitCube G t)
    (hfixed : cappedTargetMap G M d t ht.le ht1 y p = p)
    (hlt : ∀ j, p.1 j < t) (j : G.Player) (hpj : 0 < p.1 j) :
    cappedPhi G M d t ht1
      (cappedQuitRowOfCube G t ht.le ht1.le p) j = y j := by
  let row := cappedQuitRowOfCube G t ht.le ht1.le p
  let u := p.1 j + (cappedPhi G M d t ht1 row j - y j)
  have hcoordinate := congrArg (fun q : closedQuitCube G t => q.1 j) hfixed
  change max 0 (min t u) = p.1 j at hcoordinate
  have hminPos : 0 < min t u := by
    by_contra hnot
    have hmaxZero : max 0 (min t u) = 0 := max_eq_left (le_of_not_gt hnot)
    linarith
  have hminEq : min t u = p.1 j := by
    rw [max_eq_right hminPos.le] at hcoordinate
    exact hcoordinate
  have huLt : u < t := by
    by_contra hnot
    have hminT : min t u = t := min_eq_left (le_of_not_gt hnot)
    rw [hminT] at hminEq
    linarith [hlt j]
  have huEq : u = p.1 j := by
    rw [min_eq_right huLt.le] at hminEq
    exact hminEq
  dsimp only [u] at huEq
  linarith

/-- At a zero coordinate of a clipped fixed point, the capped map is below
the target. -/
private theorem cappedPhi_le_target_of_fixedPoint_zero
    (G : QuittingGame) (M d t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (y : Payoff G.Player) (p : closedQuitCube G t)
    (hfixed : cappedTargetMap G M d t ht.le ht1 y p = p)
    (j : G.Player) (hpj : p.1 j = 0) :
    cappedPhi G M d t ht1
      (cappedQuitRowOfCube G t ht.le ht1.le p) j ≤ y j := by
  let row := cappedQuitRowOfCube G t ht.le ht1.le p
  let u := p.1 j + (cappedPhi G M d t ht1 row j - y j)
  have hcoordinate := congrArg (fun q : closedQuitCube G t => q.1 j) hfixed
  change max 0 (min t u) = p.1 j at hcoordinate
  rw [hpj] at hcoordinate
  have hminNonpos : min t u ≤ 0 := by
    by_contra hnot
    have hpositive : 0 < max 0 (min t u) := lt_max_iff.mpr (Or.inr (lt_of_not_ge hnot))
    linarith
  have huNonpos : u ≤ 0 := by
    by_contra hnot
    have hminPos : 0 < min t u := lt_min ht (lt_of_not_ge hnot)
    linarith
  dsimp only [u] at huNonpos
  linarith

/-- Increase continuation coordinates just enough to turn the complementary
fixed-point inequalities into the requested exact `Phi` value. -/
private def targetAdjustedContinuation
    (G : QuittingGame) (M d t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
    (y : Payoff G.Player) (p : closedQuitCube G t) : Payoff G.Player :=
  let row := cappedQuitRowOfCube G t ht ht1.le p
  fun j => indifferentContinuation G row.1 j +
    (y j - cappedPhi G M d t ht1 row j) /
      (1 - QuitProbability G row.1)

/-- The target adjustment is coordinatewise nonnegative at a clipped fixed
point away from the upper faces. -/
private theorem indifferentContinuation_le_targetAdjusted
    (G : QuittingGame) (M d t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (y : Payoff G.Player) (p : closedQuitCube G t)
    (hfixed : cappedTargetMap G M d t ht.le ht1 y p = p)
    (hlt : ∀ j, p.1 j < t) (j : G.Player) :
    indifferentContinuation G
        (cappedQuitRowOfCube G t ht.le ht1.le p).1 j ≤
      targetAdjustedContinuation G M d t ht.le ht1 y p j := by
  let row := cappedQuitRowOfCube G t ht.le ht1.le p
  have hphi : cappedPhi G M d t ht1 row j ≤ y j := by
    by_cases hpj : 0 < p.1 j
    · exact (cappedPhi_eq_target_of_fixedPoint_positive G M d t ht ht1
        y p hfixed hlt j hpj).le
    · have hpzero : p.1 j = 0 :=
        le_antisymm (le_of_not_gt hpj) (p.2 j (Set.mem_univ j)).1
      exact cappedPhi_le_target_of_fixedPoint_zero G M d t ht ht1
        y p hfixed j hpzero
  have hsurvival : 0 < 1 - QuitProbability G row.1 :=
    one_sub_quitProbability_pos_of_forall_lt_one G row.1
      (fun k => (row.2 k).trans_lt ht1)
  change indifferentContinuation G row.1 j ≤
    indifferentContinuation G row.1 j +
      (y j - cappedPhi G M d t ht1 row j) /
        (1 - QuitProbability G row.1)
  exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hphi) hsurvival.le)

/-- Positive quitting support is not adjusted, because complementarity already
gives equality with the target there. -/
private theorem targetAdjustedContinuation_eq_of_positive
    (G : QuittingGame) (M d t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (y : Payoff G.Player) (p : closedQuitCube G t)
    (hfixed : cappedTargetMap G M d t ht.le ht1 y p = p)
    (hlt : ∀ j, p.1 j < t) (j : G.Player) (hpj : 0 < p.1 j) :
      targetAdjustedContinuation G M d t ht.le ht1 y p j =
      indifferentContinuation G
        (cappedQuitRowOfCube G t ht.le ht1.le p).1 j := by
  let row := cappedQuitRowOfCube G t ht.le ht1.le p
  have hphi := cappedPhi_eq_target_of_fixedPoint_positive G M d t ht ht1
    y p hfixed hlt j hpj
  change indifferentContinuation G row.1 j +
      (y j - cappedPhi G M d t ht1 row j) /
        (1 - QuitProbability G row.1) = indifferentContinuation G row.1 j
  rw [hphi]
  simp

/-- The adjusted continuation and fixed quitting row remain an exact
one-stage equilibrium below certain absorption. -/
private def targetAdjustedGraphPoint
    (G : QuittingGame) (M d t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (y : Payoff G.Player) (p : closedQuitCube G t)
    (hfixed : cappedTargetMap G M d t ht.le ht1 y p = p)
    (hlt : ∀ j, p.1 j < t) : EZeroTilde G := by
  let row := cappedQuitRowOfCube G t ht.le ht1.le p
  refine ⟨(targetAdjustedContinuation G M d t ht.le ht1 y p, row.1), ?_⟩
  have hstrict : ∀ j, (row.1 j : ℝ) < 1 := fun j => (row.2 j).trans_lt ht1
  change row.1 ∈ EpsilonRow G 0
      (targetAdjustedContinuation G M d t ht.le ht1 y p) ∧
    QuitProbability G row.1 < 1
  constructor
  · constructor
    · intro j hj
      have hadjust := targetAdjustedContinuation_eq_of_positive
        G M d t ht ht1 y p hfixed hlt j hj
      have hcontinue := forcedContinue_eq_of_continuation_coord_eq G row.1
        (targetAdjustedContinuation G M d t ht.le ht1 y p)
        (indifferentContinuation G row.1) j hadjust
      rw [hcontinue, forcedContinue_indifferentContinuation G row.1 hstrict j]
      simp
    · intro j _hj
      have hmono := forcedContinue_mono_continuation_coord G row.1
        (indifferentContinuation G row.1)
        (targetAdjustedContinuation G M d t ht.le ht1 y p) j
        (indifferentContinuation_le_targetAdjusted G M d t ht ht1
          y p hfixed hlt j)
      rw [forcedContinue_indifferentContinuation G row.1 hstrict j] at hmono
      simpa using hmono
  · linarith [one_sub_quitProbability_pos_of_forall_lt_one G row.1 hstrict]

/-- The adjustment changes `Phi` by exactly the target residual. -/
private theorem phi_targetAdjustedGraphPoint
    (G : QuittingGame) (M d t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (y : Payoff G.Player) (p : closedQuitCube G t)
    (hfixed : cappedTargetMap G M d t ht.le ht1 y p = p)
    (hlt : ∀ j, p.1 j < t) :
    Phi G M d (targetAdjustedGraphPoint G M d t ht ht1 y p hfixed hlt) = y := by
  classical
  let row := cappedQuitRowOfCube G t ht.le ht1.le p
  have hsurvival : 0 < 1 - QuitProbability G row.1 :=
    one_sub_quitProbability_pos_of_forall_lt_one G row.1
      (fun j => (row.2 j).trans_lt ht1)
  funext j
  have hstage : QuittingOneStagePayoff G
      (targetAdjustedContinuation G M d t ht.le ht1 y p) row.1 j =
      QuittingOneStagePayoff G (indifferentContinuation G row.1) row.1 j +
        (y j - cappedPhi G M d t ht1 row j) := by
    change QuittingOneStagePayoff G
      (fun k => indifferentContinuation G row.1 k +
        (y k - cappedPhi G M d t ht1 row k) /
          (1 - QuitProbability G row.1)) row.1 j = _
    simp only [QuittingOneStagePayoff]
    field_simp [hsurvival.ne']; ring
  simp only [targetAdjustedGraphPoint]
  change QuittingOneStagePayoff G
      (targetAdjustedContinuation G M d t ht.le ht1 y p) row.1 j -
        (5 * (Fintype.card G.Player : ℝ) * M / d) *
          ((row.1 j : ℝ) /
            (1 - (row.1 j : ℝ)) ^ Fintype.card G.Player) +
        M * ∑ k ∈ Finset.univ.erase j, (row.1 k : ℝ) = y j
  rw [hstage]
  have hcapped : QuittingOneStagePayoff G
      (indifferentContinuation G row.1) row.1 j -
        (5 * (Fintype.card G.Player : ℝ) * M / d) *
          ((row.1 j : ℝ) /
            (1 - (row.1 j : ℝ)) ^ Fintype.card G.Player) +
        M * ∑ k ∈ Finset.univ.erase j, (row.1 k : ℝ) =
      cappedPhi G M d t ht1 row j := rfl
  linear_combination hcapped

/-- Brouwer's clipped excess map and the target adjustment prove the
surjectivity half of Lemma 3.2. -/
private theorem phi_surjective (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1) :
    Function.Surjective (Phi G M d) := by
  intro y
  obtain ⟨t, ht, ht1, hface⟩ :=
    exists_cappedPhi_upperFace_lt G M d hM hd hd1 y
  obtain ⟨p, hfixed⟩ :=
    exists_cappedTargetMap_fixedPoint G M d t ht ht1 y
  have hlt : ∀ j, p.1 j < t :=
    cappedTargetMap_fixedPoint_lt_upper G M d t ht ht1
      y p hfixed hface
  exact ⟨targetAdjustedGraphPoint G M d t ht ht1 y p hfixed hlt,
    phi_targetAdjustedGraphPoint G M d t ht ht1 y p hfixed hlt⟩

/-- Recover the continuation vector from a `Phi` value and its quitting row. -/
private def recoveredContinuation (G : QuittingGame) (M d : ℝ)
    (a : Payoff G.Player) (p : QuitRow G) : Payoff G.Player := fun j =>
  (a j + (5 * (Fintype.card G.Player : ℝ) * M / d) *
      ((p j : ℝ) / (1 - (p j : ℝ)) ^ Fintype.card G.Player) -
      M * ((∑ k, (p k : ℝ)) - (p j : ℝ)) -
      QuittingOneStagePayoff G 0 p j) /
    (1 - QuitProbability G p)

/-- On the exact-equilibrium graph, the recovery formula returns the original
continuation vector. -/
private theorem recoveredContinuation_phi
    (G : QuittingGame) (M d : ℝ) (z : EZeroTilde G) :
    recoveredContinuation G M d (Phi G M d z) z.1.2 = z.1.1 := by
  classical
  have hsurvival : 1 - QuitProbability G z.1.2 ≠ 0 := by
    linarith [z.2.2]
  funext j
  have hsum := Finset.sum_erase_add Finset.univ
    (fun k => (z.1.2 k : ℝ)) (Finset.mem_univ j)
  simp only [recoveredContinuation, Phi, QuittingOneStagePayoff,
    Pi.zero_apply, mul_zero, zero_add]
  field_simp [hsurvival]
  rw [← hsum]
  ring

/-- The recovery formula is continuous whenever the supplied rows have
positive survival. -/
private theorem continuous_recoveredContinuation_comp {X : Type}
    [TopologicalSpace X] (G : QuittingGame) (M d : ℝ)
    (a : X → Payoff G.Player) (p : X → QuitRow G)
    (ha : Continuous a) (hp : Continuous p)
    (hsurvival : ∀ x, QuitProbability G (p x) < 1) :
    Continuous (fun x => recoveredContinuation G M d (a x) (p x)) := by
  classical
  rw [continuous_pi_iff]
  intro j
  have hcoord (k : G.Player) : Continuous (fun x => ((p x) k : ℝ)) :=
    continuous_subtype_val.comp ((continuous_apply k).comp hp)
  have htotal : Continuous (fun x => ∑ k, ((p x) k : ℝ)) := by
    apply continuous_finsetSum
    intro k _hk
    exact hcoord k
  have hcoordDenom : ∀ x, 1 - ((p x) j : ℝ) ≠ 0 := by
    intro x hzero
    have hjOne : ((p x) j : ℝ) = 1 := by linarith
    have hquitOne := quitProbability_eq_one_of_coord_eq_one G (p x) j hjOne
    linarith [hsurvival x]
  have hsingular : Continuous (fun x =>
      ((p x) j : ℝ) /
        (1 - ((p x) j : ℝ)) ^ Fintype.card G.Player) := by
    exact (hcoord j).div ((continuous_const.sub (hcoord j)).pow _)
      (fun x => pow_ne_zero _ (hcoordDenom x))
  have hstage : Continuous (fun x =>
      QuittingOneStagePayoff G 0 (p x) j) :=
    continuous_quittingOneStagePayoff_comp G (fun _ => 0) p
      continuous_const hp j
  have hquit := continuous_quitProbability_comp G p hp
  have hpositive : ∀ x, 1 - QuitProbability G (p x) ≠ 0 := by
    intro x
    linarith [hsurvival x]
  have hnumerator : Continuous (fun x =>
      a x j + (5 * (Fintype.card G.Player : ℝ) * M / d) *
          (((p x) j : ℝ) /
            (1 - ((p x) j : ℝ)) ^ Fintype.card G.Player) -
        M * ((∑ k, ((p x) k : ℝ)) - ((p x) j : ℝ)) -
        QuittingOneStagePayoff G 0 (p x) j) := by
    exact ((((continuous_apply j).comp ha).add
      (continuous_const.mul hsingular)).sub
        (continuous_const.mul (htotal.sub (hcoord j)))).sub hstage
  exact hnumerator.div (continuous_const.sub hquit) hpositive

/--
Lemma 3.2: surjectivity and continuity of the inverse.  The missing proof is
the paper's Jacobian argument: strict diagonal dominance gives local openness
and an inverse, Claim A gives positive-coordinate motion, and the lower
semicontinuous minimization closes surjectivity.  The generic
Kohlberg--Mertens declaration in Simon 2007 does not imply this explicit `φ`
homeomorphism.
-/
theorem lemma3_2 (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1) :
    Function.Surjective (Phi G M d) ∧ Nonempty (PhiInverseData G M d) := by
  let hsurjective := phi_surjective G M d hM hd hd1
  refine ⟨hsurjective, ?_⟩
  letI : Nonempty (EZeroTilde G) := ⟨(hsurjective 0).choose⟩
  let inv : Payoff G.Player → EZeroTilde G := Function.invFun (Phi G M d)
  have hinjective : Function.Injective (Phi G M d) :=
    (lemma3_1 G M d hM hd hd1).1
  have hleft : Function.LeftInverse inv (Phi G M d) := by
    simpa only [inv] using Function.leftInverse_invFun hinjective
  have hright : Function.RightInverse inv (Phi G M d) := by
    simpa only [inv] using Function.rightInverse_invFun hsurjective
  have hhazardLip (j : G.Player) : LipschitzWith 1
      (fun a : Payoff G.Player => (((inv a).1.2 j : UnitInterval) : ℝ)) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro a b
    have hbound := abs_hazard_sub_le_phi_norm
      G M d hM hd hd1 (inv a) (inv b) j
    rw [hright a, hright b] at hbound
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, Real.norm_eq_abs,
      dist_eq_norm] using hbound
  have hpInv : Continuous (fun a : Payoff G.Player => (inv a).1.2) := by
    rw [continuous_pi_iff]
    intro j
    apply Continuous.subtype_mk
    exact (hhazardLip j).continuous
  have hrecovered : Continuous (fun a : Payoff G.Player =>
      recoveredContinuation G M d a (inv a).1.2) :=
    continuous_recoveredContinuation_comp G M d _ _ continuous_id hpInv
      (fun a => (inv a).2.2)
  have hxInv : Continuous (fun a : Payoff G.Player => (inv a).1.1) := by
    have hformula (a : Payoff G.Player) :
        recoveredContinuation G M d a (inv a).1.2 = (inv a).1.1 := by
      nth_rewrite 1 [← hright a]
      exact recoveredContinuation_phi G M d (inv a)
    rw [show (fun a : Payoff G.Player => (inv a).1.1) =
        (fun a => recoveredContinuation G M d a (inv a).1.2) by
      funext a
      exact (hformula a).symm]
    exact hrecovered
  have hinvContinuous : Continuous inv := by
    apply Continuous.subtype_mk
    change Continuous (fun a : Payoff G.Player =>
      ((inv a).1.1, (inv a).1.2))
    exact hxInv.prodMk hpInv
  exact ⟨⟨inv, hleft, hright, hinvContinuous⟩⟩

/-- The paper's straight-line condition for the structure homotopy. -/
def IsQuitStraightLineHomotopy (G : QuittingGame)
    (H : Payoff G.Player → UnitInterval → Payoff G.Player × QuitRow G) : Prop :=
  (Continuous fun z : Payoff G.Player × UnitInterval => H z.1 z.2) ∧
    ∀ x t,
      (H x t).1 = (t : ℝ) • (H x 1).1 + (1 - (t : ℝ)) • (H x 0).1 ∧
      ∀ j,
        ((H x t).2 j : ℝ) =
          (t : ℝ) * ((H x 1).2 j : ℝ) +
            (1 - (t : ℝ)) * ((H x 0).2 j : ℝ)

/-- The rational upper box occurring in Theorem 3.1(v). -/
def StructureTargetBox (G : QuittingGame) (M ρ : ℝ)
    (x : Payoff G.Player) : Prop :=
  ∀ j, MinMaxQuit G j - ρ / 2 ≤ x j ∧ x j ≤ M

/-- The closed cube `[-R,R]ᴺ`. -/
def InClosedPayoffBox {N : Type} [Fintype N] (R : ℝ)
    (x : Payoff N) : Prop :=
  ∀ j, -R ≤ x j ∧ x j ≤ R

/-- The straight-line homotopy obtained from the explicit inverse of `Phi`. -/
private def structureHomotopy (G : QuittingGame) {M d : ℝ}
    (inverse : PhiInverseData G M d)
    (x : Payoff G.Player) (t : UnitInterval) :
    Payoff G.Player × QuitRow G :=
  ((t : ℝ) • (inverse.inv x).1.1 + (1 - (t : ℝ)) • x,
    fun j => ⟨(t : ℝ) * ((inverse.inv x).1.2 j : ℝ),
      mul_nonneg t.property.1 ((inverse.inv x).1.2 j).property.1,
      (mul_le_one₀ t.property.2 ((inverse.inv x).1.2 j).property.1
        ((inverse.inv x).1.2 j).property.2)⟩)

@[simp] private theorem structureHomotopy_zero (G : QuittingGame) {M d : ℝ}
    (inverse : PhiInverseData G M d) (x : Payoff G.Player) :
    structureHomotopy G inverse x 0 = (x, zeroQuitRow G) := by
  ext j <;> simp [structureHomotopy, zeroQuitRow]

@[simp] private theorem structureHomotopy_one (G : QuittingGame) {M d : ℝ}
    (inverse : PhiInverseData G M d) (x : Payoff G.Player) :
    structureHomotopy G inverse x 1 = (inverse.inv x).1 := by
  ext j <;> simp [structureHomotopy]

/-- Points in the closure of the complement of `W` weakly dominate every
solo payoff. -/
private theorem soloPayoff_le_of_mem_closure_compl_WSet (G : QuittingGame)
    {x : Payoff G.Player} (hx : x ∈ closure ((WSet G)ᶜ)) :
    ∀ j, SoloPayoff G j ≤ x j := by
  have hsubset : (WSet G)ᶜ ⊆ {y | ∀ j, SoloPayoff G j ≤ y j} := by
    intro y hy j
    by_contra hj
    exact hy ⟨j, le_of_not_ge hj⟩
  have hclosed : IsClosed {y : Payoff G.Player | ∀ j, SoloPayoff G j ≤ y j} := by
    rw [show {y : Payoff G.Player | ∀ j, SoloPayoff G j ≤ y j} =
        ⋂ j, {y | SoloPayoff G j ≤ y j} by ext y; simp]
    exact isClosed_iInter fun j =>
      isClosed_le continuous_const (continuous_apply j)
  exact closure_minimal hsubset hclosed hx

/-- Conversely, weak solo-payoff dominance is the closure of strict dominance
over every player. -/
private theorem mem_closure_compl_WSet_of_soloPayoff_le (G : QuittingGame)
    {x : Payoff G.Player} (hx : ∀ j, SoloPayoff G j ≤ x j) :
    x ∈ closure ((WSet G)ᶜ) := by
  let approximant : ℕ → Payoff G.Player := fun n j =>
    x j + 1 / ((n : ℝ) + 1)
  have hmem : ∀ n, approximant n ∈ (WSet G)ᶜ := by
    intro n hW
    obtain ⟨j, hj⟩ := hW
    dsimp only [approximant] at hj
    have hpositive : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith [hx j]
  have htendsto : Tendsto approximant atTop (𝓝 x) := by
    apply tendsto_pi_nhds.2
    intro j
    simpa only [approximant, add_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => x j) atTop (𝓝 (x j))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  exact mem_closure_iff_seq_limit.mpr ⟨approximant, hmem, htendsto⟩

/-- The inverse-generated homotopy has the four structural properties that
do not use the properness estimate at infinity. -/
private theorem structureHomotopy_basic (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (inverse : PhiInverseData G M d) :
    IsQuitStraightLineHomotopy G (structureHomotopy G inverse) ∧
    (∀ x, structureHomotopy G inverse x 0 = (x, zeroQuitRow G)) ∧
    {z | ∃ x, structureHomotopy G inverse x 1 = z} = EZeroTilde G ∧
    ∀ x ∈ closure ((WSet G)ᶜ), ∀ t,
      structureHomotopy G inverse x t = (x, zeroQuitRow G) := by
  classical
  have hcontinuous : Continuous (fun z : Payoff G.Player × UnitInterval =>
      structureHomotopy G inverse z.1 z.2) := by
    have ht : Continuous (fun z : Payoff G.Player × UnitInterval => (z.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have hinv : Continuous (fun z : Payoff G.Player × UnitInterval =>
        inverse.inv z.1) := inverse.continuousInv.comp continuous_fst
    have hinvPair : Continuous (fun z : Payoff G.Player × UnitInterval =>
        (inverse.inv z.1).1) := continuous_subtype_val.comp hinv
    have hbeta : Continuous (fun z : Payoff G.Player × UnitInterval =>
        (inverse.inv z.1).1.1) := continuous_fst.comp hinvPair
    have hp : Continuous (fun z : Payoff G.Player × UnitInterval =>
        (inverse.inv z.1).1.2) := continuous_snd.comp hinvPair
    apply Continuous.prodMk
    · exact (ht.smul hbeta).add ((continuous_const.sub ht).smul continuous_fst)
    · rw [continuous_pi_iff]
      intro j
      apply Continuous.subtype_mk
      exact ht.mul (continuous_subtype_val.comp ((continuous_apply j).comp hp))
  have hstraight : ∀ x t,
      (structureHomotopy G inverse x t).1 =
          (t : ℝ) • (structureHomotopy G inverse x 1).1 +
            (1 - (t : ℝ)) • (structureHomotopy G inverse x 0).1 ∧
      ∀ j, ((structureHomotopy G inverse x t).2 j : ℝ) =
        (t : ℝ) * ((structureHomotopy G inverse x 1).2 j : ℝ) +
          (1 - (t : ℝ)) *
            ((structureHomotopy G inverse x 0).2 j : ℝ) := by
    intro x t
    constructor
    · simp only [structureHomotopy_one, structureHomotopy_zero]
      rfl
    · intro j
      simp [structureHomotopy]
  refine ⟨⟨hcontinuous, hstraight⟩, structureHomotopy_zero G inverse, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨x, hx⟩
      rw [structureHomotopy_one] at hx
      exact hx ▸ (inverse.inv x).2
    · intro hz
      let point : EZeroTilde G := ⟨z, hz⟩
      refine ⟨Phi G M d point, ?_⟩
      rw [structureHomotopy_one, inverse.leftInverse point]
  · intro x hx t
    have hxSolo := soloPayoff_le_of_mem_closure_compl_WSet G hx
    have hxGraph : (x, zeroQuitRow G) ∈ EZeroTilde G :=
      ((lemma3_1 G M d hM hd hd1).2.1 x).2 hxSolo
    let point : EZeroTilde G := ⟨(x, zeroQuitRow G), hxGraph⟩
    have hphi : Phi G M d point = x :=
      (lemma3_1 G M d hM hd hd1).2.2 x hxGraph
    have hinv : inverse.inv x = point := by
      rw [← hphi, inverse.leftInverse point]
    ext j
    · simp [structureHomotopy, hinv, point]
    · simp [structureHomotopy, hinv, point, zeroQuitRow]

/--
A single `ρ` satisfying the two motion estimates on the bounded continuation
region used in Sections 3--4 and excluding the sure rational row ruled out in
Case 2B of Lemma 3.4.  The latter scale exists by
`exists_excludedSureRationalRowScale`.  The printed phrase “`ρ` satisfies
Lemmas 2.1 and 2.3” mixes a common parameter with Lemma 2.3's pointwise
quantifiers `∀ r, ∃ ρ`; this predicate records the bounded uniformization
actually used by Lemmas 3.3--4.5 rather than silently asserting a global
`∃ ρ, ∀ r`.
-/
def IsStructureMotionParameter (G : QuittingGame) (M ρ : ℝ) : Prop :=
  SatisfiesCorrectedLemma2_1Parameter G ρ ∧
  0 < ρ ∧ ρ ≤ 1 ∧
  (∀ r : Payoff G.Player,
      (∀ j, MinMaxQuit G j - ρ ≤ r j ∧
        r j ≤ 2 * (Fintype.card G.Player : ℝ) * M) →
      ∀ p, p ∈ EpsilonRow G ρ r →
        ρ * QuitProbability G p ≤
          EuclideanDist r (QuittingOneStagePayoff G r p)) ∧
  ExcludesSureRationalRowAt G ρ

/-- A positive motion scale and the independently extracted no-instant scale
can be decreased to one common Section 3 parameter. -/
theorem exists_structureMotionParameter_of_base (G : QuittingGame) (M ρ0 : ℝ)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hρ0 : 0 < ρ0) (hρ01 : ρ0 ≤ 1)
    (hcorrected : SatisfiesCorrectedLemma2_1Parameter G ρ0)
    (hglobal : ∀ r : Payoff G.Player,
      (∀ j, MinMaxQuit G j - ρ0 ≤ r j ∧
        r j ≤ 2 * (Fintype.card G.Player : ℝ) * M) →
      ∀ p, p ∈ EpsilonRow G ρ0 r →
        ρ0 * QuitProbability G p ≤
          EuclideanDist r (QuittingOneStagePayoff G r p)) :
    ∃ ρ, IsStructureMotionParameter G M ρ := by
  obtain ⟨η, hη, hnoSure⟩ := exists_excludedSureRationalRowScale G hinstant
  let ρ := min ρ0 η
  have hρ : 0 < ρ := lt_min hρ0 hη
  have hρρ0 : ρ ≤ ρ0 := min_le_left _ _
  have hρη : ρ ≤ η := min_le_right _ _
  refine ⟨ρ, ?_, hρ, hρρ0.trans hρ01, ?_, ?_⟩
  · refine ⟨hρ, hρρ0.trans hρ01, ?_⟩
    intro r p hnear hrational hrow
    have hrational0 : IsRational G ρ0 r := by
      intro j
      have := hrational j
      linarith
    have hrow0 : p ∈ EpsilonRow G ρ0 r :=
      EpsilonRow.mono G hρρ0 r hrow
    obtain ⟨hmotion, hquit⟩ :=
      hcorrected.2.2 r p hnear hrational0 hrow0
    constructor
    · have hq : 0 ≤ QuitProbability G p := (quitProbability_mem_Icc G p).1
      exact (mul_le_mul_of_nonneg_right hρρ0 hq).trans hmotion
    · linarith
  · intro r hr p hrow
    have hr0 : ∀ j, MinMaxQuit G j - ρ0 ≤ r j ∧
        r j ≤ 2 * (Fintype.card G.Player : ℝ) * M := by
      intro j
      exact ⟨by linarith [(hr j).1], (hr j).2⟩
    have hrow0 : p ∈ EpsilonRow G ρ0 r :=
      EpsilonRow.mono G hρρ0 r hrow
    have hbound := hglobal r hr0 p hrow0
    have hq : 0 ≤ QuitProbability G p := (quitProbability_mem_Icc G p).1
    exact (mul_le_mul_of_nonneg_right hρρ0 hq).trans hbound
  · intro r p j hrational hrow hsure
    apply hnoSure r p j
    · intro k
      have := hrational k
      linarith
    · exact EpsilonRow.mono G hρη r hrow
    · exact hsure

/-- The full five-part conclusion of Theorem 3.1. -/
def StructureTheoremConclusion (G : QuittingGame) (M : ℝ) : Prop :=
  ∃ H : Payoff G.Player → UnitInterval → Payoff G.Player × QuitRow G,
    IsQuitStraightLineHomotopy G H ∧
    (∀ x, H x 0 = (x, zeroQuitRow G)) ∧
    {z | ∃ x, H x 1 = z} = EZeroTilde G ∧
    (∀ x ∈ closure ((WSet G)ᶜ), ∀ t, H x t = (x, zeroQuitRow G)) ∧
    ∀ (_hnormal : ∀ n, IsNormalPlayer G n)
      (_hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
      (_hinstant : ¬HasInstantApproximateEquilibria G)
      (ρ : ℝ), IsStructureMotionParameter G M ρ →
      (∀ x, x ∈ FRow G 0 x → x ∈ closure ((WSet G)ᶜ)) ∧
      ∃ R : ℝ, 0 < R ∧ ∀ x,
        ¬InClosedPayoffBox R x → ∀ t,
          ¬StructureTargetBox G M ρ (H x t).1

/-- Round precisely the displayed players' quitting probabilities to one. -/
private def roundedQuitRow (G : QuittingGame) [DecidableEq G.Player]
    (A : Finset G.Player)
    (p : QuitRow G) : QuitRow G := fun n =>
  if n ∈ A then 1 else p n

@[simp] private theorem roundedQuitRow_apply_mem (G : QuittingGame)
    [DecidableEq G.Player]
    (A : Finset G.Player) (p : QuitRow G) {n : G.Player} (hn : n ∈ A) :
    (roundedQuitRow G A p n : ℝ) = 1 := by
  simp [roundedQuitRow, hn]

@[simp] private theorem roundedQuitRow_apply_not_mem (G : QuittingGame)
    [DecidableEq G.Player]
    (A : Finset G.Player) (p : QuitRow G) {n : G.Player} (hn : n ∉ A) :
    roundedQuitRow G A p n = p n := by
  simp [roundedQuitRow, hn]

/-- After one player is forced, rounding the others is exactly replacement
of the Bernoulli factors indexed by `A \ {n}` with point masses at Quit. -/
@[simp] private theorem bernoulliBool_one_eq_pure_true
    (h0 : (0 : ℝ) ≤ 1) (h1 : (1 : ℝ) ≤ 1) :
    Math.ProbabilityMassFunction.bernoulliBool 1 h0 h1 = PMF.pure true := by
  apply Math.ProbabilityMassFunction.toVector_injective
  funext value
  cases value <;> simp [Math.ProbabilityMassFunction.toVector]

private theorem quitRowMarginals_eq_pure_true_of_apply_eq_one
    (G : QuittingGame) (p : QuitRow G) (n : G.Player)
    (hn : (p n : ℝ) = 1) : quitRowMarginals G p n = PMF.pure true := by
  apply Math.ProbabilityMassFunction.toVector_injective
  funext value
  cases value <;>
    simp [quitRowMarginals, Math.ProbabilityMassFunction.toVector, hn]

private theorem quitRowMarginals_rounded_replace
    (G : QuittingGame) [DecidableEq G.Player]
    (A : Finset G.Player) (p : QuitRow G)
    (n : G.Player) (q : Set.Icc (0 : ℝ) 1) :
    quitRowMarginals G ((roundedQuitRow G A p).replace G n q) =
      fun i => if i ∈ A.erase n then PMF.pure true
        else quitRowMarginals G (p.replace G n q) i := by
  classical
  funext i
  by_cases hin : i = n
  · subst i
    rw [if_neg (by simp)]
    apply GameTheory.quittingRootOfHazardRow_apply_congr
    simp [QuitRow.replace]
  · by_cases hiA : i ∈ A
    · have hierase : i ∈ A.erase n := Finset.mem_erase.mpr ⟨hin, hiA⟩
      rw [if_pos hierase]
      apply Math.ProbabilityMassFunction.toVector_injective
      funext action
      cases action <;>
        simp [GameTheory.quittingRootOfHazardRow, GameTheory.rootOfHazard,
          QuitRow.replace, roundedQuitRow, hin, hiA,
          Math.ProbabilityMassFunction.toVector]
    · have hierase : i ∉ A.erase n := fun hi => hiA (Finset.mem_of_mem_erase hi)
      rw [if_neg hierase]
      apply GameTheory.quittingRootOfHazardRow_apply_congr
      simp [QuitRow.replace, roundedQuitRow, hin, hiA]

/-- The law of the forced rounded row differs by at most the sum of the
Continue probabilities of the rounded players other than the forced one. -/
private theorem pmfTV_forced_roundedQuitRow_le_sum
    (G : QuittingGame) [DecidableEq G.Player]
    (A : Finset G.Player) (p : QuitRow G)
    (n : G.Player) (q : Set.Icc (0 : ℝ) 1) :
    Math.Probability.pmfTV
        (Math.PMFProduct.pmfPi (quitRowMarginals G (p.replace G n q)))
        (Math.PMFProduct.pmfPi
          (quitRowMarginals G ((roundedQuitRow G A p).replace G n q))) ≤
      ∑ i ∈ A.erase n, (1 - (p i : ℝ)) := by
  classical
  rw [quitRowMarginals_rounded_replace]
  refine (Math.PMFProduct.pmfTV_pmfPi_replaceOn_le_sum
    (quitRowMarginals G (p.replace G n q)) (fun _ => PMF.pure true)
    (A.erase n)).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≠ n := (Finset.mem_erase.mp hi).1
  simp [QuitRow.replace, hin]

/-- Rounding a forced row changes a one-stage payoff by the payoff
oscillation times the summed Continue mass of the rounded coordinates. -/
private theorem abs_forced_roundedQuitRow_payoff_sub_le
    (G : QuittingGame) [DecidableEq G.Player]
    (A : Finset G.Player) (p : QuitRow G) (r : Payoff G.Player)
    (n : G.Player) (q : Set.Icc (0 : ℝ) 1) {C : ℝ}
    (hosc : ∀ a b : G.Player → Bool,
      |GameTheory.quittingRootPayoff G.reward r a n -
        GameTheory.quittingRootPayoff G.reward r b n| ≤ C) :
    |QuittingOneStagePayoff G r ((roundedQuitRow G A p).replace G n q) n -
        QuittingOneStagePayoff G r (p.replace G n q) n| ≤
      C * ∑ i ∈ A.erase n, (1 - (p i : ℝ)) := by
  rw [quittingOneStagePayoff_eq_rootExpectedPayoff,
    quittingOneStagePayoff_eq_rootExpectedPayoff]
  rw [abs_sub_comm]
  exact (Math.Probability.abs_expect_sub_le_pairwise_mul_pmfTV
    (Math.PMFProduct.pmfPi (quitRowMarginals G (p.replace G n q)))
    (Math.PMFProduct.pmfPi
      (quitRowMarginals G ((roundedQuitRow G A p).replace G n q)))
    (fun action => GameTheory.quittingRootPayoff G.reward r action n) hosc).trans
      (mul_le_mul_of_nonneg_left
        (pmfTV_forced_roundedQuitRow_le_sum G A p n q)
        (le_trans (abs_nonneg _) (hosc (fun _ => false) (fun _ => false))))

private theorem action_true_of_pmfPi_ne_zero_of_marginal_eq_pure_true
    {ι : Type*} [Fintype ι] (root : ι → PMF Bool) (k : ι)
    (hk : root k = PMF.pure true) (action : ι → Bool)
    (ha : Math.PMFProduct.pmfPi root action ≠ 0) : action k = true := by
  classical
  by_contra hfalse
  have hak : action k = false := by cases h : action k <;> simp_all
  apply ha
  rw [Math.PMFProduct.pmfPi_apply]
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  rw [hk, hak]
  simp

/-- The same estimate with oscillation required only on the common support
where an already-rounded player quits surely. -/
private theorem abs_forced_roundedQuitRow_payoff_sub_le_of_sure_quitter
    (G : QuittingGame) [DecidableEq G.Player]
    (A : Finset G.Player) (p : QuitRow G) (r : Payoff G.Player)
    (n k : G.Player) (q : Set.Icc (0 : ℝ) 1) {C : ℝ}
    (hkn : k ≠ n) (hk : (p k : ℝ) = 1)
    (hosc : ∀ a b : G.Player → Bool, a k = true → b k = true →
      |GameTheory.quittingRootPayoff G.reward r a n -
        GameTheory.quittingRootPayoff G.reward r b n| ≤ C) :
    |QuittingOneStagePayoff G r ((roundedQuitRow G A p).replace G n q) n -
        QuittingOneStagePayoff G r (p.replace G n q) n| ≤
      C * ∑ i ∈ A.erase n, (1 - (p i : ℝ)) := by
  let oldRoot := quitRowMarginals G (p.replace G n q)
  let newRoot := quitRowMarginals G ((roundedQuitRow G A p).replace G n q)
  have holdK : oldRoot k = PMF.pure true := by
    apply quitRowMarginals_eq_pure_true_of_apply_eq_one
    simp [QuitRow.replace, hkn, hk]
  have hnewK : newRoot k = PMF.pure true := by
    apply quitRowMarginals_eq_pure_true_of_apply_eq_one
    simp only [QuitRow.replace]
    rw [if_neg hkn]
    by_cases hkA : k ∈ A
    · exact roundedQuitRow_apply_mem G A p hkA
    · simpa [roundedQuitRow_apply_not_mem G A p hkA] using hk
  rw [quittingOneStagePayoff_eq_rootExpectedPayoff,
    quittingOneStagePayoff_eq_rootExpectedPayoff]
  change |Math.Probability.expect (Math.PMFProduct.pmfPi newRoot)
      (fun action => GameTheory.quittingRootPayoff G.reward r action n) -
    Math.Probability.expect (Math.PMFProduct.pmfPi oldRoot)
      (fun action => GameTheory.quittingRootPayoff G.reward r action n)| ≤ _
  rw [abs_sub_comm]
  refine (Math.Probability.abs_expect_sub_le_pairwise_on_common_support_mul_pmfTV
    (Math.PMFProduct.pmfPi oldRoot) (Math.PMFProduct.pmfPi newRoot)
    (fun action => GameTheory.quittingRootPayoff G.reward r action n)
    (fun action => action k = true) (C := C) ?_ ?_ ?_).trans ?_
  · intro action haction
    exact action_true_of_pmfPi_ne_zero_of_marginal_eq_pure_true
      oldRoot k holdK action haction
  · intro action haction
    exact action_true_of_pmfPi_ne_zero_of_marginal_eq_pure_true
      newRoot k hnewK action haction
  · exact fun a ha b hb => hosc a b ha hb
  · apply mul_le_mul_of_nonneg_left
    · simpa only [oldRoot, newRoot] using
        pmfTV_forced_roundedQuitRow_le_sum G A p n q
    · exact le_trans (abs_nonneg _)
        (hosc (fun _ => true) (fun _ => true) rfl rfl)

/-- Under Simon's scale, the all-continue value zero and all quitting
outcomes have payoff oscillation at most `M / 3`. -/
private theorem quittingRootPayoff_zero_osc_le
    (G : QuittingGame) (M : ℝ) (hM : IsSimonPayoffScale G M)
    (n : G.Player) (a b : G.Player → Bool) :
    |GameTheory.quittingRootPayoff G.reward 0 a n -
      GameTheory.quittingRootPayoff G.reward 0 b n| ≤ M / 3 := by
  classical
  simp only [GameTheory.quittingRootPayoff]
  split_ifs with ha hb
  · linarith [hM.2.2
      ⟨GameTheory.quittingQuitters a, ha⟩
      ⟨GameTheory.quittingQuitters b, hb⟩ n]
  · simpa using hM.2.1 ⟨GameTheory.quittingQuitters a, ha⟩ n
  · simpa only [Pi.zero_apply, zero_sub, abs_neg] using
      hM.2.1 ⟨GameTheory.quittingQuitters b, by assumption⟩ n
  · have hM0 : 0 ≤ M := le_trans (by norm_num) hM.1
    norm_num
    positivity

/-- When both profiles contain one common sure quitter, only terminal rewards
occur and their oscillation is at most `M / 3`. -/
private theorem quittingRootPayoff_osc_le_of_common_quitter
    (G : QuittingGame) (M : ℝ) (hM : IsSimonPayoffScale G M)
    (r : Payoff G.Player) (n k : G.Player) (a b : G.Player → Bool)
    (hak : a k = true) (hbk : b k = true) :
    |GameTheory.quittingRootPayoff G.reward r a n -
      GameTheory.quittingRootPayoff G.reward r b n| ≤ M / 3 := by
  classical
  have ha : (GameTheory.quittingQuitters a).Nonempty := by
    refine ⟨k, ?_⟩
    simp [GameTheory.quittingQuitters, hak]
  have hb : (GameTheory.quittingQuitters b).Nonempty := by
    refine ⟨k, ?_⟩
    simp [GameTheory.quittingQuitters, hbk]
  simp only [GameTheory.quittingRootPayoff, ha, hb, dif_pos]
  linarith [hM.2.2
    ⟨GameTheory.quittingQuitters a, ha⟩
    ⟨GameTheory.quittingQuitters b, hb⟩ n]

/-- A bounded continuation coordinate enlarges the one-stage payoff
oscillation by at most its absolute bound. -/
private theorem quittingRootPayoff_osc_le_of_continuation_bound
    (G : QuittingGame) (M B : ℝ) (hM : IsSimonPayoffScale G M)
    (r : Payoff G.Player) (n : G.Player) (hr : |r n| ≤ B)
    (a b : G.Player → Bool) :
    |GameTheory.quittingRootPayoff G.reward r a n -
      GameTheory.quittingRootPayoff G.reward r b n| ≤ B + M / 3 := by
  classical
  have hB : 0 ≤ B := (abs_nonneg (r n)).trans hr
  simp only [GameTheory.quittingRootPayoff]
  split_ifs with ha hb
  · have hterminal := hM.2.2
      ⟨GameTheory.quittingQuitters a, ha⟩
      ⟨GameTheory.quittingQuitters b, hb⟩ n
    nlinarith
  · exact (abs_sub _ _).trans <| by
      linarith [hM.2.1 ⟨GameTheory.quittingQuitters a, ha⟩ n]
  · rw [abs_sub_comm]
    exact (abs_sub _ _).trans <| by
      linarith [hM.2.1 ⟨GameTheory.quittingQuitters b, by assumption⟩ n]
  · have hM0 : 0 ≤ M := le_trans (by norm_num) hM.1
    norm_num
    positivity

private theorem roundedQuitRow_round_singleton_eq
    (G : QuittingGame) [DecidableEq G.Player]
    (A : Finset G.Player) (p : QuitRow G) {k : G.Player} (hk : k ∈ A) :
    roundedQuitRow G A (roundedQuitRow G {k} p) = roundedQuitRow G A p := by
  funext n
  by_cases hn : n ∈ A
  · simp [roundedQuitRow, hn]
  · have hnk : n ≠ k := fun h => hn (h ▸ hk)
    simp [roundedQuitRow, hn, hnk]

private theorem quitProbability_eq_one_of_apply_eq_one
    (G : QuittingGame) (p : QuitRow G) (k : G.Player)
    (hk : (p k : ℝ) = 1) : QuitProbability G p = 1 := by
  simp only [QuitProbability]
  have hzero : (∏ n, (1 - (p n : ℝ))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    linarith
  rw [hzero]
  ring

private theorem forcedContinue_eq_of_sure_other
    (G : QuittingGame) (p : QuitRow G) (r s : Payoff G.Player)
    (n k : G.Player) (hkn : k ≠ n) (hk : (p k : ℝ) = 1) :
    ForcedContinuePayoff G r p n = ForcedContinuePayoff G s p n := by
  have hkReplace : ((p.replace G n 0) k : ℝ) = 1 := by
    simp [QuitRow.replace, hkn, hk]
  have hquit := quitProbability_eq_one_of_apply_eq_one G (p.replace G n 0) k hkReplace
  simp [ForcedContinuePayoff, QuittingOneStagePayoff, hquit]

private theorem sum_continue_le_card_mul
    (G : QuittingGame) [DecidableEq G.Player]
    (A : Finset G.Player) (p : QuitRow G) (δ : ℝ)
    (hδ : 0 ≤ δ) (hA : ∀ i ∈ A, 1 - (p i : ℝ) ≤ δ) (n : G.Player) :
    ∑ i ∈ A.erase n, (1 - (p i : ℝ)) ≤
      (Fintype.card G.Player : ℝ) * δ := by
  calc
    (∑ i ∈ A.erase n, (1 - (p i : ℝ))) ≤ ∑ _i ∈ A.erase n, δ := by
      apply Finset.sum_le_sum
      intro i hi
      exact hA i (Finset.mem_of_mem_erase hi)
    _ = (A.erase n).card * δ := by simp
    _ ≤ (Fintype.card G.Player : ℝ) * δ := by
      gcongr
      exact_mod_cast Finset.card_le_univ (s := A.erase n)

/-- Lemma 3.3's rounding-to-a-sure-quitter hypotheses and conclusion. -/
def Lemma3_3Statement (G : QuittingGame) (M ε : ℝ) : Prop :=
  ∀ (β : Payoff G.Player) (p : QuitRow G),
    (β, p) ∈ EZeroTilde G → 0 < ε → ε ≤ 1 →
    (∀ j, -(Fintype.card G.Player : ℝ) * M ≤ β j) →
    ∀ k,
      1 - ε / (2 * (Fintype.card G.Player : ℝ) * M) ≤ (p k : ℝ) →
      MinMaxQuit G k - ε / 2 ≤ β k →
      (∀ l,
        (p l : ℝ) ≤ 1 - ε / (2 * (Fintype.card G.Player : ℝ) * M) →
          β l ≤ (Fintype.card G.Player : ℝ) * M) →
    ∃ r : Payoff G.Player, ∃ p' : QuitRow G,
      IsRational G ε r ∧ (p' k : ℝ) = 1 ∧ p' ∈ EpsilonRow G ε r

/--
Lemma 3.3.  Round to one every `p_m` above the displayed threshold whose
continuation payoff is at least `χ_m-ε/2`, and replace the continuation vector
by `χ-ε`.  Product-law total variation bounds the resulting endpoint-payoff
changes by `ε/6` and `5ε/6`.
-/
theorem lemma3_3 (G : QuittingGame) (M ε : ℝ)
    (hM : IsSimonPayoffScale G M) (hplayers : HasAtLeastThreePlayers G) :
    Lemma3_3Statement G M ε := by
  classical
  intro β p hp hε hε1 hβLower k hk hβk hβUpper
  let N : ℝ := Fintype.card G.Player
  let δ : ℝ := ε / (2 * N * M)
  let A : Finset G.Player := Finset.univ.filter fun n =>
    1 - δ ≤ (p n : ℝ) ∧ MinMaxQuit G n - ε / 2 ≤ β n
  let r : Payoff G.Player := fun n => MinMaxQuit G n - ε
  let p' : QuitRow G := roundedQuitRow G A p
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM.1
  have hplayersNat : 3 ≤ Fintype.card G.Player := by
    simpa only [HasAtLeastThreePlayers] using hplayers
  have hN : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hplayersNat
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNM : 3 ≤ N * M := by
    have hprod := mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hM.1)
    have hMone : 1 ≤ M := hM.1
    ring_nf at hprod
    linarith
  have hδ : 0 ≤ δ := by positivity
  have hδlt : δ < 1 := by
    dsimp only [δ]
    rw [div_lt_one (by positivity : 0 < 2 * N * M)]
    nlinarith
  have hkA : k ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hk, hβk⟩
  have hAContinue : ∀ i ∈ A, 1 - (p i : ℝ) ≤ δ := by
    intro i hi
    linarith [(Finset.mem_filter.mp hi).2.1]
  have hsum : ∀ n, ∑ i ∈ A.erase n, (1 - (p i : ℝ)) ≤ N * δ := by
    intro n
    exact sum_continue_le_card_mul G A p δ hδ hAContinue n
  have hscale : M / 3 * (N * δ) = ε / 6 := by
    dsimp only [δ, N]
    field_simp
    all_goals ring
  have hscaleFive : (5 * M / 3) * (N * δ) = 5 * ε / 6 := by
    rw [show 5 * M / 3 = 5 * (M / 3) by ring, mul_assoc, hscale]
    ring
  have hscaleTwo : (N * M + M) * δ ≤ 2 * ε / 3 := by
    have heq : (N * M + M) * δ = ε * ((N + 1) / (2 * N)) := by
      dsimp only [δ]
      field_simp
    have hratio : (N + 1) / (2 * N) ≤ (2 : ℝ) / 3 := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * N)]
      nlinarith
    rw [heq]
    calc
      ε * ((N + 1) / (2 * N)) ≤ ε * ((2 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left hratio hε.le
      _ = 2 * ε / 3 := by ring
  refine ⟨r, p', ?_, ?_, ?_⟩
  · intro n
    simp [r]
  · exact roundedQuitRow_apply_mem G A p hkA
  · have hchi : ∀ n, |MinMaxQuit G n| ≤ M / 3 := by
      intro n
      apply abs_minMaxQuit_le_of_reward_bound G n
      · positivity
      · exact fun outcome => hM.2.1 outcome n
    have haClose : ∀ n,
        |ForcedQuitPayoff G p' n - ForcedQuitPayoff G p n| ≤ ε / 6 := by
      intro n
      calc
        |ForcedQuitPayoff G p' n - ForcedQuitPayoff G p n| ≤
            (M / 3) * ∑ i ∈ A.erase n, (1 - (p i : ℝ)) := by
          exact abs_forced_roundedQuitRow_payoff_sub_le G A p 0 n 1
            (quittingRootPayoff_zero_osc_le G M hM n)
        _ ≤ (M / 3) * (N * δ) := by
          exact mul_le_mul_of_nonneg_left (hsum n) (by positivity)
        _ = ε / 6 := hscale
    have hrBound : ∀ n, |r n| ≤ 4 * M / 3 := by
      intro n
      change |MinMaxQuit G n - ε| ≤ 4 * M / 3
      calc
        |MinMaxQuit G n - ε| ≤ |MinMaxQuit G n| + |ε| := abs_sub _ _
        _ ≤ M / 3 + M := by
          rw [abs_of_pos hε]
          exact add_le_add (hchi n) (hε1.trans hM.1)
        _ = 4 * M / 3 := by ring
    have hbCloseA : ∀ n,
        |ForcedContinuePayoff G r p' n - ForcedContinuePayoff G r p n| ≤
          5 * ε / 6 := by
      intro n
      calc
        |ForcedContinuePayoff G r p' n - ForcedContinuePayoff G r p n| ≤
            (4 * M / 3 + M / 3) *
              ∑ i ∈ A.erase n, (1 - (p i : ℝ)) := by
          exact abs_forced_roundedQuitRow_payoff_sub_le G A p r n 0
            (quittingRootPayoff_osc_le_of_continuation_bound
              G M (4 * M / 3) hM r n (hrBound n))
        _ = (5 * M / 3) * ∑ i ∈ A.erase n, (1 - (p i : ℝ)) := by ring
        _ ≤ (5 * M / 3) * (N * δ) := by
          exact mul_le_mul_of_nonneg_left (hsum n) (by positivity)
        _ = 5 * ε / 6 := hscaleFive
    have hBetaBound : ∀ n, n ∉ A → |β n| ≤ N * M := by
      intro n hnA
      have hnA' : ¬(1 - δ ≤ (p n : ℝ) ∧
          MinMaxQuit G n - ε / 2 ≤ β n) := by
        simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hnA
      have hupper : β n ≤ N * M := by
        by_cases hprob : 1 - δ ≤ (p n : ℝ)
        · have hpay : β n < MinMaxQuit G n - ε / 2 := by
            exact lt_of_not_ge fun h => hnA' ⟨hprob, h⟩
          have hchiUpper : MinMaxQuit G n ≤ M / 3 :=
            (le_abs_self _).trans (hchi n)
          have hNM : M / 3 ≤ N * M := by nlinarith
          linarith
        · apply hβUpper n
          simpa only [δ, N] using le_of_not_ge hprob
      have hlower : -(N * M) ≤ β n := by
        simpa only [N, neg_mul] using hβLower n
      exact abs_le.mpr ⟨hlower, hupper⟩
    have hbCloseNotA : ∀ n, n ∉ A →
        |ForcedContinuePayoff G r p' n - ForcedContinuePayoff G β p n| ≤
          5 * ε / 6 := by
      intro n hnA
      have hkn : k ≠ n := fun h => hnA (h ▸ hkA)
      let pK : QuitRow G := roundedQuitRow G {k} p
      have hpKk : (pK k : ℝ) = 1 := by
        exact roundedQuitRow_apply_mem G {k} p (by simp)
      have hfirst :
          |ForcedContinuePayoff G β pK n - ForcedContinuePayoff G β p n| ≤
            2 * ε / 3 := by
        calc
          |ForcedContinuePayoff G β pK n - ForcedContinuePayoff G β p n| ≤
              (N * M + M / 3) * (1 - (p k : ℝ)) := by
            have hraw := abs_forced_roundedQuitRow_payoff_sub_le
              G {k} p β n 0
              (quittingRootPayoff_osc_le_of_continuation_bound
                G M (N * M) hM β n (hBetaBound n hnA))
            simpa [pK, ForcedContinuePayoff, hkn, Ne.symm hkn] using hraw
          _ ≤ (N * M + M) * (1 - (p k : ℝ)) := by
            apply mul_le_mul_of_nonneg_right
            · nlinarith
            · exact sub_nonneg.mpr (p k).property.2
          _ ≤ (N * M + M) * δ := by
            exact mul_le_mul_of_nonneg_left (hAContinue k hkA) (by positivity)
          _ ≤ 2 * ε / 3 := hscaleTwo
      have hAContinueK : ∀ i ∈ A, 1 - (pK i : ℝ) ≤ δ := by
        intro i hi
        by_cases hik : i = k
        · subst i
          rw [hpKk]
          linarith
        · simpa [pK, roundedQuitRow, hik] using hAContinue i hi
      have hsumK : ∑ i ∈ A.erase n, (1 - (pK i : ℝ)) ≤ N * δ :=
        sum_continue_le_card_mul G A pK δ hδ hAContinueK n
      have hsecond :
          |ForcedContinuePayoff G β p' n - ForcedContinuePayoff G β pK n| ≤
            ε / 6 := by
        have hround : roundedQuitRow G A pK = p' := by
          change roundedQuitRow G A (roundedQuitRow G {k} p) = roundedQuitRow G A p
          exact roundedQuitRow_round_singleton_eq G A p hkA
        calc
          |ForcedContinuePayoff G β p' n - ForcedContinuePayoff G β pK n| ≤
              (M / 3) * ∑ i ∈ A.erase n, (1 - (pK i : ℝ)) := by
            rw [← hround]
            exact abs_forced_roundedQuitRow_payoff_sub_le_of_sure_quitter
              G A pK β n k 0 hkn hpKk
              (quittingRootPayoff_osc_le_of_common_quitter G M hM β n k)
          _ ≤ (M / 3) * (N * δ) :=
            mul_le_mul_of_nonneg_left hsumK (by positivity)
          _ = ε / 6 := hscale
      have hrβ : ForcedContinuePayoff G r p' n =
          ForcedContinuePayoff G β p' n := by
        apply forcedContinue_eq_of_sure_other G p' r β n k hkn
        exact roundedQuitRow_apply_mem G A p hkA
      rw [hrβ]
      calc
        |ForcedContinuePayoff G β p' n - ForcedContinuePayoff G β p n| ≤
            |ForcedContinuePayoff G β p' n - ForcedContinuePayoff G β pK n| +
              |ForcedContinuePayoff G β pK n - ForcedContinuePayoff G β p n| :=
          abs_sub_le _ _ _
        _ ≤ ε / 6 + 2 * ε / 3 := add_le_add hsecond hfirst
        _ = 5 * ε / 6 := by ring
    have hpExact : p ∈ EpsilonRow G 0 β := hp.1
    constructor
    · intro n hp'Pos
      by_cases hnA : n ∈ A
      · have hpPos : 0 < (p n : ℝ) := by
          have hnLarge := (Finset.mem_filter.mp hnA).2.1
          linarith
        have hold := hpExact.1 n hpPos
        have hrβ : ForcedContinuePayoff G r p n ≤
            ForcedContinuePayoff G β p n := by
          apply forcedContinue_mono_continuation_coord
          have hnRational := (Finset.mem_filter.mp hnA).2.2
          change MinMaxQuit G n - ε ≤ β n
          linarith
        have ha := (abs_le.mp (haClose n)).1
        have hb := (abs_le.mp (hbCloseA n)).2
        linarith
      · have hpEq : p' n = p n := by
          exact roundedQuitRow_apply_not_mem G A p hnA
        have hpPos : 0 < (p n : ℝ) := by
          rw [← hpEq]
          exact hp'Pos
        have hold := hpExact.1 n hpPos
        have ha := (abs_le.mp (haClose n)).1
        have hb := (abs_le.mp (hbCloseNotA n hnA)).2
        linarith
    · intro n hp'Lt
      have hnA : n ∉ A := by
        intro hnA
        have hpOne := roundedQuitRow_apply_mem G A p hnA
        change (p' n : ℝ) = 1 at hpOne
        linarith
      have hpEq : p' n = p n := roundedQuitRow_apply_not_mem G A p hnA
      have hpLt : (p n : ℝ) < 1 := by
        rw [← hpEq]
        exact hp'Lt
      have hold := hpExact.2 n hpLt
      have ha := (abs_le.mp (haClose n)).2
      have hb := (abs_le.mp (hbCloseNotA n hnA)).1
      linarith

/-- A common coordinatewise ceiling for continuation and absorption bounds the row value. -/
private theorem quittingOneStagePayoff_le_of_coordinate_le
    (G : QuittingGame) (beta : Payoff G.Player) (p : QuitRow G)
    (n : G.Player) (bound : ℝ)
    (hreward : ∀ A, G.reward A n ≤ bound) (hbeta : beta n ≤ bound) :
    QuittingOneStagePayoff G beta p n ≤ bound := by
  rw [quittingOneStagePayoff_eq_rootExpectedPayoff]
  unfold GameTheory.quittingRootExpectedPayoff
  calc
    Math.Probability.expect (Math.PMFProduct.pmfPi (quitRowMarginals G p))
        (fun action => GameTheory.quittingRootPayoff G.reward beta action n) ≤
        Math.Probability.expect (Math.PMFProduct.pmfPi (quitRowMarginals G p))
          (fun _ => bound) := by
      apply Math.Probability.expect_mono
      intro action
      by_cases hquit : (GameTheory.quittingQuitters action).Nonempty
      · simpa [GameTheory.quittingRootPayoff, hquit] using
          hreward ⟨GameTheory.quittingQuitters action, hquit⟩
      · simpa [GameTheory.quittingRootPayoff, hquit] using hbeta
    _ = bound := Math.Probability.expect_const _ _

/-- The exact one-stage equilibrium graph is closed.  The support implications
are written as unions with the zero and one faces, so no strict support set is
mistaken for a closed condition. -/
private theorem isClosed_epsilonEquilibriumGraph_zero (G : QuittingGame) :
    IsClosed (EpsilonEquilibriumGraph G 0) := by
  classical
  let quitCondition : G.Player → Set (Payoff G.Player × QuitRow G) := fun n =>
    {z | (z.2 n : ℝ) = 0} ∪
      {z | ForcedContinuePayoff G z.1 z.2 n ≤ ForcedQuitPayoff G z.2 n}
  let continueCondition : G.Player → Set (Payoff G.Player × QuitRow G) := fun n =>
    {z | (z.2 n : ℝ) = 1} ∪
      {z | ForcedQuitPayoff G z.2 n ≤ ForcedContinuePayoff G z.1 z.2 n}
  have hp : Continuous (fun z : Payoff G.Player × QuitRow G => z.2) :=
    continuous_snd
  have hr : Continuous (fun z : Payoff G.Player × QuitRow G => z.1) :=
    continuous_fst
  have hreplace (n : G.Player) (q : UnitInterval) :
      Continuous (fun z : Payoff G.Player × QuitRow G => z.2.replace G n q) := by
    rw [continuous_pi_iff]
    intro k
    by_cases hkn : k = n
    · subst k
      simpa [QuitRow.replace] using
        (continuous_const : Continuous
          (fun _ : Payoff G.Player × QuitRow G => q))
    · simpa [QuitRow.replace, hkn, Function.comp_def] using
        (continuous_apply k).comp hp
  have hforced (n : G.Player) : Continuous
      (fun z : Payoff G.Player × QuitRow G => ForcedQuitPayoff G z.2 n) := by
    exact continuous_quittingOneStagePayoff_comp G
      (fun _ : Payoff G.Player × QuitRow G => (0 : Payoff G.Player))
      (fun z : Payoff G.Player × QuitRow G => z.2.replace G n 1)
      continuous_const (hreplace n 1) n
  have hcontinue (n : G.Player) : Continuous
      (fun z : Payoff G.Player × QuitRow G =>
        ForcedContinuePayoff G z.1 z.2 n) := by
    exact continuous_quittingOneStagePayoff_comp G
      (fun z : Payoff G.Player × QuitRow G => z.1)
      (fun z : Payoff G.Player × QuitRow G => z.2.replace G n 0)
      hr (hreplace n 0) n
  have hquitClosed (n : G.Player) : IsClosed (quitCondition n) := by
    apply IsClosed.union
    · exact isClosed_eq ((continuous_subtype_val.comp
        ((continuous_apply n).comp hp))) continuous_const
    · exact isClosed_le (hcontinue n) (hforced n)
  have hcontinueClosed (n : G.Player) : IsClosed (continueCondition n) := by
    apply IsClosed.union
    · exact isClosed_eq ((continuous_subtype_val.comp
        ((continuous_apply n).comp hp))) continuous_const
    · exact isClosed_le (hforced n) (hcontinue n)
  have heq : EpsilonEquilibriumGraph G 0 =
      ⋂ n, quitCondition n ∩ continueCondition n := by
    ext z
    simp only [Set.mem_iInter, Set.mem_inter_iff]
    constructor
    · intro hz n
      have hpRow : z.2 ∈ EpsilonRow G 0 z.1 := hz
      constructor
      · by_cases hn : (z.2 n : ℝ) = 0
        · exact Set.mem_union_left _ hn
        · apply Set.mem_union_right
          have hnpos : 0 < (z.2 n : ℝ) :=
            lt_of_le_of_ne (z.2 n).property.1 (Ne.symm hn)
          simpa using hpRow.1 n hnpos
      · by_cases hn : (z.2 n : ℝ) = 1
        · exact Set.mem_union_left _ hn
        · apply Set.mem_union_right
          have hnlt : (z.2 n : ℝ) < 1 :=
            lt_of_le_of_ne (z.2 n).property.2 hn
          simpa using hpRow.2 n hnlt
    · intro hz
      change _ ∈ EpsilonRow G 0 _
      constructor
      · intro n hnpos
        rcases (hz n).1 with hnzero | hnineq
        · change (z.2 n : ℝ) = 0 at hnzero
          linarith
        · simpa using hnineq
      · intro n hnlt
        rcases (hz n).2 with hnone | hnineq
        · change (z.2 n : ℝ) = 1 at hnone
          linarith
        · simpa using hnineq
  rw [heq]
  exact isClosed_iInter fun n => (hquitClosed n).inter (hcontinueClosed n)

/-- The constants selected after Lemma 3.3 and used in Lemma 3.4. -/
def AreSection3Constants (G : QuittingGame) (M d ρ ξ R : ℝ) : Prop :=
  0 < ξ ∧
  ξ ≤ (1 / 20 : ℝ) *
    (ρ / (2 * (Fintype.card G.Player : ℝ) * M)) ^ Fintype.card G.Player ∧
  R = 10 * (Fintype.card G.Player : ℝ) * M /
    (d * ξ ^ Fintype.card G.Player) ∧
  ∀ (β : Payoff G.Player) (p : QuitRow G),
    (β, p) ∈ EZeroTilde G →
    (∀ j, MinMaxQuit G j - ρ ≤ β j ∧
      β j ≤ 2 * (Fintype.card G.Player : ℝ) * M) →
    ∀ j, (p j : ℝ) ≤ 1 - ξ

/-- The bounded exact-equilibrium slice used to choose the uniform distance
from the sure-Quit faces. -/
private def boundedExactEquilibriumSlice (G : QuittingGame) (M ρ : ℝ) :
    Set (Payoff G.Player × QuitRow G) :=
  EpsilonEquilibriumGraph G 0 ∩
    ({β | ∀ j, MinMaxQuit G j - ρ ≤ β j ∧
      β j ≤ 2 * (Fintype.card G.Player : ℝ) * M} ×ˢ Set.univ)

private theorem isCompact_boundedExactEquilibriumSlice
    (G : QuittingGame) (M ρ : ℝ) :
    IsCompact (boundedExactEquilibriumSlice G M ρ) := by
  have hbeta : IsCompact
      {β : Payoff G.Player | ∀ j, MinMaxQuit G j - ρ ≤ β j ∧
        β j ≤ 2 * (Fintype.card G.Player : ℝ) * M} := by
    exact isCompact_pi_infinite fun _ => isCompact_Icc
  have hproduct : IsCompact
      ({β : Payoff G.Player | ∀ j, MinMaxQuit G j - ρ ≤ β j ∧
        β j ≤ 2 * (Fintype.card G.Player : ℝ) * M} ×ˢ
          (Set.univ : Set (QuitRow G))) :=
    hbeta.prod isCompact_univ
  exact hproduct.inter_left (isClosed_epsilonEquilibriumGraph_zero G)

/-- On the bounded exact-equilibrium slice, exclusion of rational sure-Quit
rows gives one positive survival slack for every player. -/
private theorem exists_uniform_boundedExactEquilibriumSlack
    (G : QuittingGame) (M ρ : ℝ)
    (hρ : 0 < ρ) (hexcludes : ExcludesSureRationalRowAt G ρ) :
    ∃ ξ, 0 < ξ ∧ ∀ β p,
      (β, p) ∈ EpsilonEquilibriumGraph G 0 →
      (∀ j, MinMaxQuit G j - ρ ≤ β j ∧
        β j ≤ 2 * (Fintype.card G.Player : ℝ) * M) →
      ∀ j, (p j : ℝ) ≤ 1 - ξ := by
  classical
  let K := boundedExactEquilibriumSlice G M ρ
  have hK : IsCompact K := isCompact_boundedExactEquilibriumSlice G M ρ
  by_cases hKne : K.Nonempty
  · let survival : Payoff G.Player × QuitRow G → ℝ :=
      fun z : Payoff G.Player × QuitRow G => 1 - QuitProbability G z.2
    have hsurvivalContinuous : Continuous survival := by
      exact continuous_const.sub
        (continuous_quitProbability_comp G
          (fun z : Payoff G.Player × QuitRow G => z.2) continuous_snd)
    obtain ⟨least, hleastK, hleast⟩ :=
      hK.exists_isMinOn hKne hsurvivalContinuous.continuousOn
    have hleastExact : least ∈ EpsilonEquilibriumGraph G 0 := hleastK.1
    have hleastBounds : ∀ j,
        MinMaxQuit G j - ρ ≤ least.1 j ∧
          least.1 j ≤ 2 * (Fintype.card G.Player : ℝ) * M := hleastK.2.1
    have hleastRational : IsRational G ρ least.1 := fun j =>
      (hleastBounds j).1
    have hleastRow : least.2 ∈ EpsilonRow G ρ least.1 :=
      EpsilonRow.mono G hρ.le least.1 hleastExact
    have hcoordLt (j : G.Player) : (least.2 j : ℝ) < 1 := by
      by_contra hnot
      have hj : (least.2 j : ℝ) = 1 :=
        le_antisymm (least.2 j).property.2 (le_of_not_gt hnot)
      exact hexcludes least.1 least.2 j hleastRational hleastRow hj
    have hslack : 0 < survival least := by
      dsimp only [survival]
      rw [QuitProbability, sub_sub_cancel]
      exact Finset.prod_pos fun j _ => sub_pos.mpr (hcoordLt j)
    refine ⟨survival least, hslack, ?_⟩
    intro β p hexact hbounds j
    have hmem : (β, p) ∈ K := ⟨hexact, hbounds, Set.mem_univ p⟩
    have hmin : survival least ≤ survival (β, p) := hleast hmem
    have hfactorNonneg : 0 ≤ 1 - (p j : ℝ) :=
      sub_nonneg.mpr (p j).property.2
    have hotherLe :
        ∏ k ∈ Finset.univ.erase j, (1 - (p k : ℝ)) ≤ 1 := by
      calc
        _ ≤ ∏ _k ∈ Finset.univ.erase j, (1 : ℝ) := by
          apply Finset.prod_le_prod
          · intro k _hk
            exact sub_nonneg.mpr (p k).property.2
          · intro k _hk
            linarith [(p k).property.1]
        _ = 1 := by simp
    have hsurvivalCoord : survival (β, p) ≤ 1 - (p j : ℝ) := by
      dsimp only [survival, QuitProbability, sub_sub_cancel]
      rw [← Finset.mul_prod_erase Finset.univ
        (fun k => 1 - (p k : ℝ)) (Finset.mem_univ j)]
      nlinarith
    dsimp only [survival] at hmin
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro β p hexact hbounds
    exact (hKne ⟨(β, p), hexact, hbounds, Set.mem_univ p⟩).elim

/-- The choices of `ξ` and `R` made before Lemma 3.4 exist with precisely the
bounds recorded in `AreSection3Constants`. -/
private theorem exists_section3Constants (G : QuittingGame)
    (M d ρ : ℝ) (hM : IsSimonPayoffScale G M) (_hd : 0 < d)
    (hmotion : IsStructureMotionParameter G M ρ) :
    ∃ ξ R, AreSection3Constants G M d ρ ξ R := by
  let threshold : ℝ := (1 / 20 : ℝ) *
    (ρ / (2 * (Fintype.card G.Player : ℝ) * M)) ^ Fintype.card G.Player
  have hthreshold : 0 < threshold := by
    dsimp only [threshold]
    have hcard : 0 < (Fintype.card G.Player : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hMpos : 0 < M := zero_lt_one.trans_le hM.1
    have hratio : 0 < ρ / (2 * (Fintype.card G.Player : ℝ) * M) :=
      div_pos hmotion.2.1 (by positivity)
    exact mul_pos (by norm_num) (pow_pos hratio _)
  obtain ⟨slack, hslack, hbound⟩ :=
    exists_uniform_boundedExactEquilibriumSlack G M ρ hmotion.2.1
      hmotion.2.2.2.2
  let ξ := min slack threshold
  have hξ : 0 < ξ := lt_min hslack hthreshold
  have hξthreshold : ξ ≤ threshold := min_le_right _ _
  let R := 10 * (Fintype.card G.Player : ℝ) * M /
    (d * ξ ^ Fintype.card G.Player)
  refine ⟨ξ, R, hξ, hξthreshold, rfl, ?_⟩
  intro β p hp hbounds j
  exact (hbound β p hp.1 hbounds j).trans (by
    dsimp only [ξ]
    linarith [min_le_left slack threshold])

/-- The constants chosen after Lemma 3.3 satisfy `0 < ξ < 1` and `10NM ≤ R`. -/
private theorem section3Constants_radius_bound (G : QuittingGame)
    (M d ρ ξ R : ℝ) (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R) :
    0 < ξ ∧ ξ < 1 ∧
      10 * (Fintype.card G.Player : ℝ) * M ≤ R := by
  let N : ℝ := Fintype.card G.Player
  have hN : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hplayers
  have hNpos : 0 < N := by linarith
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM.1
  have hρpos : 0 < ρ := hmotion.2.1
  have hρ1 : ρ ≤ 1 := hmotion.2.2.1
  have hratioPos : 0 < ρ / (2 * N * M) := by positivity
  have hdenSix : 6 ≤ 2 * N * M := by
    have hNM : 3 * 1 ≤ N * M :=
      mul_le_mul hN hM.1 (by norm_num) hNpos.le
    nlinarith
  have hratioOne : ρ / (2 * N * M) ≤ 1 := by
    rw [div_le_one (by positivity : 0 < 2 * N * M)]
    linarith
  have hpowOne : (ρ / (2 * N * M)) ^ Fintype.card G.Player ≤ 1 :=
    pow_le_one₀ hratioPos.le hratioOne
  have hξ : 0 < ξ := hconstants.1
  have hξOne : ξ < 1 := by
    have hsmall := hconstants.2.1
    dsimp only [N] at hsmall hpowOne
    nlinarith
  have hpowPos : 0 < ξ ^ Fintype.card G.Player := pow_pos hξ _
  have hpowξOne : ξ ^ Fintype.card G.Player ≤ 1 :=
    pow_le_one₀ hξ.le hξOne.le
  have hdenomPos : 0 < d * ξ ^ Fintype.card G.Player := mul_pos hd hpowPos
  have hdenomOne : d * ξ ^ Fintype.card G.Player ≤ 1 := by
    calc
      d * ξ ^ Fintype.card G.Player ≤
          1 * ξ ^ Fintype.card G.Player :=
        mul_le_mul_of_nonneg_right hd1 hpowPos.le
      _ ≤ 1 := by simpa using hpowξOne
  refine ⟨hξ, hξOne, ?_⟩
  rw [hconstants.2.2.1, le_div_iff₀ hdenomPos]
  have hbound := mul_le_mul_of_nonneg_left hdenomOne
    (show 0 ≤ 10 * N * M by positivity)
  simpa only [N, mul_one] using hbound

/-- The positive-coordinate estimate used in Lemma 3.4: `φ_j > R` forces `p_j = 0`. -/
private theorem lemma3_4_positive_coordinate (G : QuittingGame)
    (M d ρ ξ R : ℝ) (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (z : EZeroTilde G) (j : G.Player) (hj : R < Phi G M d z j) :
    R - (Fintype.card G.Player : ℝ) * M < z.1.1 j ∧
      (z.1.2 j : ℝ) = 0 := by
  classical
  let N : ℝ := Fintype.card G.Player
  let beta := z.1.1
  let p := z.1.2
  have hN : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hplayers
  have hNpos : 0 < N := by linarith
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM.1
  obtain ⟨_, _, hR⟩ := section3Constants_radius_bound G M d ρ ξ R
    hplayers hM hd hd1 hmotion hconstants
  have hNM : 3 * M ≤ N * M :=
    mul_le_mul_of_nonneg_right hN hMpos.le
  have hsum : ∑ k ∈ Finset.univ.erase j, (p k : ℝ) ≤ N := by
    calc
      ∑ k ∈ Finset.univ.erase j, (p k : ℝ) ≤
          ∑ _k ∈ Finset.univ.erase j, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        exact (p k).property.2
      _ = ((Finset.univ.erase j).card : ℝ) := by simp
      _ ≤ N := by
        dsimp only [N]
        exact_mod_cast (Finset.card_erase_le :
          (Finset.univ.erase j).card ≤ (Finset.univ : Finset G.Player).card)
  have hsumM : M * ∑ k ∈ Finset.univ.erase j, (p k : ℝ) ≤ N * M := by
    nlinarith [mul_le_mul_of_nonneg_left hsum hMpos.le]
  have hpjZero : (p j : ℝ) = 0 := by
    by_contra hpjNe
    have hpj : 0 < (p j : ℝ) :=
      lt_of_le_of_ne (p j).property.1 (Ne.symm hpjNe)
    have hstage := oneStagePayoff_eq_forcedQuit_of_positive G beta p
      z.2.1 z.2.2 j hpj
    have hforced := abs_forcedQuitPayoff_le_scale G M hM p j
    have hcoefficient : 0 ≤ 5 * N * M / d := by positivity
    have hpenalty :
        0 ≤ (p j : ℝ) / (1 - (p j : ℝ)) ^ Fintype.card G.Player :=
      div_nonneg (p j).property.1
        (pow_nonneg (sub_nonneg.mpr (p j).property.2) _)
    have hphiUpper : Phi G M d z j ≤ M / 3 + N * M := by
      change QuittingOneStagePayoff G beta p j -
          (5 * N * M / d) *
            ((p j : ℝ) / (1 - (p j : ℝ)) ^ Fintype.card G.Player) +
          M * ∑ k ∈ Finset.univ.erase j, (p k : ℝ) ≤ M / 3 + N * M
      rw [hstage]
      nlinarith [le_abs_self (ForcedQuitPayoff G p j),
        mul_nonneg hcoefficient hpenalty]
    nlinarith
  have hstageLower :
      R - N * M < QuittingOneStagePayoff G beta p j := by
    change R < QuittingOneStagePayoff G beta p j -
        (5 * N * M / d) *
          ((p j : ℝ) / (1 - (p j : ℝ)) ^ Fintype.card G.Player) +
        M * ∑ k ∈ Finset.univ.erase j, (p k : ℝ) at hj
    simp only [hpjZero, sub_zero, one_pow, zero_div, mul_zero] at hj
    linarith [hsumM]
  have hrewardCeiling : M / 3 ≤ R - N * M := by
    nlinarith
  have hbetaLower : R - N * M < beta j := by
    by_contra hnot
    have hstageUpper := quittingOneStagePayoff_le_of_coordinate_le G beta p j
      (R - N * M) (fun A =>
        (le_abs_self (G.reward A j)).trans
          ((hM.2.1 A j).trans hrewardCeiling)) (le_of_not_gt hnot)
    linarith
  simpa only [N, beta, p] using ⟨hbetaLower, hpjZero⟩

/-- The strict estimate behind Lemma 3.4: `φ_j < -R` forces
`p_j > 1-ξ`. -/
private theorem lemma3_4_negative_coordinate_probability_gt_one_sub_xi
    (G : QuittingGame) (M d ρ ξ R : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (z : EZeroTilde G) (j : G.Player) (hj : Phi G M d z j < -R) :
    1 - ξ < (z.1.2 j : ℝ) := by
  classical
  let N : ℝ := Fintype.card G.Player
  let beta := z.1.1
  let p := z.1.2
  have hN : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hplayers
  have hNpos : 0 < N := by linarith
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM.1
  obtain ⟨hξ, hξOne, hR⟩ := section3Constants_radius_bound G M d ρ ξ R
    hplayers hM hd hd1 hmotion hconstants
  have hNM : 3 * M ≤ N * M :=
    mul_le_mul_of_nonneg_right hN hMpos.le
  have hpLarge : 1 - ξ < (p j : ℝ) := by
    by_contra hnot
    have hpUpper : (p j : ℝ) ≤ 1 - ξ := le_of_not_gt hnot
    have hcontinue : (p j : ℝ) < 1 := by linarith
    have hstageLower : -M / 3 ≤ QuittingOneStagePayoff G beta p j := by
      have hdeviation := quittingOneStagePayoff_deviation_le G beta p z.2.1 j 1
      rw [quittingOneStagePayoff_replace_affine] at hdeviation
      norm_num at hdeviation
      have hforced := abs_forcedQuitPayoff_le_scale G M hM p j
      linarith [neg_le_of_abs_le hforced]
    have hbase : ξ ≤ 1 - (p j : ℝ) := by linarith
    have hpowBase : ξ ^ Fintype.card G.Player ≤
        (1 - (p j : ℝ)) ^ Fintype.card G.Player :=
      pow_le_pow_left₀ hξ.le hbase _
    have hpowPos : 0 < ξ ^ Fintype.card G.Player := pow_pos hξ _
    have hdenomNonneg :
        0 ≤ (1 - (p j : ℝ)) ^ Fintype.card G.Player :=
      pow_nonneg (sub_nonneg.mpr (p j).property.2) _
    have hfraction :
        (p j : ℝ) / (1 - (p j : ℝ)) ^ Fintype.card G.Player ≤
          1 / ξ ^ Fintype.card G.Player := by
      calc
        (p j : ℝ) / (1 - (p j : ℝ)) ^ Fintype.card G.Player ≤
            1 / (1 - (p j : ℝ)) ^ Fintype.card G.Player :=
          div_le_div_of_nonneg_right (p j).property.2 hdenomNonneg
        _ ≤ 1 / ξ ^ Fintype.card G.Player :=
          one_div_le_one_div_of_le hpowPos hpowBase
    have hcoefficient : 0 ≤ 5 * N * M / d := by positivity
    have hpenalty : (5 * N * M / d) *
          ((p j : ℝ) / (1 - (p j : ℝ)) ^ Fintype.card G.Player) ≤
        R / 2 := by
      have hscaled := mul_le_mul_of_nonneg_left hfraction hcoefficient
      have hReq : R = 10 * N * M /
          (d * ξ ^ Fintype.card G.Player) := by
        simpa only [N] using hconstants.2.2.1
      calc
        _ ≤ (5 * N * M / d) * (1 / ξ ^ Fintype.card G.Player) := hscaled
        _ = R / 2 := by
          rw [hReq]
          field_simp
          ring
    have hsumNonneg :
        0 ≤ M * ∑ k ∈ Finset.univ.erase j, (p k : ℝ) := by
      exact mul_nonneg hMpos.le
        (Finset.sum_nonneg fun k _ => (p k).property.1)
    have hphiLower : -M / 3 - R / 2 ≤ Phi G M d z j := by
      change -M / 3 - R / 2 ≤ QuittingOneStagePayoff G beta p j -
          (5 * N * M / d) *
            ((p j : ℝ) / (1 - (p j : ℝ)) ^ Fintype.card G.Player) +
          M * ∑ k ∈ Finset.univ.erase j, (p k : ℝ)
      linarith
    have hstrict : -R < -M / 3 - R / 2 := by
      nlinarith
    linarith
  simpa only [p] using hpLarge

/-- The displayed weak probability estimate in Lemma 3.4(iii). -/
private theorem lemma3_4_negative_coordinate_probability
    (G : QuittingGame) (M d ρ ξ R : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (z : EZeroTilde G) (j : G.Player) (hj : Phi G M d z j < -R) :
    1 - (1 / 20 : ℝ) *
        (ρ / (2 * (Fintype.card G.Player : ℝ) * M)) ^
          Fintype.card G.Player ≤ (z.1.2 j : ℝ) := by
  have hstrict := lemma3_4_negative_coordinate_probability_gt_one_sub_xi
    G M d ρ ξ R hplayers hM hd hd1 hmotion hconstants z j hj
  have hxi := hconstants.2.1
  linarith

/-- The singular part of `φ` controls a coordinate by its own quitting
hazard, uniformly over the other coordinates. -/
private theorem phi_le_scale_sub_hazard_penalty
    (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (z : EZeroTilde G) (k : G.Player) (hpk : 0 < (z.1.2 k : ℝ)) :
    Phi G M d z k ≤
      M / 3 -
        5 * (Fintype.card G.Player : ℝ) * M * (z.1.2 k : ℝ) +
        (Fintype.card G.Player : ℝ) * M := by
  classical
  let N : ℝ := Fintype.card G.Player
  let beta := z.1.1
  let p := z.1.2
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hpkLt : (p k : ℝ) < 1 := by
    by_contra hnot
    have hpkOne : (p k : ℝ) = 1 :=
      le_antisymm (p k).property.2 (le_of_not_gt hnot)
    have hquit := z.2.2
    rw [quitProbability_eq_one_of_apply_eq_one G p k hpkOne] at hquit
    linarith
  have hdenPos : 0 < (1 - (p k : ℝ)) ^ Fintype.card G.Player :=
    pow_pos (by linarith) _
  have hdenOne : (1 - (p k : ℝ)) ^ Fintype.card G.Player ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr (p k).property.2) (by linarith)
  have hfraction : (p k : ℝ) ≤
      (p k : ℝ) / (1 - (p k : ℝ)) ^ Fintype.card G.Player := by
    rw [le_div_iff₀ hdenPos]
    nlinarith [mul_le_mul_of_nonneg_left hdenOne (p k).property.1]
  have hcoefficient : 5 * N * M ≤ 5 * N * M / d := by
    rw [le_div_iff₀ hd]
    exact mul_le_of_le_one_right (by positivity) hd1
  have hpenalty : 5 * N * M * (p k : ℝ) ≤
      (5 * N * M / d) *
        ((p k : ℝ) / (1 - (p k : ℝ)) ^ Fintype.card G.Player) := by
    calc
      5 * N * M * (p k : ℝ) ≤ (5 * N * M / d) * (p k : ℝ) :=
        mul_le_mul_of_nonneg_right hcoefficient (p k).property.1
      _ ≤ _ := mul_le_mul_of_nonneg_left hfraction (by positivity)
  have hstage := oneStagePayoff_eq_forcedQuit_of_positive G beta p
    z.2.1 z.2.2 k (by simpa only [p] using hpk)
  have hforced := abs_forcedQuitPayoff_le_scale G M hM p k
  have hsum : ∑ l ∈ Finset.univ.erase k, (p l : ℝ) ≤ N := by
    calc
      ∑ l ∈ Finset.univ.erase k, (p l : ℝ) ≤
          ∑ _l ∈ Finset.univ.erase k, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro l _
        exact (p l).property.2
      _ = ((Finset.univ.erase k).card : ℝ) := by simp
      _ ≤ N := by
        dsimp only [N]
        exact_mod_cast (Finset.card_erase_le :
          (Finset.univ.erase k).card ≤ (Finset.univ : Finset G.Player).card)
  change QuittingOneStagePayoff G beta p k -
      (5 * N * M / d) *
        ((p k : ℝ) / (1 - (p k : ℝ)) ^ Fintype.card G.Player) +
      M * ∑ l ∈ Finset.univ.erase k, (p l : ℝ) ≤ _
  rw [hstage]
  dsimp only [N, p]
  nlinarith [le_abs_self (ForcedQuitPayoff G z.1.2 k),
    mul_le_mul_of_nonneg_left hsum hMpos.le]

/-- A quitting probability above the Section 3 threshold forces the
corresponding `φ` coordinate below the negative continuation scale. -/
private theorem phi_lt_neg_card_mul_scale_of_high_probability
    (G : QuittingGame) (M d ρ : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (hmotion : IsStructureMotionParameter G M ρ)
    (z : EZeroTilde G) (k : G.Player)
    (hk : 1 - ρ / (2 * (Fintype.card G.Player : ℝ) * M) ≤
      (z.1.2 k : ℝ)) :
    Phi G M d z k < -(Fintype.card G.Player : ℝ) * M := by
  let N : ℝ := Fintype.card G.Player
  have hN : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hplayers
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hNM : 3 * M ≤ N * M :=
    mul_le_mul_of_nonneg_right hN hMpos.le
  have hpk : 0 < (z.1.2 k : ℝ) := by
    have hthreshold : 0 < 1 - ρ / (2 * N * M) := by
      have hfraction : ρ / (2 * N * M) ≤ 1 / 6 := by
        rw [div_le_iff₀ (by positivity : 0 < 2 * N * M)]
        nlinarith [hmotion.2.2.1, hNM, hM.1]
      linarith
    dsimp only [N] at hthreshold
    exact hthreshold.trans_le hk
  have hphi := phi_le_scale_sub_hazard_penalty G M d hM hd hd1 z k hpk
  have hpkLower : 1 - ρ / (2 * N * M) ≤ (z.1.2 k : ℝ) := by
    simpa only [N] using hk
  have hscaledPk : 5 * N * M - 5 * ρ / 2 ≤
      5 * N * M * (z.1.2 k : ℝ) := by
    have hscale := mul_le_mul_of_nonneg_left hpkLower
      (show 0 ≤ 5 * N * M by positivity)
    calc
      5 * N * M - 5 * ρ / 2 =
          5 * N * M * (1 - ρ / (2 * N * M)) := by field_simp
      _ ≤ 5 * N * M * (z.1.2 k : ℝ) := hscale
  dsimp only [N] at hNM hscaledPk
  nlinarith [hmotion.2.2.1, hM.1]

/-- In Case 2A, a near-certain quitter has a `\phi`-coordinate below her
min--max floor. -/
private theorem lemma3_4_high_probability_coordinate_lt_minMax_sub_half
    (G : QuittingGame) (M d ρ : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (hmotion : IsStructureMotionParameter G M ρ)
    (z : EZeroTilde G) (k : G.Player)
    (hk : 1 - ρ / (2 * (Fintype.card G.Player : ℝ) * M) ≤
      (z.1.2 k : ℝ)) :
    Phi G M d z k < MinMaxQuit G k - ρ / 2 := by
  classical
  let N : ℝ := Fintype.card G.Player
  let beta := z.1.1
  let p := z.1.2
  have hN : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hplayers
  have hNpos : 0 < N := by linarith
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM.1
  have hρpos : 0 < ρ := hmotion.2.1
  have hρ1 : ρ ≤ 1 := hmotion.2.2.1
  have hNM : 3 ≤ N * M := by
    nlinarith [mul_le_mul hN hM.1 (by norm_num) hNpos.le]
  have hthreshold : (5 : ℝ) / 6 ≤ 1 - ρ / (2 * N * M) := by
    have hfraction : ρ / (2 * N * M) ≤ 1 / 6 := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * N * M)]
      nlinarith
    nlinarith
  have hpk : 0 < (p k : ℝ) := by
    dsimp only [p]
    linarith
  have hchi := abs_minMaxQuit_le_of_reward_bound G k (by positivity)
    (fun outcome => hM.2.1 outcome k)
  have hphiUpper : Phi G M d z k ≤
      M / 3 - 5 * N * M * (p k : ℝ) + N * M := by
    simpa only [N, p] using
      phi_le_scale_sub_hazard_penalty G M d hM hd hd1 z k hpk
  have hpkLower : 1 - ρ / (2 * N * M) ≤ (p k : ℝ) := by
    simpa only [N, p] using hk
  have hscaledPk : 5 * N * M - 5 * ρ / 2 ≤
      5 * N * M * (p k : ℝ) := by
    have hscale := mul_le_mul_of_nonneg_left hpkLower
      (show 0 ≤ 5 * N * M by positivity)
    calc
      5 * N * M - 5 * ρ / 2 =
          5 * N * M * (1 - ρ / (2 * N * M)) := by field_simp
      _ ≤ 5 * N * M * (p k : ℝ) := hscale
  have hstrict :
      M / 3 - 5 * N * M * (p k : ℝ) + N * M <
        -M / 3 - ρ / 2 := by
    nlinarith
  exact lt_of_le_of_lt hphiUpper (hstrict.trans_le (by
    linarith [neg_le_of_abs_le hchi]))

/-- The singular penalty `u / (1-u)^N` is increasing before the endpoint. -/
private theorem singularQuitPenalty_mono {N : ℕ} {u v : UnitInterval}
    (huv : (u : ℝ) ≤ (v : ℝ)) (hv : (v : ℝ) < 1) :
    (u : ℝ) / (1 - (u : ℝ)) ^ N ≤
      (v : ℝ) / (1 - (v : ℝ)) ^ N := by
  have hu : (u : ℝ) < 1 := huv.trans_lt hv
  have hpowU : 0 < (1 - (u : ℝ)) ^ N := pow_pos (by linarith) _
  have hpowV : 0 < (1 - (v : ℝ)) ^ N := pow_pos (by linarith) _
  have hpow : (1 - (v : ℝ)) ^ N ≤ (1 - (u : ℝ)) ^ N := by
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  calc
    (u : ℝ) / (1 - (u : ℝ)) ^ N ≤
        (v : ℝ) / (1 - (u : ℝ)) ^ N :=
      div_le_div_of_nonneg_right huv hpowU.le
    _ ≤ (v : ℝ) / (1 - (v : ℝ)) ^ N :=
      div_le_div_of_nonneg_left v.property.1 hpowV hpow

/-- One player's quitting probability is at most the probability that someone quits. -/
private theorem quitProbability_apply_le (G : QuittingGame) (p : QuitRow G)
    (n : G.Player) : (p n : ℝ) ≤ QuitProbability G p := by
  classical
  rw [QuitProbability]
  have hprod := Finset.mul_prod_erase Finset.univ
    (fun k : G.Player => 1 - (p k : ℝ)) (Finset.mem_univ n)
  have hrestNonneg :
      0 ≤ ∏ k ∈ Finset.univ.erase n, (1 - (p k : ℝ)) :=
    Finset.prod_nonneg fun k _ => sub_nonneg.mpr (p k).property.2
  have hrestOne :
      (∏ k ∈ Finset.univ.erase n, (1 - (p k : ℝ))) ≤ 1 :=
    Finset.prod_le_one
      (fun k _ => sub_nonneg.mpr (p k).property.2)
      (fun k _ => by linarith [(p k).property.1])
  rw [← hprod]
  nlinarith [(p n).property.1, (p n).property.2]

/-- A finite quitting row has a coordinate of maximal quitting probability. -/
private theorem exists_maximalQuitter (G : QuittingGame) (p : QuitRow G) :
    ∃ m : G.Player, ∀ k, (p k : ℝ) ≤ (p m : ℝ) := by
  classical
  obtain ⟨m, _hm, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun k => (p k : ℝ)) Finset.univ_nonempty
  exact ⟨m, fun k => hmax k (Finset.mem_univ k)⟩

/-- At a maximal quitter, the `φ` coordinate is at most the coordinate of
any positive-probability quitter plus the two endpoint payoff bounds. -/
private theorem phi_maximalQuitter_le (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d)
    (z : EZeroTilde G) (j m : G.Player) (hj : 0 < (z.1.2 j : ℝ))
    (hm : ∀ k, (z.1.2 k : ℝ) ≤ (z.1.2 m : ℝ)) :
    Phi G M d z m ≤ Phi G M d z j + 2 * M / 3 := by
  classical
  let N : ℝ := Fintype.card G.Player
  let beta := z.1.1
  let p := z.1.2
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hpm : 0 < (p m : ℝ) := hj.trans_le (hm j)
  have hpmLt : (p m : ℝ) < 1 :=
    (quitProbability_apply_le G p m).trans_lt z.2.2
  have hpenalty := singularQuitPenalty_mono (N := Fintype.card G.Player)
    (hm j) hpmLt
  have hstageJ := oneStagePayoff_eq_forcedQuit_of_positive G beta p
    z.2.1 z.2.2 j hj
  have hstageM := oneStagePayoff_eq_forcedQuit_of_positive G beta p
    z.2.1 z.2.2 m hpm
  have hforcedJ := abs_forcedQuitPayoff_le_scale G M hM p j
  have hforcedM := abs_forcedQuitPayoff_le_scale G M hM p m
  have hsumJ :
      (∑ k ∈ Finset.univ.erase j, (p k : ℝ)) + (p j : ℝ) =
        ∑ k, (p k : ℝ) :=
    Finset.sum_erase_add Finset.univ (fun k => (p k : ℝ)) (Finset.mem_univ j)
  have hsumM :
      (∑ k ∈ Finset.univ.erase m, (p k : ℝ)) + (p m : ℝ) =
        ∑ k, (p k : ℝ) :=
    Finset.sum_erase_add Finset.univ (fun k => (p k : ℝ)) (Finset.mem_univ m)
  have hsum : ∑ k ∈ Finset.univ.erase m, (p k : ℝ) ≤
      ∑ k ∈ Finset.univ.erase j, (p k : ℝ) := by
    linarith [hm j]
  have hcoefficient : 0 ≤ 5 * N * M / d := by positivity
  change QuittingOneStagePayoff G beta p m -
      (5 * N * M / d) *
        ((p m : ℝ) / (1 - (p m : ℝ)) ^ Fintype.card G.Player) +
      M * ∑ k ∈ Finset.univ.erase m, (p k : ℝ) ≤
    QuittingOneStagePayoff G beta p j -
      (5 * N * M / d) *
        ((p j : ℝ) / (1 - (p j : ℝ)) ^ Fintype.card G.Player) +
      M * ∑ k ∈ Finset.univ.erase j, (p k : ℝ) + 2 * M / 3
  rw [hstageJ, hstageM]
  nlinarith [neg_le_of_abs_le hforcedJ, le_abs_self (ForcedQuitPayoff G p m),
    mul_le_mul_of_nonneg_left hpenalty hcoefficient,
    mul_le_mul_of_nonneg_left hsum hMpos.le]

private theorem othersQuitProbability_eq_replace_zero (G : QuittingGame)
    (p : QuitRow G) (n : G.Player) :
    OthersQuitProbability G p n = QuitProbability G (p.replace G n 0) := by
  classical
  rw [OthersQuitProbability, QuitProbability]
  simp only [QuitRow.replace]
  congr 1
  symm
  calc
    ∏ k, (1 - ((((if k = n then (0 : UnitInterval) else p k) :
          UnitInterval)) : ℝ)) =
        (1 - (((if n = n then (0 : UnitInterval) else p n) :
          UnitInterval) : ℝ)) *
          ∏ k ∈ Finset.univ.erase n,
            (1 - (((if k = n then (0 : UnitInterval) else p k) :
              UnitInterval) : ℝ)) :=
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n)).symm
    _ = ∏ k ∈ Finset.univ.erase n, (1 - (p k : ℝ)) := by
      simp only [if_pos, Set.Icc.coe_zero, sub_zero, one_mul]
      apply Finset.prod_congr rfl
      intro k hk
      simp [Finset.ne_of_mem_erase hk]

private theorem forcedContinue_sub_solo (G : QuittingGame) (p : QuitRow G)
    (beta : Payoff G.Player) (n : G.Player) :
    ForcedContinuePayoff G beta p n -
        ForcedContinuePayoff G (SoloPayoff G) p n =
      (1 - OthersQuitProbability G p n) *
        (beta n - SoloPayoff G n) := by
  rw [ForcedContinuePayoff, ForcedContinuePayoff,
    quittingOneStagePayoff_sub, othersQuitProbability_eq_replace_zero]

/-- With the solo vector as continuation, a forced-Continue payoff remains
inside the terminal payoff scale. -/
private theorem abs_forcedContinue_solo_le_scale
    (G : QuittingGame) (M : ℝ) (hM : IsSimonPayoffScale G M)
    (p : QuitRow G) (n : G.Player) :
    |ForcedContinuePayoff G (SoloPayoff G) p n| ≤ M / 3 := by
  classical
  rw [ForcedContinuePayoff, quittingOneStagePayoff_eq_rootExpectedPayoff]
  exact GameTheory.abs_quittingRootExpectedPayoff_le_bound G.reward
    (SoloPayoff G) (quitRowMarginals G (p.replace G n 0)) n hM.2.1
      (fun k => hM.2.1 ⟨{k}, Finset.singleton_nonempty k⟩ k)

/-- If `m` maximizes the quitting probability, the probability that every
player other than any specified owner continues is at least
`(1-p_m)^(|N|-1)`. -/
private theorem maximalQuitter_opponentSurvival_lower_at
    (G : QuittingGame) (p : QuitRow G) (m owner : G.Player)
    (hm : ∀ k, (p k : ℝ) ≤ (p m : ℝ)) :
    (1 - (p m : ℝ)) ^ (Fintype.card G.Player - 1) ≤
      1 - OthersQuitProbability G p owner := by
  classical
  rw [OthersQuitProbability, sub_sub_cancel]
  have hcard : (Finset.univ.erase owner).card = Fintype.card G.Player - 1 := by
    simp
  rw [← hcard, ← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro k _
    exact sub_nonneg.mpr (p m).property.2
  · intro k _
    linarith [hm k]

/-- The owner-maximal specialization of the preceding survival bound. -/
private theorem maximalQuitter_opponentSurvival_lower
    (G : QuittingGame) (p : QuitRow G) (m : G.Player)
    (hm : ∀ k, (p k : ℝ) ≤ (p m : ℝ)) :
    (1 - (p m : ℝ)) ^ (Fintype.card G.Player - 1) ≤
      1 - OthersQuitProbability G p m :=
  maximalQuitter_opponentSurvival_lower_at G p m m hm

/-- The supported maximal quitter's continuation coordinate is controlled
by the reciprocal probability that all other players continue. -/
private theorem beta_maximalQuitter_le (G : QuittingGame) (M : ℝ)
    (hM : IsSimonPayoffScale G M) (z : EZeroTilde G) (m : G.Player)
    (hpm : 0 < (z.1.2 m : ℝ))
    (hm : ∀ k, (z.1.2 k : ℝ) ≤ (z.1.2 m : ℝ)) :
    z.1.1 m ≤ M +
      M / (1 - (z.1.2 m : ℝ)) ^ (Fintype.card G.Player - 1) := by
  let beta := z.1.1
  let p := z.1.2
  let survival := 1 - OthersQuitProbability G p m
  let floor := (1 - (p m : ℝ)) ^ (Fintype.card G.Player - 1)
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hpmLt : (p m : ℝ) < 1 :=
    (quitProbability_apply_le G p m).trans_lt z.2.2
  have hfloorPos : 0 < floor := by
    dsimp only [floor]
    positivity
  have hsurvivalLower : floor ≤ survival := by
    simpa only [floor, survival, p] using
      maximalQuitter_opponentSurvival_lower G p m hm
  have hquit := z.2.1.1 m hpm
  have hcontinue := z.2.1.2 m hpmLt
  have heq : ForcedQuitPayoff G p m = ForcedContinuePayoff G beta p m :=
    le_antisymm (by simpa only [sub_zero] using hcontinue)
      (by simpa only [sub_zero] using hquit)
  have hidentity := forcedContinue_sub_solo G p beta m
  rw [← heq] at hidentity
  have hforced := abs_forcedQuitPayoff_le_scale G M hM p m
  have hsolo := abs_forcedContinue_solo_le_scale G M hM p m
  have hscaled : survival * (beta m - SoloPayoff G m) ≤ 2 * M / 3 := by
    rw [← hidentity]
    nlinarith [le_abs_self (ForcedQuitPayoff G p m),
      neg_le_of_abs_le hsolo]
  have hdiff : beta m - SoloPayoff G m ≤ (2 * M / 3) / floor := by
    by_cases hnonneg : 0 ≤ beta m - SoloPayoff G m
    · have hmul := mul_le_mul_of_nonneg_right hsurvivalLower hnonneg
      rw [le_div_iff₀ hfloorPos]
      simpa only [mul_comm] using hmul.trans hscaled
    · exact le_trans (le_of_not_ge hnonneg) (div_nonneg (by positivity) hfloorPos.le)
  have hsoloUpper : SoloPayoff G m ≤ M / 3 :=
    (le_abs_self (SoloPayoff G m)).trans
      (hM.2.1 ⟨{m}, Finset.singleton_nonempty m⟩ m)
  dsimp only [beta, p, floor] at hdiff ⊢
  have hinvNonneg : 0 ≤ M /
      (1 - (z.1.2 m : ℝ)) ^ (Fintype.card G.Player - 1) := by
    positivity
  have hfraction : (2 * M / 3) /
        (1 - (z.1.2 m : ℝ)) ^ (Fintype.card G.Player - 1) ≤
      M / (1 - (z.1.2 m : ℝ)) ^ (Fintype.card G.Player - 1) := by
    apply div_le_div_of_nonneg_right (by nlinarith)
    exact pow_nonneg (sub_nonneg.mpr (z.1.2 m).property.2) _
  linarith

/-- The Section 3 choice makes `|N| ξ` at most `1/40`. -/
private theorem card_mul_xi_le_one_fortieth
    (G : QuittingGame) (M d ρ ξ R : ℝ)
    (hM : IsSimonPayoffScale G M)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R) :
    (Fintype.card G.Player : ℝ) * ξ ≤ 1 / 40 := by
  let N : ℝ := Fintype.card G.Player
  let delta := ρ / (2 * N * M)
  have hNpos : 0 < N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    exact div_pos hmotion.2.1 (by positivity)
  have hdeltaOne : delta ≤ 1 := by
    dsimp only [delta]
    rw [div_le_one (by positivity : 0 < 2 * N * M)]
    have hNone : 1 ≤ N := by
      dsimp only [N]
      exact_mod_cast Fintype.card_pos
    have hNMraw : 1 * 1 ≤ N * M :=
      mul_le_mul hNone hM.1 (by norm_num) (by positivity)
    have hNM : 1 ≤ N * M := by simpa using hNMraw
    exact hmotion.2.2.1.trans (by nlinarith)
  have hpowLe : delta ^ Fintype.card G.Player ≤ delta := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card G.Player))
    rw [hk, pow_succ]
    exact mul_le_of_le_one_left hdeltaPos.le
      (pow_le_one₀ hdeltaPos.le hdeltaOne)
  have hxiDelta : ξ ≤ delta / 20 := by
    have hxi := hconstants.2.1
    change ξ ≤ (1 / 20 : ℝ) * delta ^ Fintype.card G.Player at hxi
    nlinarith
  have hNdelta : N * delta ≤ 1 / 2 := by
    have hρ := hmotion.2.2.1
    dsimp only [delta]
    rw [show N * (ρ / (2 * N * M)) = ρ / (2 * M) by field_simp]
    rw [div_le_iff₀ (by positivity : 0 < 2 * M)]
    nlinarith [hmotion.2.2.1, hM.1]
  dsimp only [N] at hNdelta ⊢
  have hscale := mul_le_mul_of_nonneg_left hxiDelta hNpos.le
  nlinarith

/-- At a supported maximal quitter, the displayed definition of `φ` gives
the paper's singular upper bound. -/
private theorem phi_maximalQuitter_upper (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (_hd : 0 < d)
    (z : EZeroTilde G) (m : G.Player) (hpm : 0 < (z.1.2 m : ℝ)) :
    Phi G M d z m ≤ M / 3 -
        (5 * (Fintype.card G.Player : ℝ) * M / d) *
          ((z.1.2 m : ℝ) /
            (1 - (z.1.2 m : ℝ)) ^ Fintype.card G.Player) +
      (Fintype.card G.Player : ℝ) * M := by
  classical
  let N : ℝ := Fintype.card G.Player
  let beta := z.1.1
  let p := z.1.2
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hstage := oneStagePayoff_eq_forcedQuit_of_positive G beta p
    z.2.1 z.2.2 m hpm
  have hforced := abs_forcedQuitPayoff_le_scale G M hM p m
  have hsum : ∑ k ∈ Finset.univ.erase m, (p k : ℝ) ≤ N := by
    calc
      ∑ k ∈ Finset.univ.erase m, (p k : ℝ) ≤
          ∑ _k ∈ Finset.univ.erase m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        exact (p k).property.2
      _ = ((Finset.univ.erase m).card : ℝ) := by simp
      _ ≤ N := by
        dsimp only [N]
        exact_mod_cast (Finset.card_erase_le :
          (Finset.univ.erase m).card ≤ (Finset.univ : Finset G.Player).card)
  change QuittingOneStagePayoff G beta p m -
      (5 * N * M / d) *
        ((p m : ℝ) / (1 - (p m : ℝ)) ^ Fintype.card G.Player) +
      M * ∑ k ∈ Finset.univ.erase m, (p k : ℝ) ≤ _
  rw [hstage]
  nlinarith [le_abs_self (ForcedQuitPayoff G p m),
    mul_le_mul_of_nonneg_left hsum hMpos.le]

/-- The maximal-quitter comparison in Case 2C forces the interpolation
coefficient below `d(1-p_m)/(3|N|)`. -/
private theorem interpolation_lt_maximalQuitter
    (G : QuittingGame) (M d ρ ξ R : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (z : EZeroTilde G) (j m : G.Player)
    (hm : ∀ k, (z.1.2 k : ℝ) ≤ (z.1.2 m : ℝ))
    (haj : Phi G M d z j < -R)
    (lambda : UnitInterval) (hlambda0 : 0 < (lambda : ℝ))
    (x : Payoff G.Player)
    (hx : x = (1 - (lambda : ℝ)) • z.1.1 +
      (lambda : ℝ) • Phi G M d z)
    (hxLower : -M ≤ x m) :
    (lambda : ℝ) < d * (1 - (z.1.2 m : ℝ)) /
      (3 * (Fintype.card G.Player : ℝ)) := by
  let N : ℝ := Fintype.card G.Player
  let p := z.1.2
  let tau : ℝ := 1 - (p m : ℝ)
  let survivalFloor : ℝ := tau ^ (Fintype.card G.Player - 1)
  have hN : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hplayers
  have hNpos : 0 < N := by linarith
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hxiPos : 0 < ξ := hconstants.1
  have hNxi := card_mul_xi_le_one_fortieth G M d ρ ξ R hM
    hmotion hconstants
  have hNxi' : N * ξ ≤ 1 / 40 := by simpa only [N] using hNxi
  have hxiSmall : ξ ≤ 1 / 120 := by
    nlinarith
  have hpj := lemma3_4_negative_coordinate_probability_gt_one_sub_xi
    G M d ρ ξ R hplayers hM hd hd1 hmotion hconstants z j haj
  have hpjPos : 0 < (p j : ℝ) := by linarith
  have hpmPos : 0 < (p m : ℝ) := hpjPos.trans_le (hm j)
  have hpmLt : (p m : ℝ) < 1 :=
    (quitProbability_apply_le G p m).trans_lt z.2.2
  have htauPos : 0 < tau := by dsimp only [tau]; linarith
  have htauXi : tau < ξ := by dsimp only [tau]; linarith [hm j]
  have htauOne : tau ≤ 1 := by
    dsimp only [tau]
    linarith [(p m).property.1]
  have hfloorPos : 0 < survivalFloor := pow_pos htauPos _
  have hfloorTau : survivalFloor ≤ tau := by
    have hNnat : 3 ≤ Fintype.card G.Player := hplayers
    have hpredPos : 0 < Fintype.card G.Player - 1 := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpredPos)
    dsimp only [survivalFloor]
    rw [hk, pow_succ]
    exact mul_le_of_le_one_left htauPos.le
      (pow_le_one₀ htauPos.le htauOne)
  have hbeta := beta_maximalQuitter_le G M hM z m hpmPos hm
  have halpha := phi_maximalQuitter_upper G M d hM hd z m hpmPos
  have hpow : tau ^ Fintype.card G.Player = tau * survivalFloor := by
    have hNnat : 3 ≤ Fintype.card G.Player := hplayers
    have hcard : Fintype.card G.Player - 1 + 1 = Fintype.card G.Player := by
      omega
    calc
      tau ^ Fintype.card G.Player =
          tau ^ (Fintype.card G.Player - 1 + 1) := by rw [hcard]
      _ = tau ^ (Fintype.card G.Player - 1) * tau := pow_succ _ _
      _ = tau * survivalFloor := by simp only [survivalFloor, mul_comm]
  by_contra hnot
  have hlambdaLower : d * tau / (3 * N) ≤ (lambda : ℝ) := by
    simpa only [tau, p, N] using le_of_not_gt hnot
  have hcoefficient : 0 < 5 * N * M / d := by positivity
  have hscaledLambda : 5 * M * tau / 3 ≤
      (lambda : ℝ) * (5 * N * M / d) := by
    have hscale := mul_le_mul_of_nonneg_right hlambdaLower hcoefficient.le
    calc
      5 * M * tau / 3 = d * tau / (3 * N) * (5 * N * M / d) := by
        field_simp
      _ ≤ _ := hscale
  have halphaScaled : tau * survivalFloor * Phi G M d z m ≤
      tau * survivalFloor * (M / 3 + N * M) -
        (5 * N * M / d) * (1 - tau) := by
    have halpha' : Phi G M d z m ≤ M / 3 -
        (5 * N * M / d) * ((1 - tau) / (tau * survivalFloor)) +
          N * M := by
      dsimp only [N, p, tau, survivalFloor] at hpow ⊢
      rw [← hpow]
      simpa only [sub_sub_cancel] using halpha
    have hscale := mul_le_mul_of_nonneg_left halpha'
      (mul_nonneg htauPos.le hfloorPos.le)
    calc
      tau * survivalFloor * Phi G M d z m ≤
          tau * survivalFloor *
            (M / 3 - (5 * N * M / d) *
              ((1 - tau) / (tau * survivalFloor)) + N * M) := hscale
      _ = tau * survivalFloor * (M / 3 + N * M) -
          (5 * N * M / d) * (1 - tau) := by
        field_simp [ne_of_gt htauPos, ne_of_gt hfloorPos]
        ring
  have hbetaScaled : tau * survivalFloor * z.1.1 m ≤
      tau * survivalFloor * M + tau * M := by
    have hbeta' : z.1.1 m ≤ M + M / survivalFloor := by
      simpa only [p, tau, survivalFloor] using hbeta
    have hscale := mul_le_mul_of_nonneg_left hbeta'
      (mul_nonneg htauPos.le hfloorPos.le)
    calc
      tau * survivalFloor * z.1.1 m ≤
          tau * survivalFloor * (M + M / survivalFloor) := hscale
      _ = tau * survivalFloor * M + tau * M := by
        field_simp [ne_of_gt hfloorPos]
  have hbetaPart := mul_le_mul_of_nonneg_left hbetaScaled
    (sub_nonneg.mpr lambda.property.2)
  have halphaPart := mul_le_mul_of_nonneg_left halphaScaled lambda.property.1
  have hpenaltyPart := mul_le_mul_of_nonneg_right hscaledLambda
    (sub_nonneg.mpr htauOne)
  have hscaledX : tau * survivalFloor * x m ≤
      tau * survivalFloor * M + tau * M +
        tau * survivalFloor * (M / 3 + N * M) -
          5 * M * tau / 3 * (1 - tau) := by
    have hxm := congrFun hx m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hxm
    rw [hxm]
    calc
      tau * survivalFloor *
          ((1 - (lambda : ℝ)) * z.1.1 m +
            (lambda : ℝ) * Phi G M d z m) =
          (1 - (lambda : ℝ)) * (tau * survivalFloor * z.1.1 m) +
            (lambda : ℝ) * (tau * survivalFloor * Phi G M d z m) := by ring
      _ ≤ (1 - (lambda : ℝ)) *
            (tau * survivalFloor * M + tau * M) +
          (lambda : ℝ) *
            (tau * survivalFloor * (M / 3 + N * M) -
              (5 * N * M / d) * (1 - tau)) :=
        add_le_add hbetaPart halphaPart
      _ ≤ (1 - (lambda : ℝ)) *
            (tau * survivalFloor * M + tau * M) +
          (lambda : ℝ) * (tau * survivalFloor * (M / 3 + N * M)) -
            5 * M * tau / 3 * (1 - tau) := by
        linarith
      _ ≤ tau * survivalFloor * M + tau * M +
          tau * survivalFloor * (M / 3 + N * M) -
            5 * M * tau / 3 * (1 - tau) := by
        have hfirstNonneg : 0 ≤ tau * survivalFloor * M + tau * M := by
          positivity
        have hsecondNonneg :
            0 ≤ tau * survivalFloor * (M / 3 + N * M) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right lambda.property.2 hfirstNonneg,
          mul_le_mul_of_nonneg_right lambda.property.2 hsecondNonneg]
  have hNt : N * tau < 1 / 40 :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_left htauXi hNpos) hNxi'
  have hNs : N * survivalFloor < 1 / 40 :=
    (mul_le_mul_of_nonneg_left hfloorTau hNpos.le).trans_lt hNt
  have htauSmall : tau < 1 / 120 := htauXi.trans_le hxiSmall
  have hfloorSmall : survivalFloor < 1 / 120 := hfloorTau.trans_lt htauSmall
  have hbracket : survivalFloor + 1 + survivalFloor / 3 +
      N * survivalFloor - 5 / 3 + 5 * tau / 3 < -survivalFloor := by
    linarith only [hNs, hfloorSmall, htauSmall]
  have hstrictScaled := mul_lt_mul_of_pos_left hbracket
    (mul_pos hMpos htauPos)
  have hupperStrict :
      tau * survivalFloor * M + tau * M +
          tau * survivalFloor * (M / 3 + N * M) -
            5 * M * tau / 3 * (1 - tau) <
        -M * tau * survivalFloor := by
    calc
      tau * survivalFloor * M + tau * M +
          tau * survivalFloor * (M / 3 + N * M) -
            5 * M * tau / 3 * (1 - tau) =
          (M * tau) * (survivalFloor + 1 + survivalFloor / 3 +
            N * survivalFloor - 5 / 3 + 5 * tau / 3) := by ring
      _ < (M * tau) * (-survivalFloor) := hstrictScaled
      _ = -M * tau * survivalFloor := by ring
  have hxStrict : tau * survivalFloor * x m <
      tau * survivalFloor * (-M) := by
    calc
      tau * survivalFloor * x m ≤
          tau * survivalFloor * M + tau * M +
            tau * survivalFloor * (M / 3 + N * M) -
              5 * M * tau / 3 * (1 - tau) := hscaledX
      _ < -M * tau * survivalFloor := hupperStrict
      _ = tau * survivalFloor * (-M) := by ring
  exact (not_lt_of_ge
    (mul_le_mul_of_nonneg_left hxLower
      (mul_nonneg htauPos.le hfloorPos.le))) hxStrict

/-- Below the threshold `1-δ`, the singular fraction in `φ` is at most
`δ^(-|N|)`. -/
private theorem quitPenalty_le_inv_pow (G : QuittingGame) (p : QuitRow G)
    (n : G.Player) {δ : ℝ} (hδ : 0 < δ)
    (hn : (p n : ℝ) ≤ 1 - δ) :
    (p n : ℝ) / (1 - (p n : ℝ)) ^ Fintype.card G.Player ≤
      1 / δ ^ Fintype.card G.Player := by
  have hbase : δ ≤ 1 - (p n : ℝ) := by linarith
  have hpowPos : 0 < δ ^ Fintype.card G.Player := pow_pos hδ _
  have hdenPos : 0 < (1 - (p n : ℝ)) ^ Fintype.card G.Player :=
    pow_pos (lt_of_lt_of_le hδ hbase) _
  have hpow := pow_le_pow_left₀ hδ.le hbase (Fintype.card G.Player)
  calc
    (p n : ℝ) / (1 - (p n : ℝ)) ^ Fintype.card G.Player ≤
        1 / (1 - (p n : ℝ)) ^ Fintype.card G.Player :=
      div_le_div_of_nonneg_right (p n).property.2 hdenPos.le
    _ ≤ 1 / δ ^ Fintype.card G.Player :=
      one_div_le_one_div_of_le hpowPos hpow

/-- If Continue is in support of an exact row, its one-stage value is at
least its forced-Quit payoff. -/
private theorem forcedQuit_le_oneStage_of_continue_support
    (G : QuittingGame) (beta : Payoff G.Player) (p : QuitRow G)
    (hp : p ∈ EpsilonRow G 0 beta) (n : G.Player)
    (hn : (p n : ℝ) < 1) :
    ForcedQuitPayoff G p n ≤ QuittingOneStagePayoff G beta p n := by
  have hcontinue := hp.2 n hn
  have haffine := quittingOneStagePayoff_replace_affine G beta p n (p n)
  rw [QuitRow.replace_self] at haffine
  have hp0 := (p n).property.1
  have hp1 := (p n).property.2
  nlinarith

/-- The low-probability large-continuation alternative contradicts the
target box.  This proves both the printed positive Case 2C and the negative
alternative omitted from the paper's displayed case split. -/
private theorem lowProbability_largeContinuation_not_box
    (G : QuittingGame) (M d ρ ξ R : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (z : EZeroTilde G) (j m l : G.Player)
    (hm : ∀ k, (z.1.2 k : ℝ) ≤ (z.1.2 m : ℝ))
    (haj : Phi G M d z j < -R)
    (hlow : (z.1.2 l : ℝ) ≤
      1 - ρ / (2 * (Fintype.card G.Player : ℝ) * M))
    (hlarge : (Fintype.card G.Player : ℝ) * M < |z.1.1 l|)
    (lambda : UnitInterval) (hlambda0 : 0 < (lambda : ℝ))
    (hlambda1 : (lambda : ℝ) < 1)
    (x : Payoff G.Player)
    (hx : x = (1 - (lambda : ℝ)) • z.1.1 +
      (lambda : ℝ) • Phi G M d z) :
    ¬InClosedPayoffBox M x := by
  intro hbox
  classical
  let N : ℝ := Fintype.card G.Player
  let p := z.1.2
  let delta : ℝ := ρ / (2 * N * M)
  let coefficient : ℝ := 5 * N * M / d
  let penalty : ℝ := (p l : ℝ) /
    (1 - (p l : ℝ)) ^ Fintype.card G.Player
  have hN : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hplayers
  have hNpos : 0 < N := by linarith
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    exact div_pos hmotion.2.1 (by positivity)
  have hdeltaPowPos : 0 < delta ^ Fintype.card G.Player :=
    pow_pos hdeltaPos _
  have hxiSmallRaw := card_mul_xi_le_one_fortieth G M d ρ ξ R hM
    hmotion hconstants
  have hxiSmall : ξ ≤ 1 / 120 := by
    have hNxi : N * ξ ≤ 1 / 40 := by simpa only [N] using hxiSmallRaw
    nlinarith
  have hpj := lemma3_4_negative_coordinate_probability_gt_one_sub_xi
    G M d ρ ξ R hplayers hM hd hd1 hmotion hconstants z j haj
  have hpmXi : 1 - (p m : ℝ) < ξ := by
    dsimp only [p]
    linarith [hm j]
  have hlambda := interpolation_lt_maximalQuitter G M d ρ ξ R hplayers
    hM hd hd1 hmotion hconstants z j m hm haj lambda hlambda0 x hx
      (hbox m).1
  have hlambdaXi : (lambda : ℝ) < d * ξ / (3 * N) := by
    have hscale := mul_lt_mul_of_pos_left hpmXi hd
    have hden : 0 < 3 * N := by positivity
    exact hlambda.trans (div_lt_div_of_pos_right hscale hden)
  have hdxi : d * ξ ≤ 1 / 120 := by
    have hxiPos := hconstants.1
    have := mul_le_mul_of_nonneg_right hd1 hxiPos.le
    nlinarith
  have hlambdaNM : (lambda : ℝ) * (N * M) < M / 360 := by
    have hscale := mul_lt_mul_of_pos_right hlambdaXi (mul_pos hNpos hMpos)
    calc
      (lambda : ℝ) * (N * M) <
          (d * ξ / (3 * N)) * (N * M) := hscale
      _ = d * ξ * M / 3 := by field_simp
      _ ≤ M / 360 := by
        have hmul := mul_le_mul_of_nonneg_right hdxi hMpos.le
        nlinarith
  have hpenalty := quitPenalty_le_inv_pow G p l hdeltaPos (by
    simpa only [delta, p, N] using hlow)
  have hcoefficientPos : 0 < coefficient := by
    dsimp only [coefficient]
    positivity
  have hpenaltyNonneg : 0 ≤ penalty := by
    dsimp only [penalty]
    exact div_nonneg (p l).property.1
      (pow_nonneg (sub_nonneg.mpr (p l).property.2) _)
  have hxiPower : ξ ≤ (1 / 20 : ℝ) *
      delta ^ Fintype.card G.Player := by
    simpa only [delta, N] using hconstants.2.1
  have hpenaltyCost : (lambda : ℝ) * coefficient * penalty ≤ M / 12 := by
    have hbound := mul_le_mul_of_nonneg_left hpenalty
      (mul_nonneg lambda.property.1 hcoefficientPos.le)
    have hfactorPos : 0 < coefficient /
        delta ^ Fintype.card G.Player := div_pos hcoefficientPos hdeltaPowPos
    have hlambdaBound := mul_le_mul_of_nonneg_right hlambdaXi.le hfactorPos.le
    have hcost : 5 * M * ξ /
        (3 * delta ^ Fintype.card G.Player) ≤ M / 12 := by
      rw [div_le_iff₀ (by positivity : 0 < 3 * delta ^ Fintype.card G.Player)]
      have hscale := mul_le_mul_of_nonneg_left hxiPower
        (show 0 ≤ 5 * M by positivity)
      nlinarith
    calc
      (lambda : ℝ) * coefficient * penalty ≤
          (lambda : ℝ) * coefficient *
            (1 / delta ^ Fintype.card G.Player) := by
        simpa only [mul_assoc] using hbound
      _ = (lambda : ℝ) *
          (coefficient / delta ^ Fintype.card G.Player) := by ring
      _ ≤ (d * ξ / (3 * N)) *
          (coefficient / delta ^ Fintype.card G.Player) := hlambdaBound
      _ = 5 * M * ξ / (3 * delta ^ Fintype.card G.Player) := by
        dsimp only [coefficient]
        field_simp
      _ ≤ M / 12 := hcost
  have hplLt : (p l : ℝ) < 1 := by
    dsimp only [delta] at hdeltaPos
    dsimp only [p, N] at hlow ⊢
    linarith
  have hstageLower : -M / 3 ≤ QuittingOneStagePayoff G z.1.1 p l := by
    have hquit := forcedQuit_le_oneStage_of_continue_support G z.1.1 p
      z.2.1 l hplLt
    have hforced := abs_forcedQuitPayoff_le_scale G M hM p l
    linarith [neg_le_of_abs_le hforced]
  have hsumNonneg : 0 ≤ M * ∑ k ∈ Finset.univ.erase l, (p k : ℝ) :=
    mul_nonneg hMpos.le (Finset.sum_nonneg fun k _ => (p k).property.1)
  have halphaLower : -M / 3 - coefficient * penalty ≤ Phi G M d z l := by
    change -M / 3 - coefficient * penalty ≤
      QuittingOneStagePayoff G z.1.1 p l - coefficient * penalty +
        M * ∑ k ∈ Finset.univ.erase l, (p k : ℝ)
    linarith
  have hlambdaM : (lambda : ℝ) * (M / 3) ≤ M / 3 :=
    mul_le_of_le_one_left (by positivity) lambda.property.2
  have hNMbound : 3 * M ≤ N * M :=
    mul_le_mul_of_nonneg_right hN hMpos.le
  rw [lt_abs] at hlarge
  rcases hlarge with hpositive | hnegative
  · have hbetaWeighted := mul_lt_mul_of_pos_left hpositive
      (sub_pos.mpr hlambda1)
    have halphaWeighted := mul_le_mul_of_nonneg_left halphaLower
      lambda.property.1
    have hxm := congrFun hx l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hxm
    have hbaseLarge : M < N * M - (lambda : ℝ) * (N * M) -
        (lambda : ℝ) * (M / 3) -
          (lambda : ℝ) * coefficient * penalty := by
      linarith only [hNMbound, hlambdaNM, hlambdaM, hpenaltyCost, hMpos]
    have hxLarge : M < x l := by
      rw [hxm]
      calc
        M < N * M - (lambda : ℝ) * (N * M) -
            (lambda : ℝ) * (M / 3) -
              (lambda : ℝ) * coefficient * penalty := hbaseLarge
        _ = (1 - (lambda : ℝ)) * (N * M) +
            (lambda : ℝ) * (-M / 3 - coefficient * penalty) := by ring
        _ < (1 - (lambda : ℝ)) * z.1.1 l +
            (lambda : ℝ) * Phi G M d z l :=
          add_lt_add_of_lt_of_le hbetaWeighted halphaWeighted
    exact (not_lt_of_ge (hbox l).2) hxLarge
  · have hstageUpper : QuittingOneStagePayoff G z.1.1 p l ≤ M / 3 := by
      apply quittingOneStagePayoff_le_of_coordinate_le G z.1.1 p l (M / 3)
      · intro A
        exact (le_abs_self (G.reward A l)).trans (hM.2.1 A l)
      · nlinarith
    have hsum : ∑ k ∈ Finset.univ.erase l, (p k : ℝ) ≤ N := by
      calc
        ∑ k ∈ Finset.univ.erase l, (p k : ℝ) ≤
            ∑ _k ∈ Finset.univ.erase l, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          exact (p k).property.2
        _ = ((Finset.univ.erase l).card : ℝ) := by simp
        _ ≤ N := by
          dsimp only [N]
          exact_mod_cast (Finset.card_erase_le :
            (Finset.univ.erase l).card ≤ (Finset.univ : Finset G.Player).card)
    have halphaUpper : Phi G M d z l ≤ M / 3 + N * M := by
      change QuittingOneStagePayoff G z.1.1 p l - coefficient * penalty +
          M * ∑ k ∈ Finset.univ.erase l, (p k : ℝ) ≤ M / 3 + N * M
      nlinarith [mul_nonneg hcoefficientPos.le hpenaltyNonneg,
        mul_le_mul_of_nonneg_left hsum hMpos.le]
    have hbetaWeighted := mul_lt_mul_of_pos_left hnegative
      (sub_pos.mpr hlambda1)
    have hbetaWeighted' :
        (1 - (lambda : ℝ)) * z.1.1 l <
          (1 - (lambda : ℝ)) * (-N * M) := by
      dsimp only [N] at hbetaWeighted ⊢
      nlinarith only [hbetaWeighted]
    have halphaWeighted := mul_le_mul_of_nonneg_left halphaUpper
      lambda.property.1
    have hxm := congrFun hx l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hxm
    have hbaseSmall : -N * M + 2 * ((lambda : ℝ) * (N * M)) +
        (lambda : ℝ) * (M / 3) < -M := by
      linarith only [hNMbound, hlambdaNM, hlambdaM, hMpos]
    have hxSmall : x l < -M := by
      rw [hxm]
      calc
        (1 - (lambda : ℝ)) * z.1.1 l +
            (lambda : ℝ) * Phi G M d z l <
          (1 - (lambda : ℝ)) * (-N * M) +
            (lambda : ℝ) * (M / 3 + N * M) :=
          add_lt_add_of_lt_of_le hbetaWeighted' halphaWeighted
        _ = -N * M + 2 * ((lambda : ℝ) * (N * M)) +
            (lambda : ℝ) * (M / 3) := by ring
        _ < -M := hbaseSmall
    exact (not_lt_of_ge (hbox l).1) hxSmall

/--
Lemma 3.4.  For `a = φ(β,p)` and a point strictly inside the segment from
`β` to `a`, a coordinate of `a` outside `[-R,R]` forces the segment point
outside the rational target box.  A large positive coordinate has `pⱼ = 0`
and a large continuation value; a large negative coordinate with
`βⱼ ≥ χⱼ-ρ` has `pⱼ` close to one.
-/
theorem lemma3_4 (G : QuittingGame) (M d ρ ξ R : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (_hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (_hinstant : ¬HasInstantApproximateEquilibria G)
    (_hnormal : ∀ n, IsNormalPlayer G n)
    (z : EZeroTilde G) (t : UnitInterval)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (a : Payoff G.Player) (ha : a = Phi G M d z)
    (x : Payoff G.Player)
    (hx : x = (1 - (t : ℝ)) • z.1.1 + (t : ℝ) • a) :
    ((∃ j, R < |a j|) → ¬StructureTargetBox G M ρ x) ∧
    (∀ j, R < a j →
      R - (Fintype.card G.Player : ℝ) * M < z.1.1 j ∧
        (z.1.2 j : ℝ) = 0) ∧
    ∀ j, a j < -R → MinMaxQuit G j - ρ ≤ z.1.1 j →
      1 - (1 / 20 : ℝ) *
        (ρ / (2 * (Fintype.card G.Player : ℝ) * M)) ^
          Fintype.card G.Player ≤ (z.1.2 j : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨j, hj⟩ htarget
    rw [lt_abs] at hj
    rcases hj with hjPositive | hjNegative
    · obtain ⟨hbeta, _hpZero⟩ :=
        lemma3_4_positive_coordinate G M d ρ ξ R hplayers hM hd hd1
          hmotion hconstants z j (by simpa only [ha] using hjPositive)
      obtain ⟨_, _, hR⟩ := section3Constants_radius_bound G M d ρ ξ R
        hplayers hM hd hd1 hmotion hconstants
      have hN : 3 ≤ (Fintype.card G.Player : ℝ) := by
        exact_mod_cast hplayers
      have hMpos : 0 < M := zero_lt_one.trans_le hM.1
      have hNM : 3 * M ≤ (Fintype.card G.Player : ℝ) * M :=
        mul_le_mul_of_nonneg_right hN hMpos.le
      have hlowerM :
          M < R - (Fintype.card G.Player : ℝ) * M := by
        nlinarith
      have hxj := congrFun hx j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hxj
      have htComplement : 0 < 1 - (t : ℝ) := by linarith
      have hbetaWeighted := mul_lt_mul_of_pos_left hbeta htComplement
      have haLower :
          R - (Fintype.card G.Player : ℝ) * M < a j := by
        have hNMnonneg : 0 ≤ (Fintype.card G.Player : ℝ) * M := by
          positivity
        linarith
      have haWeighted := mul_lt_mul_of_pos_left haLower ht0
      have hxUpper := (htarget j).2
      nlinarith
    · by_cases hcase2A : ∃ k,
          1 - ρ / (2 * (Fintype.card G.Player : ℝ) * M) ≤
              (z.1.2 k : ℝ) ∧
            z.1.1 k < MinMaxQuit G k - ρ / 2
      · obtain ⟨k, hpk, hbeta⟩ := hcase2A
        have hak := lemma3_4_high_probability_coordinate_lt_minMax_sub_half
          G M d ρ hplayers hM hd hd1 hmotion z k hpk
        have hak' : a k < MinMaxQuit G k - ρ / 2 := by
          rw [ha]
          exact hak
        have hxk := congrFun hx k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hxk
        have htargetLower := (htarget k).1
        nlinarith
      · let N : ℝ := Fintype.card G.Player
        let threshold : ℝ := 1 - ρ / (2 * N * M)
        by_cases hcase2B : ∀ l, (z.1.2 l : ℝ) ≤ threshold →
            |z.1.1 l| ≤ N * M
        · have hN : 3 ≤ N := by
            dsimp only [N]
            exact_mod_cast hplayers
          have hNpos : 0 < N := by linarith
          have hMpos : 0 < M := zero_lt_one.trans_le hM.1
          have hNM : 3 ≤ N * M := by
            nlinarith [mul_le_mul hN hM.1 (by norm_num) hNpos.le]
          have hρpos : 0 < ρ := hmotion.2.1
          have hρ1 : ρ ≤ 1 := hmotion.2.2.1
          have hchi : ∀ k, |MinMaxQuit G k| ≤ M / 3 := by
            intro k
            exact abs_minMaxQuit_le_of_reward_bound G k (by positivity)
              (fun outcome => hM.2.1 outcome k)
          have hhighLower : ∀ k, threshold ≤ (z.1.2 k : ℝ) →
              MinMaxQuit G k - ρ / 2 ≤ z.1.1 k := by
            intro k hk
            by_contra hnot
            apply hcase2A
            refine ⟨k, ?_, lt_of_not_ge hnot⟩
            simpa only [threshold, N] using hk
          have hbetaLower : ∀ k, -(N * M) ≤ z.1.1 k := by
            intro k
            by_cases hk : threshold ≤ (z.1.2 k : ℝ)
            · have hlower := hhighLower k hk
              have hchiLower := neg_le_of_abs_le (hchi k)
              nlinarith
            · exact neg_le_of_abs_le (hcase2B k (le_of_not_ge hk))
          have hdeltaPos : 0 < ρ / (2 * N * M) := by positivity
          have hdeltaOne : ρ / (2 * N * M) ≤ 1 := by
            rw [div_le_one (by positivity : 0 < 2 * N * M)]
            nlinarith
          have hpowLe :
              (ρ / (2 * N * M)) ^ Fintype.card G.Player ≤
                ρ / (2 * N * M) := by
            have hcardPos : 0 < Fintype.card G.Player := Fintype.card_pos
            obtain ⟨card, hcard⟩ :=
              Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcardPos)
            rw [hcard, pow_succ]
            exact mul_le_of_le_one_left hdeltaPos.le
              (pow_le_one₀ hdeltaPos.le hdeltaOne)
          have hxiDelta : ξ ≤ ρ / (2 * N * M) := by
            have hxi := hconstants.2.1
            have hpowNonneg : 0 ≤
                (ρ / (2 * N * M)) ^ Fintype.card G.Player := by positivity
            have hscaled : (1 / 20 : ℝ) *
                (ρ / (2 * N * M)) ^ Fintype.card G.Player ≤
                  (ρ / (2 * N * M)) ^ Fintype.card G.Player := by
              nlinarith
            change ξ ≤ (1 / 20 : ℝ) *
              (ρ / (2 * N * M)) ^ Fintype.card G.Player at hxi
            exact hxi.trans (hscaled.trans hpowLe)
          have hpjStrict :=
            lemma3_4_negative_coordinate_probability_gt_one_sub_xi
              G M d ρ ξ R hplayers hM hd hd1 hmotion hconstants z j
                (by rw [← ha]; linarith)
          have hpj : threshold ≤ (z.1.2 j : ℝ) := by
            dsimp only [threshold]
            linarith
          have hbetaj := hhighLower j hpj
          obtain ⟨r, p', hrational, hpjOne, hrow⟩ :=
            lemma3_3 G M ρ hM hplayers z.1.1 z.1.2 z.2 hρpos hρ1
              (by
                intro k
                simpa only [N, neg_mul] using hbetaLower k)
              j (by simpa only [threshold, N] using hpj) hbetaj
                (by
                  intro l hl
                  exact (le_abs_self _).trans
                    (hcase2B l (by simpa only [threshold, N] using hl)))
          exact hmotion.2.2.2.2 r p' j hrational hrow hpjOne
        · push Not at hcase2B
          obtain ⟨l, hlow, hlarge⟩ := hcase2B
          obtain ⟨m, hm⟩ := exists_maximalQuitter G z.1.2
          have haj : Phi G M d z j < -R := by
            rw [← ha]
            linarith
          have hnotTarget := lowProbability_largeContinuation_not_box
            G M d ρ ξ R hplayers hM hd hd1 hmotion hconstants z j m l hm haj
              (by simpa only [threshold, N] using hlow)
              (by simpa only [N] using hlarge) t ht0 ht1 x
              (by simpa only [ha] using hx)
          apply hnotTarget
          intro k
          have hchi := abs_minMaxQuit_le_of_reward_bound G k
            (by linarith [hM.1])
            (fun outcome => hM.2.1 outcome k)
          have hρM : ρ ≤ M := hmotion.2.2.1.trans hM.1
          have hkLower := (htarget k).1
          have hchiLower := neg_le_of_abs_le hchi
          have hM0 : 0 ≤ M := by linarith [hM.1]
          exact ⟨by linarith, (htarget k).2⟩
  · intro j hj
    exact lemma3_4_positive_coordinate G M d ρ ξ R hplayers hM hd hd1
      hmotion hconstants z j (by simpa only [ha] using hj)
  · intro j hj hbeta
    exact lemma3_4_negative_coordinate_probability G M d ρ ξ R
      hplayers hM hd hd1 hmotion hconstants z j
        (by simpa only [ha] using hj)

/-- The radius selected in Section 3 lies beyond every coordinate allowed by
the rational target box. -/
private theorem not_structureTargetBox_of_radius_lt_abs
    (G : QuittingGame) (M ρ R : ℝ)
    (hM : IsSimonPayoffScale G M)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hR : 10 * (Fintype.card G.Player : ℝ) * M ≤ R)
    (x : Payoff G.Player) (j : G.Player) (hj : R < |x j|) :
    ¬StructureTargetBox G M ρ x := by
  intro htarget
  have hcard : 1 ≤ (Fintype.card G.Player : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hRM : M < R := by nlinarith
  rw [lt_abs] at hj
  rcases hj with hj | hj
  · exact (not_lt_of_ge (htarget j).2) (hRM.trans hj)
  · have hchi := abs_minMaxQuit_le_of_reward_bound G j (by positivity)
      (fun outcome => hM.2.1 outcome j)
    have hchiLower := neg_le_of_abs_le hchi
    have hρM : ρ ≤ M := hmotion.2.2.1.trans hM.1
    have hlower := (htarget j).1
    nlinarith

/--
Theorem 3.1.  The paper works throughout Sections 2--5 under the standing
assumption `|N| ≥ 3`; it is made explicit here.  The proof uses the explicit
homeomorphism from Lemma 3.2, the pointwise motion estimate from Lemma 2.3,
the compactly chosen Section 3 constants, and Lemma 3.4 at infinity.
-/
theorem theorem3_1 (G : QuittingGame) (M : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M) : StructureTheoremConclusion G M := by
  classical
  obtain ⟨_hsurjective, ⟨inverse⟩⟩ :=
    lemma3_2 G M 1 hM zero_lt_one le_rfl
  have hbasic := structureHomotopy_basic G M 1 hM zero_lt_one le_rfl inverse
  refine ⟨structureHomotopy G inverse, hbasic.1, hbasic.2.1,
    hbasic.2.2.1, hbasic.2.2.2, ?_⟩
  intro hnormal hgenerated hinstant ρ hmotion
  constructor
  · rintro x ⟨p, hp, hpayoff⟩
    obtain ⟨κ, hκ, _hκ1, hκmotion⟩ :=
      lemma2_3 G M hM hnormal hgenerated hinstant x
    have hrow : p ∈ EpsilonRow G κ x := EpsilonRow.mono G hκ.le x hp
    have hbound := hκmotion p hrow
    have hdist : EuclideanDist x (QuittingOneStagePayoff G x p) = 0 := by
      rw [hpayoff]
      simp [EuclideanDist, EuclideanNorm]
    have hquit : QuitProbability G p = 0 := by
      have hqnonneg := (quitProbability_mem_Icc G p).1
      rw [hdist] at hbound
      nlinarith
    have hpzero : p = zeroQuitRow G := by
      funext j
      apply Subtype.ext
      have hj := quitProbability_apply_le G p j
      simp only [zeroQuitRow, Set.Icc.coe_zero]
      linarith [(p j).property.1]
    rw [hpzero] at hp
    have hxGraph : (x, zeroQuitRow G) ∈ EZeroTilde G := by
      refine ⟨hp, ?_⟩
      simp [QuitProbability, zeroQuitRow]
    have hxSolo : ∀ j, SoloPayoff G j ≤ x j :=
      ((lemma3_1 G M 1 hM zero_lt_one le_rfl).2.1 x).1 hxGraph
    exact mem_closure_compl_WSet_of_soloPayoff_le G hxSolo
  · obtain ⟨ξ, R, hconstants⟩ :=
      exists_section3Constants G M 1 ρ hM zero_lt_one hmotion
    obtain ⟨_hξ, _hξ1, hR⟩ :=
      section3Constants_radius_bound G M 1 ρ ξ R hplayers hM
        zero_lt_one le_rfl hmotion hconstants
    have hRpos : 0 < R := by
      have hcard : 1 ≤ (Fintype.card G.Player : ℝ) := by
        exact_mod_cast Fintype.card_pos
      have hMpos : 0 < M := zero_lt_one.trans_le hM.1
      nlinarith
    refine ⟨R, hRpos, ?_⟩
    intro a haOutside t htarget
    have haLarge : ∃ j, R < |a j| := by
      by_contra hnot
      apply haOutside
      intro j
      exact abs_le.mp (le_of_not_gt (fun hj => hnot ⟨j, hj⟩))
    let z : EZeroTilde G := inverse.inv a
    have haPhi : Phi G M 1 z = a := inverse.rightInverse a
    by_cases ht0 : (t : ℝ) = 0
    · have hzero : t = 0 := Subtype.ext ht0
      subst t
      obtain ⟨j, hj⟩ := haLarge
      have htargetA : StructureTargetBox G M ρ a := by simpa using htarget
      exact not_structureTargetBox_of_radius_lt_abs
        G M ρ R hM hmotion hR a j hj htargetA
    by_cases ht1 : (t : ℝ) = 1
    · have hone : t = 1 := Subtype.ext ht1
      subst t
      have htargetBeta : StructureTargetBox G M ρ z.1.1 := by
        simpa using htarget
      obtain ⟨j, hj⟩ := haLarge
      rw [lt_abs] at hj
      rcases hj with hjPositive | hjNegative
      · obtain ⟨hbeta, _hpzero⟩ :=
          lemma3_4_positive_coordinate G M 1 ρ ξ R hplayers hM
            zero_lt_one le_rfl hmotion hconstants z j
              (by rw [haPhi]; exact hjPositive)
        have hcard : 1 ≤ (Fintype.card G.Player : ℝ) := by
          exact_mod_cast Fintype.card_pos
        have hMpos : 0 < M := zero_lt_one.trans_le hM.1
        have := (htargetBeta j).2
        nlinarith
      · by_cases hbeta : z.1.1 j < MinMaxQuit G j - ρ
        · have := (htargetBeta j).1
          linarith [hmotion.2.1]
        · have hpStrict :=
            lemma3_4_negative_coordinate_probability_gt_one_sub_xi
              G M 1 ρ ξ R hplayers hM zero_lt_one le_rfl hmotion
                hconstants z j (by rw [haPhi]; linarith)
          have hbetaBounds : ∀ k,
              MinMaxQuit G k - ρ ≤ z.1.1 k ∧
                z.1.1 k ≤ 2 * (Fintype.card G.Player : ℝ) * M := by
            intro k
            have hcard : 1 ≤ (Fintype.card G.Player : ℝ) := by
              exact_mod_cast Fintype.card_pos
            exact ⟨by linarith [(htargetBeta k).1, hmotion.2.1],
              by nlinarith [(htargetBeta k).2, hM.1]⟩
          have hpUpper := hconstants.2.2.2 z.1.1 z.1.2 z.2 hbetaBounds j
          linarith
    · let s : UnitInterval := ⟨1 - (t : ℝ), by
          constructor <;> linarith [t.property.1, t.property.2]⟩
      have htpos : 0 < (t : ℝ) :=
        lt_of_le_of_ne t.property.1 (Ne.symm ht0)
      have htlt : (t : ℝ) < 1 :=
        lt_of_le_of_ne t.property.2 ht1
      have hs0 : 0 < (s : ℝ) := by
        dsimp only [s]
        linarith
      have hs1 : (s : ℝ) < 1 := by
        dsimp only [s]
        linarith
      have hsegment : (structureHomotopy G inverse a t).1 =
          (1 - (s : ℝ)) • z.1.1 + (s : ℝ) • a := by
        funext j
        simp only [structureHomotopy, z, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        dsimp only [s]
        ring
      have hescape := (lemma3_4 G M 1 ρ ξ R hplayers hM zero_lt_one
        le_rfl hmotion hconstants hgenerated hinstant hnormal z s hs0 hs1
          a haPhi.symm (structureHomotopy G inverse a t).1 hsegment).1 haLarge
      exact hescape htarget

private theorem endpointDifference_eq_forced (G : QuittingGame)
    [DecidableEq G.Player] (r : Payoff G.Player)
    (p : QuitRow G) (n : G.Player) :
    GameTheory.quittingRootEndpointDifference G.reward r
        (quitRowMarginals G p) n =
      ForcedQuitPayoff G p n - ForcedContinuePayoff G r p n := by
  classical
  rw [GameTheory.quittingRootEndpointDifference]
  rw [GameTheory.quittingRootQuitPayoff_continuation_invariant
    G.reward r 0 (quitRowMarginals G p) n]
  unfold GameTheory.quittingRootQuitPayoff GameTheory.quittingRootContinuePayoff
  rw [ForcedQuitPayoff, ForcedContinuePayoff,
    quittingOneStagePayoff_eq_rootExpectedPayoff,
    quittingOneStagePayoff_eq_rootExpectedPayoff,
    quitRowMarginals_replace_one, quitRowMarginals_replace_zero]

private theorem othersQuitProbability_le (G : QuittingGame) (p : QuitRow G)
    (n : G.Player) : OthersQuitProbability G p n ≤ QuitProbability G p := by
  rw [othersQuitProbability_eq_replace_zero]
  exact quitProbability_replace_zero_le G p n

/-- At the solo continuation coordinate, the pure-action endpoint gap is
carried only by nonempty opponent coalitions. -/
private theorem abs_endpointDifference_solo_le (G : QuittingGame)
    [DecidableEq G.Player] (M : ℝ)
    (hM : IsSimonPayoffScale G M) (p : QuitRow G) (n : G.Player) :
    |GameTheory.quittingRootEndpointDifference G.reward (SoloPayoff G)
        (quitRowMarginals G p) n| ≤
      M / 3 * OthersQuitProbability G p n := by
  classical
  rw [GameTheory.quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  let carrier := (Finset.univ.erase n).powerset
  let mass := fun A : Finset G.Player =>
    GameTheory.quittingOpponentCoalitionMass (quitRowMarginals G p) n A
  let toggle := fun A : Finset G.Player =>
    GameTheory.quittingEndpointInsertionToggle G.reward (SoloPayoff G) n A
  have hempty : (∅ : Finset G.Player) ∈ carrier := by simp [carrier]
  have hsum : ∑ A ∈ carrier, mass A = 1 := by
    dsimp only [carrier, mass]
    simp only [GameTheory.quittingOpponentCoalitionMass,
      quitRowMarginals_true_toReal, quitRowMarginals_false_toReal]
    rw [← Finset.prod_add (fun k => (p k : ℝ))
      (fun k => 1 - (p k : ℝ)) (Finset.univ.erase n)]
    simp
  have hsumNonempty : ∑ A ∈ carrier.erase ∅, mass A =
      OthersQuitProbability G p n := by
    have hsplit := Finset.sum_erase_add carrier mass hempty
    have hemptyMass : mass ∅ =
        ∏ k ∈ Finset.univ.erase n, (1 - (p k : ℝ)) := by
      simp [mass, GameTheory.quittingOpponentCoalitionMass]
    rw [hemptyMass, hsum] at hsplit
    have hcalc : ∑ A ∈ carrier.erase ∅, mass A =
        1 - ∏ k ∈ Finset.univ.erase n, (1 - (p k : ℝ)) := by
      linarith
    rw [OthersQuitProbability]
    convert hcalc using 1
    congr 1
    apply Finset.prod_congr
    · ext k
      simp
    · intro k _hk
      rfl
  have htoggleEmpty : toggle ∅ = 0 := by
    simp [toggle, GameTheory.quittingEndpointInsertionToggle,
      GameTheory.quittingStageCoalitionPayoff, SoloPayoff]
  rw [show (∑ A ∈ carrier, mass A * toggle A) =
      ∑ A ∈ carrier.erase ∅, mass A * toggle A by
    have hsplit := Finset.sum_erase_add carrier
      (fun A => mass A * toggle A) hempty
    rw [htoggleEmpty, mul_zero, add_zero] at hsplit
    exact hsplit.symm]
  calc
    |∑ A ∈ carrier.erase ∅, mass A * toggle A| ≤
        ∑ A ∈ carrier.erase ∅, |mass A * toggle A| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A ∈ carrier.erase ∅, mass A * (M / 3) := by
      apply Finset.sum_le_sum
      intro A hA
      have hnonempty : A.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hA).1
      have htoggle : |toggle A| ≤ M / 3 := by
        dsimp only [toggle]
        rw [GameTheory.quittingEndpointInsertionToggle_of_nonempty
          _ _ _ _ hnonempty]
        have hraw := hM.2.2
          ⟨insert n A, Finset.insert_nonempty n A⟩ ⟨A, hnonempty⟩ n
        nlinarith
      rw [abs_mul, abs_of_nonneg
        (GameTheory.quittingOpponentCoalitionMass_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_left htoggle
        (GameTheory.quittingOpponentCoalitionMass_nonneg _ _ _)
    _ = M / 3 * OthersQuitProbability G p n := by
      rw [← Finset.sum_mul, hsumNonempty]
      ring

/-- Exact endpoint equilibrium bounds every continuation coordinate below,
and coordinates in positive Quit support on both sides. -/
private theorem beta_coordinate_bounds (G : QuittingGame) (M : ℝ)
    (hM : IsSimonPayoffScale G M) (beta : Payoff G.Player)
    (p : QuitRow G) (hp : p ∈ EpsilonRow G 0 beta)
    (hqsmall : QuitProbability G p < 1) (n : G.Player) :
    let error := (M / 3 * QuitProbability G p) /
      (1 - QuitProbability G p)
    SoloPayoff G n - error ≤ beta n ∧
      (0 < (p n : ℝ) → |beta n - SoloPayoff G n| ≤ error) := by
  classical
  let q := QuitProbability G p
  let qn := OthersQuitProbability G p n
  let error := (M / 3 * q) / (1 - q)
  have hM0 : 0 ≤ M / 3 := by linarith [hM.1]
  have hqnq : qn ≤ q := othersQuitProbability_le G p n
  have hsurvival : 0 < 1 - q := by dsimp only [q]; linarith
  have hpnLt : (p n : ℝ) < 1 :=
    (quitProbability_apply_le G p n).trans_lt hqsmall
  have hcontinue : ForcedQuitPayoff G p n ≤
      ForcedContinuePayoff G beta p n := by
    simpa only [sub_zero] using hp.2 n hpnLt
  have hgap := abs_endpointDifference_solo_le G M hM p n
  rw [endpointDifference_eq_forced] at hgap
  have hcont := forcedContinue_sub_solo G p beta n
  have hlowerScaledOther :
      -(M / 3 * q) ≤ (1 - qn) * (beta n - SoloPayoff G n) := by
    have hgapLower := neg_le_of_abs_le hgap
    have hscale : M / 3 * qn ≤ M / 3 * q :=
      mul_le_mul_of_nonneg_left hqnq hM0
    rw [← hcont]
    linarith
  have hlowerScaled :
      -(M / 3 * q) ≤ (1 - q) * (beta n - SoloPayoff G n) := by
    by_cases hx : 0 ≤ beta n - SoloPayoff G n
    · exact le_trans (neg_nonpos.mpr (mul_nonneg hM0 (by
        dsimp only [q]
        exact (quitProbability_mem_Icc G p).1)))
        (mul_nonneg hsurvival.le hx)
    · have hxneg : beta n - SoloPayoff G n < 0 := lt_of_not_ge hx
      have hfactor : 1 - q ≤ 1 - qn := by linarith
      have hmul := mul_le_mul_of_nonpos_right hfactor hxneg.le
      exact hlowerScaledOther.trans hmul
  have hlower : SoloPayoff G n - error ≤ beta n := by
    have hdiff : SoloPayoff G n - beta n ≤ M / 3 * q / (1 - q) := by
      rw [le_div_iff₀ hsurvival]
      nlinarith
    dsimp only [error]
    linarith
  refine ⟨hlower, ?_⟩
  intro hpn
  have hquit : ForcedContinuePayoff G beta p n ≤
      ForcedQuitPayoff G p n := by
    simpa only [sub_zero] using hp.1 n hpn
  have heq : ForcedQuitPayoff G p n = ForcedContinuePayoff G beta p n :=
    le_antisymm hcontinue hquit
  have habsScaledOther :
      |(1 - qn) * (beta n - SoloPayoff G n)| ≤ M / 3 * q := by
    rw [← hcont, ← heq]
    exact hgap.trans (mul_le_mul_of_nonneg_left hqnq hM0)
  have hqnSurvival : 0 ≤ 1 - qn := by
    have hqnOne : qn ≤ 1 := hqnq.trans (quitProbability_mem_Icc G p).2
    linarith
  have habsScaled :
      (1 - q) * |beta n - SoloPayoff G n| ≤ M / 3 * q := by
    have hfactor : 1 - q ≤ 1 - qn := by linarith
    have hmul := mul_le_mul_of_nonneg_right hfactor
      (abs_nonneg (beta n - SoloPayoff G n))
    rw [abs_mul, abs_of_nonneg hqnSurvival] at habsScaledOther
    exact hmul.trans habsScaledOther
  rw [le_div_iff₀ hsurvival]
  simpa only [q, mul_comm] using habsScaled

/-- An explicit point of a set bounds the Euclidean infimum distance. -/
private theorem euclideanInfDist_le_dist_of_mem {N : Type} [Fintype N]
    (x y : Payoff N) {S : Set (Payoff N)} (hy : y ∈ S) :
    EuclideanInfDist x S ≤ EuclideanDist x y := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro value ⟨z, _hz, rfl⟩
    exact Real.sqrt_nonneg _
  · exact ⟨y, hy, rfl⟩

/-- Euclidean distance is bounded by the coordinatewise `l¹` distance. -/
private theorem euclideanDist_le_sum_abs {N : Type} [Fintype N]
    (x y : Payoff N) :
    EuclideanDist x y ≤ ∑ i, |x i - y i| := by
  rw [EuclideanDist, EuclideanNorm]
  rw [← sq_le_sq₀ (Real.sqrt_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
  rw [Real.sq_sqrt]
  · simpa only [Pi.sub_apply, sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun i => |x i - y i|) fun _ _ => abs_nonneg _)
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private def lowerFaceProjection (G : QuittingGame) (j : G.Player)
    (x : Payoff G.Player) : Payoff G.Player := by
  classical
  exact fun k => if k = j then SoloPayoff G k else max (x k) (SoloPayoff G k)

/-- Raising every coordinate to its solo floor and pinning coordinate `j`
produces a point on the face `W_j ∩ ∂W`. -/
private theorem lowerFaceProjection_mem (G : QuittingGame) (j : G.Player)
    (x : Payoff G.Player) :
    lowerFaceProjection G j x ∈ Wj G j ∩ frontier (WSet G) := by
  classical
  have hall : ∀ k, SoloPayoff G k ≤ lowerFaceProjection G j x k := by
    intro k
    by_cases hkj : k = j <;> simp [lowerFaceProjection, hkj]
  constructor
  · simp [Wj, lowerFaceProjection]
  · rw [frontier_eq_closure_inter_closure]
    constructor
    · apply subset_closure
      exact ⟨j, (by simp [lowerFaceProjection])⟩
    · let y : ℕ → Payoff G.Player := fun m n =>
        lowerFaceProjection G j x n + 1 / ((m : ℝ) + 1)
      apply mem_closure_of_tendsto (b := atTop) (f := y)
      · apply tendsto_pi_nhds.mpr
        intro n
        have ht : Tendsto
            (fun m : ℕ => lowerFaceProjection G j x n + 1 / ((m : ℝ) + 1))
            atTop (nhds (lowerFaceProjection G j x n + 0)) :=
          tendsto_const_nhds.add
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa only [y, add_zero] using ht
      · exact Eventually.of_forall fun m => by
          rw [Set.mem_compl_iff]
          intro hm
          rcases hm with ⟨n, hn⟩
          have hpositive : 0 < 1 / ((m : ℝ) + 1) := by positivity
          dsimp only [y] at hn
          linarith [hall n]

private theorem euclideanNorm_le_sqrt_card_mul {N : Type} [Fintype N]
    (x : Payoff N) {c : ℝ} (hc : 0 ≤ c) (hx : ∀ i, |x i| ≤ c) :
    EuclideanNorm x ≤ Real.sqrt (Fintype.card N) * c := by
  classical
  rw [EuclideanNorm]
  have hsum : ∑ i, (x i) ^ 2 ≤ (Fintype.card N : ℝ) * c ^ 2 := by
    calc
      ∑ i, (x i) ^ 2 ≤ ∑ _i : N, c ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (x i)) hc).mpr (hx i)
      _ = (Fintype.card N : ℝ) * c ^ 2 := by simp
  calc
    Real.sqrt (∑ i, (x i) ^ 2) ≤
        Real.sqrt ((Fintype.card N : ℝ) * c ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Fintype.card N) * c := by
      rw [Real.sqrt_mul (Nat.cast_nonneg (Fintype.card N))]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

private theorem beta_eq_solo_of_unique (G : QuittingGame) (M : ℝ)
    (hM : IsSimonPayoffScale G M) (beta : Payoff G.Player)
    (p : QuitRow G) (hp : p ∈ EpsilonRow G 0 beta)
    (hqsmall : QuitProbability G p < 1) (j : G.Player)
    (hj : 0 < (p j : ℝ)) (hcard : Fintype.card G.Player = 1) :
    beta = SoloPayoff G := by
  classical
  funext k
  obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.mp hcard
  have hkj : k = j := (hu k).trans (hu j).symm
  subst k
  have hpnLt : (p j : ℝ) < 1 :=
    (quitProbability_apply_le G p j).trans_lt hqsmall
  have heq : ForcedQuitPayoff G p j = ForcedContinuePayoff G beta p j :=
    le_antisymm (by simpa only [sub_zero] using hp.2 j hpnLt)
      (by simpa only [sub_zero] using hp.1 j hj)
  have hothers : OthersQuitProbability G p j = 0 := by
    rw [OthersQuitProbability]
    have herase : (Finset.univ : Finset G.Player).erase j = ∅ := by
      ext k
      obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.mp hcard
      have hkj : k = j := (hu k).trans (hu j).symm
      simp [hkj]
    rw [herase]
    simp
  have hgap := abs_endpointDifference_solo_le G M hM p j
  rw [endpointDifference_eq_forced, hothers, mul_zero, abs_nonpos_iff] at hgap
  have hcont := forcedContinue_sub_solo G p beta j
  rw [hothers, sub_zero, one_mul, ← heq] at hcont
  linarith

private theorem beta_infDist_bound (G : QuittingGame) (M : ℝ)
    (hM : IsSimonPayoffScale G M) (beta : Payoff G.Player)
    (p : QuitRow G) (hp : p ∈ EpsilonRow G 0 beta)
    (hqpos : 0 < QuitProbability G p)
    (hqsmall : QuitProbability G p <
      1 / (2 * (Fintype.card G.Player : ℝ)))
    (j : G.Player) (hj : 0 < (p j : ℝ)) :
    EuclideanInfDist beta (Wj G j ∩ frontier (WSet G)) ≤
      QuitProbability G p * (Fintype.card G.Player : ℝ) * M / 3 := by
  classical
  let N : ℝ := Fintype.card G.Player
  let q := QuitProbability G p
  have hNpos : 0 < N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos
  have hNone : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos
  have hqOne : q < 1 := by
    have hhalf : 1 / (2 * N) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    exact hqsmall.trans_le hhalf
  by_cases hcard : Fintype.card G.Player = 1
  · have hbeta := beta_eq_solo_of_unique G M hM beta p hp hqOne j hj hcard
    subst beta
    have hmem : SoloPayoff G ∈ Wj G j ∩ frontier (WSet G) := by
      have hproj : lowerFaceProjection G j (SoloPayoff G) = SoloPayoff G := by
        funext k
        by_cases hkj : k = j <;> simp [lowerFaceProjection, hkj]
      rw [← hproj]
      exact lowerFaceProjection_mem G j (SoloPayoff G)
    refine (euclideanInfDist_le_dist_of_mem _ _ hmem).trans ?_
    have hright : 0 ≤ q * N * M / 3 := by
      exact div_nonneg (mul_nonneg (mul_nonneg hqpos.le hNpos.le)
        (by linarith [hM.1])) (by norm_num)
    simpa [EuclideanDist, EuclideanNorm] using hright
  · have hNnat : 0 < Fintype.card G.Player := Fintype.card_pos
    have hNtwoNat : 2 ≤ Fintype.card G.Player := by omega
    have hNtwo : (2 : ℝ) ≤ N := by
      change (2 : ℝ) ≤ (Fintype.card G.Player : ℝ)
      exact_mod_cast hNtwoNat
    let error := (M / 3 * q) / (1 - q)
    let w := lowerFaceProjection G j beta
    have herrorNonneg : 0 ≤ error := by
      dsimp only [error]
      exact div_nonneg (mul_nonneg (by linarith [hM.1]) hqpos.le)
        (by linarith)
    have hcoord : ∀ k, |(beta - w) k| ≤ error := by
      intro k
      have hk := beta_coordinate_bounds G M hM beta p hp hqOne k
      by_cases hkj : k = j
      · subst k
        simpa only [Pi.sub_apply, w, lowerFaceProjection, if_pos] using hk.2 hj
      · rw [Pi.sub_apply]
        simp only [w, lowerFaceProjection, hkj, if_false]
        rw [abs_sub_comm]
        by_cases hle : SoloPayoff G k ≤ beta k
        · rw [max_eq_left hle, sub_self, abs_zero]
          exact herrorNonneg
        · rw [max_eq_right (le_of_not_ge hle),
            abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hle))]
          linarith [hk.1]
    have hsqrtSq : (Real.sqrt N) ^ 2 = N := by
      rw [Real.sq_sqrt hNpos.le]
    have hsqrtBound : Real.sqrt N ≤ N * (1 - q) := by
      have hqBound : N * q < 1 / 2 := by
        rw [lt_div_iff₀ (by positivity)] at hqsmall
        nlinarith
      have hright : 0 ≤ N * (1 - q) := by positivity
      rw [← sq_le_sq₀ (Real.sqrt_nonneg N) hright, hsqrtSq]
      nlinarith
    have hnorm : EuclideanDist beta w ≤ Real.sqrt N * error := by
      exact euclideanNorm_le_sqrt_card_mul (beta - w) herrorNonneg hcoord
    have hnumeric : Real.sqrt N * error ≤ q * N * M / 3 := by
      have hsurvival : 0 < 1 - q := by linarith
      have hqM : 0 ≤ q * (M / 3) :=
        mul_nonneg hqpos.le (by linarith [hM.1])
      calc
        Real.sqrt N * error =
            (Real.sqrt N * (q * (M / 3))) / (1 - q) := by
          dsimp only [error]
          ring
        _ ≤ (N * (1 - q) * (q * (M / 3))) / (1 - q) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hsqrtBound hqM) hsurvival.le
        _ = q * N * M / 3 := by field_simp
    exact (euclideanInfDist_le_dist_of_mem beta w
      (lowerFaceProjection_mem G j beta)).trans (hnorm.trans hnumeric)

private theorem abs_forcedQuit_sub_solo_le (G : QuittingGame) (M : ℝ)
    (hM : IsSimonPayoffScale G M) (p : QuitRow G) (n : G.Player) :
    |ForcedQuitPayoff G p n - SoloPayoff G n| ≤
      2 * (M / 3) * OthersQuitProbability G p n := by
  classical
  have hroot :=
    GameTheory.abs_quittingRootExpectedPayoff_forcedQuit_sub_soloReward_le
      G.reward (SoloPayoff G) (quitRowMarginals G p) n n
      (M := M / 3) hM.2.1
  rw [GameTheory.quittingRootOpponentAbsorptionMass_eq_one_sub_prod] at hroot
  simp only [quitRowMarginals_true_toReal] at hroot
  change |GameTheory.quittingRootQuitPayoff G.reward (SoloPayoff G)
      (quitRowMarginals G p) n - GameTheory.quittingSoloReward G.reward n n| ≤
    2 * (M / 3) * OthersQuitProbability G p n at hroot
  rw [GameTheory.quittingRootQuitPayoff_continuation_invariant
    G.reward (SoloPayoff G) 0 (quitRowMarginals G p) n] at hroot
  unfold GameTheory.quittingRootQuitPayoff at hroot
  rw [ForcedQuitPayoff, quittingOneStagePayoff_eq_rootExpectedPayoff,
    quitRowMarginals_replace_one]
  simpa [GameTheory.quittingSoloReward, SoloPayoff] using hroot

/-- Exact one-stage equilibrium keeps every payoff above the corresponding
solo value up to the opponent-exit error, and pins supported Quit coordinates
on both sides. -/
private theorem oneStage_coordinate_bounds (G : QuittingGame) (M : ℝ)
    (hM : IsSimonPayoffScale G M) (beta : Payoff G.Player)
    (p : QuitRow G) (hp : p ∈ EpsilonRow G 0 beta)
    (hqsmall : QuitProbability G p < 1) (n : G.Player) :
    SoloPayoff G n - 2 * (M / 3) * QuitProbability G p ≤
        QuittingOneStagePayoff G beta p n ∧
      (0 < (p n : ℝ) →
        |QuittingOneStagePayoff G beta p n - SoloPayoff G n| ≤
          2 * (M / 3) * QuitProbability G p) := by
  classical
  have hpnLt : (p n : ℝ) < 1 :=
    (quitProbability_apply_le G p n).trans_lt hqsmall
  have hcontinue : ForcedQuitPayoff G p n ≤
      ForcedContinuePayoff G beta p n := by
    simpa only [sub_zero] using hp.2 n hpnLt
  have hcomb := quittingOneStagePayoff_replace_affine G beta p n (p n)
  rw [QuitRow.replace_self] at hcomb
  have hforced := abs_forcedQuit_sub_solo_le G M hM p n
  have hothers := othersQuitProbability_le G p n
  have hscale : 2 * (M / 3) * OthersQuitProbability G p n ≤
      2 * (M / 3) * QuitProbability G p := by
    exact mul_le_mul_of_nonneg_left hothers (by linarith [hM.1])
  have hforced' : |ForcedQuitPayoff G p n - SoloPayoff G n| ≤
      2 * (M / 3) * QuitProbability G p := hforced.trans hscale
  constructor
  · have hp0 := (p n).property.1
    have hp1 := (p n).property.2
    have hlower := neg_le_of_abs_le hforced'
    nlinarith
  · intro hpn
    have hquit : ForcedContinuePayoff G beta p n ≤
        ForcedQuitPayoff G p n := by
      simpa only [sub_zero] using hp.1 n hpn
    have heq := le_antisymm hcontinue hquit
    have hstage : QuittingOneStagePayoff G beta p n = ForcedQuitPayoff G p n := by
      rw [← heq] at hcomb
      have hp0 := (p n).property.1
      have hp1 := (p n).property.2
      nlinarith
    rw [hstage]
    exact hforced'

/-- The displayed formula underlying `φ`, with the subtype proof erased. -/
private def phiFormula (G : QuittingGame) (M d : ℝ)
    (beta : Payoff G.Player) (p : QuitRow G) : Payoff G.Player := by
  classical
  exact fun j =>
    QuittingOneStagePayoff G beta p j -
      (5 * (Fintype.card G.Player : ℝ) * M / d) *
        ((p j : ℝ) / (1 - (p j : ℝ)) ^ Fintype.card G.Player) +
      M * ∑ k ∈ Finset.univ.erase j, (p k : ℝ)

private theorem quitRow_sum_erase_le_card_mul_quitProbability
    (G : QuittingGame) [DecidableEq G.Player]
    (p : QuitRow G) (n : G.Player) :
    ∑ k ∈ Finset.univ.erase n, (p k : ℝ) ≤
      (Fintype.card G.Player : ℝ) * QuitProbability G p := by
  classical
  calc
    ∑ k ∈ Finset.univ.erase n, (p k : ℝ) ≤
        ∑ _k ∈ Finset.univ.erase n, QuitProbability G p := by
      apply Finset.sum_le_sum
      intro k _hk
      exact quitProbability_apply_le G p k
    _ = ((Finset.univ.erase n).card : ℝ) * QuitProbability G p := by simp
    _ ≤ (Fintype.card G.Player : ℝ) * QuitProbability G p := by
      apply mul_le_mul_of_nonneg_right _ (quitProbability_mem_Icc G p).1
      exact_mod_cast (Finset.card_erase_le :
        ((Finset.univ : Finset G.Player).erase n).card ≤
          (Finset.univ : Finset G.Player).card)

/-- Under the small-hazard hypothesis the singular denominator in `φ`
costs less than a factor of two. -/
private theorem quitPenalty_le_two_mul (G : QuittingGame) (p : QuitRow G)
    (hqpos : 0 < QuitProbability G p)
    (hqsmall : QuitProbability G p <
      1 / (2 * (Fintype.card G.Player : ℝ))) (n : G.Player) :
    (p n : ℝ) / (1 - (p n : ℝ)) ^ Fintype.card G.Player <
      2 * QuitProbability G p := by
  let N : ℝ := Fintype.card G.Player
  let q := QuitProbability G p
  let pn : ℝ := p n
  have hNpos : 0 < N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos
  have hpnq : pn ≤ q := quitProbability_apply_le G p n
  have hNq : N * q < 1 / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hqsmall
    nlinarith
  have hbern : 1 - N * pn ≤ (1 - pn) ^ Fintype.card G.Player := by
    have hraw := one_add_mul_le_pow (a := -pn)
      (n := Fintype.card G.Player) (by
        dsimp only [pn]
        linarith [(p n).property.2])
    dsimp only [N]
    simpa only [sub_eq_add_neg, mul_neg] using hraw
  have hden : 1 / 2 < (1 - pn) ^ Fintype.card G.Player := by
    have hNpn : N * pn ≤ N * q :=
      mul_le_mul_of_nonneg_left hpnq hNpos.le
    linarith
  rw [div_lt_iff₀ (lt_trans (by norm_num) hden)]
  have hqpos' : 0 < q := hqpos
  nlinarith

private theorem phiFormula_coordinate_bounds (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (beta : Payoff G.Player) (p : QuitRow G)
    (hp : p ∈ EpsilonRow G 0 beta)
    (hqpos : 0 < QuitProbability G p)
    (hqsmall : QuitProbability G p <
      1 / (2 * (Fintype.card G.Player : ℝ))) (n : G.Player) :
    let bound := 12 * (Fintype.card G.Player : ℝ) * M *
      QuitProbability G p / d
    SoloPayoff G n - bound ≤ phiFormula G M d beta p n ∧
      (0 < (p n : ℝ) →
        |phiFormula G M d beta p n - SoloPayoff G n| ≤ bound) := by
  classical
  dsimp only
  let N : ℝ := Fintype.card G.Player
  let q := QuitProbability G p
  let stage := QuittingOneStagePayoff G beta p n
  let penalty := (p n : ℝ) /
    (1 - (p n : ℝ)) ^ Fintype.card G.Player
  let others := ∑ k ∈ Finset.univ.erase n, (p k : ℝ)
  let coefficient := 5 * N * M / d
  let bound := 12 * N * M * q / d
  have hNpos : 0 < N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos
  have hNone : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM.1
  have hqOne : q < 1 := by
    have hhalf : 1 / (2 * N) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    exact hqsmall.trans_le hhalf
  have hstage := oneStage_coordinate_bounds G M hM beta p hp hqOne n
  have hpenaltyLt : penalty < 2 * q :=
    quitPenalty_le_two_mul G p hqpos hqsmall n
  have hpenaltyNonneg : 0 ≤ penalty := by
    dsimp only [penalty]
    exact div_nonneg (p n).property.1
      (pow_nonneg (sub_nonneg.mpr (p n).property.2) _)
  have hcoefficientNonneg : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  have hpenaltyTerm : coefficient * penalty ≤ 10 * N * M * q / d := by
    calc
      coefficient * penalty ≤ coefficient * (2 * q) :=
        mul_le_mul_of_nonneg_left hpenaltyLt.le hcoefficientNonneg
      _ = 10 * N * M * q / d := by
        dsimp only [coefficient]
        ring
  have hothersNonneg : 0 ≤ others :=
    Finset.sum_nonneg fun k _ => (p k).property.1
  have hothersBound : others ≤ N * q :=
    quitRow_sum_erase_le_card_mul_quitProbability G p n
  have hothersTerm : M * others ≤ N * M * q := by
    have := mul_le_mul_of_nonneg_left hothersBound hMpos.le
    nlinarith
  have hsmallTerm : 2 * (M / 3) * q ≤ (2 / 3 : ℝ) * N * M * q / d := by
    have hMq : 0 ≤ M * q := mul_nonneg hMpos.le hqpos.le
    have hfactor : d ≤ N := hd1.trans hNone
    rw [le_div_iff₀ hd]
    have hmul := mul_le_mul_of_nonneg_right hfactor hMq
    nlinarith
  have hothersTarget : N * M * q ≤ N * M * q / d := by
    rw [le_div_iff₀ hd]
    have hNMq : 0 ≤ N * M * q := by positivity
    nlinarith
  have hlower : SoloPayoff G n - bound ≤ phiFormula G M d beta p n := by
    have hstageLower := hstage.1
    have hotherTermNonneg : 0 ≤ M * others :=
      mul_nonneg hMpos.le hothersNonneg
    have hbase : SoloPayoff G n - bound ≤ stage - coefficient * penalty := by
      dsimp only [bound, stage, q, N] at hstageLower hpenaltyTerm hsmallTerm ⊢
      have htotal : 2 * (M / 3) * QuitProbability G p +
          5 * (Fintype.card G.Player : ℝ) * M / d *
            ((p n : ℝ) /
              (1 - (p n : ℝ)) ^ Fintype.card G.Player) ≤
          12 * (Fintype.card G.Player : ℝ) * M *
            QuitProbability G p / d := by
        calc
          _ ≤ (2 / 3 : ℝ) * (Fintype.card G.Player : ℝ) * M *
                QuitProbability G p / d +
              10 * (Fintype.card G.Player : ℝ) * M *
                QuitProbability G p / d := add_le_add hsmallTerm hpenaltyTerm
          _ ≤ _ := by
            have hterm : 0 ≤ (Fintype.card G.Player : ℝ) * M *
                QuitProbability G p / d := by positivity
            ring_nf at hterm ⊢
            nlinarith
      linarith
    change SoloPayoff G n - bound ≤
      stage - coefficient * penalty + M * others
    exact hbase.trans (le_add_of_nonneg_right hotherTermNonneg)
  refine ⟨hlower, ?_⟩
  intro hpn
  have hstageAbs := hstage.2 hpn
  have hpenaltyTermNonneg : 0 ≤ coefficient * penalty :=
    mul_nonneg hcoefficientNonneg hpenaltyNonneg
  have hotherTermNonneg : 0 ≤ M * others :=
    mul_nonneg hMpos.le hothersNonneg
  have htriangle :
      |stage - coefficient * penalty + M * others - SoloPayoff G n| ≤
        |stage - SoloPayoff G n| + coefficient * penalty + M * others := by
    calc
      |stage - coefficient * penalty + M * others - SoloPayoff G n| =
          |(stage - SoloPayoff G n) + (M * others - coefficient * penalty)| := by
        congr 1
        ring
      _ ≤ |stage - SoloPayoff G n| + |M * others - coefficient * penalty| :=
        abs_add_le _ _
      _ ≤ |stage - SoloPayoff G n| +
          (|M * others| + |coefficient * penalty|) := by
        exact add_le_add le_rfl (abs_sub _ _)
      _ = |stage - SoloPayoff G n| + coefficient * penalty + M * others := by
        rw [abs_of_nonneg hotherTermNonneg, abs_of_nonneg hpenaltyTermNonneg]
        ring
  have htotal : |stage - SoloPayoff G n| + coefficient * penalty + M * others ≤
      bound := by
    calc
      _ ≤ 2 * (M / 3) * q + 10 * N * M * q / d + N * M * q :=
        add_le_add (add_le_add hstageAbs hpenaltyTerm) hothersTerm
      _ ≤ (2 / 3 : ℝ) * N * M * q / d +
          10 * N * M * q / d + N * M * q / d :=
        add_le_add (add_le_add hsmallTerm le_rfl) hothersTarget
      _ ≤ bound := by
        have hterm : 0 ≤ N * M * q / d := by positivity
        dsimp only [bound]
        ring_nf at hterm ⊢
        nlinarith
  change |stage - coefficient * penalty + M * others - SoloPayoff G n| ≤ bound
  exact htriangle.trans htotal

private theorem phiFormula_infDist_bound (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (beta : Payoff G.Player) (p : QuitRow G)
    (hp : p ∈ EpsilonRow G 0 beta)
    (hqpos : 0 < QuitProbability G p)
    (hqsmall : QuitProbability G p <
      1 / (2 * (Fintype.card G.Player : ℝ)))
    (j : G.Player) (hj : 0 < (p j : ℝ)) :
    EuclideanInfDist (phiFormula G M d beta p)
      (Wj G j ∩ frontier (WSet G)) ≤
      12 * (Fintype.card G.Player : ℝ) ^ 2 * M *
        QuitProbability G p / d := by
  classical
  let N : ℝ := Fintype.card G.Player
  let q := QuitProbability G p
  let bound := 12 * N * M * q / d
  let a := phiFormula G M d beta p
  let w := lowerFaceProjection G j a
  have hNpos : 0 < N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos
  have hboundNonneg : 0 ≤ bound := by
    dsimp only [bound]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hNpos.le)
        (by linarith [hM.1])) hqpos.le) hd.le
  have hcoord : ∀ k, |(a - w) k| ≤ bound := by
    intro k
    have hk := phiFormula_coordinate_bounds G M d hM hd hd1 beta p hp
      hqpos hqsmall k
    by_cases hkj : k = j
    · subst k
      simpa only [Pi.sub_apply, a, w, lowerFaceProjection, if_pos] using hk.2 hj
    · rw [Pi.sub_apply]
      simp only [w, lowerFaceProjection, hkj, if_false]
      rw [abs_sub_comm]
      by_cases hle : SoloPayoff G k ≤ a k
      · rw [max_eq_left hle, sub_self, abs_zero]
        exact hboundNonneg
      · rw [max_eq_right (le_of_not_ge hle),
          abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hle))]
        linarith [hk.1]
  have hdistSum : EuclideanDist a w ≤ ∑ k, |a k - w k| :=
    euclideanDist_le_sum_abs a w
  have hsum : ∑ k, |a k - w k| ≤ N * bound := by
    calc
      ∑ k, |a k - w k| = ∑ k, |(a - w) k| := by rfl
      _ ≤ ∑ _k : G.Player, bound := by
        apply Finset.sum_le_sum
        intro k _hk
        exact hcoord k
      _ = N * bound := by simp [N]
  calc
    EuclideanInfDist a (Wj G j ∩ frontier (WSet G)) ≤
        EuclideanDist a w := euclideanInfDist_le_dist_of_mem a w
          (lowerFaceProjection_mem G j a)
    _ ≤ N * bound := hdistSum.trans hsum
    _ = 12 * (Fintype.card G.Player : ℝ) ^ 2 * M * q / d := by
      dsimp only [N, bound]
      ring

/--
Lemma 3.5.  If `0 < q(p) < 1/(2|N|)`, then every player quitting with
positive probability places both `β` and `a = φ(β,p)` within the displayed
distances of `W_j ∩ ∂W`.
-/
theorem lemma3_5 (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (z : EZeroTilde G)
    (hqpos : 0 < QuitProbability G z.1.2)
    (hqsmall : QuitProbability G z.1.2 <
      1 / (2 * (Fintype.card G.Player : ℝ)))
    (j : G.Player) (hj : 0 < (z.1.2 j : ℝ)) :
    EuclideanInfDist z.1.1 (Wj G j ∩ frontier (WSet G)) ≤
      QuitProbability G z.1.2 * (Fintype.card G.Player : ℝ) * M / 3 ∧
    EuclideanInfDist (Phi G M d z)
      (Wj G j ∩ frontier (WSet G)) ≤
      12 * (Fintype.card G.Player : ℝ) ^ 2 * M *
        QuitProbability G z.1.2 / d := by
  constructor
  · exact beta_infDist_bound G M hM z.1.1 z.1.2 z.2.1
      hqpos hqsmall j hj
  · have hbound := phiFormula_infDist_bound G M d hM hd hd1
      z.1.1 z.1.2 z.2.1 hqpos hqsmall j hj
    have hphi : Phi G M d z = phiFormula G M d z.1.1 z.1.2 := by
      funext k
      rfl
    rw [hphi]
    exact hbound

/-! ## 4. From the topological question to approximate equilibrium existence -/

/-- The singleton-payoff difference matrix `A_Q`. -/
def SingletonDifferenceMatrix (G : QuittingGame) (Q : Finset G.Player) :
    Matrix {i // i ∈ Q} {j // j ∈ Q} ℝ :=
  fun i j =>
    G.reward ⟨{j.1}, Finset.singleton_nonempty j.1⟩ i.1 - SoloPayoff G i.1

/-- The nonsingular assumption of Section 4.2. -/
def HasNonsingularSingletonDifferences (G : QuittingGame) : Prop := by
  classical
  exact ∀ Q : Finset G.Player, 2 ≤ Q.card →
    (SingletonDifferenceMatrix G Q).det ≠ 0

/-- The small off-diagonal singleton perturbation described before Lemma 4.1. -/
def IsNonsingularPerturbation (G : QuittingGame)
    (reward' : {A : Finset G.Player // A.Nonempty} → Payoff G.Player)
    (tol : ℝ) : Prop :=
  (∀ A n, |reward' A n - G.reward A n| ≤ tol) ∧
  (∀ A, A.1.card ≠ 1 → reward' A = G.reward A) ∧
  (∀ i, reward' ⟨{i}, Finset.singleton_nonempty i⟩ i = SoloPayoff G i) ∧
  (∀ i j, i ≠ j →
    reward' ⟨{j}, Finset.singleton_nonempty j⟩ i ≤
      G.reward ⟨{j}, Finset.singleton_nonempty j⟩ i) ∧
  HasNonsingularSingletonDifferences (G.withReward reward')

/-- Uniformly decrease exactly the off-diagonal singleton payoffs. -/
private def perturbedSingletonReward (G : QuittingGame) (η : ℝ)
    (A : {A : Finset G.Player // A.Nonempty}) (i : G.Player) : ℝ := by
  classical
  exact if A.1.card = 1 ∧ i ∉ A.1 then G.reward A i - η else G.reward A i

@[simp] private theorem perturbedSingletonReward_singleton_self
    (G : QuittingGame) (η : ℝ) (i : G.Player) :
    perturbedSingletonReward G η
      ⟨{i}, Finset.singleton_nonempty i⟩ i =
        G.reward ⟨{i}, Finset.singleton_nonempty i⟩ i := by
  simp [perturbedSingletonReward]

@[simp] private theorem perturbedSingletonReward_singleton_other
    (G : QuittingGame) (η : ℝ) {i j : G.Player} (hij : i ≠ j) :
    perturbedSingletonReward G η
      ⟨{j}, Finset.singleton_nonempty j⟩ i =
        G.reward ⟨{j}, Finset.singleton_nonempty j⟩ i - η := by
  simp [perturbedSingletonReward, hij]

private theorem singletonDifferenceMatrix_perturbedSingletonReward
    (G : QuittingGame) [DecidableEq G.Player]
    (η : ℝ) (Q : Finset G.Player) :
    SingletonDifferenceMatrix
        (G.withReward (perturbedSingletonReward G η)) Q =
      SingletonDifferenceMatrix G Q -
        η • Math.LinearAlgebra.offDiagonalOnes {i // i ∈ Q} := by
  classical
  ext i j
  simp only [SingletonDifferenceMatrix, QuittingGame.withReward, SoloPayoff,
    Matrix.sub_apply, Matrix.smul_apply]
  by_cases hij : i = j
  · subst j
    simp [Math.LinearAlgebra.offDiagonalOnes]
  · have hvalue : i.1 ≠ j.1 := by
      intro h
      apply hij
      exact Subtype.ext h
    rw [perturbedSingletonReward_singleton_other G η hvalue,
      perturbedSingletonReward_singleton_self]
    simp [hij, Math.LinearAlgebra.offDiagonalOnes]
    ring

/-- The algebraic part of the generic perturbation: one arbitrarily small
decrease makes every principal singleton-difference matrix nonsingular. -/
private theorem exists_reward_nonsingularPerturbation (G : QuittingGame)
    {tol : ℝ} (htol : 0 < tol) :
    ∃ η : ℝ, 0 < η ∧ η < tol ∧
      IsNonsingularPerturbation G (perturbedSingletonReward G η) tol := by
  classical
  let Eligible := {Q : Finset G.Player // 2 ≤ Q.card}
  let polynomial : Eligible → Polynomial ℝ := fun Q =>
    Math.LinearAlgebra.offDiagonalPerturbationPolynomial
      (SingletonDifferenceMatrix G Q.1)
  have hpolynomial : ∀ Q, polynomial Q ≠ 0 := by
    intro Q
    apply Math.LinearAlgebra.offDiagonalPerturbationPolynomial_ne_zero
    simpa using Q.2
  obtain ⟨η, hη, hηtol, hdet⟩ :=
    Math.LinearAlgebra.exists_pos_lt_forall_polynomial_eval_ne_zero
      polynomial hpolynomial htol
  refine ⟨η, hη, hηtol, ?_, ?_, ?_, ?_, ?_⟩
  · intro A i
    rw [perturbedSingletonReward]
    split_ifs
    · rw [sub_sub_cancel_left, abs_neg, abs_of_pos hη]
      exact hηtol.le
    · simpa only [sub_self, abs_zero] using htol.le
  · intro A hcard
    funext i
    simp [perturbedSingletonReward, hcard]
  · intro i
    simp [perturbedSingletonReward, SoloPayoff]
  · intro i j hij
    simp [perturbedSingletonReward, hij, hη.le]
  · change ∀ Q : Finset G.Player, 2 ≤ Q.card →
      (SingletonDifferenceMatrix
        (G.withReward (perturbedSingletonReward G η)) Q).det ≠ 0
    intro Q hQ
    rw [singletonDifferenceMatrix_perturbedSingletonReward]
    have hnonsingular := hdet ⟨Q, hQ⟩
    rw [Math.LinearAlgebra.offDiagonalPerturbationPolynomial_eval] at hnonsingular
    exact hnonsingular

/-- The paper's generic perturbation assertion: decreasing all off-diagonal
singleton rewards by one sufficiently small common amount makes every
principal difference matrix nonsingular and preserves normality. -/
theorem exists_nonsingularPerturbation (G : QuittingGame)
    (hnormal : ∀ n, IsNormalPlayer G n) {tol : ℝ} (htol : 0 < tol) :
    ∃ reward', IsNonsingularPerturbation G reward' tol ∧
      ∀ n, IsNormalPlayer (G.withReward reward') n := by
  obtain ⟨η, hη, _hηtol, hperturb⟩ :=
    exists_reward_nonsingularPerturbation G htol
  refine ⟨perturbedSingletonReward G η, hperturb, ?_⟩
  intro n
  have hreward : ∀ A,
      perturbedSingletonReward G η A n ≤ G.reward A n := by
    intro A
    simp only [perturbedSingletonReward]
    split_ifs
    · linarith
    · exact le_rfl
  calc
    MinMaxQuit (G.withReward (perturbedSingletonReward G η)) n ≤
        MinMaxQuit G n := minMaxQuit_mono_reward G _ n hreward
    _ ≤ SoloPayoff G n := hnormal n
    _ = SoloPayoff (G.withReward (perturbedSingletonReward G η)) n := by
      simp [SoloPayoff]

/-- Every matrix entry is bounded in absolute value by `B`. -/
def MatrixEntriesBounded {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) : Prop :=
  ∀ i j, |A i j| ≤ B

/--
Lemma 4.1.  A bounded, determinant-separated family of matrices has a common
positive lower bound on its least singular value.
-/
theorem lemma4_1 {n : ℕ} (_hn : 0 < n) {B ε : ℝ}
    (_hB : 0 < B) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin n) (Fin n) ℝ,
      MatrixEntriesBounded A B → ε ≤ |A.det| →
      ∀ v : Fin n → ℝ, δ * EuclideanNorm v ≤ EuclideanNorm (A.mulVec v) := by
  obtain ⟨δ, hδ, hbound⟩ :=
    Math.LinearAlgebra.exists_uniform_mulVec_lower_bound_of_entry_det_bounds
      (n := Fin n) hε
  refine ⟨δ, hδ, ?_⟩
  intro A hentries hdet v
  simpa only [euclideanNorm_eq_norm_toLp] using
    hbound A hentries hdet v

/-- The uniform perturbation corollary to Lemma 4.1. -/
def Corollary4_1Statement (G : QuittingGame) (η : ℝ) : Prop :=
  0 < η ∧ ∀ Q : Finset G.Player, 2 ≤ Q.card →
    ∀ d : Matrix {i // i ∈ Q} {j // j ∈ Q} ℝ,
      (∀ i j, |d i j| ≤ η) →
      ∀ r : {i // i ∈ Q} → ℝ,
        η * EuclideanNorm r ≤
          EuclideanNorm ((SingletonDifferenceMatrix G Q + d).mulVec r)

/--
Corollary 4.1.  One perturbation radius and one lower singular-value bound work
for every principal player set of cardinality at least two.
-/
theorem corollary4_1 (G : QuittingGame)
    (hnonsingular : HasNonsingularSingletonDifferences G) :
    ∃ η, Corollary4_1Statement G η := by
  classical
  let eligible : Finset (Finset G.Player) :=
    Finset.univ.filter fun Q => 2 ≤ Q.card
  let baseBound : ℝ :=
    ∑ i : G.Player, ∑ j : G.Player,
      |G.reward ⟨{j}, Finset.singleton_nonempty j⟩ i - SoloPayoff G i|
  have baseEntry_le (i j : G.Player) :
      |G.reward ⟨{j}, Finset.singleton_nonempty j⟩ i - SoloPayoff G i| ≤
        baseBound := by
    dsimp only [baseBound]
    calc
      |G.reward ⟨{j}, Finset.singleton_nonempty j⟩ i - SoloPayoff G i| ≤
          ∑ j' : G.Player,
            |G.reward ⟨{j'}, Finset.singleton_nonempty j'⟩ i -
              SoloPayoff G i| := by
        exact Finset.single_le_sum
          (f := fun j' : G.Player =>
            |G.reward ⟨{j'}, Finset.singleton_nonempty j'⟩ i -
              SoloPayoff G i|)
          (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)
      _ ≤ ∑ i' : G.Player, ∑ j' : G.Player,
            |G.reward ⟨{j'}, Finset.singleton_nonempty j'⟩ i' -
              SoloPayoff G i'| := by
        exact Finset.single_le_sum
          (f := fun i' : G.Player => ∑ j' : G.Player,
            |G.reward ⟨{j'}, Finset.singleton_nonempty j'⟩ i' -
              SoloPayoff G i'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)
  have gap_pos (Q : Finset G.Player) (hQ : 2 ≤ Q.card) :
      0 < |(SingletonDifferenceMatrix G Q).det| / 2 := by
    exact half_pos (abs_pos.mpr (hnonsingular Q hQ))
  have localRadiusExists (Q : Finset G.Player) (hQ : 2 ≤ Q.card) :
      ∃ radius : ℝ, 0 < radius ∧
        ∀ d : Matrix {i // i ∈ Q} {j // j ∈ Q} ℝ,
          (∀ i j, |d i j| ≤ radius) →
          |(SingletonDifferenceMatrix G Q).det| / 2 <
            |(SingletonDifferenceMatrix G Q + d).det| :=
    Math.LinearAlgebra.exists_entrywise_perturbation_radius_det_lower_bound
      (SingletonDifferenceMatrix G Q) (hnonsingular Q hQ)
  let radius (Q : Finset G.Player) : ℝ :=
    if hQ : 2 ≤ Q.card then
      Classical.choose (localRadiusExists Q hQ)
    else 1
  have radius_pos (Q : Finset G.Player) : 0 < radius Q := by
    by_cases hQ : 2 ≤ Q.card
    · simp only [radius, dif_pos hQ]
      exact (Classical.choose_spec (localRadiusExists Q hQ)).1
    · simp only [radius, dif_neg hQ]
      exact zero_lt_one
  have radius_spec (Q : Finset G.Player) (hQ : 2 ≤ Q.card) :
      ∀ d : Matrix {i // i ∈ Q} {j // j ∈ Q} ℝ,
        (∀ i j, |d i j| ≤ radius Q) →
        |(SingletonDifferenceMatrix G Q).det| / 2 <
          |(SingletonDifferenceMatrix G Q + d).det| := by
    simp only [radius, dif_pos hQ]
    exact (Classical.choose_spec (localRadiusExists Q hQ)).2
  have localStrengthExists (Q : Finset G.Player) (hQ : 2 ≤ Q.card) :
      ∃ strength : ℝ, 0 < strength ∧
        ∀ A : Matrix {i // i ∈ Q} {j // j ∈ Q} ℝ,
          (∀ i j, |A i j| ≤ baseBound + 1) →
          |(SingletonDifferenceMatrix G Q).det| / 2 ≤ |A.det| →
          ∀ v : {i // i ∈ Q} → ℝ,
            strength * ‖WithLp.toLp 2 v‖ ≤
              ‖WithLp.toLp 2 (Matrix.mulVec A v)‖ :=
    Math.LinearAlgebra.exists_uniform_mulVec_lower_bound_of_entry_det_bounds
      (gap_pos Q hQ)
  let strength (Q : Finset G.Player) : ℝ :=
    if hQ : 2 ≤ Q.card then
      Classical.choose (localStrengthExists Q hQ)
    else 1
  have strength_pos (Q : Finset G.Player) : 0 < strength Q := by
    by_cases hQ : 2 ≤ Q.card
    · simp only [strength, dif_pos hQ]
      exact (Classical.choose_spec (localStrengthExists Q hQ)).1
    · simp only [strength, dif_neg hQ]
      exact zero_lt_one
  have strength_spec (Q : Finset G.Player) (hQ : 2 ≤ Q.card) :
      ∀ A : Matrix {i // i ∈ Q} {j // j ∈ Q} ℝ,
        (∀ i j, |A i j| ≤ baseBound + 1) →
        |(SingletonDifferenceMatrix G Q).det| / 2 ≤ |A.det| →
        ∀ v : {i // i ∈ Q} → ℝ,
          strength Q * ‖WithLp.toLp 2 v‖ ≤
            ‖WithLp.toLp 2 (Matrix.mulVec A v)‖ := by
    simp only [strength, dif_pos hQ]
    exact (Classical.choose_spec (localStrengthExists Q hQ)).2
  let threshold (Q : Finset G.Player) : ℝ := min (radius Q) (strength Q)
  let candidates : Finset ℝ := insert 1 (eligible.image threshold)
  have candidates_nonempty : candidates.Nonempty :=
    ⟨1, Finset.mem_insert_self 1 _⟩
  let η : ℝ := candidates.min' candidates_nonempty
  have η_mem : η ∈ candidates := Finset.min'_mem candidates candidates_nonempty
  have η_pos : 0 < η := by
    rcases Finset.mem_insert.mp η_mem with hη | hη
    · simpa only [hη] using zero_lt_one
    · obtain ⟨Q, _, hQ⟩ := Finset.mem_image.mp hη
      rw [← hQ]
      exact lt_min (radius_pos Q) (strength_pos Q)
  have η_le_one : η ≤ 1 :=
    Finset.min'_le candidates 1 (Finset.mem_insert_self 1 _)
  refine ⟨η, η_pos, ?_⟩
  intro Q hQ d hd v
  have hQeligible : Q ∈ eligible := by
    simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hQ
  have hthresholdMem : threshold Q ∈ candidates := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨Q, hQeligible, rfl⟩
  have η_le_threshold : η ≤ threshold Q :=
    Finset.min'_le candidates (threshold Q) hthresholdMem
  have η_le_radius : η ≤ radius Q :=
    η_le_threshold.trans (min_le_left _ _)
  have η_le_strength : η ≤ strength Q :=
    η_le_threshold.trans (min_le_right _ _)
  have hdet := radius_spec Q hQ d fun i j =>
    (hd i j).trans η_le_radius
  have hentries : ∀ i j,
      |(SingletonDifferenceMatrix G Q + d) i j| ≤ baseBound + 1 := by
    intro i j
    rw [Matrix.add_apply]
    calc
      |SingletonDifferenceMatrix G Q i j + d i j| ≤
          |SingletonDifferenceMatrix G Q i j| + |d i j| := abs_add_le _ _
      _ ≤ baseBound + η := by
        apply add_le_add (baseEntry_le i.1 j.1) (hd i j)
      _ ≤ baseBound + 1 := add_le_add le_rfl η_le_one
  have vNorm_nonneg : 0 ≤ EuclideanNorm v := by
    exact Real.sqrt_nonneg _
  calc
    η * EuclideanNorm v ≤ strength Q * EuclideanNorm v :=
      mul_le_mul_of_nonneg_right η_le_strength vNorm_nonneg
    _ ≤ EuclideanNorm ((SingletonDifferenceMatrix G Q + d).mulVec v) := by
      simpa only [euclideanNorm_eq_norm_toLp] using
        strength_spec Q hQ (SingletonDifferenceMatrix G Q + d)
          hentries hdet.le v

/-! ### 4.3. The compact set and the glued correspondence -/

/-- The coordinate cube used to truncate `W`. -/
def ClosedCoordinateCube {N : Type} [Fintype N] (R : ℝ) : Set (Payoff N) :=
  {x | ∀ j, -R ≤ x j ∧ x j ≤ R}

/-- `C_j = W_j ∩ [-R-1,R+1]ᴺ`. -/
def TruncatedPiece (G : QuittingGame) (R : ℝ) (j : G.Player) :
    Set (Payoff G.Player) :=
  Wj G j ∩ ClosedCoordinateCube (R + 1)

/-- `C = W ∩ [-R-1,R+1]ᴺ`. -/
def TruncatedW (G : QuittingGame) (R : ℝ) : Set (Payoff G.Player) :=
  WSet G ∩ ClosedCoordinateCube (R + 1)

/-- The lower part `D = closure(∂C \ ∂W)`. -/
def LowerBoundary (G : QuittingGame) (R : ℝ) : Set (Payoff G.Player) :=
  closure (frontier (TruncatedW G R) \ frontier (WSet G))

private theorem isClosed_closedCoordinateCube {N : Type} [Fintype N]
    (R : ℝ) : IsClosed (ClosedCoordinateCube (N := N) R) := by
  rw [show ClosedCoordinateCube R =
      ⋂ j, {x : Payoff N | -R ≤ x j} ∩ {x : Payoff N | x j ≤ R} by
    ext x
    simp only [ClosedCoordinateCube, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_inter_iff]]
  exact isClosed_iInter fun j =>
    (isClosed_le (continuous_const : Continuous fun _ : Payoff N => -R)
      (continuous_apply j)).inter
      (isClosed_le (continuous_apply j)
        (continuous_const : Continuous fun _ : Payoff N => R))

private theorem mem_frontier_closedCoordinateCube_exists_abs_eq
    {N : Type} [Fintype N] [Nonempty N] {R : ℝ} (hR : 0 < R)
    {x : Payoff N} (hx : x ∈ frontier (ClosedCoordinateCube R)) :
    ∃ j, |x j| = R := by
  have hxCube : x ∈ ClosedCoordinateCube R :=
    (isClosed_closedCoordinateCube R).frontier_subset hx
  by_contra hnot
  push Not at hnot
  have hstrict : ∀ j, -R < x j ∧ x j < R := by
    intro j
    have hj := hxCube j
    have habsNe : |x j| ≠ R := hnot j
    constructor
    · by_contra hle
      have heq : x j = -R := by linarith
      apply habsNe
      rw [heq, abs_neg, abs_of_pos hR]
    · by_contra hle
      have heq : x j = R := by linarith
      apply habsNe
      rw [heq, abs_of_pos hR]
  let box : Set (Payoff N) := Set.pi Set.univ fun _ => Set.Ioo (-R) R
  have hboxOpen : IsOpen box :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have hxBox : x ∈ box := fun j _ => hstrict j
  have hboxSubset : box ⊆ ClosedCoordinateCube R := by
    intro y hy j
    exact ⟨(hy j (Set.mem_univ j)).1.le, (hy j (Set.mem_univ j)).2.le⟩
  have hxInterior : x ∈ interior (ClosedCoordinateCube R) := by
    rw [mem_interior_iff_mem_nhds]
    exact mem_of_superset (hboxOpen.mem_nhds hxBox) hboxSubset
  exact ((mem_frontier_iff_notMem_interior hxCube).mp hx) hxInterior

private theorem lowerBoundary_has_cube_coordinate (G : QuittingGame)
    {R : ℝ} (hR : 0 < R + 1) {x : Payoff G.Player}
    (hx : x ∈ LowerBoundary G R) :
    ∃ j, |x j| = R + 1 := by
  let boundaryCoordinates : Set (Payoff G.Player) :=
    {x | ∃ j, |x j| = R + 1}
  have hsource :
      frontier (TruncatedW G R) \ frontier (WSet G) ⊆ boundaryCoordinates := by
    rintro y ⟨hy, hyW⟩
    have hyUnion : y ∈
        frontier (WSet G) ∩ closure (ClosedCoordinateCube (R + 1)) ∪
          closure (WSet G) ∩ frontier (ClosedCoordinateCube (R + 1)) := by
      exact frontier_inter_subset (WSet G) (ClosedCoordinateCube (R + 1))
        (by simpa only [TruncatedW] using hy)
    rcases hyUnion with ⟨hyW', _⟩ | ⟨_, hyCube⟩
    · exact (hyW hyW').elim
    · exact mem_frontier_closedCoordinateCube_exists_abs_eq hR hyCube
  have hclosed : IsClosed boundaryCoordinates := by
    have heq : boundaryCoordinates =
        ⋃ j, {x : Payoff G.Player | |x j| = R + 1} := by
      ext y
      simp only [boundaryCoordinates, Set.mem_setOf_eq, Set.mem_iUnion]
    rw [heq]
    exact isClosed_iUnion_of_finite fun j =>
      isClosed_eq (continuous_abs.comp (continuous_apply j)) continuous_const
  exact closure_minimal hsource hclosed hx

private def lowerCubeCorner (G : QuittingGame) (R : ℝ) :
    Payoff G.Player := fun _ => -(R + 1)

private theorem lowerCubeCorner_mem_lowerBoundary (G : QuittingGame)
    (R : ℝ) (hR : 0 ≤ R + 1)
    (hsolo : ∀ j, -(R + 1) < SoloPayoff G j) :
    lowerCubeCorner G R ∈ LowerBoundary G R := by
  classical
  let j : G.Player := Classical.choice inferInstance
  have hcornerW : lowerCubeCorner G R ∈ WSet G := by
    exact ⟨j, (hsolo j).le⟩
  have hcornerCube : lowerCubeCorner G R ∈ ClosedCoordinateCube (R + 1) := by
    intro k
    dsimp only [lowerCubeCorner]
    constructor <;> linarith
  have hcornerTruncated : lowerCubeCorner G R ∈ TruncatedW G R :=
    ⟨hcornerW, hcornerCube⟩
  have hcornerInteriorW : lowerCubeCorner G R ∈ interior (WSet G) := by
    let U : Set (Payoff G.Player) := {x | x j < SoloPayoff G j}
    have hUOpen : IsOpen U := isOpen_lt (continuous_apply j) continuous_const
    have hcornerU : lowerCubeCorner G R ∈ U := hsolo j
    have hUW : U ⊆ WSet G := by
      intro x hx
      exact ⟨j, hx.le⟩
    rw [mem_interior_iff_mem_nhds]
    exact mem_of_superset (hUOpen.mem_nhds hcornerU) hUW
  have hcornerFrontier : lowerCubeCorner G R ∈ frontier (TruncatedW G R) := by
    rw [frontier_eq_closure_inter_closure]
    constructor
    · exact subset_closure hcornerTruncated
    · let outside : ℕ → Payoff G.Player := fun m k =>
        lowerCubeCorner G R k - 1 / ((m : ℝ) + 1)
      have houtsideTendsto : Tendsto outside atTop (nhds (lowerCubeCorner G R)) := by
        apply tendsto_pi_nhds.mpr
        intro k
        have hzero := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa only [outside, sub_zero] using tendsto_const_nhds.sub hzero
      apply mem_closure_of_tendsto (b := atTop) (f := outside) houtsideTendsto
      exact Filter.Eventually.of_forall fun m => by
        rw [Set.mem_compl_iff]
        intro hm
        have hcoord := hm.2 j
        have hpositive : 0 < 1 / ((m : ℝ) + 1) := by positivity
        dsimp only [outside, lowerCubeCorner] at hcoord
        linarith
  apply subset_closure
  refine ⟨hcornerFrontier, ?_⟩
  intro hfrontier
  rw [frontier] at hfrontier
  exact hfrontier.2 hcornerInteriorW

private theorem abs_coordinate_sub_le_euclideanDist
    {N : Type} [Fintype N] (x y : Payoff N) (j : N) :
    |x j - y j| ≤ EuclideanDist x y := by
  rw [EuclideanDist, euclideanNorm_eq_norm_toLp]
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    PiLp.norm_apply_le (WithLp.toLp 2 (x - y)) j

private theorem exists_large_coordinate_of_cutoff_pos
    (G : QuittingGame) {R ω : ℝ} (hR : 0 < R + 1) (hω1 : ω ≤ 1)
    (hD : (LowerBoundary G R).Nonempty)
    (cutoff : Payoff G.Player → UnitInterval)
    (hvanish : ∀ x, ω ≤ EuclideanInfDist x (LowerBoundary G R) →
      (cutoff x : ℝ) = 0)
    (a : Payoff G.Player) (ha : 0 < (cutoff a : ℝ)) :
    ∃ j, R < |a j| := by
  have hdist : EuclideanInfDist a (LowerBoundary G R) < ω := by
    by_contra hnot
    have hzero := hvanish a (le_of_not_gt hnot)
    linarith
  obtain ⟨distance, ⟨b, hbD, rfl⟩, hab⟩ :=
    exists_lt_of_csInf_lt (hD.image (EuclideanDist a)) hdist
  obtain ⟨j, hbj⟩ := lowerBoundary_has_cube_coordinate G hR hbD
  have hcoordinate := abs_coordinate_sub_le_euclideanDist a b j
  have habs : |b j| - |a j| ≤ |a j - b j| := by
    calc
      |b j| - |a j| ≤ |(|b j| - |a j|)| := le_abs_self _
      _ ≤ |b j - a j| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |a j - b j| := abs_sub_comm _ _
  refine ⟨j, ?_⟩
  linarith

/-- The upper part `U = ∂C ∩ ∂W`. -/
def UpperBoundary (G : QuittingGame) (R : ℝ) : Set (Payoff G.Player) :=
  frontier (TruncatedW G R) ∩ frontier (WSet G)

/-- The small quitting bound `δ = ε / (2|N|M)` from Section 4.3. -/
def Section4Delta (G : QuittingGame) (M ε : ℝ) : ℝ :=
  ε / (2 * (Fintype.card G.Player : ℝ) * M)

/-- The small-step radius `ω = d ε ξ ρ δ / (200 R |N|² M)`. -/
def Section4Omega (G : QuittingGame) (M d ρ ξ R ε : ℝ) : ℝ :=
  d * ε * ξ * ρ * Section4Delta G M ε /
    (200 * R * (Fintype.card G.Player : ℝ) ^ 2 * M)

private theorem section4Omega_mem_Ioc (G : QuittingGame)
    (M d ρ ξ R ε : ℝ) (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (hε : 0 < ε) (hερ : ε < ρ / 3) :
    Section4Omega G M d ρ ξ R ε ∈ Set.Ioc 0 1 := by
  let N : ℝ := Fintype.card G.Player
  obtain ⟨hξ, hξ1, hR⟩ := section3Constants_radius_bound
    G M d ρ ξ R hplayers hM hd hd1 hmotion hconstants
  have hN : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hplayers
  have hN1 : 1 ≤ N := by linarith
  have hM1 : 1 ≤ M := hM.1
  have hρ1 : ρ ≤ 1 := hmotion.2.2.1
  have hε1 : ε ≤ 1 := by linarith
  have hδpos : 0 < Section4Delta G M ε := by
    rw [Section4Delta]
    positivity
  have hδ1 : Section4Delta G M ε ≤ 1 := by
    rw [Section4Delta, div_le_one (by positivity :
      0 < 2 * (Fintype.card G.Player : ℝ) * M)]
    dsimp only [N] at hN ⊢
    nlinarith
  have hproduct1 : d * ε * ξ * ρ * Section4Delta G M ε ≤ 1 := by
    have hdε : d * ε ≤ 1 := mul_le_one₀ hd1 hε.le hε1
    have hdεξ : d * ε * ξ ≤ 1 := mul_le_one₀ hdε hξ.le hξ1.le
    have hdεξρ : d * ε * ξ * ρ ≤ 1 :=
      mul_le_one₀ hdεξ hmotion.2.1.le hρ1
    exact mul_le_one₀ hdεξρ hδpos.le hδ1
  have hR1 : 1 ≤ R := by
    have hNM : 3 ≤ N * M := by
      nlinarith [mul_le_mul hN hM1 (by norm_num) (by linarith : 0 ≤ N)]
    have hR' : 10 * N * M ≤ R := by simpa only [N] using hR
    nlinarith
  have hNpow : 1 ≤ N ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ N - 1)
      (by linarith : 0 ≤ N + 1)]
  have hden1 : 1 ≤ 200 * R * N ^ 2 * M := by
    have hfirst : 1 ≤ 200 * R := by nlinarith
    have hsecond : 200 * R ≤ 200 * R * N ^ 2 := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ 200 * R)
        (by linarith : 0 ≤ N ^ 2 - 1)]
    have hthird : 200 * R * N ^ 2 ≤ 200 * R * N ^ 2 * M := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ 200 * R * N ^ 2)
        (by linarith : 0 ≤ M - 1)]
    exact hfirst.trans (hsecond.trans hthird)
  have hdenpos : 0 < 200 * R * N ^ 2 * M := zero_lt_one.trans_le hden1
  constructor
  · rw [Section4Omega]
    apply div_pos
    · exact mul_pos (mul_pos (mul_pos (mul_pos hd hε) hξ) hmotion.2.1) hδpos
    · simpa only [N] using hdenpos
  · rw [Section4Omega, div_le_one]
    · simpa only [N] using hproduct1.trans hden1
    · simpa only [N] using hdenpos

/--
The cutoff `λ` used to glue the structure homotopy to the identity near `D`.
Its support radius is the paper's `ω`, not the separate quitting bound `δ`.
-/
def IsSection4Cutoff (G : QuittingGame) (R ω : ℝ)
    (cutoff : Payoff G.Player → UnitInterval) : Prop :=
  Continuous cutoff ∧
  (∀ x ∈ LowerBoundary G R, (cutoff x : ℝ) = 1) ∧
  (∀ x, ω ≤ EuclideanInfDist x (LowerBoundary G R) → (cutoff x : ℝ) = 0) ∧
  ∀ x ∈ TruncatedW G R \ LowerBoundary G R, (cutoff x : ℝ) < 1

/-- The first coordinate `x(a)` of the deformed graph. -/
def Section4X (G : QuittingGame) {M d : ℝ}
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval) (a : Payoff G.Player) :
    Payoff G.Player :=
  (cutoff a : ℝ) • a + (1 - (cutoff a : ℝ)) • (inverse.inv a).1.1

/-- The one-stage payoff `z(a) = f(x(a),p(a))` used in Lemma 4.3. -/
def Section4Z (G : QuittingGame) {M d : ℝ}
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval) (a : Payoff G.Player) :
    Payoff G.Player :=
  QuittingOneStagePayoff G (Section4X G inverse cutoff a) (inverse.inv a).1.2

/-- The second coordinate `y(a) = λ(a)x(a) + (1-λ(a))z(a)`. -/
def Section4Y (G : QuittingGame) {M d : ℝ}
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval) (a : Payoff G.Player) :
    Payoff G.Player :=
  let x := Section4X G inverse cutoff a
  (cutoff a : ℝ) • x +
    (1 - (cutoff a : ℝ)) • Section4Z G inverse cutoff a

/-- The straight-line homotopy used in Section 4.3. -/
def Section4H (G : QuittingGame) {M d : ℝ}
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval)
    (a : Payoff G.Player) (t : UnitInterval) :
    Payoff G.Player × Payoff G.Player :=
  (1 - (t : ℝ)) • (a, a) +
    (t : ℝ) • (Section4X G inverse cutoff a, Section4Y G inverse cutoff a)

/-- The upper neighborhoods `V_j`. -/
def UpperNeighborhoodFor (G : QuittingGame) (R ε : ℝ)
    (j : G.Player) : Set (Payoff G.Player) :=
  {x | (∀ k, SoloPayoff G k - ε / 3 ≤ x k ∧ x k ≤ R + 1 + ε / 3) ∧
    x j ≤ SoloPayoff G j + ε / 3}

/-- `V_U = ⋃_j V_j`. -/
def UpperNeighborhood (G : QuittingGame) (R ε : ℝ) :
    Set (Payoff G.Player) :=
  ⋃ j, UpperNeighborhoodFor G R ε j

/-- `V_D`, the `ε/3` neighborhood of the lower boundary. -/
def LowerNeighborhood (G : QuittingGame) (R ε : ℝ) :
    Set (Payoff G.Player) :=
  {x | EuclideanInfDist x (LowerBoundary G R) ≤ ε / 3}

/-- The small-probability quitting correspondence near `U`. -/
def UpperGlueFiber (G : QuittingGame) (R ε δ : ℝ)
    (x : Payoff G.Player) : Set (Payoff G.Player) := by
  classical
  exact {y | ∃ p : QuitRow G,
    y = QuittingOneStagePayoff G x p ∧
      ∀ j, if x ∈ UpperNeighborhoodFor G R ε j
        then (p j : ℝ) ≤ δ else (p j : ℝ) = 0}

/-- Convex combinations of `x` with feasible vectors near `D`. -/
def LowerGlueFiber (G : QuittingGame) (x : Payoff G.Player) :
    Set (Payoff G.Player) :=
  {y | ∃ z, Feasible G z ∧ ∃ t : UnitInterval,
    y = (1 - (t : ℝ)) • x + (t : ℝ) • z}

/-- The piecewise glued correspondence `G`. -/
def GluedFiber (G : QuittingGame) (R ε δ : ℝ) :
    Correspondence (Payoff G.Player) (Payoff G.Player) := by
  classical
  exact fun x =>
    if x ∈ LowerNeighborhood G R ε then LowerGlueFiber G x
    else if x ∈ UpperNeighborhood G R ε then UpperGlueFiber G R ε δ x
    else ∅

/-- The compact neighborhood `V = V_U ∪ V_D`. -/
def GluedNeighborhood (G : QuittingGame) (R ε : ℝ) : Set (Payoff G.Player) :=
  UpperNeighborhood G R ε ∪ LowerNeighborhood G R ε

/-- `J = H(C,1) ∪ G`. -/
def Section4J (G : QuittingGame) {M d : ℝ}
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval)
    (R ε δ : ℝ) : Set (Payoff G.Player × Payoff G.Player) :=
  HomotopyTerminalImage (TruncatedW G R) (Section4H G inverse cutoff) ∪
    correspondenceGraph (GluedFiber G R ε δ)

/-- The mass of the nonempty Bernoulli coalitions is the one-stage quit probability. -/
private theorem nonemptyCoalitionMass_eq_quitProbability
    (G : QuittingGame) (p : QuitRow G) :
    (∑ A ∈ Finset.univ.powerset,
        if A.Nonempty then CoalitionProbability G p A else 0) =
      QuitProbability G p := by
  classical
  have hsum := coalitionProbability_sum G p
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
        (fun A => CoalitionProbability G p A)
        (by simp : (∅ : Finset G.Player) ∈ Finset.univ.powerset)
      linarith
    _ = QuitProbability G p := by rw [hsum, hempty]; ring

/-- Centering the immediate reward at one terminal payoff costs at most quit mass. -/
private theorem centeredRewardPart_mem_Icc
    (G : QuittingGame) (p : QuitRow G) (n : G.Player)
    (reference : {A : Finset G.Player // A.Nonempty}) {D : ℝ}
    (_hD : 0 ≤ D) (hbound : ∀ A, |G.reward A n - G.reward reference n| ≤ D) :
    (∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
        CoalitionProbability G p A * G.reward ⟨A, hA⟩ n else 0) -
          QuitProbability G p * G.reward reference n ∈
      Set.Icc (-D * QuitProbability G p) (D * QuitProbability G p) := by
  classical
  let centered : ℝ := ∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
    CoalitionProbability G p A * (G.reward ⟨A, hA⟩ n - G.reward reference n) else 0
  have hcentered :
      (∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
          CoalitionProbability G p A * G.reward ⟨A, hA⟩ n else 0) -
            QuitProbability G p * G.reward reference n = centered := by
    rw [← nonemptyCoalitionMass_eq_quitProbability G p]
    simp only [Finset.sum_mul]
    dsimp only [centered]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro A hA
    split_ifs <;> ring
  rw [hcentered]
  constructor
  · rw [← nonemptyCoalitionMass_eq_quitProbability G p, Finset.mul_sum]
    dsimp only [centered]
    apply Finset.sum_le_sum
    intro A hA
    split_ifs with hnonempty
    · have hprob := coalitionProbability_nonneg G p A
      have hreward := neg_le_of_abs_le (hbound ⟨A, hnonempty⟩)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hreward hprob
    · simp
  · rw [← nonemptyCoalitionMass_eq_quitProbability G p, Finset.mul_sum]
    dsimp only [centered]
    apply Finset.sum_le_sum
    intro A hA
    split_ifs with hnonempty
    · have hprob := coalitionProbability_nonneg G p A
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (le_of_abs_le (hbound ⟨A, hnonempty⟩)) hprob
    · simp

/-- A row whose coordinates are at most `δ` quits with probability at most `|N|δ`. -/
private theorem quitProbability_le_card_mul
    (G : QuittingGame) (p : QuitRow G) {δ : ℝ} (hp : ∀ n, (p n : ℝ) ≤ δ) :
    QuitProbability G p ≤ (Fintype.card G.Player : ℝ) * δ := by
  calc
    QuitProbability G p ≤ ∑ n ∈ Finset.univ, (p n : ℝ) := by
      exact Math.one_sub_prod_one_sub_le_sum (fun n => (p n : ℝ)) Finset.univ
        (fun n _ => (p n).property.1) (fun n _ => (p n).property.2)
    _ ≤ ∑ _n ∈ (Finset.univ : Finset G.Player), δ := by
      exact Finset.sum_le_sum fun n _ => hp n
    _ = (Fintype.card G.Player : ℝ) * δ := by simp

/-- With one player forced to quit, the singleton atom is opponent survival. -/
private theorem forcedQuit_singletonProbability
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

/-- Forcing one player to quit changes her solo payoff only through opponent quitting. -/
private theorem forcedQuitPayoff_sub_solo_mem_Icc
    (G : QuittingGame) (p : QuitRow G) (n : G.Player) {D : ℝ}
    (hD : 0 ≤ D)
    (hbound : ∀ A, |G.reward A n - SoloPayoff G n| ≤ D) :
    ForcedQuitPayoff G p n - SoloPayoff G n ∈
      Set.Icc (-D * QuitProbability G (p.replace G n 0))
        (D * QuitProbability G (p.replace G n 0)) := by
  classical
  let pQuit := p.replace G n 1
  let singleton : Finset G.Player := {n}
  let centered : Finset G.Player → ℝ := fun A => if hA : A.Nonempty then
    CoalitionProbability G pQuit A * (G.reward ⟨A, hA⟩ n - SoloPayoff G n) else 0
  have hpQuit : QuitProbability G pQuit = 1 := quitProbability_replace_one G p n
  have hcentered : ForcedQuitPayoff G p n - SoloPayoff G n =
      ∑ A ∈ Finset.univ.powerset, centered A := by
    change QuittingOneStagePayoff G 0 pQuit n - SoloPayoff G n = _
    simp only [QuittingOneStagePayoff, hpQuit, sub_self, zero_mul, zero_add]
    have hmass : (∑ A ∈ Finset.univ.powerset,
        if A.Nonempty then CoalitionProbability G pQuit A else 0) = 1 := by
      rw [nonemptyCoalitionMass_eq_quitProbability G pQuit, hpQuit]
    rw [show SoloPayoff G n = 1 * SoloPayoff G n by ring, ← hmass]
    simp only [Finset.sum_mul]
    dsimp only [centered]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro A hA
    split_ifs <;> ring
  have hsingleton : centered singleton = 0 := by
    simp [centered, singleton, pQuit, SoloPayoff]
  have hmass :
      ∑ A ∈ Finset.univ.powerset.erase singleton,
          CoalitionProbability G pQuit A = QuitProbability G (p.replace G n 0) := by
    have hmem : singleton ∈ (Finset.univ.powerset : Finset (Finset G.Player)) := by
      simp [singleton]
    have hdecomp := Finset.sum_erase_add Finset.univ.powerset
      (fun A => CoalitionProbability G pQuit A) hmem
    rw [coalitionProbability_sum G pQuit] at hdecomp
    have hsingle : CoalitionProbability G pQuit singleton =
        1 - QuitProbability G (p.replace G n 0) := by
      exact forcedQuit_singletonProbability G p n
    rw [hsingle] at hdecomp
    linarith
  rw [hcentered]
  have herase : ∑ A ∈ Finset.univ.powerset, centered A =
      ∑ A ∈ Finset.univ.powerset.erase singleton, centered A := by
    have hmem : singleton ∈ (Finset.univ.powerset : Finset (Finset G.Player)) := by
      simp [singleton]
    have hdecomp := Finset.sum_erase_add Finset.univ.powerset centered hmem
    rw [hsingleton, add_zero] at hdecomp
    exact hdecomp.symm
  rw [herase]
  constructor
  · rw [← hmass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro A hA
    dsimp only [centered]
    split_ifs with hnonempty
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (neg_le_of_abs_le (hbound ⟨A, hnonempty⟩))
        (coalitionProbability_nonneg G pQuit A)
    · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hD)
        (coalitionProbability_nonneg G pQuit A)
  · rw [← hmass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro A hA
    dsimp only [centered]
    split_ifs with hnonempty
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (le_of_abs_le (hbound ⟨A, hnonempty⟩))
        (coalitionProbability_nonneg G pQuit A)
    · exact mul_nonneg hD (coalitionProbability_nonneg G pQuit A)

/--
Lemma 4.2: the upper glue is contained in `F_ε`.  Membership of `x` in the
upper neighborhood is explicit; without it `UpperGlueFiber` contains the
all-continue image even outside the domain intended in the paper.  The missing
proof is the finite product estimate that changing a row with total coordinate
hazard at most `|N|δ` changes each endpoint payoff by at most `ε/3`, followed
by the two support inequalities defining `E_ε`.
-/
theorem lemma4_2 (G : QuittingGame) (M R ε δ : ℝ)
    (hM : IsSimonPayoffScale G M) (hε : 0 < ε)
    (hδ : δ = Section4Delta G M ε) :
    ∀ x, x ∈ UpperNeighborhood G R ε → ∀ y,
      y ∈ UpperGlueFiber G R ε δ x → y ∈ FRow G ε x := by
  classical
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM.1
  have hcardNat : 0 < Fintype.card G.Player := Fintype.card_pos
  have hcard : 0 < (Fintype.card G.Player : ℝ) := by exact_mod_cast hcardNat
  have hδpos : 0 < δ := by
    rw [hδ, Section4Delta]
    positivity
  have hscale : M / 3 * ((Fintype.card G.Player : ℝ) * δ) = ε / 6 := by
    rw [hδ, Section4Delta]
    field_simp
    ring
  have hrewardDiff : ∀ n A, |G.reward A n - SoloPayoff G n| ≤ M / 3 := by
    intro n A
    have hbound := hM.2.2 A
      ⟨{n}, Finset.singleton_nonempty n⟩ n
    dsimp only [SoloPayoff]
    nlinarith
  intro x hx y hy
  rw [UpperNeighborhood] at hx
  rcases Set.mem_iUnion.mp hx with ⟨witness, hxWitness⟩
  rcases hy with ⟨p, rfl, hp⟩
  have hpδ : ∀ n, (p n : ℝ) ≤ δ := by
    intro n
    by_cases hn : x ∈ UpperNeighborhoodFor G R ε n
    · simpa [hn] using hp n
    · have hzero : (p n : ℝ) = 0 := by simpa [hn] using hp n
      linarith
  have hreplaceδ : ∀ n k, ((p.replace G n 0) k : ℝ) ≤ δ := by
    intro n k
    by_cases hkn : k = n
    · subst k
      simp [QuitRow.replace, hδpos.le]
    · simpa [QuitRow.replace, hkn] using hpδ k
  have hquitBound : ∀ n,
      QuitProbability G (p.replace G n 0) ≤
        (Fintype.card G.Player : ℝ) * δ := by
    intro n
    exact quitProbability_le_card_mul G (p.replace G n 0) (hreplaceδ n)
  have herror : ∀ n,
      M / 3 * QuitProbability G (p.replace G n 0) ≤ ε / 6 := by
    intro n
    calc
      M / 3 * QuitProbability G (p.replace G n 0) ≤
          M / 3 * ((Fintype.card G.Player : ℝ) * δ) :=
        mul_le_mul_of_nonneg_left (hquitBound n) (by positivity)
      _ = ε / 6 := hscale
  have hforced : ∀ n,
      ForcedQuitPayoff G p n - SoloPayoff G n ∈
        Set.Icc (-(ε / 6)) (ε / 6) := by
    intro n
    have hraw := forcedQuitPayoff_sub_solo_mem_Icc G p n
      (show 0 ≤ M / 3 by positivity) (hrewardDiff n)
    constructor <;> nlinarith [herror n, hraw.1, hraw.2]
  have hcontinueLower : ∀ n,
      SoloPayoff G n - ε / 2 ≤ ForcedContinuePayoff G x p n := by
    intro n
    let row := p.replace G n 0
    let q := QuitProbability G row
    have hq := quitProbability_mem_Icc G row
    have hxLower : SoloPayoff G n - ε / 3 ≤ x n := (hxWitness.1 n).1
    have hweighted :
        (1 - q) * (SoloPayoff G n - ε / 3) ≤ (1 - q) * x n :=
      mul_le_mul_of_nonneg_left hxLower (by linarith [hq.2])
    have hcentered := centeredRewardPart_mem_Icc G row n
      ⟨{n}, Finset.singleton_nonempty n⟩
      (show 0 ≤ M / 3 by positivity) (hrewardDiff n)
    have hcentered' :
        (∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
            CoalitionProbability G row A * G.reward ⟨A, hA⟩ n else 0) -
              q * SoloPayoff G n ∈
          Set.Icc (-(M / 3) * q) (M / 3 * q) := by
      simpa only [q, SoloPayoff] using hcentered
    have hqError : M / 3 * q ≤ ε / 6 := by
      simpa only [row, q] using herror n
    have hεq : 0 ≤ q * (ε / 3) := mul_nonneg hq.1 (by positivity)
    change SoloPayoff G n - ε / 2 ≤
      (1 - q) * x n +
        ∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
          CoalitionProbability G row A * G.reward ⟨A, hA⟩ n else 0
    dsimp only [q] at hweighted hcentered' hqError hεq ⊢
    nlinarith [hweighted, hcentered'.1, hεq]
  have hcontinueUpper : ∀ n, x n ≤ SoloPayoff G n + ε / 3 →
      ForcedContinuePayoff G x p n ≤ SoloPayoff G n + ε / 2 := by
    intro n hxUpper
    let row := p.replace G n 0
    let q := QuitProbability G row
    have hq := quitProbability_mem_Icc G row
    have hweighted :
        (1 - q) * x n ≤ (1 - q) * (SoloPayoff G n + ε / 3) :=
      mul_le_mul_of_nonneg_left hxUpper (by linarith [hq.2])
    have hcentered := centeredRewardPart_mem_Icc G row n
      ⟨{n}, Finset.singleton_nonempty n⟩
      (show 0 ≤ M / 3 by positivity) (hrewardDiff n)
    have hcentered' :
        (∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
            CoalitionProbability G row A * G.reward ⟨A, hA⟩ n else 0) -
              q * SoloPayoff G n ∈
          Set.Icc (-(M / 3) * q) (M / 3 * q) := by
      simpa only [q, SoloPayoff] using hcentered
    have hqError : M / 3 * q ≤ ε / 6 := by
      simpa only [row, q] using herror n
    have hεq : 0 ≤ q * (ε / 3) := mul_nonneg hq.1 (by positivity)
    change (1 - q) * x n +
        (∑ A ∈ Finset.univ.powerset, if hA : A.Nonempty then
          CoalitionProbability G row A * G.reward ⟨A, hA⟩ n else 0) ≤
      SoloPayoff G n + ε / 2
    dsimp only [q] at hweighted hcentered' hqError hεq ⊢
    nlinarith [hweighted, hcentered'.2, hεq]
  refine ⟨p, ⟨?_, ?_⟩, rfl⟩
  · intro n hnQuit
    have hnNeighborhood : x ∈ UpperNeighborhoodFor G R ε n := by
      by_contra hn
      have hzero : (p n : ℝ) = 0 := by simpa [hn] using hp n
      linarith
    have hxUpper : x n ≤ SoloPayoff G n + ε / 3 := hnNeighborhood.2
    linarith [hforced n |>.1, hcontinueUpper n hxUpper]
  · intro n _hnContinue
    linarith [hcontinueLower n, hforced n |>.2]

/-- The one-stage value differs from the terminal reward conditional on
absorption only through the all-Continue branch. -/
private theorem quittingOneStagePayoff_sub_conditionalReward
    (G : QuittingGame) (x : Payoff G.Player) (p : QuitRow G)
    (n : G.Player) (hquit : 0 < QuitProbability G p) :
    QuittingOneStagePayoff G x p n -
        quittingRewardPart G p n / QuitProbability G p =
      (1 - QuitProbability G p) *
        (x n - quittingRewardPart G p n / QuitProbability G p) := by
  change ((1 - QuitProbability G p) * x n + quittingRewardPart G p n) -
      quittingRewardPart G p n / QuitProbability G p = _
  field_simp [ne_of_gt hquit]
  ring

/-- The paper's three-times-difference normalization gives the smaller
positive bound used in Lemma 4.3's application of Lemma 2.2. -/
private theorem simonPayoffScale_twoFifthsPositiveBound
    (G : QuittingGame) {M : ℝ} (hM : IsSimonPayoffScale G M) :
    IsPositiveQuittingPayoffDifferenceBound G (2 * M / 5) := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  refine ⟨by positivity, ?_, ?_⟩
  · intro A B n
    have h := hM.2.2 A B n
    nlinarith
  · intro A n
    have h := hM.2.1 A n
    nlinarith

/-- The Section 3 scale makes `ρ/18` smaller than the positive two-fifths
payoff bound. -/
private theorem section4_eta_le_twoFifths_scale {M ρ : ℝ}
    (hM : 1 ≤ M) (hρ : ρ ≤ 1) : ρ / 18 ≤ 2 * M / 5 := by
  nlinarith

private theorem quadraticStep_nonneg {B eta : ℝ} (hB : 0 < B) :
    0 ≤ eta ^ 2 / (2 * B) :=
  div_nonneg (sq_nonneg eta) (mul_nonneg (by norm_num) hB.le)

private theorem section4_card_error_le {N ρ : ℝ}
    (hN : 3 ≤ N) (hρ : 0 ≤ ρ) : ρ / (6 * N) ≤ ρ / 18 := by
  have hNpos : 0 < N := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hN hρ
  rw [div_le_iff₀ (mul_pos (by norm_num) hNpos)]
  field_simp
  nlinarith

private theorem section4_three_eta (ρ : ℝ) : 3 * (ρ / 18) = ρ / 6 := by
  ring

private theorem section4_case2_stageBeta_lower
    {χ ρ beta stage : ℝ}
    (hbeta : χ - ρ / 6 ≤ beta)
    (hstage : χ - 3 * (ρ / 18) ≤ beta →
      χ - 3 * (ρ / 18) ≤ stage) :
    χ - ρ / 6 ≤ stage := by
  rw [← section4_three_eta ρ] at hbeta ⊢
  exact hstage hbeta

private theorem section4_quadratic_le_linear {M ρ : ℝ}
    (hM : 1 ≤ M) (hρ0 : 0 ≤ ρ) (hρM : ρ ≤ M) :
    ρ ^ 2 / (500 * M) ≤ ρ / 500 := by
  have hsq : ρ ^ 2 ≤ ρ * M := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hρM hρ0
  calc
    ρ ^ 2 / (500 * M) ≤ (ρ * M) / (500 * M) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    _ = ρ / 500 := by field_simp

private theorem section4_quadratic_drift_le {M ρ : ℝ} (hM : 0 < M) :
    ρ ^ 2 / (500 * M) ≤
      (ρ / 18) ^ 2 / (2 * (2 * M / 5)) := by
  field_simp
  nlinarith [sq_nonneg ρ]

private theorem quittingOneStagePayoff_drift_ge_of_continuation_lt
    (G : QuittingGame) (p : QuitRow G) (n : G.Player)
    (x beta : Payoff G.Player) {target drift : ℝ}
    (hxbeta : x n < beta n)
    (hbetaDrift : beta n + drift ≤ QuittingOneStagePayoff G beta p n)
    (htarget : target ≤ drift) :
    x n + target ≤ QuittingOneStagePayoff G x p n := by
  have hq : 0 ≤ QuitProbability G p := (quitProbability_mem_Icc G p).1
  have hidentity :
      QuittingOneStagePayoff G x p n - x n =
        (QuittingOneStagePayoff G beta p n - beta n) +
          QuitProbability G p * (beta n - x n) := by
    simp only [QuittingOneStagePayoff]
    ring
  have hnonnegative : 0 ≤ QuitProbability G p * (beta n - x n) :=
    mul_nonneg hq (sub_nonneg.mpr hxbeta.le)
  linarith

/-- A near-certain quitter's singular `φ` penalty lies below its continuation
coordinate once the interpolation point remains inside the payoff box. -/
private theorem high_probability_phi_lt_continuation_of_interpolation_box
    (G : QuittingGame) (M d ρ lambda : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (z : EZeroTilde G) (x : Payoff G.Player)
    (hxFormula : x = (1 - lambda) • z.1.1 + lambda • Phi G M d z)
    (hxBox : InClosedPayoffBox M x) (j : G.Player)
    (hjHigh : 1 - ρ / (2 * (Fintype.card G.Player : ℝ) * M) ≤
      (z.1.2 j : ℝ)) :
    Phi G M d z j < z.1.1 j := by
  let N : ℝ := Fintype.card G.Player
  have hN : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hplayers
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hNM : M ≤ N * M := by nlinarith
  have hphi : Phi G M d z j < -N * M := by
    simpa only [N] using
      phi_lt_neg_card_mul_scale_of_high_probability
        G M d ρ hplayers hM hd hd1 hmotion z j hjHigh
  have hbeta : -N * M < z.1.1 j := by
    by_contra hnot
    have hbetaUpper : z.1.1 j ≤ -N * M := le_of_not_gt hnot
    have hleft :
        (1 - lambda) * z.1.1 j ≤ (1 - lambda) * (-N * M) :=
      mul_le_mul_of_nonneg_left hbetaUpper (by linarith)
    have hright : lambda * Phi G M d z j < lambda * (-N * M) :=
      mul_lt_mul_of_pos_left hphi hlambda0
    have hxCoord := congrFun hxFormula j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hxCoord
    have hxUpper : x j < -N * M := by
      rw [hxCoord]
      calc
        (1 - lambda) * z.1.1 j + lambda * Phi G M d z j <
            (1 - lambda) * (-N * M) + lambda * (-N * M) :=
          add_lt_add_of_le_of_lt hleft hright
        _ = -N * M := by ring
    have hxLower := (hxBox j).1
    linarith
  exact hphi.trans hbeta

private theorem section4_case2_conditional_lower
    {χ ρ stage conditional N : ℝ}
    (hstage : χ - ρ / 6 ≤ stage)
    (hdistance : |conditional - stage| ≤ ρ / (6 * N))
    (hN : 3 ≤ N) (hρ : 0 ≤ ρ) :
    χ - 2 * ρ / 9 ≤ conditional := by
  have hlower := (abs_le.mp hdistance).1
  have herror := section4_card_error_le hN hρ
  linarith

private theorem section4_case2_conclusion
    {M ρ N χ beta conditional x stage : ℝ}
    (hM : 1 ≤ M) (hρ : 0 < ρ) (hρM : ρ ≤ M) (hN : 3 ≤ N)
    (hbeta : χ - ρ / 6 ≤ beta)
    (hconditional : |conditional - beta| ≤ ρ / (6 * N))
    (hstage : |stage - conditional| ≤ ρ / 20) :
    (χ - ρ / 3 ≤ x → χ - ρ / 3 ≤ stage) ∧
      (x < χ - ρ / 3 → x + ρ ^ 2 / (500 * M) ≤ stage) := by
  have hconditionalLower : χ - 2 * ρ / 9 ≤ conditional :=
    section4_case2_conditional_lower hbeta hconditional hN hρ.le
  have hstageCloseLower : -(ρ / 20) ≤ stage - conditional :=
    (abs_le.mp hstage).1
  have hstageLower : χ - 49 * ρ / 180 ≤ stage := by
    linarith only [hconditionalLower, hstageCloseLower]
  have hquadratic : ρ ^ 2 / (500 * M) ≤ ρ / 500 :=
    section4_quadratic_le_linear hM hρ.le hρM
  constructor
  · intro _
    linarith only [hstageLower, hρ]
  · intro hx
    linarith only [hstageLower, hx, hquadratic, hρ]

/-- Lemma 4.3's common high-probability calculation, split into the paper's
rational Case 2 and irrational Case 3. -/
private theorem lemma4_3_high_probability_cases
    (G : QuittingGame) (M ρ ξ : ℝ)
    (hM : IsSimonPayoffScale G M)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hξ : 0 < ξ)
    (hN : 3 ≤ (Fintype.card G.Player : ℝ))
    (hNM : 3 ≤ (Fintype.card G.Player : ℝ) * M)
    (hxiError :
      ξ * (((Fintype.card G.Player : ℝ) + 1) * M) ≤ ρ / 20)
    (z : EZeroTilde G) (x : Payoff G.Player) (hxBox : InClosedPayoffBox M x)
    (dominant j : G.Player)
    (hpDominant : 1 - ξ < (z.1.2 dominant : ℝ))
    (hjHigh :
      1 - ρ / (2 * (Fintype.card G.Player : ℝ) * M) <
        (z.1.2 j : ℝ)) :
    (MinMaxQuit G j - ρ / 6 ≤ z.1.1 j →
      (MinMaxQuit G j - ρ / 3 ≤ x j →
        MinMaxQuit G j - ρ / 3 ≤
          QuittingOneStagePayoff G x z.1.2 j) ∧
        (x j < MinMaxQuit G j - ρ / 3 →
          x j + ρ ^ 2 / (500 * M) ≤
            QuittingOneStagePayoff G x z.1.2 j)) ∧
      (z.1.1 j < MinMaxQuit G j - ρ / 6 →
        x j < z.1.1 j →
          x j + ρ ^ 2 / (500 * M) ≤
            QuittingOneStagePayoff G x z.1.2 j) := by
  let p : QuitRow G := z.1.2
  let beta : Payoff G.Player := z.1.1
  let q : ℝ := QuitProbability G p
  let stageBeta : ℝ := QuittingOneStagePayoff G beta p j
  let stageX : ℝ := QuittingOneStagePayoff G x p j
  let conditionalReward : ℝ := quittingRewardPart G p j / q
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hjPos : 0 < (p j : ℝ) := by
    have hthresholdNonneg :
        0 ≤ 1 - ρ / (2 * (Fintype.card G.Player : ℝ) * M) := by
      have hfraction :
          ρ / (2 * (Fintype.card G.Player : ℝ) * M) ≤ 1 := by
        rw [div_le_one (by positivity :
          0 < 2 * (Fintype.card G.Player : ℝ) * M)]
        nlinarith [hmotion.2.2.1, hNM]
      linarith
    simpa only [p] using hthresholdNonneg.trans_lt hjHigh
  have hqMem : q ∈ Set.Icc (0 : ℝ) 1 := quitProbability_mem_Icc G p
  have hqPos : 0 < q := hjPos.trans_le (quitProbability_apply_le G p j)
  have hqHigh : 1 - ξ < q := by
    have hdominant := quitProbability_apply_le G p dominant
    have hpDominant' : 1 - ξ < (p dominant : ℝ) := by
      simpa only [p] using hpDominant
    exact hpDominant'.trans_le hdominant
  have hstageBetaForced : stageBeta = ForcedQuitPayoff G p j := by
    simpa only [stageBeta, beta, p] using
      oneStagePayoff_eq_forcedQuit_of_positive G z.1.1 z.1.2
        z.2.1 z.2.2 j (by simpa only [p] using hjPos)
  have hconditionalDistance :
      |conditionalReward - stageBeta| ≤
        (M / 3) * (q - (p j : ℝ)) / q := by
    rw [hstageBetaForced]
    simpa only [conditionalReward, q] using
      abs_quittingRewardPart_div_sub_forcedQuitPayoff_le G
        (D := M / 3) (fun A B n => by
          have h := hM.2.2 A B n
          nlinarith) p j hqPos
  have hconditionalSmall :
      |conditionalReward - stageBeta| ≤
        ρ / (6 * (Fintype.card G.Player : ℝ)) := by
    let N : ℝ := Fintype.card G.Player
    have hqMinus : q - (p j : ℝ) ≤ q * (1 - (p j : ℝ)) := by
      have hscaled := mul_le_mul_of_nonneg_left hqMem.2 (p j).property.1
      nlinarith
    have hjGap : 1 - (p j : ℝ) < ρ / (2 * N * M) := by
      dsimp only [N]
      have hjHigh' :
          1 - ρ / (2 * (Fintype.card G.Player : ℝ) * M) <
            (p j : ℝ) := by
        simpa only [p] using hjHigh
      linarith only [hjHigh']
    have hscaledGap :
        (M / 3) * (q - (p j : ℝ)) ≤ q * (ρ / (6 * N)) := by
      have hfirst := mul_le_mul_of_nonneg_left hqMinus
        (show 0 ≤ M / 3 by positivity)
      have hsecond := mul_lt_mul_of_pos_left hjGap
        (show 0 < q * (M / 3) by positivity)
      apply le_of_lt
      calc
        (M / 3) * (q - (p j : ℝ)) ≤
            (M / 3) * (q * (1 - (p j : ℝ))) := hfirst
        _ = (q * (M / 3)) * (1 - (p j : ℝ)) := by ring
        _ < (q * (M / 3)) * (ρ / (2 * N * M)) := hsecond
        _ = (M / 3) * (q * (ρ / (2 * N * M))) := by ring
        _ = q * (ρ / (6 * N)) := by field_simp; ring
    apply hconditionalDistance.trans
    rw [div_le_iff₀ hqPos]
    simpa only [N, mul_comm] using hscaledGap
  have hconditionalAbs : |conditionalReward| ≤ M / 3 := by
    dsimp only [conditionalReward]
    rw [abs_div, abs_of_pos hqPos, div_le_iff₀ hqPos]
    simpa only [q] using
      abs_quittingRewardPart_le G p j (fun A => hM.2.1 A j)
  have hstageXClose : |stageX - conditionalReward| ≤ ρ / 20 := by
    have hcoordinateDistance :
        |x j - conditionalReward| ≤
          ((Fintype.card G.Player : ℝ) + 1) * M := by
      calc
        |x j - conditionalReward| ≤ |x j| + |conditionalReward| := abs_sub _ _
        _ ≤ M + M / 3 := add_le_add (abs_le.mpr (hxBox j)) hconditionalAbs
        _ ≤ ((Fintype.card G.Player : ℝ) + 1) * M := by
          nlinarith only [hN, hMpos.le]
    have hsurvival : 0 ≤ 1 - q := sub_nonneg.mpr hqMem.2
    have hsurvivalLe : 1 - q ≤ ξ := by linarith only [hqHigh]
    have hidentity : stageX - conditionalReward =
        (1 - q) * (x j - conditionalReward) := by
      simpa only [stageX, conditionalReward, q, p] using
        quittingOneStagePayoff_sub_conditionalReward G x z.1.2 j hqPos
    rw [hidentity, abs_mul, abs_of_nonneg hsurvival]
    exact (mul_le_mul hsurvivalLe hcoordinateDistance
      (abs_nonneg _) hξ.le).trans hxiError
  have hB : IsPositiveQuittingPayoffDifferenceBound G (2 * M / 5) :=
    simonPayoffScale_twoFifthsPositiveBound G hM
  have hetaPos : 0 < ρ / 18 := div_pos hmotion.2.1 (by norm_num)
  have hetaB : ρ / 18 ≤ 2 * M / 5 :=
    section4_eta_le_twoFifths_scale hM.1 hmotion.2.2.1
  have hdeltaNonneg : 0 ≤ (ρ / 18) ^ 2 / (2 * (2 * M / 5)) :=
    quadraticStep_nonneg (eta := ρ / 18) hB.1
  have hstageStep :
      (fun who => QuittingOneStagePayoff G beta p who) ∈
        FRow G ((ρ / 18) ^ 2 / (2 * (2 * M / 5))) beta := by
    refine ⟨p, EpsilonRow.mono G hdeltaNonneg beta ?_, rfl⟩
    simpa only [beta, p] using z.2.1
  have hlemma6 := lemma6_quantitative_of_positiveBound G hB hnormal
    hetaPos hetaB hstageStep j
  constructor
  · intro hbetaRational
    have hstageBetaLower : MinMaxQuit G j - ρ / 6 ≤ stageBeta := by
      apply section4_case2_stageBeta_lower
        (by simpa only [beta] using hbetaRational)
      intro hrationalEta
      simpa only [stageBeta] using hlemma6.1 hrationalEta
    simpa only [stageX, p] using
      section4_case2_conclusion hM.1 hmotion.2.1
        (hmotion.2.2.1.trans hM.1) hN hstageBetaLower
        hconditionalSmall hstageXClose
  · intro hbetaIrrational hxbeta
    have hstageBetaDrift :
        beta j + (ρ / 18) ^ 2 / (2 * (2 * M / 5)) ≤ stageBeta := by
      have hbetaIrrationalEta :
          beta j < MinMaxQuit G j - 3 * (ρ / 18) := by
        rw [section4_three_eta]
        simpa only [beta] using hbetaIrrational
      simpa only [beta, stageBeta] using
        hlemma6.2 hbetaIrrationalEta
    apply quittingOneStagePayoff_drift_ge_of_continuation_lt
      G p j x beta hxbeta hstageBetaDrift
    exact section4_quadratic_drift_le hMpos

/-- In Lemma 4.3's low-own-hazard case, one dominant opponent makes the
stationary continuation payoff an effective min-max cap. -/
private theorem lowHazard_minMax_le_stagePayoff_add
    (G : QuittingGame) (M ρ ξ : ℝ)
    (hM : IsSimonPayoffScale G M)
    (hpayoffBound : IsQuittingPayoffDifferenceBound G M)
    (hρ0 : 0 < ρ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ < 1)
    (beta x : Payoff G.Player) (p : QuitRow G) (j : G.Player)
    (hp : p ∈ EpsilonRow G 0 beta)
    (hjLt : (p j : ℝ) < 1)
    (hqOtherHigh : 1 - ξ < QuitProbability G (p.replace G j 0))
    (hbetaBound : |beta j| ≤ (Fintype.card G.Player : ℝ) * M)
    (hxBound : |x j| ≤ M)
    (hxiError : ξ * (((Fintype.card G.Player : ℝ) + 1) * M) ≤ ρ / 20) :
    MinMaxQuit G j ≤ QuittingOneStagePayoff G x p j + ρ / 10 := by
  let pZero : QuitRow G := p.replace G j 0
  let qOther : ℝ := QuitProbability G pZero
  let conditionalReward : ℝ := quittingRewardPart G pZero j / qOther
  let stageBeta : ℝ := QuittingOneStagePayoff G beta p j
  let stageX : ℝ := QuittingOneStagePayoff G x p j
  have hqOtherHigh' : 1 - ξ < qOther := by
    simpa only [qOther, pZero] using hqOtherHigh
  have hqOtherPos : 0 < qOther := by
    nlinarith
  have hqOtherMem : qOther ∈ Set.Icc (0 : ℝ) 1 :=
    quitProbability_mem_Icc G pZero
  have hstageBetaContinue :
      stageBeta = ForcedContinuePayoff G beta p j := by
    simpa only [stageBeta] using
      oneStagePayoff_eq_forcedContinue_of_lt_one G beta p hp j hjLt
  have hrewardAbs : |quittingRewardPart G pZero j| ≤ M / 3 * qOther := by
    simpa only [qOther] using
      abs_quittingRewardPart_le G pZero j (fun A => hM.2.1 A j)
  have hconditionalAbs : |conditionalReward| ≤ M / 3 := by
    dsimp only [conditionalReward]
    rw [abs_div, abs_of_pos hqOtherPos]
    rw [div_le_iff₀ hqOtherPos]
    simpa only [mul_comm] using hrewardAbs
  have hrewardEq :
      quittingRewardPart G pZero j = qOther * conditionalReward := by
    dsimp only [conditionalReward]
    field_simp [ne_of_gt hqOtherPos]
  have hstageBetaFormula :
      stageBeta = (1 - qOther) * beta j + qOther * conditionalReward := by
    rw [hstageBetaContinue]
    change (1 - QuitProbability G pZero) * beta j +
        quittingRewardPart G pZero j = _
    rw [hrewardEq]
  have hforcedLe : ForcedQuitPayoff G p j ≤ stageBeta := by
    rw [hstageBetaContinue]
    have hraw := hp.2 j hjLt
    simpa only [sub_zero] using hraw
  have hconditionalDistance :
      |conditionalReward - stageBeta| ≤ ρ / 20 := by
    have hcoordinateDistance :
        |conditionalReward - beta j| ≤
          ((Fintype.card G.Player : ℝ) + 1) * M := by
      calc
        |conditionalReward - beta j| ≤
            |conditionalReward| + |beta j| := abs_sub _ _
        _ ≤ M / 3 + (Fintype.card G.Player : ℝ) * M :=
          add_le_add hconditionalAbs hbetaBound
        _ ≤ ((Fintype.card G.Player : ℝ) + 1) * M := by
          nlinarith [hM.1]
    have hsurvivalLe : 1 - qOther ≤ ξ := by
      linarith
    have hidentity :
        conditionalReward - stageBeta =
          (1 - qOther) * (conditionalReward - beta j) := by
      rw [hstageBetaFormula]
      ring
    rw [hidentity, abs_mul, abs_of_nonneg (by linarith [hqOtherMem.2])]
    exact (mul_le_mul hsurvivalLe hcoordinateDistance
      (abs_nonneg _) hξ0).trans hxiError
  have hminmaxCap :
      MinMaxQuit G j ≤ max (ForcedQuitPayoff G p j) conditionalReward := by
    simpa only [pZero, qOther, conditionalReward] using
      minMaxQuit_le_max_forcedQuit_stationaryContinue
        G (hpayoffBound.toPositive G) p j
          (by simpa only [qOther, pZero] using hqOtherPos)
  have hminmaxBeta : MinMaxQuit G j ≤ stageBeta + ρ / 20 := by
    apply hminmaxCap.trans
    apply max_le
    · linarith
    · linarith [le_of_abs_le hconditionalDistance]
  have hstageDistance : |stageBeta - stageX| ≤ ρ / 20 := by
    have hbetaX :
        |beta j - x j| ≤ ((Fintype.card G.Player : ℝ) + 1) * M := by
      calc
        |beta j - x j| ≤ |beta j| + |x j| := abs_sub _ _
        _ ≤ (Fintype.card G.Player : ℝ) * M + M :=
          add_le_add hbetaBound hxBound
        _ = ((Fintype.card G.Player : ℝ) + 1) * M := by ring
    have hsurvivalNonneg : 0 ≤ 1 - QuitProbability G p := by
      linarith [(quitProbability_mem_Icc G p).2]
    have hsurvivalLe : 1 - QuitProbability G p ≤ ξ := by
      have hqMonotone := quitProbability_replace_zero_le G p j
      change qOther ≤ QuitProbability G p at hqMonotone
      linarith
    rw [show stageBeta - stageX =
        (1 - QuitProbability G p) * (beta j - x j) by
      exact quittingOneStagePayoff_sub G beta x p j]
    rw [abs_mul, abs_of_nonneg hsurvivalNonneg]
    exact (mul_le_mul hsurvivalLe hbetaX
      (abs_nonneg _) hξ0).trans hxiError
  have hupper := le_of_abs_le hstageDistance
  linarith

/--
Lemma 4.3's coordinate drift statement for `z = f(x,p)`, under the standing
Section 3--4 choices used in its proof.  The deformed graph coordinate is the
separate vector `y = λx + (1-λ)z`.  The hypotheses are not optional: the paper
uses normality, exclusion of the two simple equilibrium classes, the common
motion parameter, the constants `ξ,R`, the accuracy restriction `ε < ρ/3`, and
the cutoff supported in the radius `ω` defined in Section 4.3.  The proof uses
the paper's three-way split according to the player's quitting probability and
continuation coordinate, with Lemma 2.2 supplying the strict coordinate
increase in the low-rationality case.
-/
theorem lemma4_3 (G : QuittingGame) (M d ρ ξ R ε : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (_hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (_hinstant : ¬HasInstantApproximateEquilibria G)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval)
    (hcutoff : IsSection4Cutoff G R (Section4Omega G M d ρ ξ R ε) cutoff)
    (hε : 0 < ε) (hερ : ε < ρ / 3)
    (a : Payoff G.Player)
    (_haC : a ∈ TruncatedW G R)
    (hcutoff0 : 0 < (cutoff a : ℝ)) (hcutoff1 : (cutoff a : ℝ) < 1)
    (hxbox : ∀ j, -M ≤ Section4X G inverse cutoff a j ∧
      Section4X G inverse cutoff a j ≤ M) :
    ∀ j,
      (MinMaxQuit G j - ρ / 3 ≤ Section4X G inverse cutoff a j →
        MinMaxQuit G j - ρ / 3 ≤ Section4Z G inverse cutoff a j) ∧
      (Section4X G inverse cutoff a j < MinMaxQuit G j - ρ / 3 →
        Section4X G inverse cutoff a j + ρ ^ 2 / (500 * M) ≤
          Section4Z G inverse cutoff a j) := by
  classical
  let z : EZeroTilde G := inverse.inv a
  let lambda : ℝ := cutoff a
  let x : Payoff G.Player := Section4X G inverse cutoff a
  have hphi : Phi G M d z = a := inverse.rightInverse a
  obtain ⟨hξ, hξ1, hR⟩ := section3Constants_radius_bound
    G M d ρ ξ R hplayers hM hd hd1 hmotion hconstants
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hN : 3 ≤ (Fintype.card G.Player : ℝ) := by exact_mod_cast hplayers
  have hNM : 3 ≤ (Fintype.card G.Player : ℝ) * M := by
    nlinarith [mul_le_mul hN hM.1 (by norm_num)
      (by linarith : 0 ≤ (Fintype.card G.Player : ℝ))]
  have hRpos : 0 < R := by linarith
  have hsolo : ∀ j, -(R + 1) < SoloPayoff G j := by
    intro j
    have hj := hM.2.1 ⟨{j}, Finset.singleton_nonempty j⟩ j
    change |SoloPayoff G j| ≤ M / 3 at hj
    have hRM : M / 3 < R + 1 := by nlinarith [hR, hNM]
    linarith [neg_le_of_abs_le hj]
  have hD : (LowerBoundary G R).Nonempty :=
    ⟨lowerCubeCorner G R,
      lowerCubeCorner_mem_lowerBoundary G R (by linarith) hsolo⟩
  have hω := section4Omega_mem_Ioc G M d ρ ξ R ε hplayers hM hd hd1
    hmotion hconstants hε hερ
  obtain ⟨large, hlarge⟩ := exists_large_coordinate_of_cutoff_pos G
    (by linarith) hω.2 hD cutoff hcutoff.2.2.1 a hcutoff0
  have hxFormula : x =
      (1 - (cutoff a : ℝ)) • z.1.1 + (cutoff a : ℝ) • a := by
    dsimp only [x, z, Section4X]
    abel
  have hnegative : ∃ k, a k < -R := by
    rcases (lt_abs.mp hlarge) with hpos | hneg
    · have hpositive := lemma3_4_positive_coordinate G M d ρ ξ R
        hplayers hM hd hd1 hmotion hconstants z large (by
          rw [hphi]
          exact hpos)
      have hxLarge := congrFun hxFormula large
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hxLarge
      have hxUpper := (hxbox large).2
      have hbetaLarge : M < z.1.1 large := by
        nlinarith [hpositive.1]
      have haLarge : M < a large := by
        nlinarith
      have hlambda0 : 0 < (cutoff a : ℝ) := hcutoff0
      have hlambda1 : (cutoff a : ℝ) < 1 := hcutoff1
      exfalso
      nlinarith
    · exact ⟨large, by linarith⟩
  obtain ⟨dominant, hadominant⟩ := hnegative
  have hpDominant : 1 - ξ < (z.1.2 dominant : ℝ) := by
    apply lemma3_4_negative_coordinate_probability_gt_one_sub_xi
      G M d ρ ξ R hplayers hM hd hd1 hmotion hconstants z dominant
    rw [hphi]
    exact hadominant
  let threshold : ℝ :=
    1 - ρ / (2 * (Fintype.card G.Player : ℝ) * M)
  have hxBox' : InClosedPayoffBox M x := by
    intro j
    simpa only [x] using hxbox j
  have hxPhi : x = (1 - (cutoff a : ℝ)) • z.1.1 +
      (cutoff a : ℝ) • Phi G M d z := by
    rw [hphi]
    exact hxFormula
  have hbetaLow : ∀ j, (z.1.2 j : ℝ) ≤ threshold →
      |z.1.1 j| ≤ (Fintype.card G.Player : ℝ) * M := by
    intro j hj
    by_contra hnot
    obtain ⟨maximal, hmaximal⟩ := exists_maximalQuitter G z.1.2
    have hout := lowProbability_largeContinuation_not_box
      G M d ρ ξ R hplayers hM hd hd1 hmotion hconstants
      z dominant maximal j hmaximal (by rw [hphi]; exact hadominant)
      (by simpa only [threshold] using hj) (lt_of_not_ge hnot)
      (cutoff a) hcutoff0 hcutoff1 x hxPhi
    exact hout hxBox'
  have hxiThreshold :
      ξ ≤ ρ / (2 * (Fintype.card G.Player : ℝ) * M) := by
    let base : ℝ := ρ / (2 * (Fintype.card G.Player : ℝ) * M)
    have hbasePos : 0 < base := by
      dsimp only [base]
      apply div_pos hmotion.2.1
      exact mul_pos
        (mul_pos (by norm_num) (by exact_mod_cast Fintype.card_pos)) hMpos
    have hbaseOne : base ≤ 1 := by
      dsimp only [base]
      rw [div_le_one (by
        exact mul_pos
          (mul_pos (by norm_num) (by exact_mod_cast Fintype.card_pos)) hMpos)]
      nlinarith [hmotion.2.2.1, hNM]
    have hpower : base ^ Fintype.card G.Player ≤ base := by
      exact pow_le_of_le_one hbasePos.le hbaseOne
        (Nat.ne_of_gt Fintype.card_pos)
    have hraw := hconstants.2.1
    change ξ ≤ (1 / 20 : ℝ) * base ^ Fintype.card G.Player at hraw
    change ξ ≤ base
    nlinarith
  have hxiError :
      ξ * (((Fintype.card G.Player : ℝ) + 1) * M) ≤ ρ / 20 := by
    let N : ℝ := Fintype.card G.Player
    let base : ℝ := ρ / (2 * N * M)
    have hNpos : 0 < N := by dsimp only [N]; linarith
    have hbasePos : 0 < base := by
      dsimp only [base, N]
      apply div_pos hmotion.2.1
      exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast Fintype.card_pos))
        hMpos
    have hbaseOne : base ≤ 1 := by
      dsimp only [base]
      rw [div_le_one (by exact mul_pos (mul_pos (by norm_num) hNpos) hMpos)]
      nlinarith [hmotion.2.2.1, hNM]
    have hcard : 1 ≤ Fintype.card G.Player := Fintype.card_pos
    have hpower : base ^ Fintype.card G.Player ≤ base := by
      exact pow_le_of_le_one hbasePos.le hbaseOne (Nat.ne_of_gt hcard)
    have hxiBase : ξ ≤ base / 20 := by
      have hraw := hconstants.2.1
      change ξ ≤ (1 / 20 : ℝ) * base ^ Fintype.card G.Player at hraw
      nlinarith
    have hscale := mul_le_mul_of_nonneg_right hxiBase
      (show 0 ≤ (N + 1) * M by positivity)
    calc
      ξ * (((Fintype.card G.Player : ℝ) + 1) * M) ≤
          (base / 20) * ((N + 1) * M) := by simpa only [N] using hscale
      _ = ρ * (N + 1) / (40 * N) := by
        dsimp only [base]
        field_simp
        ring
      _ ≤ ρ / 20 := by
        rw [div_le_iff₀ (by positivity : 0 < 40 * N)]
        nlinarith [mul_nonneg hmotion.2.1.le (by linarith : 0 ≤ N - 1)]
  have hpayoffBound : IsQuittingPayoffDifferenceBound G M := by
    refine ⟨hM.1, ?_, ?_⟩
    · intro A B j
      have h := hM.2.2 A B j
      nlinarith
    · intro A j
      have h := hM.2.1 A j
      nlinarith
  intro j
  let p : QuitRow G := z.1.2
  let beta : Payoff G.Player := z.1.1
  let pZero : QuitRow G := p.replace G j 0
  let qOther : ℝ := QuitProbability G pZero
  let stageX : ℝ := QuittingOneStagePayoff G x p j
  have hsectionZ : Section4Z G inverse cutoff a j = stageX := by
    rfl
  by_cases hjLow : (p j : ℝ) ≤ threshold
  · have hthresholdLt : threshold < 1 := by
      dsimp only [threshold]
      have hdenom : 0 < 2 * (Fintype.card G.Player : ℝ) * M := by
        exact mul_pos
          (mul_pos (by norm_num) (by exact_mod_cast Fintype.card_pos)) hMpos
      have hquotient : 0 < ρ / (2 * (Fintype.card G.Player : ℝ) * M) :=
        div_pos hmotion.2.1 hdenom
      linarith
    have hjLt : (p j : ℝ) < 1 := hjLow.trans_lt hthresholdLt
    have hdominantNe : dominant ≠ j := by
      intro heq
      subst dominant
      have hdominantLow : (z.1.2 j : ℝ) ≤ threshold := by
        simpa only [p] using hjLow
      have hraw := hpDominant.trans_le hdominantLow
      dsimp only [threshold] at hraw
      nlinarith
    have hpZeroDominant : (pZero dominant : ℝ) = (p dominant : ℝ) := by
      simp [pZero, QuitRow.replace, hdominantNe]
    have hqOtherHigh : 1 - ξ < qOther := by
      have hcoord := quitProbability_apply_le G pZero dominant
      rw [hpZeroDominant] at hcoord
      have hdominant : 1 - ξ < (p dominant : ℝ) := by
        simpa only [p] using hpDominant
      exact hdominant.trans_le hcoord
    have hbetaBound : |beta j| ≤ (Fintype.card G.Player : ℝ) * M := by
      simpa only [beta, p] using hbetaLow j hjLow
    have hminmaxX : MinMaxQuit G j ≤ stageX + ρ / 10 := by
      apply lowHazard_minMax_le_stagePayoff_add G M ρ ξ hM hpayoffBound
        hmotion.2.1 hξ.le hξ1 beta x p j
      · simpa only [beta, p] using z.2.1
      · exact hjLt
      · simpa only [qOther, pZero] using hqOtherHigh
      · exact hbetaBound
      · exact abs_le.mpr (hxBox' j)
      · exact hxiError
    have hquadratic : ρ ^ 2 / (500 * M) ≤ ρ / 500 := by
      have hρM : ρ ≤ M := hmotion.2.2.1.trans hM.1
      have hsq : ρ ^ 2 ≤ ρ * M := by
        simpa only [pow_two] using
          mul_le_mul_of_nonneg_left hρM hmotion.2.1.le
      calc
        ρ ^ 2 / (500 * M) ≤ (ρ * M) / (500 * M) :=
          div_le_div_of_nonneg_right hsq (by positivity)
        _ = ρ / 500 := by field_simp
    rw [hsectionZ]
    constructor
    · intro _hxRational
      calc
        MinMaxQuit G j - ρ / 3 ≤ MinMaxQuit G j - ρ / 10 := by
          linarith [hmotion.2.1]
        _ ≤ stageX := by linarith [hminmaxX]
    · intro hxIrrational
      calc
        x j + ρ ^ 2 / (500 * M) ≤ x j + ρ / 500 :=
          by simpa only [add_comm] using add_le_add_left hquadratic (x j)
        _ ≤ stageX := by
          linarith [hminmaxX, hmotion.2.1]
  · have hjHigh :
        1 - ρ / (2 * (Fintype.card G.Player : ℝ) * M) <
          (z.1.2 j : ℝ) := by
      simpa only [threshold, p] using lt_of_not_ge hjLow
    have hhighCases := lemma4_3_high_probability_cases
      G M ρ ξ hM hnormal hmotion hξ hN hNM hxiError
      z x hxBox' dominant j hpDominant hjHigh
    by_cases hbetaRational : MinMaxQuit G j - ρ / 6 ≤ z.1.1 j
    · rw [hsectionZ]
      exact hhighCases.1 hbetaRational
    · have hphiBeta : Phi G M d z j < z.1.1 j :=
        high_probability_phi_lt_continuation_of_interpolation_box
          G M d ρ (cutoff a : ℝ) hplayers hM hd hd1 hmotion
          hcutoff0 hcutoff1 z x hxPhi hxBox' j hjHigh.le
      have hxBeta : x j < z.1.1 j := by
        have hxCoord := congrFun hxPhi j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hxCoord
        have hnegative :
            (cutoff a : ℝ) * (Phi G M d z j - z.1.1 j) < 0 :=
          mul_neg_of_pos_of_neg hcutoff0 (sub_neg.mpr hphiBeta)
        rw [hxCoord]
        nlinarith
      rw [hsectionZ]
      have hdrift := hhighCases.2 (lt_of_not_ge hbetaRational) hxBeta
      have hstepNonneg : 0 ≤ ρ ^ 2 / (500 * M) := by positivity
      constructor
      · intro hxRational
        exact hxRational.trans
          ((le_add_of_nonneg_right hstepNonneg).trans hdrift)
      · intro _
        exact hdrift

/-!
The proof of Lemma 4.4 uses the local inference that `pⱼ = 0` implies
`βⱼ ≤ φ(β,p)ⱼ`.  The displayed definition of `φ` and exact one-stage
equilibrium do not imply it: the following two-player zero-payoff row is an
explicit counterexample.  This refutes that proof step, not Lemma 4.4 under
all of its standing Section 3 assumptions.
-/
namespace Lemma44ZeroQuitterInference

abbrev game : QuittingGame where
  Player := Bool
  reward := fun _ _ => 0

abbrev beta : Payoff game.Player := fun j => if j then 0 else 40

abbrev row : QuitRow game := fun j => if j then ⟨1 / 2, by norm_num⟩ else 0

private theorem univ_bool : (Finset.univ : Finset Bool) = {false, true} := by
  decide

private theorem quitProbability_eq : QuitProbability game row = 1 / 2 := by
  rw [QuitProbability, univ_bool]
  norm_num [row]

private theorem oneStagePayoff_eq (n : game.Player) :
    QuittingOneStagePayoff game beta row n = (1 / 2) * beta n := by
  fin_cases n <;>
    norm_num [QuittingOneStagePayoff, quitProbability_eq, game, beta]

private theorem forcedQuitPayoff_eq (n : game.Player) :
    ForcedQuitPayoff game row n = 0 := by
  simp [ForcedQuitPayoff, QuittingOneStagePayoff, game]

private theorem forcedContinuePayoff_eq (n : game.Player) :
    ForcedContinuePayoff game beta row n = if n then 0 else 20 := by
  cases n
  · rw [ForcedContinuePayoff, QuittingOneStagePayoff, QuitProbability, univ_bool]
    simp [CoalitionProbability, QuitRow.replace, row, beta, game]
    norm_num
  ·
    norm_num [ForcedContinuePayoff, QuittingOneStagePayoff, QuitProbability,
      CoalitionProbability, QuitRow.replace, row, beta, game]

private theorem pair_mem : (beta, row) ∈ EZeroTilde game := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro n hn
    rw [forcedQuitPayoff_eq, forcedContinuePayoff_eq]
    cases n <;> simp [row] at hn ⊢
  · intro n _hn
    rw [forcedQuitPayoff_eq, forcedContinuePayoff_eq]
    fin_cases n <;> norm_num
  · rw [quitProbability_eq]
    norm_num

abbrev point : EZeroTilde game := ⟨(beta, row), pair_mem⟩

private theorem phi_false_eq : Phi game 1 1 point false = 41 / 2 := by
  rw [Phi, oneStagePayoff_eq, univ_bool]
  norm_num [point, row, beta, game]

private theorem phi_true_eq : Phi game 1 1 point true = -20 := by
  have hcard : Fintype.card game.Player = 2 := Fintype.card_bool
  rw [Phi, oneStagePayoff_eq, univ_bool]
  norm_num [point, row, beta, game, hcard]

/-- The zero-quitting-coordinate inference used in the printed proof of
Lemma 4.4 is false without the remaining standing assumptions. -/
theorem zero_quitter_inference_fails :
    (point.1.2 false : ℝ) = 0 ∧
      ¬ point.1.1 false ≤ Phi game 1 1 point false := by
  rw [phi_false_eq]
  norm_num [point, row, beta]

private theorem phi_mem_truncatedW : Phi game 1 1 point ∈ TruncatedW game 20 := by
  constructor
  · refine ⟨true, ?_⟩
    rw [phi_true_eq]
    norm_num [SoloPayoff, game]
  · intro j
    cases j
    · rw [phi_false_eq]
      norm_num
    · rw [phi_true_eq]
      norm_num

/-- Even with `φ(β,p) ∈ C`, the displayed conclusion of Lemma 4.4 is
false if the preceding Section 3 assumptions are omitted. -/
theorem boundedness_conclusion_fails_without_standing_assumptions :
    Phi game 1 1 point ∈ TruncatedW game 20 ∧
      ¬ ((∀ j, -(20 : ℝ) / 2 ≤ point.1.1 j ∧
          point.1.1 j ≤ 20 + 1) ∧
        ∀ j, 0 < (point.1.2 j : ℝ) → |point.1.1 j| ≤ 20 / 2) := by
  refine ⟨phi_mem_truncatedW, ?_⟩
  rintro ⟨hbeta, _hquit⟩
  have := (hbeta false).2
  norm_num [point, beta] at this

end Lemma44ZeroQuitterInference

/-- The singular penalty supplies the supported-coordinate half of Lemma 4.4
without using the printed (false in isolation) zero-quitter inference. -/
private theorem supportedContinuation_abs_le_half_radius
    (G : QuittingGame) (M d ρ ξ R : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (z : EZeroTilde G)
    (ha : Phi G M d z ∈ TruncatedW G R) :
    ∀ j, 0 < (z.1.2 j : ℝ) → |z.1.1 j| ≤ R / 2 := by
  classical
  let N : ℝ := Fintype.card G.Player
  let beta := z.1.1
  let p := z.1.2
  obtain ⟨_, _, hR⟩ := section3Constants_radius_bound G M d ρ ξ R
    hplayers hM hd hd1 hmotion hconstants
  have hN : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hplayers
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hRpos : 0 < R := by nlinarith
  intro j hpj
  by_contra hnot
  have hlarge : R / 2 < |beta j| := by
    simpa only [beta] using lt_of_not_ge hnot
  obtain ⟨m, hm⟩ := exists_maximalQuitter G p
  have hpm : 0 < (p m : ℝ) := hpj.trans_le (hm j)
  have hpmLt : (p m : ℝ) < 1 :=
    (quitProbability_apply_le G p m).trans_lt z.2.2
  let tau : ℝ := 1 - (p m : ℝ)
  let floor : ℝ := tau ^ (Fintype.card G.Player - 1)
  let survival : ℝ := 1 - OthersQuitProbability G p j
  have htauPos : 0 < tau := by dsimp only [tau]; linarith
  have htauOne : tau ≤ 1 := by
    dsimp only [tau]
    linarith [(p m).property.1]
  have hfloorPos : 0 < floor := pow_pos htauPos _
  have hsurvivalLower : floor ≤ survival := by
    simpa only [floor, survival] using
      maximalQuitter_opponentSurvival_lower_at G p m j hm
  have hquit := z.2.1.1 j hpj
  have hcontinue := z.2.1.2 j ((hm j).trans_lt hpmLt)
  have heq : ForcedQuitPayoff G p j = ForcedContinuePayoff G beta p j :=
    le_antisymm (by simpa only [sub_zero] using hcontinue)
      (by simpa only [sub_zero] using hquit)
  have hidentity := forcedContinue_sub_solo G p beta j
  rw [← heq] at hidentity
  have hforced := abs_forcedQuitPayoff_le_scale G M hM p j
  have hsolo := abs_forcedContinue_solo_le_scale G M hM p j
  have hscaledDistance :
      survival * |beta j - SoloPayoff G j| ≤ 2 * M / 3 := by
    have hsurvivalNonneg : 0 ≤ survival := by
      dsimp only [survival]
      rw [othersQuitProbability_eq_replace_zero]
      linarith [quitProbability_mem_Icc G (p.replace G j 0) |>.2]
    rw [← abs_of_nonneg hsurvivalNonneg, ← abs_mul, ← hidentity]
    exact (abs_sub _ _).trans (by nlinarith)
  have hsoloPay := hM.2.1 ⟨{j}, Finset.singleton_nonempty j⟩ j
  have hdistance : R / 3 < |beta j - SoloPayoff G j| := by
    have htriangle : |beta j| ≤
        |beta j - SoloPayoff G j| + |SoloPayoff G j| := by
      calc
        |beta j| = |(beta j - SoloPayoff G j) + SoloPayoff G j| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    change |SoloPayoff G j| ≤ M / 3 at hsoloPay
    nlinarith
  have hfloorDistance :
      floor * |beta j - SoloPayoff G j| ≤
        survival * |beta j - SoloPayoff G j| :=
    mul_le_mul_of_nonneg_right hsurvivalLower (abs_nonneg _)
  have hfloorR : floor * R < 2 * M := by
    nlinarith [hfloorDistance]
  have htenNFloor : 10 * N * floor < 2 := by
    have hscaledR := mul_le_mul_of_nonneg_left hR hfloorPos.le
    have hwithM : (10 * N * floor) * M < 2 * M := by
      nlinarith [hscaledR]
    exact lt_of_mul_lt_mul_right hwithM hMpos.le
  have hfloorSmall : floor < 1 / 15 := by
    have hfifteen : 15 ≤ 5 * N := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_right hfifteen hfloorPos.le
    nlinarith
  have hbern : 1 - ((Fintype.card G.Player - 1 : ℕ) : ℝ) * (p m : ℝ) ≤
      floor := by
    have hraw := one_add_mul_le_pow (a := -(p m : ℝ))
      (n := Fintype.card G.Player - 1) (by linarith [(p m).property.2])
    simpa only [floor, tau, sub_eq_add_neg, mul_neg] using hraw
  have hpred : ((Fintype.card G.Player - 1 : ℕ) : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast Nat.sub_le (Fintype.card G.Player) 1
  have hpredMul :
      ((Fintype.card G.Player - 1 : ℕ) : ℝ) * (p m : ℝ) ≤
        N * (p m : ℝ) :=
    mul_le_mul_of_nonneg_right hpred (p m).property.1
  have hNpm : 14 / 15 < N * (p m : ℝ) := by nlinarith
  let den : ℝ := tau ^ Fintype.card G.Player
  have hdenPos : 0 < den := pow_pos htauPos _
  have hdenEq : den = tau * floor := by
    have hcard : Fintype.card G.Player - 1 + 1 = Fintype.card G.Player := by
      exact Nat.sub_add_cancel Fintype.card_pos
    calc
      den = tau ^ (Fintype.card G.Player - 1 + 1) := by rw [hcard]
      _ = tau ^ (Fintype.card G.Player - 1) * tau := pow_succ _ _
      _ = tau * floor := by simp only [floor, mul_comm]
  have hdenLe : den ≤ floor := by
    rw [hdenEq]
    exact mul_le_of_le_one_left hfloorPos.le htauOne
  have hdenR : den * R < 2 * M := by
    exact (mul_le_mul_of_nonneg_right hdenLe hRpos.le).trans_lt hfloorR
  have hRdiv : R / 2 < M / den := by
    rw [lt_div_iff₀ hdenPos]
    calc
      R / 2 * den = (den * R) / 2 := by ring
      _ < (2 * M) / 2 := div_lt_div_of_pos_right hdenR (by norm_num)
      _ = M := by ring
  have hnum : 14 * M / 3 < 5 * N * M * (p m : ℝ) := by
    have hscaled : (5 * M) * (14 / 15) <
        (5 * M) * (N * (p m : ℝ)) :=
      mul_lt_mul_of_pos_left hNpm (by positivity)
    convert hscaled using 1 <;> ring
  have hbasePenalty : 7 * R / 3 <
      (5 * N * M * (p m : ℝ)) / den := by
    have hleft : (14 / 3 : ℝ) * (R / 2) <
        (14 / 3 : ℝ) * (M / den) :=
      mul_lt_mul_of_pos_left hRdiv (by norm_num)
    have hright := div_lt_div_of_pos_right hnum hdenPos
    calc
      7 * R / 3 = (14 / 3 : ℝ) * (R / 2) := by ring
      _ < (14 / 3 : ℝ) * (M / den) := hleft
      _ = (14 * M / 3) / den := by ring
      _ < (5 * N * M * (p m : ℝ)) / den := hright
  have hcoefficient : 5 * N * M ≤ 5 * N * M / d := by
    rw [le_div_iff₀ hd]
    exact mul_le_of_le_one_right (by positivity) hd1
  have hfractionNonneg :
      0 ≤ (p m : ℝ) / den := div_nonneg (p m).property.1 hdenPos.le
  have hpenalty : 7 * R / 3 <
      (5 * N * M / d) * ((p m : ℝ) / den) := by
    calc
      7 * R / 3 < (5 * N * M * (p m : ℝ)) / den := hbasePenalty
      _ = (5 * N * M) * ((p m : ℝ) / den) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoefficient hfractionNonneg
  have hphiUpper := phi_maximalQuitter_upper G M d hM hd z m hpm
  have hphiLower : -(R + 1) ≤ Phi G M d z m := (ha.2 m).1
  have hRlarge : M / 3 + N * M + 1 < 4 * R / 3 := by
    have hNM : 3 ≤ N * M := by
      calc
        3 = 3 * 1 := by ring
        _ ≤ N * M := mul_le_mul hN hM.1 (by norm_num) (by positivity)
    have hMNM : M ≤ N * M := by
      calc
        M = 1 * M := by ring
        _ ≤ N * M := mul_le_mul_of_nonneg_right (by linarith [hN]) hMpos.le
    have hRN : 10 * N * M ≤ R := by
      exact hR
    have hsmall : M / 3 + N * M + 1 ≤ 5 * (N * M) / 3 := by
      have hMthird : M / 3 ≤ (N * M) / 3 :=
        div_le_div_of_nonneg_right hMNM (by norm_num)
      have honeThird : 1 ≤ (N * M) / 3 := by
        rw [le_div_iff₀ (by norm_num)]
        simpa using hNM
      calc
        M / 3 + N * M + 1 ≤
            (N * M) / 3 + N * M + (N * M) / 3 := by
          gcongr
        _ = 5 * (N * M) / 3 := by ring
    have hstrict : 5 * (N * M) / 3 < 40 * (N * M) / 3 := by
      have hscaled := mul_lt_mul_of_pos_right
        (show (5 / 3 : ℝ) < 40 / 3 by norm_num)
        (show 0 < N * M by linarith [hNM])
      calc
        5 * (N * M) / 3 = (5 / 3) * (N * M) := by ring
        _ < (40 / 3) * (N * M) := hscaled
        _ = 40 * (N * M) / 3 := by ring
    have hscaledR : 40 * (N * M) / 3 ≤ 4 * R / 3 := by
      have hscaled := mul_le_mul_of_nonneg_left hRN (by norm_num : (0 : ℝ) ≤ 4 / 3)
      calc
        40 * (N * M) / 3 = (4 / 3) * (10 * N * M) := by ring
        _ ≤ (4 / 3) * R := hscaled
        _ = 4 * R / 3 := by ring
    exact hsmall.trans_lt (hstrict.trans_le hscaledR)
  dsimp only [N, p, tau, den] at hpenalty
  have hstrictUpper : Phi G M d z m < -(R + 1) := by
    calc
      Phi G M d z m ≤ M / 3 -
          (5 * (Fintype.card G.Player : ℝ) * M / d) *
            ((z.1.2 m : ℝ) /
              (1 - (z.1.2 m : ℝ)) ^ Fintype.card G.Player) +
          (Fintype.card G.Player : ℝ) * M := hphiUpper
      _ < M / 3 - 7 * R / 3 + N * M := by
        dsimp only [N, p, tau, den] at hpenalty ⊢
        linarith
      _ < -(R + 1) := by linarith
  exact (not_lt_of_ge hphiLower hstrictUpper).elim

/--
Lemma 4.4's boundedness of the continuation coordinate `β`, with the
standing Section 3 assumptions and the `d,ρ,ξ,R` relations made explicit.
The printed proof's zero-quitter inference is refuted immediately above; the
remaining open task is either to derive it from these standing assumptions or
replace that step while retaining the stated bounds.
-/
theorem lemma4_4 (G : QuittingGame) (M d ρ ξ R : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (z : EZeroTilde G)
    (ha : Phi G M d z ∈ TruncatedW G R) :
    (∀ j, -R / 2 ≤ z.1.1 j ∧ z.1.1 j ≤ R + 1) ∧
      ∀ j, 0 < (z.1.2 j : ℝ) → |z.1.1 j| ≤ R / 2 := by
  refine ⟨?_, supportedContinuation_abs_le_half_radius G M d ρ ξ R
    hplayers hM hd hd1 hmotion hconstants z ha⟩
  sorry

/--
Lemma 4.5.  This statement retains all seven conditions rather than replacing
them by a vague “viability” predicate.  Its proof contains the paper's long
contractibility/Jacobian and lower-boundary case analysis; no corresponding
production theorem exists.  In Property (6), Case 5, the printed final phrase
“`λ ≥ 1/2`” must be read as “`1-λ ≥ 1/2`”: the preceding sentence proves
`λ ≤ 1/2`, and `y = λx + (1-λ)f(x,p)` needs the latter coefficient on the
strict drift.
-/
theorem lemma4_5 (G : QuittingGame) (M d ρ ξ R η ε δ : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hnonsingular : HasNonsingularSingletonDifferences G)
    (hη : Corollary4_1Statement G η)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval)
    (hcutoff : IsSection4Cutoff G R (Section4Omega G M d ρ ξ R ε) cutoff)
    (hε : 0 < ε) (hεη : ε < η / 3) (hερ : ε < ρ / 3)
    (hδ : δ = Section4Delta G M ε) :
    Question1Hypotheses
      (TruncatedW G R)
      (fun j : Fin (Fintype.card G.Player) =>
        TruncatedPiece G R ((Fintype.equivFin G.Player).symm j))
      (Section4H G inverse cutoff)
      (GluedNeighborhood G R ε)
      (correspondenceGraph (GluedFiber G R ε δ))
      (Section4J G inverse cutoff R ε δ) := by
  sorry

/-! ### 4.5. Application of Question 1 -/

/--
Theorem 4.1.  Besides Lemma 4.5, the paper uses perturbation stability,
restriction to a cluster-point tail, exclusion of the lower glue, and the
extended-orbit/equilibrium implication of Theorem 2.3.  These interfaces are
all stated above, but their analytic proofs remain open; therefore the
conditional theorem is not marked as checked by merely chaining `sorry`-based
literature declarations.
-/
theorem theorem4_1 (hquestion : Question1Affirmative) :
    ∀ G : QuittingGame, (∀ n, IsNormalPlayer G n) →
      HasQuitApproximateEquilibria G := by
  sorry

/-! ## 5. Conclusion: abnormal players -/

/-- A player is abnormal when her solo payoff is below her min-max value. -/
def IsAbnormalPlayer (G : QuittingGame) (j : G.Player) : Prop :=
  ¬IsNormalPlayer G j

/-- The positive gap `ν_j = χʲ - vʲ` attached to an abnormal player. -/
def AbnormalGap (G : QuittingGame) (j : G.Player) : ℝ :=
  MinMaxQuit G j - SoloPayoff G j

/-- The game has at least one abnormal player. -/
def HasAbnormalPlayer (G : QuittingGame) : Prop :=
  ∃ j, IsAbnormalPlayer G j

/--
The minimum abnormal-player gap `ν`.  Section 5 invokes this only under
`HasAbnormalPlayer G`; outside that case the total `sInf` convention is
irrelevant.
-/
def MinimumAbnormalGap (G : QuittingGame) : ℝ :=
  sInf {ν : ℝ | ∃ j, IsAbnormalPlayer G j ∧ ν = AbnormalGap G j}

/-- The Section 5 restriction `0 < ε < ν/3`. -/
def IsSection5Accuracy (G : QuittingGame) (ε : ℝ) : Prop :=
  HasAbnormalPlayer G ∧ 0 < ε ∧ ε < MinimumAbnormalGap G / 3

/--
The modified compact set proposed in Section 5:
`(⋃_{j normal} C_j) ∪ (⋃_{k ≠ l abnormal} (C_k ∩ C_l))`.
-/
def Section5ModifiedC (G : QuittingGame) (R : ℝ) :
    Set (Payoff G.Player) :=
  {x |
    (∃ j, IsNormalPlayer G j ∧ x ∈ TruncatedPiece G R j) ∨
    ∃ k l, k ≠ l ∧ IsAbnormalPlayer G k ∧ IsAbnormalPlayer G l ∧
      x ∈ TruncatedPiece G R k ∩ TruncatedPiece G R l}

/-- Lemma 5.1 is Simon 2007, Lemma 4 (numbered Lemma 3 there): an abnormal
player has negative solo payoff, and every other player's solo exit gives her
at least her min--max value. -/
theorem lemma5_1 (G : QuittingGame) (j : G.Player)
    (habnormal : IsAbnormalPlayer G j) :
    SoloPayoff G j < 0 ∧ ∀ i, i ≠ j →
      G.reward ⟨{i}, Finset.singleton_nonempty i⟩ j ≥ MinMaxQuit G j := by
  exact Literature.Simon2007.lemma3 G j habnormal

/--
The unnumbered claim in Section 5: an affirmative answer to Question 1 still
implies approximate-equilibrium existence when abnormal players are present.
The paper sketches the modified set `Section5ModifiedC`, an artificial
boundary homotopy and glue, and a choice of `d` depending on the minimum gap,
but does not supply the complete verification.  That missing construction is
therefore recorded explicitly.
-/
theorem question1_affirmative_implies_all_quitting_games
    (hquestion : Question1Affirmative) :
    ∀ G : QuittingGame, HasQuitApproximateEquilibria G := by
  sorry

end

end Literature.Simon2012
