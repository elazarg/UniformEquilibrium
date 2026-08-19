import Literature.Simon2007

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

`Payoff N = N → ℝ` inherits mathlib's finite product norm.  Thus the topological
claims are represented in an equivalent finite-dimensional norm, while every
quantitative estimate below is explicitly a claim in that chosen norm.  No
unmentioned identification with the Euclidean two-norm is used.

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
  {z | z ∈ J ∧ ‖z.2 - z.1‖ ≤ δ}

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
infinite; `Metric.infDist` itself is real-valued.
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
  (∀ x ∈ V, IsContractibleSet (GraphFiber G x) ∧ x ∈ GraphFiber G x) ∧
  IsCompact J ∧ HomotopyTerminalImage C H ⊆ J ∧ G ⊆ J ∧
  ∃ ω : ℝ, 0 < ω ∧ SmallStepGraph J ω ⊆ G ∧
    ∀ x ∈ V, ∀ i,
      (frontier C ∩ piece i).Nonempty →
      Metric.infDist x (frontier C ∩ piece i) ≤ ω →
      ∃ y ∈ GraphFiber G x,
        Metric.infDist y (piece i) ≤ Metric.infDist x (piece i) ∧
        ω ≤ ‖y - x‖ ∧ segment ℝ x y ⊆ GraphFiber G x

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

/--
The paper reports a counterexample to Question 2 and points to a similar
Gobbino--Simon construction, but does not print the counterexample.  Closing
this `sorry` requires importing or reconstructing that external example; no
claim in the present repository supplies it.
-/
theorem question2_is_false : ¬Question2Affirmative := by
  sorry

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

/-- The strengthened version discussed immediately after Question 2. -/
theorem question1_with_no_escape : Question1NoEscapeAffirmative := by
  sorry

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

/--
A stationary approximate equilibrium can be truncated and completed by a
min-max punishment with arbitrarily small survival error.  This compactness
and tail estimate is used by the 2012 correction but has no proved declaration
in Simon 2007 or in the production quitting-game library.
-/
theorem stationary_implies_stationarilyGenerated (G : QuittingGame) :
    Literature.Simon2007.HasStationaryApproximateEquilibria G →
      HasStationarilyGeneratedApproximateEquilibria G := by
  sorry

/-- A vector lies within distance one of the feasible set. -/
def WithinOneOfFeasible (G : QuittingGame) (r : Payoff G.Player) : Prop :=
  ∃ z, Feasible G z ∧ ‖r - z‖ ≤ 1

/-- The corrected uniform conclusion in Lemma 2.1(2). -/
def SatisfiesCorrectedLemma2_1Parameter (G : QuittingGame) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ ∀ r p,
    WithinOneOfFeasible G r → IsRational G ρ r →
    p ∈ EpsilonRow G ρ r →
      let y := QuittingOneStagePayoff G r p
      ρ * QuitProbability G p ≤ ‖r - y‖ ∧
        QuitProbability G p ≤ 1 - ρ

/--
The compact-set form described in the correction paragraph.  The parameter
may depend on the chosen compact continuation set.
-/
def SatisfiesCompactMotionBound (G : QuittingGame)
    (K : Set (Payoff G.Player)) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ r ∈ K, ∀ p,
    IsRational G ρ r → p ∈ EpsilonRow G ρ r →
      let y := QuittingOneStagePayoff G r p
      ρ * QuitProbability G p ≤ ‖r - y‖ ∧
        QuitProbability G p ≤ 1 - ρ

/--
The compact-set form of Lemma 2.1(2).  This is the corrected statement behind
the displayed distance-one application: the common parameter may depend on
`K`.  The proof is the compact-subsequence argument in the paper; neither the
uncorrected Simon 2007 declaration nor the production quitting-game library
contains this uniformization.
-/
theorem lemma2_1_part2_compact (G : QuittingGame)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (K : Set (Payoff G.Player)) (hK : IsCompact K) :
    SatisfiesCompactMotionBound G K := by
  sorry

/-- Lemma 2.1(1), isolated from the corrected compactness clause. -/
theorem lemma2_1_part1 (G : QuittingGame)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    (∃ l, IsNormalPlayer G l ∧ 0 < SoloPayoff G l) ∧
      ∀ j, IsNormalPlayer G j → ∃ k, k ≠ j ∧ IsNormalPlayer G k ∧
        G.reward ⟨{j}, Finset.singleton_nonempty j⟩ k < SoloPayoff G k := by
  have hstationary : ¬Literature.Simon2007.HasStationaryApproximateEquilibria G :=
    fun h => hgenerated (stationary_implies_stationarilyGenerated G h)
  have hinstant2007 :
      ¬Literature.Simon2007.HasInstantApproximateEquilibria G :=
    fun h => hinstant ((instantApproximateEquilibria_iff_simon2007 G).2 h)
  have h := Literature.Simon2007.lemma5 G hstationary hinstant2007
  exact ⟨h.1, h.2.1⟩

/--
Lemma 2.1(2), with the two corrections printed on page 185.  Simon 2007's
`lemma5` declaration cannot prove this honestly: its hypothesis excludes only
stationary equilibria and its conclusion omits `WithinOneOfFeasible`.
The missing proof is the compact-subsequence argument from the article.
-/
theorem lemma2_1_part2 (G : QuittingGame)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    ∃ ρ, SatisfiesCorrectedLemma2_1Parameter G ρ := by
  sorry

/-- Lemma 2.1, with both corrected clauses. -/
theorem lemma2_1 (G : QuittingGame)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    ((∃ l, IsNormalPlayer G l ∧ 0 < SoloPayoff G l) ∧
      ∀ j, IsNormalPlayer G j → ∃ k, k ≠ j ∧ IsNormalPlayer G k ∧
        G.reward ⟨{j}, Finset.singleton_nonempty j⟩ k < SoloPayoff G k) ∧
      ∃ ρ, SatisfiesCorrectedLemma2_1Parameter G ρ := by
  exact ⟨lemma2_1_part1 G hgenerated hinstant,
    lemma2_1_part2 G hgenerated hinstant⟩

/-- Theorem 2.1 uses the five conditions already stated exactly in Simon 2007. -/
theorem theorem2_1 (G : QuittingGame)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    EquivalentFive (HasQuitApproximateEquilibria G) (CyclicOrbitCondition G)
      (FiniteNearOrbitCondition G) (InfiniteOrbitCondition G)
      (ExtendedOrbitCondition G) := by
  have hstationary : ¬Literature.Simon2007.HasStationaryApproximateEquilibria G :=
    fun h => hgenerated (stationary_implies_stationarilyGenerated G h)
  have hinstant2007 :
      ¬Literature.Simon2007.HasInstantApproximateEquilibria G :=
    fun h => hinstant ((instantApproximateEquilibria_iff_simon2007 G).2 h)
  exact Literature.Simon2007.theorem3 G hstationary hinstant2007

/-- A positive bound on the differences between terminal payoffs. -/
def IsPositivePayoffDifferenceBound (G : QuittingGame) (B : ℝ) : Prop :=
  0 < B ∧ ∀ A C n, |G.reward A n - G.reward C n| ≤ B

/-- Lemma 2.2 in its exact 2012 normalization. -/
theorem lemma2_2 (G : QuittingGame) {B ε : ℝ}
    (hB : IsPositivePayoffDifferenceBound G B)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hε : 0 < ε) (hε1 : ε ≤ 1) {r s : Payoff G.Player}
    (hstep : s ∈ FRow G (ε ^ 2 / (2 * B)) r) :
    ∀ n,
      (r n ≥ MinMaxQuit G n - 3 * ε →
        s n ≥ MinMaxQuit G n - 3 * ε) ∧
      (r n < MinMaxQuit G n - 3 * ε →
        s n ≥ r n + ε ^ 2 / (2 * B)) := by
  sorry

/--
Checked adapter to Simon 2007's more restrictive bound package.  This records
exactly how much of Lemma 2.2 is already represented there.
-/
theorem lemma2_2_of_simon2007_bound (G : QuittingGame) {B ε : ℝ}
    (hB : IsQuittingPayoffDifferenceBound G B)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hε : 0 < ε) (hε1 : ε ≤ 1) {r s : Payoff G.Player}
    (hstep : s ∈ FRow G (ε ^ 2 / (2 * B)) r) :
    ∀ n,
      (r n ≥ MinMaxQuit G n - 3 * ε →
        s n ≥ MinMaxQuit G n - 3 * ε) ∧
      (r n < MinMaxQuit G n - 3 * ε →
        s n ≥ r n + ε ^ 2 / (2 * B)) := by
  have hstationary : ¬Literature.Simon2007.HasStationaryApproximateEquilibria G :=
    fun h => hgenerated (stationary_implies_stationarilyGenerated G h)
  have hinstant2007 :
      ¬Literature.Simon2007.HasInstantApproximateEquilibria G :=
    fun h => hinstant ((instantApproximateEquilibria_iff_simon2007 G).2 h)
  exact Literature.Simon2007.lemma6 G hB hnormal hstationary hinstant2007
    hε hε1 hstep

/-- Theorem 2.2, with `F_ε` infinite orbits of unbounded variation. -/
theorem theorem2_2 (G : QuittingGame)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    HasQuitApproximateEquilibria G ↔ InfiniteUnrestrictedOrbitCondition G := by
  have hstationary : ¬Literature.Simon2007.HasStationaryApproximateEquilibria G :=
    fun h => hgenerated (stationary_implies_stationarilyGenerated G h)
  have hinstant2007 :
      ¬Literature.Simon2007.HasInstantApproximateEquilibria G :=
    fun h => hinstant ((instantApproximateEquilibria_iff_simon2007 G).2 h)
  exact Literature.Simon2007.corollary2 G hnormal hinstant2007 hstationary

/-- The unqualified extended-orbit condition in Theorem 2.3. -/
def ExtendedUnrestrictedOrbitCondition (G : QuittingGame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ orbit : ExtendedOrbitData (FRow G ε),
    HasUnboundedExtendedVariation orbit

/--
Theorem 2.3.  Removing rationality from an extended orbit uses Lemma 2.2 to
show eventual entry into, and permanence in, the rational region.  The
repository has no checked extended-orbit tail/reindexing implementation.
-/
theorem theorem2_3 (G : QuittingGame)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    HasQuitApproximateEquilibria G ↔ ExtendedUnrestrictedOrbitCondition G := by
  sorry

/-- Lemma 2.3's pointwise small parameter. -/
def SatisfiesLemma2_3At (G : QuittingGame) (r : Payoff G.Player)
    (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ ∀ p, p ∈ EpsilonRow G ρ r →
    ρ * QuitProbability G p ≤
      ‖r - QuittingOneStagePayoff G r p‖

/--
Lemma 2.3.  The quantifier is `∀ r, ∃ ρ`; a single global parameter is not
claimed.  Its proof combines the compact-set version of Lemma 2.1 with the
coordinate increase in Lemma 2.2.  The exact compact-set lemma remains open
above, so this result is not imported from the stronger, incorrect 2007 text.
-/
theorem lemma2_3 (G : QuittingGame)
    (M : ℝ) (hM : IsSimonPayoffScale G M)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G) :
    ∀ r, ∃ ρ, SatisfiesLemma2_3At G r ρ := by
  sorry

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

/-- A concrete inverse/homeomorphism package for `φ`. -/
structure PhiInverseData (G : QuittingGame) (M d : ℝ) where
  inv : Payoff G.Player → EZeroTilde G
  leftInverse : Function.LeftInverse inv (Phi G M d)
  rightInverse : Function.RightInverse inv (Phi G M d)
  continuousInv : Continuous inv

/-- Lemma 3.1: injectivity and the all-continue fiber. -/
theorem lemma3_1 (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1) :
    Function.Injective (Phi G M d) ∧
    (∀ x, ((x, zeroQuitRow G) ∈ EZeroTilde G ↔
      ∀ j, SoloPayoff G j ≤ x j)) ∧
    ∀ x (hx : (x, zeroQuitRow G) ∈ EZeroTilde G),
      Phi G M d ⟨(x, zeroQuitRow G), hx⟩ = x := by
  sorry

/-- Lemma 3.2: surjectivity and continuity of the inverse. -/
theorem lemma3_2 (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1) :
    Function.Surjective (Phi G M d) ∧ Nonempty (PhiInverseData G M d) := by
  sorry

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

/--
A single `ρ` satisfying the two motion estimates on the bounded continuation
region used in Sections 3--4.  The printed phrase “`ρ` satisfies Lemmas 2.1
and 2.3” mixes a common parameter with Lemma 2.3's pointwise quantifiers
`∀ r, ∃ ρ`; this predicate records the bounded uniformization actually used
by Lemmas 3.3--4.5 rather than silently asserting a global `∃ ρ, ∀ r`.
-/
def IsStructureMotionParameter (G : QuittingGame) (M ρ : ℝ) : Prop :=
  SatisfiesCorrectedLemma2_1Parameter G ρ ∧
  0 < ρ ∧ ρ ≤ 1 ∧
  ∀ r : Payoff G.Player,
    (∀ j, MinMaxQuit G j - ρ ≤ r j ∧
      r j ≤ 2 * (Fintype.card G.Player : ℝ) * M) →
    ∀ p, p ∈ EpsilonRow G ρ r →
      ρ * QuitProbability G p ≤ ‖r - QuittingOneStagePayoff G r p‖

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

/--
Theorem 3.1.  Its proof is the homeomorphism argument in Sections 3.2--3.5.
No production theorem proves injectivity, surjectivity, properness, or the
fixed-point exclusion for this `φ`; importing the 2007 Kohlberg--Mertens
statement would not establish this quitting-specific result.
-/
theorem theorem3_1 (G : QuittingGame) (M : ℝ)
    (hM : IsSimonPayoffScale G M) : StructureTheoremConclusion G M := by
  sorry

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

/-- Lemma 3.3. -/
theorem lemma3_3 (G : QuittingGame) (M ε : ℝ)
    (hM : IsSimonPayoffScale G M) : Lemma3_3Statement G M ε := by
  sorry

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

/-- Lemma 3.4, retaining all three displayed conclusions. -/
theorem lemma3_4 (G : QuittingGame) (M d ρ ξ R : ℝ)
    (hM : IsSimonPayoffScale G M)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (z : EZeroTilde G) (t : UnitInterval)
    (a : Payoff G.Player) (ha : a = Phi G M d z)
    (x : Payoff G.Player)
    (hx : x = (1 - (t : ℝ)) • z.1.1 + (t : ℝ) • a) :
    ((∃ j, R ≤ |a j|) → ¬StructureTargetBox G M ρ x) ∧
    (∀ j, R ≤ a j →
      R - (Fintype.card G.Player : ℝ) * M < z.1.1 j ∧
        (z.1.2 j : ℝ) = 0) ∧
    ∀ j, a j ≤ -R → MinMaxQuit G j - ρ ≤ z.1.1 j →
      1 - (1 / 20 : ℝ) *
        (ρ / (2 * (Fintype.card G.Player : ℝ) * M)) ^
          Fintype.card G.Player ≤ (z.1.2 j : ℝ) := by
  sorry

/-- Lemma 3.5's two distance estimates. -/
theorem lemma3_5 (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (z : EZeroTilde G)
    (hqpos : 0 < QuitProbability G z.1.2)
    (hqsmall : QuitProbability G z.1.2 <
      1 / (2 * (Fintype.card G.Player : ℝ)))
    (j : G.Player) (hj : 0 < (z.1.2 j : ℝ)) :
    Metric.infDist z.1.1 (Wj G j ∩ frontier (WSet G)) ≤
      QuitProbability G z.1.2 * (Fintype.card G.Player : ℝ) * M / 3 ∧
    Metric.infDist (Phi G M d z) (Wj G j ∩ frontier (WSet G)) ≤
      12 * (Fintype.card G.Player : ℝ) ^ 2 * M *
        QuitProbability G z.1.2 / d := by
  sorry

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

/-- Replace only the reward table while keeping the player type. -/
def WithReward (G : QuittingGame)
    (reward : {A : Finset G.Player // A.Nonempty} → Payoff G.Player) :
    QuittingGame where
  Player := G.Player
  reward := reward

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
  HasNonsingularSingletonDifferences (WithReward G reward')

/--
The paper's generic perturbation assertion.  A proof must also show that the
min-max values vary in the direction needed to preserve normality; no existing
normalization lemma proves this exact statement.
-/
theorem exists_nonsingularPerturbation (G : QuittingGame)
    (hnormal : ∀ n, IsNormalPlayer G n) {tol : ℝ} (htol : 0 < tol) :
    ∃ reward', IsNonsingularPerturbation G reward' tol ∧
      ∀ n, IsNormalPlayer (WithReward G reward') n := by
  sorry

/-- Every matrix entry is bounded in absolute value by `B`. -/
def MatrixEntriesBounded {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) : Prop :=
  ∀ i j, |A i j| ≤ B

/--
Lemma 4.1.  This is the compactness of the bounded, determinant-separated
matrix family times the unit sphere.  Mathlib has all ingredients, but the
uniform minimum proof has not been assembled in this repository.
-/
theorem lemma4_1 {n : ℕ} (hn : 0 < n) {B ε : ℝ}
    (hB : 0 < B) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin n) (Fin n) ℝ,
      MatrixEntriesBounded A B → ε ≤ |A.det| →
      ∀ v : Fin n → ℝ, δ * ‖v‖ ≤ ‖A.mulVec v‖ := by
  sorry

/-- The uniform perturbation corollary to Lemma 4.1. -/
def Corollary4_1Statement (G : QuittingGame) (η : ℝ) : Prop :=
  0 < η ∧ ∀ Q : Finset G.Player, 2 ≤ Q.card →
    ∀ d : Matrix {i // i ∈ Q} {j // j ∈ Q} ℝ,
      (∀ i j, |d i j| ≤ η) →
      ∀ r : {i // i ∈ Q} → ℝ,
        η * ‖r‖ ≤ ‖((SingletonDifferenceMatrix G Q + d).mulVec r)‖

/-- Corollary 4.1. -/
theorem corollary4_1 (G : QuittingGame)
    (hnonsingular : HasNonsingularSingletonDifferences G) :
    ∃ η, Corollary4_1Statement G η := by
  sorry

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

/-- The cutoff `λ` used to glue the structure homotopy to the identity near `D`. -/
def IsSection4Cutoff (G : QuittingGame) (R δ : ℝ)
    (cutoff : Payoff G.Player → UnitInterval) : Prop :=
  Continuous cutoff ∧
  (∀ x ∈ LowerBoundary G R, (cutoff x : ℝ) = 1) ∧
  (∀ x, δ ≤ Metric.infDist x (LowerBoundary G R) → (cutoff x : ℝ) = 0) ∧
  ∀ x ∈ TruncatedW G R \ LowerBoundary G R, (cutoff x : ℝ) < 1

/-- The first coordinate `x(a)` of the deformed graph. -/
def Section4X (G : QuittingGame) {M d : ℝ}
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval) (a : Payoff G.Player) :
    Payoff G.Player :=
  (cutoff a : ℝ) • a + (1 - (cutoff a : ℝ)) • (inverse.inv a).1.1

/-- The second coordinate `y(a)` of the deformed graph. -/
def Section4Y (G : QuittingGame) {M d : ℝ}
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval) (a : Payoff G.Player) :
    Payoff G.Player :=
  let x := Section4X G inverse cutoff a
  let p := (inverse.inv a).1.2
  (cutoff a : ℝ) • x +
    (1 - (cutoff a : ℝ)) • QuittingOneStagePayoff G x p

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
  {x | Metric.infDist x (LowerBoundary G R) ≤ ε / 3}

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

/--
Lemma 4.2: the upper glue is contained in `F_ε`.  Membership of `x` in the
upper neighborhood is explicit; without it `UpperGlueFiber` contains the
all-continue image even outside the domain intended in the paper.
-/
theorem lemma4_2 (G : QuittingGame) (M R ε δ : ℝ)
    (hM : IsSimonPayoffScale G M) (hε : 0 < ε)
    (hδ : δ = Section4Delta G M ε) :
    ∀ x, x ∈ UpperNeighborhood G R ε → ∀ y,
      y ∈ UpperGlueFiber G R ε δ x → y ∈ FRow G ε x := by
  sorry

/--
Lemma 4.3's coordinate drift statement, under the standing Section 3--4
choices used in its proof.  These hypotheses are not optional: the paper uses
normality, exclusion of the two simple equilibrium classes, the common motion
parameter, the constants `ξ,R`, and the support properties of the cutoff.
-/
theorem lemma4_3 (G : QuittingGame) (M d ρ ξ R δ : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval)
    (hcutoff : IsSection4Cutoff G R δ cutoff)
    (a : Payoff G.Player)
    (haC : a ∈ TruncatedW G R)
    (hcutoff0 : 0 < (cutoff a : ℝ)) (hcutoff1 : (cutoff a : ℝ) < 1)
    (hxbox : ∀ j, -M ≤ Section4X G inverse cutoff a j ∧
      Section4X G inverse cutoff a j ≤ M) :
    ∀ j,
      (MinMaxQuit G j - ρ / 3 ≤ Section4X G inverse cutoff a j →
        MinMaxQuit G j - ρ / 3 ≤ Section4Y G inverse cutoff a j) ∧
      (Section4X G inverse cutoff a j < MinMaxQuit G j - ρ / 3 →
        Section4X G inverse cutoff a j + ρ ^ 2 / (500 * M) ≤
          Section4Y G inverse cutoff a j) := by
  sorry

/--
Lemma 4.4's boundedness of the continuation coordinate `β`, with the `d,ξ,R`
relations from the preceding construction made explicit.
-/
theorem lemma4_4 (G : QuittingGame) (M d ρ ξ R : ℝ)
    (hM : IsSimonPayoffScale G M)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (z : EZeroTilde G)
    (ha : Phi G M d z ∈ TruncatedW G R) :
    (∀ j, -R / 2 ≤ z.1.1 j ∧ z.1.1 j ≤ R + 1) ∧
      ∀ j, 0 < (z.1.2 j : ℝ) → |z.1.1 j| ≤ R / 2 := by
  sorry

/--
Lemma 4.5.  This statement retains all seven conditions rather than replacing
them by a vague “viability” predicate.  Its proof contains the paper's long
contractibility/Jacobian and lower-boundary case analysis; no corresponding
production theorem exists.
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
    (hcutoff : IsSection4Cutoff G R δ cutoff)
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

/-- Lemma 5.1 is exactly Simon 2007, Lemma 4 (numbered Lemma 3 there). -/
theorem lemma5_1 (G : QuittingGame) (j : G.Player)
    (habnormal : ¬IsNormalPlayer G j) :
    SoloPayoff G j < 0 ∧ ∀ i, i ≠ j →
      G.reward ⟨{i}, Finset.singleton_nonempty i⟩ j ≥ MinMaxQuit G j := by
  exact Literature.Simon2007.lemma3 G j habnormal

/-!
The final paragraphs propose extending Theorem 4.1 by induction on the number
of abnormal players: their Lemma 5.1 makes “never quit” a min-max-optimal
response to singleton exits, while the structure map's parameter `d` is meant
to retain the required slack.  The paper does not state a numbered theorem or
complete that extension, so no unconditional all-player claim is added here.
-/

end

end Literature.Simon2012
