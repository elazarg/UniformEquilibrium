import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses
import UniformEquilibrium.Quitting.Classification.LCP.NormalCore
import UniformEquilibrium.Quitting.Classification.LCP.StrategicTransport
import UniformEquilibrium.Quitting.Classification.TableExistenceBranches

/-!
# Solan--Solan (2018 arXiv v1) — paper-order audit

E. Solan and O. N. Solan, *Quitting Games and Linear Complementarity
Problems*, arXiv:1707.02598v1, 9 July 2017 (the paper archive is dated
October 9, 2018).

This file is pinned to the arXiv v1 manuscript, read from `1707.02598.pdf`.
It is not a transcription of the published Mathematics of Operations
Research version. In particular, v1 defines normal players by the displayed
recursion in Section 2.3, omits `j ≠ i` in that display, and uses the
projective/simplex LCP in its Definition 2.8. The published manuscript moves
the recursion to its Section 5 alpha-player discussion, adds the distinctness
condition, and changes the normal-player definition and theorem numbering.
Those final-version statements are not silently merged here; the repository's
distinct-witness recursion remains available through the imported
`normalLayer`/`normalCore` declarations, while the v1 display is represented by
`printedNormalLayer`/`printedNormalCore`.

The paper's public-signal strategy space, discounted selection, and
construction data are represented by paper-local records below. They are not
promoted to production semantics. The stationary and LCP statements use the
faithful larger payoff-table adapter, including an explicit nontermination
payoff. Unproved expressible paper claims are `sorry`, as required by the
Literature contract.
-/

namespace Literature.SolanAndSolan2020

open GameTheory StochasticGame QuittingLCPClassification
open Filter
open scoped BigOperators
open scoped Topology

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Section 2.1 — model -/

/-! **Definition 2.1 (paper).** A quitting game is a finite player set
`I=[N]` and a payoff vector `r_S ∈ [-1,1]^N` for every `S ⊆ I`. At every
stage every player chooses Continue or Quit; the first nonempty quitter set
`S*` ends the game and pays `r_{S*}`, while never quitting pays `r_∅`.
The paper also defines pure strategies `N ∪ {∞}`, behavior strategies
`x_i=(x_i^t)_{t∈N}`, profiles `X_i`, `X`, the induced law `P_x`, expected
payoff `γ(x)`, and the undiscounted ε-equilibrium inequality.

The repository's `QuittingPayoffTable` is the faithful finite-player adapter:
`terminal` is `r_S` for nonempty `S`, and `never` is `r_∅`. Its
`terminalPayoff` supplies the induced expected payoff for a repository
behavior profile. The paper's pure-strategy presentation is equivalent to
the behavioral presentation but has no separate declaration here.
-/

/-! `paperTable` carries `(r_S)_{S ⊆ I}` together with `r_∅`. -/
abbrev paperTable (ι : Type) [Fintype ι] [DecidableEq ι] :=
  QuittingPayoffTable ι

/-! Paper ε-equilibrium adapter:
`γ_i(x) ≥ γ_i(x'_i,x_{-i}) - ε`. -/
def paperEpsilonEquilibrium
    (table : paperTable ι) (ε : ℝ)
    (profile : (quittingGame table.terminal).BehaviorProfile) : Prop :=
  (quittingGame table.terminal).IsεAsymptoticNash table.terminalPayoff ε profile

/-! `paperStationaryEpsilonEquilibria table` means stationary ε-equilibria
exist for every `ε>0`. -/
def paperStationaryEpsilonEquilibria (table : paperTable ι) : Prop :=
  table.StationaryεEquilibriumExistence

/-! **Assumption 2.1.** The paper assumes `r_i^i = 0` for every player.
This is a standing condition, not a theorem. -/

def SoloExitNormalized (table : paperTable ι) : Prop :=
  ∀ i : ι, table.terminal (quittingProjectiveSingletonTerminal i) i = 0

/-! **Lemma 2.2 (paper).** If there is a normal player `i` such that the
column/vector `r^i` is coordinatewise nonnegative, then a stationary
`ε`-equilibrium exists for every positive `ε`. The paper's `I*` is introduced
by the recursion in Section 2.3; the paper-local stationary adapter is stated
below after that recursive set has been defined. -/

/-! **Definition 2.3 (sunspot ε-equilibrium, paper).** At every stage the
players observe an independent uniform signal in `[0,1]`; a strategy is a
sequence of measurable functions from public signal histories to quit
probabilities. The local profile below packages the paper's induced payoff and
unilateral-deviation payoff functions; the probability construction is not
silently identified with the repository's terminal-only profile. -/

/-! `PaperSignal = [0,1]` and `PaperSignalHistory t = [0,1]^t`. -/
abbrev PaperSignal := Set.Icc (0 : ℝ) 1
/-! A public quit rule is `ξ_i^t : [0,1]^t → [0,1]`. -/
abbrev PaperSignalHistory (t : ℕ) := Fin t → PaperSignal
/-! Quit probabilities range over `[0,1]`. -/
abbrev PaperQuitProbability := Set.Icc (0 : ℝ) 1
/-! `PaperPublicStrategy = (ξ^t)_{t≥1}` with public signal histories. -/
abbrev PaperPublicStrategy :=
  ∀ t : ℕ, PaperSignalHistory t → PaperQuitProbability

/-! A paper sunspot profile packages public rules, induced payoff, and
unilateral deviation payoffs. -/
structure PaperSunspotProfile (table : paperTable ι) where
  strategy : ι → PaperPublicStrategy
  payoff : Payoff ι
  unilateralPayoff : ∀ _who : ι, PaperPublicStrategy
    → ℝ

/-! `ξ` is a sunspot ε-equilibrium iff
`γ_i(ξ) ≥ γ_i(ξ'_i,ξ_{-i})-ε` for every `i,ξ'_i`. -/
def paperSunspotEpsilonEquilibrium
    (table : paperTable ι) (ε : ℝ)
    (profile : PaperSunspotProfile table) : Prop :=
  ∀ who (deviation : PaperPublicStrategy),
    profile.payoff who ≥ profile.unilateralPayoff who deviation - ε

/-! At history `(t,h)`, at most one player has `ξ_i^t(h)>0`. -/
def paperAtMostOneQuitter {table : paperTable ι}
    (profile : PaperSunspotProfile table)
    (t : ℕ) (history : PaperSignalHistory t) : Prop :=
  (Finset.filter
      (fun who => 0 < (profile.strategy who t history : ℝ)) Finset.univ).card ≤ 1

/-! **Theorem 2.4 (paper).** Every quitting game admits a sunspot
ε-equilibrium for every `ε > 0`. -/

theorem paper_theorem_2_4 (table : paperTable ι) :
    ∀ ε : ℝ, 0 < ε → ∃ profile : PaperSunspotProfile table,
      paperSunspotEpsilonEquilibrium table ε profile := by
  sorry

/-! ## Section 2.3 — recursively normal players -/

/-! **Definition 2.5 (paper).** `I₀=I` and
`I_{l+1}={i∈I_l : ∃j∈I_l, r^j_i ≤ 0}`; `I* = ⋂_l I_l` is the set of normal
players and its complement is the set of abnormal players. This is the
literal v1 display, including its omitted distinctness condition. -/

/-! `I_l` is the v1 recursive normal-player layer. -/
abbrev V1NormalLayer (M : ι → ι → ℝ) := printedNormalLayer M
/-! `I* = ⋂_l I_l`, represented as the finite recursive core. -/
abbrev V1NormalCore (M : ι → ι → ℝ) := printedNormalCore M

/-! `V1NormalMatrix M` is the principal matrix on `I*`. -/
def V1NormalMatrix (M : ι → ι → ℝ) :
    V1NormalCore M → V1NormalCore M → ℝ :=
  principalMatrix M (V1NormalCore M)

/-! `I* ≠ ∅`. -/
def V1HasNormalPlayers (M : ι → ι → ℝ) : Prop :=
  (V1NormalCore M).Nonempty

/-! `I* = ∅`, i.e. every player is abnormal. -/
def V1AllPlayersAbnormal (M : ι → ι → ℝ) : Prop :=
  V1NormalCore M = ∅

/-! Equation (1) and Equation (2) (paper): if `i` is in a layer/core and
`j` is outside it, then `r^j_i > 0`. The imported
`normalCore_entry_pos_of_notMem` proves the corresponding final,
distinct-witness recursion; the literal v1 recursion collapses under
`SoloExitNormalized`, as recorded below. -/

/-! Literal v1 recursion on a solo-normalized table retains every player. -/
theorem v1_recursion_collapse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    V1NormalCore (normalizedSoloMatrix reward) = Finset.univ :=
  printedNormalCore_normalized_eq_univ reward

/-! Lemma 2.2 adapter: `∃i∈I*, r^i≥0` implies stationary ε-equilibrium
existence for every `ε>0`. -/
theorem paper_lemma_2_2
    (table : paperTable ι) (M : ι → ι → ℝ)
    (hnormal : ∃ i ∈ V1NormalCore M, ∀ who, 0 ≤ M who i) :
    paperStationaryEpsilonEquilibria table := by
  sorry

/-! **Lemma 2.6 (paper).** If all players are abnormal, a stationary
ε-equilibrium exists for every `ε > 0`. The paper proof also uses Lemma 2.2
when the last nonempty layer is reached; the exact strategic min-max-to-table
adapter is not available in this lane. -/

/-! Lemma 2.6: `I*=∅` implies stationary ε-equilibrium existence. -/
theorem paper_lemma_2_6
    (table : paperTable ι) (M : ι → ι → ℝ)
    (habnormal : V1AllPlayersAbnormal M) :
    paperStationaryEpsilonEquilibria table := by
  sorry

/-! **Definition 2.7 (paper remark).** For an `n×n` matrix `R` and `q`, the
paper recalls the textbook LCP: find `w,z ≥ 0` with `w=q+Rz` and
`w_i z_i=0`. -/

/-! The paper's projective LCP `LCP(M,q)` is solvable. -/
abbrev V1LCP (M : ι → ι → ℝ) (q : ι → ℝ) : Prop :=
  HasProjectiveLCPSolution M q

/-! **Definition 2.8 (paper).** `R` is a Q-matrix when the paper's
projective/simplex LCP `LCP(R,q)` has a solution for every `q`. -/

/-! `V1QMatrix M ↔ ∀q, LCP(M,q)` is solvable. -/
abbrev V1QMatrix (M : ι → ι → ℝ) : Prop := IsProjectiveQMatrix M

/-! **Example 2.9 (paper).** For the displayed cyclic `3×3` sign pattern
with zero diagonal, Berman--Plemmons implies Q iff the determinant is
positive. This numerical example is retained here as paper text; no
repository matrix-example declaration is introduced. -/

/-! **Lemma 2.10 (paper).** If the projective LCP with right-hand side zero
has a solution with `z₀<1`, then a stationary ε-equilibrium exists for every
positive ε. -/

/-! Lemma 2.10: a zero-LCP solution with cemetery weight `<1` yields
stationary ε-equilibria for every `ε>0`. -/
theorem paper_lemma_2_10
    (table : paperTable ι)
    (M : ι → ι → ℝ)
    (h : HasNontrivialZeroProjectiveLCPSolution M) :
    paperStationaryEpsilonEquilibria table := by
  sorry

/-! **Theorem 2.11 (paper).** Assume the normal-player set is nonempty and
the zero-right-hand-side projective LCP has no nontrivial solution. If the
normal-player matrix is not Q, then stationary ε-equilibria exist for every
positive ε. If it is Q, then a sunspot ε-equilibrium exists for every
positive ε in which at most one player quits with positive probability at
each stage. The paper-local public-signal relation is the
`PaperSunspotProfile` relation above. -/

/-! Theorem 2.11(1): the non-Q branch yields stationary ε-equilibria. -/
theorem paper_theorem_2_11_stationary_clause
    (table : paperTable ι) (M : ι → ι → ℝ)
    (hnormal : V1HasNormalPlayers M)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M)
    (hnotQ : ¬V1QMatrix M) :
    paperStationaryEpsilonEquilibria table := by
  sorry

/-! Theorem 2.11(2): the Q branch yields a unilateral-quitting sunspot
ε-equilibrium for every `ε>0`. -/
theorem paper_theorem_2_11_sunspot_clause
    (table : paperTable ι) (M : ι → ι → ℝ)
    (hnormal : V1HasNormalPlayers M)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M)
    (hQ : V1QMatrix M) :
    ∀ ε : ℝ, 0 < ε → ∃ profile : PaperSunspotProfile table,
      paperSunspotEpsilonEquilibrium table ε profile ∧
      (∀ t history, paperAtMostOneQuitter profile t history) := by
  sorry

/-! ## Section 2.5 — example -/

/-! The paper gives a four-player example with
`r¹=(0,4,-1,-1)`, `r²=(4,0,-1,-1)`, `r³=(-1,-1,0,4)`, and
`r⁴=(-1,-1,4,0)`, then describes two public-signal constructions, with
identities (5)--(8), and concludes that the first construction is a sunspot
`ε`-equilibrium and the second a sunspot `5ε`-equilibrium. These are
construction-specific probability statements, so they remain paper notes
rather than generic repository declarations. -/

/-! ## Section 3 — proof of Theorem 2.11 -/

/-! **Section 3.1 (paper definitions).** The paper defines the
`λ`-discounted quitting game, its payoff `γ^λ`, stationary payoff formula (9),
λ-discounted equilibrium, and invokes Fink/Takahashi and Bewley--Kohlberg to
choose a semi-algebraic stationary equilibrium branch `λ ↦ x^λ` with a
limit. The paper's discounted payoff is kept as a field of a paper-local game,
so it is not confused with the undiscounted terminal payoff. -/

/-! A discounted profile is a behavior profile of the quitting game. -/
abbrev PaperDiscountedProfile (table : paperTable ι) :=
  (quittingGame table.terminal).BehaviorProfile

/-! `PaperDiscountedGame.payoff λ x` is the paper's `γ^λ(x)`. -/
structure PaperDiscountedGame (table : paperTable ι) where
  payoff : ℝ → PaperDiscountedProfile table → Payoff ι

/-! A λ-discounted equilibrium satisfies every best-response inequality. -/
def paperDiscountedEquilibrium
    (table : paperTable ι) (game : PaperDiscountedGame table)
    (discount : ℝ) (profile : PaperDiscountedProfile table) : Prop :=
  ∀ who (deviation : (quittingGame table.terminal).BehaviorStrategy who),
    game.payoff discount profile who ≥
      game.payoff discount (Function.update profile who deviation) who

/-! Stationary specialization of the discounted equilibrium. -/
def paperStationaryDiscountedEquilibrium
    (table : paperTable ι) (game : PaperDiscountedGame table) (discount : ℝ)
    (root : ι → PMF Bool) : Prop :=
  paperDiscountedEquilibrium table game discount
    (quittingStationaryProfile table.terminal root)

/-! A semi-algebraic stationary equilibrium branch on `(0,1)` with a limit
as `λ→0+`. -/
structure PaperSemiAlgebraicSelection
    (table : paperTable ι) (game : PaperDiscountedGame table) where
  root : ℝ → ι → PMF Bool
  semiAlgebraic : Prop
  equilibrium : ∀ discount, 0 < discount → discount < 1 →
    paperStationaryDiscountedEquilibrium table game discount (root discount)
  limitRoot : ∃ limit : ι → PMF Bool,
    ∀ who action, Tendsto (fun discount => (root discount who) action)
      (𝓝[>] (0 : ℝ)) (𝓝 ((limit who) action))

/-! Existence of the paper's discounted-equilibrium selection. -/
def PaperHasSemiAlgebraicSelection
    (table : paperTable ι) (game : PaperDiscountedGame table) : Prop :=
  Nonempty (PaperSemiAlgebraicSelection table game)

/-! Fink/Takahashi plus Bewley--Kohlberg selection claim. -/
theorem paper_discounted_selection
    (table : paperTable ι) (game : PaperDiscountedGame table) :
    PaperHasSemiAlgebraicSelection table game := by
  sorry

/-! The paper's displayed stationary formula (9) is the defining payoff
formula supplied to `PaperDiscountedGame.payoff`; the record keeps that
formula paper-local while the proof invokes only the equilibrium and limit
fields above. -/

/-! **Lemma 3.1 (paper).** For
`D = conv(r̂¹,…,r̂ⁿ) ∩ ℝⁿ_≥0`, if `q̂ ∈ conv(r̂¹,…,r̂ⁿ)`, every solution
`(w,z)` of `LCP(R̂,q̂)` has `w ∈ ∂D`. -/

/-! `V1ColumnConvexHull M = conv{M_{·i}:i∈I}`. -/
def V1ColumnConvexHull (M : ι → ι → ℝ) : Set (ι → ℝ) :=
  convexHull ℝ (Set.range fun owner => fun who => M who owner)

/-! `V1D = conv{r̂¹,…,r̂ⁿ} ∩ ℝ^n_≥0`. -/
def V1D (M : ι → ι → ℝ) : Set (ι → ℝ) :=
  V1ColumnConvexHull M ∩ {w | ∀ who, 0 ≤ w who}

/-! `V1BoundaryPoint M w` means `w∈∂D`. -/
def V1BoundaryPoint (M : ι → ι → ℝ) (w : ι → ℝ) : Prop :=
  w ∈ frontier (V1D M)

/-! Lemma 3.1: if `q∈conv{r̂ᶦ}`, every LCP solution has `w∈∂D`. -/
theorem paper_lemma_3_1
    (M : ι → ι → ℝ) (q : ι → ℝ)
    (hq : q ∈ V1ColumnConvexHull M)
    (solution : ProjectiveLCPSolution M q) :
    V1BoundaryPoint M (fun who => solution.cemetery * q who +
      ∑ owner, solution.singleton owner * M who owner) := by
  sorry

/-! **Theorem 3.2 (paper).** For every `y∈∂D` and `ε>0`, there are
`w∈∂D`, vectors `w¹,…,wⁿ`, and simplex weights `z` satisfying (F.1)--(F.5).
The following paper-local structures spell out those five conditions. -/

/-! `V1Segment a b x` means `x∈conv{a,b}`. -/
def V1Segment (a b x : ι → ℝ) : Prop :=
  ∃ weight : ℝ, 0 ≤ weight ∧ weight ≤ 1 ∧
    ∀ who, x who = weight * a who + (1 - weight) * b who

/-! Simplex weights `z=(z₀,zᵢ)` satisfy `z₀+Σᵢzᵢ=1`. -/
structure V1SimplexWeights (ι : Type) [Fintype ι] [DecidableEq ι] where
  cemetery : ℝ
  singleton : ι → ℝ
  cemetery_nonneg : 0 ≤ cemetery
  singleton_nonneg : ∀ i, 0 ≤ singleton i
  total : cemetery + ∑ i, singleton i = 1

/-! Conditions (F.1)--(F.5) of Theorem 3.2 for `(M,y,ε)`. -/
structure V1BuildingBlock (M : ι → ι → ℝ) (y : ι → ℝ) (ε : ℝ) where
  w : ι → ℝ
  wi : ι → ι → ℝ
  z : V1SimplexWeights ι
  w_boundary : V1BoundaryPoint M w
  segment : ∀ i, V1Segment w (fun who => M who i) (wi i)
  not_w : ∀ i, wi i ≠ w
  lower : ∀ i who, -ε ≤ wi i who
  balance : ∀ who, w who = z.cemetery * y who +
    ∑ i, z.singleton i * wi i who
  complementary : ∀ i, z.singleton i > 0 → wi i i = 0
  nontrivial : 0 < ∑ i, z.singleton i

/-! The existential conclusion of Theorem 3.2. -/
def V1Theorem32Conclusion (M : ι → ι → ℝ) (y : ι → ℝ) (ε : ℝ) : Prop :=
  Nonempty (V1BuildingBlock M y ε)

/-! Theorem 3.2: every `y∈∂D` and `ε>0` admits a building block. -/
theorem paper_theorem_3_2
    (M : ι → ι → ℝ) {y : ι → ℝ} (hy : V1BoundaryPoint M y)
    {ε : ℝ} (hε : 0 < ε) : V1Theorem32Conclusion M y ε := by
  sorry

/-! **Lemmas 3.3 and 3.4 (paper).** Put `J_y={i:y_i=0}` and
`S(J_y)=conv{r̂^i:i∈J_y}`. In the two geometric cases
`conv(S(J_y),y)∩D={y}` and `conv(S(J_y),y)∩D ⊋ {y}`, respectively, the
paper proves the same `V1Theorem32Conclusion` represented above. -/

/-! `J_y={i:y_i=0}`. -/
def V1ZeroCoordinates (y : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => y i = 0)

/-! `V1SubfamilyHull M J = conv{M_{·i}:i∈J}`. -/
def V1SubfamilyHull (M : ι → ι → ℝ) (J : Finset ι) : Set (ι → ℝ) :=
  convexHull ℝ (Set.range fun i : J => fun who => M who i)

/-! Lemma 3.3: the singleton-intersection case yields (F.1)--(F.5). -/
theorem paper_lemma_3_3
    (M : ι → ι → ℝ) {y : ι → ℝ} (hy : V1BoundaryPoint M y)
    (hnot : y ∉ V1SubfamilyHull M (V1ZeroCoordinates y))
    (hpoint : (V1SubfamilyHull M (V1ZeroCoordinates y) ∪ {y}) ∩
      V1D M = {y}) {ε : ℝ} (hε : 0 < ε) :
    V1Theorem32Conclusion M y ε := by
  sorry

/-! Lemma 3.4: the strict-intersection case yields (F.1)--(F.5). -/
theorem paper_lemma_3_4
    (M : ι → ι → ℝ) {y : ι → ℝ} (hy : V1BoundaryPoint M y)
    (hnot : y ∉ V1SubfamilyHull M (V1ZeroCoordinates y))
    (hstrict : (V1SubfamilyHull M (V1ZeroCoordinates y) ∪ {y}) ∩
      V1D M ≠ {y}) {ε : ℝ} (hε : 0 < ε) :
    V1Theorem32Conclusion M y ε := by
  sorry

/-! **Theorem 3.5 (paper).** If `(X,d)` is complete and `f:X→X` has no fixed
point, then for every `c,C≥0` there are `K` and `x¹,…,xᴷ` with
`Σ_k d(xᵏ,f(xᵏ))>C` and `Σ_{k<K}d(xᵏ⁺¹,f(xᵏ))<c`. The paper proof uses
transfinite recursion. -/

/-! The finite-sequence conclusion of Theorem 3.5. -/
def V1ApproximationWitness {X : Type*} [PseudoMetricSpace X]
    (f : X → X) (c C : ℝ) : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∃ x : ℕ → X,
    C < (∑ k ∈ Finset.Icc 1 K, dist (x k) (f (x k))) ∧
    (∑ k ∈ Finset.Icc 1 (K - 1), dist (x (k + 1)) (f (x k))) < c

/-! Theorem 3.5: a fixed-point-free map admits large displacement with small
tracking error on a finite sequence. -/
theorem paper_theorem_3_5 {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] (f : X → X) (hfixed : ∀ x, f x ≠ x)
    (c C : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C) :
    V1ApproximationWitness f c C := by
  sorry

/-! **Lemmas 3.6--3.8 (paper).** For the kiloblock strategy `ξ*` built from
Theorem 3.2 and Theorem 3.5, the paper proves (i) its payoff is within
`2ε` of `w(yᴷ)` for normal players, (ii) continuation by any normal player
still terminates with probability at least `1-ε` before the final kiloblock,
and (iii) every pure deviation gains at most `5ε`. The following record is a
paper-local carrier for the induced quantities used in those statements. -/

/-! Induced payoff, deviation payoff, and continuation-termination data for
the paper's kiloblock strategy `ξ*`. -/
structure PaperKiloblockProfile (ι : Type) [Fintype ι] [DecidableEq ι] where
  payoff : Payoff ι
  unilateralPayoff : ι → ℝ
  continueTermination : ι → ℝ

/-! A kiloblock construction generated from a Theorem 3.2 building block. -/
structure PaperKiloblockConstruction
    (M : ι → ι → ℝ) (ε : ℝ) where
  profile : PaperKiloblockProfile ι
  target : Payoff ι
  buildingBlock : ∃ y, V1BoundaryPoint M y ∧ V1Theorem32Conclusion M y ε

/-! Lemma 3.6: for normal `i`, `|γ_i(ξ*)-w_i(yᴷ)|<2ε`. -/
theorem paper_lemma_3_6
    (M : ι → ι → ℝ) {ε : ℝ} (hε : 0 < ε)
    (construction : PaperKiloblockConstruction M ε) :
    ∀ i ∈ V1NormalCore M,
      |construction.profile.payoff i - construction.target i| < 2 * ε := by
  sorry

/-! Lemma 3.7: continuing by a normal player still terminates with probability
at least `1-ε` before the last kiloblock. -/
theorem paper_lemma_3_7
    (M : ι → ι → ℝ) {ε : ℝ} (hε : 0 < ε)
    (construction : PaperKiloblockConstruction M ε) :
    ∀ i ∈ V1NormalCore M,
      construction.profile.continueTermination i ≥ 1 - ε := by
  sorry

/-! Lemma 3.8: every pure deviation gains at most `5ε`. -/
theorem paper_lemma_3_8
    {M : ι → ι → ℝ} {ε : ℝ} (hε : 0 < ε)
    (construction : PaperKiloblockConstruction M ε) :
    ∀ i, construction.profile.unilateralPayoff i ≤
      construction.target i + 5 * ε := by
  sorry

/-! Section 3.4 concludes from Lemmas 3.6--3.8 that the constructed profile
is a sunspot `7ε`-equilibrium. -/

/-! Section 3.4: the constructed profile is a sunspot `7ε`-equilibrium. -/
theorem paper_section_3_4
    (table : paperTable ι) (profile : PaperSunspotProfile table)
    {ε : ℝ} (hε : 0 < ε) :
    paperSunspotEpsilonEquilibrium table (7 * ε) profile := by
  sorry

/-! ## Section 4 — sunspot payoff characterization -/

/-! **Definition (paper, Section 4).** A vector is a sunspot equilibrium
payoff if it is the limit of payoffs of sunspot ε-equilibria as ε↓0. -/

/-! A sunspot equilibrium payoff is a limit of payoffs of sunspot
ε-equilibria as `ε↓0`. -/
def paperSunspotEquilibriumPayoff
    (table : paperTable ι) (value : Payoff ι) : Prop :=
  ∃ profiles : ℕ → PaperSunspotProfile table,
    (∀ n : ℕ, paperSunspotEpsilonEquilibrium table
      ((n + 1 : ℝ)⁻¹) (profiles n)) ∧
    ∀ who, Tendsto (fun n => (profiles n).payoff who) atTop (𝓝 (value who))

/-! **M-matrix convention (paper).** Since the diagonal of `R̂` is zero, the
paper calls a Q-matrix an M-matrix when every row and every column has exactly
one positive entry. -/

/-! The v1 paper's M-matrix convention: Q, with exactly one positive entry in
each row and column. -/
def V1MMatrix (M : ι → ι → ℝ) : Prop :=
  V1QMatrix M ∧
    (∀ who, (Finset.filter (fun owner => 0 < M who owner) Finset.univ).card = 1) ∧
    (∀ owner, (Finset.filter (fun who => 0 < M who owner) Finset.univ).card = 1)

/-! **Theorem 4.1 (paper).** If `R̂` is an M-matrix, every vector in
`D~ = conv(r¹,…,rⁿ)∩ℝⁿ_≥0` is a sunspot equilibrium payoff. -/

/-! Theorem 4.1: an M-matrix makes every `v∈D~` a sunspot equilibrium payoff. -/
theorem paper_theorem_4_1
    (table : paperTable ι) (M : ι → ι → ℝ)
    (hM : V1MMatrix M) :
    ∀ value ∈ V1D M, paperSunspotEquilibriumPayoff table value := by
  sorry

/-! ## Section 5 — discussion and open problems -/

/-! The paper discusses stopping games, absorbing games, the need for a
uniform lower bound on quitting probabilities, finite-range recursions, the
inverse-positivity question for zero-diagonal Q-matrices, and the question
whether a column with strictly negative off-diagonal entries forces Q. These
are open-problem prose, not Lean theorem declarations. -/

end
end Literature.SolanAndSolan2020
