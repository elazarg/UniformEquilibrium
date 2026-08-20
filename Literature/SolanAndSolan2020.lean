import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses
import UniformEquilibrium.Quitting.Classification.LCP.NormalCore
import UniformEquilibrium.Quitting.Classification.LCP.StationaryExistence
import UniformEquilibrium.Quitting.Classification.LCP.StrategicTransport
import UniformEquilibrium.Quitting.Classification.TableExistenceBranches
import MathUE.CaristiFixedPoint
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Solan--Solan (2020) — paper-order audit

E. Solan and O. N. Solan, *Quitting Games and Linear Complementarity
Problems*, *Mathematics of Operations Research* 45(2), 434--454. The
accepted May 2018 manuscript is used where arXiv:1707.02598v1 differs from
the published result.

Two corrections are mathematically material. The arXiv v1 normal-player
display permits a self-witness and therefore retains every player under the
standing zero-diagonal assumption; the results require the published
distinct-witness recursion. The v1 building-block condition (F.1) mentions
only segments starting at `w`, although its final construction uses a segment
starting at `y`; the accepted manuscript states the necessary disjunction.
The literal v1 normal recursion remains as `printedNormalLayer` and
`printedNormalCore`, with its collapse proved below.

Public randomization is represented by an actual finite public-signal
stochastic game, and all payoffs and deviation payoffs below are induced by
behavior profiles. The stationary and LCP statements use the full payoff
table, including the nontermination payoff.
-/

namespace Literature.SolanAndSolan2020

open GameTheory StochasticGame QuittingLCPClassification
open Math.Probability
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

/-! `Table` carries `(r_S)_{S ⊆ I}` together with `r_∅`. -/
abbrev Table (ι : Type) [Fintype ι] [DecidableEq ι] :=
  QuittingPayoffTable ι

/-! Paper ε-equilibrium adapter:
`γ_i(x) ≥ γ_i(x'_i,x_{-i}) - ε`. -/
def EpsilonEquilibrium
    (table : Table ι) (ε : ℝ)
    (profile : (quittingGame table.terminal).BehaviorProfile) : Prop :=
  (quittingGame table.terminal).IsεAsymptoticNash table.terminalPayoff ε profile

/-! `StationaryEpsilonEquilibria table` means stationary ε-equilibria
exist for every `ε>0`. -/
abbrev StationaryEpsilonEquilibria (table : Table ι) : Prop :=
  table.StationaryεEquilibriumExistence

/-! **Assumption 2.1.** The paper assumes `r_i^i = 0` for every player.
This is a standing condition, not a theorem. -/

def SoloExitNormalized (table : Table ι) : Prop :=
  ∀ i : ι, table.terminal (quittingProjectiveSingletonTerminal i) i = 0

/-! The source's global payoff normalization `r_S∈[-1,1]^N`. -/
def TablePayoffsBounded (table : Table ι) : Prop :=
  (∀ S who, |table.terminal S who| ≤ 1) ∧
    ∀ who, |table.never who| ≤ 1

/-! The singleton-payoff matrix derived from the table. The subtraction by
the never payoff disappears under the subsequent solo normalization; hence,
under Assumption 2.1, this is extensionally the source matrix `R`. -/
abbrev DerivedMatrix (table : Table ι) : ι → ι → ℝ :=
  normalizedSoloMatrix table.zeroNeverReward

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

/-! The finite-support public randomizations used by the proof are exactly
coarsenings of the source's uniform `[0,1]` signal. We represent a coarsening
by a law on `ℕ`; its atoms are the publicly observed labels. -/

inductive PublicQuittingState (ι : Type) [Fintype ι] [DecidableEq ι]
    (Signal : Type) [Fintype Signal]
  | active (signal : Signal)
  | absorbed (quitters : {S : Finset ι // S.Nonempty})
deriving Fintype

/-! The induced public-signal quitting game. The current public label is the
live state. If everyone continues, the next label is sampled independently
from `signalLaw`; a nonempty quitter set is absorbing. The fixed initial label
only supplies a root before the first random draw and has no asymptotic payoff
effect. -/
def publicQuittingGame {Signal : Type} [Fintype Signal] (table : Table ι)
    (signalLaw : PMF Signal) :
    StochasticGame ι where
  State := PublicQuittingState ι Signal
  Act := fun _ => Bool
  stagePayoff := fun state _ who =>
    match state with
    | .active _ => table.never who
    | .absorbed quitters => table.terminal quitters who
  transition := fun state action =>
    match state with
    | .active _ =>
        if h : ({who | action who = true} : Finset ι).Nonempty then
          PMF.pure (.absorbed ⟨_, h⟩)
        else
          signalLaw.map PublicQuittingState.active
    | .absorbed quitters => PMF.pure (.absorbed quitters)
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

/-! Indicator and time-`t` mass of one absorbing quitter set. -/
def publicAbsorbedIndicator {Signal : Type} [Fintype Signal]
    (quitters : {S : Finset ι // S.Nonempty})
    (state : PublicQuittingState ι Signal) : ℝ := by
  classical
  exact if state = .absorbed quitters then 1 else 0

def publicAbsorbedMass
    {signalCount : ℕ} (table : Table ι)
    (signalLaw : PMF (Fin (signalCount + 1)))
    (strategy : (publicQuittingGame table signalLaw).BehaviorProfile)
    (t : ℕ) (quitters : {S : Finset ι // S.Nonempty}) : ℝ :=
  (publicQuittingGame table signalLaw).expectedStateValue strategy
    (.active 0) t (publicAbsorbedIndicator quitters)

/-! Limiting probability of absorption at one quitter set. -/
def publicAbsorbedMassLimit
    {signalCount : ℕ} (table : Table ι)
    (signalLaw : PMF (Fin (signalCount + 1)))
    (strategy : (publicQuittingGame table signalLaw).BehaviorProfile)
    (quitters : {S : Finset ι // S.Nonempty}) : ℝ :=
  ⨆ t, publicAbsorbedMass table signalLaw strategy t quitters

theorem publicAbsorbedMass_succ_ge
    {signalCount : ℕ} (table : Table ι)
    (signalLaw : PMF (Fin (signalCount + 1)))
    (strategy : (publicQuittingGame table signalLaw).BehaviorProfile)
    (t : ℕ) (quitters : {S : Finset ι // S.Nonempty}) :
    publicAbsorbedMass table signalLaw strategy t quitters ≤
      publicAbsorbedMass table signalLaw strategy (t + 1) quitters := by
  letI : Finite (publicQuittingGame table signalLaw).State :=
    inferInstanceAs (Finite (PublicQuittingState ι (Fin (signalCount + 1))))
  letI : ∀ i : ι, Finite ((publicQuittingGame table signalLaw).Act i) :=
    fun _ => inferInstanceAs (Finite Bool)
  rw [publicAbsorbedMass, publicAbsorbedMass,
    (publicQuittingGame table signalLaw).expectedStateValue_succ]
  unfold StochasticGame.expectedStateValue
  apply expect_mono
  intro history
  cases hstate : history.2 with
  | active signal =>
      rw [show publicAbsorbedIndicator quitters (.active signal) = 0 by
        simp [publicAbsorbedIndicator]]
      exact expect_nonneg _ _ fun action =>
        expect_nonneg _ _ fun state => by
          unfold publicAbsorbedIndicator
          split <;> norm_num
  | absorbed terminal =>
      simp [publicQuittingGame, publicAbsorbedIndicator]

theorem publicAbsorbedMass_le_one
    {signalCount : ℕ} (table : Table ι)
    (signalLaw : PMF (Fin (signalCount + 1)))
    (strategy : (publicQuittingGame table signalLaw).BehaviorProfile)
    (t : ℕ) (quitters : {S : Finset ι // S.Nonempty}) :
    publicAbsorbedMass table signalLaw strategy t quitters ≤ 1 := by
  letI : Finite (publicQuittingGame table signalLaw).State :=
    inferInstanceAs (Finite (PublicQuittingState ι (Fin (signalCount + 1))))
  letI : ∀ i : ι, Finite ((publicQuittingGame table signalLaw).Act i) :=
    fun _ => inferInstanceAs (Finite Bool)
  unfold publicAbsorbedMass StochasticGame.expectedStateValue
  calc
    expect ((publicQuittingGame table signalLaw).histDist strategy
        (.active 0) t)
        (fun history => publicAbsorbedIndicator quitters history.2) ≤
        expect ((publicQuittingGame table signalLaw).histDist strategy
          (.active 0) t) (fun _ => 1) := by
      apply expect_mono
      intro history
      unfold publicAbsorbedIndicator
      split <;> norm_num
    _ = 1 := expect_const _ _

theorem tendsto_publicAbsorbedMass
    {signalCount : ℕ} (table : Table ι)
    (signalLaw : PMF (Fin (signalCount + 1)))
    (strategy : (publicQuittingGame table signalLaw).BehaviorProfile)
    (quitters : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun t => publicAbsorbedMass table signalLaw strategy t quitters)
      atTop (nhds (publicAbsorbedMassLimit table signalLaw strategy quitters)) := by
  apply tendsto_atTop_ciSup
  · exact monotone_nat_of_le_succ fun t =>
      publicAbsorbedMass_succ_ge table signalLaw strategy t quitters
  · refine ⟨1, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact publicAbsorbedMass_le_one table signalLaw strategy t quitters

/-! The expected terminal payoff induced by a public profile. Absorption at
`S` changes the payoff from `r_∅` to `r_S`; the residual nonabsorption mass
therefore receives `r_∅` exactly as in the source. -/
def publicQuittingPayoff
    {signalCount : ℕ} (table : Table ι)
    (signalLaw : PMF (Fin (signalCount + 1)))
    (strategy : (publicQuittingGame table signalLaw).BehaviorProfile)
    (who : ι) : ℝ :=
  table.never who +
    ∑ quitters, publicAbsorbedMassLimit table signalLaw strategy quitters *
      (table.terminal quitters who - table.never who)

/-! A sunspot profile is a public-signal law together with an actual behavior
profile of the induced quitting game. Its payoff is computed from play. -/
structure SunspotProfile (table : Table ι) where
  signalCount : ℕ
  signalLaw : PMF (Fin (signalCount + 1))
  strategy : (publicQuittingGame table signalLaw).BehaviorProfile

/-! The payoff generated by a sunspot profile. -/
def SunspotProfile.payoff {table : Table ι}
    (profile : SunspotProfile table) : Payoff ι :=
  publicQuittingPayoff table profile.signalLaw profile.strategy

/-! `ξ` is a sunspot ε-equilibrium iff
`γ_i(ξ) ≥ γ_i(ξ'_i,ξ_{-i})-ε` for every behavior deviation. -/
def SunspotEpsilonEquilibrium
    (table : Table ι) (ε : ℝ)
    (profile : SunspotProfile table) : Prop :=
  (publicQuittingGame table profile.signalLaw).IsεAsymptoticNash
    (publicQuittingPayoff table profile.signalLaw) ε profile.strategy

/-! At every live public history, at most one player assigns positive
probability to Quit. -/
def AtMostOneQuitter {table : Table ι}
    (profile : SunspotProfile table) : Prop :=
  ∀ t (history : (publicQuittingGame table profile.signalLaw).Hist t),
    match history.2 with
    | .active _ =>
        (Finset.filter (fun who =>
          0 < ((profile.strategy who t history) true).toReal)
          Finset.univ).card ≤ 1
    | .absorbed _ => True

/-! **Theorem 2.4 (paper).** Every quitting game admits a sunspot
ε-equilibrium for every `ε > 0`. -/

theorem theorem2_4 (table : Table ι)
    (hnormalized : SoloExitNormalized table)
    (hbounded : TablePayoffsBounded table) :
    ∀ ε : ℝ, 0 < ε → ∃ profile : SunspotProfile table,
      SunspotEpsilonEquilibrium table ε profile := by
  sorry

/-! ## Section 2.3 — recursively normal players -/

/-! **Definition 2.5 (paper).** `I₀=I` and
`I_{l+1}={i∈I_l : ∃j∈I_l, r^j_i ≤ 0}`; `I* = ⋂_l I_l` is the set of normal
players and its complement is the set of abnormal players. This is the
literal v1 display, including its omitted distinctness condition. -/

/-! `I_l` is the intended distinct-witness normal-player layer. -/
abbrev NormalLayer (M : ι → ι → ℝ) := normalLayer M
/-! `I* = ⋂_l I_l`, represented as the finite recursive core. -/
abbrev NormalCore (M : ι → ι → ℝ) := normalCore M

/-! `NormalMatrix M` is the principal matrix on `I*`. -/
abbrev NormalMatrix (M : ι → ι → ℝ) := normalPlayerMatrix M

/-! `I* ≠ ∅`. -/
abbrev HasNormalPlayers (M : ι → ι → ℝ) : Prop :=
  QuittingLCPClassification.HasNormalPlayers M

/-! `I* = ∅`, i.e. every player is abnormal. -/
abbrev AllPlayersAbnormal (M : ι → ι → ℝ) : Prop :=
  QuittingLCPClassification.AllPlayersAbnormal M

/-! Equation (1) and Equation (2) (paper): if `i` is in a layer/core and
`j` is outside it, then `r^j_i > 0`. The imported
`normalCore_entry_pos_of_notMem` proves the corresponding final,
distinct-witness recursion; the literal v1 recursion collapses under
`SoloExitNormalized`, as recorded below. -/

/-! Literal v1 recursion on a solo-normalized table retains every player. -/
theorem printedRecursion_collapse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    printedNormalCore (normalizedSoloMatrix reward) = Finset.univ :=
  printedNormalCore_normalized_eq_univ reward

/-! Under Assumption 2.1, the table's singleton-payoff matrix is exactly the
normalized matrix used by the production LCP classification. -/
theorem normalizedSoloMatrix_zeroNeverReward_eq_singletonMatrix
    (table : Table ι) (hnormalized : SoloExitNormalized table) :
    normalizedSoloMatrix table.zeroNeverReward = table.singletonMatrix := by
  funext who owner
  simp only [normalizedSoloMatrix, QuittingPayoffTable.singletonMatrix,
    normalizedQuittingPayoffTable, QuittingPayoffTable.translate,
    repositoryQuittingPayoffTable,
    QuittingLCPClassification.quittingSoloBaseline,
    QuittingPayoffTable.zeroNeverReward]
  rw [hnormalized who]
  ring

/-! Lemma 2.2 adapter: `∃i∈I*, r^i≥0` implies stationary ε-equilibrium
existence for every `ε>0`. -/
theorem lemma2_2
    (table : Table ι)
    (hnormal : ∃ i ∈ NormalCore (DerivedMatrix table),
      ∀ who, 0 ≤ DerivedMatrix table who i) :
    StationaryEpsilonEquilibria table := by
  obtain ⟨owner, howner, hcolumn⟩ := hnormal
  obtain ⟨blocker, _, hne, hblocker⟩ :=
    exists_core_blocker_of_mem_normalCore (DerivedMatrix table) howner
  have hvalue :=
    isQuittingStationaryUniformEquilibriumPayoff_of_nonnegative_column
      table.zeroNeverReward hne
        (fun who _ => hcolumn who) hblocker
  change table.StationaryεEquilibriumExistence
  rw [QuittingPayoffTable.stationaryεEquilibriumExistence_iff]
  exact hvalue.hasApproximateEquilibria

/-! **Lemma 2.6 (paper).** If all players are abnormal, a stationary
ε-equilibrium exists for every `ε > 0`. The paper proof also uses Lemma 2.2
when the last nonempty layer is reached; the exact strategic min-max-to-table
adapter is not available in this lane. -/

/-! Lemma 2.6: `I*=∅` implies stationary ε-equilibrium existence. -/
theorem lemma2_6
    (table : Table ι)
    (habnormal : AllPlayersAbnormal (DerivedMatrix table)) :
    StationaryEpsilonEquilibria table := by
  obtain ⟨value, hvalue⟩ :=
    exists_stationaryUniformEquilibriumPayoff_of_allPlayersAbnormal
      table.zeroNeverReward habnormal
  change table.StationaryεEquilibriumExistence
  rw [QuittingPayoffTable.stationaryεEquilibriumExistence_iff]
  exact hvalue.hasApproximateEquilibria

/-! **Definition 2.7 (paper remark).** For an `n×n` matrix `R` and `q`, the
paper recalls the textbook LCP: find `w,z ≥ 0` with `w=q+Rz` and
`w_i z_i=0`. -/

/-! The paper's projective LCP `LCP(M,q)` is solvable. -/
abbrev LCP (M : ι → ι → ℝ) (q : ι → ℝ) : Prop :=
  HasProjectiveLCPSolution M q

/-! **Definition 2.8 (paper).** `R` is a Q-matrix when the paper's
projective/simplex LCP `LCP(R,q)` has a solution for every `q`. -/

/-! `QMatrix M ↔ ∀q, LCP(M,q)` is solvable. -/
abbrev QMatrix (M : ι → ι → ℝ) : Prop := IsProjectiveQMatrix M

/-! **Example 2.9 (paper).** For the displayed cyclic `3×3` sign pattern
with zero diagonal, Berman--Plemmons implies Q iff the determinant is
positive. This numerical example is retained here as paper text; no
repository matrix-example declaration is introduced. -/

/-! **Lemma 2.10 (paper).** If the projective LCP with right-hand side zero
has a solution with `z₀<1`, then a stationary ε-equilibrium exists for every
positive ε. -/

/-! Lemma 2.10: a zero-LCP solution with cemetery weight `<1` yields
stationary ε-equilibria for every `ε>0`. -/
theorem lemma2_10
    (table : Table ι)
    (h : HasNontrivialZeroProjectiveLCPSolution
      (NormalMatrix (DerivedMatrix table))) :
    StationaryEpsilonEquilibria table := by
  have hhomogeneous : HasHomogeneousSimplexSolution
      (normalizedNormalPlayerMatrix table.zeroNeverReward) := by
    rw [hasNontrivialZeroProjectiveLCPSolution_iff_homogeneous] at h
    exact h
  have hnormal : QuittingLCPClassification.HasNormalPlayers
      (normalizedSoloMatrix table.zeroNeverReward) := by
    obtain ⟨weight, _, _⟩ := hhomogeneous
    by_contra hempty
    unfold QuittingLCPClassification.HasNormalPlayers at hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    haveI : IsEmpty (normalCore
        (normalizedSoloMatrix table.zeroNeverReward)) := by
      rw [hempty]
      infer_instance
    have htotal := weight.property.2
    simp at htotal
  obtain ⟨value, hvalue⟩ :=
    exists_stationaryUniformEquilibriumPayoff_of_homogeneousMatrixBranch
      table.zeroNeverReward
        { normal_nonempty := hnormal, homogeneous := hhomogeneous }
  change table.StationaryεEquilibriumExistence
  rw [QuittingPayoffTable.stationaryεEquilibriumExistence_iff]
  exact hvalue.hasApproximateEquilibria

/-! **Theorem 2.11 (paper).** Assume the normal-player set is nonempty and
the zero-right-hand-side projective LCP has no nontrivial solution. If the
normal-player matrix is not Q, then stationary ε-equilibria exist for every
positive ε. If it is Q, then a sunspot ε-equilibrium exists for every
positive ε in which at most one player quits with positive probability at
each stage. The paper-local public-signal relation is the
`SunspotProfile` relation above. -/

/-! Theorem 2.11(1): the non-Q branch yields stationary ε-equilibria. -/
theorem theorem2_11_stationary
    (table : Table ι)
    (hnormal : HasNormalPlayers (DerivedMatrix table))
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution
      (NormalMatrix (DerivedMatrix table)))
    (hnotQ : ¬QMatrix (NormalMatrix (DerivedMatrix table))) :
    StationaryEpsilonEquilibria table := by
  have hnoHomogeneous : ¬HasHomogeneousSimplexSolution
      (normalizedNormalPlayerMatrix table.zeroNeverReward) := by
    rw [← hasNontrivialZeroProjectiveLCPSolution_iff_homogeneous]
    exact hzero
  have hnotStandard : ¬IsStandardQMatrix
      (normalizedNormalPlayerMatrix table.zeroNeverReward) := by
    rw [← isProjectiveQMatrix_iff_standard_of_noHomogeneous
      (normalizedNormalPlayerMatrix table.zeroNeverReward) hnoHomogeneous]
    exact hnotQ
  obtain ⟨value, hvalue⟩ :=
    exists_stationaryUniformEquilibriumPayoff_of_ordinaryNonQMatrixBranch
      table.zeroNeverReward
        { normal_nonempty := hnormal
          no_homogeneous := hnoHomogeneous
          normal_not_standardQ := hnotStandard }
  change table.StationaryεEquilibriumExistence
  rw [QuittingPayoffTable.stationaryεEquilibriumExistence_iff]
  exact hvalue.hasApproximateEquilibria

/-! Theorem 2.11(2): the Q branch yields a unilateral-quitting sunspot
ε-equilibrium for every `ε>0`. -/
theorem theorem2_11_sunspot
    (table : Table ι)
    (hnormalized : SoloExitNormalized table)
    (hbounded : TablePayoffsBounded table)
    (hnormal : HasNormalPlayers (DerivedMatrix table))
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution
      (NormalMatrix (DerivedMatrix table)))
    (hQ : QMatrix (NormalMatrix (DerivedMatrix table))) :
    ∀ ε : ℝ, 0 < ε → ∃ profile : SunspotProfile table,
      SunspotEpsilonEquilibrium table ε profile ∧
      AtMostOneQuitter profile := by
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
limit. The checked carrier below uses the repository's analytic Bellman germ
after playerwise normalization of the nontermination payoff. -/

/-! Subtracting `r^∅` identifies the paper's discounted game with the
repository quitting game `quittingGame table.zeroNeverReward`, up to the
playerwise payoff constant `r^∅`. -/
abbrev DiscountedGame (table : Table ι) :=
  quittingGame table.zeroNeverReward

/-! A semi-algebraic stationary equilibrium branch on `(0,1)` with a limit
as `λ→0+`. -/
abbrev SemiAlgebraicSelection (table : Table ι) :=
  (DiscountedGame table).AnalyticBellmanGerm

/-! Existence of the paper's discounted-equilibrium selection. -/
abbrev HasSemiAlgebraicSelection (table : Table ι) : Prop :=
  Nonempty ((DiscountedGame table).AnalyticBellmanGerm)

/-! Fink/Takahashi plus Bewley--Kohlberg selection claim. -/
theorem discountedSelection
    (table : Table ι) : HasSemiAlgebraicSelection table :=
  nonempty_analyticBellmanGerm_quittingGame table.zeroNeverReward

/-! The displayed stationary formula (9) is the stationary specialization of
the Bellman values on this germ. The formal carrier uses the reusable checked
stochastic-game semantics rather than an unconstrained payoff field. -/

/-! **Lemma 3.2 (published paper).** For
`D = conv(r̂¹,…,r̂ⁿ) ∩ ℝⁿ_≥0`, if `q̂` is in the column hull but not
the nonnegative orthant, every solution `(w,z)` of `LCP(R̂,q̂)` has
`w ∈ D₀`. -/

/-! `ColumnConvexHull M = conv{M_{·i}:i∈I}`. -/
def ColumnConvexHull (M : ι → ι → ℝ) : Set (ι → ℝ) :=
  convexHull ℝ (Set.range fun owner => fun who => M who owner)

/-! `D = conv{r̂¹,…,r̂ⁿ} ∩ ℝ^n_≥0`. -/
def D (M : ι → ι → ℝ) : Set (ι → ℝ) :=
  ColumnConvexHull M ∩ {w | ∀ who, 0 ≤ w who}

/-! The source normalizes every payoff coordinate to `[-1,1]`. -/
def MatrixPayoffsBounded (M : ι → ι → ℝ) : Prop :=
  ∀ who owner, |M who owner| ≤ 1

/-! `D₀` consists of the points of `D` with a zero coordinate. The paper
only observes that this set lies in the relative boundary of `D`; replacing
it by the ambient frontier would be vacuous because `n` columns in `ℝⁿ`
have lower-dimensional convex hull. -/
def DZero (M : ι → ι → ℝ) (w : ι → ℝ) : Prop :=
  w ∈ D M ∧ ∃ who, w who = 0

/-! The coordinatewise nonnegative orthant. -/
def NonnegativeOrthant (ι : Type) :=
  {w : ι → ℝ | ∀ who, 0 ≤ w who}

omit [DecidableEq ι] in
theorem isClosed_D (M : ι → ι → ℝ) : IsClosed (D M) := by
  apply IsClosed.inter
  · exact (Set.finite_range (fun owner => fun who => M who owner)).isClosed_convexHull ℝ
  · rw [show {w : ι → ℝ | ∀ who, 0 ≤ w who} =
        ⋂ who, {w | 0 ≤ w who} by ext; simp]
    exact isClosed_iInter fun who => isClosed_le
      (continuous_const : Continuous (fun _ : (ι → ℝ) => (0 : ℝ)))
      (continuous_apply who)

omit [Fintype ι] [DecidableEq ι] in
theorem convex_D (M : ι → ι → ℝ) : Convex ℝ (D M) := by
  apply (convex_convexHull ℝ _).inter
  rw [show {w : ι → ℝ | ∀ who, 0 ≤ w who} =
      ⋂ who, (LinearMap.proj (R := ℝ) who) ⁻¹' Set.Ici 0 by ext; simp]
  apply convex_iInter
  intro who
  exact (convex_Ici (𝕜 := ℝ) (0 : ℝ)).linear_preimage
    (LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) who)

omit [Fintype ι] [DecidableEq ι] in
theorem mem_D_of_DZero {M : ι → ι → ℝ} {y : ι → ℝ}
    (hy : DZero M y) : y ∈ D M :=
  hy.1

omit [DecidableEq ι] in
private theorem frontier_nonnegativeOrthant_has_zero
    {w : ι → ℝ} (hw : w ∈ frontier (NonnegativeOrthant ι)) :
    w ∈ NonnegativeOrthant ι ∧ ∃ who, w who = 0 := by
  have hclosed : IsClosed (NonnegativeOrthant ι) := by
    rw [NonnegativeOrthant, show {x : ι → ℝ | ∀ who, 0 ≤ x who} =
      ⋂ who, {x | 0 ≤ x who} by ext; simp]
    exact isClosed_iInter fun who => isClosed_le
      (continuous_const : Continuous (fun _ : (ι → ℝ) => (0 : ℝ)))
      (continuous_apply who)
  have hwmem : w ∈ NonnegativeOrthant ι := hclosed.frontier_subset hw
  refine ⟨hwmem, ?_⟩
  by_contra hzero
  push Not at hzero
  have hpos : ∀ who, 0 < w who := fun who =>
    lt_of_le_of_ne (hwmem who) (Ne.symm (hzero who))
  have hwInterior : w ∈ interior (NonnegativeOrthant ι) := by
    have heq : {x : ι → ℝ | ∀ who, 0 ≤ x who} =
        Set.univ.pi (fun _ => Set.Ici 0) := by
      ext x
      constructor
      · intro hx who _
        exact hx who
      · intro hx who
        exact hx who (Set.mem_univ who)
    rw [NonnegativeOrthant, heq, interior_pi_set Set.finite_univ,
      Set.mem_pi]
    intro who _
    simpa only [interior_Ici, Set.mem_Ioi] using hpos who
  exact (mem_frontier_iff_notMem_interior hwmem).1 hw hwInterior

private theorem exists_frontier_on_segment_of_mem_notMem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {u v : E} (hu : u ∈ s) (hv : v ∉ s) :
    ∃ w ∈ segment ℝ u v, w ∈ frontier s := by
  by_contra hnone
  push Not at hnone
  have havoid : segment ℝ u v ⊆ (frontier s)ᶜ := fun w hw => hnone w hw
  rw [compl_frontier_eq_union_interior] at havoid
  have huInterior : u ∈ interior s := by
    by_contra huNot
    exact hnone u (left_mem_segment ℝ u v)
      ((mem_frontier_iff_notMem_interior hu).2 huNot)
  have hvInterior : v ∈ interior sᶜ := by
    by_contra hvNot
    exact hnone v (right_mem_segment ℝ u v) <| by
      rw [← frontier_compl]
      exact (mem_frontier_iff_notMem_interior (show v ∈ sᶜ from hv)).2 hvNot
  have hdisjoint : Disjoint (interior s) (interior sᶜ) :=
    (Set.disjoint_compl_right_iff_subset.mpr fun _ hx => hx).mono
      interior_subset interior_subset
  have hsubset :=
    (convex_segment u v).isPreconnected.subset_left_of_subset_union
      isOpen_interior isOpen_interior hdisjoint havoid
      ⟨u, left_mem_segment ℝ u v, huInterior⟩
  exact hv (interior_subset (hsubset (right_mem_segment ℝ u v)))

private theorem endpoint_not_mem_tail_segment
    {E : Type*} [AddCommGroup E] [Module ℝ E] {y p c : E}
    (hp : p ∈ segment ℝ y c) (hpy : p ≠ y) (hcy : c ≠ y) :
    y ∉ segment ℝ p c := by
  rw [segment_eq_image_lineMap] at hp ⊢
  obtain ⟨t, ht, rfl⟩ := hp
  rintro ⟨s, hs, heq⟩
  have htpos : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro htzero
    apply hpy
    rw [← htzero]
    simp [AffineMap.lineMap_apply_module]
  have hcoeff : 0 < s + (1 - s) * t := by
    have hs0 := hs.1
    have hs1 := hs.2
    by_cases hspos : 0 < s
    · positivity
    · have hs0eq : s = 0 := le_antisymm (le_of_not_gt hspos) hs0
      rw [hs0eq]
      simpa using htpos
  have hv : (s + (1 - s) * t) • (c - y) = 0 := by
    rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module] at heq
    linear_combination (norm := module) heq
  have hcsub : c - y = 0 :=
    (smul_eq_zero.mp hv).resolve_left (ne_of_gt hcoeff)
  exact hcy (sub_eq_zero.mp hcsub)

/-! Lemma 3.2: `q∈conv{r̂ᶦ} ∖ ℝⁿ_≥0` forces every LCP residual into
`D₀`. -/
omit [DecidableEq ι] in
theorem lemma3_1
    (M : ι → ι → ℝ) (q : ι → ℝ)
    (hq : q ∈ ColumnConvexHull M)
    (hqNegative : q ∉ NonnegativeOrthant ι)
    (solution : ProjectiveLCPSolution M q) :
    DZero M (fun who => solution.cemetery * q who +
      ∑ owner, solution.singleton owner * M who owner) := by
  let weight : Option ι → ℝ
    | none => solution.cemetery
    | some i => solution.singleton i
  let point : Option ι → (ι → ℝ)
    | none => q
    | some i => fun who => M who i
  have hweight_nonneg (a : Option ι) : 0 ≤ weight a := by
    cases a with
    | none => exact solution.cemetery_nonneg
    | some i => exact solution.singleton_nonneg i
  have hweight_total : ∑ a : Option ι, weight a = 1 := by
    simp [weight, solution.total]
  have hpoint (a : Option ι) : point a ∈ ColumnConvexHull M := by
    cases a with
    | none => exact hq
    | some i => exact subset_convexHull ℝ _ ⟨i, rfl⟩
  have hconvex : (∑ a : Option ι, weight a • point a) ∈
      ColumnConvexHull M := by
    exact (convex_convexHull ℝ _).sum_mem
      (fun a _ => hweight_nonneg a) hweight_total (fun a _ => hpoint a)
  have hresidual : (fun who => solution.cemetery * q who +
      ∑ owner, solution.singleton owner * M who owner) ∈
      ColumnConvexHull M := by
    convert hconvex using 1
    funext who
    simp [weight, point, smul_eq_mul]
  have hwD : (fun who => solution.cemetery * q who +
      ∑ owner, solution.singleton owner * M who owner) ∈ D M :=
    ⟨hresidual, solution.residual_nonneg⟩
  have hsumNonneg : 0 ≤ ∑ owner, solution.singleton owner :=
    Finset.sum_nonneg fun owner _ => solution.singleton_nonneg owner
  have hcemeteryLe : solution.cemetery ≤ 1 := by
    linarith [solution.total]
  have hcemeteryLt : solution.cemetery < 1 := by
    apply lt_of_le_of_ne hcemeteryLe
    intro hcemetery
    have hsumZero : ∑ owner, solution.singleton owner = 0 := by
      linarith [solution.total]
    have hsingletonZero (owner : ι) : solution.singleton owner = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => solution.singleton_nonneg i)).mp hsumZero owner
        (Finset.mem_univ owner)
    apply hqNegative
    intro who
    simpa only [hcemetery, one_mul, hsingletonZero, zero_mul,
      Finset.sum_const_zero, add_zero] using solution.residual_nonneg who
  have hsumPositive : 0 < ∑ owner, solution.singleton owner := by
    linarith [solution.total]
  obtain ⟨who, _, hwho⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun i _ => solution.singleton_nonneg i)).mp hsumPositive
  refine ⟨hwD, who, ?_⟩
  exact (mul_eq_zero.mp (solution.complementary who)).resolve_left
    (ne_of_gt hwho)

/-! **Theorem 3.3 (published paper).** For every `y∈D₀` and `ε>0`,
there are `w∈D₀`, vectors `w¹,…,wⁿ`, and simplex weights `z`
satisfying (F.1)--(F.5).
The following paper-local structures spell out those five conditions. -/

/-! `Segment a b x` means `x∈conv{a,b}`. -/
def Segment (a b x : ι → ℝ) : Prop :=
  ∃ weight : ℝ, 0 ≤ weight ∧ weight ≤ 1 ∧
    ∀ who, x who = weight * a who + (1 - weight) * b who

omit [Fintype ι] [DecidableEq ι] in
private theorem segment_of_mem_segment {a b x : ι → ℝ}
    (hx : x ∈ segment ℝ a b) : Segment a b x := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨1 - t, sub_nonneg.mpr ht.2, by linarith [ht.1], ?_⟩
  intro who
  simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in
private theorem mem_segment_of_Segment {a b x : ι → ℝ}
    (hx : Segment a b x) : x ∈ segment ℝ a b := by
  obtain ⟨weight, hweight0, hweight1, hx⟩ := hx
  rw [segment_eq_image_lineMap]
  refine ⟨1 - weight, ⟨by linarith, by linarith⟩, ?_⟩
  ext who
  rw [hx]
  simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-! `J_y={i:y_i=0}`. -/
def ZeroCoordinates (y : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => y i = 0)

/-! `SubfamilyHull M J = conv{M_{·i}:i∈J}`. -/
def SubfamilyHull (M : ι → ι → ℝ) (J : Finset ι) : Set (ι → ℝ) :=
  convexHull ℝ (Set.range fun i : J => fun who => M who i)

/-! Simplex weights `z=(z₀,zᵢ)` satisfy `z₀+Σᵢzᵢ=1`. -/
structure SimplexWeights (ι : Type) [Fintype ι] [DecidableEq ι] where
  cemetery : ℝ
  singleton : ι → ℝ
  cemetery_nonneg : 0 ≤ cemetery
  singleton_nonneg : ∀ i, 0 ≤ singleton i
  total : cemetery + ∑ i, singleton i = 1

/-! Conditions (F.1)--(F.5) of the published Theorem 3.3 for `(M,y,ε)`.
The published condition (F.1) allows the segment containing `wⁱ` to start
at either `w` or `y`. This disjunction is essential in the second case of the
proof; the arXiv v1 statement omitted it even though its printed construction
uses the segment starting at `y`. -/
structure BuildingBlock (M : ι → ι → ℝ) (y : ι → ℝ) (ε : ℝ) where
  w : ι → ℝ
  wi : ι → ι → ℝ
  z : SimplexWeights ι
  w_boundary : DZero M w
  approach : ∀ i,
    (Segment w (fun who => M who i) (wi i) ∧ wi i ≠ w) ∨
      (Segment y (fun who => M who i) (wi i) ∧ wi i ≠ y)
  lower : ∀ i who, -ε ≤ wi i who
  balance : ∀ who, w who = z.cemetery * y who +
    ∑ i, z.singleton i * wi i who
  complementary : ∀ i, z.singleton i > 0 → wi i i = 0
  nontrivial : 0 < ∑ i, z.singleton i

/-! The existential conclusion of Theorem 3.2. -/
def Theorem32Conclusion (M : ι → ι → ℝ) (y : ι → ℝ) (ε : ℝ) : Prop :=
  Nonempty (BuildingBlock M y ε)

private theorem subfamilyHull_weights
    (M : ι → ι → ℝ) (J : Finset ι) {y : ι → ℝ}
    (hy : y ∈ SubfamilyHull M J) :
    ∃ weight : ι → ℝ, (∀ i, 0 ≤ weight i) ∧
      (∑ i, weight i) = 1 ∧
      (∀ i, 0 < weight i → i ∈ J) ∧
      (∀ who, ∑ i, weight i * M who i = y who) := by
  rw [SubfamilyHull, mem_convexHull_iff_exists_fintype] at hy
  obtain ⟨κ, hκ, a, point, ha, hatotal, hpoint, hsum⟩ := hy
  letI : Fintype κ := hκ
  choose owner howner using hpoint
  let weight : ι → ℝ := fun i =>
    ∑ k, if (owner k : ι) = i then a k else 0
  refine ⟨weight, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Finset.sum_nonneg fun k _ => by split <;> simp_all
  · simp only [weight]
    calc
      ∑ i, ∑ k, (if (owner k : ι) = i then a k else 0) =
          ∑ k, ∑ i, (if (owner k : ι) = i then a k else 0) := Finset.sum_comm
      _ = ∑ k, a k := by
        apply Finset.sum_congr rfl
        intro k _
        exact Fintype.sum_ite_eq (owner k : ι) (fun _ => a k)
      _ = 1 := hatotal
  · intro i hi
    by_contra hnot
    have hne (k : κ) : (owner k : ι) ≠ i := fun heq =>
      hnot (heq ▸ (owner k).property)
    simp [weight, hne] at hi
  · intro who
    have happly := congr_fun hsum who
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at happly
    simp only [weight, Finset.sum_mul]
    calc
      ∑ i, ∑ k, (if (owner k : ι) = i then a k else 0) * M who i =
          ∑ k, ∑ i, (if (owner k : ι) = i then a k else 0) * M who i :=
        Finset.sum_comm
      _ = ∑ k, a k * M who (owner k) := by
        apply Finset.sum_congr rfl
        intro k _
        simpa only [ite_mul, zero_mul] using
          (Fintype.sum_ite_eq (owner k : ι) (fun i => a k * M who i))
      _ = y who := by
        rw [← happly]
        apply Finset.sum_congr rfl
        intro k _
        rw [← howner k]

private theorem column_ne_of_no_nontrivial_zero_solution
    (M : ι → ι → ℝ) {y : ι → ℝ} (hy : y ∈ D M)
    (hdiag : ∀ i, M i i = 0)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M) (owner : ι) :
    (fun who => M who owner) ≠ y := by
  intro heq
  apply hzero
  let solution : ProjectiveLCPSolution M (0 : ι → ℝ) :=
    { cemetery := 0
      singleton := fun i => if i = owner then 1 else 0
      cemetery_nonneg := le_rfl
      singleton_nonneg := fun i => by split <;> simp_all
      total := by simp
      residual_nonneg := fun who => by
        simp only [zero_mul, zero_add, ite_mul, one_mul, zero_mul,
          Fintype.sum_ite_eq']
        rw [congr_fun heq who]
        exact hy.2 who
      complementary := fun who => by
        by_cases hwho : who = owner
        · subst who
          simp [hdiag]
        · simp [hwho] }
  exact ⟨solution, by simp [solution]⟩

private theorem column_not_mem_D_of_no_nontrivial_zero_solution
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M) (owner : ι) :
    (fun who => M who owner) ∉ D M := by
  intro hcolumn
  apply hzero
  let solution : ProjectiveLCPSolution M (0 : ι → ℝ) :=
    { cemetery := 0
      singleton := fun i => if i = owner then 1 else 0
      cemetery_nonneg := le_rfl
      singleton_nonneg := fun i => by split <;> simp_all
      total := by simp
      residual_nonneg := fun who => by
        simp only [zero_mul, zero_add, ite_mul, one_mul, zero_mul,
          Fintype.sum_ite_eq']
        exact hcolumn.2 who
      complementary := fun who => by
        by_cases hwho : who = owner
        · subst who
          simp [hdiag]
        · simp [hwho] }
  exact ⟨solution, by simp [solution]⟩

/-! The first case in the proof of Theorem 3.2: `y` already lies in the
convex hull of the columns whose own coordinate vanishes. -/
theorem theorem32Conclusion_of_mem_subfamilyHull
    (M : ι → ι → ℝ) {y : ι → ℝ} (hy : DZero M y)
    (hbound : MatrixPayoffsBounded M) (hdiag : ∀ i, M i i = 0)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M)
    (hmember : y ∈ SubfamilyHull M (ZeroCoordinates y))
    {ε : ℝ} (hε : 0 < ε) : Theorem32Conclusion M y ε := by
  let δ := min ε 1
  have hδpos : 0 < δ := lt_min hε zero_lt_one
  have hδnonneg : 0 ≤ δ := hδpos.le
  have hδε : δ ≤ ε := min_le_left _ _
  have hδone : δ ≤ 1 := min_le_right _ _
  have hyD : y ∈ D M := mem_D_of_DZero hy
  obtain ⟨weight, hweight, htotal, hsupport, haverage⟩ :=
    subfamilyHull_weights M (ZeroCoordinates y) hmember
  let wi : ι → ι → ℝ := fun i who =>
    (1 - δ) * y who + δ * M who i
  let z : SimplexWeights ι :=
    { cemetery := 0
      singleton := weight
      cemetery_nonneg := le_rfl
      singleton_nonneg := hweight
      total := by simpa using htotal }
  refine ⟨{
    w := y
    wi := wi
    z := z
    w_boundary := hy
    approach := ?_
    lower := ?_
    balance := ?_
    complementary := ?_
    nontrivial := ?_ }⟩
  · intro i
    left
    constructor
    · refine ⟨1 - δ, sub_nonneg.mpr hδone, by linarith, ?_⟩
      intro who
      simp only [wi]
      ring
    · intro hwi
      apply column_ne_of_no_nontrivial_zero_solution M hyD hdiag hzero i
      funext who
      have hcoordinate := congr_fun hwi who
      simp only [wi] at hcoordinate
      nlinarith
  · intro i who
    have hMlower : -1 ≤ M who i := (abs_le.mp (hbound who i)).1
    have hscaled : -δ ≤ δ * M who i := by
      nlinarith [mul_nonneg hδnonneg (show 0 ≤ M who i + 1 by linarith)]
    have hy_nonneg := hyD.2 who
    have hfactor : 0 ≤ 1 - δ := sub_nonneg.mpr hδone
    dsimp only [wi]
    nlinarith [mul_nonneg hfactor hy_nonneg]
  · intro who
    simp only [z, zero_mul, zero_add, wi]
    symm
    calc
      ∑ i, weight i * ((1 - δ) * y who + δ * M who i) =
          (1 - δ) * y who * (∑ i, weight i) +
            δ * (∑ i, weight i * M who i) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.sum_mul]
          ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = y who := by rw [htotal, haverage]; ring
  · intro i hi
    have hmem := hsupport i hi
    rw [ZeroCoordinates, Finset.mem_filter] at hmem
    simp only [wi, hmem.2, hdiag i]
    ring
  · simpa only [z, htotal] using (zero_lt_one : (0 : ℝ) < 1)

/-! The first subcase of Lemma 3.4: a segment from `y` to a zero-coordinate
column reaches a second boundary point of `D`. -/
theorem theorem32Conclusion_of_segment_boundary
    (M : ι → ι → ℝ) {y w : ι → ℝ}
    (hbound : MatrixPayoffsBounded M) (hdiag : ∀ i, M i i = 0)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M)
    (i : ι) (hyi : y i = 0) (hw : DZero M w)
    (hsegment : Segment y (fun who => M who i) w) (hwy : w ≠ y)
    {ε : ℝ} (hε : 0 < ε) : Theorem32Conclusion M y ε := by
  obtain ⟨a, ha0, ha1, haw⟩ := hsegment
  let δ := 1 - a
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr ha1
  have hδpos : 0 < δ := by
    apply lt_of_le_of_ne hδ0
    intro hzeroδ
    have haeq : a = 1 := by
      dsimp only [δ] at hzeroδ
      linarith
    apply hwy
    funext who
    rw [haw, haeq]
    ring
  have hδone : δ ≤ 1 := by dsimp only [δ]; linarith
  have hwD : w ∈ D M := mem_D_of_DZero hw
  have hcolumn_ne : (fun who => M who i) ≠ w := by
    exact column_ne_of_no_nontrivial_zero_solution M hwD hdiag hzero i
  have hδlt : δ < 1 := by
    apply lt_of_le_of_ne hδone
    intro hδeq
    apply hcolumn_ne
    have haeq : a = 0 := by
      dsimp only [δ] at hδeq
      linarith
    funext who
    rw [haw, haeq]
    ring
  have hw_affine (who : ι) :
      w who = (1 - δ) * y who + δ * M who i := by
    have := haw who
    dsimp only [δ]
    nlinarith
  let η := min ε 1
  have hηpos : 0 < η := lt_min hε zero_lt_one
  have hη0 : 0 ≤ η := hηpos.le
  have hηε : η ≤ ε := min_le_left _ _
  have hηone : η ≤ 1 := min_le_right _ _
  let denominator := η * (1 - δ) + δ
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    have : 0 ≤ η * (1 - δ) :=
      mul_nonneg hη0 (sub_nonneg.mpr hδone)
    linarith
  let wi : ι → ι → ℝ := fun owner who =>
    (1 - η) * w who + η * M who owner
  let z : SimplexWeights ι :=
    { cemetery := η * (1 - δ) / denominator
      singleton := fun owner => if owner = i then δ / denominator else 0
      cemetery_nonneg := div_nonneg
        (mul_nonneg hη0 (sub_nonneg.mpr hδone)) hdenominator.le
      singleton_nonneg := fun owner => by
        split
        · exact div_nonneg hδ0 hdenominator.le
        · exact le_rfl
      total := by
        simp only [Fintype.sum_ite_eq', denominator]
        field_simp [show η * (1 - δ) + δ ≠ 0 by positivity] }
  refine ⟨{
    w := w
    wi := wi
    z := z
    w_boundary := hw
    approach := ?_
    lower := ?_
    balance := ?_
    complementary := ?_
    nontrivial := ?_ }⟩
  · intro owner
    left
    constructor
    · refine ⟨1 - η, sub_nonneg.mpr hηone, by linarith, ?_⟩
      intro who
      simp only [wi]
      ring
    · intro hwi
      apply column_ne_of_no_nontrivial_zero_solution M hwD hdiag hzero owner
      funext who
      have hcoordinate := congr_fun hwi who
      simp only [wi] at hcoordinate
      nlinarith
  · intro owner who
    have hMlower : -1 ≤ M who owner :=
      (abs_le.mp (hbound who owner)).1
    have hscaled : -η ≤ η * M who owner := by
      nlinarith [mul_nonneg hη0 (show 0 ≤ M who owner + 1 by linarith)]
    have hw_nonneg := hwD.2 who
    have hfactor : 0 ≤ 1 - η := sub_nonneg.mpr hηone
    dsimp only [wi]
    nlinarith [mul_nonneg hfactor hw_nonneg]
  · intro who
    change w who = η * (1 - δ) / denominator * y who +
      ∑ owner, (if owner = i then δ / denominator else 0) * wi owner who
    have hsum :
        (∑ owner, (if owner = i then δ / denominator else 0) * wi owner who) =
          δ / denominator * wi i who := by
      simpa only [ite_mul, zero_mul] using
        (Fintype.sum_ite_eq' i fun owner => δ / denominator * wi owner who)
    rw [hsum]
    simp only [wi]
    rw [hw_affine]
    field_simp [ne_of_gt hdenominator]
    dsimp only [denominator]
    ring
  · intro owner howner
    by_cases hoi : owner = i
    · subst owner
      have hwi : w i = 0 := by rw [hw_affine, hyi, hdiag]; ring
      simp only [wi, hwi, hdiag]
      ring
    · simp [z, hoi] at howner
  · simp only [z, Fintype.sum_ite_eq', denominator]
    exact div_pos hδpos hdenominator

/-! The published second subcase of Lemma 3.5. Here `w` is a boundary
point of the small slice `(1-η)y+ηS(J_y)`. Its extreme points approach
the singleton columns from `y`, which is the second alternative in the
published condition (F.1). -/
theorem theorem32Conclusion_of_slice_boundary
    (M : ι → ι → ℝ) {y w : ι → ℝ}
    (hy : DZero M y) (hw : DZero M w)
    (hbound : MatrixPayoffsBounded M) (hdiag : ∀ i, M i i = 0)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M)
    {η ε : ℝ} (hηpos : 0 < η) (hηone : η ≤ 1) (hηε : η ≤ ε)
    (hwSlice : w ∈ SubfamilyHull
      (fun who owner => (1 - η) * y who + η * M who owner)
      (ZeroCoordinates y)) :
    Theorem32Conclusion M y ε := by
  have hyD : y ∈ D M := mem_D_of_DZero hy
  obtain ⟨weight, hweight, htotal, hsupport, haverage⟩ :=
    subfamilyHull_weights
      (fun who owner => (1 - η) * y who + η * M who owner)
      (ZeroCoordinates y) hwSlice
  let wi : ι → ι → ℝ := fun owner who =>
    (1 - η) * y who + η * M who owner
  let z : SimplexWeights ι :=
    { cemetery := 0
      singleton := weight
      cemetery_nonneg := le_rfl
      singleton_nonneg := hweight
      total := by simpa using htotal }
  refine ⟨{
    w := w
    wi := wi
    z := z
    w_boundary := hw
    approach := ?_
    lower := ?_
    balance := ?_
    complementary := ?_
    nontrivial := ?_ }⟩
  · intro owner
    right
    constructor
    · refine ⟨1 - η, sub_nonneg.mpr hηone, by linarith, ?_⟩
      intro who
      simp only [wi]
      ring
    · intro hwi
      apply column_ne_of_no_nontrivial_zero_solution M hyD hdiag hzero owner
      funext who
      have hcoordinate := congr_fun hwi who
      simp only [wi] at hcoordinate
      nlinarith
  · intro owner who
    have hMlower : -1 ≤ M who owner :=
      (abs_le.mp (hbound who owner)).1
    have hscaled : -η ≤ η * M who owner := by
      nlinarith [mul_nonneg hηpos.le (show 0 ≤ M who owner + 1 by linarith)]
    have hy_nonneg := hyD.2 who
    have hfactor : 0 ≤ 1 - η := sub_nonneg.mpr hηone
    dsimp only [wi]
    nlinarith [mul_nonneg hfactor hy_nonneg]
  · intro who
    simp only [z, zero_mul, zero_add, wi]
    exact (haverage who).symm
  · intro owner howner
    have hmem := hsupport owner howner
    rw [ZeroCoordinates, Finset.mem_filter] at hmem
    simp only [wi, hmem.2, hdiag owner]
    ring
  · simpa only [z, htotal] using (zero_lt_one : (0 : ℝ) < 1)

/-! Rescaling a nontrivial projective complementarity packet gives the
first construction in the published Lemma 3.4. -/
theorem theorem32Conclusion_of_projective_packet
    (M : ι → ι → ℝ) {y w : ι → ℝ}
    (hw : DZero M w) (hbound : MatrixPayoffsBounded M)
    (hdiag : ∀ i, M i i = 0)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M)
    (cemetery : ℝ) (singleton : ι → ℝ)
    (hcemetery : 0 ≤ cemetery) (hsingleton : ∀ i, 0 ≤ singleton i)
    (htotal : cemetery + ∑ i, singleton i = 1)
    (hbalance : ∀ who, w who = cemetery * y who +
      ∑ i, singleton i * M who i)
    (hcomplementary : ∀ i, singleton i > 0 → w i = 0)
    (hnontrivial : 0 < ∑ i, singleton i)
    {ε : ℝ} (hε : 0 < ε) : Theorem32Conclusion M y ε := by
  let η := min ε 1
  have hηpos : 0 < η := lt_min hε zero_lt_one
  have hηnonneg : 0 ≤ η := hηpos.le
  have hηε : η ≤ ε := min_le_left _ _
  have hηone : η ≤ 1 := min_le_right _ _
  let mass := ∑ i, singleton i
  let denominator := η * cemetery + mass
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hηnonneg hcemetery) hnontrivial
  let wi : ι → ι → ℝ := fun owner who =>
    (1 - η) * w who + η * M who owner
  let z : SimplexWeights ι :=
    { cemetery := η * cemetery / denominator
      singleton := fun owner => singleton owner / denominator
      cemetery_nonneg := div_nonneg (mul_nonneg hηnonneg hcemetery)
        hdenominator.le
      singleton_nonneg := fun owner =>
        div_nonneg (hsingleton owner) hdenominator.le
      total := by
        change η * cemetery / denominator +
          ∑ owner, singleton owner / denominator = 1
        rw [← Finset.sum_div]
        field_simp [ne_of_gt hdenominator]
        rfl }
  refine ⟨{
    w := w
    wi := wi
    z := z
    w_boundary := hw
    approach := ?_
    lower := ?_
    balance := ?_
    complementary := ?_
    nontrivial := ?_ }⟩
  · intro owner
    left
    constructor
    · refine ⟨1 - η, sub_nonneg.mpr hηone, by linarith, ?_⟩
      intro who
      simp only [wi]
      ring
    · intro hwi
      have hcolumn : (fun who => M who owner) = w := by
        funext who
        have hcoordinate := congr_fun hwi who
        simp only [wi] at hcoordinate
        nlinarith
      exact column_not_mem_D_of_no_nontrivial_zero_solution M hdiag
        hzero owner (hcolumn ▸ hw.1)
  · intro owner who
    have hMlower : -1 ≤ M who owner :=
      (abs_le.mp (hbound who owner)).1
    have hscaled : -η ≤ η * M who owner := by
      nlinarith [mul_nonneg hηnonneg (show 0 ≤ M who owner + 1 by linarith)]
    have hwNonnegative := hw.1.2 who
    have hfactor : 0 ≤ 1 - η := sub_nonneg.mpr hηone
    dsimp only [wi]
    nlinarith [mul_nonneg hfactor hwNonnegative]
  · intro who
    change w who = η * cemetery / denominator * y who +
      ∑ owner, singleton owner / denominator * wi owner who
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    simp_rw [wi, mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    have hweighted : ∑ owner, singleton owner * (η * M who owner) =
        η * (∑ owner, singleton owner * M who owner) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro owner _
      ring
    rw [hweighted]
    field_simp [ne_of_gt hdenominator]
    rw [hbalance]
    dsimp only [denominator, mass]
    have hmass : ∑ i, singleton i = 1 - cemetery := by
      linarith [htotal]
    rw [hmass]
    ring
  · intro owner howner
    have hsinglePos : 0 < singleton owner := by
      rcases div_pos_iff.mp howner with hpositive | hnegative
      · exact hpositive.1
      · exact False.elim ((not_lt_of_ge hdenominator.le) hnegative.2)
    have hwzero := hcomplementary owner hsinglePos
    simp only [wi, hwzero, hdiag owner]
    ring
  · change 0 < ∑ owner, singleton owner / denominator
    rw [← Finset.sum_div]
    exact div_pos hnontrivial hdenominator

/-! **Lemmas 3.3 and 3.4 (paper).** Put `J_y={i:y_i=0}` and
`S(J_y)=conv{r̂^i:i∈J_y}`. In the two geometric cases
`conv(S(J_y),y)∩D={y}` and `conv(S(J_y),y)∩D ⊋ {y}`, respectively, the
paper proves the same `Theorem32Conclusion` represented above. -/

/-! `conv(S(J),y)`, the convex hull after adjoining `y`. -/
def AugmentedHull (M : ι → ι → ℝ) (J : Finset ι)
    (y : ι → ℝ) : Set (ι → ℝ) :=
  convexHull ℝ (SubfamilyHull M J ∪ {y})

omit [Fintype ι] [DecidableEq ι] in
private theorem affine_slice_mem_subfamilyHull
    (M : ι → ι → ℝ) (J : Finset ι) {y s : ι → ℝ}
    (η : ℝ) (hs : s ∈ SubfamilyHull M J) :
    (fun who => (1 - η) * y who + η * s who) ∈
      SubfamilyHull
        (fun who owner => (1 - η) * y who + η * M who owner) J := by
  let slice : (ι → ℝ) →ᵃ[ℝ] (ι → ℝ) :=
    AffineMap.mk (fun x => (1 - η) • y + η • x)
      (η • LinearMap.id)
      (by
        intro p v
        ext who
        simp
        ring)
  have himage : slice ''
      (Set.range fun i : J => fun who => M who i) =
      Set.range (fun i : J =>
        fun who => (1 - η) * y who + η * M who i) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      ext who
      simp [slice, smul_eq_mul]
    · rintro ⟨i, rfl⟩
      refine ⟨fun who => M who i, ⟨i, rfl⟩, ?_⟩
      ext who
      simp [slice, smul_eq_mul]
  have hsImage : slice s ∈ slice ''
      convexHull ℝ (Set.range fun i : J => fun who => M who i) :=
    ⟨s, hs, rfl⟩
  rw [slice.image_convexHull, himage] at hsImage
  change (fun who => (1 - η) * y who + η * s who) ∈
    convexHull ℝ (Set.range fun i : J =>
      fun who => (1 - η) * y who + η * M who i)
  convert hsImage using 1
  ext who
  simp [slice, smul_eq_mul]

omit [Fintype ι] [DecidableEq ι] in
private theorem mem_augmentedHull
    (M : ι → ι → ℝ) (J : Finset ι) (hJ : J.Nonempty)
    {y q : ι → ℝ} (hq : q ∈ AugmentedHull M J y) :
    ∃ s ∈ SubfamilyHull M J, q ∈ segment ℝ y s := by
  have hS : (SubfamilyHull M J).Nonempty := by
    obtain ⟨i, hi⟩ := hJ
    exact ⟨fun who => M who i, subset_convexHull ℝ _ ⟨⟨i, hi⟩, rfl⟩⟩
  have hconvexS : Convex ℝ (SubfamilyHull M J) :=
    convex_convexHull ℝ _
  have heq : convexHull ℝ (SubfamilyHull M J ∪ {y}) =
      convexJoin ℝ (SubfamilyHull M J) {y} :=
    hconvexS.convexHull_union (convex_singleton y)
      hS (Set.singleton_nonempty y)
  rw [AugmentedHull, heq, mem_convexJoin] at hq
  obtain ⟨s, hs, b, hb, hsegment⟩ := hq
  have hb' : b = y := Set.mem_singleton_iff.mp hb
  subst b
  exact ⟨s, hs, segment_symm ℝ s y ▸ hsegment⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem endpoint_not_mem_augmentedHull
    {C : Set (ι → ℝ)} (hC : Convex ℝ C) (hCnonempty : C.Nonempty)
    {y s q : ι → ℝ} (hy : y ∉ C) (hs : s ∈ C)
    (hq : Segment y s q) (hqy : q ≠ y) :
    y ∉ convexHull ℝ (C ∪ {q}) := by
  intro hyHull
  have heq : convexHull ℝ (C ∪ {q}) = convexJoin ℝ C {q} :=
    hC.convexHull_union (convex_singleton q) hCnonempty
      (Set.singleton_nonempty q)
  rw [heq, mem_convexJoin] at hyHull
  obtain ⟨c, hc, q', hq', hySegment⟩ := hyHull
  have hq'eq : q' = q := Set.mem_singleton_iff.mp hq'
  subst q'
  obtain ⟨b, hb0, hb1, hqb⟩ := hq
  have hbne : b ≠ 1 := by
    intro hb
    apply hqy
    funext who
    rw [hqb who, hb]
    ring
  obtain ⟨a, ha0, ha1, hya⟩ :=
    segment_of_mem_segment hySegment
  let denominator := a + (1 - a) * (1 - b)
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    have hbone : 0 < 1 - b := lt_of_le_of_ne
      (sub_nonneg.mpr hb1) (Ne.symm (sub_ne_zero.mpr hbne.symm))
    by_cases hapos : 0 < a
    · positivity
    · have haeq : a = 0 := le_antisymm (le_of_not_gt hapos) ha0
      rw [haeq]
      simpa using hbone
  have hySegmentCS : Segment c s y := by
    refine ⟨a / denominator, div_nonneg ha0 hdenominator.le, ?_, ?_⟩
    · rw [div_le_one hdenominator]
      dsimp only [denominator]
      exact le_add_of_nonneg_right
        (mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1))
    · intro who
      field_simp [ne_of_gt hdenominator]
      dsimp only [denominator]
      linear_combination hya who + (1 - a) * (hqb who)
  exact hy <| hC.segment_subset hc hs (mem_segment_of_Segment hySegmentCS)

/-! Lemma 3.3: the singleton-intersection case yields (F.1)--(F.5). -/
theorem lemma3_3
    (M : ι → ι → ℝ) {y : ι → ℝ} (hy : DZero M y)
    (hbound : MatrixPayoffsBounded M) (hdiag : ∀ i, M i i = 0) (hzero :
      ¬HasNontrivialZeroProjectiveLCPSolution M) (hQ : QMatrix M)
    (hnot : y ∉ SubfamilyHull M (ZeroCoordinates y))
    (hpoint : AugmentedHull M (ZeroCoordinates y) y ∩
      D M = {y}) {ε : ℝ} (hε : 0 < ε) :
    Theorem32Conclusion M y ε := by
  let J := ZeroCoordinates y
  let C := SubfamilyHull M J
  obtain ⟨pivot, hpivotZero⟩ := hy.2
  have hpivot : pivot ∈ J := by
    simp only [J, ZeroCoordinates, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hpivotZero
  have hCconvex : Convex ℝ C := convex_convexHull ℝ _
  have hCnonempty : C.Nonempty := by
    exact ⟨fun who => M who pivot,
      subset_convexHull ℝ _ ⟨⟨pivot, hpivot⟩, rfl⟩⟩
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let q : ℕ → ι → ℝ := fun n who =>
    y who + δ n * (M who pivot - y who)
  have hδpos (n : ℕ) : 0 < δ n := by
    dsimp only [δ]
    positivity
  have hδone (n : ℕ) : δ n ≤ 1 := by
    dsimp only [δ]
    rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    norm_num
  have hqSegment (n : ℕ) :
      Segment y (fun who => M who pivot) (q n) := by
    refine ⟨1 - δ n, sub_nonneg.mpr (hδone n), by linarith [hδpos n], ?_⟩
    intro who
    simp only [q]
    ring
  have hqNe (n : ℕ) : q n ≠ y := by
    intro hqy
    have hcolumnNe := column_ne_of_no_nontrivial_zero_solution
      M hy.1 hdiag hzero pivot
    apply hcolumnNe
    funext who
    have hcoordinate := congr_fun hqy who
    simp only [q] at hcoordinate
    nlinarith [hδpos n]
  have hqHull (n : ℕ) : q n ∈ ColumnConvexHull M :=
    (convex_convexHull ℝ _).segment_subset hy.1.1
      (subset_convexHull ℝ _ ⟨pivot, rfl⟩)
      (mem_segment_of_Segment (hqSegment n))
  have hqAugmented (n : ℕ) : q n ∈ AugmentedHull M J y := by
    have hcolumnC : (fun who => M who pivot) ∈ C := by
      exact subset_convexHull ℝ _ ⟨⟨pivot, hpivot⟩, rfl⟩
    apply (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ <| Set.mem_union_right _ (Set.mem_singleton y))
      (subset_convexHull ℝ _ <| Set.mem_union_left _ <|
        (show (fun who => M who pivot) ∈ SubfamilyHull M J from hcolumnC))
    exact mem_segment_of_Segment (hqSegment n)
  have hqNegative (n : ℕ) : q n ∉ NonnegativeOrthant ι := by
    intro hnonnegative
    have hqD : q n ∈ D M := ⟨hqHull n, hnonnegative⟩
    have hsingleton : q n ∈ ({y} : Set (ι → ℝ)) := by
      rw [← hpoint]
      exact ⟨by simpa only [J] using hqAugmented n, hqD⟩
    exact hqNe n (Set.mem_singleton_iff.mp hsingleton)
  let solution (n : ℕ) : ProjectiveLCPSolution M (q n) :=
    Classical.choice (hQ (q n))
  let residual (n : ℕ) : ι → ℝ := fun who =>
    (solution n).cemetery * q n who +
      ∑ owner, (solution n).singleton owner * M who owner
  have hresidualDZero (n : ℕ) : DZero M (residual n) :=
    lemma3_1 M (q n) (hqHull n) (hqNegative n) (solution n)
  let coefficient (n : ℕ) : Option ι → ℝ
    | none => (solution n).cemetery
    | some owner => (solution n).singleton owner
  have hcoefficient (n : ℕ) : coefficient n ∈
      Set.univ.pi (fun _ : Option ι => Set.Icc (0 : ℝ) 1) := by
    intro index _
    constructor
    · cases index with
      | none => exact (solution n).cemetery_nonneg
      | some owner => exact (solution n).singleton_nonneg owner
    · cases index with
      | none =>
          have hsum : 0 ≤ ∑ owner, (solution n).singleton owner :=
            Finset.sum_nonneg fun owner _ =>
              (solution n).singleton_nonneg owner
          linarith [(solution n).total]
      | some owner =>
          have hsingleSum : (solution n).singleton owner ≤
              ∑ i, (solution n).singleton i :=
            Finset.single_le_sum
              (fun i _ => (solution n).singleton_nonneg i)
              (Finset.mem_univ owner)
          have hsum : ∑ i, (solution n).singleton i ≤ 1 := by
            linarith [(solution n).total, (solution n).cemetery_nonneg]
          exact hsingleSum.trans hsum
  have hcubeCompact : IsCompact
      (Set.univ.pi (fun _ : Option ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨limit, hlimitCube, subseq, hsubseq, hlimit⟩ :=
    hcubeCompact.tendsto_subseq hcoefficient
  let cemetery := limit none
  let singleton : ι → ℝ := fun owner => limit (some owner)
  have hcoefficientLimit (index : Option ι) :
      Tendsto (fun n => coefficient (subseq n) index) atTop
        (nhds (limit index)) :=
    ((continuous_apply index).tendsto limit).comp hlimit
  have hδTendsto : Tendsto δ atTop (nhds 0) := by
    simpa only [δ, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hqTendsto : Tendsto q atTop (nhds y) := by
    rw [tendsto_pi_nhds]
    intro who
    simpa only [q, zero_mul, add_zero] using
      tendsto_const_nhds.add (hδTendsto.mul_const (M who pivot - y who))
  have hqSubseq : Tendsto (q ∘ subseq) atTop (nhds y) :=
    hqTendsto.comp hsubseq.tendsto_atTop
  let w : ι → ℝ := fun who => cemetery * y who +
    ∑ owner, singleton owner * M who owner
  have hresidualTendsto : Tendsto (residual ∘ subseq) atTop (nhds w) := by
    rw [tendsto_pi_nhds]
    intro who
    have hcemetery := hcoefficientLimit none
    have hqWho : Tendsto (fun n => q (subseq n) who) atTop (nhds (y who)) :=
      (continuous_apply who).tendsto y |>.comp hqSubseq
    have hsum := tendsto_finsetSum Finset.univ fun owner _ =>
      (hcoefficientLimit (some owner)).mul_const (M who owner)
    simpa only [residual, Function.comp_apply, coefficient, w, cemetery,
      singleton] using hcemetery.mul hqWho |>.add hsum
  have hcemeteryNonneg : 0 ≤ cemetery := hlimitCube none (Set.mem_univ _)|>.1
  have hsingletonNonneg (owner : ι) : 0 ≤ singleton owner :=
    hlimitCube (some owner) (Set.mem_univ _)|>.1
  have htotal : cemetery + ∑ owner, singleton owner = 1 := by
    have htendsto : Tendsto
        (fun n => coefficient (subseq n) none +
          ∑ owner, coefficient (subseq n) (some owner)) atTop
        (nhds (cemetery + ∑ owner, singleton owner)) := by
      exact (hcoefficientLimit none).add <|
        tendsto_finsetSum Finset.univ fun owner _ =>
          hcoefficientLimit (some owner)
    have hone : Tendsto
        (fun n => coefficient (subseq n) none +
          ∑ owner, coefficient (subseq n) (some owner)) atTop
        (nhds 1) := by
      simpa only [coefficient, (solution _).total] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
    exact tendsto_nhds_unique htendsto hone
  have hcomplementary (owner : ι) :
      singleton owner * w owner = 0 := by
    have htendsto := (hcoefficientLimit (some owner)).mul <|
      (continuous_apply owner).tendsto w |>.comp hresidualTendsto
    have hzero : Tendsto
        (fun n => coefficient (subseq n) (some owner) *
          residual (subseq n) owner) atTop (nhds 0) := by
      have heq : (fun n => coefficient (subseq n) (some owner) *
          residual (subseq n) owner) = fun _ : ℕ => (0 : ℝ) := by
        funext n
        exact (solution (subseq n)).complementary owner
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique htendsto hzero
  have hwD : w ∈ D M := (isClosed_D M).mem_of_tendsto
    hresidualTendsto (Filter.Eventually.of_forall fun n =>
      (hresidualDZero (subseq n)).1)
  have hwZero : ∃ owner, w owner = 0 := by
    have hprodTendsto := tendsto_finsetProd Finset.univ fun owner _ =>
      (continuous_apply owner).tendsto w |>.comp hresidualTendsto
    have hprodZero : Tendsto
        (fun n => ∏ owner, residual (subseq n) owner) atTop (nhds 0) := by
      have heq : (fun n => ∏ owner, residual (subseq n) owner) =
          fun _ : ℕ => (0 : ℝ) := by
        funext n
        obtain ⟨owner, howner⟩ := (hresidualDZero (subseq n)).2
        exact Finset.prod_eq_zero (Finset.mem_univ owner) howner
      rw [heq]
      exact tendsto_const_nhds
    have hprod : ∏ owner, w owner = 0 :=
      tendsto_nhds_unique hprodTendsto hprodZero
    obtain ⟨owner, _, howner⟩ := Finset.prod_eq_zero_iff.mp hprod
    exact ⟨owner, howner⟩
  have hw : DZero M w := ⟨hwD, hwZero⟩
  have hwy : w ≠ y := by
    intro hwyeq
    have heventuallyPositive : ∀ᶠ n in atTop,
        ∀ owner ∈ Finset.univ, owner ∉ J →
          0 < residual (subseq n) owner := by
      rw [Finset.eventually_all]
      intro owner _
      by_cases howner : owner ∈ J
      · exact Filter.Eventually.of_forall fun _ hnotOwner =>
          False.elim (hnotOwner howner)
      · have hyowner : 0 < y owner := by
          have hyNonnegative := hy.1.2 owner
          have hyne : y owner ≠ 0 := by
            simpa only [J, ZeroCoordinates, Finset.mem_filter,
              Finset.mem_univ, true_and] using howner
          exact lt_of_le_of_ne hyNonnegative hyne.symm
        have htendsto : Tendsto (fun n => residual (subseq n) owner)
            atTop (nhds (y owner)) := by
          have ht :=
            (continuous_apply owner).tendsto w |>.comp hresidualTendsto
          change Tendsto (fun n => residual (subseq n) owner) atTop
            (nhds (w owner)) at ht
          simpa only [hwyeq] using ht
        filter_upwards [htendsto.eventually_const_lt hyowner] with n hn
        exact fun _ => hn
    obtain ⟨n, hn⟩ := heventuallyPositive.exists
    have hsingleOutside (owner : ι) (howner : owner ∉ J) :
        (solution (subseq n)).singleton owner = 0 := by
      have hcomp := (solution (subseq n)).complementary owner
      change (solution (subseq n)).singleton owner *
        residual (subseq n) owner = 0 at hcomp
      exact (mul_eq_zero.mp hcomp).resolve_right
        (ne_of_gt (hn owner (Finset.mem_univ owner) howner))
    let point : Option ι → (ι → ℝ)
      | none => q (subseq n)
      | some owner => if owner ∈ J then (fun who => M who owner)
        else q (subseq n)
    have hpointMem (index : Option ι) : point index ∈
        C ∪ {q (subseq n)} := by
      cases index with
      | none => exact Set.mem_union_right _ (Set.mem_singleton _)
      | some owner =>
          by_cases howner : owner ∈ J
          · change (if owner ∈ J then (fun who => M who owner)
                else q (subseq n)) ∈ C ∪ {q (subseq n)}
            rw [if_pos howner]
            apply Set.mem_union_left
            exact subset_convexHull ℝ _ ⟨⟨owner, howner⟩, rfl⟩
          · exact Set.mem_union_right _ (by simp [point, howner])
    have hpacketHull : residual (subseq n) ∈
        convexHull ℝ (C ∪ {q (subseq n)}) := by
      have hsum := (convex_convexHull ℝ _).sum_mem
        (t := Finset.univ) (w := fun index => coefficient (subseq n) index)
        (z := point)
        (fun index _ => by
          cases index with
          | none => exact (solution (subseq n)).cemetery_nonneg
          | some owner => exact (solution (subseq n)).singleton_nonneg owner)
        (by simpa only [coefficient, Fintype.sum_option] using
          (solution (subseq n)).total)
        (fun index _ => subset_convexHull ℝ _ (hpointMem index))
      convert hsum using 1
      funext who
      simp only [residual]
      rw [Fintype.sum_option]
      simp only [coefficient, point]
      congr 1
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro owner _
      by_cases howner : owner ∈ J
      · simp [howner]
      · simp [howner, hsingleOutside owner howner]
    have hnotEndpoint := endpoint_not_mem_augmentedHull hCconvex
      hCnonempty (by simpa only [C, J] using hnot)
      (show (fun who => M who pivot) ∈ C from
        subset_convexHull ℝ _ ⟨⟨pivot, hpivot⟩, rfl⟩)
      (hqSegment (subseq n)) (hqNe (subseq n))
    have hpacketAugmented : residual (subseq n) ∈
        AugmentedHull M J y := by
      apply (convexHull_min ?_ (convex_convexHull ℝ _)) hpacketHull
      intro x hx
      rcases hx with hx | hx
      · exact subset_convexHull ℝ _ (Set.mem_union_left _ hx)
      · rw [Set.mem_singleton_iff] at hx
        subst x
        exact hqAugmented (subseq n)
    have hresidualEq : residual (subseq n) = y := by
      apply Set.mem_singleton_iff.mp
      rw [← hpoint]
      exact ⟨by simpa only [J] using hpacketAugmented,
        (hresidualDZero (subseq n)).1⟩
    exact hnotEndpoint (hresidualEq ▸ hpacketHull)
  have hnontrivial : 0 < ∑ owner, singleton owner := by
    have hsumNonnegative : 0 ≤ ∑ owner, singleton owner :=
      Finset.sum_nonneg fun owner _ => hsingletonNonneg owner
    apply lt_of_le_of_ne hsumNonnegative
    intro hsumZero
    have hcemeteryOne : cemetery = 1 := by linarith [htotal]
    have hsingleZero (owner : ι) : singleton owner = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (fun i _ => hsingletonNonneg i)).mp hsumZero.symm owner
        (Finset.mem_univ owner)
    apply hwy
    funext who
    simp [w, hcemeteryOne, hsingleZero]
  apply theorem32Conclusion_of_projective_packet M hw hbound hdiag hzero
    cemetery singleton hcemeteryNonneg hsingletonNonneg htotal
  · exact fun who => rfl
  · intro owner howner
    exact (mul_eq_zero.mp (hcomplementary owner)).resolve_left
      (ne_of_gt howner)
  · exact hnontrivial
  · exact hε

/-! Lemma 3.4: the strict-intersection case yields (F.1)--(F.5). -/
theorem lemma3_4
    (M : ι → ι → ℝ) {y : ι → ℝ} (hy : DZero M y)
    (hbound : MatrixPayoffsBounded M) (hdiag : ∀ i, M i i = 0) (hzero :
      ¬HasNontrivialZeroProjectiveLCPSolution M) (_hQ : QMatrix M)
    (_hnot : y ∉ SubfamilyHull M (ZeroCoordinates y))
    (hstrict : AugmentedHull M (ZeroCoordinates y) y ∩
      D M ≠ {y}) {ε : ℝ} (hε : 0 < ε) :
    Theorem32Conclusion M y ε := by
  have hyD : y ∈ D M := mem_D_of_DZero hy
  have hyAugmented : y ∈ AugmentedHull M (ZeroCoordinates y) y := by
    apply subset_convexHull ℝ
    exact Set.mem_union_right _ (Set.mem_singleton y)
  have hyIntersection : y ∈
      AugmentedHull M (ZeroCoordinates y) y ∩ D M :=
    ⟨hyAugmented, hyD⟩
  obtain ⟨q, hqIntersection, hqy⟩ :
      ∃ q ∈ AugmentedHull M (ZeroCoordinates y) y ∩ D M, q ≠ y := by
    by_contra hnone
    push Not at hnone
    apply hstrict
    apply Set.Subset.antisymm
    · intro x hx
      rw [Set.mem_singleton_iff]
      exact hnone x hx
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      simpa only [hx] using hyIntersection
  have hJ : (ZeroCoordinates y).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    letI : IsEmpty (ZeroCoordinates y : Type) :=
      ⟨fun owner => by simpa [hempty] using owner.property⟩
    have hrange : (Set.range fun i : ZeroCoordinates y =>
        fun who => M who i) = ∅ :=
      Set.range_eq_empty_iff.mpr inferInstance
    have hSempty : SubfamilyHull M (ZeroCoordinates y) = ∅ := by
      simp only [SubfamilyHull, hrange, convexHull_empty]
    have hqy' : q = y := by
      have := hqIntersection.1
      simp [AugmentedHull, hSempty] at this
      exact this
    exact hqy hqy'
  obtain ⟨s, hs, hqSegment⟩ :=
    mem_augmentedHull M (ZeroCoordinates y) hJ hqIntersection.1
  by_cases hsegmentCase :
      ∃ owner ∈ ZeroCoordinates y,
        ∃ p ∈ segment ℝ y (fun who => M who owner), p ∈ D M ∧ p ≠ y
  · obtain ⟨owner, howner, p, hpSegment, hpD, hpy⟩ := hsegmentCase
    have hcolumnNotD :=
      column_not_mem_D_of_no_nontrivial_zero_solution M hdiag hzero owner
    have hcolumnHull : (fun who => M who owner) ∈ ColumnConvexHull M :=
      subset_convexHull ℝ _ ⟨owner, rfl⟩
    have hcolumnNotOrthant :
        (fun who => M who owner) ∉ NonnegativeOrthant ι := by
      intro hnonnegative
      exact hcolumnNotD ⟨hcolumnHull, hnonnegative⟩
    obtain ⟨w, hwTail, hwFrontier⟩ :=
      exists_frontier_on_segment_of_mem_notMem hpD.2 hcolumnNotOrthant
    obtain ⟨hwNonnegative, hwZero⟩ :=
      frontier_nonnegativeOrthant_has_zero hwFrontier
    have hwHull : w ∈ ColumnConvexHull M :=
      (convex_convexHull ℝ _).segment_subset hpD.1 hcolumnHull hwTail
    have hwDZero : DZero M w := ⟨⟨hwHull, hwNonnegative⟩, hwZero⟩
    have hwFull : w ∈ segment ℝ y (fun who => M who owner) :=
      (convex_segment y (fun who => M who owner)).segment_subset
        hpSegment (right_mem_segment ℝ y (fun who => M who owner)) hwTail
    have hcolumnNe : (fun who => M who owner) ≠ y := by
      intro heq
      exact hcolumnNotD (heq ▸ hyD)
    have hwy : w ≠ y := by
      intro hwy
      exact endpoint_not_mem_tail_segment hpSegment hpy hcolumnNe (hwy ▸ hwTail)
    have hyowner : y owner = 0 := by
      simpa [ZeroCoordinates] using howner
    exact theorem32Conclusion_of_segment_boundary M hbound hdiag hzero
      owner hyowner hwDZero (segment_of_mem_segment hwFull) hwy hε
  · push Not at hsegmentCase
    obtain ⟨a, ha0, ha1, hq⟩ := segment_of_mem_segment hqSegment
    let ρ := 1 - a
    have hρpos : 0 < ρ := by
      have hane : a ≠ 1 := by
        intro ha
        apply hqy
        funext who
        rw [hq who, ha]
        ring
      dsimp only [ρ]
      exact lt_of_le_of_ne (sub_nonneg.mpr ha1)
        (Ne.symm (sub_ne_zero.mpr hane.symm))
    have hqAffine (who : ι) :
        q who = (1 - ρ) * y who + ρ * s who := by
      rw [hq who]
      dsimp only [ρ]
      ring
    let η := min ε (min ρ 1)
    have hηpos : 0 < η := lt_min hε (lt_min hρpos zero_lt_one)
    have hηε : η ≤ ε := min_le_left _ _
    have hηρ : η ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
    have hηone : η ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
    let inside : ι → ℝ := fun who =>
      (1 - η) * y who + η * s who
    have hinsideSegment : inside ∈ segment ℝ y q := by
      rw [segment_eq_image_lineMap]
      refine ⟨η / ρ, ⟨div_nonneg hηpos.le hρpos.le,
        (div_le_one hρpos).mpr hηρ⟩, ?_⟩
      ext who
      simp only [inside, AffineMap.lineMap_apply_module, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hqAffine]
      field_simp [ne_of_gt hρpos]
      ring
    have hinsideD : inside ∈ D M :=
      (convex_D M).segment_subset hyD hqIntersection.2 hinsideSegment
    obtain ⟨owner, howner⟩ := hJ
    let extreme : ι → ℝ := fun who =>
      (1 - η) * y who + η * M who owner
    have hextremeSegment : extreme ∈
        segment ℝ y (fun who => M who owner) := by
      apply mem_segment_of_Segment
      refine ⟨1 - η, sub_nonneg.mpr hηone, by linarith, ?_⟩
      intro who
      simp only [extreme]
      ring
    have hextremeNe : extreme ≠ y := by
      intro heq
      have hcolumnNe := column_ne_of_no_nontrivial_zero_solution
        M hyD hdiag hzero owner
      apply hcolumnNe
      funext who
      have hcoordinate := congr_fun heq who
      simp only [extreme] at hcoordinate
      nlinarith
    have hextremeNotD : extreme ∉ D M := by
      intro hextremeD
      exact hextremeNe <|
        hsegmentCase owner howner extreme hextremeSegment hextremeD
    have hextremeHull : extreme ∈ ColumnConvexHull M :=
      (convex_convexHull ℝ _).segment_subset hyD.1
        (subset_convexHull ℝ _ ⟨owner, rfl⟩) hextremeSegment
    have hextremeNotOrthant : extreme ∉ NonnegativeOrthant ι := by
      intro hnonnegative
      exact hextremeNotD ⟨hextremeHull, hnonnegative⟩
    obtain ⟨w, hwSegment, hwFrontier⟩ :=
      exists_frontier_on_segment_of_mem_notMem hinsideD.2
        hextremeNotOrthant
    obtain ⟨hwNonnegative, hwZero⟩ :=
      frontier_nonnegativeOrthant_has_zero hwFrontier
    have hwHull : w ∈ ColumnConvexHull M :=
      (convex_convexHull ℝ _).segment_subset hinsideD.1
        hextremeHull hwSegment
    have hwDZero : DZero M w := ⟨⟨hwHull, hwNonnegative⟩, hwZero⟩
    have hinsideSlice : inside ∈ SubfamilyHull
        (fun who owner => (1 - η) * y who + η * M who owner)
        (ZeroCoordinates y) :=
      affine_slice_mem_subfamilyHull M (ZeroCoordinates y) η hs
    have hextremeSlice : extreme ∈ SubfamilyHull
        (fun who owner => (1 - η) * y who + η * M who owner)
        (ZeroCoordinates y) := by
      apply subset_convexHull ℝ
      exact ⟨⟨owner, howner⟩, rfl⟩
    have hwSlice : w ∈ SubfamilyHull
        (fun who owner => (1 - η) * y who + η * M who owner)
        (ZeroCoordinates y) :=
      (convex_convexHull ℝ _).segment_subset
        hinsideSlice hextremeSlice hwSegment
    exact theorem32Conclusion_of_slice_boundary M hy hwDZero hbound
      hdiag hzero hηpos hηone hηε hwSlice

/-! Theorem 3.3, under Theorem 2.11(2)'s standing hypotheses: the derived
matrix has zero diagonal, is Q, and its homogeneous projective problem has no
nontrivial solution. Every `y∈D₀` and `ε>0` then admits a building block. -/
theorem theorem3_2
    (M : ι → ι → ℝ) {y : ι → ℝ} (hy : DZero M y)
    (hbound : MatrixPayoffsBounded M) (hdiag : ∀ i, M i i = 0) (hzero :
      ¬HasNontrivialZeroProjectiveLCPSolution M) (hQ : QMatrix M)
    {ε : ℝ} (hε : 0 < ε) : Theorem32Conclusion M y ε := by
  by_cases hmember : y ∈ SubfamilyHull M (ZeroCoordinates y)
  · exact theorem32Conclusion_of_mem_subfamilyHull M hy hbound hdiag
      hzero hmember hε
  · by_cases hintersection :
        AugmentedHull M (ZeroCoordinates y) y ∩ D M = {y}
    · exact lemma3_3 M hy hbound hdiag hzero hQ hmember hintersection hε
    · exact lemma3_4 M hy hbound hdiag hzero hQ hmember hintersection hε

/-! **Theorem 3.5 (paper, corrected endpoint).** If `(X,d)` is a nonempty
complete metric space and `f:X→X` has no fixed point, then for every `c>0`
and `C≥0` there are `K` and `x¹,…,xᴷ` with
`Σ_k d(xᵏ,f(xᵏ))>C` and `Σ_{k<K}d(xᵏ⁺¹,f(xᵏ))<c`. The paper proof uses
transfinite recursion. The printed `c≥0` cannot include `c=0`, because the
second conclusion is then a strict inequality between a nonnegative sum and
zero. -/

/-! The displacement along a finite list `x¹,…,xᵏ`. -/
def PathDisplacement {X : Type*} [PseudoMetricSpace X]
    (f : X → X) : List X → ℝ
  | [] => 0
  | x :: xs => dist x (f x) + PathDisplacement f xs

/-! The tracking error of a finite list whose first point is intended to
follow `anchor`; subsequent points are intended to follow their predecessor
under `f`. -/
def PathTrackingFrom {X : Type*} [PseudoMetricSpace X]
    (f : X → X) (anchor : X) : List X → ℝ
  | [] => 0
  | x :: xs => dist x anchor + PathTrackingFrom f (f x) xs

theorem pathTrackingFrom_nonneg {X : Type*} [PseudoMetricSpace X]
    (f : X → X) (anchor : X) (xs : List X) :
    0 ≤ PathTrackingFrom f anchor xs := by
  induction xs generalizing anchor with
  | nil => simp [PathTrackingFrom]
  | cons x xs ih =>
      simp only [PathTrackingFrom]
      exact add_nonneg dist_nonneg (ih (f x))

/-! The finite-sequence conclusion of Theorem 3.5. The head is `x¹`; the
list contains `x²,…,xᵏ`, so its tracking error starts at `f(x¹)`. -/
def ApproximationWitness {X : Type*} [PseudoMetricSpace X]
    (f : X → X) (c C : ℝ) : Prop :=
  ∃ x : X, ∃ xs : List X,
    C < dist x (f x) + PathDisplacement f xs ∧
    PathTrackingFrom f (f x) xs < c

/-! Supremum of the displacement attainable from `anchor` while spending
less than half of the tracking budget. This is the Caristi potential in the
short proof of Theorem 3.5. -/
def RemainingDisplacement {X : Type*} [PseudoMetricSpace X]
    (f : X → X) (c : ℝ) (anchor : X) : ℝ :=
  sSup {value | ∃ xs : List X,
    PathTrackingFrom f anchor xs < c / 2 ∧
    value = PathDisplacement f xs}

/-! Theorem 3.5: a fixed-point-free map admits large displacement with small
tracking error on a finite sequence. -/
theorem theorem3_5 {X : Type*} [MetricSpace X] [Nonempty X]
    [CompleteSpace X] (f : X → X) (hfixed : ∀ x, f x ≠ x)
    (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ApproximationWitness f c C := by
  by_contra hno
  have hpathBound {x : X} {xs : List X}
      (htracking : PathTrackingFrom f (f x) xs < c) :
      dist x (f x) + PathDisplacement f xs ≤ C := by
    by_contra hnot
    exact hno ⟨x, xs, lt_of_not_ge hnot, htracking⟩
  have hset_nonempty (anchor : X) :
      {value | ∃ xs : List X,
        PathTrackingFrom f anchor xs < c / 2 ∧
        value = PathDisplacement f xs}.Nonempty := by
    refine ⟨0, [], ?_, rfl⟩
    simp [PathTrackingFrom, hc]
  have hset_bdd (anchor : X) : BddAbove
      {value | ∃ xs : List X,
        PathTrackingFrom f anchor xs < c / 2 ∧
        value = PathDisplacement f xs} := by
    refine ⟨C, ?_⟩
    rintro value ⟨xs, htracking, rfl⟩
    cases xs with
    | nil => simpa [PathDisplacement] using hC
    | cons x xs =>
        apply hpathBound
        have htail := pathTrackingFrom_nonneg f (f x) xs
        have hdistance : 0 ≤ dist x anchor := dist_nonneg
        simp only [PathTrackingFrom] at htracking
        linarith
  let φ : X → ℝ := RemainingDisplacement f c
  have hφ_nonneg (anchor : X) : 0 ≤ φ anchor := by
    apply le_csSup (hset_bdd anchor)
    exact ⟨[], by simp [PathTrackingFrom, hc], rfl⟩
  have hφ_bdd : BddBelow (Set.range φ) := by
    exact ⟨0, by rintro _ ⟨anchor, rfl⟩; exact hφ_nonneg anchor⟩
  have hφ_lsc : LowerSemicontinuous φ := by
    rw [lowerSemicontinuous_iff]
    intro anchor y hy
    dsimp [φ, RemainingDisplacement] at hy ⊢
    obtain ⟨value, hvalue, hyvalue⟩ := exists_lt_of_lt_csSup
      (hset_nonempty anchor) hy
    obtain ⟨xs, htracking, rfl⟩ := hvalue
    have hcontinuous : ContinuousAt
        (fun nextAnchor => PathTrackingFrom f nextAnchor xs) anchor := by
      cases xs with
      | nil => simpa [PathTrackingFrom] using continuousAt_const
      | cons x xs =>
          simp only [PathTrackingFrom]
          fun_prop
    filter_upwards [hcontinuous.eventually (gt_mem_nhds htracking)]
      with nextAnchor hnext
    exact hyvalue.trans_le
      (le_csSup (hset_bdd nextAnchor) ⟨xs, hnext, rfl⟩)
  have hcaristi (x : X) : dist x (f x) ≤ φ x - φ (f x) := by
    have hsuple : φ (f x) ≤ φ x - dist x (f x) := by
      apply csSup_le (hset_nonempty (f x))
      intro value hvalue
      obtain ⟨xs, htracking, rfl⟩ := hvalue
      have hmem : dist x (f x) + PathDisplacement f xs ∈
          {value | ∃ ys : List X,
            PathTrackingFrom f x ys < c / 2 ∧
            value = PathDisplacement f ys} := by
        refine ⟨x :: xs, ?_, ?_⟩
        · simpa [PathTrackingFrom] using htracking
        · simp [PathDisplacement]
      have hupper := le_csSup (hset_bdd x) hmem
      dsimp [φ, RemainingDisplacement]
      linarith
    linarith
  obtain ⟨x, hx⟩ := MathUE.exists_fixedPoint_of_caristi
    f φ hφ_lsc hφ_bdd hcaristi
  exact hfixed x hx

/-! **Lemmas 3.6--3.8 (paper).** For the kiloblock strategy `ξ*` built from
Theorem 3.2 and Theorem 3.5, the paper proves (i) its payoff is within
`2ε` of `w(yᴷ)` for normal players, (ii) continuation by any normal player
still terminates with probability at least `1-ε` before the final kiloblock,
and (iii) every pure deviation gains at most `5ε`. The following record is a
paper-local carrier for the induced quantities used in those statements. -/

/-! Induced payoff, deviation payoff, and continuation-termination data for
the paper's kiloblock strategy `ξ*`. -/
structure KiloblockProfile (ι : Type) [Fintype ι] [DecidableEq ι] where
  payoff : Payoff ι
  unilateralPayoff : ι → ℝ
  continueTermination : ι → ℝ

/-! A kiloblock construction generated from a Theorem 3.2 building block. -/
structure KiloblockConstruction
    (M : ι → ι → ℝ) (ε : ℝ) where
  profile : KiloblockProfile ι
  target : Payoff ι
  buildingBlock : ∃ y, DZero M y ∧ Theorem32Conclusion M y ε

/-! Lemma 3.6: for normal `i`, `|γ_i(ξ*)-w_i(yᴷ)|<2ε`. -/
theorem lemma3_6
    (M : ι → ι → ℝ) {ε : ℝ} (hε : 0 < ε)
    (construction : KiloblockConstruction M ε) :
    ∀ i ∈ NormalCore M,
      |construction.profile.payoff i - construction.target i| < 2 * ε := by
  sorry

/-! Lemma 3.7: continuing by a normal player still terminates with probability
at least `1-ε` before the last kiloblock. -/
theorem lemma3_7
    (M : ι → ι → ℝ) {ε : ℝ} (hε : 0 < ε)
    (construction : KiloblockConstruction M ε) :
    ∀ i ∈ NormalCore M,
      construction.profile.continueTermination i ≥ 1 - ε := by
  sorry

/-! Lemma 3.8: every pure deviation gains at most `5ε`. -/
theorem lemma3_8
    {M : ι → ι → ℝ} {ε : ℝ} (hε : 0 < ε)
    (construction : KiloblockConstruction M ε) :
    ∀ i, construction.profile.unilateralPayoff i ≤
      construction.target i + 5 * ε := by
  sorry

/-! Section 3.4 concludes from Lemmas 3.6--3.8 that the constructed profile
is a sunspot `7ε`-equilibrium. -/

/-! Section 3.4: the constructed profile is a sunspot `7ε`-equilibrium. -/
theorem section3_4
    (table : Table ι) (profile : SunspotProfile table)
    (target : Payoff ι) (ε : ℝ)
    (hpayoff : ∀ who, |profile.payoff who - target who| < 2 * ε)
    (hdeviation : ∀ who
      (deviation : (publicQuittingGame table profile.signalLaw).BehaviorStrategy who),
      publicQuittingPayoff table profile.signalLaw
        (Function.update profile.strategy who deviation) who ≤
          target who + 5 * ε) :
    SunspotEpsilonEquilibrium table (7 * ε) profile := by
  intro who deviation
  have hlower := (abs_lt.mp (hpayoff who)).1
  have hupper := hdeviation who deviation
  dsimp only [SunspotProfile.payoff] at hlower
  linarith

/-! ## Section 4 — sunspot payoff characterization -/

/-! **Definition (paper, Section 4).** A vector is a sunspot equilibrium
payoff if it is the limit of payoffs of sunspot ε-equilibria as ε↓0. -/

/-! A sunspot equilibrium payoff is a limit of payoffs of sunspot
ε-equilibria as `ε↓0`. -/
def SunspotEquilibriumPayoff
    (table : Table ι) (value : Payoff ι) : Prop :=
  ∃ profiles : ℕ → SunspotProfile table,
    (∀ n : ℕ, SunspotEpsilonEquilibrium table
      ((n + 1 : ℝ)⁻¹) (profiles n)) ∧
    ∀ who, Tendsto (fun n => (profiles n).payoff who) atTop (𝓝 (value who))

/-! **M-matrix convention (paper).** Since the diagonal of `R̂` is zero, the
paper calls a Q-matrix an M-matrix when every row and every column has exactly
one positive entry. -/

/-! The v1 paper's M-matrix convention: Q, with exactly one positive entry in
each row and column. -/
def MMatrix (M : ι → ι → ℝ) : Prop :=
  QMatrix M ∧
    (∀ who, (Finset.filter (fun owner => 0 < M who owner) Finset.univ).card = 1) ∧
    (∀ owner, (Finset.filter (fun who => 0 < M who owner) Finset.univ).card = 1)

/-! `conv{rⁱ : i∈I*}` in the full payoff space of all players. -/
def NormalSingletonHull (table : Table ι) : Set (Payoff ι) :=
  convexHull ℝ (Set.range fun owner : NormalCore (DerivedMatrix table) =>
    fun who => table.terminal (quittingProjectiveSingletonTerminal owner) who)

/-! `D̃ = conv{rⁱ : i∈I*} ∩ ℝ^N_{≥0}` from Section 4. -/
def TildeD (table : Table ι) : Set (Payoff ι) :=
  NormalSingletonHull table ∩ {value | ∀ who, 0 ≤ value who}

/-! **Theorem 4.1 (paper).** If `R̂` is an M-matrix, every vector in
`D~ = conv(r¹,…,rⁿ)∩ℝⁿ_≥0` is a sunspot equilibrium payoff. -/

/-! Theorem 4.1: an M-matrix makes every `v∈D~` a sunspot equilibrium payoff. -/
theorem theorem4_1
    (table : Table ι)
    (hnormalized : SoloExitNormalized table)
    (hbounded : TablePayoffsBounded table)
    (hM : MMatrix (NormalMatrix (DerivedMatrix table))) :
    ∀ value ∈ TildeD table, SunspotEquilibriumPayoff table value := by
  sorry

/-! ## Section 5 — discussion and open problems -/

/-! The paper discusses stopping games, absorbing games, the need for a
uniform lower bound on quitting probabilities, finite-range recursions, the
inverse-positivity question for zero-diagonal Q-matrices, and the question
whether a column with strictly negative off-diagonal entries forces Q. These
are open-problem prose, not Lean theorem declarations. -/

end
end Literature.SolanAndSolan2020
