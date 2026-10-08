import Literature.FleschThuijsmanAndVrieze1997
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import MathUE.Probability.RatioProperPair
import UniformEquilibrium.ProofView.Concepts.Existence.CompactNash
import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.RecursiveAbsorption.ProperPairLimit
import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.RecursiveAbsorption.BestReplyMassEstimate
import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.Quitting.PathwisePayoff

/-!
# Recursive repeated games with absorbing states

J. Flesch, F. Thuijsman and O. J. Vrieze, *Mathematics of Operations Research*
21 (1996), 1016–1022. DOI: `10.1287/moor.21.4.1016`.
Primary source: <https://dke.maastrichtuniversity.nl/f.thuijsman/recursive%20repeated.pdf>.

This is a partial paper audit. Definition 2.3 and Theorem 2.4 use the paper's
finite probability simplexes and absorption-weighted reward tables, delegating
the proper-pair construction to the generic ratio-ranking theorem. Lemma 2.2
and Theorem 3.1 additionally delegate to actual expected-pathwise-liminf results
for the canonical model with arbitrary finite live-state actions and literal
action-independent absorbing rewards. Definition 2.1's canonical action sets
and Lemma 3.2's arbitrary-sequence estimates use actual behavioral best replies.
Example 3
is the same three-player game analyzed in the 1997 paper, so its table and
stationary conclusions delegate to that existing formalization. The printed
exclusion for every positive error is refuted; the corrected exclusion below
one positive threshold is retained. The actual all-profile quitting payoff
identity also transports these conclusions to the paper's expected-pathwise-
liminf convention at every initial state.

## Sections 1–3: source inventory

Section 1 introduces finite stochastic games and expected pathwise limiting
average payoffs. Definition 2.1 introduces absorption probabilities, carriers,
absorbing pure actions and pure best replies. Lemma 2.2 gives the stationary
payoff ratio. Definition 2.3 introduces proper and delta-proper strategy pairs;
Theorem 2.4 proves existence of a proper pair. Theorem 3.1 proves stationary
approximate-equilibrium existence for two-player recursive repeated games with
absorbing states; Lemma 3.2 supplies its best-reply mass-ratio estimate.

Definition 2.3 and Theorem 2.4 are formalized below in their numerical-table
presentation. The canonical Lemma 2.2 identifies the actual stationary payoff,
including zero absorption. The canonical Theorem 3.1 selects one stationary
pair before every initial state and every unilateral behavioral deviation.
It is not a proof of the paper's reduction of general absorbing stage games
with state-dependent action sets to action-independent absorbing rewards.
Example 1's table, printed delta-proper family and proper limit are formalized
below. The printed family's equilibrium exclusions have explicit small-error
thresholds; they are not exclusions of every stationary pair. Its separate
exact stationary witness corrects the specific Section 4 cross-reference.
Example 2's literal table, delta-proper families and both proper limits are
presented below. The absorbing limit's exclusion has an explicit small-error
threshold. Both printed approximate-equilibrium constructions are represented
below for every sufficiently small positive real delta, with the recurrent
construction using its fixed limiting column. Their sequence formulations
also apply to every positive delta sequence tending to zero.
Remark 2's payoff-convention equality is formalized for the canonical model,
even for arbitrary behavioral profiles. Canonical Remark 3 selects one
stationary pair with limiting Nash bounds and a common finite-horizon cutoff.
Remark 1's literal subset-constrained domain, compact convex geometry and
sufficiently-small-delta feasibility are formalized below. Its unrestricted
printed delta range is refuted by the empty two-action domain at delta 3/4.
Restricted linearized auxiliary Nash existence is established for sufficiently
small delta on that literal domain. Its limiting ranking properties and the
remark's nonlinear restricted-game assertion remain separate obligations.
Example 4 is not formalized here. The original-model
versions of Remarks 2 and 3 still require the absorbing-stage reduction.
The canonical statements do not settle the original model reduction. This file
does not claim complete paper coverage or a fixed-target
uniform-equilibrium payoff from Theorem 3.1.
-/

noncomputable section

open _root_.Math.ProbabilityMassFunction
open Filter MeasureTheory
open scoped BigOperators Topology

namespace Literature.FleschThuijsmanAndVrieze1996

/-! ## Section 2: proper strategy pairs

The table records the absorption probability and both absorbing rewards for
each live-state action pair. The live-state stage reward is zero. Rewards at
zero-probability entries are immaterial: multiplication by the absorption
probability implements the paper's convention that those entries have value
zero. The canonical game below consumes precisely these data; its absorbers
have literal action-independent rewards. No reduction from general absorbing
stage games is asserted.

Stationary strategies are literally finite real probability vectors. Pure
stationary values below are the ratios in Lemma 2.2, with value zero when the
denominator vanishes. Their agreement with the canonical game's actual payoff
is identified below. Definition 2.3 uses these numerical ratios; its proper-pair
limit is along a discrete sequence, as specified by the paper's basic assumptions.
-/

/-- Canonical two-player absorption probabilities and absorbing payoff tables. -/
structure AbsorbingGameData (I J : Type*) where
  absorptionProbability : I → J → Set.Icc (0 : ℝ) 1
  reward1 : I → J → ℝ
  reward2 : I → J → ℝ

/-- The paper's simplex of stationary strategies at the live state. -/
abbrev StationaryStrategy (I : Type*) [Fintype I] :=
  {x : I → ℝ // x ∈ GameTheory.Math.Probability.simplexWeights I}

namespace AbsorbingGameData

variable {I J : Type*}

def absorptionCoefficients (G : AbsorbingGameData I J) : I → J → ℝ :=
  fun i j => G.absorptionProbability i j

/-- Actual absorption-weighted player-one rewards, not independent numerator data. -/
def payoffNumerator1 (G : AbsorbingGameData I J) : I → J → ℝ :=
  fun i j => G.absorptionCoefficients i j * G.reward1 i j

/-- Actual absorption-weighted player-two rewards. -/
def payoffNumerator2 (G : AbsorbingGameData I J) : I → J → ℝ :=
  fun i j => G.absorptionCoefficients i j * G.reward2 i j

/-- Literal canonical absorption data, with the two source reward coordinates. -/
def canonicalData {A B : Type} (G : AbsorbingGameData A B) :
    GameTheory.RecursiveAbsorption.Data A B where
  absorption := G.absorptionProbability
  reward := fun i j who => Bool.rec (G.reward1 i j) (G.reward2 i j) who

end AbsorbingGameData

/-- The actual finite action law represented by a paper simplex strategy. -/
def stationaryLaw {A : Type*} [Fintype A] (x : StationaryStrategy A) : PMF A :=
  ofVector x.1 x.2

/-- One live state and literal action-independent absorbers for the source table. -/
abbrev canonicalGame {A B : Type} (G : AbsorbingGameData A B) :=
  GameTheory.RecursiveAbsorption.game G.canonicalData

/-- The paper strategies played as an actual stationary behavioral profile. -/
def canonicalStationaryProfile {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (x : StationaryStrategy A) (y : StationaryStrategy B) :
    (canonicalGame G).BehaviorProfile :=
  GameTheory.RecursiveAbsorption.stationaryProfile G.canonicalData
    (stationaryLaw x) (stationaryLaw y)

/-- Literal expected pathwise liminf under the canonical game's infinite-play law. -/
abbrev canonicalPayoff {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (initial : (canonicalGame G).State) :=
  GameTheory.RecursiveAbsorption.liminfPayoff G.canonicalData initial

/-- Definition 2.1: the carrier is the set of positive own strategy coordinates. -/
def stationaryCarrier {A : Type*} [Fintype A] (x : StationaryStrategy A) : Set A :=
  {i | 0 < x.1 i}

/-- Definition 2.1: the actual one-stage probability of leaving the live state. -/
def canonicalAbsorptionProbability {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (x : StationaryStrategy A) (y : StationaryStrategy B) : ℝ :=
  GameTheory.RecursiveAbsorption.absorptionMass G.canonicalData
    (stationaryLaw x) (stationaryLaw y)

/-- Definition 2.1: rows with positive absorption against the opponent's strategy. -/
def absorbingPureRows {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (y : StationaryStrategy B) : Set A :=
  {i | 0 < GameTheory.RecursiveAbsorption.absorptionMass G.canonicalData
    (PMF.pure i) (stationaryLaw y)}

/-- Definition 2.1's analogous positive-absorption column set. -/
def absorbingPureColumns {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (x : StationaryStrategy A) : Set B :=
  {j | 0 < GameTheory.RecursiveAbsorption.absorptionMass G.canonicalData
    (stationaryLaw x) (PMF.pure j)}

/-- Definition 2.1: pure rows that cap every actual behavioral reply. -/
def pureBestReplies1 {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (y : StationaryStrategy B) : Set A :=
  {i | GameTheory.RecursiveAbsorption.IsRowBestReply G.canonicalData (stationaryLaw y) i}

/-- Definition 2.1: pure column best replies against all behavioral strategies. -/
def pureBestReplies2 {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (x : StationaryStrategy A) : Set B :=
  {j | GameTheory.RecursiveAbsorption.IsColumnBestReply G.canonicalData (stationaryLaw x) j}

/-- Definition 2.1's pure behavioral-best-reply row set is nonempty. -/
theorem pureBestReplies1_nonempty {A B : Type} [Fintype A] [Fintype B] [Nonempty A]
    (G : AbsorbingGameData A B) (y : StationaryStrategy B) :
    (pureBestReplies1 G y).Nonempty := by
  classical
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => GameTheory.RecursiveAbsorption.stationaryPayoff G.canonicalData
      (PMF.pure i) (stationaryLaw y) false) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  exact (GameTheory.RecursiveAbsorption.isRowBestReply_iff_pure_max
    G.canonicalData (stationaryLaw y) i).mpr (fun e => hmax e (Finset.mem_univ e))

/-- The analogous pure behavioral-best-reply column set is nonempty. -/
theorem pureBestReplies2_nonempty {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (G : AbsorbingGameData A B) (x : StationaryStrategy A) :
    (pureBestReplies2 G x).Nonempty := by
  classical
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j => GameTheory.RecursiveAbsorption.stationaryPayoff G.canonicalData
      (stationaryLaw x) (PMF.pure j) true) Finset.univ_nonempty
  refine ⟨j, ?_⟩
  exact (GameTheory.RecursiveAbsorption.isColumnBestReply_iff_pure_max
    G.canonicalData (stationaryLaw x) j).mpr (fun f => hmax f (Finset.mem_univ f))

/-- Lemma 2.2 for the canonical game, with zero-denominator value zero included. -/
theorem lemma2_2_canonical {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (x : StationaryStrategy A) (y : StationaryStrategy B)
    (who : Bool) :
    canonicalPayoff G none (canonicalStationaryProfile G x y) who =
      GameTheory.RecursiveAbsorption.absorbingContribution G.canonicalData
        (stationaryLaw x) (stationaryLaw y) who /
      GameTheory.RecursiveAbsorption.absorptionMass G.canonicalData
        (stationaryLaw x) (stationaryLaw y) :=
  GameTheory.RecursiveAbsorption.liminfPayoff_stationary_none
    G.canonicalData (stationaryLaw x) (stationaryLaw y) who

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The numerical pure row payoff in Lemma 2.2's stationary ratio presentation. -/
def pureStationaryPayoff1 (G : AbsorbingGameData I J)
    (y : StationaryStrategy J) (i : I) : ℝ :=
  Math.Probability.RatioProperPair.rowRatio
    G.absorptionCoefficients G.payoffNumerator1 y.1 i

/-- The analogous numerical pure column payoff. -/
def pureStationaryPayoff2 (G : AbsorbingGameData I J)
    (x : StationaryStrategy I) (j : J) : ℝ :=
  Math.Probability.RatioProperPair.columnRatio
    G.absorptionCoefficients G.payoffNumerator2 x.1 j

/-- The numerical pure row value is the canonical game's actual stationary value. -/
theorem pureStationaryPayoff1_eq_canonical {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (y : StationaryStrategy B) (i : A) :
    pureStationaryPayoff1 G y i =
      canonicalPayoff G none
        (GameTheory.RecursiveAbsorption.stationaryProfile G.canonicalData
          (PMF.pure i) (stationaryLaw y)) false := by
  calc
    _ = GameTheory.RecursiveAbsorption.stationaryPayoff G.canonicalData
        (PMF.pure i) (stationaryLaw y) false := by
      have hratio := GameTheory.RecursiveAbsorption.rowRatio_eq_stationaryPayoff
        G.canonicalData (stationaryLaw y) false i
      change Math.Probability.RatioProperPair.rowRatio G.absorptionCoefficients
        G.payoffNumerator1 (toVector (stationaryLaw y)) i =
          GameTheory.RecursiveAbsorption.stationaryPayoff G.canonicalData
            (PMF.pure i) (stationaryLaw y) false at hratio
      simpa only [pureStationaryPayoff1, stationaryLaw, toVector_ofVector] using hratio
    _ = _ := (GameTheory.RecursiveAbsorption.liminfPayoff_stationary_none
      G.canonicalData (PMF.pure i) (stationaryLaw y) false).symm

/-- The corresponding numerical pure column value has the same actual semantics. -/
theorem pureStationaryPayoff2_eq_canonical {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (x : StationaryStrategy A) (j : B) :
    pureStationaryPayoff2 G x j =
      canonicalPayoff G none
        (GameTheory.RecursiveAbsorption.stationaryProfile G.canonicalData
          (stationaryLaw x) (PMF.pure j)) true := by
  calc
    _ = GameTheory.RecursiveAbsorption.stationaryPayoff G.canonicalData
        (stationaryLaw x) (PMF.pure j) true := by
      have hratio := GameTheory.RecursiveAbsorption.columnRatio_eq_stationaryPayoff
        G.canonicalData (stationaryLaw x) true j
      change Math.Probability.RatioProperPair.columnRatio G.absorptionCoefficients
        G.payoffNumerator2 (toVector (stationaryLaw x)) j =
          GameTheory.RecursiveAbsorption.stationaryPayoff G.canonicalData
            (stationaryLaw x) (PMF.pure j) true at hratio
      simpa only [pureStationaryPayoff2, stationaryLaw, toVector_ofVector] using hratio
    _ = _ := (GameTheory.RecursiveAbsorption.liminfPayoff_stationary_none
      G.canonicalData (stationaryLaw x) (PMF.pure j) true).symm

/-- Lemma 2.2's second quotient, weighted by the pure rows' absorption probabilities. -/
theorem lemma2_2_absorptionWeightedRow_canonical {A B : Type}
    [Fintype A] [Fintype B] (G : AbsorbingGameData A B)
    (x : StationaryStrategy A) (y : StationaryStrategy B) :
    canonicalPayoff G none (canonicalStationaryProfile G x y) false =
      (∑ i, x.1 i *
        GameTheory.RecursiveAbsorption.absorptionMass G.canonicalData
          (PMF.pure i) (stationaryLaw y) * pureStationaryPayoff1 G y i) /
      (∑ i, x.1 i * GameTheory.RecursiveAbsorption.absorptionMass G.canonicalData
        (PMF.pure i) (stationaryLaw y)) := by
  have hpure : ∀ i, pureStationaryPayoff1 G y i =
      GameTheory.RecursiveAbsorption.stationaryPayoff G.canonicalData
        (PMF.pure i) (stationaryLaw y) false := fun i =>
    (pureStationaryPayoff1_eq_canonical G y i).trans
      (GameTheory.RecursiveAbsorption.liminfPayoff_stationary_none
        G.canonicalData (PMF.pure i) (stationaryLaw y) false)
  rw [lemma2_2_canonical,
    GameTheory.RecursiveAbsorption.absorbingContribution_eq_expect_mass_mul_pureRowPayoff
      G.canonicalData (stationaryLaw x) (stationaryLaw y) false,
    GameTheory.RecursiveAbsorption.absorptionMass_eq_expect_pureRow
      G.canonicalData (stationaryLaw x) (stationaryLaw y)]
  simp only [Math.Probability.expect_eq_sum, stationaryLaw, ofVector_toReal,
    hpure, mul_assoc]

/-- The corresponding absorption-weighted pure-column quotient in Lemma 2.2. -/
theorem lemma2_2_absorptionWeightedColumn_canonical {A B : Type}
    [Fintype A] [Fintype B] (G : AbsorbingGameData A B)
    (x : StationaryStrategy A) (y : StationaryStrategy B) :
    canonicalPayoff G none (canonicalStationaryProfile G x y) true =
      (∑ j, y.1 j *
        GameTheory.RecursiveAbsorption.absorptionMass G.canonicalData
          (stationaryLaw x) (PMF.pure j) * pureStationaryPayoff2 G x j) /
      (∑ j, y.1 j * GameTheory.RecursiveAbsorption.absorptionMass G.canonicalData
        (stationaryLaw x) (PMF.pure j)) := by
  have hpure : ∀ j, pureStationaryPayoff2 G x j =
      GameTheory.RecursiveAbsorption.stationaryPayoff G.canonicalData
        (stationaryLaw x) (PMF.pure j) true := fun j =>
    (pureStationaryPayoff2_eq_canonical G x j).trans
      (GameTheory.RecursiveAbsorption.liminfPayoff_stationary_none
        G.canonicalData (stationaryLaw x) (PMF.pure j) true)
  rw [lemma2_2_canonical,
    GameTheory.RecursiveAbsorption.absorbingContribution_eq_expect_mass_mul_pureColumnPayoff
      G.canonicalData (stationaryLaw x) (stationaryLaw y) true,
    GameTheory.RecursiveAbsorption.absorptionMass_eq_expect_pureColumn
      G.canonicalData (stationaryLaw x) (stationaryLaw y)]
  simp only [Math.Probability.expect_eq_sum, stationaryLaw, ofVector_toReal,
    hpure, mul_assoc]

/-- Definition 2.3: full mixing and both strict-payoff ranking inequalities. -/
def IsDeltaProperPair (G : AbsorbingGameData I J) (δ : ℝ)
    (x : StationaryStrategy I) (y : StationaryStrategy J) : Prop :=
  Math.Probability.RatioProperPair.IsDeltaProperPair
    G.absorptionCoefficients G.payoffNumerator1 G.payoffNumerator2 δ x.1 y.1

/-- Definition 2.3: a limit of delta-proper pairs with positive delta tending to zero. -/
def IsProperPair (G : AbsorbingGameData I J)
    (x : StationaryStrategy I) (y : StationaryStrategy J) : Prop :=
  Math.Probability.RatioProperPair.IsProperPair
    G.absorptionCoefficients G.payoffNumerator1 G.payoffNumerator2 x.1 y.1

/-! ### Example 1

Only the first row/first column entry stays live. The other three entries
absorb with probability one. The printed family has both players use
`(1 - delta^2, delta^2)`. The proper-limit conclusion uses an explicit sequence;
the small-error exclusions below apply actual behavioral pure deviations.
-/

/-- The literal zero-sum table in Example 1. -/
def example1Data : AbsorbingGameData (Fin 2) (Fin 2) where
  absorptionProbability := fun i j =>
    if i = 0 ∧ j = 0 then ⟨0, by constructor <;> norm_num⟩
    else ⟨1, by constructor <;> norm_num⟩
  reward1 := !![0, 2; 1, 0]
  reward2 := !![0, -2; -1, 0]

/-- The common printed strategy, on a concrete sufficiently-small delta interval. -/
def example1Strategy (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    StationaryStrategy (Fin 2) :=
  ⟨![1 - δ ^ 2, δ ^ 2], by
    rw [GameTheory.Math.Probability.mem_simplexWeights]
    constructor
    · intro i
      fin_cases i <;> norm_num [abs_of_nonneg hδ0] <;>
        nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hδhalf)]
    · simp [Fin.sum_univ_two]⟩

theorem example1_pureStationaryPayoff1 (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (i : Fin 2) :
    pureStationaryPayoff1 example1Data (example1Strategy δ hδ.le hδhalf) i =
      ![2, 1 - δ ^ 2] i := by
  fin_cases i <;>
    norm_num [pureStationaryPayoff1, Math.Probability.RatioProperPair.rowRatio,
      AbsorbingGameData.payoffNumerator1, AbsorbingGameData.absorptionCoefficients,
      example1Data, example1Strategy, Fin.sum_univ_two]
  field_simp [hδ.ne']

theorem example1_pureStationaryPayoff2 (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (j : Fin 2) :
    pureStationaryPayoff2 example1Data (example1Strategy δ hδ.le hδhalf) j =
      ![-1, -2 + 2 * δ ^ 2] j := by
  fin_cases j <;>
    norm_num [pureStationaryPayoff2, Math.Probability.RatioProperPair.columnRatio,
      AbsorbingGameData.payoffNumerator2, AbsorbingGameData.absorptionCoefficients,
      example1Data, example1Strategy, Fin.sum_univ_two]
  · field_simp [hδ.ne']
  · ring

/-- The printed Example 1 family is delta-proper for sufficiently small positive delta. -/
theorem example1_deltaProper (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    IsDeltaProperPair example1Data δ (example1Strategy δ hδ.le hδhalf)
      (example1Strategy δ hδ.le hδhalf) := by
  have hsq : δ ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδhalf)]
  have hfactor : δ ≤ 1 - δ ^ 2 := by linarith
  have hrank : δ ^ 2 ≤ δ * (1 - δ ^ 2) := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hfactor hδ.le
  refine ⟨hδ, by linarith, (example1Strategy δ hδ.le hδhalf).2,
    (example1Strategy δ hδ.le hδhalf).2, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [example1Strategy, abs_of_nonneg hδ.le] <;>
      nlinarith [sq_pos_of_pos hδ]
  · intro j
    fin_cases j <;> norm_num [example1Strategy, abs_of_nonneg hδ.le] <;>
      nlinarith [sq_pos_of_pos hδ]
  · intro i e h
    change pureStationaryPayoff1 example1Data (example1Strategy δ hδ.le hδhalf) e <
      pureStationaryPayoff1 example1Data (example1Strategy δ hδ.le hδhalf) i at h
    rw [example1_pureStationaryPayoff1, example1_pureStationaryPayoff1] at h
    fin_cases i <;> fin_cases e <;> norm_num at h
    all_goals
      norm_num [example1Strategy]
      nlinarith
  · intro j f h
    change pureStationaryPayoff2 example1Data (example1Strategy δ hδ.le hδhalf) f <
      pureStationaryPayoff2 example1Data (example1Strategy δ hδ.le hδhalf) j at h
    rw [example1_pureStationaryPayoff2, example1_pureStationaryPayoff2] at h
    fin_cases j <;> fin_cases f <;> norm_num at h
    all_goals
      norm_num [example1Strategy]
      nlinarith

/-- The equal mixture of the two rows, distinct from the printed delta family. -/
def example1HalfStrategy : StationaryStrategy (Fin 2) :=
  ⟨![1 / 2, 1 / 2], by
    rw [GameTheory.Math.Probability.mem_simplexWeights]
    constructor
    · intro i
      fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_two]⟩

/-- The first pure action used in the Example 1 limit and source audit. -/
def example1FirstStrategy : StationaryStrategy (Fin 2) :=
  example1Strategy 0 le_rfl (by norm_num)

private theorem exists_exampleDeltaSequence :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ n, 0 < δ n ∧ δ n ≤ 1 / 2 := by
  let δ : ℕ → ℝ := fun n => (1 / 2 : ℝ) * (1 / (n + 1 : ℝ))
  have hδ : ∀ n, 0 < δ n ∧ δ n ≤ 1 / 2 := by
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hinv : (1 / (n + 1 : ℝ)) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    constructor
    · dsimp [δ]
      positivity
    · simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hδlimit : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0)).const_mul (1 / 2 : ℝ)
  exact ⟨δ, hδlimit, hδ⟩

/-- The first/first limit of the printed delta family is a proper pair. -/
theorem example1_firstFirst_proper :
    IsProperPair example1Data example1FirstStrategy example1FirstStrategy := by
  obtain ⟨δ, hδlimit, hδ⟩ := exists_exampleDeltaSequence
  let xs : ℕ → StationaryStrategy (Fin 2) :=
    fun n => example1Strategy (δ n) (hδ n).1.le (hδ n).2
  have hx : Tendsto (fun n => (xs n).1) atTop (𝓝 example1FirstStrategy.1) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · simpa [xs, example1Strategy, example1FirstStrategy] using
        (tendsto_const_nhds.sub (hδlimit.pow 2))
    · simpa [xs, example1Strategy, example1FirstStrategy] using hδlimit.pow 2
  exact ⟨example1FirstStrategy.2, example1FirstStrategy.2,
    δ, (fun n => (xs n).1), (fun n => (xs n).1), hδlimit, hx, hx,
    fun n => example1_deltaProper (δ n) (hδ n).1 (hδ n).2⟩

private theorem pureRowPayoff_le_of_canonicalNash {A B : Type}
    [Fintype A] [Fintype B] (G : AbsorbingGameData A B)
    (x : StationaryStrategy A) (y : StationaryStrategy B) {ε : ℝ}
    (hNash : (canonicalGame G).IsεAsymptoticNash (canonicalPayoff G none) ε
      (canonicalStationaryProfile G x y)) (i : A) :
    pureStationaryPayoff1 G y i ≤
      canonicalPayoff G none (canonicalStationaryProfile G x y) false + ε := by
  have hprofile : Function.update (canonicalStationaryProfile G x y)
      false (fun _ _ => PMF.pure i) =
        GameTheory.RecursiveAbsorption.stationaryProfile G.canonicalData
          (PMF.pure i) (stationaryLaw y) := by
    funext who time history
    cases who <;> simp [canonicalStationaryProfile,
      GameTheory.RecursiveAbsorption.stationaryProfile,
      GameTheory.StochasticGame.stationaryBehaviorProfile,
      GameTheory.RecursiveAbsorption.mixedAction] <;> rfl
  have h := hNash false (fun _ _ => PMF.pure i)
  rw [hprofile] at h
  exact (pureStationaryPayoff1_eq_canonical G y i).le.trans h

/-- The printed Example 1 family's live-state row payoff is strictly below three halves. -/
theorem example1_printedFamily_rowPayoff_lt (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) :
    canonicalPayoff example1Data none
      (canonicalStationaryProfile example1Data (example1Strategy δ hδ.le hδhalf)
        (example1Strategy δ hδ.le hδhalf)) false < 3 / 2 := by
  have hsq : δ ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδhalf)]
  have hfirst : 0 ≤ 1 - δ ^ 2 := by linarith
  have hmass : GameTheory.RecursiveAbsorption.absorptionMass example1Data.canonicalData
      (stationaryLaw (example1Strategy δ hδ.le hδhalf))
      (stationaryLaw (example1Strategy δ hδ.le hδhalf)) = δ ^ 2 * (2 - δ ^ 2) := by
    norm_num [GameTheory.RecursiveAbsorption.absorptionMass, Math.Probability.expect_eq_sum,
      stationaryLaw, ofVector_toReal, AbsorbingGameData.canonicalData,
      example1Data, example1Strategy, Fin.sum_univ_two,
      ENNReal.toReal_ofReal hfirst, ENNReal.toReal_ofReal (sq_nonneg δ)]
    ring
  have hnum : GameTheory.RecursiveAbsorption.absorbingContribution example1Data.canonicalData
      (stationaryLaw (example1Strategy δ hδ.le hδhalf))
      (stationaryLaw (example1Strategy δ hδ.le hδhalf)) false =
        3 * δ ^ 2 * (1 - δ ^ 2) := by
    norm_num [GameTheory.RecursiveAbsorption.absorbingContribution,
      Math.Probability.expect_eq_sum, stationaryLaw, ofVector_toReal,
      AbsorbingGameData.canonicalData, example1Data, example1Strategy, Fin.sum_univ_two,
      ENNReal.toReal_ofReal hfirst, ENNReal.toReal_ofReal (sq_nonneg δ)]
    ring
  rw [lemma2_2_canonical, hnum, hmass]
  apply (div_lt_iff₀ (mul_pos (sq_pos_of_pos hδ) (by linarith))).mpr
  nlinarith [sq_pos_of_pos (sq_pos_of_pos hδ)]

/-- The printed family is not an approximate equilibrium at errors at most one half. -/
theorem example1_printedFamily_not_smallErrorNash (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) {ε : ℝ} (hε : ε ≤ 1 / 2) :
    ¬ (canonicalGame example1Data).IsεAsymptoticNash
      (canonicalPayoff example1Data none) ε
      (canonicalStationaryProfile example1Data (example1Strategy δ hδ.le hδhalf)
        (example1Strategy δ hδ.le hδhalf)) := by
  intro hNash
  have hpure := pureRowPayoff_le_of_canonicalNash example1Data
    (example1Strategy δ hδ.le hδhalf) (example1Strategy δ hδ.le hδhalf) hNash 0
  rw [example1_pureStationaryPayoff1 δ hδ hδhalf] at hpure
  norm_num at hpure
  have hpayoff := example1_printedFamily_rowPayoff_lt δ hδ hδhalf
  linarith

/-- The proper first/first limit is not an approximate equilibrium at errors below one. -/
theorem example1_firstFirst_not_smallErrorNash {ε : ℝ} (hε : ε < 1) :
    ¬ (canonicalGame example1Data).IsεAsymptoticNash
      (canonicalPayoff example1Data none) ε
      (canonicalStationaryProfile example1Data example1FirstStrategy example1FirstStrategy) := by
  intro hNash
  have hpure := pureRowPayoff_le_of_canonicalNash example1Data
    example1FirstStrategy example1FirstStrategy hNash 1
  have hvalue : pureStationaryPayoff1 example1Data example1FirstStrategy 1 = 1 := by
    norm_num [pureStationaryPayoff1, Math.Probability.RatioProperPair.rowRatio,
      AbsorbingGameData.payoffNumerator1, AbsorbingGameData.absorptionCoefficients,
      example1Data, example1FirstStrategy, example1Strategy, Fin.sum_univ_two]
  have hpayoff : canonicalPayoff example1Data none
      (canonicalStationaryProfile example1Data example1FirstStrategy example1FirstStrategy)
        false = 0 := by
    rw [lemma2_2_canonical]
    norm_num [GameTheory.RecursiveAbsorption.absorbingContribution,
      GameTheory.RecursiveAbsorption.absorptionMass, Math.Probability.expect_eq_sum,
      stationaryLaw, ofVector_toReal, AbsorbingGameData.canonicalData,
      example1Data, example1FirstStrategy, example1Strategy, Fin.sum_univ_two]
  rw [hvalue, hpayoff] at hpure
  linarith

theorem example1_halfFirst_payoff (who : Bool) :
    canonicalPayoff example1Data none
      (canonicalStationaryProfile example1Data example1HalfStrategy example1FirstStrategy) who =
        Bool.rec 1 (-1) who := by
  cases who <;> rw [lemma2_2_canonical] <;>
    norm_num [GameTheory.RecursiveAbsorption.absorbingContribution,
      GameTheory.RecursiveAbsorption.absorptionMass, Math.Probability.expect_eq_sum,
      stationaryLaw, ofVector_toReal, AbsorbingGameData.canonicalData,
      example1Data, example1HalfStrategy, example1FirstStrategy, example1Strategy,
      Fin.sum_univ_two]

/-- An exact stationary equilibrium of the literal Example 1 game at every initial state. -/
theorem example1_halfFirst_equilibrium :
    ∀ initial, (canonicalGame example1Data).IsεAsymptoticNash
      (canonicalPayoff example1Data initial) 0
      (canonicalStationaryProfile example1Data example1HalfStrategy example1FirstStrategy) := by
  intro initial who deviation
  cases initial with
  | none =>
      cases who with
      | false =>
          have hrow : ∀ i : Fin 2,
              GameTheory.RecursiveAbsorption.stationaryPayoff example1Data.canonicalData
                (PMF.pure i) (stationaryLaw example1FirstStrategy) false ≤ 1 := by
            intro i
            have hvalue := (pureStationaryPayoff1_eq_canonical
              example1Data example1FirstStrategy i).trans
                (GameTheory.RecursiveAbsorption.liminfPayoff_stationary_none
                  example1Data.canonicalData (PMF.pure i)
                  (stationaryLaw example1FirstStrategy) false)
            rw [← hvalue]
            fin_cases i <;>
              norm_num [pureStationaryPayoff1, Math.Probability.RatioProperPair.rowRatio,
                AbsorbingGameData.payoffNumerator1, AbsorbingGameData.absorptionCoefficients,
                example1Data, example1FirstStrategy, example1Strategy, Fin.sum_univ_two]
          calc
            _ ≤ 1 := GameTheory.RecursiveAbsorption.behavioral_rowPayoff_le_of_pure_cap
              example1Data.canonicalData (stationaryLaw example1HalfStrategy)
              (stationaryLaw example1FirstStrategy) 1 hrow deviation
            _ = _ := by rw [example1_halfFirst_payoff]; norm_num
      | true =>
          have hcolumn : ∀ j : Fin 2,
              GameTheory.RecursiveAbsorption.stationaryPayoff example1Data.canonicalData
                (stationaryLaw example1HalfStrategy) (PMF.pure j) true ≤ -1 := by
            intro j
            have hvalue := (pureStationaryPayoff2_eq_canonical
              example1Data example1HalfStrategy j).trans
                (GameTheory.RecursiveAbsorption.liminfPayoff_stationary_none
                  example1Data.canonicalData (stationaryLaw example1HalfStrategy)
                  (PMF.pure j) true)
            rw [← hvalue]
            fin_cases j <;>
              norm_num [pureStationaryPayoff2, Math.Probability.RatioProperPair.columnRatio,
                AbsorbingGameData.payoffNumerator2, AbsorbingGameData.absorptionCoefficients,
                example1Data, example1HalfStrategy, Fin.sum_univ_two]
          calc
            _ ≤ -1 := GameTheory.RecursiveAbsorption.behavioral_columnPayoff_le_of_pure_cap
              example1Data.canonicalData (stationaryLaw example1HalfStrategy)
              (stationaryLaw example1FirstStrategy) (-1) hcolumn deviation
            _ = _ := by rw [example1_halfFirst_payoff]; norm_num
  | some pair =>
      calc
        _ ≤ example1Data.canonicalData.reward pair.1 pair.2 who :=
          (GameTheory.RecursiveAbsorption.liminfPayoff_some example1Data.canonicalData
            (Function.update (canonicalStationaryProfile example1Data
              example1HalfStrategy example1FirstStrategy) who deviation) pair who).le
        _ = _ := by
          simpa only [add_zero] using
            (GameTheory.RecursiveAbsorption.liminfPayoff_some example1Data.canonicalData
            (canonicalStationaryProfile example1Data example1HalfStrategy
              example1FirstStrategy) pair who).symm

/-- Theorem 2.4: every finite two-player absorption table has a proper strategy pair. -/
theorem theorem2_4 [Nonempty I] [Nonempty J] (G : AbsorbingGameData I J) :
    ∃ (x : StationaryStrategy I) (y : StationaryStrategy J), IsProperPair G x y := by
  obtain ⟨x, y, hxy⟩ := Math.Probability.RatioProperPair.exists_properPair
    G.absorptionCoefficients G.payoffNumerator1 G.payoffNumerator2
    (fun i j => (G.absorptionProbability i j).2.1)
  exact ⟨⟨x, hxy.1⟩, ⟨y, hxy.2.1⟩, hxy⟩

/-! ## Section 3: canonical stationary approximate equilibria

This statement concerns the actual game defined above. The production proof
constructs proper pairs internally, derives the absorbing and recurrent limit
cases, and caps all behavioral deviations. The original absorbing-stage-game
reduction remains a separate obligation.
-/

/-- Theorem 3.1 for the canonical model, simultaneously at every initial state. -/
theorem theorem3_1_canonical {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (G : AbsorbingGameData A B) {ε : ℝ} (hε : 0 < ε) :
    ∃ (x : StationaryStrategy A) (y : StationaryStrategy B), ∀ initial,
      (canonicalGame G).IsεAsymptoticNash (canonicalPayoff G initial) ε
        (canonicalStationaryProfile G x y) := by
  obtain ⟨x, y, hxy⟩ :=
    GameTheory.RecursiveAbsorption.exists_stationary_liminfApproximateEquilibrium
      G.canonicalData hε
  refine ⟨⟨toVector x, toVector_mem_stdSimplex x⟩,
    ⟨toVector y, toVector_mem_stdSimplex y⟩, ?_⟩
  simpa only [canonicalStationaryProfile, stationaryLaw, ofVector_toVector] using hxy

/-! Lemma 3.2 uses arbitrary stationary sequences. Its absorbing non-best-reply
set varies along the sequence; the conditional ratio is zero off that set.
Only the opponent's strategy is required to converge. These statements concern
the canonical model, not a presumed reduction of the original absorbing stages.
-/

/-- The raw row ratio on precisely the current absorbing non-best-reply set. -/
abbrev badReplyProbabilityRatio1 {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (x : StationaryStrategy A) (y : StationaryStrategy B)
    (anchor i : A) :=
  GameTheory.RecursiveAbsorption.rowBadReplyProbabilityRatio G.canonicalData
    (stationaryLaw x) (stationaryLaw y) anchor i

/-- The corresponding conditional column ratio. -/
abbrev badReplyProbabilityRatio2 {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (x : StationaryStrategy A) (y : StationaryStrategy B)
    (anchor j : B) :=
  GameTheory.RecursiveAbsorption.columnBadReplyProbabilityRatio G.canonicalData
    (stationaryLaw x) (stationaryLaw y) anchor j

/-- Lemma 3.2: the actual canonical row payoff is eventually near its best reply. -/
theorem lemma3_2_canonical {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (xs : ℕ → StationaryStrategy A)
    (ys : ℕ → StationaryStrategy B) (y : StationaryStrategy B) (anchor : A)
    (hy : Tendsto (fun n => (ys n).1) atTop (𝓝 y.1))
    (hsupported : ∀ n, anchor ∈ stationaryCarrier (xs n))
    (hbest : ∀ n, anchor ∈ pureBestReplies1 G (ys n))
    (hhazard : anchor ∈ absorbingPureRows G y)
    (hbad : ∀ i, Tendsto
      (fun n => badReplyProbabilityRatio1 G (xs n) (ys n) anchor i) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, canonicalPayoff G none (canonicalStationaryProfile G (xs n) (ys n))
      false ≥ pureStationaryPayoff1 G (ys n) anchor - ε := by
  have hy' : Tendsto (fun n => toVector (stationaryLaw (ys n))) atTop
      (𝓝 (toVector (stationaryLaw y))) := by
    simpa only [stationaryLaw, toVector_ofVector] using hy
  have hs : ∀ n, 0 < ((stationaryLaw (xs n)) anchor).toReal := by
    intro n
    simpa only [stationaryLaw, ofVector_toReal, stationaryCarrier, Set.mem_ofPred_eq] using
      hsupported n
  have hfloor :=
    GameTheory.RecursiveAbsorption.eventually_rowPayoff_ge_bestReply_of_bad_ratio_tendsto
      G.canonicalData (fun n => stationaryLaw (xs n)) (fun n => stationaryLaw (ys n))
      (stationaryLaw y) anchor hy' hs hbest hhazard hbad hε
  simpa only [canonicalPayoff, canonicalStationaryProfile,
    pureStationaryPayoff1_eq_canonical] using hfloor

/-- The same canonical Lemma 3.2 estimate for the column player. -/
theorem lemma3_2_canonical_column {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (xs : ℕ → StationaryStrategy A)
    (ys : ℕ → StationaryStrategy B) (x : StationaryStrategy A) (anchor : B)
    (hx : Tendsto (fun n => (xs n).1) atTop (𝓝 x.1))
    (hsupported : ∀ n, anchor ∈ stationaryCarrier (ys n))
    (hbest : ∀ n, anchor ∈ pureBestReplies2 G (xs n))
    (hhazard : anchor ∈ absorbingPureColumns G x)
    (hbad : ∀ j, Tendsto
      (fun n => badReplyProbabilityRatio2 G (xs n) (ys n) anchor j) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, canonicalPayoff G none (canonicalStationaryProfile G (xs n) (ys n))
      true ≥ pureStationaryPayoff2 G (xs n) anchor - ε := by
  have hx' : Tendsto (fun n => toVector (stationaryLaw (xs n))) atTop
      (𝓝 (toVector (stationaryLaw x))) := by
    simpa only [stationaryLaw, toVector_ofVector] using hx
  have hs : ∀ n, 0 < ((stationaryLaw (ys n)) anchor).toReal := by
    intro n
    simpa only [stationaryLaw, ofVector_toReal, stationaryCarrier, Set.mem_ofPred_eq] using
      hsupported n
  have hfloor :=
    GameTheory.RecursiveAbsorption.eventually_columnPayoff_ge_bestReply_of_bad_ratio_tendsto
      G.canonicalData (fun n => stationaryLaw (xs n)) (fun n => stationaryLaw (ys n))
      (stationaryLaw x) anchor hx' hs hbest hhazard hbad hε
  simpa only [canonicalPayoff, canonicalStationaryProfile,
    pureStationaryPayoff2_eq_canonical] using hfloor

/-! ### Example 2

The first entry is live with payoff zero; all other entries absorb with
probability one. The two printed families differ in their row weights and
their limiting column. Their properness and equilibrium conclusions require
separate arguments; the table and pure values alone do not establish them.
-/

/-- The literal three-row, two-column table in Example 2. -/
def example2Data : AbsorbingGameData (Fin 3) (Fin 2) where
  absorptionProbability := fun i j =>
    if i = 0 ∧ j = 0 then ⟨0, by constructor <;> norm_num⟩
    else ⟨1, by constructor <;> norm_num⟩
  reward1 := !![0, 4; 3, 1; 1, 3]
  reward2 := !![0, -3; -2, -4; -4, -2]

private def example2RowStrategy (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (recurrent : Bool) : StationaryStrategy (Fin 3) :=
  ⟨if recurrent then ![1 - δ ^ 2 - δ ^ 4, δ ^ 2, δ ^ 4]
    else ![1 - δ ^ 2 - δ ^ 4, δ ^ 4, δ ^ 2], by
    have hsq : δ ^ 2 ≤ 1 / 4 := by
      nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hδhalf)]
    have hfour : δ ^ 4 ≤ 1 / 16 := by
      nlinarith [mul_nonneg (show 0 ≤ 1 / 4 + δ ^ 2 by positivity)
        (show 0 ≤ 1 / 4 - δ ^ 2 by linarith)]
    rw [GameTheory.Math.Probability.mem_simplexWeights]
    constructor
    · intro i
      cases recurrent <;> fin_cases i <;> norm_num [abs_of_nonneg hδ0] <;>
        nlinarith [sq_nonneg δ, pow_nonneg hδ0 4]
    · cases recurrent <;> norm_num [Fin.sum_univ_three]
      ring⟩

/-- The row strategy whose printed proper limit is absorbing. -/
abbrev example2AbsorbingRowStrategy (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :=
  example2RowStrategy δ hδ0 hδhalf false

/-- The row strategy whose printed proper limit is recurrent. -/
abbrev example2RecurrentRowStrategy (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :=
  example2RowStrategy δ hδ0 hδhalf true

/-- The column strategy in the absorbing-limit family. -/
def example2AbsorbingColumnStrategy (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    StationaryStrategy (Fin 2) :=
  ⟨![δ ^ 2, 1 - δ ^ 2], by
    have hsq : δ ^ 2 ≤ 1 / 4 := by
      nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hδhalf)]
    rw [GameTheory.Math.Probability.mem_simplexWeights]
    constructor
    · intro j
      fin_cases j <;> norm_num [abs_of_nonneg hδ0] <;> nlinarith [sq_nonneg δ]
    · norm_num [Fin.sum_univ_two]⟩

/-- The recurrent family's column strategy is the same vector as in Example 1. -/
abbrev example2RecurrentColumnStrategy := example1Strategy

theorem example2_absorbing_pureRowPayoff (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (i : Fin 3) :
    pureStationaryPayoff1 example2Data (example2AbsorbingColumnStrategy δ hδ.le hδhalf) i =
      ![4, 1 + 2 * δ ^ 2, 3 - 2 * δ ^ 2] i := by
  have hsq : δ ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδhalf)]
  have hden : 0 < 1 - δ ^ 2 := by linarith
  fin_cases i <;>
    norm_num [pureStationaryPayoff1, Math.Probability.RatioProperPair.rowRatio,
      AbsorbingGameData.payoffNumerator1, AbsorbingGameData.absorptionCoefficients,
      example2Data, example2AbsorbingColumnStrategy, Fin.sum_univ_two] <;>
    field_simp [hden.ne'] <;> ring

theorem example2_absorbing_pureColumnPayoff (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (j : Fin 2) :
    pureStationaryPayoff2 example2Data (example2AbsorbingRowStrategy δ hδ.le hδhalf) j =
      ![-(4 + 2 * δ ^ 2) / (1 + δ ^ 2), -3 + δ ^ 2 - δ ^ 4] j := by
  have hden : 0 < δ ^ 4 + δ ^ 2 := by positivity
  have hone : 0 < 1 + δ ^ 2 := by positivity
  fin_cases j <;>
    norm_num [pureStationaryPayoff2, Math.Probability.RatioProperPair.columnRatio,
      AbsorbingGameData.payoffNumerator2, AbsorbingGameData.absorptionCoefficients,
      example2Data, example2AbsorbingRowStrategy, example2RowStrategy,
      Fin.sum_univ_three] <;> field_simp [hden.ne', hone.ne'] <;> ring

theorem example2_recurrent_pureRowPayoff (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (i : Fin 3) :
    pureStationaryPayoff1 example2Data (example2RecurrentColumnStrategy δ hδ.le hδhalf) i =
      ![4, 3 - 2 * δ ^ 2, 1 + 2 * δ ^ 2] i := by
  fin_cases i <;>
    norm_num [pureStationaryPayoff1, Math.Probability.RatioProperPair.rowRatio,
      AbsorbingGameData.payoffNumerator1, AbsorbingGameData.absorptionCoefficients,
      example2Data, example2RecurrentColumnStrategy, example1Strategy,
      Fin.sum_univ_two] <;> field_simp [hδ.ne'] <;> ring

theorem example2_recurrent_pureColumnPayoff (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (j : Fin 2) :
    pureStationaryPayoff2 example2Data (example2RecurrentRowStrategy δ hδ.le hδhalf) j =
      ![-(2 + 4 * δ ^ 2) / (1 + δ ^ 2), -3 - δ ^ 2 + δ ^ 4] j := by
  have hden : 0 < δ ^ 2 + δ ^ 4 := by positivity
  have hone : 0 < 1 + δ ^ 2 := by positivity
  fin_cases j <;>
    norm_num [pureStationaryPayoff2, Math.Probability.RatioProperPair.columnRatio,
      AbsorbingGameData.payoffNumerator2, AbsorbingGameData.absorptionCoefficients,
      example2Data, example2RecurrentRowStrategy, example2RowStrategy,
      Fin.sum_univ_three] <;> field_simp [hden.ne', hone.ne'] <;> ring

private theorem example2_weightBounds (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    0 < 1 - δ ^ 2 - δ ^ 4 ∧
      δ ^ 2 ≤ δ * (1 - δ ^ 2 - δ ^ 4) ∧
      δ ^ 4 ≤ δ * δ ^ 2 ∧ δ ^ 4 ≤ δ * (1 - δ ^ 2 - δ ^ 4) := by
  have hsq : δ ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδhalf)]
  have hfour : δ ^ 4 ≤ 1 / 16 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 4 + δ ^ 2 by positivity)
      (show 0 ≤ 1 / 4 - δ ^ 2 by linarith)]
  have hfirst : δ ≤ 1 - δ ^ 2 - δ ^ 4 := by linarith
  have hlarge := mul_le_mul_of_nonneg_left hfirst hδ.le
  have hminor : δ ^ 2 ≤ δ := by
    nlinarith [mul_nonneg hδ.le (show 0 ≤ 1 - δ by linarith)]
  have hmiddle := mul_le_mul_of_nonneg_left hminor (sq_nonneg δ)
  have htail := mul_le_mul_of_nonneg_left
    (show δ ^ 2 ≤ 1 - δ ^ 2 - δ ^ 4 by linarith) hδ.le
  refine ⟨by linarith, ?_, ?_, ?_⟩ <;> nlinarith

/-- The columns in the absorbing family strictly prefer their second action. -/
theorem example2_absorbing_column_ranking (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    pureStationaryPayoff2 example2Data (example2AbsorbingRowStrategy δ hδ.le hδhalf) 0 <
      pureStationaryPayoff2 example2Data (example2AbsorbingRowStrategy δ hδ.le hδhalf) 1 := by
  rw [example2_absorbing_pureColumnPayoff δ hδ hδhalf,
    example2_absorbing_pureColumnPayoff δ hδ hδhalf]
  norm_num
  have hsq : δ ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδhalf)]
  have hfactor := mul_pos (show 0 < 1 - δ ^ 2 by linarith)
    (show 0 < 1 + δ ^ 2 + δ ^ 4 by positivity)
  apply (div_lt_iff₀ (show 0 < 1 + δ ^ 2 by positivity)).mpr
  nlinarith

/-- The columns in the recurrent family strictly prefer their first action. -/
theorem example2_recurrent_column_ranking (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    pureStationaryPayoff2 example2Data (example2RecurrentRowStrategy δ hδ.le hδhalf) 1 <
      pureStationaryPayoff2 example2Data (example2RecurrentRowStrategy δ hδ.le hδhalf) 0 := by
  rw [example2_recurrent_pureColumnPayoff δ hδ hδhalf,
    example2_recurrent_pureColumnPayoff δ hδ hδhalf]
  norm_num
  have hsq : δ ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδhalf)]
  have hfactor := mul_pos (show 0 < 1 - δ ^ 2 by linarith)
    (show 0 < 1 + δ ^ 2 + δ ^ 4 by positivity)
  apply (lt_div_iff₀ (show 0 < 1 + δ ^ 2 by positivity)).mpr
  nlinarith

/-- The first printed Example 2 family is delta-proper on a concrete small-delta interval. -/
theorem example2_absorbing_deltaProper (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    IsDeltaProperPair example2Data δ (example2AbsorbingRowStrategy δ hδ.le hδhalf)
      (example2AbsorbingColumnStrategy δ hδ.le hδhalf) := by
  have hweights := example2_weightBounds δ hδ hδhalf
  have hsq : δ ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδhalf)]
  have hcolumn := example2_absorbing_column_ranking δ hδ hδhalf
  rw [example2_absorbing_pureColumnPayoff δ hδ hδhalf,
    example2_absorbing_pureColumnPayoff δ hδ hδhalf] at hcolumn
  norm_num at hcolumn
  have hcolumnWeight : δ ^ 2 ≤ δ * (1 - δ ^ 2) := by
    nlinarith [mul_nonneg hδ.le (show 0 ≤ 1 - δ ^ 2 - δ by linarith)]
  refine ⟨hδ, by linarith, (example2AbsorbingRowStrategy δ hδ.le hδhalf).2,
    (example2AbsorbingColumnStrategy δ hδ.le hδhalf).2, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [example2AbsorbingRowStrategy, example2RowStrategy] <;>
      nlinarith [hweights.1, sq_pos_of_pos hδ, pow_pos hδ 4]
  · intro j
    fin_cases j <;> norm_num [example2AbsorbingColumnStrategy, abs_of_pos hδ] <;>
      nlinarith [sq_pos_of_pos hδ]
  · intro i e h
    change pureStationaryPayoff1 example2Data
      (example2AbsorbingColumnStrategy δ hδ.le hδhalf) e <
        pureStationaryPayoff1 example2Data
          (example2AbsorbingColumnStrategy δ hδ.le hδhalf) i at h
    rw [example2_absorbing_pureRowPayoff δ hδ hδhalf,
      example2_absorbing_pureRowPayoff δ hδ hδhalf] at h
    fin_cases i <;> fin_cases e <;> norm_num at h
    all_goals
      norm_num [example2AbsorbingRowStrategy, example2RowStrategy]
      nlinarith [hweights.2.1, hweights.2.2.1, hweights.2.2.2]
  · intro j f h
    change pureStationaryPayoff2 example2Data
      (example2AbsorbingRowStrategy δ hδ.le hδhalf) f <
        pureStationaryPayoff2 example2Data
          (example2AbsorbingRowStrategy δ hδ.le hδhalf) j at h
    rw [example2_absorbing_pureColumnPayoff δ hδ hδhalf,
      example2_absorbing_pureColumnPayoff δ hδ hδhalf] at h
    fin_cases j <;> fin_cases f <;> norm_num at h
    all_goals
      norm_num [example2AbsorbingColumnStrategy]
      nlinarith

/-- The second printed family is delta-proper; its column limit is the first action. -/
theorem example2_recurrent_deltaProper (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    IsDeltaProperPair example2Data δ (example2RecurrentRowStrategy δ hδ.le hδhalf)
      (example2RecurrentColumnStrategy δ hδ.le hδhalf) := by
  have hweights := example2_weightBounds δ hδ hδhalf
  have hsq : δ ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδhalf)]
  have hcolumn := example2_recurrent_column_ranking δ hδ hδhalf
  rw [example2_recurrent_pureColumnPayoff δ hδ hδhalf,
    example2_recurrent_pureColumnPayoff δ hδ hδhalf] at hcolumn
  norm_num at hcolumn
  have hcolumnWeight : δ ^ 2 ≤ δ * (1 - δ ^ 2) := by
    nlinarith [mul_nonneg hδ.le (show 0 ≤ 1 - δ ^ 2 - δ by linarith)]
  refine ⟨hδ, by linarith, (example2RecurrentRowStrategy δ hδ.le hδhalf).2,
    (example2RecurrentColumnStrategy δ hδ.le hδhalf).2, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [example2RecurrentRowStrategy, example2RowStrategy] <;>
      nlinarith [hweights.1, sq_pos_of_pos hδ, pow_pos hδ 4]
  · intro j
    fin_cases j <;> norm_num [example2RecurrentColumnStrategy, example1Strategy,
      abs_of_pos hδ] <;>
      nlinarith [sq_pos_of_pos hδ]
  · intro i e h
    change pureStationaryPayoff1 example2Data
      (example2RecurrentColumnStrategy δ hδ.le hδhalf) e <
        pureStationaryPayoff1 example2Data
          (example2RecurrentColumnStrategy δ hδ.le hδhalf) i at h
    rw [example2_recurrent_pureRowPayoff δ hδ hδhalf,
      example2_recurrent_pureRowPayoff δ hδ hδhalf] at h
    fin_cases i <;> fin_cases e <;> norm_num at h
    all_goals
      norm_num [example2RecurrentRowStrategy, example2RowStrategy]
      nlinarith [hweights.2.1, hweights.2.2.1, hweights.2.2.2]
  · intro j f h
    change pureStationaryPayoff2 example2Data
      (example2RecurrentRowStrategy δ hδ.le hδhalf) f <
        pureStationaryPayoff2 example2Data
          (example2RecurrentRowStrategy δ hδ.le hδhalf) j at h
    rw [example2_recurrent_pureColumnPayoff δ hδ hδhalf,
      example2_recurrent_pureColumnPayoff δ hδ hδhalf] at h
    fin_cases j <;> fin_cases f <;> norm_num at h
    all_goals
      norm_num [example2RecurrentColumnStrategy, example1Strategy]
      nlinarith

/-- The common first-row limit of both printed Example 2 families. -/
def example2FirstRowStrategy : StationaryStrategy (Fin 3) :=
  example2AbsorbingRowStrategy 0 le_rfl (by norm_num)

/-- The second-column limit of the absorbing family. -/
def example2SecondColumnStrategy : StationaryStrategy (Fin 2) :=
  example2AbsorbingColumnStrategy 0 le_rfl (by norm_num)

private theorem tendsto_example2RowStrategy (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hsmall : ∀ n, 0 < δ n ∧ δ n ≤ 1 / 2)
    (recurrent : Bool) :
    Tendsto (fun n => (example2RowStrategy (δ n) (hsmall n).1.le (hsmall n).2 recurrent).1)
      atTop (𝓝 example2FirstRowStrategy.1) := by
  have hfirst : Tendsto (fun n => 1 - δ n ^ 2 - δ n ^ 4) atTop (𝓝 (1 : ℝ)) := by
    simpa using ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (hδ.pow 2)).sub (hδ.pow 4)
  apply tendsto_pi_nhds.mpr
  intro i
  cases recurrent <;> fin_cases i
  · simpa [example2RowStrategy, example2FirstRowStrategy] using hfirst
  · simpa [example2RowStrategy, example2FirstRowStrategy] using hδ.pow 4
  · simpa [example2RowStrategy, example2FirstRowStrategy] using hδ.pow 2
  · simpa [example2RowStrategy, example2FirstRowStrategy] using hfirst
  · simpa [example2RowStrategy, example2FirstRowStrategy] using hδ.pow 2
  · simpa [example2RowStrategy, example2FirstRowStrategy] using hδ.pow 4

private theorem tendsto_example2AbsorbingColumnStrategy (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hsmall : ∀ n, 0 < δ n ∧ δ n ≤ 1 / 2) :
    Tendsto (fun n => (example2AbsorbingColumnStrategy
      (δ n) (hsmall n).1.le (hsmall n).2).1) atTop (𝓝 example2SecondColumnStrategy.1) := by
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases j
  · simpa [example2AbsorbingColumnStrategy, example2SecondColumnStrategy] using hδ.pow 2
  · simpa [example2AbsorbingColumnStrategy, example2SecondColumnStrategy] using
      tendsto_const_nhds.sub (hδ.pow 2)

private theorem tendsto_example2RecurrentColumnStrategy (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hsmall : ∀ n, 0 < δ n ∧ δ n ≤ 1 / 2) :
    Tendsto (fun n => (example2RecurrentColumnStrategy
      (δ n) (hsmall n).1.le (hsmall n).2).1) atTop (𝓝 example1FirstStrategy.1) := by
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases j
  · simpa [example2RecurrentColumnStrategy, example1Strategy, example1FirstStrategy] using
      tendsto_const_nhds.sub (hδ.pow 2)
  · simpa [example2RecurrentColumnStrategy, example1Strategy, example1FirstStrategy] using
      hδ.pow 2

/-- The first printed family has the stated absorbing proper limit. -/
theorem example2_absorbing_proper :
    IsProperPair example2Data example2FirstRowStrategy example2SecondColumnStrategy := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_exampleDeltaSequence
  refine ⟨example2FirstRowStrategy.2, example2SecondColumnStrategy.2, δ,
    (fun n => (example2AbsorbingRowStrategy (δ n) (hsmall n).1.le (hsmall n).2).1),
    (fun n => (example2AbsorbingColumnStrategy (δ n) (hsmall n).1.le (hsmall n).2).1),
    hδ, tendsto_example2RowStrategy δ hδ hsmall false,
    tendsto_example2AbsorbingColumnStrategy δ hδ hsmall, ?_⟩
  exact fun n => example2_absorbing_deltaProper (δ n) (hsmall n).1 (hsmall n).2

/-- The second printed family has the stated recurrent proper limit. -/
theorem example2_recurrent_proper :
    IsProperPair example2Data example2FirstRowStrategy example1FirstStrategy := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_exampleDeltaSequence
  refine ⟨example2FirstRowStrategy.2, example1FirstStrategy.2, δ,
    (fun n => (example2RecurrentRowStrategy (δ n) (hsmall n).1.le (hsmall n).2).1),
    (fun n => (example2RecurrentColumnStrategy (δ n) (hsmall n).1.le (hsmall n).2).1),
    hδ, tendsto_example2RowStrategy δ hδ hsmall true,
    tendsto_example2RecurrentColumnStrategy δ hδ hsmall, ?_⟩
  exact fun n => example2_recurrent_deltaProper (δ n) (hsmall n).1 (hsmall n).2

theorem example2_absorbing_limit_absorption :
    canonicalAbsorptionProbability example2Data example2FirstRowStrategy
      example2SecondColumnStrategy = 1 := by
  norm_num [canonicalAbsorptionProbability, GameTheory.RecursiveAbsorption.absorptionMass,
    Math.Probability.expect_eq_sum, stationaryLaw, ofVector_toReal,
    AbsorbingGameData.canonicalData, example2Data, example2FirstRowStrategy,
    example2AbsorbingRowStrategy, example2RowStrategy, example2SecondColumnStrategy,
    example2AbsorbingColumnStrategy, Fin.sum_univ_three, Fin.sum_univ_two]

theorem example2_recurrent_limit_absorption :
    canonicalAbsorptionProbability example2Data example2FirstRowStrategy
      example1FirstStrategy = 0 := by
  norm_num [canonicalAbsorptionProbability, GameTheory.RecursiveAbsorption.absorptionMass,
    Math.Probability.expect_eq_sum, stationaryLaw, ofVector_toReal,
    AbsorbingGameData.canonicalData, example2Data, example2FirstRowStrategy,
    example2AbsorbingRowStrategy, example2RowStrategy, example1FirstStrategy,
    example1Strategy, Fin.sum_univ_three, Fin.sum_univ_two]

theorem example2_absorbing_limit_payoff (who : Bool) :
    canonicalPayoff example2Data none
      (canonicalStationaryProfile example2Data example2FirstRowStrategy
        example2SecondColumnStrategy) who = Bool.rec 4 (-3) who := by
  cases who <;> rw [lemma2_2_canonical] <;>
    norm_num [GameTheory.RecursiveAbsorption.absorbingContribution,
      GameTheory.RecursiveAbsorption.absorptionMass, Math.Probability.expect_eq_sum,
      stationaryLaw, ofVector_toReal, AbsorbingGameData.canonicalData,
      example2Data, example2FirstRowStrategy, example2AbsorbingRowStrategy,
      example2RowStrategy, example2SecondColumnStrategy, example2AbsorbingColumnStrategy,
      Fin.sum_univ_three, Fin.sum_univ_two]

private theorem pureColumnPayoff_le_of_canonicalNash {A B : Type}
    [Fintype A] [Fintype B] (G : AbsorbingGameData A B)
    (x : StationaryStrategy A) (y : StationaryStrategy B) {ε : ℝ}
    (hNash : (canonicalGame G).IsεAsymptoticNash (canonicalPayoff G none) ε
      (canonicalStationaryProfile G x y)) (j : B) :
    pureStationaryPayoff2 G x j ≤
      canonicalPayoff G none (canonicalStationaryProfile G x y) true + ε := by
  have hprofile : Function.update (canonicalStationaryProfile G x y)
      true (fun _ _ => PMF.pure j) =
        GameTheory.RecursiveAbsorption.stationaryProfile G.canonicalData
          (stationaryLaw x) (PMF.pure j) := by
    funext who time history
    cases who <;> simp [canonicalStationaryProfile,
      GameTheory.RecursiveAbsorption.stationaryProfile,
      GameTheory.StochasticGame.stationaryBehaviorProfile,
      GameTheory.RecursiveAbsorption.mixedAction] <;> rfl
  have h := hNash true (fun _ _ => PMF.pure j)
  rw [hprofile] at h
  exact (pureStationaryPayoff2_eq_canonical G x j).le.trans h

/-- The absorbing proper limit fails at errors below three, via an actual column deviation. -/
theorem example2_absorbing_limit_not_smallErrorNash {ε : ℝ} (hε : ε < 3) :
    ¬ (canonicalGame example2Data).IsεAsymptoticNash (canonicalPayoff example2Data none) ε
      (canonicalStationaryProfile example2Data example2FirstRowStrategy
        example2SecondColumnStrategy) := by
  intro hNash
  have hpure := pureColumnPayoff_le_of_canonicalNash example2Data
    example2FirstRowStrategy example2SecondColumnStrategy hNash 0
  have hvalue : pureStationaryPayoff2 example2Data example2FirstRowStrategy 0 = 0 := by
    norm_num [pureStationaryPayoff2, Math.Probability.RatioProperPair.columnRatio,
      AbsorbingGameData.payoffNumerator2, AbsorbingGameData.absorptionCoefficients,
      example2Data, example2FirstRowStrategy, example2AbsorbingRowStrategy,
      example2RowStrategy, Fin.sum_univ_three]
  rw [hvalue, example2_absorbing_limit_payoff] at hpure
  norm_num at hpure
  linarith

/-- The printed absorbing family is eventually Nash at every initial state. -/
theorem example2_absorbing_family_eventually_equilibrium (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hsmall : ∀ n, 0 < δ n ∧ δ n ≤ 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ initial, (canonicalGame example2Data).IsεAsymptoticNash
      (canonicalPayoff example2Data initial) ε
      (canonicalStationaryProfile example2Data
        (example2AbsorbingRowStrategy (δ n) (hsmall n).1.le (hsmall n).2)
        (example2AbsorbingColumnStrategy (δ n) (hsmall n).1.le (hsmall n).2)) := by
  have hx : Tendsto (fun n => toVector (stationaryLaw
      (example2AbsorbingRowStrategy (δ n) (hsmall n).1.le (hsmall n).2))) atTop
      (𝓝 (toVector (stationaryLaw example2FirstRowStrategy))) := by
    simpa only [stationaryLaw, toVector_ofVector] using
      tendsto_example2RowStrategy δ hδ hsmall false
  have hy : Tendsto (fun n => toVector (stationaryLaw
      (example2AbsorbingColumnStrategy (δ n) (hsmall n).1.le (hsmall n).2))) atTop
      (𝓝 (toVector (stationaryLaw example2SecondColumnStrategy))) := by
    simpa only [stationaryLaw, toVector_ofVector] using
      tendsto_example2AbsorbingColumnStrategy δ hδ hsmall
  have hpairs : ∀ n, GameTheory.RecursiveAbsorption.IsDeltaProperPair
      example2Data.canonicalData (δ n)
      (stationaryLaw (example2AbsorbingRowStrategy (δ n) (hsmall n).1.le (hsmall n).2))
      (stationaryLaw (example2AbsorbingColumnStrategy (δ n) (hsmall n).1.le (hsmall n).2)) := by
    intro n
    change Math.Probability.RatioProperPair.IsDeltaProperPair
      example2Data.absorptionCoefficients example2Data.payoffNumerator1
      example2Data.payoffNumerator2 (δ n)
      (toVector (stationaryLaw
        (example2AbsorbingRowStrategy (δ n) (hsmall n).1.le (hsmall n).2)))
      (toVector (stationaryLaw
        (example2AbsorbingColumnStrategy (δ n) (hsmall n).1.le (hsmall n).2)))
    simpa only [stationaryLaw, toVector_ofVector, IsDeltaProperPair] using
      example2_absorbing_deltaProper (δ n) (hsmall n).1 (hsmall n).2
  have hpositive : 0 < GameTheory.RecursiveAbsorption.absorptionMass
      example2Data.canonicalData (stationaryLaw example2FirstRowStrategy)
        (stationaryLaw example2SecondColumnStrategy) := by
    change 0 < canonicalAbsorptionProbability example2Data example2FirstRowStrategy
      example2SecondColumnStrategy
    rw [example2_absorbing_limit_absorption]
    norm_num
  exact GameTheory.RecursiveAbsorption.eventually_isAsymptoticNash_of_absorbing_proper_limit
    example2Data.canonicalData δ
    (fun n => stationaryLaw (example2AbsorbingRowStrategy
      (δ n) (hsmall n).1.le (hsmall n).2))
    (fun n => stationaryLaw (example2AbsorbingColumnStrategy
      (δ n) (hsmall n).1.le (hsmall n).2))
    (stationaryLaw example2FirstRowStrategy) (stationaryLaw example2SecondColumnStrategy)
    hδ hx hy hpairs hpositive hε

private theorem stationaryLaw_example1FirstStrategy :
    stationaryLaw example1FirstStrategy = PMF.pure (0 : Fin 2) := by
  apply toVector_injective
  simp only [stationaryLaw, toVector_ofVector]
  funext j
  fin_cases j <;> norm_num [example1FirstStrategy, example1Strategy, toVector, PMF.pure_apply]

private theorem example2_firstColumn_pureRowPayoff (i : Fin 3) :
    pureStationaryPayoff1 example2Data example1FirstStrategy i = ![0, 3, 1] i := by
  fin_cases i <;>
    norm_num [pureStationaryPayoff1, Math.Probability.RatioProperPair.rowRatio,
      AbsorbingGameData.payoffNumerator1, AbsorbingGameData.absorptionCoefficients,
      example2Data, example1FirstStrategy, example1Strategy, Fin.sum_univ_two]

private theorem example2_firstColumn_bestReply_iff (i : Fin 3) :
    i ∈ pureBestReplies1 example2Data example1FirstStrategy ↔ i = 1 := by
  change GameTheory.RecursiveAbsorption.IsRowBestReply example2Data.canonicalData
    (stationaryLaw example1FirstStrategy) i ↔ i = 1
  rw [GameTheory.RecursiveAbsorption.isRowBestReply_iff_pure_max]
  have hvalue : ∀ e, pureStationaryPayoff1 example2Data example1FirstStrategy e =
      GameTheory.RecursiveAbsorption.stationaryPayoff example2Data.canonicalData
        (PMF.pure e) (stationaryLaw example1FirstStrategy) false := fun e =>
    (pureStationaryPayoff1_eq_canonical example2Data example1FirstStrategy e).trans
      (GameTheory.RecursiveAbsorption.liminfPayoff_stationary_none
        example2Data.canonicalData (PMF.pure e) (stationaryLaw example1FirstStrategy) false)
  simp_rw [← hvalue, example2_firstColumn_pureRowPayoff]
  fin_cases i <;> norm_num [Fin.forall_fin_succ]

private theorem example2_firstColumn_pureRowAbsorption (i : Fin 3) :
    GameTheory.RecursiveAbsorption.absorptionMass example2Data.canonicalData
      (PMF.pure i) (stationaryLaw example1FirstStrategy) = if i = 0 then 0 else 1 := by
  rw [stationaryLaw_example1FirstStrategy]
  simp only [GameTheory.RecursiveAbsorption.absorptionMass, Math.Probability.expect_pure]
  fin_cases i <;> norm_num [AbsorbingGameData.canonicalData, example2Data]

private theorem example2_recurrent_badReplyRatio (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) (i : Fin 3) :
    badReplyProbabilityRatio1 example2Data
      (example2RecurrentRowStrategy δ hδ.le hδhalf) example1FirstStrategy 1 i =
        ![0, 0, δ ^ 2] i := by
  have hbest : GameTheory.RecursiveAbsorption.IsRowBestReply example2Data.canonicalData
      (stationaryLaw example1FirstStrategy) i ↔ i = 1 :=
    example2_firstColumn_bestReply_iff i
  unfold badReplyProbabilityRatio1 GameTheory.RecursiveAbsorption.rowBadReplyProbabilityRatio
  rw [example2_firstColumn_pureRowAbsorption]
  simp only [hbest]
  fin_cases i <;>
    norm_num [stationaryLaw, ofVector_toReal, example2RecurrentRowStrategy, example2RowStrategy]
  simp only [ENNReal.toReal_ofReal (pow_nonneg hδ.le 4),
    ENNReal.toReal_ofReal (sq_nonneg δ)]
  field_simp [hδ.ne']

/-- The recurrent rows against the fixed limiting first column are eventually Nash.
The same profile caps all behavioral deviations at every initial state. -/
theorem example2_recurrent_family_eventually_equilibrium (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hsmall : ∀ n, 0 < δ n ∧ δ n ≤ 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ initial, (canonicalGame example2Data).IsεAsymptoticNash
      (canonicalPayoff example2Data initial) ε
      (canonicalStationaryProfile example2Data
        (example2RecurrentRowStrategy (δ n) (hsmall n).1.le (hsmall n).2)
        example1FirstStrategy) := by
  let xs : ℕ → StationaryStrategy (Fin 3) :=
    fun n => example2RecurrentRowStrategy (δ n) (hsmall n).1.le (hsmall n).2
  have hsupported : ∀ n, (1 : Fin 3) ∈ stationaryCarrier (xs n) := by
    intro n
    change 0 < (xs n).1 1
    simpa [xs, example2RecurrentRowStrategy, example2RowStrategy] using
      sq_pos_of_pos (hsmall n).1
  have hbest : ∀ _ : ℕ, (1 : Fin 3) ∈ pureBestReplies1 example2Data example1FirstStrategy :=
    fun _ => (example2_firstColumn_bestReply_iff 1).mpr rfl
  have hhazard : (1 : Fin 3) ∈ absorbingPureRows example2Data example1FirstStrategy := by
    change 0 < GameTheory.RecursiveAbsorption.absorptionMass example2Data.canonicalData
      (PMF.pure (1 : Fin 3)) (stationaryLaw example1FirstStrategy)
    rw [example2_firstColumn_pureRowAbsorption]
    norm_num
  have hbad : ∀ i, Tendsto (fun n => badReplyProbabilityRatio1 example2Data
      (xs n) example1FirstStrategy 1 i) atTop (𝓝 0) := by
    intro i
    have hratio : ∀ n, badReplyProbabilityRatio1 example2Data (xs n)
        example1FirstStrategy 1 i = ![0, 0, δ n ^ 2] i := fun n =>
      example2_recurrent_badReplyRatio (δ n) (hsmall n).1 (hsmall n).2 i
    simp_rw [hratio]
    fin_cases i
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
    · simpa using hδ.pow 2
  have hfloor := lemma3_2_canonical example2Data xs (fun _ => example1FirstStrategy)
    example1FirstStrategy 1 tendsto_const_nhds hsupported hbest hhazard hbad hε
  filter_upwards [hfloor] with n hn
  apply GameTheory.RecursiveAbsorption.isAsymptoticNash_of_pure_gaps
    example2Data.canonicalData (stationaryLaw (xs n)) (stationaryLaw example1FirstStrategy) hε.le
  · intro i
    have hvalue := (pureStationaryPayoff1_eq_canonical
      example2Data example1FirstStrategy i).trans
        (GameTheory.RecursiveAbsorption.liminfPayoff_stationary_none
          example2Data.canonicalData (PMF.pure i) (stationaryLaw example1FirstStrategy) false)
    rw [← hvalue]
    have hmixed := GameTheory.RecursiveAbsorption.liminfPayoff_stationary_none
      example2Data.canonicalData (stationaryLaw (xs n)) (stationaryLaw example1FirstStrategy) false
    rw [← hmixed]
    change pureStationaryPayoff1 example2Data example1FirstStrategy i ≤
      canonicalPayoff example2Data none
        (canonicalStationaryProfile example2Data (xs n) example1FirstStrategy) false + ε
    rw [example2_firstColumn_pureRowPayoff] at hn ⊢
    fin_cases i <;> norm_num at hn ⊢ <;> linarith
  · intro j
    have hvalue := (pureStationaryPayoff2_eq_canonical example2Data (xs n) j).trans
      (GameTheory.RecursiveAbsorption.liminfPayoff_stationary_none
        example2Data.canonicalData (stationaryLaw (xs n)) (PMF.pure j) true)
    rw [← hvalue, stationaryLaw_example1FirstStrategy]
    have hzero := (pureStationaryPayoff2_eq_canonical example2Data (xs n) 0).trans
      (GameTheory.RecursiveAbsorption.liminfPayoff_stationary_none
        example2Data.canonicalData (stationaryLaw (xs n)) (PMF.pure 0) true)
    rw [← hzero]
    have hrank := example2_recurrent_column_ranking (δ n) (hsmall n).1 (hsmall n).2
    change pureStationaryPayoff2 example2Data (xs n) 1 <
      pureStationaryPayoff2 example2Data (xs n) 0 at hrank
    fin_cases j
    · exact le_add_of_nonneg_right hε.le
    · change pureStationaryPayoff2 example2Data (xs n) 1 ≤
        pureStationaryPayoff2 example2Data (xs n) 0 + ε
      exact hrank.le.trans (le_add_of_nonneg_right hε.le)

private theorem exists_small_positive_parameter
    (P : {δ : ℝ // 0 < δ ∧ δ ≤ 1 / 2} → Prop)
    (hP : ∀ ds : ℕ → {δ : ℝ // 0 < δ ∧ δ ≤ 1 / 2},
      Tendsto (fun n => (ds n).1) atTop (𝓝 0) → ∀ᶠ n in atTop, P (ds n)) :
    ∃ η : {δ : ℝ // 0 < δ ∧ δ ≤ 1 / 2},
      ∀ d : {δ : ℝ // 0 < δ ∧ δ ≤ 1 / 2}, d.1 ≤ η.1 → P d := by
  have hevent : ∀ᶠ d : {δ : ℝ // 0 < δ ∧ δ ≤ 1 / 2} in
      Filter.comap Subtype.val (𝓝 (0 : ℝ)), P d := by
    apply Filter.eventually_iff_seq_eventually.mpr
    intro ds hds
    exact hP ds (Filter.tendsto_comap_iff.mp hds)
  have hnhds := Filter.eventually_comap.mp hevent
  obtain ⟨l, u, ⟨hl, hu⟩, hinterval⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
  let η : ℝ := min (u / 2) (1 / 2)
  have hηpos : 0 < η := lt_min (div_pos hu (by norm_num)) (by norm_num)
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  refine ⟨⟨η, hηpos, hηhalf⟩, ?_⟩
  intro d hd
  have hdu : d.1 < u := by
    have hηu : η ≤ u / 2 := min_le_left _ _
    linarith
  exact hinterval ⟨hl.trans d.2.1, hdu⟩ d rfl

/-- The absorbing construction works for every sufficiently small positive real delta. -/
theorem example2_absorbing_family_small_parameter {ε : ℝ} (hε : 0 < ε) :
    ∃ (η : ℝ) (hη : 0 < η ∧ η ≤ 1 / 2),
      ∀ (δ : ℝ) (hδ : 0 < δ) (hδη : δ ≤ η), ∀ initial,
        (canonicalGame example2Data).IsεAsymptoticNash
          (canonicalPayoff example2Data initial) ε
          (canonicalStationaryProfile example2Data
            (example2AbsorbingRowStrategy δ hδ.le (hδη.trans hη.2))
            (example2AbsorbingColumnStrategy δ hδ.le (hδη.trans hη.2))) := by
  obtain ⟨η, hη⟩ := exists_small_positive_parameter
    (fun d => ∀ initial, (canonicalGame example2Data).IsεAsymptoticNash
      (canonicalPayoff example2Data initial) ε
      (canonicalStationaryProfile example2Data
        (example2AbsorbingRowStrategy d.1 d.2.1.le d.2.2)
        (example2AbsorbingColumnStrategy d.1 d.2.1.le d.2.2)))
    (fun ds hds => example2_absorbing_family_eventually_equilibrium
      (fun n => (ds n).1) hds (fun n => (ds n).2) hε)
  refine ⟨η.1, η.2, ?_⟩
  intro δ hδ hδη
  exact hη ⟨δ, hδ, hδη.trans η.2.2⟩ hδη

/-- The recurrent rows work for every small positive real delta against the fixed column. -/
theorem example2_recurrent_family_small_parameter {ε : ℝ} (hε : 0 < ε) :
    ∃ (η : ℝ) (hη : 0 < η ∧ η ≤ 1 / 2),
      ∀ (δ : ℝ) (hδ : 0 < δ) (hδη : δ ≤ η), ∀ initial,
        (canonicalGame example2Data).IsεAsymptoticNash
          (canonicalPayoff example2Data initial) ε
          (canonicalStationaryProfile example2Data
            (example2RecurrentRowStrategy δ hδ.le (hδη.trans hη.2)) example1FirstStrategy) := by
  obtain ⟨η, hη⟩ := exists_small_positive_parameter
    (fun d => ∀ initial, (canonicalGame example2Data).IsεAsymptoticNash
      (canonicalPayoff example2Data initial) ε
      (canonicalStationaryProfile example2Data
        (example2RecurrentRowStrategy d.1 d.2.1.le d.2.2) example1FirstStrategy))
    (fun ds hds => example2_recurrent_family_eventually_equilibrium
      (fun n => (ds n).1) hds (fun n => (ds n).2) hε)
  refine ⟨η.1, η.2, ?_⟩
  intro δ hδ hδη
  exact hη ⟨δ, hδ, hδη.trans η.2.2⟩ hδη

/-- The recurrent proper limit has actual zero payoff for both players. -/
theorem example2_recurrent_limit_payoff (who : Bool) :
    canonicalPayoff example2Data none
      (canonicalStationaryProfile example2Data example2FirstRowStrategy
        example1FirstStrategy) who = 0 := by
  rw [lemma2_2_canonical]
  change _ / canonicalAbsorptionProbability example2Data example2FirstRowStrategy
    example1FirstStrategy = 0
  rw [example2_recurrent_limit_absorption, div_zero]

/-! ## Section 4: the Example 1 cross-reference

Section 4 cites Example 1 for nonexistence of exact stationary equilibria.
Example 1 instead has the exact stationary equilibrium proved above, so it
does not witness that nonexistence. This does not refute the nonexistence
phenomenon for recursive absorbing games in general or change the printed
delta-family exclusions.
-/

/-- The specific Example 1 nonexistence assertion suggested by Section 4's reference. -/
def Example1StationaryExclusionClaim : Prop :=
  ¬ ∃ (x : StationaryStrategy (Fin 2)) (y : StationaryStrategy (Fin 2)), ∀ initial,
    (canonicalGame example1Data).IsεAsymptoticNash (canonicalPayoff example1Data initial) 0
      (canonicalStationaryProfile example1Data x y)

/-- The literal Example 1 table has an exact stationary equilibrium. -/
theorem example1_section4_crossReference_refuted : ¬ Example1StationaryExclusionClaim := by
  intro hexclusion
  exact hexclusion ⟨example1HalfStrategy, example1FirstStrategy, example1_halfFirst_equilibrium⟩

/-! ## Section 4: Example 3

The three coordinates choose Top/Bottom, Left/Right and Near/Far respectively.
The Boolean `false` denotes the first action. The all-first-action row is live
with zero stage payoff; every other row absorbs with probability one.

The terminal-payoff presentation from the 1997 formalization is preserved.
The actual all-profile quitting payoff identity also identifies the paper's
expected-pathwise-liminf equilibrium predicate at every initial state.
Unilateral deviations in both predicates are all behavioral strategies, not
just stationary ones. The error and stationary-profile quantifiers are
preserved exactly. This literal Example 3 adapter does not establish the
original two-player paper's general absorbing-stage or legal-history reduction.
-/

abbrev Example3Player := Literature.FleschThuijsmanAndVrieze1997.Player

/-- The literal table of Example 3, including its zero live row. -/
abbrev example3TerminalReward := Literature.FleschThuijsmanAndVrieze1997.terminalReward

/-- The seven absorbing rows in quitter-set form. -/
abbrev example3Reward := GameTheory.CyclicThreePlayerQuitting.AdmissibleCycle.reward

/-- The actual recursive quitting game associated with Example 3. -/
abbrev example3Game := GameTheory.quittingGame example3Reward

abbrev Example3StationaryProfile := Literature.FleschThuijsmanAndVrieze1997.StationaryProfile

/-- The literal stationary behavior profile of the actual Example 3 game. -/
abbrev example3StationaryBehaviorProfile (profile : Example3StationaryProfile) :=
  Literature.FleschThuijsmanAndVrieze1997.stationaryBehaviorProfile profile

/-- Terminal limiting-average equilibrium against all behavioral deviations. -/
abbrev Example3EpsilonEquilibrium (ε : ℝ) (profile : Example3StationaryProfile) : Prop :=
  example3Game.IsεAsymptoticNash (GameTheory.quittingTerminalPayoff example3Reward) ε
    (example3StationaryBehaviorProfile profile)

local instance : Finite example3Game.State :=
  inferInstanceAs (Finite (Option {S : Finset Example3Player // S.Nonempty}))

local instance (who : Example3Player) : Finite (example3Game.Act who) :=
  inferInstanceAs (Finite Bool)

/-- The literal expected pathwise liminf of the actual Example 3 play law. -/
def example3PathwisePayoff (initial : example3Game.State)
    (profile : example3Game.BehaviorProfile) (who : Example3Player) : ℝ :=
  ∫ play, liminf (fun n => example3Game.pathwiseAveragePayoff who n play) atTop
    ∂example3Game.infinitePlayMeasure profile initial

/-- The paper's stationary epsilon-equilibrium notion, at every initial state. -/
def Example3PathwiseEpsilonEquilibrium (ε : ℝ) (profile : Example3StationaryProfile) : Prop :=
  ∀ initial, example3Game.IsεAsymptoticNash (example3PathwisePayoff initial) ε
    (example3StationaryBehaviorProfile profile)

/-- Every behavioral profile's literal live-state payoff equals its terminal payoff. -/
theorem example3PathwisePayoff_none (profile : example3Game.BehaviorProfile)
    (who : Example3Player) :
    example3PathwisePayoff none profile who =
      GameTheory.quittingTerminalPayoff example3Reward profile who :=
  GameTheory.integral_liminf_pathwiseAveragePayoff_quittingGame_none example3Reward profile who

/-- Every behavioral profile has the same literal payoff at an absorbed initial state. -/
theorem example3PathwisePayoff_some (profile : example3Game.BehaviorProfile)
    (S : {S : Finset Example3Player // S.Nonempty}) (who : Example3Player) :
    example3PathwisePayoff (some S) profile who = example3Reward S who :=
  GameTheory.integral_liminf_pathwiseAveragePayoff_quittingGame_some example3Reward profile S who

/-- Actual all-initial-state equilibrium is exactly terminal equilibrium, for every error. -/
theorem example3_pathwiseEquilibrium_iff_terminal (ε : ℝ)
    (profile : Example3StationaryProfile) :
    Example3PathwiseEpsilonEquilibrium ε profile ↔ Example3EpsilonEquilibrium ε profile := by
  constructor
  · intro hNash who deviation
    have hnone := hNash none who deviation
    simpa only [example3PathwisePayoff_none] using hnone
  · intro hNash initial who deviation
    cases initial with
    | none => simpa only [example3PathwisePayoff_none] using hNash who deviation
    | some S =>
        simp only [example3PathwisePayoff_some]
        have hself := hNash who ((example3StationaryBehaviorProfile profile) who)
        rw [Function.update_eq_self] at hself
        have hε : 0 ≤ ε := by linarith
        exact le_add_of_nonneg_right hε

@[simp] theorem example3TerminalReward_TLN :
    example3TerminalReward ![false, false, false] = ![0, 0, 0] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_TLN

@[simp] theorem example3TerminalReward_BLN :
    example3TerminalReward ![true, false, false] = ![1, 3, 0] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_BLN

@[simp] theorem example3TerminalReward_TRN :
    example3TerminalReward ![false, true, false] = ![0, 1, 3] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_TRN

@[simp] theorem example3TerminalReward_TLF :
    example3TerminalReward ![false, false, true] = ![3, 0, 1] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_TLF

@[simp] theorem example3TerminalReward_BRN :
    example3TerminalReward ![true, true, false] = ![1, 0, 1] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_BRN

@[simp] theorem example3TerminalReward_BLF :
    example3TerminalReward ![true, false, true] = ![0, 1, 1] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_BLF

@[simp] theorem example3TerminalReward_TRF :
    example3TerminalReward ![false, true, true] = ![1, 1, 0] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_TRF

@[simp] theorem example3TerminalReward_BRF :
    example3TerminalReward ![true, true, true] = ![0, 0, 0] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_BRF

/-- Example 3 has no exact stationary terminal equilibrium. -/
theorem example3_no_stationary_equilibrium :
    ¬ ∃ profile : Example3StationaryProfile, Example3EpsilonEquilibrium 0 profile :=
  Literature.FleschThuijsmanAndVrieze1997.lemma3_1

/-- The literal printed exclusion for every positive error is false. -/
theorem example3_printed_refuted :
    ¬ (∀ ε : ℝ, 0 < ε →
      ¬ ∃ profile : Example3StationaryProfile, Example3EpsilonEquilibrium ε profile) :=
  Literature.FleschThuijsmanAndVrieze1997.theorem3_2_printed_refuted

/-- Corrected Example 3: exclusion holds below one positive error threshold. -/
theorem example3_corrected :
    ∃ threshold : ℝ, 0 < threshold ∧
      ∀ ε : ℝ, 0 < ε → ε < threshold →
        ¬ ∃ profile : Example3StationaryProfile, Example3EpsilonEquilibrium ε profile :=
  Literature.FleschThuijsmanAndVrieze1997.theorem3_2_corrected

/-- Example 3 has no exact stationary equilibrium for literal expected pathwise liminf. -/
theorem example3_no_stationary_pathwise_equilibrium :
    ¬ ∃ profile : Example3StationaryProfile, Example3PathwiseEpsilonEquilibrium 0 profile := by
  rintro ⟨profile, hprofile⟩
  exact example3_no_stationary_equilibrium
    ⟨profile, (example3_pathwiseEquilibrium_iff_terminal 0 profile).mp hprofile⟩

/-- The all-positive-error exclusion is false also for the paper's literal payoff convention. -/
theorem example3_printed_pathwise_refuted :
    ¬ (∀ ε : ℝ, 0 < ε →
      ¬ ∃ profile : Example3StationaryProfile, Example3PathwiseEpsilonEquilibrium ε profile) := by
  intro hexclusion
  apply example3_printed_refuted
  intro ε hε
  rintro ⟨profile, hprofile⟩
  exact hexclusion ε hε
    ⟨profile, (example3_pathwiseEquilibrium_iff_terminal ε profile).mpr hprofile⟩

/-- The corrected small-error exclusion uses actual payoffs at every initial state. -/
theorem example3_pathwise_corrected :
    ∃ threshold : ℝ, 0 < threshold ∧
      ∀ ε : ℝ, 0 < ε → ε < threshold →
        ¬ ∃ profile : Example3StationaryProfile,
          Example3PathwiseEpsilonEquilibrium ε profile := by
  obtain ⟨threshold, hthreshold, hexclusion⟩ := example3_corrected
  refine ⟨threshold, hthreshold, ?_⟩
  intro ε hε hsmall
  rintro ⟨profile, hprofile⟩
  exact hexclusion ε hε hsmall
    ⟨profile, (example3_pathwiseEquilibrium_iff_terminal ε profile).mp hprofile⟩

/-! ## Section 4: Remark 1

The source's restricted simplex imposes a lower bound on the total probability
of every nonempty proper subset of actions, not just a coordinate floor.
Its printed range `0 < delta < 1` can make that domain empty: with two actions,
both singleton masses must be at least delta. The exact feasibility threshold
is delta at most 1/2. The general uniform witness below establishes feasibility
for sufficiently small delta. The following auxiliary Nash result uses the
source's linearized payoff, not the actual stationary payoff of the game.
The remark's limiting ranking properties remain separate obligations.
-/

/-- The literal Remark 1 domain, with every nonempty proper-subset mass constraint. -/
def remark1RestrictedStrategies (I : Type*) [Fintype I] (δ : ℝ) : Set (I → ℝ) :=
  {x | x ∈ GameTheory.Math.Probability.simplexWeights I ∧
    ∀ U : Finset I, U.Nonempty → U ⊂ Finset.univ →
      δ ^ (Fintype.card I - U.card) ≤ ∑ i ∈ U, x i}

/-- The source subset domain is closed, even when its constraints are infeasible. -/
theorem remark1_isClosed_restrictedStrategies (I : Type*) [Fintype I] (δ : ℝ) :
    IsClosed (remark1RestrictedStrategies I δ) := by
  classical
  have heq : remark1RestrictedStrategies I δ =
      GameTheory.Math.Probability.simplexWeights I ∩
        ⋂ U : Finset I, ⋂ _ : U.Nonempty, ⋂ _ : U ⊂ Finset.univ,
          {x : I → ℝ | δ ^ (Fintype.card I - U.card) ≤ ∑ i ∈ U, x i} := by
    ext x
    simp [remark1RestrictedStrategies]
  rw [heq]
  exact (GameTheory.Math.Probability.isClosed_simplexWeights I).inter
    (isClosed_iInter fun U => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_finsetSum U fun i _ => continuous_apply i))

/-- Compactness is inherited from the existing finite simplex. -/
theorem remark1_isCompact_restrictedStrategies (I : Type*) [Fintype I] (δ : ℝ) :
    IsCompact (remark1RestrictedStrategies I δ) :=
  (GameTheory.Math.Probability.isCompact_simplexWeights I).of_isClosed_subset
    (remark1_isClosed_restrictedStrategies I δ) (fun _ hx => hx.1)

/-- Every literal subset constraint is preserved by convex combinations. -/
theorem remark1_convex_restrictedStrategies (I : Type*) [Fintype I] (δ : ℝ) :
    Convex ℝ (remark1RestrictedStrategies I δ) := by
  intro x hx y hy s t hs ht hst
  refine ⟨GameTheory.Math.Probability.convex_simplexWeights I hx.1 hy.1 hs ht hst, ?_⟩
  intro U hU hproper
  change δ ^ (Fintype.card I - U.card) ≤ ∑ i ∈ U, (s * x i + t * y i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    δ ^ (Fintype.card I - U.card) =
        s * δ ^ (Fintype.card I - U.card) + t * δ ^ (Fintype.card I - U.card) := by
      rw [← add_mul, hst, one_mul]
    _ ≤ s * (∑ i ∈ U, x i) + t * (∑ i ∈ U, y i) :=
      add_le_add (mul_le_mul_of_nonneg_left (hx.2 U hU hproper) hs)
        (mul_le_mul_of_nonneg_left (hy.2 U hU hproper) ht)

/-- Canonical uniform weights satisfy every source constraint for sufficiently small delta. -/
theorem remark1_uniform_mem_restrictedStrategies {I : Type*} [Fintype I] {δ : ℝ}
    (hδ : 0 < δ) (hsmall : δ ≤ (Fintype.card I : ℝ)⁻¹) :
    (fun _ : I => (Fintype.card I : ℝ)⁻¹) ∈ remark1RestrictedStrategies I δ := by
  classical
  have hcard : 0 < Fintype.card I := by
    by_contra hnot
    have hzero : Fintype.card I = 0 := Nat.eq_zero_of_not_pos hnot
    have hnonpos : δ ≤ 0 := by simpa only [hzero, Nat.cast_zero, inv_zero] using hsmall
    exact (not_le_of_gt hδ) hnonpos
  let : Nonempty I := Fintype.card_pos_iff.mp hcard
  have hcardReal : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hcard
  have hcardOne : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast hcard
  have hδOne : δ ≤ 1 := hsmall.trans ((inv_le_one₀ hcardReal).mpr hcardOne)
  refine ⟨?_, ?_⟩
  · have hweights :
        ((Convexity.StdSimplex.barycenter (K := ℝ) (M := I)).weights : I → ℝ) =
          fun _ : I => (Fintype.card I : ℝ)⁻¹ := by
      funext i
      exact Convexity.StdSimplex.weights_barycenter_apply i
    rw [← hweights]
    exact weights_mem_simplexWeights (Convexity.StdSimplex.barycenter (K := ℝ) (M := I))
  · intro U hU hproper
    have hless : U.card < Fintype.card I := by
      simpa only [Finset.card_univ] using Finset.card_lt_card hproper
    have hexponent : 1 ≤ Fintype.card I - U.card := Nat.sub_pos_of_lt hless
    have hUOne : (1 : ℝ) ≤ U.card := by exact_mod_cast Finset.card_pos.mpr hU
    calc
      δ ^ (Fintype.card I - U.card) ≤ δ := by
        simpa only [pow_one] using pow_le_pow_of_le_one hδ.le hδOne hexponent
      _ ≤ (Fintype.card I : ℝ)⁻¹ := hsmall
      _ ≤ (U.card : ℝ) * (Fintype.card I : ℝ)⁻¹ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hUOne (inv_nonneg.mpr hcardReal.le)
      _ = ∑ i ∈ U, (Fintype.card I : ℝ)⁻¹ := by
        simp only [Finset.sum_const, nsmul_eq_mul]

/-- The literal restricted simplex is nonempty throughout a sufficient small-delta range. -/
theorem remark1_restrictedStrategies_nonempty_of_smallDelta
    {I : Type*} [Fintype I] {δ : ℝ}
    (hδ : 0 < δ) (hsmall : δ ≤ (Fintype.card I : ℝ)⁻¹) :
    (remark1RestrictedStrategies I δ).Nonempty :=
  ⟨_, remark1_uniform_mem_restrictedStrategies hδ hsmall⟩

/-- On two actions, the printed subset domain is feasible exactly up to delta 1/2. -/
theorem remark1_finTwo_nonempty_iff {δ : ℝ} :
    (remark1RestrictedStrategies (Fin 2) δ).Nonempty ↔ δ ≤ 1 / 2 := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    have hzero := hx.2 {0} (by simp) (by decide)
    have hone := hx.2 {1} (by simp) (by decide)
    norm_num at hzero hone
    have hsum : x 0 + x 1 = 1 := by
      simpa only [Fin.sum_univ_two] using
        (GameTheory.Math.Probability.mem_simplexWeights.mp hx.1).2
    linarith
  · intro hhalf
    have huniform := remark1_uniform_mem_restrictedStrategies
      (I := Fin 2) (δ := 1 / 2) (by norm_num) (by norm_num)
    refine ⟨_, huniform.1, ?_⟩
    intro U hU hproper
    have hUpos : 0 < U.card := Finset.card_pos.mpr hU
    have hUless : U.card < 2 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hproper
    have hUcard : U.card = 1 := by omega
    simpa [hUcard] using hhalf

/-- Delta 3/4 lies in the printed range but its two-action source domain is empty. -/
theorem remark1_finTwo_threeQuarter_empty :
    remark1RestrictedStrategies (Fin 2) (3 / 4) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hhalf := (remark1_finTwo_nonempty_iff (δ := 3 / 4)).mp ⟨x, hx⟩
  norm_num at hhalf

/-- A necessary domain-feasibility consequence of the printed full delta range. -/
def Remark1FinTwoAllDeltaFeasibilityClaim : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → (remark1RestrictedStrategies (Fin 2) δ).Nonempty

/-- The printed unrestricted delta range already fails for a two-action strategy set. -/
theorem remark1_printedDeltaRange_refuted : ¬ Remark1FinTwoAllDeltaFeasibilityClaim := by
  intro hclaim
  obtain ⟨x, hx⟩ := hclaim (3 / 4) (by norm_num) (by norm_num)
  rw [remark1_finTwo_threeQuarter_empty] at hx
  exact hx

private theorem remark1_delta_le_one {A : Type*} [Fintype A] {δ : ℝ}
    (hδ : 0 < δ) (hsmall : δ ≤ (Fintype.card A : ℝ)⁻¹) : δ ≤ 1 := by
  by_cases hzero : Fintype.card A = 0
  · have hnonpos : δ ≤ 0 := by simpa only [hzero, Nat.cast_zero, inv_zero] using hsmall
    exact False.elim ((not_le_of_gt hδ) hnonpos)
  · have hcard : (1 : ℝ) ≤ Fintype.card A := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
    exact hsmall.trans ((inv_le_one₀ (lt_of_lt_of_le zero_lt_one hcard)).mpr hcard)

/-- Literal singleton constraints imply the weaker cardinality-power coordinate floor. -/
theorem remark1_restrictedStrategies_subset_lowerSimplex {A : Type*} [Fintype A]
    {δ : ℝ} (hδ : 0 < δ) (hδOne : δ ≤ 1) :
    remark1RestrictedStrategies A δ ⊆ Math.Probability.RatioProperPair.lowerSimplex A δ := by
  classical
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro i
  by_cases hfull : ({i} : Finset A) = Finset.univ
  · have hxi : x i = 1 := by
      have hsum := (GameTheory.Math.Probability.mem_simplexWeights.mp hx.1).2
      rw [← hfull] at hsum
      simpa only [Finset.sum_singleton] using hsum
    rw [hxi]
    exact pow_le_one₀ hδ.le hδOne
  · have hproper : ({i} : Finset A) ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hfull⟩
    have hsingleton := hx.2 {i} (by simp) hproper
    simp only [Finset.card_singleton, Finset.sum_singleton] at hsingleton
    exact (pow_le_pow_of_le_one hδ.le hδOne (Nat.sub_le _ _)).trans hsingleton

private def remark1Barycenter {A : Type*} [Fintype A] (δ : ℝ) (n : ℕ)
    (weights : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (points : Fin (n + 1) → remark1RestrictedStrategies A δ) :
    remark1RestrictedStrategies A δ :=
  ⟨∑ a, weights.weights a • (points a).val,
    (remark1_convex_restrictedStrategies A δ).sum_mem
      (fun a _ => weights.weights_nonneg a) weights.total_of_fintype
      (fun a _ => (points a).property)⟩

private theorem continuous_remark1Barycenter {A : Type*} [Fintype A]
    (δ : ℝ) (n : ℕ) (points : Fin (n + 1) → remark1RestrictedStrategies A δ) :
    Continuous fun weights : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
      remark1Barycenter δ n weights points := by
  apply Continuous.subtype_mk
  apply continuous_finsetSum
  intro a _
  exact (Convexity.StdSimplex.continuous_weights_apply ℝ a).smul continuous_const

private theorem remark1Barycenter_linear {A : Type*} [Fintype A]
    (δ : ℝ) (n : ℕ) (weights : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (points : Fin (n + 1) → remark1RestrictedStrategies A δ) (coefficient : A → ℝ) :
    (∑ i, (remark1Barycenter δ n weights points).val i * coefficient i) =
      ∑ a, weights.weights a * (∑ i, (points a).val i * coefficient i) := by
  change (∑ i, (∑ a, weights.weights a • (points a).val) i * coefficient i) = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum, mul_assoc]

omit [Fintype I] in
private theorem continuous_remark1_rowValue (G : AbsorbingGameData I J)
    {δ : ℝ} (hδ : 0 < δ) (hδOne : δ ≤ 1) (i : I) :
    Continuous fun y : remark1RestrictedStrategies J δ =>
      pureStationaryPayoff1 G ⟨y.val, y.property.1⟩ i := by
  let inclusion : remark1RestrictedStrategies J δ →
      Math.Probability.RatioProperPair.lowerSimplex J δ :=
    fun y => ⟨y.val, remark1_restrictedStrategies_subset_lowerSimplex hδ hδOne y.property⟩
  have hcontinuous : Continuous inclusion := continuous_subtype_val.subtype_mk _
  exact (Math.Probability.RatioProperPair.continuous_rowRatio_lowerSimplex
    G.absorptionCoefficients G.payoffNumerator1
    (fun i j => (G.absorptionProbability i j).property.1) hδ i).comp hcontinuous

omit [Fintype J] in
private theorem continuous_remark1_columnValue (G : AbsorbingGameData I J)
    {δ : ℝ} (hδ : 0 < δ) (hδOne : δ ≤ 1) (j : J) :
    Continuous fun x : remark1RestrictedStrategies I δ =>
      pureStationaryPayoff2 G ⟨x.val, x.property.1⟩ j := by
  let inclusion : remark1RestrictedStrategies I δ →
      Math.Probability.RatioProperPair.lowerSimplex I δ :=
    fun x => ⟨x.val, remark1_restrictedStrategies_subset_lowerSimplex hδ hδOne x.property⟩
  have hcontinuous : Continuous inclusion := continuous_subtype_val.subtype_mk _
  exact (Math.Probability.RatioProperPair.continuous_columnRatio_lowerSimplex
    G.absorptionCoefficients G.payoffNumerator2
    (fun i j => (G.absorptionProbability i j).property.1) hδ j).comp hcontinuous

private def remark1LinearizedGame {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (δ : ℝ) (hδ : 0 < δ)
    (hA : δ ≤ (Fintype.card A : ℝ)⁻¹) (hB : δ ≤ (Fintype.card B : ℝ)⁻¹) :
    GameTheory.CompactBarycentricGame where
  Player := Bool
  Strategy := fun who => match who with
    | false => remark1RestrictedStrategies A δ
    | true => remark1RestrictedStrategies B δ
  strategyTopology := fun who => by cases who <;> infer_instance
  compactStrategy := fun who => by
    cases who
    · exact isCompact_iff_compactSpace.mp (remark1_isCompact_restrictedStrategies A δ)
    · exact isCompact_iff_compactSpace.mp (remark1_isCompact_restrictedStrategies B δ)
  nonemptyStrategy := fun who => by
    cases who
    · exact (remark1_restrictedStrategies_nonempty_of_smallDelta hδ hA).to_subtype
    · exact (remark1_restrictedStrategies_nonempty_of_smallDelta hδ hB).to_subtype
  payoff := fun profile who => match who with
    | false => ∑ i, (profile false).val i *
        pureStationaryPayoff1 G ⟨(profile true).val, (profile true).property.1⟩ i
    | true => ∑ j, (profile true).val j *
        pureStationaryPayoff2 G ⟨(profile false).val, (profile false).property.1⟩ j
  payoffContinuous := fun who => by
    let : (player : Bool) → TopologicalSpace (match player with
      | false => remark1RestrictedStrategies A δ
      | true => remark1RestrictedStrategies B δ) := fun player => by
        cases player <;> infer_instance
    let Profile := (player : Bool) → match player with
      | false => remark1RestrictedStrategies A δ
      | true => remark1RestrictedStrategies B δ
    have hrow : Continuous (fun profile : Profile => (profile false).val) :=
      continuous_subtype_val.comp (continuous_apply false)
    have hcolumn : Continuous (fun profile : Profile => (profile true).val) :=
      continuous_subtype_val.comp (continuous_apply true)
    cases who
    · apply continuous_finsetSum
      intro i _
      exact ((continuous_apply i).comp hrow).mul
        ((continuous_remark1_rowValue G hδ (remark1_delta_le_one hδ hB) i).comp
          (continuous_apply true))
    · apply continuous_finsetSum
      intro j _
      exact ((continuous_apply j).comp hcolumn).mul
        ((continuous_remark1_columnValue G hδ (remark1_delta_le_one hδ hA) j).comp
          (continuous_apply false))
  barycenter := fun who => by
    cases who
    · exact remark1Barycenter δ
    · exact remark1Barycenter δ
  barycenterContinuous := fun who => by
    cases who
    · exact continuous_remark1Barycenter δ
    · exact continuous_remark1Barycenter δ
  payoffBarycentric := by
    intro profile who n weights points
    cases who
    · simpa only [Function.update_self, Function.update_of_ne (by decide : true ≠ false)]
        using remark1Barycenter_linear δ n weights points
          (pureStationaryPayoff1 G ⟨(profile true).val, (profile true).property.1⟩)
    · simpa only [Function.update_self, Function.update_of_ne (by decide : false ≠ true)]
        using remark1Barycenter_linear δ n weights points
          (pureStationaryPayoff2 G ⟨(profile false).val, (profile false).property.1⟩)

/-- Remark 1's literal small-delta domains admit Nash for the linearized auxiliary payoffs. -/
theorem remark1_exists_restrictedLinearizedNash {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) {δ : ℝ} (hδ : 0 < δ)
    (hA : δ ≤ (Fintype.card A : ℝ)⁻¹) (hB : δ ≤ (Fintype.card B : ℝ)⁻¹) :
    ∃ (x : StationaryStrategy A) (y : StationaryStrategy B),
      x.val ∈ remark1RestrictedStrategies A δ ∧
      y.val ∈ remark1RestrictedStrategies B δ ∧
      (∀ x' : StationaryStrategy A, x'.val ∈ remark1RestrictedStrategies A δ →
        (∑ i, x'.val i * pureStationaryPayoff1 G y i) ≤
          ∑ i, x.val i * pureStationaryPayoff1 G y i) ∧
      (∀ y' : StationaryStrategy B, y'.val ∈ remark1RestrictedStrategies B δ →
        (∑ j, y'.val j * pureStationaryPayoff2 G x j) ≤
          ∑ j, y.val j * pureStationaryPayoff2 G x j) := by
  obtain ⟨profile, hprofile⟩ := (remark1LinearizedGame G δ hδ hA hB).exists_nash
  refine ⟨⟨(profile false).val, (profile false).property.1⟩,
    ⟨(profile true).val, (profile true).property.1⟩,
    (profile false).property, (profile true).property, ?_, ?_⟩
  · intro x' hx'
    let deviation : (remark1LinearizedGame G δ hδ hA hB).Strategy false := ⟨x'.val, hx'⟩
    let updated := Function.update profile false deviation
    have hself : updated false = deviation := Function.update_self _ _ _
    have hother : updated true = profile true :=
      Function.update_of_ne (by decide : (true : Bool) ≠ false) _ _
    have hbound := hprofile false deviation
    change (∑ i, (updated false).val i *
        pureStationaryPayoff1 G ⟨(updated true).val, (updated true).property.1⟩ i) ≤
      ∑ i, (profile false).val i *
        pureStationaryPayoff1 G ⟨(profile true).val, (profile true).property.1⟩ i at hbound
    rw [hself, hother] at hbound
    exact hbound
  · intro y' hy'
    let deviation : (remark1LinearizedGame G δ hδ hA hB).Strategy true := ⟨y'.val, hy'⟩
    let updated := Function.update profile true deviation
    have hself : updated true = deviation := Function.update_self _ _ _
    have hother : updated false = profile false :=
      Function.update_of_ne (by decide : (false : Bool) ≠ true) _ _
    have hbound := hprofile true deviation
    change (∑ j, (updated true).val j *
        pureStationaryPayoff2 G ⟨(updated false).val, (updated false).property.1⟩ j) ≤
      ∑ j, (profile true).val j *
        pureStationaryPayoff2 G ⟨(profile false).val, (profile false).property.1⟩ j at hbound
    rw [hself, hother] at hbound
    exact hbound

/-! ## Section 4: Remark 2

The alternative payoff is the liminf of expected finite averages, rather than
the expectation of the pathwise liminf. The canonical recursive-absorption
model's existing convergence theorem identifies these conventions even for
arbitrary behavioral profiles. This is not a claim that the general original
absorbing-stage model has been reduced to this canonical model. Remarks 1 and 3
for that original model remain separate obligations, as does Example 4.
-/

/-- Remark 2's alternative limiting-average payoff convention for the canonical game. -/
def alternativeCanonicalPayoff {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (initial : (canonicalGame G).State)
    (profile : (canonicalGame G).BehaviorProfile) (who : Bool) : ℝ :=
  liminf (fun horizon => (canonicalGame G).finiteAveragePayoff initial horizon profile who) atTop

/-- In the canonical model the two payoff conventions agree for every behavioral profile. -/
theorem remark2_canonical_payoffs_eq {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (initial : (canonicalGame G).State)
    (profile : (canonicalGame G).BehaviorProfile) (who : Bool) :
    alternativeCanonicalPayoff G initial profile who = canonicalPayoff G initial profile who :=
  (GameTheory.RecursiveAbsorption.tendsto_finiteAveragePayoff_liminfPayoff
    G.canonicalData profile initial who).liminf_eq

/-- Consequently the actual all-behavior equilibrium predicates agree in the canonical model. -/
theorem remark2_canonical_equilibrium_iff {A B : Type} [Fintype A] [Fintype B]
    (G : AbsorbingGameData A B) (initial : (canonicalGame G).State) (ε : ℝ)
    (profile : (canonicalGame G).BehaviorProfile) :
    (canonicalGame G).IsεAsymptoticNash (alternativeCanonicalPayoff G initial) ε profile ↔
      (canonicalGame G).IsεAsymptoticNash (canonicalPayoff G initial) ε profile := by
  have hpayoff : alternativeCanonicalPayoff G initial = canonicalPayoff G initial := by
    funext behavior who
    exact remark2_canonical_payoffs_eq G initial behavior who
  rw [hpayoff]

/-- The canonical stationary existence result also holds under Remark 2's alternative convention. -/
theorem remark2_theorem3_1_canonical {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (G : AbsorbingGameData A B) {ε : ℝ} (hε : 0 < ε) :
    ∃ (x : StationaryStrategy A) (y : StationaryStrategy B), ∀ initial,
      (canonicalGame G).IsεAsymptoticNash (alternativeCanonicalPayoff G initial) ε
        (canonicalStationaryProfile G x y) := by
  obtain ⟨x, y, hxy⟩ := theorem3_1_canonical G hε
  exact ⟨x, y, fun initial =>
    (remark2_canonical_equilibrium_iff G initial ε (canonicalStationaryProfile G x y)).mpr
      (hxy initial)⟩

/-! ## Section 4: Remark 3

The canonical producer selects its stationary pair at a smaller error and
uses a finite-horizon potential bound uniformly over behavioral deviations.
Consequently one positive cutoff works for all initial states and every longer
horizon. Pointwise convergence for separately fixed deviations is not used
as a substitute for that uniform bound. The original absorbing-stage reduction
is still pending; no fixed-payoff-target conclusion is asserted here.
-/

open GameTheory.RecursiveAbsorption in
/-- Canonical Remark 3: one stationary pair is limiting Nash and eventually finite-horizon Nash. -/
theorem remark3_canonical {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (G : AbsorbingGameData A B) {ε : ℝ} (hε : 0 < ε) :
    ∃ (x : StationaryStrategy A) (y : StationaryStrategy B),
      (∀ initial, (canonicalGame G).IsεAsymptoticNash (canonicalPayoff G initial) ε
        (canonicalStationaryProfile G x y)) ∧
      ∃ cutoff : ℕ, 0 < cutoff ∧ ∀ horizon, cutoff ≤ horizon → ∀ initial,
        (canonicalGame G).IsεHorizonNash initial horizon ε (canonicalStationaryProfile G x y) := by
  obtain ⟨x, y, hxy⟩ :=
    exists_stationary_liminfApproximateEquilibrium_with_eventual_horizonNash
      G.canonicalData hε
  refine ⟨⟨toVector x, toVector_mem_stdSimplex x⟩,
    ⟨toVector y, toVector_mem_stdSimplex y⟩, ?_⟩
  simpa only [canonicalStationaryProfile, stationaryLaw, ofVector_toVector] using hxy

end Literature.FleschThuijsmanAndVrieze1996
