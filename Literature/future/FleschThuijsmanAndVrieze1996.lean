import Literature.FleschThuijsmanAndVrieze1997
import MathUE.Probability.RatioProperPair
import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.RecursiveAbsorption.ProperPairLimit
import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.RecursiveAbsorption.BestReplyMassEstimate

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
one positive threshold is retained.

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
Examples 2 and 4 and the three final remarks are not formalized here.
The canonical statements do not settle the original model reduction. This file
does not claim complete paper coverage or a fixed-target
uniform-equilibrium payoff from Theorem 3.1.
-/

noncomputable section

open _root_.Math.ProbabilityMassFunction
open Filter
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

/-- The first/first limit of the printed delta family is a proper pair. -/
theorem example1_firstFirst_proper :
    IsProperPair example1Data example1FirstStrategy example1FirstStrategy := by
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

/-- The printed Example 1 family's live-state row payoff is at most three halves. -/
theorem example1_printedFamily_rowPayoff_le (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) :
    canonicalPayoff example1Data none
      (canonicalStationaryProfile example1Data (example1Strategy δ hδ.le hδhalf)
        (example1Strategy δ hδ.le hδhalf)) false ≤ 3 / 2 := by
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
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hδ) (by linarith))).mpr
  nlinarith [sq_nonneg (δ ^ 2)]

/-- The printed family is not an approximate equilibrium at errors below one half. -/
theorem example1_printedFamily_not_smallErrorNash (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) {ε : ℝ} (hε : ε < 1 / 2) :
    ¬ (canonicalGame example1Data).IsεAsymptoticNash
      (canonicalPayoff example1Data none) ε
      (canonicalStationaryProfile example1Data (example1Strategy δ hδ.le hδhalf)
        (example1Strategy δ hδ.le hδhalf)) := by
  intro hNash
  have hpure := pureRowPayoff_le_of_canonicalNash example1Data
    (example1Strategy δ hδ.le hδhalf) (example1Strategy δ hδ.le hδhalf) hNash 0
  rw [example1_pureStationaryPayoff1 δ hδ hδhalf] at hpure
  norm_num at hpure
  have hpayoff := example1_printedFamily_rowPayoff_le δ hδ hδhalf
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

The definitions below use the checked terminal-payoff presentation from the
1997 formalization. They do not introduce a separate expected-pathwise-liminf
semantics or prove a new equivalence with that semantics. Unilateral deviations
in the equilibrium predicate are all behavioral strategies, not just stationary
ones. The error and stationary-profile quantifiers are preserved exactly.
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

end Literature.FleschThuijsmanAndVrieze1996
