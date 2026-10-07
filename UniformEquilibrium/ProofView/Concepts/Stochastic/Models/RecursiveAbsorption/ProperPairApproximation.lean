import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.RecursiveAbsorption.AbsorptionWeightedPayoff
import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.RecursiveAbsorption.BestResponse
import MathUE.Probability.RatioProperPair
import MathUE.ProbabilityMassFunction.BoundedSupportAverage
import MathUE.ProbabilityMassFunction.SupportExpectationEquality

/-!
# Proper-ranking estimates for actual recursive absorption games

The actual absorption probabilities and absorption-weighted rewards supply the
generic proper-pair construction from Flesch, Thuijsman and Vrieze (1996),
Definition 2.3 and Theorem 2.4. The rankings concern the checked stationary
payoffs of this model, not independent raw numerator tables.

The finite estimates below derive bad absorption mass from proper ranking.
Positive anchor hazards and maximality are local helper hypotheses; they are
not premises of an approximate-equilibrium existence result. The proper-limit
absorbing and recurrent cases and simultaneous behavioral payoff caps remain
to be constructed. The original paper's absorbing-stage reduction is distinct
from this canonical model and is not asserted here.
-/

noncomputable section

open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open _root_.Math.Probability.FiniteLawRepair
open GameTheory.Math.Probability
open Filter
open scoped BigOperators Topology

namespace GameTheory.RecursiveAbsorption

variable {I J : Type} [Fintype I] [Fintype J]

/-- The actual live-state absorption coefficients. -/
def absorptionCoefficients (D : Data I J) (i : I) (j : J) : ℝ := D.absorption i j

/-- The actual absorption-weighted reward table for one player. -/
def payoffNumerator (D : Data I J) (who : Bool) (i : I) (j : J) : ℝ :=
  absorptionCoefficients D i j * D.reward i j who

omit [Fintype I] in
/-- The generic pure-row ratio is the model's checked stationary payoff. -/
theorem rowRatio_eq_stationaryPayoff (D : Data I J) (y : PMF J) (who : Bool) (i : I) :
    _root_.Math.Probability.RatioProperPair.rowRatio
      (absorptionCoefficients D) (payoffNumerator D who) (toVector y) i =
        stationaryPayoff D (PMF.pure i) y who := by
  simp only [_root_.Math.Probability.RatioProperPair.rowRatio, stationaryPayoff,
    absorbingContribution, absorptionMass, expect_pure, expect_eq_sum,
    toVector, payoffNumerator, absorptionCoefficients]

omit [Fintype J] in
/-- The corresponding generic pure-column ratio agrees with the actual payoff. -/
theorem columnRatio_eq_stationaryPayoff (D : Data I J) (x : PMF I) (who : Bool) (j : J) :
    _root_.Math.Probability.RatioProperPair.columnRatio
      (absorptionCoefficients D) (payoffNumerator D who) (toVector x) j =
        stationaryPayoff D x (PMF.pure j) who := by
  simp only [_root_.Math.Probability.RatioProperPair.columnRatio, stationaryPayoff,
    absorbingContribution, absorptionMass, expect_pure, expect_eq_sum,
    toVector, payoffNumerator, absorptionCoefficients]

/-- Delta-properness of actual independent stationary PMFs. -/
def IsDeltaProperPair (D : Data I J) (δ : ℝ) (x : PMF I) (y : PMF J) : Prop :=
  _root_.Math.Probability.RatioProperPair.IsDeltaProperPair
    (absorptionCoefficients D) (payoffNumerator D false) (payoffNumerator D true)
    δ (toVector x) (toVector y)

/-- Properness of actual stationary PMFs, via their finite probability coordinates. -/
def IsProperPair (D : Data I J) (x : PMF I) (y : PMF J) : Prop :=
  _root_.Math.Probability.RatioProperPair.IsProperPair
    (absorptionCoefficients D) (payoffNumerator D false) (payoffNumerator D true)
    (toVector x) (toVector y)

/-- Theorem 2.4's producer, using actual probabilities and internally weighted rewards. -/
theorem exists_properPair [Nonempty I] [Nonempty J] (D : Data I J) :
    ∃ (x : PMF I) (y : PMF J), IsProperPair D x y := by
  obtain ⟨x, y, hproper⟩ := _root_.Math.Probability.RatioProperPair.exists_properPair
    (absorptionCoefficients D) (payoffNumerator D false) (payoffNumerator D true)
    (fun i j => (D.absorption i j).2.1)
  refine ⟨ofVector x hproper.1, ofVector y hproper.2.1, ?_⟩
  simpa only [IsProperPair, toVector_ofVector] using hproper

theorem IsDeltaProperPair.row_pos {D : Data I J} {δ : ℝ} {x : PMF I} {y : PMF J}
    (hproper : IsDeltaProperPair D δ x y) (i : I) : 0 < (x i).toReal :=
  hproper.2.2.2.2.1 i

theorem IsDeltaProperPair.column_pos {D : Data I J} {δ : ℝ} {x : PMF I} {y : PMF J}
    (hproper : IsDeltaProperPair D δ x y) (j : J) : 0 < (y j).toReal :=
  hproper.2.2.2.2.2.1 j

/-- Actual strict row-payoff ranking bounds the worse action's raw probability. -/
theorem IsDeltaProperPair.row_ranking {D : Data I J} {δ : ℝ} {x : PMF I} {y : PMF J}
    (hproper : IsDeltaProperPair D δ x y) (anchor other : I)
    (hstrict : stationaryPayoff D (PMF.pure other) y false <
      stationaryPayoff D (PMF.pure anchor) y false) :
    (x other).toReal ≤ δ * (x anchor).toReal := by
  apply hproper.2.2.2.2.2.2.1 anchor other
  simpa only [rowRatio_eq_stationaryPayoff] using hstrict

theorem IsDeltaProperPair.column_ranking {D : Data I J} {δ : ℝ} {x : PMF I} {y : PMF J}
    (hproper : IsDeltaProperPair D δ x y) (anchor other : J)
    (hstrict : stationaryPayoff D x (PMF.pure other) true <
      stationaryPayoff D x (PMF.pure anchor) true) :
    (y other).toReal ≤ δ * (y anchor).toReal := by
  apply hproper.2.2.2.2.2.2.2 anchor other
  simpa only [columnRatio_eq_stationaryPayoff] using hstrict

/-- Positive actual mixed absorption supplies a supported positive-hazard row. -/
theorem exists_supported_row_positive_hazard (D : Data I J) (x : PMF I) (y : PMF J)
    (hpositive : 0 < absorptionMass D x y) :
    ∃ i, 0 < (x i).toReal ∧ 0 < absorptionMass D (PMF.pure i) y := by
  obtain ⟨i, hi, hle⟩ := exists_mem_support_expect_le x
    (fun i => absorptionMass D (PMF.pure i) y)
    (fun i => by rw [abs_of_nonneg (absorptionMass_nonneg D (PMF.pure i) y)]
                 exact absorptionMass_le_one D (PMF.pure i) y)
  rw [← absorptionMass_eq_expect_pureRow] at hle
  exact ⟨i, ENNReal.toReal_pos ((PMF.mem_support_iff x i).mp hi) (x.apply_ne_top i),
    hpositive.trans_le hle⟩

theorem exists_supported_column_positive_hazard (D : Data I J) (x : PMF I) (y : PMF J)
    (hpositive : 0 < absorptionMass D x y) :
    ∃ j, 0 < (y j).toReal ∧ 0 < absorptionMass D x (PMF.pure j) := by
  obtain ⟨j, hj, hle⟩ := exists_mem_support_expect_le y
    (fun j => absorptionMass D x (PMF.pure j))
    (fun j => by rw [abs_of_nonneg (absorptionMass_nonneg D x (PMF.pure j))]
                 exact absorptionMass_le_one D x (PMF.pure j))
  rw [← absorptionMass_eq_expect_pureColumn] at hle
  exact ⟨j, ENNReal.toReal_pos ((PMF.mem_support_iff y j).mp hj) (y.apply_ne_top j),
    hpositive.trans_le hle⟩

omit [Fintype J] in
/-- Recurrent mixed play has zero pure hazard at every supported row. -/
theorem pureRow_mass_eq_zero_of_mixed_mass_eq_zero (D : Data I J) (x : PMF I) (y : PMF J)
    (hzero : absorptionMass D x y = 0) (i : I) (hi : i ∈ x.support) :
    absorptionMass D (PMF.pure i) y = 0 := by
  rw [absorptionMass_eq_expect_pureRow] at hzero
  exact (expect_eq_zero_iff_eq_zero_on_support_of_nonneg_on_support x
    (fun i => absorptionMass D (PMF.pure i) y)
    (fun i _ => absorptionMass_nonneg D (PMF.pure i) y)).mp hzero i hi

theorem pureColumn_mass_eq_zero_of_mixed_mass_eq_zero (D : Data I J)
    (x : PMF I) (y : PMF J) (hzero : absorptionMass D x y = 0)
    (j : J) (hj : j ∈ y.support) : absorptionMass D x (PMF.pure j) = 0 := by
  rw [absorptionMass_eq_expect_pureColumn] at hzero
  exact (expect_eq_zero_iff_eq_zero_on_support_of_nonneg_on_support y
    (fun j => absorptionMass D x (PMF.pure j))
    (fun j _ => absorptionMass_nonneg D x (PMF.pure j))).mp hzero j hj

open Classical in
private theorem badMass_le_card_mul {K : Type} [Fintype K] (weights : K → ℝ)
    (good : Finset K) (ceiling : ℝ) (hceiling : 0 ≤ ceiling)
    (hweights : ∀ k ∉ good, weights k ≤ ceiling) :
    badMass weights good ≤ (Fintype.card K : ℝ) * ceiling := by
  classical
  calc
    badMass weights good ≤ ∑ k ∈ goodᶜ, ceiling :=
      Finset.sum_le_sum fun k hk => hweights k (Finset.mem_compl.mp hk)
    _ ≤ ∑ _k : K, ceiling := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _ _ _ => hceiling)
    _ = (Fintype.card K : ℝ) * ceiling := by simp

/-- Proper row ranking derives bad absorption mass, without a supplied decay certificate. -/
theorem rowBadAbsorptionMass_le_of_deltaProper (D : Data I J) (x : PMF I) (y : PMF J)
    {δ : ℝ} (hproper : IsDeltaProperPair D δ x y) (anchor : I)
    (hhazard : 0 < absorptionMass D (PMF.pure anchor) y)
    (hmax : ∀ i, stationaryPayoff D (PMF.pure i) y false ≤
      stationaryPayoff D (PMF.pure anchor) y false) :
    rowBadAbsorptionMass D x y false anchor ≤
      (Fintype.card I : ℝ) * (δ / absorptionMass D (PMF.pure anchor) y) := by
  classical
  have hsingle : (x anchor).toReal * absorptionMass D (PMF.pure anchor) y ≤
      absorptionMass D x y := by
    calc
      _ = rowAbsorptionWeight D x y anchor := rfl
      _ ≤ ∑ i, rowAbsorptionWeight D x y i :=
        Finset.single_le_sum (fun i _ => rowAbsorptionWeight_nonneg D x y i)
          (Finset.mem_univ anchor)
      _ = absorptionMass D x y := sum_rowAbsorptionWeight D x y
  apply badMass_le_card_mul (rowAbsorptionVector D x y) (rowPayoffLevel D y false anchor)
    (δ / absorptionMass D (PMF.pure anchor) y) (div_nonneg hproper.1.le hhazard.le)
  intro i hi
  have hne : stationaryPayoff D (PMF.pure i) y false ≠
      stationaryPayoff D (PMF.pure anchor) y false := by
    intro hequal
    exact hi (by simp [rowPayoffLevel, hequal])
  have hrank := hproper.row_ranking anchor i (lt_of_le_of_ne (hmax i) hne)
  apply (div_le_iff₀ ((mul_pos (hproper.row_pos anchor) hhazard).trans_le hsingle)).2
  calc
    rowAbsorptionWeight D x y i ≤ (x i).toReal := by
      simpa only [rowAbsorptionWeight, mul_one] using
        mul_le_mul_of_nonneg_left (absorptionMass_le_one D (PMF.pure i) y)
          (ENNReal.toReal_nonneg : 0 ≤ (x i).toReal)
    _ ≤ δ * (x anchor).toReal := hrank
    _ = (δ / absorptionMass D (PMF.pure anchor) y) *
        ((x anchor).toReal * absorptionMass D (PMF.pure anchor) y) := by
      field_simp [hhazard.ne']
    _ ≤ (δ / absorptionMass D (PMF.pure anchor) y) * absorptionMass D x y :=
      mul_le_mul_of_nonneg_left hsingle (div_nonneg hproper.1.le hhazard.le)

/-- The corresponding ranking-derived bad absorption mass bound for columns. -/
theorem columnBadAbsorptionMass_le_of_deltaProper (D : Data I J) (x : PMF I) (y : PMF J)
    {δ : ℝ} (hproper : IsDeltaProperPair D δ x y) (anchor : J)
    (hhazard : 0 < absorptionMass D x (PMF.pure anchor))
    (hmax : ∀ j, stationaryPayoff D x (PMF.pure j) true ≤
      stationaryPayoff D x (PMF.pure anchor) true) :
    columnBadAbsorptionMass D x y true anchor ≤
      (Fintype.card J : ℝ) * (δ / absorptionMass D x (PMF.pure anchor)) := by
  classical
  have hsingle : (y anchor).toReal * absorptionMass D x (PMF.pure anchor) ≤
      absorptionMass D x y := by
    calc
      _ = columnAbsorptionWeight D x y anchor := rfl
      _ ≤ ∑ j, columnAbsorptionWeight D x y j :=
        Finset.single_le_sum (fun j _ => columnAbsorptionWeight_nonneg D x y j)
          (Finset.mem_univ anchor)
      _ = absorptionMass D x y := sum_columnAbsorptionWeight D x y
  apply badMass_le_card_mul (columnAbsorptionVector D x y)
    (columnPayoffLevel D x true anchor) (δ / absorptionMass D x (PMF.pure anchor))
    (div_nonneg hproper.1.le hhazard.le)
  intro j hj
  have hne : stationaryPayoff D x (PMF.pure j) true ≠
      stationaryPayoff D x (PMF.pure anchor) true := by
    intro hequal
    exact hj (by simp [columnPayoffLevel, hequal])
  have hrank := hproper.column_ranking anchor j (lt_of_le_of_ne (hmax j) hne)
  apply (div_le_iff₀ ((mul_pos (hproper.column_pos anchor) hhazard).trans_le hsingle)).2
  calc
    columnAbsorptionWeight D x y j ≤ (y j).toReal := by
      simpa only [columnAbsorptionWeight, mul_one] using
        mul_le_mul_of_nonneg_left (absorptionMass_le_one D x (PMF.pure j))
          (ENNReal.toReal_nonneg : 0 ≤ (y j).toReal)
    _ ≤ δ * (y anchor).toReal := hrank
    _ = (δ / absorptionMass D x (PMF.pure anchor)) *
        ((y anchor).toReal * absorptionMass D x (PMF.pure anchor)) := by
      field_simp [hhazard.ne']
    _ ≤ (δ / absorptionMass D x (PMF.pure anchor)) * absorptionMass D x y :=
      mul_le_mul_of_nonneg_left hsingle (div_nonneg hproper.1.le hhazard.le)

/-- A proper pair supplies actual delta-proper PMFs along one converging sequence. -/
theorem IsProperPair.exists_stationary_sequence {D : Data I J} {x : PMF I} {y : PMF J}
    (hproper : IsProperPair D x y) :
    ∃ (δ : ℕ → ℝ) (xs : ℕ → PMF I) (ys : ℕ → PMF J),
      Tendsto δ atTop (𝓝 0) ∧
      Tendsto (fun n => toVector (xs n)) atTop (𝓝 (toVector x)) ∧
      Tendsto (fun n => toVector (ys n)) atTop (𝓝 (toVector y)) ∧
      ∀ n, IsDeltaProperPair D (δ n) (xs n) (ys n) := by
  rcases hproper with ⟨_, _, δ, rawx, rawy, hδ, hx, hy, hpairs⟩
  let xs := fun n => ofVector (rawx n) (hpairs n).2.2.1
  let ys := fun n => ofVector (rawy n) (hpairs n).2.2.2.1
  refine ⟨δ, xs, ys, hδ, ?_, ?_, ?_⟩
  · simpa only [xs, toVector_ofVector] using hx
  · simpa only [ys, toVector_ofVector] using hy
  · intro n
    simpa only [IsDeltaProperPair, xs, ys, toVector_ofVector] using hpairs n

omit [Fintype I] in
/-- Pure-row hazards converge under actual opponent-coordinate convergence. -/
theorem tendsto_pureRow_absorptionMass (D : Data I J) (ys : ℕ → PMF J) (y : PMF J)
    (hy : Tendsto (fun n => toVector (ys n)) atTop (𝓝 (toVector y))) (i : I) :
    Tendsto (fun n => absorptionMass D (PMF.pure i) (ys n)) atTop
      (𝓝 (absorptionMass D (PMF.pure i) y)) := by
  simpa only [absorptionMass, expect_pure, expect_eq_sum, toVector] using
    (tendsto_finsetSum Finset.univ fun j _ =>
      ((tendsto_pi_nhds.mp hy) j).mul_const (D.absorption i j : ℝ))

omit [Fintype J] in
theorem tendsto_pureColumn_absorptionMass (D : Data I J) (xs : ℕ → PMF I) (x : PMF I)
    (hx : Tendsto (fun n => toVector (xs n)) atTop (𝓝 (toVector x))) (j : J) :
    Tendsto (fun n => absorptionMass D (xs n) (PMF.pure j)) atTop
      (𝓝 (absorptionMass D x (PMF.pure j))) := by
  simpa only [absorptionMass, expect_pure, expect_eq_sum, toVector] using
    (tendsto_finsetSum Finset.univ fun i _ =>
      ((tendsto_pi_nhds.mp hx) i).mul_const (D.absorption i j : ℝ))

omit [Fintype I] in
/-- Pure-row payoff continuity is used only at a positive limiting hazard. -/
theorem tendsto_pureRow_stationaryPayoff (D : Data I J) (ys : ℕ → PMF J) (y : PMF J)
    (hy : Tendsto (fun n => toVector (ys n)) atTop (𝓝 (toVector y)))
    (who : Bool) (i : I) (hpositive : 0 < absorptionMass D (PMF.pure i) y) :
    Tendsto (fun n => stationaryPayoff D (PMF.pure i) (ys n) who) atTop
      (𝓝 (stationaryPayoff D (PMF.pure i) y who)) := by
  have hnum : Tendsto (fun n => absorbingContribution D (PMF.pure i) (ys n) who) atTop
      (𝓝 (absorbingContribution D (PMF.pure i) y who)) := by
    simpa only [absorbingContribution, expect_pure, expect_eq_sum, toVector] using
      (tendsto_finsetSum Finset.univ fun j _ =>
        ((tendsto_pi_nhds.mp hy) j).mul_const
          ((D.absorption i j : ℝ) * D.reward i j who))
  exact hnum.div (tendsto_pureRow_absorptionMass D ys y hy i) hpositive.ne'

omit [Fintype J] in
theorem tendsto_pureColumn_stationaryPayoff (D : Data I J) (xs : ℕ → PMF I) (x : PMF I)
    (hx : Tendsto (fun n => toVector (xs n)) atTop (𝓝 (toVector x)))
    (who : Bool) (j : J) (hpositive : 0 < absorptionMass D x (PMF.pure j)) :
    Tendsto (fun n => stationaryPayoff D (xs n) (PMF.pure j) who) atTop
      (𝓝 (stationaryPayoff D x (PMF.pure j) who)) := by
  have hnum : Tendsto (fun n => absorbingContribution D (xs n) (PMF.pure j) who) atTop
      (𝓝 (absorbingContribution D x (PMF.pure j) who)) := by
    simpa only [absorbingContribution, expect_pure, expect_eq_sum, toVector] using
      (tendsto_finsetSum Finset.univ fun i _ =>
        ((tendsto_pi_nhds.mp hx) i).mul_const
          ((D.absorption i j : ℝ) * D.reward i j who))
  exact hnum.div (tendsto_pureColumn_absorptionMass D xs x hx j) hpositive.ne'

/-- A row coordinate positive in the limit is eventually maximal against the moving opponent.
One eventual event covers every alternative simultaneously. -/
theorem eventually_row_maximal_of_limit_pos (D : Data I J)
    (δ : ℕ → ℝ) (xs : ℕ → PMF I) (ys : ℕ → PMF J) (x : PMF I)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hx : Tendsto (fun n => toVector (xs n)) atTop (𝓝 (toVector x)))
    (hpairs : ∀ n, IsDeltaProperPair D (δ n) (xs n) (ys n))
    (anchor : I) (hanchor : 0 < (x anchor).toReal) :
    ∀ᶠ n in atTop, ∀ i, stationaryPayoff D (PMF.pure i) (ys n) false ≤
      stationaryPayoff D (PMF.pure anchor) (ys n) false := by
  have hcoordinate := hδ.eventually_lt ((tendsto_pi_nhds.mp hx) anchor) hanchor
  filter_upwards [hcoordinate] with n hn
  intro i
  by_contra hnot
  have hrank := (hpairs n).row_ranking i anchor (lt_of_not_ge hnot)
  have hprobability : (xs n i).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono (by simp) (PMF.coe_le_one (xs n) i)
  exact (not_le_of_gt hn) (hrank.trans
    (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hprobability (hpairs n).1.le))

/-- The same simultaneous eventual maximality for a limiting supported column. -/
theorem eventually_column_maximal_of_limit_pos (D : Data I J)
    (δ : ℕ → ℝ) (xs : ℕ → PMF I) (ys : ℕ → PMF J) (y : PMF J)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hy : Tendsto (fun n => toVector (ys n)) atTop (𝓝 (toVector y)))
    (hpairs : ∀ n, IsDeltaProperPair D (δ n) (xs n) (ys n))
    (anchor : J) (hanchor : 0 < (y anchor).toReal) :
    ∀ᶠ n in atTop, ∀ j, stationaryPayoff D (xs n) (PMF.pure j) true ≤
      stationaryPayoff D (xs n) (PMF.pure anchor) true := by
  have hcoordinate := hδ.eventually_lt ((tendsto_pi_nhds.mp hy) anchor) hanchor
  filter_upwards [hcoordinate] with n hn
  intro j
  by_contra hnot
  have hrank := (hpairs n).column_ranking j anchor (lt_of_not_ge hnot)
  have hprobability : (ys n j).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono (by simp) (PMF.coe_le_one (ys n) j)
  exact (not_le_of_gt hn) (hrank.trans
    (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hprobability (hpairs n).1.le))

/-- The row payoff error is derived from proper ranking and the actual absorption law. -/
theorem abs_rowPayoff_gap_le_of_deltaProper (D : Data I J) (x : PMF I) (y : PMF J)
    {δ : ℝ} (hproper : IsDeltaProperPair D δ x y) (anchor : I) (bound : ℝ)
    (hhazard : 0 < absorptionMass D (PMF.pure anchor) y)
    (hmax : ∀ i, stationaryPayoff D (PMF.pure i) y false ≤
      stationaryPayoff D (PMF.pure anchor) y false)
    (hbound : ∀ i j, |D.reward i j false| ≤ bound) :
    |stationaryPayoff D x y false - stationaryPayoff D (PMF.pure anchor) y false| ≤
      (2 * bound) * (Fintype.card I : ℝ) * (δ / absorptionMass D (PMF.pure anchor) y) := by
  have hpositive : 0 < absorptionMass D x y := by
    apply (mul_pos (hproper.row_pos anchor) hhazard).trans_le
    calc
      _ = rowAbsorptionWeight D x y anchor := rfl
      _ ≤ ∑ i, rowAbsorptionWeight D x y i :=
        Finset.single_le_sum (fun i _ => rowAbsorptionWeight_nonneg D x y i)
          (Finset.mem_univ anchor)
      _ = absorptionMass D x y := sum_rowAbsorptionWeight D x y
  have hbound0 : 0 ≤ bound :=
    (abs_nonneg _).trans (abs_stationaryPayoff_le D x y false bound hbound)
  calc
    _ ≤ (2 * bound) * rowBadAbsorptionMass D x y false anchor :=
      abs_stationaryPayoff_sub_pureRow_le D x y false anchor bound hpositive hbound
    _ ≤ (2 * bound) * ((Fintype.card I : ℝ) *
        (δ / absorptionMass D (PMF.pure anchor) y)) :=
      mul_le_mul_of_nonneg_left
        (rowBadAbsorptionMass_le_of_deltaProper D x y hproper anchor hhazard hmax)
        (mul_nonneg (by norm_num) hbound0)
    _ = _ := (mul_assoc _ _ _).symm

theorem abs_columnPayoff_gap_le_of_deltaProper (D : Data I J) (x : PMF I) (y : PMF J)
    {δ : ℝ} (hproper : IsDeltaProperPair D δ x y) (anchor : J) (bound : ℝ)
    (hhazard : 0 < absorptionMass D x (PMF.pure anchor))
    (hmax : ∀ j, stationaryPayoff D x (PMF.pure j) true ≤
      stationaryPayoff D x (PMF.pure anchor) true)
    (hbound : ∀ i j, |D.reward i j true| ≤ bound) :
    |stationaryPayoff D x y true - stationaryPayoff D x (PMF.pure anchor) true| ≤
      (2 * bound) * (Fintype.card J : ℝ) * (δ / absorptionMass D x (PMF.pure anchor)) := by
  have hpositive : 0 < absorptionMass D x y := by
    apply (mul_pos (hproper.column_pos anchor) hhazard).trans_le
    calc
      _ = columnAbsorptionWeight D x y anchor := rfl
      _ ≤ ∑ j, columnAbsorptionWeight D x y j :=
        Finset.single_le_sum (fun j _ => columnAbsorptionWeight_nonneg D x y j)
          (Finset.mem_univ anchor)
      _ = absorptionMass D x y := sum_columnAbsorptionWeight D x y
  have hbound0 : 0 ≤ bound :=
    (abs_nonneg _).trans (abs_stationaryPayoff_le D x y true bound hbound)
  calc
    _ ≤ (2 * bound) * columnBadAbsorptionMass D x y true anchor :=
      abs_stationaryPayoff_sub_pureColumn_le D x y true anchor bound hpositive hbound
    _ ≤ (2 * bound) * ((Fintype.card J : ℝ) *
        (δ / absorptionMass D x (PMF.pure anchor))) :=
      mul_le_mul_of_nonneg_left
        (columnBadAbsorptionMass_le_of_deltaProper D x y hproper anchor hhazard hmax)
        (mul_nonneg (by norm_num) hbound0)
    _ = _ := (mul_assoc _ _ _).symm

private theorem pureStationaryResponsePayoff_row (D : Data I J)
    (x : PMF I) (y : PMF J) (i : I) :
    pureStationaryResponsePayoff D (mixedAction x y) false i =
      stationaryPayoff D (PMF.pure i) y false := by
  change liminfPayoff D none ((game D).stationaryBehaviorProfile
    (Function.update (mixedAction x y) false (PMF.pure i))) false = _
  calc
    _ = stationaryPayoff D
        ((Function.update (mixedAction x y) false (PMF.pure i)) false)
        ((Function.update (mixedAction x y) false (PMF.pure i)) true) false :=
      liminfPayoff_stationaryActions_none D
        (Function.update (mixedAction x y) false (PMF.pure i)) false
    _ = _ := by simp only [Function.update_self,
      Function.update_of_ne (by decide : true ≠ false), mixedAction]

private theorem pureStationaryResponsePayoff_column (D : Data I J)
    (x : PMF I) (y : PMF J) (j : J) :
    pureStationaryResponsePayoff D (mixedAction x y) true j =
      stationaryPayoff D x (PMF.pure j) true := by
  change liminfPayoff D none ((game D).stationaryBehaviorProfile
    (Function.update (mixedAction x y) true (PMF.pure j))) true = _
  calc
    _ = stationaryPayoff D
        ((Function.update (mixedAction x y) true (PMF.pure j)) false)
        ((Function.update (mixedAction x y) true (PMF.pure j)) true) true :=
      liminfPayoff_stationaryActions_none D
        (Function.update (mixedAction x y) true (PMF.pure j)) true
    _ = _ := by simp only [Function.update_self,
      Function.update_of_ne (by decide : false ≠ true), mixedAction]

/-- Actual unrestricted row deviations obey any bound on all actual pure stationary payoffs. -/
theorem behavioral_rowPayoff_le_of_pure_cap (D : Data I J) (x : PMF I) (y : PMF J)
    (ceiling : ℝ) (hcap : ∀ i, stationaryPayoff D (PMF.pure i) y false ≤ ceiling)
    (deviation : (game D).BehaviorStrategy false) :
    liminfPayoff D none (Function.update (stationaryProfile D x y) false deviation) false ≤
      ceiling := by
  obtain ⟨i, hi⟩ := exists_pure_stationary_bestResponse D (mixedAction x y) false
  exact (hi deviation none).trans
    (by change pureStationaryResponsePayoff D (mixedAction x y) false i ≤ ceiling
        rw [pureStationaryResponsePayoff_row]
        exact hcap i)

theorem behavioral_columnPayoff_le_of_pure_cap (D : Data I J) (x : PMF I) (y : PMF J)
    (ceiling : ℝ) (hcap : ∀ j, stationaryPayoff D x (PMF.pure j) true ≤ ceiling)
    (deviation : (game D).BehaviorStrategy true) :
    liminfPayoff D none (Function.update (stationaryProfile D x y) true deviation) true ≤
      ceiling := by
  obtain ⟨j, hj⟩ := exists_pure_stationary_bestResponse D (mixedAction x y) true
  exact (hj deviation none).trans
    (by change pureStationaryResponsePayoff D (mixedAction x y) true j ≤ ceiling
        rw [pureStationaryResponsePayoff_column]
        exact hcap j)

end GameTheory.RecursiveAbsorption
