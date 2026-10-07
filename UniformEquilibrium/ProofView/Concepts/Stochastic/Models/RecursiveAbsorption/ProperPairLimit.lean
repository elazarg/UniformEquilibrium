import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.RecursiveAbsorption.ProperPairApproximation
import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Asymptotic

/-!
# Proper-pair limits in the canonical recursive absorption model

The absorbing-limit argument of Flesch, Thuijsman and Vrieze (1996),
Theorem 3.1, uses actual stationary PMFs, internally selected positive-hazard
anchors, and the checked proper-ranking error estimates. Both players' errors
are controlled along one sequence and then compiled to the actual unrestricted
behavioral deviation inequalities at every initial state.

The recurrent cases keep the limiting opponent fixed, derive bad absorption
mass from strict rankings against the moving opponent, and retain zero-hazard
actions without dividing by their hazards. The final producer chooses the
actual proper pair, sequence, and limiting case internally. The original
paper's reduction from general absorbing stage games and state-dependent
action sets remains a separate obligation. This module does not identify this
canonical model with that source class or assert a fixed-target
uniform-equilibrium payoff.
-/

noncomputable section

open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open _root_.Math.Probability.FiniteLawRepair
open Filter
open scoped BigOperators Topology

namespace GameTheory.RecursiveAbsorption

variable {I J : Type} [Fintype I] [Fintype J]

private theorem isAsymptoticNash_of_pure_gaps (D : Data I J) (x : PMF I) (y : PMF J)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hrow : ∀ i, stationaryPayoff D (PMF.pure i) y false ≤ stationaryPayoff D x y false + ε)
    (hcolumn : ∀ j, stationaryPayoff D x (PMF.pure j) true ≤ stationaryPayoff D x y true + ε) :
    ∀ initial, (game D).IsεAsymptoticNash (liminfPayoff D initial) ε
      (stationaryProfile D x y) := by
  intro initial who deviation
  cases initial with
  | none =>
      cases who with
      | false =>
          calc
            _ ≤ stationaryPayoff D x y false + ε :=
              behavioral_rowPayoff_le_of_pure_cap D x y _ hrow deviation
            _ = _ := congrArg (fun value => value + ε)
              (liminfPayoff_stationary_none D x y false).symm
      | true =>
          calc
            _ ≤ stationaryPayoff D x y true + ε :=
              behavioral_columnPayoff_le_of_pure_cap D x y _ hcolumn deviation
            _ = _ := congrArg (fun value => value + ε)
              (liminfPayoff_stationary_none D x y true).symm
  | some pair =>
      calc
        _ = D.reward pair.1 pair.2 who := liminfPayoff_some D
          (Function.update (stationaryProfile D x y) who deviation) pair who
        _ ≤ D.reward pair.1 pair.2 who + ε := le_add_of_nonneg_right hε
        _ = _ := congrArg (fun value => value + ε)
          (liminfPayoff_some D (stationaryProfile D x y) pair who).symm

private theorem eventually_row_gaps_of_positive_anchor (D : Data I J)
    (δ : ℕ → ℝ) (xs : ℕ → PMF I) (ys : ℕ → PMF J) (x : PMF I) (y : PMF J)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hx : Tendsto (fun n => toVector (xs n)) atTop (𝓝 (toVector x)))
    (hy : Tendsto (fun n => toVector (ys n)) atTop (𝓝 (toVector y)))
    (hpairs : ∀ n, IsDeltaProperPair D (δ n) (xs n) (ys n))
    (anchor : I) (hcoordinate : 0 < (x anchor).toReal)
    (hhazard : 0 < absorptionMass D (PMF.pure anchor) y)
    (bound : ℝ) (hbound : ∀ i j, |D.reward i j false| ≤ bound)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ i, stationaryPayoff D (PMF.pure i) (ys n) false ≤
      stationaryPayoff D (xs n) (ys n) false + ε := by
  have hmax := eventually_row_maximal_of_limit_pos D δ xs ys x hδ hx hpairs anchor hcoordinate
  have hmass := tendsto_pureRow_absorptionMass D ys y hy anchor
  have hrate : Tendsto (fun n => (2 * bound) * (Fintype.card I : ℝ) *
      (δ n / absorptionMass D (PMF.pure anchor) (ys n))) atTop (𝓝 0) := by
    simpa only [Pi.div_apply, zero_div, mul_zero] using
      (hδ.div hmass hhazard.ne').const_mul ((2 * bound) * (Fintype.card I : ℝ))
  filter_upwards [hmax, hmass.eventually_const_lt hhazard, hrate.eventually_lt_const hε]
    with n hnmax hnhazard hnrate
  intro i
  have hgap := abs_rowPayoff_gap_le_of_deltaProper D (xs n) (ys n)
    (hpairs n) anchor bound hnhazard hnmax hbound
  have hlower := (abs_le.mp hgap).1
  linarith [hnmax i]

private theorem eventually_column_gaps_of_positive_anchor (D : Data I J)
    (δ : ℕ → ℝ) (xs : ℕ → PMF I) (ys : ℕ → PMF J) (x : PMF I) (y : PMF J)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hx : Tendsto (fun n => toVector (xs n)) atTop (𝓝 (toVector x)))
    (hy : Tendsto (fun n => toVector (ys n)) atTop (𝓝 (toVector y)))
    (hpairs : ∀ n, IsDeltaProperPair D (δ n) (xs n) (ys n))
    (anchor : J) (hcoordinate : 0 < (y anchor).toReal)
    (hhazard : 0 < absorptionMass D x (PMF.pure anchor))
    (bound : ℝ) (hbound : ∀ i j, |D.reward i j true| ≤ bound)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ j, stationaryPayoff D (xs n) (PMF.pure j) true ≤
      stationaryPayoff D (xs n) (ys n) true + ε := by
  have hmax := eventually_column_maximal_of_limit_pos D δ xs ys y hδ hy hpairs anchor hcoordinate
  have hmass := tendsto_pureColumn_absorptionMass D xs x hx anchor
  have hrate : Tendsto (fun n => (2 * bound) * (Fintype.card J : ℝ) *
      (δ n / absorptionMass D (xs n) (PMF.pure anchor))) atTop (𝓝 0) := by
    simpa only [Pi.div_apply, zero_div, mul_zero] using
      (hδ.div hmass hhazard.ne').const_mul ((2 * bound) * (Fintype.card J : ℝ))
  filter_upwards [hmax, hmass.eventually_const_lt hhazard, hrate.eventually_lt_const hε]
    with n hnmax hnhazard hnrate
  intro j
  have hgap := abs_columnPayoff_gap_le_of_deltaProper D (xs n) (ys n)
    (hpairs n) anchor bound hnhazard hnmax hbound
  have hlower := (abs_le.mp hgap).1
  linarith [hnmax j]

/-- The absorbing proper-limit case produces one eventual profile for both players,
every behavioral deviation, and every initial state of the actual canonical game. -/
theorem eventually_isAsymptoticNash_of_absorbing_proper_limit (D : Data I J)
    (δ : ℕ → ℝ) (xs : ℕ → PMF I) (ys : ℕ → PMF J) (x : PMF I) (y : PMF J)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hx : Tendsto (fun n => toVector (xs n)) atTop (𝓝 (toVector x)))
    (hy : Tendsto (fun n => toVector (ys n)) atTop (𝓝 (toVector y)))
    (hpairs : ∀ n, IsDeltaProperPair D (δ n) (xs n) (ys n))
    (hpositive : 0 < absorptionMass D x y) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ initial,
      (game D).IsεAsymptoticNash (liminfPayoff D initial) ε
        (stationaryProfile D (xs n) (ys n)) := by
  obtain ⟨row, hrowpos, hrowhazard⟩ := exists_supported_row_positive_hazard D x y hpositive
  obtain ⟨column, hcolumnpos, hcolumnhazard⟩ :=
    exists_supported_column_positive_hazard D x y hpositive
  obtain ⟨bound, hbound⟩ := exists_abs_bound_of_finite
    (fun triple : I × J × Bool => D.reward triple.1 triple.2.1 triple.2.2)
  have hrows := eventually_row_gaps_of_positive_anchor D δ xs ys x y hδ hx hy hpairs
    row hrowpos hrowhazard bound (fun i j => hbound (i, j, false)) hε
  have hcolumns := eventually_column_gaps_of_positive_anchor D δ xs ys x y hδ hx hy hpairs
    column hcolumnpos hcolumnhazard bound (fun i j => hbound (i, j, true)) hε
  filter_upwards [hrows, hcolumns] with n hnrow hncolumn
  exact isAsymptoticNash_of_pure_gaps D (xs n) (ys n) hε.le hnrow hncolumn

private theorem stationaryPayoff_eq_zero_of_mass_eq_zero (D : Data I J)
    (x : PMF I) (y : PMF J) (who : Bool) (hzero : absorptionMass D x y = 0) :
    stationaryPayoff D x y who = 0 := by
  unfold stationaryPayoff
  rw [absorbingContribution_eq_zero_of_mass_eq_zero D x y who hzero, zero_div]

omit [Fintype J] in
private theorem absorptionMass_pos_of_row_hazard (D : Data I J) (x : PMF I) (y : PMF J)
    (anchor : I) (hcoordinate : 0 < (x anchor).toReal)
    (hhazard : 0 < absorptionMass D (PMF.pure anchor) y) : 0 < absorptionMass D x y := by
  have hpositive := expect_lt_of_le_of_exists_lt x (fun _ => 0)
    (fun i => absorptionMass D (PMF.pure i) y)
    (fun i => absorptionMass_nonneg D (PMF.pure i) y)
    ⟨anchor, (toVector_pos_iff_ne_zero x anchor).mp hcoordinate, hhazard⟩
  simpa only [expect_const, ← absorptionMass_eq_expect_pureRow] using hpositive

private theorem absorptionMass_pos_of_column_hazard (D : Data I J)
    (x : PMF I) (y : PMF J) (anchor : J) (hcoordinate : 0 < (y anchor).toReal)
    (hhazard : 0 < absorptionMass D x (PMF.pure anchor)) : 0 < absorptionMass D x y := by
  have hpositive := expect_lt_of_le_of_exists_lt y (fun _ => 0)
    (fun j => absorptionMass D x (PMF.pure j))
    (fun j => absorptionMass_nonneg D x (PMF.pure j))
    ⟨anchor, (toVector_pos_iff_ne_zero y anchor).mp hcoordinate, hhazard⟩
  simpa only [expect_const, ← absorptionMass_eq_expect_pureColumn] using hpositive

private theorem abs_rowPayoff_gap_le_of_bad_probabilities (D : Data I J)
    (x : PMF I) (y : PMF J) (δ : ℝ) (anchor : I) (bound : ℝ)
    (hδ : 0 ≤ δ) (hpositive : 0 < absorptionMass D x y)
    (hhazard : 0 < absorptionMass D (PMF.pure anchor) y)
    (hbad : ∀ i, 0 < absorptionMass D (PMF.pure i) y →
      stationaryPayoff D (PMF.pure i) y false ≠ stationaryPayoff D (PMF.pure anchor) y false →
      (x i).toReal ≤ δ * (x anchor).toReal)
    (hbound : ∀ i j, |D.reward i j false| ≤ bound) :
    |stationaryPayoff D x y false - stationaryPayoff D (PMF.pure anchor) y false| ≤
      (2 * bound) * (Fintype.card I : ℝ) * (δ / absorptionMass D (PMF.pure anchor) y) := by
  classical
  have hsingle : rowAbsorptionWeight D x y anchor ≤ absorptionMass D x y :=
    (Finset.single_le_sum (fun i _ => rowAbsorptionWeight_nonneg D x y i)
      (Finset.mem_univ anchor)).trans_eq (sum_rowAbsorptionWeight D x y)
  have hpoint : ∀ i ∈ (rowPayoffLevel D y false anchor)ᶜ,
      rowAbsorptionVector D x y i ≤ δ / absorptionMass D (PMF.pure anchor) y := by
    intro i hi
    by_cases hzero : absorptionMass D (PMF.pure i) y = 0
    · simp only [rowAbsorptionVector, rowAbsorptionWeight, hzero, mul_zero, zero_div]
      exact div_nonneg hδ hhazard.le
    · have hne : stationaryPayoff D (PMF.pure i) y false ≠
          stationaryPayoff D (PMF.pure anchor) y false := by
        intro hequal
        exact (Finset.mem_compl.mp hi) (by simp [rowPayoffLevel, hequal])
      have hrank := hbad i
        (lt_of_le_of_ne (absorptionMass_nonneg D (PMF.pure i) y) (Ne.symm hzero)) hne
      apply (div_le_iff₀ hpositive).2
      calc
        rowAbsorptionWeight D x y i ≤ (x i).toReal := by
          simpa only [rowAbsorptionWeight, mul_one] using
            mul_le_mul_of_nonneg_left (absorptionMass_le_one D (PMF.pure i) y)
              (ENNReal.toReal_nonneg : 0 ≤ (x i).toReal)
        _ ≤ δ * (x anchor).toReal := hrank
        _ = (δ / absorptionMass D (PMF.pure anchor) y) * rowAbsorptionWeight D x y anchor := by
          unfold rowAbsorptionWeight
          field_simp [hhazard.ne']
        _ ≤ (δ / absorptionMass D (PMF.pure anchor) y) * absorptionMass D x y :=
          mul_le_mul_of_nonneg_left hsingle (div_nonneg hδ hhazard.le)
  have hbadmass : rowBadAbsorptionMass D x y false anchor ≤
      (Fintype.card I : ℝ) * (δ / absorptionMass D (PMF.pure anchor) y) := by
    have hsum := Finset.sum_le_card_nsmul (rowPayoffLevel D y false anchor)ᶜ
      (rowAbsorptionVector D x y) (δ / absorptionMass D (PMF.pure anchor) y) hpoint
    have hcard : (((rowPayoffLevel D y false anchor)ᶜ).card : ℝ) ≤ Fintype.card I := by
      exact_mod_cast Finset.card_le_card
        (Finset.subset_univ ((rowPayoffLevel D y false anchor)ᶜ))
    have hfirst : rowBadAbsorptionMass D x y false anchor ≤
        (((rowPayoffLevel D y false anchor)ᶜ).card : ℝ) *
          (δ / absorptionMass D (PMF.pure anchor) y) := by
      simpa only [rowBadAbsorptionMass, badMass, nsmul_eq_mul] using hsum
    exact hfirst.trans
      (mul_le_mul_of_nonneg_right hcard (div_nonneg hδ hhazard.le))
  have hbound0 : 0 ≤ bound :=
    (abs_nonneg _).trans (abs_stationaryPayoff_le D x y false bound hbound)
  calc
    _ ≤ (2 * bound) * rowBadAbsorptionMass D x y false anchor :=
      abs_stationaryPayoff_sub_pureRow_le D x y false anchor bound hpositive hbound
    _ ≤ (2 * bound) * ((Fintype.card I : ℝ) *
        (δ / absorptionMass D (PMF.pure anchor) y)) :=
      mul_le_mul_of_nonneg_left hbadmass (mul_nonneg (by norm_num) hbound0)
    _ = _ := (mul_assoc _ _ _).symm

private theorem abs_columnPayoff_gap_le_of_bad_probabilities (D : Data I J)
    (x : PMF I) (y : PMF J) (δ : ℝ) (anchor : J) (bound : ℝ)
    (hδ : 0 ≤ δ) (hpositive : 0 < absorptionMass D x y)
    (hhazard : 0 < absorptionMass D x (PMF.pure anchor))
    (hbad : ∀ j, 0 < absorptionMass D x (PMF.pure j) →
      stationaryPayoff D x (PMF.pure j) true ≠ stationaryPayoff D x (PMF.pure anchor) true →
      (y j).toReal ≤ δ * (y anchor).toReal)
    (hbound : ∀ i j, |D.reward i j true| ≤ bound) :
    |stationaryPayoff D x y true - stationaryPayoff D x (PMF.pure anchor) true| ≤
      (2 * bound) * (Fintype.card J : ℝ) * (δ / absorptionMass D x (PMF.pure anchor)) := by
  classical
  have hsingle : columnAbsorptionWeight D x y anchor ≤ absorptionMass D x y :=
    (Finset.single_le_sum (fun j _ => columnAbsorptionWeight_nonneg D x y j)
      (Finset.mem_univ anchor)).trans_eq (sum_columnAbsorptionWeight D x y)
  have hpoint : ∀ j ∈ (columnPayoffLevel D x true anchor)ᶜ,
      columnAbsorptionVector D x y j ≤ δ / absorptionMass D x (PMF.pure anchor) := by
    intro j hj
    by_cases hzero : absorptionMass D x (PMF.pure j) = 0
    · simp only [columnAbsorptionVector, columnAbsorptionWeight, hzero, mul_zero, zero_div]
      exact div_nonneg hδ hhazard.le
    · have hne : stationaryPayoff D x (PMF.pure j) true ≠
          stationaryPayoff D x (PMF.pure anchor) true := by
        intro hequal
        exact (Finset.mem_compl.mp hj) (by simp [columnPayoffLevel, hequal])
      have hrank := hbad j
        (lt_of_le_of_ne (absorptionMass_nonneg D x (PMF.pure j)) (Ne.symm hzero)) hne
      apply (div_le_iff₀ hpositive).2
      calc
        columnAbsorptionWeight D x y j ≤ (y j).toReal := by
          simpa only [columnAbsorptionWeight, mul_one] using
            mul_le_mul_of_nonneg_left (absorptionMass_le_one D x (PMF.pure j))
              (ENNReal.toReal_nonneg : 0 ≤ (y j).toReal)
        _ ≤ δ * (y anchor).toReal := hrank
        _ = (δ / absorptionMass D x (PMF.pure anchor)) * columnAbsorptionWeight D x y anchor := by
          unfold columnAbsorptionWeight
          field_simp [hhazard.ne']
        _ ≤ (δ / absorptionMass D x (PMF.pure anchor)) * absorptionMass D x y :=
          mul_le_mul_of_nonneg_left hsingle (div_nonneg hδ hhazard.le)
  have hbadmass : columnBadAbsorptionMass D x y true anchor ≤
      (Fintype.card J : ℝ) * (δ / absorptionMass D x (PMF.pure anchor)) := by
    have hsum := Finset.sum_le_card_nsmul (columnPayoffLevel D x true anchor)ᶜ
      (columnAbsorptionVector D x y) (δ / absorptionMass D x (PMF.pure anchor)) hpoint
    have hcard : (((columnPayoffLevel D x true anchor)ᶜ).card : ℝ) ≤ Fintype.card J := by
      exact_mod_cast Finset.card_le_card
        (Finset.subset_univ ((columnPayoffLevel D x true anchor)ᶜ))
    have hfirst : columnBadAbsorptionMass D x y true anchor ≤
        (((columnPayoffLevel D x true anchor)ᶜ).card : ℝ) *
          (δ / absorptionMass D x (PMF.pure anchor)) := by
      simpa only [columnBadAbsorptionMass, badMass, nsmul_eq_mul] using hsum
    exact hfirst.trans
      (mul_le_mul_of_nonneg_right hcard (div_nonneg hδ hhazard.le))
  have hbound0 : 0 ≤ bound :=
    (abs_nonneg _).trans (abs_stationaryPayoff_le D x y true bound hbound)
  calc
    _ ≤ (2 * bound) * columnBadAbsorptionMass D x y true anchor :=
      abs_stationaryPayoff_sub_pureColumn_le D x y true anchor bound hpositive hbound
    _ ≤ (2 * bound) * ((Fintype.card J : ℝ) *
        (δ / absorptionMass D x (PMF.pure anchor))) :=
      mul_le_mul_of_nonneg_left hbadmass (mul_nonneg (by norm_num) hbound0)
    _ = _ := (mul_assoc _ _ _).symm

omit [Fintype J] in
private theorem rowAbsorptionLaw_support_subset (D : Data I J) (x : PMF I) (y : PMF J)
    (hpositive : 0 < absorptionMass D x y) : (rowAbsorptionLaw D x y hpositive).support ⊆
      x.support := by
  intro i hi
  have hne := (PMF.mem_support_iff (rowAbsorptionLaw D x y hpositive) i).mp hi
  have hweight := (ofVector_ne_zero_iff
    (rowAbsorptionVector_mem_simplexWeights D x y hpositive) i).mp hne
  apply (PMF.mem_support_iff x i).mpr
  intro hzero
  simp only [rowAbsorptionVector, rowAbsorptionWeight, hzero,
    ENNReal.toReal_zero, zero_mul, zero_div] at hweight
  exact (lt_irrefl 0) hweight

private theorem columnAbsorptionLaw_support_subset (D : Data I J) (x : PMF I) (y : PMF J)
    (hpositive : 0 < absorptionMass D x y) : (columnAbsorptionLaw D x y hpositive).support ⊆
      y.support := by
  intro j hj
  have hne := (PMF.mem_support_iff (columnAbsorptionLaw D x y hpositive) j).mp hj
  have hweight := (ofVector_ne_zero_iff
    (columnAbsorptionVector_mem_simplexWeights D x y hpositive) j).mp hne
  apply (PMF.mem_support_iff y j).mpr
  intro hzero
  simp only [columnAbsorptionVector, columnAbsorptionWeight, hzero,
    ENNReal.toReal_zero, zero_mul, zero_div] at hweight
  exact (lt_irrefl 0) hweight

private theorem pureRow_le_mixed_of_supported_max (D : Data I J) (x : PMF I) (y : PMF J)
    (hmax : ∀ i ∈ x.support, ∀ other, stationaryPayoff D (PMF.pure other) y false ≤
      stationaryPayoff D (PMF.pure i) y false) :
    ∀ i, stationaryPayoff D (PMF.pure i) y false ≤ stationaryPayoff D x y false := by
  obtain ⟨anchor, hanchor⟩ := x.support_nonempty
  by_cases hzero : absorptionMass D x y = 0
  · have hanchorzero := stationaryPayoff_eq_zero_of_mass_eq_zero D (PMF.pure anchor) y false
      (pureRow_mass_eq_zero_of_mixed_mass_eq_zero D x y hzero anchor hanchor)
    have hmixedzero := stationaryPayoff_eq_zero_of_mass_eq_zero D x y false hzero
    intro i
    exact (hmax anchor hanchor i).trans_eq (hanchorzero.trans hmixedzero.symm)
  · have hpositive := lt_of_le_of_ne (absorptionMass_nonneg D x y) (Ne.symm hzero)
    have hvalue : expect (rowAbsorptionLaw D x y hpositive)
        (fun i => stationaryPayoff D (PMF.pure i) y false) =
          stationaryPayoff D (PMF.pure anchor) y false := by
      calc
        _ = expect (rowAbsorptionLaw D x y hpositive)
            (fun _ => stationaryPayoff D (PMF.pure anchor) y false) := by
          apply expect_congr_on_support
          intro i hi
          have hsupport := rowAbsorptionLaw_support_subset D x y hpositive hi
          exact le_antisymm (hmax anchor hanchor i) (hmax i hsupport anchor)
        _ = _ := expect_const _ _
    have hmixed := (expect_rowAbsorptionLaw_purePayoff D x y false hpositive).symm.trans hvalue
    intro i
    exact (hmax anchor hanchor i).trans_eq hmixed.symm

private theorem pureColumn_le_mixed_of_supported_max (D : Data I J) (x : PMF I) (y : PMF J)
    (hmax : ∀ j ∈ y.support, ∀ other, stationaryPayoff D x (PMF.pure other) true ≤
      stationaryPayoff D x (PMF.pure j) true) :
    ∀ j, stationaryPayoff D x (PMF.pure j) true ≤ stationaryPayoff D x y true := by
  obtain ⟨anchor, hanchor⟩ := y.support_nonempty
  by_cases hzero : absorptionMass D x y = 0
  · have hanchorzero := stationaryPayoff_eq_zero_of_mass_eq_zero D x (PMF.pure anchor) true
      (pureColumn_mass_eq_zero_of_mixed_mass_eq_zero D x y hzero anchor hanchor)
    have hmixedzero := stationaryPayoff_eq_zero_of_mass_eq_zero D x y true hzero
    intro j
    exact (hmax anchor hanchor j).trans_eq (hanchorzero.trans hmixedzero.symm)
  · have hpositive := lt_of_le_of_ne (absorptionMass_nonneg D x y) (Ne.symm hzero)
    have hvalue : expect (columnAbsorptionLaw D x y hpositive)
        (fun j => stationaryPayoff D x (PMF.pure j) true) =
          stationaryPayoff D x (PMF.pure anchor) true := by
      calc
        _ = expect (columnAbsorptionLaw D x y hpositive)
            (fun _ => stationaryPayoff D x (PMF.pure anchor) true) := by
          apply expect_congr_on_support
          intro j hj
          have hsupport := columnAbsorptionLaw_support_subset D x y hpositive hj
          exact le_antisymm (hmax anchor hanchor j) (hmax j hsupport anchor)
        _ = _ := expect_const _ _
    have hmixed := (expect_columnAbsorptionLaw_purePayoff D x y true hpositive).symm.trans hvalue
    intro j
    exact (hmax anchor hanchor j).trans_eq hmixed.symm

private theorem eventually_isAsymptoticNash_of_profitable_row_limit (D : Data I J)
    (δ : ℕ → ℝ) (xs : ℕ → PMF I) (ys : ℕ → PMF J) (y : PMF J)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hy : Tendsto (fun n => toVector (ys n)) atTop (𝓝 (toVector y)))
    (hpairs : ∀ n, IsDeltaProperPair D (δ n) (xs n) (ys n)) (anchor : I)
    (hmax : ∀ i, stationaryPayoff D (PMF.pure i) y false ≤
      stationaryPayoff D (PMF.pure anchor) y false)
    (hprofit : 0 < stationaryPayoff D (PMF.pure anchor) y false) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ initial,
      (game D).IsεAsymptoticNash (liminfPayoff D initial) ε (stationaryProfile D (xs n) y) := by
  have hhazard : 0 < absorptionMass D (PMF.pure anchor) y := by
    by_contra hnot
    have hzero := le_antisymm (le_of_not_gt hnot) (absorptionMass_nonneg D (PMF.pure anchor) y)
    exact hprofit.ne' (stationaryPayoff_eq_zero_of_mass_eq_zero D (PMF.pure anchor) y false hzero)
  have hbad : ∀ᶠ n in atTop, ∀ i, 0 < absorptionMass D (PMF.pure i) y →
      stationaryPayoff D (PMF.pure i) y false ≠ stationaryPayoff D (PMF.pure anchor) y false →
      (xs n i).toReal ≤ δ n * (xs n anchor).toReal := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hconditions : 0 < absorptionMass D (PMF.pure i) y ∧
        stationaryPayoff D (PMF.pure i) y false ≠ stationaryPayoff D (PMF.pure anchor) y false
    · have hstrict := lt_of_le_of_ne (hmax i) hconditions.2
      have hi := tendsto_pureRow_stationaryPayoff D ys y hy false i hconditions.1
      have ha := tendsto_pureRow_stationaryPayoff D ys y hy false anchor hhazard
      filter_upwards [hi.eventually_lt ha hstrict] with n hn
      intro _ _
      exact (hpairs n).row_ranking anchor i hn
    · exact Eventually.of_forall fun n hpositive hne =>
        False.elim (hconditions ⟨hpositive, hne⟩)
  have hcolumns : ∀ᶠ n in atTop, ∀ j ∈ y.support, ∀ other,
      stationaryPayoff D (xs n) (PMF.pure other) true ≤
        stationaryPayoff D (xs n) (PMF.pure j) true := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j ∈ y.support
    · have hpos := ENNReal.toReal_pos ((PMF.mem_support_iff y j).mp hj) (y.apply_ne_top j)
      exact (eventually_column_maximal_of_limit_pos D δ xs ys y hδ hy hpairs j hpos).mono
        (fun n hn _ => hn)
    · exact Eventually.of_forall fun n hsupport => False.elim (hj hsupport)
  obtain ⟨bound, hbound⟩ := exists_abs_bound_of_finite
    (fun pair : I × J => D.reward pair.1 pair.2 false)
  have hrate : Tendsto (fun n => (2 * bound) * (Fintype.card I : ℝ) *
      (δ n / absorptionMass D (PMF.pure anchor) y)) atTop (𝓝 0) := by
    simpa only [Pi.div_apply, zero_div, mul_zero] using
      (hδ.div tendsto_const_nhds hhazard.ne').const_mul ((2 * bound) * (Fintype.card I : ℝ))
  filter_upwards [hbad, hcolumns, hrate.eventually_lt_const hε] with n hnbad hncolumns hnrate
  have hpositive := absorptionMass_pos_of_row_hazard D (xs n) y anchor
    ((hpairs n).row_pos anchor) hhazard
  have hgap := abs_rowPayoff_gap_le_of_bad_probabilities D (xs n) y (δ n) anchor bound
    (hpairs n).1.le hpositive hhazard hnbad (fun i j => hbound (i, j))
  have hlower := (abs_le.mp hgap).1
  apply isAsymptoticNash_of_pure_gaps D (xs n) y hε.le
  · intro i
    linarith [hmax i]
  · intro j
    exact (pureColumn_le_mixed_of_supported_max D (xs n) y hncolumns j).trans
      (le_add_of_nonneg_right hε.le)

private theorem eventually_isAsymptoticNash_of_profitable_column_limit (D : Data I J)
    (δ : ℕ → ℝ) (xs : ℕ → PMF I) (ys : ℕ → PMF J) (x : PMF I)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hx : Tendsto (fun n => toVector (xs n)) atTop (𝓝 (toVector x)))
    (hpairs : ∀ n, IsDeltaProperPair D (δ n) (xs n) (ys n)) (anchor : J)
    (hmax : ∀ j, stationaryPayoff D x (PMF.pure j) true ≤
      stationaryPayoff D x (PMF.pure anchor) true)
    (hprofit : 0 < stationaryPayoff D x (PMF.pure anchor) true) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ initial,
      (game D).IsεAsymptoticNash (liminfPayoff D initial) ε (stationaryProfile D x (ys n)) := by
  have hhazard : 0 < absorptionMass D x (PMF.pure anchor) := by
    by_contra hnot
    have hzero := le_antisymm (le_of_not_gt hnot) (absorptionMass_nonneg D x (PMF.pure anchor))
    exact hprofit.ne' (stationaryPayoff_eq_zero_of_mass_eq_zero D x (PMF.pure anchor) true hzero)
  have hbad : ∀ᶠ n in atTop, ∀ j, 0 < absorptionMass D x (PMF.pure j) →
      stationaryPayoff D x (PMF.pure j) true ≠ stationaryPayoff D x (PMF.pure anchor) true →
      (ys n j).toReal ≤ δ n * (ys n anchor).toReal := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hconditions : 0 < absorptionMass D x (PMF.pure j) ∧
        stationaryPayoff D x (PMF.pure j) true ≠ stationaryPayoff D x (PMF.pure anchor) true
    · have hstrict := lt_of_le_of_ne (hmax j) hconditions.2
      have hj := tendsto_pureColumn_stationaryPayoff D xs x hx true j hconditions.1
      have ha := tendsto_pureColumn_stationaryPayoff D xs x hx true anchor hhazard
      filter_upwards [hj.eventually_lt ha hstrict] with n hn
      intro _ _
      exact (hpairs n).column_ranking anchor j hn
    · exact Eventually.of_forall fun n hpositive hne =>
        False.elim (hconditions ⟨hpositive, hne⟩)
  have hrows : ∀ᶠ n in atTop, ∀ i ∈ x.support, ∀ other,
      stationaryPayoff D (PMF.pure other) (ys n) false ≤
        stationaryPayoff D (PMF.pure i) (ys n) false := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ∈ x.support
    · have hpos := ENNReal.toReal_pos ((PMF.mem_support_iff x i).mp hi) (x.apply_ne_top i)
      exact (eventually_row_maximal_of_limit_pos D δ xs ys x hδ hx hpairs i hpos).mono
        (fun n hn _ => hn)
    · exact Eventually.of_forall fun n hsupport => False.elim (hi hsupport)
  obtain ⟨bound, hbound⟩ := exists_abs_bound_of_finite
    (fun pair : I × J => D.reward pair.1 pair.2 true)
  have hrate : Tendsto (fun n => (2 * bound) * (Fintype.card J : ℝ) *
      (δ n / absorptionMass D x (PMF.pure anchor))) atTop (𝓝 0) := by
    simpa only [Pi.div_apply, zero_div, mul_zero] using
      (hδ.div tendsto_const_nhds hhazard.ne').const_mul ((2 * bound) * (Fintype.card J : ℝ))
  filter_upwards [hbad, hrows, hrate.eventually_lt_const hε] with n hnbad hnrows hnrate
  have hpositive := absorptionMass_pos_of_column_hazard D x (ys n) anchor
    ((hpairs n).column_pos anchor) hhazard
  have hgap := abs_columnPayoff_gap_le_of_bad_probabilities D x (ys n) (δ n) anchor bound
    (hpairs n).1.le hpositive hhazard hnbad (fun i j => hbound (i, j))
  have hlower := (abs_le.mp hgap).1
  apply isAsymptoticNash_of_pure_gaps D x (ys n) hε.le
  · intro i
    exact (pureRow_le_mixed_of_supported_max D x (ys n) hnrows i).trans
      (le_add_of_nonneg_right hε.le)
  · intro j
    linarith [hmax j]

/-- The canonical-model version of Theorem 3.1: one stationary pair for each positive error
caps every unilateral behavioral deviation at every initial state under literal expected liminf.
Proper pairs, limiting sequences, and all limiting cases are produced internally. -/
theorem exists_stationary_liminfApproximateEquilibrium [Nonempty I] [Nonempty J]
    (D : Data I J) {ε : ℝ} (hε : 0 < ε) :
    ∃ (x : PMF I) (y : PMF J), ∀ initial,
      (game D).IsεAsymptoticNash (liminfPayoff D initial) ε (stationaryProfile D x y) := by
  classical
  obtain ⟨x, y, hproper⟩ := exists_properPair D
  obtain ⟨δ, xs, ys, hδ, hx, hy, hpairs⟩ := hproper.exists_stationary_sequence
  by_cases hpositive : 0 < absorptionMass D x y
  · obtain ⟨n, hn⟩ := (eventually_isAsymptoticNash_of_absorbing_proper_limit
      D δ xs ys x y hδ hx hy hpairs hpositive hε).exists
    exact ⟨xs n, ys n, hn⟩
  · have hzero : absorptionMass D x y = 0 :=
      le_antisymm (le_of_not_gt hpositive) (absorptionMass_nonneg D x y)
    obtain ⟨row, _, hrowmax⟩ := Finset.exists_max_image Finset.univ
      (fun i => stationaryPayoff D (PMF.pure i) y false) Finset.univ_nonempty
    obtain ⟨column, _, hcolumnmax⟩ := Finset.exists_max_image Finset.univ
      (fun j => stationaryPayoff D x (PMF.pure j) true) Finset.univ_nonempty
    have hrow : ∀ i, stationaryPayoff D (PMF.pure i) y false ≤
        stationaryPayoff D (PMF.pure row) y false := fun i => hrowmax i (Finset.mem_univ i)
    have hcolumn : ∀ j, stationaryPayoff D x (PMF.pure j) true ≤
        stationaryPayoff D x (PMF.pure column) true := fun j => hcolumnmax j (Finset.mem_univ j)
    by_cases hrowprofit : 0 < stationaryPayoff D (PMF.pure row) y false
    · obtain ⟨n, hn⟩ := (eventually_isAsymptoticNash_of_profitable_row_limit
        D δ xs ys y hδ hy hpairs row hrow hrowprofit hε).exists
      exact ⟨xs n, y, hn⟩
    · by_cases hcolumnprofit : 0 < stationaryPayoff D x (PMF.pure column) true
      · obtain ⟨n, hn⟩ := (eventually_isAsymptoticNash_of_profitable_column_limit
          D δ xs ys x hδ hx hpairs column hcolumn hcolumnprofit hε).exists
        exact ⟨x, ys n, hn⟩
      · refine ⟨x, y, isAsymptoticNash_of_pure_gaps D x y hε.le ?_ ?_⟩
        · intro i
          rw [stationaryPayoff_eq_zero_of_mass_eq_zero D x y false hzero, zero_add]
          exact (hrow i).trans ((le_of_not_gt hrowprofit).trans hε.le)
        · intro j
          rw [stationaryPayoff_eq_zero_of_mass_eq_zero D x y true hzero, zero_add]
          exact (hcolumn j).trans ((le_of_not_gt hcolumnprofit).trans hε.le)

end GameTheory.RecursiveAbsorption
