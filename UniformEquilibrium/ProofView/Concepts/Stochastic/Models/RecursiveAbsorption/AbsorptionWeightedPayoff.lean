import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.RecursiveAbsorption.StationaryPayoff
import MathUE.Probability.FiniteLawRepairExpectation

/-!
# Absorption-weighted pure stationary payoffs

Lemma 2.2 of Flesch, Thuijsman and Vrieze (1996) rewrites the stationary
numerator as the sum of each pure action's absorption mass times its stationary
payoff. The identities below use the actual independent action PMFs and the
checked payoff ratio, including zero pure absorption mass. Both players'
payoffs remain signed; an absolute reward bound bounds their stationary values,
not a fictitious zero-payoff action added to the best-response problem.

The normalized absorption laws and their bad-mass estimates provide the
accounting step for the paper's Lemma 3.2. Normalization requires positive
actual total absorption mass; zero total mass retains the separately checked
literal payoff zero. Bad mass means absorption-weighted probability, not raw
action probability. No general approximate-equilibrium existence result is
asserted here, and no proper-ranking decay producer is assumed or proved here.
-/

noncomputable section

open _root_.Math.Probability
open _root_.Math.ProbabilityMassFunction GameTheory.Math.Probability
open _root_.Math.Probability.FiniteLawRepair
open scoped BigOperators

namespace GameTheory.RecursiveAbsorption

variable {I J : Type} [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
/-- The actual mixed absorption mass is the expectation of its pure row masses. -/
theorem absorptionMass_eq_expect_pureRow (D : Data I J) (x : PMF I) (y : PMF J) :
    absorptionMass D x y = expect x (fun i => absorptionMass D (PMF.pure i) y) := by
  unfold absorptionMass
  simp only [expect_pure]

omit [Fintype I] [Fintype J] in
/-- The actual mixed contribution is the expectation of its pure row contributions. -/
theorem absorbingContribution_eq_expect_pureRow (D : Data I J)
    (x : PMF I) (y : PMF J) (who : Bool) :
    absorbingContribution D x y who =
      expect x (fun i => absorbingContribution D (PMF.pure i) y who) := by
  unfold absorbingContribution
  simp only [expect_pure]

/-- The corresponding actual absorption-mass identity for pure columns. -/
theorem absorptionMass_eq_expect_pureColumn (D : Data I J) (x : PMF I) (y : PMF J) :
    absorptionMass D x y = expect y (fun j => absorptionMass D x (PMF.pure j)) := by
  unfold absorptionMass
  simp only [expect_pure]
  simp_rw [expect_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The corresponding actual contribution identity for pure columns. -/
theorem absorbingContribution_eq_expect_pureColumn (D : Data I J)
    (x : PMF I) (y : PMF J) (who : Bool) :
    absorbingContribution D x y who =
      expect y (fun j => absorbingContribution D x (PMF.pure j) who) := by
  unfold absorbingContribution
  simp only [expect_pure]
  simp_rw [expect_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Lemma 2.2's absorption-weighted pure-row payoff numerator, including zero pure hazards. -/
theorem absorbingContribution_eq_expect_mass_mul_pureRowPayoff (D : Data I J)
    (x : PMF I) (y : PMF J) (who : Bool) :
    absorbingContribution D x y who = expect x (fun i =>
      absorptionMass D (PMF.pure i) y * stationaryPayoff D (PMF.pure i) y who) := by
  rw [absorbingContribution_eq_expect_pureRow]
  apply congrArg (expect x)
  funext i
  simpa only [mul_comm] using (stationaryPayoff_mul_absorptionMass D (PMF.pure i) y who).symm

/-- Lemma 2.2's absorption-weighted pure-column payoff numerator. -/
theorem absorbingContribution_eq_expect_mass_mul_pureColumnPayoff (D : Data I J)
    (x : PMF I) (y : PMF J) (who : Bool) :
    absorbingContribution D x y who = expect y (fun j =>
      absorptionMass D x (PMF.pure j) * stationaryPayoff D x (PMF.pure j) who) := by
  rw [absorbingContribution_eq_expect_pureColumn]
  apply congrArg (expect y)
  funext j
  simpa only [mul_comm] using (stationaryPayoff_mul_absorptionMass D x (PMF.pure j) who).symm

/-- An actual absolute reward bound bounds the stationary ratio, even at zero total mass. -/
theorem abs_stationaryPayoff_le (D : Data I J) (x : PMF I) (y : PMF J) (who : Bool)
    (bound : ℝ) (hbound : ∀ i j, |D.reward i j who| ≤ bound) :
    |stationaryPayoff D x y who| ≤ bound := by
  unfold stationaryPayoff
  by_cases hzero : absorptionMass D x y = 0
  · rw [hzero, div_zero, abs_zero]
    obtain ⟨i, _⟩ := x.support_nonempty
    obtain ⟨j, _⟩ := y.support_nonempty
    exact (abs_nonneg (D.reward i j who)).trans (hbound i j)
  · have hpositive : 0 < absorptionMass D x y :=
      lt_of_le_of_ne (absorptionMass_nonneg D x y) (Ne.symm hzero)
    apply abs_le.mpr
    constructor
    · exact (le_div_iff₀ hpositive).2
        (mul_mass_le_absorbingContribution D x y who (-bound)
          (fun i j => (abs_le.mp (hbound i j)).1))
    · exact (div_le_iff₀ hpositive).2
        (absorbingContribution_le_mul_mass D x y who bound
          (fun i j => (abs_le.mp (hbound i j)).2))

/-- The row's actual contribution to the total absorption probability. -/
def rowAbsorptionWeight (D : Data I J) (x : PMF I) (y : PMF J) (i : I) : ℝ :=
  (x i).toReal * absorptionMass D (PMF.pure i) y

/-- The column's actual contribution to the total absorption probability. -/
def columnAbsorptionWeight (D : Data I J) (x : PMF I) (y : PMF J) (j : J) : ℝ :=
  (y j).toReal * absorptionMass D x (PMF.pure j)

omit [Fintype I] [Fintype J] in
theorem rowAbsorptionWeight_nonneg (D : Data I J) (x : PMF I) (y : PMF J) (i : I) :
    0 ≤ rowAbsorptionWeight D x y i :=
  mul_nonneg ENNReal.toReal_nonneg (absorptionMass_nonneg D (PMF.pure i) y)

omit [Fintype I] [Fintype J] in
theorem columnAbsorptionWeight_nonneg (D : Data I J) (x : PMF I) (y : PMF J) (j : J) :
    0 ≤ columnAbsorptionWeight D x y j :=
  mul_nonneg ENNReal.toReal_nonneg (absorptionMass_nonneg D x (PMF.pure j))

omit [Fintype J] in
theorem sum_rowAbsorptionWeight (D : Data I J) (x : PMF I) (y : PMF J) :
    (∑ i, rowAbsorptionWeight D x y i) = absorptionMass D x y := by
  rw [absorptionMass_eq_expect_pureRow, expect_eq_sum]
  rfl

theorem sum_columnAbsorptionWeight (D : Data I J) (x : PMF I) (y : PMF J) :
    (∑ j, columnAbsorptionWeight D x y j) = absorptionMass D x y := by
  rw [absorptionMass_eq_expect_pureColumn, expect_eq_sum]
  rfl

theorem sum_rowAbsorptionWeight_mul_payoff (D : Data I J)
    (x : PMF I) (y : PMF J) (who : Bool) :
    (∑ i, rowAbsorptionWeight D x y i * stationaryPayoff D (PMF.pure i) y who) =
      absorbingContribution D x y who := by
  rw [absorbingContribution_eq_expect_mass_mul_pureRowPayoff, expect_eq_sum]
  simp only [rowAbsorptionWeight, mul_assoc]

theorem sum_columnAbsorptionWeight_mul_payoff (D : Data I J)
    (x : PMF I) (y : PMF J) (who : Bool) :
    (∑ j, columnAbsorptionWeight D x y j * stationaryPayoff D x (PMF.pure j) who) =
      absorbingContribution D x y who := by
  rw [absorbingContribution_eq_expect_mass_mul_pureColumnPayoff, expect_eq_sum]
  simp only [columnAbsorptionWeight, mul_assoc]

/-- Normalized row absorption weights, used as a probability law only at positive mass. -/
def rowAbsorptionVector (D : Data I J) (x : PMF I) (y : PMF J) (i : I) : ℝ :=
  rowAbsorptionWeight D x y i / absorptionMass D x y

/-- Normalized column absorption weights, with the same positive-mass restriction. -/
def columnAbsorptionVector (D : Data I J) (x : PMF I) (y : PMF J) (j : J) : ℝ :=
  columnAbsorptionWeight D x y j / absorptionMass D x y

omit [Fintype J] in
theorem rowAbsorptionVector_mem_simplexWeights (D : Data I J) (x : PMF I) (y : PMF J)
    (hpositive : 0 < absorptionMass D x y) : rowAbsorptionVector D x y ∈ simplexWeights I := by
  apply mem_simplexWeights.mpr
  refine ⟨fun i => div_nonneg (rowAbsorptionWeight_nonneg D x y i) hpositive.le, ?_⟩
  simp only [rowAbsorptionVector]
  rw [← Finset.sum_div, sum_rowAbsorptionWeight, div_self hpositive.ne']

theorem columnAbsorptionVector_mem_simplexWeights (D : Data I J) (x : PMF I) (y : PMF J)
    (hpositive : 0 < absorptionMass D x y) :
    columnAbsorptionVector D x y ∈ simplexWeights J := by
  apply mem_simplexWeights.mpr
  refine ⟨fun j => div_nonneg (columnAbsorptionWeight_nonneg D x y j) hpositive.le, ?_⟩
  simp only [columnAbsorptionVector]
  rw [← Finset.sum_div, sum_columnAbsorptionWeight, div_self hpositive.ne']

/-- Actual row-action law conditional on the one-step absorption event.
This accounting PMF does not replace the game's infinite trajectory law. -/
def rowAbsorptionLaw (D : Data I J) (x : PMF I) (y : PMF J)
    (hpositive : 0 < absorptionMass D x y) : PMF I :=
  ofVector (rowAbsorptionVector D x y) (rowAbsorptionVector_mem_simplexWeights D x y hpositive)

/-- The corresponding actual column-action law conditional on one-step absorption. -/
def columnAbsorptionLaw (D : Data I J) (x : PMF I) (y : PMF J)
    (hpositive : 0 < absorptionMass D x y) : PMF J :=
  ofVector (columnAbsorptionVector D x y)
    (columnAbsorptionVector_mem_simplexWeights D x y hpositive)

omit [Fintype J] in
theorem rowAbsorptionLaw_toVector (D : Data I J) (x : PMF I) (y : PMF J)
    (hpositive : 0 < absorptionMass D x y) :
    toVector (rowAbsorptionLaw D x y hpositive) = rowAbsorptionVector D x y :=
  toVector_ofVector (rowAbsorptionVector_mem_simplexWeights D x y hpositive)

theorem columnAbsorptionLaw_toVector (D : Data I J) (x : PMF I) (y : PMF J)
    (hpositive : 0 < absorptionMass D x y) :
    toVector (columnAbsorptionLaw D x y hpositive) = columnAbsorptionVector D x y :=
  toVector_ofVector (columnAbsorptionVector_mem_simplexWeights D x y hpositive)

/-- Lemma 2.2's actual normalized absorption-weighted row-payoff identity. -/
theorem expect_rowAbsorptionLaw_purePayoff (D : Data I J) (x : PMF I) (y : PMF J)
    (who : Bool) (hpositive : 0 < absorptionMass D x y) :
    expect (rowAbsorptionLaw D x y hpositive)
      (fun i => stationaryPayoff D (PMF.pure i) y who) = stationaryPayoff D x y who := by
  rw [expect_eq_sum]
  simp only [rowAbsorptionLaw, ofVector_toReal, rowAbsorptionVector, div_mul_eq_mul_div]
  rw [← Finset.sum_div, sum_rowAbsorptionWeight_mul_payoff]
  rfl

/-- The same normalized absorption-weighted identity for the column actions. -/
theorem expect_columnAbsorptionLaw_purePayoff (D : Data I J) (x : PMF I) (y : PMF J)
    (who : Bool) (hpositive : 0 < absorptionMass D x y) :
    expect (columnAbsorptionLaw D x y hpositive)
      (fun j => stationaryPayoff D x (PMF.pure j) who) = stationaryPayoff D x y who := by
  rw [expect_eq_sum]
  simp only [columnAbsorptionLaw, ofVector_toReal, columnAbsorptionVector, div_mul_eq_mul_div]
  rw [← Finset.sum_div, sum_columnAbsorptionWeight_mul_payoff]
  rfl

open Classical in
/-- Pure rows having the anchor's actual stationary payoff. -/
def rowPayoffLevel (D : Data I J) (y : PMF J) (who : Bool) (anchor : I) : Finset I :=
  Finset.univ.filter fun i =>
    stationaryPayoff D (PMF.pure i) y who = stationaryPayoff D (PMF.pure anchor) y who

open Classical in
/-- Pure columns having the anchor's actual stationary payoff. -/
def columnPayoffLevel (D : Data I J) (x : PMF I) (who : Bool) (anchor : J) : Finset J :=
  Finset.univ.filter fun j =>
    stationaryPayoff D x (PMF.pure j) who = stationaryPayoff D x (PMF.pure anchor) who

open Classical in
/-- Absorption-weighted mass outside the anchor's payoff level.
It is a probability mass only when the actual total absorption mass is positive. -/
def rowBadAbsorptionMass (D : Data I J) (x : PMF I) (y : PMF J)
    (who : Bool) (anchor : I) : ℝ :=
  _root_.Math.Probability.FiniteLawRepair.badMass
    (rowAbsorptionVector D x y) (rowPayoffLevel D y who anchor)

open Classical in
/-- The corresponding bad absorption-weighted mass for columns. -/
def columnBadAbsorptionMass (D : Data I J) (x : PMF I) (y : PMF J)
    (who : Bool) (anchor : J) : ℝ :=
  _root_.Math.Probability.FiniteLawRepair.badMass
    (columnAbsorptionVector D x y) (columnPayoffLevel D x who anchor)

/-- Lemma 3.2's finite bad-mass estimate, derived from the actual row absorption law.
The anchor's payoff and the mixed payoff may both be negative. -/
theorem abs_stationaryPayoff_sub_pureRow_le (D : Data I J) (x : PMF I) (y : PMF J)
    (who : Bool) (anchor : I) (bound : ℝ) (hpositive : 0 < absorptionMass D x y)
    (hbound : ∀ i j, |D.reward i j who| ≤ bound) :
    |stationaryPayoff D x y who - stationaryPayoff D (PMF.pure anchor) y who| ≤
      (2 * bound) * rowBadAbsorptionMass D x y who anchor := by
  classical
  have hanchor : anchor ∈ rowPayoffLevel D y who anchor := by
    simp only [rowPayoffLevel, Finset.mem_filter, Finset.mem_univ, true_and]
  have hgood : ∀ i ∈ rowPayoffLevel D y who anchor,
      stationaryPayoff D (PMF.pure i) y who = stationaryPayoff D (PMF.pure anchor) y who := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hestimate := abs_expect_sub_anchor_le_two_mul_badMass (rowAbsorptionLaw D x y hpositive)
      (rowPayoffLevel D y who anchor) anchor hanchor
      (fun i => stationaryPayoff D (PMF.pure i) y who) bound
      (fun i => abs_stationaryPayoff_le D (PMF.pure i) y who bound hbound) hgood
  rw [expect_rowAbsorptionLaw_purePayoff, rowAbsorptionLaw_toVector] at hestimate
  exact hestimate

/-- The column version of the same actual-law repair estimate. -/
theorem abs_stationaryPayoff_sub_pureColumn_le (D : Data I J) (x : PMF I) (y : PMF J)
    (who : Bool) (anchor : J) (bound : ℝ) (hpositive : 0 < absorptionMass D x y)
    (hbound : ∀ i j, |D.reward i j who| ≤ bound) :
    |stationaryPayoff D x y who - stationaryPayoff D x (PMF.pure anchor) who| ≤
      (2 * bound) * columnBadAbsorptionMass D x y who anchor := by
  classical
  have hanchor : anchor ∈ columnPayoffLevel D x who anchor := by
    simp only [columnPayoffLevel, Finset.mem_filter, Finset.mem_univ, true_and]
  have hgood : ∀ j ∈ columnPayoffLevel D x who anchor,
      stationaryPayoff D x (PMF.pure j) who = stationaryPayoff D x (PMF.pure anchor) who := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hestimate := abs_expect_sub_anchor_le_two_mul_badMass (columnAbsorptionLaw D x y hpositive)
      (columnPayoffLevel D x who anchor) anchor hanchor
      (fun j => stationaryPayoff D x (PMF.pure j) who) bound
      (fun j => abs_stationaryPayoff_le D x (PMF.pure j) who bound hbound) hgood
  rw [expect_columnAbsorptionLaw_purePayoff, columnAbsorptionLaw_toVector] at hestimate
  exact hestimate

/-- Bad positive-hazard row probabilities control the actual absorption-weighted payoff gap. -/
theorem abs_rowPayoff_gap_le_of_bad_probabilities (D : Data I J)
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

/-- The corresponding actual column estimate, with zero-hazard actions contributing no mass. -/
theorem abs_columnPayoff_gap_le_of_bad_probabilities (D : Data I J)
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

end GameTheory.RecursiveAbsorption
