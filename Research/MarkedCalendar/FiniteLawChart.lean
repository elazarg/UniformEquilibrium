import Research.MarkedCalendar.Order
import UniformEquilibrium.Quitting.Terminal.FiniteOpponentAtomGapReplyMenu
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Actual finite-law interval charts

The source is an actual finite family of finite stopping laws. Its average
determines positive interval cells, with Never ordered after every finite date.
The base is canonical unit-interval volume, not a supplied density law.

This initial slice constructs the actual weights, cells, and real densities.
It does not yet assert normalized chart laws, calendar/menu transport, limiting
complete caps, or realization of variations in the original game.
-/

noncomputable section

open Set MeasureTheory GameTheory.Math.Probability
open scoped BigOperators

namespace GameTheory.MarkedCalendarChart

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- Original finite laws with their literal Never clock ordered last. -/
def sourceClockLaw (laws : ι → FinDist (Option ℕ)) (i : ι) : FinDist (WithTop ℕ) :=
  (laws i).map quittingStoppingTimeValue

/-- The actual common mixture, before any interval chart is constructed. -/
def averageClockLaw (laws : ι → FinDist (Option ℕ)) : FinDist (WithTop ℕ) :=
  FinDist.uniformOfFintype.bind (sourceClockLaw laws)

theorem averageClockLaw_prob (laws : ι → FinDist (Option ℕ)) (clock : WithTop ℕ) :
    (averageClockLaw laws).prob clock =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, (sourceClockLaw laws i).prob clock := by
  rw [averageClockLaw, FinDist.prob_bind, FinDist.expect_eq_sum]
  simp only [FinDist.prob_uniformOfFintype, Finset.mul_sum]

theorem card_mul_averageClockLaw_prob (laws : ι → FinDist (Option ℕ))
    (clock : WithTop ℕ) :
    (Fintype.card ι : ℝ) * (averageClockLaw laws).prob clock =
      ∑ i, (sourceClockLaw laws i).prob clock := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [averageClockLaw_prob, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]

theorem sourceClockLaw_prob_le (laws : ι → FinDist (Option ℕ)) (i : ι)
    (clock : WithTop ℕ) :
    (sourceClockLaw laws i).prob clock ≤
      (Fintype.card ι : ℝ) * (averageClockLaw laws).prob clock := by
  rw [card_mul_averageClockLaw_prob]
  exact Finset.single_le_sum (fun j _ => (sourceClockLaw laws j).prob_nonneg clock)
    (Finset.mem_univ i)

theorem sourceClockLaw_support_subset (laws : ι → FinDist (Option ℕ)) (i : ι) :
    (sourceClockLaw laws i).support ⊆ (averageClockLaw laws).support := by
  intro clock hclock
  apply (averageClockLaw laws).prob_pos_iff.mp
  have hpos := (sourceClockLaw laws i).prob_pos_iff.mpr hclock
  have hbound := sourceClockLaw_prob_le laws i clock
  have hnonneg := (averageClockLaw laws).prob_nonneg clock
  by_contra hnot
  have hzero := le_antisymm (le_of_not_gt hnot) hnonneg
  rw [hzero, mul_zero] at hbound
  exact (not_le_of_gt hpos) hbound

/-- Only positive mixture atoms index cells; zero-width intervals are absent. -/
abbrev Cell (laws : ι → FinDist (Option ℕ)) := (averageClockLaw laws).supportFinset

def weight (laws : ι → FinDist (Option ℕ)) (a : Cell laws) : ℝ :=
  (averageClockLaw laws).prob a

def ownWeight (laws : ι → FinDist (Option ℕ)) (i : ι) (a : Cell laws) : ℝ :=
  (sourceClockLaw laws i).prob a

theorem weight_pos (laws : ι → FinDist (Option ℕ)) (a : Cell laws) : 0 < weight laws a :=
  (averageClockLaw laws).prob_pos_iff.mpr (FinDist.mem_supportFinset.mp a.property)

theorem ownWeight_nonneg (laws : ι → FinDist (Option ℕ)) (i : ι) (a : Cell laws) :
    0 ≤ ownWeight laws i a := (sourceClockLaw laws i).prob_nonneg a

theorem ownWeight_le (laws : ι → FinDist (Option ℕ)) (i : ι) (a : Cell laws) :
    ownWeight laws i a ≤ (Fintype.card ι : ℝ) * weight laws a :=
  sourceClockLaw_prob_le laws i a

theorem sum_weight (laws : ι → FinDist (Option ℕ)) : ∑ a : Cell laws, weight laws a = 1 := by
  change (∑ a : Cell laws, (averageClockLaw laws).prob a) = 1
  rw [Finset.sum_coe_sort]
  exact (averageClockLaw laws).sum_prob_supportFinset

theorem sum_ownWeight (laws : ι → FinDist (Option ℕ)) (i : ι) :
    ∑ a : Cell laws, ownWeight laws i a = 1 := by
  change (∑ a : Cell laws, (sourceClockLaw laws i).prob a) = 1
  rw [Finset.sum_coe_sort]
  have hsub : (sourceClockLaw laws i).support ⊆
      ((averageClockLaw laws).supportFinset : Set (WithTop ℕ)) :=
    fun _ h => FinDist.mem_supportFinset.mpr (sourceClockLaw_support_subset laws i h)
  have hsum := FinDist.expect_eq_sum_of_subset (sourceClockLaw laws i) (fun _ => (1 : ℝ))
    (averageClockLaw laws).supportFinset hsub
  simpa only [FinDist.expect_const, mul_one] using hsum.symm

def left (laws : ι → FinDist (Option ℕ)) (a : Cell laws) : ℝ :=
  ∑ b : Cell laws, if b < a then weight laws b else 0

def right (laws : ι → FinDist (Option ℕ)) (a : Cell laws) : ℝ :=
  left laws a + weight laws a

theorem left_nonneg (laws : ι → FinDist (Option ℕ)) (a : Cell laws) : 0 ≤ left laws a := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact (weight_pos laws b).le
  · exact le_rfl

theorem left_lt_right (laws : ι → FinDist (Option ℕ)) (a : Cell laws) :
    left laws a < right laws a := lt_add_of_pos_right _ (weight_pos laws a)

theorem right_eq_sum_le (laws : ι → FinDist (Option ℕ)) (a : Cell laws) :
    right laws a = ∑ b : Cell laws, if b ≤ a then weight laws b else 0 := by
  classical
  calc
    right laws a =
        (∑ b : Cell laws, if b < a then weight laws b else 0) +
        ∑ b : Cell laws, if b = a then weight laws b else 0 := by
      simp only [right, left, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = ∑ b : Cell laws,
        ((if b < a then weight laws b else 0) +
          if b = a then weight laws b else 0) := Finset.sum_add_distrib.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rcases lt_trichotomy b a with h | h | h
      · simp only [h, h.le, h.ne, ite_true, ite_false, add_zero]
      · subst b
        simp only [lt_self_iff_false, le_refl, ite_false, ite_true, zero_add]
      · simp only [not_lt_of_ge h.le, not_le_of_gt h, Ne.symm h.ne,
          ite_false, add_zero]

theorem right_le_one (laws : ι → FinDist (Option ℕ)) (a : Cell laws) :
    right laws a ≤ 1 := by
  rw [right_eq_sum_le, ← sum_weight laws]
  apply Finset.sum_le_sum
  intro b _
  split_ifs
  · exact le_rfl
  · exact (weight_pos laws b).le

theorem right_le_left_of_lt (laws : ι → FinDist (Option ℕ)) {a b : Cell laws}
    (hab : a < b) : right laws a ≤ left laws b := by
  rw [right_eq_sum_le, left]
  apply Finset.sum_le_sum
  intro d _
  by_cases hda : d ≤ a
  · simp only [hda, hda.trans_lt hab, ite_true, le_refl]
  · simp only [hda, ite_false]
    split_ifs
    · exact (weight_pos laws d).le
    · exact le_rfl

def leftPoint (laws : ι → FinDist (Option ℕ)) (a : Cell laws) : unitInterval :=
  ⟨left laws a, left_nonneg laws a, (left_lt_right laws a).le.trans (right_le_one laws a)⟩

def rightPoint (laws : ι → FinDist (Option ℕ)) (a : Cell laws) : unitInterval :=
  ⟨right laws a, (left_nonneg laws a).trans (left_lt_right laws a).le, right_le_one laws a⟩

/-- Half-open actual atom interval; the omitted final point has zero base mass. -/
def interval (laws : ι → FinDist (Option ℕ)) (a : Cell laws) : Set unitInterval :=
  Ico (leftPoint laws a) (rightPoint laws a)

theorem measurableSet_interval (laws : ι → FinDist (Option ℕ)) (a : Cell laws) :
    MeasurableSet (interval laws a) := measurableSet_Ico

theorem volume_interval (laws : ι → FinDist (Option ℕ)) (a : Cell laws) :
    volume (interval laws a) = ENNReal.ofReal (weight laws a) := by
  rw [interval, unitInterval.volume_Ico]
  congr 1
  change right laws a - left laws a = weight laws a
  simp only [right, add_sub_cancel_left]

theorem pairwise_disjoint_interval (laws : ι → FinDist (Option ℕ)) :
    Pairwise fun a b : Cell laws => Disjoint (interval laws a) (interval laws b) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  change left laws a ≤ (x : ℝ) ∧ (x : ℝ) < right laws a at hxa
  change left laws b ≤ (x : ℝ) ∧ (x : ℝ) < right laws b at hxb
  rcases lt_or_gt_of_ne hab with h | h
  · exact (not_lt_of_ge ((right_le_left_of_lt laws h).trans hxb.1)) hxa.2
  · exact (not_lt_of_ge ((right_le_left_of_lt laws h).trans hxa.1)) hxb.2

/-- Actual density ratio on each positive mixture cell. -/
def density (laws : ι → FinDist (Option ℕ)) (i : ι) (x : unitInterval) : ℝ :=
  ∑ a : Cell laws,
    (interval laws a).indicator (fun _ => ownWeight laws i a / weight laws a) x

theorem measurable_density (laws : ι → FinDist (Option ℕ)) (i : ι) :
    Measurable (density laws i) := by
  apply Finset.measurable_sum
  intro a _
  exact measurable_const.indicator (measurableSet_interval laws a)

theorem density_nonneg (laws : ι → FinDist (Option ℕ)) (i : ι) (x : unitInterval) :
    0 ≤ density laws i x := by
  apply Finset.sum_nonneg
  intro a _
  apply Set.indicator_nonneg
  intro _ _
  exact div_nonneg (ownWeight_nonneg laws i a) (weight_pos laws a).le

end GameTheory.MarkedCalendarChart
