import Research.MarkedCalendar.Order
import UniformEquilibrium.Quitting.Terminal.FiniteOpponentAtomGapReplyMenu
import UniformEquilibrium.Quitting.Paths.CommonStoppingCalendarRetiming
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.WithDensity
import GameTheory.Math.Probability.Measure
import Mathlib.Logic.Equiv.Option

/-! # Actual finite-law interval charts

The source is an actual finite family of finite stopping laws. Its average
determines positive interval cells, with Never ordered after every finite date.
The base is canonical unit-interval volume, not a supplied density law.

One density compiler realizes every finite law on the fixed reference cells.
Normalization and decoder recovery are derived for those literal cell weights;
domination follows from their bound relative to the old interval widths. The
original chart laws specialize this compiler and retain the exact common-mixture
identity, which is not asserted for arbitrary replacement cell laws.
The interval decoder recovers the same original
laws and their independent product, with fallback confined to a derived-null
complement. The actual endpoint calendar collapses each cell to its midpoint
or literal Never. The full finite reply-menu image preserves comparisons with
supported clocks and the original pure first outcome. The chart's independent
product has exactly the original terminal-outcome law, including literal Never.
Every original pure reply has the exact updated source-outcome law against the
unchanged opponents' chart, even when the opponent set is empty. Limiting
complete caps and original variation witnesses remain separate obligations.
-/

noncomputable section

open Set Filter MeasureTheory GameTheory.Math.Probability
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

/-- The finite source law on its actual common positive-cell carrier. -/
def cellLaw (laws : ι → FinDist (Option ℕ)) (i : ι) : FinDist (Cell laws) :=
  FinDist.ofWeights (ownWeight laws i) (ownWeight_nonneg laws i) (sum_ownWeight laws i)

theorem cellLaw_prob (laws : ι → FinDist (Option ℕ)) (i : ι) (a : Cell laws) :
    (cellLaw laws i).prob a = ownWeight laws i a := FinDist.prob_ofWeights ..

/-- An arbitrary finite cell law is realized on the unchanged reference intervals. -/
def referenceDensity (laws : ι → FinDist (Option ℕ)) (p : FinDist (Cell laws))
    (x : unitInterval) : ℝ :=
  ∑ a : Cell laws,
    (interval laws a).indicator (fun _ => p.prob a / weight laws a) x

theorem measurable_referenceDensity (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) : Measurable (referenceDensity laws p) := by
  apply Finset.measurable_sum
  intro a _
  exact measurable_const.indicator (measurableSet_interval laws a)

theorem referenceDensity_nonneg (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) (x : unitInterval) : 0 ≤ referenceDensity laws p x := by
  apply Finset.sum_nonneg
  intro a _
  apply Set.indicator_nonneg
  intro _ _
  exact div_nonneg (p.prob_nonneg a) (weight_pos laws a).le

theorem referenceDensity_eq_of_mem_interval (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws))
    {a : Cell laws} {x : unitInterval} (hx : x ∈ interval laws a) :
    referenceDensity laws p x = p.prob a / weight laws a := by
  classical
  unfold referenceDensity
  rw [Finset.sum_eq_single a]
  · exact Set.indicator_of_mem hx _
  · intro b _ hba
    apply Set.indicator_of_notMem
    exact fun hxb => Set.disjoint_left.mp (pairwise_disjoint_interval laws hba) hxb hx
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

theorem referenceDensity_eq_zero_of_notMem (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) {x : unitInterval} (hx : ∀ a, x ∉ interval laws a) :
    referenceDensity laws p x = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  exact Set.indicator_of_notMem (hx a) _

/-- Literal cell weights supply the bound; positivity of the bound is not assumed. -/
theorem referenceDensity_le (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) (C : NNReal)
    (hbound : ∀ a, p.prob a ≤ (C : ℝ) * weight laws a) (x : unitInterval) :
    referenceDensity laws p x ≤ (C : ℝ) := by
  by_cases hx : ∃ a, x ∈ interval laws a
  · obtain ⟨a, ha⟩ := hx
    rw [referenceDensity_eq_of_mem_interval laws p ha]
    exact (div_le_iff₀ (weight_pos laws a)).mpr (hbound a)
  · rw [referenceDensity_eq_zero_of_notMem laws p (not_exists.mp hx)]
    exact C.property

theorem integrable_referenceDensity (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) :
    Integrable (referenceDensity laws p) (volume : Measure unitInterval) := by
  apply integrable_finsetSum
  intro a _
  exact (integrable_const _).indicator (measurableSet_interval laws a)

theorem integral_referenceDensity (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) :
    ∫ x, referenceDensity laws p x ∂(volume : Measure unitInterval) = 1 := by
  unfold referenceDensity
  rw [integral_finsetSum]
  · rw [← p.sum_prob]
    apply Finset.sum_congr rfl
    intro a _
    rw [integral_indicator_const _ (measurableSet_interval laws a), measureReal_def,
      volume_interval, ENNReal.toReal_ofReal (weight_pos laws a).le, smul_eq_mul]
    field_simp [(weight_pos laws a).ne']
  · intro a _
    exact (integrable_const _).indicator (measurableSet_interval laws a)

/-- Actual density ratio on each positive mixture cell, using the reference-law compiler. -/
def density (laws : ι → FinDist (Option ℕ)) (i : ι) : unitInterval → ℝ :=
  referenceDensity laws (cellLaw laws i)

theorem measurable_density (laws : ι → FinDist (Option ℕ)) (i : ι) :
    Measurable (density laws i) := measurable_referenceDensity laws (cellLaw laws i)

theorem density_nonneg (laws : ι → FinDist (Option ℕ)) (i : ι) (x : unitInterval) :
    0 ≤ density laws i x := referenceDensity_nonneg laws (cellLaw laws i) x

theorem density_eq_of_mem_interval (laws : ι → FinDist (Option ℕ)) (i : ι)
    {a : Cell laws} {x : unitInterval} (hx : x ∈ interval laws a) :
    density laws i x = ownWeight laws i a / weight laws a := by
  simpa only [density, cellLaw_prob] using
    referenceDensity_eq_of_mem_interval laws (cellLaw laws i) hx

theorem density_eq_zero_of_notMem (laws : ι → FinDist (Option ℕ)) (i : ι)
    {x : unitInterval} (hx : ∀ a, x ∉ interval laws a) : density laws i x = 0 :=
  referenceDensity_eq_zero_of_notMem laws (cellLaw laws i) hx

theorem density_le_card (laws : ι → FinDist (Option ℕ)) (i : ι) (x : unitInterval) :
    density laws i x ≤ (Fintype.card ι : ℝ) := by
  apply referenceDensity_le laws (cellLaw laws i) (Fintype.card ι : NNReal) _ x
  intro a
  simpa only [cellLaw_prob, NNReal.coe_natCast] using ownWeight_le laws i a

theorem integrable_density (laws : ι → FinDist (Option ℕ)) (i : ι) :
    Integrable (density laws i) (volume : Measure unitInterval) :=
  integrable_referenceDensity laws (cellLaw laws i)

theorem integral_density (laws : ι → FinDist (Option ℕ)) (i : ι) :
    ∫ x, density laws i x ∂(volume : Measure unitInterval) = 1 :=
  integral_referenceDensity laws (cellLaw laws i)

theorem volume_iUnion_interval (laws : ι → FinDist (Option ℕ)) :
    volume (⋃ a : Cell laws, interval laws a) = 1 := by
  rw [measure_iUnion (pairwise_disjoint_interval laws) (measurableSet_interval laws),
    tsum_fintype]
  simp only [volume_interval]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (weight_pos laws a).le),
    sum_weight, ENNReal.ofReal_one]

theorem ae_mem_interval (laws : ι → FinDist (Option ℕ)) :
    ∀ᵐ x : unitInterval ∂volume, ∃ a : Cell laws, x ∈ interval laws a := by
  have hmem : (⋃ a : Cell laws, interval laws a) ∈ ae (volume : Measure unitInterval) :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion (measurableSet_interval laws))).mpr
      (volume_iUnion_interval laws)
  filter_upwards [hmem] with x hx
  exact mem_iUnion.mp hx

theorem ae_sum_density (laws : ι → FinDist (Option ℕ)) :
    ∀ᵐ x : unitInterval ∂volume, ∑ i, density laws i x = (Fintype.card ι : ℝ) := by
  filter_upwards [ae_mem_interval laws] with x hx
  obtain ⟨a, ha⟩ := hx
  simp only [density_eq_of_mem_interval laws _ ha]
  rw [← Finset.sum_div]
  change (∑ i, (sourceClockLaw laws i).prob a) / (averageClockLaw laws).prob a = _
  rw [← card_mul_averageClockLaw_prob]
  exact mul_div_cancel_right₀ _ (weight_pos laws a).ne'

/-- The normalized measure for a literal finite law on the old reference cells. -/
def referenceMeasure (laws : ι → FinDist (Option ℕ)) (p : FinDist (Cell laws)) :
    Measure unitInterval :=
  volume.withDensity (fun x => ENNReal.ofReal (referenceDensity laws p x))

instance referenceMeasure_isProbability (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) : IsProbabilityMeasure (referenceMeasure laws p) where
  measure_univ := by
    rw [referenceMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_referenceDensity laws p)
        (Eventually.of_forall (referenceDensity_nonneg laws p)), integral_referenceDensity,
      ENNReal.ofReal_one]

/-- The actual probability law, with normalization derived from the cell-law probabilities. -/
def referenceLaw (laws : ι → FinDist (Option ℕ)) (p : FinDist (Cell laws)) :
    ProbabilityMeasure unitInterval := ⟨referenceMeasure laws p, inferInstance⟩

theorem referenceMeasure_absolutelyContinuous (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) : referenceMeasure laws p ≪ volume :=
  withDensity_absolutelyContinuous volume
    (fun x => ENNReal.ofReal (referenceDensity laws p x))

/-- The actual density measure constructed from the specified player's original law. -/
def chartMeasure (laws : ι → FinDist (Option ℕ)) (i : ι) : Measure unitInterval :=
  referenceMeasure laws (cellLaw laws i)

instance chartMeasure_isProbability (laws : ι → FinDist (Option ℕ)) (i : ι) :
    IsProbabilityMeasure (chartMeasure laws i) :=
  referenceMeasure_isProbability laws (cellLaw laws i)

/-- The normalized actual chart law, not a supplied density or probability oracle. -/
def chartLaw (laws : ι → FinDist (Option ℕ)) (i : ι) : ProbabilityMeasure unitInterval :=
  referenceLaw laws (cellLaw laws i)

/-- Canonical Lebesgue probability on the unit interval. -/
def base : ProbabilityMeasure unitInterval := ⟨volume, inferInstance⟩

theorem referenceMeasure_le (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) (C : NNReal)
    (hbound : ∀ a, p.prob a ≤ (C : ℝ) * weight laws a) :
    referenceMeasure laws p ≤ (C : ENNReal) • (volume : Measure unitInterval) := by
  calc
    referenceMeasure laws p ≤ volume.withDensity
        (fun _ : unitInterval => ENNReal.ofReal (C : ℝ)) := by
      exact withDensity_mono (Eventually.of_forall fun x =>
        ENNReal.ofReal_le_ofReal (referenceDensity_le laws p C hbound x))
    _ = _ := by rw [withDensity_const, ENNReal.ofReal_coe_nnreal]

theorem referenceLaw_le (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) (C : NNReal)
    (hbound : ∀ a, p.prob a ≤ (C : ℝ) * weight laws a) :
    (referenceLaw laws p : Measure unitInterval) ≤ C • (base : Measure unitInterval) := by
  change referenceMeasure laws p ≤ C • (volume : Measure unitInterval)
  rw [← Measure.coe_nnreal_smul]
  exact referenceMeasure_le laws p C hbound

theorem chartMeasure_le (laws : ι → FinDist (Option ℕ)) (i : ι) :
    chartMeasure laws i ≤ (Fintype.card ι : ENNReal) • (volume : Measure unitInterval) := by
  apply referenceMeasure_le laws (cellLaw laws i) (Fintype.card ι : NNReal)
  intro a
  simpa only [cellLaw_prob, NNReal.coe_natCast] using ownWeight_le laws i a

theorem chartLaw_le (laws : ι → FinDist (Option ℕ)) (i : ι) :
    (chartLaw laws i : Measure unitInterval) ≤
      (Fintype.card ι : NNReal) • (base : Measure unitInterval) := by
  change chartMeasure laws i ≤ (Fintype.card ι : NNReal) • (volume : Measure unitInterval)
  rw [← Measure.coe_nnreal_smul]
  exact chartMeasure_le laws i

/-- The exact source-mixture identity, retained for all later limits and old-chart variations. -/
theorem sum_chartMeasure (laws : ι → FinDist (Option ℕ)) :
    (∑ i, chartMeasure laws i) =
      (Fintype.card ι : ENNReal) • (volume : Measure unitInterval) := by
  calc
    (∑ i, chartMeasure laws i) = volume.withDensity
        (fun x : unitInterval => ∑ i, ENNReal.ofReal (density laws i x)) := by
      have hsum : (∑ i, chartMeasure laws i) = volume.withDensity
          (∑ i, fun x : unitInterval => ENNReal.ofReal (density laws i x)) := by
        simpa only [chartMeasure, referenceMeasure, density, tsum_fintype,
          Measure.sum_fintype] using
          (withDensity_tsum (μ := (volume : Measure unitInterval))
            (fun i => (measurable_density laws i).ennreal_ofReal)).symm
      rw [hsum]
      congr 1
      funext x
      simp only [Finset.sum_apply]
    _ = volume.withDensity (fun _ : unitInterval => ENNReal.ofReal (Fintype.card ι : ℝ)) := by
      apply withDensity_congr_ae
      filter_upwards [ae_sum_density laws] with x hx
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => density_nonneg laws i x), hx]
    _ = _ := by rw [withDensity_const]; simp only [ENNReal.ofReal_natCast]

/-- Relabelling actual cells recovers the specified original law, including Never. -/
theorem cellLaw_map_val (laws : ι → FinDist (Option ℕ)) (i : ι) :
    (cellLaw laws i).map (fun a : Cell laws => (a : WithTop ℕ)) =
      sourceClockLaw laws i := by
  classical
  apply FinDist.ext_of_prob
  intro clock
  by_cases hclock : clock ∈ (averageClockLaw laws).supportFinset
  · exact (FinDist.prob_map_of_injective Subtype.val Subtype.val_injective
      (cellLaw laws i) ⟨clock, hclock⟩).trans (cellLaw_prob laws i ⟨clock, hclock⟩)
  · have hsource : (sourceClockLaw laws i).prob clock = 0 :=
      FinDist.prob_eq_zero_iff.mpr fun h =>
        hclock (FinDist.mem_supportFinset.mpr (sourceClockLaw_support_subset laws i h))
    rw [hsource, FinDist.prob_eq_zero_iff, FinDist.support_map]
    rintro ⟨a, _, ha⟩
    exact hclock (ha ▸ a.property)

/-- The decoder fallback is an actual source cell; it is used only off the full-mass union. -/
def defaultCell (laws : ι → FinDist (Option ℕ)) : Cell laws :=
  ⟨(averageClockLaw laws).support_nonempty.choose,
    FinDist.mem_supportFinset.mpr (averageClockLaw laws).support_nonempty.choose_spec⟩

/-- Decode an interval draw to its original positive cell. -/
def decodeCell (laws : ι → FinDist (Option ℕ)) (x : unitInterval) : Cell laws := by
  classical
  exact if hx : ∃ a : Cell laws, x ∈ interval laws a then hx.choose else defaultCell laws

theorem decodeCell_of_mem_interval (laws : ι → FinDist (Option ℕ))
    {a : Cell laws} {x : unitInterval} (hx : x ∈ interval laws a) :
    decodeCell laws x = a := by
  classical
  have hex : ∃ b : Cell laws, x ∈ interval laws b := ⟨a, hx⟩
  rw [decodeCell, dite_eq_left hex]
  by_contra hne
  exact Set.disjoint_left.mp (pairwise_disjoint_interval laws hne) hex.choose_spec hx

theorem decodeCell_preimage_singleton (laws : ι → FinDist (Option ℕ)) (a : Cell laws) :
    decodeCell laws ⁻¹' {a} = interval laws a ∪
      if defaultCell laws = a then (⋃ b : Cell laws, interval laws b)ᶜ else ∅ := by
  classical
  ext x
  by_cases hx : ∃ b : Cell laws, x ∈ interval laws b
  · obtain ⟨b, hb⟩ := hx
    have hout : x ∉ (⋃ d : Cell laws, interval laws d)ᶜ :=
      fun h => h (mem_iUnion.mpr ⟨b, hb⟩)
    have heq : b = a ↔ x ∈ interval laws a := by
      constructor
      · rintro rfl
        exact hb
      · intro ha
        exact (decodeCell_of_mem_interval laws hb).symm.trans
          (decodeCell_of_mem_interval laws ha)
    simp only [mem_preimage, mem_singleton_iff, decodeCell_of_mem_interval laws hb,
      mem_union]
    split_ifs
    · simpa only [hout, or_false] using heq
    · simpa only [mem_empty_iff_false, or_false] using heq
  · have hout : x ∈ (⋃ b : Cell laws, interval laws b)ᶜ :=
      fun h => hx (mem_iUnion.mp h)
    have hxa : x ∉ interval laws a := fun h => hx ⟨a, h⟩
    simp only [mem_preimage, mem_singleton_iff, decodeCell, dite_eq_right hx,
      mem_union, hxa, false_or]
    split_ifs with h
    · exact iff_of_true h hout
    · exact iff_of_false h (Set.notMem_empty x)

theorem measurable_decodeCell (laws : ι → FinDist (Option ℕ)) :
    Measurable (decodeCell laws) := by
  classical
  apply measurable_to_countable'
  intro a
  rw [decodeCell_preimage_singleton]
  apply (measurableSet_interval laws a).union
  split_ifs
  · exact (MeasurableSet.iUnion (measurableSet_interval laws)).compl
  · exact MeasurableSet.empty

/-- Decoder fallback is null for every compiled law on the unchanged reference cells. -/
theorem referenceMeasure_compl_iUnion_interval (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) :
    referenceMeasure laws p (⋃ a : Cell laws, interval laws a)ᶜ = 0 := by
  apply referenceMeasure_absolutelyContinuous laws p
  rw [measure_compl (MeasurableSet.iUnion (measurableSet_interval laws))
    (measure_ne_top _ _), volume_iUnion_interval, measure_univ, tsub_self]

theorem referenceMeasure_interval (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) (a : Cell laws) :
    referenceMeasure laws p (interval laws a) = ENNReal.ofReal (p.prob a) := by
  rw [referenceMeasure, withDensity_apply _ (measurableSet_interval laws a)]
  calc
    ∫⁻ x in interval laws a, ENNReal.ofReal (referenceDensity laws p x) ∂volume =
        ∫⁻ _ in interval laws a,
          ENNReal.ofReal (p.prob a / weight laws a) ∂volume := by
      apply setLIntegral_congr_fun (measurableSet_interval laws a)
      intro x hx
      change ENNReal.ofReal (referenceDensity laws p x) =
        ENNReal.ofReal (p.prob a / weight laws a)
      rw [referenceDensity_eq_of_mem_interval laws p hx]
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, volume_interval,
        ← ENNReal.ofReal_mul (div_nonneg (p.prob_nonneg a)
          (weight_pos laws a).le), div_mul_cancel₀ _ (weight_pos laws a).ne']

theorem ae_decodeCell_mem_interval_referenceMeasure (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) :
    ∀ᵐ x ∂referenceMeasure laws p, x ∈ interval laws (decodeCell laws x) := by
  have hmem := (referenceMeasure_absolutelyContinuous laws p).ae_le (ae_mem_interval laws)
  filter_upwards [hmem] with x hx
  obtain ⟨a, ha⟩ := hx
  rw [decodeCell_of_mem_interval laws ha]
  exact ha

/-- The old interval decoder recovers exactly the supplied finite cell law. -/
theorem referenceMeasure_map_decodeCell (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) :
    (referenceMeasure laws p).map (decodeCell laws) = p.toMeasure := by
  apply Measure.ext_of_measureReal_singleton
  intro a
  rw [map_measureReal_apply (measurable_decodeCell laws) (measurableSet_singleton a),
    FinDist.toMeasure_real_singleton]
  calc
    (referenceMeasure laws p).real (decodeCell laws ⁻¹' {a}) =
        (referenceMeasure laws p).real (interval laws a) := by
      apply measureReal_congr
      filter_upwards [ae_decodeCell_mem_interval_referenceMeasure laws p] with x hx
      apply propext
      change decodeCell laws x = a ↔ x ∈ interval laws a
      constructor
      · intro h
        exact h ▸ hx
      · exact decodeCell_of_mem_interval laws
    _ = p.prob a := by
      rw [measureReal_def, referenceMeasure_interval, ENNReal.toReal_ofReal (p.prob_nonneg a)]

/-- The fallback region has zero mass for every actual chart law. -/
theorem chartMeasure_compl_iUnion_interval (laws : ι → FinDist (Option ℕ)) (i : ι) :
    chartMeasure laws i (⋃ a : Cell laws, interval laws a)ᶜ = 0 :=
  referenceMeasure_compl_iUnion_interval laws (cellLaw laws i)

theorem chartMeasure_interval (laws : ι → FinDist (Option ℕ)) (i : ι) (a : Cell laws) :
    chartMeasure laws i (interval laws a) = ENNReal.ofReal (ownWeight laws i a) := by
  simpa only [chartMeasure, cellLaw_prob] using referenceMeasure_interval laws (cellLaw laws i) a

theorem ae_decodeCell_mem_interval (laws : ι → FinDist (Option ℕ)) (i : ι) :
    ∀ᵐ x ∂chartMeasure laws i, x ∈ interval laws (decodeCell laws x) :=
  ae_decodeCell_mem_interval_referenceMeasure laws (cellLaw laws i)

/-- The original chart specializes the one reference-cell decoder compiler. -/
theorem chartMeasure_map_decodeCell (laws : ι → FinDist (Option ℕ)) (i : ι) :
    (chartMeasure laws i).map (decodeCell laws) = (cellLaw laws i).toMeasure :=
  referenceMeasure_map_decodeCell laws (cellLaw laws i)

/-- Original clock, not the collapsed real midpoint; Never remains literal top. -/
def decodeClock (laws : ι → FinDist (Option ℕ)) (x : unitInterval) : WithTop ℕ :=
  decodeCell laws x

theorem measurable_decodeClock (laws : ι → FinDist (Option ℕ)) :
    Measurable (decodeClock laws) :=
  measurable_subtype_coe.comp (measurable_decodeCell laws)

/-- Exact pushforward to the same specified source law, not merely its common mixture. -/
theorem chartMeasure_map_decodeClock (laws : ι → FinDist (Option ℕ)) (i : ι) :
    (chartMeasure laws i).map (decodeClock laws) = (sourceClockLaw laws i).toMeasure := by
  rw [show decodeClock laws = Subtype.val ∘ decodeCell laws from rfl,
    ← Measure.map_map measurable_subtype_coe (measurable_decodeCell laws),
    chartMeasure_map_decodeCell, FinDist.toMeasure_map _ _ measurable_subtype_coe,
    cellLaw_map_val]

/-- Product transport first uses the actual finite cell carrier. -/
theorem chartProduct_map_decodeCell (laws : ι → FinDist (Option ℕ)) :
    (Measure.pi (chartMeasure laws)).map (fun x i => decodeCell laws (x i)) =
      (FinDist.pi (cellLaw laws)).toMeasure := by
  rw [Measure.pi_map_pi (fun _ => (measurable_decodeCell laws).aemeasurable)]
  simp only [chartMeasure_map_decodeCell, FinDist.toMeasure_pi]

/-- The full independent source law is recovered without declaring the clock carrier finite. -/
theorem chartProduct_map_decodeClock (laws : ι → FinDist (Option ℕ)) :
    (Measure.pi (chartMeasure laws)).map (fun x i => decodeClock laws (x i)) =
      (FinDist.pi (sourceClockLaw laws)).toMeasure := by
  have hcell : Measurable (fun x : ι → unitInterval => fun i => decodeCell laws (x i)) :=
    Measurable.of_eval fun i => (measurable_decodeCell laws).comp (measurable_pi_apply i)
  have hval : Measurable (fun a : ι → Cell laws => fun i => (a i : WithTop ℕ)) :=
    Measurable.of_eval fun i => measurable_subtype_coe.comp (measurable_pi_apply i)
  rw [show (fun x : ι → unitInterval => fun i => decodeClock laws (x i)) =
      (fun a : ι → Cell laws => fun i => (a i : WithTop ℕ)) ∘
        (fun x : ι → unitInterval => fun i => decodeCell laws (x i)) from rfl,
    ← Measure.map_map hval hcell, chartProduct_map_decodeCell,
    FinDist.toMeasure_map _ _ hval, ← FinDist.pi_map]
  apply congrArg FinDist.toMeasure
  apply congrArg FinDist.pi
  funext i
  exact cellLaw_map_val laws i

/-- Cumulative mass strictly below an original clock, computed from the actual mixture cells. -/
def cumulativeMass (laws : ι → FinDist (Option ℕ)) (clock : WithTop ℕ) : ℝ :=
  ∑ a : Cell laws, if (a : WithTop ℕ) < clock then weight laws a else 0

theorem cumulativeMass_nonneg (laws : ι → FinDist (Option ℕ)) (clock : WithTop ℕ) :
    0 ≤ cumulativeMass laws clock := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact (weight_pos laws a).le
  · exact le_rfl

theorem cumulativeMass_le_one (laws : ι → FinDist (Option ℕ)) (clock : WithTop ℕ) :
    cumulativeMass laws clock ≤ 1 := by
  rw [← sum_weight laws]
  apply Finset.sum_le_sum
  intro a _
  split_ifs
  · exact le_rfl
  · exact (weight_pos laws a).le

theorem cumulativeMass_mono (laws : ι → FinDist (Option ℕ)) :
    Monotone (cumulativeMass laws) := by
  intro first second hle
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : (a : WithTop ℕ) < first
  · simp only [ha, ha.trans_le hle, ite_true, le_refl]
  · simp only [ha, ite_false]
    split_ifs
    · exact (weight_pos laws a).le
    · exact le_rfl

theorem cumulativeMass_cell (laws : ι → FinDist (Option ℕ)) (a : Cell laws) :
    cumulativeMass laws a = left laws a := rfl

/-- The finite cutoff is the actual mixture mass of finite original clocks. -/
def cutoff (laws : ι → FinDist (Option ℕ)) : unitInterval :=
  ⟨cumulativeMass laws ⊤, cumulativeMass_nonneg laws ⊤, cumulativeMass_le_one laws ⊤⟩

theorem cutoff_eq_left_of_top (laws : ι → FinDist (Option ℕ)) (a : Cell laws)
    (ha : (a : WithTop ℕ) = ⊤) : (cutoff laws : ℝ) = left laws a := by
  change cumulativeMass laws ⊤ = left laws a
  rw [← ha, cumulativeMass_cell]

theorem cutoff_eq_one_sub_never (laws : ι → FinDist (Option ℕ)) :
    (cutoff laws : ℝ) = 1 - (averageClockLaw laws).prob ⊤ := by
  classical
  by_cases htop : ⊤ ∈ (averageClockLaw laws).supportFinset
  · let a : Cell laws := ⟨⊤, htop⟩
    have hright : right laws a = 1 := by
      rw [right_eq_sum_le]
      have hall (b : Cell laws) : b ≤ a := show (b : WithTop ℕ) ≤ ⊤ from le_top
      simp only [hall, ite_true, sum_weight]
    have hcut := cutoff_eq_left_of_top laws a rfl
    change left laws a + (averageClockLaw laws).prob ⊤ = 1 at hright
    linarith
  · have hzero : (averageClockLaw laws).prob ⊤ = 0 :=
      FinDist.prob_eq_zero_iff.mpr fun h => htop (FinDist.mem_supportFinset.mpr h)
    have hall (a : Cell laws) : (a : WithTop ℕ) < ⊤ :=
      lt_top_iff_ne_top.mpr fun h => htop (h ▸ a.property)
    simp only [cutoff, cumulativeMass, hall, ite_true, sum_weight, hzero, sub_zero]

theorem right_le_cumulativeMass (laws : ι → FinDist (Option ℕ)) (a : Cell laws)
    {clock : WithTop ℕ} (ha : (a : WithTop ℕ) < clock) :
    right laws a ≤ cumulativeMass laws clock := by
  rw [right_eq_sum_le, cumulativeMass]
  apply Finset.sum_le_sum
  intro b _
  by_cases hba : b ≤ a
  · have hb : (b : WithTop ℕ) < clock :=
      (show (b : WithTop ℕ) ≤ a from hba).trans_lt ha
    simp only [hba, hb, ite_true, le_refl]
  · simp only [hba, ite_false]
    split_ifs
    · exact (weight_pos laws b).le
    · exact le_rfl

theorem right_le_cutoff (laws : ι → FinDist (Option ℕ)) (a : Cell laws)
    (ha : (a : WithTop ℕ) ≠ ⊤) : right laws a ≤ (cutoff laws : ℝ) :=
  right_le_cumulativeMass laws a (lt_top_iff_ne_top.mpr ha)

/-- Endpoints of the actual positive cells, together with the boundary and finite cutoff. -/
def endpointSet (laws : ι → FinDist (Option ℕ)) : Set ℝ :=
  insert 0 (insert 1 (insert (cutoff laws : ℝ) (range (left laws) ∪ range (right laws))))

theorem finite_endpointSet (laws : ι → FinDist (Option ℕ)) : (endpointSet laws).Finite :=
  (((finite_range (left laws)).union (finite_range (right laws))).insert _).insert _ |>.insert _

theorem endpointSet_subset (laws : ι → FinDist (Option ℕ)) :
    endpointSet laws ⊆ Icc (0 : ℝ) 1 := by
  intro y hy
  simp only [endpointSet, mem_insert_iff, mem_union, mem_range] at hy
  rcases hy with rfl | rfl | rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · exact (cutoff laws).property
  · exact ⟨left_nonneg laws a, (left_lt_right laws a).le.trans (right_le_one laws a)⟩
  · exact ⟨(left_nonneg laws a).trans (left_lt_right laws a).le, right_le_one laws a⟩

/-- The actual finite-law calendar, without supplied geometric or endpoint restrictions. -/
def calendar (laws : ι → FinDist (Option ℕ)) : MathUE.MarkedCalendar.Calendar where
  endpoints := ⟨⟨endpointSet laws, (finite_endpointSet laws).isCompact⟩,
    ⟨0, mem_insert _ _⟩⟩
  cutoff := cutoff laws
  endpoints_subset := endpointSet_subset laws
  zero_mem := mem_insert _ _
  one_mem := mem_insert_of_mem _ (mem_insert _ _)
  cutoff_mem := mem_insert_of_mem _ (mem_insert_of_mem _ (mem_insert _ _))

theorem isGap_interval (laws : ι → FinDist (Option ℕ)) (a : Cell laws) :
    Math.Topology.IsGap (calendar laws).endpoints (left laws a) (right laws a) := by
  have hleft : left laws a ∈ endpointSet laws := by
    simp only [endpointSet, mem_insert_iff, mem_union, mem_range]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩)))
  have hright : right laws a ∈ endpointSet laws := by
    simp only [endpointSet, mem_insert_iff, mem_union, mem_range]
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, rfl⟩)))
  refine ⟨hleft, hright, left_lt_right laws a, ?_⟩
  intro y hy
  change y ∈ endpointSet laws at hy
  simp only [endpointSet, mem_insert_iff, mem_union, mem_range] at hy
  rcases hy with rfl | rfl | rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact Or.inl (left_nonneg laws a)
  · exact Or.inr (right_le_one laws a)
  · by_cases ha : (a : WithTop ℕ) = ⊤
    · exact Or.inl (cutoff_eq_left_of_top laws a ha).le
    · exact Or.inr (right_le_cutoff laws a ha)
  · rcases lt_trichotomy b a with h | rfl | h
    · exact Or.inl ((left_lt_right laws b).le.trans (right_le_left_of_lt laws h))
    · exact Or.inl le_rfl
    · exact Or.inr (right_le_left_of_lt laws h)
  · rcases lt_trichotomy b a with h | rfl | h
    · exact Or.inl (right_le_left_of_lt laws h)
    · exact Or.inr le_rfl
    · exact Or.inr ((right_le_left_of_lt laws h).trans (left_lt_right laws b).le)

/-- The finite atom midpoint, or literal Never, attached to an actual source cell. -/
def cellMark (laws : ι → FinDist (Option ℕ)) (a : Cell laws) : WithTop ℝ :=
  if (a : WithTop ℕ) = ⊤ then ⊤ else ((left laws a + right laws a) / 2 : ℝ)

theorem collapseClock_of_mem_cellInterior (laws : ι → FinDist (Option ℕ))
    (a : Cell laws) {x : unitInterval} (hleft : left laws a < (x : ℝ))
    (hright : (x : ℝ) < right laws a) :
    (calendar laws).collapseClock x = cellMark laws a := by
  by_cases ha : (a : WithTop ℕ) = ⊤
  · have hcut : (calendar laws).cutoff ≤ x := by
      change (cutoff laws : ℝ) ≤ (x : ℝ)
      rw [cutoff_eq_left_of_top laws a ha]
      exact hleft.le
    simp only [MathUE.MarkedCalendar.Calendar.collapseClock, hcut, ite_true,
      cellMark, ha]
  · have hcut : ¬(calendar laws).cutoff ≤ x := by
      change ¬(cutoff laws : ℝ) ≤ (x : ℝ)
      exact not_le_of_gt (hright.trans_le (right_le_cutoff laws a ha))
    simp only [MathUE.MarkedCalendar.Calendar.collapseClock, hcut, ite_false,
      cellMark, ha, (calendar laws).midpointClock_of_gap (isGap_interval laws a) hleft hright]

/-- Agreement follows from actual cell gaps; only cell endpoints and the null fallback
are removed. -/
theorem ae_collapseClock_eq_cellMark_decodeCell (laws : ι → FinDist (Option ℕ)) :
    (calendar laws).collapseClock =ᵐ[(volume : Measure unitInterval)]
      fun x => cellMark laws (decodeCell laws x) := by
  have hne : ∀ᵐ x : unitInterval ∂volume, ∀ a : Cell laws, x ≠ leftPoint laws a :=
    ae_all_iff.mpr fun a => volume.ae_ne (leftPoint laws a)
  filter_upwards [ae_mem_interval laws, hne] with x hx hne
  obtain ⟨a, ha⟩ := hx
  rw [decodeCell_of_mem_interval laws ha]
  have hleft : left laws a ≠ (x : ℝ) := fun h => hne a (Subtype.ext h.symm)
  exact collapseClock_of_mem_cellInterior laws a
    (lt_of_le_of_ne ha.1 hleft) ha.2

theorem chartMeasure_map_collapseClock_cellLaw (laws : ι → FinDist (Option ℕ)) (i : ι) :
    (chartMeasure laws i).map (calendar laws).collapseClock =
      ((cellLaw laws i).map (cellMark laws)).toMeasure := by
  have hae : (calendar laws).collapseClock =ᵐ[chartMeasure laws i]
      fun x => cellMark laws (decodeCell laws x) :=
    (withDensity_absolutelyContinuous volume
      (fun x => ENNReal.ofReal (density laws i x))).ae_le
        (ae_collapseClock_eq_cellMark_decodeCell laws)
  rw [Measure.map_congr hae]
  change (chartMeasure laws i).map (cellMark laws ∘ decodeCell laws) = _
  rw [← Measure.map_map (measurable_of_countable (cellMark laws))
    (measurable_decodeCell laws), chartMeasure_map_decodeCell,
    FinDist.toMeasure_map _ _ (measurable_of_countable (cellMark laws))]

/-- The actual finite reply mark: mass strictly earlier, plus half the mass tied at that date. -/
def mark (laws : ι → FinDist (Option ℕ)) (time : ℕ) : ℝ :=
  cumulativeMass laws time + (averageClockLaw laws).prob time / 2

theorem mark_nonneg (laws : ι → FinDist (Option ℕ)) (time : ℕ) : 0 ≤ mark laws time :=
  add_nonneg (cumulativeMass_nonneg laws time)
    (div_nonneg ((averageClockLaw laws).prob_nonneg time) (by norm_num))

theorem mark_eq_midpoint (laws : ι → FinDist (Option ℕ)) (a : Cell laws)
    {time : ℕ} (ha : (a : WithTop ℕ) = time) :
    mark laws time = (left laws a + right laws a) / 2 := by
  rw [mark, ← ha, cumulativeMass_cell]
  change left laws a + weight laws a / 2 = (left laws a + right laws a) / 2
  rw [right]
  ring

theorem cumulativeMass_eq_left_of_least (laws : ι → FinDist (Option ℕ))
    (clock : WithTop ℕ) (a : Cell laws) (ha : clock ≤ a)
    (hleast : ∀ b : Cell laws, clock ≤ b → a ≤ b) :
    cumulativeMass laws clock = left laws a := by
  apply Finset.sum_congr rfl
  intro b _
  have hiff : (b : WithTop ℕ) < clock ↔ b < a := by
    constructor
    · intro hb
      exact hb.trans_le ha
    · intro hb
      by_contra hnot
      exact (not_le_of_gt hb) (hleast b (le_of_not_gt hnot))
  simp only [hiff]

/-- Unsupported replies lie at an actual endpoint, including the finite terminal cutoff. -/
theorem mark_eq_left_or_cutoff_of_not_supported (laws : ι → FinDist (Option ℕ))
    (time : ℕ) (htime : (time : WithTop ℕ) ∉ (averageClockLaw laws).supportFinset) :
    (∃ a : Cell laws, (time : WithTop ℕ) < a ∧
      (∀ b : Cell laws, (time : WithTop ℕ) ≤ b → a ≤ b) ∧
      mark laws time = left laws a) ∨ mark laws time = (cutoff laws : ℝ) := by
  classical
  have hzero : (averageClockLaw laws).prob time = 0 :=
    FinDist.prob_eq_zero_iff.mpr fun h => htime (FinDist.mem_supportFinset.mpr h)
  have hmark : mark laws time = cumulativeMass laws time := by
    rw [mark, hzero, zero_div, add_zero]
  let later : Finset (Cell laws) := Finset.univ.filter
    fun a : Cell laws => (time : WithTop ℕ) ≤ (a : WithTop ℕ)
  by_cases hlater : later.Nonempty
  · let a : Cell laws := later.min' hlater
    have ha : (time : WithTop ℕ) ≤ a := (Finset.mem_filter.mp (later.min'_mem hlater)).2
    have hleast (b : Cell laws) (hb : (time : WithTop ℕ) ≤ b) : a ≤ b :=
      later.min'_le b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)
    have hlt : (time : WithTop ℕ) < a := lt_of_le_of_ne ha fun h =>
      htime (h.symm ▸ a.property)
    exact Or.inl ⟨a, hlt, hleast,
      hmark.trans (cumulativeMass_eq_left_of_least laws time a ha hleast)⟩
  · have hall (a : Cell laws) : (a : WithTop ℕ) < time := by
      by_contra ha
      exact hlater ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, le_of_not_gt ha⟩⟩
    have halltop (a : Cell laws) : (a : WithTop ℕ) < ⊤ := (hall a).trans_le le_top
    right
    rw [hmark]
    simp only [cutoff, cumulativeMass, hall, halltop, ite_true]

theorem mark_le_cutoff (laws : ι → FinDist (Option ℕ)) (time : ℕ) :
    mark laws time ≤ (cutoff laws : ℝ) := by
  classical
  by_cases htime : (time : WithTop ℕ) ∈ (averageClockLaw laws).supportFinset
  · let a : Cell laws := ⟨time, htime⟩
    rw [mark_eq_midpoint laws a rfl]
    have hright := right_le_cutoff laws a (WithTop.coe_ne_top)
    have hleft := left_lt_right laws a
    linarith
  · rcases mark_eq_left_or_cutoff_of_not_supported laws time htime with
      ⟨a, _, _, heq⟩ | heq
    · rw [heq]
      by_cases ha : (a : WithTop ℕ) = ⊤
      · exact (cutoff_eq_left_of_top laws a ha).ge
      · exact (left_lt_right laws a).le.trans (right_le_cutoff laws a ha)
    · exact heq.le

theorem atomCompatible_mark (laws : ι → FinDist (Option ℕ)) (time : ℕ) :
    (calendar laws).AtomCompatible (mark laws time) := by
  classical
  refine ⟨⟨mark_nonneg laws time, mark_le_cutoff laws time⟩, ?_⟩
  intro first last hgap hfirst hlast
  by_cases htime : (time : WithTop ℕ) ∈ (averageClockLaw laws).supportFinset
  · let a : Cell laws := ⟨time, htime⟩
    let x : unitInterval := ⟨mark laws time, mark_nonneg laws time,
      (mark_le_cutoff laws time).trans (cutoff laws).property.2⟩
    have hmark := mark_eq_midpoint laws a rfl
    have hwidth := left_lt_right laws a
    have hleft : left laws a < (x : ℝ) := by change left laws a < mark laws time; linarith
    have hright : (x : ℝ) < right laws a := by change mark laws time < right laws a; linarith
    have hcell := (calendar laws).midpointClock_of_gap (isGap_interval laws a) hleft hright
    have hother := (calendar laws).midpointClock_of_gap hgap
      (x := x) hfirst hlast
    exact hmark.trans (hcell.symm.trans hother)
  · have hmem : mark laws time ∈ (calendar laws).endpoints := by
      change mark laws time ∈ endpointSet laws
      rcases mark_eq_left_or_cutoff_of_not_supported laws time htime with
          ⟨a, _, _, heq⟩ | heq
      · rw [heq]
        simp only [endpointSet, mem_insert_iff, mem_union, mem_range]
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩)))
      · rw [heq]
        exact (calendar laws).cutoff_mem
    rcases hgap.2.2.2 _ hmem with h | h
    · exact (not_le_of_gt hfirst h).elim
    · exact (not_le_of_gt hlast h).elim

/-- Mark finite original dates and preserve literal Never, independently of legal-menu selection. -/
def markedClock (laws : ι → FinDist (Option ℕ)) : WithTop ℕ → WithTop ℝ :=
  WithTop.map (mark laws)

theorem markedClock_cell (laws : ι → FinDist (Option ℕ)) (a : Cell laws) :
    markedClock laws a = cellMark laws a := by
  by_cases ha : (a : WithTop ℕ) = ⊤
  · simp only [markedClock, ha, WithTop.map_top, cellMark, ite_true]
  · rw [cellMark, ite_eq_right ha]
    obtain ⟨time, htime⟩ := WithTop.ne_top_iff_exists.mp ha
    change WithTop.map (mark laws) (a : WithTop ℕ) = _
    rw [← htime, WithTop.map_coe, mark_eq_midpoint laws a htime.symm]

theorem ae_collapseClock_eq_marked_decodeClock (laws : ι → FinDist (Option ℕ)) :
    (calendar laws).collapseClock =ᵐ[(volume : Measure unitInterval)]
      fun x => markedClock laws (decodeClock laws x) := by
  filter_upwards [ae_collapseClock_eq_cellMark_decodeCell laws] with x hx
  exact hx.trans (markedClock_cell laws (decodeCell laws x)).symm

/-- Exact scalar marked-law pushforward from the same original finite stopping law. -/
theorem chartMeasure_map_collapseClock (laws : ι → FinDist (Option ℕ)) (i : ι) :
    (chartMeasure laws i).map (calendar laws).collapseClock =
      ((sourceClockLaw laws i).map (markedClock laws)).toMeasure := by
  have hae : (calendar laws).collapseClock =ᵐ[chartMeasure laws i]
      fun x => markedClock laws (decodeClock laws x) :=
    (withDensity_absolutelyContinuous volume
      (fun x => ENNReal.ofReal (density laws i x))).ae_le
        (ae_collapseClock_eq_marked_decodeClock laws)
  rw [Measure.map_congr hae]
  change (chartMeasure laws i).map (markedClock laws ∘ decodeClock laws) = _
  rw [← Measure.map_map (measurable_of_countable (markedClock laws))
    (measurable_decodeClock laws), chartMeasure_map_decodeClock,
    FinDist.toMeasure_map _ _ (measurable_of_countable (markedClock laws))]

/-- Exact independent marked-law pushforward, retaining the specified original marginals. -/
theorem chartProduct_map_collapseClock (laws : ι → FinDist (Option ℕ)) :
    (Measure.pi (chartMeasure laws)).map (fun x i => (calendar laws).collapseClock (x i)) =
      (FinDist.pi fun i => (sourceClockLaw laws i).map (markedClock laws)).toMeasure := by
  have hscalar (i : ι) : (calendar laws).collapseClock =ᵐ[chartMeasure laws i]
      fun x => markedClock laws (decodeClock laws x) :=
    (withDensity_absolutelyContinuous volume
      (fun x => ENNReal.ofReal (density laws i x))).ae_le
        (ae_collapseClock_eq_marked_decodeClock laws)
  have hae : (fun x : ι → unitInterval => fun i => (calendar laws).collapseClock (x i))
      =ᵐ[Measure.pi (chartMeasure laws)]
      fun x i => markedClock laws (decodeClock laws (x i)) := by
    have heach (i : ι) :=
      (measurePreserving_eval (chartMeasure laws) i).quasiMeasurePreserving.ae (hscalar i)
    filter_upwards [ae_all_iff.mpr heach] with x hx
    exact funext hx
  have hdecode : Measurable (fun x : ι → unitInterval => fun i => decodeClock laws (x i)) :=
    Measurable.of_eval fun i => (measurable_decodeClock laws).comp (measurable_pi_apply i)
  have hmark : Measurable (fun x : ι → WithTop ℕ => fun i => markedClock laws (x i)) :=
    Measurable.of_eval fun i =>
      (measurable_of_countable (markedClock laws)).comp (measurable_pi_apply i)
  rw [Measure.map_congr hae]
  change (Measure.pi (chartMeasure laws)).map
    ((fun x : ι → WithTop ℕ => fun i => markedClock laws (x i)) ∘
      (fun x : ι → unitInterval => fun i => decodeClock laws (x i))) = _
  rw [← Measure.map_map hmark hdecode, chartProduct_map_decodeClock,
    FinDist.toMeasure_map _ _ hmark, ← FinDist.pi_map]

theorem mem_calendar_of_mem_average_support (laws : ι → FinDist (Option ℕ))
    (time : ℕ) (htime : (time : WithTop ℕ) ∈ (averageClockLaw laws).support) :
    time ∈ quittingFiniteStoppingCalendar laws := by
  rw [averageClockLaw, FinDist.support_bind] at htime
  obtain ⟨i, hi⟩ := mem_iUnion.mp htime
  obtain ⟨_, hsource⟩ := mem_iUnion.mp hi
  rw [sourceClockLaw, FinDist.support_map] at hsource
  obtain ⟨choice, hchoice, hvalue⟩ := hsource
  cases choice with
  | none => exact (WithTop.top_ne_coe hvalue).elim
  | some date =>
      have hdate : date = time := WithTop.coe_injective hvalue
      subst date
      exact mem_quittingFiniteStoppingCalendar_of_mem_support laws i time hchoice

/-- The representative preserves the actual mark even when it is an unsupported successor. -/
theorem mark_atomGapRepresentative (laws : ι → FinDist (Option ℕ)) (time : ℕ) :
    mark laws (quittingAtomGapRepresentative (quittingFiniteStoppingCalendar laws) time) =
      mark laws time := by
  classical
  let dates := quittingFiniteStoppingCalendar laws
  let representative := quittingAtomGapRepresentative dates time
  by_cases htime : time ∈ dates
  · change mark laws (quittingAtomGapRepresentative dates time) = mark laws time
    rw [quittingAtomGapRepresentative, ite_eq_left htime]
  · have hrep : representative ∉ dates := by
      intro h
      have hle := (quittingAtom_le_atomGapRepresentative_iff dates h).mp le_rfl
      have hge := (quittingAtomGapRepresentative_le_atom_iff dates h).mp le_rfl
      exact htime (le_antisymm hle hge ▸ h)
    have hzero (date : ℕ) (hd : date ∉ dates) :
        (averageClockLaw laws).prob date = 0 :=
      FinDist.prob_eq_zero_iff.mpr fun h => hd (mem_calendar_of_mem_average_support laws date h)
    change mark laws representative = mark laws time
    rw [mark, mark, hzero representative hrep, hzero time htime,
      zero_div, add_zero, add_zero]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : (a : WithTop ℕ) = ⊤
    · simp only [ha, not_top_lt, ite_false]
    · obtain ⟨atom, hatom⟩ := WithTop.ne_top_iff_exists.mp ha
      have hsupported : (atom : WithTop ℕ) ∈ (averageClockLaw laws).support := by
        exact (congrArg (fun clock : WithTop ℕ => clock ∈ (averageClockLaw laws).support)
          hatom).mpr (FinDist.mem_supportFinset.mp a.property)
      have hmem : atom ∈ dates := mem_calendar_of_mem_average_support laws atom hsupported
      have hlt : atom < representative ↔ atom < time := by
        rw [lt_iff_not_ge, lt_iff_not_ge,
          quittingAtomGapRepresentative_le_atom_iff dates hmem]
      have hcompare : (a : WithTop ℕ) < representative ↔ (a : WithTop ℕ) < time := by
        rw [← hatom]
        exact WithTop.coe_lt_coe.trans (hlt.trans WithTop.coe_lt_coe.symm)
      simp only [hcompare]

/-- Only images of actual finite entries of the source reply menu are legal finite marks. -/
def legalFiniteMenu (laws : ι → FinDist (Option ℕ)) : Finset ℝ := by
  classical
  exact (quittingFiniteOpponentAtomGapReplyMenu (quittingFiniteStoppingCalendar laws)).biUnion
    fun choice => choice.elim ∅ (fun time => {mark laws time})

theorem mem_legalFiniteMenu_iff (laws : ι → FinDist (Option ℕ)) (r : ℝ) :
    r ∈ legalFiniteMenu laws ↔ ∃ time : ℕ,
      some time ∈ quittingFiniteOpponentAtomGapReplyMenu (quittingFiniteStoppingCalendar laws) ∧
      r = mark laws time := by
  classical
  constructor
  · intro hr
    obtain ⟨choice, hchoice, hr⟩ := Finset.mem_biUnion.mp hr
    cases choice with
    | none => exact (Finset.notMem_empty _ hr).elim
    | some time => exact ⟨time, hchoice, Finset.mem_singleton.mp hr⟩
  · rintro ⟨time, htime, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨some time, htime, Finset.mem_singleton_self _⟩

/-- Every original finite response is represented, without adding other compatible endpoints. -/
theorem range_mark_eq_legalFiniteMenu (laws : ι → FinDist (Option ℕ)) :
    range (mark laws) = (legalFiniteMenu laws : Set ℝ) := by
  ext r
  constructor
  · rintro ⟨time, rfl⟩
    apply (mem_legalFiniteMenu_iff laws _).mpr
    exact ⟨quittingAtomGapRepresentative (quittingFiniteStoppingCalendar laws) time,
      quittingAtomGapRepresentative_mem_replyMenu _ _,
      (mark_atomGapRepresentative laws time).symm⟩
  · intro hr
    obtain ⟨time, _, heq⟩ := (mem_legalFiniteMenu_iff laws r).mp hr
    exact ⟨time, heq.symm⟩

theorem atomCompatible_of_mem_legalFiniteMenu (laws : ι → FinDist (Option ℕ))
    {r : ℝ} (hr : r ∈ legalFiniteMenu laws) : (calendar laws).AtomCompatible r := by
  obtain ⟨time, _, rfl⟩ := (mem_legalFiniteMenu_iff laws r).mp hr
  exact atomCompatible_mark laws time

theorem mark_after_calendar_eq_cutoff (laws : ι → FinDist (Option ℕ)) (time : ℕ)
    (hafter : ∀ atom ∈ quittingFiniteStoppingCalendar laws, atom < time) :
    mark laws time = (cutoff laws : ℝ) := by
  have hzero : (averageClockLaw laws).prob time = 0 :=
    FinDist.prob_eq_zero_iff.mpr fun h => (lt_irrefl time)
      (hafter time (mem_calendar_of_mem_average_support laws time h))
  rw [mark, hzero, zero_div, add_zero]
  change cumulativeMass laws time = cumulativeMass laws ⊤
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : (a : WithTop ℕ) = ⊤
  · simp only [ha, not_top_lt, lt_self_iff_false, ite_false]
  · obtain ⟨atom, hatom⟩ := WithTop.ne_top_iff_exists.mp ha
    have hsupported : (atom : WithTop ℕ) ∈ (averageClockLaw laws).support := by
      exact (congrArg (fun clock : WithTop ℕ => clock ∈ (averageClockLaw laws).support)
        hatom).mpr (FinDist.mem_supportFinset.mp a.property)
    have hmem := mem_calendar_of_mem_average_support laws atom hsupported
    have hlt : (a : WithTop ℕ) < time := by
      rw [← hatom]
      exact WithTop.coe_lt_coe.mpr (hafter atom hmem)
    simp only [hlt, lt_top_iff_ne_top.mpr ha, ite_true]

/-- The finite cutoff is a genuine finite reply, even when every source law is Never. -/
theorem cutoff_mem_legalFiniteMenu (laws : ι → FinDist (Option ℕ)) :
    (cutoff laws : ℝ) ∈ legalFiniteMenu laws := by
  change (cutoff laws : ℝ) ∈ (legalFiniteMenu laws : Set ℝ)
  rw [← range_mark_eq_legalFiniteMenu]
  refine ⟨(quittingFiniteStoppingCalendar laws).sup id + 1, ?_⟩
  apply mark_after_calendar_eq_cutoff
  intro atom hatom
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hatom)

theorem mark_le_cumulativeMass_of_lt (laws : ι → FinDist (Option ℕ))
    {time : ℕ} {clock : WithTop ℕ} (hlt : (time : WithTop ℕ) < clock) :
    mark laws time ≤ cumulativeMass laws clock := by
  classical
  by_cases htime : (time : WithTop ℕ) ∈ (averageClockLaw laws).supportFinset
  · let a : Cell laws := ⟨time, htime⟩
    rw [mark_eq_midpoint laws a rfl]
    have hright := right_le_cumulativeMass laws a hlt
    have hwidth := left_lt_right laws a
    linarith
  · have hzero : (averageClockLaw laws).prob time = 0 :=
      FinDist.prob_eq_zero_iff.mpr fun h => htime (FinDist.mem_supportFinset.mpr h)
    rw [mark, hzero, zero_div, add_zero]
    exact cumulativeMass_mono laws hlt.le

theorem mark_lt_mark_of_supported_left (laws : ι → FinDist (Option ℕ))
    (a : Cell laws) {first last : ℕ} (ha : (a : WithTop ℕ) = first) (hlt : first < last) :
    mark laws first < mark laws last := by
  have hright := right_le_cumulativeMass laws a
    (show (a : WithTop ℕ) < last by rw [ha]; exact WithTop.coe_lt_coe.mpr hlt)
  have hwidth := left_lt_right laws a
  have hmark := mark_eq_midpoint laws a ha
  have hnonneg := (averageClockLaw laws).prob_nonneg last
  unfold mark at *
  linarith

theorem mark_lt_mark_of_supported_right (laws : ι → FinDist (Option ℕ))
    (a : Cell laws) {first last : ℕ} (ha : (a : WithTop ℕ) = last) (hlt : first < last) :
    mark laws first < mark laws last := by
  have hleft := mark_le_cumulativeMass_of_lt laws
    (time := first) (clock := last) (WithTop.coe_lt_coe.mpr hlt)
  have hcum : cumulativeMass laws last = left laws a := by rw [← ha, cumulativeMass_cell]
  rw [hcum] at hleft
  have hwidth := left_lt_right laws a
  have hmark := mark_eq_midpoint laws a ha
  linarith

/-- Order reflection holds against an actual supported clock, not between arbitrary gap dates. -/
theorem cellMark_le_mark_iff (laws : ι → FinDist (Option ℕ)) (a : Cell laws) (time : ℕ) :
    cellMark laws a ≤ (mark laws time : WithTop ℝ) ↔ (a : WithTop ℕ) ≤ time := by
  by_cases ha : (a : WithTop ℕ) = ⊤
  · rw [cellMark, ite_eq_left ha, ha]
    constructor <;> intro h
    · exact (WithTop.coe_ne_top (WithTop.top_le_iff.mp h)).elim
    · exact (WithTop.coe_ne_top (WithTop.top_le_iff.mp h)).elim
  · obtain ⟨atom, hatom⟩ := WithTop.ne_top_iff_exists.mp ha
    rw [← markedClock_cell, markedClock, ← hatom, WithTop.map_coe, WithTop.coe_le_coe]
    refine Iff.trans ?_ WithTop.coe_le_coe.symm
    constructor
    · intro h
      by_contra hnot
      exact (not_le_of_gt (mark_lt_mark_of_supported_right laws a hatom.symm
        (Nat.lt_of_not_ge hnot))) h
    · intro h
      rcases h.eq_or_lt with rfl | hlt
      · exact le_rfl
      · exact (mark_lt_mark_of_supported_left laws a hatom.symm hlt).le

theorem mark_le_cellMark_iff (laws : ι → FinDist (Option ℕ)) (a : Cell laws) (time : ℕ) :
    (mark laws time : WithTop ℝ) ≤ cellMark laws a ↔ (time : WithTop ℕ) ≤ a := by
  by_cases ha : (a : WithTop ℕ) = ⊤
  · simp only [cellMark, ha, ite_true, le_top]
  · obtain ⟨atom, hatom⟩ := WithTop.ne_top_iff_exists.mp ha
    rw [← markedClock_cell, markedClock, ← hatom, WithTop.map_coe, WithTop.coe_le_coe]
    refine Iff.trans ?_ WithTop.coe_le_coe.symm
    constructor
    · intro h
      by_contra hnot
      exact (not_le_of_gt (mark_lt_mark_of_supported_left laws a hatom.symm
        (Nat.lt_of_not_ge hnot))) h
    · intro h
      rcases h.eq_or_lt with rfl | hlt
      · exact le_rfl
      · exact (mark_lt_mark_of_supported_right laws a hatom.symm hlt).le

theorem cellMark_le_cellMark_iff (laws : ι → FinDist (Option ℕ)) (a b : Cell laws) :
    cellMark laws a ≤ cellMark laws b ↔ (a : WithTop ℕ) ≤ b := by
  by_cases hb : (b : WithTop ℕ) = ⊤
  · simp only [cellMark, hb, ite_true, le_top]
  · obtain ⟨atom, hatom⟩ := WithTop.ne_top_iff_exists.mp hb
    have hmark : cellMark laws b = (mark laws atom : WithTop ℝ) := by
      rw [← markedClock_cell, markedClock, ← hatom, WithTop.map_coe]
    rw [hmark, cellMark_le_mark_iff]
    exact Iff.of_eq (congrArg (fun clock : WithTop ℕ => (a : WithTop ℕ) ≤ clock) hatom)

private theorem minimumLabels_eq_originalOutcome_of_order_and_top
    (times : ι → Option ℕ) (clock : ι → WithTop ℝ)
    (htop : ∀ i, clock i = ⊤ ↔ quittingStoppingTimeValue (times i) = ⊤)
    (horder : ∀ i j, clock i ≤ clock j ↔
      quittingStoppingTimeValue (times i) ≤ quittingStoppingTimeValue (times j)) :
    MathUE.MarkedCalendar.minimumLabels clock =
      (quittingFirstStoppingOutcome times).elim ∅ Subtype.val := by
  by_cases hnever : quittingEarliestStoppingValue times = ⊤
  · rw [quittingFirstStoppingOutcome, ite_eq_left hnever, Option.elim_none]
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    have hiNever := (quittingEarliestStoppingValue_eq_top_iff times).mp hnever i
    have hiTop : clock i = ⊤ :=
      (htop i).mpr (by rw [hiNever]; rfl)
    exact (Finset.mem_filter.mp hi).2.1 hiTop
  · rw [quittingFirstStoppingOutcome, ite_eq_right hnever, Option.elim_some]
    ext i
    simp only [MathUE.MarkedCalendar.minimumLabels, Finset.mem_filter,
      Finset.mem_univ, true_and, mem_quittingEarliestStoppingCoalition_iff]
    constructor
    · intro hi j
      exact (horder i j).mp (hi.2 j)
    · intro hleast
      have hcoalition := (mem_quittingEarliestStoppingCoalition_iff times i).mpr hleast
      have hiEq : quittingStoppingTimeValue (times i) = quittingEarliestStoppingValue times :=
        (Finset.mem_filter.mp hcoalition).2
      refine ⟨fun hiTop => hnever (hiEq.symm.trans ((htop i).mp hiTop)), ?_⟩
      intro j
      exact (horder i j).mpr (hleast j)

/-- All supported pairwise comparisons and literal Never status identify the original outcome. -/
theorem minimumLabels_markedClock_eq_originalOutcome
    (laws : ι → FinDist (Option ℕ)) (times : ι → Option ℕ)
    (hsupport : ∀ i, quittingStoppingTimeValue (times i) ∈
      (averageClockLaw laws).supportFinset) :
    MathUE.MarkedCalendar.minimumLabels
        (fun i => markedClock laws (quittingStoppingTimeValue (times i))) =
      (quittingFirstStoppingOutcome times).elim ∅ Subtype.val := by
  apply minimumLabels_eq_originalOutcome_of_order_and_top
  · intro i
    exact WithTop.map_eq_top_iff
  · intro i j
    change markedClock laws (⟨_, hsupport i⟩ : Cell laws) ≤
      markedClock laws (⟨_, hsupport j⟩ : Cell laws) ↔ _
    rw [markedClock_cell, markedClock_cell]
    exact cellMark_le_cellMark_iff laws ⟨_, hsupport i⟩ ⟨_, hsupport j⟩

omit [Fintype ι] [Nonempty ι] in
/-- Empty labels are exactly literal Never; finite terminal coalitions cannot be empty. -/
theorem originalOutcome_labels_eq_empty_iff (outcome : QuittingTerminalOutcome ι) :
    outcome.elim ∅ Subtype.val = ∅ ↔ outcome = none := by
  cases outcome with
  | none => simp only [Option.elim_none]
  | some coalition =>
      simp only [Option.elim_some, Option.some_ne_none, iff_false]
      exact coalition.property.ne_empty

omit [Fintype ι] [Nonempty ι] in
/-- The standard option/nonempty-subtype equivalence encodes literal Never as the empty labels. -/
def outcomeLabelsEquiv : QuittingTerminalOutcome ι ≃ Finset ι := by
  classical
  exact (Equiv.optionCongr (Equiv.subtypeEquivProp
    (funext fun _ : Finset ι => propext Finset.nonempty_iff_ne_empty))).trans
      (Equiv.optionSubtypeNe ∅)

omit [Fintype ι] [Nonempty ι] in
theorem outcomeLabelsEquiv_apply (outcome : QuittingTerminalOutcome ι) :
    outcomeLabelsEquiv outcome = outcome.elim ∅ Subtype.val := by
  cases outcome <;> rfl

omit [Fintype ι] [Nonempty ι] in
/-- The explicit discrete measurable space for the existing terminal-outcome carrier. -/
@[instance_reducible]
def outcomeMeasurableSpace : MeasurableSpace (QuittingTerminalOutcome ι) := ⊤

attribute [local instance] outcomeMeasurableSpace

omit [Fintype ι] [Nonempty ι] in
local instance outcomeMeasurableSingletonClass :
    MeasurableSingletonClass (QuittingTerminalOutcome ι) where
  measurableSet_singleton _ := trivial

/-- Encode the actual chart labels in the existing literal terminal-outcome type. -/
def chartOutcome (laws : ι → FinDist (Option ℕ))
    (sample : ι → unitInterval) : QuittingTerminalOutcome ι :=
  outcomeLabelsEquiv.symm (MathUE.MarkedCalendar.firstLabels (calendar laws) sample)

theorem measurable_chartOutcome (laws : ι → FinDist (Option ℕ)) :
    Measurable (chartOutcome laws) :=
  (measurable_of_countable outcomeLabelsEquiv.symm).comp
    (MathUE.MarkedCalendar.measurable_firstLabels (calendar laws))

theorem chartOutcome_eq_none_iff (laws : ι → FinDist (Option ℕ))
    (sample : ι → unitInterval) :
    chartOutcome laws sample = none ↔
      MathUE.MarkedCalendar.firstLabels (calendar laws) sample = ∅ := by
  rw [chartOutcome, Equiv.symm_apply_eq, outcomeLabelsEquiv_apply, Option.elim_none]

/-- The original stopping choice underlying an ordered clock; top returns literal none. -/
def originalChoice : WithTop ℕ → Option ℕ := WithTop.recTopCoe none some

theorem stoppingTimeValue_originalChoice (clock : WithTop ℕ) :
    quittingStoppingTimeValue (originalChoice clock) = clock := by
  induction clock using WithTop.recTopCoe <;> rfl

theorem originalChoice_stoppingTimeValue (choice : Option ℕ) :
    originalChoice (quittingStoppingTimeValue choice) = choice := by
  cases choice <;> rfl

theorem cellLaw_map_originalChoice (laws : ι → FinDist (Option ℕ)) (i : ι) :
    (cellLaw laws i).map (fun a : Cell laws => originalChoice a) = laws i := by
  change (cellLaw laws i).map (originalChoice ∘ Subtype.val) = _
  rw [← FinDist.map_comp, cellLaw_map_val, sourceClockLaw, FinDist.map_comp]
  have hinverse : originalChoice ∘ quittingStoppingTimeValue = id :=
    funext originalChoice_stoppingTimeValue
  rw [hinverse, FinDist.map_id]

theorem cellProduct_map_originalChoice (laws : ι → FinDist (Option ℕ)) :
    (FinDist.pi (cellLaw laws)).map (fun sample i => originalChoice (sample i)) =
      FinDist.pi laws := by
  calc
    _ = FinDist.pi (fun i => (cellLaw laws i).map
        (fun a : Cell laws => originalChoice a)) :=
      (FinDist.pi_map (fun (_ : ι) (a : Cell laws) => originalChoice a) (cellLaw laws)).symm
    _ = _ := congrArg FinDist.pi (funext fun i => cellLaw_map_originalChoice laws i)

theorem minimumLabels_cellMark_eq_originalOutcome (laws : ι → FinDist (Option ℕ))
    (sample : ι → Cell laws) :
    MathUE.MarkedCalendar.minimumLabels (fun i => cellMark laws (sample i)) =
      outcomeLabelsEquiv
        (quittingFirstStoppingOutcome (fun i => originalChoice (sample i))) := by
  have hsupport (i : ι) : quittingStoppingTimeValue (originalChoice (sample i)) ∈
      (averageClockLaw laws).supportFinset := by
    rw [stoppingTimeValue_originalChoice]
    exact (sample i).property
  have h := minimumLabels_markedClock_eq_originalOutcome laws
    (fun i => originalChoice (sample i)) hsupport
  simpa only [stoppingTimeValue_originalChoice, markedClock_cell,
    outcomeLabelsEquiv_apply] using h

/-- The fixed reference geometry transports every absolutely-continuous latent product.
No original or replacement density is supplied as an outcome oracle. -/
theorem ae_chartOutcome_eq_originalOutcome_of_absolutelyContinuous
    (laws : ι → FinDist (Option ℕ)) (μ : ι → Measure unitInterval)
    [∀ i, SigmaFinite (μ i)] (hμ : ∀ i, μ i ≪ volume) :
    chartOutcome laws =ᵐ[Measure.pi μ]
      fun sample => quittingFirstStoppingOutcome
        (fun i => originalChoice (decodeCell laws (sample i))) := by
  have hscalar (i : ι) : (calendar laws).collapseClock =ᵐ[μ i]
      fun x => cellMark laws (decodeCell laws x) :=
    (hμ i).ae_le (ae_collapseClock_eq_cellMark_decodeCell laws)
  filter_upwards [Measure.ae_eq_pi hscalar] with sample hclock
  unfold chartOutcome MathUE.MarkedCalendar.firstLabels
  rw [hclock, minimumLabels_cellMark_eq_originalOutcome, Equiv.symm_apply_apply]

theorem ae_chartOutcome_eq_originalOutcome (laws : ι → FinDist (Option ℕ)) :
    chartOutcome laws =ᵐ[Measure.pi (chartMeasure laws)]
      fun sample => quittingFirstStoppingOutcome
        (fun i => originalChoice (decodeCell laws (sample i))) :=
  ae_chartOutcome_eq_originalOutcome_of_absolutelyContinuous laws (chartMeasure laws)
    (fun i => referenceMeasure_absolutelyContinuous laws (cellLaw laws i))

/-- Exact first-outcome law from the specified original independent source family.
The equality includes literal none, not just finite coalition probabilities. -/
theorem chartProduct_map_outcome (laws : ι → FinDist (Option ℕ)) :
    (Measure.pi (chartMeasure laws)).map (chartOutcome laws) =
      ((FinDist.pi laws).map quittingFirstStoppingOutcome).toMeasure := by
  let decode := fun sample : ι → unitInterval => fun i => decodeCell laws (sample i)
  let read := fun sample : ι → Cell laws =>
    quittingFirstStoppingOutcome (fun i => originalChoice (sample i))
  have hdecode : Measurable decode :=
    Measurable.of_eval fun i => (measurable_decodeCell laws).comp (measurable_pi_apply i)
  have hae : chartOutcome laws =ᵐ[Measure.pi (chartMeasure laws)] read ∘ decode :=
    ae_chartOutcome_eq_originalOutcome laws
  rw [Measure.map_congr hae,
    ← Measure.map_map (measurable_of_countable read) hdecode,
    chartProduct_map_decodeCell, FinDist.toMeasure_map _ _ (measurable_of_countable read)]
  change ((FinDist.pi (cellLaw laws)).map
    (quittingFirstStoppingOutcome ∘ (fun sample i => originalChoice (sample i)))).toMeasure = _
  rw [← FinDist.map_comp, cellProduct_map_originalChoice]

/-- The chart's literal all-Never event has exactly its original source-outcome mass. -/
theorem chartProduct_real_none (laws : ι → FinDist (Option ℕ)) :
    (Measure.pi (chartMeasure laws)).real {sample | chartOutcome laws sample = none} =
      ((FinDist.pi laws).map quittingFirstStoppingOutcome).prob none := by
  change (Measure.pi (chartMeasure laws)).real (chartOutcome laws ⁻¹' {none}) = _
  rw [← map_measureReal_apply (measurable_chartOutcome laws)
    (measurableSet_singleton (none : QuittingTerminalOutcome ι)),
    chartProduct_map_outcome, FinDist.toMeasure_real_singleton]

/-- An arbitrary original response is compared only against actual supported cells. -/
theorem cellMark_le_replyMark_iff (laws : ι → FinDist (Option ℕ))
    (a : Cell laws) (choice : Option ℕ) :
    cellMark laws a ≤ markedClock laws (quittingStoppingTimeValue choice) ↔
      (a : WithTop ℕ) ≤ quittingStoppingTimeValue choice := by
  cases choice with
  | none => simp only [quittingStoppingTimeValue, markedClock, WithTop.map_top, le_top]
  | some time => exact cellMark_le_mark_iff laws a time

theorem replyMark_le_cellMark_iff (laws : ι → FinDist (Option ℕ))
    (a : Cell laws) (choice : Option ℕ) :
    markedClock laws (quittingStoppingTimeValue choice) ≤ cellMark laws a ↔
      quittingStoppingTimeValue choice ≤ (a : WithTop ℕ) := by
  cases choice with
  | none =>
      rw [← markedClock_cell]
      change ⊤ ≤ WithTop.map (mark laws) (a : WithTop ℕ) ↔ ⊤ ≤ (a : WithTop ℕ)
      simp only [top_le_iff, WithTop.map_eq_top_iff]
  | some time => exact mark_le_cellMark_iff laws a time

section Replies

variable [DecidableEq ι]

/-- Insert any original response, including unsupported finite dates and literal Never. -/
theorem minimumLabels_responseCellClock_eq_originalOutcome
    (laws : ι → FinDist (Option ℕ)) (who : ι) (choice : Option ℕ)
    (sample : {j : ι // j ≠ who} → Cell laws) :
    MathUE.MarkedCalendar.minimumLabels
        ((Equiv.funSplitAt who (WithTop ℝ)).symm
          (markedClock laws (quittingStoppingTimeValue choice),
            fun j => cellMark laws (sample j))) =
      outcomeLabelsEquiv (quittingFirstStoppingOutcome
        ((Equiv.funSplitAt who (Option ℕ)).symm
          (choice, fun j => originalChoice (sample j)))) := by
  rw [outcomeLabelsEquiv_apply]
  apply minimumLabels_eq_originalOutcome_of_order_and_top
  · intro i
    by_cases hi : i = who
    · simp only [Equiv.funSplitAt_symm_apply, dite_eq_left hi]
      exact WithTop.map_eq_top_iff
    · simp only [Equiv.funSplitAt_symm_apply, dite_eq_right hi,
        stoppingTimeValue_originalChoice, ← markedClock_cell]
      exact WithTop.map_eq_top_iff
  · intro i j
    by_cases hi : i = who <;> by_cases hj : j = who
    · simp only [Equiv.funSplitAt_symm_apply, dite_eq_left hi, dite_eq_left hj, le_refl]
    · simp only [Equiv.funSplitAt_symm_apply, dite_eq_left hi, dite_eq_right hj,
        stoppingTimeValue_originalChoice]
      exact replyMark_le_cellMark_iff laws (sample ⟨j, hj⟩) choice
    · simp only [Equiv.funSplitAt_symm_apply, dite_eq_right hi, dite_eq_left hj,
        stoppingTimeValue_originalChoice]
      exact cellMark_le_replyMark_iff laws (sample ⟨i, hi⟩) choice
    · simp only [Equiv.funSplitAt_symm_apply, dite_eq_right hi, dite_eq_right hj,
        stoppingTimeValue_originalChoice]
      exact cellMark_le_cellMark_iff laws (sample ⟨i, hi⟩) (sample ⟨j, hj⟩)

/-- The response uses the unchanged full-source calendar and only the opponents' samples. -/
def chartResponseOutcome (laws : ι → FinDist (Option ℕ)) (who : ι) (choice : Option ℕ)
    (sample : {j : ι // j ≠ who} → unitInterval) : QuittingTerminalOutcome ι :=
  outcomeLabelsEquiv.symm (MathUE.MarkedCalendar.responseLabels (calendar laws) who
    (markedClock laws (quittingStoppingTimeValue choice)) sample)

theorem measurable_chartResponseOutcome (laws : ι → FinDist (Option ℕ))
    (who : ι) (choice : Option ℕ) : Measurable (chartResponseOutcome laws who choice) :=
  (measurable_of_countable outcomeLabelsEquiv.symm).comp
    (MathUE.MarkedCalendar.measurable_responseLabels (calendar laws) who
      (markedClock laws (quittingStoppingTimeValue choice)))

theorem chartResponseOutcome_eq_none_iff (laws : ι → FinDist (Option ℕ))
    (who : ι) (choice : Option ℕ) (sample : {j : ι // j ≠ who} → unitInterval) :
    chartResponseOutcome laws who choice sample = none ↔
      MathUE.MarkedCalendar.responseLabels (calendar laws) who
        (markedClock laws (quittingStoppingTimeValue choice)) sample = ∅ := by
  rw [chartResponseOutcome, Equiv.symm_apply_eq, outcomeLabelsEquiv_apply, Option.elim_none]

/-- Removing one coordinate does not change the actual interval decoder or its laws. -/
theorem chartOpponentProduct_map_decodeCell (laws : ι → FinDist (Option ℕ)) (who : ι) :
    (Measure.pi (fun j : {j : ι // j ≠ who} => chartMeasure laws j.val)).map
        (fun sample j => decodeCell laws (sample j)) =
      (FinDist.pi (fun j : {j : ι // j ≠ who} => cellLaw laws j.val)).toMeasure := by
  rw [Measure.pi_map_pi (fun _ => (measurable_decodeCell laws).aemeasurable)]
  simp only [chartMeasure_map_decodeCell, FinDist.toMeasure_pi]

theorem opponentCellProduct_map_originalChoice (laws : ι → FinDist (Option ℕ)) (who : ι) :
    (FinDist.pi (fun j : {j : ι // j ≠ who} => cellLaw laws j.val)).map
        (fun sample j => originalChoice (sample j)) =
      FinDist.pi (fun j : {j : ι // j ≠ who} => laws j.val) := by
  calc
    _ = FinDist.pi (fun j : {j : ι // j ≠ who} => (cellLaw laws j.val).map
        (fun a : Cell laws => originalChoice a)) :=
      (FinDist.pi_map (fun (_ : {j : ι // j ≠ who}) (a : Cell laws) => originalChoice a)
        (fun j => cellLaw laws j.val)).symm
    _ = _ := congrArg FinDist.pi (funext fun j => cellLaw_map_originalChoice laws j.val)

/-- An arbitrary original response is transported against any absolutely-continuous opponent
product on the old reference chart, including an empty opponent product. -/
theorem ae_chartResponseOutcome_eq_originalOutcome_of_absolutelyContinuous
    (laws : ι → FinDist (Option ℕ)) (who : ι) (choice : Option ℕ)
    (μ : {j : ι // j ≠ who} → Measure unitInterval)
    [∀ j, SigmaFinite (μ j)] (hμ : ∀ j, μ j ≪ volume) :
    chartResponseOutcome laws who choice
      =ᵐ[Measure.pi μ]
      fun sample => quittingFirstStoppingOutcome
        ((Equiv.funSplitAt who (Option ℕ)).symm
          (choice, fun j => originalChoice (decodeCell laws (sample j)))) := by
  have hscalar (j : {j : ι // j ≠ who}) : (calendar laws).collapseClock =ᵐ[μ j]
      fun x => cellMark laws (decodeCell laws x) :=
    (hμ j).ae_le (ae_collapseClock_eq_cellMark_decodeCell laws)
  filter_upwards [Measure.ae_eq_pi hscalar] with sample hsample
  have hclock : MathUE.MarkedCalendar.responseClock (calendar laws) who
      (markedClock laws (quittingStoppingTimeValue choice)) sample =
      (Equiv.funSplitAt who (WithTop ℝ)).symm
        (markedClock laws (quittingStoppingTimeValue choice),
          fun j => cellMark laws (decodeCell laws (sample j))) := by
    funext j
    by_cases hj : j = who
    · simp only [MathUE.MarkedCalendar.responseClock, Equiv.funSplitAt_symm_apply,
        dite_eq_left hj]
    · simpa only [MathUE.MarkedCalendar.responseClock, Equiv.funSplitAt_symm_apply,
        dite_eq_right hj] using congrFun hsample ⟨j, hj⟩
  unfold chartResponseOutcome MathUE.MarkedCalendar.responseLabels
  rw [hclock, minimumLabels_responseCellClock_eq_originalOutcome, Equiv.symm_apply_apply]

theorem ae_chartResponseOutcome_eq_originalOutcome (laws : ι → FinDist (Option ℕ))
    (who : ι) (choice : Option ℕ) :
    chartResponseOutcome laws who choice
      =ᵐ[Measure.pi (fun j : {j : ι // j ≠ who} => chartMeasure laws j.val)]
      fun sample => quittingFirstStoppingOutcome
        ((Equiv.funSplitAt who (Option ℕ)).symm
          (choice, fun j => originalChoice (decodeCell laws (sample j)))) :=
  ae_chartResponseOutcome_eq_originalOutcome_of_absolutelyContinuous laws who choice
    (fun j => chartMeasure laws j.val)
    (fun j => referenceMeasure_absolutelyContinuous laws (cellLaw laws j.val))

/-- Exact response law with the original independent opponents, including an empty opponent set. -/
theorem chartOpponentProduct_map_responseOutcome (laws : ι → FinDist (Option ℕ))
    (who : ι) (choice : Option ℕ) :
    (Measure.pi (fun j : {j : ι // j ≠ who} => chartMeasure laws j.val)).map
        (chartResponseOutcome laws who choice) =
      ((FinDist.pi (fun j : {j : ι // j ≠ who} => laws j.val)).map
        (fun times => quittingFirstStoppingOutcome
          ((Equiv.funSplitAt who (Option ℕ)).symm (choice, times)))).toMeasure := by
  let decode := fun sample : {j : ι // j ≠ who} → unitInterval =>
    fun j => decodeCell laws (sample j)
  let read := fun sample : {j : ι // j ≠ who} → Cell laws =>
    quittingFirstStoppingOutcome ((Equiv.funSplitAt who (Option ℕ)).symm
      (choice, fun j => originalChoice (sample j)))
  have hdecode : Measurable decode :=
    Measurable.of_eval fun j => (measurable_decodeCell laws).comp (measurable_pi_apply j)
  have hae : chartResponseOutcome laws who choice
      =ᵐ[Measure.pi (fun j : {j : ι // j ≠ who} => chartMeasure laws j.val)]
      read ∘ decode := ae_chartResponseOutcome_eq_originalOutcome laws who choice
  rw [Measure.map_congr hae,
    ← Measure.map_map (measurable_of_countable read) hdecode,
    chartOpponentProduct_map_decodeCell,
    FinDist.toMeasure_map _ _ (measurable_of_countable read)]
  change ((FinDist.pi (fun j : {j : ι // j ≠ who} => cellLaw laws j.val)).map
    ((fun times => quittingFirstStoppingOutcome
      ((Equiv.funSplitAt who (Option ℕ)).symm (choice, times))) ∘
        (fun sample j => originalChoice (sample j)))).toMeasure = _
  rw [← FinDist.map_comp, opponentCellProduct_map_originalChoice]

omit [Nonempty ι] in
/-- The canonical split of a pure-response update, without any opponent nonemptiness premise. -/
theorem pi_update_pure_eq_map_opponents (laws : ι → FinDist (Option ℕ))
    (who : ι) (choice : Option ℕ) :
    FinDist.pi (Function.update laws who (FinDist.pure choice)) =
      (FinDist.pi (fun j : {j : ι // j ≠ who} => laws j.val)).map
        (fun times => (Equiv.funSplitAt who (Option ℕ)).symm (choice, times)) := by
  rw [FinDist.pi_eq_map_product who, Function.update_self]
  have hother : (fun j : {j : ι // j ≠ who} =>
      Function.update laws who (FinDist.pure choice) j.val) = fun j => laws j.val :=
    funext fun j => Function.update_of_ne j.property _ _
  rw [hother, FinDist.product, FinDist.pure_bind, FinDist.map_comp]
  rfl

/-- Every original pure reply has exactly its original terminal law in the unchanged chart. -/
theorem chartOpponentProduct_map_responseOutcome_update (laws : ι → FinDist (Option ℕ))
    (who : ι) (choice : Option ℕ) :
    (Measure.pi (fun j : {j : ι // j ≠ who} => chartMeasure laws j.val)).map
        (chartResponseOutcome laws who choice) =
      ((FinDist.pi (Function.update laws who (FinDist.pure choice))).map
        quittingFirstStoppingOutcome).toMeasure := by
  rw [chartOpponentProduct_map_responseOutcome, pi_update_pure_eq_map_opponents,
    FinDist.map_comp]
  rfl

/-- Literal Never is retained separately in the exact response-law identity. -/
theorem chartOpponentProduct_real_response_none (laws : ι → FinDist (Option ℕ))
    (who : ι) (choice : Option ℕ) :
    (Measure.pi (fun j : {j : ι // j ≠ who} => chartMeasure laws j.val)).real
        {sample | chartResponseOutcome laws who choice sample = none} =
      ((FinDist.pi (Function.update laws who (FinDist.pure choice))).map
        quittingFirstStoppingOutcome).prob none := by
  change (Measure.pi (fun j : {j : ι // j ≠ who} => chartMeasure laws j.val)).real
    (chartResponseOutcome laws who choice ⁻¹' {none}) = _
  rw [← map_measureReal_apply (measurable_chartResponseOutcome laws who choice)
    (measurableSet_singleton (none : QuittingTerminalOutcome ι)),
    chartOpponentProduct_map_responseOutcome_update, FinDist.toMeasure_real_singleton]

end Replies

end GameTheory.MarkedCalendarChart
