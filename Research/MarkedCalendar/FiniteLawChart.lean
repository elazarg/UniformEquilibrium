import Research.MarkedCalendar.Order
import UniformEquilibrium.Quitting.Terminal.FiniteOpponentAtomGapReplyMenu
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.WithDensity
import GameTheory.Math.Probability.Measure

/-! # Actual finite-law interval charts

The source is an actual finite family of finite stopping laws. Its average
determines positive interval cells, with Never ordered after every finite date.
The base is canonical unit-interval volume, not a supplied density law.

The actual densities give normalized chart laws, pointwise domination, and the
exact common-mixture identity. The interval decoder recovers the same original
laws and their independent product, with fallback confined to a derived-null
complement. Calendar/menu transport, limiting complete caps, and original
variation witnesses remain separate obligations beyond this slice.
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

theorem density_eq_of_mem_interval (laws : ι → FinDist (Option ℕ)) (i : ι)
    {a : Cell laws} {x : unitInterval} (hx : x ∈ interval laws a) :
    density laws i x = ownWeight laws i a / weight laws a := by
  classical
  unfold density
  rw [Finset.sum_eq_single a]
  · exact Set.indicator_of_mem hx _
  · intro b _ hba
    apply Set.indicator_of_notMem
    exact fun hxb => Set.disjoint_left.mp (pairwise_disjoint_interval laws hba) hxb hx
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

theorem density_eq_zero_of_notMem (laws : ι → FinDist (Option ℕ)) (i : ι)
    {x : unitInterval} (hx : ∀ a, x ∉ interval laws a) : density laws i x = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  exact Set.indicator_of_notMem (hx a) _

theorem density_le_card (laws : ι → FinDist (Option ℕ)) (i : ι) (x : unitInterval) :
    density laws i x ≤ (Fintype.card ι : ℝ) := by
  by_cases hx : ∃ a, x ∈ interval laws a
  · obtain ⟨a, ha⟩ := hx
    rw [density_eq_of_mem_interval laws i ha]
    exact (div_le_iff₀ (weight_pos laws a)).mpr (ownWeight_le laws i a)
  · rw [density_eq_zero_of_notMem laws i (not_exists.mp hx)]
    exact Nat.cast_nonneg _

theorem integrable_density (laws : ι → FinDist (Option ℕ)) (i : ι) :
    Integrable (density laws i) (volume : Measure unitInterval) := by
  apply Integrable.of_bound (measurable_density laws i).aestronglyMeasurable (Fintype.card ι)
  apply Eventually.of_forall
  intro x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (density_nonneg laws i x)] using
    density_le_card laws i x

theorem integral_density (laws : ι → FinDist (Option ℕ)) (i : ι) :
    ∫ x, density laws i x ∂(volume : Measure unitInterval) = 1 := by
  unfold density
  rw [integral_finsetSum]
  · rw [← sum_ownWeight laws i]
    apply Finset.sum_congr rfl
    intro a _
    rw [integral_indicator_const _ (measurableSet_interval laws a), measureReal_def,
      volume_interval, ENNReal.toReal_ofReal (weight_pos laws a).le, smul_eq_mul]
    field_simp [(weight_pos laws a).ne']
  · intro a _
    exact (integrable_const _).indicator (measurableSet_interval laws a)

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

/-- The actual density measure constructed from the specified player's original law. -/
def chartMeasure (laws : ι → FinDist (Option ℕ)) (i : ι) : Measure unitInterval :=
  volume.withDensity (fun x => ENNReal.ofReal (density laws i x))

instance chartMeasure_isProbability (laws : ι → FinDist (Option ℕ)) (i : ι) :
    IsProbabilityMeasure (chartMeasure laws i) where
  measure_univ := by
    rw [chartMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_density laws i)
        (Eventually.of_forall (density_nonneg laws i)), integral_density, ENNReal.ofReal_one]

/-- The normalized actual chart law, not a supplied density or probability oracle. -/
def chartLaw (laws : ι → FinDist (Option ℕ)) (i : ι) : ProbabilityMeasure unitInterval :=
  ⟨chartMeasure laws i, inferInstance⟩

/-- Canonical Lebesgue probability on the unit interval. -/
def base : ProbabilityMeasure unitInterval := ⟨volume, inferInstance⟩

theorem chartMeasure_le (laws : ι → FinDist (Option ℕ)) (i : ι) :
    chartMeasure laws i ≤ (Fintype.card ι : ENNReal) • (volume : Measure unitInterval) := by
  calc
    chartMeasure laws i ≤ volume.withDensity
        (fun _ : unitInterval => ENNReal.ofReal (Fintype.card ι : ℝ)) := by
      exact withDensity_mono (Eventually.of_forall fun x =>
        ENNReal.ofReal_le_ofReal (density_le_card laws i x))
    _ = _ := by rw [withDensity_const]; simp only [ENNReal.ofReal_natCast]

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
        simpa only [chartMeasure, tsum_fintype, Measure.sum_fintype] using
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

/-- The finite source law on its actual common positive-cell carrier. -/
def cellLaw (laws : ι → FinDist (Option ℕ)) (i : ι) : FinDist (Cell laws) :=
  FinDist.ofWeights (ownWeight laws i) (ownWeight_nonneg laws i) (sum_ownWeight laws i)

theorem cellLaw_prob (laws : ι → FinDist (Option ℕ)) (i : ι) (a : Cell laws) :
    (cellLaw laws i).prob a = ownWeight laws i a := FinDist.prob_ofWeights ..

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

/-- The fallback region has zero mass for every actual chart law. -/
theorem chartMeasure_compl_iUnion_interval (laws : ι → FinDist (Option ℕ)) (i : ι) :
    chartMeasure laws i (⋃ a : Cell laws, interval laws a)ᶜ = 0 := by
  apply (withDensity_absolutelyContinuous volume
    (fun x => ENNReal.ofReal (density laws i x)))
  rw [measure_compl (MeasurableSet.iUnion (measurableSet_interval laws))
    (measure_ne_top _ _), volume_iUnion_interval, measure_univ, tsub_self]

theorem chartMeasure_interval (laws : ι → FinDist (Option ℕ)) (i : ι) (a : Cell laws) :
    chartMeasure laws i (interval laws a) = ENNReal.ofReal (ownWeight laws i a) := by
  rw [chartMeasure, withDensity_apply _ (measurableSet_interval laws a)]
  calc
    ∫⁻ x in interval laws a, ENNReal.ofReal (density laws i x) ∂volume =
        ∫⁻ _ in interval laws a,
          ENNReal.ofReal (ownWeight laws i a / weight laws a) ∂volume := by
      apply setLIntegral_congr_fun (measurableSet_interval laws a)
      intro x hx
      change ENNReal.ofReal (density laws i x) =
        ENNReal.ofReal (ownWeight laws i a / weight laws a)
      rw [density_eq_of_mem_interval laws i hx]
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, volume_interval,
        ← ENNReal.ofReal_mul (div_nonneg (ownWeight_nonneg laws i a)
          (weight_pos laws a).le), div_mul_cancel₀ _ (weight_pos laws a).ne']

theorem ae_decodeCell_mem_interval (laws : ι → FinDist (Option ℕ)) (i : ι) :
    ∀ᵐ x ∂chartMeasure laws i, x ∈ interval laws (decodeCell laws x) := by
  have hmem := (withDensity_absolutelyContinuous volume
    (fun x => ENNReal.ofReal (density laws i x))).ae_le (ae_mem_interval laws)
  filter_upwards [hmem] with x hx
  obtain ⟨a, ha⟩ := hx
  rw [decodeCell_of_mem_interval laws ha]
  exact ha

/-- The actual interval decoder has precisely the original weights on the finite carrier. -/
theorem chartMeasure_map_decodeCell (laws : ι → FinDist (Option ℕ)) (i : ι) :
    (chartMeasure laws i).map (decodeCell laws) = (cellLaw laws i).toMeasure := by
  apply Measure.ext_of_measureReal_singleton
  intro a
  rw [map_measureReal_apply (measurable_decodeCell laws) (measurableSet_singleton a),
    FinDist.toMeasure_real_singleton, cellLaw_prob]
  calc
    (chartMeasure laws i).real (decodeCell laws ⁻¹' {a}) =
        (chartMeasure laws i).real (interval laws a) := by
      apply measureReal_congr
      filter_upwards [ae_decodeCell_mem_interval laws i] with x hx
      apply propext
      change decodeCell laws x = a ↔ x ∈ interval laws a
      constructor
      · intro h
        exact h ▸ hx
      · exact decodeCell_of_mem_interval laws
    _ = ownWeight laws i a := by
      rw [measureReal_def, chartMeasure_interval,
        ENNReal.toReal_ofReal (ownWeight_nonneg laws i a)]

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

end GameTheory.MarkedCalendarChart
