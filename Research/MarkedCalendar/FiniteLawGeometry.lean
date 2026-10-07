import Research.MarkedCalendar.FiniteLawCompactification

/-! # Geometry of the actual finite-law marked calendars

Every gap of an actual source calendar is one positive source cell. Its density
is therefore constant, and a finite gap has its midpoint in the genuine source
reply menu. Source and limiting endpoint sets have no point strictly between
the finite cutoff and one.

Retained-gap menu identities, endpoint nullity outside the limiting menu,
limiting density constancy, complete caps, and original variation witnesses
are subsequent obligations, not consequences asserted by this initial slice.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology BigOperators

namespace GameTheory.MarkedCalendarChart

variable {ι : Type} [Fintype ι] [Nonempty ι]

theorem ae_mem_cellInterior (laws : ι → FinDist (Option ℕ)) :
    ∀ᵐ x : unitInterval ∂volume, ∃ a : Cell laws,
      left laws a < (x : ℝ) ∧ (x : ℝ) < right laws a := by
  have hne : ∀ᵐ x : unitInterval ∂volume, ∀ a : Cell laws, x ≠ leftPoint laws a :=
    ae_all_iff.mpr fun a => volume.ae_ne (leftPoint laws a)
  filter_upwards [ae_mem_interval laws, hne] with x hx hne
  obtain ⟨a, ha⟩ := hx
  change leftPoint laws a ≤ x ∧ x < rightPoint laws a at ha
  have hleft : leftPoint laws a < x := by
    rcases ha.1.eq_or_lt with heq | hlt
    · exact (hne a heq.symm).elim
    · exact hlt
  exact ⟨a, hleft, ha.2⟩

/-- Positive interval volume and the actual cell cover identify every source gap exactly. -/
theorem exists_cell_of_calendar_gap (laws : ι → FinDist (Option ℕ)) {a b : ℝ}
    (hgap : Math.Topology.IsGap (calendar laws).endpoints a b) :
    ∃ cell : Cell laws, left laws cell = a ∧ right laws cell = b := by
  let first : unitInterval := ⟨a, (calendar laws).endpoints_subset hgap.1⟩
  let last : unitInterval := ⟨b, (calendar laws).endpoints_subset hgap.2.1⟩
  have hpositive : (volume : Measure unitInterval) (Ioo first last) ≠ 0 := by
    rw [unitInterval.volume_Ioo]
    apply ne_of_gt
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hgap.2.2.1)
  obtain ⟨x, hx, cell, hleft, hright⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpositive
      (ae_restrict_of_ae (ae_mem_cellInterior laws))
  have hsource := (calendar laws).endpoints_of_gap (isGap_interval laws cell) hleft hright
  have hgiven := (calendar laws).endpoints_of_gap hgap
    (show a < (x : ℝ) from hx.1) (show (x : ℝ) < b from hx.2)
  exact ⟨cell, hsource.1.symm.trans hgiven.1, hsource.2.symm.trans hgiven.2⟩

/-- Source density constancy on a gap is pointwise, with its actual own/mixture mass ratio. -/
theorem density_constant_on_calendar_gap (laws : ι → FinDist (Option ℕ)) {a b : ℝ}
    (hgap : Math.Topology.IsGap (calendar laws).endpoints a b) :
    ∃ values : ι → ℝ,
      (∀ i, 0 ≤ values i ∧ values i ≤ (Fintype.card ι : ℝ)) ∧
      ∀ (i : ι) (x : unitInterval), a < (x : ℝ) → (x : ℝ) < b →
        density laws i x = values i := by
  obtain ⟨cell, hleft, hright⟩ := exists_cell_of_calendar_gap laws hgap
  refine ⟨fun i => ownWeight laws i cell / weight laws cell, ?_, ?_⟩
  · intro i
    exact ⟨div_nonneg (ownWeight_nonneg laws i cell) (weight_pos laws cell).le,
      (div_le_iff₀ (weight_pos laws cell)).mpr (ownWeight_le laws i cell)⟩
  · intro i x hax hxb
    apply density_eq_of_mem_interval laws i
    change left laws cell ≤ (x : ℝ) ∧ (x : ℝ) < right laws cell
    rw [hleft, hright]
    exact ⟨hax.le, hxb⟩

theorem right_eq_one_of_top (laws : ι → FinDist (Option ℕ)) (cell : Cell laws)
    (htop : (cell : WithTop ℕ) = ⊤) : right laws cell = 1 := by
  rw [right_eq_sum_le]
  have hall (other : Cell laws) : other ≤ cell := by
    change (other : WithTop ℕ) ≤ (cell : WithTop ℕ)
    rw [htop]
    exact le_top
  simp only [hall, ite_true, sum_weight]

/-- Every actual source endpoint is at or before the cutoff, or is the final boundary one. -/
theorem endpoint_le_cutoff_or_eq_one (laws : ι → FinDist (Option ℕ)) {x : ℝ}
    (hx : x ∈ (calendar laws).endpoints) : x ≤ (cutoff laws : ℝ) ∨ x = 1 := by
  change x ∈ endpointSet laws at hx
  simp only [endpointSet, mem_insert_iff, mem_union, mem_range] at hx
  rcases hx with rfl | rfl | rfl | ⟨cell, rfl⟩ | ⟨cell, rfl⟩
  · exact Or.inl (cutoff laws).property.1
  · exact Or.inr rfl
  · exact Or.inl le_rfl
  · apply Or.inl
    by_cases htop : (cell : WithTop ℕ) = ⊤
    · exact (cutoff_eq_left_of_top laws cell htop).ge
    · exact (left_lt_right laws cell).le.trans (right_le_cutoff laws cell htop)
  · by_cases htop : (cell : WithTop ℕ) = ⊤
    · exact Or.inr (right_eq_one_of_top laws cell htop)
    · exact Or.inl (right_le_cutoff laws cell htop)

/-- A nontrivial source Never interval is itself one calendar gap. -/
theorem isGap_cutoff_one (laws : ι → FinDist (Option ℕ)) (hcut : (cutoff laws : ℝ) < 1) :
    Math.Topology.IsGap (calendar laws).endpoints (cutoff laws : ℝ) 1 := by
  refine ⟨(calendar laws).cutoff_mem, (calendar laws).one_mem, hcut, ?_⟩
  intro x hx
  rcases endpoint_le_cutoff_or_eq_one laws hx with hle | rfl
  · exact Or.inl hle
  · exact Or.inr le_rfl

/-- A finite source gap supplies an actual supported-date midpoint in the original menu image. -/
theorem midpoint_mem_legalFiniteMenu_of_gap (laws : ι → FinDist (Option ℕ)) {a b : ℝ}
    (hgap : Math.Topology.IsGap (calendar laws).endpoints a b)
    (hb : b ≤ (cutoff laws : ℝ)) : (a + b) / 2 ∈ legalFiniteMenu laws := by
  obtain ⟨cell, hleft, hright⟩ := exists_cell_of_calendar_gap laws hgap
  have hfinite : (cell : WithTop ℕ) ≠ ⊤ := by
    intro htop
    have hcut := cutoff_eq_left_of_top laws cell htop
    rw [hleft] at hcut
    have hab := hgap.2.2.1
    linarith
  obtain ⟨time, htime⟩ := WithTop.ne_top_iff_exists.mp hfinite
  change (a + b) / 2 ∈ (legalFiniteMenu laws : Set ℝ)
  rw [← range_mark_eq_legalFiniteMenu]
  refine ⟨time, ?_⟩
  rw [mark_eq_midpoint laws cell htime.symm, hleft, hright]

/-- No compatible-but-unavailable endpoint is added: the source gap has exactly its midpoint. -/
theorem legalFiniteMenu_inter_gap (laws : ι → FinDist (Option ℕ)) {a b : ℝ}
    (hgap : Math.Topology.IsGap (calendar laws).endpoints a b)
    (hb : b ≤ (cutoff laws : ℝ)) :
    (legalFiniteMenu laws : Set ℝ) ∩ Ioo a b = {(a + b) / 2} := by
  ext t
  constructor
  · rintro ⟨ht, hat, htb⟩
    exact mem_singleton_iff.mpr
      ((atomCompatible_of_mem_legalFiniteMenu laws ht).2 a b hgap hat htb)
  · intro ht
    have heq := mem_singleton_iff.mp ht
    subst t
    refine ⟨midpoint_mem_legalFiniteMenu_of_gap laws hgap hb, ?_, ?_⟩ <;>
      linarith [hgap.2.2.1]

/-- The absence of endpoints inside Never passes from the same actual source calendars. -/
theorem limit_endpoints_notMem_Ioo_cutoff_one
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    {x : ℝ} (hx : x ∈ limit.endpoints) : x ∉ Ioo (limit.cutoff : ℝ) 1 := by
  obtain ⟨points, hmem, hpoints⟩ :=
    Math.Topology.exists_mem_tendsto_of_nonemptyCompacts_tendsto hE hx
  intro hlate
  have hbelow : ∀ᶠ k in atTop, points k < 1 := hpoints.eventually (gt_mem_nhds hlate.2)
  have hle : ∀ᶠ k in atTop, points k ≤ (cutoff (source (subsequence k)) : ℝ) := by
    filter_upwards [hbelow] with k hk
    rcases endpoint_le_cutoff_or_eq_one (source (subsequence k)) (hmem k) with hle | heq
    · exact hle
    · exact (lt_irrefl 1 (heq ▸ hk)).elim
  have hcReal : Tendsto (fun k => (cutoff (source (subsequence k)) : ℝ))
      atTop (𝓝 (limit.cutoff : ℝ)) := continuous_subtype_val.continuousAt.tendsto.comp hc
  exact (not_le_of_gt hlate.1) (le_of_tendsto_of_tendsto hpoints hcReal hle)

end GameTheory.MarkedCalendarChart
