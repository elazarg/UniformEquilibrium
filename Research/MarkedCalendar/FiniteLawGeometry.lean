import Research.MarkedCalendar.FiniteLawCompactification
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! # Geometry of the actual finite-law marked calendars

Every gap of an actual source calendar is one positive source cell. Its density
is therefore constant, and a finite gap has its midpoint in the genuine source
reply menu. Source and limiting endpoint sets have no point strictly between
the finite cutoff and one.

In a retained finite gap, the limiting actual menu contains exactly its
midpoint. Limiting compatibility is derived from this identity, not supplied.
Endpoints below the cutoff but outside the limiting menu form a countable
subset of the existing exceptional endpoints, hence are null for every
atomless base. The actual Radon--Nikodym density of each limiting marginal is
constant almost everywhere on every retained gap, including a nonempty Never
gap, on the same supplied source subsequence. Actual mapped marginals are
concentrated on the genuine marked menu, retain the exact common mixture, and
have zero Never mass when its interval is empty. Finite-atom classification
and original variation witnesses remain separate obligations.
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

/-- A finite interior latent point yields a genuine source midpoint reply. -/
theorem midpointClock_mem_legalFiniteMenu (laws : ι → FinDist (Option ℕ))
    {x : unitInterval} (hx : x < cutoff laws)
    (hxE : (x : ℝ) ∉ (calendar laws).endpoints) :
    (calendar laws).midpointClock x ∈ legalFiniteMenu laws := by
  have hupper : (calendar laws).upperEndpoint x ≤ (cutoff laws : ℝ) :=
    ((calendar laws).monotone_upperEndpoint hx.le).trans_eq
      ((calendar laws).upperEndpoint_eq_of_mem (calendar laws).cutoff_mem)
  exact midpoint_mem_legalFiniteMenu_of_gap laws
    ((calendar laws).gap_of_not_mem hxE).1 hupper

private theorem eventually_notMem_sourceEndpoints
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) {x : ℝ} (hx : x ∉ limit.endpoints) :
    ∀ᶠ k in atTop, x ∉ (calendar (source (subsequence k))).endpoints := by
  have havoid : (limit.endpoints : Set ℝ) ⊆ ({x} : Set ℝ)ᶜ := by
    intro y hy hyx
    exact hx (mem_singleton_iff.mp hyx ▸ hy)
  have h := hE.eventually
    ((NonemptyCompacts.isOpen_subsets_of_isOpen isClosed_singleton.isOpen_compl).mem_nhds havoid)
  filter_upwards [h] with k hk
  exact fun hxk => hk hxk (mem_singleton x)

omit [Fintype ι] [Nonempty ι] in
private theorem notMem_exceptionalEndpoints_of_notMem
    (C : MathUE.MarkedCalendar.Calendar) {x : ℝ} (hx : x ∉ C.endpoints) :
    x ∉ C.exceptionalEndpoints := by
  rintro (h | h) <;> exact hx h.1

/-- A legal limiting mark inside a gap is forced to its midpoint by actual source-menu replies. -/
theorem limit_menu_mem_gap_eq_midpoint
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    {a b t : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b)
    (ht : t ∈ menu) (hat : a < t) (htb : t < b) : t = (a + b) / 2 := by
  obtain ⟨dates, _, hdates⟩ := exists_legal_reply_dates_tendsto source subsequence hT ht
  let x : unitInterval := ⟨t, (limit.endpoints_subset hgap.1).1.trans hat.le,
    htb.le.trans (limit.endpoints_subset hgap.2.1).2⟩
  have hxE : (x : ℝ) ∉ limit.endpoints := by
    intro hx
    rcases hgap.2.2.2 _ hx with h | h
    · exact (not_le_of_gt hat) h
    · exact (not_le_of_gt htb) h
  have hxregular := notMem_exceptionalEndpoints_of_notMem limit hxE
  obtain ⟨hlower, hupper⟩ := limit.endpoints_of_gap hgap
    (show a < (x : ℝ) from hat) (show (x : ℝ) < b from htb)
  have hbelow : limit.lowerEndpoint x < t := by rwa [hlower]
  have habove : t < limit.upperEndpoint x := by rwa [hupper]
  have hequal : ∀ᶠ k in atTop, mark (source (subsequence k)) (dates k) =
      (calendar (source (subsequence k))).midpointClock x := by
    filter_upwards [eventually_notMem_sourceEndpoints source subsequence hE hxE,
      (MathUE.MarkedCalendar.Calendar.tendsto_lowerEndpoint hE hxregular).eventually_lt
        hdates hbelow,
      hdates.eventually_lt
        (MathUE.MarkedCalendar.Calendar.tendsto_upperEndpoint hE hxregular) habove]
      with k hk hlow hupp
    exact (atomCompatible_mark (source (subsequence k)) (dates k)).2 _ _
      ((calendar (source (subsequence k))).gap_of_not_mem hk).1 hlow hupp
  have hmid := (MathUE.MarkedCalendar.Calendar.tendsto_midpointClock hE hxregular).congr'
    (hequal.mono fun _ hk => hk.symm)
  have heq := tendsto_nhds_unique hdates hmid
  exact heq.trans (limit.midpointClock_of_gap hgap hat htb)

/-- Every retained finite gap midpoint is approached by genuine source midpoints. -/
theorem midpoint_mem_limit_menu_of_gap
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b)
    (hb : b ≤ (limit.cutoff : ℝ)) : (a + b) / 2 ∈ menu := by
  have hnonneg := (limit.endpoints_subset hgap.1).1
  have hleone := (limit.endpoints_subset hgap.2.1).2
  have hab := hgap.2.2.1
  let x : unitInterval := ⟨(a + b) / 2, by constructor <;> linarith⟩
  have hax : a < (x : ℝ) := by change a < (a + b) / 2; linarith
  have hxb : (x : ℝ) < b := by change (a + b) / 2 < b; linarith
  have hxE : (x : ℝ) ∉ limit.endpoints := by
    intro hx
    rcases hgap.2.2.2 _ hx with h | h
    · exact (not_le_of_gt hax) h
    · exact (not_le_of_gt hxb) h
  have hxregular := notMem_exceptionalEndpoints_of_notMem limit hxE
  have hxcut : (x : ℝ) < (limit.cutoff : ℝ) := hxb.trans_le hb
  have hcReal : Tendsto (fun k => (cutoff (source (subsequence k)) : ℝ))
      atTop (𝓝 (limit.cutoff : ℝ)) := continuous_subtype_val.continuousAt.tendsto.comp hc
  have hmem : ∀ᶠ k in atTop, (calendar (source (subsequence k))).midpointClock x ∈
      legalMenuCompacts (source (subsequence k)) := by
    filter_upwards [eventually_notMem_sourceEndpoints source subsequence hE hxE,
      tendsto_const_nhds.eventually_lt hcReal hxcut] with k hk hcut
    exact midpointClock_mem_legalFiniteMenu (source (subsequence k)) hcut hk
  have hlimit := Math.Topology.mem_limit_of_nonemptyCompacts_tendsto hT
    (MathUE.MarkedCalendar.Calendar.tendsto_midpointClock hE hxregular) hmem
  rwa [limit.midpointClock_of_gap hgap hax hxb] at hlimit

/-- The actual limiting menu, not the whole compatible-mark class, has one test in each gap. -/
theorem limit_menu_inter_gap
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b)
    (hb : b ≤ (limit.cutoff : ℝ)) :
    (menu : Set ℝ) ∩ Ioo a b = {(a + b) / 2} := by
  ext t
  constructor
  · rintro ⟨ht, hat, htb⟩
    exact mem_singleton_iff.mpr
      (limit_menu_mem_gap_eq_midpoint source subsequence hE hT hgap ht hat htb)
  · intro ht
    have heq := mem_singleton_iff.mp ht
    subst t
    refine ⟨midpoint_mem_limit_menu_of_gap source subsequence hE hc hT hgap hb, ?_, ?_⟩ <;>
      linarith [hgap.2.2.1]

/-- Limiting compatibility is a consequence of the exact actual-menu gap identity. -/
theorem atomCompatible_of_mem_limit_menu
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    {t : ℝ} (ht : t ∈ menu) : limit.AtomCompatible t := by
  obtain ⟨dates, _, hdates⟩ := exists_legal_reply_dates_tendsto source subsequence hT ht
  have hcReal : Tendsto (fun k => (cutoff (source (subsequence k)) : ℝ))
      atTop (𝓝 (limit.cutoff : ℝ)) := continuous_subtype_val.continuousAt.tendsto.comp hc
  have hnonneg : 0 ≤ t := le_of_tendsto_of_tendsto tendsto_const_nhds hdates
    (Eventually.of_forall fun k => mark_nonneg (source (subsequence k)) (dates k))
  have hcutoff : t ≤ (limit.cutoff : ℝ) := le_of_tendsto_of_tendsto hdates hcReal
    (Eventually.of_forall fun k => mark_le_cutoff (source (subsequence k)) (dates k))
  refine ⟨⟨hnonneg, hcutoff⟩, ?_⟩
  intro a b hgap hat htb
  have hb : b ≤ (limit.cutoff : ℝ) := by
    rcases hgap.2.2.2 _ limit.cutoff_mem with h | h
    · exact ((not_le_of_gt hat) (hcutoff.trans h)).elim
    · exact h
  have hmem : t ∈ (menu : Set ℝ) ∩ Ioo a b := ⟨ht, hat, htb⟩
  rw [limit_menu_inter_gap source subsequence hE hc hT hgap hb] at hmem
  exact mem_singleton_iff.mp hmem

/-- Two distinct source endpoints below the cutoff enclose a genuine finite reply. -/
theorem exists_legalFiniteMenu_between_endpoints (laws : ι → FinDist (Option ℕ))
    {a b : ℝ} (ha : a ∈ (calendar laws).endpoints)
    (hb : b ∈ (calendar laws).endpoints) (hab : a < b)
    (hcut : b ≤ (cutoff laws : ℝ)) :
    ∃ t ∈ legalFiniteMenu laws, a < t ∧ t < b := by
  let first : unitInterval := ⟨a, (calendar laws).endpoints_subset ha⟩
  let last : unitInterval := ⟨b, (calendar laws).endpoints_subset hb⟩
  have hpositive : (volume : Measure unitInterval) (Ioo first last) ≠ 0 := by
    rw [unitInterval.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  obtain ⟨x, hx, cell, hleft, hright⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpositive
      (ae_restrict_of_ae (ae_mem_cellInterior laws))
  have hax : a < (x : ℝ) := hx.1
  have hxb : (x : ℝ) < b := hx.2
  have hgap := isGap_interval laws cell
  have haleft : a ≤ left laws cell := by
    rcases hgap.2.2.2 a ha with h | h
    · exact h
    · linarith
  have hrightb : right laws cell ≤ b := by
    rcases hgap.2.2.2 b hb with h | h
    · linarith
    · exact h
  refine ⟨(left laws cell + right laws cell) / 2,
    midpoint_mem_legalFiniteMenu_of_gap laws hgap (hrightb.trans hcut), ?_, ?_⟩ <;>
    linarith [left_lt_right laws cell]

private theorem not_lt_endpoints_in_menu_avoiding_interval
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    {u v a b : ℝ} (havoid : (menu : Set ℝ) ⊆ (Icc u v)ᶜ)
    (hv : v ≤ (limit.cutoff : ℝ)) (ha : a ∈ limit.endpoints)
    (hb : b ∈ limit.endpoints) (hauv : a ∈ Ioo u v) (hbuv : b ∈ Ioo u v) :
    ¬ a < b := by
  intro hab
  obtain ⟨first, hfirst, hfirstlim⟩ :=
    Math.Topology.exists_mem_tendsto_of_nonemptyCompacts_tendsto hE ha
  obtain ⟨last, hlast, hlastlim⟩ :=
    Math.Topology.exists_mem_tendsto_of_nonemptyCompacts_tendsto hE hb
  have hcReal : Tendsto (fun k => (cutoff (source (subsequence k)) : ℝ))
      atTop (𝓝 (limit.cutoff : ℝ)) := continuous_subtype_val.continuousAt.tendsto.comp hc
  have havoidSource := hT.eventually
    ((NonemptyCompacts.isOpen_subsets_of_isOpen isClosed_Icc.isOpen_compl).mem_nhds havoid)
  have hcontradiction : ∀ᶠ k : ℕ in atTop, False := by
    filter_upwards [havoidSource, hfirstlim.eventually (lt_mem_nhds hauv.1),
      hlastlim.eventually (gt_mem_nhds hbuv.2), hfirstlim.eventually_lt hlastlim hab,
      hlastlim.eventually_lt hcReal (hbuv.2.trans_le hv)] with k hk hu hv hlt hcut
    obtain ⟨t, ht, hfirstt, htlast⟩ := exists_legalFiniteMenu_between_endpoints
      (source (subsequence k)) (hfirst k) (hlast k) hlt hcut.le
    exact hk ht ⟨(hu.trans hfirstt).le, (htlast.trans hv).le⟩
  exact hcontradiction.exists.choose_spec

/-- A missing finite endpoint is genuinely isolated, not declared to be an available test. -/
theorem mem_exceptionalEndpoints_of_notMem_limit_menu
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    {x : ℝ} (hxE : x ∈ limit.endpoints) (hxc : x < (limit.cutoff : ℝ))
    (hxT : x ∉ menu) : x ∈ limit.exceptionalEndpoints := by
  have hnbhd : (menu : Set ℝ)ᶜ ∩ Iio (limit.cutoff : ℝ) ∈ 𝓝 x :=
    inter_mem (menu.isCompact.isClosed.isOpen_compl.mem_nhds hxT) (gt_mem_nhds hxc)
  obtain ⟨u, v, hxuv, hinterval, hsubset⟩ :=
    exists_Icc_mem_subset_of_mem_nhds hnbhd
  have hxstrict : x ∈ Ioo u v := Icc_mem_nhds_iff.mp hinterval
  have huv : u ≤ v := hxuv.1.trans hxuv.2
  have hv : v ≤ (limit.cutoff : ℝ) := (hsubset ⟨huv, le_rfl⟩).2.le
  have havoid : (menu : Set ℝ) ⊆ (Icc u v)ᶜ := by
    intro t ht htuv
    exact (hsubset htuv).1 ht
  have hnotClosure : x ∉ closure ((limit.endpoints : Set ℝ) ∩ Ioi x) := by
    intro hclosure
    obtain ⟨y, hyuv, hyE, hxy⟩ :=
      mem_closure_iff.mp hclosure (Ioo u v) isOpen_Ioo hxstrict
    exact not_lt_endpoints_in_menu_avoiding_interval source subsequence hE hc hT
      havoid hv hxE hyE hxstrict hyuv hxy
  exact Or.inl ⟨hxE, notMem_closure_iff_nhdsWithin_eq_bot.mp hnotClosure⟩

/-- The exceptional finite endpoints omitted by the actual limit menu are countable. -/
theorem countable_limit_endpoints_outside_menu
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu)) :
    {x : ℝ | x ∈ limit.endpoints ∧ x < (limit.cutoff : ℝ) ∧ x ∉ menu}.Countable := by
  apply limit.countable_exceptionalEndpoints.mono
  rintro x ⟨hxE, hxc, hxT⟩
  exact mem_exceptionalEndpoints_of_notMem_limit_menu source subsequence hE hc hT hxE hxc hxT

/-- Actual menu availability holds almost everywhere on the finite limiting endpoints. -/
theorem ae_mem_limit_menu_of_mem_endpoints
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (μ : Measure unitInterval) [NullSingletonClass μ] :
    ∀ᵐ x : unitInterval ∂μ, (x : ℝ) ∈ limit.endpoints →
      (x : ℝ) < (limit.cutoff : ℝ) → (x : ℝ) ∈ menu := by
  filter_upwards [limit.ae_notMem_exceptionalEndpoints μ] with x hx hxE hxc
  by_contra hxT
  exact hx (mem_exceptionalEndpoints_of_notMem_limit_menu source subsequence hE hc hT hxE hxc hxT)

private theorem integral_indicator_chartLaw (laws : ι → FinDist (Option ℕ)) (i : ι)
    (s : Set unitInterval) (hs : MeasurableSet s) :
    ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂(chartLaw laws i : Measure unitInterval) =
      ∫ x in s, density laws i x ∂volume := by
  change ∫ x, s.indicator (fun _ => (1 : ℝ)) x
    ∂volume.withDensity (fun x => ENNReal.ofReal (density laws i x)) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_density laws i).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change (ENNReal.ofReal (density laws i x)).toReal • s.indicator (fun _ => (1 : ℝ)) x =
    s.indicator (density laws i) x
  rw [ENNReal.toReal_ofReal (density_nonneg laws i x), smul_eq_mul]
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx, mul_one]
  · simp only [Set.indicator_of_notMem hx, mul_zero]

private theorem eventually_density_eq_on_inner_interval
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) {a b q r : ℝ}
    (hgap : Math.Topology.IsGap limit.endpoints a b) {x : unitInterval}
    (haq : a < q) (hqx : q < (x : ℝ)) (hxr : (x : ℝ) < r) (hrb : r < b) :
    ∀ᶠ k in atTop, ∀ (i : ι) (y : unitInterval), q < (y : ℝ) → (y : ℝ) < r →
      density (source (subsequence k)) i y = density (source (subsequence k)) i x := by
  have hax := haq.trans hqx
  have hxb := hxr.trans hrb
  have hxE : (x : ℝ) ∉ limit.endpoints := by
    intro hx
    rcases hgap.2.2.2 _ hx with h | h
    · exact (not_le_of_gt hax) h
    · exact (not_le_of_gt hxb) h
  have hxregular := notMem_exceptionalEndpoints_of_notMem limit hxE
  obtain ⟨hlower, hupper⟩ := limit.endpoints_of_gap hgap hax hxb
  have hlowerq : limit.lowerEndpoint x < q := by rwa [hlower]
  have hrupper : r < limit.upperEndpoint x := by rwa [hupper]
  filter_upwards [eventually_notMem_sourceEndpoints source subsequence hE hxE,
    (MathUE.MarkedCalendar.Calendar.tendsto_lowerEndpoint hE hxregular).eventually
      (gt_mem_nhds hlowerq),
    (MathUE.MarkedCalendar.Calendar.tendsto_upperEndpoint hE hxregular).eventually
      (lt_mem_nhds hrupper)] with k hk hlow hupp
  obtain ⟨hsourcegap, hsourceleft, hsourceright⟩ :=
    (calendar (source (subsequence k))).gap_of_not_mem hk
  obtain ⟨values, _, hvalues⟩ :=
    density_constant_on_calendar_gap (source (subsequence k)) hsourcegap
  intro i y hqy hyr
  exact (hvalues i y (hlow.trans hqy) (hyr.trans hupp)).trans
    (hvalues i x hsourceleft hsourceright).symm

/-- Fixed inner-interval tests determine the source densities on the same whole subsequence.
The gap may be finite or the actual Never interval; no new extraction is made. -/
theorem exists_tendsto_density_on_limit_gap
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b) :
    ∃ value : ℝ, (0 ≤ value ∧ value ≤ (Fintype.card ι : ℝ)) ∧
      ∀ x : unitInterval, a < (x : ℝ) → (x : ℝ) < b →
        Tendsto (fun k => density (source (subsequence k)) i x) atTop (𝓝 value) := by
  have hab := hgap.2.2.1
  let x : unitInterval := ⟨(a + b) / 2, by
    have ha := (limit.endpoints_subset hgap.1).1
    have hb := (limit.endpoints_subset hgap.2.1).2
    constructor <;> linarith⟩
  have hax : a < (x : ℝ) := by change a < (a + b) / 2; linarith
  have hxb : (x : ℝ) < b := by change (a + b) / 2 < b; linarith
  obtain ⟨q, haq, hqx⟩ := exists_between hax
  obtain ⟨r, hxr, hrb⟩ := exists_between hxb
  let first : unitInterval := ⟨q, (limit.endpoints_subset hgap.1).1.trans haq.le,
    hqx.le.trans x.property.2⟩
  let last : unitInterval := ⟨r, x.property.1.trans hxr.le,
    hrb.le.trans (limit.endpoints_subset hgap.2.1).2⟩
  let inner : Set unitInterval := Ioo first last
  have hinner : MeasurableSet inner := measurableSet_Ioo
  have hvolume : 0 < (volume : Measure unitInterval).real inner := by
    change 0 < ((volume : Measure unitInterval) (Ioo first last)).toReal
    rw [unitInterval.volume_Ioo, ENNReal.toReal_ofReal]
    · change 0 < r - q
      linarith
    · change 0 ≤ r - q
      linarith
  have hconstant := eventually_density_eq_on_inner_interval source subsequence hE
    hgap haq hqx hxr hrb
  have hformula : ∀ᶠ k in atTop,
      ∫ y, inner.indicator (fun _ => (1 : ℝ)) y
        ∂(chartLaw (source (subsequence k)) i : Measure unitInterval) =
      (volume : Measure unitInterval).real inner * density (source (subsequence k)) i x := by
    filter_upwards [hconstant] with k hk
    rw [integral_indicator_chartLaw _ _ inner hinner]
    calc
      _ = ∫ _ in inner, density (source (subsequence k)) i x ∂volume := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hinner] with y hy
        exact hk i y hy.1 hy.2
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  have hweak := ProbabilityMeasure.tendsto_integral_of_tendsto_of_le_smul base
    (Fintype.card ι : NNReal) hlaw
    (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) i)
    (inner.indicator (fun _ => (1 : ℝ))) ((integrable_const _).indicator hinner)
  let value := (∫ y, inner.indicator (fun _ => (1 : ℝ)) y ∂(law : Measure unitInterval)) /
    (volume : Measure unitInterval).real inner
  have hvalue : Tendsto (fun k => density (source (subsequence k)) i x) atTop (𝓝 value) := by
    apply (hweak.div_const ((volume : Measure unitInterval).real inner)).congr'
    filter_upwards [hformula] with k hk
    rw [hk, mul_div_cancel_left₀ _ hvolume.ne']
  refine ⟨value, ⟨?_, ?_⟩, ?_⟩
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds hvalue
      (Eventually.of_forall fun k => density_nonneg (source (subsequence k)) i x)
  · exact le_of_tendsto_of_tendsto hvalue tendsto_const_nhds
      (Eventually.of_forall fun k => density_le_card (source (subsequence k)) i x)
  · intro y hay hyb
    obtain ⟨q', haq', hq'⟩ := exists_between (lt_min hax hay)
    obtain ⟨r', hr', hr'b⟩ := exists_between (max_lt hxb hyb)
    have heq := eventually_density_eq_on_inner_interval source subsequence hE hgap
      haq' (hq'.trans_le (min_le_left _ _)) ((le_max_left _ _).trans_lt hr') hr'b
    apply hvalue.congr'
    filter_upwards [heq] with k hk
    exact (hk i y (hq'.trans_le (min_le_right _ _))
      ((le_max_right _ _).trans_lt hr')).symm

/-- The limiting marginal has its actual RN density constant on each retained gap. This uses
the same source subsequence and also applies to a nonempty Never gap. -/
theorem exists_rnDeriv_toReal_constant_on_limit_gap
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b) :
    ∃ value : ℝ, (0 ≤ value ∧ value ≤ (Fintype.card ι : ℝ)) ∧
      ∀ᵐ x : unitInterval ∂volume, a < (x : ℝ) → (x : ℝ) < b →
        ((law : Measure unitInterval).rnDeriv volume x).toReal = value := by
  obtain ⟨value, hvalue, hpointwise⟩ :=
    exists_tendsto_density_on_limit_gap source subsequence hE i hlaw hgap
  have hdomination : (law : Measure unitInterval) ≤
      (Fintype.card ι : NNReal) • (base : Measure unitInterval) :=
    ProbabilityMeasure.le_of_tendsto_of_le_measure _ hlaw
      (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) i)
  obtain ⟨hmeasurable, hbounded, hrepresentation, _⟩ :=
    ProbabilityMeasure.rnDeriv_toReal_spec_of_le_smul base law
      (Fintype.card ι : NNReal) hdomination
  let rho : unitInterval → ℝ := fun x =>
    ((law : Measure unitInterval).rnDeriv volume x).toReal
  change Measurable rho at hmeasurable
  change ∀ᵐ x ∂volume, 0 ≤ rho x ∧ rho x ≤ (Fintype.card ι : ℝ) at hbounded
  change volume.withDensity (fun x => ENNReal.ofReal (rho x)) =
    (law : Measure unitInterval) at hrepresentation
  have hintegrable : Integrable rho (volume : Measure unitInterval) := by
    apply Integrable.of_bound hmeasurable.aestronglyMeasurable (Fintype.card ι : ℝ)
    filter_upwards [hbounded] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hindicator (s : Set unitInterval) (hs : MeasurableSet s) :
      ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂(law : Measure unitInterval) =
        ∫ x in s, rho x ∂volume := by
    rw [← hrepresentation, integral_withDensity_eq_integral_toReal_smul
      hmeasurable.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
      ← integral_indicator hs]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    change (ENNReal.ofReal (rho x)).toReal • s.indicator (fun _ => (1 : ℝ)) x =
      s.indicator rho x
    rw [ENNReal.toReal_ofReal (show 0 ≤ rho x from ENNReal.toReal_nonneg), smul_eq_mul]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx, mul_one]
    · simp only [Set.indicator_of_notMem hx, mul_zero]
  let gap : Set unitInterval := {x | a < (x : ℝ) ∧ (x : ℝ) < b}
  have hgapMeasurable : MeasurableSet gap := measurableSet_Ioo.preimage measurable_subtype_coe
  have hequal : rho =ᵐ[(volume : Measure unitInterval).restrict gap] fun _ => value := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq rho (fun _ => value)
      hintegrable.integrableOn (integrable_const _)
    intro s hs _
    simp only [Measure.restrict_restrict hs]
    have hset : MeasurableSet (s ∩ gap) := hs.inter hgapMeasurable
    have hconvergence := tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure unitInterval).restrict (s ∩ gap))
      (F := fun k x => density (source (subsequence k)) i x) (f := fun _ => value)
      (fun _ => (Fintype.card ι : ℝ))
      (fun k => (measurable_density (source (subsequence k)) i).aestronglyMeasurable)
      (integrable_const _) (fun k => Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (density_nonneg _ _ _)] using
          density_le_card (source (subsequence k)) i x) (by
        filter_upwards [ae_restrict_mem hset] with x hx
        exact hpointwise x hx.2.1 hx.2.2)
    have hweak := ProbabilityMeasure.tendsto_integral_of_tendsto_of_le_smul base
      (Fintype.card ι : NNReal) hlaw
      (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) i)
      ((s ∩ gap).indicator (fun _ => (1 : ℝ))) ((integrable_const _).indicator hset)
    rw [hindicator _ hset] at hweak
    have hweak' : Tendsto (fun k => ∫ x in s ∩ gap,
        density (source (subsequence k)) i x ∂volume) atTop
        (𝓝 (∫ x in s ∩ gap, rho x ∂volume)) := by
      apply hweak.congr'
      exact Eventually.of_forall fun k =>
        integral_indicator_chartLaw (source (subsequence k)) i (s ∩ gap) hset
    exact tendsto_nhds_unique hweak' hconvergence
  refine ⟨value, hvalue, ?_⟩
  filter_upwards [(ae_restrict_iff' hgapMeasurable).mp hequal] with x hx hax hxb
  exact hx ⟨hax, hxb⟩

/-- The actual limiting marked menu together with literal Never. -/
def markedMenuSet (menu : NonemptyCompacts ℝ) : Set (WithTop ℝ) :=
  insert ⊤ ((fun t : ℝ => (t : WithTop ℝ)) '' (menu : Set ℝ))

private theorem measurableSet_markedMenuSet (menu : NonemptyCompacts ℝ) :
    MeasurableSet (markedMenuSet menu) :=
  ((menu.isCompact.image WithTop.continuous_coe).insert ⊤).isClosed.measurableSet

/-- Raw chart samples land in the actual limiting menu almost surely, not merely in the
larger class of atom-compatible marks. -/
theorem ae_collapseClock_mem_limit_menu
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu)) :
    ∀ᵐ x : unitInterval ∂volume, limit.collapseClock x ∈ markedMenuSet menu := by
  filter_upwards [ae_mem_limit_menu_of_mem_endpoints source subsequence hE hc hT volume]
    with x hx
  by_cases hxc : limit.cutoff ≤ x
  · rw [(limit.collapseClock_eq_top_iff x).mpr hxc]
    exact Set.mem_insert ⊤ _
  · have hxc' : x < limit.cutoff := lt_of_not_ge hxc
    rw [limit.collapseClock_of_lt hxc']
    apply Set.mem_insert_of_mem
    refine ⟨limit.midpointClock x, ?_, rfl⟩
    by_cases hxE : (x : ℝ) ∈ limit.endpoints
    · rw [limit.midpointClock_eq_of_mem hxE]
      exact hx hxE hxc'
    · obtain ⟨hgap, hleft, hright⟩ := limit.gap_of_not_mem hxE
      have hupper : limit.upperEndpoint x ≤ (limit.cutoff : ℝ) :=
        (limit.monotone_upperEndpoint hxc'.le).trans_eq
          (limit.upperEndpoint_eq_of_mem limit.cutoff_mem)
      rw [limit.midpointClock_of_gap hgap hleft hright]
      exact midpoint_mem_limit_menu_of_gap source subsequence hE hc hT hgap hupper

/-- The actual mapped limiting marginal gives the complement of the genuine marked menu zero
mass. Absolute continuity is derived from the original chart domination. -/
theorem map_limit_chartLaw_compl_menu
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law)) :
    (law : Measure unitInterval).map limit.collapseClock (markedMenuSet menu)ᶜ = 0 := by
  have hbound : (law : Measure unitInterval) ≤
      (Fintype.card ι : NNReal) • (base : Measure unitInterval) :=
    ProbabilityMeasure.le_of_tendsto_of_le_measure _ hlaw
      (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) i)
  have habs : (law : Measure unitInterval) ≪ volume :=
    Measure.absolutelyContinuous_of_le_smul hbound
  have hae := habs.ae_le (ae_collapseClock_mem_limit_menu source subsequence hE hc hT)
  rw [Measure.map_apply limit.measurable_collapseClock
    (measurableSet_markedMenuSet menu).compl]
  exact ae_iff.mp hae

/-- The actual collapsed marginals retain the exact common mixture; no new chart is chosen. -/
theorem sum_map_limit_chartLaws
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (limit : MathUE.MarkedCalendar.Calendar) :
    (∑ i, (marginals i : Measure unitInterval).map limit.collapseClock) =
      (Fintype.card ι : NNReal) • (volume : Measure unitInterval).map limit.collapseClock := by
  have hsum : (∑ i, (marginals i : Measure unitInterval)).map limit.collapseClock =
      ∑ i, (marginals i : Measure unitInterval).map limit.collapseClock := by
    simp only [← Measure.mapₗ_apply_of_measurable limit.measurable_collapseClock, map_sum]
  rw [← hsum, sum_limit_chartLaws source subsequence hlaws,
    Measure.map_smul _ limit.measurable_collapseClock.aemeasurable]
  rfl

/-- The Never mixture mass is its actual terminal interval length, including the empty case. -/
theorem map_volume_collapseClock_top (limit : MathUE.MarkedCalendar.Calendar) :
    (volume : Measure unitInterval).map limit.collapseClock {⊤} =
      ENNReal.ofReal (1 - (limit.cutoff : ℝ)) := by
  rw [Measure.map_apply limit.measurable_collapseClock (measurableSet_singleton _)]
  have hfiber : limit.collapseClock ⁻¹' {⊤} = Ici limit.cutoff := by
    ext x
    exact limit.collapseClock_eq_top_iff x
  rw [hfiber, unitInterval.volume_Ici]

/-- If the Never interval is empty, every actual limiting marginal has zero Never mass. -/
theorem map_limit_chartLaw_top_eq_zero_of_cutoff_eq_one
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (limit : MathUE.MarkedCalendar.Calendar) (hcutoff : limit.cutoff = 1)
    (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law)) :
    (law : Measure unitInterval).map limit.collapseClock {⊤} = 0 := by
  have hbound : (law : Measure unitInterval) ≤
      (Fintype.card ι : NNReal) • (base : Measure unitInterval) :=
    ProbabilityMeasure.le_of_tendsto_of_le_measure _ hlaw
      (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) i)
  have hmap := Measure.map_mono hbound limit.measurable_collapseClock
  rw [Measure.map_smul _ limit.measurable_collapseClock.aemeasurable] at hmap
  have htop := hmap {⊤}
  change (law : Measure unitInterval).map limit.collapseClock {⊤} ≤
    ((Fintype.card ι : NNReal) • (volume : Measure unitInterval).map
      limit.collapseClock) {⊤} at htop
  rw [Measure.coe_nnreal_smul_apply, map_volume_collapseClock_top, hcutoff] at htop
  apply le_antisymm ?_ zero_le
  simpa using htop

end GameTheory.MarkedCalendarChart
