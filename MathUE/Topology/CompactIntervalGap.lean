import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Maximal gaps in a compact subset of the real line

The scalar maximal-gap step in Sorin (1986), Proposition 7, pages 152--153.
The endpoints and largest gap are selected from the actual compact set.
-/

namespace Math.Topology

open Set

/-- An empty open interval whose two endpoints belong to the given set. -/
def IsGap (K : Set ℝ) (left right : ℝ) : Prop :=
  left ∈ K ∧ right ∈ K ∧ left < right ∧
    ∀ point ∈ K, point ≤ left ∨ right ≤ point

/-- Missing an interval point between two actual compact-set members gives
an actual gap containing that point. -/
theorem exists_gap_of_mem_interval_not_mem
    (K : Set ℝ) (hK : IsCompact K) {a b missing : ℝ}
    (ha : a ∈ K) (hb : b ∈ K) (hinterval : missing ∈ Icc a b)
    (hmissing : missing ∉ K) :
    ∃ left right, IsGap K left right ∧ left < missing ∧ missing < right := by
  obtain ⟨left, hleft, hleftMax⟩ :=
    (hK.inter_right isClosed_Iic).exists_isMaxOn
      ⟨a, ha, hinterval.1⟩ continuous_id.continuousOn
  obtain ⟨right, hright, hrightMin⟩ :=
    (hK.inter_right isClosed_Ici).exists_isMinOn
      ⟨b, hb, hinterval.2⟩ continuous_id.continuousOn
  have hleftLt : left < missing := by
    apply lt_of_le_of_ne hleft.2
    intro hequal
    exact hmissing (hequal ▸ hleft.1)
  have hrightLt : missing < right := by
    apply lt_of_le_of_ne hright.2
    intro hequal
    exact hmissing (hequal.symm ▸ hright.1)
  refine ⟨left, right, ⟨hleft.1, hright.1, hleftLt.trans hrightLt, ?_⟩,
    hleftLt, hrightLt⟩
  intro point hpoint
  by_cases hside : point ≤ missing
  · exact Or.inl (hleftMax ⟨hpoint, hside⟩)
  · exact Or.inr (hrightMin ⟨hpoint, le_of_not_ge hside⟩)

/-- A positive gap of maximal length exists when a compact set omits a
point of an interval joining two of its actual members. -/
theorem exists_maximal_gap_of_not_subset
    (K : Set ℝ) (hK : IsCompact K) {a b : ℝ}
    (ha : a ∈ K) (hb : b ∈ K) (hmissing : ¬Icc a b ⊆ K) :
    ∃ left right, IsGap K left right ∧
      ∀ otherLeft otherRight, IsGap K otherLeft otherRight →
        otherRight - otherLeft ≤ right - left := by
  classical
  obtain ⟨missing, hinterval, hnot⟩ := Set.not_subset.mp hmissing
  obtain ⟨firstLeft, firstRight, hfirst, _, _⟩ :=
    exists_gap_of_mem_interval_not_mem K hK ha hb hinterval hnot
  let closedCondition : Set (ℝ × ℝ) :=
    {pair | pair.1 ≤ pair.2 ∧
      ∀ point ∈ K, point ≤ pair.1 ∨ pair.2 ≤ point}
  have hforallClosed : IsClosed
      {pair : ℝ × ℝ | ∀ point ∈ K, point ≤ pair.1 ∨ pair.2 ≤ point} := by
    have hequal : {pair : ℝ × ℝ |
        ∀ point ∈ K, point ≤ pair.1 ∨ pair.2 ≤ point} =
        ⋂ point ∈ K, {pair : ℝ × ℝ | point ≤ pair.1 ∨ pair.2 ≤ point} := by
      ext pair
      simp only [mem_ofPred_eq, mem_iInter]
    rw [hequal]
    apply isClosed_biInter
    intro point _
    exact (isClosed_le continuous_const continuous_fst).union
      (isClosed_le continuous_snd continuous_const)
  have hconditionClosed : IsClosed closedCondition :=
    (isClosed_le continuous_fst continuous_snd).inter hforallClosed
  let pairs := (K ×ˢ K) ∩ closedCondition
  have hpairsCompact : IsCompact pairs :=
    (hK.prod hK).inter_right hconditionClosed
  have hfirstPair : (firstLeft, firstRight) ∈ pairs :=
    ⟨⟨hfirst.1, hfirst.2.1⟩, hfirst.2.2.1.le, hfirst.2.2.2⟩
  obtain ⟨pair, hpair, hmax⟩ := hpairsCompact.exists_isMaxOn
    ⟨(firstLeft, firstRight), hfirstPair⟩
    (continuous_snd.sub continuous_fst).continuousOn
  have hpositive : 0 < pair.2 - pair.1 :=
    lt_of_lt_of_le (sub_pos.mpr hfirst.2.2.1) (hmax hfirstPair)
  refine ⟨pair.1, pair.2, ⟨hpair.1.1, hpair.1.2, sub_pos.mp hpositive,
    hpair.2.2⟩, ?_⟩
  intro otherLeft otherRight hother
  exact hmax (show (otherLeft, otherRight) ∈ pairs from
    ⟨⟨hother.1, hother.2.1⟩, hother.2.2.1.le, hother.2.2.2⟩)

/-- Maximal gap length bounds an actual successor from any compact-set
member below another member. Equality in the bound is retained. -/
theorem exists_right_mem_sub_le_of_maximal_gap
    (K : Set ℝ) (hK : IsCompact K) {left right : ℝ}
    (hgap : IsGap K left right)
    (hmax : ∀ otherLeft otherRight, IsGap K otherLeft otherRight →
      otherRight - otherLeft ≤ right - left)
    {current upper : ℝ} (hcurrent : current ∈ K) (hupper : upper ∈ K)
    (hlt : current < upper) :
    ∃ next ∈ K, current < next ∧ next - current ≤ right - left := by
  by_cases hshort : upper - current ≤ right - left
  · exact ⟨upper, hupper, hlt, hshort⟩
  · by_contra hnot
    let threshold := current + (right - left)
    have hthresholdUpper : threshold ≤ upper := by
      dsimp only [threshold]
      linarith
    obtain ⟨next, hnext, hnextMin⟩ :=
      (hK.inter_right isClosed_Ici).exists_isMinOn
        ⟨upper, hupper, hthresholdUpper⟩ continuous_id.continuousOn
    have hnextLt : current < next := by
      have hgapPositive := sub_pos.mpr hgap.2.2.1
      have hnextLower : current + (right - left) ≤ next := hnext.2
      linarith
    have hnextGap : IsGap K current next := by
      refine ⟨hcurrent, hnext.1, hnextLt, ?_⟩
      intro point hpoint
      by_cases hside : point ≤ current
      · exact Or.inl hside
      · right
        by_cases hthreshold : threshold ≤ point
        · exact hnextMin ⟨hpoint, hthreshold⟩
        · exfalso
          apply hnot
          refine ⟨point, hpoint, lt_of_not_ge hside, ?_⟩
          dsimp only [threshold] at hthreshold
          linarith
    exact hnot ⟨next, hnext.1, hnextLt, hmax current next hnextGap⟩

/-- The symmetric actual predecessor bound, obtained through the same
compact-order argument without assuming symmetry of the compact set. -/
theorem exists_left_mem_sub_le_of_maximal_gap
    (K : Set ℝ) (hK : IsCompact K) {left right : ℝ}
    (hgap : IsGap K left right)
    (hmax : ∀ otherLeft otherRight, IsGap K otherLeft otherRight →
      otherRight - otherLeft ≤ right - left)
    {current lower : ℝ} (hcurrent : current ∈ K) (hlower : lower ∈ K)
    (hlt : lower < current) :
    ∃ previous ∈ K, previous < current ∧ current - previous ≤ right - left := by
  by_cases hshort : current - lower ≤ right - left
  · exact ⟨lower, hlower, hlt, hshort⟩
  · by_contra hnot
    let threshold := current - (right - left)
    have hthresholdLower : lower ≤ threshold := by
      dsimp only [threshold]
      linarith
    obtain ⟨previous, hprevious, hpreviousMax⟩ :=
      (hK.inter_right isClosed_Iic).exists_isMaxOn
        ⟨lower, hlower, hthresholdLower⟩ continuous_id.continuousOn
    have hpreviousLt : previous < current := by
      have hgapPositive := sub_pos.mpr hgap.2.2.1
      have hpreviousUpper : previous ≤ current - (right - left) := hprevious.2
      linarith
    have hpreviousGap : IsGap K previous current := by
      refine ⟨hprevious.1, hcurrent, hpreviousLt, ?_⟩
      intro point hpoint
      by_cases hside : current ≤ point
      · exact Or.inr hside
      · left
        by_cases hthreshold : point ≤ threshold
        · exact hpreviousMax ⟨hpoint, hthreshold⟩
        · exfalso
          apply hnot
          refine ⟨point, hpoint, lt_of_not_ge hside, ?_⟩
          dsimp only [threshold] at hthreshold
          linarith
    exact hnot ⟨previous, hprevious.1, hpreviousLt, hmax previous current hpreviousGap⟩

/-- An arbitrary interior threshold has an actual compact-set point to its
right within maximal gap length. The threshold need not itself belong to K. -/
theorem exists_right_mem_sub_le_of_interior_threshold
    (K : Set ℝ) (hK : IsCompact K) {left right a b threshold : ℝ}
    (hgap : IsGap K left right)
    (hmax : ∀ otherLeft otherRight, IsGap K otherLeft otherRight →
      otherRight - otherLeft ≤ right - left)
    (ha : a ∈ K) (hb : b ∈ K) (hthreshold : threshold ∈ Ioo a b) :
    ∃ next ∈ K, threshold < next ∧ next - threshold ≤ right - left := by
  by_cases hmem : threshold ∈ K
  · exact exists_right_mem_sub_le_of_maximal_gap K hK hgap hmax
      hmem hb hthreshold.2
  · obtain ⟨previous, next, hlocalGap, hprevious, hnext⟩ :=
      exists_gap_of_mem_interval_not_mem K hK ha hb
        ⟨hthreshold.1.le, hthreshold.2.le⟩ hmem
    refine ⟨next, hlocalGap.2.1, hnext, ?_⟩
    have hbound := hmax previous next hlocalGap
    linarith

end Math.Topology
