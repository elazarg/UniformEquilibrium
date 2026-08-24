/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ChargedPathBudget

/-!
# Finite reachability rank for failed charged returns

Let a charged relation carry a finite label on every state.  Suppose no path
whose two endpoint labels agree contains an edge above a fixed charge
threshold.  For a state `s`, collect the labels reachable from `s` by finite
paths.  Reachability makes this finite set weakly decrease along every edge.
Across a threshold-charged edge the decrease is strict: the source label is
reachable from the source by the empty path, while reachability of that same
label from the target would close a forbidden labelled return through the
charged edge.

Thus the cardinality of the reachable-label set is an explicit well-founded
rank.  It strictly decreases at every high-charge edge, and bounds the number
of such edges on every path.  Applied after finitely labelling a compact payoff
carrier by small-diameter cells, this is the exact contrapositive of the
charged payoff near-return mechanism; importantly, it only uses subpaths of
one literal admissible path and never stitches unrelated cell transitions.
-/

noncomputable section

universe u v w

namespace Math
namespace ChargedPathBudget
namespace ChargedRelation

variable {State : Type u} {Edge : Type v} {Label : Type w}
variable (R : ChargedRelation State Edge)

/-- Finite labels of states reachable by a finite path from `source`. -/
noncomputable def reachableLabels [Fintype Label] [DecidableEq Label]
    (label : State → Label) (source : State) : Finset Label := by
  classical
  exact Finset.univ.filter fun fixed =>
    ∃ target, Nonempty (R.Path source target) ∧ label target = fixed

@[simp] theorem mem_reachableLabels_iff
    [Fintype Label] [DecidableEq Label]
    (label : State → Label) (source : State) (fixed : Label) :
    fixed ∈ R.reachableLabels label source ↔
      ∃ target, Nonempty (R.Path source target) ∧ label target = fixed := by
  classical
  simp [reachableLabels]

/-- The source's own label is reachable by the empty path. -/
theorem label_mem_reachableLabels
    [Fintype Label] [DecidableEq Label]
    (label : State → Label) (source : State) :
    label source ∈ R.reachableLabels label source := by
  rw [R.mem_reachableLabels_iff]
  exact ⟨source, ⟨.nil source⟩, rfl⟩

/-- Reachable labels weakly decrease after traversing an edge. -/
theorem reachableLabels_tgt_subset_src
    [Fintype Label] [DecidableEq Label]
    (label : State → Label) (edge : Edge) :
    R.reachableLabels label (R.tgt edge) ⊆
      R.reachableLabels label (R.src edge) := by
  intro fixed hfixed
  rw [R.mem_reachableLabels_iff] at hfixed ⊢
  obtain ⟨target, ⟨path⟩, hlabel⟩ := hfixed
  exact ⟨target, ⟨.cons edge path⟩, hlabel⟩

/-- There is no high-charge labelled return when every path with equal
endpoint labels has zero high-charge count. -/
def HasNoHighChargeLabelReturn
    (label : State → Label) (threshold : ℝ) : Prop :=
  ∀ {source target} (path : R.Path source target),
    label source = label target → path.highChargeCount threshold = 0

/-- If an edge is high-charge, its source label is not reachable from its
target; otherwise prepending the edge would give a forbidden labelled return. -/
theorem label_src_not_mem_reachableLabels_tgt
    [Fintype Label] [DecidableEq Label]
    (label : State → Label) (threshold : ℝ)
    (hnoReturn : R.HasNoHighChargeLabelReturn label threshold)
    (edge : Edge) (hhigh : threshold ≤ R.charge edge) :
    label (R.src edge) ∉ R.reachableLabels label (R.tgt edge) := by
  intro hreachable
  rw [R.mem_reachableLabels_iff] at hreachable
  obtain ⟨target, ⟨path⟩, hlabel⟩ := hreachable
  have hzero := hnoReturn (.cons edge path) hlabel.symm
  have hpositive :
      0 < (Path.cons edge path).highChargeCount threshold := by
    simp [Path.highChargeCount_cons, hhigh]
  exact (Nat.ne_of_gt hpositive) hzero

/-- Reachable labels strictly decrease across every high-charge edge. -/
theorem reachableLabels_tgt_ssubset_src
    [Fintype Label] [DecidableEq Label]
    (label : State → Label) (threshold : ℝ)
    (hnoReturn : R.HasNoHighChargeLabelReturn label threshold)
    (edge : Edge) (hhigh : threshold ≤ R.charge edge) :
    R.reachableLabels label (R.tgt edge) ⊂
      R.reachableLabels label (R.src edge) := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨R.reachableLabels_tgt_subset_src label edge, ?_⟩
  intro heq
  have hsource := R.label_mem_reachableLabels label (R.src edge)
  have htarget : label (R.src edge) ∈
      R.reachableLabels label (R.tgt edge) := by
    rw [heq]
    exact hsource
  exact R.label_src_not_mem_reachableLabels_tgt label threshold
    hnoReturn edge hhigh htarget

/-- Cardinality of the finite set of labels reachable from a state. -/
noncomputable def reachableLabelRank
    [Fintype Label] [DecidableEq Label]
    (label : State → Label) (source : State) : ℕ :=
  (R.reachableLabels label source).card

/-- The reachability rank weakly decreases across every edge. -/
theorem reachableLabelRank_tgt_le_src
    [Fintype Label] [DecidableEq Label]
    (label : State → Label) (edge : Edge) :
    R.reachableLabelRank label (R.tgt edge) ≤
      R.reachableLabelRank label (R.src edge) := by
  exact Finset.card_le_card (R.reachableLabels_tgt_subset_src label edge)

/-- The reachability rank strictly decreases across every high-charge edge. -/
theorem reachableLabelRank_tgt_lt_src
    [Fintype Label] [DecidableEq Label]
    (label : State → Label) (threshold : ℝ)
    (hnoReturn : R.HasNoHighChargeLabelReturn label threshold)
    (edge : Edge) (hhigh : threshold ≤ R.charge edge) :
    R.reachableLabelRank label (R.tgt edge) <
      R.reachableLabelRank label (R.src edge) := by
  exact Finset.card_lt_card
    (R.reachableLabels_tgt_ssubset_src label threshold hnoReturn edge hhigh)

/-- Along a path, the number of high-charge edges plus the terminal rank is
bounded by the initial rank.  This is the quantitative finite-rank form of
failed labelled recurrence. -/
theorem highChargeCount_add_reachableLabelRank_le
    [Fintype Label] [DecidableEq Label]
    (label : State → Label) (threshold : ℝ)
    (hnoReturn : R.HasNoHighChargeLabelReturn label threshold)
    {source target : State} (path : R.Path source target) :
    path.highChargeCount threshold + R.reachableLabelRank label target ≤
      R.reachableLabelRank label source := by
  induction path with
  | nil state => simp
  | cons edge rest ih =>
      by_cases hhigh : threshold ≤ R.charge edge
      · have hrank := R.reachableLabelRank_tgt_lt_src
          label threshold hnoReturn edge hhigh
        simp only [Path.highChargeCount_cons, hhigh, if_true]
        omega
      · have hrank := R.reachableLabelRank_tgt_le_src label edge
        simp only [Path.highChargeCount_cons, hhigh, if_false]
        omega

/-- In particular, every path contains at most `Fintype.card Label`
high-charge edges. -/
theorem highChargeCount_le_card_label
    [Fintype Label] [DecidableEq Label]
    (label : State → Label) (threshold : ℝ)
    (hnoReturn : R.HasNoHighChargeLabelReturn label threshold)
    {source target : State} (path : R.Path source target) :
    path.highChargeCount threshold ≤ Fintype.card Label := by
  have hpath := R.highChargeCount_add_reachableLabelRank_le
    label threshold hnoReturn path
  have hrank : R.reachableLabelRank label source ≤ Fintype.card Label := by
    unfold reachableLabelRank
    exact Finset.card_le_univ _
  omega

end ChargedRelation
end ChargedPathBudget
end Math
