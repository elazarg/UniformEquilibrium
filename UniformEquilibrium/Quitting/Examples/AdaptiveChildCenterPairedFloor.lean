import MathUE.Topology.FiniteLabelSubsequence
import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterAnchorDeletedGain
import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterAnchoredChildren

/-! # Universal positive parent-plus-unchanged-child floor at the center

The constant precedes the actual profile and the omitted player. The proof
uses actual bad profiles and a fixed deletion subsequence, not infeasibility
of a certificate system or a positive parent-only exploitability floor.
-/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open Filter Topology

theorem eventually_every_child_exploitability_lower
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (herror : Tendsto (fun index => quittingTerminalExploitability reward (profiles index))
      atTop (nhds 0)) (deleted : Fin 4) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ index in atTop, 1 / 8 - eta ≤
      quittingTerminalExploitability (childReward deleted)
        (restrictedProfileOfParent deleted (profiles index)) := by
  by_cases hanchor : deleted = 3
  · subst deleted
    exact eventually_anchor_deleted_exploitability_lower profiles herror heta
  · obtain ⟨active, hactive⟩ := Fin.exists_castSucc_eq.2 hanchor
    subst deleted
    filter_upwards [eventually_anchored_child_exploitability_lower profiles herror active heta]
      with index hindex
    linarith

/-- The reviewed bad-sequence argument yields a uniform positive paired
floor for EVERY actual profile and EVERY omitted player at the center. -/
theorem exists_center_parent_child_exploitability_floor :
    ∃ floor : ℝ, 0 < floor ∧
      ∀ parent : (quittingGame reward).BehaviorProfile, ∀ deleted : Fin 4,
        floor ≤ quittingTerminalExploitability reward parent +
          quittingTerminalExploitability (childReward deleted)
            (restrictedProfileOfParent deleted parent) := by
  classical
  by_contra hnone
  push Not at hnone
  have hchoose : ∀ index : ℕ,
      ∃ parent : (quittingGame reward).BehaviorProfile, ∃ deleted : Fin 4,
        quittingTerminalExploitability reward parent +
          quittingTerminalExploitability (childReward deleted)
            (restrictedProfileOfParent deleted parent) < 1 / ((index : ℝ) + 1) := by
    intro index
    exact hnone (1 / ((index : ℝ) + 1)) (by positivity)
  choose profiles deletion hsmall using hchoose
  have htail : Tendsto (fun index : ℕ => 1 / ((index : ℝ) + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hparent : Tendsto (fun index => quittingTerminalExploitability reward (profiles index))
      atTop (nhds 0) := by
    apply squeeze_zero'
      (Eventually.of_forall fun index => quittingTerminalExploitability_nonneg reward _) ?_ htail
    apply Eventually.of_forall
    intro index
    have hchild := quittingTerminalExploitability_nonneg (childReward (deletion index))
      (restrictedProfileOfParent (deletion index) (profiles index))
    linarith [hsmall index]
  have hchild : Tendsto (fun index => quittingTerminalExploitability (childReward (deletion index))
      (restrictedProfileOfParent (deletion index) (profiles index))) atTop (nhds 0) := by
    apply squeeze_zero'
      (Eventually.of_forall fun index => quittingTerminalExploitability_nonneg _ _) ?_ htail
    apply Eventually.of_forall
    intro index
    have hparentNonneg := quittingTerminalExploitability_nonneg reward (profiles index)
    linarith [hsmall index]
  obtain ⟨deleted, subsequence, hmono, hfixed⟩ :=
    _root_.Math.exists_fixed_label_on_strictMono_subsequence deletion
  have hparentSub : Tendsto
      (fun index => quittingTerminalExploitability reward (profiles (subsequence index)))
      atTop (nhds 0) := hparent.comp hmono.tendsto_atTop
  have hchildSub : Tendsto (fun index => quittingTerminalExploitability (childReward deleted)
      (restrictedProfileOfParent deleted (profiles (subsequence index)))) atTop (nhds 0) := by
    have hlimit := hchild.comp hmono.tendsto_atTop
    exact hlimit.congr fun index => by
      dsimp only [Function.comp_apply]
      rw [hfixed index]
  have hlower := eventually_every_child_exploitability_lower
    (profiles ∘ subsequence) hparentSub deleted (eta := 1 / 16) (by norm_num)
  have hupper : ∀ᶠ index in atTop,
      quittingTerminalExploitability (childReward deleted)
        (restrictedProfileOfParent deleted (profiles (subsequence index))) < 1 / 16 :=
    (tendsto_order.1 hchildSub).2 _ (by norm_num)
  obtain ⟨index, hlow, hupp⟩ := (hlower.and hupper).exists
  norm_num [Function.comp_def] at hlow
  linarith

end GameTheory.AdaptiveChildCenter
