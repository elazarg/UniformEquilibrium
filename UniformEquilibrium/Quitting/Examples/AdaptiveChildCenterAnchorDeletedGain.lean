import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterAdjacentMenu

/-! # Actual atom-move gain and the anchor-deleted one-eighth floor -/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open Filter Topology
open _root_.Math.Probability.DiscreteHazard.StoppingLaw
open _root_.Math.ProbabilityMassFunction

def anchorDeletedMoveStrategy (parent : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    (quittingGame (childReward 3)).BehaviorStrategy 0 :=
  quittingMoveStoppingAtomStrategy (childReward 3) (restrictedProfileOfParent 3 parent) 0
    (some cutoff) (some (cutoff + 1))

def anchorDeletedMoveGain (parent : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) : ℝ :=
  quittingTerminalPayoff (childReward 3)
      (Function.update (restrictedProfileOfParent 3 parent) 0
        (anchorDeletedMoveStrategy parent cutoff)) 0 -
    quittingTerminalPayoff (childReward 3) (restrictedProfileOfParent 3 parent) 0

@[simp] theorem anchorDeletedMoveStrategy_stoppingLaw
    (parent : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    quittingBehaviorStoppingLaw (childReward 3) (anchorDeletedMoveStrategy parent cutoff) =
      pmfMoveAtom (quittingBehaviorStoppingLaws reward parent 0)
        (some cutoff) (some (cutoff + 1)) := by
  rw [anchorDeletedMoveStrategy, quittingMoveStoppingAtomStrategy_stoppingLaw]
  simp [quittingBehaviorStoppingLaws, restrictedProfileOfParent_stoppingLaw,
    deletedEquiv, finSuccAboveEquiv_apply]
  rfl

theorem anchorDeletedMoveStrategy_none
    (parent : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    quittingBehaviorStoppingLaw (childReward 3) (anchorDeletedMoveStrategy parent cutoff) none =
      quittingBehaviorStoppingLaws reward parent 0 none := by
  rw [anchorDeletedMoveStrategy_stoppingLaw, pmfMoveAtom_adjacent_none]

theorem anchorDeletedMoveStrategy_other
    (parent : (quittingGame reward).BehaviorProfile) (cutoff other : ℕ)
    (hsource : other ≠ cutoff) (htarget : other ≠ cutoff + 1) :
    quittingBehaviorStoppingLaw (childReward 3)
        (anchorDeletedMoveStrategy parent cutoff) (some other) =
      quittingBehaviorStoppingLaws reward parent 0 (some other) := by
  rw [anchorDeletedMoveStrategy_stoppingLaw,
    pmfMoveAtom_adjacent_other _ _ _ hsource htarget]

/-- This is an actual independent replacement of only player zero's source
atom. The formula has no support, positive source mass, or tail hypothesis. -/
theorem actual_anchor_deleted_atom_move_gain
    (parent : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    anchorDeletedMoveGain parent cutoff =
      finiteMass (quittingBehaviorStoppingLaws reward parent 0) cutoff *
        (survival (quittingBehaviorStoppingLaws reward parent 1) cutoff *
            finiteMass (quittingBehaviorStoppingLaws reward parent 2) cutoff -
          finiteMass (quittingBehaviorStoppingLaws reward parent 1) cutoff *
            survival (quittingBehaviorStoppingLaws reward parent 2) cutoff +
          finiteMass (quittingBehaviorStoppingLaws reward parent 1) cutoff *
            finiteMass (quittingBehaviorStoppingLaws reward parent 2) cutoff) := by
  rw [anchorDeletedMoveGain, anchorDeletedMoveStrategy,
    quittingTerminalPayoff_moveStoppingAtom_gain, adjacent_child_menu_difference_raw]
  simp [quittingBehaviorStoppingLaws, restrictedProfileOfParent_stoppingLaw,
    deletedEquiv, finSuccAboveEquiv_apply, finiteMass]
  rfl

theorem anchorDeletedMoveGain_le_exploitability
    (parent : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    anchorDeletedMoveGain parent cutoff ≤
      quittingTerminalExploitability (childReward 3) (restrictedProfileOfParent 3 parent) := by
  have hnash := isεAsymptoticNash_of_quittingTerminalExploitability_le
    (restrictedProfileOfParent 3 parent) (le_refl _)
  have hreply := hnash 0 (anchorDeletedMoveStrategy parent cutoff)
  unfold anchorDeletedMoveGain
  linarith

/-- The actual quantile source produces a local gain tending to one eighth.
The cutoffs are selected internally; no favorable law sequence is supplied. -/
theorem exists_actual_anchor_deleted_gain_sequence
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (herror : Tendsto (fun index => quittingTerminalExploitability reward (profiles index))
      atTop (nhds 0)) :
    ∃ cutoff : ℕ → ℕ,
      Tendsto (fun index => anchorDeletedMoveGain (profiles index) (cutoff index))
        atTop (nhds (1 / 8)) := by
  obtain ⟨cutoff, _, _, _, hactive⟩ := exists_actual_quantile_rigidity profiles herror
  have hmassZero := (hactive 0).2.2
  have hmassOne := (hactive 1).2.2
  have hmassTwo := (hactive 2).2.2
  have hsurvivalOne := (hactive 1).2.1
  have hsurvivalTwo := (hactive 2).2.1
  have hlimit := hmassZero.mul
    (((hsurvivalOne.mul hmassTwo).sub (hmassOne.mul hsurvivalTwo)).add
      (hmassOne.mul hmassTwo))
  norm_num at hlimit
  refine ⟨cutoff, hlimit.congr ?_⟩
  intro index
  exact (actual_anchor_deleted_atom_move_gain (profiles index) (cutoff index)).symm

theorem eventually_anchor_deleted_exploitability_lower
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (herror : Tendsto (fun index => quittingTerminalExploitability reward (profiles index))
      atTop (nhds 0)) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ index in atTop, 1 / 8 - eta ≤
      quittingTerminalExploitability (childReward 3)
        (restrictedProfileOfParent 3 (profiles index)) := by
  obtain ⟨cutoff, hgain⟩ := exists_actual_anchor_deleted_gain_sequence profiles herror
  have hlower : ∀ᶠ index in atTop,
      1 / 8 - eta < anchorDeletedMoveGain (profiles index) (cutoff index) :=
    (tendsto_order.1 hgain).1 _ (sub_lt_self _ heta)
  filter_upwards [hlower] with index hindex
  exact hindex.le.trans (anchorDeletedMoveGain_le_exploitability _ _)

end GameTheory.AdaptiveChildCenter
