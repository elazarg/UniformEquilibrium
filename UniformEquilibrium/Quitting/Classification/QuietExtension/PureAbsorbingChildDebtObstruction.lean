import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-! # Profitable quiet lifts of exact absorbing children

An actual exact terminal Nash child has zero complete behavioral debts. If its
joint Never probability is zero, a profitable outsider deviation defeats every
arbitrary real weighted child-debt bound, even with an arbitrary finite signed
Never coefficient. Literal fixture tables must supply the profiles and gains.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A stationary child has the literal stationary Never extension of its root. -/
theorem quittingLiftDeletedProfile_stationary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (root : QuittingChildPlayer deleted → PMF Bool) :
    quittingLiftDeletedProfile reward deleted
        (quittingStationaryProfile (quittingDeleteReward reward deleted) root) =
      quittingStationaryProfile reward (quittingExtendDeletedRoot deleted root) := by
  funext player time history
  rfl

/-- The quiet lift of a pure child exit is the same pure exit in the parent. -/
theorem quittingLiftDeletedProfile_stationary_pureSetRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (active : Finset (QuittingChildPlayer deleted)) :
    quittingLiftDeletedProfile reward deleted
        (quittingStationaryProfile (quittingDeleteReward reward deleted)
          (QuittingSureSetOwnerRepair.quittingPureSetRoot active)) =
      quittingStationaryProfile reward
        (QuittingSureSetOwnerRepair.quittingPureSetRoot
          (active.map (Function.Embedding.subtype (p := fun who : ι => ¬ deleted who)))) := by
  rw [quittingLiftDeletedProfile_stationary]
  congr 1
  funext player
  by_cases hdeleted : deleted player
  · have hnot : player ∉ active.map
        (Function.Embedding.subtype (p := fun who : ι => ¬ deleted who)) := by
      rintro hmem
      obtain ⟨child, _, heq⟩ := Finset.mem_map.mp hmem
      change child.1 = player at heq
      exact child.2 (by simpa only [heq] using hdeleted)
    simp [quittingExtendDeletedRoot, hdeleted,
      QuittingSureSetOwnerRepair.quittingPureSetRoot,
      QuittingSureSetOwnerRepair.quittingSetAction, hnot]
  · have hmem : player ∈ active.map
        (Function.Embedding.subtype (p := fun who : ι => ¬ deleted who)) ↔
          (⟨player, hdeleted⟩ : QuittingChildPlayer deleted) ∈ active := by
      constructor
      · intro hplayer
        obtain ⟨child, hchild, heq⟩ := Finset.mem_map.mp hplayer
        have heq' : child = ⟨player, hdeleted⟩ := Subtype.ext heq
        exact heq' ▸ hchild
      · intro hchild
        exact Finset.mem_map_of_mem _ hchild
    simp [quittingExtendDeletedRoot, hdeleted,
      QuittingSureSetOwnerRepair.quittingPureSetRoot,
      QuittingSureSetOwnerRepair.quittingSetAction, hmem]

/-- Exact terminal Nash makes each complete behavioral deviation debt zero. -/
theorem quittingBehaviorDeviationDebt_eq_zero_of_exact_terminalNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 profile) (who : ι) :
    quittingBehaviorDeviationPayoffCap reward profile who -
      quittingTerminalPayoff reward profile who = 0 := by
  rw [quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
  apply sub_eq_zero.mpr
  apply le_antisymm
  · apply quittingBestReplyValue_le
    intro deviation
    simpa only [add_zero] using hnash who deviation
  · simpa only [Function.update_eq_self] using
      le_quittingBestReplyValue reward profile who (profile who)

/-- This actual outsider gain cannot be charged to the exact child or Never.
Child weights and the finite Never coefficient may be arbitrary real numbers. -/
theorem quietLift_gain_gt_weighted_childDebt_add_never_of_exact_child
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile)
    (hnash : (quittingGame (quittingDeleteReward reward deleted)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeleteReward reward deleted)) 0 profile)
    (hnever : (∏ child, (quittingBehaviorStoppingLaw
      (quittingDeleteReward reward deleted) (profile child) none).toReal) = 0)
    (outside : {who : ι // deleted who})
    (deviation : (quittingGame reward).BehaviorStrategy outside.1)
    (hgain : 0 < quittingTerminalPayoff reward
        (Function.update (quittingLiftDeletedProfile reward deleted profile)
          outside.1 deviation) outside.1 -
      quittingTerminalPayoff reward
        (quittingLiftDeletedProfile reward deleted profile) outside.1)
    (weight : QuittingChildPlayer deleted → ℝ)
    (neverCoefficient : ℝ) :
    (∑ child, weight child *
      (quittingBehaviorDeviationPayoffCap (quittingDeleteReward reward deleted)
          profile child -
        quittingTerminalPayoff (quittingDeleteReward reward deleted) profile child)) +
        neverCoefficient * (∏ child, (quittingBehaviorStoppingLaw
          (quittingDeleteReward reward deleted) (profile child) none).toReal) <
      quittingTerminalPayoff reward
          (Function.update (quittingLiftDeletedProfile reward deleted profile)
            outside.1 deviation) outside.1 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 := by
  simp_rw [quittingBehaviorDeviationDebt_eq_zero_of_exact_terminalNash
    (quittingDeleteReward reward deleted) profile hnash]
  simpa only [mul_zero, Finset.sum_const_zero, hnever, zero_add] using hgain

end GameTheory
