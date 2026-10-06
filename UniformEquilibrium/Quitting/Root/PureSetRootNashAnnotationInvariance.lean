import UniformEquilibrium.Quitting.Root.PureSetNashSureExit
import UniformEquilibrium.Quitting.Root.ForcedQuitEndpointStability

/-! # Pure coalitions with two sure quitters have annotation-independent Nash

Each player still faces another sure quitter after changing its action.
The singleton case is excluded: it retains an exposed Never continuation.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quittingRootSuccessorPayoff_pureSetRoot_eq_setReward_of_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {active : Finset ι} (hnonempty : active.Nonempty) :
    quittingRootSuccessorPayoff reward tail (quittingPureSetRoot active) =
      quittingSetReward reward active := by
  funext player
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_pureSetRoot,
    stationaryContinueMass_pureSetRoot_of_nonempty hnonempty]
  ring

theorem quittingRootEndpointDifference_pureSetRoot_eq_zeroTail_of_two_le_card
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (active : Finset ι) (hcard : 2 ≤ active.card) (player : ι) :
    quittingRootEndpointDifference reward tail (quittingPureSetRoot active) player =
      quittingRootEndpointDifference reward 0 (quittingPureSetRoot active) player := by
  obtain ⟨first, hfirst, second, hsecond, hne⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < active.card)
  by_cases hplayer : player = first
  · subst player
    exact quittingRootEndpointDifference_eq_zeroTail_of_sureOpponent reward tail
      (quittingPureSetRoot active) hne (by simp [quittingPureSetRoot, quittingSetAction, hsecond])
  · exact quittingRootEndpointDifference_eq_zeroTail_of_sureOpponent reward tail
      (quittingPureSetRoot active) hplayer
      (by simp [quittingPureSetRoot, quittingSetAction, hfirst])

theorem isZeroQuittingRootNash_pureSetRoot_at_annotation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail nearby : Payoff ι)
    (active : Finset ι) (hcard : 2 ≤ active.card)
    (hnash : IsεQuittingRootNash reward tail 0 (quittingPureSetRoot active)) :
    IsεQuittingRootNash reward nearby 0 (quittingPureSetRoot active) := by
  have hendpoint := (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward tail (quittingPureSetRoot active)).mpr hnash
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward nearby (quittingPureSetRoot active)).mp
  intro player
  have hgap :=
    (quittingRootEndpointDifference_pureSetRoot_eq_zeroTail_of_two_le_card
      reward nearby active hcard player).trans
      (quittingRootEndpointDifference_pureSetRoot_eq_zeroTail_of_two_le_card
        reward tail active hcard player).symm
  rw [hgap]
  exact hendpoint player

end GameTheory
