import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Root.PairedProductRoot
import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-! # Pure coalition root Nash supplies an actual sure-exit payoff

At least two sure quitters leave no exposed continuation coordinate. Their literal
root Nash inequalities therefore imply the canonical sure-exit-set tests.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isQuittingSureExitSet_of_pureSetNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (active : Finset ι) (hcard : 2 ≤ active.card)
    (hnash : IsεQuittingRootNash reward tail 0 (quittingPureSetRoot active)) :
    IsQuittingSureExitSet reward active := by
  obtain ⟨first, hfirst, second, hsecond, hne⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < active.card)
  have hactive : active.Nonempty := ⟨first, hfirst⟩
  have hpayoff : ∀ player,
      quittingRootSuccessorPayoff reward tail (quittingPureSetRoot active) player =
        quittingSetReward reward active player := by
    intro player
    unfold quittingRootSuccessorPayoff
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
      quittingRootAbsorbingContribution_pureSetRoot,
      stationaryContinueMass_pureSetRoot_of_nonempty hactive]
    ring
  constructor
  · intro player _
    have herase : (active.erase player).Nonempty := by
      by_cases heq : player = first
      · exact ⟨second, Finset.mem_erase.mpr ⟨by simpa [heq] using hne.symm, hsecond⟩⟩
      · exact ⟨first, Finset.mem_erase.mpr ⟨Ne.symm heq, hfirst⟩⟩
    have hcontinue := quittingRootContinuePayoff_le_successor_of_isZeroNash
      reward tail (quittingPureSetRoot active) player hnash
    rwa [quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
      tail active player herase, hpayoff] at hcontinue
  · intro player _
    have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
      reward tail (quittingPureSetRoot active) player hnash
    rwa [quittingRootQuitPayoff_pureSetRoot_eq_insert, hpayoff] at hquit

theorem isUniformEquilibriumPayoff_setReward_of_pureSetNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (active : Finset ι) (hcard : 2 ≤ active.card)
    (hnash : IsεQuittingRootNash reward tail 0 (quittingPureSetRoot active)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (quittingSetReward reward active) :=
  isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward
    (isQuittingSureExitSet_of_pureSetNash reward tail active hcard hnash)

omit [Fintype ι] in
theorem pairedRoot_pure_true_eq_pureSetRoot
    {first second : ι} (hne : first ≠ second) :
    PairedCycle.root first second (PMF.pure true) (PMF.pure true) =
      quittingPureSetRoot ({first, second} : Finset ι) := by
  funext player
  by_cases hfirst : player = first
  · subst player
    simp [quittingPureSetRoot, quittingSetAction, PairedCycle.root, hne]
  · by_cases hsecond : player = second
    · subst player
      simp [quittingPureSetRoot, quittingSetAction, PairedCycle.root]
    · simp [quittingPureSetRoot, quittingSetAction, PairedCycle.root, hfirst, hsecond]

theorem isQuittingSureExitSet_pair_of_purePairNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second)
    (hnash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true))) :
    IsQuittingSureExitSet reward ({first, second} : Finset ι) := by
  rw [pairedRoot_pure_true_eq_pureSetRoot hne] at hnash
  exact isQuittingSureExitSet_of_pureSetNash reward tail {first, second}
    (by simp [hne]) hnash

theorem isUniformEquilibriumPayoff_pairReward_of_purePairNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second)
    (hnash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true))) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSetReward reward {first, second}) :=
  isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward
    (isQuittingSureExitSet_pair_of_purePairNash reward tail hne hnash)

end GameTheory
