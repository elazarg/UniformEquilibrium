import UniformEquilibrium.Quitting.Classification.JoiningAttractiveCoreGenericReturn
import UniformEquilibrium.Quitting.Projective.SelectedSingletonSublevelReturnSmoothDrift

/-! # Actual selected return at every attractive-core source

Closed exact-root return restores arbitrary annotations from the dense tie
domain. Strict deficit and pure-core exclusion persist on an open source
neighborhood. No source bound is needed by the classification, so boxed
boundary sources are included without an interior-source restriction.
-/

noncomputable section

namespace GameTheory

open Set QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_exactRoot_singletonSublevel_of_joiningAttractive_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hattractive : HasStrictJoiningAttractivePremiumCore reward)
    (hcard : (quittingPremiumCore reward).card = 3)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hnopure : ¬IsεQuittingRootNash reward tail 0
      (quittingPureSetRoot (quittingPremiumCore reward))) :
    ∃ root, IsεQuittingRootNash reward tail 0 root ∧
      ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
        reward (quittingSingletonTerminal player) player := by
  exact exists_exactRoot_singletonSublevel_of_dense_sources_excluding_root reward
    (quittingPairTieAvoidanceDomain reward (quittingCoreOrderedPairs reward))
    (dense_quittingCorePairTieAvoidanceDomain_of_joiningAttractive reward hattractive)
    (quittingPureSetRoot (quittingPremiumCore reward))
    (fun source havoid hsourceBelow hsourceNoPure =>
      exists_exactRoot_singletonSublevel_of_joiningAttractive_generic_tail
        reward source hattractive hcard havoid hsourceBelow hsourceNoPure)
    tail hbelow hnopure

theorem hasBoxedSelectedSingletonSublevelReturn_of_joiningAttractive_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hattractive : HasStrictJoiningAttractivePremiumCore reward)
    (hcard : (quittingPremiumCore reward).card = 3)
    (hnopure : ∀ tail, ¬IsεQuittingRootNash reward tail 0
      (quittingPureSetRoot (quittingPremiumCore reward)))
    (bound : ℝ) : HasBoxedSelectedSingletonSublevelReturn reward bound := by
  intro tail _ hbelow
  simpa only [quittingSoloReward, quittingSingletonTerminal] using
    exists_exactRoot_singletonSublevel_of_joiningAttractive_core
      reward tail hattractive hcard hbelow (hnopure tail)

end GameTheory
