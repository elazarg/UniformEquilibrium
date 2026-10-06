import UniformEquilibrium.Quitting.Classification.JoiningAttractiveCoreGenericReturn
import UniformEquilibrium.Quitting.Root.SingletonSublevelReturnClosed
import UniformEquilibrium.Quitting.Projective.SelectedSingletonSublevelReturnSmoothDrift
import Mathlib.Topology.Neighborhoods

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
  let sources : Set (Payoff ι) := {source |
    (∃ player, source player < reward (quittingSingletonTerminal player) player) ∧
      ¬IsεQuittingRootNash reward source 0
        (quittingPureSetRoot (quittingPremiumCore reward))}
  have hbelowOpen := isOpen_iUnion fun player : ι =>
    isOpen_lt (continuous_apply player)
      (continuous_const (y := reward (quittingSingletonTerminal player) player))
  have hbelowSet : {source : Payoff ι | ∃ player,
      source player < reward (quittingSingletonTerminal player) player} =
      ⋃ player : ι, {source : Payoff ι |
        source player < reward (quittingSingletonTerminal player) player} := by
    ext source
    simp
  rw [← hbelowSet] at hbelowOpen
  have hpureClosed : IsClosed {source : Payoff ι | IsεQuittingRootNash reward source 0
      (quittingPureSetRoot (quittingPremiumCore reward))} := by
    simpa only [quittingRootOfSimplex_simplexOfRoot,
      isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash] using
      isClosed_setOf_isZeroQuittingRootEndpointNash_tail reward
        (quittingSimplexOfRoot (quittingPureSetRoot (quittingPremiumCore reward)))
  have hsourcesOpen : IsOpen sources := hbelowOpen.inter hpureClosed.isOpen_compl
  have hdense := dense_quittingCorePairTieAvoidanceDomain_of_joiningAttractive
    reward hattractive
  have hsubset : sources ∩
      quittingPairTieAvoidanceDomain reward (quittingCoreOrderedPairs reward) ⊆
      {source : Payoff ι | ∃ root, IsεQuittingRootNash reward source 0 root ∧
        ∃ player, quittingRootSuccessorPayoff reward source root player ≤
          reward (quittingSingletonTerminal player) player} := by
    intro source hsource
    exact exists_exactRoot_singletonSublevel_of_joiningAttractive_generic_tail
      reward source hattractive hcard hsource.2 hsource.1.1 hsource.1.2
  have hclosed := isClosed_setOf_exists_exactRoot_singletonSublevel reward
  exact (hclosed.closure_subset_iff.mpr hsubset)
    (hdense.open_subset_closure_inter hsourcesOpen ⟨hbelow, hnopure⟩)

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
