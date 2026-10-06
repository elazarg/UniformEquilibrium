import UniformEquilibrium.Quitting.Classification.SignedPairCoreSelectedReturn
import UniformEquilibrium.Quitting.Classification.Existence.SelectedSingletonSublevelReturnUniformPayoff
import UniformEquilibrium.Quitting.Classification.Existence.SupportwisePremiumUniformPayoff
import UniformEquilibrium.Quitting.Classification.SupportwiseQuittingPremiumNormalization
import UniformEquilibrium.Quitting.Root.PureSetNashSureExit

/-! # Actual uniform payoffs from signed empty or strict same-sign pair cores

The pure pair branch uses its sure-exit payoff. Otherwise the raw core and
joining gaps produce selected exact return internally. Participant premiums
may be signed; only own singletons are nonnegative in the strategic result.
-/

noncomputable section

namespace GameTheory

theorem exists_uniformEquilibriumPayoff_of_empty_quittingPremiumCore
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (hcore : quittingPremiumCore reward = ∅) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_supportwiseBalance reward hsingleton
  apply supportwiseBalance_of_weakPremiumPeeling
  have hpeeling := (quittingPremiumCore_eq_empty_iff_weakSupportPeeling reward).mp hcore
  intro active hactive
  obtain ⟨chosen, hchosen, hflat⟩ := hpeeling active hactive
  refine ⟨chosen, hchosen, ?_⟩
  intro terminal hterminal hsubset hmem
  apply le_of_not_gt
  intro hpositive
  exact hflat terminal hsubset hmem ⟨hterminal, hpositive⟩

theorem exists_uniformEquilibriumPayoff_of_signed_pair_core_strictSameSign
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    {first second : Fin 4} (hne : first ≠ second)
    (hcore : quittingPremiumCore reward = {first, second})
    (hjoining : 0 < quittingPairJoiningGap reward first second *
      quittingPairJoiningGap reward second first) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  classical
  by_cases hpure : ∃ tail : Payoff (Fin 4), IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true))
  · obtain ⟨tail, hnash⟩ := hpure
    exact ⟨_, isUniformEquilibriumPayoff_pairReward_of_purePairNash reward tail hne hnash⟩
  · apply exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn reward hsingleton
    apply hasBoxedSelectedSingletonSublevelReturn_of_signed_pair_core reward hne hcore hjoining
    intro tail hnash
    exact hpure ⟨tail, hnash⟩

theorem exists_uniformEquilibriumPayoff_of_empty_or_signed_pair_core_strictSameSign
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (hcore : quittingPremiumCore reward = ∅ ∨
      ∃ first second : Fin 4, first ≠ second ∧
        quittingPremiumCore reward = {first, second} ∧
        0 < quittingPairJoiningGap reward first second *
          quittingPairJoiningGap reward second first) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rcases hcore with hempty | ⟨first, second, hne, hpair, hjoining⟩
  · exact exists_uniformEquilibriumPayoff_of_empty_quittingPremiumCore reward hsingleton hempty
  · exact exists_uniformEquilibriumPayoff_of_signed_pair_core_strictSameSign
      reward hsingleton hne hpair hjoining

end GameTheory
