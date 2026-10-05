import UniformEquilibrium.Quitting.Classification.Existence.CommonQuittingPremiumLeaverRewardClosure

/-! # Greatest pair-core uniform payoff as a common-leaver instance -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isCommonQuittingPremiumLeaver_of_pairCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (first second : ι) (hcore : quittingPremiumCore reward = {first, second}) :
    IsCommonQuittingPremiumLeaver reward first := by
  refine ⟨fun terminal hmember => hnonnegative terminal first hmember, ?_⟩
  intro active htrap
  have hsubset := MathUE.IsFiniteCoalitionPremiumTrap.subset_core htrap
  change active ⊆ quittingPremiumCore reward at hsubset
  rw [hcore] at hsubset
  have heq := MathUE.IsFiniteCoalitionPremiumTrap.eq_pair_of_subset
    (not_hasPositiveOwnQuittingPremium_singleton reward) htrap first second hsubset
  rw [heq]
  simp

theorem exists_uniformEquilibriumPayoff_of_pairPremiumCore_weakLeave
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (hsingleton : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who)
    (first second : Fin 4) (hne : first ≠ second)
    (hcore : quittingPremiumCore reward = {first, second})
    (hleave : reward ⟨{first, second}, by simp⟩ first ≤
      reward (quittingSingletonTerminal second) first) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_commonLeaver_weakLeave
    reward hsingleton first (isCommonQuittingPremiumLeaver_of_pairCore
      reward hnonnegative first second hcore)
  intro coalition hcoalition hsubset
  have hpairErase : (quittingPremiumCore reward).erase first = {second} := by
    rw [hcore]
    simp [hne]
  have hsingle : coalition ⊆ {second} := by simpa only [hpairErase] using hsubset
  have heq : coalition = {second} := by
    obtain ⟨who, hwho⟩ := hcoalition
    have hwhoEq := Finset.mem_singleton.mp (hsingle hwho)
    apply Finset.Subset.antisymm hsingle
    exact Finset.singleton_subset_iff.mpr (hwhoEq ▸ hwho)
  subst coalition
  exact hleave

theorem exists_uniformEquilibriumPayoff_of_pairPremiumCore_strictLeave
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (hsingleton : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who)
    (first second : Fin 4) (hne : first ≠ second)
    (hcore : quittingPremiumCore reward = {first, second})
    (hleave : reward ⟨{first, second}, by simp⟩ first <
      reward (quittingSingletonTerminal second) first) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_commonLeaver_strictLeave
    reward hsingleton first (isCommonQuittingPremiumLeaver_of_pairCore
      reward hnonnegative first second hcore)
  intro coalition hcoalition hsubset
  have hpairErase : (quittingPremiumCore reward).erase first = {second} := by
    rw [hcore]
    simp [hne]
  have hsingle : coalition ⊆ {second} := by simpa only [hpairErase] using hsubset
  have heq : coalition = {second} := by
    obtain ⟨who, hwho⟩ := hcoalition
    have hwhoEq := Finset.mem_singleton.mp (hsingle hwho)
    apply Finset.Subset.antisymm hsingle
    exact Finset.singleton_subset_iff.mpr (hwhoEq ▸ hwho)
  subst coalition
  exact hleave

end GameTheory
