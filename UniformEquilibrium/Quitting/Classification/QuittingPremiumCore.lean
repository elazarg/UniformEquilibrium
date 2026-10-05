import MathUE.FiniteCoalitionPremiumCore
import UniformEquilibrium.Quitting.Classification.QuittingPremiumSupportPeelingOrder
import UniformEquilibrium.Quitting.Classification.NonnegativeProductLowExactRootBoundary

/-! # Greatest premium core of an actual quitting reward table -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A premium trap for the actual strict own-premium relation. -/
def IsQuittingPremiumTrap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (active : Finset ι) : Prop :=
  MathUE.IsFiniteCoalitionPremiumTrap (HasPositiveOwnQuittingPremium reward) active

/-- The greatest premium core, computed from the actual reward table. -/
def quittingPremiumCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Finset ι :=
  MathUE.finiteCoalitionPremiumCore (HasPositiveOwnQuittingPremium reward)

omit [DecidableEq ι] in
theorem quittingPremiumCore_eq_empty_iff_weakSupportPeeling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingPremiumCore reward = ∅ ↔ HasWeakQuittingPremiumSupportPeeling reward :=
  MathUE.finiteCoalitionPremiumCore_eq_empty_iff (HasPositiveOwnQuittingPremium reward)

omit [Fintype ι] [DecidableEq ι] in
theorem not_hasPositiveOwnQuittingPremium_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) :
    ¬HasPositiveOwnQuittingPremium reward player {player} := by
  rintro ⟨hcoalition, hpositive⟩
  have heq : (⟨{player}, hcoalition⟩ : {S : Finset ι // S.Nonempty}) =
      quittingSingletonTerminal player := by
    rfl
  rw [heq] at hpositive
  exact lt_irrefl _ hpositive

omit [Fintype ι] [DecidableEq ι] in
theorem not_isQuittingPremiumTrap_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) :
    ¬IsQuittingPremiumTrap reward {player} :=
  MathUE.not_isFiniteCoalitionPremiumTrap_singleton _
    (not_hasPositiveOwnQuittingPremium_singleton reward) player

/-- Outsiders are flat on coalitions contained in their own extension of the
core face. This does not impose global outsider flatness. -/
theorem quittingPremiumCore_outsider_reward_eq_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (hcore : (quittingPremiumCore reward).Nonempty)
    (player : ι) (houtside : player ∉ quittingPremiumCore reward)
    (terminal : {S : Finset ι // S.Nonempty})
    (hsubset : terminal.val ⊆ insert player (quittingPremiumCore reward))
    (hmember : player ∈ terminal.val) :
    reward terminal player = reward (quittingSingletonTerminal player) player := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hpositive
    exact MathUE.not_positive_on_core_insert
      (HasPositiveOwnQuittingPremium reward) hcore player houtside
      terminal.val hsubset hmember ⟨terminal.property, hpositive⟩
  · exact hnonnegative terminal player hmember

omit [Fintype ι] [DecidableEq ι] in
/-- Any nontrap support has a participant whose actual rewards are flat inside
that support, under nonnegative participant premiums. -/
theorem exists_flat_participant_of_not_quittingPremiumTrap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (active : Finset ι) (hactive : active.Nonempty)
    (hnot : ¬IsQuittingPremiumTrap reward active) :
    ∃ player ∈ active, ∀ terminal : {S : Finset ι // S.Nonempty},
      terminal.val ⊆ active → player ∈ terminal.val →
        reward terminal player = reward (quittingSingletonTerminal player) player := by
  obtain ⟨player, hplayer, hflat⟩ :=
    (MathUE.not_isFiniteCoalitionPremiumTrap_iff
      (HasPositiveOwnQuittingPremium reward) active hactive).mp hnot
  refine ⟨player, hplayer, ?_⟩
  intro terminal hsubset hmember
  apply le_antisymm
  · apply le_of_not_gt
    intro hpositive
    exact hflat terminal.val hsubset hmember ⟨terminal.property, hpositive⟩
  · exact hnonnegative terminal player hmember

end GameTheory
