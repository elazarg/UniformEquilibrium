import UniformEquilibrium.Quitting.Classification.QuittingPremiumCore

/-! # Premium traps depend only on participant reward entries

No equality of outsider premiums is asserted. The relevant premium relation
is preserved on members of each coalition, which determines traps and core.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [DecidableEq ι]

omit [DecidableEq ι] in
theorem participant_positivePremium_iff_of_participantReward_eq
    (reward nearby : {S : Finset ι // S.Nonempty} → Payoff ι)
    (heq : ∀ terminal player, player ∈ terminal.val →
      nearby terminal player = reward terminal player)
    (player : ι) (coalition : Finset ι) (hmember : player ∈ coalition) :
    HasPositiveOwnQuittingPremium nearby player coalition ↔
      HasPositiveOwnQuittingPremium reward player coalition := by
  unfold HasPositiveOwnQuittingPremium
  rw [heq (quittingSingletonTerminal player) player (by simp [quittingSingletonTerminal])]
  apply exists_congr
  intro hnonempty
  rw [heq ⟨coalition, hnonempty⟩ player hmember]

omit [DecidableEq ι] in
theorem quittingPremiumTrap_iff_of_participantReward_eq
    (reward nearby : {S : Finset ι // S.Nonempty} → Payoff ι)
    (heq : ∀ terminal player, player ∈ terminal.val →
      nearby terminal player = reward terminal player)
    (active : Finset ι) :
    IsQuittingPremiumTrap nearby active ↔ IsQuittingPremiumTrap reward active := by
  unfold IsQuittingPremiumTrap MathUE.IsFiniteCoalitionPremiumTrap
  apply and_congr Iff.rfl
  apply forall_congr'
  intro player
  apply imp_congr_right
  intro _
  apply exists_congr
  intro coalition
  apply and_congr Iff.rfl
  apply and_congr_right
  intro hmember
  exact participant_positivePremium_iff_of_participantReward_eq
    reward nearby heq player coalition hmember

omit [DecidableEq ι] in
theorem quittingPremiumCore_eq_of_participantReward_eq [Fintype ι]
    (reward nearby : {S : Finset ι // S.Nonempty} → Payoff ι)
    (heq : ∀ terminal player, player ∈ terminal.val →
      nearby terminal player = reward terminal player) :
    quittingPremiumCore nearby = quittingPremiumCore reward := by
  ext player
  rw [quittingPremiumCore, quittingPremiumCore,
    MathUE.mem_finiteCoalitionPremiumCore_iff, MathUE.mem_finiteCoalitionPremiumCore_iff]
  change (∃ active, IsQuittingPremiumTrap nearby active ∧ player ∈ active) ↔
    ∃ active, IsQuittingPremiumTrap reward active ∧ player ∈ active
  simp only [quittingPremiumTrap_iff_of_participantReward_eq reward nearby heq]

end GameTheory
