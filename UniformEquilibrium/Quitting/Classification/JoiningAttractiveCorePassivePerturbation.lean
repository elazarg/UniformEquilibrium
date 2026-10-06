import UniformEquilibrium.Quitting.Classification.JoiningAttractiveCoreSureCascade
import UniformEquilibrium.Quitting.Classification.ParticipantRewardInvariance

/-! # Localized passive core-entry decreases

Only a core player's passive payments on nonempty coalitions inside its
core complement are decreased. Participant entries, traps, core and own
singletons remain unchanged for every real perturbation size.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def HasWeakJoiningAttractivePremiumCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ player ∈ quittingPremiumCore reward,
    ∀ (coalition : Finset ι) (hnonempty : coalition.Nonempty),
      coalition ⊆ (quittingPremiumCore reward).erase player →
        reward ⟨coalition, hnonempty⟩ player ≤
          reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player

def joiningAttractiveCorePassivePerturbation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) : ℝ :=
  if player ∈ quittingPremiumCore reward ∧
      terminal.val ⊆ (quittingPremiumCore reward).erase player then
    reward terminal player - delta else reward terminal player

theorem joiningAttractiveCorePassivePerturbation_participant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) (hmember : player ∈ terminal.val) :
    joiningAttractiveCorePassivePerturbation reward delta terminal player =
      reward terminal player := by
  have hnot : ¬(player ∈ quittingPremiumCore reward ∧
      terminal.val ⊆ (quittingPremiumCore reward).erase player) := by
    rintro ⟨_, hsubset⟩
    exact Finset.notMem_erase player _ (hsubset hmember)
  simp only [joiningAttractiveCorePassivePerturbation, hnot, ite_false]

theorem joiningAttractiveCorePassivePerturbation_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ) (player : ι) :
    joiningAttractiveCorePassivePerturbation reward delta
      (quittingSingletonTerminal player) player =
        reward (quittingSingletonTerminal player) player :=
  joiningAttractiveCorePassivePerturbation_participant reward delta _ player
    (by simp [quittingSingletonTerminal])

theorem joiningAttractiveCorePassivePerturbation_trap_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ) (active : Finset ι) :
    IsQuittingPremiumTrap (joiningAttractiveCorePassivePerturbation reward delta) active ↔
      IsQuittingPremiumTrap reward active :=
  quittingPremiumTrap_iff_of_participantReward_eq reward _
    (joiningAttractiveCorePassivePerturbation_participant reward delta) active

theorem joiningAttractiveCorePassivePerturbation_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ) :
    quittingPremiumCore (joiningAttractiveCorePassivePerturbation reward delta) =
      quittingPremiumCore reward :=
  quittingPremiumCore_eq_of_participantReward_eq reward _
    (joiningAttractiveCorePassivePerturbation_participant reward delta)

theorem abs_joiningAttractiveCorePassivePerturbation_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) :
    |joiningAttractiveCorePassivePerturbation reward delta terminal player -
      reward terminal player| ≤ |delta| := by
  unfold joiningAttractiveCorePassivePerturbation
  split
  · simp only [sub_sub_cancel_left, abs_neg, le_refl]
  · simpa only [sub_self, abs_zero] using abs_nonneg delta

theorem joiningAttractiveCorePassivePerturbation_strict_of_weak
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hweak : HasWeakJoiningAttractivePremiumCore reward) (delta : ℝ) (hdelta : 0 < delta) :
    HasStrictJoiningAttractivePremiumCore
      (joiningAttractiveCorePassivePerturbation reward delta) := by
  intro player hplayer coalition hnonempty hsubset
  rw [joiningAttractiveCorePassivePerturbation_core] at hplayer hsubset
  have hcomparison := hweak player hplayer coalition hnonempty hsubset
  rw [joiningAttractiveCorePassivePerturbation_participant reward delta
    ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player (Finset.mem_insert_self _ _)]
  change (if player ∈ quittingPremiumCore reward ∧
    coalition ⊆ (quittingPremiumCore reward).erase player then
      reward ⟨coalition, hnonempty⟩ player - delta
    else reward ⟨coalition, hnonempty⟩ player) < _
  rw [ite_eq_left ⟨hplayer, hsubset⟩]
  exact (sub_lt_self _ hdelta).trans_le hcomparison

end GameTheory
