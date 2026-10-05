import UniformEquilibrium.Quitting.Classification.SupportSpecificQuittingPremiumLeavers

/-! # All-passive reward perturbation and participant invariance

Only nonempty terminal coalitions are in the reward domain. Arbitrary signed
increments leave every participant entry, own singleton, trap, core, and maximal
protected set unchanged. Positive increments strictify all weak trap-leave comparisons.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def passiveQuittingRewardPerturbation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) : ℝ :=
  if player ∈ terminal.val then reward terminal player else reward terminal player + delta

omit [Fintype ι] in
theorem passiveQuittingRewardPerturbation_participant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) (hmember : player ∈ terminal.val) :
    passiveQuittingRewardPerturbation reward delta terminal player = reward terminal player := by
  simp [passiveQuittingRewardPerturbation, hmember]

omit [Fintype ι] in
theorem passiveQuittingRewardPerturbation_passive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) (hmember : player ∉ terminal.val) :
    passiveQuittingRewardPerturbation reward delta terminal player =
      reward terminal player + delta := by
  simp [passiveQuittingRewardPerturbation, hmember]

omit [Fintype ι] in
@[simp] theorem passiveQuittingRewardPerturbation_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ) (player : ι) :
    passiveQuittingRewardPerturbation reward delta (quittingSingletonTerminal player) player =
      reward (quittingSingletonTerminal player) player := by
  exact passiveQuittingRewardPerturbation_participant reward delta _ player
    (by simp [quittingSingletonTerminal])

omit [Fintype ι] in
theorem abs_passiveQuittingRewardPerturbation_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) :
    |passiveQuittingRewardPerturbation reward delta terminal player - reward terminal player| ≤
      |delta| := by
  by_cases hmember : player ∈ terminal.val
  · rw [passiveQuittingRewardPerturbation_participant reward delta terminal player hmember]
    simp
  · rw [passiveQuittingRewardPerturbation_passive reward delta terminal player hmember]
    simp

omit [Fintype ι] in
theorem passiveQuittingRewardPerturbation_participant_positive_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ)
    (player : ι) (coalition : Finset ι) (hmember : player ∈ coalition) :
    HasPositiveOwnQuittingPremium (passiveQuittingRewardPerturbation reward delta)
        player coalition ↔
      HasPositiveOwnQuittingPremium reward player coalition := by
  unfold HasPositiveOwnQuittingPremium
  rw [passiveQuittingRewardPerturbation_singleton]
  apply exists_congr
  intro hnonempty
  rw [passiveQuittingRewardPerturbation_participant reward delta ⟨coalition, hnonempty⟩
    player hmember]

omit [Fintype ι] in
theorem passiveQuittingRewardPerturbation_trap_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ) (active : Finset ι) :
    IsQuittingPremiumTrap (passiveQuittingRewardPerturbation reward delta) active ↔
      IsQuittingPremiumTrap reward active := by
  unfold IsQuittingPremiumTrap MathUE.IsFiniteCoalitionPremiumTrap
  apply and_congr Iff.rfl
  apply forall_congr'
  intro player
  apply imp_congr_right
  intro _hactive
  apply exists_congr
  intro coalition
  apply and_congr Iff.rfl
  apply and_congr_right
  intro hmember
  exact passiveQuittingRewardPerturbation_participant_positive_iff
    reward delta player coalition hmember

theorem passiveQuittingRewardPerturbation_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ) :
    quittingPremiumCore (passiveQuittingRewardPerturbation reward delta) =
      quittingPremiumCore reward := by
  ext player
  rw [quittingPremiumCore, quittingPremiumCore,
    MathUE.mem_finiteCoalitionPremiumCore_iff, MathUE.mem_finiteCoalitionPremiumCore_iff]
  change (∃ active,
      IsQuittingPremiumTrap (passiveQuittingRewardPerturbation reward delta) active ∧
      player ∈ active) ↔ ∃ active, IsQuittingPremiumTrap reward active ∧ player ∈ active
  simp only [passiveQuittingRewardPerturbation_trap_iff]

omit [Fintype ι] in
theorem passiveQuittingRewardPerturbation_protectedPremiums_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ) (protectedPlayers : Finset ι) :
    HasProtectedParticipantPremiums (passiveQuittingRewardPerturbation reward delta)
        protectedPlayers ↔
      HasProtectedParticipantPremiums reward protectedPlayers := by
  constructor
  · intro hpremiums player hplayer terminal hmember
    have h := hpremiums player hplayer terminal hmember
    rw [passiveQuittingRewardPerturbation_singleton,
      passiveQuittingRewardPerturbation_participant reward delta terminal player hmember] at h
    exact h
  · intro hpremiums player hplayer terminal hmember
    rw [passiveQuittingRewardPerturbation_singleton,
      passiveQuittingRewardPerturbation_participant reward delta terminal player hmember]
    exact hpremiums player hplayer terminal hmember

theorem passiveQuittingRewardPerturbation_maximalProtectedPlayers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ) :
    quittingMaximalProtectedPlayers (passiveQuittingRewardPerturbation reward delta) =
      quittingMaximalProtectedPlayers reward := by
  apply Finset.Subset.antisymm
  · have hnear := (hasProtectedParticipantPremiums_iff_subset_maximalProtectedPlayers
      (passiveQuittingRewardPerturbation reward delta)
      (quittingMaximalProtectedPlayers (passiveQuittingRewardPerturbation reward delta))).2
        Finset.Subset.rfl
    exact (hasProtectedParticipantPremiums_iff_subset_maximalProtectedPlayers reward _).1
      ((passiveQuittingRewardPerturbation_protectedPremiums_iff reward delta _).1 hnear)
  · have hold := (hasProtectedParticipantPremiums_iff_subset_maximalProtectedPlayers reward
      (quittingMaximalProtectedPlayers reward)).2 Finset.Subset.rfl
    exact (hasProtectedParticipantPremiums_iff_subset_maximalProtectedPlayers
      (passiveQuittingRewardPerturbation reward delta) _).1
        ((passiveQuittingRewardPerturbation_protectedPremiums_iff reward delta _).2 hold)

omit [Fintype ι] in
/-- The same designated leaver for each unchanged trap becomes strict.
The passive endpoint increases and its inserted participant endpoint does not. -/
theorem passiveQuittingRewardPerturbation_strictLeavers_of_weakLeavers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (protectedPlayers : Finset ι)
    (hleavers : HasSupportSpecificQuittingLeavers reward protectedPlayers (· ≤ ·))
    (delta : ℝ) (hdelta : 0 < delta) :
    HasSupportSpecificQuittingLeavers (passiveQuittingRewardPerturbation reward delta)
      protectedPlayers (· < ·) := by
  intro active htrap
  obtain ⟨player, hplayer, hprotected, hleave⟩ := hleavers active
    ((passiveQuittingRewardPerturbation_trap_iff reward delta active).1 htrap)
  refine ⟨player, hplayer, hprotected, ?_⟩
  intro coalition hnonempty hsubset
  have hnot : player ∉ coalition := by
    intro hmember
    exact (Finset.mem_erase.mp (hsubset hmember)).1 rfl
  rw [passiveQuittingRewardPerturbation_participant reward delta
    ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player (Finset.mem_insert_self _ _),
    passiveQuittingRewardPerturbation_passive reward delta ⟨coalition, hnonempty⟩ player hnot]
  have hweak := hleave coalition hnonempty hsubset
  linarith

end GameTheory
