import UniformEquilibrium.Quitting.Classification.QuittingPremiumCore
import UniformEquilibrium.Quitting.Root.PairInactiveGapNumerator

/-! # The two passive singleton entries of a signed pair

Only the partner's singleton payment to each pair member changes. All
participant entries and own singletons remain literal, hence so do all traps
and the greatest core. The two joining gaps can be shifted independently.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [DecidableEq ι]

def signedPairPassivePerturbation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι) (firstShift secondShift : ℝ) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun terminal player =>
    if terminal.val = {second} ∧ player = first then reward terminal player - firstShift
    else if terminal.val = {first} ∧ player = second then
      reward terminal player - secondShift
    else reward terminal player

theorem signedPairPassivePerturbation_participant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstShift secondShift : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) (hmem : player ∈ terminal.val) :
    signedPairPassivePerturbation reward first second firstShift secondShift terminal player =
      reward terminal player := by
  have hfirst : ¬(terminal.val = {second} ∧ player = first) := by
    rintro ⟨heq, rfl⟩
    rw [heq, Finset.mem_singleton] at hmem
    exact hne hmem
  have hsecond : ¬(terminal.val = {first} ∧ player = second) := by
    rintro ⟨heq, rfl⟩
    rw [heq, Finset.mem_singleton] at hmem
    exact hne hmem.symm
  simp only [signedPairPassivePerturbation, hfirst, hsecond, ite_false]

theorem signedPairPassivePerturbation_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstShift secondShift : ℝ) (player : ι) :
    signedPairPassivePerturbation reward first second firstShift secondShift
      (quittingSingletonTerminal player) player =
        reward (quittingSingletonTerminal player) player :=
  signedPairPassivePerturbation_participant reward hne firstShift secondShift _ player
    (by simp [quittingSingletonTerminal])

theorem abs_signedPairPassivePerturbation_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι) (firstShift secondShift delta : ℝ)
    (hfirst : |firstShift| ≤ delta) (hsecond : |secondShift| ≤ delta)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) :
    |signedPairPassivePerturbation reward first second firstShift secondShift terminal player -
      reward terminal player| ≤ delta := by
  unfold signedPairPassivePerturbation
  split
  · simpa only [sub_sub_cancel_left, abs_neg] using hfirst
  · split
    · simpa only [sub_sub_cancel_left, abs_neg] using hsecond
    · simpa only [sub_self, abs_zero] using (abs_nonneg firstShift).trans hfirst

theorem signedPairPassivePerturbation_participant_positive_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstShift secondShift : ℝ)
    (player : ι) (coalition : Finset ι) (hmember : player ∈ coalition) :
    HasPositiveOwnQuittingPremium
        (signedPairPassivePerturbation reward first second firstShift secondShift)
        player coalition ↔ HasPositiveOwnQuittingPremium reward player coalition := by
  unfold HasPositiveOwnQuittingPremium
  rw [signedPairPassivePerturbation_singleton reward hne]
  apply exists_congr
  intro hnonempty
  rw [signedPairPassivePerturbation_participant reward hne firstShift secondShift
    ⟨coalition, hnonempty⟩ player hmember]

theorem signedPairPassivePerturbation_trap_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstShift secondShift : ℝ)
    (active : Finset ι) :
    IsQuittingPremiumTrap
        (signedPairPassivePerturbation reward first second firstShift secondShift) active ↔
      IsQuittingPremiumTrap reward active := by
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
  exact signedPairPassivePerturbation_participant_positive_iff
    reward hne firstShift secondShift player coalition hmember

theorem signedPairPassivePerturbation_core [Fintype ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstShift secondShift : ℝ) :
    quittingPremiumCore
        (signedPairPassivePerturbation reward first second firstShift secondShift) =
      quittingPremiumCore reward := by
  ext player
  rw [quittingPremiumCore, quittingPremiumCore,
    MathUE.mem_finiteCoalitionPremiumCore_iff, MathUE.mem_finiteCoalitionPremiumCore_iff]
  change (∃ active, IsQuittingPremiumTrap
      (signedPairPassivePerturbation reward first second firstShift secondShift) active ∧
      player ∈ active) ↔ ∃ active, IsQuittingPremiumTrap reward active ∧ player ∈ active
  simp only [signedPairPassivePerturbation_trap_iff reward hne]

theorem signedPairPassivePerturbation_joiningGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstShift secondShift : ℝ) :
    quittingPairJoiningGap
        (signedPairPassivePerturbation reward first second firstShift secondShift)
        first second = quittingPairJoiningGap reward first second + firstShift ∧
      quittingPairJoiningGap
        (signedPairPassivePerturbation reward first second firstShift secondShift)
        second first = quittingPairJoiningGap reward second first + secondShift := by
  constructor
  · unfold quittingPairJoiningGap
    rw [signedPairPassivePerturbation_participant reward hne firstShift secondShift
      ⟨{first, second}, by simp⟩ first (by simp)]
    simp only [signedPairPassivePerturbation, quittingSingletonTerminal,
      and_self, ite_true]
    ring
  · unfold quittingPairJoiningGap
    rw [signedPairPassivePerturbation_participant reward hne firstShift secondShift
      ⟨{second, first}, by simp⟩ second (by simp)]
    simp [signedPairPassivePerturbation, quittingSingletonTerminal, hne.symm]
    ring

end GameTheory
