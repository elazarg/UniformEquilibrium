import UniformEquilibrium.Quitting.Classification.QuittingPremiumCore
import Mathlib.Topology.Algebra.Order.Field

/-! # Finite reward-coordinate neighborhoods preserve strict premium signs

Singleton participant gaps vanish identically. Every other nonzero participant
gap preserves its sign in a neighborhood of the complete reward table. The
result preserves the actual premium-trap inventory, not a supplied graph.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem positiveOwn_iff_gap_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) :
    HasPositiveOwnQuittingPremium reward player terminal.val ↔
      0 < reward terminal player - reward (quittingSingletonTerminal player) player := by
  constructor
  · rintro ⟨_, hpositive⟩
    exact sub_pos.mpr hpositive
  · intro hpositive
    exact ⟨terminal.property, sub_pos.mp hpositive⟩

theorem eventually_participantPremiums_iff_of_nonsingleton_gaps_ne_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hgaps : ∀ (terminal : {S : Finset ι // S.Nonempty}) (player : ι),
      player ∈ terminal.val → 2 ≤ terminal.val.card →
        reward terminal player - reward (quittingSingletonTerminal player) player ≠ 0) :
    ∀ᶠ nearby in 𝓝 reward,
      ∀ (terminal : {S : Finset ι // S.Nonempty}) (player : ι),
        player ∈ terminal.val →
          (HasPositiveOwnQuittingPremium nearby player terminal.val ↔
            HasPositiveOwnQuittingPremium reward player terminal.val) := by
  rw [Filter.eventually_all]
  intro terminal
  rw [Filter.eventually_all]
  intro player
  by_cases hmember : player ∈ terminal.val
  · by_cases hsingle : terminal.val.card = 1
    · obtain ⟨owner, howner⟩ := Finset.card_eq_one.mp hsingle
      have heq : owner = player := by
        exact (Finset.mem_singleton.mp (howner ▸ hmember)).symm
      have hterminal : terminal = quittingSingletonTerminal player := by
        apply Subtype.ext
        simpa only [heq, quittingSingletonTerminal] using howner
      exact Filter.Eventually.of_forall fun nearby _ => by
        rw [positiveOwn_iff_gap_pos, positiveOwn_iff_gap_pos, hterminal]
        simp
    · have hcard : 2 ≤ terminal.val.card := by
        have hpositive := Finset.card_pos.mpr terminal.property
        omega
      have hne := hgaps terminal player hmember hcard
      let gap := fun nearby : {S : Finset ι // S.Nonempty} → Payoff ι =>
        nearby terminal player - nearby (quittingSingletonTerminal player) player
      have hcontinuous : Continuous gap := by
        unfold gap
        fun_prop
      by_cases hpositive : 0 < gap reward
      · filter_upwards [hcontinuous.continuousAt.eventually_const_lt hpositive]
          with nearby hnear _
        rw [positiveOwn_iff_gap_pos, positiveOwn_iff_gap_pos]
        exact iff_of_true hnear hpositive
      · have hnegative : gap reward < 0 :=
          lt_of_le_of_ne (le_of_not_gt hpositive) hne
        filter_upwards [hcontinuous.continuousAt.eventually_lt_const hnegative]
          with nearby hnear _
        rw [positiveOwn_iff_gap_pos, positiveOwn_iff_gap_pos]
        exact iff_of_false (not_lt_of_ge hnear.le) hpositive
  · exact Filter.Eventually.of_forall fun _ hplayer => False.elim (hmember hplayer)

theorem eventually_premiumTraps_iff_of_nonsingleton_gaps_ne_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hgaps : ∀ (terminal : {S : Finset ι // S.Nonempty}) (player : ι),
      player ∈ terminal.val → 2 ≤ terminal.val.card →
        reward terminal player - reward (quittingSingletonTerminal player) player ≠ 0) :
    ∀ᶠ nearby in 𝓝 reward, ∀ active,
      IsQuittingPremiumTrap nearby active ↔ IsQuittingPremiumTrap reward active := by
  filter_upwards
    [eventually_participantPremiums_iff_of_nonsingleton_gaps_ne_zero reward hgaps]
    with nearby hnear active
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
  have hnonempty : coalition.Nonempty := ⟨player, hmember⟩
  exact hnear ⟨coalition, hnonempty⟩ player hmember

end GameTheory
