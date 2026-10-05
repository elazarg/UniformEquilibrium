import UniformEquilibrium.Quitting.Classification.QuittingPremiumCore
import UniformEquilibrium.Quitting.Root.OneActiveCoalitionMass

/-! # Exact endpoint equality restricted to the actual active support -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Flatness is required only on coalitions in the forced player's extension
of the actual support; all zero-mass coalitions disappear from the canonical sum. -/
theorem quittingRootQuitPayoff_eq_singleton_of_support_participantReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (player : ι)
    (hconstant : ∀ terminal : {S : Finset ι // S.Nonempty},
      terminal.val ⊆ insert player (quittingPositiveHazardSupport root) →
      player ∈ terminal.val →
        reward terminal player = reward (quittingSingletonTerminal player) player) :
    quittingRootQuitPayoff reward tail root player =
      reward (quittingSingletonTerminal player) player := by
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass]
  calc
    _ = ∑ coalition ∈ (Finset.univ.erase player).powerset,
        quittingOpponentCoalitionMass root player coalition *
          reward (quittingSingletonTerminal player) player := by
      apply Finset.sum_congr rfl
      intro coalition _
      by_cases hzero : quittingOpponentCoalitionMass root player coalition = 0
      · simp [hzero]
      · have hpositive : 0 < quittingOpponentCoalitionMass root player coalition :=
          lt_of_le_of_ne (quittingOpponentCoalitionMass_nonneg root player coalition)
            (Ne.symm hzero)
        have hsubset := quittingOpponentCoalition_subset_positiveHazardSupport_of_mass_pos
          root player coalition hpositive
        simp only [quittingStageCoalitionPayoff, Finset.insert_nonempty, dite_true]
        rw [hconstant ⟨insert player coalition, Finset.insert_nonempty player coalition⟩
          (Finset.insert_subset_insert player hsubset) (Finset.mem_insert_self _ _)]
    _ = _ := by
      rw [← Finset.sum_mul, quittingOpponentCoalitionMass_sum_powerset, one_mul]

/-- A nontrap actual support supplies an active binding coordinate at every
exact root. The annotation and singleton coordinates may be signed. -/
theorem exactRootSuccessor_active_eq_singleton_of_support_not_premiumTrap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hactive : (quittingPositiveHazardSupport root).Nonempty)
    (hnot : ¬IsQuittingPremiumTrap reward (quittingPositiveHazardSupport root)) :
    ∃ player, 0 < (root player true).toReal ∧
      quittingRootSuccessorPayoff reward tail root player =
        reward (quittingSingletonTerminal player) player := by
  obtain ⟨player, hplayer, hflat⟩ :=
    exists_flat_participant_of_not_quittingPremiumTrap reward hnonnegative
      (quittingPositiveHazardSupport root) hactive hnot
  have hpositive : 0 < (root player true).toReal := by
    exact (Finset.mem_filter.mp hplayer).2
  refine ⟨player, hpositive, ?_⟩
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash
  have hquitNe : root player true ≠ 0 := by
    intro hzero
    rw [hzero] at hpositive
    norm_num at hpositive
  rw [quittingRootSuccessorPayoff_eq_quitPayoff_of_isZeroEndpointNash
    hendpoint player hquitNe]
  apply quittingRootQuitPayoff_eq_singleton_of_support_participantReward
  intro terminal hsubset hmember
  apply hflat terminal
  · simpa [Finset.insert_eq_of_mem hplayer] using hsubset
  · exact hmember

/-- The sole exceptional support for a pair core is the pair itself. -/
theorem exactRootSuccessor_active_eq_singleton_of_support_ne_pair_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (first second : ι) (hcore : quittingPremiumCore reward = {first, second})
    (tail : Payoff ι) (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hactive : (quittingPositiveHazardSupport root).Nonempty)
    (hne : quittingPositiveHazardSupport root ≠ quittingPremiumCore reward) :
    ∃ player, 0 < (root player true).toReal ∧
      quittingRootSuccessorPayoff reward tail root player =
        reward (quittingSingletonTerminal player) player := by
  apply exactRootSuccessor_active_eq_singleton_of_support_not_premiumTrap
    reward hnonnegative tail root hnash hactive
  exact MathUE.not_isFiniteCoalitionPremiumTrap_of_pair_core_ne
    (HasPositiveOwnQuittingPremium reward)
    (not_hasPositiveOwnQuittingPremium_singleton reward) first second hcore _ hne

end GameTheory
