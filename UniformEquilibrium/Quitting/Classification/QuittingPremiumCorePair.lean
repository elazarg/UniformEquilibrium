import UniformEquilibrium.Quitting.Classification.QuittingPremiumCore

/-! # Literal pair premiums of a greatest pair core -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Each core member's only possible strict witness inside a pair is the pair
itself. Nonnegative-premium assumptions are unnecessary for this fact. -/
theorem quittingPremiumCore_pair_reward_gt_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι) (hcore : quittingPremiumCore reward = {first, second}) :
    reward (quittingSingletonTerminal first) first <
        reward ⟨{first, second}, by simp⟩ first ∧
      reward (quittingSingletonTerminal second) second <
        reward ⟨{first, second}, by simp⟩ second := by
  have htrap : IsQuittingPremiumTrap reward {first, second} := by
    have hnonempty : (quittingPremiumCore reward).Nonempty := by rw [hcore]; simp
    have := MathUE.isFiniteCoalitionPremiumTrap_core
      (HasPositiveOwnQuittingPremium reward) hnonempty
    change IsQuittingPremiumTrap reward (quittingPremiumCore reward) at this
    rw [hcore] at this
    exact this
  have witness : ∀ left right : ι,
      IsQuittingPremiumTrap reward {left, right} →
        reward (quittingSingletonTerminal left) left <
          reward ⟨{left, right}, by simp⟩ left := by
    intro left right hpair
    obtain ⟨coalition, hsubset, hmember, hpositive⟩ := hpair.2 left (by simp)
    have hright : right ∈ coalition := by
      by_contra hnot
      have hsingle : coalition ⊆ {left} := by
        intro player hplayer
        have hpairMem := hsubset hplayer
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpairMem ⊢
        exact hpairMem.resolve_right (fun heq => hnot (heq ▸ hplayer))
      have heq : coalition = {left} :=
        Finset.Subset.antisymm hsingle (Finset.singleton_subset_iff.mpr hmember)
      exact not_hasPositiveOwnQuittingPremium_singleton reward left (heq ▸ hpositive)
    have heq : coalition = {left, right} := by
      apply Finset.Subset.antisymm hsubset
      intro player hplayer
      simp only [Finset.mem_insert, Finset.mem_singleton] at hplayer
      rcases hplayer with hleft | hrightEq
      · exact hleft.symm ▸ hmember
      · exact hrightEq.symm ▸ hright
    obtain ⟨hcoalition, hpositive⟩ := hpositive
    have hterminal : (⟨coalition, hcoalition⟩ : {S : Finset ι // S.Nonempty}) =
        ⟨{left, right}, by simp⟩ := Subtype.ext heq
    simpa [hterminal] using hpositive
  refine ⟨witness first second htrap, ?_⟩
  have hsecond := witness second first (by simpa [Finset.pair_comm] using htrap)
  simpa [Finset.pair_comm] using hsecond

end GameTheory
