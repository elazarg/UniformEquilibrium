import UniformEquilibrium.Quitting.Classification.NonnegativeProductLowExactRootBoundary
import UniformEquilibrium.Quitting.Root.FaceGeometry
import UniformEquilibrium.Quitting.Root.PairedProductRoot

/-! # Exact-root return for two-player premium cores with strict leave preference

Outside the designated pair, every participant reward is its own singleton.
Positive outside hazards are handled first. Only the remaining case reduces
to the two-coordinate root formulas. Only the designated leaving player's
annotation needs its singleton floor.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every absorbing exact root returns to the singleton lower boundary under
the raw two-core participant conditions and strict leave preference. Only the
first annotation coordinate needs its floor; all others may be below theirs. -/
theorem exactRootSuccessor_mem_singletonLowerBoundary_of_twoPlayerPremiumCore_strictLeave
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (first second : ι) (hne : first ≠ second)
    (houtside : ∀ player, player ≠ first → player ≠ second →
      ∀ terminal, player ∈ terminal.val →
        reward terminal player = reward (quittingSingletonTerminal player) player)
    (hleave : reward ⟨{first, second}, by simp⟩ first <
      reward (quittingSingletonTerminal second) first)
    (tail : Payoff ι)
    (hfloor : reward (quittingSingletonTerminal first) first ≤ tail first)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    (∀ player, reward (quittingSingletonTerminal player) player ≤
      quittingRootSuccessorPayoff reward tail root player) ∧
    ∃ player, 0 < (root player true).toReal ∧
      quittingRootSuccessorPayoff reward tail root player =
        reward (quittingSingletonTerminal player) player := by
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash
  have hsupported : ∀ player, 0 < (root player true).toReal →
      quittingRootSuccessorPayoff reward tail root player =
        quittingRootQuitPayoff reward tail root player := by
    intro player hactive
    apply quittingRootSuccessorPayoff_eq_quitPayoff_of_isZeroEndpointNash
      hendpoint player
    intro hzero
    rw [hzero] at hactive
    norm_num at hactive
  refine ⟨fun player =>
    (quittingSingletonReward_le_rootQuitPayoff_of_nonnegativePremium
      hnonnegative tail root player).trans
        (quittingRootQuitPayoff_le_successor_of_isZeroNash
          reward tail root player hnash), ?_⟩
  by_cases hactiveOutside : ∃ player,
      player ≠ first ∧ player ≠ second ∧ 0 < (root player true).toReal
  · obtain ⟨player, hfirst, hsecond, hactive⟩ := hactiveOutside
    refine ⟨player, hactive, ?_⟩
    rw [hsupported player hactive]
    exact quittingRootQuitPayoff_eq_singleton_of_constant_participantReward
      reward tail root player (houtside player hfirst hsecond)
  · have hcore : ∀ player, 0 < (root player true).toReal →
        player = first ∨ player = second := by
      intro player hactive
      by_cases hfirst : player = first
      · exact Or.inl hfirst
      · by_cases hsecond : player = second
        · exact Or.inr hsecond
        · exact (hactiveOutside ⟨player, hfirst, hsecond, hactive⟩).elim
    have hpureOutside : ∀ player, player ≠ first → player ≠ second →
        root player = PMF.pure false := by
      intro player hfirst hsecond
      apply Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      apply le_antisymm _ ENNReal.toReal_nonneg
      apply le_of_not_gt
      intro hactive
      exact hactiveOutside ⟨player, hfirst, hsecond, hactive⟩
    have hroot : root = PairedCycle.root first second (root first) (root second) := by
      funext player
      by_cases hfirst : player = first
      · subst player
        simp [PairedCycle.root, hne]
      · by_cases hsecond : player = second
        · subst player
          simp [PairedCycle.root]
        · simp only [PairedCycle.root, Function.update_of_ne hsecond,
            Function.update_of_ne hfirst]
          exact hpureOutside player hfirst hsecond
    have hquit := PairedCycle.rootQuit_first reward tail hne (root first) (root second)
    have hcontinue :=
      PairedCycle.rootContinue_first reward tail hne (root first) (root second)
    rw [← hroot] at hquit hcontinue
    have hgap : quittingRootEndpointDifference reward tail root first =
        (1 - (root second true).toReal) *
            (reward (quittingSingletonTerminal first) first - tail first) +
          (root second true).toReal *
            (reward ⟨{first, second}, by simp⟩ first -
              reward (quittingSingletonTerminal second) first) := by
      rw [quittingRootEndpointDifference, hquit, hcontinue]
      unfold Math.PairedAffine.activeValue
      ring
    have hnotBoth : ¬ (0 < (root first true).toReal ∧
        0 < (root second true).toReal) := by
      rintro ⟨hfirst, hsecond⟩
      have hgapNonneg : 0 ≤ quittingRootEndpointDifference reward tail root first :=
        nonneg_of_mul_nonneg_left
          (by simpa [mul_comm] using (hendpoint first).2) hfirst
      have hcontinueNonneg : 0 ≤ 1 - (root second true).toReal := by
        rw [← pmfBool_false_toReal]
        exact ENNReal.toReal_nonneg
      have hfirstTerm := mul_nonpos_of_nonneg_of_nonpos hcontinueNonneg
        (sub_nonpos.mpr hfloor)
      have hsecondTerm := mul_neg_of_pos_of_neg hsecond (sub_neg.mpr hleave)
      rw [hgap] at hgapNonneg
      linarith
    obtain ⟨player, hactive⟩ :=
      (quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos root).mp habsorption
    have hpure : ∀ other, other ≠ player → root other = PMF.pure false := by
      intro other hother
      apply Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      apply le_antisymm _ ENNReal.toReal_nonneg
      apply le_of_not_gt
      intro hotherActive
      have hotherCore := hcore other hotherActive
      rcases hcore player hactive with rfl | rfl
      · have heq : other = second := hotherCore.resolve_left hother
        exact hnotBoth ⟨hactive, heq ▸ hotherActive⟩
      · have heq : other = first := hotherCore.resolve_right hother
        exact hnotBoth ⟨heq ▸ hotherActive, hactive⟩
    refine ⟨player, hactive, ?_⟩
    rw [hsupported player hactive]
    exact (quittingRoot_endpoints_eq_singleton_tail_of_opponents_pureContinue
      reward tail root player hpure).1

end GameTheory
