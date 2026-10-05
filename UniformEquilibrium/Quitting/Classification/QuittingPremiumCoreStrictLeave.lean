import UniformEquilibrium.Quitting.Classification.QuittingPremiumCoreExactRoot
import UniformEquilibrium.Quitting.Root.PairedProductRoot

/-! # Protected first-floor return for a greatest pair premium core -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Strict preference to leave excludes the exceptional pair support. Only
the first source floor is protected; outsiders may have positive premiums
on coalitions involving other outsiders. -/
theorem exactRootSuccessor_mem_singletonLowerBoundary_of_pairPremiumCore_strictLeave
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (first second : ι) (hne : first ≠ second)
    (hcore : quittingPremiumCore reward = {first, second})
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
  refine ⟨fun player =>
    (quittingSingletonReward_le_rootQuitPayoff_of_nonnegativePremium
      hnonnegative tail root player).trans
      (quittingRootQuitPayoff_le_successor_of_isZeroNash reward tail root player hnash), ?_⟩
  have hactive : (quittingPositiveHazardSupport root).Nonempty := by
    obtain ⟨player, hplayer⟩ :=
      (quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos root).mp habsorption
    exact ⟨player, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hplayer⟩⟩
  apply exactRootSuccessor_active_eq_singleton_of_support_ne_pair_core
    reward hnonnegative first second hcore tail root hnash hactive
  intro heq
  have hsupport : quittingPositiveHazardSupport root = {first, second} := heq.trans hcore
  have hfirst : 0 < (root first true).toReal := by
    have : first ∈ quittingPositiveHazardSupport root := by rw [hsupport]; simp
    exact (Finset.mem_filter.mp this).2
  have hsecond : 0 < (root second true).toReal := by
    have : second ∈ quittingPositiveHazardSupport root := by rw [hsupport]; simp
    exact (Finset.mem_filter.mp this).2
  have hroot : root = PairedCycle.root first second (root first) (root second) := by
    funext player
    by_cases hfirstEq : player = first
    · subst player
      simp [PairedCycle.root, hne]
    · by_cases hsecondEq : player = second
      · subst player
        simp [PairedCycle.root]
      · have hpure := quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport root
          (who := player) (by simp [hsupport, hfirstEq, hsecondEq])
        simp only [PairedCycle.root, Function.update_of_ne hsecondEq,
          Function.update_of_ne hfirstEq]
        exact hpure
  have hquit := PairedCycle.rootQuit_first reward tail hne (root first) (root second)
  have hcontinue := PairedCycle.rootContinue_first reward tail hne (root first) (root second)
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
  have hgapNonneg : 0 ≤ quittingRootEndpointDifference reward tail root first :=
    nonneg_of_mul_nonneg_left
      (by simpa [mul_comm] using (hendpoint first).2) hfirst
  have hcontinueNonneg : 0 ≤ 1 - (root second true).toReal := by
    rw [← pmfBool_false_toReal]
    exact ENNReal.toReal_nonneg
  have hfirstTerm := mul_nonpos_of_nonneg_of_nonpos hcontinueNonneg (sub_nonpos.mpr hfloor)
  have hsecondTerm := mul_neg_of_pos_of_neg hsecond (sub_neg.mpr hleave)
  rw [hgap] at hgapNonneg
  linarith

end GameTheory
