import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-! # Same-root stability under reward and continuation perturbations -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Reward and continuation are alternative outcomes, not additive error sources. -/
theorem abs_quittingRootExpectedPayoff_sub_of_reward_and_tail_close
    (first second : {S : Finset ι // S.Nonempty} → Payoff ι)
    (firstTail secondTail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {delta : ℝ}
    (hreward : ∀ terminal, |first terminal who - second terminal who| ≤ delta)
    (htail : |firstTail who - secondTail who| ≤ delta) :
    |quittingRootExpectedPayoff first firstTail root who -
      quittingRootExpectedPayoff second secondTail root who| ≤ delta := by
  unfold quittingRootExpectedPayoff
  rw [← expect_sub]
  apply abs_expect_le_of_abs_le
  intro action
  by_cases hquit : (quittingQuitters action).Nonempty
  · simpa [quittingRootPayoff, hquit] using hreward ⟨_, hquit⟩
  · simpa [quittingRootPayoff, hquit] using htail

theorem abs_quittingRootEndpointDifference_sub_of_reward_close
    (first second : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hclose : ∀ terminal, |first terminal who - second terminal who| ≤ delta) :
    |quittingRootEndpointDifference first tail root who -
      quittingRootEndpointDifference second tail root who| ≤ 2 * delta := by
  have hquit := abs_quittingRootExpectedPayoff_sub_of_reward_and_tail_close
    first second tail tail (Function.update root who (PMF.pure true)) who hclose
    (by simpa using hdelta)
  have hcontinue := abs_quittingRootExpectedPayoff_sub_of_reward_and_tail_close
    first second tail tail (Function.update root who (PMF.pure false)) who hclose
    (by simpa using hdelta)
  unfold quittingRootEndpointDifference quittingRootQuitPayoff quittingRootContinuePayoff
  rw [abs_le] at hquit hcontinue ⊢
  constructor <;> linarith

end GameTheory
