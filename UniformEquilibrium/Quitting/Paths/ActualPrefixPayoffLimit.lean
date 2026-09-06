import UniformEquilibrium.Quitting.Root.BoundedEndpoint
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-! # Payoff convergence of summable literal prefixes -/

noncomputable section
namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Summable marginal hazards make the prescribed terminal payoffs of an
actual literal prefix recursion converge coordinatewise. -/
theorem exists_tendsto_terminalPayoff_of_nested_of_summable_marginalHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnested : ∀ time, profiles (time + 1) =
      quittingRootThenContinuationProfile reward (roots time) (profiles time))
    (hhazard : Summable (fun time =>
      ∑ player, (roots time player true).toReal)) :
    ∃ limit : Payoff ι, ∀ player,
      Tendsto (fun time => quittingTerminalPayoff reward (profiles time) player)
        atTop (nhds (limit player)) := by
  let value : ℕ → Payoff ι := fun time player =>
    quittingTerminalPayoff reward (profiles time) player
  have hvalueNext : ∀ time, value (time + 1) =
      quittingRootSuccessorPayoff reward (value time) (roots time) := by
    intro time
    funext player
    simp only [value, hnested time,
      quittingTerminalPayoff_rootThenContinuation_eq]
    rfl
  have habsorption : Summable (fun time =>
      quittingRootAbsorptionMass (roots time)) := by
    apply Summable.of_nonneg_of_le
      (fun time => quittingRootAbsorptionMass_nonneg (roots time))
      (fun time => quittingRootAbsorptionMass_le_sum_quitProbability
        (roots time))
      hhazard
  have hcoordinate : ∀ player, ∃ coordinateLimit : ℝ,
      Tendsto (fun time => value time player) atTop (nhds coordinateLimit) := by
    intro player
    have hincrements : Summable (fun time =>
        |value (time + 1) player - value time player|) := by
      apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
        (fun time => ?_) (habsorption.mul_left (2 * M))
      rw [hvalueNext time]
      exact abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
        reward (value time) (roots time) player M hreward
          (abs_quittingTerminalPayoff_le reward (profiles time) player hreward)
    have hdist : Summable (fun time =>
        dist (value time player) (value (time + 1) player)) := by
      simpa [Real.dist_eq, abs_sub_comm] using hincrements
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  choose limit hlimit using hcoordinate
  exact ⟨limit, fun player => by simpa [value] using hlimit player⟩

end GameTheory
