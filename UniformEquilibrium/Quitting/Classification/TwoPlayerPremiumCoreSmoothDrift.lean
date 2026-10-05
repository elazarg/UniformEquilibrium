import UniformEquilibrium.Quitting.Classification.TwoPlayerPremiumCoreExactRootBoundary
import UniformEquilibrium.Quitting.Projective.SingletonLowerBoundaryReturnSmoothDrift

/-! # Smooth full-root potential exclusion for strict-leave premium cores

The actual-root return theorem requires only the first core annotation floor.
At a lower-boundary minimum, the existing face geometry supplies another binding
coordinate. Lowering it preserves that floor and gives a charged return.
Signed singleton rewards are permitted.
-/

noncomputable section

namespace GameTheory

open Set Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Strict-leave premium cores admit no full exact-root potential differentiable
at every point of the singleton lower boundary. All exact roots at all boxed
annotations are tested, without a strategy-realizability premise. -/
theorem not_isQuittingFullExactRootPotential_of_twoPlayerPremiumCore_strictLeave
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (first second : ι) (hne : first ≠ second)
    (houtside : ∀ player, player ≠ first → player ≠ second →
      ∀ terminal, player ∈ terminal.val →
        reward terminal player = reward (quittingSingletonTerminal player) player)
    (hleave : reward ⟨{first, second}, by simp⟩ first <
      reward (quittingSingletonTerminal second) first)
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound)
    (potential : Payoff ι → ℝ)
    (hdiff : ∀ point ∈ Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound),
        DifferentiableAt ℝ potential point) :
    ¬ IsQuittingFullExactRootPotential reward bound potential := by
  apply not_isQuittingFullExactRootPotential_of_singletonLowerBoundaryReturn
    first hreward hbound
  · intro tail _hbox hfloor root hnash hpositive
    obtain ⟨hlower, player, _hactive, hplayer⟩ :=
      exactRootSuccessor_mem_singletonLowerBoundary_of_twoPlayerPremiumCore_strictLeave
        hnonnegative first second hne houtside hleave tail hfloor root hnash hpositive
    exact ⟨hlower, player, hplayer⟩
  · exact hdiff

end GameTheory
