import UniformEquilibrium.Quitting.Classification.QuittingPremiumCoreStrictLeave
import UniformEquilibrium.Quitting.Projective.SingletonLowerBoundaryReturnSmoothDrift

/-! # Greatest pair-core strict-leave exclusion with boundary-only regularity -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem not_isQuittingFullExactRootPotential_of_pairPremiumCore_strictLeave
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (first second : ι) (hne : first ≠ second)
    (hcore : quittingPremiumCore reward = {first, second})
    (hleave : reward ⟨{first, second}, by simp⟩ first <
      reward (quittingSingletonTerminal second) first)
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound) (potential : Payoff ι → ℝ)
    (hdiff : ∀ point ∈ Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound),
        DifferentiableAt ℝ potential point) :
    ¬IsQuittingFullExactRootPotential reward bound potential := by
  apply not_isQuittingFullExactRootPotential_of_singletonLowerBoundaryReturn
    first hreward hbound
  · intro tail _hbox hfloor root hnash hpositive
    obtain ⟨hlower, player, _hactive, hplayer⟩ :=
      exactRootSuccessor_mem_singletonLowerBoundary_of_pairPremiumCore_strictLeave
        reward hnonnegative first second hne hcore hleave tail hfloor root hnash hpositive
    exact ⟨hlower, player, hplayer⟩
  · exact hdiff

end GameTheory
