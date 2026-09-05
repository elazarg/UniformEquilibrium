import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineReplyCap

/-! # Early absorption in actual finite timing menus -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every requested finite accuracy, suffix length, reach threshold and lower
deadline admits independent finite timing laws satisfying only the displayed
menu Nash comparisons and early joint absorption. No full deviation cap is
assumed of the source profile. -/
def HasQuittingFiniteMenuEarlyAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ error : ℝ, 0 < error → ∀ horizon : ℕ, 1 ≤ horizon →
    ∀ reach : ℝ, 0 < reach → ∀ lowerDeadline : ℕ,
      ∃ deadline : ℕ, max horizon lowerDeadline ≤ deadline ∧
        ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
          IsQuittingFiniteDeadlineNash reward deadline error mixed ∧
          quittingJointSurvivalWeight
            (quittingProfileLiveRoot reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed))
            0 (deadline - horizon) < reach

end GameTheory
