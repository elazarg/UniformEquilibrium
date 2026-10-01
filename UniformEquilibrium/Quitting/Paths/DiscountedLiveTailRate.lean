import MathUE.RealSeries.NormalizedGeometricComparison
import UniformEquilibrium.Quitting.Paths.DiscountedStoppingLawPayoff
import UniformEquilibrium.Quitting.Paths.LiveTail
import UniformEquilibrium.Quitting.Paths.OpponentLiveMass

/-!
# Actual two-sided discounted error controlled by live tails

These are the canonical normalized expected-stage payoffs. Under the actual
zero-live-stage convention, absorption at date t has weight d^(t+1), as proved
by DiscountedStoppingLawPayoff. Every complete behavioral replacement keeps
the SAME original opponent clock. Rewards may be signed and d=0 is retained.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι]

/-- The actual normalized discounted live clock of a behavioral profile. -/
def quittingDiscountedLiveTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (discount : ℝ) : ℝ :=
  (1 - discount) * ∑' time : ℕ, discount ^ time * quittingLiveMass reward profile time

theorem summable_quittingDiscountedLiveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1) :
    Summable (fun time : ℕ => discount ^ time * quittingLiveMass reward profile time) := by
  refine (summable_geometric_of_lt_one hdiscount hdiscountOne).of_norm_bounded ?_
  intro time
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hdiscount time),
    abs_of_nonneg (quittingLiveMass_nonneg reward profile time)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (quittingLiveMass_le_one reward profile time) (pow_nonneg hdiscount time)

/-- The existing actual absorption-tail comparison with its nonnegative limit dropped. -/
theorem abs_expectedStagePayoff_sub_terminal_le_liveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (time : ℕ) (bound : ℝ) (hreward : ∀ terminal, |reward terminal who| ≤ bound) :
    |(quittingGame reward).expectedStagePayoff profile none time who -
      quittingTerminalPayoff reward profile who| ≤
        bound * quittingLiveMass reward profile time := by
  have hbound : 0 ≤ bound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal who))
  have htail := abs_quittingTerminalPayoff_sub_expectedStagePayoff_le_liveTail
    reward profile time who bound hreward
  have hdrop :
      bound * (quittingLiveMass reward profile time - quittingLiveMassLimit reward profile) ≤
        bound * quittingLiveMass reward profile time := by
    nlinarith [quittingLiveMassLimit_nonneg reward profile]
  simpa only [abs_sub_comm] using htail.trans hdrop

/-- Prescribed discounted delivery depends on the profile's OWN actual live clock. -/
theorem abs_discountedPayoff_sub_terminal_le_liveTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (bound : ℝ) (hreward : ∀ terminal, |reward terminal who| ≤ bound) :
    |(quittingGame reward).discountedPayoff discount profile none who -
      quittingTerminalPayoff reward profile who| ≤
        bound * quittingDiscountedLiveTail reward profile discount := by
  simpa only [StochasticGame.discountedPayoff, quittingDiscountedLiveTail, mul_assoc] using
    Math.RealSeries.abs_normalized_geometric_sub_le_clock discount
      (quittingTerminalPayoff reward profile who) bound
      (fun time => (quittingGame reward).expectedStagePayoff profile none time who)
      (quittingLiveMass reward profile) hdiscount hdiscountOne
      (summable_quittingDiscountedLiveMass reward profile discount hdiscount hdiscountOne)
      (fun time => abs_expectedStagePayoff_sub_terminal_le_liveMass
        reward profile who time bound hreward)

variable [DecidableEq ι]

/-- Every complete reply has absolute discounted error controlled by the
SAME original opponent-only live clock, even when its own clock does not contract. -/
theorem abs_discountedPayoff_update_sub_terminal_le_opponentLiveTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (bound : ℝ) (hreward : ∀ terminal, |reward terminal who| ≤ bound) :
    |(quittingGame reward).discountedPayoff discount
        (Function.update profile who deviation) none who -
      quittingTerminalPayoff reward (Function.update profile who deviation) who| ≤
        bound * quittingDiscountedLiveTail reward
          (quittingOpponentOnlyProfile reward profile who) discount := by
  have hbound : 0 ≤ bound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal who))
  have herror (time : ℕ) :
      |(quittingGame reward).expectedStagePayoff
          (Function.update profile who deviation) none time who -
        quittingTerminalPayoff reward (Function.update profile who deviation) who| ≤
      bound * quittingLiveMass reward (quittingOpponentOnlyProfile reward profile who) time :=
    (abs_expectedStagePayoff_sub_terminal_le_liveMass reward
      (Function.update profile who deviation) who time bound hreward).trans
        (mul_le_mul_of_nonneg_left
          (quittingLiveMass_update_le_opponentOnly reward profile who deviation time) hbound)
  simpa only [StochasticGame.discountedPayoff, quittingDiscountedLiveTail, mul_assoc] using
    Math.RealSeries.abs_normalized_geometric_sub_le_clock discount
      (quittingTerminalPayoff reward (Function.update profile who deviation) who) bound
      (fun time => (quittingGame reward).expectedStagePayoff
        (Function.update profile who deviation) none time who)
      (quittingLiveMass reward (quittingOpponentOnlyProfile reward profile who))
      hdiscount hdiscountOne
      (summable_quittingDiscountedLiveMass reward
        (quittingOpponentOnlyProfile reward profile who) discount hdiscount hdiscountOne) herror

end GameTheory
