import UniformEquilibrium.Quitting.Root.FiniteRootWordSequenceBridge
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart

/-! # Prefix payoff bounds with a bounded alternative Never reward -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι]

/-- Assigning a bounded value to the all-Never outcome keeps the actual
terminal expectation inside the same reward interval. -/
theorem abs_quittingTerminalPayoff_add_neverMass_mul_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) {bound correction : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hcorrection : |correction| ≤ bound) :
    |quittingTerminalPayoff reward profile who +
      correction * quittingLiveMassLimit reward profile| ≤ bound := by
  have hlive := quittingLiveMassLimit_nonneg reward profile
  have hpay := abs_quittingTerminalPayoff_le_absorbedMass reward profile who hreward
  have htri := abs_add_le (quittingTerminalPayoff reward profile who)
    (correction * quittingLiveMassLimit reward profile)
  rw [abs_mul, abs_of_nonneg hlive] at htri
  have hscaled := mul_le_mul_of_nonneg_right hcorrection hlive
  nlinarith

/-- Replacing an arbitrary root-sequence suffix by an actual behavioral tail
changes its payoff, even with a bounded alternative Never reward, by at most
twice the reward bound times the original joint reach. -/
theorem abs_quittingLiteralRootStackPayoff_sub_corrected_rootSequence_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ)
    (tail : (quittingGame reward).BehaviorProfile) (who : ι) {bound correction : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hcorrection : |correction| ≤ bound) :
    |quittingTerminalPayoff reward (quittingLiteralRootStackProfile reward
        (List.ofFn fun time : Fin cutoff ↦ roots time.val) tail) who -
      (quittingRootSequenceTerminalValue reward roots who 0 +
        correction * quittingJointSurvivalLimit roots 0)| ≤
      2 * bound * quittingJointSurvivalWeight roots 0 cutoff := by
  let oldTail := quittingRootSequenceProfile reward roots cutoff
  let headWord := List.ofFn fun time : Fin cutoff ↦ roots time.val
  have hsource : quittingRootSequenceProfile reward roots 0 =
      quittingLiteralRootStackProfile reward headWord oldTail := by
    simpa only [Nat.zero_add] using
      quittingRootSequenceProfile_eq_literalRootStack reward roots 0 cutoff
  have hlimit : quittingJointSurvivalLimit roots 0 =
      quittingJointSurvivalWeight roots 0 cutoff * quittingLiveMassLimit reward oldTail := by
    rw [quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit]
    simpa only [Nat.zero_add] using quittingJointSurvivalLimit_eq_prefix_mul_tail roots 0 cutoff
  have hweight : quittingLiteralRootStackJointSurvival headWord =
      quittingJointSurvivalWeight roots 0 cutoff := by
    simpa only [Nat.zero_add] using quittingLiteralRootStackJointSurvival_ofFn roots 0 cutoff
  have hdiff : quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward headWord tail) who -
      quittingRootSequenceTerminalValue reward roots who 0 =
      quittingJointSurvivalWeight roots 0 cutoff *
        (quittingTerminalPayoff reward tail who - quittingTerminalPayoff reward oldTail who) := by
    unfold quittingRootSequenceTerminalValue
    rw [hsource, quittingTerminalPayoff_literalRootStack_eq_wordPayoff,
      quittingTerminalPayoff_literalRootStack_eq_wordPayoff,
      quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul, hweight]
  have htail := abs_quittingTerminalPayoff_le reward tail who hreward
  have hold := abs_quittingTerminalPayoff_add_neverMass_mul_le
    reward oldTail who hreward hcorrection
  have hbound : |quittingTerminalPayoff reward tail who -
      (quittingTerminalPayoff reward oldTail who +
        correction * quittingLiveMassLimit reward oldTail)| ≤ 2 * bound :=
    (abs_sub _ _).trans (by linarith)
  have heq : quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward headWord tail) who -
      (quittingRootSequenceTerminalValue reward roots who 0 +
        correction * quittingJointSurvivalLimit roots 0) =
      quittingJointSurvivalWeight roots 0 cutoff *
        (quittingTerminalPayoff reward tail who -
          (quittingTerminalPayoff reward oldTail who +
            correction * quittingLiveMassLimit reward oldTail)) := by
    rw [hlimit]
    linarith [hdiff]
  change |quittingTerminalPayoff reward
    (quittingLiteralRootStackProfile reward headWord tail) who - _| ≤ _
  rw [heq, abs_mul, abs_of_nonneg (quittingJointSurvivalWeight_nonneg roots 0 cutoff)]
  nlinarith [mul_le_mul_of_nonneg_left hbound
    (quittingJointSurvivalWeight_nonneg roots 0 cutoff)]

end GameTheory
