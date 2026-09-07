import UniformEquilibrium.Diagnostics.Quitting.CompleteCapSingletonSlabCollar
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawDebtConvexity

/-! # Actual complete-cap installation segments and their uniform collar -/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Install a private mixture of one player's complete prescribed stopping
law and a supplied response law. All opponents remain literal. -/
def quittingCapResponseSegment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    (response : (quittingGame reward).BehaviorStrategy owner)
    (parameter : Set.Icc (0 : ℝ) 1) : (quittingGame reward).BehaviorProfile :=
  Function.update profile owner
    (quittingStoppingLawMixtureBehaviorStrategy reward owner (profile owner) response
      parameter.val parameter.property.1 parameter.property.2)

/-- The complete cap of the moved coordinate is constant along the actual
segment, even when the supplied response does not attain that cap. -/
theorem capResponseSegment_ownerCap_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    (response : (quittingGame reward).BehaviorStrategy owner)
    (parameter : Set.Icc (0 : ℝ) 1) :
    quittingContinuationBestResponseValue reward
        (quittingCapResponseSegment reward profile owner response parameter) owner =
      quittingContinuationBestResponseValue reward profile owner := by
  exact quittingContinuationBestResponseValue_update_self _ _ _ _

/-- Installing an attained complete cap scales the owner's debt by the
uninstalled fraction, including both closed-segment endpoints. -/
theorem capResponseSegment_ownerDebt_eq_oneSub_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    (response : (quittingGame reward).BehaviorStrategy owner)
    (hattains : quittingTerminalPayoff reward (Function.update profile owner response) owner =
      quittingContinuationBestResponseValue reward profile owner)
    (parameter : Set.Icc (0 : ℝ) 1) :
    quittingTerminalDeviationDebt reward
        (quittingCapResponseSegment reward profile owner response parameter) owner =
      (1 - parameter.val) * quittingTerminalDeviationDebt reward profile owner := by
  have hpayoff := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile owner owner (profile owner) response
      parameter.val parameter.property.1 parameter.property.2
  rw [Function.update_eq_self, hattains] at hpayoff
  unfold quittingTerminalDeviationDebt
  rw [capResponseSegment_ownerCap_eq]
  change quittingContinuationBestResponseValue reward profile owner -
    quittingTerminalPayoff reward
      (Function.update profile owner
        (quittingStoppingLawMixtureBehaviorStrategy reward owner (profile owner) response
          parameter.val parameter.property.1 parameter.property.2)) owner = _
  rw [hpayoff]
  ring

/-- A cap-installation family has one uniform off-minimum collar over the
entire closed segment. Cap attainment is unnecessary for this collar alone:
the named cap remains fixed under every unilateral stopping-law mixture. -/
theorem eventually_capResponseSegment_debtSum_ge_min_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile) (owner : ι)
    (responses : ℕ → (quittingGame reward).BehaviorStrategy owner)
    {minimumDebt : ℝ} (hpositive : 0 < minimumDebt)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      minimumDebt ≤ quittingTerminalSemanticDebtSum candidate)
    (hlimit : Tendsto (fun index =>
      quittingContinuationBestResponseValue reward (profiles index) owner) atTop
        (nhds (reward (quittingSingletonTerminal owner) owner))) :
    ∃ collar : ℝ, 0 < collar ∧ ∀ᶠ index in atTop,
      ∀ parameter : Set.Icc (0 : ℝ) 1,
        minimumDebt + collar ≤ quittingTerminalDebtSum reward
          (quittingCapResponseSegment reward (profiles index) owner
            (responses index) parameter) := by
  exact exists_uniform_offMinimum_collar_of_completeCap_tendsto_singleton
    reward
    (fun index parameter => quittingCapResponseSegment reward (profiles index) owner
      (responses index) parameter) owner
    (fun index => quittingContinuationBestResponseValue reward (profiles index) owner)
    hpositive hminimum
    (fun index parameter => capResponseSegment_ownerCap_eq
      reward (profiles index) owner (responses index) parameter) hlimit

end GameTheory
