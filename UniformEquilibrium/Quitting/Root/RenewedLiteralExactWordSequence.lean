import MathUE.RenewedChargedPathPotentialRecharge
import UniformEquilibrium.Quitting.Bellman.Finite.LiteralExactWordCapacityRecharge
import UniformEquilibrium.Quitting.Root.RenewedActualProfileDebtRecharge

/-! # Actual renewed literal words as coherent full-box path sequences

The input consists of supplied actual cap-response phases and exact literal
prefix words. Source decorations are the canonical all-Continue root, reused
literally after each horizontal update. No infinite phase producer is asserted.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Actual cap-replacement phases equipped with exact literal predecessor
words and one common positive absorption expenditure. -/
structure QuittingRenewedLiteralExactWordSequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    extends QuittingRenewedActualProfileSequence reward where
  /-- Exact roots in outermost-first prefix order above the actual phase source. -/
  roots : ℕ → List (ι → PMF Bool)
  /-- Every supplied word is an exact literal predecessor stack. -/
  roots_exact : ∀ phase,
    IsQuittingLiteralExactRootStack reward (roots phase) (source phase)
  /-- The stored actual endpoint is exactly the word profile. -/
  endpoint_eq_stack : ∀ phase,
    endpoint phase = quittingLiteralRootStackProfile reward (roots phase) (source phase)
  /-- Common lower bound for the actual root-absorption sums. -/
  minimumAbsorption : ℝ
  /-- The common absorption lower bound is positive. -/
  minimumAbsorption_pos : 0 < minimumAbsorption
  /-- Every exact word pays the common absorption lower bound. -/
  minimumAbsorption_le : ∀ phase,
    minimumAbsorption ≤ ((roots phase).map quittingRootAbsorptionMass).sum

namespace QuittingRenewedLiteralExactWordSequence

/-- Positive absorption expenditure forces every supplied exact word to be
nonempty; this is derived rather than stored as source data. -/
theorem roots_ne_nil
    (sequence : QuittingRenewedLiteralExactWordSequence reward) (phase : ℕ) :
    sequence.roots phase ≠ [] := by
  intro hempty
  have hlower := sequence.minimumAbsorption_le phase
  rw [hempty] at hlower
  simp only [List.map_nil, List.sum_nil] at hlower
  linarith [sequence.minimumAbsorption_pos]

/-- Canonical full-box state of an actual renewed source, always carrying the
same all-Continue decoration. -/
def boxSource (sequence : QuittingRenewedLiteralExactWordSequence reward)
    (phase : ℕ) : QuittingPunishmentFloorBoxState reward :=
  quittingActualProfileBoxState (sequence.source phase) quittingAllContinueSimplexRoot

/-- Canonical full-box endpoint obtained by decoding the phase's exact word. -/
def boxEndpoint (sequence : QuittingRenewedLiteralExactWordSequence reward)
    (phase : ℕ) : QuittingPunishmentFloorBoxState reward :=
  quittingLiteralExactWordEndpointState (sequence.roots phase)
    (sequence.source phase) quittingAllContinueSimplexRoot

/-- The boxed endpoint payoff is the actual stored endpoint payoff. -/
theorem boxEndpoint_payoff
    (sequence : QuittingRenewedLiteralExactWordSequence reward) (phase : ℕ) :
    (sequence.boxEndpoint phase).1.1 =
      fun who ↦ quittingTerminalPayoff reward (sequence.endpoint phase) who := by
  rw [boxEndpoint, quittingLiteralExactWordEndpointState_payoff,
    sequence.endpoint_eq_stack]

/-- The decoded boxed endpoint is the stored actual endpoint equipped with
the word's canonical endpoint decoration. -/
theorem boxEndpoint_eq_actualEndpoint
    (sequence : QuittingRenewedLiteralExactWordSequence reward) (phase : ℕ) :
    sequence.boxEndpoint phase = quittingActualProfileBoxState
      (sequence.endpoint phase)
      (quittingLiteralExactWordEndpointDecoration (sequence.roots phase)
        quittingAllContinueSimplexRoot) := by
  unfold boxEndpoint quittingLiteralExactWordEndpointState
  rw [sequence.endpoint_eq_stack]

/-- Decode all supplied exact words into a renewed full-box path sequence.
The horizontal target is definitionally the next all-Continue-decorated
source, so its decoration is literally reused. -/
def toRenewedPathSequence
    (sequence : QuittingRenewedLiteralExactWordSequence reward) :
    (quittingPunishmentFloorBoxChargedRelation reward).RenewedPathSequence where
  source := sequence.boxSource
  endpoint := sequence.boxEndpoint
  horizontalTarget := fun phase ↦ sequence.boxSource (phase + 1)
  verticalPath := fun phase ↦ quittingLiteralExactWordBoxPath
    (sequence.roots phase) (sequence.source phase) quittingAllContinueSimplexRoot
    (sequence.roots_exact phase)
  horizontalTarget_eq_nextSource := fun _ ↦ rfl
  minimumCharge := sequence.minimumAbsorption
  minimumCharge_pos := sequence.minimumAbsorption_pos
  minimumCharge_le_verticalCharge := fun phase ↦ by
    change sequence.minimumAbsorption ≤
      (quittingLiteralExactWordBoxPath (sequence.roots phase) (sequence.source phase)
        quittingAllContinueSimplexRoot (sequence.roots_exact phase)).chargeSum
    rw [quittingLiteralExactWordBoxPath_chargeSum]
    exact sequence.minimumAbsorption_le phase

@[simp] theorem toRenewedPathSequence_source
    (sequence : QuittingRenewedLiteralExactWordSequence reward) (phase : ℕ) :
    sequence.toRenewedPathSequence.source phase = sequence.boxSource phase := rfl

@[simp] theorem toRenewedPathSequence_horizontalTarget
    (sequence : QuittingRenewedLiteralExactWordSequence reward) (phase : ℕ) :
    sequence.toRenewedPathSequence.horizontalTarget phase =
      sequence.boxSource (phase + 1) := rfl

/-- The horizontal target is also literally the cap-updated actual child with
the same all-Continue source decoration. -/
theorem toRenewedPathSequence_horizontalTarget_eq_child
    (sequence : QuittingRenewedLiteralExactWordSequence reward) (phase : ℕ) :
    sequence.toRenewedPathSequence.horizontalTarget phase =
      quittingActualProfileBoxState (sequence.child phase)
        quittingAllContinueSimplexRoot := by
  rw [toRenewedPathSequence_horizontalTarget, boxSource]
  congr 1
  exact (sequence.child_eq_next_source phase).symm

@[simp] theorem toRenewedPathSequence_verticalCharge
    (sequence : QuittingRenewedLiteralExactWordSequence reward) (phase : ℕ) :
    (sequence.toRenewedPathSequence.verticalPath phase).chargeSum =
      ((sequence.roots phase).map quittingRootAbsorptionMass).sum := by
  exact quittingLiteralExactWordBoxPath_chargeSum _ _ _ _

/-- All actual phase absorption expenditures enter the capacity ledger with exact boundaries. -/
theorem sum_absorption_add_capacityBoundary_le_sum_capacityRecharge
    (sequence : QuittingRenewedLiteralExactWordSequence reward)
    (hbudget : (quittingPunishmentFloorBoxChargedRelation reward).HasFiniteBudget)
    (horizon : ℕ) :
    (∑ phase ∈ Finset.range horizon,
        ((sequence.roots phase).map quittingRootAbsorptionMass).sum) +
      (quittingPunishmentFloorBoxChargedRelation reward).value (sequence.boxSource horizon) -
      (quittingPunishmentFloorBoxChargedRelation reward).value (sequence.boxSource 0) ≤
      ∑ phase ∈ Finset.range horizon,
        sequence.toRenewedPathSequence.potentialRecharge
          (quittingPunishmentFloorBoxChargedRelation reward).value phase := by
  exact sum_literalExactWord_absorption_add_capacityBoundary_le_sum_recharge
    sequence.source sequence.roots (fun _ ↦ quittingAllContinueSimplexRoot)
    sequence.roots_exact hbudget horizon

/-- Dropping terminal capacity costs only the initial state's capacity, not the global budget. -/
theorem sum_absorption_sub_initialCapacity_le_sum_capacityRecharge
    (sequence : QuittingRenewedLiteralExactWordSequence reward)
    (hbudget : (quittingPunishmentFloorBoxChargedRelation reward).HasFiniteBudget)
    (horizon : ℕ) :
    (∑ phase ∈ Finset.range horizon,
        ((sequence.roots phase).map quittingRootAbsorptionMass).sum) -
      (quittingPunishmentFloorBoxChargedRelation reward).value (sequence.boxSource 0) ≤
      ∑ phase ∈ Finset.range horizon,
        sequence.toRenewedPathSequence.potentialRecharge
          (quittingPunishmentFloorBoxChargedRelation reward).value phase := by
  have hledger := sequence.sum_absorption_add_capacityBoundary_le_sum_capacityRecharge
    hbudget horizon
  have hterminal := (quittingPunishmentFloorBoxChargedRelation reward).value_nonneg hbudget
    (sequence.boxSource horizon)
  linarith

end QuittingRenewedLiteralExactWordSequence

end GameTheory
