import MathUE.PathFamilyPotentialRecharge
import UniformEquilibrium.Quitting.Bellman.Finite.LiteralExactPrefixBoxPath

/-! # Actual-expenditure recharge for arbitrary literal exact words

Empty and zero-charge phases are allowed. Each horizontal target is literally
the next chosen source with that source's chosen decoration.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

open Math.ChargedPathBudget.ChargedRelation

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Arbitrary exact words obey the full-box ledger, including empty and zero-charge words. -/
theorem sum_literalExactWord_absorption_add_capacityBoundary_le_sum_recharge
    (source : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → List (ι → PMF Bool)) (decoration : ℕ → QuittingRootSimplex ι)
    (hexact : ∀ phase, IsQuittingLiteralExactRootStack reward (roots phase) (source phase))
    (hbudget : (quittingPunishmentFloorBoxChargedRelation reward).HasFiniteBudget)
    (horizon : ℕ) :
    (∑ phase ∈ Finset.range horizon, ((roots phase).map quittingRootAbsorptionMass).sum) +
      (quittingPunishmentFloorBoxChargedRelation reward).value
        (quittingActualProfileBoxState (source horizon) (decoration horizon)) -
      (quittingPunishmentFloorBoxChargedRelation reward).value
        (quittingActualProfileBoxState (source 0) (decoration 0)) ≤
      ∑ phase ∈ Finset.range horizon,
        ((quittingPunishmentFloorBoxChargedRelation reward).value
          (quittingActualProfileBoxState (source (phase + 1)) (decoration (phase + 1))) -
        (quittingPunishmentFloorBoxChargedRelation reward).value
          (quittingLiteralExactWordEndpointState
            (roots phase) (source phase) (decoration phase))) := by
  have hledger := sum_pathFamily_charge_add_boundary_le_sum_recharge
    (fun phase ↦ quittingActualProfileBoxState (source phase) (decoration phase))
    (fun phase ↦ quittingLiteralExactWordEndpointState
      (roots phase) (source phase) (decoration phase))
    (fun phase ↦ quittingLiteralExactWordBoxPath
      (roots phase) (source phase) (decoration phase) (hexact phase))
    (quittingPunishmentFloorBoxChargedRelation reward).value
    ((quittingPunishmentFloorBoxChargedRelation reward).value_isBoundedPotential
      hbudget).isPotential horizon
  simpa only [quittingLiteralExactWordBoxPath_chargeSum] using hledger

/-- Only the actual initial source capacity is lost after discarding the terminal boundary. -/
theorem sum_literalExactWord_absorption_sub_initialCapacity_le_sum_recharge
    (source : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → List (ι → PMF Bool)) (decoration : ℕ → QuittingRootSimplex ι)
    (hexact : ∀ phase, IsQuittingLiteralExactRootStack reward (roots phase) (source phase))
    (hbudget : (quittingPunishmentFloorBoxChargedRelation reward).HasFiniteBudget)
    (horizon : ℕ) :
    (∑ phase ∈ Finset.range horizon, ((roots phase).map quittingRootAbsorptionMass).sum) -
      (quittingPunishmentFloorBoxChargedRelation reward).value
        (quittingActualProfileBoxState (source 0) (decoration 0)) ≤
      ∑ phase ∈ Finset.range horizon,
        ((quittingPunishmentFloorBoxChargedRelation reward).value
          (quittingActualProfileBoxState (source (phase + 1)) (decoration (phase + 1))) -
        (quittingPunishmentFloorBoxChargedRelation reward).value
          (quittingLiteralExactWordEndpointState
            (roots phase) (source phase) (decoration phase))) := by
  have hledger := sum_literalExactWord_absorption_add_capacityBoundary_le_sum_recharge
    source roots decoration hexact hbudget horizon
  have hterminal := (quittingPunishmentFloorBoxChargedRelation reward).value_nonneg hbudget
    (quittingActualProfileBoxState (source horizon) (decoration horizon))
  linarith

end GameTheory
