import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Root.NashDefect

/-! # Absorption-weighted finite forward packet data -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A finite approximate forward packet whose Bellman residual and ordinary
root regret are weighted by the row absorption mass. Packet existence is not
part of this data structure. -/
structure QuittingAbsorptionWeightedForwardPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (Payoff ι)) (tolerance chargeTarget : ℝ) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  horizon : ℕ
  value_mem : ∀ time, time ≤ horizon → value time ∈ carrier
  bellman : ∀ time, time < horizon → ∀ who,
    |value (time + 1) who -
        quittingRootSuccessorPayoff reward (value time) (roots time) who| ≤
      tolerance * quittingRootAbsorptionMass (roots time)
  regret : ∀ time, time < horizon → ∀ who,
    quittingRootCoordinateNashDefect reward (value time) (roots time) who ≤
      tolerance * quittingRootAbsorptionMass (roots time)
  rational : ∀ target time, time ≤ horizon →
    quittingPunishmentValue reward target - tolerance ≤ value time target
  chargeTarget_le : chargeTarget ≤ ∑ time ∈ Finset.range horizon,
    quittingRootAbsorptionMass (roots time)

end GameTheory
