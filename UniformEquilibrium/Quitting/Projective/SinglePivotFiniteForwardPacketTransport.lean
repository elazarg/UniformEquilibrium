import UniformEquilibrium.Quitting.Root.SinglePivotFiniteBellmanTransport
import UniformEquilibrium.Quitting.Projective.FiniteForwardProjectiveLasso
import UniformEquilibrium.Quitting.Punishment.SinglePivotPunishment

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A supplied finite forward packet transports with the same roots, horizon,
and absorption charge. -/
def QuittingFiniteForwardPacket.singlePivotNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (carrier : Set (Payoff ι)) (supportError chargeTarget : ℝ)
    (packet : QuittingFiniteForwardPacket reward carrier supportError chargeTarget)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot) pivot)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      quittingSoloReward reward who who) :
    QuittingFiniteForwardPacket (quittingSinglePivotNormalizedReward reward pivot)
      (quittingSinglePivotNormalizedCarrier reward pivot carrier)
      (supportError / reward (quittingSingletonTerminal pivot) pivot) chargeTarget where
  roots := packet.roots
  value := fun time => quittingSinglePivotNormalizedPayoff reward pivot (packet.value time)
  horizon := packet.horizon
  value_mem := by
    intro time htime
    exact ⟨packet.value time, packet.value_mem time htime, rfl⟩
  policy := by
    intro time htime
    rw [packet.policy time htime]
    exact (quittingRootSuccessorPayoff_singlePivotNormalized
      reward pivot (packet.value time) (packet.roots time)).symm
  support := by
    intro time htime
    exact isQuittingRootSupportApproxNash_singlePivotNormalized reward pivot
      (packet.value time) (packet.roots time) supportError hpivot
      (packet.support time htime)
  rational := by
    intro who time htime
    have hsolo : quittingSoloReward reward pivot pivot =
        reward (quittingSingletonTerminal pivot) pivot := rfl
    rw [quittingPunishmentValue_singlePivotNormalized reward pivot who
      (hsolo.symm ▸ hpivot) (hnormal who), hsolo]
    dsimp [quittingSinglePivotNormalizedPayoff]
    have hrational := packet.rational who time htime
    rw [← sub_div]
    apply (div_le_div_iff_of_pos_right hpivot).2
    linarith
  chargeTarget_le := packet.chargeTarget_le

end GameTheory
