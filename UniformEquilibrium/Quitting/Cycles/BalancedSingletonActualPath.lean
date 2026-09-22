import UniformEquilibrium.Quitting.Cycles.BalancedSingletonCertificate
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart

/-! # Actual infinite paths of balanced singleton child certificates

Every positive subdivision and every initial mesh phase give an absorbing
solo root sequence. Its actual terminal values are the canonical interpolants,
so the child singleton floors and owner ties hold at every date. A certificate
here is on the given reward table alone; no parent or outsider floor is assumed.
-/

noncomputable section

namespace GameTheory.BalancedSingletonCycleCertificate

open Filter _root_.Math.Probability
open scoped BigOperators Topology

variable {L : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (certificate : BalancedSingletonCycleCertificate (L := L) reward)

/-- The existing coarse opponent contraction is unchanged by subdivision. -/
theorem mesh_opponent_product_lt_one (m : ℕ) (hm : 0 < m) (who : ι) :
    (∏ phase : Fin (L * m), quittingStationaryFixedOpponentsContinueMass
      (quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
        certificate.hazard_nonneg certificate.hazard_lt_one phase) who) < 1 := by
  rw [prod_quittingSingletonArcCycleRoot_continueMass certificate.owner
    certificate.hazard m hm certificate.hazard_nonneg certificate.hazard_lt_one who]
  exact certificate.opponent_product_lt_one who

/-- The mesh annotations are actual terminal values at all phases, not only
at the certificate's selected coarse initial phase. -/
theorem mesh_value_eq_actual (m : ℕ) (hm : 0 < m) :
    quittingSingletonArcCycleValue reward certificate.owner certificate.hazard
        certificate.coarse m =
      quittingCyclicTerminalValue reward
        (quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
          certificate.hazard_nonneg certificate.hazard_lt_one) := by
  apply eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff
  · intro phase
    exact (quittingSingletonArcCycle_phase_certificate reward certificate.owner
      certificate.hazard certificate.coarse m hm certificate.hazard_nonneg
      certificate.hazard_lt_one certificate.arc
      (balancedSingletonCycleCollisionCap_nonneg reward) certificate.active
      certificate.soloFloor
      (fun block other hne => balancedSingletonCycle_collision_bound reward
        (certificate.owner block) other hne) phase).1
  · exact certificate.mesh_opponent_product_lt_one m hm

/-- Actual suffix values from an arbitrary initial phase select the rotated
mesh interpolant. -/
theorem rootSequence_terminalValue_eq (m : ℕ) (hm : 0 < m)
    (phase : Fin (L * m)) (time : ℕ) (who : ι) :
    quittingRootSequenceTerminalValue reward
        (quittingCyclicRootSequence
          (quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
            certificate.hazard_nonneg certificate.hazard_lt_one) phase) who time =
      quittingSingletonArcCycleValue reward certificate.owner certificate.hazard
        certificate.coarse m (quittingCyclicOrbit phase time) who := by
  rw [quittingRootSequenceTerminalValue_cyclic_eq, ← certificate.mesh_value_eq_actual m hm]

omit [Fintype ι] in
/-- Every nonowner literally continues at every date of the actual sequence. -/
theorem rootSequence_solo (m : ℕ) (phase : Fin (L * m)) (time : ℕ) (other : ι)
    (hne : other ≠ certificate.owner
      (quittingSingletonMeshBlock (quittingCyclicOrbit phase time))) :
    quittingCyclicRootSequence
        (quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
          certificate.hazard_nonneg certificate.hazard_lt_one) phase time other =
      PMF.pure false := by
  simp only [quittingCyclicRootSequence, quittingSingletonArcCycleRoot,
    quittingSoloStationaryRoot, Function.update_of_ne hne]

omit [Fintype ι] in
/-- The actual owner's quit probability is the prescribed mesh hazard. -/
theorem rootSequence_owner_hazard (m : ℕ) (phase : Fin (L * m)) (time : ℕ) :
    (quittingCyclicRootSequence
      (quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
        certificate.hazard_nonneg certificate.hazard_lt_one) phase time
      (certificate.owner (quittingSingletonMeshBlock
        (quittingCyclicOrbit phase time))) true).toReal =
      quittingMeshHazard
        (certificate.hazard (quittingSingletonMeshBlock
          (quittingCyclicOrbit phase time))) m := by
  simp only [quittingCyclicRootSequence, quittingSingletonArcCycleRoot,
    quittingSoloStationaryRoot, Function.update_self, quittingMeshHazardCoin_true_toReal]

omit [Fintype ι] in
theorem rootSequence_hazard_lt_one (m : ℕ) (phase : Fin (L * m)) (time : ℕ) :
    (quittingCyclicRootSequence
      (quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
        certificate.hazard_nonneg certificate.hazard_lt_one) phase time
      (certificate.owner (quittingSingletonMeshBlock
        (quittingCyclicOrbit phase time))) true).toReal < 1 := by
  rw [certificate.rootSequence_owner_hazard]
  exact quittingMeshHazard_lt_one (certificate.hazard_lt_one _) m

/-- Every initial phase absorbs almost surely. Nonemptiness of the player
type is already supplied by the certificate's owner at its initial phase. -/
theorem rootSequence_liveMassLimit_eq_zero (m : ℕ) (hm : 0 < m)
    (phase : Fin (L * m)) :
    quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward
        (quittingCyclicRootSequence
          (quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
            certificate.hazard_nonneg certificate.hazard_lt_one) phase) 0) = 0 := by
  let cycle := quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
    certificate.hazard_nonneg certificate.hazard_lt_one
  let who := certificate.owner certificate.initial
  have hopponent : Tendsto
      (quittingOpponentSurvivalWeight (quittingCyclicRootSequence cycle phase) who 0)
      atTop (nhds 0) :=
    tendsto_zero_quittingOpponentSurvivalWeight_cyclicRootSequence cycle phase who
      (certificate.mesh_opponent_product_lt_one m hm who)
  have hjoint : Tendsto
      (quittingJointSurvivalWeight (quittingCyclicRootSequence cycle phase) 0)
      atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun fuel => quittingJointSurvivalWeight_nonneg _ _ fuel
    · exact fun fuel => quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
        (quittingCyclicRootSequence cycle phase) who 0 fuel
    · exact hopponent
  rw [quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit]
  exact tendsto_nhds_unique
    (tendsto_quittingJointSurvivalLimit (quittingCyclicRootSequence cycle phase) 0) hjoint

/-- The child's singleton floors hold for actual terminal values at every
date, including dates inside subdivided arcs. -/
theorem rootSequence_soloFloor (m : ℕ) (hm : 0 < m)
    (phase : Fin (L * m)) (time : ℕ) (who : ι) :
    quittingSoloReward reward who who ≤
      quittingRootSequenceTerminalValue reward
        (quittingCyclicRootSequence
          (quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
            certificate.hazard_nonneg certificate.hazard_lt_one) phase) who time := by
  rw [certificate.rootSequence_terminalValue_eq m hm]
  exact quittingSoloReward_le_quittingSingletonArcCycleValue_of_coarse reward
    certificate.owner certificate.hazard certificate.coarse m hm certificate.hazard_nonneg
    certificate.hazard_lt_one certificate.arc certificate.soloFloor _ who

/-- The owner's actual value is its singleton payoff. This also holds at
zero-hazard dates, so it implies the required positive-hazard tie. -/
theorem rootSequence_owner_tie (m : ℕ) (hm : 0 < m)
    (phase : Fin (L * m)) (time : ℕ) :
    quittingRootSequenceTerminalValue reward
        (quittingCyclicRootSequence
          (quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
            certificate.hazard_nonneg certificate.hazard_lt_one) phase)
        (certificate.owner (quittingSingletonMeshBlock
          (quittingCyclicOrbit phase time))) time =
      quittingSoloReward reward
        (certificate.owner (quittingSingletonMeshBlock (quittingCyclicOrbit phase time)))
        (certificate.owner (quittingSingletonMeshBlock (quittingCyclicOrbit phase time))) := by
  rw [certificate.rootSequence_terminalValue_eq m hm]
  exact quittingMeshPayoffInterpolant_eq_root_of_eq (certificate.active _) _

end GameTheory.BalancedSingletonCycleCertificate
