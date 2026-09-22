import UniformEquilibrium.Quitting.Cycles.BalancedSingletonActualPath
import UniformEquilibrium.Quitting.Classification.BlockDeletionInequality

/-! # Actual balanced child paths with a Never-playing deleted block

The input certificate belongs to the deleted child reward, not the parent.
The canonical deletion-root extension supplies an absorbing parent solo path
and transports actual child floors and ties. No floor for a deleted player
is assumed or asserted here.
-/

noncomputable section

namespace GameTheory

open Filter _root_.Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Extending a root sequence by sure Continue leaves every finite joint
survival product unchanged. -/
theorem quittingJointSurvivalWeight_extendDeletedRoots
    (B : Finset ι) (roots : ℕ → QuittingBlockSurvivor B → PMF Bool)
    (start fuel : ℕ) :
    quittingJointSurvivalWeight (quittingExtendDeletedRoots (· ∈ B) roots) start fuel =
      quittingJointSurvivalWeight roots start fuel := by
  simp only [quittingJointSurvivalWeight_eq_prod, quittingExtendDeletedRoots,
    quittingStationaryContinueMass_extendDeletedRoot]

/-- The actual probability of Never is unchanged by the canonical root lift. -/
theorem quittingLiveMassLimit_extendDeletedRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (B : Finset ι) (roots : ℕ → QuittingBlockSurvivor B → PMF Bool) (start : ℕ) :
    quittingLiveMassLimit reward
        (quittingRootSequenceProfile reward (quittingExtendDeletedRoots (· ∈ B) roots) start) =
      quittingLiveMassLimit (quittingDeleteReward reward (· ∈ B))
        (quittingRootSequenceProfile (quittingDeleteReward reward (· ∈ B)) roots start) := by
  rw [quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit,
    quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit]
  apply tendsto_nhds_unique
    (tendsto_quittingJointSurvivalLimit (quittingExtendDeletedRoots (· ∈ B) roots) start)
  have heq : quittingJointSurvivalWeight (quittingExtendDeletedRoots (· ∈ B) roots) start =
      quittingJointSurvivalWeight roots start := by
    funext fuel
    exact quittingJointSurvivalWeight_extendDeletedRoots B roots start fuel
  rw [heq]
  exact tendsto_quittingJointSurvivalLimit roots start

namespace BalancedSingletonCycleCertificate

variable {L : ℕ} {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (B : Finset ι)
variable (certificate : BalancedSingletonCycleCertificate (L := L)
  (quittingDeleteReward reward (· ∈ B)))

/-- The literal parent root sequence: compile the child mesh and make the
whole deleted block Continue forever. -/
def deletedRootSequence (m : ℕ) (phase : Fin (L * m)) : ℕ → ι → PMF Bool :=
  quittingExtendDeletedRoots (· ∈ B)
    (quittingCyclicRootSequence
      (quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
        certificate.hazard_nonneg certificate.hazard_lt_one) phase)

omit [Fintype ι] in
theorem deletedRootSequence_of_deleted (m : ℕ) (phase : Fin (L * m))
    (time : ℕ) (who : ι) (hwho : who ∈ B) :
    certificate.deletedRootSequence B m phase time who = PMF.pure false := by
  exact quittingExtendDeletedRoots_of_deleted (· ∈ B) _ time hwho

omit [Fintype ι] in
theorem deletedRootSequence_apply_survivor (m : ℕ) (phase : Fin (L * m))
    (time : ℕ) (who : QuittingBlockSurvivor B) :
    certificate.deletedRootSequence B m phase time who.1 =
      quittingCyclicRootSequence
        (quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
          certificate.hazard_nonneg certificate.hazard_lt_one) phase time who := by
  exact quittingExtendDeletedRoots_apply (· ∈ B) _ time who

omit [Fintype ι] in
/-- Only the current embedded child owner may quit. -/
theorem deletedRootSequence_solo (m : ℕ) (phase : Fin (L * m)) (time : ℕ)
    (other : ι) (hne : other ≠ (certificate.owner
      (quittingSingletonMeshBlock (quittingCyclicOrbit phase time))).1) :
    certificate.deletedRootSequence B m phase time other = PMF.pure false := by
  by_cases hdeleted : other ∈ B
  · exact certificate.deletedRootSequence_of_deleted B m phase time other hdeleted
  · have hne' : (⟨other, hdeleted⟩ : QuittingBlockSurvivor B) ≠
        certificate.owner (quittingSingletonMeshBlock (quittingCyclicOrbit phase time)) := by
      intro heq
      exact hne (congrArg Subtype.val heq)
    change certificate.deletedRootSequence B m phase time
      (⟨other, hdeleted⟩ : QuittingBlockSurvivor B).1 = _
    rw [certificate.deletedRootSequence_apply_survivor B]
    exact certificate.rootSequence_solo m phase time ⟨other, hdeleted⟩ hne'

omit [Fintype ι] in
theorem deletedRootSequence_hazard_lt_one (m : ℕ) (phase : Fin (L * m)) (time : ℕ) :
    (certificate.deletedRootSequence B m phase time
      (certificate.owner (quittingSingletonMeshBlock
        (quittingCyclicOrbit phase time))).1 true).toReal < 1 := by
  rw [certificate.deletedRootSequence_apply_survivor B]
  exact certificate.rootSequence_hazard_lt_one m phase time

/-- Absorption is inherited from the child, without a parent certificate. -/
theorem deletedRootSequence_liveMassLimit_eq_zero (m : ℕ) (hm : 0 < m)
    (phase : Fin (L * m)) :
    quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward (certificate.deletedRootSequence B m phase) 0) = 0 := by
  unfold deletedRootSequence
  rw [quittingLiveMassLimit_extendDeletedRoots]
  exact certificate.rootSequence_liveMassLimit_eq_zero m hm phase

/-- Parent terminal values of surviving players are the actual child mesh
values at the corresponding rotated phase. -/
theorem deletedRootSequence_terminalValue_eq (m : ℕ) (hm : 0 < m)
    (phase : Fin (L * m)) (time : ℕ) (who : QuittingBlockSurvivor B) :
    quittingRootSequenceTerminalValue reward
        (certificate.deletedRootSequence B m phase) who.1 time =
      quittingSingletonArcCycleValue (quittingDeleteReward reward (· ∈ B))
        certificate.owner certificate.hazard certificate.coarse m
        (quittingCyclicOrbit phase time) who := by
  unfold deletedRootSequence
  rw [quittingRootSequenceTerminalValue_extendDeletedRoots]
  exact certificate.rootSequence_terminalValue_eq m hm phase time who

/-- Actual parent singleton floors hold for each surviving child player. -/
theorem deletedRootSequence_soloFloor (m : ℕ) (hm : 0 < m)
    (phase : Fin (L * m)) (time : ℕ) (who : QuittingBlockSurvivor B) :
    quittingSoloReward reward who.1 who.1 ≤
      quittingRootSequenceTerminalValue reward
        (certificate.deletedRootSequence B m phase) who.1 time := by
  unfold deletedRootSequence
  rw [quittingRootSequenceTerminalValue_extendDeletedRoots]
  have hsolo : quittingSoloReward (quittingDeleteReward reward (· ∈ B)) who who =
      quittingSoloReward reward who.1 who.1 :=
    quittingDeleteReward_singletonTerminal reward (· ∈ B) who who
  rw [← hsolo]
  exact certificate.rootSequence_soloFloor m hm phase time who

/-- The embedded owner's actual parent continuation is exactly its singleton
reward, even when its current hazard is zero. -/
theorem deletedRootSequence_owner_tie (m : ℕ) (hm : 0 < m)
    (phase : Fin (L * m)) (time : ℕ) :
    quittingRootSequenceTerminalValue reward
        (certificate.deletedRootSequence B m phase)
        (certificate.owner (quittingSingletonMeshBlock
          (quittingCyclicOrbit phase time))).1 time =
      quittingSoloReward reward
        (certificate.owner (quittingSingletonMeshBlock (quittingCyclicOrbit phase time))).1
        (certificate.owner (quittingSingletonMeshBlock (quittingCyclicOrbit phase time))).1 := by
  unfold deletedRootSequence
  rw [quittingRootSequenceTerminalValue_extendDeletedRoots, certificate.rootSequence_owner_tie m hm]
  exact quittingDeleteReward_singletonTerminal reward (· ∈ B) _ _

end BalancedSingletonCycleCertificate
end GameTheory
