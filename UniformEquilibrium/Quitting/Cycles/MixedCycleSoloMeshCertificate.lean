import UniformEquilibrium.Quitting.Cycles.MixedCycleSoloMesh
import MathUE.ProbabilityMassFunction.Bool

/-! # Literal phase certificates for a mixed-cycle solo mesh

Retained product roots need exact Continue for every player, not merely root
Nash. Zero solo hazards impose no owner anchor. Positive solo hazards use the
canonical singleton interpolation certificate, including nonzero singleton rewards.
-/

noncomputable section

namespace GameTheory.MixedCycleSoloMesh

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] {L m : ℕ}

/-- A quiet row supplies exact policy and Continue, and singleton Quit caps. -/
theorem allContinue_phase_certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : Payoff ι) (hfloor : ∀ who, quittingSoloReward reward who who ≤ value who)
    {error : ℝ} (herror : 0 ≤ error) :
    value = quittingRootSuccessorPayoff reward value quittingAllContinueRoot ∧
      (∀ who, quittingRootContinuePayoff reward value quittingAllContinueRoot who =
        value who) ∧
      ∀ who, quittingRootQuitPayoff reward value quittingAllContinueRoot who ≤
        value who + error := by
  have hpolicy : value = quittingRootSuccessorPayoff reward value quittingAllContinueRoot := by
    funext who
    rw [quittingRootSuccessorPayoff_eq_endpointMix]
    simp [quittingAllContinueRoot]
  refine ⟨hpolicy,
    fun who => quittingRootContinuePayoff_allContinueRoot reward value who, ?_⟩
  intro who
  rw [quittingRootQuitPayoff_allContinueRoot]
  change quittingSoloReward reward who who ≤ value who + error
  exact (hfloor who).trans (le_add_of_nonneg_right herror)

/-- The concrete refined phase obeys the three Bellman inequalities needed by
the full behavioral cyclic compiler. Only positive solo rows require an anchor. -/
theorem refinedPhase_certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (solo : Fin L → Bool) (owner : Fin L → ι) (mass : Fin L → ℝ)
    (coarseRoot : Fin L → ι → PMF Bool) (coarseValue : Fin L → Payoff ι)
    (hm : 0 < m) (hmass0 : ∀ block, 0 ≤ mass block)
    (hmass1 : ∀ block, mass block < 1) {D error : ℝ}
    (hD : 0 ≤ D) (herror : 0 ≤ error)
    (harc : ∀ block, solo block = true →
      coarseValue block = quittingSingletonArcPayoff (mass block)
        (quittingSoloReward reward (owner block)) (coarseValue (finRotate L block)))
    (hactive : ∀ block, solo block = true → 0 < mass block →
      coarseValue block (owner block) = quittingSoloReward reward (owner block) (owner block))
    (hfloor : ∀ block who, quittingSoloReward reward who who ≤ coarseValue block who)
    (hcollision : ∀ block other, other ≠ owner block →
      max (quittingSingletonCollisionReward reward (owner block) other -
        quittingSoloReward reward other other) 0 ≤ D)
    (hmesh : ∀ block, D * quittingMeshHazard (mass block) m ≤ error)
    (hpolicy : ∀ block, solo block ≠ true →
      coarseValue block = quittingRootSuccessorPayoff reward
        (coarseValue (finRotate L block)) (coarseRoot block))
    (hcontinue : ∀ block, solo block ≠ true → ∀ who,
      quittingRootContinuePayoff reward (coarseValue (finRotate L block))
        (coarseRoot block) who = coarseValue block who)
    (hquit : ∀ block, solo block ≠ true → ∀ who,
      quittingRootQuitPayoff reward (coarseValue (finRotate L block))
        (coarseRoot block) who ≤ coarseValue block who)
    (block : Fin L) (offset : Fin m) :
    let phase := quittingSingletonMeshPhase block offset
    let current := refinedValue reward solo owner mass coarseValue m phase
    let next := refinedValue reward solo owner mass coarseValue m (finRotate (L * m) phase)
    let root := refinedRoot solo owner mass coarseRoot m hmass0 hmass1 phase
    current = quittingRootSuccessorPayoff reward next root ∧
      (∀ who, quittingRootContinuePayoff reward next root who = current who) ∧
      ∀ who, quittingRootQuitPayoff reward next root who ≤ current who + error := by
  dsimp only
  by_cases hsolo : solo block = true
  · rw [refinedValue_rotate_of_solo reward solo owner mass coarseValue hm hmass1
      block offset hsolo (harc block hsolo)]
    simp only [refinedValue, refinedRoot, quittingSingletonMeshBlock_phase,
      quittingSingletonMeshOffset_phase, hsolo, ite_true]
    by_cases hpositive : 0 < mass block
    · have hlocal := singletonMeshStationaryRoot_interpolant_certificate reward
        (owner block) m (hmass0 block) (hmass1 block)
        (quittingSoloReward reward (owner block)) (coarseValue block) offset.val
        hD rfl (hactive block hsolo hpositive)
        (fun who => le_quittingMeshPayoffInterpolant_of_arcEndpoints
          (hmass0 block) (hmass1 block) hm (harc block hsolo)
          (hfloor block) (hfloor (finRotate L block)) offset.val offset.isLt.le who)
        (hcollision block)
      refine ⟨hlocal.1, ?_, ?_⟩
      · intro who
        rw [quittingRootContinuePayoff_eq_fixedOpponents reward
          (fun _ => quittingSoloStationaryRoot (owner block)
            (quittingMeshHazardCoin (mass block) m (hmass0 block) (hmass1 block))) who
          (quittingMeshPayoffInterpolant (quittingSoloReward reward (owner block))
            (coarseValue block) (1 - quittingMeshHazard (mass block) m) (offset.val + 1)) 0]
        exact hlocal.2.1 who
      · intro who
        rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
          (fun _ => quittingSoloStationaryRoot (owner block)
            (quittingMeshHazardCoin (mass block) m (hmass0 block) (hmass1 block))) who
          (quittingMeshPayoffInterpolant (quittingSoloReward reward (owner block))
            (coarseValue block) (1 - quittingMeshHazard (mass block) m) (offset.val + 1)) 0]
        apply (hlocal.2.2 who).trans
        simpa only [add_comm] using add_le_add_left (hmesh block)
          (quittingMeshPayoffInterpolant (quittingSoloReward reward (owner block))
            (coarseValue block) (1 - quittingMeshHazard (mass block) m) offset.val who)
    · have hzero : mass block = 0 := le_antisymm (le_of_not_gt hpositive) (hmass0 block)
      have hh : quittingMeshHazard (mass block) m = 0 := by
        simp [hzero, quittingMeshHazard]
      have hcoin : quittingMeshHazardCoin (mass block) m (hmass0 block)
          (hmass1 block) = PMF.pure false := by
        apply Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
        simp [hh]
      have hroot : quittingSoloStationaryRoot (owner block)
          (quittingMeshHazardCoin (mass block) m (hmass0 block) (hmass1 block)) =
          quittingAllContinueRoot := by
        funext who
        simp [hcoin, quittingSoloStationaryRoot, quittingAllContinueRoot]
      rw [hroot]
      have hinterp (k : ℕ) : quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner block)) (coarseValue block)
          (1 - quittingMeshHazard (mass block) m) k = coarseValue block := by
        funext who
        simp [hh, quittingMeshPayoffInterpolant, quittingMeshInterpolant]
      rw [hinterp, hinterp]
      exact allContinue_phase_certificate reward (coarseValue block) (hfloor block) herror
  · rw [refinedValue_rotate_of_retained reward solo owner mass coarseValue hm
      block offset hsolo]
    simp only [refinedValue, refinedRoot, quittingSingletonMeshBlock_phase,
      quittingSingletonMeshOffset_phase, hsolo]
    by_cases hfirst : offset.val = 0
    · simp only [hfirst, ite_true]
      exact ⟨hpolicy block hsolo, hcontinue block hsolo,
        fun who => (hquit block hsolo who).trans (le_add_of_nonneg_right herror)⟩
    · simp only [hfirst, ite_false]
      exact allContinue_phase_certificate reward (coarseValue (finRotate L block))
        (hfloor (finRotate L block)) herror

end GameTheory.MixedCycleSoloMesh
