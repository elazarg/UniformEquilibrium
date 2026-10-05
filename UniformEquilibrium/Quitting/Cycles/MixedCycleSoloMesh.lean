import UniformEquilibrium.Quitting.Cycles.SingletonArcCycle

/-! # Fixed-width solo refinement of mixed finite cycles

Every coarse phase has `m` slots. Solo phases are subdivided; other product
roots occur once, followed by all-Continue rows at the next coarse value.
The actual period is `L * m`, including these harmless quiet slots.
-/

noncomputable section

namespace GameTheory.MixedCycleSoloMesh

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] {L m : ℕ}

/-- Solo owners may repeat, and a solo aggregate hazard may be zero. -/
def refinedRoot (solo : Fin L → Bool) (owner : Fin L → ι) (mass : Fin L → ℝ)
    (coarseRoot : Fin L → ι → PMF Bool) (m : ℕ)
    (hmass0 : ∀ block, 0 ≤ mass block) (hmass1 : ∀ block, mass block < 1)
    (phase : Fin (L * m)) : ι → PMF Bool :=
  let block := quittingSingletonMeshBlock phase
  let offset := quittingSingletonMeshOffset phase
  if solo block = true then
    quittingSoloStationaryRoot (owner block)
      (quittingMeshHazardCoin (mass block) m (hmass0 block) (hmass1 block))
  else if offset.val = 0 then coarseRoot block else quittingAllContinueRoot

/-- Quiet slots after a retained root carry the next coarse value, so no
additional joint event is introduced by the fixed-width indexing. -/
def refinedValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (solo : Fin L → Bool) (owner : Fin L → ι) (mass : Fin L → ℝ)
    (coarseValue : Fin L → Payoff ι) (m : ℕ) (phase : Fin (L * m)) : Payoff ι :=
  let block := quittingSingletonMeshBlock phase
  let offset := quittingSingletonMeshOffset phase
  if solo block = true then
    quittingMeshPayoffInterpolant (quittingSoloReward reward (owner block))
      (coarseValue block) (1 - quittingMeshHazard (mass block) m) offset.val
  else if offset.val = 0 then coarseValue block else coarseValue (finRotate L block)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem refinedValue_initial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (solo : Fin L → Bool) (owner : Fin L → ι) (mass : Fin L → ℝ)
    (coarseValue : Fin L → Payoff ι) (block : Fin L) (hm : 0 < m) :
    refinedValue reward solo owner mass coarseValue m
        (quittingSingletonMeshInitialPhase block m hm) = coarseValue block := by
  simp only [quittingSingletonMeshInitialPhase, refinedValue,
    quittingSingletonMeshBlock_phase, quittingSingletonMeshOffset_phase]
  by_cases hsolo : solo block = true
  · simp only [hsolo, ite_true]
    funext who
    simp [quittingMeshPayoffInterpolant, quittingMeshInterpolant]
  · simp [hsolo]

omit [Fintype ι] [DecidableEq ι] in
theorem refinedValue_rotate_of_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (solo : Fin L → Bool) (owner : Fin L → ι) (mass : Fin L → ℝ)
    (coarseValue : Fin L → Payoff ι) (hm : 0 < m)
    (hmass1 : ∀ block, mass block < 1)
    (block : Fin L) (offset : Fin m) (hsolo : solo block = true)
    (harc : coarseValue block = quittingSingletonArcPayoff (mass block)
      (quittingSoloReward reward (owner block)) (coarseValue (finRotate L block))) :
    refinedValue reward solo owner mass coarseValue m
        (finRotate (L * m) (quittingSingletonMeshPhase block offset)) =
      quittingMeshPayoffInterpolant (quittingSoloReward reward (owner block))
        (coarseValue block) (1 - quittingMeshHazard (mass block) m) (offset.val + 1) := by
  by_cases hlast : offset.val + 1 = m
  · rw [finRotate_quittingSingletonMeshPhase_of_offset_succ_eq block offset hm hlast]
    change refinedValue reward solo owner mass coarseValue m
      (quittingSingletonMeshInitialPhase (finRotate L block) m hm) = _
    rw [refinedValue_initial, hlast]
    exact (quittingMeshPayoffInterpolant_at_length_eq_next (hmass1 block) hm harc).symm
  · have hnext : offset.val + 1 < m := by omega
    rw [finRotate_quittingSingletonMeshPhase_of_offset_succ_lt block offset hnext]
    simp [refinedValue, quittingSingletonMeshBlock_phase,
      quittingSingletonMeshOffset_phase, hsolo]

omit [Fintype ι] [DecidableEq ι] in
theorem refinedValue_rotate_of_retained
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (solo : Fin L → Bool) (owner : Fin L → ι) (mass : Fin L → ℝ)
    (coarseValue : Fin L → Payoff ι) (hm : 0 < m)
    (block : Fin L) (offset : Fin m) (hsolo : solo block ≠ true) :
    refinedValue reward solo owner mass coarseValue m
        (finRotate (L * m) (quittingSingletonMeshPhase block offset)) =
      coarseValue (finRotate L block) := by
  by_cases hlast : offset.val + 1 = m
  · rw [finRotate_quittingSingletonMeshPhase_of_offset_succ_eq block offset hm hlast]
    exact refinedValue_initial reward solo owner mass coarseValue _ hm
  · have hnext : offset.val + 1 < m := by omega
    rw [finRotate_quittingSingletonMeshPhase_of_offset_succ_lt block offset hnext]
    simp [refinedValue, quittingSingletonMeshBlock_phase,
      quittingSingletonMeshOffset_phase, hsolo]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem refinedValue_scale_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (solo : Fin L → Bool) (owner : Fin L → ι) (mass : Fin L → ℝ)
    (coarseValue : Fin L → Payoff ι) (block : Fin L) :
    refinedValue reward solo owner mass coarseValue 1
        (quittingSingletonMeshPhase block 0) = coarseValue block := by
  exact refinedValue_initial reward solo owner mass coarseValue block (by decide)

/-- A solo block retains its coarse deleted-player survival factor. -/
theorem prod_continueMass_block_of_solo
    (solo : Fin L → Bool) (owner : Fin L → ι) (mass : Fin L → ℝ)
    (coarseRoot : Fin L → ι → PMF Bool) (hm : 0 < m)
    (hmass0 : ∀ block, 0 ≤ mass block) (hmass1 : ∀ block, mass block < 1)
    (block : Fin L) (who : ι) (hsolo : solo block = true) :
    (∏ offset : Fin m, quittingStationaryFixedOpponentsContinueMass
      (refinedRoot solo owner mass coarseRoot m hmass0 hmass1
        (quittingSingletonMeshPhase block offset)) who) =
      if who = owner block then 1 else 1 - mass block := by
  have hroot (offset : Fin m) :
      refinedRoot solo owner mass coarseRoot m hmass0 hmass1
          (quittingSingletonMeshPhase block offset) =
        quittingSingletonArcCycleRoot owner mass m hmass0 hmass1
          (quittingSingletonMeshPhase block offset) := by
    simp [refinedRoot, quittingSingletonArcCycleRoot, hsolo,
      quittingSingletonMeshBlock_phase]
  simp_rw [hroot]
  exact prod_quittingSingletonArcCycleRoot_continueMass_block
    owner mass m hm hmass0 hmass1 block who

end GameTheory.MixedCycleSoloMesh
