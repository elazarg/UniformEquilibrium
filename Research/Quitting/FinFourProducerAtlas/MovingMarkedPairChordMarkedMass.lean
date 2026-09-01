import Research.Quitting.FinFourProducerAtlas.MovingMarkedPairSource

/-!
# The marked atom of an actual moving-pair response chord

The complete stopping-law chord retains the literal marked date.  At that
date the source root is the fixed pair, the target root is the pair plus the
mover, and the chord assigns exactly its mixing weight times the actual
unconditional reach to the target coalition.

This is a finite-stage identity.  It does not construct a moving family or a
causal source.
-/

noncomputable section

namespace GameTheory

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

namespace FinFourMovingMarkedPairMinimumSource

/-- The source has no mass on the routed coalition at the marked date. -/
theorem source_stageCoalitionMass_targetTerminal_eq_zero
    (data : FinFourMovingMarkedPairMinimumSource source) (rank : ℕ) :
    quittingStageCoalitionMass reward (data.sourceProfile rank)
        (data.marked rank).mark data.labels.targetTerminal = 0 := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  change quittingLiveMass reward (data.sourceProfile rank)
      (data.marked rank).mark *
      quittingRootCoalitionMass
        (quittingProfileLiveRoot reward (data.marked rank).sourceProfile
          (data.marked rank).mark) data.labels.targetTerminal.val = 0
  rw [(data.purePair rank).source_root_eq,
    QuittingActualReachedScreenedEndpointMark.PurePairData.quittingRootCoalitionMass_pureSetRoot,
    data.purePair_coalition_eq rank]
  have hne : data.labels.targetTerminal.val ≠ data.labels.pair := by
    intro hvalue
    apply (data.purePair rank).targetTerminal_ne_sourceTerminal
    apply Subtype.ext
    rw [data.purePair_targetTerminal_eq rank,
      data.purePair_sourceTerminal_eq rank]
    exact hvalue
  simp [hne]

/-- The routed target puts all marked reach on its routed coalition. -/
theorem target_stageCoalitionMass_targetTerminal_eq_markedReach
    (data : FinFourMovingMarkedPairMinimumSource source) (rank : ℕ) :
    quittingStageCoalitionMass reward (data.targetProfile rank)
        (data.marked rank).mark data.labels.targetTerminal =
      data.markedReach rank := by
  have hlive : quittingLiveMass reward (data.targetProfile rank)
      (data.marked rank).mark = data.markedReach rank := by
    unfold markedReach targetProfile sourceProfile
    apply quittingLiveMass_eq_of_liveRoot_eq_of_lt
    intro time htime
    exact (data.marked rank).targetProfile_liveRoot_eq_of_lt htime
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass, hlive]
  change data.markedReach rank *
      quittingRootCoalitionMass
        (quittingProfileLiveRoot reward (data.marked rank).targetProfile
          (data.marked rank).mark) data.labels.targetTerminal.val =
    data.markedReach rank
  rw [(data.purePair rank).target_root_eq_pureSetRoot_routed,
    QuittingActualReachedScreenedEndpointMark.PurePairData.quittingRootCoalitionMass_pureSetRoot,
    data.purePair_targetTerminal_eq rank]
  simp

/-- The actual stopping-law chord has exactly `weight * markedReach` mass on
the routed coalition at the original marked date. -/
theorem chord_stageCoalitionMass_targetTerminal_eq_weight_mul_markedReach
    (data : FinFourMovingMarkedPairMinimumSource source)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (rank : ℕ) :
    quittingStageCoalitionMass reward
        (data.chordProfile weight hweight0 hweight1 rank)
        (data.marked rank).mark data.labels.targetTerminal =
      weight * data.markedReach rank := by
  unfold chordProfile quittingResponseChordProfile
  rw [
    quittingStageCoalitionMass_stoppingLawMixture_eq,
    Function.update_eq_self,
    update_endpoint_with_response_observer_eq_response reward
      (data.sourceProfile rank) (data.targetProfile rank) data.labels.mover
      (data.targetProfile_eq_sourceProfile_of_ne rank),
    data.source_stageCoalitionMass_targetTerminal_eq_zero rank,
    data.target_stageCoalitionMass_targetTerminal_eq_markedReach rank]
  ring

end FinFourMovingMarkedPairMinimumSource

end GameTheory
