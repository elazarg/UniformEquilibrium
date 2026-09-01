import Research.Quitting.FinFourProducerAtlas.Source
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualReachedPairPremarkResidual
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticMinimumResponseChord

/-!
# A supplied moving marked-pair minimum source

This module packages the extra ancestry data needed to move a fixed outsider
into a fixed two-player quitting coalition at a rank-dependent actual date.
The ordinary minimum-atom producer does not construct this data.

All profiles below are literal behavioral profiles.  The target changes only
the mover at the displayed date, and the chord mixes the mover's complete
stopping laws.  There is no chronology, regeneration, renewal, Nash, or
uniform-equilibrium conclusion.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

/-- The fixed labels of an outsider joining a nonempty host coalition. -/
structure FinFourMovingMarkedPairLabels where
  pair : Finset (Fin 4)
  pair_nonempty : pair.Nonempty
  mover : Fin 4
  mover_not_mem : mover ∉ pair

namespace FinFourMovingMarkedPairLabels

/-- The fixed source coalition. -/
def sourceTerminal (labels : FinFourMovingMarkedPairLabels) :
    {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨labels.pair, labels.pair_nonempty⟩

/-- The fixed target coalition obtained by adding the outsider. -/
def targetTerminal (labels : FinFourMovingMarkedPairLabels) :
    {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨insert labels.mover labels.pair, Finset.insert_nonempty _ _⟩

/-- The fixed local reward gap for the outsider. -/
def rewardGap
    (labels : FinFourMovingMarkedPairLabels)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : ℝ :=
  reward labels.targetTerminal labels.mover -
    reward labels.sourceTerminal labels.mover

end FinFourMovingMarkedPairLabels

/-- A supplied moving marked-family over one minimum-atom producer.

The `marked` field is the checked one-row representation of the raw packet
data.  `purePair` and the three following equalities say that the selected
endpoint is exactly the fixed outsider joining the fixed pair, rather than a
rank-dependent relabelling. -/
structure FinFourMovingMarkedPairMinimumSource
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  labels : FinFourMovingMarkedPairLabels
  marked : ℕ → QuittingActualReachedScreenedEndpointMark reward
  purePair : ∀ rank, QuittingActualReachedScreenedEndpointMark.PurePairData
    (marked rank)
  marked_mover_eq : ∀ rank, (marked rank).mover = labels.mover
  marked_selectedAction_eq_true : ∀ rank,
    (marked rank).selectedAction = true
  purePair_coalition_eq : ∀ rank, (purePair rank).coalition = labels.pair
  localGap_eq_rewardGap : ∀ rank,
    (marked rank).localEndpointGap = labels.rewardGap reward
  rewardGap_pos : 0 < labels.rewardGap reward
  reachFloor : ℝ
  reachFloor_pos : 0 < reachFloor
  reachFloor_le : ∀ rank, reachFloor ≤
    quittingLiveMass reward (marked rank).sourceProfile (marked rank).mark
  source_tendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward (marked rank).sourceProfile,
        quittingTerminalOutcomeMass reward (marked rank).sourceProfile))
    atTop (nhds source.point)

namespace FinFourMovingMarkedPairMinimumSource

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The literal source profile at one supplied rank. -/
def sourceProfile (data : FinFourMovingMarkedPairMinimumSource source)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  (data.marked rank).sourceProfile

/-- The literal one-row target at one supplied rank. -/
def targetProfile (data : FinFourMovingMarkedPairMinimumSource source)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  (data.marked rank).targetProfile

/-- The actual unconditional reach of the displayed row. -/
def markedReach (data : FinFourMovingMarkedPairMinimumSource source)
    (rank : ℕ) : ℝ :=
  quittingLiveMass reward (data.sourceProfile rank) (data.marked rank).mark

/-- Debt remaining for the mover after the literal marked toggle. -/
def premarkResidual (data : FinFourMovingMarkedPairMinimumSource source)
    (rank : ℕ) : ℝ :=
  (data.marked rank).premarkResidual

/-- Total-debt excess of the literal target over the supplied minimum. -/
def targetDebtExcess (data : FinFourMovingMarkedPairMinimumSource source)
    (rank : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (data.targetProfile rank)) -
    quittingTerminalSemanticDebtSum source.point.1

/-- The actual fixed-weight stopping-law response chord at one row. -/
def chordProfile
    (data : FinFourMovingMarkedPairMinimumSource source)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingResponseChordProfile reward (data.sourceProfile rank)
    (data.targetProfile rank) data.labels.mover weight hweight0 hweight1

/-- The pure-pair helper's source terminal is the fixed pair. -/
theorem purePair_sourceTerminal_eq
    (data : FinFourMovingMarkedPairMinimumSource source) (rank : ℕ) :
    (data.purePair rank).sourceTerminal = data.labels.sourceTerminal := by
  apply Subtype.ext
  exact data.purePair_coalition_eq rank

/-- The pure-pair helper's routed terminal is the fixed pair plus mover. -/
theorem purePair_targetTerminal_eq
    (data : FinFourMovingMarkedPairMinimumSource source) (rank : ℕ) :
    (data.purePair rank).targetTerminal = data.labels.targetTerminal := by
  apply Subtype.ext
  change quittingPureEndpointRoutedCoalition
      (data.purePair rank).coalition (data.marked rank).mover
        (data.marked rank).selectedAction =
    insert data.labels.mover data.labels.pair
  rw [data.purePair_coalition_eq rank, data.marked_mover_eq rank,
    data.marked_selectedAction_eq_true rank]
  simp

/-- The literal target changes no opponent's complete behavioral strategy. -/
theorem targetProfile_eq_sourceProfile_of_ne
    (data : FinFourMovingMarkedPairMinimumSource source)
    (rank : ℕ) (other : Fin 4) (hne : other ≠ data.labels.mover) :
    data.targetProfile rank other = data.sourceProfile rank other := by
  have hmarked : other ≠ (data.marked rank).mover := by
    rw [data.marked_mover_eq rank]
    exact hne
  unfold targetProfile sourceProfile
    QuittingActualReachedScreenedEndpointMark.targetProfile
    quittingLiteralOneDateProfile
  rw [Function.update_of_ne hmarked]

/-- The target mover is the fixed mover. -/
theorem target_mover_debt_eq_premarkResidual
    (data : FinFourMovingMarkedPairMinimumSource source) (rank : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (data.targetProfile rank))
        data.labels.mover =
      data.premarkResidual rank := by
  rw [← data.marked_mover_eq rank]
  exact (data.marked rank).target_mover_debt_eq_premarkResidual

/-- The whole-profile marked gain is reach times the fixed reward gap. -/
theorem targetPayoff_sub_sourcePayoff_eq_markedReach_mul_rewardGap
    (data : FinFourMovingMarkedPairMinimumSource source) (rank : ℕ) :
    quittingTerminalPayoff reward (data.targetProfile rank) data.labels.mover -
        quittingTerminalPayoff reward (data.sourceProfile rank)
          data.labels.mover =
      data.markedReach rank * data.labels.rewardGap reward := by
  rw [← data.marked_mover_eq rank]
  simpa only [QuittingActualReachedScreenedEndpointMark.markedToggleGain,
    targetProfile, markedReach, sourceProfile] using
    (data.marked rank).markedToggleGain_eq_liveMass_mul_localEndpointGap
      |>.trans (by rw [data.localGap_eq_rewardGap rank])

/-- The source mover debt is the marked contribution plus the premark
residual. -/
theorem source_mover_debt_eq_markedReach_mul_rewardGap_add_premarkResidual
    (data : FinFourMovingMarkedPairMinimumSource source) (rank : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (data.sourceProfile rank))
        data.labels.mover =
      data.markedReach rank * data.labels.rewardGap reward +
        data.premarkResidual rank := by
  rw [← data.marked_mover_eq rank]
  simpa only [targetProfile, markedReach, sourceProfile, premarkResidual] using
    (data.marked rank).source_mover_debt_eq_reach_mul_localEndpointGap_add_premarkResidual
      |>.trans (by rw [data.localGap_eq_rewardGap rank])

/-- The marked gain has the uniform positive lower bound supplied by the
moving family. -/
theorem reachFloor_mul_rewardGap_le_targetPayoffGain
    (data : FinFourMovingMarkedPairMinimumSource source) (rank : ℕ) :
    data.reachFloor * data.labels.rewardGap reward ≤
      quittingTerminalPayoff reward (data.targetProfile rank)
          data.labels.mover -
        quittingTerminalPayoff reward (data.sourceProfile rank)
          data.labels.mover := by
  rw [data.targetPayoff_sub_sourcePayoff_eq_markedReach_mul_rewardGap rank]
  exact mul_le_mul_of_nonneg_right (data.reachFloor_le rank)
    data.rewardGap_pos.le

/-- The target total-debt excess is nonnegative by global minimality. -/
theorem targetDebtExcess_nonneg
    (data : FinFourMovingMarkedPairMinimumSource source) (rank : ℕ) :
    0 ≤ data.targetDebtExcess rank := by
  unfold targetDebtExcess
  exact sub_nonneg.mpr (source.minimum _
    (quittingTerminalSemanticPair_mem_carrier reward (data.targetProfile rank)))

/-- The target law moves exactly the actual marked reach from the fixed pair
to the fixed pair plus mover, including the `Never` coordinate. -/
theorem target_terminalOutcomeMass_eq_add_dirac_sub_dirac
    (data : FinFourMovingMarkedPairMinimumSource source)
    (rank : ℕ) (outcome : QuittingTerminalOutcome (Fin 4)) :
    quittingTerminalOutcomeMass reward (data.targetProfile rank) outcome =
      quittingTerminalOutcomeMass reward (data.sourceProfile rank) outcome +
        data.markedReach rank *
          (if outcome = some data.labels.targetTerminal then 1 else 0) -
        data.markedReach rank *
          (if outcome = some data.labels.sourceTerminal then 1 else 0) := by
  have h := (data.purePair rank).target_terminalOutcomeMass_eq_add_dirac_sub_dirac
    outcome
  rw [data.purePair_targetTerminal_eq rank,
    data.purePair_sourceTerminal_eq rank] at h
  exact h

/-- The complete stopping-law chord has the fixed signed law transfer scaled
by its weight. -/
theorem chord_terminalOutcomeMass_eq_add_scaled_dirac_sub_dirac
    (data : FinFourMovingMarkedPairMinimumSource source)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (rank : ℕ) (outcome : QuittingTerminalOutcome (Fin 4)) :
    quittingTerminalOutcomeMass reward
        (data.chordProfile weight hweight0 hweight1 rank) outcome =
      quittingTerminalOutcomeMass reward (data.sourceProfile rank) outcome +
        weight * data.markedReach rank *
          (if outcome = some data.labels.targetTerminal then 1 else 0) -
        weight * data.markedReach rank *
          (if outcome = some data.labels.sourceTerminal then 1 else 0) := by
  rw [chordProfile, quittingTerminalOutcomeMass_responseChord_eq reward
    (data.sourceProfile rank) (data.targetProfile rank) data.labels.mover
      weight hweight0 hweight1
      (data.targetProfile_eq_sourceProfile_of_ne rank)]
  rw [data.target_terminalOutcomeMass_eq_add_dirac_sub_dirac rank outcome]
  ring

/-- Coordinatewise cap convexity for every actual moving-family chord row. -/
theorem chord_debt_le_affine
    (data : FinFourMovingMarkedPairMinimumSource source)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (rank : ℕ) (observer : Fin 4) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (data.chordProfile weight hweight0 hweight1 rank)) observer ≤
      (1 - weight) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (data.sourceProfile rank))
          observer +
        weight * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (data.targetProfile rank))
          observer := by
  exact quittingTerminalSemanticDebt_responseChord_le reward
    (data.sourceProfile rank) (data.targetProfile rank) data.labels.mover
    observer weight hweight0 hweight1
    (data.targetProfile_eq_sourceProfile_of_ne rank)

end FinFourMovingMarkedPairMinimumSource

end GameTheory
