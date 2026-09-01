import MathUE.Topology.FiniteLabelSubsequence
import Research.Quitting.FinFourProducerAtlas.MinimumSingletonClockCompression
import Research.Quitting.FinFourProducerAtlas.PairedSameResidualSourceRegeneration
import UniformEquilibrium.Diagnostics.Quitting.FinFourPureTimeExactResponseCycleExternality
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.FinFourSignedRetraction
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.CommonPrefixTerminalLawStability
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.FinFourActualSourcePureTimeResponseAlternative
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticNearMinimumExactResponseChordCompactification

/-!
# Supplied cofinal Fin4 response cycles

This Research interface keeps the cofinal cycle choice explicit.  A cycle is
supplied for every retained tail; it is not inferred from the per-tail XOR.
The uniform-excess compiler attaches the checked signed retraction and its
exact paid-row alternative.  The near-minimum compiler below starts from one
already selected literal cycle edge and constructs its chord geometry only
after compactifying the actual finite chord profiles.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

/-- One supplied off-minimum response cycle for every cofinal tail of the
incoming minimum-source chronology. -/
structure FinFourCofinalOffMinimumResponseCycles
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (chronology : FinFourMinimumAtomChronology source) (M : ℝ) where
  tailStart : ℕ → ℕ
  tailStart_strictMono : StrictMono tailStart
  response : ∀ rank,
    FinFourActualSourcePureTimeResponseAlternative reward
      (fun offset ↦ chronology.profiles (tailStart rank + offset))
      (quittingTerminalSemanticDebtSum source.point.1) M
  cycle : ∀ rank, QuittingPureTimeOffMinimumExactResponseCycle reward
    (response rank).response.initial
    (quittingTerminalSemanticDebtSum source.point.1)
  cycle_end_le_1296 : ∀ rank,
    (cycle rank).start + (cycle rank).period ≤ 1296
  cycle_period_le_1296 : ∀ rank, (cycle rank).period ≤ 1296

namespace FinFourCofinalOffMinimumResponseCycles

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {chronology : FinFourMinimumAtomChronology source}

/-- The global source index selected inside the retained tail. -/
def globalSourceIndex
    (cycles : FinFourCofinalOffMinimumResponseCycles source chronology M)
    (rank : ℕ) : ℕ :=
  cycles.tailStart rank + (cycles.response rank).response.port.sourceIndex

/-- Every global retained index lies beyond its tail start. -/
theorem tailStart_le_globalSourceIndex
    (cycles : FinFourCofinalOffMinimumResponseCycles source chronology M)
    (rank : ℕ) :
    cycles.tailStart rank ≤ cycles.globalSourceIndex rank := by
  exact Nat.le_add_right _ _

/-- The selected global indices are cofinal, without claiming they are
strictly increasing before a further subsequence selection. -/
theorem globalSourceIndex_tendsto_atTop
    (cycles : FinFourCofinalOffMinimumResponseCycles source chronology M) :
    Tendsto cycles.globalSourceIndex atTop atTop := by
  apply Filter.tendsto_atTop_mono cycles.tailStart_le_globalSourceIndex
  exact cycles.tailStart_strictMono.tendsto_atTop

/-- The literal actual profile retained by one tail. -/
def retainedSourceProfile
    (cycles : FinFourCofinalOffMinimumResponseCycles source chronology M)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  chronology.profiles (cycles.globalSourceIndex rank)

/-- One displayed literal cycle vertex. -/
def cycleProfile
    (cycles : FinFourCofinalOffMinimumResponseCycles source chronology M)
    (rank offset : ℕ) : (quittingGame reward).BehaviorProfile :=
  (cycles.cycle rank).profile offset

/-- Every displayed cycle vertex is reached from the retained actual source
by literal complete-strategy replacements. -/
theorem retainedSource_to_cycleProfile
    (cycles : FinFourCofinalOffMinimumResponseCycles source chronology M)
    (rank offset : ℕ) :
    IsQuittingBehaviorReplacementAncestry
      (cycles.retainedSourceProfile rank) (cycles.cycleProfile rank offset) := by
  have h := (cycles.response rank).response.source_to_orbit_profile
    ((cycles.cycle rank).start + offset)
  simpa only [retainedSourceProfile, globalSourceIndex, cycleProfile,
    QuittingPureTimeOffMinimumExactResponseCycle.profile,
    QuittingPureTimeOffMinimumExactResponseCycle.state] using h

end FinFourCofinalOffMinimumResponseCycles

/-- A uniformly off-minimum selected vertex from every supplied cofinal
cycle.  The lower bound is literal and is not inferred from a limsup here. -/
structure FinFourUniformCycleExcessData
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    (cycles : FinFourCofinalOffMinimumResponseCycles source chronology M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  offset : ℕ → ℕ
  offset_le_period : ∀ rank, offset rank ≤ (cycles.cycle rank).period
  debt_excess_floor : ∀ rank, epsilon / 2 ≤
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (cycles.cycleProfile rank (offset rank))) -
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (cycles.retainedSourceProfile rank))

/-- The pointwise signed retractions and exact packet-normalized paid outputs
attached to a uniformly off-minimum supplied cycle family. -/
structure FinFourUniformCyclePaidRetraction
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    (data : FinFourUniformCycleExcessData cycles) where
  edge : ∀ rank, QuittingFinFourSignedRetraction
    (cycles.retainedSourceProfile rank)
    (cycles.cycleProfile rank (data.offset rank)) (data.epsilon / 2)
  paid : ∀ rank, QuittingFinFourUniformExcessPaidAlternative
    (M := M) (edge rank)

/-- The uniform selected vertices produce the exact signed paid retractions
at every retained rank. -/
theorem nonempty_finFourUniformCyclePaidRetraction
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    (data : FinFourUniformCycleExcessData cycles)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (FinFourUniformCyclePaidRetraction data) := by
  let edge : ∀ rank, QuittingFinFourSignedRetraction
      (cycles.retainedSourceProfile rank)
      (cycles.cycleProfile rank (data.offset rank)) (data.epsilon / 2) :=
    fun rank ↦ Classical.choice
      (nonempty_quittingFinFourSignedRetraction
        (cycles.retainedSourceProfile rank)
        (cycles.cycleProfile rank (data.offset rank)) (data.epsilon / 2)
        (data.debt_excess_floor rank))
  let paid : ∀ rank, QuittingFinFourUniformExcessPaidAlternative
      (M := M) (edge rank) := fun rank ↦ Classical.choice
    (nonempty_uniformExcessPaidAlternative (edge rank) hreward data.epsilon_pos)
  exact ⟨⟨edge, paid⟩⟩

/-- Finite label recording which paid arm occurs and the fixed player labels
on that arm. -/
inductive FinFourUniformPaidLabel
  | moverPaid (mover : Fin 4)
  | nonmoverPaid (mover observer : Fin 4)
  deriving DecidableEq, Fintype

namespace FinFourUniformCyclePaidRetraction

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {chronology : FinFourMinimumAtomChronology source}
  {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
  {data : FinFourUniformCycleExcessData cycles}

/-- The finite branch/player label of the exact paid output at one rank. -/
def label (result : FinFourUniformCyclePaidRetraction data) (rank : ℕ) :
    FinFourUniformPaidLabel :=
  match result.paid rank with
  | .moverPaid _ _ _ _ _ _ => .moverPaid (result.edge rank).mover
  | .nonmoverPaid observer _ _ _ _ _ _ _ =>
      .nonmoverPaid (result.edge rank).mover observer

end FinFourUniformCyclePaidRetraction

/-- A cofinal subsequence on which the exact paid arm, mover, and (when
present) nonmover observer are fixed.  The original exact row and all packet
constants remain available through `result.paid (subsequence rank)`. -/
structure FinFourUniformCycleFixedPaidRetraction
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    (data : FinFourUniformCycleExcessData cycles) where
  result : FinFourUniformCyclePaidRetraction data
  fixedLabel : FinFourUniformPaidLabel
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  label_eq : ∀ rank, result.label (subsequence rank) = fixedLabel

/-- Finite-label extraction makes the uniform paid arm literal on one cofinal
subsequence, including the fixed mover and fixed nonmover observer when that
branch occurs. -/
theorem nonempty_finFourUniformCycleFixedPaidRetraction
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    (data : FinFourUniformCycleExcessData cycles)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (FinFourUniformCycleFixedPaidRetraction data) := by
  obtain ⟨result⟩ := nonempty_finFourUniformCyclePaidRetraction data hreward
  obtain ⟨fixedLabel, subsequence, hsubsequence, hlabel⟩ :=
    Math.exists_fixed_label_on_strictMono_subsequence result.label
  exact ⟨⟨result, fixedLabel, subsequence, hsubsequence, hlabel⟩⟩

/-- The literal mover-paid data at one rank of a fixed mover-labelled
subsequence. The record repeats every quantitative constant so consumers do
not need to unfold the finite label encoding. -/
structure FinFourUniformCycleFixedMoverPaidRow
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    {data : FinFourUniformCycleExcessData cycles}
    (fixed : FinFourUniformCycleFixedPaidRetraction data)
    (mover : Fin 4) (rank : ℕ) where
  edge_mover_eq :
    (fixed.result.edge (fixed.subsequence rank)).mover = mover
  gainFloor : data.epsilon / 16 ≤
    (fixed.result.edge (fixed.subsequence rank)).reverseGain
  row : QuittingPaidFirstDisagreementRow reward
    (fixed.result.edge (fixed.subsequence rank)).moreOffMinimum
    (fixed.result.edge (fixed.subsequence rank)).mover (data.epsilon / 64)
  sourceWitness_mem : row.sourceWitness ∈
    (quittingBehaviorStoppingLaw reward
      ((fixed.result.edge (fixed.subsequence rank)).moreOffMinimum
        (fixed.result.edge (fixed.subsequence rank)).mover)).support
  ownSurvival_floor : data.epsilon / 16 ≤ 4 * M *
    quittingHazardSurvival
      (quittingBehaviorLiveHazard reward
        ((fixed.result.edge (fixed.subsequence rank)).moreOffMinimum
          (fixed.result.edge (fixed.subsequence rank)).mover)) row.start
  opponentReach_floor : data.epsilon / 16 ≤ 8 * M * row.liveMass
  jointReach_floor : (data.epsilon / 16) * (data.epsilon / 16) ≤
    32 * M * M * quittingSurvivalPrefix
      (quittingProfileLiveRoot reward
        (fixed.result.edge (fixed.subsequence rank)).moreOffMinimum) row.start

/-- The literal nonmover-paid data at one rank of a fixed mover/observer
subsequence, with every packet-normalized constant exposed directly. -/
structure FinFourUniformCycleFixedNonmoverPaidRow
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    {data : FinFourUniformCycleExcessData cycles}
    (fixed : FinFourUniformCycleFixedPaidRetraction data)
    (mover observer : Fin 4) (rank : ℕ) where
  edge_mover_eq :
    (fixed.result.edge (fixed.subsequence rank)).mover = mover
  observer_ne_mover : observer ≠
    (fixed.result.edge (fixed.subsequence rank)).mover
  observerDebt_floor : data.epsilon / 48 ≤
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (fixed.result.edge (fixed.subsequence rank)).moreOffMinimum) observer
  row : QuittingPaidFirstDisagreementRow reward
    (fixed.result.edge (fixed.subsequence rank)).moreOffMinimum
    observer (data.epsilon / 192)
  sourceWitness_mem : row.sourceWitness ∈
    (quittingBehaviorStoppingLaw reward
      ((fixed.result.edge (fixed.subsequence rank)).moreOffMinimum observer)).support
  ownSurvival_floor : data.epsilon / 48 ≤ 4 * M *
    quittingHazardSurvival
      (quittingBehaviorLiveHazard reward
        ((fixed.result.edge (fixed.subsequence rank)).moreOffMinimum observer))
      row.start
  opponentReach_floor : data.epsilon / 48 ≤ 8 * M * row.liveMass
  jointReach_floor : (data.epsilon / 48) * (data.epsilon / 48) ≤
    32 * M * M * quittingSurvivalPrefix
      (quittingProfileLiveRoot reward
        (fixed.result.edge (fixed.subsequence rank)).moreOffMinimum) row.start

namespace FinFourUniformCycleFixedPaidRetraction

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {chronology : FinFourMinimumAtomChronology source}
  {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
  {data : FinFourUniformCycleExcessData cycles}

/-- A mover label yields the literal mover-paid row and all exact constants
at every selected rank. -/
theorem moverPaidRow_of_fixedLabel_eq
    (fixed : FinFourUniformCycleFixedPaidRetraction data) (mover : Fin 4)
    (hfixed : fixed.fixedLabel = .moverPaid mover) (rank : ℕ) :
    Nonempty (FinFourUniformCycleFixedMoverPaidRow fixed mover rank) := by
  have hlabel := fixed.label_eq rank
  rw [hfixed] at hlabel
  generalize hpaid : fixed.result.paid (fixed.subsequence rank) = paid at hlabel ⊢
  cases paid with
  | moverPaid hgain row hsource hown hopponent hjoint =>
      simp only [FinFourUniformCyclePaidRetraction.label, hpaid] at hlabel
      injection hlabel with hmover
      exact ⟨{
        edge_mover_eq := hmover
        gainFloor := hgain
        row := row
        sourceWitness_mem := hsource
        ownSurvival_floor := hown
        opponentReach_floor := hopponent
        jointReach_floor := hjoint
      }⟩
  | nonmoverPaid observer hne hdebt row hsource hown hopponent hjoint =>
      simp only [FinFourUniformCyclePaidRetraction.label, hpaid] at hlabel
      exact FinFourUniformPaidLabel.noConfusion hlabel

/-- A nonmover label yields the literal fixed observer row and all exact
constants at every selected rank. -/
theorem nonmoverPaidRow_of_fixedLabel_eq
    (fixed : FinFourUniformCycleFixedPaidRetraction data)
    (mover observer : Fin 4)
    (hfixed : fixed.fixedLabel = .nonmoverPaid mover observer) (rank : ℕ) :
    Nonempty
      (FinFourUniformCycleFixedNonmoverPaidRow fixed mover observer rank) := by
  have hlabel := fixed.label_eq rank
  rw [hfixed] at hlabel
  generalize hpaid : fixed.result.paid (fixed.subsequence rank) = paid at hlabel ⊢
  cases paid with
  | moverPaid hgain row hsource hown hopponent hjoint =>
      simp only [FinFourUniformCyclePaidRetraction.label, hpaid] at hlabel
      exact FinFourUniformPaidLabel.noConfusion hlabel
  | nonmoverPaid selected hne hdebt row hsource hown hopponent hjoint =>
      simp only [FinFourUniformCyclePaidRetraction.label, hpaid] at hlabel
      have hmover :
          (fixed.result.edge (fixed.subsequence rank)).mover = mover :=
        (FinFourUniformPaidLabel.nonmoverPaid.inj hlabel).1
      have hobserver : selected = observer :=
        (FinFourUniformPaidLabel.nonmoverPaid.inj hlabel).2
      subst selected
      exact ⟨{
        edge_mover_eq := hmover
        observer_ne_mover := hne
        observerDebt_floor := hdebt
        row := row
        sourceWitness_mem := hsource
        ownSurvival_floor := hown
        opponentReach_floor := hopponent
        jointReach_floor := hjoint
      }⟩

end FinFourUniformCycleFixedPaidRetraction

namespace QuittingPureTimeOffMinimumExactResponseCycle

/-- One displayed cycle edge is literally a complete-strategy update by its
selected mover. -/
theorem profile_succ_eq_update
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {initial : QuittingPureTimeProfile (Fin 4)} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (offset : ℕ) :
    cycle.profile (offset + 1) =
      Function.update (cycle.profile offset) (cycle.mover offset)
        (cycle.profile (offset + 1) (cycle.mover offset)) := by
  change quittingPureTimeProfileBehavior reward
      (cycle.state (offset + 1)).toProfile =
    Function.update
      (quittingPureTimeProfileBehavior reward (cycle.state offset).toProfile)
      (cycle.step offset).mover
      (quittingPureTimeProfileBehavior reward
        (cycle.state (offset + 1)).toProfile (cycle.step offset).mover)
  rw [← cycle.step_target_eq_state_succ]
  rw [(cycle.step offset).target_profile_eq_update]
  rw [quittingPureTimeProfileBehavior_update]
  simp [state]

/-- The selected response attains the unrestricted behavioral cap on the
literal displayed source and target profiles. -/
theorem profile_succ_cap_attained
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {initial : QuittingPureTimeProfile (Fin 4)} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (offset : ℕ) :
    quittingTerminalPayoff reward (cycle.profile (offset + 1))
        (cycle.mover offset) =
      quittingContinuationBestResponseValue reward (cycle.profile offset)
        (cycle.mover offset) := by
  change quittingTerminalPayoff reward
      (quittingPureTimeProfileBehavior reward
        (cycle.state (offset + 1)).toProfile) (cycle.step offset).mover =
    quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward (cycle.state offset).toProfile)
      (cycle.step offset).mover
  rw [← cycle.step_target_eq_state_succ]
  exact (cycle.step offset).cap_attained

end QuittingPureTimeOffMinimumExactResponseCycle

/-- One fixed literal edge selected from the supplied cofinal cycles, with
both endpoints jointly compactified on the minimum fibre.  The finite rows
are not asserted to be minima. -/
structure FinFourNearMinimumCycleEdgeData
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    (cycles : FinFourCofinalOffMinimumResponseCycles source chronology M) where
  selector : ℕ → ℕ
  selector_strictMono : StrictMono selector
  offset : ℕ
  offset_succ_le_period : ∀ rank,
    offset + 1 ≤ (cycles.cycle (selector rank)).period
  mover : Fin 4
  mover_eq : ∀ rank,
    (cycles.cycle (selector rank)).mover offset = mover
  sourcePoint : QuittingTerminalSemanticLawPoint (Fin 4)
  targetPoint : QuittingTerminalSemanticLawPoint (Fin 4)
  sourcePoint_mem : sourcePoint ∈ quittingTerminalSemanticLawCarrier reward
  targetPoint_mem : targetPoint ∈ quittingTerminalSemanticLawCarrier reward
  source_tendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (cycles.cycleProfile (selector rank) offset),
        quittingTerminalOutcomeMass reward
          (cycles.cycleProfile (selector rank) offset)))
    atTop (nhds sourcePoint)
  target_tendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (cycles.cycleProfile (selector rank) (offset + 1)),
        quittingTerminalOutcomeMass reward
          (cycles.cycleProfile (selector rank) (offset + 1))))
    atTop (nhds targetPoint)
  sourceDebtSum_tendsto : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (cycles.cycleProfile (selector rank) offset)))
    atTop (nhds (quittingTerminalSemanticDebtSum source.point.1))
  targetDebtSum_tendsto : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (cycles.cycleProfile (selector rank) (offset + 1))))
    atTop (nhds (quittingTerminalSemanticDebtSum source.point.1))
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  mark : ℕ → ℕ
  target_stageMass_eq_one : ∀ rank,
    quittingStageCoalitionMass reward
      (cycles.cycleProfile (selector rank) (offset + 1))
      (mark rank) terminal = 1

namespace FinFourNearMinimumCycleEdgeData

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {chronology : FinFourMinimumAtomChronology source}
  {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}

/-- Literal source profile of the selected cycle edge. -/
def sourceProfile (data : FinFourNearMinimumCycleEdgeData cycles)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  cycles.cycleProfile (data.selector rank) data.offset

/-- Literal exact-response target profile of the selected cycle edge. -/
def targetProfile (data : FinFourNearMinimumCycleEdgeData cycles)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  cycles.cycleProfile (data.selector rank) (data.offset + 1)

/-- The target's actual complete behavioral strategy for the fixed mover. -/
def targetStrategy (data : FinFourNearMinimumCycleEdgeData cycles)
    (rank : ℕ) : (quittingGame reward).BehaviorStrategy data.mover :=
  data.targetProfile rank data.mover

/-- The selected target is literally the fixed mover's complete-strategy
update. -/
theorem targetProfile_eq_update
    (data : FinFourNearMinimumCycleEdgeData cycles) (rank : ℕ) :
    data.targetProfile rank = Function.update (data.sourceProfile rank)
      data.mover (data.targetStrategy rank) := by
  have h := (cycles.cycle (data.selector rank)).profile_succ_eq_update
    data.offset
  rw [data.mover_eq rank] at h
  exact h

/-- The literal target attains the source's unrestricted behavioral cap for
the fixed mover. -/
theorem cap_attained
    (data : FinFourNearMinimumCycleEdgeData cycles) (rank : ℕ) :
    quittingTerminalPayoff reward (data.targetProfile rank) data.mover =
      quittingContinuationBestResponseValue reward
        (data.sourceProfile rank) data.mover := by
  have h := (cycles.cycle (data.selector rank)).profile_succ_cap_attained
    data.offset
  rw [data.mover_eq rank] at h
  exact h

/-- The selected maximal-debt mover has the exact Fin4 average debt floor. -/
theorem source_moverDebt_floor
    (data : FinFourNearMinimumCycleEdgeData cycles) (rank : ℕ) :
    quittingTerminalSemanticDebtSum source.point.1 / 4 ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (data.sourceProfile rank))
        data.mover := by
  let cycle := cycles.cycle (data.selector rank)
  have h := (cycle.step data.offset).minimumDebt_div_card_le_source_mover_debt
    (quittingTerminalSemanticDebtSum source.point.1)
    (fun times ↦ source.minimum _
      (quittingTerminalSemanticPair_mem_carrier reward
        (quittingPureTimeProfileBehavior reward times)))
  change quittingTerminalSemanticDebtSum source.point.1 /
      Fintype.card (Fin 4) ≤
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (cycles.cycleProfile (data.selector rank) data.offset))
      ((cycles.cycle (data.selector rank)).mover data.offset) at h
  rw [data.mover_eq rank] at h
  change quittingTerminalSemanticDebtSum source.point.1 / 4 ≤
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (cycles.cycleProfile (data.selector rank) data.offset)) data.mover
  norm_num at h ⊢
  exact h

/-- Forget the cycle selection while retaining its literal actual endpoint
families and exact-response fields. -/
def exactResponseFamily
    (data : FinFourNearMinimumCycleEdgeData cycles) :
    QuittingNearMinimumExactResponseFamily reward where
  sourceProfile := data.sourceProfile
  targetProfile := data.targetProfile
  mover := data.mover
  targetStrategy := data.targetStrategy
  targetProfile_eq_update := data.targetProfile_eq_update
  cap_attained := data.cap_attained
  minimumDebt := quittingTerminalSemanticDebtSum source.point.1
  minimumDebt_pos := source.minimumDebt_pos
  sourcePoint := data.sourcePoint
  targetPoint := data.targetPoint
  sourcePoint_mem := data.sourcePoint_mem
  targetPoint_mem := data.targetPoint_mem
  source_tendsto := data.source_tendsto
  target_tendsto := data.target_tendsto
  minimum := source.minimum
  sourceDebtSum_tendsto := data.sourceDebtSum_tendsto
  targetDebtSum_tendsto := data.targetDebtSum_tendsto
  moverDebtFloor := quittingTerminalSemanticDebtSum source.point.1 / 4
  moverDebtFloor_pos := div_pos source.minimumDebt_pos (by norm_num)
  source_moverDebt_floor := data.source_moverDebt_floor

/-- The literal marked target atom is retained with mass one. -/
theorem target_stageMass_eq_one'
    (data : FinFourNearMinimumCycleEdgeData cycles) (rank : ℕ) :
    quittingStageCoalitionMass reward (data.targetProfile rank)
      (data.mark rank) data.terminal = 1 :=
  data.target_stageMass_eq_one rank

/-- The fixed target coalition has limiting complete-law mass one. -/
theorem targetPoint_terminalMass_eq_one
    (data : FinFourNearMinimumCycleEdgeData cycles) :
    data.targetPoint.2 (some data.terminal) = 1 := by
  have hlimit := (((continuous_apply (some data.terminal)).comp
    continuous_snd).tendsto data.targetPoint).comp data.target_tendsto
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  apply tendsto_nhds_unique hlimit
  apply hone.congr'
  filter_upwards [] with rank
  have hstage := data.target_stageMass_eq_one' rank
  have hle := quittingStageCoalitionMass_le_terminalOutcomeMass reward
    (data.targetProfile rank) (data.mark rank) data.terminal
  have hupper := terminalOutcomeMass_le_one
    (quittingTerminalOutcomeMass reward (data.targetProfile rank))
    (quittingTerminalOutcomeMass_mem_stdSimplex reward
      (data.targetProfile rank)) (some data.terminal)
  change 1 = quittingTerminalOutcomeMass reward (data.targetProfile rank)
    (some data.terminal)
  rw [hstage] at hle
  exact (le_antisymm hupper hle).symm

end FinFourNearMinimumCycleEdgeData

/-- The supplied selected edge family constructs its proper fixed-weight
minimum chord and derives the strict support child after compactification. -/
theorem nonempty_finFourNearMinimumCycleChordCompactification
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    (data : FinFourNearMinimumCycleEdgeData cycles)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    Nonempty (QuittingNearMinimumExactResponseChordCompactification
      data.exactResponseFamily weight hweight0 hweight1) :=
  nonempty_quittingNearMinimumExactResponseChordCompactification
    data.exactResponseFamily weight hweight0 hweight1

/-- The marked target atom survives in every actual chord profile with at
least the exact chord weight. -/
theorem finFourNearMinimumChord_stageMass_floor
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    (data : FinFourNearMinimumCycleEdgeData cycles)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (rank : ℕ) :
    weight ≤ quittingStageCoalitionMass reward
      (data.exactResponseFamily.fixedWeightChordProfile weight hweight0.le
        hweight1.le rank) (data.mark rank) data.terminal := by
  have haffine := quittingStageCoalitionMass_stoppingLawMixture_eq reward
    (data.exactResponseFamily.sourceProfile rank) data.mover
    (data.exactResponseFamily.sourceProfile rank data.mover)
    (data.exactResponseFamily.targetProfile rank data.mover)
    weight hweight0.le hweight1.le (data.mark rank) data.terminal
  rw [Function.update_eq_self,
    update_endpoint_with_response_observer_eq_response reward
      (data.exactResponseFamily.sourceProfile rank)
      (data.exactResponseFamily.targetProfile rank) data.mover
      (data.exactResponseFamily.targetProfile_eq_sourceProfile_of_ne rank)]
    at haffine
  change quittingStageCoalitionMass reward
      (data.exactResponseFamily.fixedWeightChordProfile weight hweight0.le
        hweight1.le rank) (data.mark rank) data.terminal = _ at haffine
  have htarget := data.target_stageMass_eq_one' rank
  change quittingStageCoalitionMass reward
      (data.exactResponseFamily.targetProfile rank) (data.mark rank)
      data.terminal = 1 at htarget
  rw [htarget] at haffine
  have hsource := quittingStageCoalitionMass_nonneg reward
    (data.exactResponseFamily.sourceProfile rank) (data.mark rank) data.terminal
  nlinarith

/-- The first source-regeneration input is the literal fixed-weight chord
family itself, retaining the packet's original moving marked dates. -/
def finFourNearMinimumChordSourceData
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    (data : FinFourNearMinimumCycleEdgeData cycles)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (compactification : QuittingNearMinimumExactResponseChordCompactification
      data.exactResponseFamily weight hweight0 hweight1) :
    FinFourPairedMinimumSourceData source where
  targetPoint := compactification.chordPoint
  targetPoint_mem := compactification.chordPoint_mem
  targetDebtSum_eq_source := by
    rw [← compactification.geometry_chord_eq,
      compactification.geometry.chord_debtSum_eq_endpoint,
      compactification.geometry_endpoint_eq,
      data.exactResponseFamily.sourcePoint_debtSum_eq_minimumDebt]
    rfl
  terminal := data.terminal
  sourceProfiles := fun rank ↦
    data.exactResponseFamily.sourceProfile
      (compactification.refinement rank)
  targetProfiles := fun rank ↦
    data.exactResponseFamily.fixedWeightChordProfile weight hweight0.le
      hweight1.le (compactification.refinement rank)
  selector := id
  selector_strictMono := strictMono_id
  mover := data.mover
  response := fun rank ↦
    data.exactResponseFamily.fixedWeightChordProfile weight hweight0.le
      hweight1.le (compactification.refinement rank) data.mover
  target_eq_update := by
    intro rank
    simp only [id_eq]
    symm
    apply update_endpoint_with_response_observer_eq_response
    intro other hother
    have hother' : other ≠ data.exactResponseFamily.mover := hother
    unfold QuittingNearMinimumExactResponseFamily.fixedWeightChordProfile
    unfold quittingResponseChordProfile
    rw [Function.update_of_ne hother']
  mark := fun rank ↦ data.mark (compactification.refinement rank)
  massFloor := weight
  massFloor_pos := hweight0
  marked_mass_floor := by
    intro rank
    simpa only [id_eq] using finFourNearMinimumChord_stageMass_floor data
      weight hweight0 hweight1 (compactification.refinement rank)
  target_tendsto := by
    simpa only [id_eq] using compactification.chord_tendsto

/-- The literal chord profiles therefore admit a source-faithful chronology
at the compactified interior minimum point, with the incoming residual kept
separate from this construction. -/
theorem nonempty_finFourNearMinimumChordSourceChronology
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    (data : FinFourNearMinimumCycleEdgeData cycles)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (compactification : QuittingNearMinimumExactResponseChordCompactification
      data.exactResponseFamily weight hweight0 hweight1) :
    Nonempty (FinFourPairedSameResidualSourceRegeneration
      (finFourNearMinimumChordSourceData data weight hweight0 hweight1
        compactification)) :=
  nonempty_finFourPairedSameResidualSourceRegeneration
    (finFourNearMinimumChordSourceData data weight hweight0 hweight1
      compactification)

private theorem quittingLiteralRootStackProfile_apply_eq_of_tail
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (roots : List (Fin 4 → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile) (who : Fin 4)
    (htail : first who = second who) :
    quittingLiteralRootStackProfile reward roots first who =
      quittingLiteralRootStackProfile reward roots second who := by
  induction roots with
  | nil => simpa
  | cons root roots ih =>
      simp only [quittingLiteralRootStackProfile_cons]
      funext time history
      cases time with
      | zero => rfl
      | succ time => exact congrFun (congrFun ih time) _

private theorem quittingLiteralRootStackProfile_eq_update_of_suffix_update
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (roots : List (Fin 4 → PMF Bool))
    (source target : (quittingGame reward).BehaviorProfile) (mover : Fin 4)
    (htarget : target = Function.update source mover (target mover)) :
    quittingLiteralRootStackProfile reward roots target =
      Function.update (quittingLiteralRootStackProfile reward roots source)
    mover (quittingLiteralRootStackProfile reward roots target mover) := by
  symm
  apply update_endpoint_with_response_observer_eq_response
  intro other hother
  apply quittingLiteralRootStackProfile_apply_eq_of_tail
  rw [htarget, Function.update_of_ne hother]

/-- Literal decomposition of the nonempty causal word used at the first
chord source.  This is the only additional common-prefix input. -/
structure FinFourNearMinimumCopiedPrefixData
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    {data : FinFourNearMinimumCycleEdgeData cycles}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    {compactification :
      QuittingNearMinimumExactResponseChordCompactification
        data.exactResponseFamily weight hweight0 hweight1}
    (chordRegeneration :
      FinFourPairedSameResidualSourceRegeneration
        (finFourNearMinimumChordSourceData data weight hweight0 hweight1
          compactification)) where
  head : ℕ → Fin 4 → PMF Bool
  tail : ℕ → List (Fin 4 → PMF Bool)
  roots_eq : ∀ rank, chordRegeneration.causalization.roots rank =
    head rank :: tail rank
  selector : ℕ → ℕ
  selector_strictMono : StrictMono selector
  shiftedTargetMass_floor : ∀ rank, weight / 2 ≤
    quittingStageCoalitionMass reward
      (quittingLiteralRootStackProfile reward
        (chordRegeneration.causalization.roots (selector rank))
        (data.exactResponseFamily.targetProfile
          (compactification.refinement (selector rank))))
      ((chordRegeneration.causalization.roots (selector rank)).length +
        data.mark (compactification.refinement (selector rank))) data.terminal

/-- The causalization words all have positive length, so the literal head-tail
decomposition required by unrestricted-cap transport is always available. -/
theorem nonempty_finFourNearMinimumCopiedPrefixData
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    {data : FinFourNearMinimumCycleEdgeData cycles}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    {compactification :
      QuittingNearMinimumExactResponseChordCompactification
        data.exactResponseFamily weight hweight0 hweight1}
    (chordRegeneration :
      FinFourPairedSameResidualSourceRegeneration
        (finFourNearMinimumChordSourceData data weight hweight0 hweight1
          compactification)) :
    Nonempty (FinFourNearMinimumCopiedPrefixData chordRegeneration) := by
  have hdecompose : ∀ rank, ∃ head tail,
      chordRegeneration.causalization.roots rank = head :: tail := by
    intro rank
    cases hroots : chordRegeneration.causalization.roots rank with
    | nil =>
        have hlength := chordRegeneration.causalization.roots_length rank
        rw [hroots] at hlength
        simp at hlength
    | cons head tail => exact ⟨head, tail, rfl⟩
  choose head tail hroots using hdecompose
  have htargetEventually : ∀ᶠ rank in atTop, weight / 2 ≤
      quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward
          (chordRegeneration.causalization.roots rank)
          (data.exactResponseFamily.targetProfile
            (compactification.refinement rank)))
        ((chordRegeneration.causalization.roots rank).length +
          data.mark (compactification.refinement rank)) data.terminal := by
    filter_upwards [chordRegeneration.causalization.eventually_shifted_mark_mass_floor]
      with rank hchordFloor
    have hlength := chordRegeneration.causalization.roots_length rank
    change weight / 2 ≤ quittingStageCoalitionMass reward
      (quittingLiteralRootStackProfile reward
        (chordRegeneration.causalization.roots rank)
        (data.exactResponseFamily.fixedWeightChordProfile weight hweight0.le
          hweight1.le (compactification.refinement rank)))
      (rank + 1 + data.mark (compactification.refinement rank)) data.terminal
      at hchordFloor
    rw [← hlength] at hchordFloor
    have hchordTransport :=
      quittingStageCoalitionMass_literalRootStack_add_length reward
        (chordRegeneration.causalization.roots rank)
        (data.exactResponseFamily.fixedWeightChordProfile weight hweight0.le
          hweight1.le (compactification.refinement rank))
        (data.mark (compactification.refinement rank)) data.terminal
    have htargetTransport :=
      quittingStageCoalitionMass_literalRootStack_add_length reward
        (chordRegeneration.causalization.roots rank)
        (data.exactResponseFamily.targetProfile
          (compactification.refinement rank))
        (data.mark (compactification.refinement rank)) data.terminal
    have htargetStage := data.target_stageMass_eq_one'
      (compactification.refinement rank)
    change quittingStageCoalitionMass reward
      (data.exactResponseFamily.targetProfile (compactification.refinement rank))
      (data.mark (compactification.refinement rank)) data.terminal = 1
      at htargetStage
    have hchordStageLe : quittingStageCoalitionMass reward
        (data.exactResponseFamily.fixedWeightChordProfile weight hweight0.le
          hweight1.le (compactification.refinement rank))
        (data.mark (compactification.refinement rank)) data.terminal ≤ 1 := by
      exact (quittingStageCoalitionMass_le_terminalOutcomeMass reward _ _ _).trans
        (terminalOutcomeMass_le_one _
          (quittingTerminalOutcomeMass_mem_stdSimplex reward _) _)
    have hproduct := quittingCapNashStackContinueProduct_nonneg
      (chordRegeneration.causalization.roots rank)
    rw [hchordTransport] at hchordFloor
    rw [htargetTransport, htargetStage]
    exact hchordFloor.trans (by nlinarith)
  obtain ⟨selector, hselector, hselected⟩ :=
    extraction_of_eventually_atTop htargetEventually
  exact ⟨⟨head, tail, hroots, selector, hselector, hselected⟩⟩

namespace FinFourNearMinimumCopiedPrefixData

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {chronology : FinFourMinimumAtomChronology source}
  {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
  {data : FinFourNearMinimumCycleEdgeData cycles}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
  {compactification :
    QuittingNearMinimumExactResponseChordCompactification
      data.exactResponseFamily weight hweight0 hweight1}
  {chordRegeneration :
    FinFourPairedSameResidualSourceRegeneration
      (finFourNearMinimumChordSourceData data weight hweight0 hweight1
        compactification)}

/-- The actual chord suffix used by the first causalization. -/
def chordProfile (_copied : FinFourNearMinimumCopiedPrefixData chordRegeneration)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  data.exactResponseFamily.fixedWeightChordProfile weight hweight0.le
    hweight1.le (compactification.refinement rank)

/-- The corresponding actual exact-response target suffix. -/
def targetProfile (_copied : FinFourNearMinimumCopiedPrefixData chordRegeneration)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  data.exactResponseFamily.targetProfile (compactification.refinement rank)

/-- The chord endpoint with the exact first causal word copied in front. -/
def prefixedChordProfile
    (copied : FinFourNearMinimumCopiedPrefixData chordRegeneration)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward
    (chordRegeneration.causalization.roots rank) (copied.chordProfile rank)

/-- The target endpoint with the same exact first causal word copied in
front. -/
def prefixedTargetProfile
    (copied : FinFourNearMinimumCopiedPrefixData chordRegeneration)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward
    (chordRegeneration.causalization.roots rank) (copied.targetProfile rank)

/-- Copying the first causal word retains the literal unilateral response
edge from the chord suffix to the target suffix. -/
theorem prefixedTargetProfile_eq_update
    (copied : FinFourNearMinimumCopiedPrefixData chordRegeneration)
    (rank : ℕ) :
    copied.prefixedTargetProfile rank =
      Function.update (copied.prefixedChordProfile rank) data.mover
        (copied.prefixedTargetProfile rank data.mover) := by
  apply quittingLiteralRootStackProfile_eq_update_of_suffix_update
  symm
  apply update_endpoint_with_response_observer_eq_response
  intro other hother
  have htarget := data.exactResponseFamily.targetProfile_eq_sourceProfile_of_ne
    (compactification.refinement rank) other hother
  change data.exactResponseFamily.targetProfile
      (compactification.refinement rank) other =
    data.exactResponseFamily.fixedWeightChordProfile weight hweight0.le
      hweight1.le (compactification.refinement rank) other
  rw [htarget]
  unfold QuittingNearMinimumExactResponseFamily.fixedWeightChordProfile
  unfold quittingResponseChordProfile
  have hother' : other ≠ data.exactResponseFamily.mover := hother
  rw [Function.update_of_ne hother']

/-- Joint survival through the copied causal words tends to one. -/
theorem jointSurvival_tendsto_one
    (_copied : FinFourNearMinimumCopiedPrefixData chordRegeneration) :
    Tendsto (fun rank ↦ quittingLiteralRootStackJointSurvival
      (chordRegeneration.causalization.roots rank)) atTop (nhds 1) := by
  simpa only [quittingLiteralRootStackJointSurvival,
    quittingCapNashStackContinueProduct] using
      chordRegeneration.causalization.continueProduct_tendsto_one

/-- The copied-prefix target family still converges jointly to the literal
minimum target law point.  This uses complete-law, prescribed-payoff, and
unrestricted-cap transport, including Never and arbitrarily late responses. -/
theorem prefixedTarget_tendsto
    (copied : FinFourNearMinimumCopiedPrefixData chordRegeneration) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward (copied.prefixedTargetProfile rank),
        quittingTerminalOutcomeMass reward (copied.prefixedTargetProfile rank)))
      atTop (nhds data.targetPoint) := by
  have hsuffix := compactification.target_tendsto
  have hsuffixLaw := continuous_snd.tendsto data.targetPoint |>.comp hsuffix
  have hprefixedLaw :=
    tendsto_quittingTerminalOutcomeMass_literalRootStack_of_joint reward
      chordRegeneration.causalization.roots copied.targetProfile
      data.targetPoint.2 copied.jointSurvival_tendsto_one hsuffixLaw
  have hprefixedPayoff : Tendsto (fun rank ↦
      fun who ↦ quittingTerminalPayoff reward
        (copied.prefixedTargetProfile rank) who)
      atTop (nhds data.targetPoint.1.1) := by
    have hmoment :=
      (continuous_quittingTerminalRewardMoment reward).tendsto
        data.targetPoint.2 |>.comp hprefixedLaw
    convert hmoment using 1
    · funext rank
      exact (quittingTerminalRewardMoment_outcomeMass reward
        (copied.prefixedTargetProfile rank)).symm
    · have hpointMoment :
          quittingTerminalRewardMoment reward data.targetPoint.2 =
            data.targetPoint.1.1 := by
        have hcarrier :=
          terminalSemanticLawCarrier_rewardMoment reward
            data.targetPoint data.targetPoint_mem
        exact hcarrier
      rw [hpointMoment]
  have hprefixedCap : Tendsto (fun rank ↦
      fun who ↦ quittingContinuationBestResponseValue reward
        (copied.prefixedTargetProfile rank) who)
      atTop (nhds data.targetPoint.1.2) := by
    apply tendsto_pi_nhds.mpr
    intro who
    have hsuffixPair := continuous_fst.tendsto data.targetPoint |>.comp hsuffix
    have hsuffixCap := ((continuous_apply who).comp continuous_snd).tendsto
      data.targetPoint.1 |>.comp hsuffixPair
    have hsemantic := terminalSemanticLawCarrier_fst_mem_carrier
      data.targetPoint data.targetPoint_mem
    have htargetDebt : quittingTerminalSemanticDebtSum data.targetPoint.1 =
        quittingTerminalSemanticDebtSum source.point.1 := by
      simpa only [FinFourNearMinimumCycleEdgeData.exactResponseFamily] using
        data.exactResponseFamily.targetPoint_debtSum_eq_minimumDebt
    have hmargin := minimumTerminalSemantic_singletonMargin
      data.targetPoint.1 hsemantic
      (fun candidate hcandidate ↦ by
        rw [htargetDebt]
        exact source.minimum candidate hcandidate)
      (by rw [htargetDebt]; exact source.minimumDebt_pos) who
    have hmoat : reward (quittingSingletonTerminal who) who <
        data.targetPoint.1.2 who := by
      have hpositive : 0 <
          quittingTerminalSemanticDebtSum data.targetPoint.1 := by
        rw [htargetDebt]
        exact source.minimumDebt_pos
      linarith
    have hcap :=
      tendsto_quittingContinuationBestResponseValue_literalRootStack_of_joint
        reward copied.head copied.tail copied.targetProfile who
        (data.targetPoint.1.2 who) (by
          simpa only [← copied.roots_eq] using
            copied.jointSurvival_tendsto_one) hsuffixCap hmoat
    simpa only [prefixedTargetProfile, copied.roots_eq] using hcap
  have hprefixedPair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward (copied.prefixedTargetProfile rank))
      atTop (nhds data.targetPoint.1) := by
    rw [← Prod.eta data.targetPoint.1]
    simpa only [quittingTerminalSemanticPair, nhds_prod_eq] using
      hprefixedPayoff.prodMk hprefixedCap
  rw [← Prod.eta data.targetPoint]
  change Tendsto (fun rank ↦
    (quittingTerminalSemanticPair reward (copied.prefixedTargetProfile rank),
      quittingTerminalOutcomeMass reward (copied.prefixedTargetProfile rank)))
    atTop (nhds (data.targetPoint.1, data.targetPoint.2))
  simpa only [nhds_prod_eq, prefixedTargetProfile] using
    hprefixedPair.prodMk hprefixedLaw

end FinFourNearMinimumCopiedPrefixData

/-- The second source-regeneration input keeps the copied prefix and the
literal exact-response edge from the chord endpoint to the target endpoint.
Its marked dates are the selected shifted dates, not dates reconstructed from
the limiting law alone. -/
def finFourNearMinimumTargetSourceData
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    {data : FinFourNearMinimumCycleEdgeData cycles}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    {compactification :
      QuittingNearMinimumExactResponseChordCompactification
        data.exactResponseFamily weight hweight0 hweight1}
    {chordRegeneration :
      FinFourPairedSameResidualSourceRegeneration
        (finFourNearMinimumChordSourceData data weight hweight0 hweight1
          compactification)}
    (copied : FinFourNearMinimumCopiedPrefixData chordRegeneration) :
    FinFourPairedMinimumSourceData chordRegeneration.next where
  targetPoint := data.targetPoint
  targetPoint_mem := data.targetPoint_mem
  targetDebtSum_eq_source := by
    change quittingTerminalSemanticDebtSum data.targetPoint.1 =
      quittingTerminalSemanticDebtSum compactification.chordPoint.1
    rw [← compactification.geometry_chord_eq,
      compactification.geometry.chord_debtSum_eq_endpoint,
      compactification.geometry_endpoint_eq]
    change quittingTerminalSemanticDebtSum
        data.exactResponseFamily.targetPoint.1 =
      quittingTerminalSemanticDebtSum data.exactResponseFamily.sourcePoint.1
    rw [data.exactResponseFamily.targetPoint_debtSum_eq_minimumDebt,
      data.exactResponseFamily.sourcePoint_debtSum_eq_minimumDebt]
  terminal := data.terminal
  sourceProfiles := copied.prefixedChordProfile
  targetProfiles := copied.prefixedTargetProfile
  selector := copied.selector
  selector_strictMono := copied.selector_strictMono
  mover := data.mover
  response := fun rank ↦ copied.prefixedTargetProfile rank data.mover
  target_eq_update := by
    intro rank
    exact copied.prefixedTargetProfile_eq_update (copied.selector rank)
  mark := fun rank ↦
    (chordRegeneration.causalization.roots rank).length +
      data.mark (compactification.refinement rank)
  massFloor := weight / 2
  massFloor_pos := div_pos hweight0 (by norm_num)
  marked_mass_floor := copied.shiftedTargetMass_floor
  target_tendsto := copied.prefixedTarget_tendsto.comp
    copied.selector_strictMono.tendsto_atTop

/-- The copied-prefix target family therefore regenerates the exact target
minimum with the incoming residual unchanged and retains its literal paired
response chronology. -/
theorem nonempty_finFourNearMinimumTargetSourceRegeneration
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    {data : FinFourNearMinimumCycleEdgeData cycles}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    {compactification :
      QuittingNearMinimumExactResponseChordCompactification
        data.exactResponseFamily weight hweight0 hweight1}
    {chordRegeneration :
      FinFourPairedSameResidualSourceRegeneration
        (finFourNearMinimumChordSourceData data weight hweight0 hweight1
          compactification)}
    (copied : FinFourNearMinimumCopiedPrefixData chordRegeneration) :
    Nonempty (FinFourPairedSameResidualSourceRegeneration
      (finFourNearMinimumTargetSourceData copied)) :=
  nonempty_finFourPairedSameResidualSourceRegeneration
    (finFourNearMinimumTargetSourceData copied)

/-- Complete near-minimum output: both the interior chord source and the
strict target child are source-faithful minimum producers with the original
hard residual, connected by the literal copied-prefix response edge. -/
structure FinFourNearMinimumCycleSourceRegeneration
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    (data : FinFourNearMinimumCycleEdgeData cycles)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) where
  compactification : QuittingNearMinimumExactResponseChordCompactification
    data.exactResponseFamily weight hweight0 hweight1
  chordRegeneration : FinFourPairedSameResidualSourceRegeneration
    (finFourNearMinimumChordSourceData data weight hweight0 hweight1
      compactification)
  copiedPrefix : FinFourNearMinimumCopiedPrefixData chordRegeneration
  targetRegeneration : FinFourPairedSameResidualSourceRegeneration
    (finFourNearMinimumTargetSourceData copiedPrefix)

namespace FinFourNearMinimumCycleSourceRegeneration

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {chronology : FinFourMinimumAtomChronology source}
  {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
  {data : FinFourNearMinimumCycleEdgeData cycles}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}

/-- The regenerated target producer. -/
def targetProducer
    (result : FinFourNearMinimumCycleSourceRegeneration
      data weight hweight0 hweight1) :
    FinFourMinimumAtomProducer reward bound :=
  result.targetRegeneration.next

@[simp] theorem targetProducer_point_eq
    (result : FinFourNearMinimumCycleSourceRegeneration
      data weight hweight0 hweight1) :
    result.targetProducer.point = data.targetPoint := rfl

@[simp] theorem targetProducer_residual_eq
    (result : FinFourNearMinimumCycleSourceRegeneration
      data weight hweight0 hweight1) :
    result.targetProducer.residual = source.residual := rfl

/-- The child target has nonempty strict support of cardinality at most three. -/
theorem targetSupport_nonempty_card_le_three_and_strict
    (result : FinFourNearMinimumCycleSourceRegeneration
      data weight hweight0 hweight1) :
    (quittingPositiveDebtSupport data.targetPoint.1).Nonempty ∧
      (quittingPositiveDebtSupport data.targetPoint.1).card ≤ 3 ∧
      quittingPositiveDebtSupport data.targetPoint.1 ⊂
        quittingPositiveDebtSupport result.compactification.chordPoint.1 := by
  exact ⟨result.compactification.targetSupport_nonempty_and_card_le_three.1,
    result.compactification.targetSupport_nonempty_and_card_le_three.2,
    result.compactification.targetSupport_ssubset_chordSupport⟩

/-- The second paired chronology retains the literal complete-strategy
replacement from the copied chord profile to the copied target profile. -/
theorem targetChronology_eq_update
    (result : FinFourNearMinimumCycleSourceRegeneration
      data weight hweight0 hweight1) (rank : ℕ) :
    result.copiedPrefix.prefixedTargetProfile
        (result.copiedPrefix.selector rank) =
      Function.update
        (result.copiedPrefix.prefixedChordProfile
          (result.copiedPrefix.selector rank)) data.mover
        (result.copiedPrefix.prefixedTargetProfile
          (result.copiedPrefix.selector rank) data.mover) :=
  result.copiedPrefix.prefixedTargetProfile_eq_update _

end FinFourNearMinimumCycleSourceRegeneration

/-- The supplied near-minimum edge produces the two-step source-faithful
minimum regeneration with a strict Fin4 support child. -/
theorem nonempty_finFourNearMinimumCycleSourceRegeneration
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    (data : FinFourNearMinimumCycleEdgeData cycles)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    Nonempty (FinFourNearMinimumCycleSourceRegeneration
      data weight hweight0 hweight1) := by
  obtain ⟨compactification⟩ :=
    nonempty_finFourNearMinimumCycleChordCompactification
      data weight hweight0 hweight1
  obtain ⟨chordRegeneration⟩ :=
    nonempty_finFourNearMinimumChordSourceChronology
      data weight hweight0 hweight1 compactification
  obtain ⟨copiedPrefix⟩ :=
    nonempty_finFourNearMinimumCopiedPrefixData chordRegeneration
  obtain ⟨targetRegeneration⟩ :=
    nonempty_finFourNearMinimumTargetSourceRegeneration copiedPrefix
  exact ⟨⟨compactification, chordRegeneration, copiedPrefix,
    targetRegeneration⟩⟩

/-! The final compiler deliberately accepts the selected asymptotic branch
as data.  The pointwise XOR does not by itself choose one cofinal branch. -/

/-- Supplied selected branch for a cofinal response-cycle family. -/
inductive FinFourSelectedCycleContractionBranch
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    (cycles : FinFourCofinalOffMinimumResponseCycles source chronology M) where
  | uniformExcess (data : FinFourUniformCycleExcessData cycles)
  | nearMinimum (data : FinFourNearMinimumCycleEdgeData cycles)
      (weight : ℝ) (weight_pos : 0 < weight) (weight_lt_one : weight < 1)

/-- Exact output of the selected supplied branch. -/
inductive FinFourSelectedCycleContractionResult
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M} :
    FinFourSelectedCycleContractionBranch cycles → Type
  | uniformExcess {data : FinFourUniformCycleExcessData cycles}
      (result : FinFourUniformCycleFixedPaidRetraction data) :
      FinFourSelectedCycleContractionResult (.uniformExcess data)
  | nearMinimum {data : FinFourNearMinimumCycleEdgeData cycles}
      {weight : ℝ} {weight_pos : 0 < weight} {weight_lt_one : weight < 1}
      (result : FinFourNearMinimumCycleSourceRegeneration
        data weight weight_pos weight_lt_one) :
      FinFourSelectedCycleContractionResult
        (.nearMinimum data weight weight_pos weight_lt_one)

/-- Every explicitly selected cycle-contraction branch has its exact checked
paid-retraction or strict-support regeneration output. -/
theorem nonempty_finFourSelectedCycleContractionResult
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {chronology : FinFourMinimumAtomChronology source}
    {cycles : FinFourCofinalOffMinimumResponseCycles source chronology M}
    (branch : FinFourSelectedCycleContractionBranch cycles)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (FinFourSelectedCycleContractionResult branch) := by
  cases branch with
  | uniformExcess data =>
      obtain ⟨result⟩ :=
        nonempty_finFourUniformCycleFixedPaidRetraction data hreward
      exact ⟨FinFourSelectedCycleContractionResult.uniformExcess result⟩
  | nearMinimum data weight weight_pos weight_lt_one =>
      obtain ⟨result⟩ := nonempty_finFourNearMinimumCycleSourceRegeneration
        data weight weight_pos weight_lt_one
      exact ⟨FinFourSelectedCycleContractionResult.nearMinimum result⟩

end GameTheory
