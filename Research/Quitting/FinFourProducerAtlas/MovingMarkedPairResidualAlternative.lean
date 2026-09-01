import MathUE.Topology.NonnegativeSubsequenceDichotomy
import Research.Quitting.FinFourProducerAtlas.MovingMarkedPairSource
import UniformEquilibrium.Quitting.Paths.BehaviorSupportedPureTimeReplacement

/-!
# Residual and target-excess alternatives for a moving marked pair

This module performs the two explicit strict-subsequence selections in the
moving marked-pair argument.  The positive-residual arm retains its literal
strictly earlier paid row and cap-port dispatch.  The other arms retain the
same composed selector for every profile, mark, reach, residual, and excess.

The final minimum approach is only an input to later compactification.  No
minimum chord, source regeneration, renewal, or equilibrium follows here.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- One selected positive-residual row with its literal paid first
disagreement and cap-port dispatch at the separately supplied minimum. -/
structure FinFourMovingMarkedPairStrictEarlierPaidPortAt
    (data : FinFourMovingMarkedPairMinimumSource source)
    (M : ℝ) (rank : ℕ) where
  paid : QuittingActualReachedScreenedEndpointMark.StrictEarlierPaidRow
    (data.marked rank) M
  capSource : QuittingPaidCapLiftedSource reward
  port : capSource.SummablePort
  minimum_eq : capSource.minimum = source.point.1
  profile_eq : capSource.profile = data.targetProfile rank
  observer_eq : capSource.observer = data.labels.mover
  gain_eq : capSource.gain = data.premarkResidual rank / 4
  row_eq : HEq capSource.row paid.row
  dispatch : capSource.ChargedNearReturn port ∨
    capSource.QuantitativeDebtDescent port ∨ capSource.InertStall port

/-- A positive residual at one literal marked row yields the complete
strict-earlier paid-port certificate. -/
theorem nonempty_finFourMovingMarkedPairStrictEarlierPaidPortAt
    (data : FinFourMovingMarkedPairMinimumSource source)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (rank : ℕ) (hresidual : 0 < data.premarkResidual rank) :
    Nonempty (FinFourMovingMarkedPairStrictEarlierPaidPortAt data M rank) := by
  obtain ⟨paid, capSource, port, hminimum, _hminimumMem, hprofile,
      hobserver, hgain, hrow, hdispatch⟩ :=
    (data.marked rank).exists_strictEarlierPaidRow_and_capPortTrichotomy
      M hreward (by simpa only [FinFourMovingMarkedPairMinimumSource.premarkResidual]
        using hresidual) source.point.1 source.semantic_mem source.minimum
        source.minimumDebt_pos
  refine ⟨{
    paid := paid
    capSource := capSource
    port := port
    minimum_eq := hminimum
    profile_eq := hprofile
    observer_eq := ?_
    gain_eq := ?_
    row_eq := hrow
    dispatch := hdispatch }⟩
  · exact hobserver.trans (data.marked_mover_eq rank)
  · simpa only [FinFourMovingMarkedPairMinimumSource.premarkResidual] using hgain

/-- A strict moving-family subsequence with one uniform positive premark
residual floor and its complete paid-port certificate at every row. -/
structure FinFourMovingMarkedPairPositiveResidual
    (data : FinFourMovingMarkedPairMinimumSource source) (M : ℝ) where
  select : ℕ → ℕ
  select_strictMono : StrictMono select
  residualFloor : ℝ
  residualFloor_pos : 0 < residualFloor
  residualFloor_le : ∀ rank,
    residualFloor ≤ data.premarkResidual (select rank)
  certificate : ∀ rank,
    FinFourMovingMarkedPairStrictEarlierPaidPortAt data M (select rank)

/-- A strict moving-family subsequence on which the premark residual
vanishes. -/
structure FinFourMovingMarkedPairVanishingResidual
    (data : FinFourMovingMarkedPairMinimumSource source) where
  select : ℕ → ℕ
  select_strictMono : StrictMono select
  residual_tendsto_zero : Tendsto (data.premarkResidual ∘ select)
    atTop (nhds 0)

/-- The exhaustive strict-subsequence split of the nonnegative premark
residual. -/
inductive FinFourMovingMarkedPairResidualAlternative
    (data : FinFourMovingMarkedPairMinimumSource source) (M : ℝ) : Type
  | positive
      (result : FinFourMovingMarkedPairPositiveResidual data M)
  | vanishing
      (result : FinFourMovingMarkedPairVanishingResidual data)

/-- The supplied moving family has either a uniform positive-residual paid
port or a strict subsequence with vanishing residual. -/
theorem nonempty_finFourMovingMarkedPairResidualAlternative
    (data : FinFourMovingMarkedPairMinimumSource source)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (FinFourMovingMarkedPairResidualAlternative data M) := by
  have hnonneg : ∀ rank, 0 ≤ data.premarkResidual rank := by
    intro rank
    rw [← data.target_mover_debt_eq_premarkResidual rank]
    exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      (quittingTerminalSemanticPair_mem_carrier reward (data.targetProfile rank))
      data.labels.mover
  obtain ⟨alternative⟩ :=
    Math.nonempty_nonnegativeSubsequenceAlternative data.premarkResidual hnonneg
  cases alternative with
  | positiveFloor select hselect floor hfloor hselected =>
      let certificate : ∀ rank,
          FinFourMovingMarkedPairStrictEarlierPaidPortAt data M (select rank) :=
        fun rank ↦ Classical.choice
          (nonempty_finFourMovingMarkedPairStrictEarlierPaidPortAt
            data M hreward (select rank) (hfloor.trans_le (hselected rank)))
      exact ⟨.positive {
        select := select
        select_strictMono := hselect
        residualFloor := floor
        residualFloor_pos := hfloor
        residualFloor_le := hselected
        certificate := certificate }⟩
  | vanishing select hselect htendsto =>
      exact ⟨.vanishing {
        select := select
        select_strictMono := hselect
        residual_tendsto_zero := htendsto }⟩

/-- On a vanishing-residual subsequence, a further strict refinement keeps
the target total-debt excess uniformly above one positive margin. -/
structure FinFourMovingMarkedPairOffMinimumEndpoint
    {data : FinFourMovingMarkedPairMinimumSource source}
    (residual : FinFourMovingMarkedPairVanishingResidual data) where
  refinement : ℕ → ℕ
  refinement_strictMono : StrictMono refinement
  excessFloor : ℝ
  excessFloor_pos : 0 < excessFloor
  excessFloor_le : ∀ rank, excessFloor ≤
    data.targetDebtExcess (residual.select (refinement rank))

/-- On a vanishing-residual subsequence, a further strict refinement also
has target total-debt excess tending to zero. -/
structure FinFourMovingMarkedPairMinimumApproach
    {data : FinFourMovingMarkedPairMinimumSource source}
    (residual : FinFourMovingMarkedPairVanishingResidual data) where
  refinement : ℕ → ℕ
  refinement_strictMono : StrictMono refinement
  excess_tendsto_zero : Tendsto
    (data.targetDebtExcess ∘ residual.select ∘ refinement)
    atTop (nhds 0)

/-- The exhaustive target-excess split after selecting a vanishing-residual
subsequence. -/
inductive FinFourMovingMarkedPairTargetAlternative
    {data : FinFourMovingMarkedPairMinimumSource source}
    (residual : FinFourMovingMarkedPairVanishingResidual data) : Type
  | offMinimum
      (result : FinFourMovingMarkedPairOffMinimumEndpoint residual)
  | minimumApproach
      (result : FinFourMovingMarkedPairMinimumApproach residual)

namespace FinFourMovingMarkedPairOffMinimumEndpoint

variable {data : FinFourMovingMarkedPairMinimumSource source}
  {residual : FinFourMovingMarkedPairVanishingResidual data}

/-- The one selector used by every displayed family in this arm is the
literal composition of the two strict refinements. -/
def select (result : FinFourMovingMarkedPairOffMinimumEndpoint residual) :
    ℕ → ℕ :=
  residual.select ∘ result.refinement

/-- The composed source selector is strictly increasing. -/
theorem select_strictMono
    (result : FinFourMovingMarkedPairOffMinimumEndpoint residual) :
    StrictMono result.select :=
  residual.select_strictMono.comp result.refinement_strictMono

/-- Premark residual still tends to zero on the composed selector. -/
theorem residual_tendsto_zero
    (result : FinFourMovingMarkedPairOffMinimumEndpoint residual) :
    Tendsto (data.premarkResidual ∘ result.select) atTop (nhds 0) :=
  residual.residual_tendsto_zero.comp result.refinement_strictMono.tendsto_atTop

/-- The literal target remains uniformly above the supplied minimum. -/
theorem minimum_add_excessFloor_le_targetDebt
    (result : FinFourMovingMarkedPairOffMinimumEndpoint residual)
    (rank : ℕ) :
    quittingTerminalSemanticDebtSum source.point.1 + result.excessFloor ≤
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (data.targetProfile (result.select rank))) := by
  have h := result.excessFloor_le rank
  unfold FinFourMovingMarkedPairMinimumSource.targetDebtExcess at h
  change result.excessFloor ≤
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (data.targetProfile (result.select rank))) -
        quittingTerminalSemanticDebtSum source.point.1 at h
  linarith

/-- The literal selected endpoint retains the fixed positive gain floor. -/
theorem reachFloor_mul_rewardGap_le_targetPayoffGain
    (result : FinFourMovingMarkedPairOffMinimumEndpoint residual)
    (rank : ℕ) :
    data.reachFloor * data.labels.rewardGap reward ≤
      quittingTerminalPayoff reward (data.targetProfile (result.select rank))
          data.labels.mover -
        quittingTerminalPayoff reward (data.sourceProfile (result.select rank))
          data.labels.mover :=
  data.reachFloor_mul_rewardGap_le_targetPayoffGain (result.select rank)

/-- The target is one literal behavioral replacement descendant of the
selected source row. -/
theorem target_ancestry
    (result : FinFourMovingMarkedPairOffMinimumEndpoint residual)
    (rank : ℕ) :
    IsQuittingBehaviorReplacementAncestry
      (data.sourceProfile (result.select rank))
      (data.targetProfile (result.select rank)) := by
  have hupdate : Function.update (data.sourceProfile (result.select rank))
      data.labels.mover
        (data.targetProfile (result.select rank) data.labels.mover) =
      data.targetProfile (result.select rank) :=
    update_endpoint_with_response_observer_eq_response reward
      (data.sourceProfile (result.select rank))
      (data.targetProfile (result.select rank)) data.labels.mover
      (data.targetProfile_eq_sourceProfile_of_ne (result.select rank))
  rw [← hupdate]
  exact isQuittingBehaviorReplacementAncestry_update _ _ _

end FinFourMovingMarkedPairOffMinimumEndpoint

namespace FinFourMovingMarkedPairMinimumApproach

variable {data : FinFourMovingMarkedPairMinimumSource source}
  {residual : FinFourMovingMarkedPairVanishingResidual data}

/-- The literal composition used by every family in the minimum-approach
arm. -/
def select (result : FinFourMovingMarkedPairMinimumApproach residual) :
    ℕ → ℕ :=
  residual.select ∘ result.refinement

/-- The composed source selector is strictly increasing. -/
theorem select_strictMono
    (result : FinFourMovingMarkedPairMinimumApproach residual) :
    StrictMono result.select :=
  residual.select_strictMono.comp result.refinement_strictMono

/-- Premark residual still tends to zero on the composed selector. -/
theorem residual_tendsto_zero
    (result : FinFourMovingMarkedPairMinimumApproach residual) :
    Tendsto (data.premarkResidual ∘ result.select) atTop (nhds 0) :=
  residual.residual_tendsto_zero.comp result.refinement_strictMono.tendsto_atTop

end FinFourMovingMarkedPairMinimumApproach

/-- Every vanishing-residual family has a further strict off-minimum or
minimum-approach target alternative. -/
theorem nonempty_finFourMovingMarkedPairTargetAlternative
    {data : FinFourMovingMarkedPairMinimumSource source}
    (residual : FinFourMovingMarkedPairVanishingResidual data) :
    Nonempty (FinFourMovingMarkedPairTargetAlternative residual) := by
  have hnonneg : ∀ rank, 0 ≤
      data.targetDebtExcess (residual.select rank) := fun rank ↦
    data.targetDebtExcess_nonneg (residual.select rank)
  obtain ⟨alternative⟩ := Math.nonempty_nonnegativeSubsequenceAlternative
    (data.targetDebtExcess ∘ residual.select) hnonneg
  cases alternative with
  | positiveFloor select hselect floor hfloor hselected =>
      exact ⟨.offMinimum {
        refinement := select
        refinement_strictMono := hselect
        excessFloor := floor
        excessFloor_pos := hfloor
        excessFloor_le := hselected }⟩
  | vanishing select hselect htendsto =>
      exact ⟨.minimumApproach {
        refinement := select
        refinement_strictMono := hselect
        excess_tendsto_zero := htendsto }⟩

/-- The complete precompact branch result: positive residual, quantitative
off-minimum endpoint, or simultaneous residual/excess approach to zero. -/
inductive FinFourMovingMarkedPairPrecompactAlternative
    (data : FinFourMovingMarkedPairMinimumSource source) (M : ℝ) : Type
  | positiveResidual
      (result : FinFourMovingMarkedPairPositiveResidual data M)
  | offMinimum
      (residual : FinFourMovingMarkedPairVanishingResidual data)
      (result : FinFourMovingMarkedPairOffMinimumEndpoint residual)
  | minimumApproach
      (residual : FinFourMovingMarkedPairVanishingResidual data)
      (result : FinFourMovingMarkedPairMinimumApproach residual)

/-- Exhaustive supplied-data compiler through the two numerical strict
subsequence splits. -/
theorem nonempty_finFourMovingMarkedPairPrecompactAlternative
    (data : FinFourMovingMarkedPairMinimumSource source)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (FinFourMovingMarkedPairPrecompactAlternative data M) := by
  obtain ⟨residualAlternative⟩ :=
    nonempty_finFourMovingMarkedPairResidualAlternative data M hreward
  cases residualAlternative with
  | positive result => exact ⟨.positiveResidual result⟩
  | vanishing residual =>
      obtain ⟨targetAlternative⟩ :=
        nonempty_finFourMovingMarkedPairTargetAlternative residual
      cases targetAlternative with
      | offMinimum result => exact ⟨.offMinimum residual result⟩
      | minimumApproach result => exact ⟨.minimumApproach residual result⟩

end GameTheory
