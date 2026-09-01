import Research.Quitting.FinFourProducerAtlas.FinFourFullDebtCapBandTargetSplit
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticMinimumResponseChord

/-!
# Fixed-weight chord compactification for a minimum cap-band target

Finite cap-band targets need not lie on the minimum fibre.  This module first
passes the source and target profiles to their common compact limits, then
forms one fixed proper stopping-law chord at every finite row and compactifies
those actual chord profiles on one further shared refinement.  Convexity and
law affinity pass to the limit and produce the abstract minimum-chord law.

The construction retains the literal source chronology and target update.  It
does not make a pointwise minimum claim about a finite source, target, or chord
profile, and it adds no regeneration, renewal, Nash, or equilibrium result.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

namespace FinFourFullDebtCapBandTargetCompactification

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The literal source and target profiles at one compactifying row differ
only in the selected mover's complete strategy. -/
theorem targetProfile_eq_sourceProfile_of_ne
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M)
    (rank : ℕ) (other : Fin 4)
    (hne : other ≠ compactification.response.mover) :
    compactification.response.targetProfile
        (compactification.refinement rank) other =
      compactification.response.sourceProfile
        (compactification.refinement rank) other := by
  rw [compactification.targetProfile_eq_update rank,
    Function.update_of_ne hne]

/-- One actual fixed-weight stopping-law chord at a retained source/target
row. -/
def fixedWeightChordProfile
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingResponseChordProfile reward
    (compactification.response.sourceProfile
      (compactification.refinement rank))
    (compactification.response.targetProfile
      (compactification.refinement rank))
    compactification.response.mover weight hweight0 hweight1

/-- The complete outcome law of every actual fixed-weight chord is the
corresponding affine combination of the literal source and target laws. -/
theorem quittingTerminalOutcomeMass_fixedWeightChordProfile_eq
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (rank : ℕ) (outcome : QuittingTerminalOutcome (Fin 4)) :
    quittingTerminalOutcomeMass reward
        (compactification.fixedWeightChordProfile
          weight hweight0 hweight1 rank) outcome =
      (1 - weight) * quittingTerminalOutcomeMass reward
        (compactification.response.sourceProfile
          (compactification.refinement rank)) outcome +
      weight * quittingTerminalOutcomeMass reward
        (compactification.response.targetProfile
          (compactification.refinement rank)) outcome := by
  exact quittingTerminalOutcomeMass_responseChord_eq reward
    (compactification.response.sourceProfile
      (compactification.refinement rank))
    (compactification.response.targetProfile
      (compactification.refinement rank))
    compactification.response.mover weight hweight0 hweight1
    (compactification.targetProfile_eq_sourceProfile_of_ne rank) outcome

end FinFourFullDebtCapBandTargetCompactification

/-- One shared further refinement of the source, target, and actual fixed
weight chord sequences, together with their limiting minimum-chord law. -/
structure FinFourFullDebtFixedWeightChordCompactification
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (base : FinFourFullDebtCapBandTargetCompactification source M)
    (minimumTarget : FinFourFullDebtCapBandMinimumTarget base)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) where
  refinement : ℕ → ℕ
  refinement_strictMono : StrictMono refinement
  chordPoint : QuittingTerminalSemanticLawPoint (Fin 4)
  chordPoint_mem : chordPoint ∈ quittingTerminalSemanticLawCarrier reward
  chord_tendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (base.fixedWeightChordProfile weight hweight0.le hweight1.le
            (refinement rank)),
        quittingTerminalOutcomeMass reward
          (base.fixedWeightChordProfile weight hweight0.le hweight1.le
            (refinement rank))))
    atTop (nhds chordPoint)
  geometry : QuittingMinimumResponseChordLaw reward
  geometry_endpoint_eq : geometry.endpoint = source.point
  geometry_response_eq : geometry.response = base.targetPoint
  geometry_chord_eq : geometry.chord = chordPoint
  geometry_weight_eq : geometry.theta = weight

namespace FinFourFullDebtFixedWeightChordCompactification

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {base : FinFourFullDebtCapBandTargetCompactification source M}
  {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}

/-- The literal source semantic pair and law still converge to the original
minimum on the chord refinement. -/
theorem source_tendsto
    (compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (base.response.sourceProfile
            (base.refinement (compactification.refinement rank))),
        quittingTerminalOutcomeMass reward
          (base.response.sourceProfile
            (base.refinement (compactification.refinement rank)))))
      atTop (nhds source.point) := by
  exact base.source_tendsto.comp
    compactification.refinement_strictMono.tendsto_atTop

/-- The literal target semantic pair and law converge to the exact minimum
target on that same refinement. -/
theorem target_tendsto
    (compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (base.response.targetProfile
            (base.refinement (compactification.refinement rank))),
        quittingTerminalOutcomeMass reward
          (base.response.targetProfile
            (base.refinement (compactification.refinement rank)))))
      atTop (nhds base.targetPoint) := by
  exact base.target_tendsto.comp
    compactification.refinement_strictMono.tendsto_atTop

/-- The final chronological source indices remain strictly increasing after
all three selections. -/
theorem ancestryIndex_strictMono
    (compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1) :
    StrictMono (base.response.sourceIndex ∘ base.refinement ∘
      compactification.refinement) :=
  base.response.sourceIndex_strictMono.comp
    (base.refinement_strictMono.comp
      compactification.refinement_strictMono)

/-- Every displayed source remains the literal retained chronological
profile at its composed index. -/
theorem sourceProfile_eq_chronologyProfile
    (compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1)
    (rank : ℕ) :
    base.response.sourceProfile
        (base.refinement (compactification.refinement rank)) =
      base.response.chronologyProfiles
        (base.response.sourceIndex
          (base.refinement (compactification.refinement rank))) := rfl

/-- Every displayed target remains the literal cap-band update of that same
source row. -/
theorem targetProfile_eq_update
    (compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1)
    (rank : ℕ) :
    base.response.targetProfile
        (base.refinement (compactification.refinement rank)) =
      Function.update
        (base.response.sourceProfile
          (base.refinement (compactification.refinement rank)))
        base.response.mover
        (base.response.cutData
          (base.refinement (compactification.refinement rank))).targetStrategy :=
  rfl

/-- The killed target-mover coordinate gives a literal strict support drop
from the interior chord to the target limit. -/
theorem targetSupport_ssubset_chordSupport
    (compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1) :
    quittingPositiveDebtSupport base.targetPoint.1 ⊂
      quittingPositiveDebtSupport compactification.chordPoint.1 := by
  have hendpoint : 0 < quittingTerminalSemanticDebt
      compactification.geometry.endpoint.1 base.response.mover := by
    rw [compactification.geometry_endpoint_eq]
    exact base.response.limitingMoverDebt_pos
  have hresponse : quittingTerminalSemanticDebt
      compactification.geometry.response.1 base.response.mover = 0 := by
    rw [compactification.geometry_response_eq]
    exact minimumTarget.targetMoverDebt_eq_zero
  have hstrict :=
    compactification.geometry.response_support_ssubset_chord_of_killed
      base.response.mover hendpoint hresponse
  rw [compactification.geometry_response_eq,
    compactification.geometry_chord_eq] at hstrict
  exact hstrict

/-- In four players, the exact-minimum target support is nonempty and has at
most three coordinates. -/
theorem targetSupport_nonempty_and_card_le_three
    (compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1) :
    (quittingPositiveDebtSupport base.targetPoint.1).Nonempty ∧
      (quittingPositiveDebtSupport base.targetPoint.1).card ≤ 3 := by
  have hendpoint : 0 < quittingTerminalSemanticDebt
      compactification.geometry.endpoint.1 base.response.mover := by
    rw [compactification.geometry_endpoint_eq]
    exact base.response.limitingMoverDebt_pos
  have hresponse : quittingTerminalSemanticDebt
      compactification.geometry.response.1 base.response.mover = 0 := by
    rw [compactification.geometry_response_eq]
    exact minimumTarget.targetMoverDebt_eq_zero
  have hpositive : 0 < quittingTerminalSemanticDebtSum
      compactification.geometry.endpoint.1 := by
    rw [compactification.geometry_endpoint_eq]
    exact source.minimumDebt_pos
  have hresult :=
    compactification.geometry.response_support_nonempty_and_card_le_three_finFour
      base.response.mover hpositive hendpoint hresponse
  rw [compactification.geometry_response_eq] at hresult
  exact hresult

end FinFourFullDebtFixedWeightChordCompactification

/-- A minimum compact cap-band target and one fixed proper weight produce an
actual jointly compactified minimum response chord. -/
theorem nonempty_finFourFullDebtFixedWeightChordCompactification
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (base : FinFourFullDebtCapBandTargetCompactification source M)
    (minimumTarget : FinFourFullDebtCapBandMinimumTarget base)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    Nonempty (FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1) := by
  let chordProfile : ℕ → (quittingGame reward).BehaviorProfile := fun rank ↦
    base.fixedWeightChordProfile weight hweight0.le hweight1.le rank
  let chordPointSeq : ℕ → QuittingTerminalSemanticLawPoint (Fin 4) := fun rank ↦
    (quittingTerminalSemanticPair reward (chordProfile rank),
      quittingTerminalOutcomeMass reward (chordProfile rank))
  have hmem : ∀ rank,
      chordPointSeq rank ∈ quittingTerminalSemanticLawCarrier reward := by
    intro rank
    exact quittingTerminalSemanticLawPoint_mem_carrier reward
      (chordProfile rank)
  obtain ⟨chordPoint, hchordMem, refinement, hrefinement, hchordTendsto⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq hmem
  have hsourceTendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (base.response.sourceProfile (base.refinement (refinement rank))),
        quittingTerminalOutcomeMass reward
          (base.response.sourceProfile (base.refinement (refinement rank)))))
      atTop (nhds source.point) :=
    base.source_tendsto.comp hrefinement.tendsto_atTop
  have htargetTendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (base.response.targetProfile (base.refinement (refinement rank))),
        quittingTerminalOutcomeMass reward
          (base.response.targetProfile (base.refinement (refinement rank)))))
      atTop (nhds base.targetPoint) :=
    base.target_tendsto.comp hrefinement.tendsto_atTop
  have hdebtLe : ∀ who,
      quittingTerminalSemanticDebt chordPoint.1 who ≤
        (1 - weight) *
            quittingTerminalSemanticDebt source.point.1 who +
          weight *
            quittingTerminalSemanticDebt base.targetPoint.1 who := by
    intro who
    have hleft := ((continuous_quittingTerminalSemanticDebt who).comp
      continuous_fst).tendsto chordPoint |>.comp hchordTendsto
    have hsourceDebt := ((continuous_quittingTerminalSemanticDebt who).comp
      continuous_fst).tendsto source.point |>.comp hsourceTendsto
    have htargetDebt := ((continuous_quittingTerminalSemanticDebt who).comp
      continuous_fst).tendsto base.targetPoint |>.comp htargetTendsto
    have hright := (hsourceDebt.const_mul (1 - weight)).add
      (htargetDebt.const_mul weight)
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [] with rank
    exact quittingTerminalSemanticDebt_responseChord_le reward
      (base.response.sourceProfile (base.refinement (refinement rank)))
      (base.response.targetProfile (base.refinement (refinement rank)))
      base.response.mover who weight hweight0.le hweight1.le
      (base.targetProfile_eq_sourceProfile_of_ne (refinement rank))
  have hlaw : ∀ outcome,
      chordPoint.2 outcome =
        (1 - weight) * source.point.2 outcome +
          weight * base.targetPoint.2 outcome := by
    intro outcome
    have hleft := (((continuous_apply outcome).comp continuous_snd).tendsto
      chordPoint).comp hchordTendsto
    have hsourceLaw := (((continuous_apply outcome).comp continuous_snd).tendsto
      source.point).comp hsourceTendsto
    have htargetLaw := (((continuous_apply outcome).comp continuous_snd).tendsto
      base.targetPoint).comp htargetTendsto
    have hright := (hsourceLaw.const_mul (1 - weight)).add
      (htargetLaw.const_mul weight)
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [] with rank
    symm
    exact base.quittingTerminalOutcomeMass_fixedWeightChordProfile_eq
      weight hweight0.le hweight1.le (refinement rank) outcome
  let geometry : QuittingMinimumResponseChordLaw reward := {
    endpoint := source.point
    response := base.targetPoint
    chord := chordPoint
    theta := weight
    theta_pos := hweight0
    theta_lt_one := hweight1
    endpoint_mem := source.point_mem
    response_mem := base.targetPoint_mem
    chord_mem := hchordMem
    endpoint_minimum := source.minimum
    response_debtSum_eq_endpoint := minimumTarget.targetDebtSum_eq_source
    chord_debt_le_affine := hdebtLe
    chord_law_eq_affine := hlaw
  }
  exact ⟨{
    refinement := refinement
    refinement_strictMono := hrefinement
    chordPoint := chordPoint
    chordPoint_mem := hchordMem
    chord_tendsto := by
      simpa only [chordPointSeq, chordProfile, Function.comp_def] using
        hchordTendsto
    geometry := geometry
    geometry_endpoint_eq := rfl
    geometry_response_eq := rfl
    geometry_chord_eq := rfl
    geometry_weight_eq := rfl
  }⟩

end GameTheory
