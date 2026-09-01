import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticMinimumResponseChord

/-!
# Near-minimum exact-response chord compactification

This source-independent interface begins with literal source and exact-response
profile families already jointly compactified at two minimum endpoints.  It
forms the actual fixed-weight stopping-law chord at every finite row, performs
one further compactification of those actual profiles, and only then constructs
the abstract minimum-response chord law.  No finite profile is asserted to be
a minimum.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

/-- A literal exact-response family whose two endpoint sequences converge to
the same positive global debt level. -/
structure QuittingNearMinimumExactResponseFamily
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) where
  sourceProfile : ℕ → (quittingGame reward).BehaviorProfile
  targetProfile : ℕ → (quittingGame reward).BehaviorProfile
  mover : Fin 4
  targetStrategy : ℕ → (quittingGame reward).BehaviorStrategy mover
  targetProfile_eq_update : ∀ rank,
    targetProfile rank =
      Function.update (sourceProfile rank) mover (targetStrategy rank)
  cap_attained : ∀ rank,
    quittingTerminalPayoff reward (targetProfile rank) mover =
      quittingContinuationBestResponseValue reward (sourceProfile rank) mover
  minimumDebt : ℝ
  minimumDebt_pos : 0 < minimumDebt
  sourcePoint : QuittingTerminalSemanticLawPoint (Fin 4)
  targetPoint : QuittingTerminalSemanticLawPoint (Fin 4)
  sourcePoint_mem : sourcePoint ∈ quittingTerminalSemanticLawCarrier reward
  targetPoint_mem : targetPoint ∈ quittingTerminalSemanticLawCarrier reward
  source_tendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward (sourceProfile rank),
        quittingTerminalOutcomeMass reward (sourceProfile rank)))
    atTop (nhds sourcePoint)
  target_tendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward (targetProfile rank),
        quittingTerminalOutcomeMass reward (targetProfile rank)))
    atTop (nhds targetPoint)
  minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    minimumDebt ≤ quittingTerminalSemanticDebtSum candidate
  sourceDebtSum_tendsto : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (sourceProfile rank)))
    atTop (nhds minimumDebt)
  targetDebtSum_tendsto : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (targetProfile rank)))
    atTop (nhds minimumDebt)
  moverDebtFloor : ℝ
  moverDebtFloor_pos : 0 < moverDebtFloor
  source_moverDebt_floor : ∀ rank, moverDebtFloor ≤
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (sourceProfile rank)) mover

namespace QuittingNearMinimumExactResponseFamily

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}

theorem targetProfile_eq_sourceProfile_of_ne
    (family : QuittingNearMinimumExactResponseFamily reward)
    (rank : ℕ) (other : Fin 4) (hne : other ≠ family.mover) :
    family.targetProfile rank other = family.sourceProfile rank other := by
  rw [family.targetProfile_eq_update rank, Function.update_of_ne hne]

theorem target_moverDebt_eq_zero
    (family : QuittingNearMinimumExactResponseFamily reward) (rank : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (family.targetProfile rank))
        family.mover = 0 := by
  have hcap : quittingContinuationBestResponseValue reward
        (family.targetProfile rank) family.mover =
      quittingContinuationBestResponseValue reward
        (family.sourceProfile rank) family.mover := by
    rw [family.targetProfile_eq_update rank,
      quittingContinuationBestResponseValue_update_self]
  change quittingContinuationBestResponseValue reward
        (family.targetProfile rank) family.mover -
      quittingTerminalPayoff reward (family.targetProfile rank) family.mover = 0
  rw [hcap, family.cap_attained rank]
  ring

theorem sourcePoint_debtSum_eq_minimumDebt
    (family : QuittingNearMinimumExactResponseFamily reward) :
    quittingTerminalSemanticDebtSum family.sourcePoint.1 =
      family.minimumDebt := by
  have hlimit := ((continuous_quittingTerminalSemanticDebtSum.comp
    continuous_fst).tendsto family.sourcePoint).comp family.source_tendsto
  exact tendsto_nhds_unique hlimit family.sourceDebtSum_tendsto

theorem targetPoint_debtSum_eq_minimumDebt
    (family : QuittingNearMinimumExactResponseFamily reward) :
    quittingTerminalSemanticDebtSum family.targetPoint.1 =
      family.minimumDebt := by
  have hlimit := ((continuous_quittingTerminalSemanticDebtSum.comp
    continuous_fst).tendsto family.targetPoint).comp family.target_tendsto
  exact tendsto_nhds_unique hlimit family.targetDebtSum_tendsto

theorem targetPoint_moverDebt_eq_zero
    (family : QuittingNearMinimumExactResponseFamily reward) :
    quittingTerminalSemanticDebt family.targetPoint.1 family.mover = 0 := by
  have hlimit := (((continuous_quittingTerminalSemanticDebt family.mover).comp
    continuous_fst).tendsto family.targetPoint).comp family.target_tendsto
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  apply tendsto_nhds_unique hlimit
  apply hzero.congr'
  filter_upwards [] with rank
  symm
  exact family.target_moverDebt_eq_zero rank

theorem moverDebtFloor_le_sourcePoint
    (family : QuittingNearMinimumExactResponseFamily reward) :
    family.moverDebtFloor ≤
      quittingTerminalSemanticDebt family.sourcePoint.1 family.mover := by
  have hlimit := (((continuous_quittingTerminalSemanticDebt family.mover).comp
    continuous_fst).tendsto family.sourcePoint).comp family.source_tendsto
  exact ge_of_tendsto hlimit
    (Eventually.of_forall family.source_moverDebt_floor)

/-- The actual finite fixed-weight response chord. -/
def fixedWeightChordProfile
    (family : QuittingNearMinimumExactResponseFamily reward)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingResponseChordProfile reward (family.sourceProfile rank)
    (family.targetProfile rank) family.mover weight hweight0 hweight1

theorem terminalOutcomeMass_fixedWeightChordProfile_eq
    (family : QuittingNearMinimumExactResponseFamily reward)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (rank : ℕ) (outcome : QuittingTerminalOutcome (Fin 4)) :
    quittingTerminalOutcomeMass reward
        (family.fixedWeightChordProfile weight hweight0 hweight1 rank) outcome =
      (1 - weight) * quittingTerminalOutcomeMass reward
          (family.sourceProfile rank) outcome +
        weight * quittingTerminalOutcomeMass reward
          (family.targetProfile rank) outcome := by
  exact quittingTerminalOutcomeMass_responseChord_eq reward
    (family.sourceProfile rank) (family.targetProfile rank) family.mover
    weight hweight0 hweight1
    (family.targetProfile_eq_sourceProfile_of_ne rank) outcome

end QuittingNearMinimumExactResponseFamily

/-- One further refinement of the actual chord profiles and the minimum chord
law derived from their common limit. -/
structure QuittingNearMinimumExactResponseChordCompactification
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (family : QuittingNearMinimumExactResponseFamily reward)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) where
  refinement : ℕ → ℕ
  refinement_strictMono : StrictMono refinement
  chordPoint : QuittingTerminalSemanticLawPoint (Fin 4)
  chordPoint_mem : chordPoint ∈ quittingTerminalSemanticLawCarrier reward
  chord_tendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (family.fixedWeightChordProfile weight hweight0.le hweight1.le
            (refinement rank)),
        quittingTerminalOutcomeMass reward
          (family.fixedWeightChordProfile weight hweight0.le hweight1.le
            (refinement rank))))
    atTop (nhds chordPoint)
  geometry : QuittingMinimumResponseChordLaw reward
  geometry_endpoint_eq : geometry.endpoint = family.sourcePoint
  geometry_response_eq : geometry.response = family.targetPoint
  geometry_chord_eq : geometry.chord = chordPoint
  geometry_weight_eq : geometry.theta = weight

namespace QuittingNearMinimumExactResponseChordCompactification

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {family : QuittingNearMinimumExactResponseFamily reward}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}

theorem source_tendsto
    (compactification : QuittingNearMinimumExactResponseChordCompactification
      family weight hweight0 hweight1) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (family.sourceProfile (compactification.refinement rank)),
        quittingTerminalOutcomeMass reward
          (family.sourceProfile (compactification.refinement rank))))
      atTop (nhds family.sourcePoint) :=
  family.source_tendsto.comp
    compactification.refinement_strictMono.tendsto_atTop

theorem target_tendsto
    (compactification : QuittingNearMinimumExactResponseChordCompactification
      family weight hweight0 hweight1) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (family.targetProfile (compactification.refinement rank)),
        quittingTerminalOutcomeMass reward
          (family.targetProfile (compactification.refinement rank))))
      atTop (nhds family.targetPoint) :=
  family.target_tendsto.comp
    compactification.refinement_strictMono.tendsto_atTop

theorem targetSupport_ssubset_chordSupport
    (compactification : QuittingNearMinimumExactResponseChordCompactification
      family weight hweight0 hweight1) :
    quittingPositiveDebtSupport family.targetPoint.1 ⊂
      quittingPositiveDebtSupport compactification.chordPoint.1 := by
  have hendpoint : 0 < quittingTerminalSemanticDebt
      compactification.geometry.endpoint.1 family.mover := by
    rw [compactification.geometry_endpoint_eq]
    exact family.moverDebtFloor_pos.trans_le
      family.moverDebtFloor_le_sourcePoint
  have hresponse : quittingTerminalSemanticDebt
      compactification.geometry.response.1 family.mover = 0 := by
    rw [compactification.geometry_response_eq]
    exact family.targetPoint_moverDebt_eq_zero
  have hstrict := compactification.geometry.response_support_ssubset_chord_of_killed
    family.mover hendpoint hresponse
  rw [compactification.geometry_response_eq,
    compactification.geometry_chord_eq] at hstrict
  exact hstrict

theorem targetSupport_nonempty_and_card_le_three
    (compactification : QuittingNearMinimumExactResponseChordCompactification
      family weight hweight0 hweight1) :
    (quittingPositiveDebtSupport family.targetPoint.1).Nonempty ∧
      (quittingPositiveDebtSupport family.targetPoint.1).card ≤ 3 := by
  have hendpoint : 0 < quittingTerminalSemanticDebt
      compactification.geometry.endpoint.1 family.mover := by
    rw [compactification.geometry_endpoint_eq]
    exact family.moverDebtFloor_pos.trans_le
      family.moverDebtFloor_le_sourcePoint
  have hresponse : quittingTerminalSemanticDebt
      compactification.geometry.response.1 family.mover = 0 := by
    rw [compactification.geometry_response_eq]
    exact family.targetPoint_moverDebt_eq_zero
  have hpositive : 0 < quittingTerminalSemanticDebtSum
      compactification.geometry.endpoint.1 := by
    rw [compactification.geometry_endpoint_eq,
      family.sourcePoint_debtSum_eq_minimumDebt]
    exact family.minimumDebt_pos
  have hresult :=
    compactification.geometry.response_support_nonempty_and_card_le_three_finFour
      family.mover hpositive hendpoint hresponse
  rw [compactification.geometry_response_eq] at hresult
  exact hresult

end QuittingNearMinimumExactResponseChordCompactification

/-- Actual fixed-weight chord profiles compactify to a minimum response chord
with no finite minimum assumption. -/
theorem nonempty_quittingNearMinimumExactResponseChordCompactification
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (family : QuittingNearMinimumExactResponseFamily reward)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    Nonempty (QuittingNearMinimumExactResponseChordCompactification
      family weight hweight0 hweight1) := by
  let chordProfile : ℕ → (quittingGame reward).BehaviorProfile := fun rank ↦
    family.fixedWeightChordProfile weight hweight0.le hweight1.le rank
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
          (family.sourceProfile (refinement rank)),
        quittingTerminalOutcomeMass reward
          (family.sourceProfile (refinement rank))))
      atTop (nhds family.sourcePoint) :=
    family.source_tendsto.comp hrefinement.tendsto_atTop
  have htargetTendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (family.targetProfile (refinement rank)),
        quittingTerminalOutcomeMass reward
          (family.targetProfile (refinement rank))))
      atTop (nhds family.targetPoint) :=
    family.target_tendsto.comp hrefinement.tendsto_atTop
  have hdebtLe : ∀ who,
      quittingTerminalSemanticDebt chordPoint.1 who ≤
        (1 - weight) *
            quittingTerminalSemanticDebt family.sourcePoint.1 who +
          weight * quittingTerminalSemanticDebt family.targetPoint.1 who := by
    intro who
    have hleft := ((continuous_quittingTerminalSemanticDebt who).comp
      continuous_fst).tendsto chordPoint |>.comp hchordTendsto
    have hsourceDebt := ((continuous_quittingTerminalSemanticDebt who).comp
      continuous_fst).tendsto family.sourcePoint |>.comp hsourceTendsto
    have htargetDebt := ((continuous_quittingTerminalSemanticDebt who).comp
      continuous_fst).tendsto family.targetPoint |>.comp htargetTendsto
    have hright := (hsourceDebt.const_mul (1 - weight)).add
      (htargetDebt.const_mul weight)
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [] with rank
    exact quittingTerminalSemanticDebt_responseChord_le reward
      (family.sourceProfile (refinement rank))
      (family.targetProfile (refinement rank)) family.mover who weight
      hweight0.le hweight1.le
      (family.targetProfile_eq_sourceProfile_of_ne (refinement rank))
  have hlaw : ∀ outcome,
      chordPoint.2 outcome =
        (1 - weight) * family.sourcePoint.2 outcome +
          weight * family.targetPoint.2 outcome := by
    intro outcome
    have hleft := (((continuous_apply outcome).comp continuous_snd).tendsto
      chordPoint).comp hchordTendsto
    have hsourceLaw := (((continuous_apply outcome).comp continuous_snd).tendsto
      family.sourcePoint).comp hsourceTendsto
    have htargetLaw := (((continuous_apply outcome).comp continuous_snd).tendsto
      family.targetPoint).comp htargetTendsto
    have hright := (hsourceLaw.const_mul (1 - weight)).add
      (htargetLaw.const_mul weight)
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [] with rank
    symm
    exact family.terminalOutcomeMass_fixedWeightChordProfile_eq
      weight hweight0.le hweight1.le (refinement rank) outcome
  have hsourceDebtEq := family.sourcePoint_debtSum_eq_minimumDebt
  have htargetDebtEq := family.targetPoint_debtSum_eq_minimumDebt
  let geometry : QuittingMinimumResponseChordLaw reward := {
    endpoint := family.sourcePoint
    response := family.targetPoint
    chord := chordPoint
    theta := weight
    theta_pos := hweight0
    theta_lt_one := hweight1
    endpoint_mem := family.sourcePoint_mem
    response_mem := family.targetPoint_mem
    chord_mem := hchordMem
    endpoint_minimum := by
      intro candidate hcandidate
      rw [hsourceDebtEq]
      exact family.minimum candidate hcandidate
    response_debtSum_eq_endpoint := by
      rw [hsourceDebtEq, htargetDebtEq]
    chord_debt_le_affine := hdebtLe
    chord_law_eq_affine := hlaw
  }
  exact ⟨{
    refinement := refinement
    refinement_strictMono := hrefinement
    chordPoint := chordPoint
    chordPoint_mem := hchordMem
    chord_tendsto := hchordTendsto
    geometry := geometry
    geometry_endpoint_eq := rfl
    geometry_response_eq := rfl
    geometry_chord_eq := rfl
    geometry_weight_eq := rfl
  }⟩

end GameTheory
