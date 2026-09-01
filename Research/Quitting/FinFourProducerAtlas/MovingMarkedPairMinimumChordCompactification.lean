import Research.Quitting.FinFourProducerAtlas.MovingMarkedPairResidualAlternative
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticMinimumResponseChord

/-!
# Minimum-chord compactification of a supplied moving marked pair

On the branch where the literal target residual and total-debt excess both
vanish, one common strict refinement compactifies the target and the actual
fixed-weight stopping-law chord.  The affine debt and strict support-drop
conclusions are derived from cap convexity and global minimality; they are not
input fields.

This remains a supplied-family compiler.  It does not construct the moving
marked-pair family, causalize a prefix, regenerate a source, or prove renewal
or uniform equilibrium.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {data : FinFourMovingMarkedPairMinimumSource source}
  {residual : FinFourMovingMarkedPairVanishingResidual data}

/-- One common compactification of the target and actual fixed-weight chord
families on the vanishing-residual, vanishing-excess branch. -/
structure FinFourMovingMarkedPairMinimumChordCompactification
    (minimum : FinFourMovingMarkedPairMinimumApproach residual)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) where
  refinement : ℕ → ℕ
  refinement_strictMono : StrictMono refinement
  targetPoint : QuittingTerminalSemanticLawPoint (Fin 4)
  targetPoint_mem : targetPoint ∈ quittingTerminalSemanticLawCarrier reward
  chordPoint : QuittingTerminalSemanticLawPoint (Fin 4)
  chordPoint_mem : chordPoint ∈ quittingTerminalSemanticLawCarrier reward
  target_tendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (data.targetProfile (minimum.select (refinement rank))),
        quittingTerminalOutcomeMass reward
          (data.targetProfile (minimum.select (refinement rank)))))
    atTop (nhds targetPoint)
  chord_tendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (data.chordProfile weight hweight0.le hweight1.le
            (minimum.select (refinement rank))),
        quittingTerminalOutcomeMass reward
          (data.chordProfile weight hweight0.le hweight1.le
            (minimum.select (refinement rank)))))
    atTop (nhds chordPoint)
  reachLimit : ℝ
  reach_tendsto : Tendsto
    (data.markedReach ∘ minimum.select ∘ refinement)
    atTop (nhds reachLimit)
  reachFloor_le_limit : data.reachFloor ≤ reachLimit
  geometry : QuittingMinimumResponseChordLaw reward
  geometry_endpoint_eq : geometry.endpoint = source.point
  geometry_response_eq : geometry.response = targetPoint
  geometry_chord_eq : geometry.chord = chordPoint
  geometry_weight_eq : geometry.theta = weight
  target_mover_debt_eq_zero :
    quittingTerminalSemanticDebt targetPoint.1 data.labels.mover = 0
  source_mover_debt_eq_reachLimit_mul_rewardGap :
    quittingTerminalSemanticDebt source.point.1 data.labels.mover =
      reachLimit * data.labels.rewardGap reward
  target_law_eq_signed : ∀ outcome,
    targetPoint.2 outcome = source.point.2 outcome +
      reachLimit *
        (if outcome = some data.labels.targetTerminal then 1 else 0) -
      reachLimit *
        (if outcome = some data.labels.sourceTerminal then 1 else 0)
  chord_law_eq_signed : ∀ outcome,
    chordPoint.2 outcome = source.point.2 outcome +
      weight * reachLimit *
        (if outcome = some data.labels.targetTerminal then 1 else 0) -
      weight * reachLimit *
        (if outcome = some data.labels.sourceTerminal then 1 else 0)

namespace FinFourMovingMarkedPairMinimumChordCompactification

variable
  {minimum : FinFourMovingMarkedPairMinimumApproach residual}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}

/-- The one final selector is the literal composition of all three strict
refinements. -/
def select
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) : ℕ → ℕ :=
  minimum.select ∘ compactification.refinement

/-- The final composed source selector is strictly increasing. -/
theorem select_strictMono
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) :
    StrictMono compactification.select :=
  minimum.select_strictMono.comp compactification.refinement_strictMono

/-- The literal source semantic/law family still converges to the supplied
minimum on the final common refinement. -/
theorem source_tendsto
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (data.sourceProfile (compactification.select rank)),
        quittingTerminalOutcomeMass reward
          (data.sourceProfile (compactification.select rank))))
      atTop (nhds source.point) :=
  data.source_tendsto.comp compactification.select_strictMono.tendsto_atTop

/-- The target is an exact global minimum. -/
theorem target_globalMinimum
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) :
    ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum compactification.targetPoint.1 ≤
        quittingTerminalSemanticDebtSum candidate := by
  intro candidate hcandidate
  rw [← compactification.geometry_response_eq,
    compactification.geometry.response_debtSum_eq_endpoint,
    compactification.geometry_endpoint_eq]
  exact source.minimum candidate hcandidate

/-- The target and chord remain on the same positive minimum fibre. -/
theorem target_and_chord_debtSum_eq_source
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) :
    quittingTerminalSemanticDebtSum compactification.targetPoint.1 =
        quittingTerminalSemanticDebtSum source.point.1 ∧
      quittingTerminalSemanticDebtSum compactification.chordPoint.1 =
        quittingTerminalSemanticDebtSum source.point.1 := by
  constructor
  · rw [← compactification.geometry_response_eq,
      compactification.geometry.response_debtSum_eq_endpoint,
      compactification.geometry_endpoint_eq]
  · rw [← compactification.geometry_chord_eq,
      compactification.geometry.chord_debtSum_eq_endpoint,
      compactification.geometry_endpoint_eq]

/-- Every chord debt coordinate is the exact affine endpoint combination. -/
theorem chord_debt_eq_affine
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) (who : Fin 4) :
    quittingTerminalSemanticDebt compactification.chordPoint.1 who =
      (1 - weight) * quittingTerminalSemanticDebt source.point.1 who +
        weight * quittingTerminalSemanticDebt
          compactification.targetPoint.1 who := by
  have h := compactification.geometry.chord_debt_eq_affine who
  rwa [compactification.geometry_endpoint_eq,
    compactification.geometry_response_eq,
    compactification.geometry_chord_eq,
    compactification.geometry_weight_eq] at h

/-- The target support is a strict subset of the interior chord support. -/
theorem targetSupport_ssubset_chordSupport
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) :
    quittingPositiveDebtSupport compactification.targetPoint.1 ⊂
      quittingPositiveDebtSupport compactification.chordPoint.1 := by
  have hsource : 0 < quittingTerminalSemanticDebt
      source.point.1 data.labels.mover := by
    rw [compactification.source_mover_debt_eq_reachLimit_mul_rewardGap]
    exact mul_pos
      (data.reachFloor_pos.trans_le compactification.reachFloor_le_limit)
      data.rewardGap_pos
  have h := compactification.geometry.response_support_ssubset_chord_of_killed
    data.labels.mover (by
      rw [compactification.geometry_endpoint_eq]
      exact hsource) (by
      rw [compactification.geometry_response_eq]
      exact compactification.target_mover_debt_eq_zero)
  rwa [compactification.geometry_response_eq,
    compactification.geometry_chord_eq] at h

/-- The positive-minimum target support is nonempty and has cardinality at
most three. -/
theorem targetSupport_nonempty_and_card_le_three
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) :
    (quittingPositiveDebtSupport compactification.targetPoint.1).Nonempty ∧
      (quittingPositiveDebtSupport compactification.targetPoint.1).card ≤ 3 := by
  have hsource : 0 < quittingTerminalSemanticDebt
      source.point.1 data.labels.mover := by
    rw [compactification.source_mover_debt_eq_reachLimit_mul_rewardGap]
    exact mul_pos
      (data.reachFloor_pos.trans_le compactification.reachFloor_le_limit)
      data.rewardGap_pos
  have h :=
    compactification.geometry.response_support_nonempty_and_card_le_three_finFour
      data.labels.mover (by
        rw [compactification.geometry_endpoint_eq]
        exact source.minimumDebt_pos) (by
        rw [compactification.geometry_endpoint_eq]
        exact hsource) (by
        rw [compactification.geometry_response_eq]
        exact compactification.target_mover_debt_eq_zero)
  rwa [compactification.geometry_response_eq] at h

end FinFourMovingMarkedPairMinimumChordCompactification

/-- Vanishing residual and target excess produce one actual jointly
compactified minimum chord with the literal signed law and killed-coordinate
support drop. -/
theorem nonempty_finFourMovingMarkedPairMinimumChordCompactification
    (minimum : FinFourMovingMarkedPairMinimumApproach residual)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    Nonempty (FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) := by
  let joint : ℕ → QuittingTerminalSemanticLawPoint (Fin 4) ×
      QuittingTerminalSemanticLawPoint (Fin 4) := fun rank ↦
    ((quittingTerminalSemanticPair reward
        (data.targetProfile (minimum.select rank)),
      quittingTerminalOutcomeMass reward
        (data.targetProfile (minimum.select rank))),
    (quittingTerminalSemanticPair reward
        (data.chordProfile weight hweight0.le hweight1.le
          (minimum.select rank)),
      quittingTerminalOutcomeMass reward
        (data.chordProfile weight hweight0.le hweight1.le
          (minimum.select rank))))
  have hjointMem : ∀ rank, joint rank ∈
      quittingTerminalSemanticLawCarrier reward ×ˢ
        quittingTerminalSemanticLawCarrier reward := by
    intro rank
    exact ⟨quittingTerminalSemanticLawPoint_mem_carrier reward _,
      quittingTerminalSemanticLawPoint_mem_carrier reward _⟩
  obtain ⟨limit, hlimitMem, refinement, hrefinement, hlimit⟩ :=
    ((quittingTerminalSemanticLawCarrier_isCompact reward).prod
      (quittingTerminalSemanticLawCarrier_isCompact reward)).tendsto_subseq
      hjointMem
  have htarget : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (data.targetProfile (minimum.select (refinement rank))),
        quittingTerminalOutcomeMass reward
          (data.targetProfile (minimum.select (refinement rank)))))
      atTop (nhds limit.1) := by
    simpa only [joint, Function.comp_def] using
      (continuous_fst.tendsto limit).comp hlimit
  have hchord : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (data.chordProfile weight hweight0.le hweight1.le
            (minimum.select (refinement rank))),
        quittingTerminalOutcomeMass reward
          (data.chordProfile weight hweight0.le hweight1.le
            (minimum.select (refinement rank)))))
      atTop (nhds limit.2) := by
    simpa only [joint, Function.comp_def] using
      (continuous_snd.tendsto limit).comp hlimit
  let finalSelect := minimum.select ∘ refinement
  have hfinalSelect : StrictMono finalSelect :=
    minimum.select_strictMono.comp hrefinement
  have hsource : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (data.sourceProfile (finalSelect rank)),
        quittingTerminalOutcomeMass reward
          (data.sourceProfile (finalSelect rank))))
      atTop (nhds source.point) :=
    data.source_tendsto.comp hfinalSelect.tendsto_atTop
  have hresidual : Tendsto (data.premarkResidual ∘ finalSelect)
      atTop (nhds 0) := by
    exact minimum.residual_tendsto_zero.comp hrefinement.tendsto_atTop
  have hexcess : Tendsto (data.targetDebtExcess ∘ finalSelect)
      atTop (nhds 0) := by
    exact minimum.excess_tendsto_zero.comp hrefinement.tendsto_atTop
  have hsourceMoverDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (data.sourceProfile (finalSelect rank))) data.labels.mover)
      atTop (nhds (quittingTerminalSemanticDebt
        source.point.1 data.labels.mover)) :=
    (((continuous_quittingTerminalSemanticDebt data.labels.mover).comp
      continuous_fst).tendsto source.point).comp hsource
  have hreachScaled : Tendsto (fun rank ↦
      data.markedReach (finalSelect rank) * data.labels.rewardGap reward)
      atTop (nhds (quittingTerminalSemanticDebt
        source.point.1 data.labels.mover)) := by
    convert hsourceMoverDebt.sub hresidual using 1
    · funext rank
      have hidentity :=
        data.source_mover_debt_eq_markedReach_mul_rewardGap_add_premarkResidual
          (finalSelect rank)
      dsimp only [Function.comp_apply]
      linarith
    · simp
  let reachLimit := quittingTerminalSemanticDebt source.point.1
      data.labels.mover / data.labels.rewardGap reward
  have hreach : Tendsto (data.markedReach ∘ finalSelect)
      atTop (nhds reachLimit) := by
    have hdiv := hreachScaled.div_const (data.labels.rewardGap reward)
    change Tendsto (fun rank ↦ data.markedReach (finalSelect rank)) atTop
      (nhds reachLimit)
    simpa only [reachLimit,
      mul_div_cancel_right₀ _ (ne_of_gt data.rewardGap_pos)] using hdiv
  have hreachFloor : data.reachFloor ≤ reachLimit := by
    apply ge_of_tendsto hreach
    exact Filter.Eventually.of_forall fun rank ↦ data.reachFloor_le _
  have htargetDebtLimit : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (data.targetProfile (finalSelect rank))))
      atTop (nhds (quittingTerminalSemanticDebtSum limit.1.1)) :=
    ((continuous_quittingTerminalSemanticDebtSum.comp continuous_fst).tendsto
      limit.1).comp htarget
  have htargetDebtSource : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (data.targetProfile (finalSelect rank))))
      atTop (nhds (quittingTerminalSemanticDebtSum source.point.1)) := by
    convert tendsto_const_nhds.add hexcess using 1
    · funext rank
      dsimp only [Function.comp_apply]
      unfold FinFourMovingMarkedPairMinimumSource.targetDebtExcess
      ring
    · simp
  have htargetDebtEq : quittingTerminalSemanticDebtSum limit.1.1 =
      quittingTerminalSemanticDebtSum source.point.1 :=
    tendsto_nhds_unique htargetDebtLimit htargetDebtSource
  have htargetMoverLimit : Tendsto (fun rank ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (data.targetProfile (finalSelect rank))) data.labels.mover)
      atTop (nhds (quittingTerminalSemanticDebt limit.1.1
        data.labels.mover)) :=
    (((continuous_quittingTerminalSemanticDebt data.labels.mover).comp
      continuous_fst).tendsto limit.1).comp htarget
  have htargetMoverZero : quittingTerminalSemanticDebt limit.1.1
      data.labels.mover = 0 := by
    apply tendsto_nhds_unique htargetMoverLimit
    apply hresidual.congr'
    filter_upwards [] with rank
    exact (data.target_mover_debt_eq_premarkResidual (finalSelect rank)).symm
  have hsourceMoverEq : quittingTerminalSemanticDebt source.point.1
      data.labels.mover = reachLimit * data.labels.rewardGap reward := by
    dsimp only [reachLimit]
    field_simp [ne_of_gt data.rewardGap_pos]
  have hdebtLe : ∀ who, quittingTerminalSemanticDebt limit.2.1 who ≤
      (1 - weight) * quittingTerminalSemanticDebt source.point.1 who +
        weight * quittingTerminalSemanticDebt limit.1.1 who := by
    intro who
    have hleft := (((continuous_quittingTerminalSemanticDebt who).comp
      continuous_fst).tendsto limit.2).comp hchord
    have hsourceDebt := (((continuous_quittingTerminalSemanticDebt who).comp
      continuous_fst).tendsto source.point).comp hsource
    have htargetDebt := (((continuous_quittingTerminalSemanticDebt who).comp
      continuous_fst).tendsto limit.1).comp htarget
    have hright := (hsourceDebt.const_mul (1 - weight)).add
      (htargetDebt.const_mul weight)
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [] with rank
    exact data.chord_debt_le_affine weight hweight0.le hweight1.le
      (finalSelect rank) who
  have hlawAffine : ∀ outcome, limit.2.2 outcome =
      (1 - weight) * source.point.2 outcome + weight * limit.1.2 outcome := by
    intro outcome
    have hleft := (((continuous_apply outcome).comp continuous_snd).tendsto
      limit.2).comp hchord
    have hsourceLaw := (((continuous_apply outcome).comp continuous_snd).tendsto
      source.point).comp hsource
    have htargetLaw := (((continuous_apply outcome).comp continuous_snd).tendsto
      limit.1).comp htarget
    have hright := (hsourceLaw.const_mul (1 - weight)).add
      (htargetLaw.const_mul weight)
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [] with rank
    symm
    exact quittingTerminalOutcomeMass_responseChord_eq reward
      (data.sourceProfile (finalSelect rank))
      (data.targetProfile (finalSelect rank)) data.labels.mover weight
      hweight0.le hweight1.le
      (data.targetProfile_eq_sourceProfile_of_ne (finalSelect rank)) outcome
  let geometry : QuittingMinimumResponseChordLaw reward := {
    endpoint := source.point
    response := limit.1
    chord := limit.2
    theta := weight
    theta_pos := hweight0
    theta_lt_one := hweight1
    endpoint_mem := source.point_mem
    response_mem := hlimitMem.1
    chord_mem := hlimitMem.2
    endpoint_minimum := source.minimum
    response_debtSum_eq_endpoint := htargetDebtEq
    chord_debt_le_affine := hdebtLe
    chord_law_eq_affine := hlawAffine }
  have htargetSigned : ∀ outcome, limit.1.2 outcome =
      source.point.2 outcome + reachLimit *
          (if outcome = some data.labels.targetTerminal then 1 else 0) -
        reachLimit *
          (if outcome = some data.labels.sourceTerminal then 1 else 0) := by
    intro outcome
    have hleft := (((continuous_apply outcome).comp continuous_snd).tendsto
      limit.1).comp htarget
    have hsourceLaw := (((continuous_apply outcome).comp continuous_snd).tendsto
      source.point).comp hsource
    have hright := (hsourceLaw.add (hreach.mul_const
      (if outcome = some data.labels.targetTerminal then 1 else 0))).sub
      (hreach.mul_const
        (if outcome = some data.labels.sourceTerminal then 1 else 0))
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [] with rank
    exact (data.target_terminalOutcomeMass_eq_add_dirac_sub_dirac
      (finalSelect rank) outcome).symm
  have hchordSigned : ∀ outcome, limit.2.2 outcome =
      source.point.2 outcome + weight * reachLimit *
          (if outcome = some data.labels.targetTerminal then 1 else 0) -
        weight * reachLimit *
          (if outcome = some data.labels.sourceTerminal then 1 else 0) := by
    intro outcome
    have hleft := (((continuous_apply outcome).comp continuous_snd).tendsto
      limit.2).comp hchord
    have hsourceLaw := (((continuous_apply outcome).comp continuous_snd).tendsto
      source.point).comp hsource
    have hweightedReach := hreach.const_mul weight
    have hright := (hsourceLaw.add (hweightedReach.mul_const
      (if outcome = some data.labels.targetTerminal then 1 else 0))).sub
      (hweightedReach.mul_const
        (if outcome = some data.labels.sourceTerminal then 1 else 0))
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [] with rank
    exact (data.chord_terminalOutcomeMass_eq_add_scaled_dirac_sub_dirac
      weight hweight0.le hweight1.le (finalSelect rank) outcome).symm
  exact ⟨{
    refinement := refinement
    refinement_strictMono := hrefinement
    targetPoint := limit.1
    targetPoint_mem := hlimitMem.1
    chordPoint := limit.2
    chordPoint_mem := hlimitMem.2
    target_tendsto := by simpa only [finalSelect, Function.comp_apply] using htarget
    chord_tendsto := by simpa only [finalSelect, Function.comp_apply] using hchord
    reachLimit := reachLimit
    reach_tendsto := by simpa only [finalSelect, Function.comp_apply] using hreach
    reachFloor_le_limit := hreachFloor
    geometry := geometry
    geometry_endpoint_eq := rfl
    geometry_response_eq := rfl
    geometry_chord_eq := rfl
    geometry_weight_eq := rfl
    target_mover_debt_eq_zero := htargetMoverZero
    source_mover_debt_eq_reachLimit_mul_rewardGap := hsourceMoverEq
    target_law_eq_signed := htargetSigned
    chord_law_eq_signed := hchordSigned }⟩

end GameTheory
