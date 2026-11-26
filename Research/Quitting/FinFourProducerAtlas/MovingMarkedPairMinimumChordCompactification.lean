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

private theorem tendsto_lawPoint_debt
    {points : ℕ → QuittingTerminalSemanticLawPoint (Fin 4)}
    {limit : QuittingTerminalSemanticLawPoint (Fin 4)} (who : Fin 4)
    (h : Tendsto points atTop (nhds limit)) :
    Tendsto (fun rank => quittingTerminalSemanticDebt (points rank).1 who) atTop
      (nhds (quittingTerminalSemanticDebt limit.1 who)) :=
  Tendsto.comp (f := points)
    (g := fun p : QuittingTerminalSemanticLawPoint (Fin 4) =>
      quittingTerminalSemanticDebt p.1 who)
    (((continuous_quittingTerminalSemanticDebt who).comp continuous_fst).tendsto limit) h

private theorem tendsto_lawPoint_mass
    {points : ℕ → QuittingTerminalSemanticLawPoint (Fin 4)}
    {limit : QuittingTerminalSemanticLawPoint (Fin 4)}
    (outcome : QuittingTerminalOutcome (Fin 4)) (h : Tendsto points atTop (nhds limit)) :
    Tendsto (fun rank => (points rank).2 outcome) atTop (nhds (limit.2 outcome)) :=
  Tendsto.comp (f := points)
    (g := fun p : QuittingTerminalSemanticLawPoint (Fin 4) => p.2 outcome)
    (((continuous_apply outcome).comp continuous_snd).tendsto limit) h

private theorem limit_le_affine
    {left first second : ℕ → ℝ} {a b c weight : ℝ}
    (hleft : Tendsto left atTop (nhds a))
    (hfirst : Tendsto first atTop (nhds b))
    (hsecond : Tendsto second atTop (nhds c))
    (h : ∀ n, left n ≤ (1 - weight) * first n + weight * second n) :
    a ≤ (1 - weight) * b + weight * c :=
  le_of_tendsto_of_tendsto hleft
    ((hfirst.const_mul (1 - weight)).add (hsecond.const_mul weight)) (Eventually.of_forall h)

private theorem limit_eq_affine
    {left first second : ℕ → ℝ} {a b c weight : ℝ}
    (hleft : Tendsto left atTop (nhds a))
    (hfirst : Tendsto first atTop (nhds b))
    (hsecond : Tendsto second atTop (nhds c))
    (h : ∀ n, left n = (1 - weight) * first n + weight * second n) :
    a = (1 - weight) * b + weight * c := by
  have hright := (hfirst.const_mul (1 - weight)).add (hsecond.const_mul weight)
  exact tendsto_nhds_unique hleft (hright.congr fun n => (h n).symm)

private theorem limit_eq_add_sub_scaled
    {left first factor : ℕ → ℝ} {a b c u v : ℝ}
    (hleft : Tendsto left atTop (nhds a))
    (hfirst : Tendsto first atTop (nhds b))
    (hfactor : Tendsto factor atTop (nhds c))
    (h : ∀ n, left n = first n + factor n * u - factor n * v) :
    a = b + c * u - c * v := by
  have hright := (hfirst.add (hfactor.mul_const u)).sub (hfactor.mul_const v)
  exact tendsto_nhds_unique hleft (hright.congr fun n => (h n).symm)

private theorem exists_common_limit {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {carrier : Set X} (hcompact : IsCompact carrier)
    (first second : ℕ → X) (hfirst : ∀ n, first n ∈ carrier)
    (hsecond : ∀ n, second n ∈ carrier) :
    ∃ limit ∈ carrier ×ˢ carrier, ∃ select : ℕ → ℕ, StrictMono select ∧
      Tendsto (first ∘ select) atTop (nhds limit.1) ∧
      Tendsto (second ∘ select) atTop (nhds limit.2) := by
  obtain ⟨limit, hmem, select, hmono, hlimit⟩ :=
    (hcompact.prod hcompact).tendsto_subseq
      (x := fun n => (first n, second n)) (fun n => ⟨hfirst n, hsecond n⟩)
  have hpair : Tendsto (fun n => (first (select n), second (select n)))
      atTop (nhds limit) := hlimit
  exact ⟨limit, hmem, select, hmono, hpair.fst_nhds, hpair.snd_nhds⟩

private theorem tendsto_reach_of_debt
    {debt residual reach : ℕ → ℝ} {limit gap : ℝ}
    (hdebt : Tendsto debt atTop (nhds limit)) (hresidual : Tendsto residual atTop (nhds 0))
    (hgap : gap ≠ 0) (h : ∀ n, debt n = reach n * gap + residual n) :
    Tendsto reach atTop (nhds (limit / gap)) := by
  have hdiv := (hdebt.sub hresidual).div_const gap
  rw [sub_zero] at hdiv
  refine hdiv.congr fun n => ?_
  rw [h n, add_sub_cancel_right, mul_div_cancel_right₀ _ hgap]

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

private def targetLawPointAt (rank : ℕ) : QuittingTerminalSemanticLawPoint (Fin 4) :=
  (quittingTerminalSemanticPair reward (data.targetProfile rank),
    quittingTerminalOutcomeMass reward (data.targetProfile rank))

private def chordLawPointAt
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1) (rank : ℕ) :
    QuittingTerminalSemanticLawPoint (Fin 4) :=
  (quittingTerminalSemanticPair reward (data.chordProfile weight hweight0 hweight1 rank),
    quittingTerminalOutcomeMass reward (data.chordProfile weight hweight0 hweight1 rank))

private theorem debtSum_eq_at_target_limit
    (select : ℕ → ℕ) (point : QuittingTerminalSemanticLawPoint (Fin 4))
    (htarget : Tendsto (targetLawPointAt (data := data) ∘ select) atTop (nhds point))
    (hexcess : Tendsto (data.targetDebtExcess ∘ select) atTop (nhds 0)) :
    quittingTerminalSemanticDebtSum point.1 = quittingTerminalSemanticDebtSum source.point.1 := by
  let debt : QuittingTerminalSemanticLawPoint (Fin 4) → ℝ :=
    fun p => quittingTerminalSemanticDebtSum p.1
  have hcontinuous : Continuous debt :=
    continuous_quittingTerminalSemanticDebtSum.comp continuous_fst
  have htargetDebt := Tendsto.comp (g := debt) (hcontinuous.tendsto point) htarget
  have hsourceDebt := (tendsto_const_nhds
    (x := quittingTerminalSemanticDebtSum source.point.1)).add hexcess
  rw [add_zero] at hsourceDebt
  refine tendsto_nhds_unique htargetDebt (hsourceDebt.congr fun rank => ?_)
  change quittingTerminalSemanticDebtSum source.point.1 +
    (quittingTerminalSemanticDebtSum (targetLawPointAt (data := data) (select rank)).1 -
      quittingTerminalSemanticDebtSum source.point.1) = _
  rw [← add_sub_assoc, add_sub_cancel_left]
  rfl

private theorem affine_add_sub (base weight reach pos neg : ℝ) :
    (1 - weight) * base + weight * (base + reach * pos - reach * neg) =
      base + weight * reach * pos - weight * reach * neg := by ring

private def sourceLawPointAt (rank : ℕ) : QuittingTerminalSemanticLawPoint (Fin 4) :=
  (quittingTerminalSemanticPair reward (data.sourceProfile rank),
    quittingTerminalOutcomeMass reward (data.sourceProfile rank))

private def reachLimitAtSource : ℝ :=
  quittingTerminalSemanticDebt source.point.1 data.labels.mover / data.labels.rewardGap reward

private theorem target_reach_summary
    (finalSelect : ℕ → ℕ) (target : QuittingTerminalSemanticLawPoint (Fin 4))
    (hsource : Tendsto (sourceLawPointAt (data := data) ∘ finalSelect) atTop (nhds source.point))
    (htarget : Tendsto (targetLawPointAt (data := data) ∘ finalSelect) atTop (nhds target))
    (hresidual : Tendsto (data.premarkResidual ∘ finalSelect) atTop (nhds 0)) :
    let reachLimit := reachLimitAtSource (data := data)
    Tendsto (data.markedReach ∘ finalSelect) atTop (nhds reachLimit) ∧
      data.reachFloor ≤ reachLimit ∧
      quittingTerminalSemanticDebt target.1 data.labels.mover = 0 ∧
      quittingTerminalSemanticDebt source.point.1 data.labels.mover =
        reachLimit * data.labels.rewardGap reward ∧
      ∀ outcome, target.2 outcome = source.point.2 outcome +
        reachLimit * (if outcome = some data.labels.targetTerminal then 1 else 0) -
        reachLimit * (if outcome = some data.labels.sourceTerminal then 1 else 0) := by
  have hsourceMoverDebt :=
    tendsto_lawPoint_debt (points := sourceLawPointAt (data := data) ∘ finalSelect)
      (limit := source.point) data.labels.mover hsource
  let reachLimit := reachLimitAtSource (data := data)
  have hreach : Tendsto (data.markedReach ∘ finalSelect) atTop (nhds reachLimit) :=
    tendsto_reach_of_debt (reach := data.markedReach ∘ finalSelect)
      hsourceMoverDebt hresidual (ne_of_gt data.rewardGap_pos) fun rank =>
        data.source_mover_debt_eq_markedReach_mul_rewardGap_add_premarkResidual
          (finalSelect rank)
  have hreachFloor : data.reachFloor ≤ reachLimit := by
    apply ge_of_tendsto hreach
    exact Filter.Eventually.of_forall fun rank ↦ data.reachFloor_le _
  have htargetMoverLimit :=
    tendsto_lawPoint_debt (points := targetLawPointAt (data := data) ∘ finalSelect)
      (limit := target) data.labels.mover htarget
  have htargetMoverZero : quittingTerminalSemanticDebt target.1 data.labels.mover = 0 := by
    have hzero : Tendsto (fun rank => quittingTerminalSemanticDebt
        ((targetLawPointAt (data := data) ∘ finalSelect) rank).1 data.labels.mover)
        atTop (nhds 0) :=
      hresidual.congr fun rank =>
        (data.target_mover_debt_eq_premarkResidual (finalSelect rank)).symm
    exact tendsto_nhds_unique htargetMoverLimit hzero
  have hsourceMoverEq : quittingTerminalSemanticDebt source.point.1
      data.labels.mover = reachLimit * data.labels.rewardGap reward :=
    (div_mul_cancel₀ _ (ne_of_gt data.rewardGap_pos)).symm
  have htargetSigned : ∀ outcome, target.2 outcome =
      source.point.2 outcome + reachLimit *
          (if outcome = some data.labels.targetTerminal then 1 else 0) -
        reachLimit *
          (if outcome = some data.labels.sourceTerminal then 1 else 0) := by
    intro outcome
    exact limit_eq_add_sub_scaled
      (u := if outcome = some data.labels.targetTerminal then 1 else 0)
      (v := if outcome = some data.labels.sourceTerminal then 1 else 0)
      (tendsto_lawPoint_mass outcome htarget) (tendsto_lawPoint_mass outcome hsource)
      hreach fun rank =>
        data.target_terminalOutcomeMass_eq_add_dirac_sub_dirac (finalSelect rank) outcome
  exact ⟨hreach, hreachFloor, htargetMoverZero, hsourceMoverEq, htargetSigned⟩

private theorem chord_affine_summary
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (finalSelect : ℕ → ℕ)
    (limit : QuittingTerminalSemanticLawPoint (Fin 4) × QuittingTerminalSemanticLawPoint (Fin 4))
    (hsource : Tendsto (sourceLawPointAt (data := data) ∘ finalSelect) atTop (nhds source.point))
    (htarget : Tendsto (targetLawPointAt (data := data) ∘ finalSelect) atTop (nhds limit.1))
    (hchord : Tendsto (chordLawPointAt (data := data) weight hweight0 hweight1 ∘ finalSelect)
      atTop (nhds limit.2)) :
    (∀ who, quittingTerminalSemanticDebt limit.2.1 who ≤
      (1 - weight) * quittingTerminalSemanticDebt source.point.1 who +
        weight * quittingTerminalSemanticDebt limit.1.1 who) ∧
      ∀ outcome, limit.2.2 outcome =
        (1 - weight) * source.point.2 outcome + weight * limit.1.2 outcome := by
  have hdebtLe : ∀ who, quittingTerminalSemanticDebt limit.2.1 who ≤
      (1 - weight) * quittingTerminalSemanticDebt source.point.1 who +
        weight * quittingTerminalSemanticDebt limit.1.1 who := by
    intro who
    exact limit_le_affine (weight := weight)
      (tendsto_lawPoint_debt who hchord) (tendsto_lawPoint_debt who hsource)
      (tendsto_lawPoint_debt who htarget) fun rank =>
        data.chord_debt_le_affine weight hweight0 hweight1 (finalSelect rank) who
  have hlawAffine : ∀ outcome, limit.2.2 outcome =
      (1 - weight) * source.point.2 outcome + weight * limit.1.2 outcome := by
    intro outcome
    exact limit_eq_affine (weight := weight)
      (tendsto_lawPoint_mass outcome hchord) (tendsto_lawPoint_mass outcome hsource)
      (tendsto_lawPoint_mass outcome htarget) fun rank =>
        quittingTerminalOutcomeMass_responseChord_eq reward
          (data.sourceProfile (finalSelect rank)) (data.targetProfile (finalSelect rank))
          data.labels.mover weight hweight0 hweight1
          (data.targetProfile_eq_sourceProfile_of_ne (finalSelect rank)) outcome
  exact ⟨hdebtLe, hlawAffine⟩

private def completeMinimumChordCompactification
    (minimum : FinFourMovingMarkedPairMinimumApproach residual)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (limit : QuittingTerminalSemanticLawPoint (Fin 4) ×
      QuittingTerminalSemanticLawPoint (Fin 4))
    (hlimitMem : limit ∈ quittingTerminalSemanticLawCarrier reward ×ˢ
      quittingTerminalSemanticLawCarrier reward)
    (refinement : ℕ → ℕ) (hrefinement : StrictMono refinement)
    (htarget : Tendsto (targetLawPointAt (data := data) ∘ minimum.select ∘ refinement)
      atTop (nhds limit.1))
    (hchord : Tendsto (chordLawPointAt (data := data) weight hweight0.le hweight1.le ∘
      minimum.select ∘ refinement) atTop (nhds limit.2)) :
    FinFourMovingMarkedPairMinimumChordCompactification minimum weight hweight0 hweight1 := by
  let finalSelect := minimum.select ∘ refinement
  have hfinalSelect : StrictMono finalSelect :=
    minimum.select_strictMono.comp hrefinement
  have hsource : Tendsto (sourceLawPointAt (data := data) ∘ finalSelect)
      atTop (nhds source.point) :=
    Tendsto.comp (f := finalSelect) (g := sourceLawPointAt (data := data))
      data.source_tendsto hfinalSelect.tendsto_atTop
  have hresidual : Tendsto (data.premarkResidual ∘ finalSelect)
      atTop (nhds 0) := by
    exact Tendsto.comp (f := refinement) (g := data.premarkResidual ∘ minimum.select)
      minimum.residual_tendsto_zero hrefinement.tendsto_atTop
  have hexcess : Tendsto (data.targetDebtExcess ∘ finalSelect)
      atTop (nhds 0) := by
    exact Tendsto.comp (f := refinement) (g := data.targetDebtExcess ∘ minimum.select)
      minimum.excess_tendsto_zero hrefinement.tendsto_atTop
  let reachLimit := reachLimitAtSource (data := data)
  obtain ⟨hreach, hreachFloor, htargetMoverZero, hsourceMoverEq, htargetSigned⟩ :=
    target_reach_summary finalSelect limit.1 hsource htarget hresidual
  obtain ⟨hdebtLe, hlawAffine⟩ :=
    chord_affine_summary weight hweight0.le hweight1.le finalSelect limit hsource htarget hchord
  have htargetDebtEq : quittingTerminalSemanticDebtSum limit.1.1 =
      quittingTerminalSemanticDebtSum source.point.1 :=
    debtSum_eq_at_target_limit finalSelect limit.1 htarget hexcess
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
  have hchordSigned : ∀ outcome, limit.2.2 outcome =
      source.point.2 outcome + weight * reachLimit *
          (if outcome = some data.labels.targetTerminal then 1 else 0) -
        weight * reachLimit *
          (if outcome = some data.labels.sourceTerminal then 1 else 0) := by
    intro outcome
    rw [hlawAffine outcome, htargetSigned outcome]
    exact affine_add_sub _ _ _ _ _
  exact {
    refinement := refinement
    refinement_strictMono := hrefinement
    targetPoint := limit.1
    targetPoint_mem := hlimitMem.1
    chordPoint := limit.2
    chordPoint_mem := hlimitMem.2
    target_tendsto := htarget
    chord_tendsto := hchord
    reachLimit := reachLimit
    reach_tendsto := hreach
    reachFloor_le_limit := hreachFloor
    geometry := geometry
    geometry_endpoint_eq := rfl
    geometry_response_eq := rfl
    geometry_chord_eq := rfl
    geometry_weight_eq := rfl
    target_mover_debt_eq_zero := htargetMoverZero
    source_mover_debt_eq_reachLimit_mul_rewardGap := hsourceMoverEq
    target_law_eq_signed := htargetSigned
    chord_law_eq_signed := hchordSigned }

/-- Vanishing residual and target excess produce one actual jointly
compactified minimum chord with the literal signed law and killed-coordinate
support drop. -/
theorem nonempty_finFourMovingMarkedPairMinimumChordCompactification
    (minimum : FinFourMovingMarkedPairMinimumApproach residual)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    Nonempty (FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) := by
  let target := targetLawPointAt (data := data) ∘ minimum.select
  let chord := chordLawPointAt (data := data) weight hweight0.le hweight1.le ∘ minimum.select
  obtain ⟨limit, hlimitMem, refinement, hrefinement, htarget, hchord⟩ :=
    exists_common_limit (quittingTerminalSemanticLawCarrier_isCompact reward)
      target chord (fun _ => quittingTerminalSemanticLawPoint_mem_carrier reward _)
      (fun _ => quittingTerminalSemanticLawPoint_mem_carrier reward _)
  exact ⟨completeMinimumChordCompactification minimum weight hweight0 hweight1
    limit hlimitMem refinement hrefinement htarget hchord⟩

end GameTheory
