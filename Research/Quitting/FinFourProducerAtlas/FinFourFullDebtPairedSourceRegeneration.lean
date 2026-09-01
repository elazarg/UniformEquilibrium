import Research.Quitting.FinFourProducerAtlas.FinFourFullDebtCommonPrefixResponse
import Research.Quitting.FinFourProducerAtlas.PairedSameResidualSourceRegeneration

/-!
# Full-debt paired-source regeneration adapter

The copied target profiles of a fixed-weight full-debt response chord converge
in their complete terminal law as well as their semantic pair.  A thin adapter
then feeds those literal chord/target pairs to the generic same-residual
regeneration compiler.  A uniform marked-row floor gives the stronger fixed-
mark compiler; positive limiting atom mass alone gives a literal paired
chronology with rank-dependent positive dates.

The uniform single-row floor is an explicit hypothesis: positive limiting
terminal-law mass alone only yields positive finite-window marks and does not
prevent temporal diffusion.  No finite profile is asserted to be a minimum,
and the retained origin edge is not called renewable.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped BigOperators Topology

private theorem jointSurvival_mul_outcomeMass_le_literalRootStack
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (roots : List (Fin 4 → PMF Bool))
    (profile : (quittingGame reward).BehaviorProfile)
    (outcome : QuittingTerminalOutcome (Fin 4)) :
    quittingLiteralRootStackJointSurvival roots *
        quittingTerminalOutcomeMass reward profile outcome ≤
      quittingTerminalOutcomeMass reward
        (quittingLiteralRootStackProfile reward roots profile) outcome := by
  induction roots with
  | nil => simp [quittingLiteralRootStackJointSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackJointSurvival, List.map_cons,
        List.prod_cons, quittingLiteralRootStackProfile_cons]
      cases outcome with
      | none =>
          rw [quittingTerminalOutcomeMass_rootThenContinuation]
          have hscaled := mul_le_mul_of_nonneg_left ih
            (quittingStationaryContinueMass_nonneg root)
          simpa only [quittingLiteralRootStackJointSurvival, mul_assoc] using hscaled
      | some terminal =>
          rw [quittingTerminalOutcomeMass_rootThenContinuation]
          have hscaled := mul_le_mul_of_nonneg_left ih
            (quittingStationaryContinueMass_nonneg root)
          calc
            quittingStationaryContinueMass root *
                  (List.map quittingStationaryContinueMass roots).prod *
                quittingTerminalOutcomeMass reward profile (some terminal) =
              quittingStationaryContinueMass root *
                ((List.map quittingStationaryContinueMass roots).prod *
                  quittingTerminalOutcomeMass reward profile (some terminal)) := by
                ring
            _ ≤ quittingStationaryContinueMass root *
                quittingTerminalOutcomeMass reward
                  (quittingLiteralRootStackProfile reward roots profile)
                  (some terminal) := hscaled
            _ ≤ quittingRootCoalitionMass root terminal.val +
                quittingStationaryContinueMass root *
                  quittingTerminalOutcomeMass reward
                    (quittingLiteralRootStackProfile reward roots profile)
                    (some terminal) := by
              exact le_add_of_nonneg_left
                (quittingRootCoalitionMass_nonneg root terminal.val)

private theorem literalRootStack_outcomeMass_le_one_sub_survival_mul
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (roots : List (Fin 4 → PMF Bool))
    (profile : (quittingGame reward).BehaviorProfile)
    (outcome : QuittingTerminalOutcome (Fin 4)) :
    quittingTerminalOutcomeMass reward
        (quittingLiteralRootStackProfile reward roots profile) outcome ≤
      1 - quittingLiteralRootStackJointSurvival roots *
        (1 - quittingTerminalOutcomeMass reward profile outcome) := by
  let prefixed := quittingLiteralRootStackProfile reward roots profile
  let q := quittingLiteralRootStackJointSurvival roots
  have hlower : ∀ other, q * quittingTerminalOutcomeMass reward profile other ≤
      quittingTerminalOutcomeMass reward prefixed other := by
    intro other
    exact jointSurvival_mul_outcomeMass_le_literalRootStack
      roots profile other
  have hsum :
      (∑ other ∈ (Finset.univ.erase outcome),
        q * quittingTerminalOutcomeMass reward profile other) ≤
      ∑ other ∈ (Finset.univ.erase outcome),
        quittingTerminalOutcomeMass reward prefixed other :=
    Finset.sum_le_sum fun other _ ↦ hlower other
  have hp := (quittingTerminalOutcomeMass_mem_stdSimplex reward prefixed).2
  have ht := (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).2
  have hmem : outcome ∈ (Finset.univ : Finset (QuittingTerminalOutcome (Fin 4))) :=
    Finset.mem_univ outcome
  have hpSplit := Finset.sum_erase_add Finset.univ
    (fun other ↦ quittingTerminalOutcomeMass reward prefixed other) hmem
  have htSplit := Finset.sum_erase_add Finset.univ
    (fun other ↦ quittingTerminalOutcomeMass reward profile other) hmem
  rw [← Finset.mul_sum] at hsum
  dsimp only [prefixed, q] at hp ht hpSplit htSplit hsum ⊢
  rw [hp] at hpSplit
  rw [ht] at htSplit
  have htRest :
      (∑ other ∈ Finset.univ.erase outcome,
        quittingTerminalOutcomeMass reward profile other) =
      1 - quittingTerminalOutcomeMass reward profile outcome := by
    linarith
  calc
    quittingTerminalOutcomeMass reward
          (quittingLiteralRootStackProfile reward roots profile) outcome =
        1 - ∑ other ∈ Finset.univ.erase outcome,
          quittingTerminalOutcomeMass reward
            (quittingLiteralRootStackProfile reward roots profile) other := by
      linarith
    _ ≤ 1 - quittingLiteralRootStackJointSurvival roots *
        ∑ other ∈ Finset.univ.erase outcome,
          quittingTerminalOutcomeMass reward profile other :=
      sub_le_sub_left hsum 1
    _ = 1 - quittingLiteralRootStackJointSurvival roots *
        (1 - quittingTerminalOutcomeMass reward profile outcome) := by
      rw [htRest]

namespace FinFourFullDebtCommonPrefixResponse

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {base : FinFourFullDebtCapBandTargetCompactification source M}
  {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
  {compactification : FinFourFullDebtFixedWeightChordCompactification
    base minimumTarget weight hweight0 hweight1}

/-- Every coordinate of the copied target terminal law converges to the
corresponding target-limit coordinate. -/
theorem targetPrefixed_outcomeMass_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (outcome : QuittingTerminalOutcome (Fin 4)) :
    Tendsto (fun rank ↦ quittingTerminalOutcomeMass reward
      (data.targetPrefixedProfile rank) outcome) atTop
      (nhds (base.targetPoint.2 outcome)) := by
  have htail := (tendsto_pi_nhds.mp
    (continuous_snd.tendsto base.targetPoint |>.comp
      compactification.target_tendsto)) outcome
  have hq := data.survival_tendsto_one
  have hlowerT := hq.mul htail
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hupperT := hone.sub (hq.mul (hone.sub htail))
  have hlowerT' : Tendsto (fun rank ↦ data.survival rank *
      quittingTerminalOutcomeMass reward
        (base.response.targetProfile
          (base.refinement (compactification.refinement rank))) outcome)
      atTop (nhds (base.targetPoint.2 outcome)) := by
    simpa using hlowerT
  have hupperT' : Tendsto (fun rank ↦ 1 - data.survival rank *
      (1 - quittingTerminalOutcomeMass reward
        (base.response.targetProfile
          (base.refinement (compactification.refinement rank))) outcome))
      atTop (nhds (base.targetPoint.2 outcome)) := by
    simpa using hupperT
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlowerT' hupperT'
  · intro rank
    simpa only [FinFourFullDebtCommonPrefixResponse.targetPrefixedProfile,
      FinFourFullDebtCommonPrefixResponse.targetTail,
      FinFourFullDebtCommonPrefixResponse.survival_eq_jointSurvival] using
      jointSurvival_mul_outcomeMass_le_literalRootStack
        (data.roots rank) (data.targetTail rank) outcome
  · intro rank
    simpa only [FinFourFullDebtCommonPrefixResponse.targetPrefixedProfile,
      FinFourFullDebtCommonPrefixResponse.targetTail,
      FinFourFullDebtCommonPrefixResponse.survival_eq_jointSurvival] using
      literalRootStack_outcomeMass_le_one_sub_survival_mul
        (data.roots rank) (data.targetTail rank) outcome

/-- The copied target terminal laws converge as a finite function. -/
theorem targetPrefixed_law_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification) :
    Tendsto (fun rank ↦ quittingTerminalOutcomeMass reward
      (data.targetPrefixedProfile rank)) atTop (nhds base.targetPoint.2) := by
  exact tendsto_pi_nhds.mpr data.targetPrefixed_outcomeMass_tendsto

/-- The copied target profiles converge in the complete joint semantic/law
topology expected by source-faithful causalization. -/
theorem targetPrefixed_joint_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward (data.targetPrefixedProfile rank),
        quittingTerminalOutcomeMass reward (data.targetPrefixedProfile rank)))
      atTop (nhds base.targetPoint) := by
  have hpayoff : Tendsto (fun rank who ↦ quittingTerminalPayoff reward
      (data.targetPrefixedProfile rank) who) atTop
      (nhds base.targetPoint.1.1) :=
    tendsto_pi_nhds.mpr data.targetPrefixed_payoff_tendsto
  have hcap : Tendsto (fun rank who ↦ quittingContinuationBestResponseValue
      reward (data.targetPrefixedProfile rank) who) atTop
      (nhds base.targetPoint.1.2) :=
    tendsto_pi_nhds.mpr data.targetPrefixed_cap_tendsto
  exact (hpayoff.prodMk_nhds hcap).prodMk_nhds
    data.targetPrefixed_law_tendsto

/-- The positive minimum target law has one fixed positive finite atom. -/
theorem exists_targetTerminalMass_pos
    (_data : FinFourFullDebtCommonPrefixResponse compactification) :
    ∃ terminal : {S : Finset (Fin 4) // S.Nonempty},
      0 < base.targetPoint.2 (some terminal) := by
  exact exists_positive_finiteLawAtom_of_finFourHardResidual_minimum
    reward bound source.residual base.targetPoint base.targetPoint_mem
      minimumTarget.target_is_globalMinimum

/-- Literal weak paired-family input.  The identity selector retains every
node-5 chord/target row, while causalization may choose fresh positive dates. -/
def toPairedMinimumChronologyData
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (hterminal : 0 < base.targetPoint.2 (some terminal)) :
    FinFourPairedMinimumChronologyData source where
  targetPoint := base.targetPoint
  targetPoint_mem := base.targetPoint_mem
  targetDebtSum_eq_source := minimumTarget.targetDebtSum_eq_source
  terminal := terminal
  terminalMass_pos := hterminal
  sourceProfiles := data.chordPrefixedProfile
  targetProfiles := data.targetPrefixedProfile
  selector := id
  selector_strictMono := strictMono_id
  mover := base.response.mover
  response := fun rank ↦ data.targetPrefixedProfile rank base.response.mover
  target_eq_update := fun rank ↦ data.targetPrefixed_eq_update rank
  target_tendsto := data.targetPrefixed_joint_tendsto

end FinFourFullDebtCommonPrefixResponse

/-- The genuinely additional datum needed to turn the copied target family
into a fixed-mark source-faithful causalization. -/
structure FinFourFullDebtTargetPrefixedMarkedFloor
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {base : FinFourFullDebtCapBandTargetCompactification source M}
    {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    {compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1}
    (data : FinFourFullDebtCommonPrefixResponse compactification) where
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  mark : ℕ → ℕ
  massFloor : ℝ
  massFloor_pos : 0 < massFloor
  marked_mass_floor : ∀ rank,
    massFloor ≤ quittingStageCoalitionMass reward
      (data.targetPrefixedProfile rank) (mark rank) terminal

namespace FinFourFullDebtTargetPrefixedMarkedFloor

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {base : FinFourFullDebtCapBandTargetCompactification source M}
  {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
  {compactification : FinFourFullDebtFixedWeightChordCompactification
    base minimumTarget weight hweight0 hweight1}
  {data : FinFourFullDebtCommonPrefixResponse compactification}

/-- Literal paired-family input to the generic same-residual compiler. -/
def toPairedMinimumSourceData
    (marked : FinFourFullDebtTargetPrefixedMarkedFloor data) :
    FinFourPairedMinimumSourceData source where
  targetPoint := base.targetPoint
  targetPoint_mem := base.targetPoint_mem
  targetDebtSum_eq_source := minimumTarget.targetDebtSum_eq_source
  terminal := marked.terminal
  sourceProfiles := data.chordPrefixedProfile
  targetProfiles := data.targetPrefixedProfile
  selector := id
  selector_strictMono := strictMono_id
  mover := base.response.mover
  response := fun rank ↦ data.targetPrefixedProfile rank base.response.mover
  target_eq_update := fun rank ↦ data.targetPrefixed_eq_update rank
  mark := marked.mark
  massFloor := marked.massFloor
  massFloor_pos := marked.massFloor_pos
  marked_mass_floor := marked.marked_mass_floor
  target_tendsto := data.targetPrefixed_joint_tendsto

end FinFourFullDebtTargetPrefixedMarkedFloor

/-- Conditional full-debt node-5 to node-6 compilation.  The output retains
the literal paired origin edge and the inherited target support bound. -/
structure FinFourFullDebtPairedSourceRegeneration
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {base : FinFourFullDebtCapBandTargetCompactification source M}
    {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    {compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1}
    {data : FinFourFullDebtCommonPrefixResponse compactification}
    (marked : FinFourFullDebtTargetPrefixedMarkedFloor data) where
  regeneration : FinFourPairedSameResidualSourceRegeneration
    marked.toPairedMinimumSourceData
  targetSupport_nonempty :
    (quittingPositiveDebtSupport base.targetPoint.1).Nonempty
  targetSupport_card_le_three :
    (quittingPositiveDebtSupport base.targetPoint.1).card ≤ 3

/-- Construct the conditional adapter, without designating its origin edge as
a renewable child. -/
theorem nonempty_finFourFullDebtPairedSourceRegeneration
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {base : FinFourFullDebtCapBandTargetCompactification source M}
    {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    {compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1}
    {data : FinFourFullDebtCommonPrefixResponse compactification}
    (marked : FinFourFullDebtTargetPrefixedMarkedFloor data) :
    Nonempty (FinFourFullDebtPairedSourceRegeneration marked) := by
  obtain ⟨regeneration⟩ :=
    nonempty_finFourPairedSameResidualSourceRegeneration
      marked.toPairedMinimumSourceData
  exact ⟨{
    regeneration := regeneration
    targetSupport_nonempty :=
      compactification.targetSupport_nonempty_and_card_le_three.1
    targetSupport_card_le_three :=
      compactification.targetSupport_nonempty_and_card_le_three.2
  }⟩

/-! ## Weak chronology adapter from the positive target atom -/

/-- Full-debt node-5 to node-6 chronology regeneration.  The public paired
chronology retains the literal chord/target response rows.  The producer is
packaged independently at the same point with the same incoming residual; no
identity with the producer's internal chronology is asserted. -/
structure FinFourFullDebtPairedSourceChronologyRegeneration
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {base : FinFourFullDebtCapBandTargetCompactification source M}
    {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    {compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1}
    (data : FinFourFullDebtCommonPrefixResponse compactification) where
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  terminalMass_pos : 0 < base.targetPoint.2 (some terminal)
  regeneration : FinFourPairedSameResidualSourceChronologyRegeneration
    (data.toPairedMinimumChronologyData terminal terminalMass_pos)
  targetSupport_nonempty :
    (quittingPositiveDebtSupport base.targetPoint.1).Nonempty
  targetSupport_card_le_three :
    (quittingPositiveDebtSupport base.targetPoint.1).card ≤ 3

namespace FinFourFullDebtPairedSourceChronologyRegeneration

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {base : FinFourFullDebtCapBandTargetCompactification source M}
  {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
  {compactification : FinFourFullDebtFixedWeightChordCompactification
    base minimumTarget weight hweight0 hweight1}
  {data : FinFourFullDebtCommonPrefixResponse compactification}

/-- Independently packaged target producer. -/
def producer
    (result : FinFourFullDebtPairedSourceChronologyRegeneration data) :
    FinFourMinimumAtomProducer reward bound :=
  result.regeneration.producer

@[simp] theorem producer_residual_eq
    (result : FinFourFullDebtPairedSourceChronologyRegeneration data) :
    result.producer.residual = source.residual := rfl

@[simp] theorem producer_point_eq
    (result : FinFourFullDebtPairedSourceChronologyRegeneration data) :
    result.producer.point = base.targetPoint := rfl

/-- Paired chronology retaining the literal node-5 target profiles. -/
def pairedChronology
    (result : FinFourFullDebtPairedSourceChronologyRegeneration data) :
    FinFourMinimumAtomChronology result.producer :=
  result.regeneration.pairedChronology

@[simp] theorem pairedChronology_profile_eq
    (result : FinFourFullDebtPairedSourceChronologyRegeneration data)
    (rank : ℕ) :
    result.pairedChronology.profiles rank =
      data.targetPrefixedProfile rank := rfl

/-- Every sufficiently late selected date has positive mass; no uniform
rankwise floor is claimed. -/
theorem eventually_pairedChronology_mark_pos
    (result : FinFourFullDebtPairedSourceChronologyRegeneration data) :
    ∀ᶠ rank in atTop,
      0 < quittingStageCoalitionMass reward
        (result.pairedChronology.profiles rank)
        (result.pairedChronology.mark rank) result.terminal := by
  exact result.regeneration.eventually_pairedChronology_mark_pos

/-- Literal chord-to-target origin edge at one public chronology rank. -/
def originEdge
    (result : FinFourFullDebtPairedSourceChronologyRegeneration data)
    (rank : ℕ) :
    FinFourPairedSameResidualSourceChronologyRegeneration.OriginEdge
      result.regeneration rank :=
  result.regeneration.originEdge rank

end FinFourFullDebtPairedSourceChronologyRegeneration

/-- Construct the weak full-debt chronology adapter directly from the fixed
positive atom of the target minimum law. -/
theorem nonempty_finFourFullDebtPairedSourceChronologyRegeneration
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {base : FinFourFullDebtCapBandTargetCompactification source M}
    {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    {compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1}
    (data : FinFourFullDebtCommonPrefixResponse compactification) :
    Nonempty (FinFourFullDebtPairedSourceChronologyRegeneration data) := by
  obtain ⟨terminal, hterminal⟩ := data.exists_targetTerminalMass_pos
  obtain ⟨regeneration⟩ :=
    nonempty_finFourPairedSameResidualSourceChronologyRegeneration
      (data.toPairedMinimumChronologyData terminal hterminal)
  exact ⟨{
    terminal := terminal
    terminalMass_pos := hterminal
    regeneration := regeneration
    targetSupport_nonempty :=
      compactification.targetSupport_nonempty_and_card_le_three.1
    targetSupport_card_le_three :=
      compactification.targetSupport_nonempty_and_card_le_three.2
  }⟩

end GameTheory
