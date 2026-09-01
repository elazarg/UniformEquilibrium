import Research.Quitting.FinFourProducerAtlas.MinimumSingletonClockCompression
import Research.Quitting.FinFourProducerAtlas.SamePointMinimumAtomProducerRegeneration
import Research.Quitting.ExactPrefixAtomTransport
import Research.Quitting.SourceFaithfulMinimumLawCausalization

/-!
# Paired same-residual source regeneration

A supplied pair of source and unilateral-response profile families is retained
on one strict reindex.  If the target family converges jointly to a positive
global-minimum law point and carries one uniformly positive marked atom, its
literal profiles and dates admit a source-faithful causalization.  The target
is then packaged as a complete Fin4 minimum-atom producer with exactly the
incoming hard residual.

Unlike a law-point-only regeneration, the result also retains a rankwise
origin edge.  Each edge records the common source index, cap--Nash word,
causal cutoff, marked date, paired prefixed profiles, unilateral update, and
the exact payoff and terminal-law transports through the common word.

This is a compiler for supplied paired families.  It does not produce those
families and asserts no renewal, terminal alternative, or uniform equilibrium.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

private theorem quittingLiteralRootStackProfile_apply_eq_of_tail_paired
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

private theorem update_eq_target_of_opponent_eq_paired
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (source target : (quittingGame reward).BehaviorProfile) (mover : Fin 4)
    (hopponent : ∀ other ≠ mover, target other = source other) :
    Function.update source mover (target mover) = target := by
  funext other
  by_cases hother : other = mover
  · subst other
    simp
  · rw [Function.update_of_ne hother]
    exact (hopponent other hother).symm

/-- Supplied paired source and target families converging, on one strict
reindex, to a positive global-minimum target law point. -/
structure FinFourPairedMinimumSourceData
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  targetPoint : QuittingTerminalSemanticLawPoint (Fin 4)
  targetPoint_mem : targetPoint ∈ quittingTerminalSemanticLawCarrier reward
  targetDebtSum_eq_source :
    quittingTerminalSemanticDebtSum targetPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  sourceProfiles : ℕ → (quittingGame reward).BehaviorProfile
  targetProfiles : ℕ → (quittingGame reward).BehaviorProfile
  selector : ℕ → ℕ
  selector_strictMono : StrictMono selector
  mover : Fin 4
  response : ℕ → (quittingGame reward).BehaviorStrategy mover
  target_eq_update : ∀ rank,
    targetProfiles (selector rank) =
      Function.update (sourceProfiles (selector rank)) mover
        (response (selector rank))
  mark : ℕ → ℕ
  massFloor : ℝ
  massFloor_pos : 0 < massFloor
  marked_mass_floor : ∀ rank,
    massFloor ≤ quittingStageCoalitionMass reward
      (targetProfiles (selector rank)) (mark (selector rank)) terminal
  target_tendsto : Tendsto (fun rank ↦
    (quittingTerminalSemanticPair reward (targetProfiles (selector rank)),
      quittingTerminalOutcomeMass reward (targetProfiles (selector rank))))
    atTop (nhds targetPoint)

namespace FinFourPairedMinimumSourceData

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The supplied target point is a global minimum. -/
theorem target_globalMinimum
    (data : FinFourPairedMinimumSourceData source)
    (candidate : QuittingTerminalSemanticPair (Fin 4))
    (hcandidate : candidate ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalSemanticDebtSum data.targetPoint.1 ≤
      quittingTerminalSemanticDebtSum candidate := by
  rw [data.targetDebtSum_eq_source]
  exact source.minimum candidate hcandidate

/-- The supplied target point realizes the literal global debt infimum. -/
theorem targetDebtSum_eq_inf
    (data : FinFourPairedMinimumSourceData source) :
    quittingTerminalSemanticDebtSum data.targetPoint.1 =
      quittingTerminalDebtSumInf reward :=
  data.targetDebtSum_eq_source.trans source.debt_eq_inf

/-- The supplied target minimum has strictly positive total debt. -/
theorem targetDebtSum_pos
    (data : FinFourPairedMinimumSourceData source) :
    0 < quittingTerminalSemanticDebtSum data.targetPoint.1 := by
  rw [data.targetDebtSum_eq_source]
  exact source.minimumDebt_pos

end FinFourPairedMinimumSourceData

/-- A source-faithful causalization of the supplied target family. -/
structure FinFourPairedSameResidualSourceRegeneration
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (data : FinFourPairedMinimumSourceData source) where
  causalization : QuittingSourceFaithfulMinimumCausalization
    data.targetPoint data.terminal
    (fun rank ↦ data.targetProfiles (data.selector rank))
    (fun rank ↦ data.mark (data.selector rank)) data.massFloor

namespace FinFourPairedSameResidualSourceRegeneration

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {data : FinFourPairedMinimumSourceData source}

/-- The causal atom built on the literal selected target profiles and dates. -/
def atom (regeneration : FinFourPairedSameResidualSourceRegeneration data) :
    QuittingMinimumLawCausalSuffixAtom reward data.targetPoint where
  terminal := data.terminal
  terminalMass_pos := regeneration.causalization.terminalMass_pos
  chronology :=
    ⟨(fun rank ↦ data.targetProfiles (data.selector rank)),
      regeneration.causalization.cutoff,
      (fun rank ↦ data.mark (data.selector rank)),
      regeneration.causalization.roots,
      regeneration.causalization.profiles_tendsto,
      regeneration.causalization.roots_length,
      regeneration.causalization.roots_nash,
      regeneration.causalization.prefix_debt_tendsto,
      regeneration.causalization.causal⟩

/-- Complete target producer with the incoming hard residual unchanged. -/
def next (regeneration : FinFourPairedSameResidualSourceRegeneration data) :
    FinFourMinimumAtomProducer reward bound where
  residual := source.residual
  point := data.targetPoint
  point_mem := data.targetPoint_mem
  semantic_mem := terminalSemanticLawCarrier_fst_mem_carrier
    data.targetPoint data.targetPoint_mem
  minimum := data.target_globalMinimum
  inf_pos := source.inf_pos
  debt_eq_inf := data.targetDebtSum_eq_inf
  atom := regeneration.atom

/-- Public chronology of the regenerated target producer. -/
def chronology
    (regeneration : FinFourPairedSameResidualSourceRegeneration data) :
    FinFourMinimumAtomChronology regeneration.next where
  profiles := fun rank ↦ data.targetProfiles (data.selector rank)
  cutoff := regeneration.causalization.cutoff
  mark := fun rank ↦ data.mark (data.selector rank)
  roots := regeneration.causalization.roots
  profiles_tendsto := regeneration.causalization.profiles_tendsto
  roots_length := regeneration.causalization.roots_length
  roots_nash := regeneration.causalization.roots_nash
  prefix_debt_tendsto := by
    simpa only [QuittingNonsingletonMinimumLawTransfer.prefixedProfile] using
      regeneration.causalization.prefix_debt_tendsto
  causal := regeneration.causalization.causal

@[simp] theorem next_residual_eq
    (regeneration : FinFourPairedSameResidualSourceRegeneration data) :
    regeneration.next.residual = source.residual := rfl

@[simp] theorem next_point_eq
    (regeneration : FinFourPairedSameResidualSourceRegeneration data) :
    regeneration.next.point = data.targetPoint := rfl

/-- One retained source-to-target edge at a displayed causal rank. -/
structure OriginEdge
    (regeneration : FinFourPairedSameResidualSourceRegeneration data)
    (rank : ℕ) where
  sourceIndex : ℕ
  sourceIndex_eq : sourceIndex = data.selector rank
  roots : List (Fin 4 → PMF Bool)
  roots_eq : roots = regeneration.causalization.roots rank
  cut : ℕ
  cut_eq : cut = regeneration.causalization.cutoff rank
  markedDate : ℕ
  markedDate_eq : markedDate = data.mark sourceIndex
  sourcePrefixedProfile : (quittingGame reward).BehaviorProfile
  sourcePrefixedProfile_eq : sourcePrefixedProfile =
    quittingLiteralRootStackProfile reward roots
      (data.sourceProfiles sourceIndex)
  targetPrefixedProfile : (quittingGame reward).BehaviorProfile
  targetPrefixedProfile_eq : targetPrefixedProfile =
    quittingLiteralRootStackProfile reward roots
      (data.targetProfiles sourceIndex)
  targetPrefixed_eq_update : targetPrefixedProfile =
    Function.update sourcePrefixedProfile data.mover
      (targetPrefixedProfile data.mover)

namespace OriginEdge

/-- The source suffix retained by an origin edge. -/
def sourceTail
    {regeneration : FinFourPairedSameResidualSourceRegeneration data}
    {rank : ℕ} (edge : OriginEdge regeneration rank) :
    (quittingGame reward).BehaviorProfile :=
  data.sourceProfiles edge.sourceIndex

/-- The target suffix retained by an origin edge. -/
def targetTail
    {regeneration : FinFourPairedSameResidualSourceRegeneration data}
    {rank : ℕ} (edge : OriginEdge regeneration rank) :
    (quittingGame reward).BehaviorProfile :=
  data.targetProfiles edge.sourceIndex

/-- The target suffix is the literal supplied unilateral response. -/
theorem targetTail_eq_update
    {regeneration : FinFourPairedSameResidualSourceRegeneration data}
    {rank : ℕ} (edge : OriginEdge regeneration rank) :
    edge.targetTail = Function.update edge.sourceTail data.mover
      (data.response edge.sourceIndex) := by
  rw [targetTail, sourceTail, edge.sourceIndex_eq]
  exact data.target_eq_update rank

/-- The prefixed target's prescribed payoff is the payoff of the recorded
literal unilateral update. -/
theorem targetPayoff_eq_update
    {regeneration : FinFourPairedSameResidualSourceRegeneration data}
    {rank : ℕ} (edge : OriginEdge regeneration rank) (who : Fin 4) :
    quittingTerminalPayoff reward edge.targetPrefixedProfile who =
      quittingTerminalPayoff reward
        (Function.update edge.sourcePrefixedProfile data.mover
          (edge.targetPrefixedProfile data.mover)) who := by
  exact congrArg
    (fun profile ↦ quittingTerminalPayoff reward profile who)
    edge.targetPrefixed_eq_update

/-- Every prescribed payoff difference is transported exactly through the
recorded common word. -/
theorem payoff_sub_eq_continueProduct_mul
    {regeneration : FinFourPairedSameResidualSourceRegeneration data}
    {rank : ℕ} (edge : OriginEdge regeneration rank) (who : Fin 4) :
    quittingTerminalPayoff reward edge.targetPrefixedProfile who -
        quittingTerminalPayoff reward edge.sourcePrefixedProfile who =
      quittingCapNashStackContinueProduct edge.roots *
        (quittingTerminalPayoff reward edge.targetTail who -
          quittingTerminalPayoff reward edge.sourceTail who) := by
  rw [edge.targetPrefixedProfile_eq, edge.sourcePrefixedProfile_eq]
  exact quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul
    (reward := reward) edge.roots edge.targetTail edge.sourceTail who

/-- Every terminal-law coordinate difference is transported exactly through
the recorded common word. -/
theorem law_sub_eq_continueProduct_mul
    {regeneration : FinFourPairedSameResidualSourceRegeneration data}
    {rank : ℕ} (edge : OriginEdge regeneration rank)
    (outcome : QuittingTerminalOutcome (Fin 4)) :
    quittingTerminalOutcomeMass reward edge.targetPrefixedProfile outcome -
        quittingTerminalOutcomeMass reward edge.sourcePrefixedProfile outcome =
      quittingCapNashStackContinueProduct edge.roots *
        (quittingTerminalOutcomeMass reward edge.targetTail outcome -
          quittingTerminalOutcomeMass reward edge.sourceTail outcome) := by
  rw [edge.targetPrefixedProfile_eq, edge.sourcePrefixedProfile_eq]
  exact quittingTerminalOutcomeMass_literalRootStack_sub_eq
    reward edge.roots edge.targetTail edge.sourceTail outcome

end OriginEdge

/-- The literal one-use origin edge at every causal rank. -/
def originEdge
    (regeneration : FinFourPairedSameResidualSourceRegeneration data)
    (rank : ℕ) : OriginEdge regeneration rank := by
  let sourceIndex := data.selector rank
  let roots := regeneration.causalization.roots rank
  let sourcePrefixedProfile := quittingLiteralRootStackProfile reward roots
    (data.sourceProfiles sourceIndex)
  let targetPrefixedProfile := quittingLiteralRootStackProfile reward roots
    (data.targetProfiles sourceIndex)
  have hne : ∀ other ≠ data.mover,
      targetPrefixedProfile other = sourcePrefixedProfile other := by
    intro other hother
    unfold targetPrefixedProfile sourcePrefixedProfile
    apply quittingLiteralRootStackProfile_apply_eq_of_tail_paired
    rw [data.target_eq_update rank, Function.update_of_ne hother]
  have hupdate : targetPrefixedProfile = Function.update sourcePrefixedProfile
      data.mover (targetPrefixedProfile data.mover) := by
    symm
    exact update_eq_target_of_opponent_eq_paired
      sourcePrefixedProfile targetPrefixedProfile data.mover hne
  exact {
    sourceIndex := sourceIndex
    sourceIndex_eq := rfl
    roots := roots
    roots_eq := rfl
    cut := regeneration.causalization.cutoff rank
    cut_eq := rfl
    markedDate := data.mark sourceIndex
    markedDate_eq := rfl
    sourcePrefixedProfile := sourcePrefixedProfile
    sourcePrefixedProfile_eq := rfl
    targetPrefixedProfile := targetPrefixedProfile
    targetPrefixedProfile_eq := rfl
    targetPrefixed_eq_update := hupdate
  }

end FinFourPairedSameResidualSourceRegeneration

/-- Construct the paired same-residual regeneration without replacing the
supplied selected target profiles or their marked dates. -/
theorem nonempty_finFourPairedSameResidualSourceRegeneration
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (data : FinFourPairedMinimumSourceData source) :
    Nonempty (FinFourPairedSameResidualSourceRegeneration data) := by
  obtain ⟨causalization⟩ := nonempty_sourceFaithfulMinimumCausalization
    data.targetPoint data.terminal
    (fun rank ↦ data.targetProfiles (data.selector rank))
    (fun rank ↦ data.mark (data.selector rank)) data.massFloor
    data.targetPoint_mem data.target_tendsto data.target_globalMinimum
    data.targetDebtSum_eq_inf source.inf_pos data.massFloor_pos
    data.marked_mass_floor
  exact ⟨⟨causalization⟩⟩

/-! ## Profile-faithful chronology regeneration without a uniform date floor -/

/-- Supplied paired families at a positive minimum-law atom.  The target
profiles are kept literally, while their positive marked dates may be
selected afresh from finite terminal-mass windows. -/
structure FinFourPairedMinimumChronologyData
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  targetPoint : QuittingTerminalSemanticLawPoint (Fin 4)
  targetPoint_mem : targetPoint ∈ quittingTerminalSemanticLawCarrier reward
  targetDebtSum_eq_source :
    quittingTerminalSemanticDebtSum targetPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  terminalMass_pos : 0 < targetPoint.2 (some terminal)
  sourceProfiles : ℕ → (quittingGame reward).BehaviorProfile
  targetProfiles : ℕ → (quittingGame reward).BehaviorProfile
  selector : ℕ → ℕ
  selector_strictMono : StrictMono selector
  mover : Fin 4
  response : ℕ → (quittingGame reward).BehaviorStrategy mover
  target_eq_update : ∀ rank,
    targetProfiles (selector rank) =
      Function.update (sourceProfiles (selector rank)) mover
        (response (selector rank))
  target_tendsto : Tendsto (fun rank ↦
    (quittingTerminalSemanticPair reward (targetProfiles (selector rank)),
      quittingTerminalOutcomeMass reward (targetProfiles (selector rank))))
    atTop (nhds targetPoint)

namespace FinFourPairedMinimumChronologyData

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

theorem target_globalMinimum
    (data : FinFourPairedMinimumChronologyData source)
    (candidate : QuittingTerminalSemanticPair (Fin 4))
    (hcandidate : candidate ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalSemanticDebtSum data.targetPoint.1 ≤
      quittingTerminalSemanticDebtSum candidate := by
  rw [data.targetDebtSum_eq_source]
  exact source.minimum candidate hcandidate

theorem targetDebtSum_eq_inf
    (data : FinFourPairedMinimumChronologyData source) :
    quittingTerminalSemanticDebtSum data.targetPoint.1 =
      quittingTerminalDebtSumInf reward :=
  data.targetDebtSum_eq_source.trans source.debt_eq_inf

end FinFourPairedMinimumChronologyData

/-- A separately retained paired chronology and same-point producer.  The
producer is packaged by the existing same-point constructor; no equality is
asserted between its internal chronology and `causalization`. -/
structure FinFourPairedSameResidualSourceChronologyRegeneration
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (data : FinFourPairedMinimumChronologyData source) where
  causalization : QuittingSourceFaithfulMinimumCausalChronology
    data.targetPoint data.terminal
      (fun rank ↦ data.targetProfiles (data.selector rank))

namespace FinFourPairedSameResidualSourceChronologyRegeneration

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {data : FinFourPairedMinimumChronologyData source}

/-- Independently packaged complete producer at the same target law point. -/
def producer
    (_regeneration : FinFourPairedSameResidualSourceChronologyRegeneration data) :
    FinFourMinimumAtomProducer reward bound :=
  source.regeneratedAtLawPoint data.targetPoint data.terminal
    data.targetPoint_mem data.targetDebtSum_eq_source data.terminalMass_pos

@[simp] theorem producer_residual_eq
    (regeneration : FinFourPairedSameResidualSourceChronologyRegeneration data) :
    regeneration.producer.residual = source.residual := rfl

@[simp] theorem producer_point_eq
    (regeneration : FinFourPairedSameResidualSourceChronologyRegeneration data) :
    regeneration.producer.point = data.targetPoint := rfl

/-- Public paired chronology, typed against the independently packaged
producer but retaining the supplied target profiles literally. -/
def pairedChronology
    (regeneration : FinFourPairedSameResidualSourceChronologyRegeneration data) :
    FinFourMinimumAtomChronology regeneration.producer where
  profiles := fun rank ↦ data.targetProfiles (data.selector rank)
  cutoff := regeneration.causalization.cutoff
  mark := regeneration.causalization.mark
  roots := regeneration.causalization.roots
  profiles_tendsto := regeneration.causalization.profiles_tendsto
  roots_length := regeneration.causalization.roots_length
  roots_nash := regeneration.causalization.roots_nash
  prefix_debt_tendsto := by
    simpa only [QuittingNonsingletonMinimumLawTransfer.prefixedProfile] using
      regeneration.causalization.prefix_debt_tendsto
  causal := regeneration.causalization.causal

/-- The paired chronology keeps every selected target profile literally. -/
@[simp] theorem pairedChronology_profile_eq
    (regeneration : FinFourPairedSameResidualSourceChronologyRegeneration data)
    (rank : ℕ) :
    regeneration.pairedChronology.profiles rank =
      data.targetProfiles (data.selector rank) := rfl

/-- The selected date is positive eventually; no uniform rankwise lower
bound is asserted. -/
theorem eventually_pairedChronology_mark_pos
    (regeneration : FinFourPairedSameResidualSourceChronologyRegeneration data) :
    ∀ᶠ rank in atTop,
      0 < quittingStageCoalitionMass reward
        (regeneration.pairedChronology.profiles rank)
        (regeneration.pairedChronology.mark rank) data.terminal := by
  filter_upwards [regeneration.causalization.causal] with rank hrank
  exact hrank.2.2.1

/-- One literal paired origin edge on the same selected index and causal
word. -/
structure OriginEdge
    (regeneration : FinFourPairedSameResidualSourceChronologyRegeneration data)
    (rank : ℕ) where
  sourceIndex : ℕ
  sourceIndex_eq : sourceIndex = data.selector rank
  cut : ℕ
  cut_eq : cut = regeneration.causalization.cutoff rank
  mark : ℕ
  mark_eq : mark = regeneration.causalization.mark rank
  sourcePrefixedProfile : (quittingGame reward).BehaviorProfile
  sourcePrefixedProfile_eq : sourcePrefixedProfile =
    quittingLiteralRootStackProfile reward
      (regeneration.causalization.roots rank)
      (data.sourceProfiles sourceIndex)
  targetPrefixedProfile : (quittingGame reward).BehaviorProfile
  targetPrefixedProfile_eq : targetPrefixedProfile =
    quittingLiteralRootStackProfile reward
      (regeneration.causalization.roots rank)
      (data.targetProfiles sourceIndex)
  targetTail_eq_update : data.targetProfiles sourceIndex =
    Function.update (data.sourceProfiles sourceIndex) data.mover
      (data.response sourceIndex)
  targetPrefixed_eq_update : targetPrefixedProfile =
    Function.update sourcePrefixedProfile data.mover
      (targetPrefixedProfile data.mover)

/-- The literal paired origin edge at every rank. -/
def originEdge
    (regeneration : FinFourPairedSameResidualSourceChronologyRegeneration data)
    (rank : ℕ) : OriginEdge regeneration rank := by
  let index := data.selector rank
  let roots := regeneration.causalization.roots rank
  let sourcePrefixed := quittingLiteralRootStackProfile reward roots
    (data.sourceProfiles index)
  let targetPrefixed := quittingLiteralRootStackProfile reward roots
    (data.targetProfiles index)
  have hne : ∀ other ≠ data.mover,
      targetPrefixed other = sourcePrefixed other := by
    intro other hother
    unfold targetPrefixed sourcePrefixed
    apply quittingLiteralRootStackProfile_apply_eq_of_tail_paired
    rw [data.target_eq_update rank, Function.update_of_ne hother]
  exact {
    sourceIndex := index
    sourceIndex_eq := rfl
    cut := regeneration.causalization.cutoff rank
    cut_eq := rfl
    mark := regeneration.causalization.mark rank
    mark_eq := rfl
    sourcePrefixedProfile := sourcePrefixed
    sourcePrefixedProfile_eq := rfl
    targetPrefixedProfile := targetPrefixed
    targetPrefixedProfile_eq := rfl
    targetTail_eq_update := data.target_eq_update rank
    targetPrefixed_eq_update := by
      symm
      exact update_eq_target_of_opponent_eq_paired
        sourcePrefixed targetPrefixed data.mover hne
  }

end FinFourPairedSameResidualSourceChronologyRegeneration

/-- Construct the weaker profile-faithful chronology regeneration. -/
theorem nonempty_finFourPairedSameResidualSourceChronologyRegeneration
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (data : FinFourPairedMinimumChronologyData source) :
    Nonempty (FinFourPairedSameResidualSourceChronologyRegeneration data) := by
  obtain ⟨causalization⟩ := nonempty_sourceFaithfulMinimumCausalChronology
    data.targetPoint data.terminal
    (fun rank ↦ data.targetProfiles (data.selector rank))
    data.targetPoint_mem data.target_tendsto data.target_globalMinimum
    data.targetDebtSum_eq_inf source.inf_pos data.terminalMass_pos
  exact ⟨⟨causalization⟩⟩

end GameTheory
