/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.FiniteLabelLiminfExtraction
import UniformEquilibrium.Quitting.Classification.Existence.PrioritizedAttachmentSingletonDefect
import UniformEquilibrium.Quitting.Classification.PreemptionTransport
import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockMonopoly
import UniformEquilibrium.Quitting.Projective.SignedProjectiveLasso

/-!
# Source-matched boundary of the prioritized preemption cycle

The augmented preemption cycle forced by a prioritized refined source is a
table-level consequence.  By itself it forgets which positive singleton came
from the retained all-Continue source or positive-singleton defect.  This file
keeps that first edge attached to its source and then uses cofinality and
finiteness to make the source owner and its first preemptor constant along a
sequence of scales tending to zero.

This is the strongest direct finite extraction available from the current
interfaces.  It is not an AGKRS branch: the projective and anchored cyclic
compilers additionally require roots, Bellman values, rationality, and
support inequalities indexed by the cycle phases.  None of those fields is
attached to the later edges of the augmented table cycle here.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingPrioritizedRefinedSourceResidualAt

/-- Provenance of the positive singleton which starts a strict preemption
edge.  In the defect arm the owner is literally the selected suffix-defect
player; in the all-Continue arm it is selected from the retained source's
nonzero-solo certificate. -/
inductive QuittingPrioritizedPreemptionSeedProvenanceAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (delta : ℝ) (owner : ι) : Prop
  | allContinue
      (source : AllContinueSourceAt reward delta)
  | positiveSingleton
      (defect : PositiveSingletonDefectAt reward delta)
      (owner_eq : defect.defect.some.defect.who = owner)

/-- A prioritized normal-form source together with a source-matched positive
singleton and its first strict solo preemption edge. -/
structure QuittingPrioritizedPreemptionSeedAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (delta : ℝ) where
  owner : ι
  other : ι
  owner_pos : 0 < quittingSoloReward reward owner owner
  other_ne_owner : other ≠ owner
  strictly_preempts :
    quittingSoloReward reward owner other <
      quittingSoloReward reward other other
  provenance :
    QuittingPrioritizedPreemptionSeedProvenanceAt reward delta owner

/-- The retained source data select the first preemption edge, rather than
only an unrelated eventual cycle of the augmented finite graph. -/
theorem nonempty_prioritizedPreemptionSeedAt
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (residual : QuittingPrioritizedRefinedSourceResidualAt reward delta)
    (hdelta : 0 < delta) :
    Nonempty (QuittingPrioritizedPreemptionSeedAt reward delta) := by
  rcases residual.allContinueSourceAt_or_positiveSingletonDefectAt hdelta with
    source | defect
  · obtain ⟨owner, howner, other, hother, hstrict⟩ :=
      source.exists_positiveSingleton_strictlyPreempted hdelta
    exact ⟨{
      owner := owner
      other := other
      owner_pos := howner
      other_ne_owner := hother
      strictly_preempts := hstrict
      provenance := .allContinue source }⟩
  · obtain ⟨other, hother, hstrict⟩ :=
      defect.exists_selectedSingleton_strictlyPreempted hdelta
    exact ⟨{
      owner := defect.defect.some.defect.who
      other := other
      owner_pos := defect.defect.some.defect.singleton_pos
      other_ne_owner := hother
      strictly_preempts := hstrict
      provenance := .positiveSingleton defect rfl }⟩

/-- A cofinal source-matched preemption boundary with one fixed ordered edge.
Every scale retains one of the two prioritized source arms; no source data are
reconstructed from the static edge. -/
structure QuittingCofinalPrioritizedPreemptionSeedSequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  owner : ι
  other : ι
  delta : ℕ → ℝ
  seed : ∀ n, QuittingPrioritizedPreemptionSeedAt reward (delta n)
  delta_pos : ∀ n, 0 < delta n
  delta_tendsto_zero : Tendsto delta atTop (nhds 0)
  owner_eq : ∀ n, (seed n).owner = owner
  other_eq : ∀ n, (seed n).other = other

namespace QuittingCofinalPrioritizedPreemptionSeedSequence

/-- The fixed source owner has a positive singleton self-reward. -/
theorem owner_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward) :
    0 < quittingSoloReward reward sequence.owner sequence.owner := by
  simpa [sequence.owner_eq 0] using (sequence.seed 0).owner_pos

/-- The fixed edge has distinct endpoints. -/
theorem other_ne_owner
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward) :
    sequence.other ≠ sequence.owner := by
  simpa [sequence.owner_eq 0, sequence.other_eq 0] using
    (sequence.seed 0).other_ne_owner

/-- The fixed ordered pair is a strict solo preemption edge. -/
theorem strictly_preempts
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward) :
    quittingSoloReward reward sequence.owner sequence.other <
      quittingSoloReward reward sequence.other sequence.other := by
  simpa [sequence.owner_eq 0, sequence.other_eq 0] using
    (sequence.seed 0).strictly_preempts

/-- The fixed seed edge's exact strict margin. -/
def preemptionGap
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward) : ℝ :=
  quittingSoloReward reward sequence.other sequence.other -
    quittingSoloReward reward sequence.owner sequence.other

/-- The source-matched fixed edge has a positive exact margin. -/
theorem preemptionGap_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward) :
    0 < sequence.preemptionGap := by
  unfold preemptionGap
  exact sub_pos.mpr sequence.strictly_preempts

/-- The strict seed edge, written at its exact positive gap. -/
theorem soloPreempts_preemptionGap
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward) :
    QuittingSoloPreempts reward sequence.preemptionGap
      sequence.owner sequence.other := by
  refine ⟨sequence.other_ne_owner, ?_⟩
  unfold preemptionGap
  linarith

/-- The retained source-matched edge has its full preemption gap as an
asymptotic lower bound on the inactive preemptor's endpoint defect along every
vanishing-hazard solo-root family whose continuation returns to the source
cross payoff. -/
theorem eventually_threshold_lt_endpointDifference
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward)
    {threshold : ℝ} (hthreshold : threshold < sequence.preemptionGap)
    (hazard : ℕ → PMF Bool) (tail : ℕ → Payoff ι)
    (hhazard : Tendsto (fun n ↦ (hazard n true).toReal) atTop (nhds 0))
    (htail : Tendsto (fun n ↦ tail n sequence.other) atTop
      (nhds (quittingSoloReward reward sequence.owner sequence.other))) :
    ∀ᶠ n in atTop, threshold <
      quittingRootEndpointDifference reward (tail n)
        (quittingSoloStationaryRoot sequence.owner (hazard n))
        sequence.other :=
  QuittingSoloPreempts.eventually_threshold_lt_endpointDifference
    sequence.soloPreempts_preemptionGap hthreshold hazard tail hhazard htail

/-- The fixed source edge rules out a cofinal solo-root lasso whenever the
owner's hazard vanishes and the preemptor's displayed continuation converges
to its payoff at the owner's solo row.  The preemptor's inactive Continue
defect then stays bounded away from zero while the retained scale vanishes.

This theorem does not rule out a signed lasso with multi-player roots or with
phase-dependent continuation values obtained from the retained source.  Those
are exactly the semantic fields still absent from the table-level edge. -/
theorem eventually_not_supportApproxNash_soloRoot_of_tendsto
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward)
    (hazard : ℕ → PMF Bool) (tail : ℕ → Payoff ι)
    (hhazard : Tendsto (fun n ↦ (hazard n true).toReal) atTop (nhds 0))
    (htail : Tendsto (fun n ↦ tail n sequence.other) atTop
      (nhds (quittingSoloReward reward sequence.owner sequence.other))) :
    ∀ᶠ n in atTop,
      ¬IsQuittingRootSupportApproxNash reward (tail n) (sequence.delta n)
        (quittingSoloStationaryRoot sequence.owner (hazard n)) :=
  QuittingSoloPreempts.eventually_not_supportApproxNash_soloRoot
    sequence.soloPreempts_preemptionGap sequence.preemptionGap_pos
      hazard tail sequence.delta hhazard htail sequence.delta_tendsto_zero

/-- In particular, the naive construction using the owner's solo payoff
vector as every continuation eventually fails support-Nash. -/
theorem eventually_not_supportApproxNash_soloTail_of_hazard_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward)
    (hazard : ℕ → PMF Bool)
    (hhazard : Tendsto (fun n ↦ (hazard n true).toReal) atTop (nhds 0)) :
    ∀ᶠ n in atTop,
      ¬IsQuittingRootSupportApproxNash reward
        (quittingSoloReward reward sequence.owner) (sequence.delta n)
        (quittingSoloStationaryRoot sequence.owner (hazard n)) := by
  apply sequence.eventually_not_supportApproxNash_soloRoot_of_tendsto
    hazard (fun _ ↦ quittingSoloReward reward sequence.owner) hhazard
  exact tendsto_const_nhds

/-- A period-one signed lasso whose only active root is the fixed seed owner
must pay the preemption gap either through the owner's hazard charge or twice
through the lasso error.  Support forces the phase value away from the owner's
solo row, while signed correction forces it back toward that row.

This excludes the period-one solo-root architecture at vanishing hazard and
error.  It does not constrain longer lassos or roots with several active
players. -/
theorem preemptionGap_le_hazardCharge_add_two_mul_error_of_periodOneSoloLasso
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward)
    {error : ℝ} (hazard : PMF Bool)
    (lasso : QuittingFiniteSignedProjectiveLasso reward 1 error)
    (hcycle : lasso.cycle 0 =
      quittingSoloStationaryRoot sequence.owner hazard)
    (hhazard : 0 < (hazard true).toReal) :
    sequence.preemptionGap ≤
      (hazard true).toReal *
          (sequence.preemptionGap + 2 * quittingRewardBound reward) +
        2 * error := by
  let target := quittingSoloReward reward sequence.owner
  have hcycleAll : lasso.cycle = fun _ ↦
      quittingSoloStationaryRoot sequence.owner hazard := by
    funext phase
    have hphase : phase = 0 := Subsingleton.elim _ _
    subst phase
    exact hcycle
  have habsorb : (∏ phase : Fin 1,
      quittingStationaryContinueMass (lasso.cycle phase)) < 1 := by
    rw [Fin.prod_univ_one, hcycle]
    exact quittingStationaryContinueMass_soloStationaryRoot_lt_one
      sequence.owner hazard hhazard
  have hpolicy : ∀ phase : Fin 1,
      (fun _ : Fin 1 ↦ target) phase =
        quittingRootSuccessorPayoff reward
          ((fun _ : Fin 1 ↦ target) (finRotate 1 phase))
          (lasso.cycle phase) := by
    intro phase
    rw [hcycleAll]
    exact (quittingRootSuccessorPayoff_soloStationaryRoot_self
      reward sequence.owner hazard).symm
  have hexact : lasso.exactValue 0 = target := by
    have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
      reward lasso.cycle (fun _ : Fin 1 ↦ target) hpolicy habsorb
    exact congrFun hvalue 0 |>.symm
  have hsupport : IsQuittingRootSupportApproxNash reward
      (lasso.value 0) error
      (quittingSoloStationaryRoot sequence.owner hazard) := by
    have hphase : finRotate 1 (0 : Fin 1) = 0 := Subsingleton.elim _ _
    simpa only [hphase, hcycle] using lasso.support 0
  have hdisplacement :=
    QuittingSoloPreempts.gap_sub_hazardCharge_sub_error_le_tailMismatch
      sequence.soloPreempts_preemptionGap hazard (lasso.value 0) hsupport
  have hclose := lasso.abs_value_sub_exactValue_le 0 sequence.other
  rw [hexact] at hclose
  dsimp only [target] at hclose
  linarith

/-- Consequently no cofinal family of period-one signed lassos can use only
the fixed seed owner's vanishing solo hazard at the retained half-scale.  A
successful signed bridge must change the phase architecture, not merely tune
this hazard more slowly. -/
theorem false_of_periodOneSoloLassos_of_hazard_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward)
    (hazard : ℕ → PMF Bool)
    (hhazardPos : ∀ n, 0 < (hazard n true).toReal)
    (hhazard : Tendsto (fun n ↦ (hazard n true).toReal) atTop (nhds 0))
    (lasso : ∀ n, QuittingFiniteSignedProjectiveLasso reward 1
      (sequence.delta n / 2))
    (hcycle : ∀ n, (lasso n).cycle 0 =
      quittingSoloStationaryRoot sequence.owner (hazard n)) : False := by
  let chargeScale := sequence.preemptionGap +
    2 * quittingRewardBound reward
  have hcharge : Tendsto
      (fun n ↦ (hazard n true).toReal * chargeScale) atTop (nhds 0) := by
    simpa only [zero_mul] using hhazard.mul_const chargeScale
  have htotal : Tendsto
      (fun n ↦ (hazard n true).toReal * chargeScale + sequence.delta n)
      atTop (nhds 0) := by
    simpa only [zero_add] using hcharge.add sequence.delta_tendsto_zero
  have hsmall : ∀ᶠ n in atTop,
      (hazard n true).toReal * chargeScale + sequence.delta n <
        sequence.preemptionGap :=
    (tendsto_order.1 htotal).2 sequence.preemptionGap
      sequence.preemptionGap_pos
  obtain ⟨n, hn⟩ := hsmall.exists
  have hbound :=
    sequence.preemptionGap_le_hazardCharge_add_two_mul_error_of_periodOneSoloLasso
      (hazard n) (lasso n) (hcycle n) (hhazardPos n)
  have hhalf : 2 * (sequence.delta n / 2) = sequence.delta n := by
    ring
  rw [hhalf] at hbound
  dsimp only [chargeScale] at hn
  linarith

/-- The provenance at every extracted scale retains failure of the
well-supported pointwise branch. -/
theorem seed_not_wellSupported
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward)
    (n : ℕ) :
    ¬QuittingWellSupportedAbsorbingSequenceAt reward (sequence.delta n) := by
  cases (sequence.seed n).provenance with
  | allContinue source => exact source.not_wellSupported
  | positiveSingleton defect _ => exact defect.not_wellSupported

end QuittingCofinalPrioritizedPreemptionSeedSequence

/-- Cofinal prioritized residuals yield a sequence of source-matched strict
preemption seeds whose scale tends to zero and whose ordered owner/preemptor
pair is fixed.  Finiteness is used only to extract an infinite fiber of the
ordered-pair label. -/
theorem
    nonempty_cofinalPrioritizedPreemptionSeedSequence_of_cofinallyPrioritized
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hcofinal : ∀ target : ℝ, 0 < target →
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ target ∧
        QuittingPrioritizedRefinedSourceResidualAt reward delta) :
    Nonempty (QuittingCofinalPrioritizedPreemptionSeedSequence reward) := by
  let target : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have htarget : ∀ n, 0 < target n := by
    intro n
    dsimp only [target]
    positivity
  let delta : ℕ → ℝ := fun n ↦ Classical.choose (hcofinal (target n) (htarget n))
  have hdeltaSpec : ∀ n,
      0 < delta n ∧ delta n ≤ target n ∧
        QuittingPrioritizedRefinedSourceResidualAt reward (delta n) := by
    intro n
    exact Classical.choose_spec (hcofinal (target n) (htarget n))
  let residual : ∀ n,
      QuittingPrioritizedRefinedSourceResidualAt reward (delta n) :=
    fun n ↦ (hdeltaSpec n).2.2
  let seed : ∀ n, QuittingPrioritizedPreemptionSeedAt reward (delta n) :=
    fun n ↦ Classical.choice
      ((residual n).nonempty_prioritizedPreemptionSeedAt (hdeltaSpec n).1)
  let label : ℕ → ι × ι := fun n ↦ ((seed n).owner, (seed n).other)
  obtain ⟨fixed, hfixedInfinite⟩ := Finite.exists_infinite_fiber label
  have hfrequent : ∃ᶠ n in atTop, label n = fixed := by
    rw [Nat.frequently_atTop_iff_infinite]
    have hinfinite : (label ⁻¹' ({fixed} : Set (ι × ι))).Infinite :=
      Set.infinite_coe_iff.mp hfixedInfinite
    convert hinfinite using 1
    ext n
    simp
  obtain ⟨subsequence, hsubsequence, hfixed⟩ :=
    extraction_of_frequently_atTop hfrequent
  have hdeltaTendsto : Tendsto (fun n ↦ delta (subsequence n)) atTop
      (nhds 0) := by
    have hupper : Tendsto (fun n ↦ target (subsequence n)) atTop (nhds 0) := by
      change Tendsto
        ((fun n : ℕ ↦ (1 : ℝ) / (n + 1)) ∘ subsequence) atTop (nhds 0)
      exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        hsubsequence.tendsto_atTop
    exact squeeze_zero
      (fun n ↦ (hdeltaSpec (subsequence n)).1.le)
      (fun n ↦ (hdeltaSpec (subsequence n)).2.1)
      hupper
  refine ⟨{
    owner := fixed.1
    other := fixed.2
    delta := fun n ↦ delta (subsequence n)
    seed := fun n ↦ seed (subsequence n)
    delta_pos := fun n ↦ (hdeltaSpec (subsequence n)).1
    delta_tendsto_zero := hdeltaTendsto
    owner_eq := ?_
    other_eq := ?_ }⟩
  · intro n
    exact congrArg Prod.fst (hfixed n)
  · intro n
    exact congrArg Prod.snd (hfixed n)

/-- At positive scale, a branch-valued consumer of a prioritized residual is
logically exactly an elimination of that residual.  The priority fields rule
out all three global branches already, so appending a static cycle cannot be
a fourth alternative: the source-matched boundary itself must be consumed. -/
theorem branchConclusion_iff_false
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (residual : QuittingPrioritizedRefinedSourceResidualAt reward delta)
    (hdelta : 0 < delta) :
    (QuittingStationaryεEquilibriumExistence reward ∨
      QuittingInstantPunishmentεEquilibriumExistence reward ∨
        QuittingWellSupportedAbsorbingSequenceExistence reward) ↔ False := by
  constructor
  · exact residual.not_stationary_or_instant_or_wellSupportedExistence hdelta
  · exact False.elim

/-- The exact semantic data absent from a static preemption cycle.  At every
cofinal source scale, a signed projective lasso would supply phase-indexed
roots and Bellman values, a rotation-uniform seam bound, support optimality,
punishment rationality, and a genuinely absorbing phase. -/
structure QuittingCofinalPrioritizedSignedLassoBridge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward) where
  period : ℕ → ℕ
  lasso : ∀ n, QuittingFiniteSignedProjectiveLasso reward (period n)
    (sequence.delta n / 2)

/-- The missing signed-lasso bridge would compile the cofinal seed boundary
to the well-supported form of AGKRS branch S.3. -/
theorem
    QuittingCofinalPrioritizedSignedLassoBridge.wellSupportedExistence
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward}
    (bridge : QuittingCofinalPrioritizedSignedLassoBridge sequence) :
    QuittingWellSupportedAbsorbingSequenceExistence reward := by
  intro error herror
  have heventually : ∀ᶠ n in atTop, sequence.delta n < error :=
    (tendsto_order.1 sequence.delta_tendsto_zero).2 error herror
  obtain ⟨n, hn⟩ := heventually.exists
  obtain ⟨plan, hsupport, hdiverges, _hrational⟩ :=
    (bridge.lasso n).exists_supportRationalDivergentPath
  have hcomplete : IsCompletelyAbsorbing plan := by
    have hdiverges' : ¬Summable (fun time ↦
        quittingRootAbsorptionMass (plan time)) := by
      change ¬Summable (fun time ↦
        quittingRootAbsorptionMass (plan time)) at hdiverges
      exact hdiverges
    have hzero :=
      tendsto_zero_quittingJointSurvivalWeight_of_not_summable_absorption
        plan 0 (by simpa using hdiverges')
    have heq : quittingJointSurvivalWeight plan 0 =
        quittingSurvivalPrefix plan := by
      funext fuel
      simpa using
        (quittingJointSurvivalWeight_eq_quittingSurvivalPrefix plan 0 fuel)
    unfold IsCompletelyAbsorbing
    rw [← heq]
    exact hzero
  refine ⟨plan, hcomplete, ?_⟩
  have hscale : 2 * (sequence.delta n / 2) = sequence.delta n := by
    ring
  rw [hscale] at hsupport
  exact hsupport.mono hn.le

/-- A prioritized seed sequence cannot already carry the missing semantic
lassos: their checked compiler gives S.3, contradicting the priority
negation retained at any one scale.  Thus closing this boundary means deriving
these phase-indexed fields and eliminating the residual, not adding the
table-level preemption cycle as another surviving case. -/
theorem not_nonempty_cofinalPrioritizedSignedLassoBridge
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (sequence : QuittingCofinalPrioritizedPreemptionSeedSequence reward) :
    ¬Nonempty (QuittingCofinalPrioritizedSignedLassoBridge sequence) := by
  rintro ⟨bridge⟩
  exact sequence.seed_not_wellSupported 0
    (bridge.wellSupportedExistence (sequence.delta 0) (sequence.delta_pos 0))

end QuittingPrioritizedRefinedSourceResidualAt
end GameTheory
