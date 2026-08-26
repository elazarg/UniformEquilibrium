/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.FiniteLabelLiminfExtraction
import UniformEquilibrium.Quitting.Classification.Existence.PrioritizedAttachmentSingletonDefect
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

/-- Cofinal prioritized residuals admit a sequence of source-matched strict
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
