/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Analysis.Nash
import GameTheory.Core.Approximate
import MathUE.MeasurableSelection

/-!
# Measurable approximate Nash selection for finite games

For a fixed finite game form, this module selects a mixed approximate Nash
profile measurably as the outcome utility varies.  The construction enumerates
a dense sequence in the compact mixed-profile polytope and takes the first
strict approximate equilibrium.  Exact mixed-Nash existence makes that open
set nonempty.
-/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability Set TopologicalSpace

universe uι us uo

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {F : GameForm.{uι, us, uo} ι}
variable [∀ i, Fintype (F.sig.Strategy i)]
variable [∀ i, Nonempty (F.sig.Strategy i)]
variable [Fintype F.sig.Outcome]

omit [∀ i, Nonempty (F.sig.Strategy i)] in
/-- Expected payoff is jointly continuous in a finite outcome-utility table
and in the mixed-profile weights. -/
theorem continuous_payoff_utility_profile (who : ι) :
    Continuous fun data :
        (F.sig.Outcome → ι → ℝ) × Profile F.sig.weights ↦
      payoff F data.1 who data.2 := by
  unfold payoff expectedUtility
  simp_rw [GameTheory.Math.Probability.expect_eq_sum]
  fun_prop

/-- The strict pure-deviation form of approximate Nash on the mixed-profile
polytope.  Strictness makes its graph open and therefore measurably
selectable. -/
def IsStrictApproximateNashWeights
    (utility : F.sig.Outcome → ι → ℝ) (ε : ℝ)
    (weights : mixedPolytope F.sig) : Prop :=
  ∀ who (action : F.sig.Strategy who),
    payoff F utility who
        (Profile.update weights.1 who (fun a => (PMF.pure action a).toReal)) <
      payoff F utility who weights.1 + ε

omit [∀ i, Nonempty (F.sig.Strategy i)] in
private theorem continuous_payoff_of_continuous {X : Type*} [TopologicalSpace X]
    (who : ι) {utility : X → F.sig.Outcome → ι → ℝ}
    {weights : X → Profile F.sig.weights}
    (hu : Continuous utility) (hw : Continuous weights) :
    Continuous fun x => payoff F (utility x) who (weights x) := by
  unfold payoff expectedUtility
  simp_rw [GameTheory.Math.Probability.expect_eq_sum]
  fun_prop

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (F.sig.Strategy i)]
  [∀ i, Nonempty (F.sig.Strategy i)] [Fintype F.sig.Outcome] in
private theorem continuous_polytope_weights :
    Continuous (fun data : (F.sig.Outcome → ι → ℝ) × mixedPolytope F.sig => data.2.1) :=
  continuous_subtype_val.comp continuous_snd

omit [∀ i, Nonempty (F.sig.Strategy i)] in
private theorem continuous_pureDeviationPayoff (who : ι) (action : F.sig.Strategy who) :
    Continuous fun data : (F.sig.Outcome → ι → ℝ) × mixedPolytope F.sig =>
      payoff F data.1 who
        (Profile.update data.2.1 who (fun a => (PMF.pure action a).toReal)) := by
  apply continuous_payoff_of_continuous (F := F) who continuous_fst
  exact (continuous_update_profile who (fun a => (PMF.pure action a).toReal)).comp
    (continuous_polytope_weights (F := F))

omit [∀ i, Nonempty (F.sig.Strategy i)] in
private theorem continuous_payoff_utility_polytope (who : ι) :
    Continuous fun data : (F.sig.Outcome → ι → ℝ) × mixedPolytope F.sig =>
      payoff F data.1 who data.2.1 :=
  continuous_payoff_of_continuous (F := F) who continuous_fst
    (continuous_polytope_weights (F := F))

omit [∀ i, Nonempty (F.sig.Strategy i)] in
/-- Strict approximate Nash weights form an open subset of utility/profile
pairs. -/
theorem isOpen_isStrictApproximateNashWeights (ε : ℝ) :
    IsOpen {data : (F.sig.Outcome → ι → ℝ) × mixedPolytope F.sig |
      IsStrictApproximateNashWeights data.1 ε data.2} := by
  simp only [IsStrictApproximateNashWeights, ofPred_forall]
  exact isOpen_iInter_of_finite fun who =>
    isOpen_iInter_of_finite fun action =>
      isOpen_lt (continuous_pureDeviationPayoff (F := F) who action)
        ((continuous_payoff_utility_polytope (F := F) who).add continuous_const)

/-- Exact Nash existence puts a strict `ε`-Nash point in the mixed-profile
polytope whenever `ε` is positive. -/
theorem exists_isStrictApproximateNashWeights
    (utility : F.sig.Outcome → ι → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ weights : mixedPolytope F.sig,
      IsStrictApproximateNashWeights utility ε weights := by
  have hintegrable := F.hasIntegrableUtility_of_finiteOutcome utility
  obtain ⟨profile, hnash⟩ := exists_isNash_mixed utility hintegrable
  rw [isNash_iff] at hnash
  let weights : mixedPolytope F.sig :=
    ⟨probs F.sig profile, probs_mem_mixedPolytope F.sig profile⟩
  refine ⟨weights, ?_⟩
  intro who action
  have hpure := (euPreference_iff _ _ _ _
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).mp
      (hnash who (PMF.pure action))
  have hdeviation :
      payoff F utility who
          (Profile.update weights.1 who (fun a => (PMF.pure action a).toReal)) ≤
        payoff F utility who weights.1 := by
    rw [show weights.1 = probs F.sig profile from rfl, ← probs_update]
    simpa only [payoff_probs hintegrable] using hpure
  linarith

/-- A fixed finite game form admits a measurable strict approximate-Nash
selector as its outcome utility table varies. -/
theorem exists_measurable_isStrictApproximateNashWeights
    {ε : ℝ} (hε : 0 < ε) :
    ∃ selector : (F.sig.Outcome → ι → ℝ) → mixedPolytope F.sig,
      Measurable selector ∧ ∀ utility,
        IsStrictApproximateNashWeights utility ε (selector utility) := by
  classical
  let : CompactSpace (mixedPolytope F.sig) :=
    isCompact_iff_compactSpace.mp (isCompact_mixedPolytope F.sig)
  let : Nonempty (mixedPolytope F.sig) :=
    (mixedPolytope_nonempty F.sig).to_subtype
  let dense : ℕ → mixedPolytope F.sig := denseSeq _
  let candidate : (F.sig.Outcome → ι → ℝ) → ℕ → Prop :=
    fun utility n ↦ IsStrictApproximateNashWeights utility ε (dense n)
  have hopen (utility : F.sig.Outcome → ι → ℝ) :
      IsOpen {weights : mixedPolytope F.sig |
        IsStrictApproximateNashWeights utility ε weights} := by
    exact (isOpen_isStrictApproximateNashWeights ε).preimage
      (continuous_const.prodMk continuous_id)
  have hexists : ∀ utility, ∃ n, candidate utility n := by
    intro utility
    obtain ⟨weights, hweights⟩ :=
      exists_isStrictApproximateNashWeights utility hε
    exact (denseRange_denseSeq (mixedPolytope F.sig)).exists_mem_open
      (hopen utility) ⟨weights, hweights⟩
  have hcandidate : ∀ n, MeasurableSet {utility | candidate utility n} := by
    intro n
    exact ((isOpen_isStrictApproximateNashWeights ε).preimage
      (continuous_id.prodMk continuous_const)).measurableSet
  let index : (F.sig.Outcome → ι → ℝ) → ℕ :=
    fun utility ↦ Nat.find (hexists utility)
  let selector : (F.sig.Outcome → ι → ℝ) → mixedPolytope F.sig :=
    fun utility ↦ dense (index utility)
  refine ⟨selector, ?_, ?_⟩
  · exact measurable_from_nat.comp (measurable_find hexists hcandidate)
  · intro utility
    exact Nat.find_spec (hexists utility)

omit [∀ i, Nonempty (F.sig.Strategy i)] in
/-- Pure-deviation approximate optimality implies mixed approximate Nash,
because a randomized deviation averages the pure deviations. -/
theorem isεNash_mixed_of_forall_pure
    (utility : F.sig.Outcome → ι → ℝ) (ε : ℝ)
    (profile : Profile F.sig.mixed)
    (hpure : ∀ who (action : F.sig.Strategy who),
      expectedUtility utility who
          (F.mixed.play
            (Profile.update profile who (PMF.pure action))) ≤
        expectedUtility utility who (F.mixed.play profile) + ε) :
    IsεNash F.mixed utility ε profile := by
  change IsNash F.mixed (euPreferenceWithin ε utility) profile
  rw [isNash_iff]
  intro who replacement
  apply (euPreferenceWithin_iff _ _ _ _ _
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).mpr
  rw [GameForm.mixed_play_update,
    expectedUtility_bind _ _ _ _ (payoffIntegrable_of_finite _ _)]
  exact (expect_mono (fun action _ ↦ hpure who action)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).trans_eq
      (expect_constant _ _)

omit [∀ i, Nonempty (F.sig.Strategy i)] in
/-- The selected strict weight profile compiles to the canonical semantic
`ε`-Nash predicate. -/
theorem IsStrictApproximateNashWeights.isεNash
    {utility : F.sig.Outcome → ι → ℝ} {ε : ℝ}
    {weights : mixedPolytope F.sig}
    (hweights : IsStrictApproximateNashWeights utility ε weights) :
    IsεNash F.mixed utility ε (ofPolytope F.sig weights.2) := by
  apply isεNash_mixed_of_forall_pure
  intro who action
  have hstrict := hweights who action
  have hintegrable := F.hasIntegrableUtility_of_finiteOutcome utility
  calc
    expectedUtility utility who
        (F.mixed.play
          (Profile.update (ofPolytope F.sig weights.2) who
            (PMF.pure action))) =
        payoff F utility who
          (probs F.sig
            (Profile.update (ofPolytope F.sig weights.2) who
              (PMF.pure action))) :=
      (payoff_probs hintegrable _ who).symm
    _ = payoff F utility who
          (Profile.update weights.1 who (fun a => (PMF.pure action a).toReal)) := by
      rw [probs_update, probs_ofPolytope]
    _ ≤ payoff F utility who weights.1 + ε := hstrict.le
    _ = expectedUtility utility who
          (F.mixed.play (ofPolytope F.sig weights.2)) + ε := by
      rw [← payoff_probs hintegrable, probs_ofPolytope]

end GameTheory
