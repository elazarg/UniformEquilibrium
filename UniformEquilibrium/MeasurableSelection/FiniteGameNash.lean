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
  simp_rw [FinDist.expect_eq_sum]
  fun_prop

/-- The strict pure-deviation form of approximate Nash on the mixed-profile
polytope.  Strictness makes its graph open and therefore measurably
selectable. -/
def IsStrictApproximateNashWeights
    (utility : F.sig.Outcome → ι → ℝ) (ε : ℝ)
    (weights : mixedPolytope F.sig) : Prop :=
  ∀ who (action : F.sig.Strategy who),
    payoff F utility who
        (Profile.update weights.1 who (FinDist.pure action).prob) <
      payoff F utility who weights.1 + ε

omit [∀ i, Nonempty (F.sig.Strategy i)] in
/-- Strict approximate Nash weights form an open subset of utility/profile
pairs. -/
theorem isOpen_isStrictApproximateNashWeights (ε : ℝ) :
    IsOpen {data : (F.sig.Outcome → ι → ℝ) × mixedPolytope F.sig |
      IsStrictApproximateNashWeights data.1 ε data.2} := by
  simp only [IsStrictApproximateNashWeights, setOf_forall]
  apply isOpen_iInter_of_finite
  intro who
  apply isOpen_iInter_of_finite
  intro action
  apply isOpen_lt
  · exact (continuous_payoff_utility_profile who).comp
      (continuous_fst.prodMk
        ((continuous_profileUpdate who).comp
          ((continuous_subtype_val.comp continuous_snd).prodMk
            continuous_const)))
  · exact ((continuous_payoff_utility_profile who).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).add
        continuous_const

omit [Fintype F.sig.Outcome] in
/-- Exact Nash existence puts a strict `ε`-Nash point in the mixed-profile
polytope whenever `ε` is positive. -/
theorem exists_isStrictApproximateNashWeights
    (utility : F.sig.Outcome → ι → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ weights : mixedPolytope F.sig,
      IsStrictApproximateNashWeights utility ε weights := by
  obtain ⟨profile, hnash⟩ := exists_isNash_mixed utility
  let weights : mixedPolytope F.sig :=
    ⟨probs F.sig profile, probs_mem_mixedPolytope F.sig profile⟩
  refine ⟨weights, ?_⟩
  intro who action
  have hpure := (isNash_mixed_iff profile).1 hnash who action
  have hdeviation :
      payoff F utility who
          (Profile.update weights.1 who (FinDist.pure action).prob) ≤
        payoff F utility who weights.1 := by
    rw [show weights.1 = probs F.sig profile from rfl, ← probs_update]
    simpa only [payoff_probs] using hpure
  linarith

/-- A fixed finite game form admits a measurable strict approximate-Nash
selector as its outcome utility table varies. -/
theorem exists_measurable_isStrictApproximateNashWeights
    {ε : ℝ} (hε : 0 < ε) :
    ∃ selector : (F.sig.Outcome → ι → ℝ) → mixedPolytope F.sig,
      Measurable selector ∧ ∀ utility,
        IsStrictApproximateNashWeights utility ε (selector utility) := by
  classical
  letI : CompactSpace (mixedPolytope F.sig) :=
    isCompact_iff_compactSpace.mp (isCompact_mixedPolytope F.sig)
  letI : Nonempty (mixedPolytope F.sig) :=
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

omit [∀ i, Fintype (F.sig.Strategy i)]
    [∀ i, Nonempty (F.sig.Strategy i)] [Fintype F.sig.Outcome] in
/-- Pure-deviation approximate optimality implies mixed approximate Nash,
because a randomized deviation averages the pure deviations. -/
theorem isεNash_mixed_of_forall_pure
    (utility : F.sig.Outcome → ι → ℝ) (ε : ℝ)
    (profile : Profile F.sig.mixed)
    (hpure : ∀ who (action : F.sig.Strategy who),
      expectedUtility utility who
          (F.mixed.play
            (Profile.update profile who (FinDist.pure action))) ≤
        expectedUtility utility who (F.mixed.play profile) + ε) :
    IsεNash F.mixed utility ε profile := by
  rw [isεNash_iff]
  intro who replacement
  rw [GameForm.mixed_play_update, expectedUtility_bind]
  calc
    (replacement.expect fun action ↦
        expectedUtility utility who
          (F.mixed.play
            (Profile.update profile who (FinDist.pure action)))) ≤
        replacement.expect fun _ ↦
          expectedUtility utility who (F.mixed.play profile) + ε :=
      FinDist.expect_mono fun action _ ↦ hpure who action
    _ = expectedUtility utility who (F.mixed.play profile) + ε :=
      FinDist.expect_const _ _

omit [∀ i, Nonempty (F.sig.Strategy i)] [Fintype F.sig.Outcome] in
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
  calc
    expectedUtility utility who
        (F.mixed.play
          (Profile.update (ofPolytope F.sig weights.2) who
            (FinDist.pure action))) =
        payoff F utility who
          (probs F.sig
            (Profile.update (ofPolytope F.sig weights.2) who
              (FinDist.pure action))) :=
      (payoff_probs _ who).symm
    _ = payoff F utility who
          (Profile.update weights.1 who (FinDist.pure action).prob) := by
      rw [probs_update, probs_ofPolytope]
    _ ≤ payoff F utility who weights.1 + ε := hstrict.le
    _ = expectedUtility utility who
          (F.mixed.play (ofPolytope F.sig weights.2)) + ε := by
      rw [← payoff_probs, probs_ofPolytope]

end GameTheory
