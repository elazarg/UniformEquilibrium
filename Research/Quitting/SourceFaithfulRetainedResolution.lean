/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.SourceFaithfulMinimumLawCausalization
import Research.Quitting.UniqueAllContinueCapStackNoGo
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCapNashNearMinimum

/-!
# Exact resolution retention through source-faithful causalization

A source-faithful minimum causalization selects exact cap--Nash words over
literal suffix profiles converging to a positive global minimum.  The robust
near-minimum cap-freezing theorem makes all-Continue the unique exact root at
every sufficiently late suffix.  Uniqueness propagates backwards through the
complete cap--Nash word, so that word is eventually a literal replicate of
all-Continue.

Consequently the causalization eventually loses no marked mass at all: its
shifted marked atom retains the full incoming floor `lambda`, not merely the
canonical `lambda / 2` recorded by the basic structure.  Every requested
resolution at most `lambda` is therefore renewable on a cofinal tail.

This is an exact quantitative renewal fact.  It does not construct the next
minimum source or consume the retained atom strategically.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingSourceFaithfulMinimumCausalization

/-- Every sufficiently late exact cap--Nash word selected by a positive
minimum causalization is literally all-Continue at every displayed row. -/
theorem eventually_roots_eq_replicate_allContinue
    {point : QuittingTerminalSemanticLawPoint ι}
    {terminal : {S : Finset ι // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda) :
    ∀ᶠ rank in atTop,
      causal.roots rank = List.replicate (causal.roots rank).length
        (quittingAllContinueRoot : ι → PMF Bool) := by
  have hminimumPos : 0 < quittingTerminalSemanticDebtSum point.1 := by
    rw [causal.debt_eq_inf]
    exact causal.inf_pos
  obtain ⟨epsilon, hepsilon, hfreeze⟩ :=
    exists_pos_nearMinimum_capNash_eq_allContinue_radius
      (reward := reward) (quittingTerminalSemanticDebtSum point.1)
        hminimumPos causal.minimum
  have hpairTendsto : Tendsto
      (fun rank ↦ quittingTerminalSemanticPair reward (profiles rank))
      atTop (nhds point.1) :=
    continuous_fst.continuousAt.tendsto.comp causal.profiles_tendsto
  have hdebtTendsto : Tendsto
      (fun rank ↦ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profiles rank)))
      atTop (nhds (quittingTerminalSemanticDebtSum point.1)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      hpairTendsto
  have hnear : ∀ᶠ rank in atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles rank)) ≤
        quittingTerminalSemanticDebtSum point.1 + epsilon :=
    (hdebtTendsto.eventually
      (Iio_mem_nhds (lt_add_of_pos_right _ hepsilon))).mono
        fun _ hlt ↦ hlt.le
  filter_upwards [hnear] with rank hrank
  have hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward
          (quittingTerminalSemanticPair reward (profiles rank)).2 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool) := by
    intro root hnash
    exact hfreeze
      (quittingTerminalSemanticPair reward (profiles rank))
      (quittingTerminalSemanticPair_mem_carrier reward (profiles rank))
      hrank root hnash
  exact (capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap
    reward (profiles rank) (causal.roots rank) hunique
      (causal.roots_nash rank)).1

/-- The joint Continue product of the selected exact word is eventually
exactly one, not merely convergent to one. -/
theorem eventually_continueProduct_eq_one
    {point : QuittingTerminalSemanticLawPoint ι}
    {terminal : {S : Finset ι // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda) :
    ∀ᶠ rank in atTop,
      quittingCapNashStackContinueProduct (causal.roots rank) = 1 := by
  filter_upwards [causal.eventually_roots_eq_replicate_allContinue]
      with rank hroots
  rw [hroots]
  have hallContinue : quittingStationaryContinueMass
      (quittingAllContinueRoot : ι → PMF Bool) = 1 := by
    have hzero := quittingRootAbsorptionMass_allContinueRoot (ι := ι)
    unfold quittingRootAbsorptionMass at hzero
    linarith
  simp [quittingCapNashStackContinueProduct,
    quittingLiteralRootStackJointSurvival, hallContinue]

/-- The complete incoming marked-mass floor is eventually retained after the
exact cap--Nash word. -/
theorem eventually_parentResolution_le_shiftedMarkMass
    {point : QuittingTerminalSemanticLawPoint ι}
    {terminal : {S : Finset ι // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda) :
    ∀ᶠ rank in atTop,
      lambda ≤ quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward
          (causal.roots rank) (profiles rank))
        (rank + 1 + mark rank) terminal := by
  filter_upwards [causal.eventually_continueProduct_eq_one]
      with rank hproduct
  rw [causal.shifted_mark_mass_eq rank, hproduct, one_mul]
  exact causal.marked_mass_floor rank

/-- Every requested resolution weakly below the incoming marked-mass floor is
renewable on the same literal source-faithful chronology. -/
theorem eventually_requestedResolution_le_shiftedMarkMass
    {point : QuittingTerminalSemanticLawPoint ι}
    {terminal : {S : Finset ι // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda requested : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda)
    (hrequested : requested ≤ lambda) :
    ∀ᶠ rank in atTop,
      requested ≤ quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward
          (causal.roots rank) (profiles rank))
        (rank + 1 + mark rank) terminal :=
  causal.eventually_parentResolution_le_shiftedMarkMass.mono
    fun _ hmass ↦ hrequested.trans hmass

/-- Positive requested resolutions are eventually available with their
literal shifted-stage mass bound. -/
theorem eventually_positiveRequestedResolution
    {point : QuittingTerminalSemanticLawPoint ι}
    {terminal : {S : Finset ι // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda requested : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda)
    (hrequestedPos : 0 < requested)
    (hrequestedLe : requested ≤ lambda) :
    ∀ᶠ rank in atTop,
      0 < requested ∧
        requested ≤ quittingStageCoalitionMass reward
          (quittingLiteralRootStackProfile reward
            (causal.roots rank) (profiles rank))
          (rank + 1 + mark rank) terminal := by
  filter_upwards [
    causal.eventually_requestedResolution_le_shiftedMarkMass hrequestedLe]
      with rank hmass
  exact ⟨hrequestedPos, hmass⟩

end QuittingSourceFaithfulMinimumCausalization

end GameTheory
