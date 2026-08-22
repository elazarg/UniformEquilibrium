/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.PureTimeWitnessNormalForm
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedSemanticCarrier

/-!
# Subsequential regimes of stationarily generated witnesses

A corrected Simon witness retains a finite stationary prefix, its punished
player, the actual punishment profile and cap, and the global behavioral Nash
inequality. This module selects all of that data at a canonical vanishing
scale and puts its two noncompact coordinates into honest normal form.

The punished player is fixed along a subsequence. The natural-number horizon
is then either fixed or tends to infinity. Finally the repeated root's
one-stage all-Continue mass converges. If the horizon is fixed and the limit
mass is positive, the structured semantic compactification already yields a
uniform-equilibrium payoff. The remaining cases are therefore exactly:

* vanishing one-stage live mass; or
* horizons tending to infinity while live mass tends to a positive limit.

This is a semantic regime theorem, not an assertion that either residual has
already been converted to the stationary or well-supported absorbing branch.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A selected family of diffuse stationary-prefix witnesses at one
vanishing error scale. -/
structure QuittingDiffuseStationaryPrefixFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  error : ℕ → ℝ
  root : ℕ → ι → PMF Bool
  horizon : ℕ → ℕ
  punished : ℕ → ι
  punishment : ℕ → ℕ → ι → PMF Bool
  error_pos : ∀ n, 0 < error n
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  horizon_gt_one : ∀ n, 1 < horizon n
  punishmentWithin : ∀ n, IsQuittingRootSequencePunishmentWithin reward
    (punished n) (error n) (punishment n)
  nash : ∀ n, IsεQuittingRootSequenceNash reward (2 * error n)
    (quittingStationaryPrefixThenRoots (root n) (horizon n) (punishment n))
  live_pos : ∀ n, 0 < quittingStationaryContinueMass (root n)

/-- The canonical positive scale `1 / (n + 1)`. -/
def quittingStationaryPrefixSelectionError (n : ℕ) : ℝ :=
  1 / (n + 1)

theorem quittingStationaryPrefixSelectionError_pos (n : ℕ) :
    0 < quittingStationaryPrefixSelectionError n := by
  unfold quittingStationaryPrefixSelectionError
  positivity

theorem tendsto_quittingStationaryPrefixSelectionError_zero :
    Tendsto quittingStationaryPrefixSelectionError atTop (nhds 0) := by
  change Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Diffuse stationarily generated approximate equilibria admit one canonical
vanishing-error family retaining every witness field. -/
theorem exists_quittingDiffuseStationaryPrefixFamily
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hgenerated : QuittingDiffuseStationarilyGeneratedApproximateEquilibria
      reward) :
    Nonempty (QuittingDiffuseStationaryPrefixFamily reward) := by
  let error := quittingStationaryPrefixSelectionError
  have hwitness : ∀ n, ∃ (root : ι → PMF Bool) (horizon : ℕ)
      (punished : ι) (punishment : ℕ → ι → PMF Bool),
      1 < horizon ∧
        IsQuittingRootSequencePunishmentWithin reward punished (error n)
          punishment ∧
        IsεQuittingRootSequenceNash reward (2 * error n)
          (quittingStationaryPrefixThenRoots root horizon punishment) ∧
        0 < quittingStationaryContinueMass root := by
    intro n
    obtain ⟨root, horizon, punished, punishment, hhorizon, hpunish,
        hnash, hlive⟩ := hgenerated (error n)
      (quittingStationaryPrefixSelectionError_pos n) (error n)
      (quittingStationaryPrefixSelectionError_pos n)
    refine ⟨root, horizon, punished, punishment, hhorizon, hpunish, ?_, hlive⟩
    simpa only [two_mul] using hnash
  choose root horizon punished punishment hhorizon hpunish hnash hlive using hwitness
  exact ⟨⟨error, root, horizon, punished, punishment,
    quittingStationaryPrefixSelectionError_pos,
    tendsto_quittingStationaryPrefixSelectionError_zero,
    hhorizon, hpunish, hnash, hlive⟩⟩

omit [DecidableEq ι] in
/-- A sequence of labels in a finite player set has a constant strict
subsequence. -/
theorem exists_fixedPlayer_strictMono_subsequence (label : ℕ → ι) :
    ∃ fixed : ι, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧ ∀ n, label (subsequence n) = fixed := by
  have hfrequent : ∃ fixed : ι, ∃ᶠ n in atTop, label n = fixed := by
    by_contra hnot
    push Not at hnot
    have hall : ∀ᶠ n in atTop, ∀ fixed : ι, label n ≠ fixed := by
      rw [eventually_all]
      exact hnot
    obtain ⟨n, hn⟩ := hall.exists
    exact hn (label n) rfl
  obtain ⟨fixed, hfixed⟩ := hfrequent
  obtain ⟨subsequence, hsubsequence, hlabel⟩ :=
    extraction_of_frequently_atTop hfixed
  exact ⟨fixed, subsequence, hsubsequence, hlabel⟩

/-- The two possible subsequential normal forms of a natural-number horizon. -/
def HasFixedOrDivergentStationaryPrefixHorizon
    (horizon : ℕ → ℕ) : Prop :=
  (∃ fixed : ℕ, ∀ n, horizon n = fixed) ∨ Tendsto horizon atTop atTop

/-- A fixed-or-divergent horizon normal form survives reindexing by a
subsequence tending to infinity. -/
theorem HasFixedOrDivergentStationaryPrefixHorizon.comp_of_tendsto_atTop
    {horizon : ℕ → ℕ}
    (hnormal : HasFixedOrDivergentStationaryPrefixHorizon horizon)
    {subsequence : ℕ → ℕ} (hsubsequence : Tendsto subsequence atTop atTop) :
    HasFixedOrDivergentStationaryPrefixHorizon (horizon ∘ subsequence) := by
  rcases hnormal with ⟨fixed, hfixed⟩ | hdivergent
  · exact Or.inl ⟨fixed, fun n ↦ hfixed (subsequence n)⟩
  · exact Or.inr (hdivergent.comp hsubsequence)

/-- The two genuine residual regimes after the fixed-horizon positive-live
case has been compactified. -/
def IsResidualQuittingStationaryPrefixRegime
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (subsequence : ℕ → ℕ) : Prop :=
  Tendsto
      (fun n ↦ quittingStationaryContinueMass (family.root (subsequence n)))
      atTop (nhds 0) ∨
    ∃ liveLimit : ℝ, 0 < liveLimit ∧
      Tendsto
        (fun n ↦ quittingStationaryContinueMass (family.root (subsequence n)))
        atTop (nhds liveLimit) ∧
      Tendsto (fun n ↦ family.horizon (subsequence n)) atTop atTop

/-- Diffuse stationarily generated witnesses either already yield a uniform
equilibrium payoff through a fixed structured semantic cell, or admit a
strict subsequence with fixed punished player, normalized horizon, and one of
the two exact residual live-mass regimes. -/
theorem exists_uniformEquilibriumPayoff_or_stationaryPrefix_residual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hgenerated : QuittingDiffuseStationarilyGeneratedApproximateEquilibria
      reward) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ (family : QuittingDiffuseStationaryPrefixFamily reward)
          (subsequence : ℕ → ℕ) (punished : ι),
        StrictMono subsequence ∧
          (∀ n, family.punished (subsequence n) = punished) ∧
          HasFixedOrDivergentStationaryPrefixHorizon
            (fun n ↦ family.horizon (subsequence n)) ∧
          IsResidualQuittingStationaryPrefixRegime family subsequence := by
  classical
  let family := Classical.choice
    (exists_quittingDiffuseStationaryPrefixFamily hgenerated)
  obtain ⟨punished, playerSubsequence, hplayerSubsequence, hpunished⟩ :=
    exists_fixedPlayer_strictMono_subsequence family.punished
  obtain ⟨horizonSubsequence, hhorizonSubsequence, hhorizonNormal⟩ :=
    Math.PureTimeWitnessNormalForm.exists_strictMono_hasNormalForm
      (fun n ↦ some (family.horizon (playerSubsequence n)))
  let firstSubsequence := playerSubsequence ∘ horizonSubsequence
  have hfirstSubsequence : StrictMono firstSubsequence :=
    hplayerSubsequence.comp hhorizonSubsequence
  have hpunishedFirst : ∀ n, family.punished (firstSubsequence n) = punished :=
    fun n ↦ hpunished (horizonSubsequence n)
  have hhorizonFirst : HasFixedOrDivergentStationaryPrefixHorizon
      (fun n ↦ family.horizon (firstSubsequence n)) := by
    rcases hhorizonNormal with ⟨fixed, hfixed⟩ | hnone | ⟨values, hvalues, heq⟩
    · exact Or.inl ⟨fixed, fun n ↦ Option.some.inj (hfixed n)⟩
    · exact False.elim (Option.some_ne_none _ (hnone 0))
    · exact Or.inr (hvalues.congr' (Filter.Eventually.of_forall fun n ↦ by
        exact Option.some.inj (heq n).symm))
  let liveMass : ℕ → ℝ := fun n ↦
    quittingStationaryContinueMass (family.root (firstSubsequence n))
  have hliveMem : ∀ n, liveMass n ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    exact ⟨quittingStationaryContinueMass_nonneg _,
      quittingStationaryContinueMass_le_one _⟩
  obtain ⟨liveLimit, hliveLimitMem, liveSubsequence, hliveSubsequence,
      hliveLimit⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).tendsto_subseq
    hliveMem
  let subsequence := firstSubsequence ∘ liveSubsequence
  have hsubsequence : StrictMono subsequence :=
    hfirstSubsequence.comp hliveSubsequence
  have hpunishedFinal : ∀ n, family.punished (subsequence n) = punished :=
    fun n ↦ hpunishedFirst (liveSubsequence n)
  have hhorizonFinal : HasFixedOrDivergentStationaryPrefixHorizon
      (fun n ↦ family.horizon (subsequence n)) := by
    simpa [subsequence, Function.comp_def] using
      hhorizonFirst.comp_of_tendsto_atTop hliveSubsequence.tendsto_atTop
  have hliveFinal : Tendsto
      (fun n ↦ quittingStationaryContinueMass (family.root (subsequence n)))
      atTop (nhds liveLimit) := by
    simpa [liveMass, subsequence, Function.comp_def] using hliveLimit
  rcases eq_or_lt_of_le hliveLimitMem.1 with hliveZero | hlivePositive
  · right
    refine ⟨family, subsequence, punished, hsubsequence, hpunishedFinal,
      hhorizonFinal, Or.inl ?_⟩
    simpa only [hliveZero] using hliveFinal
  · rcases hhorizonFinal with ⟨fixedHorizon, hhorizonFixed⟩ | hhorizonDivergent
    · have hliveEventually : ∀ᶠ n in atTop,
          liveLimit / 2 ≤ quittingStationaryContinueMass
            (family.root (subsequence n)) := by
        have hhalf : liveLimit / 2 < liveLimit := by linarith
        have hstrict := hliveFinal.eventually (Ioi_mem_nhds hhalf)
        filter_upwards [hstrict] with n hn
        exact hn.le
      obtain ⟨start, hstart⟩ := eventually_atTop.1 hliveEventually
      let selected : ℕ → ℕ := fun n ↦ subsequence (start + n)
      have hselected : StrictMono selected := by
        apply hsubsequence.comp
        intro a b hab
        exact Nat.add_lt_add_left hab start
      left
      apply exists_uniformEquilibriumPayoff_of_stationaryPrefix_witnesses
        reward fixedHorizon punished
        (fun n ↦ family.root (selected n))
        (fun n ↦ family.punishment (selected n))
        (fun n ↦ family.error (selected n))
        (fun n ↦ 2 * family.error (selected n))
        (liveLimit / 2)
      · exact family.error_tendsto_zero.comp hselected.tendsto_atTop
      · simpa using
          (tendsto_const_nhds.mul
            (family.error_tendsto_zero.comp hselected.tendsto_atTop))
      · intro n
        simpa [selected, hpunishedFinal (start + n)] using
          family.punishmentWithin (selected n)
      · intro n
        simpa [selected, hhorizonFixed (start + n)] using
          family.nash (selected n)
      · linarith
      · intro n
        exact hstart (start + n) (Nat.le_add_right start n)
    · right
      exact ⟨family, subsequence, punished, hsubsequence, hpunishedFinal,
        Or.inr hhorizonDivergent,
        Or.inr ⟨liveLimit, hlivePositive, hliveFinal, hhorizonDivergent⟩⟩

/-! ## Decoding the vanishing-live residual -/

omit [DecidableEq ι] in
/-- Zero all-Continue mass is equivalent to a sure quitter for a finite
product root. -/
theorem quittingRootHasSureQuitter_of_stationaryContinueMass_eq_zero
    (root : ι → PMF Bool)
    (hmass : quittingStationaryContinueMass root = 0) :
    QuittingRootHasSureQuitter root := by
  apply (quittingRootHasSureQuitter_iff_allContinue_mass_zero root).2
  unfold quittingStationaryContinueMass at hmass
  rcases (ENNReal.toReal_eq_zero_iff _).mp hmass with hzero | htop
  · exact hzero
  · exact False.elim ((PMF.apply_ne_top _ _) htop)

/-- A vanishing-live subsequence of actual stationary-prefix approximate
equilibria compiles to the sure-first, instant-punishment branch. The proof
compactifies the first repeated root together with the actual semantic tail;
the limiting tail is then decoded by its realizing sequence. -/
theorem quittingInstantPunishment_of_stationaryPrefix_liveMass_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence)
    (hlive : Tendsto
      (fun n ↦ quittingStationaryContinueMass (family.root (subsequence n)))
      atTop (nhds 0)) :
    QuittingInstantPunishmentεEquilibriumExistence reward := by
  let roots : ℕ → ℕ → ι → PMF Bool := fun n ↦
    quittingStationaryPrefixThenRoots (family.root (subsequence n))
      (family.horizon (subsequence n)) (family.punishment (subsequence n))
  let tailProfile : ℕ → (quittingGame reward).BehaviorProfile := fun n ↦
    quittingRootSequenceProfile reward (roots n) 1
  let data : ℕ → QuittingRootSimplex ι × QuittingTerminalSemanticPair ι :=
    fun n ↦ (quittingSimplexOfRoot (family.root (subsequence n)),
      quittingTerminalSemanticPair reward (tailProfile n))
  have hdataMem : ∀ n, data n ∈
      (Set.univ : Set (QuittingRootSimplex ι)) ×ˢ
        quittingTerminalSemanticCarrier reward := by
    intro n
    exact ⟨Set.mem_univ _, subset_closure ⟨tailProfile n, rfl⟩⟩
  obtain ⟨limit, hlimitMem, limitSubsequence, hlimitSubsequence, hlimit⟩ :=
    (isCompact_univ.prod
      (quittingTerminalSemanticCarrier_isCompact reward)).tendsto_subseq hdataMem
  let rootLimit := quittingRootOfSimplex limit.1
  have hrootIdentity : ∀ n,
      quittingRootOfSimplex (data n).1 = family.root (subsequence n) := by
    intro n
    exact quittingRootOfSimplex_simplexOfRoot _
  have hliveLimit : Tendsto
      (fun n ↦ quittingStationaryContinueMass
        (quittingRootOfSimplex (data (limitSubsequence n)).1))
      atTop (nhds (quittingStationaryContinueMass rootLimit)) := by
    exact (continuous_quittingStationaryContinueMass_simplex.tendsto limit.1).comp
      ((continuous_fst.tendsto limit).comp hlimit)
  have hliveZero : quittingStationaryContinueMass rootLimit = 0 := by
    apply tendsto_nhds_unique hliveLimit
    simpa only [hrootIdentity, Function.comp_def] using
      hlive.comp hlimitSubsequence.tendsto_atTop
  have herror : Tendsto
      (fun n ↦ 2 * family.error (subsequence (limitSubsequence n)))
      atTop (nhds 0) := by
    have hbase := family.error_tendsto_zero.comp
      (hsubsequence.comp hlimitSubsequence).tendsto_atTop
    simpa using tendsto_const_nhds.mul hbase
  have hfullDebt : ∀ who, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPrefixSimplex reward limit) who ≤ 0 := by
    intro who
    have hdebtLimit : Tendsto
        (fun n ↦ quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefixSimplex reward
            (data (limitSubsequence n))) who) atTop
        (nhds (quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefixSimplex reward limit) who)) :=
      ((continuous_quittingTerminalSemanticDebt who).comp
        (continuous_quittingTerminalSemanticPrefixSimplex reward)).tendsto
        limit |>.comp hlimit
    apply le_of_tendsto_of_tendsto hdebtLimit herror
    apply Filter.Eventually.of_forall
    intro n
    have hprofile : quittingRootSequenceProfile reward
        (roots (limitSubsequence n)) 0 =
        quittingRootThenContinuationProfile reward
          (family.root (subsequence (limitSubsequence n)))
          (tailProfile (limitSubsequence n)) := by
      exact quittingRootSequenceProfile_eq_rootThenContinuation
        reward (roots (limitSubsequence n)) 0
    have hsemantic : quittingTerminalSemanticPrefixSimplex reward
        (data (limitSubsequence n)) =
        quittingTerminalSemanticPair reward
          (quittingRootSequenceProfile reward (roots (limitSubsequence n)) 0) := by
      rw [quittingTerminalSemanticPrefixSimplex, hrootIdentity]
      rw [hprofile, quittingTerminalSemanticPair_rootThenContinuation]
    change quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefixSimplex reward
          (data (limitSubsequence n))) who ≤
      2 * family.error (subsequence (limitSubsequence n))
    rw [hsemantic]
    apply quittingTerminalSemanticDebt_pair_le_of_isεAsymptoticNash
    exact (isεQuittingRootSequenceNash_iff_isεAsymptoticNash
      reward _ (roots (limitSubsequence n))).mp
        (family.nash (subsequence (limitSubsequence n)))
  have hsure : QuittingRootHasSureQuitter rootLimit :=
    quittingRootHasSureQuitter_of_stationaryContinueMass_eq_zero rootLimit hliveZero
  letI : Nonempty ι := ⟨Classical.choose hsure⟩
  have hfullCarrier : quittingTerminalSemanticPrefixSimplex reward limit ∈
      quittingTerminalSemanticCarrier reward := by
    exact quittingTerminalSemanticPrefix_mem_carrier reward rootLimit limit.2
      hlimitMem.2
  have hfullExploitability : quittingTerminalSemanticExploitability
      (quittingTerminalSemanticPrefixSimplex reward limit) = 0 := by
    apply le_antisymm
    · unfold quittingTerminalSemanticExploitability
      apply QuittingBoundaryHolonomy.finitePlayerMax_le
      intro who
      simp only [max_le_iff]
      exact ⟨le_rfl, hfullDebt who⟩
    · unfold quittingTerminalSemanticExploitability
      exact (le_max_left 0 (quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefixSimplex reward limit)
          (Classical.choose hsure))).trans
        (QuittingBoundaryHolonomy.le_finitePlayerMax
          (fun who ↦ max 0 (quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefixSimplex reward limit) who))
          (Classical.choose hsure))
  obtain ⟨tails, htails⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward limit.2 hlimitMem.2
  have hspliceSemantic : Tendsto
      (fun n ↦ quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward rootLimit (tails n)))
      atTop (nhds (quittingTerminalSemanticPrefixSimplex reward limit)) := by
    have hprefixed :=
      (continuous_quittingTerminalSemanticPrefix reward rootLimit).tendsto
        limit.2 |>.comp htails
    simpa [Function.comp_def, quittingTerminalSemanticPair_rootThenContinuation,
      quittingTerminalSemanticPrefixSimplex, rootLimit] using hprefixed
  apply quittingInstantPunishmentεEquilibriumExistence_of_sureQuitter
  intro ε hε
  have hexploitability : Tendsto (fun n ↦ quittingTerminalSemanticExploitability
      (quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward rootLimit (tails n))))
      atTop (nhds 0) := by
    have h :=
      continuous_quittingTerminalSemanticExploitability.continuousAt.tendsto.comp
        hspliceSemantic
    rw [hfullExploitability] at h
    change Tendsto (fun n ↦ quittingTerminalSemanticExploitability
      (quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward rootLimit (tails n))))
      atTop (nhds 0) at h
    exact h
  have heventually := hexploitability.eventually (Iio_mem_nhds hε)
  obtain ⟨n, hn⟩ := heventually.exists
  obtain ⟨quitter, hquitter⟩ := hsure
  refine ⟨quitter, rootLimit, tails n, hquitter, ?_⟩
  intro who deviation
  have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (quittingRootThenContinuationProfile reward rootLimit (tails n))
      who deviation
  have hdebtLe : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward rootLimit (tails n))) who ≤ ε := by
    apply le_trans (le_max_right 0 _)
    exact (QuittingBoundaryHolonomy.le_finitePlayerMax _ who).trans hn.le
  change quittingContinuationBestResponseValue reward
      (quittingRootThenContinuationProfile reward rootLimit (tails n)) who -
      quittingTerminalPayoff reward
        (quittingRootThenContinuationProfile reward rootLimit (tails n)) who ≤ ε
    at hdebtLe
  linarith

/-- Once the instant branch is excluded, the vanishing-live residual is
impossible. Hence every unresolved selected family has horizons tending to
infinity and one-stage live mass converging to a positive limit. -/
theorem exists_uniformEquilibriumPayoff_or_positiveLive_divergentHorizon
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hgenerated : QuittingDiffuseStationarilyGeneratedApproximateEquilibria
      reward)
    (hnoInstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ (family : QuittingDiffuseStationaryPrefixFamily reward)
          (subsequence : ℕ → ℕ) (punished : ι) (liveLimit : ℝ),
        StrictMono subsequence ∧
          (∀ n, family.punished (subsequence n) = punished) ∧
          0 < liveLimit ∧
          Tendsto
            (fun n ↦ quittingStationaryContinueMass
              (family.root (subsequence n))) atTop (nhds liveLimit) ∧
          Tendsto (fun n ↦ family.horizon (subsequence n)) atTop atTop := by
  rcases exists_uniformEquilibriumPayoff_or_stationaryPrefix_residual
      hgenerated with huniform | ⟨family, subsequence, punished,
        hsubsequence, hpunished, _hhorizon, hresidual⟩
  · exact Or.inl huniform
  · rcases hresidual with hliveZero |
        ⟨liveLimit, hlivePositive, hliveLimit, hhorizon⟩
    · exact False.elim (hnoInstant
        (quittingInstantPunishment_of_stationaryPrefix_liveMass_tendsto_zero
          family subsequence hsubsequence hliveZero))
    · exact Or.inr ⟨family, subsequence, punished, liveLimit,
        hsubsequence, hpunished, hlivePositive, hliveLimit, hhorizon⟩

end GameTheory
