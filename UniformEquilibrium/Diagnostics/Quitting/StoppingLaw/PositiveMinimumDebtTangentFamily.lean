/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawVanishingRegretTangentExtraction
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ExhaustiveTangentAlternative

/-!
# Tangent families at a positive minimum of terminal semantic debt

This module extracts the finite stopping-law tangent data intrinsic to any
positive global minimum of terminal semantic debt.

Every terminal exploitability witness has a positive minimum all-Continue semantic
plateau.  A literal sequence realizing the semantic plateau can be shifted so that
every limiting positive-debt coordinate is already positive.  Near-minimum
excess and all limiting zero-debt coordinates then vanish on that one common
sequence.  The square-root scale selector makes all of them negligible
relative to one common reset scale, so the stopping-law normalized-chord
extractor applies without an additional assumption.

The resulting finite disjunction is
`IsQuittingStoppingLawTangentAlternative`: positive total slope,
zero-debt support entry, positive charged circulation, or potential-guided
active co-decrease.  The first branch has the existing positive-slope causal
decoders.  The last three are exact residuals: this module does not claim a
chronological integration, a Bellman return, or a converse from tangent data
back to a terminal exploitability witness.

The first missing implication is branch-specific.

* Positive total slope provides literal terminal atoms and causal rectangle
  rows, but not a state-matched punishment/Bellman continuation.
* Zero-debt support entry is envelope/debt data; it does not yet imply
  positive co-realized mover--recipient incidence at a common source row.
* Charged circulation is an infinitesimal balance; no theorem integrates it
  to a reset cycle in the semantic carrier.
* Potential-guided co-decrease retains a same-column second debtor, but does
  not yet supply a directed recipient return or metric/Bellman re-projection.

The older bare pipeline predicate is an overlapping cover because its flat
branches forget flatness and the duality decision.  The tagged predicate in
this module records the producing case splits and is disjoint: positive slope
versus flat, support entry versus no entry, and circulation versus its
separating-potential alternative.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The positive-debt coordinates of a terminal semantic pair. -/
def quittingPositiveDebtSupport (base : QuittingTerminalSemanticPair ι) : Finset ι :=
  Finset.univ.filter fun who ↦ 0 < quittingTerminalSemanticDebt base who

/-- A common-scale family of literal normalized replacement chords based at a
positive global minimum of terminal semantic debt.  `source` is already the
selected sequence: no hidden subsequence or chronological relation is stored. -/
structure QuittingPositiveMinimumDebtTangentFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  base : QuittingTerminalSemanticPair ι
  source : ℕ → (quittingGame reward).BehaviorProfile
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_le_one : ∀ n, scale n ≤ 1
  replacement : ∀ mover : {who // who ∈ quittingPositiveDebtSupport base},
    ℕ → (quittingGame reward).BehaviorStrategy mover.1
  tangent : {who // who ∈ quittingPositiveDebtSupport base} → ι → ℝ
  base_mem : base ∈ quittingTerminalSemanticCarrier reward
  base_minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum base ≤
      quittingTerminalSemanticDebtSum candidate
  base_positive : 0 < quittingTerminalSemanticDebtSum base
  source_tendsto : Tendsto
    (fun n ↦ quittingTerminalSemanticPair reward (source n))
    atTop (nhds base)
  scale_tendsto_zero : Tendsto scale atTop (nhds 0)
  /-- Along the selected tangent subsequence, source excess above the exact
  semantic minimum is negligible relative to the reset scale. -/
  source_excess_over_scale_tendsto_zero :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (source rank)) -
        quittingTerminalSemanticDebtSum base) /
          scale rank) atTop (nhds 0)
  tangent_tendsto : ∀ mover observer,
    Tendsto (fun rank ↦
      quittingStoppingLawNormalizedDebtDirection reward
        (source rank) mover.1 (replacement mover rank) (scale rank)
        (scale_pos rank).le (scale_le_one rank) observer)
      atTop (nhds (tangent mover observer))
  /-- At every selected rank, the literal full replacement's own debt is
  bounded both by the squared reset scale and by half of its source debt. -/
  replacement_moverDebt_le_tolerance : ∀ mover rank,
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update (source rank) mover.1
            (replacement mover rank))) mover.1 ≤
      min (scale rank ^ 2)
        (quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (source rank)) mover.1 / 2)
  tangent_inactive_nonneg : ∀ mover observer,
    quittingTerminalSemanticDebt base observer = 0 →
      0 ≤ tangent mover observer

/-- The mover support is derived from the base rather than stored. -/
def QuittingPositiveMinimumDebtTangentFamily.positiveDebtSupport
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingPositiveMinimumDebtTangentFamily reward) : Finset ι :=
  quittingPositiveDebtSupport family.base

/-- The derived support membership characterization. -/
theorem QuittingPositiveMinimumDebtTangentFamily.positiveDebtSupport_iff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingPositiveMinimumDebtTangentFamily reward) (who : ι) :
    who ∈ family.positiveDebtSupport ↔
      0 < quittingTerminalSemanticDebt family.base who := by
  simp [QuittingPositiveMinimumDebtTangentFamily.positiveDebtSupport,
    quittingPositiveDebtSupport]

/-- The selected literal full replacement drives its mover's own debt to
zero along the same common tangent subsequence. -/
theorem QuittingPositiveMinimumDebtTangentFamily.replacement_moverDebt_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ quittingPositiveDebtSupport family.base}) :
    Tendsto (fun rank ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update (family.source rank) mover.1
            (family.replacement mover rank))) mover.1)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun rank ↦
      quittingTerminalDeviationDebt_nonneg reward
          (Function.update (family.source rank) mover.1
            (family.replacement mover rank)) mover.1
  · exact Eventually.of_forall fun rank ↦
      (family.replacement_moverDebt_le_tolerance mover rank).trans
        (min_le_left _ _)
  · simpa using family.scale_tendsto_zero.pow 2

/-- Exact diagonal selection implies the half-debt bound. -/
theorem QuittingPositiveMinimumDebtTangentFamily.tangent_diagonal_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ quittingPositiveDebtSupport family.base}) :
    family.tangent mover mover.1 =
      -quittingTerminalSemanticDebt family.base mover.1 := by
  let endpointDebt : ℕ → ℝ := fun rank ↦
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update (family.source rank) mover.1
          (family.replacement mover rank))) mover.1
  have hsourceDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (family.source rank)) mover.1)
      atTop (nhds (quittingTerminalSemanticDebt family.base mover.1)) :=
    (continuous_quittingTerminalSemanticDebt mover.1).tendsto family.base |>.comp
      family.source_tendsto
  have hdirection : ∀ rank,
      quittingStoppingLawNormalizedDebtDirection reward
          (family.source rank) mover.1 (family.replacement mover rank)
          (family.scale rank) (family.scale_pos rank).le
          (family.scale_le_one rank) mover.1 =
        endpointDebt rank - quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (family.source rank)) mover.1 := by
    intro rank
    have haffine := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
      reward (family.source rank) mover.1 ((family.source rank) mover.1)
        (family.replacement mover rank) (family.scale rank)
        (family.scale_pos rank).le (family.scale_le_one rank)
    rw [Function.update_eq_self] at haffine
    dsimp only [endpointDebt, quittingStoppingLawNormalizedDebtDirection,
      quittingStoppingLawResetProfile, quittingTerminalSemanticDebtChange]
    apply (div_eq_iff (ne_of_gt (family.scale_pos rank))).2
    rw [haffine]
    ring
  have hdirectionLimit : Tendsto (fun rank ↦
      quittingStoppingLawNormalizedDebtDirection reward
        (family.source rank) mover.1 (family.replacement mover rank)
        (family.scale rank) (family.scale_pos rank).le
        (family.scale_le_one rank) mover.1) atTop
      (nhds (-quittingTerminalSemanticDebt family.base mover.1)) := by
    convert family.replacement_moverDebt_tendsto_zero mover |>.sub hsourceDebt using 1
    · funext rank
      exact hdirection rank
    · ring_nf
  exact tendsto_nhds_unique (family.tangent_tendsto mover mover.1) hdirectionLimit

/-- Exact diagonal selection implies the earlier half-debt estimate. -/
theorem QuittingPositiveMinimumDebtTangentFamily.tangent_diagonal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ quittingPositiveDebtSupport family.base}) :
    family.tangent mover mover.1 ≤
      -quittingTerminalSemanticDebt family.base mover.1 / 2 := by
  rw [family.tangent_diagonal_eq mover]
  have hpositive : 0 < quittingTerminalSemanticDebt family.base mover.1 := by
    exact (Finset.mem_filter.1 mover.2).2
  linarith

omit [DecidableEq ι] in
/-- Membership in the derived support is exactly strict positivity of debt. -/
theorem mem_quittingPositiveDebtSupport_iff
    (base : QuittingTerminalSemanticPair ι) (who : ι) :
    who ∈ quittingPositiveDebtSupport base ↔
      0 < quittingTerminalSemanticDebt base who := by
  simp [quittingPositiveDebtSupport]

/-- The family base is intrinsically a positive global minimum. -/
theorem QuittingPositiveMinimumDebtTangentFamily.hasPositiveMinimumTerminalSemanticDebt
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingPositiveMinimumDebtTangentFamily reward) :
    HasPositiveMinimumTerminalSemanticDebt reward :=
  ⟨family.base, family.base_mem, family.base_minimum, family.base_positive⟩

/-- Positive total base debt makes the derived positive-debt support
nonempty. -/
theorem QuittingPositiveMinimumDebtTangentFamily.positiveDebtSupport_nonempty
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingPositiveMinimumDebtTangentFamily reward) :
    family.positiveDebtSupport.Nonempty := by
  by_contra hempty
  have hzero : ∀ who, quittingTerminalSemanticDebt family.base who = 0 := by
    intro who
    have hnotPositive : ¬ 0 < quittingTerminalSemanticDebt family.base who := by
      intro hpositive
      exact hempty ⟨who, (family.positiveDebtSupport_iff who).2 hpositive⟩
    exact le_antisymm (le_of_not_gt hnotPositive)
      (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward family.base_mem who)
  have hpositive := family.base_positive
  unfold quittingTerminalSemanticDebtSum at hpositive
  simp only [hzero, Finset.sum_const_zero] at hpositive
  exact (lt_irrefl 0) hpositive

/-- Every family base is an exact all-Continue Nash fixed point. -/
theorem QuittingPositiveMinimumDebtTangentFamily.allContinue_plateau
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingPositiveMinimumDebtTangentFamily reward) :
    IsεQuittingRootNash reward family.base.1 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot family.base =
        family.base := by
  have hplateau := minimumTerminalSemantic_is_allContinuePlateau family.base
    family.base_mem family.base_minimum family.base_positive
  exact ⟨hplateau.1, hplateau.2.1⟩

/-- The total limiting normalized debt slope of every replacement column is
nonnegative.  This follows from global minimality and the vanishing normalized
source excess, rather than being stored in the family. -/
theorem QuittingPositiveMinimumDebtTangentFamily.tangent_sum_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ quittingPositiveDebtSupport family.base}) :
    0 ≤ ∑ observer, family.tangent mover observer := by
  let direction : ℕ → ι → ℝ := fun rank observer ↦
    quittingStoppingLawNormalizedDebtDirection reward
      (family.source rank) mover.1 (family.replacement mover rank)
      (family.scale rank) (family.scale_pos rank).le
      (family.scale_le_one rank) observer
  have hsumDirection : ∀ rank,
      (∑ observer, direction rank observer) =
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingStoppingLawResetProfile reward (family.source rank) mover.1
                (family.replacement mover rank) (family.scale rank)
                (family.scale_pos rank).le (family.scale_le_one rank))) -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward (family.source rank))) /
          family.scale rank := by
    intro rank
    dsimp only [direction, quittingStoppingLawNormalizedDebtDirection]
    rw [← Finset.sum_div]
    unfold quittingTerminalSemanticDebtSum quittingTerminalSemanticDebtChange
    rw [Finset.sum_sub_distrib]
  have hsumLimit : Tendsto (fun rank ↦ ∑ observer, direction rank observer)
      atTop (nhds (∑ observer, family.tangent mover observer)) :=
    tendsto_finsetSum Finset.univ fun observer _ ↦
      family.tangent_tendsto mover observer
  have hpointwise : ∀ rank,
      -((quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward (family.source rank)) -
          quittingTerminalSemanticDebtSum family.base) / family.scale rank) ≤
        ∑ observer, direction rank observer := by
    intro rank
    rw [hsumDirection]
    have htarget := quittingTerminalSemanticPair_mem_carrier reward
      (quittingStoppingLawResetProfile reward (family.source rank) mover.1
        (family.replacement mover rank) (family.scale rank)
        (family.scale_pos rank).le (family.scale_le_one rank))
    have hminimum := family.base_minimum _ htarget
    calc
      -((quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward (family.source rank)) -
            quittingTerminalSemanticDebtSum family.base) / family.scale rank) =
          (-(quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward (family.source rank)) -
            quittingTerminalSemanticDebtSum family.base)) / family.scale rank := by
            ring
      _ ≤ _ := (div_le_div_iff_of_pos_right (family.scale_pos rank)).2 (by linarith)
  have hleft : Tendsto (fun rank ↦
      -((quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward (family.source rank)) -
          quittingTerminalSemanticDebtSum family.base) / family.scale rank))
      atTop (nhds 0) := by
    simpa using family.source_excess_over_scale_tendsto_zero.neg
  exact le_of_tendsto_of_tendsto hleft hsumLimit
    (Eventually.of_forall hpointwise)

/-- The exact disjoint tangent alternative is derived from the primitive
family fields. -/
theorem QuittingPositiveMinimumDebtTangentFamily.exhaustiveAlternative
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingPositiveMinimumDebtTangentFamily reward) :
    IsQuittingStoppingLawExhaustiveTangentAlternative family.base
      (quittingPositiveDebtSupport family.base) family.tangent := by
  classical
  let active := quittingPositiveDebtSupport family.base
  let column := quittingActiveDebtTangentExtension active family.tangent
  let gain := quittingActiveDebtTangentGain active family.tangent
  by_cases hpositiveSlope : ∃ mover, 0 < ∑ observer, family.tangent mover observer
  · exact Or.inl hpositiveSlope
  have hflat : ∀ mover, ∑ observer, family.tangent mover observer = 0 := by
    intro mover
    exact le_antisymm (le_of_not_gt fun hgt ↦ hpositiveSlope ⟨mover, hgt⟩)
      (family.tangent_sum_nonneg mover)
  have hactiveNonempty : active.Nonempty := by
    simpa only [active,
      QuittingPositiveMinimumDebtTangentFamily.positiveDebtSupport] using
        family.positiveDebtSupport_nonempty
  letI : Nonempty ι := ⟨hactiveNonempty.choose⟩
  have hgain : ∀ mover ∈ active, 0 < gain mover := by
    intro mover hmover
    have hdiag := family.tangent_diagonal ⟨mover, hmover⟩
    have hdebtPos : 0 < quittingTerminalSemanticDebt family.base mover := by
      simpa [active, quittingPositiveDebtSupport] using hmover
    dsimp only [gain, quittingActiveDebtTangentGain,
      column, quittingActiveDebtTangentExtension]
    simp only [hmover, dite_true]
    linarith
  have hmoverLoss : ∀ mover ∈ active, column mover mover = -gain mover := by
    intro mover hmover
    dsimp only [gain, quittingActiveDebtTangentGain]
    ring
  have hcolumnFlat : ∀ mover ∈ active, ∑ who, column mover who = 0 := by
    intro mover hmover
    dsimp only [column, quittingActiveDebtTangentExtension]
    simp only [hmover, dite_true]
    exact hflat ⟨mover, hmover⟩
  have hzeroTangent : ∀ mover ∈ active, ∀ observer,
      quittingTerminalSemanticDebt family.base observer = 0 →
        0 ≤ column mover observer := by
    intro mover hmover observer hzero
    dsimp only [column, quittingActiveDebtTangentExtension]
    simp only [hmover, dite_true]
    exact family.tangent_inactive_nonneg ⟨mover, hmover⟩ observer hzero
  by_cases hentry : HasQuittingStoppingLawFlatSupportEntry family.base active family.tangent
  · exact Or.inr (Or.inl ⟨hflat, hentry⟩)
  have hdebtNonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt family.base who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward family.base_mem
  have hinactiveZero : ∀ mover ∈ active, ∀ who ∉ active, column mover who = 0 := by
    intro mover hmover who hwho
    have hdebtZero : quittingTerminalSemanticDebt family.base who = 0 := by
      apply le_antisymm
      · exact le_of_not_gt fun hpositive ↦
          hwho (by simpa [active, quittingPositiveDebtSupport] using hpositive)
      · exact hdebtNonneg who
    apply le_antisymm
    · exact le_of_not_gt fun hpositive ↦
        hentry ⟨mover, hmover, who, hdebtZero, hpositive⟩
    · exact hzeroTangent mover hmover who hdebtZero
  have hduality := flatDebtTangent_chargedCirculation_xor_nonnegativePotential
    (fun mover : {who // who ∈ active} ↦ column mover.1)
    (fun mover : {who // who ∈ active} ↦ gain mover.1)
    (fun mover ↦ hcolumnFlat mover.1 mover.2)
  rcases hduality with ⟨hcirculation, _⟩ | ⟨hpotential, hnotCirculation⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hflat, hentry, hcirculation⟩))
  · obtain ⟨potential, hpotentialNonneg, hpotential⟩ := hpotential
    obtain ⟨mover, hmover, hmoverMax⟩ :=
      Finset.exists_max_image active potential hactiveNonempty
    have hpotentialAll : ∀ source ∈ active,
        gain source ≤ ∑ who, potential who * column source who := by
      intro source hsource
      exact hpotential ⟨source, hsource⟩
    obtain ⟨other, hother, hotherDecrease⟩ :=
      exists_active_coDecrease_of_flat_chargedPotential_at_max active
        (column mover) potential mover (gain mover) (hcolumnFlat mover hmover)
        (hgain mover hmover) (hpotentialAll mover hmover) hmoverMax
        (hinactiveZero mover hmover)
    exact Or.inr (Or.inr (Or.inr ⟨hflat, hentry, hnotCirculation,
      potential, mover, hmover, other, hother, hpotentialNonneg, hpotentialAll,
      hmoverMax, hmoverLoss mover hmover, hotherDecrease⟩))

/-- Forget the disjoint tags to the coarser tangent alternative. -/
theorem QuittingPositiveMinimumDebtTangentFamily.alternative
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingPositiveMinimumDebtTangentFamily reward) :
    IsQuittingStoppingLawTangentAlternative family.base
      (quittingPositiveDebtSupport family.base) family.tangent :=
  family.exhaustiveAlternative.toTangentAlternative

/-- Core stopping-law extraction from a specified positive global minimum.
The returned equality preserves the chosen base for later minimum-fiber
re-extraction. -/
theorem exists_positiveMinimumDebtTangentFamily_of_pair
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (base : QuittingTerminalSemanticPair ι)
    (hbase : base ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hbasePositive : 0 < quittingTerminalSemanticDebtSum base) :
    ∃ family : QuittingPositiveMinimumDebtTangentFamily reward,
      family.base = base := by
  classical
  obtain ⟨rawProfiles, hrawProfiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward base hbase
  let active := quittingPositiveDebtSupport base
  have hactive : ∀ who, who ∈ active ↔
      0 < quittingTerminalSemanticDebt base who := by
    intro who
    simp only [active, quittingPositiveDebtSupport, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have heventuallyActive : ∀ᶠ n in atTop, ∀ who ∈ active,
      0 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (rawProfiles n)) who := by
    rw [eventually_all]
    intro who
    by_cases hwho : who ∈ active
    · have hcoordinate : Tendsto (fun n ↦ quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (rawProfiles n)) who)
          atTop (nhds (quittingTerminalSemanticDebt base who)) := by
        exact (continuous_quittingTerminalSemanticDebt who).tendsto base |>.comp
          hrawProfiles
      filter_upwards [hcoordinate.eventually
          (Ioi_mem_nhds ((hactive who).1 hwho))] with _ hpositive
      exact fun _ ↦ hpositive
    · exact Eventually.of_forall fun _ hmem ↦ False.elim (hwho hmem)
  obtain ⟨start, hstart⟩ := eventually_atTop.1 heventuallyActive
  let profiles : ℕ → (quittingGame reward).BehaviorProfile :=
    fun n ↦ rawProfiles (n + start)
  have hprofiles : Tendsto
      (fun n ↦ quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds base) := by
    exact (tendsto_add_atTop_iff_nat start).2 hrawProfiles
  have hsourceActive : ∀ n, ∀ who ∈ active,
      0 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) who := by
    intro n who hwho
    exact hstart (n + start) (Nat.le_add_left start n) who hwho
  let epsilon : ℕ → ℝ := fun n ↦
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profiles n)) -
      quittingTerminalSemanticDebtSum base
  have hepsilonNonneg : ∀ n, 0 ≤ epsilon n := by
    intro n
    dsimp only [epsilon]
    exact sub_nonneg.mpr (hminimum _
      (quittingTerminalSemanticPair_mem_carrier reward (profiles n)))
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    have hsum : Tendsto (fun n ↦ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profiles n))) atTop
        (nhds (quittingTerminalSemanticDebtSum base)) := by
      exact continuous_quittingTerminalSemanticDebtSum.tendsto base |>.comp
        hprofiles
    have hconst : Tendsto
        (fun _ : ℕ ↦ quittingTerminalSemanticDebtSum base) atTop
        (nhds (quittingTerminalSemanticDebtSum base)) := tendsto_const_nhds
    simpa only [epsilon, sub_self] using hsum.sub hconst
  let inactiveDebt : ι → ℕ → ℝ := fun who n ↦
    if quittingTerminalSemanticDebt base who = 0 then
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) who
    else 0
  have hinactiveNonneg : ∀ who n, 0 ≤ inactiveDebt who n := by
    intro who n
    dsimp only [inactiveDebt]
    split_ifs
    · exact quittingTerminalDeviationDebt_nonneg reward (profiles n) who
    · exact le_rfl
  have hinactiveZero : ∀ who,
      Tendsto (inactiveDebt who) atTop (nhds 0) := by
    intro who
    dsimp only [inactiveDebt]
    by_cases hzero : quittingTerminalSemanticDebt base who = 0
    · simp only [hzero, if_pos]
      have hcoordinate : Tendsto (fun n ↦ quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (profiles n)) who)
          atTop (nhds (quittingTerminalSemanticDebt base who)) := by
        exact (continuous_quittingTerminalSemanticDebt who).tendsto base |>.comp
          hprofiles
      simpa only [hzero] using hcoordinate
    · simp only [hzero]
      exact tendsto_const_nhds
  obtain ⟨lambda, hlambdaPos, hlambdaLe, hlambdaZero,
      hepsilonRate, hinactiveRate⟩ :=
    exists_commonVanishingResetScale epsilon inactiveDebt
      hepsilonNonneg hinactiveNonneg hepsilonZero hinactiveZero
  have hnear : ∀ n, ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles n)) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon n := by
    intro n candidate hcandidate
    dsimp only [epsilon]
    have hbaseLe := hminimum candidate hcandidate
    linarith
  have hinactiveRate' : ∀ who,
      quittingTerminalSemanticDebt base who = 0 →
      Tendsto (fun n ↦
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles n)) who /
          lambda n) atTop (nhds 0) := by
    intro who hzero
    simpa only [inactiveDebt, hzero, if_pos] using hinactiveRate who
  obtain ⟨bestResponse, subseq, tangent, hsubseq, hlambdaSubseq,
      htangent, hendpointDebtLeTolerance, _hendpointDebtZero, _hdiagonalEq,
      htangentInactive, _hsumNonneg, _hslopeAlternative⟩ :=
    exists_commonBase_stoppingLawDebtTangentFamily_exactDiagonal
      reward base profiles active epsilon lambda
      hprofiles hsourceActive hnear hlambdaPos hlambdaLe hlambdaZero
      hepsilonRate hinactiveRate'
  refine ⟨{
    base := base
    source := fun rank ↦ profiles (subseq rank)
    scale := fun rank ↦ lambda (subseq rank)
    scale_pos := fun rank ↦ hlambdaPos (subseq rank)
    scale_le_one := fun rank ↦ hlambdaLe (subseq rank)
    replacement := fun mover rank ↦ bestResponse mover (subseq rank)
    tangent := tangent
    base_mem := hbase
    base_minimum := hminimum
    base_positive := hbasePositive
    source_tendsto := hprofiles.comp hsubseq.tendsto_atTop
    scale_tendsto_zero := hlambdaSubseq
    source_excess_over_scale_tendsto_zero := by
      simpa only [epsilon, Function.comp_def] using
        hepsilonRate.comp hsubseq.tendsto_atTop
    tangent_tendsto := htangent
    replacement_moverDebt_le_tolerance := hendpointDebtLeTolerance
    tangent_inactive_nonneg := htangentInactive
  }, rfl⟩

/-- Every positive minimum terminal-semantic debt datum supplies a tangent
family, without any terminal exploitability witness. -/
theorem nonempty_positiveMinimumDebtTangentFamily
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hminimum : HasPositiveMinimumTerminalSemanticDebt reward) :
    Nonempty (QuittingPositiveMinimumDebtTangentFamily reward) := by
  obtain ⟨base, hbase, hglobal, hpositive⟩ := hminimum
  obtain ⟨family, _⟩ :=
    exists_positiveMinimumDebtTangentFamily_of_pair base hbase hglobal hpositive
  exact ⟨family⟩

end GameTheory
