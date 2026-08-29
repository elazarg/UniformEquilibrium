/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourPaidResetDoubleDescentRegeneration
import Research.Quitting.PaidCapMaximalOneStepRegeneration

/-!
# Canonical maximal-root reduction of the Fin4 paid-cap double port

A selector-independent unique-all-Continue cap forces every root of every
selected paid-cap lift to be all Continue.  Hence its complete selected port is
literally inert, and a quantitative debt descent cannot enter that arm.

For the Fin4 singleton source and its owner repair, the retained zero-debt
coordinates and positive opponent incidences let us apply the canonical
maximal-root theorem to both actual profiles.  The double-port boundary is
therefore reduced to a source-side one-step paid/reset regeneration, a
repaired-side one-step paid/reset regeneration, or two genuinely unique
all-Continue caps.  The last obstruction is independent of the arbitrary
selectors stored in the two paid-cap ports.

This file does not prove that the double unique-cap obstruction is impossible,
and strict real-valued debt descent is not itself well founded.
-/

noncomputable section

namespace GameTheory

open Finset
open Math.Probability Math.PMFProduct

namespace QuittingPaidCapLiftedSource

variable
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A unique all-Continue cap makes every finite selected cap-prefix semantic
pair equal to the source pair. -/
theorem semanticPair_eq_of_uniqueAllContinueAtCap
    (source : QuittingPaidCapLiftedSource reward)
    (unique : source.HasUniqueAllContinueAtCap) (time : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingCapLiftedPrefixProfile reward source.profile time) =
      quittingTerminalSemanticPair reward source.profile := by
  induction time with
  | zero => rfl
  | succ time ih =>
      let root := quittingCapLiftedPrefixRoot reward
        (quittingCapLiftedPrefixProfile reward source.profile time)
      have hnash : IsεQuittingRootNash reward
          (quittingTerminalSemanticPair reward
            (quittingCapLiftedPrefixProfile reward source.profile time)).2
          0 root := by
        simpa [root] using
          (quittingCapLiftedPrefixRoot_exactNash reward
            (quittingCapLiftedPrefixProfile reward source.profile time))
      have hroot : root = (quittingAllContinueRoot : ι → PMF Bool) := by
        apply unique root
        simpa only [ih] using hnash
      rw [quittingCapLiftedPrefixProfile_semanticPair_succ]
      change quittingTerminalSemanticPrefix reward root
          (quittingTerminalSemanticPair reward
            (quittingCapLiftedPrefixProfile reward source.profile time)) = _
      rw [hroot]
      calc
        quittingTerminalSemanticPrefix reward quittingAllContinueRoot
            (quittingTerminalSemanticPair reward
              (quittingCapLiftedPrefixProfile reward source.profile time)) =
            quittingTerminalSemanticPair reward
              (quittingCapLiftedPrefixProfile reward source.profile time) := by
          apply
            (quittingTerminalSemanticPrefix_allContinue_eq_self_iff_isZeroNash_at_cap
              reward _).2
          simpa only [hroot] using hnash
        _ = quittingTerminalSemanticPair reward source.profile := ih

/-- Every selected cap-prefix root is literally all Continue under a unique
all-Continue source cap. -/
theorem capLiftedPrefixRoot_eq_allContinue_of_uniqueAllContinueAtCap
    (source : QuittingPaidCapLiftedSource reward)
    (unique : source.HasUniqueAllContinueAtCap) (time : ℕ) :
    quittingCapLiftedPrefixRoot reward
        (quittingCapLiftedPrefixProfile reward source.profile time) =
      (quittingAllContinueRoot : ι → PMF Bool) := by
  apply unique
  have hnash := quittingCapLiftedPrefixRoot_exactNash reward
    (quittingCapLiftedPrefixProfile reward source.profile time)
  simpa only [source.semanticPair_eq_of_uniqueAllContinueAtCap unique time]
    using hnash

/-- The complete absorption of any selected paid-cap lift vanishes under a
unique all-Continue cap. -/
theorem totalAbsorption_eq_zero_of_uniqueAllContinueAtCap
    (source : QuittingPaidCapLiftedSource reward)
    (unique : source.HasUniqueAllContinueAtCap) :
    source.totalAbsorption = 0 := by
  unfold totalAbsorption
  simp only [
    source.capLiftedPrefixRoot_eq_allContinue_of_uniqueAllContinueAtCap unique,
    quittingRootAbsorptionMass_allContinueRoot, tsum_zero]

/-- Selector-independent uniqueness implies the full literal inert record for
any supplied summable paid-cap port. -/
theorem inertStall_of_uniqueAllContinueAtCap
    (source : QuittingPaidCapLiftedSource reward)
    (port : source.SummablePort)
    (unique : source.HasUniqueAllContinueAtCap) :
    source.InertStall port :=
  source.inertStall_of_totalAbsorption_eq_zero port
    (source.totalAbsorption_eq_zero_of_uniqueAllContinueAtCap unique)

/-- Canonical maximal regeneration or the complete inert record for an
arbitrary selected port. -/
theorem maximalOneStepPaidResetRegeneration_or_inertStall
    (source : QuittingPaidCapLiftedSource reward)
    (port : source.SummablePort)
    (witness : QuittingTerminalExploitabilityWitness reward)
    (resetOwner other : ι)
    (hreset : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward source.profile) resetOwner = 0)
    (hincidence : 0 < quittingTerminalOpponentIncidenceMass resetOwner other
      (quittingTerminalOutcomeMass reward source.profile)) :
    Nonempty (source.MaximalOneStepPaidResetRegeneration resetOwner other) ∨
      source.InertStall port := by
  rcases source.maximalOneStepPaidResetRegeneration_or_uniqueAllContinue
      witness resetOwner other hreset hincidence with regeneration | unique
  · exact Or.inl regeneration
  · exact Or.inr (source.inertStall_of_uniqueAllContinueAtCap port unique)

/-- A selected quantitative descent rules out the unique-cap arm and therefore
forces an immediate canonical maximal-root paid/reset regeneration. -/
theorem nonempty_maximalOneStepPaidResetRegeneration_of_quantitativeDebtDescent
    (source : QuittingPaidCapLiftedSource reward)
    (port : source.SummablePort)
    (descent : source.QuantitativeDebtDescent port)
    (witness : QuittingTerminalExploitabilityWitness reward)
    (resetOwner other : ι)
    (hreset : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward source.profile) resetOwner = 0)
    (hincidence : 0 < quittingTerminalOpponentIncidenceMass resetOwner other
      (quittingTerminalOutcomeMass reward source.profile)) :
    Nonempty (source.MaximalOneStepPaidResetRegeneration resetOwner other) := by
  rcases source.maximalOneStepPaidResetRegeneration_or_uniqueAllContinue
      witness resetOwner other hreset hincidence with regeneration | unique
  · exact regeneration
  · have inert := source.inertStall_of_uniqueAllContinueAtCap port unique
    exfalso
    rw [inert.capDisplacement_zero] at descent.displacement_pos
    exact lt_irrefl 0 descent.displacement_pos

end QuittingPaidCapLiftedSource

namespace FinFourSingletonBaseResetRepairPaidCapDoublePort

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}
  {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
  {owner : Fin 4}

/-- The original singleton source retains a zero-debt reset owner. -/
theorem sourceResetOwner_debt_eq_zero
    (double : FinFourSingletonBaseResetRepairPaidCapDoublePort
      reward bound residual owner) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          double.chain.sourceCapLiftedSource.profile)
        double.chain.producer.resetOwner = 0 := by
  have hresetMem : double.chain.producer.resetOwner ∈
      finFourSingletonBaseFree owner := by
    simp [finFourSingletonBaseFree,
      double.chain.producer.resetOwner_ne_owner]
  rw [double.chain.sourceCapLiftedSource_profile]
  exact (double.chain.producer.free_solved
    double.chain.producer.resetOwner hresetMem).1

/-- The original singleton source has positive reset-owner incidence against
its sure-Quit singleton owner. -/
theorem sourceResetOwner_owner_positiveIncidence
    (double : FinFourSingletonBaseResetRepairPaidCapDoublePort
      reward bound residual owner) :
    0 < quittingTerminalOpponentIncidenceMass
      double.chain.producer.resetOwner owner
        (quittingTerminalOutcomeMass reward
          double.chain.sourceCapLiftedSource.profile) := by
  rw [double.chain.sourceCapLiftedSource_profile,
    double.chain.producer.reset_incidence]
  norm_num

/-- The repaired singleton owner has exact zero semantic debt. -/
theorem repairedOwner_debt_eq_zero
    (double : FinFourSingletonBaseResetRepairPaidCapDoublePort
      reward bound residual owner) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          double.chain.repairedCapLiftedSource.profile) owner = 0 := by
  rw [double.chain.repairedCapLiftedSource_profile]
  change quittingStationaryUnilateralCap reward
      (quittingSingletonBaseRepairedRoot owner
        (finFourSingletonBaseFree owner) double.chain.producer.point) owner -
    quittingTerminalPayoff reward
      (quittingSingletonBaseRepairedProfile reward owner
        (finFourSingletonBaseFree owner) double.chain.producer.point) owner = 0
  exact sub_eq_zero.mpr double.chain.repair.repaired_owner_cap_eq_payoff

/-- The two actual profiles of the Fin4 double port admit a canonical
selector-independent boundary: one side regenerates immediately through its
maximal exact cap root, or both caps have all Continue as their unique exact
root. -/
theorem sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique
    (double : FinFourSingletonBaseResetRepairPaidCapDoublePort
      reward bound residual owner) :
    Nonempty
        (double.chain.sourceCapLiftedSource.MaximalOneStepPaidResetRegeneration
          double.chain.producer.resetOwner owner) ∨
      (∃ other : Fin 4,
        Nonempty
          (double.chain.repairedCapLiftedSource.MaximalOneStepPaidResetRegeneration
            owner other)) ∨
        (double.chain.sourceCapLiftedSource.HasUniqueAllContinueAtCap ∧
          double.chain.repairedCapLiftedSource.HasUniqueAllContinueAtCap) := by
  rcases double.chain.sourceCapLiftedSource.
      maximalOneStepPaidResetRegeneration_or_uniqueAllContinue
        residual.witness double.chain.producer.resetOwner owner
        double.sourceResetOwner_debt_eq_zero
        double.sourceResetOwner_owner_positiveIncidence with
      sourceRegeneration | sourceUnique
  · exact Or.inl sourceRegeneration
  obtain ⟨other, _other_ne, repairedIncidence⟩ :=
    double.exists_repairedOwner_positiveIncidence
  rcases double.chain.repairedCapLiftedSource.
      maximalOneStepPaidResetRegeneration_or_uniqueAllContinue
        residual.witness owner other double.repairedOwner_debt_eq_zero
        repairedIncidence with repairedRegeneration | repairedUnique
  · exact Or.inr (Or.inl ⟨other, repairedRegeneration⟩)
  · exact Or.inr (Or.inr ⟨sourceUnique, repairedUnique⟩)

/-- In the final structural arm, both arbitrary selected ports carry their full
literal inert records as a consequence of cap uniqueness. -/
theorem sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUniqueInert
    (double : FinFourSingletonBaseResetRepairPaidCapDoublePort
      reward bound residual owner) :
    Nonempty
        (double.chain.sourceCapLiftedSource.MaximalOneStepPaidResetRegeneration
          double.chain.producer.resetOwner owner) ∨
      (∃ other : Fin 4,
        Nonempty
          (double.chain.repairedCapLiftedSource.MaximalOneStepPaidResetRegeneration
            owner other)) ∨
        ((double.chain.sourceCapLiftedSource.HasUniqueAllContinueAtCap ∧
            double.chain.repairedCapLiftedSource.HasUniqueAllContinueAtCap) ∧
          (QuittingPaidCapLiftedSource.InertStall
              double.chain.sourceCapLiftedSource double.sourcePort ∧
            QuittingPaidCapLiftedSource.InertStall
              double.chain.repairedCapLiftedSource double.repairedPort)) := by
  rcases double.sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique
      with sourceRegeneration | repairedRegeneration | doubleUnique
  · exact Or.inl sourceRegeneration
  · exact Or.inr (Or.inl repairedRegeneration)
  · exact Or.inr (Or.inr ⟨doubleUnique,
      double.chain.sourceCapLiftedSource.inertStall_of_uniqueAllContinueAtCap
        double.sourcePort doubleUnique.1,
      double.chain.repairedCapLiftedSource.inertStall_of_uniqueAllContinueAtCap
        double.repairedPort doubleUnique.2⟩)

end FinFourSingletonBaseResetRepairPaidCapDoublePort

namespace FinFourQuantitativeFullSupportHardResidual

/-- Direct hard-residual projection of the canonical Fin4 double-port boundary.
The supplied owner is arbitrary. -/
theorem exists_paidCapDoublePort_maximalRegeneration_or_doubleUnique
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (owner : Fin 4) :
    ∃ double : FinFourSingletonBaseResetRepairPaidCapDoublePort
        reward bound residual owner,
      Nonempty
          (double.chain.sourceCapLiftedSource.MaximalOneStepPaidResetRegeneration
            double.chain.producer.resetOwner owner) ∨
        (∃ other : Fin 4,
          Nonempty
            (double.chain.repairedCapLiftedSource.MaximalOneStepPaidResetRegeneration
              owner other)) ∨
          (double.chain.sourceCapLiftedSource.HasUniqueAllContinueAtCap ∧
            double.chain.repairedCapLiftedSource.HasUniqueAllContinueAtCap) := by
  obtain ⟨double⟩ := residual.nonempty_paidCapDoublePort hreward owner
  exact ⟨double,
    double.sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique⟩

end FinFourQuantitativeFullSupportHardResidual

end GameTheory
