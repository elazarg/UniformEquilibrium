/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourPaidResetDescentRegeneration
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio

/-!
# Finite paid/reset regeneration on both Fin4 paid-cap descent arms

The singleton source and its literal owner repair have separate paid-cap ports.
The source-side quantitative descent already regenerates a finite actual
paid/reset source.  This file supplies the missing repaired-side provenance.

The retained positive strict-superset atom forces one free player to use a
positive Quit hazard.  The owner repair changes only the owner coordinate, so
that free Quit hazard survives.  It yields positive first-root opponent
incidence for the repaired owner, and stationarity lifts that incidence to the
complete repaired terminal law.  The repaired owner has zero semantic debt.
Therefore every repaired-port quantitative descent enters the existing finite
paid/reset regeneration consumer.

The resulting exact boundary has two regenerated descent arms and one literal
double-inert arm.  It does not make repeated real-valued descent well founded
and does not consume the double-inert arm.
-/

noncomputable section

namespace GameTheory

open Finset
open Math.Probability Math.PMFProduct

namespace FinFourSingletonBaseResetRepairPaidCapDoublePort

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}
  {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
  {owner : Fin 4}

/-- The repaired stationary source has a positive opponent-incidence coordinate
for its zero-debt owner.  The witness is selected from the positive atom already
retained by the original singleton source. -/
theorem exists_repairedOwner_positiveIncidence
    (double : FinFourSingletonBaseResetRepairPaidCapDoublePort
      reward bound residual owner) :
    ∃ other : Fin 4, other ≠ owner ∧
      0 < quittingTerminalOpponentIncidenceMass owner other
        (quittingTerminalOutcomeMass reward
          double.chain.repairedCapLiftedSource.profile) := by
  let producer := double.chain.producer
  let sourceRoot := finFourSingletonBaseRoot owner producer.point
  let sourceProfile := finFourSingletonBaseProfile reward owner producer.point
  let sourceMass := quittingTerminalOutcomeMass reward sourceProfile
  obtain ⟨other, hotherAtom⟩ := producer.atomFree_nonempty
  have hotherFree : other ∈ finFourSingletonBaseFree owner :=
    producer.atomFree_subset hotherAtom
  have hotherNe : other ≠ owner := by
    simpa [finFourSingletonBaseFree] using hotherFree
  have hsourceOwner : sourceRoot owner = PMF.pure true := by
    exact quittingPersistentBaseRoot_apply_of_mem_base
      ({owner} : Finset (Fin 4)) (finFourSingletonBaseFree owner)
      producer.point (by simp)
  have hsourceContinue : quittingStationaryContinueMass sourceRoot = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hsourceOwner
  let terminal : {S : Finset (Fin 4) // S.Nonempty} :=
    ⟨insert owner producer.atomFree,
      Finset.insert_nonempty owner producer.atomFree⟩
  have hterminalMass : sourceMass (some terminal) =
      quittingRootCoalitionMass sourceRoot terminal.val := by
    change quittingAbsorbedMassLimit reward sourceProfile terminal = _
    have hprefix := quittingAbsorbedMassLimit_rootThenContinuation
      reward sourceRoot sourceProfile terminal
    have hsplice : quittingRootThenContinuationProfile reward sourceRoot
        sourceProfile = sourceProfile := by
      exact quittingRootThenContinuationProfile_stationary reward sourceRoot
    rw [hsplice, hsourceContinue, zero_mul, add_zero] at hprefix
    exact hprefix
  have hdenominator :
      0 < 7 * (residual.witness.terminalGap + 2 * bound) := by
    have hsum : 0 < residual.witness.terminalGap + 2 * bound := by
      nlinarith [residual.witness.terminalGap_pos, producer.bound_pos]
    exact mul_pos (by norm_num) hsum
  have hlowerPos :
      0 < residual.witness.terminalGap /
        (7 * (residual.witness.terminalGap + 2 * bound)) :=
    div_pos residual.witness.terminalGap_pos hdenominator
  have hsourceAtomPos : 0 < sourceMass (some terminal) := by
    apply hlowerPos.trans_le
    simpa [sourceMass, sourceProfile, terminal, producer] using
      producer.atom_mass_lower
  have hsourceRootAtomPos :
      0 < quittingRootCoalitionMass sourceRoot terminal.val := by
    rw [← hterminalMass]
    exact hsourceAtomPos
  have hotherTerminal : other ∈ terminal.val := by
    simp [terminal, hotherAtom]
  have hsourceQuitPos : 0 < (sourceRoot other true).toReal :=
    hsourceRootAtomPos.trans_le
      (quittingRootCoalitionMass_le_quitProbability_of_mem
        sourceRoot terminal.val other hotherTerminal)
  let repairedRoot := quittingSingletonBaseRepairedRoot owner
    (finFourSingletonBaseFree owner) producer.point
  have hrepairedOther : repairedRoot other = sourceRoot other := by
    simp [repairedRoot, quittingSingletonBaseRepairedRoot, sourceRoot,
      finFourSingletonBaseRoot, hotherNe]
  have hrepairedQuitPos : 0 < (repairedRoot other true).toReal := by
    rw [hrepairedOther]
    exact hsourceQuitPos
  have hrootIncidenceNonneg : 0 ≤
      quittingRootOpponentIncidenceMass owner other repairedRoot := by
    unfold quittingRootOpponentIncidenceMass
    exact Finset.sum_nonneg fun candidate _ =>
      MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
        repairedRoot candidate.val
  have hrootIncidenceNe :
      quittingRootOpponentIncidenceMass owner other repairedRoot ≠ 0 := by
    intro hzero
    have hpure := root_eq_pureContinue_of_opponentIncidence_eq_zero
      owner other repairedRoot hotherNe hzero
    have hquitZero : (repairedRoot other true).toReal = 0 := by
      rw [hpure]
      norm_num
    linarith
  have hrootIncidencePos : 0 <
      quittingRootOpponentIncidenceMass owner other repairedRoot :=
    lt_of_le_of_ne hrootIncidenceNonneg (Ne.symm hrootIncidenceNe)
  let repairedProfile := quittingSingletonBaseRepairedProfile reward owner
    (finFourSingletonBaseFree owner) producer.point
  let repairedMass := quittingTerminalOutcomeMass reward repairedProfile
  have hlaw : repairedMass =
      quittingTerminalOutcomeLawPrefix repairedRoot repairedMass := by
    symm
    simpa only [repairedMass, repairedProfile, repairedRoot,
      quittingSingletonBaseRepairedProfile,
      quittingRootThenContinuationProfile_stationary] using
      (quittingTerminalOutcomeLawPrefix_outcomeMass
        reward repairedRoot repairedProfile)
  have hterminalIncidenceNonneg : 0 ≤
      quittingTerminalOpponentIncidenceMass owner other repairedMass := by
    unfold quittingTerminalOpponentIncidenceMass
    exact Finset.sum_nonneg fun candidate _ =>
      (quittingTerminalOutcomeMass_mem_stdSimplex
        reward repairedProfile).1 (some candidate)
  have hterminalIncidencePos : 0 <
      quittingTerminalOpponentIncidenceMass owner other repairedMass := by
    rw [hlaw, quittingTerminalOpponentIncidenceMass_lawPrefix]
    exact add_pos_of_pos_of_nonneg hrootIncidencePos
      (mul_nonneg (quittingStationaryContinueMass_nonneg repairedRoot)
        hterminalIncidenceNonneg)
  refine ⟨other, hotherNe, ?_⟩
  simpa [repairedMass, repairedProfile, producer] using
    hterminalIncidencePos

/-- A quantitative descent on the repaired paid-cap port regenerates a finite
actual paid/reset source.  The reset owner is the repaired singleton owner. -/
theorem exists_repairedPaidResetRegeneration
    (double : FinFourSingletonBaseResetRepairPaidCapDoublePort
      reward bound residual owner)
    (descent : QuittingPaidCapLiftedSource.QuantitativeDebtDescent
      double.chain.repairedCapLiftedSource double.repairedPort) :
    ∃ other : Fin 4,
      Nonempty
        (double.chain.repairedCapLiftedSource.FinitePaidResetRegeneration
          double.repairedPort owner other) := by
  obtain ⟨other, _hotherNe, hincidence⟩ :=
    double.exists_repairedOwner_positiveIncidence
  have hreset : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        double.chain.repairedCapLiftedSource.profile) owner = 0 := by
    rw [double.chain.repairedCapLiftedSource_profile]
    change quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingStationaryProfile reward
          (quittingSingletonBaseRepairedRoot owner
            (finFourSingletonBaseFree owner) double.chain.producer.point)))
        owner = 0
    unfold quittingTerminalSemanticDebt
    rw [quittingTerminalSemanticPair_stationary_envelope_eq_cap]
    exact sub_eq_zero.mpr double.chain.repair.repaired_owner_cap_eq_payoff
  exact ⟨other,
    QuittingPaidCapLiftedSource.QuantitativeDebtDescent.nonempty_finitePaidResetRegeneration
      double.chain.repairedCapLiftedSource double.repairedPort descent
      residual.witness owner other hreset hincidence⟩

/-- Both quantitative descent arms now retain actual finite paid/reset
provenance.  The only remaining arm of the double-port contraction is the
literal double-inert stall. -/
theorem sourcePaidResetRegeneration_or_repairedPaidResetRegeneration_or_doubleInert
    (double : FinFourSingletonBaseResetRepairPaidCapDoublePort
      reward bound residual owner) :
    Nonempty
        (double.chain.sourceCapLiftedSource.FinitePaidResetRegeneration
          double.sourcePort double.chain.producer.resetOwner owner) ∨
      (∃ other : Fin 4,
        Nonempty
          (double.chain.repairedCapLiftedSource.FinitePaidResetRegeneration
            double.repairedPort owner other)) ∨
        (QuittingPaidCapLiftedSource.InertStall
            double.chain.sourceCapLiftedSource double.sourcePort ∧
          QuittingPaidCapLiftedSource.InertStall
            double.chain.repairedCapLiftedSource double.repairedPort) := by
  rcases double.sourceDescent_or_repairedDescent_or_doubleInert with
    sourceDescent | repairedDescent | doubleInert
  · exact Or.inl (double.nonempty_sourcePaidResetRegeneration sourceDescent)
  · exact Or.inr (Or.inl
      (double.exists_repairedPaidResetRegeneration repairedDescent))
  · exact Or.inr (Or.inr doubleInert)

end FinFourSingletonBaseResetRepairPaidCapDoublePort

end GameTheory
