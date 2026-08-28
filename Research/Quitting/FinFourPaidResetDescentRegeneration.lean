/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.SingletonBaseResetRepairPaidCapDoublePort

/-!
# Finite paid/reset regeneration after Fin4 cap descent

A quantitative descent in the paid-cap port converges only at a carrier point,
but strictness is already visible at a finite literal prefix.  That finite
profile retains the exact shifted paid row.  If the original source has a
zero-debt reset coordinate and positive same-profile incidence, cap-prefixing
preserves both properties: coordinate debt is antitone, and the old incidence
is transported with at least the joint all-Continue survival factor.

The terminal witness can therefore run the fixed-law reset dispatcher again at
that finite lower-debt profile.  For the singleton source selected from a
quantitative Fin4 hard residual, this consumes the source-side descent arm of
the paid-cap trichotomy.  The remaining source-side branch is the literal inert
stall.  No well-foundedness of repeated real-valued descent is claimed.
-/

noncomputable section

namespace GameTheory

open Filter Finset

/-- Survival through a finite cap-prefix transports at least the corresponding
fraction of every old opponent-incidence coordinate. -/
theorem quittingCapLiftedSuffixReach_mul_opponentIncidence_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (marked other : ι) (horizon : ℕ) :
    quittingCapLiftedSuffixReach reward terminal horizon *
          quittingTerminalOpponentIncidenceMass marked other
            (quittingTerminalOutcomeMass reward terminal) ≤
      quittingTerminalOpponentIncidenceMass marked other
        (quittingTerminalOutcomeMass reward
          (quittingCapLiftedPrefixProfile reward terminal horizon)) := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      let profile := quittingCapLiftedPrefixProfile reward terminal horizon
      let root := quittingCapLiftedPrefixRoot reward profile
      have hlaw :
          quittingTerminalOutcomeMass reward
              (quittingCapLiftedPrefixProfile reward terminal (horizon + 1)) =
            quittingTerminalOutcomeLawPrefix root
              (quittingTerminalOutcomeMass reward profile) := by
        rw [quittingCapLiftedPrefixProfile_succ]
        exact (quittingTerminalOutcomeLawPrefix_outcomeMass
          reward root profile).symm
      rw [hlaw, quittingCapLiftedSuffixReach_succ]
      have hcontinue : 0 ≤ quittingStationaryContinueMass root :=
        quittingStationaryContinueMass_nonneg root
      calc
        quittingCapLiftedSuffixReach reward terminal horizon *
              quittingStationaryContinueMass root *
              quittingTerminalOpponentIncidenceMass marked other
                (quittingTerminalOutcomeMass reward terminal) =
            quittingStationaryContinueMass root *
              (quittingCapLiftedSuffixReach reward terminal horizon *
                quittingTerminalOpponentIncidenceMass marked other
                  (quittingTerminalOutcomeMass reward terminal)) := by ring
        _ ≤ quittingStationaryContinueMass root *
              quittingTerminalOpponentIncidenceMass marked other
                (quittingTerminalOutcomeMass reward profile) :=
          mul_le_mul_of_nonneg_left ih hcontinue
        _ ≤ quittingTerminalOpponentIncidenceMass marked other
              (quittingTerminalOutcomeLawPrefix root
                (quittingTerminalOutcomeMass reward profile)) :=
          quittingStationaryContinueMass_mul_incidence_le_lawPrefix
            marked other root (quittingTerminalOutcomeMass reward profile)

namespace QuittingPaidCapLiftedSource

variable
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The actual paid source at one finite cap-prefix.  Its suffix is literally
`source.profile`, and its paid row is the exact shifted row stored by `port`. -/
noncomputable def finitePrefixSource
    (source : QuittingPaidCapLiftedSource reward)
    (port : source.SummablePort) (horizon : ℕ) :
    QuittingPaidCapLiftedSource reward where
  minimum := source.minimum
  minimum_le := source.minimum_le
  minimum_pos := source.minimum_pos
  profile := quittingCapLiftedPrefixProfile reward source.profile horizon
  observer := source.observer
  gain := source.reachFloor * source.gain
  gain_pos := mul_pos source.reachFloor_pos source.gain_pos
  row := (port.shiftedRows horizon).row

@[simp] theorem finitePrefixSource_profile
    (source : QuittingPaidCapLiftedSource reward)
    (port : source.SummablePort) (horizon : ℕ) :
    (source.finitePrefixSource port horizon).profile =
      quittingCapLiftedPrefixProfile reward source.profile horizon := rfl

@[simp] theorem finitePrefixSource_minimum
    (source : QuittingPaidCapLiftedSource reward)
    (port : source.SummablePort) (horizon : ℕ) :
    (source.finitePrefixSource port horizon).minimum = source.minimum := rfl

/-- A quantitative limiting descent realized at one finite literal profile,
with the shifted paid row, an inherited zero-debt reset coordinate, positive
same-profile reset incidence, and a fresh fixed-law reset dispatch. -/
structure FinitePaidResetRegeneration
    (source : QuittingPaidCapLiftedSource reward)
    (port : source.SummablePort) (resetOwner other : ι) where
  horizon : ℕ
  strict_debt :
    (source.finitePrefixSource port horizon).initialDebt < source.initialDebt
  target_joint :
    (quittingTerminalSemanticPair reward
        (source.finitePrefixSource port horizon).profile,
      quittingTerminalOutcomeMass reward
        (source.finitePrefixSource port horizon).profile) ∈
      quittingTerminalSemanticLawCarrier reward
  reset_debt :
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (source.finitePrefixSource port horizon).profile) resetOwner = 0
  reset_incidence : 0 <
    quittingTerminalOpponentIncidenceMass resetOwner other
      (quittingTerminalOutcomeMass reward
        (source.finitePrefixSource port horizon).profile)
  returned : QuittingTerminalSemanticPair ι
  dispatch : QuittingFixedLawResetDispatch (reward := reward)
    source.minimum
    (quittingTerminalSemanticPair reward
      (source.finitePrefixSource port horizon).profile)
    (quittingTerminalOutcomeMass reward
      (source.finitePrefixSource port horizon).profile)
    resetOwner other returned

/-- The real-valued descent arm has an actual finite paid/reset descendant;
no limiting carrier point is used as a surrogate behavioral source. -/
theorem QuantitativeDebtDescent.nonempty_finitePaidResetRegeneration
    (source : QuittingPaidCapLiftedSource reward)
    (port : source.SummablePort)
    (descent : source.QuantitativeDebtDescent port)
    (witness : QuittingTerminalExploitabilityWitness reward)
    (resetOwner other : ι)
    (hreset : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward source.profile) resetOwner = 0)
    (hincidence : 0 < quittingTerminalOpponentIncidenceMass resetOwner other
      (quittingTerminalOutcomeMass reward source.profile)) :
    Nonempty (source.FinitePaidResetRegeneration port resetOwner other) := by
  have hdebt : Tendsto (fun horizon ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)))
      atTop
      (nhds (quittingTerminalSemanticDebtSum port.semanticPort.limit)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      port.semanticPort.semantic_tendsto
  have hlimitLt :
      quittingTerminalSemanticDebtSum port.semanticPort.limit <
        source.initialDebt := by
    linarith [descent.debtDrop_pos]
  have heventually : ∀ᶠ horizon in atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingCapLiftedPrefixProfile reward source.profile horizon)) <
        source.initialDebt :=
    hdebt.eventually_lt_const hlimitLt
  obtain ⟨horizon, hstrict⟩ := heventually.exists
  have hresetAntitone := source.debt_antitone resetOwner
  have hresetLe :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingCapLiftedPrefixProfile reward source.profile horizon))
          resetOwner ≤ 0 := by
    have hstep := hresetAntitone (Nat.zero_le horizon)
    simpa [hreset] using hstep
  have hresetNonneg : 0 ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon))
        resetOwner := by
    simpa [quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
      quittingTerminalDeviationDebt] using
      (quittingTerminalDeviationDebt_nonneg reward
        (quittingCapLiftedPrefixProfile reward source.profile horizon)
        resetOwner)
  have hresetHorizon :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingCapLiftedPrefixProfile reward source.profile horizon))
          resetOwner = 0 :=
    le_antisymm hresetLe hresetNonneg
  have hreachPos : 0 <
      quittingCapLiftedSuffixReach reward source.profile horizon :=
    source.reachFloor_pos.trans_le (source.reachFloor_le_suffixReach horizon)
  have hincidenceLower :=
    quittingCapLiftedSuffixReach_mul_opponentIncidence_le reward source.profile
      resetOwner other horizon
  have hincidenceHorizon : 0 <
      quittingTerminalOpponentIncidenceMass resetOwner other
        (quittingTerminalOutcomeMass reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)) :=
    (mul_pos hreachPos hincidence).trans_le hincidenceLower
  have hjoint := quittingTerminalSemanticLawPoint_mem_carrier reward
    (quittingCapLiftedPrefixProfile reward source.profile horizon)
  obtain ⟨returned, dispatch⟩ := witness.exists_fixedLawResetDispatch
    source.minimum
    (quittingTerminalSemanticPair reward
      (quittingCapLiftedPrefixProfile reward source.profile horizon))
    (quittingTerminalOutcomeMass reward
      (quittingCapLiftedPrefixProfile reward source.profile horizon))
    resetOwner other source.minimum_le source.minimum_pos hjoint
    hresetHorizon hincidenceHorizon
  exact ⟨{
    horizon := horizon
    strict_debt := by
      simpa [QuittingPaidCapLiftedSource.initialDebt] using hstrict
    target_joint := by simpa using hjoint
    reset_debt := by simpa using hresetHorizon
    reset_incidence := by simpa using hincidenceHorizon
    returned := returned
    dispatch := by simpa using dispatch }⟩

end QuittingPaidCapLiftedSource

/-- Source-specific specialization: a strict debt descent on the original
singleton paid/reset port regenerates a finite actual paid/reset source. -/
theorem FinFourSingletonBaseResetRepairPaidCapDoublePort.nonempty_sourcePaidResetRegeneration
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
    {owner : Fin 4}
    (double : FinFourSingletonBaseResetRepairPaidCapDoublePort reward bound
      residual owner)
    (descent : QuittingPaidCapLiftedSource.QuantitativeDebtDescent
      double.chain.sourceCapLiftedSource double.sourcePort) :
    Nonempty
      (double.chain.sourceCapLiftedSource.FinitePaidResetRegeneration
        double.sourcePort double.chain.producer.resetOwner owner) := by
  have hresetMem : double.chain.producer.resetOwner ∈
      finFourSingletonBaseFree owner := by
    simp [finFourSingletonBaseFree,
      double.chain.producer.resetOwner_ne_owner]
  have hreset : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        double.chain.sourceCapLiftedSource.profile)
      double.chain.producer.resetOwner = 0 := by
    rw [double.chain.sourceCapLiftedSource_profile]
    exact (double.chain.producer.free_solved
      double.chain.producer.resetOwner hresetMem).1
  have hincidence : 0 <
      quittingTerminalOpponentIncidenceMass
        double.chain.producer.resetOwner owner
        (quittingTerminalOutcomeMass reward
          double.chain.sourceCapLiftedSource.profile) := by
    rw [double.chain.sourceCapLiftedSource_profile,
      double.chain.producer.reset_incidence]
    norm_num
  exact QuittingPaidCapLiftedSource.QuantitativeDebtDescent.nonempty_finitePaidResetRegeneration
      double.chain.sourceCapLiftedSource double.sourcePort descent
      residual.witness double.chain.producer.resetOwner owner hreset hincidence

namespace FinFourSingletonBaseResetRepairPaidCapDoublePort

/-- The source-side paid-cap trichotomy with its descent arm consumed into an
actual finite paid/reset regeneration.  The sole remaining branch is the
literal inert stall on that same source and port. -/
theorem sourcePaidResetRegeneration_or_inert
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
    {owner : Fin 4}
    (double : FinFourSingletonBaseResetRepairPaidCapDoublePort reward bound
      residual owner) :
    Nonempty
        (double.chain.sourceCapLiftedSource.FinitePaidResetRegeneration
          double.sourcePort double.chain.producer.resetOwner owner) ∨
      QuittingPaidCapLiftedSource.InertStall
        double.chain.sourceCapLiftedSource double.sourcePort := by
  rcases double.chain.sourceCapLiftedSource
      |>.chargedNearReturn_or_quantitativeDebtDescent_or_inertStall
        double.sourcePort with charged | descent | inert
  · exact (residual.witness.not_exists_uniformEquilibriumPayoff
      charged.uniformEquilibriumPayoff).elim
  · exact Or.inl (double.nonempty_sourcePaidResetRegeneration descent)
  · exact Or.inr inert

end FinFourSingletonBaseResetRepairPaidCapDoublePort

/-- Direct hard-residual packet whose descent branch has actual paid/reset
provenance.  This is not yet a well-founded iteration: the remaining inert
stall is retained literally. -/
structure FinFourPaidResetDescentOrInertBoundary
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (owner : Fin 4) where
  double : FinFourSingletonBaseResetRepairPaidCapDoublePort reward bound
    residual owner
  outcome :
    Nonempty
        (double.chain.sourceCapLiftedSource.FinitePaidResetRegeneration
          double.sourcePort double.chain.producer.resetOwner owner) ∨
      QuittingPaidCapLiftedSource.InertStall
        double.chain.sourceCapLiftedSource double.sourcePort

/-- Every bounded quantitative hard residual and every prescribed singleton
owner reach the paid/reset regeneration-or-literal-inert boundary. -/
theorem FinFourQuantitativeFullSupportHardResidual.nonempty_paidResetDescentOrInertBoundary
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (owner : Fin 4) :
    Nonempty (FinFourPaidResetDescentOrInertBoundary reward bound residual
      owner) := by
  obtain ⟨double⟩ := residual.nonempty_paidCapDoublePort hreward owner
  exact ⟨{
    double := double
    outcome := double.sourcePaidResetRegeneration_or_inert }⟩

end GameTheory
