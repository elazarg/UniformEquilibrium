/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.SingletonBaseResetRepairPaidChain
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidCapPortExactTrichotomy

/-!
# Double paid cap port at a singleton source and its owner repair

The same-point singleton packet has a full-gap paid row on two actual profiles:
the original sure-Quit source and its literal owner repair.  Both rows can be
lifted from the same positive global semantic-debt minimum.  The exact cap-port
trichotomy applies independently to the two resulting ports.

The charged near-return branch is impossible on either port because the hard
residual retains a terminal exploitability witness, while that branch already
constructs a uniform-equilibrium payoff.  Hence at least one port has a strict
quantitative debt descent, or both ports are literally inert.

This does not make the descent recursive.  Neither limiting semantic pair is
equipped with a paid row, reset law, behavior-profile representative, or a
connector to the other profile.  In the double-inert branch, the two finite
prefix sequences are separately stationary in terminal semantics; their laws
are not identified with each other.
-/

noncomputable section

namespace GameTheory

open Finset

namespace FinFourSingletonBaseResetRepairPaidChain

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}
  {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
  {owner : Fin 4}

/-- The original paid/reset source lifted from the packet's positive global
minimum. -/
noncomputable def sourceCapLiftedSource
    (chain : FinFourSingletonBaseResetRepairPaidChain reward bound residual
      owner) : QuittingPaidCapLiftedSource reward where
  minimum := chain.producer.minimum
  minimum_le := chain.producer.minimum_global
  minimum_pos := chain.producer.minimum_positive
  profile := finFourSingletonBaseProfile reward owner chain.producer.point
  observer := owner
  gain := residual.witness.terminalGap
  gain_pos := residual.witness.terminalGap_pos
  row := Classical.choice chain.producer.paid_row

/-- The paid source obtained after the literal owner repair, using the same
positive global minimum. -/
noncomputable def repairedCapLiftedSource
    (chain : FinFourSingletonBaseResetRepairPaidChain reward bound residual
      owner) : QuittingPaidCapLiftedSource reward where
  minimum := chain.producer.minimum
  minimum_le := chain.producer.minimum_global
  minimum_pos := chain.producer.minimum_positive
  profile := quittingSingletonBaseRepairedProfile reward owner
    (finFourSingletonBaseFree owner) chain.producer.point
  observer := chain.repair.outsideDebtor
  gain := residual.witness.terminalGap
  gain_pos := residual.witness.terminalGap_pos
  row := Classical.choice chain.repair.paid_row

@[simp] theorem sourceCapLiftedSource_profile
    (chain : FinFourSingletonBaseResetRepairPaidChain reward bound residual
      owner) :
    chain.sourceCapLiftedSource.profile =
      finFourSingletonBaseProfile reward owner chain.producer.point := rfl

@[simp] theorem repairedCapLiftedSource_profile
    (chain : FinFourSingletonBaseResetRepairPaidChain reward bound residual
      owner) :
    chain.repairedCapLiftedSource.profile =
      quittingSingletonBaseRepairedProfile reward owner
        (finFourSingletonBaseFree owner) chain.producer.point := rfl

@[simp] theorem sourceCapLiftedSource_observer
    (chain : FinFourSingletonBaseResetRepairPaidChain reward bound residual
      owner) :
    chain.sourceCapLiftedSource.observer = owner := rfl

@[simp] theorem repairedCapLiftedSource_observer
    (chain : FinFourSingletonBaseResetRepairPaidChain reward bound residual
      owner) :
    chain.repairedCapLiftedSource.observer =
      chain.repair.outsideDebtor := rfl

/-- The two cap lifts keep distinct paid observers. -/
theorem capLiftedSource_observers_ne
    (chain : FinFourSingletonBaseResetRepairPaidChain reward bound residual
      owner) :
    chain.sourceCapLiftedSource.observer ≠
      chain.repairedCapLiftedSource.observer := by
  simpa using chain.repair.outsideDebtor_ne_owner.symm

end FinFourSingletonBaseResetRepairPaidChain

/-- Both actual paid profiles, together with independently selected summable
cap ports.  The original reset dispatch remains available through `chain` and
is not transported to the repaired source. -/
structure FinFourSingletonBaseResetRepairPaidCapDoublePort
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (owner : Fin 4) where
  chain : FinFourSingletonBaseResetRepairPaidChain reward bound residual owner
  sourcePort : QuittingPaidCapLiftedSource.SummablePort
    chain.sourceCapLiftedSource
  repairedPort : QuittingPaidCapLiftedSource.SummablePort
    chain.repairedCapLiftedSource

namespace FinFourSingletonBaseResetRepairPaidCapDoublePort

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}
  {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
  {owner : Fin 4}

/-- Any frozen same-point paid/reset/repair chain has two summable paid cap
ports. -/
theorem nonempty_of_chain
    (chain : FinFourSingletonBaseResetRepairPaidChain reward bound residual
      owner) :
    Nonempty (FinFourSingletonBaseResetRepairPaidCapDoublePort reward bound
      residual owner) := by
  obtain ⟨sourcePort⟩ := chain.sourceCapLiftedSource.nonempty_summablePort
  obtain ⟨repairedPort⟩ :=
    chain.repairedCapLiftedSource.nonempty_summablePort
  exact ⟨{
    chain := chain
    sourcePort := sourcePort
    repairedPort := repairedPort }⟩

private theorem not_charged_source
    (double : FinFourSingletonBaseResetRepairPaidCapDoublePort reward bound
      residual owner) :
    ¬QuittingPaidCapLiftedSource.ChargedNearReturn
      double.chain.sourceCapLiftedSource double.sourcePort := by
  intro charged
  exact residual.witness.not_exists_uniformEquilibriumPayoff
    charged.uniformEquilibriumPayoff

private theorem not_charged_repaired
    (double : FinFourSingletonBaseResetRepairPaidCapDoublePort reward bound
      residual owner) :
    ¬QuittingPaidCapLiftedSource.ChargedNearReturn
      double.chain.repairedCapLiftedSource double.repairedPort := by
  intro charged
  exact residual.witness.not_exists_uniformEquilibriumPayoff
    charged.uniformEquilibriumPayoff

/-- **Double-port contraction.**  A counterexample source has a quantitative
debt descent on the original paid/reset profile, a quantitative debt descent
on its literal owner repair, or literal inert stalls on both cap lifts. -/
theorem sourceDescent_or_repairedDescent_or_doubleInert
    (double : FinFourSingletonBaseResetRepairPaidCapDoublePort reward bound
      residual owner) :
    QuittingPaidCapLiftedSource.QuantitativeDebtDescent
        double.chain.sourceCapLiftedSource double.sourcePort ∨
      QuittingPaidCapLiftedSource.QuantitativeDebtDescent
          double.chain.repairedCapLiftedSource double.repairedPort ∨
        (QuittingPaidCapLiftedSource.InertStall
            double.chain.sourceCapLiftedSource double.sourcePort ∧
          QuittingPaidCapLiftedSource.InertStall
            double.chain.repairedCapLiftedSource double.repairedPort) := by
  rcases double.chain.sourceCapLiftedSource
      |>.chargedNearReturn_or_quantitativeDebtDescent_or_inertStall
        double.sourcePort with charged | descent | inert
  · exact (double.not_charged_source charged).elim
  · exact Or.inl descent
  · rcases double.chain.repairedCapLiftedSource
        |>.chargedNearReturn_or_quantitativeDebtDescent_or_inertStall
          double.repairedPort with charged | descent | repairedInert
    · exact (double.not_charged_repaired charged).elim
    · exact Or.inr (Or.inl descent)
    · exact Or.inr (Or.inr ⟨inert, repairedInert⟩)

end FinFourSingletonBaseResetRepairPaidCapDoublePort

/-- Every same-point singleton producer extends to the contracted double cap
port. -/
theorem FinFourSingletonBaseSameLawResetProducer.nonempty_paidCapDoublePort
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
    {owner : Fin 4}
    (producer : FinFourSingletonBaseSameLawResetProducer reward bound residual
      owner) :
    Nonempty (FinFourSingletonBaseResetRepairPaidCapDoublePort reward bound
      residual owner) := by
  obtain ⟨chain⟩ := producer.nonempty_resetRepairPaidChain
  exact FinFourSingletonBaseResetRepairPaidCapDoublePort.nonempty_of_chain chain

/-- Direct actual-residual capstone: a bounded quantitative hard residual and
any prescribed singleton owner produce the contracted double paid cap port. -/
theorem FinFourQuantitativeFullSupportHardResidual.nonempty_paidCapDoublePort
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (owner : Fin 4) :
    Nonempty (FinFourSingletonBaseResetRepairPaidCapDoublePort reward bound
      residual owner) := by
  obtain ⟨producer⟩ := residual.nonempty_singletonBaseSameLawResetProducer
    hreward owner
  exact producer.nonempty_paidCapDoublePort

end GameTheory
