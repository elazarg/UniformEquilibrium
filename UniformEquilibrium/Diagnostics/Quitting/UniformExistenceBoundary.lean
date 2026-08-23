/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.NormalizedCurvaturePaidRow
import UniformEquilibrium.Quitting.Bellman.Finite.PositiveAdmissibleCycle
import UniformEquilibrium.Quitting.Debt.Dynamic.ChronologicalDebtShadowing

/-!
# Uniform-existence boundary for finite quitting games

This module records the checked end of the positive-minimum semantic-debt
reduction without identifying independent static and chronological facts.

Every positive minimum produces a terminal exploitability witness and a stopping-law
frontier.  Exact diagonal extraction and finite support-rank descent then end
in positive total slope, zero-debt support entry, flat charged circulation, or
an eventually available paid first-disagreement row.  Independently of those
four tags, every extracted frontier has a fixed positive off-diagonal tangent
coordinate and therefore an eventually available vanishing-debt atom
alternative.  In the support-entry branch, the atom can use the actual
zero-debt recipient from the entry witness.

The remaining implications are producer statements.  One may turn static
vanishing-debt atoms into chronological debt-shadowing certificates, or turn
the paid row into a fixed positive charge threshold and, at every accuracy, a
possibly varying admissible path containing an edge above that threshold whose
endpoint payoff vectors are close.  Fixed-edge payoff closure and exact return
to the full tail state are stronger special cases.  The checked consumers for
those two concrete outputs already produce a uniform payoff.  Neither missing
producer is asserted here.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Fixed vanishing-debt atom data along one extracted stopping-law frontier.
This is static source-profile data, not an executable chronology. -/
structure QuittingVanishingDebtAtomAccess
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward) where
  mover : {who // who ∈ frontier.positiveDebtSupport}
  observer : ι
  charge : ℝ
  observer_ne_mover : observer ≠ mover.1
  charge_pos : 0 < charge
  atom_eventually : ∀ᶠ rank in atTop,
    HasQuittingStoppingLawVanishingDebtAtomAlternative reward
      (frontier.source rank) mover.1 observer
      (frontier.replacement mover rank) charge
      (quittingStoppingLawAtomDecoderError charge rank)

/-- Every extracted frontier has fixed vanishing-debt atom access.  This uses
only the exact negative diagonal, nonnegative total slope, and a positive
off-diagonal coordinate; it is independent of the four finite-rank exit tags.
-/
theorem QuittingPositiveMinimumDebtTangentFamily.nonempty_vanishingDebtAtomAccess
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward) :
    Nonempty (QuittingVanishingDebtAtomAccess frontier) := by
  obtain ⟨who, hwho⟩ := frontier.positiveDebtSupport_nonempty
  let mover : {who // who ∈ frontier.positiveDebtSupport} := ⟨who, hwho⟩
  obtain ⟨observer, charge, hobserver, _hlower, _hchargeEq, hcharge, hatom⟩ :=
    frontier.exists_quantitativeStrongVanishingDebtAtomAlternative_of_mover mover
  exact ⟨{
    mover := mover
    observer := observer
    charge := charge
    observer_ne_mover := hobserver
    charge_pos := hcharge
    atom_eventually := hatom }⟩

/-- Support entry has a stronger adapter: the atom observer may be the same
zero-debt recipient carried by the entry witness. -/
theorem QuittingPositiveMinimumDebtTangentFamily.exists_vanishingDebtAtomAccess_of_supportEntry
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (hentry : HasQuittingStoppingLawFlatSupportEntry
      frontier.base frontier.positiveDebtSupport frontier.tangent) :
    ∃ access : QuittingVanishingDebtAtomAccess frontier,
      quittingTerminalSemanticDebt frontier.base access.observer = 0 := by
  change ∃ mover ∈ frontier.positiveDebtSupport, ∃ recipient,
    quittingTerminalSemanticDebt frontier.base recipient = 0 ∧
      0 < quittingActiveDebtTangentExtension frontier.positiveDebtSupport frontier.tangent
        mover recipient at hentry
  obtain ⟨who, hwho, observer, hzero, hpositive⟩ := hentry
  let mover : {who // who ∈ frontier.positiveDebtSupport} := ⟨who, hwho⟩
  have htangent : 0 < frontier.tangent mover observer := by
    simpa only [quittingActiveDebtTangentExtension, hwho, dite_true] using hpositive
  obtain ⟨charge, _hchargeEq, hcharge, hatom⟩ :=
    frontier.exists_fixedStrongVanishingDebtAtomAlternative_of_positiveOffDiagonal
      mover observer htangent
  refine ⟨{
    mover := mover
    observer := observer
    charge := charge
    observer_ne_mover := ?_
    charge_pos := hcharge
    atom_eventually := hatom }, hzero⟩
  intro heq
  subst observer
  have hactiveDebt := (frontier.positiveDebtSupport_iff who).1 hwho
  linarith

/-- A positive exact edge together with an exact admissible return.  This is
the concrete input consumed by positive admissible-cycle amplification. -/
structure QuittingPositiveAdmissibleReturn
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  edge : QuittingPunishmentFloorAdmissibleEdge reward
  returnPath :
    (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      edge.current edge.tail
  charge_pos : 0 < edge.toBoxEdge.absorptionCharge

/-- The checked admissible-return consumer. -/
theorem QuittingPositiveAdmissibleReturn.exists_uniformEquilibriumPayoff
    (result : QuittingPositiveAdmissibleReturn reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformPayoff_of_positive_admissible_return
    result.edge result.returnPath result.charge_pos

/-- The precise missing chronological producer for the universal static atom
access above. -/
def VanishingDebtAtomChronologicalConsumer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward),
    QuittingVanishingDebtAtomAccess frontier →
      ∀ eta : ℝ, 0 < eta →
        Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta)

/-- The precise missing return producer for the paid-row arm of finite
support-rank termination. -/
def PaidFirstDisagreementAdmissibleReturnConsumer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
      (mover : {who // who ∈ frontier.positiveDebtSupport})
      (endpoint :
        QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster
          frontier mover),
    quittingTerminalSemanticDebtSum frontier.base <
        quittingTerminalSemanticDebtSum endpoint.cluster →
      ∀ observer gain, observer ≠ mover.1 → 0 < gain →
        (∀ᶠ rank in atTop,
          Nonempty (QuittingPaidFirstDisagreementRow reward
            (frontier.fullReplacementProfile mover (endpoint.subseq rank))
            observer gain)) →
        Nonempty (QuittingPositiveAdmissibleReturn reward)

/-- Source-matched paid-row consumer with the weakest downstream output used
by the four-exit argument: an unrestricted uniform-equilibrium payoff.  More
concrete paid-row consumers can factor through this interface without
duplicating the finite support-rank case split. -/
def PaidFirstDisagreementUniformPayoffConsumer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
      (mover : {who // who ∈ frontier.positiveDebtSupport})
      (endpoint :
        QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster
          frontier mover),
    quittingTerminalSemanticDebtSum frontier.base <
        quittingTerminalSemanticDebtSum endpoint.cluster →
      ∀ observer gain, observer ≠ mover.1 → 0 < gain →
        (∀ᶠ rank in atTop,
          Nonempty (QuittingPaidFirstDisagreementRow reward
            (frontier.fullReplacementProfile mover (endpoint.subseq rank))
            observer gain)) →
        ∃ payoff : Payoff ι,
          (quittingGame reward).IsUniformEquilibriumPayoff none payoff

/-- Positive minimum semantic debt reaches the checked finite support-rank
alternative.  This is a one-way reduction, not an equivalence between the
minimum and the four tags. -/
theorem finiteSupportRankAlternative_of_hasPositiveMinimumTerminalSemanticDebt
    (hpositive : HasPositiveMinimumTerminalSemanticDebt reward) :
    QuittingPositiveMinimumDebtTangentFamily.HasQuittingStoppingLawFiniteSupportRankAlternative
      reward :=
  QuittingPositiveMinimumDebtTangentFamily.finiteSupportRankAlternative_of_positiveMinimumDebt
    hpositive

/-- **Strong conditional capstone.**  Since every extracted frontier already
has static vanishing-debt atom access, a chronological producer for that
interface alone rules out every terminal exploitability witness. -/
theorem exists_uniformEquilibriumPayoff_of_vanishingDebtAtomChronologicalConsumer
    [Nonempty ι]
    (hconsumer : VanishingDebtAtomChronologicalConsumer reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  have hpositive :=
    (not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
      reward).1 hno
  let frontier := (nonempty_positiveMinimumDebtTangentFamily hpositive).some
  obtain ⟨access⟩ := frontier.nonempty_vanishingDebtAtomAccess
  exact hno
    (quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
      reward (hconsumer frontier access))

/-- Consequently the chronological atom consumer makes a positive minimum
semantic debt impossible. -/
theorem not_hasPositiveMinimumTerminalSemanticDebt_of_vanishingDebtAtomChronologicalConsumer
    [Nonempty ι]
    (hconsumer : VanishingDebtAtomChronologicalConsumer reward) :
    ¬ HasPositiveMinimumTerminalSemanticDebt reward := by
  intro hpositive
  have hno :=
    (not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
      reward).2 hpositive
  exact hno
    (exists_uniformEquilibriumPayoff_of_vanishingDebtAtomChronologicalConsumer
      hconsumer)

/-- **Generic four-exit conditional capstone.**  The first three finite-rank
exits are consumed by chronological shadowing.  The paid-row consumer keeps
the exact source telescope but may discharge it by any proof of an unrestricted
uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_finiteSupportRankExitUniformPayoffConsumers
    [Nonempty ι]
    (hpositiveSlope :
      ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward),
        (∃ mover, 0 < ∑ observer, frontier.tangent mover observer) →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hsupportEntry :
      ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward),
        HasQuittingStoppingLawFlatSupportEntry
          frontier.base frontier.positiveDebtSupport frontier.tangent →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hcirculation :
      ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward),
        HasQuittingStoppingLawFlatChargedCirculation
          frontier.positiveDebtSupport frontier.tangent →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hpaid : PaidFirstDisagreementUniformPayoffConsumer reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  have hminimum :=
    (not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
      reward).1 hno
  let first := (nonempty_positiveMinimumDebtTangentFamily hminimum).some
  obtain ⟨frontier, hpositive | hentry | hcirculationExit | hpaidExit⟩ :=
    first.finiteSupportRankAlternative
  · exact hno
      (quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
        reward (hpositiveSlope frontier hpositive))
  · exact hno
      (quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
        reward (hsupportEntry frontier hentry.2))
  · exact hno
      (quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
        reward (hcirculation frontier hcirculationExit.2.2))
  · obtain ⟨mover, endpoint, hseparated, observer, gain, hobserver, hgain,
        hrows⟩ := hpaidExit
    exact hno (hpaid frontier mover endpoint hseparated
      observer gain hobserver hgain hrows)

/-- **Exact-return four-exit capstone.**  A positive admissible return is one
concrete way to consume the paid-row exit. -/
theorem exists_uniformEquilibriumPayoff_of_finiteSupportRankExitConsumers
    [Nonempty ι]
    (hpositiveSlope :
      ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward),
        (∃ mover, 0 < ∑ observer, frontier.tangent mover observer) →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hsupportEntry :
      ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward),
        HasQuittingStoppingLawFlatSupportEntry
          frontier.base frontier.positiveDebtSupport frontier.tangent →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hcirculation :
      ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward),
        HasQuittingStoppingLawFlatChargedCirculation
          frontier.positiveDebtSupport frontier.tangent →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hpaid : PaidFirstDisagreementAdmissibleReturnConsumer reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply
    exists_uniformEquilibriumPayoff_of_finiteSupportRankExitUniformPayoffConsumers
      hpositiveSlope hsupportEntry hcirculation
  intro frontier mover endpoint hseparated observer gain hobserver hgain hrows
  obtain ⟨result⟩ := hpaid frontier mover endpoint hseparated
    observer gain hobserver hgain hrows
  exact result.exists_uniformEquilibriumPayoff

end GameTheory
