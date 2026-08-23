/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.ActiveTransferCycle
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.PotentialCoDecreaseCurvature
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
the paid row into a positive exact admissible edge with an exact return.  The
checked consumers for those two concrete outputs already produce a uniform
payoff.  Neither missing producer is asserted here.
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
    {witness : QuittingTerminalExploitabilityWitness reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier witness) where
  mover : {who // who ∈ frontier.active}
  observer : ι
  charge : ℝ
  observer_ne_mover : observer ≠ mover.1
  charge_pos : 0 < charge
  atom_eventually : ∀ᶠ rank in atTop,
    HasQuittingStoppingLawVanishingDebtAtomAlternative reward
      (frontier.profiles (frontier.subseq rank)) mover.1 observer
      (frontier.bestResponse mover (frontier.subseq rank)) charge
      (quittingStoppingLawAtomDecoderError charge rank)

/-- Every extracted frontier has fixed vanishing-debt atom access.  This uses
only the exact negative diagonal, nonnegative total slope, and a positive
off-diagonal coordinate; it is independent of the four finite-rank exit tags.
-/
theorem QuittingCounterexampleStoppingLawFrontier.nonempty_vanishingDebtAtomAccess
    {witness : QuittingTerminalExploitabilityWitness reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier witness) :
    Nonempty (QuittingVanishingDebtAtomAccess frontier) := by
  obtain ⟨who, hwho⟩ := frontier.active_nonempty
  let mover : {who // who ∈ frontier.active} := ⟨who, hwho⟩
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
theorem QuittingCounterexampleStoppingLawFrontier.exists_vanishingDebtAtomAccess_of_supportEntry
    {witness : QuittingTerminalExploitabilityWitness reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (hentry : HasQuittingStoppingLawFlatSupportEntry
      frontier.base frontier.active frontier.tangent) :
    ∃ access : QuittingVanishingDebtAtomAccess frontier,
      quittingTerminalSemanticDebt frontier.base access.observer = 0 := by
  change ∃ mover ∈ frontier.active, ∃ recipient,
    quittingTerminalSemanticDebt frontier.base recipient = 0 ∧
      0 < quittingActiveDebtTangentExtension frontier.active frontier.tangent
        mover recipient at hentry
  obtain ⟨who, hwho, observer, hzero, hpositive⟩ := hentry
  let mover : {who // who ∈ frontier.active} := ⟨who, hwho⟩
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
  have hactiveDebt := (frontier.active_iff who).1 hwho
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
  ∀ (witness : QuittingTerminalExploitabilityWitness reward)
      (frontier : QuittingCounterexampleStoppingLawFrontier witness),
    QuittingVanishingDebtAtomAccess frontier →
      ∀ eta : ℝ, 0 < eta →
        Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta)

/-- The precise missing return producer for the paid-row arm of finite
support-rank termination. -/
def PaidFirstDisagreementAdmissibleReturnConsumer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (witness : QuittingTerminalExploitabilityWitness reward)
      (frontier : QuittingCounterexampleStoppingLawFrontier witness)
      (mover : {who // who ∈ frontier.active})
      (endpoint :
        QuittingCounterexampleStoppingLawFrontier.FullResetEndpointCluster
          frontier mover),
    quittingTerminalSemanticDebtSum frontier.base <
        quittingTerminalSemanticDebtSum endpoint.cluster →
      ∀ observer gain, observer ≠ mover.1 → 0 < gain →
        (∀ᶠ rank in atTop,
          Nonempty (QuittingPaidFirstDisagreementRow reward
            (frontier.fullResetProfile mover (endpoint.subseq rank))
            observer gain)) →
        Nonempty (QuittingPositiveAdmissibleReturn reward)

/-- Positive minimum semantic debt reaches the checked finite support-rank
exit.  This is a one-way reduction, not an equivalence between the minimum and
the four exit tags. -/
theorem hasFiniteSupportRankExit_of_hasPositiveMinimumTerminalSemanticDebt
    [Nonempty ι] (hpositive : HasPositiveMinimumTerminalSemanticDebt reward) :
    ∃ witness : QuittingTerminalExploitabilityWitness reward,
      QuittingCounterexampleStoppingLawFrontier.HasQuittingStoppingLawFiniteSupportRankExit
        witness := by
  have hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
    (not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
      reward).2 hpositive
  let witness := quittingTerminalExploitabilityWitnessOfNoUniformPayoff reward hno
  obtain ⟨frontier⟩ := witness.exists_stoppingLaw_exhaustiveFrontier
  exact ⟨witness, frontier.exists_finiteSupportRankExit⟩

/-- **Strong conditional capstone.**  Since every extracted frontier already
has static vanishing-debt atom access, a chronological producer for that
interface alone rules out every terminal exploitability witness. -/
theorem exists_uniformEquilibriumPayoff_of_vanishingDebtAtomChronologicalConsumer
    [Nonempty ι]
    (hconsumer : VanishingDebtAtomChronologicalConsumer reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  let witness := quittingTerminalExploitabilityWitnessOfNoUniformPayoff reward hno
  obtain ⟨frontier⟩ := witness.exists_stoppingLaw_exhaustiveFrontier
  obtain ⟨access⟩ := frontier.nonempty_vanishingDebtAtomAccess
  exact hno
    (quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
      reward (hconsumer witness frontier access))

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

/-- **Four-exit conditional capstone.**  The first three finite-rank exits may
be consumed by chronological shadowing, while the paid-row exit may instead
be consumed by an exact positive admissible return. -/
theorem exists_uniformEquilibriumPayoff_of_finiteSupportRankExitConsumers
    [Nonempty ι]
    (hpositiveSlope :
      ∀ (witness : QuittingTerminalExploitabilityWitness reward)
        (frontier : QuittingCounterexampleStoppingLawFrontier witness),
        (∃ mover, 0 < ∑ observer, frontier.tangent mover observer) →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hsupportEntry :
      ∀ (witness : QuittingTerminalExploitabilityWitness reward)
        (frontier : QuittingCounterexampleStoppingLawFrontier witness),
        HasQuittingStoppingLawFlatSupportEntry
          frontier.base frontier.active frontier.tangent →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hcirculation :
      ∀ (witness : QuittingTerminalExploitabilityWitness reward)
        (frontier : QuittingCounterexampleStoppingLawFrontier witness),
        HasQuittingStoppingLawFlatChargedCirculation
          frontier.active frontier.tangent →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hpaid : PaidFirstDisagreementAdmissibleReturnConsumer reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  let witness := quittingTerminalExploitabilityWitnessOfNoUniformPayoff reward hno
  obtain ⟨first⟩ := witness.exists_stoppingLaw_exhaustiveFrontier
  obtain ⟨frontier, hpositive | hentry | hcirculationExit | hpaidExit⟩ :=
    first.exists_finiteSupportRankExit
  · exact hno
      (quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
        reward (hpositiveSlope witness frontier hpositive))
  · exact hno
      (quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
        reward (hsupportEntry witness frontier hentry.2))
  · exact hno
      (quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
        reward (hcirculation witness frontier hcirculationExit.2.2))
  · obtain ⟨mover, endpoint, hseparated, observer, gain, hobserver, hgain,
        hrows⟩ := hpaidExit
    obtain ⟨result⟩ := hpaid witness frontier mover endpoint hseparated
      observer gain hobserver hgain hrows
    exact hno result.exists_uniformEquilibriumPayoff

end GameTheory
