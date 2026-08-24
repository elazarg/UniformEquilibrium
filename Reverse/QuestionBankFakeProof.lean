/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.PaidFirstDisagreementPayoffNearReturn
import UniformEquilibrium.Diagnostics.Quitting.UniformExistenceBoundary
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.SuppliedCorrespondence
import UniformEquilibrium.Quitting.Debt.Dynamic.NashBellmanChronologicalForcing

/-!
# Fake proof that the active question bank is conjecture-closing

This file exists only on the `fake-proof` branch.  Every declaration whose
name starts with `fakeAnswer` is an assumed mathematical answer implemented
with `sorry`.  The downstream theorems contain no additional gap: they apply
the checked production consumers to show exactly which answers imply uniform
existence and which answers instead provide a quitting-game counterexample.

Nothing in this file is evidence for any `M`, `L`, `A`, or `C` seal.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped BigOperators Topology

/-- The universal finite-quitting uniform-existence statement, restricted to
the nonempty finite player types used by the active question bank. -/
def FiniteQuittingUniformExistence : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (reward : {S : Finset ι // S.Nonempty} → Payoff ι),
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff

/-- A concrete player type carries a counterexample to uniform existence. -/
def HasFiniteQuittingUniformExistenceCounterexample
    (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  ∃ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
    ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff

/-! ## Conditioned packet reprojection and compatible iteration -/

/-- Fake answer to the composition of the two maintained packet questions.
The local reached-source reprojection question and the abstract compatible-
iteration question are deliberately distinct.  Only their universal
composition inhabits this conjecture-level consumer. -/
theorem fakeAnswer_conditionedPacketReprojection_and_compatibleIteration
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    VanishingDebtAtomChronologicalConsumer reward := by
  sorry

/-- Universal reached-source reprojection together with compatible iteration
closes finite-quitting uniform existence.  Neither maintained local question
alone is represented by the conjecture-level consumer above. -/
theorem fake_packetReprojection_and_iteration_prove_uniformExistence :
    FiniteQuittingUniformExistence := by
  intro ι _ _ _ reward
  exact exists_uniformEquilibriumPayoff_of_vanishingDebtAtomChronologicalConsumer
    (fakeAnswer_conditionedPacketReprojection_and_compatibleIteration reward)

/-! ## Paid admissible payoff near-return -/

/-- Fake positive answer to the paid first-disagreement output obligation. -/
theorem fakeAnswer_paidAdmissiblePayoffNearReturn
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer reward := by
  sorry

/-- The paid answer closes the final finite-rank branch once the other three
chronological branch producers are supplied.  This is the precise dependency;
the paid question alone does not manufacture those three producers. -/
theorem fake_paidAdmissiblePayoffNearReturn_closes_paidBranch
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
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
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact exists_uniformEquilibriumPayoff_of_finiteSupportRankExitPayoffNearReturnConsumers
    hpositiveSlope hsupportEntry hcirculation
      (fakeAnswer_paidAdmissiblePayoffNearReturn reward)

/-! ## Simon Lyapunov certificate -/

/-- The exact output requested by the Simon question, using one global
potential (equivalently, a one-cell certificate). -/
def SimonLyapunovQuestionAnswer
    (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] : Prop :=
  ∃ (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
      (epsilon rate lowerBound upperBound : ℝ)
      (potential : QuittingSimonFiniteOrbitCarrier reward epsilon → ℝ),
    SuppliedQuittingSimonFiniteOrbitNecessity reward ∧
    (¬QuittingStationarilyGeneratedApproximateEquilibria reward) ∧
    (¬QuittingInstantPunishmentεEquilibriumExistence reward) ∧
    0 < epsilon ∧ 0 < rate ∧
    (∀ state, lowerBound ≤ potential state) ∧
    (∀ state, potential state ≤ upperBound) ∧
    ∀ pair, pair ∈ QuittingSimonFiniteOrbitGraphAt reward epsilon →
      potential pair.2 ≤ potential pair.1 - rate *
        QuittingSimonFiniteOrbitCost pair.1 pair.2

/-- Fake concrete Simon answer on five players. -/
theorem fakeAnswer_simonLyapunovCertificate :
    Nonempty (SimonLyapunovQuestionAnswer (Fin 5)) := by
  sorry

/-- A positive Simon-certificate answer is conjecture-closing in the negative
direction: it yields a concrete finite quitting game with no uniform payoff. -/
theorem fake_simonLyapunovCertificate_refutes_uniformExistence :
    HasFiniteQuittingUniformExistenceCounterexample (Fin 5) := by
  obtain ⟨reward, epsilon, rate, lowerBound, upperBound, potential,
    necessity, generated, instant, epsilon_pos, rate_pos,
    lower_bound, upper_bound, decrease⟩ := fakeAnswer_simonLyapunovCertificate
  refine ⟨reward, ?_⟩
  exact not_exists_uniformEquilibriumPayoff_of_suppliedSimonNecessity
    reward necessity generated instant epsilon_pos potential rate_pos
      lower_bound upper_bound decrease

/-! ## Incentive gadget -/

/-- The exact semantic output demanded of a successful incentive gadget. -/
structure IncentiveGadgetQuestionAnswer
    (ι : Type) [Fintype ι] [DecidableEq ι] where
  reward : {S : Finset ι // S.Nonempty} → Payoff ι
  gap : ℝ
  gap_pos : 0 < gap
  exploitability : HasTerminalExploitabilityGap reward gap

/-- Fake six-player clock-gadget answer. -/
theorem fakeAnswer_incentiveGadget :
    Nonempty (IncentiveGadgetQuestionAnswer (Fin 6)) := by
  sorry

/-- The requested all-profile gadget gain is also conjecture-closing in the
negative direction. -/
theorem fake_incentiveGadget_refutes_uniformExistence :
    HasFiniteQuittingUniformExistenceCounterexample (Fin 6) := by
  obtain ⟨answer⟩ := fakeAnswer_incentiveGadget
  refine ⟨answer.reward, ?_⟩
  exact quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
    answer.reward answer.gap_pos answer.exploitability

end GameTheory
