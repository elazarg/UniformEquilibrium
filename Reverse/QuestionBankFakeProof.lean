/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.PaidFirstDisagreementPayoffNearReturn
import UniformEquilibrium.Diagnostics.Quitting.UniformExistenceBoundary
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.SuppliedCorrespondence
import UniformEquilibrium.Quitting.Debt.Dynamic.NashBellmanChronologicalForcing
import UniformEquilibrium.Quitting.Paths.PersistentTwoLabelCounterexample

/-!
# Fake proof that the active question bank is conjecture-closing

This file exists only on the `fake-proof` branch.  Every declaration whose
name starts with `fakeAnswer` is an assumed mathematical answer implemented
with `sorry`.  The downstream theorems contain no additional gap: they apply
the checked production consumers to show exactly which answers imply uniform
existence and which answers instead provide a quitting-game counterexample.
The formerly listed universal persistent-two-label answer is now proved false
and is retained only through its valid per-spine conditional consumer.

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

/-! ## Conditioned packet reprojection -/

/-- Fake positive answer at the exact checked consumer waist. -/
theorem fakeAnswer_conditionedPacketReprojection
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    VanishingDebtAtomChronologicalConsumer reward := by
  sorry

/-- The conditioned-reprojection answer alone closes finite-quitting uniform
existence through the universal vanishing-debt atom access. -/
theorem fake_conditionedPacketReprojection_proves_uniformExistence :
    FiniteQuittingUniformExistence := by
  intro ι _ _ _ reward
  exact exists_uniformEquilibriumPayoff_of_vanishingDebtAtomChronologicalConsumer
    (fakeAnswer_conditionedPacketReprojection reward)

/-! ## Persistent two-label hazards -/

/-- Exact bounded Nash--Bellman data whose same literal roots carry two
persistent marginal labels. -/
structure PersistentTwoLabelNashBellmanAnswer
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  value : ℕ → Payoff ι
  roots : ℕ → ι → PMF Bool
  value_bound : ∀ time who,
    |value time who| ≤ quittingRewardBound reward
  bellman : ∀ time,
    value time = quittingRootSuccessorPayoff reward
      (value (time + 1)) (roots time)
  nash : ∀ time,
    IsεQuittingRootNash reward (value (time + 1)) 0 (roots time)
  persistent : HasTwoPersistentQuittingMarginals roots

/-- The proposed universal two-label answer is false even after imposing the
necessary two-player cardinality bound. -/
theorem not_forall_persistentTwoLabelNashBellmanAnswer :
    ¬ (∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      2 ≤ Fintype.card ι →
      ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
        Nonempty (PersistentTwoLabelNashBellmanAnswer reward)) := by
  intro hall
  apply not_exists_persistentTwoLabelExactNashBellmanSpine
  obtain ⟨answer⟩ := hall Bool (by decide)
    persistentTwoLabelCounterexampleReward
  exact ⟨answer.value, answer.roots, answer.bellman, answer.nash,
    answer.persistent⟩

/-- Persistent labels on one supplied exact spine still provide every-
accuracy chronological certificates and therefore a uniform-equilibrium
payoff for that game. -/
theorem PersistentTwoLabelNashBellmanAnswer.exists_uniformEquilibriumPayoff
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (answer : PersistentTwoLabelNashBellmanAnswer reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨first, second, hne, _, _⟩ := answer.persistent
  have hcard : 2 ≤ Fintype.card ι :=
    Fintype.one_lt_card_iff.mpr ⟨first, second, hne⟩
  obtain ⟨hopponent, hjoint⟩ :=
    HasTwoPersistentQuittingMarginals.survival hcard answer.persistent
  apply
    quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
      reward
  intro eta heta
  exact nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine
    reward answer.value answer.roots answer.value_bound answer.bellman
      answer.nash hjoint hopponent eta heta

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
