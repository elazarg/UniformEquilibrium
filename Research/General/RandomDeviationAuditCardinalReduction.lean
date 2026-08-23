/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.General.RandomDeviationAuditGame
import UniformEquilibrium.Diagnostics.Quitting.MinimalFinCounterexample

/-!
# Cardinal reduction for the random deviation audit game

This module states the larger-to-four reduction without asserting it.
It separates three levels which are easy to conflate.

1. `CounterexampleCardinalReductionToFour` is the exact cardinal statement:
   if a finite quitting counterexample exists at any cardinality, then one
   exists on `Fin 4`.
2. `AuditCardinalReductionToFour` is the equivalent statement entirely in
   the fixed-table audit game: every positive finite audit value produces a
   positive four-player audit value.
3. `AllMinimalCounterexamplesHaveFourPlayers` is the equivalent
   minimal-counterexample form.
4. `UniformScoreReduction` is a usable sufficient certificate.  It translates
   every target Coordinator profile back to a source profile and proves a
   positive-factor score domination.  Consequently it transports positive
   audit value, rather than merely storing target positivity as a field.

The file proves all logical equivalences and value-transport consequences.
It does **not** construct the open reduction.  In particular, it does not
claim that a four-player restriction of a larger counterexample remains a
counterexample, that players can be merged, or that ignoring a debt coordinate
is the same operation as deleting a player.

The intended game-facing producer is
`EveryPositiveAuditHasOperationalFourReduction`.  Proving it would reduce the
full finite-player quitting conjecture to the four-player case.  A future
outsider-elimination theorem may instead prove the equivalent minimal form
directly.
-/

noncomputable section

namespace GameTheory
namespace RandomDeviationAudit
namespace CardinalReduction

open StochasticGame

/-! ## The exact open cardinal propositions -/

/-- A positive uniform-audit game exists on exactly four canonical players. -/
def HasPositiveFourPlayerAudit : Prop :=
  ∃ reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
    0 < value reward (Law.uniform : Law (Fin 4))

/-- The audit-language form of the larger-to-four conclusion for one supplied
source table.  This proposition asks only for existence of some four-player
positive-audit table; an operational producer is defined below. -/
def HasFourPlayerAuditCounterexample
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  0 < value reward (Law.uniform : Law ι) → HasPositiveFourPlayerAudit

/-- Exact canonical cardinal reduction: existence of a finite quitting
counterexample at any cardinality forces one at cardinality four. -/
def CounterexampleCardinalReductionToFour : Prop :=
  (∃ n, HasQuittingCounterexampleAtCard n) →
    HasQuittingCounterexampleAtCard 4

/-- Exact audit-language cardinal reduction: positive uniform audit value for
any finite nonempty quitting table forces positive uniform audit value for
some four-player table. -/
def AuditCardinalReductionToFour : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι),
    HasFourPlayerAuditCounterexample reward

/-- Every cardinal-minimal finite quitting counterexample has exactly four
players.  This is stronger than the landed lower bound only by the open upper
bound. -/
def AllMinimalCounterexamplesHaveFourPlayers : Prop :=
  ∀ minimal : MinimalFinQuittingCounterexample,
    minimal.playerCount = 4

/-! ## Audit and terminal exploitability witness dictionaries -/

/-- Positive uniform audit on `Fin 4` is exactly existence of the canonical
four-player terminal exploitability witness. -/
theorem hasPositiveFourPlayerAudit_iff_counterexampleAtCardFour :
    HasPositiveFourPlayerAudit ↔ HasQuittingCounterexampleAtCard 4 := by
  constructor
  · rintro ⟨reward, hpositive⟩
    have hno : ¬ ∃ payoff : Payoff (Fin 4),
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
      (uniform_value_pos_iff_no_uniformEquilibriumPayoff reward).mp hpositive
    exact ⟨reward,
      (not_exists_uniformEquilibriumPayoff_iff_nonempty_terminalExploitabilityWitness
        reward).mp hno⟩
  · rintro ⟨reward, hwitness⟩
    have hno : ¬ ∃ payoff : Payoff (Fin 4),
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
      (not_exists_uniformEquilibriumPayoff_iff_nonempty_terminalExploitabilityWitness
        reward).mpr hwitness
    exact ⟨reward,
      (uniform_value_pos_iff_no_uniformEquilibriumPayoff reward).mpr hno⟩

/-- The canonical cardinal reduction converts positive uniform audit for any
fixed finite source table into positive uniform audit on four players. -/
theorem hasPositiveFourPlayerAudit_of_cardinalReduction
    (hreduction : CounterexampleCardinalReductionToFour)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpositive : 0 < value reward (Law.uniform : Law ι)) :
    HasPositiveFourPlayerAudit := by
  have hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
    (uniform_value_pos_iff_no_uniformEquilibriumPayoff reward).mp hpositive
  have hwitness : Nonempty (QuittingTerminalExploitabilityWitness reward) :=
    (not_exists_uniformEquilibriumPayoff_iff_nonempty_terminalExploitabilityWitness
      reward).mp hno
  have hcanonical : Nonempty (QuittingTerminalExploitabilityWitness
      (quittingRewardReindex (Fintype.equivFin ι) reward)) :=
    (nonempty_terminalExploitabilityWitness_reindex_fin_iff reward).2 hwitness
  have hany : ∃ n, HasQuittingCounterexampleAtCard n :=
    ⟨Fintype.card ι, _, hcanonical⟩
  exact hasPositiveFourPlayerAudit_iff_counterexampleAtCardFour.mpr
    (hreduction hany)

/-- The canonical counterexample formulation implies the fixed-table audit
formulation. -/
theorem auditCardinalReductionToFour_of_counterexampleCardinalReduction
    (hreduction : CounterexampleCardinalReductionToFour) :
    AuditCardinalReductionToFour := by
  intro ι _ _ _ reward hpositive
  exact hasPositiveFourPlayerAudit_of_cardinalReduction
    hreduction reward hpositive

/-- The fixed-table audit formulation implies the canonical counterexample
formulation. -/
theorem counterexampleCardinalReductionToFour_of_auditCardinalReduction
    (hreduction : AuditCardinalReductionToFour) :
    CounterexampleCardinalReductionToFour := by
  rintro ⟨n, reward, hwitness⟩
  have hthree : 3 < n := by
    simpa using (Classical.choice hwitness).three_lt_card
  have hnpos : 0 < n := by omega
  letI : Nonempty (Fin n) := Fintype.card_pos_iff.mp (by simpa using hnpos)
  have hno : ¬ ∃ payoff : Payoff (Fin n),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
    (Classical.choice hwitness).not_exists_uniformEquilibriumPayoff
  have hpositive : 0 < value reward (Law.uniform : Law (Fin n)) :=
    (uniform_value_pos_iff_no_uniformEquilibriumPayoff reward).mpr hno
  exact hasPositiveFourPlayerAudit_iff_counterexampleAtCardFour.mp
    (hreduction reward hpositive)

/-- Quitting-counterexample cardinal reduction and audit-game cardinal
reduction are literally equivalent propositions. -/
theorem counterexampleCardinalReductionToFour_iff_auditCardinalReduction :
    CounterexampleCardinalReductionToFour ↔
      AuditCardinalReductionToFour := by
  exact ⟨auditCardinalReductionToFour_of_counterexampleCardinalReduction,
    counterexampleCardinalReductionToFour_of_auditCardinalReduction⟩

/-! ## Minimal-cardinality equivalence -/

/-- If every minimal counterexample has four players, then any counterexample
at all supplies a four-player one. -/
theorem counterexampleCardinalReductionToFour_of_allMinimal
    (hminimal : AllMinimalCounterexamplesHaveFourPlayers) :
    CounterexampleCardinalReductionToFour := by
  rintro ⟨n, reward, hwitness⟩
  have hn : 0 < n := by
    have hthree : 3 < n := by
      simpa using (Classical.choice hwitness).three_lt_card
    omega
  letI : Nonempty (Fin n) := Fintype.card_pos_iff.mp (by simpa using hn)
  obtain ⟨minimal⟩ :=
    exists_minimalFinQuittingCounterexample reward hwitness
  have hcount : minimal.playerCount = 4 := hminimal minimal
  have hatCount : HasQuittingCounterexampleAtCard minimal.playerCount :=
    ⟨minimal.reward, ⟨minimal.witness⟩⟩
  simpa [hcount] using hatCount

/-- Conversely, if every finite counterexample implies existence of a
four-player counterexample, cardinal minimality rules out a larger minimal
one. -/
theorem allMinimal_of_counterexampleCardinalReductionToFour
    (hreduction : CounterexampleCardinalReductionToFour) :
    AllMinimalCounterexamplesHaveFourPlayers := by
  intro minimal
  have hany : ∃ n, HasQuittingCounterexampleAtCard n :=
    ⟨minimal.playerCount, minimal.reward, ⟨minimal.witness⟩⟩
  have hfourCounter : HasQuittingCounterexampleAtCard 4 :=
    hreduction hany
  have hnotLt : ¬ 4 < minimal.playerCount :=
    fun hlt ↦ minimal.minimal 4 hlt hfourCounter
  have hthree : 3 < minimal.playerCount := by
    simpa using minimal.witness.three_lt_card
  omega

/-- The fixed larger-to-four statement is exactly the assertion that every
cardinal-minimal counterexample has four players. -/
theorem counterexampleCardinalReductionToFour_iff_allMinimal :
    CounterexampleCardinalReductionToFour ↔
      AllMinimalCounterexamplesHaveFourPlayers := by
  exact ⟨allMinimal_of_counterexampleCardinalReductionToFour,
    counterexampleCardinalReductionToFour_of_allMinimal⟩

/-! ## A non-tautological operational value-transfer certificate -/

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- A profilewise score reduction between two random-deviation audit games.

Every target Coordinator profile is translated to a source profile.  The
target score dominates a fixed positive multiple of the translated source
score.  This orientation is contrapositive: a low-score target profile would
produce a low-score source profile. -/
structure UniformScoreReduction
    (sourceReward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (targetReward : {S : Finset κ // S.Nonempty} → Payoff κ) where
  /-- Translate any target schedule back to a source schedule. -/
  liftCoordinator : CoordinatorMove targetReward → CoordinatorMove sourceReward
  /-- Quantitative loss retained by the reduction. -/
  scale : ℝ
  scale_pos : 0 < scale
  /-- Profilewise audit-score domination. -/
  score_dom : ∀ targetProfile,
    scale * score sourceReward (Law.uniform : Law ι)
        (liftCoordinator targetProfile) ≤
      score targetReward (Law.uniform : Law κ) targetProfile

namespace UniformScoreReduction

variable {sourceReward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {targetReward : {S : Finset κ // S.Nonempty} → Payoff κ}

/-- A profilewise score reduction transports the Coordinator's infimum value. -/
theorem value_transport
    (reduction : UniformScoreReduction sourceReward targetReward) :
    reduction.scale * value sourceReward (Law.uniform : Law ι) ≤
      value targetReward (Law.uniform : Law κ) := by
  unfold value
  apply le_csInf (Set.range_nonempty _)
  rintro targetScore ⟨targetProfile, rfl⟩
  calc
    reduction.scale *
        sInf (Set.range fun sourceProfile : CoordinatorMove sourceReward ↦
          score sourceReward (Law.uniform : Law ι) sourceProfile) ≤
      reduction.scale *
        score sourceReward (Law.uniform : Law ι)
          (reduction.liftCoordinator targetProfile) := by
            apply mul_le_mul_of_nonneg_left
            · exact csInf_le
                (bddBelow_range_score sourceReward
                  (Law.uniform : Law ι))
                ⟨reduction.liftCoordinator targetProfile, rfl⟩
            · exact reduction.scale_pos.le
    _ ≤ score targetReward (Law.uniform : Law κ) targetProfile :=
      reduction.score_dom targetProfile

/-- In particular, positive source audit value forces positive target audit
value. -/
theorem target_value_pos
    (reduction : UniformScoreReduction sourceReward targetReward)
    (hsource : 0 < value sourceReward (Law.uniform : Law ι)) :
    0 < value targetReward (Law.uniform : Law κ) := by
  exact (mul_pos reduction.scale_pos hsource).trans_le
    reduction.value_transport

/-- The operational reduction transports nonexistence of a UE payoff. -/
theorem target_noUniformPayoff
    (reduction : UniformScoreReduction sourceReward targetReward)
    (hsource : ¬ ∃ payoff : Payoff ι,
      (quittingGame sourceReward).IsUniformEquilibriumPayoff none payoff) :
    ¬ ∃ payoff : Payoff κ,
      (quittingGame targetReward).IsUniformEquilibriumPayoff none payoff := by
  have hsourcePos : 0 < value sourceReward (Law.uniform : Law ι) :=
    (uniform_value_pos_iff_no_uniformEquilibriumPayoff sourceReward).mpr hsource
  exact (uniform_value_pos_iff_no_uniformEquilibriumPayoff targetReward).mp
    (reduction.target_value_pos hsourcePos)

end UniformScoreReduction

/-! ## Four-player operational producer -/

/-- A concrete operational reduction from one source table to some
four-player target table.  Target positivity is a theorem, not a field. -/
structure OperationalFourPlayerReduction
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (sourceReward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  targetReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)
  reduction : UniformScoreReduction sourceReward targetReward

namespace OperationalFourPlayerReduction

variable {sourceReward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A supplied operational four-player reduction sends positive source audit
value to positive four-player audit value. -/
theorem target_value_pos
    (reduction : OperationalFourPlayerReduction sourceReward)
    (hsource : 0 < value sourceReward (Law.uniform : Law ι)) :
    0 < value reduction.targetReward (Law.uniform : Law (Fin 4)) :=
  reduction.reduction.target_value_pos hsource

/-- Package the target of an operational reduction as the existential
four-player audit counterexample. -/
theorem hasPositiveFourPlayerAudit
    (reduction : OperationalFourPlayerReduction sourceReward)
    (hsource : 0 < value sourceReward (Law.uniform : Law ι)) :
    HasPositiveFourPlayerAudit :=
  ⟨reduction.targetReward, reduction.target_value_pos hsource⟩

end OperationalFourPlayerReduction

/-- The constructive producer sought by a genuine audit-game cardinal
reduction: every positive finite source audit has an operational four-player
score reduction.  This is deliberately a definition, not an asserted
theorem. -/
def EveryPositiveAuditHasOperationalFourReduction : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (sourceReward : {S : Finset ι // S.Nonempty} → Payoff ι),
    0 < value sourceReward (Law.uniform : Law ι) →
      Nonempty (OperationalFourPlayerReduction sourceReward)

/-- The operational producer implies the exact cardinal reduction. -/
theorem auditCardinalReductionToFour_of_operationalProducer
    (hproducer : EveryPositiveAuditHasOperationalFourReduction) :
    AuditCardinalReductionToFour := by
  intro ι _ _ _ reward hpositive
  obtain ⟨reduction⟩ := hproducer reward hpositive
  exact reduction.hasPositiveFourPlayerAudit hpositive

/-! ## Consequences of the open cardinal reduction -/

/-- If the cardinal reduction holds, solving every four-player table solves
every finite nonempty quitting game. -/
theorem allFiniteQuittingGames_of_cardinalReduction_of_fourPlayer
    (hreduction : CounterexampleCardinalReductionToFour)
    (hfour : ∀ reward :
      {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      ∃ payoff : Payoff (Fin 4),
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  have hwitness : Nonempty (QuittingTerminalExploitabilityWitness reward) :=
    (not_exists_uniformEquilibriumPayoff_iff_nonempty_terminalExploitabilityWitness
      reward).mp hno
  have hcanonical : Nonempty (QuittingTerminalExploitabilityWitness
      (quittingRewardReindex (Fintype.equivFin ι) reward)) :=
    (nonempty_terminalExploitabilityWitness_reindex_fin_iff reward).2 hwitness
  have hany : ∃ n, HasQuittingCounterexampleAtCard n :=
    ⟨Fintype.card ι, _, hcanonical⟩
  obtain ⟨targetReward, htargetWitness⟩ := hreduction hany
  have htargetNo : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame targetReward).IsUniformEquilibriumPayoff none payoff :=
    (not_exists_uniformEquilibriumPayoff_iff_nonempty_terminalExploitabilityWitness
      targetReward).mpr htargetWitness
  exact htargetNo (hfour targetReward)

/-- The operational producer is therefore a sufficient reduction of the
full finite-player conjecture to its four-player instance. -/
theorem allFiniteQuittingGames_of_operationalProducer_of_fourPlayer
    (hproducer : EveryPositiveAuditHasOperationalFourReduction)
    (hfour : ∀ reward :
      {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      ∃ payoff : Payoff (Fin 4),
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  allFiniteQuittingGames_of_cardinalReduction_of_fourPlayer
    (counterexampleCardinalReductionToFour_of_auditCardinalReduction
      (auditCardinalReductionToFour_of_operationalProducer hproducer))
      hfour reward

/-! ## Permanent fences -/

/-- The exact cardinal reduction is not obtained merely from the landed fact
that counterexamples have at least four players.  This alias records the
lower bound without pretending to supply the open upper bound. -/
theorem minimalCounterexample_four_le
    (minimal : MinimalFinQuittingCounterexample) :
    4 ≤ minimal.playerCount :=
  minimal.four_le_playerCount

/-- Every proper restriction of a minimal counterexample is solved.  The
result is deliberately restated at the restricted game and carries no claim
that the excluded player's incentives are controlled. -/
theorem minimalCounterexample_properRestriction_isSolved
    (minimal : MinimalFinQuittingCounterexample)
    (players : Finset (Fin minimal.playerCount))
    (hplayers : players.Nonempty) (hproper : players ≠ Finset.univ) :
    ∃ payoff : Payoff {i // i ∈ players},
      (quittingGame
        (quittingRewardRestrict minimal.reward players)).IsUniformEquilibriumPayoff
          none payoff :=
  minimal.properRestriction_exists_uniformEquilibriumPayoff
    players hplayers hproper

end CardinalReduction
end RandomDeviationAudit
end GameTheory
