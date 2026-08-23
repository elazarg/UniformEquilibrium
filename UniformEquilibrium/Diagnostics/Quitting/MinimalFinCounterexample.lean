/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.TerminalExploitabilityReindexNaturality
import UniformEquilibrium.Quitting.Classification.TerminalExploitabilitySmallPlayers
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.StaticStrategicOrientation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticConcentratedSingletonStrategicCompression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlayerDeletion

/-!
# Minimal finite counterexamples to quitting-game uniform equilibrium

This module gives the classical cardinality-minimal normal form for a
hypothetical finite quitting-game counterexample.  A counterexample may be
reindexed onto `Fin n`, where `4 ≤ n`, and `n` may be chosen so that every
quitting game on a smaller nonempty finite player type has a
uniform-equilibrium payoff.

It also defines restriction of a reward table to a finite set of retained
players.  Minimality solves every nonempty proper restriction as a quitting
game in its own right.  This statement is intentionally fenced at the
restricted game: it supplies neither payoff coordinates for excluded players
nor inequalities deterring an excluded player from joining a quitter
coalition.  Those are separate extension obligations.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [DecidableEq ι]

/-- Restrict a quitting reward table to a finite set of retained players.
Coalitions are included into the ambient player type, while payoff coordinates
are restricted to retained players. -/
def quittingRewardRestrict
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) :
    {T : Finset {i // i ∈ players} // T.Nonempty} →
      Payoff {i // i ∈ players} :=
  fun T who ↦
    reward
      ⟨T.1.map (Function.Embedding.subtype (fun i ↦ i ∈ players)),
        Finset.map_nonempty.mpr T.2⟩
      who.1

omit [DecidableEq ι] in
/-- Evaluation of a restricted reward table is evaluation of the ambient
table on the included coalition and player. -/
@[simp] theorem quittingRewardRestrict_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι)
    (T : {T : Finset {i // i ∈ players} // T.Nonempty})
    (who : {i // i ∈ players}) :
    quittingRewardRestrict reward players T who =
      reward
        ⟨T.1.map (Function.Embedding.subtype (fun i ↦ i ∈ players)),
          Finset.map_nonempty.mpr T.2⟩
        who.1 :=
  rfl

/-- There is a quitting terminal exploitability witness on the canonical
`n`-player type. -/
def HasQuittingCounterexampleAtCard (n : ℕ) : Prop :=
  ∃ reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n),
    Nonempty (QuittingTerminalExploitabilityWitness reward)

/-- Every player either has positive punishment value, has solo payoff at
least its punishment value, or strictly gains by joining a nonempty coalition
of the other players. -/
def HasQuittingOwnerEntryTrichotomy [Fintype ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ owner,
    0 < quittingPunishmentValue reward owner ∨
      quittingPunishmentValue reward owner ≤
        quittingSoloReward reward owner owner ∨
      ∃ (quitters : Finset ι) (hquitters : quitters.Nonempty),
        owner ∉ quitters ∧
          reward ⟨quitters, hquitters⟩ owner <
            reward
              ⟨insert owner quitters,
                Finset.insert_nonempty owner quitters⟩ owner

/-- A cardinality-minimal finite quitting-game counterexample in canonical
coordinates.  Minimality is stated directly in terms of the terminal
exploitability witness;
the nonexistence characterization turns it into equilibrium existence below. -/
structure MinimalFinQuittingCounterexample where
  /-- Number of players in the minimal counterexample. -/
  playerCount : ℕ
  /-- Canonically indexed terminal reward table. -/
  reward : {S : Finset (Fin playerCount) // S.Nonempty} →
    Payoff (Fin playerCount)
  /-- The table is a genuine terminal exploitability witness. -/
  witness : QuittingTerminalExploitabilityWitness reward
  /-- No smaller canonical player cardinality carries a terminal exploitability
  witness. -/
  minimal : ∀ m, m < playerCount → ¬ HasQuittingCounterexampleAtCard m

/-- Small-player existence forces every minimal counterexample to have at
least four players. -/
theorem MinimalFinQuittingCounterexample.four_le_playerCount
    (minimal : MinimalFinQuittingCounterexample) :
    4 ≤ minimal.playerCount := by
  have hcard := minimal.witness.three_lt_card
  simp only [Fintype.card_fin] at hcard
  omega

/-- If any finite nonempty quitting counterexample exists, then a
cardinality-minimal one exists on `Fin n`. -/
theorem exists_minimalFinQuittingCounterexample
    [Fintype ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcounterexample : Nonempty (QuittingTerminalExploitabilityWitness reward)) :
    Nonempty MinimalFinQuittingCounterexample := by
  classical
  letI : Nonempty ι := hcounterexample.some.nonempty_players
  have hcanonical : Nonempty (QuittingTerminalExploitabilityWitness
      (quittingRewardReindex (Fintype.equivFin ι) reward)) :=
    (nonempty_terminalExploitabilityWitness_reindex_fin_iff reward).2 hcounterexample
  have hexists : ∃ n, HasQuittingCounterexampleAtCard n :=
    ⟨Fintype.card ι, _, hcanonical⟩
  let n := Nat.find hexists
  have hn : HasQuittingCounterexampleAtCard n := Nat.find_spec hexists
  obtain ⟨minimalReward, ⟨minimalWitness⟩⟩ := hn
  refine ⟨{
    playerCount := n
    reward := minimalReward
    witness := minimalWitness
    minimal := ?_ }⟩
  intro m hm hcounter
  have hleast : n ≤ m := Nat.find_min' hexists hcounter
  omega

namespace MinimalFinQuittingCounterexample

/-- Every quitting game on a smaller nonempty finite player type has a
uniform-equilibrium payoff.  Player reindexing is used only to compare its
cardinality with the canonical minimal table. -/
theorem exists_uniformEquilibriumPayoff_of_card_lt
    (minimal : MinimalFinQuittingCounterexample)
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (hcard : Fintype.card κ < minimal.playerCount)
    (reward : {S : Finset κ // S.Nonempty} → Payoff κ) :
    ∃ payoff : Payoff κ,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  have hwitness : Nonempty (QuittingTerminalExploitabilityWitness reward) :=
    (not_exists_uniformEquilibriumPayoff_iff_nonempty_terminalExploitabilityWitness
      reward).1 hno
  have hcanonical : Nonempty (QuittingTerminalExploitabilityWitness
      (quittingRewardReindex (Fintype.equivFin κ) reward)) :=
    (nonempty_terminalExploitabilityWitness_reindex_fin_iff reward).2 hwitness
  exact minimal.minimal (Fintype.card κ) hcard ⟨_, hcanonical⟩

/-- Every nonempty proper player restriction of a minimal table has a
uniform-equilibrium payoff for the retained-player game.

This theorem does **not** extend that equilibrium to the ambient game: no
claim is made about excluded-player payoffs or deviations in which an
excluded player joins the quitting coalition. -/
theorem properRestriction_exists_uniformEquilibriumPayoff
    (minimal : MinimalFinQuittingCounterexample)
    (players : Finset (Fin minimal.playerCount))
    (hplayers : players.Nonempty) (hproper : players ≠ Finset.univ) :
    ∃ payoff : Payoff {i // i ∈ players},
      (quittingGame
        (quittingRewardRestrict minimal.reward players)).IsUniformEquilibriumPayoff
          none payoff := by
  letI : Nonempty {i // i ∈ players} := hplayers.to_subtype
  apply minimal.exists_uniformEquilibriumPayoff_of_card_lt
  simpa using (Finset.card_lt_iff_ne_univ players).2 hproper

/-- Exact deletion at the retained terminal gap is impossible in a
cardinality-minimal counterexample.  The deleted table would have a positive
terminal exploitability gap on a strictly smaller nonempty player type,
where minimality supplies a uniform-equilibrium payoff. -/
theorem not_hasQuittingExactPlayerDeletionAtGap
    (minimal : MinimalFinQuittingCounterexample)
    (owner : Fin minimal.playerCount) :
    ¬ HasQuittingExactPlayerDeletionAtGap minimal.reward owner
      minimal.witness.terminalGap := by
  rintro ⟨hdeletedNonempty, hdeletedGap⟩
  letI : Nonempty (QuittingDeletedPlayer owner) := hdeletedNonempty
  have hcard' : Fintype.card (QuittingDeletedPlayer owner) <
      minimal.playerCount := by
    simpa using card_quittingDeletedPlayer_lt owner
  have hpayoff := minimal.exists_uniformEquilibriumPayoff_of_card_lt hcard'
    (quittingDeletePlayerReward minimal.reward owner)
  exact
    (quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
      (quittingDeletePlayerReward minimal.reward owner)
      minimal.witness.terminalGap_pos hdeletedGap) hpayoff

/-- At the negative singleton gate of a cardinality-minimal counterexample,
the deleted player must gain strictly by joining some nonempty coalition of
the other players.  Otherwise the full terminal gap descends to the smaller
deleted game, contradicting minimality. -/
theorem exists_strict_owner_entry_of_solo_lt_punishment_of_nonpos
    (minimal : MinimalFinQuittingCounterexample)
    (owner : Fin minimal.playerCount)
    (hsolo : quittingSoloReward minimal.reward owner owner <
      quittingPunishmentValue minimal.reward owner)
    (hpunishment : quittingPunishmentValue minimal.reward owner ≤ 0) :
    ∃ (quitters : Finset (Fin minimal.playerCount))
        (hquitters : quitters.Nonempty),
      owner ∉ quitters ∧
        minimal.reward ⟨quitters, hquitters⟩ owner <
          minimal.reward
            ⟨insert owner quitters,
              Finset.insert_nonempty owner quitters⟩ owner := by
  have hsolo' : minimal.reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue minimal.reward owner := by
    exact hsolo
  rcases exists_strict_owner_toggle_or_exact_playerDeletion
      minimal.reward owner minimal.witness.terminalGap_pos
      minimal.witness.terminalExploitability hsolo' hpunishment with
    hentry | hdeletion
  · exact hentry
  · exact False.elim
      (minimal.not_hasQuittingExactPlayerDeletionAtGap owner
        ⟨hdeletion.1, hdeletion.2.1⟩)

/-- Every player of a cardinality-minimal counterexample satisfies the exact
owner-entry trichotomy. -/
theorem hasQuittingOwnerEntryTrichotomy
    (minimal : MinimalFinQuittingCounterexample) :
    HasQuittingOwnerEntryTrichotomy minimal.reward := by
  intro owner
  by_cases hpunishment : 0 < quittingPunishmentValue minimal.reward owner
  · exact Or.inl hpunishment
  · right
    by_cases hsolo : quittingPunishmentValue minimal.reward owner ≤
        quittingSoloReward minimal.reward owner owner
    · exact Or.inl hsolo
    · exact Or.inr
        (minimal.exists_strict_owner_entry_of_solo_lt_punishment_of_nonpos
          owner (lt_of_not_ge hsolo) (le_of_not_gt hpunishment))

/-- On a cardinality-minimal counterexample, the stopping-law singleton
orientation has only the common static atomic-toggle handoff.  The deletion
arm of the general compression is eliminated by minimality rather than
retained as a second leaf. -/
theorem stoppingLawSingletonStrategicOrientation_atomicHandoff
    (minimal : MinimalFinQuittingCounterexample)
    {frontier : QuittingPositiveMinimumDebtTangentFamily minimal.reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (horientation :
      HasQuittingStoppingLawSingletonStrategicOrientation
        (witness := minimal.witness) packet) :
    HasQuittingStaticAtomicToggleHandoff minimal.reward := by
  rcases minimal.witness.stoppingLawSingletonStrategicOrientation_compress
      packet horientation with hatomic | hdeletion
  · exact hatomic
  · exact False.elim
      (minimal.not_hasQuittingExactPlayerDeletionAtGap packet.observer
        hdeletion)

end MinimalFinQuittingCounterexample

/-- If any finite quitting counterexample exists, one exists at minimal player
cardinality whose every player satisfies the owner-entry trichotomy.  The
minimal witness also solves every smaller finite quitting game and every
nonempty proper restriction of its own reward table. -/
theorem exists_minimalFinQuittingCounterexample_with_ownerEntryTrichotomy
    [Fintype ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcounterexample : Nonempty (QuittingTerminalExploitabilityWitness reward)) :
    ∃ minimal : MinimalFinQuittingCounterexample,
      HasQuittingOwnerEntryTrichotomy minimal.reward := by
  obtain ⟨minimal⟩ :=
    exists_minimalFinQuittingCounterexample reward hcounterexample
  exact ⟨minimal, minimal.hasQuittingOwnerEntryTrichotomy⟩

end GameTheory
