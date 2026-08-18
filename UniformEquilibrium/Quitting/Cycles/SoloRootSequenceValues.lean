/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockTerminalConcentration
import UniformEquilibrium.Quitting.Paths.OpponentClockDichotomy
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium
import UniformEquilibrium.Quitting.Root.SuccessorCertificate
import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot

/-!
# Closed forms along a root sequence with a single possible quitter

A *solo* root at `owner` is one at which every other coordinate continues
surely; `eq_quittingSoloStationaryRoot_of_others_continue` identifies it with
`quittingSoloStationaryRoot owner` applied to the owner's own marginal.  A
root sequence that is solo at a fixed `owner` at every date admits exact
closed forms for all of the quantities that a unilateral stopping deviation
reads.

* **No opponent clock** (`quittingOpponentClockCharge_eq_zero_of_soloRoot`):
  the deleted-`owner` clock of a solo root is idle, hence
  (`quittingNonSoloMassLimit_eq_zero_of_soloRoots`) the sequence never
  absorbs outside `{owner}` and every other terminal coalition carries zero
  limiting mass (`quittingAbsorbedMassLimit_eq_zero_of_soloRoots`).
* **Terminal value** (`quittingRootSequenceTerminalValue_eq_of_soloRoots`):
  the delivery is the owner's singleton absorbed mass times the owner's
  singleton row, so it inherits that row's sign with no absorption
  hypothesis (`quittingRootSequenceTerminalValue_nonneg_of_soloRoots`), and
  equals the row outright once the sequence absorbs almost surely
  (`quittingRootSequenceTerminalValue_eq_soloReward_of_absorbing`).
* **Spectator coefficients**
  (`quittingFixedOpponentsContinueMass_eq_of_soloRoot`,
  `quittingFixedOpponentsContinueReward_eq_of_soloRoot`,
  `quittingFixedOpponentsQuitValue_eq_of_soloRoot`): a coordinate other than
  `owner` sees the owner's hazard as its whole environment.
* **Stopping values** (`quittingLiveLedgerAccum_eq_of_soloRoots`,
  `quittingRootSequencePureTimeTerminalValue_some_eq_of_soloRoots`): before
  its stop a spectator collects the owner's singleton row on the mass
  absorbed so far; at the stop it either exits alone or collides with the
  owner.

Every statement is at an arbitrary start date and asserts nothing about the
existence of solo sequences.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## A solo root leaves the deleted-owner clock idle -/

omit [Fintype ι] in
/-- Deleting `owner` from a solo root leaves the sure-continue row. -/
theorem update_pure_false_eq_soloStationaryRoot_of_soloRoot
    {root : ι → PMF Bool} {owner : ι}
    (hsolo : ∀ player, player ≠ owner → root player = PMF.pure false) :
    Function.update root owner (PMF.pure false) =
      quittingSoloStationaryRoot owner (PMF.pure false) := by
  funext player
  by_cases hplayer : player = owner
  · subst player
    simp [quittingSoloStationaryRoot]
  · rw [Function.update_of_ne hplayer, hsolo player hplayer]
    simp [quittingSoloStationaryRoot, hplayer]

/-- **The opponents of a solo owner cannot absorb.**  The owner's deleted
clock carries no charge at a root whose only possible quitter is the
owner. -/
theorem quittingOpponentClockCharge_eq_zero_of_soloRoot
    (roots : ℕ → ι → PMF Bool) {owner : ι} {time : ℕ}
    (hsolo : ∀ player, player ≠ owner → roots time player = PMF.pure false) :
    quittingOpponentClockCharge roots owner time = 0 := by
  rw [quittingOpponentClockCharge_eq_one_sub]
  unfold quittingFixedOpponentsContinueMass
  rw [update_pure_false_eq_soloStationaryRoot_of_soloRoot hsolo,
    quittingStationaryContinueMass_solo]
  simp

/-! ## Terminal concentration on a solo root sequence -/

/-- **A solo sequence absorbs only at the owner's singleton.**  The limiting
probability of any terminal coalition other than `{owner}` is zero. -/
theorem quittingNonSoloMassLimit_eq_zero_of_soloRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ)
    (hsolo : ∀ time player, player ≠ owner →
      roots time player = PMF.pure false) :
    quittingNonSoloMassLimit reward
      (quittingRootSequenceProfile reward roots start) owner = 0 := by
  have hcharge : ∀ offset,
      quittingOpponentClockCharge roots owner (start + offset) = 0 :=
    fun offset =>
      quittingOpponentClockCharge_eq_zero_of_soloRoot roots
        (hsolo (start + offset))
  have hsummable : Summable (fun offset =>
      quittingOpponentClockCharge roots owner (start + offset)) := by
    simp [hcharge]
  have htail : quittingOpponentClockTailCharge roots owner start = 0 := by
    unfold quittingOpponentClockTailCharge
    simp [hcharge]
  have hbound := one_sub_opponentOnlyLiveMassLimit_le_opponentClockTailCharge
    reward roots owner start hsummable
  rw [htail] at hbound
  have hle := quittingNonSoloMassLimit_le_one_sub_opponentLiveMassLimit
    reward (quittingRootSequenceProfile reward roots start) owner
  have hnonneg : 0 ≤ quittingNonSoloMassLimit reward
      (quittingRootSequenceProfile reward roots start) owner := by
    unfold quittingNonSoloMassLimit
    refine Finset.sum_nonneg fun terminal _ => ?_
    split
    · exact le_refl 0
    · exact quittingAbsorbedMassLimit_nonneg _ _ _
  linarith

/-- **Only the owner's singleton absorbs.**  Along a root sequence at which
`owner` is the only possible quitter, every other terminal coalition carries
zero absorbed mass. -/
theorem quittingAbsorbedMassLimit_eq_zero_of_soloRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ)
    (hsolo : ∀ time player, player ≠ owner →
      roots time player = PMF.pure false)
    {terminal : {S : Finset ι // S.Nonempty}}
    (hterminal : terminal ≠ quittingSingletonTerminal owner) :
    quittingAbsorbedMassLimit reward
      (quittingRootSequenceProfile reward roots start) terminal = 0 := by
  have hzero := quittingNonSoloMassLimit_eq_zero_of_soloRoots reward roots
    owner start hsolo
  unfold quittingNonSoloMassLimit at hzero
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg (fun S _ => by
    split
    · exact le_refl 0
    · exact quittingAbsorbedMassLimit_nonneg _ _ _)).1 hzero
  simpa [hterminal] using hterms terminal (Finset.mem_univ terminal)

/-- **Closed form of the terminal value on a solo root sequence.**  The
terminal payoff is the owner's singleton absorbed mass times the owner's
singleton row. -/
theorem quittingRootSequenceTerminalValue_eq_of_soloRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ)
    (hsolo : ∀ time player, player ≠ owner →
      roots time player = PMF.pure false) (who : ι) :
    quittingRootSequenceTerminalValue reward roots who start =
      quittingAbsorbedMassLimit reward
          (quittingRootSequenceProfile reward roots start)
          (quittingSingletonTerminal owner) *
        quittingSoloReward reward owner who := by
  rw [quittingRootSequenceTerminalValue, quittingTerminalPayoff]
  refine Finset.sum_eq_single (quittingSingletonTerminal owner) ?_ ?_
  · intro terminal _ hterminal
    rw [quittingAbsorbedMassLimit_eq_zero_of_soloRoots reward roots owner start
      hsolo hterminal, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- **The delivery of a solo root sequence inherits the owner's sign.**  No
absorption hypothesis is needed: the never-absorbed boundary contributes
nothing to a terminal payoff. -/
theorem quittingRootSequenceTerminalValue_nonneg_of_soloRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ)
    (hsolo : ∀ time player, player ≠ owner →
      roots time player = PMF.pure false) {who : ι}
    (hnonneg : 0 ≤ quittingSoloReward reward owner who) :
    0 ≤ quittingRootSequenceTerminalValue reward roots who start := by
  rw [quittingRootSequenceTerminalValue_eq_of_soloRoots reward roots owner
    start hsolo who]
  exact mul_nonneg (quittingAbsorbedMassLimit_nonneg reward _ _) hnonneg

/-- **The delivery of a solo sequence that absorbs almost surely.**  With no
surviving mass the whole delivery is the owner's singleton row. -/
theorem quittingRootSequenceTerminalValue_eq_soloReward_of_absorbing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ)
    (hsolo : ∀ time player, player ≠ owner →
      roots time player = PMF.pure false)
    (habsorb : quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward roots start) = 0) (who : ι) :
    quittingRootSequenceTerminalValue reward roots who start =
      quittingSoloReward reward owner who := by
  have hconservation := quittingLiveMassLimit_add_sum_absorbedMassLimit reward
    (quittingRootSequenceProfile reward roots start)
  have hconcentrate : ∑ terminal, quittingAbsorbedMassLimit reward
      (quittingRootSequenceProfile reward roots start) terminal =
      quittingAbsorbedMassLimit reward
        (quittingRootSequenceProfile reward roots start)
        (quittingSingletonTerminal owner) := by
    refine Finset.sum_eq_single (quittingSingletonTerminal owner) ?_ ?_
    · intro terminal _ hterminal
      exact quittingAbsorbedMassLimit_eq_zero_of_soloRoots reward roots owner
        start hsolo hterminal
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [hconcentrate, habsorb, zero_add] at hconservation
  rw [quittingRootSequenceTerminalValue_eq_of_soloRoots reward roots owner
    start hsolo who, hconservation, one_mul]

/-! ## Fixed-opponent coefficients of a spectator on a solo root sequence -/

/-- At a solo root the survival mass seen by a spectator is the owner's
continue probability. -/
theorem quittingFixedOpponentsContinueMass_eq_of_soloRoot
    (roots : ℕ → ι → PMF Bool) {owner other : ι} {time : ℕ}
    (hsolo : ∀ player, player ≠ owner → roots time player = PMF.pure false)
    (hne : other ≠ owner) :
    quittingFixedOpponentsContinueMass roots other time =
      (roots time owner false).toReal := by
  have hupdate : Function.update (roots time) other (PMF.pure false) =
      roots time := by
    rw [← hsolo other hne]
    exact Function.update_eq_self other (roots time)
  rw [quittingFixedOpponentsContinueMass, hupdate]
  conv_lhs => rw [eq_quittingSoloStationaryRoot_of_others_continue hsolo]
  exact quittingStationaryContinueMass_solo owner (roots time owner)

/-- At a solo root a spectator's continue reward is the owner's hazard times
the owner's singleton row. -/
theorem quittingFixedOpponentsContinueReward_eq_of_soloRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {owner other : ι} {time : ℕ}
    (hsolo : ∀ player, player ≠ owner → roots time player = PMF.pure false)
    (hne : other ≠ owner) :
    quittingFixedOpponentsContinueReward reward roots other time =
      (roots time owner true).toReal *
        quittingSoloReward reward owner other := by
  have hupdate : Function.update (roots time) other (PMF.pure false) =
      roots time := by
    rw [← hsolo other hne]
    exact Function.update_eq_self other (roots time)
  rw [quittingFixedOpponentsContinueReward, hupdate]
  conv_lhs => rw [eq_quittingSoloStationaryRoot_of_others_continue hsolo]
  exact quittingRootAbsorbingContribution_solo reward owner other
    (roots time owner)

/-- At a solo root a spectator's quit-now value mixes exiting alone with
colliding with the owner. -/
theorem quittingFixedOpponentsQuitValue_eq_of_soloRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {owner other : ι} {time : ℕ}
    (hsolo : ∀ player, player ≠ owner → roots time player = PMF.pure false)
    (hne : other ≠ owner) :
    quittingFixedOpponentsQuitValue reward roots other time =
      (roots time owner false).toReal * quittingSoloReward reward other other +
        (roots time owner true).toReal *
          quittingSingletonCollisionReward reward owner other := by
  have hstationary : quittingFixedOpponentsQuitValue reward roots other time =
      quittingStationaryFixedOpponentsQuitValue reward (roots time) other := rfl
  rw [hstationary]
  conv_lhs => rw [eq_quittingSoloStationaryRoot_of_others_continue hsolo]
  exact quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix reward hne
    (roots time owner)

/-! ## Closed form of a spectator's stopping values -/

/-- **Ledger telescope on a solo sequence.**  Everything a spectator collects
before stopping is the owner's singleton row weighted by the mass already
absorbed. -/
theorem quittingLiveLedgerAccum_eq_of_soloRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {owner other : ι} (hne : other ≠ owner)
    (hsolo : ∀ time player, player ≠ owner →
      roots time player = PMF.pure false) (start fuel : ℕ) :
    quittingLiveLedgerAccum reward roots other start fuel =
      (1 - quittingOpponentSurvivalWeight roots other start fuel) *
        quittingSoloReward reward owner other := by
  induction fuel with
  | zero => simp [quittingLiveLedgerAccum, quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hmass := quittingFixedOpponentsContinueMass_eq_of_soloRoot roots
        (hsolo (start + fuel)) hne
      have hreward := quittingFixedOpponentsContinueReward_eq_of_soloRoot reward
        roots (hsolo (start + fuel)) hne
      have hsum := quittingRoot_continueProbability_add_quitProbability
        (roots (start + fuel)) owner
      rw [quittingLiveLedgerAccum, Finset.sum_range_succ,
        ← quittingLiveLedgerAccum, ih, quittingOpponentSurvivalWeight_succ,
        hmass, hreward]
      linear_combination (quittingSoloReward reward owner other *
        quittingOpponentSurvivalWeight roots other start fuel) * hsum

/-- **A spectator's deterministic stop, in closed form.**  Before the stop the
spectator receives the owner's singleton row on the absorbed mass; at the stop
it exits alone or collides with the owner. -/
theorem quittingRootSequencePureTimeTerminalValue_some_eq_of_soloRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {owner other : ι} (hne : other ≠ owner)
    (hsolo : ∀ time player, player ≠ owner →
      roots time player = PMF.pure false) (start phase : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots other
        (some (start + phase)) start =
      (1 - quittingOpponentSurvivalWeight roots other start phase) *
          quittingSoloReward reward owner other +
        quittingOpponentSurvivalWeight roots other start phase *
          ((roots (start + phase) owner false).toReal *
              quittingSoloReward reward other other +
            (roots (start + phase) owner true).toReal *
              quittingSingletonCollisionReward reward owner other) := by
  rw [quittingRootSequencePureTimeTerminalValue_some_add reward roots other
      start phase,
    quittingLiveLedgerAccum_eq_of_soloRoots reward roots hne hsolo start phase,
    quittingFixedOpponentsQuitValue_eq_of_soloRoot reward roots
      (hsolo (start + phase)) hne]

end GameTheory
