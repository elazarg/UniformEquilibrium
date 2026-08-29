/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport

/-!
# No general transport of the quit-now-versus-never contrast across a seam

Read a player's response contrast at a behavior profile as its payoff from
quitting at date zero minus its payoff from never quitting, both taken
against the other players' fixed behavior.  A one-player full replacement
changes one coordinate of the profile and leaves the rest alone.  The
proposed transport principle asserts that such a replacement leaves every
other player's contrast unchanged.

That principle is false.  Take four players, a reward table paying player
`1` the value `1` on the simultaneous exit of `{0, 1}` and zero on every
other coalition and coordinate, the parent profile at which everybody
continues at every live history, and the child profile obtained by replacing
player `0` with sure Quit.  At the parent, player `1` quitting alone reaches
the coalition `{1}`, worth zero, and never quitting reaches no coalition,
also worth zero, so the contrast is zero.  At the child, player `1` quitting
now reaches `{0, 1}`, worth one, while continuing is absorbed at `{0}`,
worth zero, so the contrast is one.  A contrast of zero becomes a contrast
of one across a single one-player replacement.

Two facts fix the scope of this table.  First, its global minimum terminal
semantic debt is zero: the empty set is a sure exit set for it, so the
all-Never profile is an exact terminal equilibrium, its terminal semantic
debt vanishes in every coordinate, and the total-debt infimum is zero.  The
table is therefore a regression against a proposed transport principle and
not a counterexample to existence of a uniform equilibrium payoff.

Second, the refutation is of the general identity only.  It says nothing
about a transport statement carrying positive-minimum provenance, since the
table has no positive minimum to provide such provenance; a principle
restricted to seams over a positive minimum of terminal semantic debt is
untouched by this witness.  The replacement here also raises debt — player
`1` has terminal semantic debt one at the child — so the seam leaves the
zero-debt fiber of the parent, and a principle restricted to replacements
that stay on one debt fiber is likewise untouched.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The response contrast and the proposed transport principle -/

/-- Player `who`'s payoff from quitting at date zero minus its payoff from
never quitting, both against the other players' fixed behavior in
`profile`. -/
def quittingQuitNowVersusNeverContrast
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) : ℝ :=
  quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who (some 0))) who -
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingAlwaysContinueStrategy reward who)) who

/-- The proposed cross-seam response transport at a fixed finite player
type: replacing one player's whole behavior strategy leaves every other
player's quit-now-versus-never contrast unchanged. -/
def IsQuittingCrossSeamContrastTransport
    (players : Type) [Fintype players] [DecidableEq players] : Prop :=
  ∀ (reward : {S : Finset players // S.Nonempty} → Payoff players)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : players)
    (replacement : (quittingGame reward).BehaviorStrategy mover),
    observer ≠ mover →
      quittingQuitNowVersusNeverContrast reward
          (Function.update profile mover replacement) observer =
        quittingQuitNowVersusNeverContrast reward profile observer

/-- Replacing one coordinate of a stationary profile by the always-quit
strategy is again stationary, at the root with that coordinate pinned to
Quit. -/
theorem update_quittingStationaryProfile_alwaysQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    Function.update (quittingStationaryProfile reward root) who
        (quittingAlwaysQuitStrategy reward who) =
      quittingStationaryProfile reward
        (Function.update root who (PMF.pure true)) := by
  funext player time history
  by_cases hplayer : player = who
  · subst player
    simp only [Function.update_self, quittingAlwaysQuitStrategy,
      quittingStationaryProfile, StochasticGame.stationaryBehaviorProfile]
    rfl
  · simp [Function.update_of_ne hplayer, quittingStationaryProfile,
      StochasticGame.stationaryBehaviorProfile]

/-- At a pure sure-exit profile the response contrast is the difference of
the two membership toggles: joining the exit set against leaving it. -/
theorem quittingQuitNowVersusNeverContrast_pureSetRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) :
    quittingQuitNowVersusNeverContrast reward
        (quittingStationaryProfile reward (quittingPureSetRoot S)) who =
      quittingSetReward reward (insert who S) who -
        quittingSetReward reward (S.erase who) who := by
  unfold quittingQuitNowVersusNeverContrast
  rw [quittingTerminalPayoff_update_pureSetRoot_quitNow,
    quittingTerminalPayoff_update_pureSetRoot_alwaysContinue]

/-! ## The four-player witness -/

/-- Four players, one paid pair exit.  Player `1` is paid `1` exactly on the
simultaneous exit of `{0, 1}`; every other coalition and coordinate pays
`0`. -/
def quittingFinFourPairedExitReward :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun coalition who ↦
    if who = 1 ∧ coalition.val = ({0, 1} : Finset (Fin 4)) then 1 else 0

/-- The parent profile: every player continues at every live history. -/
def quittingFinFourPairedExitParentProfile :
    (quittingGame quittingFinFourPairedExitReward).BehaviorProfile :=
  quittingStationaryProfile quittingFinFourPairedExitReward
    (quittingPureSetRoot (∅ : Finset (Fin 4)))

/-- The child profile: player `0` quits at every live history, hence surely
at date zero, and every other player continues. -/
def quittingFinFourPairedExitChildProfile :
    (quittingGame quittingFinFourPairedExitReward).BehaviorProfile :=
  quittingStationaryProfile quittingFinFourPairedExitReward
    (quittingPureSetRoot ({0} : Finset (Fin 4)))

/-- No singleton coalition is the paid pair, so every player's solo exit
pays it zero. -/
theorem quittingFinFourPairedExitReward_singleton (who : Fin 4) :
    quittingFinFourPairedExitReward
        ⟨{who}, Finset.singleton_nonempty who⟩ who = 0 := by
  have hne : ¬ (who = 1 ∧ ({who} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4))) := by
    rintro ⟨-, hset⟩
    have hcard := congrArg Finset.card hset
    simp at hcard
  simp only [quittingFinFourPairedExitReward, if_neg hne]

/-- The paid pair is exactly the coalition player `1` joins when player `0`
has already quit. -/
theorem quittingFinFourPairedExitReward_insert_one_zero :
    quittingSetReward quittingFinFourPairedExitReward
      (insert 1 ({0} : Finset (Fin 4))) 1 = 1 := by
  rw [quittingSetReward_of_nonempty _ (Finset.insert_nonempty _ _)]
  have hset : (insert 1 ({0} : Finset (Fin 4))) = ({0, 1} : Finset (Fin 4)) :=
    Finset.pair_comm 1 0
  simp [quittingFinFourPairedExitReward, hset]

/-- Player `0` quitting alone pays player `1` nothing. -/
theorem quittingFinFourPairedExitReward_zero_at_one :
    quittingSetReward quittingFinFourPairedExitReward
      ({0} : Finset (Fin 4)) 1 = 0 := by
  rw [quittingSetReward_of_nonempty _ (Finset.singleton_nonempty _)]
  have hne : ({0} : Finset (Fin 4)) ≠ ({0, 1} : Finset (Fin 4)) := by
    intro hset
    have hcard := congrArg Finset.card hset
    simp at hcard
  simp [quittingFinFourPairedExitReward, hne]

/-- The child profile is a one-player full replacement of the parent
profile: only player `0`'s coordinate changes. -/
theorem quittingFinFourPairedExitChildProfile_eq_update :
    quittingFinFourPairedExitChildProfile =
      Function.update quittingFinFourPairedExitParentProfile 0
        (quittingAlwaysQuitStrategy quittingFinFourPairedExitReward 0) := by
  rw [quittingFinFourPairedExitParentProfile,
    update_quittingStationaryProfile_alwaysQuit,
    update_quittingPureSetRoot_true,
    quittingFinFourPairedExitChildProfile]
  congr 1

/-- At the parent profile, player `1` is indifferent between quitting at
date zero and never quitting. -/
theorem quittingFinFourPairedExitParentContrast :
    quittingQuitNowVersusNeverContrast quittingFinFourPairedExitReward
      quittingFinFourPairedExitParentProfile 1 = 0 := by
  rw [quittingFinFourPairedExitParentProfile,
    quittingQuitNowVersusNeverContrast_pureSetRoot]
  rw [show (∅ : Finset (Fin 4)).erase 1 = ∅ from Finset.erase_empty 1,
    quittingSetReward_empty]
  rw [show insert (1 : Fin 4) (∅ : Finset (Fin 4)) = {1} by simp]
  rw [quittingSetReward_of_nonempty _ (Finset.singleton_nonempty _),
    quittingFinFourPairedExitReward_singleton]
  ring

/-- At the child profile, player `1` strictly prefers quitting at date zero
to never quitting, by exactly one. -/
theorem quittingFinFourPairedExitChildContrast :
    quittingQuitNowVersusNeverContrast quittingFinFourPairedExitReward
      quittingFinFourPairedExitChildProfile 1 = 1 := by
  rw [quittingFinFourPairedExitChildProfile,
    quittingQuitNowVersusNeverContrast_pureSetRoot]
  rw [show ({0} : Finset (Fin 4)).erase 1 = {0} by decide,
    quittingFinFourPairedExitReward_zero_at_one,
    quittingFinFourPairedExitReward_insert_one_zero]
  ring

/-- **The response contrast is not preserved across a one-player full
replacement.**  Player `1`'s contrast is zero at the parent profile and one
at the child. -/
theorem quittingFinFourPairedExitContrast_ne :
    quittingQuitNowVersusNeverContrast quittingFinFourPairedExitReward
        quittingFinFourPairedExitChildProfile 1 ≠
      quittingQuitNowVersusNeverContrast quittingFinFourPairedExitReward
        quittingFinFourPairedExitParentProfile 1 := by
  rw [quittingFinFourPairedExitChildContrast,
    quittingFinFourPairedExitParentContrast]
  norm_num

/-- **No general cross-seam response transport.**  At four players there is
no identity carrying the quit-now-versus-never contrast across a one-player
full replacement. -/
theorem not_isQuittingCrossSeamContrastTransport_finFour :
    ¬ IsQuittingCrossSeamContrastTransport (Fin 4) := by
  intro htransport
  have hseam := htransport quittingFinFourPairedExitReward
    quittingFinFourPairedExitParentProfile 0 1
    (quittingAlwaysQuitStrategy quittingFinFourPairedExitReward 0)
    (by decide)
  rw [← quittingFinFourPairedExitChildProfile_eq_update] at hseam
  exact quittingFinFourPairedExitContrast_ne hseam

/-! ## Scope: the witness table has zero minimum debt -/

/-- The empty set is a sure exit set for the witness table: no player has a
profitable solo exit. -/
theorem quittingFinFourPairedExitReward_isQuittingSureExitSet_empty :
    IsQuittingSureExitSet quittingFinFourPairedExitReward (∅ : Finset (Fin 4)) := by
  rw [isQuittingSureExitSet_empty_iff]
  intro who
  rw [quittingSoloReward, quittingFinFourPairedExitReward_singleton]

/-- The witness table has a uniform equilibrium payoff, namely the
all-Never payoff. -/
theorem quittingFinFourPairedExit_isUniformEquilibriumPayoff :
    (quittingGame quittingFinFourPairedExitReward).IsUniformEquilibriumPayoff
      none (quittingSetReward quittingFinFourPairedExitReward ∅) :=
  isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
    quittingFinFourPairedExitReward
    quittingFinFourPairedExitReward_isQuittingSureExitSet_empty

/-- The parent profile of the witness is exact: its terminal semantic debt
vanishes in every coordinate. -/
theorem quittingFinFourPairedExitParentProfile_terminalSemanticDebt_eq_zero
    (who : Fin 4) :
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair quittingFinFourPairedExitReward
        quittingFinFourPairedExitParentProfile) who = 0 := by
  rw [quittingFinFourPairedExitParentProfile,
    quittingTerminalSemanticDebt_pureSetRoot_eq]
  rw [show (∅ : Finset (Fin 4)).erase who = ∅ from Finset.erase_empty who,
    quittingSetReward_empty]
  rw [show insert who (∅ : Finset (Fin 4)) = {who} by simp]
  rw [quittingSetReward_of_nonempty _ (Finset.singleton_nonempty _),
    quittingFinFourPairedExitReward_singleton]
  simp

/-- The witness table's total terminal semantic debt vanishes at its parent
profile. -/
theorem quittingFinFourPairedExitParentProfile_terminalSemanticDebtSum_eq_zero :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair quittingFinFourPairedExitReward
        quittingFinFourPairedExitParentProfile) = 0 := by
  unfold quittingTerminalSemanticDebtSum
  rw [Finset.sum_congr rfl fun who _ ↦
    quittingFinFourPairedExitParentProfile_terminalSemanticDebt_eq_zero who]
  simp

/-- The witness table's literal total-debt infimum is zero. -/
theorem quittingFinFourPairedExit_terminalDebtSumInf_eq_zero :
    quittingTerminalDebtSumInf quittingFinFourPairedExitReward = 0 := by
  apply le_antisymm
  · have hle := quittingTerminalDebtSumInf_le
      (reward := quittingFinFourPairedExitReward)
      quittingFinFourPairedExitParentProfile
    rwa [quittingTerminalDebtSum_eq_terminalSemanticDebtSum,
      quittingFinFourPairedExitParentProfile_terminalSemanticDebtSum_eq_zero]
      at hle
  · have hnonempty : (Set.range
        (quittingTerminalDebtSum quittingFinFourPairedExitReward)).Nonempty :=
      ⟨_, Set.mem_range_self quittingFinFourPairedExitParentProfile⟩
    unfold quittingTerminalDebtSumInf
    apply le_csInf hnonempty
    rintro total ⟨profile, rfl⟩
    unfold quittingTerminalDebtSum
    exact Finset.sum_nonneg fun player _ ↦
      quittingTerminalDeviationDebt_nonneg quittingFinFourPairedExitReward
        profile player

/-- The child profile of the witness is not exact: player `1`'s terminal
semantic debt there is one.  The replacement therefore leaves the zero-debt
fiber on which the parent sits. -/
theorem quittingFinFourPairedExitChildProfile_terminalSemanticDebt_one :
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair quittingFinFourPairedExitReward
        quittingFinFourPairedExitChildProfile) 1 = 1 := by
  rw [quittingFinFourPairedExitChildProfile,
    quittingTerminalSemanticDebt_pureSetRoot_eq]
  rw [show ({0} : Finset (Fin 4)).erase 1 = {0} by decide,
    quittingFinFourPairedExitReward_zero_at_one,
    quittingFinFourPairedExitReward_insert_one_zero]
  norm_num

/-- The witness table has no positive minimum of terminal semantic debt, so
it carries no positive-minimum provenance for a restricted transport
statement. -/
theorem quittingFinFourPairedExit_not_hasPositiveMinimumTerminalSemanticDebt :
    ¬ HasPositiveMinimumTerminalSemanticDebt quittingFinFourPairedExitReward := by
  rw [← quittingTerminalDebtSumInf_pos_iff_hasPositiveMinimumTerminalSemanticDebt,
    quittingFinFourPairedExit_terminalDebtSumInf_eq_zero]
  exact lt_irrefl 0

end GameTheory
