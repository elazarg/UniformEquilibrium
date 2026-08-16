/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.AtomSequenceDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticReachedRowDebtLocalization

/-!
# Frontier consumer for reached-row debt localization

The positive-collision marked-tail predicate already supplies literal target
profiles with a uniformly reached row at which the observer's pure-time
strategy quits surely.  The observer's initial semantic debt vanishes on
these same profiles.  The reached-row theorem therefore applies without the
predicate's stored tail cluster or its escape/fiber alternative.

This consumer retains the actual profile sequence, stop times, terminal
coalition mass, and a uniform positive lower bound on one fixed player's
legal one-row gains.  It does not provide source re-entry or an exact
Nash--Bellman return.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- The literal target profile on which the reached-row certificate is
evaluated. -/
def quittingStoppingLawPositiveCollisionReachedRowProfile
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (rank : Nat) : (quittingGame reward).BehaviorProfile :=
  Function.update
    (quittingStoppingLawRectangleTargetProfile packet rank) packet.observer
    (quittingPureTimeBehaviorStrategy reward packet.observer
      (packet.quitTime rank))

/-- The canonical legal best-endpoint gain at a selected literal target row.
-/
def quittingStoppingLawPositiveCollisionReachedRowGain
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (stop : Nat -> Nat) (other : iota) (rank : Nat) : Real :=
  let profile := quittingStoppingLawPositiveCollisionReachedRowProfile
    packet rank
  let stage := stop rank
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  let action := quittingRootBestEndpointAction reward tail.1 root other
  let deviation := quittingStagePureEndpointBehaviorDeviation
    reward profile other stage action
  quittingTerminalPayoff reward
        (Function.update profile other deviation) other -
      quittingTerminalPayoff reward profile other

/-- The explicit gain floor delivered by reached-row localization. -/
def quittingStoppingLawPositiveCollisionReachedRowGainFloor
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (lower : Real) : Real :=
  lower * quittingTerminalSemanticDebtSum frontier.base /
    (2 * ((Finset.univ.erase packet.observer).card : Real))

/-- A self-contained quantitative reached-row certificate for the
positive-collision packet.  Along one strict subsequence, the same target
profiles have a uniformly reached sure-Quit row and one fixed non-observer's
canonical legal gain is bounded below by the displayed positive floor. -/
def HasQuittingStoppingLawPositiveCollisionReachedRowLocalization
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (lower : Real) : Prop :=
  0 < lower ∧
    ∃ (stop : Nat -> Nat) (subseq : Nat -> Nat) (other : iota),
      StrictMono subseq ∧ other ≠ packet.observer ∧
      (∀ rank, packet.quitTime (subseq rank) = some (stop (subseq rank))) ∧
      (∀ rank, lower <= quittingStageCoalitionMass reward
        (quittingStoppingLawPositiveCollisionReachedRowProfile packet
          (subseq rank)) (stop (subseq rank)) packet.terminal) ∧
      ∀ rank,
        quittingStoppingLawPositiveCollisionReachedRowGainFloor packet lower <=
          quittingStoppingLawPositiveCollisionReachedRowGain packet stop other
            (subseq rank)

/-- The quantitative certificate implies nonconvergence of the fixed
player's full canonical gain sequence.  This is a mathematical projection:
it uses the positive gain floor on the stored strict subsequence. -/
theorem HasQuittingStoppingLawPositiveCollisionReachedRowLocalization.exists_gain_not_tendsto_zero
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    {lower : Real}
    (certificate :
      HasQuittingStoppingLawPositiveCollisionReachedRowLocalization
        packet lower) :
    ∃ (stop : Nat -> Nat) (other : iota), other ≠ packet.observer ∧
      ¬ Tendsto
        (quittingStoppingLawPositiveCollisionReachedRowGain packet stop other)
        atTop (nhds 0) := by
  obtain ⟨hlower, stop, subseq, other, hsubseq, hother, _htime, _hmass,
      hgain⟩ := certificate
  have hplayers : (Finset.univ.erase packet.observer).Nonempty :=
    ⟨other, Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩⟩
  have hcard : 0 < ((Finset.univ.erase packet.observer).card : Real) := by
    exact_mod_cast Finset.card_pos.mpr hplayers
  have hgainFloor : 0 <
      quittingStoppingLawPositiveCollisionReachedRowGainFloor packet lower := by
    unfold quittingStoppingLawPositiveCollisionReachedRowGainFloor
    exact div_pos (mul_pos hlower frontier.base_positive)
      (mul_pos (by norm_num) hcard)
  refine ⟨stop, other, hother, ?_⟩
  exact Math.not_tendsto_zero_of_positive_lower_bound_on_strict_subsequence
    (quittingStoppingLawPositiveCollisionReachedRowGain packet stop other)
      subseq _ hsubseq hgainFloor hgain

/-- The positive-collision marked-tail predicate already supplies the named
literal reached-row localization.  Its stored tail cluster and escape/fiber
alternative are not needed for this consumer. -/
theorem positiveCollisionMarkedTailDispatch_reachedRowLocalization
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    {lower : Real} (hlower : 0 < lower)
    (dispatch : HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch
      packet lower) :
    HasQuittingStoppingLawPositiveCollisionReachedRowLocalization
      packet lower := by
  unfold HasQuittingStoppingLawPositiveCollisionReachedRowLocalization
  obtain ⟨stop, _cluster, baseSubseq, _hcluster, hbaseSubseq, hfinite,
      hmass, _htail, _hmarked, _hdispatch⟩ := dispatch
  have hready := hfinite.and hmass
  obtain ⟨start, hstart⟩ := eventually_atTop.1 hready
  let shifted : Nat -> Nat := fun n => start + n
  have hshifted : StrictMono shifted := fun _ _ hlt =>
    Nat.add_lt_add_left hlt start
  let subseq : Nat -> Nat := fun n => baseSubseq (shifted n)
  have hsubseq : StrictMono subseq := hbaseSubseq.comp hshifted
  let profile : Nat -> (quittingGame reward).BehaviorProfile := fun n =>
    quittingStoppingLawPositiveCollisionReachedRowProfile packet (subseq n)
  let stage : Nat -> Nat := fun n => stop (subseq n)
  have htime : ∀ n,
      packet.quitTime (subseq n) = some (stage n) := by
    intro n
    exact (hstart (shifted n) (Nat.le_add_right start n)).1
  have hstageMass : ∀ n, lower <=
      quittingStageCoalitionMass reward (profile n) (stage n)
        packet.terminal := by
    intro n
    exact (hstart (shifted n) (Nat.le_add_right start n)).2
  have hsure : ∀ n,
      quittingProfileLiveRoot reward (profile n) (stage n) packet.observer =
        PMF.pure true := by
    intro n
    dsimp only [profile,
      quittingStoppingLawPositiveCollisionReachedRowProfile]
    rw [quittingProfileLiveRoot_update_pureTime_self, htime n,
      quittingPureTimeHazard_some_self]
  have hdebt : Tendsto (fun n =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profile n)) packet.observer)
      atTop (nhds 0) := by
    have hcomp :=
      packet.observer_debt_tendsto_zero.comp hsubseq.tendsto_atTop
    simpa only [profile,
      quittingStoppingLawPositiveCollisionReachedRowProfile, subseq,
      quittingStoppingLawRectangleTargetProfile, Function.comp_def] using hcomp
  have hminimum : ∀ n, quittingTerminalSemanticDebtSum frontier.base <=
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward (profile n) (stage n))) := by
    intro n
    exact frontier.base_minimum _
      (quittingTerminalSemanticPair_mem_carrier reward _)
  have hreach : ∀ n, lower <=
      quittingLiveMass reward (profile n) (stage n) := by
    intro n
    exact (hstageMass n).trans
      (quittingStageCoalitionMass_le_liveMass reward (profile n) (stage n)
        packet.terminal)
  obtain ⟨other, gainSubseq, hother, hgainSubseq, hgain⟩ :=
    exists_fixed_other_reachedRowGain_subsequence reward
      (quittingTerminalSemanticDebtSum frontier.base) frontier.base_positive
      profile stage packet.observer lower hminimum hlower hreach hsure hdebt
  let finalSubseq : Nat -> Nat := fun n => subseq (gainSubseq n)
  have hfinalSubseq : StrictMono finalSubseq :=
    hsubseq.comp hgainSubseq
  refine ⟨hlower, stop, finalSubseq, other, hfinalSubseq, hother, ?_, ?_, ?_⟩
  · intro rank
    simpa only [finalSubseq, stage] using htime (gainSubseq rank)
  · intro rank
    simpa only [finalSubseq, profile, stage] using
      hstageMass (gainSubseq rank)
  · intro rank
    simpa only [quittingStoppingLawPositiveCollisionReachedRowGainFloor,
      quittingStoppingLawPositiveCollisionReachedRowGain,
      quittingStoppingLawPositiveCollisionReachedRowProfile, finalSubseq,
      profile, stage] using hgain rank

/-- **Canonical `SL-POS-COLLISION` adapter.**  The exact marked-tail dispatch
stored by the five-way positive-collision branch yields the quantitative
reached-row certificate at its canonical mass lower bound.  No terminal
membership, collision-cardinality, or reward-sign premise is needed here:
the dispatch is already supplied, while positivity of the lower bound follows
from the packet's positive charge and positive reward bound. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.slPositiveCollision_reachedRowLocalization
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (dispatch : HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch packet
      ((packet.charge / 4) /
        ((Fintype.card (QuittingTerminalOutcome iota) : Real) *
          quittingRewardBound reward))) :
    HasQuittingStoppingLawPositiveCollisionReachedRowLocalization packet
      ((packet.charge / 4) /
        ((Fintype.card (QuittingTerminalOutcome iota) : Real) *
          quittingRewardBound reward)) := by
  apply positiveCollisionMarkedTailDispatch_reachedRowLocalization
    packet ?_ dispatch
  exact div_pos (div_pos packet.charge_pos (by norm_num))
    (mul_pos (by positivity) packet.rewardBound_pos)

end GameTheory
