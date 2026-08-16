/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.PureTimeDispatch

/-!
# Three-way stopping-law localization

Every stopping-law frontier has a self-oriented pure-time atom sequence.  Its
fixed terminal label lies in exactly one of the owner-absent, negative
owner-containing, or positive owner-containing consumers.  The prescribed
payoff-comparison branch is not part of this exhaustive localization.
-/

noncomputable section

namespace GameTheory

open Filter Set StochasticGame Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
/-! ## Self-oriented adapters to the three consumers -/

/-- The untouched opponents behind the two pure-time owner endpoints. -/
def quittingStoppingLawSelfOrientedBaseProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  frontier.profiles (frontier.subseq (packet.rank n))

/-- The reward sign selects the target pure time for positive reward and the
source pure time for negative reward. -/
def quittingStoppingLawSelfOrientedCarrierQuitTime
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier)
    (n : ℕ) : Option ℕ :=
  if 0 < reward packet.terminal packet.owner.1 then
    packet.targetQuitTime n
  else packet.sourceQuitTime n

/-- The sign-selected carrier is the corresponding pure-time endpoint. -/
def quittingStoppingLawSelfOrientedCarrierProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingPureTimeCarrierProfile reward
    (quittingStoppingLawSelfOrientedBaseProfile packet) packet.owner.1
    (quittingStoppingLawSelfOrientedCarrierQuitTime packet) n

/-- The sign-selected carrier retains the canonical terminal mass floor. -/
theorem QuittingStoppingLawSelfOrientedAtomSequence.carrier_massLower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier) (n : ℕ) :
    quittingStoppingLawSelfOrientedMassLower packet ≤
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawSelfOrientedCarrierProfile packet n)
        (some packet.terminal) := by
  by_cases hpositive : 0 < reward packet.terminal packet.owner.1
  · simpa only [quittingStoppingLawSelfOrientedCarrierProfile,
      quittingStoppingLawSelfOrientedCarrierQuitTime, if_pos hpositive,
      quittingPureTimeCarrierProfile,
      quittingStoppingLawSelfOrientedBaseProfile,
      quittingStoppingLawSelfOrientedTargetProfile] using
      packet.positiveTarget_massLower hpositive n
  · have hnegative : reward packet.terminal packet.owner.1 < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpositive) packet.reward_ne_zero
    simpa only [quittingStoppingLawSelfOrientedCarrierProfile,
      quittingStoppingLawSelfOrientedCarrierQuitTime, if_neg hpositive,
      quittingPureTimeCarrierProfile,
      quittingStoppingLawSelfOrientedBaseProfile,
      quittingStoppingLawSelfOrientedSourceProfile] using
      packet.negativeSource_massLower hnegative n

/-- The owner-absent self-oriented atom reaches the generic forced-owner wall.
-/
theorem QuittingStoppingLawSelfOrientedAtomSequence.observerAbsent_dispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier)
    (habsent : packet.owner.1 ∉ packet.terminal.val) :
    HasQuittingPureTimeObserverAbsentForcedOwnerDispatch
      (regime := regime) (quittingStoppingLawSelfOrientedBaseProfile packet)
      packet.owner.1 (quittingStoppingLawSelfOrientedCarrierQuitTime packet)
      packet.terminal (quittingStoppingLawSelfOrientedMassLower packet) := by
  apply pureTimeObserverAbsent_forcedOwnerDispatch
  · exact habsent
  · exact packet.massLower_pos
  · intro n
    simpa only [quittingStoppingLawSelfOrientedCarrierProfile] using
      packet.carrier_massLower n

/-- The negative owner-containing self-oriented atom reaches the actual
source-row atomic dispatch. -/
theorem QuittingStoppingLawSelfOrientedAtomSequence.negativeTarget_dispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier)
    (howner : packet.owner.1 ∈ packet.terminal.val)
    (hnegative : reward packet.terminal packet.owner.1 < 0) :
    HasQuittingPureTimeNegativeTargetAtomicDispatch
      (regime := regime) (quittingStoppingLawSelfOrientedBaseProfile packet)
      packet.owner.1 packet.sourceQuitTime packet.terminal
      (quittingStoppingLawSelfOrientedMassLower packet) := by
  apply pureTimeNegativeTarget_atomicDispatch
  · exact howner
  · exact packet.massLower_pos
  · intro n
    simpa only [quittingPureTimeCarrierProfile,
      quittingStoppingLawSelfOrientedBaseProfile,
      quittingStoppingLawSelfOrientedSourceProfile] using
      packet.negativeSource_massLower hnegative n

/-- The positive owner-containing self-oriented atom reaches a sure-Quit row
with vanishing owner debt and hence a fixed outsider gain. -/
theorem QuittingStoppingLawSelfOrientedAtomSequence.positiveTarget_dispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier)
    (howner : packet.owner.1 ∈ packet.terminal.val)
    (hpositive : 0 < reward packet.terminal packet.owner.1) :
    HasQuittingPureTimePositiveTargetReachedRowLocalization frontier
      (quittingStoppingLawSelfOrientedBaseProfile packet) packet.owner.1
      packet.targetQuitTime packet.terminal
      (quittingStoppingLawSelfOrientedMassLower packet) := by
  let lower := quittingStoppingLawSelfOrientedMassLower packet
  have hlower : 0 < lower := packet.massLower_pos
  have hpersistent : ∀ᶠ n in atTop, lower ≤
      quittingTerminalOutcomeMass reward
        (quittingPureTimeCarrierProfile reward
          (quittingStoppingLawSelfOrientedBaseProfile packet) packet.owner.1
          packet.targetQuitTime n) (some packet.terminal) := by
    apply Eventually.of_forall
    intro n
    simpa only [lower, quittingPureTimeCarrierProfile,
      quittingStoppingLawSelfOrientedBaseProfile,
      quittingStoppingLawSelfOrientedTargetProfile] using
      packet.positiveTarget_massLower hpositive n
  have hdebt : Tendsto (fun n =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingPureTimeCarrierProfile reward
            (quittingStoppingLawSelfOrientedBaseProfile packet) packet.owner.1
            packet.targetQuitTime n)) packet.owner.1) atTop (nhds 0) := by
    simpa only [quittingPureTimeCarrierProfile,
      quittingStoppingLawSelfOrientedBaseProfile,
      quittingStoppingLawSelfOrientedTargetProfile] using
      packet.target_debt_tendsto_zero
  obtain ⟨stop, hfinite, hmass, _hmarkedDefect⟩ :=
    exists_stops_tendsto_coordinateNashDefect_zero_of_persistent_collision
      reward (quittingStoppingLawSelfOrientedBaseProfile packet) packet.owner.1
      packet.targetQuitTime packet.terminal howner hlower hdebt hpersistent
  exact pureTimePositiveTargetReachedRowLocalization_of_eventually_stop_mass
    frontier (quittingStoppingLawSelfOrientedBaseProfile packet) packet.owner.1
      packet.targetQuitTime packet.terminal hlower stop id strictMono_id
      (by simpa only using hfinite)
      (by simpa only [quittingPureTimeCarrierProfile,
        quittingPureTimeUpdatedProfile] using hmass) hdebt

/-! ## Canonical three-way localization -/

/-- The three remaining signed/geometric stopping-law leaves. -/
def HasQuittingStoppingLawThreeWayLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) : Prop :=
  (∃ packet : QuittingStoppingLawSelfOrientedAtomSequence frontier,
    packet.owner.1 ∉ packet.terminal.val ∧
      HasQuittingPureTimeObserverAbsentForcedOwnerDispatch
        (regime := regime) (quittingStoppingLawSelfOrientedBaseProfile packet)
        packet.owner.1 (quittingStoppingLawSelfOrientedCarrierQuitTime packet)
        packet.terminal (quittingStoppingLawSelfOrientedMassLower packet)) ∨
  (∃ packet : QuittingStoppingLawSelfOrientedAtomSequence frontier,
    packet.owner.1 ∈ packet.terminal.val ∧
      reward packet.terminal packet.owner.1 < 0 ∧
      HasQuittingPureTimeNegativeTargetAtomicDispatch
        (regime := regime) (quittingStoppingLawSelfOrientedBaseProfile packet)
        packet.owner.1 packet.sourceQuitTime packet.terminal
        (quittingStoppingLawSelfOrientedMassLower packet)) ∨
  ∃ packet : QuittingStoppingLawSelfOrientedAtomSequence frontier,
    packet.owner.1 ∈ packet.terminal.val ∧
      0 < reward packet.terminal packet.owner.1 ∧
      HasQuittingPureTimePositiveTargetReachedRowLocalization frontier
        (quittingStoppingLawSelfOrientedBaseProfile packet) packet.owner.1
        packet.targetQuitTime packet.terminal
        (quittingStoppingLawSelfOrientedMassLower packet)

namespace QuittingCounterexampleStoppingLawFrontier

/-- **Three-way exhaustive stopping-law localization.**  Every counterexample
frontier supplies one self-oriented pure-time atom packet in exactly one of
the owner-absent, negative owner-containing, or positive owner-containing
consumers.  No prescribed-payoff atom branch remains. -/
theorem threeWayLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    HasQuittingStoppingLawThreeWayLocalization frontier := by
  classical
  obtain ⟨packet⟩ := frontier.nonempty_selfOrientedAtomSequence
  by_cases howner : packet.owner.1 ∈ packet.terminal.val
  · by_cases hpositive : 0 < reward packet.terminal packet.owner.1
    · exact Or.inr (Or.inr ⟨packet, howner, hpositive,
        packet.positiveTarget_dispatch howner hpositive⟩)
    · have hnegative : reward packet.terminal packet.owner.1 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpositive) packet.reward_ne_zero
      exact Or.inr (Or.inl ⟨packet, howner, hnegative,
        packet.negativeTarget_dispatch howner hnegative⟩)
  · exact Or.inl ⟨packet, howner, packet.observerAbsent_dispatch howner⟩

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
