/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.CollisionRepairScreen
import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.Support
import UniformEquilibrium.Quitting.Boundary.Repair.CollisionRateFiniteDispatch

/-!
# Finite collision dispatch for a two-owner singleton packet

For a supported blocker, packet pinning makes the rate-zero blocker defect
nonpositive.  Combining that fact with exact collision-rate elimination and
the terminal-exploitability collision screen turns every failed strict-sign
orientation into a literal profitable spectator join.

This is the generic-sign portion of the crossed support-two dispatch.  The
owner-indifference faces are already eliminated by the finite criterion in
`CollisionRateFiniteDispatch`; this module does not choose crossed spectators,
promote the resulting larger coalition, or construct a toggle cycle.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingNormalizedSingletonSourcePacket

/-- A positive-mass blocker has a nonpositive rate-zero blocker defect:
its packet-pinned singleton payoff lies above its exact punishment value. -/
theorem collisionConstraintLower_blocker_nonpos_of_mass_pos
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {owner blocker : ι} (hne : owner ≠ blocker)
    (hmass : 0 < packet.mass blocker) :
    quittingCollisionConstraintLower reward owner blocker
      (⟨blocker, Ne.symm hne⟩ : QuittingCollisionConstraintPlayer owner) ≤ 0 := by
  have hfloor := packet.punishment_le_target blocker
  rw [packet.positive_mass_pins_target blocker hmass] at hfloor
  rw [quittingCollisionConstraintLower, if_pos rfl]
  change quittingPunishmentValue reward blocker -
      reward (quittingSingletonTerminal blocker) blocker ≤ 0
  linarith

end QuittingNormalizedSingletonSourcePacket

namespace QuittingTerminalExploitabilityWitness

/-- If the owner strictly prefers the blocker singleton to the collision,
failure of every repair forces a spectator with a positive rate-zero join
defect. -/
theorem exists_spectator_lowerCollisionDefect_pos_of_ownerPair_lt
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {owner blocker : ι} (hne : owner ≠ blocker)
    (hblockerMass : 0 < packet.mass blocker)
    (hlt : quittingSetReward reward ({owner, blocker} : Finset ι) owner <
      quittingSetReward reward ({blocker} : Finset ι) owner) :
    ∃ spectator, spectator ≠ owner ∧ spectator ≠ blocker ∧
      quittingSetReward reward ({blocker} : Finset ι) spectator <
        quittingSetReward reward ({spectator, blocker} : Finset ι) spectator := by
  have hnotExists : ¬∃ (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1),
      QuittingCollisionRepairWorks reward owner blocker rate hrate0 hrate1 := by
    rintro ⟨rate, hrate0, hrate1, hworks⟩
    exact witness.not_quittingCollisionRepairWorks
      owner blocker rate hrate0 hrate1 hworks
  have hnotLower : ¬∀ index : QuittingCollisionConstraintPlayer owner,
      quittingCollisionConstraintLower reward owner blocker index ≤ 0 := by
    intro hlower
    exact hnotExists
      ((exists_quittingCollisionRepairWorks_iff_lower_of_owner_lt
        reward hne hlt).2 hlower)
  push Not at hnotLower
  obtain ⟨index, hindexPos⟩ := hnotLower
  have hindexBlocker : index.1 ≠ blocker := by
    intro heq
    have hfloor :=
      packet.collisionConstraintLower_blocker_nonpos_of_mass_pos
        hne hblockerMass
    have hsame : index =
        (⟨blocker, Ne.symm hne⟩ : QuittingCollisionConstraintPlayer owner) := by
      apply Subtype.ext
      exact heq
    rw [hsame] at hindexPos
    linarith
  refine ⟨index.1, index.2, hindexBlocker, ?_⟩
  rw [quittingCollisionConstraintLower, if_neg hindexBlocker] at hindexPos
  linarith

/-- If the owner strictly prefers the collision to the blocker singleton and
the rate-one blocker defect is nonpositive, failure of every repair forces a
spectator with a positive rate-one join defect. -/
theorem exists_spectator_upperCollisionDefect_pos_of_owner_lt
    (witness : QuittingTerminalExploitabilityWitness reward)
    {owner blocker : ι} (hne : owner ≠ blocker)
    (hlt : quittingSetReward reward ({blocker} : Finset ι) owner <
      quittingSetReward reward ({owner, blocker} : Finset ι) owner)
    (hblockerUpper : quittingSetReward reward ({owner} : Finset ι) blocker ≤
      quittingSetReward reward ({owner, blocker} : Finset ι) blocker) :
    ∃ spectator, spectator ≠ owner ∧ spectator ≠ blocker ∧
      quittingSetReward reward ({owner, blocker} : Finset ι) spectator <
        quittingSetReward reward
          ({owner, spectator, blocker} : Finset ι) spectator := by
  have hnotExists : ¬∃ (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1),
      QuittingCollisionRepairWorks reward owner blocker rate hrate0 hrate1 := by
    rintro ⟨rate, hrate0, hrate1, hworks⟩
    exact witness.not_quittingCollisionRepairWorks
      owner blocker rate hrate0 hrate1 hworks
  have hnotUpper : ¬∀ index : QuittingCollisionConstraintPlayer owner,
      quittingCollisionConstraintUpper reward owner blocker index ≤ 0 := by
    intro hupper
    exact hnotExists
      ((exists_quittingCollisionRepairWorks_iff_upper_of_owner_lt
        reward hne hlt).2 hupper)
  push Not at hnotUpper
  obtain ⟨index, hindexPos⟩ := hnotUpper
  have hindexBlocker : index.1 ≠ blocker := by
    intro heq
    have hsame : index =
        (⟨blocker, Ne.symm hne⟩ : QuittingCollisionConstraintPlayer owner) := by
      apply Subtype.ext
      exact heq
    rw [hsame, quittingCollisionConstraintUpper, if_pos rfl] at hindexPos
    linarith
  refine ⟨index.1, index.2, hindexBlocker, ?_⟩
  rw [quittingCollisionConstraintUpper, if_neg hindexBlocker] at hindexPos
  linarith

/-- **Generic crossed-support residual.**  For two supported owners, every
strict owner-sign chamber has the corresponding positive outsider join
defect.  The third clause uses the opposite owner's positive pair difference
to discharge the first orientation's rate-one blocker row.

The witnesses are not asserted distinct, and no `Fin 4` complement labeling
is used here. -/
theorem generic_supportPair_collisionDefects
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {first second : ι} (hne : first ≠ second)
    (hsupport : packet.support = {first, second}) :
    (quittingSetReward reward ({first, second} : Finset ι) first <
        quittingSetReward reward ({second} : Finset ι) first →
      ∃ spectator, spectator ≠ first ∧ spectator ≠ second ∧
        quittingSetReward reward ({second} : Finset ι) spectator <
          quittingSetReward reward ({spectator, second} : Finset ι) spectator) ∧
    (quittingSetReward reward ({first, second} : Finset ι) second <
        quittingSetReward reward ({first} : Finset ι) second →
      ∃ spectator, spectator ≠ second ∧ spectator ≠ first ∧
        quittingSetReward reward ({first} : Finset ι) spectator <
          quittingSetReward reward ({spectator, first} : Finset ι) spectator) ∧
    (quittingSetReward reward ({second} : Finset ι) first <
        quittingSetReward reward ({first, second} : Finset ι) first →
      quittingSetReward reward ({first} : Finset ι) second <
        quittingSetReward reward ({first, second} : Finset ι) second →
      ∃ spectator, spectator ≠ first ∧ spectator ≠ second ∧
        quittingSetReward reward ({first, second} : Finset ι) spectator <
          quittingSetReward reward
            ({first, spectator, second} : Finset ι) spectator) := by
  obtain ⟨hfirstMass, hsecondMass⟩ :=
    packet.mass_pos_of_support_eq_pair hsupport
  refine ⟨?_, ?_, ?_⟩
  · intro hfirst
    exact witness.exists_spectator_lowerCollisionDefect_pos_of_ownerPair_lt
      packet hne hsecondMass hfirst
  · intro hsecond
    have hsupportSwap : packet.support = {second, first} := by
      simpa only [Finset.pair_comm] using hsupport
    have hsecondSwap :
        quittingSetReward reward ({second, first} : Finset ι) second <
          quittingSetReward reward ({first} : Finset ι) second := by
      simpa only [Finset.pair_comm] using hsecond
    simpa only [Finset.pair_comm] using
      (witness.exists_spectator_lowerCollisionDefect_pos_of_ownerPair_lt
        packet hne.symm hfirstMass hsecondSwap)
  · intro hfirst hsecond
    exact witness.exists_spectator_upperCollisionDefect_pos_of_owner_lt
      hne hfirst hsecond.le

end QuittingTerminalExploitabilityWitness

end GameTheory
