/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Packet
import UniformEquilibrium.Quitting.Classification.SingletonPacketRefusal

/-!
# Strict refusal in a counterexample packet

A counterexample cannot carry a packet complementary on its active support,
because the singleton-mixture compiler would produce a uniform-equilibrium
payoff. Hence some active owner has strict packet surplus, and the generic
refusal identity turns that surplus into a strict conditional refusal gain.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleRegime

/-- **Strict packet surplus.**  The packet forced by a counterexample regime
has an active owner whose delivered singleton mixture strictly exceeds its
pinned target.  Otherwise it is a complementary singleton mixture and the
existing circulation compiler produces a uniform-equilibrium payoff. -/
theorem exists_active_strictSingletonSurplus
    (regime : QuittingCounterexampleRegime reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∃ owner, 0 < packet.mass owner ∧
      packet.target owner <
        quittingSingletonMixture reward packet.mass owner := by
  letI : Nonempty ι := regime.nonempty_players
  by_contra hstrict
  push Not at hstrict
  have hactive : ∀ owner, 0 < packet.mass owner →
      quittingSingletonMixture reward packet.mass owner =
        reward (quittingSingletonTerminal owner) owner := by
    intro owner howner
    have heq : packet.target owner =
        quittingSingletonMixture reward packet.mass owner :=
      le_antisymm (packet.mix_ge_target owner)
        (hstrict owner howner)
    rw [← heq, packet.positive_mass_pins_target owner howner]
  obtain ⟨payoff, hpayoff⟩ :=
    exists_uniformEquilibriumPayoff_of_complementarySingletonMixture
      reward packet.mass packet.target packet.mass_nonneg packet.mass_sum
        packet.mix_ge_target hactive packet.solo_le_target
        packet.punishment_le_target
  exact regime.not_exists_uniformEquilibriumPayoff ⟨payoff, hpayoff⟩

/-- **Strict packet refusal.**  One positive-mass owner strictly prefers the
singleton delivery conditioned on refusing its own prescribed atom to both
the packet target and the unconditioned delivery.  The selected atom
necessarily has mass strictly below one. -/
theorem exists_active_strictSingletonRefusal
    (regime : QuittingCounterexampleRegime reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∃ owner, 0 < packet.mass owner ∧ packet.mass owner < 1 ∧
      packet.target owner < quittingSingletonMixture reward packet.mass owner ∧
      quittingSingletonMixture reward packet.mass owner <
        quittingSingletonRefusalValue reward packet.mass owner owner := by
  obtain ⟨owner, howner, hsurplus⟩ :=
    regime.exists_active_strictSingletonSurplus packet
  have hmass : packet.mass owner < 1 := by
    apply lt_of_le_of_ne (packet.mass_le_one owner)
    intro heq
    rw [packet.singletonMixture_eq_singleton_of_mass_eq_one heq owner,
      ← packet.positive_mass_pins_target owner howner] at hsurplus
    exact (lt_irrefl _ hsurplus)
  have hpinned := packet.positive_mass_pins_target owner howner
  have hsplit := packet.singletonMixture_eq_mass_mul_add_refusal hmass owner
  rw [← hpinned] at hsplit
  refine ⟨owner, howner, hmass, hsurplus, ?_⟩
  nlinarith

end QuittingCounterexampleRegime

end GameTheory
