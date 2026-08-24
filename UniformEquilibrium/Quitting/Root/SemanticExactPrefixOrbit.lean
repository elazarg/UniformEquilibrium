/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefix
import UniformEquilibrium.Quitting.Root.NashExistence
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-!
# Exact semantic prefix orbits from an arbitrary carrier source

Finite mixed Nash existence selects one exact root at the prescribed payoff of
each current semantic pair.  Recursively prefixing those selected roots gives
an actual carrier-preserving semantic orbit.  If the initial payoff lies above
the behavioral punishment floor, every finite truncation is a certified
punishment-floor prefix.

This is only a canonical choice of roots.  Results stated for an arbitrary
`QuittingPunishmentFloorFinitePrefix` remain universal over other selections.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One classically selected exact product Nash root at a semantic pair's
prescribed coordinate. -/
def quittingTerminalSemanticSelectedExactRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) : ι → PMF Bool :=
  Classical.choose (exists_isZeroQuittingRootNash (reward := reward) pair.1)

theorem quittingTerminalSemanticSelectedExactRoot_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) :
    IsεQuittingRootNash reward pair.1 0
      (quittingTerminalSemanticSelectedExactRoot reward pair) :=
  Classical.choose_spec (exists_isZeroQuittingRootNash (reward := reward) pair.1)

/-- Infinite semantic orbit obtained by repeatedly prefixing the selected exact
root at the current prescribed payoff. -/
def quittingTerminalSemanticExactPrefixOrbit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) :
    ℕ → QuittingTerminalSemanticPair ι
  | 0 => source
  | time + 1 =>
      let current := quittingTerminalSemanticExactPrefixOrbit reward source time
      quittingTerminalSemanticPrefix reward
        (quittingTerminalSemanticSelectedExactRoot reward current) current

@[simp] theorem quittingTerminalSemanticExactPrefixOrbit_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) :
    quittingTerminalSemanticExactPrefixOrbit reward source 0 = source := rfl

theorem quittingTerminalSemanticExactPrefixOrbit_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) :
    quittingTerminalSemanticExactPrefixOrbit reward source (time + 1) =
      quittingTerminalSemanticPrefix reward
        (quittingTerminalSemanticSelectedExactRoot reward
          (quittingTerminalSemanticExactPrefixOrbit reward source time))
        (quittingTerminalSemanticExactPrefixOrbit reward source time) := rfl

theorem quittingTerminalSemanticExactPrefixOrbit_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward) (time : ℕ) :
    quittingTerminalSemanticExactPrefixOrbit reward source time ∈
      quittingTerminalSemanticCarrier reward := by
  induction time with
  | zero => exact hsource
  | succ time ih =>
      rw [quittingTerminalSemanticExactPrefixOrbit_succ]
      exact quittingTerminalSemanticPrefix_mem_carrier reward _ _ ih

/-- Finite truncation of the selected exact semantic prefix orbit. -/
def quittingTerminalSemanticExactFinitePrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤ source.1 who)
    (horizon : ℕ) : QuittingPunishmentFloorFinitePrefix reward where
  roots time := quittingTerminalSemanticSelectedExactRoot reward
    (quittingTerminalSemanticExactPrefixOrbit reward source time)
  value time := (quittingTerminalSemanticExactPrefixOrbit reward source time).1
  horizon := horizon
  value_mem := by
    intro time _
    have hpair := quittingTerminalSemanticExactPrefixOrbit_mem_carrier
      reward source hsource time
    have hbox := quittingTerminalSemanticCarrier_mem_box reward _
      (abs_reward_le_quittingRewardBound reward) hpair
    exact hbox.1
  anchor_floor := hfloor
  policy := by
    intro time _
    rw [quittingTerminalSemanticExactPrefixOrbit_succ]
    rfl
  exactNash := by
    intro time _
    exact quittingTerminalSemanticSelectedExactRoot_isZeroNash reward _

@[simp] theorem quittingTerminalSemanticExactFinitePrefix_value_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤ source.1 who)
    (horizon : ℕ) :
    (quittingTerminalSemanticExactFinitePrefix reward source hsource hfloor
      horizon).value 0 = source.1 := rfl

end GameTheory
