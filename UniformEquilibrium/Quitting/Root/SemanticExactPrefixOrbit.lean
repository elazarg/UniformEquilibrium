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

/-- Infinite semantic prefix orbit driven by an arbitrary root selector.  Nash
properties of the selector are intentionally separate from this recursion. -/
def quittingTerminalSemanticSelectorPrefixOrbit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (selector : QuittingTerminalSemanticPair ι → ι → PMF Bool)
    (source : QuittingTerminalSemanticPair ι) :
    ℕ → QuittingTerminalSemanticPair ι
  | 0 => source
  | time + 1 =>
      let current := quittingTerminalSemanticSelectorPrefixOrbit
        reward selector source time
      quittingTerminalSemanticPrefix reward
        (selector current) current

@[simp] theorem quittingTerminalSemanticSelectorPrefixOrbit_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (selector : QuittingTerminalSemanticPair ι → ι → PMF Bool)
    (source : QuittingTerminalSemanticPair ι) :
    quittingTerminalSemanticSelectorPrefixOrbit reward selector source 0 =
      source := rfl

theorem quittingTerminalSemanticSelectorPrefixOrbit_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (selector : QuittingTerminalSemanticPair ι → ι → PMF Bool)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) :
    quittingTerminalSemanticSelectorPrefixOrbit reward selector source
        (time + 1) =
      quittingTerminalSemanticPrefix reward
        (selector (quittingTerminalSemanticSelectorPrefixOrbit
          reward selector source time))
        (quittingTerminalSemanticSelectorPrefixOrbit
          reward selector source time) := rfl

theorem quittingTerminalSemanticSelectorPrefixOrbit_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (selector : QuittingTerminalSemanticPair ι → ι → PMF Bool)
    (source : QuittingTerminalSemanticPair ι)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward) (time : ℕ) :
    quittingTerminalSemanticSelectorPrefixOrbit reward selector source time ∈
      quittingTerminalSemanticCarrier reward := by
  induction time with
  | zero => exact hsource
  | succ time ih =>
      rw [quittingTerminalSemanticSelectorPrefixOrbit_succ]
      exact quittingTerminalSemanticPrefix_mem_carrier reward _ _ ih

/-- Selector-driven semantic prefixing is autonomous: restarting after a
finite prefix gives the same later orbit. -/
theorem quittingTerminalSemanticSelectorPrefixOrbit_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (selector : QuittingTerminalSemanticPair ι → ι → PMF Bool)
    (source : QuittingTerminalSemanticPair ι) (first second : ℕ) :
    quittingTerminalSemanticSelectorPrefixOrbit reward selector source
        (first + second) =
      quittingTerminalSemanticSelectorPrefixOrbit reward selector
        (quittingTerminalSemanticSelectorPrefixOrbit reward selector source
          first) second := by
  induction second with
  | zero => simp
  | succ second ih =>
      rw [Nat.add_succ,
        quittingTerminalSemanticSelectorPrefixOrbit_succ,
        quittingTerminalSemanticSelectorPrefixOrbit_succ, ih]

/-- The historical exact-prefix orbit is the generic orbit driven by the
classically selected exact root. -/
def quittingTerminalSemanticExactPrefixOrbit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) :
    ℕ → QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticSelectorPrefixOrbit reward
    (quittingTerminalSemanticSelectedExactRoot reward) source

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
      quittingTerminalSemanticCarrier reward :=
  quittingTerminalSemanticSelectorPrefixOrbit_mem_carrier
    reward (quittingTerminalSemanticSelectedExactRoot reward) source hsource time

theorem quittingTerminalSemanticExactPrefixOrbit_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (first second : ℕ) :
    quittingTerminalSemanticExactPrefixOrbit reward source (first + second) =
      quittingTerminalSemanticExactPrefixOrbit reward
        (quittingTerminalSemanticExactPrefixOrbit reward source first) second :=
  quittingTerminalSemanticSelectorPrefixOrbit_add reward
    (quittingTerminalSemanticSelectedExactRoot reward) source first second

/-- Finite punishment-floor prefix driven by a supplied exact-Nash selector.
This is the generic implementation behind the historical selected prefix. -/
def quittingTerminalSemanticSelectorFinitePrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (selector : QuittingTerminalSemanticPair ι → ι → PMF Bool)
    (hselector : ∀ pair, IsεQuittingRootNash reward pair.1 0 (selector pair))
    (source : QuittingTerminalSemanticPair ι)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤ source.1 who)
    (horizon : ℕ) : QuittingPunishmentFloorFinitePrefix reward where
  roots time := selector
    (quittingTerminalSemanticSelectorPrefixOrbit reward selector source time)
  value time :=
    (quittingTerminalSemanticSelectorPrefixOrbit reward selector source time).1
  horizon := horizon
  value_mem := by
    intro time _
    have hpair := quittingTerminalSemanticSelectorPrefixOrbit_mem_carrier
      reward selector source hsource time
    have hbox := quittingTerminalSemanticCarrier_mem_box reward _
      (abs_reward_le_quittingRewardBound reward) hpair
    exact hbox.1
  anchor_floor := hfloor
  policy := by
    intro time _
    rw [quittingTerminalSemanticSelectorPrefixOrbit_succ]
    rfl
  exactNash := by
    intro time _
    exact hselector _

/-- Finite truncation of the selected exact semantic prefix orbit. -/
def quittingTerminalSemanticExactFinitePrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤ source.1 who)
    (horizon : ℕ) : QuittingPunishmentFloorFinitePrefix reward :=
  quittingTerminalSemanticSelectorFinitePrefix reward
    (quittingTerminalSemanticSelectedExactRoot reward)
    (quittingTerminalSemanticSelectedExactRoot_isZeroNash reward)
    source hsource hfloor horizon

@[simp] theorem quittingTerminalSemanticExactFinitePrefix_value_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤ source.1 who)
    (horizon : ℕ) :
    (quittingTerminalSemanticExactFinitePrefix reward source hsource hfloor
      horizon).value 0 = source.1 := rfl

end GameTheory
