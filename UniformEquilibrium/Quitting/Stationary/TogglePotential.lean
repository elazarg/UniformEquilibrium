/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Coalition-toggle invariants and ordinal potentials

Pure sure-exit profiles form a finite coalition cube whose edges toggle one
player's membership.  This module owns the exact toggle operation, its finite
exploitability invariants, and the analogous stationary-cap infimum.

A natural-valued ordinal potential which increases on every profitable toggle
has a maximizing coalition.  That coalition is a sure exit set and therefore
produces a uniform-equilibrium payoff.  These constructions assume no
terminal exploitability witness.
-/

noncomputable section

namespace GameTheory

open Set
open QuittingSureSetOwnerRepair

variable {ι : Type} [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Toggle one player's membership in an exit coalition. -/
def quittingToggleCoalition (S : Finset ι) (who : ι) : Finset ι :=
  if who ∈ S then S.erase who else insert who S

@[simp] theorem quittingToggleCoalition_of_mem
    {S : Finset ι} {who : ι} (hwho : who ∈ S) :
    quittingToggleCoalition S who = S.erase who := by
  simp [quittingToggleCoalition, hwho]

@[simp] theorem quittingToggleCoalition_of_notMem
    {S : Finset ι} {who : ι} (hwho : who ∉ S) :
    quittingToggleCoalition S who = insert who S := by
  simp [quittingToggleCoalition, hwho]

/-- A membership toggle always changes the coalition. -/
theorem quittingToggleCoalition_ne (S : Finset ι) (who : ι) :
    quittingToggleCoalition S who ≠ S := by
  by_cases hwho : who ∈ S
  · rw [quittingToggleCoalition_of_mem hwho]
    exact Finset.erase_ne_self.mpr hwho
  · rw [quittingToggleCoalition_of_notMem hwho]
    exact Finset.insert_ne_self.mpr hwho

/-- Payoff improvement from toggling `who` at `S`. -/
def quittingPureToggleGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) : ℝ :=
  quittingSetReward reward (quittingToggleCoalition S who) who -
    quittingSetReward reward S who

variable [Fintype ι] [Nonempty ι]

/-- Best pure membership-toggle gain at one coalition. -/
def quittingPureToggleExploitability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (quittingPureToggleGain reward S)

/-- Minimum best pure-toggle gain over the finite coalition cube. -/
def quittingPureToggleCeiling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (quittingPureToggleExploitability reward)

/-- Best selected-cap gain at a stationary quitting root. -/
def quittingStationaryCapExploitability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun who =>
    quittingStationaryUnilateralCap reward root who -
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) who

/-- Infimum stationary selected-cap exploitability.  No attainment is built
into this definition. -/
def quittingStationaryCapCeiling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  sInf (Set.range (quittingStationaryCapExploitability reward))

/-! ## Ordinal-potential sufficient condition -/

/-- A natural-valued ordinal potential for pure coalition membership
toggles.  Only the sign of each strict payoff improvement is required. -/
def HasQuittingToggleOrdinalPotential
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ potential : Finset ι → ℕ,
    ∀ S who,
      quittingSetReward reward S who <
          quittingSetReward reward (quittingToggleCoalition S who) who →
        potential S < potential (quittingToggleCoalition S who)

omit [Fintype ι] [Nonempty ι] in
/-- A pure toggle ordinal potential produces a maximizing sure-exit
coalition. -/
theorem exists_sureExitSet_of_toggleOrdinalPotential
    [Finite ι]
    (hpotential : HasQuittingToggleOrdinalPotential reward) :
    ∃ S, IsQuittingSureExitSet reward S := by
  letI := Fintype.ofFinite ι
  obtain ⟨potential, hpotential⟩ := hpotential
  obtain ⟨S, -, hS⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty potential
  have hmax : ∀ T : Finset ι, potential T ≤ potential S := by
    intro T
    rw [← hS]
    exact Finset.le_sup' potential (Finset.mem_univ T)
  refine ⟨S, (isQuittingSureExitSet_iff_forall_max reward S).2 fun who => ?_⟩
  have htoggle : quittingSetReward reward
      (quittingToggleCoalition S who) who ≤ quittingSetReward reward S who := by
    by_contra hnot
    have himprove : quittingSetReward reward S who <
        quittingSetReward reward (quittingToggleCoalition S who) who :=
      lt_of_not_ge hnot
    exact (not_lt_of_ge (hmax _)) (hpotential S who himprove)
  by_cases hmem : who ∈ S
  · rw [quittingToggleCoalition_of_mem hmem] at htoggle
    rw [Finset.insert_eq_self.mpr hmem]
    exact max_le le_rfl htoggle
  · rw [quittingToggleCoalition_of_notMem hmem] at htoggle
    rw [Finset.erase_eq_of_notMem hmem]
    exact max_le htoggle le_rfl

omit [Nonempty ι] in
/-- Every quitting table with a pure membership-toggle ordinal potential has
a uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformPayoff_of_toggleOrdinalPotential
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpotential : HasQuittingToggleOrdinalPotential reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨S, hS⟩ := exists_sureExitSet_of_toggleOrdinalPotential hpotential
  exact ⟨quittingSetReward reward S,
    isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward hS⟩

end GameTheory
