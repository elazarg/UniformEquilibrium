/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ImmediateSingletonCollision
import UniformEquilibrium.Quitting.Classification.PreemptionCycle

/-!
# The Solan–Vieille boundary table realizes the frontier configuration

This module fixes the four-player quitting reward table of Solan and Vieille,
*Quitting games*, Math. Oper. Res. 26 (2001), Section 3, with players indexed
`0, 1, 2, 3` and nonabsorption payoff `0`, and checks that it realizes the
combined configuration of the reduced quitting conjecture at margin `1`:

* an executable immediate singleton collision (owner `0`, collider `2`); and
* a strict solo-preemption cycle of period two (`0 → 2 → 0`).

The strict preemption relation at margin `1` is moreover characterized
exactly: it is the complete bipartite digraph between the pairs `{0, 1}` and
`{2, 3}`.

The source paper proves that this table admits an approximate equilibrium
through a period-two two-quitter architecture, and admits neither a
stationary approximate equilibrium nor one in which at most one player quits
per stage.  None of those statements is checked here.  The checked content of
this module is only that explicit table data realizes the collision and
preemption-cycle geometry.  Any terminal-gap conclusion therefore requires
an additional checked argument beyond the realized configuration itself.

-/

noncomputable section

namespace GameTheory

namespace SolanVieilleBoundary

abbrev Player := Fin 4

/-- The Solan–Vieille Section 3 reward table.  Rows are indexed by the
quitting coalition; the final row is the grand coalition. -/
def boundaryReward (quitters : {S : Finset Player // S.Nonempty}) :
    Payoff Player :=
  if quitters.1 = {0} then ![1, 4, 0, 0]
  else if quitters.1 = {1} then ![4, 1, 0, 0]
  else if quitters.1 = {2} then ![0, 0, 1, 4]
  else if quitters.1 = {3} then ![0, 0, 4, 1]
  else if quitters.1 = {0, 1} then ![1, 1, 1, 1]
  else if quitters.1 = {0, 2} then ![1, 1, 1, 0]
  else if quitters.1 = {0, 3} then ![1, 0, 1, 1]
  else if quitters.1 = {1, 2} then ![0, 1, 1, 1]
  else if quitters.1 = {1, 3} then ![1, 1, 0, 1]
  else if quitters.1 = {2, 3} then ![1, 1, 1, 1]
  else if quitters.1 = {0, 1, 2} then ![1, 0, 0, 0]
  else if quitters.1 = {0, 1, 3} then ![0, 1, 0, 0]
  else if quitters.1 = {0, 2, 3} then ![0, 0, 0, 1]
  else if quitters.1 = {1, 2, 3} then ![0, 0, 1, 0]
  else ![-1, -1, -1, -1]

/-- Closed form of the sixteen singleton entries: a solo quitter pays itself
`1`, its own-pair partner `4`, and the opposite pair `0`. -/
@[simp] theorem soloReward_eval (owner who : Player) :
    quittingSoloReward boundaryReward owner who =
      if owner = who then 1
      else if owner.val / 2 = who.val / 2 then 4
      else 0 := by
  fin_cases owner <;> fin_cases who <;> rfl

@[simp] theorem collisionReward_zero_two :
    quittingSingletonCollisionReward boundaryReward 0 2 = 1 := rfl

/-- Every player's solo exit pays itself exactly `1`. -/
@[simp] theorem soloReward_self (owner : Player) :
    quittingSoloReward boundaryReward owner owner = 1 := by
  simp

/-- **The preemption digraph is complete bipartite.**  At margin `1`, `j`
strictly preempts `i` exactly when `i` and `j` lie in opposite pairs. -/
theorem soloPreempts_iff (i j : Player) :
    QuittingSoloPreempts boundaryReward 1 i j ↔
      ((i.val < 2 ∧ 2 ≤ j.val) ∨ (2 ≤ i.val ∧ j.val < 2)) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [QuittingSoloPreempts, Fin.ext_iff]

theorem soloPreempts_zero_two :
    QuittingSoloPreempts boundaryReward 1 0 2 :=
  (soloPreempts_iff 0 2).2 (Or.inl (by decide))

theorem soloPreempts_two_zero :
    QuittingSoloPreempts boundaryReward 1 2 0 :=
  (soloPreempts_iff 2 0).2 (Or.inr (by decide))

/-- Owner `0` and collider `2` realize the immediate singleton collision at
margin `1`. -/
def collisionCertificate :
    QuittingImmediateSingletonCollision boundaryReward 1 where
  owner := 0
  collider := 2
  collider_ne_owner := by decide
  owner_solo_floor := by
    show (1 : ℝ) ≤ quittingSoloReward boundaryReward 0 0
    simp
  collider_gain_floor := by
    show quittingSoloReward boundaryReward 0 2 + 1 ≤
      quittingSingletonCollisionReward boundaryReward 0 2
    norm_num [Fin.ext_iff]

/-- The alternating vertex sequence `0, 2, 0, 2, …`. -/
def cycleVertex (time : ℕ) : Player := if time % 2 = 0 then 0 else 2

/-- The strict solo-preemption two-cycle `0 → 2 → 0` at margin `1`. -/
def preemptionCycle : QuittingSoloPreemptionCycle boundaryReward 1 where
  period := 2
  period_pos := by norm_num
  vertex := cycleVertex
  vertex_periodic := by
    intro time
    simp [cycleVertex, Nat.add_mod_right]
  edge := by
    intro time
    rcases Nat.mod_two_eq_zero_or_one time with hmod | hmod
    · have hnext : (time + 1) % 2 = 1 := by omega
      simpa [cycleVertex, hmod, hnext] using soloPreempts_zero_two
    · have hnext : (time + 1) % 2 = 0 := by omega
      simpa [cycleVertex, hmod, hnext] using soloPreempts_two_zero

/-- **The reduced conjecture's combined configuration is realized.**  The
Solan–Vieille table carries both an immediate singleton collision and a
strict solo-preemption cycle at margin `1`. -/
theorem configuration_realized :
    Nonempty (QuittingImmediateSingletonCollision boundaryReward 1) ∧
      Nonempty (QuittingSoloPreemptionCycle boundaryReward 1) :=
  ⟨⟨collisionCertificate⟩, ⟨preemptionCycle⟩⟩

end SolanVieilleBoundary

end GameTheory
