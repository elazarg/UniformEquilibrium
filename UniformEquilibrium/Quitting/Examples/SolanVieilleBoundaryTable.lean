/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ImmediateSingletonCollision
import UniformEquilibrium.Quitting.Classification.PreemptionCycle
import UniformEquilibrium.Quitting.Classification.SoloExitPreference

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

The table also satisfies both assumptions of the source's own existence
theorem: unit solo exit and capped joint exit.  Its approximate equilibrium is
therefore an instance of that theorem and not evidence against it.

The checked companion modules separate the strategic conclusions cleanly.
`SolanVieilleBoundaryEquilibrium` constructs an exact period-two equilibrium,
while `SolanVieilleBoundaryNonstationarity` proves that sufficiently accurate
terminal approximate equilibria are neither stationary nor uniformly close
to all-Continue at every stage.  This module owns only the table and its
collision/preemption geometry.

-/

noncomputable section

namespace GameTheory

namespace SolanVieilleBoundary

abbrev Player := Fin 4

/-- The paired player in the boundary table: `0 ↔ 1` and `2 ↔ 3`. -/
def boundaryPartner : Player → Player := ![1, 0, 3, 2]

/-- One canonical player in the pair opposite to the supplied player. -/
def boundaryOppositeFirst : Player → Player := ![2, 2, 0, 0]

/-- The other player in the pair opposite to the supplied player. -/
def boundaryOppositeSecond : Player → Player := ![3, 3, 1, 1]

@[simp] theorem boundaryPartner_ne (who : Player) : boundaryPartner who ≠ who := by
  fin_cases who <;> decide

@[simp] theorem boundaryPartner_partner (who : Player) :
    boundaryPartner (boundaryPartner who) = who := by
  fin_cases who <;> rfl

@[simp] theorem boundaryPartner_val_div_two (who : Player) :
    (boundaryPartner who).val / 2 = who.val / 2 := by
  fin_cases who <;> rfl

@[simp] theorem boundaryOppositeFirst_ne (who : Player) :
    boundaryOppositeFirst who ≠ who := by
  fin_cases who <;> decide

@[simp] theorem boundaryPartner_oppositeFirst (who : Player) :
    boundaryPartner (boundaryOppositeFirst who) = boundaryOppositeSecond who := by
  fin_cases who <;> rfl

@[simp] theorem boundaryPartner_oppositeSecond (who : Player) :
    boundaryPartner (boundaryOppositeSecond who) = boundaryOppositeFirst who := by
  fin_cases who <;> rfl

/-- The Solan–Vieille Section 3 reward table, presented by membership
pattern: the four Booleans record which of the players `0, 1, 2, 3` belong to
the quitting coalition.  Each of the fifteen nonempty coalitions carries an
explicit row.  The all-Continue pattern cannot occur on the
nonempty-coalition subtype and is filled with zeros. -/
def boundaryReward (quitters : {S : Finset Player // S.Nonempty}) :
    Payoff Player :=
  match decide (0 ∈ quitters.1), decide (1 ∈ quitters.1),
      decide (2 ∈ quitters.1), decide (3 ∈ quitters.1) with
  | true, false, false, false => ![1, 4, 0, 0]
  | false, true, false, false => ![4, 1, 0, 0]
  | false, false, true, false => ![0, 0, 1, 4]
  | false, false, false, true => ![0, 0, 4, 1]
  | true, true, false, false => ![1, 1, 1, 1]
  | true, false, true, false => ![1, 1, 1, 0]
  | true, false, false, true => ![1, 0, 1, 1]
  | false, true, true, false => ![0, 1, 1, 1]
  | false, true, false, true => ![1, 1, 0, 1]
  | false, false, true, true => ![1, 1, 1, 1]
  | true, true, true, false => ![1, 0, 0, 0]
  | true, true, false, true => ![0, 1, 0, 0]
  | true, false, true, true => ![0, 0, 0, 1]
  | false, true, true, true => ![0, 0, 1, 0]
  | true, true, true, true => ![-1, -1, -1, -1]
  | false, false, false, false => ![0, 0, 0, 0]

/-- Closed form of the sixteen singleton entries: a solo quitter pays itself
`1`, its own-pair partner `4`, and the opposite pair `0`. -/
@[simp] theorem soloReward_eval (owner who : Player) :
    quittingSoloReward boundaryReward owner who =
      if owner = who then 1
      else if owner.val / 2 = who.val / 2 then 4
      else 0 := by
  fin_cases owner <;> fin_cases who <;> rfl

/-- Every two-player exit pays each displayed member exactly `1`. -/
theorem boundaryReward_pair_eq_one (owner who : Player) :
    boundaryReward ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who = 1 := by
  fin_cases owner <;> fin_cases who <;> rfl

/-- A solo exit pays the canonical opposite-pair player `0`. -/
theorem boundaryReward_solo_oppositeFirst (owner : Player) :
    boundaryReward (quittingSingletonTerminal owner)
      (boundaryOppositeFirst owner) = 0 := by
  fin_cases owner <;> rfl

/-- A solo exit pays its distinct own-pair partner `4`. -/
theorem boundaryReward_solo_partner {owner who : Player}
    (hne : owner ≠ who) (hpair : owner.val / 2 = who.val / 2) :
    boundaryReward (quittingSingletonTerminal owner) who = 4 := by
  have h := soloReward_eval owner who
  rw [if_neg hne, if_pos hpair] at h
  exact h

/-- A solo exit pays every member of the opposite pair `0`. -/
theorem boundaryReward_solo_cross {owner who : Player}
    (hpair : owner.val / 2 ≠ who.val / 2) :
    boundaryReward (quittingSingletonTerminal owner) who = 0 := by
  have hne : owner ≠ who := fun h ↦ hpair (by rw [h])
  have h := soloReward_eval owner who
  rw [if_neg hne, if_neg hpair] at h
  exact h

@[simp] theorem collisionReward_zero_two :
    quittingSingletonCollisionReward boundaryReward 0 2 = 1 := rfl

/-- Every player's solo exit pays itself exactly `1`. -/
@[simp] theorem soloReward_self (owner : Player) :
    quittingSoloReward boundaryReward owner owner = 1 := by
  simp

/-- Every player's own solo exit pays it exactly `1`. -/
theorem boundaryReward_unitSoloExit : QuittingUnitSoloExit boundaryReward :=
  soloReward_self

/-- No member of a quitting coalition is paid more than `1`.  The only entries
above `1` are the value `4` paid to the partner of a solo quitter, and that
partner is not a member of the quitting coalition. -/
theorem boundaryReward_cappedJointExit :
    QuittingCappedJointExit boundaryReward := by
  intro quitters who
  fin_cases quitters <;> fin_cases who <;> simp [boundaryReward]

/-- Every player weakly prefers its own solo exit to every joint exit it takes
part in. -/
theorem boundaryReward_weakSoloExitPreference :
    QuittingWeakSoloExitPreference boundaryReward :=
  quittingWeakSoloExitPreference_of_unitSoloExit boundaryReward_unitSoloExit
    boundaryReward_cappedJointExit

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
