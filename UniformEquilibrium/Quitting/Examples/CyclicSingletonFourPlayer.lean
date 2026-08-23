/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.CyclicSingletonTailProducer

/-!
# A four-player balanced singleton cycle

This file gives an exact four-player quitting reward outside the purely
stationary singleton construction and supplies a balanced singleton cycle for
it.  The existing balanced-cycle compiler then produces a uniform-equilibrium
payoff against arbitrary behavioral deviations.

The reward is specified on every nonempty quitting coalition.  Its singleton
columns, in player order, are

`(1,3,2,0)`, `(0,1,3,2)`, `(2,0,1,3)`, `(3,2,0,1)`.

For an adjacent pair `{k,k+1}`, the two members receive respectively `-5` and
`10`, while outsiders receive `-4`.  In every other nonsingleton coalition,
members receive `-5` and outsiders receive `-4`.
-/

noncomputable section

namespace GameTheory
namespace CyclicSingletonFourPlayer

abbrev Player := Fin 4

/-- Circulant singleton envies `(0,-1,1,2)`. -/
def envy : Player → ℝ := ![0, -1, 1, 2]

/-- The explicit four-player reward table described in the module docstring. -/
def reward (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  if terminal.1.card = 1 then
    fun who ↦ 1 + ∑ owner ∈ terminal.1, envy (owner - who)
  else if terminal.1 = {0, 1} then ![-5, 10, -4, -4]
  else if terminal.1 = {1, 2} then ![-4, -5, 10, -4]
  else if terminal.1 = {2, 3} then ![-4, -4, -5, 10]
  else if terminal.1 = {0, 3} then ![10, -4, -4, -5]
  else fun who => if who ∈ terminal.1 then -5 else -4

/-- The normalized cyclic tails `(0,0,2,2)` at survival one half. -/
def tail : Fin 4 → ℝ := ![0, 0, 2, 2]

private theorem fin4_neg_one : (-1 : Fin 4) = 3 := by decide

private theorem fin4_sub (a b : Fin 4) :
    a - b = ⟨(a.val + 4 - b.val) % 4, by omega⟩ := by
  apply Fin.ext
  simp [Fin.sub_def]
  omega

private theorem tail_neg_one : tail (-1 : Fin 4) = 2 := by
  rw [fin4_neg_one]
  change (2 : ℝ) = 2
  norm_num

private theorem envy_neg_one : envy (-1 : Fin 4) = 2 := by
  rw [fin4_neg_one]
  change (2 : ℝ) = 2
  norm_num

/-- The normalized singleton matrix is circulant with offsets
`(0,-1,1,2)`. -/
theorem singletonMatrix_eq (who phase : Fin 4) :
    QuittingLCPClassification.quittingSingletonMatrix reward who phase =
      envy (phase - who) := by
  simp [QuittingLCPClassification.quittingSingletonMatrix,
    reward, envy, Fin.sub_def]

/-- The example satisfies the reusable cyclic singleton tail recurrence. -/
def tailData : CyclicSingletonTailData reward where
  survival := 1 / 2
  tail := tail
  survival_pos := by norm_num
  survival_lt_one := by norm_num
  tail_zero := by norm_num [tail]
  tail_nonneg := by intro offset; fin_cases offset <;> norm_num [tail]
  recurrence := by
    intro phase who
    rw [singletonMatrix_eq]
    fin_cases phase <;>
    fin_cases who <;>
    norm_num [fin4_sub, tail_neg_one, envy_neg_one, tail, envy,
      finRotate_apply, Fin.sub_def, Fin.neg_def, Fin.add_def]
    all_goals first
      | (change tail (-1 : Fin 4) = envy (-1 : Fin 4)
        ; rw [tail_neg_one, envy_neg_one])
      | (change (2 : ℝ) = 1 + (1 / 2) * tail (-1 : Fin 4)
        ; rw [tail_neg_one]; norm_num)

/-- Exact balanced singleton-cycle input for the four-player table. -/
def certificate : BalancedSingletonCycleCertificate (L := 4) reward :=
  tailData.certificate (by norm_num)

@[simp] theorem certificate_payoff :
    certificate.coarse certificate.initial = ![1, 2, 2, 1] := by
  funext who
  fin_cases who <;>
    norm_num [fin4_sub, tail_neg_one, certificate,
      CyclicSingletonTailData.certificate,
      CyclicSingletonTailData.coarse, tailData, tail, quittingSoloReward,
      reward, envy, Fin.sub_def, Fin.neg_def, Fin.add_def]
  all_goals
    change 1 + (1 / 2) * tail (-1 : Fin 4) = 2
    rw [tail_neg_one]
    norm_num

/-- The explicit payoff is a uniform-equilibrium payoff against the project's
full behavioral deviation class. -/
theorem isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none ![1, 2, 2, 1] := by
  simpa using certificate.isUniformEquilibriumPayoff

/-- The same conclusion through the general cyclic-tail producer. -/
theorem isUniformEquilibriumPayoff_of_tailData :
    (quittingGame reward).IsUniformEquilibriumPayoff none ![1, 2, 2, 1] := by
  rw [← certificate_payoff]
  exact certificate.isUniformEquilibriumPayoff

end CyclicSingletonFourPlayer
end GameTheory
