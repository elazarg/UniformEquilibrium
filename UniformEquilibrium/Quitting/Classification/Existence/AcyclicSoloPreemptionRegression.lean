/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.AcyclicSoloPreemption

/-!
# Boundary tests for acyclic augmented solo preemption

These finite tables check the equality face, the strict-sink exact rate, the
one-player convention, and the directed-cycle boundary.  They are theorem
regressions, not numerical experiments.
-/

noncomputable section

namespace GameTheory.AcyclicSoloPreemptionRegression

open Math.Probability

/-! ## The weak sink and sharp `q J` factor -/

/-- Two-player equality-face table.  Player `false` owns the singleton row;
player `true` is indifferent between its own singleton and that row, but gains
one unit from colliding. -/
def weakSinkReward
    (terminal : {S : Finset Bool // S.Nonempty}) : Payoff Bool := fun who =>
  if who = false then
    if terminal.1 = {false} then 1 else 0
  else if terminal.1 = {false, true} then 1 else 0

@[simp] theorem weakSinkReward_ownerSolo :
    quittingSoloReward weakSinkReward false false = 1 := by
  norm_num [quittingSoloReward, weakSinkReward]

@[simp] theorem weakSinkReward_otherSolo :
    quittingSoloReward weakSinkReward true true = 0 := by
  norm_num [quittingSoloReward, weakSinkReward]
  decide

@[simp] theorem weakSinkReward_ownerRow_other :
    quittingSoloReward weakSinkReward false true = 0 := by
  norm_num [quittingSoloReward, weakSinkReward]
  decide

@[simp] theorem weakSinkReward_collision_other :
    quittingSingletonCollisionReward weakSinkReward false true = 1 := by
  norm_num [quittingSingletonCollisionReward, weakSinkReward, Finset.ext_iff]

/-- The clamped pair premium is exactly one on the weak-sink table. -/
theorem weakSinkReward_pairPremium :
    quittingSoloPairPremium weakSinkReward false = 1 := by
  norm_num [quittingSoloPairPremium, Math.Finset.insertMax,
    quittingSingletonCollisionReward, quittingSoloReward, weakSinkReward,
    Finset.ext_iff]

/-- A rank witnesses augmented acyclicity of the equality-face table. -/
theorem weakSinkReward_acyclic :
    IsQuittingAugmentedSoloPreemptionAcyclic weakSinkReward := by
  apply isQuittingAugmentedSoloPreemptionAcyclic_of_rank weakSinkReward
    (fun | some false => 1 | _ => 0)
  intro source target hedge
  cases source with
  | none =>
      cases target with
      | none => exact False.elim hedge
      | some target =>
          cases target
          all_goals norm_num [QuittingAugmentedSoloPreemptionEdge,
            quittingSoloReward, weakSinkReward, Finset.ext_iff] at hedge
          all_goals norm_num
  | some source =>
      cases target with
      | none =>
          cases source
          all_goals norm_num [QuittingAugmentedSoloPreemptionEdge,
            quittingSoloReward, weakSinkReward, Finset.ext_iff] at hedge
      | some target =>
          cases source <;> cases target
          all_goals norm_num [QuittingAugmentedSoloPreemptionEdge,
            quittingSoloReward, weakSinkReward, Finset.ext_iff] at hedge
          all_goals norm_num

/-- At every positive owner rate, quitting immediately gives the outsider a
strict gain.  Thus the factor `q` cannot be removed from the quantitative
theorem and weak sink inequalities do not imply exactness. -/
theorem weakSinkReward_not_exact
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ¬(quittingGame weakSinkReward).IsεAsymptoticNash
      (quittingTerminalPayoff weakSinkReward) 0
      (quittingStationaryProfile weakSinkReward
        (quittingSoloStationaryRoot false
          (quittingHazardCoin q hq0.le hq1))) := by
  rw [isεAsymptoticNash_soloStationary_exact_iff
    weakSinkReward false _ (by simpa using hq0)]
  push Not
  intro _
  refine ⟨true, by decide, ?_⟩
  simp
  exact hq0

/-! ## A rational strict sink -/

/-- Strict table with gap one and collision premium two. -/
def strictSinkReward
    (terminal : {S : Finset Bool // S.Nonempty}) : Payoff Bool := fun who =>
  if who = false then
    if terminal.1 = {false} then 1 else 0
  else if terminal.1 = {false} then 1
  else if terminal.1 = {false, true} then 3
  else 0

@[simp] theorem strictSinkReward_ownerSolo :
    quittingSoloReward strictSinkReward false false = 1 := by
  norm_num [quittingSoloReward, strictSinkReward]

@[simp] theorem strictSinkReward_otherSolo :
    quittingSoloReward strictSinkReward true true = 0 := by
  norm_num [quittingSoloReward, strictSinkReward]
  decide

@[simp] theorem strictSinkReward_ownerRow_other :
    quittingSoloReward strictSinkReward false true = 1 := by
  norm_num [quittingSoloReward, strictSinkReward]

@[simp] theorem strictSinkReward_collision_other :
    quittingSingletonCollisionReward strictSinkReward false true = 3 := by
  norm_num [quittingSingletonCollisionReward, strictSinkReward,
    Finset.ext_iff]

theorem strictSinkReward_pairPremium :
    quittingSoloPairPremium strictSinkReward false = 2 := by
  norm_num [quittingSoloPairPremium, Math.Finset.insertMax,
    quittingSingletonCollisionReward, quittingSoloReward, strictSinkReward,
    Finset.ext_iff]

theorem strictSinkReward_acyclic :
    IsQuittingAugmentedSoloPreemptionAcyclic strictSinkReward := by
  apply isQuittingAugmentedSoloPreemptionAcyclic_of_rank strictSinkReward
    (fun | some false => 1 | _ => 0)
  intro source target hedge
  cases source with
  | none =>
      cases target with
      | none => exact False.elim hedge
      | some target =>
          cases target
          all_goals norm_num [QuittingAugmentedSoloPreemptionEdge,
            quittingSoloReward, strictSinkReward, Finset.ext_iff] at hedge
          all_goals norm_num
  | some source =>
      cases target with
      | none =>
          cases source
          all_goals norm_num [QuittingAugmentedSoloPreemptionEdge,
            quittingSoloReward, strictSinkReward, Finset.ext_iff] at hedge
      | some target =>
          cases source <;> cases target
          all_goals norm_num [QuittingAugmentedSoloPreemptionEdge,
            quittingSoloReward, strictSinkReward, Finset.ext_iff] at hedge
          all_goals norm_num

/-- The displayed rational rate `1/6` is an exact terminal Nash profile. -/
theorem strictSinkReward_oneSixth_exact :
    (quittingGame strictSinkReward).IsεAsymptoticNash
      (quittingTerminalPayoff strictSinkReward) 0
      (quittingStationaryProfile strictSinkReward
        (quittingSoloStationaryRoot false
          (quittingHazardCoin (1 / 6 : ℝ) (by norm_num) (by norm_num)))) := by
  refine isεAsymptoticNash_soloStationary_exact_of_strictSink
    strictSinkReward false (gap := 1) (q := 1 / 6)
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_
  · rw [strictSinkReward_pairPremium]
    norm_num
  · norm_num
  · intro other hne
    cases other with
    | false => exact (hne rfl).elim
    | true => norm_num

/-! ## One player -/

def onePlayerReward
    (_terminal : {S : Finset PUnit // S.Nonempty}) : Payoff PUnit := fun _ => 1

theorem onePlayerReward_positiveRate_exact
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (quittingGame onePlayerReward).IsεAsymptoticNash
      (quittingTerminalPayoff onePlayerReward) 0
      (quittingStationaryProfile onePlayerReward
        (quittingSoloStationaryRoot PUnit.unit
          (quittingHazardCoin q hq0.le hq1))) := by
  apply isεAsymptoticNash_soloStationary_exact
  · simpa using hq0
  · simp [quittingSoloReward, onePlayerReward]
  · intro other hne
    exact False.elim (hne (Subsingleton.elim _ _))

/-! ## The cyclic boundary -/

/-- Each player values only its own singleton.  The two player vertices
strictly preempt one another, so the acyclic theorem is unavailable. -/
def cyclicBoundaryReward
    (terminal : {S : Finset Bool // S.Nonempty}) : Payoff Bool := fun who =>
  if terminal.1 = {who} then 1 else 0

def cyclicBoundaryVertex (time : ℕ) : Option Bool :=
  some (if time % 2 = 0 then false else true)

/-- The augmented graph genuinely contains the player two-cycle. -/
def cyclicBoundaryCycle :
    QuittingAugmentedSoloPreemptionCycle cyclicBoundaryReward where
  period := 2
  period_pos := by norm_num
  vertex := cyclicBoundaryVertex
  vertex_periodic := by
    intro time
    simp [cyclicBoundaryVertex, Nat.add_mod_right]
  edge := by
    intro time
    rcases Nat.mod_two_eq_zero_or_one time with hmod | hmod
    · have hnext : (time + 1) % 2 = 1 := by omega
      simp [cyclicBoundaryVertex, hmod, hnext,
        QuittingAugmentedSoloPreemptionEdge, quittingSoloReward,
        cyclicBoundaryReward, Finset.ext_iff]
    · have hnext : (time + 1) % 2 = 0 := by omega
      simp [cyclicBoundaryVertex, hmod, hnext,
        QuittingAugmentedSoloPreemptionEdge, quittingSoloReward,
        cyclicBoundaryReward, Finset.ext_iff]

theorem cyclicBoundaryReward_not_acyclic :
    ¬IsQuittingAugmentedSoloPreemptionAcyclic cyclicBoundaryReward := by
  intro hacyclic
  exact hacyclic ⟨cyclicBoundaryCycle⟩

end GameTheory.AcyclicSoloPreemptionRegression
