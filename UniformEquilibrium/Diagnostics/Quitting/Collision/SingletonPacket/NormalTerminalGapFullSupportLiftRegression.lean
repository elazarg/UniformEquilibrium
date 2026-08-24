/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.NormalTerminalGapConstrainedStationary
import UniformEquilibrium.Quitting.Punishment.ContinueFloor

/-!
# Boundary regressions for the normal terminal-gap full-support lift

This module checks the two explicit tables accompanying the lift.  The first
exhibits the exact lower-endpoint regret calculation and its normalized
singleton direction.  The second has punishment value zero but solo payoff
negative, proving that punishment-normality is necessary when the output
target is fixed to the solo vector.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

/-! ## Exact lower-bound mechanism -/

/-- Each player gets one when the other player quits alone and zero whenever
the player itself quits. -/
def lowerBoundMechanismReward :
    {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun S who => if who ∈ S.1 then 0 else 1

/-- The scalar quantities in the constrained-root test compute exactly as in
the packet: `Q=0`, `delta=epsilon`, `A=epsilon`, `N=1`, and the prescribed
value and Never gain have denominators `2-epsilon`. -/
theorem lowerBoundMechanism_exact_calculation
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hlt : epsilon < 1) :
    epsilon / epsilon = 1 ∧
      constrainedStationaryValue epsilon 0 epsilon (1 - epsilon) =
        (1 - epsilon) / (2 - epsilon) ∧
      1 - constrainedStationaryValue epsilon 0 epsilon (1 - epsilon) =
        1 / (2 - epsilon) ∧
      epsilon / (epsilon + epsilon) = 1 / 2 := by
  have hepsilonNe : epsilon ≠ 0 := ne_of_gt hepsilon
  have htwoNe : 2 - epsilon ≠ 0 := by linarith
  constructor
  · exact div_self hepsilonNe
  constructor
  · unfold constrainedStationaryValue
    rw [show 1 - (1 - epsilon) + epsilon * (1 - epsilon) =
      epsilon * (2 - epsilon) by ring]
    field_simp [hepsilonNe, htwoNe]
    ring
  constructor
  · unfold constrainedStationaryValue
    rw [show 1 - (1 - epsilon) + epsilon * (1 - epsilon) =
      epsilon * (2 - epsilon) by ring]
    field_simp [hepsilonNe, htwoNe]
    ring
  · field_simp [hepsilonNe]
    ring

/-- The test table has zero solo target. -/
@[simp] theorem lowerBoundMechanismReward_solo
    (who : Bool) :
    lowerBoundMechanismReward (quittingSingletonTerminal who) who = 0 := by
  simp [lowerBoundMechanismReward, quittingSingletonTerminal]

/-- The limiting normalized direction `(1/2,1/2)` pays every player exactly
`1/2`, strictly above the zero solo target. -/
theorem lowerBoundMechanismReward_half_mixture
    (who : Bool) :
    quittingSingletonMixture lowerBoundMechanismReward (fun _ => 1 / 2) who =
      1 / 2 := by
  fin_cases who <;>
    norm_num [quittingSingletonMixture, lowerBoundMechanismReward,
      quittingSingletonTerminal]

private theorem bool_univ_erase_eq (who : Bool) :
    (Finset.univ.erase who : Finset Bool) = {!who} := by
  cases who <;> decide

private theorem sum_powerset_singleton
    {α : Type} (owner : α) (f : Finset α → ℝ) :
    ∑ S ∈ ({owner} : Finset α).powerset, f S = f ∅ + f {owner} := by
  classical
  rw [show ({owner} : Finset α) = insert owner ∅ by simp,
    Finset.sum_powerset_insert (Finset.notMem_empty owner)]
  simp

private theorem sum_powerset_erase_empty_singleton
    {α : Type} [DecidableEq α] (owner : α) (f : Finset α → ℝ) :
    ∑ S ∈ ({owner} : Finset α).powerset.erase ∅, f S = f {owner} := by
  have hempty : (∅ : Finset α) ∈ ({owner} : Finset α).powerset :=
    Finset.empty_mem_powerset _
  have hsplit := Finset.add_sum_erase _ f hempty
  rw [sum_powerset_singleton owner f] at hsplit
  linarith

/-- The constant hazard row in the boundary test has exact face numerator
`-epsilon` for both players. -/
theorem lowerBoundMechanismReward_faceNumerator
    (epsilon : ℝ) (who : Bool) :
    quittingFaceNumerator (weightOfReward lowerBoundMechanismReward)
      (fun _ => epsilon) who = -epsilon := by
  unfold quittingFaceNumerator continueMassExcl sigmaValue excludedValue
  rw [bool_univ_erase_eq, sum_powerset_singleton,
    sum_powerset_erase_empty_singleton]
  fin_cases who <;>
    norm_num [weightOfReward, lowerBoundMechanismReward]

/-- At every cutoff in `[0,1]`, the constant cutoff row is a literal Nash
root of the constrained auxiliary stationary game. -/
theorem lowerBoundMechanismReward_constant_cutoff_constrainedNash
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    (∀ who : Bool, epsilon ≤ (fun _ : Bool => epsilon) who) ∧
      (∀ who : Bool, (fun _ : Bool => epsilon) who ≤ 1) ∧
      ∀ who rate, epsilon ≤ rate → rate ≤ 1 →
        rate * quittingFaceNumerator
            (weightOfReward lowerBoundMechanismReward)
            (fun _ : Bool => epsilon) who ≤
          (fun _ : Bool => epsilon) who *
            quittingFaceNumerator
              (weightOfReward lowerBoundMechanismReward)
              (fun _ : Bool => epsilon) who := by
  refine ⟨fun _ => le_rfl, fun _ => hepsilon1, ?_⟩
  intro who rate hrate _hrateOne
  rw [lowerBoundMechanismReward_faceNumerator]
  dsimp
  nlinarith

/-- The lower-bound table has no global positive terminal-exploitability gap:
the literal all-Never profile is an exact terminal Nash profile. -/
theorem lowerBoundMechanismReward_not_hasTerminalExploitabilityGap
    {gap : ℝ} (hgap : 0 < gap) :
    ¬ HasTerminalExploitabilityGap lowerBoundMechanismReward gap := by
  intro hexploit
  obtain ⟨who, deviation, himprove⟩ :=
    hexploit (quittingAlwaysContinueProfile lowerBoundMechanismReward)
  have hnash :
      (quittingGame lowerBoundMechanismReward).IsεAsymptoticNash
        (quittingTerminalPayoff lowerBoundMechanismReward) 0
        (quittingAlwaysContinueProfile lowerBoundMechanismReward) :=
    (isεAsymptoticNash_quittingAlwaysContinue_iff
      lowerBoundMechanismReward le_rfl).2 fun player => by
        simp
  have hdeviation := hnash who deviation
  linarith

/-! ## Normality cannot be dropped -/

/-- Player `false` gets `-1` whenever it joins the quitting coalition and
zero when only player `true` quits.  Player `true` is payoff-neutral. -/
def normalityBarrierReward :
    {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun S who => if who = false then if false ∈ S.1 then -1 else 0 else 0

/-- Never quitting gives player `false` the exact continue floor zero. -/
theorem normalityBarrierReward_continueFloor_false :
    quittingContinueFloor normalityBarrierReward false = 0 := by
  apply le_antisymm
  · exact quittingContinueFloor_nonpos normalityBarrierReward false
  · unfold quittingContinueFloor
    apply le_quittingBlockContinueFloor normalityBarrierReward {false} false
      le_rfl
    intro S _hS hdisjoint
    have hfalse : false ∉ S := by
      exact Finset.disjoint_singleton_right.mp hdisjoint
    simp [normalityBarrierReward, hfalse]

/-- The behavioral punishment value of player `false` is exactly zero.  The
upper bound is attained by the pure row where player `true` exits, and the
continue floor supplies the matching lower bound. -/
theorem normalityBarrierReward_punishmentValue_false :
    quittingPunishmentValue normalityBarrierReward false = 0 := by
  rw [quittingPunishmentValue_eq_continueFloor_of_pureRow
    normalityBarrierReward false ({true} : Finset Bool)]
  · exact normalityBarrierReward_continueFloor_false
  · rw [normalityBarrierReward_continueFloor_false]
    norm_num [quittingSetReward, normalityBarrierReward]

/-- Player `false` has solo payoff `-1`, hence is strictly abnormal. -/
theorem normalityBarrierReward_false_abnormal :
    IsQuittingAbnormalPlayer normalityBarrierReward false := by
  unfold IsQuittingAbnormalPlayer quittingSoloSelfPayoff
  rw [normalityBarrierReward_punishmentValue_false]
  norm_num [normalityBarrierReward, quittingSingletonTerminal]

/-- The abnormal player's only distinct normalized-solo comparison is
strictly positive. -/
theorem normalityBarrierReward_normalizedSoloMatrix_false_true :
    QuittingLCPClassification.normalizedSoloMatrix
        normalityBarrierReward false true = 1 := by
  rw [normalizedSoloMatrix_eq_soloReward_sub]
  norm_num [quittingSoloReward, normalityBarrierReward,
    quittingSingletonTerminal]

/-- Consequently the abnormal player is deleted from the recursively
stabilized normal core. -/
theorem normalityBarrierReward_false_not_mem_normalCore :
    false ∉ QuittingLCPClassification.normalCore
      (QuittingLCPClassification.normalizedSoloMatrix
        normalityBarrierReward) := by
  intro hfalse
  obtain ⟨owner, _howner, hne, hentry⟩ :=
    QuittingLCPClassification.exists_core_blocker_of_mem_normalCore
      (QuittingLCPClassification.normalizedSoloMatrix
        normalityBarrierReward) hfalse
  fin_cases owner
  · rw [normalityBarrierReward_normalizedSoloMatrix_false_true] at hentry
    norm_num at hentry
  · simp at hne

/-- Consequently no normalized singleton packet can use the literal solo
payoff as player `false`'s target: its punishment-floor field would say
`0 ≤ -1`. -/
theorem not_exists_normalityBarrierPacket_with_soloTarget_false :
    ¬ ∃ packet : QuittingNormalizedSingletonSourcePacket normalityBarrierReward,
      packet.target false =
        normalityBarrierReward (quittingSingletonTerminal false) false := by
  rintro ⟨packet, htarget⟩
  have hfloor := packet.punishment_le_target false
  rw [normalityBarrierReward_punishmentValue_false, htarget] at hfloor
  norm_num [normalityBarrierReward, quittingSingletonTerminal] at hfloor

end GameTheory
