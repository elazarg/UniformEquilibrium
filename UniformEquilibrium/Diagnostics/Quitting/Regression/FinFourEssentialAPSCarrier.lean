/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.ConvexFixedPoint

/-!
# A four-player essential-APS carrier with forced summable motion

This file defines the singleton table and compact convex carrier underlying a
concrete essential-APS regression. It proves the exact successor graph, the
greatest-family equality, terminal-freeness, and the forced three-step Mobius
recurrence. The construction is explicit supplied APS data; no Nash or source
chronology is asserted here.
-/

noncomputable section

namespace GameTheory
namespace FinFourEssentialAPSCarrier

open StochasticGame Set

abbrev Player := Fin 4

/-- Common singleton baseline and common carrier face. -/
def baseline : Payoff Player := fun _ ↦ 1

/-- The four singleton payoff rows. -/
def singletonReward (quitter recipient : Player) : ℝ :=
  if quitter.val = 0 then
    if recipient.val = 0 then 1 else if recipient.val = 1 then 3
      else if recipient.val = 2 then 0 else 1
  else if quitter.val = 1 then
    if recipient.val = 0 then 0 else if recipient.val = 1 then 1
      else if recipient.val = 2 then 3 else 1
  else if quitter.val = 2 then
    if recipient.val = 0 then 3 else if recipient.val = 1 then 0
      else if recipient.val = 2 then 1 else 1
  else
    if recipient.val = 0 then 2 else if recipient.val = 1 then 2
      else if recipient.val = 2 then 2 else 1

/-- Completion A: every nonsingleton terminal coalition pays the baseline. -/
def completionAReward
    (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  if terminal.1 = {0} then singletonReward 0
  else if terminal.1 = {1} then singletonReward 1
  else if terminal.1 = {2} then singletonReward 2
  else if terminal.1 = {3} then singletonReward 3
  else baseline

@[simp] theorem completionAReward_singleton (quitter : Player) :
    completionAReward (quittingSingletonTerminal quitter) =
      singletonReward quitter := by
  fin_cases quitter <;>
    simp +decide [completionAReward]

@[simp] theorem quittingSoloReward_completionAReward (quitter : Player) :
    quittingSoloReward completionAReward quitter = singletonReward quitter := by
  fin_cases quitter <;>
    simp +decide [quittingSoloReward, completionAReward]

@[simp] theorem quittingSoloBaseline_completionAReward :
    quittingSoloBaseline completionAReward = baseline := by
  funext who
  fin_cases who <;>
    norm_num [quittingSoloBaseline, singletonReward, baseline]

/-- Exact strict Flesch graph of the singleton table. -/
theorem fleschSuccessor_iff (owner successor : Player) :
    QuittingFleschSuccessor completionAReward owner successor ↔
      (owner = 0 ∧ successor = 1) ∨
      (owner = 1 ∧ successor = 2) ∨
      (owner = 2 ∧ successor = 0) := by
  fin_cases owner <;> fin_cases successor <;>
    norm_num +decide [QuittingFleschSuccessor, singletonReward]

/-- The only graph successor of owner zero is owner one. -/
theorem fleschSuccessor_zero_iff (successor : Player) :
    QuittingFleschSuccessor completionAReward 0 successor ↔ successor = 1 := by
  rw [fleschSuccessor_iff]
  simp

/-- The only graph successor of owner one is owner two. -/
theorem fleschSuccessor_one_iff (successor : Player) :
    QuittingFleschSuccessor completionAReward 1 successor ↔ successor = 2 := by
  rw [fleschSuccessor_iff]
  simp

/-- The only graph successor of owner two is owner zero. -/
theorem fleschSuccessor_two_iff (successor : Player) :
    QuittingFleschSuccessor completionAReward 2 successor ↔ successor = 0 := by
  rw [fleschSuccessor_iff]
  simp

/-- Owner three has no strict Flesch successor. -/
theorem not_fleschSuccessor_three (successor : Player) :
    ¬ QuittingFleschSuccessor completionAReward 3 successor := by
  rw [fleschSuccessor_iff]
  simp

/-- Owner-zero carrier value with active displacement `x`. -/
def valueZero (x : ℝ) (who : Player) : ℝ := if who.val = 1 then 1 + x else 1

/-- Owner-one carrier value with active displacement `y`. -/
def valueOne (y : ℝ) (who : Player) : ℝ := if who.val = 2 then 1 + y else 1

/-- Owner-two carrier value with active displacement `z`. -/
def valueTwo (z : ℝ) (who : Player) : ℝ := if who.val = 0 then 1 + z else 1

/-- Compact coordinatewise convex carrier from the packet. -/
def carrier : Player → Set (Payoff Player) := fun owner ↦
  if owner.val = 0 then valueZero '' Icc 0 (1 / 2 : ℝ)
  else if owner.val = 1 then valueOne '' Icc 0 (1 / 3 : ℝ)
  else if owner.val = 2 then valueTwo '' Icc 0 (1 / 5 : ℝ)
  else ∅

@[simp] theorem carrier_zero : carrier 0 = valueZero '' Icc 0 (1 / 2 : ℝ) := by
  simp [carrier]

@[simp] theorem carrier_one : carrier 1 = valueOne '' Icc 0 (1 / 3 : ℝ) := by
  simp [carrier]

@[simp] theorem carrier_two : carrier 2 = valueTwo '' Icc 0 (1 / 5 : ℝ) := by
  simp [carrier]

@[simp] theorem carrier_three : carrier 3 = ∅ := by
  simp [carrier]

private theorem continuous_valueZero : Continuous valueZero := by
  apply continuous_pi
  intro who
  fin_cases who <;> simp [valueZero] <;> fun_prop

private theorem continuous_valueOne : Continuous valueOne := by
  apply continuous_pi
  intro who
  fin_cases who <;> simp [valueOne] <;> fun_prop

private theorem continuous_valueTwo : Continuous valueTwo := by
  apply continuous_pi
  intro who
  fin_cases who <;> simp [valueTwo] <;> fun_prop

theorem compact_carrier (owner : Player) : IsCompact (carrier owner) := by
  fin_cases owner
  · change IsCompact (valueZero '' Icc 0 (1 / 2 : ℝ))
    exact isCompact_Icc.image continuous_valueZero
  · change IsCompact (valueOne '' Icc 0 (1 / 3 : ℝ))
    exact isCompact_Icc.image continuous_valueOne
  · change IsCompact (valueTwo '' Icc 0 (1 / 5 : ℝ))
    exact isCompact_Icc.image continuous_valueTwo
  · change IsCompact (∅ : Set (Payoff Player))
    exact isCompact_empty

private theorem convex_valueZero_image (upper : ℝ) :
    Convex ℝ (valueZero '' Icc 0 upper) := by
  rw [convex_iff_add_mem]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  refine ⟨a * x + b * y, ⟨?_, ?_⟩, ?_⟩
  · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  · calc
      a * x + b * y ≤ a * upper + b * upper :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = upper := by rw [← add_mul, hab, one_mul]
  · ext who
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases who <;> simp [valueZero] <;> nlinarith [hab]

private theorem convex_valueOne_image (upper : ℝ) :
    Convex ℝ (valueOne '' Icc 0 upper) := by
  rw [convex_iff_add_mem]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  refine ⟨a * x + b * y, ⟨?_, ?_⟩, ?_⟩
  · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  · calc
      a * x + b * y ≤ a * upper + b * upper :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = upper := by rw [← add_mul, hab, one_mul]
  · ext who
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases who <;> simp [valueOne] <;> nlinarith [hab]

private theorem convex_valueTwo_image (upper : ℝ) :
    Convex ℝ (valueTwo '' Icc 0 upper) := by
  rw [convex_iff_add_mem]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  refine ⟨a * x + b * y, ⟨?_, ?_⟩, ?_⟩
  · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  · calc
      a * x + b * y ≤ a * upper + b * upper :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = upper := by rw [← add_mul, hab, one_mul]
  · ext who
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases who <;> simp [valueTwo] <;> nlinarith [hab]

theorem convex_carrier (owner : Player) : Convex ℝ (carrier owner) := by
  fin_cases owner
  · change Convex ℝ (valueZero '' Icc 0 (1 / 2 : ℝ))
    exact convex_valueZero_image (1 / 2 : ℝ)
  · change Convex ℝ (valueOne '' Icc 0 (1 / 3 : ℝ))
    exact convex_valueOne_image (1 / 3 : ℝ)
  · change Convex ℝ (valueTwo '' Icc 0 (1 / 5 : ℝ))
    exact convex_valueTwo_image (1 / 5 : ℝ)
  · change Convex ℝ (∅ : Set (Payoff Player))
    exact convex_empty

theorem viable_valueZero {x : ℝ} (hx : 0 ≤ x) :
    QuittingEssentialAPSViable completionAReward (valueZero x) := by
  intro who
  fin_cases who <;>
    norm_num +decide [quittingSoloBaseline, quittingSoloReward,
      completionAReward, singletonReward, valueZero] at hx ⊢
  all_goals linarith

theorem viable_valueOne {y : ℝ} (hy : 0 ≤ y) :
    QuittingEssentialAPSViable completionAReward (valueOne y) := by
  intro who
  fin_cases who <;>
    norm_num +decide [quittingSoloBaseline, quittingSoloReward,
      completionAReward, singletonReward, valueOne] at hy ⊢
  all_goals linarith

theorem viable_valueTwo {z : ℝ} (hz : 0 ≤ z) :
    QuittingEssentialAPSViable completionAReward (valueTwo z) := by
  intro who
  fin_cases who <;>
    norm_num +decide [quittingSoloBaseline, quittingSoloReward,
      completionAReward, singletonReward, valueTwo] at hz ⊢
  all_goals linarith

/-- Forced owner-zero mass. -/
def massZero (x : ℝ) : ℝ := x / 2

/-- Forced owner-zero continuation coordinate. -/
def nextOneCoordinate (x : ℝ) : ℝ := x / (2 - x)

/-- Forced owner-one mass. -/
def massOne (y : ℝ) : ℝ := y / 2

/-- Forced owner-one continuation coordinate. -/
def nextTwoCoordinate (y : ℝ) : ℝ := y / (2 - y)

/-- Forced owner-two mass. -/
def massTwo (z : ℝ) : ℝ := z / 2

/-- Forced owner-two continuation coordinate. -/
def nextZeroCoordinate (z : ℝ) : ℝ := z / (2 - z)

/-- One complete owner circuit on the owner-zero coordinate. -/
def circuitMap (x : ℝ) : ℝ := x / (8 - 7 * x)

theorem massZero_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    massZero x ∈ Icc (0 : ℝ) 1 := by
  constructor <;> norm_num [massZero] at hx ⊢ <;> linarith

theorem nextOneCoordinate_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    nextOneCoordinate x ∈ Icc (0 : ℝ) (1 / 3) := by
  have hdenom : 0 < 2 - x := by linarith [hx.2]
  constructor
  · exact div_nonneg hx.1 hdenom.le
  · apply (div_le_iff₀ hdenom).2
    linarith [hx.2]

theorem massOne_mem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (1 / 3)) :
    massOne y ∈ Icc (0 : ℝ) 1 := by
  constructor <;> norm_num [massOne] at hy ⊢ <;> linarith

theorem nextTwoCoordinate_mem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (1 / 3)) :
    nextTwoCoordinate y ∈ Icc (0 : ℝ) (1 / 5) := by
  have hdenom : 0 < 2 - y := by linarith [hy.2]
  constructor
  · exact div_nonneg hy.1 hdenom.le
  · apply (div_le_iff₀ hdenom).2
    linarith [hy.2]

theorem massTwo_mem {z : ℝ} (hz : z ∈ Icc (0 : ℝ) (1 / 5)) :
    massTwo z ∈ Icc (0 : ℝ) 1 := by
  constructor <;> norm_num [massTwo] at hz ⊢ <;> linarith

theorem nextZeroCoordinate_mem {z : ℝ} (hz : z ∈ Icc (0 : ℝ) (1 / 5)) :
    nextZeroCoordinate z ∈ Icc (0 : ℝ) (1 / 2) := by
  have hdenom : 0 < 2 - z := by linarith [hz.2]
  constructor
  · exact div_nonneg hz.1 hdenom.le
  · apply (div_le_iff₀ hdenom).2
    linarith [hz.2]

theorem valueZero_arc (x : ℝ) (hdenom : 2 - x ≠ 0) :
    valueZero x = quittingSingletonArcPayoff (massZero x)
      (singletonReward 0) (valueOne (nextOneCoordinate x)) := by
  ext who
  fin_cases who <;>
    simp [valueZero, valueOne, singletonReward, massZero,
      nextOneCoordinate, quittingSingletonArcPayoff] <;>
    field_simp <;> ring

theorem valueOne_arc (y : ℝ) (hdenom : 2 - y ≠ 0) :
    valueOne y = quittingSingletonArcPayoff (massOne y)
      (singletonReward 1) (valueTwo (nextTwoCoordinate y)) := by
  ext who
  fin_cases who <;>
    simp [valueOne, valueTwo, singletonReward, massOne,
      nextTwoCoordinate, quittingSingletonArcPayoff] <;>
    field_simp <;> ring

theorem valueTwo_arc (z : ℝ) (hdenom : 2 - z ≠ 0) :
    valueTwo z = quittingSingletonArcPayoff (massTwo z)
      (singletonReward 2) (valueZero (nextZeroCoordinate z)) := by
  ext who
  fin_cases who <;>
    simp [valueTwo, valueZero, singletonReward, massTwo,
      nextZeroCoordinate, quittingSingletonArcPayoff] <;>
    field_simp <;> ring

theorem carrier_subinvariant :
    IsQuittingEssentialAPSSubinvariantWithin
      completionAReward carrier carrier := by
  intro owner current hcurrent
  refine ⟨hcurrent, ?_⟩
  change current ∈ quittingEssentialAPSOwnerStep completionAReward carrier owner
  right
  apply quittingSegmentEssentialAPSPrefix_subset
  fin_cases owner
  · simp only [carrier, ↓reduceIte] at hcurrent
    rcases hcurrent with ⟨x, hx, rfl⟩
    let y := nextOneCoordinate x
    have hy : y ∈ Icc (0 : ℝ) (1 / 3) := nextOneCoordinate_mem hx
    refine ⟨viable_valueZero hx.1, massZero x, massZero_mem hx,
      valueOne y, ?_, ?_, ?_⟩
    · exact ⟨1, (fleschSuccessor_zero_iff 1).2 rfl,
        by exact ⟨y, hy, rfl⟩⟩
    · rw [quittingSoloReward_completionAReward]
      exact valueZero_arc x (by linarith [hx.2])
    · rfl
  · simp only [carrier, reduceCtorEq, ↓reduceIte] at hcurrent
    rcases hcurrent with ⟨y, hy, rfl⟩
    let z := nextTwoCoordinate y
    have hz : z ∈ Icc (0 : ℝ) (1 / 5) := nextTwoCoordinate_mem hy
    refine ⟨viable_valueOne hy.1, massOne y, massOne_mem hy,
      valueTwo z, ?_, ?_, ?_⟩
    · exact ⟨2, (fleschSuccessor_one_iff 2).2 rfl,
        by exact ⟨z, hz, rfl⟩⟩
    · rw [quittingSoloReward_completionAReward]
      exact valueOne_arc y (by linarith [hy.2])
    · rfl
  · simp only [carrier, reduceCtorEq, ↓reduceIte] at hcurrent
    rcases hcurrent with ⟨z, hz, rfl⟩
    let x := nextZeroCoordinate z
    have hx : x ∈ Icc (0 : ℝ) (1 / 2) := nextZeroCoordinate_mem hz
    refine ⟨viable_valueTwo hz.1, massTwo z, massTwo_mem hz,
      valueZero x, ?_, ?_, ?_⟩
    · exact ⟨0, (fleschSuccessor_two_iff 0).2 rfl,
        by exact ⟨x, hx, rfl⟩⟩
    · rw [quittingSoloReward_completionAReward]
      exact valueTwo_arc z (by linarith [hz.2])
    · rfl
  · simp [carrier] at hcurrent

/-- The carrier is exactly the carrier-restricted greatest APS family. -/
theorem greatestFamily_eq_carrier :
    quittingEssentialAPSGreatestFamily completionAReward carrier = carrier := by
  apply le_antisymm
  · intro owner value hvalue
    exact (quittingEssentialAPSGreatestFamily_subinvariant
      completionAReward carrier owner hvalue).1
  · exact quittingEssentialAPSFamily_le_greatest
      completionAReward carrier carrier carrier_subinvariant

/-- No point of the greatest family is a viable singleton terminal point. -/
theorem greatestFamily_terminalFree :
    ∀ owner value,
      value ∈ quittingEssentialAPSGreatestFamily completionAReward carrier owner →
      value ∉ quittingEssentialAPSTerminal completionAReward owner := by
  intro owner value hvalue hterminal
  rw [greatestFamily_eq_carrier] at hvalue
  fin_cases owner
  · rcases hterminal with ⟨rfl, hviable⟩
    have hbad := hviable (2 : Player)
    norm_num +decide [QuittingEssentialAPSViable, quittingSoloBaseline,
      quittingSoloReward, completionAReward, singletonReward] at hbad
  · rcases hterminal with ⟨rfl, hviable⟩
    have hbad := hviable (0 : Player)
    norm_num +decide [QuittingEssentialAPSViable, quittingSoloBaseline,
      quittingSoloReward, completionAReward, singletonReward] at hbad
  · rcases hterminal with ⟨rfl, hviable⟩
    have hbad := hviable (1 : Player)
    norm_num +decide [QuittingEssentialAPSViable, quittingSoloBaseline,
      quittingSoloReward, completionAReward, singletonReward] at hbad
  · simp [carrier] at hvalue

/-- The three displayed fractional transitions compose to the stated Mobius map. -/
theorem nextZero_after_three_eq_circuitMap {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    nextZeroCoordinate
        (nextTwoCoordinate (nextOneCoordinate x)) = circuitMap x := by
  have h0 : 2 - x ≠ 0 := by linarith [hx.2]
  have h1 : 4 - 3 * x ≠ 0 := by linarith [hx.2]
  have hmiddle :
      nextTwoCoordinate (nextOneCoordinate x) = x / (4 - 3 * x) := by
    simp [nextOneCoordinate, nextTwoCoordinate]
    field_simp [h0, h1]
    ring
  rw [hmiddle]
  change (x / (4 - 3 * x)) / (2 - x / (4 - 3 * x)) =
    x / (8 - 7 * x)
  have houterEq :
      2 - x / (4 - 3 * x) = (8 - 7 * x) / (4 - 3 * x) := by
    apply (eq_div_iff h1).2
    rw [sub_mul, div_mul_cancel₀ x h1]
    ring
  rw [houterEq]
  exact div_div_div_cancel_right₀ h1 x (8 - 7 * x)

theorem circuitMap_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    circuitMap x ∈ Icc (0 : ℝ) (1 / 9) := by
  have hdenom : 0 < 8 - 7 * x := by linarith [hx.2]
  constructor
  · exact div_nonneg hx.1 hdenom.le
  · apply (div_le_iff₀ hdenom).2
    linarith [hx.2]

theorem circuitMap_le_two_ninth_mul {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    circuitMap x ≤ (2 / 9 : ℝ) * x := by
  have hdenom : 0 < 8 - 7 * x := by linarith [hx.2]
  rw [circuitMap, div_le_iff₀ hdenom]
  nlinarith [hx.1, hx.2]

private theorem forced_zero_aux {x p y : ℝ}
    (harc : valueZero x = quittingSingletonArcPayoff p
      (singletonReward 0) (valueOne y)) :
    p = massZero x ∧ (2 - x) * y = x := by
  have hfirst := congrFun harc (1 : Player)
  have hsecond := congrFun harc (2 : Player)
  norm_num +decide [valueZero, valueOne, singletonReward, massZero,
    quittingSingletonArcPayoff] at hfirst hsecond ⊢
  constructor
  · linarith
  · have hp : p = x / 2 := by linarith
    rw [hp] at hsecond
    nlinarith

/-- Every one-continuation segment from an owner-zero carrier point
has the displayed mass and continuation. -/
theorem forced_segment_zero {x p : ℝ} {next : Payoff Player}
    (hx : x ∈ Icc (0 : ℝ) (1 / 2))
    (hnext : next ∈ quittingEssentialAPSSuccessorSet completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier) 0)
    (harc : valueZero x = quittingSingletonArcPayoff p
      (quittingSoloReward completionAReward 0) next) :
    p = massZero x ∧ next = valueOne (nextOneCoordinate x) := by
  rcases hnext with ⟨successor, hedge, hnext⟩
  have hsuccessor : successor = 1 := (fleschSuccessor_zero_iff successor).1 hedge
  subst successor
  rw [greatestFamily_eq_carrier, carrier_one] at hnext
  rcases hnext with ⟨y, hy, rfl⟩
  rw [quittingSoloReward_completionAReward] at harc
  obtain ⟨hp, hyEq⟩ := forced_zero_aux harc
  refine ⟨hp, ?_⟩
  congr 1
  rw [nextOneCoordinate]
  apply (eq_div_iff ?_).2
  · simpa [mul_comm] using hyEq
  · linarith [hx.2]

private theorem forced_one_aux {y p z : ℝ}
    (harc : valueOne y = quittingSingletonArcPayoff p
      (singletonReward 1) (valueTwo z)) :
    p = massOne y ∧ (2 - y) * z = y := by
  have hfirst := congrFun harc (2 : Player)
  have hsecond := congrFun harc (0 : Player)
  norm_num +decide [valueOne, valueTwo, singletonReward, massOne,
    quittingSingletonArcPayoff] at hfirst hsecond ⊢
  constructor
  · linarith
  · have hp : p = y / 2 := by linarith
    rw [hp] at hsecond
    nlinarith

/-- Every one-continuation segment from an owner-one carrier point
has the displayed mass and continuation. -/
theorem forced_segment_one {y p : ℝ} {next : Payoff Player}
    (hy : y ∈ Icc (0 : ℝ) (1 / 3))
    (hnext : next ∈ quittingEssentialAPSSuccessorSet completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier) 1)
    (harc : valueOne y = quittingSingletonArcPayoff p
      (quittingSoloReward completionAReward 1) next) :
    p = massOne y ∧ next = valueTwo (nextTwoCoordinate y) := by
  rcases hnext with ⟨successor, hedge, hnext⟩
  have hsuccessor : successor = 2 := (fleschSuccessor_one_iff successor).1 hedge
  subst successor
  rw [greatestFamily_eq_carrier, carrier_two] at hnext
  rcases hnext with ⟨z, hz, rfl⟩
  rw [quittingSoloReward_completionAReward] at harc
  obtain ⟨hp, hzEq⟩ := forced_one_aux harc
  refine ⟨hp, ?_⟩
  congr 1
  rw [nextTwoCoordinate]
  apply (eq_div_iff ?_).2
  · simpa [mul_comm] using hzEq
  · linarith [hy.2]

private theorem forced_two_aux {z p x : ℝ}
    (harc : valueTwo z = quittingSingletonArcPayoff p
      (singletonReward 2) (valueZero x)) :
    p = massTwo z ∧ (2 - z) * x = z := by
  have hfirst := congrFun harc (0 : Player)
  have hsecond := congrFun harc (1 : Player)
  norm_num +decide [valueTwo, valueZero, singletonReward, massTwo,
    quittingSingletonArcPayoff] at hfirst hsecond ⊢
  constructor
  · linarith
  · have hp : p = z / 2 := by linarith
    rw [hp] at hsecond
    nlinarith

/-- Every one-continuation segment from an owner-two carrier point
has the displayed mass and continuation. -/
theorem forced_segment_two {z p : ℝ} {next : Payoff Player}
    (hz : z ∈ Icc (0 : ℝ) (1 / 5))
    (hnext : next ∈ quittingEssentialAPSSuccessorSet completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier) 2)
    (harc : valueTwo z = quittingSingletonArcPayoff p
      (quittingSoloReward completionAReward 2) next) :
    p = massTwo z ∧ next = valueZero (nextZeroCoordinate z) := by
  rcases hnext with ⟨successor, hedge, hnext⟩
  have hsuccessor : successor = 0 := (fleschSuccessor_two_iff successor).1 hedge
  subst successor
  rw [greatestFamily_eq_carrier, carrier_zero] at hnext
  rcases hnext with ⟨x, hx, rfl⟩
  rw [quittingSoloReward_completionAReward] at harc
  obtain ⟨hp, hxEq⟩ := forced_two_aux harc
  refine ⟨hp, ?_⟩
  congr 1
  rw [nextZeroCoordinate]
  apply (eq_div_iff ?_).2
  · simpa [mul_comm] using hxEq
  · linarith [hz.2]

end FinFourEssentialAPSCarrier
end GameTheory
