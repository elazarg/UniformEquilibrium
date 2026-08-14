/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# Debt-transfer roots and three-role triangle geometry

An oriented unit debt transfer from `source` to `target` is the type-`A`
root `e_target - e_source`.  Consecutive transfers contract exactly, and
every three-edge triangle is a closed circulation.

This proves that debt conservation itself has rank three.  It does *not*
turn an arbitrary quitting-game reset word into a three-player game: phase
pinning, payoff tables, punishment floors, positive edge realizability, and
chronology are additional data not present in a root vector.
-/

noncomputable section

namespace GameTheory

variable {ι : Type*} [DecidableEq ι]

/-- Signed coordinate vector of one unit debt transfer. -/
def debtTransferRoot (source target : ι) : ι → ℝ :=
  fun who => (if who = target then 1 else 0) -
    if who = source then 1 else 0

@[simp] theorem debtTransferRoot_self (source : ι) :
    debtTransferRoot source source = 0 := by
  funext who
  simp [debtTransferRoot]

/-- Reversing a transfer negates its root. -/
theorem debtTransferRoot_reverse (source target : ι) :
    debtTransferRoot target source =
      fun who => -debtTransferRoot source target who := by
  funext who
  simp only [debtTransferRoot]
  ring

/-- **Two-edge contraction.** The common intermediate coordinate cancels. -/
theorem debtTransferRoot_add (source middle target : ι) :
    (fun who => debtTransferRoot source middle who +
      debtTransferRoot middle target who) =
    debtTransferRoot source target := by
  funext who
  simp only [debtTransferRoot]
  ring

/-- Every oriented triangle is a closed debt circulation. -/
theorem debtTransferRoot_triangle (first second third : ι) :
    (fun who => debtTransferRoot first second who +
      debtTransferRoot second third who +
      debtTransferRoot third first who) = 0 := by
  rw [show (fun who => debtTransferRoot first second who +
      debtTransferRoot second third who +
      debtTransferRoot third first who) =
    fun who => debtTransferRoot first third who +
      debtTransferRoot third first who by
      funext who
      rw [← debtTransferRoot_add first second third]]
  funext who
  rw [debtTransferRoot_reverse first third]
  simp

/-- Sum of the transfer roots along a finite vertex chain. -/
def debtTransferChain : List ι → ι → ℝ
  | [], _ => 0
  | [_], _ => 0
  | source :: target :: rest, who =>
      debtTransferRoot source target who +
        debtTransferChain (target :: rest) who

/-- Every finite transfer chain contracts to its two endpoints, regardless
of how many intermediate roles it uses. -/
theorem debtTransferChain_eq_endpoints
    (source target : ι) (middle : List ι) :
    debtTransferChain (source :: middle ++ [target]) =
      debtTransferRoot source target := by
  induction middle generalizing source with
  | nil =>
      funext who
      simp [debtTransferChain]
  | cons pivot rest ih =>
      rw [show source :: (pivot :: rest) ++ [target] =
        source :: pivot :: (rest ++ [target]) by rfl]
      change (fun who => debtTransferRoot source pivot who +
        debtTransferChain (pivot :: rest ++ [target]) who) = _
      rw [ih pivot]
      exact debtTransferRoot_add source pivot target

/-- A two-edge contraction mentions at most its source, intermediate, and
target roles. -/
theorem debtTransferTriangleRoles_card_le_three
    (source middle target : ι) :
    ({source, middle, target} : Finset ι).card ≤ 3 := by
  classical
  calc
    ({source, middle, target} : Finset ι).card ≤
        ({middle, target} : Finset ι).card + 1 :=
      Finset.card_insert_le source {middle, target}
    _ ≤ ({target} : Finset ι).card + 2 := by
      have h := Finset.card_insert_le middle {target}
      omega
    _ ≤ 3 := by simp

/-- Adding one independent calibration/geometry role to a debt triangle
uses at most four roles.  This is the exact combinatorial `3+1` count, not a
strategic cardinal reduction. -/
theorem debtTransferTriangleWithCalibrator_card_le_four
    (source middle target calibrator : ι) :
    ({source, middle, target, calibrator} : Finset ι).card ≤ 4 := by
  classical
  calc
    ({source, middle, target, calibrator} : Finset ι).card ≤
        ({middle, target, calibrator} : Finset ι).card + 1 :=
      Finset.card_insert_le source {middle, target, calibrator}
    _ ≤ 4 := by
      have h := debtTransferTriangleRoles_card_le_three
        middle target calibrator
      omega

end GameTheory
