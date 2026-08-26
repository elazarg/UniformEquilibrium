/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.Simplex

/-!
# Finite-clock probability coordinates

This file gives exact finite simplex coordinates for probability mass
functions on `Option Nat` supported before a fixed clock bound.  Coordinates
use `Option (Fin (clockBound + 1))`: the final finite coordinate is an
auxiliary after-support date and is constrained to have zero mass, while
`none` remains a separate literal Never atom.

The construction is game-independent.  It proves both decoding soundness and
encoding completeness, but makes no semialgebraic or decision-procedure claim.
-/

noncomputable section

namespace Math
namespace ProbabilityMassFunction

open Set

/-- Finite clock coordinates: dates through the auxiliary after-support date,
plus a separate Never atom. -/
abbrev FiniteClockAtom (clockBound : ℕ) := Option (Fin (clockBound + 1))

/-- The distinguished auxiliary date immediately after the supported clock. -/
def finiteClockAuxAtom (clockBound : ℕ) : FiniteClockAtom clockBound :=
  some ⟨clockBound, Nat.lt_succ_self clockBound⟩

/-- Interpret a finite coordinate as a deterministic stopping time. -/
def finiteClockAtomToStoppingTime (clockBound : ℕ) :
    FiniteClockAtom clockBound → Option ℕ
  | none => none
  | some time => some time.val

/-- Encode a stopping time into the finite clock, sending every unsupported
finite date to the auxiliary coordinate. -/
def stoppingTimeToFiniteClockAtom (clockBound : ℕ) :
    Option ℕ → FiniteClockAtom clockBound
  | none => none
  | some time =>
      if htime : time < clockBound then
        some ⟨time, htime.trans (Nat.lt_succ_self clockBound)⟩
      else finiteClockAuxAtom clockBound

@[simp] theorem finiteClockAtomToStoppingTime_none (clockBound : ℕ) :
    finiteClockAtomToStoppingTime clockBound none = none := rfl

@[simp] theorem finiteClockAtomToStoppingTime_some
    (clockBound : ℕ) (time : Fin (clockBound + 1)) :
    finiteClockAtomToStoppingTime clockBound (some time) = some time.val := rfl

@[simp] theorem stoppingTimeToFiniteClockAtom_none (clockBound : ℕ) :
    stoppingTimeToFiniteClockAtom clockBound none = none := rfl

@[simp] theorem stoppingTimeToFiniteClockAtom_some_of_lt
    (clockBound time : ℕ) (htime : time < clockBound) :
    stoppingTimeToFiniteClockAtom clockBound (some time) =
      some ⟨time, htime.trans (Nat.lt_succ_self clockBound)⟩ := by
  simp [stoppingTimeToFiniteClockAtom, htime]

@[simp] theorem finiteClockAtomToStoppingTime_encode_of_lt
    (clockBound time : ℕ) (htime : time < clockBound) :
    finiteClockAtomToStoppingTime clockBound
        (stoppingTimeToFiniteClockAtom clockBound (some time)) =
      some time := by
  simp [htime]

/-- Mapping a PMF by a function that fixes every positive-mass atom leaves it
unchanged. -/
theorem PMF.map_eq_self_of_eq_on_support {α : Type*}
    (law : PMF α) (mapChoice : α → α)
    (hfix : ∀ choice, law choice ≠ 0 → mapChoice choice = choice) :
    law.map mapChoice = law := by
  classical
  apply PMF.ext
  intro choice
  rw [PMF.map_apply, tsum_eq_single choice]
  · by_cases hchoice : law choice = 0
    · simp [hchoice]
    · simp [hfix choice hchoice]
  · intro other hother
    by_cases hmass : law other = 0
    · simp [hmass]
    · simp [hfix other hmass, hother.symm]

/-- Push a stopping law into its finite coordinate space. -/
def finiteClockEncodeLaw (clockBound : ℕ) (law : PMF (Option ℕ)) :
    PMF (FiniteClockAtom clockBound) :=
  law.map (stoppingTimeToFiniteClockAtom clockBound)

/-- Real simplex coordinates of the encoded stopping law. -/
def finiteClockLawCoordinates (clockBound : ℕ)
    (law : PMF (Option ℕ)) : FiniteClockAtom clockBound → ℝ :=
  toVector (finiteClockEncodeLaw clockBound law)

theorem finiteClockLawCoordinates_mem_stdSimplex
    (clockBound : ℕ) (law : PMF (Option ℕ)) :
    finiteClockLawCoordinates clockBound law ∈
      stdSimplex ℝ (FiniteClockAtom clockBound) :=
  toVector_mem_stdSimplex _

/-- Decode real simplex weights to a complete stopping law. -/
def finiteClockDecodeLaw (clockBound : ℕ)
    (weight : FiniteClockAtom clockBound → ℝ)
    (hweight : weight ∈ stdSimplex ℝ (FiniteClockAtom clockBound)) :
    PMF (Option ℕ) :=
  (ofVector weight hweight).map (finiteClockAtomToStoppingTime clockBound)

/-- A zero auxiliary coordinate makes the decoded law supported strictly
before the clock bound, with Never retained. -/
theorem finiteClockDecodeLaw_support
    (clockBound : ℕ) (weight : FiniteClockAtom clockBound → ℝ)
    (hweight : weight ∈ stdSimplex ℝ (FiniteClockAtom clockBound))
    (haux : weight (finiteClockAuxAtom clockBound) = 0)
    (choice : Option ℕ) (hchoice : finiteClockDecodeLaw clockBound
      weight hweight choice ≠ 0) :
    choice = none ∨ ∃ time < clockBound, choice = some time := by
  have hmem : choice ∈
      ((ofVector weight hweight).map
        (finiteClockAtomToStoppingTime clockBound)).support := hchoice
  obtain ⟨atom, hatom, hdecode⟩ :=
    (PMF.mem_support_map_iff
      (finiteClockAtomToStoppingTime clockBound)
      (ofVector weight hweight) choice).mp hmem
  cases atom with
  | none =>
      exact Or.inl hdecode.symm
  | some time =>
      have htimeNe : time.val ≠ clockBound := by
        intro htime
        have hatomEq : (some time : FiniteClockAtom clockBound) =
            finiteClockAuxAtom clockBound := by
          apply congrArg some
          apply Fin.ext
          exact htime
        rw [hatomEq] at hatom
        exact hatom (by simp [haux])
      exact Or.inr ⟨time.val, by omega, hdecode.symm⟩

/-- A law supported before the clock bound assigns zero mass to the auxiliary
coordinate after encoding. -/
theorem finiteClockLawCoordinates_aux_eq_zero
    (clockBound : ℕ) (law : PMF (Option ℕ))
    (hsupport : ∀ choice, law choice ≠ 0 →
      choice = none ∨ ∃ time < clockBound, choice = some time) :
    finiteClockLawCoordinates clockBound law
      (finiteClockAuxAtom clockBound) = 0 := by
  unfold finiteClockLawCoordinates toVector
  rw [ENNReal.toReal_eq_zero_iff]
  left
  classical
  rw [finiteClockEncodeLaw, PMF.map_apply, ENNReal.tsum_eq_zero]
  intro choice
  by_cases hmass : law choice = 0
  · simp [hmass]
  · rcases hsupport choice hmass with rfl | ⟨time, htime, rfl⟩
    · simp [finiteClockAuxAtom]
    · simp [stoppingTimeToFiniteClockAtom, htime, finiteClockAuxAtom]
      omega

/-- Encoding and then decoding a supported stopping law is exact. -/
theorem finiteClockDecodeLaw_coordinates
    (clockBound : ℕ) (law : PMF (Option ℕ))
    (hsupport : ∀ choice, law choice ≠ 0 →
      choice = none ∨ ∃ time < clockBound, choice = some time) :
    finiteClockDecodeLaw clockBound
        (finiteClockLawCoordinates clockBound law)
        (finiteClockLawCoordinates_mem_stdSimplex clockBound law) = law := by
  unfold finiteClockDecodeLaw finiteClockLawCoordinates
  rw [ofVector_toVector]
  unfold finiteClockEncodeLaw
  rw [PMF.map_comp]
  apply PMF.map_eq_self_of_eq_on_support
  intro choice hchoice
  cases choice with
  | none => rfl
  | some time =>
      rcases hsupport (some time) hchoice with hnever | ⟨other, hother, heq⟩
      · contradiction
      · cases Option.some.inj heq
        exact finiteClockAtomToStoppingTime_encode_of_lt
          clockBound time hother

/-- Exact finite-coordinate characterization of a law supported before the
clock bound. -/
theorem exists_finiteClockCoordinates_iff
    (clockBound : ℕ) (law : PMF (Option ℕ)) :
    (∃ weight : FiniteClockAtom clockBound → ℝ,
      ∃ hweight : weight ∈ stdSimplex ℝ (FiniteClockAtom clockBound),
        weight (finiteClockAuxAtom clockBound) = 0 ∧
          finiteClockDecodeLaw clockBound weight hweight = law) ↔
      (∀ choice, law choice ≠ 0 →
        choice = none ∨ ∃ time < clockBound, choice = some time) := by
  constructor
  · rintro ⟨weight, hweight, haux, rfl⟩
    exact finiteClockDecodeLaw_support clockBound weight hweight haux
  · intro hsupport
    exact ⟨finiteClockLawCoordinates clockBound law,
      finiteClockLawCoordinates_mem_stdSimplex clockBound law,
      finiteClockLawCoordinates_aux_eq_zero clockBound law hsupport,
      finiteClockDecodeLaw_coordinates clockBound law hsupport⟩

end ProbabilityMassFunction
end Math
