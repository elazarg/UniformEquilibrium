/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourRationalFiniteClockProfile
import Mathlib.Combinatorics.Colex

/-!
# Rational approximation of normalized Fin4 reward tables

Every real Fin4 reward table in the unit box has a well-formed normalized
rational code at arbitrarily small uniform distance.  Rational coordinates
are first chosen densely and then clamped to `[-1, 1]`; clamping cannot
increase their distance from an already normalized real coordinate.

The existence proof is classical.  Separately, the proof-free reward-code
type already has an `Encodable` instance, so a literal `Nat`-indexed decoder
fairly enumerates every code, including every approximant constructed here.
-/

noncomputable section

namespace GameTheory

open RationalFinFourRewardCode

private theorem exists_normalized_rat_near
    {x delta : ℝ} (hx : |x| ≤ 1) (hdelta : 0 < delta) :
    ∃ q : ℚ, |q| ≤ 1 ∧ |(q : ℝ) - x| < delta := by
  obtain ⟨q, hq⟩ := exists_rat_near x hdelta
  let clamped : ℚ := max (-1) (min 1 q)
  refine ⟨clamped, ?_, ?_⟩
  · dsimp [clamped]
    rw [abs_le]
    constructor <;> simp
  · have hx' : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
    dsimp [clamped]
    by_cases hlow : q < -1
    · have hq_one : q ≤ 1 := le_trans (le_of_lt hlow) (by norm_num)
      rw [min_eq_right hq_one, max_eq_left (le_of_lt hlow)]
      norm_num only [Rat.cast_neg, Rat.cast_one]
      rw [abs_of_nonpos (by linarith)]
      have hlow' : (q : ℝ) < -1 := by exact_mod_cast hlow
      linarith [(abs_lt.mp hq).2]
    · by_cases hhigh : 1 < q
      · rw [min_eq_left (le_of_lt hhigh), max_eq_right (by norm_num)]
        norm_num only [Rat.cast_one]
        rw [abs_of_nonneg (by linarith)]
        have hhigh' : (1 : ℝ) < q := by exact_mod_cast hhigh
        linarith [(abs_lt.mp hq).1]
      · rw [min_eq_right (le_of_not_gt hhigh),
          max_eq_right (le_of_not_gt hlow)]
        simpa [abs_sub_comm] using hq

private def finFourTerminalValSet (terminal : Finset (Fin 4)) : Finset ℕ :=
  terminal.map ⟨Fin.val, Fin.val_injective⟩

private theorem terminalMask_eq_sum_valSet (terminal : Finset (Fin 4)) :
    terminalMask terminal =
      ∑ value ∈ finFourTerminalValSet terminal, 2 ^ value := by
  simp [terminalMask, finFourTerminalValSet]

private theorem terminalMask_injective :
    Function.Injective
      (fun terminal : Finset (Fin 4) ↦ terminalMask terminal) := by
  intro first second heq
  apply Finset.map_injective ⟨Fin.val, Fin.val_injective⟩
  apply Finset.geomSum_injective (n := 2) (by norm_num)
  change (∑ value ∈ finFourTerminalValSet first, 2 ^ value) =
    ∑ value ∈ finFourTerminalValSet second, 2 ^ value
  rw [← terminalMask_eq_sum_valSet, ← terminalMask_eq_sum_valSet]
  exact heq

private theorem terminalMask_pos
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) :
    0 < terminalMask terminal.1 := by
  obtain ⟨player, hplayer⟩ := terminal.2
  unfold terminalMask
  exact Finset.sum_pos (fun _ _ ↦ by positivity) ⟨player, hplayer⟩

private theorem terminalMask_le_fifteen
    (terminal : Finset (Fin 4)) :
    terminalMask terminal ≤ 15 := by
  calc
    terminalMask terminal ≤ ∑ player : Fin 4, 2 ^ player.val := by
      unfold terminalMask
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ terminal) (fun _ _ _ ↦ by positivity)
    _ = 15 := by decide

private def terminalRow
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) : Fin 15 :=
  ⟨terminalMask terminal.1 - 1, by
    have hpos := terminalMask_pos terminal
    have hle := terminalMask_le_fifteen terminal.1
    omega⟩

private theorem terminalRow_injective : Function.Injective terminalRow := by
  intro first second heq
  apply Subtype.ext
  apply terminalMask_injective
  have hfirst := terminalMask_pos first
  have hsecond := terminalMask_pos second
  have hvalue : terminalMask first.1 - 1 =
      terminalMask second.1 - 1 := congrArg Fin.val heq
  calc
    terminalMask first.1 = terminalMask first.1 - 1 + 1 :=
      (Nat.sub_add_cancel hfirst).symm
    _ = terminalMask second.1 - 1 + 1 := congrArg (.+ 1) hvalue
    _ = terminalMask second.1 := Nat.sub_add_cancel hsecond

private noncomputable def terminalAtRow (row : Fin 15) :
    {S : Finset (Fin 4) // S.Nonempty} :=
  if h : ∃ terminal, terminalRow terminal = row then
    Classical.choose h
  else
    ⟨{0}, by simp⟩

private theorem terminalAtRow_terminalRow
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) :
    terminalAtRow (terminalRow terminal) = terminal := by
  rw [terminalAtRow, dif_pos ⟨terminal, rfl⟩]
  apply terminalRow_injective
  exact Classical.choose_spec
    (show ∃ candidate, terminalRow candidate = terminalRow terminal from
      ⟨terminal, rfl⟩)

/-- A normalized rational code together with its literal uniform error bound
against one real Fin4 reward table. -/
structure FinFourRationalRewardApproximation
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (delta : ℝ) where
  code : RationalFinFourRewardCode
  normalized : code.Normalized
  close : ∀ terminal observer,
    |code.realReward terminal observer - reward terminal observer| < delta

/-- Classical coordinatewise construction of a normalized rational Fin4
reward code. -/
theorem nonempty_finFourRationalRewardApproximation
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal observer, |reward terminal observer| ≤ 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    Nonempty (FinFourRationalRewardApproximation reward delta) := by
  choose coordinate hcoordinate using fun terminal observer ↦
    exists_normalized_rat_near (hreward terminal observer) hdelta
  let code : RationalFinFourRewardCode :=
    ⟨List.ofFn fun row : Fin 15 ↦
      List.ofFn fun observer : Fin 4 ↦
        coordinate (terminalAtRow row) observer⟩
  have hwellFormed : code.WellFormed := by
    constructor
    · simp [code]
    · simp [code]
  have hnormalized : code.Normalized := by
    refine ⟨hwellFormed, ?_⟩
    simp only [code, List.forall_mem_ofFn_iff]
    intro row observer
    exact (hcoordinate (terminalAtRow row) observer).1
  refine ⟨⟨code, hnormalized, ?_⟩⟩
  intro terminal observer
  have hrow : terminalMask terminal.1 - 1 < 15 :=
    (terminalRow terminal).isLt
  have hobserver : observer.val < 4 := observer.isLt
  have hindex : (⟨terminalMask terminal.1 - 1, hrow⟩ : Fin 15) =
      terminalRow terminal := by
    apply Fin.ext
    rfl
  have hobserverIndex : (⟨observer.val, hobserver⟩ : Fin 4) =
      observer := by
    apply Fin.ext
    rfl
  change |(code.value terminal observer : ℝ) -
    reward terminal observer| < delta
  rw [show code.value terminal observer = coordinate terminal observer by
    simp only [RationalFinFourRewardCode.value, code]
    rw [List.getElem?_ofFn, dif_pos hrow, Option.bind_some,
      List.getElem?_ofFn, dif_pos hobserver, Option.getD_some,
      hindex, hobserverIndex, terminalAtRow_terminalRow]]
  exact (hcoordinate terminal observer).2

namespace RationalFinFourRewardCode

/-- The `n`th proof-free rational reward-table candidate. -/
def candidateAt (n : ℕ) : Option RationalFinFourRewardCode :=
  Encodable.decode n

/-- Every proof-free rational reward code occurs at a finite candidate index. -/
theorem candidateAt_surjective (code : RationalFinFourRewardCode) :
    ∃ n, candidateAt n = some code := by
  exact ⟨Encodable.encode code, Encodable.encodek code⟩

end RationalFinFourRewardCode

/-- Some finite entry of the executable reward-code enumeration is a
normalized uniform rational approximant. -/
theorem exists_rationalFinFourRewardCandidateAt_normalized_near
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal observer, |reward terminal observer| ≤ 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ n code,
      RationalFinFourRewardCode.candidateAt n = some code ∧
      code.Normalized ∧
      ∀ terminal observer,
        |code.realReward terminal observer - reward terminal observer| < delta := by
  obtain ⟨approximation⟩ :=
    nonempty_finFourRationalRewardApproximation reward hreward hdelta
  obtain ⟨n, hn⟩ :=
    RationalFinFourRewardCode.candidateAt_surjective approximation.code
  exact ⟨n, approximation.code, hn, approximation.normalized,
    approximation.close⟩

/-- Boolean-facing form of fair normalized reward-code coverage, suitable for
an executable outer dovetail. -/
theorem exists_rationalFinFourRewardCandidateAt_normalized_eq_true_near
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal observer, |reward terminal observer| ≤ 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ n code,
      RationalFinFourRewardCode.candidateAt n = some code ∧
      code.normalized = true ∧
      ∀ terminal observer,
        |code.realReward terminal observer - reward terminal observer| < delta := by
  obtain ⟨n, code, hn, hnormalized, hclose⟩ :=
    exists_rationalFinFourRewardCandidateAt_normalized_near
      reward hreward hdelta
  exact ⟨n, code, hn, code.normalized_eq_true_iff.mpr hnormalized, hclose⟩

end GameTheory
