/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import MathUE.Interval.RationalLowerBoxSearch
import Research.Quitting.EscapeAwareQuantileClockPolynomialLower
import Research.Quitting.FinFourSingleShellOuter
import Research.Quitting.FiniteClockPolynomialCenter
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNonsingletonAntiDiffusion
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact rational expression system for one normalized Fin4 shell

This file generates the finite rational lower-box problem attached to one
positive quantile-clock level.  Its data are executable: the only divisions
are divisions of rational constants after the level has been fixed, and the
finite-clock payoff is generated as a factored sum of products rather than by
calling the noncomputable semantic minimum-time definition.

The auxiliary finite date is retained in the expression.  Its center mass is
constrained to zero, but it remains available among the pure deviations whose
finite maximum defines the unrestricted cap.
-/

namespace GameTheory

open Math.Interval Math.ProbabilityMassFunction
open QuittingBoundaryHolonomy

variable {level variableCount : ℕ}

/-- The literal final clock used by the level-`level` Fin4 shell. -/
def finFourSingleShellClock (level : ℕ) : ℕ :=
  quantileClockSupport (Fin 4) level

/-- Number of finite-clock atoms, including the auxiliary date and Never. -/
def finFourSingleShellAtomCount (level : ℕ) : ℕ :=
  finFourSingleShellClock level + 2

/-- Number of marginal mass coordinates. -/
def finFourSingleShellMassCount (level : ℕ) : ℕ :=
  4 * finFourSingleShellAtomCount level

/-- Eight common semantic coordinates, eight center semantic coordinates,
and four finite-clock marginal simplexes. -/
def finFourSingleShellVariableCount (level : ℕ) : ℕ :=
  16 + finFourSingleShellMassCount level

/-- Four simplex, four auxiliary, four payoff, and four cap-tight rows. -/
def finFourSingleShellEqualityCount : ℕ := 16

/-- Mass and cap-upper rows, followed by sixteen shell-neighborhood rows. -/
def finFourSingleShellNonnegativeCount (level : ℕ) : ℕ :=
  2 * finFourSingleShellMassCount level + 16

abbrev FinFourSingleShellExpression (level : ℕ) :=
  RationalMaxExpression (finFourSingleShellVariableCount level)

private def finFourShellOffset
    {offset count : ℕ} (index : Fin count) : Fin (offset + count) :=
  ⟨offset + index, by omega⟩

/-- Common prescribed payoff coordinate. -/
def finFourSingleShellPointPayoffIndex (level : ℕ) (player : Fin 4) :
    Fin (finFourSingleShellVariableCount level) :=
  ⟨player, by simp [finFourSingleShellVariableCount]; omega⟩

/-- Common prescribed cap coordinate. -/
def finFourSingleShellPointCapIndex (level : ℕ) (player : Fin 4) :
    Fin (finFourSingleShellVariableCount level) :=
  ⟨4 + player, by simp [finFourSingleShellVariableCount]; omega⟩

/-- Semantic payoff coordinate of the finite-clock center. -/
def finFourSingleShellCenterPayoffIndex (level : ℕ) (player : Fin 4) :
    Fin (finFourSingleShellVariableCount level) :=
  ⟨8 + player, by simp [finFourSingleShellVariableCount]; omega⟩

/-- Semantic cap coordinate of the finite-clock center. -/
def finFourSingleShellCenterCapIndex (level : ℕ) (player : Fin 4) :
    Fin (finFourSingleShellVariableCount level) :=
  ⟨12 + player, by simp [finFourSingleShellVariableCount]; omega⟩

/-- Computable encoding of one finite-clock marginal coordinate. -/
def finFourSingleShellMassIndex (level : ℕ) (player : Fin 4)
    (atom : FiniteClockAtom (finFourSingleShellClock level)) :
    Fin (finFourSingleShellVariableCount level) :=
  finFourShellOffset
    (offset := 16)
    (finProdFinEquiv (player,
      (finSuccEquiv (finFourSingleShellClock level + 1)).symm atom))

private def finFourSingleShellVariable (level : ℕ)
    (index : Fin (finFourSingleShellVariableCount level)) :
    FinFourSingleShellExpression level :=
  .var index

private def finFourSingleShellSum (count : ℕ)
    (term : Fin count → FinFourSingleShellExpression level) :
    FinFourSingleShellExpression level :=
  (List.ofFn term).foldl (fun total value ↦ total + value) 0

private def finFourSingleShellProduct (count : ℕ)
    (term : Fin count → FinFourSingleShellExpression level) :
    FinFourSingleShellExpression level :=
  (List.ofFn term).foldl (fun total value ↦ total * value) 1

private def finFourSingleShellPlayerProduct
    (term : Fin 4 → FinFourSingleShellExpression level) :
    FinFourSingleShellExpression level :=
  ((term 0 * term 1) * term 2) * term 3

/-- Executable enumeration of the fifteen nonempty Fin4 coalitions. -/
def finFourSingleShellTerminal
    (index : Fin 15) : {S : Finset (Fin 4) // S.Nonempty} :=
  match index.1 with
  | 0 => ⟨{0}, by simp⟩
  | 1 => ⟨{1}, by simp⟩
  | 2 => ⟨{0, 1}, by simp⟩
  | 3 => ⟨{2}, by simp⟩
  | 4 => ⟨{0, 2}, by simp⟩
  | 5 => ⟨{1, 2}, by simp⟩
  | 6 => ⟨{0, 1, 2}, by simp⟩
  | 7 => ⟨{3}, by simp⟩
  | 8 => ⟨{0, 3}, by simp⟩
  | 9 => ⟨{1, 3}, by simp⟩
  | 10 => ⟨{0, 1, 3}, by simp⟩
  | 11 => ⟨{2, 3}, by simp⟩
  | 12 => ⟨{0, 2, 3}, by simp⟩
  | 13 => ⟨{1, 2, 3}, by simp⟩
  | _ => ⟨Finset.univ, Finset.univ_nonempty⟩

private theorem finFourSingleShellTerminal_bijective :
    Function.Bijective finFourSingleShellTerminal := by
  decide

private noncomputable def finFourSingleShellTerminalEquiv :
    Fin 15 ≃ {S : Finset (Fin 4) // S.Nonempty} :=
  Equiv.ofBijective finFourSingleShellTerminal
    finFourSingleShellTerminal_bijective

def finFourSingleShellPointPayoffExpression (level : ℕ)
    (player : Fin 4) : FinFourSingleShellExpression level :=
  finFourSingleShellVariable level
    (finFourSingleShellPointPayoffIndex level player)

def finFourSingleShellPointCapExpression (level : ℕ)
    (player : Fin 4) : FinFourSingleShellExpression level :=
  finFourSingleShellVariable level
    (finFourSingleShellPointCapIndex level player)

def finFourSingleShellCenterPayoffExpression (level : ℕ)
    (player : Fin 4) : FinFourSingleShellExpression level :=
  finFourSingleShellVariable level
    (finFourSingleShellCenterPayoffIndex level player)

def finFourSingleShellCenterCapExpression (level : ℕ)
    (player : Fin 4) : FinFourSingleShellExpression level :=
  finFourSingleShellVariable level
    (finFourSingleShellCenterCapIndex level player)

def finFourSingleShellMassExpression (level : ℕ) (player : Fin 4)
    (atom : FiniteClockAtom (finFourSingleShellClock level)) :
    FinFourSingleShellExpression level :=
  finFourSingleShellVariable level
    (finFourSingleShellMassIndex level player atom)

/-- Substitute one deterministic finite-clock atom for one player's marginal.
This is used only to generate the finite pure-deviation cap rows. -/
def finFourSingleShellSubstitutedMassExpression (level : ℕ)
    (mover : Fin 4)
    (candidate : FiniteClockAtom (finFourSingleShellClock level))
    (player : Fin 4)
    (atom : FiniteClockAtom (finFourSingleShellClock level)) :
    FinFourSingleShellExpression level :=
  if player = mover then
    if atom = candidate then 1 else 0
  else
    finFourSingleShellMassExpression level player atom

/-- Exact later-or-Never mass after an extended finite-clock date. -/
def finFourSingleShellTailExpression (level : ℕ)
    (mass : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) →
      FinFourSingleShellExpression level)
    (player : Fin 4)
    (time : Fin (finFourSingleShellClock level + 1)) :
    FinFourSingleShellExpression level :=
  mass player none +
    finFourSingleShellSum (finFourSingleShellClock level + 1) fun later ↦
      if time < later then mass player (some later) else 0

/-- One coalition's exact product mass at one extended finite date. -/
def finFourSingleShellCoalitionMassExpression (level : ℕ)
    (mass : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) →
      FinFourSingleShellExpression level)
    (time : Fin (finFourSingleShellClock level + 1))
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) :
    FinFourSingleShellExpression level :=
  finFourSingleShellPlayerProduct fun player ↦
    if player ∈ terminal.1 then mass player (some time)
    else finFourSingleShellTailExpression level mass player time

/-- Factored exact terminal payoff for one finite-clock product assignment.
The time range includes the auxiliary after-support date, so substituting the
auxiliary atom represents the last payoff-distinct pure finite deviation. -/
def finFourSingleShellPayoffExpression
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (mass : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) →
      FinFourSingleShellExpression level)
    (observer : Fin 4) : FinFourSingleShellExpression level :=
  finFourSingleShellSum (finFourSingleShellClock level + 1) fun time ↦
    finFourSingleShellSum 15 fun terminalIndex ↦
      let terminal := finFourSingleShellTerminal terminalIndex
      .constant (reward terminal observer) *
        finFourSingleShellCoalitionMassExpression level mass time terminal

def finFourSingleShellOnProfilePayoffExpression
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ) (observer : Fin 4) :
    FinFourSingleShellExpression level :=
  finFourSingleShellPayoffExpression reward level
    (finFourSingleShellMassExpression level) observer

def finFourSingleShellDeviationPayoffExpression
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ) (mover : Fin 4)
    (candidate : FiniteClockAtom (finFourSingleShellClock level)) :
    FinFourSingleShellExpression level :=
  finFourSingleShellPayoffExpression reward level
    (finFourSingleShellSubstitutedMassExpression level mover candidate) mover

def finFourSingleShellSimplexExpression (level : ℕ) (player : Fin 4) :
    FinFourSingleShellExpression level :=
  finFourSingleShellSum
      (finFourSingleShellAtomCount level)
      (fun index ↦ finFourSingleShellMassExpression level player
        (finSuccEquiv (finFourSingleShellClock level + 1) index)) - 1

def finFourSingleShellAuxiliaryExpression (level : ℕ) (player : Fin 4) :
    FinFourSingleShellExpression level :=
  finFourSingleShellMassExpression level player
    (finiteClockAuxAtom (finFourSingleShellClock level))

def finFourSingleShellPayoffConsistencyExpression
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ) (player : Fin 4) :
    FinFourSingleShellExpression level :=
  finFourSingleShellCenterPayoffExpression level player -
    finFourSingleShellOnProfilePayoffExpression reward level player

def finFourSingleShellCapUpperExpression
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ) (player : Fin 4)
    (candidate : FiniteClockAtom (finFourSingleShellClock level)) :
    FinFourSingleShellExpression level :=
  finFourSingleShellCenterCapExpression level player -
    finFourSingleShellDeviationPayoffExpression reward level player candidate

def finFourSingleShellCapTightExpression
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ) (player : Fin 4) :
    FinFourSingleShellExpression level :=
  finFourSingleShellProduct
    (finFourSingleShellAtomCount level)
    (fun index ↦ finFourSingleShellCapUpperExpression reward level player
      (finSuccEquiv (finFourSingleShellClock level + 1) index))

/-- Rational `12 / level` shell radius. -/
def finFourSingleShellRadiusRat (level : ℕ) : ℚ :=
  12 / level

/-- One of the sixteen signed coordinatewise shell inequalities. -/
def finFourSingleShellNeighborhoodExpression (level : ℕ)
    (player : Fin 4) (capCoordinate reverse : Bool) :
    FinFourSingleShellExpression level :=
  let point := if capCoordinate then
    finFourSingleShellPointCapExpression level player
  else
    finFourSingleShellPointPayoffExpression level player
  let center := if capCoordinate then
    finFourSingleShellCenterCapExpression level player
  else
    finFourSingleShellCenterPayoffExpression level player
  let difference := point - center
  .constant (finFourSingleShellRadiusRat level) +
    if reverse then difference else -difference

/-- `max (0, b₀-u₀, ..., b₃-u₃)`. -/
def finFourSingleShellObjectiveExpression (level : ℕ) :
    FinFourSingleShellExpression level :=
  .max 0 (.max
    (finFourSingleShellPointCapExpression level 0 -
      finFourSingleShellPointPayoffExpression level 0)
    (.max
      (finFourSingleShellPointCapExpression level 1 -
        finFourSingleShellPointPayoffExpression level 1)
      (.max
        (finFourSingleShellPointCapExpression level 2 -
          finFourSingleShellPointPayoffExpression level 2)
        (finFourSingleShellPointCapExpression level 3 -
          finFourSingleShellPointPayoffExpression level 3))))

private def finFourSingleShellMassCoordinate (level : ℕ)
    (index : Fin (finFourSingleShellMassCount level)) :
    Fin 4 × FiniteClockAtom (finFourSingleShellClock level) :=
  let pair := finProdFinEquiv.symm index
  (pair.1, finSuccEquiv (finFourSingleShellClock level + 1) pair.2)

/-- The sixteen equality rows, decoded without classical finite equivalences. -/
def finFourSingleShellEqualityExpression
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ) (index : Fin finFourSingleShellEqualityCount) :
    FinFourSingleShellExpression level :=
  let row : Fin 4 × Fin 4 := finProdFinEquiv.symm
    (Fin.cast (by norm_num [finFourSingleShellEqualityCount]) index)
  match row.1.1 with
  | 0 => finFourSingleShellSimplexExpression level row.2
  | 1 => finFourSingleShellAuxiliaryExpression level row.2
  | 2 => finFourSingleShellPayoffConsistencyExpression reward level row.2
  | _ => finFourSingleShellCapTightExpression reward level row.2

/-- Executable index of one `(row-kind, player)` equality constraint. -/
def finFourSingleShellEqualityIndex (kind player : Fin 4) :
    Fin finFourSingleShellEqualityCount :=
  Fin.cast (by norm_num [finFourSingleShellEqualityCount])
    (finProdFinEquiv (kind, player))

/-- The mass, cap-upper, and shell-neighborhood nonnegative rows. -/
def finFourSingleShellNonnegativeExpression
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (index : Fin (finFourSingleShellNonnegativeCount level)) :
    FinFourSingleShellExpression level :=
  match finSumFinEquiv.symm index with
  | .inl centerIndex =>
      let row := finProdFinEquiv.symm centerIndex
      let coordinate := finFourSingleShellMassCoordinate level row.2
      if row.1.1 = 0 then
        finFourSingleShellMassExpression level coordinate.1 coordinate.2
      else
        finFourSingleShellCapUpperExpression reward level
          coordinate.1 coordinate.2
  | .inr neighborhoodIndex =>
      let row : Fin 4 × Fin 4 := finProdFinEquiv.symm
        (Fin.cast (by norm_num) neighborhoodIndex)
      finFourSingleShellNeighborhoodExpression level row.2
        (decide (row.1.1 / 2 = 1)) (decide (row.1.1 % 2 = 1))

private def finFourSingleShellMassFlatIndex (level : ℕ) (player : Fin 4)
    (atom : FiniteClockAtom (finFourSingleShellClock level)) :
    Fin (finFourSingleShellMassCount level) :=
  finProdFinEquiv
    (player, (finSuccEquiv (finFourSingleShellClock level + 1)).symm atom)

/-- Executable index of one marginal nonnegativity row. -/
def finFourSingleShellMassNonnegativeIndex (level : ℕ) (player : Fin 4)
    (atom : FiniteClockAtom (finFourSingleShellClock level)) :
    Fin (finFourSingleShellNonnegativeCount level) :=
  finSumFinEquiv (.inl (finProdFinEquiv
    ((0 : Fin 2), finFourSingleShellMassFlatIndex level player atom)))

/-- Executable index of one pure-candidate cap upper-bound row. -/
def finFourSingleShellCapNonnegativeIndex (level : ℕ) (player : Fin 4)
    (candidate : FiniteClockAtom (finFourSingleShellClock level)) :
    Fin (finFourSingleShellNonnegativeCount level) :=
  finSumFinEquiv (.inl (finProdFinEquiv
    ((1 : Fin 2), finFourSingleShellMassFlatIndex level player candidate)))

private def finFourSingleShellNeighborhoodKind : Bool → Bool → Fin 4
  | false, false => 0
  | false, true => 1
  | true, false => 2
  | true, true => 3

/-- Executable index of one signed semantic-neighborhood row. -/
def finFourSingleShellNeighborhoodNonnegativeIndex (level : ℕ)
    (player : Fin 4) (capCoordinate reverse : Bool) :
    Fin (finFourSingleShellNonnegativeCount level) :=
  finSumFinEquiv (.inr (Fin.cast (by norm_num)
    (finProdFinEquiv
      (finFourSingleShellNeighborhoodKind capCoordinate reverse, player))))

private theorem finFourSingleShellEqualityExpression_index
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ) (kind player : Fin 4) :
    finFourSingleShellEqualityExpression reward level
        (finFourSingleShellEqualityIndex kind player) =
      match kind.1 with
      | 0 => finFourSingleShellSimplexExpression level player
      | 1 => finFourSingleShellAuxiliaryExpression level player
      | 2 => finFourSingleShellPayoffConsistencyExpression reward level player
      | _ => finFourSingleShellCapTightExpression reward level player := by
  simp [finFourSingleShellEqualityExpression,
    finFourSingleShellEqualityIndex]

private theorem finFourSingleShellNonnegativeExpression_massIndex
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ) (player : Fin 4)
    (atom : FiniteClockAtom (finFourSingleShellClock level)) :
    finFourSingleShellNonnegativeExpression reward level
        (finFourSingleShellMassNonnegativeIndex level player atom) =
      finFourSingleShellMassExpression level player atom := by
  simp [finFourSingleShellNonnegativeExpression,
    finFourSingleShellMassNonnegativeIndex,
    finFourSingleShellMassFlatIndex,
    finFourSingleShellMassCoordinate]

private theorem finFourSingleShellNonnegativeExpression_capIndex
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ) (player : Fin 4)
    (candidate : FiniteClockAtom (finFourSingleShellClock level)) :
    finFourSingleShellNonnegativeExpression reward level
        (finFourSingleShellCapNonnegativeIndex level player candidate) =
      finFourSingleShellCapUpperExpression reward level player candidate := by
  simp [finFourSingleShellNonnegativeExpression,
    finFourSingleShellCapNonnegativeIndex,
    finFourSingleShellMassFlatIndex,
    finFourSingleShellMassCoordinate]

private theorem finFourSingleShellNonnegativeExpression_neighborhoodIndex
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ) (player : Fin 4) (capCoordinate reverse : Bool) :
    finFourSingleShellNonnegativeExpression reward level
        (finFourSingleShellNeighborhoodNonnegativeIndex level player
          capCoordinate reverse) =
      finFourSingleShellNeighborhoodExpression level player
        capCoordinate reverse := by
  cases capCoordinate <;> cases reverse <;>
    simp [finFourSingleShellNonnegativeExpression,
      finFourSingleShellNeighborhoodNonnegativeIndex,
      finFourSingleShellNeighborhoodKind]

/-- Compact rational root box.  Common semantic coordinates use the shell
radius; center semantic coordinates use normalized reward bounds; marginal
masses use the unit interval. -/
def finFourSingleShellRootBox (level : ℕ) :
    RationalBox (finFourSingleShellVariableCount level) :=
  fun index =>
    if index.1 < 8 then
      ⟨-1 - finFourSingleShellRadiusRat level,
        1 + finFourSingleShellRadiusRat level⟩
    else if index.1 < 16 then
      ⟨-1, 1⟩
    else
      ⟨0, 1⟩

/-- Every coordinate interval in the executable root box is ordered. -/
theorem finFourSingleShellRootBox_valid (level : ℕ) :
    RationalLowerBoxProblem.RationalBox.Valid
      (finFourSingleShellRootBox level) := by
  intro index
  unfold finFourSingleShellRootBox RationalInterval.Valid
  split
  · have hradius : 0 ≤ finFourSingleShellRadiusRat level := by
      unfold finFourSingleShellRadiusRat
      apply div_nonneg
      · norm_num
      · exact_mod_cast Nat.zero_le level
    linarith
  · split <;> norm_num

/-- Fully executable exact-rational lower problem for the final Fin4 shell. -/
def finFourRationalSingleShellLowerProblem
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ) : RationalLowerBoxProblem
      (finFourSingleShellVariableCount level)
      finFourSingleShellEqualityCount
      (finFourSingleShellNonnegativeCount level) where
  root := finFourSingleShellRootBox level
  equality := finFourSingleShellEqualityExpression reward level
  nonnegative := finFourSingleShellNonnegativeExpression reward level
  objective := finFourSingleShellObjectiveExpression level

/-- Semantic pair represented by the eight common coordinates. -/
def finFourSingleShellPointPair (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ) :
    QuittingTerminalSemanticPair (Fin 4) :=
  (⟨fun player => assign (finFourSingleShellPointPayoffIndex level player),
    fun player => assign (finFourSingleShellPointCapIndex level player)⟩)

/-- Semantic center represented by its eight explicit coordinates. -/
def finFourSingleShellCenterPair (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ) :
    QuittingTerminalSemanticPair (Fin 4) :=
  (⟨fun player => assign (finFourSingleShellCenterPayoffIndex level player),
    fun player => assign (finFourSingleShellCenterCapIndex level player)⟩)

/-- Flat assignment assembled from one common semantic point, one semantic
center, and one family of finite-clock marginal weights. -/
def finFourSingleShellAssignmentOfData (level : ℕ)
    (point center : QuittingTerminalSemanticPair (Fin 4))
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ) :
    Fin (finFourSingleShellVariableCount level) → ℝ :=
  fun index ↦
    if hpointPayoff : index.1 < 4 then
      point.1 ⟨index.1, hpointPayoff⟩
    else if hpointCap : index.1 < 8 then
      point.2 ⟨index.1 - 4, by omega⟩
    else if hcenterPayoff : index.1 < 12 then
      center.1 ⟨index.1 - 8, by omega⟩
    else if hcenterCap : index.1 < 16 then
      center.2 ⟨index.1 - 12, by omega⟩
    else
      let massIndex : Fin
          (4 * (finFourSingleShellClock level + 1 + 1)) :=
        ⟨index.1 - 16, by
          have hbound := index.2
          simp only [finFourSingleShellVariableCount,
            finFourSingleShellMassCount, finFourSingleShellAtomCount] at hbound
          omega⟩
      let coordinate := finProdFinEquiv.symm massIndex
      weight coordinate.1
        (finSuccEquiv (finFourSingleShellClock level + 1) coordinate.2)

@[simp] theorem finFourSingleShellAssignmentOfData_pointPayoff
    (level : ℕ) (point center : QuittingTerminalSemanticPair (Fin 4))
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (player : Fin 4) :
    finFourSingleShellAssignmentOfData level point center weight
        (finFourSingleShellPointPayoffIndex level player) = point.1 player := by
  fin_cases player <;> simp [finFourSingleShellAssignmentOfData,
    finFourSingleShellPointPayoffIndex]

@[simp] theorem finFourSingleShellAssignmentOfData_pointCap
    (level : ℕ) (point center : QuittingTerminalSemanticPair (Fin 4))
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (player : Fin 4) :
    finFourSingleShellAssignmentOfData level point center weight
        (finFourSingleShellPointCapIndex level player) = point.2 player := by
  fin_cases player <;> simp [finFourSingleShellAssignmentOfData,
    finFourSingleShellPointCapIndex]

@[simp] theorem finFourSingleShellAssignmentOfData_centerPayoff
    (level : ℕ) (point center : QuittingTerminalSemanticPair (Fin 4))
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (player : Fin 4) :
    finFourSingleShellAssignmentOfData level point center weight
        (finFourSingleShellCenterPayoffIndex level player) = center.1 player := by
  fin_cases player <;> simp [finFourSingleShellAssignmentOfData,
    finFourSingleShellCenterPayoffIndex]

@[simp] theorem finFourSingleShellAssignmentOfData_centerCap
    (level : ℕ) (point center : QuittingTerminalSemanticPair (Fin 4))
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (player : Fin 4) :
    finFourSingleShellAssignmentOfData level point center weight
        (finFourSingleShellCenterCapIndex level player) = center.2 player := by
  fin_cases player <;> simp [finFourSingleShellAssignmentOfData,
    finFourSingleShellCenterCapIndex]

@[simp] theorem finFourSingleShellAssignmentOfData_mass
    (level : ℕ) (point center : QuittingTerminalSemanticPair (Fin 4))
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (player : Fin 4)
    (atom : FiniteClockAtom (finFourSingleShellClock level)) :
    finFourSingleShellAssignmentOfData level point center weight
        (finFourSingleShellMassIndex level player atom) = weight player atom := by
  rw [finFourSingleShellMassIndex, finFourShellOffset]
  simp only [finFourSingleShellAssignmentOfData]
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split
        · omega
        · let encoded := finProdFinEquiv
            (player,
              (finSuccEquiv (finFourSingleShellClock level + 1)).symm atom)
          let recovered : Fin
              (4 * (finFourSingleShellClock level + 1 + 1)) :=
            ⟨16 + encoded.1 - 16, by
              simpa only [Nat.add_sub_cancel_left] using encoded.2⟩
          change weight (finProdFinEquiv.symm recovered).1
              ((finSuccEquiv (finFourSingleShellClock level + 1))
                (finProdFinEquiv.symm recovered).2) = weight player atom
          have hrecovered : recovered = encoded := by
            apply Fin.ext
            dsimp [recovered]
            omega
          rw [hrecovered, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- Marginal weights read from a flat assignment. -/
def finFourSingleShellWeight (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (player : Fin 4)
    (atom : FiniteClockAtom (finFourSingleShellClock level)) : ℝ :=
  assign (finFourSingleShellMassIndex level player atom)

@[simp] theorem finFourSingleShellWeight_assignmentOfData
    (level : ℕ) (point center : QuittingTerminalSemanticPair (Fin 4))
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ) :
    finFourSingleShellWeight level
      (finFourSingleShellAssignmentOfData level point center weight) = weight := by
  funext player atom
  exact finFourSingleShellAssignmentOfData_mass
    level point center weight player atom

/-- Real one-hot substitution used by a generated pure-deviation row. -/
def finFourSingleShellSubstitutedWeight (level : ℕ)
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (mover : Fin 4)
    (candidate : FiniteClockAtom (finFourSingleShellClock level))
    (player : Fin 4)
    (atom : FiniteClockAtom (finFourSingleShellClock level)) : ℝ :=
  if player = mover then if atom = candidate then 1 else 0
  else weight player atom

theorem finFourSingleShellSubstitutedWeight_mem_stdSimplex
    (level : ℕ)
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (hweight : ∀ player, weight player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (mover : Fin 4)
    (candidate : FiniteClockAtom (finFourSingleShellClock level))
    (player : Fin 4) :
    finFourSingleShellSubstitutedWeight level weight mover candidate player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)) := by
  by_cases hplayer : player = mover
  · subst player
    constructor
    · intro atom
      simp only [finFourSingleShellSubstitutedWeight, ↓reduceIte]
      split <;> norm_num
    · simp [finFourSingleShellSubstitutedWeight]
  · convert hweight player using 1
    funext atom
    simp [finFourSingleShellSubstitutedWeight, hplayer]

private theorem evalReal_foldl_add
    (assign : Fin variableCount → ℝ)
    (expressions : List (RationalMaxExpression variableCount))
    (initial : RationalMaxExpression variableCount) :
    RationalMaxExpression.evalReal assign
        (expressions.foldl (fun total value ↦ total + value) initial) =
      (expressions.map (RationalMaxExpression.evalReal assign)).foldl
        (fun total value ↦ total + value)
        (RationalMaxExpression.evalReal assign initial) := by
  induction expressions generalizing initial with
  | nil => rfl
  | cons head tail hinduction =>
      rw [List.foldl_cons, hinduction]
      rfl

private theorem evalReal_foldl_mul
    (assign : Fin variableCount → ℝ)
    (expressions : List (RationalMaxExpression variableCount))
    (initial : RationalMaxExpression variableCount) :
    RationalMaxExpression.evalReal assign
        (expressions.foldl (fun total value ↦ total * value) initial) =
      (expressions.map (RationalMaxExpression.evalReal assign)).foldl
        (fun total value ↦ total * value)
        (RationalMaxExpression.evalReal assign initial) := by
  induction expressions generalizing initial with
  | nil => rfl
  | cons head tail hinduction =>
      rw [List.foldl_cons, hinduction]
      rfl

private theorem evalReal_finFourSingleShellSum
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (count : ℕ) (term : Fin count → FinFourSingleShellExpression level) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellSum count term) =
      ∑ index, RationalMaxExpression.evalReal assign (term index) := by
  rw [finFourSingleShellSum, evalReal_foldl_add]
  simp only [RationalMaxExpression.evalReal, Rat.cast_zero]
  change (List.map (RationalMaxExpression.evalReal assign)
      (List.ofFn term)).foldl (fun total value ↦ total + value) 0 = _
  rw [← List.sum_eq_foldl]
  rw [List.map_ofFn]
  exact List.sum_ofFn

private theorem evalReal_finFourSingleShellProduct
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (count : ℕ) (term : Fin count → FinFourSingleShellExpression level) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellProduct count term) =
      ∏ index, RationalMaxExpression.evalReal assign (term index) := by
  rw [finFourSingleShellProduct, evalReal_foldl_mul]
  simp only [RationalMaxExpression.evalReal, Rat.cast_one]
  change (List.map (RationalMaxExpression.evalReal assign)
      (List.ofFn term)).foldl (fun total value ↦ total * value) 1 = _
  rw [← List.prod_eq_foldl]
  rw [List.map_ofFn]
  exact List.prod_ofFn

/-- Real later-or-Never mass represented by an assignment. -/
def finFourSingleShellTailMass (level : ℕ)
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (player : Fin 4)
    (time : Fin (finFourSingleShellClock level + 1)) : ℝ :=
  weight player none +
    ∑ later : Fin (finFourSingleShellClock level + 1),
      if time < later then weight player (some later) else 0

/-- Real product mass of one earliest coalition at one extended date. -/
def finFourSingleShellCoalitionMass (level : ℕ)
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (time : Fin (finFourSingleShellClock level + 1))
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) : ℝ :=
  ∏ player, if player ∈ terminal.1 then weight player (some time)
    else finFourSingleShellTailMass level weight player time

/-- The real factored payoff represented by the executable expression. -/
def finFourSingleShellPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (observer : Fin 4) : ℝ :=
  ∑ time : Fin (finFourSingleShellClock level + 1),
    ∑ terminalIndex : Fin 15,
      (reward (finFourSingleShellTerminal terminalIndex) observer : ℝ) *
        finFourSingleShellCoalitionMass level weight time
          (finFourSingleShellTerminal terminalIndex)

private theorem evalReal_finFourSingleShellTailExpression
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (mass : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) →
      FinFourSingleShellExpression level)
    (player : Fin 4)
    (time : Fin (finFourSingleShellClock level + 1)) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellTailExpression level mass player time) =
      finFourSingleShellTailMass level
        (fun who atom ↦ RationalMaxExpression.evalReal assign (mass who atom))
        player time := by
  simp only [finFourSingleShellTailExpression, finFourSingleShellTailMass,
    RationalMaxExpression.evalReal, evalReal_finFourSingleShellSum, apply_ite,
    Rat.cast_zero]

private theorem evalReal_finFourSingleShellCoalitionMassExpression
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (mass : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) →
      FinFourSingleShellExpression level)
    (time : Fin (finFourSingleShellClock level + 1))
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellCoalitionMassExpression level mass time terminal) =
      finFourSingleShellCoalitionMass level
        (fun who atom ↦ RationalMaxExpression.evalReal assign (mass who atom))
        time terminal := by
  unfold finFourSingleShellCoalitionMassExpression
    finFourSingleShellPlayerProduct finFourSingleShellCoalitionMass
  rw [Fin.prod_univ_four]
  by_cases hzero : (0 : Fin 4) ∈ terminal.1 <;>
    by_cases hone : (1 : Fin 4) ∈ terminal.1 <;>
    by_cases htwo : (2 : Fin 4) ∈ terminal.1 <;>
    by_cases hthree : (3 : Fin 4) ∈ terminal.1 <;>
    simp [hzero, hone, htwo, hthree, RationalMaxExpression.evalReal,
      evalReal_finFourSingleShellTailExpression]

private theorem evalReal_finFourSingleShellSubstitutedMassExpression
    (level : ℕ) (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (mover : Fin 4)
    (candidate atom : FiniteClockAtom (finFourSingleShellClock level))
    (player : Fin 4) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellSubstitutedMassExpression level mover candidate
          player atom) =
      finFourSingleShellSubstitutedWeight level
        (finFourSingleShellWeight level assign) mover candidate player atom := by
  by_cases hplayer : player = mover
  · subst player
    by_cases hatom : atom = candidate <;>
      simp [finFourSingleShellSubstitutedMassExpression,
        finFourSingleShellSubstitutedWeight, hatom,
        RationalMaxExpression.evalReal]
  · simp [finFourSingleShellSubstitutedMassExpression,
      finFourSingleShellSubstitutedWeight, hplayer,
      finFourSingleShellMassExpression, finFourSingleShellWeight,
      finFourSingleShellVariable, RationalMaxExpression.evalReal]

/-- Exact expression evaluation agrees with the factored real payoff. -/
theorem evalReal_finFourSingleShellPayoffExpression
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (mass : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) →
      FinFourSingleShellExpression level)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (observer : Fin 4) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellPayoffExpression reward level mass observer) =
      finFourSingleShellPayoff reward level
        (fun who atom ↦ RationalMaxExpression.evalReal assign (mass who atom))
        observer := by
  simp only [finFourSingleShellPayoffExpression, finFourSingleShellPayoff,
    evalReal_finFourSingleShellSum, RationalMaxExpression.evalReal,
    evalReal_finFourSingleShellCoalitionMassExpression]

/-- A generated deviation row evaluates to the factored real payoff of the
corresponding one-hot substituted marginal. -/
theorem evalReal_finFourSingleShellDeviationPayoffExpression_eq_factored
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (mover : Fin 4)
    (candidate : FiniteClockAtom (finFourSingleShellClock level)) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellDeviationPayoffExpression reward level mover
          candidate) =
      finFourSingleShellPayoff reward level
        (finFourSingleShellSubstitutedWeight level
          (finFourSingleShellWeight level assign) mover candidate) mover := by
  rw [finFourSingleShellDeviationPayoffExpression,
    evalReal_finFourSingleShellPayoffExpression]
  congr 2
  funext player atom
  exact evalReal_finFourSingleShellSubstitutedMassExpression
    level assign mover candidate atom player

private theorem finiteClockAtomToStoppingTime_injective (clock : ℕ) :
    Function.Injective (finiteClockAtomToStoppingTime clock) := by
  intro first second heq
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some second => simp at heq
  | some first =>
      cases second with
      | none => simp at heq
      | some second =>
          simp only [finiteClockAtomToStoppingTime_some,
            Option.some.injEq] at heq
          exact congrArg some (Fin.ext heq)

private theorem finiteClockDecodeLaw_apply_toReal
    (clock : ℕ) (weight : FiniteClockAtom clock → ℝ)
    (hweight : weight ∈ stdSimplex ℝ (FiniteClockAtom clock))
    (atom : FiniteClockAtom clock) :
    (finiteClockDecodeLaw clock weight hweight
      (finiteClockAtomToStoppingTime clock atom)).toReal = weight atom := by
  unfold finiteClockDecodeLaw
  rw [PMF.map_apply, tsum_eq_single atom]
  · simp only [if_pos]
    exact ofVector_toReal hweight atom
  · intro other hother
    have hne : finiteClockAtomToStoppingTime clock other ≠
        finiteClockAtomToStoppingTime clock atom := by
      exact fun heq ↦ hother (finiteClockAtomToStoppingTime_injective clock heq)
    simp [Ne.symm hne]

private theorem sum_fin_eq_sum_range
    {count : ℕ} (value : Fin count → ℝ) :
    (∑ index, value index) =
      ∑ index ∈ Finset.range count,
        if hindex : index < count then value ⟨index, hindex⟩ else 0 := by
  simpa only [Finset.mem_range, Fin.isLt, dif_pos] using
    (Fin.sum_univ_eq_sum_range
      (fun index ↦ if hindex : index < count then value ⟨index, hindex⟩ else 0)
      count)

private theorem sum_fin_eq_castLE_add_sum_gt
    {count : ℕ} (time : Fin count) (value : Fin count → ℝ) :
    (∑ index, value index) =
      (∑ index : Fin (time.1 + 1),
        value (Fin.castLE (by omega) index)) +
      ∑ index : Fin count, if time < index then value index else 0 := by
  rw [sum_fin_eq_sum_range, sum_fin_eq_sum_range, sum_fin_eq_sum_range]
  rw [← Finset.sum_range_add_sum_Ico (f := fun index ↦
    if hindex : index < count then value ⟨index, hindex⟩ else 0)
      (by omega : time.1 + 1 ≤ count)]
  congr 1
  · apply Finset.sum_congr rfl
    intro index hindex
    simp only [Finset.mem_range] at hindex
    have hcount : index < count :=
      lt_of_lt_of_le hindex time.isLt
    simp only [dif_pos hcount, dif_pos hindex]
    congr 1
  · have hset : Finset.Ico (time.1 + 1) count =
        (Finset.range count).filter (fun index ↦ time.1 < index) := by
      ext index
      simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
      omega
    rw [hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro index hindex
    simp only [Finset.mem_range] at hindex
    simp only [dif_pos hindex]
    change (if time.1 < index then value ⟨index, hindex⟩ else 0) =
      if time.1 < index then value ⟨index, hindex⟩ else 0
    rfl

private theorem finiteClockDecoded_survival_eq_tailMass
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (level : ℕ)
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (hweight : ∀ player, weight player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (player : Fin 4)
    (time : Fin (finFourSingleShellClock level + 1)) :
    quittingHazardSurvival
        (quittingBehaviorLiveHazard reward
          (finiteClockDecodedProfile reward (finFourSingleShellClock level)
            weight hweight player)) (time.1 + 1) =
      finFourSingleShellTailMass level weight player time := by
  let hazard := quittingBehaviorLiveHazard reward
    (finiteClockDecodedProfile reward (finFourSingleShellClock level)
      weight hweight player)
  have hprefix :
      (∑ date : Fin (time.1 + 1),
          quittingHazardStopMass hazard date.1) =
        ∑ date : Fin (time.1 + 1), weight player
          (some (Fin.castLE (by omega) date)) := by
    apply Fintype.sum_congr
    intro date
    rw [← quittingBehaviorStoppingLaw_some_toReal]
    rw [finiteClockDecodedProfile,
      quittingBehaviorStoppingLaw_stoppingLawProfile]
    exact finiteClockDecodeLaw_apply_toReal
      (finFourSingleShellClock level) (weight player) (hweight player)
      (some (Fin.castLE (by omega) date))
  have htotal : weight player none +
      ∑ later : Fin (finFourSingleShellClock level + 1),
        weight player (some later) = 1 := by
    simpa only [Fintype.sum_option] using (hweight player).2
  calc
    quittingHazardSurvival hazard (time.1 + 1) =
        1 - ∑ date ∈ Finset.range (time.1 + 1),
          quittingHazardStopMass hazard date := by
      rw [sum_quittingHazardStopMass]
      ring
    _ = 1 - ∑ date : Fin (time.1 + 1),
          quittingHazardStopMass hazard date.1 := by
      rw [Fin.sum_univ_eq_sum_range]
    _ = 1 - ∑ date : Fin (time.1 + 1), weight player
          (some (Fin.castLE (by omega) date)) := by rw [hprefix]
    _ = finFourSingleShellTailMass level weight player time := by
      rw [← htotal,
        sum_fin_eq_castLE_add_sum_gt time (fun later ↦
          weight player (some later))]
      simp only [finFourSingleShellTailMass]
      ring

private theorem finiteClockDecodeLaw_apply_eq_zero_of_clock_lt
    (clock date : ℕ) (hclock : clock < date)
    (weight : FiniteClockAtom clock → ℝ)
    (hweight : weight ∈ stdSimplex ℝ (FiniteClockAtom clock)) :
    finiteClockDecodeLaw clock weight hweight (some date) = 0 := by
  apply Classical.byContradiction
  intro hne
  have hmem : some date ∈
      (finiteClockDecodeLaw clock weight hweight).support := hne
  obtain ⟨atom, hatom, hmap⟩ :=
    (PMF.mem_support_map_iff
      (finiteClockAtomToStoppingTime clock)
      (ofVector weight hweight) (some date)).mp hmem
  cases atom with
  | none => simp at hmap
  | some atom =>
      simp only [finiteClockAtomToStoppingTime_some,
        Option.some.injEq] at hmap
      omega

private theorem finiteClockDecodeLaw_oneHot
    (clock : ℕ) (candidate : FiniteClockAtom clock)
    (oneHot : FiniteClockAtom clock → ℝ)
    (honeHot : oneHot = fun atom ↦ if atom = candidate then 1 else 0)
    (hsimplex : oneHot ∈ stdSimplex ℝ (FiniteClockAtom clock)) :
    finiteClockDecodeLaw clock oneHot hsimplex =
      PMF.pure (finiteClockAtomToStoppingTime clock candidate) := by
  have hvector : ofVector oneHot hsimplex = PMF.pure candidate := by
    apply PMF.ext
    intro atom
    rw [ofVector_apply]
    subst oneHot
    by_cases hatom : atom = candidate
    · subst atom
      simp
    · simp [hatom]
  rw [finiteClockDecodeLaw, hvector, PMF.pure_map]

private theorem finiteClockDecodedLaws_substitutedWeight
    (level : ℕ)
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (hweight : ∀ player, weight player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (mover : Fin 4)
    (candidate : FiniteClockAtom (finFourSingleShellClock level)) :
    finiteClockDecodedLaws (finFourSingleShellClock level)
        (finFourSingleShellSubstitutedWeight level weight mover candidate)
        (finFourSingleShellSubstitutedWeight_mem_stdSimplex
          level weight hweight mover candidate) =
      quittingPureDeviationStoppingLaws
        (finiteClockDecodedLaws (finFourSingleShellClock level) weight hweight)
        mover (finiteClockAtomToStoppingTime
          (finFourSingleShellClock level) candidate) := by
  funext player
  by_cases hplayer : player = mover
  · subst player
    simp only [finiteClockDecodedLaws,
      quittingPureDeviationStoppingLaws, if_pos]
    apply finiteClockDecodeLaw_oneHot
    funext atom
    simp [finFourSingleShellSubstitutedWeight]
  · simp only [finiteClockDecodedLaws,
      quittingPureDeviationStoppingLaws, if_neg hplayer]
    congr 2
    funext atom
    simp [finFourSingleShellSubstitutedWeight, hplayer]

private theorem quittingStageCoalitionMass_finiteClockDecodedProfile_eq
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (level : ℕ)
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (hweight : ∀ player, weight player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (time : Fin (finFourSingleShellClock level + 1))
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (finiteClockDecodedProfile reward (finFourSingleShellClock level)
          weight hweight) time.1 terminal =
      finFourSingleShellCoalitionMass level weight time terminal := by
  rw [quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct]
  have hstop : ∀ player,
      (quittingBehaviorStoppingLaw reward
        (finiteClockDecodedProfile reward (finFourSingleShellClock level)
          weight hweight player) (some time.1)).toReal =
        weight player (some time) := by
    intro player
    rw [finiteClockDecodedProfile,
      quittingBehaviorStoppingLaw_stoppingLawProfile]
    exact finiteClockDecodeLaw_apply_toReal
      (finFourSingleShellClock level) (weight player) (hweight player)
      (some time)
  simp_rw [hstop]
  simp_rw [finiteClockDecoded_survival_eq_tailMass reward level weight hweight]
  unfold finFourSingleShellCoalitionMass
  rw [← Finset.prod_mul_prod_compl terminal.1 (fun player ↦
    if player ∈ terminal.1 then weight player (some time)
    else finFourSingleShellTailMass level weight player time)]
  congr 1
  · apply Finset.prod_congr rfl
    intro player hplayer
    simp [hplayer]
  · apply Finset.prod_congr rfl
    intro player hplayer
    have hnotMem : player ∉ terminal.1 := by
      simpa using hplayer
    simp [hnotMem]

private theorem quittingStageCoalitionMass_finiteClockDecodedProfile_eq_zero
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (level : ℕ)
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (hweight : ∀ player, weight player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (date : ℕ) (hdate : finFourSingleShellClock level < date)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (finiteClockDecodedProfile reward (finFourSingleShellClock level)
          weight hweight) date terminal = 0 := by
  rw [quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct]
  apply mul_eq_zero_of_left
  obtain ⟨player, hplayer⟩ := terminal.property
  apply Finset.prod_eq_zero hplayer
  rw [finiteClockDecodedProfile,
    quittingBehaviorStoppingLaw_stoppingLawProfile]
  change (finiteClockDecodeLaw (finFourSingleShellClock level)
    (weight player) (hweight player) (some date)).toReal = 0
  rw [finiteClockDecodeLaw_apply_eq_zero_of_clock_lt _ _ hdate
    (weight player) (hweight player)]
  rfl

private theorem quittingTerminalOutcomeMass_finiteClockDecodedProfile_eq_sum
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (level : ℕ)
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (hweight : ∀ player, weight player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) :
    quittingTerminalOutcomeMass reward
        (finiteClockDecodedProfile reward (finFourSingleShellClock level)
          weight hweight) (some terminal) =
      ∑ time : Fin (finFourSingleShellClock level + 1),
        finFourSingleShellCoalitionMass level weight time terminal := by
  rw [quittingTerminalOutcomeMass_eq_timeDisintegration]
  calc
    (∑' date : ℕ, quittingStageCoalitionMass reward
        (finiteClockDecodedProfile reward (finFourSingleShellClock level)
          weight hweight) date terminal) =
        ∑ date ∈ Finset.range (finFourSingleShellClock level + 1),
          quittingStageCoalitionMass reward
            (finiteClockDecodedProfile reward
              (finFourSingleShellClock level) weight hweight) date terminal := by
      apply tsum_eq_sum
      intro date hdate
      simp only [Finset.mem_range, not_lt] at hdate
      exact quittingStageCoalitionMass_finiteClockDecodedProfile_eq_zero
        reward level weight hweight date hdate terminal
    _ = ∑ time : Fin (finFourSingleShellClock level + 1),
        quittingStageCoalitionMass reward
          (finiteClockDecodedProfile reward (finFourSingleShellClock level)
            weight hweight) time.1 terminal := by
      symm
      rw [sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro date hdate
      simp [Finset.mem_range.mp hdate]
    _ = _ := by
      apply Fintype.sum_congr
      intro time
      exact quittingStageCoalitionMass_finiteClockDecodedProfile_eq
        reward level weight hweight time terminal

/-- The executable factored payoff is exactly the decoded finite-clock
terminal payoff. -/
theorem finFourSingleShellPayoff_eq_quittingTerminalPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (hweight : ∀ player, weight player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (observer : Fin 4) :
    finFourSingleShellPayoff reward level weight observer =
      quittingTerminalPayoff
        (fun terminal player ↦ (reward terminal player : ℝ))
        (finiteClockDecodedProfile
          (fun terminal player ↦ (reward terminal player : ℝ))
          (finFourSingleShellClock level) weight hweight) observer := by
  let realReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
    fun terminal player ↦ (reward terminal player : ℝ)
  let profile := finiteClockDecodedProfile realReward
    (finFourSingleShellClock level) weight hweight
  calc
    finFourSingleShellPayoff reward level weight observer =
        ∑ terminal : {S : Finset (Fin 4) // S.Nonempty},
          ∑ time : Fin (finFourSingleShellClock level + 1),
            (reward terminal observer : ℝ) *
              finFourSingleShellCoalitionMass level weight time terminal := by
      rw [finFourSingleShellPayoff, Finset.sum_comm]
      simpa [finFourSingleShellTerminalEquiv] using
        (finFourSingleShellTerminalEquiv.sum_comp
          (fun terminal ↦
            ∑ time : Fin (finFourSingleShellClock level + 1),
              (reward terminal observer : ℝ) *
                finFourSingleShellCoalitionMass level weight time terminal))
    _ = ∑ terminal : {S : Finset (Fin 4) // S.Nonempty},
        quittingTerminalOutcomeMass realReward profile (some terminal) *
          realReward terminal observer := by
      apply Fintype.sum_congr
      intro terminal
      rw [← Finset.mul_sum,
        ← quittingTerminalOutcomeMass_finiteClockDecodedProfile_eq_sum
          realReward level weight hweight terminal]
      ring
    _ = quittingTerminalPayoff realReward profile observer := by
      have hmoment := congrFun
        (quittingTerminalRewardMoment_outcomeMass realReward profile) observer
      simpa [quittingTerminalRewardMoment,
        quittingTerminalOutcomeReward] using hmoment

/-- Evaluation of the generated on-profile payoff row is the literal decoded
finite-clock terminal payoff. -/
theorem evalReal_finFourSingleShellOnProfilePayoffExpression
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (hweight : ∀ player, finFourSingleShellWeight level assign player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (observer : Fin 4) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellOnProfilePayoffExpression reward level observer) =
      quittingTerminalPayoff
        (fun terminal player ↦ (reward terminal player : ℝ))
        (finiteClockDecodedProfile
          (fun terminal player ↦ (reward terminal player : ℝ))
          (finFourSingleShellClock level)
          (finFourSingleShellWeight level assign) hweight) observer := by
  rw [finFourSingleShellOnProfilePayoffExpression,
    evalReal_finFourSingleShellPayoffExpression]
  change finFourSingleShellPayoff reward level
    (finFourSingleShellWeight level assign) observer = _
  exact finFourSingleShellPayoff_eq_quittingTerminalPayoff
    reward level (finFourSingleShellWeight level assign) hweight observer

/-- One-hot substitution in the factored formula is the literal pure-time
deviation payoff against the decoded base profile. -/
theorem finFourSingleShellPayoff_substitutedWeight_eq_update
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (hweight : ∀ player, weight player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (mover : Fin 4)
    (candidate : FiniteClockAtom (finFourSingleShellClock level)) :
    finFourSingleShellPayoff reward level
        (finFourSingleShellSubstitutedWeight level weight mover candidate)
        mover =
      quittingTerminalPayoff
        (fun terminal player ↦ (reward terminal player : ℝ))
        (Function.update
          (finiteClockDecodedProfile
            (fun terminal player ↦ (reward terminal player : ℝ))
            (finFourSingleShellClock level) weight hweight)
          mover
          (quittingPureTimeBehaviorStrategy
            (fun terminal player ↦ (reward terminal player : ℝ)) mover
            (finiteClockAtomToStoppingTime
              (finFourSingleShellClock level) candidate))) mover := by
  let realReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
    fun terminal player ↦ (reward terminal player : ℝ)
  let substituted := finFourSingleShellSubstitutedWeight
    level weight mover candidate
  let hsubstituted := finFourSingleShellSubstitutedWeight_mem_stdSimplex
    level weight hweight mover candidate
  calc
    finFourSingleShellPayoff reward level substituted mover =
        quittingTerminalPayoff realReward
          (finiteClockDecodedProfile realReward
            (finFourSingleShellClock level) substituted hsubstituted) mover :=
      finFourSingleShellPayoff_eq_quittingTerminalPayoff
        reward level substituted hsubstituted mover
    _ = quittingTerminalPayoff realReward
        (quittingStoppingLawProfile realReward
          (quittingPureDeviationStoppingLaws
            (finiteClockDecodedLaws (finFourSingleShellClock level)
              weight hweight) mover
            (finiteClockAtomToStoppingTime
              (finFourSingleShellClock level) candidate))) mover := by
      rw [finiteClockDecodedProfile,
        finiteClockDecodedLaws_substitutedWeight]
    _ = quittingTerminalPayoff realReward
        (Function.update
          (finiteClockDecodedProfile realReward
            (finFourSingleShellClock level) weight hweight)
          mover (quittingPureTimeBehaviorStrategy realReward mover
            (finiteClockAtomToStoppingTime
              (finFourSingleShellClock level) candidate))) mover := by
      rw [finiteClockDecodedProfile,
        quittingTerminalPayoff_stoppingLawProfile_eq_expect,
        ← quittingTerminalPayoff_update_stoppingLawProfile_pureTime_eq_expect]

/-- Every generated deviation row evaluates to the corresponding literal
pure-time deviation payoff. -/
theorem evalReal_finFourSingleShellDeviationPayoffExpression
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (hweight : ∀ player, finFourSingleShellWeight level assign player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (mover : Fin 4)
    (candidate : FiniteClockAtom (finFourSingleShellClock level)) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellDeviationPayoffExpression reward level mover
          candidate) =
      quittingTerminalPayoff
        (fun terminal player ↦ (reward terminal player : ℝ))
        (Function.update
          (finiteClockDecodedProfile
            (fun terminal player ↦ (reward terminal player : ℝ))
            (finFourSingleShellClock level)
            (finFourSingleShellWeight level assign) hweight)
          mover
          (quittingPureTimeBehaviorStrategy
            (fun terminal player ↦ (reward terminal player : ℝ)) mover
            (finiteClockAtomToStoppingTime
              (finFourSingleShellClock level) candidate))) mover := by
  rw [evalReal_finFourSingleShellDeviationPayoffExpression_eq_factored]
  exact finFourSingleShellPayoff_substitutedWeight_eq_update reward level
    (finFourSingleShellWeight level assign) hweight mover candidate

private theorem evalReal_finFourSingleShellSub
    (assign : Fin variableCount → ℝ)
    (first second : RationalMaxExpression variableCount) :
    RationalMaxExpression.evalReal assign (first - second) =
      RationalMaxExpression.evalReal assign first -
        RationalMaxExpression.evalReal assign second := by
  rfl

private theorem evalReal_finFourSingleShellSimplexExpression
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (player : Fin 4) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellSimplexExpression level player) =
      (∑ atom : FiniteClockAtom (finFourSingleShellClock level),
        finFourSingleShellWeight level assign player atom) - 1 := by
  unfold finFourSingleShellSimplexExpression finFourSingleShellAtomCount
  calc
    RationalMaxExpression.evalReal assign
        (finFourSingleShellSum (finFourSingleShellClock level + 2)
          (fun index ↦ finFourSingleShellMassExpression level player
            (finSuccEquiv (finFourSingleShellClock level + 1) index)) - 1) =
      RationalMaxExpression.evalReal assign
          (finFourSingleShellSum (finFourSingleShellClock level + 2)
            (fun index ↦ finFourSingleShellMassExpression level player
              (finSuccEquiv (finFourSingleShellClock level + 1) index))) - 1 := by
        rw [evalReal_finFourSingleShellSub]
        norm_num [RationalMaxExpression.evalReal]
    _ = (∑ index : Fin (finFourSingleShellClock level + 2),
        finFourSingleShellWeight level assign player
          (finSuccEquiv (finFourSingleShellClock level + 1) index)) - 1 := by
      rw [evalReal_finFourSingleShellSum]
      rfl
    _ = _ := by
      rw [Equiv.sum_comp (finSuccEquiv (finFourSingleShellClock level + 1))]

private theorem evalReal_finFourSingleShellMassExpression
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (player : Fin 4)
    (atom : FiniteClockAtom (finFourSingleShellClock level)) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellMassExpression level player atom) =
      finFourSingleShellWeight level assign player atom := rfl

private theorem evalReal_finFourSingleShellAuxiliaryExpression
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (player : Fin 4) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellAuxiliaryExpression level player) =
      finFourSingleShellWeight level assign player
        (finiteClockAuxAtom (finFourSingleShellClock level)) := rfl

private theorem evalReal_finFourSingleShellPayoffConsistencyExpression
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (hweight : ∀ player, finFourSingleShellWeight level assign player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (player : Fin 4) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellPayoffConsistencyExpression reward level player) =
      assign (finFourSingleShellCenterPayoffIndex level player) -
        quittingTerminalPayoff
          (fun terminal who ↦ (reward terminal who : ℝ))
          (finiteClockDecodedProfile
            (fun terminal who ↦ (reward terminal who : ℝ))
            (finFourSingleShellClock level)
            (finFourSingleShellWeight level assign) hweight) player := by
  change assign (finFourSingleShellCenterPayoffIndex level player) -
    RationalMaxExpression.evalReal assign
      (finFourSingleShellOnProfilePayoffExpression reward level player) = _
  rw [evalReal_finFourSingleShellOnProfilePayoffExpression
    reward level assign hweight player]

/-- Flat feasibility supplies the four literal marginal simplexes. -/
theorem finFourSingleShellWeight_mem_stdSimplex_of_feasible
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (hfeasible : (finFourRationalSingleShellLowerProblem reward level).Feasible
      assign) (player : Fin 4) :
    finFourSingleShellWeight level assign player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)) := by
  constructor
  · intro atom
    have hrow := hfeasible.2.2
      (finFourSingleShellMassNonnegativeIndex level player atom)
    change 0 ≤ RationalMaxExpression.evalReal assign
      (finFourSingleShellNonnegativeExpression reward level
        (finFourSingleShellMassNonnegativeIndex level player atom)) at hrow
    rw [finFourSingleShellNonnegativeExpression_massIndex,
      evalReal_finFourSingleShellMassExpression] at hrow
    exact hrow
  · have hrow := hfeasible.2.1
      (finFourSingleShellEqualityIndex 0 player)
    have hrow' : RationalMaxExpression.evalReal assign
        (finFourSingleShellSimplexExpression level player) = 0 := by
      simpa [finFourRationalSingleShellLowerProblem,
        finFourSingleShellEqualityExpression_index] using hrow
    rw [evalReal_finFourSingleShellSimplexExpression] at hrow'
    linarith

/-- Flat feasibility forces the auxiliary center coordinate to zero. -/
theorem finFourSingleShellWeight_aux_eq_zero_of_feasible
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (hfeasible : (finFourRationalSingleShellLowerProblem reward level).Feasible
      assign) (player : Fin 4) :
    finFourSingleShellWeight level assign player
      (finiteClockAuxAtom (finFourSingleShellClock level)) = 0 := by
  have hrow := hfeasible.2.1
    (finFourSingleShellEqualityIndex 1 player)
  have hrow' : RationalMaxExpression.evalReal assign
      (finFourSingleShellAuxiliaryExpression level player) = 0 := by
    simpa [finFourRationalSingleShellLowerProblem,
      finFourSingleShellEqualityExpression_index] using hrow
  rw [evalReal_finFourSingleShellAuxiliaryExpression] at hrow'
  exact hrow'

/-- The generated cap upper-bound and tight-product rows identify the center
cap coordinate with the unrestricted behavioral continuation value. -/
theorem finFourSingleShellCenterCap_eq_continuationBestResponseValue
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (hweight : ∀ player, finFourSingleShellWeight level assign player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (haux : ∀ player, finFourSingleShellWeight level assign player
      (finiteClockAuxAtom (finFourSingleShellClock level)) = 0)
    (player : Fin 4)
    (hupper : ∀ candidate,
      0 ≤ RationalMaxExpression.evalReal assign
        (finFourSingleShellCapUpperExpression reward level player candidate))
    (htight : RationalMaxExpression.evalReal assign
      (finFourSingleShellCapTightExpression reward level player) = 0) :
    assign (finFourSingleShellCenterCapIndex level player) =
      quittingContinuationBestResponseValue
        (fun terminal who ↦ (reward terminal who : ℝ))
        (finiteClockDecodedProfile
          (fun terminal who ↦ (reward terminal who : ℝ))
          (finFourSingleShellClock level)
          (finFourSingleShellWeight level assign) hweight) player := by
  let realReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
    fun terminal who ↦ (reward terminal who : ℝ)
  let profile := finiteClockDecodedProfile realReward
    (finFourSingleShellClock level)
    (finFourSingleShellWeight level assign) hweight
  have hupperSemantic : ∀ candidate,
      quittingTerminalPayoff realReward
        (Function.update profile player
          (quittingPureTimeBehaviorStrategy realReward player
            (finiteClockAtomToStoppingTime
              (finFourSingleShellClock level) candidate))) player ≤
        assign (finFourSingleShellCenterCapIndex level player) := by
    intro candidate
    have hrow := hupper candidate
    change 0 ≤ assign (finFourSingleShellCenterCapIndex level player) -
      RationalMaxExpression.evalReal assign
        (finFourSingleShellDeviationPayoffExpression reward level player
          candidate) at hrow
    rw [evalReal_finFourSingleShellDeviationPayoffExpression
      reward level assign hweight player candidate] at hrow
    exact sub_nonneg.mp hrow
  have htightSemantic : ∃ candidate,
      quittingTerminalPayoff realReward
        (Function.update profile player
          (quittingPureTimeBehaviorStrategy realReward player
            (finiteClockAtomToStoppingTime
              (finFourSingleShellClock level) candidate))) player =
        assign (finFourSingleShellCenterCapIndex level player) := by
    rw [finFourSingleShellCapTightExpression,
      evalReal_finFourSingleShellProduct] at htight
    change (∏ index : Fin (finFourSingleShellClock level + 2),
      RationalMaxExpression.evalReal assign
        (finFourSingleShellCapUpperExpression reward level player
          (finSuccEquiv (finFourSingleShellClock level + 1) index))) = 0
      at htight
    obtain ⟨index, hzero⟩ :
        ∃ index : Fin (finFourSingleShellClock level + 2),
        RationalMaxExpression.evalReal assign
          (finFourSingleShellCapUpperExpression reward level player
            (finSuccEquiv (finFourSingleShellClock level + 1) index)) = 0 := by
      simpa only [Finset.mem_univ, true_and] using
        (Finset.prod_eq_zero_iff.mp htight)
    refine ⟨finSuccEquiv (finFourSingleShellClock level + 1) index, ?_⟩
    change assign (finFourSingleShellCenterCapIndex level player) -
      RationalMaxExpression.evalReal assign
        (finFourSingleShellDeviationPayoffExpression reward level player
          (finSuccEquiv (finFourSingleShellClock level + 1) index)) = 0
      at hzero
    rw [evalReal_finFourSingleShellDeviationPayoffExpression
      reward level assign hweight player
        (finSuccEquiv (finFourSingleShellClock level + 1) index)] at hzero
    exact (sub_eq_zero.mp hzero).symm
  symm
  exact quittingContinuationBestResponseValue_finiteClockDecodedProfile_eq_of_maxGraph
    realReward (finFourSingleShellClock level)
    (finFourSingleShellWeight level assign) hweight haux player
    (assign (finFourSingleShellCenterCapIndex level player))
    hupperSemantic htightSemantic

/-- A feasible flat center is exactly the literal semantic pair of its
decoded finite-clock profile. -/
theorem finFourSingleShellCenterPair_eq_terminalSemanticPair_of_feasible
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (hfeasible : (finFourRationalSingleShellLowerProblem reward level).Feasible
      assign) :
    finFourSingleShellCenterPair level assign =
      quittingTerminalSemanticPair
        (fun terminal who ↦ (reward terminal who : ℝ))
        (finiteClockDecodedProfile
          (fun terminal who ↦ (reward terminal who : ℝ))
          (finFourSingleShellClock level)
          (finFourSingleShellWeight level assign)
          (finFourSingleShellWeight_mem_stdSimplex_of_feasible
            reward level assign hfeasible)) := by
  apply Prod.ext
  · funext player
    have hrow := hfeasible.2.1
      (finFourSingleShellEqualityIndex 2 player)
    have hrow' : RationalMaxExpression.evalReal assign
        (finFourSingleShellPayoffConsistencyExpression reward level player) = 0 := by
      simpa [finFourRationalSingleShellLowerProblem,
        finFourSingleShellEqualityExpression_index] using hrow
    rw [
      evalReal_finFourSingleShellPayoffConsistencyExpression reward level
        assign (finFourSingleShellWeight_mem_stdSimplex_of_feasible
          reward level assign hfeasible)] at hrow'
    exact sub_eq_zero.mp hrow'
  · funext player
    apply finFourSingleShellCenterCap_eq_continuationBestResponseValue
      reward level assign
      (finFourSingleShellWeight_mem_stdSimplex_of_feasible
        reward level assign hfeasible)
      (finFourSingleShellWeight_aux_eq_zero_of_feasible
        reward level assign hfeasible) player
    · intro candidate
      have hrow := hfeasible.2.2
        (finFourSingleShellCapNonnegativeIndex level player candidate)
      change 0 ≤ RationalMaxExpression.evalReal assign
        (finFourSingleShellNonnegativeExpression reward level
          (finFourSingleShellCapNonnegativeIndex level player candidate)) at hrow
      rwa [finFourSingleShellNonnegativeExpression_capIndex] at hrow
    · have hrow := hfeasible.2.1
        (finFourSingleShellEqualityIndex 3 player)
      simpa [finFourRationalSingleShellLowerProblem,
        finFourSingleShellEqualityExpression_index] using hrow

private theorem evalReal_finFourSingleShellNeighborhoodExpression
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (player : Fin 4) (capCoordinate reverse : Bool) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellNeighborhoodExpression level player
          capCoordinate reverse) =
      (finFourSingleShellRadiusRat level : ℝ) +
        if reverse then
          if capCoordinate then
            assign (finFourSingleShellPointCapIndex level player) -
              assign (finFourSingleShellCenterCapIndex level player)
          else
            assign (finFourSingleShellPointPayoffIndex level player) -
              assign (finFourSingleShellCenterPayoffIndex level player)
        else
          -(if capCoordinate then
            assign (finFourSingleShellPointCapIndex level player) -
              assign (finFourSingleShellCenterCapIndex level player)
          else
            assign (finFourSingleShellPointPayoffIndex level player) -
              assign (finFourSingleShellCenterPayoffIndex level player)) := by
  cases capCoordinate <;> cases reverse <;>
    simp [finFourSingleShellNeighborhoodExpression,
      finFourSingleShellPointPayoffExpression,
      finFourSingleShellPointCapExpression,
      finFourSingleShellCenterPayoffExpression,
      finFourSingleShellCenterCapExpression,
      finFourSingleShellVariable,
      evalReal_finFourSingleShellSub,
      RationalMaxExpression.evalReal]

/-- The sixteen signed neighborhood rows are exactly the coordinatewise
single-shell distance bound between the common point and its decoded center. -/
theorem finFourSingleShellPointPair_within_centerPair_of_feasible
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (hfeasible : (finFourRationalSingleShellLowerProblem reward level).Feasible
      assign) :
    semanticPairWithin (finFourSingleShellRadiusRat level : ℝ)
      (finFourSingleShellPointPair level assign)
      (finFourSingleShellCenterPair level assign) := by
  constructor <;> intro player <;> rw [abs_le] <;> constructor
  · have hrow := hfeasible.2.2
      (finFourSingleShellNeighborhoodNonnegativeIndex level player false true)
    change 0 ≤ RationalMaxExpression.evalReal assign
      (finFourSingleShellNonnegativeExpression reward level
        (finFourSingleShellNeighborhoodNonnegativeIndex level player
          false true)) at hrow
    rw [finFourSingleShellNonnegativeExpression_neighborhoodIndex,
      evalReal_finFourSingleShellNeighborhoodExpression] at hrow
    simp only [Bool.false_eq_true, ↓reduceIte] at hrow
    simp only [finFourSingleShellPointPair, finFourSingleShellCenterPair]
    linarith
  · have hrow := hfeasible.2.2
      (finFourSingleShellNeighborhoodNonnegativeIndex level player false false)
    change 0 ≤ RationalMaxExpression.evalReal assign
      (finFourSingleShellNonnegativeExpression reward level
        (finFourSingleShellNeighborhoodNonnegativeIndex level player
          false false)) at hrow
    rw [finFourSingleShellNonnegativeExpression_neighborhoodIndex,
      evalReal_finFourSingleShellNeighborhoodExpression] at hrow
    simp only [Bool.false_eq_true, ↓reduceIte] at hrow
    simp only [finFourSingleShellPointPair, finFourSingleShellCenterPair]
    linarith
  · have hrow := hfeasible.2.2
      (finFourSingleShellNeighborhoodNonnegativeIndex level player true true)
    change 0 ≤ RationalMaxExpression.evalReal assign
      (finFourSingleShellNonnegativeExpression reward level
        (finFourSingleShellNeighborhoodNonnegativeIndex level player
          true true)) at hrow
    rw [finFourSingleShellNonnegativeExpression_neighborhoodIndex,
      evalReal_finFourSingleShellNeighborhoodExpression] at hrow
    simp only [↓reduceIte] at hrow
    simp only [finFourSingleShellPointPair, finFourSingleShellCenterPair]
    linarith
  · have hrow := hfeasible.2.2
      (finFourSingleShellNeighborhoodNonnegativeIndex level player true false)
    change 0 ≤ RationalMaxExpression.evalReal assign
      (finFourSingleShellNonnegativeExpression reward level
        (finFourSingleShellNeighborhoodNonnegativeIndex level player
          true false)) at hrow
    rw [finFourSingleShellNonnegativeExpression_neighborhoodIndex,
      evalReal_finFourSingleShellNeighborhoodExpression] at hrow
    simp only [Bool.false_eq_true, ↓reduceIte] at hrow
    simp only [finFourSingleShellPointPair, finFourSingleShellCenterPair]
    linarith

private theorem finFourSingleShellRadiusRat_cast (level : ℕ) :
    (finFourSingleShellRadiusRat level : ℝ) =
      quantileClockRadius (Fin 4) level := by
  rw [quantileClockRadius_fin4]
  norm_num [finFourSingleShellRadiusRat]

/-- The decoded center of every feasible assignment is a literal member of
the finite-clock semantic center at the generated clock. -/
theorem finFourSingleShellCenterPair_mem_semanticCenter_of_feasible
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (hfeasible : (finFourRationalSingleShellLowerProblem reward level).Feasible
      assign) :
    finFourSingleShellCenterPair level assign ∈
      quittingFiniteClockSemanticCenter
        (fun terminal who ↦ (reward terminal who : ℝ))
        (finFourSingleShellClock level) := by
  rw [finFourSingleShellCenterPair_eq_terminalSemanticPair_of_feasible
    reward level assign hfeasible]
  let weight := finFourSingleShellWeight level assign
  let hweight := finFourSingleShellWeight_mem_stdSimplex_of_feasible
    reward level assign hfeasible
  let laws := finiteClockDecodedLaws (finFourSingleShellClock level)
    weight hweight
  refine ⟨laws, ?_, rfl⟩
  intro player choice hchoice
  exact finiteClockDecodeLaw_support (finFourSingleShellClock level)
    (weight player) (hweight player)
    (finFourSingleShellWeight_aux_eq_zero_of_feasible
      reward level assign hfeasible player) choice hchoice

/-- Every feasible reflected assignment maps to the analytic one-shell outer
neighborhood, with the same common semantic point. -/
theorem finFourSingleShellPointPair_mem_outerNeighborhood_of_feasible
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (hfeasible : (finFourRationalSingleShellLowerProblem reward level).Feasible
      assign) :
    finFourSingleShellPointPair level assign ∈
      (escapeAwareQuantileClockSystem
        (fun terminal who ↦ (reward terminal who : ℝ))
        (hasEscapeAwareQuantileClockCompression_of_normalized
          (fun terminal who ↦ (reward terminal who : ℝ)) hreward)).outerNeighborhood
        level := by
  let realReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
    fun terminal who ↦ (reward terminal who : ℝ)
  have hcenter : finFourSingleShellCenterPair level assign ∈
      quittingFiniteClockSemanticCenter realReward
        (quantileClockSupport (Fin 4) level) := by
    exact finFourSingleShellCenterPair_mem_semanticCenter_of_feasible
      reward level assign hfeasible
  have hwithin : semanticPairWithin (quantileClockRadius (Fin 4) level)
      (finFourSingleShellPointPair level assign)
      (finFourSingleShellCenterPair level assign) := by
    rw [← finFourSingleShellRadiusRat_cast]
    exact finFourSingleShellPointPair_within_centerPair_of_feasible
      reward level assign hfeasible
  change Metric.infDist (finFourSingleShellPointPair level assign)
      (quittingFiniteClockSemanticCenter realReward
        (quantileClockSupport (Fin 4) level)) ≤
      quantileClockRadius (Fin 4) level
  exact (Metric.infDist_le_dist_of_mem hcenter).trans
    (dist_le_of_semanticPairWithin
      (quantileClockRadius_nonneg (Fin 4) level) hwithin)

private theorem finFourSingleShellEqualityIndex_surjective
    (index : Fin finFourSingleShellEqualityCount) :
    ∃ kind player : Fin 4,
      index = finFourSingleShellEqualityIndex kind player := by
  let raw : Fin (4 * 4) :=
    Fin.cast (by norm_num [finFourSingleShellEqualityCount]) index
  let row : Fin 4 × Fin 4 := finProdFinEquiv.symm raw
  refine ⟨row.1, row.2, ?_⟩
  apply Fin.ext
  have hraw : finProdFinEquiv row = raw := by
    exact Equiv.apply_symm_apply finProdFinEquiv raw
  change raw.1 = (finProdFinEquiv row).1
  exact congrArg Fin.val hraw.symm

/-- Equality-row reconstruction for a semantic point, an actual decoded
center, and finite-clock marginal data. -/
theorem finFourSingleShellAssignmentOfData_equalityRows
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (point center : QuittingTerminalSemanticPair (Fin 4))
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (hweight : ∀ player, weight player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (haux : ∀ player, weight player
      (finiteClockAuxAtom (finFourSingleShellClock level)) = 0)
    (hcenter : center = quittingTerminalSemanticPair
      (fun terminal who ↦ (reward terminal who : ℝ))
      (finiteClockDecodedProfile
        (fun terminal who ↦ (reward terminal who : ℝ))
        (finFourSingleShellClock level) weight hweight)) :
    ∀ index, RationalMaxExpression.evalReal
      (finFourSingleShellAssignmentOfData level point center weight)
      (finFourSingleShellEqualityExpression reward level index) = 0 := by
  intro index
  obtain ⟨kind, player, rfl⟩ :=
    finFourSingleShellEqualityIndex_surjective index
  rw [finFourSingleShellEqualityExpression_index]
  have hflatWeight : ∀ player,
      finFourSingleShellWeight level
          (finFourSingleShellAssignmentOfData level point center weight) player ∈
        stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)) := by
    simpa only [finFourSingleShellWeight_assignmentOfData] using hweight
  fin_cases kind
  · change RationalMaxExpression.evalReal _
        (finFourSingleShellSimplexExpression level player) = 0
    rw [evalReal_finFourSingleShellSimplexExpression]
    simp only [finFourSingleShellWeight,
      finFourSingleShellAssignmentOfData_mass]
    linarith [hweight player |>.2]
  · change RationalMaxExpression.evalReal _
        (finFourSingleShellAuxiliaryExpression level player) = 0
    rw [evalReal_finFourSingleShellAuxiliaryExpression]
    simpa only [finFourSingleShellWeight,
      finFourSingleShellAssignmentOfData_mass] using haux player
  · change RationalMaxExpression.evalReal _
        (finFourSingleShellPayoffConsistencyExpression reward level player) = 0
    rw [finFourSingleShellPayoffConsistencyExpression,
      evalReal_finFourSingleShellSub]
    simp only [finFourSingleShellCenterPayoffExpression,
      finFourSingleShellVariable, RationalMaxExpression.evalReal,
      finFourSingleShellAssignmentOfData_centerPayoff]
    rw [finFourSingleShellOnProfilePayoffExpression,
      evalReal_finFourSingleShellPayoffExpression]
    simp only [finFourSingleShellMassExpression,
      finFourSingleShellVariable, RationalMaxExpression.evalReal,
      finFourSingleShellAssignmentOfData_mass]
    rw [finFourSingleShellPayoff_eq_quittingTerminalPayoff
      reward level weight hweight player]
    have hcenterPayoff := congrFun (congrArg Prod.fst hcenter) player
    rw [hcenterPayoff]
    simp only [quittingTerminalSemanticPair, sub_self]
  · change RationalMaxExpression.evalReal _
        (finFourSingleShellCapTightExpression reward level player) = 0
    rw [finFourSingleShellCapTightExpression,
      evalReal_finFourSingleShellProduct]
    obtain ⟨candidate, hcandidate⟩ :=
      exists_finiteClockCandidate_payoff_eq_continuationBestResponseValue
        (fun terminal who ↦ (reward terminal who : ℝ))
        (finFourSingleShellClock level) weight hweight haux player
    apply Finset.prod_eq_zero_iff.mpr
    let index : Fin (finFourSingleShellAtomCount level) :=
      Fin.cast (by simp [finFourSingleShellAtomCount])
        ((finSuccEquiv
          (finFourSingleShellClock level + 1)).symm candidate)
    have hdecode :
        finSuccEquiv (finFourSingleShellClock level + 1) index = candidate := by
      have hcast : index =
          (finSuccEquiv
            (finFourSingleShellClock level + 1)).symm candidate := by
        apply Fin.ext
        rfl
      rw [hcast, Equiv.apply_symm_apply]
    refine ⟨index, Finset.mem_univ index, ?_⟩
    rw [hdecode]
    rw [finFourSingleShellCapUpperExpression,
      evalReal_finFourSingleShellSub]
    simp only [finFourSingleShellCenterCapExpression,
      finFourSingleShellVariable, RationalMaxExpression.evalReal,
      finFourSingleShellAssignmentOfData_centerCap]
    have heval := evalReal_finFourSingleShellDeviationPayoffExpression_eq_factored
      reward level
      (finFourSingleShellAssignmentOfData level point center weight)
      player candidate
    simp only [finFourSingleShellWeight_assignmentOfData] at heval
    rw [finFourSingleShellPayoff_substitutedWeight_eq_update
      reward level weight hweight player candidate] at heval
    rw [heval]
    have hcenterCap := congrFun (congrArg Prod.snd hcenter) player
    rw [hcenterCap]
    exact sub_eq_zero.mpr hcandidate.symm

/-- Nonnegative-row reconstruction for a common point within the generated
radius of an actual decoded center. -/
theorem finFourSingleShellAssignmentOfData_nonnegativeRows
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ)
    (point center : QuittingTerminalSemanticPair (Fin 4))
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (hweight : ∀ player, weight player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (hcenter : center = quittingTerminalSemanticPair
      (fun terminal who ↦ (reward terminal who : ℝ))
      (finiteClockDecodedProfile
        (fun terminal who ↦ (reward terminal who : ℝ))
        (finFourSingleShellClock level) weight hweight))
    (hwithin : semanticPairWithin (finFourSingleShellRadiusRat level : ℝ)
      point center) :
    ∀ index, 0 ≤ RationalMaxExpression.evalReal
      (finFourSingleShellAssignmentOfData level point center weight)
      (finFourSingleShellNonnegativeExpression reward level index) := by
  intro index
  unfold finFourSingleShellNonnegativeExpression
  generalize hsplit : finSumFinEquiv.symm index = split
  cases split with
  | inl centerIndex =>
      dsimp only
      generalize hrow : finProdFinEquiv.symm centerIndex = row
      rcases row with ⟨kind, massIndex⟩
      fin_cases kind
      · change 0 ≤ RationalMaxExpression.evalReal _
          (finFourSingleShellMassExpression level
            (finFourSingleShellMassCoordinate level massIndex).1
            (finFourSingleShellMassCoordinate level massIndex).2)
        let coordinate := finFourSingleShellMassCoordinate level massIndex
        rw [evalReal_finFourSingleShellMassExpression]
        simp only [finFourSingleShellWeight,
          finFourSingleShellAssignmentOfData_mass]
        exact (hweight coordinate.1).1 coordinate.2
      · change 0 ≤ RationalMaxExpression.evalReal _
          (finFourSingleShellCapUpperExpression reward level
            (finFourSingleShellMassCoordinate level massIndex).1
            (finFourSingleShellMassCoordinate level massIndex).2)
        let coordinate := finFourSingleShellMassCoordinate level massIndex
        rw [finFourSingleShellCapUpperExpression,
          evalReal_finFourSingleShellSub]
        simp only [finFourSingleShellCenterCapExpression,
          finFourSingleShellVariable, RationalMaxExpression.evalReal,
          finFourSingleShellAssignmentOfData_centerCap]
        have heval := evalReal_finFourSingleShellDeviationPayoffExpression_eq_factored
          reward level
          (finFourSingleShellAssignmentOfData level point center weight)
          coordinate.1 coordinate.2
        simp only [finFourSingleShellWeight_assignmentOfData] at heval
        rw [finFourSingleShellPayoff_substitutedWeight_eq_update
          reward level weight hweight coordinate.1 coordinate.2] at heval
        rw [heval]
        have hcenterCap := congrFun (congrArg Prod.snd hcenter) coordinate.1
        rw [hcenterCap]
        exact sub_nonneg.mpr
          (quittingTerminalPayoff_update_pureTime_le_continuationBestResponseValue
            (fun terminal who ↦ (reward terminal who : ℝ))
            (finiteClockDecodedProfile
              (fun terminal who ↦ (reward terminal who : ℝ))
              (finFourSingleShellClock level) weight hweight)
            coordinate.1
            (finiteClockAtomToStoppingTime
              (finFourSingleShellClock level) coordinate.2))
  | inr neighborhoodIndex =>
      dsimp only
      let raw : Fin (4 * 4) := Fin.cast (by norm_num) neighborhoodIndex
      let row : Fin 4 × Fin 4 := finProdFinEquiv.symm raw
      have hrowEq : finProdFinEquiv row = raw :=
        Equiv.apply_symm_apply finProdFinEquiv raw
      rcases row with ⟨kind, player⟩
      have hrow : finProdFinEquiv.symm
          (Fin.cast (by norm_num) neighborhoodIndex) = (kind, player) := by
        change finProdFinEquiv.symm raw = (kind, player)
        rw [← hrowEq, Equiv.symm_apply_apply]
      rw [hrow]
      fin_cases kind
      · norm_num
        rw [evalReal_finFourSingleShellNeighborhoodExpression]
        simp only [Bool.false_eq_true, ↓reduceIte,
          finFourSingleShellAssignmentOfData_pointPayoff,
          finFourSingleShellAssignmentOfData_centerPayoff]
        obtain ⟨hlower, hupper⟩ := (abs_le.mp (hwithin.1 player))
        linarith
      · norm_num
        rw [evalReal_finFourSingleShellNeighborhoodExpression]
        simp only [Bool.false_eq_true, ↓reduceIte,
          finFourSingleShellAssignmentOfData_pointPayoff,
          finFourSingleShellAssignmentOfData_centerPayoff]
        obtain ⟨hlower, hupper⟩ := (abs_le.mp (hwithin.1 player))
        linarith
      · norm_num
        rw [evalReal_finFourSingleShellNeighborhoodExpression]
        simp only [Bool.false_eq_true, ↓reduceIte,
          finFourSingleShellAssignmentOfData_pointCap,
          finFourSingleShellAssignmentOfData_centerCap]
        obtain ⟨hlower, hupper⟩ := (abs_le.mp (hwithin.2 player))
        linarith
      · norm_num
        rw [evalReal_finFourSingleShellNeighborhoodExpression]
        simp only [↓reduceIte,
          finFourSingleShellAssignmentOfData_pointCap,
          finFourSingleShellAssignmentOfData_centerCap]
        obtain ⟨hlower, hupper⟩ := (abs_le.mp (hwithin.2 player))
        linarith

/-- Root-box reconstruction for normalized semantic data and simplex
marginals. -/
theorem finFourSingleShellRootBox_contains_assignmentOfData
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    (level : ℕ)
    (point center : QuittingTerminalSemanticPair (Fin 4))
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (hweight : ∀ player, weight player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (hcenter : center = quittingTerminalSemanticPair
      (fun terminal who ↦ (reward terminal who : ℝ))
      (finiteClockDecodedProfile
        (fun terminal who ↦ (reward terminal who : ℝ))
        (finFourSingleShellClock level) weight hweight))
    (hwithin : semanticPairWithin (finFourSingleShellRadiusRat level : ℝ)
      point center) :
    (finFourSingleShellRootBox level).Contains
      (finFourSingleShellAssignmentOfData level point center weight) := by
  let profile := finiteClockDecodedProfile
    (fun terminal who ↦ (reward terminal who : ℝ))
    (finFourSingleShellClock level) weight hweight
  have hcenterPayoffAbs (player : Fin 4) : |center.1 player| ≤ 1 := by
    rw [hcenter]
    exact abs_quittingTerminalPayoff_le
      (fun terminal who ↦ (reward terminal who : ℝ)) profile player hreward
  have hcenterCapAbs (player : Fin 4) : |center.2 player| ≤ 1 := by
    rw [hcenter]
    exact abs_quittingContinuationBestResponseValue_le
      (fun terminal who ↦ (reward terminal who : ℝ)) profile player hreward
  have hpointPayoffAbs (player : Fin 4) :
      |point.1 player| ≤ 1 + (finFourSingleShellRadiusRat level : ℝ) := by
    calc
      |point.1 player| =
          |(point.1 player - center.1 player) + center.1 player| := by ring_nf
      _ ≤ |point.1 player - center.1 player| + |center.1 player| :=
        abs_add_le _ _
      _ ≤ (finFourSingleShellRadiusRat level : ℝ) + 1 :=
        add_le_add (hwithin.1 player) (hcenterPayoffAbs player)
      _ = _ := by ring
  have hpointCapAbs (player : Fin 4) :
      |point.2 player| ≤ 1 + (finFourSingleShellRadiusRat level : ℝ) := by
    calc
      |point.2 player| =
          |(point.2 player - center.2 player) + center.2 player| := by ring_nf
      _ ≤ |point.2 player - center.2 player| + |center.2 player| :=
        abs_add_le _ _
      _ ≤ (finFourSingleShellRadiusRat level : ℝ) + 1 :=
        add_le_add (hwithin.2 player) (hcenterCapAbs player)
      _ = _ := by ring
  intro index
  by_cases h4 : index.1 < 4
  · have h8 : index.1 < 8 := by omega
    have hbounds := abs_le.mp (hpointPayoffAbs ⟨index.1, h4⟩)
    have hvalue : finFourSingleShellAssignmentOfData level point center weight
        index = point.1 ⟨index.1, h4⟩ := by
      simp [finFourSingleShellAssignmentOfData, h4]
    rw [hvalue]
    simp only [finFourSingleShellRootBox, h8, ↓reduceIte,
      RationalInterval.Contains, Rat.cast_sub, Rat.cast_neg, Rat.cast_one,
      Rat.cast_add]
    constructor <;> linarith
  · by_cases h8 : index.1 < 8
    · have hbounds := abs_le.mp (hpointCapAbs ⟨index.1 - 4, by omega⟩)
      have hvalue : finFourSingleShellAssignmentOfData level point center weight
          index = point.2 ⟨index.1 - 4, by omega⟩ := by
        simp [finFourSingleShellAssignmentOfData, h4, h8]
      rw [hvalue]
      simp only [finFourSingleShellRootBox, h8, ↓reduceIte,
        RationalInterval.Contains, Rat.cast_sub, Rat.cast_neg, Rat.cast_one,
        Rat.cast_add]
      constructor <;> linarith
    · by_cases h12 : index.1 < 12
      · have h16 : index.1 < 16 := by omega
        have hbounds := abs_le.mp
          (hcenterPayoffAbs ⟨index.1 - 8, by omega⟩)
        simp only [finFourSingleShellRootBox, h8, h16, ↓reduceIte,
          finFourSingleShellAssignmentOfData, h4, h12,
          RationalInterval.Contains, Rat.cast_neg, Rat.cast_one]
        exact hbounds
      · by_cases h16 : index.1 < 16
        · have hbounds := abs_le.mp
            (hcenterCapAbs ⟨index.1 - 12, by omega⟩)
          simp only [finFourSingleShellRootBox, h8, h16, ↓reduceIte,
            finFourSingleShellAssignmentOfData, h4, h12,
            RationalInterval.Contains, Rat.cast_neg, Rat.cast_one]
          exact hbounds
        · let massIndex : Fin
              (4 * (finFourSingleShellClock level + 1 + 1)) :=
            ⟨index.1 - 16, by
              have hbound := index.2
              simp only [finFourSingleShellVariableCount,
                finFourSingleShellMassCount,
                finFourSingleShellAtomCount] at hbound
              omega⟩
          let coordinate := finProdFinEquiv.symm massIndex
          let atom := finSuccEquiv
            (finFourSingleShellClock level + 1) coordinate.2
          have hnonneg := (hweight coordinate.1).1 atom
          have hsum := (hweight coordinate.1).2
          have hle : weight coordinate.1 atom ≤ 1 := by
            rw [← hsum]
            exact Finset.single_le_sum
              (fun other _ ↦ (hweight coordinate.1).1 other)
              (Finset.mem_univ atom)
          simp only [finFourSingleShellRootBox, h8, h16, ↓reduceIte,
            finFourSingleShellAssignmentOfData, h4, h12,
            RationalInterval.Contains, Rat.cast_zero, Rat.cast_one]
          exact ⟨hnonneg, hle⟩

/-- The semantic data reconstructed from one finite-clock polynomial center
give a feasible point of the executable lower problem. -/
theorem finFourSingleShellAssignmentOfData_feasible
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    (level : ℕ)
    (point center : QuittingTerminalSemanticPair (Fin 4))
    (weight : Fin 4 → FiniteClockAtom (finFourSingleShellClock level) → ℝ)
    (hweight : ∀ player, weight player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)))
    (haux : ∀ player, weight player
      (finiteClockAuxAtom (finFourSingleShellClock level)) = 0)
    (hcenter : center = quittingTerminalSemanticPair
      (fun terminal who ↦ (reward terminal who : ℝ))
      (finiteClockDecodedProfile
        (fun terminal who ↦ (reward terminal who : ℝ))
        (finFourSingleShellClock level) weight hweight))
    (hwithin : semanticPairWithin (finFourSingleShellRadiusRat level : ℝ)
      point center) :
    (finFourRationalSingleShellLowerProblem reward level).Feasible
      (finFourSingleShellAssignmentOfData level point center weight) := by
  refine ⟨finFourSingleShellRootBox_contains_assignmentOfData
      reward hreward level point center weight hweight hcenter hwithin,
    finFourSingleShellAssignmentOfData_equalityRows
      reward level point center weight hweight haux hcenter, ?_⟩
  exact finFourSingleShellAssignmentOfData_nonnegativeRows
    reward level point center weight hweight hcenter hwithin

/-- The reflected objective evaluates to the literal maximum positive debt of
the represented common semantic pair. -/
theorem evalReal_finFourSingleShellObjectiveExpression
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ) :
    RationalMaxExpression.evalReal assign
        (finFourSingleShellObjectiveExpression level) =
      quittingTerminalSemanticExploitability
        (finFourSingleShellPointPair level assign) := by
  simp only [finFourSingleShellObjectiveExpression,
    sub_eq_add_neg, RationalMaxExpression.evalReal,
    finFourSingleShellPointCapExpression,
    finFourSingleShellPointPayoffExpression,
    finFourSingleShellVariable,
    finFourSingleShellPointPair,
    quittingTerminalSemanticExploitability,
    quittingTerminalSemanticDebt, Rat.cast_zero]
  let debt : Fin 4 → ℝ := fun who ↦
    assign (finFourSingleShellPointCapIndex level who) -
      assign (finFourSingleShellPointPayoffIndex level who)
  let positive : Fin 4 → ℝ := fun who ↦ max 0 (debt who)
  change max 0 (max (debt 0) (max (debt 1) (max (debt 2) (debt 3)))) =
    finitePlayerMax positive
  have hfinite (who : Fin 4) :
      positive who ≤ finitePlayerMax positive :=
    le_finitePlayerMax positive who
  have hnonneg : 0 ≤ finitePlayerMax positive :=
    (le_max_left 0 (debt 0)).trans (hfinite 0)
  apply le_antisymm
  · apply max_le hnonneg
    apply max_le
    · exact (le_max_right 0 (debt 0)).trans (hfinite 0)
    · apply max_le
      · exact (le_max_right 0 (debt 1)).trans (hfinite 1)
      · apply max_le
        · exact (le_max_right 0 (debt 2)).trans (hfinite 2)
        · exact (le_max_right 0 (debt 3)).trans (hfinite 3)
  · apply finitePlayerMax_le
    intro who
    fin_cases who
    · apply max_le
      · exact le_max_left _ _
      · exact (le_max_left (debt 0) _).trans (le_max_right 0 _)
    · apply max_le
      · exact le_max_left _ _
      · exact (le_max_left (debt 1) _).trans
          ((le_max_right (debt 0) _).trans (le_max_right 0 _))
    · apply max_le
      · exact le_max_left _ _
      · exact (le_max_left (debt 2) (debt 3)).trans
          ((le_max_right (debt 1) _).trans
            ((le_max_right (debt 0) _).trans (le_max_right 0 _)))
    · apply max_le
      · exact le_max_left _ _
      · exact (le_max_right (debt 2) (debt 3)).trans
          ((le_max_right (debt 1) _).trans
            ((le_max_right (debt 0) _).trans (le_max_right 0 _)))

/-- Reverse one-shell reconstruction: every analytic outer-neighborhood point
has a feasible executable representative with exactly the same point pair and
objective. -/
theorem exists_finFourSingleShellFeasibleAssignment_of_mem_outerNeighborhood
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    (level : ℕ)
    (point : QuittingTerminalSemanticPair (Fin 4))
    (hpoint : point ∈
      (escapeAwareQuantileClockSystem
        (fun terminal who ↦ (reward terminal who : ℝ))
        (hasEscapeAwareQuantileClockCompression_of_normalized
          (fun terminal who ↦ (reward terminal who : ℝ)) hreward)).outerNeighborhood
        level) :
    ∃ assign : Fin (finFourSingleShellVariableCount level) → ℝ,
      (finFourRationalSingleShellLowerProblem reward level).Feasible assign ∧
      finFourSingleShellPointPair level assign = point ∧
      RationalMaxExpression.evalReal assign
          (finFourSingleShellObjectiveExpression level) =
        quittingTerminalSemanticExploitability point := by
  let compression := hasEscapeAwareQuantileClockCompression_of_normalized
    (fun terminal who ↦ (reward terminal who : ℝ)) hreward
  obtain ⟨centerAssign, hsolution, hwithinRadius⟩ :=
    exists_quantileClockCenterAssignment_of_mem_outerNeighborhood
      reward compression hpoint
  let weight := finiteClockCenterWeight
    (finFourSingleShellClock level) centerAssign
  have hweight : ∀ player, weight player ∈
      stdSimplex ℝ (FiniteClockAtom (finFourSingleShellClock level)) :=
    finiteClockCenterWeight_mem_stdSimplex
      (Rat.castHom ℝ) reward (finFourSingleShellClock level)
        centerAssign hsolution
  have haux : ∀ player, weight player
      (finiteClockAuxAtom (finFourSingleShellClock level)) = 0 :=
    finiteClockCenterWeight_aux_eq_zero
      (Rat.castHom ℝ) reward (finFourSingleShellClock level)
        centerAssign hsolution
  let center : QuittingTerminalSemanticPair (Fin 4) :=
    finiteClockCenterPair (finFourSingleShellClock level) centerAssign
  have hcenter : center = quittingTerminalSemanticPair
      (fun terminal who ↦ (reward terminal who : ℝ))
      (finiteClockDecodedProfile
        (fun terminal who ↦ (reward terminal who : ℝ))
        (finFourSingleShellClock level) weight hweight) := by
    exact finiteClockCenterPair_eq_terminalSemanticPair_of_satisfies
      (Rat.castHom ℝ) reward (finFourSingleShellClock level)
        centerAssign hsolution
  have hwithin : semanticPairWithin (finFourSingleShellRadiusRat level : ℝ)
      point center := by
    rw [finFourSingleShellRadiusRat_cast]
    exact hwithinRadius
  let assign := finFourSingleShellAssignmentOfData level point center weight
  have hpointEq : finFourSingleShellPointPair level assign = point := by
    apply Prod.ext <;> funext player
    · exact finFourSingleShellAssignmentOfData_pointPayoff
        level point center weight player
    · exact finFourSingleShellAssignmentOfData_pointCap
        level point center weight player
  refine ⟨assign,
    finFourSingleShellAssignmentOfData_feasible reward hreward level point
      center weight hweight haux hcenter hwithin,
    hpointEq, ?_⟩
  rw [evalReal_finFourSingleShellObjectiveExpression, hpointEq]

/-- Objective values of feasible assignments in the executable lower
problem. -/
def finFourRationalSingleShellFeasibleValues
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ) : Set ℝ :=
  {value | ∃ assign,
    (finFourRationalSingleShellLowerProblem reward level).Feasible assign ∧
    value = RationalMaxExpression.evalReal assign
      (finFourSingleShellObjectiveExpression level)}

/-- Forward semantic soundness: every feasible executable objective is the
exploitability of a point in the analytic one-shell outer neighborhood. -/
theorem finFourRationalSingleShellFeasibleValues_subset_shellImage
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    (level : ℕ) :
    finFourRationalSingleShellFeasibleValues reward level ⊆
      quittingTerminalSemanticExploitability ''
        (escapeAwareQuantileClockSystem
          (fun terminal who ↦ (reward terminal who : ℝ))
          (hasEscapeAwareQuantileClockCompression_of_normalized
            (fun terminal who ↦ (reward terminal who : ℝ)) hreward)).outerNeighborhood
          level := by
  rintro value ⟨assign, hfeasible, rfl⟩
  refine ⟨finFourSingleShellPointPair level assign,
    finFourSingleShellPointPair_mem_outerNeighborhood_of_feasible
      reward hreward level assign hfeasible, ?_⟩
  exact (evalReal_finFourSingleShellObjectiveExpression level assign).symm

/-- Reverse semantic completeness: every objective value in the analytic
one-shell image is represented by a feasible executable assignment. -/
theorem finFourRationalSingleShellShellImage_subset_feasibleValues
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    (level : ℕ) :
    quittingTerminalSemanticExploitability ''
        (escapeAwareQuantileClockSystem
          (fun terminal who ↦ (reward terminal who : ℝ))
          (hasEscapeAwareQuantileClockCompression_of_normalized
            (fun terminal who ↦ (reward terminal who : ℝ)) hreward)).outerNeighborhood
          level ⊆
      finFourRationalSingleShellFeasibleValues reward level := by
  rintro value ⟨point, hpoint, rfl⟩
  obtain ⟨assign, hfeasible, -, hobjective⟩ :=
    exists_finFourSingleShellFeasibleAssignment_of_mem_outerNeighborhood
      reward hreward level point hpoint
  exact ⟨assign, hfeasible, hobjective.symm⟩

/-- Exact semantic image of the executable feasible set. -/
theorem finFourRationalSingleShellFeasibleValues_eq_shellImage
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    (level : ℕ) :
    finFourRationalSingleShellFeasibleValues reward level =
      quittingTerminalSemanticExploitability ''
        (escapeAwareQuantileClockSystem
          (fun terminal who ↦ (reward terminal who : ℝ))
          (hasEscapeAwareQuantileClockCompression_of_normalized
            (fun terminal who ↦ (reward terminal who : ℝ)) hreward)).outerNeighborhood
          level := by
  apply Set.Subset.antisymm
  · exact finFourRationalSingleShellFeasibleValues_subset_shellImage
      reward hreward level
  · exact finFourRationalSingleShellShellImage_subset_feasibleValues
      reward hreward level

/-- Pointwise forward value inequality for one feasible certificate target. -/
theorem finFourSingleShellLower_le_objective_of_feasible
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    (level : ℕ)
    (assign : Fin (finFourSingleShellVariableCount level) → ℝ)
    (hfeasible : (finFourRationalSingleShellLowerProblem reward level).Feasible
      assign) :
    finFourSingleShellLower
        (fun terminal who ↦ (reward terminal who : ℝ)) hreward level ≤
      RationalMaxExpression.evalReal assign
        (finFourSingleShellObjectiveExpression level) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro value ⟨point, -, rfl⟩
    exact quittingTerminalSemanticExploitability_nonneg point
  · refine ⟨finFourSingleShellPointPair level assign,
      finFourSingleShellPointPair_mem_outerNeighborhood_of_feasible
        reward hreward level assign hfeasible, ?_⟩
    exact (evalReal_finFourSingleShellObjectiveExpression level assign).symm

/-- Lower value represented by the executable problem. -/
noncomputable def finFourRationalSingleShellProblemValue
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (level : ℕ) : ℝ :=
  sInf (finFourRationalSingleShellFeasibleValues reward level)

/-- The executable problem value is exactly the analytic normalized Fin4
single-shell lower value. -/
theorem finFourRationalSingleShellProblemValue_eq_finFourSingleShellLower
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    (level : ℕ) :
    finFourRationalSingleShellProblemValue reward level =
      finFourSingleShellLower
        (fun terminal who ↦ (reward terminal who : ℝ)) hreward level := by
  rw [finFourRationalSingleShellProblemValue,
    finFourRationalSingleShellFeasibleValues_eq_shellImage
      reward hreward level]
  rfl

/-- Positive shells have at least one feasible executable assignment. -/
theorem finFourRationalSingleShellFeasibleValues_nonempty
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    {level : ℕ} (hlevel : 0 < level) :
    (finFourRationalSingleShellFeasibleValues reward level).Nonempty := by
  rw [finFourRationalSingleShellFeasibleValues_eq_shellImage
    reward hreward level]
  let system := escapeAwareQuantileClockSystem
    (fun terminal who ↦ (reward terminal who : ℝ))
    (hasEscapeAwareQuantileClockCompression_of_normalized
      (fun terminal who ↦ (reward terminal who : ℝ)) hreward)
  exact (system.attainable_nonempty.mono
    (system.attainable_subset_outerNeighborhood hlevel)).image
      quittingTerminalSemanticExploitability

/-- A supplied exact interval tree proving `gamma` for the executable problem
proves the same lower bound for the analytic shell. -/
theorem finFourRationalSingleShellTree_sound
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    {level : ℕ} (hlevel : 0 < level)
    (gamma : ℚ)
    (tree : RationalLowerBoxTree
      (finFourSingleShellVariableCount level)
      finFourSingleShellEqualityCount
      (finFourSingleShellNonnegativeCount level))
    (hverify : (finFourRationalSingleShellLowerProblem reward level).verifies
      gamma tree = true) :
    (gamma : ℝ) ≤ finFourSingleShellLower
      (fun terminal who ↦ (reward terminal who : ℝ)) hreward level := by
  rw [← finFourRationalSingleShellProblemValue_eq_finFourSingleShellLower
    reward hreward level]
  unfold finFourRationalSingleShellProblemValue
  apply le_csInf
  · exact finFourRationalSingleShellFeasibleValues_nonempty
      reward hreward hlevel
  · rintro value ⟨assign, hfeasible, rfl⟩
    exact (finFourRationalSingleShellLowerProblem reward level).verifies_sound
      gamma tree hverify assign hfeasible

/-- Soundness of the executable fair search at any finite returned stage. -/
theorem finFourRationalSingleShellSearch_sound
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    {level : ℕ} (hlevel : 0 < level)
    (gamma : ℚ) (rounds : ℕ)
    {tree : RationalLowerBoxTree
      (finFourSingleShellVariableCount level)
      finFourSingleShellEqualityCount
      (finFourSingleShellNonnegativeCount level)}
    (hsearch : (finFourRationalSingleShellLowerProblem reward level).search
      gamma rounds = some tree) :
    (gamma : ℝ) ≤ finFourSingleShellLower
      (fun terminal who ↦ (reward terminal who : ℝ)) hreward level := by
  apply finFourRationalSingleShellTree_sound reward hreward hlevel gamma tree
  exact (finFourRationalSingleShellLowerProblem reward level).verifies_search
    gamma rounds hsearch

/-- Strict lower queries eventually close under the executable fair search.
The returned tree is also accepted by the base checker. -/
theorem exists_finFourRationalSingleShellSearch_of_lt_lower
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    (level : ℕ) (gamma : ℚ)
    (hgamma : (gamma : ℝ) < finFourSingleShellLower
      (fun terminal who ↦ (reward terminal who : ℝ)) hreward level) :
    ∃ rounds tree,
      (finFourRationalSingleShellLowerProblem reward level).search
          gamma rounds = some tree ∧
        (finFourRationalSingleShellLowerProblem reward level).verifies
          gamma tree = true := by
  apply RationalLowerBoxProblem.exists_search_verifies_of_feasible_objective_gt
    (problem := finFourRationalSingleShellLowerProblem reward level)
      gamma (finFourSingleShellRootBox_valid level)
  intro assign hfeasible
  exact hgamma.trans_le (finFourSingleShellLower_le_objective_of_feasible
    reward hreward level assign hfeasible)

end GameTheory
