/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourSameStageEndpointMonodromy
import Research.Quitting.NonsingletonMinimumLawLinearTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumLawFiniteAtom

/-!
# Source and low-tail producers for the exhaustive Fin4 atlas

This module retains the minimum joint-law source, its literal causal suffix
atom, and the exact selected row consumed by bounded same-stage purification.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open MathUE.FiniteBooleanEndpointOrbit
open QuittingNonsingletonMinimumLawTransfer

/-- The common source retained by every atlas leaf. -/
structure FinFourMinimumAtomProducer
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) where
  residual : FinFourQuantitativeFullSupportHardResidual reward bound
  point : QuittingTerminalSemanticLawPoint (Fin 4)
  point_mem : point ∈ quittingTerminalSemanticLawCarrier reward
  semantic_mem : point.1 ∈ quittingTerminalSemanticCarrier reward
  minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum point.1 ≤
      quittingTerminalSemanticDebtSum candidate
  inf_pos : 0 < quittingTerminalDebtSumInf reward
  debt_eq_inf : quittingTerminalSemanticDebtSum point.1 =
    quittingTerminalDebtSumInf reward
  atom : QuittingMinimumLawCausalSuffixAtom reward point

namespace FinFourMinimumAtomProducer

/-- The displayed minimum point has strictly positive total debt. -/
theorem minimumDebt_pos
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) :
    0 < quittingTerminalSemanticDebtSum source.point.1 := by
  rw [source.debt_eq_inf]
  exact source.inf_pos

/-- A supplied hard residual produces the common minimum-law source without
reselecting the table or losing its residual packet. -/
theorem nonempty_of_hardResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    Nonempty (FinFourMinimumAtomProducer reward bound) := by
  obtain ⟨point, hpoint, hsemantic, hminimum, hinf, hdebt, ⟨atom⟩⟩ :=
    exists_finFourHardResidual_minimumLaw_causalSuffixAtom
      reward bound residual
  exact ⟨{
    residual := residual
    point := point
    point_mem := hpoint
    semantic_mem := hsemantic
    minimum := hminimum
    inf_pos := hinf
    debt_eq_inf := hdebt
    atom := atom
  }⟩

end FinFourMinimumAtomProducer

/-- One literal selected row in the low-tail arm.  Its source profile, cap
roots, atom, and marked date remain inside `rows`. -/
structure FinFourLowTailRow
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  rows : SelectedRows reward source.point source.atom
  rank : ℕ
  stage_mass_floor :
    source.point.2 (some source.atom.terminal) ^ 2 / 8 <
      selectedStageMass rows rank
  tail_excess_lt :
    selectedTailExcess rows rank <
      source.point.2 (some source.atom.terminal) ^ 2 *
        quittingTerminalSemanticDebtSum source.point.1 / 16

namespace FinFourLowTailRow

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The literal prefixed profile carrying the selected row. -/
def profile (row : FinFourLowTailRow source) :
    (quittingGame reward).BehaviorProfile :=
  prefixedProfile reward row.rows.profiles row.rows.roots row.rank

/-- The selected actual date in the prefixed profile. -/
def stage (row : FinFourLowTailRow source) : ℕ :=
  shiftedStage row.rows.roots row.rows.mark row.rank

/-- The uniform mass floor used by the finite same-stage producer. -/
def lambda (_row : FinFourLowTailRow source) : ℝ :=
  source.point.2 (some source.atom.terminal) ^ 2 / 8

/-- The original marked atom viewed as a nonsingleton coalition. -/
def coalition (row : FinFourLowTailRow source) :
    QuittingNonsingletonCoalition (Fin 4) :=
  ⟨source.atom.terminal.val, row.rows.collision⟩

/-- The selected mass floor is positive. -/
theorem lambda_pos (row : FinFourLowTailRow source) : 0 < row.lambda := by
  dsimp only [lambda]
  exact div_pos (pow_pos source.atom.terminalMass_pos 2) (by norm_num)

/-- The selected source row carries the declared mass floor. -/
theorem lambda_le_stageMass (row : FinFourLowTailRow source) :
    row.lambda ≤ quittingStageCoalitionMass reward row.profile row.stage
      source.atom.terminal :=
  row.stage_mass_floor.le

/-- The atlas threshold is exactly the low-tail hypothesis consumed by the
same-stage purification theorem. -/
theorem lowTail (row : FinFourLowTailRow source) :
    quittingSpineDebtExcess reward row.profile
        (quittingTerminalSemanticDebtSum source.point.1) (row.stage + 1) <
      row.lambda * quittingTerminalSemanticDebtSum source.point.1 / 2 := by
  have h := row.tail_excess_lt
  change quittingSpineDebtExcess reward row.profile
      (quittingTerminalSemanticDebtSum source.point.1) (row.stage + 1) <
    source.point.2 (some source.atom.terminal) ^ 2 *
      quittingTerminalSemanticDebtSum source.point.1 / 16 at h
  calc
    quittingSpineDebtExcess reward row.profile
          (quittingTerminalSemanticDebtSum source.point.1) (row.stage + 1) <
        source.point.2 (some source.atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 16 := h
    _ = row.lambda * quittingTerminalSemanticDebtSum source.point.1 / 2 := by
      dsimp only [lambda]
      ring

/-- The exact initial state used by the checked partial-purification path. -/
def initialState (row : FinFourLowTailRow source) :
    QuittingPartialPurificationState reward row.profile row.stage row.lambda :=
  quittingPartialPurificationInitialState reward row.profile row.stage row.lambda
    row.coalition row.lambda_le_stageMass

end FinFourLowTailRow

/-- A singleton reached during the bounded preliminary purification. -/
structure FinFourPurifiedSingletonProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  low : FinFourLowTailRow source
  state : QuittingPartialPurificationState reward low.profile low.stage low.lambda
  steps : ℕ
  singleton :
    QuittingPartialPurificationSingleton reward low.profile low.stage low.lambda state
  path : QuittingPartialPurificationPath reward low.profile low.stage low.lambda
    low.initialState state steps
  steps_le : steps ≤ Fintype.card (Fin 4)

/-- A completed bounded purification, before the finite endpoint orbit is
classified as terminal or cyclic. -/
structure FinFourTotalPurificationProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  low : FinFourLowTailRow source
  finalState :
    QuittingPartialPurificationState reward low.profile low.stage low.lambda
  steps : ℕ
  path : QuittingPartialPurificationPath reward low.profile low.stage low.lambda
    low.initialState finalState steps
  steps_le : steps ≤ Fintype.card (Fin 4)
  complete : ∀ who, finalState.assignment who ≠ none

namespace FinFourTotalPurificationProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The exact source profile of the finite endpoint orbit. -/
def profile (producer : FinFourTotalPurificationProducer source) :
    (quittingGame reward).BehaviorProfile :=
  quittingPartialPurificationStateProfile reward producer.low.profile
    producer.low.stage producer.low.lambda producer.finalState

end FinFourTotalPurificationProducer

end GameTheory
