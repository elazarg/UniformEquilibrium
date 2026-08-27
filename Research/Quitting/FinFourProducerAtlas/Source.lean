/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.NonsingletonMinimumLawLinearTransfer
import Research.Quitting.SameStageEndpointPurification
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumLawFiniteAtom

/-!
# Source selection for the finite Fin4 producer reduction

This module retains one hard residual, one minimum joint semantic/law point,
one causal finite atom, and one selected-row family.  For a nonsingleton atom,
the same selected rows give either a cofinal quantitative tail escape or one
literal low-tail row.  No recursive rank, descent, or backward compiler is
asserted here.
-/

noncomputable section

namespace GameTheory

open Filter
open QuittingNonsingletonMinimumLawTransfer

/-- The common minimum-law source retained by every downstream leaf. -/
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

/-- The selected minimum semantic point has strictly positive total debt. -/
theorem minimumDebt_pos
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) :
    0 < quittingTerminalSemanticDebtSum source.point.1 := by
  rw [source.debt_eq_inf]
  exact source.inf_pos

/-- The quantitative tail threshold is positive for the same fixed minimum
point and causal atom retained by `source`; no point, law, or atom is
reselected to prove the bound. -/
theorem tailThreshold_pos
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) :
    0 < source.point.2 (some source.atom.terminal) ^ 2 *
      quittingTerminalSemanticDebtSum source.point.1 / 16 := by
  exact div_pos
    (mul_pos (pow_pos source.atom.terminalMass_pos 2) source.minimumDebt_pos)
    (by norm_num)

/-- A supplied hard residual produces one common minimum point and causal
finite atom while retaining literal equality to that residual. -/
theorem exists_residual_eq_of_hardResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    ∃ source : FinFourMinimumAtomProducer reward bound,
      source.residual = residual := by
  obtain ⟨point, hpoint, hsemantic, hminimum, hinf, hdebt, ⟨atom⟩⟩ :=
    exists_finFourHardResidual_minimumLaw_causalSuffixAtom
      reward bound residual
  refine ⟨{
    residual := residual
    point := point
    point_mem := hpoint
    semantic_mem := hsemantic
    minimum := hminimum
    inf_pos := hinf
    debt_eq_inf := hdebt
    atom := atom
  }, rfl⟩

/-- Forgetful nonempty form of `exists_residual_eq_of_hardResidual`. -/
theorem nonempty_of_hardResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    Nonempty (FinFourMinimumAtomProducer reward bound) := by
  obtain ⟨source, _⟩ :=
    exists_residual_eq_of_hardResidual reward bound residual
  exact ⟨source⟩

end FinFourMinimumAtomProducer

/-- One literal selected row in the low-tail arm.  Its actual source profile,
exact cap-root stack, atom, and marked date remain available through `rows`. -/
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

/-- The literal prefixed behavioral profile carrying the selected row. -/
def profile (row : FinFourLowTailRow source) :
    (quittingGame reward).BehaviorProfile :=
  prefixedProfile reward row.rows.profiles row.rows.roots row.rank

/-- The selected actual date in the literal prefixed profile. -/
def stage (row : FinFourLowTailRow source) : ℕ :=
  shiftedStage row.rows.roots row.rows.mark row.rank

/-- The fixed quadratic stage-mass scale `mu^2 / 8`. -/
def lambda (_row : FinFourLowTailRow source) : ℝ :=
  source.point.2 (some source.atom.terminal) ^ 2 / 8

/-- The original marked atom, with its nonsingleton proof, is the initial
coalition for same-date purification. -/
def coalition (row : FinFourLowTailRow source) :
    QuittingNonsingletonCoalition (Fin 4) :=
  ⟨source.atom.terminal.val, row.rows.collision⟩

/-- The selected row is definitionally the retained literal prefixed source. -/
theorem profile_eq_prefixedProfile (row : FinFourLowTailRow source) :
    row.profile =
      prefixedProfile reward row.rows.profiles row.rows.roots row.rank := rfl

/-- The selected date is definitionally the retained shifted source mark. -/
theorem stage_eq_shiftedStage (row : FinFourLowTailRow source) :
    row.stage = shiftedStage row.rows.roots row.rows.mark row.rank := rfl

/-- The post-date semantic tail is exactly the selected source tail; no
carrier representative or independently chosen continuation is substituted. -/
theorem tailPair_eq_selectedTail (row : FinFourLowTailRow source) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward row.profile (row.stage + 1)) =
      tailPair reward row.rows.profiles row.rows.roots row.rows.mark row.rank := rfl

/-- The selected cap-root stack remains exact at the chosen source rank. -/
theorem roots_nash (row : FinFourLowTailRow source) :
    IsQuittingCapNashRootStack reward (row.rows.roots row.rank)
      (row.rows.profiles row.rank) :=
  row.rows.roots_nash row.rank

/-- The selected exact cap-root stack has the retained causal depth. -/
theorem roots_length (row : FinFourLowTailRow source) :
    (row.rows.roots row.rank).length = row.rank + 1 :=
  row.rows.roots_length row.rank

/-- The selected mass scale is positive. -/
theorem lambda_pos (row : FinFourLowTailRow source) : 0 < row.lambda := by
  dsimp only [lambda]
  exact div_pos (pow_pos source.atom.terminalMass_pos 2) (by norm_num)

/-- The literal selected source row carries the declared mass floor. -/
theorem lambda_le_stageMass (row : FinFourLowTailRow source) :
    row.lambda ≤ quittingStageCoalitionMass reward row.profile row.stage
      source.atom.terminal :=
  row.stage_mass_floor.le

/-- The exact `mu^2 * D_* / 16` low-tail threshold is the hypothesis consumed
by the same-stage purification theorem. -/
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

/-- The exact initial state for bounded same-date partial purification. -/
def initialState (row : FinFourLowTailRow source) :
    QuittingPartialPurificationState reward row.profile row.stage row.lambda :=
  quittingPartialPurificationInitialState reward row.profile row.stage row.lambda
    row.coalition row.lambda_le_stageMass

end FinFourLowTailRow

namespace FinFourMinimumAtomProducer

/-- For one fixed nonsingleton minimum-law atom and one fixed selected-row
family, either the high-tail predicate occurs frequently and yields a strict
subsequence, or its eventual negation yields one literal low-tail row.  The
weak high threshold and strict low threshold classify equality on the high
side. -/
theorem nonempty_tailEscape_or_lowTailRow
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (hcollision : 1 < source.atom.terminal.val.card) :
    Nonempty (TailEscapeSubsequence reward source.point source.atom) ∨
      Nonempty (FinFourLowTailRow source) := by
  obtain ⟨rows⟩ := QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows
    reward source.point source.atom source.point_mem source.minimum
      source.minimumDebt_pos hcollision
  let highTail : ℕ → Prop := fun rank =>
    source.point.2 (some source.atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 16 ≤
      selectedTailExcess rows rank
  have hstage := rows.eventually_stageMass_gt_square_div_eight source.point_mem
  by_cases hhigh : ∃ᶠ rank in atTop, highTail rank
  · have hboth : ∃ᶠ rank in atTop,
        highTail rank ∧
          source.point.2 (some source.atom.terminal) ^ 2 / 8 <
            selectedStageMass rows rank :=
      hhigh.and_eventually hstage
    obtain ⟨subseq, hsubseq, hselected⟩ :=
      extraction_of_frequently_atTop hboth
    left
    exact ⟨{
      rows := rows
      subseq := subseq
      subseq_strictMono := hsubseq
      stage_mass_floor := fun rank => (hselected rank).2
      tail_excess_floor := fun rank => by
        simpa only [highTail] using (hselected rank).1
    }⟩
  · have hnotHigh : ∀ᶠ rank in atTop, ¬highTail rank :=
      not_frequently.mp hhigh
    have hlow : ∀ᶠ rank in atTop,
        selectedTailExcess rows rank <
          source.point.2 (some source.atom.terminal) ^ 2 *
            quittingTerminalSemanticDebtSum source.point.1 / 16 :=
      hnotHigh.mono fun rank hn => lt_of_not_ge hn
    have hboth : ∀ᶠ rank in atTop,
        source.point.2 (some source.atom.terminal) ^ 2 / 8 <
            selectedStageMass rows rank ∧
          selectedTailExcess rows rank <
            source.point.2 (some source.atom.terminal) ^ 2 *
              quittingTerminalSemanticDebtSum source.point.1 / 16 :=
      hstage.and hlow
    rw [Filter.eventually_atTop] at hboth
    obtain ⟨rank, hrank⟩ := hboth
    have hselected := hrank rank (le_rfl)
    right
    exact ⟨{
      rows := rows
      rank := rank
      stage_mass_floor := hselected.1
      tail_excess_lt := hselected.2
    }⟩

end FinFourMinimumAtomProducer

end GameTheory
