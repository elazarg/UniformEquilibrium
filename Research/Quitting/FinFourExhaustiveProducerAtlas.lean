/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumLawFiniteAtom
import Research.Quitting.NonsingletonMinimumLawLinearTransfer

/-!
# Exhaustive source-preserving Fin4 producer atlas

This file packages the first genuinely exhaustive finite atlas below the
four-player hard residual.  A source records one globally minimizing joint
terminal-law point, its positive minimum debt, and the literal causal suffix
atom produced at that same point.  The finite residual family then splits
only along checked exhaustive edges:

* a singleton minimum-law atom;
* a nonsingleton atom with a quantitative tail-escape subsequence; or
* a nonsingleton atom with one fixed four-player routed-transfer subsequence.

No constructor identifies the suffix atom with a cap-prefix root, and no
real-valued transfer is called a regenerated descent.  Later refinements can
replace one constructor only by proving an exhaustive source-matched split of
that constructor.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability StochasticGame
open scoped Topology

namespace FinFourProducerAtlas

/-- The complete source produced from one supplied hard residual.  The atom
and its chronology remain attached to the same selected minimum joint-law
point. -/
structure Source
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (hard : FinFourQuantitativeFullSupportHardResidual reward bound) where
  point : QuittingTerminalSemanticLawPoint (Fin 4)
  point_mem : point ∈ quittingTerminalSemanticLawCarrier reward
  semantic_mem : point.1 ∈ quittingTerminalSemanticCarrier reward
  minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum point.1 ≤
      quittingTerminalSemanticDebtSum candidate
  debtInf_pos : 0 < quittingTerminalDebtSumInf reward
  debt_eq_inf : quittingTerminalSemanticDebtSum point.1 =
    quittingTerminalDebtSumInf reward
  atom : QuittingMinimumLawCausalSuffixAtom reward point

/-- A hard residual produces the complete source without reselecting the
minimum or the terminal-law atom. -/
theorem nonempty_source
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (hard : FinFourQuantitativeFullSupportHardResidual reward bound) :
    Nonempty (Source reward bound hard) := by
  obtain ⟨point, hpoint, hsemantic, hminimum, hinf, heq, ⟨atom⟩⟩ :=
    exists_finFourHardResidual_minimumLaw_causalSuffixAtom reward bound hard
  exact ⟨{
    point := point
    point_mem := hpoint
    semantic_mem := hsemantic
    minimum := hminimum
    debtInf_pos := hinf
    debt_eq_inf := heq
    atom := atom }⟩

/-- The three checked producer modes at the current source boundary. -/
inductive Mode where
  | singleton
  | tailEscape
  | routedTransfer
  deriving DecidableEq

/-- The first finite source-carrying atlas.  Each constructor stores the whole
upstream source and the exact certificate produced on that source. -/
inductive Residual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (hard : FinFourQuantitativeFullSupportHardResidual reward bound) : Type
  | singleton (source : Source reward bound hard)
      (terminal_card : source.atom.terminal.val.card = 1)
  | tailEscape (source : Source reward bound hard)
      (terminal_card : 1 < source.atom.terminal.val.card)
      (escape : QuittingNonsingletonMinimumLawTransfer.TailEscapeSubsequence
        reward source.point source.atom)
  | routedTransfer (source : Source reward bound hard)
      (terminal_card : 1 < source.atom.terminal.val.card)
      (transfer :
        QuittingNonsingletonMinimumLawTransfer.FinFourRoutedTransferSubsequence
          reward source.point source.atom)

/-- Forgetting continuous data leaves one of exactly three finite mode labels. -/
def Residual.mode
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {hard : FinFourQuantitativeFullSupportHardResidual reward bound} :
    Residual reward bound hard → Mode
  | .singleton .. => .singleton
  | .tailEscape .. => .tailEscape
  | .routedTransfer .. => .routedTransfer

/-- The minimum debt stored in every source is strictly positive. -/
theorem Source.minimumDebt_pos
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {hard : FinFourQuantitativeFullSupportHardResidual reward bound}
    (source : Source reward bound hard) :
    0 < quittingTerminalSemanticDebtSum source.point.1 := by
  rw [source.debt_eq_inf]
  exact source.debtInf_pos

/-- **Exhaustive atlas coverage.**  Every four-player hard residual produces
one of the three current obligation types: singleton atom, quantitative tail
escape, or fixed routed transfer.  The nonsingleton split is the checked
source-matched linear-transfer theorem, not a static relabelling. -/
theorem nonempty_residual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (hard : FinFourQuantitativeFullSupportHardResidual reward bound) :
    Nonempty (Residual reward bound hard) := by
  obtain ⟨source⟩ := nonempty_source reward bound hard
  by_cases hsingleton : source.atom.terminal.val.card = 1
  · exact ⟨.singleton source hsingleton⟩
  have hcardPos : 0 < source.atom.terminal.val.card :=
    source.atom.terminal.property.card_pos
  have hcollision : 1 < source.atom.terminal.val.card := by omega
  rcases source.atom.nonempty_finFourTailEscape_or_routedTransfer
      reward source.point source.atom source.point_mem source.minimum
        source.minimumDebt_pos hcollision with ⟨escape⟩ | ⟨transfer⟩
  · exact ⟨.tailEscape source hcollision escape⟩
  · exact ⟨.routedTransfer source hcollision transfer⟩

/-- A finite collection of mode-level no-go theorems eliminates the hard
residual.  This is the accumulation principle: once a constructor is ruled
out on its full stored source type, it never has to be reconsidered under a
new parameterization. -/
theorem false_of_exhaustive_mode_noGos
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (hard : FinFourQuantitativeFullSupportHardResidual reward bound)
    (singleton_noGo : ∀ (source : Source reward bound hard),
      source.atom.terminal.val.card = 1 → False)
    (tailEscape_noGo : ∀ (source : Source reward bound hard),
      1 < source.atom.terminal.val.card →
      QuittingNonsingletonMinimumLawTransfer.TailEscapeSubsequence
        reward source.point source.atom → False)
    (routedTransfer_noGo : ∀ (source : Source reward bound hard),
      1 < source.atom.terminal.val.card →
      QuittingNonsingletonMinimumLawTransfer.FinFourRoutedTransferSubsequence
        reward source.point source.atom → False) :
    False := by
  obtain ⟨residual⟩ := nonempty_residual reward bound hard
  cases residual with
  | singleton source hcard => exact singleton_noGo source hcard
  | tailEscape source hcard escape =>
      exact tailEscape_noGo source hcard escape
  | routedTransfer source hcard transfer =>
      exact routedTransfer_noGo source hcard transfer

end FinFourProducerAtlas

end GameTheory
