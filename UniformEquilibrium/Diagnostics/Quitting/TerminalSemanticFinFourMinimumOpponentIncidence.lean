/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.LawTightCapNashStrictMinimum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumLawFiniteAtom
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawExploitabilityFloor

/-!
# Positive opponent incidence at a four-player hard-residual minimum

An arbitrary supplied global-minimum joint-law point in the Fin4 hard residual
cannot combine a zero-debt owner with zero total opponent incidence.  The
finite-atom theorem and vanishing incidence would force singleton/Never
support; cap tightness then contradicts the positive minimum singleton margin.

This result does not select the minimum point, construct a source rectangle,
or consume the resulting positive incidence.
-/

noncomputable section

namespace GameTheory
namespace FinFourQuantitativeFullSupportHardResidual

open Math.Probability

/-- A zero-debt owner at any supplied global-minimum joint-law point in the
Fin4 hard residual has positive total opponent incidence. -/
theorem totalOpponentIncidence_pos_of_minimumLaw_of_debt_eq_zero
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (point : QuittingTerminalSemanticLawPoint (Fin 4))
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (owner : Fin 4)
    (hdebt : quittingTerminalSemanticDebt point.1 owner = 0) :
    0 < quittingTerminalTotalOpponentIncidenceMass owner point.2 := by
  have hpair : point.1 ∈ quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hpositive : 0 < quittingTerminalSemanticDebtSum point.1 :=
    residual.witness.terminalGap_pos.trans_le
      (residual.witness.terminalGap_le_terminalSemanticDebtSum
        reward point.1 hpair)
  obtain ⟨terminal, hterminal⟩ :=
    exists_positive_finiteLawAtom_of_finFourHardResidual_minimum
      reward bound residual point hpoint hminimum
  have hmass := terminalSemanticLawCarrier_mass_mem_stdSimplex point hpoint
  by_contra hnotPositive
  have hincidenceNonneg :
      0 ≤ quittingTerminalTotalOpponentIncidenceMass owner point.2 := by
    unfold quittingTerminalTotalOpponentIncidenceMass
    exact Finset.sum_nonneg fun _ _ => by
      unfold quittingTerminalOpponentIncidenceMass
      exact Finset.sum_nonneg fun candidate _ => hmass.1 (some candidate)
  have hincidenceZero :
      quittingTerminalTotalOpponentIncidenceMass owner point.2 = 0 :=
    le_antisymm (le_of_not_gt hnotPositive) hincidenceNonneg
  have hterminalOwner : terminal.val = {owner} :=
    terminal_eq_singleton_of_totalOpponentIncidence_eq_zero_of_mass_pos
      owner point.2 hmass hincidenceZero terminal hterminal
  let p := point.2 (some (quittingSingletonTerminal owner))
  have hp : 0 < p := by
    have hterminalEq : terminal = quittingSingletonTerminal owner :=
      Subtype.ext hterminalOwner
    simpa only [p, hterminalEq] using hterminal
  have hfinite : ∀ candidate : {S : Finset (Fin 4) // S.Nonempty},
      point.2 (some candidate) =
        if candidate.val = {owner} then p else 0 := by
    intro candidate
    by_cases hcandidate : candidate.val = {owner}
    · rw [if_pos hcandidate]
      have hcandidateEq : candidate = quittingSingletonTerminal owner :=
        Subtype.ext hcandidate
      exact congrArg (fun selected => point.2 (some selected)) hcandidateEq
    · rw [if_neg hcandidate]
      by_cases hzero : point.2 (some candidate) = 0
      · exact hzero
      · have hcandidatePositive : 0 < point.2 (some candidate) :=
          lt_of_le_of_ne (hmass.1 (some candidate)) (Ne.symm hzero)
        exact (hcandidate
          (terminal_eq_singleton_of_totalOpponentIncidence_eq_zero_of_mass_pos
            owner point.2 hmass hincidenceZero candidate
              hcandidatePositive)).elim
  have hnever : point.2 none = 1 - p := by
    have hsum := hmass.2
    rw [Fintype.sum_option] at hsum
    have hfiniteSum :
        ∑ candidate : {S : Finset (Fin 4) // S.Nonempty},
          point.2 (some candidate) = p := by
      simp_rw [hfinite]
      have hpredicate : ∀ candidate : {S : Finset (Fin 4) // S.Nonempty},
          candidate.val = {owner} ↔
            candidate = quittingSingletonTerminal owner := by
        intro candidate
        constructor
        · exact fun heq => Subtype.ext heq
        · exact fun heq => congrArg Subtype.val heq
      simp_rw [hpredicate]
      simp
    rw [hfiniteSum] at hsum
    linarith
  have hcap :=
    terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward
      point hpoint owner p hp hfinite hnever hdebt
  have hmargin := minimumTerminalSemantic_singletonMargin
    point.1 hpair hminimum hpositive owner
  rw [hcap] at hmargin
  linarith

end FinFourQuantitativeFullSupportHardResidual
end GameTheory
