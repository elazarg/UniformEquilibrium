/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.PositiveMinimumDebtTangentFamily
import UniformEquilibrium.Quitting.Debt.Dynamic.ChronologicalSeamReduction

/-!
# Positive-minimum seed and direct-seam barrier

A positive-total-debt semantic pair cannot itself be an arbitrarily
small-coordinate-debt seed.  Moreover, replacing that pair by an artificial
small-debt anchor cannot be hidden behind a small direct semantic seam: one
coordinate pays at least the average positive debt minus the requested anchor
debt.

This separates two producer obligations.  Literal executable packets may be
anchored at actual reached positive-minimum sources.  A low-debt candidate
anchor instead needs an external source/payoff-to-candidate adapter (or a
separate solved-game disjunct); identifying the two anchors is contradictory.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Some coordinate is at least the average whenever aggregate semantic debt
is positive. -/
theorem exists_quittingTerminalSemanticDebt_ge_average
    [Nonempty ι] (pair : QuittingTerminalSemanticPair ι)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) :
    ∃ who,
      quittingTerminalSemanticDebtSum pair / Fintype.card ι ≤
        quittingTerminalSemanticDebt pair who := by
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  by_contra hnot
  push Not at hnot
  have hsum : quittingTerminalSemanticDebtSum pair <
      ∑ _who : ι,
        quittingTerminalSemanticDebtSum pair / Fintype.card ι := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      fun who _ => hnot who
  have hconstant :
      (∑ _who : ι,
          quittingTerminalSemanticDebtSum pair / Fintype.card ι) =
        quittingTerminalSemanticDebtSum pair := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [hconstant] at hsum
  exact (lt_irrefl _ hsum)

omit [Fintype ι] [DecidableEq ι] in
/-- A debt difference is bounded by the direct two-coordinate semantic seam.
No carrier or nonnegativity premise is needed. -/
theorem quittingTerminalSemanticDebt_sub_le_directSeam
    (source anchor : QuittingTerminalSemanticPair ι) (who : ι) :
    quittingTerminalSemanticDebt source who -
        quittingTerminalSemanticDebt anchor who ≤
      |source.1 who - anchor.1 who| + |source.2 who - anchor.2 who| := by
  unfold quittingTerminalSemanticDebt
  have hfirst := neg_le_abs (source.1 who - anchor.1 who)
  have hsecond := le_abs_self (source.2 who - anchor.2 who)
  rw [show
    (source.2 who - source.1 who) - (anchor.2 who - anchor.1 who) =
      (source.2 who - anchor.2 who) -
        (source.1 who - anchor.1 who) by ring]
  linarith

omit [DecidableEq ι] in
/-- No positive-total-debt semantic pair is a coordinatewise seed below its
average debt. -/
theorem not_forall_quittingTerminalSemanticDebt_le_of_lt_average
    [Nonempty ι] (pair : QuittingTerminalSemanticPair ι)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (eta : ℝ)
    (heta : eta < quittingTerminalSemanticDebtSum pair / Fintype.card ι) :
    ¬∀ who, quittingTerminalSemanticDebt pair who ≤ eta := by
  intro hsmall
  obtain ⟨who, haverage⟩ :=
    exists_quittingTerminalSemanticDebt_ge_average pair hpositive
  exact (not_le_of_gt heta) (haverage.trans (hsmall who))

omit [DecidableEq ι] in
/-- A coordinatewise small-debt anchor is separated from any positive-debt
source by the average-debt gap in one direct semantic seam. -/
theorem exists_directSemanticSeam_ge_average_sub
    [Nonempty ι]
    (source anchor : QuittingTerminalSemanticPair ι)
    (hpositive : 0 < quittingTerminalSemanticDebtSum source)
    (eta : ℝ)
    (hanchor : ∀ who, quittingTerminalSemanticDebt anchor who ≤ eta) :
    ∃ who,
      quittingTerminalSemanticDebtSum source / Fintype.card ι - eta ≤
        |source.1 who - anchor.1 who| +
          |source.2 who - anchor.2 who| := by
  obtain ⟨who, haverage⟩ :=
    exists_quittingTerminalSemanticDebt_ge_average source hpositive
  refine ⟨who, ?_⟩
  calc
    quittingTerminalSemanticDebtSum source / Fintype.card ι - eta ≤
        quittingTerminalSemanticDebt source who -
          quittingTerminalSemanticDebt anchor who := by
      linarith [hanchor who]
    _ ≤ |source.1 who - anchor.1 who| +
        |source.2 who - anchor.2 who| :=
      quittingTerminalSemanticDebt_sub_le_directSeam source anchor who

namespace QuittingPositiveMinimumDebtTangentFamily

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  (family : QuittingPositiveMinimumDebtTangentFamily reward)

/-- One base coordinate carries at least the average positive minimum debt. -/
theorem exists_baseDebt_ge_average :
    ∃ who,
      quittingTerminalSemanticDebtSum family.base / Fintype.card ι ≤
        quittingTerminalSemanticDebt family.base who := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by
    by_contra hnot
    have hzero : Fintype.card ι = 0 := by omega
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hzero
    have hbaseZero : quittingTerminalSemanticDebtSum family.base = 0 := by
      simp [quittingTerminalSemanticDebtSum]
    have hpositive := family.base_positive
    rw [hbaseZero] at hpositive
    exact (lt_irrefl 0 hpositive))
  exact exists_quittingTerminalSemanticDebt_ge_average
    family.base family.base_positive

/-- The actual positive-minimum base cannot also be a coordinatewise
small-debt seed below its average debt. -/
theorem not_baseDebt_le_of_lt_average
    (eta : ℝ)
    (heta : eta <
      quittingTerminalSemanticDebtSum family.base / Fintype.card ι) :
    ¬∀ who, quittingTerminalSemanticDebt family.base who ≤ eta := by
  intro hsmall
  obtain ⟨who, haverage⟩ := family.exists_baseDebt_ge_average
  exact (not_le_of_gt heta) (haverage.trans (hsmall who))

/-- Any small-debt artificial anchor is separated from the actual base by a
direct semantic seam of at least average base debt minus the anchor ceiling. -/
theorem exists_directSeam_ge_average_sub
    (anchor : QuittingTerminalSemanticPair ι) (eta : ℝ)
    (hanchor : ∀ who,
      quittingTerminalSemanticDebt anchor who ≤ eta) :
    ∃ who,
      quittingTerminalSemanticDebtSum family.base / Fintype.card ι - eta ≤
        |family.base.1 who - anchor.1 who| +
          |family.base.2 who - anchor.2 who| := by
  obtain ⟨who, haverage⟩ := family.exists_baseDebt_ge_average
  refine ⟨who, ?_⟩
  calc
    quittingTerminalSemanticDebtSum family.base / Fintype.card ι - eta ≤
        quittingTerminalSemanticDebt family.base who -
          quittingTerminalSemanticDebt anchor who := by
      linarith [hanchor who]
    _ ≤ |family.base.1 who - anchor.1 who| +
        |family.base.2 who - anchor.2 who| :=
      quittingTerminalSemanticDebt_sub_le_directSeam family.base anchor who

/-- In the strict small-debt regime, the forced direct seam is positive. -/
theorem exists_directSeam_pos_of_lt_average
    (anchor : QuittingTerminalSemanticPair ι) (eta : ℝ)
    (hanchor : ∀ who,
      quittingTerminalSemanticDebt anchor who ≤ eta)
    (heta : eta <
      quittingTerminalSemanticDebtSum family.base / Fintype.card ι) :
    ∃ who,
      0 < |family.base.1 who - anchor.1 who| +
        |family.base.2 who - anchor.2 who| := by
  obtain ⟨who, hseam⟩ := family.exists_directSeam_ge_average_sub anchor eta hanchor
  exact ⟨who, lt_of_lt_of_le (sub_pos.mpr heta) hseam⟩

/-- The same lower bound stated on the exact block seam consumed by the
chronological flattening interface. -/
theorem exists_totalBlockSeamNat_ge_average_sub
    (blocks : QuittingVariableLengthSeamBlocksNat reward) (block : ℕ)
    (anchor : QuittingTerminalSemanticPair ι) (eta : ℝ)
    (hendpoint : blocks.candidate block (blocks.length block) = family.base)
    (hnext : blocks.candidate (block + 1) 0 = anchor)
    (hanchor : ∀ who,
      quittingTerminalSemanticDebt anchor who ≤ eta) :
    ∃ who,
      quittingTerminalSemanticDebtSum family.base / Fintype.card ι - eta ≤
        blocks.totalBlockSeamNat who block := by
  obtain ⟨who, hseam⟩ := family.exists_directSeam_ge_average_sub anchor eta hanchor
  refine ⟨who, ?_⟩
  simpa [QuittingVariableLengthSeamBlocksNat.totalBlockSeamNat,
    QuittingVariableLengthSeamBlocksNat.prescribedBlockSeamNat,
    QuittingVariableLengthSeamBlocksNat.capBlockSeamNat,
    hendpoint, hnext] using hseam

end QuittingPositiveMinimumDebtTangentFamily

end GameTheory
