/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumAggregateSurplus
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalRewardSparseAlternative

/-!
# Sparse reward improvement selected inside a minimum joint-law support

The selected atom identities come from the positive support of the supplied
joint-carrier law.  The coefficients are reweighted by conic compression, so
the resulting sparse law is not asserted to retain the original reward
moment, behavioral realization, or deviation cap.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A sparse coordinatewise-improving law whose selected atom identities all
belong to one supplied source law. -/
structure QuittingTerminalSemanticLawSparseSourceImprovement
    (point : QuittingTerminalSemanticLawPoint ι) where
  law : QuittingTerminalOutcome ι → ℝ
  law_nonnegative : ∀ outcome, 0 ≤ law outcome
  law_sum_eq_one : ∑ outcome, law outcome = 1
  source_support : ∀ outcome, law outcome ≠ 0 → point.2 outcome ≠ 0
  coordinate_nonnegative : ∀ who,
    0 ≤ ∑ outcome, law outcome *
      quittingTerminalOutcomeSingletonSurplus reward outcome who
  coordinate_positive : ∃ who,
    0 < ∑ outcome, law outcome *
      quittingTerminalOutcomeSingletonSurplus reward outcome who
  support_card_le : Fintype.card {outcome // law outcome ≠ 0} ≤
    Fintype.card ι

omit [Nonempty ι] in
/-- A positive minimum joint-law point has a sparse coordinatewise-improving
law selected entirely from its literal positive atom support. -/
theorem nonempty_terminalSemanticLawSparseSourceImprovement_of_positiveMinimum
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum point.1)
    (hcard : 1 < Fintype.card ι) :
    Nonempty
      (QuittingTerminalSemanticLawSparseSourceImprovement
        (reward := reward) point) := by
  classical
  let support := Math.LinearAlgebra.positiveSupport point.2
  let vector : support → ι → ℝ := fun outcome who ↦
    quittingTerminalOutcomeSingletonSurplus reward outcome.1 who
  let initial : support → ℝ := fun outcome ↦ point.2 outcome.1
  let target : ι → ℝ := fun who ↦
    point.1.1 who - reward (quittingSingletonTerminal who) who
  have hmass := terminalSemanticLawCarrier_mass_mem_stdSimplex point hpoint
  have hmoment := terminalSemanticLawCarrier_rewardMoment reward point hpoint
  have hinitialNonnegative : ∀ outcome, 0 ≤ initial outcome :=
    fun outcome ↦ hmass.1 outcome.1
  have hreconstruct : ∀ who,
      ∑ outcome, initial outcome * vector outcome who = target who := by
    intro who
    calc
      (∑ outcome : support, initial outcome * vector outcome who) =
          ∑ outcome, point.2 outcome *
            quittingTerminalOutcomeSingletonSurplus reward outcome who := by
        exact Math.LinearAlgebra.sum_positiveSupport point.2
          (fun outcome ↦ point.2 outcome *
            quittingTerminalOutcomeSingletonSurplus reward outcome who)
          (fun outcome hzero ↦ by simp [hzero])
      _ = target who := by
        unfold quittingTerminalOutcomeSingletonSurplus target
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass.2, one_mul]
        have hcoordinate := congrFun hmoment who
        unfold quittingTerminalRewardMoment at hcoordinate
        rw [hcoordinate]
  obtain ⟨sparse, hsparseNonnegative, hsparseTarget, hsparseCard⟩ :=
    Math.LinearAlgebra.exists_nonnegative_finiteCombination_eq_support_card_le
      vector target initial hinitialNonnegative hreconstruct
  have htargetNonnegative : ∀ who, 0 ≤ target who := by
    have hpair := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
    have hdebtNonnegative : ∀ who,
        0 ≤ quittingTerminalSemanticDebt point.1 who :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
    have hdebtLe : ∀ who,
        quittingTerminalSemanticDebt point.1 who ≤
          quittingTerminalSemanticDebtSum point.1 := by
      intro who
      unfold quittingTerminalSemanticDebtSum
      exact Finset.single_le_sum
        (fun current _ ↦ hdebtNonnegative current) (Finset.mem_univ who)
    have hmargin := minimumTerminalSemantic_singletonMargin
      point.1 hpair hminimum hpositive
    intro who
    have hwho := hmargin who
    unfold target
    unfold quittingTerminalSemanticDebt at hdebtLe
    linarith [hdebtLe who]
  have htargetPositive : ∃ who, 0 < target who := by
    have hpair := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
    have hsum := minimumTerminalSemantic_subset_singletonSurplus
      point.1 Finset.univ hpair hminimum hpositive
    have hcardReal : (1 : ℝ) < Fintype.card ι := by
      exact_mod_cast hcard
    have hfactor : 0 < ((Fintype.card ι : ℝ) - 1) := by linarith
    have hsumPositive : 0 < ∑ who, target who := by
      have hleft : 0 < ((Fintype.card ι : ℝ) - 1) *
          quittingTerminalSemanticDebtSum point.1 :=
        mul_pos hfactor hpositive
      simpa only [Finset.card_univ, target] using hleft.trans_le hsum
    by_contra hnone
    push Not at hnone
    exact (not_lt_of_ge (Finset.sum_nonpos fun who _ ↦ hnone who))
      hsumPositive
  let raw : Math.LinearAlgebra.SparseNonnegativeConeImprovement vector := {
    coefficient := sparse
    coefficient_nonnegative := hsparseNonnegative
    value_nonnegative := fun who ↦ by
      rw [hsparseTarget who]
      exact htargetNonnegative who
    value_positive := by
      obtain ⟨who, hwho⟩ := htargetPositive
      exact ⟨who, by rw [hsparseTarget who]; exact hwho⟩
    support_card_le := hsparseCard }
  let normalized := raw.normalized
  let law : QuittingTerminalOutcome ι → ℝ := fun outcome ↦
    if h : outcome ∈ support then normalized.weight ⟨outcome, h⟩ else 0
  have hlawZero : ∀ outcome, point.2 outcome = 0 → law outcome = 0 := by
    intro outcome hzero
    have hnot : outcome ∉ support := by
      simp [support, Math.LinearAlgebra.positiveSupport, hzero]
    simp only [law, dif_neg hnot]
  have hlawSum : ∑ outcome, law outcome = 1 := by
    calc
      ∑ outcome, law outcome = ∑ outcome : support, law outcome.1 :=
        (Math.LinearAlgebra.sum_positiveSupport point.2 law hlawZero).symm
      _ = ∑ outcome : support, normalized.weight outcome := by
        apply Finset.sum_congr rfl
        intro outcome _
        simp only [law, dif_pos outcome.2]
      _ = 1 := normalized.weight_sum_eq_one
  have hlawValue : ∀ who,
      (∑ outcome, law outcome *
        quittingTerminalOutcomeSingletonSurplus reward outcome who) =
      ∑ outcome : support, normalized.weight outcome * vector outcome who := by
    intro who
    calc
      _ = ∑ outcome : support,
          law outcome.1 *
            quittingTerminalOutcomeSingletonSurplus reward outcome.1 who :=
        (Math.LinearAlgebra.sum_positiveSupport point.2
          (fun outcome ↦ law outcome *
            quittingTerminalOutcomeSingletonSurplus reward outcome who)
          (fun outcome hzero ↦ by rw [hlawZero outcome hzero, zero_mul])).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro outcome _
        simp only [law, dif_pos outcome.2]
        rfl
  have hlawSupportCard : Fintype.card {outcome // law outcome ≠ 0} ≤
      Fintype.card ι := by
    let embed : {outcome // law outcome ≠ 0} →
        {outcome : support // normalized.weight outcome ≠ 0} :=
      fun outcome ↦ by
        have hsource : point.2 outcome.1 ≠ 0 := by
          intro hzero
          exact outcome.2 (hlawZero outcome.1 hzero)
        have hmem : outcome.1 ∈ support := by
          simpa [support, Math.LinearAlgebra.positiveSupport] using hsource
        refine ⟨⟨outcome.1, hmem⟩, ?_⟩
        simpa only [law, dif_pos hmem] using outcome.2
    have hinjective : Function.Injective embed := by
      intro left right heq
      apply Subtype.ext
      exact congrArg (fun outcome ↦ outcome.1.1) heq
    exact (Fintype.card_le_of_injective embed hinjective).trans
      normalized.support_card_le
  exact ⟨{
    law := law
    law_nonnegative := fun outcome ↦ by
      simp only [law]
      split_ifs with hmem
      · exact normalized.weight_nonnegative ⟨outcome, hmem⟩
      · exact le_rfl
    law_sum_eq_one := hlawSum
    source_support := fun outcome hlaw ↦ by
      intro hzero
      exact hlaw (hlawZero outcome hzero)
    coordinate_nonnegative := fun who ↦ by
      rw [hlawValue who]
      exact normalized.value_nonnegative who
    coordinate_positive := by
      obtain ⟨who, hwho⟩ := normalized.value_positive
      exact ⟨who, by rw [hlawValue who]; exact hwho⟩
    support_card_le := hlawSupportCard }⟩

end GameTheory
