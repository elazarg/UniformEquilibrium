/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawTangentExtraction

/-!
# Vanishing-regret stopping-law tangent extraction

The common-base stopping-law extractor can choose each complete unilateral
replacement with regret bounded by the smaller of the square of the reset
scale and half of the mover's source debt.  The first bound makes endpoint
regret vanish; the second keeps the choice tolerance strictly positive at
every source.  Consequently the limiting mover diagonal is exactly the
negative base debt, rather than merely at most half of it.

This is a base-parameterized extraction theorem.  Applying it after moving to
a different minimum semantic point requires a fresh realizing sequence and a
fresh extraction at that new base.  No semantic endpoint integration or
chronological strategy is asserted here.
-/

noncomputable section

namespace GameTheory

open Filter Set
open Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Common-base tangent extraction with exact mover diagonal.**

The scale and near-minimum hypotheses are those used by
`exists_commonBase_stoppingLawDebtTangentFamily`.  Base carrier membership,
positive total base debt, and a characterization of the active set are not
needed once source positivity is supplied directly.  The selected full-reset
endpoint has own debt converging to zero for every active mover, and hence the
normalized self chord converges exactly to minus the mover's base debt. -/
theorem exists_commonBase_stoppingLawDebtTangentFamily_exactDiagonal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (active : Finset ι) (epsilon lambda : ℕ → ℝ)
    (hprofiles : Tendsto
      (fun n ↦ quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds base))
    (hsourceActive : ∀ n, ∀ who ∈ active,
      0 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) who)
    (hnear : ∀ n, ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles n)) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon n)
    (hlambdaPos : ∀ n, 0 < lambda n)
    (hlambdaLe : ∀ n, lambda n ≤ 1)
    (hlambdaZero : Tendsto lambda atTop (nhds 0))
    (herrorRate : Tendsto (fun n ↦ epsilon n / lambda n)
      atTop (nhds 0))
    (hinactiveRate : ∀ who,
      quittingTerminalSemanticDebt base who = 0 →
      Tendsto (fun n ↦
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles n)) who /
          lambda n) atTop (nhds 0)) :
    ∃ bestResponse : ∀ mover : {who // who ∈ active},
        ℕ → (quittingGame reward).BehaviorStrategy mover.1,
      ∃ subseq : ℕ → ℕ,
      ∃ tangent : {who // who ∈ active} → ι → ℝ,
        StrictMono subseq ∧
        Tendsto (fun rank ↦ lambda (subseq rank)) atTop (nhds 0) ∧
        (∀ mover observer,
          Tendsto (fun rank ↦
            quittingStoppingLawNormalizedDebtDirection reward
              (profiles (subseq rank)) mover.1
              (bestResponse mover (subseq rank)) (lambda (subseq rank))
              (hlambdaPos (subseq rank)).le (hlambdaLe (subseq rank)) observer)
            atTop (nhds (tangent mover observer))) ∧
        (∀ mover rank,
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (Function.update (profiles (subseq rank)) mover.1
                  (bestResponse mover (subseq rank)))) mover.1 ≤
            min (lambda (subseq rank) ^ 2)
              (quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (profiles (subseq rank))) mover.1 / 2)) ∧
        (∀ mover,
          Tendsto (fun rank ↦
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (Function.update (profiles (subseq rank)) mover.1
                  (bestResponse mover (subseq rank)))) mover.1)
            atTop (nhds 0)) ∧
        (∀ mover, tangent mover mover.1 =
          -quittingTerminalSemanticDebt base mover.1) ∧
        (∀ mover observer,
          quittingTerminalSemanticDebt base observer = 0 →
            0 ≤ tangent mover observer) ∧
        (∀ mover, 0 ≤ ∑ observer, tangent mover observer) ∧
        ((∃ mover, 0 < ∑ observer, tangent mover observer) ∨
          ∀ mover, ∑ observer, tangent mover observer = 0) := by
  obtain ⟨M, -, hreward⟩ := exists_quittingRewardBound reward
  have hchoice : ∀ n, ∀ mover : {who // who ∈ active},
      ∃ replacement : (quittingGame reward).BehaviorStrategy mover.1,
        quittingContinuationBestResponseValue reward (profiles n) mover.1 -
            min (lambda n ^ 2)
              (quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward (profiles n)) mover.1 / 2) ≤
          quittingTerminalPayoff reward
            (Function.update (profiles n) mover.1 replacement) mover.1 := by
    intro n mover
    apply exists_quittingContinuation_deviation_ge_sub
      (reward := reward) (continuation := profiles n) (who := mover.1)
      (δ := min (lambda n ^ 2)
        (quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (profiles n)) mover.1 / 2))
    exact lt_min (sq_pos_of_pos (hlambdaPos n))
      (div_pos (hsourceActive n mover.1 mover.2) (by norm_num))
  choose bestResponse hbestResponse using hchoice
  let endpointDebt : ℕ → {who // who ∈ active} → ℝ :=
    fun n mover ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update (profiles n) mover.1 (bestResponse n mover))) mover.1
  have hendpointDebtNonneg : ∀ n mover, 0 ≤ endpointDebt n mover := by
    intro n mover
    dsimp only [endpointDebt]
    exact quittingTerminalDeviationDebt_nonneg reward
      (Function.update (profiles n) mover.1 (bestResponse n mover)) mover.1
  have hendpointDebtLeTolerance : ∀ n mover,
      endpointDebt n mover ≤
        min (lambda n ^ 2)
          (quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles n)) mover.1 / 2) := by
    intro n mover
    have hbest := hbestResponse n mover
    dsimp only [endpointDebt, quittingTerminalSemanticDebt,
      quittingTerminalSemanticPair] at hbest ⊢
    rw [quittingContinuationBestResponseValue_update_self]
    linarith
  have hendpointDebtLe : ∀ n mover,
      endpointDebt n mover ≤ lambda n ^ 2 := by
    intro n mover
    exact (hendpointDebtLeTolerance n mover).trans (min_le_left _ _)
  have hendpointDebtZero : ∀ mover,
      Tendsto (fun n ↦ endpointDebt n mover) atTop (nhds 0) := by
    intro mover
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ hendpointDebtNonneg n mover
    · exact Eventually.of_forall fun n ↦ hendpointDebtLe n mover
    · simpa using hlambdaZero.pow 2
  let direction : ℕ → {who // who ∈ active} → ι → ℝ :=
    fun n mover observer ↦
      quittingStoppingLawNormalizedDebtDirection reward (profiles n) mover.1
        (bestResponse n mover) (lambda n) (hlambdaPos n).le (hlambdaLe n)
          observer
  let directionBox : Set ({who // who ∈ active} → ι → ℝ) :=
    Set.univ.pi fun _ ↦ Set.univ.pi fun _ ↦ Set.Icc (-4 * M) (4 * M)
  have hdirectionBoxCompact : IsCompact directionBox :=
    isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hdirectionBox : ∀ n, direction n ∈ directionBox := by
    intro n
    rw [Set.mem_univ_pi]
    intro mover
    rw [Set.mem_univ_pi]
    intro observer
    have hbound := abs_quittingTerminalSemanticDebt_stoppingLawMixture_sub_le
      reward (profiles n) mover.1 observer (bestResponse n mover)
        (lambda n) (hlambdaPos n).le (hlambdaLe n) hreward
    dsimp only [direction, quittingStoppingLawNormalizedDebtDirection,
      quittingStoppingLawResetProfile]
    have hnormalized :
        |quittingTerminalSemanticDebtChange
            (quittingTerminalSemanticPair reward (profiles n))
            (quittingTerminalSemanticPair reward
              (Function.update (profiles n) mover.1
                (quittingStoppingLawMixtureBehaviorStrategy reward mover.1
                  ((profiles n) mover.1) (bestResponse n mover) (lambda n)
                    (hlambdaPos n).le (hlambdaLe n)))) observer / lambda n| ≤
          4 * M := by
      rw [abs_div, abs_of_pos (hlambdaPos n), div_le_iff₀ (hlambdaPos n)]
      simpa only [quittingTerminalSemanticDebtChange, mul_assoc] using hbound
    rw [abs_le] at hnormalized
    constructor <;> nlinarith [hnormalized.1, hnormalized.2]
  obtain ⟨tangent, _htangentBox, subseq, hsubseq, htangent⟩ :=
    hdirectionBoxCompact.tendsto_subseq hdirectionBox
  have htangentCoordinate : ∀ mover observer,
      Tendsto (fun rank ↦ direction (subseq rank) mover observer)
        atTop (nhds (tangent mover observer)) := by
    intro mover observer
    exact (tendsto_pi_nhds.1 ((tendsto_pi_nhds.1 htangent) mover)) observer
  have hsourceDebt : ∀ who, Tendsto (fun n ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) who)
      atTop (nhds (quittingTerminalSemanticDebt base who)) := by
    intro who
    exact (continuous_quittingTerminalSemanticDebt who).tendsto base |>.comp
      hprofiles
  have hdirectionSelf : ∀ n mover,
      direction n mover mover.1 =
        endpointDebt n mover -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles n)) mover.1 := by
    intro n mover
    have haffine := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
      reward (profiles n) mover.1 ((profiles n) mover.1)
        (bestResponse n mover) (lambda n) (hlambdaPos n).le (hlambdaLe n)
    rw [Function.update_eq_self] at haffine
    dsimp only [direction, quittingStoppingLawNormalizedDebtDirection,
      quittingStoppingLawResetProfile, quittingTerminalSemanticDebtChange]
    apply (div_eq_iff (ne_of_gt (hlambdaPos n))).2
    rw [haffine]
    dsimp only [endpointDebt]
    ring
  have hdiagonal : ∀ mover,
      tangent mover mover.1 =
        -quittingTerminalSemanticDebt base mover.1 := by
    intro mover
    have hdirectionLimit : Tendsto
        (fun rank ↦ direction (subseq rank) mover mover.1) atTop
        (nhds (-quittingTerminalSemanticDebt base mover.1)) := by
      have hendpoint := (hendpointDebtZero mover).comp hsubseq.tendsto_atTop
      have hsource := (hsourceDebt mover.1).comp hsubseq.tendsto_atTop
      convert hendpoint.sub hsource using 1
      · funext rank
        exact hdirectionSelf (subseq rank) mover
      · ring_nf
    exact tendsto_nhds_unique (htangentCoordinate mover mover.1) hdirectionLimit
  have hinactiveNonneg : ∀ mover observer,
      quittingTerminalSemanticDebt base observer = 0 →
        0 ≤ tangent mover observer := by
    intro mover observer hzero
    have hpointwise : ∀ n,
        -quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles n)) observer /
              lambda n ≤
          direction n mover observer := by
      intro n
      have htargetNonneg := quittingTerminalDeviationDebt_nonneg reward
        (quittingStoppingLawResetProfile reward (profiles n) mover.1
          (bestResponse n mover) (lambda n) (hlambdaPos n).le (hlambdaLe n))
        observer
      change 0 ≤ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingStoppingLawResetProfile reward (profiles n) mover.1
            (bestResponse n mover) (lambda n) (hlambdaPos n).le
              (hlambdaLe n))) observer at htargetNonneg
      dsimp only [direction, quittingStoppingLawNormalizedDebtDirection,
        quittingTerminalSemanticDebtChange]
      exact (div_le_div_iff_of_pos_right (hlambdaPos n)).2 (by linarith)
    have hleft : Tendsto (fun rank ↦
        -quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles (subseq rank))) observer /
          lambda (subseq rank)) atTop (nhds 0) := by
      simpa [Function.comp_def, neg_div] using
        (hinactiveRate observer hzero).neg.comp hsubseq.tendsto_atTop
    exact le_of_tendsto_of_tendsto hleft (htangentCoordinate mover observer)
      (Eventually.of_forall fun rank ↦ hpointwise (subseq rank))
  have hsumDirection : ∀ n mover,
      (∑ observer, direction n mover observer) =
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingStoppingLawResetProfile reward (profiles n) mover.1
                (bestResponse n mover) (lambda n) (hlambdaPos n).le
                  (hlambdaLe n))) -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward (profiles n))) / lambda n := by
    intro n mover
    dsimp only [direction, quittingStoppingLawNormalizedDebtDirection]
    rw [← Finset.sum_div]
    unfold quittingTerminalSemanticDebtSum quittingTerminalSemanticDebtChange
    rw [Finset.sum_sub_distrib]
  have hsumLimit : ∀ mover,
      Tendsto (fun rank ↦ ∑ observer,
          direction (subseq rank) mover observer)
        atTop (nhds (∑ observer, tangent mover observer)) := by
    intro mover
    exact tendsto_finsetSum Finset.univ fun observer _ ↦
      htangentCoordinate mover observer
  have hsumNonneg : ∀ mover, 0 ≤ ∑ observer, tangent mover observer := by
    intro mover
    have hpointwise : ∀ n,
        -(epsilon n / lambda n) ≤ ∑ observer, direction n mover observer := by
      intro n
      rw [hsumDirection]
      have htarget := quittingTerminalSemanticPair_mem_carrier reward
        (quittingStoppingLawResetProfile reward (profiles n) mover.1
          (bestResponse n mover) (lambda n) (hlambdaPos n).le (hlambdaLe n))
      have hnearTarget := hnear n _ htarget
      calc
        -(epsilon n / lambda n) = (-epsilon n) / lambda n := by ring
        _ ≤ (quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingStoppingLawResetProfile reward (profiles n) mover.1
                  (bestResponse n mover) (lambda n) (hlambdaPos n).le
                    (hlambdaLe n))) -
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward (profiles n))) / lambda n :=
          (div_le_div_iff_of_pos_right (hlambdaPos n)).2 (by linarith)
    have hleft : Tendsto (fun rank ↦ -(epsilon (subseq rank) /
        lambda (subseq rank))) atTop (nhds 0) := by
      simpa [Function.comp_def] using
        herrorRate.neg.comp hsubseq.tendsto_atTop
    exact le_of_tendsto_of_tendsto hleft (hsumLimit mover)
      (Eventually.of_forall fun rank ↦ hpointwise (subseq rank))
  have hslopeAlternative :
      (∃ mover, 0 < ∑ observer, tangent mover observer) ∨
        ∀ mover, ∑ observer, tangent mover observer = 0 := by
    by_cases hpos : ∃ mover, 0 < ∑ observer, tangent mover observer
    · exact Or.inl hpos
    · right
      intro mover
      exact le_antisymm (le_of_not_gt (fun hgt ↦ hpos ⟨mover, hgt⟩))
        (hsumNonneg mover)
  refine ⟨fun mover n ↦ bestResponse n mover, subseq, tangent,
    hsubseq, hlambdaZero.comp hsubseq.tendsto_atTop, ?_, ?_, ?_, hdiagonal,
    hinactiveNonneg, hsumNonneg, hslopeAlternative⟩
  · intro mover observer
    exact htangentCoordinate mover observer
  · intro mover rank
    exact hendpointDebtLeTolerance (subseq rank) mover
  · intro mover
    exact (hendpointDebtZero mover).comp hsubseq.tendsto_atTop

end GameTheory
