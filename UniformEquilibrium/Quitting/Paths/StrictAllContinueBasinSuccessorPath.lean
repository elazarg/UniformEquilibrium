/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.StrictAllContinueBasinLinearAbsorptionDefect

/-!
# First-exit bootstrap for a strict all-Continue basin

This module iterates the linear absorption-defect estimate along an exact
successor path.  The path is indexed outward from its terminal continuation:
`value 0` is terminal, and `value (time + 1)` is the predecessor obtained from
the root against `value time`.  A terminal point within half the tube radius
of the compact basin and a sufficiently small aggregate error budget keep the
whole path in the tube.

The conclusion controls aggregate absorption and every coordinate of the path
diameter.  It does not produce a path, a nonlocal incoming edge, or a return.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A successor-linked path ending near a thick compact basin cannot make a
nonlocal excursion under a small aggregate root-error budget.  The indexing
is reversed relative to chronological time, so each root is legally tested
against its already-admitted continuation. -/
theorem successorPath_mem_and_absorptionSum_le_of_linearDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (K N : Set (Payoff ι)) (value : ℕ → Payoff ι)
    (root : ℕ → ι → PMF Bool) (error : ℕ → ℝ) (length : ℕ)
    {C c rho : ℝ} (hC : 0 < C) (hc : 0 < c) (hrho : 0 < rho)
    (hreward : ∀ S player, |reward S player| ≤ C)
    (htail : ∀ tail ∈ N, ∀ player, |tail player| ≤ C)
    (hlinear : ∀ tail ∈ N, ∀ stageRoot : ι → PMF Bool,
      c * quittingRootAbsorptionMass stageRoot ≤
        quittingRootTotalNashDefect reward tail stageRoot)
    (hKnonempty : K.Nonempty)
    (hthick : Metric.thickening rho K ⊆ N)
    (hterminal : Metric.infDist (value 0) K < rho / 2)
    (herrorNonneg : ∀ time < length, 0 ≤ error time)
    (hnash : ∀ time < length,
      IsεQuittingRootNash reward (value time) (error time) (root time))
    (hsuccessor : ∀ time < length,
      value (time + 1) =
        quittingRootSuccessorPayoff reward (value time) (root time))
    (hbudget : (2 * C * Fintype.card ι / c) *
      (∑ time ∈ Finset.range length, error time) < rho / 2) :
    (∀ time ≤ length, value time ∈ N) ∧
      (∑ time ∈ Finset.range length,
          quittingRootAbsorptionMass (root time)) ≤
        Fintype.card ι / c *
          ∑ time ∈ Finset.range length, error time ∧
      ∀ time ≤ length, ∀ player,
        |value time player - value 0 player| ≤
          (2 * C * Fintype.card ι / c) *
            ∑ stage ∈ Finset.range length, error stage := by
  have hterminalThickening :
      value 0 ∈ Metric.thickening (rho / 2) K :=
    (Metric.mem_thickening_iff_infDist_lt hKnonempty).2 hterminal
  obtain ⟨anchor, hanchorK, hterminalDist⟩ :=
    Metric.mem_thickening_iff.mp hterminalThickening
  have hterminalClose : ∀ player,
      |value 0 player - anchor player| < rho / 2 := by
    have hcoordinate := (dist_pi_lt_iff (by linarith [hrho])).mp hterminalDist
    intro player
    simpa [Real.dist_eq] using hcoordinate player
  let coefficient := 2 * C * Fintype.card ι / c
  have hcoefficientPos : 0 < coefficient := by
    dsimp only [coefficient]
    positivity
  have hpartialLe : ∀ time ≤ length,
      (∑ stage ∈ Finset.range time, error stage) ≤
        ∑ stage ∈ Finset.range length, error stage := by
    intro time htime
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono htime)
    intro stage hstage _hstageNot
    exact herrorNonneg stage (Finset.mem_range.mp hstage)
  have hinvariant : ∀ time ≤ length,
      value time ∈ N ∧
        ∀ player, |value time player - value 0 player| ≤
          coefficient * ∑ stage ∈ Finset.range time, error stage := by
    intro time htime
    induction time with
    | zero =>
        have hzeroMem : value 0 ∈ N := by
          apply hthick
          apply Metric.mem_thickening_iff.mpr
          exact ⟨anchor, hanchorK, hterminalDist.trans_le (by linarith [hrho])⟩
        refine ⟨hzeroMem, ?_⟩
        intro player
        simp
    | succ time ih =>
        have htimeLt : time < length := Nat.lt_of_succ_le htime
        have htimeLe : time ≤ length := Nat.le_of_lt htimeLt
        obtain ⟨htimeMem, htimeDistance⟩ := ih htimeLe
        have habsorption :=
          quittingRootAbsorptionMass_le_card_div_mul_of_linearDefect
            reward (value time) (root time) hc (hnash time htimeLt)
              (hlinear (value time) htimeMem (root time))
        have hedge : ∀ player,
            |value (time + 1) player - value time player| ≤
              coefficient * error time := by
          intro player
          rw [hsuccessor time htimeLt]
          have hmovement :=
            abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
              reward (value time) (root time) player C hreward
                (htail (value time) htimeMem player)
          calc
            |quittingRootSuccessorPayoff reward (value time) (root time) player -
                value time player| ≤
              2 * C * quittingRootAbsorptionMass (root time) := hmovement
            _ ≤ 2 * C * (Fintype.card ι / c * error time) :=
              mul_le_mul_of_nonneg_left habsorption (by positivity)
            _ = coefficient * error time := by
              dsimp only [coefficient]
              ring
        have hnextDistance : ∀ player,
            |value (time + 1) player - value 0 player| ≤
              coefficient *
                ∑ stage ∈ Finset.range (time + 1), error stage := by
          intro player
          calc
            |value (time + 1) player - value 0 player| =
                |(value (time + 1) player - value time player) +
                  (value time player - value 0 player)| := by ring_nf
            _ ≤ |value (time + 1) player - value time player| +
                |value time player - value 0 player| := abs_add_le _ _
            _ ≤ coefficient * error time + coefficient *
                ∑ stage ∈ Finset.range time, error stage :=
              add_le_add (hedge player) (htimeDistance player)
            _ = coefficient *
                ∑ stage ∈ Finset.range (time + 1), error stage := by
              rw [Finset.sum_range_succ]
              ring
        have hnextTotal : ∀ player,
            |value (time + 1) player - value 0 player| < rho / 2 := by
          intro player
          exact (hnextDistance player).trans_lt
            ((mul_le_mul_of_nonneg_left (hpartialLe (time + 1) htime)
              hcoefficientPos.le).trans_lt (by
                simpa only [coefficient] using hbudget))
        have hnextMem : value (time + 1) ∈ N := by
          apply hthick
          apply Metric.mem_thickening_iff.mpr
          refine ⟨anchor, hanchorK, (dist_pi_lt_iff hrho).2 ?_⟩
          intro player
          simpa [Real.dist_eq] using (show
            |value (time + 1) player - anchor player| < rho by
              calc
                |value (time + 1) player - anchor player| =
                    |(value (time + 1) player - value 0 player) +
                      (value 0 player - anchor player)| := by ring_nf
                _ ≤ |value (time + 1) player - value 0 player| +
                    |value 0 player - anchor player| := abs_add_le _ _
                _ < rho / 2 + rho / 2 :=
                  add_lt_add (hnextTotal player) (hterminalClose player)
                _ = rho := by ring)
        exact ⟨hnextMem, hnextDistance⟩
  have hallMem : ∀ time ≤ length, value time ∈ N := fun time htime =>
    (hinvariant time htime).1
  have habsorptionSum :
      (∑ time ∈ Finset.range length,
          quittingRootAbsorptionMass (root time)) ≤
        Fintype.card ι / c *
          ∑ time ∈ Finset.range length, error time := by
    calc
      (∑ time ∈ Finset.range length,
          quittingRootAbsorptionMass (root time)) ≤
          ∑ time ∈ Finset.range length,
            Fintype.card ι / c * error time := by
        apply Finset.sum_le_sum
        intro time htime
        exact quittingRootAbsorptionMass_le_card_div_mul_of_linearDefect
          reward (value time) (root time) hc
            (hnash time (Finset.mem_range.mp htime))
            (hlinear (value time)
              (hallMem time (Nat.le_of_lt (Finset.mem_range.mp htime)))
              (root time))
      _ = Fintype.card ι / c *
          ∑ time ∈ Finset.range length, error time := by
        rw [Finset.mul_sum]
  refine ⟨hallMem, habsorptionSum, ?_⟩
  intro time htime player
  exact (hinvariant time htime).2 player |>.trans
    (mul_le_mul_of_nonneg_left (hpartialLe time htime)
      hcoefficientPos.le)

omit [DecidableEq ι] [Nonempty ι] in
/-- The aggregate form of the vanishing-absorption consequence allows path
lengths to vary.  The required hypothesis is convergence of the aggregate
declared error, not convergence of the largest row error. -/
theorem quittingRootAbsorptionSum_tendsto_zero_of_linearBound
    {α : Type} {l : Filter α}
    (root : α → ℕ → ι → PMF Bool) (length : α → ℕ)
    (aggregateError : α → ℝ) {c : ℝ}
    (hbound : ∀ index,
      (∑ time ∈ Finset.range (length index),
          quittingRootAbsorptionMass (root index time)) ≤
        Fintype.card ι / c * aggregateError index)
    (herror : Filter.Tendsto aggregateError l (nhds 0)) :
    Filter.Tendsto (fun index =>
      ∑ time ∈ Finset.range (length index),
        quittingRootAbsorptionMass (root index time)) l (nhds 0) := by
  apply squeeze_zero
  · intro index
    exact Finset.sum_nonneg fun time _ =>
      quittingRootAbsorptionMass_nonneg (root index time)
  · exact hbound
  · simpa only [mul_zero] using herror.const_mul (Fintype.card ι / c)

/-- Contrapositive toll form: if such a path reaches a node outside the tube,
its aggregate declared root error is bounded below by a fixed positive amount. -/
theorem sum_error_ge_of_successorPath_exists_not_mem_linearBasin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (K N : Set (Payoff ι)) (value : ℕ → Payoff ι)
    (root : ℕ → ι → PMF Bool) (error : ℕ → ℝ) (length : ℕ)
    {C c rho : ℝ} (hC : 0 < C) (hc : 0 < c) (hrho : 0 < rho)
    (hreward : ∀ S player, |reward S player| ≤ C)
    (htail : ∀ tail ∈ N, ∀ player, |tail player| ≤ C)
    (hlinear : ∀ tail ∈ N, ∀ stageRoot : ι → PMF Bool,
      c * quittingRootAbsorptionMass stageRoot ≤
        quittingRootTotalNashDefect reward tail stageRoot)
    (hKnonempty : K.Nonempty)
    (hthick : Metric.thickening rho K ⊆ N)
    (hterminal : Metric.infDist (value 0) K < rho / 2)
    (herrorNonneg : ∀ time < length, 0 ≤ error time)
    (hnash : ∀ time < length,
      IsεQuittingRootNash reward (value time) (error time) (root time))
    (hsuccessor : ∀ time < length,
      value (time + 1) =
        quittingRootSuccessorPayoff reward (value time) (root time))
    (houtside : ∃ time ≤ length, value time ∉ N) :
    c * rho / (4 * C * Fintype.card ι) ≤
      ∑ time ∈ Finset.range length, error time := by
  apply le_of_not_gt
  intro hsmall
  have hcoefficientPos : 0 < 2 * C * Fintype.card ι / c := by positivity
  have hthresholdIdentity :
      (2 * C * Fintype.card ι / c) *
          (c * rho / (4 * C * Fintype.card ι)) = rho / 2 := by
    have hcard : (Fintype.card ι : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hbudget : (2 * C * Fintype.card ι / c) *
      (∑ time ∈ Finset.range length, error time) < rho / 2 := by
    calc
      (2 * C * Fintype.card ι / c) *
          (∑ time ∈ Finset.range length, error time) <
        (2 * C * Fintype.card ι / c) *
          (c * rho / (4 * C * Fintype.card ι)) :=
        mul_lt_mul_of_pos_left hsmall hcoefficientPos
      _ = rho / 2 := hthresholdIdentity
  have hallMem :=
    (successorPath_mem_and_absorptionSum_le_of_linearDefect
      reward K N value root error length hC hc hrho hreward htail hlinear
        hKnonempty hthick hterminal herrorNonneg hnash hsuccessor hbudget).1
  obtain ⟨time, htime, htimeOutside⟩ := houtside
  exact htimeOutside (hallMem time htime)

end GameTheory
