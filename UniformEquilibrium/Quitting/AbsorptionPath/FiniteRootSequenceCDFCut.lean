/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.DiscreteRootSequencePath

/-!
# Finite root-sequence CDF cuts

A finite absorbing root sequence is a step CDF in its absorption clock.  If
the CDF at `time` still lies below a later clock `upper`, its right staircase
inverse selects a literal source prefix.  The prefix clock and every coalition
coordinate equal the finite path value at `time`, while the next clock is
bounded by the finite path total at `upper`.

This module is finite and source-local.  It has no compactness, Nash, payoff,
or absorption-path perfection hypothesis.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A finite right-CDF cut.  The cut is the source prefix selected by the CDF
at `time`; if that CDF lies below `upper`, its successor clock is bounded by
the CDF at `upper`. -/
structure QuittingFiniteCDFCut
    {roots : ℕ → ι → PMF Bool}
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    (time upper : ℝ) where
  cut : ℕ
  cut_le_cutoff : cut ≤ certificate.cutoff
  clock_eq : quittingRootSequenceClock roots cut =
    pathTotal certificate.cadlagPath time
  cumulative_eq : ∀ coalition,
    quittingRootSequenceCumulativeCoalitionMass roots cut coalition =
      certificate.value time coalition
  clock_succ_le_upperCDF : quittingRootSequenceClock roots (cut + 1) ≤
    pathTotal certificate.cadlagPath upper

/-- Finite staircase inversion at a point whose source CDF still lies below
a chosen upper clock. -/
theorem nonempty_quittingFiniteCDFCut
    {roots : ℕ → ι → PMF Bool}
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {time upper : ℝ} (htime : 0 ≤ time)
    (htimeUpper : time < upper)
    (hCDF : pathTotal certificate.cadlagPath time < upper)
    (hupper : upper < 1) :
    Nonempty (QuittingFiniteCDFCut certificate time upper) := by
  classical
  have hlast :
      quittingRootSequenceClock roots (certificate.cutoff + 1) = 1 := by
    simp [quittingRootSequenceClock, certificate.survival_zero]
  have hexists : ∃ stage,
      time < quittingRootSequenceClock roots (stage + 1) := by
    refine ⟨certificate.cutoff, ?_⟩
    have htime_lt : time < 1 := htimeUpper.trans hupper
    simpa [hlast] using htime_lt
  let stage := Nat.find hexists
  have hstage : stage ≤ certificate.cutoff := by
    exact Nat.find_min' hexists (by
      have htime_lt : time < 1 := htimeUpper.trans hupper
      simpa [hlast] using htime_lt)
  have hnext : time < quittingRootSequenceClock roots (stage + 1) :=
    Nat.find_spec hexists
  have hminimal : ∀ earlier < stage,
      quittingRootSequenceClock roots (earlier + 1) ≤ time := by
    intro earlier hearlier
    exact not_lt.mp (Nat.find_min hexists hearlier)
  have hvalue (coalition : {S : Finset ι // S.Nonempty}) :
      certificate.value time coalition =
        quittingRootSequenceCumulativeCoalitionMass
          roots (stage + 1) coalition := by
    unfold QuittingFiniteRootSequenceAbsorption.value
      quittingRootSequenceCumulativeCoalitionMass
    let mass := fun earlier =>
      quittingRootSequenceStageCoalitionMass roots earlier coalition
    have hsubset : Finset.range (stage + 1) ⊆
        Finset.range (certificate.cutoff + 1) :=
      Finset.range_mono (Nat.add_le_add_right hstage 1)
    calc
      (∑ earlier ∈ Finset.range (certificate.cutoff + 1),
          if quittingRootSequenceClock roots earlier ≤ time then
            mass earlier else 0) =
          ∑ earlier ∈ Finset.range (stage + 1),
            if quittingRootSequenceClock roots earlier ≤ time then
              mass earlier else 0 := by
        symm
        apply Finset.sum_subset hsubset
        intro earlier _ hnotSmall
        have hearler : stage + 1 ≤ earlier := by
          simpa only [Finset.mem_range, not_lt] using hnotSmall
        have hclock : quittingRootSequenceClock roots (stage + 1) ≤
            quittingRootSequenceClock roots earlier :=
          monotone_quittingRootSequenceClock roots hearler
        rw [if_neg (not_le_of_gt (hnext.trans_le hclock))]
      _ = ∑ earlier ∈ Finset.range (stage + 1), mass earlier := by
        apply Finset.sum_congr rfl
        intro earlier hearlier
        rw [if_pos]
        rcases Nat.eq_zero_or_pos earlier with rfl | hearler0
        · exact (quittingRootSequenceClock_zero roots).le.trans htime
        · obtain ⟨previous, rfl⟩ :=
            Nat.exists_eq_succ_of_ne_zero hearler0.ne'
          exact hminimal previous (by simpa using hearlier)
      _ = ∑ earlier ∈ Finset.range (stage + 1),
          quittingRootSequenceStageCoalitionMass
            roots earlier coalition := rfl
  have htotal : pathTotal certificate.cadlagPath time =
      quittingRootSequenceClock roots (stage + 1) := by
    unfold pathTotal
    change (∑ coalition, certificate.value time coalition) = _
    simp_rw [hvalue]
    exact sum_quittingRootSequenceCumulativeCoalitionMass roots (stage + 1)
  have hstage_lt : stage < certificate.cutoff := by
    apply lt_of_le_of_ne hstage
    intro heq
    have hclock_one :
        quittingRootSequenceClock roots (stage + 1) = 1 := by
      rw [heq]
      exact hlast
    rw [htotal, hclock_one] at hCDF
    exact (not_lt_of_ge hupper.le) hCDF
  have hcut_le : stage + 1 ≤ certificate.cutoff := by omega
  have hprefix_le (coalition : {S : Finset ι // S.Nonempty}) :
      quittingRootSequenceCumulativeCoalitionMass
          roots (stage + 2) coalition ≤
        certificate.value upper coalition := by
    unfold quittingRootSequenceCumulativeCoalitionMass
      QuittingFiniteRootSequenceAbsorption.value
    let mass := fun earlier =>
      quittingRootSequenceStageCoalitionMass roots earlier coalition
    have hsubset : Finset.range (stage + 2) ⊆
        Finset.range (certificate.cutoff + 1) := by
      apply Finset.range_mono
      omega
    calc
      (∑ earlier ∈ Finset.range (stage + 2), mass earlier) =
          ∑ earlier ∈ Finset.range (stage + 2),
            if quittingRootSequenceClock roots earlier ≤ upper then
              mass earlier else 0 := by
        apply Finset.sum_congr rfl
        intro earlier hearlier
        rw [if_pos]
        have hearler : earlier ≤ stage + 1 := by
          have : earlier < stage + 2 := Finset.mem_range.mp hearlier
          omega
        have hclock := monotone_quittingRootSequenceClock roots hearler
        rw [← htotal] at hclock
        exact hclock.trans hCDF.le
      _ ≤ ∑ earlier ∈ Finset.range (certificate.cutoff + 1),
          if quittingRootSequenceClock roots earlier ≤ upper then
            mass earlier else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro earlier _ _
        split
        · exact quittingRootSequenceStageCoalitionMass_nonneg
            roots earlier coalition
        · exact le_rfl
  refine ⟨{
    cut := stage + 1
    cut_le_cutoff := hcut_le
    clock_eq := htotal.symm
    cumulative_eq := fun coalition => (hvalue coalition).symm
    clock_succ_le_upperCDF := ?_
  }⟩
  calc
    quittingRootSequenceClock roots (stage + 1 + 1) =
        ∑ coalition,
          quittingRootSequenceCumulativeCoalitionMass
            roots (stage + 2) coalition := by
      rw [sum_quittingRootSequenceCumulativeCoalitionMass]
    _ ≤ ∑ coalition, certificate.value upper coalition := by
      exact Finset.sum_le_sum fun coalition _ => hprefix_le coalition
    _ = pathTotal certificate.cadlagPath upper := by rfl

end GameTheory.QuittingAbsorptionPath
