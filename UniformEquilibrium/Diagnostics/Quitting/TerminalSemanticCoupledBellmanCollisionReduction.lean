/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.FiniteLabelSubsequence
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect

/-!
# Coupled Bellman--collision reduction

Consider actual rows on which one fixed two-player terminal coalition has a
uniformly positive probability.  The collision budget says that the positive
minimum semantic debt is paid either by shifted-tail excess or by the total
coordinate Nash defect of the same row.

This module removes the two collision players from that total defect.  If
their combined defect tends to zero and the shifted tails return to the
minimum-debt fiber, one fixed third player carries a quantitative coordinate
defect along a strict subsequence.  Without the return assumption, the exact
conclusion is the alternative between nonvanishing tail excess and that fixed
third-player defect.

The theorem does not derive shifted-tail return.  Without that hypothesis its
first disjunct records that the tail excess fails to converge to zero.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- On a persistent exact pair-collision sequence which returns to the
minimum-debt fiber, one fixed player outside the collision pair carries a
uniformly positive coordinate Nash defect along a strict subsequence.

The quantitative floor is `lower * minimumDebt / 2`, divided once more by
twice the number of players outside the pair by finite-label extraction. -/
theorem exists_fixed_third_coordinateNashDefect_of_pairCollision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (stages : ℕ → ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (first second : ι) (hne : first ≠ second) (lower : ℝ)
    (hterminal : terminal.val = {first, second})
    (hlower : 0 < lower)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hmass : ∀ n, lower ≤
      quittingStageCoalitionMass reward (profiles n) (stages n) terminal)
    (htail : Tendsto (fun n =>
      quittingSpineDebtExcess reward (profiles n)
        (quittingTerminalSemanticDebtSum minimum) (stages n + 1))
      atTop (𝓝 0))
    (hpairDefect : Tendsto (fun n =>
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (profiles n) (stages n + 1))
      let root := quittingProfileLiveRoot reward (profiles n) (stages n)
      quittingRootCoordinateNashDefect reward tail.1 root first +
        quittingRootCoordinateNashDefect reward tail.1 root second)
      atTop (𝓝 0)) :
    ∃ (third : ι) (subseq : ℕ → ℕ),
      third ≠ first ∧ third ≠ second ∧ StrictMono subseq ∧
      ∀ n,
        lower * quittingTerminalSemanticDebtSum minimum /
              (4 * (((Finset.univ.erase first).erase second).card : ℝ)) ≤
          let tail := quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (profiles (subseq n)) (stages (subseq n) + 1))
          quittingRootCoordinateNashDefect reward tail.1
            (quittingProfileLiveRoot reward
              (profiles (subseq n)) (stages (subseq n))) third := by
  let labels : Finset ι := (Finset.univ.erase first).erase second
  let tail : ℕ → QuittingTerminalSemanticPair ι := fun n =>
    quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward (profiles n) (stages n + 1))
  let defect : ℕ → ι → ℝ := fun n who =>
    quittingRootCoordinateNashDefect reward (tail n).1
      (quittingProfileLiveRoot reward (profiles n) (stages n)) who
  let excess : ℕ → ℝ := fun n =>
    quittingSpineDebtExcess reward (profiles n)
      (quittingTerminalSemanticDebtSum minimum) (stages n + 1)
  let error : ℕ → ℝ := fun n => excess n + (defect n first + defect n second)
  let floor := lower * quittingTerminalSemanticDebtSum minimum / 2
  have hcollision : 1 < terminal.val.card := by
    rw [hterminal]
    simp [hne]
  have herror : Tendsto error atTop (𝓝 0) := by
    have htail' : Tendsto excess atTop (𝓝 0) := by
      simpa only [excess] using htail
    have hpair' : Tendsto (fun n => defect n first + defect n second)
        atTop (𝓝 0) := by
      simpa only [defect, tail] using hpairDefect
    simpa only [error, zero_add] using htail'.add hpair'
  have hfloor : 0 < floor := by
    dsimp only [floor]
    positivity
  have hsplit : ∀ n,
      quittingSpineTotalNashDefect reward (profiles n) (stages n) =
        (∑ who ∈ labels, defect n who) +
          (defect n first + defect n second) := by
    intro n
    have hsecondMem : second ∈ Finset.univ.erase first :=
      Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ second⟩
    rw [show quittingSpineTotalNashDefect reward (profiles n) (stages n) =
        ∑ who, defect n who by
      simp only [quittingSpineTotalNashDefect,
        quittingRootTotalNashDefect, defect, tail]]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ first)]
    rw [← Finset.sum_erase_add _ _ hsecondMem]
    dsimp only [labels]
    ring
  have hlower : ∀ n, floor - error n ≤ ∑ who ∈ labels, defect n who := by
    intro n
    have hbudget := tailExcess_or_totalNashDefect_of_persistent_collision
      reward minimum (profiles n) (stages n) terminal lower
        hminimumCarrier hminimum hcollision (hmass n)
    have hexcessNonneg : 0 ≤ excess n := by
      dsimp only [excess, quittingSpineDebtExcess]
      exact sub_nonneg.mpr
        (hminimum _ (quittingTerminalSemanticPair_mem_carrier reward _))
    rcases hbudget with htailLarge | hdefectLarge
    · have htailLarge' : floor ≤ excess n := by
        simpa only [floor, excess] using htailLarge
      dsimp only [floor, error]
      have hfirstNonneg : 0 ≤ defect n first :=
        quittingRootCoordinateNashDefect_nonneg reward _ _ first
      have hsecondNonneg : 0 ≤ defect n second :=
        quittingRootCoordinateNashDefect_nonneg reward _ _ second
      have hsumNonneg : 0 ≤ ∑ who ∈ labels, defect n who :=
        Finset.sum_nonneg fun who _ =>
          quittingRootCoordinateNashDefect_nonneg reward _ _ who
      linarith
    · rw [hsplit n] at hdefectLarge
      dsimp only [floor, error, excess]
      linarith
  obtain ⟨third, hthirdMem, subseq, hsubseq, hthird⟩ :=
    Math.exists_fixed_mem_subsequence_of_sum_lower_and_error_tendsto_zero
      labels defect error floor hfloor herror hlower
  have hthirdFirst : third ≠ first := by
    exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hthirdMem)
  have hthirdSecond : third ≠ second := Finset.ne_of_mem_erase hthirdMem
  refine ⟨third, subseq, hthirdFirst, hthirdSecond, hsubseq, ?_⟩
  intro n
  have hbound := hthird n
  dsimp only [floor, labels] at hbound
  simpa only [defect, tail] using (show
    lower * quittingTerminalSemanticDebtSum minimum /
          (4 * (((Finset.univ.erase first).erase second).card : ℝ)) ≤
        defect (subseq n) third by
      calc
        lower * quittingTerminalSemanticDebtSum minimum /
              (4 * (((Finset.univ.erase first).erase second).card : ℝ)) =
            floor /
              (2 * (((Finset.univ.erase first).erase second).card : ℝ)) := by
          dsimp only [floor]
          ring
        _ ≤ _ := hbound)

/-- Persistent exact pair collision has an exact global alternative.  If the
two collision players' combined defects vanish, then either shifted-tail
excess fails to return to zero or one fixed third player carries the explicit
subsequence defect floor from
`exists_fixed_third_coordinateNashDefect_of_pairCollision`. -/
theorem tailExcess_not_tendsto_zero_or_exists_fixed_third_coordinateNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (stages : ℕ → ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (first second : ι) (hne : first ≠ second) (lower : ℝ)
    (hterminal : terminal.val = {first, second})
    (hlower : 0 < lower)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hmass : ∀ n, lower ≤
      quittingStageCoalitionMass reward (profiles n) (stages n) terminal)
    (hpairDefect : Tendsto (fun n =>
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (profiles n) (stages n + 1))
      let root := quittingProfileLiveRoot reward (profiles n) (stages n)
      quittingRootCoordinateNashDefect reward tail.1 root first +
        quittingRootCoordinateNashDefect reward tail.1 root second)
      atTop (𝓝 0)) :
    (¬ Tendsto (fun n =>
      quittingSpineDebtExcess reward (profiles n)
        (quittingTerminalSemanticDebtSum minimum) (stages n + 1))
      atTop (𝓝 0)) ∨
    ∃ (third : ι) (subseq : ℕ → ℕ),
      third ≠ first ∧ third ≠ second ∧ StrictMono subseq ∧
      ∀ n,
        lower * quittingTerminalSemanticDebtSum minimum /
              (4 * (((Finset.univ.erase first).erase second).card : ℝ)) ≤
          let tail := quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (profiles (subseq n)) (stages (subseq n) + 1))
          quittingRootCoordinateNashDefect reward tail.1
            (quittingProfileLiveRoot reward
              (profiles (subseq n)) (stages (subseq n))) third := by
  by_cases htail : Tendsto (fun n =>
      quittingSpineDebtExcess reward (profiles n)
        (quittingTerminalSemanticDebtSum minimum) (stages n + 1))
      atTop (𝓝 0)
  · right
    exact exists_fixed_third_coordinateNashDefect_of_pairCollision
      reward minimum profiles stages terminal first second hne lower
        hterminal hlower hminimumCarrier hminimum hminimumDebt hmass htail
          hpairDefect
  · exact Or.inl htail

/-- **Legal-deviation form of the coupled collision reduction.**

The pair collision itself lower-bounds the probability of reaching every
selected row.  Hence the fixed third player's coordinate defect from the
preceding theorem is realized by one legal behavioral deviation on the same
profile and row, with the explicit gain floor

`lower^2 * minimumDebt / (4 * card(outside pair))`.

The alternative is failure of the shifted tails to return to the minimum-debt
fiber. -/
theorem tailExcess_not_tendsto_zero_or_exists_fixed_third_legalGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (stages : ℕ → ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (first second : ι) (hne : first ≠ second) (lower : ℝ)
    (hterminal : terminal.val = {first, second})
    (hlower : 0 < lower)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hmass : ∀ n, lower ≤
      quittingStageCoalitionMass reward (profiles n) (stages n) terminal)
    (hpairDefect : Tendsto (fun n =>
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (profiles n) (stages n + 1))
      let root := quittingProfileLiveRoot reward (profiles n) (stages n)
      quittingRootCoordinateNashDefect reward tail.1 root first +
        quittingRootCoordinateNashDefect reward tail.1 root second)
      atTop (𝓝 0)) :
    (¬ Tendsto (fun n =>
      quittingSpineDebtExcess reward (profiles n)
        (quittingTerminalSemanticDebtSum minimum) (stages n + 1))
      atTop (𝓝 0)) ∨
    ∃ (third : ι) (subseq : ℕ → ℕ),
      third ≠ first ∧ third ≠ second ∧ StrictMono subseq ∧
      ∀ n,
        lower ^ 2 * quittingTerminalSemanticDebtSum minimum /
              (4 * (((Finset.univ.erase first).erase second).card : ℝ)) ≤
          let profile := profiles (subseq n)
          let stage := stages (subseq n)
          let tail := quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (stage + 1))
          let root := quittingProfileLiveRoot reward profile stage
          let action := quittingRootBestEndpointAction reward tail.1 root third
          quittingTerminalPayoff reward
                (Function.update profile third
                  (quittingStagePureEndpointBehaviorDeviation
                    reward profile third stage action)) third -
            quittingTerminalPayoff reward profile third := by
  rcases tailExcess_not_tendsto_zero_or_exists_fixed_third_coordinateNashDefect
      reward minimum profiles stages terminal first second hne lower
        hterminal hlower hminimumCarrier hminimum hminimumDebt hmass
          hpairDefect with htail | hthird
  · exact Or.inl htail
  · right
    obtain ⟨third, subseq, hthirdFirst, hthirdSecond, hsubseq, hdefect⟩ := hthird
    refine ⟨third, subseq, hthirdFirst, hthirdSecond, hsubseq, ?_⟩
    intro n
    let profile := profiles (subseq n)
    let stage := stages (subseq n)
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let defect := quittingRootCoordinateNashDefect reward tail.1 root third
    let defectFloor := lower * quittingTerminalSemanticDebtSum minimum /
      (4 * (((Finset.univ.erase first).erase second).card : ℝ))
    have hdefect' : defectFloor ≤ defect := by
      simpa only [defectFloor, defect, tail, root, profile, stage] using hdefect n
    have hdefectNonneg : 0 ≤ defect :=
      quittingRootCoordinateNashDefect_nonneg reward _ _ third
    have hlive : lower ≤ quittingLiveMass reward profile stage :=
      (hmass (subseq n)).trans
        (quittingStageCoalitionMass_le_liveMass
          reward profile stage terminal)
    have hscaled : lower * defectFloor ≤
        quittingLiveMass reward profile stage * defect :=
      (mul_le_mul_of_nonneg_left hdefect' hlower.le).trans
        (mul_le_mul_of_nonneg_right hlive hdefectNonneg)
    have hgain :=
      quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
        reward profile third stage
    dsimp only at hgain
    dsimp only [profile, stage, tail, root, defect] at hgain
    rw [hgain]
    dsimp only [defectFloor] at hscaled
    calc
      lower ^ 2 * quittingTerminalSemanticDebtSum minimum /
            (4 * (((Finset.univ.erase first).erase second).card : ℝ)) =
          lower *
            (lower * quittingTerminalSemanticDebtSum minimum /
              (4 * (((Finset.univ.erase first).erase second).card : ℝ))) := by
        ring
      _ ≤ _ := hscaled

end GameTheory
