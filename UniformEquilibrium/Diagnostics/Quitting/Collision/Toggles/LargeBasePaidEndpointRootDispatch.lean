/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargeBasePaidEndpointAtomDispatch
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseProductRescaling
import UniformEquilibrium.Quitting.Root.EndpointOpponentStability

/-!
# Exact-root charge at a stationary immediate-Quit endpoint

At a stationary source, a fixed immediate-Quit gain makes the source
Quit-minus-Continue endpoint difference positive.  An exact root at the same
tail either absorbs macroscopically already or must reverse that endpoint
difference by moving a macroscopic total amount in the opponent Bernoulli
marginals.  If the source opponent hazard is small, finite averaging forces
one opponent marginal, and hence exact-root absorption, to be macroscopic.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem card_erase_eq_card_sub_one
    (who : ι) : (Finset.univ.erase who).card = Fintype.card ι - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ who), Finset.card_univ]

/-- Source opponent absorption or exact-root absorption is at least the
packet scale `gap / (8 * bound * (card ι - 1))`. -/
theorem stationaryImmediateQuitGap_source_or_exactRoot_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sourceRoot exactRoot : ι → PMF Bool) (who : ι)
    (gap bound : ℝ) (hcard : 1 < Fintype.card ι)
    (hgap : 0 < gap) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (himmediate : gap ≤
      quittingPureTimeDeviationPayoff reward
          (quittingStationaryProfile reward sourceRoot) who (some 0) -
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward sourceRoot) who)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingTerminalPayoff reward
        (quittingStationaryProfile reward sourceRoot)) 0 exactRoot) :
    let scale := gap /
      (8 * bound * ((Fintype.card ι - 1 : ℕ) : ℝ))
    scale ≤ quittingRootOpponentAbsorptionMass sourceRoot who ∨
      scale ≤ quittingRootAbsorptionMass exactRoot := by
  let tail := quittingTerminalPayoff reward
    (quittingStationaryProfile reward sourceRoot)
  let opponentCount : ℝ := (Fintype.card ι - 1 : ℕ)
  let scale := gap / (8 * bound * opponentCount)
  dsimp only
  have hopponentCountNat : 0 < Fintype.card ι - 1 := by omega
  have hopponentCount : 0 < opponentCount := by
    have hcast : (0 : ℝ) < ((Fintype.card ι - 1 : ℕ) : ℝ) := by
      exact_mod_cast hopponentCountNat
    simpa [opponentCount] using hcast
  have htailBound : ∀ player, |tail player| ≤ bound := by
    intro player
    exact abs_quittingTerminalPayoff_le reward _ player hreward
  have hquitEq :
      quittingPureTimeDeviationPayoff reward
          (quittingStationaryProfile reward sourceRoot) who (some 0) =
        quittingRootQuitPayoff reward tail sourceRoot who := by
    have hpure : quittingPureTimeDeviationPayoff reward
        (quittingStationaryProfile reward sourceRoot) who (some 0) =
      quittingStationaryFixedOpponentsQuitValue reward sourceRoot who := by
      dsimp only [quittingPureTimeDeviationPayoff]
      rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
      simp
    have hroot : quittingRootQuitPayoff reward tail sourceRoot who =
        quittingStationaryFixedOpponentsQuitValue reward sourceRoot who := by
      simpa [tail, quittingStationaryFixedOpponentsQuitValue] using
        (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
          reward (fun _ => sourceRoot) who tail 0)
    exact hpure.trans hroot.symm
  have hsuccessor : quittingRootSuccessorPayoff reward tail sourceRoot who =
      tail who := by
    symm
    simpa [tail, quittingRootSuccessorPayoff] using
      quittingTerminalPayoff_stationary_eq_rootExpectedPayoff
        reward sourceRoot who
  have hsourceProduct : gap ≤
      (sourceRoot who false).toReal *
        quittingRootEndpointDifference reward tail sourceRoot who := by
    calc
      gap ≤ quittingPureTimeDeviationPayoff reward
          (quittingStationaryProfile reward sourceRoot) who (some 0) -
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward sourceRoot) who := himmediate
      _ = quittingRootQuitPayoff reward tail sourceRoot who -
          quittingRootSuccessorPayoff reward tail sourceRoot who := by
        rw [hquitEq, hsuccessor]
      _ = _ := quittingRootQuitPayoff_sub_successorPayoff
        reward tail sourceRoot who
  have hsourceDifference : gap ≤
      quittingRootEndpointDifference reward tail sourceRoot who := by
    let ownContinue := (sourceRoot who false).toReal
    let difference :=
      quittingRootEndpointDifference reward tail sourceRoot who
    have hcontinue0 : 0 ≤ ownContinue := ENNReal.toReal_nonneg
    have hcontinue1 : ownContinue ≤ 1 := by
      have hsum := quittingRoot_continueProbability_add_quitProbability
        sourceRoot who
      have hquit0 : 0 ≤ (sourceRoot who true).toReal := ENNReal.toReal_nonneg
      dsimp only [ownContinue]
      linarith
    have hproductPos : 0 < ownContinue * difference :=
      hgap.trans_le hsourceProduct
    have hdifferencePos : 0 < difference :=
      pos_of_mul_pos_right hproductPos hcontinue0
    calc
      gap ≤ ownContinue * difference := hsourceProduct
      _ ≤ 1 * difference :=
        mul_le_mul_of_nonneg_right hcontinue1 hdifferencePos.le
      _ = difference := one_mul difference
  by_cases hsource : scale ≤
      quittingRootOpponentAbsorptionMass sourceRoot who
  · exact Or.inl hsource
  · right
    have hsourceLt : quittingRootOpponentAbsorptionMass sourceRoot who < scale :=
      lt_of_not_ge hsource
    have hgapUpper : gap ≤ 2 * bound := by
      have hquitBound :
          |quittingPureTimeDeviationPayoff reward
            (quittingStationaryProfile reward sourceRoot) who (some 0)| ≤
              bound := by
        exact abs_quittingTerminalPayoff_le reward _ who hreward
      have htailWho := htailBound who
      have hquitUpper := (abs_le.mp hquitBound).2
      have htailLower := (abs_le.mp htailWho).1
      linarith
    have hscalePos : 0 < scale := by
      dsimp only [scale]
      positivity
    have hscaleLeOne : scale ≤ 1 := by
      have hdenom : 0 < 8 * bound * opponentCount := by positivity
      apply (div_le_one hdenom).2
      have hone : 1 ≤ opponentCount := by
        have hcast : (1 : ℝ) ≤ ((Fintype.card ι - 1 : ℕ) : ℝ) := by
          exact_mod_cast hopponentCountNat
        simpa [opponentCount] using hcast
      nlinarith
    by_cases hcontinue : (exactRoot who false).toReal = 0
    · have hquitProbability : (exactRoot who true).toReal = 1 := by
        have hsum := quittingRoot_continueProbability_add_quitProbability
          exactRoot who
        linarith
      have habsorption : quittingRootAbsorptionMass exactRoot = 1 := by
        apply le_antisymm
        · unfold quittingRootAbsorptionMass
          exact sub_le_self 1 (quittingStationaryContinueMass_nonneg exactRoot)
        · rw [← hquitProbability]
          exact quittingRoot_quitProbability_le_absorptionMass exactRoot who
      rw [habsorption]
      exact hscaleLeOne
    · have hcontinuePos : 0 < (exactRoot who false).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hcontinue)
      have hexactDifference :
          quittingRootEndpointDifference reward tail exactRoot who ≤ 0 := by
        have hrow := (hnash who).1
        exact nonpos_of_mul_nonpos_right hrow hcontinuePos
      have hstability :=
        abs_quittingRootEndpointDifference_sub_le_opponentTVSum
          reward tail sourceRoot exactRoot who hreward htailBound
      have htvLower : gap / (4 * bound) ≤
          quittingRootOpponentTVSum sourceRoot exactRoot who := by
        have hraw : gap ≤ 4 * bound *
            quittingRootOpponentTVSum sourceRoot exactRoot who := by
          calc
            gap ≤ quittingRootEndpointDifference reward tail sourceRoot who :=
              hsourceDifference
            _ ≤ quittingRootEndpointDifference reward tail sourceRoot who -
                quittingRootEndpointDifference reward tail exactRoot who := by
              linarith
            _ ≤ |quittingRootEndpointDifference reward tail sourceRoot who -
                quittingRootEndpointDifference reward tail exactRoot who| :=
              le_abs_self _
            _ ≤ _ := hstability
        exact (div_le_iff₀ (by positivity : 0 < 4 * bound)).2
          (by simpa [mul_comm] using hraw)
      let opponents := Finset.univ.erase who
      let sourceSum := ∑ other ∈ opponents,
        (sourceRoot other true).toReal
      let exactSum := ∑ other ∈ opponents,
        (exactRoot other true).toReal
      have hsourceMarginal : ∀ other ∈ opponents,
          (sourceRoot other true).toReal ≤
            quittingRootOpponentAbsorptionMass sourceRoot who := by
        intro other hother
        have hne : other ≠ who := (Finset.mem_erase.mp hother).1
        have hmarginal := quittingRoot_quitProbability_le_absorptionMass
          (Function.update sourceRoot who (PMF.pure false)) other
        simpa [quittingRootOpponentAbsorptionMass, hne] using hmarginal
      have hsourceSumBound : sourceSum ≤
          opponentCount * quittingRootOpponentAbsorptionMass sourceRoot who := by
        calc
          sourceSum ≤ ∑ _other ∈ opponents,
              quittingRootOpponentAbsorptionMass sourceRoot who := by
            apply Finset.sum_le_sum
            intro other hother
            exact hsourceMarginal other hother
          _ = opponentCount *
              quittingRootOpponentAbsorptionMass sourceRoot who := by
            rw [Finset.sum_const, nsmul_eq_mul]
            have hcardReal : (opponents.card : ℝ) = opponentCount := by
              dsimp only [opponents, opponentCount]
              exact_mod_cast card_erase_eq_card_sub_one who
            rw [hcardReal]
      have hsourceSumLt : sourceSum < gap / (8 * bound) := by
        have hscaled := mul_lt_mul_of_pos_left hsourceLt hopponentCount
        dsimp only [scale] at hscaled
        have hdenom : 0 < 8 * bound := by positivity
        have hrewrite : opponentCount *
            (gap / (8 * bound * opponentCount)) = gap / (8 * bound) := by
          field_simp
        rw [hrewrite] at hscaled
        exact hsourceSumBound.trans_lt hscaled
      have htvUpper : quittingRootOpponentTVSum sourceRoot exactRoot who ≤
          sourceSum + exactSum := by
        unfold quittingRootOpponentTVSum
        dsimp only [sourceSum, exactSum, opponents]
        calc
          (∑ other ∈ Finset.univ.erase who,
              Math.Probability.pmfTV
                (sourceRoot other) (exactRoot other)) =
              ∑ other ∈ Finset.univ.erase who,
                |(sourceRoot other true).toReal -
                  (exactRoot other true).toReal| := by
            apply Finset.sum_congr rfl
            intro other _
            exact Math.Probability.pmfTV_bool_eq_abs_apply_true _ _
          _ ≤ ∑ other ∈ Finset.univ.erase who,
              ((sourceRoot other true).toReal +
                (exactRoot other true).toReal) := by
            apply Finset.sum_le_sum
            intro other _
            exact (abs_sub _ _).trans (by
              rw [abs_of_nonneg ENNReal.toReal_nonneg,
                abs_of_nonneg ENNReal.toReal_nonneg])
          _ = _ := by rw [Finset.sum_add_distrib]
      have hexactSumLower : gap / (8 * bound) ≤ exactSum := by
        have hhalf : gap / (4 * bound) =
            gap / (8 * bound) + gap / (8 * bound) := by
          field_simp
          ring
        rw [hhalf] at htvLower
        linarith
      have hopponentsNonempty : opponents.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        have hcardZero : opponents.card = 0 := by simp [hempty]
        rw [card_erase_eq_card_sub_one who] at hcardZero
        omega
      obtain ⟨other, hother, haverage⟩ :=
        Finset.exists_max_image opponents
          (fun player => (exactRoot player true).toReal) hopponentsNonempty
      have hsumAverage : exactSum ≤
          opponentCount * (exactRoot other true).toReal := by
        have hsum := Finset.sum_le_card_nsmul opponents
          (fun player => (exactRoot player true).toReal)
          ((exactRoot other true).toReal)
          (fun player hplayer => haverage player hplayer)
        dsimp only [exactSum]
        rw [nsmul_eq_mul] at hsum
        have hcardReal : (opponents.card : ℝ) = opponentCount := by
          dsimp only [opponents, opponentCount]
          exact_mod_cast card_erase_eq_card_sub_one who
        rw [hcardReal] at hsum
        exact hsum
      have hotherLower : scale ≤ (exactRoot other true).toReal := by
        have hraw : gap / (8 * bound) ≤
            opponentCount * (exactRoot other true).toReal :=
          hexactSumLower.trans hsumAverage
        have hdenom : 0 < 8 * bound * opponentCount := by positivity
        apply (div_le_iff₀ hdenom).2
        have hbaseDenom : 0 < 8 * bound := by positivity
        have hscaled := (div_le_iff₀ hbaseDenom).1 hraw
        nlinarith
      exact hotherLower.trans
        (quittingRoot_quitProbability_le_absorptionMass exactRoot other)

namespace QuittingSingletonBaseStationaryHandoff

/-- Source-native form of the exact-root sharpening.  The source root and
debtor are the literal repaired stationary data retained by the semantic
handoff; the endpoint atom certifies that immediate Quit is the selected
high endpoint. -/
theorem quitNow_source_or_exactRoot_absorption
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {owner : ι} {free : Finset ι}
    {point : mixedPolytope (quittingBinaryForm free).sig}
    {delta terminalGap bound : ℝ}
    (handoff : QuittingSingletonBaseStationaryHandoff reward owner free point
      delta terminalGap)
    (atom : QuittingPaidEndpointAtom reward
      (quittingSingletonBaseRepairedProfile reward owner free point)
      handoff.outsideDebtor terminalGap bound)
    (hquit : atom.endpoint = some 0)
    (hcard : 1 < Fintype.card ι)
    (hgap : 0 < terminalGap) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (exactRoot : ι → PMF Bool)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point))
      0 exactRoot) :
    let scale := terminalGap /
      (8 * bound * ((Fintype.card ι - 1 : ℕ) : ℝ))
    scale ≤ quittingRootOpponentAbsorptionMass
        (quittingSingletonBaseRepairedRoot owner free point)
        handoff.outsideDebtor ∨
      scale ≤ quittingRootAbsorptionMass exactRoot := by
  apply stationaryImmediateQuitGap_source_or_exactRoot_absorption
    reward (quittingSingletonBaseRepairedRoot owner free point) exactRoot
      handoff.outsideDebtor terminalGap bound hcard hgap hbound hreward
  · have hendpoint := atom.endpoint_gap
    rw [hquit] at hendpoint
    exact hendpoint
  · exact hnash

end QuittingSingletonBaseStationaryHandoff

end GameTheory
