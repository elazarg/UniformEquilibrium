import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryPerturbedEstimates
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-!
# Positive-time crossing in the Solan--Vieille boundary example

The first positive-time crossing retains the initial atom separately. The
initial value exceeds the solo reward, so its Continue ledger term is
nonnegative; the later high-value terms pay for their singleton mass.
This gives the printed constants and error domain of Lemma 12 and Corollary 13
of Solan and Vieille, *Quitting games -- An example* (2002).
-/

noncomputable section

namespace GameTheory
namespace SolanVieilleBoundary

open Filter

private theorem quitProbability_le_of_nearContinue
    {roots : BoundaryRootSequence (ι := Fin 4)} {ε : ℝ}
    (hclose : ∀ time who, |(roots time who false).toReal - 1| < ε) :
    ∀ time who, (roots time who true).toReal ≤ ε := by
  intro time who
  have hsum := quittingRoot_continueProbability_add_quitProbability (roots time) who
  have hlower := (abs_lt.mp (hclose time who)).1
  linarith

/-- Every finite window has positive survival when all Continue coordinates
are within an error smaller than one of pure Continue. -/
theorem boundary_jointSurvivalWeight_pos_of_nearContinue
    {roots : BoundaryRootSequence (ι := Fin 4)} {ε : ℝ} (hεsmall : ε < 1)
    (hclose : ∀ time who, |(roots time who false).toReal - 1| < ε)
    (start fuel : ℕ) : 0 < quittingJointSurvivalWeight roots start fuel := by
  rw [quittingJointSurvivalWeight_eq_prod]
  apply Finset.prod_pos
  intro offset _
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_pos
  intro who _
  have hlower := (abs_lt.mp (hclose (start + offset) who)).1
  linarith

/-- A high continuation floor after time zero bounds the prefix singleton
mass by `√ε + ε`. Only the initial value floor `1` is needed at time zero. -/
theorem boundary_finiteSingletonMass_le_sqrt_add_epsilon_of_positiveTailFloor
    {roots : BoundaryRootSequence (ι := Fin 4)} {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1)
    (hclose : ∀ time who, |(roots time who false).toReal - 1| < ε)
    (hnash : IsBoundaryTerminalApproxNash boundaryReward ε
      (boundaryRootSequenceProfile boundaryReward roots))
    (who : Fin 4) (fuel : ℕ)
    (hinitial : 1 ≤ quittingRootSequenceTerminalValue boundaryReward roots who 0)
    (hfloor : ∀ time, 0 < time → time < fuel →
      1 + Real.sqrt ε ≤ quittingRootSequenceTerminalValue boundaryReward roots who time) :
    (⟨0, fuel⟩ : QuittingFiniteRootWindow roots).singletonMass who ≤ Real.sqrt ε + ε := by
  by_cases hfuelZero : fuel = 0
  · subst fuel
    simpa [QuittingFiniteRootWindow.singletonMass] using
      add_nonneg (Real.sqrt_nonneg ε) hε.le
  have hfuel : 0 < fuel := Nat.pos_of_ne_zero hfuelZero
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hsqrt0 : 0 ≤ Real.sqrt ε := hsqrt.le
  have hsquare : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hcontinue (time : ℕ) : 0 < (roots time who false).toReal := by
    have hlower := (abs_lt.mp (hclose time who)).1
    linarith
  let advantage : ℕ → ℝ := fun time =>
    quittingRootContinuePayoff boundaryReward
        (quittingRootSequenceTailVector boundaryReward roots (time + 1))
        (roots time) who -
      quittingRootSequenceTerminalValue boundaryReward roots who time
  let ledger : ℕ → ℝ := fun time =>
    quittingOpponentSurvivalWeight roots who 0 time * advantage time
  let atom : ℕ → ℝ := fun time =>
    quittingJointSurvivalWeight roots 0 time * quittingRootCoalitionMass (roots time) {who}
  have hzeroAdvantage : 0 ≤ advantage 0 := by
    have hstage := delta_mul_quitProbability_le_continueAdvantage
      boundaryReward_cappedJointExit roots who 0 (δ := 0)
      (by norm_num) (hcontinue 0) (by simpa using hinitial)
    simpa [advantage] using hstage
  have hstage (time : ℕ) (htime : 0 < time) (hbefore : time < fuel) :
      Real.sqrt ε * (roots time who true).toReal ≤ advantage time := by
    exact delta_mul_quitProbability_le_continueAdvantage
      boundaryReward_cappedJointExit roots who time hsqrt0 (hcontinue time)
      (hfloor time htime hbefore)
  have hledgerNonneg (time : ℕ) (hbefore : time < fuel) : 0 ≤ ledger time := by
    apply mul_nonneg (quittingOpponentSurvivalWeight_nonneg roots who 0 time)
    by_cases hzero : time = 0
    · simpa [hzero] using hzeroAdvantage
    · exact (mul_nonneg hsqrt0 ENNReal.toReal_nonneg).trans
        (hstage time (Nat.pos_of_ne_zero hzero) hbefore)
  have hrootNash :=
    (isεQuittingRootSequenceNash_iff_isεAsymptoticNash boundaryReward ε roots).mpr hnash
  have hdeviation := hrootNash who
    (fun time => if time < fuel then PMF.pure false else roots time who)
  unfold quittingRootSequenceHazardTerminalValue at hdeviation
  rw [quittingRootSequenceUpdate_continueUntilHazard] at hdeviation
  have hidentity := quittingContinueUntil_terminalValue_sub_eq_sum boundaryReward roots who 0 fuel
  simp only [Nat.zero_add] at hidentity
  have hledgerCap : (∑ time ∈ Finset.range fuel, ledger time) ≤ ε := by
    change (∑ time ∈ Finset.range fuel,
      quittingOpponentSurvivalWeight roots who 0 time *
        (quittingRootContinuePayoff boundaryReward
            (quittingRootSequenceTailVector boundaryReward roots (time + 1))
            (roots time) who -
          quittingRootSequenceTerminalValue boundaryReward roots who time)) ≤ ε
    linarith
  have herasedCap : (∑ time ∈ (Finset.range fuel).erase 0, ledger time) ≤ ε := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_).trans
      hledgerCap
    intro time htime _
    exact hledgerNonneg time (Finset.mem_range.mp htime)
  have hcharged :
      Real.sqrt ε * (∑ time ∈ (Finset.range fuel).erase 0, atom time) ≤ ε := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum ?_).trans herasedCap
    intro time htime
    have hpositive : 0 < time := Nat.pos_of_ne_zero (Finset.mem_erase.mp htime).1
    have hbefore : time < fuel := Finset.mem_range.mp (Finset.mem_erase.mp htime).2
    have hadvantage : 0 ≤ advantage time :=
      (mul_nonneg hsqrt0 ENNReal.toReal_nonneg).trans (hstage time hpositive hbefore)
    have hcoalition := quittingRootCoalitionMass_le_quitProbability_of_mem
      (roots time) {who} who (by simp)
    calc
      Real.sqrt ε * atom time = quittingJointSurvivalWeight roots 0 time *
          (Real.sqrt ε * quittingRootCoalitionMass (roots time) {who}) := by
        dsimp [atom]
        ring
      _ ≤ quittingJointSurvivalWeight roots 0 time *
          (Real.sqrt ε * (roots time who true).toReal) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcoalition hsqrt0)
          (quittingJointSurvivalWeight_nonneg roots 0 time)
      _ ≤ quittingJointSurvivalWeight roots 0 time * advantage time :=
        mul_le_mul_of_nonneg_left (hstage time hpositive hbefore)
          (quittingJointSurvivalWeight_nonneg roots 0 time)
      _ ≤ ledger time := mul_le_mul_of_nonneg_right
        (quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight roots who 0 time)
        hadvantage
  have hfinite :
      (⟨0, fuel⟩ : QuittingFiniteRootWindow roots).singletonMass who =
        ∑ time ∈ Finset.range fuel, atom time := by
    simp only [QuittingFiniteRootWindow.singletonMass, QuittingFiniteRootWindow.survivalWeight,
      QuittingFiniteRootWindow.rootAt, Nat.zero_add]
    change (∑ phase : Fin fuel, atom phase.val) = _
    exact Fin.sum_univ_eq_sum_range atom fuel
  have hsplit := Finset.sum_erase_add (Finset.range fuel) atom
    (Finset.mem_range.mpr hfuel)
  rw [← hfinite] at hsplit
  have hscaledSplit := congrArg (fun mass : ℝ => Real.sqrt ε * mass) hsplit
  have hstart : atom 0 ≤ ε := by
    have hcoalition := quittingRootCoalitionMass_le_quitProbability_of_mem
      (roots 0) {who} who (by simp)
    simpa [atom, quittingJointSurvivalWeight_zero_fuel] using
      hcoalition.trans (quitProbability_le_of_nearContinue hclose 0 who)
  by_contra hnot
  have hstrict := mul_lt_mul_of_pos_left (lt_of_not_ge hnot) hsqrt
  nlinarith [hscaledSplit, mul_le_mul_of_nonneg_left hstart hsqrt0]

/-- Exact Lemma 12 constants at the first positive-time crossing. Earlier
positive times retain the high floor; time zero only needs its initial
value to exceed the solo reward. The selected finite cutoff is reached with
positive joint survival. -/
theorem boundary_exists_positiveFirstDrop_with_partnerMass
    {roots : BoundaryRootSequence (ι := Fin 4)} {ε α : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (hεsmall : ε < 1 / 900)
    (hclose : ∀ time who, |(roots time who false).toReal - 1| < ε)
    (hone : ∀ time first second,
      0 < (roots time first true).toReal → 0 < (roots time second true).toReal →
      first = second)
    (hnash : IsBoundaryTerminalApproxNash boundaryReward ε
      (boundaryRootSequenceProfile boundaryReward roots))
    (who : Fin 4)
    (hinitial : 1 + α ≤ quittingRootSequenceTerminalValue boundaryReward roots who 0) :
    ∃ cutoff : ℕ, 0 < cutoff ∧
      quittingRootSequenceTerminalValue boundaryReward roots who cutoff < 1 + Real.sqrt ε ∧
      (∀ time, 0 < time → time < cutoff → 1 + Real.sqrt ε ≤
        quittingRootSequenceTerminalValue boundaryReward roots who time) ∧
      0 < quittingJointSurvivalWeight roots 0 cutoff ∧
      (⟨0, cutoff⟩ : QuittingFiniteRootWindow roots).singletonMass who ≤ 2 * Real.sqrt ε ∧
      α - Real.sqrt ε ≤
        3 * (⟨0, cutoff⟩ : QuittingFiniteRootWindow roots).singletonMass (boundaryPartner who) := by
  have hεone : ε < 1 := by linarith
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hsqrt0 : 0 ≤ Real.sqrt ε := hsqrt.le
  have hsquare : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hsqrtSmall : Real.sqrt ε < 1 / 30 := by nlinarith
  have hinitialOne : 1 ≤ quittingRootSequenceTerminalValue boundaryReward roots who 0 :=
    le_trans (by linarith) hinitial
  have hexists : ∃ time : ℕ, 0 < time ∧
      quittingRootSequenceTerminalValue boundaryReward roots who time < 1 + Real.sqrt ε := by
    by_contra hnone
    push Not at hnone
    have hfinite (fuel : ℕ) :=
      boundary_finiteSingletonMass_le_sqrt_add_epsilon_of_positiveTailFloor
        hε hεone hclose hnash who fuel hinitialOne (fun time htime _ => hnone time htime)
    have htotal : quittingRootSequenceSingletonMass roots 0 who ≤ Real.sqrt ε + ε :=
      le_of_tendsto' (tendsto_finiteWindow_singletonMass roots 0 who) hfinite
    have hlower := boundary_singletonMass_ge_two_fifteenths_sub_eight_mul_of_atMostOne
      hε.le (quitProbability_le_of_nearContinue hclose) hone hnash who
    linarith
  let cutoff := Nat.find hexists
  have hpositive : 0 < cutoff := (Nat.find_spec hexists).1
  have hdrop : quittingRootSequenceTerminalValue boundaryReward roots who cutoff <
      1 + Real.sqrt ε := (Nat.find_spec hexists).2
  have hbefore : ∀ time, 0 < time → time < cutoff → 1 + Real.sqrt ε ≤
      quittingRootSequenceTerminalValue boundaryReward roots who time := by
    intro time htime hless
    exact le_of_not_gt (fun hlow => Nat.find_min hexists hless ⟨htime, hlow⟩)
  have hown := boundary_finiteSingletonMass_le_sqrt_add_epsilon_of_positiveTailFloor
    hε hεone hclose hnash who cutoff hinitialOne hbefore
  have hεsqrt : ε ≤ Real.sqrt ε := by
    nlinarith [mul_nonneg hsqrt0 (show 0 ≤ 1 - Real.sqrt ε by linarith)]
  have hownBound :
      (⟨0, cutoff⟩ : QuittingFiniteRootWindow roots).singletonMass who ≤ 2 * Real.sqrt ε := by
    linarith
  let window : QuittingFiniteRootWindow roots := ⟨0, cutoff⟩
  have hcollisionZero : window.collisionMass = 0 := by
    apply le_antisymm _ window.collisionMass_nonneg
    exact (finiteWindow_collisionMass_le_sequenceCollisionMass roots 0 cutoff).trans_eq
      (boundary_collisionMass_eq_zero_of_atMostOne hone)
  have hcollisionReward : window.collisionRewardContribution boundaryReward who = 0 := by
    have hbound := window.abs_collisionRewardContribution_le
      boundaryReward who boundaryReward_abs_le_four
    exact abs_nonpos_iff.mp (by simpa [hcollisionZero] using hbound)
  have hdecomp := window.terminalValue_eq_singleton_add_collision_add_survival_mul
    boundaryReward who
  rw [finiteWindow_singletonRewardContribution_eq_pairMass, hcollisionReward, add_zero]
    at hdecomp
  have hpairSum :
      (∑ owner ∈ ({who, boundaryPartner who} : Finset (Fin 4)), window.singletonMass owner) ≤
        ∑ owner : Fin 4, window.singletonMass owner :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun owner _ _ => window.singletonMass_nonneg owner)
  rw [Finset.sum_pair (Ne.symm (boundaryPartner_ne who))] at hpairSum
  change window.singletonMass who + window.singletonMass (boundaryPartner who) ≤
    window.singletonTotal at hpairSum
  have hmass := window.absorptionMass_eq_singletonTotal_add_collisionMass
  rw [hcollisionZero, add_zero] at hmass
  have hsurvival := window.absorptionMass_eq_one_sub_survivalWeight
  have hsurvivalPair : quittingJointSurvivalWeight roots 0 cutoff ≤
      1 - window.singletonMass who - window.singletonMass (boundaryPartner who) := by
    change window.absorptionMass = 1 - quittingJointSurvivalWeight roots 0 cutoff at hsurvival
    linarith
  have htail : quittingJointSurvivalWeight roots 0 cutoff *
      quittingRootSequenceTerminalValue boundaryReward roots who cutoff ≤
        quittingJointSurvivalWeight roots 0 cutoff + Real.sqrt ε := by
    have hproduct := mul_le_mul_of_nonneg_left hdrop.le
      (quittingJointSurvivalWeight_nonneg roots 0 cutoff)
    have hsqrtProduct := mul_le_mul_of_nonneg_right
      (quittingJointSurvivalWeight_le_one roots 0 cutoff) hsqrt0
    nlinarith
  refine ⟨cutoff, hpositive, hdrop, hbefore,
    boundary_jointSurvivalWeight_pos_of_nearContinue hεone hclose 0 cutoff, hownBound, ?_⟩
  change α - Real.sqrt ε ≤ 3 * window.singletonMass (boundaryPartner who)
  dsimp only [window] at hdecomp
  simp only [Nat.zero_add] at hdecomp
  change quittingRootSequenceTerminalValue boundaryReward roots who 0 =
    window.singletonMass who + 4 * window.singletonMass (boundaryPartner who) +
      quittingJointSurvivalWeight roots 0 cutoff *
        quittingRootSequenceTerminalValue boundaryReward roots who cutoff at hdecomp
  linarith

/-- Exact Corollary 13: two partners cannot both start more than `7√ε`
above the solo reward on the paper's `ε < 1/900` domain. -/
theorem boundary_not_both_partners_high_of_atMostOne
    {roots : BoundaryRootSequence (ι := Fin 4)} {ε α : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 900)
    (hclose : ∀ time who, |(roots time who false).toReal - 1| < ε)
    (hone : ∀ time first second,
      0 < (roots time first true).toReal → 0 < (roots time second true).toReal →
      first = second)
    (hnash : IsBoundaryTerminalApproxNash boundaryReward ε
      (boundaryRootSequenceProfile boundaryReward roots))
    (who : Fin 4) (hα : 7 * Real.sqrt ε < α) :
    ¬ (1 + α ≤ quittingRootSequenceTerminalValue boundaryReward roots who 0 ∧
      1 + α ≤ quittingRootSequenceTerminalValue boundaryReward roots (boundaryPartner who) 0) := by
  rintro ⟨hwho, hpartner⟩
  have hαpositive : 0 < α := by linarith [Real.sqrt_nonneg ε]
  obtain ⟨whoCutoff, _, _, _, _, hwhoSmall, hpartnerLarge⟩ :=
    boundary_exists_positiveFirstDrop_with_partnerMass
      hαpositive hε hεsmall hclose hone hnash who hwho
  obtain ⟨partnerCutoff, _, _, _, _, hpartnerSmall, hwhoLarge⟩ :=
    boundary_exists_positiveFirstDrop_with_partnerMass
      hαpositive hε hεsmall hclose hone hnash (boundaryPartner who) hpartner
  rw [boundaryPartner_partner] at hwhoLarge
  rcases le_total whoCutoff partnerCutoff with hcutoffs | hcutoffs
  · have hmono := finiteWindow_singletonMass_mono_fuel roots 0 (boundaryPartner who) hcutoffs
    linarith
  · have hmono := finiteWindow_singletonMass_mono_fuel roots 0 who hcutoffs
    linarith

end SolanVieilleBoundary
end GameTheory
