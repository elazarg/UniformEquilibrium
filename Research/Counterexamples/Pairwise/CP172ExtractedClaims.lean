/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOrbitLimit
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Cycles.PeriodicWindowEvaluation
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryNeverCoupling

/-!
# Exact claims extracted from Answer 172

This experiment contains only claims that are independent of the unresolved
packet/window analytic approximation.  It reuses the production Bellman,
endpoint, and remaining-charge estimates.

The two main outputs are:

* a summable joint-absorption clock gives a full coordinatewise annotation
  limit, with the production remaining-charge modulus; and
* the phase/refusal alternatives fail different packet clauses.  A phase
  defect is quantitatively underfunded.  A refusal defect restores strict
  funding, so if the resulting coordinates are still not a packet, the
  missing inequality is the punishment floor.
-/

noncomputable section

namespace GameTheory.CounterexamplePairwiseConsistency.CP172

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Quantitative suffix best responses -/

/-- The probability that some opponent eventually quits is bounded by the
unweighted total joint-absorption charge.  This is the explicit denominator-
free bridge from the production survival bound to the summable-tail scale. -/
theorem one_sub_opponentSurvivalLimit_le_totalCharge
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time))) :
    1 - quittingOpponentSurvivalLimit roots who 0 ≤
      ∑' time : ℕ, quittingRootAbsorptionMass (roots time) := by
  let forced : ℕ → ι → PMF Bool := fun time ↦
    Function.update (roots time) who (PMF.pure false)
  have hforcedLe : ∀ time,
      quittingRootAbsorptionMass (forced time) ≤
        quittingRootAbsorptionMass (roots time) := by
    intro time
    exact quittingRootOpponentAbsorptionMass_le_absorptionMass
      (roots time) who
  have hforced : Summable (fun time ↦
      quittingRootAbsorptionMass (forced time)) := by
    apply Summable.of_nonneg_of_le
      (fun time ↦ sub_nonneg.mpr
        (quittingStationaryContinueMass_le_one (forced time)))
      hforcedLe hcharge
  have hforcedEq : forced = quittingRootSequenceUpdate roots who
      (quittingPureTimeHazard none) := by
    funext time player
    rfl
  have hlimit : quittingJointSurvivalLimit forced 0 =
      quittingOpponentSurvivalLimit roots who 0 := by
    have hforcedOpponent : Tendsto
        (quittingJointSurvivalWeight forced 0) atTop
        (nhds (quittingOpponentSurvivalLimit roots who 0)) := by
      apply (tendsto_quittingOpponentSurvivalLimit roots who 0).congr'
      apply Filter.Eventually.of_forall
      intro fuel
      rw [hforcedEq]
      exact
        (quittingJointSurvivalWeight_update_none_eq_opponentSurvivalWeight
          roots who 0 fuel).symm
    apply tendsto_nhds_unique
      (tendsto_quittingJointSurvivalLimit forced 0)
      hforcedOpponent
  have hforced0 : Summable (fun offset ↦
      quittingRootAbsorptionMass (forced (0 + offset))) := by
    simpa using hforced
  have hloss := one_sub_quittingJointSurvivalLimit_le_tailCharge
    forced 0 hforced0
  rw [hlimit] at hloss
  have hforcedLe0 : ∀ offset,
      quittingRootAbsorptionMass (forced (0 + offset)) ≤
        quittingRootAbsorptionMass (roots offset) := by
    intro offset
    simpa using hforcedLe offset
  exact hloss.trans (hforced0.tsum_le_tsum hforcedLe0 hcharge)

/-- Remaining total charge below one guarantees a positive deleted-player
survival denominator. -/
theorem opponentSurvivalLimit_pos_of_totalCharge_lt_one
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (hsmall : (∑' time : ℕ,
      quittingRootAbsorptionMass (roots time)) < 1) :
    0 < quittingOpponentSurvivalLimit roots who 0 := by
  have hloss := one_sub_opponentSurvivalLimit_le_totalCharge
    roots who hcharge
  linarith

/-- **Explicit suffix best-response bound.**  If opponents retain positive
survival along the suffix, the literal all-behavior best-response value is
within `2 * M * totalCharge` of `max 0 soloReward`.

For a summable tail the positive-survival hypothesis holds for every
sufficiently late suffix (for example, whenever its remaining total charge
is strictly below one). -/
theorem abs_suffixBestResponse_sub_maxSolo_le_totalCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (hpositive : 0 < quittingOpponentSurvivalLimit roots who 0) :
    |quittingRootSequenceBestResponseValue reward roots who -
        max 0 (reward (quittingSingletonTerminal who) who)| ≤
      2 * M * ∑' time : ℕ,
        quittingRootAbsorptionMass (roots time) := by
  have hcoupling :=
    abs_quittingRootSequenceBestResponseValue_sub_elementaryNever_le
      reward roots who 0 hM hreward hpositive
  have hcap : quittingElementaryTailRoots roots 0 (.never) =
      quittingElementaryCapRoots (.never : QuittingElementaryTailCap ι) := by
    funext time player
    rfl
  rw [hcap,
    quittingRootSequenceBestResponseValue_elementaryCap_never
      reward who hM hreward,
    quittingOpponentSurvivalWeight] at hcoupling
  have hloss := one_sub_opponentSurvivalLimit_le_totalCharge
    roots who hcharge
  exact hcoupling.trans (mul_le_mul_of_nonneg_left hloss
    (mul_nonneg (by norm_num) hM))

/-- Late-suffix wrapper with no separate denominator hypothesis: remaining
charge below one supplies it. -/
theorem abs_suffixBestResponse_sub_maxSolo_le_totalCharge_of_lt_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (hsmall : (∑' time : ℕ,
      quittingRootAbsorptionMass (roots time)) < 1) :
    |quittingRootSequenceBestResponseValue reward roots who -
        max 0 (reward (quittingSingletonTerminal who) who)| ≤
      2 * M * ∑' time : ℕ,
        quittingRootAbsorptionMass (roots time) :=
  abs_suffixBestResponse_sub_maxSolo_le_totalCharge reward roots who hM
    hreward hcharge
      (opponentSurvivalLimit_pos_of_totalCharge_lt_one roots who hcharge hsmall)

/-! ## Finite collision concentration, including the zero denominator -/

/-- Generic finite-window form of the late collision estimate.  `weight` is
the pre-stage survival mass, `absorption` is the one-stage absorption
probability, and `collision` is the one-stage probability of at least two
quitters.  The hypotheses `collision ≤ C * absorption²` and
`absorption ≤ rho` imply the usual conditional bound.

The conclusion explicitly separates a zero-absorption window: in that case
the (nonnegative) collision mass is also exactly zero, and no quotient is
formed. -/
theorem finite_collision_concentration_or_zero
    {κ : Type} [Fintype κ]
    (weight absorption collision : κ → ℝ) (C rho : ℝ)
    (hweight : ∀ phase, 0 ≤ weight phase)
    (habsorption : ∀ phase, 0 ≤ absorption phase)
    (hcollision : ∀ phase, 0 ≤ collision phase)
    (hC : 0 ≤ C)
    (hcap : ∀ phase, absorption phase ≤ rho)
    (hstage : ∀ phase,
      collision phase ≤ C * absorption phase ^ 2) :
    ((∑ phase, weight phase * absorption phase) = 0 ∧
        (∑ phase, weight phase * collision phase) = 0) ∨
      (0 < ∑ phase, weight phase * absorption phase ∧
        (∑ phase, weight phase * collision phase) /
            (∑ phase, weight phase * absorption phase) ≤ C * rho) := by
  let absorbed := ∑ phase, weight phase * absorption phase
  let collided := ∑ phase, weight phase * collision phase
  have habsorbed : 0 ≤ absorbed :=
    Finset.sum_nonneg fun phase _ ↦
      mul_nonneg (hweight phase) (habsorption phase)
  have hcollided : 0 ≤ collided :=
    Finset.sum_nonneg fun phase _ ↦
      mul_nonneg (hweight phase) (hcollision phase)
  have hpoint : ∀ phase,
      weight phase * collision phase ≤
        C * rho * (weight phase * absorption phase) := by
    intro phase
    have hsquare : absorption phase ^ 2 ≤
        rho * absorption phase := by
      nlinarith [habsorption phase, hcap phase]
    have hstage' : collision phase ≤ C * rho * absorption phase :=
      (hstage phase).trans (by
        nlinarith [mul_le_mul_of_nonneg_left hsquare hC])
    nlinarith [mul_le_mul_of_nonneg_left hstage' (hweight phase)]
  have hwindow : collided ≤ C * rho * absorbed := by
    dsimp only [collided, absorbed]
    calc
      (∑ phase, weight phase * collision phase) ≤
          ∑ phase, C * rho *
            (weight phase * absorption phase) :=
        Finset.sum_le_sum fun phase _ ↦ hpoint phase
      _ = C * rho *
          ∑ phase, weight phase * absorption phase := by
        rw [Finset.mul_sum]
  rcases habsorbed.eq_or_lt with hzero | hpositive
  · left
    change absorbed = 0 ∧ collided = 0
    refine ⟨hzero.symm, ?_⟩
    apply le_antisymm
    · rw [← hzero, mul_zero] at hwindow
      exact hwindow
    · exact hcollided
  · right
    refine ⟨hpositive, (div_le_iff₀ hpositive).2 ?_⟩
    simpa [mul_assoc, mul_left_comm, mul_comm] using hwindow

/-- Algebraic payoff consequence of collision concentration.  `S` is total
singleton mass, `C` collision mass, `A = S + C`, `X` the singleton reward
contribution, and `b` the collision reward contribution.  Conditional on
`A > 0` and `S > 0`, the full absorption payoff differs from the normalized
singleton mixture by at most `2 * M * C / A`.

The separate `S > 0` hypothesis is essential: if all absorption is by
collisions, the normalized singleton mixture has no denominator. -/
theorem abs_conditionalPayoff_sub_singletonMixture_le
    {A S C X b actual mixture M : ℝ}
    (hA : A = S + C) (hApos : 0 < A) (hSpos : 0 < S)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hX : |X| ≤ M * S) (hb : |b| ≤ M * C)
    (hactual : actual = (X + b) / A)
    (hmixture : mixture = X / S) :
    |actual - mixture| ≤ 2 * M * C / A := by
  have hAS : 0 < A * S := mul_pos hApos hSpos
  have hMC : 0 ≤ M * C := mul_nonneg hM hC
  have hexact : actual - mixture = (b * S - X * C) / (A * S) := by
    rw [hactual, hmixture, hA]
    field_simp [hSpos.ne', (show S + C ≠ 0 by linarith)]
    ring
  have hnum : |b * S - X * C| ≤ 2 * M * C * S := by
    calc
      |b * S - X * C| ≤ |b * S| + |X * C| := abs_sub _ _
      _ = |b| * S + |X| * C := by
        rw [abs_mul, abs_mul, abs_of_pos hSpos, abs_of_nonneg hC]
      _ ≤ (M * C) * S + (M * S) * C := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hb hSpos.le)
          (mul_le_mul_of_nonneg_right hX hC)
      _ = 2 * M * C * S := by ring
  rw [hexact, abs_div, abs_of_pos hAS]
  apply (div_le_iff₀ hAS).2
  have hscaled := mul_le_mul_of_nonneg_right hnum hApos.le
  field_simp [hApos.ne', hSpos.ne']
  nlinarith [hMC]

/-! ## Full annotation convergence from summable joint absorption -/

omit [DecidableEq ι] in
/-- A bounded Bellman path with summable joint absorption has a simultaneous
coordinatewise limit.  The limit also satisfies the sharp production
remaining-charge modulus `2 * M * tailCharge` in every coordinate. -/
theorem exists_annotationBoundary_of_summable_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : ∀ time who, |value time who| ≤ M)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time))) :
    ∃ boundary : Payoff ι,
      (∀ who, Tendsto (fun time ↦ value time who) atTop
        (nhds (boundary who))) ∧
      ∀ start who,
        |value start who - boundary who| ≤
          2 * M * ∑' offset : ℕ,
            quittingRootAbsorptionMass (roots (start + offset)) := by
  have hcoordinate : ∀ who, ∃ limit : ℝ,
      Tendsto (fun time ↦ value time who) atTop (nhds limit) := by
    intro who
    have hincrements : Summable (fun time ↦
        |value (time + 1) who - value time who|) := by
      apply Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _)
        (fun time ↦ abs_quittingPrescribedValue_succ_sub_le_absorptionMass
          reward roots who (fun time ↦ value time who) (fun time ↦ by
            have hcoordinate := congrFun (hpolicy time) who
            rw [quittingRootSuccessorPayoff_apply_eq_affine] at hcoordinate
            rw [quittingRootSuccessorPayoff_apply_eq_affine]
            exact hcoordinate)
          hreward (fun time ↦ hbound time who) time)
        (hcharge.mul_left (2 * M))
    have hdist : Summable (fun time ↦
        dist (value time who) (value time.succ who)) := by
      simpa [Real.dist_eq, abs_sub_comm, Nat.succ_eq_add_one] using hincrements
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  choose boundary hboundary using hcoordinate
  refine ⟨boundary, hboundary, ?_⟩
  intro start who
  exact abs_quittingValuePath_sub_limit_le_tailCharge
    reward roots value hpolicy boundary hM hreward hbound hcharge
      hboundary start who

/-- Exact Nash plus vanishing opponent absorption passes every solo-Quit
lower bound to the annotation limit.  This is the floor part of the ghost
packet, and uses no realization claim. -/
theorem singletonReward_le_annotationBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time, IsεQuittingRootNash reward
      (value (time + 1)) 0 (roots time))
    (boundary : Payoff ι)
    (hboundary : ∀ who, Tendsto (fun time ↦ value time who) atTop
      (nhds (boundary who)))
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (who : ι) :
    reward (quittingSingletonTerminal who) who ≤ boundary who := by
  have htotalZero : Tendsto (fun time ↦
      quittingRootAbsorptionMass (roots time)) atTop (nhds 0) :=
    hcharge.tendsto_atTop_zero
  have hopponentZero : Tendsto (fun time ↦
      quittingRootOpponentAbsorptionMass (roots time) who) atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun _ ↦ quittingOpponentClockCharge_nonneg roots who _
    · exact fun time ↦ quittingRootOpponentAbsorptionMass_le_absorptionMass
        (roots time) who
    · exact htotalZero
  have hlower : Tendsto (fun time ↦
      reward (quittingSingletonTerminal who) who -
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass (roots time) who)
      atTop (nhds (reward (quittingSingletonTerminal who) who)) := by
    simpa using tendsto_const_nhds.sub
      (hopponentZero.const_mul (2 * quittingRewardBound reward))
  apply le_of_tendsto_of_tendsto' hlower (hboundary who)
  intro time
  have hestimate :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (value (time + 1)) (roots time) who
      (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward)
  have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
    reward (value (time + 1)) (roots time) who (hnash time)
  rw [← congrFun (hpolicy time) who] at hquit
  linarith [abs_le.mp hestimate |>.1]

/-- A cofinal subsequence of positive own-Quit hazards pins the limiting
annotation exactly to the corresponding singleton reward. -/
theorem annotationBoundary_eq_singleton_of_active_subsequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (boundary : Payoff ι)
    (hboundary : ∀ who, Tendsto (fun time ↦ value time who) atTop
      (nhds (boundary who)))
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (who : ι) (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hactive : ∀ index, 0 < (roots (time index) who true).toReal) :
    boundary who = reward (quittingSingletonTerminal who) who := by
  have htotalZero : Tendsto (fun index ↦
      quittingRootAbsorptionMass (roots (time index))) atTop (nhds 0) :=
    hcharge.tendsto_atTop_zero.comp htime
  have hopponentZero : Tendsto (fun index ↦
      quittingRootOpponentAbsorptionMass (roots (time index)) who)
      atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun _ ↦ quittingOpponentClockCharge_nonneg roots who _
    · exact fun index ↦ quittingRootOpponentAbsorptionMass_le_absorptionMass
        (roots (time index)) who
    · exact htotalZero
  have hdistanceZero : Tendsto (fun index ↦
      |value (time index) who -
        reward (quittingSingletonTerminal who) who|) atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun _ ↦ abs_nonneg _
    · exact fun index ↦ hspine.abs_value_sub_singleton_le_of_quit_pos
        reward value roots who (time index) (hactive index)
    · change Tendsto (fun index ↦
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass (roots (time index)) who)
        atTop (nhds 0)
      simpa only [mul_zero] using
        hopponentZero.const_mul (2 * quittingRewardBound reward)
  have hdistanceBoundary : Tendsto (fun index ↦
      |value (time index) who -
        reward (quittingSingletonTerminal who) who|) atTop
      (nhds |boundary who -
        reward (quittingSingletonTerminal who) who|) :=
    ((hboundary who).comp htime).sub tendsto_const_nhds |>.abs
  have habs : |boundary who -
      reward (quittingSingletonTerminal who) who| = 0 :=
    tendsto_nhds_unique hdistanceBoundary hdistanceZero
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

/-- Abstract occupation-to-support bridge.  Any positive limiting occupation
coordinate which supplies an active date after every late cutoff is pinned to
the singleton reward.  Normalized late-window occupations should discharge
`hactiveAfter`; the normalization/denominator proof is deliberately kept
outside this exact Bellman lemma. -/
theorem annotationBoundary_eq_singleton_of_positive_occupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (boundary : Payoff ι)
    (hboundary : ∀ who, Tendsto (fun time ↦ value time who) atTop
      (nhds (boundary who)))
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (occupation : ℕ → ι → ℝ) (limitOccupation : ι → ℝ)
    (hoccupation : ∀ who, Tendsto (fun cutoff ↦ occupation cutoff who)
      atTop (nhds (limitOccupation who)))
    (hactiveAfter : ∀ cutoff who, 0 < occupation cutoff who →
      ∃ time, cutoff ≤ time ∧ 0 < (roots time who true).toReal)
    (who : ι) (hpositive : 0 < limitOccupation who) :
    boundary who = reward (quittingSingletonTerminal who) who := by
  have heventually : ∀ᶠ cutoff : ℕ in atTop,
      0 < occupation cutoff who :=
    (hoccupation who).eventually (Ioi_mem_nhds hpositive)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 heventually
  have hexists : ∀ index, ∃ time,
      index ≤ time ∧ 0 < (roots time who true).toReal := by
    intro index
    let cutoff := max threshold index
    have hocc : 0 < occupation cutoff who := hthreshold cutoff
      (le_max_left threshold index)
    obtain ⟨time, hcutoff, hactive⟩ := hactiveAfter cutoff who hocc
    exact ⟨time, (le_max_right threshold index).trans hcutoff, hactive⟩
  choose time htime hactive using hexists
  have htendsto : Tendsto time atTop atTop :=
    Filter.tendsto_atTop_mono htime tendsto_id
  exact annotationBoundary_eq_singleton_of_active_subsequence
    reward roots value hspine boundary hboundary hcharge who time htendsto
      hactive

/-! ## Exact phase/refusal packet algebra -/

/-- Mixture decomposition when the active owner's singleton value is `z`.
The term `R` is the conditional refusal value and `lambda` is the owner's
occupation mass. -/
theorem mixture_eq_owner_add_refusal
    (lambda z R : ℝ) :
    lambda * z + (1 - lambda) * R =
      R - lambda * (R - z) := by
  ring

/-- A phase-stop defect at a pinned player is quantitatively incompatible
with packet funding. -/
theorem phase_defect_forces_underfunding
    {solo mixture target eta : ℝ}
    (hpin : target = solo) (hphase : mixture + eta ≤ solo) :
    mixture + eta ≤ target := by
  simpa [hpin] using hphase

/-- A refusal defect has the opposite geometry.  With positive proper owner
mass and support pinning, refusal strictly exceeds the pinned target and the
mixture strictly funds that target. -/
theorem refusal_defect_forces_strict_funding
    {lambda z R mixture eta : ℝ}
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (hmixture : mixture = lambda * z + (1 - lambda) * R)
    (heta : 0 < eta) (hrefusal : mixture + eta ≤ R) :
    z < R ∧ z < mixture := by
  have hgap : eta ≤ lambda * (R - z) := by
    rw [hmixture, mixture_eq_owner_add_refusal] at hrefusal
    linarith
  have hRz : 0 < R - z := by
    by_contra hnot
    have hnonpos : R - z ≤ 0 := le_of_not_gt hnot
    have : lambda * (R - z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hlambda0.le hnonpos
    linarith
  constructor
  · linarith
  · rw [hmixture]
    have hweight : 0 < 1 - lambda := sub_pos.mpr hlambda1
    nlinarith

/-- If phase/refusal values are bounded by `M`, a refusal margin forces a
quantitative lower bound on the owner's occupation share. -/
theorem refusal_defect_forces_owner_mass
    {lambda z R mixture eta M : ℝ}
    (hlambda0 : 0 ≤ lambda)
    (hmixture : mixture = lambda * z + (1 - lambda) * R)
    (hz : |z| ≤ M) (hR : |R| ≤ M)
    (hrefusal : mixture + eta ≤ R) :
    eta ≤ 2 * M * lambda := by
  have hgap : eta ≤ lambda * (R - z) := by
    rw [hmixture, mixture_eq_owner_add_refusal] at hrefusal
    linarith
  have hRz : R - z ≤ 2 * M := by
    have hz' := abs_le.mp hz
    have hR' := abs_le.mp hR
    linarith
  calc
    eta ≤ lambda * (R - z) := hgap
    _ ≤ lambda * (2 * M) := mul_le_mul_of_nonneg_left hRz hlambda0
    _ = 2 * M * lambda := by ring

/-- Corrected packet-clause alternative.  In the phase branch funding fails.
In the refusal branch funding is strict; consequently, if funding and floor
still do not jointly hold, it is exactly the floor inequality that fails. -/
theorem phase_underfunded_or_refusal_floor_missing
    {lambda z R mixture eta chi : ℝ}
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (hmixture : mixture = lambda * z + (1 - lambda) * R)
    (heta : 0 < eta)
    (hbranch : mixture + eta ≤ z ∨ mixture + eta ≤ R)
    (hnotPacketClauses : ¬(z ≤ mixture ∧ chi ≤ z)) :
    mixture < z ∨ (z < mixture ∧ ¬chi ≤ z) := by
  rcases hbranch with hphase | hrefusal
  · exact Or.inl (lt_of_lt_of_le (lt_add_of_pos_right mixture heta) hphase)
  · right
    have hfund := (refusal_defect_forces_strict_funding hlambda0 hlambda1
      hmixture heta hrefusal).2
    exact ⟨hfund, fun hfloor ↦ hnotPacketClauses ⟨hfund.le, hfloor⟩⟩


end GameTheory.CounterexamplePairwiseConsistency.CP172
