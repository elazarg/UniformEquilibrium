/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.AdjacentDeadlineSingletonSeparatedTailDispatch

/-!
# Adjacent-deadline selected boundary-effect dispatch

A supplied adjacent exact timing source and singleton-separated behavioral tail
yield either a macroscopic selected boundary-effect gauge or a paid reverse
participant. The selected gauge observes all `Never`-coordinate discrepancies
and one observer boundary-gain discrepancy. It is bounded by, but is not equal
to, the full finite-deadline operational-effect distance.

The robust Fin4 payment is `27 * delta * (gamma / bound) ^ 4 / 4096`. Exact
agreement of the selected coordinates improves this to
`7 * delta * (gamma / bound) ^ 3 / 256`. The source and tail remain supplied:
this module does not select either object, put the tail on a minimum fibre, make
the tail Nash, or produce chronology, return, renewal, rank, terminal
approximation, or a uniform-equilibrium payoff. The large selected-effect arm
is returned unchanged and has no consumer here.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The old included observer gain at the newly exposed boundary action. -/
def quittingAdjacentDeadlineOldBoundaryGain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound) : ℝ :=
  (quittingFiniteDeadlineTimingGame reward (source.deadline + 1)).mixedGain
    (quittingAdjacentDeadlineOldIncludedTiming source) source.observer
    (quittingFiniteDeadlineTimingBoundaryAction source.deadline)

/-- The fully censored successor observer gain at the newly exposed boundary
action. -/
def quittingAdjacentDeadlineCensoredBoundaryGain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound) : ℝ :=
  (quittingFiniteDeadlineTimingGame reward (source.deadline + 1)).mixedGain
    (quittingAdjacentDeadlineCensoredTiming source) source.observer
    (quittingFiniteDeadlineTimingBoundaryAction source.deadline)

/-- The selected boundary-effect gauge: the largest `Never`-coefficient
discrepancy, together with the normalized discrepancy of the one selected
observer response.  This is not the full operational-effect distance. -/
def quittingAdjacentDeadlineSelectedBoundaryEffectGauge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound) : ℝ := by
  letI : Nonempty ι := ⟨source.observer⟩
  exact max
    (finiteAbsoluteMaximum fun player =>
      (source.old player none).toReal -
        ((quittingFiniteDeadlineTimingProfileCensor source.new) player none).toReal)
    (|quittingAdjacentDeadlineOldBoundaryGain source -
        quittingAdjacentDeadlineCensoredBoundaryGain source| / (4 * bound))

/-- Every selected `Never` discrepancy is bounded by the selected gauge. -/
theorem abs_quittingAdjacentDeadlineOldNever_sub_censoredNever_le_gauge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (player : ι) :
    |(source.old player none).toReal -
        ((quittingFiniteDeadlineTimingProfileCensor source.new) player none).toReal| ≤
      quittingAdjacentDeadlineSelectedBoundaryEffectGauge source := by
  letI : Nonempty ι := ⟨source.observer⟩
  rw [quittingAdjacentDeadlineSelectedBoundaryEffectGauge]
  have hcoordinate := abs_le_finiteAbsoluteMaximum
    (fun current : ι =>
      (source.old current none).toReal -
        ((quittingFiniteDeadlineTimingProfileCensor source.new) current none).toReal)
    player
  exact hcoordinate.trans (le_max_left _ _)

/-- The normalized selected observer-gain discrepancy is bounded by the
selected gauge. -/
theorem abs_quittingAdjacentDeadlineOldBoundaryGain_sub_censoredGain_div_le_gauge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound) :
    |quittingAdjacentDeadlineOldBoundaryGain source -
        quittingAdjacentDeadlineCensoredBoundaryGain source| / (4 * bound) ≤
      quittingAdjacentDeadlineSelectedBoundaryEffectGauge source := by
  letI : Nonempty ι := ⟨source.observer⟩
  rw [quittingAdjacentDeadlineSelectedBoundaryEffectGauge]
  exact le_max_right _ _

/-- The selected gauge vanishes exactly when every `Never` coefficient and
the selected observer boundary gain agree. -/
theorem quittingAdjacentDeadlineSelectedBoundaryEffectGauge_eq_zero_iff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hbound : 0 < bound) :
    quittingAdjacentDeadlineSelectedBoundaryEffectGauge source = 0 ↔
      (∀ player,
        (source.old player none).toReal =
          ((quittingFiniteDeadlineTimingProfileCensor source.new)
            player none).toReal) ∧
      quittingAdjacentDeadlineOldBoundaryGain source =
        quittingAdjacentDeadlineCensoredBoundaryGain source := by
  letI : Nonempty ι := ⟨source.observer⟩
  constructor
  · intro hzero
    have hneverLe :
        finiteAbsoluteMaximum (fun player =>
          (source.old player none).toReal -
            ((quittingFiniteDeadlineTimingProfileCensor source.new)
              player none).toReal) ≤ 0 := by
      rw [← hzero]
      exact le_max_left _ _
    have hneverZero :
        finiteAbsoluteMaximum (fun player =>
          (source.old player none).toReal -
            ((quittingFiniteDeadlineTimingProfileCensor source.new)
              player none).toReal) = 0 :=
      le_antisymm hneverLe (finiteAbsoluteMaximum_nonneg _)
    have hgainScaledLe :
        |quittingAdjacentDeadlineOldBoundaryGain source -
            quittingAdjacentDeadlineCensoredBoundaryGain source| /
            (4 * bound) ≤ 0 := by
      rw [← hzero]
      exact le_max_right _ _
    have hgainScaledNonneg : 0 ≤
        |quittingAdjacentDeadlineOldBoundaryGain source -
            quittingAdjacentDeadlineCensoredBoundaryGain source| /
            (4 * bound) := by positivity
    have hgainScaled :
        |quittingAdjacentDeadlineOldBoundaryGain source -
            quittingAdjacentDeadlineCensoredBoundaryGain source| /
            (4 * bound) = 0 :=
      le_antisymm hgainScaledLe hgainScaledNonneg
    have hdenom : 4 * bound ≠ 0 := ne_of_gt (mul_pos (by norm_num) hbound)
    have hgainAbs :
        |quittingAdjacentDeadlineOldBoundaryGain source -
          quittingAdjacentDeadlineCensoredBoundaryGain source| = 0 := by
      exact (div_eq_zero_iff.mp hgainScaled).resolve_right hdenom
    refine ⟨?_, sub_eq_zero.mp (abs_eq_zero.mp hgainAbs)⟩
    intro player
    exact sub_eq_zero.mp
      ((finiteAbsoluteMaximum_eq_zero_iff _).mp hneverZero player)
  · rintro ⟨hnever, hgain⟩
    unfold quittingAdjacentDeadlineSelectedBoundaryEffectGauge
    rw [(finiteAbsoluteMaximum_eq_zero_iff _).2]
    · rw [hgain, sub_self, abs_zero, zero_div, max_self]
    · intro player
      exact sub_eq_zero.mpr (hnever player)

/-- The selected gauge is bounded by the full finite-clock operational
effect distance.  The latter contains every hard payoff and pure-action gain;
this theorem uses only its `Never` family and the selected boundary gain. -/
theorem quittingAdjacentDeadlineSelectedBoundaryEffectGauge_le_operationalEffectDistance
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hbound : 0 < bound) :
    quittingAdjacentDeadlineSelectedBoundaryEffectGauge source ≤
      letI : Nonempty ι := ⟨source.observer⟩
      quittingFiniteDeadlineOperationalEffectDistance reward bound
          (source.deadline + 1)
          (quittingAdjacentDeadlineOldIncludedTiming source)
          (quittingAdjacentDeadlineCensoredTiming source) := by
  letI : Nonempty ι := ⟨source.observer⟩
  unfold quittingAdjacentDeadlineSelectedBoundaryEffectGauge
    quittingFiniteDeadlineOperationalEffectDistance
    finiteClockOperationalEffectDistance
  dsimp only [quittingFiniteDeadlineOperationalObservables,
    quittingAdjacentDeadlineOldBoundaryGain,
    quittingAdjacentDeadlineCensoredBoundaryGain]
  have hnever :
      (finiteAbsoluteMaximum fun player =>
          (source.old player none).toReal -
            ((quittingFiniteDeadlineTimingProfileCensor source.new)
              player none).toReal) =
        finiteAbsoluteMaximum fun player =>
          (quittingAdjacentDeadlineOldIncludedTiming source player none).toReal -
            (quittingAdjacentDeadlineCensoredTiming source player none).toReal := by
    congr 1
    funext player
    unfold quittingAdjacentDeadlineOldIncludedTiming
      quittingAdjacentDeadlineCensoredTiming
    rw [finiteDeadlineTimingProfileInclude_none_toReal source.old player]
    rw [finiteDeadlineTimingProfileInclude_none_toReal
      (quittingFiniteDeadlineTimingProfileCensor source.new) player]
  refine max_le_max hnever.le ?_
  have hcoordinate := abs_le_finiteAbsoluteMaximum
      (fun entry : ι × QuittingFiniteDeadlineTimingAction
          (source.deadline + 1) =>
        (quittingFiniteDeadlineOperationalObservables reward
              (source.deadline + 1)
              (quittingAdjacentDeadlineOldIncludedTiming source)).gain
            entry.1 entry.2 -
          (quittingFiniteDeadlineOperationalObservables reward
              (source.deadline + 1)
              (quittingAdjacentDeadlineCensoredTiming source)).gain
            entry.1 entry.2)
      (source.observer,
        quittingFiniteDeadlineTimingBoundaryAction source.deadline)
  have hdenom : 0 ≤ 4 * bound := (mul_pos (by norm_num) hbound).le
  have hscaled := div_le_div_of_nonneg_right hcoordinate hdenom
  exact hscaled.trans <| le_max_right _ _

/-- A selected gauge below `gamma / (8 * bound)` forces every censored
`Never` coefficient above `3 * (gamma / bound) / 4`. -/
theorem quittingAdjacentDeadlineCensoredNever_ge_threeFourths
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hgamma : 0 < gamma) (hbound : 0 < bound)
    (hscale : gamma / bound ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (hsmall : quittingAdjacentDeadlineSelectedBoundaryEffectGauge source <
      gamma / bound / 8)
    (player : ι) :
    (3 / 4 : ℝ) * (gamma / bound) ≤
      ((quittingFiniteDeadlineTimingProfileCensor source.new) player none).toReal := by
  have hsupport := quittingAdjacentDeadlineOldObserverNever_ne_zero_of_smallPass
    source hgamma hbound hscale hpass
  have hcoordinate :=
    (abs_quittingAdjacentDeadlineOldNever_sub_censoredNever_le_gauge
      source player).trans_lt hsmall
  have hforward :
      (source.old player none).toReal -
          ((quittingFiniteDeadlineTimingProfileCensor source.new) player none).toReal <
        gamma / bound / 8 :=
    (le_abs_self _).trans_lt hcoordinate
  by_cases hplayer : player = source.observer
  · subst player
    nlinarith
  · have hold := quittingAdjacentDeadlineOldNever_ge_div_of_ne_observer
      source hbound hreward hsupport hplayer
    have hscalePos : 0 < gamma / bound := div_pos hgamma hbound
    nlinarith

/-- The selected-gauge floor holds simultaneously on every opponent
coefficient of every possible participant. -/
theorem quittingAdjacentDeadlineCensoredOpponentNeverProduct_ge_selected
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hgamma : 0 < gamma) (hbound : 0 < bound)
    (hscale : gamma / bound ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (hsmall : quittingAdjacentDeadlineSelectedBoundaryEffectGauge source <
      gamma / bound / 8)
    (participant : ι) :
    ((3 / 4 : ℝ) * (gamma / bound)) ^ (Fintype.card ι - 1) ≤
      quittingAdjacentDeadlineCensoredOpponentNeverProduct source participant := by
  unfold quittingAdjacentDeadlineCensoredOpponentNeverProduct
  have hcard : (Finset.univ.erase participant).card = Fintype.card ι - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ participant), Finset.card_univ]
  rw [← hcard, ← Finset.prod_const]
  exact Finset.prod_le_prod
    (fun _ _ => mul_nonneg (by norm_num) (div_nonneg hgamma.le hbound.le))
    (fun player _ =>
      quittingAdjacentDeadlineCensoredNever_ge_threeFourths
        source hgamma hbound hscale hreward hpass hsmall player)

/-- Exact selected-coordinate equality gives the sharper Fin4 opponent
cylinder floor `7 * (gamma / bound)^2 / 8`. -/
theorem quittingAdjacentDeadlineCensoredOpponentNeverProduct_ge_of_never_eq_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hgamma : 0 < gamma) (hbound : 0 < bound)
    (hscale : gamma / bound ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (hnever : ∀ player,
      (source.old player none).toReal =
        ((quittingFiniteDeadlineTimingProfileCensor source.new)
          player none).toReal)
    (participant : Fin 4) :
    (7 / 8 : ℝ) * (gamma / bound) ^ 2 ≤
      quittingAdjacentDeadlineCensoredOpponentNeverProduct source participant := by
  let a := gamma / bound
  have haPos : 0 < a := div_pos hgamma hbound
  have haNonneg : 0 ≤ a := haPos.le
  have haOne : a ≤ 1 := hscale
  have hsupport := quittingAdjacentDeadlineOldObserverNever_ne_zero_of_smallPass
    source hgamma hbound hscale hpass
  have holdProduct :
      a ≤ quittingAdjacentDeadlineOldOpponentNeverProduct source :=
    quittingAdjacentDeadlineOldOpponentNeverProduct_ge_div_of_support
      source hbound hreward hsupport
  have hobserver : (7 / 8 : ℝ) ≤
      (source.old source.observer none).toReal := by
    dsimp only [a] at haOne ⊢
    nlinarith
  have holdCylinder : (7 / 8 : ℝ) * a ^ 2 ≤
      ∏ player ∈ Finset.univ.erase participant,
        (source.old player none).toReal := by
    by_cases hparticipant : participant = source.observer
    · subst participant
      have haSquareLe : a ^ 2 ≤ a := by
        nlinarith [mul_nonneg haNonneg (sub_nonneg.mpr haOne)]
      calc
        (7 / 8 : ℝ) * a ^ 2 ≤ a ^ 2 := by
          nlinarith [sq_nonneg a]
        _ ≤ a := haSquareLe
        _ ≤ quittingAdjacentDeadlineOldOpponentNeverProduct source := holdProduct
    · have hobserverMem :
          source.observer ∈ Finset.univ.erase participant := by
        simp [Ne.symm hparticipant]
      let rest := (Finset.univ.erase participant).erase source.observer
      have hrestCard : rest.card = 2 := by
        dsimp only [rest]
        rw [Finset.card_erase_of_mem hobserverMem,
          Finset.card_erase_of_mem (Finset.mem_univ participant),
          Finset.card_univ]
        norm_num
      have hrest : a ^ 2 ≤
          ∏ player ∈ rest, (source.old player none).toReal := by
        rw [← hrestCard, ← Finset.prod_const]
        exact Finset.prod_le_prod
          (fun _ _ => haNonneg)
          (fun player hplayer =>
            quittingAdjacentDeadlineOldNever_ge_div_of_ne_observer
              source hbound hreward hsupport
                (Finset.ne_of_mem_erase hplayer))
      rw [← Finset.mul_prod_erase (Finset.univ.erase participant)
        (fun player => (source.old player none).toReal) hobserverMem]
      exact mul_le_mul hobserver hrest (sq_nonneg a) ENNReal.toReal_nonneg
  rw [show quittingAdjacentDeadlineCensoredOpponentNeverProduct
      source participant =
        ∏ player ∈ Finset.univ.erase participant,
          (source.old player none).toReal by
    unfold quittingAdjacentDeadlineCensoredOpponentNeverProduct
    apply Finset.prod_congr rfl
    intro player _
    exact (hnever player).symm]
  simpa only [a] using holdCylinder

/-- Small selected effect forces the total successor boundary participation
to carry at least `gamma / (8 * bound)`. -/
theorem quittingAdjacentDeadlineBoundaryParticipation_ge_of_gauge_lt
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hgamma : 0 < gamma) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hsmall : quittingAdjacentDeadlineSelectedBoundaryEffectGauge source <
      gamma / bound / 8) :
    gamma / (8 * bound) ≤ source.boundaryParticipationMass := by
  have hscaled :=
    (abs_quittingAdjacentDeadlineOldBoundaryGain_sub_censoredGain_div_le_gauge
      source).trans_lt
      hsmall
  have hdenom : 0 < 4 * bound := mul_pos (by norm_num) hbound
  have hgainDifference :
      |quittingAdjacentDeadlineOldBoundaryGain source -
          quittingAdjacentDeadlineCensoredBoundaryGain source| < gamma / 2 := by
    have hraw := (div_lt_iff₀ hdenom).mp hscaled
    calc
      |quittingAdjacentDeadlineOldBoundaryGain source -
          quittingAdjacentDeadlineCensoredBoundaryGain source| <
          gamma / bound / 8 * (4 * bound) := hraw
      _ = gamma / 2 := by field_simp; ring
  have hcensoredEffect : gamma / 2 <
      quittingAdjacentDeadlineCensoredBoundaryGain source -
        (quittingFiniteDeadlineTimingGame reward
          (source.deadline + 1)).mixedGain source.new source.observer
            (quittingFiniteDeadlineTimingBoundaryAction source.deadline) := by
    have hupper := (abs_lt.mp hgainDifference).2
    have hold : gamma ≤ quittingAdjacentDeadlineOldBoundaryGain source := by
      exact source.oldBoundaryGain_ge
    have hnew := source.newBoundaryGain_nonpos
    linarith
  have hlipschitz := abs_quittingFiniteDeadlineTiming_mixedGain_sub_le
    reward (source.deadline + 1) (quittingAdjacentDeadlineCensoredTiming source)
      source.new source.observer
      (quittingFiniteDeadlineTimingBoundaryAction source.deadline)
      hbound.le hreward
  have hmass : gamma / (8 * bound) ≤
      ∑ player, Math.Probability.pmfTV
        (quittingAdjacentDeadlineCensoredTiming source player)
        (source.new player) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hbound)).2
    have heffectLeAbs :
        quittingAdjacentDeadlineCensoredBoundaryGain source -
            (quittingFiniteDeadlineTimingGame reward
              (source.deadline + 1)).mixedGain source.new source.observer
                (quittingFiniteDeadlineTimingBoundaryAction source.deadline) ≤
          |quittingAdjacentDeadlineCensoredBoundaryGain source -
            (quittingFiniteDeadlineTimingGame reward
              (source.deadline + 1)).mixedGain source.new source.observer
                (quittingFiniteDeadlineTimingBoundaryAction source.deadline)| :=
      le_abs_self _
    change
      |quittingAdjacentDeadlineCensoredBoundaryGain source -
          (quittingFiniteDeadlineTimingGame reward
            (source.deadline + 1)).mixedGain source.new source.observer
              (quittingFiniteDeadlineTimingBoundaryAction source.deadline)| ≤
        4 * bound * ∑ player,
          Math.Probability.pmfTV
            (quittingAdjacentDeadlineCensoredTiming source player)
            (source.new player) at hlipschitz
    nlinarith
  unfold QuittingAdjacentDeadlineGapSource.boundaryParticipationMass
  simpa [quittingAdjacentDeadlineCensoredTiming,
    quittingFiniteDeadlineTimingProfileCensor,
    quittingFiniteDeadlineTimingProfileInclude] using hmass.trans_eq
      (sum_pmfTV_quittingFiniteDeadline_include_censor_eq_boundary
        source.deadline source.new)

/-- Exact equality of the selected old and censored boundary gains forces the
sharp total boundary-mass floor `gamma / (4 * bound)`. -/
theorem quittingAdjacentDeadlineBoundaryParticipation_ge_of_selectedGain_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hgain : quittingAdjacentDeadlineOldBoundaryGain source =
      quittingAdjacentDeadlineCensoredBoundaryGain source) :
    gamma / (4 * bound) ≤ source.boundaryParticipationMass := by
  have hcensoredEffect : gamma ≤
      quittingAdjacentDeadlineCensoredBoundaryGain source -
        (quittingFiniteDeadlineTimingGame reward
          (source.deadline + 1)).mixedGain source.new source.observer
            (quittingFiniteDeadlineTimingBoundaryAction source.deadline) := by
    have hold : gamma ≤ quittingAdjacentDeadlineOldBoundaryGain source :=
      source.oldBoundaryGain_ge
    have hnew := source.newBoundaryGain_nonpos
    linarith
  have hlipschitz := abs_quittingFiniteDeadlineTiming_mixedGain_sub_le
    reward (source.deadline + 1) (quittingAdjacentDeadlineCensoredTiming source)
      source.new source.observer
      (quittingFiniteDeadlineTimingBoundaryAction source.deadline)
      hbound.le hreward
  have hmass : gamma / (4 * bound) ≤
      ∑ player, Math.Probability.pmfTV
        (quittingAdjacentDeadlineCensoredTiming source player)
        (source.new player) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hbound)).2
    have heffectLeAbs :
        quittingAdjacentDeadlineCensoredBoundaryGain source -
            (quittingFiniteDeadlineTimingGame reward
              (source.deadline + 1)).mixedGain source.new source.observer
                (quittingFiniteDeadlineTimingBoundaryAction source.deadline) ≤
          |quittingAdjacentDeadlineCensoredBoundaryGain source -
            (quittingFiniteDeadlineTimingGame reward
              (source.deadline + 1)).mixedGain source.new source.observer
                (quittingFiniteDeadlineTimingBoundaryAction source.deadline)| :=
      le_abs_self _
    change
      |quittingAdjacentDeadlineCensoredBoundaryGain source -
          (quittingFiniteDeadlineTimingGame reward
            (source.deadline + 1)).mixedGain source.new source.observer
              (quittingFiniteDeadlineTimingBoundaryAction source.deadline)| ≤
        4 * bound * ∑ player,
          Math.Probability.pmfTV
            (quittingAdjacentDeadlineCensoredTiming source player)
            (source.new player) at hlipschitz
    linarith
  unfold QuittingAdjacentDeadlineGapSource.boundaryParticipationMass
  simpa [quittingAdjacentDeadlineCensoredTiming,
    quittingFiniteDeadlineTimingProfileCensor,
    quittingFiniteDeadlineTimingProfileInclude] using hmass.trans_eq
      (sum_pmfTV_quittingFiniteDeadline_include_censor_eq_boundary
        source.deadline source.new)

/-- The generic payment floor obtained from the averaged successor-boundary
mass, the selected censored opponent cylinder, and the singleton-tail gap. -/
def quittingAdjacentDeadlineSelectedEffectPaymentFloor
    (ι : Type) [Fintype ι] (gamma bound delta : ℝ) : ℝ :=
  gamma * delta / (16 * bound * (Fintype.card ι : ℝ)) *
    ((3 / 4 : ℝ) * (gamma / bound)) ^ (Fintype.card ι - 1)

/-- Exact reverse-edge payment from separately supplied boundary-mass,
opponent-cylinder, and singleton-tail floors. -/
theorem finiteDeadlineCensoredGraft_payoffGain_ge_selectedEffect
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) (participant : ι)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (htail : delta / 2 ≤
      quittingTerminalPayoff reward tail participant -
        reward (quittingSingletonTerminal participant) participant)
    (hboundary : gamma / (8 * bound * (Fintype.card ι : ℝ)) ≤
      (source.new participant
        (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal)
    (hcylinder :
      ((3 / 4 : ℝ) * (gamma / bound)) ^ (Fintype.card ι - 1) ≤
        quittingAdjacentDeadlineCensoredOpponentNeverProduct
          source participant) :
    quittingAdjacentDeadlineSelectedEffectPaymentFloor ι gamma bound delta ≤
      quittingTerminalPayoff reward
          (quittingAdjacentDeadlineCensoredGraft source tail) participant -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineParticipantGraft source tail participant)
          participant := by
  rw [finiteDeadlineCensoredGraft_sub_participantGraft_eq]
  have hcardNat : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr ⟨participant⟩
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hcardNat
  have hpow : 0 ≤
      ((3 / 4 : ℝ) * (gamma / bound)) ^ (Fintype.card ι - 1) := by
    positivity
  have hboundaryNonneg : 0 ≤ (source.new participant
      (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal :=
    ENNReal.toReal_nonneg
  have hcylinderNonneg : 0 ≤
      quittingAdjacentDeadlineCensoredOpponentNeverProduct
        source participant := by
    unfold quittingAdjacentDeadlineCensoredOpponentNeverProduct
    exact Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  calc
    quittingAdjacentDeadlineSelectedEffectPaymentFloor ι gamma bound delta =
      (gamma / (8 * bound * (Fintype.card ι : ℝ))) *
        (((3 / 4 : ℝ) * (gamma / bound)) ^ (Fintype.card ι - 1)) *
          (delta / 2) := by
      unfold quittingAdjacentDeadlineSelectedEffectPaymentFloor
      field_simp
      ring
    _ ≤ (source.new participant
          (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal *
        quittingAdjacentDeadlineCensoredOpponentNeverProduct
          source participant *
        (quittingTerminalPayoff reward tail participant -
          reward (quittingSingletonTerminal participant) participant) := by
      gcongr

/-- The paid selected-effect certificate stores only the selected participant
and the new payment floor.  Its exact update, payoff, cap, and debt projections
delegate to the common public reverse-edge identities below. -/
structure QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) (participant : ι) : Prop where
  payoffGain_ge :
    quittingAdjacentDeadlineSelectedEffectPaymentFloor ι gamma bound delta ≤
      quittingTerminalPayoff reward
          (quittingAdjacentDeadlineCensoredGraft source tail) participant -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineParticipantGraft source tail participant)
          participant

namespace QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound delta : ℝ}
    {source : QuittingAdjacentDeadlineGapSource reward gamma bound}
    {tail : (quittingGame reward).BehaviorProfile} {participant : ι}

/-- The certificate's endpoints are literally one own-strategy update. -/
theorem update_eq
    (_edge : QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant
      (delta := delta) source tail participant) :
    quittingAdjacentDeadlineCensoredGraft source tail =
      Function.update
        (quittingAdjacentDeadlineParticipantGraft source tail participant)
        participant
        (quittingAdjacentDeadlineCensoredGraft source tail participant) :=
  quittingAdjacentDeadlineCensoredGraft_eq_update_participant
    source tail participant

/-- Exact payoff identity for the selected reverse participant. -/
theorem payoffGain_eq
    (_edge : QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant
      (delta := delta) source tail participant) :
    quittingTerminalPayoff reward
          (quittingAdjacentDeadlineCensoredGraft source tail) participant -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineParticipantGraft source tail participant)
          participant =
      (source.new participant
          (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal *
        quittingAdjacentDeadlineCensoredOpponentNeverProduct source participant *
        (quittingTerminalPayoff reward tail participant -
          reward (quittingSingletonTerminal participant) participant) :=
  finiteDeadlineCensoredGraft_sub_participantGraft_eq
    source tail participant

/-- The mover's unrestricted continuation cap is unchanged. -/
theorem bestResponseValue_eq
    (_edge : QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant
      (delta := delta) source tail participant) :
    quittingContinuationBestResponseValue reward
        (quittingAdjacentDeadlineCensoredGraft source tail) participant =
      quittingContinuationBestResponseValue reward
        (quittingAdjacentDeadlineParticipantGraft source tail participant)
        participant :=
  finiteDeadlineCensoredGraft_bestResponseValue_eq source tail participant

/-- Exact mover-debt subtraction by the displayed payoff gain. -/
theorem semanticDebt_eq_sub_payoffGain
    (_edge : QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant
      (delta := delta) source tail participant) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingAdjacentDeadlineCensoredGraft source tail)) participant =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAdjacentDeadlineParticipantGraft source tail participant))
          participant -
        (quittingTerminalPayoff reward
            (quittingAdjacentDeadlineCensoredGraft source tail) participant -
          quittingTerminalPayoff reward
            (quittingAdjacentDeadlineParticipantGraft source tail participant)
            participant) :=
  finiteDeadlineCensoredGraft_semanticDebt_eq_sub_payoffGain
    source tail participant

end QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant

/-- Either the selected boundary-effect gauge is macroscopic, or the same
literal tail supports a paid reverse-participant update.  The first branch is
returned unchanged and has no consumer here. -/
theorem quittingAdjacentDeadline_selectedBoundaryEffectGauge_ge_or_paidReverseParticipant
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (hscale : gamma / bound ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (htail : ∀ player, delta / 2 ≤
      quittingTerminalPayoff reward tail player -
        reward (quittingSingletonTerminal player) player) :
    gamma / bound / 8 ≤
        quittingAdjacentDeadlineSelectedBoundaryEffectGauge source ∨
      ∃ participant,
        QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant
          (delta := delta) source tail participant := by
  by_cases hlarge : gamma / bound / 8 ≤
      quittingAdjacentDeadlineSelectedBoundaryEffectGauge source
  · exact Or.inl hlarge
  · right
    have hsmall := lt_of_not_ge hlarge
    have hboundary :=
      quittingAdjacentDeadlineBoundaryParticipation_ge_of_gauge_lt
        source hgamma hbound hreward hsmall
    obtain ⟨participant, hparticipant⟩ :=
      exists_quittingAdjacentDeadlineBoundaryParticipant_ge_average
        source hboundary
    have hcylinder :=
      quittingAdjacentDeadlineCensoredOpponentNeverProduct_ge_selected
        source hgamma hbound hscale hreward hpass hsmall participant
    refine ⟨participant, ⟨?_⟩⟩
    exact finiteDeadlineCensoredGraft_payoffGain_ge_selectedEffect
      source tail participant hgamma hbound hdelta (htail participant)
        hparticipant hcylinder

/-- The source-specific full operational distance dominates the selected
gauge, so it inherits the same paid reverse-participant alternative.  The
large full-distance branch is returned unchanged and remains unconsumed. -/
theorem quittingAdjacentDeadline_operationalEffectDistance_ge_or_paidReverseParticipant
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (hscale : gamma / bound ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (htail : ∀ player, delta / 2 ≤
      quittingTerminalPayoff reward tail player -
        reward (quittingSingletonTerminal player) player) :
    (letI : Nonempty ι := ⟨source.observer⟩;
      gamma / bound / 8 ≤
        quittingFiniteDeadlineOperationalEffectDistance reward bound
          (source.deadline + 1)
          (quittingAdjacentDeadlineOldIncludedTiming source)
          (quittingAdjacentDeadlineCensoredTiming source)) ∨
      ∃ participant,
        QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant
          (delta := delta) source tail participant := by
  letI : Nonempty ι := ⟨source.observer⟩
  rcases
      quittingAdjacentDeadline_selectedBoundaryEffectGauge_ge_or_paidReverseParticipant
        source tail hgamma hbound hdelta hscale hreward hpass htail with
    hlarge | hpaid
  · exact Or.inl <| hlarge.trans
      (quittingAdjacentDeadlineSelectedBoundaryEffectGauge_le_operationalEffectDistance
        source hbound)
  · exact Or.inr hpaid

/-- Exact equality of the selected `Never` vector and observer boundary gain
produces a Fin4 reverse participant with the sharp `7 / 256` payment floor.
The returned selected-effect certificate also carries the common exact
update, payoff, cap, and debt projections. -/
theorem quittingAdjacentDeadline_paidReverseParticipant_finFour_of_selectedBoundaryCoordinates_eq
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (hscale : gamma / bound ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (htail : ∀ player, delta / 2 ≤
      quittingTerminalPayoff reward tail player -
        reward (quittingSingletonTerminal player) player)
    (hnever : ∀ player,
      (source.old player none).toReal =
        ((quittingFiniteDeadlineTimingProfileCensor source.new)
          player none).toReal)
    (hgain : quittingAdjacentDeadlineOldBoundaryGain source =
      quittingAdjacentDeadlineCensoredBoundaryGain source) :
    ∃ participant,
      QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant
          (delta := delta) source tail participant ∧
        7 * delta * (gamma / bound) ^ 3 / 256 ≤
          quittingTerminalPayoff reward
              (quittingAdjacentDeadlineCensoredGraft source tail) participant -
            quittingTerminalPayoff reward
              (quittingAdjacentDeadlineParticipantGraft
                source tail participant) participant := by
  have hboundary :=
    quittingAdjacentDeadlineBoundaryParticipation_ge_of_selectedGain_eq
      source hbound hreward hgain
  obtain ⟨participant, hparticipantRaw⟩ :=
    exists_quittingAdjacentDeadlineBoundaryParticipant_ge_average_of_total
      source hboundary
  have hparticipant : gamma / (16 * bound) ≤
      (source.new participant
        (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal := by
    convert hparticipantRaw using 1
    norm_num only [Fintype.card_fin]
    ring
  have hcylinder :=
    quittingAdjacentDeadlineCensoredOpponentNeverProduct_ge_of_never_eq_finFour
      source hgamma hbound hscale hreward hpass hnever participant
  have hstrong : 7 * delta * (gamma / bound) ^ 3 / 256 ≤
      quittingTerminalPayoff reward
          (quittingAdjacentDeadlineCensoredGraft source tail) participant -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineParticipantGraft source tail participant)
          participant := by
    rw [finiteDeadlineCensoredGraft_sub_participantGraft_eq]
    have hboundaryNonneg : 0 ≤ (source.new participant
        (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal :=
      ENNReal.toReal_nonneg
    have hcylinderNonneg : 0 ≤
        quittingAdjacentDeadlineCensoredOpponentNeverProduct
          source participant := by
      unfold quittingAdjacentDeadlineCensoredOpponentNeverProduct
      exact Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
    calc
      7 * delta * (gamma / bound) ^ 3 / 256 =
          (gamma / (16 * bound)) *
            ((7 / 8 : ℝ) * (gamma / bound) ^ 2) * (delta / 2) := by
        field_simp
        ring
      _ ≤ (source.new participant
            (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal *
          quittingAdjacentDeadlineCensoredOpponentNeverProduct
            source participant *
          (quittingTerminalPayoff reward tail participant -
            reward (quittingSingletonTerminal participant) participant) := by
        gcongr
        exact htail participant
  have hscalePos : 0 < gamma / bound := div_pos hgamma hbound
  have hrobustLeStrong :
      27 * delta * (gamma / bound) ^ 4 / 4096 ≤
        7 * delta * (gamma / bound) ^ 3 / 256 := by
    let a := gamma / bound
    have haNonneg : 0 ≤ a := hscalePos.le
    have hfactorNonneg : 0 ≤ delta * a ^ 3 :=
      mul_nonneg hdelta.le (pow_nonneg haNonneg _)
    calc
      27 * delta * a ^ 4 / 4096 =
          (27 / 4096 : ℝ) * (delta * a ^ 3) * a := by ring
      _ ≤ (27 / 4096 : ℝ) * (delta * a ^ 3) * 1 := by
        gcongr
      _ = (27 / 4096 : ℝ) * (delta * a ^ 3) := by ring
      _ ≤ (7 / 256 : ℝ) * (delta * a ^ 3) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) hfactorNonneg
      _ = 7 * delta * a ^ 3 / 256 := by ring
  have hrecordFloor :
      quittingAdjacentDeadlineSelectedEffectPaymentFloor
          (Fin 4) gamma bound delta ≤
        quittingTerminalPayoff reward
            (quittingAdjacentDeadlineCensoredGraft source tail) participant -
          quittingTerminalPayoff reward
            (quittingAdjacentDeadlineParticipantGraft
              source tail participant) participant := by
    calc
      quittingAdjacentDeadlineSelectedEffectPaymentFloor
          (Fin 4) gamma bound delta =
        27 * delta * (gamma / bound) ^ 4 / 4096 := by
          unfold quittingAdjacentDeadlineSelectedEffectPaymentFloor
          norm_num only [Fintype.card_fin, Nat.reduceSubDiff]
          ring
      _ ≤ 7 * delta * (gamma / bound) ^ 3 / 256 := hrobustLeStrong
      _ ≤ _ := hstrong
  exact ⟨participant, ⟨hrecordFloor⟩, hstrong⟩

/-- Selected-gauge zero is exactly the coordinate equality required by the
sharp Fin4 paid-participant theorem. -/
theorem
    quittingAdjacentDeadline_paidReverseParticipant_finFour_of_selectedBoundaryEffectGauge_eq_zero
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (hscale : gamma / bound ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (htail : ∀ player, delta / 2 ≤
      quittingTerminalPayoff reward tail player -
        reward (quittingSingletonTerminal player) player)
    (hzero : quittingAdjacentDeadlineSelectedBoundaryEffectGauge source = 0) :
    ∃ participant,
      QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant
          (delta := delta) source tail participant ∧
        7 * delta * (gamma / bound) ^ 3 / 256 ≤
          quittingTerminalPayoff reward
              (quittingAdjacentDeadlineCensoredGraft source tail) participant -
            quittingTerminalPayoff reward
              (quittingAdjacentDeadlineParticipantGraft
                source tail participant) participant := by
  rcases
      (quittingAdjacentDeadlineSelectedBoundaryEffectGauge_eq_zero_iff
        source hbound).mp hzero with ⟨hnever, hgain⟩
  exact
    quittingAdjacentDeadline_paidReverseParticipant_finFour_of_selectedBoundaryCoordinates_eq
      source tail hgamma hbound hdelta hscale hreward hpass htail hnever hgain

/-- Full operational-distance zero implies selected-gauge zero, and hence the
same sharp Fin4 paid participant.  No converse between the two distances is
claimed. -/
theorem quittingAdjacentDeadline_paidReverseParticipant_finFour_of_operationalEffectDistance_eq_zero
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (hscale : gamma / bound ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (htail : ∀ player, delta / 2 ≤
      quittingTerminalPayoff reward tail player -
        reward (quittingSingletonTerminal player) player)
    (hzero : quittingFiniteDeadlineOperationalEffectDistance reward bound
      (source.deadline + 1)
      (quittingAdjacentDeadlineOldIncludedTiming source)
      (quittingAdjacentDeadlineCensoredTiming source) = 0) :
    ∃ participant,
      QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant
          (delta := delta) source tail participant ∧
        7 * delta * (gamma / bound) ^ 3 / 256 ≤
          quittingTerminalPayoff reward
              (quittingAdjacentDeadlineCensoredGraft source tail) participant -
            quittingTerminalPayoff reward
              (quittingAdjacentDeadlineParticipantGraft
                source tail participant) participant := by
  have hselectedLe :=
    quittingAdjacentDeadlineSelectedBoundaryEffectGauge_le_operationalEffectDistance
      source hbound
  rw [hzero] at hselectedLe
  have hselectedNonneg :
      0 ≤ quittingAdjacentDeadlineSelectedBoundaryEffectGauge source := by
    unfold quittingAdjacentDeadlineSelectedBoundaryEffectGauge
    exact le_max_of_le_left (finiteAbsoluteMaximum_nonneg _)
  have hselectedZero :
      quittingAdjacentDeadlineSelectedBoundaryEffectGauge source = 0 :=
    le_antisymm hselectedLe hselectedNonneg
  exact
    quittingAdjacentDeadline_paidReverseParticipant_finFour_of_selectedBoundaryEffectGauge_eq_zero
      source tail hgamma hbound hdelta hscale hreward hpass htail hselectedZero

/-- Four-player normalization of the selected-effect payment floor. -/
theorem QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant.payoffGain_ge_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound delta : ℝ}
    {source : QuittingAdjacentDeadlineGapSource reward gamma bound}
    {tail : (quittingGame reward).BehaviorProfile} {participant : Fin 4}
    (edge : QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant
      (delta := delta) source tail participant) :
    27 * delta * (gamma / bound) ^ 4 / 4096 ≤
      quittingTerminalPayoff reward
          (quittingAdjacentDeadlineCensoredGraft source tail) participant -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineParticipantGraft source tail participant)
          participant := by
  convert edge.payoffGain_ge using 1
  unfold quittingAdjacentDeadlineSelectedEffectPaymentFloor
  norm_num only [Fintype.card_fin, Nat.reduceSubDiff]
  ring

/-- Fin4 selected-effect dispatch with the exact `27 / 4096` floor. -/
theorem quittingAdjacentDeadline_selectedBoundaryEffectGauge_ge_or_paidReverseParticipant_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (hscale : gamma / bound ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (htail : ∀ player, delta / 2 ≤
      quittingTerminalPayoff reward tail player -
        reward (quittingSingletonTerminal player) player) :
    gamma / bound / 8 ≤
        quittingAdjacentDeadlineSelectedBoundaryEffectGauge source ∨
      ∃ participant,
        QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant
            (delta := delta) source tail participant ∧
          27 * delta * (gamma / bound) ^ 4 / 4096 ≤
            quittingTerminalPayoff reward
                (quittingAdjacentDeadlineCensoredGraft source tail) participant -
              quittingTerminalPayoff reward
                (quittingAdjacentDeadlineParticipantGraft
                  source tail participant) participant := by
  rcases
      quittingAdjacentDeadline_selectedBoundaryEffectGauge_ge_or_paidReverseParticipant
        source tail hgamma hbound hdelta hscale hreward hpass htail with
    hlarge | ⟨participant, edge⟩
  · exact Or.inl hlarge
  · exact Or.inr ⟨participant, edge, edge.payoffGain_ge_finFour⟩

/-- Fin4 full operational-distance dispatch with the exact `27 / 4096`
paid-participant floor.  The large-effect branch remains unconsumed. -/
theorem
    quittingAdjacentDeadline_operationalEffectDistance_ge_or_paidReverseParticipant_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (hscale : gamma / bound ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (htail : ∀ player, delta / 2 ≤
      quittingTerminalPayoff reward tail player -
        reward (quittingSingletonTerminal player) player) :
    gamma / bound / 8 ≤
        quittingFiniteDeadlineOperationalEffectDistance reward bound
          (source.deadline + 1)
          (quittingAdjacentDeadlineOldIncludedTiming source)
          (quittingAdjacentDeadlineCensoredTiming source) ∨
      ∃ participant,
        QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant
            (delta := delta) source tail participant ∧
          27 * delta * (gamma / bound) ^ 4 / 4096 ≤
            quittingTerminalPayoff reward
                (quittingAdjacentDeadlineCensoredGraft source tail) participant -
              quittingTerminalPayoff reward
                (quittingAdjacentDeadlineParticipantGraft
                  source tail participant) participant := by
  rcases
      quittingAdjacentDeadline_operationalEffectDistance_ge_or_paidReverseParticipant
        source tail hgamma hbound hdelta hscale hreward hpass htail with
    hlarge | ⟨participant, edge⟩
  · exact Or.inl hlarge
  · exact Or.inr ⟨participant, edge, edge.payoffGain_ge_finFour⟩

end GameTheory
