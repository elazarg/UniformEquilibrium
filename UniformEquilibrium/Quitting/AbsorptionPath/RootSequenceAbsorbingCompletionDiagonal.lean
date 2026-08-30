/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Order.Filter.AtTopBot.Basic
import UniformEquilibrium.Quitting.AbsorptionPath.RootSequenceAbsorbingCompletion
import UniformEquilibrium.Quitting.Paths.VanishingNashRootSequenceFamily

/-!
# Diagonal absorbing completion of vanishing-Nash root sequences

A family of actual quitting root sequences whose Nash errors and `Never` masses
vanish admits a strict subsequence with canonical late sure-solo completions.
The completion at diagonal rank `k` starts no earlier than `k`, so every fixed
finite prefix is eventually unchanged.  All law, payoff, deviation-envelope,
and Nash perturbations are retained as literal convergent quantities.

The selected owner and cutoff may vary with `k`.  No path compactness, fixed
branch, fixed payoff target, or stagewise-perfect conclusion is asserted.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The canonical accuracy scale used by the diagonal completion. -/
def quittingLateCompletionDiagonalScale (rank : ℕ) : ℝ :=
  1 / ((rank : ℝ) + 1)

theorem quittingLateCompletionDiagonalScale_pos (rank : ℕ) :
    0 < quittingLateCompletionDiagonalScale rank := by
  unfold quittingLateCompletionDiagonalScale
  exact one_div_pos.mpr (by positivity)

theorem quittingLateCompletionDiagonalScale_le_one (rank : ℕ) :
    quittingLateCompletionDiagonalScale rank ≤ 1 := by
  unfold quittingLateCompletionDiagonalScale
  calc
    1 / ((rank : ℝ) + 1) ≤ 1 / 1 :=
      one_div_le_one_div_of_le (by norm_num) (by
        nlinarith [(Nat.cast_nonneg rank : 0 ≤ (rank : ℝ))])
    _ = 1 := by norm_num

theorem quittingLateCompletionDiagonalScale_tendsto_zero :
    Tendsto quittingLateCompletionDiagonalScale atTop (nhds 0) := by
  change Tendsto (fun rank : ℕ => 1 / ((rank : ℝ) + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

omit [DecidableEq ι] in
theorem quittingLateCompletionDiagonalScale_pow_tendsto_zero :
    Tendsto (fun rank =>
      quittingLateCompletionDiagonalScale rank ^ Fintype.card ι)
      atTop (nhds 0) := by
  have hpow := quittingLateCompletionDiagonalScale_tendsto_zero.pow
    (Fintype.card ι)
  simpa only [zero_pow Fintype.card_ne_zero] using hpow

/-- A strict diagonal of a vanishing-Nash source family, together with its
actual late sure-solo completion at every rank. -/
structure QuittingRootSequenceAbsorbingCompletionDiagonal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingRootSequenceVanishingNashFamily reward) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  source_never_lt_scale_pow : ∀ rank,
    quittingJointSurvivalLimit (source.roots (subsequence rank)) 0 <
      quittingLateCompletionDiagonalScale rank ^ Fintype.card ι
  completion : ∀ rank,
    QuittingRootSequenceLateSureSoloCompletion reward
      (source.roots (subsequence rank)) rank
      (source.error (subsequence rank))
      (quittingLateCompletionDiagonalScale rank)
      (quittingRewardBound reward)

namespace QuittingRootSequenceAbsorbingCompletionDiagonal

variable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : QuittingRootSequenceVanishingNashFamily reward}

/-- The source root sequence selected at one diagonal rank. -/
def selectedRoots
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) : ℕ → ι → PMF Bool :=
  source.roots (diagonal.subsequence rank)

/-- The sure-solo-completed root sequence at one diagonal rank. -/
def completedRoots
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) : ℕ → ι → PMF Bool :=
  quittingLateSureSoloRoots (diagonal.selectedRoots rank)
    (diagonal.completion rank).owner (diagonal.completion rank).cutoff

/-- The selected source Nash error. -/
def selectedError
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) : ℝ :=
  source.error (diagonal.subsequence rank)

/-- The exact additive Nash widening of the completion theorem. -/
def nashIncrement
    (_diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) : ℝ :=
  let d := quittingLateCompletionDiagonalScale rank
  2 * quittingRewardBound reward * (d + d ^ Fintype.card ι)

/-- The Nash error certified for the completed sequence. -/
def completedError
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) : ℝ :=
  diagonal.selectedError rank + diagonal.nashIncrement rank

/-- Pointwise absolute change in the complete terminal law. -/
def terminalLawPerturbation
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (outcome : Option {S : Finset ι // S.Nonempty}) (rank : ℕ) : ℝ :=
  |quittingTerminalOutcomeMass reward
        (quittingRootSequenceProfile reward (diagonal.selectedRoots rank) 0)
        outcome -
      quittingTerminalOutcomeMass reward
        (quittingRootSequenceProfile reward (diagonal.completedRoots rank) 0)
        outcome|

/-- Absolute change in one player's prescribed terminal payoff. -/
def prescribedPayoffPerturbation
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (who : ι) (rank : ℕ) : ℝ :=
  |quittingRootSequenceTerminalValue reward (diagonal.selectedRoots rank) who 0 -
      quittingRootSequenceTerminalValue reward (diagonal.completedRoots rank) who 0|

/-- Absolute change in one player's full deviation envelope. -/
def deviationEnvelopePerturbation
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (who : ι) (rank : ℕ) : ℝ :=
  |quittingRootSequenceBestResponseValue reward (diagonal.selectedRoots rank) who -
      quittingRootSequenceBestResponseValue reward (diagonal.completedRoots rank) who|

omit [Nonempty ι] in
/-- The chosen source indices are cofinal. -/
theorem subsequence_tendsto_atTop
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source) :
    Tendsto diagonal.subsequence atTop atTop :=
  diagonal.subsequence_strictMono.tendsto_atTop

omit [Nonempty ι] in
/-- The selected source Nash errors still tend to zero. -/
theorem selectedError_tendsto_zero
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source) :
    Tendsto diagonal.selectedError atTop (nhds 0) := by
  exact source.error_tendsto_zero.comp diagonal.subsequence_tendsto_atTop

omit [Nonempty ι] in
/-- The selected source `Never` masses still tend to zero. -/
theorem selectedNever_tendsto_zero
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source) :
    Tendsto (fun rank =>
      quittingJointSurvivalLimit (diagonal.selectedRoots rank) 0)
      atTop (nhds 0) := by
  exact source.never_tendsto_zero.comp diagonal.subsequence_tendsto_atTop

omit [Nonempty ι] in
/-- Every completed root sequence is completely absorbing. -/
theorem completelyAbsorbing
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) : IsCompletelyAbsorbing (diagonal.completedRoots rank) := by
  exact (diagonal.completion rank).completelyAbsorbing

omit [Nonempty ι] in
/-- Every completed sequence has exactly zero `Never` mass. -/
theorem completedNever_eq_zero
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) :
    quittingJointSurvivalLimit (diagonal.completedRoots rank) 0 = 0 := by
  exact quittingJointSurvivalLimit_lateSureSolo_eq_zero
    (diagonal.selectedRoots rank) (diagonal.completion rank).owner
      (diagonal.completion rank).cutoff

omit [Nonempty ι] in
/-- The completion cutoff is at least its diagonal rank. -/
theorem rank_le_cutoff
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) : rank ≤ (diagonal.completion rank).cutoff :=
  (diagonal.completion rank).cutoff_ge

omit [Nonempty ι] in
/-- The completion cutoffs tend to infinity. -/
theorem cutoff_tendsto_atTop
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source) :
    Tendsto (fun rank => (diagonal.completion rank).cutoff) atTop atTop := by
  exact tendsto_atTop_mono diagonal.rank_le_cutoff tendsto_id

omit [Nonempty ι] in
/-- At rank `k`, every source time strictly before `k` is retained literally. -/
theorem prefix_eq_of_lt_rank
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    {rank time : ℕ} (htime : time < rank) :
    diagonal.completedRoots rank time = diagonal.selectedRoots rank time := by
  exact (diagonal.completion rank).prefix_eq
    (htime.trans_le (diagonal.rank_le_cutoff rank))

omit [Nonempty ι] in
/-- Every fixed source time is eventually retained literally. -/
theorem eventually_prefix_eq
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (time : ℕ) :
    ∀ᶠ rank in atTop,
      diagonal.completedRoots rank time = diagonal.selectedRoots rank time := by
  filter_upwards [eventually_gt_atTop time] with rank hrank
  exact diagonal.prefix_eq_of_lt_rank hrank

/-- Pointwise terminal-law perturbations converge literally to zero. -/
theorem terminalLawPerturbation_tendsto_zero
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (outcome : Option {S : Finset ι // S.Nonempty}) :
    Tendsto (diagonal.terminalLawPerturbation outcome) atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun _ => abs_nonneg _
  · exact fun rank => (diagonal.completion rank).terminalLaw_close outcome
  · simpa only [mul_zero] using
      (quittingLateCompletionDiagonalScale_pow_tendsto_zero
        (ι := ι)).const_mul 2

/-- Prescribed-payoff perturbations converge literally to zero for every player. -/
theorem prescribedPayoffPerturbation_tendsto_zero
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (who : ι) :
    Tendsto (diagonal.prescribedPayoffPerturbation who) atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun _ => abs_nonneg _
  · exact fun rank => (diagonal.completion rank).prescribed_close who
  · simpa only [mul_zero] using
      (quittingLateCompletionDiagonalScale_pow_tendsto_zero
        (ι := ι)).const_mul (2 * quittingRewardBound reward)

omit [Nonempty ι] in
/-- Deviation-envelope perturbations converge literally to zero for every player. -/
theorem deviationEnvelopePerturbation_tendsto_zero
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (who : ι) :
    Tendsto (diagonal.deviationEnvelopePerturbation who) atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun _ => abs_nonneg _
  · exact fun rank => (diagonal.completion rank).envelope_close who
  · simpa only [mul_zero] using
      quittingLateCompletionDiagonalScale_tendsto_zero.const_mul
        (2 * quittingRewardBound reward)

/-- The exact additive Nash widening converges to zero. -/
theorem nashIncrement_tendsto_zero
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source) :
    Tendsto diagonal.nashIncrement atTop (nhds 0) := by
  change Tendsto (fun rank =>
    2 * quittingRewardBound reward *
      (quittingLateCompletionDiagonalScale rank +
        quittingLateCompletionDiagonalScale rank ^ Fintype.card ι))
    atTop (nhds 0)
  simpa only [mul_zero, add_zero] using
    (quittingLateCompletionDiagonalScale_tendsto_zero.add
      (quittingLateCompletionDiagonalScale_pow_tendsto_zero
        (ι := ι))).const_mul (2 * quittingRewardBound reward)

/-- The completed Nash errors converge to zero. -/
theorem completedError_tendsto_zero
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source) :
    Tendsto diagonal.completedError atTop (nhds 0) := by
  change Tendsto (fun rank =>
    diagonal.selectedError rank + diagonal.nashIncrement rank)
    atTop (nhds 0)
  simpa only [add_zero] using
    diagonal.selectedError_tendsto_zero.add diagonal.nashIncrement_tendsto_zero

omit [Nonempty ι] in
/-- Every completed sequence carries the exact widened Nash certificate. -/
theorem nash
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) :
    IsεQuittingRootSequenceNash reward (diagonal.completedError rank)
      (diagonal.completedRoots rank) := by
  exact (diagonal.completion rank).nash

omit [Nonempty ι] in
/-- The generated completed profile is Nash against every behavioral deviation
at the certified completed error. -/
theorem profile_isεAsymptoticNash
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (diagonal.completedError rank)
      (quittingRootSequenceProfile reward (diagonal.completedRoots rank) 0) := by
  exact (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward
    (diagonal.completedError rank) (diagonal.completedRoots rank)).mp
      (diagonal.nash rank)

end QuittingRootSequenceAbsorbingCompletionDiagonal

/-! ## Diagonal extraction -/

/-- A vanishing-Nash family with vanishing `Never` masses has a strict
subsequence of late, completely absorbing sure-solo completions with all
quantitative perturbations tending to zero. -/
theorem nonempty_rootSequenceAbsorbingCompletionDiagonal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingRootSequenceVanishingNashFamily reward) :
    Nonempty (QuittingRootSequenceAbsorbingCompletionDiagonal reward source) := by
  have heventually : ∀ rank, ∀ᶠ index in atTop,
      quittingJointSurvivalLimit (source.roots index) 0 <
        quittingLateCompletionDiagonalScale rank ^ Fintype.card ι := by
    intro rank
    exact source.never_tendsto_zero.eventually_lt_const
      (pow_pos (quittingLateCompletionDiagonalScale_pos rank) _)
  obtain ⟨subsequence, hstrict, hnever⟩ :=
    Filter.extraction_forall_of_eventually heventually
  have hcompletion : ∀ rank, Nonempty
      (QuittingRootSequenceLateSureSoloCompletion reward
        (source.roots (subsequence rank)) rank
        (source.error (subsequence rank))
        (quittingLateCompletionDiagonalScale rank)
        (quittingRewardBound reward)) := by
    intro rank
    exact exists_lateSureSoloCompletion_of_jointLimit_lt_pow reward
      (source.roots (subsequence rank)) rank
      (quittingLateCompletionDiagonalScale_pos rank)
      (abs_reward_le_quittingRewardBound reward)
      (source.nash (subsequence rank)) (hnever rank)
  exact ⟨{
    subsequence := subsequence
    subsequence_strictMono := hstrict
    source_never_lt_scale_pow := hnever
    completion := fun rank => Classical.choice (hcompletion rank)
  }⟩

end GameTheory
