/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.CompactQuantitativeAlternatives
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.ReachedPrefixCompactification
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.SurvivalCrossingRepair
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding

/-!
# The literal low-survival source and its exact residual hypotheses

A low cumulative survival value in an actual approximate-equilibrium root
sequence has a canonical first crossing.  The row immediately before that
crossing is still reached at the displayed floor, so the global Nash bound
can be transferred to that row and its support can be purified against its
actual source tail.

This does not by itself produce either semantic branch suggested by the
finite-orbit classification.  Cumulative survival can decay through many
small hazards, so the crossing row need not be nearly absorbing.  Conversely,
floor-clipped purification gives a quantitative survival-window landing only
when a positive uniform Continue-mass constant is supplied.  The theorems
below expose these two genuinely different extra inputs:

* a floor-clipped certificate with a positive uniform `rho` gives the repaired
  positive survival window; and
* a source-matched purified row which is additionally near-total can be
  rounded to a sure quitter and compiled to one actual punished profile.

The second conclusion is at one displayed accuracy.  The instant-punishment
branch requires such near-total rows at arbitrarily small errors, exactly as
recorded by `HasArbitrarilySmallQuittingNearTotalSupportRows`.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The first crossing canonically extracted from one literal low-survival
approximate-equilibrium prefix.  The complete source root sequence and its
global Nash property are retained; no stationary profile is inferred. -/
structure QuittingLowSurvivalFirstCrossingSourceAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (u accuracy : ℝ) (horizon : ℕ) where
  roots : ℕ → ι → PMF Bool
  lowStage : ℕ
  crossingStage : ℕ
  sourceNash : IsεQuittingRootSequenceNash reward accuracy roots
  lowStage_lt : lowStage < horizon
  crossingStage_pos : 0 < crossingStage
  crossingStage_le : crossingStage ≤ lowStage
  before : u < quittingJointSurvivalWeight roots 0 (crossingStage - 1)
  crossing : quittingJointSurvivalWeight roots 0 crossingStage ≤ u

/-- Every literal low-survival witness below a proper probability threshold
has a first crossing, still inside the witnessed finite prefix. -/
theorem
    nonempty_lowSurvivalFirstCrossingSource_of_lowSurvivalApproximatePrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {u accuracy : ℝ} {horizon : ℕ} (huOne : u < 1)
    (hlow : QuittingLowSurvivalApproximatePrefixAt reward u accuracy horizon) :
    Nonempty
      (QuittingLowSurvivalFirstCrossingSourceAt reward u accuracy horizon) := by
  classical
  obtain ⟨roots, lowStage, hnash, hlowStage, hlowSurvival⟩ := hlow
  have hexists : ∃ stage,
      quittingJointSurvivalWeight roots 0 stage ≤ u :=
    ⟨lowStage, hlowSurvival.le⟩
  let crossingStage := Nat.find hexists
  have hcrossing : quittingJointSurvivalWeight roots 0 crossingStage ≤ u := by
    exact Nat.find_spec hexists
  have hcrossingLe : crossingStage ≤ lowStage := by
    exact Nat.find_min' hexists hlowSurvival.le
  have hcrossingPos : 0 < crossingStage := by
    rcases Nat.eq_zero_or_pos crossingStage with hzero | hpos
    · have hone : (1 : ℝ) ≤ u := by
        rw [hzero, quittingJointSurvivalWeight_zero_fuel] at hcrossing
        exact hcrossing
      linarith
    · exact hpos
  have hbefore : u <
      quittingJointSurvivalWeight roots 0 (crossingStage - 1) := by
    exact lt_of_not_ge
      (Nat.find_min hexists (by omega : crossingStage - 1 < crossingStage))
  exact ⟨
    { roots := roots
      lowStage := lowStage
      crossingStage := crossingStage
      sourceNash := hnash
      lowStage_lt := hlowStage
      crossingStage_pos := hcrossingPos
      crossingStage_le := hcrossingLe
      before := hbefore
      crossing := hcrossing }⟩

/-- The predecessor of the first crossing is one genuine reached row of the
original approximate equilibrium, evaluated against its actual source tail. -/
theorem QuittingLowSurvivalFirstCrossingSourceAt.reachedNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    (hu : 0 < u) :
    IsεQuittingRootNash reward
      (quittingRootSequenceTailVector reward source.roots source.crossingStage)
      (accuracy /
        quittingJointSurvivalWeight source.roots 0
          (source.crossingStage - 1))
      (source.roots (source.crossingStage - 1)) := by
  have hsurvival : 0 < quittingJointSurvivalWeight source.roots 0
      (source.crossingStage - 1) := hu.trans source.before
  simpa only [Nat.sub_add_cancel source.crossingStage_pos] using
    (isεQuittingRootNash_tailVector_of_isεQuittingRootSequenceNash
      reward source.roots source.sourceNash (source.crossingStage - 1)
      hsurvival)

/-- The original predecessor row has positive absorption: it is the row at
which the survival product first strictly decreases through `u`.  There is no
uniform lower bound on this absorption, and purification may delete all of
it, so this is not a stationary or instant-punishment witness. -/
theorem QuittingLowSurvivalFirstCrossingSourceAt.predecessor_absorption_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    (hu : 0 < u) :
    0 < quittingRootAbsorptionMass
      (source.roots (source.crossingStage - 1)) := by
  have hbeforePos : 0 < quittingJointSurvivalWeight source.roots 0
      (source.crossingStage - 1) := hu.trans source.before
  have hdrop : quittingJointSurvivalWeight source.roots 0
      source.crossingStage <
        quittingJointSurvivalWeight source.roots 0
          (source.crossingStage - 1) :=
    source.crossing.trans_lt source.before
  have hrecurrence : quittingJointSurvivalWeight source.roots 0
      source.crossingStage =
        quittingJointSurvivalWeight source.roots 0
          (source.crossingStage - 1) *
        quittingStationaryContinueMass
          (source.roots (source.crossingStage - 1)) := by
    have hrec := quittingJointSurvivalWeight_succ source.roots 0
      (source.crossingStage - 1)
    rw [Nat.sub_add_cancel source.crossingStage_pos] at hrec
    simpa only [zero_add] using hrec
  have hcontinue : quittingStationaryContinueMass
      (source.roots (source.crossingStage - 1)) < 1 := by
    rw [hrecurrence] at hdrop
    nlinarith
  unfold quittingRootAbsorptionMass
  linarith

/-- Reached-row support purification applied at the literal first-crossing
source.  The tail is the actual continuation of the retained root sequence;
this theorem supplies neither floor rationality nor a stationary Bellman
self-loop. -/
theorem QuittingLowSurvivalFirstCrossingSourceAt.supportPurified
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    {β d M η : ℝ}
    (haccuracy : 0 < accuracy) (hu : 0 < u) (hβ : 0 < β) (hd : 0 < d)
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hscale : accuracy < u * β * d)
    (herror : β + 4 * M * (Fintype.card ι : ℝ) * d ≤ η) :
    IsQuittingRootSupportApproxNash reward
      (quittingRootSequenceTailVector reward source.roots source.crossingStage)
      η
      (quittingSupportPurifiedRoot reward
        (quittingRootSequenceTailVector reward source.roots
          source.crossingStage)
        β (source.roots (source.crossingStage - 1))) := by
  simpa only [Nat.sub_add_cancel source.crossingStage_pos] using
    (isQuittingRootSupportApproxNash_supportPurifiedRoot_of_reachedNash
      reward source.roots (source.crossingStage - 1) haccuracy hu hβ hd hM
        hreward source.sourceNash source.before.le hscale herror)

/-- The actual source profile restarted at the predecessor of the first
crossing. -/
def QuittingLowSurvivalFirstCrossingSourceAt.predecessorProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward source.roots (source.crossingStage - 1)

/-- The actual continuation after all players Continue at the predecessor
row. -/
def QuittingLowSurvivalFirstCrossingSourceAt.continuation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon) :
    (quittingGame reward).BehaviorProfile :=
  quittingProfileAllContinueContinuation reward source.predecessorProfile

/-- The continuation above is literally the retained root sequence restarted
at the crossing stage. -/
theorem QuittingLowSurvivalFirstCrossingSourceAt.continuation_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon) :
    source.continuation =
      quittingRootSequenceProfile reward source.roots source.crossingStage := by
  unfold QuittingLowSurvivalFirstCrossingSourceAt.continuation
    QuittingLowSurvivalFirstCrossingSourceAt.predecessorProfile
    quittingProfileAllContinueContinuation
  rw [shiftProfile_quittingRootSequenceProfile]
  congr 1
  exact Nat.sub_add_cancel source.crossingStage_pos

/-- The floor-clipped actual tail at the first-crossing source. -/
def QuittingLowSurvivalFirstCrossingSourceAt.clippedTail
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    (η : ℝ) : Payoff ι :=
  quittingPunishmentFloorClipAt reward η
    (fun who => quittingTerminalPayoff reward source.continuation who)

/-- The simultaneous support purification of the clipped actual crossing
row. -/
def QuittingLowSurvivalFirstCrossingSourceAt.clippedPurifiedRoot
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    (η β : ℝ) : ι → PMF Bool :=
  quittingSupportPurifiedRoot reward (source.clippedTail η) β
    (source.roots (source.crossingStage - 1))

/-- The literal source Nash property supplies the splice-Nash input of the
floor-clipped repair.  The remaining hypotheses are precisely the local
endpoint modulus, normalized near-feasibility, no-sure-quitter exclusion,
and positive uniform survival assertion used by that repair. -/
theorem QuittingLowSurvivalFirstCrossingSourceAt.floorClippedCertificate
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    {β d e η σ ρ : ℝ}
    (haccuracy : 0 < accuracy) (hu : 0 < u) (hβ : 0 < β) (hd : 0 < d)
    (hη : 0 < η) (hscale : accuracy < u * β * d)
    (hendpointError : β + 2 * e ≤ η)
    (hησ : η ≤ σ) (hηρ : η ≤ ρ)
    (hstable : IsQuittingRootEndpointStableWithin reward
      (source.clippedTail η) (source.roots (source.crossingStage - 1)) d e)
    (hnear : QuittingSimonNearFeasiblePayoffAt reward 1
      (source.clippedTail η))
    (hnoSure : SuppliedQuittingSimonNoSureQuitterAt reward σ)
    (huniform : SuppliedQuittingSimonCorrectedUniformSurvivalAt reward ρ) :
    QuittingFloorClippedPurificationCertificate reward
      (source.clippedTail η) d η ρ
      (Fintype.card ι * accuracy /
        (quittingJointSurvivalWeight source.roots 0
          (source.crossingStage - 1) * β))
      (source.roots (source.crossingStage - 1))
      (source.clippedPurifiedRoot η β) := by
  let survival := quittingJointSurvivalWeight source.roots 0
    (source.crossingStage - 1)
  have hsurvival : 0 < survival := hu.trans source.before
  have hshift := isεQuittingRootSequenceNash_shift_of_survival_ge
    reward source.roots haccuracy.le hsurvival source.sourceNash
      (source.crossingStage - 1) le_rfl
  have hprofileNash :
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (accuracy / survival)
        source.predecessorProfile := by
    have hbehavior :=
      (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward
        (accuracy / survival)
        (fun offset => source.roots
          (source.crossingStage - 1 + offset))).mp hshift
    have hprofile :
        quittingRootSequenceProfile reward
            (fun offset => source.roots
              (source.crossingStage - 1 + offset)) 0 =
      source.predecessorProfile := by
      funext player time history
      simp [quittingRootSequenceProfile,
        QuittingLowSurvivalFirstCrossingSourceAt.predecessorProfile]
    rwa [hprofile] at hbehavior
  have hadapter :=
    (isεAsymptoticNash_firstStageAdapter_iff reward
      source.predecessorProfile (accuracy / survival)).mpr hprofileNash
  have hroot : quittingProfileRoot reward source.predecessorProfile =
      source.roots (source.crossingStage - 1) := by
    funext who
    rfl
  unfold quittingFirstStageAdapter at hadapter
  rw [hroot] at hadapter
  have hscaleActual : accuracy < survival * β * d := by
    calc
      accuracy < u * β * d := hscale
      _ = u * (β * d) := by ring
      _ < survival * (β * d) :=
        mul_lt_mul_of_pos_right source.before (mul_pos hβ hd)
      _ = survival * β * d := by ring
  exact floorClippedPurificationCertificate_of_spliceNash reward
    (source.roots (source.crossingStage - 1)) source.continuation
    haccuracy hsurvival hβ hd hη hscaleActual hendpointError hησ hηρ
      hadapter hstable hnear hnoSure huniform

/-- A floor-clipped certificate with positive uniform Continue mass turns the
literal first crossing into the corrected positive survival window.  This is
the maximal quantitative conclusion of the repaired crossing calculation;
the certificate's positive `rho` is an additional compact-carrier input, not
a consequence of low cumulative survival. -/
theorem QuittingLowSurvivalFirstCrossingSourceAt.repairedSurvivalWindow
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    (tail : Payoff ι) (purified : ι → PMF Bool)
    {d η ρ β : ℝ}
    (certificate : QuittingFloorClippedPurificationCertificate reward tail
      d η ρ
        (Fintype.card ι * accuracy /
          (quittingJointSurvivalWeight source.roots 0
            (source.crossingStage - 1) * β))
      (source.roots (source.crossingStage - 1)) purified)
    (hu : 0 < u) (hρ : 0 < ρ) (hβ : 0 < β)
    (hbudget : accuracy ≤
      ρ * (3 * u) * β / (6 * Fintype.card ι)) :
    ρ / 2 < quittingStationaryContinueMass
        (source.roots (source.crossingStage - 1)) ∧
      u * ρ / 2 < quittingJointSurvivalWeight source.roots 0
        source.crossingStage ∧
      quittingJointSurvivalWeight source.roots 0 source.crossingStage ≤ u := by
  have hbefore : 3 * u / 3 < quittingJointSurvivalWeight source.roots 0
      (source.crossingStage - 1) := by
    simpa only [show 3 * u / 3 = u by ring] using source.before
  have hcrossing : quittingJointSurvivalWeight source.roots 0
      source.crossingStage ≤ 3 * u / 3 := by
    simpa only [show 3 * u / 3 = u by ring] using source.crossing
  have hresult := certificate.firstCrossing_interval reward tail source.roots
    purified source.crossingStage source.crossingStage_pos (by positivity :
      0 < 3 * u) hρ hβ hbefore hcrossing hbudget
  simpa only [show 3 * u * ρ / 6 = u * ρ / 2 by ring,
    show 3 * u / 3 = u by ring] using hresult

/-- The source-to-window connector with no certificate supplied by the
caller.  It makes explicit exactly which compact-carrier hypotheses remain
after the actual root-sequence Nash data have supplied the splice semantics. -/
theorem
    QuittingLowSurvivalFirstCrossingSourceAt.repairedSurvivalWindow_of_sourceData
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    {β d e η σ ρ : ℝ}
    (haccuracy : 0 < accuracy) (hu : 0 < u) (hβ : 0 < β) (hd : 0 < d)
    (hη : 0 < η) (hρ : 0 < ρ) (hscale : accuracy < u * β * d)
    (hendpointError : β + 2 * e ≤ η)
    (hησ : η ≤ σ) (hηρ : η ≤ ρ)
    (hstable : IsQuittingRootEndpointStableWithin reward
      (source.clippedTail η) (source.roots (source.crossingStage - 1)) d e)
    (hnear : QuittingSimonNearFeasiblePayoffAt reward 1
      (source.clippedTail η))
    (hnoSure : SuppliedQuittingSimonNoSureQuitterAt reward σ)
    (huniform : SuppliedQuittingSimonCorrectedUniformSurvivalAt reward ρ)
    (hbudget : accuracy ≤
      ρ * (3 * u) * β / (6 * Fintype.card ι)) :
    ρ / 2 < quittingStationaryContinueMass
        (source.roots (source.crossingStage - 1)) ∧
      u * ρ / 2 < quittingJointSurvivalWeight source.roots 0
        source.crossingStage ∧
      quittingJointSurvivalWeight source.roots 0 source.crossingStage ≤ u := by
  have certificate := source.floorClippedCertificate haccuracy hu hβ hd hη
    hscale hendpointError hησ hηρ hstable hnear hnoSure huniform
  exact source.repairedSurvivalWindow (source.clippedTail η)
    (source.clippedPurifiedRoot η β) certificate hu hρ hβ hbudget

/-- If the source-matched purified crossing row is additionally near-total,
finite-product rounding produces a sure quitter and the production
first-branch compiler gives one unrestricted-behavior punished profile.

The near-total inequality is not implied by the low-survival source or by
`repairedSurvivalWindow`.  Iterating this theorem at errors tending to zero
requires a producer of arbitrarily small near-total rows. -/
theorem QuittingLowSurvivalFirstCrossingSourceAt.exists_punishedProfile_of_nearTotal
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    (tail : Payoff ι) (purified : ι → PMF Bool)
    {d η ρ loss rate M δ : ℝ}
    (certificate : QuittingFloorClippedPurificationCertificate reward tail
      d η ρ loss (source.roots (source.crossingStage - 1)) purified)
    (hrate : 0 < rate) (hrateOne : rate < 1)
    (hmass : quittingStationaryContinueMass purified <
      rate ^ Fintype.card ι)
    (hη : 0 ≤ η)
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htail : ∀ player, |tail player| ≤ M)
    (hδ : 0 < δ) :
    ∃ (quitter : ι) (rounded punishRow : ι → PMF Bool),
      rounded quitter = PMF.pure true ∧
        quittingStationaryUnilateralCap reward punishRow quitter ≤
          quittingPunishmentValue reward quitter + δ ∧
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward)
          (2 * (η + 4 * M * rate) + δ)
          (quittingOneStagePunishedProfile reward rounded punishRow) := by
  obtain ⟨quitter, hcontinue⟩ :=
    exists_continueProbability_lt_of_continueMass_lt_pow_card
      purified hrate.le hmass
  let rounded := quittingSureQuitRound purified quitter
  have hsupport : IsQuittingRootSupportApproxNash reward tail
      (η + 4 * M * rate) rounded := by
    exact supportApproxNash_sureQuitRound reward tail purified quitter
      hrate.le hrateOne hcontinue hM hreward htail certificate.support
  have hrational : QuittingSimonRationalPayoffAt reward
      (η + 4 * M * rate) tail := by
    have hcost : 0 ≤ 4 * M * rate := by positivity
    exact certificate.rational.mono (by linarith)
  have hroundedError : 0 ≤ η + 4 * M * rate := by positivity
  obtain ⟨punishRow, hpunish, hnash⟩ :=
    exists_oneStagePunishedProfile_of_rational_support_sureQuitter
      reward tail rounded quitter hroundedError hδ hrational hsupport
      (quittingSureQuitRound_quitter purified quitter)
  exact ⟨quitter, rounded, punishRow,
    quittingSureQuitRound_quitter purified quitter, hpunish, hnash⟩

end GameTheory
