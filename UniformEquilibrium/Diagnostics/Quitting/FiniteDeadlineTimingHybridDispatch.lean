/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.SequenceVariation
import UniformEquilibrium.Diagnostics.Quitting.AdjacentDeadlineGapSource
import UniformEquilibrium.Diagnostics.Quitting.RetainedTailFiniteTimingRealization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport

/-!
# Coordinatewise hybrid dispatch for adjacent timing laws

An explicit nodup list enumerating exactly the opponents of the selected
observer determines a coordinatewise hybrid chain from the included old law
to the successor law.  The observer's own marginal is replaced last.

The boundary gain telescope has two exhaustive outputs.  Either the last
own-coordinate replacement is a literal paid unilateral edge, or an earlier
opponent replacement carries a common-boundary-response square.  The square
is not asserted to be a profitable edge for its mover.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem exists_paid_source_drop
    (sequence : ℕ → ℝ) {gamma : ℝ} (hgamma : 0 < gamma)
    {length : ℕ} (hlength : 0 < length)
    (hfirst : gamma ≤ sequence 0)
    (hlast : sequence length ≤ 3 * gamma / 4) :
    ∃ index < length,
      3 * gamma / 4 < sequence index ∧
        gamma / (4 * (length : ℝ)) ≤
          sequence index - sequence (index + 1) := by
  let threshold := 3 * gamma / 4
  have hexists : ∃ index,
      index < length ∧ sequence (index + 1) ≤ threshold := by
    refine ⟨length - 1, by omega, ?_⟩
    have hlengthEq : length - 1 + 1 = length := by omega
    simpa [hlengthEq] using hlast
  let first := Nat.find hexists
  have hfirstSpec := Nat.find_spec hexists
  have hpaid : ∀ index, index ≤ first → threshold < sequence index := by
    intro index hindex
    cases index with
    | zero =>
        dsimp only [threshold]
        linarith
    | succ previous =>
        have hprevious : previous < first := by omega
        have hnot := Nat.find_min hexists hprevious
        push Not at hnot
        have hbound : previous < length := by
          exact lt_trans hprevious hfirstSpec.1
        exact hnot hbound
  have hdropSum : gamma / 4 ≤
      ∑ index ∈ Finset.range (first + 1),
        (sequence index - sequence (index + 1)) := by
    rw [Math.sum_range_sub_succ]
    dsimp only [threshold] at hfirstSpec
    linarith
  let average := gamma / (4 * (length : ℝ))
  have hsumAverage :
      (∑ _index ∈ Finset.range (first + 1), average) ≤ gamma / 4 := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    dsimp only [average]
    have hfirstLength : first + 1 ≤ length := by omega
    have hlengthReal : 0 < (length : ℝ) := by positivity
    have hcast : ((first + 1 : ℕ) : ℝ) ≤ length := by exact_mod_cast hfirstLength
    calc
      ((first + 1 : ℕ) : ℝ) * (gamma / (4 * (length : ℝ))) ≤
          (length : ℝ) * (gamma / (4 * (length : ℝ))) :=
        mul_le_mul_of_nonneg_right hcast (by positivity)
      _ = gamma / 4 := by field_simp
  have hsum :
      (∑ index ∈ Finset.range (first + 1), average) ≤
        ∑ index ∈ Finset.range (first + 1),
          (sequence index - sequence (index + 1)) :=
    hsumAverage.trans hdropSum
  obtain ⟨index, hindex, hdrop⟩ :=
    Finset.exists_le_of_sum_le
      (by exact ⟨0, Finset.mem_range.mpr (by omega)⟩) hsum
  refine ⟨index, ?_, hpaid index (by simpa using hindex), ?_⟩
  · exact lt_of_lt_of_le (Finset.mem_range.mp hindex) (by omega)
  · exact hdrop

/-- The coordinatewise law after replacing the first `count` players in an
explicit opponent enumeration. -/
def quittingFiniteDeadlineTimingOpponentHybrid
    {deadline : ℕ}
    (old new : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (opponents : List ι) (count : ℕ) :
    ι → PMF (QuittingFiniteDeadlineTimingAction deadline) :=
  (opponents.take count).foldl
    (fun current player => Function.update current player (new player)) old

omit [Fintype ι] in
/-- Consecutive members of the explicit hybrid chain differ by the displayed
single coordinate. -/
theorem quittingFiniteDeadlineTimingOpponentHybrid_succ
    {deadline : ℕ}
    (old new : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (opponents : List ι) {index : ℕ} (hindex : index < opponents.length) :
    quittingFiniteDeadlineTimingOpponentHybrid old new opponents (index + 1) =
      Function.update
        (quittingFiniteDeadlineTimingOpponentHybrid old new opponents index)
        opponents[index] (new opponents[index]) := by
  unfold quittingFiniteDeadlineTimingOpponentHybrid
  rw [List.take_add_one]
  have hget : opponents[index]? = some opponents[index] := by simp
  rw [hget]
  rw [List.foldl_append]
  rfl

omit [Fintype ι] in
/-- Final opponent hybrid followed by the observer's own replacement. -/
theorem quittingFiniteDeadlineTimingOpponentHybrid_update_observer_eq
    {deadline : ℕ}
    (old new : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (observer : ι) (opponents : List ι)
    (hnodup : opponents.Nodup)
    (hmem : ∀ player, player ∈ opponents ↔ player ≠ observer) :
    Function.update
        (quittingFiniteDeadlineTimingOpponentHybrid old new opponents
          opponents.length)
        observer (new observer) = new := by
  unfold quittingFiniteDeadlineTimingOpponentHybrid
  rw [List.take_length,
    Math.PMFProduct.foldl_update_family_eq_of_nodup opponents hnodup old new]
  funext player
  by_cases hplayer : player = observer
  · subst player
    simp
  · rw [Function.update_of_ne hplayer]
    simp [hmem player, hplayer]

/-- An honest explicit enumeration of all opponents has the expected
cardinality. -/
private theorem length_eq_card_sub_one_of_opponentEnumeration
    (observer : ι) (opponents : List ι)
    (hnodup : opponents.Nodup)
    (hmem : ∀ player, player ∈ opponents ↔ player ≠ observer) :
    opponents.length = Fintype.card ι - 1 := by
  have hfinset : opponents.toFinset = Finset.univ.erase observer := by
    ext player
    simp [hmem player]
  rw [← List.toFinset_card_of_nodup hnodup, hfinset,
    Finset.card_erase_of_mem (Finset.mem_univ observer), Finset.card_univ]

/-- The own-coordinate arm: a literal update with fixed opponents, paid by
the observer's prescribed-payoff increase. -/
structure QuittingFiniteDeadlinePaidOwnTimingEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (boundary : ℕ) (observer : ι) (gamma : ℝ) where
  source : ι → PMF (QuittingFiniteDeadlineTimingAction (boundary + 1))
  target : ι → PMF (QuittingFiniteDeadlineTimingAction (boundary + 1))
  target_eq : target = Function.update source observer (target observer)
  sourceBoundaryGain_gt : 3 * gamma / 4 <
    (quittingFiniteDeadlineTimingGame reward (boundary + 1)).mixedGain
      source observer (quittingFiniteDeadlineTimingBoundaryAction boundary)
  payoffGain_gt : 3 * gamma / 4 <
    (quittingFiniteDeadlineTimingGame reward (boundary + 1)).mixedExtension.eu
        target observer -
      (quittingFiniteDeadlineTimingGame reward (boundary + 1)).mixedExtension.eu
        source observer

/-- The opponent-coordinate arm: a paid source and an exact common-response
square.  No sign is asserted for the mover's own payoff change. -/
structure QuittingFiniteDeadlinePaidResponseSquare
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (boundary : ℕ) (observer : ι) (gamma : ℝ) where
  mover : ι
  mover_ne_observer : mover ≠ observer
  source : ι → PMF (QuittingFiniteDeadlineTimingAction (boundary + 1))
  target : ι → PMF (QuittingFiniteDeadlineTimingAction (boundary + 1))
  target_eq : target = Function.update source mover (target mover)
  sourceBoundaryGain_gt : 3 * gamma / 4 <
    (quittingFiniteDeadlineTimingGame reward (boundary + 1)).mixedGain
      source observer (quittingFiniteDeadlineTimingBoundaryAction boundary)
  square_ge : gamma / (4 * ((Fintype.card ι : ℝ) - 1)) ≤
    (quittingFiniteDeadlineTimingGame reward (boundary + 1)).mixedGain
        source observer (quittingFiniteDeadlineTimingBoundaryAction boundary) -
      (quittingFiniteDeadlineTimingGame reward (boundary + 1)).mixedGain
        target observer (quittingFiniteDeadlineTimingBoundaryAction boundary)

namespace QuittingFiniteDeadlinePaidOwnTimingEdge

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {boundary : ℕ} {observer : ι} {gamma : ℝ}

/-- Actual behavioral source of the own-coordinate edge. -/
def sourceProfile
    (edge : QuittingFiniteDeadlinePaidOwnTimingEdge
      reward boundary observer gamma) :
    (quittingGame reward).BehaviorProfile :=
  quittingFiniteDeadlineTimingProfile reward (boundary + 1) edge.source

/-- Actual behavioral target of the own-coordinate edge. -/
def targetProfile
    (edge : QuittingFiniteDeadlinePaidOwnTimingEdge
      reward boundary observer gamma) :
    (quittingGame reward).BehaviorProfile :=
  quittingFiniteDeadlineTimingProfile reward (boundary + 1) edge.target

/-- The timing-law own edge is literally an update of one complete behavioral
strategy. -/
theorem targetProfile_eq_update
    (edge : QuittingFiniteDeadlinePaidOwnTimingEdge
      reward boundary observer gamma) :
    edge.targetProfile = Function.update edge.sourceProfile observer
      (edge.targetProfile observer) := by
  have hupdate := quittingRetainedTailMixedTimingProfile_update
    reward (boundary + 1) edge.source (quittingAlwaysContinueProfile reward)
      observer (edge.target observer)
  rw [← edge.target_eq] at hupdate
  change quittingRetainedTailFiniteTimingHardGraft reward
      (quittingRetainedTailMixedTimingRootStack reward (boundary + 1) edge.target) =
    Function.update
      (quittingRetainedTailFiniteTimingHardGraft reward
        (quittingRetainedTailMixedTimingRootStack reward
          (boundary + 1) edge.source)) observer
      (quittingRetainedTailFiniteTimingHardGraft reward
        (quittingRetainedTailMixedTimingRootStack reward
          (boundary + 1) edge.target) observer) at hupdate
  rw [quittingRetainedTailMixedTimingHardGraft_eq_finiteDeadlineTimingProfile,
    quittingRetainedTailMixedTimingHardGraft_eq_finiteDeadlineTimingProfile]
    at hupdate
  exact hupdate

/-- The displayed normal-form payment is the same literal terminal payoff
increase between the behavioral endpoints. -/
theorem terminalPayoffGain_gt
    (edge : QuittingFiniteDeadlinePaidOwnTimingEdge
      reward boundary observer gamma) :
    3 * gamma / 4 <
      quittingTerminalPayoff reward edge.targetProfile observer -
        quittingTerminalPayoff reward edge.sourceProfile observer := by
  simpa [sourceProfile, targetProfile,
    quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU] using
      edge.payoffGain_gt

/-- The paid source's common boundary response is the same literal
behavioral pure-time gain. -/
theorem behavioralBoundaryGain_gt
    (edge : QuittingFiniteDeadlinePaidOwnTimingEdge
      reward boundary observer gamma) :
    3 * gamma / 4 <
      quittingTerminalPayoff reward
          (Function.update edge.sourceProfile observer
            (quittingPureTimeBehaviorStrategy reward observer
              (quittingFiniteDeadlineTimingActionTime
                (quittingFiniteDeadlineTimingBoundaryAction boundary))))
          observer -
        quittingTerminalPayoff reward edge.sourceProfile observer := by
  have hdeviation :=
    quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
      reward (boundary + 1) edge.source observer
        (quittingFiniteDeadlineTimingBoundaryAction boundary)
  have hprescribed :=
    quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU
      reward (boundary + 1) edge.source observer
  have hgain := edge.sourceBoundaryGain_gt
  unfold KernelGame.mixedGain at hgain
  rw [← hdeviation, ← hprescribed] at hgain
  simpa only [sourceProfile] using hgain

/-- The observer's unrestricted behavioral cap is unchanged along the own
edge. -/
theorem bestResponseValue_eq
    (edge : QuittingFiniteDeadlinePaidOwnTimingEdge
      reward boundary observer gamma) :
    quittingContinuationBestResponseValue reward edge.targetProfile observer =
      quittingContinuationBestResponseValue reward edge.sourceProfile observer := by
  rw [edge.targetProfile_eq_update,
    quittingContinuationBestResponseValue_update_self]

/-- Exact mover-debt subtraction along the paid own edge. -/
theorem semanticDebt_eq_sub_payoffGain
    (edge : QuittingFiniteDeadlinePaidOwnTimingEdge
      reward boundary observer gamma) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward edge.targetProfile) observer =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward edge.sourceProfile) observer -
        (quittingTerminalPayoff reward edge.targetProfile observer -
          quittingTerminalPayoff reward edge.sourceProfile observer) := by
  rw [edge.targetProfile_eq_update]
  exact quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
    reward edge.sourceProfile observer (edge.targetProfile observer)

end QuittingFiniteDeadlinePaidOwnTimingEdge

namespace QuittingFiniteDeadlinePaidResponseSquare

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {boundary : ℕ} {observer : ι} {gamma : ℝ}

/-- Actual behavioral source of the response square's mover side. -/
def sourceProfile
    (square : QuittingFiniteDeadlinePaidResponseSquare
      reward boundary observer gamma) :
    (quittingGame reward).BehaviorProfile :=
  quittingFiniteDeadlineTimingProfile reward (boundary + 1) square.source

/-- Actual behavioral target of the response square's mover side. -/
def targetProfile
    (square : QuittingFiniteDeadlinePaidResponseSquare
      reward boundary observer gamma) :
    (quittingGame reward).BehaviorProfile :=
  quittingFiniteDeadlineTimingProfile reward (boundary + 1) square.target

/-- The square's mover side is a literal complete behavioral-strategy update. -/
theorem targetProfile_eq_update
    (square : QuittingFiniteDeadlinePaidResponseSquare
      reward boundary observer gamma) :
    square.targetProfile = Function.update square.sourceProfile square.mover
      (square.targetProfile square.mover) := by
  have hupdate := quittingRetainedTailMixedTimingProfile_update
    reward (boundary + 1) square.source (quittingAlwaysContinueProfile reward)
      square.mover (square.target square.mover)
  rw [← square.target_eq] at hupdate
  change quittingRetainedTailFiniteTimingHardGraft reward
      (quittingRetainedTailMixedTimingRootStack reward
        (boundary + 1) square.target) =
    Function.update
      (quittingRetainedTailFiniteTimingHardGraft reward
        (quittingRetainedTailMixedTimingRootStack reward
          (boundary + 1) square.source)) square.mover
      (quittingRetainedTailFiniteTimingHardGraft reward
        (quittingRetainedTailMixedTimingRootStack reward
          (boundary + 1) square.target) square.mover) at hupdate
  rw [quittingRetainedTailMixedTimingHardGraft_eq_finiteDeadlineTimingProfile,
    quittingRetainedTailMixedTimingHardGraft_eq_finiteDeadlineTimingProfile]
    at hupdate
  exact hupdate

/-- The mover's unrestricted cap is unchanged, although no sign is asserted
for its payoff change. -/
theorem mover_bestResponseValue_eq
    (square : QuittingFiniteDeadlinePaidResponseSquare
      reward boundary observer gamma) :
    quittingContinuationBestResponseValue reward square.targetProfile square.mover =
      quittingContinuationBestResponseValue reward square.sourceProfile square.mover := by
  rw [square.targetProfile_eq_update,
    quittingContinuationBestResponseValue_update_self]

/-- Exact mover-debt transport on the square side, with no profitability
claim. -/
theorem mover_semanticDebt_eq_sub_payoffGain
    (square : QuittingFiniteDeadlinePaidResponseSquare
      reward boundary observer gamma) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward square.targetProfile) square.mover =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward square.sourceProfile) square.mover -
        (quittingTerminalPayoff reward square.targetProfile square.mover -
          quittingTerminalPayoff reward square.sourceProfile square.mover) := by
  rw [square.targetProfile_eq_update]
  exact quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
    reward square.sourceProfile square.mover
      (square.targetProfile square.mover)

/-- The response-square lower bound is literally the drop of one common
behavioral boundary-response gain.  No sign is asserted for the mover's own
payoff change. -/
theorem behavioralCommonBoundaryResponseSquare_ge
    (square : QuittingFiniteDeadlinePaidResponseSquare
      reward boundary observer gamma) :
    gamma / (4 * ((Fintype.card ι : ℝ) - 1)) ≤
      (quittingTerminalPayoff reward
          (Function.update square.sourceProfile observer
            (quittingPureTimeBehaviorStrategy reward observer
              (quittingFiniteDeadlineTimingActionTime
                (quittingFiniteDeadlineTimingBoundaryAction boundary))))
          observer -
        quittingTerminalPayoff reward square.sourceProfile observer) -
      (quittingTerminalPayoff reward
          (Function.update square.targetProfile observer
            (quittingPureTimeBehaviorStrategy reward observer
              (quittingFiniteDeadlineTimingActionTime
                (quittingFiniteDeadlineTimingBoundaryAction boundary))))
          observer -
        quittingTerminalPayoff reward square.targetProfile observer) := by
  have hsourceDeviation :=
    quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
      reward (boundary + 1) square.source observer
        (quittingFiniteDeadlineTimingBoundaryAction boundary)
  have hsourcePrescribed :=
    quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU
      reward (boundary + 1) square.source observer
  have htargetDeviation :=
    quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
      reward (boundary + 1) square.target observer
        (quittingFiniteDeadlineTimingBoundaryAction boundary)
  have htargetPrescribed :=
    quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU
      reward (boundary + 1) square.target observer
  have hsquare := square.square_ge
  unfold KernelGame.mixedGain at hsquare
  rw [← hsourceDeviation, ← hsourcePrescribed, ← htargetDeviation,
    ← htargetPrescribed] at hsquare
  simpa only [sourceProfile, targetProfile] using hsquare

end QuittingFiniteDeadlinePaidResponseSquare

/-- Coordinatewise adjacent-hybrid dispatch.  The opponent order is explicit,
nodup, and exhaustive; no arbitrary hidden order is selected by the theorem. -/
theorem quittingAdjacentDeadline_paidOwnEdge_or_paidResponseSquare
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hgamma : 0 < gamma) (hcard : 2 ≤ Fintype.card ι)
    (opponents : List ι) (hnodup : opponents.Nodup)
    (hmem : ∀ player, player ∈ opponents ↔ player ≠ source.observer) :
    Nonempty (QuittingFiniteDeadlinePaidOwnTimingEdge reward source.deadline
        source.observer gamma) ∨
      Nonempty (QuittingFiniteDeadlinePaidResponseSquare reward source.deadline
        source.observer gamma) := by
  let initial := quittingFiniteDeadlineTimingProfileInclude source.old
  let hybrid := quittingFiniteDeadlineTimingOpponentHybrid initial source.new opponents
  let gain : ℕ → ℝ := fun index =>
    (quittingFiniteDeadlineTimingGame reward (source.deadline + 1)).mixedGain
      (hybrid index) source.observer
      (quittingFiniteDeadlineTimingBoundaryAction source.deadline)
  have hlength : opponents.length = Fintype.card ι - 1 :=
    length_eq_card_sub_one_of_opponentEnumeration
      source.observer opponents hnodup hmem
  have hlengthPos : 0 < opponents.length := by omega
  have hinitial : hybrid 0 = initial := by
    simp [hybrid, quittingFiniteDeadlineTimingOpponentHybrid]
  have hgain0 : gamma ≤ gain 0 := by
    simpa [gain, hinitial, initial] using source.oldBoundaryGain_ge
  let preOwn := hybrid opponents.length
  have htarget : Function.update preOwn source.observer
      (source.new source.observer) = source.new := by
    exact quittingFiniteDeadlineTimingOpponentHybrid_update_observer_eq
      initial source.new source.observer opponents hnodup hmem
  by_cases hpre : 3 * gamma / 4 < gain opponents.length
  · left
    have hnewGain := source.newBoundaryGain_nonpos
    have hprofileEq :
        Function.update preOwn source.observer
            (PMF.pure (quittingFiniteDeadlineTimingBoundaryAction
              source.deadline)) =
          Function.update source.new source.observer
            (PMF.pure (quittingFiniteDeadlineTimingBoundaryAction
              source.deadline)) := by
      rw [← htarget]
      simp
    have hdeviationEq :
        (quittingFiniteDeadlineTimingGame reward
          (source.deadline + 1)).mixedExtension.eu
            (Function.update preOwn source.observer
              (PMF.pure (quittingFiniteDeadlineTimingBoundaryAction
                source.deadline))) source.observer =
          (quittingFiniteDeadlineTimingGame reward
            (source.deadline + 1)).mixedExtension.eu
            (Function.update source.new source.observer
              (PMF.pure (quittingFiniteDeadlineTimingBoundaryAction
                source.deadline))) source.observer := by
      exact congrArg
        (fun profile => (quittingFiniteDeadlineTimingGame reward
          (source.deadline + 1)).mixedExtension.eu profile source.observer)
        hprofileEq
    have hpayoff : 3 * gamma / 4 <
        (quittingFiniteDeadlineTimingGame reward
          (source.deadline + 1)).mixedExtension.eu source.new source.observer -
        (quittingFiniteDeadlineTimingGame reward
          (source.deadline + 1)).mixedExtension.eu preOwn source.observer := by
      dsimp only [gain, preOwn] at hpre
      unfold KernelGame.mixedGain at hpre hnewGain
      rw [hdeviationEq] at hpre
      linarith
    exact ⟨
      { source := preOwn
        target := source.new
        target_eq := htarget.symm
        sourceBoundaryGain_gt := by simpa [gain, preOwn] using hpre
        payoffGain_gt := hpayoff }⟩
  · right
    have hfinal : gain opponents.length ≤ 3 * gamma / 4 := le_of_not_gt hpre
    obtain ⟨index, hindex, hpaid, hdrop⟩ :=
      exists_paid_source_drop gain hgamma hlengthPos hgain0 hfinal
    let edgeSource := hybrid index
    let mover := opponents[index]
    let edgeTarget := hybrid (index + 1)
    have hmover : mover ≠ source.observer :=
      (hmem mover).mp (List.getElem_mem hindex)
    have hedge : edgeTarget = Function.update edgeSource mover (source.new mover) :=
      quittingFiniteDeadlineTimingOpponentHybrid_succ
        initial source.new opponents hindex
    have hdenom : (opponents.length : ℝ) = (Fintype.card ι : ℝ) - 1 := by
      rw [hlength, Nat.cast_sub (by omega), Nat.cast_one]
    exact ⟨
      { mover := mover
        mover_ne_observer := hmover
        source := edgeSource
        target := edgeTarget
        target_eq := by
          rw [hedge]
          congr 2
          simp
        sourceBoundaryGain_gt := by simpa [gain, edgeSource] using hpaid
        square_ge := by
          rw [← hdenom]
          simpa [gain, edgeSource, edgeTarget] using hdrop }⟩

/-- In four players the response-square floor is literally `gamma / 12`. -/
theorem QuittingFiniteDeadlinePaidResponseSquare.square_ge_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {boundary : ℕ} {observer : Fin 4} {gamma : ℝ}
    (square : QuittingFiniteDeadlinePaidResponseSquare
      reward boundary observer gamma) :
    gamma / 12 ≤
      (quittingFiniteDeadlineTimingGame reward (boundary + 1)).mixedGain
          square.source observer
          (quittingFiniteDeadlineTimingBoundaryAction boundary) -
        (quittingFiniteDeadlineTimingGame reward (boundary + 1)).mixedGain
          square.target observer
          (quittingFiniteDeadlineTimingBoundaryAction boundary) := by
  have h := square.square_ge
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at h
  exact h

/-- Four-player floor on the literal common behavioral boundary-response
square. -/
theorem QuittingFiniteDeadlinePaidResponseSquare.behavioralSquare_ge_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {boundary : ℕ} {observer : Fin 4} {gamma : ℝ}
    (square : QuittingFiniteDeadlinePaidResponseSquare
      reward boundary observer gamma) :
    gamma / 12 ≤
      (quittingTerminalPayoff reward
          (Function.update square.sourceProfile observer
            (quittingPureTimeBehaviorStrategy reward observer
              (quittingFiniteDeadlineTimingActionTime
                (quittingFiniteDeadlineTimingBoundaryAction boundary))))
          observer -
        quittingTerminalPayoff reward square.sourceProfile observer) -
      (quittingTerminalPayoff reward
          (Function.update square.targetProfile observer
            (quittingPureTimeBehaviorStrategy reward observer
              (quittingFiniteDeadlineTimingActionTime
                (quittingFiniteDeadlineTimingBoundaryAction boundary))))
          observer -
        quittingTerminalPayoff reward square.targetProfile observer) := by
  have h := square.behavioralCommonBoundaryResponseSquare_ge
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at h
  exact h

end GameTheory
