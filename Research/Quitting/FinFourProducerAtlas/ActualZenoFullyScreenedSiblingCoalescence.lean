/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.ExactPrefixAtomTransport
import Research.Quitting.FinFourProducerAtlas.ActualZenoHostCompression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPositivePartSplit
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Fully screened actual-Zeno sibling coalescence

The two actual raw descendants stored by an actual-Zeno source carry the same
new literal prefix word.  If every player-deleted clock of the complete word
vanishes, the positive base floor first transfers that screening to the new
word.  Generic common-prefix estimates then show, coordinate by coordinate,
that the siblings' prescribed payoffs, unrestricted behavioral best-response
caps, and complete terminal laws coalesce.

Only live-root equality on the displayed common word is used.  This module
does not claim equality of the complete history-dependent behavioral profiles,
near-minimality, regeneration, or a terminal consumer.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Set
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- The Bellman deleted-clock product through a literal stack is exactly the
finite-list deleted survival. -/
theorem quittingOpponentSurvivalWeight_literalRootStackProfile_eq
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (roots : List (iota → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : iota) :
    quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward
          (quittingLiteralRootStackProfile reward roots terminal))
        who 0 roots.length =
      quittingLiteralRootStackOpponentSurvival roots who := by
  rw [quittingOpponentSurvivalWeight]
  simp only [Nat.zero_add]
  calc
    (∏ offset ∈ Finset.range roots.length,
        quittingFixedOpponentsContinueMass
          (quittingProfileLiveRoot reward
            (quittingLiteralRootStackProfile reward roots terminal))
          who offset) =
        ∏ index : Fin roots.length,
          quittingFixedOpponentsContinueMass
            (quittingProfileLiveRoot reward
              (quittingLiteralRootStackProfile reward roots terminal))
            who index := Finset.prod_range _
    _ = ∏ index : Fin roots.length,
          quittingRootOpponentContinueMass roots[(index : Nat)] who := by
      apply Finset.prod_congr rfl
      intro index _
      unfold quittingFixedOpponentsContinueMass
        quittingRootOpponentContinueMass
      rw [quittingProfileLiveRoot_literalRootStackProfile_eq_getElem
        reward roots terminal index index.isLt]
    _ = quittingLiteralRootStackOpponentSurvival roots who := by
      unfold quittingLiteralRootStackOpponentSurvival
      rw [← Fin.prod_ofFn]
      change (List.ofFn (fun index : Fin roots.length =>
        (fun root => quittingRootOpponentContinueMass root who)
          roots[(index : Nat)])).prod = _
      exact congrArg List.prod
        (List.ofFn_getElem_eq_map roots
          (fun root => quittingRootOpponentContinueMass root who))

omit [DecidableEq iota] in
/-- The Bellman joint-clock product through a literal stack is exactly the
finite-list joint survival. -/
theorem quittingJointSurvivalWeight_literalRootStackProfile_eq
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (roots : List (iota → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingJointSurvivalWeight
        (quittingProfileLiveRoot reward
          (quittingLiteralRootStackProfile reward roots terminal))
        0 roots.length = quittingLiteralRootStackJointSurvival roots := by
  rw [quittingJointSurvivalWeight_eq_prod]
  simp only [Nat.zero_add]
  calc
    (∏ offset ∈ Finset.range roots.length,
        quittingStationaryContinueMass
          (quittingProfileLiveRoot reward
            (quittingLiteralRootStackProfile reward roots terminal) offset)) =
        ∏ index : Fin roots.length,
          quittingStationaryContinueMass
            (quittingProfileLiveRoot reward
              (quittingLiteralRootStackProfile reward roots terminal) index) :=
      Finset.prod_range _
    _ = ∏ index : Fin roots.length,
          quittingStationaryContinueMass roots[(index : Nat)] := by
      apply Finset.prod_congr rfl
      intro index _
      rw [quittingProfileLiveRoot_literalRootStackProfile_eq_getElem
        reward roots terminal index index.isLt]
    _ = quittingLiteralRootStackJointSurvival roots := by
      unfold quittingLiteralRootStackJointSurvival
      rw [← Fin.prod_ofFn, List.ofFn_getElem_eq_map]

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {rho : ℝ}
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource rho}
  {data : FinFourNormalizedInertVanishingDensityBoundary packet}

namespace FinFourActualZenoDeletedSurvivalSource

variable (zeno : FinFourActualZenoDeletedSurvivalSource data)

/-- The target and historical comparison descendant have literally the same
live product root at every date inside the displayed new prefix word. -/
theorem sibling_liveRoot_eq_of_lt_newWord_length
    (rank time : ℕ) (htime : time < (zeno.newWord rank).length) :
    quittingProfileLiveRoot reward (zeno.profile rank) time =
      quittingProfileLiveRoot reward (zeno.sourceProfile rank) time := by
  rw [zeno.profile_eq_literalRootStack rank,
    zeno.sourceProfile_eq_literalRootStack rank,
    quittingProfileLiveRoot_literalRootStackProfile_eq_getElem
      reward (zeno.newWord rank) (zeno.baseProfile rank) time htime,
    quittingProfileLiveRoot_literalRootStackProfile_eq_getElem
      reward (zeno.newWord rank) (zeno.baseSourceProfile rank) time htime]

/-- The comparison descendant's Bellman deleted clock through the common new
word is the source record's literal deleted-survival coordinate. -/
theorem sourceOpponentSurvivalWeight_eq_newWord
    (rank : ℕ) (who : Fin 4) :
    quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward (zeno.sourceProfile rank)) who 0
        (zeno.newWord rank).length =
      quittingLiteralRootStackOpponentSurvival (zeno.newWord rank) who := by
  rw [zeno.sourceProfile_eq_literalRootStack rank]
  exact quittingOpponentSurvivalWeight_literalRootStackProfile_eq
    reward (zeno.newWord rank) (zeno.baseSourceProfile rank) who

/-- The comparison descendant's Bellman joint clock through the common new
word is the source record's literal joint-survival coordinate. -/
theorem sourceJointSurvivalWeight_eq_newWord (rank : ℕ) :
    quittingJointSurvivalWeight
        (quittingProfileLiveRoot reward (zeno.sourceProfile rank)) 0
        (zeno.newWord rank).length =
      quittingLiteralRootStackJointSurvival (zeno.newWord rank) := by
  rw [zeno.sourceProfile_eq_literalRootStack rank]
  exact quittingJointSurvivalWeight_literalRootStackProfile_eq
    reward (zeno.newWord rank) (zeno.baseSourceProfile rank)

/-- Full screening of the complete actual word also makes the joint survival
of the newly adjoined common word vanish. -/
theorem newWord_jointSurvival_tendsto_zero
    (hscreened : IsFinFourActualZenoFullyScreened zeno) :
    Tendsto (fun rank ↦
      quittingLiteralRootStackJointSurvival (zeno.newWord rank))
        atTop (nhds 0) := by
  have hopponent := zeno.newWord_fullyScreened hscreened (0 : Fin 4)
  apply squeeze_zero'
    (g := fun rank ↦ quittingLiteralRootStackOpponentSurvival
      (zeno.newWord rank) (0 : Fin 4))
  · exact Eventually.of_forall fun rank ↦
      quittingLiteralRootStackJointSurvival_nonneg (zeno.newWord rank)
  · filter_upwards [] with rank
    rw [quittingLiteralRootStackJointSurvival_eq_opponent_mul_own
      (zeno.newWord rank) (0 : Fin 4)]
    exact mul_le_of_le_one_right
      (quittingLiteralRootStackOpponentSurvival_nonneg
        (zeno.newWord rank) (0 : Fin 4))
      (quittingLiteralRootStackOwnSurvival_le_one
        (zeno.newWord rank) (0 : Fin 4))
  · exact hopponent

/-- Literal prescribed-payoff common-prefix bound for one coordinate. -/
theorem abs_sibling_terminalPayoff_sub_le
    (R : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (rank : ℕ) (who : Fin 4) :
    |quittingTerminalPayoff reward (zeno.profile rank) who -
        quittingTerminalPayoff reward (zeno.sourceProfile rank) who| ≤
      2 * R * quittingLiteralRootStackJointSurvival (zeno.newWord rank) := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  have hbound := abs_quittingRootSequenceTerminalValue_sub_le_of_prefix_eq
    reward (quittingProfileLiveRoot reward (zeno.profile rank))
      (quittingProfileLiveRoot reward (zeno.sourceProfile rank)) who
      (zeno.newWord rank).length hreward
      (zeno.sibling_liveRoot_eq_of_lt_newWord_length rank)
  rw [zeno.sourceJointSurvivalWeight_eq_newWord rank] at hbound
  exact hbound

/-- Literal unrestricted behavioral best-response common-prefix bound for
one coordinate. -/
theorem abs_sibling_bestResponseValue_sub_le
    (R : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (rank : ℕ) (who : Fin 4) :
    |quittingContinuationBestResponseValue reward (zeno.profile rank) who -
        quittingContinuationBestResponseValue reward
          (zeno.sourceProfile rank) who| ≤
      2 * R *
        quittingLiteralRootStackOpponentSurvival (zeno.newWord rank) who := by
  rw [quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot,
    quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot]
  have hbound := abs_quittingRootSequenceBestResponseValue_sub_le_of_prefix_eq
    reward (quittingProfileLiveRoot reward (zeno.profile rank))
      (quittingProfileLiveRoot reward (zeno.sourceProfile rank)) who
      (zeno.newWord rank).length hreward
      (zeno.sibling_liveRoot_eq_of_lt_newWord_length rank)
  rw [zeno.sourceOpponentSurvivalWeight_eq_newWord rank who] at hbound
  exact hbound

/-- Literal terminal-law common-prefix bound for every complete outcome,
including `Never`. -/
theorem abs_sibling_terminalOutcomeMass_sub_le
    (rank : ℕ) (outcome : QuittingTerminalOutcome (Fin 4)) :
    |quittingTerminalOutcomeMass reward (zeno.profile rank) outcome -
        quittingTerminalOutcomeMass reward (zeno.sourceProfile rank) outcome| ≤
      quittingLiteralRootStackJointSurvival (zeno.newWord rank) := by
  rw [zeno.profile_eq_literalRootStack rank,
    zeno.sourceProfile_eq_literalRootStack rank,
    quittingTerminalOutcomeMass_literalRootStack_sub_eq, abs_mul,
    abs_of_nonneg
      (quittingLiteralRootStackJointSurvival_nonneg (zeno.newWord rank))]
  have htarget0 :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward
      (zeno.baseProfile rank)).1 outcome
  have hsource0 :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward
      (zeno.baseSourceProfile rank)).1 outcome
  have htarget1 := terminalOutcomeMass_le_one
    (quittingTerminalOutcomeMass reward (zeno.baseProfile rank))
    (quittingTerminalOutcomeMass_mem_stdSimplex reward
      (zeno.baseProfile rank)) outcome
  have hsource1 := terminalOutcomeMass_le_one
    (quittingTerminalOutcomeMass reward (zeno.baseSourceProfile rank))
    (quittingTerminalOutcomeMass_mem_stdSimplex reward
      (zeno.baseSourceProfile rank)) outcome
  have hdiff : |quittingTerminalOutcomeMass reward
        (zeno.baseProfile rank) outcome -
      quittingTerminalOutcomeMass reward
        (zeno.baseSourceProfile rank) outcome| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiff
    (quittingLiteralRootStackJointSurvival_nonneg (zeno.newWord rank))

/-- Fully screened actual siblings have coalescing prescribed-payoff
coordinates. -/
theorem sibling_terminalPayoff_sub_tendsto_zero
    (hscreened : IsFinFourActualZenoFullyScreened zeno)
    (R : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (who : Fin 4) :
    Tendsto (fun rank ↦
      quittingTerminalPayoff reward (zeno.profile rank) who -
        quittingTerminalPayoff reward (zeno.sourceProfile rank) who)
      atTop (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero'
  · exact Eventually.of_forall fun rank ↦ abs_nonneg _
  · exact Eventually.of_forall fun rank ↦
      zeno.abs_sibling_terminalPayoff_sub_le R hreward rank who
  · simpa using
      (zeno.newWord_jointSurvival_tendsto_zero hscreened).const_mul (2 * R)

/-- Fully screened actual siblings have coalescing unrestricted behavioral
best-response cap coordinates. -/
theorem sibling_bestResponseValue_sub_tendsto_zero
    (hscreened : IsFinFourActualZenoFullyScreened zeno)
    (R : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (who : Fin 4) :
    Tendsto (fun rank ↦
      quittingContinuationBestResponseValue reward (zeno.profile rank) who -
        quittingContinuationBestResponseValue reward
          (zeno.sourceProfile rank) who) atTop (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero'
  · exact Eventually.of_forall fun rank ↦ abs_nonneg _
  · exact Eventually.of_forall fun rank ↦
      zeno.abs_sibling_bestResponseValue_sub_le R hreward rank who
  · simpa using
      (zeno.newWord_fullyScreened hscreened who).const_mul (2 * R)

/-- Fully screened actual siblings have coalescing complete terminal-law
coordinates, including the `Never` coordinate. -/
theorem sibling_terminalOutcomeMass_sub_tendsto_zero
    (hscreened : IsFinFourActualZenoFullyScreened zeno)
    (outcome : QuittingTerminalOutcome (Fin 4)) :
    Tendsto (fun rank ↦
      quittingTerminalOutcomeMass reward (zeno.profile rank) outcome -
        quittingTerminalOutcomeMass reward
          (zeno.sourceProfile rank) outcome) atTop (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero'
  · exact Eventually.of_forall fun rank ↦ abs_nonneg _
  · exact Eventually.of_forall fun rank ↦
      zeno.abs_sibling_terminalOutcomeMass_sub_le rank outcome
  · exact zeno.newWord_jointSurvival_tendsto_zero hscreened

/-- Product form of all three componentwise coalescence statements.  This
packages only conclusions already obtained from the same actual source. -/
theorem fullyScreened_sibling_semanticLaw_coalescence
    (hscreened : IsFinFourActualZenoFullyScreened zeno)
    (R : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ R) :
    (∀ who, Tendsto (fun rank ↦
      quittingTerminalPayoff reward (zeno.profile rank) who -
        quittingTerminalPayoff reward (zeno.sourceProfile rank) who)
      atTop (nhds 0)) ∧
    (∀ who, Tendsto (fun rank ↦
      quittingContinuationBestResponseValue reward (zeno.profile rank) who -
        quittingContinuationBestResponseValue reward
          (zeno.sourceProfile rank) who) atTop (nhds 0)) ∧
    (∀ outcome, Tendsto (fun rank ↦
      quittingTerminalOutcomeMass reward (zeno.profile rank) outcome -
        quittingTerminalOutcomeMass reward
          (zeno.sourceProfile rank) outcome) atTop (nhds 0)) := by
  exact ⟨zeno.sibling_terminalPayoff_sub_tendsto_zero hscreened R hreward,
    zeno.sibling_bestResponseValue_sub_tendsto_zero hscreened R hreward,
    zeno.sibling_terminalOutcomeMass_sub_tendsto_zero hscreened⟩

/-- Branch-local package retaining both the full-screening certificate needed
for sibling coalescence and the clearing family produced from that same actual
Zeno source. -/
structure FullyScreenedCoalescingClearingFamily (R : ℝ) where
  screened : IsFinFourActualZenoFullyScreened zeno
  clearing : zeno.FullyScreenedClearingFamily R

namespace FullyScreenedCoalescingClearingFamily

variable {zeno : FinFourActualZenoDeletedSurvivalSource data} {R : ℝ}

/-- The packaged screened branch retains all three sibling-coalescence
conclusions on the same actual Zeno source used by finite clearing. -/
theorem semanticLaw_coalescence
    (family : zeno.FullyScreenedCoalescingClearingFamily R)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R) :
    (∀ who, Tendsto (fun rank ↦
      quittingTerminalPayoff reward (zeno.profile rank) who -
        quittingTerminalPayoff reward (zeno.sourceProfile rank) who)
      atTop (nhds 0)) ∧
    (∀ who, Tendsto (fun rank ↦
      quittingContinuationBestResponseValue reward (zeno.profile rank) who -
        quittingContinuationBestResponseValue reward
          (zeno.sourceProfile rank) who) atTop (nhds 0)) ∧
    (∀ outcome, Tendsto (fun rank ↦
      quittingTerminalOutcomeMass reward (zeno.profile rank) outcome -
        quittingTerminalOutcomeMass reward
          (zeno.sourceProfile rank) outcome) atTop (nhds 0)) := by
  exact zeno.fullyScreened_sibling_semanticLaw_coalescence
    (FullyScreenedCoalescingClearingFamily.screened family) R hreward

end FullyScreenedCoalescingClearingFamily

end FinFourActualZenoDeletedSurvivalSource

namespace FinFourNormalizedInertVanishingDensityBoundary

/-- One-shot source-facing contraction.  The positive-host branch retains its
fixed endpoint.  The fully screened branch retains, on the same actual Zeno
source, both the screening proof that yields sibling semantic-law coalescence
and the finite-clearing family with its existing branch-local consumer.

No near-minimality or consumer is asserted for the positive-host endpoint. -/
theorem nonempty_actualZeno_fixedEndpoint_or_coalescingClearingFamily
    (data : FinFourNormalizedInertVanishingDensityBoundary packet)
    (hzero : data.boundary.limit.markedMass = 0)
    (R : ℝ) (hR : 0 < R)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R) :
    ∃ zeno : FinFourActualZenoDeletedSurvivalSource data,
      ((∃ positive : FinFourActualZenoPositiveHost zeno,
        Nonempty positive.FixedEndpoint) ∨
        Nonempty (zeno.FullyScreenedCoalescingClearingFamily R)) := by
  obtain ⟨zeno⟩ := data.nonempty_actualZenoDeletedSurvivalSource hzero
  refine ⟨zeno, ?_⟩
  rcases zeno.nonempty_fixedEndpoint_or_fullyScreened with
      hpositive | hscreened
  · exact Or.inl hpositive
  · exact Or.inr ⟨{
      screened := hscreened
      clearing := Classical.choice
        (zeno.nonempty_fullyScreenedClearingFamily
          hscreened R hR hreward) }⟩

end FinFourNormalizedInertVanishingDensityBoundary

end GameTheory
