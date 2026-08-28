/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinitePrefixClockClearing
import Research.Quitting.FinFourProducerAtlas.CanonicalPairMinimumEndpointSupportRankHandoff
import Research.Quitting.FinFourProducerAtlas.StrictRayTailNormalizedCapFlow
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# The finite normal form of an eventual all-Continue maximal ray

The generic first part says that one date at which the fixed opponents surely
stop makes every later deterministic stopping time equivalent to `Never`.
Consequently the unrestricted behavioral cap is attained in a finite list.

The Fin4 part applies this to the actual pure pair retained by the maximal-ray
source.  It also records the exact endpoint debt ledger.  Minimum debt gives
only a lower bound on the signed spectator leakage.  This file deliberately
does not assume or produce the missing upper bound, a debt descent, or a
renewable source.  The zero-minimum regression currently in the repository
uses a different explicit reward table from the packet motivating this file.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Set
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## A generic finite opponent barrier -/

/-- Two unilateral hazard sequences which agree through a date at which the
fixed opponents surely stop have the same terminal value.  What either
deviation does after the barrier is irrelevant. -/
theorem quittingRootSequenceHazardTerminalValue_eq_of_eq_le_of_opponentBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (first second : ℕ → PMF Bool) (start fuel : ℕ)
    (hagree : ∀ offset, offset ≤ fuel →
      first (start + offset) = second (start + offset))
    (hbarrier : quittingFixedOpponentsContinueMass roots who
      (start + fuel) = 0) :
    quittingRootSequenceHazardTerminalValue reward roots who first start =
      quittingRootSequenceHazardTerminalValue reward roots who second start := by
  induction fuel generalizing start with
  | zero =>
      have hzero := hagree 0 (by omega)
      simp only [Nat.add_zero] at hzero hbarrier
      calc
        quittingRootSequenceHazardTerminalValue reward roots who first start =
            (first start true).toReal *
                quittingFixedOpponentsQuitValue reward roots who start +
              (first start false).toReal *
                (quittingFixedOpponentsContinueReward reward roots who start +
                  quittingFixedOpponentsContinueMass roots who start *
                    quittingRootSequenceHazardTerminalValue reward roots who
                      first (start + 1)) :=
          quittingRootSequenceHazardTerminalValue_eq_hazardBellman
            reward roots who first start
        _ = quittingRootSequenceHazardTerminalValue reward roots who second
              start := by
          calc
            _ = (first start true).toReal *
                  quittingFixedOpponentsQuitValue reward roots who start +
                (first start false).toReal *
                  quittingFixedOpponentsContinueReward reward roots who
                    start := by rw [hbarrier]; ring
            _ = (second start true).toReal *
                  quittingFixedOpponentsQuitValue reward roots who start +
                (second start false).toReal *
                  quittingFixedOpponentsContinueReward reward roots who
                    start := by rw [hzero]
            _ = _ := by
              rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
                hbarrier]
              ring
  | succ fuel ih =>
      have hzero := hagree 0 (by omega)
      simp only [Nat.add_zero] at hzero
      have htail : ∀ offset, offset ≤ fuel →
          first (start + 1 + offset) = second (start + 1 + offset) := by
        intro offset hoffset
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hagree (offset + 1) (Nat.succ_le_succ hoffset)
      have htailBarrier : quittingFixedOpponentsContinueMass roots who
          (start + 1 + fuel) = 0 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbarrier
      have hinduction := ih (start + 1) htail htailBarrier
      calc
        quittingRootSequenceHazardTerminalValue reward roots who first start =
            (first start true).toReal *
                quittingFixedOpponentsQuitValue reward roots who start +
              (first start false).toReal *
                (quittingFixedOpponentsContinueReward reward roots who start +
                  quittingFixedOpponentsContinueMass roots who start *
                    quittingRootSequenceHazardTerminalValue reward roots who
                      first (start + 1)) :=
          quittingRootSequenceHazardTerminalValue_eq_hazardBellman
            reward roots who first start
        _ = (second start true).toReal *
                quittingFixedOpponentsQuitValue reward roots who start +
              (second start false).toReal *
                (quittingFixedOpponentsContinueReward reward roots who start +
                  quittingFixedOpponentsContinueMass roots who start *
                    quittingRootSequenceHazardTerminalValue reward roots who
                      second (start + 1)) := by rw [hzero, hinduction]
        _ = quittingRootSequenceHazardTerminalValue reward roots who second
              start :=
          (quittingRootSequenceHazardTerminalValue_eq_hazardBellman
            reward roots who second start).symm

/-- A deterministic stop strictly behind a finite opponent barrier has the
same value as never stopping. -/
theorem quittingRootSequencePureTimeTerminalValue_some_eq_none_of_barrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff time : ℕ)
    (hcutoff : cutoff < time)
    (hbarrier : quittingFixedOpponentsContinueMass roots who cutoff = 0) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some time) 0 =
      quittingRootSequencePureTimeTerminalValue reward roots who none 0 := by
  unfold quittingRootSequencePureTimeTerminalValue
  apply quittingRootSequenceHazardTerminalValue_eq_of_eq_le_of_opponentBarrier
    reward roots who _ _ 0 cutoff
  · intro offset hoffset
    have hne : offset ≠ time := by omega
    simp [hne]
  · simpa using hbarrier

/-- The exact finite best-response statistic before an opponent barrier. -/
def quittingFiniteOpponentBarrierBestResponseValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) : ℝ :=
  max (quittingRootSequencePureTimeTerminalValue reward roots who none 0)
    (Finset.univ.sup' (Finset.univ_nonempty :
      (Finset.univ : Finset (Fin (cutoff + 1))).Nonempty)
      (fun time ↦ quittingRootSequencePureTimeTerminalValue reward roots who
        (some time.val) 0))

/-- At a finite opponent barrier, the supremum over all deterministic stop
times and `Never` is the displayed finite maximum. -/
theorem sSup_range_quittingRootSequencePureTimeTerminalValue_eq_barrierBest
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ)
    (hbarrier : quittingFixedOpponentsContinueMass roots who cutoff = 0) :
    sSup (Set.range fun quitTime : Option ℕ ↦
      quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0) =
      quittingFiniteOpponentBarrierBestResponseValue
        reward roots who cutoff := by
  let values : Set ℝ := Set.range fun quitTime : Option ℕ ↦
    quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0
  have hbdd : BddAbove values :=
    bddAbove_range_quittingRootSequencePureTimeTerminalValue reward roots who
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨none, rfl⟩⟩
    · rintro _ ⟨quitTime, rfl⟩
      cases quitTime with
      | none => exact le_max_left _ _
      | some time =>
          by_cases htime : time ≤ cutoff
          · have hmem : (⟨time, by omega⟩ : Fin (cutoff + 1)) ∈
                (Finset.univ : Finset (Fin (cutoff + 1))) :=
              Finset.mem_univ _
            exact (Finset.le_sup'
              (fun phase : Fin (cutoff + 1) ↦
                quittingRootSequencePureTimeTerminalValue reward roots who
                  (some phase.val) 0) hmem).trans (le_max_right _ _)
          · change quittingRootSequencePureTimeTerminalValue reward roots who
                (some time) 0 ≤ _
            rw [quittingRootSequencePureTimeTerminalValue_some_eq_none_of_barrier
              reward roots who cutoff time (by omega) hbarrier]
            exact le_max_left _ _
  · apply max_le
    · exact le_csSup hbdd ⟨none, rfl⟩
    · apply Finset.sup'_le
      intro time _
      exact le_csSup hbdd ⟨some time.val, rfl⟩

/-- A finite opponent barrier makes the pure-time supremum attain its value
at `Never` or at one literal date no later than the barrier. -/
theorem exists_quittingRootSequencePureTimeTerminalValue_eq_sSup_of_barrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ)
    (hbarrier : quittingFixedOpponentsContinueMass roots who cutoff = 0) :
    ∃ quitTime : Option ℕ,
      quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0 =
        sSup (Set.range fun choice : Option ℕ ↦
          quittingRootSequencePureTimeTerminalValue reward roots who choice 0) := by
  let finiteBest := Finset.univ.sup' (Finset.univ_nonempty :
    (Finset.univ : Finset (Fin (cutoff + 1))).Nonempty)
    (fun time ↦ quittingRootSequencePureTimeTerminalValue reward roots who
      (some time.val) 0)
  let never := quittingRootSequencePureTimeTerminalValue reward roots who none 0
  have hsup := sSup_range_quittingRootSequencePureTimeTerminalValue_eq_barrierBest
    reward roots who cutoff hbarrier
  by_cases hfinite : finiteBest ≤ never
  · refine ⟨none, ?_⟩
    rw [hsup]
    simp only [quittingFiniteOpponentBarrierBestResponseValue]
    change never = max never finiteBest
    exact (max_eq_left hfinite).symm
  · obtain ⟨time, _htime, htime⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun phase : Fin (cutoff + 1) ↦
          quittingRootSequencePureTimeTerminalValue reward roots who
            (some phase.val) 0)
    refine ⟨some time.val, ?_⟩
    rw [hsup]
    simp only [quittingFiniteOpponentBarrierBestResponseValue]
    change _ = max never finiteBest
    rw [← htime]
    exact (max_eq_right (le_of_not_ge hfinite)).symm

/-- The actual unrestricted behavioral cap is attained whenever the fixed
opponents have a finite sure-stop barrier. -/
theorem exists_quittingContinuationBestResponseValue_eq_pureTime_of_barrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (cutoff : ℕ)
    (hbarrier : quittingFixedOpponentsContinueMass
      (quittingProfileLiveRoot reward profile) who cutoff = 0) :
    ∃ quitTime : Option ℕ,
      quittingContinuationBestResponseValue reward profile who =
        quittingPureTimeDeviationPayoff reward profile who quitTime := by
  obtain ⟨quitTime, htime⟩ :=
    exists_quittingRootSequencePureTimeTerminalValue_eq_sSup_of_barrier
      reward (quittingProfileLiveRoot reward profile) who cutoff hbarrier
  refine ⟨quitTime, ?_⟩
  rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  have hfunction : quittingPureTimeDeviationPayoff reward profile who =
      fun choice ↦ quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward profile) who choice 0 := by
    funext choice
    unfold quittingPureTimeDeviationPayoff
    exact quittingTerminalPayoff_update_pureTimeBehaviorStrategy
      reward profile who choice
  rw [hfunction]
  exact htime.symm

/-! ## The actual Fin4 eventual-stall normal form -/

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {returnSource :
  FinFourOwnerCompressedMinimumReturnForcedPairSource source}
variable {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

variable (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda)

/-- Every displayed ray profile retains the source's pure pair at its marked
date, independently of which maximal roots occur in the copied outer word. -/
theorem rayProfile_markedRoot_eq_pureSet (index : ℕ) :
    quittingProfileLiveRoot reward (packet.rayFamily.rayProfiles index) index =
      quittingPureSetRoot packet.rayTerminal.val := by
  rw [packet.rayFamily.rayProfiles_markedRoot_eq]
  change quittingProfileLiveRoot reward (packet.rayBaseProfile index) 0 = _
  rw [rayBaseProfile, quittingProfileLiveRoot_rootThenContinuation_zero]

/-- Every ray profile has a finite opponent barrier at its own marked pair. -/
theorem rayProfile_opponentBarrier (index : ℕ) (who : Fin 4) :
    quittingFixedOpponentsContinueMass
        (quittingProfileLiveRoot reward (packet.rayFamily.rayProfiles index))
        who index = 0 := by
  obtain ⟨other, hotherMem, hotherNe⟩ :
      ∃ other ∈ packet.rayTerminal.val, other ≠ who := by
    apply Finset.exists_mem_ne
    rw [rayTerminal, packet.movingTerminal_card]
    norm_num
  have herase : (packet.rayTerminal.val.erase who).Nonempty :=
    ⟨other, Finset.mem_erase.mpr ⟨hotherNe, hotherMem⟩⟩
  have hmass :=
    quittingStationaryFixedOpponentsContinueMass_pureSetRoot_of_erase_nonempty
      herase
  calc
    quittingFixedOpponentsContinueMass
          (quittingProfileLiveRoot reward (packet.rayFamily.rayProfiles index))
          who index =
        quittingStationaryFixedOpponentsContinueMass
          (quittingProfileLiveRoot reward
            (packet.rayFamily.rayProfiles index) index) who :=
      (quittingStationaryFixedOpponentsContinueMass_apply
        (quittingProfileLiveRoot reward (packet.rayFamily.rayProfiles index))
          who index).symm
    _ = quittingStationaryFixedOpponentsContinueMass
          (quittingPureSetRoot packet.rayTerminal.val) who := by
      rw [packet.rayProfile_markedRoot_eq_pureSet]
    _ = 0 := hmass

/-- Every actual ray profile, not only a fixed one, has an attained
unrestricted behavioral cap for every player. -/
theorem exists_rayProfile_capAttainer (index : ℕ) (who : Fin 4) :
    ∃ quitTime : Option ℕ,
      quittingContinuationBestResponseValue reward
          (packet.rayFamily.rayProfiles index) who =
        quittingPureTimeDeviationPayoff reward
          (packet.rayFamily.rayProfiles index) who quitTime :=
  exists_quittingContinuationBestResponseValue_eq_pureTime_of_barrier
    reward (packet.rayFamily.rayProfiles index) who index
      (packet.rayProfile_opponentBarrier index who)

namespace FinFourMaximalRayEventualAllContinue

/-- The one actual finite-clock profile retained at the fixation date. -/
def fixedProfile (stall : FinFourMaximalRayEventualAllContinue packet) :
    (quittingGame reward).BehaviorProfile :=
  packet.rayFamily.rayProfiles stall.cutoff

/-- The retained profile realizes the fixed semantic-ray state without a new
compactness choice or source reselection. -/
theorem fixedProfile_semantic_eq
    (stall : FinFourMaximalRayEventualAllContinue packet) :
    quittingTerminalSemanticPair reward stall.fixedProfile =
      quittingMaximalCapSemanticPrefixOrbit reward packet.raySource
        stall.cutoff :=
  packet.rayFamily.rayProfiles_semantic_eq stall.cutoff

/-- The public source-level form of literal semantic fixation. -/
theorem rayPair_eq_fixedProfile
    (stall : FinFourMaximalRayEventualAllContinue packet) (offset : ℕ) :
    quittingMaximalCapSemanticPrefixOrbit reward packet.raySource
        (stall.cutoff + offset) =
      quittingTerminalSemanticPair reward stall.fixedProfile := by
  have hpair := stall.pair_eq offset
  change quittingMaximalCapSemanticPrefixOrbit reward packet.raySource
      (stall.cutoff + offset) =
    quittingMaximalCapSemanticPrefixOrbit reward packet.raySource stall.cutoff
      at hpair
  rw [hpair, ← stall.fixedProfile_semantic_eq]

/-- All Continue is the unique exact root against the actual fixed profile's
unrestricted behavioral cap. -/
theorem fixedProfile_unique_exactRoot
    (stall : FinFourMaximalRayEventualAllContinue packet)
    (candidate : Fin 4 → PMF Bool)
    (hcandidate : IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward stall.fixedProfile).2 0 candidate) :
    candidate = (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
  apply stall.unique_exactRoot candidate
  rw [stall.fixedProfile_semantic_eq] at hcandidate
  exact hcandidate

/-- The fixed profile has the original pure pair at the retained marked date. -/
theorem fixedProfile_markedRoot_eq
    (stall : FinFourMaximalRayEventualAllContinue packet) :
    quittingProfileLiveRoot reward stall.fixedProfile stall.cutoff =
      quittingPureSetRoot packet.rayTerminal.val :=
  packet.rayProfile_markedRoot_eq_pureSet stall.cutoff

/-- Every unilateral deviation faces another sure quitter at the marked pure
pair, so the marked date is a literal opponent barrier. -/
theorem fixedProfile_opponentBarrier
    (stall : FinFourMaximalRayEventualAllContinue packet) (who : Fin 4) :
    quittingFixedOpponentsContinueMass
        (quittingProfileLiveRoot reward stall.fixedProfile) who stall.cutoff =
      0 :=
  packet.rayProfile_opponentBarrier stall.cutoff who

/-- Every unrestricted behavioral cap of the actual fixed profile is attained
by `Never` or by a deterministic quitting date no later than the pure pair. -/
theorem exists_fixedProfile_capAttainer
    (stall : FinFourMaximalRayEventualAllContinue packet) (who : Fin 4) :
    ∃ quitTime : Option ℕ,
      quittingContinuationBestResponseValue reward stall.fixedProfile who =
        quittingPureTimeDeviationPayoff reward stall.fixedProfile who quitTime :=
  packet.exists_rayProfile_capAttainer stall.cutoff who

/-- Literal fixation identifies the debt of the retained actual profile with
the strict ray's limiting debt. -/
theorem fixedProfile_debt_eq_rayLimit
    (stall : FinFourMaximalRayEventualAllContinue packet) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward stall.fixedProfile) =
      packet.rayLimit := by
  let debtAt := fun index ↦ quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward
      (packet.rayFamily.rayProfiles index))
  have heventually : ∀ᶠ index in atTop, debtAt index = debtAt stall.cutoff := by
    filter_upwards [eventually_ge_atTop stall.cutoff] with index hindex
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hindex
    dsimp only [debtAt]
    have hpair := stall.pair_eq offset
    change quittingMaximalCapSemanticPrefixOrbit reward packet.raySource
        (stall.cutoff + offset) =
      quittingMaximalCapSemanticPrefixOrbit reward packet.raySource
        stall.cutoff at hpair
    rw [packet.rayFamily.rayProfiles_semantic_eq,
      packet.rayFamily.rayProfiles_semantic_eq, hpair]
  have hconstant : Tendsto debtAt atTop (nhds (debtAt stall.cutoff)) :=
    tendsto_const_nhds.congr' (heventually.mono fun _ hvalue ↦ hvalue.symm)
  have hlimit : Tendsto debtAt atTop (nhds packet.rayLimit) := by
    simpa only [debtAt] using packet.rayProfiles_wholeDebt_tendsto
  exact (tendsto_nhds_unique hlimit hconstant).symm

/-- The fixed actual state remains strictly above the same positive global
minimum carried by the source. -/
theorem minimumDebt_lt_fixedProfile_debt
    (stall : FinFourMaximalRayEventualAllContinue packet) :
    quittingTerminalSemanticDebtSum source.point.1 <
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward stall.fixedProfile) := by
  rw [stall.fixedProfile_debt_eq_rayLimit]
  simpa only [rayLimit] using stall.strict.stall.strict

/-- The entire signed debt change outside the paid mover. -/
def spectatorLeakage
    (stall : FinFourMaximalRayEventualAllContinue packet) : ℝ :=
  ∑ who ∈ Finset.univ.erase packet.payer,
    (quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (packet.rayPaidTargetProfile stall.cutoff)) who -
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward stall.fixedProfile) who)

/-- The endpoint removes exactly the paid mover's debt.  Every other debt
change is localized in `spectatorLeakage`. -/
theorem fixedProfile_endpoint_debt_eq_sub_add_spectatorLeakage
    (stall : FinFourMaximalRayEventualAllContinue packet) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (packet.rayPaidTargetProfile stall.cutoff)) =
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward stall.fixedProfile) -
        packet.rayPaidGain stall.cutoff + stall.spectatorLeakage := by
  have hpayerSource := packet.rayProfile_payerDebt_eq_rayPaidGain stall.cutoff
  have hpayerTarget :=
    packet.rayPaidTargetProfile_payerDebt_eq_zero stall.cutoff
  unfold quittingTerminalSemanticDebtSum spectatorLeakage fixedProfile at *
  have htargetSplit :
      (∑ who, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (packet.rayPaidTargetProfile stall.cutoff)) who) =
        (∑ who ∈ Finset.univ.erase packet.payer,
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (packet.rayPaidTargetProfile stall.cutoff)) who) +
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (packet.rayPaidTargetProfile stall.cutoff)) packet.payer :=
    (Finset.sum_erase_add (s := Finset.univ)
      (f := fun who ↦ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (packet.rayPaidTargetProfile stall.cutoff)) who)
      (Finset.mem_univ packet.payer)).symm
  have hsourceSplit :
      (∑ who, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (packet.rayFamily.rayProfiles stall.cutoff)) who) =
        (∑ who ∈ Finset.univ.erase packet.payer,
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (packet.rayFamily.rayProfiles stall.cutoff)) who) +
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (packet.rayFamily.rayProfiles stall.cutoff)) packet.payer :=
    (Finset.sum_erase_add (s := Finset.univ)
      (f := fun who ↦ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (packet.rayFamily.rayProfiles stall.cutoff)) who)
      (Finset.mem_univ packet.payer)).symm
  rw [htargetSplit, hsourceSplit, Finset.sum_sub_distrib,
    hpayerSource, hpayerTarget]
  ring

/-- Global minimum debt gives the exact lower bound on spectator leakage.
The inequality points away from the upper estimate needed for descent. -/
theorem rayPaidGain_sub_fixedExcess_le_spectatorLeakage
    (stall : FinFourMaximalRayEventualAllContinue packet) :
    packet.rayPaidGain stall.cutoff -
          (quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward stall.fixedProfile) -
            quittingTerminalSemanticDebtSum source.point.1) ≤
      stall.spectatorLeakage := by
  have hminimum := source.minimum
    (quittingTerminalSemanticPair reward
      (packet.rayPaidTargetProfile stall.cutoff))
    (quittingTerminalSemanticPair_mem_carrier reward _)
  have hledger :=
    stall.fixedProfile_endpoint_debt_eq_sub_add_spectatorLeakage
  linarith

/-- A strict endpoint descent estimate on the spectator leakage is impossible:
it would put an actual endpoint below the global minimum. -/
theorem not_spectatorLeakage_lt_rayPaidGain_sub_fixedExcess
    (stall : FinFourMaximalRayEventualAllContinue packet) :
    ¬ stall.spectatorLeakage <
      packet.rayPaidGain stall.cutoff -
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward stall.fixedProfile) -
          quittingTerminalSemanticDebtSum source.point.1) :=
  not_lt_of_ge stall.rayPaidGain_sub_fixedExcess_le_spectatorLeakage

/-- A supplied nonlocal upper bound at the minimum threshold can only return
the endpoint to the minimum fibre.  This theorem does not produce that bound. -/
theorem endpoint_debt_eq_minimum_of_spectatorLeakage_le
    (stall : FinFourMaximalRayEventualAllContinue packet)
    (hupper : stall.spectatorLeakage ≤
      packet.rayPaidGain stall.cutoff -
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward stall.fixedProfile) -
          quittingTerminalSemanticDebtSum source.point.1)) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (packet.rayPaidTargetProfile stall.cutoff)) =
      quittingTerminalSemanticDebtSum source.point.1 := by
  have hlower := stall.rayPaidGain_sub_fixedExcess_le_spectatorLeakage
  have hledger :=
    stall.fixedProfile_endpoint_debt_eq_sub_add_spectatorLeakage
  linarith

/-- Packet-form lower bound, with the fixed profile debt rewritten as the
strict ray limit `L`. -/
theorem rayPaidGain_sub_rayLimitExcess_le_spectatorLeakage
    (stall : FinFourMaximalRayEventualAllContinue packet) :
    packet.rayPaidGain stall.cutoff -
          (packet.rayLimit - quittingTerminalSemanticDebtSum source.point.1) ≤
      stall.spectatorLeakage := by
  rw [← stall.fixedProfile_debt_eq_rayLimit]
  exact stall.rayPaidGain_sub_fixedExcess_le_spectatorLeakage

/-- The retained endpoint gain is strictly positive. -/
theorem fixedProfile_rayPaidGain_pos
    (stall : FinFourMaximalRayEventualAllContinue packet) :
    0 < packet.rayPaidGain stall.cutoff := by
  have hlower := packet.rayResolution_mul_minimumDebt_div_three_le_rayPaidGain
    stall.cutoff
  have hpositive : 0 < packet.rayResolution *
      quittingTerminalSemanticDebtSum source.point.1 / 3 := by
    exact div_pos
      (mul_pos packet.rayResolution_pos source.minimumDebt_pos) (by norm_num)
  exact hpositive.trans_le hlower

end FinFourMaximalRayEventualAllContinue

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
