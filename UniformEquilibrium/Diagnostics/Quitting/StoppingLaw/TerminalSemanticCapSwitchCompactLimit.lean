/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticCapSwitchSourceTransfer

/-!
# Escaping pair-deleted cap-switch clocks

If a supplied profile sequence has a uniform pair-deleted survival floor at
marks escaping to infinity, one strict subsequence of its complete stopping
laws has a simultaneous weak limit whose pair-deleted `Never` product retains
that floor.

The conclusion concerns the selected weak limit.  It is not an actual
cemetery atom of any source profile and asserts no terminal-semantic
continuity or finite-splice obstruction.
-/

noncomputable section

namespace GameTheory

open Filter MeasureTheory Set StochasticGame
open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open _root_.Math.Probability.DiscreteHazard
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Product of the inclusive finite tails of all players outside a deleted
mover/observer pair. -/
def quittingPairDeletedCompactStoppingLawSurvival
    (laws : ι → CompactStoppingLaw) (mover observer : ι) (cutoff : ℕ) : ℝ :=
  ∏ player ∈ (Finset.univ.erase mover).erase observer,
    StoppingLaw.survival (laws player).toPMF cutoff

/-- Product of the limiting `Never` atoms outside a deleted mover/observer
pair. -/
def quittingPairDeletedCompactStoppingLawNeverProduct
    (laws : ι → CompactStoppingLaw) (mover observer : ι) : ℝ :=
  ∏ player ∈ (Finset.univ.erase mover).erase observer,
    (laws player).realMass ({⊤} : Set CompactStoppingTime)

private theorem compactStoppingLaw_survival_tendsto
    {lawSeq : ℕ → CompactStoppingLaw} {law : CompactStoppingLaw}
    (hlaw : Tendsto lawSeq atTop (nhds law)) (cutoff : ℕ) :
    Tendsto (fun n ↦ StoppingLaw.survival (lawSeq n).toPMF cutoff)
      atTop (nhds (StoppingLaw.survival law.toPMF cutoff)) := by
  unfold StoppingLaw.survival StoppingLaw.finiteMass
  apply tendsto_const_nhds.sub
  exact tendsto_finsetSum (Finset.range cutoff) fun time _ ↦ by
    have hmass := CompactStoppingLaw.tendsto_realMass_of_isClopen hlaw
      (compactStoppingTime_finiteSingleton_isClopen time)
    change Tendsto
      (fun n ↦ ((lawSeq n).toPMF (time : CompactStoppingTime)).toReal)
      atTop (nhds ((law.toPMF (time : CompactStoppingTime)).toReal))
    simpa only [CompactStoppingLaw.toPMF_apply_toReal] using hmass

private theorem compactStoppingLaw_survival_tendsto_top
    (law : CompactStoppingLaw) :
    Tendsto (StoppingLaw.survival law.toPMF) atTop
      (nhds (law.realMass ({⊤} : Set CompactStoppingTime))) := by
  have hsurvival := StoppingLaw.tendsto_survival_none law.toPMF
  have htop : (law.toPMF none).toReal =
      law.realMass ({⊤} : Set CompactStoppingTime) := by
    change (law.toPMF (⊤ : CompactStoppingTime)).toReal = _
    exact CompactStoppingLaw.toPMF_apply_toReal law ⊤
  rw [← htop]
  exact hsurvival

theorem quittingPairDeletedCompactStoppingLawSurvival_tendsto
    {lawSeq : ℕ → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player, Tendsto (fun n ↦ lawSeq n player) atTop
      (nhds (laws player)))
    (mover observer : ι) (cutoff : ℕ) :
    Tendsto (fun n ↦ quittingPairDeletedCompactStoppingLawSurvival
        (lawSeq n) mover observer cutoff) atTop
      (nhds (quittingPairDeletedCompactStoppingLawSurvival
        laws mover observer cutoff)) := by
  unfold quittingPairDeletedCompactStoppingLawSurvival
  exact tendsto_finsetProd ((Finset.univ.erase mover).erase observer)
    fun player _ ↦ compactStoppingLaw_survival_tendsto (hlaw player) cutoff

theorem quittingPairDeletedCompactStoppingLawSurvival_tendsto_neverProduct
    (laws : ι → CompactStoppingLaw) (mover observer : ι) :
    Tendsto (fun cutoff ↦ quittingPairDeletedCompactStoppingLawSurvival
        laws mover observer cutoff) atTop
      (nhds (quittingPairDeletedCompactStoppingLawNeverProduct
        laws mover observer)) := by
  unfold quittingPairDeletedCompactStoppingLawSurvival
    quittingPairDeletedCompactStoppingLawNeverProduct
  exact tendsto_finsetProd ((Finset.univ.erase mover).erase observer)
    fun player _ ↦ compactStoppingLaw_survival_tendsto_top (laws player)

/-- The actual pair-deleted live clock of a profile is the finite inclusive
tail product of its extracted complete stopping laws. -/
theorem quittingPairDeletedSurvivalWeight_eq_compactStoppingLawSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hmoverObserver : mover ≠ observer) (cutoff : ℕ) :
    quittingPairDeletedSurvivalWeight
        (quittingProfileLiveRoot reward profile) mover observer 0 cutoff =
      quittingPairDeletedCompactStoppingLawSurvival
        (quittingCompactStoppingLawsOfProfile reward profile)
          mover observer cutoff := by
  unfold quittingPairDeletedSurvivalWeight
  rw [quittingOpponentSurvivalWeight_eq_prod_hazardSurvival]
  let players := Finset.univ.erase mover
  let factor := fun player ↦ quittingHazardSurvival
    (fun stage ↦ quittingRootSequenceUpdate
      (quittingProfileLiveRoot reward profile) observer
        quittingAlwaysContinueHazard stage player) cutoff
  have hobserverMem : observer ∈ players := by
    simp [players, Ne.symm hmoverObserver]
  have hobserverFactor : factor observer = 1 := by
    simp [factor, quittingRootSequenceUpdate, quittingAlwaysContinueHazard,
      quittingHazardSurvival_eq_prod]
  have hsplit := Finset.mul_prod_erase players factor hobserverMem
  rw [hobserverFactor, one_mul] at hsplit
  change (∏ player ∈ players, factor player) = _
  rw [← hsplit]
  unfold quittingPairDeletedCompactStoppingLawSurvival
  apply Finset.prod_congr rfl
  intro player hplayer
  have hobserver : player ≠ observer := Finset.ne_of_mem_erase hplayer
  have hbehavior :=
    stoppingLawSurvival_quittingBehaviorStoppingLaw reward (profile player) cutoff
  have hlaw :
      (quittingCompactStoppingLawsOfProfile reward profile player).toPMF =
        quittingBehaviorStoppingLaw reward (profile player) := by
    simp [quittingCompactStoppingLawsOfProfile]
  rw [hlaw]
  dsimp only [factor]
  simp only [quittingRootSequenceUpdate, Function.update_of_ne hobserver]
  change quittingHazardSurvival
      (quittingBehaviorLiveHazard reward (profile player)) cutoff = _
  exact hbehavior.symm

/-- Selected weak-law output of an escaping pair-deleted clock. -/
structure QuittingEscapingPairDeletedStoppingLawLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (floor : ℝ) where
  /-- One simultaneous compact-law limit. -/
  laws : ι → CompactStoppingLaw
  /-- The common strict subsequence. -/
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  law_tendsto : ∀ player, Tendsto (fun n ↦
    quittingCompactStoppingLawsOfProfile reward (profiles (subseq n)) player)
      atTop (nhds (laws player))
  /-- The selected limit retains the pair-deleted `Never` floor. -/
  floor_le_neverProduct : floor ≤
    quittingPairDeletedCompactStoppingLawNeverProduct laws mover observer

/-- **Escaping pair-deleted compactification.**  A uniform live-clock floor
at marks tending to infinity survives in one simultaneous weak limit as a
pair-deleted product of `Never` atoms. -/
theorem nonempty_quittingEscapingPairDeletedStoppingLawLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hmoverObserver : mover ≠ observer)
    (marks : ℕ → ℕ) (hmarks : Tendsto marks atTop atTop)
    (floor : ℝ)
    (hfloor : ∀ᶠ n in atTop, floor ≤ quittingPairDeletedSurvivalWeight
      (quittingProfileLiveRoot reward (profiles n))
        mover observer 0 (marks n)) :
    Nonempty (QuittingEscapingPairDeletedStoppingLawLimit reward profiles
      mover observer floor) := by
  obtain ⟨laws, subseq, hsubseq, hlaws⟩ :=
    exists_quittingCompactStoppingLawsOfProfile_tendsto_subseq reward profiles
  let lawSeq := fun n ↦
    quittingCompactStoppingLawsOfProfile reward (profiles (subseq n))
  have hmarksSubseq : Tendsto (fun n ↦ marks (subseq n)) atTop atTop :=
    hmarks.comp hsubseq.tendsto_atTop
  have hfloorSubseq : ∀ᶠ n in atTop,
      floor ≤ quittingPairDeletedSurvivalWeight
        (quittingProfileLiveRoot reward (profiles (subseq n)))
          mover observer 0 (marks (subseq n)) :=
    hsubseq.tendsto_atTop.eventually hfloor
  have hprefix (cutoff : ℕ) : floor ≤
      quittingPairDeletedCompactStoppingLawSurvival laws mover observer cutoff := by
    have hcutoff : ∀ᶠ n in atTop, cutoff ≤ marks (subseq n) :=
      (tendsto_atTop.1 hmarksSubseq cutoff)
    have hfinite : ∀ᶠ n in atTop, floor ≤
        quittingPairDeletedCompactStoppingLawSurvival
          (lawSeq n) mover observer cutoff := by
      filter_upwards [hcutoff, hfloorSubseq] with n hn hfloorN
      rw [← quittingPairDeletedSurvivalWeight_eq_compactStoppingLawSurvival
        reward (profiles (subseq n)) mover observer hmoverObserver cutoff]
      exact hfloorN.trans
        (antitone_quittingOpponentSurvivalWeight
          (quittingRootSequenceUpdate
            (quittingProfileLiveRoot reward (profiles (subseq n))) observer
              quittingAlwaysContinueHazard)
          mover 0 hn)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      (quittingPairDeletedCompactStoppingLawSurvival_tendsto
        (laws := laws) hlaws mover observer cutoff) hfinite
  have hnever : floor ≤
      quittingPairDeletedCompactStoppingLawNeverProduct laws mover observer := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      (quittingPairDeletedCompactStoppingLawSurvival_tendsto_neverProduct
        laws mover observer) (Filter.Eventually.of_forall hprefix)
  exact ⟨{
    laws := laws
    subseq := subseq
    subseq_strictMono := hsubseq
    law_tendsto := hlaws
    floor_le_neverProduct := hnever
  }⟩

/-- Reset-cube source specialization.  If a face has pair-deleted floor
`floor` and the total face scale is at most half that floor, the common
source sequence has an escaping weak-law limit with `Never` product at least
`floor / 2`. -/
theorem nonempty_quittingEscapingPairDeletedStoppingLawLimit_resetCubeSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (data : ℕ → QuittingStoppingLawResetCubeData reward)
    (face : ℕ → Finset ι) (mover observer : ι)
    (hmoverObserver : mover ≠ observer)
    (marks : ℕ → ℕ) (hmarks : Tendsto marks atTop atTop)
    (floor : ℝ)
    (hfaceFloor : ∀ᶠ n in atTop, floor ≤
      quittingPairDeletedSurvivalWeight
        (quittingProfileLiveRoot reward ((data n).profile (face n)))
          mover observer 0 (marks n))
    (hfaceScale : ∀ᶠ n in atTop,
      (∑ player ∈ face n, (data n).scale player) ≤ floor / 2) :
    Nonempty (QuittingEscapingPairDeletedStoppingLawLimit reward
      (fun n ↦ (data n).source) mover observer (floor / 2)) := by
  apply nonempty_quittingEscapingPairDeletedStoppingLawLimit
    reward (fun n ↦ (data n).source) mover observer hmoverObserver marks hmarks
      (floor / 2)
  filter_upwards [hfaceFloor, hfaceScale] with n hfaceFloorN hfaceScaleN
  have htransfer :=
    abs_quittingPairDeletedSurvivalWeight_resetCube_profile_sub_source_le
      (data n) (face n) mover observer (marks n)
  rw [abs_le] at htransfer
  linarith

end GameTheory
