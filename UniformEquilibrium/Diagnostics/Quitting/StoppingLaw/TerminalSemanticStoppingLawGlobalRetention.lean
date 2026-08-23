/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawMinimumTransfer

/-!
# Global terminal-law retention on a minimum stopping-law reset

The underlying stopping-law reset theorem retains one selected finite
coalition window.  Its proof is pointwise in the terminal coalition and time,
and the selected approximate best response does not depend on that window.
This module derives the stronger simultaneous conclusion.

One literal half reset:

* gains at least one quarter of the mover's source debt;
* decreases that debt by exactly the gain;
* transfers the gain to the opposite debt face up to the minimum error;
* obeys the full coordinatewise debt chord;
* has a terminal outcome law exactly halfway between the source and endpoint
  laws; and
* retains half of every finite chronological coalition window at once.

Thus choosing a marked atom does not consume the reset's ability to retain
the other hidden OR causes.  What remains for the cardinal reduction is to
extract a common quotient/table slot, not to diagonalize over windows.
-/


noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Players whose literal singleton terminal has positive mass at one actual
stage of a behavior profile. -/
def quittingPositiveSingletonStageSupport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) : Finset ι :=
  Finset.univ.filter fun owner ↦
    0 < quittingStageCoalitionMass reward profile time
      (quittingSingletonTerminal owner)

/-- Half-retention of every singleton row makes its positive incidence
support monotone. -/
theorem quittingPositiveSingletonStageSupport_mono_of_halfRetention
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (hretain : ∀ owner,
      (1 / 2) * quittingStageCoalitionMass reward source time
          (quittingSingletonTerminal owner) ≤
        quittingStageCoalitionMass reward target time
          (quittingSingletonTerminal owner)) :
    quittingPositiveSingletonStageSupport reward source time ⊆
      quittingPositiveSingletonStageSupport reward target time := by
  intro owner howner
  have hsource : 0 < quittingStageCoalitionMass reward source time
      (quittingSingletonTerminal owner) := by
    simpa [quittingPositiveSingletonStageSupport] using howner
  have hhalf : 0 < (1 / 2) * quittingStageCoalitionMass reward source time
      (quittingSingletonTerminal owner) := mul_pos (by norm_num) hsource
  have htarget : 0 < quittingStageCoalitionMass reward target time
      (quittingSingletonTerminal owner) :=
    hhalf.trans_le (hretain owner)
  simpa [quittingPositiveSingletonStageSupport] using htarget

/-- **Near-minimum half reset with simultaneous law/window retention.** -/
theorem exists_halfStoppingLawReset_nearMinimum_transfer_and_globalRetention
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (epsilon : ℝ)
    (hwhoDebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who)
    (hnear : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon) :
    ∃ bestResponse : (quittingGame reward).BehaviorStrategy who,
      let endpointProfile := Function.update profile who bestResponse
      let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
        reward who (profile who) bestResponse (1 / 2) (by norm_num) (by norm_num)
      let mixedProfile := Function.update profile who mixedStrategy
      let source := quittingTerminalSemanticPair reward profile
      let endpoint := quittingTerminalSemanticPair reward endpointProfile
      let target := quittingTerminalSemanticPair reward mixedProfile
      let gain := quittingTerminalPayoff reward mixedProfile who -
        quittingTerminalPayoff reward profile who
      target ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebt source who / 4 ≤ gain ∧
      0 < gain ∧
      quittingTerminalSemanticDebt target who =
        quittingTerminalSemanticDebt source who - gain ∧
      gain ≤ epsilon + ∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target other ∧
      (∀ observer,
        quittingTerminalSemanticDebt target observer ≤
          (1 / 2) * quittingTerminalSemanticDebt source observer +
            (1 / 2) * quittingTerminalSemanticDebt endpoint observer) ∧
      (∀ outcome,
        quittingTerminalOutcomeMass reward mixedProfile outcome =
          (1 / 2) * quittingTerminalOutcomeMass reward profile outcome +
            (1 / 2) *
              quittingTerminalOutcomeMass reward endpointProfile outcome) ∧
      (∀ terminal time,
        (1 / 2) * quittingStageCoalitionMass reward profile time terminal ≤
          quittingStageCoalitionMass reward mixedProfile time terminal) ∧
      ∀ terminal cutoff,
        (1 / 2) *
            (∑ time ∈ Finset.range cutoff,
              quittingStageCoalitionMass reward profile time terminal) ≤
          ∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward mixedProfile time terminal := by
  obtain ⟨bestResponse, htarget, hgainQuarter, hgainPos, hdecrease,
      htransfer, hchord, _hselectedWindow⟩ :=
    exists_halfStoppingLawReset_nearMinimum_transfer_and_windowRetention
      reward profile who (quittingSingletonTerminal who) 0 epsilon
        hwhoDebt hnear
  refine ⟨bestResponse, ?_⟩
  dsimp only
  let endpointProfile := Function.update profile who bestResponse
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
    reward who (profile who) bestResponse (1 / 2) (by norm_num) (by norm_num)
  let mixedProfile := Function.update profile who mixedStrategy
  let source := quittingTerminalSemanticPair reward profile
  let endpoint := quittingTerminalSemanticPair reward endpointProfile
  let target := quittingTerminalSemanticPair reward mixedProfile
  let gain := quittingTerminalPayoff reward mixedProfile who -
    quittingTerminalPayoff reward profile who
  have hlaw : ∀ outcome,
      quittingTerminalOutcomeMass reward mixedProfile outcome =
        (1 / 2) * quittingTerminalOutcomeMass reward profile outcome +
          (1 / 2) *
            quittingTerminalOutcomeMass reward endpointProfile outcome := by
    intro outcome
    dsimp only [mixedProfile, mixedStrategy, endpointProfile]
    have haffine := quittingTerminalOutcomeMass_stoppingLawMixture_eq
      reward profile who (profile who) bestResponse
        (1 / 2) (by norm_num) (by norm_num) outcome
    norm_num at haffine ⊢
    simpa only [Function.update_eq_self] using haffine
  have hpointwise : ∀ terminal time,
      (1 / 2) * quittingStageCoalitionMass reward profile time terminal ≤
        quittingStageCoalitionMass reward mixedProfile time terminal := by
    intro terminal time
    dsimp only [mixedProfile, mixedStrategy]
    have hrow := one_sub_mul_stageCoalitionMass_le_stoppingLawMixture
      reward profile who (profile who) bestResponse
        (1 / 2) (by norm_num) (by norm_num) time terminal
    norm_num at hrow ⊢
    simpa only [Function.update_eq_self] using hrow
  have hglobalWindow : ∀ terminal cutoff,
      (1 / 2) *
          (∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward profile time terminal) ≤
        ∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward mixedProfile time terminal := by
    intro terminal cutoff
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro time _
    exact hpointwise terminal time
  exact ⟨htarget, hgainQuarter, hgainPos, hdecrease, htransfer, hchord,
    hlaw, hpointwise, hglobalWindow⟩

/-- At an exact minimum, the global-retention reset has a positive recipient
on the opposite debt face while retaining every chronological window. -/
theorem exists_halfStoppingLawReset_minimum_positiveTransfer_globalRetention
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι)
    (hwhoDebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ bestResponse : (quittingGame reward).BehaviorStrategy who,
      let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
        reward who (profile who) bestResponse (1 / 2) (by norm_num) (by norm_num)
      let mixedProfile := Function.update profile who mixedStrategy
      let source := quittingTerminalSemanticPair reward profile
      let target := quittingTerminalSemanticPair reward mixedProfile
      (∃ recipient ∈ Finset.univ.erase who,
        0 < quittingTerminalSemanticDebtChange source target recipient) ∧
      0 < ∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target other ∧
      (∀ outcome,
        quittingTerminalOutcomeMass reward mixedProfile outcome =
          (1 / 2) * quittingTerminalOutcomeMass reward profile outcome +
            (1 / 2) * quittingTerminalOutcomeMass reward
              (Function.update profile who bestResponse) outcome) ∧
      (∀ terminal time,
        (1 / 2) * quittingStageCoalitionMass reward profile time terminal ≤
          quittingStageCoalitionMass reward mixedProfile time terminal) ∧
      ∀ terminal cutoff,
        (1 / 2) *
            (∑ time ∈ Finset.range cutoff,
              quittingStageCoalitionMass reward profile time terminal) ≤
          ∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward mixedProfile time terminal := by
  have hnear : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate + 0 := by
    intro candidate hcandidate
    simpa using hminimum candidate hcandidate
  obtain ⟨bestResponse, _htarget, _hgainQuarter, hgainPos, _hdecrease,
      htransfer, _hchord, hlaw, hpointwise, hglobalWindow⟩ :=
    exists_halfStoppingLawReset_nearMinimum_transfer_and_globalRetention
      reward profile who 0 hwhoDebt hnear
  refine ⟨bestResponse, ?_⟩
  dsimp only
  have hpositive : 0 < ∑ other ∈ Finset.univ.erase who,
      quittingTerminalSemanticDebtChange
        (quittingTerminalSemanticPair reward profile)
        (quittingTerminalSemanticPair reward
          (Function.update profile who
            (quittingStoppingLawMixtureBehaviorStrategy reward who (profile who)
              bestResponse (1 / 2) (by norm_num) (by norm_num)))) other := by
    linarith
  have hexists : ∃ recipient ∈ Finset.univ.erase who,
      0 < quittingTerminalSemanticDebtChange
        (quittingTerminalSemanticPair reward profile)
        (quittingTerminalSemanticPair reward
          (Function.update profile who
            (quittingStoppingLawMixtureBehaviorStrategy reward who (profile who)
              bestResponse (1 / 2) (by norm_num) (by norm_num)))) recipient := by
    by_contra hnot
    push Not at hnot
    have hnonpos := Finset.sum_nonpos fun recipient hrecipient =>
      hnot recipient hrecipient
    exact (not_le_of_gt hpositive) hnonpos
  exact ⟨hexists, hpositive, hlaw, hpointwise, hglobalWindow⟩

/-! ## Two matched directed resets or a quantitative excess charge -/

/-- **Two-step directed-reset alternative at an exact minimum.**

Reset one positive debtor halfway and select a positive recipient.  Let the
first target's total-debt excess over the minimum be `excess`.  Either that
excess is already at least one quarter of the recipient's target debt, or the
recipient can be used as the second reset mover and produces another positive
recipient.  In the latter branch every literal chronological atom of the
original profile survives in the second target with at least one quarter of
its mass.

The two successful edges are composable by construction: the first recipient
is the second mover.  For five players, attaching one fixed incidence player
therefore gives the four-role window isolated in
`FiveCycleIncidenceSupportRigidity`. -/
theorem exists_twoMatchedHalfResets_or_firstExcessCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (firstMover : ι)
    (hfirstDebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) firstMover)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ firstBestResponse : (quittingGame reward).BehaviorStrategy firstMover,
      let firstMixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
        reward firstMover (profile firstMover) firstBestResponse
          (1 / 2) (by norm_num) (by norm_num)
      let firstTargetProfile :=
        Function.update profile firstMover firstMixedStrategy
      let source := quittingTerminalSemanticPair reward profile
      let firstTarget := quittingTerminalSemanticPair reward firstTargetProfile
      let excess := quittingTerminalSemanticDebtSum firstTarget -
        quittingTerminalSemanticDebtSum source
      ∃ secondMover ∈ Finset.univ.erase firstMover,
        0 < quittingTerminalSemanticDebtChange source firstTarget secondMover ∧
        0 < quittingTerminalSemanticDebt firstTarget secondMover ∧
        0 ≤ excess ∧
        (∀ terminal time,
          (1 / 2) * quittingStageCoalitionMass reward profile time terminal ≤
            quittingStageCoalitionMass reward firstTargetProfile time terminal) ∧
        (quittingTerminalSemanticDebt firstTarget secondMover / 4 ≤ excess ∨
          ∃ secondBestResponse :
              (quittingGame reward).BehaviorStrategy secondMover,
            let secondMixedStrategy :=
              quittingStoppingLawMixtureBehaviorStrategy reward secondMover
                (firstTargetProfile secondMover) secondBestResponse
                (1 / 2) (by norm_num) (by norm_num)
            let secondTargetProfile :=
              Function.update firstTargetProfile secondMover secondMixedStrategy
            let secondTarget :=
              quittingTerminalSemanticPair reward secondTargetProfile
            ∃ thirdMover ∈ Finset.univ.erase secondMover,
              0 < quittingTerminalSemanticDebtChange
                firstTarget secondTarget thirdMover ∧
              ∀ terminal time,
                (1 / 4) *
                    quittingStageCoalitionMass reward profile time terminal ≤
                  quittingStageCoalitionMass reward secondTargetProfile
                    time terminal) := by
  have hnearZero : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate + 0 := by
    intro candidate hcandidate
    simpa using hminimum candidate hcandidate
  obtain ⟨firstBestResponse, hfirstTargetMem, _hfirstGainQuarter,
      hfirstGainPos, _hfirstDecrease, hfirstTransfer, _hfirstChord,
      _hfirstLaw, hfirstPointwise, _hfirstWindows⟩ :=
    exists_halfStoppingLawReset_nearMinimum_transfer_and_globalRetention
      reward profile firstMover 0 hfirstDebt hnearZero
  refine ⟨firstBestResponse, ?_⟩
  dsimp only
  let firstMixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
    reward firstMover (profile firstMover) firstBestResponse
      (1 / 2) (by norm_num) (by norm_num)
  let firstTargetProfile :=
    Function.update profile firstMover firstMixedStrategy
  let source := quittingTerminalSemanticPair reward profile
  let firstTarget := quittingTerminalSemanticPair reward firstTargetProfile
  let excess := quittingTerminalSemanticDebtSum firstTarget -
    quittingTerminalSemanticDebtSum source
  have hfirstTotalTransfer : 0 <
      ∑ other ∈ Finset.univ.erase firstMover,
        quittingTerminalSemanticDebtChange source firstTarget other := by
    linarith
  have hrecipient : ∃ secondMover ∈ Finset.univ.erase firstMover,
      0 < quittingTerminalSemanticDebtChange source firstTarget secondMover := by
    by_contra hnot
    push Not at hnot
    have hnonpos := Finset.sum_nonpos fun recipient hrecipientMem =>
      hnot recipient hrecipientMem
    exact (not_le_of_gt hfirstTotalTransfer) hnonpos
  obtain ⟨secondMover, hsecondMoverMem, hsecondChange⟩ := hrecipient
  have hsourceMem : source ∈ quittingTerminalSemanticCarrier reward := by
    exact quittingTerminalSemanticPair_mem_carrier reward profile
  have hsourceDebtNonneg : 0 ≤ quittingTerminalSemanticDebt source secondMover :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hsourceMem secondMover
  have hsecondDebt : 0 < quittingTerminalSemanticDebt firstTarget secondMover := by
    unfold quittingTerminalSemanticDebtChange at hsecondChange
    linarith
  have hexcess : 0 ≤ excess := by
    dsimp only [excess, firstTarget, source]
    exact sub_nonneg.mpr (hminimum
      (quittingTerminalSemanticPair reward firstTargetProfile)
      hfirstTargetMem)
  refine ⟨secondMover, hsecondMoverMem, hsecondChange, hsecondDebt, hexcess,
    hfirstPointwise, ?_⟩
  by_cases hexcessLarge :
      quittingTerminalSemanticDebt firstTarget secondMover / 4 ≤ excess
  · exact Or.inl hexcessLarge
  · right
    have hnearFirstTarget : ∀ candidate ∈
        quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum firstTarget ≤
          quittingTerminalSemanticDebtSum candidate + excess := by
      intro candidate hcandidate
      have hbase := hminimum candidate hcandidate
      dsimp only [excess]
      linarith
    obtain ⟨secondBestResponse, _hsecondTargetMem, hsecondGainQuarter,
        _hsecondGainPos, _hsecondDecrease, hsecondTransfer, _hsecondChord,
        _hsecondLaw, hsecondPointwise, _hsecondWindows⟩ :=
      exists_halfStoppingLawReset_nearMinimum_transfer_and_globalRetention
        reward firstTargetProfile secondMover excess hsecondDebt hnearFirstTarget
    refine ⟨secondBestResponse, ?_⟩
    let secondMixedStrategy :=
      quittingStoppingLawMixtureBehaviorStrategy reward secondMover
        (firstTargetProfile secondMover) secondBestResponse
        (1 / 2) (by norm_num) (by norm_num)
    let secondTargetProfile :=
      Function.update firstTargetProfile secondMover secondMixedStrategy
    let secondTarget :=
      quittingTerminalSemanticPair reward secondTargetProfile
    let secondGain := quittingTerminalPayoff reward secondTargetProfile
        secondMover -
      quittingTerminalPayoff reward firstTargetProfile secondMover
    have hgainAboveExcess : excess < secondGain := by
      exact lt_of_not_ge hexcessLarge |>.trans_le hsecondGainQuarter
    have hsecondTotalTransfer : 0 <
        ∑ other ∈ Finset.univ.erase secondMover,
          quittingTerminalSemanticDebtChange
            firstTarget secondTarget other := by
      linarith
    have hthirdRecipient : ∃ thirdMover ∈ Finset.univ.erase secondMover,
        0 < quittingTerminalSemanticDebtChange
          firstTarget secondTarget thirdMover := by
      by_contra hnot
      push Not at hnot
      have hnonpos := Finset.sum_nonpos fun recipient hrecipientMem =>
        hnot recipient hrecipientMem
      exact (not_le_of_gt hsecondTotalTransfer) hnonpos
    obtain ⟨thirdMover, hthirdMem, hthirdChange⟩ := hthirdRecipient
    refine ⟨thirdMover, hthirdMem, hthirdChange, ?_⟩
    intro terminal time
    have hfirst := hfirstPointwise terminal time
    have hsecond := hsecondPointwise terminal time
    have hscaled : (1 / 2) *
          ((1 / 2) * quittingStageCoalitionMass reward profile time terminal) ≤
        (1 / 2) * quittingStageCoalitionMass reward firstTargetProfile
          time terminal :=
      mul_le_mul_of_nonneg_left hfirst (by norm_num)
    calc
      (1 / 4) * quittingStageCoalitionMass reward profile time terminal =
          (1 / 2) *
            ((1 / 2) * quittingStageCoalitionMass reward profile time terminal) :=
        by ring
      _ ≤ (1 / 2) * quittingStageCoalitionMass reward firstTargetProfile
          time terminal := hscaled
      _ ≤ quittingStageCoalitionMass reward secondTargetProfile time terminal :=
        hsecond

end GameTheory
