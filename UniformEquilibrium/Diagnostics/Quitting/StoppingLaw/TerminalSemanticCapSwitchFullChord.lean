/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticCapSwitchFriction

/-!
# Full-chord output of a stopping-law cap switch

An effective complete-law mixture edge whose normalized pure-time gap changes
at first order descales to its literal full target.  One of the unmixed/full
endpoints then carries a fixed paid first-disagreement row.  The same output
retains both the pair-deleted survival floor and the exact factorization of
its full opponent survival.

This is static stopping-law geometry for supplied profiles.  It does not
produce a reset square, preserve a minimum fibre, or consume the paid row.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One source/full endpoint of a cap-switch edge, together with its paid row
and the two survival conclusions forced by the edge increment. -/
structure QuittingCapSwitchFullChordPaidRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (start : ℕ) (later : Option ℕ) (gain deletedFloor bound : ℝ) where
  /-- The selected literal endpoint profile. -/
  receiving : (quittingGame reward).BehaviorProfile
  /-- The endpoint is either the unmixed source or literal full target. -/
  receiving_eq : receiving = Function.update profile mover source ∨
    receiving = Function.update profile mover target
  /-- The selected endpoint's exact paid first-disagreement row. -/
  row : QuittingPaidFirstDisagreementRow reward receiving observer gain
  /-- Its two witnesses are exactly the supplied normalized pair, in one
  profitable orientation. -/
  row_witnesses :
    (row.sourceWitness = quittingAbsolutePureTime start later ∧
      row.receivingWitness = some start) ∨
    (row.sourceWitness = some start ∧
      row.receivingWitness = quittingAbsolutePureTime start later)
  /-- The edge-local pair-deleted clock retains the supplied floor. -/
  pairDeleted_floor : deletedFloor ≤
    quittingPairDeletedSurvivalWeight
      (quittingProfileLiveRoot reward profile) mover observer 0 start
  /-- The selected endpoint has macroscopic full opponent survival. -/
  gain_le_fullOpponentSurvival : gain ≤ 2 * bound *
    quittingOpponentSurvivalWeight
      (quittingProfileLiveRoot reward receiving) observer 0 start
  /-- The full opponent clock factors through the same pair-deleted clock
  and the selected mover's inclusive tail. -/
  fullOpponentSurvival_eq_pairDeleted_mul_moverSurvival :
    quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward receiving) observer 0 start =
      quittingPairDeletedSurvivalWeight
          (quittingProfileLiveRoot reward profile) mover observer 0 start *
        quittingHazardSurvival
          (fun time ↦ quittingProfileLiveRoot reward receiving time mover) start

private theorem fullOpponentSurvival_factor_source
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hmoverObserver : mover ≠ observer)
    (source : (quittingGame reward).BehaviorStrategy mover) (start : ℕ) :
    quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward (Function.update profile mover source))
        observer 0 start =
      quittingPairDeletedSurvivalWeight
          (quittingProfileLiveRoot reward profile) mover observer 0 start *
        quittingHazardSurvival (quittingBehaviorLiveHazard reward source) start := by
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingOpponentSurvivalWeight_eq_pairDeleted_mul_moverSurvival
      (quittingRootSequenceUpdate
        (quittingProfileLiveRoot reward profile) mover
        (quittingBehaviorLiveHazard reward source))
      mover observer hmoverObserver start]
  simp [quittingRootSequenceUpdate]

/-- **Full-chord cap-switch output.**  The hypotheses are division-free
forms of the deleted-survival and descaling budgets.  They make the theorem
usable with an edge charge proportional to a small reset scale without
introducing quotient side conditions. -/
theorem exists_quittingCapSwitchFullChordPaidRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hmoverObserver : mover ≠ observer)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (scale : ℝ) (hscale0 : 0 < scale) (hscale1 : scale ≤ 1)
    (start : ℕ) (later : Option ℕ)
    (edgeCharge gain deletedFloor bound : ℝ)
    (hgain : 0 < gain)
    (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hedge : edgeCharge ≤
      |quittingNormalizedPureTimeGap reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              scale hscale0.le hscale1)) observer start later -
        quittingNormalizedPureTimeGap reward
          (Function.update profile mover source) observer start later|)
    (hdeletedBudget : 4 * bound * scale * deletedFloor ≤ edgeCharge)
    (hgainBudget : 2 * scale * gain ≤ edgeCharge) :
    Nonempty (QuittingCapSwitchFullChordPaidRow reward profile mover observer
      source target start later gain deletedFloor bound) := by
  let sourceProfile := Function.update profile mover source
  let targetProfile := Function.update profile mover target
  let sourceGap := quittingNormalizedPureTimeGap reward sourceProfile
    observer start later
  let targetGap := quittingNormalizedPureTimeGap reward targetProfile
    observer start later
  have hfriction :=
    abs_quittingNormalizedPureTimeGap_update_stoppingLawMixture_sub_le_coarse
      reward profile mover observer hmoverObserver source target scale hscale0.le
        hscale1 start later bound hbound.le hreward
  have hdeleted : deletedFloor ≤
      quittingPairDeletedSurvivalWeight
        (quittingProfileLiveRoot reward profile) mover observer 0 start := by
    have hclock : 4 * bound * scale * deletedFloor ≤
        4 * bound * scale * quittingPairDeletedSurvivalWeight
          (quittingProfileLiveRoot reward profile) mover observer 0 start :=
      hdeletedBudget.trans (hedge.trans hfriction)
    have hcoefficient : 0 < 4 * bound * scale := by positivity
    nlinarith
  have haffine :=
    quittingNormalizedPureTimeGap_update_stoppingLawMixture_eq
      reward profile mover observer hmoverObserver source target scale
        hscale0.le hscale1 start later
  have hfullDifference : edgeCharge ≤ scale * |targetGap - sourceGap| := by
    dsimp only [sourceGap, targetGap, sourceProfile, targetProfile]
    rw [haffine] at hedge
    have hrewrite :
        (1 - scale) *
              quittingNormalizedPureTimeGap reward
                (Function.update profile mover source) observer start later +
            scale *
              quittingNormalizedPureTimeGap reward
                (Function.update profile mover target) observer start later -
          quittingNormalizedPureTimeGap reward
            (Function.update profile mover source) observer start later =
          scale *
            (quittingNormalizedPureTimeGap reward
                (Function.update profile mover target) observer start later -
              quittingNormalizedPureTimeGap reward
                (Function.update profile mover source) observer start later) := by
      ring
    rw [hrewrite, abs_mul, abs_of_nonneg hscale0.le] at hedge
    exact hedge
  have hsum : 2 * gain ≤ |targetGap| + |sourceGap| := by
    have hscaled : 2 * scale * gain ≤ scale * |targetGap - sourceGap| :=
      hgainBudget.trans hfullDifference
    have hdescaled : 2 * gain ≤ |targetGap - sourceGap| := by nlinarith
    exact hdescaled.trans (abs_sub targetGap sourceGap)
  have hendpoint : gain ≤ |sourceGap| ∨ gain ≤ |targetGap| := by
    by_contra hne
    push Not at hne
    nlinarith
  rcases hendpoint with hsource | htarget
  · have hsourceSurvival :=
      abs_quittingNormalizedPureTimeGap_le_opponentSurvival
      reward sourceProfile observer start later bound hbound.le hreward
    have hpaidSurvival : gain ≤ 2 * bound *
        quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward sourceProfile) observer 0 start :=
      hsource.trans hsourceSurvival
    have hfactor := fullOpponentSurvival_factor_source reward profile mover observer
      hmoverObserver source start
    by_cases hgap : 0 ≤ sourceGap
    · have hedgePositive : gain ≤ sourceGap := by simpa [abs_of_nonneg hgap] using hsource
      have hedgePayoff : gain ≤
          quittingPureTimeDeviationPayoff reward sourceProfile observer (some start) -
            quittingPureTimeDeviationPayoff reward sourceProfile observer
              (quittingAbsolutePureTime start later) := by
        simpa [sourceGap, quittingNormalizedPureTimeGap] using hedgePositive
      obtain ⟨row, hrowSource, hrowReceiving⟩ :=
        exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
          reward sourceProfile observer (quittingAbsolutePureTime start later)
            (some start) gain hgain hedgePayoff
      exact ⟨{
        receiving := sourceProfile
        receiving_eq := Or.inl rfl
        row := row
        row_witnesses := Or.inl ⟨hrowSource, hrowReceiving⟩
        pairDeleted_floor := hdeleted
        gain_le_fullOpponentSurvival := hpaidSurvival
        fullOpponentSurvival_eq_pairDeleted_mul_moverSurvival := by
          simpa [sourceProfile, quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
            quittingRootSequenceUpdate] using hfactor
      }⟩
    · have hgap' : sourceGap < 0 := lt_of_not_ge hgap
      have hedgePositive : gain ≤ -sourceGap := by
        simpa [abs_of_neg hgap'] using hsource
      have hedgePayoff : gain ≤
          quittingPureTimeDeviationPayoff reward sourceProfile observer
              (quittingAbsolutePureTime start later) -
            quittingPureTimeDeviationPayoff reward sourceProfile observer (some start) := by
        dsimp only [sourceGap, quittingNormalizedPureTimeGap] at hedgePositive
        linarith
      obtain ⟨row, hrowSource, hrowReceiving⟩ :=
        exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
          reward sourceProfile observer (some start)
            (quittingAbsolutePureTime start later) gain hgain hedgePayoff
      exact ⟨{
        receiving := sourceProfile
        receiving_eq := Or.inl rfl
        row := row
        row_witnesses := Or.inr ⟨hrowSource, hrowReceiving⟩
        pairDeleted_floor := hdeleted
        gain_le_fullOpponentSurvival := hpaidSurvival
        fullOpponentSurvival_eq_pairDeleted_mul_moverSurvival := by
          simpa [sourceProfile, quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
            quittingRootSequenceUpdate] using hfactor
      }⟩
  · have htargetSurvival :=
      abs_quittingNormalizedPureTimeGap_le_opponentSurvival
      reward targetProfile observer start later bound hbound.le hreward
    have hpaidSurvival : gain ≤ 2 * bound *
        quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward targetProfile) observer 0 start :=
      htarget.trans htargetSurvival
    have hfactor := fullOpponentSurvival_factor_source reward profile mover observer
      hmoverObserver target start
    by_cases hgap : 0 ≤ targetGap
    · have hedgePositive : gain ≤ targetGap := by simpa [abs_of_nonneg hgap] using htarget
      have hedgePayoff : gain ≤
          quittingPureTimeDeviationPayoff reward targetProfile observer (some start) -
            quittingPureTimeDeviationPayoff reward targetProfile observer
              (quittingAbsolutePureTime start later) := by
        simpa [targetGap, quittingNormalizedPureTimeGap] using hedgePositive
      obtain ⟨row, hrowSource, hrowReceiving⟩ :=
        exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
          reward targetProfile observer (quittingAbsolutePureTime start later)
            (some start) gain hgain hedgePayoff
      exact ⟨{
        receiving := targetProfile
        receiving_eq := Or.inr rfl
        row := row
        row_witnesses := Or.inl ⟨hrowSource, hrowReceiving⟩
        pairDeleted_floor := hdeleted
        gain_le_fullOpponentSurvival := hpaidSurvival
        fullOpponentSurvival_eq_pairDeleted_mul_moverSurvival := by
          simpa [targetProfile, quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
            quittingRootSequenceUpdate] using hfactor
      }⟩
    · have hgap' : targetGap < 0 := lt_of_not_ge hgap
      have hedgePositive : gain ≤ -targetGap := by
        simpa [abs_of_neg hgap'] using htarget
      have hedgePayoff : gain ≤
          quittingPureTimeDeviationPayoff reward targetProfile observer
              (quittingAbsolutePureTime start later) -
            quittingPureTimeDeviationPayoff reward targetProfile observer (some start) := by
        dsimp only [targetGap, quittingNormalizedPureTimeGap] at hedgePositive
        linarith
      obtain ⟨row, hrowSource, hrowReceiving⟩ :=
        exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
          reward targetProfile observer (some start)
            (quittingAbsolutePureTime start later) gain hgain hedgePayoff
      exact ⟨{
        receiving := targetProfile
        receiving_eq := Or.inr rfl
        row := row
        row_witnesses := Or.inr ⟨hrowSource, hrowReceiving⟩
        pairDeleted_floor := hdeleted
        gain_le_fullOpponentSurvival := hpaidSurvival
        fullOpponentSurvival_eq_pairDeleted_mul_moverSurvival := by
          simpa [targetProfile, quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
            quittingRootSequenceUpdate] using hfactor
      }⟩

/-- A signed rectangle along two literal mixture edges selects one of their
full chords.  The edge charge, paid gain, and deleted-floor budgets are kept
division-free; applications may substitute their preferred scale constants. -/
theorem exists_quittingCapSwitchFullChordPaidRow_of_twoEdgeRectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (firstProfile secondProfile : (quittingGame reward).BehaviorProfile)
    (firstMover secondMover observer : ι)
    (hfirstMover : firstMover ≠ observer)
    (hsecondMover : secondMover ≠ observer)
    (firstSource firstTarget :
      (quittingGame reward).BehaviorStrategy firstMover)
    (secondSource secondTarget :
      (quittingGame reward).BehaviorStrategy secondMover)
    (firstScale secondScale : ℝ)
    (hfirstScale0 : 0 < firstScale) (hfirstScale1 : firstScale ≤ 1)
    (hsecondScale0 : 0 < secondScale) (hsecondScale1 : secondScale ≤ 1)
    (start : ℕ) (later : Option ℕ)
    (edgeCharge gain deletedFloor bound : ℝ)
    (hgain : 0 < gain) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hmiddle :
      Function.update firstProfile firstMover
          (quittingStoppingLawMixtureBehaviorStrategy reward firstMover
            firstSource firstTarget firstScale hfirstScale0.le hfirstScale1) =
        Function.update secondProfile secondMover secondSource)
    (hrectangle : 2 * edgeCharge ≤
      quittingNormalizedPureTimeGap reward
          (Function.update secondProfile secondMover
            (quittingStoppingLawMixtureBehaviorStrategy reward secondMover
              secondSource secondTarget secondScale hsecondScale0.le
                hsecondScale1)) observer start later -
        quittingNormalizedPureTimeGap reward
          (Function.update firstProfile firstMover firstSource)
            observer start later)
    (hfirstDeleted :
      4 * bound * firstScale * deletedFloor ≤ edgeCharge)
    (hsecondDeleted :
      4 * bound * secondScale * deletedFloor ≤ edgeCharge)
    (hfirstGain : 2 * firstScale * gain ≤ edgeCharge)
    (hsecondGain : 2 * secondScale * gain ≤ edgeCharge) :
    Nonempty (QuittingCapSwitchFullChordPaidRow reward firstProfile
        firstMover observer firstSource firstTarget start later gain
          deletedFloor bound) ∨
      Nonempty (QuittingCapSwitchFullChordPaidRow reward secondProfile
        secondMover observer secondSource secondTarget start later gain
          deletedFloor bound) := by
  let firstStart := quittingNormalizedPureTimeGap reward
    (Function.update firstProfile firstMover firstSource) observer start later
  let middle := quittingNormalizedPureTimeGap reward
    (Function.update firstProfile firstMover
      (quittingStoppingLawMixtureBehaviorStrategy reward firstMover
        firstSource firstTarget firstScale hfirstScale0.le hfirstScale1))
      observer start later
  let secondEnd := quittingNormalizedPureTimeGap reward
    (Function.update secondProfile secondMover
      (quittingStoppingLawMixtureBehaviorStrategy reward secondMover
        secondSource secondTarget secondScale hsecondScale0.le hsecondScale1))
      observer start later
  have hmiddleGap : middle = quittingNormalizedPureTimeGap reward
      (Function.update secondProfile secondMover secondSource)
        observer start later := by
    simp only [middle]
    rw [hmiddle]
  have htotal : 2 * edgeCharge ≤ secondEnd - firstStart := by
    simpa only [firstStart, secondEnd] using hrectangle
  have hedge : edgeCharge ≤ |middle - firstStart| ∨
      edgeCharge ≤ |secondEnd - middle| := by
    by_contra hne
    push Not at hne
    have hfirstUpper : middle - firstStart < edgeCharge :=
      (le_abs_self (middle - firstStart)).trans_lt hne.1
    have hsecondUpper : secondEnd - middle < edgeCharge :=
      (le_abs_self (secondEnd - middle)).trans_lt hne.2
    linarith
  rcases hedge with hedge | hedge
  · exact Or.inl <| exists_quittingCapSwitchFullChordPaidRow
      reward firstProfile firstMover observer hfirstMover firstSource firstTarget
        firstScale hfirstScale0 hfirstScale1 start later edgeCharge gain
          deletedFloor bound hgain hbound hreward (by
            simpa only [middle, firstStart] using hedge)
          hfirstDeleted hfirstGain
  · exact Or.inr <| exists_quittingCapSwitchFullChordPaidRow
      reward secondProfile secondMover observer hsecondMover secondSource secondTarget
        secondScale hsecondScale0 hsecondScale1 start later edgeCharge gain
          deletedFloor bound hgain hbound hreward (by
            rw [hmiddleGap] at hedge
            simpa only [secondEnd] using hedge)
          hsecondDeleted hsecondGain

/-- Literal first-order specialization of the two-edge rectangle theorem.
An edge scale at most `constant * smallScale` yields the packet's
`charge / (8 * bound * constant)` deleted floor and
`charge / (4 * constant)` paid full-chord gain. -/
theorem exists_quittingCapSwitchFullChordPaidRow_of_firstOrderRectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (firstProfile secondProfile : (quittingGame reward).BehaviorProfile)
    (firstMover secondMover observer : ι)
    (hfirstMover : firstMover ≠ observer)
    (hsecondMover : secondMover ≠ observer)
    (firstSource firstTarget :
      (quittingGame reward).BehaviorStrategy firstMover)
    (secondSource secondTarget :
      (quittingGame reward).BehaviorStrategy secondMover)
    (firstScale secondScale smallScale constant charge bound : ℝ)
    (hfirstScale0 : 0 < firstScale) (hfirstScale1 : firstScale ≤ 1)
    (hsecondScale0 : 0 < secondScale) (hsecondScale1 : secondScale ≤ 1)
    (hconstant : 0 < constant)
    (hcharge : 0 < charge) (hbound : 0 < bound)
    (hfirstScale : firstScale ≤ constant * smallScale)
    (hsecondScale : secondScale ≤ constant * smallScale)
    (start : ℕ) (later : Option ℕ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hmiddle :
      Function.update firstProfile firstMover
          (quittingStoppingLawMixtureBehaviorStrategy reward firstMover
            firstSource firstTarget firstScale hfirstScale0.le hfirstScale1) =
        Function.update secondProfile secondMover secondSource)
    (hrectangle : charge * smallScale ≤
      quittingNormalizedPureTimeGap reward
          (Function.update secondProfile secondMover
            (quittingStoppingLawMixtureBehaviorStrategy reward secondMover
              secondSource secondTarget secondScale hsecondScale0.le
                hsecondScale1)) observer start later -
        quittingNormalizedPureTimeGap reward
          (Function.update firstProfile firstMover firstSource)
            observer start later) :
    Nonempty (QuittingCapSwitchFullChordPaidRow reward firstProfile
        firstMover observer firstSource firstTarget start later
          (charge / (4 * constant)) (charge / (8 * bound * constant)) bound) ∨
      Nonempty (QuittingCapSwitchFullChordPaidRow reward secondProfile
        secondMover observer secondSource secondTarget start later
          (charge / (4 * constant)) (charge / (8 * bound * constant)) bound) := by
  have hgain : 0 < charge / (4 * constant) := div_pos hcharge (by positivity)
  have hdeletedBudget (scale : ℝ) (hscale : scale ≤ constant * smallScale) :
      4 * bound * scale * (charge / (8 * bound * constant)) ≤
        charge * smallScale / 2 := by
    have heq : 4 * bound * scale * (charge / (8 * bound * constant)) =
        charge * scale / (2 * constant) := by
      field_simp
      ring
    rw [heq]
    apply (div_le_iff₀ (show 0 < 2 * constant by positivity)).2
    have hscaled := mul_le_mul_of_nonneg_left hscale hcharge.le
    nlinarith
  have hgainBudget (scale : ℝ) (hscale : scale ≤ constant * smallScale) :
      2 * scale * (charge / (4 * constant)) ≤ charge * smallScale / 2 := by
    have heq : 2 * scale * (charge / (4 * constant)) =
        charge * scale / (2 * constant) := by
      field_simp
      ring
    rw [heq]
    apply (div_le_iff₀ (show 0 < 2 * constant by positivity)).2
    have hscaled := mul_le_mul_of_nonneg_left hscale hcharge.le
    nlinarith
  apply exists_quittingCapSwitchFullChordPaidRow_of_twoEdgeRectangle
    reward firstProfile secondProfile firstMover secondMover observer
      hfirstMover hsecondMover firstSource firstTarget secondSource secondTarget
      firstScale secondScale hfirstScale0 hfirstScale1 hsecondScale0
      hsecondScale1 start later (charge * smallScale / 2)
      (charge / (4 * constant)) (charge / (8 * bound * constant)) bound
      hgain hbound hreward hmiddle
  · nlinarith
  · exact hdeletedBudget firstScale hfirstScale
  · exact hdeletedBudget secondScale hsecondScale
  · exact hgainBudget firstScale hfirstScale
  · exact hgainBudget secondScale hsecondScale

end GameTheory
