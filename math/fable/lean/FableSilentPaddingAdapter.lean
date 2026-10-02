/-
Universal silent-padding two-cut constructor.

`FablePostmarkTwoCutInstantiation` builds a padded post-mark two-cut block
from the immediate arm of the `3 * mu / 4` dichotomy, where the window is the
single original date zero.  This file removes the dichotomy: the window
threshold is an arbitrary real `chi` strictly below the terminal-law
coordinate of one fixed nonempty coalition, and the block covers the whole
selected finite window rather than one date.

The construction is the same silent prefix.  One deterministic all-Continue
product row is prepended to the canonical live-root word of the source
profile.  Countable additivity of the stage-mass disintegration selects a
finite window `[0, e)` carrying coalition mass above `chi`; the per-date
domination of stage mass by the live root's total marginal quit rate turns
that into a hazard floor `chi` on the padded rows `[1, e + 1)`.  Since the
padding row is all-Continue, joint survival to the entry cut is exactly one,
so `reachFloor = 1` and no reach factor appears downstream.

The padding row is payoff-invisible and law-invisible but not cap-invisible:
each envelope coordinate of the padded parent is the source's own envelope
coordinate raised to that player's singleton quitting reward.  Cap neutrality
is therefore stated in hypothesis form -- every singleton reward strictly
below the source's own cap -- together with the connecting consequence of the
production singleton margin at a positive global minimum, which is what makes
that hypothesis available eventually along a cap-convergent source sequence.
The sequence-level eventuality itself is not formed here.

Nothing here constructs the positive carrier minimum: it is supplied.  The
paid outputs are unilateral updates of the padded parent profile and are not
asserted to be renewable children or to return to the minimum.
-/
import FablePostmarkAtomBlock
import FablePostmarkTwoCutInstantiation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## P1: window truncation at an arbitrary threshold -/

/-- Countable additivity at an arbitrary threshold strictly below the law
coordinate: some positive finite window of dates already carries coalition
stage mass above the threshold.  No dichotomy and no date-zero split. -/
theorem fableSilentPadding_exists_window
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {χ : ℝ}
    (hlaw : χ < quittingAbsorbedMassLimit reward profile terminal) :
    ∃ window : ℕ, 0 < window ∧
      χ < ∑ time ∈ Finset.range window,
        quittingStageCoalitionMass reward profile time terminal := by
  have hsum := hasSum_quittingStageCoalitionMass reward profile terminal
  obtain ⟨cutoff, hcutoff⟩ :=
    (hsum.tendsto_sum_nat.eventually_const_lt hlaw).exists
  refine ⟨cutoff + 1, Nat.succ_pos cutoff, ?_⟩
  have hlast := quittingStageCoalitionMass_nonneg reward profile cutoff terminal
  rw [Finset.sum_range_succ]
  linarith

/-! ## P2: the window hazard floor -/

/-- Per-date domination summed over a window: a window carrying coalition
stage mass above a threshold carries total marginal quit rate above the same
threshold. -/
theorem fableSilentPadding_window_hazard_gt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {χ : ℝ} (window : ℕ)
    (hwindow : χ < ∑ time ∈ Finset.range window,
      quittingStageCoalitionMass reward profile time terminal) :
    χ < ∑ time ∈ Finset.range window,
      ∑ who, quittingRootQuitRates
        (quittingProfileLiveRoot reward profile time) who := by
  have hdominate := Finset.sum_le_sum (f := fun time =>
      quittingStageCoalitionMass reward profile time terminal)
    (g := fun time => ∑ who, quittingRootQuitRates
      (quittingProfileLiveRoot reward profile time) who)
    (s := Finset.range window)
    (fun time _ => fablePostmark_stageCoalitionMass_le_sum_quitRates
      reward profile time terminal)
  linarith

/-- The two window facts together, at an arbitrary threshold strictly below
the law coordinate. -/
theorem fableSilentPadding_exists_window_hazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {χ : ℝ}
    (hlaw : χ < quittingAbsorbedMassLimit reward profile terminal) :
    ∃ window : ℕ, 0 < window ∧
      χ < (∑ time ∈ Finset.range window,
        quittingStageCoalitionMass reward profile time terminal) ∧
      χ < ∑ time ∈ Finset.range window,
        ∑ who, quittingRootQuitRates
          (quittingProfileLiveRoot reward profile time) who := by
  obtain ⟨window, hpos, hmass⟩ :=
    fableSilentPadding_exists_window reward profile terminal hlaw
  exact ⟨window, hpos, hmass,
    fableSilentPadding_window_hazard_gt reward profile terminal window hmass⟩

/-! ## P3: the padded block instance -/

/-- The universal silent-padding post-mark two-cut block.  The padding row is
`markedRow = 0`, the original window `[0, window)` is the block
`[entryCut, exitCut) = [1, window + 1)`, the entry reach is exactly one, and
the hazard floor is the supplied window threshold. -/
def fableSilentPaddingTwoCutBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {χ : ℝ} (hχ : 0 < χ)
    (window : ℕ) (hpos : 0 < window)
    (hhazard : χ < ∑ time ∈ Finset.range window,
      ∑ who, quittingRootQuitRates
        (quittingProfileLiveRoot reward profile time) who)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    QuittingUniformlyReachedPostMarkTwoCutBlock reward where
  roots := fablePostmarkPaddedRoots (quittingProfileLiveRoot reward profile)
  entryCut := 1
  exitCut := window + 1
  entryCut_lt_exitCut := Nat.succ_lt_succ hpos
  minimum := minimum
  minimum_mem := hminimumMem
  minimum_le := hminimumLe
  minimum_pos := hminimumPos
  markedRow := 0
  markedRow_lt_entryCut := Nat.zero_lt_one
  hazardFloor := χ
  hazardFloor_pos := hχ
  totalMarginalHazard_ge := by
    show χ ≤ ∑ offset ∈ Finset.range (window + 1 - 1),
      ∑ who, ((fablePostmarkPaddedRoots
        (quittingProfileLiveRoot reward profile) (1 + offset)) who true).toReal
    have hshift : ∑ offset ∈ Finset.range (window + 1 - 1),
          ∑ who, ((fablePostmarkPaddedRoots
            (quittingProfileLiveRoot reward profile) (1 + offset))
              who true).toReal =
        ∑ time ∈ Finset.range window,
          ∑ who, quittingRootQuitRates
            (quittingProfileLiveRoot reward profile time) who := by
      simp only [Nat.add_sub_cancel]
      refine Finset.sum_congr rfl fun offset _ => ?_
      rw [Nat.add_comm 1 offset]
      rfl
    rw [hshift]
    exact hhazard.le
  reachFloor := 1
  reachFloor_pos := one_pos
  entryReach_ge := by
    show (1 : ℝ) ≤ quittingJointSurvivalWeight
      (fablePostmarkPaddedRoots (quittingProfileLiveRoot reward profile)) 0 1
    rw [quittingJointSurvivalWeight_succ]
    simp

section Fields

variable (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
  (profile : (quittingGame reward).BehaviorProfile) {χ : ℝ} (hχ : 0 < χ)
  (window : ℕ) (hpos : 0 < window)
  (hhazard : χ < ∑ time ∈ Finset.range window,
    ∑ who, quittingRootQuitRates
      (quittingProfileLiveRoot reward profile time) who)
  (minimum : QuittingTerminalSemanticPair ι)
  (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
  (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate)
  (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)

@[simp] theorem fableSilentPaddingTwoCutBlock_roots :
    (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
      minimum hminimumMem hminimumLe hminimumPos).roots =
      fablePostmarkPaddedRoots (quittingProfileLiveRoot reward profile) := rfl

@[simp] theorem fableSilentPaddingTwoCutBlock_markedRow :
    (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
      minimum hminimumMem hminimumLe hminimumPos).markedRow = 0 := rfl

@[simp] theorem fableSilentPaddingTwoCutBlock_entryCut :
    (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
      minimum hminimumMem hminimumLe hminimumPos).entryCut = 1 := rfl

@[simp] theorem fableSilentPaddingTwoCutBlock_exitCut :
    (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
      minimum hminimumMem hminimumLe hminimumPos).exitCut = window + 1 := rfl

@[simp] theorem fableSilentPaddingTwoCutBlock_hazardFloor :
    (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
      minimum hminimumMem hminimumLe hminimumPos).hazardFloor = χ := rfl

@[simp] theorem fableSilentPaddingTwoCutBlock_reachFloor :
    (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
      minimum hminimumMem hminimumLe hminimumPos).reachFloor = 1 := rfl

@[simp] theorem fableSilentPaddingTwoCutBlock_minimum :
    (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
      minimum hminimumMem hminimumLe hminimumPos).minimum = minimum := rfl

end Fields

/-- Existence form of the universal constructor: from any threshold strictly
below the terminal-law coordinate of one fixed nonempty coalition, a padded
post-mark two-cut block with mark zero, entry cut one, reach floor one, and
hazard floor that threshold. -/
theorem fableSilentPadding_exists_twoCutBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {χ : ℝ} (hχ : 0 < χ)
    (hlaw : χ < quittingAbsorbedMassLimit reward profile terminal)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ window : ℕ, 0 < window ∧
      ∃ block : QuittingUniformlyReachedPostMarkTwoCutBlock reward,
        block.roots =
            fablePostmarkPaddedRoots (quittingProfileLiveRoot reward profile) ∧
          block.markedRow = 0 ∧ block.entryCut = 1 ∧
          block.exitCut = window + 1 ∧ block.hazardFloor = χ ∧
          block.reachFloor = 1 ∧ block.minimum = minimum := by
  obtain ⟨window, hpos, -, hhazard⟩ :=
    fableSilentPadding_exists_window_hazard reward profile terminal hlaw
  exact ⟨window, hpos,
    fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
      minimum hminimumMem hminimumLe hminimumPos,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## P4: the exact shift identities -/

/-- Date-generic exit shift: the padded word's semantic pair one date after a
cut is the original word's semantic pair at that cut.  The date-two lemma of
`FablePostmarkTwoCutInstantiation` is the case `cut = 1`. -/
theorem fablePostmark_paddedSemanticPairAt_succ_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cut : ℕ) :
    quittingRootSequenceTerminalSemanticPairAt reward
        (fablePostmarkPaddedRoots roots) (cut + 1) =
      quittingRootSequenceTerminalSemanticPairAt reward roots cut := by
  unfold quittingRootSequenceTerminalSemanticPairAt
  rw [fablePostmark_paddedRootSequenceProfile_succ]

section Identities

variable (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
  (profile : (quittingGame reward).BehaviorProfile) {χ : ℝ} (hχ : 0 < χ)
  (window : ℕ) (hpos : 0 < window)
  (hhazard : χ < ∑ time ∈ Finset.range window,
    ∑ who, quittingRootQuitRates
      (quittingProfileLiveRoot reward profile time) who)
  (minimum : QuittingTerminalSemanticPair ι)
  (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
  (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate)
  (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)

/-- The block's entry pair is the source profile's own terminal semantic
pair: the silent prefix introduces no scaling at the entry cut. -/
theorem fableSilentPaddingTwoCutBlock_entryPair_eq :
    (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
        minimum hminimumMem hminimumLe hminimumPos).entryPair =
      quittingTerminalSemanticPair reward profile :=
  fablePostmark_paddedEntryPair_eq reward profile

/-- The block's exit pair is the source word's own canonical suffix pair at
the selected window length. -/
theorem fableSilentPaddingTwoCutBlock_exitPair_eq :
    (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
        minimum hminimumMem hminimumLe hminimumPos).exitPair =
      quittingRootSequenceTerminalSemanticPairAt reward
        (quittingProfileLiveRoot reward profile) window :=
  fablePostmark_paddedSemanticPairAt_succ_eq reward
    (quittingProfileLiveRoot reward profile) window

/-- The block's entry profile is the source's own canonical live-root
profile. -/
theorem fableSilentPaddingTwoCutBlock_entryProfile_eq :
    (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
        minimum hminimumMem hminimumLe hminimumPos).entryProfile =
      quittingRootSequenceProfile reward
        (quittingProfileLiveRoot reward profile) 0 :=
  fablePostmark_paddedRootSequenceProfile_succ reward
    (quittingProfileLiveRoot reward profile) 0

/-- The exact cap maximum formula at this instance: the padded parent's
prescribed payoff coordinate is the source's own, and its envelope coordinate
is the source's own envelope raised to that player's singleton quitting
reward. -/
theorem fableSilentPaddingTwoCutBlock_parentPair_eq :
    quittingRootSequenceTerminalSemanticPairAt reward
        (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
          minimum hminimumMem hminimumLe hminimumPos).roots 0 =
      ((quittingTerminalSemanticPair reward profile).1,
        fun who => max (reward (quittingSingletonTerminal who) who)
          ((quittingTerminalSemanticPair reward profile).2 who)) :=
  fablePostmark_paddedParentPair_eq reward profile

/-- The padded parent has exactly the source's terminal payoffs. -/
theorem fableSilentPaddingTwoCutBlock_parentPayoff_eq (who : ι) :
    quittingTerminalPayoff reward
        (quittingRootSequenceProfile reward
          (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
            minimum hminimumMem hminimumLe hminimumPos).roots 0) who =
      quittingTerminalPayoff reward profile who :=
  fablePostmark_paddedParent_terminalPayoff_eq reward profile who

end Identities

/-! ## P4 continued: law invariance of the silent prefix -/

omit [DecidableEq ι] in
/-- The canonical profile of a root word read from date zero has that word as
its live-root family. -/
theorem fableSilentPadding_liveRoot_rootSequenceProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingRootSequenceProfile reward roots 0) time = roots time := by
  funext player
  show roots (0 + time) player = roots time player
  rw [Nat.zero_add]

omit [DecidableEq ι] in
/-- Joint survival of the padded parent to the date after the silent row is
the source's own joint survival one date earlier. -/
theorem fableSilentPadding_paddedParent_liveMass_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward
        (quittingRootSequenceProfile reward
          (fablePostmarkPaddedRoots
            (quittingProfileLiveRoot reward profile)) 0) (time + 1) =
      quittingLiveMass reward profile time := by
  induction time with
  | zero =>
      rw [quittingLiveMass_succ,
        fablePostmark_jointContinueMass_eq_stationaryContinueMass,
        fableSilentPadding_liveRoot_rootSequenceProfile,
        fablePostmarkPaddedRoots_zero,
        fableTwoCut_stationaryContinueMass_allContinueRoot]
      simp
  | succ time ih =>
      rw [quittingLiveMass_succ,
        fablePostmark_jointContinueMass_eq_stationaryContinueMass,
        fableSilentPadding_liveRoot_rootSequenceProfile,
        fablePostmarkPaddedRoots_succ, ih, quittingLiveMass_succ,
        fablePostmark_jointContinueMass_eq_stationaryContinueMass]

/-- The silent row carries no terminal stage mass. -/
theorem fableSilentPadding_paddedParent_stageCoalitionMass_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingRootSequenceProfile reward
          (fablePostmarkPaddedRoots
            (quittingProfileLiveRoot reward profile)) 0) 0 terminal = 0 := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    fableSilentPadding_liveRoot_rootSequenceProfile,
    fablePostmarkPaddedRoots_zero]
  have hnonneg := quittingRootCoalitionMass_nonneg
    (quittingAllContinueRoot : ι → PMF Bool) terminal.val
  have hle := quittingRootCoalitionMass_le_absorptionMass_of_nonempty
    (quittingAllContinueRoot : ι → PMF Bool) terminal.val terminal.property
  rw [quittingRootAbsorptionMass_allContinueRoot] at hle
  have hzero : quittingRootCoalitionMass
      (quittingAllContinueRoot : ι → PMF Bool) terminal.val = 0 :=
    le_antisymm hle hnonneg
  rw [hzero, mul_zero]

/-- Every later stage mass of the padded parent is the source's own stage
mass one date earlier. -/
theorem fableSilentPadding_paddedParent_stageCoalitionMass_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) (time : ℕ) :
    quittingStageCoalitionMass reward
        (quittingRootSequenceProfile reward
          (fablePostmarkPaddedRoots
            (quittingProfileLiveRoot reward profile)) 0) (time + 1) terminal =
      quittingStageCoalitionMass reward profile time terminal := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    fableSilentPadding_liveRoot_rootSequenceProfile,
    fablePostmarkPaddedRoots_succ,
    fableSilentPadding_paddedParent_liveMass_succ]

/-- Law invariance: the silent prefix changes no terminal-law coordinate.
This is the third identity of the export's cap/payoff/law display. -/
theorem fableSilentPadding_paddedParent_absorbedMassLimit_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMassLimit reward
        (quittingRootSequenceProfile reward
          (fablePostmarkPaddedRoots
            (quittingProfileLiveRoot reward profile)) 0) terminal =
      quittingAbsorbedMassLimit reward profile terminal := by
  have hpadded := hasSum_quittingStageCoalitionMass reward
    (quittingRootSequenceProfile reward
      (fablePostmarkPaddedRoots (quittingProfileLiveRoot reward profile)) 0)
    terminal
  have hsplit := hpadded.summable.tsum_eq_zero_add
  rw [hpadded.tsum_eq,
    fableSilentPadding_paddedParent_stageCoalitionMass_zero] at hsplit
  rw [hsplit, zero_add]
  have hshift : ∀ time, quittingStageCoalitionMass reward
      (quittingRootSequenceProfile reward
        (fablePostmarkPaddedRoots
          (quittingProfileLiveRoot reward profile)) 0) (time + 1) terminal =
    quittingStageCoalitionMass reward profile time terminal :=
    fableSilentPadding_paddedParent_stageCoalitionMass_succ reward profile
      terminal
  simp only [hshift]
  exact tsum_quittingStageCoalitionMass reward profile terminal

/-! ## P5: cap neutrality -/

/-- Cap neutrality in hypothesis form.  If every player's singleton quitting
reward is strictly below that player's own unrestricted cap against the
source profile, the maximum in the cap formula collapses and the padded
parent's complete semantic pair is the source's own. -/
theorem fableSilentPadding_paddedParentPair_eq_of_singletonReward_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hcap : ∀ who, reward (quittingSingletonTerminal who) who <
      (quittingTerminalSemanticPair reward profile).2 who) :
    quittingRootSequenceTerminalSemanticPairAt reward
        (fablePostmarkPaddedRoots (quittingProfileLiveRoot reward profile)) 0 =
      quittingTerminalSemanticPair reward profile := by
  rw [fablePostmark_paddedParentPair_eq]
  apply Prod.ext
  · rfl
  · funext who
    exact max_eq_right (hcap who).le

/-- The production singleton margin at a positive global minimum, in the
additive form used by the cap-neutrality hypothesis: every coordinate of the
minimum's envelope clears that player's singleton quitting reward by the
whole minimum debt sum. -/
theorem fableSilentPadding_singletonReward_add_debtSum_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) (who : ι) :
    reward (quittingSingletonTerminal who) who +
        quittingTerminalSemanticDebtSum minimum ≤ minimum.2 who := by
  have hmargin := minimumTerminalSemantic_singletonMargin
    (reward := reward) minimum hminimumMem hminimumLe hminimumPos who
  linarith

/-- Connecting form: any profile whose envelope coordinates sit within the
minimum debt sum of the minimum's own envelope coordinates satisfies the
cap-neutrality hypothesis.  This is what makes that hypothesis available
eventually along a cap-convergent source sequence; the sequence-level
eventuality is not formed here. -/
theorem fableSilentPadding_singletonReward_lt_cap_of_near_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hnear : ∀ who, minimum.2 who - quittingTerminalSemanticDebtSum minimum <
      (quittingTerminalSemanticPair reward profile).2 who) (who : ι) :
    reward (quittingSingletonTerminal who) who <
      (quittingTerminalSemanticPair reward profile).2 who := by
  have hmargin := fableSilentPadding_singletonReward_add_debtSum_le reward
    minimum hminimumMem hminimumLe hminimumPos who
  have hclose := hnear who
  linarith

/-- Cap neutrality from the minimum quadruple: a source profile whose
envelope coordinates sit within the minimum debt sum of the minimum's own
gives the padded parent exactly the source's semantic pair. -/
theorem fableSilentPadding_paddedParentPair_eq_of_near_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hnear : ∀ who, minimum.2 who - quittingTerminalSemanticDebtSum minimum <
      (quittingTerminalSemanticPair reward profile).2 who) :
    quittingRootSequenceTerminalSemanticPairAt reward
        (fablePostmarkPaddedRoots (quittingProfileLiveRoot reward profile)) 0 =
      quittingTerminalSemanticPair reward profile :=
  fableSilentPadding_paddedParentPair_eq_of_singletonReward_lt reward profile
    (fun who => fableSilentPadding_singletonReward_lt_cap_of_near_minimum reward
      profile minimum hminimumMem hminimumLe hminimumPos hnear who)

/-! ## P6: coercivity and paid splice at the padded instance -/

/-- Production two-cut coercivity at the universal padded instance.  Either
the source's own canonical suffix pair at the selected window is off the
minimum by the production margin at hazard floor `chi`, or some payer's debt
at the source's own semantic pair exceeds
`(1 - exp (-chi)) * D / (2 * card)`. -/
theorem fableSilentPadding_offMinimum_or_exists_entryDebt_gt [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {χ : ℝ} (hχ : 0 < χ)
    (window : ℕ) (hpos : 0 < window)
    (hhazard : χ < ∑ time ∈ Finset.range window,
      ∑ who, quittingRootQuitRates
        (quittingProfileLiveRoot reward profile time) who)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    quittingTerminalSemanticDebtSum
          (quittingRootSequenceTerminalSemanticPairAt reward
            (quittingProfileLiveRoot reward profile) window) ≥
        quittingTerminalSemanticDebtSum minimum +
          (Real.exp χ - 1) / 2 * quittingTerminalSemanticDebtSum minimum ∨
      ∃ payer : ι,
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) payer >
          (1 - Real.exp (-χ)) *
            quittingTerminalSemanticDebtSum minimum / (2 * Fintype.card ι) := by
  rcases (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
      minimum hminimumMem hminimumLe
      hminimumPos).offMinimum_or_exists_entryDebt_gt with hoff | ⟨payer, hpayer⟩
  · have hoff' : quittingTerminalSemanticDebtSum
        (quittingRootSequenceTerminalSemanticPairAt reward
          (fablePostmarkPaddedRoots
            (quittingProfileLiveRoot reward profile)) (window + 1)) ≥
      quittingTerminalSemanticDebtSum minimum +
        (Real.exp χ - 1) / 2 *
          quittingTerminalSemanticDebtSum minimum := hoff
    rw [fablePostmark_paddedSemanticPairAt_succ_eq] at hoff'
    exact Or.inl hoff'
  · have hpayer' : quittingTerminalSemanticDebt
        (quittingRootSequenceTerminalSemanticPairAt reward
          (fablePostmarkPaddedRoots
            (quittingProfileLiveRoot reward profile)) 1) payer >
      (1 - Real.exp (-χ)) *
        quittingTerminalSemanticDebtSum minimum /
          (2 * Fintype.card ι) := hpayer
    rw [fablePostmark_paddedEntryPair_eq] at hpayer'
    exact Or.inr ⟨payer, hpayer'⟩

/-- Universal padded paid splice.  Either the source's own canonical suffix
pair at the selected window is off the minimum by the production margin, or
some payer has an actual behavioral replacement of the source's canonical
profile, spliced into the padded parent as one literal unilateral update that
leaves the silent row all-Continue, with conditional gain above
`K / (4 * card)`, updated payer debt at most `K / (4 * card)`, and
whole-profile gain against the source's own payoff -- exactly the padded
parent-level payer debt decrease -- above `K / (4 * card)` with no reach
factor, the entry reach being one.  Here `K = (1 - exp (-chi)) * D`. -/
theorem fableSilentPadding_offMinimum_or_exists_paidSplice [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {χ : ℝ} (hχ : 0 < χ)
    (window : ℕ) (hpos : 0 < window)
    (hhazard : χ < ∑ time ∈ Finset.range window,
      ∑ who, quittingRootQuitRates
        (quittingProfileLiveRoot reward profile time) who)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    quittingTerminalSemanticDebtSum
          (quittingRootSequenceTerminalSemanticPairAt reward
            (quittingProfileLiveRoot reward profile) window) ≥
        quittingTerminalSemanticDebtSum minimum +
          (Real.exp χ - 1) / 2 * quittingTerminalSemanticDebtSum minimum ∨
      ∃ payer : ι,
        ∃ deviation : (quittingGame reward).BehaviorStrategy payer,
          ∃ splice : (quittingGame reward).BehaviorProfile,
            splice = Function.update (quittingRootSequenceProfile reward
                (fablePostmarkPaddedRoots
                  (quittingProfileLiveRoot reward profile)) 0) payer
              (splice payer) ∧
            quittingProfileLiveRoot reward splice 0 =
              (quittingAllContinueRoot : ι → PMF Bool) ∧
            quittingTerminalPayoff reward
                  (Function.update (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 0) payer
                    deviation) payer -
                quittingTerminalPayoff reward
                  (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 0) payer >
              (1 - Real.exp (-χ)) *
                quittingTerminalSemanticDebtSum minimum /
                  (4 * Fintype.card ι) ∧
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (Function.update (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 0) payer
                    deviation)) payer ≤
              (1 - Real.exp (-χ)) *
                quittingTerminalSemanticDebtSum minimum /
                  (4 * Fintype.card ι) ∧
            quittingTerminalPayoff reward splice payer -
                quittingTerminalPayoff reward profile payer >
              (1 - Real.exp (-χ)) *
                quittingTerminalSemanticDebtSum minimum /
                  (4 * Fintype.card ι) ∧
            quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward
                    (quittingRootSequenceProfile reward
                      (fablePostmarkPaddedRoots
                        (quittingProfileLiveRoot reward profile)) 0)) payer -
                quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward splice) payer =
              quittingTerminalPayoff reward splice payer -
                quittingTerminalPayoff reward profile payer := by
  have hentryProfile :
      (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
        minimum hminimumMem hminimumLe hminimumPos).entryProfile =
        quittingRootSequenceProfile reward
          (quittingProfileLiveRoot reward profile) 0 :=
    fablePostmark_paddedRootSequenceProfile_succ reward
      (quittingProfileLiveRoot reward profile) 0
  rcases fableTwoCut_offMinimum_or_exists_paidSplice
      (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
        minimum hminimumMem hminimumLe hminimumPos) with
    hoff | ⟨payer, deviation, hgain, hdebt, hupdate, hparentGain, hparentDebt,
      hliteral⟩
  · have hoff' : quittingTerminalSemanticDebtSum
        (quittingRootSequenceTerminalSemanticPairAt reward
          (fablePostmarkPaddedRoots
            (quittingProfileLiveRoot reward profile)) (window + 1)) ≥
      quittingTerminalSemanticDebtSum minimum +
        (Real.exp χ - 1) / 2 *
          quittingTerminalSemanticDebtSum minimum := hoff
    rw [fablePostmark_paddedSemanticPairAt_succ_eq] at hoff'
    exact Or.inl hoff'
  · have hparent : quittingRootSequenceProfile reward
        (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
          minimum hminimumMem hminimumLe hminimumPos).roots 0 =
      quittingRootSequenceProfile reward
        (fablePostmarkPaddedRoots
          (quittingProfileLiveRoot reward profile)) 0 := rfl
    have hfloor : (fableSilentPaddingTwoCutBlock reward profile hχ window hpos
          hhazard minimum hminimumMem hminimumLe hminimumPos).reachFloor *
        (fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
          minimum hminimumMem hminimumLe hminimumPos).coerciveConstant =
      1 * ((1 - Real.exp (-χ)) *
        quittingTerminalSemanticDebtSum minimum) := rfl
    have hsilent : quittingProfileLiveRoot reward
        ((fableSilentPaddingTwoCutBlock reward profile hχ window hpos hhazard
          minimum hminimumMem hminimumLe hminimumPos).paidSpliceProfile payer
            deviation) 0 = (quittingAllContinueRoot : ι → PMF Bool) :=
      hliteral 0 Nat.zero_lt_one
    rw [hentryProfile] at hgain hdebt
    rw [hparent, fablePostmark_paddedParent_terminalPayoff_eq, hfloor,
      one_mul] at hparentGain
    rw [hparent, fablePostmark_paddedParent_terminalPayoff_eq] at hparentDebt
    exact Or.inr ⟨payer, deviation, _, hupdate, hsilent, hgain, hdebt,
      hparentGain, hparentDebt⟩

end GameTheory
