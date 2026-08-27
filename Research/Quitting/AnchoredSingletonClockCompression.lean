/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.SameStageEndpointMonodromy
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNonsingletonAntiDiffusion

/-!
# Anchored singleton-clock compression

This file isolates the profile-generic chronological calculation behind a
singleton terminal atom in a finite quitting game.  Starting from a fixed
behavior profile and anchor, the owner's conditional finite-stop law is
separated from the fixed prefix and the opponents' survival exposure.
Positive anchored singleton tail mass then determines its own least supported
owner date; no positive-date witness is supplied as an input.

At that least date, the source owner is already literally `Continue` between
the anchor and the date.  Replacing only that date by literal `Quit` therefore
concentrates at least the whole anchored singleton tail into one singleton
stage atom.  The replacement keeps all opponents, every off-date owner
behavior, the post-date live roots, and the owner's unrestricted continuation
best-response cap exactly unchanged.

This is a probability-law compression only.  It asserts no equilibrium,
near-minimality, debt, convergence, or target-side root-stack property.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The owner's conditional probability of first stopping at `offset` after
the anchor, conditional on reaching the anchor. -/
def quittingAnchoredOwnerFiniteStopMass
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ) : ℝ :=
  quittingHazardStopMass
    (fun shift => quittingBehaviorLiveHazard reward (profile who) (anchor + shift))
    offset

/-- The fixed source prefix and opponent survival exposure multiplying the
owner's conditional stop atom at an anchored singleton date. -/
def quittingAnchoredSingletonExposureMass
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ) : ℝ :=
  quittingHazardSurvival
      (quittingBehaviorLiveHazard reward (profile who)) anchor *
    ∏ other ∈ ({who} : Finset ι)ᶜ,
      quittingHazardSurvival
        (quittingBehaviorLiveHazard reward (profile other))
        (anchor + offset + 1)

/-- Total conditional finite-stop mass of the owner after the anchor. -/
def quittingAnchoredOwnerFiniteStopTotal
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ) : ℝ :=
  ∑' offset, quittingAnchoredOwnerFiniteStopMass profile who anchor offset

/-- The source's total singleton mass carried at dates on or after the anchor. -/
def quittingAnchoredSingletonTailMass
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ) : ℝ :=
  ∑' offset, quittingStageCoalitionMass reward profile (anchor + offset)
    (quittingSingletonTerminal who)

/-- The chronological singleton stage masses on and after the anchor form a
summable suffix of the complete time-disintegration series. -/
theorem summable_quittingAnchoredSingletonStageMass
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ) :
    Summable fun offset => quittingStageCoalitionMass reward profile
      (anchor + offset) (quittingSingletonTerminal who) := by
  have hfull :=
    (hasSum_quittingStageCoalitionMass reward profile
      (quittingSingletonTerminal who)).summable
  have hshift := (summable_nat_add_iff anchor).2 hfull
  simpa [Nat.add_comm] using hshift

/-- The anchored singleton tail is nonnegative. -/
theorem quittingAnchoredSingletonTailMass_nonneg
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ) :
    0 ≤ quittingAnchoredSingletonTailMass profile who anchor := by
  exact tsum_nonneg fun offset =>
    quittingStageCoalitionMass_nonneg reward profile (anchor + offset)
      (quittingSingletonTerminal who)

omit [DecidableEq ι] in
theorem quittingAnchoredOwnerFiniteStopMass_nonneg
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ) :
    0 ≤ quittingAnchoredOwnerFiniteStopMass profile who anchor offset :=
  quittingHazardStopMass_nonneg _ _

theorem quittingAnchoredSingletonExposureMass_nonneg
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ) :
    0 ≤ quittingAnchoredSingletonExposureMass profile who anchor offset := by
  apply mul_nonneg (quittingHazardSurvival_nonneg _ _)
  exact Finset.prod_nonneg fun other _ =>
    quittingHazardSurvival_nonneg
      (quittingBehaviorLiveHazard reward (profile other)) _

theorem quittingAnchoredSingletonExposureMass_le_one
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ) :
    quittingAnchoredSingletonExposureMass profile who anchor offset ≤ 1 := by
  apply mul_le_one₀ (quittingHazardSurvival_le_one _ _)
  · exact Finset.prod_nonneg fun other _ =>
      quittingHazardSurvival_nonneg
        (quittingBehaviorLiveHazard reward (profile other)) _
  · exact Finset.prod_le_one
      (fun other _ => quittingHazardSurvival_nonneg
        (quittingBehaviorLiveHazard reward (profile other)) _)
      (fun other _ => quittingHazardSurvival_le_one
        (quittingBehaviorLiveHazard reward (profile other)) _)

private theorem quittingHazardSurvival_add
    (hazard : ℕ → PMF Bool) (anchor offset : ℕ) :
    quittingHazardSurvival hazard (anchor + offset) =
      quittingHazardSurvival hazard anchor *
        quittingHazardSurvival (fun shift => hazard (anchor + shift)) offset := by
  simpa [quittingHazardSurvival, Math.survivalProduct, add_assoc] using
    Math.survivalProduct_add
      (fun time => (hazard time false).toReal) 0 anchor offset

/-- Exact anchored singleton factorization `stageMass = alpha * beta`. -/
theorem quittingStageCoalitionMass_singleton_eq_anchoredOwner_mul_exposure
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ) :
    quittingStageCoalitionMass reward profile (anchor + offset)
        (quittingSingletonTerminal who) =
      quittingAnchoredOwnerFiniteStopMass profile who anchor offset *
        quittingAnchoredSingletonExposureMass profile who anchor offset := by
  rw [quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct]
  simp only [quittingSingletonTerminal, Finset.prod_singleton,
    quittingBehaviorStoppingLaw_some_toReal]
  rw [quittingHazardStopMass_eq_survival_mul_stop,
    quittingHazardSurvival_add]
  unfold quittingAnchoredOwnerFiniteStopMass
    quittingAnchoredSingletonExposureMass
  rw [quittingHazardStopMass_eq_survival_mul_stop]
  ring

/-- The anchored singleton tail is the sum of the factored owner/exposure
atoms. -/
theorem quittingAnchoredSingletonTailMass_eq_tsum_mul
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ) :
    quittingAnchoredSingletonTailMass profile who anchor =
      ∑' offset, quittingAnchoredOwnerFiniteStopMass profile who anchor offset *
        quittingAnchoredSingletonExposureMass profile who anchor offset := by
  simp_rw [quittingAnchoredSingletonTailMass,
    quittingStageCoalitionMass_singleton_eq_anchoredOwner_mul_exposure]

/-- At anchor zero, the anchored tail is exactly the complete singleton
terminal-law coordinate. -/
@[simp] theorem quittingAnchoredSingletonTailMass_zero
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingAnchoredSingletonTailMass profile who 0 =
      quittingTerminalOutcomeMass reward profile
        (some (quittingSingletonTerminal who)) := by
  rw [quittingTerminalOutcomeMass_eq_timeDisintegration]
  simp [quittingAnchoredSingletonTailMass]

omit [DecidableEq ι] in
/-- The owner's anchored conditional stop atoms have exactly the complement
of its conditional Never mass. -/
theorem quittingAnchoredOwnerFiniteStopTotal_eq_one_sub_neverMass
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ) :
    quittingAnchoredOwnerFiniteStopTotal profile who anchor =
      1 - quittingHazardNeverMass
        (fun shift =>
          quittingBehaviorLiveHazard reward (profile who) (anchor + shift)) := by
  exact (hasSum_quittingHazardStopMass _).tsum_eq

omit [DecidableEq ι] in
theorem quittingAnchoredOwnerFiniteStopTotal_nonneg
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ) :
    0 ≤ quittingAnchoredOwnerFiniteStopTotal profile who anchor := by
  exact tsum_nonneg fun offset =>
    quittingAnchoredOwnerFiniteStopMass_nonneg profile who anchor offset

omit [DecidableEq ι] in
theorem quittingAnchoredOwnerFiniteStopTotal_le_one
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ) :
    quittingAnchoredOwnerFiniteStopTotal profile who anchor ≤ 1 := by
  rw [quittingAnchoredOwnerFiniteStopTotal_eq_one_sub_neverMass]
  linarith [quittingHazardNeverMass_nonneg
    (fun shift => quittingBehaviorLiveHazard reward (profile who) (anchor + shift))]

omit [DecidableEq ι] in
theorem summable_quittingAnchoredOwnerFiniteStopMass
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ) :
    Summable fun offset =>
      quittingAnchoredOwnerFiniteStopMass profile who anchor offset :=
  (hasSum_quittingHazardStopMass _).summable

/-- As the selected date moves later, the fixed source prefix and all
opponent-survival factors can only decrease. -/
theorem antitone_quittingAnchoredSingletonExposureMass
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ) :
    Antitone fun offset =>
      quittingAnchoredSingletonExposureMass profile who anchor offset := by
  intro first second hfirst
  unfold quittingAnchoredSingletonExposureMass
  apply mul_le_mul_of_nonneg_left _ (quittingHazardSurvival_nonneg _ _)
  apply Finset.prod_le_prod
  · intro other _
    exact quittingHazardSurvival_nonneg
      (quittingBehaviorLiveHazard reward (profile other)) _
  · intro other _
    apply antitone_quittingHazardSurvival
    omega

/-- Positive anchored singleton mass produces a positive owner stop atom;
the date is not an input certificate. -/
theorem exists_positive_quittingAnchoredOwnerFiniteStopMass
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ)
    (hpositive : 0 < quittingAnchoredSingletonTailMass profile who anchor) :
    ∃ offset, 0 < quittingAnchoredOwnerFiniteStopMass profile who anchor offset := by
  by_contra hnone
  push Not at hnone
  have hzero : ∀ offset,
      quittingAnchoredOwnerFiniteStopMass profile who anchor offset = 0 :=
    fun offset => le_antisymm (hnone offset)
      (quittingAnchoredOwnerFiniteStopMass_nonneg profile who anchor offset)
  rw [quittingAnchoredSingletonTailMass_eq_tsum_mul] at hpositive
  simp [hzero] at hpositive

/-- The least positive owner stop atom and vanishing of every earlier owner
stop atom. -/
theorem exists_least_positive_quittingAnchoredOwnerFiniteStopMass
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ)
    (hpositive : 0 < quittingAnchoredSingletonTailMass profile who anchor) :
    ∃ offset,
      0 < quittingAnchoredOwnerFiniteStopMass profile who anchor offset ∧
      ∀ earlier < offset,
        quittingAnchoredOwnerFiniteStopMass profile who anchor earlier = 0 := by
  have hexists := exists_positive_quittingAnchoredOwnerFiniteStopMass
    profile who anchor hpositive
  refine ⟨Nat.find hexists, Nat.find_spec hexists, ?_⟩
  intro earlier hearlier
  apply le_antisymm
  · apply le_of_not_gt
    intro hpositiveEarlier
    have hminimum := Nat.find_min' hexists hpositiveEarlier
    omega
  · exact quittingAnchoredOwnerFiniteStopMass_nonneg
      profile who anchor earlier

/-- Positive anchored singleton tail mass forces strictly positive total
conditional owner finite-stop mass. -/
theorem quittingAnchoredOwnerFiniteStopTotal_pos_of_tailMass_pos
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ)
    (hpositive : 0 < quittingAnchoredSingletonTailMass profile who anchor) :
    0 < quittingAnchoredOwnerFiniteStopTotal profile who anchor := by
  obtain ⟨offset, hstop⟩ :=
    exists_positive_quittingAnchoredOwnerFiniteStopMass
      profile who anchor hpositive
  exact (summable_quittingAnchoredOwnerFiniteStopMass profile who anchor).tsum_pos
    (fun index =>
      quittingAnchoredOwnerFiniteStopMass_nonneg profile who anchor index)
    offset hstop

omit [DecidableEq ι] in
/-- Before the least supported anchored owner stop date, the fixed source
owner is already literally pure `Continue` on the live history. -/
theorem quittingProfileLiveRoot_eq_pure_false_before_anchoredOwnerSupport
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ)
    (hzero : ∀ earlier < offset,
      quittingAnchoredOwnerFiniteStopMass profile who anchor earlier = 0) :
    ∀ earlier < offset,
      quittingProfileLiveRoot reward profile (anchor + earlier) who =
        PMF.pure false := by
  intro earlier hearlier
  induction earlier using Nat.strong_induction_on with
  | h earlier ih =>
      let shiftedHazard : ℕ → PMF Bool := fun shift =>
        quittingBehaviorLiveHazard reward (profile who) (anchor + shift)
      have hsurvival : quittingHazardSurvival shiftedHazard earlier = 1 := by
        rw [quittingHazardSurvival_eq_prod]
        apply Finset.prod_eq_one
        intro prior hprior
        have hpriorLt : prior < earlier := Finset.mem_range.mp hprior
        have hpure := ih prior hpriorLt (hpriorLt.trans hearlier)
        change shiftedHazard prior = PMF.pure false at hpure
        rw [hpure]
        simp
      have hmass := hzero earlier hearlier
      change quittingHazardStopMass shiftedHazard earlier = 0 at hmass
      rw [quittingHazardStopMass_eq_survival_mul_stop, hsurvival,
        one_mul] at hmass
      change shiftedHazard earlier = PMF.pure false
      exact eq_pure_false_of_apply_true_toReal_eq_zero _ hmass

/-- Weighted domination at the first supported owner date.  This is the
literal infinite-series inequality `m ≤ A * beta_k`. -/
theorem quittingAnchoredSingletonTailMass_le_total_mul_exposure
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ)
    (hzero : ∀ earlier < offset,
      quittingAnchoredOwnerFiniteStopMass profile who anchor earlier = 0) :
    quittingAnchoredSingletonTailMass profile who anchor ≤
      quittingAnchoredOwnerFiniteStopTotal profile who anchor *
        quittingAnchoredSingletonExposureMass profile who anchor offset := by
  let alpha : ℕ → ℝ := fun index =>
    quittingAnchoredOwnerFiniteStopMass profile who anchor index
  let beta : ℕ → ℝ := fun index =>
    quittingAnchoredSingletonExposureMass profile who anchor index
  have halpha0 : ∀ index, 0 ≤ alpha index := fun index =>
    quittingAnchoredOwnerFiniteStopMass_nonneg profile who anchor index
  have hbeta0 : ∀ index, 0 ≤ beta index := fun index =>
    quittingAnchoredSingletonExposureMass_nonneg profile who anchor index
  have halpha : Summable alpha :=
    summable_quittingAnchoredOwnerFiniteStopMass profile who anchor
  have hbeta : Antitone beta :=
    antitone_quittingAnchoredSingletonExposureMass profile who anchor
  have hdom : ∀ index, alpha index * beta index ≤ alpha index * beta offset := by
    intro index
    by_cases hbefore : index < offset
    · simp [alpha, hzero index hbefore]
    · exact mul_le_mul_of_nonneg_left (hbeta (Nat.le_of_not_gt hbefore))
        (halpha0 index)
  have hconstant : Summable fun index => alpha index * beta offset :=
    halpha.mul_right _
  have hweighted : Summable fun index => alpha index * beta index :=
    Summable.of_nonneg_of_le
      (fun index => mul_nonneg (halpha0 index) (hbeta0 index)) hdom hconstant
  rw [quittingAnchoredSingletonTailMass_eq_tsum_mul]
  change (∑' index, alpha index * beta index) ≤
    (∑' index, alpha index) * beta offset
  calc
    (∑' index, alpha index * beta index) ≤
        ∑' index, alpha index * beta offset :=
      hweighted.tsum_le_tsum hdom hconstant
    _ = (∑' index, alpha index) * beta offset := by rw [tsum_mul_right]

/-- The actual one-date target: only the owner is replaced, and only at the
selected anchored date, by literal `Quit`. -/
def quittingAnchoredSingletonQuitProfile
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralOneDateProfile reward profile who (anchor + offset) true

theorem quittingAnchoredSingletonQuitProfile_at_of_ne
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset time : ℕ) (htime : time ≠ anchor + offset) :
    ∀ player,
      quittingAnchoredSingletonQuitProfile profile who anchor offset player time =
        profile player time := by
  intro player
  by_cases hplayer : player = who
  · subst player
    simp only [quittingAnchoredSingletonQuitProfile,
      quittingLiteralOneDateProfile, Function.update_self]
    exact quittingLiteralOneDateOverride_of_ne
      (profile who) (anchor + offset) time true htime
  · simp [quittingAnchoredSingletonQuitProfile,
      quittingLiteralOneDateProfile, Function.update_of_ne hplayer]

/-- Every opponent's complete behavior strategy is literally unchanged. -/
theorem quittingAnchoredSingletonQuitProfile_opponent_eq
    (profile : (quittingGame reward).BehaviorProfile) (who other : ι)
    (anchor offset : ℕ) (hother : other ≠ who) :
    quittingAnchoredSingletonQuitProfile profile who anchor offset other =
      profile other := by
  simp [quittingAnchoredSingletonQuitProfile,
    quittingLiteralOneDateProfile, Function.update_of_ne hother]

/-- At the selected live row, the target owner literally quits surely. -/
theorem quittingAnchoredSingletonQuitProfile_owner_root_eq_pure_true
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ) :
    quittingProfileLiveRoot reward
        (quittingAnchoredSingletonQuitProfile profile who anchor offset)
        (anchor + offset) who = PMF.pure true := by
  rw [quittingAnchoredSingletonQuitProfile,
    quittingProfileLiveRoot_literalOneDateProfile]
  simp

/-- The complete post-selected-date live-root tail is copied literally. -/
theorem quittingAnchoredSingletonQuitProfile_liveRoot_tail_eq
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset shift : ℕ) :
    quittingProfileLiveRoot reward
        (quittingAnchoredSingletonQuitProfile profile who anchor offset)
        (anchor + offset + 1 + shift) =
      quittingProfileLiveRoot reward profile (anchor + offset + 1 + shift) := by
  exact quittingProfileLiveRoot_literalOneDateProfile_tail_eq
    profile who (anchor + offset) shift true

/-- The owner's unrestricted behavioral best-response cap is unchanged,
because the target changes only that owner's own behavior strategy. -/
theorem quittingAnchoredSingletonQuitProfile_owner_cap_eq
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ) :
    quittingContinuationBestResponseValue reward
        (quittingAnchoredSingletonQuitProfile profile who anchor offset) who =
      quittingContinuationBestResponseValue reward profile who :=
  quittingContinuationBestResponseValue_literalOneDateProfile_self_eq
    reward profile who (anchor + offset) true

private theorem quittingAnchoredSingletonQuitProfile_exposure_eq
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ) :
    quittingAnchoredSingletonExposureMass
        (quittingAnchoredSingletonQuitProfile profile who anchor offset)
        who anchor offset =
      quittingAnchoredSingletonExposureMass profile who anchor offset := by
  unfold quittingAnchoredSingletonExposureMass
  congr 1
  · rw [quittingHazardSurvival_eq_prod, quittingHazardSurvival_eq_prod]
    apply Finset.prod_congr rfl
    intro time htime
    have hlt : time < anchor := Finset.mem_range.mp htime
    have hne : time ≠ anchor + offset := by omega
    have hat := quittingAnchoredSingletonQuitProfile_at_of_ne
      profile who anchor offset time hne who
    change
      ((quittingAnchoredSingletonQuitProfile profile who anchor offset who)
          time (quittingLiveHist reward time) false).toReal = _
    rw [hat]
    rfl
  · apply Finset.prod_congr rfl
    intro other hother
    have hne : other ≠ who := by
      simpa using (Finset.mem_compl.mp hother)
    rw [quittingAnchoredSingletonQuitProfile_opponent_eq
      profile who other anchor offset hne]

private theorem quittingAnchoredOwnerFiniteStopMass_quitProfile_eq_one
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ)
    (hcontinue : ∀ earlier < offset,
      quittingProfileLiveRoot reward profile (anchor + earlier) who =
        PMF.pure false) :
    quittingAnchoredOwnerFiniteStopMass
        (quittingAnchoredSingletonQuitProfile profile who anchor offset)
        who anchor offset = 1 := by
  unfold quittingAnchoredOwnerFiniteStopMass
  rw [quittingHazardStopMass_eq_survival_mul_stop]
  have hsurvival : quittingHazardSurvival
      (fun shift => quittingBehaviorLiveHazard reward
        (quittingAnchoredSingletonQuitProfile profile who anchor offset who)
        (anchor + shift)) offset = 1 := by
    rw [quittingHazardSurvival_eq_prod]
    apply Finset.prod_eq_one
    intro earlier hearlier
    have hlt : earlier < offset := Finset.mem_range.mp hearlier
    have hne : anchor + earlier ≠ anchor + offset := by omega
    have hat := quittingAnchoredSingletonQuitProfile_at_of_ne
      profile who anchor offset (anchor + earlier) hne who
    change
      (((quittingAnchoredSingletonQuitProfile profile who anchor offset who)
          (anchor + earlier) (quittingLiveHist reward (anchor + earlier)))
          false).toReal = 1
    rw [hat]
    have hpure := hcontinue earlier hlt
    change
      ((quittingProfileLiveRoot reward profile (anchor + earlier) who false).toReal) = 1
    rw [hpure]
    simp
  rw [hsurvival, one_mul]
  have hquit :=
    quittingAnchoredSingletonQuitProfile_owner_root_eq_pure_true
      profile who anchor offset
  change
    ((quittingProfileLiveRoot reward
      (quittingAnchoredSingletonQuitProfile profile who anchor offset)
      (anchor + offset) who true).toReal) = 1
  rw [hquit]
  simp

/-- If the source owner already continues before the selected offset, the
literal one-date target's singleton stage mass is exactly the fixed-source
exposure `beta`. -/
theorem quittingStageCoalitionMass_anchoredSingletonQuitProfile_eq_exposure
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ)
    (hcontinue : ∀ earlier < offset,
      quittingProfileLiveRoot reward profile (anchor + earlier) who =
        PMF.pure false) :
    quittingStageCoalitionMass reward
        (quittingAnchoredSingletonQuitProfile profile who anchor offset)
        (anchor + offset) (quittingSingletonTerminal who) =
      quittingAnchoredSingletonExposureMass profile who anchor offset := by
  rw [quittingStageCoalitionMass_singleton_eq_anchoredOwner_mul_exposure,
    quittingAnchoredOwnerFiniteStopMass_quitProfile_eq_one
      profile who anchor offset hcontinue,
    quittingAnchoredSingletonQuitProfile_exposure_eq]
  simp

/-- At a positive selected owner atom, the division-free domination also
gives the packet's normalized lower bound `m / A ≤ beta`. -/
theorem quittingAnchoredSingletonTailMass_div_total_le_exposure
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ)
    (hstop : 0 < quittingAnchoredOwnerFiniteStopMass profile who anchor offset)
    (hzero : ∀ earlier < offset,
      quittingAnchoredOwnerFiniteStopMass profile who anchor earlier = 0) :
    quittingAnchoredSingletonTailMass profile who anchor /
        quittingAnchoredOwnerFiniteStopTotal profile who anchor ≤
      quittingAnchoredSingletonExposureMass profile who anchor offset := by
  have htotalPos : 0 < quittingAnchoredOwnerFiniteStopTotal profile who anchor := by
    exact (summable_quittingAnchoredOwnerFiniteStopMass profile who anchor).tsum_pos
      (fun index =>
        quittingAnchoredOwnerFiniteStopMass_nonneg profile who anchor index)
      offset hstop
  apply (div_le_iff₀ htotalPos).2
  simpa [mul_comm] using
    quittingAnchoredSingletonTailMass_le_total_mul_exposure
      profile who anchor offset hzero

/-- Since the conditional owner finite-stop mass is at most one, the selected
exposure dominates the entire anchored singleton tail. -/
theorem quittingAnchoredSingletonTailMass_le_exposure
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor offset : ℕ)
    (hzero : ∀ earlier < offset,
      quittingAnchoredOwnerFiniteStopMass profile who anchor earlier = 0) :
    quittingAnchoredSingletonTailMass profile who anchor ≤
      quittingAnchoredSingletonExposureMass profile who anchor offset := by
  calc
    quittingAnchoredSingletonTailMass profile who anchor ≤
        quittingAnchoredOwnerFiniteStopTotal profile who anchor *
          quittingAnchoredSingletonExposureMass profile who anchor offset :=
      quittingAnchoredSingletonTailMass_le_total_mul_exposure
        profile who anchor offset hzero
    _ ≤ 1 * quittingAnchoredSingletonExposureMass profile who anchor offset :=
      mul_le_mul_of_nonneg_right
        (quittingAnchoredOwnerFiniteStopTotal_le_one profile who anchor)
        (quittingAnchoredSingletonExposureMass_nonneg profile who anchor offset)
    _ = quittingAnchoredSingletonExposureMass profile who anchor offset := one_mul _

/-- **Anchored singleton clock compression.**  Positive source singleton tail
mass produces its own least owner stop offset and an actual literal one-date
Quit target.  The displayed conjunction contains both exact target mass and
the two packet lower bounds; the structural preservation laws are the named
target-profile theorems above. -/
theorem exists_quittingAnchoredSingletonClockCompression
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (anchor : ℕ)
    (hpositive : 0 < quittingAnchoredSingletonTailMass profile who anchor) :
    ∃ offset,
      0 < quittingAnchoredOwnerFiniteStopMass profile who anchor offset ∧
      (∀ earlier < offset,
        quittingAnchoredOwnerFiniteStopMass profile who anchor earlier = 0) ∧
      (∀ earlier < offset,
        quittingProfileLiveRoot reward profile (anchor + earlier) who =
          PMF.pure false) ∧
      quittingStageCoalitionMass reward
          (quittingAnchoredSingletonQuitProfile profile who anchor offset)
          (anchor + offset) (quittingSingletonTerminal who) =
        quittingAnchoredSingletonExposureMass profile who anchor offset ∧
      quittingAnchoredSingletonTailMass profile who anchor /
          quittingAnchoredOwnerFiniteStopTotal profile who anchor ≤
        quittingStageCoalitionMass reward
          (quittingAnchoredSingletonQuitProfile profile who anchor offset)
          (anchor + offset) (quittingSingletonTerminal who) ∧
      quittingAnchoredSingletonTailMass profile who anchor ≤
        quittingStageCoalitionMass reward
          (quittingAnchoredSingletonQuitProfile profile who anchor offset)
          (anchor + offset) (quittingSingletonTerminal who) := by
  obtain ⟨offset, hstop, hzero⟩ :=
    exists_least_positive_quittingAnchoredOwnerFiniteStopMass
      profile who anchor hpositive
  have hcontinue :=
    quittingProfileLiveRoot_eq_pure_false_before_anchoredOwnerSupport
      profile who anchor offset hzero
  have hstage :=
    quittingStageCoalitionMass_anchoredSingletonQuitProfile_eq_exposure
      profile who anchor offset hcontinue
  refine ⟨offset, hstop, hzero, hcontinue, hstage, ?_, ?_⟩
  · rw [hstage]
    exact quittingAnchoredSingletonTailMass_div_total_le_exposure
      profile who anchor offset hstop hzero
  · rw [hstage]
    exact quittingAnchoredSingletonTailMass_le_exposure
      profile who anchor offset hzero

/-- Summed post-anchor singleton mass transports exactly through a literal
finite root stack. -/
theorem tsum_quittingStageCoalitionMass_literalRootStack_postAnchor
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (who : ι) (anchor : ℕ) :
    (∑' offset,
      quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward roots terminal)
        (roots.length + (anchor + offset)) (quittingSingletonTerminal who)) =
      quittingCapNashStackContinueProduct roots *
        quittingAnchoredSingletonTailMass terminal who anchor := by
  have hsource : HasSum
      (fun offset => quittingStageCoalitionMass reward terminal
        (anchor + offset) (quittingSingletonTerminal who))
      (quittingAnchoredSingletonTailMass terminal who anchor) :=
    (summable_quittingAnchoredSingletonStageMass terminal who anchor).hasSum
  have hscaled :=
    hsource.mul_left (quittingCapNashStackContinueProduct roots)
  have htransported : HasSum
      (fun offset => quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward roots terminal)
        (roots.length + (anchor + offset)) (quittingSingletonTerminal who))
      (quittingCapNashStackContinueProduct roots *
        quittingAnchoredSingletonTailMass terminal who anchor) := by
    apply HasSum.congr_fun hscaled
    intro offset
    exact quittingStageCoalitionMass_literalRootStack_add_length reward roots
      terminal (anchor + offset) (quittingSingletonTerminal who)
  exact htransported.tsum_eq

end GameTheory
