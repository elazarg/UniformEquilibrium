/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourExactScaleResolution
import Research.Quitting.FinFourRationalFiniteClockProfileCompleteness
import Research.Quitting.FiniteClockDoubleFullGapCosource

/-!
# Rational Fin4 adapters for the double full-gap co-source

The real co-source is approximated inside its same finite-clock simplex while
the two selected pure candidates are held fixed.  For a rational reduced
threshold, continuity preserves both strict gains.  The resulting rational
payload has an exact Boolean checker and occurs at a finite index of a fair
enumeration.

The rational witnesses preserve the two literal gains, not exact cap
attainment.  Cap attainment belongs to the original real co-source and is not
stable under the rational perturbation.
-/

noncomputable section

namespace GameTheory

open Filter
open Math.ProbabilityMassFunction
open scoped Topology
open FinFourRationalFiniteClockProfileCompleteness

private theorem stoppingTimeToFiniteClockAtom_atomToStoppingTime
    (clockBound : ℕ) (atom : FiniteClockAtom clockBound) :
    stoppingTimeToFiniteClockAtom clockBound
        (finiteClockAtomToStoppingTime clockBound atom) = atom := by
  cases atom with
  | none => rfl
  | some time =>
      by_cases htime : time.val < clockBound
      · simp [finiteClockAtomToStoppingTime, stoppingTimeToFiniteClockAtom,
          htime]
      · have heq : time.val = clockBound := by omega
        simp [finiteClockAtomToStoppingTime, stoppingTimeToFiniteClockAtom,
          htime, finiteClockAuxAtom]
        apply Fin.ext
        exact heq.symm

/-- Proof-free rational co-source payload: one rational finite-clock profile,
two distinct player labels, and two same-clock pure candidates. -/
structure RationalFinFourDoubleGapCode where
  profile : RationalFinFourFiniteClockProfileCode
  first : Fin 4
  second : Fin 4
  firstCandidate : Option ℕ
  secondCandidate : Option ℕ
deriving DecidableEq, Repr

namespace RationalFinFourDoubleGapCode

/-- Decode the stored first date-or-Never response into the profile's finite
candidate alphabet, sending any late finite code to the auxiliary date. -/
def firstAtom (code : RationalFinFourDoubleGapCode) :
    FiniteClockAtom code.profile.clockBound :=
  stoppingTimeToFiniteClockAtom code.profile.clockBound code.firstCandidate

/-- Decode the stored second date-or-Never response into the profile's finite
candidate alphabet, sending any late finite code to the auxiliary date. -/
def secondAtom (code : RationalFinFourDoubleGapCode) :
    FiniteClockAtom code.profile.clockBound :=
  stoppingTimeToFiniteClockAtom code.profile.clockBound code.secondCandidate

/-- Exact validity and the two literal rational gain inequalities. -/
def Valid (reward : RationalFinFourRewardCode) (threshold : ℚ)
    (code : RationalFinFourDoubleGapCode) : Prop :=
    code.profile.Valid ∧
    code.first ≠ code.second ∧
    code.profile.payoff reward code.first + threshold ≤
      code.profile.deviationPayoff reward code.first code.firstAtom ∧
    code.profile.payoff reward code.second + threshold ≤
      code.profile.deviationPayoff reward code.second code.secondAtom

instance (reward : RationalFinFourRewardCode) (threshold : ℚ)
    (code : RationalFinFourDoubleGapCode) :
    Decidable (code.Valid reward threshold) := by
  unfold Valid
  infer_instance

/-- Executable exact verifier for the rational double-gap payload. -/
def verifies (reward : RationalFinFourRewardCode) (threshold : ℚ)
    (code : RationalFinFourDoubleGapCode) : Bool :=
  decide (code.Valid reward threshold)

theorem verifies_eq_true_iff (reward : RationalFinFourRewardCode)
    (threshold : ℚ) (code : RationalFinFourDoubleGapCode) :
    code.verifies reward threshold = true ↔ code.Valid reward threshold := by
  simp [verifies]

deriving instance Encodable for RationalFinFourDoubleGapCode

/-- The `stage`th proof-free rational double-gap candidate. -/
def candidateAt (stage : ℕ) : Option RationalFinFourDoubleGapCode :=
  Encodable.decode stage

/-- Exact enumeration, retaining only payloads accepted by the verifier. -/
def checkedCandidateAt (reward : RationalFinFourRewardCode)
    (threshold : ℚ) (stage : ℕ) : Option RationalFinFourDoubleGapCode :=
  match candidateAt stage with
  | none => none
  | some code => if code.verifies reward threshold then some code else none

theorem checkedCandidateAt_eq_some_iff
    (reward : RationalFinFourRewardCode) (threshold : ℚ) (stage : ℕ)
    (code : RationalFinFourDoubleGapCode) :
    checkedCandidateAt reward threshold stage = some code ↔
      candidateAt stage = some code ∧ code.Valid reward threshold := by
  cases hcandidate : candidateAt stage with
  | none => simp [checkedCandidateAt, hcandidate]
  | some candidate =>
      by_cases hvalid : candidate.Valid reward threshold
      · have hverifies : candidate.verifies reward threshold = true :=
          (candidate.verifies_eq_true_iff reward threshold).2 hvalid
        constructor
        · intro hout
          have heq : candidate = code := by
            simpa [checkedCandidateAt, hcandidate, hverifies] using hout
          subst code
          exact ⟨rfl, hvalid⟩
        · rintro ⟨hcode, -⟩
          have heq : candidate = code := Option.some.inj hcode
          subst code
          simp [checkedCandidateAt, hcandidate, hverifies]
      · have hverifies : candidate.verifies reward threshold = false := by
          rw [Bool.eq_false_iff]
          simpa [candidate.verifies_eq_true_iff reward threshold]
        constructor
        · intro hout
          simp [checkedCandidateAt, hcandidate, hverifies] at hout
        · rintro ⟨hcode, hcodeValid⟩
          have heq : candidate = code := Option.some.inj hcode
          subst code
          exact (hvalid hcodeValid).elim

/-- Every valid rational double-gap payload is found after finitely many
enumeration steps. -/
theorem exists_checkedCandidateAt_of_valid
    (reward : RationalFinFourRewardCode) (threshold : ℚ)
    (code : RationalFinFourDoubleGapCode)
    (hvalid : code.Valid reward threshold) :
    ∃ stage, checkedCandidateAt reward threshold stage = some code := by
  refine ⟨Encodable.encode code, ?_⟩
  apply checkedCandidateAt_eq_some_iff reward threshold _ code |>.2
  exact ⟨Encodable.encodek code, hvalid⟩

/-- A verified payload decodes to an actual finite-clock behavioral source
with the two displayed literal gains. -/
theorem semantic_sound
    (reward : RationalFinFourRewardCode) (threshold : ℚ)
    (code : RationalFinFourDoubleGapCode)
    (hvalid : code.Valid reward threshold) :
    code.first ≠ code.second ∧
      (threshold : ℝ) ≤
        quittingTerminalPayoff reward.realReward
            (Function.update
              (code.profile.toBehaviorProfile reward hvalid.1) code.first
              (quittingPureTimeBehaviorStrategy reward.realReward code.first
                (finiteClockAtomToStoppingTime code.profile.clockBound
                  code.firstAtom))) code.first -
          quittingTerminalPayoff reward.realReward
            (code.profile.toBehaviorProfile reward hvalid.1) code.first ∧
      (threshold : ℝ) ≤
        quittingTerminalPayoff reward.realReward
            (Function.update
              (code.profile.toBehaviorProfile reward hvalid.1) code.second
              (quittingPureTimeBehaviorStrategy reward.realReward code.second
                (finiteClockAtomToStoppingTime code.profile.clockBound
                  code.secondAtom))) code.second -
          quittingTerminalPayoff reward.realReward
            (code.profile.toBehaviorProfile reward hvalid.1) code.second := by
  refine ⟨hvalid.2.1, ?_, ?_⟩
  · have hgain := hvalid.2.2.1
    have hgainReal :
        (code.profile.payoff reward code.first : ℝ) + threshold ≤
          (code.profile.deviationPayoff reward code.first
            code.firstAtom : ℝ) := by
      exact_mod_cast hgain
    rw [code.profile.cast_payoff_eq_quittingTerminalPayoff reward hvalid.1,
      code.profile.cast_deviationPayoff_eq_quittingTerminalPayoff_update
        reward hvalid.1] at hgainReal
    linarith
  · have hgain := hvalid.2.2.2
    have hgainReal :
        (code.profile.payoff reward code.second : ℝ) + threshold ≤
          (code.profile.deviationPayoff reward code.second
            code.secondAtom : ℝ) := by
      exact_mod_cast hgain
    rw [code.profile.cast_payoff_eq_quittingTerminalPayoff reward hvalid.1,
      code.profile.cast_deviationPayoff_eq_quittingTerminalPayoff_update
        reward hvalid.1] at hgainReal
    linarith

end RationalFinFourDoubleGapCode

private theorem cast_rationalCode_payoff_eq_realPayoff
    (reward : RationalFinFourRewardCode) {clockBound : ℕ}
    (hclock : 0 < clockBound)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound))
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0)
    (level : ℕ) (player : Fin 4) :
    ((rationalCode weight level).payoff reward player : ℝ) =
      realPayoff reward clockBound
        (rationalApproximant
          ({ clockBound := clockBound
             clockBound_pos := hclock
             weight := weight
             weight_simplex := hweight
             auxiliary_eq_zero := haux } :
            RealFiniteClockProfile reward) level) player := by
  let source : RealFiniteClockProfile reward :=
    { clockBound := clockBound
      clockBound_pos := hclock
      weight := weight
      weight_simplex := hweight
      auxiliary_eq_zero := haux }
  let code := rationalCode weight level
  have hvalid : code.Valid :=
    rationalCode_valid hclock weight hweight haux level
  calc
    (code.payoff reward player : ℝ) =
        quittingTerminalPayoff reward.realReward
          (code.toBehaviorProfile reward hvalid) player :=
      code.cast_payoff_eq_quittingTerminalPayoff reward hvalid player
    _ = realPayoff reward code.clockBound code.realMass player := by
      rw [realPayoff_eq_terminalPayoff reward code.clockBound code.realMass
        (code.realMass_mem_stdSimplex hvalid)]
      rfl
    _ = realPayoff reward clockBound
        (rationalApproximant source level) player := by
      dsimp only [code]
      change realPayoff reward clockBound
        (rationalCode weight level).realMass player = _
      rw [rationalCode_realMass]
      rfl

private theorem cast_rationalCode_deviationPayoff_eq_realDeviationPayoff
    (reward : RationalFinFourRewardCode) {clockBound : ℕ}
    (hclock : 0 < clockBound)
    (weight : Fin 4 → FiniteClockAtom clockBound → ℝ)
    (hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound))
    (haux : ∀ player,
      weight player (finiteClockAuxAtom clockBound) = 0)
    (level : ℕ) (player : Fin 4)
    (candidate : FiniteClockAtom clockBound) :
    ((rationalCode weight level).deviationPayoff reward player candidate : ℝ) =
      realDeviationPayoff reward clockBound
        (rationalApproximant
          ({ clockBound := clockBound
             clockBound_pos := hclock
             weight := weight
             weight_simplex := hweight
             auxiliary_eq_zero := haux } :
            RealFiniteClockProfile reward) level) player candidate := by
  let source : RealFiniteClockProfile reward :=
    { clockBound := clockBound
      clockBound_pos := hclock
      weight := weight
      weight_simplex := hweight
      auxiliary_eq_zero := haux }
  let code := rationalCode weight level
  have hvalid : code.Valid :=
    rationalCode_valid hclock weight hweight haux level
  calc
    (code.deviationPayoff reward player candidate : ℝ) =
        quittingTerminalPayoff reward.realReward
          (Function.update (code.toBehaviorProfile reward hvalid) player
            (quittingPureTimeBehaviorStrategy reward.realReward player
              (finiteClockAtomToStoppingTime code.clockBound candidate)))
          player :=
      code.cast_deviationPayoff_eq_quittingTerminalPayoff_update
        reward hvalid player candidate
    _ = realDeviationPayoff reward code.clockBound code.realMass
        player candidate := by
      rw [realDeviationPayoff_eq_terminalPayoff_update reward
        code.clockBound code.realMass
        (code.realMass_mem_stdSimplex hvalid) player candidate]
      rfl
    _ = realDeviationPayoff reward clockBound
        (rationalApproximant source level) player candidate := by
      dsimp only [code]
      change realDeviationPayoff reward clockBound
        (rationalCode weight level).realMass player candidate = _
      rw [rationalCode_realMass]
      rfl

/-- Rational same-clock approximation preserves both selected strict gains
below a supplied rational threshold. -/
theorem exists_rationalFinFourDoubleGapCode
    (reward : RationalFinFourRewardCode) {gap : ℝ}
    (source : QuittingFiniteClockDoubleFullGapCosource reward.realReward gap)
    (threshold : ℚ) (hthreshold : (threshold : ℝ) < gap) :
    ∃ code : RationalFinFourDoubleGapCode,
      code.Valid reward threshold := by
  let realSource : RealFiniteClockProfile reward :=
    { clockBound := source.clockBound
      clockBound_pos := source.clockBound_pos
      weight := source.weight
      weight_simplex := source.weight_simplex
      auxiliary_eq_zero := source.auxiliary_eq_zero }
  have hweightTendsto := rationalApproximant_tendsto realSource
  have hfirstTendsto : Tendsto
      (fun level ↦
        realDeviationPayoff reward source.clockBound
            (rationalApproximant realSource level) source.first
            source.firstCandidate -
          realPayoff reward source.clockBound
            (rationalApproximant realSource level) source.first)
      atTop
      (nhds (realDeviationPayoff reward source.clockBound source.weight
          source.first source.firstCandidate -
        realPayoff reward source.clockBound source.weight source.first)) := by
    exact (((continuous_realDeviationPayoff reward source.clockBound
      source.first source.firstCandidate).sub
        (continuous_realPayoff reward source.clockBound source.first)).tendsto
          source.weight).comp hweightTendsto
  have hsecondTendsto : Tendsto
      (fun level ↦
        realDeviationPayoff reward source.clockBound
            (rationalApproximant realSource level) source.second
            source.secondCandidate -
          realPayoff reward source.clockBound
            (rationalApproximant realSource level) source.second)
      atTop
      (nhds (realDeviationPayoff reward source.clockBound source.weight
          source.second source.secondCandidate -
        realPayoff reward source.clockBound source.weight source.second)) := by
    exact (((continuous_realDeviationPayoff reward source.clockBound
      source.second source.secondCandidate).sub
        (continuous_realPayoff reward source.clockBound source.second)).tendsto
          source.weight).comp hweightTendsto
  have hfirstLimit : (threshold : ℝ) <
      realDeviationPayoff reward source.clockBound source.weight
          source.first source.firstCandidate -
        realPayoff reward source.clockBound source.weight source.first := by
    rw [realDeviationPayoff_eq_terminalPayoff_update reward
        source.clockBound source.weight source.weight_simplex,
      realPayoff_eq_terminalPayoff reward source.clockBound source.weight
        source.weight_simplex]
    linarith [source.first_gain]
  have hsecondLimit : (threshold : ℝ) <
      realDeviationPayoff reward source.clockBound source.weight
          source.second source.secondCandidate -
        realPayoff reward source.clockBound source.weight source.second := by
    rw [realDeviationPayoff_eq_terminalPayoff_update reward
        source.clockBound source.weight source.weight_simplex,
      realPayoff_eq_terminalPayoff reward source.clockBound source.weight
        source.weight_simplex]
    linarith [source.second_gain]
  have hfirstEventually : ∀ᶠ level in atTop,
      (threshold : ℝ) <
        realDeviationPayoff reward source.clockBound
            (rationalApproximant realSource level) source.first
            source.firstCandidate -
          realPayoff reward source.clockBound
            (rationalApproximant realSource level) source.first :=
    (tendsto_order.1 hfirstTendsto).1 _ hfirstLimit
  have hsecondEventually : ∀ᶠ level in atTop,
      (threshold : ℝ) <
        realDeviationPayoff reward source.clockBound
            (rationalApproximant realSource level) source.second
            source.secondCandidate -
          realPayoff reward source.clockBound
            (rationalApproximant realSource level) source.second :=
    (tendsto_order.1 hsecondTendsto).1 _ hsecondLimit
  obtain ⟨level, hfirst, hsecond⟩ :=
    (hfirstEventually.and hsecondEventually).exists
  let profileCode := rationalCode source.weight level
  let code : RationalFinFourDoubleGapCode :=
    { profile := profileCode
      first := source.first
      second := source.second
      firstCandidate :=
        finiteClockAtomToStoppingTime source.clockBound source.firstCandidate
      secondCandidate :=
        finiteClockAtomToStoppingTime source.clockBound source.secondCandidate }
  refine ⟨code, ?_⟩
  refine ⟨rationalCode_valid source.clockBound_pos source.weight
    source.weight_simplex source.auxiliary_eq_zero level,
    source.distinct, ?_, ?_⟩
  · have hpayoff := cast_rationalCode_payoff_eq_realPayoff reward
      source.clockBound_pos source.weight source.weight_simplex
      source.auxiliary_eq_zero level source.first
    have hdeviation := cast_rationalCode_deviationPayoff_eq_realDeviationPayoff
      reward source.clockBound_pos source.weight source.weight_simplex
      source.auxiliary_eq_zero level source.first source.firstCandidate
    have hfirstAtom : code.firstAtom = source.firstCandidate := by
      dsimp [code, profileCode, RationalFinFourDoubleGapCode.firstAtom]
      exact stoppingTimeToFiniteClockAtom_atomToStoppingTime
        source.clockBound source.firstCandidate
    change profileCode.payoff reward source.first + threshold ≤
      profileCode.deviationPayoff reward source.first code.firstAtom
    rw [hfirstAtom]
    have hreal :
        (profileCode.payoff reward source.first : ℝ) + threshold ≤
          (profileCode.deviationPayoff reward source.first
            source.firstCandidate : ℝ) := by
      rw [show (profileCode.payoff reward source.first : ℝ) =
          realPayoff reward source.clockBound
            (rationalApproximant realSource level) source.first by
        simpa only [profileCode] using hpayoff,
        show (profileCode.deviationPayoff reward source.first
            source.firstCandidate : ℝ) =
          realDeviationPayoff reward source.clockBound
            (rationalApproximant realSource level) source.first
            source.firstCandidate by
          simpa only [profileCode] using hdeviation]
      linarith
    exact_mod_cast hreal
  · have hpayoff := cast_rationalCode_payoff_eq_realPayoff reward
      source.clockBound_pos source.weight source.weight_simplex
      source.auxiliary_eq_zero level source.second
    have hdeviation := cast_rationalCode_deviationPayoff_eq_realDeviationPayoff
      reward source.clockBound_pos source.weight source.weight_simplex
      source.auxiliary_eq_zero level source.second source.secondCandidate
    have hsecondAtom : code.secondAtom = source.secondCandidate := by
      dsimp [code, profileCode, RationalFinFourDoubleGapCode.secondAtom]
      exact stoppingTimeToFiniteClockAtom_atomToStoppingTime
        source.clockBound source.secondCandidate
    change profileCode.payoff reward source.second + threshold ≤
      profileCode.deviationPayoff reward source.second code.secondAtom
    rw [hsecondAtom]
    have hreal :
        (profileCode.payoff reward source.second : ℝ) + threshold ≤
          (profileCode.deviationPayoff reward source.second
            source.secondCandidate : ℝ) := by
      rw [show (profileCode.payoff reward source.second : ℝ) =
          realPayoff reward source.clockBound
            (rationalApproximant realSource level) source.second by
        simpa only [profileCode] using hpayoff,
        show (profileCode.deviationPayoff reward source.second
            source.secondCandidate : ℝ) =
          realDeviationPayoff reward source.clockBound
            (rationalApproximant realSource level) source.second
            source.secondCandidate by
          simpa only [profileCode] using hdeviation]
      linarith
    exact_mod_cast hreal

/-- Exact rational enumeration terminates for every rational reduced
threshold strictly below the real full-gap co-source margin. -/
theorem exists_checkedRationalFinFourDoubleGapCode
    (reward : RationalFinFourRewardCode) {gap : ℝ}
    (source : QuittingFiniteClockDoubleFullGapCosource reward.realReward gap)
    (threshold : ℚ) (hthreshold : (threshold : ℝ) < gap) :
    ∃ stage code,
      RationalFinFourDoubleGapCode.checkedCandidateAt reward threshold stage =
        some code ∧
      code.Valid reward threshold := by
  obtain ⟨code, hvalid⟩ :=
    exists_rationalFinFourDoubleGapCode reward source threshold hthreshold
  obtain ⟨stage, hstage⟩ := code.exists_checkedCandidateAt_of_valid
    reward threshold hvalid
  exact ⟨stage, code, hstage, hvalid⟩

/-- A normalized Fin4 exact-scale lower certificate produces the packet's
real co-source at gap `epsilon / 8`. -/
theorem finFourExactScaleStep_lower_doubleFullGapCosource
    (reward : RationalFinFourRewardCode) {epsilon : ℚ}
    (hnormalized : reward.normalized = true) (hepsilon : 0 < epsilon)
    (stage rounds : ℕ) (tree : FinFourExactScaleLowerTree epsilon)
    (hstep : finFourExactScaleStep reward epsilon stage =
      some (.lower rounds tree)) :
    Nonempty (QuittingFiniteClockDoubleFullGapCosource reward.realReward
      ((epsilon : ℝ) / 8)) := by
  exact exists_quittingFiniteClockDoubleFullGapCosource reward.realReward
    (by exact_mod_cast (div_pos hepsilon (by norm_num : (0 : ℚ) < 8)))
    (finFourExactScaleStep_lower_terminalGap reward hnormalized hepsilon
      stage rounds tree hstep)

/-- At a normalized positive rational Fin4 lower certificate, exact
enumeration finds a rational co-source whose two selected gains are at least
`epsilon / 16`. -/
theorem finFourExactScaleStep_lower_exists_checkedDoubleGapCode
    (reward : RationalFinFourRewardCode) {epsilon : ℚ}
    (hnormalized : reward.normalized = true) (hepsilon : 0 < epsilon)
    (stage rounds : ℕ) (tree : FinFourExactScaleLowerTree epsilon)
    (hstep : finFourExactScaleStep reward epsilon stage =
      some (.lower rounds tree)) :
    ∃ searchStage code,
      RationalFinFourDoubleGapCode.checkedCandidateAt reward
          (epsilon / 16) searchStage = some code ∧
        code.Valid reward (epsilon / 16) := by
  obtain ⟨source⟩ := finFourExactScaleStep_lower_doubleFullGapCosource
    reward hnormalized hepsilon stage rounds tree hstep
  apply exists_checkedRationalFinFourDoubleGapCode reward source
  have hepsilonReal : (0 : ℝ) < epsilon := by exact_mod_cast hepsilon
  push_cast
  linarith

end GameTheory
