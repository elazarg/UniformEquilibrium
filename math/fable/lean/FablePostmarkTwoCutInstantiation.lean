/-
Postmark two-cut instantiation, section 4.

The atom-or-block producer of `FablePostmarkAtomBlock` reads two literal
alternatives off one behavior profile.  This file feeds each alternative into
the production `QuittingUniformlyReachedPostMarkTwoCutBlock` record and
applies the checked coercivity and paid-splice theorems to the result.

The production record is stated for a raw root sequence, not for a behavior
profile.  Both instantiations therefore use the canonical live-root word of
the source profile, whose history-independent profile has the same terminal
payoffs, the same unrestricted caps, and hence the same terminal semantic
pair as the source.  That equality is proved here.

Later arm: the block data supplies an exit cut `1 < e`, joint survival to
date one above `5 * mu / 8`, and total marginal quit rate over `[1, e)` above
`mu / 2`.  Take `markedRow = 0`, `entryCut = 1`, `exitCut = e`, and both the
reach and hazard floors equal to `mu / 2`.

Immediate arm: prefix one deterministic all-Continue row to the canonical
live-root word.  Take `markedRow = 0`, `entryCut = 1`, `exitCut = 2`, reach
floor one, and hazard floor `mu / 8`.  The entry suffix of the padded word is
literally the canonical word of the source, so the entry semantic pair is the
source's own.  The padding row is payoff-invisible but not cap-invisible: it
raises each envelope coordinate of the padded parent to that player's
singleton quitting reward when necessary.  Both facts are proved here, so the
immediate-arm parent gain is stated against the source's own payoff while the
parent debt stays the padded parent's.

Nothing here constructs the positive carrier minimum: it is supplied.  The
paid outputs are unilateral updates of the canonical parent profile and are
not asserted to be renewable children or to return to the minimum.
-/
import FablePostmarkAtomBlock
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveMinimumTwoCutPaidSplice
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchProfile
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryTailSemanticReduction

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Canonical live-root bridges -/

/-- Reading a profile through its canonical live-root word preserves its
complete terminal semantic pair. -/
theorem fableTwoCut_terminalSemanticPair_rootSequenceProfile_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward
          (quittingProfileLiveRoot reward profile) 0) =
      quittingTerminalSemanticPair reward profile := by
  apply Prod.ext
  · funext who
    exact (quittingTerminalPayoff_eq_rootSequence_profileLiveRoot
      reward profile who).symm
  · funext who
    change quittingContinuationBestResponseValue reward
        (quittingRootSequenceProfile reward
          (quittingProfileLiveRoot reward profile) 0) who =
      quittingContinuationBestResponseValue reward profile who
    simpa [quittingRootSequenceBestResponseValue] using
      (quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot
        reward profile who).symm

omit [DecidableEq ι] in
/-- Joint survival of the canonical live-root word from date zero is exactly
the profile's joint survival mass. -/
theorem fableTwoCut_jointSurvivalWeight_profileLiveRoot_eq_liveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (fuel : ℕ) :
    quittingJointSurvivalWeight (quittingProfileLiveRoot reward profile) 0 fuel =
      quittingLiveMass reward profile fuel := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [quittingJointSurvivalWeight_succ, ih, quittingLiveMass_succ,
        fablePostmark_jointContinueMass_eq_stationaryContinueMass]
      norm_num

/-! ## I1: the later-arm two-cut instance -/

/-- The later-arm postmark block: `markedRow = 0 < entryCut = 1 < exitCut`,
carried by the canonical live-root word of the source profile, with reach and
hazard floors both `mu / 2`.  The positive carrier minimum is supplied. -/
def fablePostmarkLaterArmTwoCutBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {μ : ℝ} (hμ : 0 < μ)
    (exitCut : ℕ) (hcut : 1 < exitCut)
    (hreach : 5 * μ / 8 < quittingLiveMass reward profile 1)
    (hhazard : μ / 2 < ∑ time ∈ Finset.Ico 1 exitCut,
      ∑ who, quittingRootQuitRates
        (quittingProfileLiveRoot reward profile time) who)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    QuittingUniformlyReachedPostMarkTwoCutBlock reward where
  roots := quittingProfileLiveRoot reward profile
  entryCut := 1
  exitCut := exitCut
  entryCut_lt_exitCut := hcut
  minimum := minimum
  minimum_mem := hminimumMem
  minimum_le := hminimumLe
  minimum_pos := hminimumPos
  markedRow := 0
  markedRow_lt_entryCut := Nat.zero_lt_one
  hazardFloor := μ / 2
  hazardFloor_pos := by linarith
  totalMarginalHazard_ge := by
    have hrange : ∑ time ∈ Finset.Ico 1 exitCut,
          ∑ who, quittingRootQuitRates
            (quittingProfileLiveRoot reward profile time) who =
        ∑ offset ∈ Finset.range (exitCut - 1),
          ∑ who, ((quittingProfileLiveRoot reward profile (1 + offset))
            who true).toReal := by
      rw [Finset.sum_Ico_eq_sum_range]
      rfl
    rw [hrange] at hhazard
    linarith
  reachFloor := μ / 2
  reachFloor_pos := by linarith
  entryReach_ge := by
    rw [fableTwoCut_jointSurvivalWeight_profileLiveRoot_eq_liveMass]
    linarith

section LaterArm

variable (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
  (profile : (quittingGame reward).BehaviorProfile) {μ : ℝ} (hμ : 0 < μ)
  (exitCut : ℕ) (hcut : 1 < exitCut)
  (hreach : 5 * μ / 8 < quittingLiveMass reward profile 1)
  (hhazard : μ / 2 < ∑ time ∈ Finset.Ico 1 exitCut,
    ∑ who, quittingRootQuitRates
      (quittingProfileLiveRoot reward profile time) who)
  (minimum : QuittingTerminalSemanticPair ι)
  (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
  (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate)
  (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)

@[simp] theorem fablePostmarkLaterArmTwoCutBlock_roots :
    (fablePostmarkLaterArmTwoCutBlock reward profile hμ exitCut hcut hreach
      hhazard minimum hminimumMem hminimumLe hminimumPos).roots =
      quittingProfileLiveRoot reward profile := rfl

@[simp] theorem fablePostmarkLaterArmTwoCutBlock_markedRow :
    (fablePostmarkLaterArmTwoCutBlock reward profile hμ exitCut hcut hreach
      hhazard minimum hminimumMem hminimumLe hminimumPos).markedRow = 0 := rfl

@[simp] theorem fablePostmarkLaterArmTwoCutBlock_entryCut :
    (fablePostmarkLaterArmTwoCutBlock reward profile hμ exitCut hcut hreach
      hhazard minimum hminimumMem hminimumLe hminimumPos).entryCut = 1 := rfl

@[simp] theorem fablePostmarkLaterArmTwoCutBlock_exitCut :
    (fablePostmarkLaterArmTwoCutBlock reward profile hμ exitCut hcut hreach
      hhazard minimum hminimumMem hminimumLe hminimumPos).exitCut =
      exitCut := rfl

@[simp] theorem fablePostmarkLaterArmTwoCutBlock_hazardFloor :
    (fablePostmarkLaterArmTwoCutBlock reward profile hμ exitCut hcut hreach
      hhazard minimum hminimumMem hminimumLe hminimumPos).hazardFloor =
      μ / 2 := rfl

@[simp] theorem fablePostmarkLaterArmTwoCutBlock_reachFloor :
    (fablePostmarkLaterArmTwoCutBlock reward profile hμ exitCut hcut hreach
      hhazard minimum hminimumMem hminimumLe hminimumPos).reachFloor =
      μ / 2 := rfl

@[simp] theorem fablePostmarkLaterArmTwoCutBlock_minimum :
    (fablePostmarkLaterArmTwoCutBlock reward profile hμ exitCut hcut hreach
      hhazard minimum hminimumMem hminimumLe hminimumPos).minimum =
      minimum := rfl

end LaterArm

/-- The checked block data of `FablePostmarkAtomBlock` supplies a production
post-mark two-cut block with the fixed later-arm fields. -/
theorem fablePostmark_exists_laterArmTwoCutBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {μ : ℝ} (hμ : 0 < μ)
    (hdata : FablePostmarkBlockData reward profile terminal μ)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ block : QuittingUniformlyReachedPostMarkTwoCutBlock reward,
      block.roots = quittingProfileLiveRoot reward profile ∧
        block.markedRow = 0 ∧ block.entryCut = 1 ∧ 1 < block.exitCut ∧
        block.hazardFloor = μ / 2 ∧ block.reachFloor = μ / 2 ∧
        block.minimum = minimum := by
  obtain ⟨exitCut, hcut, -, hreach, hhazard⟩ := hdata
  exact ⟨fablePostmarkLaterArmTwoCutBlock reward profile hμ exitCut hcut hreach
      hhazard minimum hminimumMem hminimumLe hminimumPos,
    rfl, rfl, rfl, hcut, rfl, rfl, rfl⟩

/-! ## I2: the later-arm coercivity output -/

/-- Production two-cut coercivity on the later-arm instance.  Either the
exit-suffix total debt exceeds the supplied minimum by
`(exp (mu / 2) - 1) / 2` times that minimum, or some payer's entry-suffix
debt exceeds `(1 - exp (-mu / 2)) * D / (2 * card)`.  The constants are the
production ones at `hazardFloor = mu / 2`. -/
theorem fablePostmarkLaterArm_offMinimum_or_exists_entryDebt_gt [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {μ : ℝ} (hμ : 0 < μ)
    (exitCut : ℕ) (hcut : 1 < exitCut)
    (hreach : 5 * μ / 8 < quittingLiveMass reward profile 1)
    (hhazard : μ / 2 < ∑ time ∈ Finset.Ico 1 exitCut,
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
            (quittingProfileLiveRoot reward profile) exitCut) ≥
        quittingTerminalSemanticDebtSum minimum +
          (Real.exp (μ / 2) - 1) / 2 *
            quittingTerminalSemanticDebtSum minimum ∨
      ∃ payer : ι,
        quittingTerminalSemanticDebt
            (quittingRootSequenceTerminalSemanticPairAt reward
              (quittingProfileLiveRoot reward profile) 1) payer >
          (1 - Real.exp (-(μ / 2))) *
            quittingTerminalSemanticDebtSum minimum / (2 * Fintype.card ι) :=
  (fablePostmarkLaterArmTwoCutBlock reward profile hμ exitCut hcut hreach
    hhazard minimum hminimumMem hminimumLe
    hminimumPos).offMinimum_or_exists_entryDebt_gt

/-! ## I3: the paid splice at cap tolerance `K / (4 * card)` -/

/-- General-index analogue of the production Fin4 paid-splice packaging.
At cap tolerance `K / (4 * card)` the entry-suffix replacement has
conditional gain above `K / (4 * card)` and updated entry-suffix payer debt
at most `K / (4 * card)`; the splice is one literal unilateral update of the
parent, its whole-profile gain exceeds `reachFloor * K / (4 * card)`, that
gain is exactly the parent-level payer debt decrease, and every live root
strictly before the entry cut is unchanged. -/
theorem fableTwoCut_offMinimum_or_exists_paidSplice [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (block : QuittingUniformlyReachedPostMarkTwoCutBlock reward) :
    quittingTerminalSemanticDebtSum block.exitPair ≥
        quittingTerminalSemanticDebtSum block.minimum +
          (Real.exp block.hazardFloor - 1) / 2 *
            quittingTerminalSemanticDebtSum block.minimum ∨
      ∃ payer : ι,
        ∃ deviation : (quittingGame reward).BehaviorStrategy payer,
          quittingTerminalPayoff reward
                (Function.update block.entryProfile payer deviation) payer -
              quittingTerminalPayoff reward block.entryProfile payer >
            block.coerciveConstant / (4 * Fintype.card ι) ∧
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (Function.update block.entryProfile payer deviation)) payer ≤
            block.coerciveConstant / (4 * Fintype.card ι) ∧
          block.paidSpliceProfile payer deviation =
            Function.update block.parentProfile payer
              (block.paidSpliceDeviation payer deviation) ∧
          quittingTerminalPayoff reward
                (block.paidSpliceProfile payer deviation) payer -
              quittingTerminalPayoff reward
                (quittingRootSequenceProfile reward block.roots 0) payer >
            block.reachFloor * block.coerciveConstant /
              (4 * Fintype.card ι) ∧
          quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (quittingRootSequenceProfile reward block.roots 0)) payer -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (block.paidSpliceProfile payer deviation)) payer =
            quittingTerminalPayoff reward
                (block.paidSpliceProfile payer deviation) payer -
              quittingTerminalPayoff reward
                (quittingRootSequenceProfile reward block.roots 0) payer ∧
          ∀ time < block.entryCut,
            quittingProfileLiveRoot reward
              (block.paidSpliceProfile payer deviation) time =
              block.roots time := by
  rcases block.offMinimum_or_exists_entryDebt_gt with hoff | ⟨payer, hpayer⟩
  · exact Or.inl hoff
  · right
    have hcard : (0 : ℝ) < Fintype.card ι := by
      exact_mod_cast Fintype.card_pos
    have hconstant := block.coerciveConstant_pos
    have htolerance : 0 < block.coerciveConstant / (4 * Fintype.card ι) := by
      positivity
    have hhalf : block.coerciveConstant / (2 * Fintype.card ι) -
        block.coerciveConstant / (4 * Fintype.card ι) =
          block.coerciveConstant / (4 * Fintype.card ι) := by
      field_simp
      ring
    have htolLt : block.coerciveConstant / (4 * Fintype.card ι) <
        block.coerciveConstant / (2 * Fintype.card ι) := by linarith
    obtain ⟨deviation, hgain, hdebt⟩ :=
      block.exists_paid_entrySuffixReplacement payer hpayer htolerance
    have hparent := block.paidSplice_gain_gt_reachFloor_mul
      payer deviation htolLt hgain
    rw [hhalf] at hgain hparent
    refine ⟨payer, deviation, hgain, hdebt,
      block.paidSpliceProfile_eq_parentProfile_update payer deviation, ?_, ?_,
      fun time htime => block.paidSplice_liveRoot_eq_of_lt payer deviation htime⟩
    · rw [mul_div_assoc]
      exact hparent
    · rw [block.parentDebt_sub_paidSpliceDebt_eq_entryReach_mul_suffixGain,
        block.paidSplice_payoffGain_eq_entryReach_mul_suffixGain]

/-- Later-arm paid splice.  Either the exit-suffix total debt is off the
minimum by the production margin, or some payer has an actual behavioral
replacement of the canonical date-one entry suffix, spliced into the
canonical parent as one literal unilateral update that leaves date zero
literal, whose conditional gain exceeds `K / (4 * card)`, whose updated
entry-suffix payer debt is at most `K / (4 * card)`, and whose whole-profile
gain -- exactly the parent-level payer debt decrease -- exceeds
`mu / 2 * K / (4 * card)`.  Here `K = (1 - exp (-mu / 2)) * D` is the
production coercive constant at hazard floor `mu / 2`. -/
theorem fablePostmarkLaterArm_offMinimum_or_exists_paidSplice [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {μ : ℝ} (hμ : 0 < μ)
    (exitCut : ℕ) (hcut : 1 < exitCut)
    (hreach : 5 * μ / 8 < quittingLiveMass reward profile 1)
    (hhazard : μ / 2 < ∑ time ∈ Finset.Ico 1 exitCut,
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
            (quittingProfileLiveRoot reward profile) exitCut) ≥
        quittingTerminalSemanticDebtSum minimum +
          (Real.exp (μ / 2) - 1) / 2 *
            quittingTerminalSemanticDebtSum minimum ∨
      ∃ payer : ι,
        ∃ deviation : (quittingGame reward).BehaviorStrategy payer,
          ∃ splice : (quittingGame reward).BehaviorProfile,
            splice = Function.update (quittingRootSequenceProfile reward
                (quittingProfileLiveRoot reward profile) 0) payer
              (splice payer) ∧
            (∀ time < 1, quittingProfileLiveRoot reward splice time =
              quittingProfileLiveRoot reward profile time) ∧
            quittingTerminalPayoff reward
                  (Function.update (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 1) payer
                    deviation) payer -
                quittingTerminalPayoff reward
                  (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 1) payer >
              (1 - Real.exp (-(μ / 2))) *
                quittingTerminalSemanticDebtSum minimum /
                  (4 * Fintype.card ι) ∧
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (Function.update (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 1) payer
                    deviation)) payer ≤
              (1 - Real.exp (-(μ / 2))) *
                quittingTerminalSemanticDebtSum minimum /
                  (4 * Fintype.card ι) ∧
            quittingTerminalPayoff reward splice payer -
                quittingTerminalPayoff reward
                  (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 0) payer >
              μ / 2 * ((1 - Real.exp (-(μ / 2))) *
                quittingTerminalSemanticDebtSum minimum) /
                  (4 * Fintype.card ι) ∧
            quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward
                    (quittingRootSequenceProfile reward
                      (quittingProfileLiveRoot reward profile) 0)) payer -
                quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward splice) payer =
              quittingTerminalPayoff reward splice payer -
                quittingTerminalPayoff reward
                  (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 0) payer := by
  have hsplice := fableTwoCut_offMinimum_or_exists_paidSplice
    (fablePostmarkLaterArmTwoCutBlock reward profile hμ exitCut hcut hreach
      hhazard minimum hminimumMem hminimumLe hminimumPos)
  rcases hsplice with hoff | ⟨payer, deviation, hgain, hdebt, hupdate,
    hparentGain, hparentDebt, hliteral⟩
  · exact Or.inl hoff
  · refine Or.inr ⟨payer, deviation, _, hupdate, hliteral, hgain, hdebt,
      hparentGain, hparentDebt⟩

/-! ## I4: the immediate-arm two-cut instance -/

/-- One deterministic all-Continue row prefixed to a root word. -/
def fablePostmarkPaddedRoots (roots : ℕ → ι → PMF Bool) :
    ℕ → ι → PMF Bool
  | 0 => quittingAllContinueRoot
  | step + 1 => roots step

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem fablePostmarkPaddedRoots_zero (roots : ℕ → ι → PMF Bool) :
    fablePostmarkPaddedRoots roots 0 = quittingAllContinueRoot := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem fablePostmarkPaddedRoots_succ
    (roots : ℕ → ι → PMF Bool) (step : ℕ) :
    fablePostmarkPaddedRoots roots (step + 1) = roots step := rfl

omit [DecidableEq ι] in
/-- The padding row is terminally silent: it has all-Continue mass one. -/
@[simp] theorem fableTwoCut_stationaryContinueMass_allContinueRoot :
    quittingStationaryContinueMass (quittingAllContinueRoot : ι → PMF Bool) =
      1 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [quittingAllContinueRoot]

omit [DecidableEq ι] in
/-- Every suffix of the padded word past the padding row is the corresponding
suffix of the original word. -/
theorem fablePostmark_paddedRootSequenceProfile_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : ℕ) :
    quittingRootSequenceProfile reward (fablePostmarkPaddedRoots roots)
        (start + 1) =
      quittingRootSequenceProfile reward roots start := by
  funext player time history
  show fablePostmarkPaddedRoots roots (start + 1 + time) player =
    roots (start + time) player
  rw [show start + 1 + time = start + time + 1 by omega]
  rfl

/-- The padded word's entry pair at date one is the source's own terminal
semantic pair. -/
theorem fablePostmark_paddedEntryPair_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingRootSequenceTerminalSemanticPairAt reward
        (fablePostmarkPaddedRoots (quittingProfileLiveRoot reward profile)) 1 =
      quittingTerminalSemanticPair reward profile := by
  unfold quittingRootSequenceTerminalSemanticPairAt
  rw [show (1 : ℕ) = 0 + 1 from rfl,
    fablePostmark_paddedRootSequenceProfile_succ,
    fableTwoCut_terminalSemanticPair_rootSequenceProfile_profileLiveRoot]

/-- The padded word's exit pair at date two is the source's date-one
canonical suffix pair. -/
theorem fablePostmark_paddedExitPair_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingRootSequenceTerminalSemanticPairAt reward
        (fablePostmarkPaddedRoots (quittingProfileLiveRoot reward profile)) 2 =
      quittingRootSequenceTerminalSemanticPairAt reward
        (quittingProfileLiveRoot reward profile) 1 := by
  unfold quittingRootSequenceTerminalSemanticPairAt
  rw [show (2 : ℕ) = 1 + 1 from rfl,
    fablePostmark_paddedRootSequenceProfile_succ]

/-- Exact action of the padding row on the source's semantic pair: the
prescribed payoff coordinate is unchanged, while each envelope coordinate is
raised to the corresponding singleton quitting reward when necessary.  So the
padding row is payoff-invisible but not, in general, cap-invisible. -/
theorem fablePostmark_paddedParentPair_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingRootSequenceTerminalSemanticPairAt reward
        (fablePostmarkPaddedRoots (quittingProfileLiveRoot reward profile)) 0 =
      ((quittingTerminalSemanticPair reward profile).1,
        fun who => max (reward (quittingSingletonTerminal who) who)
          ((quittingTerminalSemanticPair reward profile).2 who)) := by
  rw [quittingRootSequenceTerminalSemanticPairAt_eq_prefix,
    fablePostmarkPaddedRoots_zero, quittingTerminalSemanticPrefix_allContinue_eq,
    fablePostmark_paddedEntryPair_eq]

/-- The padded parent has exactly the source's terminal payoffs. -/
theorem fablePostmark_paddedParent_terminalPayoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
        (quittingRootSequenceProfile reward
          (fablePostmarkPaddedRoots
            (quittingProfileLiveRoot reward profile)) 0) who =
      quittingTerminalPayoff reward profile who :=
  congrFun (congrArg Prod.fst
    (fablePostmark_paddedParentPair_eq reward profile)) who

/-- Explicit padded-parent payer debt: the source's own envelope coordinate
raised to that player's singleton quitting reward, minus the source's own
prescribed payoff.  This is the exact price of the padding row. -/
theorem fablePostmark_paddedParent_debt_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalSemanticDebt
        (quittingRootSequenceTerminalSemanticPairAt reward
          (fablePostmarkPaddedRoots
            (quittingProfileLiveRoot reward profile)) 0) who =
      max (reward (quittingSingletonTerminal who) who)
          (quittingContinuationBestResponseValue reward profile who) -
        quittingTerminalPayoff reward profile who := by
  rw [fablePostmark_paddedParentPair_eq]
  rfl

/-- The immediate-arm postmark block.  The padding row is `markedRow = 0`,
the original date zero is the unique block row, `entryCut = 1 < exitCut = 2`,
the entry reach is one, and the hazard floor is the immediate atom
`mu / 8`. -/
def fablePostmarkImmediateArmTwoCutBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {μ : ℝ} (hμ : 0 < μ)
    (himmediate : μ / 8 ≤ quittingStageCoalitionMass reward profile 0 terminal)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    QuittingUniformlyReachedPostMarkTwoCutBlock reward where
  roots := fablePostmarkPaddedRoots (quittingProfileLiveRoot reward profile)
  entryCut := 1
  exitCut := 2
  entryCut_lt_exitCut := one_lt_two
  minimum := minimum
  minimum_mem := hminimumMem
  minimum_le := hminimumLe
  minimum_pos := hminimumPos
  markedRow := 0
  markedRow_lt_entryCut := Nat.zero_lt_one
  hazardFloor := μ / 8
  hazardFloor_pos := by linarith
  totalMarginalHazard_ge := by
    have hrates := fablePostmark_stageCoalitionMass_le_sum_quitRates
      reward profile 0 terminal
    show μ / 8 ≤ ∑ offset ∈ Finset.range (2 - 1),
      ∑ who, ((fablePostmarkPaddedRoots
        (quittingProfileLiveRoot reward profile) (1 + offset)) who true).toReal
    norm_num
    calc μ / 8 ≤ quittingStageCoalitionMass reward profile 0 terminal :=
          himmediate
      _ ≤ ∑ who, quittingRootQuitRates
            (quittingProfileLiveRoot reward profile 0) who := hrates
  reachFloor := 1
  reachFloor_pos := one_pos
  entryReach_ge := by
    show (1 : ℝ) ≤ quittingJointSurvivalWeight
      (fablePostmarkPaddedRoots (quittingProfileLiveRoot reward profile)) 0 1
    rw [quittingJointSurvivalWeight_succ]
    simp

/-- Production two-cut coercivity on the immediate-arm instance.  Either the
date-one canonical suffix total debt exceeds the supplied minimum by
`(exp (mu / 8) - 1) / 2` times that minimum, or some payer's debt at the
source's own semantic pair exceeds `(1 - exp (-mu / 8)) * D / (2 * card)`. -/
theorem fablePostmarkImmediateArm_offMinimum_or_exists_entryDebt_gt
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {μ : ℝ} (hμ : 0 < μ)
    (himmediate : μ / 8 ≤ quittingStageCoalitionMass reward profile 0 terminal)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    quittingTerminalSemanticDebtSum
          (quittingRootSequenceTerminalSemanticPairAt reward
            (quittingProfileLiveRoot reward profile) 1) ≥
        quittingTerminalSemanticDebtSum minimum +
          (Real.exp (μ / 8) - 1) / 2 *
            quittingTerminalSemanticDebtSum minimum ∨
      ∃ payer : ι,
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) payer >
          (1 - Real.exp (-(μ / 8))) *
            quittingTerminalSemanticDebtSum minimum / (2 * Fintype.card ι) := by
  rcases (fablePostmarkImmediateArmTwoCutBlock reward profile terminal hμ
      himmediate minimum hminimumMem hminimumLe
      hminimumPos).offMinimum_or_exists_entryDebt_gt with hoff | ⟨payer, hpayer⟩
  · have hoff' : quittingTerminalSemanticDebtSum
        (quittingRootSequenceTerminalSemanticPairAt reward
          (fablePostmarkPaddedRoots
            (quittingProfileLiveRoot reward profile)) 2) ≥
      quittingTerminalSemanticDebtSum minimum +
        (Real.exp (μ / 8) - 1) / 2 *
          quittingTerminalSemanticDebtSum minimum := hoff
    rw [fablePostmark_paddedExitPair_eq] at hoff'
    exact Or.inl hoff'
  · have hpayer' : quittingTerminalSemanticDebt
        (quittingRootSequenceTerminalSemanticPairAt reward
          (fablePostmarkPaddedRoots
            (quittingProfileLiveRoot reward profile)) 1) payer >
      (1 - Real.exp (-(μ / 8))) *
        quittingTerminalSemanticDebtSum minimum /
          (2 * Fintype.card ι) := hpayer
    rw [fablePostmark_paddedEntryPair_eq] at hpayer'
    exact Or.inr ⟨payer, hpayer'⟩

/-- Immediate-arm paid splice.  Either the date-one canonical suffix total
debt is off the minimum by the production margin, or some payer has an actual
behavioral replacement of the source's canonical profile, spliced into the
padded parent as one literal unilateral update that leaves the padding row
literal, with conditional gain above `K / (4 * card)`, updated payer debt at
most `K / (4 * card)`, and whole-profile gain -- exactly the parent-level
payer debt decrease -- above `1 * K / (4 * card)`, the entry reach being one.
Here `K = (1 - exp (-mu / 8)) * D` at hazard floor `mu / 8`. -/
theorem fablePostmarkImmediateArm_offMinimum_or_exists_paidSplice [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {μ : ℝ} (hμ : 0 < μ)
    (himmediate : μ / 8 ≤ quittingStageCoalitionMass reward profile 0 terminal)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    quittingTerminalSemanticDebtSum
          (quittingRootSequenceTerminalSemanticPairAt reward
            (quittingProfileLiveRoot reward profile) 1) ≥
        quittingTerminalSemanticDebtSum minimum +
          (Real.exp (μ / 8) - 1) / 2 *
            quittingTerminalSemanticDebtSum minimum ∨
      ∃ payer : ι,
        ∃ deviation : (quittingGame reward).BehaviorStrategy payer,
          ∃ splice : (quittingGame reward).BehaviorProfile,
            splice = Function.update (quittingRootSequenceProfile reward
                (fablePostmarkPaddedRoots
                  (quittingProfileLiveRoot reward profile)) 0) payer
              (splice payer) ∧
            quittingTerminalPayoff reward
                  (Function.update (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 0) payer
                    deviation) payer -
                quittingTerminalPayoff reward
                  (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 0) payer >
              (1 - Real.exp (-(μ / 8))) *
                quittingTerminalSemanticDebtSum minimum /
                  (4 * Fintype.card ι) ∧
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (Function.update (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 0) payer
                    deviation)) payer ≤
              (1 - Real.exp (-(μ / 8))) *
                quittingTerminalSemanticDebtSum minimum /
                  (4 * Fintype.card ι) ∧
            quittingTerminalPayoff reward splice payer -
                quittingTerminalPayoff reward profile payer >
              (1 - Real.exp (-(μ / 8))) *
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
      (fablePostmarkImmediateArmTwoCutBlock reward profile terminal hμ
        himmediate minimum hminimumMem hminimumLe hminimumPos).entryProfile =
        quittingRootSequenceProfile reward
          (quittingProfileLiveRoot reward profile) 0 :=
    fablePostmark_paddedRootSequenceProfile_succ reward
      (quittingProfileLiveRoot reward profile) 0
  rcases fableTwoCut_offMinimum_or_exists_paidSplice
      (fablePostmarkImmediateArmTwoCutBlock reward profile terminal hμ
        himmediate minimum hminimumMem hminimumLe hminimumPos) with
    hoff | ⟨payer, deviation, hgain, hdebt, hupdate, hparentGain, hparentDebt,
      -⟩
  · have hoff' : quittingTerminalSemanticDebtSum
        (quittingRootSequenceTerminalSemanticPairAt reward
          (fablePostmarkPaddedRoots
            (quittingProfileLiveRoot reward profile)) 2) ≥
      quittingTerminalSemanticDebtSum minimum +
        (Real.exp (μ / 8) - 1) / 2 *
          quittingTerminalSemanticDebtSum minimum := hoff
    rw [fablePostmark_paddedExitPair_eq] at hoff'
    exact Or.inl hoff'
  · have hparent : quittingRootSequenceProfile reward
        (fablePostmarkImmediateArmTwoCutBlock reward profile terminal hμ
          himmediate minimum hminimumMem hminimumLe hminimumPos).roots 0 =
      quittingRootSequenceProfile reward
        (fablePostmarkPaddedRoots
          (quittingProfileLiveRoot reward profile)) 0 := rfl
    have hfloor : (fablePostmarkImmediateArmTwoCutBlock reward profile terminal
          hμ himmediate minimum hminimumMem hminimumLe hminimumPos).reachFloor *
        (fablePostmarkImmediateArmTwoCutBlock reward profile terminal hμ
          himmediate minimum hminimumMem hminimumLe
          hminimumPos).coerciveConstant =
      1 * ((1 - Real.exp (-(μ / 8))) *
        quittingTerminalSemanticDebtSum minimum) := rfl
    rw [hentryProfile] at hgain hdebt
    rw [hparent, fablePostmark_paddedParent_terminalPayoff_eq, hfloor,
      one_mul] at hparentGain
    rw [hparent, fablePostmark_paddedParent_terminalPayoff_eq] at hparentDebt
    exact Or.inr ⟨payer, deviation, _, hupdate, hgain, hdebt, hparentGain,
      hparentDebt⟩

/-! ## Fin 4: the note's literal cap tolerance `K / 16` -/

/-- The production Fin4 paid-splice packaging on the later-arm instance, at
the note's cap tolerance `K / 16`.  The whole-profile gain, equal to the
exact parent-level payer debt decrease, exceeds `mu / 2 * K / 16`, that is
`mu * K / 32` with `K = (1 - exp (-mu / 2)) * D`. -/
theorem fablePostmarkLaterArm_finFour_offMinimum_or_exists_paidSplice
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (profile : (quittingGame reward).BehaviorProfile) {μ : ℝ} (hμ : 0 < μ)
    (exitCut : ℕ) (hcut : 1 < exitCut)
    (hreach : 5 * μ / 8 < quittingLiveMass reward profile 1)
    (hhazard : μ / 2 < ∑ time ∈ Finset.Ico 1 exitCut,
      ∑ who, quittingRootQuitRates
        (quittingProfileLiveRoot reward profile time) who)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    quittingTerminalSemanticDebtSum
          (quittingRootSequenceTerminalSemanticPairAt reward
            (quittingProfileLiveRoot reward profile) exitCut) ≥
        quittingTerminalSemanticDebtSum minimum +
          (Real.exp (μ / 2) - 1) / 2 *
            quittingTerminalSemanticDebtSum minimum ∨
      ∃ payer : Fin 4,
        ∃ deviation : (quittingGame reward).BehaviorStrategy payer,
          ∃ splice : (quittingGame reward).BehaviorProfile,
            splice = Function.update (quittingRootSequenceProfile reward
                (quittingProfileLiveRoot reward profile) 0) payer
              (splice payer) ∧
            (∀ time < 1, quittingProfileLiveRoot reward splice time =
              quittingProfileLiveRoot reward profile time) ∧
            quittingTerminalPayoff reward
                  (Function.update (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 1) payer
                    deviation) payer -
                quittingTerminalPayoff reward
                  (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 1) payer >
              (1 - Real.exp (-(μ / 2))) *
                quittingTerminalSemanticDebtSum minimum / 16 ∧
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (Function.update (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 1) payer
                    deviation)) payer ≤
              (1 - Real.exp (-(μ / 2))) *
                quittingTerminalSemanticDebtSum minimum / 16 ∧
            quittingTerminalPayoff reward splice payer -
                quittingTerminalPayoff reward
                  (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 0) payer >
              μ / 2 * ((1 - Real.exp (-(μ / 2))) *
                quittingTerminalSemanticDebtSum minimum) / 16 ∧
            quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward
                    (quittingRootSequenceProfile reward
                      (quittingProfileLiveRoot reward profile) 0)) payer -
                quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward splice) payer =
              quittingTerminalPayoff reward splice payer -
                quittingTerminalPayoff reward
                  (quittingRootSequenceProfile reward
                    (quittingProfileLiveRoot reward profile) 0) payer := by
  rcases (fablePostmarkLaterArmTwoCutBlock reward profile hμ exitCut hcut
      hreach hhazard minimum hminimumMem hminimumLe
      hminimumPos).finFour_offMinimum_or_exists_paidSplice with
    hoff | ⟨payer, deviation, hgain, hdebt, hupdate, hparentGain, hparentDebt,
      hliteral⟩
  · exact Or.inl hoff
  · exact Or.inr ⟨payer, deviation, _, hupdate, hliteral, hgain, hdebt,
      hparentGain, hparentDebt⟩

end GameTheory
