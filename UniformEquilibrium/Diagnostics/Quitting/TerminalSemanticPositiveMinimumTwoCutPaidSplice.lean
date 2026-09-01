import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CapDebtBellmanReduction
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingLaw
import UniformEquilibrium.Quitting.Terminal.TargetTail.TargetAnchoredTail

/-!
# Positive-minimum two-cut coercivity and paid behavioral splices

This module telescopes terminal semantic debt across one supplied finite
root-sequence block.  Positive total marginal hazard yields either a
quantitative off-minimum exit or a block-specific actual behavioral
replacement.  The replacement is spliced into the parent calendar as one
literal unilateral strategy update; its payoff gain is the exact decrease of
the payer's unrestricted terminal debt, and all behavior strictly before the
entry cut is unchanged.

This module treats literal executable suffix chains only.  It does not
formalize the packet's signed two-coordinate semantic-seam telescope.

Every result is conditional on supplied cuts, a positive carrier minimum,
a positive block-hazard floor, and a positive absolute entry-reach floor.
Nothing here constructs those data, attaches them to a source chronology,
makes the paid profile a renewable child, preserves ancestry, produces a
terminal equilibrium, or proves a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal terminal semantic pair of the root word beginning at `cut`. -/
def quittingRootSequenceTerminalSemanticPairAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cut : ℕ) :
    QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward
    (quittingRootSequenceProfile reward roots cut)

/-- Survival-weighted coordinate Nash charge over `[entryCut, entryCut + length)`. -/
def quittingTerminalSemanticCoordinateCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (entryCut length : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range length,
    quittingJointSurvivalWeight roots entryCut offset *
      quittingRootCoordinateNashDefect reward
        (quittingRootSequenceTerminalSemanticPairAt reward roots
          (entryCut + offset + 1)).2
        (roots (entryCut + offset)) who

/-- Survival-weighted total Nash charge over `[entryCut, entryCut + length)`. -/
def quittingTerminalSemanticTotalCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (entryCut length : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range length,
    quittingJointSurvivalWeight roots entryCut offset *
      quittingRootTotalNashDefect reward
        (quittingRootSequenceTerminalSemanticPairAt reward roots
          (entryCut + offset + 1)).2
        (roots (entryCut + offset))

theorem quittingRootSequenceTerminalSemanticPairAt_eq_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cut : ℕ) :
    quittingRootSequenceTerminalSemanticPairAt reward roots cut =
      quittingTerminalSemanticPrefix reward (roots cut)
        (quittingRootSequenceTerminalSemanticPairAt reward roots (cut + 1)) := by
  unfold quittingRootSequenceTerminalSemanticPairAt
  rw [quittingRootSequenceProfile_eq_rootThenContinuation,
    quittingTerminalSemanticPair_rootThenContinuation]

theorem quittingTerminalSemanticDebt_twoCut_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (entryCut length : ℕ) :
    quittingTerminalSemanticDebt
        (quittingRootSequenceTerminalSemanticPairAt reward roots entryCut) who =
      quittingTerminalSemanticCoordinateCharge reward roots who entryCut length +
        quittingJointSurvivalWeight roots entryCut length *
          quittingTerminalSemanticDebt
            (quittingRootSequenceTerminalSemanticPairAt reward roots
              (entryCut + length)) who := by
  induction length with
  | zero =>
      simp [quittingTerminalSemanticCoordinateCharge,
        quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  | succ length ih =>
      have hstep :=
        quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect
          reward
          (quittingRootSequenceTerminalSemanticPairAt reward roots
            (entryCut + length + 1))
          (roots (entryCut + length)) who
      rw [← quittingRootSequenceTerminalSemanticPairAt_eq_prefix reward roots
        (entryCut + length)] at hstep
      unfold quittingTerminalSemanticCoordinateCharge at ih ⊢
      rw [Finset.sum_range_succ, quittingJointSurvivalWeight_succ, ih, hstep]
      ring_nf

theorem quittingTerminalSemanticDebtSum_twoCut_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (entryCut length : ℕ) :
    quittingTerminalSemanticDebtSum
        (quittingRootSequenceTerminalSemanticPairAt reward roots entryCut) =
      quittingTerminalSemanticTotalCharge reward roots entryCut length +
        quittingJointSurvivalWeight roots entryCut length *
          quittingTerminalSemanticDebtSum
            (quittingRootSequenceTerminalSemanticPairAt reward roots
              (entryCut + length)) := by
  induction length with
  | zero =>
      simp [quittingTerminalSemanticTotalCharge,
        quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  | succ length ih =>
      have hstep :=
        quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect
          reward
          (quittingRootSequenceTerminalSemanticPairAt reward roots
            (entryCut + length + 1))
          (roots (entryCut + length))
      rw [← quittingRootSequenceTerminalSemanticPairAt_eq_prefix reward roots
        (entryCut + length)] at hstep
      unfold quittingTerminalSemanticTotalCharge at ih ⊢
      rw [Finset.sum_range_succ, quittingJointSurvivalWeight_succ, ih, hstep]
      ring_nf

theorem quittingTerminalSemanticTotalCharge_eq_sum_coordinateCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (entryCut length : ℕ) :
    quittingTerminalSemanticTotalCharge reward roots entryCut length =
      ∑ who, quittingTerminalSemanticCoordinateCharge
        reward roots who entryCut length := by
  unfold quittingTerminalSemanticTotalCharge
    quittingTerminalSemanticCoordinateCharge quittingRootTotalNashDefect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro offset _
  rw [Finset.mul_sum]

omit [DecidableEq ι] in
theorem quittingJointSurvivalWeight_le_exp_neg_totalMarginalHazard
    (roots : ℕ → ι → PMF Bool) (entryCut length : ℕ) :
    quittingJointSurvivalWeight roots entryCut length ≤
      Real.exp (-∑ offset ∈ Finset.range length,
        ∑ who, (roots (entryCut + offset) who true).toReal) := by
  rw [quittingJointSurvivalWeight_eq_prod]
  have hrow : ∀ offset ∈ Finset.range length,
      quittingStationaryContinueMass (roots (entryCut + offset)) ≤
        Real.exp (-∑ who,
          (roots (entryCut + offset) who true).toReal) := by
    intro offset _
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    calc
      (∏ who, (roots (entryCut + offset) who false).toReal) =
          ∏ who, (1 - (roots (entryCut + offset) who true).toReal) := by
        apply Finset.prod_congr rfl
        intro who _
        have hsum := quittingRoot_continueProbability_add_quitProbability
          (roots (entryCut + offset)) who
        linarith
      _ ≤ ∏ who, Real.exp (-(roots (entryCut + offset) who true).toReal) := by
        apply Finset.prod_le_prod
        · intro who _
          have hle : (roots (entryCut + offset) who true).toReal ≤ 1 := by
            rw [← ENNReal.toReal_one,
              ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by simp)]
            exact PMF.coe_le_one _ _
          positivity
        · intro who _
          exact Real.one_sub_le_exp_neg _
      _ = Real.exp (-∑ who,
          (roots (entryCut + offset) who true).toReal) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.sum_neg_distrib]
  calc
    (∏ offset ∈ Finset.range length,
        quittingStationaryContinueMass (roots (entryCut + offset))) ≤
        ∏ offset ∈ Finset.range length,
          Real.exp (-∑ who,
            (roots (entryCut + offset) who true).toReal) := by
      apply Finset.prod_le_prod
      · intro offset _
        exact quittingStationaryContinueMass_nonneg _
      · exact hrow
    _ = Real.exp (-∑ offset ∈ Finset.range length,
        ∑ who, (roots (entryCut + offset) who true).toReal) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.sum_neg_distrib]

/-- Minimal supplied two-cut data for the positive-minimum coercivity
identity.  This record has no marked row, reach floor, or hazard floor. -/
structure QuittingPositiveMinimumTwoCutBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  roots : ℕ → ι → PMF Bool
  entryCut : ℕ
  exitCut : ℕ
  entryCut_lt_exitCut : entryCut < exitCut
  minimum : QuittingTerminalSemanticPair ι
  minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward
  minimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate
  minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum

namespace QuittingPositiveMinimumTwoCutBlock

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  (block : QuittingPositiveMinimumTwoCutBlock reward)

def length : ℕ := block.exitCut - block.entryCut

def entryPair : QuittingTerminalSemanticPair ι :=
  quittingRootSequenceTerminalSemanticPairAt reward block.roots block.entryCut

def exitPair : QuittingTerminalSemanticPair ι :=
  quittingRootSequenceTerminalSemanticPairAt reward block.roots block.exitCut

theorem entryCut_add_length : block.entryCut + block.length = block.exitCut := by
  dsimp [length]
  exact Nat.add_sub_of_le block.entryCut_lt_exitCut.le

theorem entryPair_mem_carrier :
    block.entryPair ∈ quittingTerminalSemanticCarrier reward := by
  exact subset_closure
    ⟨quittingRootSequenceProfile reward block.roots block.entryCut, rfl⟩

theorem exitPair_mem_carrier :
    block.exitPair ∈ quittingTerminalSemanticCarrier reward := by
  exact subset_closure
    ⟨quittingRootSequenceProfile reward block.roots block.exitCut, rfl⟩

/-- Packet-literal arbitrary-survival coercivity.  The packet states this
for `theta < 1`; algebraically only nonnegativity of `theta` is needed. -/
theorem totalCharge_add_theta_mul_exitExcess_ge
    (theta : ℝ)
    (hsurvival :
      quittingJointSurvivalWeight block.roots block.entryCut block.length ≤
        theta) :
    quittingTerminalSemanticTotalCharge reward block.roots
          block.entryCut block.length +
        theta *
          (quittingTerminalSemanticDebtSum block.exitPair -
            quittingTerminalSemanticDebtSum block.minimum) ≥
      (1 - theta) * quittingTerminalSemanticDebtSum block.minimum := by
  have hentry := block.minimum_le block.entryPair block.entryPair_mem_carrier
  have hexit := block.minimum_le block.exitPair block.exitPair_mem_carrier
  have htel := quittingTerminalSemanticDebtSum_twoCut_eq
    reward block.roots block.entryCut block.length
  rw [block.entryCut_add_length] at htel
  have hminimum0 : 0 ≤ quittingTerminalSemanticDebtSum block.minimum :=
    block.minimum_pos.le
  have hexcess0 : 0 ≤ quittingTerminalSemanticDebtSum block.exitPair -
      quittingTerminalSemanticDebtSum block.minimum := sub_nonneg.mpr hexit
  have hsurvival0 := quittingJointSurvivalWeight_nonneg
    block.roots block.entryCut block.length
  have hsurvivalExcess :=
    mul_le_mul_of_nonneg_right hsurvival hexcess0
  have hthetaMinimum :
      (1 - theta) * quittingTerminalSemanticDebtSum block.minimum ≤
        (1 - quittingJointSurvivalWeight block.roots block.entryCut
          block.length) * quittingTerminalSemanticDebtSum block.minimum := by
    exact mul_le_mul_of_nonneg_right (by linarith) hminimum0
  dsimp [entryPair, exitPair] at hentry hexit htel ⊢
  nlinarith

end QuittingPositiveMinimumTwoCutBlock

/-- Supplied post-mark and uniformly reached extension of the minimal
two-cut coercivity data.  This record does not construct either cut and does
not assert that a paid output is a renewable child. -/
structure QuittingUniformlyReachedPostMarkTwoCutBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    extends QuittingPositiveMinimumTwoCutBlock reward where
  markedRow : ℕ
  markedRow_lt_entryCut : markedRow < entryCut
  hazardFloor : ℝ
  hazardFloor_pos : 0 < hazardFloor
  totalMarginalHazard_ge : hazardFloor ≤
    ∑ offset ∈ Finset.range (exitCut - entryCut),
      ∑ who, (roots (entryCut + offset) who true).toReal
  reachFloor : ℝ
  reachFloor_pos : 0 < reachFloor
  entryReach_ge : reachFloor ≤ quittingJointSurvivalWeight roots 0 entryCut

namespace QuittingUniformlyReachedPostMarkTwoCutBlock

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  (block : QuittingUniformlyReachedPostMarkTwoCutBlock reward)

def length : ℕ :=
  block.toQuittingPositiveMinimumTwoCutBlock.length

def entryPair : QuittingTerminalSemanticPair ι :=
  block.toQuittingPositiveMinimumTwoCutBlock.entryPair

def exitPair : QuittingTerminalSemanticPair ι :=
  block.toQuittingPositiveMinimumTwoCutBlock.exitPair

def coerciveConstant : ℝ :=
  (1 - Real.exp (-block.hazardFloor)) *
    quittingTerminalSemanticDebtSum block.minimum

theorem entryCut_add_length : block.entryCut + block.length = block.exitCut :=
  block.toQuittingPositiveMinimumTwoCutBlock.entryCut_add_length

theorem entryPair_mem_carrier :
    block.entryPair ∈ quittingTerminalSemanticCarrier reward :=
  block.toQuittingPositiveMinimumTwoCutBlock.entryPair_mem_carrier

theorem exitPair_mem_carrier :
    block.exitPair ∈ quittingTerminalSemanticCarrier reward :=
  block.toQuittingPositiveMinimumTwoCutBlock.exitPair_mem_carrier

theorem blockSurvival_le_exp_neg_hazardFloor :
    quittingJointSurvivalWeight block.roots block.entryCut block.length ≤
      Real.exp (-block.hazardFloor) := by
  have hproduct := quittingJointSurvivalWeight_le_exp_neg_totalMarginalHazard
    block.roots block.entryCut block.length
  apply hproduct.trans
  exact Real.exp_le_exp.mpr (neg_le_neg block.totalMarginalHazard_ge)

theorem totalCharge_add_exp_mul_exitExcess_ge_coerciveConstant :
    quittingTerminalSemanticTotalCharge reward block.roots
        block.entryCut block.length +
      Real.exp (-block.hazardFloor) *
        (quittingTerminalSemanticDebtSum block.exitPair -
          quittingTerminalSemanticDebtSum block.minimum) ≥
      block.coerciveConstant := by
  exact QuittingPositiveMinimumTwoCutBlock.totalCharge_add_theta_mul_exitExcess_ge
      block.toQuittingPositiveMinimumTwoCutBlock
      (Real.exp (-block.hazardFloor))
      block.blockSurvival_le_exp_neg_hazardFloor

theorem coerciveConstant_pos : 0 < block.coerciveConstant := by
  unfold coerciveConstant
  apply mul_pos
  · exact sub_pos.mpr <| Real.exp_lt_one_iff.mpr (neg_neg_of_pos block.hazardFloor_pos)
  · exact block.minimum_pos

theorem offMinimum_or_exists_entryDebt_gt [Nonempty ι] :
    quittingTerminalSemanticDebtSum block.exitPair ≥
        quittingTerminalSemanticDebtSum block.minimum +
          (Real.exp block.hazardFloor - 1) / 2 *
            quittingTerminalSemanticDebtSum block.minimum ∨
      ∃ payer : ι,
        quittingTerminalSemanticDebt block.entryPair payer >
          block.coerciveConstant / (2 * Fintype.card ι) := by
  by_cases hoff : quittingTerminalSemanticDebtSum block.exitPair ≥
      quittingTerminalSemanticDebtSum block.minimum +
        (Real.exp block.hazardFloor - 1) / 2 *
          quittingTerminalSemanticDebtSum block.minimum
  · exact Or.inl hoff
  · right
    have hoff' : quittingTerminalSemanticDebtSum block.exitPair -
        quittingTerminalSemanticDebtSum block.minimum <
      (Real.exp block.hazardFloor - 1) / 2 *
        quittingTerminalSemanticDebtSum block.minimum := by
      linarith
    have hexpProduct : Real.exp (-block.hazardFloor) *
        Real.exp block.hazardFloor = 1 := by
      rw [← Real.exp_add]
      simp
    have hhalf : Real.exp (-block.hazardFloor) *
          ((Real.exp block.hazardFloor - 1) / 2 *
            quittingTerminalSemanticDebtSum block.minimum) =
        block.coerciveConstant / 2 := by
      dsimp [coerciveConstant]
      calc
        Real.exp (-block.hazardFloor) *
            ((Real.exp block.hazardFloor - 1) / 2 *
              quittingTerminalSemanticDebtSum block.minimum) =
          ((Real.exp (-block.hazardFloor) * Real.exp block.hazardFloor -
              Real.exp (-block.hazardFloor)) / 2) *
            quittingTerminalSemanticDebtSum block.minimum := by ring
        _ = (1 - Real.exp (-block.hazardFloor)) *
              quittingTerminalSemanticDebtSum block.minimum / 2 := by
          rw [hexpProduct]
          ring
    have hexp0 : 0 < Real.exp (-block.hazardFloor) := Real.exp_pos _
    have hscaled : Real.exp (-block.hazardFloor) *
          (quittingTerminalSemanticDebtSum block.exitPair -
            quittingTerminalSemanticDebtSum block.minimum) <
        block.coerciveConstant / 2 := by
      rw [← hhalf]
      exact mul_lt_mul_of_pos_left hoff' hexp0
    have hcharge : block.coerciveConstant / 2 <
        quittingTerminalSemanticTotalCharge reward block.roots
          block.entryCut block.length := by
      have hcoercive := block.totalCharge_add_exp_mul_exitExcess_ge_coerciveConstant
      linarith
    have hcard0 : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hsumConstant :
        (∑ _who : ι, block.coerciveConstant /
            (2 * Fintype.card ι)) = block.coerciveConstant / 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    have hsumCharge :
        block.coerciveConstant / 2 <
          ∑ who, quittingTerminalSemanticCoordinateCharge reward block.roots
            who block.entryCut block.length := by
      rw [← quittingTerminalSemanticTotalCharge_eq_sum_coordinateCharge]
      exact hcharge
    rw [← hsumConstant] at hsumCharge
    obtain ⟨payer, -, hpayer⟩ := Finset.exists_lt_of_sum_lt hsumCharge
    refine ⟨payer, lt_of_lt_of_le hpayer ?_⟩
    have htel := quittingTerminalSemanticDebt_twoCut_eq reward block.roots payer
      block.entryCut block.length
    rw [block.entryCut_add_length] at htel
    have hexitDebt : 0 ≤ quittingTerminalSemanticDebt block.exitPair payer :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
        block.exitPair_mem_carrier payer
    have hsurvival := quittingJointSurvivalWeight_nonneg
      block.roots block.entryCut block.length
    dsimp [entryPair, exitPair,
      QuittingPositiveMinimumTwoCutBlock.entryPair,
      QuittingPositiveMinimumTwoCutBlock.exitPair] at htel hexitDebt ⊢
    nlinarith [mul_nonneg hsurvival hexitDebt]

def entryProfile : (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward block.roots block.entryCut

def parentProfile : (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward block.roots 0

def replacementSuffixRoots (payer : ι)
    (deviation : (quittingGame reward).BehaviorStrategy payer) :
    ℕ → ι → PMF Bool :=
  quittingRootSequenceUpdate
    (fun offset => block.roots (block.entryCut + offset)) payer
    (quittingBehaviorLiveHazard reward deviation)

def paidSpliceProfile (payer : ι)
    (deviation : (quittingGame reward).BehaviorStrategy payer) :
    (quittingGame reward).BehaviorProfile :=
  quittingPhaseSwitchProfile reward block.roots
    (block.replacementSuffixRoots payer deviation) block.entryCut

/-- The literal parent-level unilateral behavioral replacement whose update
is the paid splice. -/
def paidSpliceDeviation (payer : ι)
    (deviation : (quittingGame reward).BehaviorStrategy payer) :
    (quittingGame reward).BehaviorStrategy payer :=
  block.paidSpliceProfile payer deviation payer

theorem continuationBestResponseValue_update_self
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer) :
    quittingContinuationBestResponseValue reward
        (Function.update block.entryProfile payer deviation) payer =
      quittingContinuationBestResponseValue reward block.entryProfile payer := by
  unfold quittingContinuationBestResponseValue
  apply congrArg sSup
  congr 1
  funext replacement
  rw [Function.update_idem]

theorem exists_paid_entrySuffixReplacement
    (payer : ι)
    (hpayer : quittingTerminalSemanticDebt block.entryPair payer >
      block.coerciveConstant / (2 * Fintype.card ι))
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ deviation : (quittingGame reward).BehaviorStrategy payer,
      quittingTerminalPayoff reward
          (Function.update block.entryProfile payer deviation) payer -
          quittingTerminalPayoff reward block.entryProfile payer >
        block.coerciveConstant / (2 * Fintype.card ι) - tolerance ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update block.entryProfile payer deviation)) payer ≤
        tolerance := by
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub
      reward block.entryProfile payer htolerance
  refine ⟨deviation, ?_, ?_⟩
  · change quittingContinuationBestResponseValue reward block.entryProfile payer -
      quittingTerminalPayoff reward block.entryProfile payer >
        block.coerciveConstant / (2 * Fintype.card ι) at hpayer
    linarith
  · change quittingContinuationBestResponseValue reward
        (Function.update block.entryProfile payer deviation) payer -
      quittingTerminalPayoff reward
        (Function.update block.entryProfile payer deviation) payer ≤ tolerance
    rw [block.continuationBestResponseValue_update_self payer deviation]
    linarith

theorem replacementSuffixValue_eq_updated_entryProfile
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer) :
    quittingRootSequenceTerminalValue reward
        (block.replacementSuffixRoots payer deviation) payer 0 =
      quittingTerminalPayoff reward
        (Function.update block.entryProfile payer deviation) payer := by
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue]
  unfold replacementSuffixRoots quittingRootSequenceHazardTerminalValue
  congr 2

theorem paidSplice_payoffGain_eq_entryReach_mul_suffixGain
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer) :
    quittingTerminalPayoff reward
          (block.paidSpliceProfile payer deviation) payer -
        quittingTerminalPayoff reward
          (quittingRootSequenceProfile reward block.roots 0) payer =
      quittingJointSurvivalWeight block.roots 0 block.entryCut *
        (quittingTerminalPayoff reward
            (Function.update block.entryProfile payer deviation) payer -
          quittingTerminalPayoff reward block.entryProfile payer) := by
  change quittingRootSequenceTerminalValue reward
        (quittingPhaseSwitchRoots block.roots
          (block.replacementSuffixRoots payer deviation) block.entryCut) payer 0 -
      quittingRootSequenceTerminalValue reward block.roots payer 0 = _
  rw [quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots]
  rw [quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
    reward block.roots payer block.entryCut]
  rw [block.replacementSuffixValue_eq_updated_entryProfile payer deviation]
  change _ = quittingJointSurvivalWeight block.roots 0 block.entryCut *
    (_ - quittingRootSequenceTerminalValue reward block.roots payer block.entryCut)
  ring

theorem paidSplice_opponents_eq
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer)
    (time : ℕ) (other : ι) (hother : other ≠ payer) :
    quittingPhaseSwitchRoots block.roots
        (block.replacementSuffixRoots payer deviation) block.entryCut time other =
      block.roots time other := by
  by_cases htime : time < block.entryCut
  · rw [quittingPhaseSwitchRoots_of_lt _ _ htime]
  · have hle := Nat.not_lt.mp htime
    rw [quittingPhaseSwitchRoots_of_le _ _ hle]
    unfold replacementSuffixRoots quittingRootSequenceUpdate
    rw [Function.update_of_ne hother]
    change block.roots (block.entryCut + (time - block.entryCut)) other =
      block.roots time other
    rw [Nat.add_sub_of_le hle]

/-- The splice is literally one unilateral behavioral update of the parent
profile, not merely a root-sequence comparison. -/
theorem paidSpliceProfile_eq_parentProfile_update
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer) :
    block.paidSpliceProfile payer deviation =
      Function.update block.parentProfile payer
        (block.paidSpliceDeviation payer deviation) := by
  funext player time history
  by_cases hplayer : player = payer
  · subst player
    simp [paidSpliceDeviation]
  · rw [Function.update_of_ne hplayer]
    unfold paidSpliceProfile parentProfile quittingPhaseSwitchProfile
      quittingRootSequenceProfile
    rw [Nat.zero_add]
    exact block.paidSplice_opponents_eq payer deviation time player hplayer

/-- Every complete behavioral prescription strictly before the entry cut is
unchanged, for every player and every finite history. -/
theorem paidSpliceProfile_eq_parentProfile_of_lt
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer)
    (player : ι) {time : ℕ} (htime : time < block.entryCut)
    (history : (quittingGame reward).Hist time) :
    block.paidSpliceProfile payer deviation player time history =
      block.parentProfile player time history := by
  unfold paidSpliceProfile parentProfile quittingPhaseSwitchProfile
    quittingRootSequenceProfile
  rw [Nat.zero_add]
  change quittingPhaseSwitchRoots block.roots
      (block.replacementSuffixRoots payer deviation) block.entryCut time player =
    block.roots time player
  exact congrFun (quittingPhaseSwitchRoots_of_lt _ _ htime) player

/-- The actual parent deviation agrees with the parent's payer strategy at
every complete history strictly before the entry cut. -/
theorem paidSpliceDeviation_eq_parentProfile_of_lt
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer)
    {time : ℕ} (htime : time < block.entryCut)
    (history : (quittingGame reward).Hist time) :
    block.paidSpliceDeviation payer deviation time history =
      block.parentProfile payer time history := by
  exact block.paidSpliceProfile_eq_parentProfile_of_lt payer deviation payer
    htime history

theorem paidSplice_liveRoot_eq_of_lt
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer)
    {time : ℕ} (htime : time < block.entryCut) :
    quittingProfileLiveRoot reward
        (block.paidSpliceProfile payer deviation) time = block.roots time := by
  unfold paidSpliceProfile
  rw [quittingProfileLiveRoot_quittingPhaseSwitchProfile,
    quittingPhaseSwitchRoots_of_lt _ _ htime]

/-- Reaching any date through the entry cut has exactly the parent mass. -/
theorem paidSplice_liveMass_eq_of_le_entryCut
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer)
    {time : ℕ} (htime : time ≤ block.entryCut) :
    quittingLiveMass reward (block.paidSpliceProfile payer deviation) time =
      quittingLiveMass reward block.parentProfile time := by
  have hspliceRoot :
      quittingProfileLiveRoot reward (block.paidSpliceProfile payer deviation) =
        quittingPhaseSwitchRoots block.roots
          (block.replacementSuffixRoots payer deviation) block.entryCut := by
    unfold paidSpliceProfile
    exact quittingProfileLiveRoot_quittingPhaseSwitchProfile _ _ _ _
  have hparentRoot : quittingProfileLiveRoot reward block.parentProfile =
      block.roots := by
    unfold parentProfile
    exact quittingProfileLiveRoot_quittingRootSequenceProfile_zero _ _
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    hspliceRoot, hparentRoot]
  refine quittingJointSurvivalWeight_congr _ _ 0 time fun offset hoffset ↦ ?_
  rw [Nat.zero_add]
  exact quittingPhaseSwitchRoots_of_lt _ _ (lt_of_lt_of_le hoffset htime)

/-- The supplied entry-reach lower bound is the literal reach of both the
parent and its paid splice. -/
theorem entryReach_eq_paidSplice_liveMass
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer) :
    quittingJointSurvivalWeight block.roots 0 block.entryCut =
        quittingLiveMass reward block.parentProfile block.entryCut ∧
      quittingLiveMass reward block.parentProfile block.entryCut =
      quittingLiveMass reward (block.paidSpliceProfile payer deviation)
          block.entryCut := by
  have hparentRoot : quittingProfileLiveRoot reward block.parentProfile =
      block.roots := by
    unfold parentProfile
    exact quittingProfileLiveRoot_quittingRootSequenceProfile_zero _ _
  constructor
  · rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
      hparentRoot]
  · exact (block.paidSplice_liveMass_eq_of_le_entryCut payer deviation
      le_rfl).symm

/-- The supplied positive entry-reach floor is retained by the actual parent
splice. -/
theorem reachFloor_le_paidSplice_entryLiveMass
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer) :
    block.reachFloor ≤
      quittingLiveMass reward (block.paidSpliceProfile payer deviation)
        block.entryCut := by
  rw [← (block.entryReach_eq_paidSplice_liveMass payer deviation).2,
    ← (block.entryReach_eq_paidSplice_liveMass payer deviation).1]
  exact block.entryReach_ge

/-- The marked row is strictly pre-entry and hence its complete live root is
unchanged. -/
theorem paidSplice_markedRow_liveRoot_eq
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer) :
    quittingProfileLiveRoot reward (block.paidSpliceProfile payer deviation)
        block.markedRow =
      block.roots block.markedRow :=
  block.paidSplice_liveRoot_eq_of_lt payer deviation
    block.markedRow_lt_entryCut

/-- Every quitting-coalition terminal cylinder ending strictly before the
entry cut has exactly its parent mass. -/
theorem paidSplice_stageCoalitionMass_eq_of_lt
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer)
    {time : ℕ} (htime : time < block.entryCut)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward (block.paidSpliceProfile payer deviation)
        time terminal =
      quittingStageCoalitionMass reward block.parentProfile time terminal := by
  have hparentRoot : quittingProfileLiveRoot reward block.parentProfile =
      block.roots := by
    unfold parentProfile
    exact quittingProfileLiveRoot_quittingRootSequenceProfile_zero _ _
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    block.paidSplice_liveMass_eq_of_le_entryCut payer deviation htime.le,
    block.paidSplice_liveRoot_eq_of_lt payer deviation htime, hparentRoot]

/-- Each player's finite stopping-law atom strictly before the entry cut is
unchanged.  No `Never` or post-entry stopping-law claim is made. -/
theorem paidSplice_behaviorStoppingLaw_some_eq_of_lt
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer)
    (player : ι) {time : ℕ} (htime : time < block.entryCut) :
    (quittingBehaviorStoppingLaw reward
          (block.paidSpliceProfile payer deviation player) (some time)).toReal =
      (quittingBehaviorStoppingLaw reward
          (block.parentProfile player) (some time)).toReal := by
  rw [quittingBehaviorStoppingLaw_some_toReal,
    quittingBehaviorStoppingLaw_some_toReal]
  change quittingHazardStopMass
      (fun earlier ↦ quittingProfileLiveRoot reward
        (block.paidSpliceProfile payer deviation) earlier player) time =
    quittingHazardStopMass
      (fun earlier ↦ quittingProfileLiveRoot reward block.parentProfile
        earlier player) time
  unfold parentProfile
  rw [quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  rw [
    quittingHazardStopMass_eq_survival_mul_stop,
    quittingHazardStopMass_eq_survival_mul_stop]
  congr 1
  · rw [quittingHazardSurvival_eq_prod, quittingHazardSurvival_eq_prod]
    apply Finset.prod_congr rfl
    intro earlier hearlier
    have hearlierLt : earlier < block.entryCut :=
      (Finset.mem_range.mp hearlier).trans htime
    exact congrArg (fun root ↦ (root player false).toReal)
      (block.paidSplice_liveRoot_eq_of_lt payer deviation hearlierLt)
  · exact congrArg (fun root ↦ (root player true).toReal)
      (block.paidSplice_liveRoot_eq_of_lt payer deviation htime)

theorem paidSplice_continuationBestResponseValue_eq
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer) :
    quittingContinuationBestResponseValue reward
        (block.paidSpliceProfile payer deviation) payer =
      quittingContinuationBestResponseValue reward
        (quittingRootSequenceProfile reward block.roots 0) payer := by
  unfold quittingContinuationBestResponseValue
  apply congrArg sSup
  congr 1
  funext replacement
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue]
  apply quittingRootSequenceHazardTerminalValue_congr_of_opponents
  intro time other hother
  unfold paidSpliceProfile
  rw [quittingProfileLiveRoot_quittingPhaseSwitchProfile,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  exact block.paidSplice_opponents_eq payer deviation time other hother

theorem parentDebt_sub_paidSpliceDebt_eq_entryReach_mul_suffixGain
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer) :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingRootSequenceProfile reward block.roots 0)) payer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (block.paidSpliceProfile payer deviation)) payer =
      quittingJointSurvivalWeight block.roots 0 block.entryCut *
        (quittingTerminalPayoff reward
            (Function.update block.entryProfile payer deviation) payer -
          quittingTerminalPayoff reward block.entryProfile payer) := by
  unfold quittingTerminalSemanticDebt
  change
    quittingContinuationBestResponseValue reward
          (quittingRootSequenceProfile reward block.roots 0) payer -
        quittingTerminalPayoff reward
          (quittingRootSequenceProfile reward block.roots 0) payer -
      (quittingContinuationBestResponseValue reward
          (block.paidSpliceProfile payer deviation) payer -
        quittingTerminalPayoff reward
          (block.paidSpliceProfile payer deviation) payer) = _
  rw [block.paidSplice_continuationBestResponseValue_eq payer deviation]
  have hgain :=
    block.paidSplice_payoffGain_eq_entryReach_mul_suffixGain payer deviation
  linarith

theorem paidSplice_gain_gt_reachFloor_mul
    (payer : ι) (deviation : (quittingGame reward).BehaviorStrategy payer)
    {tolerance : ℝ}
    (htolerance : tolerance <
      block.coerciveConstant / (2 * Fintype.card ι))
    (hsuffixGain : quittingTerminalPayoff reward
          (Function.update block.entryProfile payer deviation) payer -
        quittingTerminalPayoff reward block.entryProfile payer >
      block.coerciveConstant / (2 * Fintype.card ι) - tolerance) :
    quittingTerminalPayoff reward
          (block.paidSpliceProfile payer deviation) payer -
        quittingTerminalPayoff reward
          (quittingRootSequenceProfile reward block.roots 0) payer >
      block.reachFloor *
        (block.coerciveConstant / (2 * Fintype.card ι) - tolerance) := by
  let lower := block.coerciveConstant / (2 * Fintype.card ι) - tolerance
  have hlower : 0 < lower := sub_pos.mpr htolerance
  have hreach : 0 < quittingJointSurvivalWeight block.roots 0 block.entryCut :=
    lt_of_lt_of_le block.reachFloor_pos block.entryReach_ge
  rw [block.paidSplice_payoffGain_eq_entryReach_mul_suffixGain payer deviation]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right block.entryReach_ge hlower.le)
    (mul_lt_mul_of_pos_left hsuffixGain hreach)

theorem offMinimum_or_exists_paidSplice [Nonempty ι] :
    quittingTerminalSemanticDebtSum block.exitPair ≥
        quittingTerminalSemanticDebtSum block.minimum +
          (Real.exp block.hazardFloor - 1) / 2 *
            quittingTerminalSemanticDebtSum block.minimum ∨
      ∃ payer : ι, ∀ tolerance > 0,
        ∃ deviation : (quittingGame reward).BehaviorStrategy payer,
          quittingTerminalPayoff reward
              (Function.update block.entryProfile payer deviation) payer -
              quittingTerminalPayoff reward block.entryProfile payer >
            block.coerciveConstant / (2 * Fintype.card ι) - tolerance ∧
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (Function.update block.entryProfile payer deviation)) payer ≤
            tolerance ∧
          block.paidSpliceProfile payer deviation =
            Function.update block.parentProfile payer
              (block.paidSpliceDeviation payer deviation) ∧
          quittingTerminalPayoff reward
                (block.paidSpliceProfile payer deviation) payer -
              quittingTerminalPayoff reward
                (quittingRootSequenceProfile reward block.roots 0) payer =
            quittingJointSurvivalWeight block.roots 0 block.entryCut *
              (quittingTerminalPayoff reward
                  (Function.update block.entryProfile payer deviation) payer -
                quittingTerminalPayoff reward block.entryProfile payer) ∧
          quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (quittingRootSequenceProfile reward block.roots 0)) payer -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (block.paidSpliceProfile payer deviation)) payer =
            quittingJointSurvivalWeight block.roots 0 block.entryCut *
              (quittingTerminalPayoff reward
                  (Function.update block.entryProfile payer deviation) payer -
                quittingTerminalPayoff reward block.entryProfile payer) := by
  rcases block.offMinimum_or_exists_entryDebt_gt with hoff | ⟨payer, hpayer⟩
  · exact Or.inl hoff
  · right
    refine ⟨payer, fun tolerance htolerance => ?_⟩
    obtain ⟨deviation, hgain, hdebt⟩ :=
      block.exists_paid_entrySuffixReplacement payer hpayer htolerance
    exact ⟨deviation, hgain, hdebt,
      block.paidSpliceProfile_eq_parentProfile_update payer deviation,
      block.paidSplice_payoffGain_eq_entryReach_mul_suffixGain payer deviation,
      block.parentDebt_sub_paidSpliceDebt_eq_entryReach_mul_suffixGain
        payer deviation⟩

theorem finFour_offMinimum_or_exists_paidSplice
    {reward4 : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (block : QuittingUniformlyReachedPostMarkTwoCutBlock reward4) :
    quittingTerminalSemanticDebtSum block.exitPair ≥
        quittingTerminalSemanticDebtSum block.minimum +
          (Real.exp block.hazardFloor - 1) / 2 *
            quittingTerminalSemanticDebtSum block.minimum ∨
      ∃ payer : Fin 4,
        ∃ deviation : (quittingGame reward4).BehaviorStrategy payer,
          quittingTerminalPayoff reward4
              (Function.update block.entryProfile payer deviation) payer -
              quittingTerminalPayoff reward4 block.entryProfile payer >
            block.coerciveConstant / 16 ∧
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward4
                (Function.update block.entryProfile payer deviation)) payer ≤
            block.coerciveConstant / 16 ∧
          block.paidSpliceProfile payer deviation =
            Function.update block.parentProfile payer
              (block.paidSpliceDeviation payer deviation) ∧
          quittingTerminalPayoff reward4
                (block.paidSpliceProfile payer deviation) payer -
              quittingTerminalPayoff reward4
                (quittingRootSequenceProfile reward4 block.roots 0) payer >
            block.reachFloor * block.coerciveConstant / 16 ∧
          quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward4
                  (quittingRootSequenceProfile reward4 block.roots 0)) payer -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward4
                  (block.paidSpliceProfile payer deviation)) payer =
            quittingTerminalPayoff reward4
                (block.paidSpliceProfile payer deviation) payer -
              quittingTerminalPayoff reward4
                (quittingRootSequenceProfile reward4 block.roots 0) payer ∧
          ∀ time < block.entryCut,
            quittingProfileLiveRoot reward4
              (block.paidSpliceProfile payer deviation) time = block.roots time := by
  rcases block.offMinimum_or_exists_entryDebt_gt with hoff | ⟨payer, hpayer⟩
  · exact Or.inl hoff
  · right
    have htolerance : 0 < block.coerciveConstant / 16 := by
      positivity [block.coerciveConstant_pos]
    obtain ⟨deviation, hgain, hdebt⟩ :=
      block.exists_paid_entrySuffixReplacement payer hpayer htolerance
    have hgain' : quittingTerminalPayoff reward4
          (Function.update block.entryProfile payer deviation) payer -
        quittingTerminalPayoff reward4 block.entryProfile payer >
          block.coerciveConstant / 16 := by
      simp only [Fintype.card_fin, Nat.cast_ofNat] at hgain
      convert hgain using 1
      ring_nf
    have htolLt : block.coerciveConstant / 16 <
        block.coerciveConstant / (2 * Fintype.card (Fin 4)) := by
      simp only [Fintype.card_fin, Nat.cast_ofNat]
      nlinarith [block.coerciveConstant_pos]
    have hparent := block.paidSplice_gain_gt_reachFloor_mul
      payer deviation htolLt hgain
    refine ⟨payer, deviation, hgain', hdebt,
      block.paidSpliceProfile_eq_parentProfile_update payer deviation,
      ?_, ?_, ?_⟩
    · simp only [Fintype.card_fin, Nat.cast_ofNat] at hparent
      convert hparent using 1
      ring_nf
    · rw [block.parentDebt_sub_paidSpliceDebt_eq_entryReach_mul_suffixGain,
        block.paidSplice_payoffGain_eq_entryReach_mul_suffixGain]
    · intro time htime
      exact block.paidSplice_liveRoot_eq_of_lt payer deviation htime

end QuittingUniformlyReachedPostMarkTwoCutBlock

end GameTheory
