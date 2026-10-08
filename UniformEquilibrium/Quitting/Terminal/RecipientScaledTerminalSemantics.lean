import MathUE.Analysis.CompactLinearMinimumRigidity
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Homeomorph.Lemmas
import UniformEquilibrium.Quitting.Terminal.TerminalAffineReward
import UniformEquilibrium.Quitting.Terminal.TerminalDebtSumInf

/-! # Recipient scaling of complete terminal semantics

Positive playerwise reward scaling transports the entire original semantic
carrier by a diagonal homeomorphism. Its literal new SUM-debt infimum equals
the weighted infimum over the fixed original debt image. Both coordinates
retain their actual behavioral meaning, including the unrestricted reply cap.
Every nonempty open positive-weight region contains weights with one common
new debt vector at all scaled-carrier SUM minima. This does not assert
uniqueness of pairs or select a near-identity contact-preserving reward table.
-/

noncomputable section

namespace GameTheory

open _root_.Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Diagonal scaling of prescribed payoffs and complete behavioral caps. -/
def quittingRecipientScaleSemanticPair (weights : Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) : QuittingTerminalSemanticPair ι :=
  (fun who => weights who * pair.1 who, fun who => weights who * pair.2 who)

/-- Positive scaling is an actual homeomorphism of the whole pair space. -/
def quittingRecipientScaleSemanticHomeomorph (weights : Payoff ι)
    (hpositive : ∀ who, 0 < weights who) :
    QuittingTerminalSemanticPair ι ≃ₜ QuittingTerminalSemanticPair ι :=
  let diagonal := Homeomorph.piCongrRight fun who =>
    Homeomorph.mulLeft₀ (weights who) (hpositive who).ne'
  diagonal.prodCongr diagonal

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingRecipientScaleSemanticHomeomorph_apply
    (weights : Payoff ι) (hpositive : ∀ who, 0 < weights who)
    (pair : QuittingTerminalSemanticPair ι) :
    quittingRecipientScaleSemanticHomeomorph weights hpositive pair =
      quittingRecipientScaleSemanticPair weights pair := rfl

/-- Each complete cap scales by its recipient's nonnegative factor. -/
theorem quittingContinuationBestResponseValue_recipientScale
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weights : Payoff ι) (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (hweight : 0 ≤ weights who) :
    quittingContinuationBestResponseValue
        (quittingPlayerwiseAffineReward reward weights 0) profile who =
      weights who * quittingContinuationBestResponseValue reward profile who := by
  unfold quittingContinuationBestResponseValue
  change (⨆ deviation, quittingTerminalPayoff
      (quittingPlayerwiseAffineReward reward weights 0)
      (Function.update profile who deviation) who) =
    weights who * (⨆ deviation,
      quittingTerminalPayoff reward (Function.update profile who deviation) who)
  rw [Real.mul_iSup_of_nonneg hweight]
  congr 1
  funext deviation
  calc
    _ = weights who * quittingTerminalPayoff reward (Function.update profile who deviation) who +
        (0 : Payoff ι) who *
          (1 - quittingLiveMassLimit reward (Function.update profile who deviation)) :=
      quittingTerminalPayoff_playerwiseAffine reward weights 0
        (Function.update profile who deviation) who
    _ = _ := by rw [Pi.zero_apply, zero_mul, add_zero]

/-- The diagonal action agrees with both literal coordinates of every actual profile. -/
theorem quittingTerminalSemanticPair_recipientScale
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weights : Payoff ι) (hnonnegative : ∀ who, 0 ≤ weights who)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair (quittingPlayerwiseAffineReward reward weights 0) profile =
      quittingRecipientScaleSemanticPair weights (quittingTerminalSemanticPair reward profile) := by
  apply Prod.ext <;> funext who
  · simpa only [quittingTerminalSemanticPair, quittingRecipientScaleSemanticPair,
      Pi.zero_apply, zero_mul, add_zero] using
      quittingTerminalPayoff_playerwiseAffine reward weights 0 profile who
  · exact quittingContinuationBestResponseValue_recipientScale reward weights profile who
      (hnonnegative who)

/-- Positive recipient scaling sends the whole original carrier onto the new carrier. -/
theorem quittingTerminalSemanticCarrier_recipientScale
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weights : Payoff ι) (hpositive : ∀ who, 0 < weights who) :
    quittingTerminalSemanticCarrier (quittingPlayerwiseAffineReward reward weights 0) =
      quittingRecipientScaleSemanticPair weights '' quittingTerminalSemanticCarrier reward := by
  let homeomorph := quittingRecipientScaleSemanticHomeomorph weights hpositive
  have hrange : quittingAttainableTerminalSemanticPairs
      (quittingPlayerwiseAffineReward reward weights 0) =
      homeomorph '' quittingAttainableTerminalSemanticPairs reward := by
    ext pair
    constructor
    · rintro ⟨profile, rfl⟩
      exact ⟨quittingTerminalSemanticPair reward profile, ⟨profile, rfl⟩,
        (quittingTerminalSemanticPair_recipientScale reward weights
          (fun who => (hpositive who).le) profile).symm⟩
    · rintro ⟨pair, ⟨profile, rfl⟩, rfl⟩
      exact ⟨profile, quittingTerminalSemanticPair_recipientScale reward weights
        (fun who => (hpositive who).le) profile⟩
  change closure (quittingAttainableTerminalSemanticPairs
      (quittingPlayerwiseAffineReward reward weights 0)) =
    homeomorph '' closure (quittingAttainableTerminalSemanticPairs reward)
  rw [homeomorph.image_closure, hrange]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingTerminalSemanticDebt_recipientScale
    (weights : Payoff ι) (pair : QuittingTerminalSemanticPair ι) (who : ι) :
    quittingTerminalSemanticDebt (quittingRecipientScaleSemanticPair weights pair) who =
      weights who * quittingTerminalSemanticDebt pair who := by
  dsimp [quittingTerminalSemanticDebt, quittingRecipientScaleSemanticPair]
  ring

omit [DecidableEq ι] in
/-- New unweighted SUM is the old debt vector paired with the recipient weights. -/
theorem quittingTerminalSemanticDebtSum_recipientScale
    (weights : Payoff ι) (pair : QuittingTerminalSemanticPair ι) :
    quittingTerminalSemanticDebtSum (quittingRecipientScaleSemanticPair weights pair) =
      _root_.Math.CompactLinearMinimum.pairing (quittingTerminalSemanticDebt pair) weights := by
  simp only [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt_recipientScale,
    _root_.Math.CompactLinearMinimum.pairing_apply]

/-- Fixed original coefficient set: actual debts of every original carrier point. -/
def quittingTerminalSemanticDebtImage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Set (Payoff ι) :=
  quittingTerminalSemanticDebt '' quittingTerminalSemanticCarrier reward

theorem quittingTerminalSemanticDebtImage_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (quittingTerminalSemanticDebtImage reward) := by
  exact (quittingTerminalSemanticCarrier_isCompact reward).image
    (continuous_pi fun who => continuous_quittingTerminalSemanticDebt who)

theorem quittingTerminalSemanticDebtImage_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingTerminalSemanticDebtImage reward).Nonempty :=
  (quittingTerminalSemanticCarrier_nonempty reward).image _

/-- The actual new SUM infimum is the linear infimum over the fixed original debt image. -/
theorem quittingTerminalDebtSumInf_recipientScale
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weights : Payoff ι) (hpositive : ∀ who, 0 < weights who) :
    quittingTerminalDebtSumInf (quittingPlayerwiseAffineReward reward weights 0) =
      _root_.Math.CompactLinearMinimum.value
        (quittingTerminalSemanticDebtImage reward) weights := by
  obtain ⟨coefficient, hcoefficient, hvalue, hminimum⟩ :=
    _root_.Math.CompactLinearMinimum.exists_minimizer
      (quittingTerminalSemanticDebtImage_isCompact reward)
      (quittingTerminalSemanticDebtImage_nonempty reward) weights
  obtain ⟨pair, hpair, rfl⟩ := hcoefficient
  have hscaled : quittingRecipientScaleSemanticPair weights pair ∈
      quittingTerminalSemanticCarrier (quittingPlayerwiseAffineReward reward weights 0) := by
    rw [quittingTerminalSemanticCarrier_recipientScale reward weights hpositive]
    exact ⟨pair, hpair, rfl⟩
  have hscaledMin : ∀ candidate ∈
      quittingTerminalSemanticCarrier (quittingPlayerwiseAffineReward reward weights 0),
      quittingTerminalSemanticDebtSum (quittingRecipientScaleSemanticPair weights pair) ≤
        quittingTerminalSemanticDebtSum candidate := by
    rw [quittingTerminalSemanticCarrier_recipientScale reward weights hpositive]
    rintro _ ⟨candidate, hcandidate, rfl⟩
    rw [quittingTerminalSemanticDebtSum_recipientScale,
      quittingTerminalSemanticDebtSum_recipientScale]
    exact hminimum ⟨candidate, hcandidate, rfl⟩
  rw [quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
    (quittingRecipientScaleSemanticPair weights pair) hscaled hscaledMin,
    quittingTerminalSemanticDebtSum_recipientScale]
  exact hvalue

/-- Recipient bounds compare the actual new gap to the literal original SUM gap. -/
theorem quittingTerminalDebtSumInf_recipientScale_bounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weights : Payoff ι) (hpositive : ∀ who, 0 < weights who)
    (lower upper : ℝ) (hlower : 0 ≤ lower)
    (hweights : ∀ who, lower ≤ weights who ∧ weights who ≤ upper) :
    lower * quittingTerminalDebtSumInf reward ≤
        quittingTerminalDebtSumInf (quittingPlayerwiseAffineReward reward weights 0) ∧
      quittingTerminalDebtSumInf (quittingPlayerwiseAffineReward reward weights 0) ≤
        upper * quittingTerminalDebtSumInf reward := by
  have hcompact := quittingTerminalSemanticDebtImage_isCompact reward
  have hnonempty := quittingTerminalSemanticDebtImage_nonempty reward
  rw [quittingTerminalDebtSumInf_recipientScale reward weights hpositive]
  constructor
  · obtain ⟨coefficient, hcoefficient, heq, _⟩ :=
      _root_.Math.CompactLinearMinimum.exists_minimizer hcompact hnonempty weights
    obtain ⟨pair, hpair, rfl⟩ := hcoefficient
    have hsum : lower * quittingTerminalSemanticDebtSum pair ≤
        _root_.Math.CompactLinearMinimum.pairing (quittingTerminalSemanticDebt pair) weights := by
      rw [quittingTerminalSemanticDebtSum, Finset.mul_sum,
        _root_.Math.CompactLinearMinimum.pairing_apply]
      exact Finset.sum_le_sum fun who _ => mul_le_mul_of_nonneg_right
        (hweights who).1 (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who)
    obtain ⟨old, hold, hminimum⟩ := exists_minimum_quittingTerminalSemanticDebtSum reward
    rw [quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum old hold hminimum]
    exact (mul_le_mul_of_nonneg_left (hminimum pair hpair) hlower).trans (heq ▸ hsum)
  · obtain ⟨pair, hpair, hminimum⟩ := exists_minimum_quittingTerminalSemanticDebtSum reward
    have hvalue := _root_.Math.CompactLinearMinimum.value_le hcompact weights
      (show quittingTerminalSemanticDebt pair ∈ quittingTerminalSemanticDebtImage reward from
        ⟨pair, hpair, rfl⟩)
    have hsum : _root_.Math.CompactLinearMinimum.pairing
        (quittingTerminalSemanticDebt pair) weights ≤
        upper * quittingTerminalSemanticDebtSum pair := by
      rw [_root_.Math.CompactLinearMinimum.pairing_apply,
        quittingTerminalSemanticDebtSum, Finset.mul_sum]
      exact Finset.sum_le_sum fun who _ => mul_le_mul_of_nonneg_right
        (hweights who).2 (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who)
    rw [quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum pair hpair hminimum]
    exact hvalue.trans hsum

/-- One positive weight vector has one actual new debt vector at every new SUM minimum. -/
theorem exists_recipientScale_all_minimum_debts_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (region : Set (Payoff ι)) (hopen : IsOpen region) (hregion : region.Nonempty)
    (hpositive : ∀ weights ∈ region, ∀ who, 0 < weights who) :
    ∃ weights ∈ region, ∃ debt : Payoff ι,
      (∃ pair ∈ quittingTerminalSemanticCarrier
          (quittingPlayerwiseAffineReward reward weights 0),
        quittingTerminalSemanticDebtSum pair =
            quittingTerminalDebtSumInf (quittingPlayerwiseAffineReward reward weights 0) ∧
          quittingTerminalSemanticDebt pair = debt) ∧
      ∀ pair ∈ quittingTerminalSemanticCarrier
          (quittingPlayerwiseAffineReward reward weights 0),
        quittingTerminalSemanticDebtSum pair =
            quittingTerminalDebtSumInf (quittingPlayerwiseAffineReward reward weights 0) →
          quittingTerminalSemanticDebt pair = debt := by
  have hcompact := quittingTerminalSemanticDebtImage_isCompact reward
  obtain ⟨weights, hweights, coefficient, hcoefficient, hminimum, hall⟩ :=
    _root_.Math.CompactLinearMinimum.exists_mem_open_all_minimizers_eq hcompact
      (quittingTerminalSemanticDebtImage_nonempty reward) hopen hregion
  have hweightsPositive := hpositive weights hweights
  refine ⟨weights, hweights, (fun who => weights who * coefficient who), ?_, ?_⟩
  · obtain ⟨original, horiginal, rfl⟩ := hcoefficient
    refine ⟨quittingRecipientScaleSemanticPair weights original, ?_, ?_, ?_⟩
    · rw [quittingTerminalSemanticCarrier_recipientScale reward weights hweightsPositive]
      exact ⟨original, horiginal, rfl⟩
    · rw [quittingTerminalSemanticDebtSum_recipientScale,
        quittingTerminalDebtSumInf_recipientScale reward weights hweightsPositive]
      exact (_root_.Math.CompactLinearMinimum.value_eq_of_isMinOn
        (quittingTerminalSemanticDebtImage reward) weights
        (quittingTerminalSemanticDebt original) ⟨original, horiginal, rfl⟩ hminimum).symm
    · funext who
      exact quittingTerminalSemanticDebt_recipientScale weights original who
  · intro pair hpair hpairMinimum
    rw [quittingTerminalSemanticCarrier_recipientScale reward weights hweightsPositive] at hpair
    obtain ⟨original, horiginal, rfl⟩ := hpair
    have hvalue : _root_.Math.CompactLinearMinimum.pairing
        (quittingTerminalSemanticDebt original) weights =
        _root_.Math.CompactLinearMinimum.value (quittingTerminalSemanticDebtImage reward)
          weights := by
      simpa only [quittingTerminalSemanticDebtSum_recipientScale,
        quittingTerminalDebtSumInf_recipientScale reward weights hweightsPositive] using
        hpairMinimum
    have horiginalMinimum : IsMinOn
        (fun candidate => _root_.Math.CompactLinearMinimum.pairing candidate weights)
        (quittingTerminalSemanticDebtImage reward) (quittingTerminalSemanticDebt original) := by
      intro candidate hcandidate
      change _root_.Math.CompactLinearMinimum.pairing
          (quittingTerminalSemanticDebt original) weights ≤
        _root_.Math.CompactLinearMinimum.pairing candidate weights
      rw [hvalue]
      exact _root_.Math.CompactLinearMinimum.value_le hcompact weights hcandidate
    have hdebt := hall (quittingTerminalSemanticDebt original)
      ⟨original, horiginal, rfl⟩ horiginalMinimum
    funext who
    rw [quittingTerminalSemanticDebt_recipientScale, hdebt]

end GameTheory
