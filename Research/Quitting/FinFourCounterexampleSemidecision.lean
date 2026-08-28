/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Mathlib.Data.Nat.Pairing
import Research.Quitting.FinFourExactScaleResolution
import Research.Quitting.FinFourPositiveRationalRewardApproximation

/-!
# Exact semidecision for Fin4 terminal counterexamples

One natural-numbered outer stage is decoded into a rational reward-code index,
a dyadic scale, and a local exact-resolver stage.  The stage function evaluates
only proof-free rational data and emits only lower interval certificates.

Every emitted certificate proves a positive all-behavior terminal
exploitability gap and hence literal nonexistence of a uniform-equilibrium
payoff for its normalized rational reward table.  Conversely, every normalized
rational positive-infimum code is found at a finite stage.  Reward robustness,
positive scaling, and rational density extend this to existence of an emitted
rational counterexample whenever any real Fin4 counterexample exists.

This is a recursive-enumerability statement.  Nontermination has no checked
meaning and the procedure does not decide a supplied real reward table.
-/

namespace GameTheory

/-- The three indices inspected by one global semidecision stage. -/
structure FinFourCounterexampleStage where
  rewardIndex : ℕ
  scaleIndex : ℕ
  localStage : ℕ
deriving DecidableEq, Repr

namespace FinFourCounterexampleStage

/-- Executable nested-pair encoding of one global search stage. -/
def encode (stage : FinFourCounterexampleStage) : ℕ :=
  Nat.pair stage.rewardIndex (Nat.pair stage.scaleIndex stage.localStage)

/-- Executable nested-unpair decoding of one global search stage. -/
def decode (index : ℕ) : FinFourCounterexampleStage :=
  let outer := Nat.unpair index
  let inner := Nat.unpair outer.2
  ⟨outer.1, inner.1, inner.2⟩

/-- Every triple occurs at its explicit nested-pair index. -/
@[simp] theorem decode_encode (stage : FinFourCounterexampleStage) :
    decode (encode stage) = stage := by
  rcases stage with ⟨rewardIndex, scaleIndex, localStage⟩
  simp [decode, encode]

/-- Decoding and re-encoding preserve every global natural stage. -/
@[simp] theorem encode_decode (index : ℕ) :
    encode (decode index) = index := by
  simp [decode, encode, Nat.pair_unpair]

end FinFourCounterexampleStage

/-- Positive dyadic accuracy at scale `index`. -/
def finFourCounterexampleDyadicScale (index : ℕ) : ℚ :=
  (1 / 2 : ℚ) ^ index

theorem finFourCounterexampleDyadicScale_pos (index : ℕ) :
    0 < finFourCounterexampleDyadicScale index := by
  exact pow_pos (by norm_num) index

/-- Proof-free finite output of the global semidecision.

Both the resolver stage and the stage recorded by its lower constructor are
retained.  Their equality follows from the exact origin equation rather than
being inserted as a proof field. -/
structure FinFourCounterexampleCertificate where
  rewardIndex : ℕ
  scaleIndex : ℕ
  localStage : ℕ
  lowerRounds : ℕ
  reward : RationalFinFourRewardCode
  tree : FinFourExactScaleLowerTree
    (finFourCounterexampleDyadicScale scaleIndex)
deriving DecidableEq, Repr

namespace FinFourCounterexampleCertificate

/-- Exact rational scale carried by a global output. -/
def epsilon (certificate : FinFourCounterexampleCertificate) : ℚ :=
  finFourCounterexampleDyadicScale certificate.scaleIndex

/-- Exact provenance of a global output in the reward enumeration and the
per-scale lower resolver. -/
def Origin (certificate : FinFourCounterexampleCertificate) : Prop :=
  RationalFinFourRewardCode.candidateAt certificate.rewardIndex =
      some certificate.reward ∧
    certificate.reward.normalized = true ∧
    finFourExactScaleStep certificate.reward certificate.epsilon
        certificate.localStage =
      some (.lower certificate.lowerRounds certificate.tree)

/-- Independent Boolean verifier for a global lower certificate. -/
def verifies (certificate : FinFourCounterexampleCertificate) : Bool :=
  decide (RationalFinFourRewardCode.candidateAt certificate.rewardIndex =
      some certificate.reward) &&
    certificate.reward.normalized &&
    (FinFourExactScaleCertificate.lower certificate.lowerRounds
      certificate.tree).verifies certificate.reward certificate.epsilon

end FinFourCounterexampleCertificate

/-- Evaluate one explicit reward/scale/local-stage triple.

Upper results are intentionally discarded: this outer procedure semidecides
only the existence of a positive lower gap. -/
def finFourCounterexampleStepAt
    (rewardIndex scaleIndex localStage : ℕ) :
    Option FinFourCounterexampleCertificate :=
  match RationalFinFourRewardCode.candidateAt rewardIndex with
  | none => none
  | some reward =>
      match reward.normalized with
      | false => none
      | true =>
          match finFourExactScaleStep reward
              (finFourCounterexampleDyadicScale scaleIndex) localStage with
          | some (.lower lowerRounds tree) =>
              some ⟨rewardIndex, scaleIndex, localStage, lowerRounds,
                reward, tree⟩
          | some (.upper _ _) | none => none

/-- One total computable stage of the global counterexample semidecision. -/
def finFourCounterexampleStep (index : ℕ) :
    Option FinFourCounterexampleCertificate :=
  let stage := FinFourCounterexampleStage.decode index
  finFourCounterexampleStepAt stage.rewardIndex stage.scaleIndex
    stage.localStage

/-- A direct triple-stage output has the advertised exact origin. -/
theorem finFourCounterexampleStepAt_origin
    (rewardIndex scaleIndex localStage : ℕ)
    (certificate : FinFourCounterexampleCertificate)
    (hstep : finFourCounterexampleStepAt rewardIndex scaleIndex localStage =
      some certificate) :
    certificate.Origin := by
  unfold finFourCounterexampleStepAt at hstep
  cases hreward : RationalFinFourRewardCode.candidateAt rewardIndex with
  | none => simp [hreward] at hstep
  | some reward =>
      cases hnormalized : reward.normalized with
      | false => simp [hreward, hnormalized] at hstep
      | true =>
          cases hscale : finFourExactScaleStep reward
              (finFourCounterexampleDyadicScale scaleIndex) localStage with
          | none => simp [hreward, hnormalized, hscale] at hstep
          | some result =>
              cases result with
              | upper upperStage code =>
                  simp [hreward, hnormalized, hscale] at hstep
              | lower lowerRounds tree =>
                  simp [hreward, hnormalized, hscale] at hstep
                  subst certificate
                  exact ⟨hreward, hnormalized, hscale⟩

/-- Every global emitted certificate has the exact enumerator/resolver
origin retained by its payload. -/
theorem finFourCounterexampleStep_origin
    (index : ℕ) (certificate : FinFourCounterexampleCertificate)
    (hstep : finFourCounterexampleStep index = some certificate) :
    certificate.Origin := by
  exact finFourCounterexampleStepAt_origin
    (FinFourCounterexampleStage.decode index).rewardIndex
    (FinFourCounterexampleStage.decode index).scaleIndex
    (FinFourCounterexampleStage.decode index).localStage certificate hstep

/-- Every global emitted certificate passes its independent exact checker. -/
theorem finFourCounterexampleStep_verifies
    (index : ℕ) (certificate : FinFourCounterexampleCertificate)
    (hstep : finFourCounterexampleStep index = some certificate) :
    certificate.verifies = true := by
  have horigin := finFourCounterexampleStep_origin index certificate hstep
  have hverified := finFourExactScaleStep_verifies certificate.reward
    certificate.epsilon certificate.localStage
    (.lower certificate.lowerRounds certificate.tree) horigin.2.2
  simp only [FinFourCounterexampleCertificate.verifies, horigin.1,
    decide_true, horigin.2.1, Bool.true_and]
  exact hverified

/-- Every emitted table is literally a normalized entry of the fair rational
reward enumeration. -/
theorem finFourCounterexampleStep_reward_and_normalized
    (index : ℕ) (certificate : FinFourCounterexampleCertificate)
    (hstep : finFourCounterexampleStep index = some certificate) :
    RationalFinFourRewardCode.candidateAt certificate.rewardIndex =
        some certificate.reward ∧
      certificate.reward.normalized = true := by
  have horigin := finFourCounterexampleStep_origin index certificate hstep
  exact ⟨horigin.1, horigin.2.1⟩

/-- Every emitted tree lower-bounds unrestricted global exploitability by the
positive dyadic quarter-scale. -/
theorem finFourCounterexampleStep_infimum_lower
    (index : ℕ) (certificate : FinFourCounterexampleCertificate)
    (hstep : finFourCounterexampleStep index = some certificate) :
    (certificate.epsilon : ℝ) / 4 ≤
      quittingTerminalExploitabilityInf certificate.reward.realReward := by
  have horigin := finFourCounterexampleStep_origin index certificate hstep
  exact finFourExactScaleStep_lower_infimum_sound certificate.reward
    certificate.epsilon horigin.2.1 certificate.localStage
    certificate.lowerRounds certificate.tree horigin.2.2

/-- Every emitted lower certificate has a strictly positive global
exploitability infimum. -/
theorem finFourCounterexampleStep_infimum_pos
    (index : ℕ) (certificate : FinFourCounterexampleCertificate)
    (hstep : finFourCounterexampleStep index = some certificate) :
    0 < quittingTerminalExploitabilityInf certificate.reward.realReward := by
  have hlower := finFourCounterexampleStep_infimum_lower index certificate hstep
  have hepsilon : (0 : ℝ) < certificate.epsilon := by
    exact_mod_cast finFourCounterexampleDyadicScale_pos certificate.scaleIndex
  linarith

/-- The terminal gap attached to every emitted certificate is strictly
positive. -/
theorem FinFourCounterexampleCertificate.terminalGap_pos
    (certificate : FinFourCounterexampleCertificate) :
    0 < (certificate.epsilon : ℝ) / 8 := by
  have hepsilon : (0 : ℝ) < certificate.epsilon := by
    exact_mod_cast finFourCounterexampleDyadicScale_pos certificate.scaleIndex
  positivity

/-- Every emitted lower certificate supplies a literal attained terminal gap
at one eighth of its dyadic scale. -/
theorem finFourCounterexampleStep_terminalGap
    (index : ℕ) (certificate : FinFourCounterexampleCertificate)
    (hstep : finFourCounterexampleStep index = some certificate) :
    HasTerminalExploitabilityGap certificate.reward.realReward
      ((certificate.epsilon : ℝ) / 8) := by
  have horigin := finFourCounterexampleStep_origin index certificate hstep
  exact finFourExactScaleStep_lower_terminalGap certificate.reward
    horigin.2.1
    (finFourCounterexampleDyadicScale_pos certificate.scaleIndex)
    certificate.localStage certificate.lowerRounds certificate.tree
    horigin.2.2

/-- Every emitted lower certificate literally rules out a uniform-equilibrium
payoff for its normalized rational Fin4 reward table. -/
theorem finFourCounterexampleStep_no_uniformEquilibriumPayoff
    (index : ℕ) (certificate : FinFourCounterexampleCertificate)
    (hstep : finFourCounterexampleStep index = some certificate) :
    ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame certificate.reward.realReward).IsUniformEquilibriumPayoff
        none payoff := by
  have horigin := finFourCounterexampleStep_origin index certificate hstep
  exact finFourExactScaleStep_lower_no_uniformEquilibriumPayoff
    certificate.reward horigin.2.1
    (finFourCounterexampleDyadicScale_pos certificate.scaleIndex)
    certificate.localStage certificate.lowerRounds certificate.tree
    horigin.2.2

/-- One bundled literal soundness statement for global semidecision output. -/
theorem finFourCounterexampleStep_sound
    (index : ℕ) (certificate : FinFourCounterexampleCertificate)
    (hstep : finFourCounterexampleStep index = some certificate) :
    RationalFinFourRewardCode.candidateAt certificate.rewardIndex =
        some certificate.reward ∧
      certificate.reward.normalized = true ∧
      0 < quittingTerminalExploitabilityInf certificate.reward.realReward ∧
      0 < (certificate.epsilon : ℝ) / 8 ∧
      HasTerminalExploitabilityGap certificate.reward.realReward
          ((certificate.epsilon : ℝ) / 8) ∧
      ¬ ∃ payoff : Payoff (Fin 4),
        (quittingGame certificate.reward.realReward).IsUniformEquilibriumPayoff
          none payoff := by
  obtain ⟨hreward, hnormalized⟩ :=
    finFourCounterexampleStep_reward_and_normalized index certificate hstep
  exact ⟨hreward, hnormalized,
    finFourCounterexampleStep_infimum_pos index certificate hstep,
    certificate.terminalGap_pos,
    finFourCounterexampleStep_terminalGap index certificate hstep,
    finFourCounterexampleStep_no_uniformEquilibriumPayoff
      index certificate hstep⟩

/-- Some dyadic scale has upper target strictly below every positive real
exploitability infimum. -/
theorem exists_finFourCounterexampleDyadicScale_three_quarters_lt
    {value : ℝ} (hvalue : 0 < value) :
    ∃ index : ℕ,
      3 * (finFourCounterexampleDyadicScale index : ℝ) / 4 < value := by
  obtain ⟨index, hindex⟩ : ∃ index : ℕ, (1 / 2 : ℝ) ^ index < value :=
    exists_pow_lt_of_lt_one hvalue (by norm_num)
  refine ⟨index, ?_⟩
  have hscale : (finFourCounterexampleDyadicScale index : ℝ) =
      (1 / 2 : ℝ) ^ index := by
    simp [finFourCounterexampleDyadicScale]
  rw [hscale]
  have hpositive : (0 : ℝ) < (1 / 2 : ℝ) ^ index := by positivity
  linarith

/-- Finite-stage completeness for a fixed enumerated normalized rational code
whose unrestricted global exploitability infimum is positive. -/
theorem exists_finFourCounterexampleStep_of_candidateAt_of_infimum_pos
    (rewardIndex : ℕ) (reward : RationalFinFourRewardCode)
    (hcandidate : RationalFinFourRewardCode.candidateAt rewardIndex =
      some reward)
    (hnormalized : reward.normalized = true)
    (hpositive : 0 < quittingTerminalExploitabilityInf reward.realReward) :
    ∃ index certificate,
      finFourCounterexampleStep index = some certificate ∧
        certificate.reward = reward := by
  obtain ⟨scaleIndex, hscale⟩ :=
    exists_finFourCounterexampleDyadicScale_three_quarters_lt hpositive
  let epsilon := finFourCounterexampleDyadicScale scaleIndex
  obtain ⟨localStage, result, hresult⟩ := exists_finFourExactScaleStep
    reward epsilon hnormalized
      (finFourCounterexampleDyadicScale_pos scaleIndex)
  cases result with
  | upper upperStage code =>
      obtain ⟨hvalid, hexploitability, -⟩ :=
        finFourExactScaleStep_upper_sound reward epsilon localStage
          upperStage code hresult
      have hinf := quittingTerminalExploitabilityInf_le reward.realReward
        (code.toBehaviorProfile reward hvalid)
      exact False.elim (by
        have hscale' : ((3 * epsilon / 4 : ℚ) : ℝ) =
            3 * (epsilon : ℝ) / 4 := by norm_num
        rw [hscale'] at hexploitability
        linarith)
  | lower lowerRounds tree =>
      let stage : FinFourCounterexampleStage :=
        ⟨rewardIndex, scaleIndex, localStage⟩
      let certificate : FinFourCounterexampleCertificate :=
        ⟨rewardIndex, scaleIndex, localStage, lowerRounds, reward, tree⟩
      have hresult' : finFourExactScaleStep reward
          (finFourCounterexampleDyadicScale scaleIndex) localStage =
            some (.lower lowerRounds tree) := by
        simpa only [epsilon] using hresult
      have hstepAt :
          finFourCounterexampleStepAt rewardIndex scaleIndex localStage =
            some certificate := by
        simp [finFourCounterexampleStepAt, hcandidate, hnormalized, hresult',
          certificate]
      refine ⟨stage.encode, certificate, ?_, rfl⟩
      simpa only [finFourCounterexampleStep,
        FinFourCounterexampleStage.decode_encode] using hstepAt

/-- Every normalized rational positive-infimum code is found, with its fair
reward-enumeration index chosen internally. -/
theorem exists_finFourCounterexampleStep_of_rational_infimum_pos
    (reward : RationalFinFourRewardCode)
    (hnormalized : reward.normalized = true)
    (hpositive : 0 < quittingTerminalExploitabilityInf reward.realReward) :
    ∃ index certificate,
      finFourCounterexampleStep index = some certificate ∧
        certificate.reward = reward := by
  obtain ⟨rewardIndex, hcandidate⟩ :=
    RationalFinFourRewardCode.candidateAt_surjective reward
  exact exists_finFourCounterexampleStep_of_candidateAt_of_infimum_pos
    rewardIndex reward hcandidate hnormalized hpositive

/-- If any real Fin4 reward table has positive global exploitability infimum,
the executable outer search emits a normalized rational counterexample at a
finite stage.  The output need not approximate the supplied table without
first applying the explicit positive normalization used by the density
theorem. -/
theorem exists_finFourCounterexampleStep_of_real_infimum_pos
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hpositive : 0 < quittingTerminalExploitabilityInf reward) :
    ∃ index certificate,
      finFourCounterexampleStep index = some certificate := by
  obtain ⟨rewardIndex, code, hcandidate, hnormalized, hcodePositive, -⟩ :=
    exists_scaledNormalizedRationalFinFourRewardCode_exploitabilityInf_pos
      reward hpositive
  obtain ⟨index, certificate, hstep, -⟩ :=
    exists_finFourCounterexampleStep_of_candidateAt_of_infimum_pos
      rewardIndex code hcandidate hnormalized hcodePositive
  exact ⟨index, certificate, hstep⟩

/-- Exact recursive-enumerability equivalence for existence of a positive-gap
Fin4 reward table.  The right side is finite positive evidence only; failure to
find it at any bounded collection of stages proves nothing. -/
theorem exists_finFourCounterexampleStep_iff_exists_real_infimum_pos :
    (∃ index certificate,
        finFourCounterexampleStep index = some certificate) ↔
      ∃ reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
        0 < quittingTerminalExploitabilityInf reward := by
  constructor
  · rintro ⟨index, certificate, hstep⟩
    exact ⟨certificate.reward.realReward,
      finFourCounterexampleStep_infimum_pos index certificate hstep⟩
  · rintro ⟨reward, hpositive⟩
    exact exists_finFourCounterexampleStep_of_real_infimum_pos reward hpositive

end GameTheory
