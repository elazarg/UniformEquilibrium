/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourIndependentCertificateSoundness

/-!
# Exact fixed-table Fin4 counterexample search

For one supplied normalized rational reward table, this file dovetails the
positive dyadic scales and the exact local resolver stages.  Upper certificates
are discarded.  A returned lower tree is checked independently and proves a
positive unrestricted behavioral terminal gap on the supplied table.

Unlike the global semidecision, this search does not enumerate reward tables.
Its completeness theorem is the fixed-table counterpart of the global
semidecision.
-/

namespace GameTheory

/-- The two indices inspected by one fixed-table search stage. -/
structure FinFourFixedTableCounterexampleStage where
  scaleIndex : ℕ
  localStage : ℕ
deriving DecidableEq, Repr

namespace FinFourFixedTableCounterexampleStage

/-- Executable pair encoding of a fixed-table search stage. -/
def encode (stage : FinFourFixedTableCounterexampleStage) : ℕ :=
  Nat.pair stage.scaleIndex stage.localStage

/-- Executable pair decoding of a fixed-table search stage. -/
def decode (index : ℕ) : FinFourFixedTableCounterexampleStage :=
  let pair := Nat.unpair index
  ⟨pair.1, pair.2⟩

@[simp] theorem decode_encode (stage : FinFourFixedTableCounterexampleStage) :
    decode (encode stage) = stage := by
  rcases stage with ⟨scaleIndex, localStage⟩
  simp [decode, encode]

@[simp] theorem encode_decode (index : ℕ) :
    encode (decode index) = index := by
  simp [decode, encode, Nat.pair_unpair]

end FinFourFixedTableCounterexampleStage

/-- Proof-free finite output for one fixed normalized rational table. -/
structure FinFourFixedTableCounterexampleCertificate
    (reward : RationalFinFourRewardCode) where
  scaleIndex : ℕ
  localStage : ℕ
  lowerRounds : ℕ
  tree : FinFourExactScaleLowerTree
    (finFourCounterexampleDyadicScale scaleIndex)
deriving DecidableEq, Repr

namespace FinFourFixedTableCounterexampleCertificate

variable {reward : RationalFinFourRewardCode}

/-- Exact positive dyadic scale carried by the fixed-table output. -/
def epsilon
    (certificate : FinFourFixedTableCounterexampleCertificate reward) : ℚ :=
  finFourCounterexampleDyadicScale certificate.scaleIndex

/-- Independent checker for a fixed-table lower payload. -/
def verifies
    (certificate : FinFourFixedTableCounterexampleCertificate reward) : Bool :=
  reward.normalized &&
    (FinFourExactScaleCertificate.lower certificate.lowerRounds
      certificate.tree).verifies reward certificate.epsilon

/-- Components recovered solely by evaluating the proof-free checker. -/
theorem verifies_components
    (certificate : FinFourFixedTableCounterexampleCertificate reward)
    (hverify : certificate.verifies = true) :
    reward.normalized = true ∧
      (FinFourExactScaleCertificate.lower certificate.lowerRounds
        certificate.tree).verifies reward certificate.epsilon = true := by
  simpa only [verifies, Bool.and_eq_true] using hverify

/-- Every accepted fixed-table payload proves a global unrestricted behavioral
lower bound on the supplied rational table. -/
theorem verifies_infimum_lower
    (certificate : FinFourFixedTableCounterexampleCertificate reward)
    (hverify : certificate.verifies = true) :
    (certificate.epsilon : ℝ) / 4 ≤
      quittingTerminalExploitabilityInf reward.realReward := by
  have hcomponents := certificate.verifies_components hverify
  exact FinFourExactScaleCertificate.lower_verifies_infimum_sound reward
    certificate.epsilon hcomponents.1 certificate.lowerRounds
      certificate.tree hcomponents.2

/-- The explicit rational margin attached to the fixed-table payload. -/
def gamma
    (certificate : FinFourFixedTableCounterexampleCertificate reward) : ℚ :=
  certificate.epsilon / 8

/-- The fixed-table certificate margin is positive. -/
theorem gamma_pos
    (certificate : FinFourFixedTableCounterexampleCertificate reward) :
    0 < certificate.gamma := by
  exact div_pos
    (finFourCounterexampleDyadicScale_pos certificate.scaleIndex)
    (by norm_num)

/-- Every accepted fixed-table payload proves the literal all-behavior
terminal gap carried by `gamma`. -/
theorem verifies_terminalGap
    (certificate : FinFourFixedTableCounterexampleCertificate reward)
    (hverify : certificate.verifies = true) :
    HasTerminalExploitabilityGap reward.realReward
      (certificate.gamma : ℝ) := by
  have hcomponents := certificate.verifies_components hverify
  simpa only [gamma, epsilon, Rat.cast_div, Rat.cast_ofNat] using
    FinFourExactScaleCertificate.lower_verifies_terminalGap reward
      hcomponents.1
      (finFourCounterexampleDyadicScale_pos certificate.scaleIndex)
      certificate.lowerRounds certificate.tree hcomponents.2

/-- Every accepted fixed-table payload rules out a uniform-equilibrium payoff
on the supplied table. -/
theorem verifies_no_uniformEquilibriumPayoff
    (certificate : FinFourFixedTableCounterexampleCertificate reward)
    (hverify : certificate.verifies = true) :
    ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward.realReward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
    reward.realReward (show (0 : ℝ) < (certificate.gamma : ℝ) by
      exact_mod_cast certificate.gamma_pos)
  exact certificate.verifies_terminalGap hverify

end FinFourFixedTableCounterexampleCertificate

/-- Evaluate one explicit scale/local-stage pair for a fixed rational table. -/
def finFourFixedTableCounterexampleStepAt
    (reward : RationalFinFourRewardCode)
    (scaleIndex localStage : ℕ) :
    Option (FinFourFixedTableCounterexampleCertificate reward) :=
  match reward.normalized with
  | false => none
  | true =>
      match finFourExactScaleStep reward
          (finFourCounterexampleDyadicScale scaleIndex) localStage with
      | some (.lower lowerRounds tree) =>
          some ⟨scaleIndex, localStage, lowerRounds, tree⟩
      | some (.upper _ _) | none => none

/-- One total computable fixed-table search stage. -/
def finFourFixedTableCounterexampleStep
    (reward : RationalFinFourRewardCode) (index : ℕ) :
    Option (FinFourFixedTableCounterexampleCertificate reward) :=
  let stage := FinFourFixedTableCounterexampleStage.decode index
  finFourFixedTableCounterexampleStepAt reward stage.scaleIndex stage.localStage

/-- Exact origin of a directly emitted fixed-table payload. -/
theorem finFourFixedTableCounterexampleStepAt_origin
    (reward : RationalFinFourRewardCode)
    (scaleIndex localStage : ℕ)
    (certificate : FinFourFixedTableCounterexampleCertificate reward)
    (hstep : finFourFixedTableCounterexampleStepAt reward scaleIndex localStage =
      some certificate) :
    reward.normalized = true ∧
      certificate.scaleIndex = scaleIndex ∧
      certificate.localStage = localStage ∧
      finFourExactScaleStep reward certificate.epsilon
          certificate.localStage =
        some (.lower certificate.lowerRounds certificate.tree) := by
  unfold finFourFixedTableCounterexampleStepAt at hstep
  cases hnormalized : reward.normalized with
  | false => simp [hnormalized] at hstep
  | true =>
      cases hscale : finFourExactScaleStep reward
          (finFourCounterexampleDyadicScale scaleIndex) localStage with
      | none => simp [hnormalized, hscale] at hstep
      | some result =>
          cases result with
          | upper upperStage code => simp [hnormalized, hscale] at hstep
          | lower lowerRounds tree =>
              simp [hnormalized, hscale] at hstep
              subst certificate
              exact ⟨rfl, rfl, rfl, hscale⟩

/-- Every emitted fixed-table payload passes its independent checker. -/
theorem finFourFixedTableCounterexampleStepAt_verifies
    (reward : RationalFinFourRewardCode)
    (scaleIndex localStage : ℕ)
    (certificate : FinFourFixedTableCounterexampleCertificate reward)
    (hstep : finFourFixedTableCounterexampleStepAt reward scaleIndex localStage =
      some certificate) :
    certificate.verifies = true := by
  have horigin := finFourFixedTableCounterexampleStepAt_origin reward
    scaleIndex localStage certificate hstep
  have hscale := finFourExactScaleStep_verifies reward certificate.epsilon
    certificate.localStage
    (.lower certificate.lowerRounds certificate.tree) horigin.2.2.2
  simp only [FinFourFixedTableCounterexampleCertificate.verifies,
    horigin.1, Bool.true_and]
  exact hscale

/-- Every emitted global natural stage passes the independent checker. -/
theorem finFourFixedTableCounterexampleStep_verifies
    (reward : RationalFinFourRewardCode) (index : ℕ)
    (certificate : FinFourFixedTableCounterexampleCertificate reward)
    (hstep : finFourFixedTableCounterexampleStep reward index =
      some certificate) :
    certificate.verifies = true := by
  exact finFourFixedTableCounterexampleStepAt_verifies reward
    (FinFourFixedTableCounterexampleStage.decode index).scaleIndex
    (FinFourFixedTableCounterexampleStage.decode index).localStage
    certificate hstep

/-- Finite-stage completeness for one fixed normalized rational table with
positive unrestricted behavioral exploitability infimum. -/
theorem exists_finFourFixedTableCounterexampleStep_of_infimum_pos
    (reward : RationalFinFourRewardCode)
    (hnormalized : reward.normalized = true)
    (hpositive : 0 < quittingTerminalExploitabilityInf reward.realReward) :
    ∃ index certificate,
      finFourFixedTableCounterexampleStep reward index = some certificate := by
  obtain ⟨scaleIndex, hscale⟩ :=
    exists_finFourCounterexampleDyadicScale_three_quarters_lt hpositive
  let epsilon := finFourCounterexampleDyadicScale scaleIndex
  obtain ⟨localStage, result, hresult⟩ := exists_finFourExactScaleStep
    reward epsilon hnormalized (finFourCounterexampleDyadicScale_pos scaleIndex)
  cases result with
  | upper upperStage code =>
      obtain ⟨hvalid, hexploitability, -⟩ :=
        finFourExactScaleStep_upper_sound reward epsilon localStage upperStage
          code hresult
      have hinf := quittingTerminalExploitabilityInf_le reward.realReward
        (code.toBehaviorProfile reward hvalid)
      exact False.elim (by
        have hscale' : ((3 * epsilon / 4 : ℚ) : ℝ) =
            3 * (epsilon : ℝ) / 4 := by norm_num
        rw [hscale'] at hexploitability
        linarith)
  | lower lowerRounds tree =>
      let stage : FinFourFixedTableCounterexampleStage :=
        ⟨scaleIndex, localStage⟩
      let certificate : FinFourFixedTableCounterexampleCertificate reward :=
        ⟨scaleIndex, localStage, lowerRounds, tree⟩
      have hresult' : finFourExactScaleStep reward
          (finFourCounterexampleDyadicScale scaleIndex) localStage =
            some (.lower lowerRounds tree) := by
        simpa only [epsilon] using hresult
      have hstepAt : finFourFixedTableCounterexampleStepAt reward scaleIndex
          localStage = some certificate := by
        simp [finFourFixedTableCounterexampleStepAt, hnormalized, hresult',
          certificate]
      refine ⟨stage.encode, certificate, ?_⟩
      simpa only [finFourFixedTableCounterexampleStep,
        FinFourFixedTableCounterexampleStage.decode_encode] using hstepAt

end GameTheory
