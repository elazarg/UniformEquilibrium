/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourIndependentCertificateSoundness
import Research.Quitting.FinFourProducerAtlas.NormalizedInertSingleDensityToll

/-!
# Exact negative certificates for rational strict Fin4 inert machines

The source-attached strict normalized-inert object already retains a positive
terminal exploitability witness through its minimum source.  This file connects
that semantic witness to the executable exact Fin4 counterexample semidecision.
For a normalized rational reward code on the same table, the semidecision must
emit at a finite stage.  Its proof-free payload contains the rational table, a
dyadic rational margin, and an exact interval tree; the original strict inert
object remains attached in the bundled output.

No local inert inequality is treated as evidence for a positive global gap.
The only global input used below is the terminal exploitability witness retained
by the actual minimum source.
-/

noncomputable section

namespace GameTheory

namespace FinFourMinimumAtomProducer

/-- Every actual minimum source retained by the Fin4 producer atlas already
has positive unrestricted behavioral exploitability infimum. -/
theorem terminalExploitabilityInf_pos
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) :
    0 < quittingTerminalExploitabilityInf reward := by
  exact source.residual.witness.terminalGap_pos.trans_le
    (terminalExploitabilityGap_le_quittingTerminalExploitabilityInf
      reward source.residual.witness.terminalExploitability)

end FinFourMinimumAtomProducer

/-- Finite rational counterexample output forced by one actual strict
inert machine on an arbitrary real Fin4 table.

The emitted rational table need not be the source table.  The strict witness is
retained to record the semantic cause of termination; reward robustness and
rational density supply a normalized rational counterexample somewhere in the
fair enumeration. -/
structure FinFourStrictInertRationalCounterexampleConsequence
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {source : FinFourMinimumAtomProducer reward bound}
    {returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source}
    {lambda : ℝ}
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda} where
  strict : FinFourNormalizedStrictInertSingleDensityToll packet
  index : ℕ
  certificate : FinFourCounterexampleCertificate
  emitted : finFourCounterexampleStep index = some certificate

namespace FinFourStrictInertRationalCounterexampleConsequence

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}
  {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}

/-- The exact rational table returned by the global semidecision. -/
def rewardCode
    (output : FinFourStrictInertRationalCounterexampleConsequence
      (packet := packet)) : RationalFinFourRewardCode :=
  output.certificate.reward

/-- The explicit rational terminal-gap margin returned with the certificate. -/
def gamma
    (output : FinFourStrictInertRationalCounterexampleConsequence
      (packet := packet)) : ℚ :=
  output.certificate.epsilon / 8

/-- The generated finite payload passes the independent exact verifier. -/
theorem verifies
    (output : FinFourStrictInertRationalCounterexampleConsequence
      (packet := packet)) :
    output.certificate.verifies = true :=
  finFourCounterexampleStep_verifies output.index output.certificate
    output.emitted

/-- The generated rational margin is positive. -/
theorem gamma_pos
    (output : FinFourStrictInertRationalCounterexampleConsequence
      (packet := packet)) :
    0 < output.gamma := by
  exact div_pos
    (finFourCounterexampleDyadicScale_pos output.certificate.scaleIndex)
    (by norm_num)

/-- The generated rational table has a true all-behavior terminal gap. -/
theorem terminalExploitability
    (output : FinFourStrictInertRationalCounterexampleConsequence
      (packet := packet)) :
    HasTerminalExploitabilityGap output.rewardCode.realReward
      (output.gamma : ℝ) := by
  simpa only [rewardCode, gamma, Rat.cast_div, Rat.cast_ofNat] using
    output.certificate.verifies_terminalGap output.verifies

/-- The generated rational table has no uniform-equilibrium payoff. -/
theorem not_exists_uniformEquilibriumPayoff
    (output : FinFourStrictInertRationalCounterexampleConsequence
      (packet := packet)) :
    ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame output.rewardCode.realReward).IsUniformEquilibriumPayoff
        none payoff := by
  simpa only [rewardCode] using
    output.certificate.verifies_no_uniformEquilibriumPayoff output.verifies

end FinFourStrictInertRationalCounterexampleConsequence

/-- Complete termination theorem for the rigid chamber: existence of one
source-attached strict inert machine on any real Fin4 table forces the total
natural-numbered exact search to emit a finite rational positive-gap
certificate at some stage. -/
theorem nonempty_finFourStrictInertRationalCounterexampleConsequence
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {source : FinFourMinimumAtomProducer reward bound}
    {returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source}
    {lambda : ℝ}
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (strict : FinFourNormalizedStrictInertSingleDensityToll packet) :
    Nonempty (FinFourStrictInertRationalCounterexampleConsequence
      (packet := packet)) := by
  obtain ⟨index, certificate, emitted⟩ :=
    exists_finFourCounterexampleStep_of_real_infimum_pos reward
      source.terminalExploitabilityInf_pos
  exact ⟨{
    strict := strict
    index := index
    certificate := certificate
    emitted := emitted
  }⟩

/-- Source-preserving output of the exact counterexample search for one
normalized rational strict inert machine.

`certificate` is the finite proof-free object.  `strict` retains the complete
minimum source, causal atom, normalized passport, exact-root uniqueness, and
tent-toll branch on the same rational table. -/
structure FinFourRationalStrictInertCounterexampleOutput
    (rewardCode : RationalFinFourRewardCode)
    {bound : ℝ}
    {source : FinFourMinimumAtomProducer rewardCode.realReward bound}
    {returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source}
    {lambda : ℝ}
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda} where
  strict : FinFourNormalizedStrictInertSingleDensityToll packet
  index : ℕ
  certificate : FinFourCounterexampleCertificate
  emitted : finFourCounterexampleStep index = some certificate
  reward_eq : certificate.reward = rewardCode

namespace FinFourRationalStrictInertCounterexampleOutput

variable
  {rewardCode : RationalFinFourRewardCode}
  {bound : ℝ}
  {source : FinFourMinimumAtomProducer rewardCode.realReward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}

/-- The rational terminal gap carried by the finite lower certificate. -/
def gamma
    (output : FinFourRationalStrictInertCounterexampleOutput rewardCode
      (packet := packet)) : ℚ :=
  output.certificate.epsilon / 8

/-- The derived rational certificate margin is strictly positive. -/
theorem gamma_pos
    (output : FinFourRationalStrictInertCounterexampleOutput rewardCode
      (packet := packet)) :
    0 < output.gamma := by
  exact div_pos
    (finFourCounterexampleDyadicScale_pos output.certificate.scaleIndex)
    (by norm_num)

/-- The generated payload passes the independent exact Boolean verifier. -/
theorem verifies
    (output : FinFourRationalStrictInertCounterexampleOutput rewardCode
      (packet := packet)) :
    output.certificate.verifies = true :=
  finFourCounterexampleStep_verifies output.index output.certificate
    output.emitted

/-- The finite certificate proves a terminal improvement of the rational
margin against every behavioral profile of the same reward table. -/
theorem terminalExploitability
    (output : FinFourRationalStrictInertCounterexampleOutput rewardCode
      (packet := packet)) :
    HasTerminalExploitabilityGap rewardCode.realReward
      (output.gamma : ℝ) := by
  have hgap := output.certificate.verifies_terminalGap output.verifies
  rw [output.reward_eq] at hgap
  simpa only [gamma, Rat.cast_div, Rat.cast_ofNat] using hgap

/-- The emitted finite object rules out a uniform-equilibrium payoff on the
same rational table; no stationary or bounded-horizon restriction remains. -/
theorem not_exists_uniformEquilibriumPayoff
    (output : FinFourRationalStrictInertCounterexampleOutput rewardCode
      (packet := packet)) :
    ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame rewardCode.realReward).IsUniformEquilibriumPayoff
        none payoff := by
  have hno :=
    output.certificate.verifies_no_uniformEquilibriumPayoff output.verifies
  rw [output.reward_eq] at hno
  exact hno

end FinFourRationalStrictInertCounterexampleOutput

/-- Exact source-preserving specialization of the global Fin4 semidecision.
Every normalized rational table carrying the actual strict inert input emits a
finite independently checkable positive-gap certificate at some natural stage.
The strict input is retained verbatim in the output rather than reconstructed
from local table inequalities. -/
theorem nonempty_finFourRationalStrictInertCounterexampleOutput
    (rewardCode : RationalFinFourRewardCode)
    (hnormalized : rewardCode.normalized = true)
    {bound : ℝ}
    {source : FinFourMinimumAtomProducer rewardCode.realReward bound}
    {returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source}
    {lambda : ℝ}
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (strict : FinFourNormalizedStrictInertSingleDensityToll packet) :
    Nonempty (FinFourRationalStrictInertCounterexampleOutput rewardCode
      (packet := packet)) := by
  obtain ⟨index, certificate, emitted, reward_eq⟩ :=
    exists_finFourCounterexampleStep_of_rational_infimum_pos rewardCode
      hnormalized source.terminalExploitabilityInf_pos
  exact ⟨{
    strict := strict
    index := index
    certificate := certificate
    emitted := emitted
    reward_eq := reward_eq
  }⟩

/-- Mandatory zero-minimum regression: a source-attached strict inert input
cannot live on a table whose global terminal-semantic debt minimum is zero. -/
theorem isEmpty_finFourNormalizedStrictInert_of_debtInf_eq_zero
    (rewardCode : RationalFinFourRewardCode)
    {bound : ℝ}
    {source : FinFourMinimumAtomProducer rewardCode.realReward bound}
    {returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source}
    {lambda : ℝ}
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (hzero : quittingTerminalDebtSumInf rewardCode.realReward = 0) :
    IsEmpty (FinFourNormalizedStrictInertSingleDensityToll packet) := by
  constructor
  intro _
  have hpositive := source.inf_pos
  rw [hzero] at hpositive
  exact (lt_irrefl 0) hpositive

/-- Mandatory coexistence regression: even a locally valid strict inert packet
cannot be source-attached on a table having a uniform-equilibrium payoff
elsewhere. -/
theorem isEmpty_finFourNormalizedStrictInert_of_uniformPayoff
    (rewardCode : RationalFinFourRewardCode)
    {bound : ℝ}
    {source : FinFourMinimumAtomProducer rewardCode.realReward bound}
    {returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source}
    {lambda : ℝ}
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (hpayoff : ∃ payoff : Payoff (Fin 4),
      (quittingGame rewardCode.realReward).IsUniformEquilibriumPayoff
        none payoff) :
    IsEmpty (FinFourNormalizedStrictInertSingleDensityToll packet) := by
  constructor
  intro _
  exact source.residual.witness.not_exists_uniformEquilibriumPayoff hpayoff

end GameTheory
