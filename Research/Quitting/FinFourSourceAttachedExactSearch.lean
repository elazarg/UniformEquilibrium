import Research.Quitting.FinFourCounterexampleSemidecision
import Research.Quitting.FinFourProducerAtlas.Source

/-!
# Exact fixed-table search for source-attached Fin4 chambers

This module does not promote local chamber constraints to a global
exploitability claim. It filters the existing escape-aware exact
proof-producing Fin4 semidecision to one supplied rational reward table.

A `FinFourMinimumAtomProducer` retains an unrestricted positive terminal
exploitability gap on that same table. Consequently the fixed-table search is
complete whenever a source-attached chamber object is supplied. The
`retained` parameter can be instantiated by a checked strict
normalized-inert witness, so the emitted lower certificate and the
inert-machine witness remain attached to literally the same reward table.
-/

namespace GameTheory

/-- Exact fixed-reward filter of the global proof-producing semidecision. -/
def finFourFixedRewardCounterexampleStep
    (rewardCode : RationalFinFourRewardCode) (index : ℕ) :
    Option FinFourCounterexampleCertificate :=
  match finFourCounterexampleStep index with
  | none => none
  | some certificate =>
      if certificate.reward = rewardCode then some certificate else none

/-- A fixed-reward output is an output of the checked global search, and its
reward code is literally the requested one. -/
theorem finFourFixedRewardCounterexampleStep_origin
    (rewardCode : RationalFinFourRewardCode) (index : ℕ)
    (certificate : FinFourCounterexampleCertificate)
    (hstep :
      finFourFixedRewardCounterexampleStep rewardCode index =
        some certificate) :
    finFourCounterexampleStep index = some certificate ∧
      certificate.reward = rewardCode := by
  generalize hglobal : finFourCounterexampleStep index = result
  cases result with
  | none =>
      simp [finFourFixedRewardCounterexampleStep, hglobal] at hstep
  | some candidate =>
      by_cases hreward : candidate.reward = rewardCode
      · have hcandidate : candidate = certificate := by
          simpa [finFourFixedRewardCounterexampleStep, hglobal, hreward]
            using hstep
        subst certificate
        exact ⟨hglobal, hreward⟩
      · simp [finFourFixedRewardCounterexampleStep, hglobal, hreward] at hstep

/-- Completeness of the exact fixed-reward filter for a normalized rational
table whose unrestricted behavioral exploitability infimum is positive. -/
theorem exists_finFourFixedRewardCounterexampleStep_of_infimum_pos
    (rewardCode : RationalFinFourRewardCode)
    (hnormalized : rewardCode.normalized = true)
    (hpositive :
      0 < quittingTerminalExploitabilityInf rewardCode.realReward) :
    ∃ index certificate,
      finFourFixedRewardCounterexampleStep rewardCode index =
          some certificate ∧
        certificate.reward = rewardCode := by
  obtain ⟨index, certificate, hstep, hreward⟩ :=
    exists_finFourCounterexampleStep_of_rational_infimum_pos
      rewardCode hnormalized hpositive
  refine ⟨index, certificate, ?_, hreward⟩
  simp [finFourFixedRewardCounterexampleStep, hstep, hreward]

/-- The terminal-gap witness retained by a minimum source lower-bounds the
true unrestricted behavioral exploitability infimum. -/
theorem FinFourMinimumAtomProducer.terminalExploitabilityInf_pos
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) :
    0 < quittingTerminalExploitabilityInf reward := by
  obtain ⟨terminalGap, hterminalGap, hgap⟩ := source.residual.witness
  exact hterminalGap.trans_le
    (terminalExploitabilityGap_le_quittingTerminalExploitabilityInf hgap)

/-- Same-table completeness for every source-attached chamber.

Instantiate `P` with the proposition carrying the checked strict
normalized-inert object. The finite exact lower certificate is then returned
without discarding or reconstructing that witness. -/
theorem exists_finFourFixedRewardCounterexampleStep_of_source
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    {P : Prop} (retained : P)
    (rewardCode : RationalFinFourRewardCode)
    (hnormalized : rewardCode.normalized = true)
    (hreward : rewardCode.realReward = reward) :
    ∃ index certificate,
      finFourFixedRewardCounterexampleStep rewardCode index =
          some certificate ∧
        certificate.reward = rewardCode ∧ P := by
  have hpositive :
      0 < quittingTerminalExploitabilityInf rewardCode.realReward := by
    simpa [hreward] using source.terminalExploitabilityInf_pos
  obtain ⟨index, certificate, hstep, hcode⟩ :=
    exists_finFourFixedRewardCounterexampleStep_of_infimum_pos
      rewardCode hnormalized hpositive
  exact ⟨index, certificate, hstep, hcode, retained⟩

end GameTheory
