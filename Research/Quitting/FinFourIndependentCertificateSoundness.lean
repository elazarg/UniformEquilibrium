/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourCounterexampleSemidecision

/-!
# Independent semantic checking of exact Fin4 counterexample payloads

The exact search stores generator stages for provenance, but semantic trust
should stop at the proof-free Boolean verifier.  This file proves that a lower
interval tree accepted by that verifier directly lower-bounds unrestricted
behavioral exploitability.  No replay of the search, equality with a generated
stage, or trust in the certificate producer is used.
-/

namespace GameTheory

open Math.Interval

namespace FinFourExactScaleCertificate

/-- A lower payload accepted by the independent checker proves the analytic
single-shell bound directly, without replaying or trusting its search stage. -/
theorem lower_verifies_shell_sound
    (reward : RationalFinFourRewardCode) (epsilon : ℚ)
    (hnormalized : reward.normalized = true)
    (rounds : ℕ) (tree : FinFourExactScaleLowerTree epsilon)
    (hverify : (FinFourExactScaleCertificate.lower rounds tree).verifies
      reward epsilon = true) :
    (epsilon : ℝ) / 4 ≤
      finFourSingleShellLower reward.realReward
        (reward.abs_realReward_le_one_of_normalized
          (reward.normalized_eq_true_iff.mp hnormalized))
        (finFourExactScaleLevel epsilon) := by
  change (finFourRationalSingleShellLowerProblem reward.value
      (finFourExactScaleLevel epsilon)).verifies (epsilon / 4) tree = true
    at hverify
  let hreward : ∀ terminal player,
      |(reward.value terminal player : ℝ)| ≤ 1 := by
    simpa only [RationalFinFourRewardCode.realReward] using
      reward.abs_realReward_le_one_of_normalized
        (reward.normalized_eq_true_iff.mp hnormalized)
  have hsound := finFourRationalSingleShellTree_sound reward.value hreward
    (finFourExactScaleLevel_pos epsilon) (epsilon / 4) tree hverify
  change (epsilon : ℝ) / 4 ≤
    finFourSingleShellLower
      (fun terminal who ↦ (reward.value terminal who : ℝ)) hreward
        (finFourExactScaleLevel epsilon)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hsound

/-- A lower payload accepted by the independent checker proves the global
unrestricted behavioral lower bound directly. -/
theorem lower_verifies_infimum_sound
    (reward : RationalFinFourRewardCode) (epsilon : ℚ)
    (hnormalized : reward.normalized = true)
    (rounds : ℕ) (tree : FinFourExactScaleLowerTree epsilon)
    (hverify : (FinFourExactScaleCertificate.lower rounds tree).verifies
      reward epsilon = true) :
    (epsilon : ℝ) / 4 ≤
      quittingTerminalExploitabilityInf reward.realReward := by
  let hreward := reward.abs_realReward_le_one_of_normalized
    (reward.normalized_eq_true_iff.mp hnormalized)
  exact finFourSingleShellLower_le_exploitabilityInf reward.realReward hreward
    (finFourExactScaleLevel_pos epsilon)
    (lower_verifies_shell_sound reward epsilon hnormalized rounds tree hverify)

/-- A checked lower payload at a positive scale supplies an attained terminal
gap, independently of how the payload was generated. -/
theorem lower_verifies_terminalGap
    (reward : RationalFinFourRewardCode) {epsilon : ℚ}
    (hnormalized : reward.normalized = true) (hepsilon : 0 < epsilon)
    (rounds : ℕ) (tree : FinFourExactScaleLowerTree epsilon)
    (hverify : (FinFourExactScaleCertificate.lower rounds tree).verifies
      reward epsilon = true) :
    HasTerminalExploitabilityGap reward.realReward ((epsilon : ℝ) / 8) := by
  apply hasTerminalExploitabilityGap_of_lt_quittingTerminalExploitabilityInf
  have hinf := lower_verifies_infimum_sound reward epsilon hnormalized
    rounds tree hverify
  have hepsilonReal : (0 : ℝ) < epsilon := by exact_mod_cast hepsilon
  linarith

end FinFourExactScaleCertificate

namespace FinFourCounterexampleCertificate

/-- Exact components recovered solely by evaluating the proof-free checker. -/
theorem verifies_components
    (certificate : FinFourCounterexampleCertificate)
    (hverify : certificate.verifies = true) :
    RationalFinFourRewardCode.candidateAt certificate.rewardIndex =
        some certificate.reward ∧
      certificate.reward.normalized = true ∧
      (FinFourExactScaleCertificate.lower certificate.lowerRounds
        certificate.tree).verifies certificate.reward certificate.epsilon =
          true := by
  simpa only [verifies, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    using hverify

/-- Independent soundness of a checked payload: the finite tree itself proves
the global unrestricted behavioral lower bound, with no appeal to its search
origin or stored local stage. -/
theorem verifies_infimum_lower
    (certificate : FinFourCounterexampleCertificate)
    (hverify : certificate.verifies = true) :
    (certificate.epsilon : ℝ) / 4 ≤
      quittingTerminalExploitabilityInf certificate.reward.realReward := by
  have hcomponents := certificate.verifies_components hverify
  exact FinFourExactScaleCertificate.lower_verifies_infimum_sound
    certificate.reward certificate.epsilon hcomponents.2.1
      certificate.lowerRounds certificate.tree hcomponents.2.2

/-- Independent soundness of a checked payload at the literal positive dyadic
margin used by the global counterexample format. -/
theorem verifies_terminalGap
    (certificate : FinFourCounterexampleCertificate)
    (hverify : certificate.verifies = true) :
    HasTerminalExploitabilityGap certificate.reward.realReward
      ((certificate.epsilon : ℝ) / 8) := by
  have hcomponents := certificate.verifies_components hverify
  exact FinFourExactScaleCertificate.lower_verifies_terminalGap
    certificate.reward hcomponents.2.1
      (finFourCounterexampleDyadicScale_pos certificate.scaleIndex)
      certificate.lowerRounds certificate.tree hcomponents.2.2

/-- An independently checked payload rules out a uniform-equilibrium payoff
on its encoded rational table. -/
theorem verifies_no_uniformEquilibriumPayoff
    (certificate : FinFourCounterexampleCertificate)
    (hverify : certificate.verifies = true) :
    ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame certificate.reward.realReward).IsUniformEquilibriumPayoff
        none payoff := by
  apply quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
    certificate.reward.realReward (show
      (0 : ℝ) < (certificate.epsilon : ℝ) / 8 by
      have hepsilon : (0 : ℝ) < certificate.epsilon := by
        exact_mod_cast
          finFourCounterexampleDyadicScale_pos certificate.scaleIndex
      positivity)
  exact certificate.verifies_terminalGap hverify

end FinFourCounterexampleCertificate

end GameTheory
