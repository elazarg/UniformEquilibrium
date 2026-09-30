/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.RawPassiveRowInverseCriterion
import UniformEquilibrium.Quitting.Classification.ThreePlayer.StationaryOrSmallHazard
import UniformEquilibrium.Quitting.Cycles.RationalSingletonCalendar
import UniformEquilibrium.Quitting.PayoffProcess.TailStepSelector

/-!
# Small-hazard terminal equilibria from weak inverse passive rows

An actual nearby-table balanced certificate supplies chronological cyclic roots.
Its subdivision tolerance bounds every prescribed Quit probability independently
of the requested terminal error. Reward robustness transports the same roots to
the original table, with every deleted player AlwaysContinue at every history.
The raw inverse tests are sufficient conditions, without a singleton sign
restriction; no exhaustion of the remaining standard-Q class is asserted.
-/

noncomputable section

namespace GameTheory

open StochasticGame QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem rationalRoot_quitMass_le_tolerance
    {L : ℕ} {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (certificate : BalancedSingletonCycleCertificate (L := L) reward)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (phase : Fin (certificate.rationalPeriod mesh)) (who : ι) :
    ((certificate.rationalRoot mesh phase who) true).toReal ≤ mesh := by
  let coordinate := certificate.rationalCoordinates mesh phase
  have hphase : certificate.rationalPhase mesh coordinate.1 coordinate.2 = phase :=
    certificate.rationalPhase_coordinates mesh phase
  rw [← hphase, certificate.rationalRoot_phase]
  by_cases hwho : who = certificate.owner coordinate.1
  · subst who
    rw [quittingSoloStationaryRoot_apply_owner, quittingHazardCoin_true_toReal]
    exact Math.rationalArcHazard_le_tolerance
      (certificate.hazard_nonneg coordinate.1)
      (certificate.hazard_lt_one coordinate.1) hmesh coordinate.2
  · rw [quittingSoloStationaryRoot_apply_other hwho]
    simpa using hmesh.le

omit [Fintype ι] in
private theorem rationalRoot_outside_continue
    {L : ℕ} {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (certificate : BalancedSingletonCycleCertificate (L := L) reward)
    (mesh : ℝ) (phase : Fin (certificate.rationalPeriod mesh)) (who : ι)
    (houtside : ∀ p, who ≠ certificate.owner p) :
    certificate.rationalRoot mesh phase who = PMF.pure false := by
  let coordinate := certificate.rationalCoordinates mesh phase
  have hphase : certificate.rationalPhase mesh coordinate.1 coordinate.2 = phase :=
    certificate.rationalPhase_coordinates mesh phase
  rw [← hphase, certificate.rationalRoot_phase]
  exact quittingSoloStationaryRoot_apply_other (houtside coordinate.1) _

/-- Weak inverse/passive-row data supply actual independent roots with
separately prescribed terminal accuracy and hazard cap. Deleted players have
literal Continue roots and AlwaysContinue strategies at every history. -/
theorem exists_quiet_smallHazard_terminalNash_of_nonnegativeInverse_passiveRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (hcard : Fintype.card {who : ι // ¬ deleted who} = 3)
    (hdet : Matrix.det
      (Matrix.of (normalizedSoloMatrix (quittingDeleteReward reward deleted))) ≠ 0)
    (hinverse : ∀ row column : {who : ι // ¬ deleted who},
      0 ≤ (Matrix.of
        (normalizedSoloMatrix (quittingDeleteReward reward deleted)))⁻¹ row column)
    (rows : PassiveSingletonRowFactorization reward deleted)
    (accuracy hazardCap : ℝ) (haccuracy : 0 < accuracy) (hhazardCap : 0 < hazardCap) :
    ∃ roots : ℕ → ι → PMF Bool,
      (∀ time who, (roots time who true).toReal ≤ hazardCap) ∧
      (∀ time who, deleted who → roots time who = PMF.pure false) ∧
      (∀ who, deleted who →
        quittingRootSequenceProfile reward roots 0 who =
          quittingAlwaysContinueStrategy reward who) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
        (quittingRootSequenceProfile reward roots 0) := by
  obtain ⟨perturbation, _, hclose, certificate, howners⟩ :=
    exists_strictPerturb_balancedCertificate_of_nonnegativeInverse_passiveRows
      reward deleted hcard hdet hinverse rows (accuracy / 4) (by linarith)
  let nearby := rows.perturb perturbation
  let M := quittingRewardBound nearby + 1
  have hM : 0 < M := by
    dsimp only [M]
    linarith [quittingRewardBound_nonneg nearby]
  have hreward : ∀ terminal who, |nearby terminal who| ≤ M := by
    intro terminal who
    exact (abs_reward_le_quittingRewardBound nearby terminal who).trans
      (by dsimp only [M]; linarith)
  let mesh := min hazardCap (accuracy / (4 * M))
  have hmesh : 0 < mesh := lt_min hhazardCap (div_pos haccuracy (by positivity))
  have hmeshCap : mesh ≤ hazardCap := min_le_left _ _
  have hmeshError : mesh ≤ accuracy / (4 * M) := min_le_right _ _
  let roots := quittingCyclicRootSequence
    (certificate.rationalRoot mesh) (certificate.rationalInitial mesh)
  have hquiet : ∀ time who, deleted who → roots time who = PMF.pure false := by
    intro time who hdeleted
    apply rationalRoot_outside_continue certificate mesh
      (quittingCyclicOrbit (certificate.rationalInitial mesh) time) who
    intro p hequal
    exact howners p (hequal ▸ hdeleted)
  have hnash :
      (quittingGame nearby).IsεAsymptoticNash (quittingTerminalPayoff nearby)
        (2 * M * mesh) (quittingRootSequenceProfile nearby roots 0) :=
    (certificate.rational_isTerminalNash_and_hasValue mesh hmesh hreward).1
  have hstable := IsεAsymptoticNash.of_reward_close nearby reward
    (quittingRootSequenceProfile nearby roots 0)
    (by linarith : 0 ≤ accuracy / 4) hclose hnash
  refine ⟨roots, ?_, hquiet, ?_, hstable.mono ?_⟩
  · intro time who
    exact (rationalRoot_quitMass_le_tolerance certificate mesh hmesh
      (quittingCyclicOrbit (certificate.rationalInitial mesh) time) who).trans hmeshCap
  · intro who hdeleted
    funext time history
    dsimp only [quittingRootSequenceProfile, quittingAlwaysContinueStrategy]
    change (roots (0 + time) who : PMF Bool) = PMF.pure false
    rw [Nat.zero_add]
    exact hquiet time who hdeleted
  · have hscaled := (le_div_iff₀ (by positivity : 0 < 4 * M)).mp hmeshError
    nlinarith

namespace PassiveRowInverseCriterion

/-- Literal nonnegative child inverse and outside inverse weights retain
quiet independent roots with arbitrary positive error and hazard tolerances. -/
theorem exists_quiet_smallHazard_terminalNash_of_raw_nonnegativeInverse_triple
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (hcard : Fintype.card {who : ι // ¬ deleted who} = 3)
    (hdet : (childMatrix reward deleted).det ≠ 0)
    (hinverse : ∀ row column : {who : ι // ¬ deleted who},
      0 ≤ (childMatrix reward deleted)⁻¹ row column)
    (houtside : ∀ outside, deleted outside →
      ∀ inside : {who : ι // ¬ deleted who},
        0 ≤ inverseWeight reward deleted outside inside)
    (accuracy hazardCap : ℝ) (haccuracy : 0 < accuracy) (hhazardCap : 0 < hazardCap) :
    ∃ roots : ℕ → ι → PMF Bool,
      (∀ time who, (roots time who true).toReal ≤ hazardCap) ∧
      (∀ time who, deleted who → roots time who = PMF.pure false) ∧
      (∀ who, deleted who →
        quittingRootSequenceProfile reward roots 0 who =
          quittingAlwaysContinueStrategy reward who) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
        (quittingRootSequenceProfile reward roots 0) :=
  exists_quiet_smallHazard_terminalNash_of_nonnegativeInverse_passiveRows
    reward deleted hcard hdet hinverse (factorization reward deleted hdet houtside)
      accuracy hazardCap haccuracy hhazardCap

end PassiveRowInverseCriterion

namespace QuittingThreePlayerStrategyClass

open PassiveRowInverseCriterion

/-- The raw weak triple test supplies the source's small-hazard alternative
without an own-singleton sign condition. This is a sufficient branch only. -/
theorem of_raw_nonnegativeInverse_triple
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (hcard : Fintype.card {who : ι // ¬ deleted who} = 3)
    (hdet : (PassiveRowInverseCriterion.childMatrix reward deleted).det ≠ 0)
    (hinverse : ∀ row column : {who : ι // ¬ deleted who},
      0 ≤ (PassiveRowInverseCriterion.childMatrix reward deleted)⁻¹ row column)
    (houtside : ∀ outside, deleted outside →
      ∀ inside : {who : ι // ¬ deleted who},
        0 ≤ PassiveRowInverseCriterion.inverseWeight reward deleted outside inside)
    {accuracy : ℝ} (haccuracy : 0 < accuracy) :
    StationaryOrSmallHazardTerminalEquilibrium reward accuracy := by
  obtain ⟨roots, hcap, _, _, hnash⟩ :=
    exists_quiet_smallHazard_terminalNash_of_raw_nonnegativeInverse_triple
      reward deleted hcard hdet hinverse houtside accuracy accuracy haccuracy haccuracy
  exact Or.inr ⟨roots, hcap, hnash⟩

end QuittingThreePlayerStrategyClass

end GameTheory
