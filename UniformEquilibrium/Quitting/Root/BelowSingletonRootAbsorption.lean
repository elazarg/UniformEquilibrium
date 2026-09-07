import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailUniformAbsorption
import UniformEquilibrium.Quitting.Root.NashDefect

/-! # Absorption forced by a continuation below a singleton payoff -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A below-singleton continuation forces an endpoint advantage unless the
opponents already absorb. -/
theorem quittingRootEndpointDifference_ge_gap_sub_opponentAbsorption_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) {M gap : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hgap : tail who ≤ reward (quittingSingletonTerminal who) who - gap) :
    gap - quittingRootOpponentAbsorptionMass root who * (gap + 2 * M) ≤
      quittingRootEndpointDifference reward tail root who := by
  let opponentMass := quittingRootOpponentAbsorptionMass root who
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hopponentNonneg : 0 ≤ opponentMass :=
    quittingRootOpponentAbsorptionMass_nonneg root who
  have hopponentLeOne : opponentMass ≤ 1 :=
    quittingRootOpponentAbsorptionMass_le_one root who
  have hjoining := neg_le_of_abs_le
    (abs_quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
      reward root who hreward)
  have hdecomposition :=
    quittingRootEndpointDifference_eq_outsiderNever reward tail root who
  rw [show quittingRootAbsorptionMass
      (Function.update root who (PMF.pure false)) = opponentMass by rfl]
    at hdecomposition
  have hweighted : (1 - opponentMass) * gap ≤
      (1 - opponentMass) *
        (reward (quittingSingletonTerminal who) who - tail who) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

/-- The sharp elementary absorption floor at an exact root below a singleton
payoff. -/
theorem belowSingleton_exactRoot_absorptionMass_lowerBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {M gap : ℝ} (hgapPos : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hgap : tail who ≤ reward (quittingSingletonTerminal who) who - gap)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    gap / (2 * M + gap) ≤ quittingRootAbsorptionMass root := by
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).2 hnash
  simpa [add_comm] using
    gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
      reward tail root who hgapPos hreward hgap hendpoint

/-- A coordinate defect at most one quarter of the singleton gap still forces
half of the exact-root absorption floor. -/
theorem belowSingleton_approximateRoot_absorptionMass_lowerBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {M gap : ℝ} (hgapPos : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hgap : tail who ≤ reward (quittingSingletonTerminal who) who - gap)
    (hdefect : quittingRootCoordinateNashDefect reward tail root who ≤ gap / 4) :
    gap / (2 * (2 * M + gap)) ≤ quittingRootAbsorptionMass root := by
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hdenom : 0 < 2 * M + gap := by positivity
  have hlargeDenom : 0 < 2 * (2 * M + gap) := by positivity
  by_contra hbound
  have habsorption : quittingRootAbsorptionMass root <
      gap / (2 * (2 * M + gap)) := lt_of_not_ge hbound
  have hopponent := quittingRootOpponentAbsorptionMass_le_absorptionMass root who
  have hendpointBound :=
    quittingRootEndpointDifference_ge_gap_sub_opponentAbsorption_mul
      reward tail root who hreward hgap
  have hendpoint : gap / 2 <
      quittingRootEndpointDifference reward tail root who := by
    have hratio := (lt_div_iff₀ hlargeDenom).mp habsorption
    nlinarith
  have hratioHalf : gap / (2 * (2 * M + gap)) ≤ 1 / 2 := by
    apply (div_le_iff₀ hlargeDenom).2
    nlinarith
  have hquit : (root who true).toReal ≤ quittingRootAbsorptionMass root := by
    have hcontinue := quittingStationaryContinueMass_le_ownContinueProbability
      root who
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    unfold quittingRootAbsorptionMass
    linarith
  have hcontinue : 1 / 2 < (root who false).toReal := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    nlinarith
  have hdecomposition :=
    quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart
      reward tail root who
  have hquitProbability : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hpositive : 0 ≤ quittingRootEndpointDifference reward tail root who :=
    hendpoint.le.trans' (by positivity)
  rw [max_eq_left hpositive,
    max_eq_right (by linarith : -quittingRootEndpointDifference
      reward tail root who ≤ 0), mul_zero, add_zero] at hdecomposition
  nlinarith

end GameTheory
