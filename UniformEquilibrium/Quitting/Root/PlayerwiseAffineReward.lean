import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-! # Playerwise affine reward and one-root payoff transport -/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {Player : Type} [Fintype Player] [DecidableEq Player]

/-- Independent affine transformation of each player's terminal rewards. -/
def quittingPlayerwiseAffineReward
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (scale shift : Payoff Player) :
    {coalition : Finset Player // coalition.Nonempty} → Payoff Player :=
  fun coalition who => scale who * reward coalition who + shift who

/-- The corresponding affine transformation of a payoff vector. -/
def quittingPlayerwiseAffinePayoff
    (scale shift value : Payoff Player) : Payoff Player :=
  fun who => scale who * value who + shift who

omit [DecidableEq Player] in
/-- A one-step quitting payoff transforms playerwise affinely when both
terminal rewards and the all-Continue tail are transformed together. -/
theorem quittingRootPayoff_playerwiseAffine
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (scale shift tail : Payoff Player) (action : Player → Bool) (who : Player) :
    quittingRootPayoff (quittingPlayerwiseAffineReward reward scale shift)
        (quittingPlayerwiseAffinePayoff scale shift tail) action who =
      scale who * quittingRootPayoff reward tail action who + shift who := by
  unfold quittingRootPayoff
  by_cases hquit : (quittingQuitters action).Nonempty <;>
    simp [hquit, quittingPlayerwiseAffineReward,
      quittingPlayerwiseAffinePayoff]

omit [DecidableEq Player] in
/-- A product-root successor payoff transforms playerwise affinely. -/
theorem quittingRootSuccessorPayoff_playerwiseAffine
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (scale shift tail : Payoff Player) (root : Player → PMF Bool) (who : Player) :
    quittingRootSuccessorPayoff
        (quittingPlayerwiseAffineReward reward scale shift)
        (quittingPlayerwiseAffinePayoff scale shift tail) root who =
      scale who * quittingRootSuccessorPayoff reward tail root who + shift who := by
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  simp_rw [quittingRootPayoff_playerwiseAffine]
  rw [expect_add, expect_const_mul, expect_const]

/-- Pure-Quit minus pure-Continue scales by the player's own factor; the
translation cancels. -/
theorem quittingRootEndpointDifference_playerwiseAffine
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (scale shift tail : Payoff Player) (root : Player → PMF Bool) (who : Player) :
    quittingRootEndpointDifference
        (quittingPlayerwiseAffineReward reward scale shift)
        (quittingPlayerwiseAffinePayoff scale shift tail) root who =
      scale who * quittingRootEndpointDifference reward tail root who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  change quittingRootSuccessorPayoff
        (quittingPlayerwiseAffineReward reward scale shift)
        (quittingPlayerwiseAffinePayoff scale shift tail)
        (Function.update root who (PMF.pure true)) who -
      quittingRootSuccessorPayoff
        (quittingPlayerwiseAffineReward reward scale shift)
        (quittingPlayerwiseAffinePayoff scale shift tail)
        (Function.update root who (PMF.pure false)) who =
      scale who *
        (quittingRootSuccessorPayoff reward tail
            (Function.update root who (PMF.pure true)) who -
          quittingRootSuccessorPayoff reward tail
            (Function.update root who (PMF.pure false)) who)
  rw [quittingRootSuccessorPayoff_playerwiseAffine,
    quittingRootSuccessorPayoff_playerwiseAffine]
  ring

/-- Exact root Nash is preserved by independent positive affine
transformations of the players' payoffs. -/
theorem isZeroQuittingRootNash_playerwiseAffine
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (scale shift tail : Payoff Player) (root : Player → PMF Bool)
    (hscale : ∀ who, 0 < scale who)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    IsεQuittingRootNash (quittingPlayerwiseAffineReward reward scale shift)
      (quittingPlayerwiseAffinePayoff scale shift tail) 0 root := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash] at hnash ⊢
  intro who
  obtain ⟨hcontinue, hquit⟩ := hnash who
  have hquit' : 0 ≤ (root who true).toReal *
      quittingRootEndpointDifference reward tail root who := by
    simpa using hquit
  rw [quittingRootEndpointDifference_playerwiseAffine]
  constructor
  · rw [show (root who false).toReal *
        (scale who * quittingRootEndpointDifference reward tail root who) =
      scale who * ((root who false).toReal *
        quittingRootEndpointDifference reward tail root who) by ring]
    exact mul_nonpos_of_nonneg_of_nonpos (hscale who).le hcontinue
  · rw [show (root who true).toReal *
        (scale who * quittingRootEndpointDifference reward tail root who) =
      scale who * ((root who true).toReal *
        quittingRootEndpointDifference reward tail root who) by ring]
    simpa only [neg_zero] using mul_nonneg (hscale who).le hquit'

end GameTheory
