import UniformEquilibrium.Quitting.Root.ImmediateQuitCapDisplacement
import UniformEquilibrium.Quitting.Root.TerminalChildPayoffDisplacementSequence

/-! # Sharp negative displacement at cofinal immediate-Quit resets -/

noncomputable section
namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Along cofinal immediate-Quit resets, the limiting child-minus-source
payoff displacement is at most the negative of the fixed outsider debt floor. -/
theorem exists_terminalChildPayoffDisplacement_limit_le_neg_of_frequently_quitZeroCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : ℕ → Payoff ι)
    (childProfile : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) {owner who : ι} (hne : who ≠ owner)
    {debtFloor M : ℝ} (hdebtFloor : 0 < debtFloor)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : ∀ time player, |source time player| ≤ M)
    (hsourceNext : ∀ time, source (time + 1) =
      quittingRootSuccessorPayoff reward (source time) (roots time))
    (hchildNext : ∀ time, childProfile (time + 1) =
      quittingRootThenContinuationProfile reward
        (Function.update (roots time) owner (PMF.pure false))
        (childProfile time))
    (hroot : ∀ᶠ time in atTop,
      IsεQuittingRootNash reward (source time) 0 (roots time))
    (hforcedAbsorption : Summable (fun time =>
      quittingRootAbsorptionMass
        (Function.update (roots time) owner (PMF.pure false))))
    (hownerHazard : Summable (fun time =>
      ((roots time owner) true).toReal))
    (hdebt : ∀ᶠ time in atTop,
      debtFloor ≤ quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward
          (Function.update (roots time) owner (PMF.pure false))
          (childProfile time)) who)
    (hreset : ∃ᶠ time in atTop,
      quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward
              (Function.update (roots time) owner (PMF.pure false))
              (childProfile time))
            who (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
        quittingContinuationBestResponseValue reward
          (quittingRootThenContinuationProfile reward
            (Function.update (roots time) owner (PMF.pure false))
            (childProfile time)) who) :
    ∃ limit : ℝ,
      Tendsto (fun time =>
        quittingTerminalPayoff reward (childProfile time) who -
          source time who) atTop (nhds limit) ∧
      limit ≤ -debtFloor := by
  let child : ℕ → Payoff ι := fun time player =>
    quittingTerminalPayoff reward (childProfile time) player
  have hchildValueNext : ∀ time, child (time + 1) =
      quittingRootSuccessorPayoff reward (child time)
        (Function.update (roots time) owner (PMF.pure false)) := by
    intro time
    funext player
    simp only [child, hchildNext time,
      quittingTerminalPayoff_rootThenContinuation_eq]
    rfl
  obtain ⟨limit, hlimit⟩ := exists_tendsto_terminalChildPayoffDisplacement
    reward source child roots owner who hreward hsource
      (fun time player => abs_quittingTerminalPayoff_le
        reward (childProfile time) player hreward)
      hsourceNext hchildValueNext hforcedAbsorption hownerHazard
  change Tendsto (fun time =>
    quittingTerminalPayoff reward (childProfile time) who - source time who)
      atTop (nhds limit) at hlimit
  let survival : ℕ → ℝ := fun time => quittingRootOpponentContinueMass
    (Function.update (roots time) owner (PMF.pure false)) who
  let displacement : ℕ → ℝ := fun time =>
    quittingTerminalPayoff reward (childProfile time) who - source time who
  let error : ℕ → ℝ := fun time =>
    4 * M * ((roots time owner) true).toReal
  have hsurvival : Tendsto survival atTop (nhds 1) := by
    have hopponent : Summable (fun time =>
        quittingRootOpponentAbsorptionMass
          (Function.update (roots time) owner (PMF.pure false)) who) := by
      apply Summable.of_nonneg_of_le
        (fun _ => quittingRootOpponentAbsorptionMass_nonneg _ _)
        (fun time => quittingRootOpponentAbsorptionMass_le_absorptionMass _ _)
        hforcedAbsorption
    have habsorb := hopponent.tendsto_atTop_zero
    have hidentity : ∀ time, survival time = 1 -
        quittingRootOpponentAbsorptionMass
          (Function.update (roots time) owner (PMF.pure false)) who := by
      intro time
      exact quittingRootOpponentContinueMass_eq_one_sub_absorptionMass _ _
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    convert hone.sub habsorb using 1
    · funext time
      exact hidentity time
    · norm_num
  have herror : Tendsto error atTop (nhds 0) := by
    simpa [error] using
      hownerHazard.tendsto_atTop_zero.const_mul (4 * M)
  have hrhs : Tendsto (fun time =>
      -survival time * displacement time + error time) atTop
      (nhds (-limit)) := by
    convert (hsurvival.neg.mul (by simpa [displacement] using hlimit)).add
      herror using 1
    all_goals ring_nf
  have hlower : ∃ᶠ time in atTop, debtFloor ≤
      -survival time * displacement time + error time := by
    apply (hreset.and_eventually (hroot.and hdebt)).mono
    intro time htime
    have hstep :=
      debtFloor_sub_ownerHazardError_le_neg_payoffDisplacement_of_quitZeroCap
        reward (source time) (roots time) (childProfile time) hne hdebtFloor
          hreward (hsource time) htime.2.1 htime.1 htime.2.2
    change debtFloor - error time ≤ -survival time * displacement time at hstep
    linarith
  have hlimitLe : limit ≤ -debtFloor := by
    by_contra hnot
    have hstrict : -limit < debtFloor := by linarith
    have hsmall : ∀ᶠ time in atTop,
        -survival time * displacement time + error time < debtFloor :=
      (tendsto_order.1 hrhs).2 debtFloor hstrict
    obtain ⟨_, hlowerTime, hsmallTime⟩ :=
      (hlower.and_eventually hsmall).exists
    exact (not_lt_of_ge hlowerTime) hsmallTime
  exact ⟨limit, hlimit, hlimitLe⟩


end GameTheory
