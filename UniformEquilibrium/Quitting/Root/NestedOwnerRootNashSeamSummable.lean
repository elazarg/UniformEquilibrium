import UniformEquilibrium.Quitting.Root.NestedChildBellmanEndpointDifference
import UniformEquilibrium.Quitting.Root.NestedCapChildFixedDebtor
import UniformEquilibrium.Quitting.Root.OpponentCoalitionPayoff

/-!
# Owner root optimality and summable cap-child seam terms

The forced-Continue owner is root-optimal when its complete debt is zero.
The first, second, and fourth terms of the outsider endpoint decomposition
are summable under summable owner hazard. The third, nonlocal displacement
term is not bounded by this argument.
-/

noncomputable section
namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Zero complete debt of a literal prefixed profile makes its prescribed
pure-Continue root marginal a best response for that coordinate. -/
theorem quittingRootEndpointDifference_nonpos_of_prefixed_debt_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) (who : ι)
    (hroot : root who = PMF.pure false)
    (hdebt : quittingTerminalDeviationDebt reward
      (quittingRootThenContinuationProfile reward root continuation) who = 0) :
    quittingRootEndpointDifference reward
      (fun player => quittingTerminalPayoff reward continuation player)
      root who ≤ 0 := by
  let profile := quittingRootThenContinuationProfile reward root continuation
  let deviation := quittingRootAndContinuationDeviation reward
    (PMF.pure true) (continuation who)
  have hcap := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile who deviation
  have hquit : quittingTerminalPayoff reward
      (Function.update profile who deviation) who =
      quittingRootQuitPayoff reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who := by
    rw [quittingTerminalPayoff_update_rootAndContinuationDeviation_eq]
    simp only [Function.update_eq_self]
    rfl
  have hprescribed : quittingTerminalPayoff reward profile who =
      quittingRootSuccessorPayoff reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who := by
    exact quittingTerminalPayoff_rootThenContinuation_eq
      reward root continuation who
  unfold quittingTerminalDeviationDebt at hdebt
  unfold quittingRootEndpointDifference
  rw [hquit] at hcap
  rw [hprescribed] at hdebt
  have hcontinue : quittingRootSuccessorPayoff reward
      (fun player => quittingTerminalPayoff reward continuation player)
      root who = quittingRootContinuePayoff reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who := by
    have hmix := quittingRootExpectedPayoff_update_coord_eq_mix reward
      (fun player => quittingTerminalPayoff reward continuation player)
      root who (root who) who
    rw [Function.update_eq_self] at hmix
    unfold quittingRootSuccessorPayoff
    rw [hmix, hroot]
    simp
    rfl
  rw [hcontinue] at hdebt
  change quittingContinuationBestResponseValue reward profile who -
      quittingRootContinuePayoff reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who = 0 at hdebt
  linarith

/-- Along a nested child genealogy, zero owner debt makes the prescribed
forced-Continue owner action root-Nash at every child transition. -/
theorem quittingNestedCapChild_owner_rootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (children : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hnested : ∀ depth, children (depth + 1) =
      quittingRootThenContinuationProfile reward
        (Function.update (roots depth) owner (PMF.pure false))
        (children depth))
    (hdebt : ∀ depth,
      quittingTerminalDeviationDebt reward (children depth) owner = 0) :
    ∀ depth, quittingRootEndpointDifference reward
      (fun player => quittingTerminalPayoff reward (children depth) player)
      (Function.update (roots depth) owner (PMF.pure false)) owner ≤ 0 := by
  intro depth
  apply quittingRootEndpointDifference_nonpos_of_prefixed_debt_zero
    reward _ (children depth) owner
  · simp
  · rw [← hnested depth]
    exact hdebt (depth + 1)

/-- For an outsider, forcing the owner to Continue changes opponent survival
by at most the owner's displayed Quit probability. -/
theorem abs_quittingRootOpponentContinueMass_forcedContinue_sub_le
    (root : ι → PMF Bool) {owner who : ι} (hne : who ≠ owner) :
    |quittingRootOpponentContinueMass
          (Function.update root owner (PMF.pure false)) who -
        quittingRootOpponentContinueMass root who| ≤
      (root owner true).toReal := by
  let base := Function.update root who (PMF.pure false)
  have hcommute : Function.update
      (Function.update root owner (PMF.pure false)) who (PMF.pure false) =
      Function.update base owner (PMF.pure false) := by
    exact Function.update_comm hne.symm _ _ _
  have hfactor :=
    quittingStationaryContinueMass_eq_forcedContinue_mul_own base owner
  have hbaseOwner : base owner = root owner := by
    simp [base, hne.symm]
  unfold quittingRootOpponentContinueMass
  rw [hcommute]
  rw [hbaseOwner] at hfactor
  have hforced0 := quittingStationaryContinueMass_nonneg
    (Function.update base owner (PMF.pure false))
  have hforced1 := quittingStationaryContinueMass_le_one
    (Function.update base owner (PMF.pure false))
  have hsum := quittingRoot_continueProbability_add_quitProbability root owner
  rw [hfactor]
  have heq : quittingStationaryContinueMass
          (Function.update base owner (PMF.pure false)) -
        quittingStationaryContinueMass
            (Function.update base owner (PMF.pure false)) *
          (root owner false).toReal =
      quittingStationaryContinueMass
          (Function.update base owner (PMF.pure false)) *
        (root owner true).toReal := by
    rw [show quittingStationaryContinueMass
          (Function.update base owner (PMF.pure false)) -
        quittingStationaryContinueMass
            (Function.update base owner (PMF.pure false)) *
          (root owner false).toReal =
        quittingStationaryContinueMass
            (Function.update base owner (PMF.pure false)) *
          (1 - (root owner false).toReal) by ring]
    have : 1 - (root owner false).toReal = (root owner true).toReal := by
      linarith
    rw [this]
  rw [heq, abs_mul, abs_of_nonneg hforced0,
    abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_of_le_one_left ENNReal.toReal_nonneg hforced1

/-- The first expanded outsider seam term is summable: changing the child
tail is irrelevant to a pure-Quit endpoint, and forcing the owner to Continue
costs at most `2M` times the owner's Quit hazard. -/
theorem summable_nestedChildSeam_quitPayoffDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source child : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    {owner who : ι} (hne : who ≠ owner) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hownerHazard : Summable (fun time =>
      (roots time owner true).toReal)) :
    Summable (fun time =>
      quittingRootQuitPayoff reward (child time)
          (Function.update (roots time) owner (PMF.pure false)) who -
        quittingRootQuitPayoff reward (source time) (roots time) who) := by
  have hM : 0 ≤ M :=
    (abs_nonneg (reward (quittingSingletonTerminal who) who)).trans
      (hreward (quittingSingletonTerminal who) who)
  have hmajorant : Summable (fun time =>
      (roots time owner true).toReal * (2 * M)) :=
    hownerHazard.mul_right (2 * M)
  apply hmajorant.of_norm_bounded
  intro time
  rw [Real.norm_eq_abs,
    quittingRootQuitPayoff_continuation_invariant reward (child time) 0,
    quittingRootQuitPayoff_continuation_invariant reward (source time) 0]
  let base := Function.update (roots time) who (PMF.pure true)
  have hcommute : Function.update
      (Function.update (roots time) owner (PMF.pure false)) who (PMF.pure true) =
      Function.update base owner (PMF.pure false) :=
    Function.update_comm hne.symm _ _ _
  unfold quittingRootQuitPayoff
  rw [hcommute]
  have hbound := abs_quittingRootExpectedPayoff_update_coord_sub_self_le
    reward (0 : Payoff ι) base owner who (PMF.pure false)
      hreward (fun _ => by simpa using hM)
  simpa [base, hne.symm, mul_comm] using hbound

/-- The second expanded seam term, the change in the Continue absorbing
numerator, is summable under the same owner-hazard hypothesis. -/
theorem summable_nestedChildSeam_absorbingContributionDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {owner who : ι} (hne : who ≠ owner) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hM : 0 ≤ M)
    (hownerHazard : Summable (fun time =>
      (roots time owner true).toReal)) :
    Summable (fun time =>
      quittingRootAbsorbingContribution reward
          (Function.update
            (Function.update (roots time) owner (PMF.pure false))
            who (PMF.pure false)) who -
        quittingRootAbsorbingContribution reward
          (Function.update (roots time) who (PMF.pure false)) who) := by
  have hmajorant : Summable (fun time =>
      (roots time owner true).toReal * (2 * M)) :=
    hownerHazard.mul_right (2 * M)
  apply hmajorant.of_norm_bounded
  intro time
  rw [Real.norm_eq_abs]
  let base := Function.update (roots time) who (PMF.pure false)
  have hcommute : Function.update
      (Function.update (roots time) owner (PMF.pure false)) who (PMF.pure false) =
      Function.update base owner (PMF.pure false) :=
    Function.update_comm hne.symm _ _ _
  unfold quittingRootAbsorbingContribution
  rw [hcommute]
  have hbound := abs_quittingRootExpectedPayoff_update_coord_sub_self_le
    reward (0 : Payoff ι) base owner who (PMF.pure false)
      hreward (fun _ => by simpa using hM)
  simpa [base, hne.symm, mul_comm] using hbound

/-- The fourth expanded seam term is summable: its survival-coefficient
change is bounded by the owner hazard and the literal source payoff is bounded. -/
theorem summable_nestedChildSeam_survivalDifference_mul_source
    (roots : ℕ → ι → PMF Bool) (source : ℕ → Payoff ι)
    {owner who : ι} (hne : who ≠ owner) {M : ℝ}
    (hsource : ∀ time player, |source time player| ≤ M)
    (hownerHazard : Summable (fun time =>
      (roots time owner true).toReal)) :
    Summable (fun time =>
      (quittingRootOpponentContinueMass
          (Function.update (roots time) owner (PMF.pure false)) who -
        quittingRootOpponentContinueMass (roots time) who) * source time who) := by
  have hmajorant : Summable (fun time =>
      (roots time owner true).toReal * M) := hownerHazard.mul_right M
  apply hmajorant.of_norm_bounded
  intro time
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul
    (abs_quittingRootOpponentContinueMass_forcedContinue_sub_le
      (roots time) hne)
    (hsource time who) (abs_nonneg _) ENNReal.toReal_nonneg

end GameTheory
