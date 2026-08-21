import UniformEquilibrium.Certificates.Public.FiniteHorizonProfileLawTransfer
import UniformEquilibrium.Certificates.Public.FixedPrefixAccounting
import UniformEquilibrium.Certificates.Public.TerminalChildLawTransfer
import UniformEquilibrium.ProofView.Concepts.Stochastic.Transform.Repeated.RealizedActionRepeatedAdapter

/-!
# Finite-horizon Nash continuations

A finite-horizon Nash profile remains Nash after every public history reached
with positive probability, for the remaining horizon.  A profitable child
deviation could otherwise be installed only on that public branch and would
strictly improve the root payoff.
-/

noncomputable section

namespace GameTheory.KernelGame

open Math.Probability
open Math.ProbabilityMassFunction
open scoped BigOperators

variable {ι : Type}

private noncomputable instance realizedActionHistDecidableEq
    (G : KernelGame ι) (length : ℕ) :
    DecidableEq (G.realizedActionStochasticGame.Hist length) :=
  Classical.decEq _

/-- Follow `profile` until `base`; on that public branch, replace one player's
continuation by `deviation`. -/
private noncomputable def realizedActionDeviationAfterHistory
    (G : KernelGame ι)
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    (who : ι) {prefixLength : ℕ}
    (base : G.realizedActionStochasticGame.Hist prefixLength)
    (deviation : G.realizedActionStochasticGame.BehaviorStrategy who) :
    G.realizedActionStochasticGame.BehaviorStrategy who := by
  classical
  exact fun time history =>
    if htime : prefixLength ≤ time then
      if G.realizedActionStochasticGame.terminalPrefixLE htime history = base then
        deviation (time - prefixLength)
          (G.realizedActionStochasticGame.terminalSuffixLE htime history)
      else
        profile who time history
    else
      profile who time history

private theorem realizedActionHist_startsAt
    (G : KernelGame ι) {prefixLength suffixLength : ℕ}
    (base : G.realizedActionStochasticGame.Hist prefixLength)
    (suffix : G.realizedActionStochasticGame.Hist suffixLength) :
    suffix.StartsAt base.2 := by
  cases base.2
  cases suffixLength with
  | zero =>
      simp only [StochasticGame.Hist.StartsAt]
      rfl
  | succ suffixLength =>
      simp only [StochasticGame.Hist.StartsAt]
      rfl

private theorem realizedAction_afterHistoryProfile_update_deviation
    (G : KernelGame ι) [DecidableEq ι]
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    (who : ι) {prefixLength : ℕ}
    (selected base : G.realizedActionStochasticGame.Hist prefixLength)
    (deviation : G.realizedActionStochasticGame.BehaviorStrategy who) :
    G.realizedActionStochasticGame.afterHistoryProfile
        (Function.update profile who
          (realizedActionDeviationAfterHistory
            G profile who selected deviation)) base =
      if base = selected then
        Function.update
          (G.realizedActionStochasticGame.afterHistoryProfile profile base)
          who deviation
      else
        G.realizedActionStochasticGame.afterHistoryProfile profile base := by
  classical
  funext player suffixLength suffix
  by_cases hplayer : player = who
  · subst player
    rw [G.realizedActionStochasticGame.afterHistoryProfile_apply]
    rw [Function.update_self]
    unfold realizedActionDeviationAfterHistory
    rw [dif_pos (Nat.le_add_right prefixLength suffixLength)]
    have hstart := realizedActionHist_startsAt G base suffix
    rw [G.realizedActionStochasticGame.terminalPrefixLE_appendHist
      base suffix hstart]
    by_cases hbase : base = selected
    · subst selected
      simp only [ite_true]
      rw [Function.update_self]
      congr 1
      · exact Nat.add_sub_cancel_left prefixLength suffixLength
      · exact G.realizedActionStochasticGame
          |>.terminalSuffixLE_appendHist_heq base suffix
    · simp [hbase]
  · split_ifs <;> simp [Function.update_of_ne hplayer]

private theorem realizedAction_update_deviation_agreeBefore
    (G : KernelGame ι) [DecidableEq ι]
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    (who : ι) {prefixLength : ℕ}
    (base : G.realizedActionStochasticGame.Hist prefixLength)
    (deviation : G.realizedActionStochasticGame.BehaviorStrategy who) :
    G.realizedActionStochasticGame.ProfilesAgreeBefore
      (Function.update profile who
        (realizedActionDeviationAfterHistory G profile who base deviation))
      profile prefixLength := by
  intro player time history htime
  by_cases hplayer : player = who
  · subst player
    simp only [Function.update_self]
    unfold realizedActionDeviationAfterHistory
    simp [Nat.not_le_of_lt htime]
  · simp [Function.update_of_ne hplayer]

private theorem realizedAction_expectedStagePayoff_eq_of_agreeBefore
    (G : KernelGame ι) [Fintype ι]
    [∀ player, Fintype (G.Strategy player)]
    {left right : G.realizedActionStochasticGame.BehaviorProfile}
    {fuel time : ℕ}
    (hagree : G.realizedActionStochasticGame.ProfilesAgreeBefore
      left right fuel)
    (htime : time < fuel) (who : ι) :
    G.realizedActionStochasticGame.expectedStagePayoff
        left PUnit.unit time who =
      G.realizedActionStochasticGame.expectedStagePayoff
        right PUnit.unit time who := by
  letI : Finite G.realizedActionStochasticGame.State :=
    inferInstanceAs (Finite PUnit)
  letI (player : ι) : Finite
      (G.realizedActionStochasticGame.Act player) :=
    @Finite.of_fintype _ (inferInstanceAs (Fintype (G.Strategy player)))
  unfold StochasticGame.expectedStagePayoff
  rw [G.realizedActionStochasticGame.histDist_eq_of_profilesAgreeBefore
    hagree time htime.le]
  apply expect_congr_on_support
  intro history _
  unfold StochasticGame.stageEUAt
  rw [G.realizedActionStochasticGame.stageActionDist_eq_of_profilesAgreeBefore
    hagree history htime]

private theorem realizedAction_expectedStagePayoff_add_eq_expect_afterHistory
    (G : KernelGame ι) [Fintype ι]
    [∀ player, Fintype (G.Strategy player)]
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    (prefixLength suffixLength : ℕ) (who : ι) :
    G.realizedActionStochasticGame.expectedStagePayoff profile PUnit.unit
        (prefixLength + suffixLength) who =
      expect (G.realizedActionStochasticGame.histDist
        profile PUnit.unit prefixLength) fun base =>
          G.realizedActionStochasticGame.expectedStagePayoff
            (G.realizedActionStochasticGame.afterHistoryProfile profile base)
            base.2 suffixLength who := by
  letI : Finite G.realizedActionStochasticGame.State :=
    inferInstanceAs (Finite PUnit)
  letI (player : ι) : Finite
      (G.realizedActionStochasticGame.Act player) :=
    @Finite.of_fintype _ (inferInstanceAs (Fintype (G.Strategy player)))
  unfold StochasticGame.expectedStagePayoff
  rw [G.realizedActionStochasticGame.histDist_add_eq_bind_histDistAfter,
    expect_bind]
  apply congrArg
  funext base
  unfold StochasticGame.histDistAfter
  rw [expect_map]
  rfl

private theorem realizedAction_cast_mul_finiteAveragePayoff_eq_sum
    (G : KernelGame ι) [Fintype ι]
    [∀ player, Fintype (G.Strategy player)]
    (horizon : ℕ)
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    (who : ι) :
    (horizon : ℝ) *
        G.realizedActionStochasticGame.finiteAveragePayoff
          PUnit.unit horizon profile who =
      ∑ time ∈ Finset.range horizon,
        G.realizedActionStochasticGame.expectedStagePayoff
          profile PUnit.unit time who := by
  letI : Finite G.realizedActionStochasticGame.State :=
    inferInstanceAs (Finite PUnit)
  letI (player : ι) : Finite
      (G.realizedActionStochasticGame.Act player) :=
    @Finite.of_fintype _ (inferInstanceAs (Fintype (G.Strategy player)))
  rw [G.realizedActionStochasticGame
    |>.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  by_cases hzero : horizon = 0
  · subst horizon
    simp
  · rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hzero), one_mul]

/-- A finite-horizon Nash continuation is inherited at every public history
reached with positive probability. -/
theorem realizedAction_afterHistoryProfile_isHorizonNash_of_mem_support
    (G : KernelGame ι) [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Strategy player)]
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    {prefixLength suffixLength : ℕ}
    (hnash : G.realizedActionStochasticGame.IsεHorizonNash PUnit.unit
      (prefixLength + suffixLength) 0 profile)
    (base : G.realizedActionStochasticGame.Hist prefixLength)
    (hbase : base ∈ (G.realizedActionStochasticGame.histDist
      profile PUnit.unit prefixLength).support) :
    G.realizedActionStochasticGame.IsεHorizonNash
      base.2 suffixLength 0
      (G.realizedActionStochasticGame.afterHistoryProfile profile base) := by
  letI : Finite G.realizedActionStochasticGame.State :=
    inferInstanceAs (Finite PUnit)
  letI (player : ι) : Finite
      (G.realizedActionStochasticGame.Act player) :=
    @Finite.of_fintype _ (inferInstanceAs (Fintype (G.Strategy player)))
  intro who deviation
  simp only [add_zero]
  by_cases hsuffixZero : suffixLength = 0
  · subst suffixLength
    rw [G.realizedActionStochasticGame
        |>.finiteAveragePayoff_eq_sum_expectedStagePayoff,
      G.realizedActionStochasticGame
        |>.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    simp
  let rootDeviation := realizedActionDeviationAfterHistory
    G profile who base deviation
  let deviated := Function.update profile who rootDeviation
  let prefixLaw := G.realizedActionStochasticGame.histDist
    profile PUnit.unit prefixLength
  let originalTotal : G.realizedActionStochasticGame.Hist prefixLength → ℝ :=
    fun reached => ∑ time ∈ Finset.range suffixLength,
      G.realizedActionStochasticGame.expectedStagePayoff
        (G.realizedActionStochasticGame.afterHistoryProfile profile reached)
        reached.2 time who
  let deviatedTotal : ℝ :=
    ∑ time ∈ Finset.range suffixLength,
      G.realizedActionStochasticGame.expectedStagePayoff
        (Function.update
          (G.realizedActionStochasticGame.afterHistoryProfile profile base)
          who deviation) base.2 time who
  have hagree := realizedAction_update_deviation_agreeBefore
    G profile who base deviation
  have hroot := hnash who rootDeviation
  have hscaled := mul_le_mul_of_nonneg_left hroot
    (by positivity : (0 : ℝ) ≤ prefixLength + suffixLength)
  have hdeviated := realizedAction_cast_mul_finiteAveragePayoff_eq_sum
    G (prefixLength + suffixLength) deviated who
  have horiginal := realizedAction_cast_mul_finiteAveragePayoff_eq_sum
    G (prefixLength + suffixLength) profile who
  rw [← Nat.cast_add] at hscaled
  simp only [add_zero] at hscaled
  change ((prefixLength + suffixLength : ℕ) : ℝ) *
      G.realizedActionStochasticGame.finiteAveragePayoff PUnit.unit
        (prefixLength + suffixLength) deviated who ≤
    ((prefixLength + suffixLength : ℕ) : ℝ) *
      G.realizedActionStochasticGame.finiteAveragePayoff PUnit.unit
        (prefixLength + suffixLength) profile who at hscaled
  rw [hdeviated, horiginal, Finset.sum_range_add,
    Finset.sum_range_add] at hscaled
  have hprefix :
      (∑ time ∈ Finset.range prefixLength,
          G.realizedActionStochasticGame.expectedStagePayoff
            deviated PUnit.unit time who) =
        ∑ time ∈ Finset.range prefixLength,
          G.realizedActionStochasticGame.expectedStagePayoff
            profile PUnit.unit time who := by
    apply Finset.sum_congr rfl
    intro time htime
    exact realizedAction_expectedStagePayoff_eq_of_agreeBefore
      G hagree (Finset.mem_range.mp htime) who
  rw [hprefix] at hscaled
  have hsuffix :
      (∑ time ∈ Finset.range suffixLength,
          G.realizedActionStochasticGame.expectedStagePayoff deviated PUnit.unit
            (prefixLength + time) who) ≤
        ∑ time ∈ Finset.range suffixLength,
          G.realizedActionStochasticGame.expectedStagePayoff profile PUnit.unit
            (prefixLength + time) who := by
    linarith
  have hdeviatedSuffix :
      (∑ time ∈ Finset.range suffixLength,
          G.realizedActionStochasticGame.expectedStagePayoff deviated PUnit.unit
            (prefixLength + time) who) =
        expect prefixLaw fun reached =>
          if reached = base then deviatedTotal else originalTotal reached := by
    simp_rw [realizedAction_expectedStagePayoff_add_eq_expect_afterHistory]
    rw [Math.Probability.sum_expect_range_comm]
    unfold prefixLaw
    rw [G.realizedActionStochasticGame.histDist_eq_of_profilesAgreeBefore
      hagree prefixLength le_rfl]
    apply expect_congr_on_support
    intro reached _
    unfold deviatedTotal originalTotal
    dsimp only [deviated, rootDeviation]
    rw [realizedAction_afterHistoryProfile_update_deviation]
    split_ifs with hreached
    · subst reached
      rfl
    · rfl
  have horiginalSuffix :
      (∑ time ∈ Finset.range suffixLength,
          G.realizedActionStochasticGame.expectedStagePayoff profile PUnit.unit
            (prefixLength + time) who) =
        expect prefixLaw originalTotal := by
    simp_rw [realizedAction_expectedStagePayoff_add_eq_expect_afterHistory]
    rw [Math.Probability.sum_expect_range_comm]
  rw [hdeviatedSuffix, horiginalSuffix] at hsuffix
  have htotal : deviatedTotal ≤ originalTotal base := by
    by_contra hnot
    have hstrict : originalTotal base < deviatedTotal := lt_of_not_ge hnot
    have hexpect := expect_lt_of_le_of_exists_lt prefixLaw originalTotal
      (fun reached =>
        if reached = base then deviatedTotal else originalTotal reached)
      (fun reached => by
        by_cases hreached : reached = base
        · subst reached
          simp [hstrict.le]
        · simp [hreached])
      ⟨base, by simpa [prefixLaw, PMF.mem_support_iff] using hbase, by
        simpa using hstrict⟩
    exact (not_lt_of_ge hsuffix) hexpect
  have hscale : (0 : ℝ) < suffixLength := by
    exact_mod_cast Nat.pos_of_ne_zero hsuffixZero
  have hdeviationPayoff :=
    realizedAction_cast_mul_finiteAveragePayoff_eq_sum G suffixLength
      (Function.update
        (G.realizedActionStochasticGame.afterHistoryProfile profile base)
        who deviation) who
  have horiginalPayoff :=
    realizedAction_cast_mul_finiteAveragePayoff_eq_sum G suffixLength
      (G.realizedActionStochasticGame.afterHistoryProfile profile base) who
  change (suffixLength : ℝ) *
      G.realizedActionStochasticGame.finiteAveragePayoff base.2 suffixLength
        (Function.update
          (G.realizedActionStochasticGame.afterHistoryProfile profile base)
          who deviation) who = deviatedTotal at hdeviationPayoff
  change (suffixLength : ℝ) *
      G.realizedActionStochasticGame.finiteAveragePayoff base.2 suffixLength
        (G.realizedActionStochasticGame.afterHistoryProfile profile base) who =
      originalTotal base at horiginalPayoff
  rw [← hdeviationPayoff, ← horiginalPayoff] at htotal
  nlinarith

end GameTheory.KernelGame
