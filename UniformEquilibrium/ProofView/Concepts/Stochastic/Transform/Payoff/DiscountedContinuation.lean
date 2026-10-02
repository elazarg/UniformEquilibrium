import MathUE.ProbabilityMassFunction.Simplex
import UniformEquilibrium.Certificates.Public.FiniteHorizonProfileLawTransfer
import UniformEquilibrium.Certificates.Public.FixedDepthAdaptivePotentialSplice
import UniformEquilibrium.Certificates.Public.TerminalChildLawTransfer
import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Discounted

/-!
# Discounted continuation replacement

An actual behavioral profile disintegrates over its induced finite prefix law.
Replacing one complete public continuation changes the root discounted payoff
by the actual branch probability times the remaining geometric weight.
Finiteness supplies bounded stage payoffs; no payoff realizability certificate
or restriction on the behavioral profiles is assumed.
-/

noncomputable section

namespace GameTheory.StochasticGame

open _root_.Math.Probability
open scoped BigOperators

variable {ι : Type} (G : StochasticGame ι) [Fintype ι]
  [Finite G.State] [∀ who, Finite (G.Act who)]

/-- Retain the actual prefix and replace only the selected public branch. -/
noncomputable def replaceContinuation
    (profile : G.BehaviorProfile) {depth : ℕ}
    (selected : G.Hist depth) (replacement : G.BehaviorProfile) :
    G.BehaviorProfile := by
  classical
  exact G.terminalChildDispatcher depth profile
    (Function.update (G.afterHistoryProfile profile) selected replacement)

omit [Finite G.State] [∀ who, Finite (G.Act who)] in
private theorem expectedStagePayoff_eq_of_profilesAgreeBefore
    {left right : G.BehaviorProfile} {depth : ℕ}
    (hagree : G.ProfilesAgreeBefore left right depth)
    (initial : G.State) {time : ℕ} (htime : time < depth) (who : ι) :
    G.expectedStagePayoff left initial time who =
      G.expectedStagePayoff right initial time who := by
  unfold expectedStagePayoff
  rw [G.histDist_eq_of_profilesAgreeBefore hagree time htime.le]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro history _
  unfold stageEUAt
  rw [G.stageActionDist_eq_of_profilesAgreeBefore hagree history htime]

/-- Exact decomposition at every finite depth, including zero, for every
full behavioral profile and continuation factor in `[0,1)`. -/
theorem discountedPayoff_prefix_decomposition
    (profile : G.BehaviorProfile) (initial : G.State) (depth : ℕ)
    (who : ι) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    G.discountedPayoff β profile initial who =
      (1 - β) * (∑ time ∈ Finset.range depth,
        β ^ time * G.expectedStagePayoff profile initial time who) +
      β ^ depth * expect (G.histDist profile initial depth) (fun base =>
        G.discountedPayoff β (G.afterHistoryProfile profile base) base.2 who) := by
  obtain ⟨bound, hbound⟩ := exists_abs_bound_of_finite
    (fun data : G.State × G.JointAct => G.stagePayoff data.1 data.2 who)
  have hstage : ∀ state action, |G.stagePayoff state action who| ≤ bound :=
    fun state action => hbound (state, action)
  have hβabs : |β| < 1 := by rwa [abs_of_nonneg hβ0]
  have hsum := G.summable_discounted_expectedStagePayoff hstage profile initial hβabs
  have htail : (∑' time : ℕ,
      β ^ (time + depth) * G.expectedStagePayoff profile initial (time + depth) who) =
      β ^ depth * expect (G.histDist profile initial depth) (fun base =>
        ∑' time : ℕ, β ^ time *
          G.expectedStagePayoff (G.afterHistoryProfile profile base) base.2 time who) := by
    calc
      _ = β ^ depth * ∑' time : ℕ,
          expect (G.histDist profile initial depth) (fun base =>
            β ^ time * G.expectedStagePayoff
              (G.afterHistoryProfile profile base) base.2 time who) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro time
        rw [show time + depth = depth + time by omega,
          FixedDepthAdaptivePotentialSplice.expectedStagePayoff_add_eq_expect_afterHistory,
          pow_add, expect_const_mul]
        ring
      _ = _ := by
        congr 1
        exact tsum_expect_comm _ _ fun base =>
          G.summable_discounted_expectedStagePayoff hstage
            (G.afterHistoryProfile profile base) base.2 hβabs
  unfold discountedPayoff
  rw [← hsum.sum_add_tsum_nat_add depth, htail, mul_add]
  rw [expect_const_mul]
  ring

/-- Dispatching arbitrary complete child profiles retains the discounted
prefix and averages the child payoffs over the original prefix law. -/
theorem discountedPayoff_terminalChildDispatcher
    (profile : G.BehaviorProfile) (initial : G.State) (depth : ℕ)
    (child : G.Hist depth → G.BehaviorProfile) (who : ι)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    G.discountedPayoff β (G.terminalChildDispatcher depth profile child) initial who =
      (1 - β) * (∑ time ∈ Finset.range depth,
        β ^ time * G.expectedStagePayoff profile initial time who) +
      β ^ depth * expect (G.histDist profile initial depth) (fun base =>
        G.discountedPayoff β (child base) base.2 who) := by
  let dispatched := G.terminalChildDispatcher depth profile child
  have hagree : G.ProfilesAgreeBefore dispatched profile depth := by
    intro player time history htime
    exact G.terminalChildDispatcher_before profile child htime player history
  have hprefix : (∑ time ∈ Finset.range depth,
      β ^ time * G.expectedStagePayoff dispatched initial time who) =
      ∑ time ∈ Finset.range depth,
        β ^ time * G.expectedStagePayoff profile initial time who := by
    apply Finset.sum_congr rfl
    intro time htime
    rw [expectedStagePayoff_eq_of_profilesAgreeBefore G hagree initial
      (Finset.mem_range.mp htime) who]
  have hchild (base : G.Hist depth) :
      G.discountedPayoff β (G.afterHistoryProfile dispatched base) base.2 who =
        G.discountedPayoff β (child base) base.2 who := by
    dsimp only [dispatched]
    rw [G.afterHistoryProfile_terminalChildDispatcher_canonical]
    unfold discountedPayoff
    congr 1
    apply tsum_congr
    intro time
    rw [G.expectedStagePayoff_canonicalTerminalChildProfile
      depth profile child base time who]
  have h := G.discountedPayoff_prefix_decomposition
    dispatched initial depth who hβ0 hβ1
  rw [hprefix, G.histDist_eq_of_profilesAgreeBefore hagree depth le_rfl] at h
  simp_rw [hchild] at h
  exact h

/-- A one-stage dispatcher into an actual convex payoff set stays in that
set when its actual first-stage payoff and supported actual child payoffs do. -/
theorem discountedPayoff_terminalChildDispatcher_mem_convex
    (profile : G.BehaviorProfile) (initial : G.State)
    (child : G.Hist 1 → G.BehaviorProfile) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (P : Set (Payoff ι)) (hconvex : Convex ℝ P)
    (hfirst : (fun who => G.stageEUAt profile (G.emptyHist initial) who) ∈ P)
    (hchildren : ∀ base ∈ (G.histDist profile initial 1).support,
      (fun who => G.discountedPayoff β (child base) base.2 who) ∈ P) :
    (fun who => G.discountedPayoff β
      (G.terminalChildDispatcher 1 profile child) initial who) ∈ P := by
  let : Fintype (G.Hist 1) := Fintype.ofFinite _
  let tail := fun who => expect (G.histDist profile initial 1) (fun base =>
    G.discountedPayoff β (child base) base.2 who)
  have htail : tail ∈ P :=
    Math.ProbabilityMassFunction.coordinateExpectation_mem_convex_of_mem_support
      (G.histDist profile initial 1)
      (fun base who => G.discountedPayoff β (child base) base.2 who)
      P hconvex hchildren
  have hequal : (fun who => G.discountedPayoff β
      (G.terminalChildDispatcher 1 profile child) initial who) =
      (1 - β) • (fun who => G.stageEUAt profile (G.emptyHist initial) who) +
        β • tail := by
    funext who
    simpa only [Finset.sum_range_one, pow_zero, pow_one, one_mul,
      G.expectedStagePayoff_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      G.discountedPayoff_terminalChildDispatcher profile initial 1 child who hβ0 hβ1
  rw [hequal]
  exact hconvex hfirst htail (by linarith) hβ0 (by ring)

/-- The selected branch uses its actual terminal state and actual induced
probability. The identity also covers unreachable branches and discount zero. -/
theorem discountedPayoff_replaceContinuation
    (profile : G.BehaviorProfile) (initial : G.State) {depth : ℕ}
    (selected : G.Hist depth) (replacement : G.BehaviorProfile) (who : ι)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    G.discountedPayoff β (G.replaceContinuation profile selected replacement) initial who =
      G.discountedPayoff β profile initial who +
        β ^ depth * (G.histDist profile initial depth selected).toReal *
          (G.discountedPayoff β replacement selected.2 who -
            G.discountedPayoff β (G.afterHistoryProfile profile selected) selected.2 who) := by
  classical
  let : Fintype (G.Hist depth) := Fintype.ofFinite _
  let child := Function.update (G.afterHistoryProfile profile) selected replacement
  have hnew := G.discountedPayoff_terminalChildDispatcher
    profile initial depth child who hβ0 hβ1
  have hold := G.discountedPayoff_prefix_decomposition profile initial depth who hβ0 hβ1
  have hfunction : (fun base => G.discountedPayoff β (child base) base.2 who) =
      Function.update (fun base => G.discountedPayoff β
        (G.afterHistoryProfile profile base) base.2 who)
        selected (G.discountedPayoff β replacement selected.2 who) := by
    funext base
    by_cases hbase : base = selected
    · subst base
      simp [child]
    · simp [child, Function.update_of_ne hbase]
  rw [hfunction, Math.ProbabilityMassFunction.expect_functionUpdate] at hnew
  change G.discountedPayoff β
    (G.terminalChildDispatcher depth profile child) initial who = _
  rw [hnew, hold]
  ring

omit [Finite G.State] [∀ who, Finite (G.Act who)] in
/-- With positive continuation discount and positive depth, the branch
coefficient is strictly between zero and one at every reached history. -/
theorem continuationCoefficient_mem_Ioo
    (profile : G.BehaviorProfile) (initial : G.State) {depth : ℕ}
    (hdepth : 0 < depth) (selected : G.Hist depth)
    (hsupport : selected ∈ (G.histDist profile initial depth).support)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    β ^ depth * (G.histDist profile initial depth selected).toReal ∈ Set.Ioo 0 1 := by
  let law := G.histDist profile initial depth
  have hmass : 0 < (law selected).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff law selected).mp hsupport)
      (law.apply_ne_top selected)
  have hmassOne : (law selected).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one law selected)
  constructor
  · exact mul_pos (pow_pos hβ0 depth) hmass
  · calc
      β ^ depth * (law selected).toReal ≤ β ^ depth * 1 :=
        mul_le_mul_of_nonneg_left hmassOne (pow_nonneg hβ0.le depth)
      _ = β ^ depth := mul_one _
      _ < 1 := pow_lt_one₀ hβ0.le hβ1 (Nat.ne_of_gt hdepth)

end GameTheory.StochasticGame
