import UniformEquilibrium.Quitting.Classification.BoxedQuittingNashChargeOdds
import UniformEquilibrium.Quitting.RewardBound
import Mathlib.Order.Filter.Finite

/-! # Actual boxed Nash-charge singleton-sublevel return

The parameter `M` is any coordinate reward bound; in particular it may be the
packet's maximum absolute reward, rather than the larger canonical sum bound.
Finite strict trap margins select one common box before all sources and roots.
-/

noncomputable section

namespace GameTheory

open Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def HasBoxedQuittingNashCharges
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (M : ℝ) : Prop :=
  ∀ active, IsQuittingPremiumTrap reward active →
    ∃ coefficients : QuittingTrapChargeCoefficients reward active,
      (∑ player ∈ active, reward (quittingSingletonTerminal player) player) +
        (active.card : ℝ) * M < coefficients.threshold

omit [Fintype ι] in
theorem HasBoxedQuittingNashCharges.mono_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M smaller : ℝ}
    (hcharges : HasBoxedQuittingNashCharges reward M) (hle : smaller ≤ M) :
    HasBoxedQuittingNashCharges reward smaller := by
  intro active htrap
  obtain ⟨coefficients, hmargin⟩ := hcharges active htrap
  refine ⟨coefficients, lt_of_le_of_lt ?_ hmargin⟩
  simpa only [add_comm] using
    add_le_add_left (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg active.card))
      (∑ player ∈ active, reward (quittingSingletonTerminal player) player)

theorem exists_common_box_of_boxedQuittingNashCharges
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (M : ℝ)
    (hcharges : HasBoxedQuittingNashCharges reward M) :
    ∃ bound, M < bound ∧ bound < M + 2 ∧ HasBoxedQuittingNashCharges reward bound := by
  classical
  let Trap := {active : Finset ι // IsQuittingPremiumTrap reward active}
  let coefficients : ∀ active : Trap, QuittingTrapChargeCoefficients reward active.val :=
    fun active => Classical.choose (hcharges active.val active.property)
  have hmargin : ∀ active : Trap,
      (∑ player ∈ active.val, reward (quittingSingletonTerminal player) player) +
        (active.val.card : ℝ) * M < (coefficients active).threshold :=
    fun active => Classical.choose_spec (hcharges active.val active.property)
  have hnear : ∀ᶠ bound in 𝓝 M, ∀ active : Trap,
      (∑ player ∈ active.val, reward (quittingSingletonTerminal player) player) +
        (active.val.card : ℝ) * bound < (coefficients active).threshold := by
    rw [Filter.eventually_all]
    intro active
    have hcontinuous : Continuous (fun bound : ℝ =>
        (∑ player ∈ active.val, reward (quittingSingletonTerminal player) player) +
          (active.val.card : ℝ) * bound) :=
      continuous_const.add (continuous_const.mul continuous_id)
    exact hcontinuous.continuousAt.eventually_lt_const (hmargin active)
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let step := min (radius / 2) 1
  have hstep : 0 < step := lt_min (by linarith) zero_lt_one
  have hsmall : step < radius := (min_le_left _ _).trans_lt (by linarith)
  have htwo : step < 2 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨M + step, by linarith, by linarith, ?_⟩
  have hmember : M + step ∈ Metric.ball M radius := by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hstep]
    exact hsmall
  intro active htrap
  exact ⟨coefficients ⟨active, htrap⟩, hball hmember ⟨active, htrap⟩⟩

/-- Every absorbing exact root at every boxed annotation has some successor
at most its own singleton. No global premium or source-floor sign is used. -/
theorem exists_successor_le_singleton_of_boxedQuittingNashCharges
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ)
    (hcharges : HasBoxedQuittingNashCharges reward bound)
    (tail : Payoff ι) (hbox : ∀ player, |tail player| ≤ bound)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
      reward (quittingSingletonTerminal player) player := by
  by_cases htrap : IsQuittingPremiumTrap reward (quittingPositiveHazardSupport root)
  · obtain ⟨coefficients, hmargin⟩ := hcharges _ htrap
    by_contra hnot
    push Not at hnot
    have hendpoint :=
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash
    have hhigh : ∀ player ∈ quittingPositiveHazardSupport root,
        reward (quittingSingletonTerminal player) player <
          quittingRootQuitPayoff reward tail root player := by
      intro player hplayer
      have hpositive : 0 < (root player true).toReal := (Finset.mem_filter.mp hplayer).2
      have hquitNe : root player true ≠ 0 := by
        intro hzero
        rw [hzero] at hpositive
        norm_num at hpositive
      have hhigh := hnot player
      rw [quittingRootSuccessorPayoff_eq_quitPayoff_of_isZeroEndpointNash
        hendpoint player hquitNe] at hhigh
      exact hhigh
    have hcharge := coefficients.threshold_lt_singletonSourceCharge
      reward tail root hnash hhigh
    have hupper : (∑ player ∈ quittingPositiveHazardSupport root,
        (reward (quittingSingletonTerminal player) player - tail player)) ≤
        (∑ player ∈ quittingPositiveHazardSupport root,
          reward (quittingSingletonTerminal player) player) +
          ((quittingPositiveHazardSupport root).card : ℝ) * bound := by
      calc
        _ ≤ ∑ player ∈ quittingPositiveHazardSupport root,
            (reward (quittingSingletonTerminal player) player + bound) := by
          apply Finset.sum_le_sum
          intro player _
          have hlower := (abs_le.mp (hbox player)).1
          linarith
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    exact (not_lt_of_ge hupper) (hmargin.trans hcharge)
  · exact exists_successor_le_singleton_of_exactRoot_nontrap_support
      reward tail root hnash habsorption htrap

end GameTheory
