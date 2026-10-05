import MathUE.Analysis.LowerBoxBoundaryMinimum
import UniformEquilibrium.Quitting.Classification.TwoPlayerPremiumCoreExactRootBoundary
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialFaceDrift
import UniformEquilibrium.Quitting.Root.NashExistence

/-! # Smooth full-root potential exclusion for strict-leave premium cores

The actual-root return theorem requires only the first core annotation floor.
At a lower-boundary minimum, the existing face geometry supplies another binding
coordinate. Lowering it preserves that floor and gives a charged return.
Signed singleton rewards are permitted.
-/

noncomputable section

namespace GameTheory

open Set Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Strict-leave premium cores admit no full exact-root potential differentiable
at every point of the singleton lower boundary. All exact roots at all boxed
annotations are tested, without a strategy-realizability premise. -/
theorem not_isQuittingFullExactRootPotential_of_twoPlayerPremiumCore_strictLeave
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (first second : ι) (hne : first ≠ second)
    (houtside : ∀ player, player ≠ first → player ≠ second →
      ∀ terminal, player ∈ terminal.val →
        reward terminal player = reward (quittingSingletonTerminal player) player)
    (hleave : reward ⟨{first, second}, by simp⟩ first <
      reward (quittingSingletonTerminal second) first)
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound)
    (potential : Payoff ι → ℝ)
    (hdiff : ∀ point ∈ Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound),
        DifferentiableAt ℝ potential point) :
    ¬ IsQuittingFullExactRootPotential reward bound potential := by
  intro hpotential
  let : Nonempty ι := ⟨first⟩
  let lower : Payoff ι := fun player => quittingSoloReward reward player player
  let upper : Payoff ι := fun _ => bound
  let face : ι → Payoff ι := quittingSoloReward reward
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal first) first)
  have hboundPos : 0 < bound := hM.trans_lt hbound
  have htwoBound : 0 < 2 * bound := mul_pos (by norm_num) hboundPos
  have hrewardBox : ∀ terminal player, |reward terminal player| ≤ bound :=
    fun terminal player => (hreward terminal player).trans hbound.le
  have hwidth : ∀ player, lower player < upper player := fun player =>
    ((le_abs_self _).trans (hreward (quittingSingletonTerminal player) player)).trans_lt
      hbound
  have hbottom : ∀ player, -bound < lower player := fun player =>
    (abs_lt.mp ((hreward (quittingSingletonTerminal player) player).trans_lt hbound)).1
  obtain ⟨point, hpoint, hmin⟩ :=
    (Math.isCompact_lowerBoxBoundary lower upper).exists_isMinOn
      (Math.lowerBoxBoundary_nonempty lower upper fun player => (hwidth player).le)
      (fun point hpoint => (hdiff point hpoint).continuousAt.continuousWithinAt)
  let derivative := fderiv ℝ potential point
  have hderivative : HasFDerivAt potential derivative point :=
    (hdiff point hpoint).hasFDerivAt
  have hfaceUpper : ∀ owner player, face owner player ≤ upper player :=
    fun owner player => (le_abs_self _).trans
      ((hreward (quittingSingletonTerminal owner) player).trans hbound.le)
  have hdrift : ∀ owner, point owner = lower owner →
      0 < derivative (point - face owner) := by
    intro owner howner
    exact (show (0 : ℝ) < 1 by norm_num).trans_le
      (hpotential.singletonFace_drift hreward hbound point owner
        (fun player => ⟨hpoint.1.1 player, hpoint.1.2 player⟩)
        howner derivative hderivative)
  have htwo := Math.lowerBoxBoundary_minimum_has_two_bindings
    lower upper point potential derivative face hpoint hmin hderivative hwidth
    (fun _ => rfl) hfaceUpper hdrift
  obtain ⟨player, hbind, hplayerFirst⟩ := htwo first
  obtain ⟨other, hother, hotherPlayer⟩ := htwo player
  have hpartial : 0 ≤ derivative (Pi.single player 1) :=
    Math.lowerBoxBoundary_minimum_partial_nonneg lower upper point potential
      derivative hpoint hmin hderivative player other hotherPlayer hbind hother
      (hwidth player)
  let direction : Payoff ι := -Pi.single player 1
  let path : ℝ → Payoff ι := fun rate => point + rate • direction
  have hdirection : derivative direction ≤ 0 := by
    simpa [direction] using neg_nonpos.mpr hpartial
  have hpath : HasDerivAt path direction 0 := by
    convert! (hasDerivAt_const (0 : ℝ) point).add
      ((hasDerivAt_id (0 : ℝ)).smul_const direction) using 1
    simp only [zero_add, one_smul]
  have hpotentialPath : HasDerivAt (fun rate => potential (path rate))
      (derivative direction) 0 := by
    apply hderivative.comp_hasDerivAt_of_eq 0 hpath
    simp [path]
  have hlimit : Tendsto (fun rate : ℝ =>
      rate⁻¹ * (potential (path rate) - potential point))
      (𝓝[>] 0) (𝓝 (derivative direction)) := by
    simpa [path] using hpotentialPath.tendsto_slope_zero_right
  have hpathLower : ∀ᶠ rate : ℝ in 𝓝[>] 0,
      ∀ coordinate, -bound ≤ path rate coordinate := by
    have hstrict : ∀ᶠ rate : ℝ in 𝓝[>] 0,
        ∀ coordinate, -bound < path rate coordinate := by
      apply Filter.eventually_all.mpr
      intro coordinate
      have hcont : ContinuousAt (fun rate => path rate coordinate) 0 :=
        (continuous_apply coordinate).continuousAt.comp hpath.continuousAt
      apply nhdsWithin_le_nhds
      apply hcont.eventually (lt_mem_nhds ?_)
      simpa only [path, zero_smul, add_zero] using
        (hbottom coordinate).trans_le (hpoint.1.1 coordinate)
    exact hstrict.mono fun rate hrate coordinate => (hrate coordinate).le
  have hratio : ∀ᶠ rate : ℝ in 𝓝[>] 0,
      1 / (2 * bound) ≤ rate⁻¹ * (potential (path rate) - potential point) := by
    filter_upwards [self_mem_nhdsWithin, hpathLower] with rate hrate hlower
    change 0 < rate at hrate
    have hbox : ∀ coordinate, |path rate coordinate| ≤ bound := by
      intro coordinate
      apply abs_le.mpr
      refine ⟨hlower coordinate, ?_⟩
      have hnonpos : direction coordinate ≤ 0 := by
        by_cases heq : coordinate = player
        · subst coordinate
          simp [direction]
        · simp [direction, Pi.single_eq_of_ne heq]
      have hmul := mul_nonpos_of_nonneg_of_nonpos hrate.le hnonpos
      have hupper := hpoint.1.2 coordinate
      change point coordinate + rate * direction coordinate ≤ bound
      linarith
    have hvalue : path rate player = lower player - rate := by
      simp [path, direction, hbind, sub_eq_add_neg]
    obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash (reward := reward) (path rate)
    have hsuccessorLower : lower player ≤
        quittingRootSuccessorPayoff reward (path rate) root player :=
      (quittingSingletonReward_le_rootQuitPayoff_of_nonnegativePremium
        hnonnegative (path rate) root player).trans
          (quittingRootQuitPayoff_le_successor_of_isZeroNash
            reward (path rate) root player hnash)
    have hmove := abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
      reward (path rate) root player bound hrewardBox (hbox player)
    have hcharge : rate ≤ 2 * bound * quittingRootAbsorptionMass root := by
      have hleabs := le_abs_self
        (quittingRootSuccessorPayoff reward (path rate) root player - path rate player)
      rw [hvalue] at hleabs hmove
      linarith
    have hpositive : 0 < quittingRootAbsorptionMass root := by
      by_contra hnot
      have hzero : quittingRootAbsorptionMass root = 0 :=
        le_antisymm (le_of_not_gt hnot) (quittingRootAbsorptionMass_nonneg root)
      rw [hzero, mul_zero] at hcharge
      linarith
    have hfloor : lower first ≤ path rate first := by
      simpa [path, direction, Pi.single_eq_of_ne hplayerFirst.symm] using
        hpoint.1.1 first
    obtain ⟨hsuccessor, owner, _, howner⟩ :=
      exactRootSuccessor_mem_singletonLowerBoundary_of_twoPlayerPremiumCore_strictLeave
        hnonnegative first second hne houtside hleave (path rate) hfloor root hnash
        hpositive
    have hreturn : quittingRootSuccessorPayoff reward (path rate) root ∈
        Math.lowerBoxBoundary lower upper := by
      refine ⟨⟨hsuccessor, fun coordinate => ?_⟩, owner, howner⟩
      exact (le_abs_self _).trans
        (abs_quittingRootSuccessorPayoff_le_bound reward (path rate) root coordinate
          hrewardBox hbox)
    have hminimum : potential point ≤
        potential (quittingRootSuccessorPayoff reward (path rate) root) := hmin hreturn
    have hdecrease := hpotential (path rate) hbox root hnash
    have hchargeLower : rate / (2 * bound) ≤ quittingRootAbsorptionMass root :=
      (div_le_iff₀ htwoBound).mpr (by nlinarith [hcharge])
    rw [← div_eq_inv_mul, le_div_iff₀ hrate]
    have hscaled : 1 / (2 * bound) * rate ≤ quittingRootAbsorptionMass root := by
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hchargeLower
    exact hscaled.trans (by linarith only [hminimum, hdecrease])
  have hpositiveDerivative := ge_of_tendsto hlimit hratio
  have hpositiveCharge : 0 < 1 / (2 * bound) :=
    div_pos (by norm_num) htwoBound
  linarith

end GameTheory
