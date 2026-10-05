import UniformEquilibrium.Quitting.Root.CompactExactNashFiberMoat
import UniformEquilibrium.Quitting.Root.BoundedSuccessorDisplacement
import UniformEquilibrium.Quitting.Root.NashExistence
import UniformEquilibrium.Quitting.Paths.QuitEndpointOpponentBound
import UniformEquilibrium.Quitting.Projective.ExactRootPotentialRestriction
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback

/-! # Absorption-scale Taylor exclusion at an actual minimum

The exact fiber has zero absorption, while all boxed exact successors satisfy
the derivative cone. No individually protected successor floor or continuous
root selector is assumed. The signed scales are `3*M+bound` and `4*M+2*bound`.
-/

noncomputable section

namespace GameTheory

open Set Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem not_isQuittingFullExactRootPotential_of_zeroAbsorptionFiber_derivativeCone
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound) (point : Payoff ι)
    (hpoint : point ∈ Icc (fun player => quittingSoloReward reward player player) (fun _ => bound))
    (player : ι) (hbind : point player = quittingSoloReward reward player player)
    (potential : Payoff ι → ℝ) (derivative : Payoff ι →L[ℝ] ℝ)
    (hdiff : HasFDerivAt potential derivative point)
    (hpartial : 0 ≤ derivative (Pi.single player 1))
    (hzero : ∀ root, IsεQuittingRootNash reward point 0 root → quittingRootAbsorptionMass root = 0)
    (hcone : ∀ tail, (∀ coordinate, |tail coordinate| ≤ bound) →
      ∀ root, IsεQuittingRootNash reward tail 0 root →
        0 ≤ derivative (quittingRootSuccessorPayoff reward tail root - point)) :
    ¬IsQuittingFullExactRootPotential reward bound potential := by
  intro hpotential
  let lower : Payoff ι := fun coordinate => quittingSoloReward reward coordinate coordinate
  have hM : 0 ≤ M := (abs_nonneg _).trans (hreward (quittingSingletonTerminal player) player)
  have hboundPos : 0 < bound := hM.trans_lt hbound
  let C : ℝ := 3 * M + bound
  let W : ℝ := 4 * M + 2 * bound
  have hC : 0 < C := by dsimp [C]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hCW : C ≤ W := by dsimp [C, W]; linarith
  let eta : ℝ := 1 / (2 * (C + W))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hTaylor := hdiff.isLittleO.bound heta
  obtain ⟨radius, hradius, hlocal⟩ := Metric.eventually_nhds_iff.mp hTaylor
  let direction : Payoff ι := -Pi.single player 1
  let path : ℝ → Payoff ι := fun rate => point + rate • direction
  have hpath : ContinuousAt path 0 := by
    exact (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hpathPoint : path 0 = point := by simp [path]
  have hpathTendsto : Tendsto path (𝓝 0) (𝓝 point) := by
    change Tendsto path (𝓝 0) (𝓝 (path 0)) at hpath
    simpa only [hpathPoint] using hpath
  have hsmallAbs : ∀ᶠ rate : ℝ in 𝓝[>] 0, ∀ root,
      IsεQuittingRootNash reward (path rate) 0 root →
        quittingRootAbsorptionMass root < radius / (2 * W) := by
    apply nhdsWithin_le_nhds
    have hnear := eventually_exactRoot_absorption_lt_of_exact_fiber_absorption_zero
      reward point hzero (radius / (2 * W)) (by positivity)
    exact hpathTendsto.eventually hnear
  have hpathLower : ∀ᶠ rate : ℝ in 𝓝[>] 0,
      ∀ coordinate, -bound < path rate coordinate := by
    apply Filter.eventually_all.mpr
    intro coordinate
    have hcont := (continuous_apply coordinate).continuousAt.comp hpath
    apply nhdsWithin_le_nhds
    apply hcont.eventually (lt_mem_nhds ?_)
    have hbottom := (abs_lt.mp
      ((hreward (quittingSingletonTerminal coordinate) coordinate).trans_lt hbound)).1
    change -bound < path 0 coordinate
    rw [hpathPoint]
    exact hbottom.trans_le (hpoint.1 coordinate)
  have hgood : ∀ᶠ rate : ℝ in 𝓝[>] 0,
      0 < rate ∧ (∀ coordinate, |path rate coordinate| ≤ bound) ∧
      ∀ root, IsεQuittingRootNash reward (path rate) 0 root →
        quittingRootAbsorptionMass root < radius / (2 * W) := by
    filter_upwards [self_mem_nhdsWithin, hpathLower, hsmallAbs] with rate hrate hlower hsmall
    change 0 < rate at hrate
    refine ⟨hrate, fun coordinate => abs_le.mpr ⟨(hlower coordinate).le, ?_⟩, hsmall⟩
    have hnonpos : direction coordinate ≤ 0 := by
      by_cases heq : coordinate = player
      · subst coordinate
        simp [direction]
      · simp [direction, Pi.single_eq_of_ne heq]
    have hmul := mul_nonpos_of_nonneg_of_nonpos hrate.le hnonpos
    change point coordinate + rate * direction coordinate ≤ bound
    linarith [hpoint.2 coordinate]
  obtain ⟨rate, hrate, hbox, hsmall⟩ := hgood.exists
  obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash (reward := reward) (path rate)
  let absorption := quittingRootAbsorptionMass root
  let successor := quittingRootSuccessorPayoff reward (path rate) root
  have habsorption0 : 0 ≤ absorption := quittingRootAbsorptionMass_nonneg root
  have hvalue : path rate player = lower player - rate := by
    simp [path, direction, hbind, lower, sub_eq_add_neg]
  have hquitError :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (path rate) root player M hreward
  have hopponent := quittingRootOpponentAbsorptionMass_le_absorptionMass root player
  have hquitLower : lower player - 2 * M * absorption ≤
      quittingRootQuitPayoff reward (path rate) root player := by
    have herror := (abs_le.mp hquitError).1
    change -(2 * M * quittingRootOpponentAbsorptionMass root player) ≤
      quittingRootQuitPayoff reward (path rate) root player - lower player at herror
    dsimp [absorption]
    nlinarith
  have hsuccessorLower := hquitLower.trans
    (quittingRootQuitPayoff_le_successor_of_isZeroNash reward (path rate) root player hnash)
  have hcoordinateMove :=
    abs_quittingRootSuccessorPayoff_sub_tail_le_reward_add_source_mul_absorptionMass
      reward (path rate) root player M bound hreward (hbox player)
  have hcharge : rate ≤ C * absorption := by
    have hleabs := le_abs_self (successor player - path rate player)
    change |successor player - path rate player| ≤ (M + bound) * absorption at hcoordinateMove
    rw [hvalue] at hleabs hcoordinateMove
    dsimp only [C]
    linarith
  have habsorption : 0 < absorption := by
    by_contra hnot
    have hzero : absorption = 0 := le_antisymm (le_of_not_gt hnot) habsorption0
    rw [hzero, mul_zero] at hcharge
    linarith
  have hvnorm : ‖path rate - point‖ ≤ rate := by
    apply (pi_norm_le_iff_of_nonneg hrate.le).mpr
    intro coordinate
    by_cases heq : coordinate = player
    · subst coordinate
      simp [path, direction, Real.norm_eq_abs, abs_of_pos hrate]
    · simpa [path, direction, Pi.single_eq_of_ne heq] using hrate.le
  have hmoveNorm : ‖successor - path rate‖ ≤ (M + bound) * absorption := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) habsorption0)).mpr
    intro coordinate
    exact abs_quittingRootSuccessorPayoff_sub_tail_le_reward_add_source_mul_absorptionMass
      reward (path rate) root coordinate M bound hreward (hbox coordinate)
  have hvscale : ‖path rate - point‖ ≤ C * absorption := hvnorm.trans hcharge
  have hwscale : ‖successor - point‖ ≤ W * absorption := by
    calc
      ‖successor - point‖ ≤ ‖successor - path rate‖ + ‖path rate - point‖ :=
        by simpa only [dist_eq_norm] using dist_triangle successor (path rate) point
      _ ≤ (M + bound) * absorption + C * absorption := add_le_add hmoveNorm hvscale
      _ = W * absorption := by dsimp [C, W]; ring
  have hsmallProduct : W * absorption < radius / 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2 * W)).mp (hsmall root hnash)
    change absorption * (2 * W) < radius at h
    linarith
  have hwnear : dist successor point < radius := by
    rw [dist_eq_norm]
    exact hwscale.trans_lt (hsmallProduct.trans (half_lt_self hradius))
  have hvnear : dist (path rate) point < radius := by
    rw [dist_eq_norm]
    exact (hvscale.trans (mul_le_mul_of_nonneg_right hCW habsorption0)).trans_lt
      (hsmallProduct.trans (half_lt_self hradius))
  have hwerror := hlocal hwnear
  have hverror := hlocal hvnear
  have hvdirection : derivative (path rate - point) ≤ 0 := by
    have heq : path rate - point = rate • direction := by simp [path]
    rw [heq, map_smul]
    change rate * derivative direction ≤ 0
    apply mul_nonpos_of_nonneg_of_nonpos hrate.le
    simpa [direction] using neg_nonpos.mpr hpartial
  have hwcone := hcone (path rate) hbox root hnash
  change 0 ≤ derivative (successor - point) at hwcone
  have hvupper : potential (path rate) - potential point ≤ eta * (C * absorption) := by
    have h := le_abs_self (potential (path rate) - potential point - derivative (path rate - point))
    have hraw : |potential (path rate) - potential point - derivative (path rate - point)| ≤
        eta * ‖path rate - point‖ := by
      simpa only [Real.norm_eq_abs] using hverror
    have herror : |potential (path rate) - potential point - derivative (path rate - point)| ≤
        eta * (C * absorption) :=
      hraw.trans
        (mul_le_mul_of_nonneg_left hvscale heta.le)
    linarith
  have hwlower : -(eta * (W * absorption)) ≤ potential successor - potential point := by
    have hraw : |potential successor - potential point - derivative (successor - point)| ≤
        eta * ‖successor - point‖ := by
      simpa only [Real.norm_eq_abs] using hwerror
    have herror : |potential successor - potential point - derivative (successor - point)| ≤
        eta * (W * absorption) :=
      hraw.trans
        (mul_le_mul_of_nonneg_left hwscale heta.le)
    have h := (abs_le.mp herror).1
    linarith
  have hdecrease := hpotential (path rate) hbox root hnash
  change potential successor + absorption ≤ potential (path rate) at hdecrease
  have hsum : eta * (C * absorption) + eta * (W * absorption) = absorption / 2 := by
    dsimp [eta]
    field_simp [ne_of_gt (add_pos hC hW)]
  linarith

end GameTheory
