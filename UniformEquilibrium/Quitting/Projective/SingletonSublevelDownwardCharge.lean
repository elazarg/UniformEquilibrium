import MathUE.Analysis.LowerBoxBoundaryMinimum
import UniformEquilibrium.Quitting.Paths.QuitEndpointOpponentBound
import UniformEquilibrium.Quitting.Root.BoundedSuccessorDisplacement
import UniformEquilibrium.Quitting.Root.NashExistence
import UniformEquilibrium.Quitting.Projective.ExactRootPotentialRestriction
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback

/-! # The signed downward-charge contradiction at a singleton binding

Return is needed only along the selected downward path. No other successor
singleton floor is asserted; the canonical forced-Quit error gives `3*M+bound`.
-/

noncomputable section

namespace GameTheory

open Set Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem not_isQuittingFullExactRootPotential_of_lowerBinding_selectedDownwardReturn
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound) (region : Set (Payoff ι)) (point : Payoff ι)
    (hpoint : point ∈ Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound))
    (player : ι) (hbind : point player = quittingSoloReward reward player player)
    (potential : Payoff ι → ℝ) (derivative : Payoff ι →L[ℝ] ℝ)
    (hmin : IsMinOn potential region point) (hdiff : HasFDerivAt potential derivative point)
    (hpartial : 0 ≤ derivative (Pi.single player 1))
    (hreturn : ∀ rate : ℝ, 0 < rate →
      (∀ coordinate, |(point + rate • (-Pi.single player (1 : ℝ)) : Payoff ι) coordinate| ≤ bound) →
      ∃ root, IsεQuittingRootNash reward (point + rate • (-Pi.single player 1)) 0 root ∧
        (0 < quittingRootAbsorptionMass root →
          quittingRootSuccessorPayoff reward
            (point + rate • (-Pi.single player 1)) root ∈ region)) :
    ¬IsQuittingFullExactRootPotential reward bound potential := by
  intro hpotential
  let lower : Payoff ι := fun who => quittingSoloReward reward who who
  have hM : 0 ≤ M := (abs_nonneg _).trans (hreward (quittingSingletonTerminal player) player)
  have hboundPos : 0 < bound := hM.trans_lt hbound
  have hchargeCoefficient : 0 < 3 * M + bound := by positivity
  have hbottom : ∀ coordinate, -bound < lower coordinate := fun coordinate =>
    (abs_lt.mp
      ((hreward (quittingSingletonTerminal coordinate) coordinate).trans_lt hbound)).1
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
    apply hdiff.comp_hasDerivAt_of_eq 0 hpath
    simp [path]
  have hlimit : Tendsto (fun rate : ℝ => rate⁻¹ * (potential (path rate) - potential point))
      (𝓝[>] 0) (𝓝 (derivative direction)) := by
    simpa [path] using hpotentialPath.tendsto_slope_zero_right
  have hpathLower : ∀ᶠ rate : ℝ in 𝓝[>] 0, ∀ coordinate, -bound ≤ path rate coordinate := by
    have hstrict : ∀ᶠ rate : ℝ in 𝓝[>] 0, ∀ coordinate, -bound < path rate coordinate := by
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
      1 / (3 * M + bound) ≤ rate⁻¹ * (potential (path rate) - potential point) := by
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
      simp [path, direction, hbind, lower, sub_eq_add_neg]
    obtain ⟨root, hnash, hrootReturn⟩ := hreturn rate hrate hbox
    have hquitError :=
      abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
        reward (path rate) root player M hreward
    have hopponent := quittingRootOpponentAbsorptionMass_le_absorptionMass root player
    have hquitLower : lower player - 2 * M * quittingRootAbsorptionMass root ≤
        quittingRootQuitPayoff reward (path rate) root player := by
      have herror := (abs_le.mp hquitError).1
      change -(2 * M * quittingRootOpponentAbsorptionMass root player) ≤
        quittingRootQuitPayoff reward (path rate) root player - lower player at herror
      nlinarith
    have hsuccessorLower := hquitLower.trans
      (quittingRootQuitPayoff_le_successor_of_isZeroNash reward (path rate) root player hnash)
    have hmove :=
      abs_quittingRootSuccessorPayoff_sub_tail_le_reward_add_source_mul_absorptionMass
        reward (path rate) root player M bound hreward (hbox player)
    have hcharge : rate ≤ (3 * M + bound) * quittingRootAbsorptionMass root := by
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
    have hminimum : potential point ≤
        potential (quittingRootSuccessorPayoff reward (path rate) root) :=
      hmin (hrootReturn hpositive)
    have hdecrease := hpotential (path rate) hbox root hnash
    have hchargeLower : rate / (3 * M + bound) ≤ quittingRootAbsorptionMass root :=
      (div_le_iff₀ hchargeCoefficient).mpr (by nlinarith [hcharge])
    rw [← div_eq_inv_mul, le_div_iff₀ hrate]
    have hscaled : 1 / (3 * M + bound) * rate ≤ quittingRootAbsorptionMass root := by
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hchargeLower
    exact hscaled.trans (by linarith only [hminimum, hdecrease])
  have hpositiveDerivative := ge_of_tendsto hlimit hratio
  have hpositiveCharge : 0 < 1 / (3 * M + bound) := div_pos (by norm_num) hchargeCoefficient
  linarith

/-- The original universal-return interface remains a thin instance of the
selected-root charge proof, with exactly its original hypotheses. -/
theorem not_isQuittingFullExactRootPotential_of_lowerBinding_downwardReturn
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound) (region : Set (Payoff ι)) (point : Payoff ι)
    (hpoint : point ∈ Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound))
    (player : ι) (hbind : point player = quittingSoloReward reward player player)
    (potential : Payoff ι → ℝ) (derivative : Payoff ι →L[ℝ] ℝ)
    (hmin : IsMinOn potential region point) (hdiff : HasFDerivAt potential derivative point)
    (hpartial : 0 ≤ derivative (Pi.single player 1))
    (hreturn : ∀ rate : ℝ, 0 < rate →
      (∀ coordinate, |(point + rate • (-Pi.single player (1 : ℝ)) : Payoff ι) coordinate| ≤ bound) →
      ∀ root, IsεQuittingRootNash reward (point + rate • (-Pi.single player 1)) 0 root →
      0 < quittingRootAbsorptionMass root →
        quittingRootSuccessorPayoff reward (point + rate • (-Pi.single player 1)) root ∈ region) :
    ¬IsQuittingFullExactRootPotential reward bound potential := by
  apply not_isQuittingFullExactRootPotential_of_lowerBinding_selectedDownwardReturn
    hreward hbound region point hpoint player hbind potential derivative hmin hdiff hpartial
  intro rate hrate hbox
  obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash (reward := reward)
    (point + rate • (-Pi.single player 1))
  exact ⟨root, hnash, hreturn rate hrate hbox root hnash⟩

end GameTheory
