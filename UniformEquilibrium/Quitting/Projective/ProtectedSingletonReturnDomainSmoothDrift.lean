import MathUE.Analysis.LowerBoxBoundaryMinimum
import UniformEquilibrium.Quitting.Classification.NonnegativeProductLowExactRootBoundary
import UniformEquilibrium.Quitting.Paths.QuitEndpointOpponentBound
import UniformEquilibrium.Quitting.Root.BelowSingletonRootAbsorption
import UniformEquilibrium.Quitting.Root.BoundedSuccessorDisplacement
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialFaceDrift
import UniformEquilibrium.Quitting.Root.NashExistence

/-! # Smooth exclusion from a compact protectedPlayer singleton return domain -/

noncomputable section

namespace GameTheory

open Set Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A compact return region between the singleton boundary and its protectedPlayer
sublevel domain excludes a full exact-root potential. Continuity is required
only on that region, and differentiation only on the singleton boundary. -/
theorem not_isQuittingFullExactRootPotential_of_protectedSingletonReturnDomain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (protectedPlayer : ι)
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound)
    (region : Set (Payoff ι)) (hcompact : IsCompact region)
    (hboundary : Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound) ⊆ region)
    (hregion : ∀ point ∈ region,
      (∀ player, |point player| ≤ bound) ∧
      quittingSoloReward reward protectedPlayer protectedPlayer ≤ point protectedPlayer)
    (hsublevel : ∀ point ∈ region,
      ∃ player, point player ≤ quittingSoloReward reward player player)
    (hreturn : ∀ tail, (∀ player, |tail player| ≤ bound) →
      quittingSoloReward reward protectedPlayer protectedPlayer ≤ tail protectedPlayer →
      ∀ root, IsεQuittingRootNash reward tail 0 root →
      0 < quittingRootAbsorptionMass root →
        quittingRootSuccessorPayoff reward tail root ∈ region)
    (potential : Payoff ι → ℝ) (hcontinuous : ContinuousOn potential region)
    (hdiff : ∀ point ∈ Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound),
        DifferentiableAt ℝ potential point) :
    ¬ IsQuittingFullExactRootPotential reward bound potential := by
  intro hpotential
  let : Nonempty ι := ⟨protectedPlayer⟩
  let lower : Payoff ι := fun player => quittingSoloReward reward player player
  let upper : Payoff ι := fun _ => bound
  let face : ι → Payoff ι := quittingSoloReward reward
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal protectedPlayer) protectedPlayer)
  have hboundPos : 0 < bound := hM.trans_lt hbound
  have hchargeCoefficient : 0 < 3 * M + bound := by positivity
  have hrewardBox : ∀ terminal player, |reward terminal player| ≤ bound :=
    fun terminal player => (hreward terminal player).trans hbound.le
  have hwidth : ∀ player, lower player < upper player := fun player =>
    ((le_abs_self _).trans (hreward (quittingSingletonTerminal player) player)).trans_lt
      hbound
  have hbottom : ∀ player, -bound < lower player := fun player =>
    (abs_lt.mp ((hreward (quittingSingletonTerminal player) player).trans_lt hbound)).1
  obtain ⟨point, hpointRegion, hminRegion⟩ :=
    hcompact.exists_isMinOn
      ((Math.lowerBoxBoundary_nonempty lower upper
        fun player => (hwidth player).le).mono hboundary) hcontinuous
  have hpointBox := (hregion point hpointRegion).1
  have hpointFloor := (hregion point hpointRegion).2
  have hpointLower : ∀ player, lower player ≤ point player := by
    intro player
    by_contra hnot
    have hgap : 0 < lower player - point player := sub_pos.mpr (lt_of_not_ge hnot)
    obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash (reward := reward) point
    have hmass := belowSingleton_exactRoot_absorptionMass_lowerBound reward point root
      player hgap hreward (by
        change point player ≤ lower player - (lower player - point player)
        linarith) hnash
    have hpositive : 0 < quittingRootAbsorptionMass root :=
      (div_pos hgap (by positivity : 0 < 2 * M + (lower player - point player))).trans_le
        hmass
    have hrootReturn := hreturn point hpointBox hpointFloor root hnash hpositive
    have hminimum := hminRegion hrootReturn
    change potential point ≤ potential (quittingRootSuccessorPayoff reward point root)
      at hminimum
    have hdecrease := hpotential point hpointBox root hnash
    linarith
  have hpoint : point ∈ Math.lowerBoxBoundary lower upper := by
    refine ⟨⟨hpointLower, fun player => (abs_le.mp (hpointBox player)).2⟩, ?_⟩
    obtain ⟨player, hplayer⟩ := hsublevel point hpointRegion
    exact ⟨player, le_antisymm hplayer (hpointLower player)⟩
  have hmin : IsMinOn potential (Math.lowerBoxBoundary lower upper) point :=
    fun other hother => hminRegion (hboundary hother)
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
  obtain ⟨player, hbind, hplayerProtected⟩ := htwo protectedPlayer
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
      simp [path, direction, hbind, sub_eq_add_neg]
    obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash (reward := reward) (path rate)
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
      (quittingRootQuitPayoff_le_successor_of_isZeroNash
        reward (path rate) root player hnash)
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
    have hfloor : lower protectedPlayer ≤ path rate protectedPlayer := by
      simpa [path, direction, Pi.single_eq_of_ne hplayerProtected.symm] using
        hpoint.1.1 protectedPlayer
    have hrootReturn := hreturn (path rate) hbox hfloor root hnash hpositive
    have hminimum : potential point ≤
        potential (quittingRootSuccessorPayoff reward (path rate) root) :=
      hminRegion hrootReturn
    have hdecrease := hpotential (path rate) hbox root hnash
    have hchargeLower : rate / (3 * M + bound) ≤ quittingRootAbsorptionMass root :=
      (div_le_iff₀ hchargeCoefficient).mpr (by nlinarith [hcharge])
    rw [← div_eq_inv_mul, le_div_iff₀ hrate]
    have hscaled : 1 / (3 * M + bound) * rate ≤ quittingRootAbsorptionMass root := by
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hchargeLower
    exact hscaled.trans (by linarith only [hminimum, hdecrease])
  have hpositiveDerivative := ge_of_tendsto hlimit hratio
  have hpositiveCharge : 0 < 1 / (3 * M + bound) :=
    div_pos (by norm_num) hchargeCoefficient
  linarith

end GameTheory
