import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.Order.Compact

/-! # Smooth drift exclusion at the lower boundary of a box -/

noncomputable section

namespace Math

open Set Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The union of the lower coordinate faces of a finite box. -/
def lowerBoxBoundary (lower upper : ι → ℝ) : Set (ι → ℝ) :=
  Set.Icc lower upper ∩ {point | ∃ player, point player = lower player}

omit [Nonempty ι] [DecidableEq ι] in
theorem isCompact_lowerBoxBoundary (lower upper : ι → ℝ) :
    IsCompact (lowerBoxBoundary lower upper) := by
  apply isCompact_Icc.inter_right
  have hclosed := isClosed_iUnion_of_finite fun player : ι =>
    isClosed_eq (continuous_apply player) (continuous_const (y := lower player))
  simpa only [Set.iUnion_setOf] using hclosed

omit [Fintype ι] [DecidableEq ι] in
theorem lowerBoxBoundary_nonempty (lower upper : ι → ℝ)
    (hbox : lower ≤ upper) : (lowerBoxBoundary lower upper).Nonempty := by
  exact ⟨lower, ⟨⟨le_refl _, hbox⟩, ⟨Classical.arbitrary ι, rfl⟩⟩⟩

omit [Nonempty ι] in
/-- At a minimum on the union of lower faces, every binding coordinate has
nonnegative partial derivative if another coordinate also binds. -/
theorem lowerBoxBoundary_minimum_partial_nonneg
    (lower upper point : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (derivative : (ι → ℝ) →L[ℝ] ℝ)
    (hpoint : point ∈ lowerBoxBoundary lower upper)
    (hmin : IsMinOn potential (lowerBoxBoundary lower upper) point)
    (hdiff : HasFDerivAt potential derivative point)
    (player other : ι) (hne : other ≠ player)
    (hplayer : point player = lower player)
    (hother : point other = lower other)
    (hupper : lower player < upper player) :
    0 ≤ derivative (Pi.single player 1) := by
  have hlocal : IsLocalMinOn potential (lowerBoxBoundary lower upper) point :=
    Filter.mem_of_superset self_mem_nhdsWithin hmin
  apply hlocal.hasFDerivWithinAt_nonneg hdiff.hasFDerivWithinAt
  apply mem_posTangentConeAt_of_frequently_mem
  apply Filter.Eventually.frequently
  have hsmall : ∀ᶠ rate : ℝ in 𝓝[>] 0, rate < upper player - lower player :=
    nhdsWithin_le_nhds (gt_mem_nhds (sub_pos.mpr hupper))
  filter_upwards [self_mem_nhdsWithin, hsmall] with rate hrate hsmall
  refine ⟨⟨?_, ?_⟩, ⟨other, ?_⟩⟩
  · intro coordinate
    by_cases heq : coordinate = player
    · subst coordinate
      simpa [hplayer] using hrate.le
    · simpa [Pi.single_eq_of_ne heq] using hpoint.1.1 coordinate
  · intro coordinate
    by_cases heq : coordinate = player
    · subst coordinate
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      linarith
    · simpa [Pi.single_eq_of_ne heq] using hpoint.1.2 coordinate
  · simpa [Pi.single_eq_of_ne hne] using hother

/-- A differentiable potential cannot strictly decrease from every
single-binding boundary point while providing a fixed linear decrease into
that boundary from every point below one of its faces. -/
theorem not_differentiable_lowerBoxBoundary_drift
    (bottom lower upper : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (hbottom : ∀ player, bottom player < lower player)
    (hupper : ∀ player, lower player < upper player)
    (hdiff : ∀ point ∈ Set.Icc bottom upper, DifferentiableAt ℝ potential point)
    (charge : ℝ) (hcharge : 0 < charge)
    (hsingle : ∀ point ∈ lowerBoxBoundary lower upper, ∀ player,
      (∀ other, point other = lower other → other = player) →
        ∃ target ∈ lowerBoxBoundary lower upper, potential target < potential point)
    (hbelow : ∀ point ∈ Set.Icc bottom upper, ∀ player,
      point player < lower player →
        ∃ target ∈ lowerBoxBoundary lower upper,
          charge * (lower player - point player) ≤ potential point - potential target) :
    False := by
  have hsubset : lowerBoxBoundary lower upper ⊆ Set.Icc bottom upper := by
    intro point hpoint
    exact ⟨fun player => (hbottom player).le.trans (hpoint.1.1 player), hpoint.1.2⟩
  obtain ⟨point, hpoint, hmin⟩ :=
    (isCompact_lowerBoxBoundary lower upper).exists_isMinOn
      (lowerBoxBoundary_nonempty lower upper fun player => (hupper player).le)
      (fun point hpoint => (hdiff point (hsubset hpoint)).continuousAt.continuousWithinAt)
  have hother : ∀ player, ∃ other, point other = lower other ∧ other ≠ player := by
    intro player
    by_contra hnone
    have honly : ∀ other, point other = lower other → other = player := by
      intro other hbind
      by_contra hne
      exact hnone ⟨other, hbind, hne⟩
    obtain ⟨target, htarget, hlt⟩ := hsingle point hpoint player honly
    exact (not_lt_of_ge (hmin htarget)) hlt
  let derivative := fderiv ℝ potential point
  have hderivative : HasFDerivAt potential derivative point :=
    (hdiff point (hsubset hpoint)).hasFDerivAt
  have hpartial : ∀ player, point player = lower player →
      0 ≤ derivative (Pi.single player 1) := by
    intro player hplayer
    obtain ⟨other, hbind, hne⟩ := hother player
    exact lowerBoxBoundary_minimum_partial_nonneg lower upper point potential
      derivative hpoint hmin hderivative player other hne hplayer hbind (hupper player)
  let direction : ι → ℝ := fun player => if point player = lower player then -1 else 0
  have hdirection : derivative direction ≤ 0 := by
    conv_lhs => rw [pi_eq_sum_univ' direction]
    rw [map_sum]
    apply Finset.sum_nonpos
    intro player _
    rw [map_smul]
    by_cases hbind : point player = lower player
    · simpa [direction, hbind] using neg_nonpos.mpr (hpartial player hbind)
    · simp [direction, hbind]
  let path : ℝ → ι → ℝ := fun rate => point + rate • direction
  have hpath : HasDerivAt path direction 0 := by
    convert! (hasDerivAt_const (0 : ℝ) point).add
      ((hasDerivAt_id (0 : ℝ)).smul_const direction) using 1
    simp only [zero_add, one_smul]
  have hpotential : HasDerivAt (fun rate => potential (path rate))
      (derivative direction) 0 := by
    apply hderivative.comp_hasDerivAt_of_eq 0 hpath
    simp [path]
  have hlimit : Tendsto (fun rate : ℝ => rate⁻¹ *
      (potential (path rate) - potential point)) (𝓝[>] 0) (𝓝 (derivative direction)) := by
    simpa [path] using hpotential.tendsto_slope_zero_right
  have hpathLower : ∀ᶠ rate : ℝ in 𝓝[>] 0, ∀ player,
      bottom player ≤ path rate player := by
    have hstrict : ∀ᶠ rate : ℝ in 𝓝[>] 0, ∀ player,
        bottom player < path rate player := by
      apply Filter.eventually_all.mpr
      intro player
      have hcont : ContinuousAt (fun rate : ℝ => path rate player) 0 :=
        (continuous_apply player).continuousAt.comp hpath.continuousAt
      apply nhdsWithin_le_nhds
      apply hcont.eventually (lt_mem_nhds ?_)
      simpa only [path, zero_smul, add_zero] using
        (hbottom player).trans_le (hpoint.1.1 player)
    exact hstrict.mono fun rate hrate player => (hrate player).le
  have hratio : ∀ᶠ rate : ℝ in 𝓝[>] 0,
      charge ≤ rate⁻¹ * (potential (path rate) - potential point) := by
    filter_upwards [self_mem_nhdsWithin, hpathLower] with rate hrate hlower
    change 0 < rate at hrate
    have hbox : path rate ∈ Set.Icc bottom upper := by
      refine ⟨hlower, fun player => ?_⟩
      have hnonpos : direction player ≤ 0 := by
        simp only [direction]
        split_ifs <;> norm_num
      have hbound := hpoint.1.2 player
      have hmul := mul_nonpos_of_nonneg_of_nonpos hrate.le hnonpos
      change point player + rate * direction player ≤ upper player
      linarith
    obtain ⟨player, hbind⟩ := hpoint.2
    have hvalue : path rate player = lower player - rate := by
      simp [path, direction, hbind, sub_eq_add_neg]
    obtain ⟨target, htarget, hdecrease⟩ := hbelow (path rate) hbox player (by
      rw [hvalue]
      linarith)
    have hminimum : potential point ≤ potential target := hmin htarget
    rw [hvalue] at hdecrease
    rw [← div_eq_inv_mul, le_div_iff₀ hrate]
    nlinarith
  have hpositive := ge_of_tendsto hlimit hratio
  linarith

end Math
