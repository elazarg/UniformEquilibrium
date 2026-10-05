import MathUE.Analysis.ConvexSingletonSublevelMinimum
import UniformEquilibrium.Quitting.Projective.CompactSingletonSublevelMinimum
import UniformEquilibrium.Quitting.Projective.ExactRootMinimumTaylorExclusion
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialFaceDrift

/-! # Signed potential exclusion from a convex exact-root return domain

The closed convex region contains the whole singleton upper box. All boxed
sources return to that region, but only absorbing sources inside the region
return to its singleton-sublevel part. Differentiability is boundary-only.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem not_isQuittingFullExactRootPotential_of_convexReturnDomain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound) (region : Set (Payoff ι))
    (hclosed : IsClosed region) (hconvex : Convex ℝ region)
    (hregionBox : region ⊆ Icc (fun _ => -bound) (fun _ => bound))
    (hupperBox : Icc (fun player => quittingSoloReward reward player player)
      (fun _ => bound) ⊆ region)
    (hreturn : ∀ tail, (∀ player, |tail player| ≤ bound) →
      ∀ root, IsεQuittingRootNash reward tail 0 root →
        quittingRootSuccessorPayoff reward tail root ∈ region)
    (hsublevelReturn : ∀ tail ∈ region, ∀ root, IsεQuittingRootNash reward tail 0 root →
      0 < quittingRootAbsorptionMass root → ∃ player,
        quittingRootSuccessorPayoff reward tail root player ≤
          quittingSoloReward reward player player)
    (potential : Payoff ι → ℝ)
    (hcontinuous : ContinuousOn potential
      (region ∩ {point | ∃ player, point player ≤ quittingSoloReward reward player player}))
    (hdiff : ∀ point ∈ Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound),
        DifferentiableAt ℝ potential point) :
    ¬IsQuittingFullExactRootPotential reward bound potential := by
  intro hpotential
  let lower : Payoff ι := fun player => quittingSoloReward reward player player
  let upper : Payoff ι := fun _ => bound
  let domain : Set (Payoff ι) := region ∩ {point | ∃ player, point player ≤ lower player}
  have hregionCompact : IsCompact region :=
    isCompact_Icc.of_isClosed_subset hclosed hregionBox
  have hsublevelClosed : IsClosed {point : Payoff ι | ∃ player, point player ≤ lower player} := by
    have hclosedUnion := isClosed_iUnion_of_finite fun player : ι =>
      isClosed_le (continuous_apply player) (continuous_const (y := lower player))
    have hset : {point : Payoff ι | ∃ player, point player ≤ lower player} =
        ⋃ player : ι, {point : Payoff ι | point player ≤ lower player} := by
      ext point
      simp
    rw [← hset] at hclosedUnion
    exact hclosedUnion
  have hcompact : IsCompact domain := hregionCompact.inter_right hsublevelClosed
  have hboundary : Math.lowerBoxBoundary lower upper ⊆ domain := by
    intro point hpoint
    refine ⟨hupperBox hpoint.1, ?_⟩
    obtain ⟨player, hplayer⟩ := hpoint.2
    exact ⟨player, hplayer.le⟩
  have hbox : ∀ point ∈ domain, ∀ player, |point player| ≤ bound := by
    intro point hpoint player
    exact abs_le.mpr ⟨(hregionBox hpoint.1).1 player, (hregionBox hpoint.1).2 player⟩
  have hdomainReturn : ∀ point ∈ domain, ∀ root, IsεQuittingRootNash reward point 0 root →
      0 < quittingRootAbsorptionMass root →
        quittingRootSuccessorPayoff reward point root ∈ domain := by
    intro point hpoint root hnash hpositive
    exact ⟨hreturn point (hbox point hpoint) root hnash,
      hsublevelReturn point hpoint.1 root hnash hpositive⟩
  obtain ⟨point, hpoint, hpointDomain, hminDomain, hzero⟩ :=
    hpotential.exists_lowerBoundary_minimum_of_compactSublevelReturn hreward hbound
      domain hcompact hboundary hbox (fun _ hpoint => hpoint.2) hdomainReturn hcontinuous
  have hmin : IsMinOn potential (Math.lowerBoxBoundary lower upper) point :=
    fun other hother => hminDomain (hboundary hother)
  let derivative := fderiv ℝ potential point
  have hderivative : HasFDerivAt potential derivative point := (hdiff point hpoint).hasFDerivAt
  have hwidth : ∀ player, lower player < upper player := fun player =>
    ((le_abs_self _).trans (hreward (quittingSingletonTerminal player) player)).trans_lt hbound
  let face : ι → Payoff ι := quittingSoloReward reward
  have hfaceUpper : ∀ owner player, face owner player ≤ upper player := fun owner player =>
    (le_abs_self _).trans ((hreward (quittingSingletonTerminal owner) player).trans hbound.le)
  have hdrift : ∀ owner, point owner = lower owner → 0 < derivative (point - face owner) := by
    intro owner howner
    exact (show (0 : ℝ) < 1 by norm_num).trans_le
      (hpotential.singletonFace_drift hreward hbound point owner
        (fun player => ⟨hpoint.1.1 player, hpoint.1.2 player⟩) howner derivative hderivative)
  have hsigns := Math.lowerBoxBoundary_minimum_partial_signs lower upper point potential
    derivative face hpoint hmin hderivative hwidth (fun _ => rfl) hfaceUpper hdrift
  obtain ⟨player, hbind⟩ := hpoint.2
  apply not_isQuittingFullExactRootPotential_of_zeroAbsorptionFiber_derivativeCone
    hreward hbound point hpoint.1 player hbind potential derivative hderivative
    ((hsigns player).1 hbind) hzero _ hpotential
  intro tail htailBox root hnash
  have hsuccessorRegion := hreturn tail htailBox root hnash
  exact Math.convex_singletonSublevel_minimum_apply_sub_nonneg lower upper point
    (quittingRootSuccessorPayoff reward tail root) region hconvex hpointDomain.1
    hsuccessorRegion hpoint.1 (hregionBox hsuccessorRegion).2 potential derivative
    hminDomain hderivative hsigns

end GameTheory
