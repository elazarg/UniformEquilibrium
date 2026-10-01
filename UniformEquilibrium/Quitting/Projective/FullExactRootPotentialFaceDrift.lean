import MathUE.Analysis.CollisionAdjustedDrift
import UniformEquilibrium.Quitting.Projective.ExactRootPotentialRestriction
import UniformEquilibrium.Quitting.Root.CollisionAdjustedSingletonProbe

/-! # Actual singleton-face drift of a full exact-root potential -/

noncomputable section

namespace GameTheory

open Set Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The quotient uses the actual successor at every positive rate below one.
The filter approaches zero through that entire rate interval. -/
theorem tendsto_quittingSingletonProbe_potential_differenceQuotient
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) (owner : ι)
    (potential : Payoff ι → ℝ) (derivative : Payoff ι →L[ℝ] ℝ)
    (hdiff : HasFDerivAt potential derivative point) :
    Tendsto (fun rate : Set.Ioo (0 : ℝ) 1 =>
      (potential (quittingSingletonProbeSource reward upper point owner rate) -
        potential (quittingSingletonProbeSuccessor reward upper point owner rate
          rate.property.1.le rate.property.2.le)) / rate)
      (Filter.comap Subtype.val (𝓝[>] (0 : ℝ)))
      (𝓝 (derivative (point - quittingSoloReward reward owner))) := by
  have hval : Tendsto (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ)
      (Filter.comap (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ) (𝓝[>] (0 : ℝ)))
      (𝓝[>] (0 : ℝ)) := tendsto_comap
  have hlimit := (Math.tendsto_collisionAdjusted_potential_differenceQuotient
    potential derivative point (quittingSingletonProbeCorrection reward upper point owner)
    (quittingSoloReward reward owner) hdiff).comp hval
  apply hlimit.congr
  intro rate
  have hsource : quittingSingletonProbeSource reward upper point owner rate =
      point + ((rate : ℝ) / (1 - rate)) •
        quittingSingletonProbeCorrection reward upper point owner := by
    ext who
    rfl
  have hsuccessor : quittingSingletonProbeSuccessor reward upper point owner rate
      rate.property.1.le rate.property.2.le = point + (rate : ℝ) •
        (quittingSingletonProbeCorrection reward upper point owner +
          quittingSoloReward reward owner - point) := by
    ext who
    exact quittingSingletonProbeSuccessor_eq_affine reward upper point owner rate
      rate.property.1.le rate.property.2.le (ne_of_lt rate.property.2) who
  rw [hsource, hsuccessor]
  rfl

/-- Full exact-root drift forces at least unit directional drift on every
singleton lower face, including its intersections with upper faces. -/
theorem IsQuittingFullExactRootPotential.singletonFace_drift
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {M bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hbound : M < bound) {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward bound potential)
    (point : Payoff ι) (owner : ι)
    (hpoint : ∀ who, quittingSoloReward reward who who ≤ point who ∧ point who ≤ bound)
    (howner : point owner = quittingSoloReward reward owner owner)
    (derivative : Payoff ι →L[ℝ] ℝ)
    (hdiff : HasFDerivAt potential derivative point) :
    1 ≤ derivative (point - quittingSoloReward reward owner) := by
  obtain ⟨ε, hε1, hε0, hprobe⟩ :=
    exists_small_rates_quittingSingletonProbe reward hreward hbound point owner hpoint howner
  let correction := quittingSingletonProbeCorrection reward bound point owner
  have hlimit := Math.tendsto_collisionAdjusted_potential_differenceQuotient
    potential derivative point correction (quittingSoloReward reward owner) hdiff
  have hquotient : ∀ᶠ rate : ℝ in 𝓝[>] 0,
      1 ≤ (potential (point + (rate / (1 - rate)) • correction) -
        potential (point + rate • (correction + quittingSoloReward reward owner - point))) /
        rate := by
    have hsmall : ∀ᶠ rate : ℝ in 𝓝[>] 0, rate < ε :=
      nhdsWithin_le_nhds (gt_mem_nhds hε0)
    filter_upwards [self_mem_nhdsWithin, hsmall] with rate hrate hsmall
    change 0 < rate at hrate
    obtain ⟨hsourceBox, hnash, _, habsorption⟩ := hprobe rate hrate hsmall
    have hdrift := hpotential (quittingSingletonProbeSource reward bound point owner rate)
      hsourceBox (quittingSingletonProbeRoot owner rate hrate.le
        (lt_trans hsmall hε1).le) hnash
    rw [habsorption] at hdrift
    have hsource : quittingSingletonProbeSource reward bound point owner rate =
        point + (rate / (1 - rate)) • correction := by ext who; rfl
    have hsuccessor : quittingSingletonProbeSuccessor reward bound point owner rate
        hrate.le (lt_trans hsmall hε1).le =
        point + rate • (correction + quittingSoloReward reward owner - point) := by
      ext who
      exact quittingSingletonProbeSuccessor_eq_affine reward bound point owner rate
        hrate.le (lt_trans hsmall hε1).le (ne_of_lt (lt_trans hsmall hε1)) who
    change potential (quittingSingletonProbeSuccessor reward bound point owner rate
      hrate.le (lt_trans hsmall hε1).le) + rate ≤
      potential (quittingSingletonProbeSource reward bound point owner rate) at hdrift
    rw [hsource, hsuccessor] at hdrift
    apply (le_div_iff₀ hrate).mpr
    linarith
  exact ge_of_tendsto hlimit hquotient

end GameTheory
