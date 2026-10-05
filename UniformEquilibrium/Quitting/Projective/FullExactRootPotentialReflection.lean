import MathUE.Analysis.LowerBoxBoundaryReflection
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialMinimum

/-! # Adaptive radial reversal of every full exact-root potential minimum

The rectangle is chosen from the supplied global minimum, including minima
on upper faces. The minimum gap, boundary minimizer and reflected endpoint
are produced from the full-root hypothesis, not supplied as favorable data.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Every global minimum produces the packet's quantitative radial reversal
on its adaptive lower rectangle, with the entire reflected segment boxed. -/
theorem IsQuittingFullExactRootPotential.radialReversal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ quittingSoloReward reward who who)
    {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward 3 potential)
    (hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => 3), DifferentiableAt ℝ potential point)
    (minimum : Payoff ι) (hminimum : ∀ who, |minimum who| ≤ 3)
    (hmin : IsMinOn potential (Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3)) minimum) :
    let gap := Finset.univ.inf' Finset.univ_nonempty
      (fun who => minimum who - quittingSoloReward reward who who)
    0 < gap ∧ ∃ point,
      point ∈ Math.lowerBoxBoundary (fun who => quittingSoloReward reward who who)
        (fun who => max (minimum who) 1) ∧
      IsMinOn potential (Math.lowerBoxBoundary (fun who => quittingSoloReward reward who who)
        (fun who => max (minimum who) 1)) point ∧
      fderiv ℝ potential point (point - minimum) ≤ -gap / 2 ∧
      2 • point - minimum ∈ Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3) ∧
      (∀ time ∈ Set.Icc (0 : ℝ) 2, minimum + time • (point - minimum) ∈
        Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3)) := by
  let lower : Payoff ι := fun who => quittingSoloReward reward who who
  let upper : Payoff ι := fun who => max (minimum who) 1
  let gap := Finset.univ.inf' Finset.univ_nonempty (fun who => minimum who - lower who)
  have habove : ∀ who, lower who < minimum who :=
    hpotential.minimum_above_singleton_of_differentiable hreward
      (by norm_num : (1 : ℝ) < 3) hdiff minimum hminimum hmin
  have hgap : 0 < gap := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro who _
    exact sub_pos.mpr (habove who)
  have hwidth : ∀ who, lower who < upper who :=
    fun who => (habove who).trans_le (le_max_left _ _)
  have hupper : ∀ who, upper who ≤ 3 := by
    intro who
    exact max_le ((le_abs_self _).trans (hminimum who)) (by norm_num)
  have hsubset : Set.Icc lower upper ⊆ Set.Icc lower (fun _ => 3) := by
    intro point hpoint
    exact ⟨hpoint.1, fun who => (hpoint.2 who).trans (hupper who)⟩
  obtain ⟨point, hpoint, hpointMin⟩ :=
    (Math.isCompact_lowerBoxBoundary lower upper).exists_isMinOn
      (Math.lowerBoxBoundary_nonempty lower upper (fun who => (hwidth who).le))
      (fun point hpoint => (hdiff point (hsubset hpoint.1)).continuousAt.continuousWithinAt)
  have hpointDiff : HasFDerivAt potential (fderiv ℝ potential point) point :=
    (hdiff point (hsubset hpoint.1)).hasFDerivAt
  have hfaceUpper : ∀ owner who, quittingSoloReward reward owner who ≤ upper who := by
    intro owner who
    exact ((le_abs_self _).trans (hreward (quittingSingletonTerminal owner) who)).trans
      (le_max_right _ _)
  have hfaceGap : ∀ owner who, lower who - quittingSoloReward reward owner who ≤ 2 := by
    intro owner who
    have hself := abs_le.mp (hreward (quittingSingletonTerminal who) who)
    have hother := abs_le.mp (hreward (quittingSingletonTerminal owner) who)
    change -1 ≤ quittingSoloReward reward who who ∧
      quittingSoloReward reward who who ≤ 1 at hself
    change -1 ≤ quittingSoloReward reward owner who ∧
      quittingSoloReward reward owner who ≤ 1 at hother
    change quittingSoloReward reward who who - quittingSoloReward reward owner who ≤ 2
    linarith
  have hdrift : ∀ owner, point owner = lower owner →
      1 ≤ fderiv ℝ potential point (point - quittingSoloReward reward owner) := by
    intro owner howner
    exact hpotential.singletonFace_drift hreward (by norm_num : (1 : ℝ) < 3)
      point owner (fun who => ⟨hpoint.1.1 who, (hpoint.1.2 who).trans (hupper who)⟩)
      howner (fderiv ℝ potential point) hpointDiff
  have hquantitative := Math.lowerBoxBoundary_minimum_derivative_toward_ge_half_gap
    lower upper point potential (fderiv ℝ potential point) (quittingSoloReward reward)
    hpoint hpointMin hpointDiff hwidth (fun _ => rfl) hfaceUpper hfaceGap hdrift
    minimum gap hgap.le (fun who => Finset.inf'_le _ (Finset.mem_univ who))
    (fun _ => le_max_left _ _)
  have hnegative : fderiv ℝ potential point (point - minimum) ≤ -gap / 2 := by
    have hneg : fderiv ℝ potential point (point - minimum) =
        -fderiv ℝ potential point (minimum - point) := by
      rw [← map_neg, neg_sub]
    rw [hneg]
    linarith
  have hminimumNonneg : minimum ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 3) :=
    ⟨fun who => (hsingleton who).trans (habove who).le,
      fun who => (le_abs_self _).trans (hminimum who)⟩
  exact ⟨hgap, point, hpoint, hpointMin, hnegative,
    Math.adaptiveLowerBox_reflection_mem lower minimum point hsingleton
      hminimumNonneg hpoint.1,
    fun time htime => Math.adaptiveLowerBox_segment_mem lower minimum point hsingleton
      hminimumNonneg hpoint.1 time htime⟩

/-- Every global minimum has a boxed segment on which the potential rises
to an interior maximum and subsequently falls before the lower-face point. -/
theorem IsQuittingFullExactRootPotential.exists_rise_and_fall
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ quittingSoloReward reward who who)
    {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward 3 potential)
    (hcontinuous : ContinuousOn potential (Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3)))
    (hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => 3), DifferentiableAt ℝ potential point)
    (minimum : Payoff ι) (hminimum : ∀ who, |minimum who| ≤ 3)
    (hmin : IsMinOn potential (Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3)) minimum) :
    let gap := Finset.univ.inf' Finset.univ_nonempty
      (fun who => minimum who - quittingSoloReward reward who who)
    0 < gap ∧ ∃ point time, point ∈ Math.lowerBoxBoundary
        (fun who => quittingSoloReward reward who who) (fun who => max (minimum who) 1) ∧
      IsMinOn potential (Math.lowerBoxBoundary (fun who => quittingSoloReward reward who who)
        (fun who => max (minimum who) 1)) point ∧
      fderiv ℝ potential point (point - minimum) ≤ -gap / 2 ∧
      2 • point - minimum ∈ Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3) ∧
      time ∈ Set.Ioo (0 : ℝ) 1 ∧
      potential minimum < potential (minimum + time • (point - minimum)) ∧
      potential point < potential (minimum + time • (point - minimum)) ∧
      IsMaxOn (fun rate => potential (minimum + rate • (point - minimum)))
        (Set.Icc (0 : ℝ) 1) time ∧
      (∀ rate ∈ Set.Icc (0 : ℝ) 2, minimum + rate • (point - minimum) ∈
        Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3)) := by
  obtain ⟨hgap, point, hpoint, hpointMin, hnegative, hreflection, hsegment⟩ :=
    hpotential.radialReversal hreward hsingleton hdiff minimum hminimum hmin
  let path : ℝ → Payoff ι := fun rate => minimum + rate • (point - minimum)
  have hpath : Continuous path := continuous_const.add (continuous_id.smul continuous_const)
  have hcontinuousLine : ContinuousOn (fun rate => potential (path rate))
      (Set.Icc (0 : ℝ) 1) := hcontinuous.comp hpath.continuousOn
        (fun rate hrate => hsegment rate ⟨hrate.1, hrate.2.trans (by norm_num)⟩)
  have hpointC : point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => 3) := by
    refine ⟨hpoint.1.1, fun who => ?_⟩
    exact (hpoint.1.2 who).trans
      (max_le ((le_abs_self _).trans (hminimum who)) (by norm_num))
  have hpathDerivative : HasDerivAt path (point - minimum) 1 := by
    simpa [path] using ((hasDerivAt_id (1 : ℝ)).smul_const
      (point - minimum)).const_add minimum
  have hderivative : HasDerivAt (fun rate => potential (path rate))
      (fderiv ℝ potential point (point - minimum)) 1 := by
    apply (hdiff point hpointC).hasFDerivAt.comp_hasDerivAt_of_eq 1 hpathDerivative
    simp [path]
  have hslope : fderiv ℝ potential point (point - minimum) < 0 := by
    linarith
  have hendpoint : potential (path 0) ≤ potential (path 1) := by
    simpa [path] using hmin (hsegment 1 (by norm_num))
  obtain ⟨time, htime, hfirst, hsecond, hmaximum⟩ :=
    Math.exists_interior_maximum_of_endpoint_derivative_neg _ _
      hcontinuousLine hderivative hslope hendpoint
  refine ⟨hgap, point, time, hpoint, hpointMin, hnegative, hreflection,
    htime, ?_, ?_, hmaximum, hsegment⟩
  · simpa [path] using hfirst
  · simpa [path] using hsecond

end GameTheory
