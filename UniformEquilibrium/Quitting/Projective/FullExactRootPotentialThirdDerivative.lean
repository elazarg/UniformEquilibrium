import MathUE.Analysis.MidpointThirdDerivative
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialReflection

/-! # Quantitative directional third derivative at every potential minimum

The point is on the entire reflected segment and need not lie above the
singleton vector. The direction is produced by adaptive radial reversal.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- C³ regularity on an open neighborhood of the full box upgrades each
global minimum's radial reversal to a directional third derivative ≥ 3δ.
The conclusion states the actual multilinear derivative, not a mixed partial. -/
theorem IsQuittingFullExactRootPotential.directionalThirdDerivative
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ quittingSoloReward reward who who)
    {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward 3 potential)
    (domain : Set (Payoff ι)) (hopen : IsOpen domain)
    (hbox : Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3) ⊆ domain)
    (hregular : ContDiffOn ℝ 3 potential domain)
    (minimum : Payoff ι) (hminimum : ∀ who, |minimum who| ≤ 3)
    (hmin : IsMinOn potential (Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3)) minimum) :
    let gap := Finset.univ.inf' Finset.univ_nonempty
      (fun who => minimum who - quittingSoloReward reward who who)
    0 < gap ∧ ∃ point time,
      point ∈ Math.lowerBoxBoundary (fun who => quittingSoloReward reward who who)
        (fun who => max (minimum who) 1) ∧
      IsMinOn potential (Math.lowerBoxBoundary (fun who => quittingSoloReward reward who who)
        (fun who => max (minimum who) 1)) point ∧
      time ∈ Set.Ioo (0 : ℝ) 2 ∧
      fderiv ℝ potential point (point - minimum) ≤ -gap / 2 ∧
      2 • point - minimum ∈ Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3) ∧
      3 * gap ≤ iteratedFDeriv ℝ 3 potential (minimum + time • (point - minimum))
        (fun _ => point - minimum) ∧
      (∀ rate ∈ Set.Icc (0 : ℝ) 2, minimum + rate • (point - minimum) ∈
        Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3)) ∧
      ∃ peak ∈ Set.Ioo (0 : ℝ) 1,
        potential minimum < potential (minimum + peak • (point - minimum)) ∧
        potential point < potential (minimum + peak • (point - minimum)) ∧
        IsMaxOn (fun rate => potential (minimum + rate • (point - minimum)))
          (Set.Icc (0 : ℝ) 1) peak := by
  have hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => 3), DifferentiableAt ℝ potential point := by
    intro point hpoint
    have hpointBox : point ∈ Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3) :=
      ⟨fun who => (by norm_num : (-3 : ℝ) ≤ 0).trans
        ((hsingleton who).trans (hpoint.1 who)), hpoint.2⟩
    exact (hregular.contDiffAt (hopen.mem_nhds (hbox hpointBox))).differentiableAt
      (by norm_num)
  obtain ⟨hgap, point, hpoint, hpointMin, hnegative, hreflection, hsegment⟩ :=
    hpotential.radialReversal hreward hsingleton hdiff minimum hminimum hmin
  let direction : Payoff ι := point - minimum
  let path : ℝ → Payoff ι := fun rate => minimum + rate • direction
  have hpathRegular : ContDiff ℝ 3 path :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hlineRegular : ∀ time ∈ Set.Icc (0 : ℝ) 2,
      ContDiffAt ℝ 3 (fun rate => potential (path rate)) time := by
    intro time htime
    exact (hregular.contDiffAt (hopen.mem_nhds (hbox (hsegment time htime)))).comp
      time hpathRegular.contDiffAt
  have hpointC : point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => 3) := by
    refine ⟨hpoint.1.1, fun who => ?_⟩
    exact (hpoint.1.2 who).trans
      (max_le ((le_abs_self _).trans (hminimum who)) (by norm_num))
  have hpathDerivative : HasDerivAt path direction 1 := by
    simpa [path] using ((hasDerivAt_id (1 : ℝ)).smul_const direction).const_add minimum
  have hlineDerivative : HasDerivAt (fun rate => potential (path rate))
      (fderiv ℝ potential point direction) 1 := by
    apply (hdiff point hpointC).hasFDerivAt.comp_hasDerivAt_of_eq 1 hpathDerivative
    simp [path, direction]
  have hslope : deriv (fun rate => potential (path rate)) 1 ≤
      -(Finset.univ.inf' Finset.univ_nonempty
        (fun who => minimum who - quittingSoloReward reward who who)) / 2 := by
    rw [hlineDerivative.deriv]
    exact hnegative
  have hendpoints : potential (path 0) ≤ potential (path 2) := by
    simpa [path] using hmin (hsegment 2 (by norm_num))
  obtain ⟨time, htime, hthird⟩ := Math.exists_thirdDerivative_ge_three_gap _ _
    hlineRegular hendpoints hslope
  rw [Math.thirdDerivative_affineLine_eq potential domain hopen hregular minimum direction
    time (hbox (hsegment time ⟨htime.1.le, htime.2.le⟩))] at hthird
  have hcontinuousLine : ContinuousOn (fun rate => potential (path rate))
      (Set.Icc (0 : ℝ) 1) := by
    intro rate hrate
    have hregularAt := hlineRegular rate ⟨hrate.1, hrate.2.trans (by norm_num)⟩
    exact hregularAt.continuousAt.continuousWithinAt
  have hnegativeSlope : fderiv ℝ potential point direction < 0 := by
    change fderiv ℝ potential point (point - minimum) < 0
    linarith
  have hfirstEndpoints : potential (path 0) ≤ potential (path 1) := by
    simpa [path, direction] using hmin (hsegment 1 (by norm_num))
  obtain ⟨peak, hpeak, hfirst, hsecond, hmaximum⟩ :=
    Math.exists_interior_maximum_of_endpoint_derivative_neg _ _
      hcontinuousLine hlineDerivative hnegativeSlope hfirstEndpoints
  refine ⟨hgap, point, time, hpoint, hpointMin, htime, hnegative, hreflection,
    hthird, hsegment, peak, hpeak, ?_, ?_, hmaximum⟩
  · simpa [path, direction] using hfirst
  · simpa [path, direction] using hsecond

end GameTheory
