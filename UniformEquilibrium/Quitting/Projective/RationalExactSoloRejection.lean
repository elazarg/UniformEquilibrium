import MathUE.Interval.RationalPolynomialRegularity
import UniformEquilibrium.Quitting.Projective.SingletonBoxStandardQFaceExclusion
import MathUE.Analysis.CollisionAdjustedDrift
import UniformEquilibrium.Quitting.Root.CollisionAdjustedSingletonProbe
import UniformEquilibrium.Quitting.Root.RationalBoxedEdge
import UniformEquilibrium.Quitting.Root.RationalFiniteSourceCapThresholdScan

/-! # Rational exact-Nash one-quitter rejection under actual standard Q

Rational approximation fixes the same closed singleton face, then the
canonical collision-adjusted probe supplies exact Nash at a rational small
rate. This is separate from approximate-Nash robust rejection.
-/

namespace GameTheory

open Set Filter Math.Interval Math.LinearProgramming
open scoped Topology

variable {players : ℕ}

/-- Rational arithmetic version of the EXISTING frozen-upper singleton probe. -/
def rationalQuittingSingletonProbeSource (reward : RationalQuittingReward players)
    (upper : ℚ) (point : Fin players → ℚ) (owner : Fin players) (rate : ℚ) :
    Fin players → ℚ :=
  fun other => point other + rate / (1 - rate) *
    (if other = owner then 0 else if point other < upper then
      max (reward ⟨{owner, other}, by simp⟩ other -
        reward (quittingSingletonTerminal owner) other) 0 else 0)

theorem rationalQuittingSingletonProbeSource_cast
    (reward : RationalQuittingReward players) (upper : ℚ) (point : Fin players → ℚ)
    (owner : Fin players) (rate : ℚ) :
    (fun who => (rationalQuittingSingletonProbeSource reward upper point owner rate who : ℝ)) =
      quittingSingletonProbeSource (rationalQuittingRewardToReal reward) upper
        (fun who => (point who : ℝ)) owner rate := by
  funext who
  by_cases howner : who = owner
  · subst who
    simp [rationalQuittingSingletonProbeSource, quittingSingletonProbeSource,
      quittingSingletonProbeCorrection]
  · by_cases hupper : point who < upper
    · simp [rationalQuittingSingletonProbeSource, quittingSingletonProbeSource,
        quittingSingletonProbeCorrection, quittingSingletonProbeCollision,
        quittingSingletonCollisionReward, quittingSoloReward, rationalQuittingRewardToReal,
        quittingSingletonTerminal, howner, hupper]
    · simp [rationalQuittingSingletonProbeSource, quittingSingletonProbeSource,
        quittingSingletonProbeCorrection, howner, hupper]

noncomputable section

/-- Theorem 4 of the shape packet, with every witness produced internally.
The same rational owner face is retained during approximation. The source
root is EXACT Nash, quits only at its rational owner rate in (0,1), and its
successor is literally the rational exact successor. Endpoints even lie in
the smaller radius bound+1; hence they lie in the packet's bound+2 box. -/
theorem exists_rational_exact_solo_rejection_of_standardQ_quasiconvex
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) (bound : ℚ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hQ : IsStandardQ (quittingProjectiveLCPMatrix (rationalQuittingRewardToReal reward)))
    (expression : RationalPolynomial players)
    (hquasiconvex : QuasiconvexOn ℝ
      (quittingSingletonBox (rationalQuittingRewardToReal reward) (bound : ℝ))
      (fun point => RationalPolynomial.evalReal point expression)) :
    ∃ owner : Fin players, ∃ rate : ℚ, ∃ source : Fin players → ℚ,
      0 < rate ∧ rate < 1 ∧
      (∀ who, |source who| ≤ bound + 2) ∧
      (∀ who, |rationalQuittingRootExpectedPayoff reward source
        (rationalQuittingSoloRoot owner rate) who| ≤ bound + 2) ∧
      IsεQuittingRootNash (rationalQuittingRewardToReal reward)
        (fun who => (source who : ℝ)) 0 (rationalQuittingSoloRoot owner rate).toPMF ∧
      quittingRootAbsorptionMass (rationalQuittingSoloRoot owner rate).toPMF = (rate : ℝ) ∧
      (∀ who, (rationalQuittingSoloRoot owner rate).probability who =
        if who = owner then rate else 0) ∧
      RationalPolynomial.evalReal (fun who => (source who : ℝ)) expression -
        RationalPolynomial.evalReal (fun who =>
          (rationalQuittingRootExpectedPayoff reward source
            (rationalQuittingSoloRoot owner rate) who : ℝ)) expression < 3 * (rate : ℝ) / 4 := by
  let realReward := rationalQuittingRewardToReal reward
  let potential := fun point => RationalPolynomial.evalReal point expression
  have hrewardReal : ∀ terminal who, |realReward terminal who| ≤ (bound : ℝ) := by
    intro terminal who
    change |(reward terminal who : ℝ)| ≤ (bound : ℝ)
    exact_mod_cast hreward terminal who
  have hsmooth := RationalPolynomial.contDiff_evalReal expression 1
  have hdiff : ∀ point ∈ quittingSingletonBox realReward (bound : ℝ),
      DifferentiableAt ℝ potential point := fun point _ => hsmooth.differentiable_one point
  have hfaceViolation : ∃ point ∈ quittingSingletonBox realReward (bound : ℝ), ∃ owner,
      point owner = quittingSoloReward realReward owner owner ∧
        fderiv ℝ potential point (point - quittingSoloReward realReward owner) ≤ 0 := by
    by_contra hnone
    push Not at hnone
    exact not_quasiconvex_singletonBox_of_standardQ_positive_face_drift
      realReward hrewardReal hQ potential hdiff hnone hquasiconvex
  obtain ⟨point, hpoint, owner, howner, hnonpositive⟩ := hfaceViolation
  let lower : Fin players → ℚ := fun who => reward (quittingSingletonTerminal who) who
  let upper : Fin players → ℚ :=
    Function.update (fun _ => bound + 1) owner (lower owner)
  have hwidth : lower ≤ upper := by
    intro who
    by_cases heq : who = owner
    · subst who; simp [upper]
    · have h := (le_abs_self _).trans (hreward (quittingSingletonTerminal who) who)
      simpa [upper, heq] using h.trans (by linarith : bound ≤ bound + 1)
  have hface : point ∈ Icc (fun who => (lower who : ℝ)) (fun who => (upper who : ℝ)) := by
    constructor
    · exact hpoint.1
    · intro who
      by_cases heq : who = owner
      · subst who
        simp only [upper, Function.update_self]
        change point owner ≤ (reward (quittingSingletonTerminal owner) owner : ℝ)
        change point owner = (reward (quittingSingletonTerminal owner) owner : ℝ) at howner
        exact howner.le
      · simpa [upper, heq] using hpoint.2 who
  let boxedPoint : Icc (fun who => (lower who : ℝ)) (fun who => (upper who : ℝ)) :=
    ⟨point, hface⟩
  let drift := fun input => fderiv ℝ potential input (input - quittingSoloReward realReward owner)
  have hdrift : Continuous drift := (hsmooth.continuous_fderiv one_ne_zero).clm_apply
    (continuous_id.sub continuous_const)
  have hnear : ∀ᶠ candidate in 𝓝 boxedPoint, drift candidate.1 < 1 / 2 :=
    (hdrift.comp continuous_subtype_val).continuousAt.eventually
      (gt_mem_nhds (lt_of_le_of_lt hnonpositive (by norm_num)))
  obtain ⟨rationalPoint, hrationalDrift⟩ :=
    (Math.Interval.denseRange_rationalClosedBoxCast lower upper hwidth).mem_nhds hnear
  let rationalFace := rationalPoint.1
  let face := fun who => (rationalFace who : ℝ)
  have hupper : ∀ who, upper who ≤ bound + 1 := by
    intro who
    by_cases heq : who = owner
    · subst who
      simpa [upper, lower] using
        ((le_abs_self _).trans (hreward (quittingSingletonTerminal owner) owner)).trans
          (by linarith : bound ≤ bound + 1)
    · simp [upper, heq]
  have hfaceCoordinates : ∀ who,
      quittingSoloReward realReward who who ≤ face who ∧ face who ≤ (bound : ℝ) + 1 := by
    intro who
    constructor
    · change (reward (quittingSingletonTerminal who) who : ℝ) ≤ (rationalPoint.1 who : ℝ)
      have h : reward (quittingSingletonTerminal who) who ≤ rationalPoint.1 who :=
        rationalPoint.2.1 who
      exact_mod_cast h
    · change (rationalPoint.1 who : ℝ) ≤ (bound : ℝ) + 1
      have h : rationalPoint.1 who ≤ bound + 1 :=
        (rationalPoint.2.2 who).trans (hupper who)
      exact_mod_cast h
  have hfaceOwner : face owner = quittingSoloReward realReward owner owner := by
    apply le_antisymm
    · change (rationalPoint.1 owner : ℝ) ≤
        (reward (quittingSingletonTerminal owner) owner : ℝ)
      have h : rationalPoint.1 owner ≤ lower owner := by
        simpa only [upper, Function.update_self] using rationalPoint.2.2 owner
      change rationalPoint.1 owner ≤ reward (quittingSingletonTerminal owner) owner at h
      exact_mod_cast h
    · exact (hfaceCoordinates owner).1
  have hfaceC : face ∈ quittingSingletonBox realReward (bound : ℝ) :=
    ⟨fun who => (hfaceCoordinates who).1, fun who => (hfaceCoordinates who).2⟩
  have hsmallDrift : fderiv ℝ potential face (face - quittingSoloReward realReward owner) <
      1 / 2 := hrationalDrift
  obtain ⟨probeRadius, hprobeOne, hprobePositive, hprobe⟩ :=
    exists_small_rates_quittingSingletonProbe realReward hrewardReal
      (by linarith : (bound : ℝ) < (bound : ℝ) + 1)
      face owner hfaceCoordinates hfaceOwner
  let correction := quittingSingletonProbeCorrection realReward ((bound : ℝ) + 1) face owner
  have hlimit := Math.tendsto_collisionAdjusted_potential_differenceQuotient potential
    (fderiv ℝ potential face) face correction (quittingSoloReward realReward owner)
      (hdiff face hfaceC).hasFDerivAt
  have hquotient : ∀ᶠ rate : ℝ in 𝓝[>] 0,
      (potential (face + (rate / (1 - rate)) • correction) -
        potential (face + rate • (correction + quittingSoloReward realReward owner - face))) /
          rate < 3 / 4 := hlimit.eventually (gt_mem_nhds (by linarith :
      fderiv ℝ potential face (face - quittingSoloReward realReward owner) < 3 / 4))
  obtain ⟨quotientRadius, hquotientRadius, hquotientBall⟩ :=
    Metric.mem_nhdsWithin_iff.mp hquotient
  obtain ⟨rate, hratePositive, hrateSmall⟩ :=
    exists_rat_btwn (lt_min hprobePositive hquotientRadius)
  have hsmall : (rate : ℝ) < probeRadius := hrateSmall.trans_le (min_le_left _ _)
  have hrateOne : (rate : ℝ) < 1 := hsmall.trans hprobeOne
  have hrateOneRat : rate < (1 : ℚ) := by exact_mod_cast hrateOne
  have hrateRational : rate ∈ Icc (0 : ℚ) 1 :=
    ⟨(Rat.cast_pos.mp hratePositive).le, hrateOneRat.le⟩
  have hrateBall : (rate : ℝ) ∈ Metric.ball (0 : ℝ) quotientRadius := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hratePositive]
    exact hrateSmall.trans_le (min_le_right _ _)
  have hchosenQuotient := hquotientBall ⟨hrateBall, hratePositive⟩
  change (potential (face + ((rate : ℝ) / (1 - (rate : ℝ))) • correction) -
    potential (face + (rate : ℝ) • (correction + quittingSoloReward realReward owner - face))) /
      (rate : ℝ) < 3 / 4 at hchosenQuotient
  obtain ⟨hsourceBox, hnash, htargetBox, habsorption⟩ := hprobe rate hratePositive hsmall
  let source := rationalQuittingSingletonProbeSource reward (bound + 1) rationalFace owner rate
  let root := rationalQuittingSoloRoot owner rate
  have hsourceCast : (fun who => (source who : ℝ)) =
      quittingSingletonProbeSource realReward ((bound : ℝ) + 1) face owner rate := by
    simpa [source, face, Rat.cast_add, Rat.cast_one] using
      rationalQuittingSingletonProbeSource_cast reward (bound + 1) rationalFace owner rate
  have hroot : root.toPMF =
      quittingSingletonProbeRoot owner rate hratePositive.le hrateOne.le :=
    rationalQuittingSoloRoot_toPMF_eq owner hrateRational
  have hsourceFormula : quittingSingletonProbeSource realReward ((bound : ℝ) + 1)
      face owner rate = face + ((rate : ℝ) / (1 - rate)) • correction := by ext who; rfl
  have htargetFormula : quittingSingletonProbeSuccessor realReward ((bound : ℝ) + 1)
      face owner rate hratePositive.le hrateOne.le =
        face + (rate : ℝ) • (correction + quittingSoloReward realReward owner - face) := by
    ext who
    exact quittingSingletonProbeSuccessor_eq_affine realReward ((bound : ℝ) + 1) face owner
      rate hratePositive.le hrateOne.le (ne_of_lt hrateOne) who
  rw [← hsourceFormula, ← htargetFormula] at hchosenQuotient
  have hdrop := (div_lt_iff₀ hratePositive).mp hchosenQuotient
  have hsuccessorCast := quittingRootSuccessorPayoff_rational_eq_cast reward source root
  have hcanonicalTarget : quittingSingletonProbeSuccessor realReward ((bound : ℝ) + 1)
      face owner rate hratePositive.le hrateOne.le =
        fun who => (rationalQuittingRootExpectedPayoff reward source root who : ℝ) := by
    rw [quittingSingletonProbeSuccessor, ← hsourceCast, ← hroot]
    exact hsuccessorCast
  rw [← hsourceCast, hcanonicalTarget] at hdrop
  refine ⟨owner, rate, source, Rat.cast_pos.mp hratePositive, hrateOneRat,
    ?_, ?_, ?_, ?_, rationalQuittingSoloRoot_probability_of_mem_Icc owner hrateRational, ?_⟩
  · intro who
    have h := hsourceBox who
    rw [← hsourceCast] at h
    have h' : |(source who : ℝ)| ≤ (bound : ℝ) + 2 := h.trans (by linarith)
    exact_mod_cast h'
  · intro who
    have h := htargetBox who
    rw [hcanonicalTarget] at h
    have h' : |(rationalQuittingRootExpectedPayoff reward source root who : ℝ)| ≤
        (bound : ℝ) + 2 := h.trans (by linarith)
    exact_mod_cast h'
  · rw [hsourceCast, hroot]
    exact hnash
  · rw [hroot]
    exact habsorption
  · change potential (fun who => (source who : ℝ)) - potential
      (fun who => (rationalQuittingRootExpectedPayoff reward source root who : ℝ)) < _
    linarith

end

end GameTheory
