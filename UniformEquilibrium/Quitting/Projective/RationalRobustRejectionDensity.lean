import UniformEquilibrium.Quitting.Root.RationalBoxedEdge
import UniformEquilibrium.Quitting.Root.BoundedEndpoint

/-! # Rational approximate-Nash rejection near a strict exact rejection

Regret is ordinary source-based regret compared with tolerance times the
actual absorption. Successor error is exactly zero. Exact rational Nash is
not asserted; the whole rational source/root pair is produced by density.
-/

noncomputable section

namespace GameTheory

open Set Filter
open scoped Topology

variable {players : ℕ}

/-- Strict inequalities at an exact violating edge survive rational density
in the CLOSED source/root product, including all source and root faces. -/
theorem exists_rational_robust_rejection_of_positive_exact_rejection
    (reward : RationalQuittingReward players) (bound tolerance : ℚ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (htolerance : 0 < tolerance) (potential : Payoff (Fin players) → ℝ)
    (hcontinuous : Continuous potential)
    (source : Payoff (Fin players)) (root : Fin players → PMF Bool)
    (hsource : ∀ who, |source who| ≤ (bound : ℝ))
    (hnash : IsεQuittingRootNash (rationalQuittingRewardToReal reward) source 0 root)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hdrop : potential source - potential
      (quittingRootSuccessorPayoff (rationalQuittingRewardToReal reward) source root) <
        quittingRootAbsorptionMass root) :
    ∃ rationalSource : Fin players → ℚ, ∃ rationalRoot : RationalQuittingRoot players,
      (∀ who, |rationalSource who| ≤ bound) ∧
      (∀ who, |rationalQuittingRootExpectedPayoff reward rationalSource rationalRoot who| ≤
        bound) ∧
      0 < quittingRootAbsorptionMass rationalRoot.toPMF ∧
      (∀ who, quittingRootCoordinateNashDefect (rationalQuittingRewardToReal reward)
        (fun other => (rationalSource other : ℝ)) rationalRoot.toPMF who <
          (tolerance : ℝ) * quittingRootAbsorptionMass rationalRoot.toPMF) ∧
      potential (fun who => (rationalSource who : ℝ)) - potential
        (fun who => (rationalQuittingRootExpectedPayoff reward rationalSource rationalRoot who
          : ℝ)) < quittingRootAbsorptionMass rationalRoot.toPMF := by
  let lower : Fin players → ℚ := fun _ => -bound
  let upper : Fin players → ℚ := fun _ => bound
  let SourceBox := Icc (fun who => (lower who : ℝ)) (fun who => (upper who : ℝ))
  let UnitCube := Icc (0 : Fin players → ℝ) 1
  let point : SourceBox × UnitCube :=
    (⟨source, ⟨fun who => by simpa [lower] using (abs_le.mp (hsource who)).1,
      fun who => (abs_le.mp (hsource who)).2⟩⟩,
      ⟨fun who => (root who true).toReal,
        ⟨fun _ => ENNReal.toReal_nonneg,
          fun who => by
            change (root who true).toReal ≤ (1 : ℝ)
            simpa only [ENNReal.toReal_one] using
              ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one (root who) true)⟩⟩)
  let interpretation : SourceBox × UnitCube →
      Payoff (Fin players) × QuittingRootSimplex (Fin players) :=
    fun pair => (pair.1.1, quittingUnitCubeSimplex pair.2)
  have hinterpretation : Continuous interpretation :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_quittingUnitCubeSimplex.comp continuous_snd)
  let charge := fun pair : SourceBox × UnitCube =>
    quittingRootAbsorptionMass (quittingRootOfSimplex (interpretation pair).2)
  let successor := fun pair : SourceBox × UnitCube =>
    quittingRootSuccessorPayoff (rationalQuittingRewardToReal reward)
      (interpretation pair).1 (quittingRootOfSimplex (interpretation pair).2)
  have hcharge : Continuous charge := continuous_quittingRootAbsorptionMass_simplex.comp
    (continuous_snd.comp hinterpretation)
  have hsuccessor : Continuous successor :=
    (continuous_quittingRootSuccessorPayoff_simplex (rationalQuittingRewardToReal reward)).comp
      hinterpretation
  have hpotentialDrop : Continuous (fun pair => potential pair.1.1 - potential (successor pair)) :=
    (hcontinuous.comp (continuous_subtype_val.comp continuous_fst)).sub
      (hcontinuous.comp hsuccessor)
  have hroot : quittingRootOfSimplex (quittingUnitCubeSimplex point.2) = root :=
    quittingUnitCubeSimplex_eq_actual root
  have hchargePoint : charge point = quittingRootAbsorptionMass root := by
    change quittingRootAbsorptionMass
      (quittingRootOfSimplex (quittingUnitCubeSimplex point.2)) = _
    rw [hroot]
  have hsuccessorPoint : successor point =
      quittingRootSuccessorPayoff (rationalQuittingRewardToReal reward) source root := by
    change quittingRootSuccessorPayoff _ source
      (quittingRootOfSimplex (quittingUnitCubeSimplex point.2)) = _
    rw [hroot]
  have hrelative : ∀ᶠ pair in 𝓝 point, ∀ who,
      quittingRootCoordinateNashDefect (rationalQuittingRewardToReal reward)
        (interpretation pair).1 (quittingRootOfSimplex (interpretation pair).2) who <
          (tolerance : ℝ) * charge pair := by
    apply Filter.eventually_all.mpr
    intro who
    have hdefect :=
      (continuous_quittingRootCoordinateNashDefect_simplex
        (rationalQuittingRewardToReal reward) who).comp hinterpretation
    have hzero := (isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
      (rationalQuittingRewardToReal reward) source root).mp hnash who
    have hstrict : quittingRootCoordinateNashDefect (rationalQuittingRewardToReal reward)
        (interpretation point).1 (quittingRootOfSimplex (interpretation point).2) who <
          (tolerance : ℝ) * charge point := by
      change quittingRootCoordinateNashDefect _ source
        (quittingRootOfSimplex (quittingUnitCubeSimplex point.2)) who < _
      rw [hroot, hzero, hchargePoint]
      exact mul_pos (Rat.cast_pos.mpr htolerance) habsorption
    have hnear := (hdefect.sub (continuous_const.mul hcharge)).continuousAt.eventually
      (gt_mem_nhds (sub_neg.mpr hstrict))
    exact hnear.mono fun _ h => sub_neg.mp h
  have hpositive : ∀ᶠ pair in 𝓝 point, 0 < charge pair :=
    hcharge.continuousAt.eventually (lt_mem_nhds (by rwa [hchargePoint]))
  have hreject : ∀ᶠ pair in 𝓝 point,
      potential pair.1.1 - potential (successor pair) < charge pair := by
    have hnear := (hpotentialDrop.sub hcharge).continuousAt.eventually
      (gt_mem_nhds (show potential point.1.1 - potential (successor point) - charge point < 0 by
        rw [hsuccessorPoint, hchargePoint]; exact sub_neg.mpr hdrop))
    exact hnear.mono fun _ h => sub_neg.mp h
  have hwidth : lower ≤ upper := by
    intro who
    have h := (abs_nonneg (source who)).trans (hsource who)
    change -bound ≤ bound
    have hbound : (0 : ℚ) ≤ bound := Rat.cast_nonneg.mp h
    linarith
  let CastUnitCube := Icc
    (fun who => ((0 : Fin players → ℚ) who : ℝ))
    (fun who => ((1 : Fin players → ℚ) who : ℝ))
  let recast : CastUnitCube → UnitCube := fun candidate =>
    ⟨candidate.1,
      ⟨fun who => by
          simpa only [Pi.zero_apply, Rat.cast_zero] using candidate.2.1 who,
        fun who => by
          simpa only [Pi.one_apply, Rat.cast_one] using candidate.2.2 who⟩⟩
  have hrecastContinuous : Continuous recast :=
    continuous_subtype_val.subtype_mk _
  have hrecastSurjective : Function.Surjective recast := by
    intro candidate
    let preimage : CastUnitCube :=
      ⟨candidate.1,
        ⟨fun who => by
            simpa only [Pi.zero_apply, Rat.cast_zero] using candidate.2.1 who,
          fun who => by
            simpa only [Pi.one_apply, Rat.cast_one] using candidate.2.2 who⟩⟩
    exact ⟨preimage, Subtype.ext rfl⟩
  have hunitDense : DenseRange
      (recast ∘ Math.Interval.rationalClosedBoxCast (0 : Fin players → ℚ) 1) :=
    hrecastSurjective.denseRange.comp
      (Math.Interval.denseRange_rationalClosedBoxCast
        (0 : Fin players → ℚ) 1 (by intro who; norm_num)) hrecastContinuous
  have hdense := (Math.Interval.denseRange_rationalClosedBoxCast lower upper hwidth).prodMap
    hunitDense
  have hgood : ∀ᶠ pair in 𝓝 point,
      0 < charge pair ∧
      (∀ who, quittingRootCoordinateNashDefect (rationalQuittingRewardToReal reward)
        (interpretation pair).1 (quittingRootOfSimplex (interpretation pair).2) who <
          (tolerance : ℝ) * charge pair) ∧
      potential pair.1.1 - potential (successor pair) < charge pair := by
    filter_upwards [hpositive, hrelative, hreject] with pair hp hr hv
    exact ⟨hp, hr, hv⟩
  obtain ⟨selected, hselected⟩ := hdense.mem_nhds
    (s := {pair : SourceBox × UnitCube | 0 < charge pair ∧
      (∀ who, quittingRootCoordinateNashDefect (rationalQuittingRewardToReal reward)
        (interpretation pair).1 (quittingRootOfSimplex (interpretation pair).2) who <
          (tolerance : ℝ) * charge pair) ∧
      potential pair.1.1 - potential (successor pair) < charge pair}) hgood
  let rationalSource := selected.1.1
  let rationalRoot : RationalQuittingRoot players :=
    ⟨selected.2.1, selected.2.2.1, selected.2.2.2⟩
  have hselectedRoot : quittingRootOfSimplex
      (quittingUnitCubeSimplex (recast (Math.Interval.rationalClosedBoxCast 0 1 selected.2))) =
        rationalRoot.toPMF := quittingUnitCubeSimplex_rational_eq rationalRoot
  have hsourceBox : ∀ who, |rationalSource who| ≤ bound :=
    fun who => abs_le.mpr ⟨selected.1.2.1 who, selected.1.2.2 who⟩
  have hsuccessorCast := quittingRootSuccessorPayoff_rational_eq_cast
    reward rationalSource rationalRoot
  have htargetBox : ∀ who,
      |rationalQuittingRootExpectedPayoff reward rationalSource rationalRoot who| ≤ bound := by
    intro who
    have h := abs_quittingRootSuccessorPayoff_le_bound (rationalQuittingRewardToReal reward)
      (fun other => (rationalSource other : ℝ)) rationalRoot.toPMF who
      (B := (bound : ℝ))
      (fun terminal other => by
        change |(reward terminal other : ℝ)| ≤ (bound : ℝ)
        exact_mod_cast hreward terminal other)
      (fun other => by exact_mod_cast hsourceBox other)
    rw [hsuccessorCast] at h
    change |(rationalQuittingRootExpectedPayoff reward rationalSource rationalRoot who : ℝ)| ≤
      (bound : ℝ) at h
    exact_mod_cast h
  have hselectedActual : 0 < quittingRootAbsorptionMass rationalRoot.toPMF ∧
      (∀ who, quittingRootCoordinateNashDefect (rationalQuittingRewardToReal reward)
        (fun other => (rationalSource other : ℝ)) rationalRoot.toPMF who <
          (tolerance : ℝ) * quittingRootAbsorptionMass rationalRoot.toPMF) ∧
      potential (fun who => (rationalSource who : ℝ)) - potential
        (quittingRootSuccessorPayoff (rationalQuittingRewardToReal reward)
          (fun who => (rationalSource who : ℝ)) rationalRoot.toPMF) <
            quittingRootAbsorptionMass rationalRoot.toPMF := by
    simp only [mem_ofPred_eq, charge, successor, interpretation, Prod.map,
      Function.comp_apply] at hselected
    rw [hselectedRoot] at hselected
    exact hselected
  refine ⟨rationalSource, rationalRoot, hsourceBox, htargetBox, hselectedActual.1,
    hselectedActual.2.1, ?_⟩
  simpa only [hsuccessorCast] using hselectedActual.2.2

end GameTheory
