import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalMixedMarginal
import MathUE.PMFProduct.Update

/-!
# Outsider and quiet marginals of the independent source coupling

The same child/outsider sample used for the private mixed response also
realizes the actual parent outsider stopping-law product. This prevents a
gain comparison from silently replacing the played independent profile.
-/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- With a fixed outsider deadline, adjoining it to an independent child
tuple gives the parent product law with that outsider coordinate pinned. -/
theorem map_pmfPi_child_outsideDeadline
    (childLaws : ι → PMF (Option ℕ)) (deadline : Option ℕ) :
    (pmfPi childLaws).map (fun times => outsideDeadlineClocks times deadline) =
      pmfPi (Function.update (quietParentStoppingLaws childLaws) none
        (PMF.pure deadline)) := by
  let quiet := quietParentStoppingLaws childLaws
  calc
    _ = ((pmfPi childLaws).map quietParentClocks).map
          (fun clocks => Function.update clocks none deadline) := by
      rw [PMF.map_comp]
      congr 1
      funext times player
      cases player with
      | none => rfl
      | some i => rfl
    _ = (pmfPi quiet).map
          (fun clocks => Function.update clocks none deadline) := by
      rw [map_pmfPi_child_quiet]
    _ = _ := by
      rw [← PMF.bind_pure_comp]
      exact pmfPi_bind_update_pure quiet none deadline

omit [Nonempty ι] in
/-- The source coupling's outsider-clock tuple is exactly the independent
parent stopping-law product, with no correlated profile introduced. -/
theorem map_cappedClockIndependentSample_outside
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    (cappedClockIndependentSample childLaws outsideLaw).map
        (fun sample => outsideDeadlineClocks sample.1 sample.2) =
      pmfPi (cappedClockParentSourceLaws childLaws outsideLaw) := by
  let quiet := quietParentStoppingLaws childLaws
  have hsource : cappedClockParentSourceLaws childLaws outsideLaw =
      Function.update quiet none outsideLaw := by
    funext player
    cases player <;> simp [quiet, cappedClockParentSourceLaws,
      quietParentStoppingLaws]
  calc
    _ = (pmfPi childLaws).bind (fun times =>
          outsideLaw.bind fun deadline =>
            PMF.pure (outsideDeadlineClocks times deadline)) := by
      unfold cappedClockIndependentSample
      rw [PMF.map_bind]
      apply congrArg (PMF.bind (pmfPi childLaws))
      funext times
      rw [PMF.map_comp]
      change outsideLaw.map
        (fun deadline => outsideDeadlineClocks times deadline) = _
      exact (PMF.bind_pure_comp
        (fun deadline => outsideDeadlineClocks times deadline) outsideLaw).symm
    _ = outsideLaw.bind (fun deadline =>
          (pmfPi childLaws).map fun times =>
            outsideDeadlineClocks times deadline) := by
      rw [PMF.bind_comm]
      apply congrArg (PMF.bind outsideLaw)
      funext deadline
      exact PMF.bind_pure_comp _ _
    _ = outsideLaw.bind (fun deadline =>
          pmfPi (Function.update quiet none (PMF.pure deadline))) := by
      apply congrArg (PMF.bind outsideLaw)
      funext deadline
      exact map_pmfPi_child_outsideDeadline childLaws deadline
    _ = _ := by
      rw [hsource, pmfPi_update_bind]

/-- The coupled outsider payoff is the actual evaluated payoff for the
independent outsider stopping law. -/
theorem expect_cappedClockIndependentSample_outside_eq_stoppingLaw
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    expect (cappedClockIndependentSample childLaws outsideLaw)
      (fun sample => quittingPureClockEvaluatedPayoff reward evaluation
        (outsideDeadlineClocks sample.1 sample.2) none) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (cappedClockParentSourceLaws childLaws outsideLaw) none := by
  rw [quittingStoppingLawEvaluatedPayoff]
  rw [← map_cappedClockIndependentSample_outside childLaws outsideLaw,
    expect_map]

end GameTheory
