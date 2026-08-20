/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.AnalyticOccupationFlowNormalization

/-!
# Analytic occupation-flow alternative

The capstone theorem delegates certificate stabilization, primal and dual
decoding, affine normalization, and branch incompatibility to named lemmas.
-/

noncomputable section

namespace Math.Probability

open Filter Set

variable {S I : Type*}

/-- Along an analytic zero-sum occupation-column germ, exactly one stable
actual-parameter branch occurs: an analytic nonnegative circulation using
the distinguished column, or an analytic bounded potential that charges
that column by a positive power law while having nonnegative drift on all
other columns. -/
theorem analyticPositiveCirculation_xor_boundedSeparator
    [Fintype S] [Fintype I]
    (column : ℝ → I → S → ℝ) (i₀ : I)
    (hanalytic : ∀ i destination,
      AnalyticAt ℝ (fun t ↦ column t i destination) 0)
    (hzeroSum : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ i, ∑ destination, column t i destination = 0) :
    Xor (Nonempty (AnalyticPositiveCirculation column i₀))
      (Nonempty (AnalyticBoundedOccupationSeparator column i₀)) := by
  classical
  rcases analyticOccupationCertificate_eventually_stabilizes
      column i₀ hanalytic with hcirculation | hnoCirculation
  · have hpositive := analyticPositiveCirculation_of_eventually_certificate
      column i₀ hanalytic hcirculation
    refine Or.inl ⟨hpositive, ?_⟩
    rintro ⟨separator⟩
    exact analyticPositiveCirculation_incompatible_boundedSeparator
      hpositive.some separator
  · have hseparatorFeasible :=
      eventually_separatorCertificate_of_no_occupationCertificate
        column i₀ hnoCirculation
    have hseparator :=
      analyticBoundedOccupationSeparator_of_eventually_certificate
        column i₀ hanalytic hzeroSum hseparatorFeasible
    refine Or.inr ⟨hseparator, ?_⟩
    rintro ⟨positive⟩
    rcases (hnoCirculation.and positive.eventually_certificate).exists with
      ⟨_, hno, hyes⟩
    exact hno hyes

end Math.Probability
