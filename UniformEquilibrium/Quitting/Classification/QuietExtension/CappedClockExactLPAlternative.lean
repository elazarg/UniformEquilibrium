import MathUE.DirectedTransport.FiniteInequality.Nonnegative
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPointwiseDomination

/-!
# Exact finite LP alternative for capped-clock reward certificates

The Never, future, and joining reward rows are encoded as one finite linear
system with nonnegative player weights. The generic finite-inequality
alternative gives a nonnegative dual certificate with
nonpositive weighted columns.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The three kinds of reward row in the exact capped-clock criterion. -/
inductive CappedClockExactLPRow (ι : Type)
  | never
  | future (coalition : {A : Finset ι // A.Nonempty})
  | joining (coalition : {A : Finset ι // A.Nonempty})
  deriving DecidableEq, Fintype

/-- The child-weight coefficient in a capped-clock reward row. -/
def cappedClockExactLPDelta
    {K : Type} [Sub K]
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → K) :
    CappedClockExactLPRow ι → ι → K
  | .never, who =>
      reward ⟨{some who}, Finset.singleton_nonempty (some who)⟩ (some who)
  | .future coalition, who =>
      reward ⟨{some who}, Finset.singleton_nonempty (some who)⟩ (some who) -
        reward ⟨cappedClockChildCoalition coalition,
          cappedClockChildCoalition_nonempty coalition.property⟩ (some who)
  | .joining coalition, who =>
      reward ⟨cappedClockChildCoalition (insert who coalition),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty who coalition)⟩
          (some who) -
        reward ⟨cappedClockChildCoalition coalition,
          cappedClockChildCoalition_nonempty coalition.property⟩ (some who)

/-- The outsider lower bound in a capped-clock reward row. -/
def cappedClockExactLPBase
    {K : Type} [Sub K]
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → K) :
    CappedClockExactLPRow ι → K
  | .never => reward ⟨{none}, Finset.singleton_nonempty none⟩ none
  | .future coalition =>
      reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition coalition,
          cappedClockChildCoalition_nonempty coalition.property⟩ none
  | .joining coalition =>
      reward ⟨cappedClockJoinedCoalition coalition,
          cappedClockJoinedCoalition_nonempty (coalition : Finset ι)⟩ none -
        reward ⟨cappedClockChildCoalition coalition,
          cappedClockChildCoalition_nonempty coalition.property⟩ none

/-- The structure-valued reward certificate is exactly feasibility of its
finite row system by nonnegative child weights. -/
theorem nonempty_cappedClockParentRewardCertificate_iff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) :
    Nonempty (CappedClockParentRewardCertificate reward) ↔
      ∃ weight : ι → ℝ,
        (∀ who, 0 ≤ weight who) ∧
        ∀ row, cappedClockExactLPBase reward row ≤
          dotProduct (cappedClockExactLPDelta reward row) weight := by
  constructor
  · rintro ⟨certificate⟩
    refine ⟨certificate.weight, certificate.weight_nonneg, ?_⟩
    intro row
    cases row with
    | never =>
        simpa [cappedClockExactLPBase, cappedClockExactLPDelta, dotProduct, mul_comm] using
          certificate.never_row
    | future coalition =>
        simpa [cappedClockExactLPBase, cappedClockExactLPDelta, dotProduct, mul_comm] using
          certificate.future_row coalition coalition.property
    | joining coalition =>
        simpa [cappedClockExactLPBase, cappedClockExactLPDelta, dotProduct, mul_comm] using
          certificate.join_row coalition coalition.property
  · rintro ⟨weight, hnonnegative, hrow⟩
    refine ⟨{
      weight := weight
      weight_nonneg := hnonnegative
      never_row := ?_
      future_row := ?_
      join_row := ?_
    }⟩
    · simpa [cappedClockExactLPBase, cappedClockExactLPDelta, dotProduct, mul_comm] using
        hrow CappedClockExactLPRow.never
    · intro coalition hcoalition
      simpa [cappedClockExactLPBase, cappedClockExactLPDelta, dotProduct, mul_comm] using
        hrow (CappedClockExactLPRow.future ⟨coalition, hcoalition⟩)
    · intro coalition hcoalition
      simpa [cappedClockExactLPBase, cappedClockExactLPDelta, dotProduct, mul_comm] using
        hrow (CappedClockExactLPRow.joining ⟨coalition, hcoalition⟩)

/-- Either the displayed parent table has actual capped-clock weights, or a
finite nonnegative dual combination proves that no such weights exist. -/
theorem exists_cappedClockParentRewardCertificate_or_exactLPDual
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) :
    Nonempty (CappedClockParentRewardCertificate reward) ∨
      ∃ coefficient : CappedClockExactLPRow ι → ℝ,
        (∀ row, 0 ≤ coefficient row) ∧
        (∀ who, ∑ row, coefficient row * cappedClockExactLPDelta reward row who ≤ 0) ∧
        0 < ∑ row, coefficient row * cappedClockExactLPBase reward row := by
  rcases Math.FiniteInequality.exists_nonnegativePotential_or_nonpositiveCertificate
      (cappedClockExactLPDelta reward) (cappedClockExactLPBase reward) with
    hcertificate | hdual
  · exact Or.inl
      ((nonempty_cappedClockParentRewardCertificate_iff reward).mpr hcertificate)
  · exact Or.inr hdual

/-- The capped-clock weights fail to exist exactly when a finite
nonnegative dual has nonpositive columns and strictly positive objective. -/
theorem not_nonempty_cappedClockParentRewardCertificate_iff_exactLPDual
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) :
    ¬Nonempty (CappedClockParentRewardCertificate reward) ↔
      ∃ coefficient : CappedClockExactLPRow ι → ℝ,
        (∀ row, 0 ≤ coefficient row) ∧
        (∀ who, ∑ row, coefficient row * cappedClockExactLPDelta reward row who ≤ 0) ∧
        0 < ∑ row, coefficient row * cappedClockExactLPBase reward row := by
  rw [nonempty_cappedClockParentRewardCertificate_iff]
  exact Math.FiniteInequality.not_exists_nonnegativePotential_iff_exists_nonpositiveCertificate
    (cappedClockExactLPDelta reward) (cappedClockExactLPBase reward)

/-- Rational capped-clock rows have either exact nonnegative rational weights
or an exact nonnegative rational dual certificate. -/
theorem exists_rationalCappedClockWeight_or_exactLPDual
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℚ) :
    (∃ weight : ι → ℚ,
      (∀ who, 0 ≤ weight who) ∧
      ∀ row, cappedClockExactLPBase reward row ≤
        Math.FiniteInequality.ratDotProduct
          (cappedClockExactLPDelta reward row) weight) ∨
    (∃ coefficient : CappedClockExactLPRow ι → ℚ,
      (∀ row, 0 ≤ coefficient row) ∧
      (∀ who, ∑ row, coefficient row * cappedClockExactLPDelta reward row who ≤ 0) ∧
      0 < ∑ row, coefficient row * cappedClockExactLPBase reward row) :=
  Math.FiniteInequality.exists_rationalNonnegativePotential_or_nonpositiveCertificate
    (cappedClockExactLPDelta reward) (cappedClockExactLPBase reward)

/-- Rational capped-clock weights fail to exist exactly when an exact
rational dual certificate exists. -/
theorem not_exists_rationalCappedClockWeight_iff_exactLPDual
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℚ) :
    (¬∃ weight : ι → ℚ,
      (∀ who, 0 ≤ weight who) ∧
      ∀ row, cappedClockExactLPBase reward row ≤
        Math.FiniteInequality.ratDotProduct
          (cappedClockExactLPDelta reward row) weight) ↔
    ∃ coefficient : CappedClockExactLPRow ι → ℚ,
      (∀ row, 0 ≤ coefficient row) ∧
      (∀ who, ∑ row, coefficient row * cappedClockExactLPDelta reward row who ≤ 0) ∧
      0 < ∑ row, coefficient row * cappedClockExactLPBase reward row :=
  Math.FiniteInequality.not_exists_rationalNonnegativePotential_iff_exists_nonpositiveCertificate
    (cappedClockExactLPDelta reward) (cappedClockExactLPBase reward)

end GameTheory

end
