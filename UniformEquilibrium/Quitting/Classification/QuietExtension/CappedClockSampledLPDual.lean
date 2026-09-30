import MathUE.DirectedTransport.FiniteInequality.Perturbation
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockExactLPAlternative
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPositiveSingletonQuietExtension
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockMultipleOutsiderRestriction

/-!
# Sampled literal capped-clock LP duals and reward perturbations

A finite list of actual Never/future/join rows can witness failure of the
universal raw certificate. Lists omitting Never also exclude the relaxed
future/join certificate. Nonnegative dual weights and entrywise reward
perturbations are passed to the existing exact finite LP alternative.
-/

noncomputable section

namespace GameTheory

open Maths.FiniteInequality
open scoped BigOperators

variable {ι Row : Type} [Fintype ι] [DecidableEq ι] [Fintype Row]

/-- An F/J certificate satisfies every actual row other than Never. -/
theorem CappedClockParentFutureJoinCertificate.exactLPRow_le
    {reward : {A : Finset (Option ι) // A.Nonempty} → Payoff (Option ι)}
    (certificate : CappedClockParentFutureJoinCertificate reward)
    (row : CappedClockExactLPRow ι) (hne : row ≠ .never) :
    cappedClockExactLPBase reward row ≤
      dotProduct (cappedClockExactLPDelta reward row) certificate.weight := by
  cases row with
  | never => exact (hne rfl).elim
  | future coalition =>
      simpa [cappedClockExactLPBase, cappedClockExactLPDelta, dotProduct, mul_comm] using
        certificate.future_row coalition coalition.property
  | joining coalition =>
      simpa [cappedClockExactLPBase, cappedClockExactLPDelta, dotProduct, mul_comm] using
        certificate.join_row coalition coalition.property

/-- A finite sampled dual excludes the full actual raw reward certificate. -/
theorem not_nonempty_cappedClockParentRewardCertificate_of_sampledDual
    (reward : {A : Finset (Option ι) // A.Nonempty} → Payoff (Option ι))
    (sample : Row → CappedClockExactLPRow ι) (coefficient : Row → ℝ)
    (hcoefficient : ∀ row, 0 ≤ coefficient row)
    (hcolumns : ∀ who,
      ∑ row, coefficient row * cappedClockExactLPDelta reward (sample row) who ≤ 0)
    (hobjective : 0 < ∑ row, coefficient row * cappedClockExactLPBase reward (sample row)) :
    ¬Nonempty (CappedClockParentRewardCertificate reward) := by
  have hno := (not_exists_nonnegativePotential_iff_exists_nonpositiveCertificate
      (fun row => cappedClockExactLPDelta reward (sample row))
      (fun row => cappedClockExactLPBase reward (sample row))).mpr
        ⟨coefficient, hcoefficient, hcolumns, hobjective⟩
  intro hcertificate
  obtain ⟨weight, hnonnegative, hrow⟩ :=
    (nonempty_cappedClockParentRewardCertificate_iff reward).mp hcertificate
  exact hno ⟨weight, hnonnegative, fun row => hrow (sample row)⟩

/-- Omitting Never in the same sampled dual excludes even the relaxed F/J criterion. -/
theorem not_nonempty_cappedClockParentFutureJoinCertificate_of_sampledDual
    (reward : {A : Finset (Option ι) // A.Nonempty} → Payoff (Option ι))
    (sample : Row → CappedClockExactLPRow ι) (hnever : ∀ row, sample row ≠ .never)
    (coefficient : Row → ℝ) (hcoefficient : ∀ row, 0 ≤ coefficient row)
    (hcolumns : ∀ who,
      ∑ row, coefficient row * cappedClockExactLPDelta reward (sample row) who ≤ 0)
    (hobjective : 0 < ∑ row, coefficient row * cappedClockExactLPBase reward (sample row)) :
    ¬Nonempty (CappedClockParentFutureJoinCertificate reward) := by
  have hno := (not_exists_nonnegativePotential_iff_exists_nonpositiveCertificate
      (fun row => cappedClockExactLPDelta reward (sample row))
      (fun row => cappedClockExactLPBase reward (sample row))).mpr
        ⟨coefficient, hcoefficient, hcolumns, hobjective⟩
  rintro ⟨certificate⟩
  exact hno ⟨certificate.weight, certificate.weight_nonneg,
    fun row => certificate.exactLPRow_le (sample row) (hnever row)⟩

omit [Fintype ι] in
/-- Every N/F/J column coefficient changes by at most twice the raw coordinate error. -/
theorem abs_cappedClockExactLPDelta_sub_le
    (reward other : {A : Finset (Option ι) // A.Nonempty} → Payoff (Option ι))
    (error : ℝ) (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (row : CappedClockExactLPRow ι) (who : ι) :
    |cappedClockExactLPDelta other row who - cappedClockExactLPDelta reward row who| ≤
      2 * error := by
  cases row with
  | never =>
      have h := hclose ⟨{some who}, Finset.singleton_nonempty (some who)⟩ (some who)
      have hnonnegative := (abs_nonneg _).trans h
      exact h.trans (by linarith)
  | future coalition =>
      exact Maths.FiniteInequality.abs_sub_differences_le _ _ _ _ error
        (hclose _ _) (hclose _ _)
  | joining coalition =>
      exact Maths.FiniteInequality.abs_sub_differences_le _ _ _ _ error
        (hclose _ _) (hclose _ _)

omit [Fintype ι] in
/-- Every N/F/J objective coefficient has the same raw error bound. -/
theorem abs_cappedClockExactLPBase_sub_le
    (reward other : {A : Finset (Option ι) // A.Nonempty} → Payoff (Option ι))
    (error : ℝ) (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (row : CappedClockExactLPRow ι) :
    |cappedClockExactLPBase other row - cappedClockExactLPBase reward row| ≤ 2 * error := by
  cases row with
  | never =>
      have h := hclose ⟨{none}, Finset.singleton_nonempty none⟩ none
      have hnonnegative := (abs_nonneg _).trans h
      exact h.trans (by linarith)
  | future coalition =>
      exact Maths.FiniteInequality.abs_sub_differences_le _ _ _ _ error
        (hclose _ _) (hclose _ _)
  | joining coalition =>
      exact Maths.FiniteInequality.abs_sub_differences_le _ _ _ _ error
        (hclose _ _) (hclose _ _)

/-- The actual original-player embedding of the canonical one-outsider display. -/
def quittingChildWithOutsiderOriginalEmbedding
    (deleted : ι → Prop) [DecidablePred deleted] (outside : {who : ι // deleted who}) :
    Option (QuittingChildPlayer deleted) ↪ ι :=
  (quittingChildWithOutsiderEquiv deleted outside).symm.toEmbedding.trans
    (Function.Embedding.subtype (p := fun who => ¬ (deleted who ∧ who ≠ outside.1)))

omit [Fintype ι] in
@[simp] theorem quittingChildWithOutsiderOriginalEmbedding_none
    (deleted : ι → Prop) [DecidablePred deleted] (outside : {who : ι // deleted who}) :
    quittingChildWithOutsiderOriginalEmbedding deleted outside none = outside.1 := rfl

omit [Fintype ι] in
@[simp] theorem quittingChildWithOutsiderOriginalEmbedding_some
    (deleted : ι → Prop) [DecidablePred deleted] (outside : {who : ι // deleted who})
    (who : QuittingChildPlayer deleted) :
    quittingChildWithOutsiderOriginalEmbedding deleted outside (some who) = who.1 := rfl

omit [Fintype ι] in
/-- The canonical display evaluates the literal original reward at the embedded coalition. -/
theorem quittingChildWithOutsiderReward_apply_original
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted] (outside : {who : ι // deleted who})
    (terminal : {A : Finset (Option (QuittingChildPlayer deleted)) // A.Nonempty})
    (who : Option (QuittingChildPlayer deleted)) :
    quittingChildWithOutsiderReward reward deleted outside terminal who =
      reward ⟨terminal.1.map (quittingChildWithOutsiderOriginalEmbedding deleted outside),
        Finset.map_nonempty.mpr terminal.2⟩
        (quittingChildWithOutsiderOriginalEmbedding deleted outside who) := by
  unfold quittingChildWithOutsiderReward quittingRewardReindex quittingDeleteReward
  unfold quittingExtendDeletedCoalition
  congr 1
  apply Subtype.ext
  change (((quittingCoalitionEquiv (quittingChildWithOutsiderEquiv deleted outside)).symm
    terminal).1.map
      (Function.Embedding.subtype (p := fun who => ¬ (deleted who ∧ who ≠ outside.1)))) =
    terminal.1.map (quittingChildWithOutsiderOriginalEmbedding deleted outside)
  rw [quittingCoalitionEquiv_symm_coe, Finset.map_map]
  rfl

omit [Fintype ι] in
/-- The canonical deletion/reindex adapter retains a raw reward-coordinate bound. -/
theorem abs_quittingChildWithOutsiderReward_sub_le
    (reward other : {A : Finset ι // A.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted] (outside : {who : ι // deleted who})
    (error : ℝ) (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (terminal : {A : Finset (Option (QuittingChildPlayer deleted)) // A.Nonempty})
    (who : Option (QuittingChildPlayer deleted)) :
    |quittingChildWithOutsiderReward other deleted outside terminal who -
      quittingChildWithOutsiderReward reward deleted outside terminal who| ≤ error :=
  hclose _ _

/-- A sampled F/J certificate with strict margins remains infeasible on nearby raw tables. -/
theorem not_nonempty_cappedClockParentFutureJoinCertificate_of_sampledDual_perturbation
    (reward other : {A : Finset (Option ι) // A.Nonempty} → Payoff (Option ι))
    (sample : Row → CappedClockExactLPRow ι) (hnever : ∀ row, sample row ≠ .never)
    (coefficient : Row → ℝ) (hcoefficient : ∀ row, 0 ≤ coefficient row)
    (error : ℝ) (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (hcolumns : ∀ who,
      (∑ row, coefficient row * cappedClockExactLPDelta reward (sample row) who) +
        2 * error * ∑ row, coefficient row ≤ 0)
    (hobjective : 2 * error * ∑ row, coefficient row <
      ∑ row, coefficient row * cappedClockExactLPBase reward (sample row)) :
    ¬Nonempty (CappedClockParentFutureJoinCertificate other) := by
  have hno := Maths.FiniteInequality.not_exists_nonnegativePotential_of_perturbation
    (fun row => cappedClockExactLPDelta reward (sample row))
    (fun row => cappedClockExactLPDelta other (sample row))
    (fun row => cappedClockExactLPBase reward (sample row))
    (fun row => cappedClockExactLPBase other (sample row)) coefficient (2 * error)
    hcoefficient
    (fun row who => abs_cappedClockExactLPDelta_sub_le reward other error hclose (sample row) who)
    (fun row => abs_cappedClockExactLPBase_sub_le reward other error hclose (sample row))
    hcolumns hobjective
  rintro ⟨certificate⟩
  exact hno ⟨certificate.weight, certificate.weight_nonneg,
    fun row => certificate.exactLPRow_le (sample row) (hnever row)⟩

end GameTheory
