import MathUE.Probability.ThreeIndependentFiniteLaws
import MathUE.Probability.OverlappingFirstStopping
import MathUE.ProbabilityMassFunction.StoppingLawLateIndicators
import MathUE.ProbabilityMassFunction.Coupling

/-! # Sparse finite independent laws and the overlapping first-stopping objective -/

noncomputable section

namespace Math
namespace Probability

section FiniteOverlap

variable {Date : Type*} [Fintype Date] [LinearOrder Date]

/-- The literal event indicator for a common finite first/second date strictly
before the third clock. `none` is Never, and an all-Never tie is excluded. -/
def finiteOverlapFirstKernel : Option Date → Option Date → Option Date → ℝ
  | some first, some second, none => if first = second then 1 else 0
  | some first, some second, some third => if first = second ∧ first < third then 1 else 0
  | _, _, _ => 0

def finiteOverlapFirstMass (first second third : PMF (Option Date)) : ℝ :=
  threeIndependentValue finiteOverlapFirstKernel first second third

def finiteOverlapSecondMass (first second third : PMF (Option Date)) : ℝ :=
  threeIndependentValue (fun first second third => finiteOverlapFirstKernel first third second)
    first second third

/-- On every finite ordered date set, with an additional literal Never atom,
the overlap square-root objective attains a global maximum at three laws
whose actual supports each have cardinality at most two. -/
theorem exists_twoSupported_finiteOverlap_maximizer :
    ∃ first second third : PMF (Option Date),
      Fintype.card {time // first time ≠ 0} ≤ 2 ∧
      Fintype.card {time // second time ≠ 0} ≤ 2 ∧
      Fintype.card {time // third time ≠ 0} ≤ 2 ∧
      ∀ otherFirst otherSecond otherThird : PMF (Option Date),
        Real.sqrt (finiteOverlapFirstMass otherFirst otherSecond otherThird) +
            Real.sqrt (finiteOverlapSecondMass otherFirst otherSecond otherThird) ≤
          Real.sqrt (finiteOverlapFirstMass first second third) +
            Real.sqrt (finiteOverlapSecondMass first second third) := by
  exact exists_three_twoSupported_pmf_sqrt_maximizer finiteOverlapFirstKernel
    (fun first second third => finiteOverlapFirstKernel first third second)

end FiniteOverlap

open DiscreteHazard.StoppingLaw

private theorem finiteOverlapFirstKernel_some_eq_indicator
    (time : ℕ) (second third : Option ℕ) :
    finiteOverlapFirstKernel (some time) second third =
      (if second = some time then 1 else 0) * stoppingLawTailIndicator (time + 1) third := by
  cases second with
  | none => simp [finiteOverlapFirstKernel]
  | some second =>
    cases third with
    | none => simp [finiteOverlapFirstKernel, stoppingLawTailIndicator, eq_comm]
    | some third =>
      simp only [finiteOverlapFirstKernel, stoppingLawTailIndicator,
        Finset.mem_image, Finset.mem_range, Option.some.injEq, exists_eq_right]
      by_cases heq : time = second
      · subst second
        have hrel : third < time + 1 ↔ ¬time < third := by omega
        by_cases hlt : time < third <;> simp [hrel, hlt]
      · simp [heq, Ne.symm heq]

/-- The finite-clock event expression is the canonical overlapping-event mass
on `Option Nat`; this identity itself does not require finite support. -/
theorem finiteOverlapFirstMass_eq_canonical
    (first second third : PMF (Option ℕ)) :
    finiteOverlapFirstMass first second third =
      equalFirstSecondBeforeThirdMass first second third := by
  have hinner (time : ℕ) :
      expect second (fun secondChoice =>
          expect third (finiteOverlapFirstKernel (some time) secondChoice)) =
        finiteMass second time * survival third (time + 1) := by
    have hfunction :
        (fun secondChoice =>
          expect third (finiteOverlapFirstKernel (some time) secondChoice)) =
          fun secondChoice => survival third (time + 1) *
            (if secondChoice = some time then 1 else 0) := by
      funext secondChoice
      change expect third (fun thirdChoice =>
        finiteOverlapFirstKernel (some time) secondChoice thirdChoice) = _
      simp_rw [finiteOverlapFirstKernel_some_eq_indicator]
      rw [expect_const_mul, expect_stoppingLawTailIndicator, mul_comm]
    rw [hfunction, expect_const_mul, expect_stoppingLaw_finite_atom]
    exact mul_comm _ _
  have hfunction :
      (fun firstChoice => expect second (fun secondChoice =>
        expect third (finiteOverlapFirstKernel firstChoice secondChoice))) =
        fun firstChoice => match firstChoice with
          | none => 0
          | some time => finiteMass second time * survival third (time + 1) := by
    funext firstChoice
    cases firstChoice with
    | none =>
      change expect second (fun secondChoice => expect third (fun thirdChoice =>
        finiteOverlapFirstKernel none secondChoice thirdChoice)) = 0
      simp [finiteOverlapFirstKernel, expect_const]
    | some time => exact hinner time
  unfold finiteOverlapFirstMass threeIndependentValue
  rw [hfunction]
  unfold expect equalFirstSecondBeforeThirdMass
  have hsum := (Option.some_injective ℕ).tsum_eq
    (f := fun firstChoice => (first firstChoice).toReal *
      match firstChoice with
      | none => 0
      | some time => finiteMass second time * survival third (time + 1)) (by
        intro firstChoice hnonzero
        cases firstChoice with
        | none => simp at hnonzero
        | some time => exact ⟨time, rfl⟩)
  simpa only [finiteMass, mul_assoc] using hsum.symm

/-- Symmetric canonical mass identity, with the expectation order exchanged. -/
theorem finiteOverlapSecondMass_eq_canonical
    (first second third : PMF (Option ℕ)) :
    finiteOverlapSecondMass first second third =
      equalFirstThirdBeforeSecondMass first second third := by
  have hswap : finiteOverlapSecondMass first second third =
      finiteOverlapFirstMass first third second := by
    unfold finiteOverlapSecondMass finiteOverlapFirstMass threeIndependentValue
    congr 1
    funext firstChoice
    cases firstChoice with
    | none =>
      change expect second (fun secondChoice => expect third (fun thirdChoice =>
          finiteOverlapFirstKernel none thirdChoice secondChoice)) =
        expect third (fun thirdChoice => expect second (fun secondChoice =>
          finiteOverlapFirstKernel none thirdChoice secondChoice))
      simp [finiteOverlapFirstKernel, expect_const]
    | some time =>
      change expect second (fun secondChoice => expect third (fun thirdChoice =>
          finiteOverlapFirstKernel (some time) thirdChoice secondChoice)) =
        expect third (fun thirdChoice => expect second (fun secondChoice =>
          finiteOverlapFirstKernel (some time) thirdChoice secondChoice))
      simp_rw [finiteOverlapFirstKernel_some_eq_indicator]
      let indicator : Option ℕ → ℝ := fun choice => if choice = some time then 1 else 0
      let tail := stoppingLawTailIndicator (time + 1)
      have hmul (constant : ℝ) :
          expect third (fun choice => indicator choice * constant) =
            expect third indicator * constant := by
        simpa only [mul_comm] using expect_const_mul third constant indicator
      change (expect second fun secondChoice =>
          expect third (fun thirdChoice => indicator thirdChoice * tail secondChoice)) =
        expect third (fun thirdChoice =>
          expect second (fun secondChoice => indicator thirdChoice * tail secondChoice))
      calc
        _ = expect second (fun choice => expect third indicator * tail choice) :=
          congrArg (expect second) (funext fun choice => hmul (tail choice))
        _ = expect third indicator * expect second tail := expect_const_mul _ _ _
        _ = expect third (fun choice => indicator choice * expect second tail) :=
          (hmul (expect second tail)).symm
        _ = _ := congrArg (expect third) (funext fun choice =>
          (expect_const_mul second (indicator choice) tail).symm)
  rw [hswap]
  exact finiteOverlapFirstMass_eq_canonical first third second

section DateEmbedding

variable {Date : Type*} [LinearOrder Date]

theorem finiteOverlapFirstKernel_map_dateEmbedding (embedding : Date ↪o ℕ)
    (first second third : Option Date) :
    finiteOverlapFirstKernel (Option.map embedding first) (Option.map embedding second)
        (Option.map embedding third) = finiteOverlapFirstKernel first second third := by
  cases first <;> cases second <;> cases third <;>
    simp [finiteOverlapFirstKernel, embedding.injective.eq_iff, embedding.lt_iff_lt]

/-- Embedding ordered dates preserves the full independent first event,
including the Never atom and strict comparisons. -/
theorem equalFirstSecondBeforeThirdMass_map_dateEmbedding (embedding : Date ↪o ℕ)
    (first second third : PMF (Option Date)) :
    equalFirstSecondBeforeThirdMass (first.map (Option.map embedding))
        (second.map (Option.map embedding)) (third.map (Option.map embedding)) =
      finiteOverlapFirstMass first second third := by
  rw [← finiteOverlapFirstMass_eq_canonical]
  unfold finiteOverlapFirstMass threeIndependentValue
  simp_rw [expect_map, finiteOverlapFirstKernel_map_dateEmbedding]

theorem equalFirstThirdBeforeSecondMass_map_dateEmbedding (embedding : Date ↪o ℕ)
    (first second third : PMF (Option Date)) :
    equalFirstThirdBeforeSecondMass (first.map (Option.map embedding))
        (second.map (Option.map embedding)) (third.map (Option.map embedding)) =
      finiteOverlapSecondMass first second third := by
  rw [← finiteOverlapSecondMass_eq_canonical]
  unfold finiteOverlapSecondMass threeIndependentValue
  simp_rw [expect_map, finiteOverlapFirstKernel_map_dateEmbedding]

/-- Every complete law confined to the embedded finite clock is the
pushforward of a law on that clock, so maximization covers all supported laws. -/
theorem exists_law_map_dateEmbedding_of_support_subset (embedding : Date ↪o ℕ)
    (law : PMF (Option ℕ)) (hsupport : law.support ⊆ Set.range (Option.map embedding)) :
    ∃ source : PMF (Option Date), source.map (Option.map embedding) = law := by
  refine ⟨law.map (Function.invFun (Option.map embedding)), ?_⟩
  rw [PMF.map_comp]
  apply ProbabilityMassFunction.PMF.map_eq_self_of_eq_on_support
  intro choice hchoice
  exact Function.invFun_eq (hsupport hchoice)

variable [Fintype Date]

theorem support_ncard_map_dateEmbedding (embedding : Date ↪o ℕ)
    (law : PMF (Option Date)) :
    (law.map (Option.map embedding)).support.ncard =
      Fintype.card {choice // law choice ≠ 0} := by
  classical
  rw [PMF.support_map,
    Set.ncard_image_of_injective _ (Option.map_injective embedding.injective),
    ← Set.fintypeCard_eq_ncard]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

/-- Canonical stopping-law version of the finite two-support maximizer.
The comparison is against every complete law supported on the chosen dates
and Never, not merely against laws supplied with reconstruction data. -/
theorem exists_twoSupported_canonicalOverlap_maximizer (embedding : Date ↪o ℕ) :
    ∃ first second third : PMF (Option ℕ),
      first.support ⊆ Set.range (Option.map embedding) ∧
      second.support ⊆ Set.range (Option.map embedding) ∧
      third.support ⊆ Set.range (Option.map embedding) ∧
      first.support.ncard ≤ 2 ∧ second.support.ncard ≤ 2 ∧ third.support.ncard ≤ 2 ∧
      ∀ otherFirst otherSecond otherThird : PMF (Option ℕ),
        otherFirst.support ⊆ Set.range (Option.map embedding) →
        otherSecond.support ⊆ Set.range (Option.map embedding) →
        otherThird.support ⊆ Set.range (Option.map embedding) →
        Real.sqrt (equalFirstSecondBeforeThirdMass otherFirst otherSecond otherThird) +
            Real.sqrt (equalFirstThirdBeforeSecondMass otherFirst otherSecond otherThird) ≤
          Real.sqrt (equalFirstSecondBeforeThirdMass first second third) +
            Real.sqrt (equalFirstThirdBeforeSecondMass first second third) := by
  obtain ⟨first, second, third, hfirst, hsecond, hthird, hmax⟩ :=
    exists_twoSupported_finiteOverlap_maximizer (Date := Date)
  have hsupport (law : PMF (Option Date)) :
      (law.map (Option.map embedding)).support ⊆ Set.range (Option.map embedding) := by
    rw [PMF.support_map]
    exact Set.image_subset_range _ _
  refine ⟨first.map (Option.map embedding), second.map (Option.map embedding),
    third.map (Option.map embedding), hsupport first, hsupport second, hsupport third,
    ?_, ?_, ?_, ?_⟩
  · exact (support_ncard_map_dateEmbedding embedding first).trans_le hfirst
  · exact (support_ncard_map_dateEmbedding embedding second).trans_le hsecond
  · exact (support_ncard_map_dateEmbedding embedding third).trans_le hthird
  · intro otherFirst otherSecond otherThird hotherFirst hotherSecond hotherThird
    obtain ⟨sourceFirst, rfl⟩ :=
      exists_law_map_dateEmbedding_of_support_subset embedding otherFirst hotherFirst
    obtain ⟨sourceSecond, rfl⟩ :=
      exists_law_map_dateEmbedding_of_support_subset embedding otherSecond hotherSecond
    obtain ⟨sourceThird, rfl⟩ :=
      exists_law_map_dateEmbedding_of_support_subset embedding otherThird hotherThird
    simp only [equalFirstSecondBeforeThirdMass_map_dateEmbedding,
      equalFirstThirdBeforeSecondMass_map_dateEmbedding]
    exact hmax sourceFirst sourceSecond sourceThird

end DateEmbedding

/-- An explicit finite menu of natural-number dates needs no supplied
embedding or encoding certificate. Never remains available separately. -/
theorem exists_twoSupported_canonicalOverlap_maximizer_on_dates (dates : Finset ℕ) :
    ∃ first second third : PMF (Option ℕ),
      first.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) ∧
      second.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) ∧
      third.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) ∧
      first.support.ncard ≤ 2 ∧ second.support.ncard ≤ 2 ∧ third.support.ncard ≤ 2 ∧
      ∀ otherFirst otherSecond otherThird : PMF (Option ℕ),
        otherFirst.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) →
        otherSecond.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) →
        otherThird.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) →
        Real.sqrt (equalFirstSecondBeforeThirdMass otherFirst otherSecond otherThird) +
            Real.sqrt (equalFirstThirdBeforeSecondMass otherFirst otherSecond otherThird) ≤
          Real.sqrt (equalFirstSecondBeforeThirdMass first second third) +
            Real.sqrt (equalFirstThirdBeforeSecondMass first second third) := by
  classical
  let embedding : dates ↪o ℕ := OrderEmbedding.subtype _
  have hrange : Set.range (Option.map embedding) =
      (↑(insert none (dates.image some)) : Set (Option ℕ)) := by
    ext choice
    constructor
    · rintro ⟨source, rfl⟩
      cases source with
      | none => simp
      | some time => simp [embedding, time.property]
    · intro hchoice
      rcases Finset.mem_insert.mp hchoice with rfl | hchoice
      · exact ⟨none, rfl⟩
      · obtain ⟨time, htime, rfl⟩ := Finset.mem_image.mp hchoice
        exact ⟨some ⟨time, htime⟩, rfl⟩
  simpa only [hrange] using exists_twoSupported_canonicalOverlap_maximizer embedding

end Probability

end Math
