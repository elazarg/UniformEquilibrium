/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.GeneralTotalVariation
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Discrete tightness and total variation

For arbitrary probability mass functions, uniform approximation by finite
sets is equivalent to total boundedness in total variation.  Both notions are
stated through literal finite nets, without installing a topology on `PMF`.
-/

noncomputable section

open scoped BigOperators
open Filter

namespace Math
namespace Probability

/-- Mass outside a finite set, expressed without a measurable-space choice. -/
def pmfFiniteComplementMass {Omega : Type*} (law : PMF Omega)
    (kept : Finset Omega) : Real :=
  1 - ∑ omega ∈ kept, (law omega).toReal

theorem pmfFiniteComplementMass_nonneg {Omega : Type*} (law : PMF Omega)
    (kept : Finset Omega) :
    0 <= pmfFiniteComplementMass law kept := by
  rw [pmfFiniteComplementMass, sub_nonneg]
  calc
    (∑ omega ∈ kept, (law omega).toReal) <=
        ∑' omega, (law omega).toReal :=
      (pmf_toReal_summable law).sum_le_tsum kept
        (fun _ _ => ENNReal.toReal_nonneg)
    _ = 1 := pmf_toReal_tsum_one law

theorem pmfFiniteComplementMass_anti {Omega : Type*} (law : PMF Omega)
    {first second : Finset Omega} (hsubset : first ⊆ second) :
    pmfFiniteComplementMass law second <=
      pmfFiniteComplementMass law first := by
  unfold pmfFiniteComplementMass
  exact sub_le_sub_left (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun omega _ _ => ENNReal.toReal_nonneg)) 1

theorem pmfGeneralTV_le_finiteComplementMass_add_sum_abs
    {Omega : Type*} (mu nu : PMF Omega) (kept : Finset Omega) :
    pmfGeneralTV mu nu <=
      pmfFiniteComplementMass mu kept +
        ∑ omega ∈ kept, |(mu omega).toReal - (nu omega).toReal| := by
  let overlap : Omega -> Real := fun omega =>
    min ((mu omega).toReal) ((nu omega).toReal)
  have hoverlapNonneg : forall omega, 0 <= overlap omega := fun omega =>
    le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hoverlapSummable : Summable overlap := by
    exact Summable.of_nonneg_of_le hoverlapNonneg
      (fun omega => min_le_left _ _) (pmf_toReal_summable mu)
  have hfiniteOverlap :
      (∑ omega ∈ kept, overlap omega) <= ∑' omega, overlap omega :=
    hoverlapSummable.sum_le_tsum kept (fun omega _ => hoverlapNonneg omega)
  have hcoordinate : forall omega,
      (mu omega).toReal <=
        overlap omega + |(mu omega).toReal - (nu omega).toReal| := by
    intro omega
    dsimp only [overlap]
    by_cases hle : (mu omega).toReal <= (nu omega).toReal
    · rw [min_eq_left hle]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [min_eq_right (le_of_not_ge hle), abs_of_pos (sub_pos.mpr (lt_of_not_ge hle))]
      linarith
  have hsum := Finset.sum_le_sum fun omega (_ : omega ∈ kept) =>
    hcoordinate omega
  rw [Finset.sum_add_distrib] at hsum
  unfold pmfGeneralTV pmfFiniteComplementMass
  change 1 - ∑' omega, overlap omega <= _
  linarith

/-- Literal finite-net total boundedness for arbitrary discrete laws.  Net
centers are retained inside the family. -/
def IsPMFGeneralTVTotallyBounded {Omega : Type*}
    (family : Set (PMF Omega)) : Prop :=
  ∀ error : Real, 0 < error ->
    ∃ net : Set (PMF Omega),
      net.Finite ∧ net ⊆ family ∧
        ∀ law ∈ family, ∃ center ∈ net,
          pmfGeneralTV law center < error

/-- Uniform discrete tightness by finite subsets of the sample space. -/
def IsPMFUniformlyFiniteTight {Omega : Type*}
    (family : Set (PMF Omega)) : Prop :=
  ∀ error : Real, 0 < error ->
    ∃ kept : Finset Omega, ∀ law ∈ family,
      pmfFiniteComplementMass law kept < error

theorem exists_finset_pmfFiniteComplementMass_lt
    {Omega : Type*} (law : PMF Omega) {error : Real} (herror : 0 < error) :
    ∃ kept : Finset Omega, pmfFiniteComplementMass law kept < error := by
  have hsum : HasSum (fun omega : Omega => (law omega).toReal) 1 := by
    simpa [pmf_toReal_tsum_one law] using (pmf_toReal_summable law).hasSum
  have hevent : ∀ᶠ kept : Finset Omega in atTop,
      dist (∑ omega ∈ kept, (law omega).toReal) 1 < error :=
    hsum.eventually (Metric.ball_mem_nhds 1 herror)
  obtain ⟨kept, hkept⟩ := hevent.exists
  refine ⟨kept, ?_⟩
  rw [Real.dist_eq] at hkept
  unfold pmfFiniteComplementMass
  linarith [neg_abs_le
    ((∑ omega ∈ kept, (law omega).toReal) - 1)]

private theorem restrictedVector_mem_closedBall
    {Omega : Type*} (kept : Finset Omega) (law : PMF Omega) :
    (fun omega : {omega // omega ∈ kept} => (law omega).toReal) ∈
      Metric.closedBall (0 : {omega // omega ∈ kept} -> Real) 1 := by
  rw [Metric.mem_closedBall, dist_pi_le_iff zero_le_one]
  intro omega
  rw [Pi.zero_apply, Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one law omega)

theorem isPMFGeneralTVTotallyBounded_of_uniformlyFiniteTight
    {Omega : Type*} (family : Set (PMF Omega))
    (htight : IsPMFUniformlyFiniteTight family) :
    IsPMFGeneralTVTotallyBounded family := by
  intro error herror
  by_cases hempty : family = ∅
  · exact ⟨∅, Set.finite_empty, by simp [hempty]⟩
  obtain ⟨kept, hkept⟩ := htight (error / 2) (by linarith)
  have hfamilyNonempty : family.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
  letI : Nonempty {law // law ∈ family} := hfamilyNonempty.to_subtype
  let vectors : Set ({omega // omega ∈ kept} -> Real) :=
    Metric.closedBall 0 1
  have hvectorsCompact : IsCompact vectors := isCompact_closedBall 0 1
  obtain ⟨centers, hcentersFinite, hcentersCover⟩ :=
    (Metric.totallyBounded_iff.mp hvectorsCompact.totallyBounded)
      (error / (4 * max 1 kept.card)) (by positivity)
  letI : Fintype {point // point ∈ centers} := hcentersFinite.fintype
  let vectorOf : PMF Omega -> ({omega // omega ∈ kept} -> Real) :=
    fun law omega => (law omega).toReal
  have hcenterExists : ∀ law ∈ family,
      ∃ center ∈ centers,
        dist (vectorOf law) center < error / (4 * max 1 kept.card) := by
    intro law hlaw
    have hmem := hcentersCover (restrictedVector_mem_closedBall kept law)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hmem
    obtain ⟨point, hpoint, hclose⟩ := hmem
    exact ⟨point, hpoint, hclose⟩
  choose center hcenterMem hcenterClose using hcenterExists
  let indexedCenter : {law // law ∈ family} -> {point // point ∈ centers} :=
    fun law => ⟨center law law.property, hcenterMem law law.property⟩
  let representative : {point // point ∈ centers} -> {law // law ∈ family} :=
    Function.invFun indexedCenter
  let net : Set (PMF Omega) := Set.range (Subtype.val ∘ representative)
  have hnetFinite : net.Finite := Set.finite_range _
  have hnetSubset : net ⊆ family := by
    rintro law ⟨point, rfl⟩
    exact (representative point).property
  refine ⟨net, hnetFinite, hnetSubset, fun law hlaw => ?_⟩
  let lawInFamily : {law // law ∈ family} := ⟨law, hlaw⟩
  let point := indexedCenter lawInFamily
  let selected := representative point
  have hpoint : indexedCenter selected = point := by
    dsimp only [selected, representative, point]
    exact Function.invFun_eq ⟨lawInFamily, rfl⟩
  have hsameCenter : center selected selected.property = center law hlaw := by
    exact Subtype.ext_iff.mp hpoint
  refine ⟨selected, ⟨point, rfl⟩, ?_⟩
  have hlawClose := hcenterClose law hlaw
  have hselectedClose := hcenterClose selected selected.property
  have hcoordinate : forall omega : {omega // omega ∈ kept},
      |(law omega).toReal - ((selected : PMF Omega) omega).toReal| <
        error / (2 * max 1 kept.card) := by
    intro omega
    have hlawCoordinate :
        dist (vectorOf law omega) (center law hlaw omega) <
          error / (4 * max 1 kept.card) :=
      (dist_pi_lt_iff (by positivity)).mp hlawClose omega
    have hselectedCoordinate :
        |center selected selected.property omega -
          vectorOf selected omega| <
          error / (4 * max 1 kept.card) :=
      by
        have hdistance := (dist_pi_lt_iff (by positivity)).mp
          hselectedClose omega
        simpa only [Real.dist_eq, abs_sub_comm] using hdistance
    rw [hsameCenter] at hselectedCoordinate
    rw [Real.dist_eq] at hlawCoordinate
    dsimp only [vectorOf] at hlawCoordinate hselectedCoordinate
    calc
      |(law omega).toReal - ((selected : PMF Omega) omega).toReal| <=
          |(law omega).toReal - center law hlaw omega| +
            |center law hlaw omega -
              ((selected : PMF Omega) omega).toReal| := abs_sub_le _ _ _
      _ < error / (4 * max 1 kept.card) +
          error / (4 * max 1 kept.card) :=
        add_lt_add hlawCoordinate hselectedCoordinate
      _ = error / (2 * max 1 kept.card) := by ring
  have hsumAbs :
      (∑ omega ∈ kept,
        |(law omega).toReal - ((selected : PMF Omega) omega).toReal|) <
        error / 2 := by
    by_cases hkeptNonempty : kept.Nonempty
    · calc
        (∑ omega ∈ kept,
          |(law omega).toReal - ((selected : PMF Omega) omega).toReal|) <
            ∑ _omega ∈ kept, error / (2 * max 1 kept.card) := by
          exact Finset.sum_lt_sum_of_nonempty hkeptNonempty
            (fun omega homega => hcoordinate ⟨omega, homega⟩)
        _ <= error / 2 := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hcard : (kept.card : Real) <= (max 1 kept.card : Nat) := by
            exact_mod_cast Nat.le_max_right 1 kept.card
          have hmaxPos : (0 : Real) < max 1 kept.card := by positivity
          calc
            (kept.card : Real) * (error / (2 * max 1 kept.card)) <=
                max 1 kept.card * (error / (2 * max 1 kept.card)) := by
              exact mul_le_mul_of_nonneg_right hcard (by positivity)
            _ = error / 2 := by field_simp
    · rw [Finset.not_nonempty_iff_eq_empty.mp hkeptNonempty]
      simpa using (show 0 < error / 2 by linarith)
  exact (pmfGeneralTV_le_finiteComplementMass_add_sum_abs law selected kept).trans_lt
    (by linarith [hkept law hlaw])

theorem abs_pmfFiniteComplementMass_sub_le_two_mul_pmfGeneralTV
    {Omega : Type*} (mu nu : PMF Omega) (kept : Finset Omega) :
    |pmfFiniteComplementMass mu kept -
        pmfFiniteComplementMass nu kept| <= 2 * pmfGeneralTV mu nu := by
  classical
  let indicator : Omega -> Real := fun omega => if omega ∈ kept then 1 else 0
  have hbound : forall omega, |indicator omega| <= 1 := by
    intro omega
    simp only [indicator]
    split_ifs <;> norm_num
  have hvariation :=
    abs_expect_sub_le_two_mul_bound_mul_pmfGeneralTV mu nu indicator hbound
  have hexpect : forall law : PMF Omega,
      expect law indicator = ∑ omega ∈ kept, (law omega).toReal := by
    intro law
    unfold expect
    rw [tsum_eq_sum (s := kept)]
    · simp [indicator]
    · intro omega hnot
      simp [indicator, hnot]
  rw [hexpect mu, hexpect nu] at hvariation
  simpa [pmfFiniteComplementMass, abs_sub_comm] using hvariation

theorem isPMFUniformlyFiniteTight_of_generalTVTotallyBounded
    {Omega : Type*} (family : Set (PMF Omega))
    (hbounded : IsPMFGeneralTVTotallyBounded family) :
    IsPMFUniformlyFiniteTight family := by
  classical
  intro error herror
  obtain ⟨net, hnetFinite, -, hnetCover⟩ :=
    hbounded (error / 8) (by linarith)
  choose kept hkept using fun center : PMF Omega =>
    exists_finset_pmfFiniteComplementMass_lt center (error := error / 2)
      (by linarith)
  let common : Finset Omega := hnetFinite.toFinset.biUnion kept
  refine ⟨common, fun law hlaw => ?_⟩
  obtain ⟨center, hcenterNet, hclose⟩ := hnetCover law hlaw
  have hcenterMem : center ∈ hnetFinite.toFinset :=
    Set.Finite.mem_toFinset hnetFinite |>.mpr hcenterNet
  have hkeptSubset : kept center ⊆ common := by
    intro omega homega
    exact Finset.mem_biUnion.mpr ⟨center, hcenterMem, homega⟩
  have hcenterTail : pmfFiniteComplementMass center common < error / 2 :=
    (pmfFiniteComplementMass_anti center hkeptSubset).trans_lt (hkept center)
  have hvariation :=
    abs_pmfFiniteComplementMass_sub_le_two_mul_pmfGeneralTV law center common
  have hvariationSmall :
      |pmfFiniteComplementMass law common -
          pmfFiniteComplementMass center common| < error / 4 := by
    calc
      |pmfFiniteComplementMass law common -
          pmfFiniteComplementMass center common| <=
          2 * pmfGeneralTV law center := hvariation
      _ < 2 * (error / 8) :=
        mul_lt_mul_of_pos_left hclose (by norm_num)
      _ = error / 4 := by ring
  linarith [le_abs_self
    (pmfFiniteComplementMass law common -
      pmfFiniteComplementMass center common)]

theorem isPMFGeneralTVTotallyBounded_iff_uniformlyFiniteTight
    {Omega : Type*} (family : Set (PMF Omega)) :
    IsPMFGeneralTVTotallyBounded family <->
      IsPMFUniformlyFiniteTight family :=
  ⟨isPMFUniformlyFiniteTight_of_generalTVTotallyBounded family,
    isPMFGeneralTVTotallyBounded_of_uniformlyFiniteTight family⟩

theorem exists_pos_forall_exists_finiteComplementMass_ge_of_not_totallyBounded
    {Omega : Type*} {family : Set (PMF Omega)}
    (hnot : ¬ IsPMFGeneralTVTotallyBounded family) :
    ∃ kappa : Real, 0 < kappa ∧
      ∀ kept : Finset Omega, ∃ law ∈ family,
        kappa <= pmfFiniteComplementMass law kept := by
  have hnotTight : ¬ IsPMFUniformlyFiniteTight family := by
    intro htight
    exact hnot (isPMFGeneralTVTotallyBounded_of_uniformlyFiniteTight family htight)
  unfold IsPMFUniformlyFiniteTight at hnotTight
  push Not at hnotTight
  exact hnotTight

end Probability
end Math
