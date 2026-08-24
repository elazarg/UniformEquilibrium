/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.DiscreteTightness

/-!
# Proper approximation of discrete stopping laws

For laws on `Option Nat`, finite approximation in total variation by laws
with no `none` mass is equivalent to a common finite-time tightness bound.
The complement tail includes both finite dates after the cutoff and `none`.
-/

noncomputable section

open scoped BigOperators

namespace Math
namespace Probability

/-- The finite stopping dates through `horizon`; `none` is not retained. -/
def stoppingLawFiniteTimePrefix (horizon : Nat) : Finset (Option Nat) :=
  (Finset.range (horizon + 1)).image some

@[simp] theorem none_not_mem_stoppingLawFiniteTimePrefix (horizon : Nat) :
    none ∉ stoppingLawFiniteTimePrefix horizon := by
  simp [stoppingLawFiniteTimePrefix]

@[simp] theorem some_mem_stoppingLawFiniteTimePrefix (horizon time : Nat) :
    some time ∈ stoppingLawFiniteTimePrefix horizon <-> time <= horizon := by
  simp [stoppingLawFiniteTimePrefix]

theorem stoppingLawFiniteTimePrefix_mono {first second : Nat}
    (hle : first <= second) :
    stoppingLawFiniteTimePrefix first ⊆
      stoppingLawFiniteTimePrefix second := by
  intro outcome houtcome
  obtain ⟨time, htime, rfl⟩ := Finset.mem_image.mp houtcome
  exact (some_mem_stoppingLawFiniteTimePrefix second time).2
    ((some_mem_stoppingLawFiniteTimePrefix first time).1 houtcome |>.trans hle)

/-- Mass at finite dates after `horizon`, together with the `none` atom. -/
def stoppingLawLateOrNeverMass (law : PMF (Option Nat))
    (horizon : Nat) : Real :=
  pmfFiniteComplementMass law (stoppingLawFiniteTimePrefix horizon)

/-- A stopping law is proper when it stops at a finite date almost surely. -/
def IsProperStoppingLaw (law : PMF (Option Nat)) : Prop :=
  law none = 0

/-- Finite total-variation approximation by proper centers.  Centers need not
belong to the approximated family, and the net is explicitly nonempty. -/
def IsPMFProperTVApproximable (family : Set (PMF (Option Nat))) : Prop :=
  ∀ error : Real, 0 < error ->
    ∃ net : Set (PMF (Option Nat)),
      net.Finite ∧ net.Nonempty ∧
        (∀ center ∈ net, IsProperStoppingLaw center) ∧
        ∀ law ∈ family, ∃ center ∈ net,
          pmfGeneralTV law center < error

/-- Uniform tightness on finite stopping dates.  Its tail contains `none`. -/
def IsPMFUniformlyFiniteTimeTight
    (family : Set (PMF (Option Nat))) : Prop :=
  ∀ error : Real, 0 < error -> ∃ horizon : Nat,
    ∀ law ∈ family, stoppingLawLateOrNeverMass law horizon < error

/-- Every finite set of stopping outcomes is contained in a finite-time
prefix together with `none`. -/
theorem exists_horizon_finset_subset_optionPrefix
    (kept : Finset (Option Nat)) :
    ∃ horizon : Nat, kept ⊆
      {none} ∪ stoppingLawFiniteTimePrefix horizon := by
  classical
  let finiteValue : Option Nat -> Nat
    | none => 0
    | some time => time
  refine ⟨kept.sup finiteValue, fun choice hchoice => ?_⟩
  cases choice with
  | none => simp
  | some time =>
      have htime : time <= kept.sup finiteValue := by
        simpa [finiteValue] using
          (Finset.le_sup (s := kept) (f := finiteValue) hchoice)
      simp [htime]

/-- For a proper law, adding `none` to a retained finite set does not change
its complement mass. -/
theorem pmfFiniteComplementMass_insert_none_of_proper
    (law : PMF (Option Nat)) (hproper : IsProperStoppingLaw law)
    (kept : Finset (Option Nat)) :
    pmfFiniteComplementMass law (insert none kept) =
      pmfFiniteComplementMass law kept := by
  classical
  by_cases hnone : none ∈ kept
  · rw [Finset.insert_eq_of_mem hnone]
  · unfold pmfFiniteComplementMass
    rw [Finset.sum_insert hnone]
    have hnoneZero : (law none).toReal = 0 := by rw [hproper]; rfl
    rw [hnoneZero, zero_add]

/-- Every proper stopping law has arbitrarily small late-or-Never mass. -/
theorem exists_horizon_lateOrNeverMass_lt_of_proper
    (law : PMF (Option Nat)) (hproper : IsProperStoppingLaw law)
    {error : Real} (herror : 0 < error) :
    ∃ horizon : Nat, stoppingLawLateOrNeverMass law horizon < error := by
  obtain ⟨kept, hkept⟩ :=
    exists_finset_pmfFiniteComplementMass_lt law herror
  obtain ⟨horizon, hsubset⟩ :=
    exists_horizon_finset_subset_optionPrefix kept
  have hanti := pmfFiniteComplementMass_anti law hsubset
  have hnoneNotMem := none_not_mem_stoppingLawFiniteTimePrefix horizon
  have hunion : {none} ∪ stoppingLawFiniteTimePrefix horizon =
      insert none (stoppingLawFiniteTimePrefix horizon) := by ext; simp
  rw [hunion,
    pmfFiniteComplementMass_insert_none_of_proper law hproper] at hanti
  exact ⟨horizon, hanti.trans_lt hkept⟩

/-- Collapse every late date and `none` to the finite date `horizon + 1`. -/
def truncateStoppingOutcome (horizon : Nat) : Option Nat -> Option Nat
  | some time => if time <= horizon then some time else some (horizon + 1)
  | none => some (horizon + 1)

/-- The corresponding finite-support proper truncation of a stopping law. -/
def truncateStoppingLaw (law : PMF (Option Nat)) (horizon : Nat) :
    PMF (Option Nat) :=
  law.map (truncateStoppingOutcome horizon)

@[simp] theorem truncateStoppingLaw_none
    (law : PMF (Option Nat)) (horizon : Nat) :
    truncateStoppingLaw law horizon none = 0 := by
  classical
  rw [truncateStoppingLaw, PMF.map_apply, ENNReal.tsum_eq_zero]
  intro choice
  cases choice with
  | none => simp [truncateStoppingOutcome]
  | some time =>
      by_cases htime : time <= horizon
      · simp [truncateStoppingOutcome, htime]
      · simp [truncateStoppingOutcome, htime]

theorem truncateStoppingLaw_isProper
    (law : PMF (Option Nat)) (horizon : Nat) :
    IsProperStoppingLaw (truncateStoppingLaw law horizon) := by
  exact truncateStoppingLaw_none law horizon

/-- Truncation preserves every retained finite-time coordinate. -/
theorem truncateStoppingLaw_apply_of_le
    (law : PMF (Option Nat)) {horizon time : Nat} (htime : time <= horizon) :
    truncateStoppingLaw law horizon (some time) = law (some time) := by
  classical
  rw [truncateStoppingLaw, PMF.map_apply, tsum_eq_single (some time)]
  · simp [truncateStoppingOutcome, htime]
  · intro choice hchoice
    cases choice with
    | none =>
        rw [if_neg]
        intro heq
        change some time = some (horizon + 1) at heq
        have := Option.some.inj heq
        omega
    | some other =>
        by_cases hother : other <= horizon
        · have hotherNe : other ≠ time := by
            intro heq
            subst other
            exact hchoice rfl
          rw [if_neg]
          intro heq
          rw [truncateStoppingOutcome, if_pos hother] at heq
          exact hotherNe (Option.some.inj heq).symm
        · rw [if_neg]
          intro heq
          rw [truncateStoppingOutcome, if_neg hother] at heq
          have := Option.some.inj heq
          omega

/-- Truncation is within the original law's late-or-Never mass in general
total variation. -/
theorem pmfGeneralTV_truncateStoppingLaw_le
    (law : PMF (Option Nat)) (horizon : Nat) :
    pmfGeneralTV law (truncateStoppingLaw law horizon) <=
      stoppingLawLateOrNeverMass law horizon := by
  have hbound := pmfGeneralTV_le_finiteComplementMass_add_sum_abs
    law (truncateStoppingLaw law horizon)
      (stoppingLawFiniteTimePrefix horizon)
  have hsum : (∑ outcome ∈ stoppingLawFiniteTimePrefix horizon,
      |(law outcome).toReal -
        (truncateStoppingLaw law horizon outcome).toReal|) = 0 := by
    apply Finset.sum_eq_zero
    intro outcome houtcome
    obtain ⟨time, htime, rfl⟩ :=
      Finset.mem_image.mp houtcome
    rw [truncateStoppingLaw_apply_of_le law
      ((some_mem_stoppingLawFiniteTimePrefix horizon time).1 houtcome)]
    simp
  rw [hsum, add_zero] at hbound
  exact hbound

/-- The truncation is supported on finite dates through `horizon + 1`. -/
theorem truncateStoppingLaw_support_subset
    (law : PMF (Option Nat)) (horizon : Nat) :
    (truncateStoppingLaw law horizon).support ⊆
      ↑(stoppingLawFiniteTimePrefix (horizon + 1)) := by
  intro outcome houtcome
  obtain ⟨source, _hsource, hsource⟩ :=
    (PMF.mem_support_map_iff
      (truncateStoppingOutcome horizon) law outcome).1 houtcome
  rw [← hsource]
  cases source with
  | none => simp [truncateStoppingOutcome]
  | some time =>
      by_cases htime : time <= horizon
      · simp [truncateStoppingOutcome, htime, htime.trans (Nat.le_succ _)]
      · simp [truncateStoppingOutcome, htime]

/-- A PMF supported on a finite retained set has zero complement mass. -/
theorem pmfFiniteComplementMass_eq_zero_of_support_subset
    {Omega : Type*} (law : PMF Omega) (kept : Finset Omega)
    (hsupport : law.support ⊆ ↑kept) :
    pmfFiniteComplementMass law kept = 0 := by
  have hsum : (∑ omega ∈ kept, (law omega).toReal) = 1 := by
    rw [← pmf_toReal_tsum_one law]
    symm
    apply tsum_eq_sum
    intro omega hnot
    have hzero : law omega = 0 := by
      by_contra hne
      exact hnot (hsupport ((PMF.mem_support_iff law omega).2 hne))
    simp [hzero]
  simp [pmfFiniteComplementMass, hsum]

/-- One coordinate changes by at most twice general total variation. -/
theorem abs_pmf_apply_toReal_sub_le_two_mul_pmfGeneralTV
    {Omega : Type*} (mu nu : PMF Omega) (outcome : Omega) :
    |(mu outcome).toReal - (nu outcome).toReal| <=
      2 * pmfGeneralTV mu nu := by
  classical
  let indicator : Omega -> Real := fun candidate =>
    if candidate = outcome then 1 else 0
  have hbound : ∀ candidate, |indicator candidate| <= 1 := by
    intro candidate
    simp only [indicator]
    split_ifs <;> norm_num
  have hvariation :=
    abs_expect_sub_le_two_mul_bound_mul_pmfGeneralTV
      mu nu indicator hbound
  have hexpect : ∀ law : PMF Omega,
      expect law indicator = (law outcome).toReal := by
    intro law
    unfold expect
    rw [tsum_eq_single outcome]
    · simp [indicator]
    · intro candidate hcandidate
      simp [indicator, hcandidate]
  simpa [hexpect, indicator] using hvariation

/-- Proper total-variation approximation implies a common finite-time tail
bound. -/
theorem isPMFUniformlyFiniteTimeTight_of_properTVApproximable
    (family : Set (PMF (Option Nat)))
    (happrox : IsPMFProperTVApproximable family) :
    IsPMFUniformlyFiniteTimeTight family := by
  classical
  intro error herror
  obtain ⟨net, hnetFinite, _hnetNonempty, hnetProper, hnetCover⟩ :=
    happrox (error / 8) (by linarith)
  choose horizon htail using fun center : {center // center ∈ net} =>
    exists_horizon_lateOrNeverMass_lt_of_proper center.1
      (hnetProper center.1 center.2) (error := error / 2) (by linarith)
  let common := hnetFinite.toFinset.attach.sup fun center =>
    horizon ⟨center.1, Set.Finite.mem_toFinset hnetFinite |>.mp center.2⟩
  refine ⟨common, fun law hlaw => ?_⟩
  obtain ⟨center, hcenter, hclose⟩ := hnetCover law hlaw
  let centerInNet : {center // center ∈ net} := ⟨center, hcenter⟩
  have hhorizon : horizon centerInNet <= common := by
    exact Finset.le_sup (s := hnetFinite.toFinset.attach)
      (f := fun candidate => horizon
        ⟨candidate.1,
          Set.Finite.mem_toFinset hnetFinite |>.mp candidate.2⟩)
      (show ⟨center,
          Set.Finite.mem_toFinset hnetFinite |>.mpr hcenter⟩ ∈
        hnetFinite.toFinset.attach by simp)
  have hcenterTail : stoppingLawLateOrNeverMass center common < error / 2 := by
    apply (pmfFiniteComplementMass_anti center
      (stoppingLawFiniteTimePrefix_mono hhorizon)).trans_lt
    exact htail centerInNet
  have hvariation := abs_pmfFiniteComplementMass_sub_le_two_mul_pmfGeneralTV
    law center (stoppingLawFiniteTimePrefix common)
  have hvariationSmall :
      |stoppingLawLateOrNeverMass law common -
          stoppingLawLateOrNeverMass center common| < error / 4 := by
    calc
      |stoppingLawLateOrNeverMass law common -
          stoppingLawLateOrNeverMass center common| <=
          2 * pmfGeneralTV law center := hvariation
      _ < 2 * (error / 8) :=
        mul_lt_mul_of_pos_left hclose (by norm_num)
      _ = error / 4 := by ring
  linarith [le_abs_self (stoppingLawLateOrNeverMass law common -
    stoppingLawLateOrNeverMass center common)]

/-- A common finite-time tail bound gives finite total-variation nets with
proper centers. -/
theorem isPMFProperTVApproximable_of_uniformlyFiniteTimeTight
    (family : Set (PMF (Option Nat)))
    (htight : IsPMFUniformlyFiniteTimeTight family) :
    IsPMFProperTVApproximable family := by
  classical
  intro error herror
  by_cases hempty : family = ∅
  · let center : PMF (Option Nat) := PMF.pure (some 0)
    refine ⟨{center}, Set.finite_singleton center, Set.singleton_nonempty center,
      ?_, by simp [hempty]⟩
    intro candidate hcandidate
    rw [Set.mem_singleton_iff.mp hcandidate]
    simp [IsProperStoppingLaw, center]
  obtain ⟨horizon, htail⟩ := htight (error / 2) (by linarith)
  let truncatedFamily : Set (PMF (Option Nat)) :=
    (fun law => truncateStoppingLaw law horizon) '' family
  have htruncatedTight : IsPMFUniformlyFiniteTight truncatedFamily := by
    intro delta hdelta
    refine ⟨stoppingLawFiniteTimePrefix (horizon + 1),
      fun law hlaw => ?_⟩
    obtain ⟨source, _hsource, rfl⟩ := hlaw
    rw [pmfFiniteComplementMass_eq_zero_of_support_subset]
    · exact hdelta
    · exact truncateStoppingLaw_support_subset source horizon
  have htruncatedBounded :=
    isPMFGeneralTVTotallyBounded_of_uniformlyFiniteTight
      truncatedFamily htruncatedTight
  let scale : Nat := max 1 (stoppingLawFiniteTimePrefix horizon).card
  have hscalePos : (0 : Real) < scale := by positivity
  obtain ⟨net, hnetFinite, hnetSubset, hnetCover⟩ :=
    htruncatedBounded (error / (4 * scale))
      (div_pos herror (by positivity))
  have htruncatedNonempty : truncatedFamily.Nonempty := by
    obtain ⟨law, hlaw⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    exact ⟨truncateStoppingLaw law horizon, ⟨law, hlaw, rfl⟩⟩
  have hnetNonempty : net.Nonempty := by
    obtain ⟨law, hlaw⟩ := htruncatedNonempty
    obtain ⟨center, hcenter, _hclose⟩ := hnetCover law hlaw
    exact ⟨center, hcenter⟩
  refine ⟨net, hnetFinite, hnetNonempty, ?_, fun law hlaw => ?_⟩
  · intro center hcenter
    obtain ⟨source, _hsource, hsource⟩ := hnetSubset hcenter
    rw [← hsource]
    exact truncateStoppingLaw_isProper source horizon
  · have htruncatedMem : truncateStoppingLaw law horizon ∈ truncatedFamily :=
      ⟨law, hlaw, rfl⟩
    obtain ⟨center, hcenter, hclose⟩ :=
      hnetCover (truncateStoppingLaw law horizon) htruncatedMem
    refine ⟨center, hcenter, ?_⟩
    have hcoordinate : ∀ outcome ∈ stoppingLawFiniteTimePrefix horizon,
        |(law outcome).toReal - (center outcome).toReal| <
          error / (2 * scale) := by
      intro outcome houtcome
      obtain ⟨time, htime, rfl⟩ := Finset.mem_image.mp houtcome
      rw [← truncateStoppingLaw_apply_of_le law
        ((some_mem_stoppingLawFiniteTimePrefix horizon time).1 houtcome)]
      exact (abs_pmf_apply_toReal_sub_le_two_mul_pmfGeneralTV
        (truncateStoppingLaw law horizon) center (some time)).trans_lt (by
          calc
            2 * pmfGeneralTV (truncateStoppingLaw law horizon) center <
                2 * (error / (4 * scale)) :=
              mul_lt_mul_of_pos_left hclose (by norm_num)
            _ = error / (2 * scale) := by ring)
    have hsum : (∑ outcome ∈ stoppingLawFiniteTimePrefix horizon,
        |(law outcome).toReal - (center outcome).toReal|) < error / 2 := by
      calc
        (∑ outcome ∈ stoppingLawFiniteTimePrefix horizon,
            |(law outcome).toReal - (center outcome).toReal|) <
            ∑ _outcome ∈ stoppingLawFiniteTimePrefix horizon,
              error / (2 * scale) := by
          exact Finset.sum_lt_sum_of_nonempty
            (by simp [stoppingLawFiniteTimePrefix]) hcoordinate
        _ <= error / 2 := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hcard :
              ((stoppingLawFiniteTimePrefix horizon).card : Real) <= scale := by
            exact_mod_cast Nat.le_max_right 1
              (stoppingLawFiniteTimePrefix horizon).card
          calc
            ((stoppingLawFiniteTimePrefix horizon).card : Real) *
                (error / (2 * scale)) <=
                scale * (error / (2 * scale)) := by
              exact mul_le_mul_of_nonneg_right hcard (by positivity)
            _ = error / 2 := by field_simp
    exact (pmfGeneralTV_le_finiteComplementMass_add_sum_abs
      law center (stoppingLawFiniteTimePrefix horizon)).trans_lt
        (by simpa [stoppingLawLateOrNeverMass] using
          add_lt_add (htail law hlaw) hsum)

/-- Exact equivalence between proper total-variation approximation and a
uniform late-or-Never tail bound. -/
theorem isPMFProperTVApproximable_iff_uniformlyFiniteTimeTight
    (family : Set (PMF (Option Nat))) :
    IsPMFProperTVApproximable family <->
      IsPMFUniformlyFiniteTimeTight family :=
  ⟨isPMFUniformlyFiniteTimeTight_of_properTVApproximable family,
    isPMFProperTVApproximable_of_uniformlyFiniteTimeTight family⟩

/-- Failure of proper approximation gives one fixed positive amount of
late-or-Never mass beyond every finite horizon. -/
theorem exists_pos_forall_exists_lateOrNeverMass_ge_of_not_properTVApproximable
    {family : Set (PMF (Option Nat))}
    (hnot : ¬ IsPMFProperTVApproximable family) :
    ∃ kappa : Real, 0 < kappa ∧ ∀ horizon : Nat,
      ∃ law ∈ family, kappa <= stoppingLawLateOrNeverMass law horizon := by
  have hnotTight : ¬ IsPMFUniformlyFiniteTimeTight family := by
    intro htight
    exact hnot
      (isPMFProperTVApproximable_of_uniformlyFiniteTimeTight family htight)
  unfold IsPMFUniformlyFiniteTimeTight at hnotTight
  push Not at hnotTight
  exact hnotTight

end Probability
end Math
