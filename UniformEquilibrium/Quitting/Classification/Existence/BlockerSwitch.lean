/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Finset.PowersetBernoulliWeight
import MathUE.Topology.PoincareMirandaCube
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler

/-!
# Stationary equilibria from blocker switches

A blocker switch is a positive special class of finite quitting games.  Each
player has a designated opponent.  Conditional on that opponent continuing,
joining any background coalition is strictly better than a fixed baseline;
conditional on the opponent quitting, joining is weakly worse.  Players who
continue while somebody else quits receive exactly the baseline.

Poincare--Miranda produces a positive stationary hazard row at which every
pure-Quit endpoint equals the baseline.  Passive-continuation equalities make
the pure-Continue endpoints equal the same baseline.  The resulting
stationary profile is an exact terminal Nash profile against every behavioral
deviation and implements the baseline as a uniform-equilibrium payoff.

This is a source-data theorem for this special class.  It is not a producer
for arbitrary quitting games and does not construct a nonstationary
chronology.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open Math.Finset Math.Topology Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The raw weak-upper blocker-switch conditions at a baseline payoff.
The lower switch is strict; the upper switch may bind. -/
def IsQuittingBlockerSwitch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (blocker : Equiv.Perm ι) : Prop :=
  (∀ (S : {S : Finset ι // S.Nonempty}) (who : ι),
      who ∉ S.1 → reward S who = baseline who) ∧
    ∀ (who : ι) (background : Finset ι),
      who ∉ background → blocker who ∉ background →
        baseline who <
            reward ⟨insert who background, Finset.insert_nonempty _ _⟩ who ∧
          reward
              ⟨insert (blocker who) (insert who background),
                Finset.insert_nonempty _ _⟩ who ≤
            baseline who

/-- The strict-upper blocker-switch refinement. -/
def IsStrictQuittingBlockerSwitch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (blocker : Equiv.Perm ι) : Prop :=
  (∀ (S : {S : Finset ι // S.Nonempty}) (who : ι),
      who ∉ S.1 → reward S who = baseline who) ∧
    ∀ (who : ι) (background : Finset ι),
      who ∉ background → blocker who ∉ background →
        baseline who <
            reward ⟨insert who background, Finset.insert_nonempty _ _⟩ who ∧
          reward
              ⟨insert (blocker who) (insert who background),
                Finset.insert_nonempty _ _⟩ who <
            baseline who

omit [Fintype ι] in
/-- The blocker permutation is automatically fixed-point-free.  This need
not be included as a separate source hypothesis: at empty background, a
fixed point would make the strict lower and weak upper comparisons apply to
the same singleton reward. -/
theorem IsQuittingBlockerSwitch.blocker_ne
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {baseline : Payoff ι} {blocker : Equiv.Perm ι}
    (hswitch : IsQuittingBlockerSwitch reward baseline blocker) (who : ι) :
    blocker who ≠ who := by
  intro heq
  have h := hswitch.2 who ∅ (by simp) (by simp)
  have hupper :
      reward ⟨insert who (∅ : Finset ι), Finset.insert_nonempty _ _⟩ who ≤
        baseline who := by
    simpa only [heq, Finset.insert_idem] using h.2
  exact (not_lt_of_ge hupper) h.1

omit [Fintype ι] in
/-- Strict upper switches imply the weak-upper source predicate. -/
theorem IsStrictQuittingBlockerSwitch.toBlockerSwitch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {baseline : Payoff ι} {blocker : Equiv.Perm ι}
    (hswitch : IsStrictQuittingBlockerSwitch reward baseline blocker) :
    IsQuittingBlockerSwitch reward baseline blocker := by
  refine ⟨hswitch.1, fun who background hwho hblocker => ?_⟩
  exact ⟨(hswitch.2 who background hwho hblocker).1,
    (hswitch.2 who background hwho hblocker).2.le⟩

private def blockerBackground (who blocker : ι) : Finset ι :=
  (Finset.univ.erase who).erase blocker

private lemma erase_eq_insert_blockerBackground
    {who blocker : ι} (hne : blocker ≠ who) :
    Finset.univ.erase who = insert blocker (blockerBackground who blocker) := by
  ext other
  simp [blockerBackground, hne]

private lemma blocker_not_mem_background (who blocker : ι) :
    blocker ∉ blockerBackground who blocker := by
  simp [blockerBackground]

private lemma who_not_mem_blockerBackground (who blocker : ι) :
    who ∉ blockerBackground who blocker := by
  simp [blockerBackground]

omit [Fintype ι] in
private lemma bernoulliWeight_nonneg_of_mem_cube
    {x : ι → ℝ} (hx : x ∈ Icc (fun _ => 0) (fun _ => 1))
    (carrier subset : Finset ι) :
    0 ≤ bernoulliWeight x carrier subset := by
  exact mul_nonneg
    (Finset.prod_nonneg fun j _ => hx.1 j)
    (Finset.prod_nonneg fun j _ => sub_nonneg.mpr (hx.2 j))

omit [Fintype ι] in
private lemma exists_pos_bernoulliWeight_of_mem_cube
    {x : ι → ℝ} (hx : x ∈ Icc (fun _ => 0) (fun _ => 1))
    (carrier : Finset ι) :
    ∃ subset ∈ carrier.powerset, 0 < bernoulliWeight x carrier subset := by
  by_contra hnone
  push Not at hnone
  have hzero : ∀ subset ∈ carrier.powerset,
      bernoulliWeight x carrier subset = 0 := by
    intro subset hsubset
    exact le_antisymm (hnone subset hsubset)
      (bernoulliWeight_nonneg_of_mem_cube hx carrier subset)
  have hsum := sum_bernoulliWeight x carrier
  rw [Finset.sum_eq_zero hzero] at hsum
  norm_num at hsum

omit [Fintype ι] in
private lemma baseline_lt_weightedAverage
    {x : ι → ℝ} (hx : x ∈ Icc (fun _ => 0) (fun _ => 1))
    (carrier : Finset ι) (value : Finset ι → ℝ) (baseline : ℝ)
    (hvalue : ∀ subset ∈ carrier.powerset, baseline < value subset) :
    baseline <
      ∑ subset ∈ carrier.powerset,
        bernoulliWeight x carrier subset * value subset := by
  have hpositive :
      0 < ∑ subset ∈ carrier.powerset,
        bernoulliWeight x carrier subset * (value subset - baseline) := by
    obtain ⟨subset, hsubset, hweight⟩ :=
      exists_pos_bernoulliWeight_of_mem_cube hx carrier
    apply Finset.sum_pos'
    · intro other hother
      exact mul_nonneg
        (bernoulliWeight_nonneg_of_mem_cube hx carrier other)
        (sub_nonneg.mpr (hvalue other hother).le)
    · exact ⟨subset, hsubset,
        mul_pos hweight (sub_pos.mpr (hvalue subset hsubset))⟩
  have hmass := sum_bernoulliWeight x carrier
  calc
    baseline =
        ∑ subset ∈ carrier.powerset,
          bernoulliWeight x carrier subset * baseline := by
      rw [← Finset.sum_mul, hmass, one_mul]
    _ < ∑ subset ∈ carrier.powerset,
          bernoulliWeight x carrier subset * value subset := by
      rw [← sub_pos]
      simpa only [← Finset.sum_sub_distrib, ← mul_sub] using hpositive

omit [Fintype ι] in
private lemma weightedAverage_le_baseline
    {x : ι → ℝ} (hx : x ∈ Icc (fun _ => 0) (fun _ => 1))
    (carrier : Finset ι) (value : Finset ι → ℝ) (baseline : ℝ)
    (hvalue : ∀ subset ∈ carrier.powerset, value subset ≤ baseline) :
    (∑ subset ∈ carrier.powerset,
        bernoulliWeight x carrier subset * value subset) ≤ baseline := by
  calc
    (∑ subset ∈ carrier.powerset,
        bernoulliWeight x carrier subset * value subset) ≤
        ∑ subset ∈ carrier.powerset,
          bernoulliWeight x carrier subset * baseline := by
      apply Finset.sum_le_sum
      intro subset hsubset
      exact mul_le_mul_of_nonneg_left (hvalue subset hsubset)
        (bernoulliWeight_nonneg_of_mem_cube hx carrier subset)
    _ = baseline := by
      rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

omit [Fintype ι] in
private lemma weightedAverage_lt_baseline
    {x : ι → ℝ} (hx : x ∈ Icc (fun _ => 0) (fun _ => 1))
    (carrier : Finset ι) (value : Finset ι → ℝ) (baseline : ℝ)
    (hvalue : ∀ subset ∈ carrier.powerset, value subset < baseline) :
    (∑ subset ∈ carrier.powerset,
        bernoulliWeight x carrier subset * value subset) < baseline := by
  have h := baseline_lt_weightedAverage hx carrier
    (fun subset => -value subset) (-baseline)
    (fun subset hsubset => neg_lt_neg (hvalue subset hsubset))
  have hneg :
      (∑ subset ∈ carrier.powerset,
          bernoulliWeight x carrier subset * -value subset) =
        -(∑ subset ∈ carrier.powerset,
          bernoulliWeight x carrier subset * value subset) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro subset _
    ring
  rw [hneg] at h
  linarith

private lemma sigmaValue_blocker_face_zero
    (weight : Finset ι → ι → ℝ) (x : ι → ℝ) (who blocker : ι)
    (hne : blocker ≠ who) (hface : x blocker = 0) :
    sigmaValue weight x who =
      ∑ background ∈ (blockerBackground who blocker).powerset,
        bernoulliWeight x (blockerBackground who blocker) background *
          weight (insert who background) who := by
  unfold sigmaValue bernoulliWeight
  rw [erase_eq_insert_blockerBackground hne,
    Finset.sum_powerset_insert (blocker_not_mem_background who blocker)]
  have hblockerNotMem := blocker_not_mem_background who blocker
  have hsecondZero :
      (∑ background ∈ (blockerBackground who blocker).powerset,
        (∏ j ∈ insert blocker background, x j) *
          (∏ j ∈ insert blocker (blockerBackground who blocker) \ insert blocker background,
            (1 - x j)) * weight (insert who (insert blocker background)) who) = 0 := by
    apply Finset.sum_eq_zero
    intro background hbackground
    have hsubset := Finset.mem_powerset.mp hbackground
    have hblockerBackground : blocker ∉ background :=
      fun hmem => hblockerNotMem (hsubset hmem)
    rw [Finset.prod_insert hblockerBackground, hface]
    ring
  rw [hsecondZero, add_zero]
  apply Finset.sum_congr rfl
  intro background hbackground
  have hsubset := Finset.mem_powerset.mp hbackground
  have hblockerBackground : blocker ∉ background :=
    fun hmem => hblockerNotMem (hsubset hmem)
  have hsdiff : insert blocker (blockerBackground who blocker) \ background =
      insert blocker (blockerBackground who blocker \ background) := by
    ext other
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨hother | hother, hnot⟩
      · exact Or.inl hother
      · exact Or.inr ⟨hother, hnot⟩
    · rintro (hother | ⟨hother, hnot⟩)
      · exact ⟨Or.inl hother, hother ▸ hblockerBackground⟩
      · exact ⟨Or.inr hother, hnot⟩
  rw [hsdiff]
  rw [Finset.prod_insert]
  · simp [hface]
  · intro hmem
    exact hblockerNotMem (Finset.mem_sdiff.mp hmem).1

private lemma sigmaValue_blocker_face_one
    (weight : Finset ι → ι → ℝ) (x : ι → ℝ) (who blocker : ι)
    (hne : blocker ≠ who) (hface : x blocker = 1) :
    sigmaValue weight x who =
      ∑ background ∈ (blockerBackground who blocker).powerset,
        bernoulliWeight x (blockerBackground who blocker) background *
          weight (insert blocker (insert who background)) who := by
  unfold sigmaValue bernoulliWeight
  rw [erase_eq_insert_blockerBackground hne,
    Finset.sum_powerset_insert (blocker_not_mem_background who blocker)]
  have hblockerNotMem := blocker_not_mem_background who blocker
  have hfirstZero :
      (∑ background ∈ (blockerBackground who blocker).powerset,
        (∏ j ∈ background, x j) *
          (∏ j ∈ insert blocker (blockerBackground who blocker) \ background,
            (1 - x j)) * weight (insert who background) who) = 0 := by
    apply Finset.sum_eq_zero
    intro background hbackground
    have hsubset := Finset.mem_powerset.mp hbackground
    have hblockerBackground : blocker ∉ background :=
      fun hmem => hblockerNotMem (hsubset hmem)
    have hsdiff : insert blocker (blockerBackground who blocker) \ background =
        insert blocker (blockerBackground who blocker \ background) := by
      ext other
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨hother | hother, hnot⟩
        · exact Or.inl hother
        · exact Or.inr ⟨hother, hnot⟩
      · rintro (hother | ⟨hother, hnot⟩)
        · exact ⟨Or.inl hother, hother ▸ hblockerBackground⟩
        · exact ⟨Or.inr hother, hnot⟩
    rw [hsdiff]
    rw [Finset.prod_insert]
    · simp [hface]
    · intro hmem
      exact hblockerNotMem (Finset.mem_sdiff.mp hmem).1
  rw [hfirstZero, zero_add]
  apply Finset.sum_congr rfl
  intro background hbackground
  have hsubset := Finset.mem_powerset.mp hbackground
  have hblockerBackground : blocker ∉ background :=
    fun hmem => hblockerNotMem (hsubset hmem)
  rw [Finset.prod_insert hblockerBackground, hface, one_mul]
  have hsdiff :
      insert blocker (blockerBackground who blocker) \ insert blocker background =
        blockerBackground who blocker \ background := by
    ext other
    by_cases hother : other = blocker
    · subst other
      simp [hblockerNotMem]
    · simp [hother]
  rw [hsdiff, Finset.insert_comm blocker who]

/-! The public source-data theorems follow after the private finite-sum
adapter above. -/

private def blockerSwitchField
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (blocker : Equiv.Perm ι)
    (hazard : ι → ℝ) (coordinate : ι) : ℝ :=
  sigmaValue (weightOfReward reward) hazard (blocker.symm coordinate) -
    baseline (blocker.symm coordinate)

private lemma continuous_blockerSwitchField
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (blocker : Equiv.Perm ι) :
    Continuous (blockerSwitchField reward baseline blocker) := by
  apply continuous_pi
  intro coordinate
  exact (continuous_sigmaValue (weightOfReward reward) (blocker.symm coordinate)).sub
    continuous_const

private lemma blockerSwitchField_lower_face_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {baseline : Payoff ι} {blocker : Equiv.Perm ι}
    (hswitch : IsQuittingBlockerSwitch reward baseline blocker)
    (hazard : ι → ℝ) (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (coordinate : ι) (hface : hazard coordinate = 0) :
    0 < blockerSwitchField reward baseline blocker hazard coordinate := by
  let who := blocker.symm coordinate
  have hblocker : blocker who = coordinate := blocker.apply_symm_apply coordinate
  have hne : blocker who ≠ who := hswitch.blocker_ne who
  rw [blockerSwitchField]
  rw [sigmaValue_blocker_face_zero (weightOfReward reward) hazard who
    (blocker who) hne (hblocker ▸ hface)]
  apply sub_pos.mpr
  apply baseline_lt_weightedAverage hhazard
  intro background hbackground
  have hsubset := Finset.mem_powerset.mp hbackground
  have hwho : who ∉ background :=
    fun hmem => who_not_mem_blockerBackground who (blocker who) (hsubset hmem)
  have hblockerMem : blocker who ∉ background :=
    fun hmem => blocker_not_mem_background who (blocker who) (hsubset hmem)
  simpa [weightOfReward] using (hswitch.2 who background hwho hblockerMem).1

private lemma blockerSwitchField_upper_face_nonpos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {baseline : Payoff ι} {blocker : Equiv.Perm ι}
    (hswitch : IsQuittingBlockerSwitch reward baseline blocker)
    (hazard : ι → ℝ) (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (coordinate : ι) (hface : hazard coordinate = 1) :
    blockerSwitchField reward baseline blocker hazard coordinate ≤ 0 := by
  let who := blocker.symm coordinate
  have hblocker : blocker who = coordinate := blocker.apply_symm_apply coordinate
  have hne : blocker who ≠ who := hswitch.blocker_ne who
  rw [blockerSwitchField]
  rw [sigmaValue_blocker_face_one (weightOfReward reward) hazard who
    (blocker who) hne (hblocker ▸ hface)]
  apply sub_nonpos.mpr
  apply weightedAverage_le_baseline hhazard
  intro background hbackground
  have hsubset := Finset.mem_powerset.mp hbackground
  have hwho : who ∉ background :=
    fun hmem => who_not_mem_blockerBackground who (blocker who) (hsubset hmem)
  have hblockerMem : blocker who ∉ background :=
    fun hmem => blocker_not_mem_background who (blocker who) (hsubset hmem)
  simpa [weightOfReward] using (hswitch.2 who background hwho hblockerMem).2

private lemma strictBlockerSwitchField_upper_face_neg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {baseline : Payoff ι} {blocker : Equiv.Perm ι}
    (hswitch : IsStrictQuittingBlockerSwitch reward baseline blocker)
    (hazard : ι → ℝ) (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (coordinate : ι) (hface : hazard coordinate = 1) :
    blockerSwitchField reward baseline blocker hazard coordinate < 0 := by
  let who := blocker.symm coordinate
  have hweak := hswitch.toBlockerSwitch
  have hblocker : blocker who = coordinate := blocker.apply_symm_apply coordinate
  have hne : blocker who ≠ who := hweak.blocker_ne who
  rw [blockerSwitchField]
  rw [sigmaValue_blocker_face_one (weightOfReward reward) hazard who
    (blocker who) hne (hblocker ▸ hface)]
  apply sub_neg.mpr
  apply weightedAverage_lt_baseline hhazard
  intro background hbackground
  have hsubset := Finset.mem_powerset.mp hbackground
  have hwho : who ∉ background :=
    fun hmem => who_not_mem_blockerBackground who (blocker who) (hsubset hmem)
  have hblockerMem : blocker who ∉ background :=
    fun hmem => blocker_not_mem_background who (blocker who) (hsubset hmem)
  simpa [weightOfReward] using (hswitch.2 who background hwho hblockerMem).2

/-- A weak-upper blocker switch has a positive hazard row at which every
player's pure-Quit endpoint is exactly the prescribed baseline.  Coordinates
may equal one when an upper-face switch binds. -/
theorem exists_positive_hazard_sigmaValue_eq_baseline_of_blockerSwitch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (blocker : Equiv.Perm ι)
    (hswitch : IsQuittingBlockerSwitch reward baseline blocker) :
    ∃ hazard : ι → ℝ,
      (∀ who, 0 ≤ hazard who) ∧ (∀ who, hazard who ≤ 1) ∧
        (∀ who, 0 < hazard who) ∧
          ∀ who, sigmaValue (weightOfReward reward) hazard who = baseline who := by
  obtain ⟨hazard, hhazard, hpositive, hzero⟩ :=
    exists_cube_zero_pos_of_opposite_face_signs
      (blockerSwitchField reward baseline blocker)
      (continuous_blockerSwitchField reward baseline blocker)
      (blockerSwitchField_lower_face_pos hswitch)
      (blockerSwitchField_upper_face_nonpos hswitch)
  refine ⟨hazard, hhazard.1, hhazard.2, hpositive, fun who => ?_⟩
  have hwho := hzero (blocker who)
  simp only [blockerSwitchField, blocker.symm_apply_apply] at hwho
  linarith

/-- Under strict switches on both faces, the common endpoint root can be
chosen fully mixed. -/
theorem exists_interior_hazard_sigmaValue_eq_baseline_of_strictBlockerSwitch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (blocker : Equiv.Perm ι)
    (hswitch : IsStrictQuittingBlockerSwitch reward baseline blocker) :
    ∃ hazard : ι → ℝ,
      (∀ who, 0 < hazard who) ∧ (∀ who, hazard who < 1) ∧
        ∀ who, sigmaValue (weightOfReward reward) hazard who = baseline who := by
  let hweak := hswitch.toBlockerSwitch
  obtain ⟨hazard, _hhazard, hinterior, hzero⟩ :=
    exists_cube_zero_interior_of_strict_opposite_face_signs
      (blockerSwitchField reward baseline blocker)
      (continuous_blockerSwitchField reward baseline blocker)
      (blockerSwitchField_lower_face_pos hweak)
      (strictBlockerSwitchField_upper_face_neg hswitch)
  refine ⟨hazard, fun who => (hinterior who).1,
    fun who => (hinterior who).2, fun who => ?_⟩
  have hwho := hzero (blocker who)
  simp only [blockerSwitchField, blocker.symm_apply_apply] at hwho
  linarith

private lemma gammaValue_eq_baseline_of_passive
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {baseline : Payoff ι}
    (hpassive : ∀ (S : {S : Finset ι // S.Nonempty}) (who : ι),
      who ∉ S.1 → reward S who = baseline who)
    (hazard : ι → ℝ) (who : ι) :
    gammaValue (weightOfReward reward) hazard who (baseline who) =
      baseline who := by
  let carrier := Finset.univ.erase who
  have hreward : ∀ background ∈ carrier.powerset.erase ∅,
      weightOfReward reward background who = baseline who := by
    intro background hbackground
    have hpow := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hbackground)
    have hnonempty : background.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hbackground)
    have hwho : who ∉ background := fun hmem =>
      (Finset.ne_of_mem_erase (hpow hmem)) rfl
    simpa [weightOfReward, hnonempty] using
      hpassive ⟨background, hnonempty⟩ who hwho
  have hsumReward :
      (∑ background ∈ carrier.powerset.erase ∅,
        bernoulliWeight hazard carrier background *
          weightOfReward reward background who) =
        (∑ background ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier background) * baseline who := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro background hbackground
    rw [hreward background hbackground]
  have hempty : (∅ : Finset ι) ∈ carrier.powerset :=
    Finset.empty_mem_powerset _
  have hmass :
      (∑ background ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier background) +
        continueMassExcl hazard who = 1 := by
    have htotal := sum_bernoulliWeight hazard carrier
    have hsplit := Finset.sum_erase_add carrier.powerset
      (fun background => bernoulliWeight hazard carrier background) hempty
    have hemptyWeight :
        bernoulliWeight hazard carrier ∅ = continueMassExcl hazard who := by
      simp [bernoulliWeight, continueMassExcl, carrier]
    rw [hemptyWeight] at hsplit
    linarith
  unfold gammaValue excludedValue
  change
    (∑ background ∈ carrier.powerset.erase ∅,
      bernoulliWeight hazard carrier background *
        weightOfReward reward background who) +
      continueMassExcl hazard who * baseline who = baseline who
  rw [hsumReward]
  calc
    (∑ background ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier background) * baseline who +
        continueMassExcl hazard who * baseline who =
      ((∑ background ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier background) +
        continueMassExcl hazard who) * baseline who := by ring
    _ = baseline who := by rw [hmass, one_mul]

/-- The complete stationary certificate produced by a blocker switch. -/
structure QuittingBlockerSwitchStationaryCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) where
  hazard : ι → ℝ
  hazard_nonneg : ∀ who, 0 ≤ hazard who
  hazard_le_one : ∀ who, hazard who ≤ 1
  hazard_pos : ∀ who, 0 < hazard who
  sigmaValue_eq : ∀ who,
    sigmaValue (weightOfReward reward) hazard who = baseline who
  quitEndpoint_eq : ∀ who,
    quittingRootQuitPayoff reward baseline
      (rootOfHazard hazard hazard_nonneg hazard_le_one) who = baseline who
  continueEndpoint_eq : ∀ who,
    quittingRootContinuePayoff reward baseline
      (rootOfHazard hazard hazard_nonneg hazard_le_one) who = baseline who
  fixedPoint : baseline = quittingRootSuccessorPayoff reward baseline
    (rootOfHazard hazard hazard_nonneg hazard_le_one)
  endpointNash : IsεQuittingRootEndpointNash reward baseline 0
    (rootOfHazard hazard hazard_nonneg hazard_le_one)
  jointlyContracts : quittingStationaryContinueMass
    (rootOfHazard hazard hazard_nonneg hazard_le_one) < 1
  opponentsContract : ∀ who,
    quittingStationaryFixedOpponentsContinueMass
      (rootOfHazard hazard hazard_nonneg hazard_le_one) who < 1
  terminalPayoff_eq : quittingTerminalPayoff reward
    (quittingStationaryProfile reward
      (rootOfHazard hazard hazard_nonneg hazard_le_one)) = baseline
  terminalNash : (quittingGame reward).IsεAsymptoticNash
    (quittingTerminalPayoff reward) 0
    (quittingStationaryProfile reward
      (rootOfHazard hazard hazard_nonneg hazard_le_one))
  uniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none baseline

/-- A blocker switch produces a positive stationary exact equilibrium at the
prescribed baseline.  Exact terminal Nash quantifies over every unilateral
behavioral deviation. -/
theorem exists_stationaryCertificate_of_blockerSwitch [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (blocker : Equiv.Perm ι)
    (hswitch : IsQuittingBlockerSwitch reward baseline blocker) :
    Nonempty (QuittingBlockerSwitchStationaryCertificate reward baseline) := by
  obtain ⟨hazard, hnonneg, hleOne, hpos, hsigma⟩ :=
    exists_positive_hazard_sigmaValue_eq_baseline_of_blockerSwitch
      reward baseline blocker hswitch
  let root := rootOfHazard hazard hnonneg hleOne
  have hquit : ∀ who,
      quittingRootQuitPayoff reward baseline root who = baseline who := by
    intro who
    rw [quittingRootQuitPayoff_eq_sigmaValue]
    simpa [root] using hsigma who
  have hcontinue : ∀ who,
      quittingRootContinuePayoff reward baseline root who = baseline who := by
    intro who
    rw [quittingRootContinuePayoff_eq_gammaValue]
    rw [show hazardOfRoot root = hazard by simp [root]]
    exact gammaValue_eq_baseline_of_passive hswitch.1 hazard who
  have hfixed : baseline = quittingRootSuccessorPayoff reward baseline root := by
    funext who
    rw [quittingRootSuccessorPayoff_eq_endpointMix,
      hquit who, hcontinue who]
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    calc
      baseline who =
          ((root who false).toReal + (root who true).toReal) * baseline who := by
        rw [hsum, one_mul]
      _ = (root who true).toReal * baseline who +
          (root who false).toReal * baseline who := by ring
  have hendpoint : IsεQuittingRootEndpointNash reward baseline 0 root := by
    intro who
    simp [quittingRootEndpointDifference, hquit who, hcontinue who]
  have hjoint : quittingStationaryContinueMass root < 1 := by
    let who : ι := Classical.choice (inferInstance : Nonempty ι)
    calc
      quittingStationaryContinueMass root ≤ (root who false).toReal :=
        quittingStationaryContinueMass_le_ownContinueProbability root who
      _ < 1 := by
        simp [root, rootOfHazard, hpos who]
  have hne : ∀ who, blocker who ≠ who := hswitch.blocker_ne
  have hopponents : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    intro who
    unfold quittingStationaryFixedOpponentsContinueMass
    calc
      quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) ≤
          (Function.update root who (PMF.pure false) (blocker who) false).toReal :=
        quittingStationaryContinueMass_le_ownContinueProbability _ (blocker who)
      _ = (root (blocker who) false).toReal := by
        rw [Function.update_of_ne (hne who)]
      _ < 1 := by
        simp [root, rootOfHazard, hpos (blocker who)]
  have hterminal := quittingTerminalPayoff_stationary_eq_of_fixedPoint
    reward root baseline hjoint hfixed
  have hnash :=
    isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
      reward root baseline hjoint hfixed hendpoint hopponents
  have huniform :=
    isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
      reward root baseline hjoint hfixed hendpoint hopponents
  exact ⟨{
    hazard := hazard
    hazard_nonneg := hnonneg
    hazard_le_one := hleOne
    hazard_pos := hpos
    sigmaValue_eq := hsigma
    quitEndpoint_eq := hquit
    continueEndpoint_eq := hcontinue
    fixedPoint := hfixed
    endpointNash := hendpoint
    jointlyContracts := hjoint
    opponentsContract := hopponents
    terminalPayoff_eq := hterminal
    terminalNash := hnash
    uniformEquilibriumPayoff := huniform }⟩

/-- Headline existence consequence of the blocker-switch source conditions. -/
theorem isUniformEquilibriumPayoff_of_blockerSwitch [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (blocker : Equiv.Perm ι)
    (hswitch : IsQuittingBlockerSwitch reward baseline blocker) :
    (quittingGame reward).IsUniformEquilibriumPayoff none baseline := by
  exact (exists_stationaryCertificate_of_blockerSwitch
    reward baseline blocker hswitch).some.uniformEquilibriumPayoff

/-- Strict upper switches refine the stationary certificate to a fully mixed
hazard row. -/
theorem exists_stationaryCertificate_interior_of_strictBlockerSwitch
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (blocker : Equiv.Perm ι)
    (hswitch : IsStrictQuittingBlockerSwitch reward baseline blocker) :
    ∃ certificate : QuittingBlockerSwitchStationaryCertificate reward baseline,
      ∀ who, certificate.hazard who < 1 := by
  obtain ⟨hazard, hpos, hltOne, hsigma⟩ :=
    exists_interior_hazard_sigmaValue_eq_baseline_of_strictBlockerSwitch
      reward baseline blocker hswitch
  have hnonneg : ∀ who, 0 ≤ hazard who := fun who => (hpos who).le
  have hleOne : ∀ who, hazard who ≤ 1 := fun who => (hltOne who).le
  let root := rootOfHazard hazard hnonneg hleOne
  have hweak := hswitch.toBlockerSwitch
  have hquit : ∀ who,
      quittingRootQuitPayoff reward baseline root who = baseline who := by
    intro who
    rw [quittingRootQuitPayoff_eq_sigmaValue]
    simpa [root] using hsigma who
  have hcontinue : ∀ who,
      quittingRootContinuePayoff reward baseline root who = baseline who := by
    intro who
    rw [quittingRootContinuePayoff_eq_gammaValue]
    rw [show hazardOfRoot root = hazard by simp [root]]
    exact gammaValue_eq_baseline_of_passive hswitch.1 hazard who
  have hfixed : baseline = quittingRootSuccessorPayoff reward baseline root := by
    funext who
    rw [quittingRootSuccessorPayoff_eq_endpointMix,
      hquit who, hcontinue who]
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    calc
      baseline who =
          ((root who false).toReal + (root who true).toReal) * baseline who := by
        rw [hsum, one_mul]
      _ = (root who true).toReal * baseline who +
          (root who false).toReal * baseline who := by ring
  have hendpoint : IsεQuittingRootEndpointNash reward baseline 0 root := by
    intro who
    simp [quittingRootEndpointDifference, hquit who, hcontinue who]
  have hjoint : quittingStationaryContinueMass root < 1 := by
    let who : ι := Classical.choice (inferInstance : Nonempty ι)
    calc
      quittingStationaryContinueMass root ≤ (root who false).toReal :=
        quittingStationaryContinueMass_le_ownContinueProbability root who
      _ < 1 := by simp [root, rootOfHazard, hpos who]
  have hne : ∀ who, blocker who ≠ who := hweak.blocker_ne
  have hopponents : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    intro who
    unfold quittingStationaryFixedOpponentsContinueMass
    calc
      quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) ≤
          (Function.update root who (PMF.pure false) (blocker who) false).toReal :=
        quittingStationaryContinueMass_le_ownContinueProbability _ (blocker who)
      _ = (root (blocker who) false).toReal := by
        rw [Function.update_of_ne (hne who)]
      _ < 1 := by simp [root, rootOfHazard, hpos (blocker who)]
  have hterminal := quittingTerminalPayoff_stationary_eq_of_fixedPoint
    reward root baseline hjoint hfixed
  have hnash :=
    isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
      reward root baseline hjoint hfixed hendpoint hopponents
  have huniform :=
    isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
      reward root baseline hjoint hfixed hendpoint hopponents
  exact ⟨{
    hazard := hazard
    hazard_nonneg := hnonneg
    hazard_le_one := hleOne
    hazard_pos := hpos
    sigmaValue_eq := hsigma
    quitEndpoint_eq := hquit
    continueEndpoint_eq := hcontinue
    fixedPoint := hfixed
    endpointNash := hendpoint
    jointlyContracts := hjoint
    opponentsContract := hopponents
    terminalPayoff_eq := hterminal
    terminalNash := hnash
    uniformEquilibriumPayoff := huniform }, hltOne⟩

end GameTheory
