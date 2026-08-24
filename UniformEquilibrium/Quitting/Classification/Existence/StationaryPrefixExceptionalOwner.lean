/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.StationaryPrefixDeletedClockCompactification
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedPositiveLiveLimit
import UniformEquilibrium.Quitting.Terminal.TargetTail.DiagonalTargetTailSelection

/-!
# Exceptional owner at the stationary-prefix boundary

The stationary-prefix source family retains two horizon-scale quantities that
are invisible to fixed-depth compactification: joint survival through the
whole repeated prefix and every player-deleted survival through that prefix.

After subselection, either joint survival has a positive limit, or it vanishes.
In the vanishing case, the multiplicative two-clock inequality shows that at
most one player-deleted clock can survive.  If that last clock also vanishes,
the checked deleted-clock transport produces the stationary branch.  Otherwise
one fixed exceptional owner has positive deleted survival while every other
player-deleted clock vanishes.

This is an actual-source trichotomy.  The positive-joint-reach arm still needs
an endpoint attachment theorem, while the unique-owner arm still needs a
stationary repair or a source-matched absorbing sequence.  Neither output is
silently treated as an equilibrium branch.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Joint survival through every repeated row of one selected prefix. -/
def QuittingDiffuseStationaryPrefixFamily.prefixJointSurvival
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward) (index : ℕ) : ℝ :=
  quittingJointSurvivalWeight (fun _ ↦ family.root index) 0
    (family.horizon index + 1)

/-- A player's deleted survival through every repeated row of one selected
prefix. -/
def QuittingDiffuseStationaryPrefixFamily.prefixDeletedSurvival
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (index : ℕ) (who : ι) : ℝ :=
  quittingOpponentSurvivalWeight (fun _ ↦ family.root index) who 0
    (family.horizon index + 1)

theorem QuittingDiffuseStationaryPrefixFamily.prefixJointSurvival_mem_Icc
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward) (index : ℕ) :
    family.prefixJointSurvival index ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨quittingJointSurvivalWeight_nonneg _ 0 _,
    quittingJointSurvivalWeight_le_one _ 0 _⟩

theorem QuittingDiffuseStationaryPrefixFamily.prefixDeletedSurvival_mem_Icc
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (index : ℕ) (who : ι) :
    family.prefixDeletedSurvival index who ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨quittingOpponentSurvivalWeight_nonneg _ who 0 _,
    quittingOpponentSurvivalWeight_le_one _ who 0 _⟩

/-- When whole-prefix joint survival vanishes, either all deleted clocks
vanish along one source subsequence and hence produce `S.1`, or one fixed
owner is the unique possible nonvanishing deleted clock. -/
theorem stationary_or_exists_uniqueExceptionalOwner_of_prefixJointSurvival_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence)
    (hjoint : Tendsto
      (fun n ↦ family.prefixJointSurvival (subsequence n)) atTop (nhds 0)) :
    QuittingStationaryεEquilibriumExistence reward ∨
      ∃ (owner : ι) (selected : ℕ → ℕ) (deletedLimit : ℝ),
        StrictMono selected ∧
          0 < deletedLimit ∧
          Tendsto (fun n ↦ family.prefixJointSurvival (selected n))
            atTop (nhds 0) ∧
          Tendsto (fun n ↦ family.prefixDeletedSurvival (selected n) owner)
            atTop (nhds deletedLimit) ∧
          ∀ other, other ≠ owner →
            Tendsto
              (fun n ↦ family.prefixDeletedSurvival (selected n) other)
              atTop (nhds 0) := by
  letI : Nonempty ι := ⟨family.punished 0⟩
  let threshold : ℕ → ℝ := fun n ↦
    Real.sqrt (family.prefixJointSurvival (subsequence n))
  have hthreshold : Tendsto threshold atTop (nhds 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hjoint
    simpa only [threshold, Function.comp_def, Real.sqrt_zero] using hsqrt
  have htarget : ∀ n, ∃ target : ι, ∀ who, who ≠ target →
      family.prefixDeletedSurvival (subsequence n) who ≤ threshold n := by
    intro n
    apply exists_target_forall_opponentSurvivalWeight_le_of_joint_le_sq
      (roots := fun _ ↦ family.root (subsequence n))
      (cutoff := family.horizon (subsequence n) + 1)
    · exact Real.sqrt_nonneg _
    · change family.prefixJointSurvival (subsequence n) ≤ threshold n ^ 2
      rw [Real.sq_sqrt (family.prefixJointSurvival_mem_Icc _).1]
  choose target htargetBound using htarget
  obtain ⟨owner, targetSubsequence, htargetSubsequence, htargetFixed⟩ :=
    exists_fixedPlayer_strictMono_subsequence target
  let firstSelected := subsequence ∘ targetSubsequence
  have hfirstSelected : StrictMono firstSelected :=
    hsubsequence.comp htargetSubsequence
  have hotherZero : ∀ other, other ≠ owner → Tendsto
      (fun n ↦ family.prefixDeletedSurvival (firstSelected n) other)
      atTop (nhds 0) := by
    intro other hother
    apply squeeze_zero
    · intro n
      exact (family.prefixDeletedSurvival_mem_Icc _ _).1
    · intro n
      exact htargetBound (targetSubsequence n) other
        (fun heq ↦ hother (heq.trans (htargetFixed n)))
    · exact hthreshold.comp htargetSubsequence.tendsto_atTop
  let ownerClock : ℕ → ℝ := fun n ↦
    family.prefixDeletedSurvival (firstSelected n) owner
  have hownerClockMem : ∀ n, ownerClock n ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    exact family.prefixDeletedSurvival_mem_Icc _ _
  obtain ⟨deletedLimit, hdeletedLimitMem, clockSubsequence,
      hclockSubsequence, hownerClock⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).tendsto_subseq
      hownerClockMem
  let selected := firstSelected ∘ clockSubsequence
  have hselected : StrictMono selected :=
    hfirstSelected.comp hclockSubsequence
  have hjointSelected : Tendsto
      (fun n ↦ family.prefixJointSurvival (selected n)) atTop (nhds 0) := by
    exact hjoint.comp
      (htargetSubsequence.comp hclockSubsequence).tendsto_atTop
  have hotherSelected : ∀ other, other ≠ owner → Tendsto
      (fun n ↦ family.prefixDeletedSurvival (selected n) other)
      atTop (nhds 0) := by
    intro other hother
    exact (hotherZero other hother).comp hclockSubsequence.tendsto_atTop
  have hownerSelected : Tendsto
      (fun n ↦ family.prefixDeletedSurvival (selected n) owner)
      atTop (nhds deletedLimit) := by
    simpa [ownerClock, selected, firstSelected, Function.comp_def] using
      hownerClock
  rcases eq_or_lt_of_le hdeletedLimitMem.1 with hdeletedZero | hdeletedPositive
  · left
    apply quittingStationaryεEquilibriumExistence_of_stationaryPrefix_deletedClocks
      family selected hselected
    intro who
    by_cases hwho : who = owner
    · subst who
      simpa only [QuittingDiffuseStationaryPrefixFamily.prefixDeletedSurvival,
        hdeletedZero] using hownerSelected
    · exact hotherSelected who hwho
  · exact Or.inr ⟨owner, selected, deletedLimit, hselected,
      hdeletedPositive, hjointSelected, hownerSelected, hotherSelected⟩

/-- Every source subsequence has exactly one of three horizon-scale outcomes:
the stationary branch, positive limiting reach of the actual punishment
suffix, or one unique exceptional player-deleted clock over vanishing joint
survival. -/
theorem stationary_or_positivePrefixJointReach_or_uniqueExceptionalOwner
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence) :
    QuittingStationaryεEquilibriumExistence reward ∨
      (∃ (selected : ℕ → ℕ) (jointLimit : ℝ),
        StrictMono selected ∧
          0 < jointLimit ∧
          Tendsto (fun n ↦ family.prefixJointSurvival (selected n))
            atTop (nhds jointLimit)) ∨
      ∃ (owner : ι) (selected : ℕ → ℕ) (deletedLimit : ℝ),
        StrictMono selected ∧
          0 < deletedLimit ∧
          Tendsto (fun n ↦ family.prefixJointSurvival (selected n))
            atTop (nhds 0) ∧
          Tendsto (fun n ↦ family.prefixDeletedSurvival (selected n) owner)
            atTop (nhds deletedLimit) ∧
          ∀ other, other ≠ owner →
            Tendsto
              (fun n ↦ family.prefixDeletedSurvival (selected n) other)
              atTop (nhds 0) := by
  have hjointMem : ∀ n,
      family.prefixJointSurvival (subsequence n) ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    exact family.prefixJointSurvival_mem_Icc _
  obtain ⟨jointLimit, hjointLimitMem, jointSubsequence,
      hjointSubsequence, hjointLimit⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).tendsto_subseq hjointMem
  let selected := subsequence ∘ jointSubsequence
  have hselected : StrictMono selected :=
    hsubsequence.comp hjointSubsequence
  have hjointSelected : Tendsto
      (fun n ↦ family.prefixJointSurvival (selected n))
      atTop (nhds jointLimit) := by
    simpa [selected, Function.comp_def] using hjointLimit
  rcases eq_or_lt_of_le hjointLimitMem.1 with hjointZero | hjointPositive
  · have hzero : Tendsto
        (fun n ↦ family.prefixJointSurvival (selected n))
        atTop (nhds 0) := by
      simpa only [hjointZero] using hjointSelected
    rcases
        stationary_or_exists_uniqueExceptionalOwner_of_prefixJointSurvival_tendsto_zero
          family selected hselected hzero with hstationary | hexceptional
    · exact Or.inl hstationary
    · exact Or.inr (Or.inr hexceptional)
  · exact Or.inr (Or.inl ⟨selected, jointLimit, hselected,
      hjointPositive, hjointSelected⟩)

/-- The positive-live, divergent-horizon source regime is reduced to two
checked paper branches and two horizon-scale seams.  A limiting root with
positive absorption gives the well-supported branch.  At the all-Continue
boundary, the remaining source data are exactly positive reach of the actual
punishment suffix or one unique exceptional deleted-clock owner. -/
theorem
    stationary_or_wellSupported_or_positiveJointReach_or_uniqueExceptionalOwner_of_positiveLive
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (subsequence : ℕ → ℕ) (punished : ι) (liveLimit : ℝ)
    (hsubsequence : StrictMono subsequence)
    (hpunished : ∀ n, family.punished (subsequence n) = punished)
    (hlivePositive : 0 < liveLimit)
    (hlive : Tendsto
      (fun n ↦ quittingStationaryContinueMass (family.root (subsequence n)))
      atTop (nhds liveLimit))
    (hhorizon : Tendsto (fun n ↦ family.horizon (subsequence n)) atTop atTop) :
    QuittingStationaryεEquilibriumExistence reward ∨
      QuittingWellSupportedAbsorbingSequenceExistence reward ∨
      (∃ (selected : ℕ → ℕ) (jointLimit : ℝ),
        StrictMono selected ∧
          0 < jointLimit ∧
          Tendsto (fun n ↦ family.prefixJointSurvival (selected n))
            atTop (nhds jointLimit)) ∨
      ∃ (owner : ι) (selected : ℕ → ℕ) (deletedLimit : ℝ),
        StrictMono selected ∧
          0 < deletedLimit ∧
          Tendsto (fun n ↦ family.prefixJointSurvival (selected n))
            atTop (nhds 0) ∧
          Tendsto (fun n ↦ family.prefixDeletedSurvival (selected n) owner)
            atTop (nhds deletedLimit) ∧
          ∀ other, other ≠ owner →
            Tendsto
              (fun n ↦ family.prefixDeletedSurvival (selected n) other)
              atTop (nhds 0) := by
  have hliveLe : liveLimit ≤ 1 := by
    apply le_of_tendsto hlive
    exact Filter.Eventually.of_forall fun n ↦
      quittingStationaryContinueMass_le_one (family.root (subsequence n))
  rcases lt_or_eq_of_le hliveLe with hliveStrict | hliveOne
  · obtain ⟨limit, hlimitMass⟩ :=
      exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq
        family subsequence punished liveLimit hsubsequence hpunished
          hlivePositive hlive hhorizon
    have hlimitStrict : limit.liveMass < 1 := by
      rwa [hlimitMass]
    exact Or.inr (Or.inl (limit.wellSupported_of_lt_one hlimitStrict))
  · rcases
        stationary_or_positivePrefixJointReach_or_uniqueExceptionalOwner
          family subsequence hsubsequence with
      hstationary | hpositive | hexceptional
    · exact Or.inl hstationary
    · exact Or.inr (Or.inr (Or.inl hpositive))
    · exact Or.inr (Or.inr (Or.inr hexceptional))

end GameTheory
