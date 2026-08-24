/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.DiffuseStationaryPrefixSourceAttachments

/-!
# One-row hazards of a divergent exceptional-owner source

The raw unique-exceptional-owner source permits bounded prefix horizons and
therefore does not force singleton concentration.  This file isolates what
the additional divergent-horizon datum does force.  Positive survival of the
owner-deleted repeated prefix makes the opponents' one-row Continue mass tend
to one.  Vanishing survival of the full prefix makes the exceptional owner's
one-row Quit probability eventually positive.

These are the two probabilistic root hypotheses used by the existing
exceptional solo-stationary fallback.  No tail Nash or payoff-concentration
claim is made here.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Reindex an actual stationary-prefix family along a strict source
subsequence.  All behavioral witnesses are retained literally. -/
def QuittingDiffuseStationaryPrefixFamily.reindex
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (selected : ℕ → ℕ) (hselected : StrictMono selected) :
    QuittingDiffuseStationaryPrefixFamily reward where
  error := fun n ↦ family.error (selected n)
  root := fun n ↦ family.root (selected n)
  horizon := fun n ↦ family.horizon (selected n)
  punished := fun n ↦ family.punished (selected n)
  punishment := fun n ↦ family.punishment (selected n)
  error_pos := fun n ↦ family.error_pos (selected n)
  error_tendsto_zero :=
    family.error_tendsto_zero.comp hselected.tendsto_atTop
  horizon_gt_one := fun n ↦ family.horizon_gt_one (selected n)
  punishmentWithin := fun n ↦ family.punishmentWithin (selected n)
  nash := fun n ↦ family.nash (selected n)
  live_pos := fun n ↦ family.live_pos (selected n)

/-- Reindexing is definitionally transparent on prefix horizons. -/
@[simp] theorem QuittingDiffuseStationaryPrefixFamily.horizon_reindex
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (selected : ℕ → ℕ) (hselected : StrictMono selected) (n : ℕ) :
    (family.reindex selected hselected).horizon n =
      family.horizon (selected n) := rfl

/-- Reindexing is definitionally transparent on roots. -/
@[simp] theorem QuittingDiffuseStationaryPrefixFamily.root_reindex
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (selected : ℕ → ℕ) (hselected : StrictMono selected) (n : ℕ) :
    (family.reindex selected hselected).root n = family.root (selected n) := rfl

/-- Reindexing is definitionally transparent on punished-player labels. -/
@[simp] theorem QuittingDiffuseStationaryPrefixFamily.punished_reindex
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (selected : ℕ → ℕ) (hselected : StrictMono selected) (n : ℕ) :
    (family.reindex selected hselected).punished n =
      family.punished (selected n) := rfl

/-- The positive-live divergent-horizon source split can be stated without
discarding horizon divergence.  The two residual source structures use the
literal reindexed family, and their further selections still have horizons
tending to infinity. -/
theorem
    stationary_or_wellSupported_or_divergentPositiveJoint_or_divergentExceptional
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (subsequence : ℕ → ℕ) (punished : ι) (liveLimit : ℝ)
    (hsubsequence : StrictMono subsequence)
    (hpunished : ∀ n, family.punished (subsequence n) = punished)
    (hlivePositive : 0 < liveLimit)
    (hlive : Tendsto
      (fun n ↦ quittingStationaryContinueMass (family.root (subsequence n)))
      atTop (nhds liveLimit))
    (hhorizon : Tendsto
      (fun n ↦ family.horizon (subsequence n)) atTop atTop) :
    QuittingStationaryεEquilibriumExistence reward ∨
      QuittingWellSupportedAbsorbingSequenceExistence reward ∨
      (∃ source : QuittingPositiveJointPrefixReachSource reward,
        Tendsto (fun n ↦ source.family.horizon (source.selected n))
          atTop atTop) ∨
      ∃ source : QuittingUniqueExceptionalOwnerSource reward,
        Tendsto (fun n ↦ source.family.horizon (source.selected n))
          atTop atTop := by
  let reindexed := family.reindex subsequence hsubsequence
  have hpunished' : ∀ n, reindexed.punished n = punished := by
    intro n
    exact hpunished n
  have hlive' : Tendsto
      (fun n ↦ quittingStationaryContinueMass (reindexed.root n))
      atTop (nhds liveLimit) := by
    simpa [reindexed] using hlive
  have hhorizon' : Tendsto reindexed.horizon atTop atTop := by
    change Tendsto (fun n ↦ family.horizon (subsequence n)) atTop atTop
    exact hhorizon
  rcases
      stationary_or_wellSupported_or_positiveJointReach_or_uniqueExceptionalOwner_of_positiveLive
        reindexed id punished liveLimit strictMono_id hpunished'
          hlivePositive hlive' hhorizon' with
    hstationary | hwellSupported | hpositive | hexceptional
  · exact Or.inl hstationary
  · exact Or.inr (Or.inl hwellSupported)
  · obtain ⟨selected, jointLimit, hselected, hlimitPositive, hlimit⟩ :=
      hpositive
    let source : QuittingPositiveJointPrefixReachSource reward :=
      ⟨reindexed, selected, jointLimit, hselected, hlimitPositive, hlimit⟩
    exact Or.inr (Or.inr (Or.inl ⟨source,
      hhorizon'.comp hselected.tendsto_atTop⟩))
  · obtain ⟨owner, selected, deletedLimit, hselected, hdeletedPositive,
      hjoint, howner, hother⟩ := hexceptional
    let source : QuittingUniqueExceptionalOwnerSource reward :=
      ⟨reindexed, owner, selected, deletedLimit, hselected,
        hdeletedPositive, hjoint, howner, hother⟩
    exact Or.inr (Or.inr (Or.inr ⟨source,
      hhorizon'.comp hselected.tendsto_atTop⟩))

/-- A constant root's deleted-prefix survival is the corresponding one-row
opponent Continue mass raised to the prefix length. -/
theorem QuittingDiffuseStationaryPrefixFamily.prefixDeletedSurvival_eq_pow
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (index : ℕ) (who : ι) :
    family.prefixDeletedSurvival index who =
      quittingStationaryFixedOpponentsContinueMass
          (family.root index) who ^ (family.horizon index + 1) := by
  unfold QuittingDiffuseStationaryPrefixFamily.prefixDeletedSurvival
    quittingOpponentSurvivalWeight
    quittingStationaryFixedOpponentsContinueMass
  simp [quittingFixedOpponentsContinueMass]

/-- The exceptional owner's own prefix-survival factor is the power of that
owner's one-row Continue probability. -/
theorem QuittingUniqueExceptionalOwnerSource.ownerPrefixSurvival_eq_pow
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward) (n : ℕ) :
    source.ownerPrefixSurvival n =
      (source.family.root (source.selected n) source.owner false).toReal ^
        (source.family.horizon (source.selected n) + 1) := by
  unfold QuittingUniqueExceptionalOwnerSource.ownerPrefixSurvival
  simp only [Finset.prod_const, Finset.card_range]

/-- Along a divergent-horizon exceptional source, every opponent of the
exceptional owner Continues with probability tending to one in the selected
stationary row. -/
theorem QuittingUniqueExceptionalOwnerSource.tendsto_ownerOpponentContinueMass_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward)
    (hhorizon : Tendsto
      (fun n ↦ source.family.horizon (source.selected n)) atTop atTop) :
    Tendsto (fun n ↦ quittingStationaryFixedOpponentsContinueMass
      (source.family.root (source.selected n)) source.owner)
      atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_cases hlarge : 1 < ε
  · refine ⟨0, fun n _ ↦ ?_⟩
    have hmass0 : 0 ≤ quittingStationaryFixedOpponentsContinueMass
        (source.family.root (source.selected n)) source.owner :=
      quittingFixedOpponentsContinueMass_nonneg _ _ 0
    have hmass1 : quittingStationaryFixedOpponentsContinueMass
        (source.family.root (source.selected n)) source.owner ≤ 1 :=
      quittingFixedOpponentsContinueMass_le_one _ _ 0
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hmass1)]
    linarith
  · have hεone : ε ≤ 1 := le_of_not_gt hlarge
    let base : ℝ := 1 - ε
    have hbase0 : 0 ≤ base := by dsimp [base]; linarith
    have hbase1 : base < 1 := by dsimp [base]; linarith
    have hhorizonShift : Tendsto
        (fun n ↦ source.family.horizon (source.selected n) + 1)
        atTop atTop := by
      have hadd := (tendsto_add_atTop_nat 1).comp hhorizon
      simpa [Function.comp_def, Nat.add_comm] using hadd
    have hbasePow : Tendsto (fun n ↦
        base ^ (source.family.horizon (source.selected n) + 1))
        atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1).comp
        hhorizonShift
    have hdeletedLower : ∀ᶠ n in atTop,
        source.deletedLimit / 2 <
          source.family.prefixDeletedSurvival
            (source.selected n) source.owner :=
      (tendsto_order.1 source.ownerDeleted_tendsto).1
        (source.deletedLimit / 2) (by linarith [source.deletedLimit_pos])
    have hbaseUpper : ∀ᶠ n in atTop,
        base ^ (source.family.horizon (source.selected n) + 1) <
          source.deletedLimit / 2 :=
      (tendsto_order.1 hbasePow).2 (source.deletedLimit / 2)
        (by linarith [source.deletedLimit_pos])
    obtain ⟨threshold, hthreshold⟩ :=
      Filter.eventually_atTop.1 (hdeletedLower.and hbaseUpper)
    refine ⟨threshold, fun n hn ↦ ?_⟩
    obtain ⟨hdeleted, hbase⟩ := hthreshold n hn
    let opponentMass := quittingStationaryFixedOpponentsContinueMass
      (source.family.root (source.selected n)) source.owner
    have hopponent0 : 0 ≤ opponentMass :=
      quittingFixedOpponentsContinueMass_nonneg _ _ 0
    have hopponent1 : opponentMass ≤ 1 :=
      quittingFixedOpponentsContinueMass_le_one _ _ 0
    have hopponent : base < opponentMass := by
      by_contra hnot
      have hpow : opponentMass ^
          (source.family.horizon (source.selected n) + 1) ≤
          base ^ (source.family.horizon (source.selected n) + 1) :=
        pow_le_pow_left₀ hopponent0 (le_of_not_gt hnot) _
      rw [source.family.prefixDeletedSurvival_eq_pow] at hdeleted
      change opponentMass ^
          (source.family.horizon (source.selected n) + 1) >
        source.deletedLimit / 2 at hdeleted
      linarith
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hopponent1)]
    dsimp only [base] at hopponent
    linarith

/-- Equivalently, the one-row probability that some opponent of the
exceptional owner Quits tends to zero. -/
theorem QuittingUniqueExceptionalOwnerSource.tendsto_ownerOpponentHazard_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward)
    (hhorizon : Tendsto
      (fun n ↦ source.family.horizon (source.selected n)) atTop atTop) :
    Tendsto (fun n ↦ 1 - quittingStationaryFixedOpponentsContinueMass
      (source.family.root (source.selected n)) source.owner)
      atTop (nhds 0) := by
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h := hone.sub (source.tendsto_ownerOpponentContinueMass_one hhorizon)
  norm_num at h
  exact h

/-- The exceptional owner eventually has strictly positive one-row Quit
probability.  Otherwise its own prefix-survival factor would equal one,
contradicting the checked vanishing theorem. -/
theorem QuittingUniqueExceptionalOwnerSource.eventually_ownerQuitProbability_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward) :
    ∀ᶠ n in atTop,
      0 < (source.family.root (source.selected n) source.owner true).toReal := by
  have hsurvivalSmall : ∀ᶠ n in atTop, source.ownerPrefixSurvival n < 1 / 2 :=
    (tendsto_order.1 source.ownerPrefixSurvival_tendsto_zero).2 (1 / 2)
      (by norm_num)
  filter_upwards [hsurvivalSmall] with n hsmall
  have hquitNonneg : 0 ≤
      (source.family.root (source.selected n) source.owner true).toReal :=
    ENNReal.toReal_nonneg
  apply lt_of_le_of_ne hquitNonneg
  intro hzero
  have hquitZero :
      (source.family.root (source.selected n) source.owner true).toReal = 0 :=
    hzero.symm
  have hsum := pmf_toReal_sum_one
    (source.family.root (source.selected n) source.owner)
  rw [Fintype.sum_bool, hquitZero, zero_add] at hsum
  rw [source.ownerPrefixSurvival_eq_pow, hsum, one_pow] at hsmall
  norm_num at hsmall

/-- After discarding finitely many selected rows, a divergent exceptional
source supplies both probabilistic root inputs of the solo-stationary
fallback: positive owner hazard at every retained row and vanishing opponent
hazard. -/
theorem QuittingUniqueExceptionalOwnerSource.exists_soloFallbackRootTail
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward)
    (hhorizon : Tendsto
      (fun n ↦ source.family.horizon (source.selected n)) atTop atTop) :
    ∃ start : ℕ,
      (∀ n, 0 < (source.family.root (source.selected (start + n))
        source.owner true).toReal) ∧
      Tendsto (fun n ↦
        1 - quittingStationaryFixedOpponentsContinueMass
          (source.family.root (source.selected (start + n))) source.owner)
        atTop (nhds 0) := by
  obtain ⟨start, hstart⟩ :=
    Filter.eventually_atTop.1 source.eventually_ownerQuitProbability_pos
  refine ⟨start, fun n ↦ hstart (start + n) (Nat.le_add_right start n), ?_⟩
  have hshift := source.tendsto_ownerOpponentHazard_zero hhorizon |>.comp
    (tendsto_add_atTop_nat start)
  simpa [Function.comp_def, Nat.add_comm] using hshift

end GameTheory
