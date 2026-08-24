/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargePersistentBaseFiniteNashDispatch
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseConcreteGap

/-!
# Same-profile deletion adapter for persistent bases

The finite polynomial dispatch retains the original mixed free-player
profile while deleting one paid member of a two-player persistent base. This
file records the semantic fact needed for that handoff: vanishing endpoint
differences at the retained profile reconstruct exact induced Nash, after
which the existing singleton-base compiler applies.
-/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- A product-root payoff is affine in any one displayed marginal, even when
the payoff coordinate differs from the replaced coordinate. -/
theorem quittingRootExpectedPayoff_update_eq_otherMarginalMix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (other who : ι) (marginal : PMF Bool) :
    quittingRootExpectedPayoff reward tail
        (Function.update root other marginal) who =
      (marginal true).toReal *
          quittingRootExpectedPayoff reward tail
            (Function.update root other (PMF.pure true)) who +
        (marginal false).toReal *
          quittingRootExpectedPayoff reward tail
            (Function.update root other (PMF.pure false)) who := by
  unfold quittingRootExpectedPayoff
  rw [Math.PMFProduct.pmfPi_update_bind, Math.Probability.expect_bind,
    Math.Probability.expect_eq_sum,
    Fintype.sum_bool]

omit [Nonempty ι] in
/-- A player's endpoint difference is affine in every opponent marginal. -/
theorem quittingRootEndpointDifference_eq_opponentMix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    {who other : ι} (hne : who ≠ other) :
    quittingRootEndpointDifference reward tail root who =
      (root other true).toReal *
          quittingRootEndpointDifference reward tail
            (Function.update root other (PMF.pure true)) who +
        (root other false).toReal *
          quittingRootEndpointDifference reward tail
            (Function.update root other (PMF.pure false)) who := by
  have hquit := quittingRootExpectedPayoff_update_eq_otherMarginalMix
    reward tail (Function.update root who (PMF.pure true)) other who (root other)
  have hcontinue := quittingRootExpectedPayoff_update_eq_otherMarginalMix
    reward tail (Function.update root who (PMF.pure false)) other who (root other)
  have hotherTrue :
      Function.update (Function.update root who (PMF.pure true)) other
          (PMF.pure true) =
        Function.update (Function.update root other (PMF.pure true)) who
          (PMF.pure true) := by
    exact Function.update_comm hne (PMF.pure true) (PMF.pure true) root
  have hotherFalse :
      Function.update (Function.update root who (PMF.pure true)) other
          (PMF.pure false) =
        Function.update (Function.update root other (PMF.pure false)) who
          (PMF.pure true) := by
    exact Function.update_comm hne (PMF.pure true) (PMF.pure false) root
  have hcontinueTrue :
      Function.update (Function.update root who (PMF.pure false)) other
          (PMF.pure true) =
        Function.update (Function.update root other (PMF.pure true)) who
          (PMF.pure false) := by
    exact Function.update_comm hne (PMF.pure false) (PMF.pure true) root
  have hcontinueFalse :
      Function.update (Function.update root who (PMF.pure false)) other
          (PMF.pure false) =
        Function.update (Function.update root other (PMF.pure false)) who
          (PMF.pure false) := by
    exact Function.update_comm hne (PMF.pure false) (PMF.pure false) root
  have hquitSelf :
      Function.update (Function.update root who (PMF.pure true)) other
          (root other) = Function.update root who (PMF.pure true) := by
    rw [show root other =
        Function.update root who (PMF.pure true) other by simp [hne.symm]]
    exact Function.update_eq_self other _
  have hcontinueSelf :
      Function.update (Function.update root who (PMF.pure false)) other
          (root other) = Function.update root who (PMF.pure false) := by
    rw [show root other =
        Function.update root who (PMF.pure false) other by simp [hne.symm]]
    exact Function.update_eq_self other _
  rw [hquitSelf] at hquit
  rw [hcontinueSelf] at hcontinue
  rw [hotherTrue, hotherFalse] at hquit
  rw [hcontinueTrue, hcontinueFalse] at hcontinue
  simp only [quittingRootEndpointDifference, quittingRootQuitPayoff,
    quittingRootContinuePayoff]
  rw [hquit, hcontinue]
  ring

omit [Nonempty ι] in
/-- Two-player form of opponent affinity, written in the exact binary
difference coordinates consumed by the finite dispatch. -/
theorem quittingRootEndpointDifference_eq_binaryDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    {who other : ι} (hne : who ≠ other) :
    let endpoint : Bool → ℝ := fun action =>
      quittingRootEndpointDifference reward tail
        (Function.update root other (PMF.pure action)) who
    quittingRootEndpointDifference reward tail root who =
      binaryFirstDifference endpoint (root other true).toReal := by
  intro endpoint
  rw [quittingRootEndpointDifference_eq_opponentMix reward tail root hne]
  rw [binaryFirstDifference, Math.PMFProduct.pmfBool_false_toReal]
  ring

omit [Nonempty ι] in
/-- If both pure actions are indifferent at a supplied product profile, that
profile belongs to the complete induced Nash set. -/
theorem mem_quittingPersistentBaseNashSet_of_free_endpointDifference_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (hbase : base.Nonempty)
    (hdisjoint : Disjoint base free)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (hzero : ∀ who ∈ free,
      quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot base free point) who = 0) :
    point ∈ quittingPersistentBaseNashSet reward base free := by
  let profile := ofPolytope (quittingBinaryForm free).sig point.2
  have hnash : IsNash (quittingBinaryForm free).mixed
      (euPreference (quittingPersistentBaseUtility reward base free))
      profile := by
    rw [isNash_mixed_iff]
    intro who action
    simp only [Profile.update]
    let root := quittingPersistentBaseRootOfProfile base free profile
    have hroot : root = quittingPersistentBaseRoot base free point := by
      rfl
    have hcurrent := expectedUtility_persistentBase_eq_rootExpectedPayoff
      reward base free hbase hdisjoint profile who
    have hpure := expectedUtility_persistentBase_eq_rootExpectedPayoff
      reward base free hbase hdisjoint
        (Function.update profile who (FinDist.pure action)) who
    have hupdate := quittingPersistentBaseRootOfProfile_update
      base free hdisjoint profile who (FinDist.pure action)
    have hdiff : quittingRootEndpointDifference reward 0 root who.1 = 0 := by
      rw [hroot]
      exact hzero who.1 who.2
    cases action
    · have hregret := quittingRootContinuePayoff_sub_successorPayoff
        reward 0 root who.1
      rw [hdiff, mul_zero] at hregret
      simp at hupdate
      rw [hpure, hupdate, hcurrent]
      change quittingRootContinuePayoff reward 0 root who.1 ≤
        quittingRootSuccessorPayoff reward 0 root who.1
      linarith
    · have hregret := quittingRootQuitPayoff_sub_successorPayoff
        reward 0 root who.1
      rw [hdiff, mul_zero] at hregret
      simp at hupdate
      rw [hpure, hupdate, hcurrent]
      change quittingRootQuitPayoff reward 0 root who.1 ≤
        quittingRootSuccessorPayoff reward 0 root who.1
      linarith
  change point.1 ∈ bestReplies (quittingBinaryForm free)
    (quittingPersistentBaseUtility reward base free) point.1
  have hpoly := (probs_mem_bestReplies_self_iff_isNash
    (F := quittingBinaryForm free)
    (quittingPersistentBaseUtility reward base free) profile).mpr hnash
  simpa [profile, probs_ofPolytope (quittingBinaryForm free).sig point.2]
    using hpoly

omit [Nonempty ι] in
/-- **Mixed deletion semantic dispatch.** Deleting one member `outsider` of
a two-member persistent base closes through the singleton-base all-behavior
compiler whenever the retained free profile remains indifferent, the sure
owner's punishment-floor excess is nonpositive, and the deleted member has
the required no-join sign. -/
theorem exists_uniformPayoff_of_largeBase_mixedDeletion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner outsider : ι) (free : Finset ι)
    (howner : owner ∉ free)
    (hcover : ∀ who, who ∉ ({owner} : Finset ι) ∪ free → who = outsider)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (hzero : ∀ who ∈ free,
      quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot {owner} free point) who = 0)
    (hfloor : quittingSingletonBaseOwnerFloorExcess reward owner
      (quittingPersistentBaseRoot {owner} free point) ≤ 0)
    (hpaid : quittingRootEndpointDifference reward 0
      (quittingPersistentBaseRoot {owner} free point) outsider ≤ 0) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hdisjoint : Disjoint ({owner} : Finset ι) free := by
    simpa [Finset.disjoint_left] using howner
  have hpoint : point ∈ quittingPersistentBaseNashSet reward {owner} free :=
    mem_quittingPersistentBaseNashSet_of_free_endpointDifference_eq_zero
      reward {owner} free (by simp) hdisjoint point hzero
  have hjoin : ∀ who ∉ ({owner} : Finset ι) ∪ free,
      quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot {owner} free point) who ≤ 0 := by
    intro who hwho
    rw [hcover who hwho]
    exact hpaid
  obtain ⟨certificate⟩ :=
    nonempty_quittingSingletonBaseCertificate_of_inducedNash
      reward owner free howner point hpoint hfloor hjoin
  exact ⟨quittingRootAbsorbingContribution reward
      (quittingPersistentBaseRoot {owner} free point),
    certificate.isUniformEquilibriumPayoff⟩

end GameTheory
