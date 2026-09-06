/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargePersistentBaseDeletionAdapter
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PrescribedOwnerStationaryHandoff
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargeBasePaidEndpointExactStack
import UniformEquilibrium.Quitting.Root.ForcedQuitEndpointStability

/-!
# Same-profile singleton handoff from an exact root with a sure quitter

An arbitrary exact quitting root with a prescribed sure quitter restricts to
the same point of the singleton-base induced Nash set.  The arbitrary tail is
screened from every free player's endpoints by the sure quitter.  This module
then exposes the existing stationary handoff and its checked consumers without
reselecting an induced Nash point or stationary profile.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Restrict an ambient product root to the mixed-polytope coordinates of a
specified free set. -/
def quittingRootFreeMixedPoint (free : Finset ι) (root : ι → PMF Bool) :
    mixedPolytope (quittingBinaryForm free).sig := by
  let profile : Profile (quittingBinaryForm free).sig.mixed := fun who =>
    ⟨root who, Set.toFinite _⟩
  exact ⟨probs (quittingBinaryForm free).sig profile,
    probs_mem_mixedPolytope (quittingBinaryForm free).sig profile⟩

/-- Extending the restricted free marginals, while fixing the owner to sure
Quit, recovers the original root. -/
theorem quittingPersistentBaseRoot_rootFreeMixedPoint_eq
    (root : ι → PMF Bool) (owner : ι)
    (howner : root owner = PMF.pure true) :
    quittingPersistentBaseRoot {owner} (Finset.univ.erase owner)
        (quittingRootFreeMixedPoint (Finset.univ.erase owner) root) = root := by
  funext who
  by_cases hwho : who = owner
  · subst who
    simpa using howner.symm
  · have hfree : who ∈ Finset.univ.erase owner := by simp [hwho]
    rw [quittingPersistentBaseRoot_apply_of_mem_free]
    · change ((ofPolytope (quittingBinaryForm (Finset.univ.erase owner)).sig
          _ ⟨who, hfree⟩).toPMF) = root who
      simp [quittingRootFreeMixedPoint, FinDist.toPMF]
    · exact Finset.disjoint_singleton_left.mpr (by simp)


/-- The free marginals of an exact root with a sure owner form the same
singleton-base induced Nash point. -/
theorem quittingRootFreeMixedPoint_mem_singletonBaseNashSet_of_sure_exactNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (owner : ι)
    (howner : root owner = PMF.pure true)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    quittingRootFreeMixedPoint (Finset.univ.erase owner) root ∈
      quittingPersistentBaseNashSet reward {owner} (Finset.univ.erase owner) := by
  let free := Finset.univ.erase owner
  let point := quittingRootFreeMixedPoint free root
  have hroot : quittingPersistentBaseRoot {owner} free point = root := by
    exact quittingPersistentBaseRoot_rootFreeMixedPoint_eq root owner howner
  apply mem_quittingPersistentBaseNashSet_of_free_endpointNash reward {owner} free
    (Finset.singleton_nonempty owner)
    (Finset.disjoint_singleton_left.mpr (by simp [free])) point
  intro who hwho
  have hne : who ≠ owner := by simpa [free] using hwho
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).2
      hnash who
  rw [hroot]
  change (root who false).toReal *
      quittingRootEndpointDifference reward 0 root who ≤ 0 ∧
    0 ≤ (root who true).toReal *
      quittingRootEndpointDifference reward 0 root who
  rw [← quittingRootEndpointDifference_eq_zeroTail_of_sureOpponent
    reward tail root hne howner]
  simpa using hendpoint

/-- Stationary repetition of the recovered persistent-base root is literally
stationary repetition of the supplied ambient root. -/
theorem quittingSingletonBaseStationaryProfile_rootFreeMixedPoint_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (howner : root owner = PMF.pure true) :
    quittingSingletonBaseStationaryProfile reward owner
        (Finset.univ.erase owner)
        (quittingRootFreeMixedPoint (Finset.univ.erase owner) root) =
      quittingStationaryProfile reward root := by
  unfold quittingSingletonBaseStationaryProfile
  rw [quittingPersistentBaseRoot_rootFreeMixedPoint_eq root owner howner]

/-- The named repaired profile is exactly the supplied stationary repetition
with the owner replaced by literal Always Continue. -/
theorem quittingSingletonBaseRepairedProfile_rootFreeMixedPoint_eq_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (howner : root owner = PMF.pure true) :
    quittingSingletonBaseRepairedProfile reward owner
        (Finset.univ.erase owner)
        (quittingRootFreeMixedPoint (Finset.univ.erase owner) root) =
      Function.update (quittingStationaryProfile reward root) owner
        (quittingAlwaysContinueStrategy reward owner) := by
  rw [← quittingSingletonBaseStationaryProfile_rootFreeMixedPoint_eq
    reward root owner howner]
  exact (update_quittingSingletonBaseStationaryProfile_owner_alwaysContinue
    reward owner (Finset.univ.erase owner)
      (quittingRootFreeMixedPoint (Finset.univ.erase owner) root)).symm

/-- The prescribed-owner compact gap applies at the exact induced point
obtained from the supplied sure-owner root; no Nash point is reselected. -/
theorem QuittingTerminalExploitabilityWitness.exists_samePoint_stationaryHandoff_of_sure_exactNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (tail : Payoff ι) (root : ι → PMF Bool) (owner : ι)
    (howner : root owner = PMF.pure true)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    ∃ delta : ℝ, 0 < delta ∧
      Nonempty (QuittingSingletonBaseStationaryHandoff reward owner
        (Finset.univ.erase owner)
        (quittingRootFreeMixedPoint (Finset.univ.erase owner) root)
        delta witness.terminalGap) := by
  obtain ⟨delta, hdelta, hall, _⟩ :=
    witness.exists_prescribedOwner_stationaryHandoff owner
  have hpoint :=
    quittingRootFreeMixedPoint_mem_singletonBaseNashSet_of_sure_exactNash
      reward tail root owner howner hnash
  exact ⟨delta, hdelta, (hall _ hpoint).2⟩

/-- Full checked same-point consumer: the exact supplied root yields its
literal stationary source and owner repair, a paid endpoint atom at that
same repaired profile, and either a named free floor failure or the checked
exact orbit with vanishing absorption and no fixed charged recurrence. -/
theorem QuittingTerminalExploitabilityWitness.exists_sureRootHandoff_with_paidAtom_and_floorDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (tail : Payoff ι) (root : ι → PMF Bool) (owner : ι)
    (howner : root owner = PMF.pure true)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (bound : ℝ) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ handoff : QuittingSingletonBaseStationaryHandoff reward owner
          (Finset.univ.erase owner)
          (quittingRootFreeMixedPoint (Finset.univ.erase owner) root)
          delta witness.terminalGap,
        Nonempty (QuittingPaidEndpointAtom reward
          (quittingSingletonBaseRepairedProfile reward owner
            (Finset.univ.erase owner)
            (quittingRootFreeMixedPoint (Finset.univ.erase owner) root))
          handoff.outsideDebtor witness.terminalGap bound) ∧
        ((∃ who ∈ Finset.univ.erase owner,
            quittingTerminalPayoff reward
                (quittingSingletonBaseRepairedProfile reward owner
                  (Finset.univ.erase owner)
                  (quittingRootFreeMixedPoint (Finset.univ.erase owner) root)) who <
              quittingPunishmentValue reward who) ∨
          ∃ hfloor : ∀ who, quittingPunishmentValue reward who ≤
              quittingTerminalPayoff reward
                (quittingSingletonBaseRepairedProfile reward owner
                  (Finset.univ.erase owner)
                  (quittingRootFreeMixedPoint (Finset.univ.erase owner) root)) who,
            Tendsto (fun time ↦ quittingRootAbsorptionMass
                ((handoff.repairedExactInfiniteOrbit hfloor).roots time))
              atTop (nhds 0) ∧
            ∀ chargeThreshold : ℝ, 0 < chargeThreshold →
              ¬ (∀ endpointError : ℝ, 0 < endpointError →
                ∃ start horizon : ℕ, 0 < horizon ∧
                  (∀ who,
                    |(handoff.repairedExactInfiniteOrbit hfloor).value start who -
                      (handoff.repairedExactInfiniteOrbit hfloor).value
                        (start + horizon) who| ≤ endpointError) ∧
                  chargeThreshold ≤ quittingRootAbsorptionMass
                    ((handoff.repairedExactInfiniteOrbit hfloor).roots start))) := by
  obtain ⟨delta, hdelta, handoff⟩ :=
    witness.exists_samePoint_stationaryHandoff_of_sure_exactNash
      tail root owner howner hnash
  obtain ⟨handoff⟩ := handoff
  refine ⟨delta, hdelta, handoff,
    handoff.paidEndpointAtom witness.terminalGap_pos hbound hreward, ?_⟩
  rcases handoff.floor_dispatch with hfloor | hfailure
  · right
    exact ⟨hfloor,
      witness.repairedExactOrbit_absorption_tendsto_zero handoff hfloor,
      fun threshold hthreshold =>
        witness.not_repairedExactOrbit_chargedPayoffRecurrence
          handoff hfloor threshold hthreshold⟩
  · exact Or.inl hfailure

end GameTheory
