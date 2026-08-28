/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseConcreteGap
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Root.OneDateNeverNashDebt

/-!
# Safe chambers for HOPF completion screens

This file packages three reusable successful chambers without specializing to
the moving HOPF regression table.  The singleton and pair records delegate to
the exact sure-exit-set characterization.  The induced-owner record retains an
actual mixed Nash point and delegates to the existing singleton persistent-base
all-behavior compiler.

These are sufficient-data wrappers.  They do not produce a chamber from an
atlas source, and the positive-gap alternative does not itself produce a
uniform payoff.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Literal sign data making one sure quitter an exact pure chamber. -/
structure QuittingPureSingletonChamber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : Prop where
  owner_no_leave : 0 ≤ quittingSoloReward reward owner owner
  outsider_no_join : ∀ other, other ≠ owner →
    quittingSingletonCollisionReward reward owner other ≤
      quittingSoloReward reward owner other

namespace QuittingPureSingletonChamber

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {owner : ι}

omit [Fintype ι] [Nonempty ι] in
/-- The chamber signs are exactly the singleton sure-exit-set conditions. -/
theorem isSureExitSet (chamber : QuittingPureSingletonChamber reward owner) :
    IsQuittingSureExitSet reward ({owner} : Finset ι) :=
  (isQuittingSureExitSet_singleton_iff reward owner).mpr
    ⟨chamber.owner_no_leave, chamber.outsider_no_join⟩

omit [Nonempty ι] in
/-- The pure singleton row is exact Nash against all behavioral deviations. -/
theorem terminalNash (chamber : QuittingPureSingletonChamber reward owner) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward
        (quittingPureSetRoot ({owner} : Finset ι))) :=
  (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
    reward {owner}).mpr chamber.isSureExitSet

omit [Nonempty ι] in
/-- The singleton reward is a fixed uniform-equilibrium payoff. -/
theorem uniformEquilibriumPayoff
    (chamber : QuittingPureSingletonChamber reward owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSetReward reward ({owner} : Finset ι)) :=
  isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
    reward chamber.isSureExitSet

end QuittingPureSingletonChamber

/-- Literal sign data making two distinct sure quitters an exact pure chamber. -/
structure QuittingPurePairChamber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι) : Prop where
  distinct : first ≠ second
  first_no_leave : quittingSoloReward reward second first ≤
    quittingSingletonCollisionReward reward second first
  second_no_leave : quittingSoloReward reward first second ≤
    quittingSingletonCollisionReward reward first second
  outsider_no_join : ∀ outsider, outsider ≠ first → outsider ≠ second →
    quittingSetReward reward (insert outsider {first, second}) outsider ≤
      quittingSetReward reward {first, second} outsider

namespace QuittingPurePairChamber

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {first second : ι}

omit [Fintype ι] [Nonempty ι] in
/-- The chamber signs are exactly the pair sure-exit-set conditions. -/
theorem isSureExitSet (chamber : QuittingPurePairChamber reward first second) :
    IsQuittingSureExitSet reward ({first, second} : Finset ι) :=
  (isQuittingSureExitSet_pair_iff reward chamber.distinct).mpr
    ⟨chamber.first_no_leave, chamber.second_no_leave,
      chamber.outsider_no_join⟩

omit [Nonempty ι] in
/-- The pure pair row is exact Nash against all behavioral deviations. -/
theorem terminalNash (chamber : QuittingPurePairChamber reward first second) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward
        (quittingPureSetRoot ({first, second} : Finset ι))) :=
  (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
    reward {first, second}).mpr chamber.isSureExitSet

omit [Nonempty ι] in
/-- The pair reward is a fixed uniform-equilibrium payoff. -/
theorem uniformEquilibriumPayoff
    (chamber : QuittingPurePairChamber reward first second) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSetReward reward ({first, second} : Finset ι)) :=
  isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
    reward chamber.isSureExitSet

end QuittingPurePairChamber

/-- An actual induced Nash row on the face where `owner` quits surely,
together with the remaining owner-floor and outsider-join signs. -/
structure QuittingInducedOwnerChamber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) where
  owner_not_mem : owner ∉ free
  point : mixedPolytope (quittingBinaryForm free).sig
  point_nash : point ∈ quittingPersistentBaseNashSet reward {owner} free
  owner_floor : quittingSingletonBaseOwnerFloorExcess reward owner
    (quittingPersistentBaseRoot {owner} free point) ≤ 0
  outsider_no_join : ∀ who ∉ ({owner} : Finset ι) ∪ free,
    quittingRootEndpointDifference reward 0
      (quittingPersistentBaseRoot {owner} free point) who ≤ 0

namespace QuittingInducedOwnerChamber

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {owner : ι} {free : Finset ι}

omit [Nonempty ι] in
/-- The induced chamber compiles to the existing all-behavior certificate. -/
theorem certificate (chamber : QuittingInducedOwnerChamber reward owner free) :
    QuittingSingletonBaseCertificate reward owner
      (quittingPersistentBaseRoot {owner} free chamber.point) :=
  Classical.choice (nonempty_quittingSingletonBaseCertificate_of_inducedNash
    reward owner free chamber.owner_not_mem chamber.point chamber.point_nash
    chamber.owner_floor chamber.outsider_no_join)

omit [Nonempty ι] in
/-- The induced chamber's nominal absorbing contribution is a fixed
uniform-equilibrium payoff. -/
theorem uniformEquilibriumPayoff
    (chamber : QuittingInducedOwnerChamber reward owner free) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingRootAbsorbingContribution reward
        (quittingPersistentBaseRoot {owner} free chamber.point)) :=
  chamber.certificate.isUniformEquilibriumPayoff

end QuittingInducedOwnerChamber

/-! ## Exact all-Never-tail induced-owner chamber -/

/-- Literal `Continue - Quit` margin of the sure owner at one induced Nash
point.  Nonpositivity is exactly the closing sign `Q_owner ≥ C_owner`. -/
def quittingInducedOwnerNeverExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) : ℝ :=
  quittingRootContinuePayoff reward 0
      (quittingPersistentBaseRoot {owner} free point) owner -
    quittingRootQuitPayoff reward 0
      (quittingPersistentBaseRoot {owner} free point) owner

omit [Nonempty ι] in
/-- The induced-owner margin is the negative endpoint difference. -/
theorem quittingInducedOwnerNeverExcess_eq_neg_endpointDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) :
    quittingInducedOwnerNeverExcess reward owner free point =
      -quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot {owner} free point) owner := by
  simp [quittingInducedOwnerNeverExcess, quittingRootEndpointDifference]

omit [Nonempty ι] in
/-- The literal owner margin varies continuously over the full induced Nash
carrier. -/
theorem continuous_quittingInducedOwnerNeverExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) :
    Continuous (quittingInducedOwnerNeverExcess reward owner free) := by
  have h := (continuous_quittingRootEndpointDifference_simplex reward owner).comp
    ((continuous_const : Continuous fun _ :
      mixedPolytope (quittingBinaryForm free).sig => (0 : Payoff ι)).prodMk
        (continuous_quittingPersistentBaseSimplexRoot {owner} free))
  have hroot : (fun point : mixedPolytope (quittingBinaryForm free).sig =>
      quittingRootEndpointDifference reward 0
        (quittingRootOfSimplex
          (quittingPersistentBaseSimplexRoot {owner} free point)) owner) =
      fun point => quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot {owner} free point) owner := by
    funext point
    rw [quittingRootOfSimplex_persistentBaseSimplexRoot]
  change Continuous (fun point :
      mixedPolytope (quittingBinaryForm free).sig =>
    quittingRootEndpointDifference reward 0
      (quittingRootOfSimplex
        (quittingPersistentBaseSimplexRoot {owner} free point)) owner) at h
  rw [hroot] at h
  rw [show quittingInducedOwnerNeverExcess reward owner free = fun point =>
      -quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot {owner} free point) owner by
    funext point
    exact quittingInducedOwnerNeverExcess_eq_neg_endpointDifference
      reward owner free point]
  exact h.neg

/-- One actual induced Nash point whose sure owner weakly prefers immediate
Quit to Continue, whose owner solo payoff is nonpositive, and whose fixed
outsiders weakly prefer Continue. -/
structure QuittingInducedOwnerNeverChamber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) where
  owner_not_mem : owner ∉ free
  point : mixedPolytope (quittingBinaryForm free).sig
  point_nash : point ∈ quittingPersistentBaseNashSet reward {owner} free
  owner_solo_nonpos : reward (quittingSingletonTerminal owner) owner ≤ 0
  owner_quit_ge_continue :
    quittingRootContinuePayoff reward 0
        (quittingPersistentBaseRoot {owner} free point) owner ≤
      quittingRootQuitPayoff reward 0
        (quittingPersistentBaseRoot {owner} free point) owner
  outsider_no_join : ∀ who ∉ ({owner} : Finset ι) ∪ free,
    quittingRootQuitPayoff reward 0
        (quittingPersistentBaseRoot {owner} free point) who ≤
      quittingRootContinuePayoff reward 0
        (quittingPersistentBaseRoot {owner} free point) who

namespace QuittingInducedOwnerNeverChamber

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {owner : ι} {free : Finset ι}

/-- The actual ambient product root retained by the chamber. -/
def root (chamber : QuittingInducedOwnerNeverChamber reward owner free) :
    ι → PMF Bool :=
  quittingPersistentBaseRoot {owner} free chamber.point

omit [Nonempty ι] in
@[simp] theorem root_owner
    (chamber : QuittingInducedOwnerNeverChamber reward owner free) :
    chamber.root owner = PMF.pure true :=
  quittingPersistentBaseRoot_apply_of_mem_base
    {owner} free chamber.point (by simp)

omit [Nonempty ι] in
/-- The induced row is exact Nash for zero continuation. -/
theorem zeroTailRootNash
    (chamber : QuittingInducedOwnerNeverChamber reward owner free) :
    IsεQuittingRootNash reward (0 : Payoff ι) 0 chamber.root := by
  apply (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
    reward 0 0 chamber.root).mp
  apply (isεQuittingRootEndpointNash_iff_purePayoff_le
    reward 0 0 chamber.root).mpr
  intro who
  by_cases howner : who = owner
  · subst who
    have hsuccessor : quittingRootSuccessorPayoff reward 0 chamber.root owner =
        quittingRootQuitPayoff reward 0 chamber.root owner := by
      rw [quittingRootSuccessorPayoff_eq_endpointMix, chamber.root_owner]
      simp
    constructor
    · simpa using hsuccessor.ge
    · simpa [root] using chamber.owner_quit_ge_continue.trans hsuccessor.ge
  · by_cases hfree : who ∈ free
    · have hdisjoint : Disjoint ({owner} : Finset ι) free := by
        simpa [Finset.disjoint_singleton_left] using chamber.owner_not_mem
      simpa [root] using
        (quittingPersistentBaseRoot_free_purePayoff_le reward {owner} free
          (by simp) hdisjoint chamber.point chamber.point_nash who hfree)
    · have houtside : who ∉ ({owner} : Finset ι) ∪ free := by
        simp [howner, hfree]
      have hroot : chamber.root who = PMF.pure false :=
        quittingPersistentBaseRoot_apply_of_outside
          {owner} free chamber.point houtside
      have hsuccessor : quittingRootSuccessorPayoff reward 0 chamber.root who =
          quittingRootContinuePayoff reward 0 chamber.root who := by
        rw [quittingRootSuccessorPayoff_eq_endpointMix, hroot]
        simp
      constructor
      · simpa [root] using
          (chamber.outsider_no_join who houtside).trans hsuccessor.ge
      · simpa using hsuccessor.ge

omit [Nonempty ι] in
/-- Every nonowner's deleted-opponent Continue mass vanishes because the
owner quits surely at the displayed root. -/
theorem opponentContinueMass_eq_zero
    (chamber : QuittingInducedOwnerNeverChamber reward owner free)
    {who : ι} (hwho : who ≠ owner) :
    quittingRootOpponentContinueMass chamber.root who = 0 := by
  have hle := quittingRootOpponentContinueMass_le_continueProbability_of_ne
    chamber.root (who := who) (other := owner) hwho.symm
  rw [chamber.root_owner] at hle
  have hnonneg := quittingRootOpponentContinueMass_nonneg chamber.root who
  have hleZero : quittingRootOpponentContinueMass chamber.root who ≤ 0 := by
    simpa using hle
  exact le_antisymm hleZero hnonneg

omit [Nonempty ι] in
/-- Every coordinate has exactly zero unrestricted terminal debt after the
induced root is followed by perpetual Continue. -/
theorem terminalDeviationDebt_eq_zero
    (chamber : QuittingInducedOwnerNeverChamber reward owner free)
    (who : ι) :
    quittingTerminalDeviationDebt reward
      (quittingOneDateThenNeverProfile reward chamber.root) who = 0 := by
  by_cases howner : who = owner
  · subst who
    exact quittingTerminalDeviationDebt_oneDateThenNever_eq_zero_of_solo_nonpos
      reward chamber.root owner chamber.zeroTailRootNash
        chamber.owner_solo_nonpos
  · have hupper :=
      quittingTerminalDeviationDebt_oneDateThenNever_le_continueMass_mul_solo
        reward chamber.root who chamber.zeroTailRootNash
    rw [chamber.opponentContinueMass_eq_zero howner, zero_mul] at hupper
    exact le_antisymm hupper
      (quittingTerminalDeviationDebt_nonneg reward
        (quittingOneDateThenNeverProfile reward chamber.root) who)

omit [Nonempty ι] in
/-- The literal induced root followed by the all-Never tail is exact Nash
against every behavioral deviation. -/
theorem terminalNash
    (chamber : QuittingInducedOwnerNeverChamber reward owner free) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingOneDateThenNeverProfile reward chamber.root) := by
  intro who deviation
  have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (quittingOneDateThenNeverProfile reward chamber.root) who deviation
  have hzero := chamber.terminalDeviationDebt_eq_zero who
  unfold quittingTerminalDeviationDebt at hzero
  linarith

omit [Nonempty ι] in
/-- The all-Never-tail chamber produces a checked uniform-equilibrium payoff. -/
theorem uniformEquilibriumPayoff
    (chamber : QuittingInducedOwnerNeverChamber reward owner free) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingTerminalPayoff reward
        (quittingOneDateThenNeverProfile reward chamber.root)) :=
  quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact reward _
    chamber.terminalNash

end QuittingInducedOwnerNeverChamber

omit [Nonempty ι] in
/-- Exact compact alternative for the all-Never-tail specialization.  Either
some induced Nash point has `C_owner - Q_owner ≤ 0` and closes to a uniform
payoff, or the literal margin `C_owner - Q_owner` is uniformly positive on
the entire induced Nash carrier. -/
theorem exists_uniformPayoff_or_inducedOwnerNever_continue_sub_quit_pos_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) (howner : owner ∉ free)
    (hsolo : reward (quittingSingletonTerminal owner) owner ≤ 0)
    (houtsider : ∀ point ∈
        quittingPersistentBaseNashSet reward {owner} free,
      ∀ who ∉ ({owner} : Finset ι) ∪ free,
        quittingRootQuitPayoff reward 0
            (quittingPersistentBaseRoot {owner} free point) who ≤
          quittingRootContinuePayoff reward 0
            (quittingPersistentBaseRoot {owner} free point) who) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ gamma : ℝ, 0 < gamma ∧
        ∀ point ∈ quittingPersistentBaseNashSet reward {owner} free,
          gamma ≤ quittingRootContinuePayoff reward 0
              (quittingPersistentBaseRoot {owner} free point) owner -
            quittingRootQuitPayoff reward 0
              (quittingPersistentBaseRoot {owner} free point) owner := by
  rcases exists_persistentBaseNash_nonpos_or_pos_gap reward {owner} free
      (quittingInducedOwnerNeverExcess reward owner free)
      (continuous_quittingInducedOwnerNeverExcess reward owner free) with
    haccepted | hgap
  · left
    obtain ⟨point, hpoint, hmargin⟩ := haccepted
    let chamber : QuittingInducedOwnerNeverChamber reward owner free := {
      owner_not_mem := howner
      point := point
      point_nash := hpoint
      owner_solo_nonpos := hsolo
      owner_quit_ge_continue := by
        simpa [quittingInducedOwnerNeverExcess] using hmargin
      outsider_no_join := houtsider point hpoint
    }
    exact ⟨quittingTerminalPayoff reward
      (quittingOneDateThenNeverProfile reward chamber.root),
        chamber.uniformEquilibriumPayoff⟩
  · right
    simpa only [quittingInducedOwnerNeverExcess] using hgap

omit [Nonempty ι] in
/-- The existing compact induced-Nash alternative, exposed under the chamber
name: either some induced owner chamber closes, or one positive excess margin
holds uniformly on the entire induced Nash carrier. -/
theorem exists_uniformPayoff_or_inducedOwnerChamber_pos_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) (howner : owner ∉ free) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ gamma : ℝ, 0 < gamma ∧
        ∀ point ∈ quittingPersistentBaseNashSet reward {owner} free,
          gamma ≤ quittingSingletonBaseExcess reward owner free point :=
  exists_uniformPayoff_or_singletonBase_pos_gap reward owner free howner

end GameTheory
