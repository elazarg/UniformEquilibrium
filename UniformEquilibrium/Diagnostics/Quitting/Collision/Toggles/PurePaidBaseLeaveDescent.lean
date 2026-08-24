/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseConcreteGap
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargePersistentBaseFiniteNashDispatch
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.StaticCycleChronologyBarrier
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness

/-!
# Pure paid base-leave descent

A pure Nash cell on a two-player persistent base can be tested after deleting
one base player. If the retained free actions remain best replies and the
remaining sure quitter respects its punishment floor, the singleton-base
all-behavior compiler applies. If the retained coalition is nonempty and the
remaining quitter instead has a positive leave premium, deleting it reduces
the problem to the exact sure-exit membership-toggle test.

The declarations retain four arbitrary ambient labels and an exhaustion
hypothesis; no identification of the player type with `Fin 4` is used.
-/

noncomputable section

namespace GameTheory

open Math.Probability QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The free quitters selected by a Boolean pure cell. -/
def purePaidRetainedSet (first second : ι) (firstQuits secondQuits : Bool) :
    Finset ι :=
  (if firstQuits then {first} else ∅) ∪
    if secondQuits then {second} else ∅

/-- The coalition after deleting the paid base member. -/
def purePaidDeletedCoalition (owner first second : ι)
    (firstQuits secondQuits : Bool) : Finset ι :=
  insert owner (purePaidRetainedSet first second firstQuits secondQuits)

/-- The original coalition before deleting the paid base member. -/
def purePaidOriginalCoalition (paid owner first second : ι)
    (firstQuits secondQuits : Bool) : Finset ι :=
  insert paid (purePaidDeletedCoalition owner first second firstQuits secondQuits)

/-- First free player's Quit-minus-Continue difference after deletion. -/
def purePaidDeletedFirstDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner first second : ι) (secondQuits : Bool) : ℝ :=
  quittingSetReward reward
      (purePaidDeletedCoalition owner first second true secondQuits) first -
    quittingSetReward reward
      (purePaidDeletedCoalition owner first second false secondQuits) first

/-- Second free player's Quit-minus-Continue difference after deletion. -/
def purePaidDeletedSecondDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner first second : ι) (firstQuits : Bool) : ℝ :=
  quittingSetReward reward
      (purePaidDeletedCoalition owner first second firstQuits true) second -
    quittingSetReward reward
      (purePaidDeletedCoalition owner first second firstQuits false) second

/-- The retained pure cell remains a Nash cell after deleting the paid base
member. -/
def IsPurePaidDeletedStable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner first second : ι) (firstQuits secondQuits : Bool) : Prop :=
  (if firstQuits then
      0 ≤ purePaidDeletedFirstDifference reward owner first second secondQuits
    else
      purePaidDeletedFirstDifference reward owner first second secondQuits ≤ 0) ∧
    if secondQuits then
      0 ≤ purePaidDeletedSecondDifference reward owner first second firstQuits
    else
      purePaidDeletedSecondDifference reward owner first second firstQuits ≤ 0

/-- Exact punishment-priced leave excess of the retained sure owner. The
empty retained cell exposes the punishment value; every nonempty cell absorbs
at the retained coalition after the owner leaves. -/
def purePaidOwnerFloorExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner first second : ι) (firstQuits secondQuits : Bool) : ℝ :=
  let retained := purePaidRetainedSet first second firstQuits secondQuits
  let deleted := purePaidDeletedCoalition owner first second firstQuits secondQuits
  if retained.Nonempty then
    quittingSetReward reward retained owner -
      quittingSetReward reward deleted owner
  else
    quittingPunishmentValue reward owner -
      quittingSetReward reward deleted owner

/-- Actual four-label source data for a paid pure cell. The original Nash
field records source provenance; the deletion theorems test the new retained
best replies rather than assuming they persist. -/
structure PurePaidBaseLeaveSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (paid owner first second : ι)
    (firstQuits secondQuits : Bool) (gamma : ℝ) : Prop where
  paid_ne_owner : paid ≠ owner
  paid_ne_first : paid ≠ first
  paid_ne_second : paid ≠ second
  owner_ne_first : owner ≠ first
  owner_ne_second : owner ≠ second
  first_ne_second : first ≠ second
  exhaust : ∀ who, who = paid ∨ who = owner ∨ who = first ∨ who = second
  originalPureNash :
    IsPureBinaryDifferenceNash
      (fun action ↦
        quittingSetReward reward
            (purePaidOriginalCoalition paid owner first second true action) first -
          quittingSetReward reward
            (purePaidOriginalCoalition paid owner first second false action) first)
      (fun action ↦
        quittingSetReward reward
            (purePaidOriginalCoalition paid owner first second action true) second -
          quittingSetReward reward
            (purePaidOriginalCoalition paid owner first second action false) second)
      firstQuits secondQuits
  gamma_pos : 0 < gamma
  paidLeave : gamma ≤
    quittingSetReward reward
        (purePaidDeletedCoalition owner first second firstQuits secondQuits) paid -
      quittingSetReward reward
        (purePaidOriginalCoalition paid owner first second firstQuits secondQuits) paid

/-- The literal strict residual obtained by negating retained stability and
the weak owner-floor inequality. -/
def HasPurePaidSingletonResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner first second : ι) (firstQuits secondQuits : Bool) : Prop :=
  (if firstQuits then
      purePaidDeletedFirstDifference reward owner first second secondQuits < 0
    else
      0 < purePaidDeletedFirstDifference reward owner first second secondQuits) ∨
    (if secondQuits then
      purePaidDeletedSecondDifference reward owner first second firstQuits < 0
    else
      0 < purePaidDeletedSecondDifference reward owner first second firstQuits) ∨
    0 < purePaidOwnerFloorExcess reward owner first second
      firstQuits secondQuits

omit [Fintype ι] in
theorem purePaidRetainedSet_subset
    (first second : ι) (firstQuits secondQuits : Bool) :
    purePaidRetainedSet first second firstQuits secondQuits ⊆ {first, second} := by
  intro who hwho
  cases firstQuits <;> cases secondQuits <;>
    simp_all [purePaidRetainedSet]

omit [Fintype ι] in
@[simp] theorem owner_mem_purePaidDeletedCoalition
    (owner first second : ι) (firstQuits secondQuits : Bool) :
    owner ∈ purePaidDeletedCoalition owner first second firstQuits secondQuits := by
  simp [purePaidDeletedCoalition]

omit [Fintype ι] in
theorem purePaidDeletedCoalition_erase_owner
    {owner first second : ι}
    (hownerFirst : owner ≠ first) (hownerSecond : owner ≠ second)
    (firstQuits secondQuits : Bool) :
    (purePaidDeletedCoalition owner first second
      firstQuits secondQuits).erase owner =
        purePaidRetainedSet first second firstQuits secondQuits := by
  cases firstQuits <;> cases secondQuits <;>
    simp [purePaidDeletedCoalition, purePaidRetainedSet,
      hownerFirst, hownerSecond]

omit [Fintype ι] in
theorem purePaidOriginalCoalition_eq_insert
    (paid owner first second : ι) (firstQuits secondQuits : Bool) :
    purePaidOriginalCoalition paid owner first second firstQuits secondQuits =
      insert paid
        (purePaidDeletedCoalition owner first second firstQuits secondQuits) :=
  rfl

omit [Fintype ι] in
theorem insert_first_purePaidDeletedCoalition
    {owner first second : ι} (hownerFirst : owner ≠ first)
    (hfirstSecond : first ≠ second) (firstQuits secondQuits : Bool) :
    insert first (purePaidDeletedCoalition owner first second
      firstQuits secondQuits) =
        purePaidDeletedCoalition owner first second true secondQuits := by
  ext who
  cases firstQuits <;> cases secondQuits <;>
    simp [purePaidDeletedCoalition, purePaidRetainedSet] <;> aesop

omit [Fintype ι] in
theorem erase_first_purePaidDeletedCoalition
    {owner first second : ι} (hownerFirst : owner ≠ first)
    (hfirstSecond : first ≠ second) (firstQuits secondQuits : Bool) :
    (purePaidDeletedCoalition owner first second
      firstQuits secondQuits).erase first =
        purePaidDeletedCoalition owner first second false secondQuits := by
  ext who
  cases firstQuits <;> cases secondQuits <;>
    simp [purePaidDeletedCoalition, purePaidRetainedSet] <;> aesop

omit [Fintype ι] in
theorem insert_second_purePaidDeletedCoalition
    {owner first second : ι} (hownerSecond : owner ≠ second)
    (hfirstSecond : first ≠ second) (firstQuits secondQuits : Bool) :
    insert second (purePaidDeletedCoalition owner first second
      firstQuits secondQuits) =
        purePaidDeletedCoalition owner first second firstQuits true := by
  ext who
  cases firstQuits <;> cases secondQuits <;>
    simp [purePaidDeletedCoalition, purePaidRetainedSet] <;> aesop

omit [Fintype ι] in
theorem erase_second_purePaidDeletedCoalition
    {owner first second : ι} (hownerSecond : owner ≠ second)
    (hfirstSecond : first ≠ second) (firstQuits secondQuits : Bool) :
    (purePaidDeletedCoalition owner first second
      firstQuits secondQuits).erase second =
        purePaidDeletedCoalition owner first second firstQuits false := by
  ext who
  cases firstQuits <;> cases secondQuits <;>
    simp [purePaidDeletedCoalition, purePaidRetainedSet] <;> aesop

omit [Fintype ι] in
theorem paid_not_mem_purePaidDeletedCoalition
    {paid owner first second : ι}
    (hpaidOwner : paid ≠ owner) (hpaidFirst : paid ≠ first)
    (hpaidSecond : paid ≠ second) (firstQuits secondQuits : Bool) :
    paid ∉ purePaidDeletedCoalition owner first second
      firstQuits secondQuits := by
  cases firstQuits <;> cases secondQuits <;>
    simp [purePaidDeletedCoalition, purePaidRetainedSet,
      hpaidOwner, hpaidFirst, hpaidSecond]

/-- At a pure deleted-base root, every nonowner endpoint difference is the
literal join reward minus the literal leave reward. -/
theorem quittingRootEndpointDifference_purePaidDeleted_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner first second who : ι} (hwho : who ≠ owner)
    (firstQuits secondQuits : Bool) :
    quittingRootEndpointDifference reward 0
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second
            firstQuits secondQuits)) who =
      quittingSetReward reward
          (insert who (purePaidDeletedCoalition owner first second
            firstQuits secondQuits)) who -
        quittingSetReward reward
          ((purePaidDeletedCoalition owner first second
            firstQuits secondQuits).erase who) who := by
  have herase :
      ((purePaidDeletedCoalition owner first second
        firstQuits secondQuits).erase who).Nonempty := by
    refine ⟨owner, Finset.mem_erase.mpr ⟨hwho.symm, ?_⟩⟩
    exact owner_mem_purePaidDeletedCoalition owner first second
      firstQuits secondQuits
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_pureSetRoot_eq_insert,
    quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
      (0 : Payoff ι) _ who herase]

/-- The first displayed deleted difference is the actual ambient endpoint
difference at the retained pure root. -/
theorem quittingRootEndpointDifference_purePaidDeleted_first
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner first second : ι}
    (hownerFirst : owner ≠ first) (hfirstSecond : first ≠ second)
    (firstQuits secondQuits : Bool) :
    quittingRootEndpointDifference reward 0
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second
            firstQuits secondQuits)) first =
      purePaidDeletedFirstDifference reward owner first second secondQuits := by
  rw [quittingRootEndpointDifference_purePaidDeleted_eq reward
    hownerFirst.symm firstQuits secondQuits]
  rw [insert_first_purePaidDeletedCoalition hownerFirst hfirstSecond,
    erase_first_purePaidDeletedCoalition hownerFirst hfirstSecond]
  rfl

/-- The second displayed deleted difference is the actual ambient endpoint
difference at the retained pure root. -/
theorem quittingRootEndpointDifference_purePaidDeleted_second
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner first second : ι}
    (hownerSecond : owner ≠ second) (hfirstSecond : first ≠ second)
    (firstQuits secondQuits : Bool) :
    quittingRootEndpointDifference reward 0
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second
            firstQuits secondQuits)) second =
      purePaidDeletedSecondDifference reward owner first second firstQuits := by
  rw [quittingRootEndpointDifference_purePaidDeleted_eq reward
    hownerSecond.symm firstQuits secondQuits]
  rw [insert_second_purePaidDeletedCoalition hownerSecond hfirstSecond,
    erase_second_purePaidDeletedCoalition hownerSecond hfirstSecond]
  rfl

/-- The paid base leave is exactly the deleted outsider's nonjoin endpoint
sign at the retained pure root. -/
theorem quittingRootEndpointDifference_purePaidDeleted_paid
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {paid owner first second : ι}
    (hpaidOwner : paid ≠ owner) (hpaidFirst : paid ≠ first)
    (hpaidSecond : paid ≠ second)
    (firstQuits secondQuits : Bool) :
    quittingRootEndpointDifference reward 0
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second
            firstQuits secondQuits)) paid =
      quittingSetReward reward
          (purePaidOriginalCoalition paid owner first second
            firstQuits secondQuits) paid -
        quittingSetReward reward
          (purePaidDeletedCoalition owner first second
            firstQuits secondQuits) paid := by
  rw [quittingRootEndpointDifference_purePaidDeleted_eq reward
    hpaidOwner firstQuits secondQuits]
  rw [Finset.erase_eq_of_notMem
    (paid_not_mem_purePaidDeletedCoalition hpaidOwner hpaidFirst hpaidSecond
      firstQuits secondQuits)]
  rfl

/-- The abstract singleton-owner floor excess computes to the packet's
piecewise formula, including the punishment-valued empty retained cell. -/
theorem quittingSingletonBaseOwnerFloorExcess_purePaidDeleted_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner first second : ι}
    (hownerFirst : owner ≠ first) (hownerSecond : owner ≠ second)
    (firstQuits secondQuits : Bool) :
    quittingSingletonBaseOwnerFloorExcess reward owner
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second
            firstQuits secondQuits)) =
      purePaidOwnerFloorExcess reward owner first second
        firstQuits secondQuits := by
  let retained := purePaidRetainedSet first second firstQuits secondQuits
  let deleted := purePaidDeletedCoalition owner first second
    firstQuits secondQuits
  have hdeleted : deleted.Nonempty := ⟨owner, by
    simp [deleted, owner_mem_purePaidDeletedCoalition]⟩
  have herase : deleted.erase owner = retained := by
    exact purePaidDeletedCoalition_erase_owner hownerFirst hownerSecond
      firstQuits secondQuits
  rw [quittingSingletonBaseOwnerFloorExcess,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_pureSetRoot,
    stationaryContinueMass_pureSetRoot_of_nonempty hdeleted]
  simp only [zero_mul, add_zero]
  by_cases hretained : retained.Nonempty
  · rw [quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
      (tail := fun _ ↦ quittingPunishmentValue reward owner)
      deleted owner]
    · simp [purePaidOwnerFloorExcess, retained, deleted, hretained, herase]
    · rwa [herase]
  · have hretainedEmpty : retained = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hretained
    have hdeletedSingleton : deleted = {owner} := by
      simp [deleted, purePaidDeletedCoalition, retained, hretainedEmpty]
    change quittingRootContinuePayoff reward
        (fun _ ↦ quittingPunishmentValue reward owner)
          (quittingPureSetRoot deleted) owner -
        quittingSetReward reward deleted owner = _
    rw [hdeletedSingleton,
      quittingRootContinuePayoff_pureSingleton_eq_tail]
    simp [purePaidOwnerFloorExcess, retained, deleted,
      hretainedEmpty, hdeletedSingleton]

/-- Generic bridge from the numeric singleton-owner excess to the semantic
floor field, requiring only that the displayed owner quits surely. -/
theorem purePaidOwnerFloorExcess_nonpos_iff_of_owner_quits
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (root : ι → PMF Bool)
    (howner : root owner = PMF.pure true) :
    quittingSingletonBaseOwnerFloorExcess reward owner root ≤ 0 ↔
      quittingStationaryFixedOpponentsContinueReward reward root owner +
          quittingStationaryFixedOpponentsContinueMass root owner *
            quittingPunishmentValue reward owner ≤
        quittingRootAbsorbingContribution reward root owner := by
  have hcontinueMass : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter howner
  have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents
    reward (fun _ ↦ root) owner
      (fun _ ↦ quittingPunishmentValue reward owner) 0
  have htarget := quittingRootExpectedPayoff_eq_absorbingContribution_add
    reward 0 root owner
  rw [quittingSingletonBaseOwnerFloorExcess, hcontinue, htarget,
    hcontinueMass]
  simp [quittingStationaryFixedOpponentsContinueReward,
    quittingStationaryFixedOpponentsContinueMass,
    quittingFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueMass]

/-- **Singleton-base descent.** A paid pure source whose retained free actions
remain stable and whose sure owner respects its exact punishment-priced floor
produces a uniform-equilibrium payoff against all behavioral deviations. -/
theorem isUniformEquilibriumPayoff_purePaidBaseLeave_deletedStable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ)
    (stable : IsPurePaidDeletedStable reward owner first second
      firstQuits secondQuits)
    (floor : purePaidOwnerFloorExcess reward owner first second
      firstQuits secondQuits ≤ 0) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSetReward reward
        (purePaidDeletedCoalition owner first second
          firstQuits secondQuits)) := by
  let deleted := purePaidDeletedCoalition owner first second
    firstQuits secondQuits
  let root := quittingPureSetRoot deleted
  have hownerRoot : root owner = PMF.pure true := by
    simp [root, deleted, quittingPureSetRoot, quittingSetAction]
  have hfloor : quittingSingletonBaseOwnerFloorExcess reward owner root ≤ 0 := by
    rw [show root = quittingPureSetRoot
        (purePaidDeletedCoalition owner first second
          firstQuits secondQuits) by rfl,
      quittingSingletonBaseOwnerFloorExcess_purePaidDeleted_eq reward
        source.owner_ne_first source.owner_ne_second]
    exact floor
  let certificate : QuittingSingletonBaseCertificate reward owner root := {
    owner_quits := hownerRoot
    other_endpointNash := by
      intro who hwho
      rcases source.exhaust who with hpaid | howner | hfirst | hsecond
      · subst who
        have hpaidDifference :
            quittingRootEndpointDifference reward 0 root paid ≤ -γ := by
          rw [show root = quittingPureSetRoot
              (purePaidDeletedCoalition owner first second
                firstQuits secondQuits) by rfl,
            quittingRootEndpointDifference_purePaidDeleted_paid reward
              source.paid_ne_owner source.paid_ne_first source.paid_ne_second]
          linarith [source.paidLeave]
        have hpaidOutside : paid ∉ deleted := by
          exact paid_not_mem_purePaidDeletedCoalition
            source.paid_ne_owner source.paid_ne_first source.paid_ne_second
              firstQuits secondQuits
        have hrootPaid : root paid = PMF.pure false := by
          simp [root, deleted, quittingPureSetRoot, quittingSetAction,
            hpaidOutside]
        rw [hrootPaid]
        constructor
        · simpa using hpaidDifference.trans
            (neg_nonpos.mpr source.gamma_pos.le)
        · simp
      · exact (hwho howner).elim
      · subst who
        rw [show quittingRootEndpointDifference reward 0 root first =
            purePaidDeletedFirstDifference reward owner first second
              secondQuits by
          exact quittingRootEndpointDifference_purePaidDeleted_first reward
            source.owner_ne_first source.first_ne_second
              firstQuits secondQuits]
        have hrootFirst : root first = PMF.pure firstQuits := by
          cases firstQuits <;> cases secondQuits <;>
            simp [root, deleted, quittingPureSetRoot, quittingSetAction,
              purePaidDeletedCoalition, purePaidRetainedSet,
              source.owner_ne_first.symm, source.first_ne_second]
        rw [hrootFirst]
        cases firstQuits <;>
          simpa [IsPurePaidDeletedStable] using stable.1
      · subst who
        rw [show quittingRootEndpointDifference reward 0 root second =
            purePaidDeletedSecondDifference reward owner first second
              firstQuits by
          exact quittingRootEndpointDifference_purePaidDeleted_second reward
            source.owner_ne_second source.first_ne_second
              firstQuits secondQuits]
        have hrootSecond : root second = PMF.pure secondQuits := by
          cases firstQuits <;> cases secondQuits <;>
            simp [root, deleted, quittingPureSetRoot, quittingSetAction,
              purePaidDeletedCoalition, purePaidRetainedSet,
              source.owner_ne_second.symm, source.first_ne_second.symm]
        rw [hrootSecond]
        cases secondQuits <;>
          simpa [IsPurePaidDeletedStable] using stable.2
    owner_floor_balance :=
      (purePaidOwnerFloorExcess_nonpos_iff_of_owner_quits
        reward owner root hownerRoot).mp hfloor }
  convert certificate.isUniformEquilibriumPayoff using 1
  funext who
  exact (quittingRootAbsorbingContribution_pureSetRoot reward deleted who).symm

/-- Under a terminal exploitability witness, the literal negation of the
singleton-base descent hypotheses is the three-part strict residual. -/
theorem QuittingTerminalExploitabilityWitness.hasPurePaidSingletonResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ) :
    HasPurePaidSingletonResidual reward owner first second
      firstQuits secondQuits := by
  have hnot : ¬ (IsPurePaidDeletedStable reward owner first second
      firstQuits secondQuits ∧
    purePaidOwnerFloorExcess reward owner first second
      firstQuits secondQuits ≤ 0) := by
    rintro ⟨stable, floor⟩
    exact witness.not_exists_uniformEquilibriumPayoff
      ⟨quittingSetReward reward
          (purePaidDeletedCoalition owner first second
            firstQuits secondQuits),
        isUniformEquilibriumPayoff_purePaidBaseLeave_deletedStable
          reward source stable floor⟩
  have hfailure :
      ¬ (if firstQuits then
          0 ≤ purePaidDeletedFirstDifference reward owner first second secondQuits
        else
          purePaidDeletedFirstDifference reward owner first second secondQuits ≤ 0) ∨
      ¬ (if secondQuits then
          0 ≤ purePaidDeletedSecondDifference reward owner first second firstQuits
        else
          purePaidDeletedSecondDifference reward owner first second firstQuits ≤ 0) ∨
      ¬ purePaidOwnerFloorExcess reward owner first second
        firstQuits secondQuits ≤ 0 := by
    unfold IsPurePaidDeletedStable at hnot
    tauto
  cases firstQuits <;> cases secondQuits <;>
    simpa [HasPurePaidSingletonResidual] using hfailure

/-- Exact membership-toggle screen after deleting the remaining base owner.
The three fields correspond to retained members, the other free labels, and
the originally paid label. -/
structure PurePaidSureExitScreen
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (paid first second : ι) (firstQuits secondQuits : Bool) : Prop where
  member : ∀ who ∈ purePaidRetainedSet first second firstQuits secondQuits,
    quittingSetReward reward
        ((purePaidRetainedSet first second
          firstQuits secondQuits).erase who) who ≤
      quittingSetReward reward
        (purePaidRetainedSet first second firstQuits secondQuits) who
  freeOutsider : ∀ who ∈ ({first, second} : Finset ι),
    who ∉ purePaidRetainedSet first second firstQuits secondQuits →
      quittingSetReward reward
          (insert who (purePaidRetainedSet first second
            firstQuits secondQuits)) who ≤
        quittingSetReward reward
          (purePaidRetainedSet first second firstQuits secondQuits) who
  paidOutsider :
    quittingSetReward reward
        (insert paid (purePaidRetainedSet first second
          firstQuits secondQuits)) paid ≤
      quittingSetReward reward
        (purePaidRetainedSet first second firstQuits secondQuits) paid

/-- Literal strict negation of the three sure-exit screen fields. -/
def HasPurePaidSureExitResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (paid first second : ι) (firstQuits secondQuits : Bool) : Prop :=
  (∃ who ∈ purePaidRetainedSet first second firstQuits secondQuits,
    quittingSetReward reward
        (purePaidRetainedSet first second firstQuits secondQuits) who <
      quittingSetReward reward
        ((purePaidRetainedSet first second
          firstQuits secondQuits).erase who) who) ∨
  (∃ who ∈ ({first, second} : Finset ι),
    who ∉ purePaidRetainedSet first second firstQuits secondQuits ∧
      quittingSetReward reward
          (purePaidRetainedSet first second firstQuits secondQuits) who <
        quittingSetReward reward
          (insert who (purePaidRetainedSet first second
            firstQuits secondQuits)) who) ∨
  quittingSetReward reward
      (purePaidRetainedSet first second firstQuits secondQuits) paid <
    quittingSetReward reward
      (insert paid (purePaidRetainedSet first second
        firstQuits secondQuits)) paid

omit [Fintype ι] in
theorem not_purePaidSureExitScreen_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (paid first second : ι) (firstQuits secondQuits : Bool) :
    ¬ PurePaidSureExitScreen reward paid first second
        firstQuits secondQuits ↔
      HasPurePaidSureExitResidual reward paid first second
        firstQuits secondQuits := by
  constructor
  · intro hnot
    by_contra hresidual
    apply hnot
    refine {
      member := ?_
      freeOutsider := ?_
      paidOutsider := ?_ }
    · intro who hwho
      by_contra hfail
      apply hresidual
      exact Or.inl ⟨who, hwho, lt_of_not_ge hfail⟩
    · intro who hfree hout
      by_contra hfail
      apply hresidual
      exact Or.inr (Or.inl ⟨who, hfree, hout, lt_of_not_ge hfail⟩)
    · by_contra hfail
      apply hresidual
      exact Or.inr (Or.inr (lt_of_not_ge hfail))
  · intro residual screen
    rcases residual with hmember | hfree | hpaid
    · obtain ⟨who, hwho, hstrict⟩ := hmember
      exact (not_lt_of_ge (screen.member who hwho)) hstrict
    · obtain ⟨who, hwho, hout, hstrict⟩ := hfree
      exact (not_lt_of_ge (screen.freeOutsider who hwho hout)) hstrict
    · exact (not_lt_of_ge screen.paidOutsider) hpaid

/-- **Sure-exit descent.** At a nonempty retained cell, positive owner-floor
excess is exactly the remaining owner's strict outsider no-join inequality.
Together with the displayed membership-toggle screen it constructs the exact
sure-exit set and hence a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_purePaidBaseLeave_sureExit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ)
    (retainedNonempty :
      (purePaidRetainedSet first second firstQuits secondQuits).Nonempty)
    (premium : 0 < purePaidOwnerFloorExcess reward owner first second
      firstQuits secondQuits)
    (screen : PurePaidSureExitScreen reward paid first second
      firstQuits secondQuits) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSetReward reward
        (purePaidRetainedSet first second firstQuits secondQuits)) := by
  let retained := purePaidRetainedSet first second firstQuits secondQuits
  have hownerOut : owner ∉ retained := by
    intro howner
    have hsubset := purePaidRetainedSet_subset first second
      firstQuits secondQuits howner
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsubset
    exact hsubset.elim source.owner_ne_first source.owner_ne_second
  have hpaidOut : paid ∉ retained := by
    intro hpaid
    have hsubset := purePaidRetainedSet_subset first second
      firstQuits secondQuits hpaid
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsubset
    exact hsubset.elim source.paid_ne_first source.paid_ne_second
  have hpremium :
      quittingSetReward reward (insert owner retained) owner <
        quittingSetReward reward retained owner := by
    simpa [purePaidOwnerFloorExcess, retained, retainedNonempty,
      purePaidDeletedCoalition] using premium
  have hsure : IsQuittingSureExitSet reward retained := by
    constructor
    · exact screen.member
    · intro who hwho
      rcases source.exhaust who with hpaid | howner | hfirst | hsecond
      · subst who
        exact screen.paidOutsider
      · subst who
        exact hpremium.le
      · subst who
        exact screen.freeOutsider first (by simp) hwho
      · subst who
        exact screen.freeOutsider second (by simp) hwho
  exact isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
    reward hsure

/-- Under a terminal exploitability witness, every nonempty positive-premium
cell has one of the exact strict member/free-outsider/paid-outsider failures. -/
theorem QuittingTerminalExploitabilityWitness.hasPurePaidSureExitResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ)
    (retainedNonempty :
      (purePaidRetainedSet first second firstQuits secondQuits).Nonempty)
    (premium : 0 < purePaidOwnerFloorExcess reward owner first second
      firstQuits secondQuits) :
    HasPurePaidSureExitResidual reward paid first second
      firstQuits secondQuits := by
  rw [← not_purePaidSureExitScreen_iff]
  intro screen
  exact witness.not_exists_uniformEquilibriumPayoff
    ⟨quittingSetReward reward
        (purePaidRetainedSet first second firstQuits secondQuits),
      isUniformEquilibriumPayoff_purePaidBaseLeave_sureExit
        reward source retainedNonempty premium screen⟩

end GameTheory
