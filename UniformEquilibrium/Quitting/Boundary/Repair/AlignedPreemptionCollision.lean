/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.CollisionRepairCharacterization
import UniformEquilibrium.Quitting.Classification.PreemptionGeometry

/-!
# Aligned preemption and collision repair

An immediate singleton collision and an outgoing solo-preemption edge align
when the collider is also the owner's preemptor.  In the collider's payoff
coordinate, both quitting alone and joining the owner then beat the owner's
solo exit by the common margin.

Two exact interfaces separate what this alignment does and does not provide.

* A sequential two-solo profile first lets the owner quit and, after survival,
  lets the collider quit.  The collider's legal phase-zero Quit gain is exactly
  the first-stage rate times the collision gain.  The solo-preemption edge is
  not part of this identity.  Thus the abstract two-row rotation defect is not
  by itself a source-matched periodic deviation theorem.
* In the simultaneous collision-repair row, alignment gives a uniform lower
  bound for the collider's prescribed mixture.  Combined with one scalar
  punishment-floor bound, the existing exact collision-repair
  characterization reduces to owner optimality and spectator no-join.

The first interface is a necessary screen calculation.  The second is a
necessary-and-sufficient repair criterion under the displayed automatic
blocker-floor hypothesis.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {player : Type} [Fintype player] [DecidableEq player]
variable {reward : {S : Finset player // S.Nonempty} → Payoff player}

/-! ## The sequential two-solo screen -/

/-- First let `owner` quit at `rate`; after survival, let `follower` quit
surely. -/
def quittingSequentialSoloProfile
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (owner follower : player) (rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingOneStagePunishedProfile reward
    (quittingSureSetOwnerRoot ∅ owner rate hrate0 hrate1)
    (quittingPureSetRoot {follower})

/-- The prescribed payoff of the sequential two-solo screen. -/
def quittingSequentialSoloValue
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (owner follower : player) (rate : ℝ) : Payoff player :=
  fun who ↦
    rate * quittingSoloReward reward owner who +
      (1 - rate) * quittingSoloReward reward follower who

/-- The sequential screen delivers the corresponding convex combination of
the two solo rows. -/
theorem quittingTerminalPayoff_sequentialSoloProfile
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (owner follower who : player) (rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingTerminalPayoff reward
        (quittingSequentialSoloProfile reward owner follower rate hrate0 hrate1)
        who =
      quittingSequentialSoloValue reward owner follower rate who := by
  have htail : quittingRootSequenceTerminalValue reward
      (fun _ ↦ quittingPureSetRoot ({follower} : Finset player)) who 0 =
        quittingSoloReward reward follower who := by
    calc
      quittingRootSequenceTerminalValue reward
          (fun _ ↦ quittingPureSetRoot ({follower} : Finset player)) who 0 =
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward
            (quittingPureSetRoot ({follower} : Finset player))) who := by
              rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
                quittingProfileLiveRoot_stationary]
      _ = quittingSoloReward reward follower who := by
        rw [quittingTerminalPayoff_pureSetRoot,
          quittingSetReward_singleton_eq_soloReward]
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingSequentialSoloProfile, quittingOneStagePunishedProfile,
    quittingProfileLiveRoot_quittingPhaseSwitchProfile,
    quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots,
    quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum,
    Finset.sum_range_one, quittingJointSurvivalWeight_eq_prod,
    Finset.prod_range_zero, one_mul,
    quittingRootAbsorbingContribution_sureSetOwnerRoot reward (by simp)
      rate hrate0 hrate1 who,
    quittingSureSetOwnerValue_empty,
    quittingSetReward_singleton_eq_soloReward,
    htail, quittingJointSurvivalWeight_eq_prod, Finset.prod_range_one,
    stationaryContinueMass_sureSetOwnerRoot_empty]
  rfl

/-- If the follower quits immediately instead, its payoff is the mixture of
its solo row and its collision with the owner. -/
theorem quittingTerminalPayoff_update_sequentialSoloProfile_follower_quitNow
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    {owner follower : player} (hne : follower ≠ owner)
    (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingSequentialSoloProfile reward owner follower rate hrate0 hrate1)
          follower (fun _ _ ↦ (PMF.pure true : PMF Bool))) follower =
      (1 - rate) * quittingSoloReward reward follower follower +
        rate * quittingSingletonCollisionReward reward owner follower := by
  rw [quittingTerminalPayoff_update_quitNow,
    quittingSequentialSoloProfile,
    quittingProfileLiveRoot_oneStagePunishedProfile_zero,
    fixedOpponentsQuitValue_sureSetOwnerRoot_other reward (by simp)
      hne rate hrate0 hrate1]
  unfold quittingSureSetOwnerValue
  change
    (1 - rate) *
          quittingSetReward reward ({follower} : Finset player) follower +
        rate * quittingSetReward reward ({owner, follower} : Finset player)
          follower =
      (1 - rate) * quittingSoloReward reward follower follower +
        rate * quittingSingletonCollisionReward reward owner follower
  rw [quittingSetReward_singleton_eq_soloReward,
    quittingSetReward_pair_right]

/-- **Source-matched two-stage identity.**  The follower's legal phase-zero
gain is the first-stage rate times the collision gain.  The preemption
inequality between the two solo rows does not enter this formula. -/
theorem quittingSequentialSoloProfile_follower_gain_eq
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    {owner follower : player} (hne : follower ≠ owner)
    (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingTerminalPayoff reward
          (Function.update
            (quittingSequentialSoloProfile reward owner follower rate hrate0
              hrate1)
            follower (fun _ _ ↦ (PMF.pure true : PMF Bool))) follower -
        quittingTerminalPayoff reward
          (quittingSequentialSoloProfile reward owner follower rate hrate0
            hrate1) follower =
      rate * (quittingSingletonCollisionReward reward owner follower -
        quittingSoloReward reward owner follower) := by
  rw [quittingTerminalPayoff_update_sequentialSoloProfile_follower_quitNow
      reward hne rate hrate0 hrate1,
    quittingTerminalPayoff_sequentialSoloProfile]
  unfold quittingSequentialSoloValue
  ring

/-- A collision certificate therefore blocks every positive-rate sequential
two-solo screen by the rate-scaled collision margin. -/
theorem QuittingImmediateSingletonCollision.rate_mul_margin_le_sequentialGain
    {margin rate : ℝ}
    (certificate : QuittingImmediateSingletonCollision reward margin)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    rate * margin ≤
      quittingTerminalPayoff reward
          (Function.update
            (quittingSequentialSoloProfile reward certificate.owner
              certificate.collider rate hrate0 hrate1)
            certificate.collider (fun _ _ ↦ (PMF.pure true : PMF Bool)))
            certificate.collider -
        quittingTerminalPayoff reward
          (quittingSequentialSoloProfile reward certificate.owner
            certificate.collider rate hrate0 hrate1) certificate.collider := by
  rw [quittingSequentialSoloProfile_follower_gain_eq reward
    certificate.collider_ne_owner rate hrate0 hrate1]
  apply mul_le_mul_of_nonneg_left _ hrate0
  linarith [certificate.collider_gain_floor]

/-- With positive rate and margin, the collider has a strictly profitable
immediate deviation from the sequential two-solo screen. -/
theorem QuittingImmediateSingletonCollision.sequentialGain_pos
    {margin rate : ℝ}
    (certificate : QuittingImmediateSingletonCollision reward margin)
    (hmargin : 0 < margin) (hrate : 0 < rate) (hrate1 : rate ≤ 1) :
    0 <
      quittingTerminalPayoff reward
          (Function.update
            (quittingSequentialSoloProfile reward certificate.owner
              certificate.collider rate hrate.le hrate1)
            certificate.collider (fun _ _ ↦ (PMF.pure true : PMF Bool)))
            certificate.collider -
        quittingTerminalPayoff reward
          (quittingSequentialSoloProfile reward certificate.owner
            certificate.collider rate hrate.le hrate1) certificate.collider := by
  exact (mul_pos hrate hmargin).trans_le
    (certificate.rate_mul_margin_le_sequentialGain hrate.le hrate1)

/-! ## Alignment inside the exact collision repair -/

omit [Fintype player] in
/-- At an aligned collision/preemption edge, every legal collision-repair
mixture pays the collider at least the owner's solo coordinate plus the
common margin. -/
theorem QuittingImmediateSingletonCollision.alignedCollider_floor_repairValue
    {margin rate : ℝ}
    (certificate : QuittingImmediateSingletonCollision reward margin)
    (haligned : QuittingSoloPreempts reward margin certificate.owner
      certificate.collider)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingSoloReward reward certificate.owner certificate.collider + margin ≤
      quittingCollisionRepairValue reward certificate.owner
        certificate.collider rate certificate.collider := by
  rw [quittingCollisionRepairValue_apply,
    quittingSetReward_singleton_eq_soloReward,
    quittingSetReward_pair_right]
  have hweight : 0 ≤ 1 - rate := sub_nonneg.mpr hrate1
  have hsolo := mul_le_mul_of_nonneg_left haligned.2 hweight
  have hcollision := mul_le_mul_of_nonneg_left
    certificate.collider_gain_floor hrate0
  nlinarith

/-- If the blocker's continuation floor is already below the aligned common
floor, the blocker-balance condition of collision repair is automatic. -/
theorem QuittingImmediateSingletonCollision.blockerBalance_of_aligned
    {margin rate : ℝ}
    (certificate : QuittingImmediateSingletonCollision reward margin)
    (haligned : QuittingSoloPreempts reward margin certificate.owner
      certificate.collider)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1)
    (hfloor :
      rate * quittingSoloReward reward certificate.owner certificate.collider +
          (1 - rate) * quittingPunishmentValue reward certificate.collider ≤
        quittingSoloReward reward certificate.owner certificate.collider +
          margin) :
    QuittingCollisionBlockerBalance reward certificate.owner
      certificate.collider rate := by
  have hrepair := certificate.alignedCollider_floor_repairValue haligned
    hrate0 hrate1
  unfold QuittingCollisionBlockerBalance
  rw [quittingSetReward_singleton_eq_soloReward]
  exact hfloor.trans hrepair

/-- **Aligned repair characterization.**  Under the one scalar bound making
the collider's floor automatic, the collision mechanism works exactly when
the owner's endpoints are optimal and every spectator declines to join.
These two residual conditions are both necessary and sufficient. -/
theorem QuittingImmediateSingletonCollision.collisionRepairWorks_iff_of_aligned
    {margin rate : ℝ}
    (certificate : QuittingImmediateSingletonCollision reward margin)
    (haligned : QuittingSoloPreempts reward margin certificate.owner
      certificate.collider)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1)
    (hfloor :
      rate * quittingSoloReward reward certificate.owner certificate.collider +
          (1 - rate) * quittingPunishmentValue reward certificate.collider ≤
        quittingSoloReward reward certificate.owner certificate.collider +
          margin) :
    QuittingCollisionRepairWorks reward certificate.owner certificate.collider
        rate hrate0 hrate1 ↔
      QuittingCollisionOwnerOptimal reward certificate.owner
          certificate.collider rate ∧
        QuittingCollisionSpectatorNoJoin reward certificate.owner
          certificate.collider rate := by
  rw [quittingCollisionRepairWorks_iff reward
    (Ne.symm certificate.collider_ne_owner) hrate0 hrate1]
  constructor
  · exact fun h ↦ ⟨h.1, h.2.1⟩
  · rintro ⟨howner, hspectator⟩
    exact ⟨howner, hspectator,
      certificate.blockerBalance_of_aligned haligned hrate0 hrate1 hfloor⟩

/-! ## Local feasibility -/

/-- **The aligned local conditions are jointly feasible.**  If an irreflexive
relation contains both edges between the marked owner and collider, its
universal geometry table has the collision certificate, both preemption
edges, and an exact collision repair at rate one.  Thus collision plus an
aligned two-cycle is not a local contradiction; excluding it requires
information beyond the recorded table geometry. -/
theorem preemptionGeometryReward_twoCycle_and_collisionRepairWorks
    (R : player → player → Prop) [DecidableRel R]
    (hirreflexive : ∀ who, ¬ R who who)
    {owner collider : player} (hne : collider ≠ owner)
    (hforward : R owner collider) (hback : R collider owner) :
    Nonempty (QuittingImmediateSingletonCollision
      (quittingPreemptionGeometryReward R owner collider) 1) ∧
      QuittingSoloPreempts
        (quittingPreemptionGeometryReward R owner collider) 1 owner collider ∧
      QuittingSoloPreempts
        (quittingPreemptionGeometryReward R owner collider) 1 collider owner ∧
      QuittingCollisionRepairWorks
        (quittingPreemptionGeometryReward R owner collider)
        owner collider 1 (by norm_num) (by norm_num) := by
  have hpairOwner : ({owner, collider} : Finset player) ≠ {owner} := by
    intro heq
    have hmem : collider ∈ ({owner} : Finset player) := by
      rw [← heq]
      simp
    exact hne (by simpa using hmem)
  refine ⟨⟨quittingPreemptionGeometryCollision R hne⟩,
    (quittingSoloPreempts_preemptionGeometryReward_iff
      R hirreflexive hne).2 hforward,
    (quittingSoloPreempts_preemptionGeometryReward_iff
      R hirreflexive hne).2 hback, ?_⟩
  apply (quittingCollisionRepairWorks_iff _ (Ne.symm hne)
    (by norm_num) (by norm_num)).2
  refine ⟨?_, ?_, ?_⟩
  · unfold QuittingCollisionOwnerOptimal
    rw [quittingCollisionRepairValue_apply]
    norm_num [quittingSetReward, quittingPreemptionGeometryReward,
      quittingPreemptionRelationSetReward,
      quittingPreemptionRelationSoloReward, hpairOwner, hne, Ne.symm hne,
      hback]
  · intro spectator hspectatorOwner hspectatorCollider
    have htripleOwner :
        ({owner, spectator, collider} : Finset player) ≠ {owner} := by
      intro heq
      have hmem : collider ∈ ({owner} : Finset player) := by
        rw [← heq]
        simp
      exact hne (by simpa using hmem)
    have htripleSpectator :
        ({owner, spectator, collider} : Finset player) ≠ {spectator} := by
      intro heq
      have hmem : owner ∈ ({spectator} : Finset player) := by
        rw [← heq]
        simp
      have hequal : owner = spectator := by simpa using hmem
      exact hspectatorOwner hequal.symm
    have htripleCollider :
        ({owner, spectator, collider} : Finset player) ≠ {collider} := by
      intro heq
      have hmem : owner ∈ ({collider} : Finset player) := by
        rw [← heq]
        simp
      have hequal : owner = collider := by simpa using hmem
      exact hne hequal.symm
    unfold quittingCollisionRepairValue
    norm_num [quittingSureSetOwnerValue, quittingSetReward,
      quittingPreemptionGeometryReward, quittingPreemptionRelationSetReward,
      hpairOwner, htripleOwner, htripleSpectator, htripleCollider,
      hspectatorOwner, Ne.symm hspectatorOwner, hspectatorCollider,
      Ne.symm hspectatorCollider, hne, Ne.symm hne]
  · unfold QuittingCollisionBlockerBalance
    rw [quittingCollisionRepairValue_apply]
    simp only [one_mul, sub_self, zero_mul, zero_add]
    rw [quittingSetReward_singleton_eq_soloReward,
      quittingSetReward_pair_right,
      quittingPreemptionGeometryReward_solo R hne,
      quittingPreemptionGeometryReward_collision R hne]
    norm_num

end GameTheory
