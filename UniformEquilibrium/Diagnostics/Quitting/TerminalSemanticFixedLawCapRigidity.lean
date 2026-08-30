/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalLawErasureDeviation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn
import UniformEquilibrium.Quitting.Classification.InstantPunishmentEquivalence
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

/-!
# Fixed-law cap rigidity at a sure-quitting base

A complete terminal law controls the behavioral cap exposed by deleting one
player while a distinct displayed player remains sure to Quit.  This file
first closes the actual-profile erasure estimate on the joint semantic/law
carrier.  It then applies that estimate to profiles with at least two sure
quitters and compares every semantic point in the same law fibre.

The comparison uses the full behavioral envelope.  It does not replace it by
a stationary cap, and it asserts uniqueness only after the complementary
coordinates are solved and the reverse total-debt inequality is supplied.
-/

noncomputable section

namespace GameTheory

open Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual Never-deviation estimate is closed under joint semantic/law
limits, with its complete explicit failure charge unchanged. -/
theorem terminalSemanticLawCarrier_envelope_ge_erasureMoment_sub_failure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (mover anchor : ι) (hne : mover ≠ anchor) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalErasureMoment reward point.2 mover anchor -
        M * quittingTerminalErasureFailureMass point.2 anchor ≤
      point.1.2 mover := by
  let constraint : Set (QuittingTerminalSemanticLawPoint ι) :=
    {candidate |
      quittingTerminalErasureMoment reward candidate.2 mover anchor -
          M * quittingTerminalErasureFailureMass candidate.2 anchor ≤
        candidate.1.2 mover}
  have hclosed : IsClosed constraint := by
    apply isClosed_le
    · exact
        ((continuous_quittingTerminalErasureMoment reward mover anchor).comp
          continuous_snd).sub
            (continuous_const.mul
              ((continuous_quittingTerminalErasureFailureMass anchor).comp
                continuous_snd))
    · fun_prop
  apply (closure_minimal ?_ hclosed) hpoint
  rintro candidate ⟨profile, rfl⟩
  exact quittingTerminalErasureMoment_sub_failure_le_envelope
    reward profile mover anchor hne hreward

/-- If the limiting law is entirely supported on finite coalitions carrying
the displayed anchor, its erasure moment is literally below the full
behavioral cap. -/
theorem terminalSemanticLawCarrier_envelope_ge_erasureMoment_of_sureMember
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (mover anchor : ι) (hne : mover ≠ anchor)
    (hnever : point.2 none = 0)
    (homit : ∀ terminal : {S : Finset ι // S.Nonempty},
      anchor ∉ terminal.val → point.2 (some terminal) = 0) :
    quittingTerminalErasureMoment reward point.2 mover anchor ≤
      point.1.2 mover := by
  have hfailure : quittingTerminalErasureFailureMass point.2 anchor = 0 := by
    unfold quittingTerminalErasureFailureMass
    rw [hnever, zero_add]
    apply Finset.sum_eq_zero
    intro terminal hterminal
    exact homit terminal (Finset.mem_filter.mp hterminal).2
  simpa [hfailure] using
    terminalSemanticLawCarrier_envelope_ge_erasureMoment_sub_failure
      reward point hpoint mover anchor hne
        (abs_reward_le_quittingRewardBound reward)

/-- A root/continuation splice whose root contains one sure quitter has no
Never mass and no finite terminal mass outside that quitter's incidence
face. -/
theorem quittingTerminalErasureFailureMass_rootThenContinuation_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (anchor : ι) (hanchor : root anchor = PMF.pure true) :
    quittingTerminalErasureFailureMass
        (quittingTerminalOutcomeMass reward
          (quittingRootThenContinuationProfile reward root continuation))
        anchor = 0 := by
  have hcontinue : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hanchor
  unfold quittingTerminalErasureFailureMass
  rw [quittingTerminalOutcomeMass_rootThenContinuation, hcontinue,
    zero_mul, zero_add]
  apply Finset.sum_eq_zero
  intro terminal hterminal
  simp only [quittingTerminalOutcomeMass_rootThenContinuation, hcontinue,
    zero_mul, add_zero]
  have hle := quittingRootCoalitionMass_le_continueProbability_of_not_mem
    root terminal.val anchor (Finset.mem_filter.mp hterminal).2
  have hnonneg := quittingRootCoalitionMass_nonneg root terminal.val
  rw [hanchor] at hle
  simp only [PMF.pure_apply, Bool.false_eq_true, ↓reduceIte,
    ENNReal.toReal_zero] at hle
  exact le_antisymm hle hnonneg

/-- At a root with two distinct sure quitters, a displayed member's exact
behavioral cap is the better of its prescribed payoff and the erasure moment
obtained by deleting it while retaining the other sure quitter. -/
theorem quittingSureBaseRoot_envelope_eq_max_prescribed_erasureMoment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (mover anchor : ι) (hne : mover ≠ anchor)
    (hmover : root mover = PMF.pure true)
    (hanchor : root anchor = PMF.pure true) :
    let profile :=
      quittingRootThenContinuationProfile reward root continuation
    quittingContinuationBestResponseValue reward profile mover =
      max (quittingTerminalPayoff reward profile mover)
        (quittingTerminalErasureMoment reward
          (quittingTerminalOutcomeMass reward profile) mover anchor) := by
  let profile := quittingRootThenContinuationProfile reward root continuation
  let tail : Payoff ι := fun player =>
    quittingTerminalPayoff reward continuation player
  let bestTail : Payoff ι := Function.update tail mover
    (quittingContinuationBestResponseValue reward continuation mover)
  have hupdatedMass : quittingStationaryContinueMass
      (Function.update root mover (PMF.pure false)) = 0 :=
    quittingStationaryContinueMass_update_of_sureQuitter
      hne hanchor (PMF.pure false)
  have hprescribed : quittingTerminalPayoff reward profile mover =
      quittingRootQuitPayoff reward tail root mover := by
    rw [show quittingTerminalPayoff reward profile mover =
        quittingRootSuccessorPayoff reward tail root mover by
      exact quittingTerminalPayoff_rootThenContinuation_eq
        reward root continuation mover]
    rw [quittingRootSuccessorPayoff_eq_endpointMix, hmover]
    simp
  have hcontinue : quittingRootContinuePayoff reward bestTail root mover =
      quittingRootAbsorbingContribution reward
        (Function.update root mover (PMF.pure false)) mover := by
    unfold quittingRootContinuePayoff
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
      hupdatedMass, zero_mul, add_zero]
  have hnever : quittingTerminalPayoff reward
      (Function.update profile mover
        (quittingPureTimeBehaviorStrategy reward mover none)) mover =
      quittingRootAbsorbingContribution reward
        (Function.update root mover (PMF.pure false)) mover := by
    apply quittingTerminalPayoff_update_of_sureAbsorbingDeviatedRow
    simpa [profile, quittingBehaviorLiveHazard,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard_none] using
        hupdatedMass
  have herasure :=
    quittingTerminalErasureMoment_eq_update_never_payoff_of_failure_eq_zero
      reward profile mover anchor hne
        (quittingTerminalErasureFailureMass_rootThenContinuation_eq_zero
          reward root continuation anchor hanchor)
  dsimp only
  rw [quittingContinuationBestResponseValue_rootThenContinuation_eq_max]
  change max (quittingRootQuitPayoff reward tail root mover)
      (quittingRootContinuePayoff reward bestTail root mover) = _
  rw [← hprescribed, hcontinue, ← hnever, ← herasure]

/-- Two joint-carrier points with the same complete terminal law have the
same prescribed payoff vector. -/
theorem terminalSemanticLawCarrier_prescribed_eq_of_sameLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (hfirst : (first, mass) ∈ quittingTerminalSemanticLawCarrier reward)
    (hsecond : (second, mass) ∈ quittingTerminalSemanticLawCarrier reward) :
    first.1 = second.1 := by
  rw [← terminalSemanticLawCarrier_rewardMoment reward (first, mass) hfirst,
    ← terminalSemanticLawCarrier_rewardMoment reward (second, mass) hsecond]

/-- On every member of a sure-quitting base of cardinality at least two, the
literal root/continuation splice has no larger behavioral cap than any joint
carrier point in the same complete-law fibre.  The prescribed payoff vectors
are also literally equal. -/
theorem quittingSureBaseRoot_cap_le_sameLaw_on_base
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : Finset ι) (hcard : 2 ≤ base.card)
    (root : ι → PMF Bool)
    (hsure : ∀ member ∈ base, root member = PMF.pure true)
    (continuation : (quittingGame reward).BehaviorProfile)
    (returned : QuittingTerminalSemanticPair ι)
    (hreturned :
      (returned, quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward root continuation)) ∈
          quittingTerminalSemanticLawCarrier reward) :
    let source := quittingTerminalSemanticPair reward
      (quittingRootThenContinuationProfile reward root continuation)
    returned.1 = source.1 ∧
      ∀ mover ∈ base, source.2 mover ≤ returned.2 mover := by
  let profile := quittingRootThenContinuationProfile reward root continuation
  let source := quittingTerminalSemanticPair reward profile
  let mass := quittingTerminalOutcomeMass reward profile
  have hsource : (source, mass) ∈
      quittingTerminalSemanticLawCarrier reward :=
    quittingTerminalSemanticLawPoint_mem_carrier reward profile
  have hprescribed : returned.1 = source.1 :=
    terminalSemanticLawCarrier_prescribed_eq_of_sameLaw
      reward returned source mass hreturned hsource
  refine ⟨hprescribed, ?_⟩
  intro mover hmover
  obtain ⟨anchor, hanchor, hanchorNe⟩ :=
    base.exists_mem_ne (by omega : 1 < base.card) mover
  have hidentity :=
    quittingSureBaseRoot_envelope_eq_max_prescribed_erasureMoment
      reward root continuation mover anchor hanchorNe.symm
        (hsure mover hmover) (hsure anchor hanchor)
  have hfailure :=
    quittingTerminalErasureFailureMass_rootThenContinuation_eq_zero
      reward root continuation anchor (hsure anchor hanchor)
  have herasure : quittingTerminalErasureMoment reward mass mover anchor ≤
      returned.2 mover := by
    have hbound :=
      terminalSemanticLawCarrier_envelope_ge_erasureMoment_sub_failure
        reward (returned, mass) hreturned mover anchor hanchorNe.symm
          (abs_reward_le_quittingRewardBound reward)
    have hfailure' : quittingTerminalErasureFailureMass mass anchor = 0 :=
      hfailure
    rw [hfailure', mul_zero, sub_zero] at hbound
    exact hbound
  have hreturnedCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier (returned, mass) hreturned
  have hprescribedLe : source.1 mover ≤ returned.2 mover := by
    have hdebt := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hreturnedCarrier mover
    unfold quittingTerminalSemanticDebt at hdebt
    rw [hprescribed] at hdebt
    linarith
  change source.2 mover ≤ returned.2 mover
  rw [show source.2 mover = max (source.1 mover)
      (quittingTerminalErasureMoment reward mass mover anchor) by
    simpa only [profile, source, mass, quittingTerminalSemanticPair] using
      hidentity]
  exact max_le hprescribedLe herasure

/-- If all coordinates outside the sure base are solved at the literal
source, the same-law cap comparison holds for every player. -/
theorem quittingSureBaseRoot_cap_le_sameLaw_of_complement_solved
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : Finset ι) (hcard : 2 ≤ base.card)
    (root : ι → PMF Bool)
    (hsure : ∀ member ∈ base, root member = PMF.pure true)
    (continuation : (quittingGame reward).BehaviorProfile)
    (returned : QuittingTerminalSemanticPair ι)
    (hreturned :
      (returned, quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward root continuation)) ∈
          quittingTerminalSemanticLawCarrier reward)
    (hsolved : ∀ player, player ∉ base →
      let source := quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward root continuation)
      source.2 player = source.1 player) :
    let source := quittingTerminalSemanticPair reward
      (quittingRootThenContinuationProfile reward root continuation)
    returned.1 = source.1 ∧ ∀ player, source.2 player ≤ returned.2 player := by
  let profile := quittingRootThenContinuationProfile reward root continuation
  let source := quittingTerminalSemanticPair reward profile
  let mass := quittingTerminalOutcomeMass reward profile
  have hbase := quittingSureBaseRoot_cap_le_sameLaw_on_base
    reward base hcard root hsure continuation returned hreturned
  obtain ⟨hprescribed, hbaseCap⟩ := hbase
  refine ⟨hprescribed, ?_⟩
  intro player
  by_cases hplayer : player ∈ base
  · exact hbaseCap player hplayer
  · have hreturnedCarrier :=
      terminalSemanticLawCarrier_fst_mem_carrier (returned, mass) hreturned
    have hdebt := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hreturnedCarrier player
    unfold quittingTerminalSemanticDebt at hdebt
    rw [hprescribed] at hdebt
    rw [hsolved player hplayer]
    linarith

/-- Under a solved complement, the literal sure-base source minimizes total
semantic debt throughout its complete-law fibre. -/
theorem quittingSureBaseRoot_debt_le_sameLaw_of_complement_solved
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : Finset ι) (hcard : 2 ≤ base.card)
    (root : ι → PMF Bool)
    (hsure : ∀ member ∈ base, root member = PMF.pure true)
    (continuation : (quittingGame reward).BehaviorProfile)
    (returned : QuittingTerminalSemanticPair ι)
    (hreturned :
      (returned, quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward root continuation)) ∈
          quittingTerminalSemanticLawCarrier reward)
    (hsolved : ∀ player, player ∉ base →
      let source := quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward root continuation)
      source.2 player = source.1 player) :
    let source := quittingTerminalSemanticPair reward
      (quittingRootThenContinuationProfile reward root continuation)
    quittingTerminalSemanticDebtSum source ≤
      quittingTerminalSemanticDebtSum returned := by
  let profile := quittingRootThenContinuationProfile reward root continuation
  let source := quittingTerminalSemanticPair reward profile
  obtain ⟨hprescribed, hcap⟩ :=
    quittingSureBaseRoot_cap_le_sameLaw_of_complement_solved
      reward base hcard root hsure continuation returned hreturned hsolved
  unfold quittingTerminalSemanticDebtSum
  apply Finset.sum_le_sum
  intro player _
  unfold quittingTerminalSemanticDebt
  rw [hprescribed]
  exact sub_le_sub_right (hcap player) _

/-- The literal sure-base source is the unique debt minimizer in its fixed-law
fibre once the complement is solved: a reverse debt inequality forces the
complete semantic pair, including every cap coordinate, to agree. -/
theorem quittingSureBaseRoot_unique_fixedLawDebtMinimizer_of_complement_solved
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : Finset ι) (hcard : 2 ≤ base.card)
    (root : ι → PMF Bool)
    (hsure : ∀ member ∈ base, root member = PMF.pure true)
    (continuation : (quittingGame reward).BehaviorProfile)
    (returned : QuittingTerminalSemanticPair ι)
    (hreturned :
      (returned, quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward root continuation)) ∈
          quittingTerminalSemanticLawCarrier reward)
    (hsolved : ∀ player, player ∉ base →
      let source := quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward root continuation)
      source.2 player = source.1 player)
    (hreturnedDebt :
      let source := quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward root continuation)
      quittingTerminalSemanticDebtSum returned ≤
        quittingTerminalSemanticDebtSum source) :
    returned = quittingTerminalSemanticPair reward
      (quittingRootThenContinuationProfile reward root continuation) := by
  let profile := quittingRootThenContinuationProfile reward root continuation
  let source := quittingTerminalSemanticPair reward profile
  obtain ⟨hprescribed, hcap⟩ :=
    quittingSureBaseRoot_cap_le_sameLaw_of_complement_solved
      reward base hcard root hsure continuation returned hreturned hsolved
  have hsourceDebt := quittingSureBaseRoot_debt_le_sameLaw_of_complement_solved
    reward base hcard root hsure continuation returned hreturned hsolved
  have hdebtEq : quittingTerminalSemanticDebtSum source =
      quittingTerminalSemanticDebtSum returned := le_antisymm hsourceDebt hreturnedDebt
  have hcoordinateDebt : ∀ player,
      quittingTerminalSemanticDebt source player =
        quittingTerminalSemanticDebt returned player := by
    intro player
    apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) ?_).mp hdebtEq
      player (Finset.mem_univ player)
    intro candidate _
    unfold quittingTerminalSemanticDebt
    rw [hprescribed]
    exact sub_le_sub_right (hcap candidate) _
  apply Prod.ext hprescribed
  funext player
  have hdebt := hcoordinateDebt player
  unfold quittingTerminalSemanticDebt at hdebt
  rw [hprescribed] at hdebt
  linarith

end GameTheory
