/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseNashSemanticAdapter
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.SingletonBaseSemanticDispatch
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine

/-!
# Concrete persistent-base excess and compact Nash gap

The screen below is the literal finite maximum of the base-leave and
outsider-join payoff excesses.  It is evaluated on the actual ambient product
root induced by a mixed point of the free-player game.  Free coordinates are
zero in the maximum because their inequalities are already exactly the
induced Nash conditions.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Simplex presentation of the actual ambient persistent-base root. -/
def quittingPersistentBaseSimplexRoot
    (base free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) :
    QuittingRootSimplex ι :=
  fun who => if _hbase : who ∈ base then stdSimplexEquiv (PMF.pure true)
    else if hfree : who ∈ free then
      ⟨point.1 ⟨who, hfree⟩,
        (mem_mixedPolytope (quittingBinaryForm free).sig).1 point.2
          ⟨who, hfree⟩⟩
    else stdSimplexEquiv (PMF.pure false)

omit [Nonempty ι] in
/-- The simplex presentation converts back to the actual extended PMF root. -/
theorem quittingRootOfSimplex_persistentBaseSimplexRoot
    (base free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) :
    quittingRootOfSimplex (quittingPersistentBaseSimplexRoot base free point) =
      quittingPersistentBaseRoot base free point := by
  funext who
  apply toVector_injective
  funext action
  unfold toVector
  rw [quittingRootOfSimplex_apply_toReal]
  by_cases hbase : who ∈ base
  · simp [quittingPersistentBaseSimplexRoot, quittingPersistentBaseRoot,
      quittingPersistentBaseRootOfProfile, hbase, coe_stdSimplexEquiv_apply,
      toVector]
  · by_cases hfree : who ∈ free
    · simp only [quittingPersistentBaseSimplexRoot, hbase, hfree,
        ↓reduceDIte, quittingPersistentBaseRoot,
        quittingPersistentBaseRootOfProfile]
      change point.1 ⟨who, hfree⟩ action =
        (ofPolytope (quittingBinaryForm free).sig point.2 ⟨who, hfree⟩).prob action
      exact (congrFun (congrFun
        (probs_ofPolytope (quittingBinaryForm free).sig point.2)
        ⟨who, hfree⟩) action).symm
    · simp [quittingPersistentBaseSimplexRoot, quittingPersistentBaseRoot,
        quittingPersistentBaseRootOfProfile, hbase, hfree,
        coe_stdSimplexEquiv_apply, toVector]

omit [Nonempty ι] in
/-- The ambient simplex root depends continuously on the induced mixed point. -/
theorem continuous_quittingPersistentBaseSimplexRoot
    (base free : Finset ι) :
    Continuous (quittingPersistentBaseSimplexRoot base free) := by
  apply continuous_pi
  intro who
  by_cases hbase : who ∈ base
  · simpa [quittingPersistentBaseSimplexRoot, hbase] using
      (continuous_const : Continuous fun _ :
        mixedPolytope (quittingBinaryForm free).sig =>
          stdSimplexEquiv (PMF.pure true))
  · by_cases hfree : who ∈ free
    · let freeWho : ↥free := ⟨who, hfree⟩
      have hcoordinate : Continuous fun point :
          mixedPolytope (quittingBinaryForm free).sig =>
            point.1 freeWho :=
        (continuous_apply freeWho).comp continuous_subtype_val
      have hsimplex : Continuous fun point :
          mixedPolytope (quittingBinaryForm free).sig =>
            (⟨point.1 freeWho,
              (mem_mixedPolytope (quittingBinaryForm free).sig).1 point.2
                freeWho⟩ : stdSimplex ℝ Bool) :=
        hcoordinate.subtype_mk _
      simpa [quittingPersistentBaseSimplexRoot, hbase, hfree] using hsimplex
    · simpa [quittingPersistentBaseSimplexRoot, hbase, hfree] using
        (continuous_const : Continuous fun _ :
          mixedPolytope (quittingBinaryForm free).sig =>
            stdSimplexEquiv (PMF.pure false))

/-- Large-base component excess: leave excess on the base, join excess on
outsiders, and zero on free players. -/
def quittingPersistentLargeBaseComponent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) (who : ι) : ℝ :=
  if who ∈ base then
    -quittingRootEndpointDifference reward 0
      (quittingPersistentBaseRoot base free point) who
  else if who ∈ free then 0
  else quittingRootEndpointDifference reward 0
    (quittingPersistentBaseRoot base free point) who

/-- Concrete maximum `G` for a persistent base of size at least two. -/
def quittingPersistentLargeBaseExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (quittingPersistentLargeBaseComponent reward base free point)

omit [Nonempty ι] in
/-- Every large-base component is continuous. -/
theorem continuous_quittingPersistentLargeBaseComponent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (who : ι) :
    Continuous fun point =>
      quittingPersistentLargeBaseComponent reward base free point who := by
  have hendpoint : Continuous fun point :
      mixedPolytope (quittingBinaryForm free).sig =>
      quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot base free point) who := by
    have h := (continuous_quittingRootEndpointDifference_simplex reward who).comp
      ((continuous_const : Continuous fun _ :
        mixedPolytope (quittingBinaryForm free).sig => (0 : Payoff ι)).prodMk
          (continuous_quittingPersistentBaseSimplexRoot base free))
    rw [show (fun point : mixedPolytope (quittingBinaryForm free).sig =>
        quittingRootEndpointDifference reward 0
          (quittingPersistentBaseRoot base free point) who) =
      fun point => quittingRootEndpointDifference reward 0
        (quittingRootOfSimplex
          (quittingPersistentBaseSimplexRoot base free point)) who by
      funext point
      rw [quittingRootOfSimplex_persistentBaseSimplexRoot]]
    exact h
  by_cases hbase : who ∈ base
  · simp only [quittingPersistentLargeBaseComponent, hbase, if_pos]
    convert (continuous_const.mul hendpoint : Continuous fun point =>
      (-1 : ℝ) * quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot base free point) who) using 1
    funext point
    simp
  · by_cases hfree : who ∈ free
    · simpa [quittingPersistentLargeBaseComponent, hbase, hfree] using
        (continuous_const : Continuous fun _ :
          mixedPolytope (quittingBinaryForm free).sig => (0 : ℝ))
    · simpa [quittingPersistentLargeBaseComponent, hbase, hfree] using hendpoint

/-- The concrete large-base `G` is continuous. -/
theorem continuous_quittingPersistentLargeBaseExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) :
    Continuous (quittingPersistentLargeBaseExcess reward base free) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty fun who _ =>
    continuous_quittingPersistentLargeBaseComponent reward base free who

/-- `G ≤ 0` is exactly the remaining base-leave and outsider-join sign
screen consumed by the induced-Nash semantic adapter. -/
theorem quittingPersistentLargeBaseExcess_nonpos_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) :
    quittingPersistentLargeBaseExcess reward base free point ≤ 0 ↔
      (∀ who ∈ base, 0 ≤ quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot base free point) who) ∧
      ∀ who ∉ base ∪ free,
        quittingRootEndpointDifference reward 0
          (quittingPersistentBaseRoot base free point) who ≤ 0 := by
  constructor
  · intro hscreen
    constructor
    · intro who hwho
      have hcomponent := (Finset.le_sup' (f :=
        quittingPersistentLargeBaseComponent reward base free point)
        (Finset.mem_univ who)).trans hscreen
      simpa [quittingPersistentLargeBaseComponent, hwho] using hcomponent
    · intro who hwho
      have hbase : who ∉ base := fun hmem =>
        hwho (Finset.mem_union_left free hmem)
      have hfree : who ∉ free := fun hmem =>
        hwho (Finset.mem_union_right base hmem)
      have hcomponent := (Finset.le_sup' (f :=
        quittingPersistentLargeBaseComponent reward base free point)
        (Finset.mem_univ who)).trans hscreen
      simpa [quittingPersistentLargeBaseComponent, hbase, hfree] using hcomponent
  · rintro ⟨hleave, hjoin⟩
    apply Finset.sup'_le
    intro who _
    by_cases hbase : who ∈ base
    · simpa [quittingPersistentLargeBaseComponent, hbase] using hleave who hbase
    · by_cases hfree : who ∈ free
      · simp [quittingPersistentLargeBaseComponent, hbase, hfree]
      · have houtside : who ∉ base ∪ free := by simp [hbase, hfree]
        simpa [quittingPersistentLargeBaseComponent, hbase, hfree] using
          hjoin who houtside

/-- **Concrete large-base ordered alternative.**  Either the actual induced
Nash carrier contains a semantically accepted point, or its literal `G`
screen has a uniformly positive attained compact gap. -/
theorem exists_uniformPayoff_or_persistentLargeBase_pos_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (hdisjoint : Disjoint base free)
    (hbase : 2 ≤ base.card) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ gamma : ℝ, 0 < gamma ∧
        ∀ point ∈ quittingPersistentBaseNashSet reward base free,
          gamma ≤ quittingPersistentLargeBaseExcess reward base free point := by
  rcases exists_persistentBaseNash_nonpos_or_pos_gap reward base free
      (quittingPersistentLargeBaseExcess reward base free)
      (continuous_quittingPersistentLargeBaseExcess reward base free) with
    haccepted | hgap
  · left
    apply exists_uniformPayoff_of_persistentBase_inducedNash_signs
      reward base free hdisjoint hbase
    obtain ⟨point, hpoint, hscreen⟩ := haccepted
    exact ⟨point, hpoint,
      (quittingPersistentLargeBaseExcess_nonpos_iff
        reward base free point).mp hscreen⟩
  · exact Or.inr hgap

/-! ## Singleton persistent base -/

/-- The owner's floor-priced Continue excess.  It is written as the actual
pure-Continue payoff at the exact punishment tail minus the nominal root
payoff, so continuity is immediate in product-root coordinates. -/
def quittingSingletonBaseOwnerFloorExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (root : ι → PMF Bool) : ℝ :=
  quittingRootContinuePayoff reward
      (fun _ => quittingPunishmentValue reward owner) root owner -
    quittingRootExpectedPayoff reward 0 root owner

omit [Nonempty ι] in
/-- On the literal singleton-base extension, nonpositivity of the owner
excess is exactly the floor-balance field of the semantic certificate. -/
theorem quittingSingletonBaseOwnerFloorExcess_nonpos_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) :
    quittingSingletonBaseOwnerFloorExcess reward owner
        (quittingPersistentBaseRoot {owner} free point) ≤ 0 ↔
      quittingStationaryFixedOpponentsContinueReward reward
          (quittingPersistentBaseRoot {owner} free point) owner +
        quittingStationaryFixedOpponentsContinueMass
            (quittingPersistentBaseRoot {owner} free point) owner *
          quittingPunishmentValue reward owner ≤
        quittingRootAbsorbingContribution reward
          (quittingPersistentBaseRoot {owner} free point) owner := by
  let root := quittingPersistentBaseRoot {owner} free point
  have howner : root owner = PMF.pure true := by
    exact quittingPersistentBaseRoot_apply_of_mem_base
      {owner} free point (by simp)
  have hcontinueMass : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter howner
  have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents
    reward (fun _ => root) owner
      (fun _ => quittingPunishmentValue reward owner) 0
  have htarget := quittingRootExpectedPayoff_eq_absorbingContribution_add
    reward 0 root owner
  change quittingSingletonBaseOwnerFloorExcess reward owner root ≤ 0 ↔ _
  rw [quittingSingletonBaseOwnerFloorExcess, hcontinue, htarget,
    hcontinueMass]
  simp [root, quittingStationaryFixedOpponentsContinueReward,
    quittingStationaryFixedOpponentsContinueMass,
    quittingFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueMass]

omit [Nonempty ι] in
/-- The singleton owner's floor excess is continuous on the induced mixed
profile polytope. -/
theorem continuous_quittingSingletonBaseOwnerFloorExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) :
    Continuous fun point : mixedPolytope (quittingBinaryForm free).sig =>
      quittingSingletonBaseOwnerFloorExcess reward owner
        (quittingPersistentBaseRoot {owner} free point) := by
  let tail : Payoff ι := fun _ => quittingPunishmentValue reward owner
  have hroot := continuous_quittingPersistentBaseSimplexRoot {owner} free
  have hcontinue : Continuous fun point :
      mixedPolytope (quittingBinaryForm free).sig =>
      quittingRootContinuePayoff reward tail
        (quittingPersistentBaseRoot {owner} free point) owner := by
    have h := (continuous_quittingRootContinuePayoff_simplex reward owner).comp
      ((continuous_const : Continuous fun _ :
        mixedPolytope (quittingBinaryForm free).sig => tail).prodMk hroot)
    convert h using 1
    funext point
    simp only [Function.comp_apply]
    rw [quittingRootOfSimplex_persistentBaseSimplexRoot]
  have htarget : Continuous fun point :
      mixedPolytope (quittingBinaryForm free).sig =>
      quittingRootExpectedPayoff reward 0
        (quittingPersistentBaseRoot {owner} free point) owner := by
    have h := (continuous_quittingRootExpectedPayoff_simplex reward owner).comp
      ((continuous_const : Continuous fun _ :
        mixedPolytope (quittingBinaryForm free).sig => (0 : Payoff ι)).prodMk
          hroot)
    convert h using 1
    funext point
    simp only [Function.comp_apply]
    rw [quittingRootOfSimplex_persistentBaseSimplexRoot]
  exact hcontinue.sub htarget

/-- Singleton-base component excess: the owner carries the exact punishment
floor balance, outsiders carry their join excess, and induced-game players
carry zero because their endpoint inequalities come from exact Nash. -/
def quittingSingletonBaseComponent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) (who : ι) : ℝ :=
  if who = owner then
    quittingSingletonBaseOwnerFloorExcess reward owner
      (quittingPersistentBaseRoot {owner} free point)
  else if who ∈ free then 0
  else quittingRootEndpointDifference reward 0
    (quittingPersistentBaseRoot {owner} free point) who

/-- Concrete maximum `G` for a singleton persistent base. -/
def quittingSingletonBaseExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) : ℝ :=
  Finset.univ.sup' ⟨owner, Finset.mem_univ owner⟩
    (quittingSingletonBaseComponent reward owner free point)

omit [Nonempty ι] in
/-- Every singleton-base component is continuous. -/
theorem continuous_quittingSingletonBaseComponent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) (who : ι) :
    Continuous fun point =>
      quittingSingletonBaseComponent reward owner free point who := by
  by_cases howner : who = owner
  · subst who
    simpa [quittingSingletonBaseComponent] using
      continuous_quittingSingletonBaseOwnerFloorExcess reward owner free
  · by_cases hfree : who ∈ free
    · simpa [quittingSingletonBaseComponent, howner, hfree] using
        (continuous_const : Continuous fun _ :
          mixedPolytope (quittingBinaryForm free).sig => (0 : ℝ))
    · have hendpoint : Continuous fun point :
          mixedPolytope (quittingBinaryForm free).sig =>
          quittingRootEndpointDifference reward 0
            (quittingPersistentBaseRoot {owner} free point) who := by
        have h :=
          (continuous_quittingRootEndpointDifference_simplex reward who).comp
            ((continuous_const : Continuous fun _ :
              mixedPolytope (quittingBinaryForm free).sig =>
                (0 : Payoff ι)).prodMk
              (continuous_quittingPersistentBaseSimplexRoot {owner} free))
        convert h using 1
        funext point
        simp only [Function.comp_apply]
        rw [quittingRootOfSimplex_persistentBaseSimplexRoot]
      simpa [quittingSingletonBaseComponent, howner, hfree] using hendpoint

omit [Nonempty ι] in
/-- The concrete singleton-base `G` is continuous. -/
theorem continuous_quittingSingletonBaseExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) :
    Continuous (quittingSingletonBaseExcess reward owner free) :=
  Continuous.finset_sup'_apply ⟨owner, Finset.mem_univ owner⟩ fun who _ =>
    continuous_quittingSingletonBaseComponent reward owner free who

omit [Nonempty ι] in
/-- `G ≤ 0` is exactly the owner-floor and outsider-join screen. -/
theorem quittingSingletonBaseExcess_nonpos_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) :
    quittingSingletonBaseExcess reward owner free point ≤ 0 ↔
      quittingSingletonBaseOwnerFloorExcess reward owner
          (quittingPersistentBaseRoot {owner} free point) ≤ 0 ∧
      ∀ who ∉ ({owner} : Finset ι) ∪ free,
        quittingRootEndpointDifference reward 0
          (quittingPersistentBaseRoot {owner} free point) who ≤ 0 := by
  constructor
  · intro hscreen
    constructor
    · have hcomponent := (Finset.le_sup' (f :=
        quittingSingletonBaseComponent reward owner free point)
        (Finset.mem_univ owner)).trans hscreen
      simpa [quittingSingletonBaseComponent] using hcomponent
    · intro who hwho
      have howner : who ≠ owner := by
        intro heq
        subst who
        exact hwho (Finset.mem_union_left free (by simp))
      have hfree : who ∉ free := fun hmem =>
        hwho (Finset.mem_union_right {owner} hmem)
      have hcomponent := (Finset.le_sup' (f :=
        quittingSingletonBaseComponent reward owner free point)
        (Finset.mem_univ who)).trans hscreen
      simpa [quittingSingletonBaseComponent, howner, hfree] using hcomponent
  · rintro ⟨hfloor, hjoin⟩
    apply Finset.sup'_le
    intro who _
    by_cases howner : who = owner
    · subst who
      simpa [quittingSingletonBaseComponent] using hfloor
    · by_cases hfree : who ∈ free
      · simp [quittingSingletonBaseComponent, howner, hfree]
      · have houtside : who ∉ ({owner} : Finset ι) ∪ free := by
          simp [howner, hfree]
        simpa [quittingSingletonBaseComponent, howner, hfree] using
          hjoin who houtside

omit [Nonempty ι] in
/-- An induced Nash point plus the owner-floor and outsider-join signs
constructs the singleton-base all-behavior certificate. -/
theorem nonempty_quittingSingletonBaseCertificate_of_inducedNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) (howner : owner ∉ free)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet reward {owner} free)
    (hfloor : quittingSingletonBaseOwnerFloorExcess reward owner
      (quittingPersistentBaseRoot {owner} free point) ≤ 0)
    (hjoin : ∀ who ∉ ({owner} : Finset ι) ∪ free,
      quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot {owner} free point) who ≤ 0) :
    Nonempty (QuittingSingletonBaseCertificate reward owner
      (quittingPersistentBaseRoot {owner} free point)) := by
  let root := quittingPersistentBaseRoot {owner} free point
  have hdisjoint : Disjoint ({owner} : Finset ι) free := by
    apply Finset.disjoint_left.mpr
    intro who hsingleton hfree
    have heq : who = owner := by simpa using hsingleton
    subst who
    exact howner hfree
  refine ⟨{
    owner_quits := quittingPersistentBaseRoot_apply_of_mem_base
      {owner} free point (by simp)
    other_endpointNash := ?_
    owner_floor_balance :=
      (quittingSingletonBaseOwnerFloorExcess_nonpos_iff
        reward owner free point).mp hfloor }⟩
  intro who hwho
  by_cases hfree : who ∈ free
  · obtain ⟨hquit, hcontinue⟩ :=
      quittingPersistentBaseRoot_free_purePayoff_le reward {owner} free
        (by simp) hdisjoint point hpoint who hfree
    have hquitDifference := quittingRootQuitPayoff_sub_successorPayoff
      reward 0 root who
    have hcontinueDifference := quittingRootContinuePayoff_sub_successorPayoff
      reward 0 root who
    change (root who false).toReal *
          quittingRootEndpointDifference reward 0 root who ≤ 0 ∧
        0 ≤ (root who true).toReal *
          quittingRootEndpointDifference reward 0 root who
    constructor <;> linarith
  · have houtside : who ∉ ({owner} : Finset ι) ∪ free := by
      simp [hwho, hfree]
    have hroot : root who = PMF.pure false :=
      quittingPersistentBaseRoot_apply_of_outside
        {owner} free point houtside
    change (root who false).toReal *
          quittingRootEndpointDifference reward 0 root who ≤ 0 ∧
        0 ≤ (root who true).toReal *
          quittingRootEndpointDifference reward 0 root who
    rw [hroot]
    simpa using hjoin who houtside

omit [Nonempty ι] in
/-- **Concrete singleton-base ordered alternative.**  Either the induced
Nash carrier contains a floor-admissible point and closes through the
all-behavior compiler, or the literal singleton `G` has a positive attained
gap on every induced Nash point. -/
theorem exists_uniformPayoff_or_singletonBase_pos_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) (howner : owner ∉ free) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ gamma : ℝ, 0 < gamma ∧
        ∀ point ∈ quittingPersistentBaseNashSet reward {owner} free,
          gamma ≤ quittingSingletonBaseExcess reward owner free point := by
  rcases exists_persistentBaseNash_nonpos_or_pos_gap reward {owner} free
      (quittingSingletonBaseExcess reward owner free)
      (continuous_quittingSingletonBaseExcess reward owner free) with
    haccepted | hgap
  · left
    obtain ⟨point, hpoint, hscreen⟩ := haccepted
    obtain ⟨hfloor, hjoin⟩ :=
      (quittingSingletonBaseExcess_nonpos_iff
        reward owner free point).mp hscreen
    obtain ⟨certificate⟩ :=
      nonempty_quittingSingletonBaseCertificate_of_inducedNash
        reward owner free howner point hpoint hfloor hjoin
    exact ⟨quittingRootAbsorbingContribution reward
      (quittingPersistentBaseRoot {owner} free point),
      certificate.isUniformEquilibriumPayoff⟩
  · exact Or.inr hgap

end GameTheory
