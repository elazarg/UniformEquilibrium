/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargePersistentBaseDeletionAdapter

/-!
# Actual four-label adapter for the large persistent-base dispatch

This module connects the abstract two-by-two finite Nash dispatch to the literal induced Nash
carrier and the concrete large-base excess of a four-player quitting game.  The two base labels
and two free labels are selected from arbitrary disjoint two-element finsets; no identification of
the ambient player type with `Fin 4` is used.
-/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A canonical free-face point used only to name the four literal endpoint cells. -/
def quittingLargeBaseReferencePoint (free : Finset ι) (first : ι) :
    mixedPolytope (quittingBinaryForm free).sig :=
  quittingBinaryPairMixedPoint free first 0 0 (by positivity) (by norm_num)
    (by positivity) (by norm_num)

/-- The corresponding actual persistent-base root. -/
def quittingLargeBaseReferenceRoot
    (base free : Finset ι) (first : ι) : ι → PMF Bool :=
  quittingPersistentBaseRoot base free
    (quittingLargeBaseReferencePoint free first)

/-- First free player's actual Quit-minus-Continue endpoint row. -/
def quittingLargeBaseFirstRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (first second : ι) (secondAction : Bool) : ℝ :=
  quittingRootEndpointDifference reward 0
    (Function.update (quittingLargeBaseReferenceRoot base free first)
      second (PMF.pure secondAction)) first

/-- Second free player's actual Quit-minus-Continue endpoint row. -/
def quittingLargeBaseSecondRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (first second : ι) (firstAction : Bool) : ℝ :=
  quittingRootEndpointDifference reward 0
    (Function.update (quittingLargeBaseReferenceRoot base free first)
      first (PMF.pure firstAction)) second

/-- Literal Continue-minus-Quit payoff of one persistent base label at a pure free cell. -/
def quittingLargeBaseLeaveCell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (first second owner : ι)
    (firstAction secondAction : Bool) : ℝ :=
  -quittingRootEndpointDifference reward 0
    (Function.update
      (Function.update (quittingLargeBaseReferenceRoot base free first)
        first (PMF.pure firstAction))
      second (PMF.pure secondAction)) owner

/-- The two literal base-leave observables, indexed in the `Fin 2` format consumed by the finite
dispatch. -/
def quittingLargeBaseLeaveObservable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (baseFirst baseSecond first second : ι) :
    Fin 2 → Bool → Bool → ℝ :=
  fun owner ↦
    if owner = 0 then
      quittingLargeBaseLeaveCell reward base free first second baseFirst
    else
      quittingLargeBaseLeaveCell reward base free first second baseSecond

/-- Endpoint differences ignore changes to the displayed player's own marginal. -/
theorem quittingRootEndpointDifference_eq_of_eq_off_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (firstRoot secondRoot : ι → PMF Bool) (who : ι)
    (agree : ∀ other, other ≠ who → firstRoot other = secondRoot other) :
    quittingRootEndpointDifference reward tail firstRoot who =
      quittingRootEndpointDifference reward tail secondRoot who := by
  have hquit : Function.update firstRoot who (PMF.pure true) =
      Function.update secondRoot who (PMF.pure true) := by
    funext other
    by_cases hother : other = who
    · subst other
      simp
    · simp [Function.update, hother, agree other hother]
  have hcontinue : Function.update firstRoot who (PMF.pure false) =
      Function.update secondRoot who (PMF.pure false) := by
    funext other
    by_cases hother : other = who
    · subst other
      simp
    · simp [Function.update, hother, agree other hother]
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  rw [hquit, hcontinue]

omit [Fintype ι] in
/-- Two roots on the same persistent/free face agree away from the two free labels. -/
theorem quittingPersistentBaseRoot_eq_of_not_mem_free
    (base free : Finset ι)
    (firstPoint secondPoint : mixedPolytope (quittingBinaryForm free).sig)
    {who : ι} (hwho : who ∉ free) :
    quittingPersistentBaseRoot base free firstPoint who =
      quittingPersistentBaseRoot base free secondPoint who := by
  by_cases hbase : who ∈ base
  · rw [quittingPersistentBaseRoot_apply_of_mem_base base free firstPoint hbase,
      quittingPersistentBaseRoot_apply_of_mem_base base free secondPoint hbase]
  · have houtside : who ∉ base ∪ free := by simp [hbase, hwho]
    rw [quittingPersistentBaseRoot_apply_of_outside base free firstPoint houtside,
      quittingPersistentBaseRoot_apply_of_outside base free secondPoint houtside]

/-- Once both free coordinates are replaced by pure actions, the literal endpoint cell is
independent of the original mixed point. -/
theorem quittingEndpointDifference_pairPure_eq_reference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι)
    (base free : Finset ι)
    (first second observer : ι)
    (hfirst : first ∈ free) (hsecond : second ∈ free)
    (hne : first ≠ second)
    (hcover : ∀ who ∈ free, who = first ∨ who = second)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (firstAction secondAction : Bool) :
    quittingRootEndpointDifference reward tail
        (Function.update
          (Function.update (quittingPersistentBaseRoot base free point)
            first (PMF.pure firstAction))
          second (PMF.pure secondAction)) observer =
      quittingRootEndpointDifference reward tail
        (Function.update
          (Function.update (quittingLargeBaseReferenceRoot base free first)
            first (PMF.pure firstAction))
          second (PMF.pure secondAction)) observer := by
  apply quittingRootEndpointDifference_eq_of_eq_off_self
  intro other hother
  by_cases hotherFirst : other = first
  · subst other
    simp [hne]
  · by_cases hotherSecond : other = second
    · subst other
      simp
    · have hnotFree : other ∉ free := by
        intro hfree
        rcases hcover other hfree with rfl | rfl
        · exact hotherFirst rfl
        · exact hotherSecond rfl
      simp only [Function.update_of_ne hotherSecond, Function.update_of_ne hotherFirst]
      exact quittingPersistentBaseRoot_eq_of_not_mem_free
        base free point (quittingLargeBaseReferencePoint free first) hnotFree

/-- The two endpoint rows read from an arbitrary pair point are the fixed literal rows named at
the reference root. -/
theorem quittingBinaryPair_rows_eq_largeBaseRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) {first second : ι}
    (hcover : ∀ who ∈ free, who = first ∨ who = second)
    (firstRate secondRate : ℝ)
    (hfirst0 : 0 ≤ firstRate) (hfirst1 : firstRate ≤ 1)
    (hsecond0 : 0 ≤ secondRate) (hsecond1 : secondRate ≤ 1) :
    let point := quittingBinaryPairMixedPoint free first firstRate secondRate
      hfirst0 hfirst1 hsecond0 hsecond1
    let root := quittingPersistentBaseRoot base free point
    (fun action ↦ quittingRootEndpointDifference reward 0
        (Function.update root second (PMF.pure action)) first) =
        quittingLargeBaseFirstRow reward base free first second ∧
      (fun action ↦ quittingRootEndpointDifference reward 0
        (Function.update root first (PMF.pure action)) second) =
        quittingLargeBaseSecondRow reward base free first second := by
  intro point root
  constructor
  · funext action
    apply quittingRootEndpointDifference_eq_of_eq_off_self
    intro other hotherFirst
    by_cases hotherSecond : other = second
    · subst other
      simp
    · have hnotFree : other ∉ free := by
        intro hfree
        rcases hcover other hfree with hotherFirst' | hotherSecond'
        · exact hotherFirst hotherFirst'
        · exact hotherSecond hotherSecond'
      simp only [Function.update_of_ne hotherSecond]
      exact quittingPersistentBaseRoot_eq_of_not_mem_free
        base free point (quittingLargeBaseReferencePoint free first) hnotFree
  · funext action
    apply quittingRootEndpointDifference_eq_of_eq_off_self
    intro other hotherSecond
    by_cases hotherFirst : other = first
    · subst other
      simp
    · have hnotFree : other ∉ free := by
        intro hfree
        rcases hcover other hfree with hotherFirst' | hotherSecond'
        · exact hotherFirst hotherFirst'
        · exact hotherSecond hotherSecond'
      simp only [Function.update_of_ne hotherFirst]
      exact quittingPersistentBaseRoot_eq_of_not_mem_free
        base free point (quittingLargeBaseReferencePoint free first) hnotFree

/-- A literal base-leave endpoint at an arbitrary pair point is exactly the product expectation
of its four actual pure endpoint cells. -/
theorem neg_endpointDifference_binaryPair_eq_leaveExpectation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (hdisjoint : Disjoint base free)
    {first second owner : ι}
    (hfirst : first ∈ free) (hsecond : second ∈ free)
    (hne : first ≠ second)
    (hcover : ∀ who ∈ free, who = first ∨ who = second)
    (hownerFirst : owner ≠ first) (hownerSecond : owner ≠ second)
    (firstRate secondRate : ℝ)
    (hfirst0 : 0 ≤ firstRate) (hfirst1 : firstRate ≤ 1)
    (hsecond0 : 0 ≤ secondRate) (hsecond1 : secondRate ≤ 1) :
    let point := quittingBinaryPairMixedPoint free first firstRate secondRate
      hfirst0 hfirst1 hsecond0 hsecond1
    let root := quittingPersistentBaseRoot base free point
    (-quittingRootEndpointDifference reward 0 root owner) =
      binaryProductExpectation
        (quittingLargeBaseLeaveCell reward base free first second owner)
        firstRate secondRate := by
  intro point root
  have hproduct := quittingRootEndpointDifference_eq_twoOpponentProduct
    reward 0 root hownerFirst hownerSecond hne
  have hrates := quittingPersistentBaseRoot_binaryPairMixedPoint_true_toReal
    base free hdisjoint hfirst hsecond hne firstRate secondRate
      hfirst0 hfirst1 hsecond0 hsecond1
  change (root first true).toReal = firstRate ∧
    (root second true).toReal = secondRate at hrates
  rw [hproduct, hrates.1, hrates.2]
  simp only [binaryProductExpectation]
  rw [quittingEndpointDifference_pairPure_eq_reference
      reward 0 base free first second owner hfirst hsecond hne hcover point false false,
    quittingEndpointDifference_pairPure_eq_reference
      reward 0 base free first second owner hfirst hsecond hne hcover point true false,
    quittingEndpointDifference_pairPure_eq_reference
      reward 0 base free first second owner hfirst hsecond hne hcover point false true,
    quittingEndpointDifference_pairPure_eq_reference
      reward 0 base free first second owner hfirst hsecond hne hcover point true true]
  simp only [quittingLargeBaseLeaveCell]
  ring

/-- **Actual-data finite dispatch for four displayed labels.**  A positive concrete large-base
gap on the complete induced Nash carrier produces the abstract paid pure or paid mixed output
with observables defined by literal quitting endpoint differences. -/
theorem paidPure_or_paidMixed_of_actual_largeBase_gap_labels
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (baseFirst baseSecond first second : ι)
    (hfreeNe : first ≠ second)
    (hbase : base = {baseFirst, baseSecond})
    (hfree : free = {first, second})
    (hdisjoint : Disjoint base free)
    (hexhaust : ∀ who, who = baseFirst ∨ who = baseSecond ∨
      who = first ∨ who = second)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (gap : ∀ point ∈ quittingPersistentBaseNashSet reward base free,
      gamma ≤ quittingPersistentLargeBaseExcess reward base free point) :
    HasPaidPureBinaryCell gamma
        (quittingLargeBaseFirstRow reward base free first second)
        (quittingLargeBaseSecondRow reward base free first second)
        (quittingLargeBaseLeaveObservable reward base free
          baseFirst baseSecond first second) ∨
      HasPaidMixedBinaryCell gamma
        (quittingLargeBaseFirstRow reward base free first second)
        (quittingLargeBaseSecondRow reward base free first second)
        (quittingLargeBaseLeaveObservable reward base free
          baseFirst baseSecond first second) := by
  let alpha := quittingLargeBaseFirstRow reward base free first second
  let beta := quittingLargeBaseSecondRow reward base free first second
  let observable := quittingLargeBaseLeaveObservable reward base free
    baseFirst baseSecond first second
  have hfirst : first ∈ free := by simp [hfree]
  have hsecond : second ∈ free := by simp [hfree]
  have hbaseFirst : baseFirst ∈ base := by simp [hbase]
  have hbaseSecond : baseSecond ∈ base := by simp [hbase]
  have hcover : ∀ who ∈ free, who = first ∨ who = second := by
    intro who hwho
    rw [hfree] at hwho
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hwho
  have hbaseNonempty : base.Nonempty := by simp [hbase]
  have hcross : ∀ {owner freePlayer}, owner ∈ base → freePlayer ∈ free →
      owner ≠ freePlayer := by
    intro owner freePlayer howner hfreePlayer equality
    subst freePlayer
    exact Finset.disjoint_left.mp hdisjoint howner hfreePlayer
  apply paidPure_or_paidMixed_of_forall_binaryNash gamma alpha beta observable
  intro firstRate secondRate hnash
  let point := quittingBinaryPairMixedPoint free first firstRate secondRate
    hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
  let root := quittingPersistentBaseRoot base free point
  have hrows := quittingBinaryPair_rows_eq_largeBaseRows
    reward base free hcover firstRate secondRate
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
  change
    (fun action ↦ quittingRootEndpointDifference reward 0
      (Function.update root second (PMF.pure action)) first) = alpha ∧
    (fun action ↦ quittingRootEndpointDifference reward 0
      (Function.update root first (PMF.pure action)) second) = beta at hrows
  have hpoint : point ∈ quittingPersistentBaseNashSet reward base free := by
    apply binaryPairMixedPoint_mem_quittingPersistentBaseNashSet
      reward base free hbaseNonempty hdisjoint hfirst hsecond hfreeNe hcover
        firstRate secondRate hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
    change IsBinaryDifferenceNash
      (fun action ↦ quittingRootEndpointDifference reward 0
        (Function.update root second (PMF.pure action)) first)
      (fun action ↦ quittingRootEndpointDifference reward 0
        (Function.update root first (PMF.pure action)) second)
      firstRate secondRate
    rw [hrows.1, hrows.2]
    exact hnash
  have hactual := gap point hpoint
  have hfirstExpectation :
      quittingPersistentLargeBaseComponent reward base free point baseFirst =
        binaryProductExpectation (observable 0) firstRate secondRate := by
    rw [show quittingPersistentLargeBaseComponent reward base free point baseFirst =
        -quittingRootEndpointDifference reward 0 root baseFirst by
      simp [quittingPersistentLargeBaseComponent, hbaseFirst, root]]
    rw [neg_endpointDifference_binaryPair_eq_leaveExpectation
      reward base free hdisjoint hfirst hsecond hfreeNe hcover
      (hcross hbaseFirst hfirst) (hcross hbaseFirst hsecond)
      firstRate secondRate hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2]
    rfl
  have hsecondExpectation :
      quittingPersistentLargeBaseComponent reward base free point baseSecond =
        binaryProductExpectation (observable 1) firstRate secondRate := by
    rw [show quittingPersistentLargeBaseComponent reward base free point baseSecond =
        -quittingRootEndpointDifference reward 0 root baseSecond by
      simp [quittingPersistentLargeBaseComponent, hbaseSecond, root]]
    rw [neg_endpointDifference_binaryPair_eq_leaveExpectation
      reward base free hdisjoint hfirst hsecond hfreeNe hcover
      (hcross hbaseSecond hfirst) (hcross hbaseSecond hsecond)
      firstRate secondRate hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2]
    rfl
  let paidMax := max
    (binaryProductExpectation (observable 0) firstRate secondRate)
    (binaryProductExpectation (observable 1) firstRate secondRate)
  have hexcessUpper :
      quittingPersistentLargeBaseExcess reward base free point ≤ max paidMax 0 := by
    apply Finset.sup'_le
    intro who _
    rcases hexhaust who with hwho | hwho | hwho | hwho
    · subst who
      rw [hfirstExpectation]
      exact le_max_of_le_left (le_max_left _ _)
    · subst who
      rw [hsecondExpectation]
      exact le_max_of_le_left (le_max_right _ _)
    · subst who
      have hnotBase : first ∉ base := fun hmem ↦
        Finset.disjoint_left.mp hdisjoint hmem hfirst
      have hcomponent :
          quittingPersistentLargeBaseComponent reward base free point first = 0 := by
        simp only [quittingPersistentLargeBaseComponent, hnotBase, if_false,
          hfirst, if_pos]
      rw [hcomponent]
      exact le_max_right _ _
    · subst who
      have hnotBase : second ∉ base := fun hmem ↦
        Finset.disjoint_left.mp hdisjoint hmem hsecond
      have hcomponent :
          quittingPersistentLargeBaseComponent reward base free point second = 0 := by
        simp only [quittingPersistentLargeBaseComponent, hnotBase, if_false,
          hsecond, if_pos]
      rw [hcomponent]
      exact le_max_right _ _
  have hpaid : gamma ≤ max paidMax 0 := hactual.trans hexcessUpper
  change gamma ≤ paidMax
  by_cases hpaidMax : 0 ≤ paidMax
  · rw [max_eq_left hpaidMax] at hpaid
    exact hpaid
  · have hzero : max paidMax 0 = 0 := max_eq_right (le_of_not_ge hpaidMax)
    rw [hzero] at hpaid
    linarith

/-- Instance-free spelling of the concrete positive-gap hypothesis on an arbitrary four-element
player type. -/
def HasQuittingPersistentLargeBaseGapOfCardFour
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (hfour : Fintype.card ι = 4) (gamma : ℝ) : Prop :=
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  ∀ point ∈ quittingPersistentBaseNashSet reward base free,
    gamma ≤ quittingPersistentLargeBaseExcess reward base free point

/-- Reindex-invariant output of the actual large-base finite dispatch. -/
def HasActualLargeBaseFiniteNashDispatch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (gamma : ℝ) : Prop :=
  ∃ baseFirst baseSecond first second,
    baseFirst ≠ baseSecond ∧ first ≠ second ∧
      base = {baseFirst, baseSecond} ∧ free = {first, second} ∧
      (HasPaidPureBinaryCell gamma
          (quittingLargeBaseFirstRow reward base free first second)
          (quittingLargeBaseSecondRow reward base free first second)
          (quittingLargeBaseLeaveObservable reward base free
            baseFirst baseSecond first second) ∨
        HasPaidMixedBinaryCell gamma
          (quittingLargeBaseFirstRow reward base free first second)
          (quittingLargeBaseSecondRow reward base free first second)
          (quittingLargeBaseLeaveObservable reward base free
            baseFirst baseSecond first second))

/-- **Arbitrary four-label adapter.**  Disjoint two-element persistent and free faces exhaust an
arbitrary four-element player type, so the concrete positive `G` gap reduces to the finite paid
pure/mixed binary dispatch. -/
theorem hasActualLargeBaseFiniteNashDispatch_of_card_two
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (hfour : Fintype.card ι = 4)
    (hbaseCard : base.card = 2) (hfreeCard : free.card = 2)
    (hdisjoint : Disjoint base free)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (gap : HasQuittingPersistentLargeBaseGapOfCardFour
      reward base free hfour gamma) :
    HasActualLargeBaseFiniteNashDispatch reward base free gamma := by
  obtain ⟨baseFirst, baseSecond, hbaseNe, hbase⟩ :=
    Finset.card_eq_two.mp hbaseCard
  obtain ⟨first, second, hfreeNe, hfree⟩ :=
    Finset.card_eq_two.mp hfreeCard
  letI : Nonempty ι := ⟨baseFirst⟩
  have hunionCard : (base ∪ free).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisjoint, hbaseCard, hfreeCard]
  have hunion : base ∪ free = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hunionCard, hfour]
  have hexhaust : ∀ who, who = baseFirst ∨ who = baseSecond ∨
      who = first ∨ who = second := by
    intro who
    have hmem : who ∈ base ∪ free := by rw [hunion]; simp
    simp only [hbase, hfree, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hmem
    rcases hmem with (hwho | hwho) | hwho | hwho
    · exact Or.inl hwho
    · exact Or.inr (Or.inl hwho)
    · exact Or.inr (Or.inr (Or.inl hwho))
    · exact Or.inr (Or.inr (Or.inr hwho))
  change ∀ point ∈ quittingPersistentBaseNashSet reward base free,
    gamma ≤ quittingPersistentLargeBaseExcess reward base free point at gap
  refine ⟨baseFirst, baseSecond, first, second, hbaseNe, hfreeNe,
    hbase, hfree, ?_⟩
  exact paidPure_or_paidMixed_of_actual_largeBase_gap_labels
    reward base free baseFirst baseSecond first second hfreeNe hbase hfree
      hdisjoint hexhaust gamma hgamma gap

/-! ## Same-rate mixed deletion -/

/-- The first free-player row after deleting one base member. -/
def quittingLargeBaseDeletedFirstRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) (first second : ι) : Bool → ℝ :=
  quittingLargeBaseFirstRow reward {owner} free first second

/-- The second free-player row after deleting one base member. -/
def quittingLargeBaseDeletedSecondRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) (first second : ι) : Bool → ℝ :=
  quittingLargeBaseSecondRow reward {owner} free first second

/-- Punishment-priced owner Continue-minus-Quit cell after deletion. -/
def quittingLargeBaseDeletedOwnerFloorCell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) (first second : ι)
    (firstAction secondAction : Bool) : ℝ :=
  -quittingRootEndpointDifference reward
    (fun _ ↦ quittingPunishmentValue reward owner)
    (Function.update
      (Function.update (quittingLargeBaseReferenceRoot {owner} free first)
        first (PMF.pure firstAction))
      second (PMF.pure secondAction)) owner

/-- At a sure-Quit owner, its literal floor excess is the negative endpoint difference when the
Continue endpoint is priced by the punishment value. -/
theorem quittingSingletonBaseOwnerFloorExcess_eq_neg_endpoint_of_sureQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (root : ι → PMF Bool)
    (howner : root owner = PMF.pure true) :
    quittingSingletonBaseOwnerFloorExcess reward owner root =
      -quittingRootEndpointDifference reward
        (fun _ ↦ quittingPunishmentValue reward owner) root owner := by
  have hmass : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter howner
  have hzero := quittingRootExpectedPayoff_eq_absorbingContribution_add
    reward 0 root owner
  have htail := quittingRootExpectedPayoff_eq_absorbingContribution_add
    reward (fun _ ↦ quittingPunishmentValue reward owner) root owner
  have hquit : quittingRootQuitPayoff reward
      (fun _ ↦ quittingPunishmentValue reward owner) root owner =
      quittingRootExpectedPayoff reward
        (fun _ ↦ quittingPunishmentValue reward owner) root owner := by
    unfold quittingRootQuitPayoff
    rw [← howner, Function.update_eq_self]
  rw [quittingSingletonBaseOwnerFloorExcess,
    quittingRootEndpointDifference, hquit, hzero, htail, hmass]
  simp

/-- The actual owner floor at the retained mixed point is the product expectation of its four
punishment-priced pure cells. -/
theorem singletonBaseOwnerFloorExcess_binaryPair_eq_expectation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) {first second : ι}
    (howner : owner ∉ free)
    (hfirst : first ∈ free) (hsecond : second ∈ free)
    (hne : first ≠ second)
    (hcover : ∀ who ∈ free, who = first ∨ who = second)
    (firstRate secondRate : ℝ)
    (hfirst0 : 0 ≤ firstRate) (hfirst1 : firstRate ≤ 1)
    (hsecond0 : 0 ≤ secondRate) (hsecond1 : secondRate ≤ 1) :
    let point := quittingBinaryPairMixedPoint free first firstRate secondRate
      hfirst0 hfirst1 hsecond0 hsecond1
    let root := quittingPersistentBaseRoot {owner} free point
    quittingSingletonBaseOwnerFloorExcess reward owner root =
      binaryProductExpectation
        (quittingLargeBaseDeletedOwnerFloorCell reward owner free first second)
        firstRate secondRate := by
  intro point root
  have hdisjoint : Disjoint ({owner} : Finset ι) free := by
    simpa [Finset.disjoint_left] using howner
  have hownerFirst : owner ≠ first := by
    intro equality
    subst first
    exact howner hfirst
  have hownerSecond : owner ≠ second := by
    intro equality
    subst second
    exact howner hsecond
  have hownerQuit : root owner = PMF.pure true :=
    quittingPersistentBaseRoot_apply_of_mem_base {owner} free point (by simp)
  rw [quittingSingletonBaseOwnerFloorExcess_eq_neg_endpoint_of_sureQuit
    reward owner root hownerQuit]
  have hproduct := quittingRootEndpointDifference_eq_twoOpponentProduct
    reward (fun _ ↦ quittingPunishmentValue reward owner) root
      hownerFirst hownerSecond hne
  have hrates := quittingPersistentBaseRoot_binaryPairMixedPoint_true_toReal
    ({owner} : Finset ι) free hdisjoint hfirst hsecond hne
      firstRate secondRate hfirst0 hfirst1 hsecond0 hsecond1
  change (root first true).toReal = firstRate ∧
    (root second true).toReal = secondRate at hrates
  rw [hproduct, hrates.1, hrates.2]
  simp only [binaryProductExpectation]
  rw [quittingEndpointDifference_pairPure_eq_reference reward
      (fun _ ↦ quittingPunishmentValue reward owner) {owner} free
      first second owner hfirst hsecond hne hcover point false false,
    quittingEndpointDifference_pairPure_eq_reference reward
      (fun _ ↦ quittingPunishmentValue reward owner) {owner} free
      first second owner hfirst hsecond hne hcover point true false,
    quittingEndpointDifference_pairPure_eq_reference reward
      (fun _ ↦ quittingPunishmentValue reward owner) {owner} free
      first second owner hfirst hsecond hne hcover point false true,
    quittingEndpointDifference_pairPure_eq_reference reward
      (fun _ ↦ quittingPunishmentValue reward owner) {owner} free
      first second owner hfirst hsecond hne hcover point true true]
  simp only [quittingLargeBaseDeletedOwnerFloorCell]
  ring

/-- Division-free form of the actual owner-floor balance at the retained mixed rates. -/
theorem clearedOwnerFloor_nonpos_iff_actual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) {first second : ι}
    (howner : owner ∉ free)
    (hfirst : first ∈ free) (hsecond : second ∈ free)
    (hne : first ≠ second)
    (hcover : ∀ who ∈ free, who = first ∨ who = second)
    (alpha beta : Bool → ℝ)
    (orientation : IsStrictMatchingPenniesOrientation alpha beta) :
    let hnash := isBinaryDifferenceNash_mixed orientation
    let point := quittingBinaryPairMixedPoint free first
      (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha)
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
    binaryClearedObservable alpha beta
        (quittingLargeBaseDeletedOwnerFloorCell reward owner free first second) ≤ 0 ↔
      quittingSingletonBaseOwnerFloorExcess reward owner
        (quittingPersistentBaseRoot {owner} free point) ≤ 0 := by
  intro hnash point
  have hfloor := singletonBaseOwnerFloorExcess_binaryPair_eq_expectation
    reward owner free howner hfirst hsecond hne hcover
      (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha)
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
  rw [binaryProductExpectation_mixed orientation] at hfloor
  have hden := binaryClearedDenominator_pos orientation
  have heq : binaryClearedDenominator alpha beta *
      quittingSingletonBaseOwnerFloorExcess reward owner
        (quittingPersistentBaseRoot {owner} free point) =
      binaryClearedObservable alpha beta
        (quittingLargeBaseDeletedOwnerFloorCell reward owner free first second) := by
    rw [hfloor]
    field_simp [ne_of_gt hden]
  rw [← heq]
  constructor <;> intro h <;> nlinarith

/-- Deleting the observed base member changes only that member's own marginal, so every pure
base-leave cell is the same literal endpoint cell at the singleton-base root. -/
theorem largeBaseLeaveCell_eq_singletonBaseLeaveCell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner outsider : ι) (free : Finset ι) {first second : ι}
    (hownerOutsider : owner ≠ outsider)
    (hfreeNe : first ≠ second)
    (hfreeCover : ∀ who ∈ free, who = first ∨ who = second)
    (hplayerCover : ∀ who, who ∉ ({owner} : Finset ι) ∪ free →
      who = outsider)
    (firstAction secondAction : Bool) :
    quittingLargeBaseLeaveCell reward {owner, outsider} free
        first second outsider firstAction secondAction =
      quittingLargeBaseLeaveCell reward {owner} free
        first second outsider firstAction secondAction := by
  apply congrArg Neg.neg
  apply quittingRootEndpointDifference_eq_of_eq_off_self
  intro other hotherOutsider
  by_cases hotherFirst : other = first
  · subst other
    simp [hfreeNe]
  · by_cases hotherSecond : other = second
    · subst other
      simp
    · simp only [Function.update_of_ne hotherSecond,
        Function.update_of_ne hotherFirst]
      by_cases hotherOwner : other = owner
      · subst other
        change quittingPersistentBaseRoot {owner, outsider} free
            (quittingLargeBaseReferencePoint free first) owner =
          quittingPersistentBaseRoot {owner} free
            (quittingLargeBaseReferencePoint free first) owner
        rw [quittingPersistentBaseRoot_apply_of_mem_base
            {owner, outsider} free _ (by simp [hownerOutsider]),
          quittingPersistentBaseRoot_apply_of_mem_base
            {owner} free _ (by simp)]
      · have hotherNotFree : other ∉ free := by
          intro hfree
          rcases hfreeCover other hfree with hfirst | hsecond
          · exact hotherFirst hfirst
          · exact hotherSecond hsecond
        have houtsideSingleton : other ∉ ({owner} : Finset ι) ∪ free := by
          simp [hotherOwner, hotherNotFree]
        exact False.elim (hotherOutsider
          (hplayerCover other houtsideSingleton))

/-- A positive cleared original base-leave numerator gives the deleted member's actual strict
no-join inequality at the retained mixed point. -/
theorem deletedOutsider_endpoint_nonpos_of_paidClearedObservable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner outsider : ι) (free : Finset ι) {first second : ι}
    (howner : owner ∉ free) (houtsider : outsider ∉ free)
    (hownerOutsider : owner ≠ outsider)
    (hfirst : first ∈ free) (hsecond : second ∈ free)
    (hne : first ≠ second)
    (hfreeCover : ∀ who ∈ free, who = first ∨ who = second)
    (hplayerCover : ∀ who, who ∉ ({owner} : Finset ι) ∪ free →
      who = outsider)
    (gamma : ℝ) (hgamma : 0 < gamma) (alpha beta : Bool → ℝ)
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (hpaid : gamma * binaryClearedDenominator alpha beta ≤
      binaryClearedObservable alpha beta
        (quittingLargeBaseLeaveCell reward {owner, outsider} free
          first second outsider)) :
    let hnash := isBinaryDifferenceNash_mixed orientation
    let point := quittingBinaryPairMixedPoint free first
      (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha)
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
    quittingRootEndpointDifference reward 0
      (quittingPersistentBaseRoot {owner} free point) outsider ≤ 0 := by
  intro hnash point
  have hdisjoint : Disjoint ({owner} : Finset ι) free := by
    simpa [Finset.disjoint_left] using howner
  have houtsideFirst : outsider ≠ first := by
    intro equality
    subst first
    exact houtsider hfirst
  have houtsideSecond : outsider ≠ second := by
    intro equality
    subst second
    exact houtsider hsecond
  have hexpect := neg_endpointDifference_binaryPair_eq_leaveExpectation
    reward {owner} free hdisjoint hfirst hsecond hne hfreeCover
      houtsideFirst houtsideSecond
      (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha)
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
  change -quittingRootEndpointDifference reward 0
      (quittingPersistentBaseRoot {owner} free point) outsider =
    binaryProductExpectation
      (quittingLargeBaseLeaveCell reward {owner} free first second outsider)
      (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha) at hexpect
  have hcells : quittingLargeBaseLeaveCell reward {owner} free first second outsider =
      quittingLargeBaseLeaveCell reward {owner, outsider} free first second outsider := by
    funext firstAction secondAction
    exact (largeBaseLeaveCell_eq_singletonBaseLeaveCell reward owner outsider free
      hownerOutsider hne hfreeCover hplayerCover
      firstAction secondAction).symm
  rw [hcells, binaryProductExpectation_mixed orientation] at hexpect
  have hden := binaryClearedDenominator_pos orientation
  have hstrict : gamma ≤
      -quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot {owner} free point) outsider := by
    rw [hexpect]
    exact (le_div_iff₀ hden).2 hpaid
  linarith

/-- Vanishing cleared deletion residuals are exactly enough to make both actual free-player
endpoint differences vanish at the retained mixed rates. -/
theorem free_endpointDifference_eq_zero_of_deletedResiduals
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) {first second : ι}
    (howner : owner ∉ free)
    (hfirst : first ∈ free) (hsecond : second ∈ free)
    (hne : first ≠ second)
    (hcover : ∀ who ∈ free, who = first ∨ who = second)
    (alpha beta : Bool → ℝ)
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (hfirstResidual : binaryDeletedFirstResidual alpha
      (quittingLargeBaseDeletedFirstRow reward owner free first second) = 0)
    (hsecondResidual : binaryDeletedSecondResidual beta
      (quittingLargeBaseDeletedSecondRow reward owner free first second) = 0) :
    let hnash := isBinaryDifferenceNash_mixed orientation
    let point := quittingBinaryPairMixedPoint free first
      (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha)
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
    ∀ who ∈ free,
      quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot {owner} free point) who = 0 := by
  intro hnash point who hwho
  have hdisjoint : Disjoint ({owner} : Finset ι) free := by
    simpa [Finset.disjoint_left] using howner
  let root := quittingPersistentBaseRoot {owner} free point
  have hrows := quittingBinaryPair_rows_eq_largeBaseRows
    reward {owner} free hcover (binaryMixedFirstRate beta)
      (binaryMixedSecondRate alpha)
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
  change
    (fun action ↦ quittingRootEndpointDifference reward 0
      (Function.update root second (PMF.pure action)) first) =
        quittingLargeBaseDeletedFirstRow reward owner free first second ∧
    (fun action ↦ quittingRootEndpointDifference reward 0
      (Function.update root first (PMF.pure action)) second) =
        quittingLargeBaseDeletedSecondRow reward owner free first second at hrows
  have hrates := quittingPersistentBaseRoot_binaryPairMixedPoint_true_toReal
    ({owner} : Finset ι) free hdisjoint hfirst hsecond hne
      (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha)
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
  change (root first true).toReal = binaryMixedFirstRate beta ∧
    (root second true).toReal = binaryMixedSecondRate alpha at hrates
  rcases hcover who hwho with hwhoFirst | hwhoSecond
  · subst who
    have hdiff := quittingRootEndpointDifference_eq_binaryDifference
      reward 0 root hne
    change quittingRootEndpointDifference reward 0 root first =
      binaryFirstDifference
        (fun action ↦ quittingRootEndpointDifference reward 0
          (Function.update root second (PMF.pure action)) first)
        (root second true).toReal at hdiff
    rw [hdiff, hrows.1, hrates.2]
    exact (binaryFirstDifference_mixed_eq_zero_iff_deletedResidual_eq_zero
      orientation _).2 hfirstResidual
  · subst who
    have hdiff := quittingRootEndpointDifference_eq_binaryDifference
      reward 0 root hne.symm
    change quittingRootEndpointDifference reward 0 root second =
      binaryFirstDifference
        (fun action ↦ quittingRootEndpointDifference reward 0
          (Function.update root first (PMF.pure action)) second)
        (root first true).toReal at hdiff
    rw [hdiff, hrows.2, hrates.1]
    have hzero :=
      (binarySecondDifference_mixed_eq_zero_iff_deletedResidual_eq_zero
        orientation _).2 hsecondResidual
    simpa [binarySecondDifference, binaryFirstDifference] using hzero

/-- Cleared free-player deletion residuals feed the checked singleton-base deletion compiler.
The owner floor and deleted-member no-join inequalities remain in their literal semantic form. -/
theorem exists_uniformPayoff_of_largeBase_mixedDeletion_of_clearedResiduals
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner outsider : ι) (free : Finset ι) {first second : ι}
    (howner : owner ∉ free)
    (hfirst : first ∈ free) (hsecond : second ∈ free)
    (hne : first ≠ second)
    (hfreeCover : ∀ who ∈ free, who = first ∨ who = second)
    (hplayerCover : ∀ who, who ∉ ({owner} : Finset ι) ∪ free →
      who = outsider)
    (alpha beta : Bool → ℝ)
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (hfirstResidual : binaryDeletedFirstResidual alpha
      (quittingLargeBaseDeletedFirstRow reward owner free first second) = 0)
    (hsecondResidual : binaryDeletedSecondResidual beta
      (quittingLargeBaseDeletedSecondRow reward owner free first second) = 0) :
    let hnash := isBinaryDifferenceNash_mixed orientation
    let point := quittingBinaryPairMixedPoint free first
      (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha)
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
    quittingSingletonBaseOwnerFloorExcess reward owner
        (quittingPersistentBaseRoot {owner} free point) ≤ 0 →
      quittingRootEndpointDifference reward 0
          (quittingPersistentBaseRoot {owner} free point) outsider ≤ 0 →
      ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  intro hnash point hfloor hpaid
  have hzero := free_endpointDifference_eq_zero_of_deletedResiduals
    reward owner free howner hfirst hsecond hne hfreeCover alpha beta
      orientation hfirstResidual hsecondResidual
  exact exists_uniformPayoff_of_largeBase_mixedDeletion
    reward owner outsider free howner hplayerCover point hzero hfloor hpaid

/-- **Fully cleared mixed-deletion handoff.**  The two reprojection residuals, the
punishment-priced owner numerator, and the selected original base-leave numerator imply the
literal hypotheses of the checked singleton-base all-behavior compiler. -/
theorem exists_uniformPayoff_of_largeBase_mixedDeletion_of_clearedData
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner outsider : ι) (free : Finset ι) {first second : ι}
    (howner : owner ∉ free) (houtsider : outsider ∉ free)
    (hownerOutsider : owner ≠ outsider)
    (hfirst : first ∈ free) (hsecond : second ∈ free)
    (hne : first ≠ second)
    (hfreeCover : ∀ who ∈ free, who = first ∨ who = second)
    (hplayerCover : ∀ who, who ∉ ({owner} : Finset ι) ∪ free →
      who = outsider)
    (gamma : ℝ) (hgamma : 0 < gamma) (alpha beta : Bool → ℝ)
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (hfirstResidual : binaryDeletedFirstResidual alpha
      (quittingLargeBaseDeletedFirstRow reward owner free first second) = 0)
    (hsecondResidual : binaryDeletedSecondResidual beta
      (quittingLargeBaseDeletedSecondRow reward owner free first second) = 0)
    (hfloorCleared : binaryClearedObservable alpha beta
      (quittingLargeBaseDeletedOwnerFloorCell reward owner free first second) ≤ 0)
    (hpaidCleared : gamma * binaryClearedDenominator alpha beta ≤
      binaryClearedObservable alpha beta
        (quittingLargeBaseLeaveCell reward {owner, outsider} free
          first second outsider)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let hnash := isBinaryDifferenceNash_mixed orientation
  let point := quittingBinaryPairMixedPoint free first
    (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha)
    hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
  have hfloor : quittingSingletonBaseOwnerFloorExcess reward owner
      (quittingPersistentBaseRoot {owner} free point) ≤ 0 :=
    (clearedOwnerFloor_nonpos_iff_actual reward owner free howner hfirst hsecond
      hne hfreeCover alpha beta orientation).1 hfloorCleared
  have hpaid : quittingRootEndpointDifference reward 0
      (quittingPersistentBaseRoot {owner} free point) outsider ≤ 0 :=
    deletedOutsider_endpoint_nonpos_of_paidClearedObservable
      reward owner outsider free howner houtsider hownerOutsider
      hfirst hsecond hne hfreeCover hplayerCover gamma hgamma alpha beta
      orientation hpaidCleared
  exact exists_uniformPayoff_of_largeBase_mixedDeletion_of_clearedResiduals
    reward owner outsider free howner hfirst hsecond hne hfreeCover
      hplayerCover alpha beta orientation hfirstResidual hsecondResidual
      hfloor hpaid

end GameTheory
