/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PaidMixedOwnerFloorDescent
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.StrictToggleSemanticDispatch
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.NormalCorePunishmentNormal
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.NormalTerminalGapConstrainedStationary
import
  UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.AmbientCarrierElimination

/-!
# Paid-chain refinement of a four-player strict-toggle cycle

On a four-player simple strict-toggle cycle, at least two player labels change.
Consequently a persistent base of cardinality at least two is exactly a
two-player base, the free face has exactly two players, and the two faces
exhaust the ambient player set.  This is precisely the actual-source input of
the support-two paid-chain dispatch.

The capstone below therefore replaces the coarse positive large-base `G` gap
in the cycle semantic residual by the checked pure-paid or mixed-deletion
residual on the same reward table.  The singleton-base and empty-base
residuals are retained unchanged.
-/

noncomputable section

namespace GameTheory

open ThreeCoreAmbientCarrierElimination
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

variable {witness : QuittingTerminalExploitabilityWitness reward}
variable {seed : Finset ι}

/-- Repaired pure-exit residual after a punishment-normal owner excludes the
empty owner-floor cell. -/
def HasRepairedPureExitNormalFiniteResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner remaining first second : ι} {fixed : Bool}
    (source : RepairedResidualPureExitSource owner remaining first second fixed) :
    Prop :=
  (∃ firstAction secondAction,
    0 < source.weight firstAction secondAction ∧
    let coalition := repairedResidualPreferredCoalition
      owner remaining first second fixed firstAction secondAction
    source.remainingWrongSignNumerator reward / source.denominator ≤
        repairedResidualPreferredMargin reward owner remaining first second
          fixed firstAction secondAction ∧
      0 < source.remainingWrongSignNumerator reward / source.denominator ∧
      HasRepairedRemainingToggleResidual reward remaining coalition) ∨
  ∃ firstAction secondAction,
    0 < source.weight firstAction secondAction ∧
    let coalition := repairedResidualWithoutOwner owner remaining first second
      fixed firstAction secondAction
    coalition.Nonempty ∧
      source.ownerFloorNumerator reward / source.denominator ≤
        quittingSetReward reward coalition owner -
          quittingSetReward reward (insert owner coalition) owner ∧
      0 < source.ownerFloorNumerator reward / source.denominator ∧
      HasRepairedOwnerToggleResidual reward owner coalition

/-- A source-retaining repaired residual for a failed paid pure-cell sign in
the punishment-normal chamber. -/
def HasFirstFailureRepairedNormalFiniteResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner second paid first : ι) (secondQuits : Bool) : Prop :=
  ∃ source : RepairedResidualPureExitSource owner second paid first secondQuits,
    HasRepairedPureExitNormalFiniteResidual reward source

/-- Pure-paid residual after punishment normality removes the empty retained
owner-floor cell. -/
def HasPurePaidNormalChainFiniteResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (paid owner first second : ι) (firstQuits secondQuits : Bool) : Prop :=
  ((if firstQuits then
      purePaidDeletedFirstDifference reward owner first second secondQuits < 0
    else
      0 < purePaidDeletedFirstDifference reward owner first second secondQuits) ∧
    HasFirstFailureRepairedNormalFiniteResidual reward owner second paid first
      secondQuits) ∨
  ((if secondQuits then
      purePaidDeletedSecondDifference reward owner first second firstQuits < 0
    else
      0 < purePaidDeletedSecondDifference reward owner first second firstQuits) ∧
    HasFirstFailureRepairedNormalFiniteResidual reward owner first paid second
      firstQuits) ∨
  (0 < purePaidOwnerFloorExcess reward owner first second
      firstQuits secondQuits ∧
    (purePaidRetainedSet first second firstQuits secondQuits).Nonempty ∧
    HasPurePaidSureExitResidual reward paid first second
      firstQuits secondQuits)

omit [Nonempty ι] in
/-- Punishment normality removes the empty cell from the repaired
owner-floor descent while retaining the selected source cell and margin. -/
theorem QuittingTerminalExploitabilityWitness.repairedOwnerFloorResidual_of_normal
    (witness : QuittingTerminalExploitabilityWitness reward)
    {owner remaining first second : ι} {fixed : Bool}
    (source : RepairedResidualPureExitSource owner remaining first second fixed)
    (positive : 0 < source.ownerFloorNumerator reward)
    (hnormal : IsQuittingNormalPlayer reward owner) :
    ∃ firstAction secondAction,
      0 < source.weight firstAction secondAction ∧
      let coalition := repairedResidualWithoutOwner owner remaining first second
        fixed firstAction secondAction
      coalition.Nonempty ∧
        source.ownerFloorNumerator reward / source.denominator ≤
          quittingSetReward reward coalition owner -
            quittingSetReward reward (insert owner coalition) owner ∧
        0 < source.ownerFloorNumerator reward / source.denominator ∧
        HasRepairedOwnerToggleResidual reward owner coalition := by
  obtain ⟨firstAction, secondAction, hweight, result⟩ :=
    witness.repairedOwnerFloorResidual source positive
  refine ⟨firstAction, secondAction, hweight, ?_⟩
  rcases result with hempty | hnonempty
  · have hnormal' : quittingPunishmentValue reward owner ≤
        quittingSoloReward reward owner owner := by
      simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
        quittingSoloReward, quittingSingletonTerminal] using hnormal
    have hpositive : 0 < source.ownerFloorNumerator reward /
        source.denominator := hempty.2.2
    have hbound := hempty.2.1
    exfalso
    linarith
  · exact hnonempty

omit [Nonempty ι] in
/-- A failed paid pure-cell sign retains its actual repaired source, and
punishment normality removes the empty owner-floor outcome from either sign
branch. -/
theorem QuittingTerminalExploitabilityWitness.hasFirstFailureRepairedNormalFiniteResidual
    (witness : QuittingTerminalExploitabilityWitness reward)
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {gamma : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits gamma)
    (hfailure : if firstQuits then
        purePaidDeletedFirstDifference reward owner first second secondQuits < 0
      else
        0 < purePaidDeletedFirstDifference reward owner first second
          secondQuits)
    (hnormal : IsQuittingNormalPlayer reward owner) :
    HasFirstFailureRepairedNormalFiniteResidual reward owner second paid first
      secondQuits := by
  let background := quittingPureSetRoot
    (purePaidDeletedCoalition owner first second firstQuits secondQuits)
  obtain ⟨hjoinOld, hswitchCleared, hswitchPresent⟩ :=
    source.firstFailure_paidSignFailure_sourceSigns hfailure
  obtain ⟨selection, hresidual⟩ :=
    witness.exists_paidSignFailure_residual background owner paid first second
      firstQuits secondQuits source.paid_ne_owner.symm source.owner_ne_first
      source.owner_ne_second source.paid_ne_first source.paid_ne_second
      source.first_ne_second (by
        intro who
        rcases source.exhaust who with hpaid | howner | hfirst | hsecond
        · exact Or.inr (Or.inl hpaid)
        · exact Or.inl howner
        · exact Or.inr (Or.inr (Or.inl hfirst))
        · exact Or.inr (Or.inr (Or.inr hsecond)))
      (by simp [background, purePaidDeletedCoalition, purePaidRetainedSet,
        quittingPureSetRoot, quittingSetAction])
      (by
        cases firstQuits <;> cases secondQuits <;>
          simp [background, purePaidDeletedCoalition, purePaidRetainedSet,
            quittingPureSetRoot, quittingSetAction,
            source.owner_ne_second.symm, source.first_ne_second.symm])
      gamma source.gamma_pos hjoinOld hswitchCleared hswitchPresent
  let repaired := source.firstFailureRepairedSource selection hjoinOld
    hswitchCleared
  refine ⟨repaired, ?_⟩
  have hremaining := source.firstFailure_remainingNumerator_eq selection
    hjoinOld hswitchCleared
  have howner := source.firstFailure_ownerFloorNumerator_eq selection
    hjoinOld hswitchCleared
  dsimp only at hresidual hremaining howner
  rcases hresidual with hremainingPos | hremainingNeg | hownerPos
  · left
    rcases hremainingPos with ⟨hfixed, hpositive⟩
    subst secondQuits
    apply witness.repairedWrongSignResidual repaired
    simpa [repaired, RepairedResidualPureExitSource.remainingWrongSignNumerator]
      using hremaining ▸ hpositive
  · left
    rcases hremainingNeg with ⟨hfixed, hnegative⟩
    subst secondQuits
    apply witness.repairedWrongSignResidual repaired
    have hnegative' : repaired.remainingNumerator reward < 0 :=
      hremaining ▸ hnegative
    simpa [repaired, RepairedResidualPureExitSource.remainingWrongSignNumerator]
      using (neg_pos.mpr hnegative')
  · right
    apply witness.repairedOwnerFloorResidual_of_normal repaired _ hnormal
    exact howner ▸ hownerPos

omit [Nonempty ι] in
/-- All empty owner-floor cells are absent from the source-native pure paid
chain when the retained owner is punishment-normal. -/
theorem QuittingTerminalExploitabilityWitness.hasPurePaidNormalChainFiniteResidual
    (witness : QuittingTerminalExploitabilityWitness reward)
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {gamma : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits gamma)
    (hnormal : IsQuittingNormalPlayer reward owner) :
    HasPurePaidNormalChainFiniteResidual reward paid owner first second
      firstQuits secondQuits := by
  rcases witness.hasPurePaidSingletonResidual source with
    hfirst | hsecond | hfloor
  · exact Or.inl ⟨hfirst,
      witness.hasFirstFailureRepairedNormalFiniteResidual source hfirst hnormal⟩
  · exact Or.inr (Or.inl ⟨hsecond,
      witness.hasFirstFailureRepairedNormalFiniteResidual source.swapFree
        (by
          simpa [purePaidDeletedFirstDifference,
            purePaidDeletedSecondDifference,
            purePaidDeletedCoalition_swap] using hsecond) hnormal⟩)
  · right
    right
    have hretained :
        (purePaidRetainedSet first second firstQuits secondQuits).Nonempty := by
      by_contra hempty
      have hretainedEmpty :
          purePaidRetainedSet first second firstQuits secondQuits = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hempty
      have hdeleted :
          purePaidDeletedCoalition owner first second
              firstQuits secondQuits = {owner} := by
        simp [purePaidDeletedCoalition, hretainedEmpty]
      have hpremium : quittingSoloReward reward owner owner <
          quittingPunishmentValue reward owner := by
        unfold purePaidOwnerFloorExcess at hfloor
        dsimp only at hfloor
        rw [if_neg hempty, hdeleted,
          quittingSetReward_singleton_eq_soloReward] at hfloor
        linarith
      have hnormal' : quittingPunishmentValue reward owner ≤
          quittingSoloReward reward owner owner := by
        simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
          quittingSoloReward, quittingSingletonTerminal] using hnormal
      linarith
    exact ⟨hfloor, hretained,
      witness.hasPurePaidSureExitResidual source hretained hfloor⟩

/-- The paid-mixed owner-floor face after punishment normality removes the
empty selected cell. -/
def HasPaidMixedOwnerFloorNormalFiniteResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner paid first second : ι) (alpha beta : Bool → ℝ) : Prop :=
  ∃ (orientation : IsStrictMatchingPenniesOrientation alpha beta)
      (labels : RepairedResidualFourLabels owner paid first second),
    let source := paidMixedOwnerFloorRepairedSource owner paid first second
      labels alpha beta orientation
    ∃ firstAction secondAction,
      0 < source.weight firstAction secondAction ∧
      let coalition := repairedResidualWithoutOwner owner paid first second
        false firstAction secondAction
      coalition.Nonempty ∧
        source.ownerFloorNumerator reward / source.denominator ≤
          quittingSetReward reward coalition owner -
            quittingSetReward reward (insert owner coalition) owner ∧
        0 < source.ownerFloorNumerator reward / source.denominator ∧
        HasRepairedOwnerToggleResidual reward owner coalition

omit [Nonempty ι] in
/-- Source-native compilation of a positive paid-mixed owner floor in the
all-normal chamber. -/
theorem QuittingTerminalExploitabilityWitness.paidMixedOwnerFloorNormalResidual
    (witness : QuittingTerminalExploitabilityWitness reward)
    {owner paid first second : ι}
    (labels : RepairedResidualFourLabels owner paid first second)
    {alpha beta : Bool → ℝ}
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (positive : 0 < binaryClearedObservable alpha beta
      (quittingLargeBaseDeletedOwnerFloorCell reward owner {first, second}
        first second))
    (hnormal : IsQuittingNormalPlayer reward owner) :
    HasPaidMixedOwnerFloorNormalFiniteResidual reward owner paid first second
      alpha beta := by
  refine ⟨orientation, labels, ?_⟩
  apply witness.repairedOwnerFloorResidual_of_normal
    (paidMixedOwnerFloorRepairedSource owner paid first second labels
      alpha beta orientation) _ hnormal
  rw [paidMixedOwnerFloorRepairedSource_numerator_eq]
  exact positive

/-- Paid-mixed residual with both the cleared owner-floor face and its empty
cell removed.  Only the two source-linked deletion residues remain numeric. -/
def HasActualPaidMixedNormalFiniteResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseFirst baseSecond first second : ι) (gamma : ℝ) : Prop :=
  let base : Finset ι := {baseFirst, baseSecond}
  let free : Finset ι := {first, second}
  let alpha := quittingLargeBaseFirstRow reward base free first second
  let beta := quittingLargeBaseSecondRow reward base free first second
  ∃ paid owner,
    ((paid = baseFirst ∧ owner = baseSecond) ∨
      (paid = baseSecond ∧ owner = baseFirst)) ∧
    IsStrictMatchingPenniesOrientation alpha beta ∧
    gamma * binaryClearedDenominator alpha beta ≤
      binaryClearedObservable alpha beta
        (quittingLargeBaseLeaveCell reward base free first second paid) ∧
    (binaryDeletedFirstResidual alpha
          (quittingLargeBaseDeletedFirstRow reward owner free first second) ≠ 0 ∨
      binaryDeletedSecondResidual beta
          (quittingLargeBaseDeletedSecondRow reward owner free first second) ≠ 0 ∨
      HasPaidMixedOwnerFloorNormalFiniteResidual reward owner paid first second
        alpha beta)

omit [Nonempty ι] in
/-- All-player punishment normality sharpens the actual mixed deletion
residual by excluding the empty selected owner-floor cell. -/
theorem QuittingTerminalExploitabilityWitness.hasActualPaidMixedNormalFiniteResidual
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hnormal : ∀ who, IsQuittingNormalPlayer reward who)
    (baseFirst baseSecond first second : ι)
    (hbaseNe : baseFirst ≠ baseSecond) (hfreeNe : first ≠ second)
    (hdisjoint : Disjoint ({baseFirst, baseSecond} : Finset ι)
      ({first, second} : Finset ι))
    (hexhaust : ∀ who, who = baseFirst ∨ who = baseSecond ∨
      who = first ∨ who = second)
    (gamma : ℝ)
    (residual : HasActualPaidMixedDeletionResidual reward baseFirst baseSecond
      first second gamma) :
    HasActualPaidMixedNormalFiniteResidual reward baseFirst baseSecond first
      second gamma := by
  dsimp [HasActualPaidMixedDeletionResidual] at residual
  dsimp [HasActualPaidMixedNormalFiniteResidual]
  obtain ⟨paid, owner, hpair, orientation, hpaid, hresidual⟩ := residual
  refine ⟨paid, owner, hpair, orientation, hpaid, ?_⟩
  rcases hresidual with hfirst | hsecond | hfloor
  · exact Or.inl hfirst
  · exact Or.inr (Or.inl hsecond)
  · right
    right
    let labels := repairedResidualFourLabels_of_supportTwoPair
      baseFirst baseSecond first second paid owner hbaseNe hfreeNe hdisjoint
        hexhaust hpair
    exact witness.paidMixedOwnerFloorNormalResidual labels orientation hfloor
      (hnormal owner)

/-- The support-two paid output with the pure arm sharpened by all-player
punishment normality.  The mixed owner-floor face remains compiled through
the deterministic-cell descent. -/
def HasSupportTwoNormalPaidChainResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseFirst baseSecond first second : ι) (gamma : ℝ) : Prop :=
  (∃ paid owner firstAction secondAction,
    ((paid = baseFirst ∧ owner = baseSecond) ∨
      (paid = baseSecond ∧ owner = baseFirst)) ∧
    HasPurePaidNormalChainFiniteResidual reward paid owner first second
      firstAction secondAction) ∨
  HasActualPaidMixedNormalFiniteResidual reward baseFirst baseSecond first
    second gamma

/-- A positive actual support-two gap enters the normality-sharpened paid
chain without losing the pure-cell source. -/
theorem QuittingTerminalExploitabilityWitness.hasSupportTwoNormalPaidChainResidual
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hnormal : ∀ who, IsQuittingNormalPlayer reward who)
    (baseFirst baseSecond first second : ι)
    (hbaseNe : baseFirst ≠ baseSecond) (hfreeNe : first ≠ second)
    (hdisjoint : Disjoint ({baseFirst, baseSecond} : Finset ι)
      ({first, second} : Finset ι))
    (hexhaust : ∀ who, who = baseFirst ∨ who = baseSecond ∨
      who = first ∨ who = second)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (gap : ∀ point ∈ quittingPersistentBaseNashSet reward
        {baseFirst, baseSecond} {first, second},
      gamma ≤ quittingPersistentLargeBaseExcess reward
        {baseFirst, baseSecond} {first, second} point) :
    HasSupportTwoNormalPaidChainResidual reward baseFirst baseSecond first
      second gamma := by
  rcases paidPure_or_paidMixed_of_actual_largeBase_gap_labels reward
      {baseFirst, baseSecond} {first, second} baseFirst baseSecond first second
      hfreeNe rfl rfl hdisjoint hexhaust gamma hgamma gap with hpure | hmixed
  · left
    obtain ⟨paid, owner, firstAction, secondAction, hpair, source⟩ :=
      exists_purePaidBaseLeaveSource_of_actual_paidPure reward
        baseFirst baseSecond first second hbaseNe hfreeNe hdisjoint hexhaust
          gamma hgamma hpure
    exact ⟨paid, owner, firstAction, secondAction, hpair,
      witness.hasPurePaidNormalChainFiniteResidual source (hnormal owner)⟩
  · right
    have hdeletion := witness.hasActualPaidMixedDeletionResidual
      baseFirst baseSecond first second hbaseNe hfreeNe hdisjoint hexhaust
        gamma hgamma hmixed
    exact witness.hasActualPaidMixedNormalFiniteResidual hnormal
      baseFirst baseSecond first second hbaseNe hfreeNe hdisjoint hexhaust
        gamma hdeletion

namespace QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

/-- The source-native paid-chain refinement of the large-base cycle branch. -/
def HasLargeBasePaidChainResidual
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) : Prop :=
  ∃ baseFirst baseSecond first second gamma,
    baseFirst ≠ baseSecond ∧
      first ≠ second ∧
      cycle.persistentBase = {baseFirst, baseSecond} ∧
      cycle.freePlayers = {first, second} ∧
      0 < gamma ∧
      HasSupportTwoNormalPaidChainResidual reward
        baseFirst baseSecond first second gamma

omit [Nonempty ι] in
/-- On four players, a large persistent cycle face is exactly a disjoint
two-by-two partition. -/
theorem largeBase_card_two_and_free_card_two
    (cycle : witness.ReachableStrictToggleSimpleCycle seed)
    (hfour : Fintype.card ι = 4)
    (hlarge : 2 ≤ cycle.persistentBase.card) :
    cycle.persistentBase.card = 2 ∧ cycle.freePlayers.card = 2 := by
  have hunion :
      (cycle.persistentBase ∪ cycle.freePlayers).card ≤ 4 := by
    have hsubset : cycle.persistentBase ∪ cycle.freePlayers ⊆
        (Finset.univ : Finset ι) :=
      Finset.subset_univ _
    have hcard := Finset.card_le_card hsubset
    simpa [Finset.card_univ, hfour] using hcard
  rw [Finset.card_union_of_disjoint
    cycle.disjoint_persistentBase_freePlayers] at hunion
  have hfree := cycle.two_le_card_freePlayers
  omega

/-- A positive large-base gap on an actual four-player cycle enters the
checked support-two paid-chain residual. -/
theorem hasLargeBasePaidChainResidual
    (cycle : witness.ReachableStrictToggleSimpleCycle seed)
    (hfour : Fintype.card ι = 4)
    (hnormal : ∀ who, IsQuittingNormalPlayer reward who)
    (hlarge : 2 ≤ cycle.persistentBase.card)
    (hgap : ∃ gamma : ℝ, 0 < gamma ∧
      ∀ point ∈ quittingPersistentBaseNashSet reward
          cycle.persistentBase cycle.freePlayers,
        gamma ≤ quittingPersistentLargeBaseExcess reward
          cycle.persistentBase cycle.freePlayers point) :
    cycle.HasLargeBasePaidChainResidual := by
  obtain ⟨hbaseCard, hfreeCard⟩ :=
    cycle.largeBase_card_two_and_free_card_two hfour hlarge
  obtain ⟨baseFirst, baseSecond, hbaseNe, hbase⟩ :=
    Finset.card_eq_two.mp hbaseCard
  obtain ⟨first, second, hfreeNe, hfree⟩ :=
    Finset.card_eq_two.mp hfreeCard
  obtain ⟨gamma, hgamma, hgap⟩ := hgap
  have hdisjoint :
      Disjoint ({baseFirst, baseSecond} : Finset ι) {first, second} := by
    rw [← hbase, ← hfree]
    exact cycle.disjoint_persistentBase_freePlayers
  have hunionCard :
      (({baseFirst, baseSecond} : Finset ι) ∪ {first, second}).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisjoint,
      Finset.card_pair hbaseNe, Finset.card_pair hfreeNe]
  have hunion :
      ({baseFirst, baseSecond} : Finset ι) ∪ {first, second} = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hunionCard]
    exact hfour.symm
  have hexhaust : ∀ who,
      who = baseFirst ∨ who = baseSecond ∨ who = first ∨ who = second := by
    intro who
    have hmem : who ∈
        ({baseFirst, baseSecond} : Finset ι) ∪ {first, second} := by
      rw [hunion]
      exact Finset.mem_univ who
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      at hmem
    rcases hmem with (hfirst | hsecond) | hthird | hfourth
    · exact Or.inl hfirst
    · exact Or.inr (Or.inl hsecond)
    · exact Or.inr (Or.inr (Or.inl hthird))
    · exact Or.inr (Or.inr (Or.inr hfourth))
  refine ⟨baseFirst, baseSecond, first, second, gamma,
    hbaseNe, hfreeNe, hbase, hfree, hgamma, ?_⟩
  apply witness.hasSupportTwoNormalPaidChainResidual hnormal
    baseFirst baseSecond first second hbaseNe hfreeNe hdisjoint hexhaust gamma
      hgamma
  rw [hbase, hfree] at hgap
  exact hgap

/-- The strict-toggle semantic residual with its large-base branch refined to
the actual paid chain. -/
def HasPaidRefinedSemanticResidual
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) : Prop :=
  cycle.HasLargeBasePaidChainResidual ∨
    (∃ owner : ι, cycle.persistentBase = {owner} ∧
      ∃ gamma : ℝ, 0 < gamma ∧
        ∀ point ∈ quittingPersistentBaseNashSet reward
            {owner} cycle.freePlayers,
          gamma ≤ quittingSingletonBaseExcess reward owner
            cycle.freePlayers point) ∨
    (cycle.persistentBase = ∅ ∧
      (¬ ∃ root : QuittingRootSimplex ι,
        IsQuittingEmptyBaseSimplexInteriorSolution reward
          cycle.freePlayers root) ∧
      ∀ rho : ℝ, 0 < rho → rho < 1 / 2 →
        ∃ gamma : ℝ, 0 < gamma ∧
          ∀ root ∈ quittingEmptyBaseRhoBox cycle.freePlayers rho,
            gamma ≤ quittingEmptyBaseSimplexDefect reward
              cycle.freePlayers root)

/-- **Four-player paid refinement.**  Every actual reachable strict-toggle
cycle in a terminal-counterexample regime lands in the support-two paid chain,
the singleton-base gap, or the empty-base gap.  The former coarse large-base
`G` chamber no longer appears. -/
theorem hasPaidRefinedSemanticResidual
    (cycle : witness.ReachableStrictToggleSimpleCycle seed)
    (hfour : Fintype.card ι = 4) :
    cycle.HasPaidRefinedSemanticResidual := by
  have hcore :=
    normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
      reward hfour witness.not_exists_uniformEquilibriumPayoff
  have hnormal : ∀ who, IsQuittingNormalPlayer reward who :=
    QuittingLCPClassification.all_punishmentNormal_of_normalCore_eq_univ
      reward hcore
  have hresidual := cycle.hasQuittingStrictToggleSemanticResidual_of_no_uniformPayoff
    witness.not_exists_uniformEquilibriumPayoff
  rcases hresidual with hlarge | hsingleton | hempty
  · exact Or.inl
      (cycle.hasLargeBasePaidChainResidual hfour hnormal hlarge.1 hlarge.2)
  · exact Or.inr (Or.inl hsingleton)
  · exact Or.inr (Or.inr hempty)

end QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

namespace QuittingTerminalExploitabilityWitness

/-- The quantitative full-support source in the final four-player chamber can
seed an actual strict-toggle cycle on the same reward table.  The terminal
witness supplies that cycle's semantic gap, while full normality sharpens its
large-base branch to the source-native paid chain above. -/
theorem fullSupport_fullNormalCore_with_paidRefinedCycle_of_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    {bound : ℝ} (hreward : ∀ S who, |reward S who| ≤ bound) :
    QuittingLCPClassification.normalCore
        (QuittingLCPClassification.normalizedSoloMatrix reward) =
          Finset.univ ∧
      (∀ who, IsQuittingNormalPlayer reward who) ∧
      ∃ packet : QuittingNormalizedSingletonSourcePacket reward,
        packet.support = Finset.univ ∧
        0 < 1 / (1 + (2 * bound / witness.terminalGap) * 3) ∧
        (∀ who,
          1 / (1 + (2 * bound / witness.terminalGap) * 3) ≤
            packet.mass who) ∧
        Nonempty {cycle :
            witness.ReachableStrictToggleSimpleCycle packet.support //
          cycle.HasPaidRefinedSemanticResidual} := by
  obtain ⟨hcore, hnormal, packet, hsupport, hfloor, hmass⟩ :=
    witness.fullSupport_fullNormalCore_of_finFour hreward
  obtain ⟨cycle⟩ :=
    witness.exists_reachableStrictToggleSimpleCycle (by norm_num)
      packet.support
  refine ⟨hcore, hnormal, packet, hsupport, hfloor, hmass, ⟨cycle, ?_⟩⟩
  exact cycle.hasPaidRefinedSemanticResidual (by norm_num)

end QuittingTerminalExploitabilityWitness

end GameTheory
