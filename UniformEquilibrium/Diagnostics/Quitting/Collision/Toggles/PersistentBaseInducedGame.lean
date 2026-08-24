/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.PMFProduct.PrincipalRestriction
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.InducedFaceNashCompact
import UniformEquilibrium.Quitting.PayoffProcess.FiniteStageSelector
import UniformEquilibrium.Quitting.Boundary.Repair.SureSetOwnerRepair

/-!
# The finite binary game induced by a persistent quitting base

Each free player chooses Quit or Continue once.  The terminal coalition is the
persistent base union the free quitters.  The exact mixed-Nash set is nonempty
and compact in the product-simplex coordinates used by the finite-game Nash
theorem.
-/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability
open Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Embed the quitting free-player actions back into the ambient player set. -/
def quittingPersistentBaseFreeQuitters
    (free : Finset ι) (action : (who : free) → Bool) : Finset ι :=
  (Finset.univ.filter fun who : free => action who).map
    ⟨Subtype.val, Subtype.val_injective⟩

/-- The induced binary-game utility on a persistent-base face. -/
def quittingPersistentBaseUtility
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) : ((who : free) → Bool) → free → ℝ :=
  fun action who =>
    quittingSetReward reward
      (base ∪ quittingPersistentBaseFreeQuitters free action) who.1

/-- Exact mixed Nash points of the induced persistent-base binary game. -/
def quittingPersistentBaseNashSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) :
    Set (mixedPolytope (quittingBinaryForm free).sig) :=
  mixedNashPolytopeSet (quittingPersistentBaseUtility reward base free)

/-- Extend one mixed profile of the induced game to the ambient quitting row:
base players Quit surely, free players use their mixed laws, and all remaining
players Continue surely. -/
def quittingPersistentBaseRootOfProfile
    (base free : Finset ι)
    (profile : Profile (quittingBinaryForm free).sig.mixed) : ι → PMF Bool :=
  fun who => if _hbase : who ∈ base then PMF.pure true
    else if hfree : who ∈ free then
      (profile ⟨who, hfree⟩).toPMF
    else PMF.pure false

/-- Extend one mixed point of the induced game to the ambient quitting row. -/
def quittingPersistentBaseRoot
    (base free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) : ι → PMF Bool :=
  quittingPersistentBaseRootOfProfile base free
    (ofPolytope (quittingBinaryForm free).sig point.2)

omit [Fintype ι] in
@[simp] theorem quittingPersistentBaseRoot_apply_of_mem_base
    (base free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    {who : ι} (hwho : who ∈ base) :
    quittingPersistentBaseRoot base free point who = PMF.pure true := by
  simp [quittingPersistentBaseRoot, quittingPersistentBaseRootOfProfile, hwho]

omit [Fintype ι] in
@[simp] theorem quittingPersistentBaseRoot_apply_of_mem_free
    (base free : Finset ι) (hdisjoint : Disjoint base free)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    {who : ι} (hwho : who ∈ free) :
    quittingPersistentBaseRoot base free point who =
      ((ofPolytope (quittingBinaryForm free).sig point.2) ⟨who, hwho⟩).toPMF := by
  have hnotBase : who ∉ base := fun hbase => Finset.disjoint_left.mp hdisjoint hbase hwho
  simp [quittingPersistentBaseRoot, quittingPersistentBaseRootOfProfile,
    hnotBase, hwho]

omit [Fintype ι] in
@[simp] theorem quittingPersistentBaseRoot_apply_of_outside
    (base free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    {who : ι} (hwho : who ∉ base ∪ free) :
    quittingPersistentBaseRoot base free point who = PMF.pure false := by
  have hbase : who ∉ base := fun hmem => hwho (Finset.mem_union_left free hmem)
  have hfree : who ∉ free := fun hmem => hwho (Finset.mem_union_right base hmem)
  simp [quittingPersistentBaseRoot, quittingPersistentBaseRootOfProfile,
    hbase, hfree]

omit [Fintype ι] in
@[simp] theorem quittingPersistentBaseRootOfProfile_apply_of_mem_base
    (base free : Finset ι)
    (profile : Profile (quittingBinaryForm free).sig.mixed)
    {who : ι} (hwho : who ∈ base) :
    quittingPersistentBaseRootOfProfile base free profile who = PMF.pure true := by
  simp [quittingPersistentBaseRootOfProfile, hwho]

omit [Fintype ι] in
@[simp] theorem quittingPersistentBaseRootOfProfile_apply_of_mem_free
    (base free : Finset ι) (hdisjoint : Disjoint base free)
    (profile : Profile (quittingBinaryForm free).sig.mixed)
    {who : ι} (hwho : who ∈ free) :
    quittingPersistentBaseRootOfProfile base free profile who =
      (profile ⟨who, hwho⟩).toPMF := by
  have hnotBase : who ∉ base := fun hbase =>
    Finset.disjoint_left.mp hdisjoint hbase hwho
  simp [quittingPersistentBaseRootOfProfile, hnotBase, hwho]

omit [Fintype ι] in
@[simp] theorem quittingPersistentBaseRootOfProfile_apply_of_outside
    (base free : Finset ι)
    (profile : Profile (quittingBinaryForm free).sig.mixed)
    {who : ι} (hwho : who ∉ base ∪ free) :
    quittingPersistentBaseRootOfProfile base free profile who = PMF.pure false := by
  have hbase : who ∉ base := fun hmem => hwho (Finset.mem_union_left free hmem)
  have hfree : who ∉ free := fun hmem => hwho (Finset.mem_union_right base hmem)
  simp [quittingPersistentBaseRootOfProfile, hbase, hfree]

/-- The ambient joint action obtained by extending a free-player action has
exactly the persistent base and the free quitters as its quitter coalition. -/
theorem quittingQuitters_principalExtend_persistentBase
    (base free : Finset ι) (hdisjoint : Disjoint base free)
    (action : (who : free) → Bool) :
    quittingQuitters
        (principalExtend free (fun who => decide (who ∈ base)) action) =
      base ∪ quittingPersistentBaseFreeQuitters free action := by
  ext who
  by_cases hfree : who ∈ free
  · have hbase : who ∉ base := fun hmem =>
      Finset.disjoint_left.mp hdisjoint hmem hfree
    simp [quittingQuitters, principalExtend, quittingPersistentBaseFreeQuitters,
      hfree, hbase]
  · simp [quittingQuitters, principalExtend, quittingPersistentBaseFreeQuitters,
      hfree]

/-- Pointwise identification of the induced utility with the actual ambient
zero-tail quitting payoff after fixed-coordinate extension. -/
theorem quittingRootPayoff_principalExtend_persistentBase
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (hbase : base.Nonempty)
    (hdisjoint : Disjoint base free)
    (action : (who : free) → Bool) (who : free) :
    quittingRootPayoff reward 0
        (principalExtend free (fun player => decide (player ∈ base)) action)
        who.1 =
      quittingPersistentBaseUtility reward base free action who := by
  have hcoalition :=
    quittingQuitters_principalExtend_persistentBase base free hdisjoint action
  have hnonempty :
      (quittingQuitters
        (principalExtend free (fun player => decide (player ∈ base)) action)).Nonempty := by
    rw [hcoalition]
    exact hbase.mono (Finset.subset_union_left)
  simp only [quittingRootPayoff, hnonempty, dif_pos,
    quittingPersistentBaseUtility, quittingSetReward]
  rw [dif_pos (hbase.mono Finset.subset_union_left)]
  apply congrArg (fun terminal => reward terminal who.1)
  exact Subtype.ext hcoalition

/-- **Expected-utility adapter.**  The induced normal-form expected utility is
exactly the ambient quitting-root payoff of the extended independent row. -/
theorem expectedUtility_persistentBase_eq_rootExpectedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (hbase : base.Nonempty)
    (hdisjoint : Disjoint base free)
    (profile : Profile (quittingBinaryForm free).sig.mixed) (who : free) :
    expectedUtility (quittingPersistentBaseUtility reward base free) who
        ((quittingBinaryForm free).mixed.play profile) =
      quittingRootExpectedPayoff reward 0
        (quittingPersistentBaseRootOfProfile base free profile) who.1 := by
  rw [expectedUtility_quittingBinaryForm_eq]
  symm
  unfold quittingRootExpectedPayoff
  let outside : ι → Bool := fun player => decide (player ∈ base)
  have hpure : ∀ player, player ∉ free →
      quittingPersistentBaseRootOfProfile base free profile player =
        PMF.pure (outside player) := by
    intro player hplayer
    by_cases hbasePlayer : player ∈ base
    · simp [outside, hbasePlayer,
        quittingPersistentBaseRootOfProfile_apply_of_mem_base]
    · have houtside : player ∉ base ∪ free := by simp [hbasePlayer, hplayer]
      simp [outside, hbasePlayer,
        quittingPersistentBaseRootOfProfile_apply_of_outside base free profile houtside]
  rw [expect_pmfPi_eq_principal
    (quittingPersistentBaseRootOfProfile base free profile) free outside hpure]
  have hmarginals :
      principalMarginals
          (quittingPersistentBaseRootOfProfile base free profile) free =
        fun player => (profile player).toPMF := by
    funext player
    exact quittingPersistentBaseRootOfProfile_apply_of_mem_free
      base free hdisjoint profile player.2
  rw [hmarginals]
  apply congrArg (Math.Probability.expect
    (pmfPi (fun player => (profile player).toPMF)))
  funext action
  exact quittingRootPayoff_principalExtend_persistentBase
    reward base free hbase hdisjoint action who

omit [Fintype ι] in
/-- Updating a free coordinate before ambient extension is the same as
updating that coordinate's ambient PMF afterwards. -/
theorem quittingPersistentBaseRootOfProfile_update
    (base free : Finset ι) (hdisjoint : Disjoint base free)
    (profile : Profile (quittingBinaryForm free).sig.mixed)
    (who : free) (deviation : FinDist Bool) :
    quittingPersistentBaseRootOfProfile base free
        (Function.update profile who deviation) =
      Function.update
        (quittingPersistentBaseRootOfProfile base free profile)
        who.1 deviation.toPMF := by
  funext player
  by_cases heq : player = who.1
  · subst player
    have hnotBase : who.1 ∉ base := fun hbase =>
      Finset.disjoint_left.mp hdisjoint hbase who.2
    simp [quittingPersistentBaseRootOfProfile, hnotBase, who.2]
  · rw [Function.update_of_ne heq]
    by_cases hbase : player ∈ base
    · simp [quittingPersistentBaseRootOfProfile, hbase]
    · by_cases hfree : player ∈ free
      · have hsubtype : (⟨player, hfree⟩ : free) ≠ who := by
          intro heqSubtype
          exact heq (congrArg Subtype.val heqSubtype)
        simp [quittingPersistentBaseRootOfProfile, hbase, hfree,
          Function.update_of_ne hsubtype]
      · simp [quittingPersistentBaseRootOfProfile, hbase, hfree]

omit [Fintype ι] in
/-- Membership in the analytic Nash carrier is the semantic Nash property of
the represented induced mixed profile. -/
theorem isNash_of_mem_quittingPersistentBaseNashSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet reward base free) :
    IsNash (quittingBinaryForm free).mixed
      (euPreference (quittingPersistentBaseUtility reward base free))
      (ofPolytope (quittingBinaryForm free).sig point.2) := by
  change point.1 ∈ bestReplies (quittingBinaryForm free)
    (quittingPersistentBaseUtility reward base free) point.1 at hpoint
  apply (probs_mem_bestReplies_self_iff_isNash
    (F := quittingBinaryForm free)
    (quittingPersistentBaseUtility reward base free) _).mp
  simpa [probs_ofPolytope (quittingBinaryForm free).sig point.2] using hpoint

/-- An induced Nash point gives the exact pure-Quit and pure-Continue
inequalities for every free coordinate in the actual ambient quitting row. -/
theorem quittingPersistentBaseRoot_free_purePayoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (hbase : base.Nonempty)
    (hdisjoint : Disjoint base free)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet reward base free)
    (who : ι) (hwho : who ∈ free) :
    quittingRootQuitPayoff reward 0
        (quittingPersistentBaseRoot base free point) who ≤
        quittingRootSuccessorPayoff reward 0
          (quittingPersistentBaseRoot base free point) who ∧
      quittingRootContinuePayoff reward 0
        (quittingPersistentBaseRoot base free point) who ≤
        quittingRootSuccessorPayoff reward 0
          (quittingPersistentBaseRoot base free point) who := by
  let profile := ofPolytope (quittingBinaryForm free).sig point.2
  let freeWho : free := ⟨who, hwho⟩
  have hnash := isNash_of_mem_quittingPersistentBaseNashSet
    reward base free point hpoint
  have hpure := (isNash_mixed_iff profile).mp hnash
  have hcurrent := expectedUtility_persistentBase_eq_rootExpectedPayoff
    reward base free hbase hdisjoint profile freeWho
  have hquit := hpure freeWho true
  have hcontinue := hpure freeWho false
  have hquitExpected := expectedUtility_persistentBase_eq_rootExpectedPayoff
    reward base free hbase hdisjoint
      (Function.update profile freeWho (FinDist.pure true)) freeWho
  have hcontinueExpected := expectedUtility_persistentBase_eq_rootExpectedPayoff
    reward base free hbase hdisjoint
      (Function.update profile freeWho (FinDist.pure false)) freeWho
  have hquitRoot := quittingPersistentBaseRootOfProfile_update
    base free hdisjoint profile freeWho (FinDist.pure true)
  have hcontinueRoot := quittingPersistentBaseRootOfProfile_update
    base free hdisjoint profile freeWho (FinDist.pure false)
  change quittingRootExpectedPayoff reward 0
      (Function.update
        (quittingPersistentBaseRootOfProfile base free profile) freeWho.1
        (PMF.pure true)) freeWho.1 ≤
      quittingRootExpectedPayoff reward 0
        (quittingPersistentBaseRootOfProfile base free profile) freeWho.1 ∧
    quittingRootExpectedPayoff reward 0
      (Function.update
        (quittingPersistentBaseRootOfProfile base free profile) freeWho.1
        (PMF.pure false)) freeWho.1 ≤
      quittingRootExpectedPayoff reward 0
        (quittingPersistentBaseRootOfProfile base free profile) freeWho.1
  constructor
  · rw [← show (FinDist.pure true).toPMF = PMF.pure true by simp,
      ← hquitRoot, ← hquitExpected, ← hcurrent]
    exact hquit
  · rw [← show (FinDist.pure false).toPMF = PMF.pure false by simp,
      ← hcontinueRoot, ← hcontinueExpected, ← hcurrent]
    exact hcontinue

omit [Fintype ι] in
/-- The complete induced mixed-Nash set is compact. -/
theorem isCompact_quittingPersistentBaseNashSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) :
    IsCompact (quittingPersistentBaseNashSet reward base free) :=
  @isCompact_mixedNashPolytopeSet free inferInstance inferInstance
    (quittingBinaryForm free) inferInstance
    (quittingPersistentBaseUtility reward base free)

omit [Fintype ι] in
/-- The complete induced mixed-Nash set is nonempty. -/
theorem quittingPersistentBaseNashSet_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) :
    (quittingPersistentBaseNashSet reward base free).Nonempty :=
  @mixedNashPolytopeSet_nonempty free inferInstance inferInstance
    (quittingBinaryForm free) inferInstance inferInstance
    (quittingPersistentBaseUtility reward base free)

omit [Fintype ι] in
/-- Every continuous excess on the full induced Nash set has the exact
accepted-point/positive-attained-gap alternative used by the persistent-base
semantic dispatch. -/
theorem exists_persistentBaseNash_nonpos_or_pos_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι)
    (excess : mixedPolytope (quittingBinaryForm free).sig → ℝ)
    (hexcess : Continuous excess) :
    (∃ point ∈ quittingPersistentBaseNashSet reward base free,
        excess point ≤ 0) ∨
      ∃ gamma : ℝ, 0 < gamma ∧
        ∀ point ∈ quittingPersistentBaseNashSet reward base free,
          gamma ≤ excess point :=
  @exists_mixedNash_nonpos_or_pos_gap free inferInstance inferInstance
    (quittingBinaryForm free) inferInstance inferInstance
    (quittingPersistentBaseUtility reward base free) excess hexcess

end GameTheory
