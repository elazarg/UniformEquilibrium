/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.LawTightCapNashMinimumFace
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio
import UniformEquilibrium.Quitting.Punishment.SingletonCapBindingCollision
import MathUE.FiniteSerialRelation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSingletonNeverCapTightness

/-!
# Strict chambers of a law-tight cap--Nash minimum

At a positive minimum of the law-tight cap--Nash saturation hull, every point
with a positive finite terminal atom has one of three literal carrier-level
forms: full debt support, a same-law reset-rigid return, or singleton/Never
support with a nontrivial cycle of binding collision gains.

This classification consumes supplied carrier, minimum, and source data.  It
does not produce those data, realize a carrier point by one behavioral profile,
consume any chamber, or prove a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A zero-debt coordinate whose total opponent incidence is positive has a
literal positive opponent-incidence coordinate. -/
theorem exists_positive_opponentIncidenceCoordinate_of_total_pos
    (owner : ι) (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (htotal : 0 < quittingTerminalTotalOpponentIncidenceMass owner mass) :
    ∃ other, other ≠ owner ∧
      0 < quittingTerminalOpponentIncidenceMass owner other mass := by
  unfold quittingTerminalTotalOpponentIncidenceMass at htotal
  have hnonneg : ∀ other ∈ Finset.univ.erase owner,
      0 ≤ quittingTerminalOpponentIncidenceMass owner other mass := by
    intro other _
    unfold quittingTerminalOpponentIncidenceMass
    exact Finset.sum_nonneg fun terminal _ ↦ hmass.1 (some terminal)
  obtain ⟨other, hother, hpositive⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonneg).mp htotal
  exact ⟨other, (Finset.mem_erase.mp hother).1, hpositive⟩

/-- The binding-collision edge selected by the solo probe theorem. -/
def QuittingSingletonCapBindingCollisionEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (owner other : ι) : Prop :=
  other ≠ owner ∧
    quittingSingletonCapDefect reward cap owner = 0 ∧
    quittingSingletonCapDefect reward cap other = 0 ∧
    0 < quittingSingletonCollisionGain reward owner other

omit [Fintype ι] in
theorem quittingSingletonCapBindingCollisionEdge_irreflexive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (owner : ι) :
    ¬QuittingSingletonCapBindingCollisionEdge reward cap owner owner := by
  intro hedge
  exact hedge.1 rfl

/-- A unique all-Continue exact cap root and one binding coordinate force a
binding-collision cycle of period at least two. -/
theorem exists_quittingSingletonCapBindingCollisionCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι)
    (hcap : ∀ who, reward (quittingSingletonTerminal who) who ≤ cap who)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (owner : ι)
    (howner : quittingSingletonCapDefect reward cap owner = 0) :
    ∃ cycle : Math.FiniteSerialRelation.PeriodicCycle
        (QuittingSingletonCapBindingCollisionEdge reward cap),
      2 ≤ cycle.period := by
  let binding := {who : ι // quittingSingletonCapDefect reward cap who = 0}
  let edge : binding → binding → Prop := fun first second ↦
    QuittingSingletonCapBindingCollisionEdge reward cap first.1 second.1
  letI : Nonempty binding := ⟨⟨owner, howner⟩⟩
  have hserial : ∀ first : binding, ∃ second : binding, edge first second := by
    intro first
    obtain ⟨other, hne, hzero, hgain⟩ :=
      exists_quittingSingletonCollisionGain_pos_of_unique_allContinue
        reward cap hcap hunique first.1 first.2
    exact ⟨⟨other, hzero⟩, hne, first.2, hzero, hgain⟩
  let bindingCycle := Classical.choice
    (Math.FiniteSerialRelation.nonempty_periodicCycle_of_serial edge hserial)
  let cycle := bindingCycle.map Subtype.val (fun {source target} hedge ↦ by
    change QuittingSingletonCapBindingCollisionEdge reward cap source.1 target.1
      at hedge
    exact hedge)
  refine ⟨cycle, ?_⟩
  exact cycle.two_le_period_of_irreflexive
    (quittingSingletonCapBindingCollisionEdge_irreflexive reward cap)

/-- The reset-rigid chamber retains the fixed law, reset coordinate,
incidence, transfer, toggle, and the literal all-Continue fixed-face arm. -/
structure QuittingLawTightResetRigidChamber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (origin minimum point : QuittingTerminalSemanticLawPoint ι)
    (source : QuittingTerminalSemanticPair ι) where
  owner : ι
  other : ι
  other_ne : other ≠ owner
  returned : QuittingTerminalSemanticPair ι
  dispatch : QuittingFixedLawResetDispatch (reward := reward)
    source point.1 point.2 owner other returned
  returned_mem_face : (returned, point.2) ∈
    quittingLawTightCapNashSaturationMinimumFace reward origin minimum
  allContinue_nash : IsεQuittingRootNash reward returned.2 0
    (quittingAllContinueRoot : ι → PMF Bool)
  allContinue_prefix :
    quittingTerminalSemanticPrefix reward quittingAllContinueRoot returned =
      returned

/-- A positive-incidence zero-debt point in the law-tight minimum level set
is reset-rigid. -/
theorem exists_quittingLawTightResetRigidChamber
    (witness : QuittingTerminalExploitabilityWitness reward)
    (source : QuittingTerminalSemanticPair ι)
    (hsourceMinimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (origin minimum point : QuittingTerminalSemanticLawPoint ι)
    (horigin : origin ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : IsQuittingLawTightCapNashSaturationMinimum
      reward origin minimum)
    (hpoint : point ∈ quittingLawTightCapNashSaturationMinimumFace
      reward origin minimum)
    (owner : ι)
    (hreset : quittingTerminalSemanticDebt point.1 owner = 0)
    (hincidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner point.2) :
    Nonempty
      (QuittingLawTightResetRigidChamber reward origin minimum point source) := by
  have hpointJoint : point ∈ quittingTerminalSemanticLawCarrier reward :=
    quittingLawTightCapNashSaturationHull_subset_carrier
      reward origin horigin hpoint.1
  have hmass := terminalSemanticLawCarrier_mass_mem_stdSimplex point hpointJoint
  obtain ⟨other, hother, hcoordinate⟩ :=
    exists_positive_opponentIncidenceCoordinate_of_total_pos
      owner point.2 hmass hincidence
  obtain ⟨returned, hdispatch⟩ :=
    witness.exists_fixedLawResetDispatch source point.1 point.2 owner other
      hsourceMinimum hsourcePositive hpointJoint hreset hcoordinate
  have hreturnedHull : (returned, point.2) ∈
      quittingLawTightCapNashSaturationHull reward origin :=
    quittingLawTightCapNashSaturationHull_sameLaw_of_debt_le
      reward origin point hpoint.1 returned hdispatch.joint hdispatch.target_ge
  have hreturnedMin : quittingTerminalSemanticDebtSum returned =
      quittingTerminalSemanticDebtSum minimum.1 := by
    apply le_antisymm
    · exact hdispatch.target_ge.trans_eq hpoint.2
    · exact hminimum.debt_le (returned, point.2) hreturnedHull
  have hreturnedFace : (returned, point.2) ∈
      quittingLawTightCapNashSaturationMinimumFace reward origin minimum :=
    ⟨hreturnedHull, hreturnedMin⟩
  have hfixed : IsεQuittingRootNash reward returned.2 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot returned =
        returned := by
    rcases hdispatch.dynamic_exit with habsorbing | hfixed
    · obtain ⟨root, hnash, _habsorption, _hcontinue, hstrict,
          _hjoint, _hreset, _hincidence⟩ := habsorbing
      have hprefixedHull :=
        quittingLawTightCapNashSaturationHull_prefix_mem
          reward origin (returned, point.2) hreturnedHull root hnash
      have hminimumLe := hminimum.debt_le _ hprefixedHull
      rw [hreturnedMin] at hstrict
      exact (not_lt_of_ge hminimumLe hstrict).elim
    · exact hfixed
  exact ⟨{
    owner := owner
    other := other
    other_ne := hother
    returned := returned
    dispatch := hdispatch
    returned_mem_face := hreturnedFace
    allContinue_nash := hfixed.1
    allContinue_prefix := hfixed.2
  }⟩

/-- If an owner's total opponent incidence vanishes, every positive finite
atom is the owner's singleton. -/
theorem terminal_eq_singleton_of_totalOpponentIncidence_eq_zero_of_mass_pos
    (owner : ι) (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (htotal : quittingTerminalTotalOpponentIncidenceMass owner mass = 0)
    (terminal : {S : Finset ι // S.Nonempty})
    (hterminal : 0 < mass (some terminal)) :
    terminal.val = {owner} := by
  have hcoordinateZero : ∀ other, other ≠ owner →
      quittingTerminalOpponentIncidenceMass owner other mass = 0 := by
    intro other hother
    have hmem : other ∈ Finset.univ.erase owner := by simp [hother]
    have hcoordinateNonneg : 0 ≤
        quittingTerminalOpponentIncidenceMass owner other mass := by
      unfold quittingTerminalOpponentIncidenceMass
      exact Finset.sum_nonneg fun candidate _ ↦ hmass.1 (some candidate)
    have hcoordinateLe :
        quittingTerminalOpponentIncidenceMass owner other mass ≤
          quittingTerminalTotalOpponentIncidenceMass owner mass := by
      unfold quittingTerminalTotalOpponentIncidenceMass
      exact Finset.single_le_sum
        (f := fun player ↦
          quittingTerminalOpponentIncidenceMass owner player mass)
        (fun player _ ↦ by
          unfold quittingTerminalOpponentIncidenceMass
          exact Finset.sum_nonneg fun candidate _ ↦
            hmass.1 (some candidate)) hmem
    rw [htotal] at hcoordinateLe
    exact le_antisymm hcoordinateLe hcoordinateNonneg
  have hall : ∀ player ∈ terminal.val, player = owner := by
    intro player hplayer
    by_contra hne
    have hfilter : terminal ∈ Finset.univ.filter
        (fun candidate : {S : Finset ι // S.Nonempty} ↦
          player ∈ candidate.val ∧ player ≠ owner) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ terminal, hplayer, hne⟩
    have hle : mass (some terminal) ≤
        quittingTerminalOpponentIncidenceMass owner player mass := by
      unfold quittingTerminalOpponentIncidenceMass
      exact Finset.single_le_sum
        (fun candidate _ ↦ hmass.1 (some candidate)) hfilter
    rw [hcoordinateZero player hne] at hle
    linarith
  obtain ⟨member, hmember⟩ := terminal.property
  have howner : owner ∈ terminal.val := by simpa [hall member hmember] using hmember
  ext player
  constructor
  · intro hplayer
    exact Finset.mem_singleton.mpr (hall player hplayer)
  · intro hplayer
    have heq : player = owner := Finset.mem_singleton.mp hplayer
    simpa [heq] using howner

/-- Exact support data for the singleton/Never chamber before cap tightness
is invoked. -/
structure QuittingSingletonNeverMinimumSupport
    (point : QuittingTerminalSemanticLawPoint ι) where
  owner : ι
  owner_debt_zero : quittingTerminalSemanticDebt point.1 owner = 0
  unique_zero_debt : ∀ other,
    quittingTerminalSemanticDebt point.1 other = 0 → other = owner
  singletonMass : ℝ
  singletonMass_pos : 0 < singletonMass
  singletonMass_le_one : singletonMass ≤ 1
  finite_mass : ∀ terminal : {S : Finset ι // S.Nonempty},
    point.2 (some terminal) =
      if terminal.val = {owner} then singletonMass else 0
  never_mass : point.2 none = 1 - singletonMass

/-- If some coordinate has zero debt, every zero-debt coordinate has zero
total opponent incidence, and one finite atom is positive, then the zero-debt
owner is unique and the law is supported exactly on its singleton and Never. -/
theorem exists_quittingSingletonNeverMinimumSupport
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hexistsZero : ∃ owner, quittingTerminalSemanticDebt point.1 owner = 0)
    (hzeroIncidence : ∀ owner,
      quittingTerminalSemanticDebt point.1 owner = 0 →
        quittingTerminalTotalOpponentIncidenceMass owner point.2 = 0)
    (terminal : {S : Finset ι // S.Nonempty})
    (hterminal : 0 < point.2 (some terminal)) :
    Nonempty (QuittingSingletonNeverMinimumSupport point) := by
  obtain ⟨owner, hownerZero⟩ := hexistsZero
  have hmass := terminalSemanticLawCarrier_mass_mem_stdSimplex point hpoint
  have hterminalOwner :=
    terminal_eq_singleton_of_totalOpponentIncidence_eq_zero_of_mass_pos
      owner point.2 hmass (hzeroIncidence owner hownerZero) terminal hterminal
  have hunique : ∀ other,
      quittingTerminalSemanticDebt point.1 other = 0 → other = owner := by
    intro other hotherZero
    have hterminalOther :=
      terminal_eq_singleton_of_totalOpponentIncidence_eq_zero_of_mass_pos
        other point.2 hmass (hzeroIncidence other hotherZero) terminal hterminal
    have hsingletons : ({owner} : Finset ι) = {other} :=
      hterminalOwner.symm.trans hterminalOther
    exact (Finset.singleton_inj.mp hsingletons).symm
  let p := point.2 (some (quittingSingletonTerminal owner))
  have hp : 0 < p := by
    have hterminalEq : terminal = quittingSingletonTerminal owner :=
      Subtype.ext hterminalOwner
    simpa only [p, hterminalEq] using hterminal
  have hfinite : ∀ candidate : {S : Finset ι // S.Nonempty},
      point.2 (some candidate) =
        if candidate.val = {owner} then p else 0 := by
    intro candidate
    by_cases hcandidate : candidate.val = {owner}
    · rw [if_pos hcandidate]
      have hcandidateEq : candidate = quittingSingletonTerminal owner :=
        Subtype.ext hcandidate
      exact congrArg (fun selected ↦ point.2 (some selected))
        hcandidateEq
    · rw [if_neg hcandidate]
      by_cases hzero : point.2 (some candidate) = 0
      · exact hzero
      · have hpositive : 0 < point.2 (some candidate) :=
          lt_of_le_of_ne (hmass.1 (some candidate)) (Ne.symm hzero)
        exact (hcandidate
          (terminal_eq_singleton_of_totalOpponentIncidence_eq_zero_of_mass_pos
            owner point.2 hmass (hzeroIncidence owner hownerZero)
              candidate hpositive)).elim
  have hpLe : p ≤ 1 := by
    calc
      p ≤ ∑ outcome, point.2 outcome := by
        exact Finset.single_le_sum
          (fun outcome _ ↦ hmass.1 outcome)
          (Finset.mem_univ (some (quittingSingletonTerminal owner)))
      _ = 1 := hmass.2
  have hnever : point.2 none = 1 - p := by
    have hsum := hmass.2
    rw [Fintype.sum_option] at hsum
    have hfiniteSum :
        ∑ candidate : {S : Finset ι // S.Nonempty},
          point.2 (some candidate) = p := by
      simp_rw [hfinite]
      have hpredicate : ∀ candidate : {S : Finset ι // S.Nonempty},
          candidate.val = {owner} ↔
            candidate = quittingSingletonTerminal owner := by
        intro candidate
        constructor
        · intro heq
          exact Subtype.ext heq
        · intro heq
          exact congrArg Subtype.val heq
      simp_rw [hpredicate]
      simp
    rw [hfiniteSum] at hsum
    linarith
  exact ⟨{
    owner := owner
    owner_debt_zero := hownerZero
    unique_zero_debt := hunique
    singletonMass := p
    singletonMass_pos := hp
    singletonMass_le_one := hpLe
    finite_mass := hfinite
    never_mass := hnever
  }⟩

/-- The fully literal singleton/Never arm of strict saturation. -/
structure QuittingSingletonNeverBindingCycleChamber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι) where
  support : QuittingSingletonNeverMinimumSupport point
  cap_binding : point.1.2 support.owner =
    reward (quittingSingletonTerminal support.owner) support.owner
  allContinue_nash : IsεQuittingRootNash reward point.1.2 0
    (quittingAllContinueRoot : ι → PMF Bool)
  unique_exact_root : ∀ root : ι → PMF Bool,
    IsεQuittingRootNash reward point.1.2 0 root →
      root = (quittingAllContinueRoot : ι → PMF Bool)
  cycle : Math.FiniteSerialRelation.PeriodicCycle
    (QuittingSingletonCapBindingCollisionEdge reward point.1.2)
  two_le_period : 2 ≤ cycle.period

/-- Every positive point on a law-tight minimum level set has full debt
support, a reset-rigid same-law return, or the singleton/Never binding cycle.
This is a carrier classification only; none of the three arms supplies a
behavioral realization or consumes the strict chamber. -/
theorem lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle
    (witness : QuittingTerminalExploitabilityWitness reward)
    (source : QuittingTerminalSemanticPair ι)
    (hsourceMinimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (origin minimum point : QuittingTerminalSemanticLawPoint ι)
    (horigin : origin ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : IsQuittingLawTightCapNashSaturationMinimum
      reward origin minimum)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum.1)
    (hpoint : point ∈ quittingLawTightCapNashSaturationMinimumFace
      reward origin minimum)
    (terminal : {S : Finset ι // S.Nonempty})
    (hterminal : 0 < point.2 (some terminal)) :
    (∀ who, 0 < quittingTerminalSemanticDebt point.1 who) ∨
      Nonempty
        (QuittingLawTightResetRigidChamber
          reward origin minimum point source) ∨
      Nonempty (QuittingSingletonNeverBindingCycleChamber reward point) := by
  have hpointJoint : point ∈ quittingTerminalSemanticLawCarrier reward :=
    quittingLawTightCapNashSaturationHull_subset_carrier
      reward origin horigin hpoint.1
  have hpointSemantic : point.1 ∈ quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier point hpointJoint
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt point.1 who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpointSemantic
  by_cases hzero : ∃ owner,
      quittingTerminalSemanticDebt point.1 owner = 0
  · by_cases hpositiveIncidence : ∃ owner,
        quittingTerminalSemanticDebt point.1 owner = 0 ∧
          0 < quittingTerminalTotalOpponentIncidenceMass owner point.2
    · right
      left
      obtain ⟨owner, hownerZero, hownerIncidence⟩ := hpositiveIncidence
      exact exists_quittingLawTightResetRigidChamber
        witness source hsourceMinimum hsourcePositive origin minimum point
          horigin hminimum hpoint owner hownerZero hownerIncidence
    · right
      right
      have hmass := terminalSemanticLawCarrier_mass_mem_stdSimplex
        (reward := reward) point hpointJoint
      have hzeroIncidence : ∀ owner,
          quittingTerminalSemanticDebt point.1 owner = 0 →
            quittingTerminalTotalOpponentIncidenceMass owner point.2 = 0 := by
        intro owner hownerZero
        have hnotPositive : ¬ 0 <
            quittingTerminalTotalOpponentIncidenceMass owner point.2 := by
          intro hpositive
          exact hpositiveIncidence ⟨owner, hownerZero, hpositive⟩
        have hnonneg : 0 ≤
            quittingTerminalTotalOpponentIncidenceMass owner point.2 := by
          unfold quittingTerminalTotalOpponentIncidenceMass
          exact Finset.sum_nonneg fun other _ => by
            unfold quittingTerminalOpponentIncidenceMass
            exact Finset.sum_nonneg fun candidate _ =>
              hmass.1 (some candidate)
        exact le_antisymm (le_of_not_gt hnotPositive) hnonneg
      obtain ⟨support⟩ := exists_quittingSingletonNeverMinimumSupport
        point hpointJoint hzero hzeroIncidence terminal hterminal
      have hcapBinding :=
        terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward
          point hpointJoint support.owner support.singletonMass
            support.singletonMass_pos support.finite_mass support.never_mass
              support.owner_debt_zero
      have hallContinueNash : IsεQuittingRootNash reward point.1.2 0
          (quittingAllContinueRoot : ι → PMF Bool) :=
        (quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue
          hminimum hminimumPositive hpoint quittingAllContinueRoot).2 rfl
      have hunique : ∀ root : ι → PMF Bool,
          IsεQuittingRootNash reward point.1.2 0 root →
            root = (quittingAllContinueRoot : ι → PMF Bool) := by
        intro root hnash
        exact
          (quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue
            hminimum hminimumPositive hpoint root).1 hnash
      have hcap : ∀ who,
          reward (quittingSingletonTerminal who) who ≤ point.1.2 who :=
        (isZeroQuittingRootNash_allContinue_iff_singleton_le
          reward point.1.2).1 hallContinueNash
      have hownerDefect : quittingSingletonCapDefect reward point.1.2
          support.owner = 0 := by
        unfold quittingSingletonCapDefect
        linarith
      obtain ⟨cycle, hcyclePeriod⟩ :=
        exists_quittingSingletonCapBindingCollisionCycle
          reward point.1.2 hcap hunique support.owner hownerDefect
      exact ⟨{
        support := support
        cap_binding := hcapBinding
        allContinue_nash := hallContinueNash
        unique_exact_root := hunique
        cycle := cycle
        two_le_period := hcyclePeriod
      }⟩
  · left
    intro who
    exact lt_of_le_of_ne (hdebtNonneg who) fun heq =>
      hzero ⟨who, heq.symm⟩

end GameTheory
