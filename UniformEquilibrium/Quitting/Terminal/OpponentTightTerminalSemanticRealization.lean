/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.FiniteIndependentMixture
import MathUE.ProbabilityMassFunction.CompactStoppingLaw
import MathUE.PMFProduct.Conditioning
import UniformEquilibrium.Quitting.Paths.FiniteStoppingLawMixture
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum
import UniformEquilibrium.Quitting.Terminal.StrategicallyPrecompactWatchdogProperBoundary
import UniformEquilibrium.Quitting.Terminal.StoppingLawCanonicalization
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Opponent-tight terminal-semantic realization

Weak convergence of complete quitting clocks need not preserve terminal
semantics at the joint all-Never point.  This file proves continuity when
every player faces a uniformly tight opponent clock.  The cap statement is
for unrestricted behavioral deviations, using pure-time extremality only to
represent their exact supremum.

The weak laws live on `WithTop Nat` through `CompactStoppingLaw`.  No result
asserts convergence of the Never atom.  All sequential conclusions concern
one already selected weakly convergent subsequence.
-/

noncomputable section

namespace GameTheory

open Filter MeasureTheory Set StochasticGame
open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open _root_.Math.Probability.DiscreteHazard
open scoped BigOperators ENNReal Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- Clopen late-or-Never tail mass of one compact stopping law. -/
def compactStoppingLawTailMass (law : CompactStoppingLaw) (horizon : Nat) : Real :=
  law.realMass {choice | WithTop.some horizon < choice}

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- A deterministic clock at the cutoff has zero late-or-Never tail mass. -/
@[simp] theorem compactStoppingLawTailMass_ofPMF_pure_some_self (time : Nat) :
    compactStoppingLawTailMass
        (CompactStoppingLaw.ofPMF (PMF.pure (WithTop.some time))) time = 0 := by
  unfold compactStoppingLawTailMass
  rw [CompactStoppingLaw.realMass_eq_pmfMass_toReal
    (CompactStoppingLaw.ofPMF (PMF.pure (WithTop.some time)))
    (compactStoppingTime_tail_isClopen time).1.measurableSet]
  rw [CompactStoppingLaw.toPMF_ofPMF]
  have hmass : _root_.Math.ProbabilityMassFunction.pmfMass
      (PMF.pure (WithTop.some time))
        (fun choice => choice ∈ {choice | WithTop.some time < choice}) = 0 := by
    unfold _root_.Math.ProbabilityMassFunction.pmfMass
    rw [ENNReal.tsum_eq_zero]
    intro choice
    by_cases hchoice : choice = WithTop.some time
    · subst choice
      simp [_root_.Math.ProbabilityMassFunction.pmfMask]
    · simp only [_root_.Math.ProbabilityMassFunction.pmfMask]
      split_ifs
      · rw [PMF.pure_apply_of_ne _ _ hchoice]
      · rfl
  rw [hmass]
  rfl

/-- Probability that every independent complete clock is later than the
displayed horizon or Never. -/
def quittingJointTailProduct
    (laws : ι → CompactStoppingLaw) (horizon : Nat) : Real :=
  ∏ who, compactStoppingLawTailMass (laws who) horizon

/-- Probability that every opponent of `who` is later than the displayed
horizon or Never. -/
def quittingOpponentTailProduct
    (laws : ι → CompactStoppingLaw) (who : ι) (horizon : Nat) : Real :=
  ∏ opponent ∈ Finset.univ.erase who,
    compactStoppingLawTailMass (laws opponent) horizon

/-- Product of the limiting singleton Never masses of one owner's opponents. -/
def quittingOpponentNeverProduct
    (laws : ι → CompactStoppingLaw) (who : ι) : Real :=
  ∏ opponent ∈ Finset.univ.erase who,
    (laws opponent).realMass ({⊤} : Set CompactStoppingTime)

omit [Nontrivial ι] in
/-- Deleted live-spine survival factors coordinatewise into the individual
opponent hazard survivals. -/
theorem quittingOpponentSurvivalWeight_eq_prod_hazardSurvival
    (roots : Nat → ι → PMF Bool) (who : ι) (time : Nat) :
    quittingOpponentSurvivalWeight roots who 0 time =
      ∏ opponent ∈ Finset.univ.erase who,
        quittingHazardSurvival (fun stage => roots stage opponent) time := by
  have hstage (stage : Nat) :
      quittingFixedOpponentsContinueMass roots who stage =
        ∏ opponent ∈ Finset.univ.erase who,
          (roots stage opponent false).toReal := by
    unfold quittingFixedOpponentsContinueMass
    rw [quittingStationaryContinueMass_eq_prod_continueProbability,
      ← Finset.mul_prod_erase Finset.univ
        (fun player =>
          (Function.update (roots stage) who (PMF.pure false) player false).toReal)
        (Finset.mem_univ who)]
    simp only [Function.update_self, PMF.pure_apply, if_pos,
      ENNReal.toReal_one, one_mul]
    apply Finset.prod_congr rfl
    intro opponent hopponent
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hopponent)]
  unfold quittingOpponentSurvivalWeight
  simp_rw [Nat.zero_add, hstage]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro opponent _
  rw [quittingHazardSurvival_eq_prod]

/-- Tightness of the opponents of one owner along an already selected compact
law sequence. -/
def QuittingOpponentTightAtLawSequence
    (lawSeq : Nat → ι → CompactStoppingLaw) (who : ι) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ horizon,
    ∀ᶠ n in atTop, quittingOpponentTailProduct (lawSeq n) who horizon < ε

/-- Uniform opponent tightness along one already selected sequence of compact
law profiles.  This is the epsilon form of vanishing opponent-tail limsup. -/
def QuittingOpponentTightLawSequence
    (lawSeq : Nat → ι → CompactStoppingLaw) : Prop :=
  ∀ who, QuittingOpponentTightAtLawSequence lawSeq who

/-- Uniform tightness of the joint late-or-Never event along one selected
sequence. -/
def QuittingJointTightLawSequence
    (lawSeq : Nat → ι → CompactStoppingLaw) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ horizon,
    ∀ᶠ n in atTop, quittingJointTailProduct (lawSeq n) horizon < ε

omit [Nontrivial ι] in
/-- A joint late-tail product is bounded by every deleted-player tail
product. -/
theorem quittingJointTailProduct_le_opponentTailProduct
    (laws : ι → CompactStoppingLaw) (who : ι) (horizon : Nat) :
    quittingJointTailProduct laws horizon ≤
      quittingOpponentTailProduct laws who horizon := by
  let factor := fun player => compactStoppingLawTailMass (laws player) horizon
  have hsplit := Finset.mul_prod_erase Finset.univ factor (Finset.mem_univ who)
  have hnonneg : 0 ≤ ∏ opponent ∈ Finset.univ.erase who, factor opponent :=
    Finset.prod_nonneg fun opponent _ =>
      CompactStoppingLaw.realMass_nonneg (laws opponent)
        {choice | WithTop.some horizon < choice}
  calc
    quittingJointTailProduct laws horizon =
        factor who * ∏ opponent ∈ Finset.univ.erase who, factor opponent := by
      simpa [quittingJointTailProduct, factor] using hsplit.symm
    _ ≤ 1 * ∏ opponent ∈ Finset.univ.erase who, factor opponent :=
      mul_le_mul_of_nonneg_right
        (CompactStoppingLaw.realMass_le_one (laws who)
          {choice | WithTop.some horizon < choice}) hnonneg
    _ = quittingOpponentTailProduct laws who horizon := by
      simp [quittingOpponentTailProduct, factor]

/-- Opponent tightness implies tightness of the smaller joint late event. -/
theorem QuittingOpponentTightLawSequence.joint
    {lawSeq : Nat → ι → CompactStoppingLaw}
    (htight : QuittingOpponentTightLawSequence lawSeq) :
    QuittingJointTightLawSequence lawSeq := by
  intro ε hε
  let who : ι := Classical.choice (inferInstance : Nonempty ι)
  obtain ⟨horizon, htail⟩ := htight who ε hε
  refine ⟨horizon, htail.mono ?_⟩
  intro n hn
  exact lt_of_le_of_lt
    (quittingJointTailProduct_le_opponentTailProduct (lawSeq n) who horizon) hn

omit [DecidableEq ι] [Nontrivial ι] in
/-- Fixed joint tail products converge under coordinatewise weak convergence,
because every fixed tail is clopen. -/
theorem quittingJointTailProduct_tendsto
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ who, Tendsto (fun n => lawSeq n who) atTop (nhds (laws who)))
    (horizon : Nat) :
    Tendsto (fun n => quittingJointTailProduct (lawSeq n) horizon) atTop
      (nhds (quittingJointTailProduct laws horizon)) := by
  unfold quittingJointTailProduct compactStoppingLawTailMass
  simpa using tendsto_finsetProd Finset.univ fun who _ =>
    CompactStoppingLaw.tendsto_realMass_of_isClopen (hlaw who)
      (compactStoppingTime_tail_isClopen horizon)

omit [Nontrivial ι] in
/-- Fixed opponent tail products likewise converge coordinatewise. -/
theorem quittingOpponentTailProduct_tendsto
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ who, Tendsto (fun n => lawSeq n who) atTop (nhds (laws who)))
    (owner : ι) (horizon : Nat) :
    Tendsto (fun n => quittingOpponentTailProduct (lawSeq n) owner horizon) atTop
      (nhds (quittingOpponentTailProduct laws owner horizon)) := by
  unfold quittingOpponentTailProduct compactStoppingLawTailMass
  simpa using tendsto_finsetProd (Finset.univ.erase owner) fun who _ =>
    CompactStoppingLaw.tendsto_realMass_of_isClopen (hlaw who)
      (compactStoppingTime_tail_isClopen horizon)

local instance compactStoppingTimeCutoffTopology (horizon : Nat) :
    TopologicalSpace (Option (Fin (horizon + 1))) := ⊥

local instance compactStoppingTimeCutoffDiscreteTopology (horizon : Nat) :
    DiscreteTopology (Option (Fin (horizon + 1))) :=
  discreteTopology_bot _

local instance compactStoppingTimeCutoffMeasurableSpace (horizon : Nat) :
    MeasurableSpace (Option (Fin (horizon + 1))) :=
  borel (Option (Fin (horizon + 1)))

local instance compactStoppingTimeCutoffBorelSpace (horizon : Nat) :
    BorelSpace (Option (Fin (horizon + 1))) :=
  ⟨rfl⟩

/-- Keep a finite stopping time through `horizon`, and send every later time
and Never to one common tail label. -/
def compactStoppingTimeCutoff (horizon : Nat) :
    CompactStoppingTime → Option (Fin (horizon + 1)) :=
  WithTop.recTopCoe none fun time =>
    if htime : time ≤ horizon then
      some <| Fin.mk time (Nat.lt_succ_iff.mpr htime)
    else none

/-- Realize a finite cutoff label as its finite time, with the tail label
realized by Never. -/
def compactStoppingTimeUncut (horizon : Nat) :
    Option (Fin (horizon + 1)) → CompactStoppingTime
  | none => ⊤
  | some time => WithTop.some time.val

/-- Cap a stopping time after `horizon`, replacing every later time by Never. -/
def compactStoppingTimeCap (horizon : Nat) (choice : CompactStoppingTime) :
    CompactStoppingTime :=
  compactStoppingTimeUncut horizon (compactStoppingTimeCutoff horizon choice)

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
@[simp] theorem compactStoppingTimeCutoff_top (horizon : Nat) :
    compactStoppingTimeCutoff horizon ⊤ = none := by
  rw [compactStoppingTimeCutoff, WithTop.recTopCoe_top]

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
@[simp] theorem compactStoppingTimeCutoff_coe_of_le
    (horizon time : Nat) (htime : time ≤ horizon) :
    compactStoppingTimeCutoff horizon (WithTop.some time) =
      some (Fin.mk time (Nat.lt_succ_iff.mpr htime)) := by
  rw [compactStoppingTimeCutoff, WithTop.recTopCoe_coe]
  simp [htime]

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
@[simp] theorem compactStoppingTimeCutoff_coe_of_lt
    (horizon time : Nat) (htime : horizon < time) :
    compactStoppingTimeCutoff horizon (WithTop.some time) = none := by
  rw [compactStoppingTimeCutoff, WithTop.recTopCoe_coe]
  simp [Nat.not_le.mpr htime]

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
@[simp] theorem compactStoppingTimeCap_top (horizon : Nat) :
    compactStoppingTimeCap horizon ⊤ = ⊤ := by
  simp [compactStoppingTimeCap, compactStoppingTimeUncut]

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
@[simp] theorem compactStoppingTimeCap_coe_of_le
    (horizon time : Nat) (htime : time ≤ horizon) :
    compactStoppingTimeCap horizon (WithTop.some time) = WithTop.some time := by
  rw [compactStoppingTimeCap,
    compactStoppingTimeCutoff_coe_of_le horizon time htime]
  rfl

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
@[simp] theorem compactStoppingTimeCap_coe_of_lt
    (horizon time : Nat) (htime : horizon < time) :
    compactStoppingTimeCap horizon (WithTop.some time) = ⊤ := by
  rw [compactStoppingTimeCap,
    compactStoppingTimeCutoff_coe_of_lt horizon time htime]
  rfl

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- The finite cutoff fiber is one finite singleton. -/
theorem compactStoppingTimeCutoff_preimage_some
    (horizon : Nat) (time : Fin (horizon + 1)) :
    compactStoppingTimeCutoff horizon ⁻¹' {some time} =
      ({WithTop.some time.val} : Set CompactStoppingTime) := by
  ext choice
  induction choice using WithTop.recTopCoe with
  | top => simp
  | coe actual =>
      simp only [Set.mem_preimage, Set.mem_singleton_iff, WithTop.coe_eq_coe]
      by_cases hactual : actual ≤ horizon
      · simp only [compactStoppingTimeCutoff_coe_of_le horizon actual hactual,
          Option.some.injEq]
        exact Fin.ext_iff
      · rw [compactStoppingTimeCutoff, WithTop.recTopCoe_coe]
        simp only [hactual, ↓reduceDIte]
        constructor
        · intro himpossible
          cases himpossible
        · intro heq
          subst actual
          exact (hactual (Nat.lt_succ_iff.mp time.isLt)).elim

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- The tail cutoff fiber is exactly the clopen late-or-Never event. -/
theorem compactStoppingTimeCutoff_preimage_none (horizon : Nat) :
    compactStoppingTimeCutoff horizon ⁻¹' {none} =
      {choice : CompactStoppingTime | WithTop.some horizon < choice} := by
  ext choice
  induction choice using WithTop.recTopCoe with
  | top => simp
  | coe time =>
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_setOf_eq, WithTop.coe_lt_coe]
      by_cases htime : time ≤ horizon
      · rw [compactStoppingTimeCutoff, WithTop.recTopCoe_coe]
        simp [htime]
      · rw [compactStoppingTimeCutoff, WithTop.recTopCoe_coe]
        simp [htime, Nat.lt_of_not_ge htime]

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- Every cutoff fiber is clopen. -/
theorem compactStoppingTimeCutoff_preimage_isClopen
    (horizon : Nat) (label : Option (Fin (horizon + 1))) :
    IsClopen (compactStoppingTimeCutoff horizon ⁻¹' {label}) := by
  cases label with
  | none =>
      rw [compactStoppingTimeCutoff_preimage_none]
      exact compactStoppingTime_tail_isClopen horizon
  | some time =>
      rw [compactStoppingTimeCutoff_preimage_some]
      exact compactStoppingTime_finiteSingleton_isClopen time.val

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- The cutoff map is continuous into its finite discrete label space. -/
theorem continuous_compactStoppingTimeCutoff (horizon : Nat) :
    Continuous (compactStoppingTimeCutoff horizon) := by
  rw [continuous_discrete_rng]
  exact fun label =>
    (compactStoppingTimeCutoff_preimage_isClopen horizon label).2

/-- Compact stopping laws pushed to one finite cutoff. -/
def compactStoppingLawCutoff (horizon : Nat) (law : CompactStoppingLaw) :
    PMF (Option (Fin (horizon + 1))) :=
  _root_.Math.ProbabilityMassFunction.pushforward law.toPMF
    (compactStoppingTimeCutoff horizon)

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- Weak convergence of compact stopping laws implies convergence of every
finite cutoff atom. -/
theorem compactStoppingLawCutoff_apply_tendsto
    {lawSeq : Nat → CompactStoppingLaw} {law : CompactStoppingLaw}
    (hlaw : Tendsto lawSeq atTop (nhds law)) (horizon : Nat)
    (choice : Option (Fin (horizon + 1))) :
    Tendsto (fun n => ((compactStoppingLawCutoff horizon (lawSeq n)) choice).toReal)
      atTop (nhds ((compactStoppingLawCutoff horizon law choice).toReal)) := by
  let event : Set CompactStoppingTime :=
    compactStoppingTimeCutoff horizon ⁻¹' {choice}
  have hevent : IsClopen event :=
    compactStoppingTimeCutoff_preimage_isClopen horizon choice
  have hmass (current : CompactStoppingLaw) :
      ((compactStoppingLawCutoff horizon current) choice).toReal =
        current.realMass event := by
    rw [compactStoppingLawCutoff,
      _root_.Math.ProbabilityMassFunction.pushforward_apply_eq_pmfMass]
    exact (current.realMass_eq_pmfMass_toReal hevent.1.measurableSet).symm
  simpa only [hmass] using
    CompactStoppingLaw.tendsto_realMass_of_isClopen hlaw hevent

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- Expectations of arbitrary observables on one finite cutoff converge under
weak convergence of compact stopping laws. -/
theorem compactStoppingLawCutoff_expect_tendsto
    {lawSeq : Nat → CompactStoppingLaw} {law : CompactStoppingLaw}
    (hlaw : Tendsto lawSeq atTop (nhds law)) (horizon : Nat)
    (value : Option (Fin (horizon + 1)) → Real) :
    Tendsto (fun n => expect (compactStoppingLawCutoff horizon (lawSeq n)) value)
      atTop (nhds (expect (compactStoppingLawCutoff horizon law) value)) := by
  exact expect_tendsto_of_forall_toReal_tendsto value
    (compactStoppingLawCutoff_apply_tendsto hlaw horizon)

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- A deterministic clock later than the cutoff, including Never, pushes to
the common tail label. -/
theorem compactStoppingLawCutoff_pure_of_lt
    (horizon : Nat) (choice : CompactStoppingTime)
    (hlate : WithTop.some horizon < choice) :
    compactStoppingLawCutoff horizon
        (CompactStoppingLaw.ofPMF (PMF.pure choice)) = PMF.pure none := by
  unfold compactStoppingLawCutoff
  rw [CompactStoppingLaw.toPMF_ofPMF]
  induction choice using WithTop.recTopCoe with
  | top =>
      rw [_root_.Math.ProbabilityMassFunction.pushforward,
        PMF.pure_map, compactStoppingTimeCutoff_top]
  | coe time =>
      have htime : horizon < time := by
        simpa only [WithTop.coe_lt_coe] using hlate
      rw [_root_.Math.ProbabilityMassFunction.pushforward,
        PMF.pure_map, compactStoppingTimeCutoff_coe_of_lt horizon time htime]

omit [DecidableEq ι] [Nontrivial ι] in
/-- Coordinatewise weak convergence gives pointwise convergence of the finite
product cutoff law. -/
theorem compactStoppingLawCutoff_pmfPi_apply_tendsto
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ who, Tendsto (fun n => lawSeq n who) atTop (nhds (laws who)))
    (horizon : Nat) (choices : ι → Option (Fin (horizon + 1))) :
    Tendsto (fun n =>
        ((Math.PMFProduct.pmfPi
          (fun who => compactStoppingLawCutoff horizon (lawSeq n who)))
          choices).toReal)
      atTop (nhds
        ((Math.PMFProduct.pmfPi
          (fun who => compactStoppingLawCutoff horizon (laws who)))
          choices).toReal) := by
  simp_rw [Math.PMFProduct.pmfPi_apply, ENNReal.toReal_prod]
  simpa using
    tendsto_finsetProd Finset.univ fun who _ =>
      compactStoppingLawCutoff_apply_tendsto (hlaw who) horizon (choices who)

omit [DecidableEq ι] [Nontrivial ι] in
/-- Every observable on the finite product cutoff converges under
coordinatewise weak convergence of the original compact laws. -/
theorem compactStoppingLawCutoff_pmfPi_expect_tendsto
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ who, Tendsto (fun n => lawSeq n who) atTop (nhds (laws who)))
    (horizon : Nat)
    (value : (ι → Option (Fin (horizon + 1))) → Real) :
    Tendsto (fun n => expect
        (Math.PMFProduct.pmfPi
          (fun who => compactStoppingLawCutoff horizon (lawSeq n who))) value)
      atTop (nhds (expect
        (Math.PMFProduct.pmfPi
          (fun who => compactStoppingLawCutoff horizon (laws who))) value)) := by
  exact expect_tendsto_of_forall_toReal_tendsto value
    (compactStoppingLawCutoff_pmfPi_apply_tendsto hlaw horizon)


/-- The literal behavior profile whose players use specified deterministic
finite quitting times or Never. -/
def quittingPureStoppingTimeProfile
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (choices : ι -> CompactStoppingTime) :
    (quittingGame reward).BehaviorProfile :=
  fun who => quittingPureTimeBehaviorStrategy reward who (choices who)

omit [DecidableEq ι] [Nontrivial ι] in
@[simp] theorem quittingProfileLiveRoot_pureStoppingTimeProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (choices : ι → CompactStoppingTime) (time : Nat) :
    quittingProfileLiveRoot reward
        (quittingPureStoppingTimeProfile reward choices) time =
      fun who => quittingPureTimeHazard (choices who) time :=
  rfl

omit [DecidableEq ι] [Nontrivial ι] in
/-- Capping every deterministic stopping time after `horizon` preserves the
entire live-root prefix through that horizon. -/
theorem quittingPureStoppingTimeProfile_cap_root_eq_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (choices : ι → CompactStoppingTime) (horizon time : Nat)
    (htime : time < horizon + 1) :
    quittingProfileLiveRoot reward
        (quittingPureStoppingTimeProfile reward choices) time =
      quittingProfileLiveRoot reward
        (quittingPureStoppingTimeProfile reward
          (fun who => compactStoppingTimeCap horizon (choices who))) time := by
  funext who
  change quittingPureTimeHazard (choices who) time =
    quittingPureTimeHazard (compactStoppingTimeCap horizon (choices who)) time
  induction choices who using WithTop.recTopCoe with
  | top => simp
  | coe quitTime =>
      by_cases hquit : quitTime ≤ horizon
      · rw [compactStoppingTimeCap_coe_of_le horizon quitTime hquit]
      · have hne : time ≠ quitTime := by omega
        rw [compactStoppingTimeCap_coe_of_lt horizon quitTime
          (Nat.lt_of_not_ge hquit)]
        change quittingPureTimeHazard (some quitTime) time =
          quittingPureTimeHazard none time
        rw [quittingPureTimeHazard_some_of_ne hne,
          quittingPureTimeHazard_none]

omit [DecidableEq ι] [Nontrivial ι] in
/-- The capped deterministic profile survives through the cutoff exactly on
the joint late-or-Never event. -/
theorem quittingJointSurvivalWeight_pureStoppingTimeProfile_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (choices : ι → CompactStoppingTime) (horizon : Nat) :
    quittingJointSurvivalWeight
        (quittingProfileLiveRoot reward
          (quittingPureStoppingTimeProfile reward
            (fun who => compactStoppingTimeCap horizon (choices who))))
        0 (horizon + 1) =
      if ∀ who, WithTop.some horizon < choices who then 1 else 0 := by
  classical
  rw [quittingJointSurvivalWeight_eq_prod]
  split_ifs with hlate
  · have hcap : ∀ who, compactStoppingTimeCap horizon (choices who) = ⊤ := by
      intro who
      induction hchoice : choices who using WithTop.recTopCoe with
      | top => simp
      | coe quitTime =>
          rw [compactStoppingTimeCap_coe_of_lt]
          have hwho := hlate who
          rw [hchoice] at hwho
          simpa only [WithTop.coe_lt_coe] using hwho
    simp [quittingStationaryContinueMass_eq_prod_continueProbability, hcap,
      quittingPureTimeHazard]
  · push Not at hlate
    obtain ⟨who, hwho⟩ := hlate
    induction hchoice : choices who using WithTop.recTopCoe with
    | top => simp [hchoice] at hwho
    | coe quitTime =>
        have hquit : quitTime ≤ horizon := by
          rw [hchoice] at hwho
          simpa only [WithTop.coe_le_coe] using hwho
        refine Finset.prod_eq_zero
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hquit)) ?_
        rw [quittingStationaryContinueMass_eq_prod_continueProbability]
        refine Finset.prod_eq_zero (Finset.mem_univ who) ?_
        simp only [Nat.zero_add, quittingProfileLiveRoot_pureStoppingTimeProfile]
        change ((quittingPureTimeHazard
          (compactStoppingTimeCap horizon (choices who)) quitTime) false).toReal = 0
        rw [hchoice]
        rw [compactStoppingTimeCap_coe_of_le horizon quitTime hquit]
        simp [quittingPureTimeHazard]

omit [DecidableEq ι] [Nontrivial ι] in
/-- Replacing every deterministic clock later than `horizon` by Never changes
the terminal payoff only on the joint late-or-Never event. -/
theorem abs_quittingTerminalPayoff_pureStoppingTimeProfile_sub_cap_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (choices : ι → CompactStoppingTime) (observer : ι) (horizon : Nat)
    {bound : Real}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward choices) observer -
        quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward
            (fun who => compactStoppingTimeCap horizon (choices who))) observer| ≤
      2 * bound *
        if ∀ who, WithTop.some horizon < choices who then 1 else 0 := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  have hbound := abs_quittingRootSequenceTerminalValue_sub_le_of_prefix_eq
    reward
      (quittingProfileLiveRoot reward
        (quittingPureStoppingTimeProfile reward choices))
      (quittingProfileLiveRoot reward
        (quittingPureStoppingTimeProfile reward
          (fun who => compactStoppingTimeCap horizon (choices who))))
      observer (horizon + 1) hreward
      (quittingPureStoppingTimeProfile_cap_root_eq_of_lt
        reward choices horizon)
  rw [quittingJointSurvivalWeight_pureStoppingTimeProfile_cap] at hbound
  exact hbound

omit [DecidableEq ι] [Nontrivial ι] in
/-- The expected truncation error under independent complete stopping laws is
bounded by the product of their clopen late-or-Never tail masses. -/
theorem abs_expect_quittingTerminalPayoff_pureStoppingTime_sub_cap_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw) (observer : ι) (horizon : Nat)
    {bound : Real}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |expect (Math.PMFProduct.pmfPi (fun who => (laws who).toPMF))
          (fun choices => quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward choices) observer) -
        expect (Math.PMFProduct.pmfPi (fun who => (laws who).toPMF))
          (fun choices => quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward
              (fun who => compactStoppingTimeCap horizon (choices who))) observer)| ≤
      2 * bound * ∏ who, (laws who).realMass
        {choice | WithTop.some horizon < choice} := by
  classical
  let productLaw := Math.PMFProduct.pmfPi (fun who => (laws who).toPMF)
  let fullValue : (ι → CompactStoppingTime) → Real := fun choices =>
    quittingTerminalPayoff reward
    (quittingPureStoppingTimeProfile reward choices) observer
  let capValue : (ι → CompactStoppingTime) → Real := fun choices =>
    quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward
        (fun who => compactStoppingTimeCap horizon (choices who))) observer
  let lateEvent : Set (ι → CompactStoppingTime) :=
    {choices | ∀ who, WithTop.some horizon < choices who}
  have hfull : ∀ choices, |fullValue choices| ≤ bound := fun choices =>
    abs_quittingTerminalPayoff_le reward _ observer hreward
  have hcap : ∀ choices, |capValue choices| ≤ bound := fun choices =>
    abs_quittingTerminalPayoff_le reward _ observer hreward
  have hlocal : ∀ choices,
      |fullValue choices - capValue choices| ≤
        2 * bound *
          if ∀ who, WithTop.some horizon < choices who then 1 else 0 :=
    fun choices =>
      abs_quittingTerminalPayoff_pureStoppingTimeProfile_sub_cap_le
        reward choices observer horizon hreward
  have hestimate :=
    _root_.Math.ProbabilityMassFunction.abs_expect_sub_le_mul_pmfMass
      productLaw fullValue capValue lateEvent
      (bound := 2 * bound) (observableBound := bound) hfull hcap
      (fun choices => by
        by_cases hlate : ∀ who, WithTop.some horizon < choices who
        · have h := hlocal choices
          rw [if_pos hlate] at h
          have hmem : choices ∈ lateEvent := by simpa [lateEvent] using hlate
          rw [Set.indicator_of_mem hmem]
          exact h
        · have h := hlocal choices
          rw [if_neg hlate] at h
          have hmem : choices ∉ lateEvent := by simpa [lateEvent] using hlate
          rw [Set.indicator_of_notMem hmem]
          exact h)
  have hmass :
      (_root_.Math.ProbabilityMassFunction.pmfMass productLaw
        (fun choices => choices ∈ lateEvent)).toReal =
      ∏ who, (laws who).realMass
        {choice | WithTop.some horizon < choice} := by
    rw [show productLaw =
      Math.PMFProduct.pmfPi (fun who => (laws who).toPMF) by rfl]
    simp only [lateEvent, Set.mem_setOf_eq]
    rw [Math.PMFProduct.pmfMass_pmfPi_forall, ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro who _
    symm
    simpa only [Set.mem_setOf_eq] using
      (laws who).realMass_eq_pmfMass_toReal
        (compactStoppingTime_tail_isClopen horizon).1.measurableSet
  rw [hmass] at hestimate
  simpa [productLaw, fullValue, capValue] using hestimate

/-- Terminal payoff observable on the finite product cutoff.  The tail label
is realized as Never. -/
def quittingCutoffTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (horizon : Nat) (observer : ι)
    (choices : ι → Option (Fin (horizon + 1))) : Real :=
  quittingTerminalPayoff reward
    (quittingPureStoppingTimeProfile reward
      (fun who => compactStoppingTimeUncut horizon (choices who))) observer

omit [DecidableEq ι] [Nontrivial ι] in
/-- The capped deterministic-clock expectation is literally the expectation
of the finite cutoff observable under the product cutoff law. -/
theorem expect_quittingTerminalPayoff_pureStoppingTime_cap_eq_cutoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw) (observer : ι) (horizon : Nat)
    {bound : Real}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    expect (Math.PMFProduct.pmfPi (fun who => (laws who).toPMF))
        (fun choices => quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward
            (fun who => compactStoppingTimeCap horizon (choices who))) observer) =
      expect (Math.PMFProduct.pmfPi
          (fun who => compactStoppingLawCutoff horizon (laws who)))
        (quittingCutoffTerminalValue reward horizon observer) := by
  classical
  let sourceLaw := Math.PMFProduct.pmfPi (fun who => (laws who).toPMF)
  let cutoffMap := fun choices : ι → CompactStoppingTime =>
    fun who => compactStoppingTimeCutoff horizon (choices who)
  let value := quittingCutoffTerminalValue reward horizon observer
  have hvalue : ∀ choices, |value choices| ≤ bound := fun choices =>
    abs_quittingTerminalPayoff_le reward _ observer hreward
  have hpush :
      _root_.Math.ProbabilityMassFunction.pushforward sourceLaw cutoffMap =
        Math.PMFProduct.pmfPi
          (fun who => compactStoppingLawCutoff horizon (laws who)) := by
    simpa [sourceLaw, cutoffMap, compactStoppingLawCutoff] using
      (Math.PMFProduct.pmfPi_push_coordwise
        (fun who => (laws who).toPMF)
        (fun _ => compactStoppingTimeCutoff horizon))
  have hexpect :=
    _root_.Math.ProbabilityMassFunction.expect_pushforward_of_bounded
      sourceLaw cutoffMap value hvalue
  rw [hpush] at hexpect
  symm
  simpa [sourceLaw, cutoffMap, value, quittingCutoffTerminalValue,
    compactStoppingTimeCap] using hexpect

omit [DecidableEq ι] [Nontrivial ι] in
/-- For every fixed cutoff, the capped payoff expectation converges under
coordinatewise weak convergence of compact stopping laws. -/
theorem expect_quittingTerminalPayoff_pureStoppingTime_cap_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ who, Tendsto (fun n => lawSeq n who) atTop (nhds (laws who)))
    (observer : ι) (horizon : Nat) {bound : Real}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    Tendsto (fun n =>
        expect (Math.PMFProduct.pmfPi (fun who => (lawSeq n who).toPMF))
          (fun choices => quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward
              (fun who => compactStoppingTimeCap horizon (choices who))) observer))
      atTop (nhds
        (expect (Math.PMFProduct.pmfPi (fun who => (laws who).toPMF))
          (fun choices => quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward
              (fun who => compactStoppingTimeCap horizon (choices who))) observer))) := by
  have hfinite := compactStoppingLawCutoff_pmfPi_expect_tendsto hlaw horizon
    (quittingCutoffTerminalValue reward horizon observer)
  simpa only [← expect_quittingTerminalPayoff_pureStoppingTime_cap_eq_cutoff
    reward _ observer horizon hreward] using hfinite

omit [DecidableEq ι] [Nontrivial ι] in
/-- Uniform tightness of the joint late event upgrades finite-cutoff
convergence to convergence of the full independent stopping-time payoff. -/
theorem expect_quittingTerminalPayoff_pureStoppingTime_tendsto_of_jointTight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ who, Tendsto (fun n => lawSeq n who) atTop (nhds (laws who)))
    (htight : QuittingJointTightLawSequence lawSeq) (observer : ι) :
    Tendsto (fun n =>
        expect (Math.PMFProduct.pmfPi (fun who => (lawSeq n who).toPMF))
          (fun choices => quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward choices) observer))
      atTop (nhds
        (expect (Math.PMFProduct.pmfPi (fun who => (laws who).toPMF))
          (fun choices => quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward choices) observer))) := by
  obtain ⟨bound, hbound, hreward⟩ := exists_quittingRewardBound reward
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ := ε / (8 * (bound + 1))
  have hden : 0 < 8 * (bound + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨horizon, htail⟩ := htight δ hδ
  have htailConv := quittingJointTailProduct_tendsto hlaw horizon
  have hlimitTail : quittingJointTailProduct laws horizon ≤ δ :=
    le_of_tendsto htailConv (htail.mono fun _ h => le_of_lt h)
  have hcapConv :=
    expect_quittingTerminalPayoff_pureStoppingTime_cap_tendsto
      reward hlaw observer horizon hreward
  obtain ⟨tailStart, htailStart⟩ := (eventually_atTop.1 htail)
  obtain ⟨capStart, hcapStart⟩ :=
    (Metric.tendsto_atTop.mp hcapConv (ε / 2) (half_pos hε))
  refine ⟨max tailStart capStart, ?_⟩
  intro n hn
  have hnTail : tailStart ≤ n := le_trans (le_max_left _ _) hn
  have hnCap : capStart ≤ n := le_trans (le_max_right _ _) hn
  let fullN := expect
    (Math.PMFProduct.pmfPi (fun who => (lawSeq n who).toPMF))
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) observer)
  let capN := expect
    (Math.PMFProduct.pmfPi (fun who => (lawSeq n who).toPMF))
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward
        (fun who => compactStoppingTimeCap horizon (choices who))) observer)
  let fullLimit := expect
    (Math.PMFProduct.pmfPi (fun who => (laws who).toPMF))
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) observer)
  let capLimit := expect
    (Math.PMFProduct.pmfPi (fun who => (laws who).toPMF))
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward
        (fun who => compactStoppingTimeCap horizon (choices who))) observer)
  have htailN : quittingJointTailProduct (lawSeq n) horizon < δ :=
    htailStart n hnTail
  have hfullN : |fullN - capN| ≤
      2 * bound * quittingJointTailProduct (lawSeq n) horizon := by
    simpa [fullN, capN, quittingJointTailProduct,
      compactStoppingLawTailMass] using
      abs_expect_quittingTerminalPayoff_pureStoppingTime_sub_cap_le
        reward (lawSeq n) observer horizon hreward
  have hfullLimit : |fullLimit - capLimit| ≤
      2 * bound * quittingJointTailProduct laws horizon := by
    simpa [fullLimit, capLimit, quittingJointTailProduct,
      compactStoppingLawTailMass] using
      abs_expect_quittingTerminalPayoff_pureStoppingTime_sub_cap_le
        reward laws observer horizon hreward
  have hcap : |capN - capLimit| < ε / 2 := by
    simpa [Real.dist_eq, capN, capLimit] using hcapStart n hnCap
  have hquarter : 2 * bound * δ < ε / 4 := by
    dsimp [δ]
    rw [show 2 * bound * (ε / (8 * (bound + 1))) =
      (ε / 4) * (bound / (bound + 1)) by field_simp; ring]
    have hratio : bound / (bound + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    exact mul_lt_of_lt_one_right (by positivity) hratio
  have hleft : |fullN - capN| < ε / 4 := by
    apply lt_of_le_of_lt hfullN
    apply lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (le_of_lt htailN)
        (mul_nonneg (by norm_num) hbound))
    exact hquarter
  have hright : |capLimit - fullLimit| < ε / 4 := by
    rw [abs_sub_comm]
    exact lt_of_le_of_lt hfullLimit
      (lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hlimitTail
          (mul_nonneg (by norm_num) hbound)) hquarter)
  change dist fullN fullLimit < ε
  rw [Real.dist_eq]
  calc
    |fullN - fullLimit| =
        |(fullN - capN) + (capN - capLimit) + (capLimit - fullLimit)| := by
      congr 1
      ring
    _ ≤ |fullN - capN| + |capN - capLimit| + |capLimit - fullLimit| := by
      exact abs_add_three _ _ _
    _ < ε := by linarith



omit [Nontrivial ι] in
/-- A profile reconstructed from independent complete stopping laws has the
same payoff as the independent expectation over deterministic stopping-time
profiles. -/
theorem quittingTerminalPayoff_compactStoppingLawProfile_eq_expect
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (laws : ι -> CompactStoppingLaw) (observer : ι) :
    quittingTerminalPayoff reward
        (quittingCompactStoppingLawProfile reward laws) observer =
      expect (Math.PMFProduct.pmfPi (fun who => (laws who).toPMF))
        (fun choices =>
          quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward choices) observer) := by
  obtain ⟨bound, -, hreward⟩ := exists_quittingRewardBound reward
  let realize : (who : ι) -> CompactStoppingTime ->
      (quittingGame reward).BehaviorStrategy who :=
    fun who choice => quittingPureTimeBehaviorStrategy reward who choice
  let barycenter : (who : ι) -> PMF CompactStoppingTime ->
      (quittingGame reward).BehaviorStrategy who :=
    fun who law => quittingStoppingLawBehaviorStrategy reward who law
  let observable : (quittingGame reward).BehaviorProfile -> Real :=
    fun profile => quittingTerminalPayoff reward profile observer
  have hbound : forall profile, |observable profile| <= bound := by
    intro profile
    exact abs_quittingTerminalPayoff_le reward profile observer hreward
  have haffine : forall (who : ι)
      (profile : (quittingGame reward).BehaviorProfile),
      observable (Function.update profile who
        (barycenter who ((laws who).toPMF))) =
        expect (laws who).toPMF (fun choice =>
          observable (Function.update profile who (realize who choice))) := by
    intro who profile
    exact quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect
      reward profile who observer (laws who).toPMF
  have hjoint :=
    _root_.GameTheory.Math.Probability.expect_pmfPi_eq_of_separatelyAffine
      realize barycenter observable (fun who => (laws who).toPMF)
      hbound haffine
  change quittingTerminalPayoff reward
      (fun who => quittingStoppingLawBehaviorStrategy reward who
        (laws who).toPMF) observer =
    expect (Math.PMFProduct.pmfPi (fun who => (laws who).toPMF))
      (fun choices => quittingTerminalPayoff reward
        (fun who => quittingPureTimeBehaviorStrategy reward who (choices who))
        observer)
  exact hjoint

/-- Replace one compact stopping law by a deterministic finite time or Never. -/
def quittingPureDeviationCompactLaws
    (laws : ι → CompactStoppingLaw) (who : ι)
    (choice : CompactStoppingTime) : ι → CompactStoppingLaw :=
  fun player => if player = who then
    CompactStoppingLaw.ofPMF (PMF.pure choice)
  else laws player

omit [Nontrivial ι] in
/-- A pure-time deviation against reconstructed opponents is the independent
expectation with that player's latent stopping clock fixed deterministically. -/
theorem quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_eq_expect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw) (who : ι)
    (choice : CompactStoppingTime) (observer : ι) :
    quittingTerminalPayoff reward
        (Function.update (quittingCompactStoppingLawProfile reward laws) who
          (quittingPureTimeBehaviorStrategy reward who choice)) observer =
      expect (Math.PMFProduct.pmfPi
          (fun player =>
            (quittingPureDeviationCompactLaws laws who choice player).toPMF))
        (fun choices => quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward choices) observer) := by
  classical
  obtain ⟨bound, -, hreward⟩ := exists_quittingRewardBound reward
  let samplingLaws := fun player =>
    (quittingPureDeviationCompactLaws laws who choice player).toPMF
  let realize : (player : ι) → CompactStoppingTime →
      (quittingGame reward).BehaviorStrategy player :=
    fun player time => quittingPureTimeBehaviorStrategy reward player time
  let barycenter : (player : ι) → PMF CompactStoppingTime →
      (quittingGame reward).BehaviorStrategy player :=
    fun player law => if player = who then
      quittingPureTimeBehaviorStrategy reward player choice
    else quittingStoppingLawBehaviorStrategy reward player law
  let observable : (quittingGame reward).BehaviorProfile → Real :=
    fun profile => quittingTerminalPayoff reward profile observer
  have hbound : ∀ profile, |observable profile| ≤ bound := fun profile =>
    abs_quittingTerminalPayoff_le reward profile observer hreward
  have haffine : ∀ (player : ι)
      (profile : (quittingGame reward).BehaviorProfile),
      observable (Function.update profile player
        (barycenter player (samplingLaws player))) =
        expect (samplingLaws player) (fun time =>
          observable (Function.update profile player (realize player time))) := by
    intro player profile
    by_cases hplayer : player = who
    · subst player
      simp [barycenter, samplingLaws, quittingPureDeviationCompactLaws,
        observable, realize]
    · simp only [barycenter, hplayer, ↓reduceIte, samplingLaws,
        quittingPureDeviationCompactLaws, realize, observable]
      exact quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect
        reward profile player observer (laws player).toPMF
  have hjoint :=
    _root_.GameTheory.Math.Probability.expect_pmfPi_eq_of_separatelyAffine
      realize barycenter observable samplingLaws hbound haffine
  have hprofile : (fun player => barycenter player (samplingLaws player)) =
      Function.update (quittingCompactStoppingLawProfile reward laws) who
        (quittingPureTimeBehaviorStrategy reward who choice) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [barycenter]
    · simp [barycenter, samplingLaws, quittingPureDeviationCompactLaws,
        quittingCompactStoppingLawProfile, hplayer]
  rw [← hprofile]
  change observable (fun player => barycenter player (samplingLaws player)) =
    expect (Math.PMFProduct.pmfPi samplingLaws)
      (fun samples => observable (fun player => realize player (samples player)))
  exact hjoint

omit [Nontrivial ι] in
/-- Every fixed pure-time deviation payoff converges when that player's
opponent clocks are uniformly tight. -/
theorem quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)))
    (who : ι) (htight : QuittingOpponentTightAtLawSequence lawSeq who)
    (choice : CompactStoppingTime) :
    Tendsto (fun n => quittingTerminalPayoff reward
        (Function.update (quittingCompactStoppingLawProfile reward (lawSeq n)) who
          (quittingPureTimeBehaviorStrategy reward who choice)) who)
      atTop (nhds (quittingTerminalPayoff reward
        (Function.update (quittingCompactStoppingLawProfile reward laws) who
          (quittingPureTimeBehaviorStrategy reward who choice)) who)) := by
  let modifiedSeq := fun n =>
    quittingPureDeviationCompactLaws (lawSeq n) who choice
  let modifiedLaws := quittingPureDeviationCompactLaws laws who choice
  have hmodified : ∀ player,
      Tendsto (fun n => modifiedSeq n player) atTop
        (nhds (modifiedLaws player)) := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [modifiedSeq, modifiedLaws, quittingPureDeviationCompactLaws]
    · simpa [modifiedSeq, modifiedLaws, quittingPureDeviationCompactLaws,
        hplayer] using hlaw player
  have hmodifiedTight : QuittingJointTightLawSequence modifiedSeq := by
    intro ε hε
    obtain ⟨horizon, htail⟩ := htight ε hε
    refine ⟨horizon, htail.mono ?_⟩
    intro n hn
    calc
      quittingJointTailProduct (modifiedSeq n) horizon ≤
          quittingOpponentTailProduct (modifiedSeq n) who horizon :=
        quittingJointTailProduct_le_opponentTailProduct _ who horizon
      _ = quittingOpponentTailProduct (lawSeq n) who horizon := by
        unfold quittingOpponentTailProduct
        apply Finset.prod_congr rfl
        intro player hplayer
        have hne : player ≠ who := Finset.ne_of_mem_erase hplayer
        simp [modifiedSeq, quittingPureDeviationCompactLaws, hne]
      _ < ε := hn
  have hexpect :=
    expect_quittingTerminalPayoff_pureStoppingTime_tendsto_of_jointTight
      reward hmodified hmodifiedTight who
  simpa only [modifiedSeq, modifiedLaws,
    ← quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_eq_expect
      reward _ who choice who] using hexpect

omit [Nontrivial ι] in
/-- Every fixed finite pure-time deviation payoff converges under mere
coordinatewise weak convergence.  The deviator's deterministic finite clock
itself makes the modified joint sequence tight. -/
theorem quittingTerminalPayoff_update_compactStoppingLawProfile_finiteTime_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)))
    (who : ι) (time : Nat) :
    Tendsto (fun n => quittingTerminalPayoff reward
        (Function.update (quittingCompactStoppingLawProfile reward (lawSeq n)) who
          (quittingPureTimeBehaviorStrategy reward who
            (WithTop.some time))) who)
      atTop (nhds (quittingTerminalPayoff reward
        (Function.update (quittingCompactStoppingLawProfile reward laws) who
          (quittingPureTimeBehaviorStrategy reward who
            (WithTop.some time))) who)) := by
  let choice : CompactStoppingTime := WithTop.some time
  let modifiedSeq := fun n =>
    quittingPureDeviationCompactLaws (lawSeq n) who choice
  let modifiedLaws := quittingPureDeviationCompactLaws laws who choice
  have hmodified : ∀ player,
      Tendsto (fun n => modifiedSeq n player) atTop
        (nhds (modifiedLaws player)) := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [modifiedSeq, modifiedLaws, quittingPureDeviationCompactLaws]
    · simpa [modifiedSeq, modifiedLaws, quittingPureDeviationCompactLaws,
        hplayer] using hlaw player
  have hmodifiedTight : QuittingJointTightLawSequence modifiedSeq := by
    intro ε hε
    refine ⟨time, Filter.Eventually.of_forall fun n => ?_⟩
    have hzero : compactStoppingLawTailMass (modifiedSeq n who) time = 0 := by
      rw [show modifiedSeq n who =
          CompactStoppingLaw.ofPMF (PMF.pure (WithTop.some time)) by
        simp [modifiedSeq, choice, quittingPureDeviationCompactLaws]]
      exact compactStoppingLawTailMass_ofPMF_pure_some_self time
    have hproductZero : quittingJointTailProduct (modifiedSeq n) time = 0 := by
      unfold quittingJointTailProduct
      exact Finset.prod_eq_zero (Finset.mem_univ who) hzero
    rw [hproductZero]
    exact hε
  have hexpect :=
    expect_quittingTerminalPayoff_pureStoppingTime_tendsto_of_jointTight
      reward hmodified hmodifiedTight who
  simpa only [choice, modifiedSeq, modifiedLaws,
    ← quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_eq_expect
      reward _ who (WithTop.some time) who] using hexpect

omit [Nontrivial ι] in
/-- Two pure stopping times beyond one horizon have payoff oscillation bounded
by the probability that every opponent clock is still late or Never. -/
theorem abs_quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw) (who : ι) (horizon : Nat)
    (first second : CompactStoppingTime)
    (hfirst : WithTop.some horizon < first)
    (hsecond : WithTop.some horizon < second)
    {bound : Real}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingTerminalPayoff reward
          (Function.update (quittingCompactStoppingLawProfile reward laws) who
            (quittingPureTimeBehaviorStrategy reward who first)) who -
        quittingTerminalPayoff reward
          (Function.update (quittingCompactStoppingLawProfile reward laws) who
            (quittingPureTimeBehaviorStrategy reward who second)) who| ≤
      4 * bound * quittingOpponentTailProduct laws who horizon := by
  classical
  let firstLaws := quittingPureDeviationCompactLaws laws who first
  let secondLaws := quittingPureDeviationCompactLaws laws who second
  let fullValue := fun modifiedLaws : ι → CompactStoppingLaw =>
    expect (Math.PMFProduct.pmfPi (fun player => (modifiedLaws player).toPMF))
      (fun choices => quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) who)
  let capValue := fun modifiedLaws : ι → CompactStoppingLaw =>
    expect (Math.PMFProduct.pmfPi (fun player => (modifiedLaws player).toPMF))
      (fun choices => quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward
          (fun player => compactStoppingTimeCap horizon (choices player))) who)
  have hbound := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hfirstError : |fullValue firstLaws - capValue firstLaws| ≤
      2 * bound * quittingJointTailProduct firstLaws horizon := by
    simpa [fullValue, capValue, quittingJointTailProduct,
      compactStoppingLawTailMass] using
      abs_expect_quittingTerminalPayoff_pureStoppingTime_sub_cap_le
        reward firstLaws who horizon hreward
  have hsecondError : |fullValue secondLaws - capValue secondLaws| ≤
      2 * bound * quittingJointTailProduct secondLaws horizon := by
    simpa [fullValue, capValue, quittingJointTailProduct,
      compactStoppingLawTailMass] using
      abs_expect_quittingTerminalPayoff_pureStoppingTime_sub_cap_le
        reward secondLaws who horizon hreward
  have hopponent (modifiedChoice : CompactStoppingTime) :
      quittingOpponentTailProduct
          (quittingPureDeviationCompactLaws laws who modifiedChoice) who horizon =
        quittingOpponentTailProduct laws who horizon := by
    unfold quittingOpponentTailProduct
    apply Finset.prod_congr rfl
    intro player hplayer
    have hne : player ≠ who := Finset.ne_of_mem_erase hplayer
    simp [quittingPureDeviationCompactLaws, hne]
  have hfirstJoint : quittingJointTailProduct firstLaws horizon ≤
      quittingOpponentTailProduct laws who horizon := by
    calc
      quittingJointTailProduct firstLaws horizon ≤
          quittingOpponentTailProduct firstLaws who horizon :=
        quittingJointTailProduct_le_opponentTailProduct _ who horizon
      _ = quittingOpponentTailProduct laws who horizon := hopponent first
  have hsecondJoint : quittingJointTailProduct secondLaws horizon ≤
      quittingOpponentTailProduct laws who horizon := by
    calc
      quittingJointTailProduct secondLaws horizon ≤
          quittingOpponentTailProduct secondLaws who horizon :=
        quittingJointTailProduct_le_opponentTailProduct _ who horizon
      _ = quittingOpponentTailProduct laws who horizon := hopponent second
  have hfirstError' : |fullValue firstLaws - capValue firstLaws| ≤
      2 * bound * quittingOpponentTailProduct laws who horizon :=
    hfirstError.trans (mul_le_mul_of_nonneg_left hfirstJoint
      (mul_nonneg (by norm_num) hbound))
  have hsecondError' : |fullValue secondLaws - capValue secondLaws| ≤
      2 * bound * quittingOpponentTailProduct laws who horizon :=
    hsecondError.trans (mul_le_mul_of_nonneg_left hsecondJoint
      (mul_nonneg (by norm_num) hbound))
  have hcutoff :
      (fun player => compactStoppingLawCutoff horizon (firstLaws player)) =
        fun player => compactStoppingLawCutoff horizon (secondLaws player) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [firstLaws, secondLaws, quittingPureDeviationCompactLaws,
        compactStoppingLawCutoff_pure_of_lt horizon first hfirst,
        compactStoppingLawCutoff_pure_of_lt horizon second hsecond]
    · simp [firstLaws, secondLaws, quittingPureDeviationCompactLaws, hplayer]
  have hcapEq : capValue firstLaws = capValue secondLaws := by
    calc
      capValue firstLaws = expect
          (Math.PMFProduct.pmfPi
            (fun player => compactStoppingLawCutoff horizon (firstLaws player)))
          (quittingCutoffTerminalValue reward horizon who) := by
        simpa [capValue] using
          expect_quittingTerminalPayoff_pureStoppingTime_cap_eq_cutoff
            reward firstLaws who horizon hreward
      _ = expect
          (Math.PMFProduct.pmfPi
            (fun player => compactStoppingLawCutoff horizon (secondLaws player)))
          (quittingCutoffTerminalValue reward horizon who) := by rw [hcutoff]
      _ = capValue secondLaws := by
        symm
        simpa [capValue] using
          expect_quittingTerminalPayoff_pureStoppingTime_cap_eq_cutoff
            reward secondLaws who horizon hreward
  rw [quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_eq_expect,
    quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_eq_expect]
  change |fullValue firstLaws - fullValue secondLaws| ≤ _
  calc
    |fullValue firstLaws - fullValue secondLaws| =
        |(fullValue firstLaws - capValue firstLaws) +
          (capValue secondLaws - fullValue secondLaws)| := by
      congr 1
      rw [hcapEq]
      ring
    _ ≤ |fullValue firstLaws - capValue firstLaws| +
        |capValue secondLaws - fullValue secondLaws| := abs_add_le _ _
    _ ≤ 4 * bound * quittingOpponentTailProduct laws who horizon := by
      rw [abs_sub_comm (capValue secondLaws)]
      linarith

omit [Nontrivial ι] in
/-- Under opponent tightness, the entire pure-time deviation menu converges
uniformly, including finite times that move with the sequence and Never. -/
theorem eventually_forall_abs_quittingTerminalPayoff_update_pureTime_sub_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)))
    (who : ι)
    (htight : QuittingOpponentTightAtLawSequence lawSeq who) :
    ∀ ε : Real, 0 < ε →
    ∀ᶠ n in atTop, ∀ choice : CompactStoppingTime,
      |quittingTerminalPayoff reward
            (Function.update
              (quittingCompactStoppingLawProfile reward (lawSeq n)) who
              (quittingPureTimeBehaviorStrategy reward who choice)) who -
          quittingTerminalPayoff reward
            (Function.update
              (quittingCompactStoppingLawProfile reward laws) who
              (quittingPureTimeBehaviorStrategy reward who choice)) who| < ε := by
  obtain ⟨bound, hbound, hreward⟩ := exists_quittingRewardBound reward
  intro ε hε
  let δ := ε / (16 * (bound + 1))
  have hden : 0 < 16 * (bound + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨horizon, htail⟩ := htight δ hδ
  have htailConv := quittingOpponentTailProduct_tendsto hlaw who horizon
  have hlimitTail : quittingOpponentTailProduct laws who horizon ≤ δ :=
    le_of_tendsto htailConv (htail.mono fun _ h => le_of_lt h)
  let representative : CompactStoppingTime := WithTop.some (horizon + 1)
  have hrepresentative : WithTop.some horizon < representative := by
    simpa only [representative, WithTop.coe_lt_coe] using Nat.lt_succ_self horizon
  have hearly : ∀ᶠ n in atTop, ∀ time : Fin (horizon + 1),
      |quittingTerminalPayoff reward
            (Function.update
              (quittingCompactStoppingLawProfile reward (lawSeq n)) who
              (quittingPureTimeBehaviorStrategy reward who
                (WithTop.some time.val))) who -
          quittingTerminalPayoff reward
            (Function.update
              (quittingCompactStoppingLawProfile reward laws) who
              (quittingPureTimeBehaviorStrategy reward who
                (WithTop.some time.val))) who| < ε := by
    rw [Filter.eventually_all]
    intro time
    have hfixed :=
      quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_tendsto
        reward hlaw who htight (WithTop.some time.val)
    obtain ⟨start, hstart⟩ := Metric.tendsto_atTop.mp hfixed ε hε
    exact eventually_atTop.2 ⟨start, fun n hn => by
      simpa [Real.dist_eq] using hstart n hn⟩
  have hrepresentativeConv : ∀ᶠ n in atTop,
      |quittingTerminalPayoff reward
            (Function.update
              (quittingCompactStoppingLawProfile reward (lawSeq n)) who
              (quittingPureTimeBehaviorStrategy reward who representative)) who -
          quittingTerminalPayoff reward
            (Function.update
              (quittingCompactStoppingLawProfile reward laws) who
              (quittingPureTimeBehaviorStrategy reward who representative)) who| <
        ε / 2 := by
    have hfixed :=
      quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_tendsto
        reward hlaw who htight representative
    obtain ⟨start, hstart⟩ :=
      Metric.tendsto_atTop.mp hfixed (ε / 2) (half_pos hε)
    exact eventually_atTop.2 ⟨start, fun n hn => by
      simpa [Real.dist_eq] using hstart n hn⟩
  have hquarter : 4 * bound * δ < ε / 4 := by
    dsimp [δ]
    rw [show 4 * bound * (ε / (16 * (bound + 1))) =
      (ε / 4) * (bound / (bound + 1)) by field_simp; ring]
    have hratio : bound / (bound + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    exact mul_lt_of_lt_one_right (by positivity) hratio
  filter_upwards [htail, hearly, hrepresentativeConv] with
      n htailN hearlyN hrepresentativeN
  intro choice
  let current := fun time : CompactStoppingTime =>
    quittingTerminalPayoff reward
      (Function.update
        (quittingCompactStoppingLawProfile reward (lawSeq n)) who
        (quittingPureTimeBehaviorStrategy reward who time)) who
  let limit := fun time : CompactStoppingTime =>
    quittingTerminalPayoff reward
      (Function.update
        (quittingCompactStoppingLawProfile reward laws) who
        (quittingPureTimeBehaviorStrategy reward who time)) who
  change |current choice - limit choice| < ε
  by_cases hchoice : WithTop.some horizon < choice
  · have hnOscillation : |current choice - current representative| ≤
        4 * bound * quittingOpponentTailProduct (lawSeq n) who horizon := by
      simpa [current] using
        abs_quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_sub_le
          reward (lawSeq n) who horizon choice representative hchoice
            hrepresentative hreward
    have hlimitOscillation : |limit choice - limit representative| ≤
        4 * bound * quittingOpponentTailProduct laws who horizon := by
      simpa [limit] using
        abs_quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_sub_le
          reward laws who horizon choice representative hchoice
            hrepresentative hreward
    have hnQuarter : |current choice - current representative| < ε / 4 :=
      lt_of_le_of_lt hnOscillation
        (lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left (le_of_lt htailN)
            (mul_nonneg (by norm_num) hbound)) hquarter)
    have hlimitQuarter : |limit representative - limit choice| < ε / 4 := by
      rw [abs_sub_comm]
      exact lt_of_le_of_lt hlimitOscillation
        (lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left hlimitTail
            (mul_nonneg (by norm_num) hbound)) hquarter)
    have hrepresentativeHalf :
        |current representative - limit representative| < ε / 2 := by
      simpa [current, limit] using hrepresentativeN
    calc
      |current choice - limit choice| =
          |(current choice - current representative) +
            (current representative - limit representative) +
            (limit representative - limit choice)| := by
        congr 1
        ring
      _ ≤ |current choice - current representative| +
          |current representative - limit representative| +
          |limit representative - limit choice| := abs_add_three _ _ _
      _ < ε := by linarith
  · induction choice using WithTop.recTopCoe with
    | top => exact (hchoice (by simp)).elim
    | coe time =>
        have htime : time ≤ horizon := by
          simpa only [WithTop.coe_lt_coe, not_lt] using hchoice
        simpa [current, limit] using
          hearlyN ⟨time, Nat.lt_succ_iff.mpr htime⟩

omit [Nontrivial ι] in
/-- Opponent tightness makes the exact unrestricted behavioral deviation cap
continuous.  The proof transfers the uniform pure-time menu estimate through
the exact pure-time extremality theorem. -/
theorem quittingContinuationBestResponseValue_compactStoppingLawProfile_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)))
    (who : ι)
    (htight : QuittingOpponentTightAtLawSequence lawSeq who) :
    Tendsto (fun n => quittingContinuationBestResponseValue reward
        (quittingCompactStoppingLawProfile reward (lawSeq n)) who)
      atTop (nhds (quittingContinuationBestResponseValue reward
        (quittingCompactStoppingLawProfile reward laws) who)) := by
  obtain ⟨bound, -, hreward⟩ := exists_quittingRewardBound reward
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huniform :=
    eventually_forall_abs_quittingTerminalPayoff_update_pureTime_sub_lt
      reward hlaw who htight (ε / 2) (half_pos hε)
  obtain ⟨start, hstart⟩ := eventually_atTop.1 huniform
  refine ⟨start, ?_⟩
  intro n hn
  let current := fun choice : CompactStoppingTime =>
    quittingTerminalPayoff reward
      (Function.update
        (quittingCompactStoppingLawProfile reward (lawSeq n)) who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  let limit := fun choice : CompactStoppingTime =>
    quittingTerminalPayoff reward
      (Function.update
        (quittingCompactStoppingLawProfile reward laws) who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  have huniformN : ∀ choice, |current choice - limit choice| < ε / 2 := by
    simpa [current, limit] using hstart n hn
  have hcurrentBdd : BddAbove (Set.range current) := by
    refine ⟨bound, ?_⟩
    rintro value ⟨choice, rfl⟩
    exact le_trans (le_abs_self _) (abs_quittingTerminalPayoff_le
      reward _ who hreward)
  have hlimitBdd : BddAbove (Set.range limit) := by
    refine ⟨bound, ?_⟩
    rintro value ⟨choice, rfl⟩
    exact le_trans (le_abs_self _) (abs_quittingTerminalPayoff_le
      reward _ who hreward)
  have hcurrentNonempty : (Set.range current).Nonempty :=
    ⟨current ⊤, ⟨⊤, rfl⟩⟩
  have hlimitNonempty : (Set.range limit).Nonempty :=
    ⟨limit ⊤, ⟨⊤, rfl⟩⟩
  have hcurrentLe : sSup (Set.range current) ≤
      sSup (Set.range limit) + ε / 2 := by
    apply csSup_le hcurrentNonempty
    rintro value ⟨choice, rfl⟩
    have hpoint := (abs_lt.mp (huniformN choice)).2
    have hsup := le_csSup hlimitBdd ⟨choice, rfl⟩
    linarith
  have hlimitLe : sSup (Set.range limit) ≤
      sSup (Set.range current) + ε / 2 := by
    apply csSup_le hlimitNonempty
    rintro value ⟨choice, rfl⟩
    have hpoint := (abs_lt.mp (huniformN choice)).1
    have hsup := le_csSup hcurrentBdd ⟨choice, rfl⟩
    linarith
  have hcurrentSup :
      quittingContinuationBestResponseValue reward
          (quittingCompactStoppingLawProfile reward (lawSeq n)) who =
        sSup (Set.range current) := by
    unfold quittingContinuationBestResponseValue
    change _ = sSup (Set.range fun choice : Option Nat =>
      quittingTerminalPayoff reward
        (Function.update
          (quittingCompactStoppingLawProfile reward (lawSeq n)) who
          (quittingPureTimeBehaviorStrategy reward who choice)) who)
    exact sSup_range_quittingTerminalPayoff_update_eq_pureTime reward
      (quittingCompactStoppingLawProfile reward (lawSeq n)) who
  have hlimitSup :
      quittingContinuationBestResponseValue reward
          (quittingCompactStoppingLawProfile reward laws) who =
        sSup (Set.range limit) := by
    unfold quittingContinuationBestResponseValue
    change _ = sSup (Set.range fun choice : Option Nat =>
      quittingTerminalPayoff reward
        (Function.update
          (quittingCompactStoppingLawProfile reward laws) who
          (quittingPureTimeBehaviorStrategy reward who choice)) who)
    exact sSup_range_quittingTerminalPayoff_update_eq_pureTime reward
      (quittingCompactStoppingLawProfile reward laws) who
  rw [hcurrentSup, hlimitSup, Real.dist_eq]
  rw [abs_lt]
  constructor <;> linarith

omit [Nontrivial ι] in
/-- Joint tightness gives convergence of the prescribed payoff of the
canonical reconstructed profiles. -/
theorem quittingTerminalPayoff_compactStoppingLawProfile_tendsto_of_jointTight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)))
    (htight : QuittingJointTightLawSequence lawSeq)
    (observer : ι) :
    Tendsto (fun n => quittingTerminalPayoff reward
        (quittingCompactStoppingLawProfile reward (lawSeq n)) observer)
      atTop (nhds (quittingTerminalPayoff reward
        (quittingCompactStoppingLawProfile reward laws) observer)) := by
  have hexpect :=
    expect_quittingTerminalPayoff_pureStoppingTime_tendsto_of_jointTight
      reward hlaw htight observer
  simpa only [← quittingTerminalPayoff_compactStoppingLawProfile_eq_expect]
    using hexpect

/-- Opponent tightness gives convergence of the prescribed payoff of the
canonical reconstructed profiles. -/
theorem quittingTerminalPayoff_compactStoppingLawProfile_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)))
    (htight : QuittingOpponentTightLawSequence lawSeq)
    (observer : ι) :
    Tendsto (fun n => quittingTerminalPayoff reward
        (quittingCompactStoppingLawProfile reward (lawSeq n)) observer)
      atTop (nhds (quittingTerminalPayoff reward
        (quittingCompactStoppingLawProfile reward laws) observer)) :=
  quittingTerminalPayoff_compactStoppingLawProfile_tendsto_of_jointTight
    reward hlaw htight.joint observer

/-- The full prescribed/unrestricted-cap terminal semantic pair is continuous
along every opponent-tight, coordinatewise weakly convergent selected
sequence of compact stopping-law profiles. -/
theorem quittingTerminalSemanticPair_compactStoppingLawProfile_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)))
    (htight : QuittingOpponentTightLawSequence lawSeq) :
    Tendsto (fun n => quittingTerminalSemanticPair reward
        (quittingCompactStoppingLawProfile reward (lawSeq n)))
      atTop (nhds (quittingTerminalSemanticPair reward
        (quittingCompactStoppingLawProfile reward laws))) := by
  apply Filter.Tendsto.prodMk_nhds
  · rw [tendsto_pi_nhds]
    exact fun observer =>
      quittingTerminalPayoff_compactStoppingLawProfile_tendsto
        reward hlaw htight observer
  · rw [tendsto_pi_nhds]
    exact fun who =>
      quittingContinuationBestResponseValue_compactStoppingLawProfile_tendsto
        reward hlaw who (htight who)

omit [DecidableEq ι] [Nontrivial ι] in
/-- Every source profile sequence has one subsequence on which all actual
live-spine stopping laws converge simultaneously in the compact
`WithTop Nat` weak-law space. -/
theorem exists_quittingCompactStoppingLawsOfProfile_tendsto_subseq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : Nat → (quittingGame reward).BehaviorProfile) :
    ∃ (laws : ι → CompactStoppingLaw) (subseq : Nat → Nat),
      StrictMono subseq ∧
      ∀ player, Tendsto (fun n =>
        quittingCompactStoppingLawsOfProfile reward (profiles (subseq n)) player)
        atTop (nhds (laws player)) := by
  obtain ⟨laws, subseq, hsubseq, hlaws⟩ :=
    CompactSpace.tendsto_subseq
      (fun n => quittingCompactStoppingLawsOfProfile reward (profiles n))
  refine ⟨laws, subseq, hsubseq, ?_⟩
  intro player
  have hcoordinate := tendsto_pi_nhds.mp hlaws player
  simpa [Function.comp_def] using hcoordinate

/-- An actual profile sequence realizing one terminal-semantic carrier point,
together with a strict subsequence on which every complete stopping law has a
coordinatewise weak limit.  No tightness or semantic realization by the law
limit is included. -/
structure QuittingTerminalSemanticSelectedLawLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : QuittingTerminalSemanticPair ι) where
  sourceProfile : Nat → (quittingGame reward).BehaviorProfile
  subseq : Nat → Nat
  subseq_strictMono : StrictMono subseq
  laws : ι → CompactStoppingLaw
  semantic_tendsto : Tendsto
    (fun n => quittingTerminalSemanticPair reward (sourceProfile (subseq n)))
    atTop (nhds target)
  law_tendsto : ∀ player, Tendsto
    (fun n => quittingCompactStoppingLawsOfProfile reward
      (sourceProfile (subseq n)) player)
    atTop (nhds (laws player))

omit [Nontrivial ι] in
/-- Every point of the terminal-semantic carrier has an actual realizing
profile sequence and a strict subsequence with simultaneous coordinatewise
compact stopping-law limits. -/
theorem nonempty_terminalSemanticSelectedLawLimit_of_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : QuittingTerminalSemanticPair ι)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward) :
    Nonempty (QuittingTerminalSemanticSelectedLawLimit reward target) := by
  obtain ⟨sourceProfile, hsemantic⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward target htarget
  obtain ⟨laws, subseq, hsubseq, hlaws⟩ :=
    exists_quittingCompactStoppingLawsOfProfile_tendsto_subseq
      reward sourceProfile
  refine ⟨{
    sourceProfile := sourceProfile
    subseq := subseq
    subseq_strictMono := hsubseq
    laws := laws
    semantic_tendsto := hsemantic.comp hsubseq.tendsto_atTop
    law_tendsto := hlaws }⟩

/-- **Opponent-tight full semantic realization.**  If one selected source
profile sequence converges semantically, its actual compact stopping laws
converge coordinatewise, and those selected laws are opponent-tight, then the
canonical hazard reconstruction of the weak limits realizes that exact
semantic limit. -/
theorem quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : Nat → (quittingGame reward).BehaviorProfile)
    (target : QuittingTerminalSemanticPair ι)
    (laws : ι → CompactStoppingLaw)
    (hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds target))
    (hlaw : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward (profiles n) player)
      atTop (nhds (laws player)))
    (htight : QuittingOpponentTightLawSequence
      (fun n => quittingCompactStoppingLawsOfProfile reward (profiles n))) :
    quittingTerminalSemanticPair reward
        (quittingCompactStoppingLawProfile reward laws) = target := by
  let lawSeq := fun n => quittingCompactStoppingLawsOfProfile reward (profiles n)
  have hcanonicalTarget : Tendsto (fun n => quittingTerminalSemanticPair reward
      (quittingCompactStoppingLawProfile reward (lawSeq n)))
      atTop (nhds target) := by
    apply hsemantic.congr'
    exact Filter.Eventually.of_forall fun n =>
      quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile
        reward (profiles n)
  have hcanonicalLimit :=
    quittingTerminalSemanticPair_compactStoppingLawProfile_tendsto
      reward hlaw htight
  exact tendsto_nhds_unique hcanonicalLimit hcanonicalTarget

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- A compact stopping law is proper when it puts no mass on Never. -/
def compactStoppingLawIsProper (law : CompactStoppingLaw) : Prop :=
  law.realMass ({⊤} : Set CompactStoppingTime) = 0

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- A proper compact stopping law has vanishing late-or-Never tails. -/
theorem tendsto_compactStoppingLawTailMass_zero_of_isProper
    {law : CompactStoppingLaw} (hproper : compactStoppingLawIsProper law) :
    Tendsto (compactStoppingLawTailMass law) atTop (nhds 0) := by
  rw [compactStoppingLawIsProper] at hproper
  unfold compactStoppingLawTailMass
  simpa only [hproper] using
    CompactStoppingLaw.tendsto_tail_realMass_top law

omit [Nontrivial ι] in
/-- An opponent-tail product is bounded by the tail mass of any one of the
displayed owner's opponents. -/
theorem quittingOpponentTailProduct_le_tailMass_of_ne
    (laws : ι → CompactStoppingLaw) (owner opponent : ι)
    (hne : opponent ≠ owner) (horizon : Nat) :
    quittingOpponentTailProduct laws owner horizon ≤
      compactStoppingLawTailMass (laws opponent) horizon := by
  let factor := fun player => compactStoppingLawTailMass (laws player) horizon
  have hopponent : opponent ∈ Finset.univ.erase owner := by simp [hne]
  have hsplit := Finset.mul_prod_erase
    (Finset.univ.erase owner) factor hopponent
  have hrest : ∏ player ∈ (Finset.univ.erase owner).erase opponent,
      factor player ≤ 1 := by
    exact Finset.prod_le_one
      (fun player _ => CompactStoppingLaw.realMass_nonneg (laws player) _)
      (fun player _ => CompactStoppingLaw.realMass_le_one (laws player) _)
  have hfactor : 0 ≤ factor opponent :=
    CompactStoppingLaw.realMass_nonneg (laws opponent) _
  calc
    quittingOpponentTailProduct laws owner horizon =
        factor opponent *
          ∏ player ∈ (Finset.univ.erase owner).erase opponent,
            factor player := by
      simpa [quittingOpponentTailProduct, factor] using hsplit.symm
    _ ≤ factor opponent * 1 := mul_le_mul_of_nonneg_left hrest hfactor
    _ = compactStoppingLawTailMass (laws opponent) horizon := by
      simp [factor]

omit [Nontrivial ι] in
/-- A proper weak-limit clock makes the opponents of every different owner
tight along the selected coordinatewise convergent sequence. -/
theorem QuittingOpponentTightAtLawSequence.of_properOpponentLimit
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)))
    (owner opponent : ι) (hne : opponent ≠ owner)
    (hproper : compactStoppingLawIsProper (laws opponent)) :
    QuittingOpponentTightAtLawSequence lawSeq owner := by
  intro ε hε
  have htailZero :=
    tendsto_compactStoppingLawTailMass_zero_of_isProper hproper
  obtain ⟨horizon, hlimitTail⟩ :=
    (Metric.tendsto_atTop.1 htailZero) (ε / 2) (by positivity)
  have hlimitTail' :
      compactStoppingLawTailMass (laws opponent) horizon < ε / 2 := by
    have hlimitTailAt := hlimitTail horizon le_rfl
    rw [Real.dist_0_eq_abs] at hlimitTailAt
    exact lt_of_le_of_lt (le_abs_self _) hlimitTailAt
  have htailConverges : Tendsto
      (fun n => compactStoppingLawTailMass (lawSeq n opponent) horizon)
      atTop (nhds (compactStoppingLawTailMass (laws opponent) horizon)) := by
    exact CompactStoppingLaw.tendsto_realMass_of_isClopen (hlaw opponent)
      (compactStoppingTime_tail_isClopen horizon)
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.1 htailConverges) (ε / 2) (by positivity)
  refine ⟨horizon, Filter.eventually_atTop.2 ⟨threshold, fun n hn => ?_⟩⟩
  have hdist := hthreshold n hn
  rw [Real.dist_eq, abs_sub_lt_iff] at hdist
  apply lt_of_le_of_lt
    (quittingOpponentTailProduct_le_tailMass_of_ne
      (lawSeq n) owner opponent hne horizon)
  linarith

/-- One proper limiting clock makes the selected product sequence jointly
tight, hence suffices for prescribed-payoff convergence. -/
theorem QuittingJointTightLawSequence.of_properLimit
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)))
    (properPlayer : ι)
    (hproper : compactStoppingLawIsProper (laws properPlayer)) :
    QuittingJointTightLawSequence lawSeq := by
  obtain ⟨owner, howner⟩ := exists_ne properPlayer
  have htight := QuittingOpponentTightAtLawSequence.of_properOpponentLimit
    hlaw owner properPlayer howner.symm hproper
  intro ε hε
  obtain ⟨horizon, htail⟩ := htight ε hε
  refine ⟨horizon, htail.mono ?_⟩
  intro n hn
  exact lt_of_le_of_lt
    (quittingJointTailProduct_le_opponentTailProduct (lawSeq n) owner horizon) hn

/-- With one proper limiting clock, the reconstructed profile has the exact
limiting prescribed payoff, and every other player's unrestricted cap is
also exact.  No continuity assertion is made for the proper player's own cap. -/
theorem quittingTerminalSemanticPair_partial_eq_of_proper_lawLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : Nat → (quittingGame reward).BehaviorProfile)
    (target : QuittingTerminalSemanticPair ι)
    (laws : ι → CompactStoppingLaw)
    (hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds target))
    (hlaw : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward (profiles n) player)
      atTop (nhds (laws player)))
    (properPlayer : ι)
    (hproper : compactStoppingLawIsProper (laws properPlayer)) :
    (quittingTerminalSemanticPair reward
        (quittingCompactStoppingLawProfile reward laws)).1 = target.1 ∧
      ∀ owner ≠ properPlayer,
        (quittingTerminalSemanticPair reward
          (quittingCompactStoppingLawProfile reward laws)).2 owner =
            target.2 owner := by
  let lawSeq := fun n =>
    quittingCompactStoppingLawsOfProfile reward (profiles n)
  have hlaw' : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)) := by
    simpa [lawSeq] using hlaw
  have hcanonicalTarget : Tendsto (fun n => quittingTerminalSemanticPair reward
      (quittingCompactStoppingLawProfile reward (lawSeq n)))
      atTop (nhds target) := by
    apply hsemantic.congr'
    exact Filter.Eventually.of_forall fun n =>
      quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile
        reward (profiles n)
  constructor
  · funext observer
    have hlimit :=
      quittingTerminalPayoff_compactStoppingLawProfile_tendsto_of_jointTight
        reward hlaw'
          (QuittingJointTightLawSequence.of_properLimit
            hlaw' properPlayer hproper) observer
    have htarget :=
      (((continuous_apply observer).comp continuous_fst).tendsto target).comp
        hcanonicalTarget
    exact tendsto_nhds_unique hlimit htarget
  · intro owner howner
    have htight :=
      QuittingOpponentTightAtLawSequence.of_properOpponentLimit
        hlaw' owner properPlayer howner.symm hproper
    have hlimit :=
      quittingContinuationBestResponseValue_compactStoppingLawProfile_tendsto
        reward hlaw' owner htight
    have htarget :=
      (((continuous_apply owner).comp continuous_snd).tendsto target).comp
        hcanonicalTarget
    exact tendsto_nhds_unique hlimit htarget

omit [Nontrivial ι] in
/-- Every fixed finite pure-time deviation at the weak law limit is bounded
by the corresponding limiting cap coordinate of the actual source semantic
sequence.  No opponent tightness or properness is needed. -/
theorem quittingTerminalPayoff_update_finiteTime_le_of_lawLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : Nat → (quittingGame reward).BehaviorProfile)
    (target : QuittingTerminalSemanticPair ι)
    (laws : ι → CompactStoppingLaw)
    (hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds target))
    (hlaw : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward (profiles n) player)
      atTop (nhds (laws player)))
    (who : ι) (time : Nat) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingCompactStoppingLawProfile reward laws) who
          (quittingPureTimeBehaviorStrategy reward who
            (WithTop.some time))) who ≤ target.2 who := by
  let lawSeq := fun n =>
    quittingCompactStoppingLawsOfProfile reward (profiles n)
  have hlaw' : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)) := by
    simpa [lawSeq] using hlaw
  have hcanonicalTarget : Tendsto (fun n => quittingTerminalSemanticPair reward
      (quittingCompactStoppingLawProfile reward (lawSeq n)))
      atTop (nhds target) := by
    apply hsemantic.congr'
    exact Filter.Eventually.of_forall fun n =>
      quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile
        reward (profiles n)
  have hfinite :=
    quittingTerminalPayoff_update_compactStoppingLawProfile_finiteTime_tendsto
      reward hlaw' who time
  have hcap :=
    (((continuous_apply who).comp continuous_snd).tendsto target).comp
      hcanonicalTarget
  apply le_of_tendsto_of_tendsto hfinite hcap
  exact Filter.Eventually.of_forall fun n =>
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (quittingCompactStoppingLawProfile reward (lawSeq n)) who _

omit [Nontrivial ι] in
/-- If two semantic pairs have the same prescribed vector and all cap
coordinates except possibly one, their total-debt difference is exactly that
one cap difference. -/
theorem quittingTerminalSemanticDebtSum_eq_add_capGap
    (pair target : QuittingTerminalSemanticPair ι) (owner : ι)
    (hprescribed : pair.1 = target.1)
    (hcaps : ∀ player ≠ owner, pair.2 player = target.2 player) :
    quittingTerminalSemanticDebtSum pair =
      quittingTerminalSemanticDebtSum target +
        (pair.2 owner - target.2 owner) := by
  unfold quittingTerminalSemanticDebtSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ owner),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ owner)]
  have herase : ∑ player ∈ Finset.univ.erase owner,
      quittingTerminalSemanticDebt pair player =
        ∑ player ∈ Finset.univ.erase owner,
          quittingTerminalSemanticDebt target player := by
    apply Finset.sum_congr rfl
    intro player hplayer
    unfold quittingTerminalSemanticDebt
    rw [hcaps player (Finset.ne_of_mem_erase hplayer), hprescribed]
  rw [herase]
  unfold quittingTerminalSemanticDebt
  rw [hprescribed]
  ring

/-- At a global minimum of total semantic debt, a proper limiting clock's
possibly discontinuous reconstructed cap can only jump upward. -/
theorem target_cap_le_of_proper_minimum_lawLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : Nat → (quittingGame reward).BehaviorProfile)
    (target : QuittingTerminalSemanticPair ι)
    (laws : ι → CompactStoppingLaw)
    (hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds target))
    (hlaw : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward (profiles n) player)
      atTop (nhds (laws player)))
    (properPlayer : ι)
    (hproper : compactStoppingLawIsProper (laws properPlayer))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum target ≤
        quittingTerminalSemanticDebtSum candidate) :
    target.2 properPlayer ≤
      quittingContinuationBestResponseValue reward
        (quittingCompactStoppingLawProfile reward laws) properPlayer := by
  let limitProfile := quittingCompactStoppingLawProfile reward laws
  let limitPair := quittingTerminalSemanticPair reward limitProfile
  obtain ⟨hprescribed, hcaps⟩ :=
    quittingTerminalSemanticPair_partial_eq_of_proper_lawLimit
      reward profiles target laws hsemantic hlaw properPlayer hproper
  have hdebtIdentity : quittingTerminalSemanticDebtSum limitPair =
      quittingTerminalSemanticDebtSum target +
        (limitPair.2 properPlayer - target.2 properPlayer) := by
    exact quittingTerminalSemanticDebtSum_eq_add_capGap
      limitPair target properPlayer hprescribed hcaps
  have hlimitMem : limitPair ∈ quittingTerminalSemanticCarrier reward := by
    apply subset_closure
    exact ⟨limitProfile, rfl⟩
  have hmin := hminimum limitPair hlimitMem
  rw [hdebtIdentity] at hmin
  change target.2 properPlayer ≤ limitPair.2 properPlayer
  linarith

/-- Nonattainment makes the one potentially discontinuous cap jump strictly
above its limiting source coordinate. -/
theorem target_cap_lt_of_proper_minimum_notAttained_lawLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : Nat → (quittingGame reward).BehaviorProfile)
    (target : QuittingTerminalSemanticPair ι)
    (laws : ι → CompactStoppingLaw)
    (hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds target))
    (hlaw : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward (profiles n) player)
      atTop (nhds (laws player)))
    (properPlayer : ι)
    (hproper : compactStoppingLawIsProper (laws properPlayer))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum target ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnotAttained : ∀ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticPair reward profile ≠ target) :
    target.2 properPlayer <
      quittingContinuationBestResponseValue reward
        (quittingCompactStoppingLawProfile reward laws) properPlayer := by
  have hle := target_cap_le_of_proper_minimum_lawLimit
    reward profiles target laws hsemantic hlaw properPlayer hproper hminimum
  apply lt_of_le_of_ne hle
  intro heq
  apply hnotAttained (quittingCompactStoppingLawProfile reward laws)
  obtain ⟨hprescribed, hcaps⟩ :=
    quittingTerminalSemanticPair_partial_eq_of_proper_lawLimit
      reward profiles target laws hsemantic hlaw properPlayer hproper
  apply Prod.ext
  · exact hprescribed
  · funext player
    by_cases hplayer : player = properPlayer
    · subst player
      exact heq.symm
    · exact hcaps player hplayer

omit [Nontrivial ι] in
/-- If every finite pure-time reply lies below a strict lower bound for the
unrestricted cap, then Never attains that cap exactly. -/
theorem quittingContinuationBestResponseValue_eq_never_of_finite_le_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (bound : Real)
    (hfinite : ∀ time : Nat,
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who
            (WithTop.some time))) who ≤ bound)
    (hstrict : bound <
      quittingContinuationBestResponseValue reward profile who) :
    quittingContinuationBestResponseValue reward profile who =
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who none)) who := by
  let menu := fun choice : CompactStoppingTime =>
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  have hcapSup : quittingContinuationBestResponseValue reward profile who =
      sSup (Set.range menu) := by
    unfold quittingContinuationBestResponseValue
    change _ = sSup (Set.range fun choice : Option Nat =>
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who choice)) who)
    exact sSup_range_quittingTerminalPayoff_update_eq_pureTime
      reward profile who
  have hrangeNonempty : (Set.range menu).Nonempty := ⟨menu ⊤, ⟨⊤, rfl⟩⟩
  have hneverLe : menu ⊤ ≤
      quittingContinuationBestResponseValue reward profile who :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile who _
  have hboundLtNever : bound < menu ⊤ := by
    by_contra hnot
    have hneverBound : menu ⊤ ≤ bound := le_of_not_gt hnot
    have hcapBound : quittingContinuationBestResponseValue reward profile who ≤
        bound := by
      rw [hcapSup]
      apply csSup_le hrangeNonempty
      rintro value ⟨choice, rfl⟩
      induction choice using WithTop.recTopCoe with
      | top => exact hneverBound
      | coe time => exact hfinite time
    exact (not_lt_of_ge hcapBound) hstrict
  apply le_antisymm
  · rw [hcapSup]
    apply csSup_le hrangeNonempty
    rintro value ⟨choice, rfl⟩
    induction choice using WithTop.recTopCoe with
    | top => exact le_rfl
    | coe time => exact (hfinite time).trans (le_of_lt hboundLtNever)
  · exact hneverLe

omit [DecidableEq ι] [Nontrivial ι] in
/-- The live hazard of the canonical compact-law profile is literally the
Booleanized scalar hazard reconstructed from that player's PMF. -/
theorem quittingCompactStoppingLawProfile_liveHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw) (player : ι) :
    (fun time => quittingProfileLiveRoot reward
      (quittingCompactStoppingLawProfile reward laws) time player) =
      (StoppingLaw.toScalarHazard (laws player).toPMF).toBoolean := by
  rfl

omit [DecidableEq ι] [Nontrivial ι] in
/-- Each reconstructed marginal survival converges to that compact law's
singleton Never mass. -/
theorem quittingCompactStoppingLawProfile_hazardSurvival_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw) (player : ι) :
    Tendsto (fun time => quittingHazardSurvival
        (fun stage => quittingProfileLiveRoot reward
          (quittingCompactStoppingLawProfile reward laws) stage player) time)
      atTop (nhds ((laws player).realMass
        ({⊤} : Set CompactStoppingTime))) := by
  let hazard := (StoppingLaw.toScalarHazard (laws player).toPMF).toBoolean
  have hsurvival := tendsto_quittingHazardSurvival_neverMass hazard
  have hnever : quittingHazardNeverMass hazard =
      (laws player).realMass ({⊤} : Set CompactStoppingTime) := by
    rw [← quittingHazardStoppingLaw_none_toReal]
    have hstopping : quittingHazardStoppingLaw hazard = (laws player).toPMF := by
      unfold hazard quittingHazardStoppingLaw
      rw [ScalarHazard.toScalar_toBoolean,
        StoppingLaw.stoppingLaw_toScalarHazard]
    rw [hstopping]
    exact CompactStoppingLaw.toPMF_apply_toReal (laws player) ⊤
  rw [hnever] at hsurvival
  simpa only [hazard, quittingCompactStoppingLawProfile_liveHazard]
    using hsurvival

omit [Nontrivial ι] in
/-- Deleted survival in the canonical compact-law profile converges to the
product of the opponents' singleton Never masses. -/
theorem quittingOpponentSurvivalWeight_compactStoppingLawProfile_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw) (who : ι) :
    Tendsto (fun time => quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward
          (quittingCompactStoppingLawProfile reward laws)) who 0 time)
      atTop (nhds (quittingOpponentNeverProduct laws who)) := by
  rw [show (fun time => quittingOpponentSurvivalWeight
      (quittingProfileLiveRoot reward
        (quittingCompactStoppingLawProfile reward laws)) who 0 time) =
      fun time => ∏ opponent ∈ Finset.univ.erase who,
        quittingHazardSurvival
          (fun stage => quittingProfileLiveRoot reward
            (quittingCompactStoppingLawProfile reward laws) stage opponent)
          time by
    funext time
    exact quittingOpponentSurvivalWeight_eq_prod_hazardSurvival _ who time]
  unfold quittingOpponentNeverProduct
  exact tendsto_finsetProd (Finset.univ.erase who) fun opponent _ =>
    quittingCompactStoppingLawProfile_hazardSurvival_tendsto
      reward laws opponent

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- Nonproperness is exactly positivity of the singleton Never mass. -/
theorem compactStoppingLaw_realMass_top_pos_of_not_isProper
    {law : CompactStoppingLaw} (hnot : ¬ compactStoppingLawIsProper law) :
    0 < law.realMass ({⊤} : Set CompactStoppingTime) := by
  apply lt_of_le_of_ne (CompactStoppingLaw.realMass_nonneg law _)
  exact Ne.symm (by simpa [compactStoppingLawIsProper] using hnot)

omit [Nontrivial ι] in
/-- If every opponent limit law is nonproper, the reconstructed opponents'
one-stage joint Continue probability tends to one. -/
theorem quittingFixedOpponentsContinueMass_compactStoppingLawProfile_tendsto_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw) (who : ι)
    (hopponents : ∀ opponent ≠ who,
      ¬ compactStoppingLawIsProper (laws opponent)) :
    Tendsto (fun time => quittingFixedOpponentsContinueMass
        (quittingProfileLiveRoot reward
          (quittingCompactStoppingLawProfile reward laws)) who time)
      atTop (nhds 1) := by
  let roots := quittingProfileLiveRoot reward
    (quittingCompactStoppingLawProfile reward laws)
  have hcontinue (opponent : ι) (hne : opponent ≠ who) :
      Tendsto (fun time => (roots time opponent false).toReal)
        atTop (nhds 1) := by
    have hnone : 0 < ((laws opponent).toPMF ⊤).toReal := by
      rw [CompactStoppingLaw.toPMF_apply_toReal]
      exact compactStoppingLaw_realMass_top_pos_of_not_isProper
        (hopponents opponent hne)
    have hquit :=
      StoppingLaw.toScalarHazard_toBoolean_quit_tendsto_zero_of_none_pos
        (laws opponent).toPMF hnone
    have hquit' : Tendsto (fun time => (roots time opponent true).toReal)
        atTop (nhds 0) := by
      change Tendsto (fun time =>
        (((StoppingLaw.toScalarHazard (laws opponent).toPMF).toBoolean time)
          true).toReal) atTop (nhds 0)
      exact hquit
    have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [Math.PMFProduct.pmfBool_false_toReal, sub_zero] using
      hone.sub hquit'
  have hstage (time : Nat) :
      quittingFixedOpponentsContinueMass roots who time =
        ∏ opponent ∈ Finset.univ.erase who,
          (roots time opponent false).toReal := by
    unfold quittingFixedOpponentsContinueMass
    rw [quittingStationaryContinueMass_eq_prod_continueProbability,
      ← Finset.mul_prod_erase Finset.univ
        (fun player =>
          (Function.update (roots time) who (PMF.pure false) player false).toReal)
        (Finset.mem_univ who)]
    simp only [Function.update_self, PMF.pure_apply, if_pos,
      ENNReal.toReal_one, one_mul]
    apply Finset.prod_congr rfl
    intro opponent hopponent
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hopponent)]
  rw [show (fun time => quittingFixedOpponentsContinueMass roots who time) =
      fun time => ∏ opponent ∈ Finset.univ.erase who,
        (roots time opponent false).toReal by
    funext time
    exact hstage time]
  simpa using tendsto_finsetProd (Finset.univ.erase who) fun opponent hopponent =>
    hcontinue opponent (Finset.ne_of_mem_erase hopponent)

omit [Nontrivial ι] in
/-- When every opponent limit law is nonproper, the value of quitting at a
late reconstructed row converges to the player's singleton reward. -/
theorem quittingFixedOpponentsQuitValue_compactStoppingLawProfile_tendsto_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw) (who : ι)
    (hopponents : ∀ opponent ≠ who,
      ¬ compactStoppingLawIsProper (laws opponent)) :
    Tendsto (fun time => quittingFixedOpponentsQuitValue reward
        (quittingProfileLiveRoot reward
          (quittingCompactStoppingLawProfile reward laws)) who time)
      atTop (nhds (reward (quittingSingletonTerminal who) who)) := by
  obtain ⟨bound, hbound, hreward⟩ := exists_quittingRewardBound reward
  let roots := quittingProfileLiveRoot reward
    (quittingCompactStoppingLawProfile reward laws)
  let continueMass := fun time =>
    quittingFixedOpponentsContinueMass roots who time
  let quitValue := fun time =>
    quittingFixedOpponentsQuitValue reward roots who time
  let solo := reward (quittingSingletonTerminal who) who
  have hcontinue : Tendsto continueMass atTop (nhds 1) := by
    exact quittingFixedOpponentsContinueMass_compactStoppingLawProfile_tendsto_one
      reward laws who hopponents
  have herrorBound (time : Nat) :
      |quitValue time - continueMass time * solo| ≤
        bound * (1 - continueMass time) := by
    exact abs_quittingFixedOpponentsQuitValue_sub_continueMass_mul_solo_le
      reward roots who time bound hbound (fun terminal => hreward terminal who)
  have hboundZero : Tendsto (fun time => bound * (1 - continueMass time))
      atTop (nhds 0) := by
    have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using (hone.sub hcontinue).const_mul bound
  have herror : Tendsto
      (fun time => quitValue time - continueMass time * solo)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero (fun time => abs_nonneg _) herrorBound hboundZero
  have hcontinueSolo : Tendsto (fun time => continueMass time * solo)
      atTop (nhds solo) := by
    simpa [mul_comm] using hcontinue.const_mul solo
  have hsum := herror.add hcontinueSolo
  simpa [quitValue, continueMass, solo, roots] using hsum

omit [Nontrivial ι] in
/-- **Late-finite/Never identity.**  Against reconstructed nonproper opponent
laws, a deterministic Quit time tending to infinity converges to the Never
reply plus the common opponent-Never probability times the singleton reward. -/
theorem quittingTerminalPayoff_update_finiteTime_tendsto_never_add_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw) (who : ι)
    (hopponents : ∀ opponent ≠ who,
      ¬ compactStoppingLawIsProper (laws opponent)) :
    Tendsto (fun time => quittingTerminalPayoff reward
        (Function.update
          (quittingCompactStoppingLawProfile reward laws) who
          (quittingPureTimeBehaviorStrategy reward who (some time))) who)
      atTop (nhds (quittingTerminalPayoff reward
          (Function.update
            (quittingCompactStoppingLawProfile reward laws) who
            (quittingPureTimeBehaviorStrategy reward who none)) who +
        quittingOpponentNeverProduct laws who *
          reward (quittingSingletonTerminal who) who)) := by
  let profile := quittingCompactStoppingLawProfile reward laws
  let roots := quittingProfileLiveRoot reward profile
  let solo := reward (quittingSingletonTerminal who) who
  have hledger := tendsto_quittingLiveLedgerAccum reward roots who
  have hsurvival : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop
      (nhds (quittingOpponentNeverProduct laws who)) := by
    exact quittingOpponentSurvivalWeight_compactStoppingLawProfile_tendsto
      reward laws who
  have hquit : Tendsto
      (quittingFixedOpponentsQuitValue reward roots who) atTop (nhds solo) := by
    exact
      quittingFixedOpponentsQuitValue_compactStoppingLawProfile_tendsto_singleton
        reward laws who hopponents
  have hsum := hledger.add (hsurvival.mul hquit)
  simpa only [profile, roots, solo,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingRootSequencePureTimeTerminalValue_some_eq] using hsum

omit [Nontrivial ι] in
/-- Nonproperness of every opponent makes their common singleton Never
probability strictly positive. -/
theorem quittingOpponentNeverProduct_pos_of_opponents_not_isProper
    (laws : ι → CompactStoppingLaw) (who : ι)
    (hopponents : ∀ opponent ≠ who,
      ¬ compactStoppingLawIsProper (laws opponent)) :
    0 < quittingOpponentNeverProduct laws who := by
  unfold quittingOpponentNeverProduct
  apply Finset.prod_pos
  intro opponent hopponent
  exact compactStoppingLaw_realMass_top_pos_of_not_isProper
    (hopponents opponent (Finset.ne_of_mem_erase hopponent))

/-- In the nonattained one-proper minimum arm, the reconstructed proper
player's unrestricted cap is attained exactly by Never. -/
theorem proper_minimum_cap_eq_never_of_notAttained_lawLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : Nat → (quittingGame reward).BehaviorProfile)
    (target : QuittingTerminalSemanticPair ι)
    (laws : ι → CompactStoppingLaw)
    (hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds target))
    (hlaw : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward (profiles n) player)
      atTop (nhds (laws player)))
    (properPlayer : ι)
    (hproper : compactStoppingLawIsProper (laws properPlayer))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum target ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnotAttained : ∀ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticPair reward profile ≠ target) :
    quittingContinuationBestResponseValue reward
        (quittingCompactStoppingLawProfile reward laws) properPlayer =
      quittingTerminalPayoff reward
        (Function.update
          (quittingCompactStoppingLawProfile reward laws) properPlayer
          (quittingPureTimeBehaviorStrategy reward properPlayer none))
        properPlayer := by
  apply quittingContinuationBestResponseValue_eq_never_of_finite_le_of_lt
    reward (quittingCompactStoppingLawProfile reward laws) properPlayer
      (target.2 properPlayer)
  · intro time
    exact quittingTerminalPayoff_update_finiteTime_le_of_lawLimit
      reward profiles target laws hsemantic hlaw properPlayer time
  · exact target_cap_lt_of_proper_minimum_notAttained_lawLimit
      reward profiles target laws hsemantic hlaw properPlayer hproper
        hminimum hnotAttained

/-- **One-proper minimum negative-singleton jump.**  On one fixed selected
law-limit sequence, if exactly one limiting clock is proper and a globally
minimum semantic target is not attained, then only that player's cap jumps.
The jump is attained by Never and is bounded by the positive common
opponent-Never mass times a strictly negative singleton reward.  Positivity
of the minimum debt is not needed for this stronger algebraic conclusion. -/
theorem oneProper_minimum_negativeSingletonJump_of_notAttained_lawLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : Nat → (quittingGame reward).BehaviorProfile)
    (target : QuittingTerminalSemanticPair ι)
    (laws : ι → CompactStoppingLaw)
    (hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds target))
    (hlaw : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward (profiles n) player)
      atTop (nhds (laws player)))
    (properPlayer : ι)
    (hproper : compactStoppingLawIsProper (laws properPlayer))
    (hopponents : ∀ opponent ≠ properPlayer,
      ¬ compactStoppingLawIsProper (laws opponent))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum target ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnotAttained : ∀ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticPair reward profile ≠ target) :
    let limitProfile := quittingCompactStoppingLawProfile reward laws
    let limitPair := quittingTerminalSemanticPair reward limitProfile
    let limitCap := limitPair.2 properPlayer
    let commonNever := quittingOpponentNeverProduct laws properPlayer
    let singleton := reward (quittingSingletonTerminal properPlayer) properPlayer
    limitPair.1 = target.1 ∧
      (∀ player ≠ properPlayer,
        limitPair.2 player = target.2 player) ∧
      0 < commonNever ∧
      limitCap = quittingTerminalPayoff reward
        (Function.update limitProfile properPlayer
          (quittingPureTimeBehaviorStrategy reward properPlayer none))
        properPlayer ∧
      (∀ time : Nat, quittingTerminalPayoff reward
        (Function.update limitProfile properPlayer
          (quittingPureTimeBehaviorStrategy reward properPlayer (some time)))
        properPlayer ≤ target.2 properPlayer) ∧
      singleton < 0 ∧
      0 < limitCap - target.2 properPlayer ∧
      limitCap - target.2 properPlayer ≤ -commonNever * singleton := by
  dsimp only
  let limitProfile := quittingCompactStoppingLawProfile reward laws
  let limitPair := quittingTerminalSemanticPair reward limitProfile
  let limitCap := limitPair.2 properPlayer
  let commonNever := quittingOpponentNeverProduct laws properPlayer
  let singleton := reward (quittingSingletonTerminal properPlayer) properPlayer
  obtain ⟨hprescribed, hotherCaps⟩ :=
    quittingTerminalSemanticPair_partial_eq_of_proper_lawLimit
      reward profiles target laws hsemantic hlaw properPlayer hproper
  have hstrict : target.2 properPlayer < limitCap := by
    exact target_cap_lt_of_proper_minimum_notAttained_lawLimit
      reward profiles target laws hsemantic hlaw properPlayer hproper
        hminimum hnotAttained
  have hfinite : ∀ time : Nat, quittingTerminalPayoff reward
      (Function.update limitProfile properPlayer
        (quittingPureTimeBehaviorStrategy reward properPlayer (some time)))
      properPlayer ≤ target.2 properPlayer := by
    intro time
    exact quittingTerminalPayoff_update_finiteTime_le_of_lawLimit
      reward profiles target laws hsemantic hlaw properPlayer time
  have hcapNever : limitCap = quittingTerminalPayoff reward
      (Function.update limitProfile properPlayer
        (quittingPureTimeBehaviorStrategy reward properPlayer none))
      properPlayer := by
    exact proper_minimum_cap_eq_never_of_notAttained_lawLimit
      reward profiles target laws hsemantic hlaw properPlayer hproper
        hminimum hnotAttained
  have hcommonNever : 0 < commonNever :=
    quittingOpponentNeverProduct_pos_of_opponents_not_isProper
      laws properPlayer hopponents
  have hlate :=
    quittingTerminalPayoff_update_finiteTime_tendsto_never_add_singleton
      reward laws properPlayer hopponents
  have hlateCap : Tendsto (fun time => quittingTerminalPayoff reward
      (Function.update limitProfile properPlayer
        (quittingPureTimeBehaviorStrategy reward properPlayer (some time)))
      properPlayer) atTop (nhds (limitCap + commonNever * singleton)) := by
    rw [hcapNever]
    exact hlate
  have hendpointLe : limitCap + commonNever * singleton ≤
      target.2 properPlayer :=
    le_of_tendsto hlateCap (Filter.Eventually.of_forall hfinite)
  have hgapPos : 0 < limitCap - target.2 properPlayer := sub_pos.mpr hstrict
  have hgapLe : limitCap - target.2 properPlayer ≤
      -commonNever * singleton := by
    linarith
  have hsingleton : singleton < 0 := by
    nlinarith
  refine ⟨hprescribed, hotherCaps, hcommonNever, hcapNever, hfinite,
    hsingleton, hgapPos, hgapLe⟩

omit [Nontrivial ι] in
/-- Two distinct proper weak-limit clocks make every player face a uniformly
tight opponent along the selected coordinatewise convergent law sequence. -/
theorem QuittingOpponentTightLawSequence.of_twoProperLimits
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)))
    (first second : ι) (hne : first ≠ second)
    (hfirst : compactStoppingLawIsProper (laws first))
    (hsecond : compactStoppingLawIsProper (laws second)) :
    QuittingOpponentTightLawSequence lawSeq := by
  intro owner ε hε
  let opponent := if owner = first then second else first
  have hopponentNe : opponent ≠ owner := by
    dsimp [opponent]
    split_ifs with howner
    · simpa [howner] using hne.symm
    · exact Ne.symm howner
  have hopponentProper : compactStoppingLawIsProper (laws opponent) := by
    dsimp [opponent]
    split_ifs
    · exact hsecond
    · exact hfirst
  have htailZero :=
    tendsto_compactStoppingLawTailMass_zero_of_isProper hopponentProper
  obtain ⟨horizon, hlimitTail⟩ :=
    (Metric.tendsto_atTop.1 htailZero) (ε / 2) (by positivity)
  have hlimitTail' : compactStoppingLawTailMass (laws opponent) horizon < ε / 2 := by
    have hlimitTailAt := hlimitTail horizon le_rfl
    rw [Real.dist_0_eq_abs] at hlimitTailAt
    exact lt_of_le_of_lt (le_abs_self _) hlimitTailAt
  have htailConverges : Tendsto
      (fun n => compactStoppingLawTailMass (lawSeq n opponent) horizon)
      atTop (nhds (compactStoppingLawTailMass (laws opponent) horizon)) := by
    exact CompactStoppingLaw.tendsto_realMass_of_isClopen (hlaw opponent)
      (compactStoppingTime_tail_isClopen horizon)
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.1 htailConverges) (ε / 2) (by positivity)
  have heventuallyClose : ∀ᶠ n in atTop,
      compactStoppingLawTailMass (lawSeq n opponent) horizon < ε :=
    Filter.eventually_atTop.2 ⟨threshold, fun n hn => by
      have hdist := hthreshold n hn
      rw [Real.dist_eq] at hdist
      rw [abs_sub_lt_iff] at hdist
      linarith⟩
  refine ⟨horizon, heventuallyClose.mono ?_⟩
  intro n hn
  exact lt_of_le_of_lt
    (quittingOpponentTailProduct_le_tailMass_of_ne
      (lawSeq n) owner opponent hopponentNe horizon) hn

/-- **Two-proper realization.**  Two distinct proper coordinatewise weak
limits realize the semantic limit of the actual source profiles. -/
theorem quittingTerminalSemanticPair_eq_of_twoProper_lawLimits
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : Nat → (quittingGame reward).BehaviorProfile)
    (target : QuittingTerminalSemanticPair ι)
    (laws : ι → CompactStoppingLaw)
    (hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds target))
    (hlaw : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward (profiles n) player)
      atTop (nhds (laws player)))
    (first second : ι) (hne : first ≠ second)
    (hfirst : compactStoppingLawIsProper (laws first))
    (hsecond : compactStoppingLawIsProper (laws second)) :
    quittingTerminalSemanticPair reward
        (quittingCompactStoppingLawProfile reward laws) = target := by
  apply quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit
    reward profiles target laws hsemantic hlaw
  exact QuittingOpponentTightLawSequence.of_twoProperLimits
    hlaw first second hne hfirst hsecond

/-- On a selected law-limit sequence for a semantic point not realized by any
actual profile, two proper limiting clocks must have the same owner. -/
theorem compactStoppingLaw_isProper_owner_unique_of_not_attained
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : Nat → (quittingGame reward).BehaviorProfile)
    (target : QuittingTerminalSemanticPair ι)
    (laws : ι → CompactStoppingLaw)
    (hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds target))
    (hlaw : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward (profiles n) player)
      atTop (nhds (laws player)))
    (hnotAttained : ∀ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticPair reward profile ≠ target)
    {first second : ι}
    (hfirst : compactStoppingLawIsProper (laws first))
    (hsecond : compactStoppingLawIsProper (laws second)) :
    first = second := by
  by_contra hne
  apply hnotAttained (quittingCompactStoppingLawProfile reward laws)
  exact quittingTerminalSemanticPair_eq_of_twoProper_lawLimits
    reward profiles target laws hsemantic hlaw first second hne hfirst hsecond

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- The limiting Never atom of one clock is contained in every one of its
late-or-Never tails. -/
theorem compactStoppingLaw_realMass_top_le_tailMass
    (law : CompactStoppingLaw) (horizon : Nat) :
    law.realMass ({⊤} : Set CompactStoppingTime) ≤
      compactStoppingLawTailMass law horizon := by
  unfold CompactStoppingLaw.realMass compactStoppingLawTailMass
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro choice hchoice
  have htop : choice = ⊤ := Set.mem_singleton_iff.mp hchoice
  subst choice
  simp

/-- If at most one limiting clock is proper, then on the fixed selected
coordinatewise convergent sequence one owner has a positive common
late-or-Never lower bound at every finite horizon. -/
theorem exists_commonLateOpponentTail_of_proper_owner_unique
    {lawSeq : Nat → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)))
    (hproperUnique : ∀ {first second},
      compactStoppingLawIsProper (laws first) →
      compactStoppingLawIsProper (laws second) → first = second) :
    ∃ (owner : ι) (lowerBound : Real),
      0 < lowerBound ∧
      ∀ horizon, ∀ᶠ n in atTop,
        lowerBound < quittingOpponentTailProduct (lawSeq n) owner horizon := by
  classical
  let owner : ι := if hproper : ∃ player, compactStoppingLawIsProper (laws player)
    then Classical.choose hproper
    else Classical.choice (inferInstance : Nonempty ι)
  have hopponentsNonproper : ∀ opponent ≠ owner,
      ¬ compactStoppingLawIsProper (laws opponent) := by
    intro opponent hne hopponent
    by_cases hproper : ∃ player, compactStoppingLawIsProper (laws player)
    · have howner : compactStoppingLawIsProper (laws owner) := by
        simpa [owner, hproper] using Classical.choose_spec hproper
      exact hne (hproperUnique hopponent howner)
    · exact hproper ⟨opponent, hopponent⟩
  let neverMass := fun player : ι =>
    (laws player).realMass ({⊤} : Set CompactStoppingTime)
  let limitLower := ∏ opponent ∈ Finset.univ.erase owner, neverMass opponent
  have hneverPos : ∀ opponent ∈ Finset.univ.erase owner,
      0 < neverMass opponent := by
    intro opponent hopponent
    have hne : opponent ≠ owner := Finset.ne_of_mem_erase hopponent
    have hnonzero : neverMass opponent ≠ 0 := by
      simpa [neverMass, compactStoppingLawIsProper] using hopponentsNonproper opponent hne
    exact lt_of_le_of_ne
      (CompactStoppingLaw.realMass_nonneg (laws opponent) _)
      (Ne.symm hnonzero)
  have hlimitLowerPos : 0 < limitLower := by
    exact Finset.prod_pos hneverPos
  refine ⟨owner, limitLower / 2, by positivity, ?_⟩
  intro horizon
  have hproductLower : limitLower ≤
      quittingOpponentTailProduct laws owner horizon := by
    unfold quittingOpponentTailProduct limitLower
    exact Finset.prod_le_prod
      (fun opponent _ => CompactStoppingLaw.realMass_nonneg (laws opponent) _)
      (fun opponent _ =>
        compactStoppingLaw_realMass_top_le_tailMass (laws opponent) horizon)
  have hstrict : limitLower / 2 <
      quittingOpponentTailProduct laws owner horizon := by
    exact lt_of_lt_of_le (by linarith) hproductLower
  exact (tendsto_order.1
    (quittingOpponentTailProduct_tendsto hlaw owner horizon)).1 _ hstrict

/-- **Common late-or-Never alternative.**  A semantic point not attained by
an actual profile leaves, on each fixed coordinatewise weak law-limit
sequence, one owner and one positive lower bound that work at every finite
horizon.  The event concerns finite approximants' late-or-Never tails, not
their singleton Never atoms. -/
theorem exists_commonLateOpponentTail_of_not_attained_lawLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : Nat → (quittingGame reward).BehaviorProfile)
    (target : QuittingTerminalSemanticPair ι)
    (laws : ι → CompactStoppingLaw)
    (hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds target))
    (hlaw : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward (profiles n) player)
      atTop (nhds (laws player)))
    (hnotAttained : ∀ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticPair reward profile ≠ target) :
    ∃ (owner : ι) (lowerBound : Real),
      0 < lowerBound ∧
      ∀ horizon, ∀ᶠ n in atTop,
        lowerBound < quittingOpponentTailProduct
          (quittingCompactStoppingLawsOfProfile reward (profiles n))
          owner horizon := by
  apply exists_commonLateOpponentTail_of_proper_owner_unique hlaw
  intro first second hfirst hsecond
  exact compactStoppingLaw_isProper_owner_unique_of_not_attained
    reward profiles target laws hsemantic hlaw hnotAttained hfirst hsecond

/-- **Nonnegative-singleton residual arm.**  If every player's singleton
reward is nonnegative, then a globally minimum semantic target not attained by
an actual profile can have no proper clock on the fixed selected weak law
limit.  Thus only the all-nonproper arm remains. -/
theorem all_not_compactStoppingLawIsProper_of_singleton_nonnegative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : Nat → (quittingGame reward).BehaviorProfile)
    (target : QuittingTerminalSemanticPair ι)
    (laws : ι → CompactStoppingLaw)
    (hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds target))
    (hlaw : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward (profiles n) player)
      atTop (nhds (laws player)))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum target ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnotAttained : ∀ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticPair reward profile ≠ target)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player) :
    ∀ player, ¬ compactStoppingLawIsProper (laws player) := by
  intro properPlayer hproper
  have hopponents : ∀ opponent ≠ properPlayer,
      ¬ compactStoppingLawIsProper (laws opponent) := by
    intro opponent hne hopponent
    exact hne (compactStoppingLaw_isProper_owner_unique_of_not_attained
      reward profiles target laws hsemantic hlaw hnotAttained hopponent hproper)
  obtain ⟨_, _, _, _, _, hnegative, _, _⟩ :=
    oneProper_minimum_negativeSingletonJump_of_notAttained_lawLimit
      reward profiles target laws hsemantic hlaw properPlayer hproper
        hopponents hminimum hnotAttained
  exact (not_lt_of_ge (hsingleton properPlayer)) hnegative

/-- Every nonattained carrier point admits a selected actual-profile law
limit with one owner whose opponents retain a common positive late-or-Never
tail lower bound at every finite horizon. -/
theorem exists_terminalSemanticSelectedLawLimit_with_commonLateOpponentTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : QuittingTerminalSemanticPair ι)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hnotAttained : ∀ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticPair reward profile ≠ target) :
    ∃ selected : QuittingTerminalSemanticSelectedLawLimit reward target,
      ∃ (owner : ι) (lowerBound : Real),
        0 < lowerBound ∧
        ∀ horizon, ∀ᶠ n in atTop,
          lowerBound < quittingOpponentTailProduct
            (quittingCompactStoppingLawsOfProfile reward
              (selected.sourceProfile (selected.subseq n)))
            owner horizon := by
  obtain ⟨selected⟩ :=
    nonempty_terminalSemanticSelectedLawLimit_of_mem_carrier
      reward target htarget
  refine ⟨selected, ?_⟩
  exact exists_commonLateOpponentTail_of_not_attained_lawLimit
    reward (fun n => selected.sourceProfile (selected.subseq n)) target
      selected.laws selected.semantic_tendsto selected.law_tendsto hnotAttained

/-- At a nonattained global minimum with nonnegative singleton self-rewards,
one selected actual-profile law limit exists and all of its limiting clocks
are nonproper. -/
theorem exists_terminalSemanticSelectedLawLimit_with_all_nonproper
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : QuittingTerminalSemanticPair ι)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum target ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnotAttained : ∀ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticPair reward profile ≠ target)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player) :
    ∃ selected : QuittingTerminalSemanticSelectedLawLimit reward target,
      ∀ player, ¬ compactStoppingLawIsProper (selected.laws player) := by
  obtain ⟨selected⟩ :=
    nonempty_terminalSemanticSelectedLawLimit_of_mem_carrier
      reward target htarget
  refine ⟨selected, ?_⟩
  exact all_not_compactStoppingLawIsProper_of_singleton_nonnegative
    reward (fun n => selected.sourceProfile (selected.subseq n)) target
      selected.laws selected.semantic_tendsto selected.law_tendsto hminimum
        hnotAttained hsingleton

end GameTheory
