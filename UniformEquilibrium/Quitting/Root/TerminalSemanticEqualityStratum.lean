/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.LiveMass
import MathUE.ProbabilityMassFunction.Bool
import UniformEquilibrium.Quitting.Terminal.TerminalDebtPrefixDescent
import UniformEquilibrium.Quitting.Root.FaceGeometry
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-!
# Minimum-debt equality stratum of the literal semantic carrier

The compact closure of attainable prescribed/envelope pairs admits a minimum
of total literal debt.  Exact Nash prefixing preserves the carrier and weakly
decreases every nonnegative debt coordinate.  At a total-debt minimizer every
coordinate is therefore preserved exactly.

Every positive debt coordinate lies on the unit deleted-survival,
zero-exercise-premium face.  Two positive debt coordinates force the whole
root to all-Continue; a unique positive coordinate leaves only that player's
own marginal uncontrolled.  This is an exact finite-dimensional equality
stratum, not a realization of a conditioned boundary by one behavior profile.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.SurvivalWeightedObstruction
  QuittingBoundaryHolonomy
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Total debt of a finite-dimensional terminal semantic pair. -/
def quittingTerminalSemanticDebtSum
    (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  ∑ who, quittingTerminalSemanticDebt pair who

/-- Maximum positive debt of a finite-dimensional terminal semantic pair. -/
def quittingTerminalSemanticExploitability [Nonempty ι]
    (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  finitePlayerMax fun who => max 0 (quittingTerminalSemanticDebt pair who)

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_quittingTerminalSemanticDebt (who : ι) :
    Continuous (fun pair : QuittingTerminalSemanticPair ι =>
      quittingTerminalSemanticDebt pair who) := by
  unfold quittingTerminalSemanticDebt
  have hfirst : Continuous
      (fun pair : QuittingTerminalSemanticPair ι => pair.1 who) := by
    fun_prop
  have hsecond : Continuous
      (fun pair : QuittingTerminalSemanticPair ι => pair.2 who) := by
    fun_prop
  exact hsecond.sub hfirst

omit [DecidableEq ι] in
theorem continuous_quittingTerminalSemanticDebtSum :
    Continuous (quittingTerminalSemanticDebtSum :
      QuittingTerminalSemanticPair ι → ℝ) := by
  unfold quittingTerminalSemanticDebtSum
  exact continuous_finsetSum
    (s := (Finset.univ : Finset ι)) fun who _ =>
      continuous_quittingTerminalSemanticDebt who

omit [DecidableEq ι] in
theorem continuous_quittingTerminalSemanticExploitability [Nonempty ι] :
    Continuous (quittingTerminalSemanticExploitability :
      QuittingTerminalSemanticPair ι → ℝ) := by
  unfold quittingTerminalSemanticExploitability finitePlayerMax
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro who _
  exact continuous_const.max (continuous_quittingTerminalSemanticDebt who)

/-- Actual semantic pairs have nonnegative debt in every coordinate. -/
theorem quittingTerminalSemanticDebt_nonneg_of_attainable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ quittingAttainableTerminalSemanticPairs reward) :
    ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who := by
  rintro who
  obtain ⟨profile, rfl⟩ := hpair
  exact quittingTerminalDeviationDebt_nonneg reward profile who

/-- Nonnegative debt extends to the compact attainable-semantic closure. -/
theorem quittingTerminalSemanticDebt_nonneg_of_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who := by
  have hclosed : IsClosed {candidate : QuittingTerminalSemanticPair ι |
      ∀ who, 0 ≤ quittingTerminalSemanticDebt candidate who} := by
    rw [show {candidate : QuittingTerminalSemanticPair ι |
        ∀ who, 0 ≤ quittingTerminalSemanticDebt candidate who} =
      ⋂ who, {candidate | 0 ≤ quittingTerminalSemanticDebt candidate who} by
        ext candidate
        simp]
    exact isClosed_iInter fun who =>
      isClosed_le continuous_const
        (continuous_quittingTerminalSemanticDebt who)
  exact (closure_minimal
    (fun candidate hcandidate =>
      quittingTerminalSemanticDebt_nonneg_of_attainable
        reward hcandidate)
    hclosed) hpair

/-- On actual pairs, semantic exploitability is literal terminal
exploitability. -/
theorem quittingTerminalSemanticExploitability_pair
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPair reward profile) =
      quittingTerminalExploitability reward profile := rfl

/-- The global literal exploitability infimum lower-bounds every pair in the
attainable-semantic closure. -/
theorem quittingTerminalExploitabilityInf_le_semanticCarrier
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalExploitabilityInf reward ≤
      quittingTerminalSemanticExploitability pair := by
  have hclosed : IsClosed {candidate : QuittingTerminalSemanticPair ι |
      quittingTerminalExploitabilityInf reward ≤
        quittingTerminalSemanticExploitability candidate} :=
    isClosed_le continuous_const
      continuous_quittingTerminalSemanticExploitability
  apply (closure_minimal ?_ hclosed) hpair
  rintro candidate ⟨profile, rfl⟩
  change quittingTerminalExploitabilityInf reward ≤
    quittingTerminalSemanticExploitability
      (quittingTerminalSemanticPair reward profile)
  rw [quittingTerminalSemanticExploitability_pair]
  exact quittingTerminalExploitabilityInf_le reward profile

/-- Total semantic debt attains a minimum on the compact literal carrier. -/
theorem exists_minimum_quittingTerminalSemanticDebtSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ pair ∈ quittingTerminalSemanticCarrier reward,
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤
          quittingTerminalSemanticDebtSum candidate := by
  obtain ⟨pair, hpair, hmin⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).exists_isMinOn
      (quittingTerminalSemanticCarrier_nonempty reward)
      continuous_quittingTerminalSemanticDebtSum.continuousOn
  exact ⟨pair, hpair, fun candidate hcandidate => hmin hcandidate⟩

/-- A minimum-total-debt carrier point has an executable realizing sequence,
and both finite-dimensional debt objectives converge along that sequence. -/
theorem exists_profile_sequence_tendsto_minimumTerminalSemanticDebt
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ (pair : QuittingTerminalSemanticPair ι)
        (profiles : ℕ → (quittingGame reward).BehaviorProfile),
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
        atTop (𝓝 pair) ∧
      Tendsto (fun n => quittingTerminalDebtSum reward (profiles n))
        atTop (𝓝 (quittingTerminalSemanticDebtSum pair)) ∧
      Tendsto (fun n => quittingTerminalExploitability reward (profiles n))
        atTop (𝓝 (quittingTerminalSemanticExploitability pair)) := by
  obtain ⟨pair, hpair, hmin⟩ :=
    exists_minimum_quittingTerminalSemanticDebtSum reward
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward pair hpair
  have hsum : Tendsto
      (fun n => quittingTerminalDebtSum reward (profiles n)) atTop
      (𝓝 (quittingTerminalSemanticDebtSum pair)) := by
    have hcontinuous :=
      continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
        hprofiles
    have hfunction :
        (quittingTerminalSemanticDebtSum ∘ fun n =>
          quittingTerminalSemanticPair reward (profiles n)) =
        (fun n => quittingTerminalDebtSum reward (profiles n)) := by
      funext n
      rfl
    rw [hfunction] at hcontinuous
    exact hcontinuous
  have hmax : Tendsto
      (fun n => quittingTerminalExploitability reward (profiles n)) atTop
      (𝓝 (quittingTerminalSemanticExploitability pair)) := by
    have hcontinuous :=
      continuous_quittingTerminalSemanticExploitability.continuousAt.tendsto.comp
        hprofiles
    have hfunction :
        (quittingTerminalSemanticExploitability ∘ fun n =>
          quittingTerminalSemanticPair reward (profiles n)) =
        (fun n => quittingTerminalExploitability reward (profiles n)) := by
      funext n
      exact quittingTerminalSemanticExploitability_pair reward (profiles n)
    rw [hfunction] at hcontinuous
    exact hcontinuous
  exact ⟨pair, profiles, hpair, hmin, hprofiles, hsum, hmax⟩

/-- At a minimum-total-debt semantic pair, every exact Nash prefix preserves
every debt coordinate. -/
theorem quittingTerminalSemanticDebt_prefix_eq_of_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    ∀ who,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) who =
        quittingTerminalSemanticDebt pair who := by
  let prefixed := quittingTerminalSemanticPrefix reward root pair
  have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier
      reward root pair hpair
  have hnonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hpair
  have hcoordinate : ∀ who,
      quittingTerminalSemanticDebt prefixed who ≤
        quittingTerminalSemanticDebt pair who := fun who =>
    quittingTerminalSemanticDebt_prefix_le
      reward pair root who (hnonneg who) hnash
  have hsum_le : quittingTerminalSemanticDebtSum prefixed ≤
      quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_le_sum fun who _ => hcoordinate who
  have hsum_eq : quittingTerminalSemanticDebtSum prefixed =
      quittingTerminalSemanticDebtSum pair :=
    le_antisymm hsum_le (hmin prefixed hprefixed)
  have hdiff_sum :
      ∑ who, (quittingTerminalSemanticDebt pair who -
        quittingTerminalSemanticDebt prefixed who) = 0 := by
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hsum_eq.symm
  have hdiff_nonneg : ∀ who ∈ (Finset.univ : Finset ι),
      0 ≤ quittingTerminalSemanticDebt pair who -
        quittingTerminalSemanticDebt prefixed who := fun who _ =>
    sub_nonneg.mpr (hcoordinate who)
  have hzero :=
    (Finset.sum_eq_zero_iff_of_nonneg hdiff_nonneg).mp hdiff_sum
  intro who
  have := hzero who (Finset.mem_univ who)
  linarith

/-- A positive semantic debt fixed by its survival block lies on the exact
unit-survival, zero-premium face.  This is the premise-minimal algebraic
rigidity statement. -/
theorem quittingTerminalSemantic_positiveDebt_face_of_blockAct_eq_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (who : ι) (hpositive : 0 < quittingTerminalSemanticDebt pair who)
    (heq : (quittingTerminalSemanticDebtBlock reward pair root who).act ()
        (quittingTerminalSemanticDebt pair who) =
      quittingTerminalSemanticDebt pair who) :
    quittingRootOpponentContinueMass root who = 1 ∧
      quittingRootExercisePremium reward pair.1 root who = 0 := by
  simpa [quittingTerminalSemanticDebtBlock] using
    (Block.act_eq_self_iff_of_pos
      (quittingTerminalSemanticDebtBlock reward pair root who)
      () hpositive).mp heq

/-- A positive semantic debt fixed in one coordinate by an exact Nash prefix
lies on the exact unit-survival, zero-premium face.  No carrier or global
minimality hypothesis is needed once the coordinate equality is supplied. -/
theorem quittingTerminalSemantic_positiveDebt_face_of_prefix_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (who : ι) (hpositive : 0 < quittingTerminalSemanticDebt pair who)
    (heq : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingTerminalSemanticDebt pair who) :
    quittingRootOpponentContinueMass root who = 1 ∧
      quittingRootExercisePremium reward pair.1 root who = 0 := by
  rw [quittingTerminalSemanticDebt_prefix_eq_blockAct
    reward pair root who hpositive.le hnash] at heq
  exact quittingTerminalSemantic_positiveDebt_face_of_blockAct_eq_self
    reward pair root who hpositive heq

/-- Every positive debt coordinate at a minimum-total-debt semantic pair lies
on the exact unit-survival, zero-premium face of every exact Nash root. -/
theorem quittingTerminalSemantic_minimum_positiveDebt_face
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (who : ι) (hpositive : 0 < quittingTerminalSemanticDebt pair who) :
    quittingRootOpponentContinueMass root who = 1 ∧
      quittingRootExercisePremium reward pair.1 root who = 0 := by
  apply quittingTerminalSemantic_positiveDebt_face_of_prefix_eq
    reward pair root hnash who hpositive
  exact quittingTerminalSemanticDebt_prefix_eq_of_minimum
    reward pair root hpair hmin hnash who

/-- A positive debtor at the semantic minimum forces every opponent to
Continue purely. -/
theorem quittingTerminalSemantic_minimum_positiveDebt_opponents_pureContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    {who other : ι} (hpositive : 0 < quittingTerminalSemanticDebt pair who)
    (hne : other ≠ who) :
    root other = PMF.pure false := by
  have hface := quittingTerminalSemantic_minimum_positiveDebt_face
    reward pair root hpair hmin hnash who hpositive
  exact quittingRoot_opponents_pureContinue_of_opponentContinueMass_eq_one
    root who hface.1 other hne

/-- A positive minimum-debt coordinate dominates its singleton quitting
reward.  This conclusion uses the exact Nash root supplied at that semantic
point; it does not extend to arbitrary carrier coordinates. -/
theorem quittingTerminalSemantic_minimum_positiveDebt_singleton_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (who : ι) (hpositive : 0 < quittingTerminalSemanticDebt pair who) :
    reward (quittingSingletonTerminal who) who ≤ pair.1 who := by
  have hface := quittingTerminalSemantic_minimum_positiveDebt_face
    reward pair root hpair hmin hnash who hpositive
  exact quittingRoot_singleton_le_of_face reward pair.1 root who hface

/-- If a positive minimum-debt coordinate itself Quits with positive mass at
an exact Nash root, then its singleton reward equals its prescribed value.
The root's only possible absorption is that player's singleton event. -/
theorem quittingTerminalSemantic_minimum_positiveDebt_singleton_eq_of_quit_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (who : ι) (hpositive : 0 < quittingTerminalSemanticDebt pair who)
    (hquit : 0 < (root who true).toReal) :
    reward (quittingSingletonTerminal who) who = pair.1 who := by
  have hface := quittingTerminalSemantic_minimum_positiveDebt_face
    reward pair root hpair hmin hnash who hpositive
  exact quittingRoot_singleton_eq_of_face_of_quit_pos
    reward pair.1 root hnash who hface hquit

/-- Two distinct positive debts at the semantic minimum force the displayed
root itself to be all-Continue. -/
theorem quittingTerminalSemantic_minimum_twoPositiveDebt_root_eq_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    {first second : ι} (hdistinct : first ≠ second)
    (hfirst : 0 < quittingTerminalSemanticDebt pair first)
    (hsecond : 0 < quittingTerminalSemanticDebt pair second) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  have hfirstFace := quittingTerminalSemantic_minimum_positiveDebt_face
    reward pair root hpair hmin hnash first hfirst
  have hsecondFace := quittingTerminalSemantic_minimum_positiveDebt_face
    reward pair root hpair hmin hnash second hsecond
  exact quittingRoot_eq_allContinue_of_two_opponentContinueMass_eq_one
    root hdistinct hfirstFace.1 hsecondFace.1

/-- **Face-stratum alternative.**  Given nonnegative semantic debt and the
unit-survival, zero-premium face fact for every positive coordinate, an exact
Nash root either yields an all-Continue semantic self-loop or has a unique
positive-debt owner and is a genuine solo-owner deterrence row.

In the deterrence branch the owner Quits with positive mass and is exactly
singleton-tight.  Every outsider Continues purely and satisfies the exact
Quit-versus-Continue endpoint inequality.  At least one outsider has a
singleton reward strictly above its declared continuation, so that inequality
cannot be explained by the all-Continue row: the owner's possible exit and
the associated collision outcomes are essential. -/
theorem quittingTerminalSemantic_face_stratum_alternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hface : ∀ who, 0 < quittingTerminalSemanticDebt pair who →
      quittingRootOpponentContinueMass root who = 1 ∧
        quittingRootExercisePremium reward pair.1 root who = 0)
    (first : ι) (hfirst : 0 < quittingTerminalSemanticDebt pair first) :
    (IsεQuittingRootNash reward pair.1 0
          (quittingAllContinueRoot : ι → PMF Bool) ∧
        quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair =
          pair) ∨
      ∃ owner other,
        0 < quittingTerminalSemanticDebt pair owner ∧
        (∀ player, 0 < quittingTerminalSemanticDebt pair player →
          player = owner) ∧
        other ≠ owner ∧
        pair.1 other < reward (quittingSingletonTerminal other) other ∧
        0 < (root owner true).toReal ∧
        reward (quittingSingletonTerminal owner) owner = pair.1 owner ∧
        (∀ player, player ≠ owner → root player = PMF.pure false) ∧
        ∀ player, player ≠ owner →
          quittingRootQuitPayoff reward pair.1 root player ≤
            quittingRootContinuePayoff reward pair.1 root player := by
  by_cases hsecond : ∃ second, second ≠ first ∧
      0 < quittingTerminalSemanticDebt pair second
  · obtain ⟨second, hdistinct, hsecondPositive⟩ := hsecond
    have hroot :=
      quittingRoot_eq_allContinue_of_two_opponentContinueMass_eq_one
        root hdistinct.symm (hface first hfirst).1
          (hface second hsecondPositive).1
    have hnashAll : IsεQuittingRootNash reward pair.1 0
        (quittingAllContinueRoot : ι → PMF Bool) := by
      simpa [hroot] using hnash
    exact Or.inl ⟨hnashAll,
      quittingTerminalSemanticPrefix_allContinue_eq_of_isZeroNash
        reward pair hdebt hnashAll⟩
  · have hunique : ∀ player,
        0 < quittingTerminalSemanticDebt pair player → player = first := by
      intro player hplayer
      by_contra hne
      exact hsecond ⟨player, hne, hplayer⟩
    by_cases hnashAll : IsεQuittingRootNash reward pair.1 0
        (quittingAllContinueRoot : ι → PMF Bool)
    · exact Or.inl ⟨hnashAll,
        quittingTerminalSemanticPrefix_allContinue_eq_of_isZeroNash
          reward pair hdebt hnashAll⟩
    · have hnotDominate : ¬ ∀ player,
          reward (quittingSingletonTerminal player) player ≤ pair.1 player :=
        fun hdominate => hnashAll
          ((isZeroQuittingRootNash_allContinue_iff_singleton_le
            reward pair.1).mpr hdominate)
      push Not at hnotDominate
      obtain ⟨other, hotherGain⟩ := hnotDominate
      have hfirstDominate :
          reward (quittingSingletonTerminal first) first ≤ pair.1 first :=
        quittingRoot_singleton_le_of_face
          reward pair.1 root first (hface first hfirst)
      have hotherNe : other ≠ first := by
        intro heq
        subst other
        exact (not_lt_of_ge hfirstDominate) hotherGain
      have hpureOpponent : ∀ player, player ≠ first →
          root player = PMF.pure false := by
        exact
          quittingRoot_opponents_pureContinue_of_opponentContinueMass_eq_one
            root first (hface first hfirst).1
      have hzeroOpponent : ∀ player, player ≠ first →
          (root player true).toReal = 0 := by
        intro player hne
        rw [hpureOpponent player hne]
        simp
      have hownerQuit : 0 < (root first true).toReal := by
        by_contra hnot
        have hownerZero : (root first true).toReal = 0 :=
          le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
        have hroot : root =
            (quittingAllContinueRoot : ι → PMF Bool) := by
          funext player
          by_cases hplayer : player = first
          · subst player
            have hpure := Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
              (root first) hownerZero
            simpa [quittingAllContinueRoot] using hpure
          · simpa [quittingAllContinueRoot] using
              (hpureOpponent player hplayer)
        apply hnashAll
        simpa [hroot] using hnash
      have hownerTight :=
        quittingRoot_singleton_eq_of_face_of_quit_pos
          reward pair.1 root hnash first (hface first hfirst) hownerQuit
      have houtsiderEndpoint : ∀ player, player ≠ first →
          quittingRootQuitPayoff reward pair.1 root player ≤
            quittingRootContinuePayoff reward pair.1 root player := by
        intro player hne
        have hendpoint : IsεQuittingRootEndpointNash reward pair.1 0 root :=
          (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
            reward pair.1 root).mpr hnash
        have hdiff :=
          quittingRootEndpointDifference_nonpos_of_quitProbability_eq_zero
            reward pair.1 root player hendpoint (hzeroOpponent player hne)
        simpa [quittingRootEndpointDifference] using hdiff
      exact Or.inr ⟨first, other, hfirst, hunique, hotherNe, hotherGain,
        hownerQuit, hownerTight, hpureOpponent, houtsiderEndpoint⟩

/-- **Minimum-stratum alternative.**  Carrier membership and minimum total
debt route to the face-stratum alternative through coordinatewise prefix
equality. -/
theorem quittingTerminalSemantic_minimum_stratum_alternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (first : ι) (hfirst : 0 < quittingTerminalSemanticDebt pair first) :
    (IsεQuittingRootNash reward pair.1 0
          (quittingAllContinueRoot : ι → PMF Bool) ∧
        quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair =
          pair) ∨
      ∃ owner other,
        0 < quittingTerminalSemanticDebt pair owner ∧
        (∀ player, 0 < quittingTerminalSemanticDebt pair player →
          player = owner) ∧
        other ≠ owner ∧
        pair.1 other < reward (quittingSingletonTerminal other) other ∧
        0 < (root owner true).toReal ∧
        reward (quittingSingletonTerminal owner) owner = pair.1 owner ∧
        (∀ player, player ≠ owner → root player = PMF.pure false) ∧
        ∀ player, player ≠ owner →
          quittingRootQuitPayoff reward pair.1 root player ≤
            quittingRootContinuePayoff reward pair.1 root player := by
  have hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  have hface : ∀ who, 0 < quittingTerminalSemanticDebt pair who →
      quittingRootOpponentContinueMass root who = 1 ∧
        quittingRootExercisePremium reward pair.1 root who = 0 := by
    intro who hpositive
    exact quittingTerminalSemantic_minimum_positiveDebt_face
      reward pair root hpair hmin hnash who hpositive
  exact quittingTerminalSemantic_face_stratum_alternative
    reward pair root hdebt hnash hface first hfirst

/-- In the absence of a uniform payoff, a minimum-total-debt semantic pair
has a positive debt coordinate and every exact Nash root lies on that
coordinate's unit-survival, zero-premium face. -/
theorem exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool),
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      IsεQuittingRootNash reward pair.1 0 root ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      (∃ who, 0 < quittingTerminalSemanticDebt pair who) ∧
      ∀ who, 0 < quittingTerminalSemanticDebt pair who →
        quittingRootOpponentContinueMass root who = 1 ∧
          quittingRootExercisePremium reward pair.1 root who = 0 := by
  obtain ⟨pair, hpair, hmin⟩ :=
    exists_minimum_quittingTerminalSemanticDebtSum reward
  obtain ⟨simplexRoot, hnash⟩ :=
    exists_isZeroQuittingRootEndpointNash_simplex reward pair.1
  let root := quittingRootOfSimplex simplexRoot
  have hnash' : IsεQuittingRootNash reward pair.1 0 root :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward pair.1 0 root).mp hnash
  have hfloor : 0 < quittingTerminalExploitabilityInf reward :=
    quittingTerminalExploitabilityInf_pos_of_no_uniformEquilibriumPayoff
      reward hno
  have hpositive : ∃ who, 0 < quittingTerminalSemanticDebt pair who := by
    by_contra hnot
    have hnot' : ∀ who, quittingTerminalSemanticDebt pair who ≤ 0 := by
      intro who
      exact le_of_not_gt fun hpositive => hnot ⟨who, hpositive⟩
    have hzero : ∀ who, quittingTerminalSemanticDebt pair who = 0 := by
      intro who
      exact le_antisymm (hnot' who)
        (quittingTerminalSemanticDebt_nonneg_of_mem_carrier
          reward hpair who)
    have hexploitZero : quittingTerminalSemanticExploitability pair = 0 := by
      unfold quittingTerminalSemanticExploitability finitePlayerMax
      simp [hzero]
    have hcarrierFloor :=
      quittingTerminalExploitabilityInf_le_semanticCarrier reward hpair
    rw [hexploitZero] at hcarrierFloor
    linarith
  refine ⟨pair, root, hpair, hnash', hmin, hpositive, ?_⟩
  intro who hwho
  exact quittingTerminalSemantic_minimum_positiveDebt_face
    reward pair root hpair hmin hnash' who hwho

end GameTheory
