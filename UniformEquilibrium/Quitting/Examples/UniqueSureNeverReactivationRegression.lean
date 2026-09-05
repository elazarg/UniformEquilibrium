/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.BestResponse
import UniformEquilibrium.Quitting.Stationary.CompleteBehavioralCap
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailProfileAdapter
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass
import UniformEquilibrium.Quitting.Root.OpponentCoalitionPayoff
import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport
import UniformEquilibrium.Quitting.Paths.SureExitSet
import MathUE.ProbabilityMassFunction.Simplex

/-! # A unique-sure Never repair can reactivate an outsider

This four-player regression records the boundary of the unique-sure reset:
the sure owner's profitable Never repair need not leave a terminal Nash
profile.  After the repair, an outsider has a literal profitable Quit-now
deviation.
-/

noncomputable section

namespace GameTheory.UniqueSureNeverReactivationRegression

open GameTheory Math.Probability Math.ProbabilityMassFunction

abbrev Player := Fin 4

def owner : Player := 0
def first : Player := 1
def second : Player := 2

/-- The sparse reward table from the unique-sure reset boundary example. -/
def reward (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who =>
    if who = owner then
      if owner ∈ terminal.1 then
        if terminal.1 = {owner} then 0 else 4 / 3
      else 6 / 5
    else if who = first then
      if terminal.1 = {first} then 1 / 2
      else if terminal.1 = {owner} ∨ terminal.1 = {owner, first, second} then 1
      else 0
    else if who = second then
      if terminal.1 = {owner, first} ∨ terminal.1 = {owner, second} then 1 else 0
    else 0

/-- The root has one sure owner, two fair matching-pennies outsiders, and a
dummy player who always Continues. -/
def root : Player → PMF Bool := fun who =>
  if who = owner then PMF.pure true
  else if who = first ∨ who = second then
    bernoulliBool (1 / 2) (by norm_num) (by norm_num)
  else PMF.pure false

def repairedRoot : Player → PMF Bool :=
  Function.update root owner (PMF.pure false)

/-- A concrete continuation payoff against which the displayed unique-sure
root is an exact product Nash root. -/
def exactTail : Payoff Player := fun _ ↦ 0

private theorem root_active : IsQuittingActiveRoot {owner, first, second} root := by
  intro who hwho
  fin_cases who <;> simp_all [owner, first, second, root]

private theorem repairedRoot_active :
    IsQuittingActiveRoot {first, second} repairedRoot := by
  intro who hwho
  fin_cases who <;> simp_all [owner, first, second, repairedRoot, root]

/-- The displayed source root has exactly one sure quitter. -/
theorem root_uniqueSureOwner :
    root owner = PMF.pure true ∧
      ∀ who, who ≠ owner → root who ≠ PMF.pure true := by
  constructor
  · simp [root, owner]
  · intro who hne heq
    have htrue := congrArg (fun p : PMF Bool => (p true).toReal) heq
    by_cases hfair : who = first ∨ who = second
    · simp [root, hne, hfair, bernoulliBool] at htrue
    · simp [root, hne, hfair] at htrue

private theorem root_endpointDifference_exactTail (who : Player) :
    quittingRootEndpointDifference reward exactTail root who =
      if who = owner then 1 / 10 else 0 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4, Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp [quittingRootPayoff, reward, root, exactTail, owner, first, second,
      expect_eq_sum] <;>
    norm_num +decide

/-- The regression's displayed unique-sure root is compatible with an exact
root input: the zero continuation payoff makes the owner strictly prefer Quit
and leaves every outsider indifferent. -/
theorem root_isZeroNash_exactTail :
    IsεQuittingRootNash reward exactTail 0 root := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  rw [root_endpointDifference_exactTail]
  fin_cases who <;> simp [root, owner, first, second]

private theorem coalitionMass_eq_product_choice
    (hazard : Player → ℝ) (coalition : Finset Player) :
    Math.PMFProduct.coalitionMass hazard coalition =
      ∏ player, if player ∈ coalition then hazard player else 1 - hazard player := by
  rw [Math.PMFProduct.coalitionMass]
  have hcomplement :
      (∏ player, if player ∈ coalition then 1 else 1 - hazard player) =
        ∏ player ∈ coalitionᶜ, (1 - hazard player) := by
    calc
      (∏ player, if player ∈ coalition then 1 else 1 - hazard player) =
          ∏ player, if player ∈ coalitionᶜ then 1 - hazard player else 1 := by
        apply Finset.prod_congr rfl
        intro player _
        by_cases hmem : player ∈ coalition <;> simp [hmem]
      _ = ∏ player ∈ coalitionᶜ, (1 - hazard player) :=
        Fintype.prod_ite_mem coalitionᶜ fun player => 1 - hazard player
  have hcoalition :
      (∏ player, if player ∈ coalition then hazard player else 1) =
        ∏ player ∈ coalition, hazard player :=
    Fintype.prod_ite_mem coalition hazard
  rw [← hcoalition, ← hcomplement, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro player _
  by_cases hmem : player ∈ coalition <;> simp [hmem]

/-- The original unique-sure stationary source pays the owner `1`. -/
theorem owner_source_payoff :
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) owner = 1 := by
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
  · unfold quittingRootAbsorbingContribution
    rw [quittingRootExpectedPayoff_eq_sum_activePowerset reward 0
      {owner, first, second} root root_active owner]
    have hpowerset : ({owner, first, second} : Finset Player).powerset =
        {∅, {owner}, {first}, {second}, {owner, first}, {owner, second},
          {first, second}, {owner, first, second}} := by decide
    rw [hpowerset]
    simp_rw [coalitionMass_eq_product_choice]
    simp [Fin.prod_univ_four, root, owner, first, second,
      hazardOfRoot, quittingStageCoalitionPayoff,
      quittingStationaryContinueMass_eq_prod_continueProbability,
      Fin.prod_univ_four, reward]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [reward, owner]
    norm_num +decide
  · rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    rw [Fin.prod_univ_four]
    simp [root, owner, first, second]

private theorem source_payoff (who : Player) :
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) who =
      if who = owner then 1 else if who = first ∨ who = second then 1 / 2 else 0 := by
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
  · unfold quittingRootAbsorbingContribution
    rw [quittingRootExpectedPayoff_eq_sum_activePowerset reward 0
      {owner, first, second} root root_active who]
    have hpowerset : ({owner, first, second} : Finset Player).powerset =
        {∅, {owner}, {first}, {second}, {owner, first}, {owner, second},
          {first, second}, {owner, first, second}} := by decide
    rw [hpowerset]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    simp_rw [coalitionMass_eq_product_choice]
    fin_cases who <;>
      simp [Fin.prod_univ_four, root, owner, first, second, hazardOfRoot,
        quittingStageCoalitionPayoff,
        quittingStationaryContinueMass_eq_prod_continueProbability, reward] <;>
      norm_num +decide
  · rw [quittingStationaryContinueMass_eq_prod_continueProbability,
      Fin.prod_univ_four]
    simp [root, owner, first, second]

/-- After the owner switches to Never, its payoff is `6/5`. -/
theorem owner_repaired_payoff :
    quittingTerminalPayoff reward
      (quittingStationaryProfile reward repairedRoot) owner = 6 / 5 := by
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
  · unfold quittingRootAbsorbingContribution
    rw [quittingRootExpectedPayoff_pair_active reward 0 repairedRoot first second
      owner (by decide) repairedRoot_active]
    simp [repairedRoot, root, owner, first, second, hazardOfRoot]
    simp [quittingStationaryContinueMass_eq_prod_continueProbability,
      Fin.prod_univ_four, root, owner, first, second]
    simp [reward, owner]
    norm_num +decide
  · rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    rw [Fin.prod_univ_four]
    simp [repairedRoot, root, owner, first, second]
    norm_num

theorem owner_quitNow_source_payoff :
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) owner
          (quittingPureTimeBehaviorStrategy reward owner (some 0))) owner = 1 := by
  rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
  unfold quittingStationaryFixedOpponentsQuitValue quittingFixedOpponentsQuitValue
  rw [quittingProfileLiveRoot_stationary]
  have hupdate : Function.update root owner (PMF.pure true) = root := by
    funext who
    by_cases hwho : who = owner
    · subst who
      simp [root, owner]
    · simp [Function.update_of_ne hwho]
  rw [hupdate]
  have hmass : quittingStationaryContinueMass root = 0 := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability,
      Fin.prod_univ_four]
    simp [root, owner, first, second]
  have h := one_sub_continueMass_mul_quittingTerminalPayoff_stationary
    reward root owner
  rw [hmass, owner_source_payoff] at h
  simpa [quittingRootAbsorbingContribution] using h.symm

theorem owner_never_source_payoff :
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) owner
          (quittingPureTimeBehaviorStrategy reward owner none)) owner = 6 / 5 := by
  rw [quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
    update_quittingStationaryProfile_alwaysContinue]
  exact owner_repaired_payoff

/-- Literal Never is the sure owner's exact complete behavioral cap. -/
theorem owner_completeCap_eq_six_fifths :
    quittingContinuationBestResponseValue reward
      (quittingStationaryProfile reward root) owner = 6 / 5 := by
  have hcontracts :
      quittingStationaryFixedOpponentsContinueMass root owner < 1 := by
    unfold quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueMass
    change quittingStationaryContinueMass repairedRoot < 1
    rw [quittingStationaryContinueMass_eq_prod_continueProbability,
      Fin.prod_univ_four]
    simp [repairedRoot, root, owner, first, second]
    norm_num
  rw [quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never
    reward root owner hcontracts, owner_quitNow_source_payoff,
    owner_never_source_payoff]
  norm_num

private def firstNeverRoot : Player → PMF Bool :=
  Function.update root first (PMF.pure false)

private theorem firstNeverRoot_active :
    IsQuittingActiveRoot {owner, second} firstNeverRoot := by
  intro who hwho
  fin_cases who <;>
    simp_all [firstNeverRoot, root, owner, first, second]

theorem first_never_source_payoff :
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) first
          (quittingPureTimeBehaviorStrategy reward first none)) first = 1 / 2 := by
  rw [quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
    update_quittingStationaryProfile_alwaysContinue]
  change quittingTerminalPayoff reward
    (quittingStationaryProfile reward firstNeverRoot) first = 1 / 2
  have hmass : quittingStationaryContinueMass firstNeverRoot = 0 := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability,
      Fin.prod_univ_four]
    simp [firstNeverRoot, root, owner, first, second]
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
  · unfold quittingRootAbsorbingContribution
    rw [quittingRootExpectedPayoff_pair_active reward 0 firstNeverRoot owner second
      first (by decide) firstNeverRoot_active]
    simp [firstNeverRoot, root, reward, owner, first, second, hazardOfRoot]
    rw [show Function.update root (1 : Player) (PMF.pure false) =
      firstNeverRoot from rfl]
    rw [hmass]
    norm_num +decide
  · linarith

theorem first_quitNow_source_payoff :
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) first
          (quittingPureTimeBehaviorStrategy reward first (some 0))) first = 1 / 2 := by
  rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
  unfold quittingStationaryFixedOpponentsQuitValue quittingFixedOpponentsQuitValue
  rw [quittingProfileLiveRoot_stationary]
  unfold quittingRootAbsorbingContribution
  let quitRoot := Function.update root first (PMF.pure true)
  have hactive : IsQuittingActiveRoot {owner, first, second} quitRoot := by
    intro who hwho
    fin_cases who <;> simp_all [quitRoot, root, owner, first, second]
  rw [quittingRootExpectedPayoff_eq_sum_activePowerset reward 0
    {owner, first, second} quitRoot hactive first]
  have hpowerset : ({owner, first, second} : Finset Player).powerset =
      {∅, {owner}, {first}, {second}, {owner, first}, {owner, second},
        {first, second}, {owner, first, second}} := by decide
  rw [hpowerset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp_rw [coalitionMass_eq_product_choice]
  simp [Fin.prod_univ_four, quitRoot, root, reward, owner, first, second,
    hazardOfRoot, quittingStageCoalitionPayoff]
  norm_num +decide

theorem first_completeCap_eq_sourcePayoff :
    quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward root) first =
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) first := by
  have hcontracts :
      quittingStationaryFixedOpponentsContinueMass root first < 1 := by
    unfold quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueMass
    rw [quittingStationaryContinueMass_eq_prod_continueProbability,
      Fin.prod_univ_four]
    simp [root, owner, first, second]
  rw [quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never
    reward root first hcontracts, first_quitNow_source_payoff,
    first_never_source_payoff, source_payoff]
  norm_num [owner, first, second]

private def secondNeverRoot : Player → PMF Bool :=
  Function.update root second (PMF.pure false)

private theorem secondNeverRoot_active :
    IsQuittingActiveRoot {owner, first} secondNeverRoot := by
  intro who hwho
  fin_cases who <;>
    simp_all [secondNeverRoot, root, owner, first, second]

theorem second_never_source_payoff :
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) second
          (quittingPureTimeBehaviorStrategy reward second none)) second = 1 / 2 := by
  rw [quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
    update_quittingStationaryProfile_alwaysContinue]
  change quittingTerminalPayoff reward
    (quittingStationaryProfile reward secondNeverRoot) second = 1 / 2
  have hmass : quittingStationaryContinueMass secondNeverRoot = 0 := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability,
      Fin.prod_univ_four]
    simp [secondNeverRoot, root, owner, first, second]
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
  · unfold quittingRootAbsorbingContribution
    rw [quittingRootExpectedPayoff_pair_active reward 0 secondNeverRoot owner first
      second (by decide) secondNeverRoot_active]
    simp [secondNeverRoot, root, reward, owner, first, second, hazardOfRoot]
    rw [show Function.update root (2 : Player) (PMF.pure false) =
      secondNeverRoot from rfl, hmass]
    norm_num +decide
  · linarith

theorem second_quitNow_source_payoff :
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) second
          (quittingPureTimeBehaviorStrategy reward second (some 0))) second = 1 / 2 := by
  rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
  unfold quittingStationaryFixedOpponentsQuitValue quittingFixedOpponentsQuitValue
  rw [quittingProfileLiveRoot_stationary]
  unfold quittingRootAbsorbingContribution
  let quitRoot := Function.update root second (PMF.pure true)
  have hactive : IsQuittingActiveRoot {owner, first, second} quitRoot := by
    intro who hwho
    fin_cases who <;> simp_all [quitRoot, root, owner, first, second]
  rw [quittingRootExpectedPayoff_eq_sum_activePowerset reward 0
    {owner, first, second} quitRoot hactive second]
  have hpowerset : ({owner, first, second} : Finset Player).powerset =
      {∅, {owner}, {first}, {second}, {owner, first}, {owner, second},
        {first, second}, {owner, first, second}} := by decide
  rw [hpowerset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp_rw [coalitionMass_eq_product_choice]
  simp [Fin.prod_univ_four, quitRoot, root, reward, owner, first, second,
    hazardOfRoot, quittingStageCoalitionPayoff]
  norm_num +decide

theorem second_completeCap_eq_sourcePayoff :
    quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward root) second =
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) second := by
  have hcontracts :
      quittingStationaryFixedOpponentsContinueMass root second < 1 := by
    unfold quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueMass
    rw [quittingStationaryContinueMass_eq_prod_continueProbability,
      Fin.prod_univ_four]
    simp [root, owner, first, second]
  rw [quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never
    reward root second hcontracts, second_quitNow_source_payoff,
    second_never_source_payoff, source_payoff]
  norm_num [owner, first, second]
  simp

def dummy : Player := 3

theorem dummy_never_source_payoff :
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) dummy
          (quittingPureTimeBehaviorStrategy reward dummy none)) dummy = 0 := by
  rw [quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
    update_quittingStationaryProfile_alwaysContinue]
  have hupdate : Function.update root dummy (PMF.pure false) = root := by
    funext who
    by_cases hwho : who = dummy
    · subst who
      simp [root, dummy, owner, first, second]
    · simp [Function.update_of_ne hwho]
  rw [hupdate, source_payoff]
  have hd0 : dummy ≠ owner := by decide
  have hd1 : dummy ≠ first := by decide
  have hd2 : dummy ≠ second := by decide
  simp [hd0, hd1, hd2]

theorem dummy_quitNow_source_payoff :
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) dummy
          (quittingPureTimeBehaviorStrategy reward dummy (some 0))) dummy = 0 := by
  rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
  unfold quittingStationaryFixedOpponentsQuitValue quittingFixedOpponentsQuitValue
  rw [quittingProfileLiveRoot_stationary]
  unfold quittingRootAbsorbingContribution
  let quitRoot := Function.update root dummy (PMF.pure true)
  have hactive : IsQuittingActiveRoot {owner, first, second, dummy} quitRoot := by
    intro who hwho
    fin_cases who <;> simp_all [dummy, owner, first, second]
  rw [quittingRootExpectedPayoff_eq_sum_activePowerset reward 0
    {owner, first, second, dummy} quitRoot hactive dummy]
  apply Finset.sum_eq_zero
  intro coalition _
  by_cases hnonempty : coalition.Nonempty
  · simp [quittingStageCoalitionPayoff, hnonempty, reward, dummy, owner,
      first, second]
  · simp [quittingStageCoalitionPayoff, hnonempty]

theorem dummy_completeCap_eq_sourcePayoff :
    quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward root) dummy =
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) dummy := by
  have hcontracts :
      quittingStationaryFixedOpponentsContinueMass root dummy < 1 := by
    unfold quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueMass
    rw [quittingStationaryContinueMass_eq_prod_continueProbability,
      Fin.prod_univ_four]
    simp [root, dummy, owner, first, second]
  rw [quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never
    reward root dummy hcontracts, dummy_quitNow_source_payoff,
    dummy_never_source_payoff, source_payoff]
  have hd0 : dummy ≠ owner := by decide
  have hd1 : dummy ≠ first := by decide
  have hd2 : dummy ≠ second := by decide
  simp [hd0, hd1, hd2]

/-- Every nonowner coordinate has zero complete behavioral debt at the
original stationary source. -/
theorem outsiders_completeCap_eq_sourcePayoff
    (who : Player) (hne : who ≠ owner) :
    quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward root) who =
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who := by
  fin_cases who
  · exact (hne rfl).elim
  · exact first_completeCap_eq_sourcePayoff
  · exact second_completeCap_eq_sourcePayoff
  · exact dummy_completeCap_eq_sourcePayoff

/-- The original source has exactly one debtor: the unique sure owner, whose
complete debt is `1/5`; every outsider debt is zero. -/
theorem originalSource_uniqueDebtor :
    quittingTerminalDeviationDebt reward
        (quittingStationaryProfile reward root) owner = 1 / 5 ∧
      ∀ who, who ≠ owner → quittingTerminalDeviationDebt reward
        (quittingStationaryProfile reward root) who = 0 := by
  constructor
  · unfold quittingTerminalDeviationDebt
    rw [owner_completeCap_eq_six_fifths, owner_source_payoff]
    norm_num
  · intro who hne
    unfold quittingTerminalDeviationDebt
    rw [outsiders_completeCap_eq_sourcePayoff who hne]
    ring

/-- The repaired stationary profile pays the first outsider `1/6`. -/
theorem first_repaired_payoff :
    quittingTerminalPayoff reward
      (quittingStationaryProfile reward repairedRoot) first = 1 / 6 := by
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
  · unfold quittingRootAbsorbingContribution
    rw [quittingRootExpectedPayoff_pair_active reward 0 repairedRoot first second
      first (by decide) repairedRoot_active]
    simp [repairedRoot, root, owner, first, second, hazardOfRoot]
    simp [quittingStationaryContinueMass_eq_prod_continueProbability,
      Fin.prod_univ_four, root, owner, first, second]
    simp [reward, owner, first, second]
    norm_num +decide
  · rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    rw [Fin.prod_univ_four]
    simp [repairedRoot, root, owner, first, second]
    norm_num

/-- Immediate Quit against the repaired opponents pays the first outsider
`1/4`. -/
theorem first_quitNow_repaired_payoff :
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward repairedRoot) first
          (quittingPureTimeBehaviorStrategy reward first (some 0))) first = 1 / 4 := by
  rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
  unfold quittingStationaryFixedOpponentsQuitValue quittingFixedOpponentsQuitValue
  rw [quittingProfileLiveRoot_stationary]
  unfold quittingRootAbsorbingContribution
  rw [quittingRootExpectedPayoff_pair_active reward 0
    (Function.update repairedRoot first (PMF.pure true)) first second first
    (by decide)]
  · simp [reward, repairedRoot, root, owner, first, second, hazardOfRoot]
    norm_num +decide
  · intro who hwho
    fin_cases who <;>
      simp_all [owner, first, second, repairedRoot, root]

/-- The owner's Never repair gains `1/5`, but its child immediately exposes
the first outsider's strict `1/12` Quit-now gain. -/
theorem ownerNever_gain_and_outsider_reactivation :
    quittingTerminalPayoff reward
          (quittingStationaryProfile reward repairedRoot) owner -
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) owner = 1 / 5 ∧
      quittingTerminalPayoff reward
          (Function.update (quittingStationaryProfile reward repairedRoot) first
            (quittingPureTimeBehaviorStrategy reward first (some 0))) first -
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward repairedRoot) first = 1 / 12 := by
  rw [owner_source_payoff, owner_repaired_payoff, first_repaired_payoff,
    first_quitNow_repaired_payoff]
  norm_num

/-- In particular, the stationary Never child is not terminally stable: the
first outsider has a strictly profitable unrestricted behavioral deviation. -/
theorem repairedProfile_has_profitable_outsiderDeviation :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward repairedRoot) first <
      quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward repairedRoot) first
          (quittingPureTimeBehaviorStrategy reward first (some 0))) first := by
  linarith [ownerNever_gain_and_outsider_reactivation.2]

end GameTheory.UniqueSureNeverReactivationRegression
