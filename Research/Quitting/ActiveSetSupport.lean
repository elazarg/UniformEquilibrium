/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanClockReduction

/-!
# Quitting roots with a prescribed active set

This experiment formalizes the first reduction for a quitting game in which
only a publicly specified finite set of players may move at a stage.  Inactive
players are forced to Continue.  Consequently every realized quitter
coalition is contained in the active set, and the full Boolean-cube payoff sum
truncates exactly to the active-set powerset.

The file is an isolated proof probe.  Production modules do not import it.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Force every player outside `active` to Continue. -/
def quittingActiveRoot (active : Finset ι) (root : ι → PMF Bool) : ι → PMF Bool :=
  fun i => if i ∈ active then root i else PMF.pure false

/-- A root is supported by `active` when every inactive player surely
continues. -/
def IsQuittingActiveRoot (active : Finset ι) (root : ι → PMF Bool) : Prop :=
  ∀ i, i ∉ active → root i = PMF.pure false

omit [Fintype ι] in
theorem isQuittingActiveRoot_quittingActiveRoot
    (active : Finset ι) (root : ι → PMF Bool) :
    IsQuittingActiveRoot active (quittingActiveRoot active root) := by
  intro i hi
  simp [quittingActiveRoot, hi]

omit [Fintype ι] in
@[simp] theorem quittingActiveRoot_apply_of_mem
    (active : Finset ι) (root : ι → PMF Bool) (i : ι) (hi : i ∈ active) :
    quittingActiveRoot active root i = root i := by
  simp [quittingActiveRoot, hi]

omit [Fintype ι] in
@[simp] theorem quittingActiveRoot_apply_of_not_mem
    (active : Finset ι) (root : ι → PMF Bool) (i : ι) (hi : i ∉ active) :
    quittingActiveRoot active root i = PMF.pure false := by
  simp [quittingActiveRoot, hi]

omit [Fintype ι] in
/-- The hazard vector of an active root is the original hazard on the active
set and zero elsewhere. -/
theorem hazardOfRoot_quittingActiveRoot
    (active : Finset ι) (root : ι → PMF Bool) :
    hazardOfRoot (quittingActiveRoot active root) =
      fun i => if i ∈ active then hazardOfRoot root i else 0 := by
  funext i
  by_cases hi : i ∈ active
  · simp [hazardOfRoot, hi]
  · simp [hazardOfRoot, hi]

omit [Fintype ι] [DecidableEq ι] in
/-- Inactive players have zero quitting hazard. -/
theorem hazardOfRoot_eq_zero_of_isQuittingActiveRoot
    {active : Finset ι} {root : ι → PMF Bool}
    (hroot : IsQuittingActiveRoot active root) {i : ι} (hi : i ∉ active) :
    hazardOfRoot root i = 0 := by
  unfold hazardOfRoot
  rw [hroot i hi]
  simp

/-- An exact coalition outside the active set has zero product mass. -/
theorem coalitionMass_eq_zero_of_not_subset_active
    {active : Finset ι} {root : ι → PMF Bool}
    (hroot : IsQuittingActiveRoot active root) {coalition : Finset ι}
    (hcoalition : ¬ coalition ⊆ active) :
    coalitionMass (hazardOfRoot root) coalition = 0 := by
  rw [Finset.not_subset] at hcoalition
  obtain ⟨i, hiCoalition, hiActive⟩ := hcoalition
  unfold coalitionMass
  have hzero : hazardOfRoot root i = 0 :=
    hazardOfRoot_eq_zero_of_isQuittingActiveRoot hroot hiActive
  have hprod : ∏ j ∈ coalition, hazardOfRoot root j = 0 := by
    exact Finset.prod_eq_zero hiCoalition hzero
  rw [hprod, zero_mul]

/-- **Active-powerset truncation.** The one-stage payoff expectation reads
only quitter coalitions contained in `active`. -/
theorem quittingRootExpectedPayoff_eq_sum_activePowerset
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι) (root : ι → PMF Bool)
    (hroot : IsQuittingActiveRoot active root) (who : ι) :
    quittingRootExpectedPayoff reward continuation root who =
      ∑ S ∈ active.powerset,
        coalitionMass (hazardOfRoot root) S *
          quittingStageCoalitionPayoff reward continuation S who := by
  rw [quittingRootExpectedPayoff_eq_sum_coalitionMass]
  symm
  apply Finset.sum_subset (Finset.subset_univ active.powerset)
  intro S _ hS
  have hnot : ¬ S ⊆ active := by
    simpa using hS
  rw [coalitionMass_eq_zero_of_not_subset_active hroot hnot, zero_mul]

/-- A root supported on at most `K` active players assigns zero mass to every
coalition of cardinality larger than `K`. -/
theorem coalitionMass_eq_zero_of_active_card_le
    {active : Finset ι} {root : ι → PMF Bool}
    (hroot : IsQuittingActiveRoot active root) {K : ℕ}
    (hactive : active.card ≤ K) {coalition : Finset ι}
    (hlarge : K < coalition.card) :
    coalitionMass (hazardOfRoot root) coalition = 0 := by
  apply coalitionMass_eq_zero_of_not_subset_active hroot
  intro hsubset
  have hcard := Finset.card_le_card hsubset
  omega

/-! ## Phase 2: one active player -/

omit [DecidableEq ι] in
/-- Universal continuation under a singleton-active root has mass exactly
`1 - x_owner`. -/
theorem continueMass_hazardOfRoot_eq_one_sub_of_singleton_active
    {root : ι → PMF Bool} {owner : ι}
    (hroot : IsQuittingActiveRoot {owner} root) :
    continueMass (hazardOfRoot root) = 1 - hazardOfRoot root owner := by
  classical
  unfold continueMass
  have hsplit := Finset.mul_prod_erase (Finset.univ : Finset ι)
    (fun i => 1 - hazardOfRoot root i) (Finset.mem_univ owner)
  have hrest :
      (∏ i ∈ (Finset.univ : Finset ι).erase owner,
        (1 - hazardOfRoot root i)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hine : i ≠ owner := Finset.ne_of_mem_erase hi
    have hiActive : i ∉ ({owner} : Finset ι) := by simpa using hine
    rw [hazardOfRoot_eq_zero_of_isQuittingActiveRoot hroot hiActive]
    ring
  rw [← hsplit, hrest, mul_one]

/-- The singleton quitter event has exactly the owner's hazard mass. -/
theorem coalitionMass_singleton_of_singleton_active
    {root : ι → PMF Bool} {owner : ι}
    (hroot : IsQuittingActiveRoot {owner} root) :
    coalitionMass (hazardOfRoot root) {owner} = hazardOfRoot root owner := by
  classical
  unfold coalitionMass
  have houtside :
      (∏ i ∈ ({owner} : Finset ι)ᶜ, (1 - hazardOfRoot root i)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hiActive : i ∉ ({owner} : Finset ι) := Finset.mem_compl.mp hi
    rw [hazardOfRoot_eq_zero_of_isQuittingActiveRoot hroot hiActive]
    ring
  rw [Finset.prod_singleton, houtside, mul_one]

omit [DecidableEq ι] in
/-- **Singleton affine formula.** A one-active-player quitting stage is the
affine interpolation between continuation and the singleton terminal reward.
-/
theorem quittingRootExpectedPayoff_singleton_active
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool) (owner who : ι)
    (hroot : IsQuittingActiveRoot {owner} root) :
    quittingRootExpectedPayoff reward continuation root who =
      (1 - hazardOfRoot root owner) * continuation who +
        hazardOfRoot root owner * reward ⟨{owner}, Finset.singleton_nonempty owner⟩ who := by
  classical
  rw [quittingRootExpectedPayoff_eq_sum_activePowerset
    reward continuation {owner} root hroot who]
  rw [show ({owner} : Finset ι).powerset = {∅, {owner}} by ext S; simp]
  rw [Finset.sum_insert]
  · simp only [Finset.sum_singleton]
    rw [coalitionMass_empty,
      continueMass_hazardOfRoot_eq_one_sub_of_singleton_active hroot,
      coalitionMass_singleton_of_singleton_active hroot]
    simp [quittingStageCoalitionPayoff]
  · simp

omit [DecidableEq ι] in
/-- The singleton formula in direct affine-vector form. -/
theorem quittingRootExpectedPayoff_singleton_active_affine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool) (owner who : ι)
    (hroot : IsQuittingActiveRoot {owner} root) :
    quittingRootExpectedPayoff reward continuation root who =
      continuation who + hazardOfRoot root owner *
        (reward ⟨{owner}, Finset.singleton_nonempty owner⟩ who - continuation who) := by
  classical
  rw [quittingRootExpectedPayoff_singleton_active
    reward continuation root owner who hroot]
  ring

/-! ## Phase 3: two active players -/

/-- On a supported coalition, the exact-coalition mass may be computed only
over the active set; every inactive Continue factor is one. -/
theorem coalitionMass_eq_activeProducts
    {active : Finset ι} {root : ι → PMF Bool}
    (hroot : IsQuittingActiveRoot active root) {coalition : Finset ι}
    (hcoalition : coalition ⊆ active) :
    coalitionMass (hazardOfRoot root) coalition =
      (∏ i ∈ coalition, hazardOfRoot root i) *
        ∏ i ∈ active \ coalition, (1 - hazardOfRoot root i) := by
  classical
  unfold coalitionMass
  have hcompl : coalitionᶜ = (active \ coalition) ∪ activeᶜ := by
    ext i
    simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hi
      by_cases hia : i ∈ active
      · exact Or.inl ⟨hia, hi⟩
      · exact Or.inr hia
    · rintro (⟨_, hi⟩ | hi)
      · exact hi
      · intro hic
        exact hi (hcoalition hic)
  have hdisjoint : Disjoint (active \ coalition) activeᶜ := by
    exact Finset.disjoint_left.mpr fun i hiDiff hiCompl =>
      (Finset.mem_compl.mp hiCompl) (Finset.mem_sdiff.mp hiDiff).1
  have houtside :
      (∏ i ∈ activeᶜ, (1 - hazardOfRoot root i)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hiActive : i ∉ active := Finset.mem_compl.mp hi
    rw [hazardOfRoot_eq_zero_of_isQuittingActiveRoot hroot hiActive]
    ring
  rw [hcompl, Finset.prod_union hdisjoint, houtside, mul_one]

/-- Empty-coalition mass for a two-active-player root. -/
theorem coalitionMass_empty_of_pair_active
    {root : ι → PMF Bool} {first second : ι} (hne : first ≠ second)
    (hroot : IsQuittingActiveRoot {first, second} root) :
    coalitionMass (hazardOfRoot root) ∅ =
      (1 - hazardOfRoot root first) * (1 - hazardOfRoot root second) := by
  rw [coalitionMass_eq_activeProducts hroot (Finset.empty_subset _)]
  simp [hne]

/-- First singleton mass for a two-active-player root. -/
theorem coalitionMass_first_of_pair_active
    {root : ι → PMF Bool} {first second : ι} (hne : first ≠ second)
    (hroot : IsQuittingActiveRoot {first, second} root) :
    coalitionMass (hazardOfRoot root) {first} =
      hazardOfRoot root first * (1 - hazardOfRoot root second) := by
  rw [coalitionMass_eq_activeProducts hroot (by simp)]
  have hdiff : ({first, second} : Finset ι) \ {first} = {second} := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hi | hi, hnot⟩
      · exact (hnot hi).elim
      · exact hi
    · intro hi
      refine ⟨Or.inr hi, ?_⟩
      intro hifirst
      exact hne (hifirst.symm.trans hi)
  rw [hdiff]
  simp

/-- Second singleton mass for a two-active-player root. -/
theorem coalitionMass_second_of_pair_active
    {root : ι → PMF Bool} {first second : ι} (hne : first ≠ second)
    (hroot : IsQuittingActiveRoot {first, second} root) :
    coalitionMass (hazardOfRoot root) {second} =
      (1 - hazardOfRoot root first) * hazardOfRoot root second := by
  rw [coalitionMass_eq_activeProducts hroot (by simp)]
  have hdiff : ({first, second} : Finset ι) \ {second} = {first} := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hi | hi, hnot⟩
      · exact hi
      · exact (hnot hi).elim
    · intro hi
      refine ⟨Or.inl hi, ?_⟩
      intro hisecond
      exact hne (hi.symm.trans hisecond)
  rw [hdiff]
  simp
  ring

/-- Pair-collision mass for a two-active-player root. -/
theorem coalitionMass_pair_of_pair_active
    {root : ι → PMF Bool} {first second : ι} (hne : first ≠ second)
    (hroot : IsQuittingActiveRoot {first, second} root) :
    coalitionMass (hazardOfRoot root) {first, second} =
      hazardOfRoot root first * hazardOfRoot root second := by
  rw [coalitionMass_eq_activeProducts hroot (by simp)]
  simp [hne]

/-- **Pair collision decomposition.** The only departure from the two
singleton affine branches is the quadratic joint-quitting event. -/
theorem quittingRootExpectedPayoff_pair_active
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (first second who : ι) (hne : first ≠ second)
    (hroot : IsQuittingActiveRoot {first, second} root) :
    quittingRootExpectedPayoff reward continuation root who =
      (1 - hazardOfRoot root first) * (1 - hazardOfRoot root second) * continuation who +
      hazardOfRoot root first * (1 - hazardOfRoot root second) *
        reward ⟨{first}, Finset.singleton_nonempty first⟩ who +
      (1 - hazardOfRoot root first) * hazardOfRoot root second *
        reward ⟨{second}, Finset.singleton_nonempty second⟩ who +
      hazardOfRoot root first * hazardOfRoot root second *
        reward ⟨{first, second}, by simp⟩ who := by
  rw [quittingRootExpectedPayoff_eq_sum_activePowerset
    reward continuation {first, second} root hroot who]
  rw [sum_powerset_pair first second hne]
  rw [coalitionMass_empty_of_pair_active hne hroot,
    coalitionMass_second_of_pair_active hne hroot,
    coalitionMass_first_of_pair_active hne hroot,
    coalitionMass_pair_of_pair_active hne hroot]
  simp [quittingStageCoalitionPayoff]
  ring

/-- The pair formula as a singleton first-order drift plus one quadratic
collision correction. -/
theorem quittingRootExpectedPayoff_pair_active_drift_collision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (first second who : ι) (hne : first ≠ second)
    (hroot : IsQuittingActiveRoot {first, second} root) :
    quittingRootExpectedPayoff reward continuation root who =
      continuation who +
      hazardOfRoot root first *
        (reward ⟨{first}, Finset.singleton_nonempty first⟩ who - continuation who) +
      hazardOfRoot root second *
        (reward ⟨{second}, Finset.singleton_nonempty second⟩ who - continuation who) +
      hazardOfRoot root first * hazardOfRoot root second *
        (reward ⟨{first, second}, by simp⟩ who -
          reward ⟨{first}, Finset.singleton_nonempty first⟩ who -
          reward ⟨{second}, Finset.singleton_nonempty second⟩ who + continuation who) := by
  rw [quittingRootExpectedPayoff_pair_active
    reward continuation root first second who hne hroot]
  ring

/-! ## Phase 4: cubic truncation and the four-of-five test case -/

omit [Fintype ι] [DecidableEq ι] in
/-- A hazard monomial whose coalition leaves the active set vanishes. -/
theorem prod_hazardOfRoot_eq_zero_of_not_subset_active
    {active : Finset ι} {root : ι → PMF Bool}
    (hroot : IsQuittingActiveRoot active root) {coalition : Finset ι}
    (hcoalition : ¬ coalition ⊆ active) :
    (∏ i ∈ coalition, hazardOfRoot root i) = 0 := by
  rw [Finset.not_subset] at hcoalition
  obtain ⟨i, hiCoalition, hiActive⟩ := hcoalition
  exact Finset.prod_eq_zero hiCoalition
    (hazardOfRoot_eq_zero_of_isQuittingActiveRoot hroot hiActive)

/-- The centered Möbius polynomial restricted to one public active set. -/
def quittingActiveMobiusValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  ∑ S ∈ active.powerset,
    quittingStageMobiusCoeff reward continuation who S *
      ∏ i ∈ S, hazardOfRoot root i

/-- **Möbius support truncation.** An active root evaluates only Möbius
monomials supported inside its active set. -/
theorem quittingRootExpectedPayoff_eq_continuation_add_activeMobiusValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι) (root : ι → PMF Bool)
    (hroot : IsQuittingActiveRoot active root) (who : ι) :
    quittingRootExpectedPayoff reward continuation root who =
      continuation who +
        quittingActiveMobiusValue reward continuation active root who := by
  rw [quittingRootExpectedPayoff_eq_continuation_add_multilinearValue]
  congr 1
  unfold quittingActiveMobiusValue CoalGame.multilinearValue
  symm
  apply Finset.sum_subset (Finset.subset_univ active.powerset)
  intro S _ hS
  have hnot : ¬ S ⊆ active := by simpa using hS
  rw [prod_hazardOfRoot_eq_zero_of_not_subset_active hroot hnot, mul_zero]

omit [Fintype ι] in
/-- Every Möbius monomial above the active cardinality vanishes. -/
theorem quittingStageMobiusTerm_eq_zero_of_active_card_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) {active : Finset ι} {root : ι → PMF Bool}
    (hroot : IsQuittingActiveRoot active root) {K : ℕ}
    (hactive : active.card ≤ K) (who : ι) {coalition : Finset ι}
    (hlarge : K < coalition.card) :
    quittingStageMobiusCoeff reward continuation who coalition *
      ∏ i ∈ coalition, hazardOfRoot root i = 0 := by
  have hnot : ¬ coalition ⊆ active := by
    intro hsubset
    have hcard := Finset.card_le_card hsubset
    omega
  rw [prod_hazardOfRoot_eq_zero_of_not_subset_active hroot hnot, mul_zero]

omit [Fintype ι] in
/-- Three pairwise-distinct active players really form a three-element set. -/
theorem card_triple_eq_three {first second third : ι}
    (h12 : first ≠ second) (h13 : first ≠ third) (h23 : second ≠ third) :
    ({first, second, third} : Finset ι).card = 3 := by
  simp [h12, h13, h23]

/-- **Three-active-player cubic form.** The exact payoff is the continuation
plus the centered Möbius polynomial over the eight coalitions of the active
triple. -/
theorem quittingRootExpectedPayoff_triple_active_cubic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (first second third who : ι)
    (hroot : IsQuittingActiveRoot {first, second, third} root) :
    quittingRootExpectedPayoff reward continuation root who =
      continuation who + quittingActiveMobiusValue reward continuation
        {first, second, third} root who := by
  exact quittingRootExpectedPayoff_eq_continuation_add_activeMobiusValue
    reward continuation {first, second, third} root hroot who

omit [Fintype ι] in
/-- No degree-four-or-higher Möbius term survives on a three-player active
set. -/
theorem quittingStageMobiusTerm_eq_zero_of_triple_active
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) {root : ι → PMF Bool}
    {first second third : ι}
    (h12 : first ≠ second) (h13 : first ≠ third) (h23 : second ≠ third)
    (hroot : IsQuittingActiveRoot {first, second, third} root)
    (who : ι) {coalition : Finset ι} (hlarge : 3 < coalition.card) :
    quittingStageMobiusCoeff reward continuation who coalition *
      ∏ i ∈ coalition, hazardOfRoot root i = 0 := by
  apply quittingStageMobiusTerm_eq_zero_of_active_card_le
    reward continuation hroot (K := 3) (who := who) (coalition := coalition)
  · rw [card_triple_eq_three h12 h13 h23]
  · exact hlarge

/-! ### The `4/5` intermediate model -/

/-- In the first four-player-concurrency test, the ambient game has five
players and the unique `missing` player is inactive. -/
def quittingFourOfFiveActive (missing : Fin 5) : Finset (Fin 5) :=
  Finset.univ.erase missing

/-- Force the missing player in a five-player game to Continue. -/
def quittingFourOfFiveRoot
    (missing : Fin 5) (root : Fin 5 → PMF Bool) : Fin 5 → PMF Bool :=
  quittingActiveRoot (quittingFourOfFiveActive missing) root

@[simp] theorem card_quittingFourOfFiveActive (missing : Fin 5) :
    (quittingFourOfFiveActive missing).card = 4 := by
  simp [quittingFourOfFiveActive]

theorem isQuittingActiveRoot_quittingFourOfFiveRoot
    (missing : Fin 5) (root : Fin 5 → PMF Bool) :
    IsQuittingActiveRoot (quittingFourOfFiveActive missing)
      (quittingFourOfFiveRoot missing root) :=
  isQuittingActiveRoot_quittingActiveRoot _ _

/-- The exact payoff of the `4/5` model reads only the sixteen coalitions
which omit the missing player. -/
theorem quittingRootExpectedPayoff_fourOfFive
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (continuation : Payoff (Fin 5)) (missing : Fin 5)
    (root : Fin 5 → PMF Bool) (who : Fin 5) :
    quittingRootExpectedPayoff reward continuation
        (quittingFourOfFiveRoot missing root) who =
      ∑ S ∈ (quittingFourOfFiveActive missing).powerset,
        coalitionMass
            (hazardOfRoot (quittingFourOfFiveRoot missing root)) S *
          quittingStageCoalitionPayoff reward continuation S who := by
  exact quittingRootExpectedPayoff_eq_sum_activePowerset
    reward continuation (quittingFourOfFiveActive missing)
      (quittingFourOfFiveRoot missing root)
      (isQuittingActiveRoot_quittingFourOfFiveRoot missing root) who

/-- Any five-player simultaneous quitting event is impossible in the `4/5`
model. -/
theorem coalitionMass_univ_fourOfFive_eq_zero
    (missing : Fin 5) (root : Fin 5 → PMF Bool) :
    coalitionMass (hazardOfRoot (quittingFourOfFiveRoot missing root))
      (Finset.univ : Finset (Fin 5)) = 0 := by
  apply coalitionMass_eq_zero_of_active_card_le
    (isQuittingActiveRoot_quittingFourOfFiveRoot missing root)
    (K := 4)
  · simp
  · simp

/-- Equivalently, the centered `4/5` stage polynomial has degree at most
four even though its payoff vector still has five coordinates. -/
theorem quittingStageMobiusTerm_eq_zero_of_fourOfFive_card_five
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (continuation : Payoff (Fin 5)) (missing : Fin 5)
    (root : Fin 5 → PMF Bool) (who : Fin 5)
    {coalition : Finset (Fin 5)} (hcard : coalition.card = 5) :
    quittingStageMobiusCoeff reward continuation who coalition *
      ∏ i ∈ coalition,
        hazardOfRoot (quittingFourOfFiveRoot missing root) i = 0 := by
  apply quittingStageMobiusTerm_eq_zero_of_active_card_le
    reward continuation
      (isQuittingActiveRoot_quittingFourOfFiveRoot missing root)
      (K := 4) (who := who) (coalition := coalition)
  · simp
  · omega

/-! ## Phase 5: the general `K/N` degree theorem -/

/-- The homogeneous degree-`degree` layer of the centered stage payoff,
restricted to a public active set.  Writing the cardinality test inside the
sum makes the finite degree decomposition convenient to use algebraically. -/
def quittingActiveMobiusLayer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (who : ι) (degree : ℕ) : ℝ :=
  ∑ S ∈ active.powerset,
    if S.card = degree then
      quittingStageMobiusCoeff reward continuation who S *
        ∏ i ∈ S, hazardOfRoot root i
    else 0

omit [Fintype ι] in
/-- **General `K/N` stage theorem.** If at most `K` of the ambient `N`
players are active, the exact centered stage payoff is the sum of its
homogeneous layers of degrees `0,…,K`.  There is no dependence on the ambient
player count in the upper degree bound. -/
theorem quittingActiveMobiusValue_eq_sum_layers_of_card_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (who : ι) {K : ℕ}
    (hactive : active.card ≤ K) :
    quittingActiveMobiusValue reward continuation active root who =
      ∑ degree ∈ Finset.range (K + 1),
        quittingActiveMobiusLayer reward continuation active root who degree := by
  classical
  unfold quittingActiveMobiusValue quittingActiveMobiusLayer
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hcardActive : S.card ≤ active.card :=
    Finset.card_le_card (Finset.mem_powerset.mp hS)
  have hcardK : S.card ≤ K := hcardActive.trans hactive
  rw [Finset.sum_eq_single S.card]
  · simp
  · intro degree hdegree hne
    simp [Ne.symm hne]
  · intro hnot
    exfalso
    apply hnot
    simp
    omega

/-- Exact payoff form of the general `K/N` theorem. -/
theorem quittingRootExpectedPayoff_eq_continuation_add_sum_layers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (who : ι) {K : ℕ}
    (hroot : IsQuittingActiveRoot active root)
    (hactive : active.card ≤ K) :
    quittingRootExpectedPayoff reward continuation root who =
      continuation who +
        ∑ degree ∈ Finset.range (K + 1),
          quittingActiveMobiusLayer reward continuation active root who degree := by
  rw [quittingRootExpectedPayoff_eq_continuation_add_activeMobiusValue
    reward continuation active root hroot who]
  rw [quittingActiveMobiusValue_eq_sum_layers_of_card_le
    reward continuation active root who hactive]

omit [Fintype ι] in
/-- The degree-zero centered layer vanishes.  Thus the first nontrivial
layer is precisely the singleton layer. -/
@[simp] theorem quittingActiveMobiusLayer_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingActiveMobiusLayer reward continuation active root who 0 = 0 := by
  classical
  unfold quittingActiveMobiusLayer
  apply Finset.sum_eq_zero
  intro S hS
  by_cases hcard : S.card = 0
  · have hSempty : S = ∅ := Finset.card_eq_zero.mp hcard
    subst S
    simp
  · simp [hcard]

/-! ## Phase 6: scaled hazards and the exact collision hierarchy -/

/-- The active-set centered polynomial evaluated at an arbitrary real hazard
vector.  Probability side conditions are deliberately absent: the scaling
theorems below are polynomial identities. -/
def quittingActiveMobiusValueAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (x : ι → ℝ) (who : ι) : ℝ :=
  ∑ S ∈ active.powerset,
    quittingStageMobiusCoeff reward continuation who S * ∏ i ∈ S, x i

/-- The homogeneous degree-`degree` layer at an arbitrary hazard vector. -/
def quittingActiveMobiusLayerAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (x : ι → ℝ) (who : ι) (degree : ℕ) : ℝ :=
  ∑ S ∈ active.powerset,
    if S.card = degree then
      quittingStageMobiusCoeff reward continuation who S * ∏ i ∈ S, x i
    else 0

omit [Fintype ι] in
theorem quittingActiveMobiusValue_eq_valueAt_hazardOfRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingActiveMobiusValue reward continuation active root who =
      quittingActiveMobiusValueAt reward continuation active
        (hazardOfRoot root) who := by
  rfl

omit [Fintype ι] in
theorem quittingActiveMobiusLayer_eq_layerAt_hazardOfRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (who : ι) (degree : ℕ) :
    quittingActiveMobiusLayer reward continuation active root who degree =
      quittingActiveMobiusLayerAt reward continuation active
        (hazardOfRoot root) who degree := by
  rfl

omit [Fintype ι] in
/-- Arbitrary-vector form of the general degree-`K` decomposition. -/
theorem quittingActiveMobiusValueAt_eq_sum_layers_of_card_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (x : ι → ℝ) (who : ι) {K : ℕ} (hactive : active.card ≤ K) :
    quittingActiveMobiusValueAt reward continuation active x who =
      ∑ degree ∈ Finset.range (K + 1),
        quittingActiveMobiusLayerAt reward continuation active x who degree := by
  classical
  unfold quittingActiveMobiusValueAt quittingActiveMobiusLayerAt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hcardActive : S.card ≤ active.card :=
    Finset.card_le_card (Finset.mem_powerset.mp hS)
  have hcardK : S.card ≤ K := hcardActive.trans hactive
  rw [Finset.sum_eq_single S.card]
  · simp
  · intro degree hdegree hne
    simp [Ne.symm hne]
  · intro hnot
    exfalso
    apply hnot
    simp
    omega

omit [Fintype ι] in
@[simp] theorem quittingActiveMobiusLayerAt_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (x : ι → ℝ) (who : ι) :
    quittingActiveMobiusLayerAt reward continuation active x who 0 = 0 := by
  classical
  unfold quittingActiveMobiusLayerAt
  apply Finset.sum_eq_zero
  intro S hS
  by_cases hcard : S.card = 0
  · have hSempty : S = ∅ := Finset.card_eq_zero.mp hcard
    subst S
    simp
  · simp [hcard]

omit [Fintype ι] in
/-- Homogeneous layers scale by their degree. -/
theorem quittingActiveMobiusLayerAt_smul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (x : ι → ℝ) (who : ι) (degree : ℕ) (delta : ℝ) :
    quittingActiveMobiusLayerAt reward continuation active
        (fun i => delta * x i) who degree =
      delta ^ degree *
        quittingActiveMobiusLayerAt reward continuation active x who degree := by
  classical
  unfold quittingActiveMobiusLayerAt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hcard : S.card = degree
  · simp only [hcard, if_pos]
    have hprod : (∏ i ∈ S, delta * x i) =
        delta ^ S.card * ∏ i ∈ S, x i := by
      simp_rw [Finset.prod_mul_distrib]
      simp
    rw [hprod, hcard]
    ring
  · simp [hcard]

omit [Fintype ι] in
/-- **Scaled general `K/N` theorem.** Along a common radial scale `delta`,
the exact active-set polynomial has one term `delta^degree` for each degree
up to `K`. -/
theorem quittingActiveMobiusValueAt_smul_eq_sum_scaled_layers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (x : ι → ℝ) (who : ι) (delta : ℝ) {K : ℕ}
    (hactive : active.card ≤ K) :
    quittingActiveMobiusValueAt reward continuation active
        (fun i => delta * x i) who =
      ∑ degree ∈ Finset.range (K + 1),
        delta ^ degree *
          quittingActiveMobiusLayerAt reward continuation active x who degree := by
  rw [quittingActiveMobiusValueAt_eq_sum_layers_of_card_le
    reward continuation active (fun i => delta * x i) who hactive]
  apply Finset.sum_congr rfl
  intro degree hdegree
  exact quittingActiveMobiusLayerAt_smul
    reward continuation active x who degree delta

/-- All simultaneous-quitting corrections, collected exactly from degrees
two through `K`. -/
def quittingActiveMobiusCollisionRemainderAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (x : ι → ℝ) (who : ι) (K : ℕ) (delta : ℝ) : ℝ :=
  ∑ degree ∈ Finset.range (K + 1),
    if 2 ≤ degree then
      delta ^ degree *
        quittingActiveMobiusLayerAt reward continuation active x who degree
    else 0

omit [Fintype ι] in
/-- **Singleton/collision separation for arbitrary `K/N`.** The linear
singleton flow is isolated exactly; the remainder consists only of
simultaneous-quitting layers `2,…,K`. -/
theorem quittingActiveMobiusValueAt_smul_eq_singleton_add_collision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (x : ι → ℝ) (who : ι) (delta : ℝ) {K : ℕ}
    (hK : 1 ≤ K) (hactive : active.card ≤ K) :
    quittingActiveMobiusValueAt reward continuation active
        (fun i => delta * x i) who =
      delta * quittingActiveMobiusLayerAt reward continuation active x who 1 +
        quittingActiveMobiusCollisionRemainderAt
          reward continuation active x who K delta := by
  rw [quittingActiveMobiusValueAt_smul_eq_sum_scaled_layers
    reward continuation active x who delta hactive]
  unfold quittingActiveMobiusCollisionRemainderAt
  have hsingle :
      delta * quittingActiveMobiusLayerAt reward continuation active x who 1 =
        ∑ degree ∈ Finset.range (K + 1),
          if degree = 1 then
            delta ^ degree *
              quittingActiveMobiusLayerAt reward continuation active x who degree
          else 0 := by
    symm
    rw [Finset.sum_eq_single 1]
    · simp
    · intro degree hdegree hne
      simp [hne]
    · intro hnot
      exfalso
      apply hnot
      simp
      omega
  rw [hsingle, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro degree hdegree
  have hdegreeK : degree ≤ K := by
    simp at hdegree
    omega
  by_cases hzero : degree = 0
  · subst degree
    simp
  by_cases hone : degree = 1
  · subst degree
    simp
  have htwo : 2 ≤ degree := by omega
  simp [hone, htwo]

/-! ## Phase 7: time-varying `K/N` schedules and Bellman paths -/

/-- A public schedule choosing at most `K` active players at each time. -/
structure QuittingKActiveSchedule (player : Type) (K : ℕ) where
  active : ℕ → Finset player
  card_le : ∀ time, (active time).card ≤ K

/-- A root sequence respects a public active schedule when every player
outside the scheduled set surely Continues at that time. -/
def IsQuittingActiveScheduleRoot
    {player : Type} [DecidableEq player] {K : ℕ}
    (schedule : QuittingKActiveSchedule player K)
    (roots : ℕ → player → PMF Bool) : Prop :=
  ∀ time, IsQuittingActiveRoot (schedule.active time) (roots time)

/-- Pointwise coalition-support consequence of a `K/N` schedule. -/
theorem coalitionMass_eq_zero_of_activeSchedule_card_gt
    {K : ℕ} (schedule : QuittingKActiveSchedule ι K)
    (roots : ℕ → ι → PMF Bool)
    (hsupport : IsQuittingActiveScheduleRoot schedule roots)
    (time : ℕ) {coalition : Finset ι} (hlarge : K < coalition.card) :
    coalitionMass (hazardOfRoot (roots time)) coalition = 0 := by
  exact coalitionMass_eq_zero_of_active_card_le (hsupport time)
    (schedule.card_le time) hlarge

/-- Every stage successor on a `K/N` schedule has exact degree at most `K`,
even when the public active set changes with time. -/
theorem quittingRootSuccessorPayoff_eq_next_add_sum_layers_of_activeSchedule
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    {K : ℕ} (schedule : QuittingKActiveSchedule ι K)
    (hsupport : IsQuittingActiveScheduleRoot schedule roots)
    (time : ℕ) (who : ι) :
    quittingRootSuccessorPayoff reward (value (time + 1)) (roots time) who =
      value (time + 1) who +
        ∑ degree ∈ Finset.range (K + 1),
          quittingActiveMobiusLayer reward (value (time + 1))
            (schedule.active time) (roots time) who degree := by
  exact quittingRootExpectedPayoff_eq_continuation_add_sum_layers
    reward (value (time + 1)) (schedule.active time) (roots time) who
      (hsupport time) (schedule.card_le time)

/-- **Bellman-path `K/N` theorem.** On any exact Bellman spine respecting a
public `K`-active schedule, every recursion step is continuation plus a
degree-`K` polynomial, uniformly in the ambient number of players. -/
theorem exactBellmanSpine_value_eq_next_add_sum_layers_of_activeSchedule
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    {K : ℕ} (schedule : QuittingKActiveSchedule ι K)
    (hsupport : IsQuittingActiveScheduleRoot schedule roots)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (time : ℕ) (who : ι) :
    value time who = value (time + 1) who +
      ∑ degree ∈ Finset.range (K + 1),
        quittingActiveMobiusLayer reward (value (time + 1))
          (schedule.active time) (roots time) who degree := by
  calc
    value time who =
        quittingRootSuccessorPayoff reward (value (time + 1))
          (roots time) who := congrFun (hspine.2.1 time) who
    _ = value (time + 1) who +
        ∑ degree ∈ Finset.range (K + 1),
          quittingActiveMobiusLayer reward (value (time + 1))
            (schedule.active time) (roots time) who degree :=
      quittingRootSuccessorPayoff_eq_next_add_sum_layers_of_activeSchedule
        reward value roots schedule hsupport time who

/-- With one scheduled player at a time, the Bellman spine is exactly
affine: every collision layer disappears and only the singleton layer
remains. -/
theorem exactBellmanSpine_value_eq_next_add_singletonLayer_of_oneActiveSchedule
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (schedule : QuittingKActiveSchedule ι 1)
    (hsupport : IsQuittingActiveScheduleRoot schedule roots)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (time : ℕ) (who : ι) :
    value time who = value (time + 1) who +
      quittingActiveMobiusLayer reward (value (time + 1))
        (schedule.active time) (roots time) who 1 := by
  rw [exactBellmanSpine_value_eq_next_add_sum_layers_of_activeSchedule
    reward value roots schedule hsupport hspine time who]
  simp [Finset.sum_range_succ]

/-! ## Phase 8: unilateral deviations cost one extra active coordinate -/

omit [Fintype ι] in
/-- Forcing any player to Continue does not enlarge active support. -/
theorem isQuittingActiveRoot_update_continue
    {active : Finset ι} {root : ι → PMF Bool}
    (hroot : IsQuittingActiveRoot active root) (who : ι) :
    IsQuittingActiveRoot active
      (Function.update root who (PMF.pure false)) := by
  intro i hi
  by_cases hiwho : i = who
  · subst i
    simp
  · rw [Function.update_of_ne hiwho]
    exact hroot i hi

omit [Fintype ι] in
/-- Forcing player `who` to Quit enlarges active support by at most that one
coordinate. -/
theorem isQuittingActiveRoot_update_quit
    {active : Finset ι} {root : ι → PMF Bool}
    (hroot : IsQuittingActiveRoot active root) (who : ι) :
    IsQuittingActiveRoot (insert who active)
      (Function.update root who (PMF.pure true)) := by
  intro i hi
  have hiwho : i ≠ who := by
    intro h
    subst i
    exact hi (Finset.mem_insert_self who active)
  rw [Function.update_of_ne hiwho]
  apply hroot i
  intro hiactive
  exact hi (Finset.mem_insert_of_mem hiactive)

omit [Fintype ι] in
theorem card_insert_le_succ_of_card_le
    {active : Finset ι} {K : ℕ} (hactive : active.card ≤ K) (who : ι) :
    (insert who active).card ≤ K + 1 := by
  calc
    (insert who active).card ≤ active.card + 1 := Finset.card_insert_le _ _
    _ ≤ K + 1 := Nat.add_le_add_right hactive 1

/-- A pure-Continue deviation from a `K`-active root is still a degree-`K`
calculation. -/
theorem quittingRootContinuePayoff_eq_continuation_add_sum_layers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (who : ι) {K : ℕ}
    (hroot : IsQuittingActiveRoot active root) (hactive : active.card ≤ K) :
    quittingRootContinuePayoff reward continuation root who =
      continuation who +
        ∑ degree ∈ Finset.range (K + 1),
          quittingActiveMobiusLayer reward continuation active
            (Function.update root who (PMF.pure false)) who degree := by
  unfold quittingRootContinuePayoff
  exact quittingRootExpectedPayoff_eq_continuation_add_sum_layers
    reward continuation active
      (Function.update root who (PMF.pure false)) who
      (isQuittingActiveRoot_update_continue hroot who) hactive

/-- A pure-Quit deviation from a `K`-active root is a degree-`K+1`
calculation: the deviator is the only possible new active coordinate. -/
theorem quittingRootQuitPayoff_eq_continuation_add_sum_layers_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (who : ι) {K : ℕ}
    (hroot : IsQuittingActiveRoot active root) (hactive : active.card ≤ K) :
    quittingRootQuitPayoff reward continuation root who =
      continuation who +
        ∑ degree ∈ Finset.range ((K + 1) + 1),
          quittingActiveMobiusLayer reward continuation (insert who active)
            (Function.update root who (PMF.pure true)) who degree := by
  unfold quittingRootQuitPayoff
  exact quittingRootExpectedPayoff_eq_continuation_add_sum_layers
    reward continuation (insert who active)
      (Function.update root who (PMF.pure true)) who
      (isQuittingActiveRoot_update_quit hroot who)
      (card_insert_le_succ_of_card_le hactive who)

/-- The endpoint gain used by the full-game Nash test is therefore the
difference of a degree-`K+1` Quit polynomial and a degree-`K` Continue
polynomial.  Their common continuation constant cancels exactly. -/
theorem quittingRootEndpointDifference_eq_sum_layers_succ_sub_sum_layers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (who : ι) {K : ℕ}
    (hroot : IsQuittingActiveRoot active root) (hactive : active.card ≤ K) :
    quittingRootEndpointDifference reward continuation root who =
      (∑ degree ∈ Finset.range ((K + 1) + 1),
        quittingActiveMobiusLayer reward continuation (insert who active)
          (Function.update root who (PMF.pure true)) who degree) -
      ∑ degree ∈ Finset.range (K + 1),
        quittingActiveMobiusLayer reward continuation active
          (Function.update root who (PMF.pure false)) who degree := by
  unfold quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_eq_continuation_add_sum_layers_succ
      reward continuation active root who hroot hactive,
    quittingRootContinuePayoff_eq_continuation_add_sum_layers
      reward continuation active root who hroot hactive]
  ring

/-- Local polynomial appearing in the full-game endpoint Nash test around a
`K`-active root. -/
def quittingActiveEndpointLayerDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (K : ℕ) (who : ι) : ℝ :=
  (∑ degree ∈ Finset.range ((K + 1) + 1),
    quittingActiveMobiusLayer reward continuation (insert who active)
      (Function.update root who (PMF.pure true)) who degree) -
  ∑ degree ∈ Finset.range (K + 1),
    quittingActiveMobiusLayer reward continuation active
      (Function.update root who (PMF.pure false)) who degree

theorem quittingRootEndpointDifference_eq_activeEndpointLayerDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (who : ι) {K : ℕ}
    (hroot : IsQuittingActiveRoot active root) (hactive : active.card ≤ K) :
    quittingRootEndpointDifference reward continuation root who =
      quittingActiveEndpointLayerDifference
        reward continuation active root K who := by
  exact quittingRootEndpointDifference_eq_sum_layers_succ_sub_sum_layers
    reward continuation active root who hroot hactive

/-- **Full Nash reduction around a `K`-active root.** All mixed unilateral
deviations reduce exactly to two scalar inequalities per player, whose local
polynomial is of degree at most `K+1`.  The number of constraints can still
depend on the ambient player count, but their interaction order cannot. -/
theorem isεQuittingRootNash_iff_activeEndpointLayerInequalities
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (ε : ℝ) {K : ℕ}
    (hroot : IsQuittingActiveRoot active root) (hactive : active.card ≤ K) :
    IsεQuittingRootNash reward continuation ε root ↔
      ∀ who,
        (root who false).toReal *
            quittingActiveEndpointLayerDifference
              reward continuation active root K who ≤ ε ∧
          -ε ≤ (root who true).toReal *
            quittingActiveEndpointLayerDifference
              reward continuation active root K who := by
  rw [← isεQuittingRootEndpointNash_iff_isεQuittingRootNash]
  unfold IsεQuittingRootEndpointNash
  constructor
  · intro hnash who
    rw [← quittingRootEndpointDifference_eq_activeEndpointLayerDifference
      reward continuation active root who hroot hactive]
    exact hnash who
  · intro hlayers who
    rw [quittingRootEndpointDifference_eq_activeEndpointLayerDifference
      reward continuation active root who hroot hactive]
    exact hlayers who

/-! ## Phase 9: the genuine restricted-action collapse -/

omit [Fintype ι] in
/-- If `who` is one of the legally active players, forcing Quit does not
enlarge support. -/
theorem isQuittingActiveRoot_update_quit_of_mem
    {active : Finset ι} {root : ι → PMF Bool}
    (hroot : IsQuittingActiveRoot active root) {who : ι} (hwho : who ∈ active) :
    IsQuittingActiveRoot active
      (Function.update root who (PMF.pure true)) := by
  intro i hi
  have hiwho : i ≠ who := by
    intro h
    subst i
    exact hi hwho
  rw [Function.update_of_ne hiwho]
  exact hroot i hi

/-- For a legally active deviator, the pure-Quit endpoint remains a
degree-`K` calculation rather than the degree-`K+1` full-game bound. -/
theorem quittingRootQuitPayoff_eq_continuation_add_sum_layers_of_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (who : ι) {K : ℕ}
    (hroot : IsQuittingActiveRoot active root) (hactive : active.card ≤ K)
    (hwho : who ∈ active) :
    quittingRootQuitPayoff reward continuation root who =
      continuation who +
        ∑ degree ∈ Finset.range (K + 1),
          quittingActiveMobiusLayer reward continuation active
            (Function.update root who (PMF.pure true)) who degree := by
  unfold quittingRootQuitPayoff
  exact quittingRootExpectedPayoff_eq_continuation_add_sum_layers
    reward continuation active
      (Function.update root who (PMF.pure true)) who
      (isQuittingActiveRoot_update_quit_of_mem hroot hwho) hactive

/-- Degree-`K` endpoint polynomial when only members of `active` are legal
deviators. -/
def quittingRestrictedActiveEndpointLayerDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (K : ℕ) (who : ι) : ℝ :=
  (∑ degree ∈ Finset.range (K + 1),
    quittingActiveMobiusLayer reward continuation active
      (Function.update root who (PMF.pure true)) who degree) -
  ∑ degree ∈ Finset.range (K + 1),
    quittingActiveMobiusLayer reward continuation active
      (Function.update root who (PMF.pure false)) who degree

theorem quittingRootEndpointDifference_eq_restrictedActiveEndpointLayers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (who : ι) {K : ℕ}
    (hroot : IsQuittingActiveRoot active root) (hactive : active.card ≤ K)
    (hwho : who ∈ active) :
    quittingRootEndpointDifference reward continuation root who =
      quittingRestrictedActiveEndpointLayerDifference
        reward continuation active root K who := by
  unfold quittingRootEndpointDifference
    quittingRestrictedActiveEndpointLayerDifference
  rw [quittingRootQuitPayoff_eq_continuation_add_sum_layers_of_mem
      reward continuation active root who hroot hactive hwho,
    quittingRootContinuePayoff_eq_continuation_add_sum_layers
      reward continuation active root who hroot hactive]
  ring

/-- Endpoint Nash conditions for the modified game rule in which only
members of `active` are allowed to move at this stage. -/
def IsεQuittingRestrictedActiveEndpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (ε : ℝ) (root : ι → PMF Bool) : Prop :=
  ∀ who ∈ active,
    (root who false).toReal *
        quittingRootEndpointDifference reward continuation root who ≤ ε ∧
      -ε ≤ (root who true).toReal *
        quittingRootEndpointDifference reward continuation root who

/-- **Restricted-action `K/N` Nash collapse.** With inactive moves genuinely
forbidden, every legal endpoint Nash condition has degree at most `K`; the
extra `K+1` layer from an outside deviator is absent. -/
theorem isεQuittingRestrictedActiveEndpointNash_iff_degreeKLayerInequalities
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (active : Finset ι)
    (root : ι → PMF Bool) (ε : ℝ) {K : ℕ}
    (hroot : IsQuittingActiveRoot active root) (hactive : active.card ≤ K) :
    IsεQuittingRestrictedActiveEndpointNash
        reward continuation active ε root ↔
      ∀ who ∈ active,
        (root who false).toReal *
            quittingRestrictedActiveEndpointLayerDifference
              reward continuation active root K who ≤ ε ∧
          -ε ≤ (root who true).toReal *
            quittingRestrictedActiveEndpointLayerDifference
              reward continuation active root K who := by
  unfold IsεQuittingRestrictedActiveEndpointNash
  constructor
  · intro hnash who hwho
    rw [← quittingRootEndpointDifference_eq_restrictedActiveEndpointLayers
      reward continuation active root who hroot hactive hwho]
    exact hnash who hwho
  · intro hlayers who hwho
    rw [quittingRootEndpointDifference_eq_restrictedActiveEndpointLayers
      reward continuation active root who hroot hactive hwho]
    exact hlayers who hwho

/-! ## Phase 10: direct existence reduction and the phantom obstruction -/

/-- The empty public schedule is `K`-active for every `K`. -/
def quittingEmptyActiveSchedule (player : Type) (K : ℕ) :
    QuittingKActiveSchedule player K where
  active := fun _ => ∅
  card_le := by simp

omit [Fintype ι] in
/-- The canonical all-Continue phantom spine respects even the empty
schedule. -/
theorem canonicalPhantom_isQuittingEmptyActiveScheduleRoot
    (K : ℕ) :
    IsQuittingActiveScheduleRoot
      (quittingEmptyActiveSchedule ι K)
      (quittingCanonicalPhantomRoots (ι := ι)) := by
  intro time player hplayer
  simp [quittingCanonicalPhantomRoots, quittingAllContinueRoot]

/-- Hence bare existence of a `K`-active exact Nash--Bellman spine is
vacuous: the nonabsorbing phantom supplies one for every game and every
`K`. -/
theorem exists_KActiveExactQuittingNashBellmanSpine_phantom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (K : ℕ) :
    ∃ (schedule : QuittingKActiveSchedule ι K)
      (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
      IsQuittingActiveScheduleRoot schedule roots ∧
        IsCanonicalExactQuittingNashBellmanSpine reward value roots := by
  exact ⟨quittingEmptyActiveSchedule ι K,
    quittingCanonicalPhantomValue reward,
    quittingCanonicalPhantomRoots (ι := ι),
    canonicalPhantom_isQuittingEmptyActiveScheduleRoot K,
    canonicalPhantom_isExactQuittingNashBellmanSpine reward⟩

/-- A supplied `K`-active exact spine obeys the existing exhaustive clock
alternative; the exceptional branch retains the same `K`-active support. -/
theorem uniformEquilibriumPayoff_or_summableClock_of_KActiveExactSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    {K : ℕ} (schedule : QuittingKActiveSchedule ι K)
    (hsupport : IsQuittingActiveScheduleRoot schedule roots)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (value 0) ∨
      ∃ owner,
        IsQuittingActiveScheduleRoot schedule roots ∧
          Summable (quittingOpponentClockCharge roots owner) ∧
            ∃ start,
              0 < quittingLiveMassLimit reward
                (quittingOpponentOnlyProfile reward
                  (quittingAllContinueProfileSpine reward
                    (quittingInfinitePathProfile reward roots) start)
                  owner) := by
  rcases uniformEquilibriumPayoff_or_summableClock_of_exactNashBellmanSpine
      reward value roots hspine with huniform | ⟨owner, hclock, hpositive⟩
  · exact Or.inl huniform
  · exact Or.inr ⟨owner, hsupport, hclock, hpositive⟩

/-- **Direct general `K/N` existence reduction.** Constructing one
non-phantom `K`-active exact spine whose every opponent clock diverges is
already sufficient for a uniform-equilibrium payoff.  All local Bellman and
Nash equations of that certificate have degree bounded by `K` and `K+1`,
respectively, by the preceding theorems. -/
theorem uniformEquilibriumPayoff_of_exists_productiveKActiveExactSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {K : ℕ}
    (hproductive :
      ∃ (schedule : QuittingKActiveSchedule ι K)
        (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
        IsQuittingActiveScheduleRoot schedule roots ∧
          IsCanonicalExactQuittingNashBellmanSpine reward value roots ∧
            ∀ owner, ¬ Summable (quittingOpponentClockCharge roots owner)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨schedule, value, roots, hsupport, hspine, hdivergent⟩ := hproductive
  rcases uniformEquilibriumPayoff_or_summableClock_of_KActiveExactSpine
      reward value roots schedule hsupport hspine with
    huniform | ⟨owner, _, hclock, _⟩
  · exact ⟨value 0, huniform⟩
  · exact (hdivergent owner hclock).elim

end GameTheory
