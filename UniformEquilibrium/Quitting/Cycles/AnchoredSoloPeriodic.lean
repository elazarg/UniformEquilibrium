/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PeriodicCompiler
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot
import MathUE.PMFProduct.Update

/-!
# Anchored solo-periodic profiles

Fix a period `m`, a schedule `w : Fin m → ι` of designated quitters
(repetitions allowed), and a per-phase quit hazard `hazard : Fin m → ℝ`.
The associated *single-quitter periodic profile* prescribes, at every stage
congruent to `k` modulo `m`, that `w k` quits with probability `hazard k`
while every other player continues.

Every root of that family is a `quittingSoloMixedRoot`: one designated owner
randomizes and every other player continues surely.  All one-stage statistics
of such a root are two-term mixtures of singleton, pair, and tail data, so no
`2 ^ card ι` expansion is needed anywhere below.

The profile's on-path value `quittingAnchoredCyclicOnPathValue` solves the
linear renewal recursion `U^k = p_k * r({w k}) + (1 - p_k) * U^{k+1}` around
the cycle, as `quittingAnchoredCyclicOnPathValue_renewal` records.

`IsExactAnchoredSoloPeriodic` is the exactness property of such a profile: at
every phase its root is endpoint Nash at accuracy zero against the on-path
value of the next phase.  `anchor_of_isExactAnchoredSoloPeriodic` and
`spectatorFloor_of_isExactAnchoredSoloPeriodic` decompose it into the
scheduled quitter's indifference anchor and the spectators' floor.

This module is table-independent.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Solo mixed roots

A root at which one designated owner randomizes and every other player
continues surely.  Every periodic family below is built from these, and all
their one-stage statistics are two-term mixtures of singleton, pair, and
tail data: no `2 ^ card ι` expansion is ever needed.
-/

/-- The product root at which `owner` quits with law `marginal` and every
other player continues surely. -/
def quittingSoloMixedRoot (owner : ι) (marginal : PMF Bool) : ι → PMF Bool :=
  Function.update quittingAllContinueRoot owner marginal

omit [Fintype ι] in
@[simp] theorem quittingSoloMixedRoot_self (owner : ι) (marginal : PMF Bool) :
    quittingSoloMixedRoot owner marginal owner = marginal := by
  simp [quittingSoloMixedRoot]

omit [Fintype ι] in
theorem quittingSoloMixedRoot_of_ne {owner who : ι} (hne : who ≠ owner)
    (marginal : PMF Bool) :
    quittingSoloMixedRoot owner marginal who = PMF.pure false := by
  simp [quittingSoloMixedRoot, Function.update_of_ne hne,
    quittingAllContinueRoot]

omit [Fintype ι] in
theorem quittingAllContinueRoot_update_false (owner : ι) :
    Function.update (quittingAllContinueRoot : ι → PMF Bool) owner
        (PMF.pure false) = quittingAllContinueRoot := by
  funext player
  by_cases hp : player = owner
  · subst player
    simp [quittingAllContinueRoot]
  · simp [Function.update_of_ne hp]

/-- At a solo mixed root the everyone-continues mass is the owner's own
Continue probability. -/
theorem quittingStationaryContinueMass_soloMixedRoot
    (owner : ι) (marginal : PMF Bool) :
    quittingStationaryContinueMass (quittingSoloMixedRoot owner marginal) =
      (marginal false).toReal := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  refine (Finset.prod_eq_single owner ?_ ?_).trans ?_
  · intro player _ hne
    rw [quittingSoloMixedRoot_of_ne hne]
    simp
  · intro hmem
    exact absurd (Finset.mem_univ owner) hmem
  · rw [quittingSoloMixedRoot_self]

/-- Hence its absorption mass is the owner's own Quit probability. -/
theorem quittingRootAbsorptionMass_soloMixedRoot
    (owner : ι) (marginal : PMF Bool) :
    quittingRootAbsorptionMass (quittingSoloMixedRoot owner marginal) =
      (marginal true).toReal := by
  have hsum : (marginal false).toReal + (marginal true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one marginal
  rw [quittingRootAbsorptionMass, quittingStationaryContinueMass_soloMixedRoot]
  linarith

/-- Splitting one mover's Boolean marginal.  Unlike
`quittingRootExpectedPayoff_update_eq_endpointMix`, the evaluated coordinate
is arbitrary: it need not be the mover. -/
theorem quittingRootExpectedPayoff_update_eq_moverMix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (mover who : ι)
    (marginal : PMF Bool) :
    quittingRootExpectedPayoff reward tail
        (Function.update root mover marginal) who =
      (marginal true).toReal *
          quittingRootExpectedPayoff reward tail
            (Function.update root mover (PMF.pure true)) who +
        (marginal false).toReal *
          quittingRootExpectedPayoff reward tail
            (Function.update root mover (PMF.pure false)) who := by
  unfold quittingRootExpectedPayoff
  rw [pmfPi_update_bind, expect_bind, expect_eq_sum, Fintype.sum_bool]

omit [DecidableEq ι] in
/-- A deterministic product root evaluates to its deterministic row. -/
theorem quittingRootExpectedPayoff_pure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (action : ι → Bool) (who : ι) :
    quittingRootExpectedPayoff reward tail
        (fun player ↦ PMF.pure (action player)) who =
      quittingRootPayoff reward tail action who := by
  unfold quittingRootExpectedPayoff
  rw [pmfPi_pure, expect_pure]

/-- The sure solo quit of `owner` pays every coordinate the owner's
singleton row. -/
theorem quittingRootExpectedPayoff_allContinue_update_true
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (owner who : ι) :
    quittingRootExpectedPayoff reward tail
        (Function.update (quittingAllContinueRoot : ι → PMF Bool) owner
          (PMF.pure true)) who =
      reward (quittingSingletonTerminal owner) who := by
  classical
  set action : ι → Bool := Function.update (fun _ : ι ↦ false) owner true
    with haction
  have hfamily :
      Function.update (quittingAllContinueRoot : ι → PMF Bool) owner
          (PMF.pure true) = fun player ↦ PMF.pure (action player) := by
    funext player
    by_cases hp : player = owner
    · subst player
      simp [haction]
    · simp [quittingAllContinueRoot, haction, hp]
  have hset : quittingQuitters action = {owner} := by
    ext player
    by_cases hp : player = owner <;> simp [quittingQuitters, haction, hp]
  have hnonempty : (quittingQuitters action).Nonempty := by
    rw [hset]
    exact Finset.singleton_nonempty owner
  rw [hfamily, quittingRootExpectedPayoff_pure,
    show quittingRootPayoff reward tail action who =
      reward ⟨quittingQuitters action, hnonempty⟩ who by
        simp [quittingRootPayoff, hnonempty]]
  congr 1
  exact Subtype.ext hset

/-- The sure joint quit of two distinct players pays every coordinate the
corresponding pair row. -/
theorem quittingRootExpectedPayoff_allContinue_update_pair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (owner joiner who : ι) :
    quittingRootExpectedPayoff reward tail
        (Function.update
          (Function.update (quittingAllContinueRoot : ι → PMF Bool) joiner
            (PMF.pure true)) owner (PMF.pure true)) who =
      reward ⟨{owner, joiner}, Finset.insert_nonempty owner {joiner}⟩ who := by
  classical
  set action : ι → Bool :=
    fun player ↦ decide (player = owner ∨ player = joiner) with haction
  have hfamily :
      Function.update
          (Function.update (quittingAllContinueRoot : ι → PMF Bool) joiner
            (PMF.pure true)) owner (PMF.pure true) =
        fun player ↦ PMF.pure (action player) := by
    funext player
    by_cases hp : player = owner
    · subst player
      simp [haction]
    · by_cases hq : player = joiner
      · subst player
        simp [haction, hp]
      · simp [quittingAllContinueRoot, haction, hp, hq]
  have hset : quittingQuitters action = {owner, joiner} := by
    ext player
    simp [quittingQuitters, haction]
  have hnonempty : (quittingQuitters action).Nonempty := by
    rw [hset]
    exact Finset.insert_nonempty owner {joiner}
  rw [hfamily, quittingRootExpectedPayoff_pure,
    show quittingRootPayoff reward tail action who =
      reward ⟨quittingQuitters action, hnonempty⟩ who by
        simp [quittingRootPayoff, hnonempty]]
  congr 1
  exact Subtype.ext hset

/-! ### One-stage statistics of a solo mixed root -/

/-- Every coordinate reads the same two-term mixture: the owner's singleton
row with the owner's quit probability, the declared tail otherwise. -/
theorem quittingRootSuccessorPayoff_soloMixedRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (owner who : ι) (marginal : PMF Bool) :
    quittingRootSuccessorPayoff reward tail
        (quittingSoloMixedRoot owner marginal) who =
      (marginal true).toReal * reward (quittingSingletonTerminal owner) who +
        (marginal false).toReal * tail who := by
  unfold quittingRootSuccessorPayoff quittingSoloMixedRoot
  rw [quittingRootExpectedPayoff_update_eq_moverMix,
    quittingRootExpectedPayoff_allContinue_update_true,
    quittingAllContinueRoot_update_false]
  congr 2
  simpa [quittingRootContinuePayoff, quittingAllContinueRoot_update_false]
    using (quittingRootContinuePayoff_allContinueRoot reward tail who)

/-- The owner's pure Quit endpoint is its own singleton row. -/
theorem quittingRootQuitPayoff_soloMixedRoot_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (owner : ι) (marginal : PMF Bool) :
    quittingRootQuitPayoff reward tail
        (quittingSoloMixedRoot owner marginal) owner =
      reward (quittingSingletonTerminal owner) owner := by
  unfold quittingRootQuitPayoff quittingSoloMixedRoot
  rw [Function.update_idem]
  exact quittingRootExpectedPayoff_allContinue_update_true reward tail owner owner

/-- The owner's pure Continue endpoint is its declared tail coordinate. -/
theorem quittingRootContinuePayoff_soloMixedRoot_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (owner : ι) (marginal : PMF Bool) :
    quittingRootContinuePayoff reward tail
        (quittingSoloMixedRoot owner marginal) owner = tail owner := by
  unfold quittingRootContinuePayoff quittingSoloMixedRoot
  rw [Function.update_idem, quittingAllContinueRoot_update_false]
  simpa [quittingRootContinuePayoff, quittingAllContinueRoot_update_false]
    using (quittingRootContinuePayoff_allContinueRoot reward tail owner)

/-- A spectator's pure Quit endpoint mixes the collision row with its own
singleton row. -/
theorem quittingRootQuitPayoff_soloMixedRoot_of_ne
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {owner who : ι} (hne : who ≠ owner)
    (marginal : PMF Bool) :
    quittingRootQuitPayoff reward tail
        (quittingSoloMixedRoot owner marginal) who =
      (marginal true).toReal *
          reward ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who +
        (marginal false).toReal *
          reward (quittingSingletonTerminal who) who := by
  unfold quittingRootQuitPayoff quittingSoloMixedRoot
  rw [Function.update_comm hne.symm,
    quittingRootExpectedPayoff_update_eq_moverMix,
    quittingRootExpectedPayoff_allContinue_update_pair reward tail owner who who]
  congr 2
  rw [show Function.update
      (Function.update (quittingAllContinueRoot : ι → PMF Bool) who
        (PMF.pure true)) owner (PMF.pure false) =
    Function.update (quittingAllContinueRoot : ι → PMF Bool) who
      (PMF.pure true) by
    funext player
    by_cases hp : player = owner
    · subst player
      simp [Function.update_of_ne hne.symm, quittingAllContinueRoot]
    · simp [Function.update_of_ne hp]]
  exact quittingRootExpectedPayoff_allContinue_update_true reward tail who who

/-- A spectator's pure Continue endpoint is the same mixture as its
successor payoff: continuing is what the prescribed root already does. -/
theorem quittingRootContinuePayoff_soloMixedRoot_of_ne
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {owner who : ι} (hne : who ≠ owner)
    (marginal : PMF Bool) :
    quittingRootContinuePayoff reward tail
        (quittingSoloMixedRoot owner marginal) who =
      (marginal true).toReal * reward (quittingSingletonTerminal owner) who +
        (marginal false).toReal * tail who := by
  have hfix : Function.update (quittingSoloMixedRoot owner marginal) who
      (PMF.pure false) = quittingSoloMixedRoot owner marginal := by
    rw [← quittingSoloMixedRoot_of_ne hne marginal]
    exact Function.update_eq_self who _
  unfold quittingRootContinuePayoff
  rw [hfix]
  exact quittingRootSuccessorPayoff_soloMixedRoot reward tail owner who marginal

/-! ### Exact root Nash for a solo mixed root -/

/-- A solo mixed root is exactly Nash against its declared tail as soon as
the owner is indifferent and every spectator's collision mixture is at most
its prescribed continuation. -/
theorem isZeroQuittingRootEndpointNash_soloMixedRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (owner : ι) (marginal : PMF Bool)
    (howner : reward (quittingSingletonTerminal owner) owner = tail owner)
    (hspectator : ∀ who, who ≠ owner →
      (marginal true).toReal *
            reward ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who +
          (marginal false).toReal *
            reward (quittingSingletonTerminal who) who ≤
        (marginal true).toReal * reward (quittingSingletonTerminal owner) who +
          (marginal false).toReal * tail who) :
    IsεQuittingRootEndpointNash reward tail 0
      (quittingSoloMixedRoot owner marginal) := by
  intro who
  by_cases hwho : who = owner
  · subst hwho
    have hdiff : quittingRootEndpointDifference reward tail
        (quittingSoloMixedRoot who marginal) who = 0 := by
      rw [quittingRootEndpointDifference,
        quittingRootQuitPayoff_soloMixedRoot_self,
        quittingRootContinuePayoff_soloMixedRoot_self, howner, sub_self]
    simp [hdiff]
  · have hdiff : quittingRootEndpointDifference reward tail
        (quittingSoloMixedRoot owner marginal) who ≤ 0 := by
      rw [quittingRootEndpointDifference,
        quittingRootQuitPayoff_soloMixedRoot_of_ne reward tail hwho,
        quittingRootContinuePayoff_soloMixedRoot_of_ne reward tail hwho]
      linarith [hspectator who hwho]
    rw [quittingSoloMixedRoot_of_ne hwho]
    exact ⟨by simpa using hdiff, by simp⟩

/-! ## The anchored cyclic family -/

variable {m : ℕ}

/-- The single-quitter periodic cycle of a schedule `w` and hazards
`hazard`: at phase `k` the player `w k` quits with probability `hazard k`
and everyone else continues. -/
def quittingAnchoredCyclicCycle (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) :
    Fin m → ι → PMF Bool :=
  fun k ↦
    quittingSoloMixedRoot (w k) (quittingHazardCoin (hazard k) (h0 k) (h1 k))

/-- The initial phase of a nonempty period. -/
def quittingAnchoredCyclicStart (m : ℕ) [NeZero m] : Fin m :=
  ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩

/-- The behavior profile generated by the anchored cyclic cycle, started at
phase zero. -/
def quittingAnchoredCyclicProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) [NeZero m] :
    (quittingGame reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward
    (quittingAnchoredCyclicCycle w hazard h0 h1) (quittingAnchoredCyclicStart m)

/-- The on-path value `U^k`: the terminal payoff of the anchored cyclic
profile read from phase `k`. -/
def quittingAnchoredCyclicOnPathValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (phase : Fin m) :
    Payoff ι :=
  quittingCyclicTerminalValue reward
    (quittingAnchoredCyclicCycle w hazard h0 h1) phase

/-- The on-path value is literally the profile's terminal payoff. -/
theorem quittingTerminalPayoff_anchoredCyclicProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) [NeZero m] :
    quittingTerminalPayoff reward
        (quittingAnchoredCyclicProfile reward w hazard h0 h1) =
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
        (quittingAnchoredCyclicStart m) := rfl

/-- **The linear renewal system.**  `U^k = p_k * r({w k}) + (1 - p_k) * U^{k+1}`
around the cycle, coordinatewise, with no limits. -/
theorem quittingAnchoredCyclicOnPathValue_renewal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (phase : Fin m) (who : ι) :
    quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase who =
      hazard phase * reward (quittingSingletonTerminal (w phase)) who +
        (1 - hazard phase) *
          quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
            (finRotate m phase) who := by
  unfold quittingAnchoredCyclicOnPathValue
  rw [quittingCyclicTerminalValue_eq_rootSuccessorPayoff reward
    (quittingAnchoredCyclicCycle w hazard h0 h1) phase]
  rw [show quittingAnchoredCyclicCycle w hazard h0 h1 phase =
      quittingSoloMixedRoot (w phase)
        (quittingHazardCoin (hazard phase) (h0 phase) (h1 phase)) from rfl,
    quittingRootSuccessorPayoff_soloMixedRoot]
  simp

/-- An exact anchored solo-periodic profile: at every phase the scheduled
player `w phase` mixes with hazard `hazard phase` while every other player
continues, and the resulting one-stage root is exactly endpoint Nash against
the on-path continuation value of the next phase. -/
def IsExactAnchoredSoloPeriodic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {m : ℕ}
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) : Prop :=
  ∀ phase : Fin m,
    IsεQuittingRootEndpointNash reward
      (quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 (finRotate m phase))
      0 (quittingAnchoredCyclicCycle w hazard h0 h1 phase)

/-- An `ε`-exact anchored solo-periodic profile: at every phase the scheduled
player's root is endpoint Nash at accuracy `ε` against the on-path
continuation value of the next phase. -/
def IsεExactAnchoredSoloPeriodic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) {m : ℕ}
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) : Prop :=
  ∀ phase : Fin m,
    IsεQuittingRootEndpointNash reward
      (quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 (finRotate m phase))
      ε (quittingAnchoredCyclicCycle w hazard h0 h1 phase)

theorem isExactAnchoredSoloPeriodic_iff_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {m : ℕ}
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) :
    IsExactAnchoredSoloPeriodic reward w hazard h0 h1 ↔
      IsεExactAnchoredSoloPeriodic reward 0 w hazard h0 h1 :=
  Iff.rfl

/-- The scheduled quitter's indifference, from above: the excess of the next
phase's on-path value over the scheduled quitter's own solo exit, weighted by
that player's own quit hazard, is capped by `ε`. -/
theorem anchorUpperBound_of_isεExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {ε : ℝ} {m : ℕ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsεExactAnchoredSoloPeriodic reward ε w hazard h0 h1)
    (phase : Fin m) :
    hazard phase *
        (quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
            (finRotate m phase) (w phase) -
          reward (quittingSingletonTerminal (w phase)) (w phase)) ≤ ε := by
  have hroot : quittingAnchoredCyclicCycle w hazard h0 h1 phase =
      quittingSoloMixedRoot (w phase)
        (quittingHazardCoin (hazard phase) (h0 phase) (h1 phase)) := rfl
  have h := (hexact phase (w phase)).2
  rw [hroot] at h
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_soloMixedRoot_self,
    quittingRootContinuePayoff_soloMixedRoot_self] at h
  simp only [quittingSoloMixedRoot_self, quittingHazardCoin_true_toReal] at h
  nlinarith [h]

/-- The scheduled quitter's indifference, from below. -/
theorem anchorLowerBound_of_isεExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {ε : ℝ} {m : ℕ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsεExactAnchoredSoloPeriodic reward ε w hazard h0 h1)
    (phase : Fin m) :
    (1 - hazard phase) *
        (reward (quittingSingletonTerminal (w phase)) (w phase) -
          quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
            (finRotate m phase) (w phase)) ≤ ε := by
  have hroot : quittingAnchoredCyclicCycle w hazard h0 h1 phase =
      quittingSoloMixedRoot (w phase)
        (quittingHazardCoin (hazard phase) (h0 phase) (h1 phase)) := rfl
  have h := (hexact phase (w phase)).1
  rw [hroot] at h
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_soloMixedRoot_self,
    quittingRootContinuePayoff_soloMixedRoot_self] at h
  simp only [quittingSoloMixedRoot_self, quittingHazardCoin_false_toReal] at h
  nlinarith [h]

/-- The spectator floor at accuracy `ε`. -/
theorem spectatorFloor_of_isεExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {ε : ℝ} {m : ℕ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsεExactAnchoredSoloPeriodic reward ε w hazard h0 h1)
    (phase : Fin m) {who : ι} (hne : who ≠ w phase) :
    hazard phase *
          reward ⟨{w phase, who}, Finset.insert_nonempty (w phase) {who}⟩ who +
        (1 - hazard phase) * reward (quittingSingletonTerminal who) who ≤
      hazard phase * reward (quittingSingletonTerminal (w phase)) who +
        (1 - hazard phase) *
          quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
            (finRotate m phase) who + ε := by
  have hroot : quittingAnchoredCyclicCycle w hazard h0 h1 phase =
      quittingSoloMixedRoot (w phase)
        (quittingHazardCoin (hazard phase) (h0 phase) (h1 phase)) := rfl
  have h := (hexact phase who).1
  rw [hroot] at h
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_soloMixedRoot_of_ne _ _ hne,
    quittingRootContinuePayoff_soloMixedRoot_of_ne _ _ hne] at h
  rw [quittingSoloMixedRoot_of_ne hne] at h
  simp only [PMF.pure_apply_self, ENNReal.toReal_one, one_mul,
    quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal] at h
  linarith

/-- Exactness in the sense of `IsExactAnchoredSoloPeriodic` is exactly the
statement that at every phase no player gains by any deviation of the
one-stage root against the on-path continuation value of the next phase. -/
theorem isExactAnchoredSoloPeriodic_iff_rootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {m : ℕ}
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) :
    IsExactAnchoredSoloPeriodic reward w hazard h0 h1 ↔
      ∀ phase : Fin m,
        IsεQuittingRootNash reward
          (quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 (finRotate m phase))
          0 (quittingAnchoredCyclicCycle w hazard h0 h1 phase) :=
  forall_congr' fun _ ↦
    isεQuittingRootEndpointNash_iff_isεQuittingRootNash _ _ _ _

/-- The indifference anchor: at every phase the scheduled quitter's own solo
exit value equals the on-path continuation value of the next phase. -/
theorem anchor_of_isExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {m : ℕ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsExactAnchoredSoloPeriodic reward w hazard h0 h1)
    (hpos : ∀ k, 0 < hazard k) (hlt : ∀ k, hazard k < 1) (phase : Fin m) :
    reward (quittingSingletonTerminal (w phase)) (w phase) =
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
        (finRotate m phase) (w phase) := by
  have hup := anchorUpperBound_of_isεExactAnchoredSoloPeriodic hexact phase
  have hlo := anchorLowerBound_of_isεExactAnchoredSoloPeriodic hexact phase
  have hp := hpos phase
  have hq : 0 < 1 - hazard phase := sub_pos.mpr (hlt phase)
  have hle : quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
      (finRotate m phase) (w phase) -
      reward (quittingSingletonTerminal (w phase)) (w phase) ≤ 0 := by
    nlinarith [hup]
  have hge : reward (quittingSingletonTerminal (w phase)) (w phase) -
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
        (finRotate m phase) (w phase) ≤ 0 := by
    nlinarith [hlo]
  linarith

/-- The spectator floor: no player other than the scheduled quitter gains by
quitting at that phase. -/
theorem spectatorFloor_of_isExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {m : ℕ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsExactAnchoredSoloPeriodic reward w hazard h0 h1)
    (phase : Fin m) {who : ι} (hne : who ≠ w phase) :
    hazard phase *
          reward ⟨{w phase, who}, Finset.insert_nonempty (w phase) {who}⟩ who +
        (1 - hazard phase) * reward (quittingSingletonTerminal who) who ≤
      hazard phase * reward (quittingSingletonTerminal (w phase)) who +
        (1 - hazard phase) *
          quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
            (finRotate m phase) who := by
  have h := spectatorFloor_of_isεExactAnchoredSoloPeriodic hexact phase hne
  linarith

end GameTheory
