/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PeriodicWindows
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot
import MathUE.PMFProduct.Update

/-!
# The anchored cyclic screen for single-quitter periodic schedules

Fix a period `m`, a schedule `w : Fin m → ι` of designated quitters
(repetitions allowed), and a per-phase quit hazard `hazard : Fin m → ℝ`.
The associated *single-quitter periodic profile* prescribes, at every stage
congruent to `k` modulo `m`, that `w k` quits with probability `hazard k`
while every other player continues.  This file evaluates that profile
exactly and screens it against a counterexample regime.

Two finite objects carry the analysis.

* The **on-path value** `U^k` is the profile's terminal payoff read from
  phase `k`.  It solves the linear renewal recursion
  `U^k = p_k * r({w k}) + (1 - p_k) * U^{k+1}` around the cycle.
* The **response cap** is the exact finite periodic best-response statistic
  of the repository's evaluator: the larger of the refusal value and the
  best deterministic stop inside one pass.  Against a periodic profile this
  statistic is the supremum over *all* behavioral deviations.

The screen then says: in a counterexample regime, for *every* `(m, w, p)`,
some player's response cap beats the on-path value by the full terminal gap.
Contrapositively, exhibiting one schedule whose cap is everywhere at most
the on-path value excludes the table from every counterexample regime.

The last section states the max-linear response system for the anchored
cyclic family and identifies it with the repository's Bellman cap recursion
along the periodic live path.  The passage from a solution of that system to
the evaluator's response cap is *not* proved here.  Its
deterministic-stop half is (`quittingAnchoredCyclicPhaseStop_le`); its
refusal half is carried as the explicit hypothesis `hrefusal` of
`exists_anchoredCyclicResponse_gain`.
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

/-- The exact finite response cap of the anchored cyclic profile: the larger
of the refusal value and the best deterministic stop in one pass. -/
def quittingAnchoredCyclicResponseCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) [NeZero m]
    (who : ι) : ℝ :=
  quittingPeriodicWindowBestResponseValue reward
    (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
      (quittingAnchoredCyclicStart m)) who m

/-- **The response cap is the exact behavioral best response.**  It is the
supremum of the terminal payoffs of *all* unilateral behavioral deviations
from the anchored cyclic profile, not merely of stopping times. -/
theorem sSup_range_quittingTerminalPayoff_update_anchoredCyclicProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) [NeZero m] (who : ι) :
    sSup (Set.range fun deviation :
        (quittingGame reward).BehaviorStrategy who ↦
      quittingTerminalPayoff reward
        (Function.update
          (quittingAnchoredCyclicProfile reward w hazard h0 h1) who
          deviation) who) =
      quittingAnchoredCyclicResponseCap reward w hazard h0 h1 who := by
  have hperiodic : ∀ time,
      quittingProfileLiveRoot reward
          (quittingAnchoredCyclicProfile reward w hazard h0 h1) (time + m) =
        quittingProfileLiveRoot reward
          (quittingAnchoredCyclicProfile reward w hazard h0 h1) time := by
    intro time
    unfold quittingAnchoredCyclicProfile
    rw [quittingProfileLiveRoot_cyclicBehaviorProfile]
    exact quittingCyclicRootSequence_add_period _ _ time
  rw [sSup_range_quittingTerminalPayoff_update_eq_periodicWindow
    reward _ who m hperiodic]
  unfold quittingAnchoredCyclicResponseCap quittingAnchoredCyclicProfile
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile]

/-! ## The screen -/

namespace QuittingCounterexampleRegime

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- **The anchored cyclic screen.**  In a counterexample regime, *every*
period `m`, *every* schedule `w` (repetitions allowed), and *every* hazard
vector leave some player whose exact finite response cap beats the on-path
renewal value by the full terminal gap.  No limit profiles and no `γ / 2`
loss. -/
theorem exists_anchoredCyclicCap_gain
    (regime : QuittingCounterexampleRegime reward)
    {m : ℕ} [NeZero m] (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) :
    ∃ who,
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
          (quittingAnchoredCyclicStart m) who + regime.terminalGap ≤
        quittingAnchoredCyclicResponseCap reward w hazard h0 h1 who := by
  have hperiodic : ∀ time,
      quittingProfileLiveRoot reward
          (quittingAnchoredCyclicProfile reward w hazard h0 h1) (time + m) =
        quittingProfileLiveRoot reward
          (quittingAnchoredCyclicProfile reward w hazard h0 h1) time := by
    intro time
    unfold quittingAnchoredCyclicProfile
    rw [quittingProfileLiveRoot_cyclicBehaviorProfile]
    exact quittingCyclicRootSequence_add_period _ _ time
  obtain ⟨who, hgain⟩ := regime.exists_periodicCap_gain
    (quittingAnchoredCyclicProfile reward w hazard h0 h1) m hperiodic
  refine ⟨who, ?_⟩
  rw [quittingTerminalPayoff_anchoredCyclicProfile] at hgain
  refine hgain.trans_eq ?_
  unfold quittingAnchoredCyclicResponseCap quittingAnchoredCyclicProfile
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile]

/-- **The contrapositive.**  A table carrying one anchored cyclic schedule
whose exact response cap is everywhere at most the on-path renewal value
carries no counterexample regime at all. -/
theorem isEmpty_of_anchoredCyclicCap_le
    {m : ℕ} [NeZero m] (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hexact : ∀ who,
      quittingAnchoredCyclicResponseCap reward w hazard h0 h1 who ≤
        quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
          (quittingAnchoredCyclicStart m) who) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  refine ⟨fun regime ↦ ?_⟩
  obtain ⟨who, hgain⟩ := regime.exists_anchoredCyclicCap_gain w hazard h0 h1
  linarith [hexact who, regime.terminalGap_pos]

end QuittingCounterexampleRegime

/-! ## The max-linear response system

The system below is the optimal-stopping fixed-point system `S` for the
anchored cyclic family.  It is *stated*, and identified with the repository's
Bellman cap recursion along the periodic live path.
-/

/-- The one-phase Quit value of `who` against the anchored cyclic root of
phase `k`. -/
def quittingAnchoredCyclicQuitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (phase : Fin m) (who : ι) : ℝ :=
  if who = w phase then reward (quittingSingletonTerminal who) who
  else
    hazard phase *
        reward ⟨{w phase, who}, Finset.insert_nonempty (w phase) {who}⟩ who +
      (1 - hazard phase) * reward (quittingSingletonTerminal who) who

/-- The one-phase Continue value of `who` against the anchored cyclic root
of phase `k`, using `next` from the following phase onwards. -/
def quittingAnchoredCyclicContinueValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (phase : Fin m) (who : ι)
    (next : ℝ) : ℝ :=
  if who = w phase then next
  else
    hazard phase * reward (quittingSingletonTerminal (w phase)) who +
      (1 - hazard phase) * next

/-- **The max-linear response system.**  A phase-indexed family `S` solves
the anchored cyclic optimal-stopping recursion. -/
def IsAnchoredCyclicResponseSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (S : Fin m → ι → ℝ) : Prop :=
  ∀ phase who,
    S phase who =
      max (quittingAnchoredCyclicQuitValue reward w hazard phase who)
        (quittingAnchoredCyclicContinueValue reward w hazard phase who
          (S (finRotate m phase) who))

/-- The one-phase Quit value is the repository's fixed-opponent quit value
along the anchored cyclic live path. -/
theorem quittingFixedOpponentsQuitValue_anchoredCyclic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (phase : Fin m) (who : ι) (time : ℕ) :
    quittingFixedOpponentsQuitValue reward
        (quittingCyclicRootSequence
          (quittingAnchoredCyclicCycle w hazard h0 h1) phase) who time =
      quittingAnchoredCyclicQuitValue reward w hazard
        (quittingCyclicOrbit phase time) who := by
  set step := quittingCyclicOrbit phase time with hstep
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward _ who 0 time,
    show quittingCyclicRootSequence
        (quittingAnchoredCyclicCycle w hazard h0 h1) phase time =
      quittingSoloMixedRoot (w step)
        (quittingHazardCoin (hazard step) (h0 step) (h1 step)) from rfl]
  unfold quittingAnchoredCyclicQuitValue
  by_cases hwho : who = w step
  · rw [hwho, quittingRootQuitPayoff_soloMixedRoot_self]
    simp
  · rw [quittingRootQuitPayoff_soloMixedRoot_of_ne reward _ hwho]
    simp [hwho]

/-- The one-phase Continue value is the repository's fixed-opponent continue
statistic along the anchored cyclic live path. -/
theorem quittingFixedOpponentsContinue_anchoredCyclic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (phase : Fin m) (who : ι) (time : ℕ) (next : ℝ) :
    quittingFixedOpponentsContinueReward reward
        (quittingCyclicRootSequence
          (quittingAnchoredCyclicCycle w hazard h0 h1) phase) who time +
        quittingFixedOpponentsContinueMass
          (quittingCyclicRootSequence
            (quittingAnchoredCyclicCycle w hazard h0 h1) phase) who time *
          next =
      quittingAnchoredCyclicContinueValue reward w hazard
        (quittingCyclicOrbit phase time) who next := by
  set step := quittingCyclicOrbit phase time with hstep
  set roots := quittingCyclicRootSequence
    (quittingAnchoredCyclicCycle w hazard h0 h1) phase with hroots
  have hstepRoot : roots time =
      quittingSoloMixedRoot (w step)
        (quittingHazardCoin (hazard step) (h0 step) (h1 step)) := rfl
  rw [← quittingRootContinuePayoff_eq_fixedOpponents reward roots who
    (fun _ ↦ next) time, hstepRoot]
  unfold quittingAnchoredCyclicContinueValue
  by_cases hwho : who = w step
  · rw [hwho, quittingRootContinuePayoff_soloMixedRoot_self]
    simp
  · rw [quittingRootContinuePayoff_soloMixedRoot_of_ne reward _ hwho]
    simp [hwho]

/-- **Identification of the max-linear system.**  A solution of the source
analysis's system, read along the periodic live path, is exactly a Bellman
cap in the repository's sense, coordinate by coordinate. -/
theorem isQuittingLiveBellmanCap_of_isAnchoredCyclicResponseSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (phase : Fin m) (who : ι) :
    IsQuittingLiveBellmanCap reward
      (quittingCyclicRootSequence
        (quittingAnchoredCyclicCycle w hazard h0 h1) phase) who
      (fun time ↦ S (quittingCyclicOrbit phase time) who) := by
  intro time
  rw [quittingLiveBellmanValue,
    quittingFixedOpponentsQuitValue_anchoredCyclic reward w hazard h0 h1
      phase who time,
    quittingFixedOpponentsContinue_anchoredCyclic reward w hazard h0 h1
      phase who time]
  rw [show quittingCyclicOrbit phase (time + 1) =
      finRotate m (quittingCyclicOrbit phase time) by
    rw [quittingCyclicOrbit_succ, finRotate_eq_quittingCyclicOrbit_one]]
  exact hS (quittingCyclicOrbit phase time) who

/-! ### The deterministic-stop half of the bridge -/

/-- **A Bellman cap dominates every deterministic stop.**  This is the
supersolution half of the optimal-stopping identification: it needs no
contraction, no periodicity, and no exactness of the prescribed root. -/
theorem quittingRootSequencePureTimeTerminalValue_le_of_bellmanCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cap : ℕ → ℝ)
    (hcap : IsQuittingLiveBellmanCap reward roots who cap)
    (start fuel : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some (start + fuel)) start ≤ cap start := by
  induction fuel generalizing start with
  | zero =>
      rw [Nat.add_zero,
        quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
      have hstep := hcap start
      rw [quittingLiveBellmanValue] at hstep
      have hquit := le_max_left
        (quittingFixedOpponentsQuitValue reward roots who start)
        (quittingFixedOpponentsContinueReward reward roots who start +
          quittingFixedOpponentsContinueMass roots who start * cap (start + 1))
      rw [← hstep] at hquit
      exact hquit
  | succ fuel ih =>
      have hne : start ≠ start + (fuel + 1) := by omega
      have hidx : start + (fuel + 1) = start + 1 + fuel := by omega
      have htail : quittingRootSequenceHazardTerminalValue reward roots who
          (quittingPureTimeHazard (some (start + (fuel + 1)))) (start + 1) ≤
          cap (start + 1) := by
        simpa only [quittingRootSequencePureTimeTerminalValue, hidx]
          using ih (start + 1)
      have hmass : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      have hstep := hcap start
      rw [quittingLiveBellmanValue] at hstep
      have hcontinue := le_max_right
        (quittingFixedOpponentsQuitValue reward roots who start)
        (quittingFixedOpponentsContinueReward reward roots who start +
          quittingFixedOpponentsContinueMass roots who start * cap (start + 1))
      rw [← hstep] at hcontinue
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
        quittingPureTimeHazard_some_of_ne hne]
      simp only [PMF.pure_apply, if_neg (by decide : (true : Bool) ≠ false),
        ENNReal.toReal_zero, if_true, ENNReal.toReal_one, zero_mul, one_mul]
      have hscaled := mul_le_mul_of_nonneg_left htail hmass
      linarith

/-- Every deterministic stop against the anchored cyclic profile is capped
by a solution of the max-linear response system. -/
theorem quittingAnchoredCyclicPureTime_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (phase : Fin m) (who : ι) (start fuel : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward
        (quittingCyclicRootSequence
          (quittingAnchoredCyclicCycle w hazard h0 h1) phase) who
        (some (start + fuel)) start ≤
      S (quittingCyclicOrbit phase start) who :=
  quittingRootSequencePureTimeTerminalValue_le_of_bellmanCap reward _ who
    (fun time ↦ S (quittingCyclicOrbit phase time) who)
    (isQuittingLiveBellmanCap_of_isAnchoredCyclicResponseSolution reward w hazard
      h0 h1 S hS phase who) start fuel

/-- Every phase stop of one pass is capped by a solution of the max-linear
response system. -/
theorem quittingAnchoredCyclicPhaseStop_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) [NeZero m]
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (who : ι) (stop : Fin m) :
    quittingPeriodicWindowPhaseStopValue reward
        (quittingCyclicRootSequence
          (quittingAnchoredCyclicCycle w hazard h0 h1)
          (quittingAnchoredCyclicStart m)) who stop ≤
      S (quittingAnchoredCyclicStart m) who := by
  have hbound := quittingAnchoredCyclicPureTime_le reward w hazard h0 h1 S hS
    (quittingAnchoredCyclicStart m) who 0 stop.val
  simpa [quittingPeriodicWindowPhaseStopValue, quittingCyclicOrbit_zero]
    using hbound

/-- **The screen against the max-linear system.**  Given a solution `S` of
`IsAnchoredCyclicResponseSolution` whose refusal branch is also dominated, a
counterexample regime forces some player to satisfy `S⁰ ≥ U⁰ + γ`.

`hrefusal` is the one step of the bridge that is not proved here: the
deterministic-stop half is `quittingAnchoredCyclicPhaseStop_le` above. -/
theorem exists_anchoredCyclicResponse_gain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward)
    {m : ℕ} [NeZero m] (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (hrefusal : ∀ who,
      quittingPeriodicWindowRefusalValue reward
          (quittingCyclicRootSequence
            (quittingAnchoredCyclicCycle w hazard h0 h1)
            (quittingAnchoredCyclicStart m)) who ≤
        S (quittingAnchoredCyclicStart m) who) :
    ∃ who,
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
          (quittingAnchoredCyclicStart m) who + regime.terminalGap ≤
        S (quittingAnchoredCyclicStart m) who := by
  obtain ⟨who, hgain⟩ := regime.exists_anchoredCyclicCap_gain w hazard h0 h1
  refine ⟨who, hgain.trans ?_⟩
  unfold quittingAnchoredCyclicResponseCap quittingPeriodicWindowBestResponseValue
  refine max_le (hrefusal who) ?_
  unfold quittingPeriodicWindowBestPhaseStop
  refine Finset.sup'_le _ _ fun stop _ ↦ ?_
  exact quittingAnchoredCyclicPhaseStop_le reward w hazard h0 h1 S hS who stop

end GameTheory
