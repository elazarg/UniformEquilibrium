/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PeriodicWindows
import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic

/-!
# The anchored cyclic screen for single-quitter periodic schedules

The single-quitter periodic profile of a period `m`, a schedule
`w : Fin m → ι` of designated quitters (repetitions allowed), and a per-phase
quit hazard `hazard : Fin m → ℝ` is `quittingAnchoredCyclicProfile`, and its
exact on-path value is `quittingAnchoredCyclicOnPathValue`.  This file
evaluates that profile against a counterexample regime.

The **response cap** is the exact finite periodic best-response statistic of
the repository's evaluator: the larger of the refusal value and the best
deterministic stop inside one pass.  Against a periodic profile this
statistic is the supremum over *all* behavioral deviations.

The screen then says: in a counterexample regime, for *every* `(m, w, p)`,
some player's response cap beats the on-path value by the full terminal gap.
Contrapositively, exhibiting one schedule whose cap is everywhere at most
the on-path value excludes the table from every counterexample regime.

At accuracy zero the screen has a second reading.
`StochasticGame.isεAsymptoticNash_zero_iff_sSup_range_update_le` characterizes
exact asymptotic Nash by a supremum bound on unilateral deviations, and
`quittingAnchoredCyclicResponseCap_le_onPathValue_of_isεAsymptoticNash` turns
an exactly Nash anchored cyclic profile into the screen's contrapositive
hypothesis.  That route consumes the profile's Nash property; it does not
compute the response cap.

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

variable {m : ℕ}

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

/-! ## Exact asymptotic Nash as a supremum bound

Accuracy zero turns the family of Nash inequalities of
`StochasticGame.IsεAsymptoticNash` into a single bound on the supremum of the
deviation payoffs, because the on-path value bounds every deviation with no
slack to spare.
-/

namespace StochasticGame

/-- At accuracy zero, exact asymptotic Nash caps the supremum of a player's
unilateral deviation payoffs by its on-path value.  Boundedness of the
deviation range is not needed: the supremum is taken of a set every member of
which is already below the on-path value. -/
theorem sSup_range_update_le_of_isεAsymptoticNash_zero
    (G : StochasticGame ι) (u : G.BehaviorProfile → ι → ℝ)
    {σ : G.BehaviorProfile} (hnash : G.IsεAsymptoticNash u 0 σ) (who : ι) :
    sSup (Set.range fun deviation : G.BehaviorStrategy who ↦
        u (Function.update σ who deviation) who) ≤ u σ who := by
  refine csSup_le ⟨_, Set.mem_range_self (σ who)⟩ ?_
  rintro value ⟨deviation, rfl⟩
  simpa using hnash who deviation

/-- **Exact asymptotic Nash is a supremum bound.**  For a bounded deviation
range the converse holds too, so accuracy-zero asymptotic Nash is exactly the
statement that no player's deviation supremum exceeds its on-path value. -/
theorem isεAsymptoticNash_zero_iff_sSup_range_update_le
    (G : StochasticGame ι) (u : G.BehaviorProfile → ι → ℝ)
    (σ : G.BehaviorProfile)
    (hbdd : ∀ who, BddAbove (Set.range fun deviation : G.BehaviorStrategy who ↦
      u (Function.update σ who deviation) who)) :
    G.IsεAsymptoticNash u 0 σ ↔
      ∀ who, sSup (Set.range fun deviation : G.BehaviorStrategy who ↦
        u (Function.update σ who deviation) who) ≤ u σ who := by
  refine ⟨fun hnash ↦ sSup_range_update_le_of_isεAsymptoticNash_zero G u hnash,
    fun hsup who deviation ↦ ?_⟩
  have hle := le_csSup (hbdd who) (Set.mem_range_self deviation)
  simpa using hle.trans (hsup who)

end StochasticGame

/-- **An exactly Nash anchored cyclic profile has no response gain.**  If the
anchored cyclic profile of `(m, w, p)` is asymptotic Nash at accuracy zero for
the terminal payoff, then its exact finite response cap is everywhere at most
its on-path renewal value. -/
theorem quittingAnchoredCyclicResponseCap_le_onPathValue_of_isεAsymptoticNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) [NeZero m]
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingAnchoredCyclicProfile reward w hazard h0 h1))
    (who : ι) :
    quittingAnchoredCyclicResponseCap reward w hazard h0 h1 who ≤
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
        (quittingAnchoredCyclicStart m) who := by
  rw [← sSup_range_quittingTerminalPayoff_update_anchoredCyclicProfile reward w
    hazard h0 h1 who, ← quittingTerminalPayoff_anchoredCyclicProfile reward w
    hazard h0 h1]
  exact StochasticGame.sSup_range_update_le_of_isεAsymptoticNash_zero _ _ hnash who

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

/-- A table admitting one anchored cyclic profile that is asymptotic Nash at
accuracy zero for the terminal payoff carries no counterexample regime. -/
theorem isEmpty_of_anchoredCyclic_isεAsymptoticNash
    {m : ℕ} [NeZero m] (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingAnchoredCyclicProfile reward w hazard h0 h1)) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  isEmpty_of_anchoredCyclicCap_le w hazard h0 h1
    (quittingAnchoredCyclicResponseCap_le_onPathValue_of_isεAsymptoticNash reward
      w hazard h0 h1 hnash)

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
