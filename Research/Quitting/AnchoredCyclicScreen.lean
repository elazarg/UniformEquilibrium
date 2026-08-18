/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PeriodicWindows
import UniformEquilibrium.Quitting.Bellman.Finite.BellmanCapPureTimeStop
import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic
import UniformEquilibrium.Quitting.Cycles.PeriodicRootResponseSystem

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

The first section reads the spectator half of exact root Nash as a hazard
threshold.  `quittingSoloCollisionPenalty` and `quittingContinuationSurplus`
name the two reward differences the condition compares, and
`hazard_mul_penalty_le_iff_ratio_le` turns the comparison into the ceiling
`p / (1 - p) ≤ surplus / penalty` on a positive penalty below sure quitting.
A nonpositive penalty drops the constraint only against a nonnegative surplus
(`hazard_mul_penalty_le_of_penalty_nonpos`), and at `p = 1` the constraint is
the sign of the penalty alone.  The owner half is sharpened the same way:
`isZeroQuittingRootEndpointNash_soloMixedRoot_of_ownerSigns` asks only for the
two signed endpoint conditions, so a deterministic phase carries a one-sided
inequality rather than indifference
(`isZeroQuittingRootEndpointNash_anchoredCyclicCycle_of_pureQuit` and its
sure-continue companion).

At accuracy zero the screen has a second reading.
`StochasticGame.isεAsymptoticNash_zero_iff_sSup_range_update_le` characterizes
exact asymptotic Nash by a supremum bound on unilateral deviations, and
`quittingAnchoredCyclicResponseCap_le_onPathValue_of_isεAsymptoticNash` turns
an exactly Nash anchored cyclic profile into the screen's contrapositive
hypothesis.  That route consumes the profile's Nash property; it does not
compute the response cap.

The last section states the max-linear response system for the anchored
cyclic family and identifies it with the general periodic response system
`IsQuittingCyclicResponseSolution`, of which it is the single-quitter case
(`isQuittingCyclicResponseSolution_of_isAnchoredCyclicResponseSolution`), and
hence with the repository's Bellman cap recursion along the periodic live path.
It also records the matching lower bound
`quittingAnchoredCyclicQuitValue_le_responseCap`: quitting at the opening phase
is one of the deviations the cap ranges over, so a schedule whose opening quit
value already beats its on-path value is rejected.  Two consequences of that
lower bound are recorded with it.  On a table whose quit-now row at a player is
flat — the same payoff alone as alongside the phase's scheduled quitter — that
payoff is a best-reply floor (`le_quittingBestReplyValue_of_flatQuitRow`).  And
against an `ε`-exact anchored solo-periodic profile the quit-now value exceeds
the on-path value by at most `ε`, at every phase and for every player
(`quittingAnchoredCyclicQuitValue_le_onPathValue_add_of_isεExactAnchoredSoloPeriodic`),
so a flat quit-now row at `c` gives every on-path coordinate the floor `c - ε`.
The passage from a solution
of that system to the evaluator's response cap splits into two halves.  The
deterministic-stop half is `quittingAnchoredCyclicPhaseStop_le`.
The refusal half is carried here as the explicit hypothesis `hrefusal` of
`exists_anchoredCyclicResponse_gain`, and is discharged in
`Research/Quitting/AnchoredCyclicRenewal.lean`: the refusal identity evaluates
refusal against an anchored cyclic profile as the on-path value of the same
schedule with the refuser's own phases zeroed, which gives
`quittingAnchoredCyclicResponseCap_le_of_response`.  Its one residual — a
player owning every phase that carries positive hazard needs a nonnegative
solution coordinate — is removed by the spectator condition in
`quittingAnchoredCyclicResponseCap_le_of_response_of_spectatorHazard` and
`exists_anchoredCyclicResponse_gain_of_exists_spectatorHazard`.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The spectator incentive inequality as a hazard threshold

The spectator hypothesis of `isZeroQuittingRootEndpointNash_soloMixedRoot`
compares two mixtures.  Cancelling the common terms leaves a comparison of two
reward differences weighted by the owner's quit and continue probabilities:
hazard times a *collision penalty* against survival times a *continuation
surplus*.  Both differences are properties of the table and the declared tail
alone, so the condition reads as an explicit ceiling on the phase hazard.
-/

/-- What `who` loses by quitting alongside a solo exit owned by `owner`
instead of standing outside it. -/
def quittingSoloCollisionPenalty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner who : ι) : ℝ :=
  reward ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who -
    reward (quittingSingletonTerminal owner) who

/-- What `who` gains by staying for the declared tail instead of taking its own
solo exit. -/
def quittingContinuationSurplus
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (who : ι) : ℝ :=
  tail who - reward (quittingSingletonTerminal who) who

omit [Fintype ι] in
/-- **The spectator hypothesis, rearranged.**  Cancelling the common singleton
and tail terms turns the mixture comparison into hazard times the collision
penalty against survival times the continuation surplus. -/
theorem quittingSoloSpectatorCap_iff_hazard_mul_penalty_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (owner who : ι) (marginal : PMF Bool) :
    ((marginal true).toReal *
            reward ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who +
          (marginal false).toReal *
            reward (quittingSingletonTerminal who) who ≤
        (marginal true).toReal * reward (quittingSingletonTerminal owner) who +
          (marginal false).toReal * tail who) ↔
      (marginal true).toReal * quittingSoloCollisionPenalty reward owner who ≤
        (marginal false).toReal * quittingContinuationSurplus reward tail who := by
  unfold quittingSoloCollisionPenalty quittingContinuationSurplus
  constructor <;> intro hcap <;> nlinarith [hcap]

omit [Fintype ι] [DecidableEq ι] in
/-- **The threshold form.**  Against a positive collision penalty and below
sure quitting, the spectator constraint is an explicit ceiling on the odds of
the phase hazard. -/
theorem hazard_mul_penalty_le_iff_ratio_le {hazard penalty surplus : ℝ}
    (hlt : hazard < 1) (hpenalty : 0 < penalty) :
    hazard * penalty ≤ (1 - hazard) * surplus ↔
      hazard / (1 - hazard) ≤ surplus / penalty := by
  have hsurvival : 0 < 1 - hazard := by linarith
  rw [div_le_div_iff₀ hsurvival hpenalty]
  constructor <;> intro hbound <;> nlinarith [hbound]

omit [Fintype ι] [DecidableEq ι] in
/-- A nonpositive collision penalty against a nonnegative continuation surplus
imposes no constraint at all: joining the exit never pays and staying never
costs. -/
theorem hazard_mul_penalty_le_of_penalty_nonpos {hazard penalty surplus : ℝ}
    (h0 : 0 ≤ hazard) (h1 : hazard ≤ 1) (hpenalty : penalty ≤ 0)
    (hsurplus : 0 ≤ surplus) :
    hazard * penalty ≤ (1 - hazard) * surplus :=
  le_trans (mul_nonpos_of_nonneg_of_nonpos h0 hpenalty)
    (mul_nonneg (by linarith) hsurplus)

omit [Fintype ι] [DecidableEq ι] in
/-- At a sure-quit phase the constraint degenerates to the sign of the
collision penalty: the continuation surplus is never reached. -/
theorem hazard_mul_penalty_le_one_iff {penalty surplus : ℝ} :
    (1 : ℝ) * penalty ≤ (1 - 1) * surplus ↔ penalty ≤ 0 := by
  constructor <;> intro hbound <;> linarith [hbound]

/-! ### The owner's condition at a deterministic phase -/

/-- **The sharp owner condition.**  Exact root Nash needs only the signed
endpoint conditions the definition asks for: quitting must be weakly better
where the owner puts Quit mass, and weakly worse where it puts Continue mass.
Indifference is what those two force when both masses are positive. -/
theorem isZeroQuittingRootEndpointNash_soloMixedRoot_of_ownerSigns
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (owner : ι) (marginal : PMF Bool)
    (hquit : 0 ≤ (marginal true).toReal *
      (reward (quittingSingletonTerminal owner) owner - tail owner))
    (hcontinue : (marginal false).toReal *
      (reward (quittingSingletonTerminal owner) owner - tail owner) ≤ 0)
    (hspectator : ∀ who, who ≠ owner →
      (marginal true).toReal * quittingSoloCollisionPenalty reward owner who ≤
        (marginal false).toReal * quittingContinuationSurplus reward tail who) :
    IsεQuittingRootEndpointNash reward tail 0
      (quittingSoloMixedRoot owner marginal) := by
  intro who
  by_cases hwho : who = owner
  · subst hwho
    have hdiff : quittingRootEndpointDifference reward tail
        (quittingSoloMixedRoot who marginal) who =
          reward (quittingSingletonTerminal who) who - tail who := by
      rw [quittingRootEndpointDifference,
        quittingRootQuitPayoff_soloMixedRoot_self,
        quittingRootContinuePayoff_soloMixedRoot_self]
    rw [quittingSoloMixedRoot_self, hdiff]
    exact ⟨hcontinue, by simpa using hquit⟩
  · have hcap := (quittingSoloSpectatorCap_iff_hazard_mul_penalty_le reward tail
      owner who marginal).2 (hspectator who hwho)
    have hdiff : quittingRootEndpointDifference reward tail
        (quittingSoloMixedRoot owner marginal) who ≤ 0 := by
      rw [quittingRootEndpointDifference,
        quittingRootQuitPayoff_soloMixedRoot_of_ne reward tail hwho,
        quittingRootContinuePayoff_soloMixedRoot_of_ne reward tail hwho]
      linarith [hcap]
    rw [quittingSoloMixedRoot_of_ne hwho]
    exact ⟨by simpa using hdiff, by simp⟩

/-- **A sure-quit phase needs only one inequality from its owner.**  Where the
owner quits with probability one, exact root Nash asks that its solo exit be
weakly better than the declared tail, not that the two agree. -/
theorem isZeroQuittingRootEndpointNash_soloMixedRoot_of_pureQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (owner : ι) (marginal : PMF Bool)
    (hpure : (marginal false).toReal = 0)
    (howner : tail owner ≤ reward (quittingSingletonTerminal owner) owner)
    (hspectator : ∀ who, who ≠ owner →
      quittingSoloCollisionPenalty reward owner who ≤ 0) :
    IsεQuittingRootEndpointNash reward tail 0
      (quittingSoloMixedRoot owner marginal) := by
  have hmass : (marginal true).toReal = 1 := by
    have hsum : (marginal false).toReal + (marginal true).toReal = 1 := by
      simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one marginal
    linarith
  refine isZeroQuittingRootEndpointNash_soloMixedRoot_of_ownerSigns reward tail
    owner marginal ?_ ?_ fun who hwho ↦ ?_
  · rw [hmass]
    linarith
  · rw [hpure]
    linarith
  · rw [hmass, hpure]
    linarith [hspectator who hwho]

/-- **A sure-continue phase needs only the reverse inequality.**  Where the
owner never quits, exact root Nash asks that its solo exit be weakly worse than
the declared tail, and every spectator's continuation surplus be nonnegative. -/
theorem isZeroQuittingRootEndpointNash_soloMixedRoot_of_pureContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (owner : ι) (marginal : PMF Bool)
    (hpure : (marginal true).toReal = 0)
    (howner : reward (quittingSingletonTerminal owner) owner ≤ tail owner)
    (hspectator : ∀ who, who ≠ owner →
      0 ≤ quittingContinuationSurplus reward tail who) :
    IsεQuittingRootEndpointNash reward tail 0
      (quittingSoloMixedRoot owner marginal) := by
  have hmass : (marginal false).toReal = 1 := by
    have hsum : (marginal false).toReal + (marginal true).toReal = 1 := by
      simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one marginal
    linarith
  refine isZeroQuittingRootEndpointNash_soloMixedRoot_of_ownerSigns reward tail
    owner marginal ?_ ?_ fun who hwho ↦ ?_
  · rw [hpure]
    linarith
  · rw [hmass]
    linarith
  · rw [hmass, hpure]
    linarith [hspectator who hwho]

variable {m : ℕ}

/-- The anchored cyclic root of a sure-quit phase is exactly Nash against a
declared tail as soon as its owner weakly prefers its own solo exit and no
spectator gains by joining that exit. -/
theorem isZeroQuittingRootEndpointNash_anchoredCyclicCycle_of_pureQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (tail : Payoff ι) (phase : Fin m) (hpure : hazard phase = 1)
    (howner : tail (w phase) ≤
      reward (quittingSingletonTerminal (w phase)) (w phase))
    (hspectator : ∀ who, who ≠ w phase →
      quittingSoloCollisionPenalty reward (w phase) who ≤ 0) :
    IsεQuittingRootEndpointNash reward tail 0
      (quittingAnchoredCyclicCycle w hazard h0 h1 phase) :=
  isZeroQuittingRootEndpointNash_soloMixedRoot_of_pureQuit reward tail (w phase)
    _ (by simp [hpure]) howner hspectator

/-- The anchored cyclic root of a sure-continue phase is exactly Nash against a
declared tail as soon as its owner weakly prefers the tail and every spectator's
continuation surplus is nonnegative. -/
theorem isZeroQuittingRootEndpointNash_anchoredCyclicCycle_of_pureContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (tail : Payoff ι) (phase : Fin m) (hpure : hazard phase = 0)
    (howner : reward (quittingSingletonTerminal (w phase)) (w phase) ≤
      tail (w phase))
    (hspectator : ∀ who, who ≠ w phase →
      0 ≤ quittingContinuationSurplus reward tail who) :
    IsεQuittingRootEndpointNash reward tail 0
      (quittingAnchoredCyclicCycle w hazard h0 h1 phase) :=
  isZeroQuittingRootEndpointNash_soloMixedRoot_of_pureContinue reward tail
    (w phase) _ (by simp [hpure]) howner hspectator

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

/-- The anchored cyclic response cap is the periodic response cap of the
anchored cyclic cycle read from its opening phase. -/
theorem quittingAnchoredCyclicResponseCap_eq_quittingCyclicResponseCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) [NeZero m] (who : ι) :
    quittingAnchoredCyclicResponseCap reward w hazard h0 h1 who =
      quittingCyclicResponseCap reward (quittingAnchoredCyclicCycle w hazard h0 h1)
        (quittingAnchoredCyclicStart m) who := rfl

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

The three declarations of this section constrain the hazard vector nowhere.
The one-phase Quit and Continue values are affine in `hazard phase` and the
solution predicate is their fixed-point equation, so all three are defined, and
the system is solvable or not, for an arbitrary real hazard vector.  The range
matters only at the passage from a solution to a Bellman cap, which evaluates
the actual root sequence and so needs each per-phase coin to be a probability.
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

/-! ### The anchored system is the general cyclic system

`IsQuittingCyclicResponseSolution` states the max-linear response system for an
arbitrary cycle of product rows.  The anchored cyclic family is the
single-quitter case, and the two scalar formulas
`quittingAnchoredCyclicQuitValue` and `quittingAnchoredCyclicContinueValue`
evaluate the general branches at a solo mixed row.
-/

/-- The general Quit branch of an anchored cyclic row is the scalar one-phase
Quit value.  The declared tail does not enter: quitting ends the play. -/
theorem quittingRootQuitPayoff_anchoredCyclicCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (phase : Fin m) (who : ι) :
    quittingRootQuitPayoff reward tail
        (quittingAnchoredCyclicCycle w hazard h0 h1 phase) who =
      quittingAnchoredCyclicQuitValue reward w hazard phase who := by
  rw [show quittingAnchoredCyclicCycle w hazard h0 h1 phase =
    quittingSoloMixedRoot (w phase)
      (quittingHazardCoin (hazard phase) (h0 phase) (h1 phase)) from rfl]
  unfold quittingAnchoredCyclicQuitValue
  by_cases hwho : who = w phase
  · rw [hwho, quittingRootQuitPayoff_soloMixedRoot_self]
    simp
  · rw [quittingRootQuitPayoff_soloMixedRoot_of_ne reward _ hwho]
    simp [hwho]

/-- The general Continue branch of an anchored cyclic row is the scalar
one-phase Continue value, evaluated at the declared tail's own coordinate. -/
theorem quittingRootContinuePayoff_anchoredCyclicCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (phase : Fin m) (who : ι) :
    quittingRootContinuePayoff reward tail
        (quittingAnchoredCyclicCycle w hazard h0 h1 phase) who =
      quittingAnchoredCyclicContinueValue reward w hazard phase who (tail who) := by
  rw [show quittingAnchoredCyclicCycle w hazard h0 h1 phase =
    quittingSoloMixedRoot (w phase)
      (quittingHazardCoin (hazard phase) (h0 phase) (h1 phase)) from rfl]
  unfold quittingAnchoredCyclicContinueValue
  by_cases hwho : who = w phase
  · rw [hwho, quittingRootContinuePayoff_soloMixedRoot_self]
    simp
  · rw [quittingRootContinuePayoff_soloMixedRoot_of_ne reward _ hwho]
    simp [hwho]

/-- **The anchored response system is the general one.**  A solution of the
single-quitter scalar recursion solves the max-linear response system of the
anchored cyclic cycle, so every bound proved for arbitrary product cycles
applies to it. -/
theorem isQuittingCyclicResponseSolution_of_isAnchoredCyclicResponseSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) {S : Fin m → ι → ℝ}
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S) :
    IsQuittingCyclicResponseSolution reward
      (quittingAnchoredCyclicCycle w hazard h0 h1) S := by
  intro phase who
  rw [quittingRootQuitPayoff_anchoredCyclicCycle reward _ w hazard h0 h1 phase who,
    quittingRootContinuePayoff_anchoredCyclicCycle reward _ w hazard h0 h1 phase who]
  exact hS phase who

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
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward _ who 0 time]
  exact quittingRootQuitPayoff_anchoredCyclicCycle reward 0 w hazard h0 h1 _ who

/-- **The response cap dominates quitting at once.**  A lower bound on the
exact finite best-response statistic: stopping at the opening phase is one of
the deviations the cap ranges over.  This is what lets the screen *reject* a
schedule, not only certify one. -/
theorem quittingAnchoredCyclicQuitValue_le_responseCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) [NeZero m] (who : ι) :
    quittingAnchoredCyclicQuitValue reward w hazard
        (quittingAnchoredCyclicStart m) who ≤
      quittingAnchoredCyclicResponseCap reward w hazard h0 h1 who := by
  have hstop : quittingPeriodicWindowPhaseStopValue reward
      (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
        (quittingAnchoredCyclicStart m)) who (quittingAnchoredCyclicStart m) =
      quittingAnchoredCyclicQuitValue reward w hazard
        (quittingAnchoredCyclicStart m) who := by
    show quittingRootSequencePureTimeTerminalValue reward
      (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
        (quittingAnchoredCyclicStart m)) who (some 0) 0 = _
    rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
      quittingFixedOpponentsQuitValue_anchoredCyclic, quittingCyclicOrbit_zero]
  unfold quittingAnchoredCyclicResponseCap quittingPeriodicWindowBestResponseValue
  refine le_trans (le_of_eq hstop.symm) (le_trans ?_ (le_max_right _ _))
  exact Finset.le_sup' _ (Finset.mem_univ (quittingAnchoredCyclicStart m))

/-! ### A flat quit-now row -/

omit [Fintype ι] in
/-- **A flat quit-now row evaluates the one-phase Quit value.**  If quitting
pays `who` the amount `c` both alone and alongside the phase's scheduled
quitter, then quitting at that phase pays `c`, for every schedule and every
hazard.  Only the scheduled quitter's pair row enters, and only when `who` is
not that quitter. -/
theorem quittingAnchoredCyclicQuitValue_eq_of_flatQuitRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (phase : Fin m) {who : ι} {c : ℝ}
    (hself : reward (quittingSingletonTerminal who) who = c)
    (hpair : who ≠ w phase →
      reward ⟨{w phase, who}, Finset.insert_nonempty (w phase) {who}⟩ who = c) :
    quittingAnchoredCyclicQuitValue reward w hazard phase who = c := by
  unfold quittingAnchoredCyclicQuitValue
  by_cases hwho : who = w phase
  · rw [if_pos hwho, hself]
  · rw [if_neg hwho, hpair hwho, hself]
    ring

omit [Fintype ι] in
/-- At an idle phase quitting pays `who` its own solo exit, whatever the
schedule: nobody else is quitting to collide with. -/
theorem quittingAnchoredCyclicQuitValue_of_hazard_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (phase : Fin m) (who : ι)
    (hzero : hazard phase = 0) :
    quittingAnchoredCyclicQuitValue reward w hazard phase who =
      reward (quittingSingletonTerminal who) who := by
  unfold quittingAnchoredCyclicQuitValue
  rw [hzero]
  split_ifs with hwho
  · rfl
  · ring

/-- **The behavioral supremum dominates quitting at once.**  Stopping at the
opening phase is one of the deviations the best-reply value ranges over. -/
theorem quittingAnchoredCyclicQuitValue_le_quittingBestReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) [NeZero m] (who : ι) :
    quittingAnchoredCyclicQuitValue reward w hazard
        (quittingAnchoredCyclicStart m) who ≤
      quittingBestReplyValue reward
        (quittingAnchoredCyclicProfile reward w hazard h0 h1) who := by
  have hcap := quittingAnchoredCyclicQuitValue_le_responseCap reward w hazard
    h0 h1 who
  have hsup := sSup_range_quittingTerminalPayoff_update_anchoredCyclicProfile
    reward w hazard h0 h1 who
  show _ ≤ ⨆ deviation, _
  rw [show (⨆ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward
        (Function.update (quittingAnchoredCyclicProfile reward w hazard h0 h1)
          who deviation) who) =
      sSup (Set.range fun deviation :
          (quittingGame reward).BehaviorStrategy who ↦
        quittingTerminalPayoff reward
          (Function.update (quittingAnchoredCyclicProfile reward w hazard h0 h1)
            who deviation) who) from rfl, hsup]
  exact hcap

/-- **A flat quit-now row is a best-reply floor.**  Composing the flat row at
the opening phase with the quit-now lower bound: no player's best reply against
an anchored cyclic profile pays it less than the flat value. -/
theorem le_quittingBestReplyValue_of_flatQuitRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) [NeZero m] {who : ι}
    {c : ℝ} (hself : reward (quittingSingletonTerminal who) who = c)
    (hpair : who ≠ w (quittingAnchoredCyclicStart m) →
      reward ⟨{w (quittingAnchoredCyclicStart m), who},
          Finset.insert_nonempty (w (quittingAnchoredCyclicStart m)) {who}⟩ who =
        c) :
    c ≤ quittingBestReplyValue reward
      (quittingAnchoredCyclicProfile reward w hazard h0 h1) who := by
  have hquit := quittingAnchoredCyclicQuitValue_le_quittingBestReplyValue reward
    w hazard h0 h1 who
  rwa [quittingAnchoredCyclicQuitValue_eq_of_flatQuitRow reward w hazard
    (quittingAnchoredCyclicStart m) hself hpair] at hquit

/-! ### The one-stage floor of an `ε`-exact profile -/

/-- **The one-stage floor.**  Against an `ε`-exact anchored solo-periodic
profile the quit-now value exceeds the on-path value by at most `ε`, at every
phase and for every player.  The scheduled quitter's own coordinate is its
lower endpoint condition read through the renewal identity; every other
coordinate is the spectator floor.  No hazard positivity and no condition on
the table enter. -/
theorem quittingAnchoredCyclicQuitValue_le_onPathValue_add_of_isεExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {ε : ℝ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsεExactAnchoredSoloPeriodic reward ε w hazard h0 h1)
    (phase : Fin m) (who : ι) :
    quittingAnchoredCyclicQuitValue reward w hazard phase who ≤
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase who + ε := by
  have hren := quittingAnchoredCyclicOnPathValue_renewal reward w hazard h0 h1
    phase who
  unfold quittingAnchoredCyclicQuitValue
  by_cases hwho : who = w phase
  · subst hwho
    rw [if_pos rfl]
    linarith [anchorLowerBound_of_isεExactAnchoredSoloPeriodic hexact phase]
  · rw [if_neg hwho]
    linarith [spectatorFloor_of_isεExactAnchoredSoloPeriodic hexact phase hwho]

/-- **The value floor of a flat quit-now row.**  On a table whose quit-now row
at `who` is flat at `c`, every on-path coordinate of an `ε`-exact anchored
solo-periodic profile is at least `c - ε`, at every phase. -/
theorem sub_le_quittingAnchoredCyclicOnPathValue_of_flatQuitRow
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {ε c : ℝ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1} {who : ι}
    (hself : reward (quittingSingletonTerminal who) who = c)
    (hexact : IsεExactAnchoredSoloPeriodic reward ε w hazard h0 h1)
    (phase : Fin m)
    (hpair : who ≠ w phase →
      reward ⟨{w phase, who}, Finset.insert_nonempty (w phase) {who}⟩ who = c) :
    c - ε ≤ quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase who := by
  have hquit :=
    quittingAnchoredCyclicQuitValue_le_onPathValue_add_of_isεExactAnchoredSoloPeriodic
      hexact phase who
  rw [quittingAnchoredCyclicQuitValue_eq_of_flatQuitRow reward w hazard phase
    hself hpair] at hquit
  linarith

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
  rw [← quittingRootContinuePayoff_eq_fixedOpponents reward
    (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1) phase)
    who (fun _ ↦ next) time]
  exact quittingRootContinuePayoff_anchoredCyclicCycle reward (fun _ ↦ next) w hazard
    h0 h1 _ who

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
      (fun time ↦ S (quittingCyclicOrbit phase time) who) :=
  isQuittingLiveBellmanCap_of_isQuittingCyclicResponseSolution
    (isQuittingCyclicResponseSolution_of_isAnchoredCyclicResponseSolution reward w
      hazard h0 h1 hS) phase who

/-! ### The deterministic-stop half of the bridge -/

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
  quittingRootSequencePureTimeTerminalValue_le_of_bellmanSupersolution reward _ who
    (fun time ↦ S (quittingCyclicOrbit phase time) who)
    (isQuittingLiveBellmanCap_of_isAnchoredCyclicResponseSolution reward w hazard
      h0 h1 S hS phase who).supersolution start fuel

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
      S (quittingAnchoredCyclicStart m) who :=
  quittingPeriodicWindowPhaseStopValue_le_of_isQuittingCyclicResponseSolution
    (isQuittingCyclicResponseSolution_of_isAnchoredCyclicResponseSolution reward w
      hazard h0 h1 hS) (quittingAnchoredCyclicStart m) who stop

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
