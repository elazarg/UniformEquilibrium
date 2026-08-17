/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.SoloTailExactStructure
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification

/-!
# Benevolent sink soloists and the screen they supply

A coordinate `owner` is a *benevolent sink soloist*
(`QuittingBenevolentSinkSoloist`) when its own singleton reward is
nonnegative, it preempts nobody even weakly -- every other coordinate likes
the owner's solo exit at least as much as its own -- and, at every coordinate
that is exactly indifferent between the two exits, joining the owner is not
tempting.

Such a coordinate produces an exact terminal equilibrium of the quitting game
at some positive rate: the rate feasibility question of
`QuittingSoloQuitterCriterion` is a finite intersection of half-lines through
the origin, and the equality clause is exactly what keeps every half-line from
degenerating to `{0}`.  A positive terminal exploitability gap therefore
excludes benevolent sink soloists outright, which is a screen on reward
tables that does not pass through any viability threshold.

* `exists_rate_quittingSoloQuitterCriterion_of_benevolentSink`: a feasible
  positive rate exists.
* `exists_hazard_isεAsymptoticNash_of_benevolentSink`: the corresponding solo
  stationary profile is an exact terminal equilibrium.
* `not_quittingBenevolentSinkSoloist_of_terminalExploitabilityGap`: the
  screen.
* `exists_weakPreemption_or_collisionTemptation_of_terminalExploitabilityGap`:
  its positive form, listing the two ways a nonnegative soloist can fail to be
  a benevolent sink.
-/

noncomputable section

namespace GameTheory

open StochasticGame QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The table condition -/

/-- `owner` is a **benevolent sink soloist**: its own exit pays it
nonnegatively, no other coordinate is preempted by it even weakly, and where
a coordinate is exactly indifferent between its own exit and the owner's,
colliding with the owner is no better. -/
def QuittingBenevolentSinkSoloist
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : Prop :=
  0 ≤ quittingSoloReward reward owner owner ∧
    (∀ other, other ≠ owner →
      quittingSoloReward reward other other ≤
        quittingSoloReward reward owner other) ∧
    ∀ other, other ≠ owner →
      quittingSoloReward reward other other =
          quittingSoloReward reward owner other →
        quittingSingletonCollisionReward reward owner other ≤
          quittingSoloReward reward other other

/-- The sink clause of a benevolent sink soloist is exactly nonnegativity of
its column of the normalized solo matrix. -/
theorem quittingBenevolentSinkSoloist_sink_iff_normalizedSoloMatrix_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner other : ι) :
    quittingSoloReward reward other other ≤
        quittingSoloReward reward owner other ↔
      0 ≤ normalizedSoloMatrix reward other owner := by
  rw [normalizedSoloMatrix_eq_soloReward_sub]
  constructor <;> intro h <;> linarith

/-! ## A feasible positive rate -/

/-- The largest rate at which `other` tolerates the owner's solo exit, or `1`
when `other` tolerates every rate. -/
private def benevolentSinkThreshold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner other : ι) :
    ℝ :=
  if 0 < quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward other other then
    (quittingSoloReward reward owner other -
        quittingSoloReward reward other other) /
      (quittingSingletonCollisionReward reward owner other -
        quittingSoloReward reward other other)
  else 1

omit [Fintype ι] in
private theorem benevolentSinkThreshold_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {owner other : ι}
    (hsink : QuittingBenevolentSinkSoloist reward owner) :
    0 < benevolentSinkThreshold reward owner other := by
  unfold benevolentSinkThreshold
  split_ifs with htempt
  · by_cases hother : other = owner
    · subst other
      rw [quittingSingletonCollisionReward] at htempt
      simp only [quittingSoloReward] at htempt ⊢
      have hpair : ({owner, owner} : Finset ι) = {owner} := by simp
      rw [show (⟨{owner, owner}, by simp⟩ :
          {S : Finset ι // S.Nonempty}) = ⟨{owner}, by simp⟩ from by
            simp [hpair]] at htempt
      simp at htempt
    · have hweak := hsink.2.1 other hother
      have hstrict : quittingSoloReward reward other other <
          quittingSoloReward reward owner other := by
        rcases lt_or_eq_of_le hweak with hlt | heq
        · exact hlt
        · exact absurd (hsink.2.2 other hother heq)
            (not_le.mpr (by linarith : quittingSoloReward reward other other <
              quittingSingletonCollisionReward reward owner other))
      exact div_pos (by linarith) htempt
  · norm_num

/-- **A benevolent sink soloist has a feasible positive rate.**  Every
opponent's tolerance is a half-line through the origin with a strictly
positive right endpoint, and there are finitely many opponents. -/
theorem exists_rate_quittingSoloQuitterCriterion_of_benevolentSink
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hsink : QuittingBenevolentSinkSoloist reward owner) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ QuittingSoloQuitterCriterion reward owner p := by
  classical
  have hnonempty : (Finset.univ : Finset ι).Nonempty := ⟨owner, by simp⟩
  set floor := Finset.univ.inf' hnonempty
    (benevolentSinkThreshold reward owner) with hfloor
  have hfloorPos : 0 < floor := by
    rw [hfloor, Finset.lt_inf'_iff]
    exact fun other _ => benevolentSinkThreshold_pos reward hsink
  refine ⟨min 1 floor, lt_min one_pos hfloorPos, min_le_left _ _, ?_⟩
  rw [quittingSoloQuitterCriterion_iff_affine]
  intro other hother
  have hbound : min 1 floor ≤ benevolentSinkThreshold reward owner other :=
    (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ other))
  have hweak := hsink.2.1 other hother
  by_cases htempt : 0 < quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward other other
  · rw [benevolentSinkThreshold, if_pos htempt, le_div_iff₀ htempt] at hbound
    linarith
  · have hrate : 0 < min 1 floor := lt_min one_pos hfloorPos
    nlinarith [hrate, not_lt.mp htempt]

/-! ## The equilibrium producer -/

/-- **A benevolent sink soloist produces an exact terminal equilibrium.**  At
a feasible positive rate the owner's solo stationary profile is an exact
terminal Nash equilibrium of the quitting game, delivering the owner's
singleton row to everybody. -/
theorem exists_hazard_isεAsymptoticNash_of_benevolentSink
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hsink : QuittingBenevolentSinkSoloist reward owner) :
    ∃ hazard : PMF Bool, 0 < (hazard true).toReal ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner hazard)) := by
  obtain ⟨p, hp0, hp1, hcriterion⟩ :=
    exists_rate_quittingSoloQuitterCriterion_of_benevolentSink reward owner
      hsink
  have hpositive : 0 < (quittingHazardCoin p hp0.le hp1 true).toReal := by
    rw [quittingHazardCoin_true_toReal]
    exact hp0
  refine ⟨quittingHazardCoin p hp0.le hp1, hpositive, ?_⟩
  refine isεAsymptoticNash_soloStationary_exact reward owner _ hpositive
    hsink.1 ?_
  intro other hother
  rw [quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
  exact hcriterion other hother

/-! ## The screen -/

/-- **Screen.**  A positive terminal exploitability gap excludes benevolent
sink soloists: the stationary profile they produce would be an exact terminal
equilibrium, which no gap tolerates. -/
theorem not_quittingBenevolentSinkSoloist_of_terminalExploitabilityGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {gap : ℝ}
    (hgapPos : 0 < gap) (hexploit : HasTerminalExploitabilityGap reward gap)
    (owner : ι) : ¬ QuittingBenevolentSinkSoloist reward owner := by
  intro hsink
  obtain ⟨hazard, _, hnash⟩ :=
    exists_hazard_isεAsymptoticNash_of_benevolentSink reward owner hsink
  obtain ⟨who, deviation, hbeat⟩ :=
    hexploit (quittingStationaryProfile reward
      (quittingSoloStationaryRoot owner hazard))
  have hcap := hnash who deviation
  rw [add_zero] at hcap
  linarith

/-- **Positive form of the screen.**  Under a positive terminal
exploitability gap, every coordinate whose own exit pays it nonnegatively
either strictly preempts somebody -- some coordinate strictly prefers its own
exit to that coordinate's -- or has a coordinate that is indifferent between
the two exits and strictly tempted to collide.  Neither alternative passes
through a viability threshold on the owner's reward. -/
theorem exists_weakPreemption_or_collisionTemptation_of_terminalExploitabilityGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {gap : ℝ}
    (hgapPos : 0 < gap) (hexploit : HasTerminalExploitabilityGap reward gap)
    (owner : ι) (howner : 0 ≤ quittingSoloReward reward owner owner) :
    (∃ other, other ≠ owner ∧
        quittingSoloReward reward owner other <
          quittingSoloReward reward other other) ∨
      ∃ other, other ≠ owner ∧
        quittingSoloReward reward other other =
            quittingSoloReward reward owner other ∧
          quittingSoloReward reward other other <
            quittingSingletonCollisionReward reward owner other := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hweak, hequality⟩ := hcontra
  refine not_quittingBenevolentSinkSoloist_of_terminalExploitabilityGap reward
    hgapPos hexploit owner ⟨howner, ?_, ?_⟩
  · intro other hother
    exact hweak other hother
  · intro other hother heq
    exact hequality other hother heq

end GameTheory
