/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Experiments.counterexample_search.RegularTournamentFiveSeed
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.AnchoredCyclicRenewal
import UniformEquilibrium.Quitting.Cycles.AnchoredCyclicRenewal

/-!
# Player zero's singleton row against the seed's anchored cyclic route

`Experiments/counterexample_search/RegularTournamentFiveSeedSoloExits.lean`
reads off four uniform-equilibrium payoffs of the realized seed table, the
singleton rows of the owners other than `0`.  They are successive cyclic
shifts, and the fifth member of that orbit — player zero's own singleton row
`(1, 0, 0, 3, 3)` — is missing, because the sure-exit route excludes the owner
`0` at the marked pair `{0, 1}`.

This module asks whether the anchored cyclic route reaches that vector
instead, and answers no, in four checked steps.

* **Only player zero's exit pays it.**  The linear functional
  `x ↦ x 3 + x 4` is at most `4` on every singleton row other than player
  zero's and equals `6` at `(1, 0, 0, 3, 3)`, so the target is outside the
  convex hull of the singleton rows of any set of owners omitting `0`
  (`orbitTarget_notMem_convexHull_of_notMem`).  Through
  `quittingAnchoredCyclicOnPathValue_ne_of_not_mem_convexHull` this rules out
  every absorbing anchored cyclic schedule that omits player zero.
* **The obvious schedule does pay it.**  Period one, player zero quitting
  surely, has on-path value exactly the target
  (`quittingAnchoredCyclicOnPathValue_soloZero`).
* **The opening phase of any target-paying schedule is idle or owned by player
  zero.**  The target pays players one and two nothing, the renewal weights are
  nonnegative, and player zero's exit is the only singleton row paying both of
  them nothing, so the opening term of the renewal sum pins the opening phase
  (`hazard_eq_zero_or_schedule_eq_zero_of_onPathValue_eq_orbitTarget`).
* **And every target-paying schedule is rejected.**  Player one's collision
  penalty at player zero's exit is `1` — the marked pair pays it more than
  being preempted — and quitting alone pays it `1` at an idle phase, so its
  exact finite response cap is at least `1` while the target pays it nothing
  (`not_isεAsymptoticNash_of_onPathValue_eq_orbitTarget`).  The same collision
  blocks the certificate route directly: no solo mixed root owned by player
  zero is exactly Nash against a tail paying player one less than one
  (`not_isZeroQuittingRootEndpointNash_soloMixedRoot_zero`).

## Scope

Every statement above is about the anchored cyclic family on this one literal
table.  Whether `(1, 0, 0, 3, 3)` is a uniform-equilibrium payoff of the
realized seed by some profile outside that family is not decided here, and no
general negative about the seed is claimed.

## Reproduction

`lake env lean Experiments/counterexample_search/RegularTournamentFiveSeedZeroOrbitGap.lean`
-/

noncomputable section

namespace GameTheory
namespace RegularTournamentFiveSeed

open Math.Probability

/-! ## The missing orbit member -/

/-- The fifth member of the seed's cyclic payoff orbit: player zero's
singleton row. -/
def orbitTarget : Payoff Player := ![1, 0, 0, 3, 3]

/-- Explicit singleton rows of the realized table. -/
@[simp] theorem reward_singletonTerminal_entries (owner who : Player) :
    reward (quittingSingletonTerminal owner) who =
      ![![1, 3, 3, 0, 0], ![0, 1, 3, 3, 0], ![0, 0, 1, 3, 3],
        ![3, 0, 0, 1, 3], ![3, 3, 0, 0, 1]] who owner := by
  have hrow : reward (quittingSingletonTerminal owner) who =
      1 + singletonMatrix who owner := by
    simp [reward, quittingSingletonTerminal]
  rw [hrow, singletonMatrix_entries]
  fin_cases who <;> fin_cases owner <;> norm_num

theorem reward_singletonTerminal_zero :
    reward (quittingSingletonTerminal (0 : Player)) = orbitTarget := by
  funext who
  rw [reward_singletonTerminal_entries]
  fin_cases who <;> rfl

/-- Player one's own solo exit pays it `1`. -/
theorem reward_singletonTerminal_one_self :
    reward (quittingSingletonTerminal (1 : Player)) 1 = 1 := by
  rw [reward_singletonTerminal_entries]
  norm_num

/-- The marked pair `{0, 1}` pays player one `1`, as much as its own solo exit
does. -/
theorem reward_markedPair_one :
    reward ⟨{(0 : Player), 1}, Finset.insert_nonempty 0 {1}⟩ 1 = 1 := by
  norm_num [reward]

/-! ## Only player zero's exit reaches the target -/

/-- The separating functional: the sum of the last two coordinates. -/
def tailPairSum (payoff : Payoff Player) : ℝ := payoff 3 + payoff 4

theorem isLinearMap_tailPairSum : IsLinearMap ℝ tailPairSum where
  map_add first second := by simp [tailPairSum]; ring
  map_smul scalar payoff := by simp [tailPairSum]; ring

theorem tailPairSum_orbitTarget : tailPairSum orbitTarget = 6 := by
  rw [tailPairSum]
  norm_num [orbitTarget, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.tail_cons, Matrix.head_cons]

/-- Every singleton row other than player zero's is at most `4` under the
separating functional; player zero's row is `6`. -/
theorem tailPairSum_reward_singletonTerminal_le {owner : Player} (hne : owner ≠ 0) :
    tailPairSum (reward (quittingSingletonTerminal owner)) ≤ 4 := by
  fin_cases owner
  · exact absurd rfl hne
  all_goals
    · rw [tailPairSum, reward_singletonTerminal_entries,
        reward_singletonTerminal_entries]
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.tail_cons, Matrix.head_cons]

/-- **The target is outside the reach of any schedule omitting player zero.**
It is not in the convex hull of the singleton rows of any set of owners that
excludes `0`. -/
theorem orbitTarget_notMem_convexHull_of_notMem {owners : Set Player}
    (hzero : (0 : Player) ∉ owners) :
    orbitTarget ∉ convexHull ℝ
      ((fun owner ↦ reward (quittingSingletonTerminal owner)) '' owners) := by
  intro hmem
  have hsubset : convexHull ℝ
      ((fun owner ↦ reward (quittingSingletonTerminal owner)) '' owners) ⊆
        {payoff : Payoff Player | tailPairSum payoff ≤ 4} := by
    refine convexHull_min ?_ (convex_halfSpace_le isLinearMap_tailPairSum 4)
    rintro payoff ⟨owner, howner, rfl⟩
    exact tailPairSum_reward_singletonTerminal_le fun hcontra ↦ hzero (hcontra ▸ howner)
  have hbound : tailPairSum orbitTarget ≤ 4 := hsubset hmem
  rw [tailPairSum_orbitTarget] at hbound
  norm_num at hbound

/-- **No absorbing anchored cyclic schedule omitting player zero pays the
target.**  This is the convex-hull prescreen at the realized seed table. -/
theorem quittingAnchoredCyclicOnPathValue_ne_orbitTarget_of_notMem_range
    {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hcontraction : ∏ k, (1 - hazard k) < 1) (phase : Fin m)
    (hzero : (0 : Player) ∉ Set.range w) :
    quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase ≠ orbitTarget :=
  quittingAnchoredCyclicOnPathValue_ne_of_not_mem_convexHull reward w hazard h0 h1
    hcontraction phase (orbitTarget_notMem_convexHull_of_notMem hzero)

/-! ## The schedule that does pay the target -/

/-- Period one: player zero quits, surely. -/
def soloZeroSchedule : Fin 1 → Player := ![0]

/-- The sure hazard of that single phase. -/
def soloZeroHazard : Fin 1 → ℝ := ![1]

theorem soloZeroHazard_nonneg (phase : Fin 1) : 0 ≤ soloZeroHazard phase := by
  fin_cases phase
  norm_num [soloZeroHazard]

theorem soloZeroHazard_le_one (phase : Fin 1) : soloZeroHazard phase ≤ 1 := by
  fin_cases phase
  norm_num [soloZeroHazard]

theorem prod_one_sub_soloZeroHazard :
    ∏ k : Fin 1, (1 - soloZeroHazard k) = 0 := by
  rw [Fin.prod_univ_one]
  norm_num [soloZeroHazard]

/-- The constant family at the target solves the renewal system of that
schedule. -/
theorem isAnchoredCyclicRenewalSolution_orbitTarget :
    IsAnchoredCyclicRenewalSolution reward soloZeroSchedule soloZeroHazard
      (fun _ ↦ orbitTarget) := by
  intro phase who
  fin_cases phase
  rw [show soloZeroSchedule ⟨0, Nat.one_pos⟩ = 0 from rfl,
    reward_singletonTerminal_zero]
  norm_num [soloZeroHazard]

/-- **The target is an anchored cyclic on-path value.**  Player zero quitting
surely, at period one, pays exactly `(1, 0, 0, 3, 3)`. -/
theorem quittingAnchoredCyclicOnPathValue_soloZero :
    quittingAnchoredCyclicOnPathValue reward soloZeroSchedule soloZeroHazard
        soloZeroHazard_nonneg soloZeroHazard_le_one
        (quittingAnchoredCyclicStart 1) = orbitTarget :=
  congrFun
    (eq_of_isAnchoredCyclicRenewalSolution
      (quittingAnchoredCyclicOnPathValue_isAnchoredCyclicRenewalSolution reward
        soloZeroSchedule soloZeroHazard soloZeroHazard_nonneg
        soloZeroHazard_le_one)
      isAnchoredCyclicRenewalSolution_orbitTarget
      (by rw [prod_one_sub_soloZeroHazard]; norm_num))
    (quittingAnchoredCyclicStart 1)

/-! ## The marked collision rejects it -/

/-- Player one's collision penalty at player zero's solo exit is one: the
marked pair `{0, 1}` pays player one more than being preempted does. -/
theorem quittingSoloCollisionPenalty_zero_one :
    quittingSoloCollisionPenalty reward 0 1 = 1 := by
  rw [quittingSoloCollisionPenalty, reward_singletonTerminal_entries]
  norm_num [reward]

/-- **No solo mixed root owned by player zero is exactly Nash against a tail
that pays player one less than one.**  Player one continues surely at such a
root, so its endpoint condition is the full spectator inequality, and the
marked pair makes quitting worth one whatever the owner's hazard. -/
theorem not_isZeroQuittingRootEndpointNash_soloMixedRoot_zero
    (tail : Payoff Player) (marginal : PMF Bool) (htail : tail 1 < 1) :
    ¬ IsεQuittingRootEndpointNash reward tail 0
      (quittingSoloMixedRoot (0 : Player) marginal) := by
  intro hnash
  have hne : (1 : Player) ≠ 0 := by decide
  obtain ⟨hcontinue, -⟩ := hnash 1
  rw [quittingSoloMixedRoot_of_ne hne] at hcontinue
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_soloMixedRoot_of_ne reward tail hne,
    quittingRootContinuePayoff_soloMixedRoot_of_ne reward tail hne] at hcontinue
  have hpair := reward_markedPair_one
  have hsolo := reward_singletonTerminal_one_self
  have hpreempt : reward (quittingSingletonTerminal (0 : Player)) 1 = 0 := by
    rw [reward_singletonTerminal_entries]
    norm_num
  have hsum : (marginal false).toReal + (marginal true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one marginal
  have hfalse : 0 ≤ (marginal false).toReal := ENNReal.toReal_nonneg
  have htrue : 0 ≤ (marginal true).toReal := ENNReal.toReal_nonneg
  rw [hpair, hsolo, hpreempt] at hcontinue
  simp only [PMF.pure_apply, if_true, ENNReal.toReal_one, one_mul] at hcontinue
  rcases le_or_gt 0 (tail 1) with hsign | hsign
  · nlinarith [hcontinue]
  · nlinarith [hcontinue]

/-- Every singleton row of the realized table is nonnegative. -/
theorem zero_le_reward_singletonTerminal (owner who : Player) :
    0 ≤ reward (quittingSingletonTerminal owner) who := by
  rw [reward_singletonTerminal_entries]
  fin_cases owner <;> fin_cases who <;> norm_num

/-- Player zero's exit is the only one paying both player one and player two
nothing: every other owner pays at least one of them. -/
theorem eq_zero_of_reward_singletonTerminal_eq_zero {owner : Player}
    (hone : reward (quittingSingletonTerminal owner) 1 = 0)
    (htwo : reward (quittingSingletonTerminal owner) 2 = 0) : owner = 0 := by
  rw [reward_singletonTerminal_entries] at hone htwo
  fin_cases owner
  · rfl
  · revert hone
    norm_num
  · revert hone
    norm_num
  · revert hone
    norm_num
  · revert htwo
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- Player one's one-phase Quit value against a phase owned by player zero is
one, whatever the phase hazard: the marked pair pays exactly what quitting
alone does. -/
theorem quittingAnchoredCyclicQuitValue_one_of_zero {m : ℕ}
    (w : Fin m → Player) (hazard : Fin m → ℝ) (phase : Fin m)
    (hphase : w phase = 0) :
    quittingAnchoredCyclicQuitValue reward w hazard phase 1 = 1 :=
  quittingAnchoredCyclicQuitValue_eq_of_flatQuitRow reward w hazard phase
    reward_singletonTerminal_one_self fun _ ↦ by
      rw [hphase]
      exact reward_markedPair_one

/-- Player one's one-phase Quit value against an idle phase is one: quitting
alone pays it its own singleton row. -/
theorem quittingAnchoredCyclicQuitValue_one_of_hazard_eq_zero {m : ℕ}
    (w : Fin m → Player) (hazard : Fin m → ℝ) (phase : Fin m)
    (hzero : hazard phase = 0) :
    quittingAnchoredCyclicQuitValue reward w hazard phase 1 = 1 := by
  rw [quittingAnchoredCyclicQuitValue_of_hazard_eq_zero reward w hazard phase 1
    hzero]
  exact reward_singletonTerminal_one_self

/-- **The opening phase of a target-paying schedule is idle or owned by player
zero.**  Both player one and player two are paid nothing by the target, and the
renewal weights are nonnegative, so the opening term of the renewal sum must
vanish in both coordinates. -/
theorem hazard_eq_zero_or_schedule_eq_zero_of_onPathValue_eq_orbitTarget
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hcontraction : ∏ k, (1 - hazard k) < 1)
    (hvalue : quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
      (quittingAnchoredCyclicStart m) = orbitTarget) :
    hazard (quittingAnchoredCyclicStart m) = 0 ∨
      w (quittingAnchoredCyclicStart m) = 0 := by
  have hmem : 0 ∈ Finset.range m := Finset.mem_range.2 (Nat.pos_of_ne_zero (NeZero.ne m))
  have hkey : ∀ who : Player, orbitTarget who = 0 →
      hazard (quittingAnchoredCyclicStart m) *
        reward (quittingSingletonTerminal (w (quittingAnchoredCyclicStart m)))
          who = 0 := by
    intro who hwho
    have hdiv := quittingAnchoredCyclicOnPathValue_eq_div reward w hazard h0 h1
      (ne_of_lt hcontraction) (quittingAnchoredCyclicStart m) who
    rw [congrFun hvalue who, hwho] at hdiv
    have hpos : 0 < 1 - ∏ k, (1 - hazard k) := by linarith
    have hsum : quittingAnchoredCyclicRenewalSum reward w hazard
        (quittingAnchoredCyclicStart m) who = 0 := by
      field_simp at hdiv
      linarith [hdiv]
    have hnonneg : ∀ offset ∈ Finset.range m,
        0 ≤ quittingAnchoredCyclicRenewalWeight hazard
              (quittingAnchoredCyclicStart m) offset *
            reward (quittingSingletonTerminal
              (w (quittingCyclicOrbit (quittingAnchoredCyclicStart m) offset)))
              who :=
      fun offset _ ↦ mul_nonneg
        (quittingAnchoredCyclicRenewalWeight_nonneg h0 h1 _ offset)
        (zero_le_reward_singletonTerminal _ who)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum 0 hmem
    rwa [quittingAnchoredCyclicRenewalWeight,
      quittingAnchoredCyclicPrefixSurvival_zero, one_mul,
      quittingCyclicOrbit_zero] at hterm
  by_cases hidle : hazard (quittingAnchoredCyclicStart m) = 0
  · exact Or.inl hidle
  refine Or.inr (eq_zero_of_reward_singletonTerminal_eq_zero ?_ ?_)
  · have := hkey 1 (by norm_num [orbitTarget])
    rcases mul_eq_zero.1 this with hcontra | hrow
    · exact absurd hcontra hidle
    · exact hrow
  · have := hkey 2 (by
      norm_num [orbitTarget, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons])
    rcases mul_eq_zero.1 this with hcontra | hrow
    · exact absurd hcontra hidle
    · exact hrow

/-- **The screen rejects every target-paying schedule.**  Player one's exact
finite response cap is at least one, while the target pays it nothing. -/
theorem one_le_quittingAnchoredCyclicResponseCap_one_of_onPathValue_eq
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hcontraction : ∏ k, (1 - hazard k) < 1)
    (hvalue : quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
      (quittingAnchoredCyclicStart m) = orbitTarget) :
    1 ≤ quittingAnchoredCyclicResponseCap reward w hazard h0 h1 1 := by
  refine le_trans (le_of_eq ?_)
    (quittingAnchoredCyclicQuitValue_le_responseCap reward w hazard h0 h1 1)
  rcases hazard_eq_zero_or_schedule_eq_zero_of_onPathValue_eq_orbitTarget w hazard
    h0 h1 hcontraction hvalue with hidle | hopen
  · exact (quittingAnchoredCyclicQuitValue_one_of_hazard_eq_zero w hazard
      (quittingAnchoredCyclicStart m) hidle).symm
  · exact (quittingAnchoredCyclicQuitValue_one_of_zero w hazard
      (quittingAnchoredCyclicStart m) hopen).symm

/-- **The anchored cyclic route does not deliver the missing orbit member.**
No absorbing anchored cyclic profile of the realized seed whose on-path value
is `(1, 0, 0, 3, 3)` is asymptotic Nash at accuracy zero: player one's exact
response cap is at least one there, while the target pays it nothing. -/
theorem not_isεAsymptoticNash_of_onPathValue_eq_orbitTarget {m : ℕ} [NeZero m]
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hcontraction : ∏ k, (1 - hazard k) < 1)
    (hvalue : quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
      (quittingAnchoredCyclicStart m) = orbitTarget) :
    ¬ (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingAnchoredCyclicProfile reward w hazard h0 h1) := by
  intro hnash
  have hcap := quittingAnchoredCyclicResponseCap_le_onPathValue_of_isεAsymptoticNash
    reward w hazard h0 h1 hnash 1
  rw [hvalue, show orbitTarget 1 = 0 from by norm_num [orbitTarget]] at hcap
  linarith [one_le_quittingAnchoredCyclicResponseCap_one_of_onPathValue_eq w hazard
    h0 h1 hcontraction hvalue]

/-- The period-one witness that pays the target is rejected by the screen. -/
theorem not_isεAsymptoticNash_soloZero :
    ¬ (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingAnchoredCyclicProfile reward soloZeroSchedule soloZeroHazard
        soloZeroHazard_nonneg soloZeroHazard_le_one) :=
  not_isεAsymptoticNash_of_onPathValue_eq_orbitTarget soloZeroSchedule
    soloZeroHazard soloZeroHazard_nonneg soloZeroHazard_le_one
    (by rw [prod_one_sub_soloZeroHazard]; norm_num)
    quittingAnchoredCyclicOnPathValue_soloZero

end RegularTournamentFiveSeed
end GameTheory
