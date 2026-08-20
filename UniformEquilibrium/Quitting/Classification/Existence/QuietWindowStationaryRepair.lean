/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.RootSequenceWindowLedger
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback
import UniformEquilibrium.Quitting.RewardBound

/-!
# The quiet-window stationary repair

Case 1 of the block analysis of Solan and Vieille, *Quitting games*, Math.
Oper. Res. 26 (2001), Section 2.5.3, in this development's root-sequence
vocabulary.  When one player's opponents are nearly silent over a window
through which the plan almost surely absorbs, the plan's continuation value
at the window start concentrates on that player's solo-exit reward,
coordinatewise; the stationary repair itself is assembled downstream by the
production compiler
`isεAsymptoticNash_soloStationary_of_tail_bounds_of_hazard`.

* `abs_quittingRootExpectedPayoff_forcedQuit_sub_soloReward_le` — forcing
  one player to Quit pays every observer within `2M` times the opponent
  absorption mass of the solo-exit reward.
* `abs_quittingRootSequenceTerminalValue_sub_soloReward_le_window` — the
  window concentration: the plan's value is within
  `4M (window opponent charges) + 2M (window survival)` of the solo-exit
  reward, coordinatewise.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Forcing one player to Quit pays close to its solo exit -/

omit [Fintype ι] in
/-- Opponent silence at one action: everyone except `owner` continues. -/
theorem update_false_eq_allContinue_iff (sample : ι → Bool) (owner : ι) :
    Function.update sample owner false =
      (quittingAllContinueAction : ι → Bool) ↔
      ∀ player, player ≠ owner → sample player = false := by
  constructor
  · intro hquiet player hne
    have hcoordinate := congrFun hquiet player
    rw [Function.update_of_ne hne] at hcoordinate
    exact hcoordinate
  · intro hquiet
    funext player
    by_cases hplayer : player = owner
    · subst hplayer
      simp [quittingAllContinueAction]
    · rw [Function.update_of_ne hplayer]
      simpa [quittingAllContinueAction] using hquiet player hplayer

/-- When every opponent continues, forcing `owner` to Quit selects exactly
the solo quitter set. -/
theorem quittingQuitters_update_true_eq_singleton (sample : ι → Bool)
    (owner : ι)
    (hquiet : ∀ player, player ≠ owner → sample player = false) :
    quittingQuitters (Function.update sample owner true) = {owner} := by
  ext player
  simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  by_cases hplayer : player = owner
  · subst hplayer
    simp
  · rw [Function.update_of_ne hplayer]
    rw [hquiet player hplayer]
    simp [hplayer]

/-- **Forced-quit solo comparison, every observer.**  Replacing one player's
marginal by pure Quit pays every observer within `2M` times the opponent
absorption mass of the solo-exit reward: the payoffs differ only when some
opponent of the quitter also quits. -/
theorem abs_quittingRootExpectedPayoff_forcedQuit_sub_soloReward_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (owner who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootExpectedPayoff reward tail
        (Function.update root owner (PMF.pure true)) who -
      quittingSoloReward reward owner who| ≤
      2 * M * quittingRootOpponentAbsorptionMass root owner := by
  classical
  have hpush : quittingRootExpectedPayoff reward tail
      (Function.update root owner (PMF.pure true)) who =
      expect (pmfPi root) (fun sample =>
        quittingRootPayoff reward tail
          (Function.update sample owner true) who) := by
    unfold quittingRootExpectedPayoff
    rw [← pmfPi_bind_update_pure, expect_bind]
    apply congrArg (expect (pmfPi root))
    funext sample
    rw [expect_pure]
  have hpointwise : ∀ sample : ι → Bool,
      |quittingRootPayoff reward tail (Function.update sample owner true) who -
        quittingSoloReward reward owner who| ≤
        2 * M * (1 - (if Function.update sample owner false =
          (quittingAllContinueAction : ι → Bool) then (1 : ℝ) else 0)) := by
    intro sample
    have hmem : owner ∈ quittingQuitters (Function.update sample owner true) := by
      simp [quittingQuitters]
    have hnonempty :
        (quittingQuitters (Function.update sample owner true)).Nonempty :=
      ⟨owner, hmem⟩
    by_cases hquiet : Function.update sample owner false =
        (quittingAllContinueAction : ι → Bool)
    · rw [if_pos hquiet]
      have hsingleton := quittingQuitters_update_true_eq_singleton sample owner
        ((update_false_eq_allContinue_iff sample owner).1 hquiet)
      unfold quittingRootPayoff
      rw [dif_pos hnonempty]
      rw [show (⟨quittingQuitters (Function.update sample owner true),
          hnonempty⟩ : {S : Finset ι // S.Nonempty}) =
          ⟨{owner}, Finset.singleton_nonempty owner⟩ from
        Subtype.ext hsingleton]
      simp [quittingSoloReward]
    · rw [if_neg hquiet]
      unfold quittingRootPayoff
      rw [dif_pos hnonempty]
      have hvalue := hreward ⟨_, hnonempty⟩ who
      have hsolo : |quittingSoloReward reward owner who| ≤ M := hreward _ who
      obtain ⟨hvalue₁, hvalue₂⟩ := abs_le.mp hvalue
      obtain ⟨hsolo₁, hsolo₂⟩ := abs_le.mp hsolo
      rw [abs_le]
      constructor <;> [linarith; linarith]
  have hindicator : expect (pmfPi root) (fun sample =>
      1 - (if Function.update sample owner false =
        (quittingAllContinueAction : ι → Bool) then (1 : ℝ) else 0)) =
      quittingRootOpponentAbsorptionMass root owner := by
    rw [expect_sub, expect_const]
    have hpush' : expect (pmfPi root) (fun sample =>
        if Function.update sample owner false =
          (quittingAllContinueAction : ι → Bool) then (1 : ℝ) else 0) =
        expect (pmfPi (Function.update root owner (PMF.pure false)))
          (fun action =>
            if action = (quittingAllContinueAction : ι → Bool)
              then (1 : ℝ) else 0) := by
      rw [← pmfPi_bind_update_pure, expect_bind]
      apply congrArg (expect (pmfPi root))
      funext sample
      rw [expect_pure]
    rw [hpush', expect_allContinueIndicator_eq_continueMass]
    rfl
  have hcap : expect (pmfPi root) (fun sample =>
      2 * M * (1 - (if Function.update sample owner false =
        (quittingAllContinueAction : ι → Bool) then (1 : ℝ) else 0))) =
      2 * M * quittingRootOpponentAbsorptionMass root owner := by
    rw [expect_const_mul, hindicator]
  have hupper : quittingRootExpectedPayoff reward tail
      (Function.update root owner (PMF.pure true)) who -
      quittingSoloReward reward owner who ≤
      2 * M * quittingRootOpponentAbsorptionMass root owner := by
    rw [hpush]
    have hmono : expect (pmfPi root) (fun sample =>
        quittingRootPayoff reward tail
            (Function.update sample owner true) who -
          quittingSoloReward reward owner who) ≤
        expect (pmfPi root) (fun sample =>
          2 * M * (1 - (if Function.update sample owner false =
            (quittingAllContinueAction : ι → Bool) then (1 : ℝ) else 0))) := by
      apply expect_mono
      intro sample
      exact le_trans (le_abs_self _) (hpointwise sample)
    have hleft : expect (pmfPi root) (fun sample =>
        quittingRootPayoff reward tail
            (Function.update sample owner true) who -
          quittingSoloReward reward owner who) =
        expect (pmfPi root) (fun sample =>
          quittingRootPayoff reward tail
            (Function.update sample owner true) who) -
          quittingSoloReward reward owner who := by
      rw [expect_sub, expect_const]
    rw [hleft, hcap] at hmono
    linarith
  have hlower : -(2 * M * quittingRootOpponentAbsorptionMass root owner) ≤
      quittingRootExpectedPayoff reward tail
        (Function.update root owner (PMF.pure true)) who -
      quittingSoloReward reward owner who := by
    rw [hpush]
    have hmono : expect (pmfPi root) (fun sample =>
        quittingSoloReward reward owner who -
          quittingRootPayoff reward tail
            (Function.update sample owner true) who) ≤
        expect (pmfPi root) (fun sample =>
          2 * M * (1 - (if Function.update sample owner false =
            (quittingAllContinueAction : ι → Bool) then (1 : ℝ) else 0))) := by
      apply expect_mono
      intro sample
      have hpoint := hpointwise sample
      linarith [(abs_le.mp hpoint).1]
    have hleft : expect (pmfPi root) (fun sample =>
        quittingSoloReward reward owner who -
          quittingRootPayoff reward tail
            (Function.update sample owner true) who) =
        quittingSoloReward reward owner who -
          expect (pmfPi root) (fun sample =>
            quittingRootPayoff reward tail
              (Function.update sample owner true) who) := by
      rw [expect_sub, expect_const]
    rw [hleft, hcap] at hmono
    linarith
  rw [abs_le]
  exact ⟨hlower, hupper⟩

/-! ## Window concentration of the plan's value -/

/-- **Window concentration.**  Along any root sequence, the plan's value at
a window start is within `4M` times the window's survival-weighted opponent
absorption plus `2M` times the window's joint survival of the solo-exit
reward, coordinatewise: within the window, absorption is essentially the
owner quitting alone. -/
theorem abs_quittingRootSequenceTerminalValue_sub_soloReward_le_window
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∀ window start,
      |quittingRootSequenceTerminalValue reward roots who start -
        quittingSoloReward reward owner who| ≤
        4 * M * (∑ t ∈ Finset.range window,
          quittingJointSurvivalWeight roots start t *
            quittingRootOpponentAbsorptionMass (roots (start + t)) owner) +
        2 * M * quittingJointSurvivalWeight roots start window := by
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward owner hreward
  intro window
  induction window with
  | zero =>
      intro start
      have hγ := abs_quittingRootSequenceTerminalValue_le reward roots who
        start hM hreward
      have hsolo : |quittingSoloReward reward owner who| ≤ M := hreward _ who
      obtain ⟨hγ₁, hγ₂⟩ := abs_le.mp hγ
      obtain ⟨hsolo₁, hsolo₂⟩ := abs_le.mp hsolo
      have hjsw : quittingJointSurvivalWeight roots start 0 = 1 :=
        quittingJointSurvivalWeight_zero_fuel roots start
      rw [hjsw]
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add]
      rw [abs_le]
      constructor <;> linarith
  | succ window ih =>
      intro start
      set γ' := quittingRootSequenceTerminalValue reward roots who (start + 1)
        with hγ'
      set solo := quittingSoloReward reward owner who with hsolodef
      set forcedQuit := quittingRootExpectedPayoff reward (0 : Payoff ι)
        (Function.update (roots start) owner (PMF.pure true)) who
        with hforcedQuit
      set forcedContinue := quittingRootExpectedPayoff reward (0 : Payoff ι)
        (Function.update (roots start) owner (PMF.pure false)) who
        with hforcedContinue
      set ownQuit := (roots start owner true).toReal with hownQuit
      set ownContinue := (roots start owner false).toReal with hownContinue
      set opContinue := quittingStationaryContinueMass
        (Function.update (roots start) owner (PMF.pure false))
        with hopContinue
      have hplan := quittingRootSequenceTerminalValue_eq_absorbingContribution_add
        reward roots who start
      have hplan' : quittingRootSequenceTerminalValue reward roots who start =
          quittingRootAbsorbingContribution reward (roots start) who +
            quittingStationaryContinueMass (roots start) * γ' := by
        rw [hγ']
        exact hplan
      have hmix := quittingRootExpectedPayoff_update_coord_eq_mix reward
        (0 : Payoff ι) (roots start) owner (roots start owner) who
      rw [Function.update_eq_self] at hmix
      have hAC : quittingRootAbsorbingContribution reward (roots start) who =
          ownQuit * forcedQuit + ownContinue * forcedContinue := hmix
      have hfactor' : quittingStationaryContinueMass (roots start) =
          opContinue * ownContinue :=
        quittingStationaryContinueMass_eq_forcedContinue_mul_own
          (roots start) owner
      have hsum := quittingRoot_continueProbability_add_quitProbability
        (roots start) owner
      have hop : quittingRootOpponentAbsorptionMass (roots start) owner =
          1 - opContinue := rfl
      have hq : ownQuit = 1 - ownContinue := by
        rw [hownQuit, hownContinue]
        linarith
      have hidentity : quittingRootSequenceTerminalValue reward roots who
          start - solo =
          ownQuit * (forcedQuit - solo) + ownContinue * forcedContinue +
            ownContinue * (opContinue - 1) * solo +
            opContinue * ownContinue * (γ' - solo) := by
        rw [hplan', hAC, hfactor', hq]
        ring
      have hzero₁ : (0 : ℝ) ≤ (roots start owner true).toReal :=
        ENNReal.toReal_nonneg
      have hzero₂ : (0 : ℝ) ≤ (roots start owner false).toReal :=
        ENNReal.toReal_nonneg
      have hownQuit0 : (0 : ℝ) ≤ ownQuit := hzero₁
      have hownContinue0 : (0 : ℝ) ≤ ownContinue := hzero₂
      have hownQuit1 : ownQuit ≤ 1 := by
        rw [hownQuit]
        linarith
      have hownContinue1 : ownContinue ≤ 1 := by
        rw [hownContinue]
        linarith
      have hopContinue0 : 0 ≤ opContinue :=
        quittingStationaryContinueMass_nonneg _
      have hopContinue1 : opContinue ≤ 1 :=
        quittingStationaryContinueMass_le_one _
      have hop0 : 0 ≤ quittingRootOpponentAbsorptionMass (roots start) owner :=
        quittingRootOpponentAbsorptionMass_nonneg (roots start) owner
      have hforced : |forcedQuit - solo| ≤
          2 * M * quittingRootOpponentAbsorptionMass (roots start) owner :=
        abs_quittingRootExpectedPayoff_forcedQuit_sub_soloReward_le
          reward (0 : Payoff ι) (roots start) owner who hreward
      have hcontinueBound : |forcedContinue| ≤
          M * quittingRootOpponentAbsorptionMass (roots start) owner :=
        abs_quittingRootAbsorbingContribution_le_mul_absorptionMass reward
          (Function.update (roots start) owner (PMF.pure false)) who hreward
      have hsoloBound : |solo| ≤ M := hreward _ who
      have hnext : |γ' - solo| ≤
          4 * M * (∑ t ∈ Finset.range window,
            quittingJointSurvivalWeight roots (start + 1) t *
              quittingRootOpponentAbsorptionMass
                (roots (start + 1 + t)) owner) +
          2 * M * quittingJointSurvivalWeight roots (start + 1) window := by
        rw [hγ', hsolodef]
        exact ih (start + 1)
      have htriangle : |quittingRootSequenceTerminalValue reward roots who
          start - solo| ≤
          ownQuit * |forcedQuit - solo| + ownContinue * |forcedContinue| +
            ownContinue * (1 - opContinue) * |solo| +
            opContinue * ownContinue * |γ' - solo| := by
        rw [hidentity]
        have h4 := abs_add_le
          (ownQuit * (forcedQuit - solo) + ownContinue * forcedContinue +
            ownContinue * (opContinue - 1) * solo)
          (opContinue * ownContinue * (γ' - solo))
        have h3 := abs_add_le
          (ownQuit * (forcedQuit - solo) + ownContinue * forcedContinue)
          (ownContinue * (opContinue - 1) * solo)
        have h2 := abs_add_le (ownQuit * (forcedQuit - solo))
          (ownContinue * forcedContinue)
        have e1 : |ownQuit * (forcedQuit - solo)| =
            ownQuit * |forcedQuit - solo| := by
          rw [abs_mul, abs_of_nonneg hownQuit0]
        have e2 : |ownContinue * forcedContinue| =
            ownContinue * |forcedContinue| := by
          rw [abs_mul, abs_of_nonneg hownContinue0]
        have e3 : |ownContinue * (opContinue - 1) * solo| =
            ownContinue * (1 - opContinue) * |solo| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hownContinue0,
            abs_of_nonpos (by linarith : opContinue - 1 ≤ 0)]
          ring
        have e4 : |opContinue * ownContinue * (γ' - solo)| =
            opContinue * ownContinue * |γ' - solo| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hopContinue0,
            abs_of_nonneg hownContinue0]
        rw [e1, e2] at h2
        rw [e3] at h3
        rw [e4] at h4
        linarith
      have hbound1 : ownQuit * |forcedQuit - solo| ≤
          2 * M * quittingRootOpponentAbsorptionMass (roots start) owner := by
        have hRHS0 : 0 ≤ 2 * M *
            quittingRootOpponentAbsorptionMass (roots start) owner := by
          nlinarith
        calc ownQuit * |forcedQuit - solo| ≤
            1 * (2 * M * quittingRootOpponentAbsorptionMass
              (roots start) owner) :=
              mul_le_mul hownQuit1 hforced (abs_nonneg _) (by norm_num)
          _ = _ := one_mul _
      have hbound2 : ownContinue * |forcedContinue| ≤
          M * quittingRootOpponentAbsorptionMass (roots start) owner := by
        calc ownContinue * |forcedContinue| ≤
            1 * (M * quittingRootOpponentAbsorptionMass
              (roots start) owner) :=
              mul_le_mul hownContinue1 hcontinueBound (abs_nonneg _)
                (by norm_num)
          _ = _ := one_mul _
      have hbound3 : ownContinue * (1 - opContinue) * |solo| ≤
          M * quittingRootOpponentAbsorptionMass (roots start) owner := by
        rw [hop]
        have hfactor0 : 0 ≤ ownContinue * (1 - opContinue) :=
          mul_nonneg hownContinue0 (by linarith)
        calc ownContinue * (1 - opContinue) * |solo| ≤
            ownContinue * (1 - opContinue) * M :=
              mul_le_mul_of_nonneg_left hsoloBound hfactor0
          _ ≤ 1 * ((1 - opContinue) * M) := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_right hownContinue1
                (mul_nonneg (by linarith) hM)
          _ = M * (1 - opContinue) := by ring
      have hsum0 : 0 ≤ ∑ t ∈ Finset.range window,
          quittingJointSurvivalWeight roots (start + 1) t *
            quittingRootOpponentAbsorptionMass (roots (start + 1 + t)) owner :=
        Finset.sum_nonneg fun t _ => mul_nonneg
          (quittingJointSurvivalWeight_nonneg roots (start + 1) t)
          (quittingRootOpponentAbsorptionMass_nonneg _ _)
      have hjsw0 : 0 ≤ quittingJointSurvivalWeight roots (start + 1) window :=
        quittingJointSurvivalWeight_nonneg roots (start + 1) window
      have hbound4 : opContinue * ownContinue * |γ' - solo| ≤
          opContinue * ownContinue *
            (4 * M * (∑ t ∈ Finset.range window,
              quittingJointSurvivalWeight roots (start + 1) t *
                quittingRootOpponentAbsorptionMass
                  (roots (start + 1 + t)) owner) +
              2 * M * quittingJointSurvivalWeight roots (start + 1) window) :=
        mul_le_mul_of_nonneg_left hnext
          (mul_nonneg hopContinue0 hownContinue0)
      have hshrink : opContinue * ownContinue *
          (4 * M * (∑ t ∈ Finset.range window,
            quittingJointSurvivalWeight roots (start + 1) t *
              quittingRootOpponentAbsorptionMass
                (roots (start + 1 + t)) owner) +
            2 * M * quittingJointSurvivalWeight roots (start + 1) window) =
          4 * M * (∑ t ∈ Finset.range window,
            quittingJointSurvivalWeight roots start (t + 1) *
              quittingRootOpponentAbsorptionMass
                (roots (start + 1 + t)) owner) +
            2 * M * quittingJointSurvivalWeight roots start (window + 1) := by
        have hsurvival : ∀ fuel, quittingJointSurvivalWeight roots start
            (fuel + 1) =
            opContinue * ownContinue *
              quittingJointSurvivalWeight roots (start + 1) fuel := by
          intro fuel
          rw [quittingJointSurvivalWeight_succ_left, hfactor']
        have hsumEq : (∑ t ∈ Finset.range window,
            quittingJointSurvivalWeight roots start (t + 1) *
              quittingRootOpponentAbsorptionMass
                (roots (start + 1 + t)) owner) =
            opContinue * ownContinue * (∑ t ∈ Finset.range window,
              quittingJointSurvivalWeight roots (start + 1) t *
                quittingRootOpponentAbsorptionMass
                  (roots (start + 1 + t)) owner) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          rw [hsurvival t]
          ring
        rw [hsumEq, hsurvival window]
        ring
      have hwindowSum : (∑ t ∈ Finset.range (window + 1),
          quittingJointSurvivalWeight roots start t *
            quittingRootOpponentAbsorptionMass (roots (start + t)) owner) =
          (∑ t ∈ Finset.range window,
            quittingJointSurvivalWeight roots start (t + 1) *
              quittingRootOpponentAbsorptionMass
                (roots (start + 1 + t)) owner) +
            quittingRootOpponentAbsorptionMass (roots start) owner := by
        rw [Finset.sum_range_succ' (fun t =>
          quittingJointSurvivalWeight roots start t *
            quittingRootOpponentAbsorptionMass (roots (start + t)) owner)
          window]
        have hzero : quittingJointSurvivalWeight roots start 0 = 1 :=
          quittingJointSurvivalWeight_zero_fuel roots start
        simp only [Nat.add_zero, hzero, one_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro t _
        rw [show start + (t + 1) = start + 1 + t from by omega]
      rw [hwindowSum]
      have hchain := le_trans hbound4 (le_of_eq hshrink)
      linarith [htriangle, hbound1, hbound2, hbound3, hchain]

/-! ## The quiet-window stationary repair -/

/-- **The quiet-window stationary repair** (Solan and Vieille, *Quitting
games*, Math. Oper. Res. 26 (2001), Section 2.5.3).  Under unit solo exit,
if at some stage a player quits with positive probability while its
opponents' absorption over a following window plus the window's survival is
below `η`, and the stage's row is one-stage `εr`-perfect against the plan's
own continuation, then the stationary profile in which that player quits
alone at its own prescribed rate is a terminal `(εr + 4Mη)`-equilibrium.

The window concentration supplies the compiler's concentration hypothesis;
the plan-value floor under unit solo exit supplies its never-quit clause;
one-stage perfectness supplies its spectator quit clauses verbatim. -/
theorem isεAsymptoticNash_soloStationary_of_quietWindow
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start window : ℕ)
    {M εr η : ℝ} (hεr : 0 ≤ εr)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hperfect : QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward roots (start + 1)) (roots start)
      εr)
    (hpositive : 0 < (roots start owner true).toReal)
    (hwindow : 0 < window)
    (hη : 2 * (∑ t ∈ Finset.range window,
        quittingJointSurvivalWeight roots start t *
          quittingRootOpponentAbsorptionMass (roots (start + t)) owner) +
      quittingJointSurvivalWeight roots start window ≤ η)
    (hMη : M * η ≤ 1) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      (εr + 4 * M * η)
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot owner (roots start owner))) := by
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward owner hreward
  have hsum0 : 0 ≤ ∑ t ∈ Finset.range window,
      quittingJointSurvivalWeight roots start t *
        quittingRootOpponentAbsorptionMass (roots (start + t)) owner :=
    Finset.sum_nonneg fun t _ => mul_nonneg
      (quittingJointSurvivalWeight_nonneg roots start t)
      (quittingRootOpponentAbsorptionMass_nonneg _ _)
  have hjsw0 : 0 ≤ quittingJointSurvivalWeight roots start window :=
    quittingJointSurvivalWeight_nonneg roots start window
  have hη0 : 0 ≤ η := by linarith
  have hconcentration : ∀ who,
      |quittingRootSequenceTerminalValue reward roots who start -
        quittingSoloReward reward owner who| ≤ 2 * M * η := by
    intro who
    have hwin := abs_quittingRootSequenceTerminalValue_sub_soloReward_le_window
      reward roots owner who hreward window start
    have hscale := mul_le_mul_of_nonneg_left hη
      (by linarith : (0 : ℝ) ≤ 2 * M)
    linarith
  apply isεAsymptoticNash_soloStationary_of_tail_bounds_of_hazard reward
    (roots start)
    (fun who => quittingRootSequenceTerminalValue reward roots who start)
    owner hεr hη0 hreward ?_ hpositive hconcentration ?_ ?_
  · -- the current stage's opponent hazard is below `η`
    show 1 - quittingStationaryFixedOpponentsContinueMass (roots start)
      owner ≤ η
    have hhazardEq : 1 - quittingStationaryFixedOpponentsContinueMass
        (roots start) owner =
        quittingRootOpponentAbsorptionMass (roots start) owner := rfl
    rw [hhazardEq]
    have hstage : quittingRootOpponentAbsorptionMass (roots start) owner ≤
        ∑ t ∈ Finset.range window,
          quittingJointSurvivalWeight roots start t *
            quittingRootOpponentAbsorptionMass (roots (start + t)) owner := by
      have hmem : 0 ∈ Finset.range window := Finset.mem_range.mpr hwindow
      have hsingle := Finset.single_le_sum
        (f := fun t => quittingJointSurvivalWeight roots start t *
          quittingRootOpponentAbsorptionMass (roots (start + t)) owner)
        (fun t _ => mul_nonneg
          (quittingJointSurvivalWeight_nonneg roots start t)
          (quittingRootOpponentAbsorptionMass_nonneg _ _)) hmem
      have hzero : quittingJointSurvivalWeight roots start 0 = 1 :=
        quittingJointSurvivalWeight_zero_fuel roots start
      simpa [hzero] using hsingle
    linarith
  · -- never quitting cannot fall below the floored plan value
    show -M * η ≤ quittingRootSequenceTerminalValue reward roots owner
      start + εr
    have hconcOwner := hconcentration owner
    have hsoloOwner : quittingSoloReward reward owner owner = 1 := hunit owner
    rw [hsoloOwner] at hconcOwner
    have := (abs_le.mp hconcOwner).1
    nlinarith [mul_nonneg hM hη0]
  · -- spectator quit values are capped by one-stage perfectness
    intro who hne
    have hclause := (hperfect who).1
    have hrec := quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
      reward roots who start
    have hbridge : quittingRootQuitPayoff reward
        (quittingRootSequenceTailVector reward roots (start + 1))
        (roots start) who =
        quittingStationaryFixedOpponentsQuitValue reward (roots start) who := by
      simpa [quittingStationaryFixedOpponentsQuitValue] using
        (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
          (fun _ => roots start) who
          (quittingRootSequenceTailVector reward roots (start + 1)) 0)
    rw [hbridge, ← hrec] at hclause
    exact hclause

end GameTheory
