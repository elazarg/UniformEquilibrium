/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.BonferroniProductBounds
import MathUE.PMFProduct.Bind
import MathUE.PMFProduct.SumFubini
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchProfile
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# Quantitative passive-player padding of terminal exploitability

A finite block of new players can be added to a quitting game without
destroying a positive terminal exploitability gap.  New-only absorption pays
each participating new player a fixed negative penalty, while old players
receive an upper bound on their original terminal reward.  An old profitable
deviation either survives the new clock or some new player profits by
switching permanently to Continue.

The core theorem accepts arbitrary coordinatewise lower and upper bounds.  It
uses the actual live roots of every supplied padded behavior profile and keeps
the unrestricted behavioral-deviation quantifiers of
`HasTerminalExploitabilityGap`.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct StochasticGame

variable {I J : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

/-- Old players contained in a padded terminal coalition. -/
def quittingPassivePaddingOldPart (terminal : Finset (I ⊕ J)) : Finset I :=
  Finset.univ.filter fun old => Sum.inl old ∈ terminal

@[simp] theorem quittingPassivePaddingOldPart_quitters_sumElim
    (old : I → Bool) (fresh : J → Bool) :
    quittingPassivePaddingOldPart
        (quittingQuitters (Sum.elim old fresh)) =
      quittingQuitters old := by
  ext who
  simp [quittingPassivePaddingOldPart, quittingQuitters]

/-- Reward table obtained by adding a finite block of strategically passive
players.  Old-containing coalitions retain the old reward after deleting the
new labels.  New-only absorption pays old players their supplied upper bound
and charges each participating new player `penalty`. -/
def quittingPassivePaddingReward
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ) :
    {T : Finset (I ⊕ J) // T.Nonempty} → Payoff (I ⊕ J) :=
  fun terminal player =>
    if hold : (quittingPassivePaddingOldPart terminal.1).Nonempty then
      match player with
      | .inl old => reward ⟨quittingPassivePaddingOldPart terminal.1, hold⟩ old
      | .inr _ => 0
    else
      match player with
      | .inl old => upper old
      | .inr fresh => if Sum.inr fresh ∈ terminal.1 then -penalty else 0

@[simp] theorem quittingPassivePaddingReward_old_of_old_quits
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ) (old : I → Bool) (fresh : J → Bool)
    (hold : (quittingQuitters old).Nonempty) (who : I) :
    quittingPassivePaddingReward (J := J) reward upper penalty
        ⟨quittingQuitters (Sum.elim old fresh), by
          obtain ⟨owner, howner⟩ := hold
          exact ⟨.inl owner, by simpa [quittingQuitters] using howner⟩⟩ (.inl who) =
      reward ⟨quittingQuitters old, hold⟩ who := by
  simp [quittingPassivePaddingReward, hold]

@[simp] theorem quittingPassivePaddingReward_old_of_fresh_only
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ) (old : I → Bool) (fresh : J → Bool)
    (hold : ¬(quittingQuitters old).Nonempty)
    (hfresh : (quittingQuitters fresh).Nonempty) (who : I) :
    quittingPassivePaddingReward (J := J) reward upper penalty
        ⟨quittingQuitters (Sum.elim old fresh), by
          obtain ⟨owner, howner⟩ := hfresh
          exact ⟨.inr owner, by simpa [quittingQuitters] using howner⟩⟩ (.inl who) =
      upper who := by
  simp [quittingPassivePaddingReward, hold]

/-- Restriction of padded product roots to the old coordinates. -/
def quittingPassivePaddingOldRoots
    (roots : ℕ → I ⊕ J → PMF Bool) : ℕ → I → PMF Bool :=
  fun time old => roots time (.inl old)

/-- Restriction of padded product roots to the new coordinates. -/
def quittingPassivePaddingFreshRoots
    (roots : ℕ → I ⊕ J → PMF Bool) : ℕ → J → PMF Bool :=
  fun time fresh => roots time (.inr fresh)

/-- Project a padded profile by reading its actual old-player live roots. -/
def quittingPassivePaddingProjectProfile
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {upper : I → ℝ} {penalty : ℝ}
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward upper penalty)).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward
    (quittingPassivePaddingOldRoots
      (quittingProfileLiveRoot
        (quittingPassivePaddingReward (J := J) reward upper penalty) profile)) 0

@[simp] theorem quittingProfileLiveRoot_passivePaddingProjectProfile
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {upper : I → ℝ} {penalty : ℝ}
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward upper penalty)).BehaviorProfile) :
    quittingProfileLiveRoot reward
        (quittingPassivePaddingProjectProfile reward profile) =
      quittingPassivePaddingOldRoots
        (quittingProfileLiveRoot
          (quittingPassivePaddingReward (J := J) reward upper penalty) profile) := by
  apply quittingProfileLiveRoot_quittingRootSequenceProfile_zero

omit [DecidableEq I] [DecidableEq J] in
/-- The all-Continue mass of a sum-indexed root factors across the old and
new player blocks. -/
theorem quittingStationaryContinueMass_sumElim
    (old : I → PMF Bool) (fresh : J → PMF Bool) :
    quittingStationaryContinueMass (Sum.elim old fresh) =
      quittingStationaryContinueMass old *
        quittingStationaryContinueMass fresh := by
  simp only [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- At one product root, an old player's padded absorbing contribution is
the original contribution plus the fresh-only absorption mass times the
supplied upper endpoint. -/
theorem quittingRootAbsorbingContribution_passivePadding_old
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ) (old : I → PMF Bool)
    (fresh : J → PMF Bool) (who : I) :
    quittingRootAbsorbingContribution
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        (Sum.elim old fresh) (.inl who) =
      quittingRootAbsorbingContribution reward old who +
        quittingStationaryContinueMass old *
          quittingRootAbsorptionMass fresh * upper who := by
  classical
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [expect_pmfPi_sum]
  have hinner : ∀ oldAction : I → Bool,
      expect (pmfPi fresh) (fun freshAction =>
        quittingRootPayoff
          (quittingPassivePaddingReward (J := J) reward upper penalty) 0
          (Sum.elim oldAction freshAction) (.inl who)) =
        quittingRootPayoff reward 0 oldAction who +
          (if (quittingQuitters oldAction).Nonempty then 0
            else quittingRootAbsorptionMass fresh * upper who) := by
    intro oldAction
    by_cases hold : (quittingQuitters oldAction).Nonempty
    · have hpoint : (fun freshAction =>
          quittingRootPayoff
            (quittingPassivePaddingReward (J := J) reward upper penalty) 0
            (Sum.elim oldAction freshAction) (.inl who)) =
          fun _ => quittingRootPayoff reward 0 oldAction who := by
        funext freshAction
        have hcombined :
            (quittingQuitters (Sum.elim oldAction freshAction)).Nonempty := by
          obtain ⟨owner, howner⟩ := hold
          exact ⟨.inl owner, by simpa [quittingQuitters] using howner⟩
        rw [quittingRootPayoff, dif_pos hcombined,
          quittingRootPayoff, dif_pos hold]
        exact quittingPassivePaddingReward_old_of_old_quits
          reward upper penalty oldAction freshAction hold who
      rw [hpoint, expect_const]
      simp [hold]
    · have hpoint : (fun freshAction =>
          quittingRootPayoff
            (quittingPassivePaddingReward (J := J) reward upper penalty) 0
            (Sum.elim oldAction freshAction) (.inl who)) =
          fun freshAction =>
            upper who *
              (if (quittingQuitters freshAction).Nonempty then 1 else 0) := by
        funext freshAction
        by_cases hfresh : (quittingQuitters freshAction).Nonempty
        · have hcombined :
              (quittingQuitters (Sum.elim oldAction freshAction)).Nonempty := by
            obtain ⟨owner, howner⟩ := hfresh
            exact ⟨.inr owner, by simpa [quittingQuitters] using howner⟩
          rw [quittingRootPayoff, dif_pos hcombined,
            quittingPassivePaddingReward_old_of_fresh_only
              reward upper penalty oldAction freshAction hold hfresh who]
          simp only [if_pos hfresh, mul_one]
        · have hcombined :
              ¬(quittingQuitters (Sum.elim oldAction freshAction)).Nonempty := by
            intro hnonempty
            obtain ⟨player, hplayer⟩ := hnonempty
            cases player with
            | inl owner =>
                apply hold
                exact ⟨owner, by simpa [quittingQuitters] using hplayer⟩
            | inr owner =>
                apply hfresh
                exact ⟨owner, by simpa [quittingQuitters] using hplayer⟩
          simp [quittingRootPayoff, hcombined, hfresh]
      rw [hpoint, expect_const_mul,
        expect_quittingNonemptyIndicator_eq_absorptionMass]
      simp [quittingRootPayoff, hold, mul_comm]
  change expect (pmfPi old) (fun oldAction =>
      expect (pmfPi fresh) (fun freshAction =>
        quittingRootPayoff
          (quittingPassivePaddingReward (J := J) reward upper penalty) 0
          (Sum.elim oldAction freshAction) (.inl who))) = _
  simp_rw [hinner]
  rw [expect_add]
  have hscale : (fun oldAction : I → Bool =>
        if (quittingQuitters oldAction).Nonempty then 0
        else quittingRootAbsorptionMass fresh * upper who) =
      fun oldAction =>
        (quittingRootAbsorptionMass fresh * upper who) *
          (if (quittingQuitters oldAction).Nonempty then 0 else 1) := by
    funext oldAction
    split_ifs <;> ring
  rw [hscale, expect_const_mul]
  have hindicator : expect (pmfPi old) (fun oldAction =>
        if (quittingQuitters oldAction).Nonempty then 0 else (1 : ℝ)) =
      quittingStationaryContinueMass old := by
    have hfunction : (fun oldAction : I → Bool =>
          if (quittingQuitters oldAction).Nonempty then 0 else (1 : ℝ)) =
        fun oldAction =>
          if oldAction = (quittingAllContinueAction : I → Bool)
          then 1 else 0 := by
      funext oldAction
      by_cases hquit : (quittingQuitters oldAction).Nonempty
      · have hne :
            oldAction ≠ (quittingAllContinueAction : I → Bool) := by
          intro heq
          subst oldAction
          simp at hquit
        simp [hquit, hne]
      · have heq :=
            eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty
              oldAction hquit
        simp [heq]
    rw [hfunction]
    rw [← Math.Probability.apply_toReal_eq_expect_indicator]
    rfl
  rw [hindicator]
  ring

/-- A new player's one-stage padded contribution is minus the penalty times
the probability that all old players Continue and that player Quits. -/
theorem quittingRootAbsorbingContribution_passivePadding_fresh
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ) (old : I → PMF Bool)
    (fresh : J → PMF Bool) (who : J) :
    quittingRootAbsorbingContribution
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        (Sum.elim old fresh) (.inr who) =
      -penalty * quittingStationaryContinueMass old *
        (fresh who true).toReal := by
  classical
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [expect_pmfPi_sum]
  change expect (pmfPi old) (fun oldAction =>
      expect (pmfPi fresh) (fun freshAction =>
        quittingRootPayoff
          (quittingPassivePaddingReward (J := J) reward upper penalty) 0
          (Sum.elim oldAction freshAction) (.inr who))) = _
  have hinner : ∀ oldAction : I → Bool,
      expect (pmfPi fresh) (fun freshAction =>
        quittingRootPayoff
          (quittingPassivePaddingReward (J := J) reward upper penalty) 0
          (Sum.elim oldAction freshAction) (.inr who)) =
        if (quittingQuitters oldAction).Nonempty then 0
        else -penalty * (fresh who true).toReal := by
    intro oldAction
    by_cases hold : (quittingQuitters oldAction).Nonempty
    · have hpoint : (fun freshAction =>
          quittingRootPayoff
            (quittingPassivePaddingReward (J := J) reward upper penalty) 0
            (Sum.elim oldAction freshAction) (.inr who)) = fun _ => 0 := by
        funext freshAction
        have hcombined :
            (quittingQuitters (Sum.elim oldAction freshAction)).Nonempty := by
          obtain ⟨owner, howner⟩ := hold
          exact ⟨.inl owner, by simpa [quittingQuitters] using howner⟩
        rw [quittingRootPayoff, dif_pos hcombined]
        simp [quittingPassivePaddingReward, hold]
      rw [hpoint, expect_const]
      simp [hold]
    · have hpoint : (fun freshAction =>
          quittingRootPayoff
            (quittingPassivePaddingReward (J := J) reward upper penalty) 0
            (Sum.elim oldAction freshAction) (.inr who)) =
          fun freshAction => if freshAction who = true then -penalty else 0 := by
        funext freshAction
        by_cases hwho : freshAction who = true
        · have hfresh : (quittingQuitters freshAction).Nonempty := by
            exact ⟨who, by simpa [quittingQuitters] using hwho⟩
          have hcombined :
              (quittingQuitters (Sum.elim oldAction freshAction)).Nonempty := by
            exact ⟨.inr who, by simpa [quittingQuitters] using hwho⟩
          have hmem : Sum.inr who ∈
              quittingQuitters (Sum.elim oldAction freshAction) := by
            simpa [quittingQuitters] using hwho
          rw [quittingRootPayoff, dif_pos hcombined]
          simp [quittingPassivePaddingReward, hold, hwho, hmem]
        · by_cases hfresh : (quittingQuitters freshAction).Nonempty
          · have hcombined :
                (quittingQuitters (Sum.elim oldAction freshAction)).Nonempty := by
              obtain ⟨owner, howner⟩ := hfresh
              exact ⟨.inr owner, by simpa [quittingQuitters] using howner⟩
            have hnotmem : Sum.inr who ∉
                quittingQuitters (Sum.elim oldAction freshAction) := by
              simpa [quittingQuitters] using hwho
            rw [quittingRootPayoff, dif_pos hcombined]
            simp [quittingPassivePaddingReward, hold, hwho, hnotmem]
          · have hcombined :
                ¬(quittingQuitters
                  (Sum.elim oldAction freshAction)).Nonempty := by
              intro hnonempty
              obtain ⟨player, hplayer⟩ := hnonempty
              cases player with
              | inl owner =>
                  apply hold
                  exact ⟨owner, by simpa [quittingQuitters] using hplayer⟩
              | inr owner =>
                  apply hfresh
                  exact ⟨owner, by simpa [quittingQuitters] using hplayer⟩
            simp [quittingRootPayoff, hcombined, hwho]
      rw [hpoint, if_neg hold]
      calc
        expect (pmfPi fresh)
              (fun freshAction =>
                if freshAction who = true then -penalty else 0) =
            expect (pushforward (pmfPi fresh)
              (fun action : J → Bool => action who))
              (fun action => if action = true then -penalty else 0) := by
          symm
          exact expect_map (fun action : J → Bool => action who)
            (pmfPi fresh) _
        _ = expect (fresh who)
              (fun action => if action = true then -penalty else 0) := by
          rw [pmfPi_push_coord]
        _ = -penalty * (fresh who true).toReal := by
          simp [expect_eq_sum]
          ring
  simp_rw [hinner]
  have hscale : (fun oldAction : I → Bool =>
        if (quittingQuitters oldAction).Nonempty then 0
        else -penalty * (fresh who true).toReal) =
      fun oldAction => (-penalty * (fresh who true).toReal) *
        (if (quittingQuitters oldAction).Nonempty then 0 else 1) := by
    funext oldAction
    split_ifs <;> ring
  rw [hscale, expect_const_mul]
  have hindicator : expect (pmfPi old) (fun oldAction =>
        if (quittingQuitters oldAction).Nonempty then 0 else (1 : ℝ)) =
      quittingStationaryContinueMass old := by
    have hfunction : (fun oldAction : I → Bool =>
          if (quittingQuitters oldAction).Nonempty then 0 else (1 : ℝ)) =
        fun oldAction =>
          if oldAction = (quittingAllContinueAction : I → Bool)
          then 1 else 0 := by
      funext oldAction
      by_cases hquit : (quittingQuitters oldAction).Nonempty
      · have hne : oldAction ≠ (quittingAllContinueAction : I → Bool) := by
          intro heq
          subst oldAction
          simp at hquit
        simp [hquit, hne]
      · have heq :=
            eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty
              oldAction hquit
        simp [heq]
    rw [hfunction, ← Math.Probability.apply_toReal_eq_expect_indicator]
    rfl
  rw [hindicator]
  ring

omit [DecidableEq J] in
/-- One-stage absorption is bounded by the sum of the marginal Quit
probabilities. -/
theorem quittingRootAbsorptionMass_le_sum_quitProbability
    (root : J → PMF Bool) :
    quittingRootAbsorptionMass root ≤
      ∑ who, (root who true).toReal := by
  let hazard : J → ℝ := fun who => (root who true).toReal
  have hcontinue : ∀ who, (root who false).toReal = 1 - hazard who := by
    intro who
    linarith [quittingRoot_continueProbability_add_quitProbability root who]
  rw [quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  simpa [hazard, hcontinue] using
    (Math.one_sub_prod_one_sub_le_sum hazard Finset.univ
      (fun who _ => ENNReal.toReal_nonneg)
      (fun who _ => by
        have := ENNReal.toReal_nonneg (a := root who false)
        rw [hcontinue] at this
        linarith))

/-- Finite zero-boundary evaluation of a root sequence at its displayed
marginals. -/
def quittingRootSequenceFiniteValue
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (roots : ℕ → I → PMF Bool) (who : I) (start fuel : ℕ) : ℝ :=
  quittingFiniteRootPayoff reward roots who (fun time => roots time who)
    start fuel

theorem quittingRootSequenceFiniteValue_succ
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (roots : ℕ → I → PMF Bool) (who : I) (start fuel : ℕ) :
    quittingRootSequenceFiniteValue reward roots who start (fuel + 1) =
      quittingRootAbsorbingContribution reward (roots start) who +
      quittingStationaryContinueMass (roots start) *
          quittingRootSequenceFiniteValue reward roots who (start + 1) fuel := by
  unfold quittingRootSequenceFiniteValue
  rw [quittingFiniteRootPayoff]
  rw [Function.update_eq_self,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]

/-- A finite zero-boundary root evaluation remains inside every interval
containing zero and all terminal reward coordinates. -/
theorem quittingRootSequenceFiniteValue_mem_Icc
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (roots : ℕ → I → PMF Bool) (who : I)
    {lower upper : ℝ} (hlower : lower ≤ 0) (hupper : 0 ≤ upper)
    (hreward : ∀ terminal, reward terminal who ∈ Set.Icc lower upper)
    (start fuel : ℕ) :
    quittingRootSequenceFiniteValue reward roots who start fuel ∈
      Set.Icc lower upper := by
  induction fuel generalizing start with
  | zero => exact ⟨hlower, hupper⟩
  | succ fuel ih =>
      unfold quittingRootSequenceFiniteValue quittingFiniteRootPayoff
      rw [Function.update_eq_self]
      constructor
      · calc
          lower = expect (pmfPi (roots start)) (fun _ => lower) := by
            rw [expect_const]
          _ ≤ expect (pmfPi (roots start))
                (fun action => quittingRootPayoff reward
                  (fun _ => quittingRootSequenceFiniteValue reward roots who
                    (start + 1) fuel) action who) := by
            apply expect_mono
            intro action
            by_cases hquit : (quittingQuitters action).Nonempty
            · simp [quittingRootPayoff, hquit, (hreward ⟨_, hquit⟩).1]
            · simp [quittingRootPayoff, hquit, (ih (start + 1)).1]
          _ = _ := rfl
      · calc
          expect (pmfPi (roots start))
                (fun action => quittingRootPayoff reward
                  (fun _ => quittingRootSequenceFiniteValue reward roots who
                    (start + 1) fuel) action who) ≤
              expect (pmfPi (roots start)) (fun _ => upper) := by
            apply expect_mono
            intro action
            by_cases hquit : (quittingQuitters action).Nonempty
            · simp [quittingRootPayoff, hquit, (hreward ⟨_, hquit⟩).2]
            · simp [quittingRootPayoff, hquit, (ih (start + 1)).2]
          _ = upper := by rw [expect_const]

/-- Finite probability that the new block absorbs before the old block in a
sum-indexed root sequence. -/
def quittingPassivePaddingFreshOnlyFiniteMass
    (roots : ℕ → I ⊕ J → PMF Bool) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | start, fuel + 1 =>
      let oldMass := quittingStationaryContinueMass
        (quittingPassivePaddingOldRoots roots start)
      let freshMass := quittingStationaryContinueMass
        (quittingPassivePaddingFreshRoots roots start)
      oldMass * ((1 - freshMass) + freshMass *
        quittingPassivePaddingFreshOnlyFiniteMass roots (start + 1) fuel)

omit [DecidableEq I] [DecidableEq J] in
theorem quittingPassivePaddingFreshOnlyFiniteMass_mem_Icc
    (roots : ℕ → I ⊕ J → PMF Bool) (start fuel : ℕ) :
    quittingPassivePaddingFreshOnlyFiniteMass roots start fuel ∈
      Set.Icc (0 : ℝ) 1 := by
  induction fuel generalizing start with
  | zero => simp [quittingPassivePaddingFreshOnlyFiniteMass]
  | succ fuel ih =>
      simp only [quittingPassivePaddingFreshOnlyFiniteMass]
      have ho0 := quittingStationaryContinueMass_nonneg
        (quittingPassivePaddingOldRoots roots start)
      have ho1 := quittingStationaryContinueMass_le_one
        (quittingPassivePaddingOldRoots roots start)
      have hf0 := quittingStationaryContinueMass_nonneg
        (quittingPassivePaddingFreshRoots roots start)
      have hf1 := quittingStationaryContinueMass_le_one
        (quittingPassivePaddingFreshRoots roots start)
      have hnext := ih (start + 1)
      have hinside0 : 0 ≤
          1 - quittingStationaryContinueMass
              (quittingPassivePaddingFreshRoots roots start) +
            quittingStationaryContinueMass
              (quittingPassivePaddingFreshRoots roots start) *
              quittingPassivePaddingFreshOnlyFiniteMass
                roots (start + 1) fuel :=
        add_nonneg (sub_nonneg.mpr hf1) (mul_nonneg hf0 hnext.1)
      have hinside1 :
          1 - quittingStationaryContinueMass
              (quittingPassivePaddingFreshRoots roots start) +
            quittingStationaryContinueMass
              (quittingPassivePaddingFreshRoots roots start) *
              quittingPassivePaddingFreshOnlyFiniteMass
                roots (start + 1) fuel ≤ 1 := by
        nlinarith [mul_le_mul_of_nonneg_left hnext.2 hf0]
      exact ⟨mul_nonneg ho0 hinside0,
        (mul_le_of_le_one_left hinside0 ho1).trans hinside1⟩

/-- The finite old-player coupling: padding can only increase the old value,
and its increase is at most the coordinate width times fresh-only absorption. -/
theorem quittingRootSequenceFiniteValue_passivePadding_old
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ)
    (roots : ℕ → I ⊕ J → PMF Bool) (who : I)
    {lower : ℝ} (hlower : lower ≤ 0) (hupper : 0 ≤ upper who)
    (hreward : ∀ terminal, reward terminal who ∈ Set.Icc lower (upper who))
    (start fuel : ℕ) :
    let padded := quittingRootSequenceFiniteValue
      (quittingPassivePaddingReward (J := J) reward upper penalty)
      roots (.inl who) start fuel
    let old := quittingRootSequenceFiniteValue reward
      (quittingPassivePaddingOldRoots roots) who start fuel
    0 ≤ padded - old ∧
      padded - old ≤ (upper who - lower) *
        quittingPassivePaddingFreshOnlyFiniteMass roots start fuel := by
  induction fuel generalizing start with
  | zero => norm_num [quittingRootSequenceFiniteValue,
      quittingFiniteRootPayoff, quittingPassivePaddingFreshOnlyFiniteMass]
  | succ fuel ih =>
      dsimp only
      rw [quittingRootSequenceFiniteValue_succ,
        quittingRootSequenceFiniteValue_succ]
      have hroot : roots start = Sum.elim
          (quittingPassivePaddingOldRoots roots start)
          (quittingPassivePaddingFreshRoots roots start) := by
        funext player
        cases player <;> rfl
      rw [hroot,
        quittingRootAbsorbingContribution_passivePadding_old,
        quittingStationaryContinueMass_sumElim]
      simp only [quittingPassivePaddingFreshOnlyFiniteMass]
      let oldRoot := quittingPassivePaddingOldRoots roots start
      let freshRoot := quittingPassivePaddingFreshRoots roots start
      let paddedNext := quittingRootSequenceFiniteValue
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        roots (.inl who) (start + 1) fuel
      let oldNext := quittingRootSequenceFiniteValue reward
        (quittingPassivePaddingOldRoots roots) who (start + 1) fuel
      have hnext := ih (start + 1)
      have holdNext := quittingRootSequenceFiniteValue_mem_Icc
        reward (quittingPassivePaddingOldRoots roots) who hlower hupper
        hreward (start + 1) fuel
      have ho0 := quittingStationaryContinueMass_nonneg oldRoot
      have ho1 := quittingStationaryContinueMass_le_one oldRoot
      have hf0 := quittingStationaryContinueMass_nonneg freshRoot
      have hf1 := quittingStationaryContinueMass_le_one freshRoot
      have hs0 :=
        (quittingPassivePaddingFreshOnlyFiniteMass_mem_Icc
          roots (start + 1) fuel).1
      have hwidth : 0 ≤ upper who - lower := by linarith
      have hfAbs : 0 ≤ 1 - quittingStationaryContinueMass freshRoot := by
        linarith
      have hupperOld : 0 ≤ upper who - oldNext := by
        linarith [holdNext.2]
      have hupperOldWidth : upper who - oldNext ≤ upper who - lower := by
        linarith [holdNext.1]
      have hdiff :
          quittingRootAbsorbingContribution reward oldRoot who +
                quittingStationaryContinueMass oldRoot *
                    quittingRootAbsorptionMass freshRoot * upper who +
              quittingStationaryContinueMass oldRoot *
                  quittingStationaryContinueMass freshRoot * paddedNext -
            (quittingRootAbsorbingContribution reward oldRoot who +
              quittingStationaryContinueMass oldRoot * oldNext) =
          quittingStationaryContinueMass oldRoot *
            ((1 - quittingStationaryContinueMass freshRoot) *
                (upper who - oldNext) +
              quittingStationaryContinueMass freshRoot *
                (paddedNext - oldNext)) := by
        unfold quittingRootAbsorptionMass
        ring
      dsimp only [oldRoot, freshRoot, paddedNext, oldNext] at *
      rw [hdiff]
      constructor
      · exact mul_nonneg ho0 (add_nonneg
          (mul_nonneg hfAbs hupperOld)
          (mul_nonneg hf0 hnext.1))
      · calc
          quittingStationaryContinueMass
                (quittingPassivePaddingOldRoots roots start) *
              ((1 - quittingStationaryContinueMass
                    (quittingPassivePaddingFreshRoots roots start)) *
                  (upper who - quittingRootSequenceFiniteValue reward
                    (quittingPassivePaddingOldRoots roots) who
                    (start + 1) fuel) +
                quittingStationaryContinueMass
                    (quittingPassivePaddingFreshRoots roots start) *
                  (quittingRootSequenceFiniteValue
                      (quittingPassivePaddingReward (J := J)
                        reward upper penalty)
                      roots (.inl who) (start + 1) fuel -
                    quittingRootSequenceFiniteValue reward
                      (quittingPassivePaddingOldRoots roots) who
                      (start + 1) fuel)) ≤
              quittingStationaryContinueMass
                  (quittingPassivePaddingOldRoots roots start) *
                ((1 - quittingStationaryContinueMass
                      (quittingPassivePaddingFreshRoots roots start)) *
                    (upper who - lower) +
                  quittingStationaryContinueMass
                      (quittingPassivePaddingFreshRoots roots start) *
                    ((upper who - lower) *
                      quittingPassivePaddingFreshOnlyFiniteMass
                        roots (start + 1) fuel)) := by
            gcongr
            exact hnext.2
          _ = (upper who - lower) *
              (quittingStationaryContinueMass
                (quittingPassivePaddingOldRoots roots start) *
                (1 - quittingStationaryContinueMass
                    (quittingPassivePaddingFreshRoots roots start) +
                  quittingStationaryContinueMass
                      (quittingPassivePaddingFreshRoots roots start) *
                    quittingPassivePaddingFreshOnlyFiniteMass
                      roots (start + 1) fuel)) := by ring

/-- Across the whole new block, finite padded payoff is at most minus the
penalty times fresh-only absorption. -/
theorem sum_quittingRootSequenceFiniteValue_passivePadding_fresh_le
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) {penalty : ℝ} (hpenalty : 0 ≤ penalty)
    (roots : ℕ → I ⊕ J → PMF Bool) (start fuel : ℕ) :
    (∑ who : J, quittingRootSequenceFiniteValue
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        roots (.inr who) start fuel) ≤
      -penalty *
        quittingPassivePaddingFreshOnlyFiniteMass roots start fuel := by
  induction fuel generalizing start with
  | zero => simp [quittingRootSequenceFiniteValue,
      quittingFiniteRootPayoff, quittingPassivePaddingFreshOnlyFiniteMass]
  | succ fuel ih =>
      simp_rw [quittingRootSequenceFiniteValue_succ]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hroot : roots start = Sum.elim
          (quittingPassivePaddingOldRoots roots start)
          (quittingPassivePaddingFreshRoots roots start) := by
        funext player
        cases player <;> rfl
      rw [hroot, quittingStationaryContinueMass_sumElim]
      simp_rw [quittingRootAbsorbingContribution_passivePadding_fresh]
      rw [← Finset.mul_sum]
      simp only [quittingPassivePaddingFreshOnlyFiniteMass]
      let oldMass := quittingStationaryContinueMass
        (quittingPassivePaddingOldRoots roots start)
      let freshMass := quittingStationaryContinueMass
        (quittingPassivePaddingFreshRoots roots start)
      let freshHazard := ∑ who : J,
        (quittingPassivePaddingFreshRoots roots start who true).toReal
      let nextPayoff := ∑ who : J, quittingRootSequenceFiniteValue
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        roots (.inr who) (start + 1) fuel
      let nextMass := quittingPassivePaddingFreshOnlyFiniteMass
        roots (start + 1) fuel
      have ho0 : 0 ≤ oldMass := quittingStationaryContinueMass_nonneg _
      have hf0 : 0 ≤ freshMass := quittingStationaryContinueMass_nonneg _
      have habs0 : 0 ≤ quittingRootAbsorptionMass
          (quittingPassivePaddingFreshRoots roots start) :=
        quittingRootAbsorptionMass_nonneg _
      have hunion : quittingRootAbsorptionMass
          (quittingPassivePaddingFreshRoots roots start) ≤ freshHazard :=
        quittingRootAbsorptionMass_le_sum_quitProbability _
      have hnext : nextPayoff ≤ -penalty * nextMass := ih (start + 1)
      have hfirst : -penalty * oldMass * freshHazard ≤
          -penalty * oldMass * quittingRootAbsorptionMass
            (quittingPassivePaddingFreshRoots roots start) := by
        have hcoefficient : -penalty * oldMass ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpenalty) ho0
        exact mul_le_mul_of_nonpos_left hunion hcoefficient
      have hsecond : oldMass * freshMass * nextPayoff ≤
          oldMass * freshMass * (-penalty * nextMass) := by
        exact mul_le_mul_of_nonneg_left hnext (mul_nonneg ho0 hf0)
      dsimp only [oldMass, freshMass, freshHazard, nextPayoff, nextMass] at *
      calc
        -penalty *
              quittingStationaryContinueMass
                (quittingPassivePaddingOldRoots roots start) *
              ∑ x,
                (quittingPassivePaddingFreshRoots roots start x true).toReal +
            (quittingStationaryContinueMass
                (quittingPassivePaddingOldRoots roots start) *
              quittingStationaryContinueMass
                (quittingPassivePaddingFreshRoots roots start)) *
              ∑ x,
                quittingRootSequenceFiniteValue
                  (quittingPassivePaddingReward (J := J)
                    reward upper penalty)
                  roots (.inr x) (start + 1) fuel ≤
          -penalty *
              quittingStationaryContinueMass
                (quittingPassivePaddingOldRoots roots start) *
              quittingRootAbsorptionMass
                (quittingPassivePaddingFreshRoots roots start) +
            (quittingStationaryContinueMass
                (quittingPassivePaddingOldRoots roots start) *
              quittingStationaryContinueMass
                (quittingPassivePaddingFreshRoots roots start)) *
              (-penalty *
                quittingPassivePaddingFreshOnlyFiniteMass
                  roots (start + 1) fuel) := add_le_add hfirst hsecond
        _ = -penalty *
            (quittingStationaryContinueMass
              (quittingPassivePaddingOldRoots roots start) *
              (1 - quittingStationaryContinueMass
                  (quittingPassivePaddingFreshRoots roots start) +
                quittingStationaryContinueMass
                    (quittingPassivePaddingFreshRoots roots start) *
                  quittingPassivePaddingFreshOnlyFiniteMass
                    roots (start + 1) fuel)) := by
          unfold quittingRootAbsorptionMass
          ring

/-- Unconditional mass of fresh-only first absorption at one live date. -/
def quittingPassivePaddingFreshOnlyStageMass
    (roots : ℕ → I ⊕ J → PMF Bool) (start offset : ℕ) : ℝ :=
  quittingJointSurvivalWeight roots start offset *
    quittingStationaryContinueMass
      (quittingPassivePaddingOldRoots roots (start + offset)) *
    quittingRootAbsorptionMass
      (quittingPassivePaddingFreshRoots roots (start + offset))

omit [DecidableEq I] [DecidableEq J] in
theorem quittingPassivePaddingFreshOnlyStageMass_nonneg
    (roots : ℕ → I ⊕ J → PMF Bool) (start offset : ℕ) :
    0 ≤ quittingPassivePaddingFreshOnlyStageMass roots start offset := by
  exact mul_nonneg
    (mul_nonneg (quittingJointSurvivalWeight_nonneg roots start offset)
      (quittingStationaryContinueMass_nonneg _))
    (quittingRootAbsorptionMass_nonneg _)

omit [DecidableEq I] [DecidableEq J] in
theorem quittingPassivePaddingFreshOnlyStageMass_le_absorption
    (roots : ℕ → I ⊕ J → PMF Bool) (start offset : ℕ) :
    quittingPassivePaddingFreshOnlyStageMass roots start offset ≤
      quittingJointSurvivalWeight roots start offset *
        (1 - quittingStationaryContinueMass (roots (start + offset))) := by
  have hroot : roots (start + offset) = Sum.elim
      (quittingPassivePaddingOldRoots roots (start + offset))
      (quittingPassivePaddingFreshRoots roots (start + offset)) := by
    funext player
    cases player <;> rfl
  rw [hroot, quittingStationaryContinueMass_sumElim]
  unfold quittingPassivePaddingFreshOnlyStageMass
  have ho0 := quittingStationaryContinueMass_nonneg
    (quittingPassivePaddingOldRoots roots (start + offset))
  have ho1 := quittingStationaryContinueMass_le_one
    (quittingPassivePaddingOldRoots roots (start + offset))
  have hf0 := quittingStationaryContinueMass_nonneg
    (quittingPassivePaddingFreshRoots roots (start + offset))
  have hf1 := quittingStationaryContinueMass_le_one
    (quittingPassivePaddingFreshRoots roots (start + offset))
  have hsurvival := quittingJointSurvivalWeight_nonneg roots start offset
  unfold quittingRootAbsorptionMass
  have hinner :
      quittingStationaryContinueMass
          (quittingPassivePaddingOldRoots roots (start + offset)) *
        (1 - quittingStationaryContinueMass
          (quittingPassivePaddingFreshRoots roots (start + offset))) ≤
      1 - quittingStationaryContinueMass
          (quittingPassivePaddingOldRoots roots (start + offset)) *
        quittingStationaryContinueMass
          (quittingPassivePaddingFreshRoots roots (start + offset)) := by
    nlinarith
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left hinner hsurvival)

omit [DecidableEq I] [DecidableEq J] in
theorem summable_quittingPassivePaddingFreshOnlyStageMass
    (roots : ℕ → I ⊕ J → PMF Bool) (start : ℕ) :
    Summable (quittingPassivePaddingFreshOnlyStageMass roots start) := by
  apply summable_of_sum_range_le
    (quittingPassivePaddingFreshOnlyStageMass_nonneg roots start)
  intro fuel
  calc
    ∑ offset ∈ Finset.range fuel,
        quittingPassivePaddingFreshOnlyStageMass roots start offset ≤
      ∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight roots start offset *
          (1 - quittingStationaryContinueMass
            (roots (start + offset))) :=
      Finset.sum_le_sum fun offset _ =>
        quittingPassivePaddingFreshOnlyStageMass_le_absorption
          roots start offset
    _ = 1 - quittingJointSurvivalWeight roots start fuel :=
      sum_quittingJointSurvivalWeight_mul_one_sub_continueMass
        roots start fuel
    _ ≤ 1 := by
      linarith [quittingJointSurvivalWeight_nonneg roots start fuel]

/-- Total probability that the new block is the first block to absorb. -/
def quittingPassivePaddingFreshOnlyMass
    (roots : ℕ → I ⊕ J → PMF Bool) (start : ℕ := 0) : ℝ :=
  ∑' offset, quittingPassivePaddingFreshOnlyStageMass roots start offset

omit [DecidableEq I] [DecidableEq J] in
theorem quittingPassivePaddingFreshOnlyMass_nonneg
    (roots : ℕ → I ⊕ J → PMF Bool) (start : ℕ) :
    0 ≤ quittingPassivePaddingFreshOnlyMass roots start := by
  exact tsum_nonneg fun offset =>
    quittingPassivePaddingFreshOnlyStageMass_nonneg roots start offset

omit [DecidableEq I] [DecidableEq J] in
theorem quittingPassivePaddingFreshOnlyFiniteMass_eq_sum
    (roots : ℕ → I ⊕ J → PMF Bool) (start fuel : ℕ) :
    quittingPassivePaddingFreshOnlyFiniteMass roots start fuel =
      ∑ offset ∈ Finset.range fuel,
        quittingPassivePaddingFreshOnlyStageMass roots start offset := by
  induction fuel generalizing start with
  | zero => simp [quittingPassivePaddingFreshOnlyFiniteMass]
  | succ fuel ih =>
      rw [Finset.sum_range_succ']
      have hstage : ∀ offset,
          quittingPassivePaddingFreshOnlyStageMass roots start (offset + 1) =
            quittingStationaryContinueMass (roots start) *
              quittingPassivePaddingFreshOnlyStageMass
                roots (start + 1) offset := by
        intro offset
        unfold quittingPassivePaddingFreshOnlyStageMass
        rw [show offset + 1 = 1 + offset by omega,
          quittingJointSurvivalWeight_add]
        simp only [quittingJointSurvivalWeight,
          quittingFiniteContinueWeight, Nat.add_assoc]
        ring
      simp_rw [hstage, ← Finset.mul_sum, ← ih (start := start + 1)]
      simp only [quittingPassivePaddingFreshOnlyFiniteMass,
        quittingPassivePaddingFreshOnlyStageMass,
        quittingJointSurvivalWeight, quittingFiniteContinueWeight, one_mul]
      have hroot : roots start = Sum.elim
          (quittingPassivePaddingOldRoots roots start)
          (quittingPassivePaddingFreshRoots roots start) := by
        funext player
        cases player <;> rfl
      rw [hroot, quittingStationaryContinueMass_sumElim]
      unfold quittingRootAbsorptionMass
      ring_nf

omit [DecidableEq I] [DecidableEq J] in
theorem tendsto_quittingPassivePaddingFreshOnlyFiniteMass
    (roots : ℕ → I ⊕ J → PMF Bool) (start : ℕ) :
    Filter.Tendsto
      (quittingPassivePaddingFreshOnlyFiniteMass roots start)
      Filter.atTop
      (nhds (quittingPassivePaddingFreshOnlyMass roots start)) := by
  have heq : quittingPassivePaddingFreshOnlyFiniteMass roots start =
      fun fuel => ∑ offset ∈ Finset.range fuel,
        quittingPassivePaddingFreshOnlyStageMass roots start offset := by
    funext fuel
    exact quittingPassivePaddingFreshOnlyFiniteMass_eq_sum roots start fuel
  rw [heq]
  exact (summable_quittingPassivePaddingFreshOnlyStageMass roots start).hasSum
    |>.tendsto_sum_nat

/-- Infinite-horizon old-player coupling for arbitrary time-dependent product
roots. -/
theorem quittingRootSequenceTerminalValue_passivePadding_old
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ)
    (roots : ℕ → I ⊕ J → PMF Bool) (who : I)
    {lower : ℝ} (hlower : lower ≤ 0) (hupper : 0 ≤ upper who)
    (hreward : ∀ terminal, reward terminal who ∈ Set.Icc lower (upper who))
    (start : ℕ) :
    let padded := quittingRootSequenceTerminalValue
      (quittingPassivePaddingReward (J := J) reward upper penalty)
      roots (.inl who) start
    let old := quittingRootSequenceTerminalValue reward
      (quittingPassivePaddingOldRoots roots) who start
    0 ≤ padded - old ∧
      padded - old ≤ (upper who - lower) *
        quittingPassivePaddingFreshOnlyMass roots start := by
  dsimp only
  have hpadded := tendsto_quittingFiniteRootPayoff_self_terminalValue
    (quittingPassivePaddingReward (J := J) reward upper penalty)
    roots (.inl who) start
  have hold := tendsto_quittingFiniteRootPayoff_self_terminalValue
    reward (quittingPassivePaddingOldRoots roots) who start
  have hdiff : Filter.Tendsto (fun fuel =>
      quittingRootSequenceFiniteValue
          (quittingPassivePaddingReward (J := J) reward upper penalty)
          roots (.inl who) start fuel -
        quittingRootSequenceFiniteValue reward
          (quittingPassivePaddingOldRoots roots) who start fuel)
      Filter.atTop
      (nhds (quittingRootSequenceTerminalValue
          (quittingPassivePaddingReward (J := J) reward upper penalty)
          roots (.inl who) start -
        quittingRootSequenceTerminalValue reward
          (quittingPassivePaddingOldRoots roots) who start)) := by
    simpa only [quittingRootSequenceFiniteValue] using hpadded.sub hold
  have hmass :=
    tendsto_quittingPassivePaddingFreshOnlyFiniteMass roots start
  constructor
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds hdiff
      (Filter.Eventually.of_forall fun fuel =>
        (quittingRootSequenceFiniteValue_passivePadding_old
          reward upper penalty roots who hlower hupper hreward start fuel).1)
  · have hright := hmass.const_mul (upper who - lower)
    exact le_of_tendsto_of_tendsto hdiff hright
      (Filter.Eventually.of_forall fun fuel =>
        (quittingRootSequenceFiniteValue_passivePadding_old
          reward upper penalty roots who hlower hupper hreward start fuel).2)

/-- The infinite-horizon sum of the new players' padded payoffs is bounded by
minus the penalty times fresh-only first absorption. -/
theorem sum_quittingRootSequenceTerminalValue_passivePadding_fresh_le
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) {penalty : ℝ} (hpenalty : 0 ≤ penalty)
    (roots : ℕ → I ⊕ J → PMF Bool) (start : ℕ) :
    (∑ who : J, quittingRootSequenceTerminalValue
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        roots (.inr who) start) ≤
      -penalty * quittingPassivePaddingFreshOnlyMass roots start := by
  have hvalue : ∀ who : J, Filter.Tendsto (fun fuel =>
      quittingRootSequenceFiniteValue
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        roots (.inr who) start fuel) Filter.atTop
      (nhds (quittingRootSequenceTerminalValue
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        roots (.inr who) start)) := by
    intro who
    simpa only [quittingRootSequenceFiniteValue] using
      (tendsto_quittingFiniteRootPayoff_self_terminalValue
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        roots (.inr who) start)
  have hsum : Filter.Tendsto (fun fuel =>
      ∑ who : J, quittingRootSequenceFiniteValue
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        roots (.inr who) start fuel) Filter.atTop
      (nhds (∑ who : J, quittingRootSequenceTerminalValue
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        roots (.inr who) start)) := by
    exact tendsto_finsetSum (Finset.univ : Finset J)
      (fun who _ => hvalue who)
  have hmass :=
    (tendsto_quittingPassivePaddingFreshOnlyFiniteMass roots start).const_mul
      (-penalty)
  exact le_of_tendsto_of_tendsto hsum hmass
    (Filter.Eventually.of_forall fun fuel =>
      sum_quittingRootSequenceFiniteValue_passivePadding_fresh_le
        reward upper hpenalty roots start fuel)

/-- A padded new player who never Quits receives exactly zero, regardless of
the other players' behavior. -/
theorem quittingRootSequenceHazardTerminalValue_passivePadding_fresh_never
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ)
    (roots : ℕ → I ⊕ J → PMF Bool) (who : J) (start : ℕ) :
    quittingRootSequenceHazardTerminalValue
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        roots (.inr who) (fun _ => PMF.pure false) start = 0 := by
  unfold quittingRootSequenceHazardTerminalValue
  rw [quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution]
  calc
    ∑' offset,
        quittingJointSurvivalWeight
            (quittingRootSequenceUpdate roots (.inr who)
              (fun _ => PMF.pure false)) start offset *
          quittingRootAbsorbingContribution
            (quittingPassivePaddingReward (J := J) reward upper penalty)
            ((quittingRootSequenceUpdate roots (.inr who)
              (fun _ => PMF.pure false)) (start + offset)) (.inr who) =
        ∑' _offset : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro offset
      apply mul_eq_zero_of_right
      let updated := quittingRootSequenceUpdate roots (.inr who)
        (fun _ => PMF.pure false)
      have hroot : updated (start + offset) = Sum.elim
          (quittingPassivePaddingOldRoots roots (start + offset))
          (Function.update
            (quittingPassivePaddingFreshRoots roots (start + offset))
            who (PMF.pure false)) := by
        funext player
        cases player with
        | inl old => rfl
        | inr fresh =>
            by_cases hfresh : fresh = who
            · subst fresh
              simp [updated, quittingRootSequenceUpdate]
            · simp [updated, quittingRootSequenceUpdate,
                quittingPassivePaddingFreshRoots,
                Function.update_of_ne hfresh]
      change quittingRootAbsorbingContribution
          (quittingPassivePaddingReward (J := J) reward upper penalty)
          (updated (start + offset)) (.inr who) = 0
      rw [hroot,
        quittingRootAbsorbingContribution_passivePadding_fresh]
      simp
    _ = 0 := tsum_zero

/-- Behavioral-profile form of the passive new player's exact Never payoff. -/
theorem quittingTerminalPayoff_update_passivePadding_fresh_never_eq_zero
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward upper penalty)).BehaviorProfile)
    (who : J) :
    quittingTerminalPayoff
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        (Function.update profile (.inr who)
          (quittingPureTimeBehaviorStrategy
            (quittingPassivePaddingReward (J := J) reward upper penalty)
            (.inr who) none)) (.inr who) = 0 := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  unfold quittingRootSequencePureTimeTerminalValue
  have hpure : quittingPureTimeHazard none = fun _ => PMF.pure false := by
    funext time
    exact quittingPureTimeHazard_none time
  rw [hpure]
  exact
    quittingRootSequenceHazardTerminalValue_passivePadding_fresh_never
      reward upper penalty
      (quittingProfileLiveRoot
        (quittingPassivePaddingReward (J := J) reward upper penalty) profile)
      who 0

/-- Behavioral-profile form of the old-coordinate terminal coupling. -/
theorem quittingTerminalPayoff_passivePadding_old
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward upper penalty)).BehaviorProfile)
    (who : I) {lower : ℝ} (hlower : lower ≤ 0)
    (hupper : 0 ≤ upper who)
    (hreward : ∀ terminal, reward terminal who ∈ Set.Icc lower (upper who)) :
    let padded := quittingTerminalPayoff
      (quittingPassivePaddingReward (J := J) reward upper penalty)
      profile (.inl who)
    let old := quittingTerminalPayoff reward
      (quittingPassivePaddingProjectProfile reward profile) who
    0 ≤ padded - old ∧
      padded - old ≤ (upper who - lower) *
        quittingPassivePaddingFreshOnlyMass
          (quittingProfileLiveRoot
            (quittingPassivePaddingReward (J := J) reward upper penalty)
            profile) 0 := by
  dsimp only
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingProfileLiveRoot_passivePaddingProjectProfile]
  exact quittingRootSequenceTerminalValue_passivePadding_old
    reward upper penalty
    (quittingProfileLiveRoot
      (quittingPassivePaddingReward (J := J) reward upper penalty) profile)
    who hlower hupper hreward 0

/-- Behavioral-profile form of the aggregate new-player penalty account. -/
theorem sum_quittingTerminalPayoff_passivePadding_fresh_le
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) {penalty : ℝ} (hpenalty : 0 ≤ penalty)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward upper penalty)).BehaviorProfile) :
    (∑ who : J, quittingTerminalPayoff
      (quittingPassivePaddingReward (J := J) reward upper penalty)
      profile (.inr who)) ≤
      -penalty * quittingPassivePaddingFreshOnlyMass
        (quittingProfileLiveRoot
          (quittingPassivePaddingReward (J := J) reward upper penalty)
          profile) 0 := by
  simp_rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  exact sum_quittingRootSequenceTerminalValue_passivePadding_fresh_le
    reward upper hpenalty
    (quittingProfileLiveRoot
      (quittingPassivePaddingReward (J := J) reward upper penalty) profile) 0

/-- Lift an old behavioral deviation to the padded game by replaying its
actual live-history hazards. -/
def quittingPassivePaddingLiftOldDeviation
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ) {who : I}
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    (quittingGame
      (quittingPassivePaddingReward (J := J) reward upper penalty)).BehaviorStrategy
        (.inl who) :=
  fun time _history => quittingBehaviorLiveHazard reward deviation time

@[simp] theorem quittingBehaviorLiveHazard_passivePaddingLiftOldDeviation
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ) {who : I}
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingBehaviorLiveHazard
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        (quittingPassivePaddingLiftOldDeviation
          (J := J) reward upper penalty deviation) =
      quittingBehaviorLiveHazard reward deviation := by
  rfl

/-- An old behavioral deviation is worth at least its projected old-game
value when lifted to the padded profile. -/
theorem quittingTerminalPayoff_update_passivePadding_old_ge
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward upper penalty)).BehaviorProfile)
    (who : I) (deviation : (quittingGame reward).BehaviorStrategy who)
    {lower : ℝ} (hlower : lower ≤ 0) (hupper : 0 ≤ upper who)
    (hreward : ∀ terminal, reward terminal who ∈ Set.Icc lower (upper who)) :
    quittingTerminalPayoff
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        (Function.update profile (.inl who)
          (quittingPassivePaddingLiftOldDeviation
            (J := J) reward upper penalty deviation)) (.inl who) ≥
      quittingTerminalPayoff reward
        (Function.update (quittingPassivePaddingProjectProfile reward profile)
          who deviation) who := by
  let roots := quittingProfileLiveRoot
    (quittingPassivePaddingReward (J := J) reward upper penalty) profile
  let hazard := quittingBehaviorLiveHazard reward deviation
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue]
  simp only [quittingBehaviorLiveHazard_passivePaddingLiftOldDeviation,
    quittingProfileLiveRoot_passivePaddingProjectProfile]
  unfold quittingRootSequenceHazardTerminalValue
  let updated := quittingRootSequenceUpdate roots (.inl who) hazard
  have holdUpdated : quittingPassivePaddingOldRoots updated =
      quittingRootSequenceUpdate
        (quittingPassivePaddingOldRoots roots) who hazard := by
    funext time old
    by_cases hold : old = who
    · subst old
      simp [updated, quittingRootSequenceUpdate,
        quittingPassivePaddingOldRoots]
    · simp [updated, quittingRootSequenceUpdate,
        quittingPassivePaddingOldRoots, Function.update_of_ne hold]
  have hcomparison :=
    (quittingRootSequenceTerminalValue_passivePadding_old
      reward upper penalty updated who hlower hupper hreward 0).1
  rw [holdUpdated] at hcomparison
  exact sub_nonneg.mp hcomparison

/-- Elementary balancing inequality behind passive padding. -/
theorem passivePadding_balance
    {penalty players width gap mass : ℝ}
    (hpenalty : 0 < penalty) (hplayers : 0 < players)
    (hwidth : 0 ≤ width) :
    penalty / (penalty + players * width) * gap ≤
      max (gap - width * mass) (penalty * mass / players) := by
  have hdenom : 0 < penalty + players * width := by positivity
  let target := penalty / (penalty + players * width) * gap
  by_cases hold : target ≤ gap - width * mass
  · exact hold.trans (le_max_left _ _)
  · have hstrict : gap - width * mass < target := lt_of_not_ge hold
    have hnew : target ≤ penalty * mass / players := by
      by_cases hwidthZero : width = 0
      · subst width
        have htargetEq : target = gap := by
          dsimp [target]
          rw [mul_zero, add_zero, div_self hpenalty.ne']
          simp
        linarith
      · have hwidthPos : 0 < width := lt_of_le_of_ne hwidth
            (Ne.symm hwidthZero)
        have htarget : target * (penalty + players * width) =
            penalty * gap := by
          dsimp [target]
          field_simp
        have hmassBound : players * gap ≤
            mass * (penalty + players * width) := by
          nlinarith [mul_pos hwidthPos hdenom]
        apply (le_div_iff₀ hplayers).2
        calc
          target * players =
              penalty * (players * gap) /
                (penalty + players * width) := by
            dsimp [target]
            field_simp
          _ ≤ penalty *
                (mass * (penalty + players * width)) /
                (penalty + players * width) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hmassBound hpenalty.le)
              hdenom.le
          _ = penalty * mass := by
            field_simp
    exact hnew.trans (le_max_right _ _)

/-- **Quantitative passive-player padding.** A terminal exploitability gap
survives adding any nonempty finite block of passive players, with the sharp
factor `penalty / (penalty + card J * width)`. -/
theorem HasTerminalExploitabilityGap.passivePlayerPadding
    [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (lower upper : I → ℝ) {penalty width gap : ℝ}
    (hpenalty : 0 < penalty) (hwidth : 0 ≤ width)
    (hlower : ∀ who, lower who ≤ 0)
    (hupper : ∀ who, 0 ≤ upper who)
    (hreward : ∀ terminal who,
      reward terminal who ∈ Set.Icc (lower who) (upper who))
    (hoscillation : ∀ who, upper who - lower who ≤ width)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    HasTerminalExploitabilityGap
      (quittingPassivePaddingReward (J := J) reward upper penalty)
      (penalty / (penalty + (Fintype.card J : ℝ) * width) * gap) := by
  intro profile
  let paddedReward :=
    quittingPassivePaddingReward (J := J) reward upper penalty
  let projected := quittingPassivePaddingProjectProfile reward profile
  let roots := quittingProfileLiveRoot paddedReward profile
  let mass := quittingPassivePaddingFreshOnlyMass roots 0
  let players : ℝ := Fintype.card J
  let transported := penalty / (penalty + players * width) * gap
  have hplayers : 0 < players := by
    dsimp only [players]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J)
  have hmass : 0 ≤ mass :=
    quittingPassivePaddingFreshOnlyMass_nonneg roots 0
  obtain ⟨oldWho, oldDeviation, holdDeviation⟩ := hexploit projected
  let lifted := quittingPassivePaddingLiftOldDeviation
    (J := J) reward upper penalty oldDeviation
  have hbase := quittingTerminalPayoff_passivePadding_old
    (J := J) reward upper penalty profile oldWho
    (hlower oldWho) (hupper oldWho) (hreward · oldWho)
  have hlift := quittingTerminalPayoff_update_passivePadding_old_ge
    (J := J) reward upper penalty profile oldWho oldDeviation
    (hlower oldWho) (hupper oldWho) (hreward · oldWho)
  have hbaseWidth :
      quittingTerminalPayoff paddedReward profile (.inl oldWho) -
          quittingTerminalPayoff reward projected oldWho ≤ width * mass := by
    calc
      quittingTerminalPayoff paddedReward profile (.inl oldWho) -
          quittingTerminalPayoff reward projected oldWho ≤
        (upper oldWho - lower oldWho) * mass := hbase.2
      _ ≤ width * mass :=
        mul_le_mul_of_nonneg_right (hoscillation oldWho) hmass
  have holdGain :
      quittingTerminalPayoff paddedReward profile (.inl oldWho) +
          (gap - width * mass) ≤
        quittingTerminalPayoff paddedReward
          (Function.update profile (.inl oldWho) lifted) (.inl oldWho) := by
    dsimp only [projected] at holdDeviation hlift
    dsimp only [paddedReward, mass, roots] at hbaseWidth ⊢
    linarith
  have hsumPayoff := sum_quittingTerminalPayoff_passivePadding_fresh_le
    (J := J) reward upper hpenalty.le profile
  have hsumGain : penalty * mass ≤
      ∑ who : J, -quittingTerminalPayoff paddedReward profile (.inr who) := by
    dsimp only [paddedReward, mass, roots] at hsumPayoff ⊢
    rw [show (∑ who : J,
        -quittingTerminalPayoff
          (quittingPassivePaddingReward (J := J) reward upper penalty)
          profile (.inr who)) =
        -(∑ who : J, quittingTerminalPayoff
          (quittingPassivePaddingReward (J := J) reward upper penalty)
          profile (.inr who)) by simp]
    linarith
  have hconstant :
      (∑ _who : J, penalty * mass / players) = penalty * mass := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ]
    change players * (penalty * mass / players) = penalty * mass
    field_simp
  have haverageSum :
      (∑ _who : J, penalty * mass / players) ≤
        ∑ who : J, -quittingTerminalPayoff paddedReward profile (.inr who) := by
    rw [hconstant]
    exact hsumGain
  obtain ⟨freshWho, _, hfreshGain⟩ :=
    Finset.exists_le_of_sum_le
      (show (Finset.univ : Finset J).Nonempty from Finset.univ_nonempty)
      haverageSum
  have hbalance := passivePadding_balance (gap := gap) (mass := mass)
    hpenalty hplayers hwidth
  change transported ≤
    max (gap - width * mass) (penalty * mass / players) at hbalance
  change ∃ who dev,
    quittingTerminalPayoff paddedReward profile who + transported ≤
      quittingTerminalPayoff paddedReward
        (Function.update profile who dev) who
  by_cases hroute : transported ≤ gap - width * mass
  · refine ⟨.inl oldWho, lifted, ?_⟩
    linarith
  · have hfreshRoute : transported ≤ penalty * mass / players := by
      by_contra hnew
      have holdlt : gap - width * mass < transported := lt_of_not_ge hroute
      have hnewlt : penalty * mass / players < transported :=
        lt_of_not_ge hnew
      have hmaxlt :
          max (gap - width * mass) (penalty * mass / players) <
            transported := max_lt holdlt hnewlt
      exact (not_lt_of_ge hbalance) hmaxlt
    let never := quittingPureTimeBehaviorStrategy paddedReward (.inr freshWho) none
    refine ⟨.inr freshWho, never, ?_⟩
    have hnever :=
      quittingTerminalPayoff_update_passivePadding_fresh_never_eq_zero
        (J := J) reward upper penalty profile freshWho
    dsimp only [never, paddedReward]
    rw [hnever]
    dsimp only [paddedReward, mass, roots, players] at hfreshGain hfreshRoute ⊢
    linarith

end GameTheory
