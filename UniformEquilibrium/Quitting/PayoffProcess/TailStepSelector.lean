/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PerfectSequenceExtraction
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback
import UniformEquilibrium.Quitting.Paths.LiveTail

/-!
# Measurable step selection of constant-table quitting equilibria

Solan--Vieille's general-payoff-process argument needs an adapted tail
equilibrium after a deterministic cutoff.  The infinite-horizon selector is
only a countable step function: select a nearby table satisfying the solo-exit
assumptions, then use one fixed equilibrium chosen for that table.
-/

noncomputable section

namespace GameTheory

open StochasticGame Set TopologicalSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The constant quitting tables covered by Solan--Vieille's existence
theorem. -/
def soloExitRewardSet : Set
    ({S : Finset ι // S.Nonempty} → Payoff ι) :=
  {reward | QuittingUnitSoloExit reward ∧ QuittingCappedJointExit reward}

omit [DecidableEq ι] in
/-- Terminal payoff is one-Lipschitz in the terminal table under the uniform
coordinate metric. -/
theorem abs_quittingTerminalPayoff_sub_le_of_forall_abs_sub_le
    (first second : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame first).BehaviorProfile) (who : ι)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ terminal player,
      |first terminal player - second terminal player| ≤ ε) :
    |quittingTerminalPayoff first profile who -
        quittingTerminalPayoff second profile who| ≤ ε := by
  classical
  unfold quittingTerminalPayoff
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ terminal, (
        quittingAbsorbedMassLimit first profile terminal *
            first terminal who -
          quittingAbsorbedMassLimit second profile terminal *
            second terminal who)| ≤
        ∑ terminal,
          |quittingAbsorbedMassLimit first profile terminal *
              first terminal who -
            quittingAbsorbedMassLimit second profile terminal *
              second terminal who| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ terminal,
          quittingAbsorbedMassLimit first profile terminal *
            |first terminal who - second terminal who| := by
      apply Finset.sum_congr rfl
      intro terminal _
      rw [← quittingAbsorbedMassLimit_reward_irrelevant first second]
      rw [← mul_sub, abs_mul,
        abs_of_nonneg (quittingAbsorbedMassLimit_nonneg first profile terminal)]
    _ ≤ ∑ terminal,
          quittingAbsorbedMassLimit first profile terminal * ε := by
      exact Finset.sum_le_sum fun terminal _ ↦
        mul_le_mul_of_nonneg_left (hclose terminal who)
          (quittingAbsorbedMassLimit_nonneg first profile terminal)
    _ = (1 - quittingLiveMassLimit first profile) * ε := by
      rw [← Finset.sum_mul]
      have hconservation :=
        quittingLiveMassLimit_add_sum_absorbedMassLimit first profile
      congr 1
      linarith
    _ ≤ ε := by
      have hlive : 0 ≤ quittingLiveMassLimit first profile :=
        quittingLiveMassLimit_nonneg first profile
      have habsorb : 0 ≤ 1 - quittingLiveMassLimit first profile := by
        rw [show 1 - quittingLiveMassLimit first profile =
          ∑ terminal, quittingAbsorbedMassLimit first profile terminal by
            linarith [quittingLiveMassLimit_add_sum_absorbedMassLimit
              first profile]]
        exact Finset.sum_nonneg fun terminal _ ↦
          quittingAbsorbedMassLimit_nonneg first profile terminal
      nlinarith

/-- Approximate terminal Nash is stable under a uniform perturbation of the
terminal table. -/
theorem IsεAsymptoticNash.of_reward_close
    (first second : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame first).BehaviorProfile)
    {ε η : ℝ} (hη : 0 ≤ η)
    (hclose : ∀ terminal player,
      |first terminal player - second terminal player| ≤ η)
    (hnash : (quittingGame first).IsεAsymptoticNash
      (quittingTerminalPayoff first) ε profile) :
    (quittingGame second).IsεAsymptoticNash
      (quittingTerminalPayoff second) (ε + 2 * η) profile := by
  intro who deviation
  have hbase := abs_quittingTerminalPayoff_sub_le_of_forall_abs_sub_le
    first second profile who hη hclose
  have hdeviation := abs_quittingTerminalPayoff_sub_le_of_forall_abs_sub_le
    first second (Function.update profile who deviation) who hη hclose
  have hnash' := hnash who deviation
  rcases (abs_le.mp hbase) with ⟨_hbaseLower, hbaseUpper⟩
  rcases (abs_le.mp hdeviation) with ⟨hdeviationLower, _hdeviationUpper⟩
  have hbaseRearranged :
      quittingTerminalPayoff first profile who ≤
        quittingTerminalPayoff second profile who + η :=
    by
      simpa [add_comm] using sub_le_iff_le_add.mp hbaseUpper
  calc
    quittingTerminalPayoff second
          (Function.update profile who deviation) who ≤
        quittingTerminalPayoff first
            (Function.update profile who deviation) who + η := by
      exact neg_le_sub_iff_le_add.mp hdeviationLower
    _ ≤ quittingTerminalPayoff first profile who + ε + η := by
      simpa [add_comm] using add_le_add_right hnash' η
    _ ≤ quittingTerminalPayoff second profile who + (ε + 2 * η) := by
      calc
        _ ≤ (quittingTerminalPayoff second profile who + η) + ε + η := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right (add_le_add_right hbaseRearranged ε) η
        _ = _ := by ring

omit [Fintype ι] [DecidableEq ι] in
/-- Tables satisfying the solo-exit assumptions are nonempty whenever there
is at least one player. -/
theorem soloExitRewardSet_nonempty [Nonempty ι] :
    soloExitRewardSet (ι := ι).Nonempty := by
  let reward : {S : Finset ι // S.Nonempty} → Payoff ι :=
    fun _ _ ↦ 1
  refine ⟨reward, ?_, ?_⟩
  · intro who
    rfl
  · intro terminal who _
    rfl

/-! ## A countable step selector -/

/-- A payoff table satisfying the hypotheses of the constant-table theorem. -/
abbrev SoloExitReward (ι : Type) [Fintype ι] :=
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι //
    reward ∈ soloExitRewardSet}

/-- The constant-one table witnesses that the solo-exit table space is
inhabited. -/
noncomputable instance soloExitRewardNonempty [Nonempty ι] :
    Nonempty (SoloExitReward ι) := by
  obtain ⟨reward, hreward⟩ := soloExitRewardSet_nonempty (ι := ι)
  exact ⟨⟨reward, hreward⟩⟩

/-- A fixed countable dense family of tables satisfying the solo-exit
hypotheses. -/
noncomputable def soloExitRewardCenter [Nonempty ι] (index : ℕ) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  (denseSeq (SoloExitReward ι) index).1

/-- Each center of the dense family has a fixed terminal approximate Nash
profile. -/
theorem exists_soloExitCenterTerminalNash [Nonempty ι]
    (index : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ profile : (quittingGame (soloExitRewardCenter (ι := ι) index)).BehaviorProfile,
      (quittingGame (soloExitRewardCenter (ι := ι) index)).IsεAsymptoticNash
        (quittingTerminalPayoff (soloExitRewardCenter (ι := ι) index))
        ε profile := by
  let center : SoloExitReward ι := denseSeq (SoloExitReward ι) index
  obtain ⟨roots, _period, _hperiod, _hperiodic, hnash⟩ :=
    exists_cyclic_subgamePerfectTerminalNash_of_soloExitPreference
      center.property.1 center.property.2 hε
  exact ⟨quittingRootSequenceProfile center.1 roots 0, hnash 0⟩

/-- The fixed terminal equilibrium chosen at a center table. -/
noncomputable def soloExitCenterTerminalProfile [Nonempty ι]
    (index : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (quittingGame (soloExitRewardCenter (ι := ι) index)).BehaviorProfile :=
  Classical.choose (exists_soloExitCenterTerminalNash index hε)

/-- The chosen center profile has the advertised terminal Nash error. -/
theorem soloExitCenterTerminalProfile_isNash [Nonempty ι]
    (index : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (quittingGame (soloExitRewardCenter (ι := ι) index)).IsεAsymptoticNash
      (quittingTerminalPayoff (soloExitRewardCenter (ι := ι) index)) ε
      (soloExitCenterTerminalProfile index ε hε) :=
  Classical.choose_spec (exists_soloExitCenterTerminalNash index hε)

/-- A center is admissible for a table when it lies within `radius`. -/
def soloExitTailCloseCandidate [Nonempty ι] (radius : ℝ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (index : ℕ) : Prop :=
  dist reward (soloExitRewardCenter (ι := ι) index) < radius

/-- The fallback candidate is center zero exactly when no close center exists.
This makes first-candidate selection total without changing it near the
solo-exit set. -/
def soloExitTailCandidate [Nonempty ι] (radius : ℝ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (index : ℕ) : Prop :=
  soloExitTailCloseCandidate radius reward index ∨
    (index = 0 ∧ ∀ candidate, ¬ soloExitTailCloseCandidate radius reward candidate)

omit [DecidableEq ι] in
/-- The fallback candidate predicate is inhabited for every table. -/
theorem exists_soloExitTailCandidate [Nonempty ι] (radius : ℝ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ index, soloExitTailCandidate radius reward index := by
  classical
  by_cases hclose : ∃ index, soloExitTailCloseCandidate radius reward index
  · obtain ⟨index, hindex⟩ := hclose
    exact ⟨index, Or.inl hindex⟩
  · exact ⟨0, Or.inr ⟨rfl, by simpa only [not_exists] using hclose⟩⟩

/-- The first close center, with center zero as fallback. -/
noncomputable def soloExitTailIndex [Nonempty ι] (radius : ℝ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℕ := by
  classical
  exact Nat.find (exists_soloExitTailCandidate radius reward)

omit [DecidableEq ι] in
/-- The first-center index is Borel measurable. -/
theorem measurable_soloExitTailIndex [Nonempty ι] (radius : ℝ) :
    Measurable (soloExitTailIndex (ι := ι) radius) := by
  classical
  let closeSet : ℕ → Set ({S : Finset ι // S.Nonempty} → Payoff ι) :=
    fun index ↦ {reward | soloExitTailCloseCandidate radius reward index}
  have hclose : ∀ index, MeasurableSet (closeSet index) := by
    intro index
    have hcontinuous : Continuous fun reward :
        ({S : Finset ι // S.Nonempty} → Payoff ι) ↦
        dist reward (soloExitRewardCenter (ι := ι) index) :=
      continuous_id.dist continuous_const
    exact (isOpen_lt hcontinuous continuous_const).measurableSet
  have hany : MeasurableSet {reward :
      ({S : Finset ι // S.Nonempty} → Payoff ι) | ∃ index : ℕ,
      soloExitTailCloseCandidate radius reward index} := by
    have heq : {reward :
        ({S : Finset ι // S.Nonempty} → Payoff ι) | ∃ index : ℕ,
          soloExitTailCloseCandidate radius reward index} =
        ⋃ index, closeSet index := by
      ext reward
      simp only [closeSet, Set.mem_setOf_eq, Set.mem_iUnion]
    rw [heq]
    exact MeasurableSet.iUnion hclose
  have hnone : MeasurableSet {reward :
      ({S : Finset ι // S.Nonempty} → Payoff ι) |
      ∀ candidate, ¬ soloExitTailCloseCandidate radius reward candidate} := by
    have hcomplement := hany.compl
    convert hcomplement using 1
    ext reward
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists]
  unfold soloExitTailIndex
  apply measurable_find (exists_soloExitTailCandidate (ι := ι) radius)
  intro index
  by_cases hindex : index = 0
  · subst index
    have hunion := (hclose 0).union hnone
    convert hunion using 1
    ext reward
    simp only [soloExitTailCandidate, closeSet, Set.mem_union,
      Set.mem_setOf_eq, true_and]
  · simpa only [soloExitTailCandidate, closeSet, hindex, false_and, or_false] using
      hclose index

/-- The countable-step terminal profile selected from a payoff table. -/
noncomputable def soloExitTailStepProfile [Nonempty ι]
    (ε : ℝ) (hε : 0 < ε)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingGame reward).BehaviorProfile :=
  soloExitCenterTerminalProfile (soloExitTailIndex (2 * ε) reward) ε hε

/-- Every coordinate of the selected step profile is Borel measurable in the
payoff table. -/
theorem measurable_soloExitTailStepProfile_apply [Nonempty ι]
    (ε : ℝ) (hε : 0 < ε) (who : ι) (time : ℕ)
    (history : (quittingGame
      (soloExitRewardCenter (ι := ι) 0)).Hist time) (action : Bool) :
    Measurable fun reward ↦
      soloExitTailStepProfile ε hε reward who time history action := by
  change Measurable fun reward :
      ({S : Finset ι // S.Nonempty} → Payoff ι) ↦
    soloExitCenterTerminalProfile
      (soloExitTailIndex (2 * ε) reward) ε hε who time history action
  exact (measurable_from_nat : Measurable fun index : ℕ ↦
    soloExitCenterTerminalProfile index ε hε who time history action).comp
      (measurable_soloExitTailIndex (2 * ε))

omit [DecidableEq ι] in
/-- Any table within `ε` of the solo-exit set has a selected center within
`2ε`. -/
theorem dist_soloExitTailStepCenter_lt [Nonempty ι]
    {ε : ℝ} (hε : 0 < ε)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnear : ∃ exact ∈ soloExitRewardSet,
      dist reward exact < ε) :
    dist reward (soloExitRewardCenter (ι := ι)
      (soloExitTailIndex (2 * ε) reward)) < 2 * ε := by
  classical
  obtain ⟨exact, hexact, hreward⟩ := hnear
  obtain ⟨index, hindex⟩ :=
    (denseRange_denseSeq (SoloExitReward ι)).exists_dist_lt
      ⟨exact, hexact⟩ hε
  have hclose : soloExitTailCloseCandidate (2 * ε) reward index := by
    unfold soloExitTailCloseCandidate soloExitRewardCenter
    calc
      dist reward (denseSeq (SoloExitReward ι) index).1 ≤
          dist reward exact +
            dist exact (denseSeq (SoloExitReward ι) index).1 :=
        dist_triangle _ _ _
      _ < ε + ε := add_lt_add hreward hindex
      _ = 2 * ε := by ring
  have hchosen := Nat.find_spec
    (exists_soloExitTailCandidate (ι := ι) (2 * ε) reward)
  rcases hchosen with hchosen | ⟨_, hnone⟩
  · exact hchosen
  · exact False.elim (hnone index hclose)

/-- Near the solo-exit set, the selected step profile is a terminal
`5ε`-Nash profile for the supplied table. -/
theorem soloExitTailStepProfile_isNash [Nonempty ι]
    {ε : ℝ} (hε : 0 < ε)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnear : ∃ exact ∈ soloExitRewardSet,
      dist reward exact < ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (5 * ε)
      (soloExitTailStepProfile ε hε reward) := by
  let index := soloExitTailIndex (2 * ε) reward
  let center := soloExitRewardCenter (ι := ι) index
  have hdist : dist reward center < 2 * ε :=
    dist_soloExitTailStepCenter_lt hε reward hnear
  have hclose : ∀ terminal player,
      |center terminal player - reward terminal player| ≤ 2 * ε := by
    intro terminal player
    have hterminal := (dist_pi_lt_iff (by positivity : 0 < 2 * ε)).mp hdist terminal
    have hplayer := (dist_pi_lt_iff (by positivity : 0 < 2 * ε)).mp
      hterminal player
    simpa only [Real.dist_eq, abs_sub_comm] using hplayer.le
  have hnash : (quittingGame center).IsεAsymptoticNash
      (quittingTerminalPayoff center) ε
      (soloExitCenterTerminalProfile index ε hε) :=
    soloExitCenterTerminalProfile_isNash index ε hε
  have hstable := IsεAsymptoticNash.of_reward_close
    center reward (soloExitCenterTerminalProfile index ε hε)
    (by positivity) hclose hnash
  have herror : ε + 2 * (2 * ε) ≤ 5 * ε := by
    ring_nf
    exact le_rfl
  simpa only [soloExitTailStepProfile, index, center] using hstable.mono herror

end GameTheory
