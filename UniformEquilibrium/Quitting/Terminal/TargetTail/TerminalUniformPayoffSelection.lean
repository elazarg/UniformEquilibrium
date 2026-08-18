/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformization

/-!
# Selecting a fixed uniform payoff from terminal equilibria

The profile-level terminal-to-uniform theorem leaves one existence-level
quantifier: terminal approximate equilibria at successively smaller errors may
have different payoff vectors.  Their terminal payoffs lie in a common compact
finite-dimensional cube.  A convergent subsequence, the strict-error
terminal-to-uniform theorem, and fixed-profile Cesaro convergence select one
uniform equilibrium payoff.

Consequently, for finite quitting games, existence of terminal approximate
equilibria at every positive accuracy is equivalent to existence of a uniform
equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Terminal payoffs of arbitrary profiles lie in the cube determined by the
canonical finite reward bound. -/
theorem quittingTerminalPayoff_mem_rewardCube
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile ∈
      Set.Icc (fun _ => -quittingRewardBound reward)
        (fun _ => quittingRewardBound reward) := by
  constructor <;> intro who
  · exact neg_le_of_abs_le (abs_quittingTerminalPayoff_le reward profile who
      (abs_reward_le_quittingRewardBound reward))
  · exact le_of_abs_le (abs_quittingTerminalPayoff_le reward profile who
      (abs_reward_le_quittingRewardBound reward))

omit [DecidableEq ι] in
/-- Any limit of quitting terminal-payoff vectors lies in the canonical reward
cube.  The convergence is in the finite product topology on `Payoff ι`. -/
theorem quittingTerminalPayoff_limit_mem_rewardCube
    {index : Type*} {filter : Filter index} [NeBot filter]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : index → (quittingGame reward).BehaviorProfile)
    (target : Payoff ι)
    (htarget : Tendsto
      (fun n ↦ quittingTerminalPayoff reward (profiles n))
      filter (nhds target)) :
    target ∈ Set.Icc (fun _ ↦ -quittingRewardBound reward)
      (fun _ ↦ quittingRewardBound reward) := by
  exact isClosed_Icc.mem_of_tendsto htarget
    (Filter.Eventually.of_forall fun n ↦
      quittingTerminalPayoff_mem_rewardCube reward (profiles n))

/-- Every uniform-equilibrium payoff of a finite quitting game lies in the exact canonical reward
cube.  Arbitrarily accurate on-path delivery closes the finite-average payoff bound without any
extra unit of slack. -/
theorem quittingGame_isUniformEquilibriumPayoff_mem_rewardCube
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (hpayoff : (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    target ∈ Set.Icc (fun _ ↦ -quittingRewardBound reward)
      (fun _ ↦ quittingRewardBound reward) := by
  have htargetBound : ∀ who, |target who| ≤ quittingRewardBound reward := by
    intro who
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨profile, threshold, hprofile⟩ := hpayoff ε hε
    have hdelivery := (hprofile threshold le_rfl).2 who
    have havg :
        |(quittingGame reward).finiteAveragePayoff none threshold profile who| ≤
          quittingRewardBound reward := by
      apply (quittingGame reward).abs_finiteAveragePayoff_le
        (quittingRewardBound_nonneg reward) (fun state _action ↦ ?_)
        none threshold profile
      cases state with
      | none =>
          change |(0 : ℝ)| ≤ quittingRewardBound reward
          simpa using quittingRewardBound_nonneg reward
      | some terminal =>
          change |reward terminal who| ≤ quittingRewardBound reward
          exact abs_reward_le_quittingRewardBound reward terminal who
    calc
      |target who| =
          |(target who -
              (quittingGame reward).finiteAveragePayoff none threshold profile who) +
            (quittingGame reward).finiteAveragePayoff none threshold profile who| := by
              ring_nf
      _ ≤ |target who -
              (quittingGame reward).finiteAveragePayoff none threshold profile who| +
            |(quittingGame reward).finiteAveragePayoff none threshold profile who| :=
          abs_add_le _ _
      _ = |(quittingGame reward).finiteAveragePayoff none threshold profile who -
              target who| +
            |(quittingGame reward).finiteAveragePayoff none threshold profile who| := by
          rw [abs_sub_comm]
      _ ≤ ε + quittingRewardBound reward := add_le_add hdelivery havg
      _ = quittingRewardBound reward + ε := by ring
  exact ⟨fun who ↦ neg_le_of_abs_le (htargetBound who),
    fun who ↦ le_of_abs_le (htargetBound who)⟩

/-- Terminal approximate Nash profiles which approach one fixed target at
every positive accuracy make that target a uniform-equilibrium payoff.  This
is the shared fixed-target acceptance compiler: the same accuracy bounds both
terminal Nash error and coordinatewise terminal-payoff distance. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (haccept : ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile ∧
        ∀ who,
          |quittingTerminalPayoff reward profile who - target who| ≤ ε) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨profile, hterminalNash, htarget⟩ := haccept (ε / 2) hhalf
  have huniform : (quittingGame reward).IsUniformεEquilibrium
      none ε profile :=
    quittingGame_isUniformεEquilibrium_of_terminalNash
      reward profile (by linarith) hterminalNash
  obtain ⟨nashThreshold, hnashThreshold⟩ := huniform
  have heventuallyDelivery : ∀ᶠ horizon : ℕ in atTop, ∀ who,
      |(quittingGame reward).finiteAveragePayoff none horizon profile who -
        quittingTerminalPayoff reward profile who| < ε / 2 := by
    apply Filter.eventually_all.mpr
    intro who
    have hball :=
      (tendsto_finiteAveragePayoff_quittingGame reward profile who).eventually
        (Metric.ball_mem_nhds
          (quittingTerminalPayoff reward profile who) hhalf)
    filter_upwards [hball] with horizon hhorizon
    simpa only [Metric.mem_ball, Real.dist_eq] using hhorizon
  obtain ⟨deliveryThreshold, hdeliveryThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨profile, max nashThreshold deliveryThreshold,
    fun horizon hhorizon ↦ ?_⟩
  constructor
  · exact hnashThreshold horizon
      (le_trans (Nat.le_max_left _ _) hhorizon)
  · intro who
    have hdelivery := hdeliveryThreshold horizon
      (le_trans (Nat.le_max_right _ _) hhorizon) who
    calc
      |(quittingGame reward).finiteAveragePayoff none horizon profile who -
          target who| =
        |((quittingGame reward).finiteAveragePayoff none horizon profile who -
            quittingTerminalPayoff reward profile who) +
          (quittingTerminalPayoff reward profile who - target who)| := by
            ring_nf
      _ ≤ |(quittingGame reward).finiteAveragePayoff none horizon profile who -
            quittingTerminalPayoff reward profile who| +
          |quittingTerminalPayoff reward profile who - target who| :=
        abs_add_le _ _
      _ ≤ ε := by
        linarith [htarget who]

/-- An exact terminal Nash profile's own terminal payoff is a
uniform-equilibrium payoff. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 profile) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingTerminalPayoff reward profile) := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance
  intro ε hε
  exact ⟨profile, hnash.mono hε.le, fun who ↦ by simpa using hε.le⟩

/-- Terminal approximate equilibria whose errors tend to zero and whose
terminal payoff vectors tend to one specified target make that target a
uniform-equilibrium payoff.  The indexing filter is arbitrary.  Errors may
approach zero from either side; only their eventual strict upper bound at each
positive accuracy is used, and terminal Nash is required only frequently.

Payoff convergence is convergence in the finite product topology on
`Payoff ι = ι → ℝ`. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
    {index : Type*} {filter : Filter index}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (error : index → ℝ)
    (profiles : index → (quittingGame reward).BehaviorProfile)
    (herror : Tendsto error filter (nhds 0))
    (hnash : ∃ᶠ n in filter,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (error n) (profiles n))
    (htarget : Tendsto
      (fun n ↦ quittingTerminalPayoff reward (profiles n))
      filter (nhds target)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance
  intro ε hε
  have heventuallyError : ∀ᶠ n in filter, error n < ε :=
    (tendsto_order.1 herror).2 ε hε
  have heventuallyPayoff : ∀ᶠ n in filter, ∀ who,
      |quittingTerminalPayoff reward (profiles n) who - target who| < ε := by
    apply Filter.eventually_all.mpr
    intro who
    have hcoordinate : Tendsto
        (fun n ↦ quittingTerminalPayoff reward (profiles n) who)
        filter (nhds (target who)) :=
      (continuous_apply who).tendsto target |>.comp htarget
    have hball := hcoordinate.eventually
      (Metric.ball_mem_nhds (target who) hε)
    filter_upwards [hball] with n hn
    simpa only [Metric.mem_ball, Real.dist_eq] using hn
  obtain ⟨selectedIndex, hselectedNash, hselectedError, hselectedPayoff⟩ :=
    (hnash.and_eventually
      (heventuallyError.and heventuallyPayoff)).exists
  exact ⟨profiles selectedIndex, hselectedNash.mono hselectedError.le,
    fun who ↦ (hselectedPayoff who).le⟩

/-- Terminal approximate equilibria at every positive accuracy select one
fixed uniform-equilibrium payoff inside the canonical reward cube. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_mem_rewardCube_of_terminalNash_all_errors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hterminal : ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile) :
    ∃ payoff : Payoff ι,
      payoff ∈ Set.Icc (fun _ => -quittingRewardBound reward)
          (fun _ => quittingRewardBound reward) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let approximationError : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have herrorPositive : ∀ n, 0 < approximationError n := by
    intro n
    dsimp [approximationError]
    positivity
  have hexists : ∀ n, ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (approximationError n) profile :=
    fun n => hterminal (approximationError n) (herrorPositive n)
  choose profiles hprofiles using hexists
  let terminalPayoffs : ℕ → Payoff ι := fun n =>
    quittingTerminalPayoff reward (profiles n)
  have hmem : ∀ n, terminalPayoffs n ∈
      Set.Icc (fun _ => -quittingRewardBound reward)
        (fun _ => quittingRewardBound reward) := by
    intro n
    exact quittingTerminalPayoff_mem_rewardCube reward (profiles n)
  obtain ⟨payoff, hpayoffMem, subsequence, hsubsequence, hpayoffLimit⟩ :=
    (isCompact_Icc : IsCompact
      (Set.Icc (fun _ : ι => -quittingRewardBound reward)
        (fun _ : ι => quittingRewardBound reward))).tendsto_subseq hmem
  have herrorLimit : Tendsto approximationError atTop (nhds 0) := by
    simpa [approximationError] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨payoff, hpayoffMem,
    quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
      (filter := atTop)
      reward payoff (approximationError ∘ subsequence)
        (profiles ∘ subsequence) ?_ ?_ ?_⟩
  · exact herrorLimit.comp hsubsequence.tendsto_atTop
  · exact Filter.Frequently.of_forall fun n ↦ hprofiles (subsequence n)
  · change Tendsto (terminalPayoffs ∘ subsequence) atTop (nhds payoff)
    exact hpayoffLimit

/-- Terminal approximate equilibria at every positive accuracy select one
fixed uniform equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hterminal : ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨payoff, _, huniform⟩ :=
    quittingGame_exists_uniformEquilibriumPayoff_mem_rewardCube_of_terminalNash_all_errors
      reward hterminal
  exact ⟨payoff, huniform⟩

/-- A uniform-equilibrium payoff supplies a terminal approximate equilibrium
at every positive error. -/
theorem quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (hpayoff : (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨profile, threshold, hprofile⟩ := hpayoff (ε / 2) hhalf
  have huniform : (quittingGame reward).IsUniformεEquilibrium
      none (ε / 2) profile :=
    ⟨threshold, fun horizon hhorizon ↦ (hprofile horizon hhorizon).1⟩
  have hterminal : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (ε / 2) profile :=
    (quittingGame reward).isεAsymptoticNash_of_isUniformεEquilibrium
      none (quittingTerminalPayoff reward) huniform
      (fun selectedProfile who ↦
        tendsto_finiteAveragePayoff_quittingGame
          reward selectedProfile who)
  exact ⟨profile, hterminal.mono (by linarith)⟩

/-- For finite quitting games, terminal approximate existence at every
positive error is equivalent to existence of a uniform-equilibrium payoff in
the canonical reward cube. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_mem_rewardCube_iff_terminalNash_all_errors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
      payoff ∈ Set.Icc (fun _ ↦ -quittingRewardBound reward)
          (fun _ ↦ quittingRewardBound reward) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ profile : (quittingGame reward).BehaviorProfile,
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) ε profile := by
  constructor
  · rintro ⟨payoff, _, hpayoff⟩
    exact quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff
      reward payoff hpayoff
  · exact
      quittingGame_exists_uniformEquilibriumPayoff_mem_rewardCube_of_terminalNash_all_errors
        reward

/-- Target-free form of terminal approximate existence versus uniform-equilibrium-payoff
existence.  Exact target boundedness identifies its left side with the canonical-cube form. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ profile : (quittingGame reward).BehaviorProfile,
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) ε profile := by
  refine Iff.trans ?_
    (quittingGame_exists_uniformEquilibriumPayoff_mem_rewardCube_iff_terminalNash_all_errors
      reward)
  constructor
  · rintro ⟨payoff, hpayoff⟩
    exact ⟨payoff,
      quittingGame_isUniformEquilibriumPayoff_mem_rewardCube reward payoff hpayoff, hpayoff⟩
  · rintro ⟨payoff, _, hpayoff⟩
    exact ⟨payoff, hpayoff⟩

/-- Uniform approximate equilibria at every positive error select one fixed
uniform-equilibrium payoff.

The hypothesis lets the profile and its payoff vector move with the error; the
conclusion fixes one target before the error is chosen.  Cesaro convergence to
the terminal payoff turns each uniform approximate equilibrium into a terminal
approximate equilibrium, and terminal selection then supplies the fixed
target. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_uniformεEquilibrium_all_errors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (huniform : ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsUniformεEquilibrium none ε profile) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  refine quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
    reward fun ε hε ↦ ?_
  obtain ⟨profile, hprofile⟩ := huniform ε hε
  exact ⟨profile,
    (quittingGame reward).isεAsymptoticNash_of_isUniformεEquilibrium
      none (quittingTerminalPayoff reward) hprofile
      (fun selectedProfile who ↦
        tendsto_finiteAveragePayoff_quittingGame reward selectedProfile who)⟩

/-- **The quitting notion-alignment equivalence.**  For finite quitting games,
having a uniform `ε`-equilibrium at every positive `ε`—with the profile and its
payoff free to move with `ε`—is equivalent to having one fixed
uniform-equilibrium payoff.

The two sides are not equivalent for general stochastic games; the quitting
Cesaro-convergence bridge and the compact terminal-payoff cube are what close
the gap here. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_iff_uniformεEquilibrium_all_errors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ profile : (quittingGame reward).BehaviorProfile,
          (quittingGame reward).IsUniformεEquilibrium none ε profile := by
  constructor
  · rintro ⟨payoff, hpayoff⟩ ε hε
    obtain ⟨profile, threshold, hprofile⟩ := hpayoff ε hε
    exact ⟨profile, threshold, fun horizon hhorizon ↦ (hprofile horizon hhorizon).1⟩
  · exact quittingGame_exists_uniformEquilibriumPayoff_of_uniformεEquilibrium_all_errors
      reward

end GameTheory
