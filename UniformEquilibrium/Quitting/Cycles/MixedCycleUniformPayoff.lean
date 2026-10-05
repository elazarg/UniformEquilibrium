import UniformEquilibrium.Quitting.Cycles.MixedCycleSourceCertificate
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-! # Fixed-target behavioral compilation of mixed finite cycles

The actual period is `L * m`: each retained root occurs once and is padded
with quiet rows. Period contraction is preserved exactly, including retained
sure hazards. The coarse source and selected initial target are fixed before
accuracy is requested; only the subdivision scale and behavioral profile vary.
This compiler does not produce the packet-specific coarse coefficients.
-/

noncomputable section

namespace GameTheory.MixedCycleSoloMesh

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] {L m : ℕ}

theorem collision_surplus_le_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner other : ι) :
    max (quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward other other) 0 ≤ 2 * quittingRewardBound reward := by
  have hpair := (abs_le.mp (abs_reward_le_quittingRewardBound reward
    ⟨{owner, other}, by simp⟩ other)).2
  have hsolo := (abs_le.mp (abs_reward_le_quittingRewardBound reward
    (quittingSingletonTerminal other) other)).1
  have hbound := quittingRewardBound_nonneg reward
  change max (reward ⟨{owner, other}, by simp⟩ other -
    reward (quittingSingletonTerminal other) other) 0 ≤ _
  apply max_le <;> linarith

theorem coarse_continueMass_of_solo
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {solo : Fin L → Bool} {owner : Fin L → ι} {mass : Fin L → ℝ}
    {root : Fin L → ι → PMF Bool} {value : Fin L → Payoff ι}
    (source : SourceCertificate reward solo owner mass root value)
    (block : Fin L) (who : ι) (hsolo : solo block = true) :
    quittingStationaryFixedOpponentsContinueMass (root block) who =
      if who = owner block then 1 else 1 - soloMass solo mass block := by
  rw [source.solo_root block hsolo]
  by_cases howner : who = owner block
  · subst who
    simp
  · rw [ite_eq_right howner,
      quittingStationaryFixedOpponentsContinueMass_solo_other howner]
    simp [soloMass, hsolo]

/-- Exact preservation of every player's whole-period opponent survival. -/
theorem prod_continueMass_eq_coarse
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {solo : Fin L → Bool} {owner : Fin L → ι} {mass : Fin L → ℝ}
    {root : Fin L → ι → PMF Bool} {value : Fin L → Payoff ι}
    (source : SourceCertificate reward solo owner mass root value)
    (hm : 0 < m) (who : ι) :
    (∏ phase : Fin (L * m), quittingStationaryFixedOpponentsContinueMass
      (refinedRoot solo owner (soloMass solo mass) root m source.soloMass_nonneg
        source.soloMass_lt_one phase) who) =
      ∏ block : Fin L, quittingStationaryFixedOpponentsContinueMass (root block) who := by
  let factor := fun phase : Fin (L * m) =>
    quittingStationaryFixedOpponentsContinueMass
      (refinedRoot solo owner (soloMass solo mass) root m source.soloMass_nonneg
        source.soloMass_lt_one phase) who
  rw [← finProdFinEquiv.prod_comp factor, Fintype.prod_prod_type]
  apply Fintype.prod_congr
  intro block
  change (∏ offset : Fin m, quittingStationaryFixedOpponentsContinueMass
    (refinedRoot solo owner (soloMass solo mass) root m source.soloMass_nonneg
      source.soloMass_lt_one (quittingSingletonMeshPhase block offset)) who) = _
  by_cases hsolo : solo block = true
  · rw [prod_continueMass_block_of_solo solo owner (soloMass solo mass) root hm
      source.soloMass_nonneg source.soloMass_lt_one block who hsolo]
    exact (coarse_continueMass_of_solo source block who hsolo).symm
  · exact prod_continueMass_block_of_retained solo owner (soloMass solo mass) root hm
      source.soloMass_nonneg source.soloMass_lt_one block who hsolo

/-- The concrete fixed-scale cyclic behavioral profile is terminal approximate
Nash and has exactly the selected coarse target, not just a nearby target. -/
theorem isTerminalNash_and_hasValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (solo : Fin L → Bool) (owner : Fin L → ι) (mass : Fin L → ℝ)
    (root : Fin L → ι → PMF Bool) (value : Fin L → Payoff ι)
    (source : SourceCertificate reward solo owner mass root value)
    (initial : Fin L) (hm : 0 < m) {error : ℝ} (herror : 0 ≤ error)
    (hmesh : ∀ block, 2 * quittingRewardBound reward *
      quittingMeshHazard (soloMass solo mass block) m ≤ error) :
    let cycle := refinedRoot solo owner (soloMass solo mass) root m
      source.soloMass_nonneg source.soloMass_lt_one
    let phase := quittingSingletonMeshInitialPhase initial m hm
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) error
        (quittingCyclicBehaviorProfile reward cycle phase) ∧
      quittingTerminalPayoff reward (quittingCyclicBehaviorProfile reward cycle phase) =
        value initial := by
  let cycle := refinedRoot solo owner (soloMass solo mass) root m
    source.soloMass_nonneg source.soloMass_lt_one
  let refined := refinedValue reward solo owner (soloMass solo mass) value m
  let phase := quittingSingletonMeshInitialPhase initial m hm
  have hcert : ∀ phase, refined phase = quittingRootSuccessorPayoff reward
      (refined (finRotate (L * m) phase)) (cycle phase) ∧
      (∀ who, quittingRootContinuePayoff reward
        (refined (finRotate (L * m) phase)) (cycle phase) who = refined phase who) ∧
      ∀ who, quittingRootQuitPayoff reward
        (refined (finRotate (L * m) phase)) (cycle phase) who ≤ refined phase who + error := by
    intro phase
    rw [← quittingSingletonMeshPhase_block_offset phase]
    exact refinedPhase_certificate reward solo owner (soloMass solo mass) root value hm
      source.soloMass_nonneg source.soloMass_lt_one
      (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)) herror
      source.solo_arc source.solo_active source.singleton_floor
      (fun block other _ => collision_surplus_le_rewardBound reward (owner block) other)
      hmesh (fun block _ => source.policy block)
      (fun block _ => source.continue_eq block) source.retained_quit _ _
  have hcontracts : ∀ who,
      (∏ phase, quittingStationaryFixedOpponentsContinueMass (cycle phase) who) < 1 := by
    intro who
    rw [prod_continueMass_eq_coarse source hm who]
    exact source.contracts who
  have hcontinue : ∀ phase who,
      quittingStationaryFixedOpponentsContinueReward reward (cycle phase) who +
        quittingStationaryFixedOpponentsContinueMass (cycle phase) who *
          refined (finRotate (L * m) phase) who = refined phase who := by
    intro phase who
    have h := (hcert phase).2.1 who
    rw [quittingRootContinuePayoff_eq_fixedOpponents reward (fun _ => cycle phase)
      who (refined (finRotate (L * m) phase)) 0] at h
    exact h
  have hquit : ∀ phase who,
      quittingStationaryFixedOpponentsQuitValue reward (cycle phase) who ≤
        refined phase who + error := by
    intro phase who
    have h := (hcert phase).2.2 who
    rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward (fun _ => cycle phase)
      who (refined (finRotate (L * m) phase)) 0] at h
    exact h
  refine ⟨isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue
    reward cycle refined phase herror (quittingRewardBound_nonneg reward)
    (abs_reward_le_quittingRewardBound reward) (fun phase => (hcert phase).1)
    hquit hcontinue hcontracts, ?_⟩
  have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff reward cycle
    refined (fun phase => (hcert phase).1) hcontracts
  rw [quittingTerminalPayoff_cyclicBehaviorProfile, ← hvalue]
  exact refinedValue_initial reward solo owner (soloMass solo mass) value initial hm

/-- Literal mixed coarse data yields a fixed uniform-equilibrium target.
Only solo blocks are refined; retained joint hazards need not be proper. -/
theorem isUniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (solo : Fin L → Bool) (owner : Fin L → ι) (mass : Fin L → ℝ)
    (root : Fin L → ι → PMF Bool) (value : Fin L → Payoff ι)
    (source : SourceCertificate reward solo owner mass root value) (initial : Fin L) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (value initial) := by
  classical
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance
  intro error herror
  let intensity := fun block => quittingMeshIntensity (soloMass solo mass block)
  let aStar := ∑ block : Fin L, intensity block
  have hintensity0 (block : Fin L) : 0 ≤ intensity block :=
    quittingMeshIntensity_nonneg (source.soloMass_nonneg block)
      (source.soloMass_lt_one block).le
  have haStar0 : 0 ≤ aStar := Finset.sum_nonneg (fun block _ => hintensity0 block)
  have ha (block : Fin L) : intensity block ≤ aStar :=
    Finset.single_le_sum (fun other _ => hintensity0 other) (Finset.mem_univ block)
  let D := 2 * quittingRewardBound reward
  have hD : 0 ≤ D := mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)
  obtain ⟨m, hmLarge⟩ := exists_nat_gt (D * aStar / error)
  have hmReal : 0 < (m : ℝ) :=
    (div_nonneg (mul_nonneg hD haStar0) herror.le).trans_lt hmLarge
  have hm : 0 < m := by exact_mod_cast hmReal
  have hsmall : D * aStar / (m : ℝ) ≤ error := by
    apply le_of_lt
    rw [div_lt_iff₀ hmReal]
    have h := (div_lt_iff₀ herror).mp hmLarge
    nlinarith
  have hmesh (block : Fin L) : D * quittingMeshHazard (soloMass solo mass block) m ≤
      error := by
    have hh := quittingMeshHazard_le_intensityBound_div (m := m)
      (soloMass solo mass) source.soloMass_lt_one ha block
    calc
      D * quittingMeshHazard (soloMass solo mass block) m ≤
          D * (aStar / (m : ℝ)) := mul_le_mul_of_nonneg_left hh hD
      _ = D * aStar / (m : ℝ) := by ring
      _ ≤ error := hsmall
  obtain ⟨hnash, hvalue⟩ := isTerminalNash_and_hasValue reward solo owner mass root value
    source initial hm herror.le hmesh
  refine ⟨_, hnash, ?_⟩
  intro who
  rw [hvalue]
  simpa using herror.le

end GameTheory.MixedCycleSoloMesh
