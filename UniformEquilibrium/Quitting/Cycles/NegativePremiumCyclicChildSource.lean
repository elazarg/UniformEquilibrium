import UniformEquilibrium.Quitting.Cycles.NegativePremiumCyclicChildEndpoints
import UniformEquilibrium.Quitting.Root.PlayerwiseAffineReward

/-! # Actual negative-premium sources with signed own rewards

The scalar rates are produced from the raw table, including the zero-pivot
boundary branch. Playerwise affine transport is used only for finite roots;
actual terminal and behavioral-deviation claims use opponent-cycle contraction.
-/

noncomputable section

namespace GameTheory.NegativePremiumCyclicChild

open _root_.Math.CyclicChildNegativePremium

structure Certificate (reward : Reward) where
  rates : Rates
  value : Fin 3 → Payoff Player
  policy : ∀ phase, value phase = quittingRootSuccessorPayoff reward
    (value (finRotate 3 phase)) (cycle rates phase)
  rootNash : ∀ phase, IsεQuittingRootNash reward
    (value (finRotate 3 phase)) 0 (cycle rates phase)

theorem RawTable.exists_certificate {loss : ℝ} {reward : Reward}
    (table : RawTable loss reward) : ∃ source : Certificate reward,
    (loss < 15 / 26 ∧ source.value = lowValue loss source.rates ∧
      source.rates.p ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
      source.rates.y ∈ Set.Ioo (2 / 5 : ℝ) (2 / 3)) ∨
    (15 / 26 ≤ loss ∧ source.rates = highRates ∧ source.value = highValue) := by
  by_cases hloss : loss < 15 / 26
  · obtain ⟨y, hy, hp, _, hz, hw, hchild, hpivot⟩ :=
      exists_low_rates ⟨table.loss_mem.1, hloss⟩
    let rates : Rates := {
      p := selected loss y
      y := y
      z := second (selected loss y) y
      w := third (selected loss y) y
      p_mem := ⟨hp.1.le, by linarith [hp.2]⟩
      y_mem := ⟨by linarith [hy.1], by linarith [hy.2]⟩
      z_mem := hz
      w_mem := hw }
    have hcert := low_certificate loss reward table rates hp.2 hy.1 rfl rfl hchild hpivot
    refine ⟨⟨rates, lowValue loss rates, hcert.1, hcert.2⟩, Or.inl ?_⟩
    exact ⟨hloss, rfl, hp, hy⟩
  · have hcert := high_certificate loss reward table (le_of_not_gt hloss)
    exact ⟨⟨highRates, highValue, hcert.1, hcert.2⟩,
      Or.inr ⟨le_of_not_gt hloss, rfl, rfl⟩⟩

namespace Certificate

def profile {reward : Reward} (source : Certificate reward) :
    (quittingGame reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward (cycle source.rates) 0

theorem terminal_eq {reward : Reward} (source : Certificate reward) :
    quittingTerminalPayoff reward source.profile = source.value 0 := by
  rw [profile, quittingTerminalPayoff_cyclicBehaviorProfile]
  exact (congrFun (eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff
    reward (cycle source.rates) source.value source.policy (cycle_contracts source.rates)) 0).symm

theorem terminalNash {reward : Reward} (source : Certificate reward) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 source.profile :=
  isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate reward
    (cycle source.rates) source.value 0 source.policy source.rootNash
    (cycle_contracts source.rates)

theorem uniformPayoff {reward : Reward} (source : Certificate reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (source.value 0) := by
  rw [← source.terminal_eq]
  exact quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    reward source.profile source.terminalNash

theorem fixedProfileWitnesses {reward : Reward} (source : Certificate reward) :
    ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
      ∀ horizon, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon accuracy source.profile ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon source.profile who -
            source.value 0 who| ≤ accuracy := by
  rw [← source.terminal_eq]
  exact quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact
    reward source.profile source.terminalNash

def affine {reward : Reward} (source : Certificate reward) (scale shift : Payoff Player)
    (hscale : ∀ who, 0 < scale who) :
    Certificate (quittingPlayerwiseAffineReward reward scale shift) where
  rates := source.rates
  value := fun phase => quittingPlayerwiseAffinePayoff scale shift (source.value phase)
  policy := by
    intro phase
    funext who
    rw [quittingRootSuccessorPayoff_playerwiseAffine, ← source.policy]
    rfl
  rootNash := fun phase => isZeroQuittingRootNash_playerwiseAffine
    reward scale shift (source.value (finRotate 3 phase)) (cycle source.rates phase)
      hscale (source.rootNash phase)

private theorem cast_rates {first second : Reward} (heq : first = second)
    (source : Certificate first) : (heq ▸ source).rates = source.rates := by
  cases heq
  rfl

private theorem cast_value {first second : Reward} (heq : first = second)
    (source : Certificate first) : (heq ▸ source).value = source.value := by
  cases heq
  rfl

end Certificate

def normalizedReward (own scale : Payoff Player) (reward : Reward) : Reward :=
  fun coalition who => 1 + (reward coalition who - own who) / scale who

/-- Signed own rewards and positive row scales, with only literal normalized
rows/caps supplied. No source hazards or value vectors are input fields. -/
structure SignedRawTable (loss : ℝ) (own scale : Payoff Player) (reward : Reward) : Prop where
  scale_pos : ∀ who, 0 < scale who
  normalized : RawTable loss (normalizedReward own scale reward)

theorem normalized_affine_eq (own scale : Payoff Player) (reward : Reward)
    (hscale : ∀ who, 0 < scale who) :
    quittingPlayerwiseAffineReward (normalizedReward own scale reward) scale
      (fun who => own who - scale who) = reward := by
  funext coalition who
  unfold quittingPlayerwiseAffineReward normalizedReward
  field_simp [(hscale who).ne']
  ring

/-- One internally constructed cyclic profile caps all behavioral terminal
deviations and witnesses one fixed target at every positive accuracy. -/
theorem SignedRawTable.exists_terminalNash_fixed_target {loss : ℝ}
    {own scale : Payoff Player} {reward : Reward} (table : SignedRawTable loss own scale reward) :
    ∃ canonical : Certificate (normalizedReward own scale reward),
      let profile := quittingCyclicBehaviorProfile reward (cycle canonical.rates) 0
      let target := fun who => own who + scale who * (canonical.value 0 who - 1)
      quittingTerminalPayoff reward profile = target ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 profile ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none target ∧
      ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
        ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon accuracy profile ∧
            ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon profile who -
              target who| ≤ accuracy := by
  obtain ⟨canonical, _⟩ := table.normalized.exists_certificate
  let affineSource := canonical.affine scale (fun who => own who - scale who) table.scale_pos
  have heq := normalized_affine_eq own scale reward table.scale_pos
  let source : Certificate reward := heq ▸ affineSource
  have hrates : source.rates = canonical.rates := by
    exact Certificate.cast_rates heq affineSource
  have hvalue : source.value 0 =
      fun who => own who + scale who * (canonical.value 0 who - 1) := by
    rw [show source.value = affineSource.value from Certificate.cast_value heq affineSource]
    funext who
    change scale who * canonical.value 0 who + (own who - scale who) = _
    ring
  refine ⟨canonical, ?_⟩
  change quittingTerminalPayoff reward
      (quittingCyclicBehaviorProfile reward (cycle canonical.rates) 0) = _ ∧ _
  have hprofile : source.profile =
      quittingCyclicBehaviorProfile reward (cycle canonical.rates) 0 := by
    rw [Certificate.profile, hrates]
  rw [← hprofile, ← hvalue]
  exact ⟨source.terminal_eq, source.terminalNash, source.uniformPayoff,
    source.fixedProfileWitnesses⟩

end GameTheory.NegativePremiumCyclicChild
