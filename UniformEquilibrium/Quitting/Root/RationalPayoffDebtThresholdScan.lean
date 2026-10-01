import UniformEquilibrium.Quitting.Root.RationalFiniteSourceCapThresholdScan
import UniformEquilibrium.Quitting.Root.TerminalSemanticSoloPayoffThreshold

/-! # Executable first actual payoff/debt hit

Only the rational iterate and its actual payoff/debt predicate are searched.
The real logarithm certifies termination and does not enter runtime data.
-/

namespace GameTheory

variable {players : ℕ}

/-- Rational small-total-debt or outsider-payoff hit. This is not a cap scan. -/
def rationalSoloPayoffDebtThresholdHit
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard working : ℚ) (source : RationalQuittingSemanticPair players)
    (steps : ℕ) : Prop :=
  rationalQuittingSemanticDebtSum
      (rationalQuittingSoloSemanticIterate reward owner hazard source steps) < working ∨
    ∃ who, who ≠ owner ∧
      (rationalQuittingSoloSemanticIterate reward owner hazard source steps).1 who ≤
        reward (quittingSingletonTerminal who) who + working / 2

instance rationalSoloPayoffDebtThresholdHit_decidable
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard working : ℚ) (source : RationalQuittingSemanticPair players) (steps : ℕ) :
    Decidable (rationalSoloPayoffDebtThresholdHit reward owner hazard working source steps) := by
  unfold rationalSoloPayoffDebtThresholdHit
  infer_instance

/-- Exact agreement of the computed predicate with the actual semantic hit. -/
theorem rationalSoloPayoffDebtThresholdHit_iff_real
    (reward : RationalQuittingReward players) (owner : Fin players)
    {hazard : ℚ} (hhazard : hazard ∈ Set.Icc (0 : ℚ) 1)
    (working : ℚ) (source : RationalQuittingSemanticPair players) (steps : ℕ) :
    rationalSoloPayoffDebtThresholdHit reward owner hazard working source steps ↔
      quittingSoloPayoffDebtThresholdHit (rationalQuittingRewardToReal reward)
        source.toReal owner
        (quittingHazardCoin (hazard : ℝ)
          (by exact_mod_cast hhazard.1) (by exact_mod_cast hhazard.2))
        (working : ℝ) steps := by
  unfold rationalSoloPayoffDebtThresholdHit quittingSoloPayoffDebtThresholdHit
  rw [quittingSoloSemanticIterate_rational_eq_cast reward owner hhazard source steps,
    quittingTerminalSemanticDebtSum_rational_eq_cast]
  simp only [RationalQuittingSemanticPair.toReal, rationalQuittingRewardToReal]
  constructor
  · rintro (hdebt | ⟨who, hne, hpayoff⟩)
    · left
      exact_mod_cast hdebt
    · right
      exact ⟨who, hne, by exact_mod_cast hpayoff⟩
  · rintro (hdebt | ⟨who, hne, hpayoff⟩)
    · left
      exact_mod_cast hdebt
    · right
      exact ⟨who, hne, by exact_mod_cast hpayoff⟩

/-- Every literal rational finite source is an actual semantic carrier point. -/
theorem rationalQuittingFiniteWordSemanticPair_mem_carrier
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) :
    (rationalQuittingFiniteWordSemanticPair reward roots).toReal ∈
      quittingTerminalSemanticCarrier (rationalQuittingRewardToReal reward) := by
  let profile := quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
    (roots.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
  have hpair : quittingTerminalSemanticPair (rationalQuittingRewardToReal reward) profile =
      (rationalQuittingFiniteWordSemanticPair reward roots).toReal := by
    exact quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward roots
  rw [← hpair]
  exact subset_closure (Set.mem_range_self profile)

/-- The rational iterate is exactly the actual solo prefix over the OLD word. -/
theorem quittingTerminalSemanticPair_rationalSoloPrefix_eq_iterate
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) (owner : Fin players)
    {hazard : ℚ} (hhazard : hazard ∈ Set.Icc (0 : ℚ) 1) (steps : ℕ) :
    quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          ((List.replicate steps (rationalQuittingSoloRoot owner hazard) ++ roots).map
            RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) =
      (rationalQuittingSoloSemanticIterate reward owner hazard
        (rationalQuittingFiniteWordSemanticPair reward roots) steps).toReal := by
  rw [List.map_append, List.map_replicate, quittingLiteralRootStackProfile_append,
    rationalQuittingSoloRoot_toPMF_eq owner hhazard,
    quittingTerminalSemanticPair_replicate_solo_word,
    quittingTerminalSemanticPair_rationalFiniteWord_eq_cast]
  exact quittingSoloSemanticIterate_rational_eq_cast reward owner hhazard _ steps

/-- The literal finite source and failed positive column internally produce a
payoff hit below the logarithmic horizon. No preemption gap is required. -/
theorem exists_rationalSoloPayoffDebtThreshold_hit_le_horizon
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) (owner blocker : Fin players)
    {M hazard working : ℚ} (hM : 0 < M) (hworking : 0 < working)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hhazard0 : 0 < hazard) (hhazard1 : hazard < 1)
    (hcharge : 4 * M * hazard = working / 4)
    (howner : working / 4 <
      (rationalQuittingFiniteWordSemanticPair reward roots).2 owner -
        reward (quittingSingletonTerminal owner) owner)
    (hne : blocker ≠ owner)
    (hcolumn : reward (quittingSingletonTerminal owner) blocker <
      reward (quittingSingletonTerminal blocker) blocker + working / 4) :
    ∃ steps ≤ quittingSoloCapThresholdHorizon (M : ℝ) (hazard : ℝ) ((working : ℝ) / 2),
      rationalSoloPayoffDebtThresholdHit reward owner hazard working
        (rationalQuittingFiniteWordSemanticPair reward roots) steps := by
  have hrewardReal : ∀ terminal who,
      |rationalQuittingRewardToReal reward terminal who| ≤ (M : ℝ) := by
    intro terminal who
    change |(reward terminal who : ℝ)| ≤ (M : ℝ)
    exact_mod_cast hreward terminal who
  have hownerReal : (working : ℝ) / 4 <
      (rationalQuittingFiniteWordSemanticPair reward roots).toReal.2 owner -
        rationalQuittingRewardToReal reward (quittingSingletonTerminal owner) owner := by
    change (working : ℝ) / 4 <
      ((rationalQuittingFiniteWordSemanticPair reward roots).2 owner : ℝ) -
        (reward (quittingSingletonTerminal owner) owner : ℝ)
    exact_mod_cast howner
  have hcolumnReal : rationalQuittingRewardToReal reward
      (quittingSingletonTerminal owner) blocker <
      rationalQuittingRewardToReal reward (quittingSingletonTerminal blocker) blocker +
        (working : ℝ) / 4 := by
    change (reward (quittingSingletonTerminal owner) blocker : ℝ) <
      (reward (quittingSingletonTerminal blocker) blocker : ℝ) + (working : ℝ) / 4
    exact_mod_cast hcolumn
  obtain ⟨steps, hsteps, hhit⟩ := exists_soloPayoffDebtThreshold_hit_le_horizon
    (rationalQuittingRewardToReal reward)
    (rationalQuittingFiniteWordSemanticPair reward roots).toReal owner blocker
    (M := (M : ℝ)) (working := (working : ℝ)) (θ := (hazard : ℝ))
    (by exact_mod_cast hM) (by exact_mod_cast hworking) hrewardReal
    (rationalQuittingFiniteWordSemanticPair_mem_carrier reward roots)
    (by exact_mod_cast hhazard0) (by exact_mod_cast hhazard1)
    (by exact_mod_cast hcharge) hownerReal hne hcolumnReal
  exact ⟨steps, hsteps,
    (rationalSoloPayoffDebtThresholdHit_iff_real reward owner
      ⟨hhazard0.le, hhazard1.le⟩ working _ steps).mpr hhit⟩

/-- Computable first payoff/debt hit. The existence proof is erased. -/
def rationalFirstSoloPayoffDebtThresholdIndex
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard working : ℚ) (source : RationalQuittingSemanticPair players)
    (hexists : ∃ steps,
      rationalSoloPayoffDebtThresholdHit reward owner hazard working source steps) : ℕ :=
  Nat.find hexists

theorem rationalFirstSoloPayoffDebtThresholdIndex_spec
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard working : ℚ) (source : RationalQuittingSemanticPair players)
    (hexists : ∃ steps,
      rationalSoloPayoffDebtThresholdHit reward owner hazard working source steps) :
    rationalSoloPayoffDebtThresholdHit reward owner hazard working source
      (rationalFirstSoloPayoffDebtThresholdIndex reward owner hazard working source hexists) :=
  Nat.find_spec hexists

theorem rationalFirstSoloPayoffDebtThresholdIndex_before
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard working : ℚ) (source : RationalQuittingSemanticPair players)
    (hexists : ∃ steps,
      rationalSoloPayoffDebtThresholdHit reward owner hazard working source steps)
    {steps : ℕ}
    (hsteps : steps <
      rationalFirstSoloPayoffDebtThresholdIndex reward owner hazard working source hexists) :
    ¬rationalSoloPayoffDebtThresholdHit reward owner hazard working source steps :=
  Nat.find_min hexists hsteps

theorem rationalFirstSoloPayoffDebtThresholdIndex_le
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard working : ℚ) (source : RationalQuittingSemanticPair players)
    (hexists : ∃ steps,
      rationalSoloPayoffDebtThresholdHit reward owner hazard working source steps)
    {steps : ℕ}
    (hhit : rationalSoloPayoffDebtThresholdHit reward owner hazard working source steps) :
    rationalFirstSoloPayoffDebtThresholdIndex reward owner hazard working source hexists ≤ steps :=
  Nat.find_min' hexists hhit

end GameTheory
