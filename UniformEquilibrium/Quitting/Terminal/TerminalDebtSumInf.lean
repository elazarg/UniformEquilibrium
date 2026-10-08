import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt

/-! # The actual-profile SUM-debt infimum

The literal behavioral infimum agrees with every global minimum on the
original terminal-semantic carrier. Positivity is equivalent to failure of
uniform-payoff existence for an inhabited finite player type.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Literal total deviation debt is exactly total debt of the associated
finite-dimensional terminal-semantic pair. -/
theorem quittingTerminalDebtSum_eq_terminalSemanticDebtSum
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalDebtSum reward profile =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) := by
  rfl

/-- Infimum of total literal debt over executable behavior profiles. -/
def quittingTerminalDebtSumInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  sInf (Set.range (quittingTerminalDebtSum reward))

theorem bddBelow_range_quittingTerminalDebtSum
    : BddBelow (Set.range (quittingTerminalDebtSum reward)) := by
  refine ⟨0, ?_⟩
  rintro total ⟨profile, rfl⟩
  unfold quittingTerminalDebtSum
  exact Finset.sum_nonneg fun player _ =>
    quittingTerminalDeviationDebt_nonneg reward profile player

/-- The literal total-debt infimum is nonnegative. -/
theorem quittingTerminalDebtSumInf_nonneg :
    0 ≤ quittingTerminalDebtSumInf reward := by
  unfold quittingTerminalDebtSumInf
  have hrange : (Set.range (quittingTerminalDebtSum reward)).Nonempty :=
    ⟨quittingTerminalDebtSum reward (quittingAlwaysContinueProfile reward),
      quittingAlwaysContinueProfile reward, rfl⟩
  apply (le_csInf_iff
    (bddBelow_range_quittingTerminalDebtSum (reward := reward)) hrange).2
  rintro total ⟨profile, rfl⟩
  unfold quittingTerminalDebtSum
  exact Finset.sum_nonneg fun player _ =>
    quittingTerminalDeviationDebt_nonneg reward profile player

/-- The total-debt infimum lies below every actual profile. -/
theorem quittingTerminalDebtSumInf_le
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalDebtSumInf reward ≤
      quittingTerminalDebtSum reward profile := by
  exact csInf_le (bddBelow_range_quittingTerminalDebtSum
    (reward := reward)) ⟨profile, rfl⟩

/-- One exact terminal Nash profile forces the literal total-debt infimum to
zero. -/
theorem quittingTerminalDebtSumInf_eq_zero_of_isZeroAsymptoticNash
    (profile : (quittingGame reward).BehaviorProfile)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 profile) :
    quittingTerminalDebtSumInf reward = 0 := by
  apply le_antisymm
  · calc
      quittingTerminalDebtSumInf reward ≤
          quittingTerminalDebtSum reward profile :=
        quittingTerminalDebtSumInf_le profile
      _ = quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) :=
        quittingTerminalDebtSum_eq_terminalSemanticDebtSum profile
      _ ≤ Fintype.card ι * (0 : ℝ) :=
        terminalSemanticDebtSum_le_card_mul_of_isEpsilonAsymptoticNash
          reward profile 0 hnash
      _ = 0 := by ring
  · exact quittingTerminalDebtSumInf_nonneg

/-- The literal-profile debt infimum equals the value of every global
minimum on the compact terminal-semantic carrier.  Passing to the closure
neither lowers nor raises the infimum of this continuous debt functional. -/
theorem quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate) :
    quittingTerminalDebtSumInf reward =
      quittingTerminalSemanticDebtSum pair := by
  apply le_antisymm
  · obtain ⟨profiles, hprofiles⟩ :=
      exists_terminalProfile_sequence_tendsto_semanticPair reward pair hpair
    have hdebt : Tendsto (fun n => quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profiles n))) atTop
        (nhds (quittingTerminalSemanticDebtSum pair)) :=
      continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
        hprofiles
    apply ge_of_tendsto hdebt
    apply Filter.Eventually.of_forall
    intro n
    rw [← quittingTerminalDebtSum_eq_terminalSemanticDebtSum]
    exact quittingTerminalDebtSumInf_le (reward := reward) (profiles n)
  · unfold quittingTerminalDebtSumInf
    have hrange : (Set.range (quittingTerminalDebtSum reward)).Nonempty :=
      ⟨quittingTerminalDebtSum reward
          (quittingAlwaysContinueProfile reward),
        quittingAlwaysContinueProfile reward, rfl⟩
    apply (le_csInf_iff
      (bddBelow_range_quittingTerminalDebtSum (reward := reward))
      hrange).2
    rintro total ⟨profile, rfl⟩
    rw [quittingTerminalDebtSum_eq_terminalSemanticDebtSum]
    exact hminimum _ (subset_closure ⟨profile, rfl⟩)

/-- Positivity of the literal total-debt infimum is exactly the compact
positive-minimum terminal-semantic obstruction. -/
theorem quittingTerminalDebtSumInf_pos_iff_hasPositiveMinimumTerminalSemanticDebt :
    0 < quittingTerminalDebtSumInf reward ↔
      HasPositiveMinimumTerminalSemanticDebt reward := by
  constructor
  · intro hinf
    obtain ⟨pair, hpair, hminimum⟩ :=
      exists_minimum_quittingTerminalSemanticDebtSum reward
    have heq :=
      quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
        pair hpair hminimum
    exact ⟨pair, hpair, hminimum, heq ▸ hinf⟩
  · rintro ⟨pair, hpair, hminimum, hpositive⟩
    rw [quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      pair hpair hminimum]
    exact hpositive

/-- For an inhabited finite player type, positive literal total-debt infimum
is equivalently failure of uniform-equilibrium-payoff existence. -/
theorem quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff
    [Nonempty ι] :
    0 < quittingTerminalDebtSumInf reward ↔
      ¬∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingTerminalDebtSumInf_pos_iff_hasPositiveMinimumTerminalSemanticDebt.trans
    (not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
      reward).symm

end GameTheory
