import UniformEquilibrium.Quitting.Root.PureTimeCapPrefixSelection
import UniformEquilibrium.Quitting.Root.TerminalSemanticDebt

/-! # Debt recharge under source-coherent cap responses

Each horizontal child changes one player's strategy to a complete behavioral
cap-attaining response and is literally the next source. Exact debt ledgers
hold for every finite horizon. A supplied common vertical debt-drop bound
forces linear cross-player recharge, with the initial debt as an explicit
boundary term. No exact-prefix word or uniform-equilibrium hypothesis is
needed for these semantic identities.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Supplied actual horizontal cap replacements, coherent with the next source profile. -/
structure QuittingRenewedActualProfileSequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  source : ℕ → (quittingGame reward).BehaviorProfile
  endpoint : ℕ → (quittingGame reward).BehaviorProfile
  owner : ℕ → ι
  response : ∀ phase, (quittingGame reward).BehaviorStrategy (owner phase)
  response_attains_cap : ∀ phase,
    quittingTerminalPayoff reward
        (Function.update (endpoint phase) (owner phase) (response phase)) (owner phase) =
      quittingContinuationBestResponseValue reward (endpoint phase) (owner phase)
  child_eq_next_source : ∀ phase,
    Function.update (endpoint phase) (owner phase) (response phase) = source (phase + 1)

namespace QuittingRenewedActualProfileSequence

def totalDebt
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile)

theorem totalDebt_eq_sum (profile : (quittingGame reward).BehaviorProfile) :
    totalDebt profile = ∑ who, quittingTerminalDeviationDebt reward profile who := by
  rfl

theorem totalDebt_nonneg (profile : (quittingGame reward).BehaviorProfile) :
    0 ≤ totalDebt profile := by
  rw [totalDebt_eq_sum]
  exact Finset.sum_nonneg fun who _ ↦
    quittingTerminalDeviationDebt_nonneg reward profile who

def child (sequence : QuittingRenewedActualProfileSequence reward) (phase : ℕ) :=
  Function.update (sequence.endpoint phase) (sequence.owner phase) (sequence.response phase)

def horizontalDebtInjection (sequence : QuittingRenewedActualProfileSequence reward)
    (phase : ℕ) : ℝ :=
  totalDebt (sequence.child phase) - totalDebt (sequence.endpoint phase)

def capGain (sequence : QuittingRenewedActualProfileSequence reward) (phase : ℕ) : ℝ :=
  quittingTerminalPayoff reward (sequence.child phase) (sequence.owner phase) -
    quittingTerminalPayoff reward (sequence.endpoint phase) (sequence.owner phase)

def crossPlayerDebtInjection (sequence : QuittingRenewedActualProfileSequence reward)
    (phase : ℕ) : ℝ :=
  ∑ who ∈ Finset.univ.erase (sequence.owner phase),
    (quittingTerminalDeviationDebt reward (sequence.child phase) who -
      quittingTerminalDeviationDebt reward (sequence.endpoint phase) who)

theorem owner_child_debt_eq_zero
    (sequence : QuittingRenewedActualProfileSequence reward) (phase : ℕ) :
    quittingTerminalDeviationDebt reward (sequence.child phase) (sequence.owner phase) = 0 := by
  unfold child
  apply quittingTerminalDeviationDebt_update_eq_zero_of_attainsCap
  exact sequence.response_attains_cap phase

theorem owner_endpoint_debt_eq_capGain
    (sequence : QuittingRenewedActualProfileSequence reward) (phase : ℕ) :
    quittingTerminalDeviationDebt reward (sequence.endpoint phase) (sequence.owner phase) =
      sequence.capGain phase := by
  unfold quittingTerminalDeviationDebt capGain
  unfold child
  rw [sequence.response_attains_cap]

theorem horizontalDebtInjection_eq_neg_capGain_add_cross
    (sequence : QuittingRenewedActualProfileSequence reward) (phase : ℕ) :
    sequence.horizontalDebtInjection phase =
      -sequence.capGain phase + sequence.crossPlayerDebtInjection phase := by
  unfold horizontalDebtInjection crossPlayerDebtInjection
  rw [totalDebt_eq_sum, totalDebt_eq_sum]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (sequence.owner phase))]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (sequence.owner phase))]
  rw [sequence.owner_child_debt_eq_zero, sequence.owner_endpoint_debt_eq_capGain]
  rw [Finset.sum_sub_distrib]
  ring

theorem capGain_nonneg
    (sequence : QuittingRenewedActualProfileSequence reward) (phase : ℕ) :
    0 ≤ sequence.capGain phase := by
  rw [← sequence.owner_endpoint_debt_eq_capGain]
  exact quittingTerminalDeviationDebt_nonneg reward _ _

theorem sum_horizontalDebtInjection_eq_sum_verticalDrop_add_boundary
    (sequence : QuittingRenewedActualProfileSequence reward) (horizon : ℕ) :
    (∑ phase ∈ Finset.range horizon, sequence.horizontalDebtInjection phase) =
      (∑ phase ∈ Finset.range horizon,
        (totalDebt (sequence.source phase) - totalDebt (sequence.endpoint phase))) +
        totalDebt (sequence.source horizon) - totalDebt (sequence.source 0) := by
  simp_rw [horizontalDebtInjection, child, sequence.child_eq_next_source]
  have htelescope :=
    Finset.sum_range_sub (fun phase ↦ totalDebt (sequence.source phase)) horizon
  rw [Finset.sum_sub_distrib] at htelescope
  simp_rw [Finset.sum_sub_distrib]
  linarith

theorem card_mul_minimumDebtDrop_add_boundary_le_sum_horizontalDebtInjection
    (sequence : QuittingRenewedActualProfileSequence reward) (minimumDebtDrop : ℝ)
    (hminimum : ∀ phase, minimumDebtDrop ≤
      totalDebt (sequence.source phase) - totalDebt (sequence.endpoint phase))
    (horizon : ℕ) :
    (horizon : ℝ) * minimumDebtDrop + totalDebt (sequence.source horizon) -
          totalDebt (sequence.source 0) ≤
      ∑ phase ∈ Finset.range horizon, sequence.horizontalDebtInjection phase := by
  rw [sequence.sum_horizontalDebtInjection_eq_sum_verticalDrop_add_boundary]
  have hsum : (horizon : ℝ) * minimumDebtDrop ≤
      ∑ phase ∈ Finset.range horizon,
        (totalDebt (sequence.source phase) - totalDebt (sequence.endpoint phase)) := by
    calc
      (horizon : ℝ) * minimumDebtDrop =
          ∑ _phase ∈ Finset.range horizon, minimumDebtDrop := by simp
      _ ≤ _ := Finset.sum_le_sum fun phase _ ↦ hminimum phase
  linarith

theorem card_mul_minimumDebtDrop_add_gain_boundary_le_sum_crossPlayerDebtInjection
    (sequence : QuittingRenewedActualProfileSequence reward) (minimumDebtDrop : ℝ)
    (hminimum : ∀ phase, minimumDebtDrop ≤
      totalDebt (sequence.source phase) - totalDebt (sequence.endpoint phase))
    (horizon : ℕ) :
    (horizon : ℝ) * minimumDebtDrop +
        (∑ phase ∈ Finset.range horizon, sequence.capGain phase) +
        totalDebt (sequence.source horizon) - totalDebt (sequence.source 0) ≤
      ∑ phase ∈ Finset.range horizon, sequence.crossPlayerDebtInjection phase := by
  have hhorizontal :=
    sequence.card_mul_minimumDebtDrop_add_boundary_le_sum_horizontalDebtInjection
      minimumDebtDrop hminimum horizon
  have hphase (phase : ℕ) : sequence.crossPlayerDebtInjection phase =
      sequence.horizontalDebtInjection phase + sequence.capGain phase := by
    rw [sequence.horizontalDebtInjection_eq_neg_capGain_add_cross]
    ring
  simp_rw [hphase, Finset.sum_add_distrib]
  linarith

theorem card_mul_minimumDebtDrop_sub_initial_le_sum_horizontalDebtInjection
    (sequence : QuittingRenewedActualProfileSequence reward) (minimumDebtDrop : ℝ)
    (hminimum : ∀ phase, minimumDebtDrop ≤
      totalDebt (sequence.source phase) - totalDebt (sequence.endpoint phase))
    (horizon : ℕ) :
    (horizon : ℝ) * minimumDebtDrop - totalDebt (sequence.source 0) ≤
      ∑ phase ∈ Finset.range horizon, sequence.horizontalDebtInjection phase := by
  have h := sequence.card_mul_minimumDebtDrop_add_boundary_le_sum_horizontalDebtInjection
    minimumDebtDrop hminimum horizon
  have hterminal := totalDebt_nonneg (sequence.source horizon)
  linarith

theorem card_mul_minimumDebtDrop_add_gain_sub_initial_le_sum_crossPlayerDebtInjection
    (sequence : QuittingRenewedActualProfileSequence reward) (minimumDebtDrop : ℝ)
    (hminimum : ∀ phase, minimumDebtDrop ≤
      totalDebt (sequence.source phase) - totalDebt (sequence.endpoint phase))
    (horizon : ℕ) :
    (horizon : ℝ) * minimumDebtDrop +
        (∑ phase ∈ Finset.range horizon, sequence.capGain phase) -
        totalDebt (sequence.source 0) ≤
      ∑ phase ∈ Finset.range horizon, sequence.crossPlayerDebtInjection phase := by
  have h :=
    sequence.card_mul_minimumDebtDrop_add_gain_boundary_le_sum_crossPlayerDebtInjection
      minimumDebtDrop hminimum horizon
  have hterminal := totalDebt_nonneg (sequence.source horizon)
  linarith

/-- Exact cross-player recharge pays vertical debt drops and owner gains, with both boundaries. -/
theorem sum_crossPlayerDebtInjection_eq_sum_verticalDrop_add_gain_boundary
    (sequence : QuittingRenewedActualProfileSequence reward) (horizon : ℕ) :
    (∑ phase ∈ Finset.range horizon, sequence.crossPlayerDebtInjection phase) =
      (∑ phase ∈ Finset.range horizon,
        (totalDebt (sequence.source phase) - totalDebt (sequence.endpoint phase))) +
      (∑ phase ∈ Finset.range horizon, sequence.capGain phase) +
      totalDebt (sequence.source horizon) - totalDebt (sequence.source 0) := by
  have hphase (phase : ℕ) : sequence.crossPlayerDebtInjection phase =
      sequence.horizontalDebtInjection phase + sequence.capGain phase := by
    rw [sequence.horizontalDebtInjection_eq_neg_capGain_add_cross]
    ring
  simp_rw [hphase, Finset.sum_add_distrib]
  rw [sequence.sum_horizontalDebtInjection_eq_sum_verticalDrop_add_boundary]
  ring

end QuittingRenewedActualProfileSequence
end GameTheory
