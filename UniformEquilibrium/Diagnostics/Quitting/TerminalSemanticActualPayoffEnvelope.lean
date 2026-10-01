import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPayoffEnvelope
import Mathlib.Data.Finset.Lattice.Fold

/-! # The literal actual-payoff supremum envelope

This specializes the existing quadratic-margin bound to
max(0, sup over actual profiles of their minimum singleton surplus).
No envelope witness or payoff realizer is supplied by the consumer.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The minimum singleton surplus of an actual complete behavioral profile. -/
def quittingActualMinimumSingletonSurplus
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun who =>
    quittingTerminalPayoff reward profile who - reward (quittingSingletonTerminal who) who

/-- The literal nonnegative actual-payoff envelope in the cap-threshold packet. -/
def quittingActualSingletonSurplusEnvelope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  max 0 (sSup (Set.range (quittingActualMinimumSingletonSurplus reward)))

omit [DecidableEq ι] in
theorem quittingActualSingletonSurplusEnvelope_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 ≤ quittingActualSingletonSurplusEnvelope reward :=
  le_max_left _ _

omit [DecidableEq ι] in
private theorem actualMinimumSingletonSurplus_bddAbove
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    BddAbove (Set.range (quittingActualMinimumSingletonSurplus reward)) := by
  classical
  let owner : ι := Classical.choice inferInstance
  refine ⟨2 * quittingRewardBound reward, ?_⟩
  rintro _ ⟨profile, rfl⟩
  have hminimum : quittingActualMinimumSingletonSurplus reward profile ≤
      quittingTerminalPayoff reward profile owner -
        reward (quittingSingletonTerminal owner) owner :=
    Finset.inf'_le _ (Finset.mem_univ owner)
  have hpayoff := abs_quittingTerminalPayoff_le_quittingRewardBound reward profile owner
  have hsolo := abs_reward_le_quittingRewardBound reward
    (quittingSingletonTerminal owner) owner
  linarith [(abs_le.mp hpayoff).2, (abs_le.mp hsolo).1]

omit [DecidableEq ι] in
/-- The envelope upper-bound witness is derived from the actual finite minimum
and bounded supremum, not accepted as additional source data. -/
theorem exists_owner_payoffMargin_le_actualSingletonSurplusEnvelope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∃ owner, quittingTerminalPayoff reward profile owner -
      reward (quittingSingletonTerminal owner) owner ≤
        quittingActualSingletonSurplusEnvelope reward := by
  have hsup : quittingActualMinimumSingletonSurplus reward profile ≤
      sSup (Set.range (quittingActualMinimumSingletonSurplus reward)) :=
    le_csSup (actualMinimumSingletonSurplus_bddAbove reward) (Set.mem_range_self profile)
  have hupper : quittingActualMinimumSingletonSurplus reward profile ≤
      quittingActualSingletonSurplusEnvelope reward := hsup.trans (le_max_right _ _)
  obtain ⟨owner, _, howner⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty (α := ι)) fun who =>
      quittingTerminalPayoff reward profile who - reward (quittingSingletonTerminal who) who
  refine ⟨owner, ?_⟩
  simpa only [quittingActualMinimumSingletonSurplus, howner] using hupper

/-- The literal supremum-envelope display at any carrier pair with the
quadratic margins; the preceding owner derives its actual upper envelope. -/
theorem terminalSemanticDebtSum_le_sqrt_actualSingletonSurplusEnvelope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    {M : ℝ} (hM : 0 < M)
    (hquadratic : ∀ owner,
      quittingTerminalSemanticDebtSum pair ^ 2 / (8 * M) ≤
        pair.1 owner - reward (quittingSingletonTerminal owner) owner) :
    quittingTerminalSemanticDebtSum pair ≤
      Real.sqrt (8 * M * quittingActualSingletonSurplusEnvelope reward) :=
  terminalSemanticDebtSum_le_sqrt_of_all_quadraticMargins reward pair hpair hM
    (quittingActualSingletonSurplusEnvelope_nonneg reward) hquadratic
    (exists_owner_payoffMargin_le_actualSingletonSurplusEnvelope reward)

/-- Nonnegative singleton tables have the literal actual-envelope minimum
bound, with the minimizing pair internally selected by the canonical owner. -/
theorem exists_minimumTerminalSemanticDebt_le_sqrt_actualEnvelope_nonnegativeSingleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsingleton : ∀ owner, 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    ∃ pair : QuittingTerminalSemanticPair ι,
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤ quittingTerminalSemanticDebtSum candidate) ∧
      quittingTerminalSemanticDebtSum pair ≤
        Real.sqrt (8 * M * quittingActualSingletonSurplusEnvelope reward) :=
  exists_minimumTerminalSemanticDebt_le_sqrt_of_nonnegativeSingleton reward hM
    (quittingActualSingletonSurplusEnvelope_nonneg reward) hreward hsingleton
    (exists_owner_payoffMargin_le_actualSingletonSurplusEnvelope reward)

/-- The same literal display for signed Fin4 tables, with no singleton signs. -/
theorem exists_minimumTerminalSemanticDebt_le_sqrt_actualEnvelope_finFour
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ pair : QuittingTerminalSemanticPair (Fin 4),
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤ quittingTerminalSemanticDebtSum candidate) ∧
      quittingTerminalSemanticDebtSum pair ≤
        Real.sqrt (8 * M * quittingActualSingletonSurplusEnvelope reward) :=
  exists_minimumTerminalSemanticDebt_le_sqrt_of_fourPlayer reward (by decide) hM
    (quittingActualSingletonSurplusEnvelope_nonneg reward) hreward
    (exists_owner_payoffMargin_le_actualSingletonSurplusEnvelope reward)

end GameTheory
