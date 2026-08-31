import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualSourcePureTimeResponseAlternative
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.FinFourArbitraryClockMinimumActualReachPaidPort

/-!
# Four-player actual-source pure-time response alternative

This module retains the normalized four-player paid port while attaching the
bounded supported purification and the horizontal pure-clock response
alternative.  It does not turn that orbit into a chronology or consume either
branch.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

/-- Four-player source-faithful entrance retaining both the normalized paid
port and its subsequent pure-clock response alternative. -/
structure FinFourActualSourcePureTimeResponseAlternative
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (original : ℕ → (quittingGame reward).BehaviorProfile)
    (minimumDebt M : ℝ) where
  sourcePort : FinFourOffMinimumActualReachPaidPort
    reward original minimumDebt M
  response : QuittingActualSourcePureTimeResponseAlternative
    reward original minimumDebt M
  response_port_eq : response.port = sourcePort.port
  purification_replacementCount_le_four :
    response.purification.replacementCount ≤ 4
  bounded_alternative :
    Xor
      (∃ entrance : QuittingPureTimeMinimumDebtEntrance
          reward response.initial minimumDebt,
        entrance.time ≤ 1296)
      (∃ cycle : QuittingPureTimeOffMinimumExactResponseCycle
          reward response.initial minimumDebt,
        cycle.start + cycle.period ≤ 1296 ∧ cycle.period ≤ 1296)

private theorem bounded_alternative_of_response
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {original : ℕ → (quittingGame reward).BehaviorProfile}
    {minimumDebt M : ℝ}
    (response : QuittingActualSourcePureTimeResponseAlternative
      reward original minimumDebt M) :
    Xor
      (∃ entrance : QuittingPureTimeMinimumDebtEntrance
          reward response.initial minimumDebt,
        entrance.time ≤ 1296)
      (∃ cycle : QuittingPureTimeOffMinimumExactResponseCycle
          reward response.initial minimumDebt,
        cycle.start + cycle.period ≤ 1296 ∧ cycle.period ≤ 1296) := by
  have halternative := response.alternative
  rw [xor_def] at halternative ⊢
  rcases halternative with
      ⟨⟨entrance⟩, hnotCycle⟩ | ⟨⟨cycle⟩, hnotEntrance⟩
  · refine Or.inl ⟨⟨entrance, entrance.time_le_stateCard.trans ?_⟩, ?_⟩
    · exact card_quittingPureTimeInheritedState_le_1296_finFour response.initial
    · rintro ⟨otherCycle, _hend, _hperiod⟩
      exact hnotCycle ⟨otherCycle⟩
  · refine Or.inr ⟨⟨cycle, ?_, ?_⟩, ?_⟩
    · exact cycle.end_le_stateCard.trans
        (card_quittingPureTimeInheritedState_le_1296_finFour response.initial)
    · exact (Nat.le_add_left cycle.period cycle.start).trans
        (cycle.end_le_stateCard.trans
          (card_quittingPureTimeInheritedState_le_1296_finFour response.initial))
    · rintro ⟨otherEntrance, _htime⟩
      exact hnotEntrance ⟨otherEntrance⟩

namespace FinFourOffMinimumActualReachPaidPort

/-- A normalized four-player paid port enters the source-faithful pure-clock
response alternative in at most four supported purification replacements. -/
theorem exists_actualSourcePureTimeResponseAlternative
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {original : ℕ → (quittingGame reward).BehaviorProfile}
    {minimumDebt M : ℝ}
    (sourcePort : FinFourOffMinimumActualReachPaidPort
      reward original minimumDebt M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      minimumDebt ≤ quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < minimumDebt) :
    Nonempty (FinFourActualSourcePureTimeResponseAlternative
      reward original minimumDebt M) := by
  obtain ⟨response, hresponse⟩ :=
    sourcePort.port.exists_actualSourcePureTimeResponseAlternative
      hminimum hpositive
  exact ⟨{
    sourcePort := sourcePort
    response := response
    response_port_eq := hresponse
    purification_replacementCount_le_four := by
      simpa using response.purification.replacementCount_le_card
    bounded_alternative := bounded_alternative_of_response response }⟩

end FinFourOffMinimumActualReachPaidPort

/-- A supplied four-player realizing sequence for a positive global minimum
enters the normalized source-faithful pure-clock response alternative. -/
theorem finFourMinimumRealizingSequence_exists_actualSourcePureTimeResponseAlternative
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hprofiles : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (𝓝 minimum))
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (FinFourActualSourcePureTimeResponseAlternative
      reward profiles (quittingTerminalSemanticDebtSum minimum) M) := by
  obtain ⟨sourcePort⟩ :=
    finFourMinimumRealizingSequence_exists_offMinimumActualReachPaidPort
      reward minimum hminimum hpositive profiles hprofiles M hreward
  exact sourcePort.exists_actualSourcePureTimeResponseAlternative
    hminimum hpositive

/-- Positive four-player terminal-debt infimum directly selects a compact
minimum, one realizing sequence, and its normalized source-faithful pure-clock
response alternative. -/
theorem exists_finFourActualSourcePureTimeResponseAlternative_of_debtSumInf_pos
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinf : 0 < quittingTerminalDebtSumInf reward) :
    ∃ (minimum : QuittingTerminalSemanticPair (Fin 4))
        (profiles : ℕ → (quittingGame reward).BehaviorProfile),
      minimum ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      quittingTerminalSemanticDebtSum minimum =
        quittingTerminalDebtSumInf reward ∧
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
        atTop (𝓝 minimum) ∧
      Nonempty (FinFourActualSourcePureTimeResponseAlternative
        reward profiles (quittingTerminalDebtSumInf reward) M) := by
  obtain ⟨minimum, profiles, hminimumMem, hminimum, hminimumValue, hprofiles,
      sourcePort⟩ :=
    exists_finFourMinimumRealizingSequence_offMinimumActualReachPaidPort_of_debtSumInf_pos
      reward M hreward hinf
  obtain ⟨result⟩ := sourcePort
  have hminimumInf : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalDebtSumInf reward ≤
        quittingTerminalSemanticDebtSum candidate := by
    intro candidate hcandidate
    rw [← hminimumValue]
    exact hminimum candidate hcandidate
  have hresponse := result.exists_actualSourcePureTimeResponseAlternative
    hminimumInf hinf
  exact ⟨minimum, profiles, hminimumMem, hminimum, hminimumValue, hprofiles,
    by simpa only [hminimumValue] using hresponse⟩

end GameTheory
