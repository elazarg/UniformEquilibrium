import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ArbitraryClockMinimumActualReachPaidPort

/-!
# Four-player arbitrary-clock minimum reduction

This file only normalizes the generic player-cardinality constants to four.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

/-- Four-player literal normalization of the arbitrary-clock paid-port
passport. -/
structure FinFourOffMinimumActualReachPaidPort
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (original : ℕ → (quittingGame reward).BehaviorProfile)
    (minimumDebt M : ℝ) where
  port : QuittingOffMinimumActualReachPaidPort
    reward original minimumDebt M
  observerDebtFloor : minimumDebt / 4 ≤
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward port.target) port.observer
  paidGainFloor : minimumDebt / 16 ≤
    port.row.liveMass * port.row.reachedGain
  ownSurvivalFloor : minimumDebt / 4 ≤
    4 * M * quittingHazardSurvival
      (quittingBehaviorLiveHazard reward
        (port.target port.observer)) port.row.start
  opponentLiveFloor : minimumDebt / 4 ≤ 8 * M * port.row.liveMass
  jointReachFloor :
    (minimumDebt / 4) * (minimumDebt / 4) ≤
      32 * M * M * quittingSurvivalPrefix
        (quittingProfileLiveRoot reward port.target) port.row.start

/-- A supplied four-player realizing sequence for a positive global minimum
has a literal off-minimum descendant with debt `D*/4`, paid gain `D*/16`,
and the same actual-reach passport. -/
theorem finFourMinimumRealizingSequence_exists_offMinimumActualReachPaidPort
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
    Nonempty (FinFourOffMinimumActualReachPaidPort reward profiles
      (quittingTerminalSemanticDebtSum minimum) M) := by
  obtain ⟨port⟩ :=
    minimumRealizingSequence_exists_offMinimumActualReachPaidPort
      reward minimum hminimum hpositive profiles hprofiles M hreward
  exact ⟨{
    port := port
    observerDebtFloor := by simpa using port.observerDebtFloor
    paidGainFloor := by
      convert port.paidGainFloor using 1
      norm_num
    ownSurvivalFloor := by simpa using port.ownSurvivalFloor
    opponentLiveFloor := by simpa using port.opponentLiveFloor
    jointReachFloor := by simpa using port.jointReachFloor }⟩

/-- Positive four-player terminal-debt infimum directly selects a compact
minimum, a retained realizing sequence, and the normalized actual-reach paid
port with debt `D*/4` and gain `D*/16`. -/
theorem exists_finFourMinimumRealizingSequence_offMinimumActualReachPaidPort_of_debtSumInf_pos
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
      Nonempty (FinFourOffMinimumActualReachPaidPort reward profiles
        (quittingTerminalDebtSumInf reward) M) := by
  obtain ⟨minimum, profiles, hminimumMem, hminimum, hminimumValue, hprofiles,
      _port⟩ :=
    exists_minimumRealizingSequence_offMinimumActualReachPaidPort_of_debtSumInf_pos
      reward M hreward hinf
  have hport :=
    finFourMinimumRealizingSequence_exists_offMinimumActualReachPaidPort
      reward minimum hminimum (hminimumValue ▸ hinf) profiles hprofiles M hreward
  exact ⟨minimum, profiles, hminimumMem, hminimum, hminimumValue, hprofiles,
    by simpa only [hminimumValue] using hport⟩

end GameTheory
