import UniformEquilibrium.Diagnostics.Quitting.PureTimeExactResponseMinimumAlternative
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ArbitraryClockMinimumActualReachPaidPort
import UniformEquilibrium.Quitting.Paths.BoundedSupportedPureTimePurification

/-!
# Actual-source entrance to a pure-time response alternative

An off-minimum actual-reach paid port is purified through supported literal
replacements.  If that purification lands on the global minimum, canonical
pure-time deadline descent leaves it again.  The resulting pure-clock source
starts a horizontal selected-response orbit which either first reaches the
minimum face or contains an entirely off-minimum exact-response cycle.

The paid row is retained as historical provenance.  The selected-response
orbit is not an in-game chronology, a renewable return, or an equilibrium
construction.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Source-faithful data from one actual off-minimum paid port to a pure-clock
minimum entrance or an entirely off-minimum horizontal response cycle. -/
structure QuittingActualSourcePureTimeResponseAlternative
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (original : ℕ → (quittingGame reward).BehaviorProfile)
    (minimumDebt M : ℝ) where
  port : QuittingOffMinimumActualReachPaidPort
    reward original minimumDebt M
  purification : QuittingBehaviorSupportedPureTimePurification
    reward port.target
  initial : QuittingPureTimeProfile ι
  purified_to_initial : IsQuittingPureTimeReplacementAncestry
    purification.targetTimes initial
  source_to_initial : IsQuittingBehaviorReplacementAncestry
    (original port.sourceIndex)
      (quittingPureTimeProfileBehavior reward initial)
  initial_offMinimum : minimumDebt <
    quittingPureTimeTerminalSemanticDebtSum reward initial
  alternative :
    Xor (Nonempty (QuittingPureTimeMinimumDebtEntrance
        reward initial minimumDebt))
      (Nonempty (QuittingPureTimeOffMinimumExactResponseCycle
        reward initial minimumDebt))
  source_to_orbit_profile : ∀ time,
    IsQuittingBehaviorReplacementAncestry
      (original port.sourceIndex)
      (quittingPureTimeProfileBehavior reward
        (quittingPureTimeSelectedExactResponseOrbit
          reward initial time).toProfile)

namespace QuittingOffMinimumActualReachPaidPort

/-- A supplied off-minimum actual-reach port enters the pure-clock response
alternative without reselecting its retained actual source. -/
theorem exists_actualSourcePureTimeResponseAlternative
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {original : ℕ → (quittingGame reward).BehaviorProfile}
    {minimumDebt M : ℝ}
    (port : QuittingOffMinimumActualReachPaidPort
      reward original minimumDebt M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      minimumDebt ≤ quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < minimumDebt) :
    ∃ result : QuittingActualSourcePureTimeResponseAlternative
        reward original minimumDebt M,
      result.port = port := by
  obtain ⟨purification⟩ :=
    nonempty_quittingBehaviorSupportedPureTimePurification reward port.target
  have hpurifiedLower : minimumDebt ≤
      quittingPureTimeTerminalSemanticDebtSum
        reward purification.targetTimes := by
    apply hminimum
    exact quittingTerminalSemanticPair_mem_carrier reward
      (quittingPureTimeProfileBehavior reward purification.targetTimes)
  have assemble : ∀ initial : QuittingPureTimeProfile ι,
      IsQuittingPureTimeReplacementAncestry
        purification.targetTimes initial →
      minimumDebt < quittingPureTimeTerminalSemanticDebtSum reward initial →
      ∃ result : QuittingActualSourcePureTimeResponseAlternative
          reward original minimumDebt M,
        result.port = port := by
    intro initial hpureAncestry hoffInitial
    have hsourceToPurified : IsQuittingBehaviorReplacementAncestry
        (original port.sourceIndex)
        (quittingPureTimeProfileBehavior reward purification.targetTimes) :=
      port.ancestry.trans purification.path.ancestry
    have hsourceToInitial : IsQuittingBehaviorReplacementAncestry
        (original port.sourceIndex)
        (quittingPureTimeProfileBehavior reward initial) :=
      hsourceToPurified.trans
        (isQuittingBehaviorReplacementAncestry_pureTimeProfileBehavior
          hpureAncestry)
    have halternative :=
      exists_minimumDebtEntrance_xor_offMinimumExactResponseCycle
        reward initial minimumDebt hpositive
          (fun times => hminimum _
            (quittingTerminalSemanticPair_mem_carrier reward
              (quittingPureTimeProfileBehavior reward times)))
          hoffInitial
    refine ⟨{
      port := port
      purification := purification
      initial := initial
      purified_to_initial := hpureAncestry
      source_to_initial := hsourceToInitial
      initial_offMinimum := hoffInitial
      alternative := halternative
      source_to_orbit_profile := ?_
    }, rfl⟩
    intro time
    exact hsourceToInitial.trans
      (isQuittingBehaviorReplacementAncestry_selectedExactResponseOrbit
        reward initial time)
  rcases hpurifiedLower.lt_or_eq with hstrict | hequal
  · exact assemble purification.targetTimes Relation.ReflTransGen.refl hstrict
  · obtain ⟨initial, hpureAncestry, hoffInitial⟩ :=
      pureTimeMinimum_exists_offMinimum reward minimumDebt hminimum hpositive
        purification.targetTimes hequal.symm
    exact assemble initial hpureAncestry hoffInitial

end QuittingOffMinimumActualReachPaidPort

/-- A supplied realizing sequence for a positive global minimum enters the
source-faithful pure-time response alternative. -/
theorem minimumRealizingSequence_exists_actualSourcePureTimeResponseAlternative
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
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
    Nonempty (QuittingActualSourcePureTimeResponseAlternative
      reward profiles (quittingTerminalSemanticDebtSum minimum) M) := by
  obtain ⟨port⟩ :=
    minimumRealizingSequence_exists_offMinimumActualReachPaidPort
      reward minimum hminimum hpositive profiles hprofiles M hreward
  obtain ⟨result, _⟩ := port.exists_actualSourcePureTimeResponseAlternative
    hminimum hpositive
  exact ⟨result⟩

end GameTheory
