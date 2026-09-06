import MathUE.Topology.FiniteLabelSubsequence
import UniformEquilibrium.Diagnostics.Quitting.FinFourVanishingSurvivalFiniteSourceCapHandoff

/-! # A fixed paid-row observer along the finite-source handoffs -/

noncomputable section

namespace GameTheory

open Filter Math.Probability

/-- A strict sequence of literal finite handoffs whose full-gap and reached
paid rows use one fixed observer.  At each rank both rows still come from the
same `PaidRows` object, so their actual source witnesses are not reselected. -/
structure FinFourFixedObserverPaidRows
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {source : StationaryQuitNowCapPinSource reward}
    {roots : ℕ → Fin 4 → PMF Bool} {minimum gap : ℝ}
    (branch : FirstStationaryRootZeroBranch source roots minimum gap)
    (terminalGap bound : ℝ) where
  index : ℕ → ℕ
  index_strictMono : StrictMono index
  handoff : ∀ rank, FinFourFiniteSourceCapHandoff branch (index rank)
  paid : ∀ rank, (handoff rank).PaidRows terminalGap bound
  observer : Fin 4
  observer_eq : ∀ rank, (paid rank).observer = observer

/-- The actual vanishing-survival branch, together with the genuine terminal
gap witness, has a fixed paid observer after a strict subsequence. -/
theorem FirstStationaryRootZeroBranch.nonempty_fixedObserverPaidRows
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {source : StationaryQuitNowCapPinSource reward}
    {roots : ℕ → Fin 4 → PMF Bool} {minimum gap : ℝ}
    (branch : FirstStationaryRootZeroBranch source roots minimum gap)
    {terminalGap bound : ℝ} (hgapPos : 0 < terminalGap)
    (exploit : HasTerminalExploitabilityGap reward terminalGap)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    Nonempty (FinFourFixedObserverPaidRows branch terminalGap bound) := by
  obtain ⟨cutoff, hready⟩ :=
    eventually_atTop.1 branch.nonempty_finiteSourceCapHandoff
  let handoff : ∀ rank, FinFourFiniteSourceCapHandoff branch (cutoff + rank) :=
    fun rank ↦ Classical.choice (hready (cutoff + rank) (Nat.le_add_right cutoff rank))
  let paid : ∀ rank, (handoff rank).PaidRows terminalGap bound :=
    fun rank ↦ Classical.choice
      ((handoff rank).exists_distinctTerminalGapPaidRows hgapPos exploit hreward)
  obtain ⟨observer, subsequence, hmono, hobserver⟩ :=
    Math.exists_fixed_label_on_strictMono_subsequence (fun rank ↦ (paid rank).observer)
  refine ⟨{
    index := fun rank ↦ cutoff + subsequence rank
    index_strictMono := fun _ _ hlt ↦ Nat.add_lt_add_left (hmono hlt) cutoff
    handoff := fun rank ↦ handoff (subsequence rank)
    paid := fun rank ↦ paid (subsequence rank)
    observer := observer
    observer_eq := hobserver }⟩

end GameTheory
