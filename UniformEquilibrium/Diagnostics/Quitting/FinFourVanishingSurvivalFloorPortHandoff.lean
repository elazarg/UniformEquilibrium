import UniformEquilibrium.Diagnostics.Quitting.FinFourVanishingSurvivalFiniteSourceCapHandoff
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidRowExactPortAlternative
import UniformEquilibrium.Quitting.Stationary.MinMax

/-! # Floor-port continuation of the literal Fin4 cap handoff -/

noncomputable section

namespace GameTheory
namespace FinFourFiniteSourceCapHandoff

open Math.Probability

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {source : StationaryQuitNowCapPinSource reward}
variable {roots : ℕ → Fin 4 → PMF Bool} {minimum gap : ℝ}
variable {branch : FirstStationaryRootZeroBranch source roots minimum gap}
variable {index : ℕ}

/-- Exact cap attainment puts the updated owner above its behavioral
punishment floor at the literal finite child. -/
theorem owner_punishment_le_child_payoff
    (handoff : FinFourFiniteSourceCapHandoff branch index) :
    quittingPunishmentValue reward branch.owner ≤
      quittingTerminalPayoff reward handoff.child branch.owner := by
  have hpunishment : quittingPunishmentValue reward branch.owner ≤
      quittingContinuationBestResponseValue reward handoff.child branch.owner := by
    simpa [quittingBestReplyValue, quittingContinuationBestResponseValue, iSup] using
      (quittingPunishmentValue_le reward branch.owner handoff.child)
  have hzero := handoff.child_owner_debt_eq_zero
  unfold quittingTerminalDeviationDebt at hzero
  linarith

/-- Package the already selected full-gap row at exactly the finite child
once every prescribed payoff is above its punishment floor. -/
def floorSafeSource
    (handoff : FinFourFiniteSourceCapHandoff branch index)
    {terminalGap bound : ℝ} (paid : handoff.PaidRows terminalGap bound)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward handoff.child who)
    (hgap : 0 < terminalGap) : QuittingPaidRowFloorSafeSource reward where
  profile := handoff.child
  observer := paid.observer
  gain := terminalGap
  gain_pos := hgap
  row := paid.fullGapRow
  punishment_le := hfloor

/-- At the actual cap child, either a displayed nonowner is underfloor, or
the literal paid row enters the existing marked exact-orbit alternative.
No stationary replacement or new orbit construction occurs here. -/
theorem floorSafeMarkedOrbit_or_underfloor
    (handoff : FinFourFiniteSourceCapHandoff branch index)
    (witness : QuittingTerminalExploitabilityWitness reward)
    {bound : ℝ} (paid : handoff.PaidRows witness.terminalGap bound) :
    (∃ underfloor : Fin 4, underfloor ≠ branch.owner ∧
      quittingTerminalPayoff reward handoff.child underfloor <
        quittingPunishmentValue reward underfloor) ∨
    ∃ hfloor : ∀ who, quittingPunishmentValue reward who ≤
        quittingTerminalPayoff reward handoff.child who,
      ∃ marked : QuittingPaidRowMarkedExactOrbit
          (handoff.floorSafeSource paid hfloor witness.terminalGap_pos),
        (∃ payoff : Payoff (Fin 4),
          (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
        ∃ port :
            QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
              marked.orbit,
          Nonempty (QuittingPaidRowMarkedExactOrbit.SummableSemanticPort marked port) ∧
          Nonempty (QuittingPaidRowMarkedExactOrbit.PositivePaidSuffixReach marked) := by
  by_cases hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward handoff.child who
  · right
    let floorSource := handoff.floorSafeSource paid hfloor witness.terminalGap_pos
    obtain ⟨marked, halternative⟩ :=
      floorSource.exists_markedExactOrbit_alternative_of_witness witness
    exact ⟨hfloor, marked, halternative⟩
  · left
    push Not at hfloor
    obtain ⟨underfloor, hunderfloor⟩ := hfloor
    refine ⟨underfloor, ?_, hunderfloor⟩
    intro heq
    subst underfloor
    exact (not_lt_of_ge (handoff.owner_punishment_le_child_payoff)) hunderfloor

end FinFourFiniteSourceCapHandoff
end GameTheory
