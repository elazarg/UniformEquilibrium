import UniformEquilibrium.Diagnostics.Quitting.FirstExactRootStationaryDichotomy
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinitePureTimeResetArrival
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualProfileTerminalGapPaidCap
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualReachPaidFirstDisagreement

/-! # Literal finite-source cap handoff from the vanishing-survival branch -/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction

/-- One actual finite descendant retained from the full vanishing-survival branch.
The tail, new root, prefixed source, shifted stationary cap endpoint, and child
remain definitionally attached to the branch's common subsequence. -/
structure FinFourFiniteSourceCapHandoff
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {source : StationaryQuitNowCapPinSource reward}
    {roots : ℕ → Fin 4 → PMF Bool} {minimum gap : ℝ}
    (branch : FirstStationaryRootZeroBranch source roots minimum gap)
    (index : ℕ) where
  source_debt_floor : minimum / 2 ≤
    quittingTerminalDeviationDebt reward
      (quittingRootThenContinuationProfile reward (roots (branch.select index))
        (source.profile (branch.select index))) branch.owner
  cap_attained : quittingTerminalPayoff reward
      (Function.update
        (quittingRootThenContinuationProfile reward (roots (branch.select index))
          (source.profile (branch.select index))) branch.owner
        (quittingPureTimeBehaviorStrategy reward branch.owner
          (branch.endpoint.map Nat.succ))) branch.owner =
    quittingContinuationBestResponseValue reward
      (quittingRootThenContinuationProfile reward (roots (branch.select index))
        (source.profile (branch.select index))) branch.owner

namespace FinFourFiniteSourceCapHandoff

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {source : StationaryQuitNowCapPinSource reward}
variable {roots : ℕ → Fin 4 → PMF Bool} {minimum gap : ℝ}
variable {branch : FirstStationaryRootZeroBranch source roots minimum gap}
variable {index : ℕ}

def tail (_handoff : FinFourFiniteSourceCapHandoff branch index) :
    (quittingGame reward).BehaviorProfile := source.profile (branch.select index)

def root (_ : FinFourFiniteSourceCapHandoff branch index) : Fin 4 → PMF Bool :=
  roots (branch.select index)

def prefixed (handoff : FinFourFiniteSourceCapHandoff branch index) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward handoff.root handoff.tail

def response (_ : FinFourFiniteSourceCapHandoff branch index) :
    (quittingGame reward).BehaviorStrategy branch.owner :=
  quittingPureTimeBehaviorStrategy reward branch.owner (branch.endpoint.map Nat.succ)

def child (handoff : FinFourFiniteSourceCapHandoff branch index) :
    (quittingGame reward).BehaviorProfile :=
  Function.update handoff.prefixed branch.owner handoff.response

def capStep (handoff : FinFourFiniteSourceCapHandoff branch index) :
    QuittingExactPureTimeCapStep reward (minimum / 2) handoff.prefixed branch.owner := {
  quitTime := branch.endpoint.map Nat.succ
  target := handoff.child
  target_eq := rfl
  source_debt_floor := handoff.source_debt_floor
  cap_attained := handoff.cap_attained }

/-- The child gains exactly the literal source debt, hence at least half the
branch debt floor. -/
theorem payoff_gain_eq_source_debt
    (handoff : FinFourFiniteSourceCapHandoff branch index) :
    quittingTerminalPayoff reward handoff.child branch.owner -
        quittingTerminalPayoff reward handoff.prefixed branch.owner =
      quittingTerminalDeviationDebt reward handoff.prefixed branch.owner := by
  exact handoff.capStep.payoff_gain_eq_source_debt

theorem half_minimum_le_payoff_gain
    (handoff : FinFourFiniteSourceCapHandoff branch index) :
    minimum / 2 ≤ quittingTerminalPayoff reward handoff.child branch.owner -
      quittingTerminalPayoff reward handoff.prefixed branch.owner :=
  handoff.capStep.gap_le_payoff_gain

/-- The complete-cap update kills the owner's actual semantic debt exactly. -/
theorem child_owner_debt_eq_zero
    (handoff : FinFourFiniteSourceCapHandoff branch index) :
    quittingTerminalDeviationDebt reward handoff.child branch.owner = 0 := by
  change quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward handoff.child) branch.owner = 0
  exact handoff.capStep.target_reset

end FinFourFiniteSourceCapHandoff

/-- The vanishing-survival branch constructs the literal finite handoff eventually;
cap attainment is not supplied again as an independent hypothesis. -/
theorem FirstStationaryRootZeroBranch.nonempty_finiteSourceCapHandoff
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {source : StationaryQuitNowCapPinSource reward}
    {roots : ℕ → Fin 4 → PMF Bool} {minimum gap : ℝ}
    (branch : FirstStationaryRootZeroBranch source roots minimum gap) :
    ∀ᶠ index in atTop, Nonempty (FinFourFiniteSourceCapHandoff branch index) := by
  filter_upwards [branch.owner_debt_floor, branch.finite_cap] with index hdebt hfinite
  refine ⟨{
    source_debt_floor := ?_
    cap_attained := ?_ }⟩
  · simpa using hdebt
  · simpa using hfinite.2

/-- One common terminal-gap observer together with its behavioral witness,
full-gap supported pure-time row, and (possibly different) actual-reach row. -/
structure FinFourFiniteSourceCapHandoff.PaidRows
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {source : StationaryQuitNowCapPinSource reward}
    {roots : ℕ → Fin 4 → PMF Bool} {minimum gap : ℝ}
    {branch : FirstStationaryRootZeroBranch source roots minimum gap}
    {index : ℕ} (handoff : FinFourFiniteSourceCapHandoff branch index)
    (terminalGap bound : ℝ) where
  observer : Fin 4
  observer_ne_owner : observer ≠ branch.owner
  deviation : (quittingGame reward).BehaviorStrategy observer
  deviation_gain : terminalGap ≤ quittingTerminalPayoff reward
      (Function.update handoff.child observer deviation) observer -
    quittingTerminalPayoff reward handoff.child observer
  debt_floor : terminalGap ≤ quittingTerminalDeviationDebt reward handoff.child observer
  sourceWitness : Option ℕ
  receivingWitness : Option ℕ
  sourceWitness_mem : sourceWitness ∈
    (quittingBehaviorStoppingLaw reward (handoff.child observer)).support
  receivingWitness_mem : receivingWitness ∈
    (quittingBehaviorStoppingLaw reward deviation).support
  fullGapRow : QuittingPaidFirstDisagreementRow reward handoff.child observer terminalGap
  fullGapRow_source_eq : fullGapRow.sourceWitness = sourceWitness
  fullGapRow_receiving_eq : fullGapRow.receivingWitness = receivingWitness
  actualReachRow : QuittingPaidFirstDisagreementRow reward handoff.child observer (terminalGap / 4)
  ownSurvival_bound : terminalGap ≤ 4 * bound * quittingHazardSurvival
    (quittingBehaviorLiveHazard reward (handoff.child observer)) actualReachRow.start
  opponentLiveMass_bound : terminalGap ≤ 8 * bound * actualReachRow.liveMass
  actualReach_source_supported :
    (∃ n, actualReachRow.sourceWitness = some n ∧
      0 < quittingHazardStopMass
        (quittingBehaviorLiveHazard reward (handoff.child observer)) n) ∨
    (actualReachRow.sourceWitness = none ∧
      0 < quittingHazardNeverMass
        (quittingBehaviorLiveHazard reward (handoff.child observer)))

namespace FinFourFiniteSourceCapHandoff

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {source : StationaryQuitNowCapPinSource reward}
variable {roots : ℕ → Fin 4 → PMF Bool} {minimum gap : ℝ}
variable {branch : FirstStationaryRootZeroBranch source roots minimum gap}
variable {index : ℕ}

/-- The terminal-gap observer is selected once; both paid-row constructions
remain attached to that same observer at the literal finite child. -/
theorem exists_distinctTerminalGapPaidRows
    (handoff : FinFourFiniteSourceCapHandoff branch index)
    {terminalGap bound : ℝ} (hgapPos : 0 < terminalGap)
    (exploit : HasTerminalExploitabilityGap reward terminalGap)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    Nonempty (handoff.PaidRows terminalGap bound) := by
  obtain ⟨observer, deviation, hdeviation, sourceWitness, receivingWitness,
      hsource, hreceiving, hgap⟩ :=
    exploit.exists_supported_pureTimePayoff_sub_at_with_gain handoff.child
  have hdebt : terminalGap ≤ quittingTerminalDeviationDebt reward handoff.child observer := by
    unfold quittingTerminalDeviationDebt
    have hcap := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward handoff.child observer deviation
    linarith
  have hne : observer ≠ branch.owner := by
    intro heq
    subst observer
    rw [handoff.child_owner_debt_eq_zero] at hdebt
    linarith
  obtain ⟨fullRow, hfullSource, hfullReceiving⟩ :=
    exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub reward handoff.child
      observer sourceWitness receivingWitness terminalGap hgapPos hgap
  obtain ⟨reachRow, hown, hlive, hsupported⟩ :=
    positiveDebt_exists_actualReach_paidRow_withSupport reward handoff.child observer
      bound terminalGap hreward hgapPos hdebt
  exact ⟨{
    observer := observer
    observer_ne_owner := hne
    deviation := deviation
    deviation_gain := hdeviation
    debt_floor := hdebt
    sourceWitness := sourceWitness
    receivingWitness := receivingWitness
    sourceWitness_mem := hsource
    receivingWitness_mem := hreceiving
    fullGapRow := fullRow
    fullGapRow_source_eq := hfullSource
    fullGapRow_receiving_eq := hfullReceiving
    actualReachRow := reachRow
    ownSurvival_bound := hown
    opponentLiveMass_bound := hlive
    actualReach_source_supported := hsupported }⟩

end FinFourFiniteSourceCapHandoff

end GameTheory
