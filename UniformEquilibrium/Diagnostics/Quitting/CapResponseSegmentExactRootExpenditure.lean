import UniformEquilibrium.Diagnostics.Quitting.CapResponseSegmentCollar
import UniformEquilibrium.Diagnostics.Quitting.FirstExactRootDebtDescent

/-!
# Every exact root at a proper cap-segment point spends a fixed amount

Actual cap-attaining responses give affine owner debt along their private
installation segment. A fixed proper segment point inherits a positive debt
floor and the original singleton cap limit. The resulting expenditure and
absorption bounds hold for every exact root at every sufficiently late index.
No minimum-debt hypothesis, stationary realization, or attained cap at the
newly prefixed profile is asserted or required.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The packet's bounds at installation parameter `t`, with surviving debt
floor `(1 - t) * gamma`, uniformly over all late exact product roots. -/
theorem eventually_capResponseSegment_exactRoot_debtDrop_and_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile) (owner : ι)
    (responses : ℕ → (quittingGame reward).BehaviorStrategy owner)
    (hattains : ∀ index,
      quittingTerminalPayoff reward (Function.update (profiles index) owner
          (responses index)) owner =
        quittingContinuationBestResponseValue reward (profiles index) owner)
    (parameter : Set.Icc (0 : ℝ) 1) (hproper : parameter.val < 1)
    {M gamma : ℝ} (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hdebt : ∀ index, gamma ≤ quittingTerminalDeviationDebt reward (profiles index) owner)
    (hcap : Tendsto (fun index =>
      quittingContinuationBestResponseValue reward (profiles index) owner) atTop
        (nhds (reward (quittingSingletonTerminal owner) owner))) :
    let floor := (1 - parameter.val) * gamma
    ∀ᶠ index in atTop, ∀ root : ι → PMF Bool,
      let pair := quittingTerminalSemanticPair reward
        (quittingCapResponseSegment reward (profiles index) owner (responses index) parameter)
      IsεQuittingRootNash reward pair.1 0 root →
        min (floor / 2) (floor ^ 2 / (16 * M)) ≤
            quittingTerminalSemanticDebtSum pair -
              quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPrefix reward root pair) ∧
          min 1 (floor / (16 * M)) ≤ quittingRootAbsorptionMass root := by
  let segments := fun index => quittingCapResponseSegment reward (profiles index) owner
    (responses index) parameter
  let pairs := fun index => quittingTerminalSemanticPair reward (segments index)
  let floor := (1 - parameter.val) * gamma
  have hfloor : 0 < floor := mul_pos (sub_pos.mpr hproper) hgamma
  have hsegmentDebt : ∀ index, floor ≤ quittingTerminalSemanticDebt (pairs index) owner := by
    intro index
    change floor ≤ quittingTerminalDeviationDebt reward (segments index) owner
    rw [capResponseSegment_ownerDebt_eq_oneSub_mul reward (profiles index) owner
      (responses index) (hattains index) parameter]
    exact mul_le_mul_of_nonneg_left (hdebt index) (sub_nonneg.mpr parameter.property.2)
  have hsegmentCap : Tendsto (fun index => (pairs index).2 owner) atTop
      (nhds (reward (quittingSingletonTerminal owner) owner)) := by
    simpa only [pairs, segments, quittingTerminalSemanticPair,
      capResponseSegment_ownerCap_eq] using hcap
  have hvalue : ∀ index, |(pairs index).1 owner| ≤ M :=
    fun index => abs_quittingTerminalPayoff_le reward (segments index) owner hreward
  have hnonneg : ∀ index who, 0 ≤ quittingTerminalSemanticDebt (pairs index) who :=
    fun index who => quittingTerminalDeviationDebt_nonneg reward (segments index) who
  have hdrop := eventually_fixedCapLimit_totalDebtDrop reward pairs owner
    hM hfloor hreward hvalue hnonneg hsegmentDebt hsegmentCap
  have habsorption := eventually_fixedCapLimit_exactRoot_absorptionMass_lowerBound
    reward pairs owner hM hfloor hreward hvalue hsegmentDebt hsegmentCap
  filter_upwards [hdrop, habsorption] with index hdropIndex habsorptionIndex
  intro root
  dsimp only
  intro hnash
  exact ⟨hdropIndex root hnash, habsorptionIndex root hnash⟩

end GameTheory
