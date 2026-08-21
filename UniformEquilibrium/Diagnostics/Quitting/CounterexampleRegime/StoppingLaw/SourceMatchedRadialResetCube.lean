/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.SourceMatchedRadialScaling
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawResetCube

/-!
# Radially scaled source-matched stopping-law reset cubes

A flat charged circulation supplies one legal radial coefficient for every
active player.  This file places those coefficients in one literal reset cube
at the common frontier source.  Every frozen active edge is exactly the
frontier reset scale times the corresponding radial debt direction.

Consequently, the whole frozen cube star is asymptotically balanced after
normalization by the frontier scale, while its mover-diagonal charge converges
to a strictly positive number.  This is a simultaneous-profile realization
of the charged star.  It does not assert that the cube path is a chronological
quitting-game prefix.
-/

noncomputable section

namespace GameTheory

open Filter Finset Math.Finset.CubicalResetIntegrability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleStoppingLawFrontier

/-- Extend the active inner resets by the unchanged source strategies. -/
def sourceMatchedRadialCubeTarget
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (who : ι) :
    (quittingGame reward).BehaviorStrategy who :=
  if hwho : who ∈ frontier.active then
    frontier.sourceMatchedInnerResetStrategy rank ⟨who, hwho⟩
  else
    frontier.profiles (frontier.subseq rank) who

/-- Extend radial coefficients by zero on inactive players. -/
def sourceMatchedRadialCubeScale
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (weight : {who // who ∈ frontier.active} → ℝ) (who : ι) : ℝ :=
  if hwho : who ∈ frontier.active then weight ⟨who, hwho⟩ else 0

@[simp]
theorem sourceMatchedRadialCubeTarget_active
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (mover : {who // who ∈ frontier.active}) :
    frontier.sourceMatchedRadialCubeTarget rank mover.1 =
      frontier.sourceMatchedInnerResetStrategy rank mover := by
  simp [sourceMatchedRadialCubeTarget, mover.property]

@[simp]
theorem sourceMatchedRadialCubeScale_active
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (weight : {who // who ∈ frontier.active} → ℝ)
    (mover : {who // who ∈ frontier.active}) :
    frontier.sourceMatchedRadialCubeScale weight mover.1 = weight mover := by
  simp [sourceMatchedRadialCubeScale, mover.property]

/-- One variable-scale reset cube containing all radially scaled active
frontier columns. -/
def sourceMatchedRadialResetCubeData
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1) :
    QuittingStoppingLawResetCubeData reward where
  source := frontier.profiles (frontier.subseq rank)
  target := frontier.sourceMatchedRadialCubeTarget rank
  scale := frontier.sourceMatchedRadialCubeScale weight
  scale_nonneg := by
    intro who
    by_cases hwho : who ∈ frontier.active
    · simpa [sourceMatchedRadialCubeScale, hwho] using hweight0 ⟨who, hwho⟩
    · simp [sourceMatchedRadialCubeScale, hwho]
  scale_le_one := by
    intro who
    by_cases hwho : who ∈ frontier.active
    · simpa [sourceMatchedRadialCubeScale, hwho] using hweight1 ⟨who, hwho⟩
    · simp [sourceMatchedRadialCubeScale, hwho]

@[simp]
theorem sourceMatchedRadialResetCubeData_profile_empty
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1) :
    (frontier.sourceMatchedRadialResetCubeData rank weight hweight0 hweight1).profile ∅ =
      frontier.profiles (frontier.subseq rank) := by
  funext who
  simp [QuittingStoppingLawResetCubeData.profile,
    sourceMatchedRadialResetCubeData]

/-- Every active singleton vertex is exactly its literal radial reset. -/
theorem sourceMatchedRadialResetCubeData_profile_singleton
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (mover : {who // who ∈ frontier.active}) :
    (frontier.sourceMatchedRadialResetCubeData rank weight hweight0 hweight1).profile
        {mover.1} =
      frontier.sourceMatchedRadialResetProfile rank mover (weight mover)
        (hweight0 mover) (hweight1 mover) := by
  let data := frontier.sourceMatchedRadialResetCubeData rank weight
    hweight0 hweight1
  change data.profile {mover.1} = _
  funext observer
  by_cases hobserver : observer = mover.1
  · subst observer
    rw [data.profile_apply_of_mem {mover.1} mover.1 (by simp)]
    simp only [sourceMatchedRadialResetProfile, Function.update_self]
    have htarget : data.target mover.1 =
        frontier.sourceMatchedInnerResetStrategy rank mover := by
      exact frontier.sourceMatchedRadialCubeTarget_active rank mover
    have hscale : data.scale mover.1 = weight mover := by
      exact frontier.sourceMatchedRadialCubeScale_active weight mover
    have hsource : data.source mover.1 =
        frontier.profiles (frontier.subseq rank) mover.1 := rfl
    rw [htarget, hsource]
    simpa only using
      quittingStoppingLawMixtureBehaviorStrategy_congr_scale reward mover.1
        (frontier.profiles (frontier.subseq rank) mover.1)
        (frontier.sourceMatchedInnerResetStrategy rank mover)
        (data.scale mover.1) (weight mover) (data.scale_nonneg mover.1)
        (data.scale_le_one mover.1) hscale
  · rw [data.profile_apply_of_not_mem {mover.1} observer (by simpa)]
    simp [data, sourceMatchedRadialResetCubeData,
      sourceMatchedRadialResetProfile, hobserver]

/-- A frozen active cube edge divided by the positive frontier scale is
exactly its normalized radial debt direction. -/
theorem sourceMatchedRadialResetCubeData_debtEdge_div_eq_radialDirection
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (mover : {who // who ∈ frontier.active}) (observer : ι) :
    let data := frontier.sourceMatchedRadialResetCubeData rank weight
      hweight0 hweight1
    let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward candidate) observer
    edge (data.value debt) ∅ mover.1 /
        frontier.lambda (frontier.subseq rank) =
      frontier.sourceMatchedRadialDebtDirection rank mover (weight mover)
        (hweight0 mover) (hweight1 mover) observer := by
  dsimp only
  rw [edge]
  change
    (quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            ((frontier.sourceMatchedRadialResetCubeData rank weight
              hweight0 hweight1).profile {mover.1})) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            ((frontier.sourceMatchedRadialResetCubeData rank weight
              hweight0 hweight1).profile ∅)) observer) /
      frontier.lambda (frontier.subseq rank) = _
  rw [frontier.sourceMatchedRadialResetCubeData_profile_singleton,
    frontier.sourceMatchedRadialResetCubeData_profile_empty]
  rfl

/-- The normalized frozen active star is exactly the sum of the normalized
radial debt directions. -/
theorem sum_sourceMatchedRadialResetCubeData_debtEdge_div_eq
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1) (observer : ι) :
    let data := frontier.sourceMatchedRadialResetCubeData rank weight
      hweight0 hweight1
    let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward candidate) observer
    (∑ mover : {who // who ∈ frontier.active},
      edge (data.value debt) ∅ mover.1) /
        frontier.lambda (frontier.subseq rank) =
      ∑ mover, frontier.sourceMatchedRadialDebtDirection rank mover
        (weight mover) (hweight0 mover) (hweight1 mover) observer := by
  dsimp only
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro mover _moverMem
  exact frontier.sourceMatchedRadialResetCubeData_debtEdge_div_eq_radialDirection
    rank weight hweight0 hweight1 mover observer

/-- Listing every active player once turns the cubical frozen-edge sum into
the active-subtype star. -/
theorem frozenEdgeSum_sourceMatchedRadialResetCubeData_eq_sum
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observable : (quittingGame reward).BehaviorProfile → ℝ) :
    let data := frontier.sourceMatchedRadialResetCubeData rank weight
      hweight0 hweight1
    frozenEdgeSum (data.value observable) ∅ frontier.active.toList =
      ∑ mover : {who // who ∈ frontier.active},
        edge (data.value observable) ∅ mover.1 := by
  dsimp only
  rw [frozenEdgeSum,
    ← List.sum_toFinset _ frontier.active.nodup_toList]
  simp only [Finset.toList_toFinset]
  rw [← Finset.sum_attach, Finset.attach_eq_univ]

/-- The normalized frozen edge sum along the active reset word is exactly the
sum of normalized radial debt directions. -/
theorem frozenEdgeSum_sourceMatchedRadialResetCubeData_debt_div_eq
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1) (observer : ι) :
    let data := frontier.sourceMatchedRadialResetCubeData rank weight
      hweight0 hweight1
    let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward candidate) observer
    frozenEdgeSum (data.value debt) ∅ frontier.active.toList /
        frontier.lambda (frontier.subseq rank) =
      ∑ mover, frontier.sourceMatchedRadialDebtDirection rank mover
        (weight mover) (hweight0 mover) (hweight1 mover) observer := by
  dsimp only
  rw [frontier.frozenEdgeSum_sourceMatchedRadialResetCubeData_eq_sum]
  exact frontier.sum_sourceMatchedRadialResetCubeData_debtEdge_div_eq
    rank weight hweight0 hweight1 observer

/-- **A flat charged circulation is one asymptotically balanced literal
variable-scale reset cube.**

There is one cube coordinate per active player.  The normalized frozen debt
star converges coordinatewise to zero, while the normalized mover-diagonal
charge converges to a strictly positive limit. -/
theorem exists_boundedRadialSourceMatchedResetCube
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (hflat : ∀ mover, ∑ observer, frontier.tangent mover observer = 0)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.active frontier.tangent) :
    ∃ weight : {who // who ∈ frontier.active} → ℝ,
      ∃ hweight0 : ∀ mover, 0 ≤ weight mover,
      ∃ hweight1 : ∀ mover, weight mover ≤ 1,
      ∃ charge : ℝ, 0 < charge ∧
        (∀ observer,
          Tendsto (fun rank =>
            let data := frontier.sourceMatchedRadialResetCubeData rank weight
              hweight0 hweight1
            let debt := fun candidate :
                (quittingGame reward).BehaviorProfile ↦
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward candidate) observer
            frozenEdgeSum (data.value debt) ∅ frontier.active.toList /
              frontier.lambda (frontier.subseq rank))
            atTop (nhds 0)) ∧
        Tendsto (fun rank =>
          ∑ mover : {who // who ∈ frontier.active},
            -(let data := frontier.sourceMatchedRadialResetCubeData rank weight
                hweight0 hweight1
              let debt := fun candidate :
                  (quittingGame reward).BehaviorProfile ↦
                quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward candidate) mover.1
              edge (data.value debt) ∅ mover.1 /
                frontier.lambda (frontier.subseq rank)))
          atTop (nhds charge) := by
  obtain ⟨weight, hweight0, hweight1, hbalance, charge, hcharge, hchargeLimit⟩ :=
    frontier.exists_boundedRadialSourceMatchedCirculation hflat hcirculation
  refine ⟨weight, hweight0, hweight1, charge, hcharge, ?_, ?_⟩
  · intro observer
    convert hbalance observer using 1
    funext rank
    exact frontier.frozenEdgeSum_sourceMatchedRadialResetCubeData_debt_div_eq
      rank weight hweight0 hweight1 observer
  · convert hchargeLimit using 1
    funext rank
    apply Finset.sum_congr rfl
    intro mover _moverMem
    rw [frontier.sourceMatchedRadialResetCubeData_debtEdge_div_eq_radialDirection]

end QuittingCounterexampleStoppingLawFrontier
end GameTheory
