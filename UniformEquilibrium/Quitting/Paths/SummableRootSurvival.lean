import MathUE.SummableChargeSurvival
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-! # Joint-survival bounds from summable marginal Quit hazards -/

noncomputable section

open scoped Topology

namespace GameTheory

open Filter

/-- Summable marginal hazards make every sufficiently late finite joint
survival window uniformly near one. -/
theorem eventually_one_sub_le_jointSurvivalWindow_of_summable_marginalHazard
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (roots : ℕ → ι → PMF Bool)
    (hsummable : Summable (fun time =>
      ∑ player, (roots time player true).toReal))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ start in atTop, ∀ fuel,
      1 - ε ≤ ∏ offset ∈ Finset.range fuel,
        quittingStationaryContinueMass (roots (start + offset)) := by
  let charge := fun time => quittingRootAbsorptionMass (roots time)
  have hcharge0 : ∀ n, 0 ≤ charge n := fun n =>
    quittingRootAbsorptionMass_nonneg (roots n)
  have hcharge1 : ∀ n, charge n ≤ 1 := by
    intro n
    dsimp [charge, quittingRootAbsorptionMass]
    linarith [quittingStationaryContinueMass_nonneg (roots n)]
  have hchargeSummable : Summable charge := by
    apply Summable.of_nonneg_of_le hcharge0
      (fun n => quittingRootAbsorptionMass_le_sum_quitProbability (roots n))
      hsummable
  have hwindow :=
    Math.eventually_one_sub_le_finiteSurvivalWindow_of_summable
      charge hcharge0 hcharge1 hchargeSummable hε
  filter_upwards [hwindow] with start hstart
  intro fuel
  simpa [charge, quittingRootAbsorptionMass] using hstart fuel

/-- Positive joint survival at every root strengthens summable marginal
hazards to one positive lower bound on every joint-survival prefix. -/
theorem exists_pos_le_jointSurvivalPrefix_of_summable_marginalHazard
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (roots : ℕ → ι → PMF Bool)
    (hsummable : Summable (fun time =>
      ∑ player, (roots time player true).toReal))
    (hpositive : ∀ time, 0 < quittingStationaryContinueMass (roots time)) :
    ∃ lower, 0 < lower ∧ ∀ horizon,
      lower ≤ ∏ time ∈ Finset.range horizon,
        quittingStationaryContinueMass (roots time) := by
  let charge := fun time => quittingRootAbsorptionMass (roots time)
  have hcharge0 : ∀ n, 0 ≤ charge n := fun n =>
    quittingRootAbsorptionMass_nonneg (roots n)
  have hcharge1 : ∀ n, charge n < 1 := by
    intro n
    dsimp [charge, quittingRootAbsorptionMass]
    linarith [hpositive n]
  have hchargeSummable : Summable charge := by
    apply Summable.of_nonneg_of_le hcharge0
      (fun n => quittingRootAbsorptionMass_le_sum_quitProbability (roots n))
      hsummable
  simpa [charge, quittingRootAbsorptionMass] using
    Math.exists_pos_le_prod_one_sub_of_summable
      charge hcharge0 hcharge1 hchargeSummable

/-- Without pointwise positivity, summable marginal hazards still allow only
finitely many roots with zero joint survival. -/
theorem eventually_jointSurvival_pos_of_summable_marginalHazard
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (roots : ℕ → ι → PMF Bool)
    (hsummable : Summable (fun time =>
      ∑ player, (roots time player true).toReal)) :
    ∀ᶠ time in atTop, 0 < quittingStationaryContinueMass (roots time) := by
  have htendsto := hsummable.tendsto_atTop_zero
  filter_upwards [htendsto.eventually (Iio_mem_nhds zero_lt_one)] with time htime
  have habsorption :=
    quittingRootAbsorptionMass_le_sum_quitProbability (roots time)
  have hjoint0 := quittingStationaryContinueMass_nonneg (roots time)
  unfold quittingRootAbsorptionMass at habsorption
  linarith

/-- Every fixed marginal hazard is summable when the total marginal hazard is. -/
theorem summable_coordinateHazard_of_summable_marginalHazard
    {ι : Type} [Fintype ι] (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hhazard : Summable (fun time =>
      ∑ player, (roots time player true).toReal)) :
    Summable (fun time => (roots time owner true).toReal) := by
  apply Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg)
    (fun time => Finset.single_le_sum
      (fun player _ => ENNReal.toReal_nonneg) (Finset.mem_univ owner))
    hhazard

/-- Absorption after forcing one coordinate to Continue is summable under
summable total marginal hazard. -/
theorem summable_forcedContinue_absorption_of_summable_marginalHazard
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hhazard : Summable (fun time =>
      ∑ player, (roots time player true).toReal)) :
    Summable (fun time => quittingRootAbsorptionMass
      (Function.update (roots time) owner (PMF.pure false))) := by
  apply Summable.of_nonneg_of_le
    (fun time => quittingRootAbsorptionMass_nonneg _)
    (fun time => ?_) hhazard
  refine (quittingRootAbsorptionMass_le_sum_quitProbability _).trans ?_
  apply Finset.sum_le_sum
  intro player _
  by_cases hplayer : player = owner
  · subst player
    simp
  · rw [Function.update_of_ne hplayer]

/-- Summable total marginal hazards force every forced-Continue opponent
survival coefficient to one, including the forced owner's coefficient. -/
theorem tendsto_forcedContinue_opponentSurvival_one_of_summable_marginalHazard
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (roots : ℕ → ι → PMF Bool) (owner who : ι)
    (hhazard : Summable (fun time =>
      ∑ player, (roots time player true).toReal)) :
    Tendsto (fun time => quittingRootOpponentContinueMass
        (Function.update (roots time) owner (PMF.pure false)) who)
      atTop (nhds 1) := by
  have hlower : ∀ time, 1 - (∑ player, (roots time player true).toReal) ≤
      quittingRootOpponentContinueMass
        (Function.update (roots time) owner (PMF.pure false)) who := by
    intro time
    have habsorption :=
      quittingRootAbsorptionMass_le_sum_quitProbability (roots time)
    have howner :=
      quittingStationaryContinueMass_le_update_pure_false (roots time) owner
    have hwho := quittingStationaryContinueMass_le_update_pure_false
      (Function.update (roots time) owner (PMF.pure false)) who
    unfold quittingRootAbsorptionMass at habsorption
    unfold quittingRootOpponentContinueMass
    linarith
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hlow := hone.sub hhazard.tendsto_atTop_zero
  simp only [sub_zero] at hlow
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hone hlower
    (fun time => quittingRootOpponentContinueMass_le_one _ _)

end GameTheory
