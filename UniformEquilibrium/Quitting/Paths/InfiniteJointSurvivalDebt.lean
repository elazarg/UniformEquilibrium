import UniformEquilibrium.Quitting.Paths.SummableRootSurvival
import UniformEquilibrium.Quitting.Root.ExactCapClockTransport

/-! # Infinite joint survival and literal cap-clock debt floor -/

noncomputable section
namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal infinite joint-survival product, defined as the infimum of
its finite chronological prefix products. -/
def quittingInfiniteJointSurvival (roots : ℕ → ι → PMF Bool) : ℝ :=
  sInf (Set.range fun horizon => ∏ time ∈ Finset.range horizon,
    quittingStationaryContinueMass (roots time))

omit [DecidableEq ι] in
theorem antitone_quittingJointSurvivalPrefix
    (roots : ℕ → ι → PMF Bool) :
    Antitone (fun horizon => ∏ time ∈ Finset.range horizon,
      quittingStationaryContinueMass (roots time)) := by
  apply antitone_nat_of_succ_le
  intro horizon
  rw [Finset.prod_range_succ]
  have hprefix : 0 ≤ ∏ time ∈ Finset.range horizon,
      quittingStationaryContinueMass (roots time) := Finset.prod_nonneg fun time _ =>
    quittingStationaryContinueMass_nonneg (roots time)
  have hfactor := quittingStationaryContinueMass_le_one (roots horizon)
  nlinarith [mul_nonneg hprefix
    (quittingStationaryContinueMass_nonneg (roots horizon))]

omit [DecidableEq ι] in
theorem tendsto_quittingJointSurvivalPrefix_infinite
    (roots : ℕ → ι → PMF Bool) :
    Tendsto (fun horizon => ∏ time ∈ Finset.range horizon,
      quittingStationaryContinueMass (roots time)) atTop
      (nhds (quittingInfiniteJointSurvival roots)) := by
  simpa [quittingInfiniteJointSurvival, sInf_range] using
    tendsto_atTop_ciInf (antitone_quittingJointSurvivalPrefix roots)
    ⟨0, fun value hvalue => by
      obtain ⟨horizon, rfl⟩ := hvalue
      exact Finset.prod_nonneg fun time _ =>
        quittingStationaryContinueMass_nonneg (roots time)⟩

omit [DecidableEq ι] in
theorem quittingInfiniteJointSurvival_le_prefix
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ) :
    quittingInfiniteJointSurvival roots ≤
      ∏ time ∈ Finset.range horizon,
        quittingStationaryContinueMass (roots time) := by
  unfold quittingInfiniteJointSurvival
  apply csInf_le
  · exact ⟨0, fun value hvalue => by
      obtain ⟨n, rfl⟩ := hvalue
      exact Finset.prod_nonneg fun time _ =>
        quittingStationaryContinueMass_nonneg (roots time)⟩
  · exact ⟨horizon, rfl⟩

/-- Summable marginal hazards and pointwise positive root survival make the
actual infinite joint-survival product strictly positive. -/
theorem quittingInfiniteJointSurvival_pos_of_summable_marginalHazard
    (roots : ℕ → ι → PMF Bool)
    (hsummable : Summable (fun time =>
      ∑ player, (roots time player true).toReal))
    (hpositive : ∀ time,
      0 < quittingStationaryContinueMass (roots time)) :
    0 < quittingInfiniteJointSurvival roots := by
  obtain ⟨lower, hlower, hprefix⟩ :=
    exists_pos_le_jointSurvivalPrefix_of_summable_marginalHazard
      roots hsummable hpositive
  apply hlower.trans_le
  unfold quittingInfiniteJointSurvival
  apply le_csInf
  · exact Set.range_nonempty _
  · rintro value ⟨horizon, rfl⟩
    exact hprefix horizon

theorem quittingJointSurvivalPrefix_le_opponentSurvivalPrefix
    (roots : ℕ → ι → PMF Bool) (owner : ι) (horizon : ℕ) :
    (∏ time ∈ Finset.range horizon,
      quittingStationaryContinueMass (roots time)) ≤
      ∏ time ∈ Finset.range horizon,
        quittingRootOpponentContinueMass (roots time) owner := by
  apply Finset.prod_le_prod
  · intro time _
    exact quittingStationaryContinueMass_nonneg (roots time)
  · intro time _
    rw [quittingStationaryContinueMass_eq_forcedContinue_mul_own]
    change quittingRootOpponentContinueMass (roots time) owner *
        (roots time owner false).toReal ≤ _
    exact mul_le_of_le_one_right
      (quittingRootOpponentContinueMass_nonneg (roots time) owner)
      (ENNReal.toReal_mono ENNReal.one_ne_top
        ((roots time owner).coe_le_one false))

/-- The literal cap-clock debt stays above the actual infinite joint-survival
constant times its initial positive debt floor. -/
theorem quitting_pureTimeCap_debt_ge_infiniteJointSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile)
    (owner : ι) {gamma : ℝ}
    (hbase : quittingTerminalPayoff reward
        (Function.update terminal owner
          (quittingPureTimeBehaviorStrategy reward owner (some 0))) owner =
      quittingContinuationBestResponseValue reward terminal owner)
    (hnash : ∀ n, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward
        (quittingReversePrefixProfile reward roots (fun _ => terminal) n) player)
      0 (roots n))
    (hcontinue : ∀ n, 0 < (roots n owner false).toReal)
    (hgamma : gamma ≤
      quittingTerminalDeviationDebt reward terminal owner) (hgamma0 : 0 ≤ gamma) :
    ∀ horizon, quittingInfiniteJointSurvival roots * gamma ≤
      quittingTerminalDeviationDebt reward
        (quittingReversePrefixProfile reward roots (fun _ => terminal) horizon)
        owner := by
  intro horizon
  have hclock := quitting_pureTimeCap_literalPrefix_transport
    reward roots terminal owner hbase hnash hcontinue horizon
  rw [hclock.2.1]
  have hinfinite := quittingInfiniteJointSurvival_le_prefix roots horizon
  have hopponent :=
    quittingJointSurvivalPrefix_le_opponentSurvivalPrefix roots owner horizon
  have hopponent0 : 0 ≤ ∏ time ∈ Finset.range horizon,
      quittingRootOpponentContinueMass (roots time) owner :=
    Finset.prod_nonneg fun time _ =>
      quittingRootOpponentContinueMass_nonneg (roots time) owner
  have hprefix0 : 0 ≤ ∏ time ∈ Finset.range horizon,
      quittingStationaryContinueMass (roots time) :=
    Finset.prod_nonneg fun time _ =>
      quittingStationaryContinueMass_nonneg (roots time)
  exact (mul_le_mul hinfinite hgamma hgamma0 hprefix0).trans
    (mul_le_mul hopponent le_rfl
      (quittingTerminalDeviationDebt_nonneg reward terminal owner) hopponent0)

end GameTheory
