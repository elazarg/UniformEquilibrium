import Research.Quitting.FinFourProducerAtlas.FinFourFullDebtCapBandTargetSplit
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ArbitraryClockMinimumActualReachPaidPort

/-!
# Full-debt off-minimum target paid port

For one supplied strict compact target, this module selects a literal target
profile from the retained family and constructs its actual-reach paid port.
It preserves the chronological source index, finite cut, unilateral update,
gain, and reach bounds.  It neither produces the minimum source nor asserts
renewal, a terminal conclusion, Nash play, or uniform equilibrium.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

/-- A strict compact target branch together with one literal retained target
profile and its actual-reach paid port. -/
structure FinFourFullDebtOffMinimumActualReachPaidPort
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (base : FinFourFullDebtCapBandTargetCompactification source M) where
  margin : ℝ
  margin_pos : 0 < margin
  targetDebt_eq_source_add_two_mul :
    quittingTerminalSemanticDebtSum base.targetPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1 + 2 * margin
  rank : ℕ
  targetDebt_ge_source_add_margin :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (base.response.targetProfile (base.refinement rank))) ≥
      quittingTerminalSemanticDebtSum source.point.1 + margin
  port : QuittingOffMinimumActualReachPaidPort reward
    base.response.chronologyProfiles
    (quittingTerminalSemanticDebtSum source.point.1) M
  port_sourceIndex_eq :
    port.sourceIndex = base.response.sourceIndex (base.refinement rank)
  port_target_eq :
    port.target = base.response.targetProfile (base.refinement rank)

namespace FinFourFullDebtOffMinimumActualReachPaidPort

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {base : FinFourFullDebtCapBandTargetCompactification source M}

/-- The paid port's source index is the retained composite chronological
index. -/
theorem chronologyProfile_at_port_sourceIndex_eq
    (result : FinFourFullDebtOffMinimumActualReachPaidPort base) :
    base.response.chronologyProfiles result.port.sourceIndex =
      base.response.sourceProfile (base.refinement result.rank) := by
  rw [result.port_sourceIndex_eq]
  exact (base.sourceProfile_eq_chronologyProfile result.rank).symm

/-- The paid port's target is the literal cap-band update at the selected
finite cut. -/
theorem port_target_eq_update
    (result : FinFourFullDebtOffMinimumActualReachPaidPort base) :
    result.port.target = Function.update
      (base.response.sourceProfile (base.refinement result.rank))
      base.response.mover
      (base.response.cutData
        (base.refinement result.rank)).targetStrategy := by
  rw [result.port_target_eq]
  exact base.targetProfile_eq_update result.rank

/-- The port target and source retain identical live roots strictly before
the selected cap-band cut. -/
theorem port_target_liveRoot_eq_source_of_lt
    (result : FinFourFullDebtOffMinimumActualReachPaidPort base)
    (time : ℕ)
    (htime : time <
      (base.response.cutData (base.refinement result.rank)).cut) :
    quittingProfileLiveRoot reward result.port.target time =
      quittingProfileLiveRoot reward
        (base.response.sourceProfile (base.refinement result.rank)) time := by
  rw [result.port_target_eq]
  exact base.response.target_liveRoot_eq_source_of_lt
    (base.refinement result.rank) time htime

/-- The cap-band gain at the selected target retains the uniform half-limit
mover-debt floor. -/
theorem half_limitingMoverDebt_le_payoffGain
    (result : FinFourFullDebtOffMinimumActualReachPaidPort base)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticDebt source.point.1 base.response.mover / 2 ≤
      quittingTerminalPayoff reward result.port.target base.response.mover -
        quittingTerminalPayoff reward
          (base.response.sourceProfile (base.refinement result.rank))
          base.response.mover := by
  rw [result.port_target_eq]
  exact base.half_limitingMoverDebt_le_payoffGain hreward result.rank

/-- The original source still reaches the selected finite cut with the
uniform cap-band joint-reach floor. -/
theorem limitingMoverDebt_div_four_mul_le_jointReach
    (result : FinFourFullDebtOffMinimumActualReachPaidPort base)
    (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticDebt source.point.1 base.response.mover /
          (4 * M) ≤
      quittingJointSurvivalWeight
        (quittingProfileLiveRoot reward
          (base.response.sourceProfile (base.refinement result.rank))) 0
        (base.response.cutData (base.refinement result.rank)).cut :=
  base.limitingMoverDebt_div_four_mul_le_jointReach
    hM hreward result.rank

end FinFourFullDebtOffMinimumActualReachPaidPort

/-- One strict compact-target alternative selects a literal member of the
retained target family and exposes its complete actual-reach paid port. -/
theorem nonempty_finFourFullDebtOffMinimumActualReachPaidPort
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (base : FinFourFullDebtCapBandTargetCompactification source M)
    (margin : ℝ) (hmargin : 0 < margin)
    (htargetDebt :
      quittingTerminalSemanticDebtSum base.targetPoint.1 =
        quittingTerminalSemanticDebtSum source.point.1 + 2 * margin)
    (heventually : ∀ᶠ rank in atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (base.response.targetProfile (base.refinement rank))) ≥
        quittingTerminalSemanticDebtSum source.point.1 + margin)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (FinFourFullDebtOffMinimumActualReachPaidPort base) := by
  obtain ⟨rank, hrank⟩ := heventually.exists
  let sourceIndex := base.response.sourceIndex (base.refinement rank)
  let target := base.response.targetProfile (base.refinement rank)
  have hancestry : IsQuittingBehaviorReplacementAncestry
      (base.response.chronologyProfiles sourceIndex) target := by
    rw [show base.response.chronologyProfiles sourceIndex =
        base.response.sourceProfile (base.refinement rank) by
      exact (base.sourceProfile_eq_chronologyProfile rank).symm]
    rw [show target = Function.update
        (base.response.sourceProfile (base.refinement rank))
        base.response.mover
        (base.response.cutData
          (base.refinement rank)).targetStrategy by
      exact base.targetProfile_eq_update rank]
    exact isQuittingBehaviorReplacementAncestry_update _ _ _
  have hoff : quittingTerminalSemanticDebtSum source.point.1 <
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward target) := by
    have hstrict : quittingTerminalSemanticDebtSum source.point.1 <
        quittingTerminalSemanticDebtSum source.point.1 + margin := by
      linarith
    exact hstrict.trans_le (by simpa only [target] using hrank)
  obtain ⟨port, hsourceIndex, htarget⟩ :=
    replacementAncestry_exists_offMinimumActualReachPaidPort
      reward base.response.chronologyProfiles
      (quittingTerminalSemanticDebtSum source.point.1) M
      source.minimumDebt_pos hreward sourceIndex target hancestry hoff
  exact ⟨{
    margin := margin
    margin_pos := hmargin
    targetDebt_eq_source_add_two_mul := htargetDebt
    rank := rank
    targetDebt_ge_source_add_margin := hrank
    port := port
    port_sourceIndex_eq := hsourceIndex
    port_target_eq := htarget
  }⟩

end GameTheory
