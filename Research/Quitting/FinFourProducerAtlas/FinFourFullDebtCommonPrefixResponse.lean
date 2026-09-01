import Research.Quitting.FinFourProducerAtlas.FinFourFullDebtFixedWeightChordCompactification
import Research.Quitting.ExactPrefixAtomTransport
import Research.Quitting.SourceFaithfulMinimumLawCausalization
import UniformEquilibrium.Quitting.Root.CommonPrefixCapStability

/-!
# Common cap--Nash prefixes for a fixed minimum response chord

At every row of an actual fixed-weight response chord, this module selects a
finite exact cap--Nash word whose length tends to infinity.  The same word is
placed before the source, chord, and target tails.  Exact cap--Nash debt
scaling applies to the chord-prefixed row, while common-prefix cancellation
transports the literal chord-to-target response edge.

This is a supplied-source compiler.  The roots are selected against the
actual chord tail at each row.  No root is claimed exact against the source
or target tail, and no regeneration, renewal, chronology, Nash, or uniform
equilibrium conclusion is asserted.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

/-- A finite exact cap--Nash word, of increasing positive length, selected
against every actual chord row. -/
structure FinFourFullDebtCommonPrefixResponse
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {base : FinFourFullDebtCapBandTargetCompactification source M}
    {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    (compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1) where
  roots : ℕ → List (Fin 4 → PMF Bool)
  roots_length : ∀ rank, (roots rank).length = rank + 1
  roots_capNash : ∀ rank, IsQuittingCapNashRootStack reward (roots rank)
    (base.fixedWeightChordProfile weight hweight0.le hweight1.le
      (compactification.refinement rank))

namespace FinFourFullDebtCommonPrefixResponse

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {base : FinFourFullDebtCapBandTargetCompactification source M}
  {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
  {compactification : FinFourFullDebtFixedWeightChordCompactification
    base minimumTarget weight hweight0 hweight1}

/-- Literal source tail at one final compactification row. -/
def sourceTail (_data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  base.response.sourceProfile
    (base.refinement (compactification.refinement rank))

/-- Actual fixed-weight chord tail at one final compactification row. -/
def chordTail (_data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  base.fixedWeightChordProfile weight hweight0.le hweight1.le
    (compactification.refinement rank)

/-- Literal cap-band target tail at one final compactification row. -/
def targetTail (_data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  base.response.targetProfile
    (base.refinement (compactification.refinement rank))

/-- Joint survival of the selected exact cap--Nash word. -/
def survival (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) : ℝ :=
  quittingCapNashStackContinueProduct (data.roots rank)

/-- The source tail behind the selected common word. -/
def sourcePrefixedProfile
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward (data.roots rank)
    (data.sourceTail rank)

/-- The actual chord tail behind the exact cap--Nash word selected against
that tail. -/
def chordPrefixedProfile
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward (data.roots rank)
    (data.chordTail rank)

/-- The target tail behind the same selected word. -/
def targetPrefixedProfile
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward (data.roots rank)
    (data.targetTail rank)

/-- A common literal word preserves equality of one player's complete tail
strategy. -/
theorem quittingLiteralRootStackProfile_apply_eq_of_tail
    (roots : List (Fin 4 → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile) (who : Fin 4)
    (htail : first who = second who) :
    quittingLiteralRootStackProfile reward roots first who =
      quittingLiteralRootStackProfile reward roots second who := by
  induction roots with
  | nil => simpa
  | cons root roots ih =>
      simp only [quittingLiteralRootStackProfile_cons]
      funext time history
      cases time with
      | zero => rfl
      | succ time =>
          exact congrFun (congrFun ih time) _

/-- The source, chord, and target prefixes preserve their literal
chronological source index and selected cap-band cut. -/
theorem sourceTail_eq_chronologyProfile
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    data.sourceTail rank =
      base.response.chronologyProfiles
        (base.response.sourceIndex
          (base.refinement (compactification.refinement rank))) := rfl

/-- The selected target tail remains the literal update of the retained
source tail. -/
theorem targetTail_eq_update
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    data.targetTail rank = Function.update (data.sourceTail rank)
      base.response.mover
      (base.response.cutData
        (base.refinement (compactification.refinement rank))).targetStrategy := rfl

/-- Opponents have the same complete strategy in the source, chord, and
target tails. -/
theorem targetTail_eq_chordTail_of_ne
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) (other : Fin 4) (hne : other ≠ base.response.mover) :
    data.targetTail rank other = data.chordTail rank other := by
  rw [targetTail, chordTail]
  unfold FinFourFullDebtCapBandTargetCompactification.fixedWeightChordProfile
  unfold quittingResponseChordProfile
  rw [Function.update_of_ne hne]
  exact base.targetProfile_eq_sourceProfile_of_ne
    (compactification.refinement rank) other hne

/-- The common prefix preserves the literal opponent agreement of the chord
and target endpoints. -/
theorem targetPrefixedProfile_eq_chordPrefixedProfile_of_ne
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) (other : Fin 4) (hne : other ≠ base.response.mover) :
    data.targetPrefixedProfile rank other =
      data.chordPrefixedProfile rank other := by
  exact quittingLiteralRootStackProfile_apply_eq_of_tail
    (data.roots rank) (data.targetTail rank) (data.chordTail rank) other
    (data.targetTail_eq_chordTail_of_ne rank other hne)

/-- Replacing the mover's complete prefixed chord strategy by its prefixed
target strategy is definitionally the target-prefixed profile. -/
theorem update_chordPrefixedProfile_eq_targetPrefixedProfile
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    Function.update (data.chordPrefixedProfile rank) base.response.mover
        (data.targetPrefixedProfile rank base.response.mover) =
      data.targetPrefixedProfile rank := by
  funext other
  by_cases hother : other = base.response.mover
  · subst other
    simp
  · rw [Function.update_of_ne hother]
    exact (data.targetPrefixedProfile_eq_chordPrefixedProfile_of_ne
      rank other hother).symm

/-- Exact total-debt scaling for the chord-prefixed cap--Nash row. -/
theorem chordPrefixed_debtSum_eq_survival_mul
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingTerminalDebtSum reward (data.chordPrefixedProfile rank) =
      data.survival rank *
        quittingTerminalDebtSum reward (data.chordTail rank) := by
  exact quittingTerminalDebtSum_capNashRootStack_eq
    (reward := reward) (data.roots rank) (data.chordTail rank)
      (data.roots_capNash rank)

/-- The global literal debt infimum lies below every product-scaled chord
tail debt. -/
theorem debtSumInf_le_survival_mul_chordDebt
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingTerminalDebtSumInf reward ≤ data.survival rank *
      quittingTerminalDebtSum reward (data.chordTail rank) := by
  exact debtSumInf_le_capNashStackContinueProduct_mul_debtSum
    (reward := reward) (data.roots rank) (data.chordTail rank)
      (data.roots_capNash rank)

/-- The supplied minimum debt lies below every product-scaled actual chord
tail debt. -/
theorem minimumDebt_le_survival_mul_chordDebt
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingTerminalSemanticDebtSum source.point.1 ≤ data.survival rank *
      quittingTerminalDebtSum reward (data.chordTail rank) := by
  rw [source.debt_eq_inf]
  exact data.debtSumInf_le_survival_mul_chordDebt rank

/-- The cap--Nash survival product is definitionally the joint survival of
the same literal word. -/
theorem survival_eq_jointSurvival
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    data.survival rank =
      quittingLiteralRootStackJointSurvival (data.roots rank) := rfl

/-- The actual chord tails converge jointly to the fixed minimum chord
point and its terminal law. -/
theorem chordTail_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward (data.chordTail rank),
        quittingTerminalOutcomeMass reward (data.chordTail rank)))
      atTop (nhds compactification.chordPoint) := by
  simpa only [chordTail] using compactification.chord_tendsto

/-- The compact chord lies on the supplied global minimum fibre. -/
theorem chordPoint_debtSum_eq_inf
    (_data : FinFourFullDebtCommonPrefixResponse compactification) :
    quittingTerminalSemanticDebtSum compactification.chordPoint.1 =
      quittingTerminalDebtSumInf reward := by
  rw [← source.debt_eq_inf, ← compactification.geometry_endpoint_eq,
    ← compactification.geometry_chord_eq]
  exact compactification.geometry.chord_debtSum_eq_endpoint

/-- The total debt of the actual chord tails converges to the global literal
debt infimum. -/
theorem chordTail_debtSum_tendsto_inf
    (data : FinFourFullDebtCommonPrefixResponse compactification) :
    Tendsto (fun rank ↦
      quittingTerminalDebtSum reward (data.chordTail rank)) atTop
      (nhds (quittingTerminalDebtSumInf reward)) := by
  have hpair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward (data.chordTail rank)) atTop
      (nhds compactification.chordPoint.1) :=
    continuous_fst.tendsto compactification.chordPoint |>.comp
      data.chordTail_tendsto
  have hdebt := continuous_quittingTerminalSemanticDebtSum.tendsto
    compactification.chordPoint.1 |>.comp hpair
  change Tendsto (fun rank ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (data.chordTail rank))) atTop
    (nhds (quittingTerminalSemanticDebtSum compactification.chordPoint.1))
    at hdebt
  rw [← data.chordPoint_debtSum_eq_inf]
  simpa only [quittingTerminalDebtSum_eq_terminalSemanticDebtSum] using hdebt

/-- The selected finite-word survival products converge to one. -/
theorem survival_tendsto_one
    (data : FinFourFullDebtCommonPrefixResponse compactification) :
    Tendsto data.survival atTop (nhds 1) := by
  have hlower : Tendsto (fun rank ↦
      quittingTerminalDebtSumInf reward /
        quittingTerminalDebtSum reward (data.chordTail rank)) atTop
      (nhds 1) := by
    have hconstant : Tendsto
        (fun _ : ℕ ↦ quittingTerminalDebtSumInf reward) atTop
        (nhds (quittingTerminalDebtSumInf reward)) := tendsto_const_nhds
    have hquotient := hconstant.div
      data.chordTail_debtSum_tendsto_inf source.inf_pos.ne'
    convert hquotient using 1
    · rfl
    · rw [div_self source.inf_pos.ne']
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
  · intro rank
    exact capNashStack_continueProduct_lowerBound
      (reward := reward) (data.roots rank) (data.chordTail rank)
        source.inf_pos (data.roots_capNash rank)
  · intro rank
    exact quittingCapNashStackContinueProduct_le_one (data.roots rank)

/-- Every fixed player-deleted survival factor of the selected words also
converges to one. -/
theorem opponentSurvival_tendsto_one
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦
      quittingLiteralRootStackOpponentSurvival (data.roots rank) who)
      atTop (nhds 1) := by
  apply tendsto_quittingLiteralRootStackOpponentSurvival_one
  simpa only [← data.survival_eq_jointSurvival] using data.survival_tendsto_one

/-- The exact chord-prefixed debt totals converge to the same global
minimum. -/
theorem chordPrefixed_debtSum_tendsto_inf
    (data : FinFourFullDebtCommonPrefixResponse compactification) :
    Tendsto (fun rank ↦
      quittingTerminalDebtSum reward (data.chordPrefixedProfile rank)) atTop
      (nhds (quittingTerminalDebtSumInf reward)) := by
  have hproduct := data.survival_tendsto_one.mul
    data.chordTail_debtSum_tendsto_inf
  convert hproduct using 1
  · funext rank
    exact data.chordPrefixed_debtSum_eq_survival_mul rank
  · simp

/-- The target is a literal unilateral behavioral response to the prefixed
chord row. -/
theorem targetPrefixed_eq_update
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    data.targetPrefixedProfile rank =
      Function.update (data.chordPrefixedProfile rank) base.response.mover
        (data.targetPrefixedProfile rank base.response.mover) := by
  exact (data.update_chordPrefixedProfile_eq_targetPrefixedProfile rank).symm

/-- The mover's unrestricted behavioral cap is unchanged by taking the
literal target response. -/
theorem targetPrefixed_mover_cap_eq_chordPrefixed
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingContinuationBestResponseValue reward
        (data.targetPrefixedProfile rank) base.response.mover =
      quittingContinuationBestResponseValue reward
        (data.chordPrefixedProfile rank) base.response.mover := by
  rw [data.targetPrefixed_eq_update rank]
  exact quittingContinuationBestResponseValue_update_self reward
    (data.chordPrefixedProfile rank) base.response.mover
    (data.targetPrefixedProfile rank base.response.mover)

/-- The target tail is the full behavioral response endpoint of the actual
chord tail. -/
theorem update_chordTail_eq_targetTail
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    Function.update (data.chordTail rank) base.response.mover
        (data.targetTail rank base.response.mover) =
      data.targetTail rank := by
  apply update_endpoint_with_response_observer_eq_response
  intro other hother
  exact data.targetTail_eq_chordTail_of_ne rank other hother

/-- The mover's complete behavioral cap agrees at the actual chord and target
tails. -/
theorem targetTail_mover_cap_eq_chordTail
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingContinuationBestResponseValue reward (data.targetTail rank)
        base.response.mover =
      quittingContinuationBestResponseValue reward (data.chordTail rank)
        base.response.mover := by
  rw [← data.update_chordTail_eq_targetTail rank]
  exact quittingContinuationBestResponseValue_update_self reward
    (data.chordTail rank) base.response.mover
      (data.targetTail rank base.response.mover)

/-- The common word scales the prescribed mover-payoff response gain by its
joint survival. -/
theorem targetPrefixed_payoff_sub_chordPrefixed_eq_survival_mul
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) (who : Fin 4) :
    quittingTerminalPayoff reward (data.targetPrefixedProfile rank) who -
        quittingTerminalPayoff reward (data.chordPrefixedProfile rank) who =
      data.survival rank *
        (quittingTerminalPayoff reward (data.targetTail rank) who -
          quittingTerminalPayoff reward (data.chordTail rank) who) := by
  exact quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul
    (reward := reward) (data.roots rank) (data.targetTail rank)
      (data.chordTail rank) who

/-- The same common word transports the source-versus-chord payoff
difference for every observer. -/
theorem sourcePrefixed_payoff_sub_chordPrefixed_eq_survival_mul
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) (who : Fin 4) :
    quittingTerminalPayoff reward (data.sourcePrefixedProfile rank) who -
        quittingTerminalPayoff reward (data.chordPrefixedProfile rank) who =
      data.survival rank *
        (quittingTerminalPayoff reward (data.sourceTail rank) who -
          quittingTerminalPayoff reward (data.chordTail rank) who) := by
  exact quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul
    (reward := reward) (data.roots rank) (data.sourceTail rank)
      (data.chordTail rank) who

/-- The common word scales the prescribed mover-payoff response gain by its
joint survival. -/
theorem targetPrefixed_payoffGain_eq_survival_mul
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingTerminalPayoff reward (data.targetPrefixedProfile rank)
          base.response.mover -
        quittingTerminalPayoff reward (data.chordPrefixedProfile rank)
          base.response.mover =
      data.survival rank *
        (quittingTerminalPayoff reward (data.targetTail rank)
            base.response.mover -
          quittingTerminalPayoff reward (data.chordTail rank)
            base.response.mover) := by
  exact data.targetPrefixed_payoff_sub_chordPrefixed_eq_survival_mul
    rank base.response.mover

/-- The unprefixed chord-to-target gain is the fixed complementary weight
times the original literal cap-band response gain. -/
theorem targetTail_payoffGain_eq_complement_mul_sourceGain
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingTerminalPayoff reward (data.targetTail rank) base.response.mover -
        quittingTerminalPayoff reward (data.chordTail rank) base.response.mover =
      (1 - weight) *
        (quittingTerminalPayoff reward (data.targetTail rank)
            base.response.mover -
          quittingTerminalPayoff reward (data.sourceTail rank)
            base.response.mover) := by
  let sourceProfile := data.sourceTail rank
  let targetProfile := data.targetTail rank
  have htarget : Function.update sourceProfile base.response.mover
      (targetProfile base.response.mover) = targetProfile := by
    apply update_endpoint_with_response_observer_eq_response
    intro other hother
    dsimp only [sourceProfile, targetProfile, sourceTail, targetTail]
    exact base.targetProfile_eq_sourceProfile_of_ne
      (compactification.refinement rank) other hother
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq reward
    sourceProfile base.response.mover base.response.mover
      (sourceProfile base.response.mover) (targetProfile base.response.mover)
      weight hweight0.le hweight1.le
  rw [Function.update_eq_self, htarget] at haffine
  change quittingTerminalPayoff reward (data.chordTail rank)
      base.response.mover =
    (1 - weight) * quittingTerminalPayoff reward (data.sourceTail rank)
        base.response.mover +
      weight * quittingTerminalPayoff reward (data.targetTail rank)
        base.response.mover at haffine
  linarith

/-- The displayed prefixed response gain retains both the common-word
survival and the complementary chord weight. -/
theorem targetPrefixed_payoffGain_eq_survival_mul_complement_mul_sourceGain
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingTerminalPayoff reward (data.targetPrefixedProfile rank)
          base.response.mover -
        quittingTerminalPayoff reward (data.chordPrefixedProfile rank)
          base.response.mover =
      data.survival rank * (1 - weight) *
        (quittingTerminalPayoff reward (data.targetTail rank)
            base.response.mover -
          quittingTerminalPayoff reward (data.sourceTail rank)
            base.response.mover) := by
  rw [data.targetPrefixed_payoffGain_eq_survival_mul rank,
    data.targetTail_payoffGain_eq_complement_mul_sourceGain rank]
  ring

/-- The retained cap-band gain floor passes literally through the proper
chord and common word. -/
theorem survival_mul_complement_mul_halfMoverDebt_le_targetPrefixed_gain
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (rank : ℕ) :
    data.survival rank * (1 - weight) *
        (quittingTerminalSemanticDebt source.point.1 base.response.mover / 2) ≤
      quittingTerminalPayoff reward (data.targetPrefixedProfile rank)
          base.response.mover -
        quittingTerminalPayoff reward (data.chordPrefixedProfile rank)
          base.response.mover := by
  rw [data.targetPrefixed_payoffGain_eq_survival_mul_complement_mul_sourceGain]
  have hgain := base.half_limitingMoverDebt_le_payoffGain hreward
    (compactification.refinement rank)
  have hfactor : 0 ≤ data.survival rank * (1 - weight) :=
    mul_nonneg (quittingCapNashStackContinueProduct_nonneg (data.roots rank))
      (sub_nonneg.mpr hweight1.le)
  exact mul_le_mul_of_nonneg_left hgain hfactor

/-- The target-prefixed mover debt is exactly the word survival times the
unprefixed target mover debt. -/
theorem targetPrefixed_moverDebt_eq_survival_mul
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingTerminalDeviationDebt reward (data.targetPrefixedProfile rank)
        base.response.mover =
      data.survival rank *
        quittingTerminalDeviationDebt reward (data.targetTail rank)
          base.response.mover := by
  have hchord := quittingTerminalDeviationDebt_capNashRootStack_eq
    (reward := reward) (data.roots rank) (data.chordTail rank)
      base.response.mover (data.roots_capNash rank)
  have hgain := data.targetPrefixed_payoffGain_eq_survival_mul rank
  have hprefixCap := data.targetPrefixed_mover_cap_eq_chordPrefixed rank
  have htailCap := data.targetTail_mover_cap_eq_chordTail rank
  unfold quittingTerminalDeviationDebt at hchord ⊢
  change quittingContinuationBestResponseValue reward
        (data.chordPrefixedProfile rank) base.response.mover -
      quittingTerminalPayoff reward (data.chordPrefixedProfile rank)
        base.response.mover =
    data.survival rank *
      (quittingContinuationBestResponseValue reward (data.chordTail rank)
          base.response.mover -
        quittingTerminalPayoff reward (data.chordTail rank)
          base.response.mover) at hchord
  rw [hprefixCap]
  linear_combination hchord - hgain - data.survival rank * htailCap

/-- Every terminal-law coordinate of the target-versus-chord difference is
transported by the same word survival. -/
theorem targetPrefixed_law_sub_chordPrefixed_eq_survival_mul
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) (outcome : QuittingTerminalOutcome (Fin 4)) :
    quittingTerminalOutcomeMass reward (data.targetPrefixedProfile rank) outcome -
        quittingTerminalOutcomeMass reward (data.chordPrefixedProfile rank) outcome =
      data.survival rank *
        (quittingTerminalOutcomeMass reward (data.targetTail rank) outcome -
          quittingTerminalOutcomeMass reward (data.chordTail rank) outcome) := by
  exact quittingTerminalOutcomeMass_literalRootStack_sub_eq
    reward (data.roots rank) (data.targetTail rank)
      (data.chordTail rank) outcome

/-- Every terminal-law coordinate of the source-versus-chord difference is
transported by the same word survival. -/
theorem sourcePrefixed_law_sub_chordPrefixed_eq_survival_mul
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) (outcome : QuittingTerminalOutcome (Fin 4)) :
    quittingTerminalOutcomeMass reward (data.sourcePrefixedProfile rank) outcome -
        quittingTerminalOutcomeMass reward (data.chordPrefixedProfile rank) outcome =
      data.survival rank *
        (quittingTerminalOutcomeMass reward (data.sourceTail rank) outcome -
          quittingTerminalOutcomeMass reward (data.chordTail rank) outcome) := by
  exact quittingTerminalOutcomeMass_literalRootStack_sub_eq
    reward (data.roots rank) (data.sourceTail rank)
      (data.chordTail rank) outcome

/-- The actual target-tail mover debt tends to zero on the fixed chord
refinement. -/
theorem targetTail_moverDebt_tendsto_zero
    (data : FinFourFullDebtCommonPrefixResponse compactification) :
    Tendsto (fun rank ↦ quittingTerminalDeviationDebt reward
      (data.targetTail rank) base.response.mover) atTop (nhds 0) := by
  have hpair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward (data.targetTail rank)) atTop
      (nhds base.targetPoint.1) :=
    continuous_fst.tendsto base.targetPoint |>.comp
      compactification.target_tendsto
  have hdebt := (continuous_quittingTerminalSemanticDebt
    base.response.mover).tendsto base.targetPoint.1 |>.comp hpair
  change Tendsto (fun rank ↦ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (data.targetTail rank))
        base.response.mover) atTop
    (nhds (quittingTerminalSemanticDebt base.targetPoint.1
      base.response.mover)) at hdebt
  rw [minimumTarget.targetMoverDebt_eq_zero] at hdebt
  change Tendsto (fun rank ↦ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (data.targetTail rank))
        base.response.mover) atTop (nhds 0)
  exact hdebt

/-- The literal target-prefixed response kills the mover debt in the limit. -/
theorem targetPrefixed_moverDebt_tendsto_zero
    (data : FinFourFullDebtCommonPrefixResponse compactification) :
    Tendsto (fun rank ↦ quittingTerminalDeviationDebt reward
      (data.targetPrefixedProfile rank) base.response.mover) atTop
      (nhds 0) := by
  have hproduct := data.survival_tendsto_one.mul
    data.targetTail_moverDebt_tendsto_zero
  convert hproduct using 1
  · funext rank
    exact data.targetPrefixed_moverDebt_eq_survival_mul rank
  · simp

/-- Each actual chord-tail debt coordinate converges to its compact chord
coordinate. -/
theorem chordTail_debt_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingTerminalDeviationDebt reward
      (data.chordTail rank) who) atTop
      (nhds (quittingTerminalSemanticDebt compactification.chordPoint.1 who)) := by
  have hpair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward (data.chordTail rank)) atTop
      (nhds compactification.chordPoint.1) :=
    continuous_fst.tendsto compactification.chordPoint |>.comp
      data.chordTail_tendsto
  have hdebt := (continuous_quittingTerminalSemanticDebt who).tendsto
    compactification.chordPoint.1 |>.comp hpair
  change Tendsto (fun rank ↦ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (data.chordTail rank)) who)
    atTop
      (nhds (quittingTerminalSemanticDebt compactification.chordPoint.1 who))
  exact hdebt

/-- Exact playerwise debt scaling for the actual chord-prefixed cap--Nash
row. -/
theorem chordPrefixed_debt_eq_survival_mul
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) (who : Fin 4) :
    quittingTerminalDeviationDebt reward (data.chordPrefixedProfile rank) who =
      data.survival rank *
        quittingTerminalDeviationDebt reward (data.chordTail rank) who := by
  exact quittingTerminalDeviationDebt_capNashRootStack_eq
    (reward := reward) (data.roots rank) (data.chordTail rank) who
      (data.roots_capNash rank)

/-- Every chord-prefixed debt coordinate converges to its compact chord
coordinate. -/
theorem chordPrefixed_debt_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingTerminalDeviationDebt reward
      (data.chordPrefixedProfile rank) who) atTop
      (nhds (quittingTerminalSemanticDebt compactification.chordPoint.1 who)) := by
  have hproduct := data.survival_tendsto_one.mul
    (data.chordTail_debt_tendsto who)
  convert hproduct using 1
  · funext rank
    exact data.chordPrefixed_debt_eq_survival_mul rank who
  · simp

/-- The selected word is nonempty at every row. -/
theorem roots_ne_nil
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) : data.roots rank ≠ [] := by
  intro hempty
  have hlength := data.roots_length rank
  rw [hempty] at hlength
  simp at hlength

/-- First root of the selected nonempty word. -/
def firstRoot (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) : Fin 4 → PMF Bool :=
  (data.roots rank).head (data.roots_ne_nil rank)

/-- Remaining roots after the first root of the selected word. -/
def remainingRoots
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) : List (Fin 4 → PMF Bool) :=
  (data.roots rank).tail

/-- The head/tail decomposition recovers the selected word literally. -/
theorem firstRoot_cons_remainingRoots
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (rank : ℕ) :
    data.firstRoot rank :: data.remainingRoots rank = data.roots rank := by
  exact List.cons_head_tail (data.roots_ne_nil rank)

/-- Every coordinate of the actual chord-tail unrestricted cap converges to
the corresponding cap coordinate of the compact chord. -/
theorem chordTail_cap_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingContinuationBestResponseValue reward
      (data.chordTail rank) who) atTop
      (nhds (compactification.chordPoint.1.2 who)) := by
  have hpair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward (data.chordTail rank)) atTop
      (nhds compactification.chordPoint.1) :=
    continuous_fst.tendsto compactification.chordPoint |>.comp
      data.chordTail_tendsto
  have hcap := ((continuous_apply who).comp continuous_snd).tendsto
    compactification.chordPoint.1 |>.comp hpair
  change Tendsto (fun rank ↦ quittingContinuationBestResponseValue reward
      (data.chordTail rank) who) atTop
    (nhds (compactification.chordPoint.1.2 who)) at hcap
  exact hcap

/-- Every coordinate of the actual target-tail unrestricted cap converges to
the corresponding cap coordinate of the compact target. -/
theorem targetTail_cap_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingContinuationBestResponseValue reward
      (data.targetTail rank) who) atTop (nhds (base.targetPoint.1.2 who)) := by
  have hpair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward (data.targetTail rank)) atTop
      (nhds base.targetPoint.1) :=
    continuous_fst.tendsto base.targetPoint |>.comp
      compactification.target_tendsto
  have hcap := ((continuous_apply who).comp continuous_snd).tendsto
    base.targetPoint.1 |>.comp hpair
  change Tendsto (fun rank ↦ quittingContinuationBestResponseValue reward
      (data.targetTail rank) who) atTop
    (nhds (base.targetPoint.1.2 who)) at hcap
  exact hcap

/-- The compact chord is itself a positive global minimum semantic pair. -/
theorem chordPoint_globalMinimum
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (candidate : QuittingTerminalSemanticPair (Fin 4))
    (hcandidate : candidate ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalSemanticDebtSum compactification.chordPoint.1 ≤
      quittingTerminalSemanticDebtSum candidate := by
  rw [data.chordPoint_debtSum_eq_inf, ← source.debt_eq_inf]
  exact source.minimum candidate hcandidate

/-- Singleton cash-out is strictly below every compact chord cap
coordinate. -/
theorem singletonReward_lt_chordPoint_cap
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (who : Fin 4) :
    reward (quittingSingletonTerminal who) who <
      compactification.chordPoint.1.2 who := by
  have hsemantic : compactification.chordPoint.1 ∈
      quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier compactification.chordPoint
      compactification.chordPoint_mem
  have hmargin := minimumTerminalSemantic_singletonMargin
    compactification.chordPoint.1 hsemantic data.chordPoint_globalMinimum
      (by rw [data.chordPoint_debtSum_eq_inf]; exact source.inf_pos) who
  have hpositive : 0 < quittingTerminalSemanticDebtSum
      compactification.chordPoint.1 := by
    rw [data.chordPoint_debtSum_eq_inf]
    exact source.inf_pos
  linarith

/-- Singleton cash-out is strictly below every compact target cap
coordinate. -/
theorem singletonReward_lt_targetPoint_cap
    (_data : FinFourFullDebtCommonPrefixResponse compactification)
    (who : Fin 4) :
    reward (quittingSingletonTerminal who) who < base.targetPoint.1.2 who := by
  have hsemantic : base.targetPoint.1 ∈
      quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier base.targetPoint
      base.targetPoint_mem
  have hpositive : 0 < quittingTerminalSemanticDebtSum base.targetPoint.1 := by
    rw [minimumTarget.targetDebtSum_eq_source]
    exact source.minimumDebt_pos
  have hmargin := minimumTerminalSemantic_singletonMargin
    base.targetPoint.1 hsemantic minimumTarget.target_is_globalMinimum
      hpositive who
  linarith

/-- The complete unrestricted behavioral caps of the chord-prefixed rows
converge coordinatewise to the compact chord caps. -/
theorem chordPrefixed_cap_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingContinuationBestResponseValue reward
      (data.chordPrefixedProfile rank) who) atTop
      (nhds (compactification.chordPoint.1.2 who)) := by
  have hsurvival : Tendsto (fun rank ↦
      quittingLiteralRootStackJointSurvival
        (data.firstRoot rank :: data.remainingRoots rank)) atTop (nhds 1) := by
    simpa only [data.firstRoot_cons_remainingRoots,
      ← data.survival_eq_jointSurvival] using data.survival_tendsto_one
  have hcap := tendsto_quittingContinuationBestResponseValue_literalRootStack_of_joint
    reward data.firstRoot data.remainingRoots data.chordTail who
      (compactification.chordPoint.1.2 who) hsurvival
      (data.chordTail_cap_tendsto who)
      (data.singletonReward_lt_chordPoint_cap who)
  simpa only [chordPrefixedProfile,
    data.firstRoot_cons_remainingRoots] using hcap

/-- The complete unrestricted behavioral caps of the target-prefixed rows
converge coordinatewise to the compact target caps. -/
theorem targetPrefixed_cap_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingContinuationBestResponseValue reward
      (data.targetPrefixedProfile rank) who) atTop
      (nhds (base.targetPoint.1.2 who)) := by
  have hsurvival : Tendsto (fun rank ↦
      quittingLiteralRootStackJointSurvival
        (data.firstRoot rank :: data.remainingRoots rank)) atTop (nhds 1) := by
    simpa only [data.firstRoot_cons_remainingRoots,
      ← data.survival_eq_jointSurvival] using data.survival_tendsto_one
  have hcap := tendsto_quittingContinuationBestResponseValue_literalRootStack_of_joint
    reward data.firstRoot data.remainingRoots data.targetTail who
      (base.targetPoint.1.2 who) hsurvival (data.targetTail_cap_tendsto who)
      (data.singletonReward_lt_targetPoint_cap who)
  simpa only [targetPrefixedProfile,
    data.firstRoot_cons_remainingRoots] using hcap

/-- The prescribed chord-tail payoffs converge coordinatewise to the compact
chord payoff. -/
theorem chordTail_payoff_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingTerminalPayoff reward
      (data.chordTail rank) who) atTop
      (nhds (compactification.chordPoint.1.1 who)) := by
  have hpair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward (data.chordTail rank)) atTop
      (nhds compactification.chordPoint.1) :=
    continuous_fst.tendsto compactification.chordPoint |>.comp
      data.chordTail_tendsto
  have hpayoff := ((continuous_apply who).comp continuous_fst).tendsto
    compactification.chordPoint.1 |>.comp hpair
  change Tendsto (fun rank ↦ quittingTerminalPayoff reward
      (data.chordTail rank) who) atTop
    (nhds (compactification.chordPoint.1.1 who)) at hpayoff
  exact hpayoff

/-- The prescribed target-tail payoffs converge coordinatewise to the compact
target payoff. -/
theorem targetTail_payoff_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingTerminalPayoff reward
      (data.targetTail rank) who) atTop (nhds (base.targetPoint.1.1 who)) := by
  have hpair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward (data.targetTail rank)) atTop
      (nhds base.targetPoint.1) :=
    continuous_fst.tendsto base.targetPoint |>.comp
      compactification.target_tendsto
  have hpayoff := ((continuous_apply who).comp continuous_fst).tendsto
    base.targetPoint.1 |>.comp hpair
  change Tendsto (fun rank ↦ quittingTerminalPayoff reward
      (data.targetTail rank) who) atTop
    (nhds (base.targetPoint.1.1 who)) at hpayoff
  exact hpayoff

/-- The prescribed chord-prefixed payoffs converge coordinatewise to the
compact chord payoff. -/
theorem chordPrefixed_payoff_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingTerminalPayoff reward
      (data.chordPrefixedProfile rank) who) atTop
      (nhds (compactification.chordPoint.1.1 who)) := by
  have hdifference := (data.chordPrefixed_cap_tendsto who).sub
    (data.chordPrefixed_debt_tendsto who)
  unfold quittingTerminalDeviationDebt at hdifference
  simpa only [quittingTerminalSemanticDebt, sub_sub_cancel] using hdifference

/-- The prescribed target-prefixed payoffs converge coordinatewise to the
compact target payoff. -/
theorem targetPrefixed_payoff_tendsto
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingTerminalPayoff reward
      (data.targetPrefixedProfile rank) who) atTop
      (nhds (base.targetPoint.1.1 who)) := by
  have htailDifference := (data.targetTail_payoff_tendsto who).sub
    (data.chordTail_payoff_tendsto who)
  have hscaled := data.survival_tendsto_one.mul htailDifference
  have hsum := hscaled.add (data.chordPrefixed_payoff_tendsto who)
  convert hsum using 1
  · funext rank
    have htransport :=
      data.targetPrefixed_payoff_sub_chordPrefixed_eq_survival_mul rank who
    linarith
  · congr 1
    ring

end FinFourFullDebtCommonPrefixResponse

/-- Exact finite cap--Nash words of length `rank + 1` exist against every
actual chord row. -/
theorem nonempty_finFourFullDebtCommonPrefixResponse
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {base : FinFourFullDebtCapBandTargetCompactification source M}
    {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    (compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1) :
    Nonempty (FinFourFullDebtCommonPrefixResponse compactification) := by
  let chordTail : ℕ → (quittingGame reward).BehaviorProfile := fun rank ↦
    base.fixedWeightChordProfile weight hweight0.le hweight1.le
      (compactification.refinement rank)
  have hexists : ∀ rank, ∃ roots : List (Fin 4 → PMF Bool),
      roots.length = rank + 1 ∧
        IsQuittingCapNashRootStack reward roots (chordTail rank) := by
    intro rank
    exact exists_quittingCapNashRootStack reward (chordTail rank) (rank + 1)
  let roots : ℕ → List (Fin 4 → PMF Bool) := fun rank ↦
    Classical.choose (hexists rank)
  exact ⟨{
    roots := roots
    roots_length := fun rank ↦ (Classical.choose_spec (hexists rank)).1
    roots_capNash := fun rank ↦ (Classical.choose_spec (hexists rank)).2
  }⟩

end GameTheory
