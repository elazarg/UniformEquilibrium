import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSignAdaptiveContactSource
import UniformEquilibrium.Quitting.Terminal.RecipientScaledTerminalSemantics

/-! # Recipient rigidity preserving fixed reward contacts

An actual row-generic contact source admits arbitrarily small positive
recipient contractions. One new table retains all original labels and cohorts
and has one common debt vector at every actual new SUM minimum. Pair
uniqueness, transport of old minima, and singleton preservation are not asserted.
The closed producers choose an original worst table internally, then retain its
fixed labels while selecting one final table before every new minimum pair.
No finite-law realization or final cap classification is asserted.
-/

noncomputable section

namespace GameTheory

open _root_.Set QuittingSureSetOwnerRepair
open scoped Topology

private abbrev RecipientContactTable :=
  {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)

private theorem setReward_recipientScale (center : RecipientContactTable)
    (weights : Payoff (Fin 4)) (coalition : Finset (Fin 4)) (who : Fin 4) :
    quittingSetReward (quittingPlayerwiseAffineReward center weights 0) coalition who =
      weights who * quittingSetReward center coalition who := by
  by_cases hne : coalition.Nonempty
  · simp [quittingSetReward, quittingPlayerwiseAffineReward, hne]
  · simp [quittingSetReward, hne]

private theorem membershipGain_recipientScale (center : RecipientContactTable)
    (weights : Payoff (Fin 4)) (who : Fin 4) (coalition : Finset (Fin 4)) :
    quittingMembershipGain (quittingPlayerwiseAffineReward center weights 0) who coalition =
      weights who * quittingMembershipGain center who coalition := by
  simp only [quittingMembershipGain, MathUE.binaryJoinGain, setReward_recipientScale]
  ring

private theorem continuous_fixed_contact (original : RecipientContactTable)
    (label : QuittingSignAdaptiveContactLabel original) :
    Continuous (fun table : RecipientContactTable =>
      quittingSignAdaptiveContactValue original table label) := by
  have hlipschitz : LipschitzWith 8 (fun table : RecipientContactTable =>
      quittingSignAdaptiveContactValue original table label) := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    have hclose : ∀ terminal who,
        |first terminal who - second terminal who| ≤ dist first second := by
      intro terminal who
      rw [← Real.dist_eq]
      exact (dist_le_pi_dist (first terminal) (second terminal) who).trans
        (dist_le_pi_dist first second terminal)
    simpa only [Real.dist_eq, NNReal.coe_ofNat] using
      abs_quittingSignAdaptiveContactValue_sub_le original first second
        (dist first second) hclose label
  exact hlipschitz.continuous

private theorem continuous_recipientTable (center : RecipientContactTable) :
    Continuous (fun weights : Payoff (Fin 4) =>
      quittingPlayerwiseAffineReward center weights 0) := by
  change Continuous (fun weights : Payoff (Fin 4) =>
    fun terminal who => weights who * center terminal who + 0)
  exact continuous_pi fun _ => continuous_pi fun who =>
    ((continuous_apply who).mul continuous_const).add continuous_const

private theorem recipientTable_one (center : RecipientContactTable) :
    quittingPlayerwiseAffineReward center 1 0 = center := by
  funext terminal who
  simp [quittingPlayerwiseAffineReward]

/-- A positive recipient contraction preserves all row and cohort data exactly. -/
private theorem rowGenericSource_recipientScale
    {original center : RecipientContactTable}
    (source : QuittingSignAdaptiveRowGenericSource original center)
    (weights : Payoff (Fin 4))
    (hweights : ∀ who, (1 / 2 : ℝ) ≤ weights who ∧ weights who < 1)
    (hcontacts : ∀ label : QuittingSignAdaptiveContactLabel original,
      quittingSignAdaptiveContactValue original
          (quittingPlayerwiseAffineReward center weights 0) label ≠
        quittingTerminalDebtSumInf (quittingPlayerwiseAffineReward center weights 0)) :
    QuittingSignAdaptiveRowGenericSource original
      (quittingPlayerwiseAffineReward center weights 0) := by
  have hpositive : ∀ who, 0 < weights who := by
    intro who
    linarith [(hweights who).1]
  refine ⟨?_, ?_, hcontacts, ?_, ?_, ?_⟩
  · intro terminal who
    simp only [quittingPlayerwiseAffineReward, Pi.zero_apply, add_zero, abs_mul,
      abs_of_pos (hpositive who)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hweights who).2.le).trans_lt
      (source.strictUnit terminal who)
  · have hbound := (quittingTerminalDebtSumInf_recipientScale_bounds center weights
        hpositive (1 / 2) 1 (by norm_num)
        (fun who => ⟨(hweights who).1, (hweights who).2.le⟩)).1
    exact (mul_pos (by norm_num) source.positiveSum).trans_le hbound
  · intro coalition hcard
    rw [source.member_cohort coalition hcard]
    apply Finset.filter_congr
    intro who _
    rw [membershipGain_recipientScale, ← mul_neg,
      mul_pos_iff_of_pos_left (hpositive who)]
  · intro coalition hne
    rw [source.outsider_cohort coalition hne]
    apply Finset.filter_congr
    intro who _
    simp only [membershipGain_recipientScale, mul_pos_iff_of_pos_left (hpositive who)]
  · intro who first second hne hequal
    have hscaled : weights who * center first who = weights who * center second who := by
      simpa only [quittingPlayerwiseAffineReward, Pi.zero_apply, add_zero] using hequal
    exact source.row_distinct who first second hne
      (mul_left_cancel₀ (hpositive who).ne' hscaled)

/-- One nearby contracted table preserves fixed contacts and has one debt vector at all minima. -/
theorem exists_recipientRigid_signAdaptiveContact_source
    (original center : RecipientContactTable)
    (source : QuittingSignAdaptiveRowGenericSource original center)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ weights : Payoff (Fin 4),
      (∀ who, max 0 (1 - tolerance) < weights who ∧ weights who < 1) ∧
      let final := quittingPlayerwiseAffineReward center weights 0
      QuittingSignAdaptiveRowGenericSource original final ∧
      (∀ terminal who, |final terminal who - center terminal who| < tolerance) ∧
      ∃ debt : Payoff (Fin 4),
        (∃ pair ∈ quittingTerminalSemanticCarrier final,
          quittingTerminalSemanticDebtSum pair = quittingTerminalDebtSumInf final ∧
            quittingTerminalSemanticDebt pair = debt) ∧
        ∀ pair ∈ quittingTerminalSemanticCarrier final,
          quittingTerminalSemanticDebtSum pair = quittingTerminalDebtSumInf final →
            quittingTerminalSemanticDebt pair = debt := by
  classical
  have hnearTables : ∀ᶠ table in nhds center,
      ∀ label : QuittingSignAdaptiveContactLabel original,
        quittingSignAdaptiveContactValue original table label ≠
          quittingTerminalDebtSumInf table := by
    apply Filter.eventually_all.mpr
    intro label
    have h := ((continuous_fixed_contact original label).sub
      continuous_quittingTerminalDebtSumInf).continuousAt.tendsto.eventually
        (eventually_ne_nhds (sub_ne_zero.mpr (source.contact_ne_sum label)))
    filter_upwards [h] with table htable
    exact sub_ne_zero.mp htable
  have hscaleLimit : Filter.Tendsto
      (fun weights : Payoff (Fin 4) => quittingPlayerwiseAffineReward center weights 0)
      (nhds 1) (nhds center) := by
    simpa only [recipientTable_one] using
      (continuous_recipientTable center).continuousAt.tendsto (x := (1 : Payoff (Fin 4)))
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp
    (hscaleLimit.eventually hnearTables)
  let eta := min tolerance (min radius (1 / 2))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hetaTolerance : eta ≤ tolerance := min_le_left _ _
  have hetaRadius : eta ≤ radius := (min_le_right _ _).trans (min_le_left _ _)
  have hetaHalf : eta ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let region : Set (Payoff (Fin 4)) := Set.pi univ fun _ => Ioo (1 - eta) 1
  have hopen : IsOpen region := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have hregion : region.Nonempty := by
    refine ⟨fun _ => 1 - eta / 2, ?_⟩
    intro who _
    change 1 - eta < 1 - eta / 2 ∧ 1 - eta / 2 < 1
    constructor <;> linarith
  have hregionPositive : ∀ weights ∈ region, ∀ who, 0 < weights who := by
    intro weights hweights who
    have h := hweights who (mem_univ who)
    change 1 - eta < weights who ∧ weights who < 1 at h
    linarith
  obtain ⟨weights, hweights, debt, hattained, hall⟩ :=
    exists_recipientScale_all_minimum_debts_eq center region hopen hregion hregionPositive
  have hbox (who : Fin 4) : 1 - eta < weights who ∧ weights who < 1 :=
    hweights who (mem_univ who)
  have hweightsHalf (who : Fin 4) : (1 / 2 : ℝ) ≤ weights who ∧ weights who < 1 := by
    constructor
    · linarith [(hbox who).1]
    · exact (hbox who).2
  have hdist : dist weights (1 : Payoff (Fin 4)) < radius := by
    apply (dist_pi_lt_iff hradius).mpr
    intro who
    rw [Real.dist_eq, Pi.one_apply, abs_of_neg (sub_neg.mpr (hbox who).2)]
    linarith [(hbox who).1]
  refine ⟨weights, ?_, ?_⟩
  · intro who
    refine ⟨?_, (hbox who).2⟩
    exact lt_of_le_of_lt (max_le (by linarith) (by linarith)) (hbox who).1
  · refine ⟨rowGenericSource_recipientScale source weights hweightsHalf (hball hdist),
      ?_, debt, hattained, hall⟩
    intro terminal who
    have hequal : quittingPlayerwiseAffineReward center weights 0 terminal who -
        center terminal who = (weights who - 1) * center terminal who := by
      simp only [quittingPlayerwiseAffineReward, Pi.zero_apply, add_zero]
      ring
    rw [hequal, abs_mul, abs_of_neg (sub_neg.mpr (hbox who).2)]
    have hcenter := (source.strictUnit terminal who).le
    have hnonnegative : 0 ≤ -(weights who - 1) := by linarith [(hbox who).2]
    exact (mul_le_mul_of_nonneg_left hcenter hnonnegative).trans_lt (by
      rw [mul_one]
      linarith [(hbox who).1])

/-- Positive SUM supplies a worst-table source with one debt vector at every final minimum. -/
theorem exists_positive_recipientRigid_signAdaptiveContact_source
    (reward : RecipientContactTable) (hpositive : 0 < quittingTerminalDebtSumInf reward)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ original final : RecipientContactTable,
      (∀ terminal who, |original terminal who| ≤ 1) ∧
      0 < quittingTerminalDebtSumInf original ∧ quittingTerminalDebtSumInf original ≤ 4 / 5 ∧
      (∀ candidate : RecipientContactTable,
        (∀ terminal who, |candidate terminal who| ≤ 1) →
          quittingTerminalDebtSumInf candidate ≤ quittingTerminalDebtSumInf original) ∧
      QuittingSignAdaptiveRowGenericSource original final ∧
      (∀ terminal who, |final terminal who - original terminal who| < tolerance) ∧
      ∃ debt : Payoff (Fin 4),
        (∃ pair ∈ quittingTerminalSemanticCarrier final,
          quittingTerminalSemanticDebtSum pair = quittingTerminalDebtSumInf final ∧
            quittingTerminalSemanticDebt pair = debt) ∧
        ∀ pair ∈ quittingTerminalSemanticCarrier final,
          quittingTerminalSemanticDebtSum pair = quittingTerminalDebtSumInf final →
            quittingTerminalSemanticDebt pair = debt := by
  have hhalf : 0 < tolerance / 2 := by positivity
  obtain ⟨original, center, hunit, hsum, hupper, hmaximum, hsource, hcenterClose⟩ :=
    exists_rowGeneric_quittingSignAdaptiveContact_source reward hpositive hhalf
  obtain ⟨weights, _, hfinalSource, hfinalClose, debt, hattained, hall⟩ :=
    exists_recipientRigid_signAdaptiveContact_source original center hsource hhalf
  refine ⟨original, quittingPlayerwiseAffineReward center weights 0,
    hunit, hsum, hupper, hmaximum, hfinalSource, ?_, debt, hattained, hall⟩
  intro terminal who
  have hequal : quittingPlayerwiseAffineReward center weights 0 terminal who -
      original terminal who =
      (quittingPlayerwiseAffineReward center weights 0 terminal who - center terminal who) +
        (center terminal who - original terminal who) := by ring
  rw [hequal]
  exact (abs_add_le _ _).trans_lt (by
    linarith [hfinalClose terminal who, hcenterClose terminal who])

/-- No uniform payoff supplies the same actual worst-table and all-minimum debt producer. -/
theorem exists_recipientRigid_signAdaptiveContact_source_of_not_uniformPayoff
    (reward : RecipientContactTable)
    (hnot : ¬∃ target : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none target)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ original final : RecipientContactTable,
      (∀ terminal who, |original terminal who| ≤ 1) ∧
      0 < quittingTerminalDebtSumInf original ∧ quittingTerminalDebtSumInf original ≤ 4 / 5 ∧
      (∀ candidate : RecipientContactTable,
        (∀ terminal who, |candidate terminal who| ≤ 1) →
          quittingTerminalDebtSumInf candidate ≤ quittingTerminalDebtSumInf original) ∧
      QuittingSignAdaptiveRowGenericSource original final ∧
      (∀ terminal who, |final terminal who - original terminal who| < tolerance) ∧
      ∃ debt : Payoff (Fin 4),
        (∃ pair ∈ quittingTerminalSemanticCarrier final,
          quittingTerminalSemanticDebtSum pair = quittingTerminalDebtSumInf final ∧
            quittingTerminalSemanticDebt pair = debt) ∧
        ∀ pair ∈ quittingTerminalSemanticCarrier final,
          quittingTerminalSemanticDebtSum pair = quittingTerminalDebtSumInf final →
            quittingTerminalSemanticDebt pair = debt := by
  exact exists_positive_recipientRigid_signAdaptiveContact_source reward
    (quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr hnot) htolerance

end GameTheory
