import MathUE.SignedAffineRowComparison
import UniformEquilibrium.Diagnostics.Quitting.SingleOptionalMembershipRows
import Mathlib.Tactic.Linarith

/-! # Opposed membership reversals at actual three-sure positive minima

The old table and common stretch are retained. All affine contacts come from
actual attained-minimum all-player ties. The comparison reselects only the
optional private law, and old globality is proved BEFORE old all-player ties.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct
open Math.SignedAffineRows

private theorem singleOptional_endpoint_eq_stretch
    (original final : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (alpha : ℝ) (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (optional who : Fin 4) (preferred choice : Bool) :
    quittingSingleOptionalDebtEndpoint final optional preferred choice who =
      Math.signedEndpointGapStretch alpha
        (quittingSingleOptionalDebtEndpoint original optional preferred choice who) := by
  have hcard : ({optional, who} : Finset (Fin 4)).card <
      (Finset.univ : Finset (Fin 4)).card :=
    Finset.card_le_two.trans_lt (by norm_num)
  obtain ⟨opponent, _, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hne : opponent ≠ optional ∧ opponent ≠ who := by simpa using hnot
  unfold quittingSingleOptionalDebtEndpoint
  by_cases hwho : who = optional
  · subst who
    simp only [ite_true]
    by_cases hchoice : choice = preferred
    · simp only [ite_eq_left hchoice, Math.signedEndpointGapStretch_zero]
    · simp only [ite_eq_right hchoice]
      exact quittingDirectedMembershipGap_eq_stretch_of_quittingOpponent
        original final alpha hagrees optional preferred (fun _ => true) hne.2 rfl
  · simp only [ite_eq_right hwho]
    exact quittingDirectedMembershipGap_eq_stretch_of_quittingOpponent
      original final alpha hagrees who false (quittingSingleOptionalAction optional choice)
      hne.2 (by simp only [quittingSingleOptionalAction, Function.update_of_ne hne.1])

private theorem abs_singleOptional_endpoint_le_two
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hbound : ∀ terminal who, |reward terminal who| ≤ 1)
    (optional who : Fin 4) (preferred choice : Bool) :
    |quittingSingleOptionalDebtEndpoint reward optional preferred choice who| ≤ 2 := by
  unfold quittingSingleOptionalDebtEndpoint
  split_ifs
  · norm_num
  · exact abs_quittingDirectedMembershipGap_le_two reward hbound optional preferred _
  · exact abs_quittingDirectedMembershipGap_le_two reward hbound who false _

/-- A weak comparison with one strict debt cannot beat a positive original infimum.
The full-profile global minimum is first obtained from the two-sided value chain. -/
private theorem not_fullDebt_comparison_below_positiveInf
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hbound : ∀ terminal who, |reward terminal who| ≤ 1)
    {value : ℝ} (hvalue : 0 < value)
    (hvalueInf : value ≤ quittingTerminalExploitabilityInf reward)
    (profile : (quittingGame reward).BehaviorProfile)
    (hweak : ∀ who, quittingTerminalDeviationDebt reward profile who ≤ value)
    (hstrict : ∃ who, quittingTerminalDeviationDebt reward profile who < value) : False := by
  have hupper : quittingTerminalExploitability reward profile ≤ value := by
    rw [quittingTerminalExploitability_eq_max_debt]
    exact QuittingBoundaryHolonomy.finitePlayerMax_le hweak
  have hlower : value ≤ quittingTerminalExploitability reward profile :=
    hvalueInf.trans (quittingTerminalExploitabilityInf_le reward profile)
  have hequal : quittingTerminalExploitability reward profile = value :=
    le_antisymm hupper hlower
  have hglobal (candidate : (quittingGame reward).BehaviorProfile) :
      quittingTerminalExploitability reward profile ≤
        quittingTerminalExploitability reward candidate := by
    rw [hequal]
    exact hvalueInf.trans (quittingTerminalExploitabilityInf_le reward candidate)
  obtain ⟨who, hwho⟩ := hstrict
  have htie := quittingTerminalDeviationDebt_eq_exploitability_of_attained_positive_minimum
    reward profile hbound hglobal (by rwa [hequal]) who
  rw [hequal] at htie
  exact (ne_of_lt hwho) htie

/-- The actual source has two DISTINCT sure owners reversing in opposite optional
orientations, with all four strict signs retained at BOTH literal tables. -/
theorem exists_opposedSureOwner_optionalReversals_of_membershipStretch_positiveMinimum_finFour
    (original final : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {alpha : ℝ} (halpha : 0 < alpha)
    (halpham : alpha < quittingTerminalExploitabilityInf final / 4)
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (horiginalBound : ∀ terminal who, |original terminal who| ≤ 1)
    (hfinalBound : ∀ terminal who, |final terminal who| ≤ 1)
    (root : Fin 4 → PMF Bool) (optional : Fin 4)
    (hsure : ∀ who, who ≠ optional → (root who true).toReal = 1)
    (hpositive : 0 < quittingTerminalExploitabilityInf final)
    (hinfOrder : quittingTerminalExploitabilityInf final ≤
      quittingTerminalExploitabilityInf original)
    (hminimum : quittingTerminalExploitability final
        (quittingOneDateThenNeverProfile final root) = quittingTerminalExploitabilityInf final) :
    ∃ first second : Fin 4, first ≠ optional ∧ second ≠ optional ∧ first ≠ second ∧
      quittingDirectedMembershipGap original first false
          (quittingSingleOptionalAction optional false) < 0 ∧
      0 < quittingDirectedMembershipGap original first false
          (quittingSingleOptionalAction optional true) ∧
      quittingDirectedMembershipGap original second false
          (quittingSingleOptionalAction optional true) < 0 ∧
      0 < quittingDirectedMembershipGap original second false
          (quittingSingleOptionalAction optional false) ∧
      quittingDirectedMembershipGap final first false
          (quittingSingleOptionalAction optional false) < 0 ∧
      0 < quittingDirectedMembershipGap final first false
          (quittingSingleOptionalAction optional true) ∧
      quittingDirectedMembershipGap final second false
          (quittingSingleOptionalAction optional true) < 0 ∧
      0 < quittingDirectedMembershipGap final second false
          (quittingSingleOptionalAction optional false) := by
  let value := quittingTerminalExploitabilityInf final
  have hglobal (candidate : (quittingGame final).BehaviorProfile) :
      quittingTerminalExploitability final (quittingOneDateThenNeverProfile final root) ≤
        quittingTerminalExploitability final candidate := by
    rw [hminimum]
    exact quittingTerminalExploitabilityInf_le final candidate
  have htie (who : Fin 4) : quittingTerminalDeviationDebt final
      (quittingOneDateThenNeverProfile final root) who = value := by
    rw [quittingTerminalDeviationDebt_eq_exploitability_of_attained_positive_minimum
      final _ hfinalBound hglobal (by rwa [hminimum]) who, hminimum]
  have hhalf : value < 1 / 2 := by
    have h := quittingTerminalExploitability_lt_half_of_attained_positive_minimum
      final _ hfinalBound hglobal (by rwa [hminimum])
    rwa [hminimum] at h
  obtain ⟨hmixed, core, negative, positive, hcore, hchoices, _, _,
    hnOld, hpOld, hnFinal, hpFinal⟩ :=
    exists_sureOwner_strictOptionalReversal_of_membershipStretch_positiveMinimum_finFour
      original final halpha hagrees horiginalBound hfinalBound root optional hsure
      hpositive hinfOrder hminimum
  have hother : positive = !negative := by
    cases negative <;> cases positive <;> simp_all
  subst positive
  obtain ⟨preferred, hbest⟩ := exists_quittingAveragedBestDirections final root
  let choice := preferred optional
  have hoptionalFinal : 0 ≤ quittingDirectedMembershipGap final optional choice
      (fun _ => true) := by
    have h := hbest optional
    rwa [expect_quittingDirectedMembershipGap_optional_eq
      final root optional choice hsure] at h
  obtain ⟨opponent, _, hopponentNe, hopponentSure⟩ :=
    exists_sureOpponent_singleOptional_finFour root optional optional hsure
  have hoptionalDebt := quittingTerminalDeviationDebt_singleOptional_optional_eq
    final root optional choice hsure hopponentNe hopponentSure hoptionalFinal
  rw [htie optional] at hoptionalDebt
  have hoptionalFinalStrict : 0 < quittingDirectedMembershipGap final optional choice
      (fun _ => true) := by
    by_contra hnot
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (ENNReal.toReal_nonneg : 0 ≤ (root optional (!choice)).toReal) (le_of_not_gt hnot)
    rw [← hoptionalDebt] at hnonpos
    exact (not_le_of_gt hpositive) hnonpos
  have hoptionalStretch := quittingDirectedMembershipGap_eq_stretch_of_quittingOpponent
    original final alpha hagrees optional choice (fun _ => true) hopponentNe rfl
  have hoptionalOld : 0 < quittingDirectedMembershipGap original optional choice
      (fun _ => true) := by
    rw [hoptionalStretch] at hoptionalFinalStrict
    exact (Math.signedEndpointGapStretch_pos_iff_of_abs_le_two halpha.le
      (abs_quittingDirectedMembershipGap_le_two original horiginalBound optional choice _)).mp
        hoptionalFinalStrict
  let left := quittingSingleOptionalDebtEndpoint original optional choice negative
  let right := quittingSingleOptionalDebtEndpoint original optional choice (!negative)
  let probability := (root optional negative).toReal
  have hp : 0 < probability := by
    cases negative
    · dsimp [probability]
      rw [pmfBool_false_toReal]
      linarith [hmixed.2]
    · exact hmixed.1
  have hp1 : probability < 1 := by
    cases negative
    · dsimp [probability]
      rw [pmfBool_false_toReal]
      linarith [hmixed.1]
    · exact hmixed.2
  have hbound (who : Fin 4) : |left who| ≤ 2 ∧ |right who| ≤ 2 :=
    ⟨abs_singleOptional_endpoint_le_two original horiginalBound optional who choice negative,
      abs_singleOptional_endpoint_le_two original horiginalBound optional who choice (!negative)⟩
  have hcontact (who : Fin 4) :
      rowValue probability (Math.signedEndpointGapStretch alpha (left who))
        (Math.signedEndpointGapStretch alpha (right who)) = value := by
    have hrow := quittingTerminalDeviationDebt_singleOptional_eq_endpoint_row
      final root optional choice negative hsure hoptionalFinal who
    rw [htie who,
      singleOptional_endpoint_eq_stretch original final alpha hagrees optional who choice negative,
      singleOptional_endpoint_eq_stretch original final alpha hagrees optional who choice
        (!negative)] at hrow
    change value = max 0 (rowValue probability
      (Math.signedEndpointGapStretch alpha (left who))
      (Math.signedEndpointGapStretch alpha (right who))) at hrow
    rcases le_total 0 (rowValue probability
      (Math.signedEndpointGapStretch alpha (left who))
      (Math.signedEndpointGapStretch alpha (right who))) with hnonneg | hnonpos
    · rw [max_eq_right hnonneg] at hrow
      exact hrow.symm
    · rw [max_eq_left hnonpos] at hrow
      exact False.elim ((ne_of_gt hpositive) hrow)
  have hrightNegative_leftPositive (who : Fin 4) (hright : right who < 0) :
      0 < left who := by
    have hrightStretch := (Math.signedEndpointGapStretch_neg_iff_of_abs_le_two
      halpha.le (hbound who).2).mpr hright
    by_contra hnot
    have hleftStretch : Math.signedEndpointGapStretch alpha (left who) ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      exact hnot ((Math.signedEndpointGapStretch_pos_iff_of_abs_le_two
        halpha.le (hbound who).1).mp hpos)
    have hsumNonpos := add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos hp.le hleftStretch)
      (mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1 - probability)
        hrightStretch.le)
    have h := hcontact who
    unfold rowValue at h
    rw [h] at hsumNonpos
    exact (not_le_of_gt hpositive) hsumNonpos
  have hexists : ∃ other : Fin 4, other ≠ optional ∧ right other < 0 := by
    by_contra hnone
    have hright (who : Fin 4) : 0 ≤ right who := by
      by_cases hwho : who = optional
      · subst who
        simp only [right, quittingSingleOptionalDebtEndpoint, ite_true]
        split_ifs
        · exact le_rfl
        · exact hoptionalOld.le
      · apply le_of_not_gt
        intro hnegative
        exact hnone ⟨who, hwho, hnegative⟩
    have hrows (who : Fin 4) :
        (left who < 0 ∧ 0 < right who) ∨ (0 ≤ left who ∧ 0 ≤ right who) := by
      by_cases hleft : left who < 0
      · left
        refine ⟨hleft, ?_⟩
        have hrightStretchNonpos : right who ≤ 0 → False := by
          intro hnonpos
          have hzero : right who = 0 := le_antisymm hnonpos (hright who)
          have hleftStretch := (Math.signedEndpointGapStretch_neg_iff_of_abs_le_two
            halpha.le (hbound who).1).mpr hleft
          have h := hcontact who
          rw [hzero, Math.signedEndpointGapStretch_zero] at h
          unfold rowValue at h
          have hnegative : probability * Math.signedEndpointGapStretch alpha (left who) < 0 :=
            mul_neg_of_pos_of_neg hp hleftStretch
          linarith
        exact lt_of_not_ge hrightStretchNonpos
      · exact Or.inr ⟨le_of_not_gt hleft, hright who⟩
    have hreversing : ∃ who, left who < 0 ∧ 0 < right who := by
      refine ⟨core, ?_, ?_⟩
      · simpa only [left, quittingSingleOptionalDebtEndpoint, ite_eq_right hcore] using hnOld
      · simpa only [right, quittingSingleOptionalDebtEndpoint, ite_eq_right hcore] using hpOld
    have hoptional : ∃ who, (left who = 0 ∧ 0 < right who) ∨
        (0 < left who ∧ right who = 0) := by
      refine ⟨optional, ?_⟩
      cases negative <;> cases hchoice : choice <;>
        simp only [left, right, quittingSingleOptionalDebtEndpoint, hchoice, ite_true,
          Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, ite_false]
      all_goals
        simpa only [hchoice, lt_self_iff_false, eq_self, true_and, and_true,
          false_and, and_false, false_or, or_false] using hoptionalOld
    obtain ⟨selected, hselected, hselectedOne, hweak, hstrict, _, _⟩ :=
      exists_sameOrientation_comparison hpositive hhalf halpha halpham hp hp1
        left right hbound hrows hcontact hreversing hoptional
    let marginal := if negative then
        quittingHazardCoin selected hselected.le hselectedOne.le
      else quittingHazardCoin (1 - selected)
        (by linarith : 0 ≤ 1 - selected) (by linarith : 1 - selected ≤ 1)
    let selectedRoot := Function.update root optional marginal
    have hselectedSure : ∀ who, who ≠ optional → (selectedRoot who true).toReal = 1 := by
      intro who hwho
      simpa only [selectedRoot, Function.update_of_ne hwho] using hsure who hwho
    have hselectedProbability : (selectedRoot optional negative).toReal = selected := by
      cases negative <;>
        simp only [selectedRoot, Function.update_self, marginal, Bool.false_eq_true, ite_false,
          ite_true, quittingHazardCoin_true_toReal, pmfBool_false_toReal, sub_sub_cancel]
    have hselectedDebt (who : Fin 4) :
        quittingTerminalDeviationDebt original
            (quittingOneDateThenNeverProfile original selectedRoot) who =
          max 0 (rowValue selected (left who) (right who)) := by
      rw [quittingTerminalDeviationDebt_singleOptional_eq_endpoint_row
        original selectedRoot optional choice negative hselectedSure hoptionalOld.le who,
        hselectedProbability]
      rfl
    exact not_fullDebt_comparison_below_positiveInf original horiginalBound hpositive hinfOrder
      (quittingOneDateThenNeverProfile original selectedRoot)
      (fun who => by rw [hselectedDebt who]; exact hweak who)
      (by obtain ⟨who, hwho⟩ := hstrict; exact ⟨who, by rw [hselectedDebt who]; exact hwho⟩)
  obtain ⟨other, hotherCore, hotherNegative⟩ := hexists
  have hotherPositive := hrightNegative_leftPositive other hotherNegative
  have hdifferent : core ≠ other := by
    intro heq
    subst other
    have h : 0 < right core := by
      simpa only [right, quittingSingleOptionalDebtEndpoint, ite_eq_right hcore] using hpOld
    exact (not_lt_of_ge h.le) hotherNegative
  have hotherNegGap : quittingDirectedMembershipGap original other false
      (quittingSingleOptionalAction optional (!negative)) < 0 := by
    simpa only [right, quittingSingleOptionalDebtEndpoint, ite_eq_right hotherCore]
      using hotherNegative
  have hotherPosGap : 0 < quittingDirectedMembershipGap original other false
      (quittingSingleOptionalAction optional negative) := by
    simpa only [left, quittingSingleOptionalDebtEndpoint, ite_eq_right hotherCore]
      using hotherPositive
  have hotherNegFinal : quittingDirectedMembershipGap final other false
      (quittingSingleOptionalAction optional (!negative)) < 0 := by
    have h := singleOptional_endpoint_eq_stretch
      original final alpha hagrees optional other choice (!negative)
    simp only [quittingSingleOptionalDebtEndpoint, ite_eq_right hotherCore] at h
    rw [h]
    exact (Math.signedEndpointGapStretch_neg_iff_of_abs_le_two halpha.le
      (abs_quittingDirectedMembershipGap_le_two original horiginalBound other false _)).mpr
        hotherNegGap
  have hotherPosFinal : 0 < quittingDirectedMembershipGap final other false
      (quittingSingleOptionalAction optional negative) := by
    have h := singleOptional_endpoint_eq_stretch
      original final alpha hagrees optional other choice negative
    simp only [quittingSingleOptionalDebtEndpoint, ite_eq_right hotherCore] at h
    rw [h]
    exact (Math.signedEndpointGapStretch_pos_iff_of_abs_le_two halpha.le
      (abs_quittingDirectedMembershipGap_le_two original horiginalBound other false _)).mpr
        hotherPosGap
  cases negative with
  | false =>
      exact ⟨core, other, hcore, hotherCore, hdifferent,
        hnOld, hpOld, hotherNegGap, hotherPosGap, hnFinal, hpFinal,
        hotherNegFinal, hotherPosFinal⟩
  | true =>
      exact ⟨other, core, hotherCore, hcore, Ne.symm hdifferent,
        hotherNegGap, hotherPosGap, hnOld, hpOld,
        hotherNegFinal, hotherPosFinal, hnFinal, hpFinal⟩

end GameTheory
