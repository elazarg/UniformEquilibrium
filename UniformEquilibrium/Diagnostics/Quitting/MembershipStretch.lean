import MathUE.SignedEndpointStretch
import UniformEquilibrium.Diagnostics.Quitting.ScreenedMembershipDebt

/-!
# Literal membership stretching and supported directed gaps

The constructed table leaves own singleton coordinates fixed. A final table
may reselect those coordinates, but it must agree with the same constructed
stretch everywhere else. Only the constructed table inherits the displacement
bound. A quitting opponent keeps every directed-gap comparison away from the
reselected own singleton coordinates.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [DecidableEq ι]

/-- One common endpoint stretch on all paired membership reward coordinates. -/
def quittingMembershipStretchedReward
    (original : {S : Finset ι // S.Nonempty} → Payoff ι) (alpha : ℝ) :
    {S : Finset ι // S.Nonempty} → Payoff ι := fun terminal who =>
  if who ∈ terminal.val then
    if hnonempty : (terminal.val.erase who).Nonempty then
      Math.unitEndpointStretch alpha (original terminal who)
        (original ⟨terminal.val.erase who, hnonempty⟩ who)
    else original terminal who
  else
    Math.unitEndpointStretch alpha (original terminal who)
      (original ⟨insert who terminal.val, Finset.insert_nonempty who terminal.val⟩ who)

@[simp] theorem quittingMembershipStretchedReward_ownSingleton
    (original : {S : Finset ι // S.Nonempty} → Payoff ι) (alpha : ℝ) (who : ι) :
    quittingMembershipStretchedReward original alpha (quittingSingletonTerminal who) who =
      original (quittingSingletonTerminal who) who := by
  simp [quittingMembershipStretchedReward, quittingSingletonTerminal]

/-- Both orientations come from one literal pair of original reward entries. -/
theorem quittingMembershipStretchedReward_pair
    (original : {S : Finset ι // S.Nonempty} → Payoff ι) (alpha : ℝ)
    (who : ι) (opponents : Finset ι) (hnonempty : opponents.Nonempty)
    (hwho : who ∉ opponents) :
    quittingMembershipStretchedReward original alpha ⟨opponents, hnonempty⟩ who =
        Math.unitEndpointStretch alpha (original ⟨opponents, hnonempty⟩ who)
          (original ⟨insert who opponents, Finset.insert_nonempty who opponents⟩ who) ∧
      quittingMembershipStretchedReward original alpha
          ⟨insert who opponents, Finset.insert_nonempty who opponents⟩ who =
        Math.unitEndpointStretch alpha
          (original ⟨insert who opponents, Finset.insert_nonempty who opponents⟩ who)
          (original ⟨opponents, hnonempty⟩ who) := by
  constructor
  · simp [quittingMembershipStretchedReward, hwho]
  · simp [quittingMembershipStretchedReward, hwho, hnonempty]

theorem abs_quittingMembershipStretchedReward_le_one
    (original : {S : Finset ι // S.Nonempty} → Payoff ι) {alpha : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hbound : ∀ terminal who, |original terminal who| ≤ 1)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) :
    |quittingMembershipStretchedReward original alpha terminal who| ≤ 1 := by
  have hentry : original terminal who ∈ Set.Icc (-1 : ℝ) 1 :=
    abs_le.mp (hbound terminal who)
  unfold quittingMembershipStretchedReward
  split_ifs
  · exact abs_le.mpr (Math.unitEndpointStretch_mem_Icc halpha0 halpha1 hentry)
  · exact hbound terminal who
  · exact abs_le.mpr (Math.unitEndpointStretch_mem_Icc halpha0 halpha1 hentry)

/-- This bound does not apply after arbitrary own-singleton reselection. -/
theorem abs_quittingMembershipStretchedReward_sub_le
    (original : {S : Finset ι // S.Nonempty} → Payoff ι) {alpha : ℝ}
    (halpha0 : 0 ≤ alpha)
    (hbound : ∀ terminal who, |original terminal who| ≤ 1)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) :
    |quittingMembershipStretchedReward original alpha terminal who -
        original terminal who| ≤ 2 * alpha := by
  have hentry : original terminal who ∈ Set.Icc (-1 : ℝ) 1 :=
    abs_le.mp (hbound terminal who)
  unfold quittingMembershipStretchedReward
  split_ifs
  · exact Math.abs_unitEndpointStretch_sub_le halpha0 hentry
  · simp only [sub_self, abs_zero]
    linarith
  · exact Math.abs_unitEndpointStretch_sub_le halpha0 hentry

/-- The final table keeps the same original-table stretch away from own singletons. -/
def QuittingAgreesWithMembershipStretch
    (original final : {S : Finset ι // S.Nonempty} → Payoff ι) (alpha : ℝ) : Prop :=
  ∀ terminal who, terminal.val ≠ {who} →
    final terminal who = quittingMembershipStretchedReward original alpha terminal who

theorem quittingAgreesWithMembershipStretch_constructed
    (original : {S : Finset ι // S.Nonempty} → Payoff ι) (alpha : ℝ) :
    QuittingAgreesWithMembershipStretch original
      (quittingMembershipStretchedReward original alpha) alpha := by
  intro terminal who _
  rfl

variable [Fintype ι]

private theorem quittingQuitters_update_false_eq_erase (action : ι → Bool) (who : ι) :
    quittingQuitters (Function.update action who false) = (quittingQuitters action).erase who := by
  ext player
  by_cases heq : player = who
  · subst player
    simp [quittingQuitters]
  · simp [quittingQuitters, heq]

private theorem quittingQuitters_update_true_eq_insert_erase (action : ι → Bool) (who : ι) :
    quittingQuitters (Function.update action who true) =
      insert who ((quittingQuitters action).erase who) := by
  ext player
  by_cases heq : player = who
  · subst player
    simp [quittingQuitters]
  · simp [quittingQuitters, heq]

private theorem directedMembershipGap_pairDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (preferred : Bool) (action : ι → Bool)
    (hnonempty : ((quittingQuitters action).erase who).Nonempty) :
    quittingDirectedMembershipGap reward who preferred action =
      if preferred then
        reward ⟨insert who ((quittingQuitters action).erase who), Finset.insert_nonempty _ _⟩ who -
          reward ⟨(quittingQuitters action).erase who, hnonempty⟩ who
      else
        reward ⟨(quittingQuitters action).erase who, hnonempty⟩ who -
          reward ⟨insert who ((quittingQuitters action).erase who),
            Finset.insert_nonempty _ _⟩ who := by
  cases preferred <;>
    simp [quittingDirectedMembershipGap, quittingRootPayoff,
      quittingQuitters_update_false_eq_erase, quittingQuitters_update_true_eq_insert_erase,
      hnonempty]

/-- A quitting opponent removes every own-singleton coordinate from this comparison. -/
theorem quittingDirectedMembershipGap_eq_stretch_of_quittingOpponent
    (original final : {S : Finset ι // S.Nonempty} → Payoff ι) (alpha : ℝ)
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (who : ι) (preferred : Bool) (action : ι → Bool) {opponent : ι}
    (hne : opponent ≠ who) (hquit : action opponent = true) :
    quittingDirectedMembershipGap final who preferred action =
      Math.signedEndpointGapStretch alpha
        (quittingDirectedMembershipGap original who preferred action) := by
  let opponents := (quittingQuitters action).erase who
  have hopponent : opponent ∈ opponents := by
    simp [opponents, quittingQuitters, hne, hquit]
  have hnonempty : opponents.Nonempty := ⟨opponent, hopponent⟩
  have hwho : who ∉ opponents := Finset.notMem_erase who _
  have hneSingleton : opponents ≠ {who} := by
    intro heq
    apply hwho
    rw [heq]
    exact Finset.mem_singleton_self who
  have hinsertNe : insert who opponents ≠ {who} := by
    intro heq
    have hmem : opponent ∈ insert who opponents := Finset.mem_insert_of_mem hopponent
    rw [heq] at hmem
    exact hne (Finset.mem_singleton.mp hmem)
  have hfalse := hagrees ⟨opponents, hnonempty⟩ who hneSingleton
  have htrue := hagrees ⟨insert who opponents, Finset.insert_nonempty _ _⟩ who hinsertNe
  obtain ⟨hpairFalse, hpairTrue⟩ :=
    quittingMembershipStretchedReward_pair original alpha who opponents hnonempty hwho
  rw [hpairFalse] at hfalse
  rw [hpairTrue] at htrue
  rw [directedMembershipGap_pairDifference final who preferred action hnonempty,
    directedMembershipGap_pairDifference original who preferred action hnonempty]
  change (if preferred then _ - _ else _ - _) = _
  change final ⟨opponents, hnonempty⟩ who = _ at hfalse
  cases preferred <;> simp only [Bool.false_eq_true, if_false, if_true]
  · rw [hfalse, htrue]
    exact Math.unitEndpointStretch_sub_reverse alpha _ _
  · rw [hfalse, htrue]
    exact Math.unitEndpointStretch_sub_reverse alpha _ _

/-- The original table and stretch parameter are retained at every supported product draw. -/
theorem quittingDirectedMembershipGap_eq_stretch_on_support
    (original final : {S : Finset ι // S.Nonempty} → Payoff ι) (alpha : ℝ)
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (root : ι → PMF Bool) (who : ι) (preferred : Bool) {opponent : ι}
    (hne : opponent ≠ who) (hsure : (root opponent true).toReal = 1)
    (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support) :
    quittingDirectedMembershipGap final who preferred action =
      Math.signedEndpointGapStretch alpha
        (quittingDirectedMembershipGap original who preferred action) := by
  apply quittingDirectedMembershipGap_eq_stretch_of_quittingOpponent
    original final alpha hagrees who preferred action hne
  by_contra hnot
  have hfalse : action opponent = false := Bool.eq_false_of_not_eq_true hnot
  have hzeroReal : (root opponent false).toReal = 0 := by
    rw [Math.PMFProduct.pmfBool_false_toReal, hsure]
    ring
  have hzero : root opponent false = 0 := by
    exact ((ENNReal.toReal_eq_zero_iff _).mp hzeroReal).resolve_right
      ((root opponent).apply_ne_top false)
  have hproduct : pmfPi root action = 0 := by
    rw [pmfPi_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ opponent) (by rw [hfalse, hzero])
  exact (PMF.mem_support_iff _ action).mp hsupport hproduct

/-- Unit reward bounds control directed gaps even when an endpoint is all-Continue. -/
theorem abs_quittingDirectedMembershipGap_le_two
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hbound : ∀ terminal who, |reward terminal who| ≤ 1)
    (who : ι) (preferred : Bool) (action : ι → Bool) :
    |quittingDirectedMembershipGap reward who preferred action| ≤ 2 := by
  have hroot (draw : ι → Bool) : |quittingRootPayoff reward 0 draw who| ≤ 1 :=
    abs_quittingRootPayoff_le reward 0 hbound (by intro player; simp) draw who
  unfold quittingDirectedMembershipGap
  apply (abs_sub _ _).trans
  have hfirst := hroot (Function.update action who preferred)
  have hsecond := hroot (Function.update action who (!preferred))
  linarith

/-- Pointwise coherence may be tested at either table on the same supported draws. -/
theorem quittingDirectedMembershipGap_nonneg_iff_on_support
    (original final : {S : Finset ι // S.Nonempty} → Payoff ι) {alpha : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (root : ι → PMF Bool) (who : ι) (preferred : Bool) {opponent : ι}
    (hne : opponent ≠ who) (hsure : (root opponent true).toReal = 1)
    (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support) :
    0 ≤ quittingDirectedMembershipGap final who preferred action ↔
      0 ≤ quittingDirectedMembershipGap original who preferred action := by
  rw [quittingDirectedMembershipGap_eq_stretch_on_support
    original final alpha hagrees root who preferred hne hsure action hsupport]
  exact Math.signedEndpointGapStretch_nonneg_iff halpha0 halpha1

/-- Equal nonnegative directed gaps under positive stretch are zero or saturated. -/
theorem quittingDirectedMembershipGap_eq_iff_zero_or_two_on_support
    (original final : {S : Finset ι // S.Nonempty} → Payoff ι) {alpha : ℝ}
    (halpha : 0 < alpha)
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (root : ι → PMF Bool) (who : ι) (preferred : Bool) {opponent : ι}
    (hne : opponent ≠ who) (hsure : (root opponent true).toReal = 1)
    (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support)
    (hgap : 0 ≤ quittingDirectedMembershipGap original who preferred action) :
    quittingDirectedMembershipGap final who preferred action =
        quittingDirectedMembershipGap original who preferred action ↔
      quittingDirectedMembershipGap original who preferred action = 0 ∨
        quittingDirectedMembershipGap original who preferred action = 2 := by
  rw [quittingDirectedMembershipGap_eq_stretch_on_support
    original final alpha hagrees root who preferred hne hsure action hsupport]
  exact Math.signedEndpointGapStretch_eq_self_iff_of_nonneg halpha hgap

end GameTheory
