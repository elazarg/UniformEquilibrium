import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineNashExistence
import UniformEquilibrium.Quitting.Root.SinglePivotNormalization

/-! # The single-pivot scalar obstruction in finite timing menus -/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def IsSinglePivotSingletonTable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) : Prop :=
  ∀ who, reward (quittingSingletonTerminal who) who = if who = pivot then 1 else 0

omit [Fintype ι] in
/-- Normalizing at a positive singleton gives the same player's unit singleton vector. -/
theorem singlePivotNormalized_isSinglePivotSingletonTable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pivot : ι) (hpivot : 0 < reward (quittingSingletonTerminal pivot) pivot) :
    IsSinglePivotSingletonTable (quittingSinglePivotNormalizedReward reward pivot) pivot := by
  intro who
  exact quittingSoloReward_singlePivotNormalized reward pivot who hpivot.ne'

theorem singlePivot_nonpivot_fullCap_eq_menuCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    {who : ι} (hne : who ≠ pivot) :
    quittingContinuationBestResponseValue reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) who =
      quittingFiniteDeadlineReplyCap reward deadline mixed who := by
  rw [quittingContinuationBestResponseValue_finiteDeadlineTimingProfile_eq_max,
    hcanonical who, if_neg hne, mul_zero, add_zero]
  apply max_eq_left
  exact quittingFiniteDeadline_purePayoff_le_replyCap reward deadline mixed who none

theorem singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingContinuationBestResponseValue reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot =
      max (quittingFiniteDeadlineReplyCap reward deadline mixed pivot)
        (quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot +
          quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot) := by
  rw [quittingContinuationBestResponseValue_finiteDeadlineTimingProfile_eq_max,
    hcanonical pivot, if_pos rfl, mul_one]

theorem singlePivot_nonpivot_fullDebt_eq_menuDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    {who : ι} (hne : who ≠ pivot) :
    quittingTerminalDeviationDebt reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) who =
      quittingFiniteDeadlineMenuDebt reward deadline mixed who := by
  unfold quittingTerminalDeviationDebt quittingFiniteDeadlineMenuDebt
  rw [singlePivot_nonpivot_fullCap_eq_menuCap reward pivot hcanonical deadline mixed hne]

theorem singlePivot_pivot_fullDebt_eq_max_menuDebt_scalar
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingTerminalDeviationDebt reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot =
      max (quittingFiniteDeadlineMenuDebt reward deadline mixed pivot)
        (quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot +
          quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot -
          quittingTerminalPayoff reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot) := by
  unfold quittingTerminalDeviationDebt quittingFiniteDeadlineMenuDebt
  rw [singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever
    reward pivot hcanonical deadline mixed]
  rcases le_total
      (quittingFiniteDeadlineReplyCap reward deadline mixed pivot)
      (quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot +
        quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
  · rw [max_eq_left h, max_eq_left (by linarith)]

theorem singlePivot_fullExploitability_eq_max_menuExploitability_scalar
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingTerminalExploitability reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) =
      max (quittingFiniteDeadlineMenuExploitability reward deadline mixed)
        (quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot +
          quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot -
          quittingTerminalPayoff reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot) := by
  rw [quittingTerminalExploitability_eq_max_debt]
  let scalar := quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot +
    quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot -
    quittingTerminalPayoff reward
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot
  apply le_antisymm
  · apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    by_cases hwho : who = pivot
    · subst who
      rw [singlePivot_pivot_fullDebt_eq_max_menuDebt_scalar
        reward pivot hcanonical deadline mixed]
      exact max_le_max
        (QuittingBoundaryHolonomy.le_finitePlayerMax
          (fun player ↦ quittingFiniteDeadlineMenuDebt reward deadline mixed player) pivot)
        le_rfl
    · rw [singlePivot_nonpivot_fullDebt_eq_menuDebt
        reward pivot hcanonical deadline mixed hwho]
      exact (QuittingBoundaryHolonomy.le_finitePlayerMax
        (fun player ↦ quittingFiniteDeadlineMenuDebt reward deadline mixed player) who).trans
          (le_max_left _ _)
  · apply max_le
    · apply QuittingBoundaryHolonomy.finitePlayerMax_le
      intro who
      have hmenu : quittingFiniteDeadlineMenuDebt reward deadline mixed who ≤
          quittingTerminalDeviationDebt reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who := by
        unfold quittingFiniteDeadlineMenuDebt quittingTerminalDeviationDebt
        exact sub_le_sub_right
          (by
            unfold quittingFiniteDeadlineReplyCap
            apply Finset.sup'_le
            intro action _
            exact quittingTerminalPayoff_update_le_continuationBestResponseValue reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) who _)
          _
      exact hmenu.trans (QuittingBoundaryHolonomy.le_finitePlayerMax
        (fun player ↦ quittingTerminalDeviationDebt reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) player) who)
    · have hp := singlePivot_pivot_fullDebt_eq_max_menuDebt_scalar
        reward pivot hcanonical deadline mixed
      have hscalar : scalar ≤ quittingTerminalDeviationDebt reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot := by
        rw [hp]
        exact le_max_right _ _
      exact hscalar.trans (QuittingBoundaryHolonomy.le_finitePlayerMax
        (fun player ↦ quittingTerminalDeviationDebt reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) player) pivot)

theorem singlePivot_exactMenuNash_nonpivot_debt_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : IsQuittingFiniteDeadlineNash reward deadline 0 mixed)
    {who : ι} (hne : who ≠ pivot) :
    quittingTerminalDeviationDebt reward
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) who = 0 := by
  unfold quittingTerminalDeviationDebt
  rw [singlePivot_nonpivot_fullCap_eq_menuCap reward pivot hcanonical deadline mixed hne]
  have hle := hnash who
  simp only [add_zero] at hle
  have hnonneg := quittingTerminalDeviationDebt_nonneg reward
    (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
  unfold quittingTerminalDeviationDebt at hnonneg
  rw [singlePivot_nonpivot_fullCap_eq_menuCap
    reward pivot hcanonical deadline mixed hne] at hnonneg
  linarith

theorem singlePivot_exactMenuNash_pivot_debt_eq_posPart_scalar
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : IsQuittingFiniteDeadlineNash reward deadline 0 mixed) :
    quittingTerminalDeviationDebt reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot =
      max 0 (quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot +
        quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot -
        quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot) := by
  unfold quittingTerminalDeviationDebt
  rw [singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever
    reward pivot hcanonical deadline mixed]
  have hmenu := hnash pivot
  simp only [add_zero] at hmenu
  have hdebt := quittingTerminalDeviationDebt_nonneg reward
    (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot
  unfold quittingTerminalDeviationDebt at hdebt
  rw [singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever
    reward pivot hcanonical deadline mixed] at hdebt
  rcases le_total
      (quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot +
        quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot)
      (quittingFiniteDeadlineReplyCap reward deadline mixed pivot) with hlate | hreply
  · rw [max_eq_left hlate] at hdebt ⊢
    have heq : quittingFiniteDeadlineReplyCap reward deadline mixed pivot =
        quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot := by
      linarith
    rw [heq, max_eq_left (by linarith [hlate])]
    ring
  · rw [max_eq_right hreply] at hdebt ⊢
    rw [max_eq_right hdebt]

theorem singlePivot_exactMenuNash_pivot_debt_le_deletedNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : IsQuittingFiniteDeadlineNash reward deadline 0 mixed) :
    quittingTerminalDeviationDebt reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot ≤
      quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot := by
  rw [singlePivot_exactMenuNash_pivot_debt_eq_posPart_scalar
    reward pivot hcanonical deadline mixed hnash]
  have hnever := quittingFiniteDeadline_purePayoff_le_replyCap
    reward deadline mixed pivot none
  change quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot ≤
    quittingFiniteDeadlineReplyCap reward deadline mixed pivot at hnever
  have hmenu := hnash pivot
  simp only [add_zero] at hmenu
  have hD : 0 ≤ quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot := by
    unfold quittingFiniteDeadlineOpponentNeverProduct quittingOpponentNeverProduct
    exact Finset.prod_nonneg fun who _ ↦
      Math.Probability.CompactStoppingLaw.realMass_nonneg _ _
  rw [max_le_iff]
  constructor
  · exact hD
  · linarith

theorem singlePivot_mixedNash_pivot_neverSupport_debt_eq_deletedNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash mixed)
    (hsupport : 0 < (mixed pivot none).toReal) :
    quittingTerminalDeviationDebt reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot =
      quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot := by
  have hmenu := mixedNash_isQuittingFiniteDeadlineNash reward deadline mixed hnash
  rw [singlePivot_exactMenuNash_pivot_debt_eq_posPart_scalar
    reward pivot hcanonical deadline mixed hmenu,
    finiteDeadline_mixedNash_neverSupport_payoff_eq_never
      reward deadline mixed pivot hnash hsupport]
  simp only [add_sub_cancel_left]
  rw [max_eq_right]
  unfold quittingFiniteDeadlineOpponentNeverProduct quittingOpponentNeverProduct
  exact Finset.prod_nonneg fun who _ ↦
    Math.Probability.CompactStoppingLaw.realMass_nonneg _ _

theorem singlePivot_exactMenuNash_pivot_debt_eq_deletedNever_of_payoff_eq_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : IsQuittingFiniteDeadlineNash reward deadline 0 mixed)
    (heq : quittingTerminalPayoff reward
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot =
        quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot) :
    quittingTerminalDeviationDebt reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot =
      quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot := by
  rw [singlePivot_exactMenuNash_pivot_debt_eq_posPart_scalar
    reward pivot hcanonical deadline mixed hnash, heq, add_sub_cancel_left, max_eq_right]
  unfold quittingFiniteDeadlineOpponentNeverProduct quittingOpponentNeverProduct
  exact Finset.prod_nonneg fun who _ ↦
    Math.Probability.CompactStoppingLaw.realMass_nonneg _ _

/-- Deadline zero is genuinely included: its unique menu law has zero menu
exploitability and unit unrestricted pivot debt. -/
theorem exists_singlePivot_deadlineZero_menuExploitability_zero_pivotDebt_one
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction 0),
      IsQuittingFiniteDeadlineNash reward 0 0 mixed ∧
      quittingFiniteDeadlineMenuExploitability reward 0 mixed = 0 ∧
      quittingTerminalDeviationDebt reward
        (quittingFiniteDeadlineTimingProfile reward 0 mixed) pivot = 1 := by
  obtain ⟨mixed, hnash, hmenuNash⟩ := exists_exactFiniteDeadlineTimingNash reward 0
  have hmixed : ∀ who, mixed who = PMF.pure none := by
    intro who
    apply PMF.ext
    intro action
    cases action with
    | none =>
        have hpure : (PMF.pure none : PMF (QuittingFiniteDeadlineTimingAction 0)) none = 1 := by
          simp
        rw [hpure]
        rw [(mixed who).apply_eq_one_iff]
        obtain ⟨supported, hsupported⟩ := (mixed who).support_nonempty
        have hsupportedEq : supported = none := by
          cases supported with
          | none => rfl
          | some time => exact Fin.elim0 time
        subst supported
        ext action
        have ha : action = none := by
          cases action with
          | none => rfl
          | some time => exact Fin.elim0 time
        subst action
        simp [hsupported]
    | some time => exact Fin.elim0 time
  have hsupport : 0 < (mixed pivot none).toReal := by simp [hmixed pivot]
  have hD : quittingFiniteDeadlineOpponentNeverProduct 0 mixed pivot = 1 := by
    have hdefault : (default : QuittingFiniteDeadlineTimingAction 0) = none := by
      cases (default : QuittingFiniteDeadlineTimingAction 0) with
      | none => rfl
      | some time => exact Fin.elim0 time
    unfold quittingFiniteDeadlineOpponentNeverProduct quittingOpponentNeverProduct
    simp_rw [← Math.Probability.CompactStoppingLaw.toPMF_apply_toReal]
    simp [hmixed, quittingFiniteDeadlineTimingLaw,
      quittingFiniteDeadlineTimingActionTime, hdefault]
  refine ⟨mixed, hmenuNash, ?_, ?_⟩
  · unfold quittingFiniteDeadlineMenuExploitability
    apply le_antisymm
    · apply QuittingBoundaryHolonomy.finitePlayerMax_le
      intro who
      have hle := hmenuNash who
      have hn := quittingFiniteDeadlineMenuDebt_nonneg reward 0 mixed who
      unfold quittingFiniteDeadlineMenuDebt at hn ⊢
      simp only [add_zero] at hle
      linarith
    · exact (quittingFiniteDeadlineMenuDebt_nonneg reward 0 mixed pivot).trans
        (QuittingBoundaryHolonomy.le_finitePlayerMax
          (fun who ↦ quittingFiniteDeadlineMenuDebt reward 0 mixed who) pivot)
  · rw [singlePivot_mixedNash_pivot_neverSupport_debt_eq_deletedNever
      reward pivot hcanonical 0 mixed hnash hsupport, hD]

end GameTheory
