import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalRaw
import MathUE.Probability.DiscreteHazardMixture

/-!
# Disjoint private deadline operations

The advance and withdrawal choices use separate Bernoulli coins on disjoint
source-clock events. Their one-site expectation has coefficient
`max(advanceWeight, withdrawalWeight)`, not their sum. This module concerns
legal private stopping-clock laws; payoff integration is a later adapter.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.Probability.DiscreteHazard

/-- A two-point real coin has the expected affine average. -/
private theorem expect_booleanCoin_value
    (probability : ℝ) (hzero : 0 ≤ probability) (hone : probability ≤ 1)
    (value : Bool → ℝ) :
    expect (booleanCoin probability hzero hone) value =
      probability * value true + (1 - probability) * value false := by
  rw [expect_eq_sum, Fintype.sum_bool,
    booleanCoin_true_toReal, booleanCoin_false_toReal]

/-- Pushing the coin to two possible clocks yields the same affine average. -/
private theorem expect_booleanCoin_clock
    (probability : ℝ) (hzero : 0 ≤ probability) (hone : probability ≤ 1)
    (yes no : Option ℕ) (value : Option ℕ → ℝ) :
    expect ((booleanCoin probability hzero hone).map fun choose =>
      if choose then yes else no) value =
      probability * value yes + (1 - probability) * value no := by
  rw [expect_map, expect_booleanCoin_value]
  rfl

/-- Clearing a positive common denominator recovers the unnormalized
one-operation gain. -/
private theorem weighted_coin_gain
    (weight total yes base : ℝ) (htotal : total ≠ 0) :
    total * ((weight / total) * yes +
      (1 - weight / total) * base - base) = weight * (yes - base) := by
  field_simp [htotal]
  ring

/-- At one privately sampled source clock and one independently sampled
deadline, advance only when the source is later, withdraw only when it is
exactly tied, and otherwise keep the original clock. -/
def deadlineMixedPrivateClockLaw
    (source deadline : Option ℕ) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    PMF (Option ℕ) := by
  let total := max advanceWeight withdrawalWeight
  by_cases htotalZero : total = 0
  · exact PMF.pure source
  · have htotalNonneg : 0 ≤ total := hadvance.trans (le_max_left _ _)
    have htotal : 0 < total := lt_of_le_of_ne htotalNonneg (Ne.symm htotalZero)
    have hadvanceLe : advanceWeight ≤ total := le_max_left _ _
    have hwithdrawalLe : withdrawalWeight ≤ total := le_max_right _ _
    cases deadline with
    | none => exact PMF.pure source
    | some time =>
        by_cases hbefore : (time : WithTop ℕ) < quittingStoppingTimeValue source
        · let coin := booleanCoin (advanceWeight / total)
            (div_nonneg hadvance htotal.le)
            ((div_le_one htotal).mpr hadvanceLe)
          exact coin.map fun choose => if choose then some time else source
        · by_cases htie : source = some time
          · let coin := booleanCoin (withdrawalWeight / total)
              (div_nonneg hwithdrawal htotal.le)
              ((div_le_one htotal).mpr hwithdrawalLe)
            exact coin.map fun choose => if choose then none else source
          · exact PMF.pure source

/-- A zero maximum means that both nonnegative operation weights vanish,
so the private replacement is exactly the original pure clock. -/
theorem deadlineMixedPrivateClockLaw_zero
    (source deadline : Option ℕ) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight)
    (hzero : max advanceWeight withdrawalWeight = 0) :
    deadlineMixedPrivateClockLaw source deadline advanceWeight withdrawalWeight
      hadvance hwithdrawal = PMF.pure source := by
  simp [deadlineMixedPrivateClockLaw, hzero]

/-- If the outsider deadline is Never, both operations are the identity. -/
theorem deadlineMixedPrivateClockLaw_none
    (source : Option ℕ) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    deadlineMixedPrivateClockLaw source none advanceWeight withdrawalWeight
      hadvance hwithdrawal = PMF.pure source := by
  simp [deadlineMixedPrivateClockLaw]

/-- On a strictly later source clock, the private law advances to the
deadline with probability `a/max(a,b)`. -/
theorem expect_deadlineMixedPrivateClockLaw_of_before
    (source : Option ℕ) (time : ℕ)
    (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight)
    (htotal : 0 < max advanceWeight withdrawalWeight)
    (hbefore : (time : WithTop ℕ) < quittingStoppingTimeValue source)
    (value : Option ℕ → ℝ) :
    expect (deadlineMixedPrivateClockLaw source (some time)
      advanceWeight withdrawalWeight hadvance hwithdrawal) value =
      (advanceWeight / max advanceWeight withdrawalWeight) * value (some time) +
        (1 - advanceWeight / max advanceWeight withdrawalWeight) * value source := by
  have htotalNe : max advanceWeight withdrawalWeight ≠ 0 := ne_of_gt htotal
  simpa [deadlineMixedPrivateClockLaw, htotalNe, hbefore] using
    (expect_booleanCoin_clock
      (advanceWeight / max advanceWeight withdrawalWeight)
      (div_nonneg hadvance htotal.le)
      ((div_le_one htotal).mpr (le_max_left advanceWeight withdrawalWeight))
      (some time) source value)

/-- On the finite deadline atom, the private law withdraws to Never with
probability `b/max(a,b)`. -/
theorem expect_deadlineMixedPrivateClockLaw_of_tie
    (time : ℕ) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight)
    (htotal : 0 < max advanceWeight withdrawalWeight)
    (value : Option ℕ → ℝ) :
    expect (deadlineMixedPrivateClockLaw (some time) (some time)
      advanceWeight withdrawalWeight hadvance hwithdrawal) value =
      (withdrawalWeight / max advanceWeight withdrawalWeight) * value none +
        (1 - withdrawalWeight / max advanceWeight withdrawalWeight) *
          value (some time) := by
  have htotalNe : max advanceWeight withdrawalWeight ≠ 0 := ne_of_gt htotal
  simpa [deadlineMixedPrivateClockLaw, htotalNe, quittingStoppingTimeValue] using
    (expect_booleanCoin_clock
      (withdrawalWeight / max advanceWeight withdrawalWeight)
      (div_nonneg hwithdrawal htotal.le)
      ((div_le_one htotal).mpr (le_max_right advanceWeight withdrawalWeight))
      none (some time) value)

/-- Exact one-site conditional identity. The coefficient is `max(a,b)`
because advancing and atom withdrawal are selected on disjoint source-clock
events. It holds for any payoff function of the resulting clock. -/
theorem deadlineMixedPrivateClockLaw_gain_identity
    (source deadline : Option ℕ) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight)
    (value : Option ℕ → ℝ) :
    max advanceWeight withdrawalWeight *
        (expect (deadlineMixedPrivateClockLaw source deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal) value -
          value source) =
      advanceWeight * (value (cappedStoppingClock source deadline) - value source) +
        withdrawalWeight *
          (value (deadlineWithdrawnClock source deadline) - value source) := by
  let total := max advanceWeight withdrawalWeight
  by_cases htotalZero : total = 0
  · have ha : advanceWeight = 0 := by
      have hle : advanceWeight ≤ 0 := (le_max_left _ _).trans_eq htotalZero
      exact le_antisymm hle hadvance
    have hb : withdrawalWeight = 0 := by
      have hle : withdrawalWeight ≤ 0 := (le_max_right _ _).trans_eq htotalZero
      exact le_antisymm hle hwithdrawal
    simp [ha, hb, deadlineMixedPrivateClockLaw_zero]
  have htotal : 0 < total := by
    have hnonneg : 0 ≤ total := hadvance.trans (le_max_left _ _)
    exact lt_of_le_of_ne hnonneg (Ne.symm htotalZero)
  have htotalNe : total ≠ 0 := ne_of_gt htotal
  cases deadline with
  | none =>
      simp [deadlineMixedPrivateClockLaw_none, deadlineWithdrawnClock_none,
        cappedStoppingClock, quittingStoppingTimeValue]
  | some time =>
      by_cases hbefore : (time : WithTop ℕ) < quittingStoppingTimeValue source
      · have hsource : source ≠ some time := by
          intro h
          subst source
          exact (lt_irrefl _) hbefore
        have hcap : cappedStoppingClock source (some time) = some time := by
          have hnot : ¬ quittingStoppingTimeValue source ≤ (time : WithTop ℕ) :=
            not_le.mpr hbefore
          change (if quittingStoppingTimeValue source ≤ (time : WithTop ℕ)
            then source else some time) = some time
          exact ite_eq_right hnot
        have hwithdraw : deadlineWithdrawnClock source (some time) = source :=
          deadlineWithdrawnClock_some_ne source time hsource
        rw [hcap, hwithdraw, sub_self, mul_zero, add_zero]
        rw [expect_deadlineMixedPrivateClockLaw_of_before source time
          advanceWeight withdrawalWeight hadvance hwithdrawal htotal hbefore value]
        exact weighted_coin_gain advanceWeight total (value (some time))
          (value source) htotalNe
      · by_cases htie : source = some time
        · subst source
          have hcap : cappedStoppingClock (some time) (some time) = some time := by
            simp [cappedStoppingClock]
          rw [hcap, sub_self, mul_zero, zero_add]
          rw [deadlineWithdrawnClock_some_eq (some time) time rfl]
          rw [expect_deadlineMixedPrivateClockLaw_of_tie time
            advanceWeight withdrawalWeight hadvance hwithdrawal htotal value]
          exact weighted_coin_gain withdrawalWeight total (value none)
            (value (some time)) htotalNe
        · have hcap : cappedStoppingClock source (some time) = source := by
            have hle : quittingStoppingTimeValue source ≤ (time : WithTop ℕ) :=
              le_of_not_gt hbefore
            change (if quittingStoppingTimeValue source ≤ (time : WithTop ℕ)
              then source else some time) = source
            exact ite_eq_left hle
          have hwithdraw : deadlineWithdrawnClock source (some time) = source :=
            deadlineWithdrawnClock_some_ne source time htie
          have hlaw : deadlineMixedPrivateClockLaw source (some time)
              advanceWeight withdrawalWeight hadvance hwithdrawal = PMF.pure source := by
            simp [deadlineMixedPrivateClockLaw, hbefore, htie]
          simp [hlaw, hcap, hwithdraw]

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Replace just one child clock, keeping the outsider quiet. -/
def deadlinePrivateChildClocks (times : ι → Option ℕ) (i : ι)
    (newClock : Option ℕ) : Option ι → Option ℕ
  | none => none
  | some j => if j = i then newClock else times j

/-- The generic max-weight identity applied to the *actual* evaluated
quitting payoff of one deterministic tuple. It does not yet integrate over
independent laws or compare the outsider gain. -/
theorem deadlineMixedPrivateClockLaw_evaluatedGain_identity
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι)
    (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    max advanceWeight withdrawalWeight *
        (expect (deadlineMixedPrivateClockLaw (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal)
          (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
            (deadlinePrivateChildClocks times i clock) (some i)) -
          quittingPureClockEvaluatedPayoff reward evaluation
            (quietParentClocks times) (some i)) =
      advanceWeight * cappedClockActualEvaluatedChildGain
          reward evaluation times deadline i +
        withdrawalWeight * deadlineWithdrawalActualEvaluatedChildGain
          reward evaluation times deadline i := by
  have hbase : deadlinePrivateChildClocks times i (times i) =
      quietParentClocks times := by
    funext player
    cases player with
    | none => rfl
    | some j => by_cases h : j = i <;> simp [deadlinePrivateChildClocks,
        quietParentClocks, h]
  have hcap : deadlinePrivateChildClocks times i
      (cappedStoppingClock (times i) deadline) =
      cappedChildParentClocks times deadline i := by
    funext player
    cases player with
    | none => rfl
    | some j => by_cases h : j = i <;> simp [deadlinePrivateChildClocks,
        cappedChildParentClocks, h]
  have hwithdraw : deadlinePrivateChildClocks times i
      (deadlineWithdrawnClock (times i) deadline) =
      withdrawnChildParentClocks times deadline i := by
    funext player
    cases player with
    | none => rfl
    | some j => by_cases h : j = i <;> simp [deadlinePrivateChildClocks,
        withdrawnChildParentClocks, h]
  simpa only [hbase, hcap, hwithdraw, cappedClockActualEvaluatedChildGain,
    deadlineWithdrawalActualEvaluatedChildGain] using
    (deadlineMixedPrivateClockLaw_gain_identity (times i) deadline
      advanceWeight withdrawalWeight hadvance hwithdrawal
      (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
        (deadlinePrivateChildClocks times i clock) (some i)))

/-- This is one legal private child stopping law: it samples the child's
original clock and an independent outsider deadline, then samples only the
appropriate operation coin. No opponent clock enters the construction. -/
def deadlineMixedPrivateReplacementLaw
    (sourceLaw outsideLaw : PMF (Option ℕ))
    (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    PMF (Option ℕ) :=
  sourceLaw.bind fun source =>
    outsideLaw.bind fun deadline =>
      deadlineMixedPrivateClockLaw source deadline advanceWeight withdrawalWeight
        hadvance hwithdrawal

/-- Bounded integration exposes the two independent source draws and the
disjoint conditional coin. This does not yet integrate over opponent clocks. -/
theorem expect_deadlineMixedPrivateReplacementLaw_of_bounded
    (sourceLaw outsideLaw : PMF (Option ℕ))
    (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight)
    (value : Option ℕ → ℝ) {bound : ℝ}
    (hvalue : ∀ clock, |value clock| ≤ bound) :
    expect (deadlineMixedPrivateReplacementLaw sourceLaw outsideLaw
      advanceWeight withdrawalWeight hadvance hwithdrawal) value =
      expect sourceLaw fun source =>
        expect outsideLaw fun deadline =>
          expect (deadlineMixedPrivateClockLaw source deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal) value := by
  unfold deadlineMixedPrivateReplacementLaw
  rw [expect_bind_of_bounded sourceLaw _ value hvalue]
  apply congrArg (expect sourceLaw)
  funext source
  exact expect_bind_of_bounded outsideLaw _ value hvalue

end GameTheory
