import UniformEquilibrium.Quitting.Classification.QuietExtension.ExecutableWithdrawalQuietFiniteWords
import UniformEquilibrium.Quitting.Classification.QuietExtension.ExecutableAdvancingWeights
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockBlockDeletion

/-! # Bounded executable withdrawal source smoke evidence

Reproduce from the repository root, using the shared dependency cache:

```sh
LEAN_NUM_THREADS=1 lake --quiet --iofail build Experiments.Quitting.WithdrawalExecutableSmoke
lake env lean -j1 --run Experiments/Quitting/WithdrawalExecutableSmoke.lean
```

The fixed literal rational tables test exact primal/dual security optimization
(including zero hazard), advancing-only and empty-row feasibility, all five
full withdrawal kinds, zero- and one-date child words, and an F/J-only table
with actual positive singleton one, Never excess two and computed K two.
The selected child word's acceptance at accuracy/K and actual rational Never
atom are checked without changing the calendar or dropping late/Never replies.

Every raw feasibility witness is a proof about the actual finite table and
is erased. Runtime data are rational coefficients, exact selectors, weights,
security values, K, words and atoms; no selected real optimizer/profile/cap
or Classical Real-valued data are supplied to execution. The generic source
and correctness interfaces are imported integrated owners, not defined here.

Success prints nothing. Any failed assertion raises IO.userError. This is a
bounded collection of runtime fixtures, not a general runtime or complexity
theorem, executable infeasibility decision, universal certificate producer
or prescribed-target algorithm. Exact exhaustive fallback searches can be
expensive or exhaust interpreter resources; a successful run would verify
only these fixed instances. Named compilation alone is not runtime success.
-/

namespace Experiments.Quitting.WithdrawalExecutableSmoke

open GameTheory GameTheory.ExecutableWithdrawal
open scoped BigOperators

private abbrev deleted (who : Fin 2) : Prop := who = 1

private def childZero : QuittingChildPlayer deleted := ⟨0, by decide⟩

private def outsideOne : {who : Fin 2 // deleted who} := ⟨1, rfl⟩

private instance : Nonempty (QuittingChildPlayer deleted) := ⟨childZero⟩

private instance : Nonempty {who : Fin 2 // deleted who} := ⟨outsideOne⟩

private def label : QuittingChildPlayer deleted ≃ Fin 1 where
  toFun _ := 0
  invFun _ := childZero
  left_inv who := by
    apply Subtype.ext
    apply Fin.ext
    have hne : who.val ≠ (1 : Fin 2) := who.property
    have hnat : who.val.val ≠ 1 := by
      intro h
      exact hne (Fin.ext h)
    have hlt := who.val.isLt
    change 0 = who.val.val
    omega
  right_inv index := by
    apply Fin.ext
    have hlt := index.isLt
    change 0 = index.val
    omega

private def zeroParent : RationalQuittingReward 2 := fun _ _ => 0

private def nonzeroParent : RationalQuittingReward 2 :=
  fun _ who => if who = 0 then 1 else 0

/-- Every finite exit pays child zero one and outsider one two. Never still pays zero. -/
private def residualParent : RationalQuittingReward 2 :=
  fun _ who => if who = 0 then 1 else 2

/-- The actual F/J source rows are zero on the outside recipient. No N row is assumed.
The zero feasible witness is erased; it is NOT an input to the runtime weight selector. -/
private theorem residualSource (kind : WithdrawalFutureJoinKind) :
    FutureJoinSource residualParent deleted (fun _ => kind) := by
  intro outside
  have houtside (terminal :
      {A : Finset (Option (QuittingChildPlayer deleted)) // A.Nonempty}) :
      quittingChildWithOutsiderReward (rationalQuittingRewardToReal residualParent)
        deleted outside terminal none = 2 := by
    rw [quittingChildWithOutsiderReward_apply_original,
      quittingChildWithOutsiderOriginalEmbedding_none]
    change (residualParent _ outside.val : ℝ) = 2
    rw [show outside.val = (1 : Fin 2) from outside.property]
    norm_num [residualParent]
  have hfutureZero : kind.futureWeight 0 = 0 := by
    cases kind <;> rfl
  refine ⟨{
    advanceWeight := 0
    withdrawalWeight := 0
    advanceWeight_nonneg := fun _ => le_rfl
    withdrawalWeight_nonneg := fun _ => le_rfl
    future_row := ?_
    join_row := ?_ }⟩
  · intro A hA
    simp only [houtside, sub_self, Pi.zero_apply, zero_mul, hfutureZero,
      add_zero, Finset.sum_const_zero, le_refl]
  · intro A hA
    simp only [houtside, sub_self, Pi.zero_apply, zero_mul,
      add_zero, Finset.sum_const_zero, le_refl]

private noncomputable def outsideZeroCappedCertificate
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hzero : ∀ terminal, reward terminal none = 0) :
    CappedClockParentRewardCertificate reward :=
  cappedClockParentRewardCertificate_zero_of_blockDispensable reward (by
    constructor
    · intro terminal hterminal _
      rw [hzero, hzero]
    · rw [hzero]
      apply le_quittingBlockContinueFloor reward {none} none le_rfl
      intro terminal hterminal _
      rw [hzero])

private theorem outsideZeroFullCertificate
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hzero : ∀ terminal, reward terminal none = 0) (kind : WithdrawalFutureJoinKind) :
    Nonempty (kind.FullCertificate reward) := by
  let certificate := outsideZeroCappedCertificate reward hzero
  cases kind
  all_goals
    refine ⟨{
      advanceWeight := certificate.weight
      withdrawalWeight := fun _ => 0
      advanceWeight_nonneg := certificate.weight_nonneg
      withdrawalWeight_nonneg := fun _ => le_rfl
      never_row := by
        simpa using certificate.never_row
      future_row := by
        intro A hA
        simpa using certificate.future_row A hA
      join_row := by
        intro A hA
        simpa using certificate.join_row A hA }⟩

private theorem fullSource_of_outside_zero (reward : RationalQuittingReward 2)
    (hzero : ∀ terminal, reward terminal 1 = 0) (kind : WithdrawalFutureJoinKind) :
    FullSource reward deleted (fun _ => kind) := by
  intro outside
  apply outsideZeroFullCertificate
  intro terminal
  rw [quittingChildWithOutsiderReward_apply_original,
    quittingChildWithOutsiderOriginalEmbedding_none]
  change (reward _ outside.val : ℝ) = 0
  have houtside : outside.val = (1 : Fin 2) := outside.property
  rw [houtside, hzero]
  norm_num

private theorem zeroSource (kind : WithdrawalFutureJoinKind) :
    FullSource zeroParent deleted (fun _ => kind) :=
  fullSource_of_outside_zero zeroParent (fun _ => rfl) kind

private theorem nonzeroSource (kind : WithdrawalFutureJoinKind) :
    FullSource nonzeroParent deleted (fun _ => kind) := by
  apply fullSource_of_outside_zero
  intro terminal
  norm_num [nonzeroParent]

private def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

/-- All five actual full-source computations on the zero parent and its one child. -/
def checkZeroKind (kind : WithdrawalFutureJoinKind) : IO Unit := do
  let weights := fullSourceWeights zeroParent deleted (fun _ => kind) (zeroSource kind) outsideOne
  ensure (decide (∀ coordinate, weights coordinate = 0)) "zero full-source weights"
  let amplification := fullAmplification zeroParent deleted (fun _ => kind) (zeroSource kind)
  ensure (decide (amplification = 1)) "zero full-source amplification"
  let childReward := restriction zeroParent deleted outsideOne
  ensure (decide (neverExcess kind childReward weights = 0)) "zero Never excess"
  ensure (decide (∀ child, debtWeight kind weights child = 0)) "zero debt coefficients"
  let word := fullWord zeroParent deleted (fun _ => kind) (zeroSource kind)
    label (by decide) 1 (by decide)
  ensure word.isEmpty "zero selected word is not the empty calendar"
  let searchedReward := rationalQuittingDeletedChildReward zeroParent deleted label
  ensure (rationalQuittingFiniteWordAccepts searchedReward (1 / amplification) word)
    "zero selected child word rejected"

/-- A literal nonzero child singleton forces a one-date word at accuracy one half. -/
def checkNonzeroWord : IO Unit := do
  let kind := WithdrawalFutureJoinKind.deadline
  let amplification :=
    fullAmplification nonzeroParent deleted (fun _ => kind) (nonzeroSource kind)
  ensure (decide (amplification = 1)) "nonzero full-source amplification"
  let word := fullWord nonzeroParent deleted (fun _ => kind) (nonzeroSource kind)
    label (by decide) (1 / 2) (by norm_num)
  ensure (decide (word.length = 1)) "nonzero selected calendar length"
  ensure (decide ((word.getD 0 (rationalQuittingZeroRoot 1)).probability 0 = 1))
    "nonzero selected hazard is not sure Quit"
  let searchedReward := rationalQuittingDeletedChildReward nonzeroParent deleted label
  ensure (rationalQuittingFiniteWordAccepts searchedReward ((1 / 2) / amplification) word)
    "nonzero selected child word rejected"

/-- A genuine omitted-Never computation: zero selected F/J weights, excess two,
positive actual singleton one, corrected pivot coefficient and K two, then the
SAME child word accepted at accuracy/K. Deadline avoids a second security search. -/
def checkNeverResidual : IO Unit := do
  let kind := WithdrawalFutureJoinKind.deadline
  let source := residualSource kind
  let childReward := restriction residualParent deleted outsideOne
  let weights := futureJoinSourceWeights residualParent deleted (fun _ => kind)
    source outsideOne
  ensure (decide (∀ coordinate, weights coordinate = 0)) "omitted-Never selected F/J weights"
  ensure (decide (singleton childReward childZero = 1)) "omitted-Never actual pivot singleton"
  ensure (decide (outsideCoefficient childReward none = 2)) "omitted-Never actual outside solo"
  ensure (decide (neverExcess kind childReward weights = 2)) "omitted-Never computed residual"
  ensure (decide (debtWeight kind weights childZero = 0)) "omitted-Never uncorrected debt"
  ensure (decide (correctedWeight kind childReward weights childZero childZero = 2))
    "omitted-Never computed pivot correction"
  let amplification :=
    futureJoinAmplification residualParent deleted (fun _ => kind) source childZero
  ensure (decide (amplification = 2)) "omitted-Never computed amplification"
  let accuracy : ℚ := 1
  let word := futureJoinWord residualParent deleted (fun _ => kind) source childZero
    label (by decide) accuracy (by decide)
  ensure (decide (word.length = 1)) "omitted-Never selected calendar length"
  ensure (decide ((word.getD 0 (rationalQuittingZeroRoot 1)).probability 0 = 1))
    "omitted-Never selected child hazard"
  let searchedReward := rationalQuittingDeletedChildReward residualParent deleted label
  ensure (rationalQuittingFiniteWordAccepts searchedReward (accuracy / amplification) word)
    "omitted-Never selected child word rejected at accuracy/K"
  ensure (decide (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
    word.length 0 none = 0)) "omitted-Never selected child has positive Never mass"

/-- Actual exact security optimization, retaining the zero-hazard endpoint. -/
def checkSecurity : IO Unit := do
  let reward : Reward (Fin 1) := fun _ _ => 0
  ensure (decide (Fintype.card {A : Finset (Fin 1) // A.Nonempty ∧ (0 : Fin 1) ∉ A} = 0))
    "one-player passive-row family is not empty"
  ensure (decide (patientFloor reward 0 = 0 ∧ zeroFloor reward 0 = 0)) "finite zero floors"
  ensure (decide (securityRow reward 0 0 none = 0 ∧ securityRow reward 0 1 none = 0))
    "security endpoint singleton rows"
  let solution := securitySolution reward 0
  ensure (decide (solution.1 0 = 0 ∧ solution.1 1 - solution.1 2 = 0))
    "computed security hazard/value"
  ensure (decide (solution.2 none = 0 ∧ solution.2 (some none) = 1))
    "computed exact security dual"
  ensure (Math.LinearProgramming.rationalPrimalDualAccepts
    (securityMatrix reward 0) (securityRhs reward 0) securityObjective solution)
    "computed security primal/dual rejected"

/-- Single-block source selection and a literal empty-row feasibility endpoint. -/
def checkAdvancingAndEmptyRows : IO Unit := do
  let reward : Reward (Fin 1) := fun _ _ => 0
  let weights := advancingWeights reward
    (show Nonempty (CappedClockParentRewardCertificate (toReal reward)) from
      ⟨outsideZeroCappedCertificate (toReal reward) (by
        intro terminal
        norm_num only [toReal, reward, Rat.cast_zero])⟩)
  ensure (decide (weights 0 = 0)) "computed advancing-only weight"
  let emptyMatrix : Fin 0 → Fin 1 → ℚ := fun row => Fin.elim0 row
  let emptyRhs : Fin 0 → ℚ := fun row => Fin.elim0 row
  let emptySelected := Math.LinearProgramming.selectNonnegativeRationalFeasible
    emptyMatrix emptyRhs (by
      refine ⟨fun _ => (0 : ℝ), fun _ => le_rfl, ?_⟩
      intro row
      exact Fin.elim0 row)
  ensure (decide (emptySelected 0 = 0)) "computed empty-row nonnegative weight"

/-- Run exactly the fixed source/word assertions documented above. -/
def run : IO Unit := do
  checkAdvancingAndEmptyRows
  checkSecurity
  for kind in [GameTheory.WithdrawalFutureJoinKind.patient,
      .deadline, .evaluatedSecurity, .terminalSecurity, .cancellation] do
    checkZeroKind kind
  checkNonzeroWord
  checkNeverResidual

end Experiments.Quitting.WithdrawalExecutableSmoke

/-- Direct Lean --run entry point; all experiment logic remains namespaced. -/
def main : IO Unit :=
  Experiments.Quitting.WithdrawalExecutableSmoke.run
