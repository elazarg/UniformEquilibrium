import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedChildDeletionAdapter

/-!
# Raw deadline-withdrawal rows

The finite N/F/J reward-table predicate from the deadline-withdrawal packet.
The two arrays of nonnegative weights remain separate. The all-evaluation
comparison for positive withdrawal weights requires the atom-withdrawal
stopping-law adapter; the zero-withdrawal specialization delegates to the
existing capped-clock theorem.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance deadlineWithdrawalChildNonempty :
    Nonempty {who : Option ι // ¬ who = none} :=
  Nonempty.map (fun who => ⟨some who, Option.some_ne_none who⟩)
    (inferInstance : Nonempty ι)

/-- Withdraw precisely the atom at a finite deadline. At Never the
operation is the identity, including for a source clock equal to Never. -/
def deadlineWithdrawnClock (source deadline : Option ℕ) : Option ℕ :=
  match deadline with
  | none => source
  | some time => if source = some time then none else source

theorem deadlineWithdrawnClock_none (source : Option ℕ) :
    deadlineWithdrawnClock source none = source := rfl

theorem deadlineWithdrawnClock_some_eq
    (source : Option ℕ) (time : ℕ) (hsource : source = some time) :
    deadlineWithdrawnClock source (some time) = none := by
  simp [deadlineWithdrawnClock, hsource]

theorem deadlineWithdrawnClock_some_ne
    (source : Option ℕ) (time : ℕ) (hsource : source ≠ some time) :
    deadlineWithdrawnClock source (some time) = source := by
  simp [deadlineWithdrawnClock, hsource]

/-- A separate child experiment: only the queried child's deadline atom
is withdrawn, while the outsider remains Never. -/
def withdrawnChildParentClocks (times : ι → Option ℕ)
    (deadline : Option ℕ) (i : ι) : Option ι → Option ℕ
  | none => none
  | some j => if j = i then deadlineWithdrawnClock (times j) deadline else times j

omit [Fintype ι] [Nonempty ι] in
/-- An outsider Never deadline cannot withdraw any child atom. -/
theorem withdrawnChildParentClocks_none
    (times : ι → Option ℕ) (i : ι) :
    withdrawnChildParentClocks times none i = quietParentClocks times := by
  funext player
  cases player with
  | none => rfl
  | some j =>
      by_cases h : j = i <;>
        simp [withdrawnChildParentClocks, quietParentClocks,
          deadlineWithdrawnClock_none, h]

omit [Fintype ι] [Nonempty ι] in
/-- Only a child's exact finite deadline atom can change its clock. -/
theorem withdrawnChildParentClocks_some_of_ne
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hclock : times i ≠ some time) :
    withdrawnChildParentClocks times (some time) i = quietParentClocks times := by
  funext player
  cases player with
  | none => rfl
  | some j =>
      by_cases h : j = i
      · subst j
        simp [withdrawnChildParentClocks, quietParentClocks,
          deadlineWithdrawnClock_some_ne _ _ hclock]
      · simp [withdrawnChildParentClocks, quietParentClocks, h]

/-- The evaluated payoff gain of the literal atom-withdrawal experiment. -/
def deadlineWithdrawalActualEvaluatedChildGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) : ℝ :=
  quittingPureClockEvaluatedPayoff reward evaluation
      (withdrawnChildParentClocks times deadline i) (some i) -
    quittingPureClockEvaluatedPayoff reward evaluation
      (quietParentClocks times) (some i)

theorem deadlineWithdrawalActualEvaluatedChildGain_none
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (i : ι) :
    deadlineWithdrawalActualEvaluatedChildGain reward evaluation times none i = 0 := by
  simp [deadlineWithdrawalActualEvaluatedChildGain,
    withdrawnChildParentClocks_none]

theorem deadlineWithdrawalActualEvaluatedChildGain_some_of_ne
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hclock : times i ≠ some time) :
    deadlineWithdrawalActualEvaluatedChildGain reward evaluation times
      (some time) i = 0 := by
  simp [deadlineWithdrawalActualEvaluatedChildGain,
    withdrawnChildParentClocks_some_of_ne times time i hclock]

/-- The finite passive floor: zero and all nonempty child-coalition rewards
to `i` when `i` is outside the coalition. -/
def deadlineWithdrawalZeroFloor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) : ℝ := by
  classical
  let passive : Finset ℝ :=
    Finset.univ.image fun B : {A : Finset ι // A.Nonempty ∧ i ∉ A} =>
      reward ⟨cappedClockChildCoalition B.1,
        cappedClockChildCoalition_nonempty B.2.1⟩ (some i)
  exact (insert 0 passive).min' (Finset.insert_nonempty 0 passive)

omit [Nonempty ι] in
/-- The zero alternative keeps the evaluated singleton floor nonpositive. -/
theorem deadlineWithdrawalZeroFloor_le_zero
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) : deadlineWithdrawalZeroFloor reward i ≤ 0 := by
  classical
  unfold deadlineWithdrawalZeroFloor
  exact Finset.min'_le _ 0 (Finset.mem_insert_self 0 _)

omit [Nonempty ι] in
/-- Every finite later opponent coalition is one of the floor candidates. -/
theorem deadlineWithdrawalZeroFloor_le_passiveReward
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (B : Finset ι) (hB : B.Nonempty) (hi : i ∉ B) :
    deadlineWithdrawalZeroFloor reward i ≤
      reward ⟨cappedClockChildCoalition B,
        cappedClockChildCoalition_nonempty hB⟩ (some i) := by
  classical
  unfold deadlineWithdrawalZeroFloor
  apply Finset.min'_le
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr
    ⟨⟨B, hB, hi⟩, Finset.mem_univ _, rfl⟩

/-- The nonpositive passive floor survives a later, smaller evaluation
weight even when the later reward is negative. This is the numerical core
of the singleton atom-withdrawal case. -/
theorem deadlineWithdrawal_laterEvaluatedFloor_le
    (earlyWeight lateWeight floor reward : ℝ)
    (hearly : 0 ≤ earlyWeight) (hlate : 0 ≤ lateWeight)
    (hantitone : lateWeight ≤ earlyWeight)
    (hfloor : floor ≤ 0) (hreward : floor ≤ reward) :
    earlyWeight * floor ≤ lateWeight * reward := by
  by_cases hrewardNonneg : 0 ≤ reward
  · exact (mul_nonpos_of_nonneg_of_nonpos hearly hfloor).trans
      (mul_nonneg hlate hrewardNonneg)
  · have hfirst : earlyWeight * floor ≤ lateWeight * floor :=
      mul_le_mul_of_nonpos_right hantitone hfloor
    have hsecond : lateWeight * floor ≤ lateWeight * reward :=
      mul_le_mul_of_nonneg_left hreward hlate
    exact hfirst.trans hsecond

/-- The raw withdrawal gain floor W_i^(l⁰)(A). The erased-coalition branch
is used exactly when that coalition is nonempty. -/
def deadlineWithdrawalGainFloor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (A : Finset ι) (hA : A.Nonempty) : ℝ :=
  if _hi : i ∈ A then
    if hrest : (A.erase i).Nonempty then
      reward ⟨cappedClockChildCoalition (A.erase i),
        cappedClockChildCoalition_nonempty hrest⟩ (some i) -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ (some i)
    else
      deadlineWithdrawalZeroFloor reward i -
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
  else 0

omit [Nonempty ι] in
/-- A singleton withdrawal uses the zero-or-passive finite floor. -/
theorem deadlineWithdrawalGainFloor_singleton
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) :
    deadlineWithdrawalGainFloor reward i {i} (Finset.singleton_nonempty i) =
      deadlineWithdrawalZeroFloor reward i -
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) := by
  simp [deadlineWithdrawalGainFloor]

omit [Nonempty ι] in
/-- Outsiders to the first child coalition have no atom-withdrawal gain. -/
theorem deadlineWithdrawalGainFloor_of_not_mem
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (A : Finset ι) (hA : A.Nonempty) (hi : i ∉ A) :
    deadlineWithdrawalGainFloor reward i A hA = 0 := by
  simp [deadlineWithdrawalGainFloor, hi]

omit [Nonempty ι] in
/-- Removing a member of a nonsingleton first coalition exposes the
remaining coalition at that same deadline. -/
theorem deadlineWithdrawalGainFloor_of_erase_nonempty
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (A : Finset ι) (hi : i ∈ A)
    (hrest : (A.erase i).Nonempty) :
    deadlineWithdrawalGainFloor reward i A ⟨i, hi⟩ =
      reward ⟨cappedClockChildCoalition (A.erase i),
        cappedClockChildCoalition_nonempty hrest⟩ (some i) -
      reward ⟨cappedClockChildCoalition A,
        cappedClockChildCoalition_nonempty ⟨i, hi⟩⟩ (some i) := by
  simp [deadlineWithdrawalGainFloor, hi, hrest]

/-- Literal D-N, D-F, and D-J for one outsider. The row weights are finite
raw-table data, with no strategy or favorable-root premise. -/
structure DeadlineWithdrawalRewardCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) where
  advanceWeight : ι → ℝ
  withdrawalWeight : ι → ℝ
  advanceWeight_nonneg : ∀ i, 0 ≤ advanceWeight i
  withdrawalWeight_nonneg : ∀ i, 0 ≤ withdrawalWeight i
  never_row :
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
      ∑ i, advanceWeight i *
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
  future_row : ∀ A (hA : A.Nonempty),
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, advanceWeight i *
        (reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
          reward ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ (some i))
  join_row : ∀ A (hA : A.Nonempty),
    reward ⟨cappedClockJoinedCoalition A,
          cappedClockJoinedCoalition_nonempty A⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, (advanceWeight i *
          (reward ⟨cappedClockChildCoalition (insert i A),
              cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A,
              cappedClockChildCoalition_nonempty hA⟩ (some i)) +
        withdrawalWeight i * deadlineWithdrawalGainFloor reward i A hA)

/-- The pointwise coefficient in the deadline comparison is the larger of
the two weights, because advance and atom withdrawal occur on disjoint
private-clock events. -/
def DeadlineWithdrawalRewardCertificate.debtWeight
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : DeadlineWithdrawalRewardCertificate reward) (i : ι) : ℝ :=
  max (certificate.advanceWeight i) (certificate.withdrawalWeight i)

omit [Nonempty ι] in
theorem DeadlineWithdrawalRewardCertificate.debtWeight_nonneg
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : DeadlineWithdrawalRewardCertificate reward) (i : ι) :
    0 ≤ certificate.debtWeight i :=
  le_trans (certificate.advanceWeight_nonneg i) (le_max_left _ _)

/-- Setting every withdrawal weight to zero recovers the advancing-only
raw capped-clock certificate without changing any reward row. -/
def CappedClockParentRewardCertificate.toDeadlineWithdrawal
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : CappedClockParentRewardCertificate reward) :
    DeadlineWithdrawalRewardCertificate reward where
  advanceWeight := certificate.weight
  withdrawalWeight := fun _ => 0
  advanceWeight_nonneg := certificate.weight_nonneg
  withdrawalWeight_nonneg := by intro; exact le_rfl
  never_row := certificate.never_row
  future_row := certificate.future_row
  join_row := by
    intro A hA
    simpa using certificate.join_row A hA

/-- The exact all-evaluation behavioral comparison already checked for
the advancing-only subcone of the deadline rows. Positive withdrawal weights
require the distinct mixed-response adapter described in the dependency note. -/
theorem CappedClockParentRewardCertificate.deadlineZeroWithdrawal_debt_le
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted none -
        quittingBehaviorEvaluatedPayoff reward evaluation lifted none ≤
      ∑ i, (certificate.toDeadlineWithdrawal.debtWeight i) *
        (quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩) := by
  have hweight (i : ι) :
      certificate.toDeadlineWithdrawal.debtWeight i = certificate.weight i := by
    simp [DeadlineWithdrawalRewardCertificate.debtWeight,
      CappedClockParentRewardCertificate.toDeadlineWithdrawal,
      max_eq_left (certificate.weight_nonneg i)]
  simp_rw [hweight]
  exact quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt
    reward certificate evaluation evaluation_nonneg evaluation_antitone childProfile

end GameTheory
