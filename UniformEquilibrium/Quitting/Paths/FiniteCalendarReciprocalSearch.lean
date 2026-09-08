import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawGroupDecision
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawStrictDecision
import UniformEquilibrium.Quitting.Paths.FiniteCalendarReciprocalParameterDecision
import UniformEquilibrium.Quitting.Paths.FiniteCalendarReciprocalParameterRecovery

/-! # Terminating reciprocal searches after exact raw recognition -/

namespace GameTheory

variable {players : Nat}

/-- Test one positive reciprocal denominator for a strict-deficit certificate. -/
def testQuittingFiniteCalendarRawStrictReciprocal
    (reward : RationalQuittingReward players) (denominator : Nat) : Bool :=
  decide (0 < denominator) &&
    decideHasQuittingFiniteCalendarRawStrictSingletonDeficit reward
      (denominator : ℚ)⁻¹

/-- The strict reciprocal test has its literal denominator and deficit semantics. -/
theorem testQuittingFiniteCalendarRawStrictReciprocal_eq_true_iff
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    (denominator : Nat) :
    testQuittingFiniteCalendarRawStrictReciprocal reward denominator = true ↔
      0 < denominator ∧
        HasQuittingFiniteCalendarRawStrictSingletonDeficit
          (rationalQuittingRewardToReal reward) (((denominator : ℚ)⁻¹ : ℚ) : ℝ) := by
  rw [testQuittingFiniteCalendarRawStrictReciprocal, Bool.and_eq_true,
    decide_eq_true_eq,
    decideHasQuittingFiniteCalendarRawStrictSingletonDeficit_eq_true_iff]

private theorem exists_strictReciprocalTest_eq_true
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    (haccepted : decideHasQuittingFiniteCalendarRawStrictExclusion reward = true) :
    ∃ denominator,
      testQuittingFiniteCalendarRawStrictReciprocal reward denominator = true := by
  have hstrict :=
    (decideHasQuittingFiniteCalendarRawStrictExclusion_eq_true_iff reward).mp haccepted
  obtain ⟨denominator, hpositive, _, hdeficit⟩ :=
    exists_nat_reciprocal_finiteCalendarRawStrictSingletonDeficit
      (rationalQuittingRewardToReal reward) hstrict
  exact ⟨denominator,
    (testQuittingFiniteCalendarRawStrictReciprocal_eq_true_iff
      reward denominator).mpr ⟨hpositive, hdeficit⟩⟩

/-- If strict exclusion is recognized, return the first positive denominator
whose reciprocal passes the exact strict-deficit test; otherwise return none. -/
def findQuittingFiniteCalendarRawStrictReciprocal?
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) : Option Nat :=
  if haccepted :
      decideHasQuittingFiniteCalendarRawStrictExclusion reward = true then
    some (Nat.find (exists_strictReciprocalTest_eq_true reward haccepted))
  else none

/-- A returned strict denominator is positive and its reciprocal supplies the
actual raw strict deficit. -/
theorem findQuittingFiniteCalendarRawStrictReciprocal?_eq_some_imp
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    {denominator : Nat}
    (hresult : findQuittingFiniteCalendarRawStrictReciprocal? reward =
      some denominator) :
    0 < denominator ∧
      HasQuittingFiniteCalendarRawStrictSingletonDeficit
        (rationalQuittingRewardToReal reward) (((denominator : ℚ)⁻¹ : ℚ) : ℝ) := by
  rw [findQuittingFiniteCalendarRawStrictReciprocal?] at hresult
  split at hresult
  next haccepted =>
    have hequal :
        Nat.find (exists_strictReciprocalTest_eq_true reward haccepted) =
          denominator := Option.some.inj hresult
    have htest := Nat.find_spec
      (exists_strictReciprocalTest_eq_true reward haccepted)
    rw [hequal] at htest
    exact (testQuittingFiniteCalendarRawStrictReciprocal_eq_true_iff
      reward denominator).mp htest
  next => simp at hresult

/-- No smaller denominator passes the strict reciprocal test. -/
theorem findQuittingFiniteCalendarRawStrictReciprocal?_minimal
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    {denominator : Nat}
    (hresult : findQuittingFiniteCalendarRawStrictReciprocal? reward =
      some denominator) :
    ∀ earlier < denominator,
      testQuittingFiniteCalendarRawStrictReciprocal reward earlier = false := by
  rw [findQuittingFiniteCalendarRawStrictReciprocal?] at hresult
  split at hresult
  next haccepted =>
    have hequal :
        Nat.find (exists_strictReciprocalTest_eq_true reward haccepted) =
          denominator := Option.some.inj hresult
    intro earlier hearlier
    apply Bool.eq_false_of_not_eq_true
    apply Nat.find_min (exists_strictReciprocalTest_eq_true reward haccepted)
    rwa [hequal]
  next => simp at hresult

/-- Strict reciprocal search fails exactly when actual strict exclusion fails. -/
theorem findQuittingFiniteCalendarRawStrictReciprocal?_eq_none_iff
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) :
    findQuittingFiniteCalendarRawStrictReciprocal? reward = none ↔
      ¬HasQuittingFiniteCalendarRawStrictExclusion
        (rationalQuittingRewardToReal reward) := by
  rw [← decideHasQuittingFiniteCalendarRawStrictExclusion_eq_true_iff reward]
  unfold findQuittingFiniteCalendarRawStrictReciprocal?
  split <;> simp_all

/-- Test one reciprocal denominator at least two for ordered-pair group exclusion. -/
def testQuittingFiniteCalendarRawGroupReciprocal
    (reward : RationalQuittingReward players) (denominator : Nat) : Bool :=
  decide (2 ≤ denominator) &&
    decideHasQuittingFiniteCalendarRawOrderedPairGroupExclusion reward
      (denominator : ℚ)⁻¹

/-- The group reciprocal test has its literal denominator and ordered-pair semantics. -/
theorem testQuittingFiniteCalendarRawGroupReciprocal_eq_true_iff
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    (denominator : Nat) :
    testQuittingFiniteCalendarRawGroupReciprocal reward denominator = true ↔
      2 ≤ denominator ∧
        HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
          (rationalQuittingRewardToReal reward) (((denominator : ℚ)⁻¹ : ℚ) : ℝ) := by
  rw [testQuittingFiniteCalendarRawGroupReciprocal, Bool.and_eq_true,
    decide_eq_true_eq,
    decideHasQuittingFiniteCalendarRawOrderedPairGroupExclusion_eq_true_iff]

private theorem exists_groupReciprocalTest_eq_true
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    (haccepted : decideExistsQuittingFiniteCalendarRawGroupExclusion reward = true) :
    ∃ denominator,
      testQuittingFiniteCalendarRawGroupReciprocal reward denominator = true := by
  have hgroup :=
    (decideExistsQuittingFiniteCalendarRawGroupExclusion_eq_true_iff reward).mp
      haccepted
  obtain ⟨denominator, htwo, _, _, hpairs⟩ :=
    exists_nat_reciprocal_orderedPairGroupExclusion_of_finiteCalendarRaw
      (rationalQuittingRewardToReal reward) hgroup
  exact ⟨denominator,
    (testQuittingFiniteCalendarRawGroupReciprocal_eq_true_iff
      reward denominator).mpr ⟨htwo, hpairs⟩⟩

/-- If group exclusion is recognized, return the first denominator at least two
whose reciprocal passes the exact ordered-pair test; otherwise return none. -/
def findQuittingFiniteCalendarRawGroupReciprocal?
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) : Option Nat :=
  if haccepted :
      decideExistsQuittingFiniteCalendarRawGroupExclusion reward = true then
    some (Nat.find (exists_groupReciprocalTest_eq_true reward haccepted))
  else none

/-- A returned group denominator is at least two and its reciprocal supplies
the actual raw ordered-pair group parameter. -/
theorem findQuittingFiniteCalendarRawGroupReciprocal?_eq_some_imp
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    {denominator : Nat}
    (hresult : findQuittingFiniteCalendarRawGroupReciprocal? reward =
      some denominator) :
    2 ≤ denominator ∧
      HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
        (rationalQuittingRewardToReal reward) (((denominator : ℚ)⁻¹ : ℚ) : ℝ) := by
  rw [findQuittingFiniteCalendarRawGroupReciprocal?] at hresult
  split at hresult
  next haccepted =>
    have hequal :
        Nat.find (exists_groupReciprocalTest_eq_true reward haccepted) =
          denominator := Option.some.inj hresult
    have htest := Nat.find_spec
      (exists_groupReciprocalTest_eq_true reward haccepted)
    rw [hequal] at htest
    exact (testQuittingFiniteCalendarRawGroupReciprocal_eq_true_iff
      reward denominator).mp htest
  next => simp at hresult

/-- No smaller denominator passes the group reciprocal test. -/
theorem findQuittingFiniteCalendarRawGroupReciprocal?_minimal
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    {denominator : Nat}
    (hresult : findQuittingFiniteCalendarRawGroupReciprocal? reward =
      some denominator) :
    ∀ earlier < denominator,
      testQuittingFiniteCalendarRawGroupReciprocal reward earlier = false := by
  rw [findQuittingFiniteCalendarRawGroupReciprocal?] at hresult
  split at hresult
  next haccepted =>
    have hequal :
        Nat.find (exists_groupReciprocalTest_eq_true reward haccepted) =
          denominator := Option.some.inj hresult
    intro earlier hearlier
    apply Bool.eq_false_of_not_eq_true
    apply Nat.find_min (exists_groupReciprocalTest_eq_true reward haccepted)
    rwa [hequal]
  next => simp at hresult

/-- Group reciprocal search fails exactly when actual group exclusion fails. -/
theorem findQuittingFiniteCalendarRawGroupReciprocal?_eq_none_iff
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) :
    findQuittingFiniteCalendarRawGroupReciprocal? reward = none ↔
      ¬∃ beta < 1,
        HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion
          (rationalQuittingRewardToReal reward) beta := by
  rw [← decideExistsQuittingFiniteCalendarRawGroupExclusion_eq_true_iff reward]
  unfold findQuittingFiniteCalendarRawGroupReciprocal?
  split <;> simp_all

end GameTheory
