import UniformEquilibrium.Quitting.Paths.FiniteCalendarStrictDeficitSource
import UniformEquilibrium.Quitting.Paths.RationalFiniteCalendarWeakSubsetSource
import UniformEquilibrium.Quitting.Paths.ExecutableRationalStrictDeficitSource
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawWeakSubsetDecision
import UniformEquilibrium.Quitting.Paths.FiniteCalendarReciprocalSearch
import UniformEquilibrium.Quitting.Paths.GroupExclusionFiniteWordSource

/-! # Accepted raw tests as actual finite-selector sources

The existing Boolean checks and reciprocal searches supply exactly the erased
source hypotheses of the actual rational selectors. No favorable root, cap or
continuation profile is input or recovered by payoff compression.
-/

namespace GameTheory

variable {players : ℕ}

/-- A literal rational raw margin restricts to the exact rational payoff fold
of every actual rational finite word. The cast proof has one canonical owner. -/
theorem rationalQuittingFiniteWordStrictSingletonDeficit_of_finiteCalendarRaw
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hraw : HasQuittingFiniteCalendarRawStrictSingletonDeficit
      (rationalQuittingRewardToReal reward) (gap : ℝ)) :
    RationalQuittingFiniteWordStrictSingletonDeficit reward gap :=
  rationalQuittingFiniteWordStrictSingletonDeficit_of_real reward gap
    (hasQuittingFiniteWordStrictSingletonDeficit_of_finiteCalendarRaw
      (rationalQuittingRewardToReal reward) (gap : ℝ) hraw)

/-- A successful weak-subset Boolean check supplies both the actual rational
word source and its designated-owner signs; no preemption premise is needed. -/
theorem rationalFiniteWordOwnerExclusion_and_signs_of_rawWeakSubsetDecision
    [Nonempty (Fin players)]
    (reward : RationalQuittingReward players) (owners : Finset (Fin players))
    (haccepted : decideHasQuittingFiniteCalendarRawWeakSubsetExclusion
      reward owners = true) :
    RationalQuittingFiniteWordOwnerExclusionOn reward owners ∧
      ∀ who ∈ owners, 0 ≤ reward (quittingSingletonTerminal who) who :=
  rationalFiniteWordOwnerExclusion_and_signs_of_rawWeakSubsetExclusion reward owners
    ((decideHasQuittingFiniteCalendarRawWeakSubsetExclusion_eq_true_iff
      reward owners).mp haccepted)

/-- The actual strict reciprocal search output is a positive rational margin
for every rational source word, ready for the existing first-word selector. -/
theorem rationalFiniteWordStrictDeficit_of_returned_rawStrictReciprocal
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    {denominator : ℕ}
    (hresult : findQuittingFiniteCalendarRawStrictReciprocal? reward = some denominator) :
    0 < (denominator : ℚ)⁻¹ ∧
      RationalQuittingFiniteWordStrictSingletonDeficit reward (denominator : ℚ)⁻¹ := by
  obtain ⟨hpositive, hraw⟩ :=
    findQuittingFiniteCalendarRawStrictReciprocal?_eq_some_imp reward hresult
  refine ⟨inv_pos.mpr (Nat.cast_pos.mpr hpositive), ?_⟩
  exact rationalQuittingFiniteWordStrictSingletonDeficit_of_finiteCalendarRaw
    reward (denominator : ℚ)⁻¹ hraw

/-- A returned group denominator supplies the actual finite-word GE source
at the SAME rational complementary cap. The ordered pair may vary by word. -/
theorem finiteWordGroupExclusion_of_returned_rawGroupReciprocal
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    {denominator : ℕ}
    (hresult : findQuittingFiniteCalendarRawGroupReciprocal? reward = some denominator) :
    (1 - (denominator : ℚ)⁻¹ : ℚ) < 1 ∧
      HasQuittingFiniteWordNonconcentratedGroupExclusion
        (rationalQuittingRewardToReal reward) ((1 - (denominator : ℚ)⁻¹ : ℚ) : ℝ) := by
  obtain ⟨hdenominator, hraw⟩ :=
    findQuittingFiniteCalendarRawGroupReciprocal?_eq_some_imp reward hresult
  have hdenominatorPos : (0 : ℚ) < denominator := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hdenominator)
  have hdenominatorTwo : (2 : ℚ) ≤ denominator := by exact_mod_cast hdenominator
  have hpositive : (0 : ℚ) < (denominator : ℚ)⁻¹ := inv_pos.mpr hdenominatorPos
  have hhalf : (denominator : ℚ)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 2)
      hdenominatorTwo
  have hbeta : (1 - (denominator : ℚ)⁻¹ : ℚ) < 1 := by linarith
  refine ⟨hbeta, ?_⟩
  let rate : ℚ := (denominator : ℚ)⁻¹
  have hrawRate : HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
      (rationalQuittingRewardToReal reward) (rate : ℝ) := hraw
  have hpairs := (hasQuittingFiniteCalendarRawOrderedPairGroupExclusion_iff_actual
    (rationalQuittingRewardToReal reward) (rate : ℝ)).mp hrawRate
  have hrealHalf : (1 : ℝ) / 2 ≤ ((1 - (denominator : ℚ)⁻¹ : ℚ) : ℝ) := by
    have hcast : (((1 : ℚ) / 2 : ℚ) : ℝ) ≤
        ((1 - (denominator : ℚ)⁻¹ : ℚ) : ℝ) :=
      Rat.cast_le.mpr (show (1 : ℚ) / 2 ≤ 1 - (denominator : ℚ)⁻¹ by linarith)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hcast
  have hrealBeta : ((1 - (denominator : ℚ)⁻¹ : ℚ) : ℝ) < 1 := by exact_mod_cast hbeta
  apply hasQuittingFiniteWordNonconcentratedGroupExclusion_of_actual
  apply (hasQuittingActualNonconcentratedGroupExclusion_iff_orderedPair
    (rationalQuittingRewardToReal reward) _ hrealHalf hrealBeta).mpr
  change HasQuittingActualOrderedPairGroupExclusion
    (rationalQuittingRewardToReal reward) (1 - ((1 - rate : ℚ) : ℝ))
  simpa only [Rat.cast_sub, Rat.cast_one, sub_sub_cancel] using hpairs

end GameTheory
