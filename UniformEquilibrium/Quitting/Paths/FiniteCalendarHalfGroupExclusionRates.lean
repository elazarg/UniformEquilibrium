import UniformEquilibrium.Quitting.Paths.GroupExclusionFiniteWordRates
import UniformEquilibrium.Quitting.Paths.GroupExclusionFiniteWordSource
import UniformEquilibrium.Quitting.Paths.ExecutableRationalGroupExclusionRates

/-! # Literal half-cap reciprocal rates on the actual selected words

The raw calendar source supplies exclusion; no selected word or cap certificate
is an input. In particular the two-pair reward-table producer supplies this
source. The zero-initial-debt case is included, with no division-positivity input.
-/

namespace GameTheory

/-- The literal exact-word constant at cap one half is (32M+3D₀). -/
theorem quittingGroupExclusionExactWordDebt_half_raw_reciprocal
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {M : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hraw : HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion reward (1 / 2))
    (time : ℕ) :
    let initial := quittingGroupExclusionExactWordDebt reward (1 / 2) 0
    quittingGroupExclusionExactWordDebt reward (1 / 2) time ≤
      (32 * M + 3 * initial) * initial /
        (32 * M + 3 * initial + time * initial) := by
  dsimp only
  have hexclusion := hasQuittingFiniteWordNonconcentratedGroupExclusion_of_raw
    reward (1 / 2) hraw
  have hbeta : (1 / 2 : ℝ) < 1 := by norm_num
  by_cases hpositive : 0 < quittingGroupExclusionExactWordDebt reward (1 / 2) 0
  · have hconstant : ∀ initial : ℝ,
        quittingGroupExclusionReciprocalConstant M (1 / 2) initial =
          32 * M + 3 * initial := by
      intro initial
      unfold quittingGroupExclusionReciprocalConstant
      ring
    simpa only [hconstant] using quittingGroupExclusionExactWordDebt_reciprocal
      reward hbeta hreward hexclusion hpositive time
  · have hzero : quittingGroupExclusionExactWordDebt reward (1 / 2) 0 = 0 :=
      le_antisymm (le_of_not_gt hpositive)
        (quittingGroupExclusionExactWordDebt_nonneg reward (1 / 2) 0)
    have hle := quittingGroupExclusionExactWordDebt_antitone
      reward hbeta hreward hexclusion (Nat.zero_le time)
    simpa only [hzero, mul_zero, add_zero, zero_div] using hle

/-- The literal executable-word constant at cap one half is (128M+15D₀).
This is rational full debt of the canonical executable source word, not a
separate payoff-equivalent replacement. -/
theorem executableRationalGroupExclusionDebt_half_raw_reciprocal
    (reward : RationalQuittingReward 4) (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hraw : HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion
      (rationalQuittingRewardToReal reward) (1 / 2))
    (time : ℕ) :
    let debt := executableRationalGroupExclusionDebt reward (1 / 2) M hM (by norm_num)
    debt time ≤ (128 * M + 15 * debt 0) * debt 0 /
      (128 * M + 15 * debt 0 + time * debt 0) := by
  dsimp only
  have hbeta : (1 / 2 : ℚ) < 1 := by norm_num
  have hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion
      (rationalQuittingRewardToReal reward) ((1 / 2 : ℚ) : ℝ) := by
    simpa using hasQuittingFiniteWordNonconcentratedGroupExclusion_of_raw
      (rationalQuittingRewardToReal reward) (1 / 2) hraw
  by_cases hpositive :
      0 < executableRationalGroupExclusionDebt reward (1 / 2) M hM hbeta 0
  · have hconstant : ∀ initial : ℚ,
        executableRationalGroupExclusionReciprocalConstant M (1 / 2) initial =
          128 * M + 15 * initial := by
      intro initial
      unfold executableRationalGroupExclusionReciprocalConstant
      ring
    simpa only [hconstant] using executableRationalGroupExclusionDebt_reciprocal
      reward (1 / 2) M hM hbeta hreward hexclusion hpositive time
  · have hzero :
        executableRationalGroupExclusionDebt reward (1 / 2) M hM hbeta 0 = 0 :=
      le_antisymm (le_of_not_gt hpositive)
        (executableRationalGroupExclusionDebt_nonneg reward (1 / 2) M hM hbeta 0)
    have hle := executableRationalGroupExclusionDebt_antitone
      reward (1 / 2) M hM hbeta hreward hexclusion (Nat.zero_le time)
    simpa only [hzero, mul_zero, add_zero, zero_div] using hle

end GameTheory
