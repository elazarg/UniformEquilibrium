import UniformEquilibrium.Quitting.Paths.FiniteWordSelectedOwnerRates
import UniformEquilibrium.Quitting.Paths.ExecutableRationalSelectedOwnerRates

/-! # Literal reciprocal debt rates of the actual renewed words

The exact and rational sequences are the existing source-preserving renewals.
The initial debt may be zero; no positive-debt or stopping-time oracle is input.
-/

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact-root renewal has the printed reciprocal rate at every phase,
including phase zero and a zero initial debt. -/
theorem quittingSelectedOwnerExactWordDebt_reciprocal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) :
    let initial := quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward 0
    let scale := (32 * M + 6 * initial) / 3
    quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward phase ≤
        scale * initial / (scale + phase * initial) := by
  dsimp only
  let debt := quittingSelectedOwnerExactWordDebt
    reward Eligible hWE preemption M hM hreward
  have hinitial := quittingSelectedOwnerExactWordDebt_nonneg
    reward Eligible hWE preemption M hM hreward 0
  have hscale : 0 < (32 * M + 6 * debt 0) / 3 := by
    change 0 ≤ debt 0 at hinitial
    positivity
  exact Math.sequence_le_reciprocal_of_fixed_quadratic_step debt hscale
    (quittingSelectedOwnerExactWordDebt_nonneg reward Eligible hWE preemption M hM hreward)
    (quittingSelectedOwnerExactWordDebt_antitone reward Eligible hWE preemption M hM hreward)
    (fun time hpositive => quittingSelectedOwnerExactWordDebt_fixedQuadraticStep
      reward Eligible hWE preemption M hM hreward time hpositive) phase

/-- The executable rational renewal satisfies the packet's exact C0 envelope,
not just an existential first-hit or phase-count bound. -/
theorem executableRationalSelectedOwnerDebt_reciprocal
    {players : ℕ} (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) :
    let initial := executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward 0
    let scale := (128 * M + 24 * initial) / 3
    executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward phase ≤
        scale * initial / (scale + phase * initial) := by
  dsimp only
  let debt := executableRationalSelectedOwnerDebt
    reward owners hWE hpreempted M hM hreward
  have hinitial := executableRationalSelectedOwnerDebt_nonneg
    reward owners hWE hpreempted M hM hreward 0
  have hscale : 0 < (128 * M + 24 * debt 0) / 3 := by
    change 0 ≤ debt 0 at hinitial
    positivity
  exact Math.sequence_le_reciprocal_of_fixed_quadratic_step debt hscale
    (executableRationalSelectedOwnerDebt_nonneg reward owners hWE hpreempted M hM hreward)
    (executableRationalSelectedOwnerDebt_antitone reward owners hWE hpreempted M hM hreward)
    (fun time hpositive => executableRationalSelectedOwnerDebt_fixedQuadraticStep
      reward owners hWE hpreempted M hM hreward time hpositive) phase

/-- The rational bound is literally the unrestricted complete-response debt
of the SAME chronological word followed by Never in the actual real game. -/
theorem executableRationalSelectedOwnerWord_actualDebt_reciprocal
    {players : ℕ} (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) :
    let initial := executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward 0
    let scale := (128 * M + 24 * initial) / 3
    let roots := executableRationalSelectedOwnerWords
      reward owners hWE hpreempted M hM hreward phase
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (roots.map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward)))) ≤
      ((scale * initial / (scale + phase * initial) : ℚ) : ℝ) := by
  dsimp only
  rw [quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast]
  exact_mod_cast executableRationalSelectedOwnerDebt_reciprocal
    reward owners hWE hpreempted M hM hreward phase

end GameTheory
