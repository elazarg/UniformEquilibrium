import MathUE.ReciprocalDebtRecurrence
import UniformEquilibrium.Quitting.Paths.ExecutableRationalSelectedOwnerStep

/-! # Executable rational selected-owner renewal rates

The literal rational words are produced by repeated executable owner, blocker,
threshold, and grid scans.  The first target hit is itself a rational search.
The logarithm occurs only in the proved fixed-table row bound, never in the
computed word.
-/

namespace GameTheory

variable {players : ℕ}

/-- Literal rational words obtained by repeatedly prefixing one selected-owner
renewal block. -/
def executableRationalSelectedOwnerWords
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ℕ → List (RationalQuittingRoot players)
  | 0 => []
  | phase + 1 =>
      let old := executableRationalSelectedOwnerWords
        reward owners hWE hpreempted M hM hreward phase
      executableRationalSelectedOwnerDebtBlock
        reward owners hWE hpreempted old M hM hreward ++ old

@[simp] theorem executableRationalSelectedOwnerWords_zero
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    executableRationalSelectedOwnerWords
      reward owners hWE hpreempted M hM hreward 0 = [] := rfl

@[simp] theorem executableRationalSelectedOwnerWords_succ
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) :
    executableRationalSelectedOwnerWords
        reward owners hWE hpreempted M hM hreward (phase + 1) =
      executableRationalSelectedOwnerDebtBlock reward owners hWE hpreempted
          (executableRationalSelectedOwnerWords
            reward owners hWE hpreempted M hM hreward phase) M hM hreward ++
        executableRationalSelectedOwnerWords
          reward owners hWE hpreempted M hM hreward phase := rfl

/-- Rational total debt along the executable words. -/
def executableRationalSelectedOwnerDebt
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) : ℚ :=
  rationalFiniteSourceDebt reward
    (executableRationalSelectedOwnerWords
      reward owners hWE hpreempted M hM hreward phase)

theorem executableRationalSelectedOwnerDebt_nonneg
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) :
    0 ≤ executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward phase := by
  let roots := executableRationalSelectedOwnerWords
    reward owners hWE hpreempted M hM hreward phase
  let profile := quittingLiteralRootStackProfile
    (rationalQuittingRewardToReal reward)
    (roots.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
  have hnonnegative : 0 ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward) profile) := by
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalSemanticDebt_nonneg_of_attainable
        (rationalQuittingRewardToReal reward) ⟨profile, rfl⟩ who
  rw [quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast] at hnonnegative
  exact_mod_cast hnonnegative

theorem executableRationalSelectedOwnerDebt_step_of_pos
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ)
    (hpositive : 0 < executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward phase) :
    executableRationalSelectedOwnerDebt
        reward owners hWE hpreempted M hM hreward (phase + 1) ≤
      executableRationalSelectedOwnerDebt
          reward owners hWE hpreempted M hM hreward phase -
        3 * executableRationalSelectedOwnerDebt
            reward owners hWE hpreempted M hM hreward phase ^ 2 /
          (128 * M + 24 * executableRationalSelectedOwnerDebt
            reward owners hWE hpreempted M hM hreward phase) := by
  unfold executableRationalSelectedOwnerDebt
  rw [executableRationalSelectedOwnerWords_succ]
  exact executableRationalSelectedOwnerDebtBlock_debtSum_le
    reward owners hWE hpreempted _ M hM hreward hpositive

theorem executableRationalSelectedOwnerDebt_step_of_nonpos
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ)
    (hnonpos : ¬ 0 < executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward phase) :
    executableRationalSelectedOwnerDebt
        reward owners hWE hpreempted M hM hreward (phase + 1) =
      executableRationalSelectedOwnerDebt
        reward owners hWE hpreempted M hM hreward phase := by
  let old := executableRationalSelectedOwnerWords
    reward owners hWE hpreempted M hM hreward phase
  have hnonpos' : ¬ 0 < rationalFiniteSourceDebt reward old := by
    simpa only [old, executableRationalSelectedOwnerDebt] using hnonpos
  unfold executableRationalSelectedOwnerDebt
  rw [executableRationalSelectedOwnerWords_succ,
    executableRationalSelectedOwnerDebtBlock, dif_neg hnonpos']
  simp

theorem executableRationalSelectedOwnerDebt_antitone
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Antitone (executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward) := by
  apply antitone_nat_of_succ_le
  intro phase
  by_cases hpositive : 0 < executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward phase
  · have hstep := executableRationalSelectedOwnerDebt_step_of_pos
      reward owners hWE hpreempted M hM hreward phase hpositive
    have hdrop : 0 ≤ 3 * executableRationalSelectedOwnerDebt
        reward owners hWE hpreempted M hM hreward phase ^ 2 /
          (128 * M + 24 * executableRationalSelectedOwnerDebt
            reward owners hWE hpreempted M hM hreward phase) := by
      positivity
    linarith
  · rw [executableRationalSelectedOwnerDebt_step_of_nonpos
      reward owners hWE hpreempted M hM hreward phase hpositive]

theorem executableRationalSelectedOwnerDebt_fixedQuadraticStep
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ)
    (hpositive : 0 < executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward phase) :
    let initial := executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward 0
    let scale := (128 * M + 24 * initial) / 3
    executableRationalSelectedOwnerDebt
        reward owners hWE hpreempted M hM hreward (phase + 1) ≤
      executableRationalSelectedOwnerDebt
          reward owners hWE hpreempted M hM hreward phase -
        executableRationalSelectedOwnerDebt
            reward owners hWE hpreempted M hM hreward phase ^ 2 / scale := by
  dsimp only
  let debt := executableRationalSelectedOwnerDebt
    reward owners hWE hpreempted M hM hreward
  have hcurrentNonnegative := executableRationalSelectedOwnerDebt_nonneg
    reward owners hWE hpreempted M hM hreward phase
  have hinitialNonnegative := executableRationalSelectedOwnerDebt_nonneg
    reward owners hWE hpreempted M hM hreward 0
  have hcurrentLeInitial := executableRationalSelectedOwnerDebt_antitone
    reward owners hWE hpreempted M hM hreward (Nat.zero_le phase)
  have hcurrentDenom : 0 < 128 * M + 24 * debt phase := by positivity
  have hscale : 0 < (128 * M + 24 * debt 0) / 3 := by positivity
  have hdenomLe : 128 * M + 24 * debt phase ≤ 128 * M + 24 * debt 0 := by
    linarith
  have hquotient : debt phase ^ 2 / ((128 * M + 24 * debt 0) / 3) ≤
      3 * debt phase ^ 2 / (128 * M + 24 * debt phase) := by
    apply (div_le_div_iff₀ hscale hcurrentDenom).2
    nlinarith [sq_nonneg (debt phase)]
  have hraw := executableRationalSelectedOwnerDebt_step_of_pos
    reward owners hWE hpreempted M hM hreward phase hpositive
  dsimp only [debt] at hquotient hraw ⊢
  linarith

/-- The executable rational recurrence crosses every positive rational debt
threshold within its rational-ceiling phase bound. -/
theorem exists_executableRationalSelectedOwnerDebt_le_of_phaseBound
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℚ} (hε : 0 < ε) :
    let initial := executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward 0
    let scale := (128 * M + 24 * initial) / 3
    ∃ phase ≤ Nat.ceil (scale / ε),
      executableRationalSelectedOwnerDebt
        reward owners hWE hpreempted M hM hreward phase ≤ ε := by
  dsimp only
  let debt := executableRationalSelectedOwnerDebt
    reward owners hWE hpreempted M hM hreward
  let scale := (128 * M + 24 * debt 0) / 3
  have hinitialNonnegative := executableRationalSelectedOwnerDebt_nonneg
    reward owners hWE hpreempted M hM hreward 0
  have hscale : 0 < scale := by dsimp only [scale]; positivity
  have hstep : ∀ phase, 0 < debt phase →
      debt (phase + 1) ≤ debt phase - debt phase ^ 2 / scale := by
    intro phase hpositive
    simpa only [debt, scale] using
      executableRationalSelectedOwnerDebt_fixedQuadraticStep
        reward owners hWE hpreempted M hM hreward phase hpositive
  simpa only [debt, scale] using
    Math.exists_index_le_rationalCeil_of_quadratic_descent
      debt hscale hε hstep

/-- Erasing the quantitative phase field leaves termination of the executable
rational debt search. -/
theorem exists_executableRationalSelectedOwnerDebt_le
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℚ} (hε : 0 < ε) :
    ∃ phase, executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward phase ≤ ε := by
  obtain ⟨phase, -, hdebt⟩ :=
    exists_executableRationalSelectedOwnerDebt_le_of_phaseBound
      reward owners hWE hpreempted M hM hreward hε
  exact ⟨phase, hdebt⟩

/-- The first rational phase whose total debt is at most the target.  The
search predicate and every phase transition are executable over `ℚ`. -/
def executableRationalSelectedOwnerFirstPhase
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ε : ℚ) (hε : 0 < ε) : ℕ :=
  Nat.find (p := fun phase => executableRationalSelectedOwnerDebt
    reward owners hWE hpreempted M hM hreward phase ≤ ε)
      (exists_executableRationalSelectedOwnerDebt_le
        reward owners hWE hpreempted M hM hreward hε)

theorem executableRationalSelectedOwnerFirstPhase_spec
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ε : ℚ) (hε : 0 < ε) :
    executableRationalSelectedOwnerDebt reward owners hWE hpreempted M hM hreward
        (executableRationalSelectedOwnerFirstPhase
          reward owners hWE hpreempted M hM hreward ε hε) ≤ ε := by
  exact Nat.find_spec (p := fun phase => executableRationalSelectedOwnerDebt
    reward owners hWE hpreempted M hM hreward phase ≤ ε) _

theorem executableRationalSelectedOwnerFirstPhase_le
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ε : ℚ) (hε : 0 < ε) :
    let initial := executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward 0
    let scale := (128 * M + 24 * initial) / 3
    executableRationalSelectedOwnerFirstPhase
        reward owners hWE hpreempted M hM hreward ε hε ≤
      Nat.ceil (scale / ε) := by
  dsimp only
  let hbounded := exists_executableRationalSelectedOwnerDebt_le_of_phaseBound
    reward owners hWE hpreempted M hM hreward hε
  obtain ⟨witness, hwitnessLe, hwitnessDebt⟩ := hbounded
  exact (Nat.find_min'
    (exists_executableRationalSelectedOwnerDebt_le
      reward owners hWE hpreempted M hM hreward hε) hwitnessDebt).trans hwitnessLe

theorem executableRationalSelectedOwnerFirstPhase_before
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ε : ℚ) (hε : 0 < ε) {phase : ℕ}
    (hphase : phase < executableRationalSelectedOwnerFirstPhase
      reward owners hWE hpreempted M hM hreward ε hε) :
    ε < executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward phase := by
  exact lt_of_not_ge (Nat.find_min _ hphase)

/-- The fixed-table proof-only row bound for one phase above `ε`. -/
noncomputable def executableRationalSelectedOwnerUniformPhaseRowBound
    (M initial ε gap : ℝ) : ℕ :=
  1 + Nat.ceil
    (32 * (M + initial) / ε * Real.log (4 * M / gap))

theorem executableRationalSelectedOwnerDebtBlock_length_le_uniform
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℚ} (hε : 0 < ε) (phase : ℕ)
    (habove : ε < executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward phase) :
    let initial := executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward 0
    let old := executableRationalSelectedOwnerWords
      reward owners hWE hpreempted M hM hreward phase
    (executableRationalSelectedOwnerDebtBlock
        reward owners hWE hpreempted old M hM hreward).length ≤
      executableRationalSelectedOwnerUniformPhaseRowBound
        (M : ℝ) (initial : ℝ) (ε : ℝ)
          (rationalQuittingSelectedOwnerPreemptionFloor
            reward owners hWE hpreempted : ℝ) := by
  dsimp only
  let debt := executableRationalSelectedOwnerDebt
    reward owners hWE hpreempted M hM hreward
  let old := executableRationalSelectedOwnerWords
    reward owners hWE hpreempted M hM hreward phase
  let owner := rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE old
  let ell := rationalQuittingSelectedOwnerGap reward owners hWE hpreempted owner
  let gap := rationalQuittingSelectedOwnerPreemptionFloor
    reward owners hWE hpreempted
  have hD : 0 < debt phase := hε.trans habove
  have hlength := executableRationalSelectedOwnerDebtBlock_length_le
    reward owners hWE hpreempted old M hM hreward hD
  have hDleInitial : debt phase ≤ debt 0 :=
    executableRationalSelectedOwnerDebt_antitone
      reward owners hWE hpreempted M hM hreward (Nat.zero_le phase)
  have hownerMem := rationalQuittingFiniteWordExcludedOwnerOn_mem
    reward owners hWE old
  have hell : 0 < ell := rationalQuittingSelectedOwnerBlocker_spec
    reward owners hWE hpreempted owner hownerMem
  have hgapLeEll : gap ≤ ell :=
    rationalQuittingSelectedOwnerPreemptionFloor_le
      reward owners hWE hpreempted owner hownerMem
  have hgap : 0 < gap :=
    rationalQuittingSelectedOwnerPreemptionFloor_pos
      reward owners hWE hpreempted
  have hleftUpper :
      reward (quittingSingletonTerminal
          (rationalQuittingSelectedOwnerBlocker reward owners hWE hpreempted owner))
        (rationalQuittingSelectedOwnerBlocker reward owners hWE hpreempted owner) ≤ M :=
    (le_abs_self _).trans (hreward _ _)
  have hrightLower : -M ≤ reward (quittingSingletonTerminal owner)
      (rationalQuittingSelectedOwnerBlocker reward owners hWE hpreempted owner) :=
    neg_le_of_abs_le (hreward _ _)
  have hellUpper : ell ≤ 2 * M := by
    dsimp only [ell, rationalQuittingSelectedOwnerGap]
    linarith
  have hgapUpper : gap ≤ 2 * M := hgapLeEll.trans hellUpper
  have hratioGap : (1 : ℝ) < 4 * (M : ℝ) / (gap : ℝ) := by
    apply (lt_div_iff₀ (by exact_mod_cast hgap)).2
    have hgapFour : (gap : ℝ) < 4 * (M : ℝ) := by
      exact_mod_cast (by nlinarith : gap < 4 * M)
    simpa only [one_mul] using hgapFour
  have hratioEll : (0 : ℝ) < 4 * (M : ℝ) / (ell : ℝ) := by
    positivity
  have hratioLe : 4 * (M : ℝ) / (ell : ℝ) ≤
      4 * (M : ℝ) / (gap : ℝ) := by
    apply (div_le_div_iff₀ (by exact_mod_cast hell) (by exact_mod_cast hgap)).2
    exact_mod_cast (by nlinarith : 4 * M * gap ≤ 4 * M * ell)
  have hlogNonnegative : 0 ≤ Real.log (4 * (M : ℝ) / (gap : ℝ)) :=
    (Real.log_pos hratioGap).le
  have hlogLe : Real.log (4 * (M : ℝ) / (ell : ℝ)) ≤
      Real.log (4 * (M : ℝ) / (gap : ℝ)) :=
    Real.log_le_log hratioEll hratioLe
  have hcoefficient : 0 ≤
      32 * ((M : ℝ) + (debt phase : ℝ)) / (debt phase : ℝ) := by positivity
  have hcoefficientLe :
      32 * ((M : ℝ) + (debt phase : ℝ)) / (debt phase : ℝ) ≤
        32 * ((M : ℝ) + (debt 0 : ℝ)) / (ε : ℝ) := by
    apply (div_le_div_iff₀ (by exact_mod_cast hD) (by exact_mod_cast hε)).2
    exact_mod_cast (by
      nlinarith [mul_nonneg hM.le (sub_nonneg.mpr habove.le),
        mul_nonneg hD.le (sub_nonneg.mpr hDleInitial)])
  have hproduct :
      (((debt phase / (32 * (M + debt phase)) : ℚ) : ℝ)⁻¹) *
          Real.log (4 * (M : ℝ) / (ell : ℝ)) ≤
        32 * ((M : ℝ) + (debt 0 : ℝ)) / (ε : ℝ) *
          Real.log (4 * (M : ℝ) / (gap : ℝ)) := by
    have hidentity : (((debt phase / (32 * (M + debt phase)) : ℚ) : ℝ)⁻¹) =
        32 * ((M : ℝ) + (debt phase : ℝ)) / (debt phase : ℝ) := by
      push_cast
      field_simp
    rw [hidentity]
    exact (mul_le_mul_of_nonneg_left hlogLe hcoefficient).trans
      (mul_le_mul_of_nonneg_right hcoefficientLe hlogNonnegative)
  change _ ≤ executableRationalSelectedOwnerUniformPhaseRowBound
    (M : ℝ) (debt 0 : ℝ) (ε : ℝ) (gap : ℝ)
  exact hlength.trans (Nat.add_le_add_left (Nat.ceil_mono hproduct) 1)

/-- The executable first-hit word has the rational phase bound and the
fixed-table logarithmic date bound. -/
theorem executableRationalSelectedOwnerFirstWord_debt_and_length_le
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ε : ℚ) (hε : 0 < ε) :
    let initial := executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward 0
    let scale := (128 * M + 24 * initial) / 3
    let phase := executableRationalSelectedOwnerFirstPhase
      reward owners hWE hpreempted M hM hreward ε hε
    let roots := executableRationalSelectedOwnerWords
      reward owners hWE hpreempted M hM hreward phase
    rationalFiniteSourceDebt reward roots ≤ ε ∧
      phase ≤ Nat.ceil (scale / ε) ∧
      roots.length ≤ phase * executableRationalSelectedOwnerUniformPhaseRowBound
        (M : ℝ) (initial : ℝ) (ε : ℝ)
          (rationalQuittingSelectedOwnerPreemptionFloor
            reward owners hWE hpreempted : ℝ) := by
  dsimp only
  let debt := executableRationalSelectedOwnerDebt
    reward owners hWE hpreempted M hM hreward
  let words := executableRationalSelectedOwnerWords
    reward owners hWE hpreempted M hM hreward
  let phase := executableRationalSelectedOwnerFirstPhase
    reward owners hWE hpreempted M hM hreward ε hε
  let rowBound := executableRationalSelectedOwnerUniformPhaseRowBound
    (M : ℝ) (debt 0 : ℝ) (ε : ℝ)
      (rationalQuittingSelectedOwnerPreemptionFloor reward owners hWE hpreempted : ℝ)
  have hhit := executableRationalSelectedOwnerFirstPhase_spec
    reward owners hWE hpreempted M hM hreward ε hε
  have hphaseLe := executableRationalSelectedOwnerFirstPhase_le
    reward owners hWE hpreempted M hM hreward ε hε
  have hlength : ∀ time, time ≤ phase → (words time).length ≤ time * rowBound := by
    intro time htime
    induction time with
    | zero => simp only [words, executableRationalSelectedOwnerWords_zero,
        List.length_nil, zero_mul, le_refl]
    | succ time ih =>
        have htimeLt : time < phase := by omega
        have holdAbove : ε < debt time :=
          executableRationalSelectedOwnerFirstPhase_before
            reward owners hWE hpreempted M hM hreward ε hε htimeLt
        have hblock := executableRationalSelectedOwnerDebtBlock_length_le_uniform
          reward owners hWE hpreempted M hM hreward hε time holdAbove
        have holdLength := ih (by omega)
        simp only [words, executableRationalSelectedOwnerWords_succ, List.length_append]
        change _ + (words time).length ≤ (time + 1) * rowBound
        change _ ≤ rowBound at hblock
        calc
          _ ≤ rowBound + time * rowBound := Nat.add_le_add hblock holdLength
          _ = (time + 1) * rowBound := by rw [Nat.succ_mul, Nat.add_comm]
  exact ⟨hhit, hphaseLe, hlength phase le_rfl⟩

end GameTheory
