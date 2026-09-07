import MathUE.ReciprocalDebtRecurrence
import UniformEquilibrium.Quitting.Paths.FiniteWordWeakExclusionStep

/-! # Quantitative rates for weak-exclusion literal finite words -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Total complete-deviation debt of a literal finite word followed by Never. -/
def quittingWeakExclusionFiniteWordDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) : ℝ :=
  quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward
      (quittingLiteralRootStackProfile reward roots
        (quittingAlwaysContinueProfile reward)))

/-- One selected renewal of a literal word. At positive debt it carries the
owner, row bound, and quadratic drop delivered by cap-threshold descent; at
zero debt it is literally empty. -/
structure QuittingWeakExclusionRenewal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (roots : List (ι → PMF Bool)) where
  owner : ι
  block : List (ι → PMF Bool)
  block_eq_nil_of_nonpos : ¬ 0 < quittingWeakExclusionFiniteWordDebt reward roots →
    block = []
  length_le_of_pos : 0 < quittingWeakExclusionFiniteWordDebt reward roots →
    block.length ≤ 1 + quittingSoloCapThresholdHorizon M
      (quittingWeakExclusionFiniteWordDebt reward roots /
        (32 * (M + quittingWeakExclusionFiniteWordDebt reward roots)))
      (reward (quittingSingletonTerminal (preemption.blocker owner))
          (preemption.blocker owner) -
        reward (quittingSingletonTerminal owner) (preemption.blocker owner))
  debt_le_of_pos : 0 < quittingWeakExclusionFiniteWordDebt reward roots →
    quittingWeakExclusionFiniteWordDebt reward (block ++ roots) ≤
      quittingWeakExclusionFiniteWordDebt reward roots -
        3 * quittingWeakExclusionFiniteWordDebt reward roots ^ 2 /
          (32 * M + 6 * quittingWeakExclusionFiniteWordDebt reward roots)

theorem exists_quittingWeakExclusionRenewal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (roots : List (ι → PMF Bool)) :
    Nonempty (QuittingWeakExclusionRenewal reward preemption M roots) := by
  by_cases hpositive : 0 < quittingWeakExclusionFiniteWordDebt reward roots
  · obtain ⟨owner, block, hlength, hdebt⟩ :=
      exists_finiteWord_weakExclusion_quadraticDebtStep
        reward hWE preemption roots hM hreward hpositive
    exact ⟨{
      owner := owner
      block := block
      block_eq_nil_of_nonpos := fun hnonpos => (hnonpos hpositive).elim
      length_le_of_pos := fun _ => hlength
      debt_le_of_pos := fun _ => hdebt }⟩
  · obtain ⟨owner, _⟩ := hWE roots
    exact ⟨{
      owner := owner
      block := []
      block_eq_nil_of_nonpos := fun _ => rfl
      length_le_of_pos := fun hpos => (hpositive hpos).elim
      debt_le_of_pos := fun hpos => (hpositive hpos).elim }⟩

/-- The canonical selected renewal at a literal weak-exclusion word. -/
def quittingWeakExclusionSelectedRenewal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (roots : List (ι → PMF Bool)) :
    QuittingWeakExclusionRenewal reward preemption M roots :=
  Classical.choice
    (exists_quittingWeakExclusionRenewal reward hWE preemption M hM hreward roots)

/-- Literal finite words obtained by repeatedly prefixing the selected
cap-threshold renewal. -/
def quittingWeakExclusionExactWords
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ℕ → List (ι → PMF Bool)
  | 0 => []
  | phase + 1 =>
      let old := quittingWeakExclusionExactWords
        reward hWE preemption M hM hreward phase
      (quittingWeakExclusionSelectedRenewal
        reward hWE preemption M hM hreward old).block ++ old

@[simp] theorem quittingWeakExclusionExactWords_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingWeakExclusionExactWords reward hWE preemption M hM hreward 0 = [] := rfl

@[simp] theorem quittingWeakExclusionExactWords_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) :
    quittingWeakExclusionExactWords reward hWE preemption M hM hreward (phase + 1) =
      (quittingWeakExclusionSelectedRenewal reward hWE preemption M hM hreward
        (quittingWeakExclusionExactWords reward hWE preemption M hM hreward phase)).block ++
      quittingWeakExclusionExactWords reward hWE preemption M hM hreward phase := rfl

/-- Total debt along the selected weak-exclusion words. -/
def quittingWeakExclusionExactWordDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) : ℝ :=
  quittingWeakExclusionFiniteWordDebt reward
    (quittingWeakExclusionExactWords reward hWE preemption M hM hreward phase)

theorem quittingWeakExclusionExactWordDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) :
    0 ≤ quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward phase := by
  unfold quittingWeakExclusionExactWordDebt quittingWeakExclusionFiniteWordDebt
  exact Finset.sum_nonneg fun player _ =>
    quittingTerminalSemanticDebt_nonneg_of_attainable reward
      ⟨quittingLiteralRootStackProfile reward
        (quittingWeakExclusionExactWords reward hWE preemption M hM hreward phase)
        (quittingAlwaysContinueProfile reward), rfl⟩ player

theorem quittingWeakExclusionExactWordDebt_step_of_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ)
    (hpositive : 0 < quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward phase) :
    quittingWeakExclusionExactWordDebt reward hWE preemption M hM hreward
        (phase + 1) ≤
      quittingWeakExclusionExactWordDebt reward hWE preemption M hM hreward phase -
        3 * quittingWeakExclusionExactWordDebt
            reward hWE preemption M hM hreward phase ^ 2 /
          (32 * M + 6 * quittingWeakExclusionExactWordDebt
            reward hWE preemption M hM hreward phase) := by
  unfold quittingWeakExclusionExactWordDebt
  rw [quittingWeakExclusionExactWords_succ]
  exact (quittingWeakExclusionSelectedRenewal
    reward hWE preemption M hM hreward _).debt_le_of_pos hpositive

theorem quittingWeakExclusionExactWordDebt_step_of_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ)
    (hnonpos : ¬ 0 < quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward phase) :
    quittingWeakExclusionExactWordDebt reward hWE preemption M hM hreward
        (phase + 1) =
      quittingWeakExclusionExactWordDebt reward hWE preemption M hM hreward phase := by
  unfold quittingWeakExclusionExactWordDebt
  rw [quittingWeakExclusionExactWords_succ,
    (quittingWeakExclusionSelectedRenewal
      reward hWE preemption M hM hreward _).block_eq_nil_of_nonpos hnonpos]
  simp

theorem quittingWeakExclusionExactWordDebt_antitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Antitone (quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward) := by
  apply antitone_nat_of_succ_le
  intro phase
  by_cases hpositive : 0 < quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward phase
  · have hstep := quittingWeakExclusionExactWordDebt_step_of_pos
      reward hWE preemption M hM hreward phase hpositive
    have hdrop : 0 ≤ 3 * quittingWeakExclusionExactWordDebt
        reward hWE preemption M hM hreward phase ^ 2 /
          (32 * M + 6 * quittingWeakExclusionExactWordDebt
            reward hWE preemption M hM hreward phase) := by
      positivity
    linarith
  · rw [quittingWeakExclusionExactWordDebt_step_of_nonpos
      reward hWE preemption M hM hreward phase hpositive]

/-- At every positive phase, the variable cap-threshold drop dominates a
quadratic drop with one constant fixed by the initial debt. -/
theorem quittingWeakExclusionExactWordDebt_fixedQuadraticStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ)
    (hpositive : 0 < quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward phase) :
    let initial := quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward 0
    let scale := (32 * M + 6 * initial) / 3
    quittingWeakExclusionExactWordDebt reward hWE preemption M hM hreward
        (phase + 1) ≤
      quittingWeakExclusionExactWordDebt reward hWE preemption M hM hreward phase -
        quittingWeakExclusionExactWordDebt
            reward hWE preemption M hM hreward phase ^ 2 / scale := by
  dsimp only
  let debt := quittingWeakExclusionExactWordDebt
    reward hWE preemption M hM hreward
  have hcurrentNonnegative := quittingWeakExclusionExactWordDebt_nonneg
    reward hWE preemption M hM hreward phase
  have hinitialNonnegative := quittingWeakExclusionExactWordDebt_nonneg
    reward hWE preemption M hM hreward 0
  have hcurrentLeInitial := quittingWeakExclusionExactWordDebt_antitone
    reward hWE preemption M hM hreward (Nat.zero_le phase)
  have hcurrentDenom : 0 < 32 * M + 6 * debt phase := by positivity
  have hscale : 0 < (32 * M + 6 * debt 0) / 3 := by positivity
  have hdenomLe : 32 * M + 6 * debt phase ≤ 32 * M + 6 * debt 0 := by
    linarith
  have hquotient : debt phase ^ 2 / ((32 * M + 6 * debt 0) / 3) ≤
      3 * debt phase ^ 2 / (32 * M + 6 * debt phase) := by
    apply (div_le_div_iff₀ hscale hcurrentDenom).2
    nlinarith [sq_nonneg (debt phase)]
  have hraw := quittingWeakExclusionExactWordDebt_step_of_pos
    reward hWE preemption M hM hreward phase hpositive
  dsimp only [debt] at hquotient hraw ⊢
  linarith

/-- The selected literal word crosses a positive total-debt threshold within
the explicit reciprocal number of renewal phases. -/
theorem exists_quittingWeakExclusionExactWordDebt_le_of_phase_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    let initial := quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward 0
    let scale := (32 * M + 6 * initial) / 3
    ∃ phase ≤ Nat.ceil (scale / ε),
      quittingWeakExclusionExactWordDebt
        reward hWE preemption M hM hreward phase ≤ ε := by
  dsimp only
  let debt := quittingWeakExclusionExactWordDebt
    reward hWE preemption M hM hreward
  let scale := (32 * M + 6 * debt 0) / 3
  have hinitialNonnegative := quittingWeakExclusionExactWordDebt_nonneg
    reward hWE preemption M hM hreward 0
  have hscale : 0 < scale := by dsimp only [scale]; positivity
  have hstep : ∀ phase, 0 < debt phase →
      debt (phase + 1) ≤ debt phase - debt phase ^ 2 / scale := by
    intro phase hpositive
    simpa only [debt, scale] using
      quittingWeakExclusionExactWordDebt_fixedQuadraticStep
        reward hWE preemption M hM hreward phase hpositive
  simpa only [debt, scale] using
    Math.exists_index_le_ceil_of_quadratic_descent debt hscale hε hstep

/-- A uniform row bound for every renewal phase whose debt is still above
the target error. -/
def quittingWeakExclusionUniformPhaseRowBound
    (M initial ε gap : ℝ) : ℕ :=
  1 + Nat.ceil
    (32 * (M + initial) / ε * Real.log (4 * M / gap))

theorem quittingWeakExclusionSelectedRenewal_length_le_uniform
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℝ} (hε : 0 < ε) (phase : ℕ)
    (habove : ε < quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward phase) :
    let initial := quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward 0
    let old := quittingWeakExclusionExactWords
      reward hWE preemption M hM hreward phase
    (quittingWeakExclusionSelectedRenewal
        reward hWE preemption M hM hreward old).block.length ≤
      quittingWeakExclusionUniformPhaseRowBound
        M initial ε preemption.gap := by
  dsimp only
  let debt := quittingWeakExclusionExactWordDebt
    reward hWE preemption M hM hreward
  let old := quittingWeakExclusionExactWords
    reward hWE preemption M hM hreward phase
  let renewal := quittingWeakExclusionSelectedRenewal
    reward hWE preemption M hM hreward old
  let D := debt phase
  let initial := debt 0
  let ell := reward (quittingSingletonTerminal (preemption.blocker renewal.owner))
      (preemption.blocker renewal.owner) -
    reward (quittingSingletonTerminal renewal.owner) (preemption.blocker renewal.owner)
  have hD : 0 < D := hε.trans habove
  have hlength := renewal.length_le_of_pos hD
  have hDleInitial : D ≤ initial :=
    quittingWeakExclusionExactWordDebt_antitone
      reward hWE preemption M hM hreward (Nat.zero_le phase)
  have hell : 0 < ell := by
    exact preemption.gap_pos.trans_le (preemption.gap_le renewal.owner)
  have hgapLeEll : preemption.gap ≤ ell := preemption.gap_le renewal.owner
  have hleftUpper :
      reward (quittingSingletonTerminal (preemption.blocker renewal.owner))
          (preemption.blocker renewal.owner) ≤ M :=
    (le_abs_self _).trans
      (hreward (quittingSingletonTerminal (preemption.blocker renewal.owner))
        (preemption.blocker renewal.owner))
  have hrightLower : -M ≤
      reward (quittingSingletonTerminal renewal.owner)
        (preemption.blocker renewal.owner) :=
    neg_le_of_abs_le (hreward (quittingSingletonTerminal renewal.owner)
      (preemption.blocker renewal.owner))
  have hellUpper : ell ≤ 2 * M := by
    dsimp only [ell]
    linarith
  have hgapUpper : preemption.gap ≤ 2 * M := hgapLeEll.trans hellUpper
  have hgap : 0 < preemption.gap := preemption.gap_pos
  have hratioGap : 1 < 4 * M / preemption.gap := by
    apply (lt_div_iff₀ hgap).2
    nlinarith
  have hratioEll : 0 < 4 * M / ell := div_pos (by positivity) hell
  have hratioLe : 4 * M / ell ≤ 4 * M / preemption.gap := by
    apply (div_le_div_iff₀ hell hgap).2
    nlinarith
  have hlogNonnegative : 0 ≤ Real.log (4 * M / preemption.gap) :=
    (Real.log_pos hratioGap).le
  have hlogLe : Real.log (4 * M / ell) ≤
      Real.log (4 * M / preemption.gap) :=
    Real.log_le_log hratioEll hratioLe
  have hcoefficient : 0 ≤ 32 * (M + D) / D := by positivity
  have hcoefficientLe : 32 * (M + D) / D ≤
      32 * (M + initial) / ε := by
    apply (div_le_div_iff₀ hD hε).2
    nlinarith [mul_nonneg hM.le (sub_nonneg.mpr habove.le),
      mul_nonneg hD.le (sub_nonneg.mpr hDleInitial)]
  have hproduct : (D / (32 * (M + D)))⁻¹ * Real.log (4 * M / ell) ≤
      32 * (M + initial) / ε * Real.log (4 * M / preemption.gap) := by
    have hidentity : (D / (32 * (M + D)))⁻¹ = 32 * (M + D) / D := by
      field_simp
    rw [hidentity]
    exact (mul_le_mul_of_nonneg_left hlogLe hcoefficient).trans
      (mul_le_mul_of_nonneg_right hcoefficientLe hlogNonnegative)
  change renewal.block.length ≤
    quittingWeakExclusionUniformPhaseRowBound M initial ε preemption.gap
  exact hlength.trans (Nat.add_le_add_left
    (Nat.ceil_mono hproduct) 1)

/-- The first selected phase reaching the target debt has no more than the
reciprocal phase count and every preceding phase is strictly above target. -/
theorem exists_quittingWeakExclusionExactWordDebt_first_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    let initial := quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward 0
    let scale := (32 * M + 6 * initial) / 3
    ∃ phase ≤ Nat.ceil (scale / ε),
      quittingWeakExclusionExactWordDebt
          reward hWE preemption M hM hreward phase ≤ ε ∧
        ∀ earlier < phase, ε < quittingWeakExclusionExactWordDebt
          reward hWE preemption M hM hreward earlier := by
  dsimp only
  obtain ⟨witness, hwitnessLe, hwitness⟩ :=
    exists_quittingWeakExclusionExactWordDebt_le_of_phase_bound
      reward hWE preemption M hM hreward hε
  let debt := quittingWeakExclusionExactWordDebt
    reward hWE preemption M hM hreward
  have hexists : ∃ phase, debt phase ≤ ε := ⟨witness, hwitness⟩
  let phase := Nat.find hexists
  have hhit : debt phase ≤ ε := Nat.find_spec hexists
  have hphaseLe : phase ≤ witness := Nat.find_min' hexists hwitness
  refine ⟨phase, hphaseLe.trans hwitnessLe, hhit, ?_⟩
  intro earlier hearlier
  exact lt_of_not_ge (Nat.find_min hexists hearlier)

/-- At its first target crossing, the selected literal word has the phase
count times the uniform per-phase row bound. -/
theorem exists_quittingWeakExclusionExactWord_debt_and_length_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    let initial := quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward 0
    let scale := (32 * M + 6 * initial) / 3
    ∃ phase ≤ Nat.ceil (scale / ε),
      quittingWeakExclusionExactWordDebt
          reward hWE preemption M hM hreward phase ≤ ε ∧
        (quittingWeakExclusionExactWords
          reward hWE preemption M hM hreward phase).length ≤
          phase * quittingWeakExclusionUniformPhaseRowBound
            M initial ε preemption.gap := by
  dsimp only
  obtain ⟨phase, hphaseLe, hhit, hbefore⟩ :=
    exists_quittingWeakExclusionExactWordDebt_first_le
      reward hWE preemption M hM hreward hε
  let words := quittingWeakExclusionExactWords
    reward hWE preemption M hM hreward
  let debt := quittingWeakExclusionExactWordDebt
    reward hWE preemption M hM hreward
  let initial := debt 0
  let rowBound := quittingWeakExclusionUniformPhaseRowBound
    M initial ε preemption.gap
  have hlength : ∀ time, time ≤ phase →
      (words time).length ≤ time * rowBound := by
    intro time htime
    induction time with
    | zero => simp only [words, quittingWeakExclusionExactWords_zero,
        List.length_nil, zero_mul, le_refl]
    | succ time ih =>
        have htimeLt : time < phase := by omega
        have holdAbove : ε < debt time := hbefore time htimeLt
        have hblock := quittingWeakExclusionSelectedRenewal_length_le_uniform
          reward hWE preemption M hM hreward hε time holdAbove
        have holdLength := ih (by omega)
        simp only [words, quittingWeakExclusionExactWords_succ, List.length_append]
        change _ + (words time).length ≤ (time + 1) * rowBound
        change _ ≤ rowBound at hblock
        calc
          _ ≤ rowBound + time * rowBound := Nat.add_le_add hblock holdLength
          _ = (time + 1) * rowBound := by rw [Nat.succ_mul, Nat.add_comm]
  refine ⟨phase, hphaseLe, hhit, ?_⟩
  exact hlength phase le_rfl

/-- A selected literal word reaches the target debt within the product of
the reciprocal phase bound and the uniform logarithmic row bound. -/
theorem exists_finiteWord_debtSum_and_length_le_of_weakExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    let initial := quittingWeakExclusionFiniteWordDebt reward []
    let scale := (32 * M + 6 * initial) / 3
    ∃ roots : List (ι → PMF Bool),
      quittingWeakExclusionFiniteWordDebt reward roots ≤ ε ∧
        roots.length ≤ Nat.ceil (scale / ε) *
          quittingWeakExclusionUniformPhaseRowBound
            M initial ε preemption.gap := by
  dsimp only
  obtain ⟨phase, hphaseLe, hdebt, hlength⟩ :=
    exists_quittingWeakExclusionExactWord_debt_and_length_le
      reward hWE preemption M hM hreward hε
  refine ⟨quittingWeakExclusionExactWords
    reward hWE preemption M hM hreward phase, hdebt, ?_⟩
  exact hlength.trans (Nat.mul_le_mul_right _ hphaseLe)

/-- With nonnegative singleton rewards, the all-Never initial debt is the
sum of the singleton coordinates. -/
theorem quittingWeakExclusionFiniteWordDebt_nil_eq_sum_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player) :
    quittingWeakExclusionFiniteWordDebt reward [] =
      ∑ player, reward (quittingSingletonTerminal player) player := by
  unfold quittingWeakExclusionFiniteWordDebt quittingTerminalSemanticDebtSum
  rw [quittingLiteralRootStackProfile_nil]
  apply Finset.sum_congr rfl
  intro player _
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change quittingContinuationBestResponseValue reward
      (quittingAlwaysContinueProfile reward) player -
        quittingTerminalPayoff reward
          (quittingAlwaysContinueProfile reward) player = _
  rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
    quittingTerminalPayoff_quittingAlwaysContinue]
  exact sub_zero _ |>.trans (max_eq_right (hsingleton player))

/-- Under nonnegative singleton rewards, the quantitative real-table bound
is expressed directly using the singleton sum `D₀`. -/
theorem exists_finiteWord_debtSum_and_length_le_of_weakExclusion_nonnegativeSingleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    {ε : ℝ} (hε : 0 < ε) :
    let D₀ := ∑ player, reward (quittingSingletonTerminal player) player
    let scale := (32 * M + 6 * D₀) / 3
    ∃ roots : List (ι → PMF Bool),
      quittingWeakExclusionFiniteWordDebt reward roots ≤ ε ∧
        roots.length ≤ Nat.ceil (scale / ε) *
          quittingWeakExclusionUniformPhaseRowBound
            M D₀ ε preemption.gap := by
  simpa only [quittingWeakExclusionFiniteWordDebt_nil_eq_sum_singleton
    reward hsingleton] using
      exists_finiteWord_debtSum_and_length_le_of_weakExclusion
        reward hWE preemption M hM hreward hε

end GameTheory
