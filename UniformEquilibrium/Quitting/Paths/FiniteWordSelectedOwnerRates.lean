import MathUE.ReciprocalDebtRecurrence
import UniformEquilibrium.Quitting.Paths.FiniteWordSelectedOwnerStep

/-! # Quantitative rates for selected-owner literal finite words

The logarithmic row bound is uniform across phases for one fixed reward table
and eligible-owner preemption floor.  It is not uniform across reward tables.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One selected eligible-owner renewal. -/
structure QuittingSelectedOwnerRenewal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (roots : List (ι → PMF Bool)) where
  owner : ι
  owner_eligible : Eligible owner
  owner_payoff_le_singleton :
    quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward roots
          (quittingAlwaysContinueProfile reward)) owner ≤
      reward (quittingSingletonTerminal owner) owner
  block : List (ι → PMF Bool)
  block_eq_nil_of_nonpos : ¬ 0 < quittingFiniteWordDebt reward roots → block = []
  length_le_of_pos : 0 < quittingFiniteWordDebt reward roots →
    block.length ≤ 1 + quittingSoloCapThresholdHorizon M
      (quittingFiniteWordDebt reward roots /
        (32 * (M + quittingFiniteWordDebt reward roots)))
      (reward (quittingSingletonTerminal (preemption.blocker owner))
          (preemption.blocker owner) -
        reward (quittingSingletonTerminal owner) (preemption.blocker owner))
  debt_le_of_pos : 0 < quittingFiniteWordDebt reward roots →
    quittingFiniteWordDebt reward (block ++ roots) ≤
      quittingFiniteWordDebt reward roots -
        3 * quittingFiniteWordDebt reward roots ^ 2 /
          (32 * M + 6 * quittingFiniteWordDebt reward roots)

theorem exists_quittingSelectedOwnerRenewal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (roots : List (ι → PMF Bool)) :
    Nonempty (QuittingSelectedOwnerRenewal reward Eligible preemption M roots) := by
  by_cases hpositive : 0 < quittingFiniteWordDebt reward roots
  · obtain ⟨owner, hownerEligible, howner, block, hlength, hdebt⟩ :=
      exists_finiteWord_ownerExclusion_witnessed_quadraticDebtStep
        reward Eligible hWE preemption roots hM hreward hpositive
    exact ⟨{
      owner := owner
      owner_eligible := hownerEligible
      owner_payoff_le_singleton := howner
      block := block
      block_eq_nil_of_nonpos := fun hnonpos => (hnonpos hpositive).elim
      length_le_of_pos := fun _ => hlength
      debt_le_of_pos := fun _ => hdebt }⟩
  · obtain ⟨owner, hownerEligible, howner⟩ := hWE roots
    exact ⟨{
      owner := owner
      owner_eligible := hownerEligible
      owner_payoff_le_singleton := howner
      block := []
      block_eq_nil_of_nonpos := fun _ => rfl
      length_le_of_pos := fun hpos => (hpositive hpos).elim
      debt_le_of_pos := fun hpos => (hpositive hpos).elim }⟩

/-- The canonical selected eligible-owner renewal. -/
def quittingSelectedOwnerRenewal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (roots : List (ι → PMF Bool)) :
    QuittingSelectedOwnerRenewal reward Eligible preemption M roots :=
  Classical.choice
    (exists_quittingSelectedOwnerRenewal
      reward Eligible hWE preemption M hM hreward roots)

/-- Literal words obtained by repeatedly prefixing the selected renewal. -/
def quittingSelectedOwnerExactWords
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ℕ → List (ι → PMF Bool)
  | 0 => []
  | phase + 1 =>
      let old := quittingSelectedOwnerExactWords
        reward Eligible hWE preemption M hM hreward phase
      (quittingSelectedOwnerRenewal
        reward Eligible hWE preemption M hM hreward old).block ++ old

@[simp] theorem quittingSelectedOwnerExactWords_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingSelectedOwnerExactWords
      reward Eligible hWE preemption M hM hreward 0 = [] := rfl

@[simp] theorem quittingSelectedOwnerExactWords_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) :
    quittingSelectedOwnerExactWords reward Eligible hWE preemption M hM hreward
        (phase + 1) =
      (quittingSelectedOwnerRenewal reward Eligible hWE preemption M hM hreward
        (quittingSelectedOwnerExactWords
          reward Eligible hWE preemption M hM hreward phase)).block ++
      quittingSelectedOwnerExactWords
        reward Eligible hWE preemption M hM hreward phase := rfl

/-- Total debt along the selected eligible-owner words. -/
def quittingSelectedOwnerExactWordDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) : ℝ :=
  quittingFiniteWordDebt reward
    (quittingSelectedOwnerExactWords
      reward Eligible hWE preemption M hM hreward phase)

theorem quittingSelectedOwnerExactWordDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) :
    0 ≤ quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward phase := by
  unfold quittingSelectedOwnerExactWordDebt quittingFiniteWordDebt
  exact Finset.sum_nonneg fun player _ =>
    quittingTerminalSemanticDebt_nonneg_of_attainable reward
      ⟨quittingLiteralRootStackProfile reward
        (quittingSelectedOwnerExactWords
          reward Eligible hWE preemption M hM hreward phase)
        (quittingAlwaysContinueProfile reward), rfl⟩ player

theorem quittingSelectedOwnerExactWordDebt_step_of_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ)
    (hpositive : 0 < quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward phase) :
    quittingSelectedOwnerExactWordDebt
        reward Eligible hWE preemption M hM hreward (phase + 1) ≤
      quittingSelectedOwnerExactWordDebt
          reward Eligible hWE preemption M hM hreward phase -
        3 * quittingSelectedOwnerExactWordDebt
            reward Eligible hWE preemption M hM hreward phase ^ 2 /
          (32 * M + 6 * quittingSelectedOwnerExactWordDebt
            reward Eligible hWE preemption M hM hreward phase) := by
  unfold quittingSelectedOwnerExactWordDebt
  rw [quittingSelectedOwnerExactWords_succ]
  exact (quittingSelectedOwnerRenewal
    reward Eligible hWE preemption M hM hreward _).debt_le_of_pos hpositive

theorem quittingSelectedOwnerExactWordDebt_step_of_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ)
    (hnonpos : ¬ 0 < quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward phase) :
    quittingSelectedOwnerExactWordDebt
        reward Eligible hWE preemption M hM hreward (phase + 1) =
      quittingSelectedOwnerExactWordDebt
        reward Eligible hWE preemption M hM hreward phase := by
  unfold quittingSelectedOwnerExactWordDebt
  rw [quittingSelectedOwnerExactWords_succ,
    (quittingSelectedOwnerRenewal
      reward Eligible hWE preemption M hM hreward _).block_eq_nil_of_nonpos hnonpos]
  simp

theorem quittingSelectedOwnerExactWordDebt_antitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Antitone (quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward) := by
  apply antitone_nat_of_succ_le
  intro phase
  by_cases hpositive : 0 < quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward phase
  · have hstep := quittingSelectedOwnerExactWordDebt_step_of_pos
      reward Eligible hWE preemption M hM hreward phase hpositive
    have hdrop : 0 ≤ 3 * quittingSelectedOwnerExactWordDebt
        reward Eligible hWE preemption M hM hreward phase ^ 2 /
          (32 * M + 6 * quittingSelectedOwnerExactWordDebt
            reward Eligible hWE preemption M hM hreward phase) := by
      positivity
    linarith
  · rw [quittingSelectedOwnerExactWordDebt_step_of_nonpos
      reward Eligible hWE preemption M hM hreward phase hpositive]

theorem quittingSelectedOwnerExactWordDebt_fixedQuadraticStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ)
    (hpositive : 0 < quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward phase) :
    let initial := quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward 0
    let scale := (32 * M + 6 * initial) / 3
    quittingSelectedOwnerExactWordDebt
        reward Eligible hWE preemption M hM hreward (phase + 1) ≤
      quittingSelectedOwnerExactWordDebt
          reward Eligible hWE preemption M hM hreward phase -
        quittingSelectedOwnerExactWordDebt
            reward Eligible hWE preemption M hM hreward phase ^ 2 / scale := by
  dsimp only
  let debt := quittingSelectedOwnerExactWordDebt
    reward Eligible hWE preemption M hM hreward
  have hcurrentNonnegative := quittingSelectedOwnerExactWordDebt_nonneg
    reward Eligible hWE preemption M hM hreward phase
  have hinitialNonnegative := quittingSelectedOwnerExactWordDebt_nonneg
    reward Eligible hWE preemption M hM hreward 0
  have hcurrentLeInitial := quittingSelectedOwnerExactWordDebt_antitone
    reward Eligible hWE preemption M hM hreward (Nat.zero_le phase)
  have hcurrentDenom : 0 < 32 * M + 6 * debt phase := by positivity
  have hscale : 0 < (32 * M + 6 * debt 0) / 3 := by positivity
  have hdenomLe : 32 * M + 6 * debt phase ≤ 32 * M + 6 * debt 0 := by
    linarith
  have hquotient : debt phase ^ 2 / ((32 * M + 6 * debt 0) / 3) ≤
      3 * debt phase ^ 2 / (32 * M + 6 * debt phase) := by
    apply (div_le_div_iff₀ hscale hcurrentDenom).2
    nlinarith [sq_nonneg (debt phase)]
  have hraw := quittingSelectedOwnerExactWordDebt_step_of_pos
    reward Eligible hWE preemption M hM hreward phase hpositive
  dsimp only [debt] at hquotient hraw ⊢
  linarith

/-- A selected-owner renewal crosses a positive debt threshold within the
explicit reciprocal phase count. -/
theorem exists_quittingSelectedOwnerExactWordDebt_le_of_phase_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    let initial := quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward 0
    let scale := (32 * M + 6 * initial) / 3
    ∃ phase ≤ Nat.ceil (scale / ε),
      quittingSelectedOwnerExactWordDebt
        reward Eligible hWE preemption M hM hreward phase ≤ ε := by
  dsimp only
  let debt := quittingSelectedOwnerExactWordDebt
    reward Eligible hWE preemption M hM hreward
  let scale := (32 * M + 6 * debt 0) / 3
  have hinitialNonnegative := quittingSelectedOwnerExactWordDebt_nonneg
    reward Eligible hWE preemption M hM hreward 0
  have hscale : 0 < scale := by dsimp only [scale]; positivity
  have hstep : ∀ phase, 0 < debt phase →
      debt (phase + 1) ≤ debt phase - debt phase ^ 2 / scale := by
    intro phase hpositive
    simpa only [debt, scale] using
      quittingSelectedOwnerExactWordDebt_fixedQuadraticStep
        reward Eligible hWE preemption M hM hreward phase hpositive
  simpa only [debt, scale] using
    Math.exists_index_le_ceil_of_quadratic_descent debt hscale hε hstep

/-- Fixed-table row bound for one phase above the target debt.  Its logarithm
depends on the eligible-owner preemption floor. -/
def quittingSelectedOwnerUniformPhaseRowBound
    (M initial ε gap : ℝ) : ℕ :=
  1 + Nat.ceil
    (32 * (M + initial) / ε * Real.log (4 * M / gap))

theorem quittingSelectedOwnerRenewal_length_le_uniform
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℝ} (hε : 0 < ε) (phase : ℕ)
    (habove : ε < quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward phase) :
    let initial := quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward 0
    let old := quittingSelectedOwnerExactWords
      reward Eligible hWE preemption M hM hreward phase
    (quittingSelectedOwnerRenewal
        reward Eligible hWE preemption M hM hreward old).block.length ≤
      quittingSelectedOwnerUniformPhaseRowBound
        M initial ε preemption.gap := by
  dsimp only
  let debt := quittingSelectedOwnerExactWordDebt
    reward Eligible hWE preemption M hM hreward
  let old := quittingSelectedOwnerExactWords
    reward Eligible hWE preemption M hM hreward phase
  let renewal := quittingSelectedOwnerRenewal
    reward Eligible hWE preemption M hM hreward old
  let D := debt phase
  let initial := debt 0
  let ell := reward (quittingSingletonTerminal (preemption.blocker renewal.owner))
      (preemption.blocker renewal.owner) -
    reward (quittingSingletonTerminal renewal.owner) (preemption.blocker renewal.owner)
  have hD : 0 < D := hε.trans habove
  have hlength := renewal.length_le_of_pos hD
  have hDleInitial : D ≤ initial :=
    quittingSelectedOwnerExactWordDebt_antitone
      reward Eligible hWE preemption M hM hreward (Nat.zero_le phase)
  have hell : 0 < ell :=
    preemption.gap_pos.trans_le
      (preemption.gap_le renewal.owner renewal.owner_eligible)
  have hgapLeEll : preemption.gap ≤ ell :=
    preemption.gap_le renewal.owner renewal.owner_eligible
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
    quittingSelectedOwnerUniformPhaseRowBound M initial ε preemption.gap
  exact hlength.trans (Nat.add_le_add_left (Nat.ceil_mono hproduct) 1)

/-- The first selected phase reaching the target debt. -/
theorem exists_quittingSelectedOwnerExactWordDebt_first_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    let initial := quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward 0
    let scale := (32 * M + 6 * initial) / 3
    ∃ phase ≤ Nat.ceil (scale / ε),
      quittingSelectedOwnerExactWordDebt
          reward Eligible hWE preemption M hM hreward phase ≤ ε ∧
        ∀ earlier < phase, ε < quittingSelectedOwnerExactWordDebt
          reward Eligible hWE preemption M hM hreward earlier := by
  dsimp only
  obtain ⟨witness, hwitnessLe, hwitness⟩ :=
    exists_quittingSelectedOwnerExactWordDebt_le_of_phase_bound
      reward Eligible hWE preemption M hM hreward hε
  let debt := quittingSelectedOwnerExactWordDebt
    reward Eligible hWE preemption M hM hreward
  have hexists : ∃ phase, debt phase ≤ ε := ⟨witness, hwitness⟩
  let phase := Nat.find hexists
  have hhit : debt phase ≤ ε := Nat.find_spec hexists
  have hphaseLe : phase ≤ witness := Nat.find_min' hexists hwitness
  refine ⟨phase, hphaseLe.trans hwitnessLe, hhit, ?_⟩
  intro earlier hearlier
  exact lt_of_not_ge (Nat.find_min hexists hearlier)

/-- The first target-crossing word has phase count times the uniform
fixed-table row bound. -/
theorem exists_quittingSelectedOwnerExactWord_debt_and_length_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    let initial := quittingSelectedOwnerExactWordDebt
      reward Eligible hWE preemption M hM hreward 0
    let scale := (32 * M + 6 * initial) / 3
    ∃ phase ≤ Nat.ceil (scale / ε),
      quittingSelectedOwnerExactWordDebt
          reward Eligible hWE preemption M hM hreward phase ≤ ε ∧
        (quittingSelectedOwnerExactWords
          reward Eligible hWE preemption M hM hreward phase).length ≤
          phase * quittingSelectedOwnerUniformPhaseRowBound
            M initial ε preemption.gap := by
  dsimp only
  obtain ⟨phase, hphaseLe, hhit, hbefore⟩ :=
    exists_quittingSelectedOwnerExactWordDebt_first_le
      reward Eligible hWE preemption M hM hreward hε
  let words := quittingSelectedOwnerExactWords
    reward Eligible hWE preemption M hM hreward
  let debt := quittingSelectedOwnerExactWordDebt
    reward Eligible hWE preemption M hM hreward
  let initial := debt 0
  let rowBound := quittingSelectedOwnerUniformPhaseRowBound
    M initial ε preemption.gap
  have hlength : ∀ time, time ≤ phase →
      (words time).length ≤ time * rowBound := by
    intro time htime
    induction time with
    | zero => simp only [words, quittingSelectedOwnerExactWords_zero,
        List.length_nil, zero_mul, le_refl]
    | succ time ih =>
        have htimeLt : time < phase := by omega
        have holdAbove : ε < debt time := hbefore time htimeLt
        have hblock := quittingSelectedOwnerRenewal_length_le_uniform
          reward Eligible hWE preemption M hM hreward hε time holdAbove
        have holdLength := ih (by omega)
        simp only [words, quittingSelectedOwnerExactWords_succ, List.length_append]
        change _ + (words time).length ≤ (time + 1) * rowBound
        change _ ≤ rowBound at hblock
        calc
          _ ≤ rowBound + time * rowBound := Nat.add_le_add hblock holdLength
          _ = (time + 1) * rowBound := by rw [Nat.succ_mul, Nat.add_comm]
  refine ⟨phase, hphaseLe, hhit, ?_⟩
  exact hlength phase le_rfl

/-- A finite literal word with the complete fixed-table phase and date bounds. -/
theorem exists_finiteWord_debtSum_and_length_le_of_ownerExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    let initial := quittingFiniteWordDebt reward []
    let scale := (32 * M + 6 * initial) / 3
    ∃ roots : List (ι → PMF Bool),
      quittingFiniteWordDebt reward roots ≤ ε ∧
        roots.length ≤ Nat.ceil (scale / ε) *
          quittingSelectedOwnerUniformPhaseRowBound
            M initial ε preemption.gap := by
  dsimp only
  obtain ⟨phase, hphaseLe, hdebt, hlength⟩ :=
    exists_quittingSelectedOwnerExactWord_debt_and_length_le
      reward Eligible hWE preemption M hM hreward hε
  refine ⟨quittingSelectedOwnerExactWords
    reward Eligible hWE preemption M hM hreward phase, hdebt, ?_⟩
  exact hlength.trans (Nat.mul_le_mul_right _ hphaseLe)

end GameTheory
