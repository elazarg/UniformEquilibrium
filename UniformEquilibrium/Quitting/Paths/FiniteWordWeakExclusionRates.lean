import UniformEquilibrium.Quitting.Paths.FiniteWordSelectedOwnerRates
import UniformEquilibrium.Quitting.Paths.FiniteWordWeakExclusionStep

/-! # Quantitative rates for global weak-exclusion literal finite words

The public global-owner interface specializes the selected-owner recurrence
with every player eligible.  There is only one recursive word construction.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Total complete-deviation debt of a literal finite word followed by Never. -/
abbrev quittingWeakExclusionFiniteWordDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) : ℝ :=
  quittingFiniteWordDebt reward roots

/-- Global renewal is selected-owner renewal with every player eligible. -/
abbrev QuittingWeakExclusionRenewal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (roots : List (ι → PMF Bool)) :=
  QuittingSelectedOwnerRenewal reward (fun _ => True)
    (preemption.toEligible reward) M roots

theorem exists_quittingWeakExclusionRenewal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (roots : List (ι → PMF Bool)) :
    Nonempty (QuittingWeakExclusionRenewal reward preemption M roots) :=
  exists_quittingSelectedOwnerRenewal reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward roots

/-- The canonical selected global weak-exclusion renewal. -/
def quittingWeakExclusionSelectedRenewal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (roots : List (ι → PMF Bool)) :
    QuittingWeakExclusionRenewal reward preemption M roots :=
  quittingSelectedOwnerRenewal reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward roots

/-- Literal words from the shared selected-owner recurrence. -/
def quittingWeakExclusionExactWords
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ℕ → List (ι → PMF Bool) :=
  quittingSelectedOwnerExactWords reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward

@[simp] theorem quittingWeakExclusionExactWords_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingWeakExclusionExactWords reward hWE preemption M hM hreward 0 = [] :=
  quittingSelectedOwnerExactWords_zero reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward

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
      quittingWeakExclusionExactWords reward hWE preemption M hM hreward phase :=
  quittingSelectedOwnerExactWords_succ reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward phase

/-- Total debt along the shared selected words. -/
def quittingWeakExclusionExactWordDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) : ℝ :=
  quittingSelectedOwnerExactWordDebt reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward phase

theorem quittingWeakExclusionExactWordDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (phase : ℕ) :
    0 ≤ quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward phase :=
  quittingSelectedOwnerExactWordDebt_nonneg reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward phase

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
            reward hWE preemption M hM hreward phase) :=
  quittingSelectedOwnerExactWordDebt_step_of_pos reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward phase hpositive

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
      quittingWeakExclusionExactWordDebt reward hWE preemption M hM hreward phase :=
  quittingSelectedOwnerExactWordDebt_step_of_nonpos reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward phase hnonpos

theorem quittingWeakExclusionExactWordDebt_antitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Antitone (quittingWeakExclusionExactWordDebt
      reward hWE preemption M hM hreward) :=
  quittingSelectedOwnerExactWordDebt_antitone reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward

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
            reward hWE preemption M hM hreward phase ^ 2 / scale :=
  quittingSelectedOwnerExactWordDebt_fixedQuadraticStep reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward phase hpositive

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
        reward hWE preemption M hM hreward phase ≤ ε :=
  exists_quittingSelectedOwnerExactWordDebt_le_of_phase_bound reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward hε

/-- The shared fixed-table row bound. -/
abbrev quittingWeakExclusionUniformPhaseRowBound :=
  quittingSelectedOwnerUniformPhaseRowBound

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
        M initial ε preemption.gap :=
  quittingSelectedOwnerRenewal_length_le_uniform reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward hε phase habove

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
          reward hWE preemption M hM hreward earlier :=
  exists_quittingSelectedOwnerExactWordDebt_first_le reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward hε

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
            M initial ε preemption.gap :=
  exists_quittingSelectedOwnerExactWord_debt_and_length_le reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward hε

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
            M initial ε preemption.gap :=
  exists_finiteWord_debtSum_and_length_le_of_ownerExclusion reward (fun _ => True)
    (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
    (preemption.toEligible reward) M hM hreward hε

/-- With nonnegative singleton rewards, all-Never debt is their sum. -/
theorem quittingWeakExclusionFiniteWordDebt_nil_eq_sum_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player) :
    quittingWeakExclusionFiniteWordDebt reward [] =
      ∑ player, reward (quittingSingletonTerminal player) player := by
  unfold quittingWeakExclusionFiniteWordDebt quittingFiniteWordDebt
    quittingTerminalSemanticDebtSum
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
