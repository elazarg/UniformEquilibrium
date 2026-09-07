import UniformEquilibrium.Quitting.Paths.FiniteSoloCapThresholdDescent
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps
import UniformEquilibrium.Quitting.Classification.LCP.FourPlayerSingletonColumnBlockers

/-! # Literal finite-word debt descent under weak singleton exclusion -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Weak payoff exclusion on every literal finite word over the all-Never
tail, stated with the owner witness needed by cap-threshold descent. -/
def QuittingFiniteWordWeakSingletonExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ roots : List (ι → PMF Bool), ∃ owner,
    quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward roots
          (quittingAlwaysContinueProfile reward)) owner ≤
      reward (quittingSingletonTerminal owner) owner

omit [DecidableEq ι] in
/-- Pointwise strict preemption over a finite nonempty player set has a
single positive floor, packaged in the existing blocker certificate. -/
theorem nonempty_singletonColumnBlockerCertificate_of_all_strictPreempted
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpreempted : ∀ owner, ∃ blocker, 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker) :
    Nonempty (SingletonColumnBlockerCertificate reward) := by
  classical
  choose blocker hblocker using hpreempted
  let gaps : Finset ℝ := Finset.univ.image fun owner =>
    reward (quittingSingletonTerminal (blocker owner)) (blocker owner) -
      reward (quittingSingletonTerminal owner) (blocker owner)
  have hgaps : gaps.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  let gap := gaps.min' hgaps
  refine ⟨{
    blocker := blocker
    gap := gap
    gap_pos := ?_
    blocker_ne := ?_
    gap_le := ?_ }⟩
  · have hmem := Finset.min'_mem gaps hgaps
    rw [Finset.mem_image] at hmem
    obtain ⟨owner, howner, hgap⟩ := hmem
    change 0 < gaps.min' hgaps
    rw [← hgap]
    exact hblocker owner
  · intro owner heq
    have h := hblocker owner
    rw [heq] at h
    linarith
  · intro owner
    exact Finset.min'_le gaps _
      (Finset.mem_image.mpr ⟨owner, Finset.mem_univ owner, rfl⟩)

/-- One exact cap-threshold phase, selected by weak exclusion, renews an actual finite
word and strictly decreases its total debt by the explicit quadratic term.
The owner inequality is converted to `L_owner ≤ D` inside the proof. -/
theorem exists_finiteWord_weakExclusion_quadraticDebtStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (oldRoots : List (ι → PMF Bool))
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdebtPos : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward oldRoots
          (quittingAlwaysContinueProfile reward)))) :
    let source := quittingLiteralRootStackProfile reward oldRoots
      (quittingAlwaysContinueProfile reward)
    let D := quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward source)
    let θ := D / (32 * (M + D))
    ∃ (owner : ι) (block : List (ι → PMF Bool)),
      block.length ≤ 1 + quittingSoloCapThresholdHorizon M θ
        (reward (quittingSingletonTerminal (preemption.blocker owner))
            (preemption.blocker owner) -
          reward (quittingSingletonTerminal owner) (preemption.blocker owner)) ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward (block ++ oldRoots)
              (quittingAlwaysContinueProfile reward))) ≤
        D - 3 * D ^ 2 / (32 * M + 6 * D) := by
  dsimp only
  let source := quittingLiteralRootStackProfile reward oldRoots
    (quittingAlwaysContinueProfile reward)
  let pair := quittingTerminalSemanticPair reward source
  let D := quittingTerminalSemanticDebtSum pair
  obtain ⟨owner, howner⟩ := hWE oldRoots
  change pair.1 owner ≤ reward (quittingSingletonTerminal owner) owner at howner
  have hownerDebtLe : quittingTerminalSemanticDebt pair owner ≤ D := by
    dsimp only [D, quittingTerminalSemanticDebtSum]
    exact Finset.single_le_sum
      (fun player _ => quittingTerminalSemanticDebt_nonneg_of_attainable
        reward ⟨source, rfl⟩ player)
      (Finset.mem_univ owner)
  have hmarginLeDebt : pair.2 owner -
      reward (quittingSingletonTerminal owner) owner ≤
        quittingTerminalSemanticDebt pair owner := by
    dsimp only [pair, source, quittingTerminalSemanticDebt]
    linarith
  have hmarginLe : pair.2 owner -
      reward (quittingSingletonTerminal owner) owner ≤ D :=
    hmarginLeDebt.trans hownerDebtLe
  have hpreempted : 0 <
      reward (quittingSingletonTerminal (preemption.blocker owner))
          (preemption.blocker owner) -
        reward (quittingSingletonTerminal owner) (preemption.blocker owner) :=
    preemption.gap_pos.trans_le (preemption.gap_le owner)
  obtain ⟨block, hlength, hdebt⟩ :=
    exists_literal_capThreshold_block_debtSum_le_quadraticDrop
      reward source owner (preemption.blocker owner) hM hreward
        (by simpa only [D, pair, source] using hdebtPos) hpreempted
  have hmax : max D
      (pair.2 owner - reward (quittingSingletonTerminal owner) owner) = D :=
    max_eq_left hmarginLe
  refine ⟨owner, block, ?_, ?_⟩
  · change block.length ≤ 1 + quittingSoloCapThresholdHorizon M
        (max D (pair.2 owner - reward (quittingSingletonTerminal owner) owner) /
          (32 * (M +
            max D (pair.2 owner - reward (quittingSingletonTerminal owner) owner))))
        (reward (quittingSingletonTerminal (preemption.blocker owner))
            (preemption.blocker owner) -
          reward (quittingSingletonTerminal owner) (preemption.blocker owner)) at hlength
    rw [hmax] at hlength
    exact hlength
  · rw [quittingLiteralRootStackProfile_append]
    change quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward block source)) ≤
      D - 3 * D ^ 2 / (32 * M + 6 * D)
    change quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward block source)) ≤
      max D (pair.2 owner - reward (quittingSingletonTerminal owner) owner) -
        3 * max D (pair.2 owner - reward (quittingSingletonTerminal owner) owner) ^ 2 /
          (32 * M +
            6 * max D (pair.2 owner - reward (quittingSingletonTerminal owner) owner)) at hdebt
    rw [hmax] at hdebt
    exact hdebt

/-- Repeated exact cap-threshold renewal terminates at a literal finite word of any
prescribed positive total-debt accuracy. This is the qualitative actual-word
iteration; no phase-count claim is folded into it. -/
theorem exists_finiteWord_debtSum_le_of_weakExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ roots : List (ι → PMF Bool),
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward))) ≤ ε := by
  let debt : List (ι → PMF Bool) → ℝ := fun roots =>
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots
          (quittingAlwaysContinueProfile reward)))
  have hdebtNonnegative : ∀ roots, 0 ≤ debt roots := by
    intro roots
    unfold debt quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun player _ =>
      quittingTerminalSemanticDebt_nonneg_of_attainable reward
        ⟨quittingLiteralRootStackProfile reward roots
          (quittingAlwaysContinueProfile reward), rfl⟩ player
  have hstepExists : ∀ roots, 0 < debt roots →
      ∃ block : List (ι → PMF Bool),
        debt (block ++ roots) ≤
          debt roots - 3 * debt roots ^ 2 / (32 * M + 6 * debt roots) := by
    intro roots hpositive
    obtain ⟨owner, block, hlength, hnext⟩ :=
      exists_finiteWord_weakExclusion_quadraticDebtStep
        reward hWE preemption roots hM hreward hpositive
    exact ⟨block, hnext⟩
  let block : List (ι → PMF Bool) → List (ι → PMF Bool) := fun roots =>
    if hpositive : 0 < debt roots then Classical.choose (hstepExists roots hpositive)
    else []
  have hblock : ∀ roots, 0 < debt roots →
      debt (block roots ++ roots) ≤
        debt roots - 3 * debt roots ^ 2 / (32 * M + 6 * debt roots) := by
    intro roots hpositive
    dsimp only [block]
    rw [dif_pos hpositive]
    exact Classical.choose_spec (hstepExists roots hpositive)
  let words : ℕ → List (ι → PMF Bool) := fun phase =>
    Nat.rec [] (fun _ roots => block roots ++ roots) phase
  have hwordsZero : words 0 = [] := rfl
  have hwordsSucc : ∀ phase, words (phase + 1) = block (words phase) ++ words phase := by
    intro phase
    simp only [words]
  let D : ℕ → ℝ := fun phase => debt (words phase)
  have hDnonnegative : ∀ phase, 0 ≤ D phase := fun phase =>
    hdebtNonnegative (words phase)
  by_contra hnone
  push Not at hnone
  have hDabove : ∀ phase, ε < D phase := by
    intro phase
    simpa only [D, debt] using hnone (words phase)
  have hDstep : ∀ phase,
      D (phase + 1) ≤ D phase - 3 * D phase ^ 2 / (32 * M + 6 * D phase) := by
    intro phase
    dsimp only [D]
    rw [hwordsSucc]
    exact hblock (words phase) (hε.trans (hDabove phase))
  have hDleInitial : ∀ phase, D phase ≤ D 0 := by
    intro phase
    induction phase with
    | zero => exact le_rfl
    | succ phase ih =>
        have hdenom : 0 < 32 * M + 6 * D phase := by
          nlinarith [hDnonnegative phase]
        have hdrop : 0 ≤ 3 * D phase ^ 2 / (32 * M + 6 * D phase) := by
          positivity
        exact (hDstep phase).trans ((sub_le_self _ hdrop).trans ih)
  let δ := 3 * ε ^ 2 / (32 * M + 6 * D 0)
  have hdenomInitial : 0 < 32 * M + 6 * D 0 := by
    nlinarith [hDnonnegative 0]
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hdropFloor : ∀ phase, δ ≤
      3 * D phase ^ 2 / (32 * M + 6 * D phase) := by
    intro phase
    have hdenom : 0 < 32 * M + 6 * D phase := by
      nlinarith [hDnonnegative phase]
    have hdenomLe : 32 * M + 6 * D phase ≤ 32 * M + 6 * D 0 := by
      linarith [hDleInitial phase]
    have hsquare : ε ^ 2 ≤ D phase ^ 2 := by
      nlinarith [hε, hDabove phase]
    dsimp only [δ]
    apply (div_le_div_iff₀ hdenomInitial hdenom).2
    have hleft := mul_le_mul_of_nonneg_right hsquare (by norm_num : (0 : ℝ) ≤ 3)
    have hright := mul_le_mul_of_nonneg_left hdenomLe
      (by positivity : 0 ≤ 3 * D phase ^ 2)
    nlinarith [mul_nonneg (show 0 ≤ 3 * ε ^ 2 by positivity) hdenom.le]
  have hlinear : ∀ phase, D phase ≤ D 0 - (phase : ℝ) * δ := by
    intro phase
    induction phase with
    | zero => simp
    | succ phase ih =>
        have hstep := (hDstep phase).trans
          (sub_le_sub_left (hdropFloor phase) (D phase))
        push_cast
        nlinarith
  obtain ⟨phase, hphase⟩ := exists_nat_gt (D 0 / δ)
  have hnegative : D 0 - (phase : ℝ) * δ < 0 := by
    have := (div_lt_iff₀ hδ).mp hphase
    nlinarith
  linarith [hDnonnegative phase, hlinear phase]

/-- General all-preempted form: the common finite preemption floor is
constructed internally rather than supplied as input. -/
theorem exists_finiteWord_debtSum_le_of_weakExclusion_allPreempted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (hpreempted : ∀ owner, ∃ blocker, 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker)
    {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ roots : List (ι → PMF Bool),
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward))) ≤ ε := by
  obtain ⟨owner, howner⟩ := hWE []
  letI : Nonempty ι := ⟨owner⟩
  obtain ⟨preemption⟩ :=
    nonempty_singletonColumnBlockerCertificate_of_all_strictPreempted
      reward hpreempted
  exact exists_finiteWord_debtSum_le_of_weakExclusion
    reward hWE preemption hM hε hreward

/-- The produced literal finite words at every accuracy feed the standard
all-errors selector and therefore yield one fixed uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_finiteWordWeakExclusion_allPreempted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (hpreempted : ∀ owner, ∃ blocker, 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let M := quittingRewardBound reward + 1
  have hM : 0 < M := by
    dsimp only [M]
    linarith [quittingRewardBound_nonneg reward]
  have hreward : ∀ terminal player, |reward terminal player| ≤ M := by
    intro terminal player
    exact (abs_reward_le_quittingRewardBound reward terminal player).trans (by
      dsimp only [M]
      linarith)
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro ε hε
  obtain ⟨roots, hdebt⟩ :=
    exists_finiteWord_debtSum_le_of_weakExclusion_allPreempted
      reward hWE hpreempted hM hε hreward
  refine ⟨quittingLiteralRootStackProfile reward roots
    (quittingAlwaysContinueProfile reward), ?_⟩
  exact isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le reward _ hdebt

end GameTheory
