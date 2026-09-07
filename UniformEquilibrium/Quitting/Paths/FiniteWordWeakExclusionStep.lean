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

end GameTheory
