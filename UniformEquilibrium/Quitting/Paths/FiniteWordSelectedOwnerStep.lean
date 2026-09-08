import UniformEquilibrium.Quitting.Paths.FiniteSoloCapThresholdDescent

/-! # A selected-owner cap-threshold renewal step

This is the owner-selection layer shared by global and designated weak
exclusion.  Eligibility controls both the exclusion witness and the range on
which a common strict-preemption certificate is required.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Total complete-deviation debt of a literal finite word followed by Never. -/
def quittingFiniteWordDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) : ℝ :=
  quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward
      (quittingLiteralRootStackProfile reward roots
        (quittingAlwaysContinueProfile reward)))

/-- Every literal word has a weak-exclusion witness satisfying `Eligible`. -/
def QuittingFiniteWordOwnerExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop) : Prop :=
  ∀ roots : List (ι → PMF Bool), ∃ owner, Eligible owner ∧
    quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward roots
          (quittingAlwaysContinueProfile reward)) owner ≤
      reward (quittingSingletonTerminal owner) owner

/-- A positive preemption floor only over owners eligible for selection.  The
blocker function is total so the quantitative recurrence does not carry proof
arguments in its data. -/
structure QuittingEligibleBlockerCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop) where
  blocker : ι → ι
  gap : ℝ
  gap_pos : 0 < gap
  blocker_ne : ∀ owner, Eligible owner → blocker owner ≠ owner
  gap_le : ∀ owner, Eligible owner → gap ≤
    reward (quittingSingletonTerminal (blocker owner)) (blocker owner) -
      reward (quittingSingletonTerminal owner) (blocker owner)

omit [DecidableEq ι] in
/-- Finitely many eligible owners with pointwise strict preemptors admit one
common positive preemption floor. -/
theorem nonempty_eligibleBlockerCertificate_of_strictPreempted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hexists : ∃ owner, Eligible owner)
    (hpreempted : ∀ owner, Eligible owner → ∃ blocker, 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker) :
    Nonempty (QuittingEligibleBlockerCertificate reward Eligible) := by
  classical
  let fallback := Classical.choose hexists
  let blocker : ι → ι := fun owner =>
    if howner : Eligible owner then Classical.choose (hpreempted owner howner)
    else fallback
  let eligibleOwners := Finset.univ.filter Eligible
  have heligibleOwners : eligibleOwners.Nonempty := by
    obtain ⟨owner, howner⟩ := hexists
    exact ⟨owner, Finset.mem_filter.mpr ⟨Finset.mem_univ _, howner⟩⟩
  let gaps : Finset ℝ := eligibleOwners.image fun owner =>
    reward (quittingSingletonTerminal (blocker owner)) (blocker owner) -
      reward (quittingSingletonTerminal owner) (blocker owner)
  have hgaps : gaps.Nonempty := Finset.image_nonempty.mpr heligibleOwners
  let gap := gaps.min' hgaps
  have hblocker (owner : ι) (howner : Eligible owner) : 0 <
      reward (quittingSingletonTerminal (blocker owner)) (blocker owner) -
        reward (quittingSingletonTerminal owner) (blocker owner) := by
    dsimp only [blocker]
    rw [dif_pos howner]
    exact Classical.choose_spec (hpreempted owner howner)
  refine ⟨{
    blocker := blocker
    gap := gap
    gap_pos := ?_
    blocker_ne := ?_
    gap_le := ?_ }⟩
  · have hmem := Finset.min'_mem gaps hgaps
    rw [Finset.mem_image] at hmem
    obtain ⟨owner, hownerSet, hgap⟩ := hmem
    change 0 < gaps.min' hgaps
    rw [← hgap]
    have howner : Eligible owner := by
      have := Finset.mem_filter.mp hownerSet
      exact this.2
    exact hblocker owner howner
  · intro owner howner heq
    have hpositive := hblocker owner howner
    rw [heq] at hpositive
    linarith
  · intro owner howner
    apply Finset.min'_le gaps
    apply Finset.mem_image.mpr
    exact ⟨owner, Finset.mem_filter.mpr ⟨Finset.mem_univ _, howner⟩, rfl⟩

/-- One selected-owner exact cap-threshold phase, retaining its blocker and
literal block length as well as the quadratic total-debt drop. -/
theorem exists_finiteWord_ownerExclusion_quadraticDebtStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (Eligible : ι → Prop)
    (hWE : QuittingFiniteWordOwnerExclusion reward Eligible)
    (preemption : QuittingEligibleBlockerCertificate reward Eligible)
    (oldRoots : List (ι → PMF Bool))
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdebtPos : 0 < quittingFiniteWordDebt reward oldRoots) :
    let D := quittingFiniteWordDebt reward oldRoots
    let θ := D / (32 * (M + D))
    ∃ (owner : ι) (_ : Eligible owner) (block : List (ι → PMF Bool)),
      block.length ≤ 1 + quittingSoloCapThresholdHorizon M θ
        (reward (quittingSingletonTerminal (preemption.blocker owner))
            (preemption.blocker owner) -
          reward (quittingSingletonTerminal owner) (preemption.blocker owner)) ∧
      quittingFiniteWordDebt reward (block ++ oldRoots) ≤
        D - 3 * D ^ 2 / (32 * M + 6 * D) := by
  dsimp only
  let source := quittingLiteralRootStackProfile reward oldRoots
    (quittingAlwaysContinueProfile reward)
  let pair := quittingTerminalSemanticPair reward source
  let D := quittingFiniteWordDebt reward oldRoots
  obtain ⟨owner, hownerEligible, howner⟩ := hWE oldRoots
  change pair.1 owner ≤ reward (quittingSingletonTerminal owner) owner at howner
  have hownerDebtLe : quittingTerminalSemanticDebt pair owner ≤ D := by
    dsimp only [D, quittingFiniteWordDebt, quittingTerminalSemanticDebtSum]
    exact Finset.single_le_sum
      (fun player _ => quittingTerminalSemanticDebt_nonneg_of_attainable
        reward ⟨source, rfl⟩ player)
      (Finset.mem_univ owner)
  have hmarginLeDebt : pair.2 owner -
      reward (quittingSingletonTerminal owner) owner ≤
        quittingTerminalSemanticDebt pair owner := by
    dsimp only [quittingTerminalSemanticDebt]
    linarith
  have hmarginLe : pair.2 owner -
      reward (quittingSingletonTerminal owner) owner ≤ D :=
    hmarginLeDebt.trans hownerDebtLe
  have hpreempted : 0 <
      reward (quittingSingletonTerminal (preemption.blocker owner))
          (preemption.blocker owner) -
        reward (quittingSingletonTerminal owner) (preemption.blocker owner) :=
    preemption.gap_pos.trans_le (preemption.gap_le owner hownerEligible)
  obtain ⟨block, hlength, hdebt⟩ :=
    exists_literal_capThreshold_block_debtSum_le_quadraticDrop
      reward source owner (preemption.blocker owner) hM hreward
        (by simpa only [D, pair, source, quittingFiniteWordDebt] using hdebtPos)
        hpreempted
  have hmax : max D
      (pair.2 owner - reward (quittingSingletonTerminal owner) owner) = D :=
    max_eq_left hmarginLe
  refine ⟨owner, hownerEligible, block, ?_, ?_⟩
  · change block.length ≤ 1 + quittingSoloCapThresholdHorizon M
        (max D (pair.2 owner - reward (quittingSingletonTerminal owner) owner) /
          (32 * (M +
            max D (pair.2 owner - reward (quittingSingletonTerminal owner) owner))))
        (reward (quittingSingletonTerminal (preemption.blocker owner))
            (preemption.blocker owner) -
          reward (quittingSingletonTerminal owner) (preemption.blocker owner)) at hlength
    rw [hmax] at hlength
    exact hlength
  · unfold quittingFiniteWordDebt
    rw [quittingLiteralRootStackProfile_append]
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
