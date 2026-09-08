import UniformEquilibrium.Quitting.Classification.LCP.FourPlayerSingletonColumnBlockers
import UniformEquilibrium.Quitting.Paths.FiniteWordSelectedOwnerStep

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
/-- Global weak exclusion is selected-owner exclusion with every owner
eligible. -/
theorem finiteWordOwnerExclusion_all_of_weakSingletonExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward) :
    QuittingFiniteWordOwnerExclusion reward (fun _ => True) := by
  intro roots
  obtain ⟨owner, howner⟩ := hWE roots
  exact ⟨owner, True.intro, howner⟩

/-- A global singleton-column blocker certificate is the selected-owner
certificate with every owner eligible. -/
def SingletonColumnBlockerCertificate.toEligible
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (preemption : SingletonColumnBlockerCertificate reward) :
    QuittingEligibleBlockerCertificate reward (fun _ => True) where
  blocker := preemption.blocker
  gap := preemption.gap
  gap_pos := preemption.gap_pos
  blocker_ne := fun owner _ => preemption.blocker_ne owner
  gap_le := fun owner _ => preemption.gap_le owner

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
  obtain ⟨selected⟩ := nonempty_eligibleBlockerCertificate_of_strictPreempted
    reward (fun _ => True) (by exact ⟨Classical.choice inferInstance, True.intro⟩)
      (fun owner _ => hpreempted owner)
  exact ⟨{
    blocker := selected.blocker
    gap := selected.gap
    gap_pos := selected.gap_pos
    blocker_ne := fun owner => selected.blocker_ne owner True.intro
    gap_le := fun owner => selected.gap_le owner True.intro }⟩

/-- One exact cap-threshold phase, selected by weak exclusion, renews an actual finite
word and strictly decreases its total debt by the explicit quadratic term.
The owner's singleton margin is bounded by total debt inside the generic proof. -/
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
  obtain ⟨owner, -, block, hlength, hdebt⟩ :=
    exists_finiteWord_ownerExclusion_quadraticDebtStep
      reward (fun _ => True)
        (finiteWordOwnerExclusion_all_of_weakSingletonExclusion reward hWE)
        (preemption.toEligible reward) oldRoots hM hreward hdebtPos
  exact ⟨owner, block, hlength, hdebt⟩

end GameTheory
