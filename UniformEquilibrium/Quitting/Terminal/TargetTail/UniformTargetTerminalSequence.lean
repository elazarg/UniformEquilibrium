import UniformEquilibrium.Quitting.Classification.Existence.UniformPayoffTerminalSemanticCarrier
import UniformEquilibrium.Quitting.Terminal.TerminalExploitability

/-! # Actual terminal approximants of a fixed uniform payoff target -/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A fixed uniform payoff supplies actual terminal profiles with vanishing
unrestricted exploitability and payoffs converging to that same target. -/
theorem exists_terminalProfile_sequence_exploitability_tendsto_zero_of_uniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (target : Payoff ι)
    (huniform : (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      Tendsto (fun n ↦ quittingTerminalPayoff reward (profiles n)) atTop (nhds target) ∧
      Tendsto (fun n ↦ quittingTerminalExploitability reward (profiles n)) atTop (nhds 0) := by
  have hmem := (isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier
    reward target).mp huniform
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward (target, target) hmem
  refine ⟨profiles, ?_, ?_⟩
  · exact continuous_fst.continuousAt.tendsto.comp hprofiles
  have hzero : quittingTerminalSemanticExploitability (target, target) = 0 := by
    unfold quittingTerminalSemanticExploitability QuittingBoundaryHolonomy.finitePlayerMax
      quittingTerminalSemanticDebt
    simp
  have h := continuous_quittingTerminalSemanticExploitability.continuousAt.tendsto.comp hprofiles
  rw [hzero] at h
  change Tendsto (fun n ↦ quittingTerminalSemanticExploitability
    (quittingTerminalSemanticPair reward (profiles n))) atTop (nhds 0) at h
  simpa only [quittingTerminalSemanticExploitability_pair] using h

end GameTheory
