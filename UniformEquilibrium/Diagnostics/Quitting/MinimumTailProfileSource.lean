import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumLawFiniteAtom

/-!
# Literal profile sources converging to minimum terminal debt

This file isolates the durable boundary needed by the silent-padding consumer.
It retains the literal executable profile sequence, selects a subsequence in the
joint semantic/law carrier, and proves that the selected joint point is again a
global positive-debt minimum.  The source need only supply convergence of total
debt, rather than convergence of the complete semantic pair.

For four-player hard residuals the limiting joint law has a positive finite
coalition coordinate.  No atlas labels, chronological marks, renewal, Nash
profile, or uniform-equilibrium payoff are asserted here.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A literal executable profile sequence whose terminal-semantic total debt
converges to the debt of a supplied positive global minimum. -/
structure QuittingPositiveMinimumTailProfileSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  profiles : ℕ → (quittingGame reward).BehaviorProfile
  minimum : QuittingTerminalSemanticPair ι
  minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward
  minimum_global : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate
  minimumDebt_pos : 0 < quittingTerminalSemanticDebtSum minimum
  debt_tendsto : Tendsto (fun rank ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (profiles rank))) atTop
    (nhds (quittingTerminalSemanticDebtSum minimum))

/-- A compact joint semantic/law limit selected from the literal profile
sequence.  Its semantic coordinate is a positive global debt minimum. -/
structure QuittingPositiveMinimumTailJointCompactification
    (source : QuittingPositiveMinimumTailProfileSource reward) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  point : QuittingTerminalSemanticLawPoint ι
  point_mem : point ∈ quittingTerminalSemanticLawCarrier reward
  point_tendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (source.profiles (subsequence rank)),
        quittingTerminalOutcomeMass reward
          (source.profiles (subsequence rank)))) atTop (nhds point)
  pointDebt_eq_minimumDebt :
    quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalSemanticDebtSum source.minimum

namespace QuittingPositiveMinimumTailJointCompactification

variable {source : QuittingPositiveMinimumTailProfileSource reward}

/-- The semantic coordinate of the selected joint point belongs to the
terminal-semantic carrier. -/
theorem point_semantic_mem
    (compactification :
      QuittingPositiveMinimumTailJointCompactification source) :
    compactification.point.1 ∈ quittingTerminalSemanticCarrier reward :=
  terminalSemanticLawCarrier_fst_mem_carrier
    compactification.point compactification.point_mem

/-- The selected semantic coordinate is a global minimum. -/
theorem point_minimum
    (compactification :
      QuittingPositiveMinimumTailJointCompactification source) :
    ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum compactification.point.1 ≤
        quittingTerminalSemanticDebtSum candidate := by
  intro candidate hcandidate
  rw [compactification.pointDebt_eq_minimumDebt]
  exact source.minimum_global candidate hcandidate

/-- The selected semantic coordinate has positive total debt. -/
theorem pointDebt_pos
    (compactification :
      QuittingPositiveMinimumTailJointCompactification source) :
    0 < quittingTerminalSemanticDebtSum compactification.point.1 := by
  rw [compactification.pointDebt_eq_minimumDebt]
  exact source.minimumDebt_pos

end QuittingPositiveMinimumTailJointCompactification

/-- Every literal minimum-debt tail source has a source-faithful compact joint
semantic/law subsequence. -/
theorem QuittingPositiveMinimumTailProfileSource.nonempty_jointCompactification
    (source : QuittingPositiveMinimumTailProfileSource reward) :
    Nonempty (QuittingPositiveMinimumTailJointCompactification source) := by
  let joint : ℕ → QuittingTerminalSemanticLawPoint ι := fun rank ↦
    (quittingTerminalSemanticPair reward (source.profiles rank),
      quittingTerminalOutcomeMass reward (source.profiles rank))
  have hjoint : ∀ rank,
      joint rank ∈ quittingTerminalSemanticLawCarrier reward := by
    intro rank
    exact quittingTerminalSemanticLawPoint_mem_carrier reward
      (source.profiles rank)
  obtain ⟨point, hpoint, subsequence, hsubsequence, hlimit⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq hjoint
  have hpair : Tendsto (fun rank ↦ (joint (subsequence rank)).1) atTop
      (nhds point.1) :=
    continuous_fst.continuousAt.tendsto.comp hlimit
  have hpointDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum (joint (subsequence rank)).1) atTop
      (nhds (quittingTerminalSemanticDebtSum point.1)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp hpair
  have hminimumDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum (joint (subsequence rank)).1) atTop
      (nhds (quittingTerminalSemanticDebtSum source.minimum)) := by
    exact source.debt_tendsto.comp hsubsequence.tendsto_atTop
  exact ⟨{
    subsequence := subsequence
    subsequence_strictMono := hsubsequence
    point := point
    point_mem := hpoint
    point_tendsto := hlimit
    pointDebt_eq_minimumDebt := tendsto_nhds_unique hpointDebt hminimumDebt }⟩

/-- A four-player literal minimum-tail source attached to the hard residual
which supplies punishment normality and failure of a uniform payoff. -/
structure FinFourHardResidualMinimumTailProfileSource
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) where
  residual : FinFourQuantitativeFullSupportHardResidual reward bound
  tailSource : QuittingPositiveMinimumTailProfileSource reward

/-- A compactification of a four-player hard-residual tail source, together
with one positive coordinate of the limiting finite terminal law. -/
structure FinFourMinimumTailFiniteAtomCompactification
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (source : FinFourHardResidualMinimumTailProfileSource reward bound) where
  compactification :
    QuittingPositiveMinimumTailJointCompactification source.tailSource
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  terminalMass_pos : 0 < compactification.point.2 (some terminal)

/-- Joint compactness and the minimum-law finite-atom theorem turn every
four-player hard-residual tail source into a fixed positive limiting atom. -/
theorem FinFourHardResidualMinimumTailProfileSource.nonempty_finiteAtomCompactification
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (source : FinFourHardResidualMinimumTailProfileSource reward bound) :
    Nonempty (FinFourMinimumTailFiniteAtomCompactification source) := by
  obtain ⟨compactification⟩ := source.tailSource.nonempty_jointCompactification
  obtain ⟨terminal, hterminal⟩ :=
    exists_positive_finiteLawAtom_of_finFourHardResidual_minimum
      reward bound source.residual compactification.point
        compactification.point_mem compactification.point_minimum
  exact ⟨{
    compactification := compactification
    terminal := terminal
    terminalMass_pos := hterminal }⟩

end GameTheory
