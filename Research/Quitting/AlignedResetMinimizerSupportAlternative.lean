import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.RectangleResetFaceMinimizer

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every semantic carrier point has a compatible complete-law lift. -/
theorem exists_terminalSemanticLawCarrier_lift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    ∃ mass : QuittingTerminalOutcome ι → ℝ,
      (pair, mass) ∈ quittingTerminalSemanticLawCarrier reward := by
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward pair hpair
  let points : ℕ → QuittingTerminalSemanticLawPoint ι := fun n =>
    (quittingTerminalSemanticPair reward (profiles n),
      quittingTerminalOutcomeMass reward (profiles n))
  have hpoints : ∀ n,
      points n ∈ quittingTerminalSemanticLawCarrier reward := by
    intro n
    exact quittingTerminalSemanticLawPoint_mem_carrier reward (profiles n)
  obtain ⟨cluster, hcluster, subseq, hsubseq, hlimit⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq
      hpoints
  have hclusterFst : Tendsto (fun n => (points (subseq n)).1)
      atTop (nhds cluster.1) :=
    continuous_fst.tendsto cluster |>.comp hlimit
  have hpairFst : Tendsto (fun n => (points (subseq n)).1)
      atTop (nhds pair) := by
    simpa only [points] using hprofiles.comp hsubseq.tendsto_atTop
  have hfst : cluster.1 = pair :=
    tendsto_nhds_unique hclusterFst hpairFst
  refine ⟨cluster.2, ?_⟩
  have hclusterEq : cluster = (pair, cluster.2) :=
    Prod.ext hfst rfl
  rw [← hclusterEq]
  exact hcluster

/-- Re-extract at a minimum-fiber point whose positive-debt support loses one
old active coordinate and enters no old inactive coordinate. -/
theorem QuittingPositiveMinimumDebtTangentFamily.exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (point : QuittingTerminalSemanticPair ι)
    (hpoint : point ∈ quittingTerminalSemanticCarrier reward)
    (hminimumFiber : quittingTerminalSemanticDebtSum point =
      quittingTerminalSemanticDebtSum frontier.base)
    (hsupportSubset : ∀ who,
      0 < quittingTerminalSemanticDebt point who →
        who ∈ frontier.positiveDebtSupport)
    (hvanished : ∃ who ∈ frontier.positiveDebtSupport,
      quittingTerminalSemanticDebt point who = 0) :
    ∃ next : QuittingPositiveMinimumDebtTangentFamily reward,
      next.base = point ∧
        next.positiveDebtSupport ⊂ frontier.positiveDebtSupport := by
  have hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point ≤
        quittingTerminalSemanticDebtSum candidate := by
    intro candidate hcandidate
    rw [hminimumFiber]
    exact frontier.base_minimum candidate hcandidate
  have hpositive : 0 < quittingTerminalSemanticDebtSum point := by
    rw [hminimumFiber]
    exact frontier.base_positive
  obtain ⟨next, hnextBase⟩ :=
    exists_positiveMinimumDebtTangentFamily_of_pair point hpoint hminimum
      hpositive
  refine ⟨next, hnextBase, Finset.ssubset_iff_subset_ne.mpr ?_⟩
  constructor
  · intro who hwho
    have hpositiveWho : 0 < quittingTerminalSemanticDebt point who := by
      have hnextPositive := (next.positiveDebtSupport_iff who).1 hwho
      simpa only [hnextBase] using hnextPositive
    exact hsupportSubset who hpositiveWho
  · intro heq
    obtain ⟨who, hwho, hzero⟩ := hvanished
    have hnextWho : who ∈ next.positiveDebtSupport := by
      rw [heq]
      exact hwho
    have hpositiveWho := (next.positiveDebtSupport_iff who).1 hnextWho
    rw [hnextBase, hzero] at hpositiveWho
    exact (lt_irrefl 0) hpositiveWho

end GameTheory
