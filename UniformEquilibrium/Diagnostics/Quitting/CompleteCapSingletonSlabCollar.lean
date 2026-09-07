import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget

/-! # Uniform off-minimum collars for complete-cap singleton slabs -/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A closed singleton-cap slab has a positive debt gap above any positive
global lower bound. The bound need not be supplied with an attaining point. -/
theorem exists_offMinimum_collar_on_completeCap_singletonSlab
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {minimumDebt : ℝ} (hpositive : 0 < minimumDebt)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      minimumDebt ≤ quittingTerminalSemanticDebtSum candidate) :
    ∃ collar : ℝ, 0 < collar ∧
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        |candidate.2 who - reward (quittingSingletonTerminal who) who| ≤
            minimumDebt / 2 →
          minimumDebt + collar ≤ quittingTerminalSemanticDebtSum candidate := by
  let solo := reward (quittingSingletonTerminal who) who
  let slab : Set (QuittingTerminalSemanticPair ι) :=
    quittingTerminalSemanticCarrier reward ∩
      {pair | |pair.2 who - solo| ≤ minimumDebt / 2}
  have hcompact : IsCompact slab := by
    apply (quittingTerminalSemanticCarrier_isCompact reward).inter_right
    exact isClosed_le (continuous_abs.comp
      (((continuous_apply who).comp continuous_snd).sub continuous_const))
      continuous_const
  by_cases hnonempty : slab.Nonempty
  · obtain ⟨selected, hselected, hselectedMin⟩ :=
      hcompact.exists_isMinOn hnonempty
        continuous_quittingTerminalSemanticDebtSum.continuousOn
    have hstrict : minimumDebt < quittingTerminalSemanticDebtSum selected := by
      refine lt_of_le_of_ne (hminimum selected hselected.1) ?_
      intro heq
      have hmargin := minimumTerminalSemantic_singletonMargin
        selected hselected.1 (fun candidate hcandidate => by
          rw [← heq]
          exact hminimum candidate hcandidate) (by rwa [← heq]) who
      have hupper : selected.2 who - solo ≤ minimumDebt / 2 :=
        (abs_le.mp hselected.2).2
      dsimp only [solo] at hupper
      linarith
    refine ⟨(quittingTerminalSemanticDebtSum selected - minimumDebt) / 2,
      by positivity, fun candidate hcandidate hcap => ?_⟩
    have hselectedLe := hselectedMin (show candidate ∈ slab from ⟨hcandidate, hcap⟩)
    change quittingTerminalSemanticDebtSum selected ≤
      quittingTerminalSemanticDebtSum candidate at hselectedLe
    linarith
  · refine ⟨1, zero_lt_one, fun candidate hcandidate hcap => ?_⟩
    exact (hnonempty ⟨candidate, hcandidate, hcap⟩).elim

/-- Uniform parameter-family version: if all profiles at an index have the
same named cap and that cap tends to the singleton, one collar works for all
parameters at every sufficiently late index. No parameter compactness is needed. -/
theorem exists_uniform_offMinimum_collar_of_completeCap_tendsto_singleton
    {Parameter : Type*}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → Parameter → (quittingGame reward).BehaviorProfile)
    (who : ι) (capLevel : ℕ → ℝ)
    {minimumDebt : ℝ} (hpositive : 0 < minimumDebt)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      minimumDebt ≤ quittingTerminalSemanticDebtSum candidate)
    (hcap : ∀ index parameter,
      quittingContinuationBestResponseValue reward (profiles index parameter) who =
        capLevel index)
    (hlimit : Tendsto capLevel atTop
      (nhds (reward (quittingSingletonTerminal who) who))) :
    ∃ collar : ℝ, 0 < collar ∧ ∀ᶠ index in atTop, ∀ parameter,
      minimumDebt + collar ≤
        quittingTerminalDebtSum reward (profiles index parameter) := by
  obtain ⟨collar, hcollar, hslab⟩ :=
    exists_offMinimum_collar_on_completeCap_singletonSlab
      reward who hpositive hminimum
  have hsmall : ∀ᶠ index in atTop,
      |capLevel index - reward (quittingSingletonTerminal who) who| ≤ minimumDebt / 2 :=
    (hlimit.eventually (Metric.closedBall_mem_nhds _ (half_pos hpositive))).mono
      (fun _ h => by simpa [Metric.mem_closedBall, Real.dist_eq] using h)
  refine ⟨collar, hcollar, ?_⟩
  filter_upwards [hsmall] with index hindex
  intro parameter
  apply hslab (quittingTerminalSemanticPair reward (profiles index parameter))
    (subset_closure (Set.mem_range_self (profiles index parameter)))
  change |quittingContinuationBestResponseValue reward (profiles index parameter) who - _| ≤ _
  rw [hcap index parameter]
  exact hindex

end GameTheory
