/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.StrictAllContinueBasinLinearAbsorptionDefect
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumFiberIsolation

/-!
# Linear absorption defect on the four-player minimum semantic fiber

The integrated four-player minimum-fiber isolation theorem supplies the
compact strict basin needed by the abstract linear absorption-defect theorem.
Thus, in the no-uniform-payoff branch, one open neighborhood of the entire
prescribed minimum-fiber projection charges absorption linearly at every
scale.  In particular, any sequence of local approximate roots whose declared
errors tend to zero has absorption tending to zero.

This is a root-level, continuation-oriented conclusion.  It neither produces
an incoming Bellman edge nor assigns carrier debt to an arbitrary payoff tail.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open scoped Topology

/-- Literal `Fin 4` no-uniform data gives one linear Nash-defect basin around
the prescribed projection of the complete global-minimum carrier fiber. -/
theorem exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (base : QuittingTerminalSemanticPair (Fin 4))
        (K N : Set (Payoff (Fin 4))) (c C rho : ℝ),
      base ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum base ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalSemanticDebtSum base ∧
      K = Prod.fst '' quittingTerminalSemanticMinimumFiber reward base ∧
      IsCompact K ∧ K.Nonempty ∧ IsOpen N ∧ K ⊆ N ∧
      Bornology.IsBounded N ∧ 0 < c ∧ 0 < C ∧ 0 < rho ∧
      (∀ S player, |reward S player| ≤ C) ∧
      (∀ tail ∈ N, ∀ player, |tail player| ≤ C) ∧
      Metric.thickening rho K ⊆ N ∧
      (∀ tail ∈ N, ∀ root : Fin 4 → PMF Bool,
        c * quittingRootAbsorptionMass root ≤
          quittingRootTotalNashDefect reward tail root) ∧
      ∀ (tail : ℕ → Payoff (Fin 4))
          (root : ℕ → Fin 4 → PMF Bool) (error : ℕ → ℝ),
        (∀ time, tail time ∈ N) →
        (∀ time, IsεQuittingRootNash reward
          (tail time) (error time) (root time)) →
        Tendsto error atTop (nhds 0) →
        Tendsto (fun time => quittingRootAbsorptionMass (root time))
          atTop (nhds 0) := by
  obtain ⟨base, delta, _epsilon, tube, hbase, hminimum, hpositive,
      hdelta, _hepsilon, _htubeOpen, hseparation, hfiberTube,
      hfreeze, _hdebtMoat⟩ :=
    exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff
      reward hno
  let K : Set (Payoff (Fin 4)) :=
    Prod.fst '' quittingTerminalSemanticMinimumFiber reward base
  have hKcompact : IsCompact K := by
    exact (quittingTerminalSemanticMinimumFiber_isCompact reward base).image
      continuous_fst
  have hKnonempty : K.Nonempty := by
    exact (quittingTerminalSemanticMinimumFiber_nonempty reward base hbase).image
      Prod.fst
  have hKgap : ∀ tail ∈ K, ∀ who,
      delta ≤ tail who - reward (quittingSingletonTerminal who) who := by
    intro tail htail who
    obtain ⟨pair, hpair, rfl⟩ := htail
    exact (hseparation pair hpair who).2.2
  have hKunique : ∀ tail ∈ K, ∀ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward tail 0 root →
        root = (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
    intro tail htail root hnash
    obtain ⟨pair, hpair, rfl⟩ := htail
    exact (hfreeze pair.1 (hfiberTube pair hpair)).2 root hnash
  obtain ⟨N, c, C, rho, hNopen, hKN, hNbounded, hc, hC, hrho,
      hrewardC, htailC, hthick, hlinear⟩ :=
    exists_bounded_open_linearAbsorptionDefect_of_compact_strictAllContinue
      reward K hKcompact hKnonempty (quittingRewardBound_nonneg reward)
        hdelta (abs_reward_le_quittingRewardBound reward) hKgap hKunique
  refine ⟨base, K, N, c, C, rho, hbase, hminimum, hpositive, rfl,
    hKcompact, hKnonempty, hNopen, hKN, hNbounded, hc, hC, hrho,
    hrewardC, htailC, hthick, hlinear, ?_⟩
  intro tail root error htail hnash herror
  apply quittingRootAbsorptionMass_tendsto_zero_of_linearDefect
    reward tail root error hc hnash
  · intro time
    exact hlinear (tail time) (htail time) (root time)
  · exact herror

end GameTheory
