/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportHardNashBellmanSpine
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumFiberIsolation
import UniformEquilibrium.Quitting.Bellman.Finite.AllContinueBasinRestartMoat

/-!
# Restart moats at the Fin4 terminal-semantic minimum fibre

If a four-player quitting game has no uniform-equilibrium payoff, its compact
terminal-semantic minimum fibre lies inside one open unique-all-Continue basin.
This supplies a uniform terminal-seam moat for every positively absorbing exact
block starting at an actual minimum-fibre value.

For a supplied canonical exact Nash--Bellman spine, the no-uniform-payoff
residual compiler also proves summability of every marginal Quit hazard. The
generic restart-moat alternative therefore gives a convergent spine which is
either the constant all-Continue spine or has a limit uniformly separated from
every actual minimum-fibre value.

The result consumes a supplied exact spine. It does not construct such a spine,
rule out either alternative, or prove a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology BigOperators

open QuittingFiniteExactNashBellmanBlock

/-- Literal Fin4 source adapter for actual minimum-fibre anchors: no uniform
payoff supplies one uniform endpoint-seam floor for every positively absorbing
exact block whose restart anchor is the value of a minimum-fibre point. -/
theorem exists_finFour_minimumFiber_uniformRestartMoat_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (base : QuittingTerminalSemanticPair (Fin 4))
        (tube : Set (Payoff (Fin 4))) (rho : ℝ),
      base ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum base ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalSemanticDebtSum base ∧
      IsOpen tube ∧
      (∀ pair ∈ quittingTerminalSemanticMinimumFiber reward base,
        pair.1 ∈ tube) ∧
      0 < rho ∧
      ∀ (carrier : Set (QuittingNashBellmanPoint (Fin 4)))
          (pair : QuittingTerminalSemanticPair (Fin 4)),
        pair ∈ quittingTerminalSemanticMinimumFiber reward base →
        ∀ block : QuittingFiniteExactNashBellmanBlock reward carrier,
          ∀ stage, stage < block.horizon →
            0 < quittingRootAbsorptionMass (block.root stage) →
              rho ≤ dist (block.state block.horizon).1 pair.1 := by
  obtain ⟨base, _delta, _epsilon, tube, hbase, hminimum, hpositive,
      _hdelta, _hepsilon, htubeOpen, _hgap, hfiberTube, hfreeze, _hnear⟩ :=
    exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff
      reward hno
  let plateau : Set (Payoff (Fin 4)) :=
    Prod.fst '' quittingTerminalSemanticMinimumFiber reward base
  have hcompact : IsCompact plateau :=
    (quittingTerminalSemanticMinimumFiber_isCompact reward base).image
      continuous_fst
  have hsubset : plateau ⊆ tube := by
    rintro anchor ⟨pair, hpair, rfl⟩
    exact hfiberTube pair hpair
  have huniqueEndpoint : ∀ tail ∈ tube, ∀ root : Fin 4 → PMF Bool,
      IsεQuittingRootEndpointNash reward tail 0 root →
        root = (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
    intro tail htail root hnash
    exact (hfreeze tail htail).2 root
      ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward tail root).1 hnash)
  obtain ⟨rho, hrho, hseparation⟩ :=
    exists_uniform_terminal_separation_of_positiveAbsorption
      plateau tube hcompact htubeOpen hsubset huniqueEndpoint
  refine ⟨base, tube, rho, hbase, hminimum, hpositive, htubeOpen,
    hfiberTube, hrho, ?_⟩
  intro carrier pair hpair block stage hstage habsorption
  exact hseparation carrier pair.1 ⟨pair, hpair, rfl⟩
    block stage hstage habsorption

/-- Conditional Fin4 limit alternative for a supplied canonical exact spine
and explicitly supplied summability of every marginal Quit hazard. The
separated branch is uniform over every actual minimum-fibre value. -/
theorem finFour_noUniformPayoff_constantAllContinue_or_limit_uniformlySeparated_of_summable
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (value : ℕ → Payoff (Fin 4)) (roots : ℕ → Fin 4 → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (hsummable : ∀ player,
      Summable (fun time ↦ (roots time player true).toReal)) :
    ∃ (base : QuittingTerminalSemanticPair (Fin 4))
        (tube : Set (Payoff (Fin 4))) (rho : ℝ) (limit : Payoff (Fin 4)),
      base ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum base ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalSemanticDebtSum base ∧
      IsOpen tube ∧
      (∀ pair ∈ quittingTerminalSemanticMinimumFiber reward base,
        pair.1 ∈ tube) ∧
      0 < rho ∧ Tendsto value atTop (nhds limit) ∧
      ((∀ time, value time = limit ∧
          roots time = (quittingAllContinueRoot : Fin 4 → PMF Bool)) ∨
        (limit ∉ tube ∧
          ∀ pair ∈ quittingTerminalSemanticMinimumFiber reward base,
            rho ≤ dist limit pair.1)) := by
  obtain ⟨base, _delta, _epsilon, tube, hbase, hminimum, hpositive,
      _hdelta, _hepsilon, htubeOpen, _hgap, hfiberTube, hfreeze, _hnear⟩ :=
    exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff
      reward hno
  let plateau : Set (Payoff (Fin 4)) :=
    Prod.fst '' quittingTerminalSemanticMinimumFiber reward base
  have hcompact : IsCompact plateau :=
    (quittingTerminalSemanticMinimumFiber_isCompact reward base).image
      continuous_fst
  have hsubset : plateau ⊆ tube := by
    rintro anchor ⟨pair, hpair, rfl⟩
    exact hfiberTube pair hpair
  have hunique : ∀ tail ∈ tube, ∀ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward tail 0 root →
        root = (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
    intro tail htail root hnash
    exact (hfreeze tail htail).2 root hnash
  obtain ⟨rho, limit, hrho, hlimit, hbranch⟩ :=
    hspine.eq_constantAllContinue_or_limit_uniformlySeparated
      plateau tube hcompact htubeOpen hsubset hunique hsummable
  refine ⟨base, tube, rho, limit, hbase, hminimum, hpositive,
    htubeOpen, hfiberTube, hrho, hlimit, ?_⟩
  rcases hbranch with hconstant | ⟨houtside, hseparation⟩
  · exact Or.inl hconstant
  · exact Or.inr ⟨houtside, fun pair hpair ↦
      hseparation pair.1 ⟨pair, hpair, rfl⟩⟩
/-- Direct Fin4 no-uniform-payoff limit alternative for a supplied canonical
exact spine. The no-uniform-payoff hypothesis supplies summability of every
marginal Quit hazard. The separated branch is uniform over every actual
minimum-fibre value. -/
theorem finFour_noUniformPayoff_constantAllContinue_or_limit_uniformlySeparated
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (value : ℕ → Payoff (Fin 4)) (roots : ℕ → Fin 4 → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots) :
    ∃ (base : QuittingTerminalSemanticPair (Fin 4))
        (tube : Set (Payoff (Fin 4))) (rho : ℝ) (limit : Payoff (Fin 4)),
      base ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum base ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalSemanticDebtSum base ∧
      IsOpen tube ∧
      (∀ pair ∈ quittingTerminalSemanticMinimumFiber reward base,
        pair.1 ∈ tube) ∧
      0 < rho ∧ Tendsto value atTop (nhds limit) ∧
      ((∀ time, value time = limit ∧
          roots time = (quittingAllContinueRoot : Fin 4 → PMF Bool)) ∨
        (limit ∉ tube ∧
          ∀ pair ∈ quittingTerminalSemanticMinimumFiber reward base,
            rho ≤ dist limit pair.1)) := by
  apply finFour_noUniformPayoff_constantAllContinue_or_limit_uniformlySeparated_of_summable
    reward hno value roots hspine
  intro player
  change Summable (quittingMarginalQuitHazard roots player)
  exact all_marginalQuitHazards_summable_of_no_uniformPayoff reward
    (bound := quittingRewardBound reward)
    (abs_reward_le_quittingRewardBound reward) hno value roots hspine player

end GameTheory
