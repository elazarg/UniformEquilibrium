/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.EndpointNashClosed
import UniformEquilibrium.Quitting.Root.SimplexCoalitionMass

/-!
# Maximal-absorption exact quitting roots

At every fixed continuation cap, the compact exact root-Nash correspondence
contains a root with maximum one-stage absorption.  The canonical selector
below is cap-indexed only; no continuity of that selector is claimed.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Absorption attains a maximum on the exact cap--Nash correspondence at a
fixed continuation vector. -/
theorem exists_maximalAbsorption_isZeroQuittingRootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) :
    ∃ root : ι → PMF Bool,
      IsεQuittingRootNash reward tail 0 root ∧
      ∀ other : ι → PMF Bool,
        IsεQuittingRootNash reward tail 0 other →
          quittingRootAbsorptionMass other ≤
            quittingRootAbsorptionMass root := by
  let roots : Set (QuittingRootSimplex ι) :=
    {root | IsεQuittingRootEndpointNash reward tail 0
      (quittingRootOfSimplex root)}
  have hcompact : IsCompact roots := by
    simpa only [roots] using
      isCompact_setOf_isZeroQuittingRootEndpointNash_root reward tail
  have hnonempty : roots.Nonempty := by
    obtain ⟨root, hroot⟩ :=
      exists_isZeroQuittingRootEndpointNash_simplex reward tail
    exact ⟨root, hroot⟩
  obtain ⟨chosen, hchosen, hmax⟩ := hcompact.exists_isMaxOn hnonempty
    continuous_quittingSimplexAbsorptionMass.continuousOn
  let root := quittingRootOfSimplex chosen
  have hnash : IsεQuittingRootNash reward tail 0 root :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward tail 0 root).1 hchosen
  refine ⟨root, hnash, ?_⟩
  intro other hother
  let otherSimplex : QuittingRootSimplex ι :=
    fun who ↦ stdSimplexEquiv (other who)
  have hotherRoot : quittingRootOfSimplex otherSimplex = other := by
    funext who
    exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (other who)
  have hotherEndpoint : IsεQuittingRootEndpointNash reward tail 0
      (quittingRootOfSimplex otherSimplex) := by
    rw [hotherRoot]
    exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward tail 0 other).2 hother
  rw [isMaxOn_iff] at hmax
  have hmaximal := hmax otherSimplex hotherEndpoint
  rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass,
    quittingSimplexAbsorptionMass_eq_rootAbsorptionMass] at hmaximal
  simpa only [root, hotherRoot] using hmaximal

/-- A canonical maximal-absorption exact root indexed only by its continuation
cap. -/
noncomputable def quittingMaximalAbsorptionCapRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) : ι → PMF Bool :=
  Classical.choose (exists_maximalAbsorption_isZeroQuittingRootNash reward cap)

theorem quittingMaximalAbsorptionCapRoot_exactNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) :
    IsεQuittingRootNash reward cap 0
      (quittingMaximalAbsorptionCapRoot reward cap) :=
  (Classical.choose_spec
    (exists_maximalAbsorption_isZeroQuittingRootNash reward cap)).1

theorem quittingMaximalAbsorptionCapRoot_maximal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (other : ι → PMF Bool)
    (hother : IsεQuittingRootNash reward cap 0 other) :
    quittingRootAbsorptionMass other ≤
      quittingRootAbsorptionMass
        (quittingMaximalAbsorptionCapRoot reward cap) :=
  (Classical.choose_spec
    (exists_maximalAbsorption_isZeroQuittingRootNash reward cap)).2 other hother

theorem quittingMaximalAbsorptionCapRoot_eq_of_cap_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {cap cap' : Payoff ι} (hcap : cap = cap') :
    quittingMaximalAbsorptionCapRoot reward cap =
      quittingMaximalAbsorptionCapRoot reward cap' := by
  rw [hcap]

end GameTheory
