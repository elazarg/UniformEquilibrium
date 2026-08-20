/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.SpecialCases.SingleController.NoTrapPerturbation

/-!
# No-trap extraction for the Vrieze single-controller LP

This file closes the game-specific policy-improvement part of the
single-controller residual.

For a strongly complementary Vrieze primal--dual pair, let `R` be the states
with positive total dual occupation mass.  If a state could not reach `R`
through any pure controller-action support edge, the set of all such states
would be closed under every positive controller transition.  Its dual
occupation rows vanish by nonnegativity.

`NoTrapPerturbation` converts exactly those two facts into a strictly better
feasible Vrieze primal point: strong complementarity supplies a finite common
bias-slack margin, while the game-independent closed-region lemma in
`MathUE.LinearProgramming.ClosedTrapPerturbation` preserves the gain and bias
rows under an indicator bump.  Re-encoding lowers the minimization objective,
contradicting the generic zero-gap optimality interface.

The conclusion is support-graph reachability to `R`.  It does not yet turn a
completed policy into a mean-ergodic transience/projection statement; that is
the next, genuinely probabilistic, step.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {G : StochasticGame Bool} [Finite G.State]
  [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]

/-- A strongly complementary Vrieze pair has no controller-support trap
outside its positive dual-occupation support. -/
theorem all_canReach_vriezeOccupationSupport_of_strongComplementary
    {controller : Bool} (hSC : G.IsSingleController controller)
    {q : VriezeCol G controller → ℝ}
    {w : VriezeRow G controller → ℝ}
    (hstrong : Math.LinearProgramming.IsStrongComplementaryPair
      (G.vriezeA controller) (G.vriezeB controller)
        (G.vriezeC controller) q w) :
    ∀ source : G.State,
      FiniteReachability.CanReachSet (G.controllerSucc controller)
        (G.vriezeOccupationSupport controller
          (G.vriezeDualZ controller w)) source := by
  classical
  let R : G.State → Prop :=
    G.vriezeOccupationSupport controller (G.vriezeDualZ controller w)
  let Succ : G.State → G.State → Prop := G.controllerSucc controller
  let bad : G.State → Prop := fun state ↦
    ¬ FiniteReachability.CanReachSet Succ R state
  by_contra hall
  push Not at hall
  obtain ⟨badState, hbadState⟩ := hall
  change bad badState at hbadState
  have hbad_not_R : ∀ {state : G.State}, bad state → ¬ R state := by
    intro state hbad hR
    exact hbad ⟨state, hR, Relation.ReflTransGen.refl⟩
  have hbad_closed : ∀ {source destination : G.State},
      bad source → Succ source destination → bad destination := by
    intro source destination hsource hstep
    exact (FiniteReachability.trap_closed_of_not_canReachSet
      Succ R (hbad_not_R hsource) hsource hstep).2
  have hkernel_pure : ∀ (source : G.State) (action : G.Act controller),
      G.controllerKernel controller (fun _ ↦ PMF.pure action) source =
        G.transition source
          (G.jointOfControllerAct controller action) := by
    intro source action
    rw [G.controllerKernel_eq_bind hSC
      (fun _ ↦ PMF.pure action) source
      (G.jointOfControllerAct controller action), PMF.pure_bind]
    congr 1
    have hupdate := Function.update_eq_self controller
      (G.jointOfControllerAct controller action)
    rwa [G.jointOfControllerAct_apply_self] at hupdate
  have hbad_of_transProb_pos : ∀ {source destination : G.State}
      (action : G.Act controller), bad source →
      0 < G.transProb controller source action destination →
      bad destination := by
    intro source destination action hsource hpositive
    apply hbad_closed hsource
    refine ⟨action, ?_⟩
    rw [PMF.mem_support_iff, hkernel_pure source action]
    intro hzero
    simp [transProb, hzero] at hpositive
  have hdualZ_zero_of_bad : ∀ state, bad state → ∀ action,
      G.vriezeDualZ controller w state action = 0 := by
    intro state hstate action
    have hmass_nonpos :
        (∑ candidate, G.vriezeDualZ controller w state candidate) ≤ 0 :=
      le_of_not_gt (hbad_not_R hstate)
    have hnonneg : ∀ candidate : G.Act controller,
        0 ≤ G.vriezeDualZ controller w state candidate := fun candidate ↦
      hstrong.2.1.1 (Sum.inr (Sum.inl (state, candidate)))
    apply le_antisymm
    · exact (Finset.single_le_sum
        (fun candidate _ ↦ hnonneg candidate)
        (Finset.mem_univ action)).trans hmass_nonpos
    · exact hnonneg action
  obtain ⟨candidate, hcandidate, himproves⟩ :=
    G.exists_vriezePrimalFeasible_strictImprovement_of_closedZeroOccupation
      hstrong bad ⟨badState, hbadState⟩ hbad_of_transProb_pos
        hdualZ_zero_of_bad
  exact (not_lt_of_ge
    (hstrong.minPrimalValue_le_of_feasible hcandidate)) himproves

/-- Primal optimality therefore supplies a strongly complementary pair whose
positive occupation support is reachable from every state. -/
theorem exists_vriezeStrongComplementaryPair_noTrap
    [Nonempty G.State] {controller : Bool}
    (hSC : G.IsSingleController controller)
    {x : G.State → PMF (G.Act (!controller))} {g v : G.State → ℝ}
    (hopt : G.IsVriezePrimalOptimal controller x g v) :
    ∃ (q : VriezeCol G controller → ℝ)
        (w : VriezeRow G controller → ℝ),
      Math.LinearProgramming.IsStrongComplementaryPair
          (G.vriezeA controller) (G.vriezeB controller)
            (G.vriezeC controller) q w ∧
        ∀ source : G.State,
          FiniteReachability.CanReachSet (G.controllerSucc controller)
            (G.vriezeOccupationSupport controller
              (G.vriezeDualZ controller w)) source := by
  obtain ⟨q, w, hstrong⟩ :=
    G.exists_vriezeStrongComplementaryPair_of_vriezePrimalOptimal hSC hopt
  exact ⟨q, w, hstrong,
    G.all_canReach_vriezeOccupationSupport_of_strongComplementary
      hSC hstrong⟩

end StochasticGame
end GameTheory
