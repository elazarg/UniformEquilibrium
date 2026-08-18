/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.CounterexampleNecessary

/-!
# Stationary existence on the whole non-Q side of the α-player gate

Solan and Solan, *Quitting games and linear complementarity problems*,
Math. Oper. Res. **45**(2) (2020), Section 5.1, describe three situations in
which a finite quitting game has a stationary `ε`-equilibrium for every
`ε > 0`: there are no α-players; the homogeneous problem on the α-player
matrix has a nontrivial solution; or that matrix is not a Q-matrix, which is
their Theorem 5.1(1).  Only the last is stated as a theorem there, and its
proof is given by analogy with their Theorem 2.13.

Those three situations are exactly the first three regimes of
`faithful_q_nonQ_lcp_matrix_gate`.  This file collects the three producers,
each already proved at stationary strength in its own module, into the single
statement they add up to: outside the nonhomogeneous standard-Q side there is
always a payoff vector approached by stationary `ε`-equilibria.

Two strengthenings over the source are kept throughout.

* The deviation class is all behavior strategies of the quitting game, not
  only stationary ones, and the payoff functional is the terminal absorption
  payoff `GameTheory.quittingTerminalPayoff`.
* One limit payoff is pinned, so each producer also exhibits a uniform
  equilibrium payoff.  The source's conclusion is recovered by
  `IsQuittingStationaryUniformEquilibriumPayoff.hasApproximateEquilibria`.

Nothing here decides the remaining nonhomogeneous standard-Q side, where the
source produces only a sunspot `ε`-equilibrium.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Stationary existence off the standard-Q side.**  Every finite quitting
reward table either admits a payoff vector approached by stationary
`ε`-equilibria, or has a nonempty α-player core whose restricted matrix is
nonhomogeneous and textbook standard Q.

The three producing regimes are the empty α-player core, the homogeneous
branch, and the ordinary non-Q branch of Solan and Solan, *Quitting games and
linear complementarity problems*, Math. Oper. Res. **45**(2) (2020),
Theorem 5.1(1). -/
theorem exists_stationaryUniformEquilibriumPayoff_or_standardQMatrixSide
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ value : Payoff ι,
        IsQuittingStationaryUniformEquilibriumPayoff reward value) ∨
      StandardQMatrixSide reward := by
  rcases faithful_q_nonQ_lcp_matrix_gate reward with
    habnormal | hhomogeneous | hnonQ | hqbar | hresidual
  · exact Or.inl
      (exists_stationaryUniformEquilibriumPayoff_of_allPlayersAbnormal
        reward habnormal)
  · exact Or.inl
      (exists_stationaryUniformEquilibriumPayoff_of_homogeneousMatrixBranch
        reward hhomogeneous)
  · exact Or.inl
      (exists_stationaryUniformEquilibriumPayoff_of_ordinaryNonQMatrixBranch
        reward hnonQ)
  · exact Or.inr hqbar.toStandardQMatrixSide
  · exact Or.inr hresidual.toStandardQMatrixSide

/-- The literal Section 5.1 conclusion off the standard-Q side: a stationary
`ε`-equilibrium at every positive accuracy. -/
theorem hasQuittingStationaryApproximateEquilibria_or_standardQMatrixSide
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasQuittingStationaryApproximateEquilibria reward ∨
      StandardQMatrixSide reward := by
  rcases exists_stationaryUniformEquilibriumPayoff_or_standardQMatrixSide
      reward with ⟨_, hvalue⟩ | hstandard
  · exact Or.inl hvalue.hasApproximateEquilibria
  · exact Or.inr hstandard

/-- **Sharp stationary restriction.**  A quitting game with no stationary
`ε`-equilibrium at some positive accuracy has a nonempty α-player core, no
nontrivial homogeneous solution on the restricted matrix, and a textbook
standard-Q restricted matrix.

This is strictly sharper than
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`: it reaches the
same algebraic conclusion from failure of the weaker stationary conclusion. -/
theorem standardQMatrixSide_of_not_hasStationaryApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬HasQuittingStationaryApproximateEquilibria reward) :
    StandardQMatrixSide reward := by
  rcases hasQuittingStationaryApproximateEquilibria_or_standardQMatrixSide
      reward with hstationary | hstandard
  · exact absurd hstationary hnot
  · exact hstandard

/-- Every stationary producer of this folder also exhibits a uniform
equilibrium payoff, so the stationary gate refines the uniform-payoff gate. -/
theorem exists_uniformEquilibriumPayoff_or_standardQMatrixSide
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      StandardQMatrixSide reward := by
  rcases exists_stationaryUniformEquilibriumPayoff_or_standardQMatrixSide
      reward with ⟨_, hvalue⟩ | hstandard
  · exact Or.inl (exists_uniformEquilibriumPayoff_of_stationaryFamily hvalue)
  · exact Or.inr hstandard

end QuittingLCPClassification
end GameTheory
