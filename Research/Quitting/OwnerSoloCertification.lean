/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification

/-!
# Owner-solo certification research residuals

The canonical owner-solo certification, terminal delivery, rate dichotomy,
and positive-debt refinement live in
`UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification`.  This file
keeps only the two Research conclusions that assemble that canonical API into
the ownerwise and stagewise transfer statements used by the research lane.
-/

noncomputable section

namespace GameTheory
namespace OwnerSoloCertificationResearch

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Ownerwise assembly and the stagewise transfer kernel -/

/-- Ownerwise assembly (SR2).  With finitely many players, either some
player's solo payoff vector is a uniform-equilibrium payoff, or every
player carrying positive exact dynamic debt at any live date of any
admissible zero-boundary chain has the universal joining obstruction at
every rate. -/
theorem exists_soloUniformPayoff_or_forall_positiveDebt_owners_obstructed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ owner, (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner)) ∨
    ∀ (owner : ι) (cutoff : ℕ)
      (path : QuittingFiniteNashBellmanPath ι cutoff),
      path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff →
      ∀ start, start ≤ cutoff →
        0 < quittingFiniteNashBellmanPathDynamicDebt reward cutoff path
          owner start →
        ∀ p : ℝ, 0 < p → p ≤ 1 →
          QuittingSoloJoiningObstruction reward owner p := by
  by_cases hexists : ∃ owner,
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingSoloReward reward owner)
  · exact Or.inl hexists
  · right
    intro owner cutoff path hpath start hstart hdebt
    rcases uniformPayoff_or_universalJoining_of_positiveDebt reward cutoff
      path hpath owner start hstart hdebt with hpayoff | hobstruction
    · exact absurd ⟨owner, hpayoff⟩ hexists
    · exact hobstruction

omit [Fintype ι] in
/-- Stagewise transfer kernel (SR3a).  Under the universal constant-rate
joining obstruction, every hazard sequence has, at each stage with positive
hazard, a strict stagewise joiner.  The obstruction is therefore not
specific to constant rates. -/
theorem stagewise_obstruction_of_universalJoining
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hobstruction : ∀ p : ℝ, 0 < p → p ≤ 1 →
      QuittingSoloJoiningObstruction reward owner p)
    (hazardSeq : ℕ → ℝ) (hrange : ∀ t, 0 ≤ hazardSeq t ∧ hazardSeq t ≤ 1)
    (time : ℕ) (hlive : 0 < hazardSeq time) :
    ∃ other, other ≠ owner ∧
      quittingSoloReward reward owner other <
        (1 - hazardSeq time) * quittingSoloReward reward other other +
          hazardSeq time *
            quittingSingletonCollisionReward reward owner other :=
  hobstruction (hazardSeq time) hlive (hrange time).2

end OwnerSoloCertificationResearch
end GameTheory
