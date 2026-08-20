/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ExactCycleStrata
import UniformEquilibrium.Quitting.Debt.Dynamic.DebtSourceObstructionCarrier

/-!
# Finite return words in simultaneous debt-source zero faces

This module records the game-independent data of a finite chronological word
whose exact boxed dynamic-debt edges lie in every playerwise zero-source face.
Interpreting those faces through a particular attained-zero witness belongs to
the corresponding adapter.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming.FlowCostateDuality

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A finite chronological word in the simultaneous debt-source zero face.

The source field retains literal exact boxed dynamic-debt edges.  `zeroFaces`
is the all-player exposed-face condition, not an averaged or limiting
condition.  The final two fields are exactly the absorption and punishment
gates required by the solved-cycle compiler. -/
structure QuittingDebtSourceFaceReturnWord
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (K : ℕ) where
  phase : Fin K
  state : Fin K → QuittingDebtPoint ι
  source : ∀ current,
    (state current, state (finRotate K current)) ∈
      quittingFloorDynamicDebtEdgeGraph reward
  zeroFaces : ∀ current selected,
    quittingDebtSourceObstructionFlow
          (state current, state (finRotate K current)) ∈
      exposedFace (quittingDebtSourceZeroFaceCostate selected)
        (quittingDebtSourceOneStageObstructionCarrier reward)
  absorbs :
    (∏ current : Fin K,
      quittingStationaryContinueMass
        (quittingRootOfSimplex (state current).1.2)) < 1
  punishmentAdmissible :
    IsQuittingCyclePunishmentAdmissible reward
      (fun current ↦ quittingRootOfSimplex (state current).1.2)

namespace QuittingDebtSourceFaceReturnWord

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (word : QuittingDebtSourceFaceReturnWord reward K)

/-- The literal product-root cycle carried by the return word. -/
def cycle : Fin K → ι → PMF Bool :=
  fun current ↦ quittingRootOfSimplex (word.state current).1.2

/-- The augmented-cap value cycle carried by the return word. -/
def value : Fin K → Payoff ι :=
  fun current ↦ quittingDynamicDebtCap (word.state current)

end QuittingDebtSourceFaceReturnWord

/-- Existence of one literal finite common return word in all playerwise
zero-source faces. -/
def HasQuittingDebtSourceFaceReturnWord
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ K, Nonempty (QuittingDebtSourceFaceReturnWord reward K)

end GameTheory
