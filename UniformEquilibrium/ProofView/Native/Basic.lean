/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import GameTheory.Stochastic.Basic
import MathUE.Probability.FinitePMF
import UniformEquilibrium.ProofView.Languages.MultiRound.StochasticGame

/-!
# Native GameTheory bridge for the PMF proof view

The project proof view retains Mathlib PMFs because its finite-history algebra
is expressed in those terms. On finite state spaces it compiles without loss
to the canonical finite-support stochastic game supplied by GameTheory.
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

variable {ι : Type}

/-- Compile a finite-state PMF proof-view game to GameTheory's canonical
finite-support stochastic-game carrier. The proof-only discount field is
irrelevant to finite-horizon average play and is intentionally erased. -/
@[reducible]
def toNative (G : StochasticGame ι) [Finite G.State] :
    Stochastic.Game ι where
  State := G.State
  Action := G.Act
  transition state actions :=
    _root_.Math.Probability.finDistOfPMF (G.transition state actions)
  stageUtility := G.stagePayoff

@[simp]
theorem toNative_transition_toPMF (G : StochasticGame ι) [Finite G.State]
    (state : G.State) (actions : ∀ i, G.Act i) :
    ((G.toNative.transition state actions).toPMF) = G.transition state actions :=
  rfl

@[simp]
theorem toNative_stageUtility (G : StochasticGame ι) [Finite G.State]
    (state : G.State) (actions : ∀ i, G.Act i) (who : ι) :
    G.toNative.stageUtility state actions who = G.stagePayoff state actions who :=
  rfl

end StochasticGame

namespace Stochastic.Game

variable {ι : Type}

/-- Forget finite-support witnesses and regard a native stochastic game as a
PMF proof-view game. The chosen discount is zero because the proof view's
finite-average semantics does not inspect that field. -/
@[reducible]
def toProofView (G : Stochastic.Game ι) : StochasticGame ι where
  State := G.State
  Act := G.Action
  stagePayoff := G.stageUtility
  transition state actions := (G.transition state actions).toPMF
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

@[simp]
theorem toProofView_transition (G : Stochastic.Game ι)
    (state : G.State) (actions : ∀ i, G.Action i) :
    G.toProofView.transition state actions = (G.transition state actions).toPMF :=
  rfl

@[simp]
theorem toProofView_stagePayoff (G : Stochastic.Game ι)
    (state : G.State) (actions : ∀ i, G.Action i) (who : ι) :
    G.toProofView.stagePayoff state actions who =
      G.stageUtility state actions who :=
  rfl

end Stochastic.Game

end GameTheory
