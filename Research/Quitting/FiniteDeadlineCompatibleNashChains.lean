/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.Topology.CompactDependentFinitePrefixRelation
import Research.Quitting.FiniteDeadlineProjectiveCompatibility

/-!
# Finite compatible timing-Nash chains

Separate Nash existence at every deadline does not provide an inverse
system.  The finite datum required by compactness is stronger: for every
depth, all Nash and adjacent censor equations through that depth must hold
simultaneously.

This module names that exact producer contract.  The compact dependent-prefix
theorem is the generic existence mechanism; the remaining game-specific
adapter must represent finite timing laws in their compact simplex fibers and
prove that the Nash-and-censor graphs are closed.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One simultaneously compatible chain of exact timing Nash laws from
deadline zero through `horizon`. -/
structure QuittingFiniteDeadlineCompatibleNashChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (horizon : ℕ) where
  mixed : ∀ time : Fin (horizon + 1),
    ι → PMF (QuittingFiniteDeadlineTimingAction time)
  isNash : ∀ time : Fin (horizon + 1),
    (quittingFiniteDeadlineTimingGame reward time).mixedExtension.IsNash
      (mixed time)
  censor_succ : ∀ time : Fin horizon,
    quittingFiniteDeadlineTimingProfileCensor
        (mixed ⟨(time : ℕ) + 1, Nat.succ_lt_succ time.isLt⟩) =
      mixed ⟨time, lt_trans time.isLt (Nat.lt_succ_self horizon)⟩

/-- Exact finite-intersection producer datum for projective timing Nash laws. -/
def HasFiniteCompatibleQuittingTimingNashChains
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ horizon, Nonempty (QuittingFiniteDeadlineCompatibleNashChain
    reward horizon)

/-- The strictly weaker datum supplied by ordinary finite-game Nash
existence: each deadline has some Nash law, with no adjacent compatibility. -/
def HasDeadlinewiseQuittingTimingNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ deadline,
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash
        mixed

/-- Ordinary finite-game Nash existence supplies the pointwise datum at every
deadline.  It supplies no censor equations between the independently chosen
laws. -/
theorem hasDeadlinewiseQuittingTimingNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasDeadlinewiseQuittingTimingNash reward := by
  intro deadline
  let game := quittingFiniteDeadlineTimingGame reward deadline
  letI (who : ι) : Finite (game.Strategy who) := by
    dsimp only [game, quittingFiniteDeadlineTimingGame, KernelGame.ofPureEU]
    infer_instance
  letI (who : ι) : Nonempty (game.Strategy who) := by
    dsimp only [game, quittingFiniteDeadlineTimingGame, KernelGame.ofPureEU]
    infer_instance
  letI : Finite game.Outcome := by
    dsimp only [game, quittingFiniteDeadlineTimingGame, KernelGame.ofPureEU]
    infer_instance
  exact game.mixed_nash_exists

/-- Simultaneously compatible finite chains in particular give ordinary
deadlinewise Nash existence.  The converse is deliberately not asserted. -/
theorem hasDeadlinewiseQuittingTimingNash_of_finiteCompatibleChains
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (chains : HasFiniteCompatibleQuittingTimingNashChains reward) :
    HasDeadlinewiseQuittingTimingNash reward := by
  intro deadline
  obtain ⟨chain⟩ := chains deadline
  let terminal : Fin (deadline + 1) :=
    ⟨deadline, Nat.lt_succ_self deadline⟩
  exact ⟨chain.mixed terminal, chain.isNash terminal⟩

/-- The exact remaining compactness adapter.  Its premise is finite-chain
realizability, not independent deadlinewise Nash existence. -/
def FiniteCompatibleChainsProduceProjectiveNashFamily : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι),
    HasFiniteCompatibleQuittingTimingNashChains reward →
      Nonempty (QuittingFiniteDeadlineCompatibleNashFamily reward)

end GameTheory
