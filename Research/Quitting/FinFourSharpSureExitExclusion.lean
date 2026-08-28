/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import Research.Quitting.FinFourHopfConcreteChambers
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# The sharp four-player table has no sure exit set

`GameTheory.IsQuittingSureExitSet` holds at a coalition `S` exactly when no
member of `S` gains by staying behind and no outsider gains by joining, and
`GameTheory.isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet` shows
that this is exactly when the pure profile "precisely `S` quits surely" is an
exact terminal Nash equilibrium against all behavior deviations.

For the reward table
`GameTheory.FinFourHopfConcreteChambers.sharpReward R singletonLevel` the test
fails at every one of the sixteen subsets of `Fin 4`, the empty coalition and
the grand coalition included: each coalition carries one player whose single
membership toggle strictly raises that player's own payoff.

Fifteen of the sixteen witnessing gains are rational constants, independent of
both parameters; the sixteenth, at the empty coalition, is `singletonLevel`
itself.  The exclusion therefore holds at every real `R`, with no constraint on
that parameter, and needs only a positive singleton level.  That level
hypothesis is sharp, and
`GameTheory.FinFourHopfConcreteChambers.isQuittingSureExitSet_sharpReward_empty_iff`
locates the boundary: the empty coalition is a sure exit set exactly when the
singleton level is nonpositive.
-/

noncomputable section

namespace GameTheory

namespace FinFourHopfConcreteChambers

open QuittingSureSetOwnerRepair

/-- The sixteen subsets of the four players, listed by increasing size. -/
private theorem finsetPlayer_cases (S : Finset Player) :
    S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {3} ∨
      S = {0, 1} ∨ S = {0, 2} ∨ S = {0, 3} ∨ S = {1, 2} ∨ S = {1, 3} ∨
      S = {2, 3} ∨ S = {0, 1, 2} ∨ S = {0, 1, 3} ∨ S = {0, 2, 3} ∨
      S = {1, 2, 3} ∨ S = {0, 1, 2, 3} := by
  revert S
  decide

/-- **Every coalition is toggled through.**  For each subset `S` of the four
players some single player strictly prefers the coalition obtained by flipping
its own membership in `S`: a member of `S` who prefers the exit `S ∖ {i}` it
would leave behind, or an outsider who prefers the exit `S ∪ {j}` it could
force.

The empty coalition is witnessed by player three, whose solo exit pays
`singletonLevel` against the value `0` of never absorbing; every other
coalition is witnessed by a gain that does not depend on the parameters. -/
theorem exists_strict_toggle_sharpReward (R singletonLevel : ℝ)
    (hlevel : 0 < singletonLevel) (S : Finset Player) :
    (∃ member ∈ S,
        quittingSetReward (sharpReward R singletonLevel) S member <
          quittingSetReward (sharpReward R singletonLevel)
            (S.erase member) member) ∨
      ∃ outsider ∉ S,
        quittingSetReward (sharpReward R singletonLevel) S outsider <
          quittingSetReward (sharpReward R singletonLevel)
            (insert outsider S) outsider := by
  rcases finsetPlayer_cases S with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine .inr ⟨3, by decide, ?_⟩
    rw [show insert (3 : Player) (∅ : Finset Player) = {3} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
    exact hlevel
  · refine .inr ⟨1, by decide, ?_⟩
    rw [show insert (1 : Player) ({0} : Finset Player) = {0, 1} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inr ⟨0, by decide, ?_⟩
    rw [show insert (0 : Player) ({1} : Finset Player) = {0, 1} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inr ⟨3, by decide, ?_⟩
    rw [show insert (3 : Player) ({2} : Finset Player) = {2, 3} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inr ⟨0, by decide, ?_⟩
    rw [show insert (0 : Player) ({3} : Finset Player) = {0, 3} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inr ⟨2, by decide, ?_⟩
    rw [show insert (2 : Player) ({0, 1} : Finset Player) = {0, 1, 2} from
      by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inl ⟨0, by decide, ?_⟩
    rw [show ({0, 2} : Finset Player).erase 0 = {2} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inl ⟨3, by decide, ?_⟩
    rw [show ({0, 3} : Finset Player).erase 3 = {0} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inl ⟨1, by decide, ?_⟩
    rw [show ({1, 2} : Finset Player).erase 1 = {2} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inl ⟨3, by decide, ?_⟩
    rw [show ({1, 3} : Finset Player).erase 3 = {1} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inl ⟨2, by decide, ?_⟩
    rw [show ({2, 3} : Finset Player).erase 2 = {3} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inl ⟨0, by decide, ?_⟩
    rw [show ({0, 1, 2} : Finset Player).erase 0 = {1, 2} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inl ⟨3, by decide, ?_⟩
    rw [show ({0, 1, 3} : Finset Player).erase 3 = {0, 1} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inl ⟨0, by decide, ?_⟩
    rw [show ({0, 2, 3} : Finset Player).erase 0 = {2, 3} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inl ⟨1, by decide, ?_⟩
    rw [show ({1, 2, 3} : Finset Player).erase 1 = {2, 3} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
  · refine .inl ⟨0, by decide, ?_⟩
    rw [show ({0, 1, 2, 3} : Finset Player).erase 0 = {1, 2, 3} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]

/-- **No pure coalition screen holds.**  At every positive singleton level and
every real `R`, no subset of the four players at all is a sure exit set of
`GameTheory.FinFourHopfConcreteChambers.sharpReward R singletonLevel`.  The
empty coalition and the grand coalition are included. -/
theorem not_isQuittingSureExitSet_sharpReward (R singletonLevel : ℝ)
    (hlevel : 0 < singletonLevel) (S : Finset Player) :
    ¬ IsQuittingSureExitSet (sharpReward R singletonLevel) S :=
  not_isQuittingSureExitSet_of_strict_toggle _
    (exists_strict_toggle_sharpReward R singletonLevel hlevel S)

/-- **The positive singleton level is sharp.**  At a nonpositive singleton
level the empty coalition passes the sure-exit test at every real `R`, and at a
positive one it fails.  Player three's solo exit pays the singleton level
itself, while the other three solo exits pay zero, so the all-continue test
`isQuittingSureExitSet_empty_iff` turns exactly on the sign of that level.

The hypothesis `0 < singletonLevel` of `not_isQuittingSureExitSet_sharpReward`
therefore cannot be weakened to `0 ≤ singletonLevel`. -/
theorem isQuittingSureExitSet_sharpReward_empty_iff (R singletonLevel : ℝ) :
    IsQuittingSureExitSet (sharpReward R singletonLevel) (∅ : Finset Player) ↔
      singletonLevel ≤ 0 := by
  rw [isQuittingSureExitSet_empty_iff]
  constructor
  · intro hsolo
    have hthree := hsolo 3
    norm_num +decide [quittingSoloReward, sharpReward, sharpSpectatorPassive,
      indicator] at hthree
    exact hthree
  · intro hlevel who
    fin_cases who <;>
      norm_num +decide [quittingSoloReward, sharpReward, sharpActivePassive,
        sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale,
        sharpLoss]
    exact hlevel

/-- **No pure coalition profile is a terminal equilibrium.**  For every subset
`S` of the four players the stationary pure profile at which exactly the
members of `S` quit at every live history fails to be an exact terminal Nash
equilibrium of the quitting game on
`GameTheory.FinFourHopfConcreteChambers.sharpReward R singletonLevel`.  The
deviation class is all behavior strategies. -/
theorem not_isεAsymptoticNash_pureSetRoot_sharpReward (R singletonLevel : ℝ)
    (hlevel : 0 < singletonLevel) (S : Finset Player) :
    ¬ (quittingGame (sharpReward R singletonLevel)).IsεAsymptoticNash
        (quittingTerminalPayoff (sharpReward R singletonLevel)) 0
        (quittingStationaryProfile (sharpReward R singletonLevel)
          (quittingPureSetRoot S)) := fun hnash ↦
  not_isQuittingSureExitSet_sharpReward R singletonLevel hlevel S
    ((isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
      (sharpReward R singletonLevel) S).mp hnash)

end FinFourHopfConcreteChambers

end GameTheory
