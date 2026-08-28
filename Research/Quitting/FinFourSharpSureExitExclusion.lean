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
fails at every one of the fifteen nonempty subsets of `Fin 4`, the grand
coalition included: each such coalition carries one player whose single
membership toggle strictly raises that player's own payoff, by a rational
constant independent of both parameters.  The empty coalition instead passes
exactly when the singleton level is nonpositive, its only toggle being player
three's solo exit at that level against the value `0` of never absorbing.

`GameTheory.FinFourHopfConcreteChambers.isQuittingSureExitSet_sharpReward_iff`
assembles the two halves into a classification holding at every real `R` and
every real singleton level, with no hypothesis on either: the sure exit sets
are exactly the empty coalition when that level is nonpositive, and there are
none when it is positive.
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

/-- **Every nonempty coalition is toggled through.**  For each nonempty subset
`S` of the four players some single player strictly prefers the coalition
obtained by flipping its own membership in `S`: a member of `S` who prefers the
exit `S ∖ {i}` it would leave behind, or an outsider who prefers the exit
`S ∪ {j}` it could force.

Each of the fifteen witnessing gains is a rational constant, so neither
parameter is constrained. -/
theorem exists_strict_toggle_sharpReward_of_nonempty (R singletonLevel : ℝ)
    {S : Finset Player} (hS : S.Nonempty) :
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
  · exact absurd rfl (Finset.nonempty_iff_ne_empty.mp hS)
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

/-- **No nonempty pure coalition screen holds.**  At every real `R` and every
real singleton level, no nonempty subset of the four players is a sure exit set
of `GameTheory.FinFourHopfConcreteChambers.sharpReward R singletonLevel`.  The
grand coalition is included. -/
theorem not_isQuittingSureExitSet_sharpReward_of_nonempty
    (R singletonLevel : ℝ) {S : Finset Player} (hS : S.Nonempty) :
    ¬ IsQuittingSureExitSet (sharpReward R singletonLevel) S :=
  not_isQuittingSureExitSet_of_strict_toggle _
    (exists_strict_toggle_sharpReward_of_nonempty R singletonLevel hS)

/-- **The empty coalition turns on the sign of the singleton level.**  At a
nonpositive singleton level the empty coalition passes the sure-exit test at
every real `R`, and at a positive one it fails.  Player three's solo exit pays
the singleton level itself, while the other three solo exits pay zero, so the
all-continue test `isQuittingSureExitSet_empty_iff` reads off that sign. -/
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

/-- **The sure exit sets of the sharp table, classified.**  For every real `R`
and every real singleton level, a subset of the four players is a sure exit set
of `GameTheory.FinFourHopfConcreteChambers.sharpReward R singletonLevel`
exactly when it is empty and that level is nonpositive.

So at a positive singleton level the table has no sure exit set at all, and at
a nonpositive one the empty coalition is the only one: the all-continue profile
is then the sole surviving pure coalition screen.  No hypothesis on either
parameter is imposed. -/
theorem isQuittingSureExitSet_sharpReward_iff (R singletonLevel : ℝ)
    (S : Finset Player) :
    IsQuittingSureExitSet (sharpReward R singletonLevel) S ↔
      S = ∅ ∧ singletonLevel ≤ 0 := by
  constructor
  · intro hexit
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact ⟨rfl,
        (isQuittingSureExitSet_sharpReward_empty_iff R singletonLevel).mp hexit⟩
    · exact absurd hexit
        (not_isQuittingSureExitSet_sharpReward_of_nonempty R singletonLevel hS)
  · rintro ⟨rfl, hlevel⟩
    exact (isQuittingSureExitSet_sharpReward_empty_iff R singletonLevel).mpr
      hlevel

/-- **Every coalition is toggled through at a positive singleton level.**  The
empty coalition is then witnessed by player three, whose solo exit pays the
singleton level against the value `0` of never absorbing; every nonempty
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
  rcases S.eq_empty_or_nonempty with rfl | hS
  · refine .inr ⟨3, by decide, ?_⟩
    rw [show insert (3 : Player) (∅ : Finset Player) = {3} from by decide]
    norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
      sharpActiveGain, sharpSpectatorPassive, indicator, sharpScale, sharpLoss]
    exact hlevel
  · exact exists_strict_toggle_sharpReward_of_nonempty R singletonLevel hS

/-- **No pure coalition screen holds.**  At every positive singleton level and
every real `R`, no subset of the four players at all is a sure exit set of
`GameTheory.FinFourHopfConcreteChambers.sharpReward R singletonLevel`.  The
empty coalition and the grand coalition are included. -/
theorem not_isQuittingSureExitSet_sharpReward (R singletonLevel : ℝ)
    (hlevel : 0 < singletonLevel) (S : Finset Player) :
    ¬ IsQuittingSureExitSet (sharpReward R singletonLevel) S := by
  rw [isQuittingSureExitSet_sharpReward_iff]
  rintro ⟨-, hnonpos⟩
  exact absurd hlevel (not_lt.mpr hnonpos)

/-- **No nonempty pure coalition profile is a terminal equilibrium.**  At every
real `R` and every real singleton level, and for every nonempty subset `S` of
the four players, the stationary pure profile at which exactly the members of
`S` quit at every live history fails to be an exact terminal Nash equilibrium
of the quitting game on
`GameTheory.FinFourHopfConcreteChambers.sharpReward R singletonLevel`.  The
deviation class is all behavior strategies. -/
theorem not_isεAsymptoticNash_pureSetRoot_sharpReward_of_nonempty
    (R singletonLevel : ℝ) {S : Finset Player} (hS : S.Nonempty) :
    ¬ (quittingGame (sharpReward R singletonLevel)).IsεAsymptoticNash
        (quittingTerminalPayoff (sharpReward R singletonLevel)) 0
        (quittingStationaryProfile (sharpReward R singletonLevel)
          (quittingPureSetRoot S)) := fun hnash ↦
  not_isQuittingSureExitSet_sharpReward_of_nonempty R singletonLevel hS
    ((isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
      (sharpReward R singletonLevel) S).mp hnash)

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
