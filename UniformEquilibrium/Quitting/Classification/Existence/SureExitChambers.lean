/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Pure sure-exit chambers

This file packages singleton and pair sign data that delegate to the exact
sure-exit-set characterization.  These are sufficient-data wrappers; they do
not produce a chamber from an atlas source.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Literal sign data making one sure quitter an exact pure chamber. -/
structure QuittingPureSingletonChamber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : Prop where
  owner_no_leave : 0 ≤ quittingSoloReward reward owner owner
  outsider_no_join : ∀ other, other ≠ owner →
    quittingSingletonCollisionReward reward owner other ≤
      quittingSoloReward reward owner other

namespace QuittingPureSingletonChamber

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {owner : ι}

omit [Fintype ι] [Nonempty ι] in
/-- The chamber signs are exactly the singleton sure-exit-set conditions. -/
theorem isSureExitSet (chamber : QuittingPureSingletonChamber reward owner) :
    IsQuittingSureExitSet reward ({owner} : Finset ι) :=
  (isQuittingSureExitSet_singleton_iff reward owner).mpr
    ⟨chamber.owner_no_leave, chamber.outsider_no_join⟩

omit [Nonempty ι] in
/-- The pure singleton row is exact Nash against all behavioral deviations. -/
theorem terminalNash (chamber : QuittingPureSingletonChamber reward owner) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward
        (quittingPureSetRoot ({owner} : Finset ι))) :=
  (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
    reward {owner}).mpr chamber.isSureExitSet

omit [Nonempty ι] in
/-- The singleton reward is a fixed uniform-equilibrium payoff. -/
theorem uniformEquilibriumPayoff
    (chamber : QuittingPureSingletonChamber reward owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSetReward reward ({owner} : Finset ι)) :=
  isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
    reward chamber.isSureExitSet

end QuittingPureSingletonChamber

/-- Literal sign data making two distinct sure quitters an exact pure chamber. -/
structure QuittingPurePairChamber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι) : Prop where
  distinct : first ≠ second
  first_no_leave : quittingSoloReward reward second first ≤
    quittingSingletonCollisionReward reward second first
  second_no_leave : quittingSoloReward reward first second ≤
    quittingSingletonCollisionReward reward first second
  outsider_no_join : ∀ outsider, outsider ≠ first → outsider ≠ second →
    quittingSetReward reward (insert outsider {first, second}) outsider ≤
      quittingSetReward reward {first, second} outsider

namespace QuittingPurePairChamber

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {first second : ι}

omit [Fintype ι] [Nonempty ι] in
/-- The chamber signs are exactly the pair sure-exit-set conditions. -/
theorem isSureExitSet (chamber : QuittingPurePairChamber reward first second) :
    IsQuittingSureExitSet reward ({first, second} : Finset ι) :=
  (isQuittingSureExitSet_pair_iff reward chamber.distinct).mpr
    ⟨chamber.first_no_leave, chamber.second_no_leave,
      chamber.outsider_no_join⟩

omit [Nonempty ι] in
/-- The pure pair row is exact Nash against all behavioral deviations. -/
theorem terminalNash (chamber : QuittingPurePairChamber reward first second) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward
        (quittingPureSetRoot ({first, second} : Finset ι))) :=
  (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
    reward {first, second}).mpr chamber.isSureExitSet

omit [Nonempty ι] in
/-- The pair reward is a fixed uniform-equilibrium payoff. -/
theorem uniformEquilibriumPayoff
    (chamber : QuittingPurePairChamber reward first second) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSetReward reward ({first, second} : Finset ι)) :=
  isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
    reward chamber.isSureExitSet

end QuittingPurePairChamber

end GameTheory
