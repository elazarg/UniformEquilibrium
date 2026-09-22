import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPairedFamily

/-!
# Completing arbitrary data into the paired capped-clock family

An arbitrary four-player reward table supplies all nonsingleton coordinates
of players `0`, `1`, and `2`.  This module preserves those thirty-three
coordinates, replaces the singleton rows by the fixed paired rows, and fills
the remaining eleven nonsingleton coordinates of player `3` so that the
paired-family future and join inequalities hold.

The construction is entirely at the raw reward-table level.  Its uniform-
equilibrium payoff follows from the paired-family consumer; no profile,
equilibrium, absorption schedule, or target is an input.
-/

noncomputable section

namespace GameTheory

open StochasticGame

namespace CappedClockPairedCompletion

abbrev Player := Fin 4

abbrev RewardTable :=
  {S : Finset Player // S.Nonempty} → Payoff Player

/-- Player `2`'s completed value on a child coalition.  Singleton rows use
the fixed paired data; nonsingleton rows retain the source coordinate. -/
private def childTwoValue (source : RewardTable)
    (quitters : {S : Finset Player // S.Nonempty}) : ℝ :=
  if quitters.1.card = 1 then
    SolanVieilleBoundary.boundaryReward quitters 2
  else source quitters 2

/-- Player `3`'s completed value on a coalition not containing player `3`.
The nonsingleton branch makes the future row tight. -/
private def ownerBaseValue (source : RewardTable)
    (quitters : {S : Finset Player // S.Nonempty}) : ℝ :=
  if quitters.1.card = 1 then
    SolanVieilleBoundary.boundaryReward quitters 3
  else 2 * source quitters 2 - 1

/-- Complete an arbitrary raw table into the paired capped-clock family.

Singleton rows are the literal boundary-table rows.  On nonsingletons every
coordinate except player `3` is preserved.  Player `3`'s child-coalition rows
make the future inequality tight, and its joining rows make the corresponding
join inequality tight. -/
def completedReward (source : RewardTable) : RewardTable :=
  fun quitters who =>
    if quitters.1.card = 1 then
      SolanVieilleBoundary.boundaryReward quitters who
    else if who ≠ 3 then
      source quitters who
    else if 3 ∉ quitters.1 then
      2 * source quitters 2 - 1
    else
      let childCoalition := quitters.1.erase 3
      if hchild : childCoalition.Nonempty then
        ownerBaseValue source ⟨childCoalition, hchild⟩ +
          2 * (childTwoValue source
              ⟨insert 2 childCoalition, Finset.insert_nonempty 2 childCoalition⟩ -
            childTwoValue source ⟨childCoalition, hchild⟩)
      else 0

/-- The completion has exactly the fixed paired singleton rows. -/
@[simp] theorem completedReward_singleton (source : RewardTable) (owner : Player) :
    completedReward source (quittingSingletonTerminal owner) =
      SolanVieilleBoundary.boundaryReward (quittingSingletonTerminal owner) := by
  funext who
  simp [completedReward, quittingSingletonTerminal]

/-- Every nonsingleton coordinate belonging to players `0`, `1`, or `2` is
preserved literally from the supplied source table. -/
theorem completedReward_eq_source_of_two_le_card_of_ne_three
    (source : RewardTable) (quitters : {S : Finset Player // S.Nonempty})
    (hcard : 2 ≤ quitters.1.card) {who : Player} (hwho : who ≠ 3) :
    completedReward source quitters who = source quitters who := by
  have hne : quitters.1.card ≠ 1 := by omega
  simp [completedReward, hne, hwho]

/-- Every completed table satisfies the paired-family raw inequalities. -/
theorem completedReward_conditions (source : RewardTable) :
    CappedClockPairedFamily.Conditions (completedReward source) := by
  refine ⟨?_, ?_, ?_⟩
  · intro owner who
    fin_cases owner <;> fin_cases who <;> rfl
  · intro A
    fin_cases A <;>
      norm_num [completedReward, childTwoValue, ownerBaseValue,
        CappedClockPairedFamily.childTwo,
        SolanVieilleBoundary.boundaryReward] <;>
      ring_nf <;> norm_num
  · intro A
    fin_cases A <;>
      norm_num [completedReward, childTwoValue, ownerBaseValue,
        CappedClockPairedFamily.childTwo]

/-- Every table produced by `completedReward` has a uniform-equilibrium
payoff. -/
theorem completedReward_exists_uniformEquilibriumPayoff (source : RewardTable) :
    ∃ payoff : Payoff Player,
      (quittingGame (completedReward source)).IsUniformEquilibriumPayoff none payoff :=
  CappedClockPairedFamily.exists_uniformEquilibriumPayoff
    (completedReward_conditions source)

end CappedClockPairedCompletion

end GameTheory
