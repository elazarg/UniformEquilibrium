/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import Research.Quitting.FinFourSharpSureExitExclusion
import Research.Quitting.HopfCompletionSafeChambers

/-!
# The sharp table's induced owner margin at the persistent base `{2}`

Take the persistent base `{2}` of
`GameTheory.FinFourHopfConcreteChambers.sharpReward R singletonLevel`, with
player three the single free player and players zero and one fixed on Continue.
The induced binary game has one free coordinate, in which quitting beats
continuing by exactly `1` — the spectator's reward rises from `singletonLevel`
at the terminal `{2}` to `singletonLevel + 1` at `{2, 3}` — so every point of
`GameTheory.quittingPersistentBaseNashSet` puts the free player on Quit.

Against that row the owner's own `GameTheory.quittingInducedOwnerNeverExcess`
is `39 / 100`, positive and so the wrong sign for
`GameTheory.QuittingInducedOwnerNeverChamber`: owner two strictly prefers
Continue and is unsafe as a persistent base. The value is the same at every
point of the induced Nash carrier and at every real `R` and singleton level,
because both rewards it is built from, `r₂({3}) = 0` and
`r₂({2, 3}) = -39/100`, are rational constants.

Owner two is the owner that *is* safe for the two older completions, by
`GameTheory.FinFourMaximalRayZeroMinimumRegressions.rationalPureSingletonChamber`
and
`GameTheory.FinFourMaximalRayZeroMinimumRegressions.fullBindingPureSingletonChamber`.
For the sharp table it is a chamber at no parameter at all.

## The compact alternative is silent here

`GameTheory.exists_uniformPayoff_or_singletonBase_pos_gap` offers a
uniform-equilibrium payoff or a positive gap on the induced Nash carrier. For
this table its left branch holds outright:
`GameTheory.FinFourHopfConcreteChambers.sharpReward_exists_uniformEquilibriumPayoff`
supplies the payoff for every `R` in `[0, 1/37]`. A disjunction satisfied on the
left constrains nothing on the right, so the margin below cannot be read off
that alternative and is computed directly instead. Proving the equilibrium is
what deactivated the screen.
-/

noncomputable section

namespace GameTheory

namespace FinFourHopfConcreteChambers

open QuittingSureSetOwnerRepair

/-- The induced persistent base carrying the owner margin: player two quits
surely, player three is free, players zero and one continue surely. -/
def sharpInducedBaseRoot
    (point : mixedPolytope (quittingBinaryForm ({3} : Finset Player)).sig) :
    Player → PMF Bool :=
  quittingPersistentBaseRoot ({2} : Finset Player) {3} point

/-- Off the free coordinate the induced base row is the pure exit of `{2}`. -/
theorem sharpInducedBaseRoot_eq_pureSetRoot_of_ne
    (point : mixedPolytope (quittingBinaryForm ({3} : Finset Player)).sig)
    {who : Player} (hwho : who ≠ 3) :
    sharpInducedBaseRoot point who =
      quittingPureSetRoot ({2} : Finset Player) who := by
  unfold sharpInducedBaseRoot
  by_cases htwo : who = 2
  · subst who
    rw [quittingPersistentBaseRoot_apply_of_mem_base _ _ _ (by simp)]
    simp [quittingPureSetRoot, quittingSetAction]
  · rw [quittingPersistentBaseRoot_apply_of_outside _ _ _
      (by simp [htwo, hwho])]
    simp [quittingPureSetRoot, quittingSetAction, htwo]

/-- Replacing one coordinate erases every difference outside it. -/
theorem update_eq_update_of_forall_ne
    {root other : Player → PMF Bool} {who : Player}
    (hagree : ∀ player, player ≠ who → root player = other player)
    (law : PMF Bool) :
    Function.update root who law = Function.update other who law := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp
  · rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
    exact hagree player hplayer

/-! ## The free coordinate is pure Quit -/

/-- The free player's pure Quit endpoint at the induced base row is the
spectator's reward at the terminal `{2, 3}`. -/
theorem quittingRootQuitPayoff_sharpInducedBaseRoot_three
    (R singletonLevel : ℝ)
    (point : mixedPolytope (quittingBinaryForm ({3} : Finset Player)).sig) :
    quittingRootQuitPayoff (sharpReward R singletonLevel) 0
        (sharpInducedBaseRoot point) 3 =
      quittingSetReward (sharpReward R singletonLevel)
        (insert 3 ({2} : Finset Player)) 3 := by
  unfold quittingRootQuitPayoff
  rw [update_eq_update_of_forall_ne
    (fun player hplayer ↦
      sharpInducedBaseRoot_eq_pureSetRoot_of_ne point hplayer)]
  exact quittingRootQuitPayoff_pureSetRoot_eq_insert 0 ({2} : Finset Player) 3

/-- The free player's pure Continue endpoint at the induced base row is the
spectator's reward at the terminal `{2}`. -/
theorem quittingRootContinuePayoff_sharpInducedBaseRoot_three
    (R singletonLevel : ℝ)
    (point : mixedPolytope (quittingBinaryForm ({3} : Finset Player)).sig) :
    quittingRootContinuePayoff (sharpReward R singletonLevel) 0
        (sharpInducedBaseRoot point) 3 =
      quittingSetReward (sharpReward R singletonLevel)
        (({2} : Finset Player).erase 3) 3 := by
  unfold quittingRootContinuePayoff
  rw [update_eq_update_of_forall_ne
    (fun player hplayer ↦
      sharpInducedBaseRoot_eq_pureSetRoot_of_ne point hplayer)]
  exact quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty 0
    ({2} : Finset Player) 3 (by decide)

/-- **The free coordinate strictly prefers Quit, by exactly one.**  The
spectator's reward rises from `singletonLevel` at the terminal `{2}` to
`singletonLevel + 1` at `{2, 3}`, at every real `R`. -/
theorem quittingRootEndpointDifference_sharpInducedBaseRoot_three
    (R singletonLevel : ℝ)
    (point : mixedPolytope (quittingBinaryForm ({3} : Finset Player)).sig) :
    quittingRootEndpointDifference (sharpReward R singletonLevel) 0
      (sharpInducedBaseRoot point) 3 = 1 := by
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_sharpInducedBaseRoot_three,
    quittingRootContinuePayoff_sharpInducedBaseRoot_three,
    show insert 3 ({2} : Finset Player) = {2, 3} from by decide,
    show ({2} : Finset Player).erase 3 = {2} from by decide]
  norm_num +decide [quittingSetReward, sharpReward, sharpSpectatorPassive,
    indicator]

/-- **Every induced Nash point puts the free player on Quit.**  A strict
one-sided endpoint preference leaves the free coordinate no mixed best
reply. -/
theorem sharpInducedBaseRoot_three_eq_pure_true
    (R singletonLevel : ℝ)
    {point : mixedPolytope (quittingBinaryForm ({3} : Finset Player)).sig}
    (hpoint : point ∈ quittingPersistentBaseNashSet
      (sharpReward R singletonLevel) {2} {3}) :
    sharpInducedBaseRoot point 3 = PMF.pure true := by
  obtain ⟨hquit, -⟩ := quittingPersistentBaseRoot_free_purePayoff_le
    (sharpReward R singletonLevel) {2} {3} (by decide) (by decide) point hpoint
    3 (by decide)
  rw [quittingRootSuccessorPayoff_eq_endpointMix] at hquit
  have hdifference :=
    quittingRootEndpointDifference_sharpInducedBaseRoot_three
      R singletonLevel point
  rw [quittingRootEndpointDifference] at hdifference
  have hfalse := Math.PMFProduct.pmfBool_false_toReal
    (sharpInducedBaseRoot point 3)
  have hmix : quittingRootQuitPayoff (sharpReward R singletonLevel) 0
        (sharpInducedBaseRoot point) 3 ≤
      (sharpInducedBaseRoot point 3 true).toReal *
          quittingRootQuitPayoff (sharpReward R singletonLevel) 0
            (sharpInducedBaseRoot point) 3 +
        (1 - (sharpInducedBaseRoot point 3 true).toReal) *
          quittingRootContinuePayoff (sharpReward R singletonLevel) 0
            (sharpInducedBaseRoot point) 3 := by
    rw [← hfalse]
    exact hquit
  have hnonpos : (1 - (sharpInducedBaseRoot point 3 true).toReal) *
      (quittingRootQuitPayoff (sharpReward R singletonLevel) 0
          (sharpInducedBaseRoot point) 3 -
        quittingRootContinuePayoff (sharpReward R singletonLevel) 0
          (sharpInducedBaseRoot point) 3) ≤ 0 := by linarith
  rw [hdifference, mul_one] at hnonpos
  have hle : (sharpInducedBaseRoot point 3 true).toReal ≤ 1 := by
    have hnonneg : (0 : ℝ) ≤
        (sharpInducedBaseRoot point 3 false).toReal :=
      ENNReal.toReal_nonneg
    linarith
  refine Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one _ ?_
  linarith

/-! ## The owner margin -/

/-- **The owner's uniform unsafe margin.**  At every point of the induced Nash
carrier of the persistent base `{2}` with free player three, and at every real
`R` and every real singleton level, owner two's Continue endpoint beats its
Quit endpoint by exactly `39 / 100`.

Positivity is the wrong sign for
`GameTheory.QuittingInducedOwnerNeverChamber.owner_quit_ge_continue`, so the
base does not close there. -/
theorem quittingInducedOwnerNeverExcess_sharpReward_eq
    (R singletonLevel : ℝ)
    {point : mixedPolytope (quittingBinaryForm ({3} : Finset Player)).sig}
    (hpoint : point ∈ quittingPersistentBaseNashSet
      (sharpReward R singletonLevel) {2} {3}) :
    quittingInducedOwnerNeverExcess (sharpReward R singletonLevel) 2 {3} point =
      39 / 100 := by
  have hagree : ∀ player, player ≠ 2 →
      sharpInducedBaseRoot point player =
        quittingPureSetRoot ({3} : Finset Player) player := by
    intro player hplayer
    by_cases hthree : player = 3
    · subst player
      rw [sharpInducedBaseRoot_three_eq_pure_true R singletonLevel hpoint]
      simp [quittingPureSetRoot, quittingSetAction]
    · unfold sharpInducedBaseRoot
      rw [quittingPersistentBaseRoot_apply_of_outside _ _ _
        (by simp [hplayer, hthree])]
      simp [quittingPureSetRoot, quittingSetAction, hthree]
  rw [quittingInducedOwnerNeverExcess]
  change quittingRootContinuePayoff (sharpReward R singletonLevel) 0
      (sharpInducedBaseRoot point) 2 -
    quittingRootQuitPayoff (sharpReward R singletonLevel) 0
      (sharpInducedBaseRoot point) 2 = _
  unfold quittingRootContinuePayoff quittingRootQuitPayoff
  rw [update_eq_update_of_forall_ne hagree (PMF.pure false),
    update_eq_update_of_forall_ne hagree (PMF.pure true)]
  rw [show quittingRootExpectedPayoff (sharpReward R singletonLevel) 0
      (Function.update (quittingPureSetRoot ({3} : Finset Player)) 2
        (PMF.pure false)) 2 =
      quittingRootContinuePayoff (sharpReward R singletonLevel) 0
        (quittingPureSetRoot ({3} : Finset Player)) 2 from rfl,
    show quittingRootExpectedPayoff (sharpReward R singletonLevel) 0
      (Function.update (quittingPureSetRoot ({3} : Finset Player)) 2
        (PMF.pure true)) 2 =
      quittingRootQuitPayoff (sharpReward R singletonLevel) 0
        (quittingPureSetRoot ({3} : Finset Player)) 2 from rfl]
  rw [quittingRootQuitPayoff_pureSetRoot_eq_insert,
    quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty 0
      ({3} : Finset Player) 2 (by decide),
    show insert 2 ({3} : Finset Player) = {2, 3} from by decide,
    show ({3} : Finset Player).erase 2 = {3} from by decide]
  norm_num +decide [quittingSetReward, sharpReward, sharpActivePassive,
    sharpActiveGain, indicator, sharpLoss]

/-- **Owner two is a chamber for neither parameter.**  For the sharp table the
pure singleton row owned by player two fails the sure-exit test at every real
`R` and every real singleton level, in contrast with
`GameTheory.FinFourMaximalRayZeroMinimumRegressions.rationalPureSingletonChamber`
and
`GameTheory.FinFourMaximalRayZeroMinimumRegressions.fullBindingPureSingletonChamber`,
which hold at that same owner for the rational and full-binding completions. -/
theorem not_quittingPureSingletonChamber_sharpReward_two
    (R singletonLevel : ℝ) :
    ¬ QuittingPureSingletonChamber (sharpReward R singletonLevel) (2 : Player) :=
  fun chamber ↦
    not_isQuittingSureExitSet_sharpReward_of_nonempty R singletonLevel
      (Finset.singleton_nonempty (2 : Player)) chamber.isSureExitSet

end FinFourHopfConcreteChambers

end GameTheory
