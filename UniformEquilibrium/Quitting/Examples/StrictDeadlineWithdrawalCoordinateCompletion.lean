import UniformEquilibrium.Quitting.Examples.StrictDeadlineWithdrawalTable
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Independent thirty-three plus eleven terminal coordinates

All sixteen singleton entries are fixed, not merely the four own singletons.
Every nonsingleton entry for recipients zero, one and two is an independent
arbitrary real parameter. The eleven remaining nonsingleton entries are the
outsider's actual rewards. This parameterization does not assert that every
completion satisfies the raw deadline rows.
-/

noncomputable section

namespace GameTheory.StrictDeadlineWithdrawal

open FinFourLastPlayerChild

abbrev ChildCollisionCoordinate :=
  {coordinate : {S : Finset (Fin 4) // S.Nonempty} × Fin 4 //
    coordinate.1.1.card ≠ 1 ∧ coordinate.2 ≠ 3}

abbrev OutsiderCollisionCoordinate :=
  {terminal : {S : Finset (Fin 4) // S.Nonempty} // terminal.1.card ≠ 1}

abbrev ChildCollisionSpace := ChildCollisionCoordinate → ℝ
abbrev OutsiderCollisionSpace := OutsiderCollisionCoordinate → ℝ

theorem card_childCollisionCoordinate : Fintype.card ChildCollisionCoordinate = 33 := by
  decide

theorem card_outsiderCollisionCoordinate : Fintype.card OutsiderCollisionCoordinate = 11 := by
  decide

/-- Each actual reward is affine in the outsider's eleven final reward coordinates. -/
def completionRewardAffine (free : ChildCollisionSpace)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    OutsiderCollisionSpace →ᵃ[ℝ] ℝ :=
  if hsingle : terminal.1.card = 1 then
    AffineMap.const ℝ OutsiderCollisionSpace (reward terminal who)
  else if hwho : who = 3 then
    (LinearMap.proj ⟨terminal, hsingle⟩ : OutsiderCollisionSpace →ₗ[ℝ] ℝ).toAffineMap
  else
    AffineMap.const ℝ OutsiderCollisionSpace (free ⟨(terminal, who), hsingle, hwho⟩)

def completionReward (free : ChildCollisionSpace) (outside : OutsiderCollisionSpace) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal who => completionRewardAffine free terminal who outside

theorem completionReward_child_coordinate (free : ChildCollisionSpace)
    (outside : OutsiderCollisionSpace) (coordinate : ChildCollisionCoordinate) :
    completionReward free outside coordinate.1.1 coordinate.1.2 = free coordinate := by
  simp [completionReward, completionRewardAffine, coordinate.property]

theorem completionReward_outsider_coordinate (free : ChildCollisionSpace)
    (outside : OutsiderCollisionSpace) (coordinate : OutsiderCollisionCoordinate) :
    completionReward free outside coordinate.1 3 = outside coordinate := by
  simp [completionReward, completionRewardAffine, coordinate.property]

theorem completionReward_singleton (free : ChildCollisionSpace)
    (outside : OutsiderCollisionSpace) (owner who : Fin 4) :
    completionReward free outside ⟨{owner}, Finset.singleton_nonempty owner⟩ who =
      reward ⟨{owner}, Finset.singleton_nonempty owner⟩ who := by
  simp [completionReward, completionRewardAffine]

/-- No parameter is redundant: both complete coordinate blocks are recovered from the table. -/
theorem completionReward_injective :
    Function.Injective (fun parameters : ChildCollisionSpace × OutsiderCollisionSpace =>
      completionReward parameters.1 parameters.2) := by
  intro first second heq
  apply Prod.ext
  · funext coordinate
    have h := congrFun (congrFun heq coordinate.1.1) coordinate.1.2
    simpa only [completionReward_child_coordinate] using h
  · funext coordinate
    have h := congrFun (congrFun heq coordinate.1) 3
    simpa only [completionReward_outsider_coordinate] using h

/-- Every actual table with these sixteen singleton entries occurs in the chart. -/
theorem completionReward_covers_fixed_singletons
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingle : ∀ owner who, table ⟨{owner}, Finset.singleton_nonempty owner⟩ who =
      reward ⟨{owner}, Finset.singleton_nonempty owner⟩ who) :
    completionReward (fun coordinate => table coordinate.1.1 coordinate.1.2)
      (fun coordinate => table coordinate.1 3) = table := by
  funext terminal who
  by_cases hcard : terminal.1.card = 1
  · obtain ⟨owner, hterminal⟩ := Finset.card_eq_one.mp hcard
    have heq : terminal = ⟨{owner}, Finset.singleton_nonempty owner⟩ :=
      Subtype.ext hterminal
    rw [heq, completionReward_singleton, hsingle]
  · by_cases hwho : who = 3
    · subst who
      exact completionReward_outsider_coordinate _ _ ⟨terminal, hcard⟩
    · exact completionReward_child_coordinate _ _ ⟨(terminal, who), hcard, hwho⟩

/-- Varying only outsider recipients leaves every child-recipient entry unchanged. -/
theorem completionReward_child_recipient_congr (free : ChildCollisionSpace)
    (first second : OutsiderCollisionSpace)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) (hwho : who ≠ 3) :
    completionReward free first terminal who = completionReward free second terminal who := by
  by_cases hsingle : terminal.1.card = 1
  all_goals simp [completionReward, completionRewardAffine, hsingle, hwho]

/-- This is the actual child-plus-outsider restriction, including joined coalitions. -/
theorem completionReward_childReward_recipient_congr (free : ChildCollisionSpace)
    (first second : OutsiderCollisionSpace)
    (terminal : {S : Finset (Option Child) // S.Nonempty}) (who : Child) :
    childReward (completionReward free first) terminal (some who) =
      childReward (completionReward free second) terminal (some who) := by
  simpa only [quittingChildWithOutsiderReward_apply_original,
    quittingChildWithOutsiderOriginalEmbedding_some] using
    completionReward_child_recipient_congr free first second
      ⟨terminal.1.map (quittingChildWithOutsiderOriginalEmbedding (· = 3) outside),
        Finset.map_nonempty.mpr terminal.2⟩ who.1 who.2

end GameTheory.StrictDeadlineWithdrawal
