import UniformEquilibrium.Quitting.Cycles.PairedCycleFin4Pivot
import UniformEquilibrium.Quitting.Cycles.PairedCycleAffineTruncation
import UniformEquilibrium.Quitting.Cycles.CyclicFiniteMenu
import UniformEquilibrium.Quitting.Cycles.PairedCycleFiniteSource

/-! # Exact Fin4 pivot menus with the paired geometric full-regret bound -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine

def fin4PivotValue
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (q : Fin 4 → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) : Payoff (Fin 4) :=
  fun player => fin4PivotScale reward player * value reward fin4Schedule q hq 0 player +
    fin4PivotShift reward player

theorem fin4PivotFinite_debt_le_geometric
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hregion : RawRegion reward fin4Schedule) (q : Fin 4 → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap fin4Schedule.partner (singleton reward)
      (partnerReward reward fin4Schedule) (jointReward reward fin4Schedule)
      (quietRows reward fin4Schedule) q player = 0)
    (turns : ℕ) (hturns : 1 ≤ turns) (player : Fin 4) :
    quittingTerminalDeviationDebt (fin4PivotReward reward)
        (quittingCyclicFiniteProfile (fin4PivotReward reward)
          (cycle fin4Schedule q hq) 0 (turns * 2)) player ≤
      5 / 3 * (99 / 100 : ℝ) ^ (4 * turns) := by
  rw [fin4PivotReward, affine_finiteProfile_debt_eq reward fin4Schedule hregion q hq
    hinterior hzero (fin4PivotScale reward) (fin4PivotShift reward)
    (fin4PivotScale_pos reward hregion) 0 turns hturns player
    (fin4PivotSingleton_nonneg reward hregion player)]
  have hv := (fin4PivotValue_bounds reward hregion q hq hinterior hzero player).2
  have hupper : fin4PivotScale reward player * value reward fin4Schedule q hq 0 player +
      fin4PivotShift reward player ≤ 5 / 3 := by
    split_ifs at hv <;> linarith
  have hsurvival := jointCycleSurvival_pow_le_geometric q
    (fun player => ⟨(hinterior player).1.le, (hq player).2⟩) turns
  simp only [Fintype.card_fin] at hsurvival
  have hnonneg := pow_nonneg (jointCycleSurvival_nonneg q (fun player => (hq player).2)) turns
  have hscaled := mul_le_mul_of_nonneg_left hupper hnonneg
  nlinarith

/-- The same selected hazards give one literal finite menu satisfying both canonical
inequalities, with exact transformed payoff and unrestricted cap coordinates. -/
theorem exists_fin4PivotMenu_exact_of_selected
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hregion : RawRegion reward fin4Schedule) (q : Fin 4 → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap fin4Schedule.partner (singleton reward)
      (partnerReward reward fin4Schedule) (jointReward reward fin4Schedule)
      (quietRows reward fin4Schedule) q player = 0)
    (turns : ℕ) (hturns : 1 ≤ turns) :
    ∃ mixed : Fin 4 → PMF (QuittingFiniteDeadlineTimingAction (turns * 2)),
      (∀ player, (quittingFiniteDeadlineTimingLaw (mixed player)).toPMF =
        quittingBehaviorStoppingLaw (fin4PivotReward reward)
          (quittingCyclicFiniteProfile (fin4PivotReward reward)
            (cycle fin4Schedule q hq) 0 (turns * 2) player)) ∧
      quittingTerminalSemanticPair (fin4PivotReward reward)
          (quittingFiniteDeadlineTimingProfile (fin4PivotReward reward) (turns * 2) mixed) =
        (fun player => (1 - jointCycleSurvival q ^ turns) * fin4PivotValue reward q hq player,
          fin4PivotValue reward q hq) ∧
      quittingTerminalExploitability (fin4PivotReward reward)
          (quittingFiniteDeadlineTimingProfile (fin4PivotReward reward) (turns * 2) mixed) ≤
        5 / 3 * (99 / 100 : ℝ) ^ (4 * turns) ∧
      quittingFiniteDeadlineMenuExploitability (fin4PivotReward reward) (turns * 2) mixed ≤
        5 / 3 * (99 / 100 : ℝ) ^ (4 * turns) ∧
      quittingFiniteDeadlineNeverPayoff (fin4PivotReward reward) (turns * 2) mixed 0 +
          quittingFiniteDeadlineOpponentNeverProduct (turns * 2) mixed 0 -
          quittingTerminalPayoff (fin4PivotReward reward)
            (quittingFiniteDeadlineTimingProfile (fin4PivotReward reward) (turns * 2) mixed) 0 ≤
        5 / 3 * (99 / 100 : ℝ) ^ (4 * turns) := by
  obtain ⟨mixed, hlaws, hpair, _⟩ := exists_finiteDeadlineTimingProfile_cyclicFinite_exact
    (fin4PivotReward reward) (cycle fin4Schedule q hq) 0 (turns * 2)
  have hpayoff := congrArg Prod.fst hpair
  have hcap := congrArg Prod.snd hpair
  change quittingTerminalPayoff (fin4PivotReward reward) _ =
    quittingTerminalPayoff (fin4PivotReward reward) _ at hpayoff
  change (fun player => quittingContinuationBestResponseValue (fin4PivotReward reward) _ player) =
    (fun player => quittingContinuationBestResponseValue (fin4PivotReward reward) _ player) at hcap
  have hexploit : quittingTerminalExploitability (fin4PivotReward reward)
      (quittingFiniteDeadlineTimingProfile (fin4PivotReward reward) (turns * 2) mixed) ≤
        5 / 3 * (99 / 100 : ℝ) ^ (4 * turns) := by
    rw [quittingTerminalExploitability_eq_max_debt]
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro player
    unfold quittingTerminalDeviationDebt
    rw [hpayoff, congrFun hcap player]
    exact fin4PivotFinite_debt_le_geometric reward hregion q hq hinterior hzero
      turns hturns player
  have hcanonical := singlePivot_fullExploitability_eq_max_menuExploitability_scalar
    (fin4PivotReward reward) 0
    (fin4PivotReward_isSinglePivotSingletonTable reward hregion) (turns * 2) mixed
  have hmenu := (le_max_left _ _).trans (hcanonical.symm.le.trans hexploit)
  have hscalar := (le_max_right _ _).trans (hcanonical.symm.le.trans hexploit)
  refine ⟨mixed, hlaws, ?_, hexploit, hmenu, hscalar⟩
  rw [hpair]
  apply Prod.ext
  · funext player
    change quittingTerminalPayoff (fin4PivotReward reward) _ player = _
    exact affine_finiteProfile_payoff_eq reward fin4Schedule q hq
      (fun player => by linarith [(hinterior player).1])
      (fin4PivotScale reward) (fin4PivotShift reward) 0 turns player
  · funext player
    change quittingContinuationBestResponseValue (fin4PivotReward reward) _ player = _
    exact affine_finiteProfile_cap_eq reward fin4Schedule hregion q hq hinterior hzero
      (fin4PivotScale reward) (fin4PivotShift reward) (fin4PivotScale_pos reward hregion)
      0 turns hturns player (fin4PivotSingleton_nonneg reward hregion player)

/-- The actual transformed target strictly exceeds the canonical singleton
vector, including the pivot's unit singleton, not merely zero. -/
theorem fin4PivotValue_gt_singleton_of_selected
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hregion : RawRegion reward fin4Schedule) (q : Fin 4 → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap fin4Schedule.partner (singleton reward)
      (partnerReward reward fin4Schedule) (jointReward reward fin4Schedule)
      (quietRows reward fin4Schedule) q player = 0) (player : Fin 4) :
    (if player = 0 then (1 : ℝ) else 0) < fin4PivotValue reward q hq player := by
  have hv := (value_bounds_of_selected reward fin4Schedule hregion q hq hinterior hzero
    0 player).1
  have hmul := mul_lt_mul_of_pos_left hv (fin4PivotScale_pos reward hregion player)
  have hsingleton := fin4PivotReward_isSinglePivotSingletonTable reward hregion player
  change fin4PivotScale reward player * singleton reward player +
    fin4PivotShift reward player = _ at hsingleton
  unfold fin4PivotValue
  linarith


end GameTheory.PairedCycle
