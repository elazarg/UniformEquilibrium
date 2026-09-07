import UniformEquilibrium.Quitting.Cycles.PairedCycleStoppingLaws
import UniformEquilibrium.Quitting.Cycles.PairedCycleFiniteSource

/-! # Literal finite timing menus for the same selected paired cycle -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

/-- One menu simultaneously realizes exact laws, payoff/cap/debt, an early cap
attainer for every player, and the full behavioral geometric Nash bound. -/
theorem exists_finiteMenu_exact_of_selected
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (initial : Fin period) (turns : ℕ) (hturns : 1 ≤ turns) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (turns * period)),
      (∀ player, (quittingFiniteDeadlineTimingLaw (mixed player)).toPMF =
        quittingBehaviorStoppingLaw reward
          (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial
            (turns * period) player)) ∧
      (∀ player,
        quittingTerminalPayoff reward
            (quittingFiniteDeadlineTimingProfile reward (turns * period) mixed) player =
          (1 - jointCycleSurvival q ^ turns) * value reward schedule q hq initial player ∧
        quittingContinuationBestResponseValue reward
            (quittingFiniteDeadlineTimingProfile reward (turns * period) mixed) player =
          value reward schedule q hq initial player ∧
        quittingTerminalDeviationDebt reward
            (quittingFiniteDeadlineTimingProfile reward (turns * period) mixed) player =
          jointCycleSurvival q ^ turns * value reward schedule q hq initial player ∧
        quittingTerminalPayoff reward
            (Function.update (quittingFiniteDeadlineTimingProfile reward (turns * period) mixed)
              player (quittingPureTimeBehaviorStrategy reward player
                (some (firstActiveTime schedule initial player)))) player =
          value reward schedule q hq initial player) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
        (21 / 10 * (99 / 100 : ℝ) ^ (Fintype.card ι * turns))
        (quittingFiniteDeadlineTimingProfile reward (turns * period) mixed) := by
  obtain ⟨mixed, hlaws, hpair, hpure⟩ :=
    exists_finiteDeadlineTimingProfile_cyclicFinite_exact reward (cycle schedule q hq)
      initial (turns * period)
  have hpayoff := congrArg Prod.fst hpair
  have hcap := congrArg Prod.snd hpair
  change quittingTerminalPayoff reward _ = quittingTerminalPayoff reward _ at hpayoff
  change (fun player => quittingContinuationBestResponseValue reward _ player) =
    (fun player => quittingContinuationBestResponseValue reward _ player) at hcap
  refine ⟨mixed, hlaws, ?_, ?_⟩
  · intro player
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hpayoff, finiteProfile_payoff_eq]
    · rw [congrFun hcap player]
      exact finiteProfile_cap_eq_value reward schedule hregion q hq hinterior hzero
        initial turns hturns player
    · unfold quittingTerminalDeviationDebt
      rw [hpayoff, congrFun hcap player]
      exact finiteProfile_debt_eq reward schedule hregion q hq hinterior hzero
        initial turns hturns player
    · rw [hpure]
      exact finiteProfile_firstActiveTime_attains_value reward schedule hregion q hq
        hinterior hzero initial turns hturns player
  · intro player deviation
    have hreply := quittingTerminalPayoff_update_le_continuationBestResponseValue reward
      (quittingFiniteDeadlineTimingProfile reward (turns * period) mixed) player deviation
    have hdebt := finiteProfile_debt_le_geometric reward schedule hregion q hq
      hinterior hzero initial turns hturns player
    unfold quittingTerminalDeviationDebt at hdebt
    rw [congrFun hcap player] at hreply
    rw [hpayoff]
    linarith

end GameTheory.PairedCycle
