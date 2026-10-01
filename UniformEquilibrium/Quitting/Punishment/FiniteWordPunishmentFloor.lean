import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Root.CommonPrefixCapStability

/-! # Punishment floors for finite response words with formal continuations

Only the continuation coordinate of the responding player is used. The opponent
word is arbitrary; no Nash, contraction or positive reach premise is needed.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The two actual one-row endpoints preserve the minmax floor, with a
nonnegative accuracy allowance, for every independent opponent row. -/
theorem quittingPunishmentValue_sub_le_rootEndpointMax
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (eta : ℝ) (heta : 0 ≤ eta)
    (htail : quittingPunishmentValue reward who - eta ≤ tail who) :
    quittingPunishmentValue reward who - eta ≤
      max (quittingRootQuitPayoff reward tail root who)
        (quittingRootContinuePayoff reward tail root who) := by
  let c := quittingStationaryFixedOpponentsContinueMass root who
  have hc0 : 0 ≤ c := quittingStationaryFixedOpponentsContinueMass_nonneg root who
  have hc1 : c ≤ 1 := quittingStationaryFixedOpponentsContinueMass_le_one root who
  have hquitEq :
      quittingRootQuitPayoff reward tail root who =
        quittingStationaryFixedOpponentsQuitValue reward root who := by
    simpa [quittingStationaryFixedOpponentsQuitValue] using
      quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward (fun _ => root) who tail 0
  have hcontinueEq :
      quittingRootContinuePayoff reward tail root who =
        quittingStationaryFixedOpponentsContinueReward reward root who + c * tail who := by
    simpa [c, quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass] using
      quittingRootContinuePayoff_eq_fixedOpponents reward (fun _ => root) who tail 0
  rw [hquitEq, hcontinueEq]
  by_cases hdeg : c = 1
  · have hzero := quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
      reward (root := root) (who := who) hdeg
    rw [hzero, hdeg, one_mul, zero_add]
    exact htail.trans (le_max_right _ _)
  · have hc : c < 1 := lt_of_le_of_ne hc1 hdeg
    have hcap := quittingPunishmentValue_le_stationaryUnilateralCap reward who root
    rw [quittingStationaryUnilateralCap_eq_max_div] at hcap
    rcases le_max_iff.mp hcap with hquit | hwait
    · exact (sub_le_self _ heta).trans (hquit.trans (le_max_left _ _))
    · have hden : 0 < 1 - c := sub_pos.mpr hc
      have hreward :
          quittingPunishmentValue reward who * (1 - c) ≤
            quittingStationaryFixedOpponentsContinueReward reward root who :=
        (le_div_iff₀ hden).mp hwait
      have hscaled := mul_le_mul_of_nonneg_left htail hc0
      have herror := mul_le_mul_of_nonneg_right hc1 heta
      apply le_trans _ (le_max_right _ _)
      nlinarith

/-- Any finite independent response word with a formal suffix at the
minmax floor has a response cap at the same floor. Empty words and zero
opponent survival require no division or exceptional hypotheses. -/
theorem quittingPunishmentValue_sub_le_finiteRootWordCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (who : ι) (eta value : ℝ)
    (heta : 0 ≤ eta)
    (hvalue : quittingPunishmentValue reward who - eta ≤ value) :
    quittingPunishmentValue reward who - eta ≤
      quittingFiniteRootWordCap reward roots who value := by
  induction roots with
  | nil => exact hvalue
  | cons root roots ih =>
      have h := quittingPunishmentValue_sub_le_rootEndpointMax reward
        (Function.update 0 who (quittingFiniteRootWordCap reward roots who value))
        root who eta heta (by simpa only [Function.update_self] using ih)
      rw [quittingRootQuitPayoff_continuation_invariant reward _ 0 root who] at h
      exact h

end GameTheory
