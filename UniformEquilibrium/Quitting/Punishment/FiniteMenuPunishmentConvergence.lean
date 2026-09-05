import UniformEquilibrium.Quitting.Punishment.FiniteMenuPunishmentOperator

/-! # Identification of the signed punishment Bellman limit -/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Comparing with one stationary root bounds the signed iterate limit by its
full behavioral cap, even when finite iterates start above a negative cap. -/
theorem operator_iterate_limit_le_quittingStationaryUnilateralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) {limit : ℝ}
    (htendsto : Tendsto (fun index : ℕ ↦
      (quittingFiniteMenuPunishmentOperator reward who)^[index] 0) atTop (nhds limit))
    (root : ι → PMF Bool) :
    limit ≤ quittingStationaryUnilateralCap reward root who := by
  let operator := quittingFiniteMenuPunishmentOperator reward who
  let cap := quittingStationaryUnilateralCap reward root who
  let mass := quittingStationaryFixedOpponentsContinueMass root who
  let quit := quittingStationaryFixedOpponentsQuitValue reward root who
  let flow := quittingStationaryFixedOpponentsContinueReward reward root who
  have hmassNonneg : 0 ≤ mass := quittingStationaryFixedOpponentsContinueMass_nonneg root who
  have hmassLe : mass ≤ 1 := quittingStationaryFixedOpponentsContinueMass_le_one root who
  have hrow (value : ℝ) : operator value ≤ max quit (flow + mass * value) := by
    obtain ⟨_, _, hminimum⟩ :=
      exists_quittingFiniteMenuPunishmentOperator_minimizer reward who value
    simpa only [quittingFiniteRootWordCap_singleton_eq_fixedOpponents] using hminimum root
  by_cases hmass : mass = 1
  · have hflow : flow = 0 :=
      quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one reward hmass
    have hcap : cap = max quit 0 := by
      change max quit (flow / (1 - mass)) = max quit 0
      rw [hmass, sub_self, div_zero]
    have hbound (index : ℕ) : operator^[index] 0 ≤ cap := by
      induction index with
      | zero => simpa only [Function.iterate_zero, id_eq, hcap] using le_max_right quit 0
      | succ index ih =>
          rw [Function.iterate_succ_apply']
          apply (hrow _).trans
          rw [hflow, hmass, one_mul, zero_add]
          exact max_le (hcap ▸ le_max_left quit 0) ih
    exact le_of_tendsto htendsto (Filter.Eventually.of_forall hbound)
  · have hcontracts : mass < 1 := lt_of_le_of_ne hmassLe hmass
    have hbellman : cap = max quit (flow + mass * cap) :=
      quittingStationaryUnilateralCap_bellman reward root who hcontracts
    have hquit : quit ≤ cap := hbellman ▸ le_max_left _ _
    have hflowCap : flow + mass * cap ≤ cap := (le_max_right _ _).trans_eq hbellman.symm
    have hbound (index : ℕ) : operator^[index] 0 ≤ cap + mass ^ index * |cap| := by
      induction index with
      | zero =>
          simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
          have := neg_abs_le cap
          linarith
      | succ index ih =>
          rw [Function.iterate_succ_apply']
          apply (hrow _).trans
          apply max_le
          · exact hquit.trans (le_add_of_nonneg_right
              (mul_nonneg (pow_nonneg hmassNonneg _) (abs_nonneg cap)))
          · calc
              flow + mass * operator^[index] 0 ≤
                  flow + mass * (cap + mass ^ index * |cap|) := by
                    gcongr
              _ = flow + mass * cap + mass ^ (index + 1) * |cap| := by
                    rw [pow_succ]
                    ring
              _ ≤ cap + mass ^ (index + 1) * |cap| := by linarith
    have hpower : Tendsto (fun index : ℕ ↦ mass ^ index) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hmassNonneg hcontracts
    have hupper : Tendsto (fun index : ℕ ↦ cap + mass ^ index * |cap|)
        atTop (nhds cap) := by
      simpa using tendsto_const_nhds.add (hpower.mul_const |cap|)
    exact le_of_tendsto_of_tendsto' htendsto hupper hbound

/-- The Bellman iterate limit is the full behavioral punishment value. This
statement concerns the scalar sequence; the actual-menu recursion is separate. -/
theorem operator_iterate_limit_eq_quittingPunishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) {limit : ℝ}
    (htendsto : Tendsto (fun index : ℕ ↦
      (quittingFiniteMenuPunishmentOperator reward who)^[index] 0) atTop (nhds limit))
    (hfixed : quittingFiniteMenuPunishmentOperator reward who limit = limit) :
    limit = quittingPunishmentValue reward who := by
  apply le_antisymm
  · rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
    exact le_ciInf (operator_iterate_limit_le_quittingStationaryUnilateralCap
      reward who htendsto)
  · exact quittingPunishmentValue_le_operator_iterate_limit reward who htendsto hfixed

theorem tendsto_quittingFiniteMenuPunishmentOperator_iterate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Tendsto (fun index : ℕ ↦
      (quittingFiniteMenuPunishmentOperator reward who)^[index] 0) atTop
      (nhds (quittingPunishmentValue reward who)) := by
  obtain ⟨limit, _, htendsto, hfixed⟩ :=
    exists_quittingFiniteMenuPunishmentOperator_iterate_limit reward who
  rwa [operator_iterate_limit_eq_quittingPunishmentValue reward who htendsto hfixed] at htendsto

end GameTheory
