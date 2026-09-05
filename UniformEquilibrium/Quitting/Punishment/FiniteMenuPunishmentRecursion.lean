import UniformEquilibrium.Quitting.Punishment.FiniteMenuPunishmentOperator
import UniformEquilibrium.Quitting.Punishment.FiniteMenuPunishmentValue
import UniformEquilibrium.Quitting.Punishment.FiniteMenuPunishmentConvergence
import UniformEquilibrium.Quitting.Root.FiniteDeadlineCapRecursion
import UniformEquilibrium.Quitting.Root.FiniteDeadlineWordRealization

/-! # Finite timing-menu punishment and Bellman recursion -/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every finite date-or-Never envelope remains within the reward interval. -/
theorem abs_quittingFiniteRootWordCap_zero_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (who : ι) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingFiniteRootWordCap reward roots who 0| ≤ bound := by
  have hbound : 0 ≤ bound :=
    (abs_nonneg (reward ⟨{who}, Finset.singleton_nonempty who⟩ who)).trans
      (hreward _ who)
  induction roots with
  | nil => simpa [quittingFiniteRootWordCap] using hbound
  | cons root roots ih =>
      change |quittingFiniteRootWordCap reward [root] who
        (quittingFiniteRootWordCap reward roots who 0)| ≤ bound
      exact abs_quittingFiniteRootWordCap_singleton_le reward root who hreward ih

theorem abs_quittingFiniteMenuPunishmentValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (deadline : ℕ) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingFiniteMenuPunishmentValue reward deadline who| ≤ bound := by
  obtain ⟨mixed, hvalue, _⟩ :=
    exists_quittingFiniteMenuPunishmentValue_minimizer reward deadline who
  rw [← hvalue, quittingFiniteDeadlineReplyCap_eq_finiteRootWordCap]
  exact abs_quittingFiniteRootWordCap_zero_le reward _ who hreward

/-- The Bellman optimum is attained by a literal finite product-root word. -/
theorem exists_quittingFiniteRootWordCap_minimizer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (deadline : ℕ) :
    ∃ roots : List (ι → PMF Bool), roots.length = deadline ∧
      quittingFiniteRootWordCap reward roots who 0 =
        (quittingFiniteMenuPunishmentOperator reward who)^[deadline] 0 ∧
      ∀ other : List (ι → PMF Bool), other.length = deadline →
        (quittingFiniteMenuPunishmentOperator reward who)^[deadline] 0 ≤
          quittingFiniteRootWordCap reward other who 0 := by
  induction deadline with
  | zero =>
      refine ⟨[], rfl, rfl, ?_⟩
      intro other hlength
      have : other = [] := List.length_eq_zero_iff.mp hlength
      subst other
      exact le_rfl
  | succ deadline ih =>
      obtain ⟨tail, hlength, htail, hminimum⟩ := ih
      obtain ⟨root, hroot, hrootMinimum⟩ :=
        exists_quittingFiniteMenuPunishmentOperator_minimizer reward who
          ((quittingFiniteMenuPunishmentOperator reward who)^[deadline] 0)
      refine ⟨root :: tail, by simp [hlength], ?_, ?_⟩
      · change quittingFiniteRootWordCap reward [root] who
          (quittingFiniteRootWordCap reward tail who 0) = _
        rw [htail, hroot, Function.iterate_succ_apply']
      · intro other hother
        cases other with
        | nil => simp at hother
        | cons head rest =>
            have hrest : rest.length = deadline := by simpa using hother
            have hvalue := hminimum rest hrest
            rw [Function.iterate_succ_apply']
            apply (hrootMinimum head).trans
            change quittingFiniteRootWordCap reward [head] who
              ((quittingFiniteMenuPunishmentOperator reward who)^[deadline] 0) ≤
                quittingFiniteRootWordCap reward [head] who
                  (quittingFiniteRootWordCap reward rest who 0)
            rw [quittingFiniteRootWordCap_singleton_eq_fixedOpponents,
              quittingFiniteRootWordCap_singleton_eq_fixedOpponents]
            apply max_le_max le_rfl
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_left hvalue
                (quittingStationaryFixedOpponentsContinueMass_nonneg head who))

/-- Actual finite-menu laws cannot beat the Bellman optimum. -/
theorem operator_iterate_le_quittingFiniteMenuPunishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (deadline : ℕ) :
    (quittingFiniteMenuPunishmentOperator reward who)^[deadline] 0 ≤
      quittingFiniteMenuPunishmentValue reward deadline who := by
  obtain ⟨_, _, _, hminimum⟩ :=
    exists_quittingFiniteRootWordCap_minimizer reward who deadline
  apply le_ciInf
  intro mixed
  rw [quittingFiniteDeadlineReplyCap_eq_finiteRootWordCap]
  exact hminimum _ List.length_ofFn

@[simp] theorem quittingFiniteMenuPunishmentValue_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingFiniteMenuPunishmentValue reward 0 who = 0 := by
  obtain ⟨mixed, hvalue, _⟩ :=
    exists_quittingFiniteMenuPunishmentValue_minimizer reward 0 who
  rw [← hvalue, quittingFiniteDeadlineReplyCap_eq_finiteRootWordCap]
  rfl

/-- The primary actual-menu minimum equals the scalar Bellman iterate. Both
inequalities use actual semantic adapters, including legal word realization. -/
theorem quittingFiniteMenuPunishmentValue_eq_operator_iterate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (deadline : ℕ) :
    quittingFiniteMenuPunishmentValue reward deadline who =
      (quittingFiniteMenuPunishmentOperator reward who)^[deadline] 0 := by
  apply le_antisymm
  · obtain ⟨word, hlength, hword, _⟩ :=
      exists_quittingFiniteRootWordCap_minimizer reward who deadline
    subst deadline
    let roots : ℕ → ι → PMF Bool := fun time ↦
      if htime : time < word.length then word[time] else quittingAllContinueRoot
    have hlist : (List.ofFn fun time : Fin word.length ↦ roots time.val) = word := by
      calc
        _ = List.ofFn word.get := by
          congr 1
          funext time
          simp [roots, time.isLt]
        _ = word := List.ofFn_get word
    obtain ⟨mixed, hmixed⟩ :=
      exists_finiteDeadlineReplyCap_eq_finiteRootWordCap reward roots word.length
    obtain ⟨_, _, hminimum⟩ :=
      exists_quittingFiniteMenuPunishmentValue_minimizer reward word.length who
    have hbound := hminimum mixed
    rwa [hmixed who, hlist, hword] at hbound
  · exact operator_iterate_le_quittingFiniteMenuPunishmentValue reward who deadline

theorem quittingFiniteMenuPunishmentValue_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (deadline : ℕ) :
    quittingFiniteMenuPunishmentValue reward (deadline + 1) who =
      quittingFiniteMenuPunishmentOperator reward who
        (quittingFiniteMenuPunishmentValue reward deadline who) := by
  simp only [quittingFiniteMenuPunishmentValue_eq_operator_iterate,
    Function.iterate_succ_apply']

/-- Actual finite-menu punishment converges to full behavioral punishment. -/
theorem tendsto_quittingFiniteMenuPunishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Tendsto (fun deadline : ℕ ↦ quittingFiniteMenuPunishmentValue reward deadline who)
      atTop (nhds (quittingPunishmentValue reward who)) := by
  simpa only [quittingFiniteMenuPunishmentValue_eq_operator_iterate] using
    tendsto_quittingFiniteMenuPunishmentOperator_iterate reward who

/-- Uniform finite-player deficit of a finite menu below full punishment. -/
def quittingFiniteMenuPunishmentDeficit [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun who ↦
    max 0 (quittingPunishmentValue reward who -
      quittingFiniteMenuPunishmentValue reward deadline who)

theorem quittingFiniteMenuPunishmentDeficit_nonneg [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ) :
    0 ≤ quittingFiniteMenuPunishmentDeficit reward deadline := by
  let who : ι := Classical.choice inferInstance
  exact (le_max_left _ _).trans (Finset.le_sup'
    (fun player ↦ max 0 (quittingPunishmentValue reward player -
      quittingFiniteMenuPunishmentValue reward deadline player)) (Finset.mem_univ who))

theorem quittingPunishmentValue_sub_menu_le_deficit [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ) (who : ι) :
    quittingPunishmentValue reward who - quittingFiniteMenuPunishmentValue reward deadline who ≤
      quittingFiniteMenuPunishmentDeficit reward deadline :=
  (le_max_right _ _).trans (Finset.le_sup'
    (fun player ↦ max 0 (quittingPunishmentValue reward player -
      quittingFiniteMenuPunishmentValue reward deadline player)) (Finset.mem_univ who))

theorem tendsto_quittingFiniteMenuPunishmentDeficit [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Tendsto (quittingFiniteMenuPunishmentDeficit reward) atTop (nhds 0) := by
  have hplayer (who : ι) : Tendsto (fun deadline : ℕ ↦
      max 0 (quittingPunishmentValue reward who -
        quittingFiniteMenuPunishmentValue reward deadline who)) atTop (nhds 0) := by
    have hconstant : Tendsto (fun _ : ℕ ↦ quittingPunishmentValue reward who)
        atTop (nhds (quittingPunishmentValue reward who)) := tendsto_const_nhds
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ))
      atTop (nhds 0)).max
        (hconstant.sub (tendsto_quittingFiniteMenuPunishmentValue reward who))
  have hmaximum := Filter.Tendsto.finset_sup'_nhds_apply
    (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
    (fun who _ ↦ hplayer who)
  change Tendsto (fun deadline : ℕ ↦ Finset.univ.sup' Finset.univ_nonempty
    (fun who ↦ max 0 (quittingPunishmentValue reward who -
      quittingFiniteMenuPunishmentValue reward deadline who))) atTop (nhds 0)
  simpa using hmaximum

end GameTheory
