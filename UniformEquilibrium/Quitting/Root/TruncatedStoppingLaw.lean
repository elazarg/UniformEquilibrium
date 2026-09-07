import UniformEquilibrium.Quitting.Root.FiniteDeadlineWordRealization
import MathUE.ProbabilityMassFunction.LateFiniteStoppingLawCensor
import MathUE.ProbabilityMassFunction.FiniteTailCollapse
import MathUE.ProbabilityMassFunction.FiniteSupportSurvival

/-! # Literal finite root truncation is exact late-finite stopping-law censoring -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem quittingBehaviorStoppingLaw_truncatedRoots_some_eq_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (deadline time : ℕ) (htime : time < deadline) (who : ι) :
    quittingBehaviorStoppingLaw reward
        (quittingRootSequenceProfile reward (quittingTruncatedRoots roots deadline) 0 who)
        (some time) =
      quittingBehaviorStoppingLaw reward (quittingRootSequenceProfile reward roots 0 who)
        (some time) := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
    (PMF.apply_ne_top _ _)).mp
  rw [quittingBehaviorStoppingLaw_some_toReal, quittingBehaviorStoppingLaw_some_toReal,
    quittingHazardStopMass_eq_survival_mul_stop, quittingHazardStopMass_eq_survival_mul_stop,
    quittingHazardSurvival_eq_prod, quittingHazardSurvival_eq_prod]
  simp only [quittingBehaviorLiveHazard, quittingRootSequenceProfile, Nat.zero_add]
  rw [quittingTruncatedRoots_of_lt roots htime]
  congr 1
  apply Finset.prod_congr rfl
  intro offset hoff
  rw [quittingTruncatedRoots_of_lt roots (lt_trans (Finset.mem_range.mp hoff) htime)]

omit [DecidableEq ι] in
/-- Stopping all hazards at a positive deadline independently sends precisely the
later finite atoms to Never; earlier finite masses are unchanged. -/
theorem quittingBehaviorStoppingLaw_truncatedRoots_eq_censor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (deadline : ℕ) (hdeadline : 0 < deadline) (who : ι) :
    quittingBehaviorStoppingLaw reward
        (quittingRootSequenceProfile reward (quittingTruncatedRoots roots deadline) 0 who) =
      censorLateFiniteStoppingLaw
        (quittingBehaviorStoppingLaw reward (quittingRootSequenceProfile reward roots 0 who))
        (deadline - 1) := by
  apply pmf_eq_of_eq_away _ _ none
  intro choice hchoice
  cases choice with
  | none => exact (hchoice rfl).elim
  | some time =>
      by_cases htime : time < deadline
      · rw [censorLateFiniteStoppingLaw_apply_some_of_le _ (by omega)]
        exact quittingBehaviorStoppingLaw_truncatedRoots_some_eq_of_lt
          reward roots deadline time htime who
      · rw [quittingBehaviorStoppingLaw_truncatedRootProfile_some_eq_zero_of_le
          reward roots deadline who (Nat.le_of_not_gt htime)]
        symm
        by_contra hne
        have hmem := (PMF.mem_support_iff _ _).mpr hne
        have hsupport := censorLateFiniteStoppingLaw_support_subset
          (quittingBehaviorStoppingLaw reward (quittingRootSequenceProfile reward roots 0 who))
          (deadline - 1) hmem
        have : time ≤ deadline - 1 := by simpa using hsupport
        omega

omit [DecidableEq ι] in
/-- The Never atom of a finite root word is exactly its own survival through the cut. -/
theorem quittingBehaviorStoppingLaw_truncatedRoots_none_toReal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (deadline : ℕ) (hdeadline : 0 < deadline) (who : ι) :
    (quittingBehaviorStoppingLaw reward
        (quittingRootSequenceProfile reward (quittingTruncatedRoots roots deadline) 0 who)
        none).toReal =
      ∏ time ∈ Finset.range deadline, (roots time who false).toReal := by
  let law := quittingBehaviorStoppingLaw reward
    (quittingRootSequenceProfile reward (quittingTruncatedRoots roots deadline) 0 who)
  have hsupport : law.support ⊆ ↑(stoppingLawFinitePrefix (deadline - 1)) := by
    rw [show law = _ from quittingBehaviorStoppingLaw_truncatedRoots_eq_censor
      reward roots deadline hdeadline who]
    exact censorLateFiniteStoppingLaw_support_subset _ _
  have hnever := stoppingLawSurvival_eq_none_of_support_prefix law (deadline - 1) deadline
    (by omega) hsupport
  rw [← hnever, stoppingLawSurvival_quittingBehaviorStoppingLaw,
    quittingHazardSurvival_eq_prod]
  apply Finset.prod_congr rfl
  intro time htime
  simp only [quittingBehaviorLiveHazard, quittingRootSequenceProfile, Nat.zero_add]
  rw [quittingTruncatedRoots_of_lt roots (Finset.mem_range.mp htime)]

end GameTheory
