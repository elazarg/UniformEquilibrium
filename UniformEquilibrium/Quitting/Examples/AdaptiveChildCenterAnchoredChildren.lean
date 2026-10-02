import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterAdjacentMenu

/-! # The three actual children retaining the anchor -/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open Filter Topology
open _root_.Math.Probability _root_.Math.Probability.DiscreteHazard.StoppingLaw

def anchoredChildObserver : Fin 3 → Fin 3 := ![0, 1, 0]
def anchoredChildAmbient : Fin 3 → Fin 3 := ![1, 2, 0]
def anchoredChildSign (deleted : Fin 3) : ℝ := if deleted = 2 then 1 else -1
def anchoredChildReplyChoice (deleted : Fin 3) : Option ℕ :=
  if deleted = 2 then some 0 else none
def anchoredChildReplyValue (deleted : Fin 3) : ℝ := if deleted = 2 then 1 else 0

theorem anchoredChildObserver_embedding (deleted : Fin 3) :
    childEmbedding deleted.castSucc (anchoredChildObserver deleted) =
      (anchoredChildAmbient deleted).castSucc := by
  fin_cases deleted <;> rfl

theorem activePayoff_deleted_row (q : Fin 3 → ℝ) (deleted : Fin 3) :
    activePayoff (Function.update q deleted 0) (anchoredChildAmbient deleted) =
      anchoredChildSign deleted * q (anchoredChildAmbient deleted) := by
  fin_cases deleted <;>
    simp [activePayoff, anchoredChildAmbient, anchoredChildSign]

private theorem beforeMass_nonneg (law : PMF (Option ℕ)) (cutoff : ℕ) :
    0 ≤ 1 - survival law cutoff := by
  rw [← sum_finiteMass_range_eq_one_sub_survival]
  exact Finset.sum_nonneg fun time _ => finiteMass_nonneg law time

private theorem prescribed_law_quantile_estimate
    (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff)
    {accuracy : ℝ} (hbefore : ∀ active : Fin 3,
      1 - survival (laws active.castSucc) cutoff ≤ accuracy)
    (htail : survival (laws 3) (cutoff + 1) ≤ accuracy) (active : Fin 3) :
    |quittingStoppingLawExpectedPayoff reward laws active.castSucc -
        finiteMass (laws 3) cutoff * activePayoff (conditionalProbabilities laws cutoff) active|
      ≤ 14 * accuracy := by
  have hestimate := actual_prescribed_payoff_estimate
    (quittingStoppingLawProfile reward laws) cutoff
    (by simpa only [quittingBehaviorStoppingLaws_stoppingLawProfile] using hpositive)
    (by simpa only [quittingBehaviorStoppingLaws_stoppingLawProfile] using hbefore)
    (by simpa only [quittingBehaviorStoppingLaws_stoppingLawProfile] using htail) active
  rw [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff] at hestimate
  simpa only [quittingBehaviorStoppingLaws_stoppingLawProfile] using hestimate

theorem conditionalProbabilities_delete_never (laws : Fin 4 → PMF (Option ℕ))
    (cutoff : ℕ) (deleted : Fin 3) :
    conditionalProbabilities (Function.update laws deleted.castSucc (PMF.pure none)) cutoff =
      Function.update (conditionalProbabilities laws cutoff) deleted 0 := by
  funext active
  by_cases heq : active = deleted
  · subst active
    simp [conditionalProbabilities, finiteMass]
  · have hcast : active.castSucc ≠ deleted.castSucc := by simpa using heq
    simp only [conditionalProbabilities, Function.update_of_ne heq,
      Function.update_of_ne hcast]

/-- The child estimate is a direct use of the actual parent row estimate
on the canonical Never lift, whose surviving laws are literally unchanged. -/
theorem actual_anchored_child_payoff_estimate
    (parent : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) (deleted : Fin 3)
    (hpositive : ∀ active : Fin 3,
      0 < survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff)
    {accuracy : ℝ} (hbefore : ∀ active : Fin 3,
      1 - survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff ≤ accuracy)
    (htail : survival (quittingBehaviorStoppingLaws reward parent 3) (cutoff + 1) ≤ accuracy) :
    |quittingTerminalPayoff (childReward deleted.castSucc)
          (restrictedProfileOfParent deleted.castSucc parent) (anchoredChildObserver deleted) -
        finiteMass (quittingBehaviorStoppingLaws reward parent 3) cutoff *
          (anchoredChildSign deleted * conditionalProbabilities
            (quittingBehaviorStoppingLaws reward parent) cutoff (anchoredChildAmbient deleted))|
      ≤ 14 * accuracy := by
  let laws := quittingBehaviorStoppingLaws reward parent
  let lifted := Function.update laws deleted.castSucc (PMF.pure none)
  have haccuracy : 0 ≤ accuracy := (beforeMass_nonneg (laws 0) cutoff).trans (hbefore 0)
  have hpositiveLift : ∀ active : Fin 3, 0 < survival (lifted active.castSucc) cutoff := by
    intro active
    by_cases heq : active = deleted
    · subst active
      simp [lifted, survival, finiteMass]
    · have hcast : active.castSucc ≠ deleted.castSucc := by simpa using heq
      simpa only [lifted, Function.update_of_ne hcast] using hpositive active
  have hbeforeLift : ∀ active : Fin 3,
      1 - survival (lifted active.castSucc) cutoff ≤ accuracy := by
    intro active
    by_cases heq : active = deleted
    · subst active
      simpa [lifted, survival, finiteMass] using haccuracy
    · have hcast : active.castSucc ≠ deleted.castSucc := by simpa using heq
      simpa only [lifted, Function.update_of_ne hcast] using hbefore active
  have hanchor : lifted 3 = laws 3 := by
    simp only [lifted, Function.update_of_ne (Ne.symm (active_ne_anchor deleted))]
  have hestimate := prescribed_law_quantile_estimate lifted cutoff hpositiveLift
    hbeforeLift (by simpa only [hanchor] using htail) (anchoredChildAmbient deleted)
  rw [restrictedProfileOfParent_payoff_eq_never_lift, anchoredChildObserver_embedding]
  rw [hanchor, conditionalProbabilities_delete_never, activePayoff_deleted_row] at hestimate
  exact hestimate

theorem tendsto_actual_anchored_child_payoff
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (herror : Tendsto (fun index => quittingTerminalExploitability reward (profiles index))
      atTop (nhds 0)) (deleted : Fin 3) :
    Tendsto (fun index => quittingTerminalPayoff (childReward deleted.castSucc)
      (restrictedProfileOfParent deleted.castSucc (profiles index)) (anchoredChildObserver deleted))
      atTop (nhds (anchoredChildSign deleted * (1 / 2))) := by
  obtain ⟨cutoff, hsource, hp, hq, _⟩ := exists_actual_quantile_rigidity profiles herror
  let row := fun index => finiteMass (quittingBehaviorStoppingLaws reward (profiles index) 3)
    (cutoff index) * (anchoredChildSign deleted * conditionalProbabilities
      (quittingBehaviorStoppingLaws reward (profiles index)) (cutoff index)
        (anchoredChildAmbient deleted))
  have hrow : Tendsto row atTop (nhds (anchoredChildSign deleted * (1 / 2))) := by
    simpa only [one_mul] using
      hp.mul ((tendsto_pi_nhds.mp hq (anchoredChildAmbient deleted)).const_mul
        (anchoredChildSign deleted))
  have hclose : Tendsto (fun index =>
      |quittingTerminalPayoff (childReward deleted.castSucc)
          (restrictedProfileOfParent deleted.castSucc (profiles index))
          (anchoredChildObserver deleted) - row index|) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_
      (by simpa only [mul_zero] using (tendsto_quantileAccuracy profiles herror).const_mul 14)
    filter_upwards [hsource] with index hindex
    exact actual_anchored_child_payoff_estimate (profiles index) (cutoff index) deleted
      (fun who => (hindex.2.2.2 who).2.2.2)
      (fun who => (hindex.2.2.2 who).2.1) hindex.2.2.1
  exact hrow.congr_dist (by simpa only [Real.dist_eq, abs_sub_comm] using hclose)

private theorem childClockPayoff_never_selected
    (deleted : Fin 3) (hdeleted : deleted ≠ 2) (times : Fin 3 → Option ℕ)
    (hnever : times (anchoredChildObserver deleted) = none) :
    childClockPayoff deleted.castSucc times (anchoredChildObserver deleted) = 0 := by
  classical
  by_cases htop : quittingEarliestStoppingValue times = ⊤
  · simp [childClockPayoff, quittingFirstStoppingOutcome, htop, quittingTerminalOutcomeReward]
  · have hnot : anchoredChildObserver deleted ∉ quittingEarliestStoppingCoalition times := by
      intro hmem
      have hvalue : quittingStoppingTimeValue (times (anchoredChildObserver deleted)) =
          quittingEarliestStoppingValue times := by
        simpa only [quittingEarliestStoppingCoalition, Finset.mem_filter,
          Finset.mem_univ, true_and] using hmem
      rw [hnever] at hvalue
      exact htop hvalue.symm
    fin_cases deleted
    · change (0 : Fin 3) ∉ quittingEarliestStoppingCoalition times at hnot
      change childClockPayoff 0 times 0 = 0
      simp [childClockPayoff, quittingFirstStoppingOutcome, htop, quittingTerminalOutcomeReward,
        childReward_zero_selected, hnot]
    · change (1 : Fin 3) ∉ quittingEarliestStoppingCoalition times at hnot
      change childClockPayoff 1 times 1 = 0
      simp [childClockPayoff, quittingFirstStoppingOutcome, htop, quittingTerminalOutcomeReward,
        childReward_one_selected, hnot]
    · exact (hdeleted rfl).elim

theorem anchored_child_reply_payoff
    (deleted : Fin 3) (child : (quittingGame (childReward deleted.castSucc)).BehaviorProfile) :
    quittingBehaviorPureTimePayoff (childReward deleted.castSucc) child
      (anchoredChildObserver deleted) (anchoredChildReplyChoice deleted) =
        anchoredChildReplyValue deleted := by
  classical
  rw [quittingBehaviorPureTimePayoff_eq_expect_overwrite]
  have hpointwise : ∀ times : Fin 3 → Option ℕ,
      childClockPayoff deleted.castSucc
        (Function.update times (anchoredChildObserver deleted) (anchoredChildReplyChoice deleted))
        (anchoredChildObserver deleted) = anchoredChildReplyValue deleted := by
    intro times
    by_cases hdeleted : deleted = 2
    · subst deleted
      have hmin : quittingEarliestStoppingValue (Function.update times 0 (some 0)) = 0 := by
        apply le_antisymm
        · exact (Finset.inf_le (Finset.mem_univ (0 : Fin 3))).trans_eq
            (by simp [quittingStoppingTimeValue])
        · exact bot_le
      simp [childClockPayoff, anchoredChildObserver, anchoredChildReplyChoice,
        anchoredChildReplyValue, quittingFirstStoppingOutcome, hmin,
        quittingTerminalOutcomeReward, childReward_two_selected,
        quittingEarliestStoppingCoalition, quittingStoppingTimeValue]
    · exact (childClockPayoff_never_selected deleted hdeleted _
        (by simp [anchoredChildReplyChoice, hdeleted])).trans
        (by simp [anchoredChildReplyValue, hdeleted])
  change expect _ (fun times => childClockPayoff deleted.castSucc
    (Function.update times (anchoredChildObserver deleted) (anchoredChildReplyChoice deleted))
    (anchoredChildObserver deleted)) = _
  simp_rw [hpointwise]
  exact expect_const _ _

theorem eventually_anchored_child_exploitability_lower
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (herror : Tendsto (fun index => quittingTerminalExploitability reward (profiles index))
      atTop (nhds 0)) (deleted : Fin 3) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ index in atTop, 1 / 2 - eta ≤
      quittingTerminalExploitability (childReward deleted.castSucc)
        (restrictedProfileOfParent deleted.castSucc (profiles index)) := by
  have hgain : Tendsto (fun index => anchoredChildReplyValue deleted -
      quittingTerminalPayoff (childReward deleted.castSucc)
        (restrictedProfileOfParent deleted.castSucc (profiles index))
        (anchoredChildObserver deleted))
      atTop (nhds (1 / 2)) := by
    have hlimit := (tendsto_const_nhds (x := anchoredChildReplyValue deleted)).sub
      (tendsto_actual_anchored_child_payoff profiles herror deleted)
    have hvalue :
        anchoredChildReplyValue deleted - anchoredChildSign deleted * (1 / 2) = 1 / 2 := by
      fin_cases deleted <;> norm_num [anchoredChildReplyValue, anchoredChildSign]
    simpa only [hvalue] using hlimit
  have hlower := (tendsto_order.1 hgain).1 (1 / 2 - eta) (sub_lt_self _ heta)
  filter_upwards [hlower] with index hindex
  have hnash := isεAsymptoticNash_of_quittingTerminalExploitability_le
    (restrictedProfileOfParent deleted.castSucc (profiles index)) (le_refl _)
  have hreply := hnash (anchoredChildObserver deleted)
    (quittingPureTimeBehaviorStrategy (childReward deleted.castSucc)
      (anchoredChildObserver deleted) (anchoredChildReplyChoice deleted))
  change quittingBehaviorPureTimePayoff _ _ _ _ ≤ _ at hreply
  rw [anchored_child_reply_payoff] at hreply
  linarith

end GameTheory.AdaptiveChildCenter
