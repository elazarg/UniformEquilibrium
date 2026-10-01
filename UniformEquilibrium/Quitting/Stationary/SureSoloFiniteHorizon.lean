import UniformEquilibrium.Quitting.Paths.FiniteHorizonPureTimeCap
import UniformEquilibrium.Quitting.Punishment.InstantPunishment

/-! # The same nonnegative sure-solo stationary profile is Nash at every horizon

The prescribed root is literally sure owner and all Continue opponents.
Its actual stopping laws are date zero for the owner and Never otherwise.
The owner nonnegativity premise is essential. This module makes no stationary
claim for the signed sole-owner punishment branch.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] (owner : ι)

/-- The actual complete clock tuple of the stationary sure-solo root. -/
def quittingSureSoloClocks : ι → Option ℕ :=
  fun who => if who = owner then some 0 else none

/-- Actual laws of the unchanged stationary profile, including Never atoms. -/
theorem quittingBehaviorStoppingLaws_sureSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingBehaviorStoppingLaws reward
        (quittingStationaryProfile reward (quittingInstantRoot owner)) =
      fun who => PMF.pure (quittingSureSoloClocks owner who) := by
  funext who
  by_cases hwho : who = owner
  · subst who
    have hmass :
        quittingBehaviorStoppingLaw reward
            (quittingStationaryProfile reward (quittingInstantRoot owner) owner)
            (some 0) = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff'
        (PMF.apply_ne_top _ _) ENNReal.one_ne_top).mp
      rw [quittingBehaviorStoppingLaw_some_toReal,
        quittingHazardStopMass_eq_survival_mul_stop, quittingHazardSurvival_zero, one_mul]
      change (quittingInstantRoot owner owner true).toReal = (1 : ENNReal).toReal
      simp [quittingInstantRoot, quittingSoloStationaryRoot]
    have hpure :
        quittingBehaviorStoppingLaw reward
          (quittingStationaryProfile reward (quittingInstantRoot owner) owner) =
          PMF.pure (some 0) := by
      by_contra hnot
      obtain ⟨choice, hchoice, hpositive⟩ := exists_ne_of_ne_pure _ hnot
      have hsupport := (PMF.apply_eq_one_iff _ (some 0)).mp hmass
      have hmem := (PMF.mem_support_iff _ choice).mpr hpositive
      rw [hsupport] at hmem
      exact hchoice (Set.mem_singleton_iff.mp hmem)
    simpa only [quittingBehaviorStoppingLaws, quittingSureSoloClocks,
      ite_eq_left rfl, ite_true] using hpure
  · have hstrategy :
        quittingStationaryProfile reward (quittingInstantRoot owner) who =
          quittingPureTimeBehaviorStrategy reward who none := by
      funext time history
      change quittingInstantRoot owner who = PMF.pure false
      simp only [quittingInstantRoot, quittingSoloStationaryRoot, Function.update_of_ne hwho]
    change quittingBehaviorStoppingLaw reward
      (quittingStationaryProfile reward (quittingInstantRoot owner) who) = _
    rw [hstrategy, quittingBehaviorStoppingLaw_pureTime_never]
    simp only [quittingSureSoloClocks, ite_eq_right hwho]

omit [Fintype ι] in
private theorem sureSolo_owner_event (time : ℕ) :
    QuittingClockFirstEvent time (quittingSingletonTerminal owner)
      (Function.update (quittingSureSoloClocks owner) owner (some time)) := by
  intro who
  by_cases hwho : who = owner
  · subst who
    simp [quittingSingletonTerminal]
  · simp [quittingSingletonTerminal, quittingSureSoloClocks, hwho]

omit [Fintype ι] in
private theorem sureSolo_other_event
    (who : ι) (hwho : who ≠ owner) (choice : Option ℕ) (hchoice : choice ≠ some 0) :
    QuittingClockFirstEvent 0 (quittingSingletonTerminal owner)
      (Function.update (quittingSureSoloClocks owner) who choice) := by
  intro player
  by_cases howner : player = owner
  · subst player
    simp [quittingSingletonTerminal, hwho.symm, quittingSureSoloClocks]
  · by_cases hplayer : player = who
    · subst player
      simpa [quittingSingletonTerminal, howner,
        Finset.range_one] using hchoice
    · simp [quittingSingletonTerminal, howner, hplayer, quittingSureSoloClocks]

omit [Fintype ι] in
private theorem sureSolo_join_event (who : ι) (hwho : who ≠ owner) :
    QuittingClockFirstEvent 0
        ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩
      (Function.update (quittingSureSoloClocks owner) who (some 0)) := by
  intro player
  by_cases howner : player = owner
  · subst player
    simp [hwho.symm, quittingSureSoloClocks]
  · by_cases hplayer : player = who
    · subst player
      simp
    · simp [howner, hplayer, quittingSureSoloClocks]

private theorem sureSolo_law_reply_eq_pure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (horizon : ℕ) (who : ι) (choice : Option ℕ) :
    letI : Nonempty ι := ⟨owner⟩
    quittingStoppingLawEvaluatedPayoff reward (quittingFiniteHorizonEvaluation horizon)
        (Function.update (fun player => PMF.pure (quittingSureSoloClocks owner player)) who
          (PMF.pure choice)) who =
      quittingPureClockEvaluatedPayoff reward (quittingFiniteHorizonEvaluation horizon)
        (Function.update (quittingSureSoloClocks owner) who choice) who := by
  let : Nonempty ι := ⟨owner⟩
  have hupdate :
      Function.update (fun player => PMF.pure (quittingSureSoloClocks owner player)) who
          (PMF.pure choice) =
        fun player => PMF.pure (Function.update (quittingSureSoloClocks owner) who choice player) :=
    by funext player; by_cases heq : player = who <;> simp [heq]
  rw [hupdate, quittingStoppingLawEvaluatedPayoff, pmfPi_pure, expect_pure]

/-- Every owner date or Never is priced with its actual absorption-date weight. -/
theorem quittingSureSolo_owner_pureTime_horizon_reply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (horizon : ℕ) (choice : Option ℕ) :
    letI : Nonempty ι := ⟨owner⟩
    quittingStoppingLawEvaluatedPayoff reward (quittingFiniteHorizonEvaluation horizon)
        (Function.update (fun player => PMF.pure (quittingSureSoloClocks owner player)) owner
          (PMF.pure choice)) owner =
      match choice with
      | none => 0
      | some time => (horizon - time - 1 : ℕ) / (horizon : ℝ) *
          quittingSoloReward reward owner owner := by
  let : Nonempty ι := ⟨owner⟩
  rw [sureSolo_law_reply_eq_pure]
  cases choice with
  | none =>
      have hall :
          Function.update (quittingSureSoloClocks owner) owner none = fun _ => none := by
        funext who
        by_cases hwho : who = owner <;> simp [quittingSureSoloClocks, hwho]
      simp only [hall, quittingPureClockEvaluatedPayoff, quittingFirstStoppingOutcome_all_never]
  | some time =>
      obtain ⟨hearliest, hfirst⟩ := (quittingClockFirstEvent_iff time
        (quittingSingletonTerminal owner) _).mp (sureSolo_owner_event owner time)
      simp only [quittingPureClockEvaluatedPayoff, hfirst, hearliest,
        quittingFiniteHorizonEvaluation_coe, quittingSoloReward, quittingSingletonTerminal]

/-- An outsider either joins at zero or faces the owner's singleton at zero.
Its own later clock and Never are genuinely retained. -/
theorem quittingSureSolo_other_pureTime_horizon_reply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (horizon : ℕ) (who : ι) (hwho : who ≠ owner) (choice : Option ℕ) :
    letI : Nonempty ι := ⟨owner⟩
    quittingStoppingLawEvaluatedPayoff reward (quittingFiniteHorizonEvaluation horizon)
        (Function.update (fun player => PMF.pure (quittingSureSoloClocks owner player)) who
          (PMF.pure choice)) who =
      (horizon - 1 : ℕ) / (horizon : ℝ) *
        if choice = some 0 then quittingSingletonCollisionReward reward owner who
        else quittingSoloReward reward owner who := by
  let : Nonempty ι := ⟨owner⟩
  rw [sureSolo_law_reply_eq_pure]
  by_cases hchoice : choice = some 0
  · subst choice
    obtain ⟨hearliest, hfirst⟩ := (quittingClockFirstEvent_iff 0
      ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ _).mp
        (sureSolo_join_event owner who hwho)
    simp only [quittingPureClockEvaluatedPayoff, hfirst, hearliest,
      quittingFiniteHorizonEvaluation_coe, Nat.sub_zero, ite_true,
      quittingSingletonCollisionReward]
  · obtain ⟨hearliest, hfirst⟩ := (quittingClockFirstEvent_iff 0
      (quittingSingletonTerminal owner) _).mp (sureSolo_other_event owner who hwho choice hchoice)
    simp only [quittingPureClockEvaluatedPayoff, hfirst, hearliest,
      quittingFiniteHorizonEvaluation_coe, Nat.sub_zero, ite_eq_right hchoice,
      quittingSoloReward, quittingSingletonTerminal]

/-- The same stationary profile has its literal singleton payoff, multiplied
by its exact paid-stage fraction. This includes the zero horizon. -/
theorem quittingFiniteAveragePayoff_sureSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (horizon : ℕ) (who : ι) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (quittingStationaryProfile reward (quittingInstantRoot owner)) who =
      (horizon - 1 : ℕ) / (horizon : ℝ) * quittingSoloReward reward owner who := by
  let : Nonempty ι := ⟨owner⟩
  rw [quittingFiniteAveragePayoff_eq_stoppingLawEvaluatedPayoff,
    quittingBehaviorStoppingLaws_sureSolo, quittingStoppingLawEvaluatedPayoff,
    pmfPi_pure, expect_pure]
  have hself :
      Function.update (quittingSureSoloClocks owner) owner (some 0) =
        quittingSureSoloClocks owner := by
    funext player
    by_cases hplayer : player = owner <;> simp [quittingSureSoloClocks, hplayer]
  have hevent := sureSolo_owner_event owner 0
  rw [hself] at hevent
  obtain ⟨hearliest, hfirst⟩ := (quittingClockFirstEvent_iff 0
    (quittingSingletonTerminal owner) _).mp hevent
  simp only [quittingPureClockEvaluatedPayoff, hfirst, hearliest,
    quittingFiniteHorizonEvaluation_coe, Nat.sub_zero, quittingSoloReward,
    quittingSingletonTerminal]

/-- Exact full behavioral caps equal prescribed payoff at every finite horizon.
Only the owner singleton is assumed nonnegative; other reward rows stay signed. -/
theorem quittingFiniteHorizonDeviationCap_sureSolo_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (howner : 0 ≤ quittingSoloReward reward owner owner)
    (hnoJoin : IsQuittingInstantNoJoin reward owner) (horizon : ℕ) (who : ι) :
    quittingFiniteHorizonDeviationCap reward
        (quittingStationaryProfile reward (quittingInstantRoot owner)) horizon who =
      (quittingGame reward).finiteAveragePayoff none horizon
        (quittingStationaryProfile reward (quittingInstantRoot owner)) who := by
  let : Nonempty ι := ⟨owner⟩
  apply le_antisymm
  · rw [quittingFiniteHorizonDeviationCap_eq_pureTime, quittingBehaviorStoppingLaws_sureSolo,
      quittingFiniteAveragePayoff_sureSolo]
    apply csSup_le
    · exact ⟨_, ⟨none, rfl⟩⟩
    · rintro _ ⟨choice, rfl⟩
      change quittingStoppingLawEvaluatedPayoff reward (quittingFiniteHorizonEvaluation horizon)
        (Function.update (fun player => PMF.pure (quittingSureSoloClocks owner player)) who
          (PMF.pure choice)) who ≤
        (horizon - 1 : ℕ) / (horizon : ℝ) * quittingSoloReward reward owner who
      by_cases hwho : who = owner
      · subst who
        rw [quittingSureSolo_owner_pureTime_horizon_reply]
        cases choice with
        | none =>
            exact mul_nonneg
              (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) howner
        | some time =>
            apply mul_le_mul_of_nonneg_right _ howner
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            exact_mod_cast Nat.sub_le_sub_right (Nat.sub_le horizon time) 1
      · rw [quittingSureSolo_other_pureTime_horizon_reply owner reward horizon who hwho]
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        split_ifs
        · exact hnoJoin who hwho
        · exact le_rfl
  · have hprescribed := quittingFiniteAveragePayoff_update_le_deviationCap reward
      (quittingStationaryProfile reward (quittingInstantRoot owner)) horizon who
      (quittingStationaryProfile reward (quittingInstantRoot owner) who)
    simpa only [Function.update_eq_self] using hprescribed

/-- No unilateral complete behavioral replacement improves the SAME stationary
profile at any finite horizon; no contracting deleted clock is required. -/
theorem quittingFiniteAveragePayoff_update_sureSolo_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (howner : 0 ≤ quittingSoloReward reward owner owner)
    (hnoJoin : IsQuittingInstantNoJoin reward owner) (horizon : ℕ) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (quittingStationaryProfile reward (quittingInstantRoot owner))
          who deviation) who ≤
      (quittingGame reward).finiteAveragePayoff none horizon
        (quittingStationaryProfile reward (quittingInstantRoot owner)) who := by
  have hcap := quittingFiniteAveragePayoff_update_le_deviationCap reward
    (quittingStationaryProfile reward (quittingInstantRoot owner)) horizon who deviation
  rw [quittingFiniteHorizonDeviationCap_sureSolo_eq owner reward howner hnoJoin] at hcap
  exact hcap

/-- Actual payoff delivery of this fixed stationary profile is bounded by M/H.
No sign assumption is needed for the delivery calculation itself. -/
theorem abs_quittingFiniteAveragePayoff_sureSolo_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (horizon : ℕ) (hhorizon : 0 < horizon) (bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) (who : ι) :
    |(quittingGame reward).finiteAveragePayoff none horizon
          (quittingStationaryProfile reward (quittingInstantRoot owner)) who -
        quittingSoloReward reward owner who| ≤ bound / (horizon : ℝ) := by
  rw [quittingFiniteAveragePayoff_sureSolo]
  have hhorizonReal : (horizon : ℝ) ≠ 0 := by exact_mod_cast hhorizon.ne'
  have hfactor : (horizon - 1 : ℕ) / (horizon : ℝ) - 1 = -(horizon : ℝ)⁻¹ := by
    rw [Nat.cast_sub (by omega : 1 ≤ horizon), Nat.cast_one]
    field_simp [hhorizonReal]; ring
  rw [show (horizon - 1 : ℕ) / (horizon : ℝ) * quittingSoloReward reward owner who -
      quittingSoloReward reward owner who =
      ((horizon - 1 : ℕ) / (horizon : ℝ) - 1) * quittingSoloReward reward owner who by ring,
    hfactor, abs_mul, abs_neg, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg horizon))]
  have hbound := mul_le_mul_of_nonneg_left
    (hreward (quittingSingletonTerminal owner) who)
    (inv_nonneg.mpr (Nat.cast_nonneg horizon) : 0 ≤ (horizon : ℝ)⁻¹)
  simpa only [quittingSoloReward, quittingSingletonTerminal, div_eq_mul_inv, mul_comm]
    using hbound

end GameTheory
