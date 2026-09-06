import MathUE.ProbabilityMassFunction.IndicatorExpectation
import UniformEquilibrium.Diagnostics.Quitting.PivotRepairNonattainedZeroLP
import UniformEquilibrium.Quitting.Terminal.StoppingLawExploitability
import UniformEquilibrium.Quitting.Terminal.PivotRepairBehavioralInfimum

/-! # Strict nonattainment of the zero repair optimum by every pivot strategy -/

noncomputable section

namespace GameTheory.PivotRepairNonattainedAllLaws

open PivotRepairNonattainedZeroLP
open _root_.Math.Probability

private theorem allNeverPayoff (observer : Fin 4) :
    quittingTerminalPayoff reward (quittingStoppingLawProfile reward opponents) observer = 0 := by
  simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingStoppingLawExpectedPayoff]
  rw [show quittingIndependentTerminalOutcomeLaw opponents = PMF.pure none by
    unfold quittingIndependentTerminalOutcomeLaw
    rw [show opponents = fun _ : Fin 4 ↦ PMF.pure none by rfl,
      Math.PMFProduct.pmfPi_pure, PMF.pure_map]
    congr 1]
  simp [quittingTerminalOutcomeReward]

private theorem purePivotPayoff (time : ℕ) :
    quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward
        (Function.update opponents 0 (PMF.pure (some time)))) 0 = 1 := by
  rw [quittingTerminalPayoff_stoppingLawProfile_late_pure_eq_never_add
    reward opponents 0 0]
  · have hup : Function.update opponents 0 (PMF.pure none) = opponents := by
      funext player
      simp [opponents, Function.update_apply]
    rw [hup, allNeverPayoff]
    norm_num [opponents, reward, quittingSingletonTerminal]
  · intro j hj choice hchoice
    left
    simpa [opponents, PMF.pure_apply] using hchoice
  · omega

/-- Against the fixed all-Never opponents, the pivot receives exactly its
finite stopping mass. -/
theorem pivotPayoff_eq_one_sub_never (law : PMF (Option ℕ)) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update opponents 0 law)) 0 = 1 - (law none).toReal := by
  rw [quittingTerminalPayoff_stoppingLawProfile_update_eq_expect]
  have hpoint : (fun choice : Option ℕ ↦
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update opponents 0 (PMF.pure choice))) 0) =
      fun choice ↦ if choice = none then 0 else 1 := by
    funext choice
    cases choice with
    | none =>
        have hup : Function.update opponents 0 (PMF.pure none) = opponents := by
          funext player
          simp [opponents, Function.update_apply]
        rw [hup, allNeverPayoff]
        simp
    | some time => simp [purePivotPayoff time]
  rw [hpoint, expect_complementSingletonIndicator]

private theorem pureMatchingPayoff (time : ℕ) (choice : Option ℕ) :
    quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward
        (Function.update (Function.update opponents 0 (PMF.pure choice)) 1
          (PMF.pure (some time)))) 1 = if choice = some time then 1 else 0 := by
  cases choice with
  | none =>
      rw [show Function.update opponents 0 (PMF.pure none) = opponents by
        funext player
        simp [opponents, Function.update_apply]]
      rw [quittingTerminalPayoff_stoppingLawProfile_late_pure_eq_never_add
        reward opponents 1 0]
      · rw [show Function.update opponents 1 (PMF.pure none) = opponents by
          funext player
          simp [opponents, Function.update_apply]]
        rw [allNeverPayoff]
        simp [opponents, reward, quittingSingletonTerminal]
      · intro j hj other hother
        left
        simpa [opponents, PMF.pure_apply] using hother
      · omega
  | some chosen =>
      by_cases heq : chosen = time
      · subst chosen
        rw [quittingTerminalPayoff_stoppingLawProfile_late_pair_eq_never_add
          reward opponents 0 1 1 (by norm_num) 0 time (by omega)]
        · rw [allNeverPayoff]
          norm_num [opponents, reward]
        · rfl
        · rfl
        · intro j hj0 hj1 other hother
          left
          simpa [opponents, PMF.pure_apply] using hother
      · by_cases horder : chosen < time
        · rw [quittingTerminalPayoff_stoppingLawProfile_ordered_late_pair_eq_never_add
            reward opponents 0 1 1 (by norm_num) 0 chosen time (by omega) horder]
          · rw [allNeverPayoff]
            simp [opponents, reward, quittingSingletonTerminal, heq]
          · rfl
          · rfl
          · intro j hj0 hj1 other hother
            left
            simpa [opponents, PMF.pure_apply] using hother
        · have hreverse : time < chosen :=
            lt_of_le_of_ne (Nat.le_of_not_gt horder) (Ne.symm heq)
          have hcomm :
              Function.update (Function.update opponents 0 (PMF.pure (some chosen))) 1
                  (PMF.pure (some time)) =
                Function.update (Function.update opponents 1 (PMF.pure (some time))) 0
                  (PMF.pure (some chosen)) := Function.update_comm (by norm_num) _ _ _
          rw [hcomm,
            quittingTerminalPayoff_stoppingLawProfile_ordered_late_pair_eq_never_add
              reward opponents 1 0 1 (by norm_num) 0 time chosen (by omega) hreverse]
          · rw [allNeverPayoff]
            simp [opponents, reward, quittingSingletonTerminal, heq]
          · rfl
          · rfl
          · intro j hj1 hj0 other hother
            left
            simpa [opponents, PMF.pure_apply] using hother

/-- Matching a finite pivot atom gives player 1 exactly that atom's mass. -/
theorem matchingPayoff_eq_atom (law : PMF (Option ℕ)) (time : ℕ) :
    quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward
        (Function.update (Function.update opponents 0 law) 1
          (PMF.pure (some time)))) 1 = (law (some time)).toReal := by
  have hcomm :
      Function.update (Function.update opponents 0 law) 1 (PMF.pure (some time)) =
        Function.update (Function.update opponents 1 (PMF.pure (some time))) 0 law :=
    Function.update_comm (by norm_num) _ _ _
  rw [hcomm, quittingTerminalPayoff_stoppingLawProfile_update_eq_expect]
  have hpoint : (fun choice : Option ℕ ↦
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (Function.update opponents 1 (PMF.pure (some time))) 0
            (PMF.pure choice))) 1) =
      fun choice ↦ if choice = some time then 1 else 0 := by
    funext choice
    rw [show Function.update (Function.update opponents 1 (PMF.pure (some time))) 0
        (PMF.pure choice) =
      Function.update (Function.update opponents 0 (PMF.pure choice)) 1
        (PMF.pure (some time)) by exact Function.update_comm (by norm_num) _ _ _]
    exact pureMatchingPayoff time choice
  rw [hpoint, expect_singletonIndicator]

private theorem playerOnePayoff_eq_zero (law : PMF (Option ℕ)) :
    quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward (Function.update opponents 0 law)) 1 = 0 := by
  rw [quittingTerminalPayoff_stoppingLawProfile_update_eq_expect]
  have hpoint : (fun choice : Option ℕ ↦
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update opponents 0 (PMF.pure choice))) 1) = fun _ ↦ 0 := by
    funext choice
    cases choice with
    | none =>
        rw [show Function.update opponents 0 (PMF.pure none) = opponents by
          funext player
          simp [opponents, Function.update_apply], allNeverPayoff]
    | some time =>
        rw [quittingTerminalPayoff_stoppingLawProfile_late_pure_observer_eq_never_add
          reward opponents 0 1 0]
        · rw [show Function.update opponents 0 (PMF.pure none) = opponents by
            funext player
            simp [opponents, Function.update_apply], allNeverPayoff]
          norm_num [opponents, reward, quittingSingletonTerminal]
        · intro j hj other hother
          left
          simpa [opponents, PMF.pure_apply] using hother
        · omega
  rw [hpoint, expect_const]

/-- No complete pivot stopping law against the fixed actual opponents attains
the zero exploitability infimum. -/
theorem stoppingLawProfile_exploitability_pos (law : PMF (Option ℕ)) :
    0 < quittingTerminalExploitability reward
      (quittingStoppingLawProfile reward (Function.update opponents 0 law)) := by
  let profile := quittingStoppingLawProfile reward (Function.update opponents 0 law)
  change 0 < quittingTerminalExploitability reward profile
  by_cases hnever : law none = 0
  · obtain ⟨choice, hchoice⟩ := law.support_nonempty
    have hchoicePos : 0 < law choice := (law.apply_pos_iff choice).2 hchoice
    cases choice with
    | none =>
        rw [hnever] at hchoicePos
        exact (lt_irrefl _ hchoicePos).elim
    | some time =>
        have hatom : 0 < (law (some time)).toReal :=
          ENNReal.toReal_pos (ne_of_gt hchoicePos) (PMF.apply_ne_top law _)
        have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
          reward profile 1 (quittingPureTimeBehaviorStrategy reward 1 (some time))
        rw [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq] at hbest
        have hupdate : Function.update (Function.update opponents 0 law) 1
            (PMF.pure (some time)) =
            Function.update (Function.update opponents 0 law) 1
              (PMF.pure (some time)) := rfl
        rw [hupdate, matchingPayoff_eq_atom] at hbest
        have hdebt := quittingTerminalDeviationDebt_le_exploitability reward profile 1
        unfold quittingTerminalDeviationDebt at hdebt
        rw [show quittingTerminalPayoff reward profile 1 = 0 by
          exact playerOnePayoff_eq_zero law] at hdebt
        linarith
  · have hneverPos : 0 < (law none).toReal :=
      ENNReal.toReal_pos hnever (PMF.apply_ne_top law _)
    have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile 0 (quittingPureTimeBehaviorStrategy reward 0 (some 0))
    rw [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq] at hbest
    have hoverwrite : Function.update (Function.update opponents 0 law) 0
        (PMF.pure (some 0)) = Function.update opponents 0 (PMF.pure (some 0)) := by
      funext player
      by_cases hp : player = 0 <;> simp [hp]
    rw [hoverwrite, purePivotPayoff] at hbest
    have hdebt := quittingTerminalDeviationDebt_le_exploitability reward profile 0
    unfold quittingTerminalDeviationDebt at hdebt
    rw [show quittingTerminalPayoff reward profile 0 = 1 - (law none).toReal by
      exact pivotPayoff_eq_one_sub_never law] at hdebt
    linarith

/-- Canonicalization transfers strict nonattainment to every behavioral pivot
strategy against the fixed actual all-Never opponents. -/
theorem pivotBehavior_exploitability_pos
    (strategy : (quittingGame reward).BehaviorStrategy 0) :
    0 < quittingTerminalExploitability reward
      (Function.update (quittingStoppingLawProfile reward opponents) 0 strategy) := by
  let profile := Function.update (quittingStoppingLawProfile reward opponents) 0 strategy
  let law := quittingBehaviorStoppingLaw reward strategy
  have hlaws : quittingBehaviorStoppingLaws reward profile =
      Function.update opponents 0 law := by
    unfold profile law
    rw [quittingBehaviorStoppingLaws_update,
      quittingBehaviorStoppingLaws_stoppingLawProfile]
  have hpos := stoppingLawProfile_exploitability_pos law
  rw [← hlaws] at hpos
  rw [quittingTerminalExploitability_stoppingLawProfile_behaviorLaws_eq] at hpos
  exact hpos

/-- The greatest lower bound over all actual pivot behaviors is the zero
finite-LP boundary value. -/
theorem behavioral_repair_infimum_eq_zero :
    sInf (Set.range (fun strategy : (quittingGame reward).BehaviorStrategy 0 ↦
      quittingTerminalExploitability reward
        (Function.update (quittingStoppingLawProfile reward opponents) 0 strategy))) = 0 := by
  have hfixture := zeroBoundaryMass_is_zero_minimizer
  have hmin : IsMinOn input.objective
      (Math.LinearProgramming.pivotRepairMassFeasibleSet input.deadline)
      zeroBoundaryMass := by
    intro mass hmass
    exact hfixture.2 mass hmass
  have hglb := input.isGLB_pivotLaw_exploitability_of_objective_minimizer
    zeroBoundaryMass zeroBoundaryMass_feasible hmin
  change sInf (Set.range (fun strategy :
      (quittingGame reward).BehaviorStrategy input.pivot ↦
    quittingTerminalExploitability reward
      (Function.update (quittingStoppingLawProfile reward input.opponents)
        input.pivot strategy))) = 0
  rw [input.range_pivotBehavior_exploitability_eq_range_stoppingLaw] at ⊢
  calc
    sInf (Set.range (fun law : PMF (Option ℕ) ↦
        quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward
            (Function.update input.opponents input.pivot law)))) =
        input.objective zeroBoundaryMass :=
      hglb.csInf_eq (Set.range_nonempty _)
    _ = 0 := hfixture.1

/-- The behavioral repair infimum is zero and is attained by no pivot
behavior strategy. -/
theorem behavioral_repair_infimum_zero_not_attained :
    ∀ strategy : (quittingGame reward).BehaviorStrategy 0,
      quittingTerminalExploitability reward
          (Function.update (quittingStoppingLawProfile reward opponents) 0 strategy) ≠
        sInf (Set.range (fun deviation : (quittingGame reward).BehaviorStrategy 0 ↦
          quittingTerminalExploitability reward
            (Function.update (quittingStoppingLawProfile reward opponents) 0 deviation))) := by
  intro strategy hzero
  rw [behavioral_repair_infimum_eq_zero] at hzero
  have hpos := pivotBehavior_exploitability_pos strategy
  linarith

end GameTheory.PivotRepairNonattainedAllLaws
