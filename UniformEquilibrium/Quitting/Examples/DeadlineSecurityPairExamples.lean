import UniformEquilibrium.Quitting.Classification.QuietExtension.RationalSecurityHazard
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityEvaluated
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalPerturbation

/-!
# Two literal stationary-security boundaries

The actual child has two players, with a quiet additional outsider represented
by `none`. All unspecified reward coordinates are zero. The first table has
an exact zero evaluated security guarantee strictly above its negative passive
floor. The second has terminal LP value one only at hazard zero: positive
geometric hazards approach but do not attain that value, and Never pays zero
against opponent Never. No nonattainment assertion for all private plans or
positive finite-horizon restart security is made.
-/

noncomputable section

namespace GameTheory.DeadlineSecurityPairExamples

open _root_.Math.Probability

/-- A complete actual reward table on the two-player child and quiet outsider. -/
def pairReward (singleton passive joint : ℝ)
    (terminal : {A : Finset (Option (Fin 2)) // A.Nonempty})
    (who : Option (Fin 2)) : ℝ :=
  if who = some 0 then
    if terminal.1 = {some 0} then singleton
    else if terminal.1 = {some 1} then passive
    else if terminal.1 = {some 0, some 1} then joint else 0
  else 0

private theorem opponentCoalition_eq
    (B : Finset (Fin 2)) (hB : B.Nonempty) (hzero : (0 : Fin 2) ∉ B) : B = {1} := by
  apply hB.subset_singleton_iff.mp
  intro who hwho
  fin_cases who
  · exact False.elim (hzero hwho)
  · exact Finset.mem_singleton_self _

private def opponentRow : {B : Finset (Fin 2) // B.Nonempty ∧ (0 : Fin 2) ∉ B} :=
  ⟨{1}, Finset.singleton_nonempty _, by decide⟩

private theorem pairReward_singleton (singleton passive joint : ℝ) :
    pairReward singleton passive joint ⟨{some 0}, Finset.singleton_nonempty _⟩ (some 0) =
      singleton := by
  simp only [pairReward, ite_true]

private theorem pairReward_passive (singleton passive joint : ℝ) :
    pairReward singleton passive joint
        ⟨cappedClockChildCoalition ({1} : Finset (Fin 2)),
          cappedClockChildCoalition_nonempty (Finset.singleton_nonempty _)⟩ (some 0) =
      passive := by
  have hcoalition : cappedClockChildCoalition ({1} : Finset (Fin 2)) = {some 1} := by
    change ({1} : Finset (Fin 2)).map ⟨some, Option.some_injective _⟩ = {some 1}
    simp only [Finset.map_singleton, Function.Embedding.coeFn_mk]
  norm_num +decide [pairReward, hcoalition]

private theorem pairReward_joint (singleton passive joint : ℝ) :
    pairReward singleton passive joint
        ⟨cappedClockChildCoalition ({0, 1} : Finset (Fin 2)),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty _ _)⟩ (some 0) =
      joint := by
  have hcoalition : cappedClockChildCoalition ({0, 1} : Finset (Fin 2)) =
      {some 0, some 1} := by
    change ({0, 1} : Finset (Fin 2)).map ⟨some, Option.some_injective _⟩ = {some 0, some 1}
    simp only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coeFn_mk]
  norm_num +decide [pairReward, hcoalition]

theorem pairReward_securityRow (singleton passive joint hazard : ℝ)
    (row : Option {B : Finset (Fin 2) // B.Nonempty ∧ (0 : Fin 2) ∉ B}) :
    deadlineWithdrawalSecurityRow (pairReward singleton passive joint) 0 hazard row =
      match row with
      | none => singleton
      | some _ => (1 - hazard) * passive + hazard * joint := by
  cases row with
  | none => exact pairReward_singleton _ _ _
  | some B =>
      have hB := opponentCoalition_eq B.1 B.2.1 B.2.2
      simp only [deadlineWithdrawalSecurityRow, hB,
        pairReward_passive, pairReward_joint]

theorem pairReward_securityFeasible_iff (singleton passive joint hazard value : ℝ) :
    DeadlineWithdrawalSecurityFeasible (pairReward singleton passive joint) 0 hazard value ↔
      hazard ∈ Set.Icc (0 : ℝ) 1 ∧ value ≤ singleton ∧
        value ≤ (1 - hazard) * passive + hazard * joint := by
  constructor
  · rintro ⟨hmem, hrows⟩
    exact ⟨hmem, by simpa only [pairReward_securityRow] using hrows none,
      by simpa only [pairReward_securityRow] using hrows (some opponentRow)⟩
  · rintro ⟨hmem, hsolo, hrow⟩
    refine ⟨hmem, ?_⟩
    intro row
    cases row with
    | none => simpa only [pairReward_securityRow] using hsolo
    | some B => simpa only [pairReward_securityRow] using hrow

theorem pairReward_securityEnvelope (singleton passive joint hazard : ℝ) :
    deadlineWithdrawalSecurityEnvelope (pairReward singleton passive joint) 0 hazard =
      min singleton ((1 - hazard) * passive + hazard * joint) := by
  have hrows := (deadlineWithdrawalSecurity_le_envelope_iff
    (pairReward singleton passive joint) 0 hazard _).mp le_rfl
  apply le_antisymm
  · apply le_min
    · simpa only [pairReward_securityRow] using hrows none
    · simpa only [pairReward_securityRow] using hrows (some opponentRow)
  · apply (deadlineWithdrawalSecurity_le_envelope_iff _ _ _ _).mpr
    intro row
    cases row
    · simpa only [pairReward_securityRow] using
        (min_le_left singleton ((1 - hazard) * passive + hazard * joint))
    · simpa only [pairReward_securityRow] using
        (min_le_right singleton ((1 - hazard) * passive + hazard * joint))

theorem pairReward_zeroFloor (singleton passive joint : ℝ) :
    deadlineWithdrawalZeroFloor (pairReward singleton passive joint) 0 = min 0 passive := by
  apply le_antisymm
  · apply le_min (deadlineWithdrawalZeroFloor_le_zero _ _)
    simpa only [pairReward_passive] using deadlineWithdrawalZeroFloor_le_passiveReward
      (pairReward singleton passive joint) 0 {1} (Finset.singleton_nonempty _) (by decide)
  · apply (le_deadlineWithdrawalZeroFloor_iff _ _ _).mpr
    refine ⟨min_le_left _ _, ?_⟩
    intro B hB hzero
    have hB := opponentCoalition_eq B hB hzero
    subst B
    simpa only [pairReward_passive] using (min_le_right (0 : ℝ) passive)

def zeroSecurityReward := pairReward 0 (-1) 1
def positiveSecurityReward := pairReward 1 1 0

theorem zeroSecurity_envelope (hazard : ℝ) :
    deadlineWithdrawalSecurityEnvelope zeroSecurityReward 0 hazard = min 0 (-1 + 2 * hazard)
    := by
  rw [zeroSecurityReward, pairReward_securityEnvelope]
  congr 1
  ring

theorem zeroSecurity_half_feasible :
    DeadlineWithdrawalSecurityFeasible zeroSecurityReward 0 (1 / 2) 0 := by
  rw [zeroSecurityReward, pairReward_securityFeasible_iff]
  norm_num

theorem zeroSecurity_value_eq_zero : deadlineWithdrawalSecurityValue zeroSecurityReward 0 = 0
    := by
  obtain ⟨_, _, hoptimal⟩ :=
    deadlineWithdrawalSecurityValue_spec zeroSecurityReward 0
  have hlower := hoptimal (1 / 2) 0 zeroSecurity_half_feasible
  have hupper := deadlineWithdrawalSecurityValue_le_singleton zeroSecurityReward 0
  simp only [zeroSecurityReward, pairReward_singleton] at hupper
  exact le_antisymm hupper hlower

theorem zeroSecurity_floor_values :
    deadlineWithdrawalZeroFloor zeroSecurityReward 0 = -1 ∧
      deadlineWithdrawalSecurityFloor zeroSecurityReward 0 = 0 ∧
      min (deadlineWithdrawalSecurityFloor zeroSecurityReward 0) 0 = 0 := by
  have hfloor : deadlineWithdrawalZeroFloor zeroSecurityReward 0 = -1 := by
    norm_num [zeroSecurityReward, pairReward_zeroFloor]
  simp only [deadlineWithdrawalSecurityFloor, hfloor, zeroSecurity_value_eq_zero]
  norm_num

theorem zeroSecurity_evaluated_floor_strict_improvement :
    deadlineWithdrawalZeroFloor zeroSecurityReward 0 <
      min (deadlineWithdrawalSecurityFloor zeroSecurityReward 0) 0 := by
  rw [zeroSecurity_floor_values.1, zeroSecurity_floor_values.2.2]
  norm_num

theorem zeroSecurity_rational_half_optimal :
    DeadlineWithdrawalSecurityFeasible zeroSecurityReward 0 ((1 / 2 : ℚ) : ℝ)
      (deadlineWithdrawalSecurityValue zeroSecurityReward 0) := by
  rw [zeroSecurity_value_eq_zero]
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using zeroSecurity_half_feasible

/-- The literal half-hazard law secures zero for all nonnegative antitone evaluations. -/
theorem zeroSecurity_half_evaluated_guarantee
    (evaluation : WithTop ℕ → ℝ) (hnonneg : ∀ time, 0 ≤ evaluation time)
    (hantitone : Antitone evaluation) (deadline : ℕ)
    (opponents : Fin 2 → Option ℕ) (hown : opponents 0 = none)
    (hfuture : ∀ j, (deadline : WithTop ℕ) < quittingStoppingTimeValue (opponents j)) :
    0 ≤ expect (deadlineWithdrawalSecurityRestartLaw deadline (1 / 2)
      (by norm_num) zeroSecurity_half_feasible.1.2)
      (fun clock => quittingPureClockEvaluatedPayoff zeroSecurityReward evaluation
        (Function.update (quietParentClocks opponents) (some 0) clock) (some 0)) := by
  simpa only [mul_zero] using deadlineWithdrawalSecurityRestartLaw_evaluated_floor
    zeroSecurityReward evaluation hnonneg hantitone 0 (1 / 2) 0 (by norm_num) le_rfl
    zeroSecurity_half_feasible deadline opponents hown hfuture

theorem positiveSecurity_envelope (hazard : ℝ) (hmem : hazard ∈ Set.Icc (0 : ℝ) 1) :
    deadlineWithdrawalSecurityEnvelope positiveSecurityReward 0 hazard = 1 - hazard := by
  rw [positiveSecurityReward, pairReward_securityEnvelope]
  simp only [mul_one, mul_zero, add_zero]
  exact min_eq_right (by linarith [hmem.1])

theorem positiveSecurity_zero_feasible :
    DeadlineWithdrawalSecurityFeasible positiveSecurityReward 0 0 1 := by
  rw [positiveSecurityReward, pairReward_securityFeasible_iff]
  norm_num

theorem positiveSecurity_value_eq_one :
    deadlineWithdrawalSecurityValue positiveSecurityReward 0 = 1 := by
  obtain ⟨_, _, hoptimal⟩ :=
    deadlineWithdrawalSecurityValue_spec positiveSecurityReward 0
  have hlower := hoptimal 0 1 positiveSecurity_zero_feasible
  have hupper := deadlineWithdrawalSecurityValue_le_singleton positiveSecurityReward 0
  simp only [positiveSecurityReward, pairReward_singleton] at hupper
  exact le_antisymm hupper hlower

theorem positiveSecurity_optimal_hazard_iff (hazard : ℝ) :
    DeadlineWithdrawalSecurityFeasible positiveSecurityReward 0 hazard 1 ↔ hazard = 0 := by
  rw [positiveSecurityReward, pairReward_securityFeasible_iff]
  constructor
  · rintro ⟨hmem, _, hrow⟩
    linarith [hmem.1]
  · rintro rfl
    norm_num

theorem positiveSecurity_floor_values :
    deadlineWithdrawalZeroFloor positiveSecurityReward 0 = 0 ∧
      deadlineWithdrawalSecurityFloor positiveSecurityReward 0 = 1 ∧
      min (deadlineWithdrawalSecurityFloor positiveSecurityReward 0) 0 = 0 := by
  have hfloor : deadlineWithdrawalZeroFloor positiveSecurityReward 0 = 0 := by
    norm_num [positiveSecurityReward, pairReward_zeroFloor]
  simp only [deadlineWithdrawalSecurityFloor, hfloor, positiveSecurity_value_eq_one]
  norm_num

theorem positiveSecurity_positive_hazard_feasible
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    DeadlineWithdrawalSecurityFeasible positiveSecurityReward 0 hazard (1 - hazard) := by
  rw [positiveSecurityReward, pairReward_securityFeasible_iff]
  exact ⟨⟨hpositive.le, hle⟩, by linarith,
    by simpa only [mul_one, mul_zero, add_zero] using (le_refl (1 - hazard))⟩

/-- The positive geometric law guarantees `1 - hazard` against every future tuple. -/
theorem positiveSecurity_terminal_guarantee
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) (deadline : ℕ)
    (opponents : Fin 2 → Option ℕ) (hown : opponents 0 = none)
    (hfuture : ∀ j, (deadline : WithTop ℕ) < quittingStoppingTimeValue (opponents j)) :
    1 - hazard ≤ expect (deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hle)
      (fun clock => quittingPureClockTerminalPayoff positiveSecurityReward
        (Function.update (quietParentClocks opponents) (some 0) clock) (some 0)) := by
  exact deadlineWithdrawalSecurityRestartLaw_terminal_floor positiveSecurityReward 0 hazard _
    hpositive (positiveSecurity_positive_hazard_feasible hazard hpositive hle)
    deadline opponents hown hfuture

/-- At the first possible opponent date the actual three-branch law pays `1 - hazard`. -/
theorem positiveSecurity_first_restart_date_payoff
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) (deadline : ℕ) :
    expect (deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hle)
      (fun clock => quittingPureClockTerminalPayoff positiveSecurityReward
        (Function.update (fun player : Option (Fin 2) =>
          if player = some 1 then some (deadline + 1) else none) (some 0) clock) (some 0)) =
      1 - hazard := by
  let opponents : Option (Fin 2) → Option ℕ := fun player =>
    if player = some 1 then some (deadline + 1) else none
  have hinside : ∀ player ∈ ({some 1} : Finset (Option (Fin 2))),
      opponents player = some (deadline + 1 + 0) := by
    intro player hplayer
    have heq := Finset.mem_singleton.mp hplayer
    subst player
    simp only [opponents, ite_true, add_zero]
  have houtside : ∀ player, player ≠ some 0 → player ∉ ({some 1} : Finset _ ) →
      ((deadline + 1 + 0 : ℕ) : WithTop ℕ) < quittingStoppingTimeValue (opponents player) := by
    intro player _ hnot
    have hne : player ≠ some 1 := by simpa only [Finset.mem_singleton] using hnot
    simp [opponents, hne, quittingStoppingTimeValue]
  have hbranches := deadlineWithdrawalSecurity_terminalPayoff_threeBranch
    positiveSecurityReward 0 opponents {some 1} (Finset.singleton_nonempty _)
    (by decide) (deadline + 1) 0
  rw [deadlineWithdrawalSecurityRestartLaw, geometricFiniteStoppingLaw, expect_map]
  have hfun : (fun offset => quittingPureClockTerminalPayoff positiveSecurityReward
      (Function.update opponents (some 0) (some (deadline + 1 + offset))) (some 0)) =
      (fun offset => if offset < 0 then (1 : ℝ) else if offset = 0 then 0 else 1) := by
    funext offset
    have hpairZero : ({some 0, some 1} : Finset (Option (Fin 2))) ≠ {some 0} := by decide
    simpa [positiveSecurityReward, pairReward, hpairZero] using
      hbranches offset hinside houtside
  change expect (geometricOffsetLaw hazard hpositive hle) _ = _
  rw [hfun, deadlineWithdrawalSecurity_geometric_threeBranch_expect]
  ring

theorem positiveSecurity_first_restart_date_lt_value
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) (deadline : ℕ) :
    expect (deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hle)
      (fun clock => quittingPureClockTerminalPayoff positiveSecurityReward
        (Function.update (fun player : Option (Fin 2) =>
          if player = some 1 then some (deadline + 1) else none) (some 0) clock) (some 0)) <
      deadlineWithdrawalSecurityValue positiveSecurityReward 0 := by
  rw [positiveSecurity_first_restart_date_payoff, positiveSecurity_value_eq_one]
  linarith

theorem positiveSecurity_geometric_opponentsNever
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) (deadline : ℕ) :
    expect (deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hle)
      (fun clock => quittingPureClockTerminalPayoff positiveSecurityReward
        (Function.update (fun _ : Option (Fin 2) => none) (some 0) clock) (some 0)) = 1 := by
  simpa only [positiveSecurityReward, pairReward_singleton] using
    deadlineWithdrawalSecurityRestartLaw_terminalPayoff_opponentsNever
      positiveSecurityReward 0 deadline hazard hpositive hle

theorem positiveSecurity_never_opponentsNever :
    quittingPureClockTerminalPayoff positiveSecurityReward
      (fun _ : Option (Fin 2) => none) (some 0) = 0 := by
  simp only [quittingPureClockTerminalPayoff, quittingFirstStoppingOutcome_all_never]

end GameTheory.DeadlineSecurityPairExamples
