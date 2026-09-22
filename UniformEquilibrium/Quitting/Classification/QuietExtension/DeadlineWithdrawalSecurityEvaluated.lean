import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityPayoff

/-!
# Nonpositive stationary security for decreasing evaluations

Joint and passive rewards at the first opponent date are paired before
applying the feasible LP row. Individual collision rewards need not satisfy
the security floor.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem security_firstDate_update
    (i : ι) (opponents : Option ι → Option ℕ)
    (coalition : Finset (Option ι)) (hne : coalition.Nonempty)
    (hi : some i ∉ coalition) (own first : ℕ)
    (hinside : ∀ player ∈ coalition, opponents player = some first)
    (houtside : ∀ player, player ≠ some i → player ∉ coalition →
      (first : WithTop ℕ) < quittingStoppingTimeValue (opponents player)) :
    quittingEarliestStoppingValue (Function.update opponents (some i) (some own)) =
      min (own : WithTop ℕ) first := by
  let clocks := Function.update opponents (some i) (some own)
  apply le_antisymm
  · apply le_min
    · have h : quittingEarliestStoppingValue clocks ≤
          quittingStoppingTimeValue (clocks (some i)) :=
        Finset.inf_le (Finset.mem_univ (some i))
      simpa [clocks, quittingStoppingTimeValue] using h
    · let member := hne.choose
      have hmem : member ∈ coalition := hne.choose_spec
      have hneOwn : member ≠ some i := by intro h; exact hi (h ▸ hmem)
      have h : quittingEarliestStoppingValue clocks ≤
          quittingStoppingTimeValue (clocks member) :=
        Finset.inf_le (Finset.mem_univ member)
      simpa [clocks, hneOwn, hinside member hmem, quittingStoppingTimeValue] using h
  · apply Finset.le_inf
    intro player _
    by_cases hown : player = some i
    · subst player
      simp only [Function.update_self, quittingStoppingTimeValue]
      exact min_le_left (own : WithTop ℕ) first
    · by_cases hmem : player ∈ coalition
      · rw [Function.update_of_ne hown, hinside player hmem]
        exact min_le_right (own : WithTop ℕ) first
      · exact (min_le_right _ _).trans (by
          simpa [clocks, hown] using (houtside player hown hmem).le)

/-- Actual evaluated payoff at each own geometric offset. -/
theorem deadlineWithdrawalSecurity_evaluatedPayoff_threeBranch
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (i : ι) (opponents : Option ι → Option ℕ)
    (coalition : Finset (Option ι)) (hne : coalition.Nonempty)
    (hi : some i ∉ coalition) (start count offset : ℕ)
    (hinside : ∀ player ∈ coalition, opponents player = some (start + count))
    (houtside : ∀ player, player ≠ some i → player ∉ coalition →
      ((start + count : ℕ) : WithTop ℕ) < quittingStoppingTimeValue (opponents player)) :
    quittingPureClockEvaluatedPayoff reward evaluation
        (Function.update opponents (some i) (some (start + offset))) (some i) =
      if offset < count then evaluation (start + offset : ℕ) *
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
      else if offset = count then evaluation (start + count : ℕ) *
        reward ⟨insert (some i) coalition, Finset.insert_nonempty _ _⟩ (some i)
      else evaluation (start + count : ℕ) * reward ⟨coalition, hne⟩ (some i) := by
  have hmul (clocks : Option ι → Option ℕ) :
      quittingPureClockEvaluatedPayoff reward evaluation clocks (some i) =
        evaluation (quittingEarliestStoppingValue clocks) *
          quittingPureClockTerminalPayoff reward clocks (some i) := by
    unfold quittingPureClockEvaluatedPayoff quittingPureClockTerminalPayoff
    cases quittingFirstStoppingOutcome clocks <;> simp
  rw [hmul, security_firstDate_update i opponents coalition hne hi _ _ hinside houtside,
    deadlineWithdrawalSecurity_terminalPayoff_threeBranch reward i opponents
      coalition hne hi start count offset hinside houtside]
  by_cases hbefore : offset < count
  · have hle : ((start + offset : ℕ) : WithTop ℕ) ≤ (start + count : ℕ) := by
      exact_mod_cast (Nat.add_le_add_left hbefore.le start)
    simp only [Nat.cast_add] at hle ⊢
    rw [min_eq_left hle]
    simp [hbefore]
  · have hle : ((start + count : ℕ) : WithTop ℕ) ≤ (start + offset : ℕ) := by
      exact_mod_cast (Nat.add_le_add_left (Nat.le_of_not_gt hbefore) start)
    simp only [Nat.cast_add] at hle ⊢
    rw [min_eq_right hle]
    by_cases heq : offset = count
    · subst offset
      simp
    · simp [hbefore, heq]

omit [Fintype ι] [DecidableEq ι] in
/-- Nonpositive security for the evaluated geometric branches. The joint and
passive branches share one evaluation weight and are averaged together. -/
theorem deadlineWithdrawalSecurity_geometric_evaluated_branch_floor
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (deadline count : ℕ) (singleton joint passive value : ℝ)
    (hvalue : value ≤ 0) (hsingleton : value ≤ singleton)
    (hrow : value ≤ (1 - hazard) * passive + hazard * joint) :
    evaluation deadline * value ≤ expect (geometricOffsetLaw hazard hpositive hle)
      (fun offset => if offset < count then evaluation (deadline + 1 + offset : ℕ) * singleton
        else if offset = count then evaluation (deadline + 1 + count : ℕ) * joint
        else evaluation (deadline + 1 + count : ℕ) * passive) := by
  let law := geometricOffsetLaw hazard hpositive hle
  let lower : ℕ → ℝ := fun offset =>
    if offset < count then evaluation deadline * value
    else if offset = count then evaluation (deadline + 1 + count : ℕ) * joint
    else evaluation (deadline + 1 + count : ℕ) * passive
  let actual : ℕ → ℝ := fun offset =>
    if offset < count then evaluation (deadline + 1 + offset : ℕ) * singleton
    else if offset = count then evaluation (deadline + 1 + count : ℕ) * joint
    else evaluation (deadline + 1 + count : ℕ) * passive
  let R := |singleton| + |joint| + |passive| + |value|
  have hbound (time : ℕ) (r : ℝ) (hr : |r| ≤ R) :
      |evaluation time * r| ≤ evaluation 0 * R := by
    rw [abs_mul, abs_of_nonneg (hnonneg _)]
    exact mul_le_mul (hantitone (by simp)) hr (abs_nonneg r) (hnonneg _)
  have hs : |singleton| ≤ R := by
    dsimp [R]; linarith [abs_nonneg joint, abs_nonneg passive, abs_nonneg value]
  have hj : |joint| ≤ R := by
    dsimp [R]; linarith [abs_nonneg singleton, abs_nonneg passive, abs_nonneg value]
  have hp : |passive| ≤ R := by
    dsimp [R]; linarith [abs_nonneg singleton, abs_nonneg joint, abs_nonneg value]
  have hv : |value| ≤ R := by
    dsimp [R]; linarith [abs_nonneg singleton, abs_nonneg joint, abs_nonneg passive]
  have hlower : ∀ offset, |lower offset| ≤ evaluation 0 * R := by
    intro offset
    dsimp [lower]
    split_ifs
    · exact hbound _ _ hv
    · exact hbound _ _ hj
    · exact hbound _ _ hp
  have hactual : ∀ offset, |actual offset| ≤ evaluation 0 * R := by
    intro offset
    dsimp [actual]
    split_ifs
    · exact hbound _ _ hs
    · exact hbound _ _ hj
    · exact hbound _ _ hp
  have hcompare : ∀ offset, lower offset ≤ actual offset := by
    intro offset
    dsimp [lower, actual]
    split_ifs
    · exact deadlineWithdrawal_laterEvaluatedFloor_le _ _ _ _
        (hnonneg _) (hnonneg _) (hantitone (by exact_mod_cast (by omega :
          deadline ≤ deadline + 1 + offset))) hvalue hsingleton
    · exact le_rfl
    · exact le_rfl
  have hexpect := expect_mono_of_pointwise_bounded law lower actual hcompare hlower hactual
  have hformula := deadlineWithdrawalSecurity_geometric_threeBranch_expect hazard
    hpositive hle count (evaluation deadline * value)
    (evaluation (deadline + 1 + count : ℕ) * joint)
    (evaluation (deadline + 1 + count : ℕ) * passive)
  change expect law lower = _ at hformula
  have hpaired : evaluation deadline * value ≤
      evaluation (deadline + 1 + count : ℕ) *
        ((1 - hazard) * passive + hazard * joint) :=
    deadlineWithdrawal_laterEvaluatedFloor_le _ _ _ _ (hnonneg _) (hnonneg _)
      (hantitone (by exact_mod_cast (by omega : deadline ≤ deadline + 1 + count)))
      hvalue hrow
  have hsurvival : 0 ≤ (1 - hazard) ^ count := pow_nonneg (sub_nonneg.mpr hle) count
  have hweighted := mul_le_mul_of_nonneg_left hpaired hsurvival
  change evaluation deadline * value ≤ expect law actual
  rw [hformula] at hexpect
  nlinarith

/-- The evaluated LP security floor for the actual geometric restart at a
finite first opponent date. The floor must be nonpositive. -/
theorem deadlineWithdrawalSecurityRestartLaw_evaluated_finiteOpponent_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (i : ι) (hazard value : ℝ) (hpositive : 0 < hazard) (hvalue : value ≤ 0)
    (hfeasible : DeadlineWithdrawalSecurityFeasible reward i hazard value)
    (deadline count : ℕ) (B : {A : Finset ι // A.Nonempty ∧ i ∉ A})
    (opponents : Option ι → Option ℕ)
    (hinside : ∀ player ∈ cappedClockChildCoalition B.1,
      opponents player = some (deadline + 1 + count))
    (houtside : ∀ player, player ≠ some i → player ∉ cappedClockChildCoalition B.1 →
      ((deadline + 1 + count : ℕ) : WithTop ℕ) <
        quittingStoppingTimeValue (opponents player)) :
    evaluation deadline * value ≤ expect
      (deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hfeasible.1.2)
      (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
        (Function.update opponents (some i) clock) (some i)) := by
  rw [deadlineWithdrawalSecurityRestartLaw, geometricFiniteStoppingLaw, expect_map]
  have hi : some i ∉ cappedClockChildCoalition B.1 := by
    change some i ∉ B.1.map ⟨some, Option.some_injective ι⟩
    simpa using B.2.2
  have hcoalition : insert (some i) (cappedClockChildCoalition B.1) =
      cappedClockChildCoalition (insert i B.1) := by
    change insert (some i) (B.1.map ⟨some, Option.some_injective ι⟩) =
      (insert i B.1).map ⟨some, Option.some_injective ι⟩
    rw [Finset.map_insert]
    rfl
  have hfun : (fun offset => quittingPureClockEvaluatedPayoff reward evaluation
      (Function.update opponents (some i) (some (deadline + 1 + offset))) (some i)) =
      (fun offset => if offset < count then evaluation (deadline + 1 + offset : ℕ) *
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
      else if offset = count then evaluation (deadline + 1 + count : ℕ) *
        reward ⟨cappedClockChildCoalition (insert i B.1),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty i B.1)⟩ (some i)
      else evaluation (deadline + 1 + count : ℕ) * reward ⟨cappedClockChildCoalition B.1,
        cappedClockChildCoalition_nonempty B.2.1⟩ (some i)) := by
    funext offset
    simpa only [hcoalition] using deadlineWithdrawalSecurity_evaluatedPayoff_threeBranch
      reward evaluation i opponents (cappedClockChildCoalition B.1)
      (cappedClockChildCoalition_nonempty B.2.1) hi (deadline + 1) count offset
      hinside houtside
  rw [hfun]
  exact deadlineWithdrawalSecurity_geometric_evaluated_branch_floor hazard hpositive
    hfeasible.1.2 evaluation hnonneg hantitone deadline count _ _ _ value hvalue
    (hfeasible.2 none) (hfeasible.2 (some B))

/-- Evaluated security against opponent Never uses almost-sure finite own
stopping; the potentially positive LP value is not assigned to Never. -/
theorem deadlineWithdrawalSecurityRestartLaw_evaluated_opponentsNever_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (i : ι) (hazard value : ℝ) (hpositive : 0 < hazard) (hvalue : value ≤ 0)
    (hfeasible : DeadlineWithdrawalSecurityFeasible reward i hazard value)
    (deadline : ℕ) :
    evaluation deadline * value ≤ expect
      (deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hfeasible.1.2)
      (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
        (Function.update (fun _ : Option ι => none) (some i) clock) (some i)) := by
  rw [deadlineWithdrawalSecurityRestartLaw, geometricFiniteStoppingLaw, expect_map]
  let law := geometricOffsetLaw hazard hpositive hfeasible.1.2
  let payoff : ℕ → ℝ := fun offset => quittingPureClockEvaluatedPayoff reward evaluation
    (Function.update (fun _ : Option ι => none) (some i)
      (some (deadline + 1 + offset))) (some i)
  have hpointwise (offset : ℕ) : evaluation deadline * value ≤ payoff offset := by
    let time := deadline + 1 + offset
    let clocks := Function.update (fun _ : Option ι => none) (some i) (some time)
    have hfirst : quittingEarliestStoppingValue clocks = (time : WithTop ℕ) := by
      apply le_antisymm
      · have h : quittingEarliestStoppingValue clocks ≤
            quittingStoppingTimeValue (clocks (some i)) :=
          Finset.inf_le (Finset.mem_univ (some i))
        simpa [clocks, quittingStoppingTimeValue] using h
      · apply Finset.le_inf
        intro player _
        by_cases hp : player = some i <;> simp [clocks, hp, quittingStoppingTimeValue]
    have hmul : payoff offset = evaluation time *
        quittingPureClockTerminalPayoff reward clocks (some i) := by
      change quittingPureClockEvaluatedPayoff reward evaluation clocks (some i) = _
      unfold quittingPureClockEvaluatedPayoff quittingPureClockTerminalPayoff
      rw [hfirst]
      cases quittingFirstStoppingOutcome clocks <;> simp
    rw [hmul]
    change evaluation deadline * value ≤ evaluation time *
      quittingPureClockTerminalPayoff reward
        (Function.update (fun _ : Option ι => none) (some i) (some time)) (some i)
    rw [deadlineWithdrawalSecurity_terminalPayoff_opponentsNever]
    exact deadlineWithdrawal_laterEvaluatedFloor_le _ _ _ _ (hnonneg _) (hnonneg _)
      (hantitone (by exact_mod_cast (by dsimp [time]; omega : deadline ≤ time)))
      hvalue (hfeasible.2 none)
  have hbound (offset : ℕ) : |payoff offset| ≤ evaluation 0 * quittingRewardBound reward :=
    abs_quittingPureClockEvaluatedPayoff_le reward evaluation hnonneg hantitone _ _
  have h := expect_mono_of_pointwise_summable law (fun _ => evaluation deadline * value)
    payoff hpointwise
    (expect_summable_of_bounded law _ (fun _ => le_rfl))
    (expect_summable_of_bounded law _ hbound)
  simpa only [expect_const] using h

/-- Actual geometric security for every deterministic future opponent tuple
and every nonnegative antitone evaluation, at a nonpositive feasible value. -/
theorem deadlineWithdrawalSecurityRestartLaw_evaluated_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (i : ι) (hazard value : ℝ) (hpositive : 0 < hazard) (hvalue : value ≤ 0)
    (hfeasible : DeadlineWithdrawalSecurityFeasible reward i hazard value)
    (deadline : ℕ) (opponents : ι → Option ℕ) (hown : opponents i = none)
    (hfuture : ∀ j, (deadline : WithTop ℕ) < quittingStoppingTimeValue (opponents j)) :
    evaluation deadline * value ≤ expect
      (deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hfeasible.1.2)
      (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
        (Function.update (quietParentClocks opponents) (some i) clock) (some i)) := by
  let : Nonempty ι := ⟨i⟩
  have hmin (j : ι) : quittingEarliestStoppingValue opponents ≤
      quittingStoppingTimeValue (opponents j) :=
    Finset.inf_le (Finset.mem_univ j)
  induction hfirst : quittingEarliestStoppingValue opponents using WithTop.recTopCoe with
  | top =>
      have hnone : ∀ j, opponents j = none := by
        intro j
        have hj := hmin j
        rw [hfirst] at hj
        cases hclock : opponents j with
        | none => rfl
        | some time => simp [hclock, quittingStoppingTimeValue] at hj
      have hquiet : quietParentClocks opponents = (fun _ : Option ι => none) := by
        funext player
        cases player with
        | none => rfl
        | some j => exact hnone j
      rw [hquiet]
      exact deadlineWithdrawalSecurityRestartLaw_evaluated_opponentsNever_floor
        reward evaluation hnonneg hantitone i hazard value hpositive hvalue hfeasible deadline
  | coe first =>
      let B := quittingEarliestStoppingCoalition opponents
      have hB : B.Nonempty := quittingEarliestStoppingCoalition_nonempty opponents
      have hi : i ∉ B := by
        simp [B, quittingEarliestStoppingCoalition, hown, hfirst, quittingStoppingTimeValue]
      have hmember (j : ι) (hj : j ∈ B) : opponents j = some first := by
        have heq : quittingStoppingTimeValue (opponents j) = (first : WithTop ℕ) := by
          simpa [B, quittingEarliestStoppingCoalition, hfirst] using hj
        cases hclock : opponents j with
        | none => simp [hclock, quittingStoppingTimeValue] at heq
        | some time =>
            have htime : time = first := by
              simpa [hclock, quittingStoppingTimeValue] using heq
            simp [htime]
      let member := hB.choose
      have hmemberB : member ∈ B := hB.choose_spec
      have hdeadline : deadline < first := by
        have h := hfuture member
        rw [hmember member hmemberB] at h
        simpa [quittingStoppingTimeValue] using h
      let count := first - (deadline + 1)
      have htime : deadline + 1 + count = first := by dsimp [count]; omega
      apply deadlineWithdrawalSecurityRestartLaw_evaluated_finiteOpponent_floor
        reward evaluation hnonneg hantitone i hazard value hpositive hvalue hfeasible
        deadline count ⟨B, hB, hi⟩ (quietParentClocks opponents)
      · intro player hplayer
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hplayer
        change opponents j = some (deadline + 1 + count)
        rw [htime]
        exact hmember j hj
      · intro player _ hplayer
        rw [htime]
        cases player with
        | none => simp [quietParentClocks, quittingStoppingTimeValue]
        | some j =>
            have hj : j ∉ B := by
              intro hj
              exact hplayer (Finset.mem_map.mpr ⟨j, hj, rfl⟩)
            have hne : quittingStoppingTimeValue (opponents j) ≠ (first : WithTop ℕ) := by
              simpa [B, quittingEarliestStoppingCoalition, hfirst] using hj
            have hle := hmin j
            rw [hfirst] at hle
            exact lt_of_le_of_ne hle hne.symm

end GameTheory
