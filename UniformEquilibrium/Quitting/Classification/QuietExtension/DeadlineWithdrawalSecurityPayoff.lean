import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityRestart

/-!
# Stationary security at a finite first opponent date

The geometric expectation groups the same-date Continue and Quit branches
before using the LP row. The singleton branch and this grouped branch then
form a convex combination. Identification with arbitrary opponent clocks is
separate from this exact finite-date calculation.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability
open scoped BigOperators

private theorem security_geometric_head_sum (hazard : ℝ) (count : ℕ) :
    (∑ offset ∈ Finset.range count, hazard * (1 - hazard) ^ offset) =
      1 - (1 - hazard) ^ count := by
  induction count with
  | zero => simp
  | succ count ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

private theorem security_expect_indicator
    (law : PMF ℕ) (kept : Finset ℕ) :
    expect law (fun offset => if offset ∈ kept then (1 : ℝ) else 0) =
      ∑ offset ∈ kept, (law offset).toReal := by
  unfold expect
  rw [tsum_eq_sum (s := kept)]
  · simp
  · intro offset hoffset
    simp [hoffset]

/-- The exact geometric terminal calculation: opponent first stop at offset
`count`, with own-only, joint, and passive rewards kept distinct. -/
theorem deadlineWithdrawalSecurity_geometric_threeBranch_expect
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (count : ℕ) (singleton joint passive : ℝ) :
    expect (geometricOffsetLaw hazard hpositive hle)
        (fun offset => if offset < count then singleton
          else if offset = count then joint else passive) =
      (1 - (1 - hazard) ^ count) * singleton +
        (1 - hazard) ^ count * ((1 - hazard) * passive + hazard * joint) := by
  let law := geometricOffsetLaw hazard hpositive hle
  let early : ℕ → ℝ := fun offset =>
    (singleton - passive) * if offset ∈ Finset.range count then 1 else 0
  let tie : ℕ → ℝ := fun offset =>
    (joint - passive) * if offset ∈ ({count} : Finset ℕ) then 1 else 0
  have hearly : ∀ offset, |early offset| ≤ |singleton - passive| := by
    intro offset
    dsimp [early]
    split_ifs <;> simp
  have htie : ∀ offset, |tie offset| ≤ |joint - passive| := by
    intro offset
    dsimp [tie]
    split_ifs <;> simp
  have hfirst : ∀ offset, |passive + early offset| ≤
      |passive| + |singleton - passive| := by
    intro offset
    exact (abs_add_le _ _).trans (add_le_add_right (hearly offset) _)
  have hfun : (fun offset => if offset < count then singleton
      else if offset = count then joint else passive) =
      (fun offset => (passive + early offset) + tie offset) := by
    funext offset
    by_cases hbefore : offset < count
    · have hne : offset ≠ count := Nat.ne_of_lt hbefore
      simp [early, tie, hbefore, hne]
    · by_cases heq : offset = count
      · subst offset
        simp [early, tie]
      · simp [early, tie, hbefore, heq]
  rw [hfun]
  change expect law (fun offset => (passive + early offset) + tie offset) = _
  rw [expect_add_of_summable law _ _
      (expect_summable_of_bounded law _ hfirst)
      (expect_summable_of_bounded law _ htie),
    expect_add_of_summable law _ _
      (expect_summable_of_bounded law (fun _ => passive) (fun _ => le_rfl))
      (expect_summable_of_bounded law _ hearly)]
  simp only [early, tie, expect_const, expect_const_mul, security_expect_indicator]
  simp only [law, geometricOffsetLaw_apply_toReal, Finset.sum_singleton,
    security_geometric_head_sum]
  ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact terminal branches against a deterministic first opponent coalition.
The hypotheses describe its clocks, rather than assume any payoff bound. -/
theorem deadlineWithdrawalSecurity_terminalPayoff_threeBranch
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (opponents : Option ι → Option ℕ)
    (coalition : Finset (Option ι)) (hne : coalition.Nonempty)
    (hi : some i ∉ coalition) (start count offset : ℕ)
    (hinside : ∀ player ∈ coalition, opponents player = some (start + count))
    (houtside : ∀ player, player ≠ some i → player ∉ coalition →
      ((start + count : ℕ) : WithTop ℕ) < quittingStoppingTimeValue (opponents player)) :
    quittingPureClockTerminalPayoff reward
        (Function.update opponents (some i) (some (start + offset))) (some i) =
      if offset < count then
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
      else if offset = count then
        reward ⟨insert (some i) coalition, Finset.insert_nonempty _ _⟩ (some i)
      else reward ⟨coalition, hne⟩ (some i) := by
  let clocks := Function.update opponents (some i) (some (start + offset))
  by_cases hbefore : offset < count
  · have htime : ((start + offset : ℕ) : WithTop ℕ) < (start + count : ℕ) := by
      exact_mod_cast (Nat.add_lt_add_left hbefore start)
    have houtcome := quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
      clocks {some i} (Finset.singleton_nonempty (some i)) (start + offset)
      (by
        intro player hplayer
        have heq := Finset.mem_singleton.mp hplayer
        subst player
        simp [clocks])
      (by
        intro player hplayer
        have hplayerNe : player ≠ some i := by simpa using hplayer
        simp only [clocks, Function.update_of_ne hplayerNe]
        by_cases hmem : player ∈ coalition
        · rw [hinside player hmem]
          exact htime
        · exact htime.trans (houtside player hplayerNe hmem))
    simp [quittingPureClockTerminalPayoff, clocks, houtcome, hbefore] at *
  · by_cases heq : offset = count
    · subst offset
      have houtcome := quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
        clocks (insert (some i) coalition) (Finset.insert_nonempty _ _) (start + count)
        (by
          intro player hplayer
          rcases Finset.mem_insert.mp hplayer with heq | hmem
          · subst player
            simp [clocks]
          · have hplayerNe : player ≠ some i := by
              intro heq
              exact hi (heq ▸ hmem)
            simpa [clocks, hplayerNe] using hinside player hmem)
        (by
          intro player hplayer
          simp only [Finset.mem_insert, not_or] at hplayer
          simpa [clocks, hplayer.1, quittingStoppingTimeValue] using
            houtside player hplayer.1 hplayer.2)
      simp [quittingPureClockTerminalPayoff, clocks, houtcome] at *
    · have hafter : count < offset := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hbefore)
        (Ne.symm heq)
      have houtcome := quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
        clocks coalition hne (start + count)
        (by
          intro player hplayer
          have hplayerNe : player ≠ some i := by
            intro heq
            exact hi (heq ▸ hplayer)
          simpa [clocks, hplayerNe] using hinside player hplayer)
        (by
          intro player hplayer
          by_cases hplayerEq : player = some i
          · subst player
            simp only [clocks, Function.update_self, quittingStoppingTimeValue]
            exact_mod_cast (Nat.add_lt_add_left hafter start)
          · simpa [clocks, hplayerEq, quittingStoppingTimeValue] using
              houtside player hplayerEq hplayer)
      simp [quittingPureClockTerminalPayoff, clocks, houtcome, hbefore, heq] at *

omit [Fintype ι] in
/-- For literal LP-feasible reward rows, the geometric three-branch
expectation at every finite first opponent date is at least the value. -/
theorem deadlineWithdrawalSecurity_finiteOpponent_branch_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (hazard value : ℝ) (hpositive : 0 < hazard)
    (hfeasible : DeadlineWithdrawalSecurityFeasible reward i hazard value)
    (count : ℕ) (B : {A : Finset ι // A.Nonempty ∧ i ∉ A}) :
    value ≤ expect (geometricOffsetLaw hazard hpositive hfeasible.1.2)
      (fun offset => if offset < count then
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
      else if offset = count then
        reward ⟨cappedClockChildCoalition (insert i B.1),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty i B.1)⟩ (some i)
      else reward ⟨cappedClockChildCoalition B.1,
        cappedClockChildCoalition_nonempty B.2.1⟩ (some i)) := by
  rw [deadlineWithdrawalSecurity_geometric_threeBranch_expect]
  have hsurvival : 0 ≤ (1 - hazard) ^ count :=
    pow_nonneg (sub_nonneg.mpr hfeasible.1.2) count
  have hsurvivalLe : (1 - hazard) ^ count ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr hfeasible.1.2) (by linarith)
  have hsolo := hfeasible.2 none
  have hrow := hfeasible.2 (some B)
  dsimp [deadlineWithdrawalSecurityRow] at hsolo hrow
  have hfirst := mul_le_mul_of_nonneg_left hsolo (sub_nonneg.mpr hsurvivalLe)
  have hsecond := mul_le_mul_of_nonneg_left hrow hsurvival
  nlinarith

/-- The LP bound for the actual independently sampled post-deadline clock
against a deterministic finite first opponent date and coalition. -/
theorem deadlineWithdrawalSecurityRestartLaw_finiteOpponent_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (hazard value : ℝ) (hpositive : 0 < hazard)
    (hfeasible : DeadlineWithdrawalSecurityFeasible reward i hazard value)
    (deadline count : ℕ) (B : {A : Finset ι // A.Nonempty ∧ i ∉ A})
    (opponents : Option ι → Option ℕ)
    (hinside : ∀ player ∈ cappedClockChildCoalition B.1,
      opponents player = some (deadline + 1 + count))
    (houtside : ∀ player, player ≠ some i → player ∉ cappedClockChildCoalition B.1 →
      ((deadline + 1 + count : ℕ) : WithTop ℕ) <
        quittingStoppingTimeValue (opponents player)) :
    value ≤ expect (deadlineWithdrawalSecurityRestartLaw deadline hazard
        hpositive hfeasible.1.2)
      (fun clock => quittingPureClockTerminalPayoff reward
        (Function.update opponents (some i) clock) (some i)) := by
  rw [deadlineWithdrawalSecurityRestartLaw, geometricFiniteStoppingLaw, expect_map]
  have hi : some i ∉ cappedClockChildCoalition B.1 := by
    change some i ∉ B.1.map ⟨some, Option.some_injective ι⟩
    simpa using B.2.2
  have hbranches := deadlineWithdrawalSecurity_terminalPayoff_threeBranch reward i
    opponents (cappedClockChildCoalition B.1) (cappedClockChildCoalition_nonempty B.2.1)
    hi (deadline + 1) count
  have hcoalition : insert (some i) (cappedClockChildCoalition B.1) =
      cappedClockChildCoalition (insert i B.1) := by
    change insert (some i) (B.1.map ⟨some, Option.some_injective ι⟩) =
      (insert i B.1).map ⟨some, Option.some_injective ι⟩
    rw [Finset.map_insert]
    rfl
  have hfun : (fun offset => quittingPureClockTerminalPayoff reward
      (Function.update opponents (some i) (some (deadline + 1 + offset))) (some i)) =
      (fun offset => if offset < count then
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
      else if offset = count then
        reward ⟨cappedClockChildCoalition (insert i B.1),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty i B.1)⟩ (some i)
      else reward ⟨cappedClockChildCoalition B.1,
        cappedClockChildCoalition_nonempty B.2.1⟩ (some i)) := by
    funext offset
    simpa only [hcoalition] using hbranches offset hinside houtside
  rw [hfun]
  exact deadlineWithdrawalSecurity_finiteOpponent_branch_floor
    reward i hazard value hpositive hfeasible count B

/-- Terminal security against every deterministic future opponent tuple.
The owner's unused opponent coordinate is normalized to Never. -/
theorem deadlineWithdrawalSecurityRestartLaw_terminal_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (hazard value : ℝ) (hpositive : 0 < hazard)
    (hfeasible : DeadlineWithdrawalSecurityFeasible reward i hazard value)
    (deadline : ℕ) (opponents : ι → Option ℕ) (hown : opponents i = none)
    (hfuture : ∀ j, (deadline : WithTop ℕ) < quittingStoppingTimeValue (opponents j)) :
    value ≤ expect (deadlineWithdrawalSecurityRestartLaw deadline hazard
        hpositive hfeasible.1.2)
      (fun clock => quittingPureClockTerminalPayoff reward
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
      rw [hquiet, deadlineWithdrawalSecurityRestartLaw_terminalPayoff_opponentsNever]
      exact hfeasible.2 none
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
      apply deadlineWithdrawalSecurityRestartLaw_finiteOpponent_floor
        reward i hazard value hpositive hfeasible deadline count ⟨B, hB, hi⟩
        (quietParentClocks opponents)
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
