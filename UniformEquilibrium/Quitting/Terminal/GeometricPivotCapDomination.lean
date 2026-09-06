import UniformEquilibrium.Quitting.Terminal.FiniteOpponentPivotResponseFormula
import MathUE.ProbabilityMassFunction.GeometricPivotStoppingLaw

/-! # Signed geometric pivot-tail endpoint domination -/

noncomputable section

namespace GameTheory

open Filter
open _root_.Math.Probability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual limit of finite late responses, retaining both finite-tail
and Never contributions with their original signed rewards. -/
def quittingPivotLateLimitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot responder who : ι)
    (deadline : ℕ) (law : PMF (Option ℕ)) : ℝ :=
  quittingPivotEarlyContribution reward opponents pivot responder who deadline law +
    (∏ j ∈ (Finset.univ.erase pivot).erase responder, (opponents j none).toReal) *
      (reward (quittingSingletonTerminal pivot) who *
          stoppingLawLateFiniteMass law (deadline - 1) +
        reward (quittingSingletonTerminal responder) who * (law none).toReal)

/-- The third signed endpoint is the limit of actual old finite responses;
it need not be attained by a stopping time. -/
theorem quittingTerminalPayoff_pivot_late_response_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot responder who : ι) (hne : responder ≠ pivot)
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (hfinite : ∀ j, j ≠ pivot → j ≠ responder →
      IsFiniteClockStoppingLaw deadline (opponents j)) (law : PMF (Option ℕ)) :
    Tendsto (fun time ↦ quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward
        (Function.update (Function.update opponents pivot law)
          responder (PMF.pure (some time)))) who) atTop
      (nhds (quittingPivotLateLimitValue reward opponents pivot responder who deadline law)) := by
  let early := quittingPivotEarlyContribution reward opponents pivot responder who deadline law
  let weight := ∏ j ∈ (Finset.univ.erase pivot).erase responder, (opponents j none).toReal
  let before := reward (quittingSingletonTerminal pivot) who
  let tie := reward ⟨{pivot, responder}, by simp⟩ who
  let after := reward (quittingSingletonTerminal responder) who
  let tail := stoppingLawLateFiniteMass law (deadline - 1)
  let never := (law none).toReal
  have hmass := stoppingLaw_sum_Ico_tendsto_lateFiniteMass law hdeadline
  have hatom := stoppingLaw_finite_atom_tendsto_zero law
  have hlimit : Tendsto (fun time ↦ early + weight *
      (after * (tail + never) +
        (before - after) * (∑ chosen ∈ Finset.Ico deadline time, (law (some chosen)).toReal) +
        (tie - after) * (law (some time)).toReal)) atTop
      (nhds (early + weight *
        (after * (tail + never) + (before - after) * tail + (tie - after) * 0))) := by
    exact tendsto_const_nhds.add (tendsto_const_nhds.mul
      ((tendsto_const_nhds.add (tendsto_const_nhds.mul hmass)).add
        (tendsto_const_nhds.mul hatom)))
  have hvalue : early + weight *
      (after * (tail + never) + (before - after) * tail + (tie - after) * 0) =
      quittingPivotLateLimitValue reward opponents pivot responder who deadline law := by
    change early + weight *
      (after * (tail + never) + (before - after) * tail + (tie - after) * 0) =
      early + weight * (before * tail + after * never)
    ring
  rw [hvalue] at hlimit
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop deadline] with time htime
  exact (quittingTerminalPayoff_pivot_late_response_eq reward opponents pivot responder who hne
    deadline time hdeadline htime hfinite law).symm

/-- Every new finite late response is an exact convex interpolation between
the old first-positive-atom response and the old limiting late response. -/
theorem quittingTerminalPayoff_geometric_pivot_late_response_eq_affine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot responder who : ι) (hne : responder ≠ pivot)
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (hfinite : ∀ j, j ≠ pivot → j ≠ responder →
      IsFiniteClockStoppingLaw deadline (opponents j)) (law : PMF (Option ℕ))
    (first : ℕ) (hfirst : deadline ≤ first)
    (hzero : ∀ time, deadline ≤ time → time < first → (law (some time)).toReal = 0)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (hmatch : stoppingLawLateFiniteMass law (deadline - 1) * hazard =
      (law (some first)).toReal) (offset : ℕ) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update
            (Function.update opponents pivot
              (geometricPivotStoppingLaw law deadline hazard hpositive hle))
            responder (PMF.pure (some (deadline + offset))))) who =
      (1 - hazard) ^ offset * quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (Function.update opponents pivot law)
            responder (PMF.pure (some first)))) who +
        (1 - (1 - hazard) ^ offset) *
          quittingPivotLateLimitValue reward opponents pivot responder who deadline law := by
  have hnew := quittingTerminalPayoff_pivot_late_response_eq
    reward opponents pivot responder who hne deadline (deadline + offset)
    hdeadline (by omega) hfinite
    (geometricPivotStoppingLaw law deadline hazard hpositive hle)
  have hearly : quittingPivotEarlyContribution reward opponents pivot responder who deadline
      (geometricPivotStoppingLaw law deadline hazard hpositive hle) =
      quittingPivotEarlyContribution reward opponents pivot responder who deadline law := by
    unfold quittingPivotEarlyContribution
    rw [censorLateFiniteStoppingLaw_geometricPivotStoppingLaw law hdeadline hazard hpositive hle]
  rw [hearly, geometricPivotStoppingLaw_lateFiniteMass law hdeadline hazard hpositive hle,
    geometricPivotStoppingLaw_none,
    geometricPivotStoppingLaw_sum_Ico_add law hdeadline hazard hpositive hle,
    geometricPivotStoppingLaw_add_apply_toReal law hdeadline hazard hpositive hle] at hnew
  have hold := quittingTerminalPayoff_pivot_late_response_eq
    reward opponents pivot responder who hne deadline first hdeadline hfirst hfinite law
  have hsum : (∑ time ∈ Finset.Ico deadline first, (law (some time)).toReal) = 0 := by
    apply Finset.sum_eq_zero
    intro time htime
    exact hzero time (Finset.mem_Ico.mp htime).1 (Finset.mem_Ico.mp htime).2
  rw [hsum, ← hmatch] at hold
  rw [hnew, hold]
  unfold quittingPivotLateLimitValue
  ring

private theorem actual_pure_response_le_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (responder : ι) (choice : Option ℕ) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (Function.update laws responder (PMF.pure choice)))
        responder ≤
      quittingContinuationBestResponseValue reward (quittingStoppingLawProfile reward laws)
        responder := by
  rw [quittingTerminalPayoff_stoppingLawProfile_update_pure_eq]
  exact quittingTerminalPayoff_update_le_continuationBestResponseValue reward _ responder _

/-- The limiting finite-response endpoint is bounded by the old unrestricted
behavioral cap even when no finite date attains that endpoint. -/
theorem quittingPivotLateLimitValue_le_continuationBestResponseValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot responder : ι) (hne : responder ≠ pivot)
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (hfinite : ∀ j, j ≠ pivot → j ≠ responder →
      IsFiniteClockStoppingLaw deadline (opponents j)) (law : PMF (Option ℕ)) :
    quittingPivotLateLimitValue reward opponents pivot responder responder deadline law ≤
      quittingContinuationBestResponseValue reward
        (quittingStoppingLawProfile reward (Function.update opponents pivot law)) responder := by
  have hlimit := quittingTerminalPayoff_pivot_late_response_tendsto reward opponents
    pivot responder responder hne deadline hdeadline hfinite law
  exact le_of_tendsto hlimit (Filter.Eventually.of_forall fun time ↦
    actual_pure_response_le_cap reward (Function.update opponents pivot law) responder (some time))

/-- Matching the geometric first atom to the first positive source atom
weakly lowers every nonpivot's full behavioral deviation cap. This includes
Never, every finite date, and all behavioral mixtures of those responses. -/
theorem quittingContinuationBestResponseValue_geometric_pivot_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot responder : ι) (hne : responder ≠ pivot)
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (hfinite : ∀ j, j ≠ pivot → IsFiniteClockStoppingLaw deadline (opponents j))
    (law : PMF (Option ℕ)) (first : ℕ) (hfirst : deadline ≤ first)
    (hzero : ∀ time, deadline ≤ time → time < first → (law (some time)).toReal = 0)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (hmatch : stoppingLawLateFiniteMass law (deadline - 1) * hazard =
      (law (some first)).toReal) :
    quittingContinuationBestResponseValue reward
        (quittingStoppingLawProfile reward
          (Function.update opponents pivot
            (geometricPivotStoppingLaw law deadline hazard hpositive hle))) responder ≤
      quittingContinuationBestResponseValue reward
        (quittingStoppingLawProfile reward (Function.update opponents pivot law)) responder := by
  let target := geometricPivotStoppingLaw law deadline hazard hpositive hle
  let targetLaws := Function.update opponents pivot target
  let sourceLaws := Function.update opponents pivot law
  have hhead : ∀ time < deadline, target (some time) = law (some time) := by
    intro time htime
    exact geometricPivotStoppingLaw_some_of_lt law deadline hazard hpositive hle htime
  have hnever : target none = law none :=
    geometricPivotStoppingLaw_none law deadline hazard hpositive hle
  have hearly (choice : Option ℕ)
      (hchoice : choice = none ∨ ∃ time < deadline, choice = some time) :
      quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward
            (Function.update targetLaws responder (PMF.pure choice))) responder =
        quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward
            (Function.update sourceLaws responder (PMF.pure choice))) responder := by
    apply quittingTerminalPayoff_pivot_finiteReplacement_eq reward opponents pivot deadline
      hfinite target law hhead hnever responder hne (PMF.pure choice) _ responder
    intro value hvalue
    have heq : value = choice := by simpa [PMF.pure_apply] using hvalue
    exact heq ▸ hchoice
  have hlimit := quittingPivotLateLimitValue_le_continuationBestResponseValue reward opponents
    pivot responder hne deadline hdeadline (fun j hjp _ ↦ hfinite j hjp) law
  have hfirstBound := actual_pure_response_le_cap reward sourceLaws responder (some first)
  change quittingContinuationBestResponseValue reward
    (quittingStoppingLawProfile reward targetLaws) responder ≤ _
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  apply csSup_le
  · exact ⟨_, ⟨none, rfl⟩⟩
  · rintro value ⟨choice, rfl⟩
    dsimp only
    rw [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq]
    change quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update targetLaws responder (PMF.pure choice))) responder ≤
      quittingContinuationBestResponseValue reward (quittingStoppingLawProfile reward sourceLaws)
        responder
    cases choice with
    | none =>
        rw [hearly none (Or.inl rfl)]
        exact actual_pure_response_le_cap reward sourceLaws responder none
    | some time =>
        by_cases htime : time < deadline
        · rw [hearly (some time) (Or.inr ⟨time, htime, rfl⟩)]
          exact actual_pure_response_le_cap reward sourceLaws responder (some time)
        · obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le (show deadline ≤ time by omega)
          rw [quittingTerminalPayoff_geometric_pivot_late_response_eq_affine reward opponents
            pivot responder responder hne deadline hdeadline (fun j hjp _ ↦ hfinite j hjp)
            law first hfirst hzero hazard hpositive hle hmatch offset]
          have hpower : 0 ≤ (1 - hazard) ^ offset := pow_nonneg (sub_nonneg.mpr hle) offset
          have hpowerLe : (1 - hazard) ^ offset ≤ 1 :=
            pow_le_one₀ (sub_nonneg.mpr hle) (by linarith)
          have hfirstWeighted := mul_le_mul_of_nonneg_left hfirstBound hpower
          have hlimitWeighted := mul_le_mul_of_nonneg_left hlimit (sub_nonneg.mpr hpowerLe)
          dsimp only [sourceLaws] at hfirstWeighted ⊢
          nlinarith

/-- Every geometric redistribution of the finite pivot tail preserves the
complete labelled terminal outcome law against the fixed finite opponents. -/
theorem quittingIndependentTerminalOutcomeLaw_geometric_pivot_eq
    (opponents : ι → PMF (Option ℕ)) (pivot : ι) (deadline : ℕ)
    (hfinite : ∀ j, j ≠ pivot → IsFiniteClockStoppingLaw deadline (opponents j))
    (law : PMF (Option ℕ)) (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    letI : Nonempty ι := ⟨pivot⟩
    quittingIndependentTerminalOutcomeLaw
        (Function.update opponents pivot
          (geometricPivotStoppingLaw law deadline hazard hpositive hle)) =
      quittingIndependentTerminalOutcomeLaw (Function.update opponents pivot law) := by
  exact quittingIndependentTerminalOutcomeLaw_pivot_eq_of_head_and_never
    opponents pivot deadline hfinite
    (geometricPivotStoppingLaw law deadline hazard hpositive hle) law
    (fun _ htime ↦ geometricPivotStoppingLaw_some_of_lt law deadline hazard hpositive hle htime)
    (geometricPivotStoppingLaw_none law deadline hazard hpositive hle)

/-- The actual prescribed payoff vector is unchanged by finite-tail
geometric redistribution; this identity does not require the cap-optimal
choice of geometric hazard. -/
theorem quittingTerminalPayoff_geometric_pivot_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot : ι) (deadline : ℕ)
    (hfinite : ∀ j, j ≠ pivot → IsFiniteClockStoppingLaw deadline (opponents j))
    (law : PMF (Option ℕ)) (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update opponents pivot
            (geometricPivotStoppingLaw law deadline hazard hpositive hle))) =
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (Function.update opponents pivot law)) := by
  exact quittingTerminalPayoff_pivot_eq_of_head_and_never reward opponents pivot deadline hfinite
    (geometricPivotStoppingLaw law deadline hazard hpositive hle) law
    (fun _ htime ↦ geometricPivotStoppingLaw_some_of_lt law deadline hazard hpositive hle htime)
    (geometricPivotStoppingLaw_none law deadline hazard hpositive hle)

/-- Every arbitrary actual pivot law admits an actual geometric finite-tail
replacement preserving all prescribed payoffs and weakly lowering every
player's unrestricted behavioral cap. The geometric hazard is selected from
the source's first positive late atom, with zero tail handled by identity. -/
theorem exists_geometric_pivot_payoff_eq_and_caps_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot : ι)
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (hfinite : ∀ j, j ≠ pivot → IsFiniteClockStoppingLaw deadline (opponents j))
    (law : PMF (Option ℕ)) :
    ∃ (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1),
      quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward
            (Function.update opponents pivot
              (geometricPivotStoppingLaw law deadline hazard hpositive hle))) =
        quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (Function.update opponents pivot law)) ∧
      ∀ responder, quittingContinuationBestResponseValue reward
          (quittingStoppingLawProfile reward
            (Function.update opponents pivot
              (geometricPivotStoppingLaw law deadline hazard hpositive hle))) responder ≤
        quittingContinuationBestResponseValue reward
          (quittingStoppingLawProfile reward (Function.update opponents pivot law)) responder := by
  by_cases htailZero : stoppingLawLateFiniteMass law (deadline - 1) = 0
  · refine ⟨1, by norm_num, by norm_num, ?_, ?_⟩
    · exact quittingTerminalPayoff_geometric_pivot_eq reward opponents pivot deadline hfinite
        law 1 (by norm_num) (by norm_num)
    · intro responder
      rw [geometricPivotStoppingLaw_eq_of_lateFiniteMass_eq_zero law hdeadline htailZero]
  · have htail : 0 < stoppingLawLateFiniteMass law (deadline - 1) := by
      exact lt_of_le_of_ne (pmfFiniteComplementMass_nonneg law
        (stoppingLawFinitePrefix (deadline - 1))) (Ne.symm htailZero)
    obtain ⟨first, hfirst, hfirstPositive, hzero⟩ :=
      exists_first_positive_late_stoppingAtom law hdeadline htail
    let hazard := (law (some first)).toReal / stoppingLawLateFiniteMass law (deadline - 1)
    have hpositive : 0 < hazard :=
      (late_stoppingAtom_div_tail_mem_Ioc law hdeadline hfirst hfirstPositive).1
    have hle : hazard ≤ 1 :=
      (late_stoppingAtom_div_tail_mem_Ioc law hdeadline hfirst hfirstPositive).2
    have hmatch : stoppingLawLateFiniteMass law (deadline - 1) * hazard =
        (law (some first)).toReal := by
      dsimp only [hazard]
      field_simp
    refine ⟨hazard, hpositive, hle,
      quittingTerminalPayoff_geometric_pivot_eq reward opponents pivot deadline hfinite
        law hazard hpositive hle, ?_⟩
    intro responder
    by_cases hresponder : responder = pivot
    · subst responder
      exact le_of_eq
        (quittingContinuationBestResponseValue_stoppingLawProfile_update_self reward opponents pivot
          (geometricPivotStoppingLaw law deadline hazard hpositive hle) law)
    · exact quittingContinuationBestResponseValue_geometric_pivot_le reward opponents pivot
        responder hresponder deadline hdeadline hfinite law first hfirst hzero
        hazard hpositive hle hmatch

/-- The same actual geometric replacement preserves the prescribed payoff
vector and weakly lowers full terminal exploitability, for arbitrary signed
rewards and an arbitrary original complete pivot law. -/
theorem exists_geometric_pivot_payoff_eq_and_exploitability_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot : ι)
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (hfinite : ∀ j, j ≠ pivot → IsFiniteClockStoppingLaw deadline (opponents j))
    (law : PMF (Option ℕ)) :
    letI : Nonempty ι := ⟨pivot⟩
    ∃ (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1),
      quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward
            (Function.update opponents pivot
              (geometricPivotStoppingLaw law deadline hazard hpositive hle))) =
        quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (Function.update opponents pivot law)) ∧
      quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward
            (Function.update opponents pivot
              (geometricPivotStoppingLaw law deadline hazard hpositive hle))) ≤
        quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward (Function.update opponents pivot law)) := by
  letI : Nonempty ι := ⟨pivot⟩
  obtain ⟨hazard, hpositive, hle, hpayoff, hcaps⟩ :=
    exists_geometric_pivot_payoff_eq_and_caps_le
      reward opponents pivot deadline hdeadline hfinite law
  refine ⟨hazard, hpositive, hle, hpayoff, ?_⟩
  unfold quittingTerminalExploitability
  apply QuittingBoundaryHolonomy.finitePlayerMax_le
  intro who
  rw [hpayoff]
  exact (max_le_max_left 0 (sub_le_sub_right (hcaps who) _)).trans
    (QuittingBoundaryHolonomy.le_finitePlayerMax
      (fun player ↦ max 0 (quittingContinuationBestResponseValue reward
        (quittingStoppingLawProfile reward (Function.update opponents pivot law)) player -
        quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (Function.update opponents pivot law)) player)) who)

end GameTheory
