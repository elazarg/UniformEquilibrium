/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNonnegativeWeightChamber
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn

/-!
# A joint-law certificate for the nonnegative-weight chamber

At a positive ordinary total-debt minimum, the complete terminal law of one
joint carrier lift assigns an atom a uniformly averaged share of the weighted
surplus above own-singleton rewards.  This is a finite-law certificate.  It
does not select a source prefix, a behavioral return, or a renewal edge.

No sparse-support or sparse-reward-boundary conclusion is defined here.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- One outcome in the displayed joint-carrier law carries the uniform
average of the sharp nonnegative-weight surplus. -/
theorem exists_terminalOutcome_weightedSurplusContribution_ge_minimumDebt
    (point : QuittingTerminalSemanticLawPoint ι) (weight : ι → ℝ)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum point.1)
    (hweight : ∀ who, 0 ≤ weight who) :
    ∃ outcome : QuittingTerminalOutcome ι,
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum point.1 /
          Fintype.card (QuittingTerminalOutcome ι) ≤
        point.2 outcome *
          (quittingWeightedTerminalOutcomeReward reward weight outcome -
            quittingWeightedSingletonReward reward weight) := by
  have hpair := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hlower := minimumTerminalSemantic_nonnegativeWeight_lowerBound
    point.1 weight hpair hminimum hpositive hweight
  have hmass := terminalSemanticLawCarrier_mass_mem_stdSimplex point hpoint
  have hmoment := terminalSemanticLawCarrier_rewardMoment reward point hpoint
  let contribution : QuittingTerminalOutcome ι → ℝ := fun outcome =>
    point.2 outcome *
      (quittingWeightedTerminalOutcomeReward reward weight outcome -
        quittingWeightedSingletonReward reward weight)
  have hsum : quittingPlayerWeightOffMaximum weight *
        quittingTerminalSemanticDebtSum point.1 ≤
      ∑ outcome, contribution outcome := by
    have hweightedMoment :
        (∑ outcome, point.2 outcome *
            quittingWeightedTerminalOutcomeReward reward weight outcome) =
          quittingTerminalSemanticWeightedPrescribed weight point.1 := by
      unfold quittingWeightedTerminalOutcomeReward
        quittingTerminalSemanticWeightedPrescribed
      calc
        (∑ outcome, point.2 outcome *
            ∑ who, weight who *
              quittingTerminalOutcomeReward reward outcome who) =
            ∑ who, weight who *
              (∑ outcome, point.2 outcome *
                quittingTerminalOutcomeReward reward outcome who) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro who _
          apply Finset.sum_congr rfl
          intro outcome _
          ring
        _ = ∑ who, weight who * point.1.1 who := by
          apply Finset.sum_congr rfl
          intro who _
          have hcoordinate := congrFun hmoment who
          unfold quittingTerminalRewardMoment at hcoordinate
          rw [hcoordinate]
    have hconstant :
        (∑ outcome, point.2 outcome *
            quittingWeightedSingletonReward reward weight) =
          quittingWeightedSingletonReward reward weight := by
      rw [← Finset.sum_mul, hmass.2, one_mul]
    dsimp only [contribution]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hweightedMoment, hconstant]
    linarith
  have hcardPos :
      0 < (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  by_contra hnone
  push Not at hnone
  have hsumLt : (∑ outcome, contribution outcome) <
      ∑ _outcome : QuittingTerminalOutcome ι,
        quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum point.1 /
          Fintype.card (QuittingTerminalOutcome ι) := by
    apply Finset.sum_lt_sum
    · intro outcome _
      exact (hnone outcome).le
    · exact ⟨none, Finset.mem_univ none, hnone none⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsumLt
  have haverage :
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          (quittingPlayerWeightOffMaximum weight *
              quittingTerminalSemanticDebtSum point.1 /
            Fintype.card (QuittingTerminalOutcome ι)) =
        quittingPlayerWeightOffMaximum weight *
          quittingTerminalSemanticDebtSum point.1 := by
    field_simp
  linarith

/-- Under a uniform reward bound and a nonnegative weighted singleton value,
the selected atom is a finite coalition.  Its weighted surplus and its law
mass have the literal quantitative floors forced by the minimum debt. -/
theorem exists_terminalLawFiniteAtom_weightedSurplus_and_mass_ge
    (point : QuittingTerminalSemanticLawPoint ι) (weight : ι → ℝ)
    (first second : ι) (hne : first ≠ second)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum point.1)
    (hweight : ∀ who, 0 ≤ weight who)
    (hfirst : 0 < weight first) (hsecond : 0 < weight second)
    {R : ℝ} (hR : 0 < R)
    (hreward : ∀ terminal who, |reward terminal who| ≤ R)
    (hsingleton : 0 ≤ quittingWeightedSingletonReward reward weight) :
    ∃ terminal : {S : Finset ι // S.Nonempty},
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum point.1 /
          Fintype.card (QuittingTerminalOutcome ι) ≤
        point.2 (some terminal) *
          (quittingWeightedTerminalOutcomeReward reward weight
              (some terminal) -
            quittingWeightedSingletonReward reward weight) ∧
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum point.1 /
          Fintype.card (QuittingTerminalOutcome ι) ≤
        quittingWeightedTerminalOutcomeReward reward weight
            (some terminal) -
          quittingWeightedSingletonReward reward weight ∧
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum point.1 /
          (R * quittingPlayerWeightTotal weight *
            Fintype.card (QuittingTerminalOutcome ι)) ≤
        point.2 (some terminal) := by
  have hgap := quittingPlayerWeightOffMaximum_pos_of_two_positive
    weight first second hne hweight hfirst hsecond
  obtain ⟨outcome, hproduct⟩ :=
    exists_terminalOutcome_weightedSurplusContribution_ge_minimumDebt
      point weight hpoint hminimum hpositive hweight
  have hmass := terminalSemanticLawCarrier_mass_mem_stdSimplex point hpoint
  have hcardPos :
      0 < (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have haveragePos : 0 <
      quittingPlayerWeightOffMaximum weight *
          quittingTerminalSemanticDebtSum point.1 /
        Fintype.card (QuittingTerminalOutcome ι) :=
    div_pos (mul_pos hgap hpositive) hcardPos
  let surplus :=
    quittingWeightedTerminalOutcomeReward reward weight outcome -
      quittingWeightedSingletonReward reward weight
  have hmassNonneg : 0 ≤ point.2 outcome := hmass.1 outcome
  have hproductPos : 0 < point.2 outcome * surplus :=
    haveragePos.trans_le hproduct
  have hsurplusPos : 0 < surplus := by
    by_contra hnot
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos
      hmassNonneg (le_of_not_gt hnot))) hproductPos
  have hmassLeOne : point.2 outcome ≤ 1 := by
    calc
      point.2 outcome ≤ ∑ candidate, point.2 candidate := by
        exact Finset.single_le_sum (fun candidate _ => hmass.1 candidate)
          (Finset.mem_univ outcome)
      _ = 1 := hmass.2
  have hsurplusFloor :
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum point.1 /
          Fintype.card (QuittingTerminalOutcome ι) ≤ surplus := by
    calc
      _ ≤ point.2 outcome * surplus := hproduct
      _ ≤ 1 * surplus :=
        mul_le_mul_of_nonneg_right hmassLeOne hsurplusPos.le
      _ = surplus := one_mul _
  cases outcome with
  | none =>
      have hsurplusNonpos : surplus ≤ 0 := by
        dsimp only [surplus]
        simpa [quittingWeightedTerminalOutcomeReward,
          quittingTerminalOutcomeReward] using neg_nonpos.mpr hsingleton
      exact False.elim ((not_lt_of_ge hsurplusNonpos) hsurplusPos)
  | some terminal =>
      have htotalPos : 0 < quittingPlayerWeightTotal weight := by
        have hfirstLe : weight first ≤ ∑ who, weight who := by
          exact Finset.single_le_sum (fun who _ => hweight who)
            (Finset.mem_univ first)
        unfold quittingPlayerWeightTotal
        linarith
      have houtcomeUpper :
          quittingWeightedTerminalOutcomeReward reward weight
              (some terminal) ≤
            R * quittingPlayerWeightTotal weight := by
        unfold quittingWeightedTerminalOutcomeReward
          quittingPlayerWeightTotal
        calc
          (∑ who, weight who *
              quittingTerminalOutcomeReward reward (some terminal) who) ≤
              ∑ who, weight who * R := by
            exact Finset.sum_le_sum fun who _ =>
              mul_le_mul_of_nonneg_left
                (by
                  simpa [quittingTerminalOutcomeReward] using
                    (abs_le.mp (hreward terminal who)).2)
                (hweight who)
          _ = R * ∑ who, weight who := by
            rw [← Finset.sum_mul]
            ring
      have hsurplusUpper : surplus ≤
          R * quittingPlayerWeightTotal weight := by
        dsimp only [surplus]
        linarith
      have hdenomPos : 0 <
          R * quittingPlayerWeightTotal weight *
            (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
        positivity
      have hmassFloor :
          quittingPlayerWeightOffMaximum weight *
                quittingTerminalSemanticDebtSum point.1 /
              (R * quittingPlayerWeightTotal weight *
                Fintype.card (QuittingTerminalOutcome ι)) ≤
            point.2 (some terminal) := by
        apply (div_le_iff₀ hdenomPos).2
        have hscaled := (div_le_iff₀ hcardPos).1 hproduct
        have hproductUpper : point.2 (some terminal) * surplus ≤
            point.2 (some terminal) *
              (R * quittingPlayerWeightTotal weight) :=
          mul_le_mul_of_nonneg_left hsurplusUpper hmassNonneg
        calc
          quittingPlayerWeightOffMaximum weight *
                quittingTerminalSemanticDebtSum point.1 ≤
              (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
                (point.2 (some terminal) * surplus) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
          _ ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
                (point.2 (some terminal) *
                  (R * quittingPlayerWeightTotal weight)) :=
            mul_le_mul_of_nonneg_left hproductUpper hcardPos.le
          _ = point.2 (some terminal) *
                (R * quittingPlayerWeightTotal weight *
                  Fintype.card (QuittingTerminalOutcome ι)) := by ring
      exact ⟨terminal, hproduct, hsurplusFloor, hmassFloor⟩

/-- A supplied positive ordinary minimum has an actual subsequential joint-law
lift carrying the finite weighted-surplus atom and its quantitative mass
floor. The conclusion retains the selected law; it does not assert that one
behavioral profile attains it. -/
theorem minimumTerminalSemantic_exists_jointLawLiftFiniteAtom_weightedSurplus_and_mass_ge
    (pair : QuittingTerminalSemanticPair ι) (weight : ι → ℝ)
    (first second : ι) (hne : first ≠ second)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hweight : ∀ who, 0 ≤ weight who)
    (hfirst : 0 < weight first) (hsecond : 0 < weight second)
    {R : ℝ} (hR : 0 < R)
    (hreward : ∀ terminal who, |reward terminal who| ≤ R)
    (hsingleton : 0 ≤ quittingWeightedSingletonReward reward weight) :
    ∃ (mass : QuittingTerminalOutcome ι → ℝ)
        (terminal : {S : Finset ι // S.Nonempty}),
      (pair, mass) ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum pair /
          Fintype.card (QuittingTerminalOutcome ι) ≤
        mass (some terminal) *
          (quittingWeightedTerminalOutcomeReward reward weight
              (some terminal) -
            quittingWeightedSingletonReward reward weight) ∧
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum pair /
          Fintype.card (QuittingTerminalOutcome ι) ≤
        quittingWeightedTerminalOutcomeReward reward weight
            (some terminal) -
          quittingWeightedSingletonReward reward weight ∧
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum pair /
          (R * quittingPlayerWeightTotal weight *
            Fintype.card (QuittingTerminalOutcome ι)) ≤
        mass (some terminal) := by
  obtain ⟨mass, hlift⟩ :=
    exists_terminalSemanticLawCarrier_lift reward pair hpair
  obtain ⟨terminal, hproduct, hsurplus, hmass⟩ :=
    exists_terminalLawFiniteAtom_weightedSurplus_and_mass_ge
      (pair, mass) weight first second hne hlift hminimum hpositive hweight
        hfirst hsecond hR hreward hsingleton
  exact ⟨mass, terminal, hlift, hproduct, hsurplus, hmass⟩

/-- For four players and total weight one, the finite-law certificate has
the literal factors `16` and `16 * R`. -/
theorem exists_finFourTerminalLawFiniteAtom_weightedSurplus_and_mass_ge
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (point : QuittingTerminalSemanticLawPoint (Fin 4))
    (weight : Fin 4 → ℝ) (first second : Fin 4) (hne : first ≠ second)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum point.1)
    (hweight : ∀ who, 0 ≤ weight who)
    (hfirst : 0 < weight first) (hsecond : 0 < weight second)
    (htotal : quittingPlayerWeightTotal weight = 1)
    {R : ℝ} (hR : 0 < R)
    (hreward : ∀ terminal who, |reward terminal who| ≤ R)
    (hsingleton : 0 ≤ quittingWeightedSingletonReward reward weight) :
    ∃ terminal : {S : Finset (Fin 4) // S.Nonempty},
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum point.1 / 16 ≤
        point.2 (some terminal) *
          (quittingWeightedTerminalOutcomeReward reward weight
              (some terminal) -
            quittingWeightedSingletonReward reward weight) ∧
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum point.1 / 16 ≤
        quittingWeightedTerminalOutcomeReward reward weight
            (some terminal) -
          quittingWeightedSingletonReward reward weight ∧
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum point.1 /
          (16 * R) ≤ point.2 (some terminal) := by
  obtain ⟨terminal, hproduct, hsurplus, hmass⟩ :=
    exists_terminalLawFiniteAtom_weightedSurplus_and_mass_ge
      point weight first second hne hpoint hminimum hpositive hweight
        hfirst hsecond hR hreward hsingleton
  have hcard : Fintype.card (QuittingTerminalOutcome (Fin 4)) = 16 := by
    decide
  refine ⟨terminal, ?_, ?_, ?_⟩
  · simpa only [hcard, Nat.cast_ofNat] using hproduct
  · simpa only [hcard, Nat.cast_ofNat] using hsurplus
  · convert hmass using 1
    simp only [hcard, Nat.cast_ofNat, htotal]
    ring

/-- Fin4 corollary with the symmetric reward-bound denominator. The preceding
theorem records the stronger mass floor available from the same nonnegative
singleton hypothesis. -/
theorem exists_finFourTerminalLawFiniteAtom_weightedSurplus_and_mass_ge_symmetricRewardBound
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (point : QuittingTerminalSemanticLawPoint (Fin 4))
    (weight : Fin 4 → ℝ) (first second : Fin 4) (hne : first ≠ second)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum point.1)
    (hweight : ∀ who, 0 ≤ weight who)
    (hfirst : 0 < weight first) (hsecond : 0 < weight second)
    (htotal : quittingPlayerWeightTotal weight = 1)
    {R : ℝ} (hR : 0 < R)
    (hreward : ∀ terminal who, |reward terminal who| ≤ R)
    (hsingleton : 0 ≤ quittingWeightedSingletonReward reward weight) :
    ∃ terminal : {S : Finset (Fin 4) // S.Nonempty},
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum point.1 / 16 ≤
        point.2 (some terminal) *
          (quittingWeightedTerminalOutcomeReward reward weight
              (some terminal) -
            quittingWeightedSingletonReward reward weight) ∧
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum point.1 / 16 ≤
        quittingWeightedTerminalOutcomeReward reward weight
            (some terminal) -
          quittingWeightedSingletonReward reward weight ∧
      quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum point.1 /
          (32 * R) ≤ point.2 (some terminal) := by
  obtain ⟨terminal, hproduct, hsurplus, hmass⟩ :=
    exists_finFourTerminalLawFiniteAtom_weightedSurplus_and_mass_ge
      reward point weight first second hne hpoint hminimum hpositive hweight
        hfirst hsecond htotal hR hreward hsingleton
  refine ⟨terminal, hproduct, hsurplus, ?_⟩
  have hmassSimplex :=
    terminalSemanticLawCarrier_mass_mem_stdSimplex point hpoint
  have hmassNonneg : 0 ≤ point.2 (some terminal) :=
    hmassSimplex.1 (some terminal)
  have hdenomStrong : 0 < 16 * R := mul_pos (by norm_num) hR
  have hdenomWeak : 0 < 32 * R := mul_pos (by norm_num) hR
  apply (div_le_iff₀ hdenomWeak).2
  have hscaled := (div_le_iff₀ hdenomStrong).1 hmass
  calc
    quittingPlayerWeightOffMaximum weight *
          quittingTerminalSemanticDebtSum point.1 ≤
        (16 * R) * point.2 (some terminal) := by
      simpa only [mul_comm] using hscaled
    _ ≤ (32 * R) * point.2 (some terminal) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith) hmassNonneg
    _ = point.2 (some terminal) * (32 * R) := by ring

end GameTheory
