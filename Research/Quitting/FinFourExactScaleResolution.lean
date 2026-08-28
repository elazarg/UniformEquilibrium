/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourRationalSingleShellLower
import Research.Quitting.FinFourSingleShellUpperResolution
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityUniformPayoff

/-!
# Executable exact resolution of one normalized Fin4 scale

At a positive rational accuracy, this module runs two proof-free exact searches
at every natural-numbered stage.  It tests the rational finite-clock upper
enumerator first, then the rational interval-tree lower search.  Every emitted
object has an independent Boolean verifier and a semantic soundness theorem.

Classical compactness appears only in the proof that some finite stage emits a
certificate.  The stage function itself contains no choice, real comparison,
or noncomputable selection.  The equality boundary for the analytic shell
value is assigned to the upper branch in the completeness proof.  This does
not assert operational exclusivity: a lower tree proves a non-strict bound and
could also verify at equality.
-/

namespace GameTheory

open Math.Interval

/-- The exact shell level used to resolve the rational accuracy `epsilon`. -/
def finFourExactScaleLevel (epsilon : ℚ) : ℕ :=
  ⌊96 / epsilon⌋₊ + 1

/-- The selected shell level is positive for every input, including malformed
nonpositive accuracies on which no completeness claim is made. -/
theorem finFourExactScaleLevel_pos (epsilon : ℚ) :
    0 < finFourExactScaleLevel epsilon := by
  simp [finFourExactScaleLevel]

/-- The floor choice leaves the strict quantitative room required by the
single-shell upper resolver. -/
theorem finFourExactScale_bracket_gap
    {epsilon : ℚ} (hepsilon : 0 < epsilon) :
    24 / (finFourExactScaleLevel epsilon : ℝ) < (epsilon : ℝ) / 4 := by
  have hfloor := Nat.lt_floor_add_one (96 / epsilon : ℚ)
  have hlevelRat : (96 / epsilon : ℚ) <
      (finFourExactScaleLevel epsilon : ℚ) := by
    simpa only [finFourExactScaleLevel, Nat.cast_add, Nat.cast_one] using hfloor
  have hlevelRatPos : (0 : ℚ) < finFourExactScaleLevel epsilon := by
    exact_mod_cast finFourExactScaleLevel_pos epsilon
  have hproduct : (96 : ℚ) <
      (finFourExactScaleLevel epsilon : ℚ) * epsilon :=
    (div_lt_iff₀ hepsilon).mp hlevelRat
  have hgapRat : (24 : ℚ) / finFourExactScaleLevel epsilon < epsilon / 4 := by
    apply (div_lt_iff₀ hlevelRatPos).2
    nlinarith
  have hgapReal :
      ((((24 : ℚ) / finFourExactScaleLevel epsilon : ℚ)) : ℝ) <
        (((epsilon / 4 : ℚ)) : ℝ) := by
    exact_mod_cast hgapRat
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast,
    Nat.cast_ofNat] using hgapReal

/-- Exact interval-tree payload at the prescribed shell level. -/
abbrev FinFourExactScaleLowerTree (epsilon : ℚ) :=
  RationalLowerBoxTree
    (finFourSingleShellVariableCount (finFourExactScaleLevel epsilon))
    finFourSingleShellEqualityCount
    (finFourSingleShellNonnegativeCount (finFourExactScaleLevel epsilon))

/-- Proof-free result of one exact scale resolver.

The stored stage is provenance for the generating search.  It is not a proof
field and is checked by the stage-equation theorems below. -/
inductive FinFourExactScaleCertificate (epsilon : ℚ) where
  | upper (stage : ℕ) (code : RationalFinFourFiniteClockProfileCode)
  | lower (rounds : ℕ) (tree : FinFourExactScaleLowerTree epsilon)
deriving DecidableEq, Repr

namespace FinFourExactScaleCertificate

/-- Independent exact checker for a scale certificate. -/
def verifies (reward : RationalFinFourRewardCode) (epsilon : ℚ) :
    FinFourExactScaleCertificate epsilon → Bool
  | .upper _ code => code.verifiesUpper reward (3 * epsilon / 4)
  | .lower _ tree =>
      (finFourRationalSingleShellLowerProblem reward.value
        (finFourExactScaleLevel epsilon)).verifies (epsilon / 4) tree

end FinFourExactScaleCertificate

/-- One total executable stage of the exact resolver.

Both searches receive the same stage number, so neither can be starved.  The
upper check is deliberately first; this mirrors the non-strict upper case in
the termination proof without claiming that lower certificates are impossible
at equality. -/
def finFourExactScaleStep
    (reward : RationalFinFourRewardCode) (epsilon : ℚ) (stage : ℕ) :
    Option (FinFourExactScaleCertificate epsilon) :=
  match RationalFinFourFiniteClockProfileCode.checkedCandidateAt reward
      (3 * epsilon / 4) stage with
  | some code => some (.upper stage code)
  | none =>
      match (finFourRationalSingleShellLowerProblem reward.value
          (finFourExactScaleLevel epsilon)).search (epsilon / 4) stage with
      | some tree => some (.lower stage tree)
      | none => none

/-- Exact generator equation for an emitted upper certificate. -/
theorem finFourExactScaleStep_upper_iff
    (reward : RationalFinFourRewardCode) (epsilon : ℚ)
    (stage index : ℕ) (code : RationalFinFourFiniteClockProfileCode) :
    finFourExactScaleStep reward epsilon stage = some (.upper index code) ↔
      stage = index ∧
        RationalFinFourFiniteClockProfileCode.checkedCandidateAt reward
          (3 * epsilon / 4) stage = some code := by
  cases hupper : RationalFinFourFiniteClockProfileCode.checkedCandidateAt
      reward (3 * epsilon / 4) stage with
  | some found => simp [finFourExactScaleStep, hupper]
  | none =>
      cases hlower : (finFourRationalSingleShellLowerProblem reward.value
          (finFourExactScaleLevel epsilon)).search (epsilon / 4) stage with
      | some found => simp [finFourExactScaleStep, hupper, hlower]
      | none => simp [finFourExactScaleStep, hupper, hlower]

/-- Exact generator equation for an emitted lower certificate. -/
theorem finFourExactScaleStep_lower_iff
    (reward : RationalFinFourRewardCode) (epsilon : ℚ)
    (stage rounds : ℕ) (tree : FinFourExactScaleLowerTree epsilon) :
    finFourExactScaleStep reward epsilon stage = some (.lower rounds tree) ↔
      RationalFinFourFiniteClockProfileCode.checkedCandidateAt reward
          (3 * epsilon / 4) stage = none ∧
        stage = rounds ∧
        (finFourRationalSingleShellLowerProblem reward.value
            (finFourExactScaleLevel epsilon)).search
          (epsilon / 4) stage = some tree := by
  cases hupper : RationalFinFourFiniteClockProfileCode.checkedCandidateAt
      reward (3 * epsilon / 4) stage with
  | some found => simp [finFourExactScaleStep, hupper]
  | none =>
      cases hlower : (finFourRationalSingleShellLowerProblem reward.value
          (finFourExactScaleLevel epsilon)).search (epsilon / 4) stage with
      | some found => simp [finFourExactScaleStep, hupper, hlower]
      | none => simp [finFourExactScaleStep, hupper, hlower]

/-- Every generated certificate passes its independent exact checker. -/
theorem finFourExactScaleStep_verifies
    (reward : RationalFinFourRewardCode) (epsilon : ℚ) (stage : ℕ)
    (certificate : FinFourExactScaleCertificate epsilon)
    (hstep : finFourExactScaleStep reward epsilon stage = some certificate) :
    certificate.verifies reward epsilon = true := by
  cases certificate with
  | upper index code =>
      exact ((RationalFinFourFiniteClockProfileCode.checkedCandidateAt_eq_some_iff
          reward (3 * epsilon / 4) stage code).mp
          ((finFourExactScaleStep_upper_iff reward epsilon stage index code).mp
            hstep).2).2
  | lower rounds tree =>
      have hsearch :=
        ((finFourExactScaleStep_lower_iff reward epsilon stage rounds tree).mp
          hstep).2.2
      exact (finFourRationalSingleShellLowerProblem reward.value
        (finFourExactScaleLevel epsilon)).verifies_search
          (epsilon / 4) stage hsearch

/-- An emitted upper certificate decodes to an actual finite-clock behavioral
profile with unrestricted exploitability strictly below `3 * epsilon / 4`. -/
theorem finFourExactScaleStep_upper_sound
    (reward : RationalFinFourRewardCode) (epsilon : ℚ)
    (stage index : ℕ) (code : RationalFinFourFiniteClockProfileCode)
    (hstep : finFourExactScaleStep reward epsilon stage =
      some (.upper index code)) :
    ∃ hvalid : code.Valid,
      quittingTerminalExploitability reward.realReward
          (code.toBehaviorProfile reward hvalid) <
        ((3 * epsilon / 4 : ℚ) : ℝ) ∧
      ∃ laws : Fin 4 → PMF (Option ℕ),
        (∀ player, IsFiniteClockStoppingLaw code.clockBound (laws player)) ∧
        code.toBehaviorProfile reward hvalid =
          quittingStoppingLawProfile reward.realReward laws := by
  have hchecked :=
    ((finFourExactScaleStep_upper_iff reward epsilon stage index code).mp
      hstep).2
  exact RationalFinFourFiniteClockProfileCode.checkedCandidateAt_sound
    reward (3 * epsilon / 4) stage code hchecked

/-- An emitted lower certificate proves the requested lower bound on the
analytic single shell. -/
theorem finFourExactScaleStep_lower_shell_sound
    (reward : RationalFinFourRewardCode) (epsilon : ℚ)
    (hnormalized : reward.normalized = true)
    (stage rounds : ℕ) (tree : FinFourExactScaleLowerTree epsilon)
    (hstep : finFourExactScaleStep reward epsilon stage =
      some (.lower rounds tree)) :
    (epsilon : ℝ) / 4 ≤
      finFourSingleShellLower reward.realReward
        (reward.abs_realReward_le_one_of_normalized
          (reward.normalized_eq_true_iff.mp hnormalized))
        (finFourExactScaleLevel epsilon) := by
  have hsearch :=
    ((finFourExactScaleStep_lower_iff reward epsilon stage rounds tree).mp
      hstep).2.2
  let hreward : ∀ terminal player,
      |(reward.value terminal player : ℝ)| ≤ 1 := by
    simpa only [RationalFinFourRewardCode.realReward] using
      reward.abs_realReward_le_one_of_normalized
        (reward.normalized_eq_true_iff.mp hnormalized)
  have hsound := finFourRationalSingleShellSearch_sound reward.value hreward
    (finFourExactScaleLevel_pos epsilon) (epsilon / 4) stage hsearch
  change (epsilon : ℝ) / 4 ≤
    finFourSingleShellLower
      (fun terminal who ↦ (reward.value terminal who : ℝ)) hreward
        (finFourExactScaleLevel epsilon)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hsound

/-- An emitted lower certificate proves the same positive lower bound for the
global unrestricted behavioral exploitability infimum. -/
theorem finFourExactScaleStep_lower_infimum_sound
    (reward : RationalFinFourRewardCode) (epsilon : ℚ)
    (hnormalized : reward.normalized = true)
    (stage rounds : ℕ) (tree : FinFourExactScaleLowerTree epsilon)
    (hstep : finFourExactScaleStep reward epsilon stage =
      some (.lower rounds tree)) :
    (epsilon : ℝ) / 4 ≤
      quittingTerminalExploitabilityInf reward.realReward := by
  let hreward := reward.abs_realReward_le_one_of_normalized
    (reward.normalized_eq_true_iff.mp hnormalized)
  exact finFourSingleShellLower_le_exploitabilityInf reward.realReward hreward
    (finFourExactScaleLevel_pos epsilon)
    (finFourExactScaleStep_lower_shell_sound reward epsilon hnormalized
      stage rounds tree hstep)

/-- Reducing the certified non-strict lower bound to `epsilon / 8` produces a
literal attained terminal exploitability gap. -/
theorem finFourExactScaleStep_lower_terminalGap
    (reward : RationalFinFourRewardCode) {epsilon : ℚ}
    (hnormalized : reward.normalized = true) (hepsilon : 0 < epsilon)
    (stage rounds : ℕ) (tree : FinFourExactScaleLowerTree epsilon)
    (hstep : finFourExactScaleStep reward epsilon stage =
      some (.lower rounds tree)) :
    HasTerminalExploitabilityGap reward.realReward ((epsilon : ℝ) / 8) := by
  apply hasTerminalExploitabilityGap_of_lt_quittingTerminalExploitabilityInf
  have hinf := finFourExactScaleStep_lower_infimum_sound reward epsilon
    hnormalized stage rounds tree hstep
  have hepsilonReal : (0 : ℝ) < epsilon := by exact_mod_cast hepsilon
  linarith

/-- Every emitted lower certificate at a positive scale rules out a
uniform-equilibrium payoff for the encoded quitting game. -/
theorem finFourExactScaleStep_lower_no_uniformEquilibriumPayoff
    (reward : RationalFinFourRewardCode) {epsilon : ℚ}
    (hnormalized : reward.normalized = true) (hepsilon : 0 < epsilon)
    (stage rounds : ℕ) (tree : FinFourExactScaleLowerTree epsilon)
    (hstep : finFourExactScaleStep reward epsilon stage =
      some (.lower rounds tree)) :
    ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward.realReward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
    reward.realReward (show (0 : ℝ) < (epsilon : ℝ) / 8 by
      exact div_pos (by exact_mod_cast hepsilon) (by norm_num))
  exact finFourExactScaleStep_lower_terminalGap reward hnormalized hepsilon
    stage rounds tree hstep

/-- The explicit upper-first dovetail terminates at a finite stage for every
normalized rational Fin4 reward and every positive rational accuracy.

The proof splits at the exact analytic shell value.  The non-strict case,
including equality, uses the upper enumerator.  The strict complementary case
uses interval-search completeness. -/
theorem exists_finFourExactScaleStep
    (reward : RationalFinFourRewardCode) (epsilon : ℚ)
    (hnormalized : reward.normalized = true) (hepsilon : 0 < epsilon) :
    ∃ stage certificate,
      finFourExactScaleStep reward epsilon stage = some certificate := by
  let hreward := reward.abs_realReward_le_one_of_normalized
    (reward.normalized_eq_true_iff.mp hnormalized)
  let level := finFourExactScaleLevel epsilon
  by_cases hlower : finFourSingleShellLower reward.realReward hreward level ≤
      (epsilon : ℝ) / 4
  · obtain ⟨resolution⟩ := nonempty_finFourSingleShellUpperResolution
      reward epsilon hnormalized (finFourExactScaleLevel_pos epsilon)
      hlower (finFourExactScale_bracket_gap hepsilon)
    refine ⟨resolution.stage, .upper resolution.stage resolution.code, ?_⟩
    simp [finFourExactScaleStep, resolution.checked]
  · have hstrict : ((epsilon / 4 : ℚ) : ℝ) <
        finFourSingleShellLower reward.realReward hreward level := by
      rw [Rat.cast_div, Rat.cast_ofNat]
      exact lt_of_not_ge hlower
    obtain ⟨rounds, tree, hsearch, -⟩ :=
      exists_finFourRationalSingleShellSearch_of_lt_lower reward.value hreward
        level (epsilon / 4) hstrict
    cases hupper : RationalFinFourFiniteClockProfileCode.checkedCandidateAt
        reward (3 * epsilon / 4) rounds with
    | some code =>
        exact ⟨rounds, .upper rounds code, by
          simp [finFourExactScaleStep, hupper]⟩
    | none =>
        have hsearch' :
            (finFourRationalSingleShellLowerProblem reward.value
              (finFourExactScaleLevel epsilon)).search
                (epsilon / 4) rounds = some tree := by
          simpa only [level] using hsearch
        exact ⟨rounds, .lower rounds tree, by
          simp [finFourExactScaleStep, hupper, hsearch']⟩

/-- At a zero global exploitability infimum, no positive-scale lower
certificate can be emitted. -/
theorem finFourExactScaleStep_not_lower_of_infimum_eq_zero
    (reward : RationalFinFourRewardCode) {epsilon : ℚ}
    (hnormalized : reward.normalized = true) (hepsilon : 0 < epsilon)
    (hinfimum : quittingTerminalExploitabilityInf reward.realReward = 0)
    (stage rounds : ℕ) (tree : FinFourExactScaleLowerTree epsilon) :
    finFourExactScaleStep reward epsilon stage ≠
      some (.lower rounds tree) := by
  intro hstep
  have hlower := finFourExactScaleStep_lower_infimum_sound reward epsilon
    hnormalized stage rounds tree hstep
  rw [hinfimum] at hlower
  have hepsilonReal : (0 : ℝ) < epsilon := by exact_mod_cast hepsilon
  linarith

/-- A zero global exploitability infimum forces the terminating exact-scale
event to be an upper certificate at every positive rational accuracy. -/
theorem exists_finFourExactScaleStep_upper_of_infimum_eq_zero
    (reward : RationalFinFourRewardCode) (epsilon : ℚ)
    (hnormalized : reward.normalized = true) (hepsilon : 0 < epsilon)
    (hinfimum : quittingTerminalExploitabilityInf reward.realReward = 0) :
    ∃ stage index code,
      finFourExactScaleStep reward epsilon stage =
        some (.upper index code) := by
  obtain ⟨stage, certificate, hstep⟩ :=
    exists_finFourExactScaleStep reward epsilon hnormalized hepsilon
  cases certificate with
  | upper index code => exact ⟨stage, index, code, hstep⟩
  | lower rounds tree =>
      exact False.elim
        (finFourExactScaleStep_not_lower_of_infimum_eq_zero reward
          hnormalized hepsilon hinfimum stage rounds tree hstep)

/-- The forced upper event at a zero global infimum literally decodes to an
actual finite-clock behavioral profile at the requested scale. -/
theorem exists_finFourExactScaleStep_upper_profile_of_infimum_eq_zero
    (reward : RationalFinFourRewardCode) (epsilon : ℚ)
    (hnormalized : reward.normalized = true) (hepsilon : 0 < epsilon)
    (hinfimum : quittingTerminalExploitabilityInf reward.realReward = 0) :
    ∃ stage index code, ∃ hvalid : code.Valid,
      finFourExactScaleStep reward epsilon stage =
          some (.upper index code) ∧
        quittingTerminalExploitability reward.realReward
            (code.toBehaviorProfile reward hvalid) <
          ((3 * epsilon / 4 : ℚ) : ℝ) ∧
        ∃ laws : Fin 4 → PMF (Option ℕ),
          (∀ player, IsFiniteClockStoppingLaw code.clockBound (laws player)) ∧
          code.toBehaviorProfile reward hvalid =
            quittingStoppingLawProfile reward.realReward laws := by
  obtain ⟨stage, index, code, hstep⟩ :=
    exists_finFourExactScaleStep_upper_of_infimum_eq_zero reward epsilon
      hnormalized hepsilon hinfimum
  obtain ⟨hvalid, hexploitability, laws, hfinite, hprofile⟩ :=
    finFourExactScaleStep_upper_sound reward epsilon stage index code hstep
  exact ⟨stage, index, code, hvalid, hstep, hexploitability,
    laws, hfinite, hprofile⟩

/-- There is a positive rational exact-search accuracy whose upper threshold
is below any prescribed positive real value. -/
theorem exists_finFourExactScaleAccuracy_three_quarters_lt
    {value : ℝ} (hvalue : 0 < value) :
    ∃ epsilon : ℚ,
      0 < epsilon ∧ 3 * (epsilon : ℝ) / 4 < value := by
  obtain ⟨index, hindex⟩ : ∃ index : ℕ, (1 / 2 : ℝ) ^ index < value :=
    exists_pow_lt_of_lt_one hvalue (by norm_num)
  let epsilon : ℚ := (1 / 2 : ℚ) ^ index
  refine ⟨epsilon, by dsimp only [epsilon]; positivity, ?_⟩
  have hepsilon : (epsilon : ℝ) = (1 / 2 : ℝ) ^ index := by
    simp [epsilon]
  rw [hepsilon]
  have hpositive : (0 : ℝ) < (1 / 2 : ℝ) ^ index := by positivity
  linarith

/-- At zero global exploitability infimum, actual finite-clock behavioral
profiles have arbitrarily small literal unrestricted exploitability.  The
profile is allowed to depend on the requested error. -/
theorem finFourExactScale_profiles_all_errors_of_infimum_eq_zero
    (reward : RationalFinFourRewardCode)
    (hnormalized : reward.normalized = true)
    (hinfimum : quittingTerminalExploitabilityInf reward.realReward = 0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ profile : (quittingGame reward.realReward).BehaviorProfile,
        quittingTerminalExploitability reward.realReward profile < delta := by
  intro delta hdelta
  obtain ⟨epsilon, hepsilon, hthreshold⟩ :=
    exists_finFourExactScaleAccuracy_three_quarters_lt hdelta
  obtain ⟨-, -, code, hvalid, -, hexploitability, -⟩ :=
    exists_finFourExactScaleStep_upper_profile_of_infimum_eq_zero reward
      epsilon hnormalized hepsilon hinfimum
  have hcast : (((3 * epsilon / 4 : ℚ) : ℝ)) =
      3 * (epsilon : ℝ) / 4 := by norm_num
  rw [hcast] at hexploitability
  exact ⟨code.toBehaviorProfile reward hvalid,
    hexploitability.trans hthreshold⟩

/-- The semantic zero branch of exact scale resolution selects one fixed
uniform-equilibrium payoff.  Only the approximating profiles vary with the
requested error. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_finFourExactScale_infimum_eq_zero
    (reward : RationalFinFourRewardCode)
    (hnormalized : reward.normalized = true)
    (hinfimum : quittingTerminalExploitabilityInf reward.realReward = 0) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward.realReward).IsUniformEquilibriumPayoff none payoff := by
  exact
    quittingGame_exists_uniformEquilibriumPayoff_of_terminalExploitability_all_errors
      reward.realReward
      (finFourExactScale_profiles_all_errors_of_infimum_eq_zero reward
        hnormalized hinfimum)

/-- A positive global exploitability infimum forces a literal lower event at
some positive exact-search scale. -/
theorem exists_finFourExactScaleStep_lower_of_infimum_pos
    (reward : RationalFinFourRewardCode)
    (hnormalized : reward.normalized = true)
    (hpositive : 0 < quittingTerminalExploitabilityInf reward.realReward) :
    ∃ (epsilon : ℚ) (stage rounds : ℕ)
        (tree : FinFourExactScaleLowerTree epsilon),
      0 < epsilon ∧
        3 * (epsilon : ℝ) / 4 <
          quittingTerminalExploitabilityInf reward.realReward ∧
        finFourExactScaleStep reward epsilon stage =
          some (.lower rounds tree) := by
  obtain ⟨epsilon, hepsilon, hthreshold⟩ :=
    exists_finFourExactScaleAccuracy_three_quarters_lt hpositive
  obtain ⟨stage, certificate, hstep⟩ :=
    exists_finFourExactScaleStep reward epsilon hnormalized hepsilon
  cases certificate with
  | upper index code =>
      obtain ⟨hvalid, hexploitability, -⟩ :=
        finFourExactScaleStep_upper_sound reward epsilon stage index code hstep
      have hinfimum := quittingTerminalExploitabilityInf_le reward.realReward
        (code.toBehaviorProfile reward hvalid)
      have hcast : (((3 * epsilon / 4 : ℚ) : ℝ)) =
          3 * (epsilon : ℝ) / 4 := by norm_num
      rw [hcast] at hexploitability
      exact False.elim (by linarith)
  | lower rounds tree =>
      exact ⟨epsilon, stage, rounds, tree, hepsilon, hthreshold, hstep⟩

/-- Literal semantic dichotomy behind exact scale resolution for a normalized
rational Fin4 table: zero infimum yields one fixed uniform-equilibrium payoff;
positive infimum yields a finite lower-search event. -/
theorem finFourExactScale_infimum_zero_or_lower_event
    (reward : RationalFinFourRewardCode)
    (hnormalized : reward.normalized = true) :
    (quittingTerminalExploitabilityInf reward.realReward = 0 ∧
      ∃ payoff : Payoff (Fin 4),
        (quittingGame reward.realReward).IsUniformEquilibriumPayoff none payoff) ∨
    (0 < quittingTerminalExploitabilityInf reward.realReward ∧
      ∃ (epsilon : ℚ) (stage rounds : ℕ)
          (tree : FinFourExactScaleLowerTree epsilon),
        0 < epsilon ∧
          3 * (epsilon : ℝ) / 4 <
            quittingTerminalExploitabilityInf reward.realReward ∧
          finFourExactScaleStep reward epsilon stage =
            some (.lower rounds tree)) := by
  have hinfimumNonnegative :
      0 ≤ quittingTerminalExploitabilityInf reward.realReward := by
    unfold quittingTerminalExploitabilityInf
    apply le_csInf (Set.range_nonempty _)
    rintro value ⟨profile, rfl⟩
    exact quittingTerminalExploitability_nonneg reward.realReward profile
  rcases hinfimumNonnegative.eq_or_lt with hinfimum | hpositive
  · exact Or.inl ⟨hinfimum.symm,
      quittingGame_exists_uniformEquilibriumPayoff_of_finFourExactScale_infimum_eq_zero
        reward hnormalized hinfimum.symm⟩
  · exact Or.inr ⟨hpositive,
      exists_finFourExactScaleStep_lower_of_infimum_pos reward hnormalized
        hpositive⟩

end GameTheory
