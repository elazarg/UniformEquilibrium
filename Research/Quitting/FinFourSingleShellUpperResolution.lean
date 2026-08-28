/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourRationalFiniteClockProfileCompleteness
import Research.Quitting.FinFourSingleShellOuter

/-!
# Upper-search resolution from one normalized Fin4 shell

The analytic one-shell upper value is attained by an actual independent
finite-clock stopping-law profile.  If the corresponding shell lower value is
at most `epsilon / 4` and the exact bracket width `24 / level` is strictly less
than `epsilon / 4`, that profile has unrestricted exploitability strictly less
than `3 * epsilon / 4`.  Rational finite-clock profile completeness then puts a
checked upper certificate at a finite stage of the explicit enumeration.

This module imports only the analytic single-shell bracket and the upper-search
completeness theorem.  It does not import or assume the moving executable lower
adapter.
-/

noncomputable section

namespace GameTheory

open FinFourRationalFiniteClockProfileCompleteness

namespace RationalFinFourRewardCode

/-- Every exact coordinate read from a normalized proof-free Fin4 reward code
lies in the rational unit interval.  The total malformed-code fallbacks are
zero and satisfy the same bound. -/
theorem abs_value_le_one_of_normalized
    (reward : RationalFinFourRewardCode) (hnormalized : reward.Normalized)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (observer : Fin 4) :
    |reward.value terminal observer| ≤ 1 := by
  unfold value
  cases hrow : reward.rows[(terminalMask terminal.1 - 1)]? with
  | none => simp
  | some row =>
      have hrowMem : row ∈ reward.rows := by
        obtain ⟨hindex, hrowValue⟩ := List.getElem?_eq_some_iff.mp hrow
        rw [← hrowValue]
        exact List.getElem_mem hindex
      cases hentry : row[observer.val]? with
      | none => simp [hentry]
      | some entry =>
          have hentryMem : entry ∈ row := by
            obtain ⟨hindex, hentryValue⟩ :=
              List.getElem?_eq_some_iff.mp hentry
            rw [← hentryValue]
            exact List.getElem_mem hindex
          simpa [hrow, hentry] using
            hnormalized.2 row hrowMem entry hentryMem

/-- Real reward coordinates of a normalized exact code satisfy the unit bound
required by the Fin4 shell bracket. -/
theorem abs_realReward_le_one_of_normalized
    (reward : RationalFinFourRewardCode) (hnormalized : reward.Normalized)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (observer : Fin 4) :
    |reward.realReward terminal observer| ≤ 1 := by
  change |(reward.value terminal observer : ℝ)| ≤ 1
  exact_mod_cast reward.abs_value_le_one_of_normalized hnormalized
    terminal observer

end RationalFinFourRewardCode

/-- Actual finite-clock profile and finite rational enumeration stage supplied
by the upper arm of one exact shell resolution. -/
structure FinFourSingleShellUpperResolution
    (reward : RationalFinFourRewardCode) (epsilon : ℚ) (level : ℕ) where
  laws : Fin 4 → PMF (Option ℕ)
  finite_clock : ∀ player,
    IsFiniteClockStoppingLaw (8 * level + 1) (laws player)
  exploitability_lt :
    quittingTerminalExploitability reward.realReward
        (quittingStoppingLawProfile reward.realReward laws) <
      ((3 * epsilon / 4 : ℚ) : ℝ)
  stage : ℕ
  code : RationalFinFourFiniteClockProfileCode
  checked :
    RationalFinFourFiniteClockProfileCode.checkedCandidateAt reward
      (3 * epsilon / 4) stage = some code
  code_clockBound : code.clockBound = 8 * level + 1

/-- The exact single-shell upper arm terminates at a finite rational upper
certificate.  Both input inequalities remain strict/non-strict exactly as
advertised; no equality boundary is silently reassigned to the lower arm. -/
theorem nonempty_finFourSingleShellUpperResolution
    (reward : RationalFinFourRewardCode) (epsilon : ℚ)
    (hnormalized : reward.normalized = true)
    {level : ℕ} (hlevel : 0 < level)
    (hlower : finFourSingleShellLower reward.realReward
        (reward.abs_realReward_le_one_of_normalized
          (reward.normalized_eq_true_iff.mp hnormalized)) level ≤
      (epsilon : ℝ) / 4)
    (hgap : 24 / (level : ℝ) < (epsilon : ℝ) / 4) :
    Nonempty (FinFourSingleShellUpperResolution reward epsilon level) := by
  let hreward : ∀ terminal observer,
      |reward.realReward terminal observer| ≤ 1 :=
    reward.abs_realReward_le_one_of_normalized
      (reward.normalized_eq_true_iff.mp hnormalized)
  let compression :=
    hasEscapeAwareQuantileClockCompression_of_normalized
      reward.realReward hreward
  obtain ⟨pair, hpair, hpairValue⟩ :=
    exists_finiteClockSemanticPair_exploitability_eq_upper
      reward.realReward compression level
  obtain ⟨laws, hlaws, hpairEq⟩ := hpair
  rw [quantileClockSupport_fin4] at hlaws
  have hbracket := finFourSingleShell_quantitative_bracket
    reward.realReward hreward hlevel
  have hupperLtHalf :
      escapeAwareQuantileClockUpper reward.realReward compression level <
        (epsilon : ℝ) / 2 := by
    have hlower' :
        finFourSingleShellLower reward.realReward hreward level ≤
          (epsilon : ℝ) / 4 := by
      exact hlower
    linarith [hbracket.2.2]
  have hepsilonPos : (0 : ℝ) < epsilon := by
    have hpositive : (0 : ℝ) < 24 / (level : ℝ) := by
      positivity
    linarith
  have hprofileExploitability :
      quittingTerminalExploitability reward.realReward
          (quittingStoppingLawProfile reward.realReward laws) <
        ((3 * epsilon / 4 : ℚ) : ℝ) := by
    have hpairExploitability :
        quittingTerminalSemanticExploitability pair =
          quittingTerminalExploitability reward.realReward
            (quittingStoppingLawProfile reward.realReward laws) := by
      rw [hpairEq, quittingTerminalSemanticExploitability_pair]
    rw [← hpairExploitability, hpairValue]
    norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    linarith
  obtain ⟨stage, code, hchecked, hcodeClock, -⟩ :=
    exists_checkedCandidateAt_of_finiteClockStoppingLaws reward
      (3 * epsilon / 4) hnormalized (8 * level + 1) (by positivity)
      laws hlaws hprofileExploitability
  exact ⟨⟨laws, hlaws, hprofileExploitability, stage, code,
    hchecked, hcodeClock⟩⟩

end GameTheory
