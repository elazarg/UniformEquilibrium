import Mathlib.Analysis.SpecificLimits.Basic
import UniformEquilibrium.Quitting.Paths.CommonQuantileClockApproximation

/-! # Actual independent finite-clock sources with full behavioral regret bounds -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Internally select independent complete stopping laws at the common-quantile rate.
The bound is on full behavioral exploitability, not only replies in the finite clock menu. -/
theorem exists_finiteClockStoppingLaws_exploitability_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {level : ℕ} (hlevel : 0 < level) :
    ∃ laws : ι → PMF (Option ℕ),
      (∀ who, IsFiniteClockStoppingLaw (quantileClockSupport ι level) (laws who)) ∧
      quittingTerminalExploitabilityInf reward ≤
        quittingTerminalExploitability reward (quittingStoppingLawProfile reward laws) ∧
      quittingTerminalExploitability reward (quittingStoppingLawProfile reward laws) ≤
        quittingTerminalExploitabilityInf reward + 2 * quantileClockRadius ι level ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
        (quittingTerminalExploitabilityInf reward + 2 * quantileClockRadius ι level)
        (quittingStoppingLawProfile reward laws) := by
  let hcompression := hasEscapeAwareQuantileClockCompression_of_normalized reward hreward
  obtain ⟨pair, hreachable, hvalue⟩ :=
    exists_finiteClockSemanticPair_exploitability_eq_upper reward hcompression level
  obtain ⟨laws, hlaws, hpair⟩ := hreachable
  rw [hpair, quittingTerminalSemanticExploitability_pair] at hvalue
  obtain ⟨hlower, -, hgap⟩ :=
    escapeAwareQuantileClock_quantitative_bracket reward hcompression hlevel
  have hbound :
      quittingTerminalExploitability reward (quittingStoppingLawProfile reward laws) ≤
        quittingTerminalExploitabilityInf reward + 2 * quantileClockRadius ι level := by
    rw [hvalue]
    linarith
  exact ⟨laws, hlaws, quittingTerminalExploitabilityInf_le reward _, hbound,
    isεAsymptoticNash_of_quittingTerminalExploitability_le _ hbound⟩

/-- Four players admit one actual independent source at support `8 * level + 1`
and regret error `24 / level`, retaining the full behavioral reply quantifier. -/
theorem exists_fin4_finiteClockStoppingLaws_exploitability_le
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {level : ℕ} (hlevel : 0 < level) :
    ∃ laws : Fin 4 → PMF (Option ℕ),
      (∀ who, IsFiniteClockStoppingLaw (8 * level + 1) (laws who)) ∧
      quittingTerminalExploitabilityInf reward ≤
        quittingTerminalExploitability reward (quittingStoppingLawProfile reward laws) ∧
      quittingTerminalExploitability reward (quittingStoppingLawProfile reward laws) ≤
        quittingTerminalExploitabilityInf reward + 24 / (level : ℝ) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
        (quittingTerminalExploitabilityInf reward + 24 / (level : ℝ))
        (quittingStoppingLawProfile reward laws) := by
  have hsource := exists_finiteClockStoppingLaws_exploitability_le reward hreward hlevel
  rw [quantileClockSupport_fin4, show 2 * quantileClockRadius (Fin 4) level =
      24 / (level : ℝ) by rw [quantileClockRadius_fin4]; ring] at hsource
  exact hsource

/-- The same selected laws embed into every larger clock, without changing the profile,
its unrestricted caps, its Never atoms, or the quantitative regret bound. -/
theorem exists_fin4_uniformCalendarStoppingLaws_exploitability_le
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {level : ℕ} (hlevel : 0 < level) :
    ∃ laws : Fin 4 → PMF (Option ℕ),
      (∀ clockBound, 8 * level + 1 ≤ clockBound →
        ∀ who, IsFiniteClockStoppingLaw clockBound (laws who)) ∧
      quittingTerminalExploitabilityInf reward ≤
        quittingTerminalExploitability reward (quittingStoppingLawProfile reward laws) ∧
      quittingTerminalExploitability reward (quittingStoppingLawProfile reward laws) ≤
        quittingTerminalExploitabilityInf reward + 24 / (level : ℝ) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
        (quittingTerminalExploitabilityInf reward + 24 / (level : ℝ))
        (quittingStoppingLawProfile reward laws) := by
  obtain ⟨laws, hlaws, hfloor, hbound, hnash⟩ :=
    exists_fin4_finiteClockStoppingLaws_exploitability_le reward hreward hlevel
  exact ⟨laws, fun _ hclock who => isFiniteClockStoppingLaw_mono hclock (hlaws who),
    hfloor, hbound, hnash⟩

/-- A reward-independent error for embedding the common-quantile source at a
prescribed calendar depth. The level is the literal integer quotient `(clock - 1) / 8`. -/
def fin4FiniteClockApproximationError (clock : ℕ) : ℝ :=
  24 / (((clock - 1) / 8 : ℕ) : ℝ)

/-- The prescribed-calendar error tends to zero, independently of the unit reward table. -/
theorem tendsto_fin4FiniteClockApproximationError :
    Filter.Tendsto fin4FiniteClockApproximationError Filter.atTop (nhds 0) := by
  have hlevel : Filter.Tendsto (fun clock : ℕ => (clock - 1) / 8)
      Filter.atTop Filter.atTop :=
    (Nat.tendsto_div_const_atTop (show (8 : ℕ) ≠ 0 by decide)).comp
      (Filter.tendsto_sub_atTop_nat 1)
  exact (tendsto_const_div_atTop_nhds_zero_nat (24 : ℝ)).comp hlevel

/-- At every sufficiently large prescribed depth, internally select ONE independent
source before ALL larger calendars. The same full behavioral caps obey the reward-uniform
vanishing error; Never is not identified with a finite late clock. -/
theorem exists_fin4_calendarUniformStoppingLaws_exploitability_le
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {clock : ℕ} (hclock : 9 ≤ clock) :
    ∃ laws : Fin 4 → PMF (Option ℕ),
      (∀ clockBound, clock ≤ clockBound →
        ∀ who, IsFiniteClockStoppingLaw clockBound (laws who)) ∧
      quittingTerminalExploitabilityInf reward ≤
        quittingTerminalExploitability reward (quittingStoppingLawProfile reward laws) ∧
      quittingTerminalExploitability reward (quittingStoppingLawProfile reward laws) ≤
        quittingTerminalExploitabilityInf reward + fin4FiniteClockApproximationError clock ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
        (quittingTerminalExploitabilityInf reward + fin4FiniteClockApproximationError clock)
        (quittingStoppingLawProfile reward laws) := by
  have hlevel : 0 < (clock - 1) / 8 := by omega
  have hsupport : 8 * ((clock - 1) / 8) + 1 ≤ clock := by omega
  obtain ⟨laws, hlaws, hfloor, hbound, hnash⟩ :=
    exists_fin4_uniformCalendarStoppingLaws_exploitability_le reward hreward hlevel
  exact ⟨laws, fun _ hlarge => hlaws _ (hsupport.trans hlarge), hfloor, hbound, hnash⟩

end GameTheory
