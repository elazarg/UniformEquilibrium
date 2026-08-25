/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt

/-!
# Same-profile spare-player cancellation

This module records a semantic consumer for a spare player.  One actual
behavior profile is fixed, and only the spare player's complete behavior
strategy is replaced.  The replacement is therefore source-matched by
construction.  All caps below are the unrestricted behavioral best-response
envelopes, not stationary or one-stage deviation values.

At accuracy `ε`, the operational debt support is the set of players whose
terminal semantic debt exceeds `ε`.  Suppose this support has rank at least
two at the source.  A designated residual coordinate may remain uncontrolled.
For every other coordinate, either the spare-player floor controls the spare
itself, or the actual payoff gained from the intervention covers both the
change in unrestricted cap and the source debt.  If aggregate payoff gain also
covers aggregate cap exposure, then the replacement profile yields exactly
one of three semantic outputs:

* a terminal `ε`-Nash profile;
* a strict decrease of total terminal semantic debt; or
* equality of total debt together with support concentrated on the single
  residual coordinate, hence a strict finite-rank decrease.

The five-player corollary specializes the coordinates to a literal `(2+2)`
source: players `0,1` are the two source debtors, players `2,3` are the two
protected coordinates, and player `4` is the spare.  Player `0` is cancelled
and player `1` is the only permitted residual.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Players whose unrestricted terminal semantic debt is strictly larger than
`ε`.  This is the operational finite rank used by spare-player cancellation. -/
def quittingTerminalSemanticDebtSupportAbove
    (pair : QuittingTerminalSemanticPair ι) (ε : ℝ) : Finset ι :=
  Finset.univ.filter fun who =>
    ε < quittingTerminalSemanticDebt pair who

@[simp] theorem mem_quittingTerminalSemanticDebtSupportAbove
    (pair : QuittingTerminalSemanticPair ι) (ε : ℝ) (who : ι) :
    who ∈ quittingTerminalSemanticDebtSupportAbove pair ε ↔
      ε < quittingTerminalSemanticDebt pair who := by
  simp [quittingTerminalSemanticDebtSupportAbove]

/-- The actual endpoint obtained by changing only the spare player's complete
behavior strategy. -/
def quittingSpareReplacementProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (spare : ι)
    (replacement : (quittingGame reward).BehaviorStrategy spare) :
    (quittingGame reward).BehaviorProfile :=
  Function.update source spare replacement

/-- Change in one player's unrestricted behavioral best-response cap caused by
the spare-player intervention. -/
def quittingSpareCapExposure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (spare : ι)
    (replacement : (quittingGame reward).BehaviorStrategy spare)
    (who : ι) : ℝ :=
  quittingContinuationBestResponseValue reward
      (quittingSpareReplacementProfile reward source spare replacement) who -
    quittingContinuationBestResponseValue reward source who

/-- Change in one player's prescribed terminal payoff caused by the
spare-player intervention.  This is the literal same-profile collision gain. -/
def quittingSparePayoffGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (spare : ι)
    (replacement : (quittingGame reward).BehaviorStrategy spare)
    (who : ι) : ℝ :=
  quittingTerminalPayoff reward
      (quittingSpareReplacementProfile reward source spare replacement) who -
    quittingTerminalPayoff reward source who

/-- Exact coordinate bookkeeping: endpoint debt is source debt plus cap
exposure minus actual payoff gain. -/
theorem quittingTerminalSemanticDebt_spareReplacement_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (spare who : ι)
    (replacement : (quittingGame reward).BehaviorStrategy spare) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingSpareReplacementProfile reward source spare replacement)) who =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) who +
        quittingSpareCapExposure reward source spare replacement who -
        quittingSparePayoffGain reward source spare replacement who := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    quittingSpareCapExposure quittingSparePayoffGain
  ring

/-- A player's own prescribed-strategy replacement does not alter that
player's unrestricted cap, because its opponents are unchanged. -/
theorem quittingSpareCapExposure_self_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (spare : ι)
    (replacement : (quittingGame reward).BehaviorStrategy spare) :
    quittingSpareCapExposure reward source spare replacement spare = 0 := by
  unfold quittingSpareCapExposure quittingSpareReplacementProfile
  rw [quittingContinuationBestResponseValue_update_self]
  ring

/-- Exact aggregate bookkeeping for the same-profile intervention. -/
theorem quittingTerminalSemanticDebtSum_spareReplacement_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (spare : ι)
    (replacement : (quittingGame reward).BehaviorStrategy spare) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingSpareReplacementProfile reward source spare replacement)) -
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward source) =
      (∑ who, quittingSpareCapExposure reward source spare replacement who) -
        ∑ who, quittingSparePayoffGain reward source spare replacement who := by
  unfold quittingTerminalSemanticDebtSum
  simp_rw [quittingTerminalSemanticDebt_spareReplacement_eq]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- Coordinatewise unrestricted-debt control is already a full terminal
approximate-Nash certificate; no factor equal to the number of players is
needed. -/
theorem isEpsilonAsymptoticNash_of_terminalSemanticDebt_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (ε : ℝ)
    (hdebt : ∀ who,
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile := by
  intro who deviation
  have hgain :=
    quittingTerminalPayoff_update_sub_le_terminalSemanticDebt
      reward profile who deviation
  linarith [hdebt who]

/-- **Same-profile spare-player cancellation.**

`residual` is the one coordinate which the intervention is allowed not to
cancel.  The floor inequality controls the spare against all behavioral
deviations.  The collision inequalities say that, at every other coordinate,
the literal payoff gain covers the cap exposure and the source debt up to
`ε`.  The aggregate debt inequality prevents the intervention from increasing
total semantic debt.

The output is semantic rather than graph-theoretic: an actual terminal
approximate equilibrium, a strict total-debt decrease, or a same-debt strict
decrease of the finite `ε`-debt-support rank. -/
theorem spareReplacement_terminalNash_or_debtDecrease_or_rankDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile)
    (spare residual : ι)
    (replacement : (quittingGame reward).BehaviorStrategy spare)
    (ε : ℝ)
    (hspareResidual : spare ≠ residual)
    (hsourceRank :
      2 ≤ (quittingTerminalSemanticDebtSupportAbove
        (quittingTerminalSemanticPair reward source) ε).card)
    (hfloor :
      quittingContinuationBestResponseValue reward source spare ≤
        quittingTerminalPayoff reward
          (quittingSpareReplacementProfile reward source spare replacement)
          spare + ε)
    (hcollision : ∀ who, who ≠ spare → who ≠ residual →
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) who +
        quittingSpareCapExposure reward source spare replacement who ≤
      quittingSparePayoffGain reward source spare replacement who + ε)
    (haggregate :
      (∑ who, quittingSpareCapExposure reward source spare replacement who) ≤
        ∑ who, quittingSparePayoffGain reward source spare replacement who) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingSpareReplacementProfile reward source spare replacement) ∨
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source spare replacement)) <
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward source) ∨
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source spare replacement)) =
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward source) ∧
        quittingTerminalSemanticDebtSupportAbove
            (quittingTerminalSemanticPair reward
              (quittingSpareReplacementProfile reward source spare replacement))
            ε = {residual} ∧
        (quittingTerminalSemanticDebtSupportAbove
            (quittingTerminalSemanticPair reward
              (quittingSpareReplacementProfile reward source spare replacement))
            ε).card <
          (quittingTerminalSemanticDebtSupportAbove
            (quittingTerminalSemanticPair reward source) ε).card := by
  have hcontrolled (who : ι) (hwhoResidual : who ≠ residual) :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source spare replacement))
          who ≤ ε := by
    by_cases hwhoSpare : who = spare
    · subst who
      change quittingContinuationBestResponseValue reward
            (quittingSpareReplacementProfile reward source spare replacement)
            spare -
          quittingTerminalPayoff reward
            (quittingSpareReplacementProfile reward source spare replacement)
            spare ≤ ε
      unfold quittingSpareReplacementProfile
      rw [quittingContinuationBestResponseValue_update_self]
      linarith
    · rw [quittingTerminalSemanticDebt_spareReplacement_eq]
      linarith [hcollision who hwhoSpare hwhoResidual]
  by_cases hresidual :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source spare replacement))
          residual ≤ ε
  · left
    apply isEpsilonAsymptoticNash_of_terminalSemanticDebt_le
    intro who
    by_cases hwho : who = residual
    · simpa [hwho] using hresidual
    · exact hcontrolled who hwho
  · right
    have hresidualLarge :
        ε < quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source spare replacement))
          residual := lt_of_not_ge hresidual
    have hsupportSubset :
        quittingTerminalSemanticDebtSupportAbove
            (quittingTerminalSemanticPair reward
              (quittingSpareReplacementProfile reward source spare replacement))
            ε ⊆ {residual} := by
      intro who hwho
      simp only [Finset.mem_singleton]
      by_contra hne
      have hlarge :=
        (mem_quittingTerminalSemanticDebtSupportAbove
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source spare replacement))
          ε who).1 hwho
      exact (not_lt_of_ge (hcontrolled who hne)) hlarge
    have hresidualMem :
        residual ∈ quittingTerminalSemanticDebtSupportAbove
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source spare replacement))
          ε :=
      (mem_quittingTerminalSemanticDebtSupportAbove _ _ _).2 hresidualLarge
    have hsupportEq :
        quittingTerminalSemanticDebtSupportAbove
            (quittingTerminalSemanticPair reward
              (quittingSpareReplacementProfile reward source spare replacement))
            ε = {residual} := by
      apply Finset.Subset.antisymm hsupportSubset
      simpa only [Finset.singleton_subset_iff] using hresidualMem
    have hendpointCard :
        (quittingTerminalSemanticDebtSupportAbove
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source spare replacement))
          ε).card = 1 := by
      rw [hsupportEq]
      simp
    have hrankDrop :
        (quittingTerminalSemanticDebtSupportAbove
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source spare replacement))
          ε).card <
        (quittingTerminalSemanticDebtSupportAbove
          (quittingTerminalSemanticPair reward source) ε).card := by
      rw [hendpointCard]
      exact lt_of_lt_of_le (by decide : 1 < 2) hsourceRank
    have htotalIdentity :=
      quittingTerminalSemanticDebtSum_spareReplacement_sub_eq
        reward source spare replacement
    have htotalLe :
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingSpareReplacementProfile reward source spare replacement)) ≤
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward source) := by
      linarith
    rcases lt_or_eq_of_le htotalLe with htotalLt | htotalEq
    · exact Or.inl htotalLt
    · exact Or.inr ⟨htotalEq, hsupportEq, hrankDrop⟩

/-- Literal five-player `(2+2)+1` specialization.  At scale `ε`, players
`0,1` are the source debt support; `0` is cancelled, `1` is the permitted
residual, `2,3` are protected, and `4` is the spare.  The hypotheses are
exactly the spare floor, one debtor-cancellation inequality, two protected
collision inequalities, and aggregate debt balance, all on the same actual
source and replacement profile. -/
theorem finFive_twoPlusTwo_spareCancellation
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (source : (quittingGame reward).BehaviorProfile)
    (replacement : (quittingGame reward).BehaviorStrategy (4 : Fin 5))
    (ε : ℝ)
    (hsourceSupport :
      quittingTerminalSemanticDebtSupportAbove
          (quittingTerminalSemanticPair reward source) ε =
        ({0, 1} : Finset (Fin 5)))
    (hfloor :
      quittingContinuationBestResponseValue reward source 4 ≤
        quittingTerminalPayoff reward
          (quittingSpareReplacementProfile reward source 4 replacement) 4 + ε)
    (hcancel :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 0 +
        quittingSpareCapExposure reward source 4 replacement 0 ≤
      quittingSparePayoffGain reward source 4 replacement 0 + ε)
    (hprotectTwo :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 2 +
        quittingSpareCapExposure reward source 4 replacement 2 ≤
      quittingSparePayoffGain reward source 4 replacement 2 + ε)
    (hprotectThree :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 3 +
        quittingSpareCapExposure reward source 4 replacement 3 ≤
      quittingSparePayoffGain reward source 4 replacement 3 + ε)
    (haggregate :
      (∑ who, quittingSpareCapExposure reward source 4 replacement who) ≤
        ∑ who, quittingSparePayoffGain reward source 4 replacement who) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingSpareReplacementProfile reward source 4 replacement) ∨
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source 4 replacement)) <
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward source) ∨
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source 4 replacement)) =
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward source) ∧
        quittingTerminalSemanticDebtSupportAbove
            (quittingTerminalSemanticPair reward
              (quittingSpareReplacementProfile reward source 4 replacement))
            ε = ({1} : Finset (Fin 5)) ∧
        (quittingTerminalSemanticDebtSupportAbove
            (quittingTerminalSemanticPair reward
              (quittingSpareReplacementProfile reward source 4 replacement))
            ε).card <
          (quittingTerminalSemanticDebtSupportAbove
            (quittingTerminalSemanticPair reward source) ε).card := by
  apply spareReplacement_terminalNash_or_debtDecrease_or_rankDrop
    reward source 4 1 replacement ε (by decide)
  · rw [hsourceSupport]
    norm_num
  · exact hfloor
  · intro who hwhoSpare hwhoResidual
    fin_cases who
    · exact hcancel
    · exact (hwhoResidual rfl).elim
    · exact hprotectTwo
    · exact hprotectThree
    · exact (hwhoSpare rfl).elim
  · exact haggregate

/-- At a source which is minimal along the actual spare intervention, aggregate
balance rules out the strict-debt branch.  Thus the same literal endpoint is
either terminal `ε`-Nash or lies on the same debt fiber with a strict finite
rank drop. -/
theorem finFive_twoPlusTwo_spareCancellation_at_minimum
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (source : (quittingGame reward).BehaviorProfile)
    (replacement : (quittingGame reward).BehaviorStrategy (4 : Fin 5))
    (ε : ℝ)
    (hsourceSupport :
      quittingTerminalSemanticDebtSupportAbove
          (quittingTerminalSemanticPair reward source) ε =
        ({0, 1} : Finset (Fin 5)))
    (hfloor :
      quittingContinuationBestResponseValue reward source 4 ≤
        quittingTerminalPayoff reward
          (quittingSpareReplacementProfile reward source 4 replacement) 4 + ε)
    (hcancel :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 0 +
        quittingSpareCapExposure reward source 4 replacement 0 ≤
      quittingSparePayoffGain reward source 4 replacement 0 + ε)
    (hprotectTwo :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 2 +
        quittingSpareCapExposure reward source 4 replacement 2 ≤
      quittingSparePayoffGain reward source 4 replacement 2 + ε)
    (hprotectThree :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 3 +
        quittingSpareCapExposure reward source 4 replacement 3 ≤
      quittingSparePayoffGain reward source 4 replacement 3 + ε)
    (haggregate :
      (∑ who, quittingSpareCapExposure reward source 4 replacement who) ≤
        ∑ who, quittingSparePayoffGain reward source 4 replacement who)
    (hminimumAlongIntervention :
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward source) ≤
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source 4 replacement))) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingSpareReplacementProfile reward source 4 replacement) ∨
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source 4 replacement)) =
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward source) ∧
        quittingTerminalSemanticDebtSupportAbove
            (quittingTerminalSemanticPair reward
              (quittingSpareReplacementProfile reward source 4 replacement))
            ε = ({1} : Finset (Fin 5)) ∧
        (quittingTerminalSemanticDebtSupportAbove
            (quittingTerminalSemanticPair reward
              (quittingSpareReplacementProfile reward source 4 replacement))
            ε).card <
          (quittingTerminalSemanticDebtSupportAbove
            (quittingTerminalSemanticPair reward source) ε).card := by
  rcases finFive_twoPlusTwo_spareCancellation reward source replacement ε
      hsourceSupport hfloor hcancel hprotectTwo hprotectThree haggregate with
    hnash | hdecrease | hrank
  · exact Or.inl hnash
  · exact (not_lt_of_ge hminimumAlongIntervention hdecrease).elim
  · exact Or.inr hrank

end GameTheory
