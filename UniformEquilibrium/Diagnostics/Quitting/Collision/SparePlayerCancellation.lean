/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# Same-profile spare-player cancellation

This module gives a semantic consumer for a spare player.  It starts from one
actual behavior profile and changes only the spare player's complete behavior
strategy.  Thus every payoff comparison, every collision comparison, and every
best-response cap is evaluated on the same literal source/intervention pair.
There is no label-cycle reprojection.

At accuracy `ε`, the operational debt support is the set of players whose
unrestricted terminal semantic debt exceeds `ε`.  A `(2+2)` source need only
localize that support to a two-label cover; it need not make both covered debts
positive.  Under a spare floor, coordinatewise collision repayment, and an
aggregate debt balance, the intervened profile yields exactly one of:

* a terminal `ε`-Nash profile against arbitrary behavioral deviations;
* a strict decrease of total terminal semantic debt; or
* equality of total debt and a strict finite cover-rank decrease from at least
  two labels to the single permitted residual label.

At a minimum-debt source the middle branch is impossible.  Under a terminal
exploitability gap larger than `ε`, the Nash branch is impossible as well, so
the fifth player forces a literal same-fiber rank decrease.

The lower-level theorem uses exact best-response-cap exposure.  A second,
more operational theorem derives those cap inequalities from one bound which
holds uniformly for every unilateral behavioral deviation.  This is the
explicit all-behavior collision control required of the spare player.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Players whose unrestricted terminal semantic debt is strictly larger than
`ε`. -/
def quittingTerminalSemanticDebtSupportAbove
    (pair : QuittingTerminalSemanticPair ι) (ε : ℝ) : Finset ι :=
  Finset.univ.filter fun who =>
    ε < quittingTerminalSemanticDebt pair who

@[simp] theorem mem_quittingTerminalSemanticDebtSupportAbove
    (pair : QuittingTerminalSemanticPair ι) (ε : ℝ) (who : ι) :
    who ∈ quittingTerminalSemanticDebtSupportAbove pair ε ↔
      ε < quittingTerminalSemanticDebt pair who := by
  simp [quittingTerminalSemanticDebtSupportAbove]

/-- A finite set which contains every debt coordinate above accuracy `ε`.
Its cardinality is the operational finite rank used below. -/
def IsQuittingTerminalSemanticDebtCover
    (pair : QuittingTerminalSemanticPair ι) (ε : ℝ)
    (cover : Finset ι) : Prop :=
  quittingTerminalSemanticDebtSupportAbove pair ε ⊆ cover

/-- A strict decrease from a certified source debt cover to the target's
canonical debt support. -/
def HasQuittingTerminalSemanticDebtCoverRankDrop
    (source target : QuittingTerminalSemanticPair ι) (ε : ℝ)
    (sourceCover : Finset ι) : Prop :=
  IsQuittingTerminalSemanticDebtCover source ε sourceCover ∧
    (quittingTerminalSemanticDebtSupportAbove target ε).card <
      sourceCover.card

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

/-- A uniform all-behavior collision-cap certificate.  After the spare is
replaced, even an arbitrary unilateral behavioral deviation by `who` changes
`who`'s payoff by at most `cap who` relative to the same deviation at the
literal source. -/
def HasQuittingSpareUnrestrictedCollisionCaps
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (spare : ι)
    (replacement : (quittingGame reward).BehaviorStrategy spare)
    (cap : Payoff ι) : Prop :=
  ∀ who (deviation : (quittingGame reward).BehaviorStrategy who),
    quittingTerminalPayoff reward
          (Function.update
            (quittingSpareReplacementProfile reward source spare replacement)
            who deviation) who -
        quittingTerminalPayoff reward
          (Function.update source who deviation) who ≤
      cap who

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
  unfold quittingContinuationBestResponseValue
  congr 2
  funext deviation
  rw [Function.update_idem]

/-- An all-behavior collision-cap certificate bounds the actual change of the
unrestricted best-response envelope. -/
theorem quittingSpareCapExposure_le_of_unrestrictedCollisionCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (spare who : ι)
    (replacement : (quittingGame reward).BehaviorStrategy spare)
    (bound : ℝ)
    (hbound : ∀ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward
            (Function.update
              (quittingSpareReplacementProfile reward source spare replacement)
              who deviation) who -
          quittingTerminalPayoff reward
            (Function.update source who deviation) who ≤
        bound) :
    quittingSpareCapExposure reward source spare replacement who ≤ bound := by
  unfold quittingSpareCapExposure
  rw [sub_le_iff_le_add]
  unfold quittingContinuationBestResponseValue
  apply csSup_le
  · exact Set.range_nonempty _
  rintro payoff ⟨deviation, rfl⟩
  have hsource :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward source who deviation
  have hexposure := hbound deviation
  linarith

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

/-- **Same-profile spare-player cancellation, exact-cap form.**

`residual` is the one coordinate which the intervention is allowed not to
cancel.  `sourceCover` certifies the finite unresolved rank at the source.
The floor controls the spare against all behavioral deviations.  Every other
nonresidual coordinate is repaid by its literal payoff gain after charging the
exact drift of its unrestricted cap.  Aggregate gain covers aggregate cap
exposure.

The output is semantic rather than graph-theoretic: an actual terminal
approximate equilibrium, a strict total-debt decrease, or a same-debt strict
decrease of the certified finite debt-cover rank. -/
theorem spareReplacement_terminalNash_or_debtDecrease_or_coverRankDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile)
    (spare residual : ι)
    (replacement : (quittingGame reward).BehaviorStrategy spare)
    (ε : ℝ) (sourceCover : Finset ι)
    (hsourceCover : IsQuittingTerminalSemanticDebtCover
      (quittingTerminalSemanticPair reward source) ε sourceCover)
    (hsourceRank : 2 ≤ sourceCover.card)
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
        HasQuittingTerminalSemanticDebtCoverRankDrop
          (quittingTerminalSemanticPair reward source)
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source spare replacement))
          ε sourceCover := by
  have hcontrolled (who : ι) (hwhoResidual : who ≠ residual) :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source spare replacement))
          who ≤ ε := by
    by_cases hwhoSpare : who = spare
    · subst who
      rw [quittingTerminalSemanticDebt_spareReplacement_eq,
        quittingSpareCapExposure_self_eq_zero]
      unfold quittingSparePayoffGain
      unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
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
        HasQuittingTerminalSemanticDebtCoverRankDrop
          (quittingTerminalSemanticPair reward source)
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source spare replacement))
          ε sourceCover := by
      constructor
      · exact hsourceCover
      · rw [hendpointCard]
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

/-- **Same-profile spare-player cancellation, all-behavior collision form.**

Instead of assuming the abstract cap exposures, this theorem takes an explicit
uniform collision bound for every unilateral behavioral deviation.  The
supremum lemma above converts those bounds to unrestricted cap exposure. -/
theorem spareReplacement_terminalNash_or_debtDecrease_or_coverRankDrop_of_unrestrictedCollisionCaps
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile)
    (spare residual : ι)
    (replacement : (quittingGame reward).BehaviorStrategy spare)
    (ε : ℝ) (sourceCover : Finset ι) (cap : Payoff ι)
    (hsourceCover : IsQuittingTerminalSemanticDebtCover
      (quittingTerminalSemanticPair reward source) ε sourceCover)
    (hsourceRank : 2 ≤ sourceCover.card)
    (hcaps : HasQuittingSpareUnrestrictedCollisionCaps
      reward source spare replacement cap)
    (hfloor :
      quittingContinuationBestResponseValue reward source spare ≤
        quittingTerminalPayoff reward
          (quittingSpareReplacementProfile reward source spare replacement)
          spare + ε)
    (hcollision : ∀ who, who ≠ spare → who ≠ residual →
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) who + cap who ≤
        quittingSparePayoffGain reward source spare replacement who + ε)
    (haggregate :
      (∑ who, cap who) ≤
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
        HasQuittingTerminalSemanticDebtCoverRankDrop
          (quittingTerminalSemanticPair reward source)
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source spare replacement))
          ε sourceCover := by
  have hcapExposure : ∀ who,
      quittingSpareCapExposure reward source spare replacement who ≤ cap who := by
    intro who
    exact quittingSpareCapExposure_le_of_unrestrictedCollisionCap
      reward source spare who replacement (cap who) (hcaps who)
  apply spareReplacement_terminalNash_or_debtDecrease_or_coverRankDrop
    reward source spare residual replacement ε sourceCover
      hsourceCover hsourceRank hfloor
  · intro who hwhoSpare hwhoResidual
    linarith [hcollision who hwhoSpare hwhoResidual, hcapExposure who]
  · calc
      (∑ who, quittingSpareCapExposure reward source spare replacement who) ≤
          ∑ who, cap who :=
        Finset.sum_le_sum fun who _ => hcapExposure who
      _ ≤ ∑ who, quittingSparePayoffGain reward source spare replacement who :=
        haggregate

/-- Literal five-player `(2+2)+1` specialization.  Players `0,1` form the
certified source debt cover, players `2,3` are protected, and player `4` is the
spare.  Player `0` is cancelled and player `1` is the only permitted residual.
All cap bounds quantify over unrestricted behavioral deviations on the same
source/intervention pair. -/
theorem finFive_twoPlusTwo_spareCancellation
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (source : (quittingGame reward).BehaviorProfile)
    (replacement : (quittingGame reward).BehaviorStrategy (4 : Fin 5))
    (ε : ℝ) (cap : Payoff (Fin 5))
    (hsourceLocalized : IsQuittingTerminalSemanticDebtCover
      (quittingTerminalSemanticPair reward source) ε
      ({0, 1} : Finset (Fin 5)))
    (hcaps : HasQuittingSpareUnrestrictedCollisionCaps
      reward source 4 replacement cap)
    (hfloor :
      quittingContinuationBestResponseValue reward source 4 ≤
        quittingTerminalPayoff reward
          (quittingSpareReplacementProfile reward source 4 replacement) 4 + ε)
    (hcancel :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 0 + cap 0 ≤
        quittingSparePayoffGain reward source 4 replacement 0 + ε)
    (hprotectTwo :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 2 + cap 2 ≤
        quittingSparePayoffGain reward source 4 replacement 2 + ε)
    (hprotectThree :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 3 + cap 3 ≤
        quittingSparePayoffGain reward source 4 replacement 3 + ε)
    (haggregate :
      (∑ who, cap who) ≤
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
        HasQuittingTerminalSemanticDebtCoverRankDrop
          (quittingTerminalSemanticPair reward source)
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source 4 replacement))
          ε ({0, 1} : Finset (Fin 5)) := by
  apply spareReplacement_terminalNash_or_debtDecrease_or_coverRankDrop_of_unrestrictedCollisionCaps
    reward source 4 1 replacement ε ({0, 1} : Finset (Fin 5)) cap
      hsourceLocalized (by norm_num) hcaps hfloor
  · intro who hwhoSpare hwhoResidual
    fin_cases who
    · exact hcancel
    · exact (hwhoResidual rfl).elim
    · exact hprotectTwo
    · exact hprotectThree
    · exact (hwhoSpare rfl).elim
  · exact haggregate

/-- At a source which is minimal along the actual spare intervention,
aggregate balance rules out strict debt descent.  The literal endpoint is
therefore terminal `ε`-Nash or lies on the same debt fiber with a certified
rank-two-to-rank-one decrease. -/
theorem finFive_twoPlusTwo_spareCancellation_at_minimum
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (source : (quittingGame reward).BehaviorProfile)
    (replacement : (quittingGame reward).BehaviorStrategy (4 : Fin 5))
    (ε : ℝ) (cap : Payoff (Fin 5))
    (hsourceLocalized : IsQuittingTerminalSemanticDebtCover
      (quittingTerminalSemanticPair reward source) ε
      ({0, 1} : Finset (Fin 5)))
    (hcaps : HasQuittingSpareUnrestrictedCollisionCaps
      reward source 4 replacement cap)
    (hfloor :
      quittingContinuationBestResponseValue reward source 4 ≤
        quittingTerminalPayoff reward
          (quittingSpareReplacementProfile reward source 4 replacement) 4 + ε)
    (hcancel :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 0 + cap 0 ≤
        quittingSparePayoffGain reward source 4 replacement 0 + ε)
    (hprotectTwo :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 2 + cap 2 ≤
        quittingSparePayoffGain reward source 4 replacement 2 + ε)
    (hprotectThree :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 3 + cap 3 ≤
        quittingSparePayoffGain reward source 4 replacement 3 + ε)
    (haggregate :
      (∑ who, cap who) ≤
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
        HasQuittingTerminalSemanticDebtCoverRankDrop
          (quittingTerminalSemanticPair reward source)
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source 4 replacement))
          ε ({0, 1} : Finset (Fin 5)) := by
  rcases finFive_twoPlusTwo_spareCancellation reward source replacement ε cap
      hsourceLocalized hcaps hfloor hcancel hprotectTwo hprotectThree haggregate with
    hnash | hdecrease | hrank
  · exact Or.inl hnash
  · exact (not_lt_of_ge hminimumAlongIntervention hdecrease).elim
  · exact Or.inr hrank

/-- In the counterexample regime, choose `ε` below the fixed terminal gap.
At an intervention-minimal source the terminal-Nash and strict-debt branches
are both impossible, so spare-player cancellation gives an unconditional
same-fiber finite-rank decrease. -/
theorem finFive_twoPlusTwo_spareCancellation_rankDrop_of_terminalGap
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (source : (quittingGame reward).BehaviorProfile)
    (replacement : (quittingGame reward).BehaviorStrategy (4 : Fin 5))
    (ε gap : ℝ) (cap : Payoff (Fin 5))
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hεgap : ε < gap)
    (hsourceLocalized : IsQuittingTerminalSemanticDebtCover
      (quittingTerminalSemanticPair reward source) ε
      ({0, 1} : Finset (Fin 5)))
    (hcaps : HasQuittingSpareUnrestrictedCollisionCaps
      reward source 4 replacement cap)
    (hfloor :
      quittingContinuationBestResponseValue reward source 4 ≤
        quittingTerminalPayoff reward
          (quittingSpareReplacementProfile reward source 4 replacement) 4 + ε)
    (hcancel :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 0 + cap 0 ≤
        quittingSparePayoffGain reward source 4 replacement 0 + ε)
    (hprotectTwo :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 2 + cap 2 ≤
        quittingSparePayoffGain reward source 4 replacement 2 + ε)
    (hprotectThree :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) 3 + cap 3 ≤
        quittingSparePayoffGain reward source 4 replacement 3 + ε)
    (haggregate :
      (∑ who, cap who) ≤
        ∑ who, quittingSparePayoffGain reward source 4 replacement who)
    (hminimumAlongIntervention :
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward source) ≤
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source 4 replacement))) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingSpareReplacementProfile reward source 4 replacement)) =
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward source) ∧
      quittingTerminalSemanticDebtSupportAbove
          (quittingTerminalSemanticPair reward
            (quittingSpareReplacementProfile reward source 4 replacement))
          ε = ({1} : Finset (Fin 5)) ∧
      HasQuittingTerminalSemanticDebtCoverRankDrop
        (quittingTerminalSemanticPair reward source)
        (quittingTerminalSemanticPair reward
          (quittingSpareReplacementProfile reward source 4 replacement))
        ε ({0, 1} : Finset (Fin 5)) := by
  rcases finFive_twoPlusTwo_spareCancellation_at_minimum
      reward source replacement ε cap hsourceLocalized hcaps hfloor hcancel
        hprotectTwo hprotectThree haggregate hminimumAlongIntervention with
    hnash | hrank
  · obtain ⟨who, deviation, hdeviation⟩ :=
      hexploit (quittingSpareReplacementProfile reward source 4 replacement)
    have hnashBound := hnash who deviation
    linarith
  · exact hrank

end GameTheory
