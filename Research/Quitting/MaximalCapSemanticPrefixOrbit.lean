/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CausalTailEscapeMaxAbsorptionCore
import UniformEquilibrium.Quitting.Root.SemanticExactPrefixOrbit
import UniformEquilibrium.Quitting.Root.SelfTailClosure

/-!
# The semantic orbit of the maximal-absorption cap selector

The maximal-absorption exact root is indexed by a semantic cap.  Iterating
that selector on semantic pairs therefore gives one autonomous orbit, one
explicit outward root word, and one scalar joint-survival ray.  Actual tails
whose semantic pair is the displayed source realize that same orbit when the
common word is prepended.

This module is source-independent.  It neither constructs a Fin4 source nor
asserts that different behavioral tails are equal.  It also makes no claim
that maximality passes to a limiting root.
-/

noncomputable section

namespace GameTheory

open Math.Probability Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The cap-indexed maximal root viewed as a selector on semantic pairs. -/
def quittingMaximalCapSemanticRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) : ι → PMF Bool :=
  quittingMaximalAbsorptionCapRoot reward pair.2

theorem quittingMaximalCapSemanticRoot_exactNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) :
    IsεQuittingRootNash reward pair.2 0
      (quittingMaximalCapSemanticRoot reward pair) :=
  quittingMaximalAbsorptionCapRoot_exactNash reward pair.2

theorem quittingMaximalCapSemanticRoot_maximal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (other : ι → PMF Bool)
    (hother : IsεQuittingRootNash reward pair.2 0 other) :
    quittingRootAbsorptionMass other ≤
      quittingRootAbsorptionMass
        (quittingMaximalCapSemanticRoot reward pair) :=
  quittingMaximalAbsorptionCapRoot_maximal reward pair.2 other hother

theorem quittingMaximalCapSemanticRoot_eq_of_cap_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : QuittingTerminalSemanticPair ι}
    (hcap : first.2 = second.2) :
    quittingMaximalCapSemanticRoot reward first =
      quittingMaximalCapSemanticRoot reward second :=
  quittingMaximalAbsorptionCapRoot_eq_of_cap_eq reward hcap

/-- The autonomous semantic orbit driven by maximal-absorption cap roots. -/
def quittingMaximalCapSemanticPrefixOrbit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) :
    ℕ → QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticSelectorPrefixOrbit reward
    (quittingMaximalCapSemanticRoot reward) source

@[simp] theorem quittingMaximalCapSemanticPrefixOrbit_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) :
    quittingMaximalCapSemanticPrefixOrbit reward source 0 = source := rfl

theorem quittingMaximalCapSemanticPrefixOrbit_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) :
    quittingMaximalCapSemanticPrefixOrbit reward source (time + 1) =
      quittingTerminalSemanticPrefix reward
        (quittingMaximalCapSemanticRoot reward
          (quittingMaximalCapSemanticPrefixOrbit reward source time))
        (quittingMaximalCapSemanticPrefixOrbit reward source time) := rfl

theorem quittingMaximalCapSemanticPrefixOrbit_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward) (time : ℕ) :
    quittingMaximalCapSemanticPrefixOrbit reward source time ∈
      quittingTerminalSemanticCarrier reward :=
  quittingTerminalSemanticSelectorPrefixOrbit_mem_carrier reward
    (quittingMaximalCapSemanticRoot reward) source hsource time

/-- Chronological outer-to-inner root word realizing one semantic-orbit
point over an executable tail. -/
def quittingMaximalCapSemanticPrefixRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) :
    ℕ → List (ι → PMF Bool)
  | 0 => []
  | time + 1 =>
      quittingMaximalCapSemanticRoot reward
          (quittingMaximalCapSemanticPrefixOrbit reward source time) ::
        quittingMaximalCapSemanticPrefixRootStack reward source time

@[simp] theorem quittingMaximalCapSemanticPrefixRootStack_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) :
    quittingMaximalCapSemanticPrefixRootStack reward source 0 = [] := rfl

@[simp] theorem quittingMaximalCapSemanticPrefixRootStack_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) :
    quittingMaximalCapSemanticPrefixRootStack reward source (time + 1) =
      quittingMaximalCapSemanticRoot reward
          (quittingMaximalCapSemanticPrefixOrbit reward source time) ::
        quittingMaximalCapSemanticPrefixRootStack reward source time := rfl

@[simp] theorem quittingMaximalCapSemanticPrefixRootStack_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) :
    (quittingMaximalCapSemanticPrefixRootStack reward source time).length =
      time := by
  induction time with
  | zero => rfl
  | succ time ih => simp [ih]

/-- Joint survival of the common maximal-cap root word. -/
def quittingMaximalCapSemanticPrefixSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) : ℝ :=
  quittingCapNashStackContinueProduct
    (quittingMaximalCapSemanticPrefixRootStack reward source time)

@[simp] theorem quittingMaximalCapSemanticPrefixSurvival_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) :
    quittingMaximalCapSemanticPrefixSurvival reward source 0 = 1 := rfl

theorem quittingMaximalCapSemanticPrefixSurvival_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) :
    quittingMaximalCapSemanticPrefixSurvival reward source (time + 1) =
      quittingStationaryContinueMass
          (quittingMaximalCapSemanticRoot reward
            (quittingMaximalCapSemanticPrefixOrbit reward source time)) *
        quittingMaximalCapSemanticPrefixSurvival reward source time := rfl

theorem quittingMaximalCapSemanticPrefixSurvival_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) :
    0 ≤ quittingMaximalCapSemanticPrefixSurvival reward source time :=
  quittingCapNashStackContinueProduct_nonneg _

theorem quittingMaximalCapSemanticPrefixSurvival_le_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) :
    quittingMaximalCapSemanticPrefixSurvival reward source time ≤ 1 :=
  quittingCapNashStackContinueProduct_le_one _

/-- Actual profile obtained by putting the semantic orbit's common root word
in front of an arbitrary executable tail. -/
def quittingMaximalCapSemanticPrefixProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward
    (quittingMaximalCapSemanticPrefixRootStack reward source time) terminal

@[simp] theorem quittingMaximalCapSemanticPrefixProfile_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingMaximalCapSemanticPrefixProfile reward source terminal 0 =
      terminal := rfl

theorem quittingMaximalCapSemanticPrefixProfile_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingMaximalCapSemanticPrefixProfile reward source terminal (time + 1) =
      quittingRootThenContinuationProfile reward
        (quittingMaximalCapSemanticRoot reward
          (quittingMaximalCapSemanticPrefixOrbit reward source time))
        (quittingMaximalCapSemanticPrefixProfile reward source terminal time) :=
  rfl

/-- If the declared tail has the source semantic pair, the common root word
realizes exactly the source-indexed semantic orbit. -/
theorem quittingTerminalSemanticPair_maximalCapSemanticPrefixProfile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hterminal : quittingTerminalSemanticPair reward terminal = source)
    (time : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingMaximalCapSemanticPrefixProfile reward source terminal time) =
      quittingMaximalCapSemanticPrefixOrbit reward source time := by
  induction time with
  | zero => simpa using hterminal
  | succ time ih =>
      rw [quittingMaximalCapSemanticPrefixProfile_succ,
        quittingTerminalSemanticPair_rootThenContinuation,
        quittingMaximalCapSemanticPrefixOrbit_succ, ih]

/-- The common word is exactly the profile-indexed maximal-prefix recursion
when its semantic source is the terminal's actual semantic pair. -/
theorem quittingMaximalCapPrefixProfile_eq_semanticPrefixProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingMaximalCapPrefixProfile reward terminal time =
      quittingMaximalCapSemanticPrefixProfile reward
        (quittingTerminalSemanticPair reward terminal) terminal time := by
  induction time with
  | zero => rfl
  | succ time ih =>
      rw [quittingMaximalCapPrefixProfile_succ,
        quittingMaximalCapSemanticPrefixProfile_succ, ih]
      congr 2
      apply quittingMaximalAbsorptionCapRoot_eq_of_cap_eq reward
      exact congrArg Prod.snd
        (quittingTerminalSemanticPair_maximalCapSemanticPrefixProfile_eq
          reward (quittingTerminalSemanticPair reward terminal) terminal rfl
            time)

/-- Every root of the explicit word is exact Nash against the actual cap of
its remaining executable suffix. -/
theorem isQuittingCapNashRootStack_maximalCapSemanticPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hterminal : quittingTerminalSemanticPair reward terminal = source)
    (time : ℕ) :
    IsQuittingCapNashRootStack reward
      (quittingMaximalCapSemanticPrefixRootStack reward source time) terminal := by
  induction time with
  | zero => trivial
  | succ time ih =>
      rw [quittingMaximalCapSemanticPrefixRootStack_succ,
        isQuittingCapNashRootStack_cons_iff]
      refine ⟨?_, ih⟩
      have hsemantic :=
        quittingTerminalSemanticPair_maximalCapSemanticPrefixProfile_eq
          reward source terminal hterminal time
      have hcap := congrArg Prod.snd hsemantic
      change (fun player => quittingContinuationBestResponseValue reward
          (quittingLiteralRootStackProfile reward
            (quittingMaximalCapSemanticPrefixRootStack reward source time)
            terminal) player) =
        (quittingMaximalCapSemanticPrefixOrbit reward source time).2 at hcap
      rw [hcap]
      exact quittingMaximalCapSemanticRoot_exactNash reward _

/-- After the complete common root word, the all-Continue continuation is
literally the declared behavioral tail. -/
theorem quittingAllContinueProfileSpine_maximalCapSemanticPrefixProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingAllContinueProfileSpine reward
        (quittingMaximalCapSemanticPrefixProfile reward source terminal time)
        time = terminal := by
  simpa only [quittingMaximalCapSemanticPrefixProfile,
    quittingMaximalCapSemanticPrefixRootStack_length] using
      (quittingAllContinueProfileSpine_literalRootStackProfile_length
        reward (quittingMaximalCapSemanticPrefixRootStack reward source time)
          terminal)

/-! ## Exact scalar-ray identities -/

/-- Every semantic debt coordinate is multiplied by the common joint
survival and by no other factor. -/
theorem quittingTerminalSemanticDebt_maximalCapSemanticPrefixOrbit_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) (who : ι) :
    quittingTerminalSemanticDebt
        (quittingMaximalCapSemanticPrefixOrbit reward source time) who =
      quittingMaximalCapSemanticPrefixSurvival reward source time *
        quittingTerminalSemanticDebt source who := by
  induction time with
  | zero => simp
  | succ time ih =>
      rw [quittingMaximalCapSemanticPrefixOrbit_succ,
        quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
          (reward := reward)
          (quittingMaximalCapSemanticPrefixOrbit reward source time)
          (quittingMaximalCapSemanticRoot reward
            (quittingMaximalCapSemanticPrefixOrbit reward source time)) who
          (quittingMaximalCapSemanticRoot_exactNash reward _),
        ih, quittingMaximalCapSemanticPrefixSurvival_succ]
      ring

/-- Total semantic debt lies on the same scalar ray. -/
theorem quittingTerminalSemanticDebtSum_maximalCapSemanticPrefixOrbit_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) :
    quittingTerminalSemanticDebtSum
        (quittingMaximalCapSemanticPrefixOrbit reward source time) =
      quittingMaximalCapSemanticPrefixSurvival reward source time *
        quittingTerminalSemanticDebtSum source := by
  unfold quittingTerminalSemanticDebtSum
  simp_rw [quittingTerminalSemanticDebt_maximalCapSemanticPrefixOrbit_eq
    reward source time]
  rw [Finset.mul_sum]

/-- Literal deviation debt of every actual common-word realization has the
same scalar formula when its tail realizes the declared semantic source. -/
theorem quittingTerminalDeviationDebt_maximalCapSemanticPrefixProfile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hterminal : quittingTerminalSemanticPair reward terminal = source)
    (time : ℕ) (who : ι) :
    quittingTerminalDeviationDebt reward
        (quittingMaximalCapSemanticPrefixProfile reward source terminal time)
        who =
      quittingMaximalCapSemanticPrefixSurvival reward source time *
        quittingTerminalSemanticDebt source who := by
  change quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingMaximalCapSemanticPrefixProfile reward source terminal time))
      who = _
  rw [quittingTerminalSemanticPair_maximalCapSemanticPrefixProfile_eq
    reward source terminal hterminal time,
    quittingTerminalSemanticDebt_maximalCapSemanticPrefixOrbit_eq]

/-- Literal total debt of every actual common-word realization has the same
scalar formula. -/
theorem quittingTerminalDebtSum_maximalCapSemanticPrefixProfile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hterminal : quittingTerminalSemanticPair reward terminal = source)
    (time : ℕ) :
    quittingTerminalDebtSum reward
        (quittingMaximalCapSemanticPrefixProfile reward source terminal time) =
      quittingMaximalCapSemanticPrefixSurvival reward source time *
        quittingTerminalSemanticDebtSum source := by
  rw [quittingTerminalDebtSum_eq_terminalSemanticDebtSum,
    quittingTerminalSemanticPair_maximalCapSemanticPrefixProfile_eq
      reward source terminal hterminal time,
    quittingTerminalSemanticDebtSum_maximalCapSemanticPrefixOrbit_eq]

/-- A positive global minimum gives the correctly oriented lower survival
bound `D_* / D_0 ≤ alpha`. -/
theorem minimumDebt_div_sourceDebt_le_maximalCapSemanticPrefixSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (time : ℕ) :
    quittingTerminalSemanticDebtSum minimum /
          quittingTerminalSemanticDebtSum source ≤
      quittingMaximalCapSemanticPrefixSurvival reward source time := by
  have hsourcePos : 0 < quittingTerminalSemanticDebtSum source :=
    hminimumPos.trans_le (hminimum source hsource)
  apply (div_le_iff₀ hsourcePos).2
  rw [← quittingTerminalSemanticDebtSum_maximalCapSemanticPrefixOrbit_eq]
  exact hminimum _
    (quittingMaximalCapSemanticPrefixOrbit_mem_carrier
      reward source hsource time)

theorem quittingMaximalCapSemanticPrefixSurvival_pos_of_positiveMinimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (time : ℕ) :
    0 < quittingMaximalCapSemanticPrefixSurvival reward source time := by
  have hsourcePos : 0 < quittingTerminalSemanticDebtSum source :=
    hminimumPos.trans_le (hminimum source hsource)
  exact (div_pos hminimumPos hsourcePos).trans_le
    (minimumDebt_div_sourceDebt_le_maximalCapSemanticPrefixSurvival
      reward minimum source hminimum hminimumPos hsource time)

/-- Positive-debt support is invariant at every finite point of the ray. -/
theorem quittingTerminalSemanticDebt_maximalCapSemanticPrefixOrbit_pos_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (time : ℕ) (who : ι) :
    0 < quittingTerminalSemanticDebt
        (quittingMaximalCapSemanticPrefixOrbit reward source time) who ↔
      0 < quittingTerminalSemanticDebt source who := by
  rw [quittingTerminalSemanticDebt_maximalCapSemanticPrefixOrbit_eq]
  exact mul_pos_iff_of_pos_left
    (quittingMaximalCapSemanticPrefixSurvival_pos_of_positiveMinimum
      reward minimum source hminimum hminimumPos hsource time)

theorem quittingMaximalCapSemanticPrefixOrbit_positiveDebtSupport_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (time : ℕ) :
    (Finset.univ.filter fun who => 0 < quittingTerminalSemanticDebt
        (quittingMaximalCapSemanticPrefixOrbit reward source time) who) =
      Finset.univ.filter fun who =>
        0 < quittingTerminalSemanticDebt source who := by
  ext who
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact quittingTerminalSemanticDebt_maximalCapSemanticPrefixOrbit_pos_iff
    reward minimum source hminimum hminimumPos hsource time who

/-- Normalized debt coordinates are invariant along the positive scalar ray.
-/
theorem quittingTerminalSemanticDebt_normalized_maximalCapSemanticPrefixOrbit_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (time : ℕ) (who : ι) :
    quittingTerminalSemanticDebt
          (quittingMaximalCapSemanticPrefixOrbit reward source time) who /
        quittingTerminalSemanticDebtSum
          (quittingMaximalCapSemanticPrefixOrbit reward source time) =
      quittingTerminalSemanticDebt source who /
        quittingTerminalSemanticDebtSum source := by
  rw [quittingTerminalSemanticDebt_maximalCapSemanticPrefixOrbit_eq,
    quittingTerminalSemanticDebtSum_maximalCapSemanticPrefixOrbit_eq]
  exact mul_div_mul_left _ _
    (ne_of_gt
      (quittingMaximalCapSemanticPrefixSurvival_pos_of_positiveMinimum
        reward minimum source hminimum hminimumPos hsource time))

/-! ## Literal root-word transport -/

theorem quittingMaximalCapSemanticPrefixProfile_eq_literalRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingMaximalCapSemanticPrefixProfile reward source terminal time =
      quittingLiteralRootStackProfile reward
        (quittingMaximalCapSemanticPrefixRootStack reward source time)
        terminal := rfl

theorem quittingProfileLiveRoot_maximalCapSemanticPrefixProfile_eq_getElem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (time stage : ℕ) (hstage : stage < time) :
    quittingProfileLiveRoot reward
        (quittingMaximalCapSemanticPrefixProfile reward source terminal time)
        stage =
      (quittingMaximalCapSemanticPrefixRootStack reward source time)[stage]'
        (by simpa using hstage) := by
  exact quittingProfileLiveRoot_literalRootStackProfile_eq_getElem
    reward (quittingMaximalCapSemanticPrefixRootStack reward source time)
      terminal stage (by simpa using hstage)

/-- Every fixed suffix atom is shifted by the word length and multiplied by
the ray survival. -/
theorem quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (time stage : ℕ) (coalition : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingMaximalCapSemanticPrefixProfile reward source terminal time)
        (time + stage) coalition =
      quittingMaximalCapSemanticPrefixSurvival reward source time *
        quittingStageCoalitionMass reward terminal stage coalition := by
  simpa only [quittingMaximalCapSemanticPrefixProfile,
    quittingMaximalCapSemanticPrefixSurvival,
    quittingMaximalCapSemanticPrefixRootStack_length] using
      (quittingStageCoalitionMass_literalRootStack_add_length reward
        (quittingMaximalCapSemanticPrefixRootStack reward source time)
          terminal stage coalition)

/-- A common explicit maximal-cap root word scales every prescribed-payoff
difference between two tails by the same survival. -/
theorem quittingTerminalPayoff_maximalCapSemanticPrefixProfile_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (time : ℕ) (who : ι) :
    quittingTerminalPayoff reward
          (quittingMaximalCapSemanticPrefixProfile reward source first time)
          who -
        quittingTerminalPayoff reward
          (quittingMaximalCapSemanticPrefixProfile reward source second time)
          who =
      quittingMaximalCapSemanticPrefixSurvival reward source time *
        (quittingTerminalPayoff reward first who -
          quittingTerminalPayoff reward second who) := by
  exact quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul
    (reward := reward)
    (quittingMaximalCapSemanticPrefixRootStack reward source time)
    first second who

theorem quittingTerminalPayoffGain_maximalCapSemanticPrefixProfile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (target base : (quittingGame reward).BehaviorProfile)
    (time : ℕ) (who : ι) (gain : ℝ)
    (hgain : quittingTerminalPayoff reward target who -
      quittingTerminalPayoff reward base who = gain) :
    quittingTerminalPayoff reward
          (quittingMaximalCapSemanticPrefixProfile reward source target time)
          who -
        quittingTerminalPayoff reward
          (quittingMaximalCapSemanticPrefixProfile reward source base time)
          who =
      quittingMaximalCapSemanticPrefixSurvival reward source time * gain := by
  rw [quittingTerminalPayoff_maximalCapSemanticPrefixProfile_sub_eq, hgain]

/-! ## Autonomous restart laws -/

theorem quittingMaximalCapSemanticPrefixOrbit_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (first second : ℕ) :
    quittingMaximalCapSemanticPrefixOrbit reward source (first + second) =
      quittingMaximalCapSemanticPrefixOrbit reward
        (quittingMaximalCapSemanticPrefixOrbit reward source first) second :=
  quittingTerminalSemanticSelectorPrefixOrbit_add reward
    (quittingMaximalCapSemanticRoot reward) source first second

theorem quittingMaximalCapSemanticPrefixRootStack_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (first second : ℕ) :
    quittingMaximalCapSemanticPrefixRootStack reward source (first + second) =
      quittingMaximalCapSemanticPrefixRootStack reward
          (quittingMaximalCapSemanticPrefixOrbit reward source first) second ++
        quittingMaximalCapSemanticPrefixRootStack reward source first := by
  induction second with
  | zero => simp
  | succ second ih =>
      rw [Nat.add_succ,
        quittingMaximalCapSemanticPrefixRootStack_succ,
        quittingMaximalCapSemanticPrefixRootStack_succ,
        quittingMaximalCapSemanticPrefixOrbit_add, ih, List.cons_append]

theorem quittingMaximalCapSemanticPrefixSurvival_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (first second : ℕ) :
    quittingMaximalCapSemanticPrefixSurvival reward source (first + second) =
      quittingMaximalCapSemanticPrefixSurvival reward
          (quittingMaximalCapSemanticPrefixOrbit reward source first) second *
        quittingMaximalCapSemanticPrefixSurvival reward source first := by
  unfold quittingMaximalCapSemanticPrefixSurvival
  rw [quittingMaximalCapSemanticPrefixRootStack_add,
    quittingCapNashStackContinueProduct_append]

theorem quittingMaximalCapSemanticPrefixProfile_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (first second : ℕ) :
    quittingMaximalCapSemanticPrefixProfile reward source terminal
        (first + second) =
      quittingMaximalCapSemanticPrefixProfile reward
        (quittingMaximalCapSemanticPrefixOrbit reward source first)
        (quittingMaximalCapSemanticPrefixProfile reward source terminal first)
        second := by
  unfold quittingMaximalCapSemanticPrefixProfile
  rw [quittingMaximalCapSemanticPrefixRootStack_add,
    quittingLiteralRootStackProfile_append]

end GameTheory
