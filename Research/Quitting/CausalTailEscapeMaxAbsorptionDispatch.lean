/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStrictTailEscapeReturn
import UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed
import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailUniformAbsorption
import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationCompactPath
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPureTimeRectangleDisintegration
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAtomicSupportBoundary
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCapNashNearMinimum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumLawFiniteAtom
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Quitting.Terminal.OpponentTightTerminalSemanticRealization
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefix
import UniformEquilibrium.Quitting.RewardBound
import Research.Quitting.UniqueAllContinueCapStackNoGo

/-!
# Maximal-absorption dispatch for a causal tail escape

The argument treats strict tail escape below a literal causal suffix atom. It
uses compactness of the exact cap--Nash correspondence, exact prefix-debt
scaling, and the return-selection interface. It yields either a same-tail
return or universal quantitative undercharge even at the maximal-absorption
exact root.

The exact cap--Nash correspondence at a fixed tail is compact.  Hence its
one-stage absorption mass has a maximizer.  This removes an artificial
root-selection ambiguity from the causal tail-escape gate:

* if the maximizer spends enough of the tail excess, the existing return gate
  retains the literal suffix atom near the minimum fiber;
* otherwise no exact cap--Nash root at that same tail can spend enough.

The second branch is the precise same-tail obstruction.  It splits further:
the all-Continue root is exact Nash, or the maximal root has positive
absorption forced by a concrete singleton-cap gap but is still quantitatively
undercharged.  Thus finite Nash existence, extremal root selection, and local
singleton-gap forcing are all exhausted.  Any further argument must change
the cap/state or use additional chronology.

The state-changing case allows the literal state and cap to change. Maximal
exact cap roots, semantic prefix scaling, fixed-tail absorption bounds, closed
endpoint Nash graphs, and compactness of the joint terminal semantic/law carrier
yield a nested maximal-root chronology with summable charge, retained suffix
atoms, and finite charged cap rise. The remaining local obstruction is a cap
whose exact Nash correspondence is the singleton all-Continue root.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Absorption attains a maximum on the exact cap--Nash correspondence at a
fixed continuation vector. -/
theorem exists_maximalAbsorption_isZeroQuittingRootNash
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (tail : Payoff iota) :
    ∃ root : iota → PMF Bool,
      IsεQuittingRootNash reward tail 0 root ∧
      ∀ other : iota → PMF Bool,
        IsεQuittingRootNash reward tail 0 other →
          quittingRootAbsorptionMass other ≤
            quittingRootAbsorptionMass root := by
  let roots : Set (QuittingRootSimplex iota) :=
    {root | IsεQuittingRootEndpointNash reward tail 0
      (quittingRootOfSimplex root)}
  have hcompact : IsCompact roots := by
    simpa only [roots] using
      isCompact_setOf_isZeroQuittingRootEndpointNash_root reward tail
  have hnonempty : roots.Nonempty := by
    obtain ⟨root, hroot⟩ :=
      exists_isZeroQuittingRootEndpointNash_simplex reward tail
    exact ⟨root, hroot⟩
  obtain ⟨chosen, hchosen, hmax⟩ := hcompact.exists_isMaxOn hnonempty
    continuous_quittingSimplexAbsorptionMass.continuousOn
  let root := quittingRootOfSimplex chosen
  have hnash : IsεQuittingRootNash reward tail 0 root :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward tail 0 root).1 hchosen
  refine ⟨root, hnash, ?_⟩
  intro other hother
  let otherSimplex : QuittingRootSimplex iota :=
    fun who ↦ stdSimplexEquiv (other who)
  have hotherRoot : quittingRootOfSimplex otherSimplex = other := by
    funext who
    exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (other who)
  have hotherEndpoint : IsεQuittingRootEndpointNash reward tail 0
      (quittingRootOfSimplex otherSimplex) := by
    rw [hotherRoot]
    exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward tail 0 other).2 hother
  rw [isMaxOn_iff] at hmax
  have hmaximal := hmax otherSimplex hotherEndpoint
  rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass,
    quittingSimplexAbsorptionMass_eq_rootAbsorptionMass] at hmaximal
  simpa only [root, hotherRoot] using hmaximal

/-- **Maximal-absorption causal tail dispatch.**

At a strict escaped tail carrying a literal suffix atom, choose an exact
cap--Nash root with maximal absorption.  Positive minimum debt forces this
root to retain positive survival.  Either it returns to the requested
minimum neighborhood and the atom survives literally, or every exact root at
this same tail fails the return selection.

In the universal-failure branch, either all-Continue is already exact Nash,
or a concrete singleton-cap gap forces the maximal root to absorb with the
standard positive modulus.  In the latter case even that forced, maximal
charge is insufficient: this is the sharp local obstruction left after
extremal root selection. -/
theorem exists_maximalCapNash_returnSelection_or_sameTailUndercharge
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum tail : QuittingTerminalSemanticPair iota)
    (tolerance : ℝ) {M : ℝ}
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hescape : quittingTerminalSemanticDebtSum minimum <
      quittingTerminalSemanticDebtSum tail)
    (htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward) :
    ∃ root : iota → PMF Bool,
      IsεQuittingRootNash reward tail.2 0 root ∧
      0 < quittingStationaryContinueMass root ∧
      (∀ other : iota → PMF Bool,
        IsεQuittingRootNash reward tail.2 0 other →
          quittingRootAbsorptionMass other ≤
            quittingRootAbsorptionMass root) ∧
      (IsQuittingCapNashResetReturnSelection
          (reward := reward) minimum tail root tolerance ∨
        ((∀ other : iota → PMF Bool,
            IsεQuittingRootNash reward tail.2 0 other →
              ¬ IsQuittingCapNashResetReturnSelection
                (reward := reward) minimum tail other tolerance) ∧
          quittingTerminalSemanticDebtSum tail *
                quittingRootAbsorptionMass root <
            (quittingTerminalSemanticDebtSum tail -
                quittingTerminalSemanticDebtSum minimum) - tolerance ∧
          (IsεQuittingRootNash reward
              tail.2 0
                (quittingAllContinueRoot : iota → PMF Bool) ∨
            ∃ blocker : iota,
              let eta := reward (quittingSingletonTerminal blocker) blocker -
                tail.2 blocker
              0 < eta ∧
                eta / (eta + 2 * M) ≤
                  quittingRootAbsorptionMass root ∧
                ¬ IsQuittingCapNashResetReturnSelection
                  (reward := reward) minimum tail root tolerance))) := by
  obtain ⟨root, hnash, hmax⟩ :=
    exists_maximalAbsorption_isZeroQuittingRootNash reward tail.2
  have htailDebtNonneg : 0 ≤ quittingTerminalSemanticDebtSum tail :=
    hminimumPositive.le.trans hescape.le
  have hcontinue : 0 < quittingStationaryContinueMass root := by
    have hcontinueNonneg : 0 ≤ quittingStationaryContinueMass root :=
      quittingStationaryContinueMass_nonneg root
    by_contra hnot
    have hcontinueZero : quittingStationaryContinueMass root = 0 :=
      le_antisymm (le_of_not_gt hnot) hcontinueNonneg
    let returned := quittingTerminalSemanticPrefix reward root tail
    have hreturnedCarrier : returned ∈
        quittingTerminalSemanticCarrier reward :=
      quittingTerminalSemanticPrefix_mem_carrier
        reward root tail htailCarrier
    have hreturnedLower := hminimum returned hreturnedCarrier
    have hscale : quittingTerminalSemanticDebtSum returned =
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum tail :=
      quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
        (reward := reward) tail root hnash
    rw [hscale, hcontinueZero, zero_mul] at hreturnedLower
    linarith
  refine ⟨root, hnash, hcontinue, hmax, ?_⟩
  by_cases hselection : IsQuittingCapNashResetReturnSelection
      (reward := reward) minimum tail root tolerance
  · left
    exact hselection
  · right
    have huniversal : ∀ other : iota → PMF Bool,
        IsεQuittingRootNash reward tail.2 0 other →
          ¬ IsQuittingCapNashResetReturnSelection
            (reward := reward) minimum tail other tolerance := by
      intro other hother hotherSelection
      apply hselection
      refine ⟨hnash, ?_⟩
      have habsorption := hmax other hother
      have hscaled :
          quittingTerminalSemanticDebtSum tail *
              quittingRootAbsorptionMass other ≤
            quittingTerminalSemanticDebtSum tail *
              quittingRootAbsorptionMass root :=
        mul_le_mul_of_nonneg_left habsorption htailDebtNonneg
      exact hotherSelection.2.trans hscaled
    have hundercharge :
        quittingTerminalSemanticDebtSum tail *
              quittingRootAbsorptionMass root <
          (quittingTerminalSemanticDebtSum tail -
              quittingTerminalSemanticDebtSum minimum) - tolerance := by
      apply lt_of_not_ge
      intro hcharge
      exact hselection ⟨hnash, hcharge⟩
    refine ⟨huniversal, hundercharge, ?_⟩
    by_cases hallContinue : IsεQuittingRootNash reward tail.2 0
        (quittingAllContinueRoot : iota → PMF Bool)
    · exact Or.inl hallContinue
    · right
      have hnotCap : ¬ ∀ player,
          reward (quittingSingletonTerminal player) player ≤ tail.2 player :=
        fun hcap ↦ hallContinue
          ((isZeroQuittingRootNash_allContinue_iff_singleton_le
            reward tail.2).2 hcap)
      push Not at hnotCap
      obtain ⟨blocker, hgap⟩ := hnotCap
      let eta := reward (quittingSingletonTerminal blocker) blocker -
        tail.2 blocker
      have heta : 0 < eta := by dsimp [eta]; linarith
      have hendpoint : IsεQuittingRootEndpointNash reward tail.2 0 root :=
        (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
          reward tail.2 0 root).2 hnash
      have hgapForm : tail.2 blocker ≤
          reward (quittingSingletonTerminal blocker) blocker - eta := by
        dsimp [eta]
        linarith
      have habsorption :=
        gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
          reward tail.2 root blocker heta hreward hgapForm hendpoint
      exact ⟨blocker, heta, habsorption, hselection⟩

end GameTheory

/-! ## Recursive state-changing maximal prefixes -/

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction Math.Topology
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- A canonical maximal-absorption exact cap root at one literal profile. -/
noncomputable def quittingMaximalCapPrefixRoot
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) : iota → PMF Bool :=
  Classical.choose (exists_maximalAbsorption_isZeroQuittingRootNash reward
    (quittingTerminalSemanticPair reward profile).2)

theorem quittingMaximalCapPrefixRoot_exactNash
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) :
    IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward profile).2 0
        (quittingMaximalCapPrefixRoot reward profile) :=
  (Classical.choose_spec
    (exists_maximalAbsorption_isZeroQuittingRootNash reward
      (quittingTerminalSemanticPair reward profile).2)).1

theorem quittingMaximalCapPrefixRoot_maximal
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (other : iota → PMF Bool)
    (hother : IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward profile).2 0 other) :
    quittingRootAbsorptionMass other ≤
      quittingRootAbsorptionMass
        (quittingMaximalCapPrefixRoot reward profile) :=
  (Classical.choose_spec
    (exists_maximalAbsorption_isZeroQuittingRootNash reward
      (quittingTerminalSemanticPair reward profile).2)).2 other hother

/-- Prefix outward recursively, recomputing a maximal-absorption exact root
against the cap of the newly reached literal state at every step. -/
noncomputable def quittingMaximalCapPrefixProfile
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) :
    ℕ → (quittingGame reward).BehaviorProfile
  | 0 => terminal
  | n + 1 => quittingRootThenContinuationProfile reward
      (quittingMaximalCapPrefixRoot reward
        (quittingMaximalCapPrefixProfile reward terminal n))
      (quittingMaximalCapPrefixProfile reward terminal n)

@[simp] theorem quittingMaximalCapPrefixProfile_zero
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingMaximalCapPrefixProfile reward terminal 0 = terminal := rfl

@[simp] theorem quittingMaximalCapPrefixProfile_succ
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) (n : ℕ) :
    quittingMaximalCapPrefixProfile reward terminal (n + 1) =
      quittingRootThenContinuationProfile reward
        (quittingMaximalCapPrefixRoot reward
          (quittingMaximalCapPrefixProfile reward terminal n))
        (quittingMaximalCapPrefixProfile reward terminal n) := rfl

/-- Exact total-debt recursion along the state-changing maximal-prefix
sequence. -/
theorem quittingMaximalCapPrefixProfile_debt_succ
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (n : ℕ) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal (n + 1))) =
      quittingStationaryContinueMass
          (quittingMaximalCapPrefixRoot reward
            (quittingMaximalCapPrefixProfile reward terminal n)) *
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal n)) := by
  rw [quittingMaximalCapPrefixProfile_succ,
    quittingTerminalSemanticPair_rootThenContinuation reward
      (quittingMaximalCapPrefixRoot reward
        (quittingMaximalCapPrefixProfile reward terminal n))
      (quittingMaximalCapPrefixProfile reward terminal n)]
  exact quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
    (reward := reward)
    (quittingTerminalSemanticPair reward
      (quittingMaximalCapPrefixProfile reward terminal n))
    (quittingMaximalCapPrefixRoot reward
      (quittingMaximalCapPrefixProfile reward terminal n))
    (quittingMaximalCapPrefixRoot_exactNash reward
      (quittingMaximalCapPrefixProfile reward terminal n))

/-- A suffix stage atom is shifted one date and scaled by the exact joint
Continue mass at every recursive prefix. -/
theorem quittingMaximalCapPrefixProfile_stage_succ
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (stage n : ℕ) (coalition : {S : Finset iota // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingMaximalCapPrefixProfile reward terminal (n + 1))
        (n + 1 + stage) coalition =
      quittingStationaryContinueMass
          (quittingMaximalCapPrefixRoot reward
            (quittingMaximalCapPrefixProfile reward terminal n)) *
        quittingStageCoalitionMass reward
          (quittingMaximalCapPrefixProfile reward terminal n)
          (n + stage) coalition := by
  rw [quittingMaximalCapPrefixProfile_succ]
  rw [show n + 1 + stage = (n + stage) + 1 by omega,
    quittingStageCoalitionMass_rootThenContinuation_succ]

/-- Debt and one fixed suffix atom are multiplied by the same recursive
survival factor.  This cross-multiplied form avoids introducing a separate
infinite-product object. -/
theorem quittingMaximalCapPrefixProfile_debt_mul_stage_eq
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (stage n : ℕ) (coalition : {S : Finset iota // S.Nonempty}) :
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward terminal) *
        quittingStageCoalitionMass reward
          (quittingMaximalCapPrefixProfile reward terminal n)
          (n + stage) coalition =
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal n)) *
        quittingStageCoalitionMass reward terminal stage coalition := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [quittingMaximalCapPrefixProfile_stage_succ,
        quittingMaximalCapPrefixProfile_debt_succ
          reward terminal]
      calc
        _ = quittingStationaryContinueMass
              (quittingMaximalCapPrefixRoot reward
                (quittingMaximalCapPrefixProfile reward terminal n)) *
            (quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward terminal) *
              quittingStageCoalitionMass reward
                (quittingMaximalCapPrefixProfile reward terminal n)
                (n + stage) coalition) := by ring
        _ = quittingStationaryContinueMass
              (quittingMaximalCapPrefixRoot reward
                (quittingMaximalCapPrefixProfile reward terminal n)) *
            (quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward
                  (quittingMaximalCapPrefixProfile reward terminal n)) *
              quittingStageCoalitionMass reward terminal stage coalition) := by
                rw [ih]
        _ = _ := by ring

/-- The global positive semantic minimum charges the whole finite prefix of
the recursively changed-state chronology. -/
theorem minimum_mul_sum_maximalCapPrefix_absorption_le_debtDrop
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∀ horizon : ℕ,
      quittingTerminalSemanticDebtSum minimum *
          ∑ n ∈ Finset.range horizon,
            quittingRootAbsorptionMass
              (quittingMaximalCapPrefixRoot reward
                (quittingMaximalCapPrefixProfile reward terminal n)) ≤
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward terminal) -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingMaximalCapPrefixProfile reward terminal horizon)) := by
  intro horizon
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      let profile := quittingMaximalCapPrefixProfile reward terminal horizon
      let root := quittingMaximalCapPrefixRoot reward profile
      let debt := quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile)
      have hcarrier : quittingTerminalSemanticPair reward profile ∈
          quittingTerminalSemanticCarrier reward :=
        quittingTerminalSemanticPair_mem_carrier reward profile
      have hminimumDebt : quittingTerminalSemanticDebtSum minimum ≤ debt :=
        hminimum _ hcarrier
      have habsorption : 0 ≤ quittingRootAbsorptionMass root :=
        quittingRootAbsorptionMass_nonneg root
      have hlocal : quittingTerminalSemanticDebtSum minimum *
            quittingRootAbsorptionMass root ≤
          debt * quittingRootAbsorptionMass root :=
        mul_le_mul_of_nonneg_right hminimumDebt habsorption
      have hstep := quittingMaximalCapPrefixProfile_debt_succ
        reward terminal horizon
      have hlocalDrop : quittingTerminalSemanticDebtSum minimum *
            quittingRootAbsorptionMass root ≤
          debt - quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingMaximalCapPrefixProfile reward terminal (horizon + 1))) := by
        dsimp only [profile, root, debt] at hstep ⊢
        unfold quittingRootAbsorptionMass at hlocal ⊢
        nlinarith
      rw [Finset.sum_range_succ]
      dsimp only [profile, root, debt] at hlocalDrop
      nlinarith [hlocalDrop]

/-- The changed-state maximal-prefix hazards are summable under a positive
global semantic debt floor. -/
theorem summable_maximalCapPrefix_absorption
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum) :
    Summable (fun n ↦ quittingRootAbsorptionMass
      (quittingMaximalCapPrefixRoot reward
        (quittingMaximalCapPrefixProfile reward terminal n))) := by
  refine summable_of_sum_range_le
    (c := quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward terminal) /
      quittingTerminalSemanticDebtSum minimum)
    (fun n ↦ quittingRootAbsorptionMass_nonneg _) ?_
  intro horizon
  have hcharge :=
    minimum_mul_sum_maximalCapPrefix_absorption_le_debtDrop
      reward minimum terminal hminimum horizon
  have hprofileLower := hminimum
    (quittingTerminalSemanticPair reward
      (quittingMaximalCapPrefixProfile reward terminal horizon))
    (quittingTerminalSemanticPair_mem_carrier reward _)
  apply (le_div_iff₀ hminimumPositive).2
  nlinarith

/-- A fixed positive singleton-cap gap cannot persist along the recursively
state-changing chronology.  Otherwise every maximal root would have the
same positive absorption lower bound, contradicting summability. -/
theorem exists_maximalCapPrefix_singletonGapCollapse
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (blocker : iota) (eta : ℝ)
     (heta : 0 < eta)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ n,
      reward (quittingSingletonTerminal blocker) blocker - eta <
        (quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal n)).2 blocker := by
  obtain ⟨M, hM, hreward⟩ :=
    exists_quittingRewardBound reward
  by_contra hnot
  push Not at hnot
  let absorption : ℕ → ℝ := fun n ↦ quittingRootAbsorptionMass
    (quittingMaximalCapPrefixRoot reward
      (quittingMaximalCapPrefixProfile reward terminal n))
  have habsorption : Tendsto absorption atTop (nhds 0) := by
    exact (summable_maximalCapPrefix_absorption reward minimum terminal
      hminimum hminimumPositive).tendsto_atTop_zero
  have hratio : 0 < eta / (eta + 2 * M) := by positivity
  have hsmall : ∀ᶠ n in atTop, absorption n < eta / (eta + 2 * M) :=
    habsorption.eventually (Iio_mem_nhds hratio)
  rw [eventually_atTop] at hsmall
  obtain ⟨n, hn⟩ := hsmall
  have hnSmall := hn n le_rfl
  have hnash := quittingMaximalCapPrefixRoot_exactNash reward
    (quittingMaximalCapPrefixProfile reward terminal n)
  have hendpoint :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward
        (quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal n)).2 0 _).2 hnash
  have hlower := gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
    reward
      (quittingTerminalSemanticPair reward
        (quittingMaximalCapPrefixProfile reward terminal n)).2
      (quittingMaximalCapPrefixRoot reward
        (quittingMaximalCapPrefixProfile reward terminal n))
      blocker heta hreward (hnot n) hendpoint
  exact (not_lt_of_ge hlower) hnSmall

/-- If the original tail has a singleton-cap gap `eta`, some finite changed
state raises that same cap coordinate by more than `eta / 2`.  This is a
cumulative envelope-drift certificate; it is not yet a same-row unilateral
gain or a marked-atom charge. -/
theorem exists_maximalCapPrefix_capRise_halfGap
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (blocker : iota) (eta : ℝ)
     (heta : 0 < eta)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hinitialGap :
      (quittingTerminalSemanticPair reward terminal).2 blocker ≤
        reward (quittingSingletonTerminal blocker) blocker - eta) :
    ∃ n, eta / 2 <
      (quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal n)).2 blocker -
        (quittingTerminalSemanticPair reward terminal).2 blocker := by
  obtain ⟨n, hcollapse⟩ := exists_maximalCapPrefix_singletonGapCollapse
    reward minimum terminal blocker (eta / 2) (by positivity) hminimum
      hminimumPositive
  exact ⟨n, by linarith⟩

/-- Cumulative cap drift along the recursive chronology is paid by the
literal absorption charge of the same finite prefix. -/
theorem abs_maximalCapPrefix_cap_sub_initial_le_charge
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (who : iota) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M) :
    ∀ horizon : ℕ,
      |(quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal horizon)).2 who -
          (quittingTerminalSemanticPair reward terminal).2 who| ≤
        4 * M * ∑ n ∈ Finset.range horizon,
          quittingRootAbsorptionMass
            (quittingMaximalCapPrefixRoot reward
              (quittingMaximalCapPrefixProfile reward terminal n)) := by
  intro horizon
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      let profile := quittingMaximalCapPrefixProfile reward terminal horizon
      let root := quittingMaximalCapPrefixRoot reward profile
      have hstack : IsQuittingCapNashRootStack reward [root] profile := by
        exact ⟨quittingMaximalCapPrefixRoot_exactNash reward profile, trivial⟩
      have hstepRaw :=
        abs_quittingContinuationBestResponseValue_capNashRootStack_sub_terminal_le
          (reward := reward) [root] profile who hreward hstack
      have hstep :
          |(quittingTerminalSemanticPair reward
                (quittingMaximalCapPrefixProfile reward terminal (horizon + 1))).2
                who -
              (quittingTerminalSemanticPair reward profile).2 who| ≤
            4 * M * quittingRootAbsorptionMass root := by
        simpa [quittingMaximalCapPrefixProfile_succ,
          quittingLiteralRootStackProfile, quittingTerminalSemanticPair,
          quittingCapNashStackAbsorptionSum] using hstepRaw
      have htriangle := abs_sub_le
        ((quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal (horizon + 1))).2 who)
        ((quittingTerminalSemanticPair reward profile).2 who)
        ((quittingTerminalSemanticPair reward terminal).2 who)
      rw [Finset.sum_range_succ]
      dsimp only [profile, root] at hstep ⊢
      calc
        _ ≤ |(quittingTerminalSemanticPair reward
                  (quittingMaximalCapPrefixProfile reward terminal (horizon + 1))).2
                  who -
                (quittingTerminalSemanticPair reward
                  (quittingMaximalCapPrefixProfile reward terminal horizon)).2 who| +
              |(quittingTerminalSemanticPair reward
                  (quittingMaximalCapPrefixProfile reward terminal horizon)).2 who -
                (quittingTerminalSemanticPair reward terminal).2 who| :=
            htriangle
        _ ≤ 4 * M * quittingRootAbsorptionMass
                (quittingMaximalCapPrefixRoot reward
                  (quittingMaximalCapPrefixProfile reward terminal horizon)) +
              4 * M * ∑ n ∈ Finset.range horizon,
                quittingRootAbsorptionMass
                  (quittingMaximalCapPrefixRoot reward
                    (quittingMaximalCapPrefixProfile reward terminal n)) :=
            add_le_add hstep ih
        _ = _ := by ring

/-- Every fixed suffix atom retains the debt-ratio fraction of its original
mass throughout the changed-state maximal-prefix chronology. -/
theorem maximalCapPrefix_atomMass_lowerBound
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (stage n : ℕ) (coalition : {S : Finset iota // S.Nonempty})
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum) :
    quittingTerminalSemanticDebtSum minimum /
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward terminal) *
        quittingStageCoalitionMass reward terminal stage coalition ≤
      quittingStageCoalitionMass reward
        (quittingMaximalCapPrefixProfile reward terminal n)
        (n + stage) coalition := by
  let initialDebt := quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward terminal)
  let currentDebt := quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward
      (quittingMaximalCapPrefixProfile reward terminal n))
  let initialMass := quittingStageCoalitionMass reward terminal stage coalition
  let currentMass := quittingStageCoalitionMass reward
    (quittingMaximalCapPrefixProfile reward terminal n) (n + stage) coalition
  have hinitialPositive : 0 < initialDebt :=
    hminimumPositive.trans_le (hminimum _
      (quittingTerminalSemanticPair_mem_carrier reward terminal))
  have hcurrentLower : quittingTerminalSemanticDebtSum minimum ≤ currentDebt :=
    hminimum _ (quittingTerminalSemanticPair_mem_carrier reward _)
  have hinitialMassNonneg : 0 ≤ initialMass :=
    quittingStageCoalitionMass_nonneg reward terminal stage coalition
  have hscaled : quittingTerminalSemanticDebtSum minimum * initialMass ≤
      currentDebt * initialMass :=
    mul_le_mul_of_nonneg_right hcurrentLower hinitialMassNonneg
  have hinvariant := quittingMaximalCapPrefixProfile_debt_mul_stage_eq
    reward terminal stage n coalition
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hinitialPositive).2
  rw [mul_comm _
    (quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward terminal)), hinvariant]
  exact hscaled

/-- **Smallest state-changing transport interface.**

An initial singleton-cap gap forces one finite nested exact chronology whose
same cap coordinate rises, whose actual absorption charge pays that rise,
and whose shifted causal suffix atom retains the uniform debt-ratio mass.
All three facts concern the same changed-state profile.  What remains absent
is an owner decoder turning the jointly generated cap rise or charge into one
legal unilateral gain. -/
theorem exists_maximalCapPrefix_chargedCapRise_retainingAtom
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (blocker : iota) (eta : ℝ)
    (stage : ℕ) (coalition : {S : Finset iota // S.Nonempty})
    {M : ℝ} (heta : 0 < eta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hinitialGap :
      (quittingTerminalSemanticPair reward terminal).2 blocker ≤
        reward (quittingSingletonTerminal blocker) blocker - eta) :
    ∃ horizon,
      eta / 2 <
        (quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal horizon)).2 blocker -
          (quittingTerminalSemanticPair reward terminal).2 blocker ∧
      eta / 2 < 4 * M * ∑ n ∈ Finset.range horizon,
        quittingRootAbsorptionMass
          (quittingMaximalCapPrefixRoot reward
            (quittingMaximalCapPrefixProfile reward terminal n)) ∧
      quittingTerminalSemanticDebtSum minimum /
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward terminal) *
          quittingStageCoalitionMass reward terminal stage coalition ≤
        quittingStageCoalitionMass reward
          (quittingMaximalCapPrefixProfile reward terminal horizon)
          (horizon + stage) coalition := by
  obtain ⟨horizon, hrise⟩ := exists_maximalCapPrefix_capRise_halfGap
    reward minimum terminal blocker eta heta hminimum
      hminimumPositive hinitialGap
  have hcapBound := abs_maximalCapPrefix_cap_sub_initial_le_charge
    reward terminal blocker hreward horizon
  have hrisePositive : 0 <
      (quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal horizon)).2 blocker -
        (quittingTerminalSemanticPair reward terminal).2 blocker := by
    linarith
  have hriseAbs : eta / 2 <
      |(quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal horizon)).2 blocker -
        (quittingTerminalSemanticPair reward terminal).2 blocker| := by
    rw [abs_of_pos hrisePositive]
    exact hrise
  refine ⟨horizon, hrise, hriseAbs.trans_le hcapBound, ?_⟩
  exact maximalCapPrefix_atomMass_lowerBound reward minimum terminal stage
    horizon coalition hminimum hminimumPositive

/-- **State-changing limit of universal same-tail undercharge.**

Recursively recomputing a maximal exact cap root produces a genuinely nested
literal chronology.  If none of its states enters the requested minimum
neighborhood, a joint semantic/law subsequence converges to an off-minimum
point which retains a uniform fraction of the original causal suffix atom.
The roots converge to all-Continue, so closed endpoint complementarity makes
all-Continue exact Nash at the limiting cap.

Maximality is deliberately not passed to the limit.  The conclusion instead
exposes the exhaustive residual: either the limiting exact-Nash
correspondence is the singleton all-Continue root, or a positive-absorption
root appears discontinuously at the limiting cap.  The latter is the precise
support-entry branch that a changed-state return theorem would have to
consume. -/
theorem exists_offMinimum_retainedLaw_allContinue_or_supportEntry
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (coalition : {S : Finset iota // S.Nonempty})
    (tolerance : ℝ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hatom : 0 < quittingStageCoalitionMass reward terminal stage coalition)
    (hnoReturn : ∀ n,
      quittingTerminalSemanticDebtSum minimum + tolerance <
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal n))) :
    ∃ cluster : QuittingTerminalSemanticLawPoint iota,
      cluster ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebtSum minimum + tolerance ≤
        quittingTerminalSemanticDebtSum cluster.1 ∧
      quittingTerminalSemanticDebtSum minimum /
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward terminal) *
          quittingStageCoalitionMass reward terminal stage coalition ≤
        cluster.2 (some coalition) ∧
      0 < cluster.2 (some coalition) ∧
      IsεQuittingRootNash reward cluster.1.2 0
        (quittingAllContinueRoot : iota → PMF Bool) ∧
      ((∀ root : iota → PMF Bool,
          IsεQuittingRootNash reward cluster.1.2 0 root →
            root = (quittingAllContinueRoot : iota → PMF Bool)) ∨
        ∃ root : iota → PMF Bool,
          IsεQuittingRootNash reward cluster.1.2 0 root ∧
            0 < quittingRootAbsorptionMass root) := by
  let profile : ℕ → (quittingGame reward).BehaviorProfile :=
    quittingMaximalCapPrefixProfile reward terminal
  let root : ℕ → iota → PMF Bool := fun n ↦
    quittingMaximalCapPrefixRoot reward (profile n)
  let point : ℕ → QuittingTerminalSemanticLawPoint iota := fun n ↦
    (quittingTerminalSemanticPair reward (profile n),
      quittingTerminalOutcomeMass reward (profile n))
  have habsorption : Tendsto
      (fun n ↦ quittingRootAbsorptionMass (root n)) atTop (nhds 0) := by
    exact (summable_maximalCapPrefix_absorption reward minimum terminal
      hminimum hminimumPositive).tendsto_atTop_zero
  have hquit : ∀ who, Tendsto (fun n ↦ (root n who true).toReal)
      atTop (nhds 0) := by
    intro who
    apply squeeze_zero
    · exact fun _ ↦ ENNReal.toReal_nonneg
    · exact fun n ↦ quitProbability_le_quittingRootAbsorptionMass
        (root n) who
    · exact habsorption
  let simplexRoot : ℕ → QuittingRootSimplex iota :=
    fun n who ↦ stdSimplexEquiv (root n who)
  have hsimplexRoot : Tendsto simplexRoot atTop
      (nhds (quittingAllContinueSimplexRoot : QuittingRootSimplex iota)) := by
    rw [tendsto_pi_nhds]
    intro who
    rw [tendsto_subtype_rng, tendsto_pi_nhds]
    intro action
    have hcoordinate : ∀ n,
        ((simplexRoot n who : stdSimplex ℝ Bool) : Bool → ℝ) action =
          (root n who action).toReal := by
      intro n
      exact congrFun (coe_stdSimplexEquiv_apply (root n who)) action
    have hallCoordinate :
        (((quittingAllContinueSimplexRoot : QuittingRootSimplex iota) who :
          stdSimplex ℝ Bool) : Bool → ℝ) action =
            (PMF.pure false action).toReal := by
      exact congrFun (coe_stdSimplexEquiv_apply (PMF.pure false)) action
    have hbase : Tendsto (fun n ↦ (root n who action).toReal)
        atTop (nhds ((PMF.pure false action).toReal)) := by
      cases action with
      | true => simpa using hquit who
      | false =>
          have hidentity : (fun n ↦ (root n who false).toReal) =
              fun n ↦ 1 - (root n who true).toReal := by
            funext n
            linarith [quittingRoot_continueProbability_add_quitProbability
              (root n) who]
          rw [hidentity]
          simpa using tendsto_const_nhds.sub (hquit who)
    have hactual := hbase.congr'
      (Filter.Eventually.of_forall fun n ↦ (hcoordinate n).symm)
    convert hactual using 1
    · rfl
    · exact congrArg nhds hallCoordinate
  have hpointMem : ∀ n, point n ∈
      quittingTerminalSemanticLawCarrier reward := by
    intro n
    exact quittingTerminalSemanticLawPoint_mem_carrier reward (profile n)
  obtain ⟨cluster, hcluster, subseq, hsubseq, hpointLimit⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq
      hpointMem
  have hpairLimit : Tendsto (fun rank ↦ (point (subseq rank)).1)
      atTop (nhds cluster.1) :=
    continuous_fst.continuousAt.tendsto.comp hpointLimit
  have hcapLimit : Tendsto (fun rank ↦ (point (subseq rank)).1.2)
      atTop (nhds cluster.1.2) :=
    continuous_snd.continuousAt.tendsto.comp hpairLimit
  have hrootLimit : Tendsto (fun rank ↦ simplexRoot (subseq rank))
      atTop (nhds (quittingAllContinueSimplexRoot : QuittingRootSimplex iota)) :=
    hsimplexRoot.comp hsubseq.tendsto_atTop
  have hnashLimit : IsεQuittingRootEndpointNash reward cluster.1.2 0
      (quittingRootOfSimplex
        (quittingAllContinueSimplexRoot : QuittingRootSimplex iota)) := by
    apply isεQuittingRootEndpointNash_of_tendsto reward
      (fun _ : ℕ ↦ 0) (fun rank ↦ (point (subseq rank)).1.2)
      (fun rank ↦ simplexRoot (subseq rank))
      tendsto_const_nhds hcapLimit hrootLimit
    filter_upwards [] with rank
    have hnash := quittingMaximalCapPrefixRoot_exactNash reward
      (profile (subseq rank))
    have hrootEq : quittingRootOfSimplex (simplexRoot (subseq rank)) =
        root (subseq rank) := by
      funext who
      exact (stdSimplexEquiv (α := Bool)).symm_apply_apply
        (root (subseq rank) who)
    rw [hrootEq]
    exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward (point (subseq rank)).1.2 0 (root (subseq rank))).2 hnash
  have hdebtLimit : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum (point (subseq rank)).1)
      atTop (nhds (quittingTerminalSemanticDebtSum cluster.1)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      hpairLimit
  have hoffMinimum : quittingTerminalSemanticDebtSum minimum + tolerance ≤
      quittingTerminalSemanticDebtSum cluster.1 :=
    ge_of_tendsto' hdebtLimit fun rank ↦ (hnoReturn (subseq rank)).le
  have hlawLimit : Tendsto (fun rank ↦
      (point (subseq rank)).2 (some coalition)) atTop
      (nhds (cluster.2 (some coalition))) :=
    ((continuous_apply (some coalition)).comp continuous_snd).continuousAt.tendsto.comp
      hpointLimit
  let lower := quittingTerminalSemanticDebtSum minimum /
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward terminal) *
      quittingStageCoalitionMass reward terminal stage coalition
  have hlower : ∀ n, lower ≤ (point n).2 (some coalition) := by
    intro n
    have hstageLower := maximalCapPrefix_atomMass_lowerBound
      reward minimum terminal stage n coalition hminimum hminimumPositive
    have hstageToLaw := quittingStageCoalitionMass_le_terminalOutcomeMass
      reward (profile n) (n + stage) coalition
    exact hstageLower.trans hstageToLaw
  have hlawLower : lower ≤ cluster.2 (some coalition) :=
    ge_of_tendsto' hlawLimit fun rank ↦ hlower (subseq rank)
  have hinitialDebtPositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward terminal) :=
    hminimumPositive.trans_le (hminimum _
      (quittingTerminalSemanticPair_mem_carrier reward terminal))
  have hlowerPositive : 0 < lower := by
    exact mul_pos (div_pos hminimumPositive hinitialDebtPositive) hatom
  have hnashAllContinue : IsεQuittingRootNash reward cluster.1.2 0
      (quittingAllContinueRoot : iota → PMF Bool) := by
    rw [← quittingRootOfSimplex_allContinueSimplexRoot]
    exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward cluster.1.2 0 _).1 hnashLimit
  refine ⟨cluster, hcluster, hoffMinimum, hlawLower,
    hlowerPositive.trans_le hlawLower, hnashAllContinue, ?_⟩
  by_cases hunique : ∀ candidate : iota → PMF Bool,
      IsεQuittingRootNash reward cluster.1.2 0 candidate →
        candidate = (quittingAllContinueRoot : iota → PMF Bool)
  · exact Or.inl hunique
  · right
    push Not at hunique
    obtain ⟨candidate, hnash, hne⟩ := hunique
    refine ⟨candidate, hnash, ?_⟩
    have habsorptionNonneg : 0 ≤ quittingRootAbsorptionMass candidate :=
      quittingRootAbsorptionMass_nonneg candidate
    apply lt_of_le_of_ne habsorptionNonneg
    intro hzero
    have hcontinue : quittingStationaryContinueMass candidate = 1 := by
      unfold quittingRootAbsorptionMass at hzero
      linarith
    apply hne
    funext who
    simpa [quittingAllContinueRoot] using
      eq_pure_false_of_quittingStationaryContinueMass_eq_one hcontinue who

/-! ## Exact punishment-prefix realization of the changed-cap chronology -/

/-- The recursively recomputed maximal-cap roots, read in their natural
outward order, form an exact punishment-floor prefix on the *behavioral cap*
states.  Thus their absorption sum is not merely an analytic charge: it is
already accepted by the canonical finite-prefix capacity interface.

The construction uses no extra residual predicate. -/
noncomputable def quittingMaximalCapPrefixPunishmentFloorPrefix
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (horizon : ℕ) : QuittingPunishmentFloorFinitePrefix reward where
  roots := fun time ↦ quittingMaximalCapPrefixRoot reward
    (quittingMaximalCapPrefixProfile reward terminal time)
  value := fun time ↦
    (quittingTerminalSemanticPair reward
      (quittingMaximalCapPrefixProfile reward terminal time)).2
  horizon := horizon
  value_mem := by
    intro time _
    constructor
    · intro who
      exact neg_le_of_abs_le
        (abs_quittingContinuationBestResponseValue_le reward
          (quittingMaximalCapPrefixProfile reward terminal time) who
          (abs_reward_le_quittingRewardBound reward))
    · intro who
      exact le_of_abs_le
        (abs_quittingContinuationBestResponseValue_le reward
          (quittingMaximalCapPrefixProfile reward terminal time) who
          (abs_reward_le_quittingRewardBound reward))
  anchor_floor := by
    intro who
    exact quittingPunishmentValue_le_terminalSemanticEnvelope
      (quittingTerminalSemanticPair reward terminal)
      (quittingTerminalSemanticPair_mem_carrier reward terminal) who
  policy := by
    intro time _
    rw [quittingMaximalCapPrefixProfile_succ,
      quittingTerminalSemanticPair_rootThenContinuation reward
        (quittingMaximalCapPrefixRoot reward
          (quittingMaximalCapPrefixProfile reward terminal time))
        (quittingMaximalCapPrefixProfile reward terminal time)]
    exact
      quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
        (reward := reward)
        (quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal time))
        (quittingMaximalCapPrefixRoot reward
          (quittingMaximalCapPrefixProfile reward terminal time))
        (quittingMaximalCapPrefixRoot_exactNash reward
          (quittingMaximalCapPrefixProfile reward terminal time))
  exactNash := by
    intro time _
    exact quittingMaximalCapPrefixRoot_exactNash reward
      (quittingMaximalCapPrefixProfile reward terminal time)

@[simp]
theorem quittingMaximalCapPrefixPunishmentFloorPrefix_charge
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (horizon : ℕ) :
    (quittingMaximalCapPrefixPunishmentFloorPrefix
        reward terminal horizon).charge =
      ∑ n ∈ Finset.range horizon,
        quittingRootAbsorptionMass
          (quittingMaximalCapPrefixRoot reward
            (quittingMaximalCapPrefixProfile reward terminal n)) := by
  rfl

/-- **Capacity-exhaustion no-go for the maximal-cap chronology.**  Although
every finite segment is a legal punishment-floor prefix, its charge is
uniformly bounded by the initial semantic excess divided by the positive
minimum debt.  Consequently this chronology cannot by itself trigger the
unbounded-prefix-charge compiler.  Any closure through capacity must
produce charge not already paid by this debt-scaling telescope. -/
theorem maximalCapPrefixPunishmentFloorPrefix_charge_le_semanticBudget
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (horizon : ℕ) :
    (quittingMaximalCapPrefixPunishmentFloorPrefix
        reward terminal horizon).charge ≤
      (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward terminal) -
        quittingTerminalSemanticDebtSum minimum) /
          quittingTerminalSemanticDebtSum minimum := by
  rw [quittingMaximalCapPrefixPunishmentFloorPrefix_charge]
  have hcharged := minimum_mul_sum_maximalCapPrefix_absorption_le_debtDrop
    reward minimum terminal hminimum horizon
  have hfinalLower := hminimum
    (quittingTerminalSemanticPair reward
      (quittingMaximalCapPrefixProfile reward terminal horizon))
    (quittingTerminalSemanticPair_mem_carrier reward _)
  apply (le_div_iff₀ hminimumPositive).2
  nlinarith

/-- **Hard state-change reduction.**  At a positive global semantic minimum, the
first state-changing maximal cap root has only two possibilities.  If it has
positive absorption, it is already a positively charged exact
punishment-floor prefix and it literally retains every positive suffix atom.
If it has zero absorption, maximality forces *every* exact root against the
same cap to be all-Continue.

Consequently neither a separate owner decoder nor a support-entry decoder is
needed for the positive-absorption branch.  The unique all-Continue
correspondence is the sole surviving local obstruction. -/
theorem maximalCapPrefix_positivePunishmentCharge_retainingAtom_or_uniqueAllContinue
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (coalition : {S : Finset iota // S.Nonempty})
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hatom : 0 <
      quittingStageCoalitionMass reward terminal stage coalition) :
    (0 < (quittingMaximalCapPrefixPunishmentFloorPrefix
          reward terminal 1).charge ∧
      0 < quittingStageCoalitionMass reward
        (quittingMaximalCapPrefixProfile reward terminal 1)
        (1 + stage) coalition) ∨
      ∀ candidate : iota → PMF Bool,
        IsεQuittingRootNash reward
            (quittingTerminalSemanticPair reward terminal).2 0 candidate →
          candidate = (quittingAllContinueRoot : iota → PMF Bool) := by
  let root := quittingMaximalCapPrefixRoot reward terminal
  have hnash : IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward terminal).2 0 root := by
    exact quittingMaximalCapPrefixRoot_exactNash reward terminal
  have hcontinue : 0 < quittingStationaryContinueMass root := by
    have hcontinueNonneg : 0 ≤ quittingStationaryContinueMass root :=
      quittingStationaryContinueMass_nonneg root
    by_contra hnot
    have hcontinueZero : quittingStationaryContinueMass root = 0 :=
      le_antisymm (le_of_not_gt hnot) hcontinueNonneg
    have hnextLower := hminimum
      (quittingTerminalSemanticPair reward
        (quittingMaximalCapPrefixProfile reward terminal 1))
      (quittingTerminalSemanticPair_mem_carrier reward _)
    have hstep := quittingMaximalCapPrefixProfile_debt_succ
      reward terminal 0
    change quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal 1)) =
      quittingStationaryContinueMass root *
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward terminal) at hstep
    rw [hcontinueZero, zero_mul] at hstep
    rw [hstep] at hnextLower
    linarith
  by_cases hpositive : 0 < quittingRootAbsorptionMass root
  · left
    constructor
    · change 0 < ∑ n ∈ Finset.range 1,
          quittingRootAbsorptionMass
            (quittingMaximalCapPrefixRoot reward
              (quittingMaximalCapPrefixProfile reward terminal n))
      simpa [root]
    · have hstage := quittingMaximalCapPrefixProfile_stage_succ
        reward terminal stage 0 coalition
      have hstage' : quittingStageCoalitionMass reward
          (quittingMaximalCapPrefixProfile reward terminal 1)
            (1 + stage) coalition =
        quittingStationaryContinueMass root *
          quittingStageCoalitionMass reward terminal stage coalition := by
        simpa [root] using hstage
      rw [hstage']
      exact mul_pos hcontinue hatom
  · right
    have hrootZero : quittingRootAbsorptionMass root = 0 :=
      le_antisymm (le_of_not_gt hpositive)
        (quittingRootAbsorptionMass_nonneg root)
    intro candidate hcandidate
    have hle := quittingMaximalCapPrefixRoot_maximal
      reward terminal candidate hcandidate
    have hcandidateZero : quittingRootAbsorptionMass candidate = 0 := by
      apply le_antisymm
      · simpa [root, hrootZero] using hle
      · exact quittingRootAbsorptionMass_nonneg candidate
    have hcandidateContinue : quittingStationaryContinueMass candidate = 1 := by
      unfold quittingRootAbsorptionMass at hcandidateZero
      linarith
    funext who
    simpa [quittingAllContinueRoot] using
      eq_pure_false_of_quittingStationaryContinueMass_eq_one
        hcandidateContinue who

/-- The charged cap-rise/atom-retention theorem lands directly in the exact
punishment-prefix family.  This discharges the previously claimed "owner
decoder" gap for this branch: the cap rise need not first be decoded as a
same-row deviation in order for the canonical capacity to consume its
absorption charge. -/
theorem exists_maximalCapPrefix_punishmentFloorCharge_retainingAtom
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (blocker : iota) (eta : ℝ)
    (stage : ℕ) (coalition : {S : Finset iota // S.Nonempty})
    (heta : 0 < eta)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hinitialGap :
      (quittingTerminalSemanticPair reward terminal).2 blocker ≤
        reward (quittingSingletonTerminal blocker) blocker - eta) :
    ∃ horizon,
      let cert := quittingMaximalCapPrefixPunishmentFloorPrefix
        reward terminal horizon
      eta / 2 <
          (quittingTerminalSemanticPair reward
              (quittingMaximalCapPrefixProfile reward terminal horizon)).2
                blocker -
            (quittingTerminalSemanticPair reward terminal).2 blocker ∧
        eta / 2 < 4 * quittingRewardBound reward * cert.charge ∧
        quittingTerminalSemanticDebtSum minimum /
              quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward terminal) *
            quittingStageCoalitionMass reward terminal stage coalition ≤
            quittingStageCoalitionMass reward
            (quittingMaximalCapPrefixProfile reward terminal horizon)
            (horizon + stage) coalition := by
  obtain ⟨horizon, hrise, hcharge, hatom⟩ :=
    exists_maximalCapPrefix_chargedCapRise_retainingAtom
      reward minimum terminal blocker eta stage coalition
        heta (abs_reward_le_quittingRewardBound reward)
        hminimum hminimumPositive hinitialGap
  refine ⟨horizon, hrise, ?_, hatom⟩
  simpa using hcharge

/-! ## Same-point causal-atom consumption -/

/-- The strategic output obtained by applying the first maximal-cap prefix to
one actual positive row selected from a causal suffix-atom packet.

The retained exact cap stack is longer than any requested depth.  The
positive-charge arm is a one-step exact punishment-floor prefix.  It does not
assert that the resulting behavioral profile is globally cap--Nash or uniform.
In the other arm the same retained stack is literally all-Continue, has zero
charge, and fixes the full semantic pair and terminal law. -/
structure QuittingMinimumLawCausalSuffixMaximalCapDispatch
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (requestedDepth : ℕ) where
  chronologyIndex : ℕ
  profile : (quittingGame reward).BehaviorProfile
  stage : ℕ
  roots : List (iota → PMF Bool)
  roots_length : roots.length = chronologyIndex + 1
  requestedDepth_lt_roots_length : requestedDepth < roots.length
  rootStack : IsQuittingCapNashRootStack reward roots profile
  pointAtom_pos : 0 < point.2 (some atom.terminal)
  sourceAtom_pos :
    0 < quittingStageCoalitionMass reward profile stage atom.terminal
  shiftedSourceAtom_pos :
    0 < quittingStageCoalitionMass reward
      (quittingLiteralRootStackProfile reward roots profile)
      (chronologyIndex + 1 + stage) atom.terminal
  oneStepCharge_retainingAtom_or_uniqueAllContinue :
    (0 < (quittingMaximalCapPrefixPunishmentFloorPrefix
          reward profile 1).charge ∧
        0 < quittingStageCoalitionMass reward
          (quittingMaximalCapPrefixProfile reward profile 1)
          (1 + stage) atom.terminal) ∨
      ((∀ candidate : iota → PMF Bool,
        IsεQuittingRootNash reward
            (quittingTerminalSemanticPair reward profile).2 0 candidate →
          candidate = (quittingAllContinueRoot : iota → PMF Bool)) ∧
        roots = List.replicate roots.length
          (quittingAllContinueRoot : iota → PMF Bool) ∧
        quittingCapNashStackAbsorptionSum roots = 0 ∧
        quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots profile) =
          quittingTerminalSemanticPair reward profile ∧
        quittingTerminalOutcomeMass reward
            (quittingLiteralRootStackProfile reward roots profile) =
          quittingTerminalOutcomeMass reward profile)

/-- A causal suffix-atom packet has an actual literal positive row at which
the first maximal exact cap root either gives positive punishment-prefix
charge while retaining that same row, or the exact cap--Nash correspondence
is the singleton all-Continue root.

The selected coalition is exactly the finite atom of `point`; neither the
terminal law nor the behavioral cap is reprojected.  The selected source stack
can be required to exceed any prescribed finite depth. -/
theorem QuittingMinimumLawCausalSuffixAtom.nonempty_maximalCapDispatch
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (requestedDepth : ℕ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum point.1) :
    Nonempty
      (QuittingMinimumLawCausalSuffixMaximalCapDispatch
        reward point atom requestedDepth) := by
  obtain ⟨profiles, _cutoff, mark, roots, _hprofiles, hlength,
      hstack, _hdebt, heventual⟩ := atom.chronology
  rw [eventually_atTop] at heventual
  obtain ⟨first, hfirst⟩ := heventual
  let index := max first requestedDepth
  have hrow := hfirst index (le_max_left first requestedDepth)
  let profile := profiles index
  let stage := mark index
  let selectedRoots := roots index
  have hselectedLength : selectedRoots.length = index + 1 := by
    simpa only [selectedRoots] using hlength index
  have hdepth : requestedDepth < selectedRoots.length := by
    rw [hselectedLength]
    dsimp only [index]
    omega
  have hselectedStack :
      IsQuittingCapNashRootStack reward selectedRoots profile := by
    simpa only [selectedRoots, profile] using hstack index
  have hsourceAtom : 0 <
      quittingStageCoalitionMass reward profile stage atom.terminal := by
    simpa only [profile, stage] using hrow.2.2.1
  have hshiftedAtom : 0 < quittingStageCoalitionMass reward
      (quittingLiteralRootStackProfile reward selectedRoots profile)
      (index + 1 + stage) atom.terminal := by
    simpa only [selectedRoots, profile, stage] using hrow.2.2.2
  have hdispatch :=
    maximalCapPrefix_positivePunishmentCharge_retainingAtom_or_uniqueAllContinue
      reward point.1 profile stage atom.terminal hminimum hminimumPositive
        hsourceAtom
  have hstrongDispatch :
      (0 < (quittingMaximalCapPrefixPunishmentFloorPrefix
            reward profile 1).charge ∧
          0 < quittingStageCoalitionMass reward
            (quittingMaximalCapPrefixProfile reward profile 1)
            (1 + stage) atom.terminal) ∨
        ((∀ candidate : iota → PMF Bool,
            IsεQuittingRootNash reward
                (quittingTerminalSemanticPair reward profile).2 0 candidate →
              candidate = (quittingAllContinueRoot : iota → PMF Bool)) ∧
          selectedRoots = List.replicate selectedRoots.length
            (quittingAllContinueRoot : iota → PMF Bool) ∧
          quittingCapNashStackAbsorptionSum selectedRoots = 0 ∧
          quittingTerminalSemanticPair reward
              (quittingLiteralRootStackProfile reward selectedRoots profile) =
            quittingTerminalSemanticPair reward profile ∧
          quittingTerminalOutcomeMass reward
              (quittingLiteralRootStackProfile reward selectedRoots profile) =
            quittingTerminalOutcomeMass reward profile) := by
    rcases hdispatch with hpositive | hunique
    · exact Or.inl hpositive
    · right
      have hstackData :=
        capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap
          reward profile selectedRoots hunique hselectedStack
      have hcharge :=
        capNashStackAbsorptionSum_eq_zero_of_unique_terminalCap
          reward profile selectedRoots hunique hselectedStack
      have hlaw :=
        capNashRootStack_terminalOutcomeMass_eq_of_unique_terminalCap
          reward profile selectedRoots hunique hselectedStack
      exact ⟨hunique, hstackData.1, hcharge, hstackData.2, hlaw⟩
  exact ⟨{
    chronologyIndex := index
    profile := profile
    stage := stage
    roots := selectedRoots
    roots_length := hselectedLength
    requestedDepth_lt_roots_length := hdepth
    rootStack := hselectedStack
    pointAtom_pos := atom.terminalMass_pos
    sourceAtom_pos := hsourceAtom
    shiftedSourceAtom_pos := hshiftedAtom
    oneStepCharge_retainingAtom_or_uniqueAllContinue := hstrongDispatch }⟩

/-- In a punishment-normal quitting game with no uniform-equilibrium payoff,
every supplied globally minimizing joint-law point has one same-point finite
atom whose actual causal rows satisfy the maximal-cap dispatch beyond every
prescribed finite depth.

This is a local exact-prefix alternative.  Its positive-charge branch is not
a global cap--Nash or uniform-equilibrium conclusion. -/
theorem exists_minimumLawCausalSuffixMaximalCapDispatch_of_punishmentNormal_of_not_uniform
    [Nonempty iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (hno : ¬∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (point : QuittingTerminalSemanticLawPoint iota)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ atom : QuittingMinimumLawCausalSuffixAtom reward point,
      ∀ requestedDepth,
        Nonempty
          (QuittingMinimumLawCausalSuffixMaximalCapDispatch
            reward point atom requestedDepth) := by
  obtain ⟨atom⟩ :=
    nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff
      reward hno hnormal point hpoint hminimum
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr
      hno
  have hcarrier := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hminimumValue : quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalDebtSumInf reward :=
    (quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      point.1 hcarrier hminimum).symm
  have hminimumPositive : 0 <
      quittingTerminalSemanticDebtSum point.1 := by
    rw [hminimumValue]
    exact hinf
  exact ⟨atom, fun requestedDepth ↦ atom.nonempty_maximalCapDispatch
    reward point requestedDepth hminimum hminimumPositive⟩

/-! ## Eventual minimum-cap freeze -/

/-- An arbitrarily deep exact source stack selected from a causal atom packet
after the near-minimum cap-freezing radius has been entered.

Every stored equality concerns the same literal suffix profile, exact root
word, and finite atom.  The stack is inert; this structure does not assert
that an inert stack yields a uniform-equilibrium payoff or a contradiction. -/
structure QuittingMinimumLawCausalSuffixInertCapStack
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (requestedDepth : ℕ) where
  chronologyIndex : ℕ
  profile : (quittingGame reward).BehaviorProfile
  stage : ℕ
  roots : List (iota → PMF Bool)
  roots_length : roots.length = chronologyIndex + 1
  requestedDepth_lt_roots_length : requestedDepth < roots.length
  rootStack : IsQuittingCapNashRootStack reward roots profile
  pointAtom_pos : 0 < point.2 (some atom.terminal)
  sourceAtom_pos :
    0 < quittingStageCoalitionMass reward profile stage atom.terminal
  shiftedSourceAtom_pos :
    0 < quittingStageCoalitionMass reward
      (quittingLiteralRootStackProfile reward roots profile)
      (chronologyIndex + 1 + stage) atom.terminal
  cap_uniqueAllContinue : ∀ candidate : iota → PMF Bool,
    IsεQuittingRootNash reward
        (quittingTerminalSemanticPair reward profile).2 0 candidate →
      candidate = (quittingAllContinueRoot : iota → PMF Bool)
  roots_eq_replicate_allContinue :
    roots = List.replicate roots.length
      (quittingAllContinueRoot : iota → PMF Bool)
  absorptionSum_eq_zero : quittingCapNashStackAbsorptionSum roots = 0
  semanticPair_eq :
    quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots profile) =
      quittingTerminalSemanticPair reward profile
  terminalOutcomeMass_eq :
    quittingTerminalOutcomeMass reward
        (quittingLiteralRootStackProfile reward roots profile) =
      quittingTerminalOutcomeMass reward profile

/-- Near-minimum cap freezing consumes the positive-charge arm of the causal
packet dispatch.  Beyond every prescribed finite depth, one of the packet's
actual source-matched exact stacks is literally replicated all-Continue,
zero-charge, and invariant in both semantic and complete terminal-law
coordinates, while retaining the same positive finite atom. -/
theorem QuittingMinimumLawCausalSuffixAtom.nonempty_inertCapStack
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (requestedDepth : ℕ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum point.1) :
    Nonempty
      (QuittingMinimumLawCausalSuffixInertCapStack
        reward point atom requestedDepth) := by
  obtain ⟨epsilon, hepsilon, hfreeze⟩ :=
    exists_pos_nearMinimum_capNash_eq_allContinue_radius
      (reward := reward) (quittingTerminalSemanticDebtSum point.1)
        hminimumPositive hminimum
  obtain ⟨profiles, _cutoff, mark, roots, hprofiles, hlength,
      hstack, _hdebt, hatomEventually⟩ := atom.chronology
  have hpairTendsto : Tendsto
      (fun n ↦ quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds point.1) :=
    continuous_fst.continuousAt.tendsto.comp hprofiles
  have hdebtTendsto : Tendsto
      (fun n ↦ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profiles n)))
      atTop (nhds (quittingTerminalSemanticDebtSum point.1)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      hpairTendsto
  have hnearEventually : ∀ᶠ n in atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles n)) <
        quittingTerminalSemanticDebtSum point.1 + epsilon :=
    (tendsto_order.1 hdebtTendsto).2
      (quittingTerminalSemanticDebtSum point.1 + epsilon) (by linarith)
  have hdataEventually := hatomEventually.and hnearEventually
  rw [eventually_atTop] at hdataEventually
  obtain ⟨first, hfirst⟩ := hdataEventually
  let index := max first requestedDepth
  have hdata := hfirst index (le_max_left first requestedDepth)
  let profile := profiles index
  let stage := mark index
  let selectedRoots := roots index
  have hselectedLength : selectedRoots.length = index + 1 := by
    simpa only [selectedRoots] using hlength index
  have hdepth : requestedDepth < selectedRoots.length := by
    rw [hselectedLength]
    dsimp only [index]
    omega
  have hselectedStack :
      IsQuittingCapNashRootStack reward selectedRoots profile := by
    simpa only [selectedRoots, profile] using hstack index
  have hsourceAtom : 0 <
      quittingStageCoalitionMass reward profile stage atom.terminal := by
    simpa only [profile, stage] using hdata.1.2.2.1
  have hshiftedAtom : 0 < quittingStageCoalitionMass reward
      (quittingLiteralRootStackProfile reward selectedRoots profile)
      (index + 1 + stage) atom.terminal := by
    simpa only [selectedRoots, profile, stage] using hdata.1.2.2.2
  have hprofileMem : quittingTerminalSemanticPair reward profile ∈
      quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward profile
  have hunique : ∀ candidate : iota → PMF Bool,
      IsεQuittingRootNash reward
          (quittingTerminalSemanticPair reward profile).2 0 candidate →
        candidate = (quittingAllContinueRoot : iota → PMF Bool) := by
    exact hfreeze (quittingTerminalSemanticPair reward profile) hprofileMem
      (by simpa only [profile] using hdata.2.le)
  have hstackData :=
    capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap
      reward profile selectedRoots hunique hselectedStack
  have hcharge :=
    capNashStackAbsorptionSum_eq_zero_of_unique_terminalCap
      reward profile selectedRoots hunique hselectedStack
  have hlaw :=
    capNashRootStack_terminalOutcomeMass_eq_of_unique_terminalCap
      reward profile selectedRoots hunique hselectedStack
  exact ⟨{
    chronologyIndex := index
    profile := profile
    stage := stage
    roots := selectedRoots
    roots_length := hselectedLength
    requestedDepth_lt_roots_length := hdepth
    rootStack := hselectedStack
    pointAtom_pos := atom.terminalMass_pos
    sourceAtom_pos := hsourceAtom
    shiftedSourceAtom_pos := hshiftedAtom
    cap_uniqueAllContinue := hunique
    roots_eq_replicate_allContinue := hstackData.1
    absorptionSum_eq_zero := hcharge
    semanticPair_eq := hstackData.2
    terminalOutcomeMass_eq := hlaw }⟩

/-- Punishment-normality and failure of uniform-payoff existence select one
finite atom at every supplied minimum joint-law point.  The checked positive
infimum equivalence then makes that same atom admit arbitrarily deep literal
inert source stacks.

The conclusion is an inert-stack boundary, not a uniform-payoff or
contradiction theorem. -/
theorem exists_minimumLawCausalSuffixInertCapStack_of_punishmentNormal_of_not_uniform
    [Nonempty iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (hno : ¬∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (point : QuittingTerminalSemanticLawPoint iota)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ atom : QuittingMinimumLawCausalSuffixAtom reward point,
      ∀ requestedDepth,
        Nonempty
          (QuittingMinimumLawCausalSuffixInertCapStack
            reward point atom requestedDepth) := by
  obtain ⟨atom⟩ :=
    nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff
      reward hno hnormal point hpoint hminimum
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr
      hno
  have hcarrier := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hminimumValue : quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalDebtSumInf reward :=
    (quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      point.1 hcarrier hminimum).symm
  have hminimumPositive : 0 <
      quittingTerminalSemanticDebtSum point.1 := by
    rw [hminimumValue]
    exact hinf
  exact ⟨atom, fun requestedDepth ↦ atom.nonempty_inertCapStack
    reward point requestedDepth hminimum hminimumPositive⟩

/-! ## Pure-Never marginal limit of the inert chronology -/

omit [DecidableEq iota] in
private theorem quittingProfileLiveRoot_literal_replicate_allContinue_of_lt
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (depth time : ℕ) (htime : time < depth) :
    quittingProfileLiveRoot reward
        (quittingLiteralRootStackProfile reward
          (List.replicate depth
            (quittingAllContinueRoot : iota → PMF Bool)) terminal)
        time = (quittingAllContinueRoot : iota → PMF Bool) := by
  induction depth generalizing time with
  | zero => omega
  | succ depth ih =>
      rw [List.replicate_succ, quittingLiteralRootStackProfile_cons]
      cases time with
      | zero => exact quittingProfileLiveRoot_rootThenContinuation_zero _ _ _
      | succ time =>
          rw [quittingProfileLiveRoot_rootThenContinuation_succ]
          exact ih time (by omega)

omit [DecidableEq iota] in
private theorem quittingCompactStoppingLaw_finiteMass_literal_allContinue_eq_zero
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (depth time : ℕ) (htime : time < depth) (player : iota) :
    (quittingCompactStoppingLawsOfProfile reward
        (quittingLiteralRootStackProfile reward
          (List.replicate depth
            (quittingAllContinueRoot : iota → PMF Bool)) terminal)
        player).realMass
          {(time : _root_.Math.Probability.CompactStoppingTime)} = 0 := by
  rw [← _root_.Math.Probability.CompactStoppingLaw.toPMF_apply_toReal]
  simp only [quittingCompactStoppingLawsOfProfile,
    _root_.Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
  have hroot :=
    quittingProfileLiveRoot_literal_replicate_allContinue_of_lt
      reward terminal depth time htime
  have hrootPlayer := congrFun hroot player
  have hhazard : quittingBehaviorLiveHazard reward
      ((quittingLiteralRootStackProfile reward
        (List.replicate depth
          (quittingAllContinueRoot : iota → PMF Bool)) terminal) player)
      time = PMF.pure false := by
    simpa only [quittingProfileLiveRoot, quittingBehaviorLiveHazard,
      quittingAllContinueRoot] using hrootPlayer
  have hsource : ((quittingBehaviorStoppingLaw reward
      ((quittingLiteralRootStackProfile reward
        (List.replicate depth
          (quittingAllContinueRoot : iota → PMF Bool)) terminal) player)
      (some time)).toReal = 0) := by
    rw [quittingBehaviorStoppingLaw_some_toReal,
      quittingHazardStopMass_eq_survival_mul_stop, hhazard]
    simp
  exact hsource

private theorem compactStoppingLaw_eq_pureNever_of_finiteMass_eventually_zero
    {lawSeq : ℕ → _root_.Math.Probability.CompactStoppingLaw}
    {law : _root_.Math.Probability.CompactStoppingLaw}
    (hlaw : Tendsto lawSeq atTop (nhds law))
    (hzero : ∀ time : ℕ, ∀ᶠ n in atTop,
      (lawSeq n).realMass
        {(time : _root_.Math.Probability.CompactStoppingTime)} = 0) :
    law = _root_.Math.Probability.CompactStoppingLaw.ofPMF
      (PMF.pure (⊤ : _root_.Math.Probability.CompactStoppingTime)) := by
  have hfinite (time : ℕ) : law.realMass
      {(time : _root_.Math.Probability.CompactStoppingTime)} = 0 := by
    have hlimit :=
      _root_.Math.Probability.CompactStoppingLaw.tendsto_realMass_of_isClopen
        hlaw
        (_root_.Math.Probability.compactStoppingTime_finiteSingleton_isClopen time)
    have hzeroLimit : Tendsto (fun n ↦
        (lawSeq n).realMass
          {(time : _root_.Math.Probability.CompactStoppingTime)})
        atTop (nhds 0) :=
      tendsto_const_nhds.congr'
        ((hzero time).mono fun _ hn ↦ hn.symm)
    exact tendsto_nhds_unique hlimit hzeroLimit
  have hfinitePMF (time : ℕ) :
      (law.toPMF
        (time : _root_.Math.Probability.CompactStoppingTime)).toReal = 0 := by
    rw [_root_.Math.Probability.CompactStoppingLaw.toPMF_apply_toReal]
    exact hfinite time
  have hsupportSubset : law.toPMF.support ⊆
      {(⊤ : _root_.Math.Probability.CompactStoppingTime)} := by
    intro choice hchoice
    induction choice using WithTop.recTopCoe with
    | top => simp
    | coe time =>
        exfalso
        have hne : law.toPMF
            (time : _root_.Math.Probability.CompactStoppingTime) ≠ 0 :=
          (PMF.mem_support_iff _ _).mp hchoice
        have hzero : law.toPMF
            (time : _root_.Math.Probability.CompactStoppingTime) = 0 :=
          (ENNReal.toReal_eq_zero_iff _).mp (hfinitePMF time)
            |>.resolve_right (PMF.apply_ne_top _ _)
        exact hne hzero
  have hsupport : law.toPMF.support =
      {(⊤ : _root_.Math.Probability.CompactStoppingTime)} := by
    apply Set.Subset.antisymm hsupportSubset
    obtain ⟨choice, hchoice⟩ := law.toPMF.support_nonempty
    have hchoiceTop : choice =
        (⊤ : _root_.Math.Probability.CompactStoppingTime) := by
      simpa using hsupportSubset hchoice
    subst choice
    simpa using hchoice
  have htop : law.toPMF
      (⊤ : _root_.Math.Probability.CompactStoppingTime) = 1 :=
    (law.toPMF.apply_eq_one_iff _).mpr hsupport
  have hpmf : law.toPMF =
      PMF.pure (⊤ : _root_.Math.Probability.CompactStoppingTime) := by
    apply _root_.Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
    intro choice
    induction choice using WithTop.recTopCoe with
    | top => simp [htop]
    | coe time => simpa using hfinitePMF time
  rw [← _root_.Math.Probability.CompactStoppingLaw.ofPMF_toPMF law]
  exact congrArg _root_.Math.Probability.CompactStoppingLaw.ofPMF hpmf

private theorem compactStoppingLawTailMass_pureNever (horizon : ℕ) :
    compactStoppingLawTailMass
      (_root_.Math.Probability.CompactStoppingLaw.ofPMF
        (PMF.pure
          (⊤ : _root_.Math.Probability.CompactStoppingTime))) horizon = 1 := by
  unfold compactStoppingLawTailMass
  rw [_root_.Math.Probability.CompactStoppingLaw.realMass_eq_pmfMass_toReal _
    (_root_.Math.Probability.compactStoppingTime_tail_isClopen horizon).1.measurableSet]
  rw [_root_.Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
  unfold _root_.Math.ProbabilityMassFunction.pmfMass
  rw [tsum_eq_single
    (⊤ : _root_.Math.Probability.CompactStoppingTime)]
  · simp [_root_.Math.ProbabilityMassFunction.pmfMask]
  · intro choice hchoice
    unfold _root_.Math.ProbabilityMassFunction.pmfMask
    split_ifs
    · rw [PMF.pure_apply_of_ne _ _ hchoice]
    · rfl

/-- One source-matched inert chronology above a fixed limiting joint point.

The terminal label and limiting point are fixed.  At every selected depth,
the literal all-Continue prefix preserves that depth's suffix semantic pair
and full terminal law exactly, and the same finite terminal label has positive
mass in both source and shifted stages.  The depth-dependent coordinates are
only asserted to converge jointly to `point`; no cross-depth equality of
semantic pairs or full terminal laws is claimed.

After one strict subsequence, every coordinate compact stopping-law limit is
literally the Dirac law at Never.  These marginal weak limits do not recover
the positive joint finite terminal atom retained by the relative timing of
the actual profiles. -/
structure QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point) where
  chronologyIndex : ℕ → ℕ
  chronologyIndex_strictMono : StrictMono chronologyIndex
  suffixProfile : ℕ → (quittingGame reward).BehaviorProfile
  cutoff : ℕ → ℕ
  stage : ℕ → ℕ
  roots : ℕ → List (iota → PMF Bool)
  roots_length : ∀ n, (roots n).length = chronologyIndex n + 1
  requestedDepth_lt_roots_length : ∀ n, n < (roots n).length
  rootStack : ∀ n,
    IsQuittingCapNashRootStack reward (roots n) (suffixProfile n)
  cap_uniqueAllContinue : ∀ n, ∀ candidate : iota → PMF Bool,
    IsεQuittingRootNash reward
        (quittingTerminalSemanticPair reward (suffixProfile n)).2 0 candidate →
      candidate = (quittingAllContinueRoot : iota → PMF Bool)
  roots_eq_replicate_allContinue : ∀ n,
    roots n = List.replicate (roots n).length
      (quittingAllContinueRoot : iota → PMF Bool)
  absorptionSum_eq_zero : ∀ n,
    quittingCapNashStackAbsorptionSum (roots n) = 0
  pointAtom_pos : 0 < point.2 (some atom.terminal)
  sourceAtom_cumulative_pos : ∀ n,
    point.2 (some atom.terminal) / 2 <
      ∑ time ∈ Finset.range (cutoff n),
        quittingStageCoalitionMass reward
          (suffixProfile n) time atom.terminal
  stage_lt_cutoff : ∀ n, stage n < cutoff n
  sourceAtom_pos : ∀ n, 0 < quittingStageCoalitionMass reward
    (suffixProfile n) (stage n) atom.terminal
  shiftedSourceAtom_pos : ∀ n, 0 < quittingStageCoalitionMass reward
    (quittingLiteralRootStackProfile reward (roots n) (suffixProfile n))
    ((roots n).length + stage n) atom.terminal
  semanticPair_eq : ∀ n,
    quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward (roots n) (suffixProfile n)) =
      quittingTerminalSemanticPair reward (suffixProfile n)
  terminalOutcomeMass_eq : ∀ n,
    quittingTerminalOutcomeMass reward
        (quittingLiteralRootStackProfile reward (roots n) (suffixProfile n)) =
      quittingTerminalOutcomeMass reward (suffixProfile n)
  suffix_joint_tendsto : Tendsto (fun n ↦
    (quittingTerminalSemanticPair reward (suffixProfile n),
      quittingTerminalOutcomeMass reward (suffixProfile n)))
    atTop (nhds point)
  prefixed_joint_tendsto : Tendsto (fun n ↦
    (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward (roots n) (suffixProfile n)),
      quittingTerminalOutcomeMass reward
        (quittingLiteralRootStackProfile reward (roots n) (suffixProfile n))))
    atTop (nhds point)
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  marginalLimit : iota → _root_.Math.Probability.CompactStoppingLaw
  marginal_tendsto : ∀ player, Tendsto (fun n ↦
    quittingCompactStoppingLawsOfProfile reward
      (quittingLiteralRootStackProfile reward
        (roots (subseq n)) (suffixProfile (subseq n))) player)
    atTop (nhds (marginalLimit player))
  marginalLimit_eq_pureNever : ∀ player,
    marginalLimit player =
      _root_.Math.Probability.CompactStoppingLaw.ofPMF
        (PMF.pure (⊤ : _root_.Math.Probability.CompactStoppingTime))

/-- Near-minimum cap freezing turns the source chronology of one fixed atom
into the pure-Never marginal-limit normal form.  The target joint point is
retained as a limit, not upgraded to an exact value at each selected depth. -/
theorem QuittingMinimumLawCausalSuffixAtom.nonempty_pureNeverMarginalLimit
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum point.1) :
    Nonempty
      (QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
        reward point atom) := by
  obtain ⟨epsilon, hepsilon, hfreeze⟩ :=
    exists_pos_nearMinimum_capNash_eq_allContinue_radius
      (reward := reward) (quittingTerminalSemanticDebtSum point.1)
        hminimumPositive hminimum
  obtain ⟨profiles, cutoff, mark, roots, hprofiles, hlength,
      hstack, _hdebt, hatomEventually⟩ := atom.chronology
  have hpairTendsto : Tendsto
      (fun n ↦ quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds point.1) :=
    continuous_fst.continuousAt.tendsto.comp hprofiles
  have hdebtTendsto : Tendsto
      (fun n ↦ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profiles n)))
      atTop (nhds (quittingTerminalSemanticDebtSum point.1)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      hpairTendsto
  have hnearEventually : ∀ᶠ n in atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles n)) <
        quittingTerminalSemanticDebtSum point.1 + epsilon :=
    (tendsto_order.1 hdebtTendsto).2
      (quittingTerminalSemanticDebtSum point.1 + epsilon) (by linarith)
  have hdataEventually := hatomEventually.and hnearEventually
  rw [eventually_atTop] at hdataEventually
  obtain ⟨first, hfirst⟩ := hdataEventually
  let index : ℕ → ℕ := fun n ↦ n + first
  let suffix : ℕ → (quittingGame reward).BehaviorProfile :=
    fun n ↦ profiles (index n)
  let selectedCutoff : ℕ → ℕ := fun n ↦ cutoff (index n)
  let selectedStage : ℕ → ℕ := fun n ↦ mark (index n)
  let selectedRoots : ℕ → List (iota → PMF Bool) :=
    fun n ↦ roots (index n)
  let prefixed : ℕ → (quittingGame reward).BehaviorProfile :=
    fun n ↦ quittingLiteralRootStackProfile reward
      (selectedRoots n) (suffix n)
  have hindexStrict : StrictMono index := by
    intro a b hab
    dsimp only [index]
    omega
  have hindexTendsto : Tendsto index atTop atTop :=
    hindexStrict.tendsto_atTop
  have hdata (n : ℕ) := hfirst (index n) (by
    dsimp only [index]
    omega)
  have hselectedLength (n : ℕ) :
      (selectedRoots n).length = index n + 1 := by
    simpa only [selectedRoots] using hlength (index n)
  have hdepth (n : ℕ) : n < (selectedRoots n).length := by
    rw [hselectedLength]
    dsimp only [index]
    omega
  have hselectedStack (n : ℕ) :
      IsQuittingCapNashRootStack reward (selectedRoots n) (suffix n) := by
    simpa only [selectedRoots, suffix] using hstack (index n)
  have hunique (n : ℕ) : ∀ candidate : iota → PMF Bool,
      IsεQuittingRootNash reward
          (quittingTerminalSemanticPair reward (suffix n)).2 0 candidate →
        candidate = (quittingAllContinueRoot : iota → PMF Bool) := by
    intro candidate hcandidate
    have hprofileMem : quittingTerminalSemanticPair reward (suffix n) ∈
        quittingTerminalSemanticCarrier reward :=
      quittingTerminalSemanticPair_mem_carrier reward (suffix n)
    exact hfreeze (quittingTerminalSemanticPair reward (suffix n))
      hprofileMem (by simpa only [suffix] using (hdata n).2.le)
      candidate hcandidate
  have hstackData (n : ℕ) :=
    capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap
      reward (suffix n) (selectedRoots n) (hunique n) (hselectedStack n)
  have hcharge (n : ℕ) :=
    capNashStackAbsorptionSum_eq_zero_of_unique_terminalCap
      reward (suffix n) (selectedRoots n) (hunique n) (hselectedStack n)
  have hlaw (n : ℕ) :=
    capNashRootStack_terminalOutcomeMass_eq_of_unique_terminalCap
      reward (suffix n) (selectedRoots n) (hunique n) (hselectedStack n)
  have hsuffixJoint : Tendsto (fun n ↦
      (quittingTerminalSemanticPair reward (suffix n),
        quittingTerminalOutcomeMass reward (suffix n)))
      atTop (nhds point) := by
    simpa [suffix, Function.comp_def] using
      hprofiles.comp hindexTendsto
  have hprefixedJoint : Tendsto (fun n ↦
      (quittingTerminalSemanticPair reward (prefixed n),
        quittingTerminalOutcomeMass reward (prefixed n)))
      atTop (nhds point) := by
    apply hsuffixJoint.congr'
    filter_upwards [] with n
    dsimp only [prefixed]
    rw [(hstackData n).2, hlaw n]
  obtain ⟨laws, subseq, hsubseq, hlaws⟩ :=
    exists_quittingCompactStoppingLawsOfProfile_tendsto_subseq
      reward prefixed
  have hlawsPureNever (player : iota) : laws player =
      _root_.Math.Probability.CompactStoppingLaw.ofPMF
        (PMF.pure
          (⊤ : _root_.Math.Probability.CompactStoppingTime)) := by
    apply compactStoppingLaw_eq_pureNever_of_finiteMass_eventually_zero
      (hlaws player)
    intro time
    filter_upwards [eventually_ge_atTop time] with n hn
    have hnSubseq : n ≤ subseq n := hsubseq.id_le n
    have htime : time < (selectedRoots (subseq n)).length :=
      lt_of_le_of_lt (hn.trans hnSubseq) (hdepth (subseq n))
    dsimp only [prefixed]
    rw [(hstackData (subseq n)).1]
    exact quittingCompactStoppingLaw_finiteMass_literal_allContinue_eq_zero
      reward (suffix (subseq n)) (selectedRoots (subseq n)).length
        time htime player
  exact ⟨{
    chronologyIndex := index
    chronologyIndex_strictMono := hindexStrict
    suffixProfile := suffix
    cutoff := selectedCutoff
    stage := selectedStage
    roots := selectedRoots
    roots_length := hselectedLength
    requestedDepth_lt_roots_length := hdepth
    rootStack := hselectedStack
    cap_uniqueAllContinue := hunique
    roots_eq_replicate_allContinue := fun n ↦ (hstackData n).1
    absorptionSum_eq_zero := hcharge
    pointAtom_pos := atom.terminalMass_pos
    sourceAtom_cumulative_pos := fun n ↦ by
      simpa only [suffix, selectedCutoff] using (hdata n).1.1
    stage_lt_cutoff := fun n ↦ by
      simpa only [selectedStage, selectedCutoff] using (hdata n).1.2.1
    sourceAtom_pos := fun n ↦ by
      simpa only [suffix, selectedStage] using (hdata n).1.2.2.1
    shiftedSourceAtom_pos := fun n ↦ by
      simpa only [suffix, selectedStage, selectedRoots,
        hlength (index n)] using (hdata n).1.2.2.2
    semanticPair_eq := fun n ↦ (hstackData n).2
    terminalOutcomeMass_eq := hlaw
    suffix_joint_tendsto := hsuffixJoint
    prefixed_joint_tendsto := by simpa only [prefixed] using hprefixedJoint
    subseq := subseq
    subseq_strictMono := hsubseq
    marginalLimit := laws
    marginal_tendsto := by simpa only [prefixed] using hlaws
    marginalLimit_eq_pureNever := hlawsPureNever }⟩

/-- The selected actual marginal-law sequence of the pure-Never normal form. -/
def QuittingMinimumLawCausalSuffixPureNeverMarginalLimit.selectedMarginalLawSequence
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom) :
    ℕ → iota → _root_.Math.Probability.CompactStoppingLaw :=
  fun n player ↦ quittingCompactStoppingLawsOfProfile reward
    (quittingLiteralRootStackProfile reward
      (packet.roots (packet.subseq n))
      (packet.suffixProfile (packet.subseq n))) player

namespace QuittingMinimumLawCausalSuffixPureNeverMarginalLimit

/-- Vanishing-error Nash roots against the selected literal suffix caps have
vanishing one-stage absorption.  The cap sequence is the one retained by the
causal packet and converges to the displayed minimum cap; no cap is
recomputed from marginal limits.

This rules out macroscopic approximate-prefix escape at the same source caps.
It does not rule out vanishing-absorption tangent or paid structure. -/
theorem approximateRoot_absorption_tendsto_zero
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum point.1)
    (error : ℕ → ℝ) (root : ℕ → QuittingRootSimplex iota)
    (herror : Tendsto error atTop (nhds 0))
    (hnash : ∀ n, IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward (packet.suffixProfile n)).2
      (error n) (quittingRootOfSimplex (root n))) :
    Tendsto (fun n ↦ quittingSimplexAbsorptionMass (root n))
      atTop (nhds 0) := by
  have hpairTendsto : Tendsto (fun n ↦
      quittingTerminalSemanticPair reward (packet.suffixProfile n))
      atTop (nhds point.1) :=
    continuous_fst.continuousAt.tendsto.comp packet.suffix_joint_tendsto
  have hpointMem : point.1 ∈ quittingTerminalSemanticCarrier reward :=
    (quittingTerminalSemanticCarrier_isCompact reward).isClosed.mem_of_tendsto
      hpairTendsto (Filter.Eventually.of_forall fun n ↦
        quittingTerminalSemanticPair_mem_carrier reward
          (packet.suffixProfile n))
  obtain ⟨radius, hradius, hfreeze⟩ :=
    exists_pos_nearMinimum_capNash_eq_allContinue_radius
      (reward := reward) (quittingTerminalSemanticDebtSum point.1)
        hminimumPositive hminimum
  have hpointUnique : ∀ candidate : iota → PMF Bool,
      IsεQuittingRootNash reward point.1.2 0 candidate →
        candidate = (quittingAllContinueRoot : iota → PMF Bool) := by
    exact hfreeze point.1 hpointMem (by linarith)
  have hcapTendsto : Tendsto (fun n ↦
      (quittingTerminalSemanticPair reward (packet.suffixProfile n)).2)
      atTop (nhds point.1.2) :=
    continuous_snd.continuousAt.tendsto.comp hpairTendsto
  have hscaledError : Tendsto
      (fun n ↦ (Fintype.card iota : ℝ) * error n)
      atTop (nhds 0) := by
    simpa using herror.const_mul (Fintype.card iota : ℝ)
  apply tendsto_order.2
  constructor
  · intro lower hlower
    filter_upwards [] with n
    have hnonneg : 0 ≤ quittingSimplexAbsorptionMass (root n) := by
      rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass]
      exact quittingRootAbsorptionMass_nonneg _
    exact hlower.trans_le hnonneg
  · intro eta heta
    obtain ⟨moat, hmoat, hnear⟩ :=
      exists_eventually_absorptionNashDefect_moat_of_unique_allContinue
        reward point.1.2 eta heta hpointUnique
    have hcapNear := hcapTendsto.eventually hnear
    have herrorSmall : ∀ᶠ n in atTop,
        (Fintype.card iota : ℝ) * error n < moat :=
      (tendsto_order.1 hscaledError).2 moat hmoat
    filter_upwards [hcapNear, herrorSmall] with n hnearCap hsmall
    apply lt_of_not_ge
    intro habsorption
    have hdefectLower := hnearCap (root n) habsorption
    have hdefectUpper :=
      quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
        reward
          (quittingTerminalSemanticPair reward (packet.suffixProfile n)).2
          (quittingRootOfSimplex (root n)) (error n) (hnash n)
    linarith

/-- At every fixed horizon, the joint late-or-Never product along the
selected actual subsequence tends to one.  The horizon is fixed before the
limit; no uniform-in-horizon convergence is asserted. -/
theorem jointTailProduct_tendsto_one
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom) (horizon : ℕ) :
    Tendsto (fun n ↦ quittingJointTailProduct
      (packet.selectedMarginalLawSequence n) horizon) atTop (nhds 1) := by
  have hlimit := quittingJointTailProduct_tendsto
    packet.marginal_tendsto horizon
  have hproduct : quittingJointTailProduct packet.marginalLimit horizon = 1 := by
    unfold quittingJointTailProduct
    apply Finset.prod_eq_one
    intro player _
    rw [packet.marginalLimit_eq_pureNever player]
    exact compactStoppingLawTailMass_pureNever horizon
  rw [hproduct] at hlimit
  change Tendsto (fun n ↦ quittingJointTailProduct
    (quittingCompactStoppingLawsOfProfile reward
      (quittingLiteralRootStackProfile reward
        (packet.roots (packet.subseq n))
        (packet.suffixProfile (packet.subseq n)))) horizon)
    atTop (nhds 1)
  exact hlimit

/-- For every owner and fixed horizon, the product of that owner's opponent
late-or-Never masses along the selected actual subsequence tends to one. -/
theorem opponentTailProduct_tendsto_one
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom) (owner : iota) (horizon : ℕ) :
    Tendsto (fun n ↦ quittingOpponentTailProduct
      (packet.selectedMarginalLawSequence n) owner horizon)
      atTop (nhds 1) := by
  have hlimit := quittingOpponentTailProduct_tendsto
    packet.marginal_tendsto owner horizon
  have hproduct : quittingOpponentTailProduct
      packet.marginalLimit owner horizon = 1 := by
    unfold quittingOpponentTailProduct
    apply Finset.prod_eq_one
    intro player _
    rw [packet.marginalLimit_eq_pureNever player]
    exact compactStoppingLawTailMass_pureNever horizon
  rw [hproduct] at hlimit
  change Tendsto (fun n ↦ quittingOpponentTailProduct
    (quittingCompactStoppingLawsOfProfile reward
      (quittingLiteralRootStackProfile reward
        (packet.roots (packet.subseq n))
        (packet.suffixProfile (packet.subseq n)))) owner horizon)
    atTop (nhds 1)
  exact hlimit

/-- The selected marginal sequence is not jointly tight.  This is a
fixed-horizon consequence of convergence to one, not a uniform-in-horizon
limit statement or a uniform-equilibrium contradiction. -/
theorem not_jointTight
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom) :
    ¬ QuittingJointTightLawSequence packet.selectedMarginalLawSequence := by
  intro htight
  obtain ⟨horizon, hsmall⟩ := htight (1 / 2) (by norm_num)
  have hlarge : ∀ᶠ n in atTop, 1 / 2 < quittingJointTailProduct
      (packet.selectedMarginalLawSequence n) horizon :=
    (tendsto_order.1 (packet.jointTailProduct_tendsto_one horizon)).1
      (1 / 2) (by norm_num)
  obtain ⟨n, hnSmall, hnLarge⟩ := (hsmall.and hlarge).exists
  linarith

/-- For each displayed owner, its opponent-tail sequence is not tight. -/
theorem not_opponentTightAt
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom) (owner : iota) :
    ¬ QuittingOpponentTightAtLawSequence
      packet.selectedMarginalLawSequence owner := by
  intro htight
  obtain ⟨horizon, hsmall⟩ := htight (1 / 2) (by norm_num)
  have hlarge : ∀ᶠ n in atTop, 1 / 2 < quittingOpponentTailProduct
      (packet.selectedMarginalLawSequence n) owner horizon :=
    (tendsto_order.1
      (packet.opponentTailProduct_tendsto_one owner horizon)).1
        (1 / 2) (by norm_num)
  obtain ⟨n, hnSmall, hnLarge⟩ := (hsmall.and hlarge).exists
  linarith

/-- With a displayed player available, the selected marginal sequence fails
the uniform opponent-tightness condition. -/
theorem not_opponentTight
    [Nonempty iota]
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom) :
    ¬ QuittingOpponentTightLawSequence
      packet.selectedMarginalLawSequence := by
  intro htight
  let owner : iota := Classical.choice inferInstance
  exact packet.not_opponentTightAt owner (htight owner)

end QuittingMinimumLawCausalSuffixPureNeverMarginalLimit

/-- Punishment-normality and failure of uniform-payoff existence select the
fixed finite atom needed for the pure-Never marginal-limit normal form at
every supplied minimizing joint-law point. -/
theorem exists_minimumLawCausalSuffixPureNeverMarginalLimit_of_punishmentNormal_of_not_uniform
    [Nonempty iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (hno : ¬∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (point : QuittingTerminalSemanticLawPoint iota)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ atom : QuittingMinimumLawCausalSuffixAtom reward point,
      Nonempty
        (QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
          reward point atom) := by
  obtain ⟨atom⟩ :=
    nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff
      reward hno hnormal point hpoint hminimum
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr
      hno
  have hcarrier := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hminimumValue : quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalDebtSumInf reward :=
    (quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      point.1 hcarrier hminimum).symm
  have hminimumPositive : 0 <
      quittingTerminalSemanticDebtSum point.1 := by
    rw [hminimumValue]
    exact hinf
  exact ⟨atom, atom.nonempty_pureNeverMarginalLimit
    reward point hminimum hminimumPositive⟩

end GameTheory
