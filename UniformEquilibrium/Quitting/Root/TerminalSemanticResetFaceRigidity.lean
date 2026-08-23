/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

/-!
# Rigidity at a positive reset-face minimum

If a positive-debt semantic pair minimizes total debt among carrier points on
one zero-debt face, prefixing it by an exact Nash root against its envelope
cannot decrease total debt.  Exact prefix scaling then forces joint Continue
mass one, hence the root is all-Continue.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A positive total-debt minimum on one reset face has only the all-Continue
exact Nash root against its envelope.  The statement uses no terminal-law or
chronological data. -/
theorem fixedLawResetPoint_unique_allContinue_of_globalResetFaceMinimum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (returned : QuittingTerminalSemanticPair ι) (owner : ι)
    (hreturned : returned ∈ quittingTerminalSemanticCarrier reward)
    (hpositive : 0 < quittingTerminalSemanticDebtSum returned)
    (hreset : quittingTerminalSemanticDebt returned owner = 0)
    (hfaceMinimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebt candidate owner = 0 →
        quittingTerminalSemanticDebtSum returned ≤
          quittingTerminalSemanticDebtSum candidate) :
    ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward returned.2 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool) := by
  intro root hnash
  let prefixed := quittingTerminalSemanticPrefix reward root returned
  have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier reward root returned hreturned
  have hcoordinate : ∀ who,
      quittingTerminalSemanticDebt prefixed who =
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt returned who := by
    intro who
    have hquit : quittingRootQuitPayoff reward returned.1 root who =
        quittingRootQuitPayoff reward returned.2 root who :=
      quittingRootQuitPayoff_continuation_invariant
        reward returned.1 returned.2 root who
    have hcontinue :
        quittingRootContinuePayoff reward
            (Function.update returned.1 who (returned.2 who)) root who =
          quittingRootContinuePayoff reward returned.2 root who := by
      apply quittingRootExpectedPayoff_continuation_congr
      simp
    unfold prefixed quittingTerminalSemanticDebt
      quittingTerminalSemanticPrefix
    dsimp only
    rw [hquit, hcontinue,
      ← quittingRootSuccessorPayoff_eq_max_of_isZeroNash
        reward returned.2 root who hnash]
    unfold quittingRootSuccessorPayoff
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
      quittingRootExpectedPayoff_eq_absorbingContribution_add]
    ring
  have hprefixedReset : quittingTerminalSemanticDebt prefixed owner = 0 := by
    rw [hcoordinate owner, hreset, mul_zero]
  have hface := hfaceMinimum prefixed hprefixed hprefixedReset
  have hscale : quittingTerminalSemanticDebtSum prefixed =
      quittingStationaryContinueMass root *
        quittingTerminalSemanticDebtSum returned := by
    unfold quittingTerminalSemanticDebtSum
    simp_rw [hcoordinate]
    rw [Finset.mul_sum]
  have hcontinueLe := quittingStationaryContinueMass_le_one root
  have hcontinue : quittingStationaryContinueMass root = 1 := by
    rw [hscale] at hface
    nlinarith
  funext player
  have hpure := eq_pure_false_of_quittingStationaryContinueMass_eq_one
    hcontinue player
  simpa only [quittingAllContinueRoot] using hpure

end GameTheory
