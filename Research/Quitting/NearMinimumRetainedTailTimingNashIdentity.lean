/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingGame
import UniformEquilibrium.Diagnostics.Quitting.RetainedTailFiniteTimingNash
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourStrictMinimumPlateauIsolation
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanClockReduction
import UniformEquilibrium.Quitting.Root.LiteralExactPrefixStack

/-!
# Near-minimum exact-root and retained-tail stack rigidity

An actual terminal tail whose prescribed payoff uniformly dominates every
singleton reward cannot admit a nontrivial exact Nash prefix sufficiently
close to the positive global minimum of total behavioral debt.

The quantitative argument is stronger than the cardinality-averaged version:
if one player participates, its opponents absorb with probability at least
`kappa / (kappa + 2 * M)`.  Every other participant has the same bound, while
forcing a nonparticipant to Continue changes nothing.  Thus every coordinate
has the same opponent-absorption floor, without a loss by the number of
players.

The final theorem propagates this one-stage result backward through an
`IsQuittingLiteralExactRootStack`.  This is the exact credible-suffix contract
needed by a retained-tail finite timing law.  This module does not prove that
an arbitrary mixed Nash law of a retained-tail timing game supplies that
contract; in particular it makes no claim about approximate, behavioral, or
zero-return timing equilibria, and contains no Fin4 source adapter.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The missing retained-tail normal-form source seam -/

/-- Pure root word represented by one finite timing-action profile.  A player
Quits at exactly its selected finite date and Continues at every displayed
date when it selects `Never`. -/
def quittingRetainedTailPureTimingRootStack
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline) :
    List (ι → PMF Bool) :=
  List.ofFn fun date who => PMF.pure (decide (choices who = some date))

/-- The finite normal-form timing game whose `Never` action resumes one fixed
actual behavioral tail.  This is distinct from
`quittingFiniteDeadlineTimingGame`, whose `Never` payoff is zero. -/
abbrev quittingRetainedTailFiniteTimingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (tail : (quittingGame reward).BehaviorProfile) : KernelGame ι :=
  KernelGame.ofPureEU (fun _ => QuittingFiniteDeadlineTimingAction deadline)
    (fun choices who => quittingTerminalPayoff reward
      (quittingRetainedTailFiniteTimingGraft reward
        (quittingRetainedTailPureTimingRootStack deadline choices) tail) who)

/-- The retained-tail timing game has the same finite outcome carrier as its
finite timing-action profile space. -/
instance quittingRetainedTailFiniteTimingGame_finiteOutcome
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (tail : (quittingGame reward).BehaviorProfile) :
    Finite (quittingRetainedTailFiniteTimingGame reward deadline tail).Outcome := by
  unfold quittingRetainedTailFiniteTimingGame KernelGame.ofPureEU
  infer_instance

/-- The finite hazard word carried by independent mixed timing laws.  The
missing source theorem must identify the retained-tail normal-form mixed
payoff with the graft of this word, and then turn positive joint `Never` mass
into an exact credible suffix stack. -/
def quittingRetainedTailMixedTimingRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    List (ι → PMF Bool) :=
  List.ofFn fun date : Fin deadline => quittingProfileLiveRoot reward
    (quittingFiniteDeadlineTimingProfile reward deadline mixed) date.val

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingRetainedTailPureTimingRootStack_length
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline) :
    (quittingRetainedTailPureTimingRootStack deadline choices).length =
      deadline := by
  simp [quittingRetainedTailPureTimingRootStack]

omit [DecidableEq ι] in
@[simp] theorem quittingRetainedTailMixedTimingRootStack_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    (quittingRetainedTailMixedTimingRootStack reward deadline mixed).length =
      deadline := by
  simp [quittingRetainedTailMixedTimingRootStack]

/-- Positive Quit support and exact endpoint Nash force a quantitative amount
of opponent absorption when the prescribed continuation dominates the
player's singleton reward. -/
theorem quittingRootOpponentAbsorptionMass_ge_gapRatio_of_quit_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {M kappa : ℝ} (hkappa : 0 < kappa)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsingleton : reward (quittingSingletonTerminal who) who + kappa ≤
      tail who)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hquit : 0 < (root who true).toReal) :
    kappa / (kappa + 2 * M) ≤
      quittingRootOpponentAbsorptionMass root who := by
  apply gap_div_le_quittingRootOpponentAbsorptionMass_of_isZeroNash_of_quit_pos
    reward tail root who hkappa hreward
  · linarith
  · exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).mp hnash
  · exact hquit

/-- A nonidentity exact root has the same quantitative opponent-absorption
floor at every coordinate.  A nonparticipant loses no mass when it is forced
to Continue, so no cardinality averaging is necessary. -/
theorem nonidentity_exactRoot_uniformOpponentAbsorption_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    {M kappa : ℝ} (hkappa : 0 < kappa)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsingleton : ∀ who,
      reward (quittingSingletonTerminal who) who + kappa ≤ tail who)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hnonidentity : root ≠ (quittingAllContinueRoot : ι → PMF Bool)) :
    ∀ who, kappa / (kappa + 2 * M) ≤
      quittingRootOpponentAbsorptionMass root who := by
  have hparticipant : ∃ participant, 0 < (root participant true).toReal := by
    by_contra hnone
    have hzero : ∀ player, (root player true).toReal = 0 := by
      intro player
      apply le_antisymm
      · exact le_of_not_gt fun hpositive => hnone ⟨player, hpositive⟩
      · exact ENNReal.toReal_nonneg
    apply hnonidentity
    funext player
    exact Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      _ (hzero player)
  obtain ⟨participant, hparticipant⟩ := hparticipant
  have hparticipantFloor :=
    quittingRootOpponentAbsorptionMass_ge_gapRatio_of_quit_pos
      reward tail root participant hkappa hreward
        (hsingleton participant) hnash hparticipant
  intro who
  by_cases hquit : 0 < (root who true).toReal
  · exact quittingRootOpponentAbsorptionMass_ge_gapRatio_of_quit_pos
      reward tail root who hkappa hreward (hsingleton who) hnash hquit
  · have hzero : (root who true).toReal = 0 := by
      exact le_antisymm (le_of_not_gt hquit) ENNReal.toReal_nonneg
    have hpure : root who = PMF.pure false :=
      Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
        _ hzero
    have hforced : Function.update root who (PMF.pure false) = root := by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp [hpure]
      · simp [Function.update_of_ne hplayer]
    calc
      kappa / (kappa + 2 * M) ≤
          quittingRootOpponentAbsorptionMass root participant :=
        hparticipantFloor
      _ ≤ quittingRootAbsorptionMass root :=
        quittingRootOpponentAbsorptionMass_le_absorptionMass root participant
      _ = quittingRootOpponentAbsorptionMass root who := by
        unfold quittingRootOpponentAbsorptionMass
        rw [hforced]

/-- Direct contraction form of near-minimum rigidity.  The tail and the
prefixed profile are both actual behavioral profiles, so the global literal
debt infimum applies to both without a realization hypothesis. -/
theorem nearMinimum_rootNashAgainstPayoff_eq_allContinue_of_contraction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (root : ι → PMF Bool) {M kappa excess : ℝ}
    (hM : 0 < M) (hkappa : 0 < kappa)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htail : quittingTerminalDebtSum reward tail ≤
      quittingTerminalDebtSumInf reward + excess)
    (hsingleton : ∀ who,
      reward (quittingSingletonTerminal who) who + kappa ≤
        quittingTerminalPayoff reward tail who)
    (hnash : IsεQuittingRootEndpointNash reward
      (fun who => quittingTerminalPayoff reward tail who) 0 root)
    (hcontraction :
      (1 - kappa / (kappa + 2 * M)) *
          (quittingTerminalDebtSumInf reward + excess) <
        quittingTerminalDebtSumInf reward) :
    root = quittingAllContinueRoot := by
  by_contra hnonidentity
  have habsorption :=
    nonidentity_exactRoot_uniformOpponentAbsorption_ge
      reward (fun who => quittingTerminalPayoff reward tail who) root
        hkappa hreward hsingleton hnash hnonidentity
  have hsurvival : ∀ who, quittingRootOpponentContinueMass root who ≤
      1 - kappa / (kappa + 2 * M) := by
    intro who
    rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass]
    linarith [habsorption who]
  have hnashRoot : IsεQuittingRootNash reward
      (fun who => quittingTerminalPayoff reward tail who) 0 root :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward (fun who => quittingTerminalPayoff reward tail who) 0 root).mp hnash
  let prefixed := quittingRootThenContinuationProfile reward root tail
  have hfactorNonneg : 0 ≤ 1 - kappa / (kappa + 2 * M) := by
    have hdenom : 0 < kappa + 2 * M := by positivity
    have hratioLe : kappa / (kappa + 2 * M) ≤ 1 := by
      exact (div_le_one hdenom).2 (by linarith)
    linarith
  have hsum : quittingTerminalDebtSum reward prefixed ≤
      (1 - kappa / (kappa + 2 * M)) *
        quittingTerminalDebtSum reward tail := by
    unfold quittingTerminalDebtSum
    calc
      ∑ who, quittingTerminalDeviationDebt reward prefixed who ≤
          ∑ who, (1 - kappa / (kappa + 2 * M)) *
            quittingTerminalDeviationDebt reward tail who := by
        apply Finset.sum_le_sum
        intro who _
        have hprefix :=
          quittingTerminalDeviationDebt_rootThenContinuation_le
            reward root tail who hnashRoot
        have hscaled :
            quittingRootOpponentContinueMass root who *
                quittingTerminalDeviationDebt reward tail who ≤
              (1 - kappa / (kappa + 2 * M)) *
                quittingTerminalDeviationDebt reward tail who :=
          mul_le_mul_of_nonneg_right (hsurvival who)
            (quittingTerminalDeviationDebt_nonneg reward tail who)
        exact hprefix.trans hscaled
      _ = (1 - kappa / (kappa + 2 * M)) *
          ∑ who, quittingTerminalDeviationDebt reward tail who := by
        rw [Finset.mul_sum]
  have hinf := quittingTerminalDebtSumInf_le (reward := reward) prefixed
  have htailScaled :
      (1 - kappa / (kappa + 2 * M)) *
          quittingTerminalDebtSum reward tail ≤
        (1 - kappa / (kappa + 2 * M)) *
          (quittingTerminalDebtSumInf reward + excess) :=
    mul_le_mul_of_nonneg_left htail hfactorNonneg
  exact (not_lt_of_ge (hinf.trans (hsum.trans htailScaled))) hcontraction

/-- Explicit near-minimum modulus.  The permitted excess is
`kappa * Dstar / (2 * M)`, strictly stronger than the cardinality-averaged
bound because every nonparticipant sees the full existing absorption. -/
theorem nearMinimum_rootNashAgainstPayoff_eq_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (root : ι → PMF Bool) {M kappa excess : ℝ}
    (hM : 0 < M) (hkappa : 0 < kappa)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : 0 < quittingTerminalDebtSumInf reward)
    (htail : quittingTerminalDebtSum reward tail ≤
      quittingTerminalDebtSumInf reward + excess)
    (hsingleton : ∀ who,
      reward (quittingSingletonTerminal who) who + kappa ≤
        quittingTerminalPayoff reward tail who)
    (hnash : IsεQuittingRootEndpointNash reward
      (fun who => quittingTerminalPayoff reward tail who) 0 root)
    (hnear : excess <
      kappa * quittingTerminalDebtSumInf reward / (2 * M)) :
    root = quittingAllContinueRoot := by
  have hminimumNonneg : 0 ≤ quittingTerminalDebtSumInf reward := hminimum.le
  apply nearMinimum_rootNashAgainstPayoff_eq_allContinue_of_contraction
    reward tail root hM hkappa hreward htail hsingleton hnash
  have htwoM : 0 < 2 * M := by positivity
  have hdenom : 0 < kappa + 2 * M := by positivity
  have hnearMul :
      excess * (2 * M) <
        kappa * quittingTerminalDebtSumInf reward :=
    (lt_div_iff₀ htwoM).mp hnear
  rw [show 1 - kappa / (kappa + 2 * M) =
      2 * M / (kappa + 2 * M) by
        field_simp
        ring]
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hdenom).2
  nlinarith [hminimumNonneg]

omit [DecidableEq ι] in
/-- A finite word of all-Continue roots preserves the prescribed payoff of
the literal terminal tail exactly. -/
theorem quittingTerminalPayoff_literalRootStack_replicate_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (depth : ℕ) (who : ι) :
    quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward
          (List.replicate depth quittingAllContinueRoot) tail) who =
      quittingTerminalPayoff reward tail who := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [List.replicate_succ, quittingLiteralRootStackProfile_cons,
        quittingTerminalPayoff_rootThenContinuation_eq]
      have hallContinue : quittingRootExpectedPayoff reward
          (fun player => quittingTerminalPayoff reward
            (quittingLiteralRootStackProfile reward
              (List.replicate depth quittingAllContinueRoot) tail) player)
          quittingAllContinueRoot who =
            quittingTerminalPayoff reward
              (quittingLiteralRootStackProfile reward
                (List.replicate depth quittingAllContinueRoot) tail) who := by
        classical
        unfold quittingRootExpectedPayoff quittingAllContinueRoot
        rw [Math.PMFProduct.pmfPi_pure]
        simp [quittingRootPayoff]
      rw [hallContinue]
      exact ih

/-- Backward rigidity for a supplied credible retained-tail root stack.  Each
stored root is exact Nash against the actual executable suffix, and the whole
word is therefore the literal all-Continue identity block. -/
theorem nearMinimum_literalExactRootStack_eq_replicate_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (roots : List (ι → PMF Bool)) {M kappa excess : ℝ}
    (hM : 0 < M) (hkappa : 0 < kappa)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : 0 < quittingTerminalDebtSumInf reward)
    (htail : quittingTerminalDebtSum reward tail ≤
      quittingTerminalDebtSumInf reward + excess)
    (hsingleton : ∀ who,
      reward (quittingSingletonTerminal who) who + kappa ≤
        quittingTerminalPayoff reward tail who)
    (hnear : excess <
      kappa * quittingTerminalDebtSumInf reward / (2 * M))
    (hstack : IsQuittingLiteralExactRootStack reward roots tail) :
    roots = List.replicate roots.length quittingAllContinueRoot := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
      rw [isQuittingLiteralExactRootStack_cons_iff] at hstack
      have hroots := ih hstack.2
      have hpayoff :
          (fun who => quittingTerminalPayoff reward
            (quittingLiteralRootStackProfile reward roots tail) who) =
            fun who => quittingTerminalPayoff reward tail who := by
        funext who
        rw [hroots]
        exact quittingTerminalPayoff_literalRootStack_replicate_allContinue
          reward tail roots.length who
      have hnash := hstack.1
      rw [hpayoff] at hnash
      have hroot := nearMinimum_rootNashAgainstPayoff_eq_allContinue
        reward tail root hM hkappa hreward hminimum htail hsingleton hnash hnear
      calc
        root :: roots = quittingAllContinueRoot ::
            List.replicate roots.length quittingAllContinueRoot := by
          rw [hroot]
          exact congrArg (List.cons quittingAllContinueRoot) hroots
        _ = List.replicate (root :: roots).length quittingAllContinueRoot := by
          rw [List.length_cons, List.replicate_succ]

end GameTheory
