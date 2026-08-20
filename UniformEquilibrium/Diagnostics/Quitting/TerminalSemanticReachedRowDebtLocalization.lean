/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.SurvivalWeightedReachedHistoryAccount
import MathUE.Topology.FiniteLabelSubsequence
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionWindow

/-!
# Reached-row debt localization

The generic reached-history account specializes exactly to the literal
quitting spine: its weights are live masses, and its one-step defects are the
coordinate Nash defects against the successive continuation caps.

At a literal row where one observer quits surely, every other player's
current-suffix semantic debt is its local Nash defect.  A scalar lower bound
on current total semantic debt and survival-weighted transport of the
observer's debt therefore localize the remaining debt on those other-player
defects.

For a sequence of such uniformly reached rows, vanishing initial observer
debt freezes one other player along a strict subsequence.  That player's
literal best-endpoint deviation has a uniformly positive global gain.  In
particular, the sequence of its canonical legal gains does not converge to
zero.
-/

noncomputable section

namespace GameTheory

open Filter Finset Math.Probability Math.PMFProduct
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-! ## Exact literal-spine account -/

omit [DecidableEq iota] in
/-- The reached-history weight of the literal roots is exactly the
probability that the original profile remains live at the displayed row. -/
theorem reachedHistoryWeight_stationaryContinueMass_eq_quittingLiveMass
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∀ time,
      reachedHistoryWeight
          (fun stage => quittingStationaryContinueMass
            (quittingProfileLiveRoot reward profile stage)) time =
        quittingLiveMass reward profile time := by
  intro time
  induction time with
  | zero => simp
  | succ time ih =>
      rw [reachedHistoryWeight_succ, quittingLiveMass_succ, ih]
      congr 1

/-- **Exact finite literal-spine account.**  Initial semantic debt equals the
sum of live-mass-weighted coordinate Nash defects against the successive cap
vectors, plus the live-mass-weighted debt remaining at the cutoff.  No reward
bound, sign premise, or equilibrium hypothesis is needed. -/
theorem quittingTerminalSemanticDebt_eq_sum_liveMass_mul_capDefect_add_liveTailDebt
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (cutoff : Nat) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who =
      (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile
                (time + 1))).2
            (quittingProfileLiveRoot reward profile time) who) +
        quittingLiveMass reward profile cutoff *
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile cutoff)) who := by
  let survival : Nat -> Real := fun time =>
    quittingStationaryContinueMass
      (quittingProfileLiveRoot reward profile time)
  let defect : Nat -> Real := fun time =>
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).2
      (quittingProfileLiveRoot reward profile time) who
  let debt : Nat -> Real := fun time =>
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile time)) who
  have haccount : ∀ time,
      debt time = defect time + survival time * debt (time + 1) := by
    intro time
    dsimp only [debt, defect, survival]
    rw [quittingTerminalSemanticPair_spine_eq_prefix reward profile time]
    exact quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul
      reward _ _ who
  have htelescope :=
    debt_zero_eq_sum_reachedHistoryWeight_mul_defect_add
      survival defect debt haccount cutoff
  have hweight : ∀ time,
      reachedHistoryWeight survival time =
        quittingLiveMass reward profile time := by
    intro time
    exact reachedHistoryWeight_stationaryContinueMass_eq_quittingLiveMass
      reward profile time
  simpa only [survival, defect, debt, hweight,
    quittingAllContinueProfileSpine] using htelescope

/-! ## Pointwise reached-row localization -/

/-- If a different player quits surely, another player's semantic debt after
prefixing by the displayed root is exactly its coordinate Nash defect.  No
sign or carrier premise on the tail pair is needed. -/
theorem quittingTerminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_sureQuitter
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (tail : QuittingTerminalSemanticPair iota) (root : iota -> PMF Bool)
    (observer other : iota) (hother : other ≠ observer)
    (hsure : root observer = PMF.pure true) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root tail) other =
      quittingRootCoordinateNashDefect reward tail.1 root other := by
  have hsureContinue : QuittingRootHasSureQuitter
      (Function.update root other (PMF.pure false)) := by
    refine ⟨observer, ?_⟩
    simp [Function.update, hother.symm, hsure]
  have hcontinue := quittingRootExpectedPayoff_eq_of_hasSureQuitter
    reward (Function.update root other (PMF.pure false)) hsureContinue
      (Function.update tail.1 other (tail.2 other)) tail.1 other
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
    quittingRootCoordinateNashDefect quittingRootContinuePayoff
  dsimp only
  rw [hcontinue]

/-- **Reached-row debt inequality.**  Suppose `minimumDebt` is a lower bound
for the total semantic debt of the current suffix.  At a row reached with
probability at least `reachFloor` where `observer` quits surely, all of that
floor except the survival-affordable observer debt is carried by the other
players' coordinate Nash defects.

The premise is the one current-suffix inequality actually used; it does not
require a chosen minimizing semantic pair or global minimality of the scalar
floor. -/
theorem minimumDebt_sub_observerDebt_div_reachFloor_le_sum_other_reachedDefect
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (minimumDebt : Real)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : iota) (stage : Nat) (reachFloor : Real)
    (hminimum : minimumDebt <= quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile stage)))
    (hreachFloor : 0 < reachFloor)
    (hreach : reachFloor <= quittingLiveMass reward profile stage)
    (hsure : quittingProfileLiveRoot reward profile stage observer =
      PMF.pure true) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    minimumDebt -
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) observer /
            reachFloor <=
      ∑ other ∈ Finset.univ.erase observer,
        quittingRootCoordinateNashDefect reward tail.1 root other := by
  dsimp only
  let current := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile stage)
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  have hcurrentCarrier : current ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have hcurrentDebtNonneg : 0 <=
      quittingTerminalSemanticDebt current observer :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hcurrentCarrier observer
  have hcurrentPrefix : current =
      quittingTerminalSemanticPrefix reward root tail := by
    dsimp only [current, root, tail]
    exact quittingTerminalSemanticPair_spine_eq_prefix reward profile stage
  have hotherDebt : ∀ other ∈ Finset.univ.erase observer,
      quittingTerminalSemanticDebt current other =
        quittingRootCoordinateNashDefect reward tail.1 root other := by
    intro other hother
    rw [hcurrentPrefix]
    exact
      quittingTerminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_sureQuitter
        reward tail root observer other (Finset.ne_of_mem_erase hother)
          (by simpa only [root] using hsure)
  have hcurrentSplit : quittingTerminalSemanticDebtSum current =
      quittingTerminalSemanticDebt current observer +
        ∑ other ∈ Finset.univ.erase observer,
          quittingRootCoordinateNashDefect reward tail.1 root other := by
    unfold quittingTerminalSemanticDebtSum
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ observer), add_comm]
    congr 1
    apply Finset.sum_congr rfl
    exact hotherDebt
  have hweightedDebt := quittingLiveMass_mul_spineDebt_le_initialDebt
    (reward := reward) profile observer stage
  have hfloorWeighted : reachFloor *
        quittingTerminalSemanticDebt current observer <=
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) observer := by
    calc
      reachFloor * quittingTerminalSemanticDebt current observer <=
          quittingLiveMass reward profile stage *
            quittingTerminalSemanticDebt current observer :=
        mul_le_mul_of_nonneg_right hreach hcurrentDebtNonneg
      _ <= quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer := by
        simpa only [current] using hweightedDebt
  have hcurrentDebtLe : quittingTerminalSemanticDebt current observer <=
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer /
        reachFloor :=
    (le_div_iff₀ hreachFloor).2 (by
      simpa only [mul_comm] using hfloorWeighted)
  change minimumDebt <= quittingTerminalSemanticDebtSum current at hminimum
  rw [hcurrentSplit] at hminimum
  linarith

/-- **Uniform-reach asymptotic reached-row localization.**  If current suffix
debt is uniformly bounded below by a positive scalar while the observer's
initial debt vanishes and its selected sure-Quit rows retain a fixed positive
reach floor, one fixed other player has a legal reached-row deviation with a
uniformly positive gain along a strict subsequence.

No cardinality premise is required.  Nonemptiness of the erased player set
follows from the positive asymptotic lower bound. -/
theorem exists_fixed_other_reachedRowGain_subsequence
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (minimumDebt : Real) (hminimumDebt : 0 < minimumDebt)
    (profiles : Nat -> (quittingGame reward).BehaviorProfile)
    (stages : Nat -> Nat) (observer : iota) (reachFloor : Real)
    (hminimum : ∀ n,
      minimumDebt <= quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward (profiles n) (stages n))))
    (hreachFloor : 0 < reachFloor)
    (hreach : ∀ n, reachFloor <=
      quittingLiveMass reward (profiles n) (stages n))
    (hsure : ∀ n,
      quittingProfileLiveRoot reward (profiles n) (stages n) observer =
        PMF.pure true)
    (hobserverDebt : Tendsto (fun n =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) observer)
      atTop (nhds 0)) :
    ∃ (other : iota) (subseq : Nat -> Nat),
      other ≠ observer ∧ StrictMono subseq ∧
      ∀ n,
        reachFloor * minimumDebt /
              (2 * ((Finset.univ.erase observer).card : Real)) <=
          quittingTerminalPayoff reward
              (Function.update (profiles (subseq n)) other
                (quittingStagePureEndpointBehaviorDeviation reward
                  (profiles (subseq n)) other (stages (subseq n))
                  (quittingRootBestEndpointAction reward
                    (quittingTerminalSemanticPair reward
                      (quittingAllContinueProfileSpine reward
                        (profiles (subseq n))
                        (stages (subseq n) + 1))).1
                    (quittingProfileLiveRoot reward
                      (profiles (subseq n)) (stages (subseq n))) other))) other -
            quittingTerminalPayoff reward (profiles (subseq n)) other := by
  let defect : Nat -> iota -> Real := fun n who =>
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (profiles n) (stages n + 1))).1
      (quittingProfileLiveRoot reward (profiles n) (stages n)) who
  let error : Nat -> Real := fun n =>
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (profiles n)) observer / reachFloor
  have herror : Tendsto error atTop (nhds 0) := by
    have hdiv := hobserverDebt.div_const reachFloor
    simpa only [error, zero_div] using hdiv
  have hlower : ∀ n, minimumDebt - error n <=
      ∑ other ∈ Finset.univ.erase observer, defect n other := by
    intro n
    exact minimumDebt_sub_observerDebt_div_reachFloor_le_sum_other_reachedDefect
      reward minimumDebt (profiles n) observer (stages n) reachFloor
        (hminimum n) hreachFloor (hreach n) (hsure n)
  obtain ⟨other, hotherMem, subseq, hsubseq, hdefect⟩ :=
    Math.exists_fixed_mem_subsequence_of_sum_lower_and_error_tendsto_zero
      (Finset.univ.erase observer) defect error minimumDebt hminimumDebt
        herror hlower
  have hother : other ≠ observer := Finset.ne_of_mem_erase hotherMem
  refine ⟨other, subseq, hother, hsubseq, ?_⟩
  intro n
  have hdefectNonneg : 0 <= defect (subseq n) other :=
    quittingRootCoordinateNashDefect_nonneg reward _ _ other
  have hscaled : reachFloor *
        (minimumDebt /
          (2 * ((Finset.univ.erase observer).card : Real))) <=
      quittingLiveMass reward (profiles (subseq n)) (stages (subseq n)) *
        defect (subseq n) other := by
    calc
      reachFloor *
            (minimumDebt /
              (2 * ((Finset.univ.erase observer).card : Real))) <=
          reachFloor * defect (subseq n) other :=
        mul_le_mul_of_nonneg_left (hdefect n) hreachFloor.le
      _ <= quittingLiveMass reward (profiles (subseq n)) (stages (subseq n)) *
            defect (subseq n) other :=
        mul_le_mul_of_nonneg_right (hreach (subseq n)) hdefectNonneg
  calc
    reachFloor * minimumDebt /
          (2 * ((Finset.univ.erase observer).card : Real)) =
        reachFloor *
          (minimumDebt /
            (2 * ((Finset.univ.erase observer).card : Real))) := by ring
    _ <= quittingLiveMass reward (profiles (subseq n)) (stages (subseq n)) *
          defect (subseq n) other := hscaled
    _ = _ := by
      symm
      simpa only [defect] using
        (quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
          reward (profiles (subseq n)) other (stages (subseq n)))

/-- **Reached-row nonconvergence capstone.**  Under the uniform-reach and
positive scalar debt-floor hypotheses, one fixed non-observer's canonical
legal best-endpoint gain sequence does not converge to zero. -/
theorem exists_other_reachedRowGain_not_tendsto_zero
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (minimumDebt : Real) (hminimumDebt : 0 < minimumDebt)
    (profiles : Nat -> (quittingGame reward).BehaviorProfile)
    (stages : Nat -> Nat) (observer : iota) (reachFloor : Real)
    (hminimum : ∀ n,
      minimumDebt <= quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward (profiles n) (stages n))))
    (hreachFloor : 0 < reachFloor)
    (hreach : ∀ n, reachFloor <=
      quittingLiveMass reward (profiles n) (stages n))
    (hsure : ∀ n,
      quittingProfileLiveRoot reward (profiles n) (stages n) observer =
        PMF.pure true)
    (hobserverDebt : Tendsto (fun n =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) observer)
      atTop (nhds 0)) :
    ∃ other : iota, other ≠ observer ∧
      ¬ Tendsto (fun n =>
        quittingTerminalPayoff reward
            (Function.update (profiles n) other
              (quittingStagePureEndpointBehaviorDeviation reward
                (profiles n) other (stages n)
                (quittingRootBestEndpointAction reward
                  (quittingTerminalSemanticPair reward
                    (quittingAllContinueProfileSpine reward
                      (profiles n) (stages n + 1))).1
                  (quittingProfileLiveRoot reward
                    (profiles n) (stages n)) other))) other -
          quittingTerminalPayoff reward (profiles n) other)
        atTop (nhds 0) := by
  obtain ⟨other, subseq, hother, hsubseq, hbound⟩ :=
    exists_fixed_other_reachedRowGain_subsequence reward minimumDebt
      hminimumDebt profiles stages observer reachFloor hminimum hreachFloor
        hreach hsure hobserverDebt
  refine ⟨other, hother, ?_⟩
  have hplayers : (Finset.univ.erase observer).Nonempty := by
    exact ⟨other, Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩⟩
  have hcard : 0 < ((Finset.univ.erase observer).card : Real) := by
    exact_mod_cast Finset.card_pos.mpr hplayers
  apply Math.not_tendsto_zero_of_positive_lower_bound_on_strict_subsequence
    _ subseq
      (reachFloor * minimumDebt /
        (2 * ((Finset.univ.erase observer).card : Real))) hsubseq
  · positivity
  · exact hbound

end GameTheory
