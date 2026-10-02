/-
Marked rows of strict-inert selections are uniformly cap-inexact.

A marked row of a profile sequence carries a uniform stage-mass floor at one
fixed terminal coalition.  Stage mass factors as live mass times the live
root's exact coalition mass, and live mass is at most one, so the marked live
root keeps coalition mass — hence total absorption — above that floor.

If the marked spine tails' caps converge to a cap whose only exact product
cap--Nash root is all-Continue, the robust absorption moat at that cap applies
to every marked live root at all late ranks: the marked row as a whole pays a
uniform positive total Nash defect against its own tail cap.

The uniqueness hypothesis is automatic when the tails converge to a carrier
pair whose total debt is at most the positive global minimum, by the
table-level near-minimum cap--Nash radius.
-/
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauNashMoat
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMarkedVariational
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCapNashNearMinimum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticDirectedTransport
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Cycles.CyclicGreenDebt
import UniformEquilibrium.Quitting.Paths.LiveMassRecurrence

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.ProbabilityMassFunction

open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The marked-row cap-defect floor -/

/-- **Marked-row cap-defect floor.**  Suppose a marked row of a profile
sequence carries a uniform positive stage-mass floor at one fixed terminal
coalition, and the marked spine tails' caps converge to a cap at which the
all-Continue root is the only exact product cap--Nash root.  Then one fixed
positive moat bounds below the total Nash defect of every marked live root
against its own tail cap, at all late ranks. -/
theorem fable_strictInert_markedRow_capDefect_floor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (capLim : Payoff ι)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward capLim 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (profile : ℕ → (quittingGame reward).BehaviorProfile) (mark : ℕ → ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) {kappa : ℝ} (hkappa : 0 < kappa)
    (hmass : ∀ n, kappa ≤
      quittingStageCoalitionMass reward (profile n) (mark n) terminal)
    (hcap : Filter.Tendsto
      (fun n => (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (profile n) (mark n + 1))).2)
      Filter.atTop (nhds capLim)) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ᶠ n in Filter.atTop,
        moat ≤ quittingRootTotalNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward (profile n)
              (mark n + 1))).2
          (quittingProfileLiveRoot reward (profile n) (mark n)) := by
  obtain ⟨moat, hmoat, hnear⟩ :=
    exists_eventually_absorptionNashDefect_moat_of_unique_allContinue
      reward capLim kappa hkappa hunique
  refine ⟨moat, hmoat, ?_⟩
  filter_upwards [hcap.eventually hnear] with n hn
  have hfactor :=
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass
      reward (profile n) (mark n) terminal
  have hstage := hmass n
  rw [hfactor] at hstage
  set root := quittingProfileLiveRoot reward (profile n) (mark n)
  have hcoalNonneg := quittingRootCoalitionMass_nonneg root terminal.val
  have hprod :
      quittingLiveMass reward (profile n) (mark n) *
          quittingRootCoalitionMass root terminal.val ≤
        quittingRootCoalitionMass root terminal.val :=
    mul_le_of_le_one_left hcoalNonneg
      (quittingLiveMass_le_one reward (profile n) (mark n))
  have habsorb : kappa ≤ quittingRootAbsorptionMass root := by
    have hcover := quittingRootCoalitionMass_le_absorptionMass_of_nonempty
      root terminal.val terminal.2
    linarith
  have hback : quittingRootOfSimplex (fun who => stdSimplexEquiv (root who)) = root := by
    funext who
    exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)
  have hsimplex :
      kappa ≤ quittingSimplexAbsorptionMass (fun who => stdSimplexEquiv (root who)) := by
    rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass, hback]
    exact habsorb
  have hdefect := hn (fun who => stdSimplexEquiv (root who)) hsimplex
  rwa [hback] at hdefect

/-! ## The near-minimum tail form -/

/-- **Marked-row cap-defect floor at a near-minimum tail limit.**  If the
marked spine tails' caps converge to the cap coordinate of a carrier pair
whose total debt is at most the positive global carrier minimum, the
uniqueness hypothesis is supplied by the table-level near-minimum cap--Nash
radius and the same uniform floor holds. -/
theorem fable_strictInert_markedRow_capDefect_floor_of_minimumTailLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpos : 0 < quittingTerminalSemanticDebtSum source)
    (tailLim : QuittingTerminalSemanticPair ι)
    (htailMem : tailLim ∈ quittingTerminalSemanticCarrier reward)
    (htailDebt : quittingTerminalSemanticDebtSum tailLim ≤
      quittingTerminalSemanticDebtSum source)
    (profile : ℕ → (quittingGame reward).BehaviorProfile) (mark : ℕ → ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) {kappa : ℝ} (hkappa : 0 < kappa)
    (hmass : ∀ n, kappa ≤
      quittingStageCoalitionMass reward (profile n) (mark n) terminal)
    (hcap : Filter.Tendsto
      (fun n => (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (profile n) (mark n + 1))).2)
      Filter.atTop (nhds tailLim.2)) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ᶠ n in Filter.atTop,
        moat ≤ quittingRootTotalNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward (profile n)
              (mark n + 1))).2
          (quittingProfileLiveRoot reward (profile n) (mark n)) := by
  obtain ⟨epsilon, hepsilon, hradius⟩ :=
    exists_pos_nearMinimum_capNash_eq_allContinue_radius
      (reward := reward) (quittingTerminalSemanticDebtSum source) hpos hminimum
  exact fable_strictInert_markedRow_capDefect_floor reward tailLim.2
    (hradius tailLim htailMem (by linarith)) profile mark terminal hkappa hmass
    hcap

/-! ## The whole-minus-tail debt excess -/

/-- The directed-transport ledger of the all-Continue spine, summed over
players: total semantic debt of a profile is the live-mass-weighted sum of the
total one-stage Nash defects of its live rows before the cutoff, plus the
live-mass-weighted total debt of the spine tail at the cutoff. -/
private theorem fable_debtSum_eq_sum_liveMass_totalDefect_add_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) =
      (∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingRootTotalNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile (time + 1))).2
              (quittingProfileLiveRoot reward profile time)) +
        quittingLiveMass reward profile cutoff *
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile cutoff)) := by
  have hweight :=
    reachedHistoryWeight_stationaryContinueMass_eq_quittingLiveMass
      reward profile
  have hledger : ∀ who : ι,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who =
        (∑ time ∈ Finset.range cutoff,
            reachedHistoryWeight
                (fun stage => quittingStationaryContinueMass
                  (quittingProfileLiveRoot reward profile stage)) time *
              quittingRootCoordinateNashDefect reward
                (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward profile
                    (time + 1))).2
                (quittingProfileLiveRoot reward profile time) who) +
          reachedHistoryWeight
              (fun stage => quittingStationaryContinueMass
                (quittingProfileLiveRoot reward profile stage)) cutoff *
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile cutoff)) who :=
    fun who => (QuittingTerminalSemanticPrefixChain.ofProfile
      (reward := reward) profile).debt_zero_eq_sum_reached_defect_add_tail
      who cutoff
  simp only [hweight] at hledger
  unfold quittingTerminalSemanticDebtSum
  simp only [hledger]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun time _ => ?_
    simp only [quittingRootTotalNashDefect, Finset.mul_sum]
  · rw [Finset.mul_sum]

/-- **Whole-minus-tail debt excess floor.**  Under the hypotheses of the
marked-row cap-defect floor, the uniform row defect is charged against the
profile's own total semantic debt: eventually, the whole debt exceeds the
survival-weighted spine-tail debt by at least `kappa * moat`.  The marked row
is the only summand of the directed-transport ledger that is retained; every
other reached row contributes a nonnegative charge. -/
theorem fable_strictInert_wholeDebt_excess_floor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (capLim : Payoff ι)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward capLim 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (profile : ℕ → (quittingGame reward).BehaviorProfile) (mark : ℕ → ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) {kappa : ℝ} (hkappa : 0 < kappa)
    (hmass : ∀ n, kappa ≤
      quittingStageCoalitionMass reward (profile n) (mark n) terminal)
    (hcap : Filter.Tendsto
      (fun n => (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (profile n) (mark n + 1))).2)
      Filter.atTop (nhds capLim)) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ᶠ n in Filter.atTop,
        kappa * moat +
            quittingLiveMass reward (profile n) (mark n + 1) *
              quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward (profile n)
                    (mark n + 1))) ≤
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward (profile n)) := by
  obtain ⟨moat, hmoat, hfloor⟩ :=
    fable_strictInert_markedRow_capDefect_floor reward capLim hunique profile
      mark terminal hkappa hmass hcap
  refine ⟨moat, hmoat, ?_⟩
  filter_upwards [hfloor] with n hn
  have hledger := fable_debtSum_eq_sum_liveMass_totalDefect_add_tail
    reward (profile n) (mark n + 1)
  have hnonneg : ∀ time ∈ Finset.range (mark n + 1),
      0 ≤ quittingLiveMass reward (profile n) time *
        quittingRootTotalNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward (profile n)
              (time + 1))).2
          (quittingProfileLiveRoot reward (profile n) time) :=
    fun time _ => mul_nonneg (quittingLiveMass_nonneg reward (profile n) time)
      (quittingRootTotalNashDefect_nonneg reward _ _)
  have hsingle :
      quittingLiveMass reward (profile n) (mark n) *
          quittingRootTotalNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward (profile n)
                (mark n + 1))).2
            (quittingProfileLiveRoot reward (profile n) (mark n)) ≤
        ∑ time ∈ Finset.range (mark n + 1),
          quittingLiveMass reward (profile n) time *
            quittingRootTotalNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward (profile n)
                  (time + 1))).2
              (quittingProfileLiveRoot reward (profile n) time) :=
    Finset.single_le_sum hnonneg
      (Finset.mem_range.mpr (Nat.lt_succ_self (mark n)))
  have hlive : kappa ≤ quittingLiveMass reward (profile n) (mark n) :=
    le_trans (hmass n)
      (quittingStageCoalitionMass_le_liveMass reward (profile n) (mark n)
        terminal)
  have hcharge : kappa * moat ≤
      quittingLiveMass reward (profile n) (mark n) *
        quittingRootTotalNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward (profile n)
              (mark n + 1))).2
          (quittingProfileLiveRoot reward (profile n) (mark n)) :=
    mul_le_mul hlive hn hmoat.le
      (quittingLiveMass_nonneg reward (profile n) (mark n))
  linarith

end GameTheory
