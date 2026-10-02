/-
Marked near-minimum dates are finitely multiple in any single play.

Fix a cap whose only exact product cap--Nash root is all-Continue, a terminal
coalition, and a positive stage-mass floor.  One robust absorption moat and one
neighborhood of that cap then serve every behavioral profile at once: at each
date where the profile puts at least the floor of stage mass on the coalition
and the post-date all-Continue-shift tail cap lies in the neighborhood, the
live root pays at least the moat of total Nash defect against its own tail cap,
and its reached weight is at least the floor.

The summed directed-transport ledger, taken at any cutoff beyond the last
marked date, writes the profile's total semantic debt as a nonnegatively
weighted sum of row charges plus a nonnegative tail term.  Retaining only the
marked dates turns the per-date charge into a count: the number of such dates
in one play is bounded by the profile's own total debt divided by floor times
moat.

The uniqueness hypothesis is automatic when the cap is the cap coordinate of a
carrier pair whose total debt is at most the positive global minimum, by the
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

/-! ## The row charge of a date -/

/-- The directed-transport charge a profile pays at one date: the reached
weight of the live row times the total Nash defect of the live root against the
cap of its own all-Continue-shift tail. -/
private def fableMarkedRowCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) : ℝ :=
  quittingLiveMass reward profile time *
    quittingRootTotalNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).2
      (quittingProfileLiveRoot reward profile time)

private theorem fableMarkedRowCharge_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    0 ≤ fableMarkedRowCharge reward profile time :=
  mul_nonneg (quittingLiveMass_nonneg reward profile time)
    (quittingRootTotalNashDefect_nonneg reward _ _)

/-- Total semantic debt of a carrier pair is nonnegative, coordinate by
coordinate. -/
private theorem fable_debtSum_nonneg_of_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    0 ≤ quittingTerminalSemanticDebtSum pair :=
  Finset.sum_nonneg fun who _ =>
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who

/-! ## The summed directed-transport ledger -/

/-- The directed-transport ledger of the all-Continue spine, summed over
players: total semantic debt of a profile is the sum of its row charges before
the cutoff, plus the live-mass-weighted total debt of the spine tail at the
cutoff. -/
private theorem fable_debtSum_eq_sum_charge_add_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) =
      (∑ time ∈ Finset.range cutoff,
          fableMarkedRowCharge reward profile time) +
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
    simp only [fableMarkedRowCharge, quittingRootTotalNashDefect,
      Finset.mul_sum]
  · rw [Finset.mul_sum]

/-! ## The per-date charge floor -/

/-- At a date whose stage coalition mass clears the floor and whose tail cap
lies in the robust moat neighborhood, the row charge is at least floor times
moat.  Stage mass factors as live mass times the live root's exact coalition
mass, and live mass is at most one, so the live root keeps absorption above the
floor; the reached weight of the row is itself at least the stage mass. -/
private theorem fable_markedDate_charge_floor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) {kappa moat : ℝ}
    (hmoat : 0 ≤ moat)
    (hdefect : moat ≤ quittingRootTotalNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).2
      (quittingProfileLiveRoot reward profile time))
    (hstageBound :
      kappa ≤ quittingStageCoalitionMass reward profile time terminal) :
    kappa * moat ≤ fableMarkedRowCharge reward profile time := by
  have hlive : kappa ≤ quittingLiveMass reward profile time :=
    le_trans hstageBound
      (quittingStageCoalitionMass_le_liveMass reward profile time terminal)
  exact mul_le_mul hlive hdefect hmoat
    (quittingLiveMass_nonneg reward profile time)

/-- A date whose stage coalition mass clears the floor has a live root whose
total absorption clears the floor. -/
private theorem fable_markedDate_absorption_floor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) {kappa : ℝ}
    (hstageBound :
      kappa ≤ quittingStageCoalitionMass reward profile time terminal) :
    kappa ≤ quittingRootAbsorptionMass
      (quittingProfileLiveRoot reward profile time) := by
  have hstage := hstageBound
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass
    reward profile time terminal] at hstage
  set root := quittingProfileLiveRoot reward profile time
  have hcoalNonneg := quittingRootCoalitionMass_nonneg root terminal.val
  have hprod :
      quittingLiveMass reward profile time *
          quittingRootCoalitionMass root terminal.val ≤
        quittingRootCoalitionMass root terminal.val :=
    mul_le_of_le_one_left hcoalNonneg
      (quittingLiveMass_le_one reward profile time)
  have hcover := quittingRootCoalitionMass_le_absorptionMass_of_nonempty
    root terminal.val terminal.2
  linarith

/-! ## The marked-date multiplicity bound -/

/-- **Marked-date multiplicity bound.**  Fix a cap at which the all-Continue
root is the only exact product cap--Nash root, one terminal coalition, and a
positive stage-mass floor.  Then one positive moat and one neighborhood of that
cap work for every behavioral profile at once: for every finite set of dates at
which the profile puts at least the floor of stage mass on the coalition and
the post-date all-Continue-shift tail cap lies in the neighborhood, the number
of such dates times floor times moat is at most the profile's own total
terminal semantic debt.

With rewards bounded, total debt is bounded, so a single play reaches only
boundedly many such dates. -/
theorem fable_markedDate_multiplicity_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (capLim : Payoff ι)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward capLim 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (terminal : {S : Finset ι // S.Nonempty}) {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ moat : ℝ, 0 < moat ∧ ∃ U ∈ 𝓝 capLim,
      ∀ (profile : (quittingGame reward).BehaviorProfile) (F : Finset ℕ),
        (∀ t ∈ F, kappa ≤ quittingStageCoalitionMass reward profile t terminal ∧
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (t + 1))).2 ∈ U) →
        (F.card : ℝ) * (kappa * moat) ≤
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) := by
  obtain ⟨moat, hmoat, hnear⟩ :=
    exists_eventually_absorptionNashDefect_moat_of_unique_allContinue
      reward capLim kappa hkappa hunique
  obtain ⟨U, hU, hUprop⟩ := Filter.eventually_iff_exists_mem.mp hnear
  refine ⟨moat, hmoat, U, hU, ?_⟩
  intro profile F hF
  rcases F.eq_empty_or_nonempty with rfl | hne
  · simpa using fable_debtSum_nonneg_of_mem_carrier reward
      (quittingTerminalSemanticPair_mem_carrier reward profile)
  -- Every marked date pays at least `kappa * moat` of row charge.
  have hkey : ∀ t ∈ F, kappa * moat ≤ fableMarkedRowCharge reward profile t := by
    intro t ht
    obtain ⟨hstageBound, hcapMem⟩ := hF t ht
    have habsorb := fable_markedDate_absorption_floor reward profile t terminal
      hstageBound
    set root := quittingProfileLiveRoot reward profile t
    have hback :
        quittingRootOfSimplex (fun who => stdSimplexEquiv (root who)) = root := by
      funext who
      exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)
    have hsimplex :
        kappa ≤ quittingSimplexAbsorptionMass
          (fun who => stdSimplexEquiv (root who)) := by
      rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass, hback]
      exact habsorb
    have hdefect := hUprop _ hcapMem (fun who => stdSimplexEquiv (root who)) hsimplex
    rw [hback] at hdefect
    exact fable_markedDate_charge_floor reward profile t terminal hmoat.le
      hdefect hstageBound
  -- The ledger at any cutoff beyond the last marked date dominates the count.
  have hsubset : F ⊆ Finset.range (F.max' hne + 1) := fun t ht =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (F.le_max' t ht))
  have hrestrict :
      ∑ t ∈ F, fableMarkedRowCharge reward profile t ≤
        ∑ t ∈ Finset.range (F.max' hne + 1),
          fableMarkedRowCharge reward profile t :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      fun t _ _ => fableMarkedRowCharge_nonneg reward profile t
  have hcount : (F.card : ℝ) * (kappa * moat) ≤
      ∑ t ∈ F, fableMarkedRowCharge reward profile t := by
    have hsmul := Finset.card_nsmul_le_sum F
      (fun t => fableMarkedRowCharge reward profile t) (kappa * moat) hkey
    simpa [nsmul_eq_mul] using hsmul
  have hledger := fable_debtSum_eq_sum_charge_add_tail reward profile
    (F.max' hne + 1)
  have htail :
      0 ≤ quittingLiveMass reward profile (F.max' hne + 1) *
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile
              (F.max' hne + 1))) :=
    mul_nonneg (quittingLiveMass_nonneg reward profile (F.max' hne + 1))
      (fable_debtSum_nonneg_of_mem_carrier reward
        (quittingTerminalSemanticPair_mem_carrier reward _))
  linarith

/-! ## The near-minimum tail form -/

/-- **Marked-date multiplicity bound at a near-minimum cap.**  If the cap is
the cap coordinate of a carrier pair whose total debt is at most the positive
global carrier minimum, the uniqueness hypothesis is supplied by the
table-level near-minimum cap--Nash radius and the same multiplicity bound
holds. -/
theorem fable_markedDate_multiplicity_bound_of_minimumTailLimit
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
    (terminal : {S : Finset ι // S.Nonempty}) {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ moat : ℝ, 0 < moat ∧ ∃ U ∈ 𝓝 tailLim.2,
      ∀ (profile : (quittingGame reward).BehaviorProfile) (F : Finset ℕ),
        (∀ t ∈ F, kappa ≤ quittingStageCoalitionMass reward profile t terminal ∧
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (t + 1))).2 ∈ U) →
        (F.card : ℝ) * (kappa * moat) ≤
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) := by
  obtain ⟨epsilon, hepsilon, hradius⟩ :=
    exists_pos_nearMinimum_capNash_eq_allContinue_radius
      (reward := reward) (quittingTerminalSemanticDebtSum source) hpos hminimum
  exact fable_markedDate_multiplicity_bound reward tailLim.2
    (hradius tailLim htailMem (by linarith)) terminal hkappa

end GameTheory
