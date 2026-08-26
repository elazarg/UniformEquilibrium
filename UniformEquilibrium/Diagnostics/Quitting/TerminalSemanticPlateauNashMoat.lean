/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import MathUE.ProbabilityMassFunction.Simplex
import MathUE.Topology.CompactRobustMoat
import UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed
import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationCompactPath
import UniformEquilibrium.Quitting.Root.NashDefect
import UniformEquilibrium.Quitting.Root.NashDefectContinuity

/-!
# A Nash-defect moat around the canonical incidence plateau

At the canonical joint reset point selected by the debt/incidence
lexicographic argument, the all-Continue root is the unique exact cap--Nash
root.  Compactness of the finite product root simplex upgrades this qualitative
uniqueness to a uniform separation statement.

For every positive threshold `eta`, all roots whose total opponent incidence
is at least `eta` have total Nash defect bounded below by a positive moat.
The moat persists for every cap in an open neighborhood of the selected cap.
No linear modulus or explicit neighborhood radius is asserted.

The final producer couples this separation with the positive-incidence joint
semantic/law point.  It does not yet identify the nearby cap with the shifted
tail payoff at a chronological row of a realizing profile; that cap-provenance
step remains necessary before the moat becomes a legal stage-deviation charge.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Root coalition mass is continuous in simplex coordinates. -/
theorem continuous_quittingRootCoalitionMass_simplex
    (coalition : Finset ι) :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingRootCoalitionMass (quittingRootOfSimplex root) coalition) := by
  unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
    quittingRootQuitRates
  apply (continuous_finsetProd _ fun player _ => ?_).mul
    (continuous_finsetProd _ fun player _ => ?_)
  · simp only [quittingRootOfSimplex_apply_toReal]
    have hplayer : Continuous (fun root : QuittingRootSimplex ι =>
        (root player : Bool → ℝ)) :=
      continuous_subtype_val.comp (continuous_apply player)
    exact (continuous_apply true).comp hplayer
  · simp only [quittingRootOfSimplex_apply_toReal]
    have hplayer : Continuous (fun root : QuittingRootSimplex ι =>
        (root player : Bool → ℝ)) :=
      continuous_subtype_val.comp (continuous_apply player)
    exact continuous_const.sub ((continuous_apply true).comp hplayer)

/-- Total opponent incidence of a root is continuous in simplex coordinates. -/
theorem continuous_quittingRootTotalOpponentIncidenceMass_simplex
    (owner : ι) :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingRootTotalOpponentIncidenceMass owner
        (quittingRootOfSimplex root)) := by
  unfold quittingRootTotalOpponentIncidenceMass
    quittingRootOpponentIncidenceMass
  exact continuous_finsetSum _ fun _ _ =>
    continuous_finsetSum _ fun terminal _ =>
      continuous_quittingRootCoalitionMass_simplex terminal.val

/-- The all-Continue root has zero total opponent incidence. -/
@[simp] theorem quittingRootTotalOpponentIncidenceMass_allContinueRoot
    (owner : ι) :
    quittingRootTotalOpponentIncidenceMass owner
      (quittingAllContinueRoot : ι → PMF Bool) = 0 := by
  unfold quittingRootTotalOpponentIncidenceMass
    quittingRootOpponentIncidenceMass
  apply Finset.sum_eq_zero
  intro other _
  apply Finset.sum_eq_zero
  intro terminal _
  unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
    quittingRootQuitRates quittingAllContinueRoot
  obtain ⟨member, hmember⟩ := terminal.property
  have hzero : ∏ player ∈ terminal.val,
      ((PMF.pure false : PMF Bool) true).toReal = 0 := by
    apply Finset.prod_eq_zero hmember
    simp
  rw [hzero, zero_mul]

/-- **Fixed-cap Nash-defect moat.**  If all exact cap--Nash roots are
all-Continue, every root with a fixed positive amount of total opponent
incidence pays a uniformly positive total Nash defect. -/
theorem exists_totalNashDefect_moat_of_unique_allContinue
    (cap : Payoff ι) (owner : ι) (eta : ℝ)
    (heta : 0 < eta)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ root : QuittingRootSimplex ι,
        eta ≤ quittingRootTotalOpponentIncidenceMass owner
          (quittingRootOfSimplex root) →
        moat ≤ quittingRootTotalNashDefect reward cap
          (quittingRootOfSimplex root) := by
  let highIncidence : Set (QuittingRootSimplex ι) :=
    {root | eta ≤ quittingRootTotalOpponentIncidenceMass owner
      (quittingRootOfSimplex root)}
  have hhighClosed : IsClosed highIncidence :=
    isClosed_Ici.preimage
      (continuous_quittingRootTotalOpponentIncidenceMass_simplex owner)
  have hhighCompact : IsCompact highIncidence := hhighClosed.isCompact
  by_cases hhighNonempty : highIncidence.Nonempty
  · have hdefectContinuous : Continuous (fun root : QuittingRootSimplex ι =>
        quittingRootTotalNashDefect reward cap
          (quittingRootOfSimplex root)) := by
      change Continuous
        ((fun point : Payoff ι × QuittingRootSimplex ι =>
            quittingRootTotalNashDefect reward point.1
              (quittingRootOfSimplex point.2)) ∘
          fun root : QuittingRootSimplex ι => (cap, root))
      exact (continuous_quittingRootTotalNashDefect_simplex reward).comp
        (continuous_const.prodMk continuous_id)
    obtain ⟨selected, hselectedHigh, hselectedMin⟩ :=
      hhighCompact.exists_isMinOn hhighNonempty
        hdefectContinuous.continuousOn
    have hselectedNonneg : 0 ≤ quittingRootTotalNashDefect reward cap
        (quittingRootOfSimplex selected) :=
      quittingRootTotalNashDefect_nonneg reward cap
        (quittingRootOfSimplex selected)
    have hselectedPositive : 0 < quittingRootTotalNashDefect reward cap
        (quittingRootOfSimplex selected) := by
      apply lt_of_le_of_ne hselectedNonneg
      intro hzero
      have hnash : IsεQuittingRootNash reward cap 0
          (quittingRootOfSimplex selected) :=
        (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
          reward cap (quittingRootOfSimplex selected)).2 hzero.symm
      have hroot := hunique (quittingRootOfSimplex selected) hnash
      have hincidenceZero :
          quittingRootTotalOpponentIncidenceMass owner
            (quittingRootOfSimplex selected) = 0 := by
        rw [hroot]
        exact quittingRootTotalOpponentIncidenceMass_allContinueRoot owner
      have hselectedEta : eta ≤ quittingRootTotalOpponentIncidenceMass owner
          (quittingRootOfSimplex selected) := hselectedHigh
      rw [hincidenceZero] at hselectedEta
      linarith
    exact ⟨quittingRootTotalNashDefect reward cap
        (quittingRootOfSimplex selected), hselectedPositive,
      fun root hroot => hselectedMin hroot⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro root hroot
    exact False.elim (hhighNonempty ⟨root, hroot⟩)

/-! ## Robust compact-fiber moats -/

/-- Any continuous root statistic that vanishes at all-Continue inherits a
robust positive Nash-defect moat above each positive statistic threshold when
all-Continue is the unique exact root. This is the game-specific adapter to
the generic compact-fiber robust-moat theorem. -/
theorem exists_eventually_totalNashDefect_moat_of_uniqueAllContinue_of_continuous_measure
    (cap : Payoff ι) (measure : QuittingRootSimplex ι → ℝ)
    (hmeasure : Continuous measure)
    (hzero : ∀ root : QuittingRootSimplex ι,
      quittingRootOfSimplex root =
          (quittingAllContinueRoot : ι → PMF Bool) →
        measure root = 0)
    (eta : ℝ) (heta : 0 < eta)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ᶠ nearbyCap in 𝓝 cap,
        ∀ root : QuittingRootSimplex ι,
          eta ≤ measure root →
            moat ≤ quittingRootTotalNashDefect reward nearbyCap
              (quittingRootOfSimplex root) := by
  let high : Set (QuittingRootSimplex ι) := {root | eta ≤ measure root}
  have hhighClosed : IsClosed high :=
    isClosed_Ici.preimage hmeasure
  have hpositive : ∀ root ∈ high,
      0 < quittingRootTotalNashDefect reward cap
        (quittingRootOfSimplex root) := by
    intro root hrootHigh
    have hnonneg : 0 ≤ quittingRootTotalNashDefect reward cap
        (quittingRootOfSimplex root) :=
      quittingRootTotalNashDefect_nonneg reward cap
        (quittingRootOfSimplex root)
    apply lt_of_le_of_ne hnonneg
    intro hdefectZero
    have hnash : IsεQuittingRootNash reward cap 0
        (quittingRootOfSimplex root) :=
      (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
        reward cap (quittingRootOfSimplex root)).2 hdefectZero.symm
    have hroot := hunique (quittingRootOfSimplex root) hnash
    have hmeasureZero := hzero root hroot
    change eta ≤ measure root at hrootHigh
    rw [hmeasureZero] at hrootHigh
    linarith
  simpa only [high, Set.mem_setOf_eq] using
    (Math.Topology.exists_eventually_uniform_pos_on_closed_of_compactSpace
      (fun nearbyCap root => quittingRootTotalNashDefect reward nearbyCap
        (quittingRootOfSimplex root))
      (continuous_quittingRootTotalNashDefect_simplex reward)
      high hhighClosed cap hpositive)

/-- The total-opponent-incidence specialization of the generic root-statistic
moat. -/
theorem exists_eventually_totalNashDefect_moat_of_unique_allContinue
    (cap : Payoff ι) (owner : ι) (eta : ℝ)
    (heta : 0 < eta)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ᶠ nearbyCap in 𝓝 cap,
        ∀ root : QuittingRootSimplex ι,
          eta ≤ quittingRootTotalOpponentIncidenceMass owner
            (quittingRootOfSimplex root) →
          moat ≤ quittingRootTotalNashDefect reward nearbyCap
            (quittingRootOfSimplex root) := by
  refine
    exists_eventually_totalNashDefect_moat_of_uniqueAllContinue_of_continuous_measure
      (reward := reward) cap
      (fun root => quittingRootTotalOpponentIncidenceMass owner
        (quittingRootOfSimplex root))
      (continuous_quittingRootTotalOpponentIncidenceMass_simplex owner)
      ?_ eta heta hunique
  intro root hroot
  rw [hroot]
  exact quittingRootTotalOpponentIncidenceMass_allContinueRoot owner

/-- The robust total-absorption moat at a unique all-Continue cap. -/
theorem exists_eventually_absorptionNashDefect_moat_of_unique_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ᶠ nearbyCap in 𝓝 cap,
        ∀ root : QuittingRootSimplex ι,
          eta ≤ quittingSimplexAbsorptionMass root →
          moat ≤ quittingRootTotalNashDefect reward nearbyCap
            (quittingRootOfSimplex root) := by
  refine
    exists_eventually_totalNashDefect_moat_of_uniqueAllContinue_of_continuous_measure
      (reward := reward) cap quittingSimplexAbsorptionMass
      continuous_quittingSimplexAbsorptionMass ?_ eta heta hunique
  intro root hroot
  rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass, hroot]
  exact quittingRootAbsorptionMass_allContinueRoot

/-- A fixed-cap approximate Nash root whose total absorption exceeds a positive
threshold pays one positive total-defect moat. -/
theorem exists_absorptionNashDefect_moat_of_unique_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ ε root,
        IsεQuittingRootNash reward cap ε
            (quittingRootOfSimplex root) →
        Fintype.card ι * ε < moat →
        quittingSimplexAbsorptionMass root < eta := by
  obtain ⟨moat, hmoat, hnear⟩ :=
    exists_eventually_absorptionNashDefect_moat_of_unique_allContinue
      reward cap eta heta hunique
  have hfixed := hnear.self_of_nhds
  refine ⟨moat, hmoat, ?_⟩
  intro ε root hnash hsmall
  by_contra hnot
  have hhigh : eta ≤ quittingSimplexAbsorptionMass root :=
    le_of_not_gt hnot
  have hlower := hfixed root hhigh
  have hupper :=
    quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
      reward cap (quittingRootOfSimplex root) ε hnash
  linarith

/-- Opponent absorption is continuous in simplex coordinates. -/
theorem continuous_quittingRootOpponentAbsorptionMass_simplex
    (owner : ι) :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingRootOpponentAbsorptionMass (quittingRootOfSimplex root) owner) := by
  simp_rw [quittingRootOpponentAbsorptionMass_eq_one_sub_prod,
    quittingRootOfSimplex_apply_toReal]
  exact continuous_const.sub
    (continuous_finsetProd _ fun other _ =>
      continuous_const.sub
        ((continuous_apply true).comp
          (continuous_subtype_val.comp (continuous_apply other))))

/-- The robust Nash-defect moat specialized to one owner's ordinary opponent
absorption hazard. -/
theorem exists_eventually_totalNashDefect_moat_of_unique_allContinue_opponentAbsorption
    (cap : Payoff ι) (owner : ι) (eta : ℝ)
    (heta : 0 < eta)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ᶠ nearbyCap in 𝓝 cap,
        ∀ root : QuittingRootSimplex ι,
          eta ≤ quittingRootOpponentAbsorptionMass
              (quittingRootOfSimplex root) owner →
            moat ≤ quittingRootTotalNashDefect reward nearbyCap
              (quittingRootOfSimplex root) := by
  refine
    exists_eventually_totalNashDefect_moat_of_uniqueAllContinue_of_continuous_measure
      (reward := reward) cap
      (fun root => quittingRootOpponentAbsorptionMass
        (quittingRootOfSimplex root) owner)
      (continuous_quittingRootOpponentAbsorptionMass_simplex owner)
      ?_ eta heta hunique
  intro root hroot
  rw [hroot]
  unfold quittingRootOpponentAbsorptionMass
  rw [show Function.update
      (quittingAllContinueRoot : ι → PMF Bool) owner (PMF.pure false) =
        quittingAllContinueRoot by
    funext player
    by_cases hplayer : player = owner
    · subst player
      simp [quittingAllContinueRoot]
    · simp [Function.update_of_ne hplayer, quittingAllContinueRoot]]
  exact quittingRootAbsorptionMass_allContinueRoot

/-- The canonical reset-face plateau carries a robust Nash-defect moat at
every positive total-opponent-incidence scale. -/
theorem exists_resetFace_positiveIncidence_robustNashMoat
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (owner : ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (htarget : (target, mass) ∈
      quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt target owner = 0)
    (hincidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner mass) :
    ∃ returned : QuittingTerminalSemanticLawPoint ι,
      returned ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt returned.1 owner = 0 ∧
      0 < quittingTerminalTotalOpponentIncidenceMass owner returned.2 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned.1 ∧
      (∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward returned.1.2 0 root →
          root = (quittingAllContinueRoot : ι → PMF Bool)) ∧
      ∀ eta, 0 < eta →
        ∃ moat : ℝ, 0 < moat ∧
          ∀ᶠ nearbyCap in 𝓝 returned.1.2,
            ∀ root : QuittingRootSimplex ι,
              eta ≤ quittingRootTotalOpponentIncidenceMass owner
                (quittingRootOfSimplex root) →
              moat ≤ quittingRootTotalNashDefect reward nearbyCap
                (quittingRootOfSimplex root) := by
  obtain ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
      hsourceLe, _hallContinueNash, _hfixed, hallRoots⟩ :=
    exists_resetFace_positiveTotalIncidence_allContinueCapPlateau
      source target mass owner hminimum hsourcePositive htarget hreset hincidence
  refine ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
    hsourceLe, hallRoots, ?_⟩
  intro eta heta
  exact exists_eventually_totalNashDefect_moat_of_unique_allContinue
    (reward := reward) returned.1.2 owner eta heta hallRoots

end GameTheory
