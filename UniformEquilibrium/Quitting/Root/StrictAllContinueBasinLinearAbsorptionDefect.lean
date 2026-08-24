/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailUniformAbsorption
import UniformEquilibrium.Quitting.Root.NashDefectContinuity
import UniformEquilibrium.Quitting.Stationary.ReturnedBlockTangentObstruction

/-!
# Linear absorption-defect price in a strict all-Continue basin

On a compact set of tails which is uniformly above every own singleton reward,
assume that all-Continue is the unique exact product-root Nash equilibrium.
Then one open neighborhood of that compact set charges every amount of root
absorption linearly by total Nash defect.

The proof has two scales.  At low absorption, the strict singleton gap forces
each played Quit marginal to pay a fixed coordinate defect.  At high absorption,
compactness and exact-root uniqueness supply a positive moat.  This module also
records the direct approximate-Nash, finite-family, Bellman-motion, and
vanishing-error consequences.  It supplies no root or chronological path.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- Root absorption is continuous in simplex coordinates. -/
theorem continuous_quittingRootAbsorptionMass_simplex :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingRootAbsorptionMass (quittingRootOfSimplex root)) := by
  simp_rw [quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingRootOfSimplex_apply_toReal]
  exact continuous_const.sub
    (continuous_finsetProd _ fun who _ =>
      (continuous_apply false).comp
        (continuous_subtype_val.comp (continuous_apply who)))

omit [DecidableEq ι] [Nonempty ι] in
/-- Absorption mass is at most one. -/
theorem quittingRootAbsorptionMass_le_one
    (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root ≤ 1 := by
  unfold quittingRootAbsorptionMass
  linarith [quittingStationaryContinueMass_nonneg root]

omit [Nonempty ι] in
/-- Low absorption in a strict singleton basin pays a linear Nash defect.
This is the explicit small-scale half of the compactness argument. -/
theorem quarterGap_mul_absorptionMass_le_totalNashDefect_of_smallAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) {M delta : ℝ}
    (hM : 0 ≤ M) (hdelta : 0 < delta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hgap : ∀ who, delta / 2 ≤ tail who -
      reward (quittingSingletonTerminal who) who)
    (hsmall : quittingRootAbsorptionMass root ≤
      delta / (2 * (delta + 4 * M))) :
    delta / 4 * quittingRootAbsorptionMass root ≤
      quittingRootTotalNashDefect reward tail root := by
  have hthresholdNonneg : 0 ≤ delta / (2 * (delta + 4 * M)) := by
    positivity
  have hcoordinate : ∀ who,
      delta / 4 * quittingRootQuitRates root who ≤
        quittingRootCoordinateNashDefect reward tail root who := by
    intro who
    let opponentMass := quittingRootOpponentAbsorptionMass root who
    have hopponentNonneg : 0 ≤ opponentMass :=
      quittingRootOpponentAbsorptionMass_nonneg root who
    have hopponentLe : opponentMass ≤
        delta / (2 * (delta + 4 * M)) := by
      exact (quittingRootOpponentAbsorptionMass_le_absorptionMass root who).trans
        hsmall
    have hopponentLeOne : opponentMass ≤ 1 :=
      quittingRootOpponentAbsorptionMass_le_one root who
    have hjoining :=
      abs_quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
        reward root who hreward
    have hjoiningUpper :
        quittingOutsiderJoiningContribution reward root who ≤
          2 * M * opponentMass := by
      exact (le_abs_self _).trans (by simpa [opponentMass] using hjoining)
    have hdecomposition :=
      quittingRootEndpointDifference_eq_outsiderNever reward tail root who
    rw [show quittingRootAbsorptionMass
        (Function.update root who (PMF.pure false)) = opponentMass by rfl]
      at hdecomposition
    have hsurvivalNonneg : 0 ≤ 1 - opponentMass := by linarith
    have hweightedGap : (1 - opponentMass) * (delta / 2) ≤
        (1 - opponentMass) *
          (tail who - reward (quittingSingletonTerminal who) who) :=
      mul_le_mul_of_nonneg_left (hgap who) hsurvivalNonneg
    have hthresholdIdentity :
        delta / (2 * (delta + 4 * M)) * (delta / 2 + 2 * M) =
          delta / 4 := by
      have hdenom : delta + 4 * M ≠ 0 := by positivity
      field_simp
      ring
    have hendpoint :
        quittingRootEndpointDifference reward tail root who ≤ -delta / 4 := by
      rw [show reward (quittingSingletonTerminal who) who - tail who =
          -(tail who - reward (quittingSingletonTerminal who) who) by ring]
        at hdecomposition
      have hfactorNonneg : 0 ≤ delta / 2 + 2 * M := by positivity
      have hthresholdProduct : opponentMass * (delta / 2 + 2 * M) ≤
          delta / 4 := by
        calc
          opponentMass * (delta / 2 + 2 * M) ≤
              delta / (2 * (delta + 4 * M)) * (delta / 2 + 2 * M) :=
            mul_le_mul_of_nonneg_right hopponentLe hfactorNonneg
          _ = delta / 4 := hthresholdIdentity
      nlinarith [hdecomposition, hjoiningUpper, hweightedGap]
    rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart,
      max_eq_right (by linarith :
        quittingRootEndpointDifference reward tail root who ≤ 0),
      max_eq_left (by linarith :
        0 ≤ -quittingRootEndpointDifference reward tail root who)]
    simp only [mul_zero, zero_add, quittingRootQuitRates]
    have hquitNonneg : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
    have hmul := mul_le_mul_of_nonneg_left
      (show delta / 4 ≤
        -quittingRootEndpointDifference reward tail root who by linarith)
      hquitNonneg
    nlinarith
  have hsum : delta / 4 * ∑ who, quittingRootQuitRates root who ≤
      quittingRootTotalNashDefect reward tail root := by
    unfold quittingRootTotalNashDefect
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun who _ => hcoordinate who
  exact (mul_le_mul_of_nonneg_left
      (quittingRootAbsorptionMass_le_sum_quitRates root)
      (by positivity : 0 ≤ delta / 4)).trans hsum

omit [Nonempty ι] in
/-- A compact strict all-Continue basin has one open neighborhood and one
positive linear absorption-to-defect modulus valid at every root scale. -/
theorem exists_open_linearAbsorptionDefect_of_compact_strictAllContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (K : Set (Payoff ι)) {M delta : ℝ}
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hM : 0 ≤ M) (hdelta : 0 < delta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hgap : ∀ tail ∈ K, ∀ who,
      delta ≤ tail who - reward (quittingSingletonTerminal who) who)
    (hunique : ∀ tail ∈ K, ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ (N : Set (Payoff ι)) (c : ℝ),
      IsOpen N ∧ K ⊆ N ∧ 0 < c ∧
      ∀ tail ∈ N, ∀ root : ι → PMF Bool,
        c * quittingRootAbsorptionMass root ≤
          quittingRootTotalNashDefect reward tail root := by
  let threshold := delta / (2 * (delta + 4 * M))
  have hthresholdPos : 0 < threshold := by
    dsimp only [threshold]
    positivity
  let gapNeighborhood : Set (Payoff ι) :=
    {tail | ∀ who, delta / 2 < tail who -
      reward (quittingSingletonTerminal who) who}
  have hgapNeighborhoodOpen : IsOpen gapNeighborhood := by
    rw [show gapNeighborhood = ⋂ who, {tail : Payoff ι |
        delta / 2 < tail who -
          reward (quittingSingletonTerminal who) who} by
      ext tail
      simp only [gapNeighborhood, mem_iInter, mem_setOf_eq]]
    apply isOpen_iInter_of_finite
    intro who
    exact isOpen_lt continuous_const ((continuous_apply who).sub continuous_const)
  have hKgap : K ⊆ gapNeighborhood := by
    intro tail htail who
    linarith [hgap tail htail who, hdelta]
  let highAbsorption : Set (QuittingRootSimplex ι) :=
    {root | threshold ≤
      quittingRootAbsorptionMass (quittingRootOfSimplex root)}
  have hhighClosed : IsClosed highAbsorption :=
    isClosed_Ici.preimage continuous_quittingRootAbsorptionMass_simplex
  have hhighCompact : IsCompact highAbsorption := hhighClosed.isCompact
  by_cases hhighNonempty : highAbsorption.Nonempty
  · let domain : Set (Payoff ι × QuittingRootSimplex ι) :=
      K ×ˢ highAbsorption
    have hdomainCompact : IsCompact domain := hKcompact.prod hhighCompact
    have hdomainNonempty : domain.Nonempty := hKnonempty.prod hhighNonempty
    let defect : Payoff ι × QuittingRootSimplex ι → ℝ := fun point =>
      quittingRootTotalNashDefect reward point.1
        (quittingRootOfSimplex point.2)
    have hdefectContinuous : Continuous defect :=
      continuous_quittingRootTotalNashDefect_simplex reward
    obtain ⟨selected, hselectedDomain, hselectedMin⟩ :=
      hdomainCompact.exists_isMinOn hdomainNonempty
        hdefectContinuous.continuousOn
    have hselectedNonneg : 0 ≤ defect selected :=
      quittingRootTotalNashDefect_nonneg reward selected.1
        (quittingRootOfSimplex selected.2)
    have hselectedPositive : 0 < defect selected := by
      apply lt_of_le_of_ne hselectedNonneg
      intro hzero
      have hnash : IsεQuittingRootNash reward selected.1 0
          (quittingRootOfSimplex selected.2) :=
        (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
          reward selected.1 (quittingRootOfSimplex selected.2)).2 hzero.symm
      have hroot := hunique selected.1 hselectedDomain.1
        (quittingRootOfSimplex selected.2) hnash
      have hhigh := hselectedDomain.2
      change threshold ≤ quittingRootAbsorptionMass
        (quittingRootOfSimplex selected.2) at hhigh
      rw [hroot, quittingRootAbsorptionMass_allContinueRoot] at hhigh
      linarith
    let moat := defect selected / 2
    let bad : Set (Payoff ι × QuittingRootSimplex ι) :=
      {point | threshold ≤
          quittingRootAbsorptionMass (quittingRootOfSimplex point.2) ∧
        quittingRootTotalNashDefect reward point.1
            (quittingRootOfSimplex point.2) ≤ moat}
    have hbadClosed : IsClosed bad := by
      exact (isClosed_le continuous_const
        (continuous_quittingRootAbsorptionMass_simplex.comp continuous_snd)).inter
        (isClosed_le (continuous_quittingRootTotalNashDefect_simplex reward)
          continuous_const)
    have hprojectionClosed : IsClosed (Prod.fst '' bad) :=
      isClosedMap_fst_of_compactSpace bad hbadClosed
    have hKnotBad : ∀ tail ∈ K, tail ∉ Prod.fst '' bad := by
      intro tail htail
      rintro ⟨⟨_nearbyTail, root⟩, hrootBad, rfl⟩
      have hlower := hselectedMin ⟨htail, hrootBad.1⟩
      change defect selected ≤
        quittingRootTotalNashDefect reward _nearbyTail
          (quittingRootOfSimplex root) at hlower
      have hupper : quittingRootTotalNashDefect reward _nearbyTail
          (quittingRootOfSimplex root) ≤ defect selected / 2 := by
        simpa only [moat] using hrootBad.2
      linarith
    let N := gapNeighborhood ∩ (Prod.fst '' bad)ᶜ
    let c := min (delta / 4) moat
    refine ⟨N, c, hgapNeighborhoodOpen.inter hprojectionClosed.isOpen_compl,
      ?_, ?_, ?_⟩
    · intro tail htail
      exact ⟨hKgap htail, hKnotBad tail htail⟩
    · dsimp only [c, moat]
      exact lt_min (by positivity) (by linarith)
    · intro tail htail root
      by_cases hsmall : quittingRootAbsorptionMass root ≤ threshold
      · have hlow :=
          quarterGap_mul_absorptionMass_le_totalNashDefect_of_smallAbsorption
            reward tail root hM hdelta hreward
              (fun who => le_of_lt (htail.1 who)) (by
                simpa only [threshold] using hsmall)
        exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
          (quittingRootAbsorptionMass_nonneg root)).trans hlow
      · have hhigh : threshold ≤ quittingRootAbsorptionMass root :=
          le_of_lt (lt_of_not_ge hsmall)
        let simplexRoot : QuittingRootSimplex ι := fun who =>
          stdSimplexEquiv (root who)
        have hsimplexRoot : quittingRootOfSimplex simplexRoot = root := by
          funext who
          exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)
        have hnotBad : tail ∉ Prod.fst '' bad := htail.2
        have hmoatLt : moat < quittingRootTotalNashDefect reward tail root := by
          apply lt_of_not_ge
          intro hdefect
          apply hnotBad
          refine ⟨(tail, simplexRoot), ?_, rfl⟩
          exact ⟨by simpa [hsimplexRoot] using hhigh,
            by simpa [hsimplexRoot] using hdefect⟩
        have hcLeMoat : c ≤ moat := min_le_right _ _
        have habsorptionLeOne := quittingRootAbsorptionMass_le_one root
        have hcNonneg : 0 ≤ c := le_of_lt (lt_min
          (by positivity : 0 < delta / 4)
          (by dsimp only [moat]; linarith))
        calc
          c * quittingRootAbsorptionMass root ≤ c * 1 :=
            mul_le_mul_of_nonneg_left habsorptionLeOne hcNonneg
          _ = c := mul_one c
          _ ≤ moat := hcLeMoat
          _ ≤ quittingRootTotalNashDefect reward tail root := hmoatLt.le
  · refine ⟨gapNeighborhood, delta / 4, hgapNeighborhoodOpen, hKgap,
      by positivity, ?_⟩
    intro tail htail root
    have hsmall : quittingRootAbsorptionMass root ≤ threshold := by
      apply le_of_not_gt
      intro hhigh
      let simplexRoot : QuittingRootSimplex ι := fun who =>
        stdSimplexEquiv (root who)
      have hsimplexRoot : quittingRootOfSimplex simplexRoot = root := by
        funext who
        exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)
      exact hhighNonempty ⟨simplexRoot, by
        change threshold ≤ quittingRootAbsorptionMass
          (quittingRootOfSimplex simplexRoot)
        rw [hsimplexRoot]
        exact hhigh.le⟩
    exact quarterGap_mul_absorptionMass_le_totalNashDefect_of_smallAbsorption
      reward tail root hM hdelta hreward
        (fun who => le_of_lt (htail who)) (by
          simpa only [threshold] using hsmall)

omit [Nonempty ι] in
/-- The linear basin can be chosen as a bounded metric thickening of the
compact source set.  One positive constant then bounds both the reward table
and every tail coordinate in the basin. -/
theorem exists_bounded_open_linearAbsorptionDefect_of_compact_strictAllContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (K : Set (Payoff ι)) {M delta : ℝ}
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hM : 0 ≤ M) (hdelta : 0 < delta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hgap : ∀ tail ∈ K, ∀ who,
      delta ≤ tail who - reward (quittingSingletonTerminal who) who)
    (hunique : ∀ tail ∈ K, ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ (N : Set (Payoff ι)) (c C rho : ℝ),
      IsOpen N ∧ K ⊆ N ∧ Bornology.IsBounded N ∧
      0 < c ∧ 0 < C ∧ 0 < rho ∧
      (∀ S player, |reward S player| ≤ C) ∧
      (∀ tail ∈ N, ∀ player, |tail player| ≤ C) ∧
      Metric.thickening rho K ⊆ N ∧
      ∀ tail ∈ N, ∀ root : ι → PMF Bool,
        c * quittingRootAbsorptionMass root ≤
          quittingRootTotalNashDefect reward tail root := by
  obtain ⟨ambient, c, hambientOpen, hKambient, hc, hlinear⟩ :=
    exists_open_linearAbsorptionDefect_of_compact_strictAllContinue
      reward K hKcompact hKnonempty hM hdelta hreward hgap hunique
  obtain ⟨rho, hrho, hthickAmbient⟩ :=
    hKcompact.exists_thickening_subset_open hambientOpen hKambient
  let N := Metric.thickening rho K
  have hNopen : IsOpen N := Metric.isOpen_thickening
  have hKN : K ⊆ N := by
    intro tail htail
    exact Metric.mem_thickening_iff.mpr
      ⟨tail, htail, by simpa using hrho⟩
  have hNbounded : Bornology.IsBounded N := hKcompact.isBounded.thickening
  obtain ⟨R, hNR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Payoff ι)).mp hNbounded
  obtain ⟨selected, hselectedK⟩ := hKnonempty
  have hselectedN : selected ∈ N := hKN hselectedK
  have hR : 0 ≤ R := by
    have hselectedBall := hNR hselectedN
    exact (dist_nonneg.trans hselectedBall)
  let C := max 1 (max M R)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hMC : M ≤ C :=
    (le_max_left M R).trans (le_max_right 1 (max M R))
  have hRC : R ≤ C :=
    (le_max_right M R).trans (le_max_right 1 (max M R))
  have hrewardC : ∀ S player, |reward S player| ≤ C := by
    intro S player
    exact (hreward S player).trans hMC
  have htailC : ∀ tail ∈ N, ∀ player, |tail player| ≤ C := by
    intro tail htail player
    have htailBall := hNR htail
    have htailDist : dist tail (0 : Payoff ι) ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using htailBall
    have hcoordinate := (dist_pi_le_iff hR).mp htailDist player
    simpa [Real.dist_eq] using hcoordinate.trans hRC
  refine ⟨N, c, C, rho, hNopen, hKN, hNbounded, hc, hC, hrho,
    hrewardC, htailC, Subset.rfl, ?_⟩
  intro tail htail root
  exact hlinear tail (hthickAmbient htail) root

/-- A linear defect modulus converts an approximate root-Nash certificate
into a quantitative absorption bound. -/
theorem quittingRootAbsorptionMass_le_card_div_mul_of_linearDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) {c ε : ℝ}
    (hc : 0 < c) (hnash : IsεQuittingRootNash reward tail ε root)
    (hlinear : c * quittingRootAbsorptionMass root ≤
      quittingRootTotalNashDefect reward tail root) :
    quittingRootAbsorptionMass root ≤ Fintype.card ι / c * ε := by
  have hdefect :=
    quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
      reward tail root ε hnash
  rw [show Fintype.card ι / c * ε = (Fintype.card ι * ε) / c by
    field_simp]
  apply (le_div_iff₀ hc).2
  calc
    quittingRootAbsorptionMass root * c =
        c * quittingRootAbsorptionMass root := by ring
    _ ≤ quittingRootTotalNashDefect reward tail root := hlinear
    _ ≤ Fintype.card ι * ε := hdefect

/-- A finite family of local approximate roots pays aggregate absorption by
the sum, rather than the maximum, of its declared root errors. -/
theorem sum_quittingRootAbsorptionMass_le_card_div_mul_sum_error
    {κ : Type} [Fintype κ]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : κ → Payoff ι) (root : κ → ι → PMF Bool)
    (error : κ → ℝ) {c : ℝ} (hc : 0 < c)
    (hnash : ∀ index,
      IsεQuittingRootNash reward (tail index) (error index) (root index))
    (hlinear : ∀ index,
      c * quittingRootAbsorptionMass (root index) ≤
        quittingRootTotalNashDefect reward (tail index) (root index)) :
    (∑ index, quittingRootAbsorptionMass (root index)) ≤
      Fintype.card ι / c * ∑ index, error index := by
  calc
    (∑ index, quittingRootAbsorptionMass (root index)) ≤
        ∑ index, Fintype.card ι / c * error index :=
      Finset.sum_le_sum fun index _ =>
        quittingRootAbsorptionMass_le_card_div_mul_of_linearDefect
          reward (tail index) (root index) hc (hnash index) (hlinear index)
    _ = Fintype.card ι / c * ∑ index, error index := by
      rw [Finset.mul_sum]

/-- Bounded exact Bellman successors inherit the aggregate error control as
an aggregate coordinate-motion estimate. -/
theorem sum_abs_successorPayoff_sub_tail_le_of_linearDefect
    {κ : Type} [Fintype κ]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : κ → Payoff ι) (root : κ → ι → PMF Bool)
    (error : κ → ℝ) {C c : ℝ} (hc : 0 < c)
    (hreward : ∀ S player, |reward S player| ≤ C)
    (htail : ∀ index player, |tail index player| ≤ C)
    (hnash : ∀ index,
      IsεQuittingRootNash reward (tail index) (error index) (root index))
    (hlinear : ∀ index,
      c * quittingRootAbsorptionMass (root index) ≤
        quittingRootTotalNashDefect reward (tail index) (root index))
    (who : ι) :
    (∑ index, |quittingRootSuccessorPayoff reward
        (tail index) (root index) who - tail index who|) ≤
      (2 * C * Fintype.card ι / c) * ∑ index, error index := by
  have habsorptionSum :=
    sum_quittingRootAbsorptionMass_le_card_div_mul_sum_error
      reward tail root error hc hnash hlinear
  have hC : 0 ≤ C :=
    quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  calc
    (∑ index, |quittingRootSuccessorPayoff reward
        (tail index) (root index) who - tail index who|) ≤
        ∑ index, 2 * C * quittingRootAbsorptionMass (root index) :=
      Finset.sum_le_sum fun index _ =>
        abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
          reward (tail index) (root index) who C hreward (htail index who)
    _ = 2 * C * ∑ index, quittingRootAbsorptionMass (root index) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * C * (Fintype.card ι / c * ∑ index, error index) :=
      mul_le_mul_of_nonneg_left habsorptionSum (by positivity)
    _ = (2 * C * Fintype.card ι / c) * ∑ index, error index := by ring

/-- Along any sequence of local approximate roots, declared error tending to
zero forces one-stage absorption to tend to zero. -/
theorem quittingRootAbsorptionMass_tendsto_zero_of_linearDefect
    {α : Type} {l : Filter α}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : α → Payoff ι) (root : α → ι → PMF Bool)
    (error : α → ℝ) {c : ℝ} (hc : 0 < c)
    (hnash : ∀ index,
      IsεQuittingRootNash reward (tail index) (error index) (root index))
    (hlinear : ∀ index,
      c * quittingRootAbsorptionMass (root index) ≤
        quittingRootTotalNashDefect reward (tail index) (root index))
    (herror : Tendsto error l (nhds 0)) :
    Tendsto (fun index => quittingRootAbsorptionMass (root index)) l
      (nhds 0) := by
  apply squeeze_zero
  · exact fun index => quittingRootAbsorptionMass_nonneg (root index)
  · exact fun index =>
      quittingRootAbsorptionMass_le_card_div_mul_of_linearDefect
        reward (tail index) (root index) hc (hnash index) (hlinear index)
  · simpa only [mul_zero] using herror.const_mul (Fintype.card ι / c)

end GameTheory
