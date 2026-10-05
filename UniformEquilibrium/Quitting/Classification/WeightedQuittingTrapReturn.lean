import UniformEquilibrium.Quitting.Classification.WeightedQuittingTrapLeavers

/-! # Actual weighted trap exclusion and singleton-sublevel return

The all-sure support is treated separately: multiplying endpoint gaps by
Continue probabilities would erase every comparison in that case.
-/

noncomputable section

namespace GameTheory

open Math.PMFProduct _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem trap_erase_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (active : Finset ι)
    (htrap : IsQuittingPremiumTrap reward active) (player : ι) (hplayer : player ∈ active) :
    (active.erase player).Nonempty := by
  by_contra hnot
  have heq : active = {player} := by
    ext who
    constructor
    · intro hwho
      by_cases heq : who = player
      · simp [heq]
      · exact False.elim (hnot ⟨who, Finset.mem_erase.mpr ⟨heq, hwho⟩⟩)
    · intro hwho
      simpa only [Finset.mem_singleton.mp hwho] using hplayer
  exact not_isQuittingPremiumTrap_singleton reward player (heq ▸ htrap)

/-- Erasing a nonsure active player leaves a positive full coalition atom,
even when every other active player quits surely. -/
theorem quittingRootCoalitionMass_erase_support_pos
    (root : ι → PMF Bool) (player : ι)
    (hcontinue : 0 < (root player false).toReal) :
    0 < quittingRootCoalitionMass root ((quittingPositiveHazardSupport root).erase player) := by
  unfold quittingRootCoalitionMass quittingRootQuitRates coalitionMass
  simp_rw [← pmfBool_false_toReal]
  apply mul_pos
  · apply Finset.prod_pos
    intro who hwho
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp hwho).2).2
  · apply Finset.prod_pos
    intro who hwho
    by_cases heq : who = player
    · simpa [heq] using hcontinue
    · have houtside : who ∉ quittingPositiveHazardSupport root := by
        intro hactive
        exact (Finset.mem_compl.mp hwho) (Finset.mem_erase.mpr ⟨heq, hactive⟩)
      rw [quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport root houtside]
      norm_num

/-- All active players quitting surely gives a deterministic coalition.
The full exact endpoint difference is its literal withdrawal toggle. -/
theorem quittingRootEndpointDifference_eq_toggle_of_sure_support
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool)
    (hsure : ∀ who ∈ quittingPositiveHazardSupport root, (root who true).toReal = 1)
    (player : ι) :
    quittingRootEndpointDifference reward tail root player =
      quittingEndpointInsertionToggle reward tail player
        ((quittingPositiveHazardSupport root).erase player) := by
  let action : ι → Bool := fun who => decide (who ∈ quittingPositiveHazardSupport root)
  have hroot : root = fun who => PMF.pure (action who) := by
    funext who
    by_cases hwho : who ∈ quittingPositiveHazardSupport root
    · simpa [action, hwho] using eq_pure_true_of_true_toReal_eq_one (root who) (hsure who hwho)
    · simpa [action, hwho] using
        quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport root hwho
  have hpayoff : ∀ choice : Bool,
      quittingRootExpectedPayoff reward tail (Function.update root player (PMF.pure choice))
        player = quittingStageCoalitionPayoff reward tail
          (if choice then insert player ((quittingPositiveHazardSupport root).erase player)
            else (quittingPositiveHazardSupport root).erase player) player := by
    intro choice
    have hupdate : Function.update root player (PMF.pure choice) =
        fun who => PMF.pure (Function.update action player choice who) := by
      rw [hroot]
      funext who
      by_cases heq : who = player <;> simp [heq]
    have hquitters : quittingQuitters (Function.update action player choice) =
        if choice then insert player ((quittingPositiveHazardSupport root).erase player)
          else (quittingPositiveHazardSupport root).erase player := by
      ext who
      cases choice <;> by_cases heq : who = player <;>
        simp [quittingQuitters, action, heq]
    unfold quittingRootExpectedPayoff
    rw [hupdate, pmfPi_pure, expect_pure,
      quittingRootPayoff_eq_stageCoalitionPayoff, hquitters]
  unfold quittingRootEndpointDifference quittingRootQuitPayoff quittingRootContinuePayoff
  rw [hpayoff true, hpayoff false]
  rfl

/-- The strict raw weighted tests exclude every trapped actual support at
sources in the canonical invariant region. Both hazard-boundary cases occur. -/
theorem not_premiumTrap_support_of_weighted_strictLeave
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hleavers : HasWeightedQuittingTrapLeavers reward (· < ·))
    (bound : ℝ) (tail : Payoff ι)
    (htail : tail ∈ quittingGlobalWeightedFloorBox reward bound)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root) :
    ¬IsQuittingPremiumTrap reward (quittingPositiveHazardSupport root) := by
  intro htrap
  let active := quittingPositiveHazardSupport root
  obtain ⟨weight, hpositive, houtside, hglobal, hleave⟩ := hleavers active htrap
  have hnonneg : ∀ player, 0 ≤ weight player := by
    intro player
    by_cases hplayer : player ∈ active
    · exact (hpositive player hplayer).le
    · rw [houtside player hplayer]
  have hcharge : (∑ player ∈ active, weight player *
      (reward (quittingSingletonTerminal player) player - tail player)) ≤ 0 := by
    have hfloor := htail.2 weight ⟨hnonneg, hglobal⟩
    have hsum : (∑ player, weight player *
        (tail player - reward (quittingSingletonTerminal player) player)) =
        ∑ player ∈ active, weight player *
          (tail player - reward (quittingSingletonTerminal player) player) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro player _ hnot
      simp [houtside player hnot]
    rw [hsum] at hfloor
    have hneg : (∑ player ∈ active, weight player *
        (reward (quittingSingletonTerminal player) player - tail player)) =
        -(∑ player ∈ active, weight player *
          (tail player - reward (quittingSingletonTerminal player) player)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro player _
      ring
    rw [hneg]
    exact neg_nonpos.mpr hfloor
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash
  have hgap : ∀ player ∈ active, 0 ≤ quittingRootEndpointDifference reward tail root player := by
    intro player hplayer
    exact nonneg_of_mul_nonneg_left
      (by simpa [hazardOfRoot, mul_comm] using (hendpoint player).2)
      ((Finset.mem_filter.mp hplayer).2)
  by_cases hsure : ∀ player ∈ active, (root player true).toReal = 1
  · obtain ⟨player, hplayer⟩ := htrap.1
    have hnonempty := trap_erase_nonempty reward active htrap player hplayer
    have hproper : active.erase player ⊂ active := Finset.erase_ssubset hplayer
    have hstrict := hleave (active.erase player) hnonempty hproper
    have hdiff : active \ active.erase player = {player} := by
      ext who
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
      aesop
    have hinsert : insert player (active.erase player) = active := Finset.insert_erase hplayer
    have hstrictToggle : weight player *
        quittingEndpointInsertionToggle reward tail player (active.erase player) < 0 := by
      rw [quittingEndpointInsertionToggle_of_nonempty reward tail player _ hnonempty]
      simpa [quittingWeightedLeaveSum, hdiff, hinsert] using hstrict
    have hgapEqual := quittingRootEndpointDifference_eq_toggle_of_sure_support
      reward tail root hsure player
    rw [← hgapEqual] at hstrictToggle
    exact (not_lt_of_ge (mul_nonneg (hpositive player hplayer).le (hgap player hplayer)))
      hstrictToggle
  · push Not at hsure
    obtain ⟨player, hplayer, hnotSure⟩ := hsure
    have hcontinue : 0 < (root player false).toReal := by
      have hsum := quittingRoot_continueProbability_add_quitProbability root player
      have hnonnegFalse := ENNReal.toReal_nonneg (a := root player false)
      rcases hnonnegFalse.eq_or_lt with hzero | hpos
      · exact False.elim (hnotSure (by linarith))
      · exact hpos
    have hnonempty := trap_erase_nonempty reward active htrap player hplayer
    have hproper : active.erase player ⊂ active := Finset.erase_ssubset hplayer
    have hnegative : (∑ coalition ∈ (active.powerset.erase ∅).erase active,
        quittingRootCoalitionMass root coalition *
          ∑ player ∈ active \ coalition,
            weight player * quittingEndpointInsertionToggle reward tail player coalition) < 0 := by
      have hterm : ∀ coalition ∈ (active.powerset.erase ∅).erase active,
          (∑ player ∈ active \ coalition,
            weight player * quittingEndpointInsertionToggle reward tail player coalition) < 0 := by
        intro coalition hcoalition
        have hnonemptyCoalition : coalition.Nonempty := Finset.nonempty_iff_ne_empty.mpr
          (Finset.mem_erase.mp (Finset.mem_erase.mp hcoalition).2).1
        have hproperCoalition : coalition ⊂ active :=
          Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp
              (Finset.mem_erase.mp hcoalition).2).2, (Finset.mem_erase.mp hcoalition).1⟩
        simp_rw [quittingEndpointInsertionToggle_of_nonempty reward tail _ _ hnonemptyCoalition]
        exact hleave coalition hnonemptyCoalition hproperCoalition
      apply Finset.sum_neg'
      · intro coalition hcoalition
        exact mul_nonpos_of_nonneg_of_nonpos
          (quittingRootCoalitionMass_nonneg root coalition) (hterm coalition hcoalition).le
      · refine ⟨active.erase player, ?_, ?_⟩
        · simp [Finset.nonempty_iff_ne_empty.mp hnonempty, hproper.ne,
            Finset.erase_subset]
        · exact mul_neg_of_pos_of_neg
            (quittingRootCoalitionMass_erase_support_pos root player hcontinue)
            (hterm _ (by simp [Finset.nonempty_iff_ne_empty.mp hnonempty,
              hproper.ne, Finset.erase_subset]))
    have hidentity := quittingWeightedEndpointGap_eq_continueCharge_add_properSubsetSum
      reward tail root active weight Finset.Subset.rfl
    have hleft : 0 ≤ ∑ player ∈ active, weight player * (root player false).toReal *
        quittingRootEndpointDifference reward tail root player := by
      exact Finset.sum_nonneg fun player hplayer =>
        mul_nonneg (mul_nonneg (hpositive player hplayer).le ENNReal.toReal_nonneg)
          (hgap player hplayer)
    have hfirst := mul_nonpos_of_nonneg_of_nonpos
      (quittingStationaryContinueMass_nonneg root) hcharge
    linarith

/-- Absorbing exact roots return to a singleton sublevel from the canonical
weighted source domain. No individual singleton floors are asserted. -/
theorem exists_successor_le_singleton_of_weighted_strictLeave
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hleavers : HasWeightedQuittingTrapLeavers reward (· < ·))
    (bound : ℝ) (tail : Payoff ι)
    (htail : tail ∈ quittingGlobalWeightedFloorBox reward bound)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
      reward (quittingSingletonTerminal player) player :=
  exists_successor_le_singleton_of_exactRoot_nontrap_support reward tail root hnash habsorption
    (not_premiumTrap_support_of_weighted_strictLeave reward hleavers bound tail htail root hnash)

end GameTheory
