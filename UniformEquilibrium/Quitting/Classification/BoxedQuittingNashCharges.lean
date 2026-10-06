import UniformEquilibrium.Quitting.Classification.WeightedQuittingTrapReturn

/-! # Literal boxed Nash-charge coefficient tests

The full-coalition identity is used before any odds division. Nonpositive
proper-subset leave sums and strict erased-support leave sums exclude every
sure active hazard, independently of source floors and inserted premiums.
Interior odds charges and the common-box return producer are separate units.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingTrapInsertedPremiumSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active coalition : Finset ι) : ℝ :=
  ∑ player ∈ active \ coalition,
    (reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player -
      reward (quittingSingletonTerminal player) player)

def quittingTrapLeaveSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (coalition : {S : Finset ι // S.Nonempty}) : ℝ :=
  quittingWeightedLeaveSum reward active (fun _ => 1) coalition

/-- The literal three cardinality ranges, including an empty middle range. -/
structure QuittingTrapChargeCoefficients
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (active : Finset ι) where
  delta : ℝ
  tau : ℝ
  gap : ℝ
  loss : ℝ
  delta_pos : 0 < delta
  tau_pos : 0 < tau
  gap_pos : 0 < gap
  loss_pos : 0 < loss
  card_ge_three : 3 ≤ active.card
  singleton : ∀ (coalition : Finset ι) (hne : coalition.Nonempty),
    coalition ⊂ active → coalition.card = 1 →
      quittingTrapInsertedPremiumSum reward active coalition ≤ -delta ∧
        quittingTrapLeaveSum reward active ⟨coalition, hne⟩ ≤ -gap
  middle : ∀ (coalition : Finset ι) (hne : coalition.Nonempty),
    coalition ⊂ active → 2 ≤ coalition.card → coalition.card ≤ active.card - 2 →
      quittingTrapInsertedPremiumSum reward active coalition ≤ 0 ∧
        quittingTrapLeaveSum reward active ⟨coalition, hne⟩ ≤ 0
  penultimate : ∀ (coalition : Finset ι) (hne : coalition.Nonempty),
    coalition ⊂ active → coalition.card = active.card - 1 →
      quittingTrapInsertedPremiumSum reward active coalition ≤ tau ∧
        quittingTrapLeaveSum reward active ⟨coalition, hne⟩ ≤ -loss

omit [Fintype ι] in
theorem QuittingTrapChargeCoefficients.leave_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (active : Finset ι)
    (coefficients : QuittingTrapChargeCoefficients reward active)
    (coalition : Finset ι) (hne : coalition.Nonempty) (hproper : coalition ⊂ active) :
    quittingTrapLeaveSum reward active ⟨coalition, hne⟩ ≤ 0 := by
  by_cases hsingle : coalition.card = 1
  · exact ((coefficients.singleton coalition hne hproper hsingle).2).trans
      (neg_nonpos.mpr coefficients.gap_pos.le)
  by_cases hlast : coalition.card = active.card - 1
  · exact ((coefficients.penultimate coalition hne hproper hlast).2).trans
      (neg_nonpos.mpr coefficients.loss_pos.le)
  have hpositive := Finset.card_pos.mpr hne
  have hless := Finset.card_lt_card hproper
  exact (coefficients.middle coalition hne hproper (by omega) (by omega)).2

/-- The canonical full-cube identity specialized to unit weights.
No odds, nonzero probabilities, source floors or Nash premise are needed. -/
theorem quittingTrapEndpointGap_eq_continueCharge_add_leaveSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) :
    (∑ player ∈ quittingPositiveHazardSupport root, (root player false).toReal *
        quittingRootEndpointDifference reward tail root player) =
      quittingStationaryContinueMass root *
        (∑ player ∈ quittingPositiveHazardSupport root,
          (reward (quittingSingletonTerminal player) player - tail player)) +
      ∑ coalition ∈ ((quittingPositiveHazardSupport root).powerset.erase ∅).erase
          (quittingPositiveHazardSupport root),
        quittingRootCoalitionMass root coalition *
          ∑ player ∈ quittingPositiveHazardSupport root \ coalition,
            quittingEndpointInsertionToggle reward tail player coalition := by
  simpa only [one_mul] using
    quittingWeightedEndpointGap_eq_continueCharge_add_properSubsetSum reward tail root
      (quittingPositiveHazardSupport root) (fun _ => 1) Finset.Subset.rfl

/-- Only leave-coefficient hypotheses belong to the sure-hazard exclusion.
The all-sure profile requires its separate profitable-withdrawal comparison. -/
theorem quittingRoot_activeHazards_lt_one_of_leave_sums
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hcard : 2 ≤ (quittingPositiveHazardSupport root).card)
    (hleave : ∀ (coalition : Finset ι) (hne : coalition.Nonempty),
      coalition ⊂ quittingPositiveHazardSupport root →
        quittingTrapLeaveSum reward (quittingPositiveHazardSupport root) ⟨coalition, hne⟩ ≤ 0)
    (herase : ∀ (player : ι) (_ : player ∈ quittingPositiveHazardSupport root)
      (hne : ((quittingPositiveHazardSupport root).erase player).Nonempty),
      quittingTrapLeaveSum reward (quittingPositiveHazardSupport root)
        ⟨(quittingPositiveHazardSupport root).erase player, hne⟩ < 0) :
    ∀ player ∈ quittingPositiveHazardSupport root, (root player true).toReal < 1 := by
  let active := quittingPositiveHazardSupport root
  change 2 ≤ active.card at hcard
  have hnonempty : ∀ player ∈ active, (active.erase player).Nonempty := by
    intro player hplayer
    apply Finset.card_pos.mp
    have hcount := Finset.card_erase_of_mem hplayer
    omega
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash
  have hgap : ∀ player ∈ active, 0 ≤ quittingRootEndpointDifference reward tail root player := by
    intro player hplayer
    exact nonneg_of_mul_nonneg_left
      (by simpa [hazardOfRoot, mul_comm] using (hendpoint player).2)
      ((Finset.mem_filter.mp hplayer).2)
  intro surePlayer hsurePlayer
  by_contra hnot
  have hsurePlayerQuit : (root surePlayer true).toReal = 1 := by
    apply le_antisymm _ (not_lt.mp hnot)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (root surePlayer) true)
  have hzero : quittingStationaryContinueMass root = 0 := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    apply Finset.prod_eq_zero (Finset.mem_univ surePlayer)
    have hsum := quittingRoot_continueProbability_add_quitProbability root surePlayer
    linarith
  by_cases hallSure : ∀ player ∈ active, (root player true).toReal = 1
  · have hne := hnonempty surePlayer hsurePlayer
    have hstrict := herase surePlayer hsurePlayer hne
    change quittingTrapLeaveSum reward active ⟨active.erase surePlayer, hne⟩ < 0 at hstrict
    have hdifference : active \ active.erase surePlayer = {surePlayer} := by
      ext who
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
      aesop
    have htoggle : quittingEndpointInsertionToggle reward tail surePlayer
        (active.erase surePlayer) < 0 := by
      rw [quittingEndpointInsertionToggle_of_nonempty reward tail surePlayer _ hne]
      simpa only [quittingTrapLeaveSum, quittingWeightedLeaveSum, hdifference,
        Finset.sum_singleton, one_mul] using hstrict
    have hequal := quittingRootEndpointDifference_eq_toggle_of_sure_support
      reward tail root hallSure surePlayer
    rw [← hequal] at htoggle
    exact (not_lt_of_ge (hgap surePlayer hsurePlayer)) htoggle
  · push Not at hallSure
    obtain ⟨player, hplayer, hnotSure⟩ := hallSure
    have hcontinue : 0 < (root player false).toReal := by
      have hsum := quittingRoot_continueProbability_add_quitProbability root player
      have hnonnegative := ENNReal.toReal_nonneg (a := root player false)
      rcases hnonnegative.eq_or_lt with hzero | hpos
      · exact False.elim (hnotSure (by linarith))
      · exact hpos
    have hne := hnonempty player hplayer
    have hproper := Finset.erase_ssubset hplayer
    have hnegative : (∑ coalition ∈ (active.powerset.erase ∅).erase active,
        quittingRootCoalitionMass root coalition *
          ∑ who ∈ active \ coalition,
            quittingEndpointInsertionToggle reward tail who coalition) < 0 := by
      have hterm : ∀ coalition ∈ (active.powerset.erase ∅).erase active,
          (∑ who ∈ active \ coalition,
            quittingEndpointInsertionToggle reward tail who coalition) ≤ 0 := by
        intro coalition hcoalition
        have hneCoalition : coalition.Nonempty := Finset.nonempty_iff_ne_empty.mpr
          (Finset.mem_erase.mp (Finset.mem_erase.mp hcoalition).2).1
        have hproperCoalition : coalition ⊂ active :=
          Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp
              (Finset.mem_erase.mp hcoalition).2).2, (Finset.mem_erase.mp hcoalition).1⟩
        simp_rw [quittingEndpointInsertionToggle_of_nonempty reward tail _ _ hneCoalition]
        simpa [quittingTrapLeaveSum, quittingWeightedLeaveSum] using
          hleave coalition hneCoalition hproperCoalition
      apply Finset.sum_neg'
      · intro coalition hcoalition
        exact mul_nonpos_of_nonneg_of_nonpos
          (quittingRootCoalitionMass_nonneg root coalition) (hterm coalition hcoalition)
      · refine ⟨active.erase player, ?_, ?_⟩
        · simp [Finset.nonempty_iff_ne_empty.mp hne, hproper.ne, Finset.erase_subset]
        · apply mul_neg_of_pos_of_neg
            (quittingRootCoalitionMass_erase_support_pos root player hcontinue)
          simp_rw [quittingEndpointInsertionToggle_of_nonempty reward tail _ _ hne]
          simpa [quittingTrapLeaveSum, quittingWeightedLeaveSum] using herase player hplayer hne
    have hidentity := quittingTrapEndpointGap_eq_continueCharge_add_leaveSum reward tail root
    rw [hzero, zero_mul, zero_add] at hidentity
    have hleft : 0 ≤ ∑ player ∈ active, (root player false).toReal *
        quittingRootEndpointDifference reward tail root player :=
      Finset.sum_nonneg fun player hplayer => mul_nonneg ENNReal.toReal_nonneg
        (hgap player hplayer)
    linarith

theorem QuittingTrapChargeCoefficients.activeHazards_lt_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (coefficients : QuittingTrapChargeCoefficients reward (quittingPositiveHazardSupport root))
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    ∀ player ∈ quittingPositiveHazardSupport root, (root player true).toReal < 1 := by
  apply quittingRoot_activeHazards_lt_one_of_leave_sums reward tail root hnash
    (by have h := coefficients.card_ge_three; omega)
    (coefficients.leave_nonpos reward _)
  intro player hplayer hne
  exact lt_of_le_of_lt
    (coefficients.penultimate _ hne (Finset.erase_ssubset hplayer)
      (Finset.card_erase_of_mem hplayer)).2 (neg_neg_of_pos coefficients.loss_pos)

end GameTheory
