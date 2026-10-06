import UniformEquilibrium.Quitting.Classification.BoxedQuittingNashCharges
import UniformEquilibrium.Quitting.Root.InteriorCoalitionOdds
import MathUE.FiniteNextToTopSymmetricMean

/-! # Actual interior odds polynomials for boxed Nash charges

Raw leave tests first establish global positive Continue mass. The two
polynomials below retain all nonempty proper support coalitions. The positive
inserted-premium polynomial and the exact source-charge equality are produced
from actual endpoint Nash, not supplied polynomial or root certificates.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingTrapOddsPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool) : ℝ :=
  ∑ coalition ∈ ((quittingPositiveHazardSupport root).powerset.erase ∅).erase
      (quittingPositiveHazardSupport root),
    (∏ player ∈ coalition, quittingRootOdds root player) *
      quittingTrapInsertedPremiumSum reward (quittingPositiveHazardSupport root) coalition

def quittingTrapOddsLeave
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) : ℝ :=
  ∑ coalition ∈ ((quittingPositiveHazardSupport root).powerset.erase ∅).erase
      (quittingPositiveHazardSupport root),
    (∏ player ∈ coalition, quittingRootOdds root player) *
      ∑ player ∈ quittingPositiveHazardSupport root \ coalition,
        quittingEndpointInsertionToggle reward tail player coalition

theorem QuittingTrapChargeCoefficients.continue_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (coefficients : QuittingTrapChargeCoefficients reward (quittingPositiveHazardSupport root))
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    ∀ player, 0 < (root player false).toReal := by
  intro player
  by_cases hactive : player ∈ quittingPositiveHazardSupport root
  · have hless := coefficients.activeHazards_lt_one reward tail root hnash player hactive
    have hsum := quittingRoot_continueProbability_add_quitProbability root player
    linarith
  · rw [quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport root hactive]
    norm_num

theorem QuittingTrapChargeCoefficients.odds_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (coefficients : QuittingTrapChargeCoefficients reward (quittingPositiveHazardSupport root))
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (player : ι) (hplayer : player ∈ quittingPositiveHazardSupport root) :
    0 < quittingRootOdds root player :=
  div_pos (Finset.mem_filter.mp hplayer).2
    (coefficients.continue_pos reward tail root hnash player)

theorem quittingContinuePremiumSum_eq_continueMass_mul_oddsPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (hcontinue : ∀ player, 0 < (root player false).toReal) :
    (∑ player ∈ quittingPositiveHazardSupport root, (root player false).toReal *
        (quittingRootQuitPayoff reward tail root player -
          reward (quittingSingletonTerminal player) player)) =
      quittingStationaryContinueMass root * quittingTrapOddsPremium reward root := by
  rw [quittingContinuePremiumSum_eq_properSubsetPremiumSum reward tail root
    (quittingPositiveHazardSupport root) Finset.Subset.rfl]
  unfold quittingTrapOddsPremium quittingTrapInsertedPremiumSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coalition _
  rw [quittingRootCoalitionMass_eq_continueMass_mul_prod_odds root hcontinue coalition]
  ring

/-- Favorable active Quit endpoints force a positive actual odds polynomial. -/
theorem quittingTrapOddsPremium_pos_of_active_quitPayoff_gt_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (coefficients : QuittingTrapChargeCoefficients reward (quittingPositiveHazardSupport root))
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hhigh : ∀ player ∈ quittingPositiveHazardSupport root,
      reward (quittingSingletonTerminal player) player < quittingRootQuitPayoff reward tail root
        player) :
    0 < quittingTrapOddsPremium reward root := by
  have hcontinue := coefficients.continue_pos reward tail root hnash
  have hnonempty : (quittingPositiveHazardSupport root).Nonempty :=
    Finset.card_pos.mp (by have h := coefficients.card_ge_three; omega)
  have hpositive : 0 < ∑ player ∈ quittingPositiveHazardSupport root,
      (root player false).toReal * (quittingRootQuitPayoff reward tail root player -
        reward (quittingSingletonTerminal player) player) :=
    Finset.sum_pos (fun player hplayer =>
      mul_pos (hcontinue player) (sub_pos.mpr (hhigh player hplayer))) hnonempty
  rw [quittingContinuePremiumSum_eq_continueMass_mul_oddsPremium reward tail root hcontinue]
    at hpositive
  exact pos_of_mul_pos_right hpositive
    (quittingStationaryContinueMass_pos_of_continue_pos root hcontinue).le

/-- The exact source charge is the negative leave polynomial at an actual
interior endpoint Nash root. No singleton or annotation sign is assumed. -/
theorem singletonSourceCharge_eq_neg_oddsLeave_of_chargeCoefficients
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (coefficients : QuittingTrapChargeCoefficients reward (quittingPositiveHazardSupport root))
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    (∑ player ∈ quittingPositiveHazardSupport root,
      (reward (quittingSingletonTerminal player) player - tail player)) =
        -quittingTrapOddsLeave reward tail root := by
  have hcontinue := coefficients.continue_pos reward tail root hnash
  have hmass := quittingStationaryContinueMass_pos_of_continue_pos root hcontinue
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash
  have hzero : (∑ player ∈ quittingPositiveHazardSupport root,
      (root player false).toReal * quittingRootEndpointDifference reward tail root player) = 0 := by
    apply Finset.sum_eq_zero
    intro player hplayer
    rw [quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
      reward tail root player hendpoint (hcontinue player) (Finset.mem_filter.mp hplayer).2,
      mul_zero]
  have hsum : (∑ coalition ∈ ((quittingPositiveHazardSupport root).powerset.erase ∅).erase
        (quittingPositiveHazardSupport root),
      quittingRootCoalitionMass root coalition *
        ∑ player ∈ quittingPositiveHazardSupport root \ coalition,
          quittingEndpointInsertionToggle reward tail player coalition) =
      quittingStationaryContinueMass root * quittingTrapOddsLeave reward tail root := by
    unfold quittingTrapOddsLeave
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coalition _
    rw [quittingRootCoalitionMass_eq_continueMass_mul_prod_odds root hcontinue coalition]
    ring
  have hidentity := quittingTrapEndpointGap_eq_continueCharge_add_leaveSum reward tail root
  rw [hzero, hsum] at hidentity
  nlinarith

omit [Fintype ι] in
/-- The raw cardinality tests bound the entire inserted-premium polynomial.
All intermediate layers are retained with their nonpositive coefficients. -/
theorem QuittingTrapChargeCoefficients.premiumPolynomial_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (active : Finset ι)
    (coefficients : QuittingTrapChargeCoefficients reward active)
    (coordinates : ι → ℝ) (hnonnegative : ∀ player ∈ active, 0 ≤ coordinates player) :
    (∑ coalition ∈ (active.powerset.erase ∅).erase active,
      (∏ player ∈ coalition, coordinates player) *
        quittingTrapInsertedPremiumSum reward active coalition) ≤
      -coefficients.delta * (∑ player ∈ active, coordinates player) +
        coefficients.tau * Math.NextToTopSymmetric.value active coordinates := by
  let carrier := (active.powerset.erase ∅).erase active
  have hcard := coefficients.card_ge_three
  have hbound : ∀ coalition ∈ carrier, quittingTrapInsertedPremiumSum reward active coalition ≤
      (if coalition.card = 1 then -coefficients.delta else 0) +
        (if coalition.card = active.card - 1 then coefficients.tau else 0) := by
    intro coalition hcoalition
    have hne : coalition.Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (Finset.mem_erase.mp (Finset.mem_erase.mp hcoalition).2).1
    have hproper : coalition ⊂ active := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp
        (Finset.mem_erase.mp hcoalition).2).2, (Finset.mem_erase.mp hcoalition).1⟩
    by_cases hsingle : coalition.card = 1
    · have hlast : coalition.card ≠ active.card - 1 := by omega
      rw [ite_eq_left hsingle, ite_eq_right hlast, add_zero]
      exact (coefficients.singleton coalition hne hproper hsingle).1
    by_cases hlast : coalition.card = active.card - 1
    · rw [ite_eq_right hsingle, ite_eq_left hlast, zero_add]
      exact (coefficients.penultimate coalition hne hproper hlast).1
    · have hpositive := Finset.card_pos.mpr hne
      have hless := Finset.card_lt_card hproper
      simpa only [ite_eq_right hsingle, ite_eq_right hlast, zero_add] using
        (coefficients.middle coalition hne hproper (by omega) (by omega)).1
  exact Math.NextToTopSymmetric.sum_prod_coefficient_le_two_layers active (by omega)
    coordinates hnonnegative (quittingTrapInsertedPremiumSum reward active)
    (-coefficients.delta) coefficients.tau hbound

/-- The same cardinality-layer grouping bounds the signed leave polynomial
above by negative singleton and penultimate contributions. -/
theorem QuittingTrapChargeCoefficients.oddsLeave_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (coefficients : QuittingTrapChargeCoefficients reward (quittingPositiveHazardSupport root))
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    quittingTrapOddsLeave reward tail root ≤
      -coefficients.gap * (∑ player ∈ quittingPositiveHazardSupport root,
        quittingRootOdds root player) -
      coefficients.loss * Math.NextToTopSymmetric.value (quittingPositiveHazardSupport root)
        (quittingRootOdds root) := by
  let active := quittingPositiveHazardSupport root
  let coefficient : Finset ι → ℝ := fun coalition =>
    ∑ player ∈ active \ coalition, quittingEndpointInsertionToggle reward tail player coalition
  have hcard := coefficients.card_ge_three
  have hbound : ∀ coalition ∈ (active.powerset.erase ∅).erase active,
      coefficient coalition ≤ (if coalition.card = 1 then -coefficients.gap else 0) +
        (if coalition.card = active.card - 1 then -coefficients.loss else 0) := by
    intro coalition hcoalition
    have hne : coalition.Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (Finset.mem_erase.mp (Finset.mem_erase.mp hcoalition).2).1
    have hproper : coalition ⊂ active := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp
        (Finset.mem_erase.mp hcoalition).2).2, (Finset.mem_erase.mp hcoalition).1⟩
    have hequal : coefficient coalition = quittingTrapLeaveSum reward active ⟨coalition, hne⟩ := by
      simp only [coefficient, quittingTrapLeaveSum, quittingWeightedLeaveSum, one_mul]
      apply Finset.sum_congr rfl
      intro player _
      rw [quittingEndpointInsertionToggle_of_nonempty reward tail player coalition hne]
    rw [hequal]
    by_cases hsingle : coalition.card = 1
    · have hlast : coalition.card ≠ active.card - 1 := by
        change 3 ≤ active.card at hcard
        omega
      rw [ite_eq_left hsingle, ite_eq_right hlast, add_zero]
      exact (coefficients.singleton coalition hne hproper hsingle).2
    by_cases hlast : coalition.card = active.card - 1
    · rw [ite_eq_right hsingle, ite_eq_left hlast, zero_add]
      exact (coefficients.penultimate coalition hne hproper hlast).2
    · have hpositive := Finset.card_pos.mpr hne
      have hless := Finset.card_lt_card hproper
      change 3 ≤ active.card at hcard
      have hlower : 2 ≤ coalition.card := by omega
      have hupper : coalition.card ≤ active.card - 2 := by omega
      simpa only [ite_eq_right hsingle, ite_eq_right hlast, zero_add] using
        (coefficients.middle coalition hne hproper hlower hupper).2
  have hresult := Math.NextToTopSymmetric.sum_prod_coefficient_le_two_layers active
    (by change 3 ≤ active.card at hcard; omega) (quittingRootOdds root)
    (fun player hplayer => (coefficients.odds_pos reward tail root hnash player hplayer).le)
    coefficient (-coefficients.gap) (-coefficients.loss) hbound
  simpa only [quittingTrapOddsLeave, coefficient, active, sub_eq_add_neg, neg_mul] using hresult

theorem QuittingTrapChargeCoefficients.sourceCharge_ge_odds_layers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (coefficients : QuittingTrapChargeCoefficients reward (quittingPositiveHazardSupport root))
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    coefficients.gap * (∑ player ∈ quittingPositiveHazardSupport root,
        quittingRootOdds root player) +
      coefficients.loss * Math.NextToTopSymmetric.value (quittingPositiveHazardSupport root)
        (quittingRootOdds root) ≤
      ∑ player ∈ quittingPositiveHazardSupport root,
        (reward (quittingSingletonTerminal player) player - tail player) := by
  rw [singletonSourceCharge_eq_neg_oddsLeave_of_chargeCoefficients reward tail root
    coefficients hnash]
  have hbound := coefficients.oddsLeave_le reward tail root hnash
  linarith

theorem QuittingTrapChargeCoefficients.delta_mul_oddsSum_lt_tau_mul_symmetric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (coefficients : QuittingTrapChargeCoefficients reward (quittingPositiveHazardSupport root))
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hhigh : ∀ player ∈ quittingPositiveHazardSupport root,
      reward (quittingSingletonTerminal player) player < quittingRootQuitPayoff reward tail root
        player) :
    coefficients.delta * (∑ player ∈ quittingPositiveHazardSupport root,
        quittingRootOdds root player) <
      coefficients.tau * Math.NextToTopSymmetric.value (quittingPositiveHazardSupport root)
        (quittingRootOdds root) := by
  have hpositive := quittingTrapOddsPremium_pos_of_active_quitPayoff_gt_singleton
    reward tail root coefficients hnash hhigh
  have hbound := coefficients.premiumPolynomial_le reward _ (quittingRootOdds root)
    (fun player hplayer => (coefficients.odds_pos reward tail root hnash player hplayer).le)
  change quittingTrapOddsPremium reward root ≤ _ at hbound
  linarith

def QuittingTrapChargeCoefficients.threshold
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {active : Finset ι}
    (coefficients : QuittingTrapChargeCoefficients reward active) : ℝ :=
  (active.card : ℝ) * (coefficients.delta / coefficients.tau) ^
    ((active.card - 2 : ℕ) : ℝ)⁻¹ *
      (coefficients.gap + coefficients.loss * coefficients.delta / coefficients.tau)

/-- The literal Nash charge threshold is derived from actual supported
endpoint equations and favorable Quit endpoints, for arbitrary finite support. -/
theorem QuittingTrapChargeCoefficients.threshold_lt_singletonSourceCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (coefficients : QuittingTrapChargeCoefficients reward (quittingPositiveHazardSupport root))
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hhigh : ∀ player ∈ quittingPositiveHazardSupport root,
      reward (quittingSingletonTerminal player) player < quittingRootQuitPayoff reward tail root
        player) :
    coefficients.threshold < ∑ player ∈ quittingPositiveHazardSupport root,
      (reward (quittingSingletonTerminal player) player - tail player) := by
  let active := quittingPositiveHazardSupport root
  let total := ∑ player ∈ active, quittingRootOdds root player
  let symmetric := Math.NextToTopSymmetric.value active (quittingRootOdds root)
  have hnonnegative : ∀ player ∈ active, 0 ≤ quittingRootOdds root player :=
    fun player hplayer => (coefficients.odds_pos reward tail root hnash player hplayer).le
  have htotal : 0 < total := by
    apply Finset.sum_pos
    · exact fun player hplayer => coefficients.odds_pos reward tail root hnash player hplayer
    · apply Finset.card_pos.mp
      have hcard := coefficients.card_ge_three
      change 3 ≤ active.card at hcard
      omega
  have hmean := Math.NextToTopSymmetric.value_finset_le_sum_pow_div_card_pow active
    (quittingRootOdds root) coefficients.card_ge_three hnonnegative
  have hpremium := coefficients.delta_mul_oddsSum_lt_tau_mul_symmetric
    reward tail root hnash hhigh
  have hlower := Math.NextToTopSymmetric.card_mul_ratio_rpow_lt_total_of_symmetric_bound
    active.card coefficients.card_ge_three total symmetric coefficients.delta coefficients.tau
    htotal coefficients.delta_pos coefficients.tau_pos hmean hpremium
  have hratio : coefficients.delta / coefficients.tau * total < symmetric := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ coefficients.tau_pos).mpr
    simpa only [mul_comm] using hpremium
  have hfactor : 0 < coefficients.gap +
      coefficients.loss * coefficients.delta / coefficients.tau :=
    add_pos coefficients.gap_pos
      (div_pos (mul_pos coefficients.loss_pos coefficients.delta_pos) coefficients.tau_pos)
  have hcharge := coefficients.sourceCharge_ge_odds_layers reward tail root hnash
  have hmiddle : (coefficients.gap +
      coefficients.loss * coefficients.delta / coefficients.tau) * total <
      coefficients.gap * total + coefficients.loss * symmetric := by
    have hstrict := mul_lt_mul_of_pos_left hratio coefficients.loss_pos
    have hnormalize : coefficients.loss * (coefficients.delta / coefficients.tau * total) =
        coefficients.loss * coefficients.delta / coefficients.tau * total := by ring
    rw [hnormalize] at hstrict
    nlinarith
  have hstrict := mul_lt_mul_of_pos_right hlower hfactor
  have hmiddle' : total * (coefficients.gap +
      coefficients.loss * coefficients.delta / coefficients.tau) <
      coefficients.gap * total + coefficients.loss * symmetric := by
    simpa only [mul_comm] using hmiddle
  unfold QuittingTrapChargeCoefficients.threshold
  exact hstrict.trans (hmiddle'.trans_le hcharge)

end GameTheory
