import UniformEquilibrium.Diagnostics.Quitting.OneDateProductRootCaps
import MathUE.PMFProduct.FiniteFubini

/-!
# Literal singleton and timing boundaries for root screening

Only player two's own-singleton reward varies. Two sure opponents at date zero
screen it from the complete cap, but one all-Continue padding row restores it.
With only player two quitting surely, even the unpadded Quit endpoint is the
varying singleton. These are complete-table boundary examples, not minimum sources.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

def membershipScreeningSingletonReward (singleton : ℝ)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) : ℝ :=
  if terminal.1 = {2} ∧ who = 2 then singleton else 0

def membershipScreeningTwoSureRoot : Fin 4 → PMF Bool :=
  fun player => PMF.pure (![true, true, false, false] player)

def membershipScreeningOneSureRoot : Fin 4 → PMF Bool :=
  fun player => PMF.pure (![false, false, true, false] player)

theorem membershipScreeningSingletonReward_eq_of_ne_ownSingleton
    (left right : ℝ) (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4)
    (hnot : terminal.1 ≠ {who}) :
    membershipScreeningSingletonReward left terminal who =
      membershipScreeningSingletonReward right terminal who := by
  unfold membershipScreeningSingletonReward
  split_ifs with h
  · obtain ⟨hterminal, hwho⟩ := h
    subst who
    exact (hnot hterminal).elim
  · rfl

theorem membershipScreeningSingletonReward_abs_le_one {singleton : ℝ}
    (hbound : |singleton| ≤ 1)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    |membershipScreeningSingletonReward singleton terminal who| ≤ 1 := by
  unfold membershipScreeningSingletonReward
  split_ifs
  · exact hbound
  · norm_num

theorem membershipScreeningSingletonReward_ownSingleton (singleton : ℝ) :
    membershipScreeningSingletonReward singleton (quittingSingletonTerminal 2) 2 = singleton := by
  simp +decide [membershipScreeningSingletonReward]

theorem membershipScreeningTwoSureRoot_endpoints (singleton : ℝ) :
    oneDateProductQuitEndpoint (membershipScreeningSingletonReward singleton)
      membershipScreeningTwoSureRoot 2 = 0 ∧
    oneDateProductContinueEndpoint (membershipScreeningSingletonReward singleton)
      membershipScreeningTwoSureRoot 2 = 0 := by
  constructor <;>
    simp +decide [oneDateProductQuitEndpoint, oneDateProductContinueEndpoint,
      quittingRootQuitPayoff, quittingRootContinuePayoff, quittingRootExpectedPayoff,
      expect_pmfPi_fin4, membershipScreeningTwoSureRoot, quittingRootPayoff,
      membershipScreeningSingletonReward, Function.update]

theorem membershipScreeningOneSureRoot_endpoints (singleton : ℝ) :
    oneDateProductQuitEndpoint (membershipScreeningSingletonReward singleton)
      membershipScreeningOneSureRoot 2 = singleton ∧
    oneDateProductContinueEndpoint (membershipScreeningSingletonReward singleton)
      membershipScreeningOneSureRoot 2 = 0 := by
  constructor <;>
    simp +decide [oneDateProductQuitEndpoint, oneDateProductContinueEndpoint,
      quittingRootQuitPayoff, quittingRootContinuePayoff, quittingRootExpectedPayoff,
      expect_pmfPi_fin4, membershipScreeningOneSureRoot, quittingRootPayoff,
      membershipScreeningSingletonReward, Function.update]

theorem membershipScreeningTwoSureRoot_unpadded_cap (singleton : ℝ) :
    quittingContinuationBestResponseValue (membershipScreeningSingletonReward singleton)
      (quittingOneDateThenNeverProfile (membershipScreeningSingletonReward singleton)
        membershipScreeningTwoSureRoot) 2 = 0 := by
  have hsure : (membershipScreeningTwoSureRoot 0 true).toReal = 1 := by
    simp [membershipScreeningTwoSureRoot]
  rw [oneDateProductQuittingContinuationBestResponseValue_oneDateThenNever_sureQuitter
    _ _ 2 (by decide : (0 : Fin 4) ≠ 2) hsure,
    (membershipScreeningTwoSureRoot_endpoints singleton).1,
    (membershipScreeningTwoSureRoot_endpoints singleton).2, max_self]

theorem membershipScreeningTwoSureRoot_padded_cap (singleton : ℝ) :
    quittingContinuationBestResponseValue (membershipScreeningSingletonReward singleton)
      (oneDateProductPaddedOneDateProfile (membershipScreeningSingletonReward singleton)
        1 membershipScreeningTwoSureRoot) 2 = max singleton 0 := by
  have hsure : (membershipScreeningTwoSureRoot 0 true).toReal = 1 := by
    simp [membershipScreeningTwoSureRoot]
  rw [oneDateProductQuittingContinuationBestResponseValue_paddedOneDateProfile _ (by decide),
    membershipScreeningSingletonReward_ownSingleton,
    (membershipScreeningTwoSureRoot_endpoints singleton).1,
    (membershipScreeningTwoSureRoot_endpoints singleton).2,
    oneDateProductOppContinue_eq_zero_of_sureQuitter _ 2 (by decide : (0 : Fin 4) ≠ 2) hsure]
  simp

/-- A single sure quitter's complete cap is its own singleton when that reward is nonnegative. -/
theorem membershipScreeningOneSureRoot_cap {singleton : ℝ} (hsingleton : 0 ≤ singleton) :
    quittingContinuationBestResponseValue (membershipScreeningSingletonReward singleton)
      (quittingOneDateThenNeverProfile (membershipScreeningSingletonReward singleton)
        membershipScreeningOneSureRoot) 2 = singleton := by
  apply le_antisymm
  · have hbound (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
        |membershipScreeningSingletonReward singleton terminal who| ≤ singleton := by
      unfold membershipScreeningSingletonReward
      split_ifs
      · exact le_of_eq (abs_of_nonneg hsingleton)
      · simpa only [abs_zero] using hsingleton
    exact (le_abs_self _).trans (abs_quittingContinuationBestResponseValue_le _ _ 2 hbound)
  · rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
    apply le_csSup (bddAbove_range_quittingPureTimeDeviationPayoff _ _ _)
    refine ⟨some 0, ?_⟩
    rw [oneDateProductPureTimeDeviationPayoff_oneDateThenNever_zero,
      (membershipScreeningOneSureRoot_endpoints singleton).1]

/-- Changing only the singleton from zero to one leaves the screened cap zero,
but changes both the padded cap and the one-sure unpadded cap from zero to one. -/
theorem membershipScreening_singleton_zero_one_cap_boundary :
    (∀ singleton : ℝ,
      quittingContinuationBestResponseValue (membershipScreeningSingletonReward singleton)
        (quittingOneDateThenNeverProfile (membershipScreeningSingletonReward singleton)
          membershipScreeningTwoSureRoot) 2 = 0) ∧
    quittingContinuationBestResponseValue (membershipScreeningSingletonReward 0)
      (oneDateProductPaddedOneDateProfile (membershipScreeningSingletonReward 0)
        1 membershipScreeningTwoSureRoot) 2 = 0 ∧
    quittingContinuationBestResponseValue (membershipScreeningSingletonReward 1)
      (oneDateProductPaddedOneDateProfile (membershipScreeningSingletonReward 1)
        1 membershipScreeningTwoSureRoot) 2 = 1 ∧
    quittingContinuationBestResponseValue (membershipScreeningSingletonReward 0)
      (quittingOneDateThenNeverProfile (membershipScreeningSingletonReward 0)
        membershipScreeningOneSureRoot) 2 = 0 ∧
    quittingContinuationBestResponseValue (membershipScreeningSingletonReward 1)
      (quittingOneDateThenNeverProfile (membershipScreeningSingletonReward 1)
        membershipScreeningOneSureRoot) 2 = 1 := by
  refine ⟨membershipScreeningTwoSureRoot_unpadded_cap, ?_, ?_, ?_, ?_⟩
  · rw [membershipScreeningTwoSureRoot_padded_cap]
    norm_num
  · rw [membershipScreeningTwoSureRoot_padded_cap]
    norm_num
  · exact membershipScreeningOneSureRoot_cap le_rfl
  · exact membershipScreeningOneSureRoot_cap zero_le_one

end GameTheory
