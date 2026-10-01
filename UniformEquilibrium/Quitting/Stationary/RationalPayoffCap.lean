import UniformEquilibrium.Quitting.Root.RationalFiniteWordSemantics
import UniformEquilibrium.Quitting.Stationary.HazardPayoffCap

/-! # Exact rational stationary payoff and full behavioral-cap evaluation

The evaluators use finite rational sums, products, quotients, and maxima. Their
correctness is proved on the closed probability cube with contracting deleted
opponents. They provide a decidable regret test for one supplied rational root;
this file does not claim enumeration success or search termination.
-/

namespace GameTheory

open scoped BigOperators

variable {n : ℕ}

/-- Exact rational joint survival at a product root. -/
def rationalQuittingStationaryContinueMass (root : RationalQuittingRoot n) : ℚ :=
  ∏ who, (1 - root.probability who)

/-- Exact rational deleted-opponents survival. -/
def rationalQuittingStationaryDeletedContinueMass
    (root : RationalQuittingRoot n) (who : Fin n) : ℚ :=
  ∏ other ∈ Finset.univ.erase who, (1 - root.probability other)

/-- Exact rational stationary prescribed payoff, on the absorbing regime. -/
def rationalQuittingStationaryPayoff (reward : RationalQuittingReward n)
    (root : RationalQuittingRoot n) (who : Fin n) : ℚ :=
  rationalQuittingRootExpectedPayoff reward 0 root who /
    (1 - rationalQuittingStationaryContinueMass root)

/-- Exact rational complete cap on the deleted-opponents contracting regime. -/
def rationalQuittingStationaryFullCap (reward : RationalQuittingReward n)
    (root : RationalQuittingRoot n) (who : Fin n) : ℚ :=
  max (rationalQuittingRootPurePayoff reward 0 root who true)
    (rationalQuittingRootPurePayoff reward 0 root who false /
      (1 - rationalQuittingStationaryDeletedContinueMass root who))

/-- A supplied rational root passes precisely when deleted opponents contract
and every exact rational complete-cap regret is at most the tolerance. -/
def rationalQuittingStationaryRegretAccepts (reward : RationalQuittingReward n)
    (root : RationalQuittingRoot n) (accuracy : ℚ) : Bool :=
  decide ((∀ who, rationalQuittingStationaryDeletedContinueMass root who < 1) ∧
    ∀ who, rationalQuittingStationaryFullCap reward root who ≤
      rationalQuittingStationaryPayoff reward root who + accuracy)

theorem quittingStationaryContinueMass_rationalQuitting_eq_cast
    (root : RationalQuittingRoot n) :
    quittingStationaryContinueMass root.toPMF =
      (rationalQuittingStationaryContinueMass root : ℝ) := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [rationalQuittingStationaryContinueMass]

theorem quittingStationaryDeletedContinueMass_rationalQuitting_eq_cast
    (root : RationalQuittingRoot n) (who : Fin n) :
    quittingStationaryFixedOpponentsContinueMass root.toPMF who =
      (rationalQuittingStationaryDeletedContinueMass root who : ℝ) := by
  rw [quittingStationaryFixedOpponentsContinueMass_eq_continueMassExcl]
  simp [continueMassExcl, hazardOfRoot, rationalQuittingStationaryDeletedContinueMass]

theorem quittingStationaryQuitValue_rationalQuitting_eq_cast
    (reward : RationalQuittingReward n) (root : RationalQuittingRoot n) (who : Fin n) :
    quittingStationaryFixedOpponentsQuitValue
      (rationalQuittingRewardToReal reward) root.toPMF who =
        (rationalQuittingRootPurePayoff reward 0 root who true : ℝ) := by
  change quittingRootQuitPayoff (rationalQuittingRewardToReal reward) 0 root.toPMF who = _
  have hzero : (fun player : Fin n => ((0 : Fin n → ℚ) player : ℝ)) =
      (0 : Payoff (Fin n)) := by
    funext player
    simp
  have h := quittingRootPurePayoff_rationalQuitting_eq_cast reward 0 root who true
  rw [hzero] at h
  exact h

theorem quittingStationaryContinueReward_rationalQuitting_eq_cast
    (reward : RationalQuittingReward n) (root : RationalQuittingRoot n) (who : Fin n) :
    quittingStationaryFixedOpponentsContinueReward
      (rationalQuittingRewardToReal reward) root.toPMF who =
        (rationalQuittingRootPurePayoff reward 0 root who false : ℝ) := by
  change quittingRootContinuePayoff (rationalQuittingRewardToReal reward) 0 root.toPMF who = _
  have hzero : (fun player : Fin n => ((0 : Fin n → ℚ) player : ℝ)) =
      (0 : Payoff (Fin n)) := by
    funext player
    simp
  have h := quittingRootPurePayoff_rationalQuitting_eq_cast reward 0 root who false
  rw [hzero] at h
  exact h

/-- Correctness for the actual stationary terminal payoff, not a finite surrogate. -/
theorem quittingTerminalPayoff_stationary_rationalQuitting_eq_cast
    (reward : RationalQuittingReward n) (root : RationalQuittingRoot n) (who : Fin n)
    (hcontracts : rationalQuittingStationaryDeletedContinueMass root who < 1) :
    quittingTerminalPayoff (rationalQuittingRewardToReal reward)
      (quittingStationaryProfile (rationalQuittingRewardToReal reward) root.toPMF) who =
        (rationalQuittingStationaryPayoff reward root who : ℝ) := by
  have hreal : quittingStationaryFixedOpponentsContinueMass root.toPMF who < 1 := by
    rw [quittingStationaryDeletedContinueMass_rationalQuitting_eq_cast]
    exact_mod_cast hcontracts
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div _ _ who
    (quittingStationaryContinueMass_lt_one_of_deleted_contracts root.toPMF who hreal),
    rationalQuittingStationaryPayoff, Rat.cast_div, Rat.cast_sub, Rat.cast_one,
    ← quittingStationaryContinueMass_rationalQuitting_eq_cast]
  congr 1
  change quittingRootExpectedPayoff (rationalQuittingRewardToReal reward) 0 root.toPMF who = _
  have hzero : (fun player : Fin n => ((0 : Fin n → ℚ) player : ℝ)) =
      (0 : Payoff (Fin n)) := by
    funext player
    simp
  have h := quittingRootExpectedPayoff_rationalQuitting_eq_cast reward 0 root who
  rw [hzero] at h
  exact h

/-- Correctness for the actual full-rate cap over all behavioral deviations. -/
theorem quittingStationaryFullRateUnilateralCap_rationalQuitting_eq_cast
    (reward : RationalQuittingReward n) (root : RationalQuittingRoot n) (who : Fin n)
    (hcontracts : rationalQuittingStationaryDeletedContinueMass root who < 1) :
    quittingStationaryFullRateUnilateralCap (rationalQuittingRewardToReal reward)
      root.toPMF who = (rationalQuittingStationaryFullCap reward root who : ℝ) := by
  have hreal : quittingStationaryFixedOpponentsContinueMass root.toPMF who < 1 := by
    rw [quittingStationaryDeletedContinueMass_rationalQuitting_eq_cast]
    exact_mod_cast hcontracts
  rw [quittingStationaryFullRateUnilateralCap_of_lt _ _ who hreal]
  simp only [quittingStationaryUnilateralCap, quittingStationarySelectedCap,
    quittingStationaryNeverValue, rationalQuittingStationaryFullCap,
    quittingStationaryQuitValue_rationalQuitting_eq_cast,
    quittingStationaryContinueReward_rationalQuitting_eq_cast,
    quittingStationaryDeletedContinueMass_rationalQuitting_eq_cast,
    Rat.cast_max, Rat.cast_div, Rat.cast_sub, Rat.cast_one]

theorem quittingContinuationBestResponseValue_stationary_rationalQuitting_eq_cast
    (reward : RationalQuittingReward n) (root : RationalQuittingRoot n) (who : Fin n)
    (hcontracts : rationalQuittingStationaryDeletedContinueMass root who < 1) :
    quittingContinuationBestResponseValue (rationalQuittingRewardToReal reward)
      (quittingStationaryProfile (rationalQuittingRewardToReal reward) root.toPMF) who =
        (rationalQuittingStationaryFullCap reward root who : ℝ) := by
  rw [quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap]
  exact quittingStationaryFullRateUnilateralCap_rationalQuitting_eq_cast
    reward root who hcontracts

/-- The executable acceptance test is equivalent to contraction and actual
terminal approximate Nash against the entire behavioral deviation class. -/
theorem rationalQuittingStationaryRegretAccepts_eq_true_iff
    (reward : RationalQuittingReward n) (root : RationalQuittingRoot n) (accuracy : ℚ) :
    rationalQuittingStationaryRegretAccepts reward root accuracy = true ↔
      (∀ who, quittingStationaryFixedOpponentsContinueMass root.toPMF who < 1) ∧
      (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
        (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) (accuracy : ℝ)
        (quittingStationaryProfile (rationalQuittingRewardToReal reward) root.toPMF) := by
  rw [rationalQuittingStationaryRegretAccepts, decide_eq_true_eq,
    isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le]
  constructor
  · rintro ⟨hcontracts, hregret⟩
    refine ⟨?_, ?_⟩
    · intro who
      rw [quittingStationaryDeletedContinueMass_rationalQuitting_eq_cast]
      exact_mod_cast hcontracts who
    · intro who
      rw [quittingStationaryFullRateUnilateralCap_rationalQuitting_eq_cast
        reward root who (hcontracts who),
        quittingTerminalPayoff_stationary_rationalQuitting_eq_cast
          reward root who (hcontracts who)]
      exact_mod_cast hregret who
  · rintro ⟨hcontracts, hregret⟩
    have hrational (who : Fin n) :
        rationalQuittingStationaryDeletedContinueMass root who < 1 := by
      have h := hcontracts who
      rw [quittingStationaryDeletedContinueMass_rationalQuitting_eq_cast] at h
      exact_mod_cast h
    refine ⟨hrational, fun who => ?_⟩
    have h := hregret who
    rw [quittingStationaryFullRateUnilateralCap_rationalQuitting_eq_cast
      reward root who (hrational who),
      quittingTerminalPayoff_stationary_rationalQuitting_eq_cast
        reward root who (hrational who)] at h
    exact_mod_cast h

end GameTheory
