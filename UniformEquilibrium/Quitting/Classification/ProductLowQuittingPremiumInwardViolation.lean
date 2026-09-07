import MathUE.FiniteSupportInwardScaling
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumMonotonicity

/-! # Inward witnesses for failure of product-low quitting premiums -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The singleton-relative pure-Quit payoff written directly as a polynomial
in the opponents' hazard coordinates. -/
def quittingHazardQuitPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hazard : ι → ℝ) (player : ι) : ℝ :=
  ∑ coalition ∈ (Finset.univ.erase player).powerset,
    ((∏ other ∈ coalition, hazard other) *
      ∏ other ∈ Finset.univ.erase player \ coalition,
        (1 - hazard other)) *
      (reward ⟨insert player coalition,
          Finset.insert_nonempty player coalition⟩ player -
        reward (quittingSingletonTerminal player) player)

theorem continuous_quittingHazardQuitPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) :
    Continuous (fun hazard => quittingHazardQuitPremium reward hazard player) := by
  apply continuous_finsetSum
  intro coalition _
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_finsetProd _ fun other _ => continuous_apply other
    · exact continuous_finsetProd _ fun other _ =>
        continuous_const.sub (continuous_apply other)
  · exact continuous_const

theorem quittingHazardQuitPremium_eq_rootQuitPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hazard : ι → ℝ) (hzero : ∀ player, 0 ≤ hazard player)
    (hone : ∀ player, hazard player ≤ 1) (player : ι) :
    quittingHazardQuitPremium reward hazard player =
      quittingRootQuitPayoff reward 0
          (rootOfHazard hazard hzero hone) player -
        reward (quittingSingletonTerminal player) player := by
  rw [quittingRootQuitPremium_eq_sum_opponentCoalitionPremium]
  apply Finset.sum_congr rfl
  intro coalition _
  congr 1
  simp [quittingOpponentCoalitionMass, rootOfHazard,
    pmfBool_false_toReal]

/-- Failure of product-low premiums can always be witnessed away from every
sure-Quit face, with the same positive support and strict endpoint violations. -/
theorem not_hasProductLowQuittingPremium_iff_exists_inwardViolation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ¬HasProductLowQuittingPremium reward ↔
      ∃ root : ι → PMF Bool,
        0 < quittingRootAbsorptionMass root ∧
        (∀ player, (root player true).toReal < 1) ∧
        ∀ player, 0 < (root player true).toReal →
          reward (quittingSingletonTerminal player) player <
            quittingRootQuitPayoff reward 0 root player := by
  constructor
  · intro hfailure
    unfold HasProductLowQuittingPremium at hfailure
    push Not at hfailure
    obtain ⟨root, habsorption, hstrict⟩ := hfailure
    let hazard := hazardOfRoot root
    have hzero : ∀ player, 0 ≤ hazard player := hazardOfRoot_nonneg root
    have hone : ∀ player, hazard player ≤ 1 := hazardOfRoot_le_one root
    have hpositive : ∀ player, 0 < hazard player →
        0 < quittingHazardQuitPremium reward hazard player := by
      intro player hactive
      rw [quittingHazardQuitPremium_eq_rootQuitPremium reward hazard hzero hone]
      rw [rootOfHazard_hazardOfRoot]
      exact sub_pos.mpr (hstrict player hactive)
    obtain ⟨inward, hinward0, hinward1, hsupport, htests⟩ :=
      Math.exists_inwardScale_preserving_positiveSupport_tests
        hazard hzero hone
        (fun player candidate =>
          quittingHazardQuitPremium reward candidate player)
        (fun player =>
          (continuous_quittingHazardQuitPremium reward player).continuousAt)
        hpositive
    let inwardRoot := rootOfHazard inward hinward0 (fun player => (hinward1 player).le)
    have hrates : ∀ player, (inwardRoot player true).toReal = inward player := by
      intro player
      change hazardOfRoot inwardRoot player = inward player
      rw [show hazardOfRoot inwardRoot = inward from
        hazardOfRoot_rootOfHazard inward hinward0
          (fun player => (hinward1 player).le)]
    obtain ⟨activePlayer, hactivePlayer⟩ :
        ∃ player, 0 < (root player true).toReal := by
      by_contra hnone
      push Not at hnone
      have hzeroRoot : ∀ player, (root player true).toReal = 0 := fun player =>
        le_antisymm (hnone player) ENNReal.toReal_nonneg
      unfold quittingRootAbsorptionMass at habsorption
      rw [quittingStationaryContinueMass_eq_prod_continueProbability] at habsorption
      have hcontinue : (fun player => (root player false).toReal) = fun _ => 1 := by
        funext player
        have := quittingRoot_continueProbability_add_quitProbability root player
        rw [hzeroRoot player] at this
        linarith
      rw [hcontinue] at habsorption
      simp at habsorption
    have hinwardActive : 0 < inward activePlayer :=
      (hsupport activePlayer).mpr hactivePlayer
    have habsorptionInward : 0 < quittingRootAbsorptionMass inwardRoot := by
      have hcontinue :=
        quittingStationaryContinueMass_le_ownContinueProbability
          inwardRoot activePlayer
      have hsum := quittingRoot_continueProbability_add_quitProbability
        inwardRoot activePlayer
      unfold quittingRootAbsorptionMass
      rw [hrates activePlayer] at hsum
      linarith
    refine ⟨inwardRoot, habsorptionInward, ?_, ?_⟩
    · intro player
      rw [hrates player]
      exact hinward1 player
    · intro player hactive
      have htest := htests player (by simpa [hrates player] using hactive)
      rw [quittingHazardQuitPremium_eq_rootQuitPremium reward inward
        hinward0 (fun other => (hinward1 other).le) player] at htest
      exact sub_pos.mp htest
  · rintro ⟨root, habsorption, _hinward, hstrict⟩ hlow
    obtain ⟨player, hactive, hle⟩ := hlow root habsorption
    exact (not_lt_of_ge hle) (hstrict player hactive)

/-- The product-low condition written on real hazard vectors. -/
theorem hasProductLowQuittingPremium_iff_hazard
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasProductLowQuittingPremium reward ↔
      ∀ hazard : ι → ℝ, (∀ player, 0 ≤ hazard player) →
        (∀ player, hazard player ≤ 1) → (∃ player, 0 < hazard player) →
          ∃ player, 0 < hazard player ∧
            quittingHazardQuitPremium reward hazard player ≤ 0 := by
  constructor
  · intro hlow hazard hzero hone hactive
    let root := rootOfHazard hazard hzero hone
    have hrootHazard : hazardOfRoot root = hazard :=
      hazardOfRoot_rootOfHazard hazard hzero hone
    have habsorption : 0 < quittingRootAbsorptionMass root := by
      rw [quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos]
      change ∃ player, 0 < hazardOfRoot root player
      rwa [hrootHazard]
    obtain ⟨player, hplayer, hpremium⟩ := hlow root habsorption
    refine ⟨player, ?_, ?_⟩
    · change 0 < hazardOfRoot root player at hplayer
      rwa [hrootHazard] at hplayer
    · rw [quittingHazardQuitPremium_eq_rootQuitPremium reward hazard hzero hone]
      exact sub_nonpos.mpr hpremium
  · intro hhazard root habsorption
    have hactive : ∃ player, 0 < hazardOfRoot root player := by
      simpa [hazardOfRoot] using
        (quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos root).mp
          habsorption
    obtain ⟨player, hplayer, hpremium⟩ :=
      hhazard (hazardOfRoot root) (hazardOfRoot_nonneg root)
        (hazardOfRoot_le_one root) hactive
    refine ⟨player, hplayer, ?_⟩
    rw [quittingHazardQuitPremium_eq_rootQuitPremium reward (hazardOfRoot root)
      (hazardOfRoot_nonneg root) (hazardOfRoot_le_one root),
      rootOfHazard_hazardOfRoot] at hpremium
    exact sub_nonpos.mp hpremium

end GameTheory
