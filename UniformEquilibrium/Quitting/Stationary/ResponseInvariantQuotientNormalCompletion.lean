import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientStrategic
import UniformEquilibrium.Quitting.Cycles.DiffuseTailSoloStructure
import UniformEquilibrium.Quitting.Punishment.SoloCycleCompletion
import UniformEquilibrium.Quitting.Classification.LCP.NormalCorePunishmentNormal
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.AmbientCarrierElimination

/-!
# Punishment completion of a stationary quotient root

A positive-absorption exact stationary Bellman root either contracts every
player's opponent clock, or has one positive-rate solo owner. In the latter
case, punishment normality feeds the existing solo-cycle completion compiler.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming QuittingLCPClassification
open ThreeCoreAmbientCarrierElimination

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An absorbing stationary Bellman root is strategically complete under
all-player punishment normality, even if its sole owner's reward is negative.
The solo branch uses the existing finite-prefix punishment compiler. -/
theorem exists_uniformEquilibriumPayoff_of_stationaryBellmanRoot_of_normality
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (value : Payoff ι)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hfixed : value = quittingRootSuccessorPayoff reward value root)
    (hnash : IsεQuittingRootNash reward value 0 root)
    (hnormal : ∀ who, IsQuittingNormalPlayer reward who) :
    ∃ payoff, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have habsorbs : quittingStationaryContinueMass root < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  by_cases hcontracts : ∀ who : ι,
      quittingStationaryFixedOpponentsContinueMass root who < 1
  · refine ⟨value, ?_⟩
    exact isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
      reward root value habsorbs hfixed
        ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
          reward value root).mpr hnash) hcontracts
  · obtain ⟨owner, hnotContract⟩ := not_forall.mp hcontracts
    have hmass : quittingStationaryFixedOpponentsContinueMass root owner = 1 := by
      exact le_antisymm
        (quittingStationaryFixedOpponentsContinueMass_le_one root owner)
        (le_of_not_gt hnotContract)
    have hpure := opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
      root owner hmass
    have hsolo : IsQuittingSoloRoot root owner := by
      intro other hne
      exact hpure other hne
    have hroot : root = quittingSoloStationaryRoot owner (root owner) :=
      hsolo.eq_soloStationaryRoot
    have hpositive : 0 < (root owner true).toReal := by
      rw [← hsolo.absorptionMass]
      exact habsorption
    have hsoloFixed : quittingSoloReward reward owner =
        quittingRootSuccessorPayoff reward
          (quittingSoloReward reward owner) root := by
      rw [hroot]
      exact (quittingRootSuccessorPayoff_soloStationaryRoot_self
        reward owner (root owner)).symm
    have hvalue : value = quittingSoloReward reward owner := by
      have hactual := quittingTerminalPayoff_stationary_eq_of_fixedPoint
        reward root value habsorbs hfixed
      have hsoloActual := quittingTerminalPayoff_stationary_eq_of_fixedPoint
        reward root (quittingSoloReward reward owner) habsorbs hsoloFixed
      exact hactual.symm.trans hsoloActual
    have hendpoint : IsεQuittingRootEndpointNash reward
        (quittingSoloReward reward owner) 0
        (quittingSoloStationaryRoot owner (root owner)) := by
      have hendpointOriginal :=
        (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
          reward value root).mpr hnash
      rw [hvalue] at hendpointOriginal
      rw [hroot] at hendpointOriginal
      exact hendpointOriginal
    have hpunishment : quittingPunishmentValue reward owner ≤
        quittingSoloReward reward owner owner := by
      simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
        quittingSoloReward, quittingSingletonTerminal] using hnormal owner
    exact ⟨quittingSoloReward reward owner,
      isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR
        reward owner (root owner) hpositive hendpoint hpunishment⟩

/-- Raw response invariance, quotient R0, nonunit quotient degree, and
all-player punishment normality imply a fixed original-game uniform payoff.
No root, punishment plan, or favorable strategy is supplied. -/
theorem exists_uniformEquilibriumPayoff_of_responseInvariant_normality
    {k : ℕ} (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (hR0 : IsR0Matrix
      (quittingResponseQuotientMatrix reward block representative))
    (hdegree : r0Degree (quittingResponseQuotientMatrix reward block representative)
      hR0 ≠ 1)
    (hnormal : ∀ who, IsQuittingNormalPlayer reward who) :
    ∃ payoff, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨root, value, habsorption, _hactual, hfixed, hnash, _hequal⟩ :=
    exists_original_stationaryBellmanRoot_of_quotientDegree_ne_one
      reward block representative hrepresentative hresponse hR0 hdegree
  exact exists_uniformEquilibriumPayoff_of_stationaryBellmanRoot_of_normality
    reward root value habsorption hfixed hnash hnormal

/-- The signed four-player response-invariant quotient criterion. The
normality input is derived from the original table under the contrary
no-uniform-payoff assumption, rather than supplied separately. -/
theorem exists_uniformEquilibriumPayoff_finFour_of_responseInvariant_degree_ne_one
    {k : ℕ} (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (block : Fin 4 → Fin k) (representative : Fin k → Fin 4)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (hR0 : IsR0Matrix
      (quittingResponseQuotientMatrix reward block representative))
    (hdegree : r0Degree (quittingResponseQuotientMatrix reward block representative)
      hR0 ≠ 1) :
    ∃ payoff, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  have hcore :=
    normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
      reward (by norm_num) hno
  have hnormal := all_punishmentNormal_of_normalCore_eq_univ reward hcore
  exact hno (exists_uniformEquilibriumPayoff_of_responseInvariant_normality
    reward block representative hrepresentative hresponse hR0 hdegree hnormal)

end GameTheory
