import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleCertificate
import UniformEquilibrium.Quitting.Terminal.TerminalProfileFiniteEarlyAbsorption

noncomputable section

namespace GameTheory
namespace SignedFourCycleSingletonData

open Filter Math.Probability
open scoped Topology

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable (data : SignedFourCycleSingletonData reward) (tests : data.StrictTests)

private theorem certificateProfile_liveMassZero (m : ℕ) (hm : 0 < m) :
    quittingLiveMassLimit reward
        (quittingCyclicBehaviorProfile reward
          (quittingSingletonArcCycleRoot (data.certificate tests).owner
            (data.certificate tests).hazard m
            (data.certificate tests).hazard_nonneg
            (data.certificate tests).hazard_lt_one)
          (quittingSingletonMeshInitialPhase
            (data.certificate tests).initial m hm)) = 0 := by
  let certificate := SignedFourCycleSingletonData.certificate data tests
  let roots := quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
    certificate.hazard_nonneg certificate.hazard_lt_one
  let phase := quittingSingletonMeshInitialPhase certificate.initial m hm
  have hopponent : Tendsto
      (quittingOpponentSurvivalWeight
        (quittingCyclicRootSequence roots phase) 0 0) atTop (nhds 0) := by
    apply tendsto_zero_quittingOpponentSurvivalWeight_cyclicRootSequence
    rw [prod_quittingSingletonArcCycleRoot_continueMass
      certificate.owner certificate.hazard m hm certificate.hazard_nonneg
      certificate.hazard_lt_one 0]
    exact certificate.opponent_product_lt_one 0
  have hjoint : Tendsto
      (quittingJointSurvivalWeight
        (quittingCyclicRootSequence roots phase) 0) atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun fuel ↦ quittingJointSurvivalWeight_nonneg _ _ _
    · exact fun fuel ↦
        quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
          (quittingCyclicRootSequence roots phase) 0 0 fuel
    · exact hopponent
  rw [quittingCyclicBehaviorProfile,
    quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit]
  exact tendsto_nhds_unique
    (tendsto_quittingJointSurvivalLimit
      (quittingCyclicRootSequence roots phase) 0) hjoint

/-- The signed four-cycle certificate supplies the unrestricted terminal
profiles needed by finite-menu early absorption. -/
theorem hasTerminalProfiles_liveMassZero
    (data : SignedFourCycleSingletonData reward) (tests : data.StrictTests) :
    ∀ error : ℝ, 0 < error →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        quittingTerminalExploitability reward profile < error ∧
        quittingLiveMassLimit reward profile = 0 := by
  intro error herror
  let certificate := SignedFourCycleSingletonData.certificate data tests
  let scale := balancedSingletonCycleCollisionCap reward *
    balancedSingletonCycleIntensityCap certificate
  have hscale : 0 ≤ scale := mul_nonneg
    (balancedSingletonCycleCollisionCap_nonneg reward)
    (balancedSingletonCycleIntensityCap_nonneg certificate)
  obtain ⟨m, hmLarge⟩ := exists_nat_gt (scale / error)
  have hmReal : 0 < (m : ℝ) :=
    lt_of_le_of_lt (div_nonneg hscale herror.le) hmLarge
  have hm : 0 < m := by exact_mod_cast hmReal
  let profile := quittingCyclicBehaviorProfile reward
    (quittingSingletonArcCycleRoot certificate.owner certificate.hazard m
      certificate.hazard_nonneg certificate.hazard_lt_one)
    (quittingSingletonMeshInitialPhase certificate.initial m hm)
  refine ⟨profile, ?_, data.certificateProfile_liveMassZero tests m hm⟩
  have hnash := (certificate.isTerminalNash_and_hasValue m hm).1
  have herrorBound := quittingTerminalExploitability_le_of_isεAsymptoticNash
    reward profile (div_nonneg hscale (Nat.cast_nonneg m)) hnash
  have hratio : scale / (m : ℝ) < error := by
    rw [div_lt_iff₀ hmReal]
    simpa [mul_comm] using (div_lt_iff₀ herror).mp hmLarge
  exact herrorBound.trans_lt hratio

/-- The signed four-cycle construction retains an unrestricted terminal cap
while forcing absorption before every requested terminal window. -/
theorem hasFiniteMenuFullEarlyAbsorption
    (data : SignedFourCycleSingletonData reward) (tests : data.StrictTests) :
    HasQuittingFiniteMenuFullEarlyAbsorption reward :=
  finiteMenuFullEarlyAbsorption_of_terminalProfiles_liveMassZero reward
    (hasTerminalProfiles_liveMassZero data tests)

/-- In particular, the signed four-cycle construction satisfies the displayed
finite-menu early-absorption predicate. -/
theorem hasFiniteMenuEarlyAbsorption
    (data : SignedFourCycleSingletonData reward) (tests : data.StrictTests) :
    HasQuittingFiniteMenuEarlyAbsorption reward :=
  finiteMenuEarlyAbsorption_of_terminalProfiles_liveMassZero reward
    (hasTerminalProfiles_liveMassZero data tests)

end SignedFourCycleSingletonData
end GameTheory
