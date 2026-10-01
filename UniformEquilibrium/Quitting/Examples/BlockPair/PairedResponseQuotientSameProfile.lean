import UniformEquilibrium.Quitting.Examples.BlockPair.PairedResponseQuotientClass
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientSameProfile

/-!
# The paired centered class: an actual same-profile stationary equilibrium

Only the two singleton-block owners, players two and three, need nonnegative
own-singleton rewards. The paired owners' own rewards and all permitted
nonsingleton entries remain signed. The generic root-preserving producer
supplies the actual independent stationary profile, fixed payoff and complete
behavioral cap, rather than accepting them as certificate fields.
-/

noncomputable section

namespace GameTheory
namespace PairedResponseQuotient

open Math.LinearProgramming

/-- The paired sign alternative retains the produced root and actual fixed value,
with one SAME stationary profile serving every positive accuracy. -/
theorem exists_stationaryTerminalNash_sameProfileUniform_of_pairedCenteredCompletion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclass : IsPairedCenteredCompletion reward)
    (htwo : 0 ≤ reward (quittingSingletonTerminal 2) 2)
    (hthree : 0 ≤ reward (quittingSingletonTerminal 3) 3) :
    ∃ point : Fin 3 → ℝ, ∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
      point ≠ 0 ∧
      quittingQuotientStationaryClippedMap reward block representative point = point ∧
      hazardOfRoot root = quittingBlockLift block point ∧
      0 < quittingRootAbsorptionMass root ∧
      value = quittingTerminalPayoff reward (quittingStationaryProfile reward root) ∧
      value = quittingRootSuccessorPayoff reward value root ∧
      IsεQuittingRootNash reward value 0 root ∧
      hazardOfRoot root 0 = hazardOfRoot root 1 ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none value ∧
      ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
        ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon accuracy
            (quittingStationaryProfile reward root) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingStationaryProfile reward root) who - value who| ≤ accuracy := by
  have hquotient := quotientMatrix_eq_of_pairedSingletonMatrix reward hclass.1
  have hR0 : IsR0Matrix (quittingResponseQuotientMatrix reward block representative) := by
    rw [hquotient]
    exact isR0
  have hdegree :
      r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 ≠ 1 := by
    simpa only [hquotient] using degree_ne_one
  have hsign : ∀ who : Fin 4,
      (∀ other, other ≠ who → block other ≠ block who) →
        0 ≤ reward (quittingSingletonTerminal who) who := by
    intro who hsingleton
    fin_cases who
    · exact (hsingleton 1 (by decide) rfl).elim
    · exact (hsingleton 0 (by decide) rfl).elim
    · exact htwo
    · exact hthree
  obtain ⟨point, root, value, hpoint, hfixed, hhazard, habsorption, hactual,
      hbellman, hnash, hequal, hterminal, huniform, hsame⟩ :=
    exists_stationaryTerminalNash_sameProfileUniform_of_responseInvariant_singletonSign
      reward block representative block_representative hsign
      (responseInvariant_of_pairedCenteredCompletion reward hclass) hR0 hdegree
  exact ⟨point, root, value, hpoint, hfixed, hhazard, habsorption, hactual,
    hbellman, hnash, hequal 0 1 rfl, hterminal, huniform, hsame⟩

end PairedResponseQuotient
end GameTheory
