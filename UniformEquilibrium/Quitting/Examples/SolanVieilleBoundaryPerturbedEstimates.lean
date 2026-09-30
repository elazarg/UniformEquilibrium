import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryNonstationarity
import UniformEquilibrium.Quitting.Classification.Existence.ApproximateEquilibriumVanishingNeverAlternative

/-!
# Exact estimates for perturbed Solan--Vieille boundary equilibria

The one-quitter hypothesis eliminates collision outcomes exactly. The resulting
payoff identities and the global behavioral Nash cap give the constants in
Lemma 10 of Solan and Vieille, *Quitting games -- An example* (2002).
The Never estimate uses only the Nash cap and unit solo rewards.
-/

noncomputable section

namespace GameTheory
namespace SolanVieilleBoundary

/-- Every terminal approximate equilibrium of the boundary table has Never
probability at most its error, without a perturbation or absorption assumption. -/
theorem boundary_survivalLimit_le_nashError
    {roots : BoundaryRootSequence (ι := Fin 4)} {ε : ℝ} (hε : 0 ≤ ε)
    (hnash : IsBoundaryTerminalApproxNash boundaryReward ε
      (boundaryRootSequenceProfile boundaryReward roots)) :
    quittingJointSurvivalLimit roots 0 ≤ ε := by
  have hrootNash :=
    (isεQuittingRootSequenceNash_iff_isεAsymptoticNash boundaryReward ε roots).mpr hnash
  by_cases hzero : quittingJointSurvivalLimit roots 0 = 0
  · simpa [hzero] using hε
  have hpositive : 0 < quittingJointSurvivalLimit roots 0 :=
    lt_of_le_of_ne (quittingJointSurvivalLimit_nonneg roots 0) (Ne.symm hzero)
  have hcap := singletonReward_le_nashError_div_never
    boundaryReward roots ε hε hrootNash hpositive (0 : Fin 4)
  have hself : boundaryReward (quittingSingletonTerminal (0 : Fin 4)) 0 = 1 :=
    boundaryReward_unitSoloExit 0
  rw [hself] at hcap
  simpa using (le_div_iff₀ hpositive).mp hcap

/-- The source's one-quitter condition removes total collision mass, including
in profiles with positive Never probability. -/
theorem boundary_collisionMass_eq_zero_of_atMostOne
    {roots : BoundaryRootSequence (ι := Fin 4)}
    (hone : ∀ time first second,
      0 < (roots time first true).toReal → 0 < (roots time second true).toReal →
      first = second) :
    quittingRootSequenceCollisionMass roots 0 = 0 := by
  have hstage : ∀ time, quittingRootCollisionMass (roots time) = 0 :=
    fun time =>
      (quittingRootCollisionMass_eq_zero_iff_atMostOne_quitProbability_pos _).mpr (hone time)
  simp [quittingRootSequenceCollisionMass, hstage]

/-- Without collisions, each player's payoff is its singleton mass plus four
times its partner's singleton mass. -/
theorem boundary_terminalValue_eq_pairMass_of_atMostOne
    {roots : BoundaryRootSequence (ι := Fin 4)}
    (hone : ∀ time first second,
      0 < (roots time first true).toReal → 0 < (roots time second true).toReal →
      first = second) (who : Fin 4) :
    quittingRootSequenceTerminalValue boundaryReward roots who 0 =
      quittingRootSequenceSingletonMass roots 0 who +
        4 * quittingRootSequenceSingletonMass roots 0 (boundaryPartner who) := by
  have hbound := boundary_terminalValue_pairMass_approx roots who
  rw [boundary_collisionMass_eq_zero_of_atMostOne hone, mul_zero] at hbound
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hbound)

/-- A singleton exit distributes total payoff five; Never distributes zero. -/
theorem boundary_sum_terminalValue_eq_five_mul_absorption_of_atMostOne
    {roots : BoundaryRootSequence (ι := Fin 4)}
    (hone : ∀ time first second,
      0 < (roots time first true).toReal → 0 < (roots time second true).toReal →
      first = second) :
    (∑ who : Fin 4, quittingRootSequenceTerminalValue boundaryReward roots who 0) =
      5 * (1 - quittingJointSurvivalLimit roots 0) := by
  have hmass := sum_quittingRootSequenceSingletonMass_add_collisionMass roots 0
  rw [boundary_collisionMass_eq_zero_of_atMostOne hone, add_zero,
    Fin.sum_univ_four] at hmass
  rw [Fin.sum_univ_four]
  simp_rw [boundary_terminalValue_eq_pairMass_of_atMostOne hone]
  change
    (quittingRootSequenceSingletonMass roots 0 0 +
        4 * quittingRootSequenceSingletonMass roots 0 1) +
      (quittingRootSequenceSingletonMass roots 0 1 +
        4 * quittingRootSequenceSingletonMass roots 0 0) +
      (quittingRootSequenceSingletonMass roots 0 2 +
        4 * quittingRootSequenceSingletonMass roots 0 3) +
      (quittingRootSequenceSingletonMass roots 0 3 +
        4 * quittingRootSequenceSingletonMass roots 0 2) = _
  linarith

private theorem absorptionMass_le_of_atMostOne
    {roots : BoundaryRootSequence (ι := Fin 4)} {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ∀ time who, (roots time who true).toReal ≤ ε)
    (hone : ∀ time first second,
      0 < (roots time first true).toReal → 0 < (roots time second true).toReal →
      first = second) (time : ℕ) :
    quittingRootAbsorptionMass (roots time) ≤ ε := by
  refine (quittingRootAbsorptionMass_le_sum_quitProbability (roots time)).trans ?_
  by_cases hexists : ∃ owner, 0 < (roots time owner true).toReal
  · obtain ⟨owner, howner⟩ := hexists
    rw [Finset.sum_eq_single owner]
    · exact hsmall time owner
    · intro other _ hne
      apply le_antisymm _ ENNReal.toReal_nonneg
      exact le_of_not_gt (fun hpositive => hne (hone time other owner hpositive howner))
    · simp
  · have hzero : ∀ owner, (roots time owner true).toReal = 0 := by
      intro owner
      apply le_antisymm _ ENNReal.toReal_nonneg
      exact le_of_not_gt (fun hpositive => hexists ⟨owner, hpositive⟩)
    simpa [hzero] using hε

/-- Immediate Quit is within `8ε` of the solo reward when at most one
player can quit and each marginal Quit probability is at most `ε`. -/
theorem boundary_fixedOpponentsQuitValue_ge_of_atMostOne
    {roots : BoundaryRootSequence (ι := Fin 4)} {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ∀ time who, (roots time who true).toReal ≤ ε)
    (hone : ∀ time first second,
      0 < (roots time first true).toReal → 0 < (roots time second true).toReal →
      first = second) (who : Fin 4) (time : ℕ) :
    1 - 8 * ε ≤ quittingFixedOpponentsQuitValue boundaryReward roots who time := by
  have hnear := abs_quittingFixedOpponentsQuitValue_sub_one_le
    boundaryReward_unitSoloExit roots who time boundaryReward_abs_le_four
  have hopponent := (quittingRootOpponentAbsorptionMass_le_absorptionMass
    (roots time) who).trans (absorptionMass_le_of_atMostOne hε hsmall hone time)
  have hlower := (abs_le.mp hnear).1
  linarith

/-- The global Nash cap applied to immediate Quit gives the exact source floor. -/
theorem boundary_terminalValue_ge_one_sub_nine_mul_of_atMostOne
    {roots : BoundaryRootSequence (ι := Fin 4)} {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ∀ time who, (roots time who true).toReal ≤ ε)
    (hone : ∀ time first second,
      0 < (roots time first true).toReal → 0 < (roots time second true).toReal →
      first = second)
    (hnash : IsBoundaryTerminalApproxNash boundaryReward ε
      (boundaryRootSequenceProfile boundaryReward roots)) (who : Fin 4) :
    1 - 9 * ε ≤ quittingRootSequenceTerminalValue boundaryReward roots who 0 := by
  have hrootNash :=
    (isεQuittingRootSequenceNash_iff_isεAsymptoticNash boundaryReward ε roots).mpr hnash
  have htransfer := quittingJointSurvivalWeight_mul_stageDeviationGain_le
    boundaryReward roots hrootNash who 0
    (PMF.pure true) (fun offset => roots (1 + offset) who)
  have hupdated :
      quittingRootSuccessorPayoff boundaryReward
        (fun _ => quittingRootSequenceHazardTerminalValue boundaryReward
          (fun offset => roots (1 + offset)) who
          (fun offset => roots (1 + offset) who) 0)
        (Function.update (roots 0) who (PMF.pure true)) who =
      quittingFixedOpponentsQuitValue boundaryReward roots who 0 := by
    rw [quittingRootSuccessorPayoff, quittingRootExpectedPayoff_update_eq_endpointMix]
    simp
    exact quittingRootQuitPayoff_eq_fixedOpponentsQuitValue boundaryReward roots who _ 0
  rw [hupdated] at htransfer
  simp only [quittingJointSurvivalWeight_zero_fuel, one_mul] at htransfer
  have hquit := boundary_fixedOpponentsQuitValue_ge_of_atMostOne hε hsmall hone who 0
  linarith

/-- One coordinate is at least `5/4 - 2ε`, as in the printed Lemma 10. -/
theorem boundary_exists_player_value_ge_five_fourths_sub_two_mul_of_atMostOne
    {roots : BoundaryRootSequence (ι := Fin 4)} {ε : ℝ} (hε : 0 ≤ ε)
    (hone : ∀ time first second,
      0 < (roots time first true).toReal → 0 < (roots time second true).toReal →
      first = second)
    (hnash : IsBoundaryTerminalApproxNash boundaryReward ε
      (boundaryRootSequenceProfile boundaryReward roots)) :
    ∃ who : Fin 4, 5 / 4 - 2 * ε ≤
      quittingRootSequenceTerminalValue boundaryReward roots who 0 := by
  have hnever := boundary_survivalLimit_le_nashError hε hnash
  have hsum := boundary_sum_terminalValue_eq_five_mul_absorption_of_atMostOne hone
  by_contra hno
  push Not at hno
  have hzero := hno 0
  have honeValue := hno 1
  have htwo := hno 2
  have hthree := hno 3
  rw [Fin.sum_univ_four] at hsum
  linarith

/-- The exact pair identities and the four coordinate floors give every
singleton mass the printed lower bound `2/15 - 8ε`. -/
theorem boundary_singletonMass_ge_two_fifteenths_sub_eight_mul_of_atMostOne
    {roots : BoundaryRootSequence (ι := Fin 4)} {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ∀ time who, (roots time who true).toReal ≤ ε)
    (hone : ∀ time first second,
      0 < (roots time first true).toReal → 0 < (roots time second true).toReal →
      first = second)
    (hnash : IsBoundaryTerminalApproxNash boundaryReward ε
      (boundaryRootSequenceProfile boundaryReward roots)) (who : Fin 4) :
    2 / 15 - 8 * ε ≤ quittingRootSequenceSingletonMass roots 0 who := by
  have hpair (player : Fin 4) :=
    boundary_terminalValue_ge_one_sub_nine_mul_of_atMostOne hε hsmall hone hnash player
  simp_rw [boundary_terminalValue_eq_pairMass_of_atMostOne hone] at hpair
  have hmass := sum_quittingRootSequenceSingletonMass_add_collisionMass roots 0
  have hnever := quittingJointSurvivalLimit_nonneg roots 0
  rw [boundary_collisionMass_eq_zero_of_atMostOne hone, add_zero,
    Fin.sum_univ_four] at hmass
  have hzero := hpair 0
  have honeValue := hpair 1
  have htwo := hpair 2
  have hthree := hpair 3
  change 1 - 9 * ε ≤ quittingRootSequenceSingletonMass roots 0 0 +
    4 * quittingRootSequenceSingletonMass roots 0 1 at hzero
  change 1 - 9 * ε ≤ quittingRootSequenceSingletonMass roots 0 1 +
    4 * quittingRootSequenceSingletonMass roots 0 0 at honeValue
  change 1 - 9 * ε ≤ quittingRootSequenceSingletonMass roots 0 2 +
    4 * quittingRootSequenceSingletonMass roots 0 3 at htwo
  change 1 - 9 * ε ≤ quittingRootSequenceSingletonMass roots 0 3 +
    4 * quittingRootSequenceSingletonMass roots 0 2 at hthree
  fin_cases who
  · change 2 / 15 - 8 * ε ≤ quittingRootSequenceSingletonMass roots 0 0
    linarith
  · change 2 / 15 - 8 * ε ≤ quittingRootSequenceSingletonMass roots 0 1
    linarith
  · change 2 / 15 - 8 * ε ≤ quittingRootSequenceSingletonMass roots 0 2
    linarith
  · change 2 / 15 - 8 * ε ≤ quittingRootSequenceSingletonMass roots 0 3
    linarith

end SolanVieilleBoundary
end GameTheory
