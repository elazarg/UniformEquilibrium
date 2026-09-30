import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic
import UniformEquilibrium.Quitting.Root.BernoulliExpectation
import UniformEquilibrium.Quitting.Boundary.Exceptional.InfiniteLTG
import MathUE.PMFProduct.SequentialSingletonMass

/-!
# Sequential serialization of small-hazard quitting roots

The construction replaces each simultaneous row by one substage per player.
The row comparison is division-free: the continuation coefficient is exactly
unchanged, and only collision rewards are reassigned to singleton outcomes.
The four-player estimates below are independent of the reward table. They
formalize the serialization argument of Solan--Vieille (2002), Lemma 9.
-/

noncomputable section

namespace GameTheory

open Filter _root_.Math.Probability Math.PMFProduct

/-- Replace a simultaneous row by its designated singleton substage. -/
def quittingSerializedStage {n : ℕ} (root : Fin n → PMF Bool) (phase : Fin n) :
    Fin n → PMF Bool :=
  quittingSoloMixedRoot phase (root phase)

/-- Chronological serialization: original row `time / n`, phase `time % n`. -/
def quittingSerializedRoots {n : ℕ} [NeZero n] (roots : ℕ → Fin n → PMF Bool) :
    ℕ → Fin n → PMF Bool :=
  fun time => quittingSerializedStage (roots (time / n))
    ⟨time % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- At a specified block and phase the serialized clock selects the literal row. -/
theorem quittingSerializedRoots_at {n : ℕ} [NeZero n]
    (roots : ℕ → Fin n → PMF Bool) (stage : ℕ) (phase : Fin n) :
    quittingSerializedRoots roots (n * stage + phase.val) =
      quittingSerializedStage (roots stage) phase := by
  have hdiv : (n * stage + phase.val) / n = stage := by
    rw [Nat.mul_add_div (NeZero.pos n), Nat.div_eq_of_lt phase.isLt, Nat.add_zero]
  have hmod : (n * stage + phase.val) % n = phase.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt phase.isLt]
  simp [quittingSerializedRoots, hdiv, hmod]

/-- Every substage retains exactly its owner's Continue probability. -/
theorem quittingSerializedStage_continueMass {n : ℕ}
    (root : Fin n → PMF Bool) (phase : Fin n) :
    quittingStationaryContinueMass (quittingSerializedStage root phase) =
      (root phase false).toReal :=
  quittingStationaryContinueMass_soloMixedRoot phase (root phase)

/-- Block survival agrees exactly with the unsplit row, for any player count. -/
theorem quittingSerializedStage_blockSurvival {n : ℕ} (root : Fin n → PMF Bool) :
    (∏ phase, quittingStationaryContinueMass (quittingSerializedStage root phase)) =
      quittingStationaryContinueMass root := by
  simp_rw [quittingSerializedStage_continueMass]
  exact (quittingStationaryContinueMass_eq_prod_continueProbability root).symm

/-- Actual Bellman evaluation of the four chronological singleton substages. -/
def quittingSerializedBlockPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (tail : Payoff (Fin 4)) : Payoff (Fin 4) :=
  quittingRootSuccessorPayoff reward
    (quittingRootSuccessorPayoff reward
      (quittingRootSuccessorPayoff reward
        (quittingRootSuccessorPayoff reward tail (quittingSerializedStage root 3))
        (quittingSerializedStage root 2))
      (quittingSerializedStage root 1))
    (quittingSerializedStage root 0)

/-- The chronological block is exactly the generic ordered-singleton expectation. -/
theorem quittingSerializedBlockPayoff_eq_orderedSingletonExpectation
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (tail : Payoff (Fin 4)) (who : Fin 4) :
    quittingSerializedBlockPayoff reward root tail who =
      orderedSingletonExpectation (fun coalition => weightOfReward reward coalition who)
        (tail who) (hazardOfRoot root) := by
  simp only [quittingSerializedBlockPayoff, quittingSerializedStage,
    quittingRootSuccessorPayoff_soloMixedRoot]
  simp only [orderedSingletonExpectation, continueMass, orderedSingletonMass,
    Finset.prod_filter, Fin.prod_univ_four, Fin.sum_univ_four]
  simp only [pmfBool_false_toReal]
  norm_num [hazardOfRoot, weightOfReward, quittingSingletonTerminal]
  ring

/-- A serialized row changes bounded payoffs only through original collisions.
No bound on the continuation payoff is required. -/
theorem abs_quittingSerializedBlockPayoff_sub_rootPayoff_le
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (tail : Payoff (Fin 4)) (who : Fin 4)
    {M ε : ℝ} (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hsmall : ∀ owner, (root owner true).toReal ≤ ε) :
    |quittingSerializedBlockPayoff reward root tail who -
        quittingRootSuccessorPayoff reward tail root who| ≤
      8 * M * ε * (1 - quittingStationaryContinueMass root) := by
  have hcontinue : continueMass (hazardOfRoot root) = quittingStationaryContinueMass root := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    apply Finset.prod_congr rfl
    intro owner _
    have hsum := quittingRoot_continueProbability_add_quitProbability root owner
    dsimp [hazardOfRoot]
    linarith
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal who))
  rw [quittingSerializedBlockPayoff_eq_orderedSingletonExpectation]
  change |orderedSingletonExpectation _ _ _ - quittingRootExpectedPayoff _ _ _ _| ≤ _
  rw [quittingRootExpectedPayoff_eq_smallHazardExpectation_weightOfReward]
  have hrow := abs_orderedSingletonExpectation_sub_smallHazardExpectation_le
    (fun coalition => weightOfReward reward coalition who) (tail who) (hazardOfRoot root)
    (hazardOfRoot_nonneg root) (hazardOfRoot_le_one root)
    (fun coalition hcoalition => by
      simpa [weightOfReward, hcoalition] using hreward ⟨coalition, hcoalition⟩)
  have hcollision := collisionMass_le_card_mul_maxHazard_mul_absorption
    (hazardOfRoot root) (hazardOfRoot_nonneg root) (hazardOfRoot_le_one root) hsmall
  refine hrow.trans ?_
  have hbound : 2 * M * collisionMass (hazardOfRoot root) ≤
      2 * M * ((Fintype.card (Fin 4) : ℝ) * ε * (1 - continueMass (hazardOfRoot root))) :=
    mul_le_mul_of_nonneg_left hcollision (mul_nonneg (by norm_num) hM)
  calc
    2 * M * collisionMass (hazardOfRoot root) ≤
        2 * M * ((Fintype.card (Fin 4) : ℝ) * ε *
          (1 - continueMass (hazardOfRoot root))) := hbound
    _ = 8 * M * ε * (1 - quittingStationaryContinueMass root) := by
      rw [hcontinue]
      norm_num only [Fintype.card_fin]
      ring

/-- The same continuation coordinate is transported by the unchanged block survival. -/
theorem quittingSerializedBlockPayoff_sub_eq_continueMass_mul
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (first second : Payoff (Fin 4)) (who : Fin 4) :
    quittingSerializedBlockPayoff reward root first who -
        quittingSerializedBlockPayoff reward root second who =
      quittingStationaryContinueMass root * (first who - second who) := by
  rw [quittingSerializedBlockPayoff_eq_orderedSingletonExpectation,
    quittingSerializedBlockPayoff_eq_orderedSingletonExpectation]
  have hcontinue : continueMass (hazardOfRoot root) = quittingStationaryContinueMass root := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    apply Finset.prod_congr rfl
    intro owner _
    have hsum := quittingRoot_continueProbability_add_quitProbability root owner
    dsimp [hazardOfRoot]
    linarith
  simp only [orderedSingletonExpectation, hcontinue]
  ring

/-- Four steps of the actual finite clock equal the literal serialized block evaluator. -/
theorem quittingFiniteRootPayoff_serialized_four_step
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (roots : ℕ → Fin 4 → PMF Bool) (who : Fin 4) (start fuel : ℕ) :
    quittingFiniteRootPayoff reward (quittingSerializedRoots roots) who
        (fun time => quittingSerializedRoots roots time who) (4 * start) (4 * fuel + 4) =
      quittingSerializedBlockPayoff reward (roots start)
        (fun _ => quittingFiniteRootPayoff reward (quittingSerializedRoots roots) who
          (fun time => quittingSerializedRoots roots time who) (4 * (start + 1))
          (4 * fuel)) who := by
  have hclock : ∀ phase : Fin 4,
      quittingSerializedRoots roots (4 * start + phase.val) =
        quittingSerializedStage (roots start) phase := quittingSerializedRoots_at roots start
  have hclock0 : quittingSerializedRoots roots (4 * start) =
      quittingSerializedStage (roots start) 0 := by simpa using hclock 0
  have hclock1 : quittingSerializedRoots roots (4 * start + 1) =
      quittingSerializedStage (roots start) 1 := by simpa using hclock 1
  have hclock2 : quittingSerializedRoots roots (4 * start + 2) =
      quittingSerializedStage (roots start) 2 := by simpa using hclock 2
  have hclock3 : quittingSerializedRoots roots (4 * start + 3) =
      quittingSerializedStage (roots start) 3 := by simpa using hclock 3
  change quittingFiniteRootPayoff _ _ _ _ (4 * start) (4 * fuel + 1 + 1 + 1 + 1) = _
  simp only [quittingFiniteRootPayoff, Function.update_eq_self]
  simp only [Nat.add_assoc]
  norm_num only
  rw [hclock0, hclock1, hclock2, hclock3]
  have hnext : 4 * start + 4 = 4 * (start + 1) := by omega
  simp only [hnext]
  rfl

end GameTheory
