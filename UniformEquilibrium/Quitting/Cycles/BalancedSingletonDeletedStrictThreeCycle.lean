import UniformEquilibrium.Quitting.Cycles.BalancedSingletonDeletedPath
import UniformEquilibrium.Quitting.Paths.StrictThreeCycleSingletonFloor
import UniformEquilibrium.Quitting.Terminal.StrictThreeCycleDeadlineResponseDebt

/-! # Strict three-cycle consequences of an actual deleted balanced path

The balanced certificate belongs only to the deleted child game. The parent
schedule is its literal Never lift. Its floor, deadline, and response-debt
consequences use actual parent terminal values, with no parent floor premise.
-/

noncomputable section

namespace GameTheory.BalancedSingletonCycleCertificate

open Math.LinearProgramming Math.LinearProgramming.ThreeCycleInverseFormulas
open QuittingLCPClassification

variable {L : ℕ} {ι : Type}
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (B : Finset ι)
variable (certificate : BalancedSingletonCycleCertificate (L := L)
  (quittingDeleteReward reward (· ∈ B)))

/-- The exact path hypotheses needed by the strict-cycle consumers. They
come from the child certificate and the literal Never lift. -/
private theorem deletedRootSequence_strictThreeCyclePath
    [Fintype ι] [DecidableEq ι]
    (m : ℕ) (hm : 0 < m) (phase : Fin (L * m))
    (child : Fin 3 ↪ ι) (owner : ℕ → Fin 3)
    (hsurvive : ∀ i, child i ∉ B)
    (howner : ∀ time,
      (certificate.owner (quittingSingletonMeshBlock
        (quittingCyclicOrbit phase time))).1 = child (owner time)) :
    (∀ time other, other ≠ child (owner time) →
      certificate.deletedRootSequence B m phase time other = PMF.pure false) ∧
    (∀ time,
      (certificate.deletedRootSequence B m phase time
        (child (owner time)) true).toReal < 1) ∧
    quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward
        (certificate.deletedRootSequence B m phase) 0) = 0 ∧
    (∀ time i, quittingSoloReward reward (child i) (child i) ≤
      quittingRootSequenceTerminalValue reward
        (certificate.deletedRootSequence B m phase) (child i) time) ∧
    (∀ time, 0 < (certificate.deletedRootSequence B m phase time
        (child (owner time)) true).toReal →
      quittingRootSequenceTerminalValue reward
          (certificate.deletedRootSequence B m phase)
          (child (owner time)) time =
        quittingSoloReward reward (child (owner time)) (child (owner time))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro time other hne
    exact certificate.deletedRootSequence_solo B m phase time other
      (by simpa only [howner time] using hne)
  · intro time
    simpa only [howner time] using
      certificate.deletedRootSequence_hazard_lt_one B m phase time
  · exact certificate.deletedRootSequence_liveMassLimit_eq_zero B m hm phase
  · intro time i
    exact certificate.deletedRootSequence_soloFloor B m hm phase time
      ⟨child i, hsurvive i⟩
  · intro time _
    simpa only [howner time] using
      certificate.deletedRootSequence_owner_tie B m hm phase time

/-- The certificate's finite intensity cap bounds the actual parent hazard
at every mesh date. -/
theorem deletedRootSequence_hazard_le_intensity_div
    [DecidableEq ι]
    (m : ℕ) (phase : Fin (L * m))
    (child : Fin 3 ↪ ι) (owner : ℕ → Fin 3)
    (howner : ∀ time,
      (certificate.owner (quittingSingletonMeshBlock
        (quittingCyclicOrbit phase time))).1 = child (owner time))
    (time : ℕ) :
    (certificate.deletedRootSequence B m phase time
      (child (owner time)) true).toReal ≤
      balancedSingletonCycleIntensityCap certificate / (m : ℝ) := by
  let block := quittingSingletonMeshBlock (quittingCyclicOrbit phase time)
  rw [← howner time]
  rw [certificate.deletedRootSequence_apply_survivor B]
  rw [certificate.rootSequence_owner_hazard]
  exact quittingMeshHazard_le_intensityBound_div certificate.hazard
    certificate.hazard_lt_one
    (balancedSingletonCycleIntensityCap_bound certificate) block

/-- On the actual Never-lifted schedule, a parent's singleton floor holds
on every tail exactly when its actual inverse-row coefficients are nonnegative.
The tested player may be deleted or surviving. -/
theorem deletedRootSequence_singletonFloor_on_tail_iff_inverseRow_nonneg
    [Fintype ι] [DecidableEq ι]
    (m : ℕ) (hm : 0 < m) (phase : Fin (L * m))
    (child : Fin 3 ↪ ι) (owner : ℕ → Fin 3)
    (hsurvive : ∀ i, child i ∉ B)
    (howner : ∀ time,
      (certificate.owner (quittingSingletonMeshBlock
        (quittingCyclicOrbit phase time))).1 = child (owner time))
    (a b c d e f : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f)
    (hmatrix : (quittingSingletonMatrix reward).submatrix child child =
      directedCycleMatrix a b c d e f)
    (who : ι) (start : ℕ) :
    (∀ time, start ≤ time → quittingSoloReward reward who who ≤
      quittingRootSequenceTerminalValue reward
        (certificate.deletedRootSequence B m phase) who time) ↔
      ∀ j, 0 ≤ Matrix.vecMul
        (fun i => quittingSingletonMatrix reward who (child i))
        ((quittingSingletonMatrix reward).submatrix child child)⁻¹ j := by
  obtain ⟨hsolo, hquit, habsorb, hfloor, htie⟩ :=
    certificate.deletedRootSequence_strictThreeCyclePath
      B m hm phase child owner hsurvive howner
  exact quittingRootSequence_singletonFloor_on_tail_iff_inverseRow_nonneg_of_strictThreeCycle
    reward (certificate.deletedRootSequence B m phase) child owner
    a b c d e f ha hb hc hd he hf hgap hmatrix
    hsolo hquit habsorb hfloor htie who start

/-- A positive inverse-row deficit gives an actual finite pure-time reply
against the parent's Never-lifted suffix profile at any starting date. -/
theorem deletedRootSequence_exists_pureTimeDeviationGain_ge
    [Fintype ι] [DecidableEq ι]
    (m : ℕ) (hm : 0 < m) (phase : Fin (L * m))
    (child : Fin 3 ↪ ι) (owner : ℕ → Fin 3)
    (hsurvive : ∀ i, child i ∉ B)
    (howner : ∀ time,
      (certificate.owner (quittingSingletonMeshBlock
        (quittingCyclicOrbit phase time))).1 = child (owner time))
    (outside : ι) (houtside : outside ∈ B) (start : ℕ)
    (a b c d e f M : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f)
    (hmatrix : (quittingSingletonMatrix reward).submatrix child child =
      directedCycleMatrix a b c d e f)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpositive : 0 < quittingStrictThreeCycleInverseRowDeficit
      reward child a b c d e f outside -
        2 * M * (balancedSingletonCycleIntensityCap certificate / (m : ℝ))) :
    ∃ date : ℕ, start ≤ date ∧
      a * d * e / (b * c * f) ≤
        quittingOpponentSurvivalWeight
          (certificate.deletedRootSequence B m phase) outside start (date - start) ∧
      a * d * e / (b * c * f) *
          (quittingStrictThreeCycleInverseRowDeficit
            reward child a b c d e f outside -
              2 * M * (balancedSingletonCycleIntensityCap certificate / (m : ℝ))) ≤
        quittingTerminalPayoff reward
            (Function.update
              (quittingRootSequenceProfile reward
                (certificate.deletedRootSequence B m phase) start) outside
              (quittingPureTimeBehaviorStrategy reward outside
                (some (date - start)))) outside -
          quittingTerminalPayoff reward
            (quittingRootSequenceProfile reward
              (certificate.deletedRootSequence B m phase) start) outside := by
  obtain ⟨hsolo, hquit, habsorb, hfloor, htie⟩ :=
    certificate.deletedRootSequence_strictThreeCyclePath
      B m hm phase child owner hsurvive howner
  have houtside' : ∀ i, outside ≠ child i := by
    intro i heq
    exact hsurvive i (heq ▸ houtside)
  have hhazard : ∀ time,
      (certificate.deletedRootSequence B m phase time
        (child (owner time)) true).toReal ≤
        balancedSingletonCycleIntensityCap certificate / (m : ℝ) := by
    intro time
    exact certificate.deletedRootSequence_hazard_le_intensity_div
      B m phase child owner howner time
  exact exists_pureTimeDeviationGain_ge_of_strictThreeCycle_from_start
    reward (certificate.deletedRootSequence B m phase) child owner start
    outside houtside' a b c d e f M
    (balancedSingletonCycleIntensityCap certificate / (m : ℝ))
    ha hb hc hd he hf hgap hmatrix hsolo hquit hhazard habsorb
    hfloor htie hreward hpositive

/-- Every suffix of the same lifted schedule obeys the quantitative bound
for the outsider's unrestricted behavioral response debt. -/
theorem deletedRootSequence_behaviorDeviationDebt_ge
    [Fintype ι] [DecidableEq ι]
    (m : ℕ) (hm : 0 < m) (phase : Fin (L * m))
    (child : Fin 3 ↪ ι) (owner : ℕ → Fin 3)
    (hsurvive : ∀ i, child i ∉ B)
    (howner : ∀ time,
      (certificate.owner (quittingSingletonMeshBlock
        (quittingCyclicOrbit phase time))).1 = child (owner time))
    (outside : ι) (houtside : outside ∈ B) (start : ℕ)
    (a b c d e f M : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f)
    (hmatrix : (quittingSingletonMatrix reward).submatrix child child =
      directedCycleMatrix a b c d e f)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    a * d * e / (b * c * f) *
        max (quittingStrictThreeCycleInverseRowDeficit
          reward child a b c d e f outside -
            2 * M * (balancedSingletonCycleIntensityCap certificate / (m : ℝ))) 0 ≤
      quittingBehaviorDeviationPayoffCap reward
          (quittingRootSequenceProfile reward
            (certificate.deletedRootSequence B m phase) start) outside -
        quittingTerminalPayoff reward
          (quittingRootSequenceProfile reward
            (certificate.deletedRootSequence B m phase) start) outside := by
  obtain ⟨hsolo, hquit, habsorb, hfloor, htie⟩ :=
    certificate.deletedRootSequence_strictThreeCyclePath
      B m hm phase child owner hsurvive howner
  have houtside' : ∀ i, outside ≠ child i := by
    intro i heq
    exact hsurvive i (heq ▸ houtside)
  have hhazard : ∀ time,
      (certificate.deletedRootSequence B m phase time
        (child (owner time)) true).toReal ≤
        balancedSingletonCycleIntensityCap certificate / (m : ℝ) := by
    intro time
    exact certificate.deletedRootSequence_hazard_le_intensity_div
      B m phase child owner howner time
  exact quittingBehaviorDeviationDebt_ge_of_strictThreeCycle_from_start
    reward (certificate.deletedRootSequence B m phase) child owner start
    outside houtside' a b c d e f M
    (balancedSingletonCycleIntensityCap certificate / (m : ℝ))
    ha hb hc hd he hf hgap hmatrix hsolo hquit hhazard habsorb
    hfloor htie hreward

/-! A complete labeling of a three-player survivor set determines the
strict-cycle owner sequence directly from the certificate. -/

/-- The parent embedding induced by a labeling of all three survivors. -/
def deletedThreeChild (label : Fin 3 ≃ QuittingBlockSurvivor B) : Fin 3 ↪ ι where
  toFun i := (label i).1
  inj' := by
    intro i j hij
    exact label.injective (Subtype.ext hij)

/-- The actual mesh owner expressed in the three-survivor labeling. -/
def deletedThreeOwner (label : Fin 3 ≃ QuittingBlockSurvivor B)
    {m : ℕ}
    (phase : Fin (L * m)) : ℕ → Fin 3 :=
  fun time => label.symm
    (certificate.owner (quittingSingletonMeshBlock (quittingCyclicOrbit phase time)))

theorem deletedThreeOwner_compatible
    {m : ℕ}
    (label : Fin 3 ≃ QuittingBlockSurvivor B) (phase : Fin (L * m))
    (time : ℕ) :
    (certificate.owner (quittingSingletonMeshBlock
      (quittingCyclicOrbit phase time))).1 =
        deletedThreeChild B label (certificate.deletedThreeOwner B label phase time) := by
  change (certificate.owner (quittingSingletonMeshBlock
      (quittingCyclicOrbit phase time))).1 =
    (label (label.symm (certificate.owner (quittingSingletonMeshBlock
      (quittingCyclicOrbit phase time))))).1
  exact congrArg Subtype.val (label.apply_symm_apply _).symm

/-- Three-survivor specialization of the actual parent floor criterion. -/
theorem deletedThree_singletonFloor_on_tail_iff_inverseRow_nonneg
    [Fintype ι] [DecidableEq ι]
    (m : ℕ) (hm : 0 < m) (phase : Fin (L * m))
    (label : Fin 3 ≃ QuittingBlockSurvivor B)
    (a b c d e f : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f)
    (hmatrix : (quittingSingletonMatrix reward).submatrix
      (deletedThreeChild B label) (deletedThreeChild B label) =
        directedCycleMatrix a b c d e f)
    (who : ι) (start : ℕ) :
    (∀ time, start ≤ time → quittingSoloReward reward who who ≤
      quittingRootSequenceTerminalValue reward
        (certificate.deletedRootSequence B m phase) who time) ↔
      ∀ j, 0 ≤ Matrix.vecMul
        (fun i => quittingSingletonMatrix reward who (deletedThreeChild B label i))
        ((quittingSingletonMatrix reward).submatrix
          (deletedThreeChild B label) (deletedThreeChild B label))⁻¹ j := by
  let child := deletedThreeChild B label
  let owner := certificate.deletedThreeOwner B label phase
  have hsurvive : ∀ i, child i ∉ B := by
    intro i
    exact (label i).2
  have howner : ∀ time,
      (certificate.owner (quittingSingletonMeshBlock
        (quittingCyclicOrbit phase time))).1 = child (owner time) := by
    intro time
    exact certificate.deletedThreeOwner_compatible B label phase time
  exact certificate.deletedRootSequence_singletonFloor_on_tail_iff_inverseRow_nonneg
    B m hm phase child owner hsurvive howner
    a b c d e f ha hb hc hd he hf hgap hmatrix who start

/-- Three-survivor specialization of the actual finite deadline witness. -/
theorem deletedThree_exists_pureTimeDeviationGain_ge
    [Fintype ι] [DecidableEq ι]
    (m : ℕ) (hm : 0 < m) (phase : Fin (L * m))
    (label : Fin 3 ≃ QuittingBlockSurvivor B)
    (outside : ι) (houtside : outside ∈ B) (start : ℕ)
    (a b c d e f M : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f)
    (hmatrix : (quittingSingletonMatrix reward).submatrix
      (deletedThreeChild B label) (deletedThreeChild B label) =
        directedCycleMatrix a b c d e f)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpositive : 0 < quittingStrictThreeCycleInverseRowDeficit
      reward (deletedThreeChild B label) a b c d e f outside -
        2 * M * (balancedSingletonCycleIntensityCap certificate / (m : ℝ))) :
    ∃ date : ℕ, start ≤ date ∧
      a * d * e / (b * c * f) ≤
        quittingOpponentSurvivalWeight
          (certificate.deletedRootSequence B m phase) outside start (date - start) ∧
      a * d * e / (b * c * f) *
          (quittingStrictThreeCycleInverseRowDeficit
            reward (deletedThreeChild B label) a b c d e f outside -
              2 * M * (balancedSingletonCycleIntensityCap certificate / (m : ℝ))) ≤
        quittingTerminalPayoff reward
            (Function.update
              (quittingRootSequenceProfile reward
                (certificate.deletedRootSequence B m phase) start) outside
              (quittingPureTimeBehaviorStrategy reward outside
                (some (date - start)))) outside -
          quittingTerminalPayoff reward
            (quittingRootSequenceProfile reward
              (certificate.deletedRootSequence B m phase) start) outside := by
  let child := deletedThreeChild B label
  let owner := certificate.deletedThreeOwner B label phase
  have hsurvive : ∀ i, child i ∉ B := by
    intro i
    exact (label i).2
  have howner : ∀ time,
      (certificate.owner (quittingSingletonMeshBlock
        (quittingCyclicOrbit phase time))).1 = child (owner time) := by
    intro time
    exact certificate.deletedThreeOwner_compatible B label phase time
  exact certificate.deletedRootSequence_exists_pureTimeDeviationGain_ge
    B m hm phase child owner hsurvive howner outside houtside start
    a b c d e f M ha hb hc hd he hf hgap hmatrix hreward hpositive

/-- Three-survivor specialization of the actual full behavioral debt bound. -/
theorem deletedThree_behaviorDeviationDebt_ge
    [Fintype ι] [DecidableEq ι]
    (m : ℕ) (hm : 0 < m) (phase : Fin (L * m))
    (label : Fin 3 ≃ QuittingBlockSurvivor B)
    (outside : ι) (houtside : outside ∈ B) (start : ℕ)
    (a b c d e f M : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f)
    (hmatrix : (quittingSingletonMatrix reward).submatrix
      (deletedThreeChild B label) (deletedThreeChild B label) =
        directedCycleMatrix a b c d e f)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    a * d * e / (b * c * f) *
        max (quittingStrictThreeCycleInverseRowDeficit
          reward (deletedThreeChild B label) a b c d e f outside -
            2 * M * (balancedSingletonCycleIntensityCap certificate / (m : ℝ))) 0 ≤
      quittingBehaviorDeviationPayoffCap reward
          (quittingRootSequenceProfile reward
            (certificate.deletedRootSequence B m phase) start) outside -
        quittingTerminalPayoff reward
          (quittingRootSequenceProfile reward
            (certificate.deletedRootSequence B m phase) start) outside := by
  let child := deletedThreeChild B label
  let owner := certificate.deletedThreeOwner B label phase
  have hsurvive : ∀ i, child i ∉ B := by
    intro i
    exact (label i).2
  have howner : ∀ time,
      (certificate.owner (quittingSingletonMeshBlock
        (quittingCyclicOrbit phase time))).1 = child (owner time) := by
    intro time
    exact certificate.deletedThreeOwner_compatible B label phase time
  exact certificate.deletedRootSequence_behaviorDeviationDebt_ge
    B m hm phase child owner hsurvive howner outside houtside start
    a b c d e f M ha hb hc hd he hf hgap hmatrix hreward

end GameTheory.BalancedSingletonCycleCertificate
