import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenter
import UniformEquilibrium.Quitting.Root.RewardStability
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine
import MathUE.ProbabilityMassFunction.IntervalBernoulliSimplex
import MathUE.Topology.RectangularPoincareMiranda

/-! # Internally produced interior active root for every nearby reward table -/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open Math.ProbabilityMassFunction _root_.Math.Topology

/-- The active cube, with a sure anchor, in continuous simplex coordinates. -/
def nearbySimplex (probability : Fin 3 → ℝ) : QuittingRootSimplex (Fin 4) :=
  ![intervalBernoulliSimplex (probability 0), intervalBernoulliSimplex (probability 1),
    intervalBernoulliSimplex (probability 2), stdSimplexEquiv (PMF.pure true)]

def nearbyRoot (probability : Fin 3 → ℝ) : Fin 4 → PMF Bool :=
  quittingRootOfSimplex (nearbySimplex probability)

theorem nearbyRoot_eq_rootOf (probability : Fin 3 → ℝ) :
    nearbyRoot probability = rootOf
      (quittingRootOfSimplex (nearbySimplex probability) 0)
      (quittingRootOfSimplex (nearbySimplex probability) 1)
      (quittingRootOfSimplex (nearbySimplex probability) 2) := by
  funext who
  fin_cases who <;> simp [nearbyRoot, nearbySimplex, rootOf, quittingRootOfSimplex]

@[simp] theorem nearbyRoot_anchor (probability : Fin 3 → ℝ) :
    nearbyRoot probability 3 = PMF.pure true := by
  simp [nearbyRoot, nearbySimplex, quittingRootOfSimplex]

theorem nearbyRoot_hasSureQuitter (probability : Fin 3 → ℝ) :
    QuittingRootHasSureQuitter (nearbyRoot probability) :=
  ⟨3, nearbyRoot_anchor probability⟩

@[simp] theorem nearbyRoot_active_true (probability : Fin 3 → ℝ) (active : Fin 3) :
    (nearbyRoot probability active.castSucc true).toReal =
      unitIntervalClip (probability active) := by
  fin_cases active <;> simp [nearbyRoot, nearbySimplex]

@[simp] theorem nearbyRoot_active_false (probability : Fin 3 → ℝ) (active : Fin 3) :
    (nearbyRoot probability active.castSucc false).toReal =
      1 - unitIntervalClip (probability active) := by
  fin_cases active <;> simp [nearbyRoot, nearbySimplex]

theorem continuous_nearbySimplex : Continuous nearbySimplex := by
  apply continuous_pi
  intro who
  fin_cases who
  · exact continuous_intervalBernoulliSimplex.comp (continuous_apply 0)
  · exact continuous_intervalBernoulliSimplex.comp (continuous_apply 1)
  · exact continuous_intervalBernoulliSimplex.comp (continuous_apply 2)
  · exact continuous_const

def nearbyGap
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ) (active : Fin 3) : ℝ :=
  quittingRootEndpointDifference table 0 (nearbyRoot probability) active.castSucc

/-- The coordinate permutation is exactly the packet's `(Delta1,Delta2,-Delta0)`. -/
def nearbyField
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![nearbyGap table probability 1, nearbyGap table probability 2,
    -nearbyGap table probability 0]

theorem continuous_nearbyGap
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (active : Fin 3) :
    Continuous (fun probability => nearbyGap table probability active) := by
  have hmap : Continuous (fun probability : Fin 3 → ℝ =>
      ((0 : Payoff (Fin 4)), nearbySimplex probability)) :=
    continuous_const.prodMk continuous_nearbySimplex
  simpa only [Function.comp_def, nearbyGap, nearbyRoot] using
    (continuous_quittingRootEndpointDifference_simplex table active.castSucc).comp hmap

theorem continuous_nearbyField
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    Continuous (nearbyField table) := by
  apply continuous_pi
  intro coordinate
  fin_cases coordinate
  · exact continuous_nearbyGap table 1
  · exact continuous_nearbyGap table 2
  · exact (continuous_nearbyGap table 0).neg

theorem nearbyField_center (probability : Fin 3 → ℝ) (coordinate : Fin 3)
    (hbox : probability ∈ Set.Icc (fun _ => (1 / 4 : ℝ)) (fun _ => (3 / 4 : ℝ))) :
    nearbyField reward probability coordinate = 2 * probability coordinate - 1 := by
  have hclip : ∀ active, unitIntervalClip (probability active) = probability active := by
    intro active
    apply unitIntervalClip_eq_self <;> linarith [hbox.1 active, hbox.2 active]
  fin_cases coordinate
  · simp [nearbyField, nearbyGap, nearbyRoot_eq_rootOf, endpointDifference_one,
      nearbySimplex, hclip]
  · simp [nearbyField, nearbyGap, nearbyRoot_eq_rootOf, endpointDifference_two,
      nearbySimplex, hclip]
  · simp [nearbyField, nearbyGap, nearbyRoot_eq_rootOf, endpointDifference_zero,
      nearbySimplex, hclip]

theorem nearbyField_close
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta)
    (probability : Fin 3 → ℝ) (coordinate : Fin 3) :
    |nearbyField table probability coordinate - nearbyField reward probability coordinate| ≤
      2 * delta := by
  have hgap : ∀ active : Fin 3,
      |nearbyGap table probability active - nearbyGap reward probability active| ≤
        2 * delta := by
    intro active
    exact abs_quittingRootEndpointDifference_sub_of_reward_close
      table reward 0 (nearbyRoot probability) active.castSucc hdelta
      (fun terminal => hclose terminal active.castSucc)
  fin_cases coordinate
  · exact hgap 1
  · exact hgap 2
  · change |-nearbyGap table probability 0 - -nearbyGap reward probability 0| ≤ 2 * delta
    rw [neg_sub_neg, abs_sub_comm]
    exact hgap 0

/-- An actual interior zero is produced from signs; no zero/root certificate is input. -/
theorem exists_nearby_interior_active_root
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {delta : ℝ} (hdelta : 0 ≤ delta) (hsmall : delta < 1 / 8)
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta) :
    ∃ probability : Fin 3 → ℝ,
      (∀ active, 1 / 4 < probability active ∧ probability active < 3 / 4) ∧
      ∀ active, nearbyGap table probability active = 0 := by
  have hlower : ∀ probability ∈ Set.Icc (fun _ => (1 / 4 : ℝ)) (fun _ => (3 / 4 : ℝ)),
      ∀ coordinate, probability coordinate = 1 / 4 →
        nearbyField table probability coordinate < 0 := by
    intro probability hbox coordinate hface
    have hbound := nearbyField_close table hdelta hclose probability coordinate
    rw [nearbyField_center probability coordinate hbox, hface] at hbound
    linarith [abs_le.mp hbound]
  have hupper : ∀ probability ∈ Set.Icc (fun _ => (1 / 4 : ℝ)) (fun _ => (3 / 4 : ℝ)),
      ∀ coordinate, probability coordinate = 3 / 4 →
        0 < nearbyField table probability coordinate := by
    intro probability hbox coordinate hface
    have hbound := nearbyField_close table hdelta hclose probability coordinate
    rw [nearbyField_center probability coordinate hbox, hface] at hbound
    linarith [abs_le.mp hbound]
  obtain ⟨probability, _, hinterior, hzero⟩ := exists_rectangular_zero_of_strict_face_signs
    (fun _ : Fin 3 => (1 / 4 : ℝ)) (fun _ => (3 / 4 : ℝ)) (nearbyField table)
    (fun _ => by norm_num) (continuous_nearbyField table) hlower hupper
  refine ⟨probability, hinterior, ?_⟩
  intro active
  have hfirst := hzero 0
  have hsecond := hzero 1
  have hthird := hzero 2
  fin_cases active
  · simpa [nearbyField] using neg_eq_zero.mp hthird
  · exact hfirst
  · exact hsecond

theorem nearbyRoot_update_active_hasSureQuitter
    (probability : Fin 3 → ℝ) (active : Fin 3) (action : Bool) :
    QuittingRootHasSureQuitter (Function.update (nearbyRoot probability)
      active.castSucc (PMF.pure action)) := by
  refine ⟨3, ?_⟩
  have hdifferent : (3 : Fin 4) ≠ active.castSucc := by fin_cases active <;> decide
  rw [Function.update_of_ne hdifferent, nearbyRoot_anchor]

/-- The anchor covers both active endpoints, so active gaps ignore every tail value. -/
theorem nearbyGap_eq_endpointDifference_tail
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (tail : Payoff (Fin 4)) (probability : Fin 3 → ℝ) (active : Fin 3) :
    nearbyGap table probability active =
      quittingRootEndpointDifference table tail (nearbyRoot probability) active.castSucc := by
  unfold nearbyGap quittingRootEndpointDifference quittingRootQuitPayoff quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_of_hasSureQuitter table _
    (nearbyRoot_update_active_hasSureQuitter probability active true) 0 tail,
    quittingRootExpectedPayoff_eq_of_hasSureQuitter table _
      (nearbyRoot_update_active_hasSureQuitter probability active false) 0 tail]

end GameTheory.AdaptiveChildCenter
