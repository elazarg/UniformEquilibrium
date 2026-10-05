import MathUE.PMFProduct.PureUpdateExpectation
import UniformEquilibrium.Quitting.Root.OpponentCoalitionPayoff
import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport

/-! # Full-coalition endpoint identities

The exact identities retain every coalition, arbitrary signed weights, and all
zero or sure hazards. Support pruning is a separate consequence, not a premise
of the finite Fubini identity. No Nash or reward-sign assumption is used.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Pinning Quit averages the inserted coalition payoff against the original
full product law, independently of the prescribed hazard of the pinned player. -/
theorem quittingRootQuitPayoff_eq_sum_fullCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (player : ι) :
    quittingRootQuitPayoff reward tail root player =
      ∑ coalition : Finset ι, quittingRootCoalitionMass root coalition *
        reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_update_pure]
  have hroot : root = fun who =>
      if who ∈ (Finset.univ : Finset ι) then root who else PMF.pure false := by
    funext who
    simp
  rw [hroot, expect_pmfPi_boolFamily_eq_sum_powerset']
  simp only [Finset.mem_univ, ite_true, Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro coalition _
  have hquitters : quittingQuitters
      (Function.update (fun who => if who ∈ coalition then true else false)
        player true) = insert player coalition := by
    ext who
    by_cases hwho : who = player <;> simp [quittingQuitters, hwho]
  rw [quittingRootPayoff_eq_stageCoalitionPayoff, hquitters]
  simp only [quittingStageCoalitionPayoff, Finset.insert_nonempty, dite_true]
  rfl

/-- The player's Continue factor completes the opponent atom to the full
atom. This identity also holds when that factor or any opponent factor is zero. -/
theorem quittingContinueProbability_mul_opponentCoalitionMass
    (root : ι → PMF Bool) (player : ι) (coalition : Finset ι)
    (hnot : player ∉ coalition) :
    (root player false).toReal * quittingOpponentCoalitionMass root player coalition =
      quittingRootCoalitionMass root coalition := by
  unfold quittingOpponentCoalitionMass quittingRootCoalitionMass
    quittingRootQuitRates coalitionMass
  simp_rw [← pmfBool_false_toReal]
  have herase : Finset.univ.erase player \ coalition =
      (Finset.univ \ coalition).erase player := by
    ext who
    simp [and_comm]
  rw [Finset.compl_eq_univ_sdiff, herase, mul_left_comm]
  congr 1
  exact Finset.mul_prod_erase (Finset.univ \ coalition)
    (fun who => (root who false).toReal)
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)

/-- The empty full atom is the literal all-Continue probability. -/
theorem quittingRootCoalitionMass_empty_eq_continueMass
    (root : ι → PMF Bool) :
    quittingRootCoalitionMass root ∅ = quittingStationaryContinueMass root := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [quittingRootCoalitionMass, coalitionMass, quittingRootQuitRates,
    pmfBool_false_toReal]

/-- One played-Continue endpoint gap as a full-universe coalition sum. -/
theorem quittingContinueProbability_mul_endpointDifference_eq_fullCoalitionSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (player : ι) :
    (root player false).toReal * quittingRootEndpointDifference reward tail root player =
      ∑ coalition : Finset ι, quittingRootCoalitionMass root coalition *
        (if player ∈ coalition then 0
          else quittingEndpointInsertionToggle reward tail player coalition) := by
  rw [quittingContinueProbability_mul_endpointDifference_eq_sum_atoms]
  have hfilter : (Finset.univ.erase player).powerset =
      (Finset.univ : Finset (Finset ι)).filter (fun coalition => player ∉ coalition) := by
    ext coalition
    simp [Finset.subset_erase]
  rw [hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro coalition _
  by_cases hnot : player ∉ coalition
  · simp only [hnot, not_false_eq_true, ite_true, ite_false]
    rw [quittingContinueProbability_mul_opponentCoalitionMass root player coalition hnot]
  · simp [hnot]

/-- Finite Fubini for arbitrary selected players and arbitrary real weights.
Coalitions range over the whole universe; neither support nor zero-outside
weight assumptions belong to this identity. -/
theorem quittingWeightedEndpointGap_eq_fullCoalitionSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (selected : Finset ι) (weight : ι → ℝ) :
    (∑ player ∈ selected, weight player * (root player false).toReal *
        quittingRootEndpointDifference reward tail root player) =
      ∑ coalition : Finset ι, quittingRootCoalitionMass root coalition *
        ∑ player ∈ selected \ coalition,
          weight player * quittingEndpointInsertionToggle reward tail player coalition := by
  calc
    _ = ∑ player ∈ selected, ∑ coalition : Finset ι,
        quittingRootCoalitionMass root coalition *
          (if player ∈ coalition then 0
            else weight player *
              quittingEndpointInsertionToggle reward tail player coalition) := by
      apply Finset.sum_congr rfl
      intro player _
      rw [mul_assoc,
        quittingContinueProbability_mul_endpointDifference_eq_fullCoalitionSum,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro coalition _
      by_cases hmember : player ∈ coalition <;> simp [hmember, mul_left_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro coalition _
      have hfilter : selected.filter (fun player => player ∉ coalition) =
          selected \ coalition := by
        ext player
        simp
      rw [← hfilter, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro player _
      by_cases hmember : player ∈ coalition <;> simp [hmember]

/-- The empty atom separates into the singleton-minus-source charge, while
every nonempty full coalition keeps its entire weighted insertion sum. -/
theorem quittingWeightedEndpointGap_eq_continueCharge_add_nonemptyCoalitionSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (selected : Finset ι) (weight : ι → ℝ) :
    (∑ player ∈ selected, weight player * (root player false).toReal *
        quittingRootEndpointDifference reward tail root player) =
      quittingStationaryContinueMass root *
        (∑ player ∈ selected,
          weight player * (reward (quittingSingletonTerminal player) player - tail player)) +
      ∑ coalition ∈ (Finset.univ : Finset (Finset ι)).erase ∅,
        quittingRootCoalitionMass root coalition *
          ∑ player ∈ selected \ coalition,
            weight player * quittingEndpointInsertionToggle reward tail player coalition := by
  rw [quittingWeightedEndpointGap_eq_fullCoalitionSum,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (∅ : Finset ι))]
  simp only [Finset.sdiff_empty, quittingEndpointInsertionToggle_empty,
    quittingRootCoalitionMass_empty_eq_continueMass]

/-- Exact atoms outside any set containing the positive-hazard support vanish. -/
theorem quittingRootCoalitionMass_eq_zero_of_not_subset_supportContainer
    (root : ι → PMF Bool) (active coalition : Finset ι)
    (hsupport : quittingPositiveHazardSupport root ⊆ active)
    (houtside : ¬ coalition ⊆ active) :
    quittingRootCoalitionMass root coalition = 0 := by
  obtain ⟨player, hplayer, hnot⟩ := Finset.not_subset.mp houtside
  have hzero : (root player true).toReal = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    apply not_lt.mp
    intro hpositive
    apply hnot
    apply hsupport
    change player ∈ Finset.univ.filter (fun who => 0 < (root who true).toReal)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpositive⟩
  exact le_antisymm
    ((quittingRootCoalitionMass_le_quitProbability_of_mem root coalition player hplayer).trans
      hzero.le) (quittingRootCoalitionMass_nonneg root coalition)

/-- With support contained in `active`, only its nonempty proper subsets
survive in the charge identity. The full active atom has an empty insertion sum. -/
theorem quittingWeightedEndpointGap_eq_continueCharge_add_properSubsetSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (active : Finset ι) (weight : ι → ℝ)
    (hsupport : quittingPositiveHazardSupport root ⊆ active) :
    (∑ player ∈ active, weight player * (root player false).toReal *
        quittingRootEndpointDifference reward tail root player) =
      quittingStationaryContinueMass root *
        (∑ player ∈ active,
          weight player * (reward (quittingSingletonTerminal player) player - tail player)) +
      ∑ coalition ∈ (active.powerset.erase ∅).erase active,
        quittingRootCoalitionMass root coalition *
          ∑ player ∈ active \ coalition,
            weight player * quittingEndpointInsertionToggle reward tail player coalition := by
  rw [quittingWeightedEndpointGap_eq_continueCharge_add_nonemptyCoalitionSum]
  congr 1
  symm
  apply Finset.sum_subset
  · intro coalition hcoalition
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hcoalition).2).1, Finset.mem_univ _⟩
  · intro coalition _hcoalition houtside
    by_cases hsubset : coalition ⊆ active
    · have heq : coalition = active := by
        by_contra hne
        exact houtside (by simp_all)
      subst coalition
      simp
    · rw [quittingRootCoalitionMass_eq_zero_of_not_subset_supportContainer
        root active coalition hsupport hsubset, zero_mul]

end GameTheory
