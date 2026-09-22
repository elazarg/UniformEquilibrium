import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotient
import UniformEquilibrium.Quitting.Root.PlayerReindex
import MathUE.Finset.PowersetBernoulliWeight

/-! # Permutation transport of stationary response subset weights -/

noncomputable section

namespace GameTheory

open Math.Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Bernoulli subset mass commutes with a player permutation which fixes
the hazard family. This is the common reindexing step for both Q and H. -/
theorem bernoulliWeight_map_of_invariant
    (e : ι ≃ ι) (hazard : ι → ℝ)
    (hinvariant : ∀ who, hazard (e who) = hazard who)
    (opponents coalition : Finset ι) :
    bernoulliWeight hazard (opponents.map e.toEmbedding)
        (coalition.map e.toEmbedding) =
      bernoulliWeight hazard opponents coalition := by
  unfold bernoulliWeight
  rw [← Finset.map_sdiff]
  simp only [Finset.prod_map]
  simp only [Equiv.toEmbedding_apply, hinvariant]

omit [Fintype ι] in
/-- Reindex an entire opponent-subset expectation without expanding any
coalition or reward coordinate. -/
theorem sum_powerset_bernoulliWeight_map_of_invariant
    (e : ι ≃ ι) (hazard : ι → ℝ)
    (hinvariant : ∀ who, hazard (e who) = hazard who)
    (opponents : Finset ι) (payoff : Finset ι → ℝ) :
    (∑ coalition ∈ (opponents.map e.toEmbedding).powerset,
      bernoulliWeight hazard (opponents.map e.toEmbedding) coalition * payoff coalition) =
      ∑ coalition ∈ opponents.powerset,
        bernoulliWeight hazard opponents coalition *
          payoff (coalition.map e.toEmbedding) := by
  symm
  apply Finset.sum_equiv (Equiv.finsetCongr e)
  · intro coalition
    simp only [Finset.mem_powerset, Equiv.finsetCongr_apply]
    exact (Finset.map_subset_map).symm
  · intro coalition hcoalition
    simp only [Equiv.finsetCongr_apply]
    rw [bernoulliWeight_map_of_invariant e hazard hinvariant]

omit [Fintype ι] in
/-- An affine change of every terminal payoff adds exactly its constant to
the complete opponent-subset expectation. -/
theorem sum_powerset_bernoulliWeight_map_add
    (e : ι ≃ ι) (hazard : ι → ℝ)
    (hinvariant : ∀ who, hazard (e who) = hazard who)
    (opponents : Finset ι) (first second : Finset ι → ℝ) (offset : ℝ)
    (hpayoff : ∀ coalition ∈ opponents.powerset,
      second (coalition.map e.toEmbedding) = first coalition + offset) :
    (∑ coalition ∈ (opponents.map e.toEmbedding).powerset,
      bernoulliWeight hazard (opponents.map e.toEmbedding) coalition *
        second coalition) =
      (∑ coalition ∈ opponents.powerset,
        bernoulliWeight hazard opponents coalition * first coalition) + offset := by
  rw [sum_powerset_bernoulliWeight_map_of_invariant e hazard hinvariant]
  calc
    (∑ coalition ∈ opponents.powerset,
        bernoulliWeight hazard opponents coalition *
          second (coalition.map e.toEmbedding)) =
        ∑ coalition ∈ opponents.powerset,
          bernoulliWeight hazard opponents coalition *
            (first coalition + offset) := by
      apply Finset.sum_congr rfl
      intro coalition hcoalition
      rw [hpayoff coalition hcoalition]
    _ = (∑ coalition ∈ opponents.powerset,
          bernoulliWeight hazard opponents coalition * first coalition) +
          (∑ coalition ∈ opponents.powerset,
            bernoulliWeight hazard opponents coalition) * offset := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    _ = _ := by rw [sum_bernoulliWeight]; ring

omit [Fintype ι] in
/-- The nonempty opponent-subset mass is one minus the all-Continue atom. -/
theorem sum_nonempty_bernoulliWeight
    (hazard : ι → ℝ) (opponents : Finset ι) :
    (∑ coalition ∈ opponents.powerset.erase ∅,
      bernoulliWeight hazard opponents coalition) =
      1 - ∏ who ∈ opponents, (1 - hazard who) := by
  have hempty : (∅ : Finset ι) ∈ opponents.powerset := by simp
  have hsplit := Finset.add_sum_erase opponents.powerset
    (bernoulliWeight hazard opponents) hempty
  rw [sum_bernoulliWeight] at hsplit
  have hemptyValue : bernoulliWeight hazard opponents ∅ =
      ∏ who ∈ opponents, (1 - hazard who) := by
    simp [bernoulliWeight]
  rw [hemptyValue] at hsplit
  linarith

omit [Fintype ι] in
/-- The affine payoff correction on nonempty opponent coalitions is the
probability that some opponent acts, times the constant shift. -/
theorem sum_nonempty_powerset_bernoulliWeight_map_add
    (e : ι ≃ ι) (hazard : ι → ℝ)
    (hinvariant : ∀ who, hazard (e who) = hazard who)
    (opponents : Finset ι) (first second : Finset ι → ℝ) (offset : ℝ)
    (hpayoff : ∀ coalition ∈ opponents.powerset.erase ∅,
      second (coalition.map e.toEmbedding) = first coalition + offset) :
    (∑ coalition ∈ (opponents.map e.toEmbedding).powerset.erase ∅,
      bernoulliWeight hazard (opponents.map e.toEmbedding) coalition *
        second coalition) =
      (∑ coalition ∈ opponents.powerset.erase ∅,
        bernoulliWeight hazard opponents coalition * first coalition) +
        offset * (1 - ∏ who ∈ opponents, (1 - hazard who)) := by
  have htransport :
      (∑ coalition ∈ (opponents.map e.toEmbedding).powerset.erase ∅,
        bernoulliWeight hazard (opponents.map e.toEmbedding) coalition *
          second coalition) =
        ∑ coalition ∈ opponents.powerset.erase ∅,
          bernoulliWeight hazard opponents coalition *
            second (coalition.map e.toEmbedding) := by
    symm
    apply Finset.sum_equiv (Equiv.finsetCongr e)
    · intro coalition
      simp only [Finset.mem_erase, Finset.mem_powerset,
        Equiv.finsetCongr_apply, Finset.map_subset_map]
      constructor
      · rintro ⟨hne, hsubset⟩
        refine ⟨?_, hsubset⟩
        intro hmap
        exact hne (Finset.map_eq_empty.mp hmap)
      · rintro ⟨hne, hsubset⟩
        refine ⟨?_, hsubset⟩
        intro hempty
        exact hne (by simp [hempty])
    · intro coalition _
      simp only [Equiv.finsetCongr_apply]
      rw [bernoulliWeight_map_of_invariant e hazard hinvariant]
  rw [htransport]
  calc
    (∑ coalition ∈ opponents.powerset.erase ∅,
        bernoulliWeight hazard opponents coalition *
          second (coalition.map e.toEmbedding)) =
        ∑ coalition ∈ opponents.powerset.erase ∅,
          bernoulliWeight hazard opponents coalition *
            (first coalition + offset) := by
      apply Finset.sum_congr rfl
      intro coalition hcoalition
      rw [hpayoff coalition hcoalition]
    _ = (∑ coalition ∈ opponents.powerset.erase ∅,
          bernoulliWeight hazard opponents coalition * first coalition) +
          (∑ coalition ∈ opponents.powerset.erase ∅,
            bernoulliWeight hazard opponents coalition) * offset := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    _ = _ := by rw [sum_nonempty_bernoulliWeight]; ring

/-- Opponent Continue mass is invariant under a relabeling that fixes the
hazard vector. -/
theorem continueMassExcl_equiv_of_invariant
    (e : ι ≃ ι) (hazard : ι → ℝ)
    (hinvariant : ∀ who, hazard (e who) = hazard who) (who : ι) :
    continueMassExcl hazard (e who) = continueMassExcl hazard who := by
  have herase : (Finset.univ.erase who).map e.toEmbedding =
      Finset.univ.erase (e who) := by simp
  unfold continueMassExcl
  rw [← herase, Finset.prod_map]
  simp only [Equiv.toEmbedding_apply, hinvariant]

/-- The pure-Quit expectation changes by the recipient's centered row
offset under a player relabeling fixing the hazard vector. -/
theorem sigmaValue_equiv_centered
    (e : ι ≃ ι) (hazard : ι → ℝ)
    (hinvariant : ∀ who, hazard (e who) = hazard who)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (offset : ℝ)
    (hcenter : ∀ terminal,
      reward (quittingCoalitionEquiv e terminal) (e who) =
        reward terminal who + offset) :
    sigmaValue (weightOfReward reward) hazard (e who) =
      sigmaValue (weightOfReward reward) hazard who + offset := by
  have herase : (Finset.univ.erase who).map e.toEmbedding =
      Finset.univ.erase (e who) := by simp
  have hsum := sum_powerset_bernoulliWeight_map_add e hazard hinvariant
    (Finset.univ.erase who)
    (fun coalition => weightOfReward reward (insert who coalition) who)
    (fun coalition => weightOfReward reward (insert (e who) coalition) (e who))
    offset (by
      intro coalition _
      have h := hcenter ⟨insert who coalition, by simp⟩
      simpa [weightOfReward, quittingCoalitionEquiv, Finset.map_insert] using h)
  simpa only [sigmaValue, bernoulliWeight, herase] using hsum

/-- The pure-Continue absorbing expectation changes by the centered offset
only when an opponent quits. -/
theorem excludedValue_equiv_centered
    (e : ι ≃ ι) (hazard : ι → ℝ)
    (hinvariant : ∀ who, hazard (e who) = hazard who)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (offset : ℝ)
    (hcenter : ∀ terminal,
      reward (quittingCoalitionEquiv e terminal) (e who) =
        reward terminal who + offset) :
    excludedValue (weightOfReward reward) hazard (e who) =
      excludedValue (weightOfReward reward) hazard who +
        offset * (1 - continueMassExcl hazard who) := by
  have herase : (Finset.univ.erase who).map e.toEmbedding =
      Finset.univ.erase (e who) := by simp
  have hsum := sum_nonempty_powerset_bernoulliWeight_map_add e hazard hinvariant
    (Finset.univ.erase who)
    (fun coalition => weightOfReward reward coalition who)
    (fun coalition => weightOfReward reward coalition (e who)) offset (by
      intro coalition hcoalition
      have hnonempty : coalition.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hcoalition).1
      have hmapped : (coalition.map e.toEmbedding).Nonempty :=
        Finset.map_nonempty.mpr hnonempty
      have h := hcenter ⟨coalition, hnonempty⟩
      simpa [weightOfReward, quittingCoalitionEquiv, hnonempty, hmapped] using h)
  simpa only [excludedValue, bernoulliWeight, continueMassExcl, herase] using hsum

/-- Raw zero-discount displacement is permutation-equivariant for one
centered recipient row, with no condition on other recipients. -/
theorem quittingDiscountedDisplacement_equiv_centered
    (e : ι ≃ ι) (hazard : ι → ℝ)
    (hinvariant : ∀ who, hazard (e who) = hazard who)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (offset : ℝ)
    (hcenter : ∀ terminal,
      reward (quittingCoalitionEquiv e terminal) (e who) =
        reward terminal who + offset) :
    quittingDiscountedDisplacement reward 0 hazard (e who) =
      quittingDiscountedDisplacement reward 0 hazard who := by
  rw [quittingDiscountedDisplacement, quittingDiscountedDisplacement,
    continueMassExcl_equiv_of_invariant e hazard hinvariant who,
    sigmaValue_equiv_centered e hazard hinvariant reward who offset hcenter,
    excludedValue_equiv_centered e hazard hinvariant reward who offset hcenter]
  ring

end GameTheory
