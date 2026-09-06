import MathUE.PMFProduct.Basic

/-! # Rigidity of a pair-only Boolean product row -/

noncomputable section

namespace Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Active coordinates of a Boolean product action. -/
def booleanActiveSet (action : ι → Bool) : Finset ι :=
  Finset.univ.filter fun who ↦ action who

/-- A positive product atom remains positive after changing one coordinate
to another positive marginal atom. -/
private theorem pmfPi_update_mem_support
    (root : ι → PMF Bool) (action : ι → Bool)
    (haction : action ∈ (pmfPi root).support) (who : ι) (choice : Bool)
    (hchoice : choice ∈ (root who).support) :
    Function.update action who choice ∈ (pmfPi root).support := by
  simp only [PMF.mem_support_iff, pmfPi_apply] at haction hchoice ⊢
  rw [Finset.prod_ne_zero_iff] at haction ⊢
  intro other _
  by_cases hother : other = who
  · subst other
    simpa using hchoice
  · simpa [Function.update_of_ne hother] using haction other (Finset.mem_univ other)

/-- If every nonempty supported atom of a Boolean product row has one fixed
cardinality at least two, any supported nonempty atom is deterministic. -/
theorem fixedCardProductRow_eq_deterministic
    (root : ι → PMF Bool) (action : ι → Bool)
    (haction : action ∈ (pmfPi root).support)
    (hactionNonempty : (booleanActiveSet action).Nonempty)
    (cardinality : ℕ) (hcardinality : 2 ≤ cardinality)
    (hfixedCard : ∀ candidate ∈ (pmfPi root).support,
      (booleanActiveSet candidate).Nonempty →
        (booleanActiveSet candidate).card = cardinality) :
    (booleanActiveSet action).card = cardinality ∧
      ∀ who, root who = PMF.pure (action who) := by
  have hcard := hfixedCard action haction hactionNonempty
  refine ⟨hcard, ?_⟩
  intro who
  have hsupp : (root who).support = {action who} := by
    ext choice
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hchoice
      by_contra hne
      have hflip := pmfPi_update_mem_support root action haction who choice hchoice
      have hshape := hfixedCard (Function.update action who choice) hflip
      by_cases hwho : who ∈ booleanActiveSet action
      · have hupdated : booleanActiveSet (Function.update action who choice) =
            (booleanActiveSet action).erase who := by
          ext other
          by_cases hother : other = who
          · subst other
            have hactionTrue : action who = true := by
              simpa [booleanActiveSet] using hwho
            cases choice <;> simp_all [booleanActiveSet]
          · simp [booleanActiveSet, hother]
        have hnonempty :
            (booleanActiveSet (Function.update action who choice)).Nonempty := by
          rw [hupdated]
          exact Finset.card_pos.mp (by
            rw [Finset.card_erase_of_mem hwho, hcard]
            omega)
        have := hshape hnonempty
        rw [hupdated, Finset.card_erase_of_mem hwho, hcard] at this
        omega
      · have hupdated : booleanActiveSet (Function.update action who choice) =
            insert who (booleanActiveSet action) := by
          ext other
          by_cases hother : other = who
          · subst other
            have hchoiceTrue : choice = true := by
              cases hchoiceValue : choice <;> simp_all [booleanActiveSet]
            simp [booleanActiveSet, hchoiceTrue]
          · simp [booleanActiveSet, hother]
        have hnonempty :
            (booleanActiveSet (Function.update action who choice)).Nonempty := by
          rw [hupdated]
          exact Finset.insert_nonempty _ _
        have := hshape hnonempty
        rw [hupdated, Finset.card_insert_of_notMem hwho, hcard] at this
        omega
    · rintro rfl
      simp only [PMF.mem_support_iff, pmfPi_apply,
        Finset.prod_ne_zero_iff] at haction
      exact haction who (Finset.mem_univ who)
  have hone : root who (action who) = 1 :=
    (PMF.apply_eq_one_iff (root who) (action who)).mpr hsupp
  apply PMF.ext
  intro choice
  by_cases hchoice : choice = action who
  · subst choice
    simp [hone]
  · have hzero : root who choice = 0 := by
      apply not_ne_iff.mp
      intro hnonzero
      have hmem : choice ∈ (root who).support := hnonzero
      rw [hsupp] at hmem
      exact hchoice (by simpa only [Set.mem_singleton_iff] using hmem)
    simp [hchoice, hzero]

/-- Pair-only support is the cardinality-two specialization of fixed-card
product-row rigidity. -/
theorem pairOnlyProductRow_eq_deterministicPair
    (root : ι → PMF Bool) (action : ι → Bool)
    (haction : action ∈ (pmfPi root).support)
    (hactionNonempty : (booleanActiveSet action).Nonempty)
    (hpairOnly : ∀ candidate ∈ (pmfPi root).support,
      (booleanActiveSet candidate).Nonempty →
        (booleanActiveSet candidate).card = 2) :
    (booleanActiveSet action).card = 2 ∧
      ∀ who, root who = PMF.pure (action who) := by
  exact fixedCardProductRow_eq_deterministic root action haction hactionNonempty
    2 (by omega) hpairOnly

end Math.PMFProduct
