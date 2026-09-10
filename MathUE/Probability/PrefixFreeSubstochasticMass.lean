import Mathlib.Data.Finset.Preimage
import Mathlib.Data.List.Infix
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Substochastic mass bounds for actual prefix-free word sets -/

noncomputable section

namespace Math

open scoped ENNReal

variable {Label : Type*} [DecidableEq Label]

/-- Distinct code words cannot extend one another. -/
def IsPrefixFreeCode (code : Set (List Label)) : Prop :=
  ∀ first ∈ code, ∀ second ∈ code, first <+: second → first = second

private def codeTails (code : Finset (List Label)) (label : Label) : Finset (List Label) :=
  code.preimage (List.cons label) (fun _ _ _ _ h => List.cons.inj h |>.2)

omit [DecidableEq Label] in
@[simp] private theorem mem_codeTails (code : Finset (List Label)) (label : Label)
    (word : List Label) : word ∈ codeTails code label ↔ label :: word ∈ code := by
  simp [codeTails]

private theorem sum_prefixFree_mass_le_of_length
    (mass : List Label → ℝ≥0∞)
    (hchild : ∀ stem (children : Finset Label),
      (∑ label ∈ children, mass (stem ++ [label])) ≤ mass stem)
    (bound : ℕ) (code : Finset (List Label))
    (hcode : IsPrefixFreeCode (code : Set (List Label)))
    (hlength : ∀ word ∈ code, word.length ≤ bound) (stem : List Label) :
    (∑ word ∈ code, mass (stem ++ word)) ≤ mass stem := by
  induction bound generalizing code stem with
  | zero =>
      have hsubset : code ⊆ {[]} := by
        intro word hword
        have hzero := hlength word hword
        simpa using List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hzero)
      calc
        _ ≤ ∑ word ∈ ({[]} : Finset (List Label)), mass (stem ++ word) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => bot_le)
        _ = mass stem := by simp
  | succ bound ih =>
      by_cases hnil : [] ∈ code
      · have heq : code = {[]} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨hnil, ?_⟩
          intro word hword
          exact (hcode [] hnil word hword List.nil_prefix).symm
        simp [heq]
      · let heads : Finset Label := code.biUnion List.toFinset
        have hdecomp : code = heads.biUnion
            (fun label => (codeTails code label).image (List.cons label)) := by
          ext word
          constructor
          · intro hword
            cases word with
            | nil => exact (hnil hword).elim
            | cons label tail =>
                apply Finset.mem_biUnion.mpr
                refine ⟨label, ?_, ?_⟩
                · exact Finset.mem_biUnion.mpr ⟨label :: tail, hword, by simp⟩
                · exact Finset.mem_image.mpr ⟨tail, by simpa using hword, rfl⟩
          · intro hword
            obtain ⟨label, _, hword⟩ := Finset.mem_biUnion.mp hword
            obtain ⟨tail, htail, rfl⟩ := Finset.mem_image.mp hword
            simpa using htail
        have hdisjoint : Set.PairwiseDisjoint (heads : Set Label)
            (fun label => (codeTails code label).image (List.cons label)) := by
          intro first _ second _ hne
          apply Finset.disjoint_left.mpr
          intro word hfirst hsecond
          obtain ⟨tail, _, htail⟩ := Finset.mem_image.mp hfirst
          obtain ⟨tail', _, htail'⟩ := Finset.mem_image.mp hsecond
          exact hne (List.cons.inj (htail.trans htail'.symm)).1
        calc
          _ = ∑ label ∈ heads, ∑ word ∈ codeTails code label,
              mass ((stem ++ [label]) ++ word) := by
            conv_lhs => rw [hdecomp]
            rw [Finset.sum_biUnion hdisjoint]
            apply Finset.sum_congr rfl
            intro label _
            rw [Finset.sum_image]
            · simp only [List.append_assoc, List.singleton_append]
            · intro first _ second _ heq
              exact (List.cons.inj heq).2
          _ ≤ ∑ label ∈ heads, mass (stem ++ [label]) := by
            apply Finset.sum_le_sum
            intro label _
            apply ih
            · intro first hfirst second hsecond hprefix
              have heq := hcode (label :: first) (by simpa using hfirst)
                (label :: second) (by simpa using hsecond)
                (List.cons_prefix_cons.mpr ⟨rfl, hprefix⟩)
              exact (List.cons.inj heq).2
            · intro word hword
              have h := hlength (label :: word) (by simpa using hword)
              simpa using h
          _ ≤ mass stem := hchild stem heads

/-- Finite-child substochasticity bounds every finite prefix-free code, with
no finiteness or countability assumption on the alphabet. -/
theorem sum_prefixFree_mass_le
    (mass : List Label → ℝ≥0∞)
    (hchild : ∀ stem (children : Finset Label),
      (∑ label ∈ children, mass (stem ++ [label])) ≤ mass stem)
    (code : Finset (List Label))
    (hcode : IsPrefixFreeCode (code : Set (List Label))) (stem : List Label) :
    (∑ word ∈ code, mass (stem ++ word)) ≤ mass stem := by
  apply sum_prefixFree_mass_le_of_length mass hchild (code.sup List.length) code hcode
  intro word hword
  exact Finset.le_sup hword

/-- The corresponding bound for an arbitrary prefix-free set of words. -/
theorem tsum_prefixFree_mass_le
    (mass : List Label → ℝ≥0∞)
    (hchild : ∀ stem (children : Finset Label),
      (∑ label ∈ children, mass (stem ++ [label])) ≤ mass stem)
    (code : Set (List Label)) (hcode : IsPrefixFreeCode code) (stem : List Label) :
    (∑' word : code, mass (stem ++ word.val)) ≤ mass stem := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro finite
  let words := finite.image (fun word : code => word.val)
  have hwords : IsPrefixFreeCode (words : Set (List Label)) := by
    intro first hfirst second hsecond hprefix
    obtain ⟨first', _, rfl⟩ := Finset.mem_image.mp hfirst
    obtain ⟨second', _, rfl⟩ := Finset.mem_image.mp hsecond
    exact hcode _ first'.property _ second'.property hprefix
  have hbound := sum_prefixFree_mass_le mass hchild words hwords stem
  simpa only [words, Finset.sum_image, Subtype.val_injective.injOn] using hbound

end Math
