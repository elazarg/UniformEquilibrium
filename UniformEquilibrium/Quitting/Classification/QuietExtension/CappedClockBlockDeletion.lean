import Mathlib.Data.Finset.Option
import UniformEquilibrium.Quitting.Classification.BlockDeletion
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPointwiseDomination

/-!
# Zero-weight capped-clock certificates and exact block deletion

For a parent indexed by `Option ι`, the capped-clock certificate with every
child weight equal to zero is exactly the existing dispensability gate for
the singleton block `{none}`.  Thus weighted capped-clock extension contains
the exact quiet-deletion class literally, rather than only by analogy between
their displayed inequalities.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem cappedClockChildCoalition_eq_map_some (A : Finset ι) :
    cappedClockChildCoalition A = A.map Function.Embedding.some :=
  rfl

omit [Fintype ι] in
private theorem cappedClockJoinedCoalition_eq_insert_none_map_some
    (A : Finset ι) :
    cappedClockJoinedCoalition A =
      insert none (A.map Function.Embedding.some) :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem cappedClockChildCoalition_disjoint_none (A : Finset ι) :
    Disjoint (cappedClockChildCoalition A) {none} := by
  rw [Finset.disjoint_singleton_right]
  simp [cappedClockChildCoalition_eq_map_some]

/-- A dispensable quiet outsider gives the capped-clock certificate whose
child weights all vanish. -/
def cappedClockParentRewardCertificate_zero_of_blockDispensable
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hgate : QuittingBlockDispensable reward {none} none) :
    CappedClockParentRewardCertificate reward where
  weight := 0
  weight_nonneg := by simp
  never_row := by
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    exact hgate.2.trans
      (quittingBlockContinueFloor_nonpos reward {none} none)
  future_row := by
    intro A hA
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    rw [sub_nonpos]
    exact hgate.2.trans
      (quittingBlockContinueFloor_le reward {none} none
        (cappedClockChildCoalition A)
        (cappedClockChildCoalition_nonempty hA)
        (cappedClockChildCoalition_disjoint_none A))
  join_row := by
    intro A hA
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    rw [sub_nonpos]
    exact hgate.1 (cappedClockChildCoalition A)
      (cappedClockChildCoalition_nonempty hA)
      (cappedClockChildCoalition_disjoint_none A)

omit [Fintype ι] in
private theorem eraseNone_nonempty_of_nonempty_of_disjoint_none
    (S : Finset (Option ι)) (hS : S.Nonempty) (hdisjoint : Disjoint S {none}) :
    (Finset.eraseNone S).Nonempty := by
  have hnone : none ∉ S := Finset.disjoint_singleton_right.mp hdisjoint
  have hmap : (Finset.eraseNone S).map Function.Embedding.some = S := by
    rw [Finset.map_some_eraseNone, Finset.erase_eq_of_notMem hnone]
  apply Finset.map_nonempty.mp
  rwa [hmap]

omit [Fintype ι] in
private theorem map_some_eraseNone_eq_of_disjoint_none
    (S : Finset (Option ι)) (hdisjoint : Disjoint S {none}) :
    (Finset.eraseNone S).map Function.Embedding.some = S := by
  rw [Finset.map_some_eraseNone,
    Finset.erase_eq_of_notMem (Finset.disjoint_singleton_right.mp hdisjoint)]

/-- A zero-weight capped-clock certificate is equivalent to exact
dispensability of the quiet singleton block. -/
theorem exists_cappedClockParentRewardCertificate_zero_weight_iff_blockDispensable
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) :
    (∃ certificate : CappedClockParentRewardCertificate reward,
      certificate.weight = 0) ↔
        QuittingBlockDispensable reward {none} none := by
  constructor
  · rintro ⟨certificate, hweight⟩
    have hnever := certificate.never_row
    rw [hweight] at hnever
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hnever
    refine ⟨?_, le_quittingBlockContinueFloor reward {none} none hnever ?_⟩
    · intro S hS hdisjoint
      let A := Finset.eraseNone S
      have hA : A.Nonempty :=
        eraseNone_nonempty_of_nonempty_of_disjoint_none S hS hdisjoint
      have hmap : A.map Function.Embedding.some = S :=
        map_some_eraseNone_eq_of_disjoint_none S hdisjoint
      have hrow := certificate.join_row A hA
      rw [hweight] at hrow
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hrow
      rw [sub_nonpos] at hrow
      simpa only [cappedClockChildCoalition_eq_map_some,
        cappedClockJoinedCoalition_eq_insert_none_map_some, hmap] using hrow
    · intro S hS hdisjoint
      let A := Finset.eraseNone S
      have hA : A.Nonempty :=
        eraseNone_nonempty_of_nonempty_of_disjoint_none S hS hdisjoint
      have hmap : A.map Function.Embedding.some = S :=
        map_some_eraseNone_eq_of_disjoint_none S hdisjoint
      have hrow := certificate.future_row A hA
      rw [hweight] at hrow
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hrow
      rw [sub_nonpos] at hrow
      change reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
        reward ⟨S, hS⟩ none
      simpa only [cappedClockChildCoalition_eq_map_some, hmap] using hrow
  · intro hgate
    exact ⟨cappedClockParentRewardCertificate_zero_of_blockDispensable
      reward hgate, rfl⟩

end GameTheory
