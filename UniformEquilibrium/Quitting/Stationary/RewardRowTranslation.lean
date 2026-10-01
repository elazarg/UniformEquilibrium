import UniformEquilibrium.Quitting.Stationary.DiscountedDisplacement
import UniformEquilibrium.Quitting.Root.PlayerwiseAffineReward
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import MathUE.Finset.BernoulliBounds

/-! # Terminal recipient-row translations and actual stationary residuals

Only nonempty terminal rewards are translated. Never remains zero. The
undiscounted ambient residual and singleton matrix are invariant; the
discounted residual has the explicitly retained discount correction.
No arbitrary-profile payoff-translation claim is made here.
-/

noncomputable section

namespace GameTheory

open Math.Finset QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- The canonical affine terminal map, at unit scale, translates nonempty rows. -/
theorem weightOfReward_playerwiseTranslation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (shift : Payoff ι)
    (coalition : Finset ι) (hnonempty : coalition.Nonempty) (who : ι) :
    weightOfReward (quittingPlayerwiseAffineReward reward 1 shift) coalition who =
      weightOfReward reward coalition who + shift who := by
  simp [weightOfReward, hnonempty, quittingPlayerwiseAffineReward]

/-- Pure-Quit coalition weights sum to one, on the whole ambient hazard space. -/
theorem sigmaValue_playerwiseTranslation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (shift : Payoff ι)
    (hazard : ι → ℝ) (who : ι) :
    sigmaValue (weightOfReward (quittingPlayerwiseAffineReward reward 1 shift)) hazard who =
      sigmaValue (weightOfReward reward) hazard who + shift who := by
  change (∑ subset ∈ (Finset.univ.erase who).powerset,
      bernoulliWeight hazard (Finset.univ.erase who) subset *
        weightOfReward (quittingPlayerwiseAffineReward reward 1 shift) (insert who subset) who) =
    (∑ subset ∈ (Finset.univ.erase who).powerset,
      bernoulliWeight hazard (Finset.univ.erase who) subset *
        weightOfReward reward (insert who subset) who) + shift who
  simp_rw [weightOfReward_playerwiseTranslation reward shift _
    (Finset.insert_nonempty who _) who, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_bernoulliWeight, one_mul]

/-- Continue absorption picks up the translation only on nonempty outcomes. -/
theorem excludedValue_playerwiseTranslation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (shift : Payoff ι)
    (hazard : ι → ℝ) (who : ι) :
    excludedValue (weightOfReward (quittingPlayerwiseAffineReward reward 1 shift)) hazard who =
      excludedValue (weightOfReward reward) hazard who +
        (1 - continueMassExcl hazard who) * shift who := by
  let carrier := Finset.univ.erase who
  have hsum : (∑ subset ∈ carrier.powerset.erase ∅,
      bernoulliWeight hazard carrier subset *
        weightOfReward (quittingPlayerwiseAffineReward reward 1 shift) subset who) =
      ∑ subset ∈ carrier.powerset.erase ∅,
        bernoulliWeight hazard carrier subset *
          (weightOfReward reward subset who + shift who) := by
    apply Finset.sum_congr rfl
    intro subset hsubset
    rw [weightOfReward_playerwiseTranslation reward shift subset
      (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hsubset).1) who]
  change (∑ subset ∈ carrier.powerset.erase ∅,
      bernoulliWeight hazard carrier subset *
        weightOfReward (quittingPlayerwiseAffineReward reward 1 shift) subset who) = _
  rw [hsum]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_bernoulliWeight_erase_empty]
  rfl

/-- The positive-discount correction prevents a false discounted invariance claim. -/
theorem quittingDiscountedDisplacement_playerwiseTranslation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (shift : Payoff ι)
    (discountComplement : ℝ) (hazard : ι → ℝ) (who : ι) :
    quittingDiscountedDisplacement (quittingPlayerwiseAffineReward reward 1 shift)
        discountComplement hazard who =
      quittingDiscountedDisplacement reward discountComplement hazard who +
        discountComplement * continueMassExcl hazard who * shift who := by
  unfold quittingDiscountedDisplacement
  rw [sigmaValue_playerwiseTranslation, excludedValue_playerwiseTranslation]
  ring

/-- Packet Section 7's undiscounted residual invariance holds on all ambient rows. -/
theorem quittingDiscountedDisplacement_zero_playerwiseTranslation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (shift : Payoff ι)
    (hazard : ι → ℝ) (who : ι) :
    quittingDiscountedDisplacement (quittingPlayerwiseAffineReward reward 1 shift) 0 hazard who =
      quittingDiscountedDisplacement reward 0 hazard who := by
  rw [quittingDiscountedDisplacement_playerwiseTranslation]
  simp

omit [Fintype ι] [DecidableEq ι] in
/-- Reuse the canonical terminal-shift singleton comparison identity. -/
theorem quittingSingletonMatrix_playerwiseTranslation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (shift : Payoff ι) :
    quittingSingletonMatrix (quittingPlayerwiseAffineReward reward 1 shift) =
      quittingSingletonMatrix reward := by
  have hreward : quittingPlayerwiseAffineReward reward 1 shift =
      fun coalition player => reward coalition player - (-shift) player := by
    funext coalition player
    change 1 * reward coalition player + shift player =
      reward coalition player - -shift player
    ring
  rw [hreward]
  exact quittingSingletonMatrix_sub_payoff reward (-shift)

omit [Fintype ι] [DecidableEq ι] in
/-- Filling the empty coalition with zero preserves actual recipient-row equality. -/
theorem weightOfReward_congr_recipient
    (reward other : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (hrow : ∀ terminal, other terminal who = reward terminal who)
    (coalition : Finset ι) :
    weightOfReward other coalition who = weightOfReward reward coalition who := by
  unfold weightOfReward
  split_ifs with hnonempty
  · exact hrow ⟨coalition, hnonempty⟩
  · rfl

/-- A recipient's residual depends only on that recipient's actual terminal row. -/
theorem quittingDiscountedDisplacement_congr_recipient
    (reward other : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (hrow : ∀ terminal, other terminal who = reward terminal who)
    (discountComplement : ℝ) (hazard : ι → ℝ) :
    quittingDiscountedDisplacement other discountComplement hazard who =
      quittingDiscountedDisplacement reward discountComplement hazard who := by
  unfold quittingDiscountedDisplacement sigmaValue excludedValue
  simp_rw [weightOfReward_congr_recipient reward other who hrow]

end GameTheory
