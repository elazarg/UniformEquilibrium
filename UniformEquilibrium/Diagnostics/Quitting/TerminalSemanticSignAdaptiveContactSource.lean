import UniformEquilibrium.Quitting.Stationary.SignedInfluenceCycleBalance

/-! # Sign-adaptive endpoints for actual four-player reward contacts

One endpoint table assigns every literal reward coordinate from the original
joining signs. Zero lower joins take the negative branch; zero grand
withdrawals take the positive branch. Every positive convex step preserves
the strict joining signs and turns all weakly nonnegative withdrawals positive.
Finite contact separation, row genericity and the final source producer are
not asserted by this endpoint prefix.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

private def signAdaptiveContactLower
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (who : Fin 4) (background : Finset (Fin 4)) : ℝ :=
  if insert who background = Finset.univ then
    if 0 ≤ -quittingMembershipGain reward who background then 0 else -1
  else if 0 < quittingMembershipGain reward who background then -1 else 0

private def signAdaptiveContactUpper
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (who : Fin 4) (background : Finset (Fin 4)) : ℝ :=
  if insert who background = Finset.univ then
    if 0 ≤ -quittingMembershipGain reward who background then -1 else 0
  else if 0 < quittingMembershipGain reward who background then 1 else -1 / 2

/-- The actual sign-adaptive endpoint on all sixty terminal reward coordinates. -/
def quittingSignAdaptiveContactEndpoint
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) := fun terminal who =>
  if terminal.val = {who} then 1
  else if who ∈ terminal.val then
    signAdaptiveContactUpper reward who (terminal.val.erase who)
  else signAdaptiveContactLower reward who terminal.val

/-- A common convex step in the original reward table toward its sign-adaptive endpoint. -/
def quittingSignAdaptiveContactStep
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (alpha : ℝ) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) := fun terminal who =>
  (1 - alpha) * reward terminal who +
    alpha * quittingSignAdaptiveContactEndpoint reward terminal who

@[simp]
theorem quittingSignAdaptiveContactEndpoint_ownSingleton
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (who : Fin 4) :
    quittingSignAdaptiveContactEndpoint reward (quittingSingletonTerminal who) who = 1 := by
  simp [quittingSignAdaptiveContactEndpoint, quittingSingletonTerminal]

theorem abs_quittingSignAdaptiveContactEndpoint_le_one
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    |quittingSignAdaptiveContactEndpoint reward terminal who| ≤ 1 := by
  unfold quittingSignAdaptiveContactEndpoint signAdaptiveContactUpper signAdaptiveContactLower
  split_ifs <;> norm_num

private theorem membershipGain_eq_actual_pair_difference
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (who : Fin 4) (background : Finset (Fin 4)) (hne : background.Nonempty)
    (hwho : who ∉ background) :
    quittingMembershipGain reward who background =
      reward ⟨insert who background, Finset.insert_nonempty who background⟩ who -
        reward ⟨background, hne⟩ who := by
  simp [quittingMembershipGain, MathUE.binaryJoinGain,
    Finset.erase_eq_of_notMem hwho, quittingSetReward, hne]

/-- Both coordinates of every nonempty joining pair use one original-table branch. -/
theorem quittingSignAdaptiveContactEndpoint_pair
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (who : Fin 4) (background : Finset (Fin 4)) (hne : background.Nonempty)
    (hwho : who ∉ background) :
    quittingSignAdaptiveContactEndpoint reward ⟨background, hne⟩ who =
        signAdaptiveContactLower reward who background ∧
      quittingSignAdaptiveContactEndpoint reward
          ⟨insert who background, Finset.insert_nonempty who background⟩ who =
        signAdaptiveContactUpper reward who background := by
  have hlower : background ≠ {who} := by
    intro heq
    exact hwho (heq.symm ▸ Finset.mem_singleton_self who)
  have hupper : insert who background ≠ {who} := by
    intro heq
    obtain ⟨other, hother⟩ := hne
    have hequal : other = who :=
      Finset.mem_singleton.mp (heq ▸ Finset.mem_insert_of_mem hother)
    exact hwho (hequal ▸ hother)
  constructor
  · simp [quittingSignAdaptiveContactEndpoint, hlower, hwho]
  · simp [quittingSignAdaptiveContactEndpoint, hupper, hwho]

/-- Every endpoint join has its literal lower-pair or grand-pair value. -/
theorem quittingSignAdaptiveContactEndpoint_join
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (who : Fin 4) (background : Finset (Fin 4)) (hne : background.Nonempty)
    (hwho : who ∉ background) :
    quittingMembershipGain (quittingSignAdaptiveContactEndpoint reward) who background =
      if insert who background = Finset.univ then
        if 0 ≤ -quittingMembershipGain reward who background then -1 else 1
      else if 0 < quittingMembershipGain reward who background then 2 else -1 / 2 := by
  rw [membershipGain_eq_actual_pair_difference _ who background hne hwho]
  obtain ⟨hlower, hupper⟩ := quittingSignAdaptiveContactEndpoint_pair
    reward who background hne hwho
  rw [hlower, hupper]
  unfold signAdaptiveContactUpper signAdaptiveContactLower
  split_ifs <;> norm_num

private theorem endpoint_join_positive_of_positive
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (who : Fin 4) (background : Finset (Fin 4)) (hne : background.Nonempty)
    (hwho : who ∉ background) (hpositive : 0 < quittingMembershipGain reward who background) :
    0 < quittingMembershipGain (quittingSignAdaptiveContactEndpoint reward) who background := by
  rw [quittingSignAdaptiveContactEndpoint_join reward who background hne hwho]
  have hnegative : ¬0 ≤ -quittingMembershipGain reward who background := by linarith
  simp only [hnegative, hpositive, ite_true, ite_false]
  split_ifs <;> norm_num

private theorem endpoint_join_negative_of_nonpositive
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (who : Fin 4) (background : Finset (Fin 4)) (hne : background.Nonempty)
    (hwho : who ∉ background) (hnonpositive : quittingMembershipGain reward who background ≤ 0) :
    quittingMembershipGain (quittingSignAdaptiveContactEndpoint reward) who background < 0 := by
  rw [quittingSignAdaptiveContactEndpoint_join reward who background hne hwho]
  have hpositive : ¬0 < quittingMembershipGain reward who background :=
    not_lt_of_ge hnonpositive
  have hnegative : 0 ≤ -quittingMembershipGain reward who background := by linarith
  simp only [hnegative, hpositive, ite_true, ite_false]
  split_ifs <;> norm_num

private theorem step_join_eq
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (alpha : ℝ)
    (who : Fin 4) (background : Finset (Fin 4)) (hne : background.Nonempty)
    (hwho : who ∉ background) :
    quittingMembershipGain (quittingSignAdaptiveContactStep reward alpha) who background =
      (1 - alpha) * quittingMembershipGain reward who background +
        alpha * quittingMembershipGain (quittingSignAdaptiveContactEndpoint reward)
          who background := by
  rw [membershipGain_eq_actual_pair_difference _ who background hne hwho,
    membershipGain_eq_actual_pair_difference reward who background hne hwho,
    membershipGain_eq_actual_pair_difference _ who background hne hwho]
  unfold quittingSignAdaptiveContactStep
  ring

/-- All fresh joining signs agree with the strict original signs, including original zeros. -/
theorem quittingSignAdaptiveContactStep_join_pos_iff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {alpha : ℝ} (halpha : 0 < alpha) (halphaOne : alpha < 1)
    (who : Fin 4) (background : Finset (Fin 4)) (hne : background.Nonempty)
    (hwho : who ∉ background) :
    0 < quittingMembershipGain (quittingSignAdaptiveContactStep reward alpha) who background ↔
      0 < quittingMembershipGain reward who background := by
  rw [step_join_eq reward alpha who background hne hwho]
  by_cases hpositive : 0 < quittingMembershipGain reward who background
  · have hendpoint := endpoint_join_positive_of_positive reward who background hne hwho hpositive
    exact iff_of_true (add_pos (mul_pos (sub_pos.mpr halphaOne) hpositive)
      (mul_pos halpha hendpoint)) hpositive
  · have hendpoint := endpoint_join_negative_of_nonpositive reward who background hne hwho
      (not_lt.mp hpositive)
    have hnegative := add_neg_of_nonpos_of_neg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr halphaOne.le) (not_lt.mp hpositive))
      (mul_neg_of_pos_of_neg halpha hendpoint)
    exact iff_of_false (not_lt_of_ge hnegative.le) hpositive

/-- Every fresh negative join corresponds to an originally weakly nonpositive join. -/
theorem quittingSignAdaptiveContactStep_join_neg_iff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {alpha : ℝ} (halpha : 0 < alpha) (halphaOne : alpha < 1)
    (who : Fin 4) (background : Finset (Fin 4)) (hne : background.Nonempty)
    (hwho : who ∉ background) :
    quittingMembershipGain (quittingSignAdaptiveContactStep reward alpha) who background < 0 ↔
      quittingMembershipGain reward who background ≤ 0 := by
  constructor
  · intro hnegative
    by_contra hnot
    have hpositive := (quittingSignAdaptiveContactStep_join_pos_iff
      reward halpha halphaOne who background hne hwho).mpr (not_le.mp hnot)
    exact (not_lt_of_gt hpositive) hnegative
  · intro hnonpositive
    rw [step_join_eq reward alpha who background hne hwho]
    exact add_neg_of_nonpos_of_neg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr halphaOne.le) hnonpositive)
      (mul_neg_of_pos_of_neg halpha
        (endpoint_join_negative_of_nonpositive reward who background hne hwho hnonpositive))

/-- Grand withdrawal is positive after the step exactly for the old weak positive branch. -/
theorem quittingSignAdaptiveContactStep_grandWithdrawal_pos_iff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {alpha : ℝ} (halpha : 0 < alpha) (halphaOne : alpha < 1) (who : Fin 4) :
    0 < -quittingMembershipGain (quittingSignAdaptiveContactStep reward alpha)
        who (Finset.univ.erase who) ↔
      0 ≤ -quittingMembershipGain reward who (Finset.univ.erase who) := by
  have hne : (Finset.univ.erase who).Nonempty :=
    (by decide : ∀ i : Fin 4, (Finset.univ.erase i).Nonempty) who
  simpa only [neg_pos, neg_nonneg] using
    quittingSignAdaptiveContactStep_join_neg_iff reward halpha halphaOne who
      (Finset.univ.erase who) hne (by simp)

end GameTheory
