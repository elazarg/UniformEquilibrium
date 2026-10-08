import UniformEquilibrium.Quitting.Stationary.SignedInfluenceCycleBalance
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticWorstSumRewardSource
import MathUE.Topology.CoordinateAffineAvoidance

/-! # Sign-adaptive endpoints for actual four-player reward contacts

One endpoint table assigns every literal reward coordinate from the original
joining signs. Zero lower joins take the negative branch; zero grand
withdrawals take the positive branch. Every positive convex step preserves
the strict joining signs and turns all weakly nonnegative withdrawals positive.
The typed contact family keeps all canonical labels and only the eligible
mixed labels, with their cohorts fixed from the original table. Values are
convex-linear, change by at most eight times the reward-coordinate error,
and originally positive contacts have endpoint value at least one. Every
positive worst SUM table admits an arbitrarily small common step with
positive new SUM and all fixed labels separated from that new infimum.
Arbitrarily close row-generic tables retain the fixed contacts and original
cohorts. Recipient-scale rigidity and the final source producer remain separate
obligations. This endpoint changes own singletons; the
older singleton-preserving eight-coordinate source is a separate scope.
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

/-- Distinct canonical contact labels, including the empty-background singleton floor. -/
inductive QuittingSignAdaptiveCanonicalContact where
  | grandWithdrawal (who : Fin 4)
  | coalitionJoin (background : {S : Finset (Fin 4) // S.Nonempty ∧ S ≠ Finset.univ})
  | individualJoin
      (pair : {p : Fin 4 × Finset (Fin 4) // p.2.Nonempty ∧ p.1 ∉ p.2})
  | singletonFloor (pair : {p : Fin 4 × Finset (Fin 4) // p.1 ∉ p.2})
  | grandSingletonFloor (who : Fin 4)
  deriving DecidableEq, Fintype

/-- The complete canonical label census counts labels, not distinct numerical values. -/
theorem card_quittingSignAdaptiveCanonicalContact :
    Fintype.card QuittingSignAdaptiveCanonicalContact = 82 := by
  decide

/-- Original weakly nonnegative member withdrawals, including original zero contacts. -/
def quittingSignAdaptiveMemberCohort
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : Finset (Fin 4)) : Finset (Fin 4) := by
  classical
  exact coalition.filter fun who =>
    0 ≤ -quittingMembershipGain original who (coalition.erase who)

/-- Original strictly positive outsider joins. -/
def quittingSignAdaptiveOutsiderCohort
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : Finset (Fin 4)) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter fun who =>
    who ∉ coalition ∧ 0 < quittingMembershipGain original who coalition

/-- Only coalitions with two member contacts or one outsider contact receive a mixed label. -/
def QuittingSignAdaptiveMixedContact
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :=
  {coalition : Finset (Fin 4) // 2 ≤ coalition.card ∧
    (2 ≤ (quittingSignAdaptiveMemberCohort original coalition).card ∨
      1 ≤ (quittingSignAdaptiveOutsiderCohort original coalition).card)}

noncomputable instance
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    Fintype (QuittingSignAdaptiveMixedContact original) := by
  classical
  unfold QuittingSignAdaptiveMixedContact
  infer_instance

/-- The eligible mixed labels are a subset of the eleven nonsingleton coalitions. -/
theorem card_quittingSignAdaptiveMixedContact_le
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    Fintype.card (QuittingSignAdaptiveMixedContact original) ≤ 11 := by
  let embedding : QuittingSignAdaptiveMixedContact original →
      {coalition : Finset (Fin 4) // 2 ≤ coalition.card} :=
    fun coalition => ⟨coalition.val, coalition.property.1⟩
  have hinjective : Function.Injective embedding := by
    intro first second heq
    exact Subtype.ext (congrArg
      (fun coalition : {coalition : Finset (Fin 4) // 2 ≤ coalition.card} => coalition.val) heq)
  have hcard : Fintype.card {coalition : Finset (Fin 4) // 2 ≤ coalition.card} = 11 := by
    decide
  exact (Fintype.card_le_of_injective embedding hinjective).trans_eq hcard

/-- One typed family with canonical labels and original-table eligible mixed labels. -/
abbrev QuittingSignAdaptiveContactLabel
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :=
  QuittingSignAdaptiveCanonicalContact ⊕ QuittingSignAdaptiveMixedContact original

/-- The combined family has at most ninety-three labels without selecting positive witnesses. -/
theorem card_quittingSignAdaptiveContactLabel_le
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    Fintype.card (QuittingSignAdaptiveContactLabel original) ≤ 93 := by
  rw [Fintype.card_sum, card_quittingSignAdaptiveCanonicalContact]
  have hcard := card_quittingSignAdaptiveMixedContact_le original
  omega

/-- Actual evaluation of every canonical contact, with literal zero at the empty coalition. -/
def quittingSignAdaptiveCanonicalContactValue
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    QuittingSignAdaptiveCanonicalContact → ℝ
  | .grandWithdrawal who => -quittingMembershipGain table who (Finset.univ.erase who)
  | .coalitionJoin background =>
      ∑ who ∈ Finset.univ \ background.val, quittingMembershipGain table who background.val
  | .individualJoin pair => quittingMembershipGain table pair.val.1 pair.val.2
  | .singletonFloor pair =>
      table (quittingSingletonTerminal pair.val.1) pair.val.1 -
        quittingSetReward table pair.val.2 pair.val.1
  | .grandSingletonFloor who =>
      table (quittingSingletonTerminal who) who -
        table ⟨Finset.univ, Finset.univ_nonempty⟩ who

/-- Moving-table values always use the cohorts and label eligibility of the original table. -/
def quittingSignAdaptiveContactValue
    (original table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    QuittingSignAdaptiveContactLabel original → ℝ
  | .inl label => quittingSignAdaptiveCanonicalContactValue table label
  | .inr coalition =>
      (∑ who ∈ quittingSignAdaptiveMemberCohort original coalition.val,
        -quittingMembershipGain table who (coalition.val.erase who)) +
      ∑ who ∈ quittingSignAdaptiveOutsiderCohort original coalition.val,
        quittingMembershipGain table who coalition.val

/-- The empty-background floor is the actual own singleton, not a dropped contact. -/
theorem quittingSignAdaptiveCanonicalContactValue_empty_floor
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (who : Fin 4) :
    quittingSignAdaptiveCanonicalContactValue table
        (.singletonFloor ⟨(who, ∅), by simp⟩) =
      table (quittingSingletonTerminal who) who := by
  simp [quittingSignAdaptiveCanonicalContactValue, quittingSetReward]

/-- Every mixed label retains the exact original eligibility disjunction. -/
theorem quittingSignAdaptiveMixedContact_eligible
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : QuittingSignAdaptiveMixedContact original) :
    2 ≤ (quittingSignAdaptiveMemberCohort original coalition.val).card ∨
      1 ≤ (quittingSignAdaptiveOutsiderCohort original coalition.val).card :=
  coalition.property.2

/-- Fresh positive member withdrawals are exactly the original weak-positive cohort. -/
theorem quittingSignAdaptiveMemberCohort_eq_step_positive
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {alpha : ℝ} (halpha : 0 < alpha) (halphaOne : alpha < 1)
    (coalition : Finset (Fin 4)) (hcard : 2 ≤ coalition.card) :
    quittingSignAdaptiveMemberCohort original coalition =
      coalition.filter (fun who =>
        0 < -quittingMembershipGain (quittingSignAdaptiveContactStep original alpha)
          who (coalition.erase who)) := by
  classical
  ext who
  simp only [quittingSignAdaptiveMemberCohort, Finset.mem_filter]
  by_cases hwho : who ∈ coalition
  · simp only [hwho, true_and]
    have hne : (coalition.erase who).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hwho]
      omega
    simpa only [neg_pos, neg_nonneg] using
      (quittingSignAdaptiveContactStep_join_neg_iff original halpha halphaOne who
        (coalition.erase who) hne (by simp)).symm
  · simp [hwho]

/-- Fresh positive outsider joins are exactly the original strict-positive cohort. -/
theorem quittingSignAdaptiveOutsiderCohort_eq_step_positive
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {alpha : ℝ} (halpha : 0 < alpha) (halphaOne : alpha < 1)
    (coalition : Finset (Fin 4)) (hne : coalition.Nonempty) :
    quittingSignAdaptiveOutsiderCohort original coalition =
      Finset.univ.filter (fun who => who ∉ coalition ∧
        0 < quittingMembershipGain (quittingSignAdaptiveContactStep original alpha)
          who coalition) := by
  classical
  ext who
  simp only [quittingSignAdaptiveOutsiderCohort, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hwho : who ∈ coalition
  · simp [hwho]
  · simp only [hwho, not_false_eq_true, true_and]
    exact (quittingSignAdaptiveContactStep_join_pos_iff
      original halpha halphaOne who coalition hne hwho).symm

private theorem setReward_convex_combination
    (first second : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (alpha : ℝ) (coalition : Finset (Fin 4)) (who : Fin 4) :
    quittingSetReward (fun terminal player =>
        (1 - alpha) * first terminal player + alpha * second terminal player) coalition who =
      (1 - alpha) * quittingSetReward first coalition who +
        alpha * quittingSetReward second coalition who := by
  by_cases hne : coalition.Nonempty <;> simp [quittingSetReward, hne]

private theorem membershipGain_convex_combination
    (first second : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (alpha : ℝ) (who : Fin 4) (coalition : Finset (Fin 4)) :
    quittingMembershipGain (fun terminal player =>
        (1 - alpha) * first terminal player + alpha * second terminal player) who coalition =
      (1 - alpha) * quittingMembershipGain first who coalition +
        alpha * quittingMembershipGain second who coalition := by
  simp only [quittingMembershipGain, MathUE.binaryJoinGain, setReward_convex_combination]
  ring

private theorem canonicalContactValue_convex_combination
    (first second : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (alpha : ℝ) (label : QuittingSignAdaptiveCanonicalContact) :
    quittingSignAdaptiveCanonicalContactValue (fun terminal player =>
        (1 - alpha) * first terminal player + alpha * second terminal player) label =
      (1 - alpha) * quittingSignAdaptiveCanonicalContactValue first label +
        alpha * quittingSignAdaptiveCanonicalContactValue second label := by
  cases label <;>
    simp only [quittingSignAdaptiveCanonicalContactValue, membershipGain_convex_combination,
      setReward_convex_combination, Finset.sum_add_distrib, Finset.mul_sum] <;> ring

/-- Every fixed original-table label is linear along every actual reward convex line. -/
theorem quittingSignAdaptiveContactValue_convex_combination
    (original first second : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (alpha : ℝ) (label : QuittingSignAdaptiveContactLabel original) :
    quittingSignAdaptiveContactValue original (fun terminal player =>
        (1 - alpha) * first terminal player + alpha * second terminal player) label =
      (1 - alpha) * quittingSignAdaptiveContactValue original first label +
        alpha * quittingSignAdaptiveContactValue original second label := by
  cases label with
  | inl label => exact canonicalContactValue_convex_combination first second alpha label
  | inr coalition =>
      have hmembers (who : Fin 4) :
          -quittingMembershipGain (fun terminal player =>
              (1 - alpha) * first terminal player + alpha * second terminal player)
              who (coalition.val.erase who) =
            (1 - alpha) * -quittingMembershipGain first who (coalition.val.erase who) +
              alpha * -quittingMembershipGain second who (coalition.val.erase who) := by
        rw [membershipGain_convex_combination]
        ring
      simp only [quittingSignAdaptiveContactValue]
      simp_rw [hmembers, membershipGain_convex_combination]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

private theorem setReward_difference_le
    (first second : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hclose : ∀ terminal who, |first terminal who - second terminal who| ≤ delta)
    (coalition : Finset (Fin 4)) (who : Fin 4) :
    |quittingSetReward first coalition who - quittingSetReward second coalition who| ≤ delta := by
  by_cases hne : coalition.Nonempty
  · simpa only [quittingSetReward, dite_eq_left hne] using hclose ⟨coalition, hne⟩ who
  · simpa only [quittingSetReward, dite_eq_right hne, sub_self, abs_zero] using hdelta

private theorem membershipGain_difference_le
    (first second : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hclose : ∀ terminal who, |first terminal who - second terminal who| ≤ delta)
    (who : Fin 4) (coalition : Finset (Fin 4)) :
    |quittingMembershipGain first who coalition -
        quittingMembershipGain second who coalition| ≤ 2 * delta := by
  unfold quittingMembershipGain MathUE.binaryJoinGain
  have hupper := setReward_difference_le first second delta hdelta hclose
    (insert who coalition) who
  have hlower := setReward_difference_le first second delta hdelta hclose
    (coalition.erase who) who
  have heq :
      (quittingSetReward first (insert who coalition) who -
          quittingSetReward first (coalition.erase who) who) -
        (quittingSetReward second (insert who coalition) who -
          quittingSetReward second (coalition.erase who) who) =
      (quittingSetReward first (insert who coalition) who -
          quittingSetReward second (insert who coalition) who) -
        (quittingSetReward first (coalition.erase who) who -
          quittingSetReward second (coalition.erase who) who) := by ring
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add hupper hlower).trans_eq (by ring))

private theorem abs_sum_difference_le
    (indices : Finset (Fin 4)) (first second : Fin 4 → ℝ) (bound : ℝ)
    (hbound : ∀ who ∈ indices, |first who - second who| ≤ bound) :
    |(∑ who ∈ indices, first who) - ∑ who ∈ indices, second who| ≤
      (indices.card : ℝ) * bound := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ who ∈ indices, (first who - second who)| ≤
        ∑ who ∈ indices, |first who - second who| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _who ∈ indices, bound := Finset.sum_le_sum hbound
    _ = (indices.card : ℝ) * bound := by simp

private theorem canonicalContactValue_difference_le
    (first second : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hclose : ∀ terminal who, |first terminal who - second terminal who| ≤ delta)
    (label : QuittingSignAdaptiveCanonicalContact) :
    |quittingSignAdaptiveCanonicalContactValue first label -
        quittingSignAdaptiveCanonicalContactValue second label| ≤ 8 * delta := by
  cases label with
  | grandWithdrawal who =>
      have h := membershipGain_difference_le first second delta hdelta hclose who
        (Finset.univ.erase who)
      simpa only [quittingSignAdaptiveCanonicalContactValue, neg_sub_neg, abs_sub_comm] using
        h.trans (by linarith)
  | coalitionJoin background =>
      have h := abs_sum_difference_le (Finset.univ \ background.val)
        (fun who => quittingMembershipGain first who background.val)
        (fun who => quittingMembershipGain second who background.val) (2 * delta)
        (fun who _ => membershipGain_difference_le first second delta hdelta hclose who _)
      have hcard : (Finset.univ \ background.val).card ≤ 4 :=
        (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by decide)
      have hcardReal : ((Finset.univ \ background.val).card : ℝ) ≤ 4 := by exact_mod_cast hcard
      exact h.trans (by nlinarith)
  | individualJoin pair =>
      exact (membershipGain_difference_le first second delta hdelta hclose _ _).trans
        (by linarith)
  | singletonFloor pair =>
      have hfirst := hclose (quittingSingletonTerminal pair.val.1) pair.val.1
      have hsecond := setReward_difference_le first second delta hdelta hclose pair.val.2
        pair.val.1
      change |(_ - _) - (_ - _)| ≤ 8 * delta
      have heq : (first (quittingSingletonTerminal pair.val.1) pair.val.1 -
          quittingSetReward first pair.val.2 pair.val.1) -
          (second (quittingSingletonTerminal pair.val.1) pair.val.1 -
            quittingSetReward second pair.val.2 pair.val.1) =
          (first (quittingSingletonTerminal pair.val.1) pair.val.1 -
            second (quittingSingletonTerminal pair.val.1) pair.val.1) -
          (quittingSetReward first pair.val.2 pair.val.1 -
            quittingSetReward second pair.val.2 pair.val.1) := by ring
      rw [heq]
      exact (abs_sub _ _).trans ((add_le_add hfirst hsecond).trans (by linarith))
  | grandSingletonFloor who =>
      have hfirst := hclose (quittingSingletonTerminal who) who
      have hsecond := hclose ⟨Finset.univ, Finset.univ_nonempty⟩ who
      change |(_ - _) - (_ - _)| ≤ 8 * delta
      have heq : (first (quittingSingletonTerminal who) who -
          first ⟨Finset.univ, Finset.univ_nonempty⟩ who) -
          (second (quittingSingletonTerminal who) who -
            second ⟨Finset.univ, Finset.univ_nonempty⟩ who) =
          (first (quittingSingletonTerminal who) who -
            second (quittingSingletonTerminal who) who) -
          (first ⟨Finset.univ, Finset.univ_nonempty⟩ who -
            second ⟨Finset.univ, Finset.univ_nonempty⟩ who) := by ring
      rw [heq]
      exact (abs_sub _ _).trans ((add_le_add hfirst hsecond).trans (by linarith))

/-- Every fixed label changes by at most eight times the reward-coordinate error. -/
theorem abs_quittingSignAdaptiveContactValue_sub_le
    (original first second : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (delta : ℝ)
    (hclose : ∀ terminal who, |first terminal who - second terminal who| ≤ delta)
    (label : QuittingSignAdaptiveContactLabel original) :
    |quittingSignAdaptiveContactValue original first label -
        quittingSignAdaptiveContactValue original second label| ≤ 8 * delta := by
  classical
  have hdelta : 0 ≤ delta := (abs_nonneg _).trans
    (hclose (quittingSingletonTerminal 0) 0)
  cases label with
  | inl label => exact canonicalContactValue_difference_le first second delta hdelta hclose label
  | inr coalition =>
      let members := quittingSignAdaptiveMemberCohort original coalition.val
      let outsiders := quittingSignAdaptiveOutsiderCohort original coalition.val
      have hdisjoint : Disjoint members outsiders := by
        apply Finset.disjoint_left.mpr
        intro who hmember houtside
        exact (Finset.mem_filter.mp houtside).2.1 (Finset.mem_filter.mp hmember).1
      have hcard : members.card + outsiders.card ≤ 4 := by
        rw [← Finset.card_union_of_disjoint hdisjoint]
        exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by decide)
      have hcardReal : (members.card : ℝ) + (outsiders.card : ℝ) ≤ 4 := by
        exact_mod_cast hcard
      have hmembers := abs_sum_difference_le members
        (fun who => -quittingMembershipGain first who (coalition.val.erase who))
        (fun who => -quittingMembershipGain second who (coalition.val.erase who)) (2 * delta)
        (fun who _ => by simpa only [neg_sub_neg, abs_sub_comm] using
          membershipGain_difference_le first second delta hdelta hclose who _)
      have houtside := abs_sum_difference_le outsiders
        (fun who => quittingMembershipGain first who coalition.val)
        (fun who => quittingMembershipGain second who coalition.val) (2 * delta)
        (fun who _ => membershipGain_difference_le first second delta hdelta hclose who _)
      change |(_ + _) - (_ + _)| ≤ 8 * delta
      have heq :
          ((∑ who ∈ members, -quittingMembershipGain first who (coalition.val.erase who)) +
            ∑ who ∈ outsiders, quittingMembershipGain first who coalition.val) -
          ((∑ who ∈ members, -quittingMembershipGain second who (coalition.val.erase who)) +
            ∑ who ∈ outsiders, quittingMembershipGain second who coalition.val) =
          ((∑ who ∈ members, -quittingMembershipGain first who (coalition.val.erase who)) -
            ∑ who ∈ members, -quittingMembershipGain second who (coalition.val.erase who)) +
          ((∑ who ∈ outsiders, quittingMembershipGain first who coalition.val) -
            ∑ who ∈ outsiders, quittingMembershipGain second who coalition.val) := by ring
      rw [heq]
      exact (abs_add_le _ _).trans ((add_le_add hmembers houtside).trans (by nlinarith))

private theorem endpoint_join_ge_one_of_positive
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (who : Fin 4) (background : Finset (Fin 4)) (hne : background.Nonempty)
    (hwho : who ∉ background) (hpositive : 0 < quittingMembershipGain original who background) :
    1 ≤ quittingMembershipGain (quittingSignAdaptiveContactEndpoint original) who background := by
  rw [quittingSignAdaptiveContactEndpoint_join original who background hne hwho]
  have hnegative : ¬0 ≤ -quittingMembershipGain original who background := by linarith
  simp only [hnegative, hpositive, ite_true, ite_false]
  split_ifs <;> norm_num

private theorem endpoint_passive_nonpos
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (background : Finset (Fin 4)) (who : Fin 4) (hwho : who ∉ background) :
    quittingSetReward (quittingSignAdaptiveContactEndpoint original) background who ≤ 0 := by
  by_cases hne : background.Nonempty
  · have hsingle : background ≠ {who} := by
      intro heq
      exact hwho (heq.symm ▸ Finset.mem_singleton_self who)
    simp only [quittingSetReward, dite_eq_left hne, quittingSignAdaptiveContactEndpoint,
      hsingle, hwho, ite_false]
    unfold signAdaptiveContactLower
    split_ifs <;> norm_num
  · simp [quittingSetReward, hne]

private theorem endpoint_grand_nonpos
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (who : Fin 4) :
    quittingSignAdaptiveContactEndpoint original ⟨Finset.univ, Finset.univ_nonempty⟩ who ≤ 0 := by
  have hsingle : (Finset.univ : Finset (Fin 4)) ≠ {who} := by
    intro heq
    have hcard := congrArg Finset.card heq
    norm_num at hcard
  simp only [quittingSignAdaptiveContactEndpoint, hsingle, ite_false, Finset.mem_univ,
    ite_true, signAdaptiveContactUpper, Finset.insert_erase (Finset.mem_univ who)]
  split_ifs <;> norm_num

private theorem endpoint_coalitionJoin_ge_one_of_positive
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (background : {S : Finset (Fin 4) // S.Nonempty ∧ S ≠ Finset.univ})
    (hpositive : 0 < ∑ who ∈ Finset.univ \ background.val,
      quittingMembershipGain original who background.val) :
    1 ≤ ∑ who ∈ Finset.univ \ background.val,
      quittingMembershipGain (quittingSignAdaptiveContactEndpoint original) who background.val := by
  classical
  let outsiders := Finset.univ \ background.val
  by_cases hgrand : ∃ who ∈ outsiders, insert who background.val = Finset.univ
  · obtain ⟨who, hwho, hgrand⟩ := hgrand
    have hsingle : outsiders = {who} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hwho, ?_⟩
      intro other hother
      have hinsert : other ∈ insert who background.val := by
        rw [hgrand]
        exact Finset.mem_univ other
      exact (Finset.mem_insert.mp hinsert).resolve_right (Finset.mem_sdiff.mp hother).2
    change 0 < ∑ player ∈ outsiders, quittingMembershipGain original player background.val
      at hpositive
    change 1 ≤ ∑ player ∈ outsiders,
      quittingMembershipGain (quittingSignAdaptiveContactEndpoint original) player background.val
    rw [hsingle, Finset.sum_singleton] at hpositive ⊢
    exact endpoint_join_ge_one_of_positive original who background.val background.property.1
      (Finset.mem_sdiff.mp hwho).2 hpositive
  · have hnotgrand : ∀ who ∈ outsiders, insert who background.val ≠ Finset.univ := by
      intro who hwho heq
      exact hgrand ⟨who, hwho, heq⟩
    have hsome : ∃ who ∈ outsiders, 0 < quittingMembershipGain original who background.val := by
      by_contra hnone
      have hnonpos : ∀ who ∈ outsiders, quittingMembershipGain original who background.val ≤ 0 := by
        intro who hwho
        exact le_of_not_gt (fun hp => hnone ⟨who, hwho, hp⟩)
      exact (not_lt_of_ge (Finset.sum_nonpos hnonpos)) hpositive
    obtain ⟨who, hwho, hwhoPositive⟩ := hsome
    have hchosen : quittingMembershipGain (quittingSignAdaptiveContactEndpoint original)
        who background.val = 2 := by
      rw [quittingSignAdaptiveContactEndpoint_join original who background.val
        background.property.1 (Finset.mem_sdiff.mp hwho).2,
        ite_eq_right (hnotgrand who hwho), ite_eq_left hwhoPositive]
    have hlower : ∀ other ∈ outsiders.erase who,
        -1 / 2 ≤ quittingMembershipGain (quittingSignAdaptiveContactEndpoint original)
          other background.val := by
      intro other hother
      have houtside := Finset.mem_of_mem_erase hother
      rw [quittingSignAdaptiveContactEndpoint_join original other background.val
        background.property.1 (Finset.mem_sdiff.mp houtside).2,
        ite_eq_right (hnotgrand other houtside)]
      split_ifs <;> norm_num
    have hcount : outsiders.card ≤ 3 := by
      have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ background.val)
      have hne := Finset.card_pos.mpr background.property.1
      have huniv : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
      dsimp [outsiders]
      omega
    have herase : (outsiders.erase who).card ≤ 2 := by
      rw [Finset.card_erase_of_mem hwho]
      omega
    have heraseReal : ((outsiders.erase who).card : ℝ) ≤ 2 := by exact_mod_cast herase
    have hsum : ((outsiders.erase who).card : ℝ) * (-1 / 2) ≤
        ∑ other ∈ outsiders.erase who,
          quittingMembershipGain (quittingSignAdaptiveContactEndpoint original)
            other background.val := by
      simpa using Finset.sum_le_sum hlower
    have heq := Finset.sum_erase_add outsiders
      (fun player => quittingMembershipGain (quittingSignAdaptiveContactEndpoint original)
        player background.val) hwho
    change 1 ≤ ∑ player ∈ outsiders,
      quittingMembershipGain (quittingSignAdaptiveContactEndpoint original) player background.val
    rw [← heq, hchosen]
    nlinarith

/-- Every eligible mixed label has endpoint value at least one, including original zeros. -/
theorem quittingSignAdaptiveContactValue_mixed_endpoint_ge_one
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : QuittingSignAdaptiveMixedContact original) :
    1 ≤ quittingSignAdaptiveContactValue original (quittingSignAdaptiveContactEndpoint original)
      (.inr coalition) := by
  classical
  let members := quittingSignAdaptiveMemberCohort original coalition.val
  let outsiders := quittingSignAdaptiveOutsiderCohort original coalition.val
  have hmembers : ∀ who ∈ members,
      1 / 2 ≤ -quittingMembershipGain (quittingSignAdaptiveContactEndpoint original)
        who (coalition.val.erase who) := by
    intro who hwho
    have hmem : who ∈ coalition.val := (Finset.mem_filter.mp hwho).1
    have hweak : 0 ≤ -quittingMembershipGain original who (coalition.val.erase who) :=
      (Finset.mem_filter.mp hwho).2
    have hne : (coalition.val.erase who).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hmem]
      have hcard := coalition.property.1
      omega
    have hnotpos : ¬0 < quittingMembershipGain original who (coalition.val.erase who) := by
      linarith
    rw [quittingSignAdaptiveContactEndpoint_join original who (coalition.val.erase who)
      hne (by simp)]
    simp only [hweak, hnotpos, ite_true, ite_false]
    split_ifs <;> norm_num
  have houtside : ∀ who ∈ outsiders,
      1 ≤ quittingMembershipGain (quittingSignAdaptiveContactEndpoint original)
        who coalition.val := by
    intro who hwho
    have hcond := (Finset.mem_filter.mp hwho).2
    have hne : coalition.val.Nonempty := by
      apply Finset.card_pos.mp
      have hcard := coalition.property.1
      omega
    exact endpoint_join_ge_one_of_positive original who coalition.val hne hcond.1 hcond.2
  have hmemberSum : (members.card : ℝ) / 2 ≤
      ∑ who ∈ members, -quittingMembershipGain (quittingSignAdaptiveContactEndpoint original)
        who (coalition.val.erase who) := by
    simpa [div_eq_mul_inv] using Finset.sum_le_sum hmembers
  have houtsideSum : (outsiders.card : ℝ) ≤
      ∑ who ∈ outsiders,
        quittingMembershipGain (quittingSignAdaptiveContactEndpoint original)
          who coalition.val := by
    simpa using Finset.sum_le_sum houtside
  have hmembersNonneg : (0 : ℝ) ≤ members.card := Nat.cast_nonneg _
  have houtsideNonneg : (0 : ℝ) ≤ outsiders.card := Nat.cast_nonneg _
  change 1 ≤ (∑ who ∈ members,
    -quittingMembershipGain (quittingSignAdaptiveContactEndpoint original)
      who (coalition.val.erase who)) +
    ∑ who ∈ outsiders,
      quittingMembershipGain (quittingSignAdaptiveContactEndpoint original) who coalition.val
  rcases coalition.property.2 with hmemberCount | houtsideCount
  · have hcount : (2 : ℝ) ≤ members.card := by exact_mod_cast hmemberCount
    linarith
  · have hcount : (1 : ℝ) ≤ outsiders.card := by exact_mod_cast houtsideCount
    linarith

/-- Every originally positive fixed contact has endpoint value at least one. -/
theorem quittingSignAdaptiveContactValue_endpoint_ge_one_of_positive
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (label : QuittingSignAdaptiveContactLabel original)
    (hpositive : 0 < quittingSignAdaptiveContactValue original original label) :
    1 ≤ quittingSignAdaptiveContactValue original (quittingSignAdaptiveContactEndpoint original)
      label := by
  cases label with
  | inr coalition => exact quittingSignAdaptiveContactValue_mixed_endpoint_ge_one original coalition
  | inl label =>
      cases label with
      | grandWithdrawal who =>
          have hne : (Finset.univ.erase who).Nonempty :=
            (by decide : ∀ i : Fin 4, (Finset.univ.erase i).Nonempty) who
          have hweak : 0 ≤ -quittingMembershipGain original who (Finset.univ.erase who) :=
            hpositive.le
          change 1 ≤ -quittingMembershipGain (quittingSignAdaptiveContactEndpoint original)
            who (Finset.univ.erase who)
          rw [quittingSignAdaptiveContactEndpoint_join original who (Finset.univ.erase who)
            hne (by simp)]
          simp [hweak]
      | coalitionJoin background =>
          exact endpoint_coalitionJoin_ge_one_of_positive original background hpositive
      | individualJoin pair =>
          exact endpoint_join_ge_one_of_positive original pair.val.1 pair.val.2
            pair.property.1 pair.property.2 hpositive
      | singletonFloor pair =>
          change 1 ≤ quittingSignAdaptiveContactEndpoint original
            (quittingSingletonTerminal pair.val.1) pair.val.1 -
            quittingSetReward (quittingSignAdaptiveContactEndpoint original) pair.val.2 pair.val.1
          rw [quittingSignAdaptiveContactEndpoint_ownSingleton]
          have h := endpoint_passive_nonpos original pair.val.2 pair.val.1 pair.property
          linarith
      | grandSingletonFloor who =>
          change 1 ≤ quittingSignAdaptiveContactEndpoint original
            (quittingSingletonTerminal who) who -
            quittingSignAdaptiveContactEndpoint original ⟨Finset.univ, Finset.univ_nonempty⟩ who
          rw [quittingSignAdaptiveContactEndpoint_ownSingleton]
          have h := endpoint_grand_nonpos original who
          linarith

private theorem continuous_signAdaptiveContactStep
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    Continuous (quittingSignAdaptiveContactStep original) := by
  apply continuous_pi
  intro terminal
  apply continuous_pi
  intro who
  exact ((continuous_const.sub continuous_id).mul continuous_const).add
    (continuous_id.mul continuous_const)

private theorem signAdaptiveContactStep_zero
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    quittingSignAdaptiveContactStep original 0 = original := by
  funext terminal who
  simp [quittingSignAdaptiveContactStep]

/-- Every convex step stays in the whole unit reward cube. -/
theorem abs_quittingSignAdaptiveContactStep_le_one
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hbound : ∀ terminal who, |original terminal who| ≤ 1)
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaOne : alpha ≤ 1)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    |quittingSignAdaptiveContactStep original alpha terminal who| ≤ 1 := by
  have hfirst := mul_le_mul_of_nonneg_left (hbound terminal who)
    (sub_nonneg.mpr halphaOne)
  have hsecond := mul_le_mul_of_nonneg_left
    (abs_quittingSignAdaptiveContactEndpoint_le_one original terminal who) halpha
  calc
    |quittingSignAdaptiveContactStep original alpha terminal who| ≤
        |(1 - alpha) * original terminal who| +
          |alpha * quittingSignAdaptiveContactEndpoint original terminal who| := abs_add_le _ _
    _ = (1 - alpha) * |original terminal who| +
        alpha * |quittingSignAdaptiveContactEndpoint original terminal who| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr halphaOne), abs_of_nonneg halpha]
    _ ≤ 1 := by linarith

/-- The literal error in every reward coordinate is at most twice the step parameter. -/
theorem abs_quittingSignAdaptiveContactStep_sub_le
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hbound : ∀ terminal who, |original terminal who| ≤ 1)
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    |quittingSignAdaptiveContactStep original alpha terminal who - original terminal who| ≤
      2 * alpha := by
  have hpair :
      |quittingSignAdaptiveContactEndpoint original terminal who - original terminal who| ≤
        2 := by
    calc
      |quittingSignAdaptiveContactEndpoint original terminal who - original terminal who| ≤
          |quittingSignAdaptiveContactEndpoint original terminal who| +
            |original terminal who| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add
        (abs_quittingSignAdaptiveContactEndpoint_le_one original terminal who) (hbound _ _)
      _ = 2 := by norm_num
  have heq : quittingSignAdaptiveContactStep original alpha terminal who - original terminal who =
      alpha * (quittingSignAdaptiveContactEndpoint original terminal who -
        original terminal who) := by
    unfold quittingSignAdaptiveContactStep
    ring
  rw [heq, abs_mul, abs_of_nonneg halpha]
  exact (mul_le_mul_of_nonneg_left hpair halpha).trans_eq (mul_comm alpha 2)

/-- An arbitrarily small common positive step separates every fixed contact from its new SUM. -/
theorem exists_small_quittingSignAdaptiveContactStep_avoiding_sumInf
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hbound : ∀ terminal who, |original terminal who| ≤ 1)
    (hpositive : 0 < quittingTerminalDebtSumInf original)
    (hmaximum : ∀ candidate : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      (∀ terminal who, |candidate terminal who| ≤ 1) →
        quittingTerminalDebtSumInf candidate ≤ quittingTerminalDebtSumInf original)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ alpha < tolerance ∧
      0 < quittingTerminalDebtSumInf (quittingSignAdaptiveContactStep original alpha) ∧
      (∀ terminal who, |quittingSignAdaptiveContactStep original alpha terminal who| ≤ 1) ∧
      (∀ label : QuittingSignAdaptiveContactLabel original,
        quittingSignAdaptiveContactValue original
          (quittingSignAdaptiveContactStep original alpha) label ≠
            quittingTerminalDebtSumInf (quittingSignAdaptiveContactStep original alpha)) ∧
      (∀ coalition, 2 ≤ coalition.card →
        quittingSignAdaptiveMemberCohort original coalition =
          coalition.filter (fun who =>
            0 < -quittingMembershipGain (quittingSignAdaptiveContactStep original alpha)
              who (coalition.erase who))) ∧
      (∀ coalition, coalition.Nonempty →
        quittingSignAdaptiveOutsiderCohort original coalition =
          Finset.univ.filter (fun who => who ∉ coalition ∧
            0 < quittingMembershipGain (quittingSignAdaptiveContactStep original alpha)
              who coalition)) := by
  classical
  let omega := quittingTerminalDebtSumInf original
  have homega : omega ≤ 4 / 5 :=
    quittingTerminalDebtSumInf_le_four_fifths_of_unitReward original hbound
  have hsumContinuous : Continuous (fun alpha : ℝ =>
      quittingTerminalDebtSumInf (quittingSignAdaptiveContactStep original alpha)) :=
    continuous_quittingTerminalDebtSumInf.comp (continuous_signAdaptiveContactStep original)
  have hsumLimit : Filter.Tendsto (fun alpha : ℝ =>
      quittingTerminalDebtSumInf (quittingSignAdaptiveContactStep original alpha))
      (nhds 0) (nhds omega) := by
    simpa only [signAdaptiveContactStep_zero] using
      (hsumContinuous.continuousAt (x := 0)).tendsto
  have hnearPositive : ∀ᶠ alpha : ℝ in nhds 0,
      0 < quittingTerminalDebtSumInf (quittingSignAdaptiveContactStep original alpha) :=
    hsumLimit.eventually (Ioi_mem_nhds hpositive)
  have hnearLabels : ∀ᶠ alpha : ℝ in nhds 0,
      ∀ label : QuittingSignAdaptiveContactLabel original,
        quittingSignAdaptiveContactValue original original label ≠ omega →
          quittingSignAdaptiveContactValue original
            (quittingSignAdaptiveContactStep original alpha) label ≠
              quittingTerminalDebtSumInf (quittingSignAdaptiveContactStep original alpha) := by
    apply Filter.eventually_all.mpr
    intro label
    by_cases hequal : quittingSignAdaptiveContactValue original original label = omega
    · exact Filter.Eventually.of_forall fun _ hne => False.elim (hne hequal)
    have hline : (fun alpha : ℝ => quittingSignAdaptiveContactValue original
        (quittingSignAdaptiveContactStep original alpha) label) =
        (fun alpha : ℝ => (1 - alpha) *
          quittingSignAdaptiveContactValue original original label + alpha *
            quittingSignAdaptiveContactValue original
              (quittingSignAdaptiveContactEndpoint original) label) := by
      funext alpha
      exact quittingSignAdaptiveContactValue_convex_combination original original
        (quittingSignAdaptiveContactEndpoint original) alpha label
    have hcontactContinuous : Continuous (fun alpha : ℝ =>
        quittingSignAdaptiveContactValue original
          (quittingSignAdaptiveContactStep original alpha) label) := by
      rw [hline]
      exact ((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)
    have hcontactLimit : Filter.Tendsto (fun alpha : ℝ =>
        quittingSignAdaptiveContactValue original
          (quittingSignAdaptiveContactStep original alpha) label)
        (nhds 0) (nhds (quittingSignAdaptiveContactValue original original label)) := by
      simpa only [signAdaptiveContactStep_zero] using
        (hcontactContinuous.continuousAt (x := 0)).tendsto
    have hnear := (hcontactLimit.sub hsumLimit).eventually
      (eventually_ne_nhds (sub_ne_zero.mpr hequal))
    filter_upwards [hnear] with alpha hne _
    exact sub_ne_zero.mp hne
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp
    (hnearPositive.and hnearLabels)
  let alpha := min (radius / 2) (min (tolerance / 2) (1 / 2))
  have halpha : 0 < alpha := by dsimp only [alpha]; positivity
  have halphaRadius : alpha < radius :=
    (min_le_left _ _).trans_lt (by linarith)
  have halphaTolerance : alpha < tolerance :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have halphaOne : alpha < 1 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  have hnear := hball (show alpha ∈ Metric.ball (0 : ℝ) radius by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos halpha] using halphaRadius)
  have hstepBound := abs_quittingSignAdaptiveContactStep_le_one original hbound
    halpha.le halphaOne.le
  refine ⟨alpha, halpha, halphaOne, halphaTolerance, hnear.1, hstepBound, ?_,
    fun coalition hcard => quittingSignAdaptiveMemberCohort_eq_step_positive original
      halpha halphaOne coalition hcard,
    fun coalition hne => quittingSignAdaptiveOutsiderCohort_eq_step_positive original
      halpha halphaOne coalition hne⟩
  intro label
  by_cases hequal : quittingSignAdaptiveContactValue original original label = omega
  · have hendpoint := quittingSignAdaptiveContactValue_endpoint_ge_one_of_positive original
      label (hequal.symm ▸ hpositive)
    have hline := quittingSignAdaptiveContactValue_convex_combination original original
      (quittingSignAdaptiveContactEndpoint original) alpha label
    change quittingSignAdaptiveContactValue original
      (quittingSignAdaptiveContactStep original alpha) label = _ at hline
    rw [hequal] at hline
    have hstepSum : quittingTerminalDebtSumInf
        (quittingSignAdaptiveContactStep original alpha) ≤ omega := hmaximum _ hstepBound
    have hstrict : omega < quittingSignAdaptiveContactValue original
        (quittingSignAdaptiveContactStep original alpha) label := by
      nlinarith
    exact ne_of_gt (hstepSum.trans_lt hstrict)
  · exact hnear.2 label hequal

/-- A positive original SUM supplies a worst table and one common contact-separated step. -/
theorem exists_positive_quittingSignAdaptiveContact_source
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hpositive : 0 < quittingTerminalDebtSumInf reward)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4), ∃ alpha : ℝ,
      (∀ terminal who, |original terminal who| ≤ 1) ∧
      0 < quittingTerminalDebtSumInf original ∧ quittingTerminalDebtSumInf original ≤ 4 / 5 ∧
      (∀ candidate : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
        (∀ terminal who, |candidate terminal who| ≤ 1) →
          quittingTerminalDebtSumInf candidate ≤ quittingTerminalDebtSumInf original) ∧
      0 < alpha ∧ alpha < 1 ∧ alpha < tolerance ∧
      0 < quittingTerminalDebtSumInf (quittingSignAdaptiveContactStep original alpha) ∧
      (∀ terminal who, |quittingSignAdaptiveContactStep original alpha terminal who| ≤ 1) ∧
      (∀ terminal who,
        |quittingSignAdaptiveContactStep original alpha terminal who - original terminal who| ≤
          2 * alpha) ∧
      ∀ label : QuittingSignAdaptiveContactLabel original,
        quittingSignAdaptiveContactValue original
          (quittingSignAdaptiveContactStep original alpha) label ≠
            quittingTerminalDebtSumInf (quittingSignAdaptiveContactStep original alpha) := by
  obtain ⟨original, hbound, horiginalPositive, _, hmaximum⟩ :=
    exists_positive_maximum_quittingTerminalDebtSumInf_unitReward reward hpositive
  obtain ⟨alpha, halpha, halphaOne, halphaTolerance, hstepPositive, hstepBound, hlabels, _, _⟩ :=
    exists_small_quittingSignAdaptiveContactStep_avoiding_sumInf original hbound
      horiginalPositive hmaximum htolerance
  exact ⟨original, alpha, hbound, horiginalPositive,
    quittingTerminalDebtSumInf_le_four_fifths_of_unitReward original hbound, hmaximum,
    halpha, halphaOne, halphaTolerance, hstepPositive, hstepBound,
    abs_quittingSignAdaptiveContactStep_sub_le original hbound halpha.le, hlabels⟩

/-- Failure of a uniform payoff supplies the actual common contact-separated step. -/
theorem exists_quittingSignAdaptiveContact_source_of_not_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬∃ target : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none target)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4), ∃ alpha : ℝ,
      (∀ terminal who, |original terminal who| ≤ 1) ∧
      0 < quittingTerminalDebtSumInf original ∧ quittingTerminalDebtSumInf original ≤ 4 / 5 ∧
      (∀ candidate : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
        (∀ terminal who, |candidate terminal who| ≤ 1) →
          quittingTerminalDebtSumInf candidate ≤ quittingTerminalDebtSumInf original) ∧
      0 < alpha ∧ alpha < 1 ∧ alpha < tolerance ∧
      0 < quittingTerminalDebtSumInf (quittingSignAdaptiveContactStep original alpha) ∧
      (∀ terminal who, |quittingSignAdaptiveContactStep original alpha terminal who| ≤ 1) ∧
      (∀ terminal who,
        |quittingSignAdaptiveContactStep original alpha terminal who - original terminal who| ≤
          2 * alpha) ∧
      ∀ label : QuittingSignAdaptiveContactLabel original,
        quittingSignAdaptiveContactValue original
          (quittingSignAdaptiveContactStep original alpha) label ≠
            quittingTerminalDebtSumInf (quittingSignAdaptiveContactStep original alpha) := by
  exact exists_positive_quittingSignAdaptiveContact_source reward
    (quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr hnot) htolerance

private theorem setReward_scale
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (rate : ℝ) (coalition : Finset (Fin 4)) (who : Fin 4) :
    quittingSetReward (scaleQuittingReward rate table) coalition who =
      rate * quittingSetReward table coalition who := by
  by_cases hne : coalition.Nonempty <;> simp [quittingSetReward, scaleQuittingReward, hne]

private theorem membershipGain_scale
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (rate : ℝ) (coalition : Finset (Fin 4)) (who : Fin 4) :
    quittingMembershipGain (scaleQuittingReward rate table) who coalition =
      rate * quittingMembershipGain table who coalition := by
  simp only [quittingMembershipGain, MathUE.binaryJoinGain, setReward_scale]
  ring

private theorem contactValue_zero
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (label : QuittingSignAdaptiveContactLabel original) :
    quittingSignAdaptiveContactValue original 0 label = 0 := by
  cases label with
  | inl label =>
      cases label <;> simp [quittingSignAdaptiveContactValue,
        quittingSignAdaptiveCanonicalContactValue, quittingMembershipGain,
        MathUE.binaryJoinGain, quittingSetReward]
  | inr coalition =>
      simp [quittingSignAdaptiveContactValue, quittingMembershipGain,
        MathUE.binaryJoinGain, quittingSetReward]

/-- Every fixed original-table contact scales by the same actual common reward factor. -/
theorem quittingSignAdaptiveContactValue_scaleQuittingReward
    (original table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (rate : ℝ) (label : QuittingSignAdaptiveContactLabel original) :
    quittingSignAdaptiveContactValue original (scaleQuittingReward rate table) label =
      rate * quittingSignAdaptiveContactValue original table label := by
  have h := quittingSignAdaptiveContactValue_convex_combination original 0 table rate label
  have heq : (fun terminal who => (1 - rate) *
      (0 : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) terminal who +
      rate * table terminal who) = scaleQuittingReward rate table := by
    funext terminal who
    simp [scaleQuittingReward]
  rw [heq, contactValue_zero, mul_zero, zero_add] at h
  exact h

private theorem reward_coordinate_error_le_dist
    (first second : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    |first terminal who - second terminal who| ≤ dist first second := by
  rw [← Real.dist_eq]
  exact (dist_le_pi_dist (first terminal) (second terminal) who).trans
    (dist_le_pi_dist first second terminal)

private theorem continuous_contactValue
    (original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (label : QuittingSignAdaptiveContactLabel original) :
    Continuous (fun table => quittingSignAdaptiveContactValue original table label) := by
  have h : LipschitzWith 8 (fun table =>
      quittingSignAdaptiveContactValue original table label) := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    simpa only [Real.dist_eq, NNReal.coe_ofNat] using
      abs_quittingSignAdaptiveContactValue_sub_le original first second (dist first second)
        (reward_coordinate_error_le_dist first second) label
  exact h.continuous

private theorem continuous_membershipGain (who : Fin 4) (coalition : Finset (Fin 4)) :
    Continuous (fun table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) =>
      quittingMembershipGain table who coalition) := by
  have h : LipschitzWith 2 (fun table => quittingMembershipGain table who coalition) := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    simpa only [Real.dist_eq, NNReal.coe_ofNat] using
      membershipGain_difference_le first second (dist first second) dist_nonneg
        (reward_coordinate_error_le_dist first second) who coalition
  exact h.continuous

private abbrev ContactTerminal := {S : Finset (Fin 4) // S.Nonempty}
private abbrev ContactJoinIndex :=
  {pair : Fin 4 × Finset (Fin 4) // pair.2.Nonempty ∧ pair.1 ∉ pair.2}

private theorem dense_flat_rowwiseDistinct :
    Dense {point : ContactTerminal × Fin 4 → ℝ |
      ∀ who first second, first ≠ second → point (first, who) ≠ point (second, who)} := by
  classical
  let Comparison := {pair : Fin 4 × (ContactTerminal × ContactTerminal) //
    pair.2.1 ≠ pair.2.2}
  let field := fun (pair : Comparison) (point : ContactTerminal × Fin 4 → ℝ) =>
    point (pair.val.2.1, pair.val.1) - point (pair.val.2.2, pair.val.1)
  have hcontinuous : ∀ pair : Comparison, Continuous (field pair) := fun pair =>
    (continuous_apply (pair.val.2.1, pair.val.1)).sub
      (continuous_apply (pair.val.2.2, pair.val.1))
  have hvariation : ∀ (pair : Comparison) point rate,
      field pair (Function.update point (pair.val.2.1, pair.val.1)
        (point (pair.val.2.1, pair.val.1) + rate)) = field pair point + 1 * rate := by
    intro pair point rate
    have hne : (pair.val.2.2, pair.val.1) ≠ (pair.val.2.1, pair.val.1) := by
      intro heq
      exact pair.property (congrArg Prod.fst heq).symm
    simp only [field, Function.update_self, Function.update_of_ne hne]
    ring
  have hdense := Math.Topology.dense_iInter_nonzero_of_coordinate_affine field
    (fun pair => (pair.val.2.1, pair.val.1)) (fun _ => 1) hcontinuous
    (fun _ => one_ne_zero) hvariation
  apply hdense.mono
  intro point hpoint who first second hne
  have h := Set.mem_iInter.mp hpoint (⟨(who, (first, second)), hne⟩ : Comparison)
  exact sub_ne_zero.mp h

private theorem exists_rowwiseDistinct_near_preserving_contacts
    (original center : ContactTerminal → Payoff (Fin 4))
    (hunit : ∀ terminal who, |center terminal who| < 1)
    (hpositive : 0 < quittingTerminalDebtSumInf center)
    (hcontacts : ∀ label : QuittingSignAdaptiveContactLabel original,
      quittingSignAdaptiveContactValue original center label ≠ quittingTerminalDebtSumInf center)
    (hjoins : ∀ pair : ContactJoinIndex,
      quittingMembershipGain center pair.val.1 pair.val.2 ≠ 0)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ final : ContactTerminal → Payoff (Fin 4),
      dist final center < tolerance ∧
      (∀ terminal who, |final terminal who| < 1) ∧
      0 < quittingTerminalDebtSumInf final ∧
      (∀ label : QuittingSignAdaptiveContactLabel original,
        quittingSignAdaptiveContactValue original final label ≠ quittingTerminalDebtSumInf final) ∧
      (∀ pair : ContactJoinIndex,
        (0 < quittingMembershipGain final pair.val.1 pair.val.2 ↔
          0 < quittingMembershipGain center pair.val.1 pair.val.2) ∧
        (quittingMembershipGain final pair.val.1 pair.val.2 < 0 ↔
          quittingMembershipGain center pair.val.1 pair.val.2 < 0)) ∧
      ∀ who first second, first ≠ second → final first who ≠ final second who := by
  classical
  have hnearUnit : ∀ᶠ table in nhds center, ∀ terminal who, |table terminal who| < 1 := by
    apply Filter.eventually_all.mpr
    intro terminal
    apply Filter.eventually_all.mpr
    intro who
    have hcoordinate : Continuous (fun table : ContactTerminal → Payoff (Fin 4) =>
        table terminal who) :=
      (continuous_apply who).comp (continuous_apply terminal)
    have h : Filter.Tendsto (fun table : ContactTerminal → Payoff (Fin 4) =>
        |table terminal who|) (nhds center) (nhds |center terminal who|) :=
      (continuous_abs.comp hcoordinate).continuousAt.tendsto
    exact h.eventually (Iio_mem_nhds (hunit terminal who))
  have hnearPositive : ∀ᶠ table in nhds center, 0 < quittingTerminalDebtSumInf table :=
    continuous_quittingTerminalDebtSumInf.continuousAt.tendsto.eventually
      (Ioi_mem_nhds hpositive)
  have hnearContacts : ∀ᶠ table in nhds center,
      ∀ label : QuittingSignAdaptiveContactLabel original,
        quittingSignAdaptiveContactValue original table label ≠
          quittingTerminalDebtSumInf table := by
    apply Filter.eventually_all.mpr
    intro label
    have h := ((continuous_contactValue original label).sub
      continuous_quittingTerminalDebtSumInf).continuousAt.tendsto.eventually
        (eventually_ne_nhds (sub_ne_zero.mpr (hcontacts label)))
    filter_upwards [h] with table htable
    exact sub_ne_zero.mp htable
  have hnearSigns : ∀ᶠ table in nhds center, ∀ pair : ContactJoinIndex,
      (0 < quittingMembershipGain table pair.val.1 pair.val.2 ↔
        0 < quittingMembershipGain center pair.val.1 pair.val.2) ∧
      (quittingMembershipGain table pair.val.1 pair.val.2 < 0 ↔
        quittingMembershipGain center pair.val.1 pair.val.2 < 0) := by
    apply Filter.eventually_all.mpr
    intro pair
    have h : Filter.Tendsto (fun table : ContactTerminal → Payoff (Fin 4) =>
        quittingMembershipGain table pair.val.1 pair.val.2) (nhds center)
        (nhds (quittingMembershipGain center pair.val.1 pair.val.2)) :=
      (continuous_membershipGain pair.val.1 pair.val.2).continuousAt.tendsto
    rcases lt_or_gt_of_ne (hjoins pair) with hnegative | hpositiveJoin
    · filter_upwards [h.eventually (Iio_mem_nhds hnegative)] with table htable
      constructor <;> constructor <;> intro hsign <;> linarith
    · filter_upwards [h.eventually (Ioi_mem_nhds hpositiveJoin)] with table htable
      constructor <;> constructor <;> intro hsign <;> linarith
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp
    (hnearUnit.and (hnearPositive.and (hnearContacts.and hnearSigns)))
  let region := Homeomorph.piCurry ⁻¹' Metric.ball center (min radius tolerance)
  have hopen : IsOpen region := Metric.isOpen_ball.preimage Homeomorph.piCurry.continuous
  have hnonempty : region.Nonempty := by
    refine ⟨Function.uncurry center, ?_⟩
    change Function.curry (Function.uncurry center) ∈ Metric.ball center (min radius tolerance)
    simpa only [Function.curry_uncurry] using
      Metric.mem_ball_self (lt_min hradius htolerance)
  obtain ⟨point, hgeneric, hregion⟩ := dense_flat_rowwiseDistinct.exists_mem_open hopen hnonempty
  let final := Function.curry point
  have hdist : dist final center < min radius tolerance := hregion
  have hnear := hball ((lt_min_iff.mp hdist).1)
  exact ⟨final, (lt_min_iff.mp hdist).2, hnear.1, hnear.2.1, hnear.2.2.1,
    hnear.2.2.2, hgeneric⟩

/-- A chosen actual table retains all fixed contacts and cohorts and has distinct terminal rows. -/
structure QuittingSignAdaptiveRowGenericSource
    (original final : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : Prop where
  strictUnit : ∀ terminal who, |final terminal who| < 1
  positiveSum : 0 < quittingTerminalDebtSumInf final
  contact_ne_sum : ∀ label : QuittingSignAdaptiveContactLabel original,
    quittingSignAdaptiveContactValue original final label ≠ quittingTerminalDebtSumInf final
  member_cohort : ∀ coalition, 2 ≤ coalition.card →
    quittingSignAdaptiveMemberCohort original coalition = coalition.filter (fun who =>
      0 < -quittingMembershipGain final who (coalition.erase who))
  outsider_cohort : ∀ coalition, coalition.Nonempty →
    quittingSignAdaptiveOutsiderCohort original coalition =
      Finset.univ.filter (fun who => who ∉ coalition ∧
        0 < quittingMembershipGain final who coalition)
  row_distinct : ∀ who first second, first ≠ second → final first who ≠ final second who

namespace QuittingSignAdaptiveRowGenericSource

variable {original final : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}

/-- Positive joins are exactly the strict positive original joins. -/
theorem join_pos_iff (source : QuittingSignAdaptiveRowGenericSource original final)
    (who : Fin 4) (background : Finset (Fin 4)) (hne : background.Nonempty)
    (hwho : who ∉ background) :
    0 < quittingMembershipGain final who background ↔
      0 < quittingMembershipGain original who background := by
  classical
  have h := Finset.ext_iff.mp (source.outsider_cohort background hne) who
  simpa only [quittingSignAdaptiveOutsiderCohort, Finset.mem_filter, Finset.mem_univ,
    hwho, not_false_eq_true, true_and] using h.symm

/-- Each legal nonempty joining pair has different actual final rewards. -/
theorem join_ne_zero (source : QuittingSignAdaptiveRowGenericSource original final)
    (who : Fin 4) (background : Finset (Fin 4)) (hne : background.Nonempty)
    (hwho : who ∉ background) : quittingMembershipGain final who background ≠ 0 := by
  rw [membershipGain_eq_actual_pair_difference final who background hne hwho]
  apply sub_ne_zero.mpr
  apply source.row_distinct
  intro heq
  have hset : insert who background = background := congrArg Subtype.val heq
  have hmem := Finset.mem_insert_self who background
  rw [hset] at hmem
  exact hwho hmem

/-- Negative joins are exactly the weakly nonpositive original joins, including original zeros. -/
theorem join_neg_iff (source : QuittingSignAdaptiveRowGenericSource original final)
    (who : Fin 4) (background : Finset (Fin 4)) (hne : background.Nonempty)
    (hwho : who ∉ background) :
    quittingMembershipGain final who background < 0 ↔
      quittingMembershipGain original who background ≤ 0 := by
  constructor
  · intro hnegative
    by_contra hnot
    have hpositive := (source.join_pos_iff who background hne hwho).mpr (not_le.mp hnot)
    linarith
  · intro hnonpositive
    have hnot : ¬0 < quittingMembershipGain final who background := by
      intro hpositive
      exact (not_lt_of_ge hnonpositive)
        ((source.join_pos_iff who background hne hwho).mp hpositive)
    exact lt_of_le_of_ne (le_of_not_gt hnot) (source.join_ne_zero who background hne hwho)

/-- A positive grand withdrawal is exactly the weakly nonnegative original withdrawal. -/
theorem grandWithdrawal_pos_iff (source : QuittingSignAdaptiveRowGenericSource original final)
    (who : Fin 4) :
    0 < -quittingMembershipGain final who (Finset.univ.erase who) ↔
      0 ≤ -quittingMembershipGain original who (Finset.univ.erase who) := by
  classical
  have h := Finset.ext_iff.mp (source.member_cohort Finset.univ (by decide)) who
  simpa only [quittingSignAdaptiveMemberCohort, Finset.mem_filter, Finset.mem_univ,
    true_and] using h.symm

end QuittingSignAdaptiveRowGenericSource

/-- One row-generic actual table is chosen before any new minimizing laws. -/
theorem exists_rowGeneric_quittingSignAdaptiveContact_source
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hpositive : 0 < quittingTerminalDebtSumInf reward)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ original final : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      (∀ terminal who, |original terminal who| ≤ 1) ∧
      0 < quittingTerminalDebtSumInf original ∧ quittingTerminalDebtSumInf original ≤ 4 / 5 ∧
      (∀ candidate : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
        (∀ terminal who, |candidate terminal who| ≤ 1) →
          quittingTerminalDebtSumInf candidate ≤ quittingTerminalDebtSumInf original) ∧
      QuittingSignAdaptiveRowGenericSource original final ∧
      ∀ terminal who, |final terminal who - original terminal who| < tolerance := by
  classical
  have hquarter : 0 < tolerance / 4 := by positivity
  obtain ⟨original, alpha, hbound, horiginalPositive, horiginalUpper, hmaximum,
      halpha, halphaOne, halphaSmall, hstepPositive, hstepBound, hstepClose, hstepContacts⟩ :=
    exists_positive_quittingSignAdaptiveContact_source reward hpositive hquarter
  let step := quittingSignAdaptiveContactStep original alpha
  let shrink := min (tolerance / 4) (1 / 2)
  let rate := 1 - shrink
  let center := scaleQuittingReward rate step
  have hshrink : 0 < shrink := by dsimp only [shrink]; positivity
  have hshrinkHalf : shrink ≤ 1 / 2 := min_le_right _ _
  have hshrinkSmall : shrink ≤ tolerance / 4 := min_le_left _ _
  have hrate : 0 < rate := by dsimp only [rate]; linarith
  have hrateOne : rate < 1 := by dsimp only [rate]; linarith
  have hcenterUnit : ∀ terminal who, |center terminal who| < 1 := by
    intro terminal who
    change |rate * step terminal who| < 1
    rw [abs_mul, abs_of_pos hrate]
    exact ((mul_le_mul_of_nonneg_left (hstepBound terminal who) hrate.le).trans_eq
      (mul_one rate)).trans_lt hrateOne
  have hcenterPositive : 0 < quittingTerminalDebtSumInf center := by
    rw [quittingTerminalDebtSumInf_scaleQuittingReward hrate.le]
    exact mul_pos hrate hstepPositive
  have hcenterContacts : ∀ label : QuittingSignAdaptiveContactLabel original,
      quittingSignAdaptiveContactValue original center label ≠
        quittingTerminalDebtSumInf center := by
    intro label hequal
    rw [quittingSignAdaptiveContactValue_scaleQuittingReward,
      quittingTerminalDebtSumInf_scaleQuittingReward hrate.le] at hequal
    exact hstepContacts label (mul_left_cancel₀ hrate.ne' hequal)
  have hstepJoins : ∀ pair : ContactJoinIndex,
      quittingMembershipGain step pair.val.1 pair.val.2 ≠ 0 := by
    intro pair
    by_cases hjoin : 0 < quittingMembershipGain original pair.val.1 pair.val.2
    · exact ne_of_gt ((quittingSignAdaptiveContactStep_join_pos_iff original halpha
        halphaOne pair.val.1 pair.val.2 pair.property.1 pair.property.2).mpr hjoin)
    · exact ne_of_lt ((quittingSignAdaptiveContactStep_join_neg_iff original halpha
        halphaOne pair.val.1 pair.val.2 pair.property.1 pair.property.2).mpr (le_of_not_gt hjoin))
  have hcenterJoins : ∀ pair : ContactJoinIndex,
      quittingMembershipGain center pair.val.1 pair.val.2 ≠ 0 := by
    intro pair
    rw [membershipGain_scale]
    exact mul_ne_zero hrate.ne' (hstepJoins pair)
  obtain ⟨final, hdist, hfinalUnit, hfinalPositive, hfinalContacts, hfinalSigns, hfinalRows⟩ :=
    exists_rowwiseDistinct_near_preserving_contacts original center hcenterUnit
      hcenterPositive hcenterContacts hcenterJoins hquarter
  have hfinalJoinSigns (who : Fin 4) (background : Finset (Fin 4))
      (hne : background.Nonempty) (hwho : who ∉ background) :
      (0 < quittingMembershipGain final who background ↔
        0 < quittingMembershipGain step who background) ∧
      (quittingMembershipGain final who background < 0 ↔
        quittingMembershipGain step who background < 0) := by
    have h := hfinalSigns (⟨(who, background), hne, hwho⟩ : ContactJoinIndex)
    change (0 < quittingMembershipGain final who background ↔
      0 < quittingMembershipGain (scaleQuittingReward rate step) who background) ∧
      (quittingMembershipGain final who background < 0 ↔
        quittingMembershipGain (scaleQuittingReward rate step) who background < 0) at h
    rw [membershipGain_scale] at h
    have hnegative : rate * quittingMembershipGain step who background < 0 ↔
        quittingMembershipGain step who background < 0 := by
      constructor
      · intro hneg
        nlinarith
      · exact mul_neg_of_pos_of_neg hrate
    have hpositive : 0 < rate * quittingMembershipGain step who background ↔
        0 < quittingMembershipGain step who background := by
      constructor
      · intro hpos
        nlinarith
      · exact mul_pos hrate
    exact ⟨h.1.trans hpositive, h.2.trans hnegative⟩
  refine ⟨original, final, hbound, horiginalPositive, horiginalUpper, hmaximum,
    ⟨hfinalUnit, hfinalPositive, hfinalContacts, ?_, ?_, hfinalRows⟩, ?_⟩
  · intro coalition hcard
    rw [quittingSignAdaptiveMemberCohort_eq_step_positive original
      halpha halphaOne coalition hcard]
    ext who
    simp only [Finset.mem_filter]
    by_cases hwho : who ∈ coalition
    · simp only [hwho, true_and]
      have hne : (coalition.erase who).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem hwho]
        omega
      simpa only [neg_pos] using
        (hfinalJoinSigns who (coalition.erase who) hne (by simp)).2.symm
    · simp [hwho]
  · intro coalition hne
    rw [quittingSignAdaptiveOutsiderCohort_eq_step_positive original
      halpha halphaOne coalition hne]
    ext who
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hwho : who ∈ coalition
    · simp [hwho]
    · simp only [hwho, not_false_eq_true, true_and]
      exact (hfinalJoinSigns who coalition hne hwho).1.symm
  · intro terminal who
    have hfinalCenter : |final terminal who - center terminal who| < tolerance / 4 :=
      (reward_coordinate_error_le_dist final center terminal who).trans_lt hdist
    have hcenterStep : |center terminal who - step terminal who| ≤ tolerance / 4 := by
      have heq : center terminal who - step terminal who = -shrink * step terminal who := by
        dsimp only [center, scaleQuittingReward, rate]
        ring
      rw [heq, abs_mul, abs_neg, abs_of_pos hshrink]
      exact ((mul_le_mul_of_nonneg_left (hstepBound terminal who) hshrink.le).trans_eq
        (mul_one shrink)).trans hshrinkSmall
    have heq : final terminal who - original terminal who =
        (final terminal who - center terminal who) +
          (center terminal who - step terminal who) +
          (step terminal who - original terminal who) := by ring
    rw [heq]
    calc
      |(final terminal who - center terminal who) +
          (center terminal who - step terminal who) +
          (step terminal who - original terminal who)| ≤
          |final terminal who - center terminal who| +
            |center terminal who - step terminal who| +
            |step terminal who - original terminal who| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      _ < tolerance := by linarith [hstepClose terminal who]

/-- The no-uniform-payoff input supplies a row-generic table with all fixed contact gaps. -/
theorem exists_rowGeneric_quittingSignAdaptiveContact_source_of_not_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬∃ target : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none target)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ original final : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      (∀ terminal who, |original terminal who| ≤ 1) ∧
      0 < quittingTerminalDebtSumInf original ∧ quittingTerminalDebtSumInf original ≤ 4 / 5 ∧
      (∀ candidate : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
        (∀ terminal who, |candidate terminal who| ≤ 1) →
          quittingTerminalDebtSumInf candidate ≤ quittingTerminalDebtSumInf original) ∧
      QuittingSignAdaptiveRowGenericSource original final ∧
      ∀ terminal who, |final terminal who - original terminal who| < tolerance := by
  exact exists_rowGeneric_quittingSignAdaptiveContact_source reward
    (quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr hnot) htolerance

end GameTheory
