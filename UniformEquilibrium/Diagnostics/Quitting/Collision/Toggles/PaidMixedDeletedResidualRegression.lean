/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PaidMixedOwnerFloorDescent
import UniformEquilibrium.Quitting.Root.EndpointBackwardStability

/-!
# Semantic regression for paid-mixed deletion residuals

The two cleared deletion residuals are exactly scaled endpoint defects at the
actual singleton-base root.  Multiplication by the corresponding row gap
gives an orientation-free signed coordinate, and the normalized square sum
is exactly the squared semantic defect.  This is the source-linked invariant
which a genuine re-equilibration would have to decrease.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual singleton-base mixed point obtained by retaining the original
large-base strict-mixed rates. -/
def quittingPaidMixedDeletedPoint
    (free : Finset ι) (first : ι) {alpha beta : Bool → ℝ}
    (orientation : IsStrictMatchingPenniesOrientation alpha beta) :
    mixedPolytope (quittingBinaryForm free).sig :=
  let hnash := isBinaryDifferenceNash_mixed orientation
  quittingBinaryPairMixedPoint free first
    (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha)
    hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2

/-- The first cleared deletion residual is the first player's actual endpoint
defect times the original first-row gap. -/
theorem binaryDeletedFirstResidual_eq_gap_mul_actualEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) {first second : ι}
    (howner : owner ∉ free)
    (hfirst : first ∈ free) (hsecond : second ∈ free)
    (hne : first ≠ second)
    (hcover : ∀ who ∈ free, who = first ∨ who = second)
    (alpha beta : Bool → ℝ)
    (orientation : IsStrictMatchingPenniesOrientation alpha beta) :
    binaryDeletedFirstResidual alpha
        (quittingLargeBaseDeletedFirstRow reward owner free first second) =
      (alpha false - alpha true) *
        quittingRootEndpointDifference reward 0
          (quittingPersistentBaseRoot {owner} free
            (quittingPaidMixedDeletedPoint free first orientation)) first := by
  have hdisjoint : Disjoint ({owner} : Finset ι) free := by
    simpa [Finset.disjoint_left] using howner
  let hnash := isBinaryDifferenceNash_mixed orientation
  let point := quittingPaidMixedDeletedPoint free first orientation
  let root := quittingPersistentBaseRoot {owner} free point
  have hrows := quittingBinaryPair_rows_eq_largeBaseRows
    reward {owner} free hcover (binaryMixedFirstRate beta)
      (binaryMixedSecondRate alpha)
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
  change
    (fun action ↦ quittingRootEndpointDifference reward 0
      (Function.update root second (PMF.pure action)) first) =
        quittingLargeBaseDeletedFirstRow reward owner free first second ∧
    _ at hrows
  have hrates := quittingPersistentBaseRoot_binaryPairMixedPoint_true_toReal
    ({owner} : Finset ι) free hdisjoint hfirst hsecond hne
      (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha)
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
  change (root first true).toReal = binaryMixedFirstRate beta ∧
    (root second true).toReal = binaryMixedSecondRate alpha at hrates
  have hdiff := quittingRootEndpointDifference_eq_binaryDifference
    reward 0 root hne
  change quittingRootEndpointDifference reward 0 root first =
    binaryFirstDifference
      (fun action ↦ quittingRootEndpointDifference reward 0
        (Function.update root second (PMF.pure action)) first)
      (root second true).toReal at hdiff
  rw [hdiff, hrows.1, hrates.2,
    binaryFirstDifference_mixed_eq_deletedResidual_div orientation]
  have hgap : alpha false - alpha true ≠ 0 := by
    rcases orientation with orientation | orientation <;> linarith
  field_simp [hgap]

/-- The second cleared deletion residual is the second player's actual
endpoint defect times the original second-row gap. -/
theorem binaryDeletedSecondResidual_eq_gap_mul_actualEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) {first second : ι}
    (howner : owner ∉ free)
    (hfirst : first ∈ free) (hsecond : second ∈ free)
    (hne : first ≠ second)
    (hcover : ∀ who ∈ free, who = first ∨ who = second)
    (alpha beta : Bool → ℝ)
    (orientation : IsStrictMatchingPenniesOrientation alpha beta) :
    binaryDeletedSecondResidual beta
        (quittingLargeBaseDeletedSecondRow reward owner free first second) =
      (beta true - beta false) *
        quittingRootEndpointDifference reward 0
          (quittingPersistentBaseRoot {owner} free
            (quittingPaidMixedDeletedPoint free first orientation)) second := by
  have hdisjoint : Disjoint ({owner} : Finset ι) free := by
    simpa [Finset.disjoint_left] using howner
  let hnash := isBinaryDifferenceNash_mixed orientation
  let point := quittingPaidMixedDeletedPoint free first orientation
  let root := quittingPersistentBaseRoot {owner} free point
  have hrows := quittingBinaryPair_rows_eq_largeBaseRows
    reward {owner} free hcover (binaryMixedFirstRate beta)
      (binaryMixedSecondRate alpha)
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
  change _ ∧
    (fun action ↦ quittingRootEndpointDifference reward 0
      (Function.update root first (PMF.pure action)) second) =
        quittingLargeBaseDeletedSecondRow reward owner free first second at hrows
  have hrates := quittingPersistentBaseRoot_binaryPairMixedPoint_true_toReal
    ({owner} : Finset ι) free hdisjoint hfirst hsecond hne
      (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha)
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
  change (root first true).toReal = binaryMixedFirstRate beta ∧
    (root second true).toReal = binaryMixedSecondRate alpha at hrates
  have hdiff := quittingRootEndpointDifference_eq_binaryDifference
    reward 0 root hne.symm
  change quittingRootEndpointDifference reward 0 root second =
    binaryFirstDifference
      (fun action ↦ quittingRootEndpointDifference reward 0
        (Function.update root first (PMF.pure action)) second)
      (root first true).toReal at hdiff
  have hformula := binarySecondDifference_mixed_eq_deletedResidual_div
    orientation
      (quittingLargeBaseDeletedSecondRow reward owner free first second)
  rw [hdiff, hrows.2, hrates.1]
  rw [show binaryFirstDifference
      (quittingLargeBaseDeletedSecondRow reward owner free first second)
        (binaryMixedFirstRate beta) =
      binarySecondDifference
        (quittingLargeBaseDeletedSecondRow reward owner free first second)
          (binaryMixedFirstRate beta) by
    simp [binaryFirstDifference, binarySecondDifference], hformula]
  have hgap : beta true - beta false ≠ 0 := by
    rcases orientation with orientation | orientation <;> linarith
  field_simp [hgap]

/-- Orientation-free semantic signs: multiplying a cleared residual by its
row gap has exactly the sign of the corresponding actual endpoint defect. -/
theorem binaryDeletedResidual_orientedSigns_iff_actual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) {first second : ι}
    (howner : owner ∉ free)
    (hfirst : first ∈ free) (hsecond : second ∈ free)
    (hne : first ≠ second)
    (hcover : ∀ who ∈ free, who = first ∨ who = second)
    (alpha beta : Bool → ℝ)
    (orientation : IsStrictMatchingPenniesOrientation alpha beta) :
    let root := quittingPersistentBaseRoot {owner} free
      (quittingPaidMixedDeletedPoint free first orientation)
    let firstResidual := binaryDeletedFirstResidual alpha
      (quittingLargeBaseDeletedFirstRow reward owner free first second)
    let secondResidual := binaryDeletedSecondResidual beta
      (quittingLargeBaseDeletedSecondRow reward owner free first second)
    (0 < firstResidual * (alpha false - alpha true) ↔
        0 < quittingRootEndpointDifference reward 0 root first) ∧
      (firstResidual * (alpha false - alpha true) < 0 ↔
        quittingRootEndpointDifference reward 0 root first < 0) ∧
      (0 < secondResidual * (beta true - beta false) ↔
        0 < quittingRootEndpointDifference reward 0 root second) ∧
      (secondResidual * (beta true - beta false) < 0 ↔
        quittingRootEndpointDifference reward 0 root second < 0) := by
  dsimp only
  rw [binaryDeletedFirstResidual_eq_gap_mul_actualEndpoint reward owner free
      howner hfirst hsecond hne hcover alpha beta orientation,
    binaryDeletedSecondResidual_eq_gap_mul_actualEndpoint reward owner free
      howner hfirst hsecond hne hcover alpha beta orientation]
  have halphaNe : alpha false - alpha true ≠ 0 := by
    rcases orientation with orientation | orientation <;> linarith
  have hbetaNe : beta true - beta false ≠ 0 := by
    rcases orientation with orientation | orientation <;> linarith
  have halphaSq : 0 < (alpha false - alpha true) *
      (alpha false - alpha true) := mul_self_pos.mpr halphaNe
  have hbetaSq : 0 < (beta true - beta false) *
      (beta true - beta false) := mul_self_pos.mpr hbetaNe
  have hfirstReorder (endpoint : ℝ) :
      (alpha false - alpha true) * endpoint *
          (alpha false - alpha true) =
        ((alpha false - alpha true) * (alpha false - alpha true)) *
          endpoint := by ring
  have hsecondReorder (endpoint : ℝ) :
      (beta true - beta false) * endpoint *
          (beta true - beta false) =
        ((beta true - beta false) * (beta true - beta false)) *
          endpoint := by ring
  constructor
  · rw [hfirstReorder]
    exact mul_pos_iff_of_pos_left halphaSq
  constructor
  · rw [hfirstReorder]
    constructor
    · intro hnegative
      rcases (mul_neg_iff.mp hnegative) with hendpoint | hbad
      · exact hendpoint.2
      · exact False.elim ((not_lt_of_ge halphaSq.le) hbad.1)
    · exact mul_neg_of_pos_of_neg halphaSq
  constructor
  · rw [hsecondReorder]
    exact mul_pos_iff_of_pos_left hbetaSq
  · rw [hsecondReorder]
    constructor
    · intro hnegative
      rcases (mul_neg_iff.mp hnegative) with hendpoint | hbad
      · exact hendpoint.2
      · exact False.elim ((not_lt_of_ge hbetaSq.le) hbad.1)
    · exact mul_neg_of_pos_of_neg hbetaSq

/-- Normalized squared defect of the two deleted indifference equations. -/
def binaryDeletedResidualEnergy
    (alpha beta deletedAlpha deletedBeta : Bool → ℝ) : ℝ :=
  (binaryDeletedFirstResidual alpha deletedAlpha /
      (alpha false - alpha true)) ^ 2 +
    (binaryDeletedSecondResidual beta deletedBeta /
      (beta true - beta false)) ^ 2

/-- The normalized residual energy is exactly the squared endpoint-defect
energy at the actual singleton-base root. -/
theorem binaryDeletedResidualEnergy_eq_actualEndpointSquares
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) {first second : ι}
    (howner : owner ∉ free)
    (hfirst : first ∈ free) (hsecond : second ∈ free)
    (hne : first ≠ second)
    (hcover : ∀ who ∈ free, who = first ∨ who = second)
    (alpha beta : Bool → ℝ)
    (orientation : IsStrictMatchingPenniesOrientation alpha beta) :
    let root := quittingPersistentBaseRoot {owner} free
      (quittingPaidMixedDeletedPoint free first orientation)
    binaryDeletedResidualEnergy alpha beta
        (quittingLargeBaseDeletedFirstRow reward owner free first second)
        (quittingLargeBaseDeletedSecondRow reward owner free first second) =
      (quittingRootEndpointDifference reward 0 root first) ^ 2 +
        (quittingRootEndpointDifference reward 0 root second) ^ 2 := by
  dsimp only
  rw [binaryDeletedResidualEnergy,
    binaryDeletedFirstResidual_eq_gap_mul_actualEndpoint reward owner free
      howner hfirst hsecond hne hcover alpha beta orientation,
    binaryDeletedSecondResidual_eq_gap_mul_actualEndpoint reward owner free
      howner hfirst hsecond hne hcover alpha beta orientation]
  have halpha : alpha false - alpha true ≠ 0 := by
    rcases orientation with orientation | orientation <;> linarith
  have hbeta : beta true - beta false ≠ 0 := by
    rcases orientation with orientation | orientation <;> linarith
  field_simp [halpha, hbeta]

/-- A live deleted residual gives a strictly positive source-linked semantic
energy; it is not merely an un-oriented algebraic case. -/
theorem binaryDeletedResidualEnergy_pos_of_nonzero
    {alpha beta deletedAlpha deletedBeta : Bool → ℝ}
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (nonzero : binaryDeletedFirstResidual alpha deletedAlpha ≠ 0 ∨
      binaryDeletedSecondResidual beta deletedBeta ≠ 0) :
    0 < binaryDeletedResidualEnergy alpha beta deletedAlpha deletedBeta := by
  have halpha : alpha false - alpha true ≠ 0 := by
    rcases orientation with orientation | orientation <;> linarith
  have hbeta : beta true - beta false ≠ 0 := by
    rcases orientation with orientation | orientation <;> linarith
  unfold binaryDeletedResidualEnergy
  rcases nonzero with hfirst | hsecond
  · have hdiv : binaryDeletedFirstResidual alpha deletedAlpha /
        (alpha false - alpha true) ≠ 0 := div_ne_zero hfirst halpha
    nlinarith [sq_pos_of_ne_zero hdiv,
      sq_nonneg (binaryDeletedSecondResidual beta deletedBeta /
        (beta true - beta false))]
  · have hdiv : binaryDeletedSecondResidual beta deletedBeta /
        (beta true - beta false) ≠ 0 := div_ne_zero hsecond hbeta
    nlinarith [sq_pos_of_ne_zero hdiv,
      sq_nonneg (binaryDeletedFirstResidual alpha deletedAlpha /
        (alpha false - alpha true))]

/-! ## Actual-source screen regression -/

/-- Reward-table shift supported only on one player's own quitting sets. -/
def paidOnlyOwnShift (paid : ι) (amount : ℝ) : ι → ℝ :=
  fun who => if who = paid then amount else 0

/-- Shifting only the paid coordinate preserves both free-player rows after
deletion, hence preserves the entire normalized residual energy. -/
theorem quittingLargeBaseDeletedRows_paidOnlyOwnShift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner paid : ι) (free : Finset ι) (first second : ι)
    (hfirstPaid : first ≠ paid) (hsecondPaid : second ≠ paid)
    (amount : ℝ) :
    quittingLargeBaseDeletedFirstRow
        (ownShiftReward reward (paidOnlyOwnShift paid amount))
          owner free first second =
        quittingLargeBaseDeletedFirstRow reward owner free first second ∧
      quittingLargeBaseDeletedSecondRow
        (ownShiftReward reward (paidOnlyOwnShift paid amount))
          owner free first second =
        quittingLargeBaseDeletedSecondRow reward owner free first second := by
  constructor <;> funext action
  · unfold quittingLargeBaseDeletedFirstRow quittingLargeBaseFirstRow
    rw [quittingRootEndpointDifference_ownShiftReward]
    simp [paidOnlyOwnShift, hfirstPaid]
  · unfold quittingLargeBaseDeletedSecondRow quittingLargeBaseSecondRow
    rw [quittingRootEndpointDifference_ownShiftReward]
    simp [paidOnlyOwnShift, hsecondPaid]

/-- The same paid-only table shift preserves the original two-free-player
rows before deletion as well. -/
theorem quittingLargeBaseRows_paidOnlyOwnShift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (paid first second : ι)
    (hfirstPaid : first ≠ paid) (hsecondPaid : second ≠ paid)
    (amount : ℝ) :
    quittingLargeBaseFirstRow
        (ownShiftReward reward (paidOnlyOwnShift paid amount))
          base free first second =
        quittingLargeBaseFirstRow reward base free first second ∧
      quittingLargeBaseSecondRow
        (ownShiftReward reward (paidOnlyOwnShift paid amount))
          base free first second =
        quittingLargeBaseSecondRow reward base free first second := by
  constructor <;> funext action
  · unfold quittingLargeBaseFirstRow
    rw [quittingRootEndpointDifference_ownShiftReward]
    simp [paidOnlyOwnShift, hfirstPaid]
  · unfold quittingLargeBaseSecondRow
    rw [quittingRootEndpointDifference_ownShiftReward]
    simp [paidOnlyOwnShift, hsecondPaid]

/-- At every actual root, the paid-only shift translates the paid player's
join endpoint by exactly the chosen amount. -/
theorem quittingRootEndpointDifference_paidOnlyOwnShift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (paid : ι) (amount : ℝ) :
    quittingRootEndpointDifference
        (ownShiftReward reward (paidOnlyOwnShift paid amount)) tail root paid =
      quittingRootEndpointDifference reward tail root paid + amount := by
  rw [quittingRootEndpointDifference_ownShiftReward]
  simp [paidOnlyOwnShift]

/-- Sharp actual-source regression: with both original and deleted free rows
fixed exactly, the paid join screen at any proposed corrected root can be set
to an arbitrary real value.  Residual-energy descent alone therefore gives
no monotone control of the attachment screen. -/
theorem exists_paidOnlyOwnShift_preserving_rows_with_endpoint_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner paid : ι) (base free : Finset ι) (first second : ι)
    (hfirstPaid : first ≠ paid) (hsecondPaid : second ≠ paid)
    (root : ι → PMF Bool) (target : ℝ) :
    ∃ shiftedReward : {S : Finset ι // S.Nonempty} → Payoff ι,
      quittingLargeBaseFirstRow shiftedReward base free first second =
          quittingLargeBaseFirstRow reward base free first second ∧
      quittingLargeBaseSecondRow shiftedReward base free first second =
          quittingLargeBaseSecondRow reward base free first second ∧
      quittingLargeBaseDeletedFirstRow shiftedReward owner free first second =
          quittingLargeBaseDeletedFirstRow reward owner free first second ∧
      quittingLargeBaseDeletedSecondRow shiftedReward owner free first second =
          quittingLargeBaseDeletedSecondRow reward owner free first second ∧
      quittingRootEndpointDifference shiftedReward 0 root paid = target := by
  let amount := target - quittingRootEndpointDifference reward 0 root paid
  let shiftedReward := ownShiftReward reward (paidOnlyOwnShift paid amount)
  refine ⟨shiftedReward, ?_, ?_, ?_, ?_, ?_⟩
  · exact (quittingLargeBaseRows_paidOnlyOwnShift reward base free paid first
      second hfirstPaid hsecondPaid amount).1
  · exact (quittingLargeBaseRows_paidOnlyOwnShift reward base free paid first
      second hfirstPaid hsecondPaid amount).2
  · exact (quittingLargeBaseDeletedRows_paidOnlyOwnShift reward owner paid free
      first second hfirstPaid hsecondPaid amount).1
  · exact (quittingLargeBaseDeletedRows_paidOnlyOwnShift reward owner paid free
      first second hfirstPaid hsecondPaid amount).2
  · rw [quittingRootEndpointDifference_paidOnlyOwnShift]
    dsimp [amount]
    ring

/-! ## Source-matched interior correction -/

/-- Finite strict-toggle output exposed by a strict join whose enlarged set
is not a sure-exit set. -/
def HasStrictJoinFiniteResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (paid : ι) : Prop :=
  ∃ coalition : Finset ι,
    coalition.Nonempty ∧ paid ∉ coalition ∧
    quittingSetReward reward coalition paid <
        quittingSetReward reward (insert paid coalition) paid ∧
    ((∃ member ∈ coalition,
        quittingSetReward reward (insert paid coalition) member <
          quittingSetReward reward
            ((insert paid coalition).erase member) member) ∨
      ∃ outsider ∉ insert paid coalition,
        quittingSetReward reward (insert paid coalition) outsider <
          quittingSetReward reward
            (insert outsider (insert paid coalition)) outsider)

/-- In terminal-counterexample semantics a strict join cannot produce a
sure-exit set, so it leaves the literal finite toggle output. -/
theorem QuittingTerminalExploitabilityWitness.strictJoinFiniteResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (coalition : Finset ι) (paid : ι)
    (hnonempty : coalition.Nonempty) (hpaid : paid ∉ coalition)
    (hjoin : quittingSetReward reward coalition paid <
      quittingSetReward reward (insert paid coalition) paid) :
    HasStrictJoinFiniteResidual reward paid := by
  refine ⟨coalition, hnonempty, hpaid, hjoin, ?_⟩
  rcases isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin
      reward coalition hpaid hjoin with hsure | htoggle
  · exact False.elim (witness.not_exists_uniformEquilibriumPayoff
      ⟨_, isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
        reward hsure⟩)
  · exact htoggle

/-- A pure singleton-base paid-join cell is the corresponding deterministic
coalition join difference. -/
theorem neg_quittingLargeBaseLeaveCell_eq_repairedPaidJoin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner paid first second : ι}
    (labels : RepairedResidualFourLabels owner paid first second)
    (firstAction secondAction : Bool) :
    -quittingLargeBaseLeaveCell reward {owner} {first, second}
        first second paid firstAction secondAction =
      let coalition := repairedResidualCellCoalition owner paid first second
        false firstAction secondAction
      quittingSetReward reward (insert paid coalition) paid -
        quittingSetReward reward coalition paid := by
  let coalition := repairedResidualCellCoalition owner paid first second
    false firstAction secondAction
  have hroot := quittingLargeBaseDeletedPureRoot_eq_repairedCell labels
    firstAction secondAction
  unfold quittingLargeBaseLeaveCell
  rw [hroot]
  have hpaid : paid ∉ coalition := by
    cases firstAction <;> cases secondAction <;>
      simp [coalition, repairedResidualCellCoalition,
        labels.owner_ne_remaining.symm, labels.remaining_ne_first,
        labels.remaining_ne_second]
  have herase : coalition.erase paid = coalition :=
    Finset.erase_eq_of_notMem hpaid
  have hnonempty : (coalition.erase paid).Nonempty := by
    rw [herase]
    exact ⟨owner, by
      simp [coalition, repairedResidualCellCoalition]⟩
  rw [quittingRootEndpointDifference_pureSet_of_erase_nonempty
    reward coalition paid hnonempty, herase]
  dsimp only
  ring

/-- A positive paid endpoint at the corrected strict-mixed singleton root has
a positive-weight deterministic strict-join cell. -/
theorem exists_paidMixedStrictJoinCell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner paid first second : ι}
    (labels : RepairedResidualFourLabels owner paid first second)
    {alpha beta : Bool → ℝ}
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (positive : 0 < quittingRootEndpointDifference reward 0
      (quittingPersistentBaseRoot {owner} {first, second}
        (quittingPaidMixedDeletedPoint {first, second} first orientation)) paid) :
    ∃ firstAction secondAction,
      0 < binaryClearedCellWeight alpha beta firstAction secondAction ∧
      let coalition := repairedResidualCellCoalition owner paid first second
        false firstAction secondAction
      coalition.Nonempty ∧ paid ∉ coalition ∧
        quittingSetReward reward coalition paid <
          quittingSetReward reward (insert paid coalition) paid := by
  let hnash := isBinaryDifferenceNash_mixed orientation
  let point := quittingPaidMixedDeletedPoint {first, second} first orientation
  have hdisjoint : Disjoint ({owner} : Finset ι) {first, second} := by
    simp [labels.owner_ne_first, labels.owner_ne_second]
  have hexpect := neg_endpointDifference_binaryPair_eq_leaveExpectation
    reward {owner} {first, second} hdisjoint (by simp) (by simp)
      labels.first_ne_second (by simp) labels.remaining_ne_first
      labels.remaining_ne_second
      (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha)
      hnash.1.1 hnash.1.2 hnash.2.1.1 hnash.2.1.2
  change -quittingRootEndpointDifference reward 0
      (quittingPersistentBaseRoot {owner} {first, second} point) paid =
    binaryProductExpectation
      (quittingLargeBaseLeaveCell reward {owner} {first, second}
        first second paid)
      (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha) at hexpect
  have hcleared : 0 < binaryClearedObservable alpha beta
      (fun firstAction secondAction =>
        -quittingLargeBaseLeaveCell reward {owner} {first, second}
          first second paid firstAction secondAction) := by
    have hscoreEq : binaryProductExpectation
        (fun firstAction secondAction =>
          -quittingLargeBaseLeaveCell reward {owner} {first, second}
            first second paid firstAction secondAction)
        (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha) =
      quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot {owner} {first, second} point) paid := by
      simp only [binaryProductExpectation] at hexpect ⊢
      linarith
    have hproductPos : 0 < binaryProductExpectation
        (fun firstAction secondAction =>
          -quittingLargeBaseLeaveCell reward {owner} {first, second}
            first second paid firstAction secondAction)
        (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha) := by
      rw [hscoreEq]
      simpa [point] using positive
    rw [binaryProductExpectation_mixed orientation] at hproductPos
    rcases div_pos_iff.mp hproductPos with hpositive | hnegative
    · exact hpositive.1
    · exact False.elim
        ((not_lt_of_ge (binaryClearedDenominator_pos orientation).le)
          hnegative.2)
  obtain ⟨firstAction, secondAction, hweight, hbound⟩ :=
    exists_bool_cell_weight_pos_and_total_mul_score_ge
      (binaryClearedCellWeight alpha beta)
      (fun firstAction secondAction =>
        -quittingLargeBaseLeaveCell reward {owner} {first, second}
          first second paid firstAction secondAction)
      (binaryClearedDenominator alpha beta)
      (binaryClearedObservable alpha beta
        (fun firstAction secondAction =>
          -quittingLargeBaseLeaveCell reward {owner} {first, second}
            first second paid firstAction secondAction))
      (fun firstAction secondAction =>
        (binaryClearedCellWeight_pos orientation firstAction secondAction).le)
      (binaryClearedCellWeight_sum alpha beta) rfl
      (binaryClearedDenominator_pos orientation)
  refine ⟨firstAction, secondAction, hweight, ?_⟩
  have hscore : 0 < -quittingLargeBaseLeaveCell reward {owner}
      {first, second} first second paid firstAction secondAction := by
    have hden := binaryClearedDenominator_pos orientation
    nlinarith
  rw [neg_quittingLargeBaseLeaveCell_eq_repairedPaidJoin reward labels]
    at hscore
  refine ⟨⟨owner, by
    simp [repairedResidualCellCoalition]⟩, ?_, ?_⟩
  · cases firstAction <;> cases secondAction <;>
      simp [repairedResidualCellCoalition,
        labels.owner_ne_remaining.symm, labels.remaining_ne_first,
        labels.remaining_ne_second]
  · linarith

/-- Exact finite output of re-equilibrating the deleted two-free-player game
in its strict interior chamber. -/
def HasPaidMixedInteriorCorrectionResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner paid first second : ι)
    (labels : RepairedResidualFourLabels owner paid first second)
    (alpha beta : Bool → ℝ)
    (orientation : IsStrictMatchingPenniesOrientation alpha beta) : Prop :=
  HasRepairedPureExitFiniteResidual reward
      (paidMixedOwnerFloorRepairedSource owner paid first second labels
        alpha beta orientation) ∨
    HasStrictJoinFiniteResidual reward paid

/-- The corrected strict-mixed point is an actual induced Nash point of the
deleted singleton-base game. -/
theorem quittingPaidMixedDeletedPoint_mem_nashSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) {first second : ι}
    (howner : owner ∉ free)
    (hfirst : first ∈ free) (hsecond : second ∈ free)
    (hne : first ≠ second)
    (hcover : ∀ who ∈ free, who = first ∨ who = second)
    (orientation : IsStrictMatchingPenniesOrientation
      (quittingLargeBaseDeletedFirstRow reward owner free first second)
      (quittingLargeBaseDeletedSecondRow reward owner free first second)) :
    quittingPaidMixedDeletedPoint free first orientation ∈
      quittingPersistentBaseNashSet reward {owner} free := by
  have hdisjoint : Disjoint ({owner} : Finset ι) free := by
    simpa [Finset.disjoint_left] using howner
  have hfirstResidual : binaryDeletedFirstResidual
      (quittingLargeBaseDeletedFirstRow reward owner free first second)
      (quittingLargeBaseDeletedFirstRow reward owner free first second) = 0 := by
    simp [binaryDeletedFirstResidual]
    ring
  have hsecondResidual : binaryDeletedSecondResidual
      (quittingLargeBaseDeletedSecondRow reward owner free first second)
      (quittingLargeBaseDeletedSecondRow reward owner free first second) = 0 := by
    simp [binaryDeletedSecondResidual]
    ring
  have hzero := free_endpointDifference_eq_zero_of_deletedResiduals
    reward owner free howner hfirst hsecond hne hcover
      (quittingLargeBaseDeletedFirstRow reward owner free first second)
      (quittingLargeBaseDeletedSecondRow reward owner free first second)
      orientation hfirstResidual hsecondResidual
  apply mem_quittingPersistentBaseNashSet_of_free_endpointDifference_eq_zero
    reward {owner} free (by simp) hdisjoint
      (quittingPaidMixedDeletedPoint free first orientation)
  exact hzero

/-- Source-matched interior re-equilibration eliminates both nonzero deleted
residuals at once.  At the corrected singleton-base Nash point, terminal
counterexample semantics forces either the checked owner-floor descent or a
positive paid join, which is purified to a strict deterministic join toggle. -/
theorem QuittingTerminalExploitabilityWitness.paidMixedInteriorCorrectionResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcard : Fintype.card ι = 4)
    {owner paid first second : ι}
    (labels : RepairedResidualFourLabels owner paid first second)
    (orientation : IsStrictMatchingPenniesOrientation
      (quittingLargeBaseDeletedFirstRow reward owner {first, second}
        first second)
      (quittingLargeBaseDeletedSecondRow reward owner {first, second}
        first second)) :
    HasPaidMixedInteriorCorrectionResidual reward owner paid first second
      labels
      (quittingLargeBaseDeletedFirstRow reward owner {first, second}
        first second)
      (quittingLargeBaseDeletedSecondRow reward owner {first, second}
        first second) orientation := by
  let free : Finset ι := {first, second}
  let alpha := quittingLargeBaseDeletedFirstRow reward owner free first second
  let beta := quittingLargeBaseDeletedSecondRow reward owner free first second
  let point := quittingPaidMixedDeletedPoint free first orientation
  let root := quittingPersistentBaseRoot {owner} free point
  have howner : owner ∉ free := by
    simp [free, labels.owner_ne_first, labels.owner_ne_second]
  have hfirst : first ∈ free := by simp [free]
  have hsecond : second ∈ free := by simp [free]
  have hcover : ∀ who ∈ free, who = first ∨ who = second := by
    intro who hwho
    simpa [free] using hwho
  have hpoint : point ∈ quittingPersistentBaseNashSet reward {owner} free := by
    exact quittingPaidMixedDeletedPoint_mem_nashSet reward owner free howner
      hfirst hsecond labels.first_ne_second hcover orientation
  have houtside : ∀ who, who ∉ ({owner} : Finset ι) ∪ free → who = paid := by
    intro who hwho
    rcases labels.exhaust who with hownerWho | hpaidWho | hfirstWho | hsecondWho
    · subst who
      exact False.elim (hwho (by simp))
    · exact hpaidWho
    · subst who
      exact False.elim (hwho (by simp [free]))
    · subst who
      exact False.elim (hwho (by simp [free]))
  by_cases hfloor : quittingSingletonBaseOwnerFloorExcess reward owner root ≤ 0
  · by_cases hpaid : quittingRootEndpointDifference reward 0 root paid ≤ 0
    · have hjoin : ∀ who ∉ ({owner} : Finset ι) ∪ free,
          quittingRootEndpointDifference reward 0 root who ≤ 0 := by
        intro who hwho
        rw [houtside who hwho]
        exact hpaid
      obtain ⟨certificate⟩ :=
        nonempty_quittingSingletonBaseCertificate_of_inducedNash
          reward owner free howner point hpoint hfloor hjoin
      exact False.elim (witness.not_exists_uniformEquilibriumPayoff
        ⟨quittingRootAbsorbingContribution reward root,
          certificate.isUniformEquilibriumPayoff⟩)
    · right
      obtain ⟨firstAction, secondAction, _hweight, hnonempty, hpaidNot,
          hjoin⟩ :=
        exists_paidMixedStrictJoinCell reward labels orientation
          (lt_of_not_ge hpaid)
      exact witness.strictJoinFiniteResidual
        (repairedResidualCellCoalition owner paid first second false
          firstAction secondAction) paid hnonempty hpaidNot hjoin
  · left
    apply witness.paidMixedOwnerFloorFiniteResidual hcard labels orientation
    have himp := (clearedOwnerFloor_nonpos_iff_actual reward owner free howner
      hfirst hsecond labels.first_ne_second hcover alpha beta orientation)
    exact lt_of_not_ge fun hcleared => hfloor (himp.mp hcleared)

end GameTheory
