/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.FinFourIntegralTournament
import UniformEquilibrium.Quitting.Classification.LCP.Normalization
import UniformEquilibrium.Quitting.Cycles.BalancedSingletonCertificate

/-!
# Balanced singleton payoffs on four-player integral-tournament fibres

Every no-sink integral tournament on four players supplies a three-phase
balanced singleton certificate for every quitting reward table with the
prescribed normalized singleton matrix.  The existing certificate consumer
therefore gives a fixed uniform-equilibrium payoff while leaving every
nonsingleton terminal reward unrestricted.  In the complementary sink branch,
the normalized singleton matrix has a homogeneous simplex-LCP solution.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification
namespace FinFourIntegralTournamentBalancedSingleton

open Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Owner of one of the three selected cyclic phases. -/
def owner {A : ι → ι → ℝ}
    (selected : FinFourIntegralTournamentCycleOutsider A) (phase : Fin 3) : ι :=
  selected.relabel phase.castSucc

/-- The fourth selected player, outside the directed owner triangle. -/
def outsider {A : ι → ι → ℝ}
    (selected : FinFourIntegralTournamentCycleOutsider A) : ι :=
  selected.relabel 3

/-- Survival factor of the equal-hazard three-phase cycle. -/
def survival (t : ℝ) : ℝ := 1 / t

/-- Hazard of the equal-hazard three-phase cycle. -/
def hazard (t : ℝ) : ℝ := 1 - survival t

/-- Normalized payoff to the outsider when the selected phase owner quits. -/
def outsiderEntry {A : ι → ι → ℝ}
    (selected : FinFourIntegralTournamentCycleOutsider A)
    (t : ℝ) (phase : Fin 3) : ℝ :=
  tournamentSkewMatrix t A (outsider selected) (owner selected phase)

/-- The exact cyclic continuation tail of the outsider. -/
def outsiderTail {A : ι → ι → ℝ}
    (selected : FinFourIntegralTournamentCycleOutsider A)
    (t : ℝ) (phase : Fin 3) : ℝ :=
  let s := survival t
  (outsiderEntry selected t phase +
      s * outsiderEntry selected t (finRotate 3 phase) +
      s ^ 2 * outsiderEntry selected t (finRotate 3 (finRotate 3 phase))) /
    (1 - s ^ 3)

/-- Normalized continuation tails of all four selected players.  Owners have
tail `t` immediately before their own phase and zero elsewhere; the outsider
uses the closed cyclic resolvent. -/
def tail {A : ι → ι → ℝ}
    (selected : FinFourIntegralTournamentCycleOutsider A)
    (t : ℝ) (phase : Fin 3) : Payoff ι := fun who =>
  ![if phase = 2 then t else 0,
    if phase = 0 then t else 0,
    if phase = 1 then t else 0,
    outsiderTail selected t phase] (selected.relabel.symm who)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem tail_at_owner_zero
    {A : ι → ι → ℝ} (selected : FinFourIntegralTournamentCycleOutsider A)
    (t : ℝ) (phase : Fin 3) :
    tail selected t phase (owner selected 0) = if phase = 2 then t else 0 := by
  simp [tail, owner]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem tail_at_owner_one
    {A : ι → ι → ℝ} (selected : FinFourIntegralTournamentCycleOutsider A)
    (t : ℝ) (phase : Fin 3) :
    tail selected t phase (owner selected 1) = if phase = 0 then t else 0 := by
  simp [tail, owner]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem tail_at_owner_two
    {A : ι → ι → ℝ} (selected : FinFourIntegralTournamentCycleOutsider A)
    (t : ℝ) (phase : Fin 3) :
    tail selected t phase (owner selected 2) = if phase = 1 then t else 0 := by
  simp [tail, owner]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem tail_at_outsider
    {A : ι → ι → ℝ} (selected : FinFourIntegralTournamentCycleOutsider A)
    (t : ℝ) (phase : Fin 3) :
    tail selected t phase (outsider selected) = outsiderTail selected t phase := by
  simp [tail, outsider]

/-- Coarse phase payoff obtained by adding the hazard-scaled tail to each
player's own-singleton baseline. -/
def coarse {A : ι → ι → ℝ}
    (selected : FinFourIntegralTournamentCycleOutsider A)
    (t : ℝ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (phase : Fin 3) : Payoff ι := fun who =>
  quittingSoloReward reward who who + hazard t * tail selected t phase who

theorem survival_pos {t : ℝ} (ht : 1 < t) :
    0 < survival t := by
  unfold survival
  positivity

theorem survival_lt_one {t : ℝ} (ht : 1 < t) :
    survival t < 1 := by
  unfold survival
  rw [div_lt_one (by linarith : (0 : ℝ) < t)]
  exact ht

theorem hazard_pos {t : ℝ} (ht : 1 < t) :
    0 < hazard t := by
  unfold hazard
  linarith [survival_lt_one ht]

theorem hazard_nonneg {t : ℝ} (ht : 1 < t) :
    0 ≤ hazard t := (hazard_pos ht).le

theorem hazard_lt_one {t : ℝ} (ht : 1 < t) :
    hazard t < 1 := by
  unfold hazard
  linarith [survival_pos ht]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem owner_zero {A : ι → ι → ℝ}
    (selected : FinFourIntegralTournamentCycleOutsider A) :
    owner selected 0 = selected.relabel 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem owner_one {A : ι → ι → ℝ}
    (selected : FinFourIntegralTournamentCycleOutsider A) :
    owner selected 1 = selected.relabel 1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem owner_two {A : ι → ι → ℝ}
    (selected : FinFourIntegralTournamentCycleOutsider A) :
    owner selected 2 = selected.relabel 2 := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem owner_injective {A : ι → ι → ℝ}
    (selected : FinFourIntegralTournamentCycleOutsider A) :
    Function.Injective (owner selected) := by
  intro first second heq
  apply Fin.castSucc_injective
  exact selected.relabel.injective heq

omit [Fintype ι] [DecidableEq ι] in
theorem outsider_ne_owner {A : ι → ι → ℝ}
    (selected : FinFourIntegralTournamentCycleOutsider A) (phase : Fin 3) :
    outsider selected ≠ owner selected phase := by
  intro heq
  have := selected.relabel.injective heq
  have hval := congrArg Fin.val this
  have hphase := phase.isLt
  simp at hval
  omega

omit [Fintype ι] [DecidableEq ι] in
theorem owner_or_outsider {A : ι → ι → ℝ}
    (selected : FinFourIntegralTournamentCycleOutsider A) (who : ι) :
    (∃ phase : Fin 3, who = owner selected phase) ∨ who = outsider selected := by
  generalize hindex : selected.relabel.symm who = index
  have hwho := selected.relabel.apply_symm_apply who
  rw [hindex] at hwho
  fin_cases index
  · exact Or.inl ⟨0, by simpa [owner] using hwho.symm⟩
  · exact Or.inl ⟨1, by simpa [owner] using hwho.symm⟩
  · exact Or.inl ⟨2, by simpa [owner] using hwho.symm⟩
  · exact Or.inr (by simpa [outsider] using hwho.symm)

omit [Fintype ι] [DecidableEq ι] in
private theorem reverse_eq_zero_of_edge_eq_one
    {A : ι → ι → ℝ} (hA : IsFractionalTournament A)
    {first second : ι} (hne : first ≠ second) (hedge : A first second = 1) :
    A second first = 0 := by
  nlinarith [hA.2.2 first second hne]

omit [Fintype ι] [DecidableEq ι] in
theorem outsiderEntry_zero
    {A : ι → ι → ℝ} (hA : IsIntegralTournament A)
    (selected : FinFourIntegralTournamentCycleOutsider A) (t : ℝ) :
    outsiderEntry selected t 0 = t := by
  have hne : selected.relabel 3 ≠ selected.relabel 0 :=
    selected.relabel.injective.ne (by decide)
  have hreverse : A (selected.relabel 0) (selected.relabel 3) = 0 :=
    reverse_eq_zero_of_edge_eq_one hA.1 hne selected.outsider_beats_zero
  simp [outsiderEntry, outsider, owner, tournamentSkewMatrix,
    selected.outsider_beats_zero, hreverse]

omit [Fintype ι] [DecidableEq ι] in
theorem outsiderEntry_one
    {A : ι → ι → ℝ} (hA : IsIntegralTournament A)
    (selected : FinFourIntegralTournamentCycleOutsider A) (t : ℝ) :
    outsiderEntry selected t 1 = t := by
  have hne : selected.relabel 3 ≠ selected.relabel 1 :=
    selected.relabel.injective.ne (by decide)
  have hreverse : A (selected.relabel 1) (selected.relabel 3) = 0 :=
    reverse_eq_zero_of_edge_eq_one hA.1 hne selected.outsider_beats_one
  simp [outsiderEntry, outsider, owner, tournamentSkewMatrix,
    selected.outsider_beats_one, hreverse]

omit [Fintype ι] [DecidableEq ι] in
theorem outsiderEntry_two_eq_t_or_neg_one
    {A : ι → ι → ℝ} (hA : IsIntegralTournament A)
    (selected : FinFourIntegralTournamentCycleOutsider A) (t : ℝ) :
    outsiderEntry selected t 2 = t ∨ outsiderEntry selected t 2 = -1 := by
  have hne : selected.relabel 3 ≠ selected.relabel 2 :=
    selected.relabel.injective.ne (by decide)
  rcases hA.2 (selected.relabel 3) (selected.relabel 2) with hedge | hedge
  · right
    have hreverse : A (selected.relabel 2) (selected.relabel 3) = 1 := by
      nlinarith [hA.1.2.2 (selected.relabel 3) (selected.relabel 2) hne]
    simp [outsiderEntry, outsider, owner, tournamentSkewMatrix, hedge, hreverse]
  · left
    have hreverse : A (selected.relabel 2) (selected.relabel 3) = 0 :=
      reverse_eq_zero_of_edge_eq_one hA.1 hne hedge
    simp [outsiderEntry, outsider, owner, tournamentSkewMatrix, hedge, hreverse]

theorem one_sub_survival_pow_three_pos {t : ℝ} (ht : 1 < t) :
    0 < 1 - survival t ^ 3 := by
  exact sub_pos.mpr <| pow_lt_one₀ (survival_pos ht).le
    (survival_lt_one ht) (by norm_num)

omit [Fintype ι] [DecidableEq ι] in
theorem outsiderTail_recurrence
    {A : ι → ι → ℝ} (selected : FinFourIntegralTournamentCycleOutsider A)
    {t : ℝ} (ht : 1 < t) (phase : Fin 3) :
    outsiderTail selected t phase = outsiderEntry selected t phase +
      survival t * outsiderTail selected t (finRotate 3 phase) := by
  have hdenom : 1 - survival t ^ 3 ≠ 0 :=
    (one_sub_survival_pow_three_pos ht).ne'
  fin_cases phase <;>
    simp [outsiderTail] <;>
    field_simp [hdenom] <;>
    ring

omit [Fintype ι] [DecidableEq ι] in
theorem outsiderTail_pos
    {A : ι → ι → ℝ} (hA : IsIntegralTournament A)
    (selected : FinFourIntegralTournamentCycleOutsider A)
    {t : ℝ} (ht : 1 < t) (phase : Fin 3) :
    0 < outsiderTail selected t phase := by
  have htpos : 0 < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := htpos.ne'
  have hspos := survival_pos ht
  have hslt := survival_lt_one ht
  have hs2lt : survival t ^ 2 < 1 :=
    pow_lt_one₀ hspos.le hslt (by norm_num)
  have hst : survival t * t = 1 := by
    simp [survival, htne]
  have hs2t : survival t ^ 2 * t = survival t := by
    rw [pow_two]
    nlinarith
  have hdenom := one_sub_survival_pow_three_pos ht
  have hzero := outsiderEntry_zero hA selected t
  have hone := outsiderEntry_one hA selected t
  rcases outsiderEntry_two_eq_t_or_neg_one hA selected t with htwo | htwo
  · fin_cases phase <;>
      simp [outsiderTail, hzero, hone, htwo] <;>
      exact div_pos (by nlinarith) hdenom
  · fin_cases phase <;>
      simp [outsiderTail, hzero, hone, htwo] <;>
      exact div_pos (by nlinarith) hdenom

omit [Fintype ι] [DecidableEq ι] in
theorem tail_nonneg
    {A : ι → ι → ℝ} (hA : IsIntegralTournament A)
    (selected : FinFourIntegralTournamentCycleOutsider A)
    {t : ℝ} (ht : 1 < t) (phase : Fin 3) (who : ι) :
    0 ≤ tail selected t phase who := by
  have ht0 : 0 ≤ t := (lt_trans zero_lt_one ht).le
  generalize hindex : selected.relabel.symm who = index
  fin_cases index <;> fin_cases phase <;>
    simp [tail, hindex, ht0, (outsiderTail_pos hA selected ht _).le]

omit [Fintype ι] [DecidableEq ι] in
theorem tail_recurrence
    {A : ι → ι → ℝ} (hA : IsIntegralTournament A)
    (selected : FinFourIntegralTournamentCycleOutsider A)
    {t : ℝ} (ht : 1 < t) (phase : Fin 3) (who : ι) :
    tail selected t phase who =
      tournamentSkewMatrix t A who (owner selected phase) +
        survival t * tail selected t (finRotate 3 phase) who := by
  have htne : t ≠ 0 := (lt_trans zero_lt_one ht).ne'
  have h01 : A (selected.relabel 0) (selected.relabel 1) = 0 :=
    reverse_eq_zero_of_edge_eq_one hA.1
      (selected.relabel.injective.ne (by decide)) selected.one_beats_zero
  have h12 : A (selected.relabel 1) (selected.relabel 2) = 0 :=
    reverse_eq_zero_of_edge_eq_one hA.1
      (selected.relabel.injective.ne (by decide)) selected.two_beats_one
  have h20 : A (selected.relabel 2) (selected.relabel 0) = 0 :=
    reverse_eq_zero_of_edge_eq_one hA.1
      (selected.relabel.injective.ne (by decide)) selected.zero_beats_two
  generalize hindex : selected.relabel.symm who = index
  have hwho := selected.relabel.apply_symm_apply who
  rw [hindex] at hwho
  rw [← hwho]
  fin_cases index
  · fin_cases phase <;>
      simp [tail, owner, survival, tournamentSkewMatrix, hA.1.1,
        selected.one_beats_zero, selected.zero_beats_two, h01, h20, htne]
  · fin_cases phase <;>
      simp [tail, owner, survival, tournamentSkewMatrix, hA.1.1,
        selected.one_beats_zero, selected.two_beats_one, h01, h12, htne]
  · fin_cases phase <;>
      simp [tail, owner, survival, tournamentSkewMatrix, hA.1.1,
        selected.two_beats_one, selected.zero_beats_two, h12, h20, htne]
  · simpa [tail, outsiderEntry, outsider, owner] using
      outsiderTail_recurrence selected ht phase

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem tail_owner_eq_zero
    {A : ι → ι → ℝ} (selected : FinFourIntegralTournamentCycleOutsider A)
    (t : ℝ) (phase : Fin 3) :
    tail selected t phase (owner selected phase) = 0 := by
  fin_cases phase <;> simp [tail, owner]

private theorem quittingSoloReward_eq_own_add_matrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ι → ι → ℝ} (hmatrix : normalizedSoloMatrix reward = M)
    (who owner : ι) :
    quittingSoloReward reward owner who =
      quittingSoloReward reward who who + M who owner := by
  have hentry := congrFun (congrFun hmatrix who) owner
  change quittingSoloReward reward owner who -
      quittingSoloReward reward who who = M who owner at hentry
  linarith

/-- Source-preserving constructor from one literal tournament selection to
the balanced three-phase singleton certificate. -/
def certificate
    {A : ι → ι → ℝ} (hA : IsIntegralTournament A)
    (selected : FinFourIntegralTournamentCycleOutsider A)
    {t : ℝ} (ht : 1 < t)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hmatrix : normalizedSoloMatrix reward = tournamentSkewMatrix t A) :
    BalancedSingletonCycleCertificate (L := 3) reward where
  owner := owner selected
  hazard := fun _ => hazard t
  coarse := coarse selected t reward
  initial := 0
  hazard_nonneg := fun _ => hazard_nonneg ht
  hazard_lt_one := fun _ => hazard_lt_one ht
  arc := by
    intro phase
    funext who
    change quittingSoloReward reward who who + hazard t * tail selected t phase who =
      hazard t * quittingSoloReward reward (owner selected phase) who +
        (1 - hazard t) *
          (quittingSoloReward reward who who +
            hazard t * tail selected t (finRotate 3 phase) who)
    rw [quittingSoloReward_eq_own_add_matrix reward hmatrix who
      (owner selected phase)]
    have hrecurrence := tail_recurrence hA selected ht phase who
    rw [hrecurrence]
    unfold hazard
    ring
  active := by
    intro phase
    simp [coarse]
  soloFloor := by
    intro phase who
    exact le_add_of_nonneg_right <|
      mul_nonneg (hazard_nonneg ht) (tail_nonneg hA selected ht phase who)
  opponentDivergence := by
    intro who
    generalize hindex : selected.relabel.symm who = index
    have hwho := selected.relabel.apply_symm_apply who
    rw [hindex] at hwho
    rw [← hwho]
    fin_cases index
    · refine ⟨1, ?_, hazard_pos ht⟩
      exact selected.relabel.injective.ne (by
        intro heq
        have hval := congrArg Fin.val heq
        norm_num at hval)
    · refine ⟨2, ?_, hazard_pos ht⟩
      exact selected.relabel.injective.ne (by
        intro heq
        have hval := congrArg Fin.val heq
        norm_num at hval)
    · refine ⟨0, ?_, hazard_pos ht⟩
      exact selected.relabel.injective.ne (by
        intro heq
        have hval := congrArg Fin.val heq
        norm_num at hval)
    · refine ⟨0, ?_, hazard_pos ht⟩
      exact selected.relabel.injective.ne (by
        intro heq
        have hval := congrArg Fin.val heq
        norm_num at hval)

/-- The fixed target selected by a supplied cycle-and-outsider witness. -/
def target
    {A : ι → ι → ℝ} (selected : FinFourIntegralTournamentCycleOutsider A)
    (t : ℝ) (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Payoff ι :=
  coarse selected t reward 0

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem target_apply
    {A : ι → ι → ℝ} (selected : FinFourIntegralTournamentCycleOutsider A)
    (t : ℝ) (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    target selected t reward who =
      quittingSoloReward reward who who + hazard t * tail selected t 0 who := rfl

@[simp] theorem certificate_coarse_initial
    {A : ι → ι → ℝ} (hA : IsIntegralTournament A)
    (selected : FinFourIntegralTournamentCycleOutsider A)
    {t : ℝ} (ht : 1 < t)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hmatrix : normalizedSoloMatrix reward = tournamentSkewMatrix t A) :
    (certificate hA selected ht reward hmatrix).coarse
        (certificate hA selected ht reward hmatrix).initial =
      target selected t reward := rfl

/-- The selected phase-zero target is a uniform-equilibrium payoff against
all unilateral behavioral deviations. -/
theorem target_isUniformEquilibriumPayoff
    {A : ι → ι → ℝ} (hA : IsIntegralTournament A)
    (selected : FinFourIntegralTournamentCycleOutsider A)
    {t : ℝ} (ht : 1 < t)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hmatrix : normalizedSoloMatrix reward = tournamentSkewMatrix t A) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (target selected t reward) := by
  exact (certificate hA selected ht reward hmatrix).isUniformEquilibriumPayoff

/-- A no-sink integral tournament on four players supplies actual balanced
singleton certificate data. -/
theorem exists_certificate_of_unitOutneighbor
    (hcard : Fintype.card ι = 4) {A : ι → ι → ℝ}
    (hA : IsIntegralTournament A)
    (hunit : FractionalTournamentHasUnitOutneighbor A)
    {t : ℝ} (ht : 1 < t)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hmatrix : normalizedSoloMatrix reward = tournamentSkewMatrix t A) :
    Nonempty (BalancedSingletonCycleCertificate (L := 3) reward) := by
  let selected := Classical.choice <|
    exists_finFourIntegralTournamentCycleOutsider hcard hA hunit
  exact ⟨certificate hA selected ht reward hmatrix⟩

/-- Literal fixed-target no-sink conclusion.  The witness target is selected
before the accuracy parameter of uniform equilibrium. -/
theorem exists_target_isUniformEquilibriumPayoff_of_unitOutneighbor
    (hcard : Fintype.card ι = 4) {A : ι → ι → ℝ}
    (hA : IsIntegralTournament A)
    (hunit : FractionalTournamentHasUnitOutneighbor A)
    {t : ℝ} (ht : 1 < t)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hmatrix : normalizedSoloMatrix reward = tournamentSkewMatrix t A) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let selected := Classical.choice <|
    exists_finFourIntegralTournamentCycleOutsider hcard hA hunit
  exact ⟨target selected t reward,
    target_isUniformEquilibriumPayoff hA selected ht reward hmatrix⟩

/-- The normalized-matrix hypothesis is exactly the displayed affine
singleton-row identity. -/
theorem normalizedSoloMatrix_eq_tournamentSkewMatrix_iff
    {A : ι → ι → ℝ} (t : ℝ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    normalizedSoloMatrix reward = tournamentSkewMatrix t A ↔
      ∀ who owner,
        quittingSoloReward reward owner who =
          quittingSoloReward reward who who + tournamentSkewMatrix t A who owner := by
  constructor
  · intro hmatrix who owner
    exact quittingSoloReward_eq_own_add_matrix reward hmatrix who owner
  · intro hrows
    funext who owner
    rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
    change quittingSoloReward reward owner who -
        quittingSoloReward reward who who = tournamentSkewMatrix t A who owner
    rw [hrows who owner]
    ring

/-- Literal singleton-row form of the no-sink result.  No hypothesis mentions
a nonsingleton terminal coalition. -/
theorem exists_target_isUniformEquilibriumPayoff_of_singletonRows
    (hcard : Fintype.card ι = 4) {A : ι → ι → ℝ}
    (hA : IsIntegralTournament A)
    (hunit : FractionalTournamentHasUnitOutneighbor A)
    {t : ℝ} (ht : 1 < t)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hrows : ∀ who owner,
      quittingSoloReward reward owner who =
        quittingSoloReward reward who who + tournamentSkewMatrix t A who owner) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_target_isUniformEquilibriumPayoff_of_unitOutneighbor
    hcard hA hunit ht reward
  exact (normalizedSoloMatrix_eq_tournamentSkewMatrix_iff t reward).2 hrows

/-- Source-preserving singleton-row form with the literal phase-zero target. -/
theorem target_isUniformEquilibriumPayoff_of_singletonRows
    {A : ι → ι → ℝ} (hA : IsIntegralTournament A)
    (selected : FinFourIntegralTournamentCycleOutsider A)
    {t : ℝ} (ht : 1 < t)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hrows : ∀ who owner,
      quittingSoloReward reward owner who =
        quittingSoloReward reward who who + tournamentSkewMatrix t A who owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (target selected t reward) := by
  apply target_isUniformEquilibriumPayoff hA selected ht reward
  exact (normalizedSoloMatrix_eq_tournamentSkewMatrix_iff t reward).2 hrows

/-- Exhaustive branchwise conclusion for a four-player integral-tournament
fibre: either the normalized matrix has a homogeneous simplex-LCP witness, or
the original full reward table has a balanced singleton certificate. -/
theorem singletonLCPFeasible_or_exists_certificate
    (hcard : Fintype.card ι = 4) {A : ι → ι → ℝ}
    (hA : IsIntegralTournament A) {t : ℝ} (ht : 1 < t)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hmatrix : normalizedSoloMatrix reward = tournamentSkewMatrix t A) :
    SingletonLCPFeasible (normalizedSoloMatrix reward) ∨
      Nonempty (BalancedSingletonCycleCertificate (L := 3) reward) := by
  classical
  by_cases hunit : FractionalTournamentHasUnitOutneighbor A
  · exact Or.inr <|
      exists_certificate_of_unitOutneighbor hcard hA hunit ht reward hmatrix
  · left
    have hloser : ∃ i, ∀ j, i ≠ j → A i j ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hunit hcon
    obtain ⟨i, hi⟩ := hloser
    have hrow : ∀ j, A i j = 0 := by
      intro j
      by_cases hij : i = j
      · rw [hij]
        exact hA.1.1 j
      · exact (hA.2 i j).resolve_right (hi j hij)
    rw [hmatrix]
    exact singletonLCPFeasible_tournamentSkewMatrix_of_row_eq_zero hA.1
      (lt_trans zero_lt_one ht).le hrow

/-- Direct branchwise headline: the matrix gate fails, or the original full
reward table has a fixed uniform-equilibrium payoff. -/
theorem singletonLCPFeasible_or_exists_uniformEquilibriumPayoff
    (hcard : Fintype.card ι = 4) {A : ι → ι → ℝ}
    (hA : IsIntegralTournament A) {t : ℝ} (ht : 1 < t)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hmatrix : normalizedSoloMatrix reward = tournamentSkewMatrix t A) :
    SingletonLCPFeasible (normalizedSoloMatrix reward) ∨
      ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rcases singletonLCPFeasible_or_exists_certificate
      hcard hA ht reward hmatrix with hfeasible | hcertificate
  · exact Or.inl hfeasible
  · obtain ⟨certificate⟩ := hcertificate
    exact Or.inr ⟨certificate.coarse certificate.initial,
      certificate.isUniformEquilibriumPayoff⟩

end FinFourIntegralTournamentBalancedSingleton
end QuittingLCPClassification
end GameTheory
