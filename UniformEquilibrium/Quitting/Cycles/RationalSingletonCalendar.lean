import MathUE.FinVariableCycle
import MathUE.RationalArcSubdivision
import UniformEquilibrium.Quitting.Cycles.BalancedSingletonCertificate

/-!
# Exact rational calendars from balanced singleton cycles

Each coarse phase is subdivided into its own positive number of dates using
`q / (n - l*q)`. The chronological flattening preserves coarse successors,
both survival products, and the selected initial payoff. Concrete roots and
exact Continue recursions feed the existing complete behavioral compiler.
-/

noncomputable section

namespace GameTheory

open StochasticGame _root_.Math.Probability Math.PMFProduct

variable {L : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace BalancedSingletonCycleCertificate

variable (certificate : BalancedSingletonCycleCertificate (L := L) reward)

/-- Positive local block lengths selected from the literal coarse hazards. -/
def rationalLength (δ : ℝ) (p : Fin L) : ℕ :=
  Math.rationalArcLength (certificate.hazard p) δ

omit [Fintype ι] [DecidableEq ι] in
theorem rationalLength_pos (δ : ℝ) (p : Fin L) :
    0 < certificate.rationalLength δ p :=
  Math.rationalArcLength_pos _ _

/-- Number of dates in one variable-length microcycle. -/
def rationalPeriod (δ : ℝ) : ℕ := ∑ p, certificate.rationalLength δ p

/-- Chronological flattened index of a coarse phase and its local date. -/
def rationalPhase (δ : ℝ) (p : Fin L) (l : Fin (certificate.rationalLength δ p)) :
    Fin (certificate.rationalPeriod δ) :=
  Math.finVariablePhase (certificate.rationalLength δ) p l

/-- Start at local date zero of the certificate's selected initial phase. -/
def rationalInitial (δ : ℝ) : Fin (certificate.rationalPeriod δ) :=
  certificate.rationalPhase δ certificate.initial
    ⟨0, certificate.rationalLength_pos δ certificate.initial⟩

def rationalCoordinates (δ : ℝ) (phase : Fin (certificate.rationalPeriod δ)) :
    (p : Fin L) × Fin (certificate.rationalLength δ p) :=
  finSigmaFinEquiv.symm phase

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem rationalCoordinates_phase (δ : ℝ) (p : Fin L)
    (l : Fin (certificate.rationalLength δ p)) :
    certificate.rationalCoordinates δ (certificate.rationalPhase δ p l) = ⟨p, l⟩ :=
  Equiv.symm_apply_apply finSigmaFinEquiv ⟨p, l⟩

omit [Fintype ι] [DecidableEq ι] in
theorem rationalPhase_coordinates (δ : ℝ) (phase : Fin (certificate.rationalPeriod δ)) :
    certificate.rationalPhase δ (certificate.rationalCoordinates δ phase).1
      (certificate.rationalCoordinates δ phase).2 = phase :=
  Equiv.apply_symm_apply finSigmaFinEquiv phase

/-- The actual singleton mixture conditional on reaching local date `l`. -/
def rationalLocalValue (δ : ℝ) (p : Fin L) (l : ℕ) : Payoff ι :=
  quittingSingletonArcPayoff
    (Math.rationalArcResidual (certificate.hazard p) (certificate.rationalLength δ p) l)
    (quittingSoloReward reward (certificate.owner p))
    (certificate.coarse (finRotate L p))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem rationalLocalValue_zero (δ : ℝ) (p : Fin L) :
    certificate.rationalLocalValue δ p 0 = certificate.coarse p := by
  unfold rationalLocalValue
  rw [Math.rationalArcResidual_start _ (certificate.rationalLength_pos δ p)]
  exact (certificate.arc p).symm

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem rationalLocalValue_end (δ : ℝ) (p : Fin L) :
    certificate.rationalLocalValue δ p (certificate.rationalLength δ p) =
      certificate.coarse (finRotate L p) := by
  funext who
  simp [rationalLocalValue, quittingSingletonArcPayoff]

omit [Fintype ι] [DecidableEq ι] in
theorem active_successor (p : Fin L) :
    certificate.coarse (finRotate L p) (certificate.owner p) =
      quittingSoloReward reward (certificate.owner p) (certificate.owner p) := by
  have harc := congrFun (certificate.arc p) (certificate.owner p)
  rw [certificate.active p] at harc
  dsimp only [quittingSingletonArcPayoff] at harc
  have hbalance : (1 - certificate.hazard p) *
      (certificate.coarse (finRotate L p) (certificate.owner p) -
        quittingSoloReward reward (certificate.owner p) (certificate.owner p)) = 0 := by
    nlinarith
  have heq := (mul_eq_zero.mp hbalance).resolve_left
    (ne_of_gt (sub_pos.mpr (certificate.hazard_lt_one p)))
  linarith

omit [Fintype ι] [DecidableEq ι] in
theorem rationalLocalValue_active (δ : ℝ) (p : Fin L) (l : ℕ) :
    certificate.rationalLocalValue δ p l (certificate.owner p) =
      quittingSoloReward reward (certificate.owner p) (certificate.owner p) := by
  unfold rationalLocalValue quittingSingletonArcPayoff
  rw [certificate.active_successor p]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem rationalLocalValue_floor (δ : ℝ) (p : Fin L) (l : ℕ)
    (hl : l ≤ certificate.rationalLength δ p) (who : ι) :
    quittingSoloReward reward who who ≤ certificate.rationalLocalValue δ p l who := by
  let q := certificate.hazard p
  let f := Math.rationalArcResidual q (certificate.rationalLength δ p) l
  have hf0 : 0 ≤ f := Math.rationalArcResidual_nonneg
    (certificate.hazard_nonneg p) (certificate.hazard_lt_one p)
    (certificate.rationalLength_pos δ p) hl
  have hfq : f ≤ q := Math.rationalArcResidual_le
    (certificate.hazard_nonneg p) (certificate.hazard_lt_one p)
    (certificate.rationalLength_pos δ p) hl
  have harc := congrFun (certificate.arc p) who
  have hstart := certificate.soloFloor p who
  have hnext := certificate.soloFloor (finRotate L p) who
  change quittingSoloReward reward who who ≤
    f * quittingSoloReward reward (certificate.owner p) who +
      (1 - f) * certificate.coarse (finRotate L p) who
  dsimp only [quittingSingletonArcPayoff] at harc
  by_cases hq : q = 0
  · have hf : f = 0 := by linarith
    simpa [hf] using hnext
  · have hqpos : 0 < q := lt_of_le_of_ne (certificate.hazard_nonneg p) (Ne.symm hq)
    have hmix := add_nonneg
      (mul_nonneg hf0 (sub_nonneg.mpr hstart))
      (mul_nonneg (sub_nonneg.mpr hfq) (sub_nonneg.mpr hnext))
    have hscaled : 0 ≤ q *
        (f * quittingSoloReward reward (certificate.owner p) who +
          (1 - f) * certificate.coarse (finRotate L p) who -
          quittingSoloReward reward who who) := by
      convert hmix using 1
      rw [harc]
      dsimp only [q]
      ring
    have hnonneg := (mul_nonneg_iff_of_pos_left hqpos).mp hscaled
    linarith

omit [Fintype ι] [DecidableEq ι] in
theorem rationalLocalValue_recursion (δ : ℝ) (p : Fin L)
    (l : Fin (certificate.rationalLength δ p)) :
    certificate.rationalLocalValue δ p l = quittingSingletonArcPayoff
      (Math.rationalArcHazard (certificate.hazard p) (certificate.rationalLength δ p) l)
      (quittingSoloReward reward (certificate.owner p))
      (certificate.rationalLocalValue δ p (l.val + 1)) := by
  have hstep := Math.rationalArcResidual_recursion
    (certificate.hazard_nonneg p) (certificate.hazard_lt_one p) l
  funext who
  dsimp only [rationalLocalValue, quittingSingletonArcPayoff]
  rw [hstep]
  ring

/-- Concrete Bernoulli singleton root at every chronological microphase. -/
def rationalRoot (δ : ℝ) (phase : Fin (certificate.rationalPeriod δ)) : ι → PMF Bool :=
  let coordinate := certificate.rationalCoordinates δ phase
  quittingSoloStationaryRoot (certificate.owner coordinate.1)
    (quittingHazardCoin
      (Math.rationalArcHazard (certificate.hazard coordinate.1)
        (certificate.rationalLength δ coordinate.1) coordinate.2)
      (Math.rationalArcHazard_nonneg (certificate.hazard_nonneg coordinate.1)
        (certificate.hazard_lt_one coordinate.1) coordinate.2)
      (Math.rationalArcHazard_lt_one (certificate.hazard_nonneg coordinate.1)
        (certificate.hazard_lt_one coordinate.1) coordinate.2).le)

omit [Fintype ι] in
/-- Normalize the dependent coordinates before using the local singleton root. -/
theorem rationalRoot_phase (δ : ℝ) (p : Fin L)
    (l : Fin (certificate.rationalLength δ p)) :
    certificate.rationalRoot δ (certificate.rationalPhase δ p l) =
      quittingSoloStationaryRoot (certificate.owner p)
        (quittingHazardCoin
          (Math.rationalArcHazard (certificate.hazard p) (certificate.rationalLength δ p) l)
          (Math.rationalArcHazard_nonneg (certificate.hazard_nonneg p)
            (certificate.hazard_lt_one p) l)
          (Math.rationalArcHazard_lt_one (certificate.hazard_nonneg p)
            (certificate.hazard_lt_one p) l).le) := by
  let coordinate := certificate.rationalCoordinates δ (certificate.rationalPhase δ p l)
  have hcoordinate : coordinate = ⟨p, l⟩ := certificate.rationalCoordinates_phase δ p l
  have howner : certificate.owner coordinate.1 = certificate.owner p :=
    congrArg (fun coordinate => certificate.owner coordinate.1) hcoordinate
  have hhazard : Math.rationalArcHazard (certificate.hazard coordinate.1)
      (certificate.rationalLength δ coordinate.1) coordinate.2 =
      Math.rationalArcHazard (certificate.hazard p) (certificate.rationalLength δ p) l :=
    congrArg (fun coordinate : (p : Fin L) × Fin (certificate.rationalLength δ p) =>
      Math.rationalArcHazard (certificate.hazard coordinate.1)
        (certificate.rationalLength δ coordinate.1) coordinate.2) hcoordinate
  dsimp only [coordinate] at hhazard
  unfold rationalRoot
  dsimp only
  rw [howner]
  congr 1
  apply _root_.Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro choice
  cases choice <;>
    simp only [quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal, hhazard]

def rationalValue (δ : ℝ) (phase : Fin (certificate.rationalPeriod δ)) : Payoff ι :=
  let coordinate := certificate.rationalCoordinates δ phase
  certificate.rationalLocalValue δ coordinate.1 coordinate.2

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem rationalValue_phase (δ : ℝ) (p : Fin L)
    (l : Fin (certificate.rationalLength δ p)) :
    certificate.rationalValue δ (certificate.rationalPhase δ p l) =
      certificate.rationalLocalValue δ p l := by
  unfold rationalValue
  rw [certificate.rationalCoordinates_phase]

omit [Fintype ι] [DecidableEq ι] in
theorem rationalValue_rotate_phase (δ : ℝ) (p : Fin L)
    (l : Fin (certificate.rationalLength δ p)) :
    certificate.rationalValue δ
      (finRotate (certificate.rationalPeriod δ) (certificate.rationalPhase δ p l)) =
        certificate.rationalLocalValue δ p (l.val + 1) := by
  change certificate.rationalValue δ
      (finRotate (∑ p, certificate.rationalLength δ p)
        (Math.finVariablePhase (certificate.rationalLength δ) p l)) = _
  have hl : l.val + 1 ≤ certificate.rationalLength δ p := l.isLt
  rcases hl.lt_or_eq with hl | hl
  · rw [Math.finRotate_finVariablePhase_inside (certificate.rationalLength δ) p l hl]
    exact certificate.rationalValue_phase δ p ⟨l.val + 1, hl⟩
  · rw [Math.finRotate_finVariablePhase_boundary (certificate.rationalLength δ)
      (certificate.rationalLength_pos δ) p l hl]
    change certificate.rationalValue δ
      (certificate.rationalPhase δ (finRotate L p)
        ⟨0, certificate.rationalLength_pos δ (finRotate L p)⟩) = _
    rw [certificate.rationalValue_phase, certificate.rationalLocalValue_zero, hl,
      certificate.rationalLocalValue_end]

/-- All inputs to the existing behavioral compiler are generated locally. -/
theorem rational_phase_certificate (δ : ℝ) (hδ : 0 < δ) {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (phase : Fin (certificate.rationalPeriod δ)) :
    certificate.rationalValue δ phase = quittingRootSuccessorPayoff reward
        (certificate.rationalValue δ (finRotate (certificate.rationalPeriod δ) phase))
        (certificate.rationalRoot δ phase) ∧
      (∀ who, quittingStationaryFixedOpponentsContinueReward reward
            (certificate.rationalRoot δ phase) who +
          quittingStationaryFixedOpponentsContinueMass (certificate.rationalRoot δ phase) who *
            certificate.rationalValue δ (finRotate (certificate.rationalPeriod δ) phase) who =
          certificate.rationalValue δ phase who) ∧
      ∀ who, quittingStationaryFixedOpponentsQuitValue reward
          (certificate.rationalRoot δ phase) who ≤
        certificate.rationalValue δ phase who + 2 * M * δ := by
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward ⟨{certificate.owner certificate.initial}, by simp⟩
      (certificate.owner certificate.initial))
  let p := (certificate.rationalCoordinates δ phase).1
  let l := (certificate.rationalCoordinates δ phase).2
  have hphase : certificate.rationalPhase δ p l = phase :=
    certificate.rationalPhase_coordinates δ phase
  rw [← hphase]
  rw [certificate.rationalValue_phase, certificate.rationalValue_rotate_phase]
  rw [certificate.rationalRoot_phase]
  let h := Math.rationalArcHazard (certificate.hazard p) (certificate.rationalLength δ p) l
  have hh0 : 0 ≤ h := Math.rationalArcHazard_nonneg
    (certificate.hazard_nonneg p) (certificate.hazard_lt_one p) l
  have hhδ : h ≤ δ := Math.rationalArcHazard_le_tolerance
    (certificate.hazard_nonneg p) (certificate.hazard_lt_one p) hδ l
  have hstep := certificate.rationalLocalValue_recursion δ p l
  constructor
  · rw [quittingRootSuccessorPayoff_solo]
    funext who
    simpa only [quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal,
      quittingSingletonArcPayoff] using congrFun hstep who
  constructor
  · intro who
    by_cases howner : who = certificate.owner p
    · subst who
      rw [quittingStationaryFixedOpponentsContinueReward_solo_owner,
        quittingStationaryFixedOpponentsContinueMass_solo_owner,
        certificate.rationalLocalValue_active, certificate.rationalLocalValue_active]
      ring
    · rw [quittingStationaryFixedOpponentsContinueReward_solo_other reward howner,
        quittingStationaryFixedOpponentsContinueMass_solo_other howner,
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
      exact (congrFun hstep who).symm
  · intro who
    by_cases howner : who = certificate.owner p
    · subst who
      rw [quittingStationaryFixedOpponentsQuitValue_solo_owner,
        certificate.rationalLocalValue_active]
      exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hM) hδ.le)
    · rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix reward howner,
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
      have hcollision := hreward ⟨{certificate.owner p, who}, by simp⟩ who
      have hsolo := hreward ⟨{who}, by simp⟩ who
      have hgap : max (quittingSingletonCollisionReward reward (certificate.owner p) who -
          quittingSoloReward reward who who) 0 ≤ 2 * M := by
        apply max_le
        · unfold quittingSingletonCollisionReward quittingSoloReward
          rw [abs_le] at hcollision hsolo
          linarith
        · positivity
      have hlocal : (1 - h) * quittingSoloReward reward who who +
          h * quittingSingletonCollisionReward reward (certificate.owner p) who ≤
          certificate.rationalLocalValue δ p l who + h * (2 * M) :=
        singletonQuitMix_le_value_add_hazard_mul hh0
          (certificate.rationalLocalValue_floor δ p l l.isLt.le who) hgap
      have hscaled := mul_le_mul_of_nonneg_left hhδ
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
      exact hlocal.trans (by nlinarith)

/-- Subdivision preserves every player's deleted-opponent survival product. -/
theorem rational_opponent_product (δ : ℝ) (who : ι) :
    (∏ phase : Fin (certificate.rationalPeriod δ),
      quittingStationaryFixedOpponentsContinueMass (certificate.rationalRoot δ phase) who) =
      ∏ p : Fin L, if who = certificate.owner p then 1 else 1 - certificate.hazard p := by
  change (∏ phase : Fin (∑ p, certificate.rationalLength δ p),
    quittingStationaryFixedOpponentsContinueMass (certificate.rationalRoot δ phase) who) = _
  rw [Math.prod_finVariablePhase (certificate.rationalLength δ)]
  apply Fintype.prod_congr
  intro p
  change (∏ l : Fin (certificate.rationalLength δ p),
    quittingStationaryFixedOpponentsContinueMass
      (certificate.rationalRoot δ (certificate.rationalPhase δ p l)) who) = _
  simp_rw [certificate.rationalRoot_phase]
  by_cases howner : who = certificate.owner p
  · subst who
    simp
  · simp only [howner, ↓reduceIte]
    simp_rw [quittingStationaryFixedOpponentsContinueMass_solo_other howner,
      quittingHazardCoin_false_toReal]
    have hprefix := Math.rationalArcPrefix_at_length (certificate.hazard_nonneg p)
      (certificate.hazard_lt_one p) (certificate.rationalLength_pos δ p)
    unfold Math.rationalArcPrefix at hprefix
    rw [← Fin.prod_univ_eq_prod_range (fun k : ℕ =>
      1 - Math.rationalArcHazard (certificate.hazard p) (certificate.rationalLength δ p) k)
      (certificate.rationalLength δ p)] at hprefix
    exact hprefix

theorem rational_opponent_contracts (δ : ℝ) (who : ι) :
    (∏ phase : Fin (certificate.rationalPeriod δ),
      quittingStationaryFixedOpponentsContinueMass (certificate.rationalRoot δ phase) who) <
        1 := by
  rw [certificate.rational_opponent_product δ who]
  exact certificate.toWithBounds.opponent_product_lt_one who

/-- Subdivision also preserves the joint one-cycle Continue probability. -/
theorem rational_joint_product (δ : ℝ) :
    (∏ phase : Fin (certificate.rationalPeriod δ),
      quittingStationaryContinueMass (certificate.rationalRoot δ phase)) =
        ∏ p : Fin L, (1 - certificate.hazard p) := by
  change (∏ phase : Fin (∑ p, certificate.rationalLength δ p),
    quittingStationaryContinueMass (certificate.rationalRoot δ phase)) = _
  rw [Math.prod_finVariablePhase (certificate.rationalLength δ)]
  apply Fintype.prod_congr
  intro p
  change (∏ l : Fin (certificate.rationalLength δ p),
    quittingStationaryContinueMass
      (certificate.rationalRoot δ (certificate.rationalPhase δ p l))) = _
  simp_rw [certificate.rationalRoot_phase]
  simp_rw [quittingStationaryContinueMass_solo, quittingHazardCoin_false_toReal]
  have hprefix := Math.rationalArcPrefix_at_length (certificate.hazard_nonneg p)
    (certificate.hazard_lt_one p) (certificate.rationalLength_pos δ p)
  unfold Math.rationalArcPrefix at hprefix
  rw [← Fin.prod_univ_eq_prod_range (fun k : ℕ =>
    1 - Math.rationalArcHazard (certificate.hazard p) (certificate.rationalLength δ p) k)
    (certificate.rationalLength δ p)] at hprefix
  exact hprefix

theorem rational_joint_contracts (δ : ℝ) :
    (∏ phase : Fin (certificate.rationalPeriod δ),
      quittingStationaryContinueMass (certificate.rationalRoot δ phase)) < 1 := by
  rw [certificate.rational_joint_product δ]
  let who := certificate.owner certificate.initial
  have hle : (∏ p : Fin L, (1 - certificate.hazard p)) ≤
      ∏ p : Fin L, if who = certificate.owner p then 1 else 1 - certificate.hazard p := by
    apply Finset.prod_le_prod₀
    · intro p _
      exact (sub_pos.mpr (certificate.hazard_lt_one p)).le
    · intro p _
      split_ifs
      · linarith [certificate.hazard_nonneg p]
      · exact le_rfl
  exact hle.trans_lt (certificate.toWithBounds.opponent_product_lt_one who)

/-- The produced infinite calendar, with complete history-independent prescriptions. -/
def rationalProfile (δ : ℝ) : (quittingGame reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward (certificate.rationalRoot δ)
    (certificate.rationalInitial δ)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem rationalValue_initial (δ : ℝ) :
    certificate.rationalValue δ (certificate.rationalInitial δ) =
      certificate.coarse certificate.initial := by
  simp [rationalInitial]

/-- Actual-source rational subdivision delivers the original target and controls
every complete behavioral replacement, including Never, with error `2*M*δ`. -/
theorem rational_isTerminalNash_and_hasValue (δ : ℝ) (hδ : 0 < δ)
    {M : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) (2 * M * δ)
        (certificate.rationalProfile δ) ∧
      quittingTerminalPayoff reward (certificate.rationalProfile δ) =
        certificate.coarse certificate.initial := by
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward ⟨{certificate.owner certificate.initial}, by simp⟩
      (certificate.owner certificate.initial))
  have hlocal := certificate.rational_phase_certificate δ hδ hreward
  have hpolicy := fun phase ↦ (hlocal phase).1
  have hcontinue := fun phase ↦ (hlocal phase).2.1
  have hquit := fun phase ↦ (hlocal phase).2.2
  have hcontracts := certificate.rational_opponent_contracts δ
  constructor
  · exact isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue
      reward (certificate.rationalRoot δ) (certificate.rationalValue δ)
      (certificate.rationalInitial δ)
      (mul_nonneg (mul_nonneg (by norm_num) hM) hδ.le)
      hM hreward hpolicy hquit hcontinue hcontracts
  · have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff
      reward (certificate.rationalRoot δ) (certificate.rationalValue δ) hpolicy hcontracts
    unfold rationalProfile
    rw [quittingTerminalPayoff_cyclicBehaviorProfile, ← hvalue]
    exact certificate.rationalValue_initial δ

/-- Players outside the image of the coarse owner map Continue at every history. -/
theorem rationalProfile_outside_continue (δ : ℝ) (who : ι)
    (houtside : ∀ p, who ≠ certificate.owner p) (time : ℕ)
    (history : (quittingGame reward).Hist time) :
    certificate.rationalProfile δ who time history = PMF.pure false := by
  unfold rationalProfile quittingCyclicBehaviorProfile quittingRootSequenceProfile
    quittingCyclicRootSequence rationalRoot quittingSoloStationaryRoot
  exact Function.update_of_ne (houtside _) _ _

omit [Fintype ι] in
/-- At its own scheduled date, the owner's Quit probability is the exact scalar hazard. -/
theorem rationalRoot_phase_quitMass (δ : ℝ) (p : Fin L)
    (l : Fin (certificate.rationalLength δ p)) :
    ((certificate.rationalRoot δ (certificate.rationalPhase δ p l)
      (certificate.owner p)) true).toReal =
        Math.rationalArcHazard (certificate.hazard p) (certificate.rationalLength δ p) l := by
  rw [certificate.rationalRoot_phase]
  simp [quittingSoloStationaryRoot]

omit [Fintype ι] in
/-- Rational coarse hazards yield literal rational prescribed marginal probabilities. -/
theorem rationalRoot_phase_quitMass_ratCast (δ : ℝ) (p : Fin L)
    (l : Fin (certificate.rationalLength δ p)) (q : ℚ)
    (hq : certificate.hazard p = (q : ℝ)) :
    ((certificate.rationalRoot δ (certificate.rationalPhase δ p l)
      (certificate.owner p)) true).toReal =
        ((q / ((certificate.rationalLength δ p : ℚ) - l.val * q) : ℚ) : ℝ) := by
  rw [certificate.rationalRoot_phase_quitMass, hq]
  exact (Math.rationalArcHazard_ratCast q (certificate.rationalLength δ p) l).symm

omit [Fintype ι] [DecidableEq ι] in
/-- Total microcycle length retains the source ceiling estimate. -/
theorem rationalPeriod_le (δ : ℝ) (hδ : 0 < δ) :
    (certificate.rationalPeriod δ : ℝ) ≤
      (L : ℝ) + (∑ p : Fin L, Math.rationalArcOdds (certificate.hazard p)) / δ := by
  unfold rationalPeriod rationalLength
  rw [Nat.cast_sum]
  calc
    (∑ p : Fin L, (Math.rationalArcLength (certificate.hazard p) δ : ℝ)) ≤
        ∑ p : Fin L, (1 + Math.rationalArcOdds (certificate.hazard p) / δ) := by
      exact Finset.sum_le_sum fun p _ => Math.rationalArcLength_le
        (certificate.hazard_nonneg p) (certificate.hazard_lt_one p) hδ
    _ = (L : ℝ) + (∑ p : Fin L, Math.rationalArcOdds (certificate.hazard p)) / δ := by
      simp [Finset.sum_add_distrib, Finset.sum_div]

end BalancedSingletonCycleCertificate

end GameTheory
