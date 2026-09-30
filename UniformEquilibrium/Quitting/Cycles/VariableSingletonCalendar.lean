import MathUE.FinVariableCycle
import MathUE.RationalArcSubdivision
import UniformEquilibrium.Quitting.Cycles.BalancedSingletonCertificate

/-!
# Variable-length rational calendars from balanced singleton cycles

Each coarse phase has an arbitrary supplied positive length and uses
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

/-- Number of dates in one variable-length microcycle. -/
def variablePeriod (length : Fin L → ℕ) : ℕ := ∑ p, length p

/-- Chronological flattened index of a coarse phase and its local date. -/
def variablePhase (length : Fin L → ℕ) (p : Fin L) (l : Fin (length p)) :
    Fin (variablePeriod length) :=
  Math.finVariablePhase length p l

/-- Start at local date zero of the certificate's selected initial phase. -/
def variableInitial (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) : Fin
  (variablePeriod length) :=
  variablePhase length certificate.initial
    ⟨0, hlen certificate.initial⟩

def variableCoordinates (length : Fin L → ℕ) (phase : Fin
  (variablePeriod length)) :
    (p : Fin L) × Fin (length p) :=
  finSigmaFinEquiv.symm phase

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem variableCoordinates_phase (length : Fin L → ℕ) (p : Fin
  L)
    (l : Fin (length p)) :
    variableCoordinates length (variablePhase length p l) = ⟨p,
      l⟩ :=
  Equiv.symm_apply_apply finSigmaFinEquiv ⟨p, l⟩

omit [Fintype ι] [DecidableEq ι] in
theorem variablePhase_coordinates (length : Fin L → ℕ) (phase : Fin
  (variablePeriod length)) :
    variablePhase length (variableCoordinates length phase).1
      (variableCoordinates length phase).2 = phase :=
  Equiv.apply_symm_apply finSigmaFinEquiv phase

/-- The actual singleton mixture conditional on reaching local date `l`. -/
def variableLocalValue (length : Fin L → ℕ) (p : Fin L) (l : ℕ) :
  Payoff ι :=
  quittingSingletonArcPayoff
    (Math.rationalArcResidual (certificate.hazard p) (length p) l)
    (quittingSoloReward reward (certificate.owner p))
    (certificate.coarse (finRotate L p))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem variableLocalValue_zero (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) (p : Fin
  L) :
    certificate.variableLocalValue length p 0 = certificate.coarse p := by
  unfold variableLocalValue
  rw [Math.rationalArcResidual_start _ (hlen p)]
  exact (certificate.arc p).symm

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem variableLocalValue_end (length : Fin L → ℕ) (p : Fin L) :
    certificate.variableLocalValue length p (length p) =
      certificate.coarse (finRotate L p) := by
  funext who
  simp [variableLocalValue, quittingSingletonArcPayoff]

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
theorem variableLocalValue_active (length : Fin L → ℕ) (p : Fin L) (l :
  ℕ) :
    certificate.variableLocalValue length p l (certificate.owner p) =
      quittingSoloReward reward (certificate.owner p) (certificate.owner p) := by
  unfold variableLocalValue quittingSingletonArcPayoff
  rw [certificate.active_successor p]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem variableLocalValue_floor (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) (p : Fin L) (l : ℕ)
    (hl : l ≤ length p) (who : ι) :
    quittingSoloReward reward who who ≤ certificate.variableLocalValue length p l who := by
  let q := certificate.hazard p
  let f := Math.rationalArcResidual q (length p) l
  have hf0 : 0 ≤ f := Math.rationalArcResidual_nonneg
    (certificate.hazard_nonneg p) (certificate.hazard_lt_one p)
    (hlen p) hl
  have hfq : f ≤ q := Math.rationalArcResidual_le
    (certificate.hazard_nonneg p) (certificate.hazard_lt_one p)
    (hlen p) hl
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
theorem variableLocalValue_recursion (length : Fin L → ℕ) (p : Fin L)
    (l : Fin (length p)) :
    certificate.variableLocalValue length p l = quittingSingletonArcPayoff
      (Math.rationalArcHazard (certificate.hazard p) (length p) l)
      (quittingSoloReward reward (certificate.owner p))
      (certificate.variableLocalValue length p (l.val + 1)) := by
  have hstep := Math.rationalArcResidual_recursion
    (certificate.hazard_nonneg p) (certificate.hazard_lt_one p) l
  funext who
  dsimp only [variableLocalValue, quittingSingletonArcPayoff]
  rw [hstep]
  ring

/-- Concrete Bernoulli singleton root at every chronological microphase. -/
def variableRoot (length : Fin L → ℕ) (phase : Fin
  (variablePeriod length)) : ι → PMF Bool :=
  let coordinate := variableCoordinates length phase
  quittingSoloStationaryRoot (certificate.owner coordinate.1)
    (quittingHazardCoin
      (Math.rationalArcHazard (certificate.hazard coordinate.1)
        (length coordinate.1) coordinate.2)
      (Math.rationalArcHazard_nonneg (certificate.hazard_nonneg coordinate.1)
        (certificate.hazard_lt_one coordinate.1) coordinate.2)
      (Math.rationalArcHazard_lt_one (certificate.hazard_nonneg coordinate.1)
        (certificate.hazard_lt_one coordinate.1) coordinate.2).le)

omit [Fintype ι] in
/-- Normalize the dependent coordinates before using the local singleton root. -/
theorem variableRoot_phase (length : Fin L → ℕ) (p : Fin L)
    (l : Fin (length p)) :
    certificate.variableRoot length (variablePhase length p l) =
      quittingSoloStationaryRoot (certificate.owner p)
        (quittingHazardCoin
          (Math.rationalArcHazard (certificate.hazard p) (length p) l)
          (Math.rationalArcHazard_nonneg (certificate.hazard_nonneg p)
            (certificate.hazard_lt_one p) l)
          (Math.rationalArcHazard_lt_one (certificate.hazard_nonneg p)
            (certificate.hazard_lt_one p) l).le) := by
  let coordinate := variableCoordinates length (variablePhase length p l)
  have hcoordinate : coordinate = ⟨p, l⟩ := variableCoordinates_phase length p l
  have howner : certificate.owner coordinate.1 = certificate.owner p :=
    congrArg (fun coordinate => certificate.owner coordinate.1) hcoordinate
  have hhazard : Math.rationalArcHazard (certificate.hazard coordinate.1)
      (length coordinate.1) coordinate.2 =
      Math.rationalArcHazard (certificate.hazard p) (length p) l :=
    congrArg (fun coordinate : (p : Fin L) × Fin (length p) =>
      Math.rationalArcHazard (certificate.hazard coordinate.1)
        (length coordinate.1) coordinate.2) hcoordinate
  dsimp only [coordinate] at hhazard
  unfold variableRoot
  dsimp only
  rw [howner]
  congr 1
  apply _root_.Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro choice
  cases choice <;>
    simp only [quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal, hhazard]

def variableValue (length : Fin L → ℕ) (phase : Fin
  (variablePeriod length)) : Payoff ι :=
  let coordinate := variableCoordinates length phase
  certificate.variableLocalValue length coordinate.1 coordinate.2

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem variableValue_phase (length : Fin L → ℕ) (p : Fin L)
    (l : Fin (length p)) :
    certificate.variableValue length (variablePhase length p l) =
      certificate.variableLocalValue length p l := by
  unfold variableValue
  rw [variableCoordinates_phase]

omit [Fintype ι] [DecidableEq ι] in
theorem variableValue_rotate_phase (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) (p : Fin L)
    (l : Fin (length p)) :
    certificate.variableValue length
      (finRotate (variablePeriod length) (variablePhase length p
        l)) =
        certificate.variableLocalValue length p (l.val + 1) := by
  change certificate.variableValue length
      (finRotate (∑ p, length p)
        (Math.finVariablePhase length p l)) = _
  have hl : l.val + 1 ≤ length p := l.isLt
  rcases hl.lt_or_eq with hl | hl
  · rw [Math.finRotate_finVariablePhase_inside (length) p l hl]
    exact certificate.variableValue_phase length p ⟨l.val + 1, hl⟩
  · rw [Math.finRotate_finVariablePhase_boundary (length)
      hlen p l hl]
    change certificate.variableValue length
      (variablePhase length (finRotate L p)
        ⟨0, hlen (finRotate L p)⟩) = _
    rw [certificate.variableValue_phase,
      certificate.variableLocalValue_zero length hlen (finRotate L p), hl,
      certificate.variableLocalValue_end]

/-- All inputs to the existing behavioral compiler are generated locally. -/
theorem variable_phase_certificate (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) (cap : ℝ) (hcap
  : 0 ≤ cap)
    (hhazard : ∀ p (l : Fin (length p)),
      Math.rationalArcHazard (certificate.hazard p) (length p) l ≤ cap) {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (phase : Fin (variablePeriod length)) :
    certificate.variableValue length phase = quittingRootSuccessorPayoff reward
        (certificate.variableValue length (finRotate (variablePeriod length)
          phase))
        (certificate.variableRoot length phase) ∧
      (∀ who, quittingStationaryFixedOpponentsContinueReward reward
            (certificate.variableRoot length phase) who +
          quittingStationaryFixedOpponentsContinueMass (certificate.variableRoot length
            phase) who *
            certificate.variableValue length (finRotate (variablePeriod length) phase) who =
          certificate.variableValue length phase who) ∧
      ∀ who, quittingStationaryFixedOpponentsQuitValue reward
          (certificate.variableRoot length phase) who ≤
        certificate.variableValue length phase who + 2 * M * cap := by
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward ⟨{certificate.owner certificate.initial}, by simp⟩
      (certificate.owner certificate.initial))
  let p := (variableCoordinates length phase).1
  let l := (variableCoordinates length phase).2
  have hphase : variablePhase length p l = phase :=
    variablePhase_coordinates length phase
  rw [← hphase]
  rw [certificate.variableValue_phase, certificate.variableValue_rotate_phase length hlen p l]
  rw [certificate.variableRoot_phase]
  let h := Math.rationalArcHazard (certificate.hazard p) (length p) l
  have hh0 : 0 ≤ h := Math.rationalArcHazard_nonneg
    (certificate.hazard_nonneg p) (certificate.hazard_lt_one p) l
  have hhδ : h ≤ cap := hhazard p l
  have hstep := certificate.variableLocalValue_recursion length p l
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
        certificate.variableLocalValue_active, certificate.variableLocalValue_active]
      ring
    · rw [quittingStationaryFixedOpponentsContinueReward_solo_other reward howner,
        quittingStationaryFixedOpponentsContinueMass_solo_other howner,
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
      exact (congrFun hstep who).symm
  · intro who
    by_cases howner : who = certificate.owner p
    · subst who
      rw [quittingStationaryFixedOpponentsQuitValue_solo_owner,
        certificate.variableLocalValue_active]
      exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hM) hcap)
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
          certificate.variableLocalValue length p l who + h * (2 * M) :=
        singletonQuitMix_le_value_add_hazard_mul hh0
          (certificate.variableLocalValue_floor length hlen p l l.isLt.le who) hgap
      have hscaled := mul_le_mul_of_nonneg_left hhδ
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
      exact hlocal.trans (by nlinarith)

/-- Subdivision preserves every player's deleted-opponent survival product. -/
theorem variable_opponent_product (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) (who : ι) :
    (∏ phase : Fin (variablePeriod length),
      quittingStationaryFixedOpponentsContinueMass (certificate.variableRoot length phase)
        who) =
      ∏ p : Fin L, if who = certificate.owner p then 1 else 1 - certificate.hazard p := by
  change (∏ phase : Fin (∑ p, length p),
    quittingStationaryFixedOpponentsContinueMass (certificate.variableRoot length phase) who)
      = _
  rw [Math.prod_finVariablePhase length]
  apply Fintype.prod_congr
  intro p
  change (∏ l : Fin (length p),
    quittingStationaryFixedOpponentsContinueMass
      (certificate.variableRoot length (variablePhase length p l)) who) = _
  simp_rw [certificate.variableRoot_phase]
  by_cases howner : who = certificate.owner p
  · subst who
    simp
  · simp only [howner, ↓reduceIte]
    simp_rw [quittingStationaryFixedOpponentsContinueMass_solo_other howner,
      quittingHazardCoin_false_toReal]
    have hprefix := Math.rationalArcPrefix_at_length (certificate.hazard_nonneg p)
      (certificate.hazard_lt_one p) (hlen p)
    unfold Math.rationalArcPrefix at hprefix
    rw [← Fin.prod_univ_eq_prod_range (fun k : ℕ =>
      1 - Math.rationalArcHazard (certificate.hazard p) (length p) k)
      (length p)] at hprefix
    exact hprefix

theorem variable_opponent_contracts (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) (who : ι) :
    (∏ phase : Fin (variablePeriod length),
      quittingStationaryFixedOpponentsContinueMass (certificate.variableRoot length phase)
        who) <
        1 := by
  rw [certificate.variable_opponent_product length hlen who]
  exact certificate.toWithBounds.opponent_product_lt_one who

/-- Subdivision also preserves the joint one-cycle Continue probability. -/
theorem variable_joint_product (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) :
    (∏ phase : Fin (variablePeriod length),
      quittingStationaryContinueMass (certificate.variableRoot length phase)) =
        ∏ p : Fin L, (1 - certificate.hazard p) := by
  change (∏ phase : Fin (∑ p, length p),
    quittingStationaryContinueMass (certificate.variableRoot length phase)) = _
  rw [Math.prod_finVariablePhase length]
  apply Fintype.prod_congr
  intro p
  change (∏ l : Fin (length p),
    quittingStationaryContinueMass
      (certificate.variableRoot length (variablePhase length p l))) = _
  simp_rw [certificate.variableRoot_phase]
  simp_rw [quittingStationaryContinueMass_solo, quittingHazardCoin_false_toReal]
  have hprefix := Math.rationalArcPrefix_at_length (certificate.hazard_nonneg p)
    (certificate.hazard_lt_one p) (hlen p)
  unfold Math.rationalArcPrefix at hprefix
  rw [← Fin.prod_univ_eq_prod_range (fun k : ℕ =>
    1 - Math.rationalArcHazard (certificate.hazard p) (length p) k)
    (length p)] at hprefix
  exact hprefix

theorem variable_joint_contracts (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) :
    (∏ phase : Fin (variablePeriod length),
      quittingStationaryContinueMass (certificate.variableRoot length phase)) < 1 := by
  rw [certificate.variable_joint_product length hlen]
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

/-- The infinite calendar for the supplied positive phase lengths, with complete
  history-independent prescriptions. -/
def variableProfile (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) : (quittingGame
  reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward (certificate.variableRoot length)
    (certificate.variableInitial length hlen)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem variableValue_initial (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) :
    certificate.variableValue length (certificate.variableInitial length hlen) =
      certificate.coarse certificate.initial := by
  rw [variableInitial, certificate.variableValue_phase]
  exact certificate.variableLocalValue_zero length hlen certificate.initial

/-- The constructed phase values are actual terminal values for arbitrary positive lengths. -/
theorem variable_value_eq_actual (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) :
    certificate.variableValue length =
      quittingCyclicTerminalValue reward (certificate.variableRoot length) := by
  apply eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff
  · intro phase
    exact (certificate.variable_phase_certificate length hlen 1 (by norm_num)
      (fun p l => (Math.rationalArcHazard_lt_one (certificate.hazard_nonneg p)
        (certificate.hazard_lt_one p) l).le)
      (abs_reward_le_quittingRewardBound reward) phase).1
  · exact certificate.variable_opponent_contracts length hlen

/-- Every actual suffix selects the constructed chronological phase value. -/
theorem variable_rootSequence_terminalValue_eq
    (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p)
    (phase : Fin (variablePeriod length)) (time : ℕ) (who : ι) :
    quittingRootSequenceTerminalValue reward
        (quittingCyclicRootSequence (certificate.variableRoot length) phase) who time =
      certificate.variableValue length (quittingCyclicOrbit phase time) who := by
  rw [quittingRootSequenceTerminalValue_cyclic_eq,
    ← certificate.variable_value_eq_actual length hlen]

omit [Fintype ι] in
/-- Only the owner of the actual chronological phase may Quit. -/
theorem variableRoot_solo (length : Fin L → ℕ)
    (phase : Fin (variablePeriod length)) (other : ι)
    (hne : other ≠ certificate.owner (variableCoordinates length phase).1) :
    certificate.variableRoot length phase other = PMF.pure false := by
  dsimp only [variableRoot, quittingSoloStationaryRoot]
  exact Function.update_of_ne hne _ _

omit [Fintype ι] in
/-- The actual owner marginal is exactly the rational-function local hazard. -/
theorem variableRoot_quitMass (length : Fin L → ℕ)
    (phase : Fin (variablePeriod length)) :
    ((certificate.variableRoot length phase)
      (certificate.owner (variableCoordinates length phase).1) true).toReal =
      Math.rationalArcHazard
        (certificate.hazard (variableCoordinates length phase).1)
        (length (variableCoordinates length phase).1)
        (variableCoordinates length phase).2 := by
  simp [variableRoot, quittingSoloStationaryRoot]

/-- The same source delivers its fixed target and caps every complete behavioral replacement. -/
theorem variable_isTerminalNash_and_hasValue (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) (cap
  : ℝ) (hcap : 0 ≤ cap)
    (hhazard : ∀ p (l : Fin (length p)),
      Math.rationalArcHazard (certificate.hazard p) (length p) l ≤ cap)
    {M : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) (2 * M * cap)
        (certificate.variableProfile length hlen) ∧
      quittingTerminalPayoff reward (certificate.variableProfile length hlen) =
        certificate.coarse certificate.initial := by
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward ⟨{certificate.owner certificate.initial}, by simp⟩
      (certificate.owner certificate.initial))
  have hlocal := certificate.variable_phase_certificate length hlen cap hcap hhazard hreward
  have hpolicy := fun phase ↦ (hlocal phase).1
  have hcontinue := fun phase ↦ (hlocal phase).2.1
  have hquit := fun phase ↦ (hlocal phase).2.2
  have hcontracts := certificate.variable_opponent_contracts length hlen
  constructor
  · exact isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue
      reward (certificate.variableRoot length) (certificate.variableValue length)
      (certificate.variableInitial length hlen)
      (mul_nonneg (mul_nonneg (by norm_num) hM) hcap)
      hM hreward hpolicy hquit hcontinue hcontracts
  · have hvalue := certificate.variable_value_eq_actual length hlen
    unfold variableProfile
    rw [quittingTerminalPayoff_cyclicBehaviorProfile, ← hvalue]
    exact certificate.variableValue_initial length hlen

/-- Players outside the image of the coarse owner map Continue at every history. -/
theorem variableProfile_outside_continue (length : Fin L → ℕ) (hlen : ∀ p, 0 < length p) (who : ι)
    (houtside : ∀ p, who ≠ certificate.owner p) (time : ℕ)
    (history : (quittingGame reward).Hist time) :
    certificate.variableProfile length hlen who time history = PMF.pure false := by
  unfold variableProfile quittingCyclicBehaviorProfile quittingRootSequenceProfile
    quittingCyclicRootSequence variableRoot quittingSoloStationaryRoot
  exact Function.update_of_ne (houtside _) _ _

omit [Fintype ι] in
/-- At its own scheduled date, the owner's Quit probability is the exact scalar hazard. -/
theorem variableRoot_phase_quitMass (length : Fin L → ℕ) (p : Fin L)
    (l : Fin (length p)) :
    ((certificate.variableRoot length (variablePhase length p l)
      (certificate.owner p)) true).toReal =
        Math.rationalArcHazard (certificate.hazard p) (length p) l := by
  rw [certificate.variableRoot_phase]
  simp [quittingSoloStationaryRoot]

omit [Fintype ι] in
/-- Rational coarse hazards yield literal rational prescribed marginal probabilities. -/
theorem variableRoot_phase_quitMass_ratCast (length : Fin L → ℕ) (p :
  Fin L)
    (l : Fin (length p)) (q : ℚ)
    (hq : certificate.hazard p = (q : ℝ)) :
    ((certificate.variableRoot length (variablePhase length p l)
      (certificate.owner p)) true).toReal =
        ((q / ((length p : ℚ) - l.val * q) : ℚ) : ℝ) := by
  rw [certificate.variableRoot_phase_quitMass, hq]
  exact (Math.rationalArcHazard_ratCast q (length p) l).symm

end BalancedSingletonCycleCertificate

end GameTheory
