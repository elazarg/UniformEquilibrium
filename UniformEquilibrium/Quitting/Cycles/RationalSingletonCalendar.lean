import UniformEquilibrium.Quitting.Cycles.VariableSingletonCalendar

/-!
# Exact rational calendars from balanced singleton cycles

The tolerance selects positive phase lengths. The variable-length calendar
supplies the chronological root, phase values, survival products and exact
behavioral compiler; these legacy names retain the tolerance-selected interface.
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
def rationalPeriod (δ : ℝ) : ℕ :=
  variablePeriod (certificate.rationalLength δ)

/-- Chronological flattened index of a coarse phase and its local date. -/
def rationalPhase (δ : ℝ) (p : Fin L) (l : Fin (certificate.rationalLength δ p)) :
    Fin (certificate.rationalPeriod δ) :=
  variablePhase (certificate.rationalLength δ) p l

/-- Start at local date zero of the certificate's selected initial phase. -/
def rationalInitial (δ : ℝ) : Fin (certificate.rationalPeriod δ) :=
  certificate.variableInitial (certificate.rationalLength δ) (certificate.rationalLength_pos δ)

def rationalCoordinates (δ : ℝ) (phase : Fin (certificate.rationalPeriod δ)) :
    (p : Fin L) × Fin (certificate.rationalLength δ p) :=
  variableCoordinates (certificate.rationalLength δ) phase

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem rationalCoordinates_phase (δ : ℝ) (p : Fin L)
    (l : Fin (certificate.rationalLength δ p)) :
    certificate.rationalCoordinates δ (certificate.rationalPhase δ p l) = ⟨p, l⟩ := by
  exact variableCoordinates_phase (certificate.rationalLength δ) p l

omit [Fintype ι] [DecidableEq ι] in
theorem rationalPhase_coordinates (δ : ℝ) (phase : Fin (certificate.rationalPeriod δ)) :
    certificate.rationalPhase δ (certificate.rationalCoordinates δ phase).1
      (certificate.rationalCoordinates δ phase).2 = phase := by
  exact variablePhase_coordinates (certificate.rationalLength δ) phase

/-- The actual singleton mixture conditional on reaching local date `l`. -/
def rationalLocalValue (δ : ℝ) (p : Fin L) (l : ℕ) : Payoff ι :=
  certificate.variableLocalValue (certificate.rationalLength δ) p l

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem rationalLocalValue_zero (δ : ℝ) (p : Fin L) :
    certificate.rationalLocalValue δ p 0 = certificate.coarse p := by
  exact certificate.variableLocalValue_zero (certificate.rationalLength δ)
    (certificate.rationalLength_pos δ) p

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem rationalLocalValue_end (δ : ℝ) (p : Fin L) :
    certificate.rationalLocalValue δ p (certificate.rationalLength δ p) =
      certificate.coarse (finRotate L p) := by
  exact certificate.variableLocalValue_end (certificate.rationalLength δ) p

omit [Fintype ι] [DecidableEq ι] in
theorem rationalLocalValue_active (δ : ℝ) (p : Fin L) (l : ℕ) :
    certificate.rationalLocalValue δ p l (certificate.owner p) =
      quittingSoloReward reward (certificate.owner p) (certificate.owner p) := by
  exact certificate.variableLocalValue_active (certificate.rationalLength δ) p l

omit [Fintype ι] [DecidableEq ι] in
theorem rationalLocalValue_floor (δ : ℝ) (p : Fin L) (l : ℕ)
    (hl : l ≤ certificate.rationalLength δ p) (who : ι) :
    quittingSoloReward reward who who ≤ certificate.rationalLocalValue δ p l who := by
  exact certificate.variableLocalValue_floor (certificate.rationalLength δ)
    (certificate.rationalLength_pos δ) p l hl who

omit [Fintype ι] [DecidableEq ι] in
theorem rationalLocalValue_recursion (δ : ℝ) (p : Fin L)
    (l : Fin (certificate.rationalLength δ p)) :
    certificate.rationalLocalValue δ p l = quittingSingletonArcPayoff
      (Math.rationalArcHazard (certificate.hazard p) (certificate.rationalLength δ p) l)
      (quittingSoloReward reward (certificate.owner p))
      (certificate.rationalLocalValue δ p (l.val + 1)) := by
  exact certificate.variableLocalValue_recursion (certificate.rationalLength δ) p l

/-- Concrete Bernoulli singleton root at every chronological microphase. -/
def rationalRoot (δ : ℝ) (phase : Fin (certificate.rationalPeriod δ)) : ι → PMF Bool :=
  certificate.variableRoot (certificate.rationalLength δ) phase

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
  exact certificate.variableRoot_phase (certificate.rationalLength δ) p l

def rationalValue (δ : ℝ) (phase : Fin (certificate.rationalPeriod δ)) : Payoff ι :=
  certificate.variableValue (certificate.rationalLength δ) phase

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem rationalValue_phase (δ : ℝ) (p : Fin L)
    (l : Fin (certificate.rationalLength δ p)) :
    certificate.rationalValue δ (certificate.rationalPhase δ p l) =
      certificate.rationalLocalValue δ p l := by
  exact certificate.variableValue_phase (certificate.rationalLength δ) p l

omit [Fintype ι] [DecidableEq ι] in
theorem rationalValue_rotate_phase (δ : ℝ) (p : Fin L)
    (l : Fin (certificate.rationalLength δ p)) :
    certificate.rationalValue δ
      (finRotate (certificate.rationalPeriod δ) (certificate.rationalPhase δ p l)) =
        certificate.rationalLocalValue δ p (l.val + 1) := by
  exact certificate.variableValue_rotate_phase (certificate.rationalLength δ)
    (certificate.rationalLength_pos δ) p l

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
  exact certificate.variable_phase_certificate (certificate.rationalLength δ)
    (certificate.rationalLength_pos δ)
    δ hδ.le (fun p l => Math.rationalArcHazard_le_tolerance
      (certificate.hazard_nonneg p) (certificate.hazard_lt_one p) hδ l)
    hreward phase

/-- Subdivision preserves every player's deleted-opponent survival product. -/
theorem rational_opponent_product (δ : ℝ) (who : ι) :
    (∏ phase : Fin (certificate.rationalPeriod δ),
      quittingStationaryFixedOpponentsContinueMass (certificate.rationalRoot δ phase) who) =
      ∏ p : Fin L, if who = certificate.owner p then 1 else 1 - certificate.hazard p := by
  exact certificate.variable_opponent_product (certificate.rationalLength δ)
    (certificate.rationalLength_pos δ) who

theorem rational_opponent_contracts (δ : ℝ) (who : ι) :
    (∏ phase : Fin (certificate.rationalPeriod δ),
      quittingStationaryFixedOpponentsContinueMass (certificate.rationalRoot δ phase) who) <
        1 := by
  exact certificate.variable_opponent_contracts (certificate.rationalLength δ)
    (certificate.rationalLength_pos δ) who

/-- Subdivision also preserves the joint one-cycle Continue probability. -/
theorem rational_joint_product (δ : ℝ) :
    (∏ phase : Fin (certificate.rationalPeriod δ),
      quittingStationaryContinueMass (certificate.rationalRoot δ phase)) =
        ∏ p : Fin L, (1 - certificate.hazard p) := by
  exact certificate.variable_joint_product (certificate.rationalLength δ)
    (certificate.rationalLength_pos δ)

theorem rational_joint_contracts (δ : ℝ) :
    (∏ phase : Fin (certificate.rationalPeriod δ),
      quittingStationaryContinueMass (certificate.rationalRoot δ phase)) < 1 := by
  exact certificate.variable_joint_contracts (certificate.rationalLength δ)
    (certificate.rationalLength_pos δ)

/-- The produced infinite calendar, with complete history-independent prescriptions. -/
def rationalProfile (δ : ℝ) : (quittingGame reward).BehaviorProfile :=
  certificate.variableProfile (certificate.rationalLength δ) (certificate.rationalLength_pos δ)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem rationalValue_initial (δ : ℝ) :
    certificate.rationalValue δ (certificate.rationalInitial δ) =
      certificate.coarse certificate.initial := by
  exact certificate.variableValue_initial (certificate.rationalLength δ)
    (certificate.rationalLength_pos δ)

/-- Actual-source rational subdivision delivers the original target and controls
every complete behavioral replacement, including Never, with error `2*M*δ`. -/
theorem rational_isTerminalNash_and_hasValue (δ : ℝ) (hδ : 0 < δ)
    {M : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) (2 * M * δ)
        (certificate.rationalProfile δ) ∧
      quittingTerminalPayoff reward (certificate.rationalProfile δ) =
        certificate.coarse certificate.initial := by
  exact certificate.variable_isTerminalNash_and_hasValue (certificate.rationalLength δ)
    (certificate.rationalLength_pos δ)
    δ hδ.le (fun p l => Math.rationalArcHazard_le_tolerance
      (certificate.hazard_nonneg p) (certificate.hazard_lt_one p) hδ l)
    hreward

/-- Players outside the image of the coarse owner map Continue at every history. -/
theorem rationalProfile_outside_continue (δ : ℝ) (who : ι)
    (houtside : ∀ p, who ≠ certificate.owner p) (time : ℕ)
    (history : (quittingGame reward).Hist time) :
    certificate.rationalProfile δ who time history = PMF.pure false := by
  exact certificate.variableProfile_outside_continue (certificate.rationalLength δ)
    (certificate.rationalLength_pos δ) who houtside time history

omit [Fintype ι] in
/-- At its own scheduled date, the owner's Quit probability is the exact scalar hazard. -/
theorem rationalRoot_phase_quitMass (δ : ℝ) (p : Fin L)
    (l : Fin (certificate.rationalLength δ p)) :
    ((certificate.rationalRoot δ (certificate.rationalPhase δ p l)
      (certificate.owner p)) true).toReal =
        Math.rationalArcHazard (certificate.hazard p) (certificate.rationalLength δ p) l := by
  exact certificate.variableRoot_phase_quitMass (certificate.rationalLength δ) p l

omit [Fintype ι] in
/-- Rational coarse hazards yield literal rational prescribed marginal probabilities. -/
theorem rationalRoot_phase_quitMass_ratCast (δ : ℝ) (p : Fin L)
    (l : Fin (certificate.rationalLength δ p)) (q : ℚ)
    (hq : certificate.hazard p = (q : ℝ)) :
    ((certificate.rationalRoot δ (certificate.rationalPhase δ p l)
      (certificate.owner p)) true).toReal =
        ((q / ((certificate.rationalLength δ p : ℚ) - l.val * q) : ℚ) : ℝ) := by
  exact certificate.variableRoot_phase_quitMass_ratCast (certificate.rationalLength δ) p l q hq

omit [Fintype ι] [DecidableEq ι] in
/-- Total microcycle length retains the source ceiling estimate. -/
theorem rationalPeriod_le (δ : ℝ) (hδ : 0 < δ) :
    (certificate.rationalPeriod δ : ℝ) ≤
      (L : ℝ) + (∑ p : Fin L, Math.rationalArcOdds (certificate.hazard p)) / δ := by
  unfold rationalPeriod variablePeriod rationalLength
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
