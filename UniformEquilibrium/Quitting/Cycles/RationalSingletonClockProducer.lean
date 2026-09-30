import MathUE.RationalCalendarSearch
import UniformEquilibrium.Quitting.Cycles.RationalSingletonFiniteCalendar
import UniformEquilibrium.Quitting.Cycles.CyclicFiniteMenu
import UniformEquilibrium.Quitting.Root.RationalFiniteClockLaw
import Mathlib.Data.Finset.Lattice.Fold

/-! # Actual finite rational clocks from the same singleton calendar

Rational owners, coarse hazards and an initial phase compute the exact mesh,
chronological rational root word, clock masses and power cutoff. Equality with
a supplied balanced certificate identifies this word with its actual calendar.
The existing full behavioral censor bounds then supply terminal accuracy at
the certificate's fixed target. Producing rational coarse hazards from a raw
reward table is a separate adapter.
-/

namespace GameTheory

open scoped BigOperators

/-- Executable calendar data; no strategy, continuation value or cap is a field. -/
structure RationalSingletonCalendarData (players phases : ℕ) where
  owner : Fin phases → Fin players
  initial : Fin phases
  hazard : Fin phases → ℚ
  hazard_nonneg : ∀ phase, 0 ≤ hazard phase
  hazard_lt_one : ∀ phase, hazard phase < 1

namespace RationalSingletonCalendarData

variable {players phases : ℕ} (data : RationalSingletonCalendarData players phases)

def length (δ : ℚ) (phase : Fin phases) : ℕ :=
  Math.rationalArcLengthRat (data.hazard phase) δ

theorem length_pos (δ : ℚ) (phase : Fin phases) : 0 < data.length δ phase :=
  Math.rationalArcLengthRat_pos _ _

def period (δ : ℚ) : ℕ := ∑ phase, data.length δ phase

def phase (δ : ℚ) (coarse : Fin phases) (localDate : Fin (data.length δ coarse)) :
    Fin (data.period δ) := finSigmaFinEquiv ⟨coarse, localDate⟩

def coordinates (δ : ℚ) (phase : Fin (data.period δ)) :
    (coarse : Fin phases) × Fin (data.length δ coarse) := finSigmaFinEquiv.symm phase

@[simp] theorem coordinates_phase (δ : ℚ) (coarse : Fin phases)
    (localDate : Fin (data.length δ coarse)) :
    data.coordinates δ (data.phase δ coarse localDate) = ⟨coarse, localDate⟩ :=
  Equiv.symm_apply_apply finSigmaFinEquiv ⟨coarse, localDate⟩

theorem phase_coordinates (δ : ℚ) (phase : Fin (data.period δ)) :
    data.phase δ (data.coordinates δ phase).1 (data.coordinates δ phase).2 = phase :=
  Equiv.apply_symm_apply finSigmaFinEquiv phase

def initialPhase (δ : ℚ) : Fin (data.period δ) :=
  data.phase δ data.initial ⟨0, data.length_pos δ data.initial⟩

def localHazard (δ : ℚ) (coarse : Fin phases)
    (localDate : Fin (data.length δ coarse)) : ℚ :=
  data.hazard coarse / ((data.length δ coarse : ℚ) - localDate.val * data.hazard coarse)

theorem localHazard_nonneg (δ : ℚ) (coarse : Fin phases)
    (localDate : Fin (data.length δ coarse)) : 0 ≤ data.localHazard δ coarse localDate := by
  have h := Math.rationalArcHazard_nonneg
    (show (0 : ℝ) ≤ (data.hazard coarse : ℝ) by exact_mod_cast data.hazard_nonneg coarse)
    (show (data.hazard coarse : ℝ) < 1 by exact_mod_cast data.hazard_lt_one coarse) localDate
  rw [← Math.rationalArcHazard_ratCast] at h
  exact_mod_cast h

theorem localHazard_lt_one (δ : ℚ) (coarse : Fin phases)
    (localDate : Fin (data.length δ coarse)) : data.localHazard δ coarse localDate < 1 := by
  have h := Math.rationalArcHazard_lt_one
    (show (0 : ℝ) ≤ (data.hazard coarse : ℝ) by exact_mod_cast data.hazard_nonneg coarse)
    (show (data.hazard coarse : ℝ) < 1 by exact_mod_cast data.hazard_lt_one coarse) localDate
  rw [← Math.rationalArcHazard_ratCast] at h
  exact_mod_cast h

def root (δ : ℚ) (phase : Fin (data.period δ)) : RationalQuittingRoot players where
  probability who :=
    let coordinate := data.coordinates δ phase
    if who = data.owner coordinate.1 then data.localHazard δ coordinate.1 coordinate.2 else 0
  nonnegative := by
    intro who
    dsimp only
    split_ifs
    · exact data.localHazard_nonneg δ _ _
    · exact le_rfl
  le_one := by
    intro who
    dsimp only
    split_ifs
    · exact (data.localHazard_lt_one δ _ _).le
    · norm_num

/-- The chronological orbit is computed with natural-number remainder. -/
def orbit (δ : ℚ) (time : ℕ) : Fin (data.period δ) :=
  ⟨((data.initialPhase δ).val + time) % data.period δ,
    Nat.mod_lt _ (data.initialPhase δ).pos⟩

def sequence (δ : ℚ) (time : ℕ) : RationalQuittingRoot players :=
  data.root δ (data.orbit δ time)

def word (δ : ℚ) (turns : ℕ) : List (RationalQuittingRoot players) :=
  List.ofFn fun time : Fin (turns * data.period δ) => data.sequence δ time.val

def mass (δ : ℚ) (turns : ℕ) (who : Fin players) :
    Option (Fin (turns * data.period δ)) → ℚ :=
  rationalFiniteClockMass (data.sequence δ) (turns * data.period δ) who

def opponentSurvival (who : Fin players) : ℚ :=
  ∏ phase, if who = data.owner phase then 1 else 1 - data.hazard phase

theorem opponentSurvival_nonneg (who : Fin players) : 0 ≤ data.opponentSurvival who := by
  apply Finset.prod_nonneg
  intro phase _
  split_ifs
  · norm_num
  · exact (sub_pos.mpr (data.hazard_lt_one phase)).le

/-- Maximum deleted-opponent survival, computed from the coarse rational hazards. -/
def survivalBound : ℚ :=
  Finset.univ.sup' ⟨data.owner data.initial, Finset.mem_univ _⟩ data.opponentSurvival

theorem opponentSurvival_le (who : Fin players) :
    data.opponentSurvival who ≤ data.survivalBound :=
  Finset.le_sup' _ (Finset.mem_univ who)

theorem survivalBound_nonneg : 0 ≤ data.survivalBound :=
  (data.opponentSurvival_nonneg (data.owner data.initial)).trans
    (data.opponentSurvival_le (data.owner data.initial))

/-- Exact terminating cutoff, including when some hazards are zero. -/
def turns (M η : ℚ) (hM : 0 < M) (hη : 0 < η)
    (hcontracts : data.survivalBound < 1) : ℕ :=
  Math.rationalPowerCutoff data.survivalBound (η / (6 * M))
    data.survivalBound_nonneg hcontracts (div_pos hη (by positivity))

theorem turns_pos (M η : ℚ) (hM : 0 < M) (hη : 0 < η)
    (hcontracts : data.survivalBound < 1) : 0 < data.turns M η hM hη hcontracts :=
  Math.rationalPowerCutoff_pos _ _ _ _ _

theorem turns_spec (M η : ℚ) (hM : 0 < M) (hη : 0 < η)
    (hcontracts : data.survivalBound < 1) (who : Fin players) :
    data.opponentSurvival who ^ data.turns M η hM hη hcontracts ≤ η / (6 * M) := by
  exact (pow_le_pow_left₀ (data.opponentSurvival_nonneg who)
    (data.opponentSurvival_le who) _).trans (Math.rationalPowerCutoff_spec _ _ _ _ _)

end RationalSingletonCalendarData

variable {players phases : ℕ}
variable {reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players)}

private theorem rationalOrbit_cast {n m : ℕ} (h : n = m) (phase : Fin n) (time : ℕ) :
    Fin.cast h ⟨(phase.val + time) % n, Nat.mod_lt _ phase.pos⟩ =
      quittingCyclicOrbit (Fin.cast h phase) time := by
  subst m
  rfl

namespace BalancedSingletonCycleCertificate

variable (certificate : BalancedSingletonCycleCertificate (L := phases) reward)

/-- Honest intermediate adapter: the rational hazards equal the same certificate's hazards. -/
def rationalClockData (q : Fin phases → ℚ)
    (hq : ∀ phase, certificate.hazard phase = (q phase : ℝ)) :
    RationalSingletonCalendarData players phases where
  owner := certificate.owner
  initial := certificate.initial
  hazard := q
  hazard_nonneg := by
    intro phase
    have h := certificate.hazard_nonneg phase
    rw [hq phase] at h
    exact_mod_cast h
  hazard_lt_one := by
    intro phase
    have h := certificate.hazard_lt_one phase
    rw [hq phase] at h
    exact_mod_cast h

variable (q : Fin phases → ℚ) (hq : ∀ phase, certificate.hazard phase = (q phase : ℝ))

theorem rationalClockData_length_eq (δ : ℚ) :
    (certificate.rationalClockData q hq).length δ = certificate.rationalLength (δ : ℝ) := by
  funext phase
  rw [RationalSingletonCalendarData.length, Math.rationalArcLengthRat_eq_real]
  simp only [rationalClockData, rationalLength, hq phase]

theorem rationalClockData_period_eq (δ : ℚ) :
    (certificate.rationalClockData q hq).period δ = certificate.rationalPeriod (δ : ℝ) := by
  unfold RationalSingletonCalendarData.period rationalPeriod variablePeriod
  rw [certificate.rationalClockData_length_eq q hq δ]

theorem rationalClockData_phase_cast (δ : ℚ) (phase : Fin phases)
    (localDate : Fin ((certificate.rationalClockData q hq).length δ phase)) :
    Fin.cast (certificate.rationalClockData_period_eq q hq δ)
        ((certificate.rationalClockData q hq).phase δ phase localDate) =
      certificate.rationalPhase (δ : ℝ) phase
        (Fin.cast (congrFun (certificate.rationalClockData_length_eq q hq δ) phase) localDate) :=
  Math.finVariablePhase_cast (certificate.rationalClockData_length_eq q hq δ) phase localDate

theorem rationalClockData_initial_cast (δ : ℚ) :
    Fin.cast (certificate.rationalClockData_period_eq q hq δ)
        ((certificate.rationalClockData q hq).initialPhase δ) =
      certificate.rationalInitial (δ : ℝ) := by
  unfold RationalSingletonCalendarData.initialPhase
  rw [certificate.rationalClockData_phase_cast q hq δ]
  rfl

theorem rationalClockData_root_toPMF (δ : ℚ)
    (phase : Fin ((certificate.rationalClockData q hq).period δ)) :
    ((certificate.rationalClockData q hq).root δ phase).toPMF =
      certificate.rationalRoot (δ : ℝ)
        (Fin.cast (certificate.rationalClockData_period_eq q hq δ) phase) := by
  let data := certificate.rationalClockData q hq
  let coarse := (data.coordinates δ phase).1
  let localDate := (data.coordinates δ phase).2
  have hphase := data.phase_coordinates δ phase
  change data.phase δ coarse localDate = phase at hphase
  rw [← hphase, certificate.rationalClockData_phase_cast q hq δ]
  rw [certificate.rationalRoot_phase]
  have hrate : (data.localHazard δ coarse localDate : ℝ) =
      Math.rationalArcHazard (certificate.hazard coarse)
        (certificate.rationalLength (δ : ℝ) coarse) localDate.val := by
    unfold RationalSingletonCalendarData.localHazard
    rw [Math.rationalArcHazard_ratCast]
    change Math.rationalArcHazard (q coarse : ℝ) (data.length δ coarse) localDate.val = _
    calc
      Math.rationalArcHazard (q coarse : ℝ) (data.length δ coarse) localDate.val =
          Math.rationalArcHazard (certificate.hazard coarse)
            (data.length δ coarse) localDate.val := by rw [hq coarse]
      _ = _ := congrArg
        (fun length : ℕ =>
          Math.rationalArcHazard (certificate.hazard coarse) length localDate.val)
        (congrFun (certificate.rationalClockData_length_eq q hq δ) coarse)
  funext who
  have hprob : (data.root δ (data.phase δ coarse localDate)).probability who =
      if who = certificate.owner coarse then data.localHazard δ coarse localDate else 0 := by
    exact congrArg
      (fun coordinate : (Σ phase, Fin (data.length δ phase)) =>
        if who = data.owner coordinate.1 then data.localHazard δ coordinate.1 coordinate.2
        else 0)
      (data.coordinates_phase δ coarse localDate)
  dsimp only [data] at hprob hrate
  dsimp only [data]
  apply _root_.Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro choice
  by_cases howner : who = certificate.owner coarse
  · subst who
    cases choice <;>
      simp [quittingSoloStationaryRoot, hprob, hrate]
  · cases choice <;>
      simp [quittingSoloStationaryRoot, howner, hprob]

/-- Every rational row is the corresponding row of the actual periodic calendar. -/
theorem rationalClockData_sequence_toPMF (δ : ℚ) (time : ℕ) :
    ((certificate.rationalClockData q hq).sequence δ time).toPMF =
      quittingCyclicRootSequence (certificate.rationalRoot (δ : ℝ))
        (certificate.rationalInitial (δ : ℝ)) time := by
  unfold RationalSingletonCalendarData.sequence
  rw [certificate.rationalClockData_root_toPMF q hq δ]
  unfold RationalSingletonCalendarData.orbit quittingCyclicRootSequence
  rw [rationalOrbit_cast, certificate.rationalClockData_initial_cast q hq δ]

theorem rationalClockData_opponentSurvival_cast (who : Fin players) :
    ((certificate.rationalClockData q hq).opponentSurvival who : ℝ) =
      ∏ phase, if who = certificate.owner phase then 1 else 1 - certificate.hazard phase := by
  unfold RationalSingletonCalendarData.opponentSurvival
  rw [Rat.cast_prod]
  apply Finset.prod_congr rfl
  intro phase _
  by_cases howner : who = certificate.owner phase
  · simp [rationalClockData, howner]
  · simp [rationalClockData, howner, hq phase]

theorem rationalClockData_survivalBound_lt_one :
    (certificate.rationalClockData q hq).survivalBound < 1 := by
  unfold RationalSingletonCalendarData.survivalBound
  apply (Finset.sup'_lt_iff
    (show (Finset.univ : Finset (Fin players)).Nonempty from
      ⟨certificate.owner certificate.initial, Finset.mem_univ _⟩)).mpr
  intro who _
  have h := certificate.toWithBounds.opponent_product_lt_one who
  change (∏ phase, if who = certificate.owner phase then 1
    else 1 - certificate.hazard phase) < 1 at h
  rw [← certificate.rationalClockData_opponentSurvival_cast q hq who] at h
  exact_mod_cast h

/-- The exact rational cutoff discharges every player's censor-survival bound. -/
theorem rationalClockData_turns_cut {M η : ℚ} (hM : 0 < M) (hη : 0 < η)
    (who : Fin players) :
    (∏ phase, if who = certificate.owner phase then 1 else 1 - certificate.hazard phase) ^
        (certificate.rationalClockData q hq).turns M η hM hη
          (certificate.rationalClockData_survivalBound_lt_one q hq) ≤
      (η : ℝ) / (6 * (M : ℝ)) := by
  rw [← certificate.rationalClockData_opponentSurvival_cast q hq who]
  exact_mod_cast (certificate.rationalClockData q hq).turns_spec M η hM hη
    (certificate.rationalClockData_survivalBound_lt_one q hq) who

/-- The actual finite rational independent laws realize the same source calendar,
retain exact rational masses, and satisfy its full terminal accuracy bounds.
The coarse target is fixed before either rational accuracy or the cutoff. -/
theorem exists_rationalClocks_isTerminalNash_and_delivery
    {M η : ℚ} (hη : 0 < η) (hηM : η ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ (M : ℝ)) :
    let data := certificate.rationalClockData q hq
    let turns := data.turns M η (hη.trans_le hηM) hη
      (certificate.rationalClockData_survivalBound_lt_one q hq)
    let δ := η / (4 * M)
    ∃ mixed : Fin players → PMF (Option (Fin (turns * data.period δ))),
      (∀ who choice, (mixed who choice).toReal = (data.mass δ turns who choice : ℝ)) ∧
      (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        quittingBehaviorStoppingLaw reward
          (certificate.rationalFiniteProfile (δ : ℝ) turns who)) ∧
      quittingTerminalSemanticPair reward
          (quittingFiniteDeadlineTimingProfile reward (turns * data.period δ) mixed) =
        quittingTerminalSemanticPair reward (certificate.rationalFiniteProfile (δ : ℝ) turns) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) (η : ℝ)
        (quittingFiniteDeadlineTimingProfile reward (turns * data.period δ) mixed) ∧
      (∀ who, |quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward (turns * data.period δ) mixed) who -
          certificate.coarse certificate.initial who| ≤ (η : ℝ) / 6) ∧
      (∀ who, (∀ phase, who ≠ certificate.owner phase) → mixed who = PMF.pure none) ∧
      ((turns * data.period δ : ℕ) : ℝ) ≤ (turns : ℝ) *
        ((phases : ℝ) + (4 * (M : ℝ) / (η : ℝ)) *
          ∑ phase, Math.rationalArcOdds (certificate.hazard phase)) := by
  let data := certificate.rationalClockData q hq
  have hM : 0 < M := hη.trans_le hηM
  let turns := data.turns M η hM hη (certificate.rationalClockData_survivalBound_lt_one q hq)
  let δ : ℚ := η / (4 * M)
  have hturns : 0 < turns := data.turns_pos _ _ _ _ _
  have hdeadline : 0 < turns * data.period δ :=
    Nat.mul_pos hturns (data.initialPhase δ).pos
  have hsequence : (fun time => (data.sequence δ time).toPMF) =
      quittingCyclicRootSequence (certificate.rationalRoot (δ : ℝ))
        (certificate.rationalInitial (δ : ℝ)) := by
    funext time
    exact certificate.rationalClockData_sequence_toPMF q hq δ time
  have hprofile : quittingRootSequenceProfile reward
      (quittingTruncatedRoots (fun time => (data.sequence δ time).toPMF)
        (turns * data.period δ)) 0 = certificate.rationalFiniteProfile (δ : ℝ) turns := by
    rw [hsequence, certificate.rationalClockData_period_eq q hq δ,
      ← quittingCyclicFiniteProfile_eq_truncatedRootProfile]
    rfl
  obtain ⟨mixed, hmass, hlaws, hpair⟩ :=
    exists_rationalFiniteClockLaws_exact reward (data.sequence δ) _ hdeadline
  rw [hprofile] at hlaws hpair
  have hsource := certificate.rationalFiniteProfile_isTerminalNash_and_delivery_le
    hreward (show (0 : ℝ) < (η : ℝ) by exact_mod_cast hη)
    (show (η : ℝ) ≤ (M : ℝ) by exact_mod_cast hηM) turns
    (certificate.rationalClockData_turns_cut q hq hM hη)
  have hδcast : (δ : ℝ) = (η : ℝ) / (4 * (M : ℝ)) := by simp [δ]
  rw [← hδcast] at hsource
  have hpay := congrArg Prod.fst hpair
  have hcap := congrArg Prod.snd hpair
  change quittingTerminalPayoff reward _ = quittingTerminalPayoff reward _ at hpay
  change quittingContinuationBestResponseValue reward _ =
    quittingContinuationBestResponseValue reward _ at hcap
  refine ⟨mixed, hmass, hlaws, hpair, ?_, ?_, ?_, ?_⟩
  · intro who deviation
    have hreply := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (quittingFiniteDeadlineTimingProfile reward _ mixed) who deviation
    rw [hcap] at hreply
    rw [hpay]
    apply hreply.trans
    unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, certificate.rationalFiniteProfile (δ : ℝ) turns who, rfl⟩
    · rintro value ⟨response, rfl⟩
      exact hsource.1 who response
  · intro who
    rw [hpay]
    exact hsource.2 who
  · intro who hout
    apply rationalFiniteClockLaw_eq_pure_none_of_zero (data.sequence δ) _ who (mixed who)
      (hmass who)
    intro time _
    simp [RationalSingletonCalendarData.sequence, RationalSingletonCalendarData.root,
      data, rationalClockData, hout]
  · rw [certificate.rationalClockData_period_eq q hq δ, hδcast]
    exact certificate.rationalFiniteProfile_dateCount_le
      (show (0 : ℝ) < (η : ℝ) by exact_mod_cast hη)
      (show (η : ℝ) ≤ (M : ℝ) by exact_mod_cast hηM) turns

end BalancedSingletonCycleCertificate

end GameTheory
