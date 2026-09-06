import UniformEquilibrium.Quitting.Paths.EarliestPositiveStageAbsorption
import MathUE.PMFProduct.FixedCardinalityRigidity

/-! # Pair-only actual terminal-law rigidity -/

noncomputable section

namespace GameTheory

open Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Whether a terminal outcome is a two-player coalition. -/
def IsQuittingPairOutcome : QuittingTerminalOutcome ι → Prop
  | none => False
  | some terminal => terminal.1.card = 2

instance instDecidableIsQuittingPairOutcome :
    DecidablePred (@IsQuittingPairOutcome ι) := fun outcome => by
  cases outcome <;> simp only [IsQuittingPairOutcome] <;> infer_instance

/-- Total actual terminal mass carried by two-player coalitions. -/
def quittingTerminalPairMass
    (profile : (quittingGame reward).BehaviorProfile) : ℝ := by
  classical
  exact ∑ outcome, if IsQuittingPairOutcome outcome then
      quittingTerminalOutcomeMass reward profile outcome else 0

omit [DecidableEq ι] in
private theorem terminalOutcomeMass_eq_zero_of_not_pair_of_pairMass_eq_one
    (profile : (quittingGame reward).BehaviorProfile)
    (hpair : quittingTerminalPairMass profile = 1)
    (outcome : QuittingTerminalOutcome ι)
    (houtcome : ¬ IsQuittingPairOutcome outcome) :
    quittingTerminalOutcomeMass reward profile outcome = 0 := by
  classical
  let mass := quittingTerminalOutcomeMass reward profile
  have hsimplex := quittingTerminalOutcomeMass_mem_stdSimplex reward profile
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    IsQuittingPairOutcome mass
  have hpair' : ∑ outcome ∈ Finset.univ.filter IsQuittingPairOutcome,
      mass outcome = 1 := by
    rw [quittingTerminalPairMass, ← Finset.sum_filter] at hpair
    exact hpair
  have hcomplement : ∑ candidate ∈
      Finset.univ.filter (fun x => ¬ IsQuittingPairOutcome x), mass candidate = 0 := by
    have := hsimplex.2
    change (∑ candidate, mass candidate) = 1 at this
    linarith
  have hle : mass outcome ≤ ∑ candidate ∈
      Finset.univ.filter (fun x => ¬ IsQuittingPairOutcome x), mass candidate := by
    apply Finset.single_le_sum (fun candidate _ => hsimplex.1 candidate)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact houtcome
  exact le_antisymm (by simpa [hcomplement] using hle) (hsimplex.1 outcome)

private theorem exists_positive_stageAbsorption_of_pairMass_eq_one
    (profile : (quittingGame reward).BehaviorProfile)
    (hpair : quittingTerminalPairMass profile = 1) :
    ∃ time, 0 < quittingStageAbsorptionMass profile time := by
  classical
  have hpositive : 0 < quittingTerminalPairMass profile := by rw [hpair]; norm_num
  simp only [quittingTerminalPairMass] at hpositive
  have hexistsOutcome : ∃ outcome, IsQuittingPairOutcome outcome ∧
      0 < quittingTerminalOutcomeMass reward profile outcome := by
    by_contra hnone
    push Not at hnone
    have hnonpos : quittingTerminalPairMass profile ≤ 0 := by
      unfold quittingTerminalPairMass
      exact Finset.sum_nonpos fun outcome _ => by
        split_ifs with hp
        · exact hnone outcome hp
        · exact le_rfl
    linarith
  obtain ⟨outcome, houtcome, hmass⟩ := hexistsOutcome
  cases outcome with
  | none => simp [IsQuittingPairOutcome] at houtcome
  | some terminal =>
    rw [quittingTerminalOutcomeMass_eq_timeDisintegration] at hmass
    have hstage : ∃ time,
        0 < quittingStageCoalitionMass reward profile time terminal := by
      by_contra hnone
      push Not at hnone
      have hstageZero : ∀ time,
          quittingStageCoalitionMass reward profile time terminal = 0 := by
        intro time
        exact le_antisymm (hnone time)
          (quittingStageCoalitionMass_nonneg reward profile time terminal)
      simp_rw [hstageZero] at hmass
      simp at hmass
    obtain ⟨time, htime⟩ := hstage
    refine ⟨time, lt_of_lt_of_le htime ?_⟩
    rw [← sum_quittingStageCoalitionMass_eq_stageAbsorptionMass]
    exact Finset.single_le_sum
      (fun candidate _ =>
        quittingStageCoalitionMass_nonneg reward profile time candidate)
      (Finset.mem_univ terminal)

/-- If an actual terminal law is entirely supported on pairs, one pair has
terminal mass one. -/
theorem exists_pair_terminalOutcomeMass_eq_one_of_terminalPairMass_eq_one
    (profile : (quittingGame reward).BehaviorProfile)
    (hpair : quittingTerminalPairMass profile = 1) :
    ∃ terminal : {S : Finset ι // S.Nonempty},
      terminal.1.card = 2 ∧
        quittingTerminalOutcomeMass reward profile (some terminal) = 1 := by
  classical
  obtain ⟨first, hpositive, _hbefore, hlive⟩ :=
    exists_earliestPositiveStageAbsorption_liveMass_eq_one profile
      (exists_positive_stageAbsorption_of_pairMass_eq_one profile hpair)
  have hsumPositive : 0 < ∑ terminal : {S : Finset ι // S.Nonempty},
      quittingStageCoalitionMass reward profile first terminal := by
    rw [sum_quittingStageCoalitionMass_eq_stageAbsorptionMass]
    exact hpositive
  have hexistsTerminal : ∃ terminal : {S : Finset ι // S.Nonempty},
      0 < quittingStageCoalitionMass reward profile first terminal := by
    by_contra hnone
    push Not at hnone
    have hnonpos : (∑ terminal : {S : Finset ι // S.Nonempty},
        quittingStageCoalitionMass reward profile first terminal) ≤ 0 :=
      Finset.sum_nonpos fun terminal _ => hnone terminal
    linarith
  obtain ⟨terminal, hterminalPositive⟩ := hexistsTerminal
  let root := quittingProfileLiveRoot reward profile first
  let action := quittingTerminalCoalitionAction terminal
  have hactionSupport : action ∈ (pmfPi root).support := by
    rw [PMF.mem_support_iff]
    have hrowPositive :
        0 < quittingLiveRowCoalitionMass reward profile first terminal := by
      rw [quittingStageCoalitionMass, hlive, one_mul] at hterminalPositive
      exact hterminalPositive
    unfold quittingLiveRowCoalitionMass at hrowPositive
    change 0 < ((pmfPi root) action).toReal at hrowPositive
    intro hzero
    rw [hzero] at hrowPositive
    simp at hrowPositive
  have hactionNonempty : (booleanActiveSet action).Nonempty := by
    simpa [booleanActiveSet, action, quittingTerminalCoalitionAction] using terminal.2
  have hpairOnly : ∀ candidate ∈ (pmfPi root).support,
      (booleanActiveSet candidate).Nonempty →
        (booleanActiveSet candidate).card = 2 := by
    intro candidate hcandidate hcandidateNonempty
    let candidateTerminal : {S : Finset ι // S.Nonempty} :=
      ⟨booleanActiveSet candidate, hcandidateNonempty⟩
    by_contra hcard
    have hnotPair : ¬ IsQuittingPairOutcome (some candidateTerminal) := by
      simpa [IsQuittingPairOutcome, candidateTerminal] using hcard
    have hterminalZero :=
      terminalOutcomeMass_eq_zero_of_not_pair_of_pairMass_eq_one
        profile hpair (some candidateTerminal) hnotPair
    have hcandidatePositive : 0 < ((pmfPi root) candidate).toReal := by
      exact ENNReal.toReal_pos ((PMF.mem_support_iff _ _).1 hcandidate)
        (PMF.apply_ne_top _ _)
    have hcandidateAction :
        quittingTerminalCoalitionAction candidateTerminal = candidate := by
      funext who
      cases hvalue : candidate who <;>
        simp [candidateTerminal, booleanActiveSet,
          quittingTerminalCoalitionAction, hvalue]
    have hstagePositive :
        0 < quittingStageCoalitionMass reward profile first candidateTerminal := by
      rw [quittingStageCoalitionMass, hlive, one_mul]
      unfold quittingLiveRowCoalitionMass
      change 0 < ((pmfPi root)
        (quittingTerminalCoalitionAction candidateTerminal)).toReal
      rw [hcandidateAction]
      exact hcandidatePositive
    have hle := quittingStageCoalitionMass_le_terminalOutcomeMass
      reward profile first candidateTerminal
    rw [hterminalZero] at hle
    linarith
  have hpure := pairOnlyProductRow_eq_deterministicPair root action
    hactionSupport hactionNonempty hpairOnly
  refine ⟨terminal, ?_, ?_⟩
  · have hactive : booleanActiveSet action = terminal.1 := by
      ext who
      simp [action, booleanActiveSet, quittingTerminalCoalitionAction]
    simpa [hactive] using hpure.1
  · have hrootMass : quittingRootCoalitionMass root terminal.1 = 1 := by
      rw [← quittingLiveRowCoalitionMass_eq_rootCoalitionMass]
      unfold quittingLiveRowCoalitionMass
      change ((pmfPi root) action).toReal = 1
      have hroot : root = fun who => PMF.pure (action who) := funext hpure.2
      rw [hroot, pmfPi_pure]
      simp
    have hstageOne : quittingStageCoalitionMass reward profile first terminal = 1 := by
      rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
        hlive, one_mul]
      exact hrootMass
    have hlower := quittingStageCoalitionMass_le_terminalOutcomeMass
      reward profile first terminal
    rw [hstageOne] at hlower
    have hsimplex := quittingTerminalOutcomeMass_mem_stdSimplex reward profile
    have hupper : quittingTerminalOutcomeMass reward profile (some terminal) ≤ 1 := by
      rw [← hsimplex.2]
      exact Finset.single_le_sum (fun outcome _ => hsimplex.1 outcome)
        (Finset.mem_univ (some terminal))
    exact le_antisymm hupper hlower

/-- No actual four-player profile realizes the uniform value `1/6` on every
pair outcome and zero on every other terminal outcome. -/
theorem no_finFour_profile_with_uniform_six_pair_terminalLaw
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    ¬ ∃ profile : (quittingGame reward).BehaviorProfile,
      ∀ outcome : QuittingTerminalOutcome (Fin 4),
        quittingTerminalOutcomeMass reward profile outcome =
          if IsQuittingPairOutcome outcome then (1 / 6 : ℝ) else 0 := by
  classical
  rintro ⟨profile, huniform⟩
  have hpair : quittingTerminalPairMass profile = 1 := by
    have hsimplex := quittingTerminalOutcomeMass_mem_stdSimplex reward profile
    rw [← hsimplex.2]
    unfold quittingTerminalPairMass
    apply Finset.sum_congr rfl
    intro outcome _
    rw [huniform]
    split_ifs <;> rfl
  obtain ⟨terminal, hterminalCard, hterminalOne⟩ :=
    exists_pair_terminalOutcomeMass_eq_one_of_terminalPairMass_eq_one
      profile hpair
  have huniformTerminal := huniform (some terminal)
  rw [if_pos (by simpa [IsQuittingPairOutcome] using hterminalCard)] at huniformTerminal
  rw [hterminalOne] at huniformTerminal
  norm_num at huniformTerminal

/-- The uniform `1/6` pair coordinates obey every two-coordinate square-root
inequality, despite not being an actual terminal law. -/
theorem uniformSixPairCoordinates_sqrt_add_sqrt_le_one :
    Real.sqrt (1 / 6 : ℝ) + Real.sqrt (1 / 6 : ℝ) ≤ 1 := by
  have hsqrt : Real.sqrt (1 / 6 : ℝ) ≤ 1 / 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  linarith

/-- The literal six-coordinate candidate law on four-player terminal
outcomes. -/
def uniformSixPairTerminalLaw : QuittingTerminalOutcome (Fin 4) → ℝ :=
  fun outcome => if IsQuittingPairOutcome outcome then 1 / 6 else 0

theorem uniformSixPairTerminalLaw_nonneg
    (outcome : QuittingTerminalOutcome (Fin 4)) :
    0 ≤ uniformSixPairTerminalLaw outcome := by
  unfold uniformSixPairTerminalLaw
  split_ifs <;> norm_num

theorem uniformSixPairTerminalLaw_sum_eq_one :
    ∑ outcome, uniformSixPairTerminalLaw outcome = 1 := by
  norm_num [uniformSixPairTerminalLaw, IsQuittingPairOutcome,
    Fin.sum_univ_succ]
  rw [← Finset.sum_filter]
  have hcard : (Finset.univ.filter (fun x : {S : Finset (Fin 4) // S.Nonempty} =>
      x.1.card = 2)).card = 6 := by decide
  rw [Finset.sum_const, hcard]
  norm_num

theorem uniformSixPairTerminalLaw_mem_stdSimplex :
    uniformSixPairTerminalLaw ∈
      stdSimplex ℝ (QuittingTerminalOutcome (Fin 4)) :=
  ⟨uniformSixPairTerminalLaw_nonneg, uniformSixPairTerminalLaw_sum_eq_one⟩

theorem uniformSixPairTerminalLaw_pair_sqrt
    (first second : QuittingTerminalOutcome (Fin 4))
    (hfirst : IsQuittingPairOutcome first)
    (hsecond : IsQuittingPairOutcome second) :
    Real.sqrt (uniformSixPairTerminalLaw first) +
        Real.sqrt (uniformSixPairTerminalLaw second) ≤ 1 := by
  rw [uniformSixPairTerminalLaw, if_pos hfirst,
    uniformSixPairTerminalLaw, if_pos hsecond]
  exact uniformSixPairCoordinates_sqrt_add_sqrt_le_one

/-- The uniform six-pair vector is a probability law satisfying every
pairwise square-root constraint, but is not an actual independent-clock
terminal law. -/
theorem uniformSixPairTerminalLaw_noncharacterization
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    uniformSixPairTerminalLaw ∈
        stdSimplex ℝ (QuittingTerminalOutcome (Fin 4)) ∧
      (∀ first second,
        IsQuittingPairOutcome first → IsQuittingPairOutcome second →
          Real.sqrt (uniformSixPairTerminalLaw first) +
            Real.sqrt (uniformSixPairTerminalLaw second) ≤ 1) ∧
      ¬ ∃ profile : (quittingGame reward).BehaviorProfile,
        quittingTerminalOutcomeMass reward profile = uniformSixPairTerminalLaw := by
  refine ⟨uniformSixPairTerminalLaw_mem_stdSimplex,
    fun first second => uniformSixPairTerminalLaw_pair_sqrt first second, ?_⟩
  rintro ⟨profile, hprofile⟩
  apply no_finFour_profile_with_uniform_six_pair_terminalLaw reward
  exact ⟨profile, fun outcome => congrFun hprofile outcome⟩

end GameTheory
