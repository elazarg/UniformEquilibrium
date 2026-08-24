/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.HarmonicStateAccount

/-!
# A defective-renewal obstruction to the visit-epoch factorization

The one-state visit-epoch factorization proposed after the failure of the
conditional return bound is also false.  The obstruction needs a nontrivial
return-time phase: return after one step with probability `1 / 5`, return
after three steps with probability `7 / 10`, and never return with probability
`1 / 10`.  The nonreturn value has four-periodic phases `0, 0, 1, 1`.

The exact backward-harmonic values at the renewal state are
`12 / 25, 11 / 25, 13 / 25, 14 / 25`.  Starting in phase zero, the expected
numbers of visits in the four phases are `288 / 95, 206 / 95, 212 / 95,
244 / 95`.  Consequently the variation charged to this one renewal state is
`478 / 475 > 1`, whereas its total nonreturn visit charge is exactly one.

This finite scalar calculation is realized by a seven-state homogeneous
Markov chain: one renewal state, a deterministic two-state corridor for the
three-step return, and a deterministic four-cycle carrying the nonreturn
phase values.  The calculation refutes the per-state aggregate renewal
factorization.  It does not refute Simon's overall cardinality bound, whose
right-hand side for that realization is seven rather than one.
-/

namespace Math.Probability

noncomputable section

namespace DefectiveRenewalVisitEpochCounterexample

abbrev Phase := Fin 4

/-- Addition of one to the phase, written explicitly for computation. -/
def advanceOne : Phase → Phase
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 0

/-- Addition of three to the phase, written explicitly for computation. -/
def advanceThree : Phase → Phase
  | 0 => 3
  | 1 => 0
  | 2 => 1
  | 3 => 2

/-- The four-periodic value obtained upon the nonreturn branch. -/
def nonreturnValue : Phase → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1

/-- The unique four-periodic backward-harmonic value at the renewal state. -/
def renewalValue : Phase → ℝ
  | 0 => 12 / 25
  | 1 => 11 / 25
  | 2 => 13 / 25
  | 3 => 14 / 25

theorem renewalValue_mem_Icc (phase : Phase) :
    renewalValue phase ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases phase <;> norm_num [renewalValue]

/-- The displayed values obey the defective renewal equation exactly. -/
theorem renewalValue_eq_expect_successor (phase : Phase) :
    renewalValue phase =
      (1 / 5 : ℝ) * renewalValue (advanceOne phase) +
        (7 / 10 : ℝ) * renewalValue (advanceThree phase) +
          (1 / 10 : ℝ) * nonreturnValue phase := by
  fin_cases phase <;>
    norm_num [renewalValue, advanceOne, advanceThree, nonreturnValue]

/-- Conditional absolute variation at one visit in the displayed phase. -/
def localVariation (phase : Phase) : ℝ :=
  (1 / 5 : ℝ) *
      |renewalValue (advanceOne phase) - renewalValue phase| +
    (7 / 10 : ℝ) *
      |renewalValue (advanceThree phase) - renewalValue phase| +
    (1 / 10 : ℝ) *
      |nonreturnValue phase - renewalValue phase|

/-- The computed four-periodic local variation. -/
def displayedLocalVariation : Phase → ℝ
  | 0 => 14 / 125
  | 1 => 11 / 125
  | 2 => 14 / 125
  | 3 => 11 / 125

theorem localVariation_eq (phase : Phase) :
    localVariation phase = displayedLocalVariation phase := by
  fin_cases phase <;>
    norm_num [localVariation, renewalValue, advanceOne, advanceThree,
      nonreturnValue, displayedLocalVariation]

/-- Expected numbers of visits in each phase, starting from phase zero. -/
def occupationWeight : Phase → ℝ
  | 0 => 288 / 95
  | 1 => 206 / 95
  | 2 => 212 / 95
  | 3 => 244 / 95

/-- The predecessor phase for a one-step return. -/
def predecessorOne : Phase → Phase
  | 0 => 3
  | 1 => 0
  | 2 => 1
  | 3 => 2

/-- The predecessor phase for a three-step return. -/
def predecessorThree : Phase → Phase
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 0

/-- The occupation weights solve the exact renewal resolvent equation. -/
theorem occupationWeight_balance (phase : Phase) :
    occupationWeight phase =
      (if phase = 0 then 1 else 0) +
        (1 / 5 : ℝ) * occupationWeight (predecessorOne phase) +
          (7 / 10 : ℝ) * occupationWeight (predecessorThree phase) := by
  fin_cases phase <;>
    norm_num [occupationWeight, predecessorOne, predecessorThree]

theorem sum_occupationWeight :
    ∑ phase, occupationWeight phase = (10 : ℝ) := by
  norm_num [occupationWeight, Fin.sum_univ_four]

/-- The total variation owned by the renewal state is strictly above one. -/
theorem sum_occupationWeight_mul_localVariation :
    ∑ phase, occupationWeight phase * localVariation phase =
      (478 / 475 : ℝ) := by
  norm_num [occupationWeight, localVariation, renewalValue, advanceOne,
    advanceThree, nonreturnValue, Fin.sum_univ_four]

/-- The total nonreturn visit charge is exactly one. -/
theorem nonreturnCharge_eq_one :
    (1 / 10 : ℝ) * ∑ phase, occupationWeight phase = 1 := by
  rw [sum_occupationWeight]
  norm_num

/-- Exact failure of the scalar aggregate visit-epoch comparison. -/
theorem not_variation_le_nonreturnCharge :
    ¬ (∑ phase, occupationWeight phase * localVariation phase) ≤
      (1 / 10 : ℝ) * ∑ phase, occupationWeight phase := by
  rw [sum_occupationWeight_mul_localVariation, nonreturnCharge_eq_one]
  norm_num

end DefectiveRenewalVisitEpochCounterexample

/-! ## Homogeneous seven-state realization -/

namespace SevenStateVisitEpochCounterexample

inductive State
  | owner
  | corridorFirst
  | corridorSecond
  | cycleZero
  | cycleOne
  | cycleTwo
  | cycleThree
  deriving DecidableEq, Fintype

def ownerWeights : State → ENNReal
  | .owner => ENNReal.ofReal (1 / 5 : ℝ)
  | .corridorFirst => ENNReal.ofReal (7 / 10 : ℝ)
  | .corridorSecond => 0
  | .cycleZero => ENNReal.ofReal (1 / 10 : ℝ)
  | .cycleOne => 0
  | .cycleTwo => 0
  | .cycleThree => 0

private theorem state_univ : (Finset.univ : Finset State) =
    {.owner, .corridorFirst, .corridorSecond, .cycleZero, .cycleOne,
      .cycleTwo, .cycleThree} := by
  decide

theorem ownerWeights_sum : ∑ state, ownerWeights state = 1 := by
  classical
  rw [state_univ]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [ownerWeights, add_zero, zero_add]
  rw [← ENNReal.ofReal_add]
  rw [← ENNReal.ofReal_add]
  norm_num
  all_goals positivity

/-- The renewal state branches to itself, a two-state return corridor, or a
deterministic four-cycle. -/
def kernel : State → PMF State := fun state =>
  match state with
  | .owner => PMF.ofFintype ownerWeights ownerWeights_sum
  | .corridorFirst => PMF.pure .corridorSecond
  | .corridorSecond => PMF.pure .owner
  | .cycleZero => PMF.pure .cycleOne
  | .cycleOne => PMF.pure .cycleTwo
  | .cycleTwo => PMF.pure .cycleThree
  | .cycleThree => PMF.pure .cycleZero

private theorem mod_four_cases (time : ℕ) :
    time % 4 = 0 ∨ time % 4 = 1 ∨ time % 4 = 2 ∨ time % 4 = 3 := by
  omega

def renewalTimeValue (time : ℕ) : ℝ :=
  if time % 4 = 0 then 12 / 25
  else if time % 4 = 1 then 11 / 25
  else if time % 4 = 2 then 13 / 25
  else 14 / 25

def cycleTimeValue (state : State) (time : ℕ) : ℝ :=
  if state = .cycleZero then
    if time % 4 = 0 ∨ time % 4 = 3 then 1 else 0
  else if state = .cycleOne then
    if time % 4 = 0 ∨ time % 4 = 1 then 1 else 0
  else if state = .cycleTwo then
    if time % 4 = 1 ∨ time % 4 = 2 then 1 else 0
  else if time % 4 = 2 ∨ time % 4 = 3 then 1 else 0

/-- The space-time value extending the four-phase renewal calculation along
the deterministic corridor and cycle. -/
def value (state : State) (time : ℕ) : ℝ :=
  match state with
  | .owner => renewalTimeValue time
  | .corridorFirst => renewalTimeValue (time + 2)
  | .corridorSecond => renewalTimeValue (time + 1)
  | state => cycleTimeValue state time

theorem value_mem_Icc (state : State) (time : ℕ) :
    value state time ∈ Set.Icc (0 : ℝ) 1 := by
  cases state <;>
    simp [value, renewalTimeValue, cycleTimeValue] <;>
    split_ifs <;> norm_num

private theorem expect_ownerWeights (f : State → ℝ) :
    expect (PMF.ofFintype ownerWeights ownerWeights_sum) f =
      (1 / 5 : ℝ) * f .owner +
        (7 / 10 : ℝ) * f .corridorFirst +
          (1 / 10 : ℝ) * f .cycleZero := by
  rw [expect_eq_sum]
  rw [show (∑ x, (PMF.ofFintype ownerWeights ownerWeights_sum x).toReal * f x) =
      ∑ x ∈ (Finset.univ : Finset State),
        (PMF.ofFintype ownerWeights ownerWeights_sum x).toReal * f x by simp]
  rw [state_univ]
  simp [PMF.ofFintype_apply, ownerWeights]
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 7 / 10)]
  ring

private theorem value_owner_harmonic (time : ℕ) :
    value .owner time =
      (1 / 5 : ℝ) * value .owner (time + 1) +
        (7 / 10 : ℝ) * value .corridorFirst (time + 1) +
          (1 / 10 : ℝ) * value .cycleZero (time + 1) := by
  rcases mod_four_cases time with htime | htime | htime | htime
  · have h1 : (time + 1) % 4 = 1 := by omega
    have h2 : (time + 2) % 4 = 2 := by omega
    have h3 : (time + 3) % 4 = 3 := by omega
    norm_num [value, renewalTimeValue, cycleTimeValue, htime, h1, h2, h3]
  · have h1 : (time + 1) % 4 = 2 := by omega
    have h2 : (time + 2) % 4 = 3 := by omega
    have h3 : (time + 3) % 4 = 0 := by omega
    norm_num [value, renewalTimeValue, cycleTimeValue, htime, h1, h2, h3]
  · have h1 : (time + 1) % 4 = 3 := by omega
    have h2 : (time + 2) % 4 = 0 := by omega
    have h3 : (time + 3) % 4 = 1 := by omega
    norm_num [value, renewalTimeValue, cycleTimeValue, htime, h1, h2, h3]
  · have h1 : (time + 1) % 4 = 0 := by omega
    have h2 : (time + 2) % 4 = 1 := by omega
    have h3 : (time + 3) % 4 = 2 := by omega
    norm_num [value, renewalTimeValue, cycleTimeValue, htime, h1, h2, h3]

/-- The seven-state value is bounded backward harmonic for the homogeneous
kernel. -/
theorem value_isUnitIntervalBackwardMarkovHarmonic :
    IsUnitIntervalBackwardMarkovHarmonic kernel value := by
  refine ⟨value_mem_Icc, ?_⟩
  intro state time
  cases state with
  | owner =>
    rw [show kernel .owner =
        PMF.ofFintype ownerWeights ownerWeights_sum by rfl]
    rw [expect_ownerWeights]
    exact value_owner_harmonic time
  | corridorFirst => simp [kernel, value]
  | corridorSecond => simp [kernel, value]
  | cycleZero =>
      simp [kernel, value, cycleTimeValue]
      split_ifs <;> norm_num <;> omega
  | cycleOne =>
      simp [kernel, value, cycleTimeValue]
      split_ifs <;> norm_num <;> omega
  | cycleTwo =>
      simp [kernel, value, cycleTimeValue]
      split_ifs <;> norm_num <;> omega
  | cycleThree =>
      simp [kernel, value, cycleTimeValue]
      split_ifs <;> norm_num <;> omega

end SevenStateVisitEpochCounterexample

/-! ## Finite-history marginal adapter -/

/-- Under the adaptive-history presentation of a homogeneous chain, the last
state of a positive-length history has the ordinary iterated-kernel marginal. -/
theorem expect_adaptiveHistoryLaw_homogeneous_last
    {S : Type*} [Fintype S]
    (initial : S) (kernel : S → PMF S) (time : ℕ) (f : S → ℝ) :
    expect
        (adaptiveHistoryLaw (homogeneousMarkovStep initial kernel) (time + 1))
        (fun history => f (history (Fin.last time))) =
      expect (Math.PMFIter.iter kernel time initial) f := by
  induction time generalizing f with
  | zero =>
      rw [adaptiveHistoryLaw_succ, expect_bind, adaptiveHistoryLaw_zero,
        expect_pure]
      rw [homogeneousMarkovStep_zero, expect_map, expect_pure]
      rw [Math.PMFIter.iter_zero, expect_pure]
      change f initial = f initial
      rfl
  | succ time ih =>
      rw [adaptiveHistoryLaw_succ, expect_bind]
      simp_rw [expect_map]
      simp only [homogeneousMarkovStep_succ, Fin.snoc_last]
      change
        expect
            (adaptiveHistoryLaw
              (homogeneousMarkovStep initial kernel) (time + 1))
            (fun history => expect (kernel (history (Fin.last time))) f) =
          expect (Math.PMFIter.iter kernel (time + 1) initial) f
      rw [ih (fun state => expect (kernel state) f)]
      rw [Math.PMFIter.iter_succ', expect_bind]

namespace SevenStateVisitEpochCounterexample

/-- Conditional variation when the current state is the renewal owner. -/
def ownerConditionalVariation (time : ℕ) : ℝ :=
  expect (kernel .owner) fun successor =>
    |value successor (time + 1) - value .owner time|

theorem ownerConditionalVariation_eq (time : ℕ) :
    ownerConditionalVariation time =
      if time % 2 = 0 then (14 / 125 : ℝ) else 11 / 125 := by
  rw [ownerConditionalVariation]
  rw [show kernel .owner =
      PMF.ofFintype ownerWeights ownerWeights_sum by rfl]
  rw [expect_ownerWeights]
  rcases Nat.mod_two_eq_zero_or_one time with htime | htime
  · have hfour : time % 4 = 0 ∨ time % 4 = 2 := by omega
    rcases hfour with hfour | hfour
    · have h1 : (time + 1) % 4 = 1 := by omega
      have h3 : (time + 3) % 4 = 3 := by omega
      norm_num [value, renewalTimeValue, cycleTimeValue, htime, hfour, h1, h3]
    · have h1 : (time + 1) % 4 = 3 := by omega
      have h3 : (time + 3) % 4 = 1 := by omega
      norm_num [value, renewalTimeValue, cycleTimeValue, htime, hfour, h1, h3]
  · have hfour : time % 4 = 1 ∨ time % 4 = 3 := by omega
    rcases hfour with hfour | hfour
    · have h1 : (time + 1) % 4 = 2 := by omega
      have h3 : (time + 3) % 4 = 0 := by omega
      norm_num [value, renewalTimeValue, cycleTimeValue, htime, hfour, h1, h3]
    · have h1 : (time + 1) % 4 = 0 := by omega
      have h3 : (time + 3) % 4 = 2 := by omega
      norm_num [value, renewalTimeValue, cycleTimeValue, htime, hfour, h1, h3]

private theorem expect_owner_indicator (law : PMF State) (amount : ℝ) :
    expect law (fun state => if state = .owner then amount else 0) =
      (law .owner).toReal * amount := by
  rw [expect_eq_sum, state_univ]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp

/-- Exact current-marginal expression for the finite owner variation. -/
theorem finiteExpectedStateOwnedMarkovVariation_eq_sum_iter (horizon : ℕ) :
    finiteExpectedStateOwnedMarkovVariation
        .owner kernel value .owner horizon =
      ∑ time ∈ Finset.range horizon,
        (Math.PMFIter.iter kernel time .owner .owner).toReal *
          ownerConditionalVariation time := by
  induction horizon with
  | zero =>
      simp [finiteExpectedStateOwnedMarkovVariation,
        stateOwnedConditionalMarkovVariation]
  | succ horizon ih =>
      rw [finiteExpectedStateOwnedMarkovVariation]
      rw [Finset.sum_range_succ]
      change
        (∑ round ∈ Finset.range (horizon + 1),
            expect
              (adaptiveHistoryLaw (homogeneousMarkovStep .owner kernel) round)
              (stateOwnedConditionalMarkovVariation kernel value .owner round)) +
          expect
            (adaptiveHistoryLaw
              (homogeneousMarkovStep .owner kernel) (horizon + 1))
            (stateOwnedConditionalMarkovVariation
              kernel value .owner (horizon + 1)) = _
      rw [← finiteExpectedStateOwnedMarkovVariation, ih]
      rw [Finset.sum_range_succ]
      congr 1
      have hmarginal := expect_adaptiveHistoryLaw_homogeneous_last
        .owner kernel horizon
        (fun state => if state = .owner then ownerConditionalVariation horizon else 0)
      rw [expect_owner_indicator] at hmarginal
      rw [← hmarginal]
      apply congrArg
      funext history
      simp [stateOwnedConditionalMarkovVariation, ownerConditionalVariation]

/-- The real marginal mass vector of the seven-state chain. -/
def stateMass : ℕ → State → ℝ
  | 0, state => if state = .owner then 1 else 0
  | time + 1, state =>
      match state with
      | .owner =>
          (1 / 5 : ℝ) * stateMass time .owner +
            stateMass time .corridorSecond
      | .corridorFirst => (7 / 10 : ℝ) * stateMass time .owner
      | .corridorSecond => stateMass time .corridorFirst
      | .cycleZero =>
          (1 / 10 : ℝ) * stateMass time .owner +
            stateMass time .cycleThree
      | .cycleOne => stateMass time .cycleZero
      | .cycleTwo => stateMass time .cycleOne
      | .cycleThree => stateMass time .cycleTwo

/-- The explicit real recurrence is the exact iterated-kernel marginal. -/
theorem iter_toReal_eq_stateMass (time : ℕ) (state : State) :
    (Math.PMFIter.iter kernel time .owner state).toReal =
      stateMass time state := by
  induction time generalizing state with
  | zero =>
      cases state <;> simp [Math.PMFIter.iter_zero, stateMass]
  | succ time ih =>
      rw [Math.PMFIter.iter_succ']
      rw [Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum]
      rw [state_univ]
      rw [Finset.sum_insert (by decide)]
      rw [Finset.sum_insert (by decide)]
      rw [Finset.sum_insert (by decide)]
      rw [Finset.sum_insert (by decide)]
      rw [Finset.sum_insert (by decide)]
      rw [Finset.sum_insert (by decide)]
      rw [Finset.sum_singleton]
      simp_rw [ih]
      have hseven : (ENNReal.ofReal (7 / 10 : ℝ)).toReal = 7 / 10 :=
        ENNReal.toReal_ofReal (by norm_num)
      cases state <;>
        simp [kernel, PMF.ofFintype_apply, ownerWeights, stateMass, hseven] <;>
        ring

/-- A compact recurrence certificate carrying the three transient masses and
their accumulated owner variation. -/
structure OwnerAccount where
  ownerMass : ℝ
  firstMass : ℝ
  secondMass : ℝ
  variation : ℝ

def ownerAccountStep (time : ℕ) (account : OwnerAccount) : OwnerAccount where
  ownerMass := (1 / 5 : ℝ) * account.ownerMass + account.secondMass
  firstMass := (7 / 10 : ℝ) * account.ownerMass
  secondMass := account.firstMass
  variation := account.variation + account.ownerMass *
    (if time % 2 = 0 then (14 / 125 : ℝ) else 11 / 125)

def ownerAccount : ℕ → OwnerAccount
  | 0 => ⟨1, 0, 0, 0⟩
  | time + 1 => ownerAccountStep time (ownerAccount time)

def advanceOwnerAccount : ℕ → ℕ → OwnerAccount → OwnerAccount
  | _, 0, account => account
  | start, count + 1, account =>
      ownerAccountStep (start + count)
        (advanceOwnerAccount start count account)

theorem ownerAccount_add (start count : ℕ) :
    ownerAccount (start + count) =
      advanceOwnerAccount start count (ownerAccount start) := by
  induction count with
  | zero => simp [advanceOwnerAccount]
  | succ count ih =>
      rw [Nat.add_succ, ownerAccount, ih]
      rfl

theorem ownerAccount_masses (time : ℕ) :
    (ownerAccount time).ownerMass = stateMass time .owner ∧
      (ownerAccount time).firstMass = stateMass time .corridorFirst ∧
      (ownerAccount time).secondMass = stateMass time .corridorSecond := by
  induction time with
  | zero => simp [ownerAccount, stateMass]
  | succ time ih =>
      rcases ih with ⟨howner, hfirst, hsecond⟩
      simp [ownerAccount, ownerAccountStep, stateMass, howner, hfirst, hsecond]

theorem ownerAccount_variation (horizon : ℕ) :
    (ownerAccount horizon).variation =
      ∑ time ∈ Finset.range horizon,
        stateMass time .owner *
          (if time % 2 = 0 then (14 / 125 : ℝ) else 11 / 125) := by
  induction horizon with
  | zero => simp [ownerAccount]
  | succ horizon ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp [ownerAccount, ownerAccountStep, (ownerAccount_masses horizon).1]

private theorem ownerAccount_20 : ownerAccount 20 =
    ⟨
      13888060201576 / 95367431640625,
      1705701261019973 / 12207031250000000,
      335320033617023 / 2441406250000000,
      88909299474290859 / 152587890625000000
    ⟩ := by
  norm_num [ownerAccount, ownerAccountStep]

private theorem ownerAccount_40 : ownerAccount 40 =
    ⟨
      2832728474065634451040368376421 /
        37252902984619140625000000000000,
      8044079923626924800417483555419 /
        149011611938476562500000000000000,
      848303962359965242656985518597 /
        14901161193847656250000000000000,
      1525323914693305205386060180974077 /
        1862645149230957031250000000000000
    ⟩ := by
  rw [show 40 = 20 + 20 by omega, ownerAccount_add, ownerAccount_20]
  norm_num [advanceOwnerAccount, ownerAccountStep]

private theorem ownerAccount_60 : ownerAccount 60 =
    ⟨
      30040063328058854396777365060231447400285987401 /
        909494701772928237915039062500000000000000000000,
      5491165658540512090663608275173542481734696829 /
        227373675443232059478759765625000000000000000000,
      2284555714656133851204584871490780377101726083 /
        90949470177292823791503906250000000000000000000,
      10502555406956346169123542941069501882570168699303 /
        11368683772161602973937988281250000000000000000000
    ⟩ := by
  rw [show 60 = 40 + 20 by omega, ownerAccount_add, ownerAccount_40]
  norm_num [advanceOwnerAccount, ownerAccountStep]

private theorem ownerAccount_80 : ownerAccount 80 =
    ⟨
      40419504332539317450110979162423040038437380724544703328349707 /
        2775557561562891351059079170227050781250000000000000000000000000,
      117883868785952003475469988725103976890331002571551193890169823 /
        11102230246251565404236316680908203125000000000000000000000000000,
      24568678643101903781992467637516838503127930590318185995233123 /
        2220446049250313080847263336181640625000000000000000000000000000,
      134611931435448093096672902712642863194093357700850477305472210909 /
        138777878078144567552953958511352539062500000000000000000000000000
    ⟩ := by
  rw [show 80 = 60 + 20 by omega, ownerAccount_add, ownerAccount_60]
  norm_num [advanceOwnerAccount, ownerAccountStep]

private theorem ownerAccount_100 : ownerAccount 100 =
    ⟨
      27159176372199873368535985774581074392487035700924050801424984019739597688187 /
        4235164736271501695341612503398209810256958007812500000000000000000000000000000,
      633842565966011710361121763237982905784738030588416424541097614633335804573719 /
        135525271560688054250931600108742713928222656250000000000000000000000000000000000,
      66035749347353677757081457120140504022517779002980905665981731243005057930247 /
        13552527156068805425093160010874271392822265625000000000000000000000000000000000,
      1677657567388643624008793098240426477258725244576403494559666447715061703309065477 /
        1694065894508600678136645001359283924102783203125000000000000000000000000000000000
    ⟩ := by
  rw [show 100 = 80 + 20 by omega, ownerAccount_add, ownerAccount_80]
  norm_num [advanceOwnerAccount, ownerAccountStep]

private theorem ownerAccount_123_variation_gt_one :
    1 < (ownerAccount 123).variation := by
  rw [show 123 = 100 + 23 by omega, ownerAccount_add, ownerAccount_100]
  norm_num [advanceOwnerAccount, ownerAccountStep]

/-- By transition 123 the finite owner variation has already crossed one. -/
theorem one_lt_finiteExpectedStateOwnedMarkovVariation_123 :
    1 < finiteExpectedStateOwnedMarkovVariation
      .owner kernel value .owner 123 := by
  rw [finiteExpectedStateOwnedMarkovVariation_eq_sum_iter]
  simp_rw [iter_toReal_eq_stateMass, ownerConditionalVariation_eq]
  rw [← ownerAccount_variation]
  exact ownerAccount_123_variation_gt_one

/-- The proposed aggregate visit-epoch principle is false for a finite
homogeneous seven-state chain. -/
theorem not_homogeneousBackwardHarmonicVisitEpochPrinciple :
    ¬ HomogeneousBackwardHarmonicVisitEpochPrinciple State := by
  intro principle
  have visitEpoch := principle .owner kernel value
    value_isUnitIntervalBackwardMarkovHarmonic
  let ownedVariation := finiteExpectedStateOwnedMarkovVariation
    State.owner kernel value State.owner 123
  have hvariation : 1 < ownedVariation :=
    one_lt_finiteExpectedStateOwnedMarkovVariation_123
  let slack := (ownedVariation - 1) / 2
  have hslack : 0 < slack := by
    dsimp only [slack]
    linarith
  obtain ⟨visitHorizon, hvisit⟩ :=
    visitEpoch State.owner 123 slack hslack
  have hcharge := finiteExpectedMarkovReturnVisitCharge_le_one
    State.owner kernel State.owner visitHorizon
  dsimp only [ownedVariation, slack] at hvariation hvisit ⊢
  linarith

end SevenStateVisitEpochCounterexample

end

end Math.Probability
