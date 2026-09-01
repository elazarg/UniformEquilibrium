/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.ZeroSingletonBehavioralLawProductBase

/-!
# A sharp four-atom reward-law boundary

This concrete four-player table witnesses both sharpness of the four-atom
conic support bound and failure of behavioral realization.  The latter is an
exact obstruction; it makes no claim about approximate realization with
small singleton or Never leakage.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

/-- The four pair coalitions in the sharp support regression. -/
def finFourSharpPair (label : Fin 4) : Finset (Fin 4) :=
  match label with
  | 0 => {0, 1}
  | 1 => {0, 2}
  | 2 => {0, 3}
  | 3 => {1, 2}

theorem finFourSharpPair_nonempty (label : Fin 4) :
    (finFourSharpPair label).Nonempty := by
  fin_cases label <;> simp [finFourSharpPair]

theorem finFourSharpPair_injective : Function.Injective finFourSharpPair := by
  intro first second heq
  fin_cases first <;> fin_cases second <;>
    simp +decide at heq ⊢

theorem finFourSharpPair_card (label : Fin 4) :
    (finFourSharpPair label).card = 2 := by
  fin_cases label <;> simp [finFourSharpPair]

theorem singleton_ne_finFourSharpPair (player label : Fin 4) :
    ({player} : Finset (Fin 4)) ≠ finFourSharpPair label := by
  intro heq
  have hcard := congrArg Finset.card heq
  simp [finFourSharpPair_card] at hcard

theorem finFourSharpPair_ne_singleton (label player : Fin 4) :
    finFourSharpPair label ≠ ({player} : Finset (Fin 4)) :=
  fun heq => singleton_ne_finFourSharpPair player label heq.symm

/-- The sharp reward table: displayed pair `k` pays `4` to coordinate `k`
and `-1` elsewhere; an own singleton pays zero and all other entries pay
`-1`. -/
def finFourSharpSparseReward
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) : Payoff (Fin 4) :=
  fun player =>
    if terminal.val = finFourSharpPair player then 4
    else if terminal.val = {player} then 0
    else -1

/-- The law assigning mass `1/4` to each displayed pair and zero elsewhere. -/
def finFourSharpPairLaw : QuittingTerminalOutcome (Fin 4) → ℝ
  | outcome =>
      ∑ label : Fin 4,
        if outcome = some ⟨finFourSharpPair label,
          finFourSharpPair_nonempty label⟩ then 1 / 4 else 0

@[simp] theorem finFourSharpPairLaw_none : finFourSharpPairLaw none = 0 := by
  simp [finFourSharpPairLaw]

@[simp] theorem finFourSharpPairLaw_pair (label : Fin 4) :
    finFourSharpPairLaw (some ⟨finFourSharpPair label,
      finFourSharpPair_nonempty label⟩) = 1 / 4 := by
  simp [finFourSharpPairLaw, Subtype.ext_iff,
    finFourSharpPair_injective.eq_iff]

@[simp] theorem finFourSharpPairLaw_singleton (player : Fin 4) :
    finFourSharpPairLaw (some (quittingSingletonTerminal player)) = 0 := by
  fin_cases player <;>
    simp [finFourSharpPairLaw, Subtype.ext_iff,
      quittingSingletonTerminal, singleton_ne_finFourSharpPair]

theorem finFourSharpPairLaw_nonnegative
    (outcome : QuittingTerminalOutcome (Fin 4)) :
    0 ≤ finFourSharpPairLaw outcome := by
  unfold finFourSharpPairLaw
  exact Finset.sum_nonneg fun _ _ => by split <;> norm_num

theorem finFourSharpPairLaw_sum_eq_one :
    ∑ outcome, finFourSharpPairLaw outcome = 1 := by
  unfold finFourSharpPairLaw
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_ite_eq']
  norm_num [Fin.sum_univ_four]

theorem finFourSharpSparseReward_pair (label player : Fin 4) :
    finFourSharpSparseReward
      ⟨finFourSharpPair label, finFourSharpPair_nonempty label⟩ player =
        if player = label then 4 else -1 := by
  simp [finFourSharpSparseReward, finFourSharpPair_injective.eq_iff,
    finFourSharpPair_ne_singleton, eq_comm]

/-- Every displayed pair pays total social reward one. -/
theorem finFourSharpSparseReward_pair_sum (label : Fin 4) :
    ∑ player : Fin 4,
        finFourSharpSparseReward
          ⟨finFourSharpPair label, finFourSharpPair_nonempty label⟩ player = 1 := by
  simp_rw [finFourSharpSparseReward_pair]
  fin_cases label <;> norm_num [Fin.sum_univ_four] <;>
    simp +decide <;> norm_num

/-- The uniform displayed-pair law has reward moment `1/4` in every
coordinate. -/
theorem finFourSharpPairLaw_rewardMoment (player : Fin 4) :
    quittingTerminalRewardMoment finFourSharpSparseReward
      finFourSharpPairLaw player = 1 / 4 := by
  unfold quittingTerminalRewardMoment finFourSharpPairLaw
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [ite_mul, zero_mul, Fintype.sum_ite_eq']
  simp only [quittingTerminalOutcomeReward]
  simp_rw [finFourSharpSparseReward_pair]
  fin_cases player <;> norm_num [Fin.sum_univ_four] <;>
    simp +decide <;> norm_num

/-- Number of displayed pair labels represented by an outcome.  Injectivity
makes this either zero or one. -/
def finFourSharpDisplayedIndicator
    (outcome : QuittingTerminalOutcome (Fin 4)) : ℝ :=
  ∑ label : Fin 4,
    if outcome = some ⟨finFourSharpPair label,
        finFourSharpPair_nonempty label⟩ then 1 else 0

private theorem finFourSharpDisplayedIndicator_pair (label : Fin 4) :
    finFourSharpDisplayedIndicator
      (some ⟨finFourSharpPair label, finFourSharpPair_nonempty label⟩) = 1 := by
  simp [finFourSharpDisplayedIndicator, Subtype.ext_iff,
    finFourSharpPair_injective.eq_iff]

private theorem finFourSharpDisplayedIndicator_eq_zero
    (outcome : QuittingTerminalOutcome (Fin 4))
    (hnot : ∀ label : Fin 4,
      outcome ≠ some ⟨finFourSharpPair label,
        finFourSharpPair_nonempty label⟩) :
    finFourSharpDisplayedIndicator outcome = 0 := by
  unfold finFourSharpDisplayedIndicator
  apply Finset.sum_eq_zero
  intro label _
  rw [if_neg (hnot label)]

private theorem sum_mass_mul_finFourSharpDisplayedIndicator
    (mass : QuittingTerminalOutcome (Fin 4) → ℝ) :
    (∑ outcome, mass outcome * finFourSharpDisplayedIndicator outcome) =
      ∑ label : Fin 4,
        mass (some ⟨finFourSharpPair label,
          finFourSharpPair_nonempty label⟩) := by
  unfold finFourSharpDisplayedIndicator
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq']

private theorem finFourSharp_totalReward_le_indicator
    (outcome : QuittingTerminalOutcome (Fin 4)) :
    (∑ player : Fin 4,
      quittingTerminalOutcomeReward finFourSharpSparseReward outcome player) ≤
        finFourSharpDisplayedIndicator outcome := by
  cases outcome with
  | none =>
      simp [quittingTerminalOutcomeReward,
        finFourSharpDisplayedIndicator_eq_zero]
  | some terminal =>
      by_cases hdisplayed : ∃ label : Fin 4,
        terminal.val = finFourSharpPair label
      · obtain ⟨label, hlabel⟩ := hdisplayed
        have hterminal : terminal =
            ⟨finFourSharpPair label, finFourSharpPair_nonempty label⟩ :=
          Subtype.ext hlabel
        subst terminal
        rw [finFourSharpDisplayedIndicator_pair]
        simpa only [quittingTerminalOutcomeReward] using
          (finFourSharpSparseReward_pair_sum label).le
      · have hindicator : finFourSharpDisplayedIndicator (some terminal) = 0 := by
          apply finFourSharpDisplayedIndicator_eq_zero
          intro label heq
          exact hdisplayed ⟨label, congrArg Subtype.val (Option.some.inj heq)⟩
        rw [hindicator]
        apply Finset.sum_nonpos
        intro player _
        simp only [quittingTerminalOutcomeReward]
        unfold finFourSharpSparseReward
        rw [if_neg (fun heq => hdisplayed ⟨player, heq⟩)]
        split <;> norm_num

private theorem finFourSharp_coordinate_le_indicator
    (outcome : QuittingTerminalOutcome (Fin 4)) (label : Fin 4) :
    quittingTerminalOutcomeReward finFourSharpSparseReward outcome label ≤
      -finFourSharpDisplayedIndicator outcome +
        5 * (if outcome = some ⟨finFourSharpPair label,
          finFourSharpPair_nonempty label⟩ then 1 else 0) := by
  by_cases hselected : outcome = some ⟨finFourSharpPair label,
      finFourSharpPair_nonempty label⟩
  · subst outcome
    rw [finFourSharpDisplayedIndicator_pair]
    simp only [quittingTerminalOutcomeReward, finFourSharpSparseReward_pair,
      if_pos]
    norm_num
  · by_cases hdisplayed : ∃ other : Fin 4,
      outcome = some ⟨finFourSharpPair other,
        finFourSharpPair_nonempty other⟩
    · obtain ⟨other, hother⟩ := hdisplayed
      have hne : label ≠ other := by
        intro heq
        subst other
        exact hselected hother
      subst outcome
      rw [finFourSharpDisplayedIndicator_pair]
      simp [quittingTerminalOutcomeReward, finFourSharpSparseReward_pair,
        finFourSharpPair_injective.eq_iff, hne, Ne.symm hne]
    · have hindicator := finFourSharpDisplayedIndicator_eq_zero outcome
          (fun other heq => hdisplayed ⟨other, heq⟩)
      rw [hindicator, if_neg hselected]
      simp only [neg_zero, zero_add, mul_zero]
      cases outcome with
      | none => simp [quittingTerminalOutcomeReward]
      | some terminal =>
          simp only [quittingTerminalOutcomeReward]
          unfold finFourSharpSparseReward
          rw [if_neg (fun heq => hdisplayed ⟨label,
            congrArg some (Subtype.ext heq)⟩)]
          split <;> norm_num

/-- Every nonnegative law whose reward moment weakly dominates zero and is
strict in one coordinate assigns positive mass to all four displayed pairs. -/
theorem finFourSharpPairLaw_positive_on_every_pair
    (mass : QuittingTerminalOutcome (Fin 4) → ℝ)
    (hmass : ∀ outcome, 0 ≤ mass outcome)
    (hnonnegative : ∀ player,
      0 ≤ quittingTerminalRewardMoment finFourSharpSparseReward mass player)
    (hstrict : ∃ player,
      0 < quittingTerminalRewardMoment finFourSharpSparseReward mass player) :
    ∀ label : Fin 4,
      0 < mass (some ⟨finFourSharpPair label,
        finFourSharpPair_nonempty label⟩) := by
  let displayedMass := ∑ label : Fin 4,
    mass (some ⟨finFourSharpPair label, finFourSharpPair_nonempty label⟩)
  have htotalPositive : 0 < ∑ player : Fin 4,
      quittingTerminalRewardMoment finFourSharpSparseReward mass player := by
    obtain ⟨player, hplayer⟩ := hstrict
    exact Finset.sum_pos' (fun other _ => hnonnegative other)
      ⟨player, Finset.mem_univ player, hplayer⟩
  have htotalLe : (∑ player : Fin 4,
      quittingTerminalRewardMoment finFourSharpSparseReward mass player) ≤
        displayedMass := by
    unfold quittingTerminalRewardMoment
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      (∑ outcome, mass outcome *
          ∑ player, quittingTerminalOutcomeReward
            finFourSharpSparseReward outcome player) ≤
          ∑ outcome, mass outcome * finFourSharpDisplayedIndicator outcome := by
        apply Finset.sum_le_sum
        intro outcome _
        exact mul_le_mul_of_nonneg_left
          (finFourSharp_totalReward_le_indicator outcome) (hmass outcome)
      _ = displayedMass := by
        exact sum_mass_mul_finFourSharpDisplayedIndicator mass
  have hdisplayedPositive : 0 < displayedMass := htotalPositive.trans_le htotalLe
  intro label
  have hcoordinateLe :
      quittingTerminalRewardMoment finFourSharpSparseReward mass label ≤
        -displayedMass +
          5 * mass (some ⟨finFourSharpPair label,
            finFourSharpPair_nonempty label⟩) := by
    unfold quittingTerminalRewardMoment
    calc
      (∑ outcome, mass outcome *
          quittingTerminalOutcomeReward
            finFourSharpSparseReward outcome label) ≤
          ∑ outcome, mass outcome *
            (-finFourSharpDisplayedIndicator outcome +
              5 * (if outcome = some ⟨finFourSharpPair label,
                finFourSharpPair_nonempty label⟩ then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro outcome _
        exact mul_le_mul_of_nonneg_left
          (finFourSharp_coordinate_le_indicator outcome label) (hmass outcome)
      _ = -displayedMass +
          5 * mass (some ⟨finFourSharpPair label,
            finFourSharpPair_nonempty label⟩) := by
        simp_rw [mul_add, mul_neg, Finset.sum_add_distrib,
          Finset.sum_neg_distrib]
        rw [sum_mass_mul_finFourSharpDisplayedIndicator]
        simp_rw [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq']
        ring
  have hmassNonnegative := hmass
    (some ⟨finFourSharpPair label, finFourSharpPair_nonempty label⟩)
  have hcoordinateNonnegative := hnonnegative label
  nlinarith

/-- Consequently every coordinatewise-improving law has support cardinality
at least four. -/
theorem finFourSharpPairLaw_support_card_ge_four
    (mass : QuittingTerminalOutcome (Fin 4) → ℝ)
    (hmass : ∀ outcome, 0 ≤ mass outcome)
    (hnonnegative : ∀ player,
      0 ≤ quittingTerminalRewardMoment finFourSharpSparseReward mass player)
    (hstrict : ∃ player,
      0 < quittingTerminalRewardMoment finFourSharpSparseReward mass player) :
    4 ≤ (Finset.univ.filter fun outcome => mass outcome ≠ 0).card := by
  let pairs : Finset (QuittingTerminalOutcome (Fin 4)) :=
    Finset.univ.image fun label : Fin 4 =>
      some ⟨finFourSharpPair label, finFourSharpPair_nonempty label⟩
  have hpairsCard : pairs.card = 4 := by
    rw [Finset.card_image_iff.mpr]
    · norm_num [pairs]
    · intro first _ second _ heq
      exact finFourSharpPair_injective
        (congrArg Subtype.val (Option.some.inj heq))
  have hsubset : pairs ⊆ Finset.univ.filter fun outcome => mass outcome ≠ 0 := by
    intro outcome houtcome
    rw [Finset.mem_image] at houtcome
    obtain ⟨label, -, rfl⟩ := houtcome
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ne_of_gt (finFourSharpPairLaw_positive_on_every_pair mass hmass
      hnonnegative hstrict label)
  calc
    4 = pairs.card := hpairsCard.symm
    _ ≤ (Finset.univ.filter fun outcome => mass outcome ≠ 0).card :=
      Finset.card_le_card hsubset

/-- The displayed law itself has exactly four positive atoms.  This is the
literal sharpness equality behind the general lower bound above. -/
theorem finFourSharpPairLaw_support_card_eq_four :
    (Finset.univ.filter fun outcome =>
      finFourSharpPairLaw outcome ≠ 0).card = 4 := by
  let pairs : Finset (QuittingTerminalOutcome (Fin 4)) :=
    Finset.univ.image fun label : Fin 4 =>
      some ⟨finFourSharpPair label, finFourSharpPair_nonempty label⟩
  have hpairsCard : pairs.card = 4 := by
    rw [Finset.card_image_iff.mpr]
    · norm_num [pairs]
    · intro first _ second _ heq
      exact finFourSharpPair_injective
        (congrArg Subtype.val (Option.some.inj heq))
  have hsupportSubset :
      Finset.univ.filter (fun outcome => finFourSharpPairLaw outcome ≠ 0) ⊆
        pairs := by
    intro outcome houtcome
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at houtcome
    by_contra hnot
    have hnotPair : ∀ label : Fin 4,
        outcome ≠ some ⟨finFourSharpPair label,
          finFourSharpPair_nonempty label⟩ := by
      intro label heq
      exact hnot (Finset.mem_image.2 ⟨label, Finset.mem_univ label, heq.symm⟩)
    have hzero : finFourSharpPairLaw outcome = 0 := by
      unfold finFourSharpPairLaw
      apply Finset.sum_eq_zero
      intro label _
      rw [if_neg (hnotPair label)]
    exact houtcome hzero
  have hupper :
      (Finset.univ.filter fun outcome =>
        finFourSharpPairLaw outcome ≠ 0).card ≤ 4 := by
    calc
      (Finset.univ.filter fun outcome =>
          finFourSharpPairLaw outcome ≠ 0).card ≤ pairs.card :=
        Finset.card_le_card hsupportSubset
      _ = 4 := hpairsCard
  have hlower : 4 ≤
      (Finset.univ.filter fun outcome =>
        finFourSharpPairLaw outcome ≠ 0).card := by
    apply finFourSharpPairLaw_support_card_ge_four finFourSharpPairLaw
      finFourSharpPairLaw_nonnegative
    · intro player
      rw [finFourSharpPairLaw_rewardMoment]
      norm_num
    · exact ⟨0, by rw [finFourSharpPairLaw_rewardMoment]; norm_num⟩
  omega

/-- The four displayed pairs have no common player. -/
theorem not_mem_all_finFourSharpPairs (player : Fin 4) :
    ¬ ∀ label : Fin 4, player ∈ finFourSharpPair label := by
  fin_cases player
  · intro h
    simpa [finFourSharpPair] using h 3
  · intro h
    simpa [finFourSharpPair] using h 1
  · intro h
    simpa [finFourSharpPair] using h 0
  · intro h
    simpa [finFourSharpPair] using h 0

/-- The uniform four-pair law is not the complete terminal law of any
ordinary behavioral profile. -/
theorem no_behaviorProfile_realizes_finFourSharpPairLaw :
    ¬ ∃ profile : (quittingGame finFourSharpSparseReward).BehaviorProfile,
      ∀ outcome, quittingTerminalOutcomeMass finFourSharpSparseReward
        profile outcome = finFourSharpPairLaw outcome := by
  rintro ⟨profile, hlaw⟩
  let point : QuittingTerminalSemanticLawPoint (Fin 4) :=
    (quittingTerminalSemanticPair finFourSharpSparseReward profile,
      quittingTerminalOutcomeMass finFourSharpSparseReward profile)
  have hpoint : point ∈
      quittingTerminalSemanticLawCarrier finFourSharpSparseReward :=
    quittingTerminalSemanticLawPoint_mem_carrier finFourSharpSparseReward profile
  have hnever : point.2 none = 0 := by
    change quittingTerminalOutcomeMass finFourSharpSparseReward profile none = 0
    rw [hlaw]
    exact finFourSharpPairLaw_none
  have hsingleton : ∀ player,
      point.2 (some (quittingSingletonTerminal player)) = 0 := by
    intro player
    change quittingTerminalOutcomeMass finFourSharpSparseReward profile
      (some (quittingSingletonTerminal player)) = 0
    rw [hlaw]
    exact finFourSharpPairLaw_singleton player
  obtain ⟨root, first, second, hne, hfirst, hsecond, hrootLaw, hsupport⟩ :=
    exists_twoSureProductRoot_realizing_law_of_mem_terminalSemanticLawCarrier
      finFourSharpSparseReward point hpoint hnever hsingleton (by norm_num)
  have hfirstAll : ∀ label : Fin 4, first ∈ finFourSharpPair label := by
    intro label
    exact (hsupport ⟨finFourSharpPair label, finFourSharpPair_nonempty label⟩
      (by simp [point, hlaw])).1
  exact not_mem_all_finFourSharpPairs first hfirstAll

/-- In particular, no arbitrary one-date product root followed by Never has
the displayed terminal law. -/
theorem no_oneDateProductProfile_realizes_finFourSharpPairLaw :
    ¬ ∃ root : Fin 4 → PMF Bool,
      ∀ outcome, quittingTerminalOutcomeMass finFourSharpSparseReward
        (quittingOneDateThenNeverProfile finFourSharpSparseReward root) outcome =
          finFourSharpPairLaw outcome := by
  rintro ⟨root, hlaw⟩
  exact no_behaviorProfile_realizes_finFourSharpPairLaw
    ⟨quittingOneDateThenNeverProfile finFourSharpSparseReward root, hlaw⟩

end GameTheory
