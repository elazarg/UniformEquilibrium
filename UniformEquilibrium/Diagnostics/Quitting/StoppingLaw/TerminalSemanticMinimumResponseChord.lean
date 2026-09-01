import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawMinimumFiberAffine
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveDebtSupport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn

/-!
# Minimum-fibre stopping-law response chords

Mixing one player's complete stopping laws gives a literal behavioral profile.
Its terminal law and prescribed payoffs are affine, while every unrestricted
behavioral cap is convex.  If both endpoint total debts equal one global
minimum, the coordinatewise convexity gaps all vanish.  This gives exact debt
affinity and an exact union formula for positive-debt support.

This module is finite-player and source-independent.  It contains no source
ancestry, compactification producer, prefix copying, regeneration, renewal,
Nash, or uniform-equilibrium conclusion.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Mix only `mover`'s complete stopping laws between two actual profiles. -/
def quittingResponseChordProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile)
    (mover : ι) (weight : ℝ) (hweight0 : 0 ≤ weight)
    (hweight1 : weight ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  Function.update source mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover
      (source mover) (target mover) weight hweight0 hweight1)

/-- If the target changes only `mover`, updating the source by the target's
mover strategy recovers the complete target profile. -/
theorem update_endpoint_with_response_observer_eq_response
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (hopponents : ∀ other, other ≠ mover → target other = source other) :
    Function.update source mover (target mover) = target := by
  funext other
  by_cases hother : other = mover
  · subst other
    simp
  · rw [Function.update_of_ne hother]
    exact (hopponents other hother).symm

/-- The complete terminal law of the literal response chord is the affine
mixture of the two endpoint laws, including the `Never` coordinate. -/
theorem quittingTerminalOutcomeMass_responseChord_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile)
    (mover : ι) (weight : ℝ) (hweight0 : 0 ≤ weight)
    (hweight1 : weight ≤ 1)
    (hopponents : ∀ other, other ≠ mover → target other = source other)
    (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass reward
        (quittingResponseChordProfile reward source target mover weight
          hweight0 hweight1) outcome =
      (1 - weight) * quittingTerminalOutcomeMass reward source outcome +
        weight * quittingTerminalOutcomeMass reward target outcome := by
  have haffine := quittingTerminalOutcomeMass_stoppingLawMixture_eq
    reward source mover (source mover) (target mover) weight hweight0 hweight1
      outcome
  rw [Function.update_eq_self,
    update_endpoint_with_response_observer_eq_response reward source target
      mover hopponents] at haffine
  exact haffine

/-- Every semantic-debt coordinate of the literal response chord lies below
the corresponding endpoint chord. -/
theorem quittingTerminalSemanticDebt_responseChord_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (weight : ℝ)
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hopponents : ∀ other, other ≠ mover → target other = source other) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingResponseChordProfile reward source target mover weight
            hweight0 hweight1)) observer ≤
      (1 - weight) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) observer +
        weight * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) observer := by
  have hconvex := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward source mover observer (source mover) (target mover) weight
      hweight0 hweight1
  rw [Function.update_eq_self,
    update_endpoint_with_response_observer_eq_response reward source target
      mover hopponents] at hconvex
  exact hconvex

/-- Abstract joint-law geometry supplied by a cluster of executable response
chords.  Only the coordinatewise cap-convexity bound and exact law affinity
are retained; all debt equalities below follow from global minimality. -/
structure QuittingMinimumResponseChordLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  endpoint : QuittingTerminalSemanticLawPoint ι
  response : QuittingTerminalSemanticLawPoint ι
  chord : QuittingTerminalSemanticLawPoint ι
  theta : ℝ
  theta_pos : 0 < theta
  theta_lt_one : theta < 1
  endpoint_mem : endpoint ∈ quittingTerminalSemanticLawCarrier reward
  response_mem : response ∈ quittingTerminalSemanticLawCarrier reward
  chord_mem : chord ∈ quittingTerminalSemanticLawCarrier reward
  endpoint_minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum endpoint.1 ≤
      quittingTerminalSemanticDebtSum candidate
  response_debtSum_eq_endpoint :
    quittingTerminalSemanticDebtSum response.1 =
      quittingTerminalSemanticDebtSum endpoint.1
  chord_debt_le_affine : ∀ who,
    quittingTerminalSemanticDebt chord.1 who ≤
      (1 - theta) * quittingTerminalSemanticDebt endpoint.1 who +
        theta * quittingTerminalSemanticDebt response.1 who
  chord_law_eq_affine : ∀ outcome,
    chord.2 outcome = (1 - theta) * endpoint.2 outcome +
      theta * response.2 outcome

namespace QuittingMinimumResponseChordLaw

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Two literal same-minimum profiles differing only in one player's complete
strategy produce a minimum response-chord law without compactification. -/
def ofProfiles
    (source target : (quittingGame reward).BehaviorProfile)
    (mover : ι) (weight : ℝ) (hweight0 : 0 < weight)
    (hweight1 : weight < 1)
    (hopponents : ∀ other, other ≠ mover → target other = source other)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward source) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsame : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward target) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward source)) :
    QuittingMinimumResponseChordLaw reward where
  endpoint :=
    (quittingTerminalSemanticPair reward source,
      quittingTerminalOutcomeMass reward source)
  response :=
    (quittingTerminalSemanticPair reward target,
      quittingTerminalOutcomeMass reward target)
  chord :=
    let profile := quittingResponseChordProfile reward source target mover
      weight hweight0.le hweight1.le
    (quittingTerminalSemanticPair reward profile,
      quittingTerminalOutcomeMass reward profile)
  theta := weight
  theta_pos := hweight0
  theta_lt_one := hweight1
  endpoint_mem := quittingTerminalSemanticLawPoint_mem_carrier reward source
  response_mem := quittingTerminalSemanticLawPoint_mem_carrier reward target
  chord_mem := quittingTerminalSemanticLawPoint_mem_carrier reward _
  endpoint_minimum := hminimum
  response_debtSum_eq_endpoint := hsame
  chord_debt_le_affine := by
    intro who
    exact quittingTerminalSemanticDebt_responseChord_le reward source target
      mover who weight hweight0.le hweight1.le hopponents
  chord_law_eq_affine := by
    intro outcome
    exact quittingTerminalOutcomeMass_responseChord_eq reward source target
      mover weight hweight0.le hweight1.le hopponents outcome

/-- The literal constructor's chord coordinate is definitionally the exact
stopping-law mixture profile. -/
theorem ofProfiles_chord_eq
    (source target : (quittingGame reward).BehaviorProfile)
    (mover : ι) (weight : ℝ) (hweight0 : 0 < weight)
    (hweight1 : weight < 1)
    (hopponents : ∀ other, other ≠ mover → target other = source other)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward source) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsame : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward target) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward source)) :
    (ofProfiles source target mover weight hweight0 hweight1 hopponents
      hminimum hsame).chord =
      let profile := quittingResponseChordProfile reward source target mover
        weight hweight0.le hweight1.le
      (quittingTerminalSemanticPair reward profile,
        quittingTerminalOutcomeMass reward profile) := rfl

/-- The interior chord remains on the same global minimum total-debt fibre. -/
theorem chord_debtSum_eq_endpoint
    (law : QuittingMinimumResponseChordLaw reward) :
    quittingTerminalSemanticDebtSum law.chord.1 =
      quittingTerminalSemanticDebtSum law.endpoint.1 := by
  have hchordCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier law.chord law.chord_mem
  have hlower := law.endpoint_minimum law.chord.1 hchordCarrier
  have hupper : quittingTerminalSemanticDebtSum law.chord.1 ≤
      (1 - law.theta) *
          quittingTerminalSemanticDebtSum law.endpoint.1 +
        law.theta * quittingTerminalSemanticDebtSum law.response.1 := by
    unfold quittingTerminalSemanticDebtSum
    calc
      ∑ who, quittingTerminalSemanticDebt law.chord.1 who ≤
          ∑ who, ((1 - law.theta) *
              quittingTerminalSemanticDebt law.endpoint.1 who +
            law.theta * quittingTerminalSemanticDebt law.response.1 who) :=
        Finset.sum_le_sum fun who _ ↦ law.chord_debt_le_affine who
      _ = (1 - law.theta) *
            ∑ who, quittingTerminalSemanticDebt law.endpoint.1 who +
          law.theta *
            ∑ who, quittingTerminalSemanticDebt law.response.1 who := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [law.response_debtSum_eq_endpoint] at hupper
  nlinarith

/-- Every coordinate debt is exactly affine on a proper minimum chord. -/
theorem chord_debt_eq_affine
    (law : QuittingMinimumResponseChordLaw reward) (who : ι) :
    quittingTerminalSemanticDebt law.chord.1 who =
      (1 - law.theta) * quittingTerminalSemanticDebt law.endpoint.1 who +
        law.theta * quittingTerminalSemanticDebt law.response.1 who := by
  let gap : ι → ℝ := fun player ↦
    (1 - law.theta) * quittingTerminalSemanticDebt law.endpoint.1 player +
      law.theta * quittingTerminalSemanticDebt law.response.1 player -
        quittingTerminalSemanticDebt law.chord.1 player
  have hgapNonneg : ∀ player, 0 ≤ gap player := fun player ↦
    sub_nonneg.mpr (law.chord_debt_le_affine player)
  have hgapSum : (∑ player, gap player) = 0 := by
    dsimp only [gap]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    change (1 - law.theta) *
          quittingTerminalSemanticDebtSum law.endpoint.1 +
        law.theta * quittingTerminalSemanticDebtSum law.response.1 -
          quittingTerminalSemanticDebtSum law.chord.1 = 0
    rw [law.response_debtSum_eq_endpoint, law.chord_debtSum_eq_endpoint]
    ring
  have hrest : 0 ≤ ∑ player ∈ Finset.univ.erase who, gap player :=
    Finset.sum_nonneg fun player _ ↦ hgapNonneg player
  have hsplit := Finset.sum_erase_add Finset.univ gap (Finset.mem_univ who)
  rw [hgapSum] at hsplit
  have hzero : gap who = 0 := by linarith [hgapNonneg who, hrest]
  dsimp only [gap] at hzero
  linarith

/-- Positive debt support of the interior chord is exactly the union of the
endpoint supports. -/
theorem chord_support_eq_union
    (law : QuittingMinimumResponseChordLaw reward) :
    quittingPositiveDebtSupport law.chord.1 =
      quittingPositiveDebtSupport law.endpoint.1 ∪
        quittingPositiveDebtSupport law.response.1 := by
  ext who
  simp only [quittingPositiveDebtSupport, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union]
  rw [law.chord_debt_eq_affine who]
  have hendpointCarrier := terminalSemanticLawCarrier_fst_mem_carrier
    law.endpoint law.endpoint_mem
  have hresponseCarrier := terminalSemanticLawCarrier_fst_mem_carrier
    law.response law.response_mem
  have hendpointNonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
    reward hendpointCarrier who
  have hresponseNonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
    reward hresponseCarrier who
  have honeMinusPos : 0 < 1 - law.theta := sub_pos.mpr law.theta_lt_one
  constructor
  · intro hpositive
    by_contra hnone
    push Not at hnone
    rcases hnone with ⟨hendpointNot, hresponseNot⟩
    nlinarith
  · rintro (hendpointPositive | hresponsePositive)
    · exact add_pos_of_pos_of_nonneg
        (mul_pos honeMinusPos hendpointPositive)
        (mul_nonneg law.theta_pos.le hresponseNonneg)
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg honeMinusPos.le hendpointNonneg)
        (mul_pos law.theta_pos hresponsePositive)

/-- On a literal same-minimum response chord, every coordinate debt is
exactly affine between the source and target profiles. -/
theorem quittingTerminalSemanticDebt_responseChord_eq_of_minimum_sameDebtSum
    (source target : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (weight : ℝ) (hweight0 : 0 < weight)
    (hweight1 : weight < 1)
    (hopponents : ∀ other, other ≠ mover → target other = source other)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward source) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsame : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward target) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward source)) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingResponseChordProfile reward source target mover weight
            hweight0.le hweight1.le)) observer =
      (1 - weight) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) observer +
        weight * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) observer := by
  let law := ofProfiles source target mover weight hweight0 hweight1
    hopponents hminimum hsame
  exact law.chord_debt_eq_affine observer

/-- The same literal chord has total debt exactly equal to the source global
minimum. -/
theorem quittingTerminalSemanticDebtSum_responseChord_eq_of_minimum_sameDebtSum
    (source target : (quittingGame reward).BehaviorProfile)
    (mover : ι) (weight : ℝ) (hweight0 : 0 < weight)
    (hweight1 : weight < 1)
    (hopponents : ∀ other, other ≠ mover → target other = source other)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward source) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsame : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward target) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward source)) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingResponseChordProfile reward source target mover weight
            hweight0.le hweight1.le)) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward source) := by
  let law := ofProfiles source target mover weight hweight0 hweight1
    hopponents hminimum hsame
  exact law.chord_debtSum_eq_endpoint

/-- Positive-debt support of the literal interior chord is exactly the union
of source and target supports. -/
theorem quittingPositiveDebtSupport_responseChord_eq_union_of_minimum_sameDebtSum
    (source target : (quittingGame reward).BehaviorProfile)
    (mover : ι) (weight : ℝ) (hweight0 : 0 < weight)
    (hweight1 : weight < 1)
    (hopponents : ∀ other, other ≠ mover → target other = source other)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward source) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsame : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward target) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward source)) :
    quittingPositiveDebtSupport
        (quittingTerminalSemanticPair reward
          (quittingResponseChordProfile reward source target mover weight
            hweight0.le hweight1.le)) =
      quittingPositiveDebtSupport (quittingTerminalSemanticPair reward source) ∪
        quittingPositiveDebtSupport
          (quittingTerminalSemanticPair reward target) := by
  let law := ofProfiles source target mover weight hweight0 hweight1
    hopponents hminimum hsame
  exact law.chord_support_eq_union

/-- Every response-law atom retains at least its response weight in the
interior chord. -/
theorem theta_mul_le_chord_terminalMass
    (law : QuittingMinimumResponseChordLaw reward)
    (terminal : {S : Finset ι // S.Nonempty}) (mass : ℝ)
    (hmass : mass ≤ law.response.2 (some terminal)) :
    law.theta * mass ≤ law.chord.2 (some terminal) := by
  rw [law.chord_law_eq_affine]
  have hendpointSimplex := terminalSemanticLawCarrier_mass_mem_stdSimplex
    law.endpoint law.endpoint_mem
  have hendpointNonneg := hendpointSimplex.1 (some terminal)
  have hweightNonneg : 0 ≤ 1 - law.theta :=
    sub_nonneg.mpr law.theta_lt_one.le
  nlinarith [mul_nonneg hweightNonneg hendpointNonneg,
    mul_le_mul_of_nonneg_left hmass law.theta_pos.le]

/-- If the response kills a coordinate positive at the source endpoint, its
support is a strict subset of the interior/source-union support. -/
theorem response_support_ssubset_chord_of_killed
    (law : QuittingMinimumResponseChordLaw reward) (who : ι)
    (hendpoint : 0 < quittingTerminalSemanticDebt law.endpoint.1 who)
    (hresponse : quittingTerminalSemanticDebt law.response.1 who = 0) :
    quittingPositiveDebtSupport law.response.1 ⊂
      quittingPositiveDebtSupport law.chord.1 := by
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · rw [law.chord_support_eq_union]
    exact Finset.subset_union_right
  · intro heq
    have hchordMem : who ∈ quittingPositiveDebtSupport law.chord.1 := by
      rw [law.chord_support_eq_union]
      exact Finset.mem_union_left _
        ((mem_quittingPositiveDebtSupport_iff law.endpoint.1 who).2 hendpoint)
    have hresponseMem : who ∈ quittingPositiveDebtSupport law.response.1 := by
      rw [heq]
      exact hchordMem
    have hpositive :=
      (mem_quittingPositiveDebtSupport_iff law.response.1 who).1 hresponseMem
    rw [hresponse] at hpositive
    exact (lt_irrefl 0) hpositive

/-- Positive minimum total debt makes the response support nonempty. -/
theorem response_support_nonempty_of_endpointDebtSum_pos
    (law : QuittingMinimumResponseChordLaw reward)
    (hpositive : 0 < quittingTerminalSemanticDebtSum law.endpoint.1) :
    (quittingPositiveDebtSupport law.response.1).Nonempty := by
  by_contra hempty
  have hresponseCarrier := terminalSemanticLawCarrier_fst_mem_carrier
    law.response law.response_mem
  have hzero : ∀ who,
      quittingTerminalSemanticDebt law.response.1 who = 0 := by
    intro who
    have hnotPositive :
        ¬0 < quittingTerminalSemanticDebt law.response.1 who := by
      intro hwho
      exact hempty ⟨who,
        (mem_quittingPositiveDebtSupport_iff law.response.1 who).2 hwho⟩
    exact le_antisymm (le_of_not_gt hnotPositive)
      (quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hresponseCarrier who)
  have hresponsePositive :
      0 < quittingTerminalSemanticDebtSum law.response.1 := by
    rw [law.response_debtSum_eq_endpoint]
    exact hpositive
  unfold quittingTerminalSemanticDebtSum at hresponsePositive
  simp only [hzero, Finset.sum_const_zero] at hresponsePositive
  exact (lt_irrefl 0) hresponsePositive

/-- In four players, killing one source-positive coordinate bounds response
support cardinality by three. -/
theorem response_support_card_le_three_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (law : QuittingMinimumResponseChordLaw reward) (who : Fin 4)
    (hendpoint : 0 < quittingTerminalSemanticDebt law.endpoint.1 who)
    (hresponse : quittingTerminalSemanticDebt law.response.1 who = 0) :
    (quittingPositiveDebtSupport law.response.1).card ≤ 3 := by
  have hstrict := law.response_support_ssubset_chord_of_killed who
    hendpoint hresponse
  have hcardStrict := Finset.card_lt_card hstrict
  have hchordCard : (quittingPositiveDebtSupport law.chord.1).card ≤ 4 := by
    have hsubset : quittingPositiveDebtSupport law.chord.1 ⊆
        (Finset.univ : Finset (Fin 4)) := Finset.subset_univ _
    have hcard := Finset.card_le_card hsubset
    simpa using hcard
  omega

/-- A positive four-player minimum and one killed source coordinate leave a
nonempty response support of cardinality at most three. -/
theorem response_support_nonempty_and_card_le_three_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (law : QuittingMinimumResponseChordLaw reward) (who : Fin 4)
    (hpositive : 0 < quittingTerminalSemanticDebtSum law.endpoint.1)
    (hendpoint : 0 < quittingTerminalSemanticDebt law.endpoint.1 who)
    (hresponse : quittingTerminalSemanticDebt law.response.1 who = 0) :
    (quittingPositiveDebtSupport law.response.1).Nonempty ∧
      (quittingPositiveDebtSupport law.response.1).card ≤ 3 :=
  ⟨law.response_support_nonempty_of_endpointDebtSum_pos hpositive,
    law.response_support_card_le_three_finFour who hendpoint hresponse⟩

end QuittingMinimumResponseChordLaw

end GameTheory
