/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CirculantConstantStepCycle
import Research.Quitting.CirculantPocketAnchoredNoGo
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Assembling the branches of the five-player circulant trichotomy

For a five-player table whose singleton and two-element rows are rotation
symmetric, with nonnegative solo self value and nonpositive join margins, three
producers divide every sign pattern between them.

* Nonpositive margin sum makes the normalized solo matrix fail standard `Q`,
  and the counterexample gate is collapsed by
  `Research/Quitting/CirculantTrichotomy.lean`.
* No negative margin at all leaves one player quitting alone self-enforcing:
  it is a sure exit set in the sense of
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`, because no other player
  prefers joining the exit to watching it.
* Positive margin sum with a negative margin calls on a *firing step* — a step
  `c` whose own margin is negative and whose complementary margin `m (4 * c)`
  is nonnegative, and which in addition has either a nonnegative doubled
  complementary margin `m (3 * c)` or a nonpositive doubled margin `m (2 * c)`.
  A firing step puts an anchor root strictly inside the unit interval, at which
  the four floor inequalities of the constant-step producer of
  `Research/Quitting/CirculantConstantStepCycle.lean` reduce to nonpositivity
  of the join margins along the same progression.

Two of the four floors are free at any anchor root of a step of negative
margin: the phase-one floor reads a join margin against zero, and the anchor
equation itself makes the backward partial sum positive.  The remaining two are
the content of the firing sign condition.  The floor at the deepest elapsed
phase needs `0 ≤ m (4 * c)`.  The floor one phase earlier is funded in two
independent ways — directly by `0 ≤ m (3 * c)`, or through the positive
backward partial sum by `m (2 * c) ≤ 0` — and admitting both is what carries
the branch past the sign condition that only the first disjunct supports.

The third producer is delimited exactly.  Among margin vectors of positive sum
with at least one negative margin, a firing step is missing precisely when the
negative margins are one complementary pair of distances, and
`IsComplementaryPocketMargin` names that pattern.  There are two such patterns,
the neighbour distances and the distant ones; the open pocket of
`Research/Quitting/CirculantPocketAnchoredNoGo.lean` is an instance of the
first.  So the complementary pockets of positive margin sum are the whole
residual, which is what `isEmpty_counterexampleRegime_or_isComplementaryPocketMargin`
records.

Neither pocket is closed by sign data alone, but both are closed by sign data
together with two inequalities on the join margins.  The producer behind that
is `exists_uniformEquilibriumPayoff_of_complementaryStep`: a step whose own
margin is negative and whose complementary margin is nonpositive runs the
constant-step cycle once the join margins along its progression are
nonpositive at the two shallowest phases and capped by the complementary
margin at the two deepest.  Each pocket admits two such steps — the pocket
distance and its complement — hence two independent cap pairs, and
`isEmpty_counterexampleRegime_or_uncappedComplementaryPocket` records the
census that survives all four.  Both pockets of the collider completion are
settled outright in `Research/Quitting/CirculantColliderClosure.lean`.

## Main definitions

* `IsFiringStep` — the sign condition on a step under which the constant-step
  producer needs nothing beyond nonpositive join margins
* `IsComplementaryPocketMargin` — the sign pattern whose negative margins are
  exactly one complementary pair
* `ConstantStepCyclicResolution` — the proposition that a firing step resolves
  a table of positive margin sum with no hypothesis on rows of two or more
  players

## Main results

* `hasCirculantSoloMatrix_of_isCirculantPairTable` — rotation-symmetric
  singleton rows give a circulant normalized solo matrix
* `exists_uniformEquilibriumPayoff_of_isFiringStep` and
  `isEmpty_counterexampleRegime_of_isFiringStep` — the firing-step branch
* `isQuittingSureExitSet_singleton_of_isCirculantPairTable` and
  `isEmpty_counterexampleRegime_of_nonneg_margins` — the solo exit branch
* `isFiringStep_complement_of_unique_nonneg` — with a single nonnegative
  distance `g`, the complementary distance `4 * g` is a firing step
* `exists_uniformEquilibriumPayoff_of_unique_nonneg` and
  `isEmpty_counterexampleRegime_of_unique_nonneg` — three negative margins are
  resolved with no further hypothesis
* `exists_isFiringStep` — every other sign pattern of positive margin sum with
  a negative margin carries a firing step
* `not_isFiringStep_of_isComplementaryPocketMargin` — and the complementary
  pairs carry none
* `neighbour_or_distant_of_isComplementaryPocketMargin` — there are two
  complementary pockets
* `exists_uniformEquilibriumPayoff_of_complementaryStep` — the producer both
  complementary pockets run on
* `exists_uniformEquilibriumPayoff_of_neighbourPocket` and
  `exists_uniformEquilibriumPayoff_of_neighbourPocket_stepOne` — the neighbour
  pocket of any completion capped at `m 1`, respectively at `m 4`
* `exists_uniformEquilibriumPayoff_of_distantPocket` and
  `exists_uniformEquilibriumPayoff_of_distantPocket_stepThree` — the distant
  pocket of any completion capped at `m 3`, respectively at `m 2`
* `isEmpty_counterexampleRegime_of_neighbourPocket` and
  `isEmpty_counterexampleRegime_of_distantPocket` — either pocket at either cap
* `not_exists_nonneg_complement_pair_of_unique_nonneg` — at three negative
  margins the first disjunct of the firing condition is unavailable
* `isEmpty_counterexampleRegime_of_not_isComplementaryPocketMargin` and
  `isEmpty_counterexampleRegime_or_isComplementaryPocketMargin` — the branches
  together, and the census they leave
* `isEmpty_counterexampleRegime_or_uncappedComplementaryPocket` — the same
  census with the four cap pairs removed from the residual
-/

noncomputable section

namespace GameTheory
namespace CirculantTrichotomyClosure

open QuittingLCPClassification CirculantConstantStepCycle

/-! ## Arithmetic of the five-cycle -/

theorem mul_ne_zero_five : ∀ k c : ZMod 5, k ≠ 0 → c ≠ 0 → k * c ≠ 0 := by decide

theorem exists_mul_eq_neg_one : ∀ c : ZMod 5, c ≠ 0 → ∃ c' : ZMod 5, c * c' = -1 := by
  decide

/-- Every nonzero element of the five-cycle is one of the four multiples of
every other nonzero element. -/
theorem eq_mul_of_ne_zero :
    ∀ c d : ZMod 5, c ≠ 0 → d ≠ 0 → c = d ∨ c = 2 * d ∨ c = 3 * d ∨ c = 4 * d := by
  decide

/-! ## The two sign conditions -/

/-- **A firing step.**  The step is nonzero, its own margin is negative, its
complementary margin is nonnegative, and either its doubled complementary
margin is nonnegative or its doubled margin is nonpositive. -/
def IsFiringStep (margin : ZMod 5 → ℝ) (c : ZMod 5) : Prop :=
  c ≠ 0 ∧ margin c < 0 ∧ 0 ≤ margin (4 * c) ∧
    (0 ≤ margin (3 * c) ∨ margin (2 * c) ≤ 0)

/-- **A complementary pocket.**  Some distance and its complement both carry
negative margins while the other two distances carry nonnegative ones, so the
negative margins are exactly one complementary pair. -/
def IsComplementaryPocketMargin (margin : ZMod 5 → ℝ) : Prop :=
  ∃ d : ZMod 5, d ≠ 0 ∧ margin d < 0 ∧ margin (4 * d) < 0 ∧
    0 ≤ margin (2 * d) ∧ 0 ≤ margin (3 * d)

/-! ## Rotation-symmetric singleton rows -/

variable {reward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5)}
  {s : ℝ} {m J : ZMod 5 → ℝ}

/-- Rotation-symmetric singleton rows around a common solo self value give a
circulant normalized solo matrix with the same margin vector: the common value
cancels against each receiver's own solo payoff. -/
theorem hasCirculantSoloMatrix_of_isCirculantPairTable
    (htable : IsCirculantPairTable reward s m J) :
    HasCirculantSoloMatrix reward m := by
  funext who owner
  show (normalizedQuittingPayoffTable reward).singletonMatrix who owner =
    m (owner - who)
  rw [normalized_singletonMatrix_eq_quittingSingletonMatrix, quittingSingletonMatrix,
    show (⟨{owner}, Finset.singleton_nonempty owner⟩ :
        {S : Finset (ZMod 5) // S.Nonempty}) = quittingSingletonTerminal owner from rfl,
    show (⟨{who}, Finset.singleton_nonempty who⟩ :
        {S : Finset (ZMod 5) // S.Nonempty}) = quittingSingletonTerminal who from rfl,
    htable.singleton, htable.singleton, sub_self, htable.margin_zero]
  ring

/-! ## The firing-step branch -/

/-- The backward partial sum of the constant-step anchor, written the way the
constant-step producer's second floor reads it. -/
theorem constantStepAnchorTail_eq (m : ZMod 5 → ℝ) (c : ZMod 5) (q : ℝ) :
    constantStepAnchorTail m c q =
      m (2 * c) + q * m (3 * c) + q ^ 2 * m (4 * c) := by
  rw [constantStepAnchorTail, Math.cubicAnchorTail]
  norm_num [nsmul_eq_mul]
  ring

/-- **The firing-step branch.**  A rotation-symmetric table of positive margin
sum whose join margins along the progression of a firing step are nonpositive
has an ordinary uniform-equilibrium payoff.

The anchor root supplies the first floor and, through positivity of the
backward partial sum at that root, the second.  The nonnegative complementary
margin supplies the fourth.  The third is supplied by the nonnegative doubled
complementary margin when that is what the firing condition offers, and
otherwise by the nonpositive doubled margin against the same positive backward
partial sum. -/
theorem exists_uniformEquilibriumPayoff_of_isFiringStep
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hsum : 0 < ∑ e, m e) {c : ZMod 5} (hfire : IsFiringStep m c)
    (hjoin : ∀ k : ZMod 5, k ≠ 0 → J (k * c) ≤ 0) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨hc, hneg, hcomplement, hthird⟩ := hfire
  obtain ⟨q, hq, hroot, htail⟩ :=
    exists_constantStepAnchor_root_zmod_five m htable.margin_zero hc hneg hsum
  obtain ⟨c', hcc'⟩ := exists_mul_eq_neg_one c hc
  have hrootStep : stepAnchor m c q = 0 :=
    (stepAnchor_eq_constantStepAnchor m c q).trans hroot
  rw [constantStepAnchorTail_eq] at htail
  have hfloor₁ : J c ≤ 0 := by
    have := hjoin 1 (by decide)
    rwa [one_mul] at this
  have hfloor₂ : J (2 * c) ≤ m (2 * c) + q * m (3 * c) + q ^ 2 * m (4 * c) := by
    linarith [hjoin 2 (by decide)]
  have hfloor₃ : J (3 * c) ≤ m (3 * c) + q * m (4 * c) := by
    have hstep : 0 ≤ m (3 * c) + q * m (4 * c) := by
      rcases hthird with hdoubled | hdouble
      · exact add_nonneg hdoubled (mul_nonneg hq.1.le hcomplement)
      · rcases le_or_gt (m (3 * c) + q * m (4 * c)) 0 with hle | hlt
        · nlinarith [hq.1]
        · exact hlt.le
    linarith [hjoin 3 (by decide)]
  have hfloor₄ : J (4 * c) ≤ m (4 * c) := by
    linarith [hjoin 4 (by decide)]
  exact ⟨_, isUniformEquilibriumPayoff_constantStep htable hcc' hs hq.1 hq.2
    hrootStep hfloor₁ hfloor₂ hfloor₃ hfloor₄⟩

/-- The firing-step branch, as emptiness of the counterexample regime. -/
theorem isEmpty_counterexampleRegime_of_isFiringStep
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hsum : 0 < ∑ e, m e) {c : ZMod 5} (hfire : IsFiringStep m c)
    (hjoin : ∀ k : ZMod 5, k ≠ 0 → J (k * c) ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  ⟨fun regime => regime.not_exists_uniformEquilibriumPayoff
    (exists_uniformEquilibriumPayoff_of_isFiringStep htable hs hsum hfire hjoin)⟩

/-! ## The solo exit branch -/

/-- **The solo exit of a rotation-symmetric table.**  When the solo self value
is nonnegative and every join margin is at most the singleton margin at the
same distance, one player quitting alone at every live history is a sure exit
set in the sense of `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`: the
quitter does not prefer nonabsorption to its own solo self value, and no other
player prefers joining the exit to watching it. -/
theorem isQuittingSureExitSet_singleton_of_isCirculantPairTable
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hle : ∀ d : ZMod 5, d ≠ 0 → J d ≤ m d) (owner : ZMod 5) :
    IsQuittingSureExitSet reward {owner} := by
  refine (isQuittingSureExitSet_singleton_iff reward owner).mpr ⟨?_, ?_⟩
  · have hsolo : quittingSoloReward reward owner owner = s + m (owner - owner) :=
      htable.singleton owner owner
    rw [hsolo, sub_self, htable.margin_zero, add_zero]
    exact hs
  · intro other hother
    have hcollision : quittingSingletonCollisionReward reward owner other =
        s + J (owner - other) := htable.pair owner other (Ne.symm hother)
    have hsolo : quittingSoloReward reward owner other = s + m (owner - other) :=
      htable.singleton owner other
    rw [hcollision, hsolo]
    linarith [hle _ (sub_ne_zero_of_ne (Ne.symm hother))]

/-- **The solo exit branch.**  A rotation-symmetric table with nonnegative solo
self value whose join margins never exceed the singleton margins at the same
distance has an ordinary uniform-equilibrium payoff, namely the row of a solo
exit.  Neither the margin sum nor any anchor root enters. -/
theorem exists_uniformEquilibriumPayoff_of_join_le_margin
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hle : ∀ d : ZMod 5, d ≠ 0 → J d ≤ m d) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  ⟨_, isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward
    (isQuittingSureExitSet_singleton_of_isCirculantPairTable htable hs hle 0)⟩

/-- **No negative margin.**  A rotation-symmetric table of nonpositive join
margins whose singleton margins are all nonnegative has an ordinary
uniform-equilibrium payoff: every player weakly prefers watching a solo exit to
joining it, so the solo exit is self-enforcing. -/
theorem exists_uniformEquilibriumPayoff_of_nonneg_margins
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0)
    (hm : ∀ d : ZMod 5, d ≠ 0 → 0 ≤ m d) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_join_le_margin htable hs
    fun d hd => (hjoin d hd).trans (hm d hd)

/-- The solo exit branch, as emptiness of the counterexample regime. -/
theorem isEmpty_counterexampleRegime_of_nonneg_margins
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0)
    (hm : ∀ d : ZMod 5, d ≠ 0 → 0 ≤ m d) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  ⟨fun regime => regime.not_exists_uniformEquilibriumPayoff
    (exists_uniformEquilibriumPayoff_of_nonneg_margins htable hs hjoin hm)⟩

/-! ## Three negative margins -/

/-- **The step of a three-negative margin vector.**  If `g` is the only nonzero
distance whose margin is nonnegative, the complementary distance `4 * g` is a
firing step: its own margin and its doubled margin are two of the three
negative margins, because in the five-cycle neither `4 * g` nor `3 * g` is `g`,
and its complementary margin is `m g`. -/
theorem isFiringStep_complement_of_unique_nonneg {g : ZMod 5} (hg : g ≠ 0)
    (hgm : 0 ≤ m g) (hother : ∀ e : ZMod 5, e ≠ 0 → e ≠ g → m e < 0) :
    IsFiringStep m (4 * g) := by
  have h2g : (2 : ZMod 5) * g ≠ 0 := mul_ne_zero_five 2 g (by decide) hg
  have h3g : (3 : ZMod 5) * g ≠ 0 := mul_ne_zero_five 3 g (by decide) hg
  have h4g : (4 : ZMod 5) * g ≠ 0 := mul_ne_zero_five 4 g (by decide) hg
  have hdouble : (2 : ZMod 5) * (4 * g) = 3 * g := by
    rw [← mul_assoc, show (2 : ZMod 5) * 4 = 3 from by decide]
  have hcomp : (4 : ZMod 5) * (4 * g) = g := by
    rw [← mul_assoc, show (4 : ZMod 5) * 4 = 1 from by decide, one_mul]
  refine ⟨h4g, hother _ h4g fun h => h3g (by linear_combination h), ?_, Or.inr ?_⟩
  · rw [hcomp]
    exact hgm
  · rw [hdouble]
    exact (hother _ h3g fun h => h2g (by linear_combination h)).le

/-- A single nonnegative distance of a margin vector of positive sum is
nonzero: were it the zero distance, all four nonzero margins would be negative
and the sum could not be positive. -/
theorem ne_zero_of_unique_nonneg (hm0 : m 0 = 0) (hsum : 0 < ∑ e, m e) {g : ZMod 5}
    (hother : ∀ e : ZMod 5, e ≠ 0 → e ≠ g → m e < 0) : g ≠ 0 := by
  rintro rfl
  have hfive : (∑ e : ZMod 5, m e) = m 0 + m 1 + m 2 + m 3 + m 4 :=
    Fin.sum_univ_five (fun e : ZMod 5 => m e)
  rw [hfive, hm0] at hsum
  linarith [hother 1 (by decide) (by decide), hother 2 (by decide) (by decide),
    hother 3 (by decide) (by decide), hother 4 (by decide) (by decide)]

/-- **Three negative margins.**  A rotation-symmetric table of positive margin
sum with exactly one nonnegative nonzero distance `g`, nonnegative solo self
value and nonpositive join margins has an ordinary uniform-equilibrium payoff.
The witness is the constant-step cyclic profile of step `4 * g`. -/
theorem exists_uniformEquilibriumPayoff_of_unique_nonneg
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hsum : 0 < ∑ e, m e) {g : ZMod 5} (hgm : 0 ≤ m g)
    (hother : ∀ e : ZMod 5, e ≠ 0 → e ≠ g → m e < 0)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hg : g ≠ 0 := ne_zero_of_unique_nonneg htable.margin_zero hsum hother
  exact exists_uniformEquilibriumPayoff_of_isFiringStep htable hs hsum
    (isFiringStep_complement_of_unique_nonneg hg hgm hother)
    fun k hk => hjoin _ (mul_ne_zero_five k (4 * g) hk
      (mul_ne_zero_five 4 g (by decide) hg))

/-- Three negative margins, as emptiness of the counterexample regime. -/
theorem isEmpty_counterexampleRegime_of_unique_nonneg
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hsum : 0 < ∑ e, m e) {g : ZMod 5} (hgm : 0 ≤ m g)
    (hother : ∀ e : ZMod 5, e ≠ 0 → e ≠ g → m e < 0)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  ⟨fun regime => regime.not_exists_uniformEquilibriumPayoff
    (exists_uniformEquilibriumPayoff_of_unique_nonneg htable hs hsum hgm hother
      hjoin)⟩

/-! ## Which sign patterns carry a firing step -/

/-- The firing condition at step one, read on the numerals of the five-cycle. -/
theorem isFiringStep_one (h1 : m 1 < 0) (h4 : 0 ≤ m 4)
    (hthird : 0 ≤ m 3 ∨ m 2 ≤ 0) : IsFiringStep m 1 := by
  refine ⟨by decide, h1, ?_, ?_⟩
  · rwa [show (4 : ZMod 5) * 1 = 4 from by decide]
  · rwa [show (3 : ZMod 5) * 1 = 3 from by decide,
      show (2 : ZMod 5) * 1 = 2 from by decide]

/-- The firing condition at step two, read on the numerals of the
five-cycle. -/
theorem isFiringStep_two (h2 : m 2 < 0) (h3 : 0 ≤ m 3)
    (hthird : 0 ≤ m 1 ∨ m 4 ≤ 0) : IsFiringStep m 2 := by
  refine ⟨by decide, h2, ?_, ?_⟩
  · rwa [show (4 : ZMod 5) * 2 = 3 from by decide]
  · rwa [show (3 : ZMod 5) * 2 = 1 from by decide,
      show (2 : ZMod 5) * 2 = 4 from by decide]

/-- The firing condition at step three, read on the numerals of the
five-cycle. -/
theorem isFiringStep_three (h3 : m 3 < 0) (h2 : 0 ≤ m 2)
    (hthird : 0 ≤ m 4 ∨ m 1 ≤ 0) : IsFiringStep m 3 := by
  refine ⟨by decide, h3, ?_, ?_⟩
  · rwa [show (4 : ZMod 5) * 3 = 2 from by decide]
  · rwa [show (3 : ZMod 5) * 3 = 4 from by decide,
      show (2 : ZMod 5) * 3 = 1 from by decide]

/-- The firing condition at step four, read on the numerals of the
five-cycle. -/
theorem isFiringStep_four (h4 : m 4 < 0) (h1 : 0 ≤ m 1)
    (hthird : 0 ≤ m 2 ∨ m 3 ≤ 0) : IsFiringStep m 4 := by
  refine ⟨by decide, h4, ?_, ?_⟩
  · rwa [show (4 : ZMod 5) * 4 = 1 from by decide]
  · rwa [show (3 : ZMod 5) * 4 = 2 from by decide,
      show (2 : ZMod 5) * 4 = 3 from by decide]

/-- The complementary pocket on the neighbour distances. -/
theorem isComplementaryPocketMargin_one (h1 : m 1 < 0) (h4 : m 4 < 0)
    (h2 : 0 ≤ m 2) (h3 : 0 ≤ m 3) : IsComplementaryPocketMargin m := by
  refine ⟨1, by decide, h1, ?_, ?_, ?_⟩
  · rwa [show (4 : ZMod 5) * 1 = 4 from by decide]
  · rwa [show (2 : ZMod 5) * 1 = 2 from by decide]
  · rwa [show (3 : ZMod 5) * 1 = 3 from by decide]

/-- The complementary pocket on the distant distances. -/
theorem isComplementaryPocketMargin_two (h2 : m 2 < 0) (h3 : m 3 < 0)
    (h4 : 0 ≤ m 4) (h1 : 0 ≤ m 1) : IsComplementaryPocketMargin m := by
  refine ⟨2, by decide, h2, ?_, ?_, ?_⟩
  · rwa [show (4 : ZMod 5) * 2 = 3 from by decide]
  · rwa [show (2 : ZMod 5) * 2 = 4 from by decide]
  · rwa [show (3 : ZMod 5) * 2 = 1 from by decide]

/-- **There are two complementary pockets.**  The negative margins of a
complementary pocket are either the two neighbour distances or the two distant
ones. -/
theorem neighbour_or_distant_of_isComplementaryPocketMargin
    (hpocket : IsComplementaryPocketMargin m) :
    (m 1 < 0 ∧ m 4 < 0 ∧ 0 ≤ m 2 ∧ 0 ≤ m 3) ∨
      (m 2 < 0 ∧ m 3 < 0 ∧ 0 ≤ m 4 ∧ 0 ≤ m 1) := by
  obtain ⟨d, hd, hown, hcomplement, hdouble, hdoubled⟩ := hpocket
  rcases zmod_five_cases d with h | h | h | h | h <;> subst h
  · exact absurd rfl hd
  · rw [show (4 : ZMod 5) * 1 = 4 from by decide] at hcomplement
    rw [show (2 : ZMod 5) * 1 = 2 from by decide] at hdouble
    rw [show (3 : ZMod 5) * 1 = 3 from by decide] at hdoubled
    exact Or.inl ⟨hown, hcomplement, hdouble, hdoubled⟩
  · rw [show (4 : ZMod 5) * 2 = 3 from by decide] at hcomplement
    rw [show (2 : ZMod 5) * 2 = 4 from by decide] at hdouble
    rw [show (3 : ZMod 5) * 2 = 1 from by decide] at hdoubled
    exact Or.inr ⟨hown, hcomplement, hdouble, hdoubled⟩
  · rw [show (4 : ZMod 5) * 3 = 2 from by decide] at hcomplement
    rw [show (2 : ZMod 5) * 3 = 1 from by decide] at hdouble
    rw [show (3 : ZMod 5) * 3 = 4 from by decide] at hdoubled
    exact Or.inr ⟨hcomplement, hown, hdoubled, hdouble⟩
  · rw [show (4 : ZMod 5) * 4 = 1 from by decide] at hcomplement
    rw [show (2 : ZMod 5) * 4 = 3 from by decide] at hdouble
    rw [show (3 : ZMod 5) * 4 = 2 from by decide] at hdoubled
    exact Or.inl ⟨hcomplement, hown, hdoubled, hdouble⟩

/-- The open pocket of `Research/Quitting/CirculantPocketAnchoredNoGo.lean` is
a complementary pocket. -/
theorem isComplementaryPocketMargin_of_isOpenPocketMargin
    (hpocket : IsOpenPocketMargin m) : IsComplementaryPocketMargin m :=
  isComplementaryPocketMargin_one hpocket.1 hpocket.2.1 hpocket.2.2.1.le
    hpocket.2.2.2.le

/-- **Every other sign pattern fires.**  A margin vector of positive sum with
at least one negative margin whose negative margins are not exactly one
complementary pair has a firing step.

Four negative margins are ruled out by the positive sum.  A single negative
margin fires at itself, since its complementary and doubled complementary
distances are both distinct from it.  Two negative margins at distances `c` and
`2 * c` fire at `c`, and three negative margins fire at the complement of the
single nonnegative distance. -/
theorem exists_isFiringStep (hm0 : m 0 = 0) (hsum : 0 < ∑ e, m e)
    (hneg : ∃ a : ZMod 5, a ≠ 0 ∧ m a < 0)
    (hpocket : ¬ IsComplementaryPocketMargin m) :
    ∃ c : ZMod 5, IsFiringStep m c := by
  have hfive : (∑ e : ZMod 5, m e) = m 0 + m 1 + m 2 + m 3 + m 4 :=
    Fin.sum_univ_five (fun e : ZMod 5 => m e)
  rw [hfive, hm0] at hsum
  have hsome : m 1 < 0 ∨ m 2 < 0 ∨ m 3 < 0 ∨ m 4 < 0 := by
    obtain ⟨a, ha, hma⟩ := hneg
    rcases zmod_five_cases a with h | h | h | h | h <;> subst h
    · exact absurd rfl ha
    · exact Or.inl hma
    · exact Or.inr (Or.inl hma)
    · exact Or.inr (Or.inr (Or.inl hma))
    · exact Or.inr (Or.inr (Or.inr hma))
  rcases lt_or_ge (m 1) 0 with h1 | h1 <;> rcases lt_or_ge (m 2) 0 with h2 | h2 <;>
      rcases lt_or_ge (m 3) 0 with h3 | h3 <;> rcases lt_or_ge (m 4) 0 with h4 | h4
  · linarith
  · exact ⟨1, isFiringStep_one h1 h4 (Or.inr h2.le)⟩
  · exact ⟨2, isFiringStep_two h2 h3 (Or.inr h4.le)⟩
  · exact ⟨1, isFiringStep_one h1 h4 (Or.inl h3)⟩
  · exact ⟨3, isFiringStep_three h3 h2 (Or.inr h1.le)⟩
  · exact ⟨3, isFiringStep_three h3 h2 (Or.inl h4)⟩
  · exact absurd (isComplementaryPocketMargin_one h1 h4 h2 h3) hpocket
  · exact ⟨1, isFiringStep_one h1 h4 (Or.inl h3)⟩
  · exact ⟨4, isFiringStep_four h4 h1 (Or.inr h3.le)⟩
  · exact absurd (isComplementaryPocketMargin_two h2 h3 h4 h1) hpocket
  · exact ⟨2, isFiringStep_two h2 h3 (Or.inl h1)⟩
  · exact ⟨2, isFiringStep_two h2 h3 (Or.inl h1)⟩
  · exact ⟨4, isFiringStep_four h4 h1 (Or.inl h2)⟩
  · exact ⟨3, isFiringStep_three h3 h2 (Or.inl h4)⟩
  · exact ⟨4, isFiringStep_four h4 h1 (Or.inl h2)⟩
  · rcases hsome with h | h | h | h <;> linarith

/-- **A complementary pocket carries no firing step.**  A step of negative
margin in such a pattern is the pocket distance or its complement, and in both
cases its complementary margin is the other negative one. -/
theorem not_isFiringStep_of_isComplementaryPocketMargin
    (hpocket : IsComplementaryPocketMargin m) : ¬ ∃ c : ZMod 5, IsFiringStep m c := by
  rintro ⟨c, hc, hneg, hcomplement, -⟩
  obtain ⟨d, hd, hd1, hd4, hd2, hd3⟩ := hpocket
  rcases eq_mul_of_ne_zero c d hc hd with h | h | h | h <;> subst h
  · linarith
  · linarith
  · linarith
  · rw [← mul_assoc, show (4 : ZMod 5) * 4 = 1 from by decide, one_mul] at hcomplement
    linarith

/-- **At most one nonnegative margin leaves the first disjunct unavailable.**
If every nonzero distance other than `g` carries a negative margin, no step has
both a nonnegative complementary and a nonnegative doubled complementary
margin: those two distances would both have to be `g`, forcing the step to
vanish.  Every firing step of such a vector therefore rests on the nonpositive
doubled margin, which is what
`isFiringStep_complement_of_unique_nonneg` supplies. -/
theorem not_exists_nonneg_complement_pair_of_unique_nonneg {g : ZMod 5}
    (hnegative : ∀ e : ZMod 5, e ≠ 0 → e ≠ g → m e < 0) :
    ¬ ∃ c : ZMod 5, c ≠ 0 ∧ m c < 0 ∧ 0 ≤ m (4 * c) ∧ 0 ≤ m (3 * c) := by
  rintro ⟨c, hc, -, hcomplement, hdoubled⟩
  have hfour : 4 * c = g := by
    by_contra hne
    exact absurd hcomplement
      (not_le.mpr (hnegative _ (mul_ne_zero_five 4 c (by decide) hc) hne))
  have hthree : 3 * c = g := by
    by_contra hne
    exact absurd hdoubled
      (not_le.mpr (hnegative _ (mul_ne_zero_five 3 c (by decide) hc) hne))
  exact hc (by linear_combination hfour - hthree)

/-! ## The complementary-step producer -/

/-- **The complementary-step producer.**  A step whose own margin is negative
and whose complementary margin is nonpositive carries a constant-step cyclic
equilibrium as soon as the join margins along its progression obey four
inequalities: nonpositive at the step itself and at its double, and capped by
the complementary margin at the two deepest elapsed phases.

This is the producer the two complementary pockets need, where no step fires
in the sense of `IsFiringStep` — a firing step wants `0 ≤ m (4 * c)`, and here
that margin is the second negative one of the pocket.  What replaces it is the
pair of caps, which the pocket cannot supply from sign data alone.

The floor at the shallowest elapsed phase reads `J c` against zero and the
next is funded by the positive backward partial sum at the anchor root.  The
floor at the deepest phase is the cap `J (4 * c) ≤ m (4 * c)` verbatim, and
the one before it reads `m (3 * c) + q * m (4 * c)`, which is at least
`m (4 * c)` because `m (3 * c)` is nonnegative, `m (4 * c)` nonpositive and
`q` below one.  So the same cap value serves at both depths. -/
theorem exists_uniformEquilibriumPayoff_of_complementaryStep
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hsum : 0 < ∑ e, m e) {c : ZMod 5} (hc : c ≠ 0) (hneg : m c < 0)
    (hthird : 0 ≤ m (3 * c)) (hcomplement : m (4 * c) ≤ 0)
    (hown : J c ≤ 0) (hdouble : J (2 * c) ≤ 0)
    (hcap₃ : J (3 * c) ≤ m (4 * c)) (hcap₄ : J (4 * c) ≤ m (4 * c)) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨q, hq, hroot, htail⟩ :=
    exists_constantStepAnchor_root_zmod_five m htable.margin_zero hc hneg hsum
  obtain ⟨c', hcc'⟩ := exists_mul_eq_neg_one c hc
  rw [constantStepAnchorTail_eq] at htail
  have hrootStep : stepAnchor m c q = 0 :=
    (stepAnchor_eq_constantStepAnchor m c q).trans hroot
  have h1q : (0 : ℝ) ≤ 1 - q := by linarith [hq.2]
  refine ⟨_, isUniformEquilibriumPayoff_constantStep htable hcc' hs hq.1 hq.2
    hrootStep hown ?_ ?_ hcap₄⟩
  · linarith
  · nlinarith

/-! ## The neighbour pocket -/

/-- **A wedge containing the neighbour pocket, for any completion.**  The
hypotheses `m 1 ≤ 0`, `m 4 < 0`, `0 ≤ m 2` at positive margin sum do not
constrain `m 3`, so they admit more than the pocket proper: with `m 3`
negative a firing step may exist as well.  In the pocket proper, where `m 3`
is also nonnegative, no step fires, and the step-four cycle of this theorem is
one of the two producers known there; it runs on the two caps `J 1 ≤ m 1` and
`J 2 ≤ m 1`, and on nonpositivity of the join margins at distances three and
four only.

It is the case `c = 4` of `exists_uniformEquilibriumPayoff_of_complementaryStep`,
whose complementary margin is `m 1`. -/
theorem exists_uniformEquilibriumPayoff_of_neighbourPocket
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hm1 : m 1 ≤ 0) (hm4 : m 4 < 0) (hm2 : 0 ≤ m 2)
    (hsum : 0 < ∑ e, m e) (hthree : J 3 ≤ 0) (hfour : J 4 ≤ 0)
    (hone : J 1 ≤ m 1) (htwo : J 2 ≤ m 1) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have h24 : (2 : ZMod 5) * 4 = 3 := by decide
  have h34 : (3 : ZMod 5) * 4 = 2 := by decide
  have h44 : (4 : ZMod 5) * 4 = 1 := by decide
  exact exists_uniformEquilibriumPayoff_of_complementaryStep htable hs hsum
    (by decide) hm4 (by rw [h34]; exact hm2) (by rw [h44]; exact hm1) hfour
    (by rw [h24]; exact hthree) (by rw [h34, h44]; exact htwo)
    (by rw [h44]; exact hone)

/-- **The neighbour pocket, capped at `m 4`.**  The step-one cycle closes the
same wedge from the other side: its complementary margin is `m 4`, so the two
caps sit at `m 4` and the free floors ask nonpositivity at distances one and
two.  It is the case `c = 1` of the complementary-step producer. -/
theorem exists_uniformEquilibriumPayoff_of_neighbourPocket_stepOne
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hm1 : m 1 < 0) (hm4 : m 4 ≤ 0) (hm3 : 0 ≤ m 3)
    (hsum : 0 < ∑ e, m e) (hone : J 1 ≤ 0) (htwo : J 2 ≤ 0)
    (hthree : J 3 ≤ m 4) (hfour : J 4 ≤ m 4) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have h21 : (2 : ZMod 5) * 1 = 2 := by decide
  have h31 : (3 : ZMod 5) * 1 = 3 := by decide
  have h41 : (4 : ZMod 5) * 1 = 4 := by decide
  exact exists_uniformEquilibriumPayoff_of_complementaryStep htable hs hsum
    (by decide) hm1 (by rw [h31]; exact hm3) (by rw [h41]; exact hm4)
    hone (by rw [h21]; exact htwo) (by rw [h31, h41]; exact hthree)
    (by rw [h41]; exact hfour)

/-- **The neighbour pocket at either cap.**  In the pocket proper both cycles
are available in principle, and the pocket closes as soon as one of the two
cap pairs holds. -/
theorem isEmpty_counterexampleRegime_of_neighbourPocket
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0)
    (hm1 : m 1 < 0) (hm4 : m 4 < 0) (hm2 : 0 ≤ m 2) (hm3 : 0 ≤ m 3)
    (hsum : 0 < ∑ e, m e)
    (hcap : (J 1 ≤ m 1 ∧ J 2 ≤ m 1) ∨ (J 3 ≤ m 4 ∧ J 4 ≤ m 4)) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  refine ⟨fun regime => regime.not_exists_uniformEquilibriumPayoff ?_⟩
  rcases hcap with ⟨hone, htwo⟩ | ⟨hthree, hfour⟩
  · exact exists_uniformEquilibriumPayoff_of_neighbourPocket htable hs hm1.le hm4
      hm2 hsum (hjoin 3 (by decide)) (hjoin 4 (by decide)) hone htwo
  · exact exists_uniformEquilibriumPayoff_of_neighbourPocket_stepOne htable hs hm1
      hm4.le hm3 hsum (hjoin 1 (by decide)) (hjoin 2 (by decide)) hthree hfour

/-! ## The distant pocket -/

/-- **A wedge containing the distant pocket, for any completion.**  This is
the mirror of `exists_uniformEquilibriumPayoff_of_neighbourPocket` across the
automorphism doubling the five-cycle: the negative pair is now `m 2`, `m 3`,
the cycle is the step-two one, and the complementary margin at which the two
caps sit is `m 3`.

Before this the distant pocket was closed only for the collider completion of
`Research/Quitting/CirculantColliderClosure.lean`, which supplies the caps
from `low - s ≤ m 3`; the statement here asks only for the caps themselves. -/
theorem exists_uniformEquilibriumPayoff_of_distantPocket
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hm2 : m 2 < 0) (hm3 : m 3 ≤ 0) (hm1 : 0 ≤ m 1)
    (hsum : 0 < ∑ e, m e) (htwo : J 2 ≤ 0) (hfour : J 4 ≤ 0)
    (hone : J 1 ≤ m 3) (hthree : J 3 ≤ m 3) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have h22 : (2 : ZMod 5) * 2 = 4 := by decide
  have h32 : (3 : ZMod 5) * 2 = 1 := by decide
  have h42 : (4 : ZMod 5) * 2 = 3 := by decide
  exact exists_uniformEquilibriumPayoff_of_complementaryStep htable hs hsum
    (by decide) hm2 (by rw [h32]; exact hm1) (by rw [h42]; exact hm3) htwo
    (by rw [h22]; exact hfour) (by rw [h32, h42]; exact hone)
    (by rw [h42]; exact hthree)

/-- **The distant pocket, capped at `m 2`.**  The step-three cycle closes the
same wedge from the other side, with both caps at `m 2`. -/
theorem exists_uniformEquilibriumPayoff_of_distantPocket_stepThree
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hm3 : m 3 < 0) (hm2 : m 2 ≤ 0) (hm4 : 0 ≤ m 4)
    (hsum : 0 < ∑ e, m e) (hthree : J 3 ≤ 0) (hone : J 1 ≤ 0)
    (hfour : J 4 ≤ m 2) (htwo : J 2 ≤ m 2) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have h23 : (2 : ZMod 5) * 3 = 1 := by decide
  have h33 : (3 : ZMod 5) * 3 = 4 := by decide
  have h43 : (4 : ZMod 5) * 3 = 2 := by decide
  exact exists_uniformEquilibriumPayoff_of_complementaryStep htable hs hsum
    (by decide) hm3 (by rw [h33]; exact hm4) (by rw [h43]; exact hm2) hthree
    (by rw [h23]; exact hone) (by rw [h33, h43]; exact hfour)
    (by rw [h43]; exact htwo)

/-- **The distant pocket at either cap.** -/
theorem isEmpty_counterexampleRegime_of_distantPocket
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0)
    (hm2 : m 2 < 0) (hm3 : m 3 < 0) (hm4 : 0 ≤ m 4) (hm1 : 0 ≤ m 1)
    (hsum : 0 < ∑ e, m e)
    (hcap : (J 1 ≤ m 3 ∧ J 3 ≤ m 3) ∨ (J 2 ≤ m 2 ∧ J 4 ≤ m 2)) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  refine ⟨fun regime => regime.not_exists_uniformEquilibriumPayoff ?_⟩
  rcases hcap with ⟨hone, hthree⟩ | ⟨htwo, hfour⟩
  · exact exists_uniformEquilibriumPayoff_of_distantPocket htable hs hm2 hm3.le
      hm1 hsum (hjoin 2 (by decide)) (hjoin 4 (by decide)) hone hthree
  · exact exists_uniformEquilibriumPayoff_of_distantPocket_stepThree htable hs hm3
      hm2.le hm4 hsum (hjoin 3 (by decide)) (hjoin 1 (by decide)) hfour htwo

/-! ## The branches together -/

/-- **The two branches together.**  A rotation-symmetric table with nonnegative
solo self value and nonpositive join margins carries no counterexample regime as
soon as its margin sum is nonpositive, or some step fires. -/
theorem isEmpty_counterexampleRegime_of_nonpositiveSum_or_isFiringStep
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0)
    (hbranch : (∑ e, m e) ≤ 0 ∨ ∃ c : ZMod 5, IsFiringStep m c) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  have hcirculant := hasCirculantSoloMatrix_of_isCirculantPairTable htable
  rcases hbranch with hsum | ⟨c, hfire⟩
  · exact isEmpty_counterexampleRegime_of_pentagonCirculant_surplus_nonpos
      hcirculant hsum
  · by_cases hsum : (∑ e, m e) ≤ 0
    · exact isEmpty_counterexampleRegime_of_pentagonCirculant_surplus_nonpos
        hcirculant hsum
    · exact isEmpty_counterexampleRegime_of_isFiringStep htable hs (not_le.mp hsum)
        hfire fun k hk => hjoin (k * c) (mul_ne_zero_five k c hk hfire.1)

/-- **The closure up to the complementary pockets.**  A rotation-symmetric
table with nonnegative solo self value and nonpositive join margins carries no
counterexample regime unless its margin sum is positive and its negative
margins are exactly one complementary pair.

Three producers divide the sign patterns between them.  Nonpositive margin sum
is the failure of standard `Q`.  Positive margin sum with a negative margin and
no complementary pocket has a firing step.  No negative margin at all leaves
the solo exit self-enforcing. -/
theorem isEmpty_counterexampleRegime_of_not_isComplementaryPocketMargin
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0)
    (hbranch : (∑ e, m e) ≤ 0 ∨ ¬ IsComplementaryPocketMargin m) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  rcases hbranch with hsum | hpocket
  · exact isEmpty_counterexampleRegime_of_pentagonCirculant_surplus_nonpos
      (hasCirculantSoloMatrix_of_isCirculantPairTable htable) hsum
  · by_cases hneg : ∃ a : ZMod 5, a ≠ 0 ∧ m a < 0
    · refine isEmpty_counterexampleRegime_of_nonpositiveSum_or_isFiringStep htable
        hs hjoin ?_
      by_cases hsum : (∑ e, m e) ≤ 0
      · exact Or.inl hsum
      · exact Or.inr
          (exists_isFiringStep htable.margin_zero (not_le.mp hsum) hneg hpocket)
    · refine isEmpty_counterexampleRegime_of_nonneg_margins htable hs hjoin ?_
      intro d hd
      rcases le_or_gt 0 (m d) with h | h
      · exact h
      · exact absurd ⟨d, hd, h⟩ hneg

/-- **The census.**  A rotation-symmetric table with nonnegative solo self
value and nonpositive join margins either carries no counterexample regime, or
has positive margin sum and negative margins forming exactly one complementary
pair.  No sign pattern is left unaccounted for. -/
theorem isEmpty_counterexampleRegime_or_isComplementaryPocketMargin
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime reward) ∨
      (0 < ∑ e, m e ∧ IsComplementaryPocketMargin m) := by
  by_cases hpocket : IsComplementaryPocketMargin m
  · by_cases hsum : (∑ e, m e) ≤ 0
    · exact Or.inl (isEmpty_counterexampleRegime_of_not_isComplementaryPocketMargin
        htable hs hjoin (Or.inl hsum))
    · exact Or.inr ⟨not_le.mp hsum, hpocket⟩
  · exact Or.inl (isEmpty_counterexampleRegime_of_not_isComplementaryPocketMargin
      htable hs hjoin (Or.inr hpocket))

/-- **The census at the pocket caps.**  A rotation-symmetric table with
nonnegative solo self value and nonpositive join margins either carries no
counterexample regime, or has positive margin sum, negative margins forming
exactly one complementary pair, and *both* cap pairs of that pocket violated.

Against `isEmpty_counterexampleRegime_or_isComplementaryPocketMargin` this
removes from the residual every pocket table meeting one of its two cap pairs.
For the neighbour pocket the two pairs are `J 1, J 2 ≤ m 1` (step four) and
`J 3, J 4 ≤ m 4` (step one); for the distant pocket they are `J 1, J 3 ≤ m 3`
(step two) and `J 2, J 4 ≤ m 2` (step three).  What survives is a table whose
join margins are nonpositive yet still strictly above both negative margins of
its own pocket, in one coordinate of each cap pair. -/
theorem isEmpty_counterexampleRegime_or_uncappedComplementaryPocket
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime reward) ∨
      (0 < ∑ e, m e ∧
        ((m 1 < 0 ∧ m 4 < 0 ∧ 0 ≤ m 2 ∧ 0 ≤ m 3 ∧
            (m 1 < J 1 ∨ m 1 < J 2) ∧ (m 4 < J 3 ∨ m 4 < J 4)) ∨
          (m 2 < 0 ∧ m 3 < 0 ∧ 0 ≤ m 4 ∧ 0 ≤ m 1 ∧
            (m 3 < J 1 ∨ m 3 < J 3) ∧ (m 2 < J 2 ∨ m 2 < J 4)))) := by
  rcases isEmpty_counterexampleRegime_or_isComplementaryPocketMargin htable hs
    hjoin with hempty | ⟨hsum, hpocket⟩
  · exact Or.inl hempty
  rcases neighbour_or_distant_of_isComplementaryPocketMargin hpocket with
    ⟨hm1, hm4, hm2, hm3⟩ | ⟨hm2, hm3, hm4, hm1⟩
  · by_cases hfirst : J 1 ≤ m 1 ∧ J 2 ≤ m 1
    · exact Or.inl (isEmpty_counterexampleRegime_of_neighbourPocket htable hs hjoin
        hm1 hm4 hm2 hm3 hsum (Or.inl hfirst))
    by_cases hsecond : J 3 ≤ m 4 ∧ J 4 ≤ m 4
    · exact Or.inl (isEmpty_counterexampleRegime_of_neighbourPocket htable hs hjoin
        hm1 hm4 hm2 hm3 hsum (Or.inr hsecond))
    refine Or.inr ⟨hsum, Or.inl ⟨hm1, hm4, hm2, hm3, ?_, ?_⟩⟩
    · rcases not_and_or.mp hfirst with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    · rcases not_and_or.mp hsecond with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
  · by_cases hfirst : J 1 ≤ m 3 ∧ J 3 ≤ m 3
    · exact Or.inl (isEmpty_counterexampleRegime_of_distantPocket htable hs hjoin
        hm2 hm3 hm4 hm1 hsum (Or.inl hfirst))
    by_cases hsecond : J 2 ≤ m 2 ∧ J 4 ≤ m 2
    · exact Or.inl (isEmpty_counterexampleRegime_of_distantPocket htable hs hjoin
        hm2 hm3 hm4 hm1 hsum (Or.inr hsecond))
    refine Or.inr ⟨hsum, Or.inr ⟨hm2, hm3, hm4, hm1, ?_, ?_⟩⟩
    · rcases not_and_or.mp hfirst with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    · rcases not_and_or.mp hsecond with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)

/-! ## The residual -/

/-- The constant-step resolution without structure on the larger rows: a
five-player table whose normalized solo matrix is circulant with positive
margin sum, and which has a firing step, has an ordinary uniform-equilibrium
payoff, whatever its rows on two or more players. -/
def ConstantStepCyclicResolution
    (reward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5))
    (margin : ZMod 5 → ℝ) : Prop :=
  HasCirculantSoloMatrix reward margin →
    0 < ∑ e, margin e →
    (∃ c : ZMod 5, IsFiringStep margin c) →
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff

end CirculantTrichotomyClosure
end GameTheory
