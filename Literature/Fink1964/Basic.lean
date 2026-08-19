import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Discounted.FinkHeterogeneous
import UniformEquilibrium.ProofView.Concepts.Stochastic.Transform.ActionLegality.Disintegration

/-!
# Fink 1964: finite stochastic cost games

This file gives the paper's finite model, its stationary value equation, and
its equilibrium predicate.  State-dependent finite action sets are represented
by finite ambient carriers together with legality predicates; every ambient
label is legalized before costs and transitions are evaluated.
-/

noncomputable section

namespace Literature.Fink1964

open GameTheory
open GameTheory.StochasticGame
open Math.Probability
open Math.PMFProduct
open Math.ProbabilityMassFunction

/-- Fink's finite stochastic cost game.  `Legal s i` is the paper's
state-dependent alternative set `J^i(s)`. -/
structure Game (ι : Type) where
  State : Type
  Act : ι → Type
  Legal : State → ∀ i, Act i → Prop
  legal_nonempty : ∀ s i, ∃ a, Legal s i a
  cost : State → (∀ i, Act i) → ι → ℝ
  transition : State → (∀ i, Act i) → PMF State
  discount : ι → ℝ
  discount_nonneg : ∀ i, 0 ≤ discount i
  discount_lt_one : ∀ i, discount i < 1

variable {ι : Type}

namespace Game

/-- The ambient cost game before state-dependent alternatives are padded. -/
def costGame (P : Game ι) : StochasticGame ι where
  State := P.State
  Act := P.Act
  stagePayoff := P.cost
  transition := P.transition
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

/-- The padded cost game: every action is first replaced by a legal action at
the current state. -/
abbrev paddedCostGame (P : Game ι) [Fintype ι] [DecidableEq ι] :
    StochasticGame ι :=
  P.costGame.normalizedGame P.Legal P.legal_nonempty

/-- The reward game used by the production Fink fixed-point theorem.  Rewards
are the negatives of the paper's costs. -/
abbrev rewardGame (P : Game ι) [Fintype ι] [DecidableEq ι] :
    StochasticGame ι where
  State := P.State
  Act := P.Act
  stagePayoff := fun s a who => -P.paddedCostGame.stagePayoff s a who
  transition := P.paddedCostGame.transition
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

/-- A stationary mixed profile on the finite padded action carriers. -/
abbrev StationaryMixedProfile (P : Game ι) [Fintype ι] [DecidableEq ι] :=
  P.rewardGame.StationaryMixedProfile

/-- The legal alternative selected by an ambient action label. -/
def effectiveAction (P : Game ι) [Fintype ι] [DecidableEq ι]
    (s : P.State) (i : ι) (a : P.Act i) :
    {b : P.Act i // P.Legal s i b} :=
  ⟨P.costGame.legalizeAct P.Legal P.legal_nonempty s i a,
    P.costGame.legal_legalizeAct P.Legal P.legal_nonempty s i a⟩

/-- The probability vector on the paper's literal alternative set `J^i(s)`
induced by a padded stationary strategy. -/
def effectiveMixedAction (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (s : P.State) (i : ι) :
    PMF {a : P.Act i // P.Legal s i a} :=
  (x s i).map (P.effectiveAction s i)

/-- Fink's unnormalized value vector `e_{hi}` encoded as the normalized reward
vector expected by the production fixed-point theorem. -/
def normalizedRewardValue (P : Game ι)
    (e : P.State → Payoff ι) : P.State → Payoff ι :=
  fun s who => -(1 - P.discount who) * e s who

/-- The integrand in equations (3), (4), and (6): current cost plus discounted
expected continuation cost. -/
def oneStepCost (P : Game ι) [Fintype ι] [DecidableEq ι]
    (e : P.State → Payoff ι) (s : P.State) (a : ∀ i, P.Act i)
    (who : ι) : ℝ :=
  P.paddedCostGame.stagePayoff s a who +
    P.discount who *
      expect (P.paddedCostGame.transition s a) (fun s' => e s' who)

/-- Equation (6), and equations (3)--(5) after mixing.  The deviating player's
mixed action is `y`; every other player uses the state component of `x`. -/
def f (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (who : ι) (y : PMF (P.Act who))
    (e : P.State → Payoff ι) (s : P.State) : ℝ :=
  expect (pmfPi (Function.update (x s) who y))
    (fun a => P.oneStepCost e s a who)

/-- Equation (4): `e` is the stationary value vector induced by `x`. -/
def IsValueVector (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι) : Prop :=
  ∀ s who, P.f x who (x s who) e s = e s who

/-- Equation (5): the prescribed mixed action minimizes one-stage cost plus
discounted continuation cost at every state and for every player. -/
def IsEquilibriumPoint (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι) : Prop :=
  P.IsValueVector x e ∧
    ∀ s who (y : PMF (P.Act who)),
      P.f x who (x s who) e s ≤ P.f x who y e s

theorem one_sub_discount_pos (P : Game ι) (who : ι) :
    0 < 1 - P.discount who :=
  sub_pos.mpr (P.discount_lt_one who)

theorem one_sub_discount_ne (P : Game ι) (who : ι) :
    1 - P.discount who ≠ 0 :=
  ne_of_gt (P.one_sub_discount_pos who)

private theorem update_own_mixedAction
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (s : P.State) (who : ι) :
    Function.update (x s) who (x s who) = x s := by
  funext i
  by_cases hi : i = who
  · subst i
    simp
  · simp [Function.update_of_ne hi]

/-- Pointwise algebra behind the cost/reward adapter. -/
theorem reward_discountedAuxPayoff_eq
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    (e : P.State → Payoff ι) (s : P.State) (a : ∀ i, P.Act i)
    (who : ι) :
    P.rewardGame.discountedAuxPayoff (P.discount who)
        (P.normalizedRewardValue e) s a who =
      -(1 - P.discount who) * P.oneStepCost e s a who := by
  change
    (1 - P.discount who) * (-P.paddedCostGame.stagePayoff s a who) +
        P.discount who *
          expect (P.paddedCostGame.transition s a)
            (fun s' => -(1 - P.discount who) * e s' who) =
      -(1 - P.discount who) *
        (P.paddedCostGame.stagePayoff s a who +
          P.discount who *
            expect (P.paddedCostGame.transition s a) (fun s' => e s' who))
  rw [expect_const_mul]
  ring

/-- Mixed algebra behind the cost/reward adapter. -/
theorem reward_discountedAuxEU_eq
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (who : ι) (y : PMF (P.Act who))
    (e : P.State → Payoff ι) (s : P.State) :
    P.rewardGame.discountedAuxEU (P.discount who)
        (P.normalizedRewardValue e) s
        (Function.update (x s) who y) who =
      -(1 - P.discount who) * P.f x who y e s := by
  unfold StochasticGame.discountedAuxEU f
  simp_rw [P.reward_discountedAuxPayoff_eq e s]
  rw [expect_const_mul]

/-- The same mixed algebra for the prescribed profile, without the
syntactic self-update. -/
theorem reward_discountedAuxEU_profile_eq
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι)
    (s : P.State) (who : ι) :
    P.rewardGame.discountedAuxEU (P.discount who)
        (P.normalizedRewardValue e) s (x s) who =
      -(1 - P.discount who) * P.f x who (x s who) e s := by
  rw [← P.update_own_mixedAction x s who]
  exact P.reward_discountedAuxEU_eq x who (x s who) e s

/-- The normalized-reward Bellman certificate is exactly the paper's
cost-minimizing equilibrium condition. -/
theorem isEquilibriumPoint_iff_isPlayerDiscountedStationaryBellmanEq
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι) :
    P.IsEquilibriumPoint x e ↔
      P.rewardGame.IsPlayerDiscountedStationaryBellmanEq P.discount x
        (P.normalizedRewardValue e) := by
  constructor
  · rintro ⟨hvalue, hmin⟩
    constructor
    · intro s who y
      rw [P.reward_discountedAuxEU_eq x who y e s,
        P.reward_discountedAuxEU_profile_eq x e s who]
      exact mul_le_mul_of_nonpos_left (hmin s who y)
        (neg_nonpos.mpr (sub_nonneg.mpr (P.discount_lt_one who).le))
    · intro s who
      rw [P.reward_discountedAuxEU_profile_eq x e s who,
        hvalue s who]
      rfl
  · rintro ⟨hnash, hvalue⟩
    constructor
    · intro s who
      have h := hvalue s who
      rw [P.reward_discountedAuxEU_profile_eq x e s who] at h
      dsimp [normalizedRewardValue] at h
      have hne := P.one_sub_discount_ne who
      nlinarith
    · intro s who y
      have h := hnash s who y
      rw [P.reward_discountedAuxEU_eq x who y e s,
        P.reward_discountedAuxEU_profile_eq x e s who] at h
      have hpos := P.one_sub_discount_pos who
      nlinarith

/-- A uniform bound on the finite reward table. -/
def rewardBound (P : Game ι) [Fintype P.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (P.Act i)] : ℝ :=
  ∑ s : P.State, ∑ a : (∀ i, P.Act i), ∑ who : ι,
    |P.rewardGame.stagePayoff s a who|

theorem rewardBound_nonneg (P : Game ι) [Fintype P.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (P.Act i)] :
    0 ≤ P.rewardBound := by
  unfold rewardBound
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_reward_le_rewardBound
    (P : Game ι) [Fintype P.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (P.Act i)]
    (s : P.State) (a : ∀ i, P.Act i) (who : ι) :
    |P.rewardGame.stagePayoff s a who| ≤ P.rewardBound := by
  classical
  unfold rewardBound
  calc
    |P.rewardGame.stagePayoff s a who|
        ≤ ∑ who' : ι, |P.rewardGame.stagePayoff s a who'| := by
          exact Finset.single_le_sum
            (f := fun who' : ι => |P.rewardGame.stagePayoff s a who'|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ who)
    _ ≤ ∑ a' : (∀ i, P.Act i),
          ∑ who' : ι, |P.rewardGame.stagePayoff s a' who'| := by
          exact Finset.single_le_sum
            (f := fun a' : (∀ i, P.Act i) =>
              ∑ who' : ι, |P.rewardGame.stagePayoff s a' who'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (Finset.mem_univ a)
    _ ≤ ∑ s' : P.State, ∑ a' : (∀ i, P.Act i),
          ∑ who' : ι, |P.rewardGame.stagePayoff s' a' who'| := by
          exact Finset.single_le_sum
            (f := fun s' : P.State =>
              ∑ a' : (∀ i, P.Act i),
                ∑ who' : ι, |P.rewardGame.stagePayoff s' a' who'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ =>
              Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (Finset.mem_univ s)

end Game

end Literature.Fink1964
