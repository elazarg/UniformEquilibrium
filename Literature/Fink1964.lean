import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Discounted.FinkHeterogeneous
import UniformEquilibrium.ProofView.Concepts.Stochastic.Transform.ActionLegality.Disintegration

/-!
# A. M. Fink, *Equilibrium in a Stochastic n-Person Game* (1964)

Primary source:

A. M. Fink, “Equilibrium in a Stochastic n-Person Game,”
*Journal of Science of the Hiroshima University, Series A-I* **28** (1964),
89–93. DOI: `10.32917/hmj/1206139508`.

The file follows the paper's cost-minimization convention and its
player-specific discount factors `α_h`.  Two representation adapters are
made explicit.

* The paper writes a separate finite alternative set `J^h(i)` at each state.
  `Game.Act h` is a finite ambient carrier and `Game.Legal i h` selects
  `J^h(i)`.  Illegal ambient labels are mapped to a fixed legal alternative
  before costs and transitions are evaluated.  This is the standard finite
  padding of a state-dependent action family.
* The production Fink map is written for normalized rewards.  A paper cost
  value `e` is encoded as the normalized reward
  `-(1 - α_h) e_h`.  The definition `f` divides the resulting auxiliary
  reward by the same positive factor, so it is exactly Fink's unnormalized
  expression `C_h + α_h E[e_h']`.

The paper's headline theorem is proved without `sorry`.  The proof uses the
single-valued Brouwer implementation in
`FinkHeterogeneous.lean`; this is equivalent to the paper's Kakutani route
but does not silently replace the paper's definitions or its
player-dependent discounts.
-/

noncomputable section

namespace Literature.Fink1964

open GameTheory
open GameTheory.StochasticGame
open Math.Probability
open Math.ProbabilityMassFunction

/-- The finite stochastic cost game on pages 89–90.

`Legal s i` is the paper's state-dependent alternative set `J^i(s)`,
represented inside a common finite ambient action type. -/
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

/-- The padded cost game: every ambient action is first replaced by a legal
action at the current state. -/
abbrev paddedCostGame (P : Game ι) [Fintype ι] [DecidableEq ι] :
    StochasticGame ι :=
  P.costGame.normalizedGame P.Legal P.legal_nonempty

/-- The reward game used by the production fixed-point theorem.  Rewards are
the negatives of Fink's costs. -/
abbrev rewardGame (P : Game ι) [Fintype ι] [DecidableEq ι] :
    StochasticGame ι where
  State := P.State
  Act := P.Act
  stagePayoff := fun s a who => -P.paddedCostGame.stagePayoff s a who
  transition := P.paddedCostGame.transition
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

/-- A stationary mixed profile, represented on the finite padded action
carriers.  Its semantic marginal on `J^i(s)` is `effectiveMixedAction`. -/
abbrev StationaryMixedProfile (P : Game ι) [Fintype ι] [DecidableEq ι] :=
  P.rewardGame.StationaryMixedProfile

/-- The actual legal alternative selected by an ambient action label. -/
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

/-- Fink's unnormalized value vector `e_{hi}` is encoded as a normalized
reward vector. -/
def normalizedRewardValue (P : Game ι)
    (e : P.State → Payoff ι) : P.State → Payoff ι :=
  fun s who => -(1 - P.discount who) * e s who

/-- Equation (6), and equations (3)–(5) after mixing.

The displayed definition is the exact cost expression through the normalized
reward adapter:
`f(x,y,e) = - EU_reward(x_{-h},y; -(1-α_h)e) / (1-α_h)`.
Because `α_h < 1`, this expands to
`E[C_h + α_h E[e_h(next)]]`. -/
def f (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (who : ι) (y : PMF (P.Act who))
    (e : P.State → Payoff ι) (s : P.State) : ℝ :=
  -P.rewardGame.discountedAuxEU (P.discount who)
      (P.normalizedRewardValue e) s (Function.update (x s) who y) who /
    (1 - P.discount who)

/-- Equation (4): `e(x)` is a value vector for the stationary profile `x`. -/
def IsValueVector (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι) : Prop :=
  ∀ s who, P.f x who (x s who) e s = e s who

/-- Equation (5): at every state and for every player, the prescribed mixed
alternative minimizes the one-stage cost plus discounted continuation cost. -/
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
      have hmin' := hmin s who y
      unfold f at hmin'
      rw [P.update_own_mixedAction x s who] at hmin'
      have hpos := P.one_sub_discount_pos who
      have hscaled := (div_le_div_iff_of_pos_right hpos).mp hmin'
      linarith
    · intro s who
      have h := hvalue s who
      unfold f at h
      rw [P.update_own_mixedAction x s who] at h
      have hne := P.one_sub_discount_ne who
      have hmul := (div_eq_iff hne).mp h
      dsimp [normalizedRewardValue]
      linarith
  · rintro ⟨hnash, hvalue⟩
    constructor
    · intro s who
      unfold f
      rw [P.update_own_mixedAction x s who, hvalue s who]
      dsimp [normalizedRewardValue]
      field_simp [P.one_sub_discount_ne who]
      ring
    · intro s who y
      have h := hnash s who y
      unfold f
      rw [P.update_own_mixedAction x s who]
      have hpos := P.one_sub_discount_pos who
      apply (div_le_div_iff_of_pos_right hpos).mpr
      linarith

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

/-- Theorem 2: every finite stochastic `n`-person cost game has a stationary
equilibrium point, with the discount factor allowed to depend on the player. -/
theorem exists_equilibriumPoint
    (P : Game ι) [Finite P.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (P.Act i)] [∀ i, Nonempty (P.Act i)] :
    ∃ (x : P.StationaryMixedProfile) (e : P.State → Payoff ι),
      P.IsEquilibriumPoint x e := by
  letI : Fintype P.State := Fintype.ofFinite P.State
  letI : ∀ i, Fintype (P.Act i) := fun i => Fintype.ofFinite (P.Act i)
  obtain ⟨x, V, hcert⟩ :=
    P.rewardGame.exists_isPlayerDiscountedStationaryBellmanEq
      P.discount P.rewardBound P.rewardBound_nonneg
      P.discount_nonneg (fun who => (P.discount_lt_one who).le)
      P.abs_reward_le_rewardBound
  let e : P.State → Payoff ι :=
    fun s who => -V s who / (1 - P.discount who)
  have hencode : P.normalizedRewardValue e = V := by
    funext s who
    dsimp [normalizedRewardValue, e]
    field_simp [P.one_sub_discount_ne who]
  refine ⟨x, e,
    (P.isEquilibriumPoint_iff_isPlayerDiscountedStationaryBellmanEq x e).2 ?_⟩
  rw [hencode]
  exact hcert

/-!
## Paper proof route

After Lemma 1, Fink defines the optimal-response operator `T_x`, proves it is
an `α = max_h α_h` contraction (Theorem 1), obtains its unique fixed point
`β(x)`, proves boundedness and continuity of `β`, proves that the optimal
response correspondence `φ` has closed graph, and applies Kakutani.

The production theorem above proves the same finite claim through the
equivalent gain-adjustment Brouwer map.  In particular:

* compactness and convexity are `convex_finkDomain` and
  `isCompact_finkDomain`;
* continuity of the joint map is `continuous_playerFinkMap`;
* fixed-point existence is `exists_playerFinkMap_fixedPoint`;
* decoding the fixed point is
  `isPlayerDiscountedStationaryBellmanEq_of_playerFinkMap_fixedPoint`.

Thus none of the paper's existence argument is assumed.  The numbered
contraction and correspondence lemmas are proof architecture for Theorem 2,
not additional game-theoretic conclusions; the imported Brouwer
implementation discharges their role without introducing axioms.

## Scope of the final paragraph

The paper also says that the argument extends to countably many states with
bounded costs by replacing the finite-dimensional value space by `ℓ∞`, and
that arbitrary action cardinalities with `min` replaced by `inf` yield
ε-effective strategies.  Those sentences do not specify the topology,
measurability, or attainment hypotheses needed for a unique Lean statement.
They are recorded here rather than silently strengthened.  The formal theorem
above is exactly the finite-state, finite-action theorem proved in the body of
the paper.  The comparisons with Shapley's two-player theorem and the
one-player dynamic-programming case are bibliographic remarks.
-/

end Game

end Literature.Fink1964
