import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Discounted.FinkHeterogeneous
import UniformEquilibrium.ProofView.Concepts.Stochastic.Transform.ActionLegality.Disintegration

/-!
# A. M. Fink, *Equilibrium in a Stochastic n-Person Game* (1964)

Primary source:

A. M. Fink, “Equilibrium in a Stochastic n-Person Game,”
*Journal of Science of the Hiroshima University, Series A-I* **28** (1964),
89–93. DOI: `10.32917/hmj/1206139508`.

The file follows the paper's cost-minimization convention and its
player-specific discount factors `α_h`. Two representation adapters are made
explicit.

* The paper writes a separate finite alternative set `J^h(i)` at each state.
  `Game.Act h` is a finite ambient carrier and `Game.Legal i h` selects
  `J^h(i)`. Illegal ambient labels are mapped to a fixed legal alternative
  before costs and transitions are evaluated. This is the standard finite
  padding of a state-dependent action family.
* The production Fink map is written for normalized rewards. A paper cost
  value `e` is encoded as the normalized reward
  `-(1 - α_h) e_h`. The definition `f` divides the resulting auxiliary reward
  by the same positive factor, so it is exactly Fink's unnormalized expression
  `C_h + α_h E[e_h']`.

The paper's headline theorem is proved without `sorry`. The proof uses the
single-valued Brouwer implementation in `FinkHeterogeneous.lean`; this is
equivalent to the paper's Kakutani route but does not silently replace the
paper's definitions or its player-dependent discounts.
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

/-- The ambient cost game before state-dependent alternatives are padded. -/
def Game.costGame (P : Game ι) : StochasticGame ι where
  State := P.State
  Act := P.Act
  stagePayoff := P.cost
  transition := P.transition
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

/-- The padded cost game: every ambient action is first replaced by a legal
action at the current state. -/
abbrev Game.paddedCostGame (P : Game ι) [Fintype ι] [DecidableEq ι] :
    StochasticGame ι :=
  P.costGame.normalizedGame P.Legal P.legal_nonempty

/-- The reward game used by the production fixed-point theorem. Rewards are
the negatives of Fink's costs. -/
def Game.rewardGame (P : Game ι) [Fintype ι] [DecidableEq ι] :
    StochasticGame ι where
  State := P.State
  Act := P.Act
  stagePayoff := fun s a who => -P.paddedCostGame.stagePayoff s a who
  transition := P.paddedCostGame.transition
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

/-- A stationary mixed profile, represented on the finite padded action
carriers. Its semantic marginal on `J^i(s)` is `effectiveMixedAction`. -/
abbrev Game.StationaryMixedProfile (P : Game ι) [Fintype ι] [DecidableEq ι] :=
  P.rewardGame.StationaryMixedProfile

/-- The actual legal alternative selected by an ambient action label. -/
def Game.effectiveAction (P : Game ι) [Fintype ι] [DecidableEq ι]
    (s : P.State) (i : ι) (a : P.Act i) :
    {b : P.Act i // P.Legal s i b} :=
  ⟨P.costGame.legalizeAct P.Legal P.legal_nonempty s i a,
    P.costGame.legal_legalizeAct P.Legal P.legal_nonempty s i a⟩

/-- The probability vector on the paper's literal alternative set `J^i(s)`
induced by a padded stationary strategy. -/
def Game.effectiveMixedAction (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (s : P.State) (i : ι) :
    PMF {a : P.Act i // P.Legal s i a} :=
  (x s i).map (P.effectiveAction s i)

/-- Fink's unnormalized value vector `e_{hi}` is encoded as a normalized
reward vector. -/
def Game.normalizedRewardValue (P : Game ι)
    (e : P.State → Payoff ι) : P.State → Payoff ι :=
  fun s who => -(1 - P.discount who) * e s who

/-- Equation (6), and equations (3)–(5) after mixing.

The displayed definition is the exact cost expression through the normalized
reward adapter:
`f(x,y,e) = - EU_reward(x_{-h},y; -(1-α_h)e) / (1-α_h)`.
Because `α_h < 1`, this expands to
`E[C_h + α_h E[e_h(next)]]`. -/
def Game.f (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (y : PMF (P.Act who))
    (e : P.State → Payoff ι) (s : P.State) (who : ι) : ℝ :=
  -P.rewardGame.discountedAuxEU (P.discount who)
      (P.normalizedRewardValue e) s (Function.update (x s) who y) who /
    (1 - P.discount who)

/-- Equation (4): `e(x)` is a value vector for the stationary profile `x`. -/
def Game.IsValueVector (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι) : Prop :=
  ∀ s who, P.f x (x s who) e s who = e s who

/-- Equation (5): at every state and for every player, the prescribed mixed
alternative minimizes the one-stage cost plus discounted continuation cost. -/
def Game.IsEquilibriumPoint (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι) : Prop :=
  P.IsValueVector x e ∧
    ∀ s who (y : PMF (P.Act who)),
      P.f x (x s who) e s who ≤ P.f x y e s who

theorem Game.one_sub_discount_pos (P : Game ι) (who : ι) :
    0 < 1 - P.discount who :=
  sub_pos.mpr (P.discount_lt_one who)

theorem Game.one_sub_discount_ne (P : Game ι) (who : ι) :
    1 - P.discount who ≠ 0 :=
  ne_of_gt (P.one_sub_discount_pos who)

/-- The normalized-reward Bellman certificate is exactly the paper's
cost-minimizing equilibrium condition. -/
theorem Game.isEquilibriumPoint_iff_isPlayerDiscountedStationaryBellmanEq
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι) :
    P.IsEquilibriumPoint x e ↔
      P.rewardGame.IsPlayerDiscountedStationaryBellmanEq P.discount x
        (P.normalizedRewardValue e) := by
  constructor
  · rintro ⟨hvalue, hmin⟩
    constructor
    · intro s who y
      have hpos := P.one_sub_discount_pos who
      have hmin' := hmin s who y
      unfold Game.f at hmin'
      dsimp only at hmin'
      nlinarith
    · intro s who
      have h := hvalue s who
      unfold Game.f at h
      dsimp [Game.normalizedRewardValue]
      have hne := P.one_sub_discount_ne who
      apply (div_eq_iff hne).mp at h
      nlinarith
  · rintro ⟨hnash, hvalue⟩
    constructor
    · intro s who
      have h := hvalue s who
      unfold Game.f
      rw [h]
      simp only [Game.normalizedRewardValue]
      field_simp [P.one_sub_discount_ne who]
      ring
    · intro s who y
      have h := hnash s who y
      unfold Game.f
      have hpos := P.one_sub_discount_pos who
      nlinarith

/-- A chosen uniform upper bound on the absolute finite reward table. -/
noncomputable def Game.rewardBound (P : Game ι) [Finite P.State]
    [Fintype ι] [DecidableEq ι] [∀ i, Finite (P.Act i)] : ℝ :=
  max 0 (Classical.choose (Finite.bddAbove_range
    (fun p : P.rewardGame.State × P.rewardGame.JointAct × ι =>
      |P.rewardGame.stagePayoff p.1 p.2.1 p.2.2|)))

theorem Game.rewardBound_nonneg (P : Game ι) [Finite P.State]
    [Fintype ι] [DecidableEq ι] [∀ i, Finite (P.Act i)] :
    0 ≤ P.rewardBound := by
  exact le_max_left 0 _

theorem Game.abs_reward_le_rewardBound
    (P : Game ι) [Finite P.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Finite (P.Act i)]
    (s : P.rewardGame.State) (a : P.rewardGame.JointAct) (who : ι) :
    |P.rewardGame.stagePayoff s a who| ≤ P.rewardBound := by
  let F : P.rewardGame.State × P.rewardGame.JointAct × ι → ℝ :=
    fun p => |P.rewardGame.stagePayoff p.1 p.2.1 p.2.2|
  have hb : BddAbove (Set.range F) := Finite.bddAbove_range F
  have hchosen : F (s, a, who) ≤ Classical.choose hb :=
    Classical.choose_spec hb ⟨(s, a, who), rfl⟩
  exact hchosen.trans (le_max_right 0 (Classical.choose hb))

/-- Theorem 2: every finite stochastic `n`-person cost game has a stationary
equilibrium point, with the discount factor allowed to depend on the player. -/
theorem Game.exists_equilibriumPoint
    (P : Game ι) [Finite P.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (P.Act i)] [∀ i, Nonempty (P.Act i)] :
    ∃ (x : P.StationaryMixedProfile) (e : P.State → Payoff ι),
      P.IsEquilibriumPoint x e := by
  obtain ⟨x, V, hcert⟩ :=
    P.rewardGame.exists_isPlayerDiscountedStationaryBellmanEq
      P.discount P.rewardBound P.rewardBound_nonneg
      P.discount_nonneg (fun who => (P.discount_lt_one who).le)
      P.abs_reward_le_rewardBound
  let e : P.State → Payoff ι :=
    fun s who => -V s who / (1 - P.discount who)
  have hencode : P.normalizedRewardValue e = V := by
    funext s who
    dsimp [Game.normalizedRewardValue, e]
    field_simp [P.one_sub_discount_ne who]
    ring
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
equivalent gain-adjustment Brouwer map. In particular:

* compactness and convexity are `convex_finkDomain` and
  `isCompact_finkDomain`;
* continuity of the joint map is `continuous_playerFinkMap`;
* fixed-point existence is `exists_playerFinkMap_fixedPoint`;
* decoding the fixed point is
  `isPlayerDiscountedStationaryBellmanEq_of_playerFinkMap_fixedPoint`.

Thus none of the paper's existence argument is assumed. The numbered
contraction and correspondence lemmas are proof architecture for Theorem 2,
not additional game-theoretic conclusions; the imported Brouwer
implementation discharges their role without introducing axioms.

## Scope of the final paragraph

The paper also says that the argument extends to countably many states with
bounded costs by replacing the finite-dimensional value space by `ℓ∞`, and
that arbitrary action cardinalities with `min` replaced by `inf` yield
ε-effective strategies. Those sentences do not specify the topology,
measurability, or attainment hypotheses needed for a unique Lean statement.
They are recorded here rather than silently strengthened. The formal theorem
above is exactly the finite-state, finite-action theorem proved in the body of
the paper. The comparisons with Shapley's two-player theorem and the
one-player dynamic-programming case are bibliographic remarks.
-/

end Literature.Fink1964
