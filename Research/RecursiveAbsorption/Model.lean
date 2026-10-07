import MathUE.PMFProduct.Bool
import UniformEquilibrium.ProofView.Concepts.Stochastic.Classes.Absorbing

/-!
# Canonical recursive games with probabilistic absorption

There are two players with arbitrary finite action spaces and one live state.
The live stage payoff is zero. Each live action pair independently absorbs
with its specified probability into an action-independent payoff state.
This is the canonical table presentation used by Flesch, Thuijsman and Vrieze
(1996), Section 2. It is not a reduction from arbitrary stochastic games or
an equivalence for state-dependent action padding.

The absorbing states retain both action spaces, but every action has exactly
the same payoff and self-transition there. No expected-pathwise-liminf payoff
identity or behavioral best-response theorem is asserted in this model module.
-/

noncomputable section

open _root_.Math.Probability Math.PMFProduct

namespace GameTheory.RecursiveAbsorption

/-- `false` is the row player and `true` is the column player. -/
abbrev Action (I J : Type) (who : Bool) : Type := Bool.rec I J who

/-- Actual absorption probabilities and both players' absorbing rewards. -/
structure Data (I J : Type) where
  absorption : I → J → Set.Icc (0 : ℝ) 1
  reward : I → J → Payoff Bool

variable {I J : Type}

instance [Fintype I] [Fintype J] (who : Bool) : Fintype (Action I J who) := by
  cases who <;> assumption

/-- The literal joint action with row `i` and column `j`. -/
def jointAction (i : I) (j : J) : ∀ who, Action I J who :=
  fun who => Bool.rec i j who

@[simp] theorem jointAction_false (i : I) (j : J) : jointAction i j false = i := rfl

@[simp] theorem jointAction_true (i : I) (j : J) : jointAction i j true = j := rfl

/-- One live state and one absorbing payoff state for every action pair. -/
def game (D : Data I J) : StochasticGame Bool where
  State := Option (I × J)
  Act := Action I J
  stagePayoff := fun state _ who =>
    match state with
    | none => 0
    | some pair => D.reward pair.1 pair.2 who
  transition := fun state action =>
    match state with
    | none =>
        (bernoulliBoolEquiv (D.absorption (action false) (action true))).map
          fun absorbed => if absorbed then some (action false, action true) else none
    | some pair => PMF.pure (some pair)
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

instance [Fintype I] [Fintype J] (D : Data I J) : Fintype (game D).State :=
  inferInstanceAs (Fintype (Option (I × J)))

instance [DecidableEq I] [DecidableEq J] (D : Data I J) : DecidableEq (game D).State :=
  inferInstanceAs (DecidableEq (Option (I × J)))

instance [Fintype I] [Fintype J] (D : Data I J) (who : Bool) :
    Fintype ((game D).Act who) := by
  cases who <;> assumption

instance [DecidableEq I] [DecidableEq J] (D : Data I J) (who : Bool) :
    DecidableEq ((game D).Act who) := by
  cases who <;> assumption

instance [Nonempty I] [Nonempty J] (D : Data I J) (who : Bool) :
    Nonempty ((game D).Act who) := by
  cases who <;> assumption

@[simp] theorem stagePayoff_none (D : Data I J)
    (action : (game D).JointAct) (who : Bool) :
    (game D).stagePayoff none action who = 0 := rfl

@[simp] theorem stagePayoff_some (D : Data I J) (pair : I × J)
    (action : (game D).JointAct) (who : Bool) :
    (game D).stagePayoff (some pair) action who = D.reward pair.1 pair.2 who := rfl

@[simp] theorem transition_some (D : Data I J) (pair : I × J)
    (action : (game D).JointAct) :
    (game D).transition (some pair) action = PMF.pure (some pair) := rfl

/-- Every payoff state is literally absorbing, independently of both actions. -/
theorem isAbsorbingState_some (D : Data I J) (pair : I × J) :
    (game D).IsAbsorbingState (some pair) := fun _ => rfl

/-- Exact expectation of any state value after a live-state pure action pair. -/
theorem expect_transition_none (D : Data I J) (action : (game D).JointAct)
    (v : (game D).State → ℝ) :
    expect ((game D).transition none action) v =
      (1 - (D.absorption (action false) (action true) : ℝ)) * v none +
        (D.absorption (action false) (action true) : ℝ) *
          v (some (action false, action true)) := by
  change expect
    ((bernoulliBoolEquiv (D.absorption (action false) (action true))).map
      fun absorbed => if absorbed then some (action false, action true) else none) v = _
  rw [expect_map_fintype_source, Fintype.sum_bool]
  simp [add_comm]

@[simp] theorem expect_transition_some (D : Data I J) (pair : I × J)
    (action : (game D).JointAct) (v : (game D).State → ℝ) :
    expect ((game D).transition (some pair) action) v = v (some pair) := by
  change expect (PMF.pure (some pair)) (fun state : Option (I × J) => v state) = _
  exact expect_pure _ _

/-- Both independent live-state mixed actions, retained harmlessly after absorption. -/
def mixedAction (x : PMF I) (y : PMF J) : ∀ who, PMF (Action I J who) :=
  fun who => Bool.rec x y who

/-- The actual stationary behavioral profile, not a supplied payoff functional. -/
def stationaryProfile (D : Data I J) (x : PMF I) (y : PMF J) :
    (game D).BehaviorProfile :=
  (game D).stationaryBehaviorProfile (mixedAction x y)

section FiniteActions

variable [Fintype I] [Fintype J]

/-- The stationary action law has the literal row-column independent expectation. -/
theorem expect_stationaryAction (D : Data I J) (x : PMF I) (y : PMF J)
    {t : ℕ} (history : (game D).Hist t) (f : (game D).JointAct → ℝ) :
    expect ((game D).stageActionDist (stationaryProfile D x y) history) f =
      expect x (fun i => expect y (fun j => f (jointAction i j))) := by
  change expect (pmfPi (mixedAction x y)) f = _
  exact expect_pmfPi_boolFamily (mixedAction x y) f

/-- The actual one-step state-value expectation at the live state under stationary play. -/
theorem expect_stationaryTransition_none (D : Data I J) (x : PMF I) (y : PMF J)
    (v : (game D).State → ℝ) :
    expect ((game D).stageActionDist (stationaryProfile D x y)
        ((game D).emptyHist none))
      (fun action => expect ((game D).transition none action) v) =
      expect x (fun i => expect y (fun j =>
        (1 - (D.absorption i j : ℝ)) * v none +
          (D.absorption i j : ℝ) * v (some (i, j)))) := by
  rw [expect_stationaryAction]
  apply congrArg (expect x)
  funext i
  apply congrArg (expect y)
  funext j
  exact expect_transition_none D (jointAction i j) v

end FiniteActions

end GameTheory.RecursiveAbsorption
