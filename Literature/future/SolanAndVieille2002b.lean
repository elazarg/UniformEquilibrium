import Mathlib

noncomputable section

open scoped BigOperators
open Filter Set

/-!
# E. Solan and N. Vieille, “Correlated Equilibrium in Stochastic Games” (2002)

Bibliography label: Solan & Vieille 2002b.
Published in *Games and Economic Behavior* 38(2), 362--399.
DOI: `10.1006/game.2001.0887`.
Public copy: `https://www.math.tau.ac.il/~eilons/correl8.pdf`.

This is a partial source audit and therefore remains in `Literature/future/`.
It records the semantic core needed before the later proof statements can be
audited safely.  In particular:

* action sets are finite and nonempty;
* an exit stores only the coalition action, not arbitrary outsider actions;
* equation (5) is a probability law on states outside the communicating set;
* stationary evaluation is harmonic, with no added stage-payoff term;
* the cleaning operation and equations (19)--(21) are explicit;
* asymptotic exit laws first take the eventual exit law for each profile and
  only then take the profile limit; and
* the constrained fixed-point assertion is restricted to sufficiently small
  parameters and to the positive-recursive absorbing reduction of Section 5.

The paper's equilibrium conclusions are not restated as Lean propositions
until the extended-game probability and deviation semantics are complete.
This avoids hiding missing definitions behind arbitrary `Prop` parameters.
-/

namespace Literature.SolanAndVieille2002b

/-- A finitely supported probability distribution.  The list representation
avoids imposing a global decidable-equality instance on every semantic type. -/
structure FiniteDistribution (α : Type*) where
  support : List α
  nodup : support.Nodup
  prob : α → ℝ
  nonnegative : ∀ a, 0 ≤ prob a
  zero_off_support : ∀ a, a ∉ support → prob a = 0
  total : (support.map prob).sum = 1

namespace FiniteDistribution

variable {α β : Type*}

/-- Expectation of a real-valued function. -/
def expectation (d : FiniteDistribution α) (f : α → ℝ) : ℝ :=
  (d.support.map fun a => d.prob a * f a).sum

/-- The probability assigned to a predicate. -/
def eventProbability (d : FiniteDistribution α) (event : α → Prop)
    [DecidablePred event] : ℝ :=
  (d.support.map fun a => if event a then d.prob a else 0).sum

end FiniteDistribution

/-- The finite stochastic-game data of Section 2.  Nonempty actions are part
of the carrier, so Theorem 2.3 is not silently extended to empty menus. -/
structure PaperGame (ι : Type*) [Fintype ι] [DecidableEq ι] where
  State : Type
  stateFintype : Fintype State
  stateDecidableEq : DecidableEq State
  Action : ι → Type
  actionFintype : ∀ i, Fintype (Action i)
  actionDecidableEq : ∀ i, DecidableEq (Action i)
  actionNonempty : ∀ i, Nonempty (Action i)
  transition : State → (∀ i, Action i) → FiniteDistribution State
  stagePayoff : State → (∀ i, Action i) → ι → ℝ
  payoffBound : ∀ state action who, |stagePayoff state action who| ≤ 1

attribute [instance] PaperGame.stateFintype PaperGame.stateDecidableEq
  PaperGame.actionFintype PaperGame.actionDecidableEq PaperGame.actionNonempty

namespace PaperGame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

abbrev JointAction := ∀ i, G.Action i
abbrev ProductMixedAction := ∀ i, FiniteDistribution (G.Action i)
abbrev StationaryProfile := G.State → G.ProductMixedAction

/-- The product probability of a pure joint action. -/
def productProbability (x : G.ProductMixedAction) (action : G.JointAction) : ℝ := by
  classical
  exact ∏ i, (x i).prob (action i)

/-- Mixed transition probability under independent player lotteries. -/
def mixedTransitionProbability (state : G.State) (x : G.ProductMixedAction)
    (next : G.State) : ℝ := by
  classical
  exact ∑ action : G.JointAction,
    G.productProbability x action * (G.transition state action).prob next

/-- Mixed transition mass of a finite state set. -/
def mixedTransitionMass (state : G.State) (x : G.ProductMixedAction)
    (states : Finset G.State) : ℝ := by
  classical
  exact ∑ next ∈ states, G.mixedTransitionProbability state x next

/-- Mixed one-stage payoff under independent player lotteries. -/
def mixedStagePayoff (state : G.State) (x : G.ProductMixedAction)
    (who : ι) : ℝ := by
  classical
  exact ∑ action : G.JointAction,
    G.productProbability x action * G.stagePayoff state action who

/-- An autonomous device chooses a fresh private signal vector from the
previous private signal vectors only.  It does not observe states or actions. -/
structure AutonomousDevice (G : PaperGame ι) where
  Signal : ℕ → ι → Type
  signalFintype : ∀ n i, Fintype (Signal n i)
  signalDecidableEq : ∀ n i, DecidableEq (Signal n i)
  law : (n : ℕ) → ((k : Fin n) → ∀ i, Signal k i) →
    FiniteDistribution (∀ i, Signal n i)

/-- A stationary device draws the same private signal law independently at
every stage. -/
structure StationaryDevice (G : PaperGame ι) where
  Signal : ι → Type
  signalFintype : ∀ i, Fintype (Signal i)
  signalDecidableEq : ∀ i, DecidableEq (Signal i)
  law : FiniteDistribution (∀ i, Signal i)

/-- Every stationary device is autonomous with history-independent laws. -/
def StationaryDevice.toAutonomous (device : G.StationaryDevice) :
    G.AutonomousDevice where
  Signal := fun _ => device.Signal
  signalFintype := fun _ => device.signalFintype
  signalDecidableEq := fun _ => device.signalDecidableEq
  law := fun _ _ => device.law

/-- A state is absorbing when every pure action keeps the state fixed. -/
def IsAbsorbingState (state : G.State) : Prop :=
  ∀ action, (G.transition state action).prob state = 1

/-- Recursive games have zero stage payoff at every nonabsorbing state. -/
def IsRecursive : Prop :=
  ∀ state, ¬G.IsAbsorbingState state →
    ∀ action who, G.stagePayoff state action who = 0

/-- Positive games have strictly positive stage payoff at absorbing states. -/
def IsPositive : Prop :=
  ∀ state, G.IsAbsorbingState state →
    ∀ action who, 0 < G.stagePayoff state action who

/-- The class used in Theorem 2.4. -/
def IsPositiveRecursive : Prop := G.IsPositive ∧ G.IsRecursive

/-- A stationary profile is fully mixed. -/
def FullyMixed (x : G.StationaryProfile) : Prop :=
  ∀ state who action, 0 < (x state who).prob action

/-- Positive transition edge of the stationary Markov chain. -/
def SupportEdge (x : G.StationaryProfile) (source target : G.State) : Prop :=
  0 < G.mixedTransitionProbability source (x source) target

/-- Reachability inside a state set by positive transition edges. -/
def ReachesWithin (x : G.StationaryProfile) (states : Finset G.State)
    (source target : G.State) : Prop :=
  Relation.ReflTransGen
    (fun s t => s ∈ states ∧ t ∈ states ∧ G.SupportEdge x s t)
    source target

/-- Stability under a stationary profile. -/
def StableUnder (x : G.StationaryProfile) (states : Finset G.State) : Prop :=
  ∀ source ∈ states,
    G.mixedTransitionMass source (x source) states = 1

/-- A finite closed communicating class of the stationary Markov chain. -/
def IsErgodicSetUnder (x : G.StationaryProfile)
    (states : Finset G.State) : Prop :=
  states.Nonempty ∧ G.StableUnder x states ∧
    ∀ source ∈ states, ∀ target ∈ states,
      G.ReachesWithin x states source target

/-- The absorbing reduction used at the start of Section 5.3: under every
fully mixed profile, each ergodic set is one absorbing state. -/
def FullyMixedErgodicReduction : Prop :=
  ∀ x : G.StationaryProfile, G.FullyMixed x →
    ∀ states : Finset G.State, G.IsErgodicSetUnder x states →
      ∃ state, states = {state} ∧ G.IsAbsorbingState state

/-- A profile is absorbing when every nonempty closed set contains an
absorbing state.  For a finite chain this is equivalent to almost-sure
absorption from every initial state. -/
def IsAbsorbingProfile (x : G.StationaryProfile) : Prop :=
  ∀ states : Finset G.State, states.Nonempty → G.StableUnder x states →
    ∃ state ∈ states, G.IsAbsorbingState state

/-- Correct stationary evaluation equation (paper equation (32)): the value
is harmonic under the transition kernel.  No stage-payoff term is added. -/
def StationaryHarmonic (x : G.StationaryProfile)
    (value : G.State → ι → ℝ) : Prop :=
  ∀ state who,
    (∑ next : G.State,
      G.mixedTransitionProbability state (x state) next * value next who) =
      value state who

/-- Boundary values at absorbing states.  This formulation permits the
absorbing payoff to depend on the stationary action used there. -/
def StationaryBoundary (x : G.StationaryProfile)
    (value : G.State → ι → ℝ) : Prop :=
  ∀ state, G.IsAbsorbingState state →
    ∀ who, value state who = G.mixedStagePayoff state (x state) who

/-- The stationary expected-undiscounted evaluation used in Section 5. -/
def IsStationaryEvaluation (x : G.StationaryProfile)
    (value : G.State → ι → ℝ) : Prop :=
  G.IsAbsorbingProfile x ∧ G.StationaryHarmonic x value ∧
    G.StationaryBoundary x value

/-! ## Communicating sets and exits (Section 3.4) -/

/-- Support enlargement, the paper's notion of a perturbation. -/
def IsSupportPerturbation (y x : G.StationaryProfile) : Prop :=
  ∀ state who action,
    0 < (x state who).prob action → 0 < (y state who).prob action

/-- The paper's communicating-set condition, stated in support language. -/
def CommunicatesUnder (x : G.StationaryProfile)
    (states : Finset G.State) : Prop :=
  states.Nonempty ∧
    ∀ target ∈ states,
      ∃ y : G.StationaryProfile,
        G.IsSupportPerturbation y x ∧ G.StableUnder y states ∧
          ∀ source ∈ states, G.ReachesWithin y states source target

/-- Pure actions of exactly the coalition `coalition`. -/
abbrev CoalitionAction (coalition : Finset ι) :=
  (who : {i // i ∈ coalition}) → G.Action who.1

/-- Pure actions of the outsiders. -/
abbrev OutsiderAction (coalition : Finset ι) :=
  (who : {i // i ∉ coalition}) → G.Action who.1

/-- Combine a coalition action and an outsider action without storing
irrelevant outsider coordinates in the exit itself. -/
def combineCoalitionAction (coalition : Finset ι)
    (inside : G.CoalitionAction coalition)
    (outside : G.OutsiderAction coalition) : G.JointAction :=
  fun who => by
    by_cases h : who ∈ coalition
    · exact inside ⟨who, h⟩
    · exact outside ⟨who, h⟩

/-- Product probability of an outsider action. -/
def outsiderProbability (x : G.ProductMixedAction) (coalition : Finset ι)
    (outside : G.OutsiderAction coalition) : ℝ := by
  classical
  exact ∏ who : {i // i ∉ coalition},
    (x who.1).prob (outside who)

/-- Transition probability when the coalition action is fixed and outsiders
use their components of `x`. -/
def coalitionTransitionProbability (state : G.State)
    (x : G.ProductMixedAction) (coalition : Finset ι)
    (inside : G.CoalitionAction coalition) (next : G.State) : ℝ := by
  classical
  exact ∑ outside : G.OutsiderAction coalition,
    G.outsiderProbability x coalition outside *
      (G.transition state
        (G.combineCoalitionAction coalition inside outside)).prob next

/-- Transition mass of a state set under a coalition action. -/
def coalitionTransitionMass (state : G.State) (x : G.ProductMixedAction)
    (coalition : Finset ι) (inside : G.CoalitionAction coalition)
    (states : Finset G.State) : ℝ := by
  classical
  exact ∑ next ∈ states,
    G.coalitionTransitionProbability state x coalition inside next

/-- Restrict a coalition action to a subcoalition. -/
def restrictCoalitionAction {small large : Finset ι}
    (hsub : small ⊆ large) (action : G.CoalitionAction large) :
    G.CoalitionAction small :=
  fun who => action ⟨who.1, hsub who.2⟩

/-- The coalition action on the singleton `{who}`. -/
def singletonCoalitionAction (who : ι) (action : G.Action who) :
    G.CoalitionAction {who} :=
  fun member => by
    rcases member with ⟨player, hplayer⟩
    simp only [Finset.mem_singleton] at hplayer
    subst player
    exact action

/-- Definition 3.5.  An exit stores `(s, aᴸ)` relative to the fixed outsider
profile; outsiders are not arbitrary data and hence cannot duplicate exits. -/
structure Exit (x : G.StationaryProfile) (states : Finset G.State) where
  state : G.State
  state_mem : state ∈ states
  coalition : Finset ι
  coalition_nonempty : coalition.Nonempty
  action : G.CoalitionAction coalition
  leaves :
    0 < G.coalitionTransitionMass state (x state) coalition action
      (Finset.univ \ states)
  minimal :
    ∀ (small : Finset ι) (hsub : small ⊆ coalition),
      small ≠ coalition →
        G.coalitionTransitionMass state (x state) small
          (G.restrictCoalitionAction hsub action)
          (Finset.univ \ states) = 0

namespace Exit

variable {G}
variable {x : G.StationaryProfile} {states : Finset G.State}

/-- The transition law `q_e`. -/
def transitionProbability (exit : G.Exit x states) (next : G.State) : ℝ :=
  G.coalitionTransitionProbability exit.state (x exit.state)
    exit.coalition exit.action next

/-- Probability that the exit action actually leaves the set. -/
def outsideMass (exit : G.Exit x states) : ℝ :=
  G.coalitionTransitionMass exit.state (x exit.state)
    exit.coalition exit.action (Finset.univ \ states)

/-- A unilateral exit of player `who`. -/
def IsUnilateral (exit : G.Exit x states) (who : ι) : Prop :=
  exit.coalition = {who}

/-- Continuation payoff `q_e γ`. -/
def continuationValue (exit : G.Exit x states)
    (value : G.State → ι → ℝ) (who : ι) : ℝ := by
  classical
  exact ∑ next : G.State, exit.transitionProbability next * value next who

end Exit

/-- Numerator in equation (5). -/
def inducedExitNumerator {x : G.StationaryProfile}
    {states : Finset G.State}
    (distribution : FiniteDistribution (G.Exit x states))
    (next : G.State) : ℝ :=
  (distribution.support.map fun exit =>
    distribution.prob exit * exit.transitionProbability next).sum

/-- Denominator in equation (5), the probability that the selected exit
action actually leaves the communicating set. -/
def inducedExitDenominator {x : G.StationaryProfile}
    {states : Finset G.State}
    (distribution : FiniteDistribution (G.Exit x states)) : ℝ :=
  (distribution.support.map fun exit =>
    distribution.prob exit * exit.outsideMass).sum

/-- Equation (5), extended by zero on `C`.  Its support is therefore contained
in `S \ C`, as required for the induced Markov chain and Proposition 3.8. -/
def inducedExitStateProbability {x : G.StationaryProfile}
    {states : Finset G.State}
    (distribution : FiniteDistribution (G.Exit x states))
    (next : G.State) : ℝ := by
  classical
  exact if next ∈ states then 0 else
    G.inducedExitNumerator distribution next /
      G.inducedExitDenominator distribution

@[simp]
theorem inducedExitStateProbability_of_mem {x : G.StationaryProfile}
    {states : Finset G.State}
    (distribution : FiniteDistribution (G.Exit x states))
    {next : G.State} (hnext : next ∈ states) :
    G.inducedExitStateProbability distribution next = 0 := by
  simp [inducedExitStateProbability, hnext]

/-- Equation (5) is normalized on the complement.  This elementary finite
sum proof is left open in the future audit. -/
theorem inducedExitStateProbability_total {x : G.StationaryProfile}
    {states : Finset G.State}
    (distribution : FiniteDistribution (G.Exit x states)) :
    (∑ next : G.State,
      G.inducedExitStateProbability distribution next) = 1 := by
  sorry

/-- The induced chain (7).  A block state uses its conditioned exit law;
other states use the stationary transition law. -/
def inducedKernel {κ : Type*} [Fintype κ]
    (x : G.StationaryProfile) (block : κ → Finset G.State)
    (blockOf : G.State → Option κ)
    (exitDistribution : ∀ k, FiniteDistribution (G.Exit x (block k)))
    (source target : G.State) : ℝ :=
  match blockOf source with
  | none => G.mixedTransitionProbability source (x source) target
  | some k => G.inducedExitStateProbability (exitDistribution k) target

/-- A numerical finite kernel is absorbing relative to the game's absorbing
states when every nonempty closed set contains one. -/
def KernelIsAbsorbing (kernel : G.State → G.State → ℝ) : Prop :=
  ∀ states : Finset G.State, states.Nonempty →
    (∀ source ∈ states,
      (∑ target ∈ states, kernel source target) = 1) →
    ∃ state ∈ states, G.IsAbsorbingState state

/-- The seven hypotheses of Proposition 3.8, without hiding any of them in
opaque proposition fields.  The mediated-equilibrium conclusion awaits the
extended-game semantics. -/
def Proposition3_8Hypotheses {κ : Type*} [Fintype κ]
    (value minmax : G.State → ι → ℝ) (x : G.StationaryProfile)
    (block : κ → Finset G.State) (blockOf : G.State → Option κ)
    (exitDistribution : ∀ k, FiniteDistribution (G.Exit x (block k))) : Prop :=
  let kernel := G.inducedKernel x block blockOf exitDistribution
  G.KernelIsAbsorbing kernel ∧
  G.StationaryHarmonic x value ∧
  (∀ state who action,
    (∑ next : G.State,
      G.coalitionTransitionProbability state (x state) {who}
        (G.singletonCoalitionAction who action)
        next * value next who) ≤ value state who) ∧
  G.StationaryBoundary x value ∧
  (∀ state who, minmax state who ≤ value state who) ∧
  (∀ k state, state ∈ block k →
    ∀ who,
      (∑ next : G.State,
        G.inducedExitStateProbability (exitDistribution k) next *
          value next who) = value state who) ∧
  (∀ k,
    ((∀ exit, exit ∈ (exitDistribution k).support →
        0 < (exitDistribution k).prob exit →
        ∀ who, exit.IsUnilateral who →
          ∀ state, state ∈ block k →
            exit.continuationValue value who = value state who) ∨
      (∀ exit, exit ∈ (exitDistribution k).support →
        0 < (exitDistribution k).prob exit →
          ∃ who, exit.IsUnilateral who))) ∧
  (∀ k who (first second : G.Exit x (block k)),
    Exit.IsUnilateral first who → Exit.IsUnilateral second who →
      first ∈ (exitDistribution k).support →
      0 < (exitDistribution k).prob first →
      (∀ state, state ∈ block k →
        Exit.continuationValue first value who ≤ value state who) ∧
      Exit.continuationValue second value who ≤
        Exit.continuationValue first value who)

/-! ## The cleaning operation and equations (19)--(21) -/

/-- Transition probability under a correlated joint-action law. -/
def correlatedTransitionProbability (state : G.State)
    (actionLaw : FiniteDistribution G.JointAction) (next : G.State) : ℝ :=
  (actionLaw.support.map fun action =>
    actionLaw.prob action * (G.transition state action).prob next).sum

/-- Transition mass under a correlated joint-action law. -/
def correlatedTransitionMass (state : G.State)
    (actionLaw : FiniteDistribution G.JointAction)
    (states : Finset G.State) : ℝ := by
  classical
  exact ∑ next ∈ states,
    G.correlatedTransitionProbability state actionLaw next

/-- States with the same min--max vector as `state`. -/
def equalValueClass (value : G.State → ι → ℝ) (state : G.State) :
    Finset G.State := by
  classical
  exact Finset.univ.filter fun next => ∀ who, value next who = value state who

/-- The target set `(S \ C_s) ∪ S̄` used in equations (14)--(21). -/
def changingTargetSet (value : G.State → ι → ℝ)
    (marked : Finset G.State) (state : G.State) : Finset G.State :=
  (Finset.univ \ G.equalValueClass value state) ∪ marked

/-- The first bad-action set `B₁`. -/
def initialBadActions (value : G.State → ι → ℝ)
    (marked : Finset G.State) (state : G.State) :
    Finset G.JointAction := by
  classical
  exact Finset.univ.filter fun action =>
    0 < ∑ next ∈ G.changingTargetSet value marked state,
      (G.transition state action).prob next

/-- The scale `ε^(1/(2|A|))` from Definition 4.2 and Lemma 4.3. -/
def cleaningScale (epsilon : ℝ) : ℝ :=
  Real.rpow epsilon
    ((1 : ℝ) / (2 * (Fintype.card G.JointAction : ℝ)))

/-- One closure step `B_n ↦ B_{n+1}`. -/
def badActionClosureStep (actionLaw : FiniteDistribution G.JointAction)
    (epsilon : ℝ) (bad : Finset G.JointAction) : Finset G.JointAction := by
  classical
  exact bad ∪ Finset.univ.filter fun action =>
    ∃ witness ∈ bad,
      actionLaw.prob action ≤
        actionLaw.prob witness / G.cleaningScale epsilon

/-- Iteration of the bad-action closure. -/
def badActionClosureAux (actionLaw : FiniteDistribution G.JointAction)
    (epsilon : ℝ) : ℕ → Finset G.JointAction → Finset G.JointAction
  | 0, bad => bad
  | n + 1, bad =>
      badActionClosureAux actionLaw epsilon n
        (G.badActionClosureStep actionLaw epsilon bad)

/-- The stationary closure `B_∞ = B_|A|`. -/
def badActionClosure (actionLaw : FiniteDistribution G.JointAction)
    (epsilon : ℝ) (initial : Finset G.JointAction) :
    Finset G.JointAction :=
  G.badActionClosureAux actionLaw epsilon
    (Fintype.card G.JointAction) initial

/-- Surviving mass after deleting `B_∞`. -/
def cleanedMass (actionLaw : FiniteDistribution G.JointAction)
    (bad : Finset G.JointAction) : ℝ := by
  classical
  exact ∑ action : G.JointAction,
    if action ∈ bad then 0 else actionLaw.prob action

/-- The paper's cleaned and normalized probability.  Lemma 4.3 proves the
denominator positive before this expression is used. -/
def cleanedProbability (actionLaw : FiniteDistribution G.JointAction)
    (bad : Finset G.JointAction) (action : G.JointAction) : ℝ := by
  classical
  exact if action ∈ bad then 0 else
    actionLaw.prob action / G.cleanedMass actionLaw bad

/-- The marginal probability of player `who` receiving action `own`. -/
def playerMarginal (actionLaw : FiniteDistribution G.JointAction)
    (who : ι) (own : G.Action who) : ℝ := by
  classical
  exact (actionLaw.support.map fun action =>
    if action who = own then actionLaw.prob action else 0).sum

abbrev OtherAction (who : ι) :=
  (other : {j // j ≠ who}) → G.Action other.1

/-- Combine one recommended action with all opponents' actions. -/
def combineOwnAndOthers (who : ι) (own : G.Action who)
    (others : G.OtherAction who) : G.JointAction :=
  fun player => by
    by_cases h : player = who
    · subst player
      exact own
    · exact others ⟨player, h⟩

/-- Conditional probability over opponents' actions, given a recommendation. -/
def conditionalOtherProbability (actionLaw : FiniteDistribution G.JointAction)
    (who : ι) (own : G.Action who) (others : G.OtherAction who) : ℝ :=
  actionLaw.prob (G.combineOwnAndOthers who own others) /
    G.playerMarginal actionLaw who own

/-- A pointwise formulation of the paper's correlated-distance bound. -/
def CorrelatedDistanceLe
    (left right : FiniteDistribution G.JointAction) (bound : ℝ) : Prop :=
  ∀ who own others,
    0 < left.prob (G.combineOwnAndOthers who own others) →
      |G.conditionalOtherProbability left who own others -
        G.conditionalOtherProbability right who own others| ≤ bound

/-- The normalized cleaned law, available after Lemma 4.3 establishes
positive surviving mass. -/
def cleanedDistribution (actionLaw : FiniteDistribution G.JointAction)
    (bad : Finset G.JointAction)
    (hpositive : 0 < G.cleanedMass actionLaw bad) :
    FiniteDistribution G.JointAction := by
  classical
  refine
    { support := actionLaw.support.filter fun action => action ∉ bad
      nodup := actionLaw.nodup.filter _
      prob := G.cleanedProbability actionLaw bad
      nonnegative := ?_
      zero_off_support := ?_
      total := ?_ }
  · intro action
    sorry
  · intro action haction
    sorry
  · sorry

/-- Concrete semantic content of Lemma 4.3.  There are no placeholder
`isPaperCleaning` fields: the deleted set and normalization are the formulas
above. -/
def Lemma4_3Core (value : G.State → ι → ℝ)
    (marked : Finset G.State) (state : G.State)
    (actionLaw : FiniteDistribution G.JointAction) (epsilon : ℝ) : Prop :=
  let initial := G.initialBadActions value marked state
  let bad := G.badActionClosure actionLaw epsilon initial
  ∃ hpositive : 0 < G.cleanedMass actionLaw bad,
    G.CorrelatedDistanceLe
      (G.cleanedDistribution actionLaw bad hpositive)
      actionLaw
      ((Fintype.card G.JointAction : ℝ) * G.cleaningScale epsilon) ∧
    (∀ next ∈ G.changingTargetSet value marked state,
      (∑ action : G.JointAction,
        G.cleanedProbability actionLaw bad action *
          (G.transition state action).prob next) = 0)

/-- `n`-step transition probability of a numerical finite kernel. -/
def kernelProbabilityAfter (kernel : G.State → G.State → ℝ) :
    ℕ → G.State → G.State → ℝ
  | 0, source, target => if source = target then 1 else 0
  | n + 1, source, target =>
      ∑ middle : G.State,
        kernel source middle *
          kernelProbabilityAfter kernel n middle target

/-- Expected next value under a numerical kernel. -/
def kernelExpectedValue (kernel : G.State → G.State → ℝ)
    (value : G.State → ι → ℝ) (state : G.State) (who : ι) : ℝ :=
  ∑ next : G.State, kernel state next * value next who

/-- Probability that the value vector differs after exactly `steps` moves. -/
def valueChangeProbability (kernel : G.State → G.State → ℝ)
    (value : G.State → ι → ℝ) (steps : ℕ) (state : G.State) : ℝ := by
  classical
  exact ∑ next ∈ Finset.univ.filter
      (fun next => ∃ who, value next who ≠ value state who),
    G.kernelProbabilityAfter kernel steps state next

/-- Equation (19): nonnegative drift on `S̄` and a uniformly positive chance
of a value change within at most `|S|` block steps. -/
def Equation19 (kernel : G.State → G.State → ℝ)
    (value : G.State → ι → ℝ) (marked : Finset G.State)
    (omega : ℝ) : Prop :=
  ∀ state ∈ marked,
    (∀ who, value state who ≤
      G.kernelExpectedValue kernel value state who) ∧
    ∃ steps, 1 ≤ steps ∧ steps ≤ Fintype.card G.State ∧
      omega ≤ G.valueChangeProbability kernel value steps state

/-- Equation (20): the value vector is constant after a good-state block. -/
def Equation20 (kernel : G.State → G.State → ℝ)
    (value : G.State → ι → ℝ) (good : Finset G.State) : Prop :=
  ∀ state ∈ good, ∀ next,
    0 < kernel state next → ∀ who, value next who = value state who

/-- Equation (21): controlled negative drift on `S₂` and a change probability
at least `ε`. -/
def Equation21 (kernel : G.State → G.State → ℝ)
    (value : G.State → ι → ℝ) (residual : Finset G.State)
    (epsilon error : ℝ) : Prop :=
  ∀ state ∈ residual,
    (∀ who,
      value state who - error ≤
        G.kernelExpectedValue kernel value state who) ∧
    epsilon ≤ G.valueChangeProbability kernel value 1 state

/-- The finite closed-class part of Lemma 4.5.  The almost-sure convergence
and expected-visit bounds require the path measure, which is not yet defined
in this partial file. -/
def EveryClosedClassIsGood (kernel : G.State → G.State → ℝ)
    (good : Finset G.State) : Prop :=
  ∀ states : Finset G.State, states.Nonempty →
    (∀ source ∈ states,
      (∑ target ∈ states, kernel source target) = 1) →
    states ⊆ good

/-! ## Eventual exit laws and graph asymptotics (Section 5) -/

/-- A set is transient under `x` when every nonempty subset has a positive
one-step escape from at least one of its states. -/
def IsTransientUnder (x : G.StationaryProfile)
    (states : Finset G.State) : Prop :=
  ∀ nonempty : Finset G.State, nonempty.Nonempty → nonempty ⊆ states →
    ∃ state ∈ nonempty,
      G.mixedTransitionMass state (x state) nonempty < 1

/-- Raw data of a `B`-graph: one action and successor for each state of `B`. -/
abbrev GraphData (states : Finset G.State) :=
  (state : {s // s ∈ states}) → G.JointAction × G.State

/-- The deterministic successor relation of a graph. -/
def GraphStep {states : Finset G.State} (graph : G.GraphData states)
    (source target : G.State) : Prop :=
  ∃ hsource : source ∈ states,
    target = (graph ⟨source, hsource⟩).2

/-- The graph path from `source` exits at `target`. -/
def GraphEndsAt {states : Finset G.State} (graph : G.GraphData states)
    (source target : G.State) : Prop :=
  target ∉ states ∧
    Relation.TransGen (G.GraphStep graph) source target

/-- The two defining conditions of a `B`-graph. -/
def IsExitGraph {states : Finset G.State}
    (graph : G.GraphData states) : Prop :=
  (∀ state : {s // s ∈ states},
    0 < (G.transition state.1 (graph state).1).prob (graph state).2) ∧
  ∀ state : {s // s ∈ states},
    ∃ target, G.GraphEndsAt graph state.1 target

/-- Graph weight (26). -/
def graphWeight (x : G.StationaryProfile) {states : Finset G.State}
    (graph : G.GraphData states) : ℝ := by
  classical
  exact ∏ state : {s // s ∈ states},
    G.productProbability (x state.1) (graph state).1 *
      (G.transition state.1 (graph state).1).prob (graph state).2

/-- Numerator in the Freidlin--Wentzell graph formula (27). -/
def graphExitNumerator (x : G.StationaryProfile)
    (states : Finset G.State) (source target : G.State) : ℝ := by
  classical
  exact ∑ graph : G.GraphData states,
    if G.IsExitGraph graph ∧ G.GraphEndsAt graph source target then
      G.graphWeight x graph
    else 0

/-- Denominator in the graph formula (27). -/
def graphExitDenominator (x : G.StationaryProfile)
    (states : Finset G.State) : ℝ := by
  classical
  exact ∑ graph : G.GraphData states,
    if G.IsExitGraph graph then G.graphWeight x graph else 0

/-- Eventual first-exit law for one stationary profile.  Formula (27) is
valid under the explicit transience hypothesis used by its consumers. -/
def stationaryExitLaw (x : G.StationaryProfile)
    (states : Finset G.State) (source target : G.State) : ℝ :=
  G.graphExitNumerator x states source target /
    G.graphExitDenominator x states

/-- Formula (27) may be used only together with transience.  The supplied
`exitProbability` is the eventual first-exit law, not a finite-horizon event. -/
def SatisfiesGraphExitFormula (x : G.StationaryProfile)
    (states : Finset G.State)
    (exitProbability : G.State → G.State → ℝ) : Prop :=
  G.IsTransientUnder x states ∧
  ∀ source, source ∈ states →
    ∀ target, target ∉ states →
      exitProbability source target =
        G.stationaryExitLaw x states source target

/-- The correct two-level asymptotic exit law: for each profile take its
*eventual* first-exit law, then let the profile index tend to infinity. -/
def HasAsymptoticExitLaw (profiles : ℕ → G.StationaryProfile)
    (states : Finset G.State) (limitLaw : G.State → G.State → ℝ) : Prop :=
  (∀ n, G.IsTransientUnder (profiles n) states) ∧
  ∀ source, source ∈ states →
    ∀ target, target ∉ states →
      Tendsto
        (fun n => G.stationaryExitLaw (profiles n) states source target)
        atTop (nhds (limitLaw source target))

/-- A graph uses an exit exactly when its coalition coordinates are `aᴸ`,
its outsider coordinates lie in the support of `x⁻ᴸ`, and the arrow leaves
`C`. -/
def GraphUsesExit {x : G.StationaryProfile}
    {states : Finset G.State} (graph : G.GraphData states)
    (exit : G.Exit x states) : Prop :=
  let arrow := graph ⟨exit.state, exit.state_mem⟩
  arrow.2 ∉ states ∧
  (∀ who, ∀ hwho : who ∈ exit.coalition,
    arrow.1 who = exit.action ⟨who, hwho⟩) ∧
  (∀ who, who ∉ exit.coalition →
    0 < (x exit.state who).prob (arrow.1 who))

/-- A maximal graph has no competing graph with asymptotically unbounded
relative weight. -/
def IsMaximalGraph (profiles : ℕ → G.StationaryProfile)
    {states : Finset G.State} (graph : G.GraphData states) : Prop :=
  G.IsExitGraph graph ∧
  ∀ other : G.GraphData states, G.IsExitGraph other →
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ᶠ n in atTop,
        G.graphWeight (profiles n) other ≤
          bound * G.graphWeight (profiles n) graph

/-- Correct support criterion for the limiting first-used-exit law.  It does
not use the invalid diagonal event “exit within `n` under profile `n`.” -/
def ExitHasPositiveAsymptoticWeight
    (profiles : ℕ → G.StationaryProfile) (limitProfile : G.StationaryProfile)
    {states : Finset G.State} (exit : G.Exit limitProfile states) : Prop :=
  ∃ graph : G.GraphData states,
    G.IsMaximalGraph profiles graph ∧ G.GraphUsesExit graph exit

/-! ## Constrained fixed point (Section 5.3) -/

/-- The constraint set `X_ε`. -/
def IsEpsilonConstrained (epsilon : ℝ) (x : G.StationaryProfile) : Prop :=
  ∀ state who action, epsilon ^ 2 ≤ (x state who).prob action

/-- Explicit feasibility condition for `X_ε`. -/
def ConstraintFeasible (epsilon : ℝ) : Prop :=
  ∀ who,
    (Fintype.card (G.Action who) : ℝ) * epsilon ^ 2 ≤ 1

/-- Continuation payoff from a pure unilateral action. -/
def unilateralContinuation (value : G.State → ι → ℝ)
    (x : G.StationaryProfile) (state : G.State) (who : ι)
    (action : G.Action who) : ℝ :=
  ∑ next : G.State,
    G.coalitionTransitionProbability state (x state) {who}
      (G.singletonCoalitionAction who action)
      next * value next who

/-- Best continuation payoff in (30). -/
def bestUnilateralContinuation (value : G.State → ι → ℝ)
    (x : G.StationaryProfile) (state : G.State) (who : ι) : ℝ :=
  sSup (Set.range fun action : G.Action who =>
    G.unilateralContinuation value x state who action)

/-- Continuation cost (30). -/
def continuationCost (value : G.State → ι → ℝ)
    (x : G.StationaryProfile) (state : G.State) (who : ι)
    (action : G.Action who) : ℝ :=
  G.bestUnilateralContinuation value x state who -
    G.unilateralContinuation value x state who action

/-- Fixed-point equation (31), stated without pretending that it maps into
`X_ε` for arbitrary `ε`. -/
def SatisfiesApproximateBestReplyEquation (epsilon : ℝ)
    (value : G.State → ι → ℝ) (x : G.StationaryProfile) : Prop :=
  ∀ state who action,
    (x state who).prob action =
      Real.rpow epsilon (G.continuationCost value x state who action) /
        (∑ alternative : G.Action who,
          Real.rpow epsilon
            (G.continuationCost value x state who alternative))

/-- Faithful quantifiers for the Section 5.3 fixed-point construction.
The paper asserts the construction only for sufficiently small `ε`, after
restricting to positive recursive games and making the absorbing reduction. -/
def ConstrainedFixedPointClaim : Prop :=
  G.IsPositiveRecursive → G.FullyMixedErgodicReduction →
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 →
        G.ConstraintFeasible epsilon ∧
        ∃ x : G.StationaryProfile, ∃ value : G.State → ι → ℝ,
          G.IsEpsilonConstrained epsilon x ∧
          G.IsStationaryEvaluation x value ∧
          G.SatisfiesApproximateBestReplyEquation epsilon value x

end PaperGame

end Literature.SolanAndVieille2002b
