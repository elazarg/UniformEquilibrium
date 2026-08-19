import Mathlib

noncomputable section

open scoped BigOperators
open Filter

/-!
# E. Solan and N. Vieille, “Correlated Equilibrium in Stochastic Games” (2002)

Primary locator: *Games and Economic Behavior* 38 (2002), 362--399.
DOI: `10.1006/game.2001.0887`.

This file follows the paper in order.  Its finite stochastic game, private
signal devices, histories, deviations, communicating sets, exits, and graph
objects are paper-local.  In particular, private correlation is not replaced
by public correlation, and Theorem 2.4 retains the paper's assertion that one
stationary device works for every approximation error.

The remaining `sorry`s are the paper's substantive arguments.  Each is
preceded by the missing mathematical ingredient; no `sorry` abbreviates a
change of definition or a dropped quantifier.
-/

namespace Literature.SolanAndVieille2002a

/-! ## Finite distributions -/

/-- A probability distribution with explicitly finite support. -/
structure FiniteDistribution (α : Type) where
  atoms : Finset α
  prob : α → ℝ
  nonnegative : ∀ a, 0 ≤ prob a
  zero_off_atoms : ∀ a, a ∉ atoms → prob a = 0
  total : ∑ a in atoms, prob a = 1

namespace FiniteDistribution

variable {α β : Type}

/-- The positive-probability support. -/
def support (d : FiniteDistribution α) : Set α :=
  {a | 0 < d.prob a}

/-- Expectation under a finite distribution. -/
def expectation (d : FiniteDistribution α) (f : α → ℝ) : ℝ :=
  ∑ a in d.atoms, d.prob a * f a

/-- Point mass at one element. -/
noncomputable def pure (chosen : α) : FiniteDistribution α := by
  classical
  refine
    { atoms := {chosen}
      prob := fun a => if a = chosen then 1 else 0
      nonnegative := ?_
      zero_off_atoms := ?_
      total := ?_ }
  · intro a
    split_ifs <;> norm_num
  · intro a ha
    have hne : a ≠ chosen := by simpa using ha
    simp [hne]
  · simp

/-- Conditional deletion and renormalization.  The stored finite atom
set is retained; removed atoms receive probability zero. -/
noncomputable def conditionAway (d : FiniteDistribution α)
    (removed : Finset α)
    (hpositive : 0 < ∑ a in d.atoms, if a ∈ removed then 0 else d.prob a) :
    FiniteDistribution α := by
  classical
  let mass : ℝ :=
    ∑ a in d.atoms, if a ∈ removed then 0 else d.prob a
  have hmass : mass ≠ 0 := ne_of_gt hpositive
  refine
    { atoms := d.atoms
      prob := fun a =>
        (if a ∈ removed then 0 else d.prob a) / mass
      nonnegative := ?_
      zero_off_atoms := ?_
      total := ?_ }
  · intro a
    apply div_nonneg
    · split_ifs
      · exact le_rfl
      · exact d.nonnegative a
    · exact le_of_lt hpositive
  · intro a ha
    rw [d.zero_off_atoms a ha]
    split_ifs <;> simp
  · change
      (∑ a in d.atoms,
        (if a ∈ removed then 0 else d.prob a) / mass) = 1
    rw [Finset.sum_div]
    change mass / mass = 1
    exact div_self hmass

@[simp]
theorem conditionAway_removed (d : FiniteDistribution α)
    (removed : Finset α)
    (hpositive : 0 < ∑ a in d.atoms, if a ∈ removed then 0 else d.prob a)
    {a : α} (ha : a ∈ removed) :
    (d.conditionAway removed hpositive).prob a = 0 := by
  simp [conditionAway, ha]

end FiniteDistribution

/-! ## Section 2: the model and correlation devices -/

abbrev Payoff (ι : Type) := ι → ℝ

/-- The finite stochastic game of Section 2. -/
structure PaperGame (ι : Type) [Fintype ι] [DecidableEq ι] where
  State : Type
  stateFintype : Fintype State
  Action : ι → Type
  actionFintype : ∀ i, Fintype (Action i)
  transition : State → (∀ i, Action i) → FiniteDistribution State
  stagePayoff : State → (∀ i, Action i) → Payoff ι
  payoffBound : ∀ state action who, |stagePayoff state action who| ≤ 1

attribute [instance] PaperGame.stateFintype PaperGame.actionFintype

namespace PaperGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

abbrev JointAction := ∀ i, G.Action i
abbrev MixedAction := ∀ i, FiniteDistribution (G.Action i)
abbrev StationaryProfile := G.State → G.MixedAction
abbrev StatePayoff := G.State → Payoff ι

/-- Public finite history: the initial state followed by realized
`(action,next-state)` pairs. -/
structure History where
  initial : G.State
  stages : List (G.JointAction × G.State)

/-- Number of completed stages. -/
def History.length (history : G.History) : ℕ :=
  history.stages.length

/-- Current state after the finite history. -/
def History.current (history : G.History) : G.State :=
  match history.stages.getLast? with
  | none => history.initial
  | some stage => stage.2

/-- One-state history. -/
def initialHistory (state : G.State) : G.History where
  initial := state
  stages := []

/-- Append one realized action and transition. -/
def extendHistory (history : G.History) (action : G.JointAction)
    (next : G.State) : G.History where
  initial := history.initial
  stages := history.stages ++ [(action, next)]

@[simp]
theorem length_initialHistory (state : G.State) :
    (G.initialHistory state).length = 0 := by
  rfl

@[simp]
theorem length_extendHistory (history : G.History)
    (action : G.JointAction) (next : G.State) :
    (G.extendHistory history action next).length = history.length + 1 := by
  simp [History.length, extendHistory]

@[simp]
theorem current_initialHistory (state : G.State) :
    (G.initialHistory state).current = state := by
  rfl

@[simp]
theorem current_extendHistory (history : G.History)
    (action : G.JointAction) (next : G.State) :
    (G.extendHistory history action next).current = next := by
  simp [History.current, extendHistory]

/-- Probability of a pure action combination under independent mixing. -/
noncomputable def productProbability (x : G.MixedAction)
    (action : G.JointAction) : ℝ :=
  ∏ who, (x who).prob (action who)

/-- Mixed transition probability `q(next | state,x)`. -/
noncomputable def mixedTransitionProbability (state : G.State)
    (x : G.MixedAction) (next : G.State) : ℝ :=
  ∑ action : G.JointAction,
    G.productProbability x action * (G.transition state action).prob next

/-- Mixed one-stage payoff. -/
noncomputable def mixedStagePayoff (state : G.State)
    (x : G.MixedAction) (who : ι) : ℝ :=
  ∑ action : G.JointAction,
    G.productProbability x action * G.stagePayoff state action who

/-- Expected continuation value `q_{state,x} value`. -/
noncomputable def mixedContinuationValue (state : G.State)
    (x : G.MixedAction) (value : G.State → ℝ) : ℝ :=
  ∑ next : G.State,
    G.mixedTransitionProbability state x next * value next

/-- Replace one player's pure action. -/
def replaceAction (action : G.JointAction) (who : ι)
    (choice : G.Action who) : G.JointAction :=
  Function.update action who choice

/-- Replace one player's mixed action. -/
def replaceMixedAction (x : G.MixedAction) (who : ι)
    (choice : FiniteDistribution (G.Action who)) : G.MixedAction :=
  Function.update x who choice

/-- Behavioral strategy in the base game. -/
abbrev BehaviorStrategy (who : ι) :=
  G.History → FiniteDistribution (G.Action who)

/-- Behavioral profile in the base game. -/
abbrev BehaviorProfile := ∀ who, G.BehaviorStrategy who

/-- Correlated profile `H → Delta(A)`. -/
abbrev CorrelatedProfile := G.History → FiniteDistribution G.JointAction

/-- Product probability selected by a behavioral profile. -/
noncomputable def behaviorActionProbability (profile : G.BehaviorProfile)
    (history : G.History) (action : G.JointAction) : ℝ :=
  ∏ who, (profile who history).prob (action who)

/-- Expected total payoff in the next finite number of stages. -/
noncomputable def behaviorTotalPayoffFrom (profile : G.BehaviorProfile)
    (history : G.History) : ℕ → ι → ℝ
  | 0, _ => 0
  | horizon + 1, who =>
      ∑ action : G.JointAction,
        G.behaviorActionProbability profile history action *
          (G.stagePayoff history.current action who +
            ∑ next : G.State,
              (G.transition history.current action).prob next *
                behaviorTotalPayoffFrom G profile
                  (G.extendHistory history action next) horizon who)

/-- Expected finite average payoff. -/
noncomputable def behaviorAveragePayoffFrom (profile : G.BehaviorProfile)
    (history : G.History) (horizon : ℕ) (who : ι) : ℝ :=
  (horizon : ℝ)⁻¹ *
    G.behaviorTotalPayoffFrom profile history horizon who

/-- Expected payoff at one future stage. -/
noncomputable def behaviorStagePayoffFrom (profile : G.BehaviorProfile)
    (history : G.History) : ℕ → ι → ℝ
  | 0, who =>
      ∑ action : G.JointAction,
        G.behaviorActionProbability profile history action *
          G.stagePayoff history.current action who
  | delay + 1, who =>
      ∑ action : G.JointAction,
        G.behaviorActionProbability profile history action *
          ∑ next : G.State,
            (G.transition history.current action).prob next *
              behaviorStagePayoffFrom G profile
                (G.extendHistory history action next) delay who

/-- Normalized `lambda`-discounted payoff. -/
noncomputable def behaviorDiscountedPayoffFrom
    (profile : G.BehaviorProfile) (history : G.History)
    (discount : ℝ) (who : ι) : ℝ :=
  ∑' delay : ℕ,
    discount * (1 - discount) ^ delay *
      G.behaviorStagePayoffFrom profile history delay who

/-- Expected total payoff under a correlated profile. -/
noncomputable def correlatedTotalPayoffFrom
    (profile : G.CorrelatedProfile) (history : G.History) : ℕ → ι → ℝ
  | 0, _ => 0
  | horizon + 1, who =>
      ∑ action in (profile history).atoms,
        (profile history).prob action *
          (G.stagePayoff history.current action who +
            ∑ next : G.State,
              (G.transition history.current action).prob next *
                correlatedTotalPayoffFrom G profile
                  (G.extendHistory history action next) horizon who)

/-- Expected finite average under a correlated profile. -/
noncomputable def correlatedAveragePayoffFrom
    (profile : G.CorrelatedProfile) (history : G.History)
    (horizon : ℕ) (who : ι) : ℝ :=
  (horizon : ℝ)⁻¹ *
    G.correlatedTotalPayoffFrom profile history horizon who

/-- Marginal recommendation law of one player. -/
noncomputable def correlatedMarginal
    (law : FiniteDistribution G.JointAction) (who : ι) :
    FiniteDistribution (G.Action who) := by
  classical
  refine
    { atoms := Finset.univ
      prob := fun choice =>
        ∑ action in law.atoms,
          if action who = choice then law.prob action else 0
      nonnegative := ?_
      zero_off_atoms := ?_
      total := ?_ }
  · intro choice
    exact Finset.sum_nonneg fun action _ => by
      split_ifs
      · exact law.nonnegative action
      · exact le_rfl
  · intro choice hout
    simp at hout
  · calc
      (∑ choice : G.Action who,
          ∑ action in law.atoms,
            if action who = choice then law.prob action else 0) =
          ∑ action in law.atoms,
            ∑ choice : G.Action who,
              if action who = choice then law.prob action else 0 := by
                rw [Finset.sum_comm]
      _ = ∑ action in law.atoms, law.prob action := by
        apply Finset.sum_congr rfl
        intro action _
        simp
      _ = 1 := law.total

/-- Expected state value after `delay` stages. -/
noncomputable def behaviorExpectedStateValueFrom
    (profile : G.BehaviorProfile) (history : G.History) :
    ℕ → (G.State → ℝ) → ℝ
  | 0, value => value history.current
  | delay + 1, value =>
      ∑ action : G.JointAction,
        G.behaviorActionProbability profile history action *
          ∑ next : G.State,
            (G.transition history.current action).prob next *
              behaviorExpectedStateValueFrom G profile
                (G.extendHistory history action next) delay value

end PaperGame

/-- Heterogeneous joint-signal histories `M_1 × ... × M_n`. -/
def JointSignalHistory {ι : Type} (Signal : ℕ → ι → Type) : ℕ → Type
  | 0 => PUnit
  | n + 1 => JointSignalHistory Signal n × (∀ i, Signal n i)

/-- One player's private projection of a signal history. -/
def PrivateSignalHistory {ι : Type} (Signal : ℕ → ι → Type)
    (who : ι) : ℕ → Type
  | 0 => PUnit
  | n + 1 => PrivateSignalHistory Signal who n × Signal n who

/-- Project a joint signal history to player `who`. -/
def privateSignalHistory {ι : Type} (Signal : ℕ → ι → Type)
    (who : ι) : ∀ {n}, JointSignalHistory Signal n →
      PrivateSignalHistory Signal who n
  | 0, _ => PUnit.unit
  | n + 1, history =>
      (privateSignalHistory Signal who history.1, history.2 who)

/-- Definition 2.1: autonomous private correlation device. -/
structure AutonomousDevice {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : PaperGame ι) where
  Signal : ℕ → ι → Type
  signalFintype : ∀ n i, Fintype (Signal n i)
  law : ∀ n, JointSignalHistory Signal n →
    FiniteDistribution (∀ i, Signal n i)

attribute [instance] AutonomousDevice.signalFintype

namespace AutonomousDevice

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {G : PaperGame ι} (device : AutonomousDevice G)

/-- Behavioral strategy in the extended game.  The equality proof enforces
that the public and signal histories have the same stage. -/
abbrev Strategy (who : ι) :=
  ∀ n, (history : G.History), history.length = n →
    PrivateSignalHistory device.Signal who n → device.Signal n who →
      FiniteDistribution (G.Action who)

/-- Profile in the extended game. -/
abbrev Profile := ∀ who, device.Strategy who

/-- Probability of a joint action after one signal realization. -/
noncomputable def actionProbability (profile : device.Profile) (n : ℕ)
    (history : G.History) (hlength : history.length = n)
    (signals : JointSignalHistory device.Signal n)
    (current : ∀ i, device.Signal n i) (action : G.JointAction) : ℝ :=
  ∏ who,
    (profile who n history hlength
      (privateSignalHistory device.Signal who signals) (current who)).prob
        (action who)

/-- Expected total payoff in the next finite number of stages in `G(device)`. -/
noncomputable def totalPayoffFrom (profile : device.Profile) :
    ∀ n, (history : G.History), history.length = n →
      JointSignalHistory device.Signal n → ℕ → ι → ℝ
  | n, history, hlength, signals, 0, _ => 0
  | n, history, hlength, signals, horizon + 1, who =>
      ∑ current in (device.law n signals).atoms,
        (device.law n signals).prob current *
          ∑ action : G.JointAction,
            device.actionProbability profile n history hlength signals
                current action *
              (G.stagePayoff history.current action who +
                ∑ next : G.State,
                  (G.transition history.current action).prob next *
                    totalPayoffFrom device profile (n + 1)
                      (G.extendHistory history action next)
                      (by simpa [hlength] using
                        G.length_extendHistory history action next)
                      (signals, current) horizon who)

/-- Expected payoff at one future stage in `G(device)`. -/
noncomputable def stagePayoffFrom (profile : device.Profile) :
    ∀ n, (history : G.History), history.length = n →
      JointSignalHistory device.Signal n → ℕ → ι → ℝ
  | n, history, hlength, signals, 0, who =>
      ∑ current in (device.law n signals).atoms,
        (device.law n signals).prob current *
          ∑ action : G.JointAction,
            device.actionProbability profile n history hlength signals
                current action *
              G.stagePayoff history.current action who
  | n, history, hlength, signals, delay + 1, who =>
      ∑ current in (device.law n signals).atoms,
        (device.law n signals).prob current *
          ∑ action : G.JointAction,
            device.actionProbability profile n history hlength signals
                current action *
              ∑ next : G.State,
                (G.transition history.current action).prob next *
                  stagePayoffFrom device profile (n + 1)
                    (G.extendHistory history action next)
                    (by simpa [hlength] using
                      G.length_extendHistory history action next)
                    (signals, current) delay who

/-- `gamma_n(device,state,profile)`. -/
noncomputable def horizonAveragePayoff (profile : device.Profile)
    (initial : G.State) (horizon : ℕ) (who : ι) : ℝ :=
  (horizon : ℝ)⁻¹ *
    device.totalPayoffFrom profile 0 (G.initialHistory initial) rfl
      PUnit.unit horizon who

/-- `gamma_lambda(device,state,profile)`. -/
noncomputable def discountedPayoff (profile : device.Profile)
    (initial : G.State) (discount : ℝ) (who : ι) : ℝ :=
  ∑' delay : ℕ,
    discount * (1 - discount) ^ delay *
      device.stagePayoffFrom profile 0 (G.initialHistory initial) rfl
        PUnit.unit delay who

/-- Unilateral replacement of one extended-game strategy. -/
def updateProfile (profile : device.Profile) (who : ι)
    (deviation : device.Strategy who) : device.Profile :=
  Function.update profile who deviation

/-- Epsilon equilibrium of the finite average-payoff game. -/
def IsHorizonEpsilonEquilibrium (profile : device.Profile)
    (initial : G.State) (horizon : ℕ) (epsilon : ℝ) : Prop :=
  ∀ who (deviation : device.Strategy who),
    device.horizonAveragePayoff
        (device.updateProfile profile who deviation) initial horizon who ≤
      device.horizonAveragePayoff profile initial horizon who + epsilon

/-- Epsilon equilibrium of the normalized discounted game. -/
def IsDiscountedEpsilonEquilibrium (profile : device.Profile)
    (initial : G.State) (discount epsilon : ℝ) : Prop :=
  ∀ who (deviation : device.Strategy who),
    device.discountedPayoff
        (device.updateProfile profile who deviation) initial discount who ≤
      device.discountedPayoff profile initial discount who + epsilon

end AutonomousDevice

/-- Definition 2.1: stationary private correlation device. -/
structure StationaryDevice {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : PaperGame ι) where
  Signal : ι → Type
  signalFintype : ∀ i, Fintype (Signal i)
  law : FiniteDistribution (∀ i, Signal i)

attribute [instance] StationaryDevice.signalFintype

namespace StationaryDevice

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {G : PaperGame ι} (device : StationaryDevice G)

/-- A stationary device as the autonomous device with an i.i.d. signal law. -/
def toAutonomous : AutonomousDevice G where
  Signal _ i := device.Signal i
  signalFintype _ i := device.signalFintype i
  law _ _ := device.law

@[simp]
theorem toAutonomous_law (n : ℕ)
    (history : JointSignalHistory device.toAutonomous.Signal n) :
    device.toAutonomous.law n history = device.law := by
  rfl

end StationaryDevice

namespace PaperGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- A state is absorbing when no action can leave it. -/
def IsAbsorbingState (state : G.State) : Prop :=
  ∀ action, (G.transition state action).prob state = 1

/-- A recursive game has zero daily payoff in every nonabsorbing state. -/
def IsRecursive : Prop :=
  ∀ state, ¬G.IsAbsorbingState state →
    ∀ action who, G.stagePayoff state action who = 0

/-- A positive game has strictly positive daily payoffs at absorbing states. -/
def IsPositive : Prop :=
  ∀ state, G.IsAbsorbingState state →
    ∀ action who, 0 < G.stagePayoff state action who

/-- One device/profile realizes one target in all long finite games and all
small-discount games. -/
def RealizesUniformTargetWithDevice (target : G.StatePayoff)
    (epsilon : ℝ) (device : AutonomousDevice G)
    (profile : device.Profile) : Prop :=
  ∃ horizonThreshold : ℕ, ∃ discountThreshold : ℝ,
    0 < discountThreshold ∧ discountThreshold < 1 ∧
      (∀ initial horizon, horizonThreshold ≤ horizon →
        device.IsHorizonEpsilonEquilibrium profile initial horizon epsilon ∧
          ∀ who,
            |device.horizonAveragePayoff profile initial horizon who -
                target initial who| ≤ epsilon) ∧
      ∀ initial discount, 0 < discount → discount ≤ discountThreshold →
        device.IsDiscountedEpsilonEquilibrium
          profile initial discount epsilon ∧
          ∀ who,
            |device.discountedPayoff profile initial discount who -
                target initial who| ≤ epsilon

/-- Definition 2.2: autonomous correlated equilibrium payoff. -/
def IsAutonomousCorrelatedEquilibriumPayoff
    (target : G.StatePayoff) : Prop :=
  ∀ epsilon, 0 < epsilon →
    ∃ device : AutonomousDevice G, ∃ profile : device.Profile,
      G.RealizesUniformTargetWithDevice target epsilon device profile

/-- Definition 2.2: stationary correlated equilibrium payoff. -/
def IsStationaryCorrelatedEquilibriumPayoff
    (target : G.StatePayoff) : Prop :=
  ∀ epsilon, 0 < epsilon →
    ∃ device : StationaryDevice G,
      ∃ profile : device.toAutonomous.Profile,
        G.RealizesUniformTargetWithDevice
          target epsilon device.toAutonomous profile

/-- Theorem 2.4's stronger fixed-device quantifier. -/
def HasFixedStationaryCorrelationDevice
    (target : G.StatePayoff) : Prop :=
  ∃ device : StationaryDevice G,
    ∀ epsilon, 0 < epsilon →
      ∃ profile : device.toAutonomous.Profile,
        G.RealizesUniformTargetWithDevice
          target epsilon device.toAutonomous profile

/-- A fixed stationary device is, in particular, a stationary correlated
payoff device at each error. -/
theorem isStationaryCorrelatedEquilibriumPayoff_of_fixedDevice
    {target : G.StatePayoff}
    (h : G.HasFixedStationaryCorrelationDevice target) :
    G.IsStationaryCorrelatedEquilibriumPayoff target := by
  obtain ⟨device, hdevice⟩ := h
  intro epsilon hepsilon
  obtain ⟨profile, hprofile⟩ := hdevice epsilon hepsilon
  exact ⟨device, profile, hprofile⟩

/-- Theorem 2.3, stated where it occurs in the paper. -/
def Theorem2_3Claim : Prop :=
  ∃ target : G.StatePayoff,
    G.IsAutonomousCorrelatedEquilibriumPayoff target

/-- Theorem 2.4, including independence of the stationary device from the
approximation error. -/
def Theorem2_4Claim : Prop :=
  G.IsPositive → G.IsRecursive →
    ∃ target : G.StatePayoff,
      G.HasFixedStationaryCorrelationDevice target

end PaperGame

/-! ## Section 3.1: stationary profiles and communication -/

namespace PaperGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- A stationary profile as a behavioral profile. -/
def stationaryBehaviorProfile (x : G.StationaryProfile) :
    G.BehaviorProfile :=
  fun who history => x history.current who

/-- Support inclusion: `y` is a perturbation of `x`. -/
def IsPerturbationOf (y x : G.StationaryProfile) : Prop :=
  ∀ state who action,
    0 < (x state who).prob action → 0 < (y state who).prob action

/-- Sup-coordinate closeness used for arbitrarily small perturbations. -/
def StationaryProfilesWithin (epsilon : ℝ)
    (x y : G.StationaryProfile) : Prop :=
  ∀ state who action,
    |(x state who).prob action - (y state who).prob action| < epsilon

/-- Stability of a finite state set under a stationary profile. -/
noncomputable def IsStableUnder (states : Finset G.State)
    (x : G.StationaryProfile) : Prop :=
  ∀ state, state ∈ states →
    (∑ next : G.State,
      if next ∈ states then
        G.mixedTransitionProbability state (x state) next else 0) = 1

/-- Probability of hitting a target in at most the stated number of steps. -/
noncomputable def stationaryHitWithin (x : G.StationaryProfile)
    (target : G.State) : G.State → ℕ → ℝ
  | state, 0 => if state = target then 1 else 0
  | state, steps + 1 =>
      if state = target then 1
      else
        ∑ next : G.State,
          G.mixedTransitionProbability state (x state) next *
            stationaryHitWithin G x target next steps

/-- Almost-sure reachability under a stationary profile. -/
def StationaryReachesAlmostSurely (x : G.StationaryProfile)
    (source target : G.State) : Prop :=
  Tendsto (fun steps => G.stationaryHitWithin x target source steps)
    atTop (nhds 1)

/-- Section 3.4.1: communication under a stationary profile. -/
def CommunicatesUnder (states : Finset G.State)
    (x : G.StationaryProfile) : Prop :=
  G.IsStableUnder states x ∧
    ∀ target, target ∈ states →
      ∃ y : G.StationaryProfile,
        G.IsPerturbationOf y x ∧ G.IsStableUnder states y ∧
          ∀ source, source ∈ states →
            G.StationaryReachesAlmostSurely y source target

/-- The paper's arbitrarily close communicating perturbation observation. -/
def CloseCommunicatingPerturbationClaim : Prop :=
  ∀ (states : Finset G.State) (x : G.StationaryProfile),
    G.CommunicatesUnder states x →
      ∀ epsilon, 0 < epsilon → ∀ target, target ∈ states →
        ∃ y : G.StationaryProfile,
          G.IsPerturbationOf y x ∧ G.IsStableUnder states y ∧
            G.StationaryProfilesWithin epsilon x y ∧
              ∀ source, source ∈ states →
                G.StationaryReachesAlmostSurely y source target

/-- The support perturbation is elementary, but its almost-sure hitting
preservation still needs a finite-chain proof in this paper-local encoding. -/
theorem closeCommunicatingPerturbation :
    G.CloseCommunicatingPerturbationClaim := by
  sorry

end PaperGame

/-! ## Section 3.2: the min--max value -/

namespace PaperGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- Replace one player's base-game strategy. -/
def updateBehaviorProfile (profile : G.BehaviorProfile) (who : ι)
    (deviation : G.BehaviorStrategy who) : G.BehaviorProfile :=
  Function.update profile who deviation

/-- Uniform min--max characterization in Section 3.2. -/
def IsUniformMinmaxValue (value : ι → G.State → ℝ) : Prop :=
  ∀ who state epsilon, 0 < epsilon →
    ∃ threshold : ℕ,
      (∃ punishment : G.BehaviorProfile,
        ∀ deviation : G.BehaviorStrategy who, ∀ horizon,
          threshold < horizon →
            G.behaviorAveragePayoffFrom
                (G.updateBehaviorProfile punishment who deviation)
                (G.initialHistory state) horizon who ≤
              value who state + epsilon) ∧
      ∀ opponents : G.BehaviorProfile,
        ∃ deviation : G.BehaviorStrategy who, ∀ horizon,
          threshold < horizon →
            value who state - epsilon ≤
              G.behaviorAveragePayoffFrom
                (G.updateBehaviorProfile opponents who deviation)
                (G.initialHistory state) horizon who

/-- Discounted min--max characterization. -/
def IsDiscountedMinmaxValue (discount : ℝ)
    (value : ι → G.State → ℝ) : Prop :=
  ∀ who state,
    (∃ punishment : G.BehaviorProfile,
      ∀ deviation : G.BehaviorStrategy who,
        G.behaviorDiscountedPayoffFrom
            (G.updateBehaviorProfile punishment who deviation)
            (G.initialHistory state) discount who ≤ value who state) ∧
    ∀ opponents : G.BehaviorProfile,
      ∃ deviation : G.BehaviorStrategy who,
        value who state ≤
          G.behaviorDiscountedPayoffFrom
            (G.updateBehaviorProfile opponents who deviation)
            (G.initialHistory state) discount who

/-- Bounded variation on `(0,1)`, in the partition form used by the paper. -/
def HasBoundedVariationOnUnitInterval (f : ℝ → ℝ) : Prop :=
  ∃ bound : ℝ, 0 ≤ bound ∧
    ∀ n (point : Fin (n + 1) → ℝ),
      (∀ k, 0 < point k ∧ point k < 1) →
      (∀ k : Fin n, point k.castSucc ≤ point k.succ) →
        ∑ k : Fin n,
          |f (point k.succ) - f (point k.castSucc)| ≤ bound

/-- Lemma 3.1: existence of uniform min--max values and convergence of the
bounded-variation discounted values. -/
def Lemma3_1Claim : Prop :=
  ∃ discountedValue : ℝ → ι → G.State → ℝ,
    ∃ value : ι → G.State → ℝ,
      (∀ discount, 0 < discount → discount < 1 →
        G.IsDiscountedMinmaxValue discount (discountedValue discount)) ∧
      G.IsUniformMinmaxValue value ∧
      (∀ who state,
        HasBoundedVariationOnUnitInterval
          (fun discount => discountedValue discount who state)) ∧
      ∀ who state,
        Tendsto (fun discount => discountedValue discount who state)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (value who state))

/-- The paper invokes Neyman's unpublished n-player extension of the
Mertens--Neyman theorem.  That result is not present in the dependencies. -/
theorem lemma3_1 : G.Lemma3_1Claim := by
  sorry

end PaperGame

/-! ## Section 3.3: mimicking and autonomous correlation -/

namespace PaperGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- A stage-`n` recommendation table, restricted to histories of length `n`. -/
abbrev RecommendationTable (n : ℕ) (who : ι) :=
  (history : G.History) → history.length = n → G.Action who

/-- Exact data of the first mimicking device. -/
structure FirstMimickingDeviceData (profile : G.CorrelatedProfile) where
  device : AutonomousDevice G
  decode : ∀ n who, device.Signal n who → G.RecommendationTable n who
  historyIndependent : ∀ n
      (first second : JointSignalHistory device.Signal n),
    device.law n first = device.law n second
  coordinateLaw : ∀ n
      (signalHistory : JointSignalHistory device.Signal n)
      (history : G.History) (hlength : history.length = n)
      (action : G.JointAction),
    (∑ signal in (device.law n signalHistory).atoms,
      if (fun who => decode n who (signal who) history hlength) = action then
        (device.law n signalHistory).prob signal else 0) =
      (profile history).prob action
  obedientProfile : device.Profile
  obeys : ∀ who n (history : G.History)
      (hlength : history.length = n)
      (past : PrivateSignalHistory device.Signal who n)
      (current : device.Signal n who) action,
    (obedientProfile who n history hlength past current).prob action =
      if action = decode n who current history hlength then 1 else 0
  averagePayoffEquality : ∀ initial horizon who,
    device.horizonAveragePayoff obedientProfile initial horizon who =
      G.correlatedAveragePayoffFrom profile
        (G.initialHistory initial) horizon who

/-- The second mimicking device additionally reveals the complete previous
recommendation table to every player. -/
structure SecondMimickingDeviceData (profile : G.CorrelatedProfile) where
  first : G.FirstMimickingDeviceData profile
  previousTable : ∀ n who,
    first.device.Signal (n + 1) who →
      (∀ player, G.RecommendationTable n player)
  revealsPrevious : ∀ n
      (past : JointSignalHistory first.device.Signal (n + 1))
      (current : ∀ i, first.device.Signal (n + 1) i),
    0 < (first.device.law (n + 1) past).prob current →
      ∀ observer₁ observer₂,
        previousTable n observer₁ (current observer₁) =
          previousTable n observer₂ (current observer₂)

/-- Section 3.3.1: both finite mimicking devices exist. -/
def MimickingDevicesClaim (profile : G.CorrelatedProfile) : Prop :=
  Nonempty (G.FirstMimickingDeviceData profile) ∧
    Nonempty (G.SecondMimickingDeviceData profile)

/-- This is a dependent finite-product construction over all stage-`n`
histories.  Its coordinate-marginal proof is not yet available as a reusable
finite-distribution lemma. -/
theorem mimickingDevices (profile : G.CorrelatedProfile) :
    G.MimickingDevicesClaim profile := by
  sorry

/-- Definition 3.2: uniform convergence of average payoffs in every subgame. -/
def AveragePayoffsConvergeTo (profile : G.CorrelatedProfile)
    (limitPayoff : G.History → Payoff ι) : Prop :=
  ∀ epsilon, 0 < epsilon →
    ∃ threshold : ℕ, ∀ history horizon,
      threshold ≤ horizon → ∀ who,
        |G.correlatedAveragePayoffFrom profile history horizon who -
            limitPayoff history who| ≤ epsilon

/-- Conditional probability of a full recommendation given one player's
recommended action. -/
noncomputable def conditionalRecommendationProbability
    (law : FiniteDistribution G.JointAction) (who : ι)
    (recommended : G.Action who) (action : G.JointAction) : ℝ :=
  if action who = recommended then
    law.prob action /
      (∑ candidate in law.atoms,
        if candidate who = recommended then law.prob candidate else 0)
  else 0

/-- Expected continuation target after obeying a recommendation. -/
noncomputable def conditionalContinuationTarget
    (profile : G.CorrelatedProfile)
    (limitPayoff : G.History → Payoff ι)
    (history : G.History) (who : ι)
    (recommended : G.Action who) : ℝ :=
  ∑ action in (profile history).atoms,
    G.conditionalRecommendationProbability
        (profile history) who recommended action *
      ∑ next : G.State,
        (G.transition history.current action).prob next *
          limitPayoff (G.extendHistory history action next) who

/-- Expected post-deviation min--max continuation. -/
noncomputable def conditionalDeviationMinmax
    (profile : G.CorrelatedProfile) (minmax : ι → G.State → ℝ)
    (history : G.History) (who : ι)
    (recommended deviation : G.Action who) : ℝ :=
  ∑ action in (profile history).atoms,
    G.conditionalRecommendationProbability
        (profile history) who recommended action *
      ∑ next : G.State,
        (G.transition history.current
          (G.replaceAction action who deviation)).prob next *
            minmax who next

/-- Definition 3.3: epsilon individual rationality. -/
def IsEpsilonIndividuallyRational (profile : G.CorrelatedProfile)
    (limitPayoff : G.History → Payoff ι)
    (minmax : ι → G.State → ℝ) (epsilon : ℝ) : Prop :=
  ∀ history recommendation,
    0 < (profile history).prob recommendation →
      ∀ who (deviation : G.Action who),
        G.conditionalDeviationMinmax profile minmax history who
            (recommendation who) deviation - epsilon ≤
          G.conditionalContinuationTarget
            profile limitPayoff history who (recommendation who)

/-- Theorem 3.4. -/
def Theorem3_4Claim : Prop :=
  ∀ minmax : ι → G.State → ℝ,
    G.IsUniformMinmaxValue minmax →
      (∀ epsilon, 0 < epsilon →
        ∃ profile : G.CorrelatedProfile,
          ∃ limitPayoff : G.History → Payoff ι,
            G.AveragePayoffsConvergeTo profile limitPayoff ∧
              G.IsEpsilonIndividuallyRational
                profile limitPayoff minmax epsilon) →
        ∃ target : G.StatePayoff,
          G.IsAutonomousCorrelatedEquilibriumPayoff target

/-- The proof needs the second mimicking device, first-deviation detection,
and a strategy splice to uniform min--max punishments in private histories.
That splice is not formalized in the current game semantics. -/
theorem theorem3_4 : G.Theorem3_4Claim := by
  sorry

end PaperGame

/-! ## Section 3.4: exits and the stationary sufficient condition -/

namespace PaperGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- Probability of a realized joint action when a coalition uses fixed pure
actions and the other players use `x`. -/
noncomputable def coalitionActionProbability
    (x : G.StationaryProfile) (state : G.State)
    (coalition : Finset ι) (fixed realized : G.JointAction) : ℝ :=
  ∏ who,
    if who ∈ coalition then
      if realized who = fixed who then 1 else 0
    else (x state who).prob (realized who)

/-- Transition under the coalition perturbation. -/
noncomputable def coalitionTransitionProbability
    (x : G.StationaryProfile) (state : G.State)
    (coalition : Finset ι) (fixed : G.JointAction)
    (next : G.State) : ℝ :=
  ∑ realized : G.JointAction,
    G.coalitionActionProbability x state coalition fixed realized *
      (G.transition state realized).prob next

/-- Probability that the coalition perturbation stays in `states`. -/
noncomputable def coalitionStayProbability
    (x : G.StationaryProfile) (states : Finset G.State)
    (state : G.State) (coalition : Finset ι)
    (fixed : G.JointAction) : ℝ :=
  ∑ next : G.State,
    if next ∈ states then
      G.coalitionTransitionProbability x state coalition fixed next else 0

/-- Candidate exit data. -/
structure ExitData where
  state : G.State
  coalition : Finset ι
  action : G.JointAction

/-- Definition 3.5: a minimal coalition perturbation that can leave `C`. -/
def IsExit (x : G.StationaryProfile) (states : Finset G.State)
    (exit : G.ExitData) : Prop :=
  exit.state ∈ states ∧ exit.coalition.Nonempty ∧
    G.coalitionStayProbability x states exit.state
        exit.coalition exit.action < 1 ∧
      ∀ smaller : Finset ι, smaller ⊂ exit.coalition →
        G.coalitionStayProbability x states exit.state
          smaller exit.action = 1

/-- The finite mathematical set `E(x,C)`, represented as a subtype. -/
abbrev Exit (x : G.StationaryProfile) (states : Finset G.State) :=
  {exit : G.ExitData // G.IsExit x states exit}

/-- A unilateral exit of player `who`. -/
def IsUnilateralExit {x : G.StationaryProfile}
    {states : Finset G.State} (exit : G.Exit x states)
    (who : ι) : Prop :=
  exit.1.coalition = {who}

/-- A joint exit. -/
def IsJointExit {x : G.StationaryProfile}
    {states : Finset G.State} (exit : G.Exit x states) : Prop :=
  2 ≤ exit.1.coalition.card

/-- Exit transition `q_e`. -/
noncomputable def exitTransitionProbability
    {x : G.StationaryProfile} {states : Finset G.State}
    (exit : G.Exit x states) (next : G.State) : ℝ :=
  G.coalitionTransitionProbability x exit.1.state
    exit.1.coalition exit.1.action next

/-- Equation (5): state law induced by a distribution over exits. -/
noncomputable def inducedExitStateProbability
    {x : G.StationaryProfile} {states : Finset G.State}
    (exitLaw : FiniteDistribution (G.Exit x states))
    (next : G.State) : ℝ :=
  (∑ exit in exitLaw.atoms,
      exitLaw.prob exit * G.exitTransitionProbability exit next) /
    (∑ exit in exitLaw.atoms,
      exitLaw.prob exit *
        (∑ outside : G.State,
          if outside ∈ states then 0
          else G.exitTransitionProbability exit outside))

/-- `mu gamma`, expected continuation under the induced state law. -/
noncomputable def inducedExitContinuationValue
    {x : G.StationaryProfile} {states : Finset G.State}
    (exitLaw : FiniteDistribution (G.Exit x states))
    (value : G.State → ℝ) : ℝ :=
  ∑ next : G.State,
    G.inducedExitStateProbability exitLaw next * value next

/-- `q_e gamma^i`, continuation value of one exit. -/
noncomputable def exitContinuationValue
    {x : G.StationaryProfile} {states : Finset G.State}
    (exit : G.Exit x states) (value : G.StatePayoff)
    (who : ι) : ℝ :=
  ∑ next : G.State,
    G.exitTransitionProbability exit next * value next who

/-- A behavior profile is an epsilon perturbation of `x`. -/
def IsBehaviorEpsilonPerturbation (profile : G.BehaviorProfile)
    (x : G.StationaryProfile) (epsilon : ℝ) : Prop :=
  ∀ history who action,
    |(profile who history).prob action -
        (x history.current who).prob action| < epsilon

/-- Probability of reaching a history event within bounded time. -/
noncomputable def behaviorEventWithinProbability
    (profile : G.BehaviorProfile) (event : G.History → Prop) :
    G.History → ℕ → ℝ
  | history, 0 => if event history then 1 else 0
  | history, steps + 1 =>
      if event history then 1
      else
        ∑ action : G.JointAction,
          G.behaviorActionProbability profile history action *
            ∑ next : G.State,
              (G.transition history.current action).prob next *
                behaviorEventWithinProbability G profile event
                  (G.extendHistory history action next) steps

/-- Lemma 3.6's recurrent scheduling property. -/
def RecurrentlySchedulesExitRows (profile : G.BehaviorProfile)
    (x : G.StationaryProfile) (states : Finset G.State) : Prop :=
  ∀ exit : G.Exit x states, ∀ cutoff : ℕ, ∀ source,
    source ∈ states →
      Tendsto
        (fun steps =>
          G.behaviorEventWithinProbability profile
            (fun history =>
              cutoff < history.length ∧
                history.current = exit.1.state ∧
                  ∀ who, profile who history = x history.current who)
            (G.initialHistory source) steps)
        atTop (nhds 1)

/-- Lemma 3.6. -/
def Lemma3_6Claim : Prop :=
  ∀ (x : G.StationaryProfile) (states : Finset G.State),
    G.CommunicatesUnder states x →
      ∀ epsilon, 0 < epsilon →
        ∃ profile : G.BehaviorProfile,
          G.IsBehaviorEpsilonPerturbation profile x epsilon ∧
            G.RecurrentlySchedulesExitRows profile x states

/-- The round-robin proof depends only on the close communicating
perturbations above, whose almost-sure hitting lemma remains open here. -/
theorem lemma3_6 : G.Lemma3_6Claim := by
  sorry

/-- Probability that the first state outside `states` is `target`, within a
bounded number of future stages. -/
noncomputable def firstExitAtWithin (profile : G.BehaviorProfile)
    (states : Finset G.State) (target : G.State) :
    G.History → ℕ → ℝ
  | history, 0 =>
      if history.current ∉ states ∧ history.current = target then 1 else 0
  | history, steps + 1 =>
      if history.current ∉ states then
        if history.current = target then 1 else 0
      else
        ∑ action : G.JointAction,
          G.behaviorActionProbability profile history action *
            ∑ next : G.State,
              (G.transition history.current action).prob next *
                firstExitAtWithin G profile states target
                  (G.extendHistory history action next) steps

/-- A profile realizes the state law induced by an exit distribution. -/
def RealizesExitStateLaw (profile : G.BehaviorProfile)
    {x : G.StationaryProfile} {states : Finset G.State}
    (exitLaw : FiniteDistribution (G.Exit x states)) : Prop :=
  ∀ source, source ∈ states → ∀ target, target ∉ states →
    Tendsto
      (fun steps =>
        G.firstExitAtWithin profile states target
          (G.initialHistory source) steps)
      atTop (nhds (G.inducedExitStateProbability exitLaw target))

/-- Lemma 3.7. -/
def Lemma3_7Claim : Prop :=
  ∀ (x : G.StationaryProfile) (states : Finset G.State),
    G.CommunicatesUnder states x →
      ∀ exitLaw : FiniteDistribution (G.Exit x states),
        ∀ epsilon, 0 < epsilon →
          ∃ profile : G.BehaviorProfile,
            G.IsBehaviorEpsilonPerturbation profile x epsilon ∧
              G.RealizesExitStateLaw profile exitLaw

/-- The paper's calibrated hazards give a short ratio proof once Lemma 3.6
supplies the recurrent schedule; that constructor is the missing premise. -/
theorem lemma3_7 : G.Lemma3_7Claim := by
  sorry

/-- Probability of occupying `target` at one stationary date. -/
noncomputable def stationaryStateProbabilityAt (x : G.StationaryProfile)
    (target : G.State) : G.State → ℕ → ℝ
  | source, 0 => if source = target then 1 else 0
  | source, time + 1 =>
      ∑ next : G.State,
        G.mixedTransitionProbability source (x source) next *
          stationaryStateProbabilityAt G x target next time

/-- Finite-state transience, expressed by finite expected total visits. -/
def IsTransientStateUnder (x : G.StationaryProfile)
    (state : G.State) : Prop :=
  ∀ source,
    Summable (fun time => G.stationaryStateProbabilityAt x state source time)

/-- Partition into communicating blocks and transient remainder. -/
structure CommunicatingPartition (x : G.StationaryProfile) where
  Block : Type
  blockFintype : Fintype Block
  block : Block → Finset G.State
  transient : Finset G.State
  pairwiseDisjoint : Set.PairwiseDisjoint Set.univ fun k => (block k : Set G.State)
  disjointTransient : ∀ k, Disjoint (block k) transient
  coversNonabsorbing : ∀ state, ¬G.IsAbsorbingState state →
    state ∈ transient ∨ ∃ k, state ∈ block k
  blocksCommunicate : ∀ k, G.CommunicatesUnder (block k) x
  transientStates : ∀ state, state ∈ transient →
    G.IsTransientStateUnder x state

attribute [instance] CommunicatingPartition.blockFintype

/-- Equation (7): kernel induced by stationary play on transient states and
an exit law on each communicating block. -/
noncomputable def inducedKernel {x : G.StationaryProfile}
    (partition : G.CommunicatingPartition x)
    (exitLaw : ∀ k, FiniteDistribution (G.Exit x (partition.block k)))
    (state next : G.State) : ℝ :=
  if hblock : ∃ k, state ∈ partition.block k then
    G.inducedExitStateProbability
      (exitLaw (Classical.choose hblock)) next
  else G.mixedTransitionProbability state (x state) next

/-- Hitting probability for a finite kernel. -/
noncomputable def kernelHitsAbsorbingWithin
    (kernel : G.State → G.State → ℝ) : G.State → ℕ → ℝ
  | state, 0 => if G.IsAbsorbingState state then 1 else 0
  | state, steps + 1 =>
      if G.IsAbsorbingState state then 1
      else
        ∑ next : G.State,
          kernel state next *
            kernelHitsAbsorbingWithin G kernel next steps

/-- The induced chain is a probability kernel and absorbs almost surely. -/
def IsAbsorbingKernel (kernel : G.State → G.State → ℝ) : Prop :=
  (∀ state next, 0 ≤ kernel state next) ∧
    (∀ state, ∑ next : G.State, kernel state next = 1) ∧
      ∀ state,
        Tendsto (fun steps => G.kernelHitsAbsorbingWithin kernel state steps)
          atTop (nhds 1)

/-- Proposition 3.8's seven hypotheses. -/
structure StationarySufficientData where
  target : G.StatePayoff
  x : G.StationaryProfile
  partition : G.CommunicatingPartition x
  exitLaw : ∀ k, FiniteDistribution (G.Exit x (partition.block k))
  minmax : ι → G.State → ℝ
  minmax_spec : G.IsUniformMinmaxValue minmax
  condition1 : G.IsAbsorbingKernel (G.inducedKernel partition exitLaw)
  condition2a : ∀ state who,
    G.mixedContinuationValue state (x state)
        (fun next => target next who) = target state who
  condition2b : ∀ state who (choice : G.Action who),
    G.mixedContinuationValue state
        (G.replaceMixedAction (x state) who
          (FiniteDistribution.pure choice))
        (fun next => target next who) ≤ target state who
  condition3 : ∀ state, G.IsAbsorbingState state →
    ∀ action who, target state who = G.stagePayoff state action who
  condition4 : ∀ state who, minmax who state ≤ target state who
  condition5 : ∀ k state, state ∈ partition.block k → ∀ who,
    G.inducedExitContinuationValue (exitLaw k)
        (fun next => target next who) = target state who
  condition6 : ∀ k,
    (∀ who (exit : G.Exit x (partition.block k)),
      G.IsUnilateralExit exit who → 0 < (exitLaw k).prob exit →
        ∀ state, state ∈ partition.block k →
          G.exitContinuationValue exit target who = target state who) ∨
    (∀ exit : G.Exit x (partition.block k),
      0 < (exitLaw k).prob exit →
        ∃ who, G.IsUnilateralExit exit who)
  condition7 : ∀ k who
      (supported other : G.Exit x (partition.block k)),
    G.IsUnilateralExit supported who →
      G.IsUnilateralExit other who →
        0 < (exitLaw k).prob supported →
          ∀ state, state ∈ partition.block k →
            G.exitContinuationValue other target who ≤
              G.exitContinuationValue supported target who ∧
            G.exitContinuationValue supported target who ≤ target state who

/-- Proposition 3.8. -/
def Proposition3_8Claim : Prop :=
  ∀ data : G.StationarySufficientData,
    G.IsStationaryCorrelatedEquilibriumPayoff data.target

/-- The joint-exit branch requires asymptotic frequency tests with uniform
false-detection bounds.  The cited tests have not been reconstructed for the
paper-local private-signal strategies. -/
theorem proposition3_8 : G.Proposition3_8Claim := by
  sorry

end PaperGame

/-! ## Section 4.1: the Mertens--Neyman profile -/

namespace PaperGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- Bellman inequality (8) for one player's history-dependent local discount. -/
def SatisfiesMertensNeymanBellman
    (g : ℝ → G.State → ℝ) (who : ι)
    (localDiscount : G.History → ℝ)
    (profile : G.BehaviorProfile) : Prop :=
  ∀ history,
    g (localDiscount history) history.current ≤
      ∑ action : G.JointAction,
        G.behaviorActionProbability profile history action *
          (localDiscount history * G.stagePayoff history.current action who +
            (1 - localDiscount history) *
              ∑ next : G.State,
                (G.transition history.current action).prob next *
                  g (localDiscount history) next)

/-- Conclusions (MN.2) and (MN.3), the parts used in this paper.  The paper
also proves almost-sure convergence of the local discounts to zero (MN.1),
but explicitly does not use it. -/
structure MertensNeymanGuarantees
    (g0 : G.State → ℝ) (who : ι)
    (profile : G.BehaviorProfile) (epsilon : ℝ) where
  futureLevel : ∀ history delay,
    g0 history.current - epsilon ≤
      G.behaviorExpectedStateValueFrom profile history delay g0
  longAverage : ∃ threshold : ℕ, ∀ history horizon,
    threshold ≤ horizon →
      g0 history.current - epsilon ≤
        G.behaviorAveragePayoffFrom profile history horizon who

/-- The bounded-variation Mertens--Neyman construction summarized before
(8). -/
def MertensNeymanConstructionClaim : Prop :=
  ∀ (g : ℝ → G.State → ℝ) (g0 : G.State → ℝ)
      (who : ι) (epsilon alpha : ℝ),
    0 < epsilon → 0 < alpha →
    (∀ state, HasBoundedVariationOnUnitInterval (fun l => g l state)) →
    (∀ state,
      Tendsto (fun discount => g discount state)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (g0 state))) →
      ∃ localDiscount : G.History → ℝ,
        (∀ history, 0 < localDiscount history ∧
          localDiscount history < alpha) ∧
        ∀ profile : G.BehaviorProfile,
          G.SatisfiesMertensNeymanBellman
              g who localDiscount profile →
            Nonempty (G.MertensNeymanGuarantees g0 who profile epsilon)

/-- The local-discount stopping estimate is the Mertens--Neyman theorem
itself; no bounded-variation version of it exists in Mathlib or this project. -/
theorem mertensNeymanConstruction :
    G.MertensNeymanConstructionClaim := by
  sorry

/-- Payoff of the auxiliary one-shot game `G(state,lambda-vector)`. -/
noncomputable def auxiliaryOneShotPayoff
    (discountedMinmax : ℝ → ι → G.State → ℝ)
    (state : G.State) (discount : ι → ℝ)
    (action : G.JointAction) (who : ι) : ℝ :=
  discount who * G.stagePayoff state action who +
    (1 - discount who) *
      ∑ next : G.State,
        (G.transition state action).prob next *
          discountedMinmax (discount who) who next

/-- Nash equilibrium of the auxiliary one-shot game. -/
def IsAuxiliaryOneShotNash
    (discountedMinmax : ℝ → ι → G.State → ℝ)
    (state : G.State) (discount : ι → ℝ)
    (x : G.MixedAction) : Prop :=
  ∀ who (choice : G.Action who),
    (∑ action : G.JointAction,
      G.productProbability x action *
        G.auxiliaryOneShotPayoff
          discountedMinmax state discount action who) ≥
    (∑ action : G.JointAction,
      G.productProbability x action *
        G.auxiliaryOneShotPayoff discountedMinmax state discount
          (G.replaceAction action who choice) who)

/-- Selection `x(state,lambda-vector)` of auxiliary one-shot equilibria. -/
def AuxiliaryEquilibriumSelection
    (discountedMinmax : ℝ → ι → G.State → ℝ)
    (selection : G.State → (ι → ℝ) → G.MixedAction) : Prop :=
  ∀ state discount,
    G.IsAuxiliaryOneShotNash
      discountedMinmax state discount (selection state discount)

/-- Equation (9): play the selected auxiliary equilibrium at the vector of
local discounts calculated separately by the players. -/
def IsMertensNeymanProfile
    (selection : G.State → (ι → ℝ) → G.MixedAction)
    (localDiscount : ι → G.History → ℝ)
    (profile : G.BehaviorProfile) : Prop :=
  ∀ history who,
    profile who history =
      selection history.current (fun player => localDiscount player history) who

/-- Section 4.1: the profile obtained from the auxiliary equilibria is
approximately individually rational with respect to the uniform min--max
vector. -/
def Section4_1Claim : Prop :=
  ∀ discountedMinmax : ℝ → ι → G.State → ℝ,
    ∀ minmax : ι → G.State → ℝ,
      (∀ discount, 0 < discount → discount < 1 →
        G.IsDiscountedMinmaxValue discount
          (discountedMinmax discount)) →
      (∀ who state,
        HasBoundedVariationOnUnitInterval
          (fun discount => discountedMinmax discount who state)) →
      (∀ who state,
        Tendsto (fun discount => discountedMinmax discount who state)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (minmax who state))) →
      ∀ epsilon, 0 < epsilon →
        ∃ profile : G.BehaviorProfile,
          ∃ selection localDiscount,
            G.AuxiliaryEquilibriumSelection discountedMinmax selection ∧
            G.IsMertensNeymanProfile selection localDiscount profile ∧
            ∀ who,
              Nonempty (G.MertensNeymanGuarantees
                (minmax who) who profile epsilon)

/-- This is the simultaneous application of the preceding construction to
all players.  It remains open because the Mertens--Neyman constructor does. -/
theorem section4_1 : G.Section4_1Claim := by
  sorry

end PaperGame

/-! ## Section 4.2: cyclic cleaning and convergence -/

namespace PaperGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- Coordinatewise convergence of mixed action profiles. -/
def MixedActionsTendTo (sequence : ℕ → G.MixedAction)
    (limit : G.MixedAction) : Prop :=
  ∀ who action,
    Tendsto (fun n => (sequence n who).prob action)
      atTop (nhds ((limit who).prob action))

/-- `X*(state)`: accumulation points as every local discount vanishes. -/
def XStar (selection : G.State → (ι → ℝ) → G.MixedAction)
    (state : G.State) : Set G.MixedAction :=
  {limit | ∃ discount : ℕ → ι → ℝ,
    (∀ who, Tendsto (fun n => discount n who) atTop (nhds 0)) ∧
      G.MixedActionsTendTo (fun n => selection state (discount n)) limit}

/-- State class `C_state` on which the whole min--max vector is equal. -/
def equalMinmaxClass (minmax : ι → G.State → ℝ)
    (state : G.State) : Finset G.State :=
  Finset.univ.filter fun other =>
    ∀ who, minmax who other = minmax who state

/-- Probability that a mixed action enters a finite state set. -/
noncomputable def mixedTransitionToSet (state : G.State)
    (x : G.MixedAction) (states : Finset G.State) : ℝ :=
  ∑ next : G.State,
    if next ∈ states then
      G.mixedTransitionProbability state x next else 0

/-- Increasing sequence `S-tilde_n`; index zero denotes the empty set. -/
noncomputable def changingMinmaxStates
    (selection : G.State → (ι → ℝ) → G.MixedAction)
    (minmax : ι → G.State → ℝ) : ℕ → Finset G.State
  | 0 => ∅
  | depth + 1 =>
      Finset.univ.filter fun state =>
        ∃ x, x ∈ G.XStar selection state ∧
          0 < G.mixedTransitionToSet state x
            ((G.equalMinmaxClass minmax state)ᶜ ∪
              changingMinmaxStates G selection minmax depth)

/-- Stabilized set `S-tilde = S-tilde_|S|`. -/
noncomputable def changingMinmaxSet
    (selection : G.State → (ι → ℝ) → G.MixedAction)
    (minmax : ι → G.State → ℝ) : Finset G.State :=
  G.changingMinmaxStates selection minmax (Fintype.card G.State)

/-- Definition 4.1: a good state for the chosen block length. -/
def IsGoodState
    (selection : G.State → (ι → ℝ) → G.MixedAction)
    (minmax : ι → G.State → ℝ) (profile : G.BehaviorProfile)
    (blockLength : ℕ) (epsilon : ℝ) (state : G.State) : Prop :=
  state ∉ G.changingMinmaxSet selection minmax ∧
    G.behaviorEventWithinProbability profile
      (fun history =>
        history.current ∉ G.equalMinmaxClass minmax state ∨
          history.current ∈ G.changingMinmaxSet selection minmax)
      (G.initialHistory state) (blockLength + 1) ≤ epsilon

/-- Definition 4.2: maximum change of conditional recommendation laws. -/
noncomputable def correlatedDistance
    (y x : FiniteDistribution G.JointAction) : ℝ :=
  sSup {distance : ℝ | ∃ who (recommended : G.Action who)
      (action : G.JointAction),
    0 < y.prob action ∧ action who = recommended ∧
      distance =
        |G.conditionalRecommendationProbability y who recommended action -
          G.conditionalRecommendationProbability x who recommended action|}

/-- Bad actions `B_1`. -/
noncomputable def initialBadActions
    (selection : G.State → (ι → ℝ) → G.MixedAction)
    (minmax : ι → G.State → ℝ) (state : G.State) :
    Finset G.JointAction :=
  Finset.univ.filter fun action =>
    0 < ∑ next : G.State,
      if next ∈
        (G.equalMinmaxClass minmax state)ᶜ ∪
          G.changingMinmaxSet selection minmax then
        (G.transition state action).prob next else 0

/-- Closure `B_n` used before renormalization. -/
noncomputable def badActionClosure
    (selection : G.State → (ι → ℝ) → G.MixedAction)
    (minmax : ι → G.State → ℝ) (state : G.State)
    (law : FiniteDistribution G.JointAction) (epsilon : ℝ) :
    ℕ → Finset G.JointAction
  | 0 => G.initialBadActions selection minmax state
  | depth + 1 =>
      let previous :=
        badActionClosure G selection minmax state law epsilon depth
      Finset.univ.filter fun action =>
        action ∈ previous ∨
          ∃ bad ∈ previous,
            law.prob action ≤
              law.prob bad /
                epsilon ^ ((2 * Fintype.card G.JointAction : ℝ)⁻¹)

/-- `B_infinity = B_|A|`. -/
noncomputable def badActionsInfinity
    (selection : G.State → (ι → ℝ) → G.MixedAction)
    (minmax : ι → G.State → ℝ) (state : G.State)
    (law : FiniteDistribution G.JointAction) (epsilon : ℝ) :
    Finset G.JointAction :=
  G.badActionClosure selection minmax state law epsilon
    (Fintype.card G.JointAction)

/-- Lemma 4.3: deletion is defined, is close in correlated distance, and
eliminates every bad transition. -/
def Lemma4_3Claim : Prop :=
  ∀ (selection : G.State → (ι → ℝ) → G.MixedAction)
      (minmax : ι → G.State → ℝ) (state : G.State)
      (law : FiniteDistribution G.JointAction) (epsilon : ℝ),
    0 < epsilon →
    G.mixedTransitionToSet state
      (fun who => G.correlatedMarginal law who)
      ((G.equalMinmaxClass minmax state)ᶜ ∪
        G.changingMinmaxSet selection minmax) ≤ epsilon →
    let removed :=
      G.badActionsInfinity selection minmax state law epsilon
    ∃ hmass : 0 < ∑ action in law.atoms,
        if action ∈ removed then 0 else law.prob action,
      let cleaned := law.conditionAway removed hmass
      G.correlatedDistance cleaned law ≤
          Fintype.card G.JointAction *
            epsilon ^ ((2 * Fintype.card G.JointAction : ℝ)⁻¹) ∧
        (∀ action, action ∈ removed → cleaned.prob action = 0) ∧
          ∀ action, 0 < cleaned.prob action →
            (∑ next : G.State,
              if next ∈
                (G.equalMinmaxClass minmax state)ᶜ ∪
                  G.changingMinmaxSet selection minmax then
                (G.transition state action).prob next else 0) = 0

/-- The finite conditional-probability telescoping estimate in Lemma 4.3
has not yet been isolated as a reusable distribution lemma. -/
theorem lemma4_3 : G.Lemma4_3Claim := by
  sorry

/-- Data specifying the paper's cleaning of one good `N0`-stage block. -/
structure GoodBlockCleaningData where
  selection : G.State → (ι → ℝ) → G.MixedAction
  minmax : ι → G.State → ℝ
  original : G.CorrelatedProfile
  cleaned : G.CorrelatedProfile
  initial : G.State
  blockLength : ℕ
  epsilon zeta : ℝ
  good : G.IsGoodState selection minmax
    (fun who history => G.correlatedMarginal (original history) who)
    blockLength epsilon initial
  zetaPositive : 0 < zeta
  isPaperCleaning : Prop

/-- Lemma 4.4. -/
def Lemma4_4Claim : Prop :=
  ∀ data : G.GoodBlockCleaningData,
    data.isPaperCleaning → ∀ who,
      |G.correlatedAveragePayoffFrom data.cleaned
          (G.initialHistory data.initial) data.blockLength who -
        G.correlatedAveragePayoffFrom data.original
          (G.initialHistory data.initial) data.blockLength who| <
        Fintype.card G.JointAction * Real.sqrt data.epsilon / data.zeta

/-- The proof is the paper's path coupling: the two laws agree until a
deleted action is selected.  A coupling theorem for these recursive
correlated profiles is not available. -/
theorem lemma4_4 : G.Lemma4_4Claim := by
  sorry

/-- Finite Markov kernel. -/
structure FiniteKernel where
  prob : G.State → G.State → ℝ
  nonnegative : ∀ state next, 0 ≤ prob state next
  total : ∀ state, ∑ next : G.State, prob state next = 1

/-- State distribution after a finite number of kernel steps. -/
noncomputable def kernelStateProbability (kernel : G.FiniteKernel)
    (target : G.State) : G.State → ℕ → ℝ
  | source, 0 => if source = target then 1 else 0
  | source, time + 1 =>
      ∑ next : G.State,
        kernel.prob source next *
          kernelStateProbability G kernel target next time

/-- Expected value after a finite number of kernel steps. -/
noncomputable def kernelExpectedValue (kernel : G.FiniteKernel)
    (value : G.State → ℝ) (source : G.State) (time : ℕ) : ℝ :=
  ∑ target : G.State,
    G.kernelStateProbability kernel target source time * value target

/-- Expected total visits to a finite state set. -/
noncomputable def kernelExpectedVisits (kernel : G.FiniteKernel)
    (states : Finset G.State) (source : G.State) : ℝ :=
  ∑' time : ℕ,
    ∑ target in states,
      G.kernelStateProbability kernel target source time

/-- Closed communicating class of a finite kernel. -/
def IsErgodicClass (kernel : G.FiniteKernel)
    (states : Finset G.State) : Prop :=
  states.Nonempty ∧
    (∀ state, state ∈ states → ∀ next,
      0 < kernel.prob state next → next ∈ states) ∧
    ∀ source, source ∈ states → ∀ target, target ∈ states →
      Tendsto
        (fun steps =>
          G.stationaryHitWithin
            (fun state _ =>
              { atoms := Finset.univ
                prob := kernel.prob state
                nonnegative := kernel.nonnegative state
                zero_off_atoms := by simp
                total := kernel.total state })
            target source steps)
        atTop (nhds 1)

/-- Quantitative hypotheses (19)--(21) for Lemma 4.5. -/
structure Lemma4_5Data where
  minmax : ι → G.State → ℝ
  changing good bad : Finset G.State
  kernel : G.FiniteKernel
  epsilon : ℝ
  epsilonPositive : 0 < epsilon
  partition : changing ∪ good ∪ bad = Finset.univ
  changingDrift : Prop
  goodConstancy : ∀ state, state ∈ good → ∀ next,
    0 < kernel.prob state next →
      ∀ who, minmax who next = minmax who state
  badDrift : Prop

/-- Lemma 4.5's four conclusions. -/
def Lemma4_5Claim : Prop :=
  ∀ data : G.Lemma4_5Data,
    data.changingDrift → data.badDrift →
      (∀ ergodic, G.IsErgodicClass data.kernel ergodic →
        ergodic ⊆ data.good) ∧
      (∀ source who,
        Summable fun time =>
          |G.kernelExpectedValue data.kernel (data.minmax who) source
              (time + 1) -
            G.kernelExpectedValue data.kernel (data.minmax who) source time|) ∧
      (∀ source,
        G.kernelExpectedVisits data.kernel
            (data.bad ∪ data.changing) source ≤
          data.epsilon ^
            (-((Fintype.card ι + 1) * Fintype.card G.State : ℤ))) ∧
      ∀ source,
        ∃ limit : Payoff ι,
          (∀ who,
            Tendsto
              (fun time =>
                G.kernelExpectedValue data.kernel
                  (data.minmax who) source time)
              atTop (nhds (limit who))) ∧
          ∀ who, data.minmax who source - data.epsilon ≤ limit who

/-- The lexicographic drift argument (23)--(25) is a quantitative finite
Markov-chain lemma not currently present in the library. -/
theorem lemma4_5 : G.Lemma4_5Claim := by
  sorry

/-- Theorem 2.3, proved in Section 4. -/
theorem theorem2_3 : G.Theorem2_3Claim := by
  sorry

end PaperGame

/-! ## Section 5.1: exit graphs -/

namespace PaperGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- A pure stationary action combination `a in A^S`. -/
abbrev PureStationaryAction := G.State → G.JointAction

/-- `x(a)`, probability of a pure stationary action combination. -/
noncomputable def stationaryPureProbability (x : G.StationaryProfile)
    (action : G.PureStationaryAction) : ℝ :=
  ∏ state, G.productProbability (x state) (action state)

/-- A `B`-graph. -/
structure ExitGraph (states : Finset G.State) where
  action : G.State → G.JointAction
  target : G.State → G.State
  positive : ∀ state, state ∈ states →
    0 < (G.transition state (action state)).prob (target state)
  eventuallyOutside : ∀ state, state ∈ states →
    ∃ steps : ℕ, (target^[steps]) state ∉ states

/-- A finite complete enumeration of all `B`-graphs. -/
structure ExitGraphEnumeration (states : Finset G.State) where
  graphs : Finset (G.ExitGraph states)
  complete : ∀ graph, graph ∈ graphs

/-- Equation (26): graph weight. -/
noncomputable def graphWeight {states : Finset G.State}
    (x : G.StationaryProfile) (graph : G.ExitGraph states) : ℝ :=
  ∏ state in states,
    G.productProbability (x state) (graph.action state) *
      (G.transition state (graph.action state)).prob (graph.target state)

/-- The graph path from `source` first exits at `target`. -/
def GraphEndsAt {states : Finset G.State}
    (graph : G.ExitGraph states) (source target : G.State) : Prop :=
  ∃ steps : ℕ,
    (∀ earlier, earlier < steps →
      (graph.target^[earlier]) source ∈ states) ∧
    (graph.target^[steps]) source = target ∧ target ∉ states

/-- Stationary first-exit law from `states`. -/
def IsStationaryExitLaw (x : G.StationaryProfile)
    (states : Finset G.State) (source : G.State)
    (law : G.State → ℝ) : Prop :=
  ∀ target, target ∉ states →
    Tendsto
      (fun steps =>
        G.firstExitAtWithin (G.stationaryBehaviorProfile x) states target
          (G.initialHistory source) steps)
      atTop (nhds (law target))

/-- Equation (27), the Freidlin--Wentzell graph formula. -/
def GraphExitFormulaClaim : Prop :=
  ∀ (states : Finset G.State) (enumeration : G.ExitGraphEnumeration states)
      (x : G.StationaryProfile) (source target : G.State)
      (law : G.State → ℝ),
    source ∈ states → target ∉ states →
    G.IsStationaryExitLaw x states source law →
      law target =
        (∑ graph in enumeration.graphs,
          if G.GraphEndsAt graph source target then
            G.graphWeight x graph else 0) /
        (∑ graph in enumeration.graphs, G.graphWeight x graph)

/-- Equation (27) is cited from Freidlin--Wentzell.  Its finite matrix-tree
proof is not reconstructed in the repository. -/
theorem graphExitFormula : G.GraphExitFormulaClaim := by
  sorry

end PaperGame

/-! ## Section 5.2: asymptotic ratios and maximal graphs -/

namespace PaperGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- An absorbing stationary profile with its undiscounted payoff vector. -/
structure AbsorbingStationaryEvaluation where
  profile : G.StationaryProfile
  value : G.StatePayoff
  absorbs : ∀ state,
    Tendsto
      (fun steps =>
        G.kernelHitsAbsorbingWithin
          (fun source next =>
            G.mixedTransitionProbability source (profile source) next)
          state steps)
      atTop (nhds 1)
  harmonic : ∀ state who,
    G.mixedStagePayoff state (profile state) who +
      G.mixedContinuationValue state (profile state)
        (fun next => value next who) = value state who
  averageConverges : ∀ state who,
    Tendsto
      (fun horizon =>
        G.behaviorAveragePayoffFrom
          (G.stationaryBehaviorProfile profile)
          (G.initialHistory state) horizon who)
      atTop (nhds (value state who))

/-- Asymptotic profile data satisfying the ratio subsequence extraction (28). -/
structure AsymptoticProfileData where
  epsilon : ℕ → ℝ
  epsilonPositive : ∀ n, 0 < epsilon n
  epsilonTendsToZero : Tendsto epsilon atTop (nhds 0)
  evaluation : ℕ → G.AbsorbingStationaryEvaluation
  supportIndependent : ∀ m n state who action,
    0 < ((evaluation m).profile state who).prob action ↔
      0 < ((evaluation n).profile state who).prob action
  ratioLimit : G.PureStationaryAction → G.PureStationaryAction → ENNReal
  ratiosConverge : ∀ first second,
    0 < G.stationaryPureProbability (evaluation 0).profile second →
      Tendsto
        (fun n =>
          ENNReal.ofReal
              (G.stationaryPureProbability (evaluation n).profile first) /
            ENNReal.ofReal
              (G.stationaryPureProbability (evaluation n).profile second))
        atTop (nhds (ratioLimit first second))
  limitProfile : G.StationaryProfile
  profileConverges : ∀ state who action,
    Tendsto
      (fun n => ((evaluation n).profile state who).prob action)
      atTop (nhds ((limitProfile state who).prob action))
  limitPayoff : G.StatePayoff
  payoffConverges : ∀ state who,
    Tendsto (fun n => (evaluation n).value state who)
      atTop (nhds (limitPayoff state who))
  exitLimit : Finset G.State → G.State → G.State → ℝ
  exitLawsConverge : ∀ states source target,
    source ∈ states → target ∉ states →
      Tendsto
        (fun n =>
          G.firstExitAtWithin
              (G.stationaryBehaviorProfile (evaluation n).profile)
              states target (G.initialHistory source) n)
        atTop (nhds (exitLimit states source target))

/-- Definition 5.1: communication under the asymptotic ratios `theta`. -/
def CommunicatesUnderTheta (data : G.AsymptoticProfileData)
    (states : Finset G.State) : Prop :=
  (∀ state, state ∈ states → ¬G.IsAbsorbingState state) ∧
    ∀ source, source ∈ states → ∀ target,
      target ∈ states → target ≠ source →
        data.exitLimit (states.erase target) source target = 1

/-- A graph is maximal when no competing graph has asymptotically infinite
weight relative to it. -/
def IsMaximalGraph (data : G.AsymptoticProfileData)
    {states : Finset G.State} (graph : G.ExitGraph states) : Prop :=
  ∀ other : G.ExitGraph states,
    ¬ Tendsto
      (fun n =>
        ENNReal.ofReal
            (G.graphWeight (data.evaluation n).profile other) /
          ENNReal.ofReal
            (G.graphWeight (data.evaluation n).profile graph))
      atTop atTop

/-- Lemma 5.2: only maximal graphs contribute to the limiting exit law. -/
def Lemma5_2Claim : Prop :=
  ∀ (data : G.AsymptoticProfileData) (states : Finset G.State)
      (enumeration : G.ExitGraphEnumeration states),
    G.CommunicatesUnderTheta data states →
      ∀ source, source ∈ states → ∀ target, target ∉ states →
        Tendsto
          (fun n =>
            (∑ graph in enumeration.graphs,
              if G.IsMaximalGraph data graph ∧
                  G.GraphEndsAt graph source target then
                G.graphWeight (data.evaluation n).profile graph else 0) /
              (∑ graph in enumeration.graphs,
                G.graphWeight (data.evaluation n).profile graph))
          atTop (nhds (data.exitLimit states source target))

/-- This is the finite-sum pruning of equation (27) with possibly infinite
extended-real action-probability ratios.  The needed ratio lemma is absent. -/
theorem lemma5_2 : G.Lemma5_2Claim := by
  sorry

/-- An exit is used by a graph when the graph's leaving arrow realizes that
coalition perturbation against supported opponent actions. -/
def GraphUsesExit (data : G.AsymptoticProfileData)
    {states : Finset G.State}
    (graph : G.ExitGraph states)
    (exit : G.Exit data.limitProfile states) : Prop :=
  graph.action exit.1.state = exit.1.action ∧
    graph.target exit.1.state ∉ states

/-- Equation (29) and the law `mu_(theta,C)` of the first exit used. -/
def FirstUsedExitLawClaim : Prop :=
  ∀ (data : G.AsymptoticProfileData) (states : Finset G.State),
    G.CommunicatesUnderTheta data states →
      ∀ source, source ∈ states →
        ∃ exitLaw : FiniteDistribution
            (G.Exit data.limitProfile states),
          (∀ exit,
            0 < exitLaw.prob exit ↔
              ∃ graph : G.ExitGraph states,
                G.IsMaximalGraph data graph ∧
                  G.GraphUsesExit data graph exit) ∧
          ∀ target, target ∉ states →
            G.inducedExitStateProbability exitLaw target =
              data.exitLimit states source target

/-- Formal completion requires a coupled stopping law for the first actual
exit and the first exit-shaped action, which is not in the current semantics. -/
theorem firstUsedExitLaw : G.FirstUsedExitLawClaim := by
  sorry

end PaperGame

/-! ## Section 5.3: constrained fixed points -/

namespace PaperGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- The constrained profile set `X_epsilon`. -/
def IsInConstrainedProfileSet (epsilon : ℝ)
    (x : G.StationaryProfile) : Prop :=
  ∀ state who action, epsilon ^ 2 ≤ (x state who).prob action

/-- Equation (30): continuation cost of one action. -/
noncomputable def continuationCost (x : G.StationaryProfile)
    (payoff : G.StatePayoff) (state : G.State) (who : ι)
    (choice : G.Action who) : ℝ :=
  sSup (Set.range fun alternative : G.Action who =>
    G.mixedContinuationValue state
      (G.replaceMixedAction (x state) who
        (FiniteDistribution.pure alternative))
      (fun next => payoff next who) -
    G.mixedContinuationValue state
      (G.replaceMixedAction (x state) who
        (FiniteDistribution.pure choice))
      (fun next => payoff next who))

/-- Equation (31): approximate-best-reply fixed-point equation. -/
def SatisfiesConstrainedFixedPointEquation (epsilon : ℝ)
    (x : G.StationaryProfile) (payoff : G.StatePayoff) : Prop :=
  ∀ state who choice,
    (x state who).prob choice =
      Real.rpow epsilon (G.continuationCost x payoff state who choice) /
        ∑ alternative : G.Action who,
          Real.rpow epsilon
            (G.continuationCost x payoff state who alternative)

/-- Existence of the Brouwer fixed points `x_epsilon`. -/
def ConstrainedFixedPointClaim : Prop :=
  ∀ epsilon, 0 < epsilon → epsilon < 1 →
    ∃ evaluation : G.AbsorbingStationaryEvaluation,
      G.IsInConstrainedProfileSet epsilon evaluation.profile ∧
        G.SatisfiesConstrainedFixedPointEquation
          epsilon evaluation.profile evaluation.value

/-- The missing work is continuity of the undiscounted absorbing payoff on
the constrained finite simplex and the Brouwer self-map argument. -/
theorem constrainedFixedPoint : G.ConstrainedFixedPointClaim := by
  sorry

/-- Equation (32): harmonicity of the fixed-point payoff. -/
def FixedPointHarmonicity (x : G.StationaryProfile)
    (payoff : G.StatePayoff) : Prop :=
  ∀ state who,
    G.mixedContinuationValue state (x state)
      (fun next => payoff next who) = payoff state who

/-- Lemma 5.3: the limiting payoff dominates every uniform min--max value. -/
def Lemma5_3Claim : Prop :=
  ∀ minmax : ι → G.State → ℝ,
    G.IsUniformMinmaxValue minmax →
      ∀ (x : G.StationaryProfile) (payoff : G.StatePayoff),
        (∀ state who, 0 ≤ payoff state who) →
        G.FixedPointHarmonicity x payoff →
        (∀ state who (choice : G.Action who),
          G.mixedContinuationValue state
            (G.replaceMixedAction (x state) who
              (FiniteDistribution.pure choice))
            (fun next => payoff next who) ≤ payoff state who) →
          ∀ state who, minmax who state ≤ payoff state who

/-- The paper's maximum-principle contradiction uses a uniform punishment
from a maximal state class.  That dynamic separation lemma is not formalized. -/
theorem lemma5_3 : G.Lemma5_3Claim := by
  sorry

/-- Overall graph cost. -/
noncomputable def graphCost (x : G.StationaryProfile)
    (payoff : G.StatePayoff) {states : Finset G.State}
    (graph : G.ExitGraph states) : ℝ :=
  ∑ state in states,
    ∑ who,
      G.continuationCost x payoff state who (graph.action state who)

/-- Cost of an exit, represented by a maximal graph using it. -/
def IsExitCost (data : G.AsymptoticProfileData)
    {states : Finset G.State}
    (exit : G.Exit data.limitProfile states) (cost : ℝ) : Prop :=
  ∃ graph : G.ExitGraph states,
    G.IsMaximalGraph data graph ∧
      G.GraphUsesExit data graph exit ∧
        G.graphCost data.limitProfile data.limitPayoff graph = cost

/-- Lemma 5.4: supported exits have equal cost. -/
def Lemma5_4Claim : Prop :=
  ∀ (data : G.AsymptoticProfileData) (states : Finset G.State)
      (exitLaw : FiniteDistribution (G.Exit data.limitProfile states))
      (first second : G.Exit data.limitProfile states)
      (firstCost secondCost : ℝ),
    0 < exitLaw.prob first → 0 < exitLaw.prob second →
      G.IsExitCost data first firstCost →
        G.IsExitCost data second secondCost →
          firstCost = secondCost

/-- Equation (31) turns a strict cost inequality into an infinite graph-weight
ratio.  Formalizing that exponential comparison is the missing step. -/
theorem lemma5_4 : G.Lemma5_4Claim := by
  sorry

/-- Lemma 5.5: zero-cost directed tree to any selected root. -/
def Lemma5_5Claim : Prop :=
  ∀ (data : G.AsymptoticProfileData) (states : Finset G.State),
    G.CommunicatesUnderTheta data states →
      ∀ root, root ∈ states →
        ∃ graph : G.ExitGraph (states.erase root),
          (∀ source, source ∈ states.erase root →
            ∃ steps, (graph.target^[steps]) source = root) ∧
          G.graphCost data.limitProfile data.limitPayoff graph = 0

/-- The paper extracts a directed spanning tree from a close communicating
perturbation.  The support-to-zero-cost argument depends on the still-open
asymptotic fixed-point bridge. -/
theorem lemma5_5 : G.Lemma5_5Claim := by
  sorry

/-- Corollary 5.6: joint exits cost zero; a unilateral exit costs its owner's
continuation loss. -/
def Corollary5_6Claim : Prop :=
  ∀ (data : G.AsymptoticProfileData) (states : Finset G.State)
      (exit : G.Exit data.limitProfile states) (cost : ℝ),
    G.IsExitCost data exit cost →
      (G.IsJointExit exit → cost = 0) ∧
      ∀ who, G.IsUnilateralExit exit who →
        cost = data.limitPayoff exit.1.state who -
          G.exitContinuationValue exit data.limitPayoff who

/-- This is the graph-splicing consequence of Lemma 5.5.  It remains open
with that lemma and the maximal-graph/exit-use bridge. -/
theorem corollary5_6 : G.Corollary5_6Claim := by
  sorry

/-- The asymptotic fixed-point data satisfy all seven hypotheses of
Proposition 3.8. -/
def Section5_3SufficientDataClaim : Prop :=
  G.IsPositive → G.IsRecursive →
    Nonempty G.StationarySufficientData

/-- Conditions 1--5 require the limiting harmonicity and Lemma 5.3;
conditions 6--7 require Lemmas 5.4--5.5 and Corollary 5.6. -/
theorem section5_3SufficientData :
    G.Section5_3SufficientDataClaim := by
  sorry

/-- Theorem 2.4, proved in Section 5. -/
theorem theorem2_4 : G.Theorem2_4Claim := by
  sorry

end PaperGame

end Literature.SolanAndVieille2002a
