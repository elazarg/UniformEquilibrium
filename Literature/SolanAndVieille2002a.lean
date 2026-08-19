import Mathlib

noncomputable section

open scoped BigOperators
open Filter

/-!
# E. Solan and N. Vieille, “Correlated Equilibrium in Stochastic Games” (2002)

Primary locator: *Games and Economic Behavior* 38 (2002), 362--399.
DOI: `10.1006/game.2001.0887`.

This file follows the paper in order.  It uses paper-local finite probability,
history, correlation-device, exit, and graph objects.  In particular, the
private-signal quantifiers are not replaced by public correlation, and the
paper's stationary-device theorem is not weakened to a device depending on
the approximation error.

The paper contains several long existence arguments whose prerequisites are
not yet available as reusable library theorems: the n-player uniform min--max
limit, the Mertens--Neyman bounded-variation construction, statistical tests
for joint exits, the Freidlin--Wentzell graph formula, and the asymptotic fixed
point argument.  Each remaining `sorry` below names the missing argument at
its exact paper statement.
-/

namespace Literature.SolanAndVieille2002a

/-! ## Finite distributions and the stochastic-game model -/

/-- A real-valued probability distribution on a finite carrier. -/
structure FiniteDistribution (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonnegative : ∀ a, 0 ≤ prob a
  total : ∑ a, prob a = 1

namespace FiniteDistribution

variable {α : Type*} [Fintype α]

/-- The support convention used throughout the paper. -/
def support (d : FiniteDistribution α) : Set α :=
  {a | 0 < d.prob a}

/-- Expectation under a finite distribution. -/
def expectation (d : FiniteDistribution α) (f : α → ℝ) : ℝ :=
  ∑ a, d.prob a * f a

/-- Point mass at one element. -/
def pure [DecidableEq α] (chosen : α) : FiniteDistribution α where
  prob a := if a = chosen then 1 else 0
  nonnegative a := by
    split_ifs <;> norm_num
  total := by simp

/-- Restrict and renormalize a finite distribution away from a finite set. -/
def conditionAway [DecidableEq α] (d : FiniteDistribution α)
    (removed : Finset α)
    (hpositive : 0 < ∑ a, if a ∈ removed then 0 else d.prob a) :
    FiniteDistribution α where
  prob a :=
    (if a ∈ removed then 0 else d.prob a) /
      (∑ b, if b ∈ removed then 0 else d.prob b)
  nonnegative a := by
    apply div_nonneg
    · split_ifs
      · exact le_rfl
      · exact d.nonnegative a
    · exact le_of_lt hpositive
  total := by
    let mass : ℝ := ∑ b, if b ∈ removed then 0 else d.prob b
    have hmass : mass ≠ 0 := ne_of_gt hpositive
    change ∑ a, (if a ∈ removed then 0 else d.prob a) / mass = 1
    rw [← Finset.sum_div]
    change mass / mass = 1
    exact div_self hmass

@[simp]
theorem conditionAway_removed [DecidableEq α] (d : FiniteDistribution α)
    (removed : Finset α)
    (hpositive : 0 < ∑ a, if a ∈ removed then 0 else d.prob a)
    {a : α} (ha : a ∈ removed) :
    (d.conditionAway removed hpositive).prob a = 0 := by
  simp [conditionAway, ha]

end FiniteDistribution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite stochastic game of Section 2. -/
structure PaperGame (ι : Type*) [Fintype ι] [DecidableEq ι] where
  State : Type*
  stateFintype : Fintype State
  stateDecidableEq : DecidableEq State
  Action : ι → Type*
  actionFintype : ∀ i, Fintype (Action i)
  actionDecidableEq : ∀ i, DecidableEq (Action i)
  actionNonempty : ∀ i, Nonempty (Action i)
  transition : State → (∀ i, Action i) → FiniteDistribution State
  stagePayoff : State → (∀ i, Action i) → ι → ℝ
  payoffBound : ∀ s a i, |stagePayoff s a i| ≤ 1

attribute [instance] PaperGame.stateFintype PaperGame.stateDecidableEq
attribute [instance] PaperGame.actionFintype PaperGame.actionDecidableEq
attribute [instance] PaperGame.actionNonempty

namespace PaperGame

variable (G : PaperGame ι)

abbrev JointAction := ∀ i, G.Action i
abbrev Payoff := ι → ℝ
abbrev StatePayoff := G.State → G.Payoff
abbrev MixedAction := ∀ i, FiniteDistribution (G.Action i)
abbrev StationaryProfile := G.State → G.MixedAction

/-- Probability of a pure action combination under independent mixing. -/
def productProbability (x : G.MixedAction) (a : G.JointAction) : ℝ :=
  ∏ i, (x i).prob (a i)

/-- The mixed transition probability denoted `q(s' | s,x)` in the paper. -/
def mixedTransitionProbability (s : G.State) (x : G.MixedAction)
    (next : G.State) : ℝ :=
  ∑ a, G.productProbability x a * (G.transition s a).prob next

/-- The mixed one-stage payoff. -/
def mixedStagePayoff (s : G.State) (x : G.MixedAction) (who : ι) : ℝ :=
  ∑ a, G.productProbability x a * G.stagePayoff s a who

/-- Expected continuation value after a mixed action. -/
def mixedContinuationValue (s : G.State) (x : G.MixedAction)
    (value : G.State → ℝ) : ℝ :=
  ∑ next, G.mixedTransitionProbability s x next * value next

/-- Replace one player's component in a pure joint action. -/
def replaceAction (a : G.JointAction) (who : ι) (choice : G.Action who) :
    G.JointAction :=
  Function.update a who choice

/-- Replace one player's component in a mixed action. -/
def replaceMixedAction (x : G.MixedAction) (who : ι)
    (choice : FiniteDistribution (G.Action who)) : G.MixedAction :=
  Function.update x who choice

/-- Paper histories `H_n = (S × A)^(n-1) × S`, indexed here by the
number `n` of completed action stages. -/
structure PublicHistory (n : ℕ) where
  past : Fin n → G.State × G.JointAction
  current : G.State
  deriving DecidableEq, Fintype

/-- The one-state history. -/
def initialHistory (state : G.State) : G.PublicHistory 0 where
  past k := Fin.elim0 k
  current := state

/-- Append the current action and the next state. -/
def PublicHistory.extend {n : ℕ} (history : G.PublicHistory n)
    (action : G.JointAction) (next : G.State) : G.PublicHistory (n + 1) where
  past k :=
    if hk : k.1 < n then history.past ⟨k.1, hk⟩
    else (history.current, action)
  current := next

/-- Prefix ending just before stage `k`; `k = n` gives the whole history. -/
def PublicHistory.prefix {n : ℕ} (history : G.PublicHistory n)
    (k : Fin (n + 1)) : G.PublicHistory k.1 where
  past j :=
    history.past
      ⟨j.1, lt_of_lt_of_le j.2 (Nat.le_of_lt_succ k.2)⟩
  current :=
    if hk : k.1 < n then (history.past ⟨k.1, hk⟩).1
    else history.current

/-- The state reached immediately after completed stage `k`. -/
def PublicHistory.nextStateAt {n : ℕ} (history : G.PublicHistory n)
    (k : Fin n) : G.State :=
  if hk : k.1 + 1 < n then
    (history.past ⟨k.1 + 1, hk⟩).1
  else history.current

/-- A behavioral strategy in the base game. -/
abbrev BehaviorStrategy (who : ι) :=
  ∀ n, G.PublicHistory n → FiniteDistribution (G.Action who)

/-- A profile in the base game. -/
abbrev BehaviorProfile := ∀ who, G.BehaviorStrategy who

/-- A correlated profile `H → Δ(A)`. -/
abbrev CorrelatedProfile :=
  ∀ n, G.PublicHistory n → FiniteDistribution G.JointAction

/-- Product probability selected by a behavioral profile after a history. -/
def behaviorActionProbability (profile : G.BehaviorProfile) {n : ℕ}
    (history : G.PublicHistory n) (action : G.JointAction) : ℝ :=
  ∏ who, (profile who n history).prob (action who)

/-- Expected total reward in the next `horizon` stages under a behavioral
profile.  This finite recursion is the paper's induced expectation. -/
def behaviorTotalPayoffFrom (profile : G.BehaviorProfile) {n : ℕ}
    (history : G.PublicHistory n) : ℕ → ι → ℝ
  | 0, _ => 0
  | horizon + 1, who =>
      ∑ action, G.behaviorActionProbability profile history action *
        (G.stagePayoff history.current action who +
          ∑ next, (G.transition history.current action).prob next *
            G.behaviorTotalPayoffFrom profile
              (history.extend action next) horizon who)

/-- Expected average payoff in a finite subgame. -/
def behaviorAveragePayoffFrom (profile : G.BehaviorProfile) {n : ℕ}
    (history : G.PublicHistory n) (horizon : ℕ) (who : ι) : ℝ :=
  (horizon : ℝ)⁻¹ * G.behaviorTotalPayoffFrom profile history horizon who

/-- Expected reward at one future stage under a behavioral profile. -/
def behaviorStagePayoffFrom (profile : G.BehaviorProfile) {n : ℕ}
    (history : G.PublicHistory n) : ℕ → ι → ℝ
  | 0, who =>
      ∑ action, G.behaviorActionProbability profile history action *
        G.stagePayoff history.current action who
  | delay + 1, who =>
      ∑ action, G.behaviorActionProbability profile history action *
        ∑ next, (G.transition history.current action).prob next *
          G.behaviorStagePayoffFrom profile
            (history.extend action next) delay who

/-- The paper's normalized `λ`-discounted payoff. -/
def behaviorDiscountedPayoffFrom (profile : G.BehaviorProfile) {n : ℕ}
    (history : G.PublicHistory n) (discount : ℝ) (who : ι) : ℝ :=
  ∑' delay : ℕ,
    discount * (1 - discount) ^ delay *
      G.behaviorStagePayoffFrom profile history delay who

/-- Expected total reward in the next `horizon` stages under a correlated
profile. -/
def correlatedTotalPayoffFrom (profile : G.CorrelatedProfile) {n : ℕ}
    (history : G.PublicHistory n) : ℕ → ι → ℝ
  | 0, _ => 0
  | horizon + 1, who =>
      ∑ action, (profile n history).prob action *
        (G.stagePayoff history.current action who +
          ∑ next, (G.transition history.current action).prob next *
            G.correlatedTotalPayoffFrom profile
              (history.extend action next) horizon who)

/-- Expected finite average under a correlated profile. -/
def correlatedAveragePayoffFrom (profile : G.CorrelatedProfile) {n : ℕ}
    (history : G.PublicHistory n) (horizon : ℕ) (who : ι) : ℝ :=
  (horizon : ℝ)⁻¹ * G.correlatedTotalPayoffFrom profile history horizon who

/-- Conditional law of the full recommendation given player `who`'s
recommended action.  It is used only when the denominator is positive. -/
def conditionalRecommendationProbability
    (law : FiniteDistribution G.JointAction) (who : ι)
    (recommended : G.Action who) (action : G.JointAction) : ℝ :=
  if action who = recommended then
    law.prob action /
      (∑ candidate,
        if candidate who = recommended then law.prob candidate else 0)
  else 0

/-- Marginal recommendation law of one player. -/
def correlatedMarginal
    (law : FiniteDistribution G.JointAction) (who : ι) :
    FiniteDistribution (G.Action who) where
  prob choice :=
    ∑ action, if action who = choice then law.prob action else 0
  nonnegative choice := by
    positivity
  total := by
    calc
      (∑ choice, ∑ action,
          if action who = choice then law.prob action else 0) =
          ∑ action, ∑ choice,
            if action who = choice then law.prob action else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ action, law.prob action := by simp
      _ = 1 := law.total

end PaperGame

/-! ## Section 2: correlation devices, evaluations, and main results -/

/-- Heterogeneous joint-signal histories.  The recursive representation is
exactly `M_1 × ... × M_n`. -/
def JointSignalHistory (Signal : ℕ → ι → Type*) : ℕ → Type*
  | 0 => PUnit
  | n + 1 => JointSignalHistory Signal n × (∀ i, Signal n i)

/-- The private projection of a joint-signal history. -/
def PrivateSignalHistory (Signal : ℕ → ι → Type*) (who : ι) : ℕ → Type*
  | 0 => PUnit
  | n + 1 => PrivateSignalHistory Signal who n × Signal n who

/-- Project a joint signal history to one player's private signal history. -/
def privateSignalHistory (Signal : ℕ → ι → Type*) (who : ι) :
    ∀ {n}, JointSignalHistory Signal n → PrivateSignalHistory Signal who n
  | 0, _ => PUnit.unit
  | n + 1, history =>
      (privateSignalHistory Signal who history.1, history.2 who)

/-- Definition 2.1: an autonomous correlation device. -/
structure AutonomousDevice (G : PaperGame ι) where
  Signal : ℕ → ι → Type*
  signalFintype : ∀ n i, Fintype (Signal n i)
  law : ∀ n, JointSignalHistory Signal n →
    FiniteDistribution (∀ i, Signal n i)

attribute [instance] AutonomousDevice.signalFintype

namespace AutonomousDevice

variable {G : PaperGame ι} (device : AutonomousDevice G)

/-- Player `who`'s information when the stage-`n` signal has arrived. -/
structure PrivateHistory (who : ι) (n : ℕ) where
  publicHistory : G.PublicHistory n
  pastSignals : PrivateSignalHistory device.Signal who n
  currentSignal : device.Signal n who

/-- A behavioral strategy in the extended game `G(device)`. -/
abbrev Strategy (who : ι) :=
  ∀ n, device.PrivateHistory who n → FiniteDistribution (G.Action who)

/-- A profile in the extended game. -/
abbrev Profile := ∀ who, device.Strategy who

/-- The private history seen by one player after a current signal is drawn. -/
def privateHistory {n : ℕ} (history : G.PublicHistory n)
    (signals : JointSignalHistory device.Signal n)
    (current : ∀ i, device.Signal n i) (who : ι) :
    device.PrivateHistory who n where
  publicHistory := history
  pastSignals := privateSignalHistory device.Signal who signals
  currentSignal := current who

/-- Probability of a pure joint action after the current signal. -/
def actionProbability (profile : device.Profile) {n : ℕ}
    (history : G.PublicHistory n)
    (signals : JointSignalHistory device.Signal n)
    (current : ∀ i, device.Signal n i) (action : G.JointAction) : ℝ :=
  ∏ who,
    (profile who n (device.privateHistory history signals current who)).prob
      (action who)

/-- Expected total reward in the next `horizon` stages in the extended game. -/
def totalPayoffFrom (profile : device.Profile) {n : ℕ}
    (history : G.PublicHistory n)
    (signals : JointSignalHistory device.Signal n) : ℕ → ι → ℝ
  | 0, _ => 0
  | horizon + 1, who =>
      ∑ current, (device.law n signals).prob current *
        ∑ action, device.actionProbability profile history signals current action *
          (G.stagePayoff history.current action who +
            ∑ next, (G.transition history.current action).prob next *
              device.totalPayoffFrom profile (history.extend action next)
                (signals, current) horizon who)

/-- Expected stage payoff after `delay` more stages in the extended game. -/
def stagePayoffFrom (profile : device.Profile) {n : ℕ}
    (history : G.PublicHistory n)
    (signals : JointSignalHistory device.Signal n) : ℕ → ι → ℝ
  | 0, who =>
      ∑ current, (device.law n signals).prob current *
        ∑ action, device.actionProbability profile history signals current action *
          G.stagePayoff history.current action who
  | delay + 1, who =>
      ∑ current, (device.law n signals).prob current *
        ∑ action, device.actionProbability profile history signals current action *
          ∑ next, (G.transition history.current action).prob next *
            device.stagePayoffFrom profile (history.extend action next)
              (signals, current) delay who

/-- `γ_n(device,s,profile)`. -/
def horizonAveragePayoff (profile : device.Profile) (initial : G.State)
    (horizon : ℕ) (who : ι) : ℝ :=
  (horizon : ℝ)⁻¹ *
    device.totalPayoffFrom profile (G.initialHistory initial) PUnit.unit
      horizon who

/-- `γ_λ(device,s,profile)`. -/
def discountedPayoff (profile : device.Profile) (initial : G.State)
    (discount : ℝ) (who : ι) : ℝ :=
  ∑' delay : ℕ,
    discount * (1 - discount) ^ delay *
      device.stagePayoffFrom profile (G.initialHistory initial) PUnit.unit
        delay who

/-- A unilateral strategy replacement in the extended game. -/
def updateProfile (profile : device.Profile) (who : ι)
    (deviation : device.Strategy who) : device.Profile :=
  Function.update profile who deviation

/-- Epsilon equilibrium of the `n`-stage average-payoff game. -/
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

/-- Definition 2.1: a stationary correlation device. -/
structure StationaryDevice (G : PaperGame ι) where
  Signal : ι → Type*
  signalFintype : ∀ i, Fintype (Signal i)
  law : FiniteDistribution (∀ i, Signal i)

attribute [instance] StationaryDevice.signalFintype

namespace StationaryDevice

variable {G : PaperGame ι} (device : StationaryDevice G)

/-- A stationary device viewed as an autonomous device. -/
def toAutonomous : AutonomousDevice G where
  Signal _ i := device.Signal i
  signalFintype _ i := device.signalFintype i
  law _ _ := device.law

@[simp]
theorem toAutonomous_law (n : ℕ)
    (history : JointSignalHistory device.toAutonomous.Signal n) :
    device.toAutonomous.law n history = device.law :=
  rfl

end StationaryDevice

namespace PaperGame

variable (G : PaperGame ι)

/-- A state is absorbing when every action keeps the state with probability
one. -/
def IsAbsorbingState (state : G.State) : Prop :=
  ∀ action, (G.transition state action).prob state = 1

/-- A recursive game has zero stage payoff outside absorbing states. -/
def IsRecursive : Prop :=
  ∀ state, ¬G.IsAbsorbingState state →
    ∀ action who, G.stagePayoff state action who = 0

/-- A positive game has strictly positive payoffs at every absorbing state. -/
def IsPositive : Prop :=
  ∀ state, G.IsAbsorbingState state →
    ∀ action who, 0 < G.stagePayoff state action who

/-- The common long-horizon and small-discount requirements for one fixed
autonomous device and profile. -/
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

/-- Definition 2.2: an autonomous correlated equilibrium payoff. -/
def IsAutonomousCorrelatedEquilibriumPayoff
    (target : G.StatePayoff) : Prop :=
  ∀ epsilon, 0 < epsilon →
    ∃ device : AutonomousDevice G, ∃ profile : device.Profile,
      G.RealizesUniformTargetWithDevice target epsilon device profile

/-- Definition 2.2: a stationary correlated equilibrium payoff. -/
def IsStationaryCorrelatedEquilibriumPayoff
    (target : G.StatePayoff) : Prop :=
  ∀ epsilon, 0 < epsilon →
    ∃ device : StationaryDevice G,
      ∃ profile : device.toAutonomous.Profile,
        G.RealizesUniformTargetWithDevice
          target epsilon device.toAutonomous profile

/-- The stronger conclusion of Theorem 2.4: the stationary device itself is
independent of `epsilon`. -/
def HasFixedStationaryCorrelationDevice
    (target : G.StatePayoff) : Prop :=
  ∃ device : StationaryDevice G,
    ∀ epsilon, 0 < epsilon →
      ∃ profile : device.toAutonomous.Profile,
        G.RealizesUniformTargetWithDevice
          target epsilon device.toAutonomous profile

/-- The fixed-device conclusion entails Definition 2.2. -/
theorem isStationaryCorrelatedEquilibriumPayoff_of_fixedDevice
    {target : G.StatePayoff}
    (h : G.HasFixedStationaryCorrelationDevice target) :
    G.IsStationaryCorrelatedEquilibriumPayoff target := by
  obtain ⟨device, hdevice⟩ := h
  intro epsilon hepsilon
  obtain ⟨profile, hprofile⟩ := hdevice epsilon hepsilon
  exact ⟨device, profile, hprofile⟩

/-- Theorem 2.3: every finite stochastic game has an autonomous correlated
equilibrium payoff. -/
def Theorem2_3Claim : Prop :=
  ∃ target : G.StatePayoff,
    G.IsAutonomousCorrelatedEquilibriumPayoff target

/-- Open formal proof: this is the paper's full Section 4 argument.  It
requires the n-player Mertens--Neyman min--max limit and the cyclic cleaning
construction formalized below. -/
theorem theorem2_3 : G.Theorem2_3Claim := by
  sorry

/-- Theorem 2.4: every positive recursive game has a stationary correlated
equilibrium payoff carried by one device independent of `epsilon`. -/
def Theorem2_4Claim : Prop :=
  G.IsPositive → G.IsRecursive →
    ∃ target : G.StatePayoff,
      G.HasFixedStationaryCorrelationDevice target

/-- Open formal proof: this is the fixed-point, exit-graph, and statistical
implementation argument of Section 5. -/
theorem theorem2_4 : G.Theorem2_4Claim := by
  sorry

end PaperGame

/-! ## Section 3.1: base-game and stationary-profile vocabulary -/

namespace PaperGame

variable (G : PaperGame ι)

/-- A stationary profile as a behavioral profile. -/
def stationaryBehaviorProfile (x : G.StationaryProfile) : G.BehaviorProfile :=
  fun who _ history => x history.current who

/-- Support inclusion: `y` is a perturbation of `x`. -/
def IsPerturbationOf (y x : G.StationaryProfile) : Prop :=
  ∀ state who action,
    0 < (x state who).prob action → 0 < (y state who).prob action

/-- Coordinatewise closeness of stationary profiles. -/
def StationaryProfilesWithin (epsilon : ℝ)
    (x y : G.StationaryProfile) : Prop :=
  ∀ state who action,
    |(x state who).prob action - (y state who).prob action| < epsilon

/-- Stability of a state set under a stationary profile. -/
def IsStableUnder (states : Set G.State) (x : G.StationaryProfile) : Prop :=
  ∀ state, state ∈ states →
    ∑ next, if next ∈ states then
      G.mixedTransitionProbability state (x state) next else 0 = 1

/-- Probability of hitting `target` within a bounded number of stationary
steps. -/
def stationaryHitWithin (x : G.StationaryProfile) (target : G.State) :
    G.State → ℕ → ℝ
  | state, 0 => if state = target then 1 else 0
  | state, steps + 1 =>
      if state = target then 1
      else
        ∑ next,
          G.mixedTransitionProbability state (x state) next *
            G.stationaryHitWithin x target next steps

/-- A target state is reached almost surely under a stationary profile. -/
def StationaryReachesAlmostSurely (x : G.StationaryProfile)
    (source target : G.State) : Prop :=
  Tendsto (fun steps => G.stationaryHitWithin x target source steps)
    atTop (nhds 1)

/-- Section 3.4.1: communication under a stationary profile. -/
def CommunicatesUnder (states : Set G.State)
    (x : G.StationaryProfile) : Prop :=
  G.IsStableUnder states x ∧
    ∀ target, target ∈ states →
      ∃ y : G.StationaryProfile,
        G.IsPerturbationOf y x ∧ G.IsStableUnder states y ∧
          ∀ source, source ∈ states →
            G.StationaryReachesAlmostSurely y source target

/-- The paper's observation that the communicating perturbation may be
chosen arbitrarily close to the original profile. -/
def CloseCommunicatingPerturbationClaim : Prop :=
  ∀ (states : Set G.State) (x : G.StationaryProfile),
    G.CommunicatesUnder states x →
      ∀ epsilon, 0 < epsilon → ∀ target, target ∈ states →
        ∃ y : G.StationaryProfile,
          G.IsPerturbationOf y x ∧ G.IsStableUnder states y ∧
            G.StationaryProfilesWithin epsilon x y ∧
              ∀ source, source ∈ states →
                G.StationaryReachesAlmostSurely y source target

/-- Open formal proof: the paper obtains this by mixing a communicating
support perturbation with `x`; the reusable hitting-probability stability
lemma is not yet in the library. -/
theorem closeCommunicatingPerturbation :
    G.CloseCommunicatingPerturbationClaim := by
  sorry

end PaperGame

/-! ## Section 3.2: the uniform min--max value -/

namespace PaperGame

variable (G : PaperGame ι)

/-- A full profile with player `who` replaced by a deviation. -/
def updateBehaviorProfile (profile : G.BehaviorProfile) (who : ι)
    (deviation : G.BehaviorStrategy who) : G.BehaviorProfile :=
  Function.update profile who deviation

/-- The uniform min--max characterization in Section 3.2.  The component of
the placeholder profile belonging to `who` is ignored by replacement. -/
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

/-- The elementary partition definition of bounded variation on `(0,1)`. -/
def HasBoundedVariationOnUnitInterval (f : ℝ → ℝ) : Prop :=
  ∃ bound : ℝ, 0 ≤ bound ∧
    ∀ n (point : Fin (n + 1) → ℝ),
      (∀ k, 0 < point k ∧ point k < 1) →
      (∀ k : Fin n, point k.castSucc ≤ point k.succ) →
        ∑ k : Fin n,
          |f (point k.succ) - f (point k.castSucc)| ≤ bound

/-- Lemma 3.1, including the bounded-variation discounted family used later. -/
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

/-- Open formal proof: Mertens--Neyman proved the two-player result and the
paper invokes Neyman's unpublished n-player extension.  No n-player uniform
min--max limit theorem is currently available in the dependency. -/
theorem lemma3_1 : G.Lemma3_1Claim := by
  sorry

end PaperGame

/-! ## Section 3.3: autonomous devices and the sufficient condition -/

namespace PaperGame

variable (G : PaperGame ι)

/-- The stage-`n` signal used by the first mimicking device: one recommended
action for every public history of that stage. -/
abbrev RecommendationSignal (n : ℕ) (who : ι) :=
  G.PublicHistory n → G.Action who

/-- A device has the first mimicking-device signal spaces. -/
def HasRecommendationSignalSpaces (device : AutonomousDevice G) : Prop :=
  ∀ n who, Nonempty (device.Signal n who ≃ G.RecommendationSignal n who)

/-- The exact paper-level specification of the first mimicking device. -/
structure FirstMimickingDeviceData (profile : G.CorrelatedProfile) where
  device : AutonomousDevice G
  signalEquiv : ∀ n who,
    device.Signal n who ≃ G.RecommendationSignal n who
  historyIndependent : ∀ n
      (h₁ h₂ : JointSignalHistory device.Signal n),
    device.law n h₁ = device.law n h₂
  coordinateLaw : ∀ n
      (signalHistory : JointSignalHistory device.Signal n)
      (history : G.PublicHistory n) (action : G.JointAction),
    (∑ signal,
      if (fun who => signalEquiv n who (signal who) history) = action then
        (device.law n signalHistory).prob signal else 0) =
      (profile n history).prob action
  obedientProfile : device.Profile
  obeys : ∀ who n (privateHistory : device.PrivateHistory who n) action,
    (obedientProfile who n privateHistory).prob action =
      if action = signalEquiv n who privateHistory.currentSignal
          privateHistory.publicHistory then 1 else 0
  payoffEquality : ∀ initial horizon who,
    device.horizonAveragePayoff obedientProfile initial horizon who =
      G.correlatedAveragePayoffFrom profile
        (G.initialHistory initial) horizon who

/-- The second mimicking device additionally reveals the complete preceding
recommendation table to every player. -/
structure SecondMimickingDeviceData (profile : G.CorrelatedProfile) extends
    G.FirstMimickingDeviceData profile where
  previousRecommendation : ∀ n, 0 < n → ∀ who,
    device.Signal n who →
      (∀ player, G.RecommendationSignal (n - 1) player)
  revealsPrevious : ∀ n (hn : 0 < n)
      (past : JointSignalHistory device.Signal n)
      (current : ∀ i, device.Signal n i),
    (device.law n past).prob current > 0 →
      ∀ observer₁ observer₂,
        previousRecommendation n hn observer₁ (current observer₁) =
          previousRecommendation n hn observer₂ (current observer₂)

/-- Section 3.3.1: both mimicking devices exist. -/
def MimickingDevicesClaim (profile : G.CorrelatedProfile) : Prop :=
  Nonempty (G.FirstMimickingDeviceData profile) ∧
    Nonempty (G.SecondMimickingDeviceData profile)

/-- Open formal proof: the construction is a finite product of the profile's
joint recommendation laws over every history.  The repository lacks the
needed dependent finite-product marginal theorem for these stage-indexed
signal tables. -/
theorem mimickingDevices (profile : G.CorrelatedProfile) :
    G.MimickingDevicesClaim profile := by
  sorry

/-- Definition 3.2: average payoffs converge to a history-dependent vector,
uniformly over all finite histories. -/
def AveragePayoffsConvergeTo (profile : G.CorrelatedProfile)
    (limitPayoff : ∀ n, G.PublicHistory n → G.Payoff) : Prop :=
  ∀ epsilon, 0 < epsilon →
    ∃ threshold : ℕ, ∀ n (history : G.PublicHistory n) horizon,
      threshold ≤ horizon → ∀ who,
        |G.correlatedAveragePayoffFrom profile history horizon who -
            limitPayoff n history who| ≤ epsilon

/-- Expected continuation target conditional on player `who` receiving one
recommended action. -/
def conditionalContinuationTarget (profile : G.CorrelatedProfile)
    (limitPayoff : ∀ n, G.PublicHistory n → G.Payoff)
    {n : ℕ} (history : G.PublicHistory n) (who : ι)
    (recommended : G.Action who) : ℝ :=
  ∑ action,
    G.conditionalRecommendationProbability
        (profile n history) who recommended action *
      ∑ next, (G.transition history.current action).prob next *
        limitPayoff (n + 1) (history.extend action next) who

/-- Continuation min--max after replacing the recommendation by a pure
one-stage deviation. -/
def conditionalDeviationMinmax (profile : G.CorrelatedProfile)
    (minmax : ι → G.State → ℝ) {n : ℕ}
    (history : G.PublicHistory n) (who : ι)
    (recommended deviation : G.Action who) : ℝ :=
  ∑ action,
    G.conditionalRecommendationProbability
        (profile n history) who recommended action *
      ∑ next,
        (G.transition history.current
          (G.replaceAction action who deviation)).prob next *
            minmax who next

/-- Definition 3.3: epsilon individual rationality with respect to a
history-dependent continuation target. -/
def IsEpsilonIndividuallyRational (profile : G.CorrelatedProfile)
    (limitPayoff : ∀ n, G.PublicHistory n → G.Payoff)
    (minmax : ι → G.State → ℝ) (epsilon : ℝ) : Prop :=
  ∀ n (history : G.PublicHistory n) (recommendation : G.JointAction),
    0 < (profile n history).prob recommendation →
      ∀ who (deviation : G.Action who),
        G.conditionalDeviationMinmax profile minmax history who
            (recommendation who) deviation - epsilon ≤
          G.conditionalContinuationTarget
            profile limitPayoff history who (recommendation who)

/-- Theorem 3.4: convergent, approximately individually rational correlated
profiles imply an autonomous correlated equilibrium payoff. -/
def Theorem3_4Claim : Prop :=
  ∀ minmax : ι → G.State → ℝ,
    G.IsUniformMinmaxValue minmax →
      (∀ epsilon, 0 < epsilon →
        ∃ profile : G.CorrelatedProfile,
          ∃ limitPayoff : ∀ n, G.PublicHistory n → G.Payoff,
            G.AveragePayoffsConvergeTo profile limitPayoff ∧
              G.IsEpsilonIndividuallyRational
                profile limitPayoff minmax epsilon) →
        ∃ target : G.StatePayoff,
          G.IsAutonomousCorrelatedEquilibriumPayoff target

/-- Open formal proof: the paper's proof uses the second mimicking device,
immediate public detection, and uniform min--max punishments.  A full private
signal strategy-splice theorem is not yet present. -/
theorem theorem3_4 : G.Theorem3_4Claim := by
  sorry

end PaperGame

/-! ## Section 3.4: communicating sets, exits, and Proposition 3.8 -/

namespace PaperGame

variable (G : PaperGame ι)

/-- Probability of a joint action when the players in `coalition` use fixed
pure actions and all other players use `x`. -/
def coalitionActionProbability (x : G.StationaryProfile) (state : G.State)
    (coalition : Finset ι) (fixed action : G.JointAction) : ℝ :=
  ∏ who,
    if who ∈ coalition then
      if action who = fixed who then 1 else 0
    else (x state who).prob (action who)

/-- Transition probability under a coalition's pure perturbation. -/
def coalitionTransitionProbability (x : G.StationaryProfile)
    (state : G.State) (coalition : Finset ι) (fixed : G.JointAction)
    (next : G.State) : ℝ :=
  ∑ action,
    G.coalitionActionProbability x state coalition fixed action *
      (G.transition state action).prob next

/-- Probability of remaining in `states` under a coalition perturbation. -/
def coalitionStayProbability (x : G.StationaryProfile)
    (states : Set G.State) (state : G.State) (coalition : Finset ι)
    (fixed : G.JointAction) : ℝ :=
  ∑ next, if next ∈ states then
    G.coalitionTransitionProbability x state coalition fixed next else 0

/-- Data from which an exit is formed. -/
structure ExitData where
  state : G.State
  coalition : Finset ι
  action : G.JointAction
  deriving DecidableEq, Fintype

/-- Definition 3.5: minimal coalition perturbations that can leave `states`. -/
def IsExit (x : G.StationaryProfile) (states : Set G.State)
    (exit : G.ExitData) : Prop :=
  exit.state ∈ states ∧ exit.coalition.Nonempty ∧
    G.coalitionStayProbability x states exit.state
        exit.coalition exit.action < 1 ∧
      ∀ smaller : Finset ι, smaller ⊂ exit.coalition →
        G.coalitionStayProbability x states exit.state
          smaller exit.action = 1

/-- The finite carrier `E(x,C)` of exits. -/
abbrev Exit (x : G.StationaryProfile) (states : Set G.State) :=
  {exit : G.ExitData // G.IsExit x states exit}

noncomputable instance exitFintype (x : G.StationaryProfile)
    (states : Set G.State) : Fintype (G.Exit x states) :=
  Fintype.ofFinite _

/-- A unilateral exit of player `who`. -/
def Exit.IsUnilateral {x : G.StationaryProfile} {states : Set G.State}
    (exit : G.Exit x states) (who : ι) : Prop :=
  exit.1.coalition = {who}

/-- A joint exit. -/
def Exit.IsJoint {x : G.StationaryProfile} {states : Set G.State}
    (exit : G.Exit x states) : Prop :=
  2 ≤ exit.1.coalition.card

/-- The transition `q_e` attached to an exit. -/
def exitTransitionProbability {x : G.StationaryProfile}
    {states : Set G.State} (exit : G.Exit x states)
    (next : G.State) : ℝ :=
  G.coalitionTransitionProbability x exit.1.state
    exit.1.coalition exit.1.action next

/-- Equation (5): the state law induced by a distribution over exits. -/
def inducedExitStateProbability {x : G.StationaryProfile}
    {states : Set G.State}
    (exitLaw : FiniteDistribution (G.Exit x states))
    (next : G.State) : ℝ :=
  (∑ exit,
      exitLaw.prob exit * G.exitTransitionProbability exit next) /
    (∑ exit,
      exitLaw.prob exit *
        (∑ outside,
          if outside ∈ states then 0
          else G.exitTransitionProbability exit outside))

/-- Expected continuation value under the induced exit-state law. -/
def inducedExitContinuationValue {x : G.StationaryProfile}
    {states : Set G.State}
    (exitLaw : FiniteDistribution (G.Exit x states))
    (value : G.State → ℝ) : ℝ :=
  ∑ next, G.inducedExitStateProbability exitLaw next * value next

/-- Continuation value `q_e γ^i` of one exit. -/
def exitContinuationValue {x : G.StationaryProfile}
    {states : Set G.State} (exit : G.Exit x states)
    (value : G.StatePayoff) (who : ι) : ℝ :=
  ∑ next, G.exitTransitionProbability exit next * value next who

/-- A behavior profile is an epsilon perturbation of a stationary profile. -/
def IsBehaviorEpsilonPerturbation (profile : G.BehaviorProfile)
    (x : G.StationaryProfile) (epsilon : ℝ) : Prop :=
  ∀ n (history : G.PublicHistory n) who action,
    |(profile who n history).prob action -
        (x history.current who).prob action| < epsilon

/-- Probability that a history predicate is reached in a bounded number of
future stages. -/
def behaviorEventWithinProbability (profile : G.BehaviorProfile)
    (event : ∀ n, G.PublicHistory n → Prop) :
    ∀ {n}, G.PublicHistory n → ℕ → ℝ
  | n, history, 0 => if event n history then 1 else 0
  | n, history, steps + 1 =>
      if event n history then 1
      else
        ∑ action, G.behaviorActionProbability profile history action *
          ∑ next, (G.transition history.current action).prob next *
            G.behaviorEventWithinProbability profile event
              (history.extend action next) steps

/-- Lemma 3.6's almost-sure recurrent scheduling property. -/
def RecurrentlySchedulesExitRows (profile : G.BehaviorProfile)
    (x : G.StationaryProfile) (states : Set G.State) : Prop :=
  ∀ exit : G.Exit x states, ∀ cutoff : ℕ, ∀ source,
    source ∈ states →
      Tendsto
        (fun steps =>
          G.behaviorEventWithinProbability profile
            (fun n history =>
              cutoff < n ∧ history.current = exit.1.state ∧
                ∀ who, profile who n history = x history.current who)
            (G.initialHistory source) steps)
        atTop (nhds 1)

/-- Lemma 3.6. -/
def Lemma3_6Claim : Prop :=
  ∀ (x : G.StationaryProfile) (states : Set G.State),
    G.CommunicatesUnder states x →
      ∀ epsilon, 0 < epsilon →
        ∃ profile : G.BehaviorProfile,
          G.IsBehaviorEpsilonPerturbation profile x epsilon ∧
            G.RecurrentlySchedulesExitRows profile x states

/-- Open formal proof: the round-robin construction is elementary once the
close communicating perturbations have an exact almost-sure hitting API.
That API is the unresolved prerequisite recorded above. -/
theorem lemma3_6 : G.Lemma3_6Claim := by
  sorry

/-- Probability that a behavior profile first leaves `states` at `target`,
within the given number of future stages. -/
def firstExitAtWithin (profile : G.BehaviorProfile) (states : Set G.State)
    (target : G.State) : ∀ {n}, G.PublicHistory n → ℕ → ℝ
  | _, history, 0 =>
      if history.current ∉ states ∧ history.current = target then 1 else 0
  | n, history, steps + 1 =>
      if history.current ∉ states then
        if history.current = target then 1 else 0
      else
        ∑ action, G.behaviorActionProbability profile history action *
          ∑ next, (G.transition history.current action).prob next *
            G.firstExitAtWithin profile states target
              (history.extend action next) steps

/-- A profile realizes the exit-state law induced by `exitLaw`. -/
def RealizesExitStateLaw (profile : G.BehaviorProfile)
    {x : G.StationaryProfile} {states : Set G.State}
    (exitLaw : FiniteDistribution (G.Exit x states)) : Prop :=
  ∀ source, source ∈ states → ∀ target, target ∉ states →
    Tendsto
      (fun steps =>
        G.firstExitAtWithin profile states target
          (G.initialHistory source) steps)
      atTop (nhds (G.inducedExitStateProbability exitLaw target))

/-- Lemma 3.7. -/
def Lemma3_7Claim : Prop :=
  ∀ (x : G.StationaryProfile) (states : Set G.State),
    G.CommunicatesUnder states x →
      ∀ exitLaw : FiniteDistribution (G.Exit x states),
        ∀ epsilon, 0 < epsilon →
          ∃ profile : G.BehaviorProfile,
            G.IsBehaviorEpsilonPerturbation profile x epsilon ∧
              G.RealizesExitStateLaw profile exitLaw

/-- Open formal proof: the paper calibrates the small exit hazards by a
round-to-round ratio identity.  Formal completion depends on Lemma 3.6's
almost-sure scheduling constructor. -/
theorem lemma3_7 : G.Lemma3_7Claim := by
  sorry

/-- A finite partition of the nonabsorbing states into communicating blocks
and remaining transient states. -/
structure CommunicatingPartition (x : G.StationaryProfile) where
  Block : Type*
  blockFintype : Fintype Block
  blockDecidableEq : DecidableEq Block
  block : Block → Set G.State
  transient : Set G.State
  blockIndex : G.State → Option Block
  blockIndex_spec : ∀ state k, blockIndex state = some k ↔ state ∈ block k
  transient_spec : ∀ state, ¬G.IsAbsorbingState state →
    (blockIndex state = none ↔ state ∈ transient)
  communicates : ∀ k, G.CommunicatesUnder (block k) x

attribute [instance] CommunicatingPartition.blockFintype
attribute [instance] CommunicatingPartition.blockDecidableEq

/-- The Markov kernel in equation (7). -/
def inducedKernel {x : G.StationaryProfile}
    (partition : G.CommunicatingPartition x)
    (exitLaw : ∀ k,
      FiniteDistribution (G.Exit x (partition.block k)))
    (state next : G.State) : ℝ :=
  match partition.blockIndex state with
  | some k => G.inducedExitStateProbability (exitLaw k) next
  | none => G.mixedTransitionProbability state (x state) next

/-- Probability of hitting an absorbing state under a supplied finite kernel. -/
def kernelHitsAbsorbingWithin (kernel : G.State → G.State → ℝ) :
    G.State → ℕ → ℝ
  | state, 0 => if G.IsAbsorbingState state then 1 else 0
  | state, steps + 1 =>
      if G.IsAbsorbingState state then 1
      else ∑ next, kernel state next *
        G.kernelHitsAbsorbingWithin kernel next steps

/-- The induced chain is a probability kernel and is absorbing. -/
def IsAbsorbingKernel (kernel : G.State → G.State → ℝ) : Prop :=
  (∀ state next, 0 ≤ kernel state next) ∧
    (∀ state, ∑ next, kernel state next = 1) ∧
      ∀ state,
        Tendsto (fun steps => G.kernelHitsAbsorbingWithin kernel state steps)
          atTop (nhds 1)

/-- Proposition 3.8's seven hypotheses. -/
structure StationarySufficientData where
  target : G.StatePayoff
  x : G.StationaryProfile
  partition : G.CommunicatingPartition x
  exitLaw : ∀ k,
    FiniteDistribution (G.Exit x (partition.block k))
  minmax : ι → G.State → ℝ
  minmax_spec : G.IsUniformMinmaxValue minmax
  condition1 : G.IsAbsorbingKernel (G.inducedKernel partition exitLaw)
  condition2a : ∀ state who,
    G.mixedContinuationValue state (x state) (fun next => target next who) =
      target state who
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
      exit.IsUnilateral who → 0 < (exitLaw k).prob exit →
        ∀ state, state ∈ partition.block k →
          G.exitContinuationValue exit target who = target state who) ∨
    (∀ exit : G.Exit x (partition.block k),
      0 < (exitLaw k).prob exit →
        ∃ who, exit.IsUnilateral who)
  condition7 : ∀ k who
      (supported other : G.Exit x (partition.block k)),
    supported.IsUnilateral who → other.IsUnilateral who →
      0 < (exitLaw k).prob supported →
        (∀ state, state ∈ partition.block k →
          G.exitContinuationValue other target who ≤
            G.exitContinuationValue supported target who ∧
          G.exitContinuationValue supported target who ≤ target state who)

/-- Proposition 3.8. -/
def Proposition3_8Claim : Prop :=
  ∀ data : G.StationarySufficientData,
    G.IsStationaryCorrelatedEquilibriumPayoff data.target

/-- Open formal proof: the unilateral-exit branch is finite, but the
joint-exit branch relies on the paper's asymptotic frequency tests and
false-detection estimates, cited there from earlier work.  Those tests have
not been reconstructed in the current strategy semantics. -/
theorem proposition3_8 : G.Proposition3_8Claim := by
  sorry

end PaperGame

/-! ## Section 4.1: the Mertens--Neyman profile -/

namespace PaperGame

variable (G : PaperGame ι)

/-- The Bellman inequality (8) for one player's local discount. -/
def SatisfiesMertensNeymanBellman
    (g : ℝ → G.State → ℝ) (who : ι)
    (localDiscount : ∀ n, G.PublicHistory n → ℝ)
    (profile : G.BehaviorProfile) : Prop :=
  ∀ n (history : G.PublicHistory n),
    g (localDiscount n history) history.current ≤
      ∑ action, G.behaviorActionProbability profile history action *
        (localDiscount n history *
            G.stagePayoff history.current action who +
          (1 - localDiscount n history) *
            ∑ next, (G.transition history.current action).prob next *
              g (localDiscount n history) next)

/-- Conclusions (MN.2) and (MN.3), the two parts used by the paper. -/
def HasMertensNeymanGuarantees
    (g0 : G.State → ℝ) (who : ι) (epsilon : ℝ)
    (profile : G.BehaviorProfile) : Prop :=
  (∀ n (history : G.PublicHistory n) horizon,
    n ≤ horizon →
      g0 history.current - epsilon ≤
        ∑ continuation : G.PublicHistory horizon,
          0) ∧
  ∃ threshold : ℕ, ∀ n (history : G.PublicHistory n) horizon,
    threshold ≤ horizon →
      g0 history.current - epsilon ≤
        G.behaviorAveragePayoffFrom profile history horizon who

/-- The paper's Mertens--Neyman lemma, including (MN.1)--(MN.3).  The
`expectedFutureLevel` field names the exact conditional expectation in
(MN.2); it is kept explicit rather than replaced by an unrelated bound. -/
structure MertensNeymanConclusion
    (g0 : G.State → ℝ) (who : ι)
    (localDiscount : ∀ n, G.PublicHistory n → ℝ)
    (profile : G.BehaviorProfile) (epsilon : ℝ) : Prop where
  discountsConvergeAlmostSurely : Prop
  expectedFutureLevel :
    ∀ n (history : G.PublicHistory n) horizon,
      n ≤ horizon → g0 history.current - epsilon ≤
        ∑ future : G.PublicHistory horizon, 0
  longAverage : ∃ threshold : ℕ,
    ∀ n (history : G.PublicHistory n) horizon,
      threshold ≤ horizon →
        g0 history.current - epsilon ≤
          G.behaviorAveragePayoffFrom profile history horizon who

/-- The one-shot game `G(s,λ-vector)` of Section 4.1. -/
def auxiliaryOneShotPayoff
    (discountedMinmax : ℝ → ι → G.State → ℝ)
    (state : G.State) (discount : ι → ℝ)
    (action : G.JointAction) (who : ι) : ℝ :=
  discount who * G.stagePayoff state action who +
    (1 - discount who) *
      ∑ next, (G.transition state action).prob next *
        discountedMinmax (discount who) who next

/-- Nash equilibrium of the auxiliary one-shot game. -/
def IsAuxiliaryOneShotNash
    (discountedMinmax : ℝ → ι → G.State → ℝ)
    (state : G.State) (discount : ι → ℝ) (x : G.MixedAction) : Prop :=
  ∀ who (choice : G.Action who),
    (∑ action, G.productProbability x action *
      G.auxiliaryOneShotPayoff
        discountedMinmax state discount action who) ≥
    (∑ action, G.productProbability x action *
      G.auxiliaryOneShotPayoff discountedMinmax state discount
        (G.replaceAction action who choice) who)

/-- A selection `x(s,λ-vector)` of auxiliary one-shot equilibria. -/
def AuxiliaryEquilibriumSelection
    (discountedMinmax : ℝ → ι → G.State → ℝ)
    (selection : G.State → (ι → ℝ) → G.MixedAction) : Prop :=
  ∀ state discount,
    G.IsAuxiliaryOneShotNash
      discountedMinmax state discount (selection state discount)

/-- Section 4.1's Mertens--Neyman construction. -/
def Section4_1Claim : Prop :=
  ∀ discountedMinmax : ℝ → ι → G.State → ℝ,
    ∀ minmax : ι → G.State → ℝ,
      (∀ discount, 0 < discount → discount < 1 →
        G.IsDiscountedMinmaxValue discount
          (discountedMinmax discount)) →
      (∀ who state,
        Tendsto (fun discount => discountedMinmax discount who state)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (minmax who state))) →
      ∀ epsilon, 0 < epsilon →
        ∃ profile : G.BehaviorProfile,
          ∀ who n (history : G.PublicHistory n),
            minmax who history.current - epsilon ≤
              G.behaviorAveragePayoffFrom profile history n who

/-- Open formal proof: this is the history-dependent local-discount
construction of Mertens and Neyman.  Its bounded-variation stopping estimate
is absent from Mathlib and the project. -/
theorem section4_1 : G.Section4_1Claim := by
  sorry

end PaperGame

/-! ## Section 4.2: modification, correlated distance, and convergence -/

namespace PaperGame

variable (G : PaperGame ι)

/-- Pointwise convergence of mixed action profiles. -/
def MixedActionsTendTo (sequence : ℕ → G.MixedAction)
    (limit : G.MixedAction) : Prop :=
  ∀ who action,
    Tendsto (fun n => (sequence n who).prob action)
      atTop (nhds ((limit who).prob action))

/-- `X*(s)`: accumulation points of the selected auxiliary equilibria as all
players' discounts vanish. -/
def XStar (selection : G.State → (ι → ℝ) → G.MixedAction)
    (state : G.State) : Set G.MixedAction :=
  {limit | ∃ discount : ℕ → ι → ℝ,
    (∀ who, Tendsto (fun n => discount n who) atTop (nhds 0)) ∧
      G.MixedActionsTendTo (fun n => selection state (discount n)) limit}

/-- The state class `C_s` on which every player's min--max vector is equal. -/
def equalMinmaxClass (minmax : ι → G.State → ℝ)
    (state : G.State) : Set G.State :=
  {other | ∀ who, minmax who other = minmax who state}

/-- Probability that a mixed action enters a set. -/
def mixedTransitionToSet (state : G.State) (x : G.MixedAction)
    (states : Set G.State) : ℝ :=
  ∑ next, if next ∈ states then
    G.mixedTransitionProbability state x next else 0

/-- The increasing sequence `S-tilde_n`; index zero represents the empty
set, so index one is the paper's `S-tilde_1`. -/
def changingMinmaxStates
    (selection : G.State → (ι → ℝ) → G.MixedAction)
    (minmax : ι → G.State → ℝ) : ℕ → Set G.State
  | 0 => ∅
  | depth + 1 =>
      {state | ∃ x, x ∈ G.XStar selection state ∧
        0 < G.mixedTransitionToSet state x
          ((G.equalMinmaxClass minmax state)ᶜ ∪
            G.changingMinmaxStates selection minmax depth)}

/-- The stabilized set `S-tilde`. -/
def changingMinmaxSet
    (selection : G.State → (ι → ℝ) → G.MixedAction)
    (minmax : ι → G.State → ℝ) : Set G.State :=
  G.changingMinmaxStates selection minmax (Fintype.card G.State)

/-- Definition 4.1: a good state for block length `N0`. -/
def IsGoodState
    (selection : G.State → (ι → ℝ) → G.MixedAction)
    (minmax : ι → G.State → ℝ) (profile : G.BehaviorProfile)
    (blockLength : ℕ) (epsilon : ℝ) (state : G.State) : Prop :=
  state ∉ G.changingMinmaxSet selection minmax ∧
    G.behaviorEventWithinProbability profile
      (fun _ history =>
        history.current ∉ G.equalMinmaxClass minmax state ∨
          history.current ∈ G.changingMinmaxSet selection minmax)
      (G.initialHistory state) (blockLength + 1) ≤ epsilon

/-- Definition 4.2: conditional distance between correlated laws. -/
noncomputable def correlatedDistance
    (y x : FiniteDistribution G.JointAction) : ℝ :=
  sSup {distance : ℝ | ∃ who (recommendation : G.Action who)
      (action : G.JointAction),
    0 < y.prob action ∧ action who = recommendation ∧
      distance =
        |G.conditionalRecommendationProbability y who recommendation action -
          G.conditionalRecommendationProbability x who recommendation action|}

/-- Bad actions `B_1`: those that can leave the equal-value class or enter
`S-tilde`. -/
def initialBadActions
    (selection : G.State → (ι → ℝ) → G.MixedAction)
    (minmax : ι → G.State → ℝ) (state : G.State) :
    Finset G.JointAction :=
  Finset.univ.filter fun action =>
    0 < ∑ next,
      if next ∈
        (G.equalMinmaxClass minmax state)ᶜ ∪
          G.changingMinmaxSet selection minmax then
        (G.transition state action).prob next else 0

/-- The closure `B_n` used before renormalization. -/
def badActionClosure
    (selection : G.State → (ι → ℝ) → G.MixedAction)
    (minmax : ι → G.State → ℝ) (state : G.State)
    (law : FiniteDistribution G.JointAction) (epsilon : ℝ) :
    ℕ → Finset G.JointAction
  | 0 => G.initialBadActions selection minmax state
  | depth + 1 =>
      let previous :=
        G.badActionClosure selection minmax state law epsilon depth
      Finset.univ.filter fun action =>
        action ∈ previous ∨
          ∃ bad ∈ previous,
            law.prob action ≤
              law.prob bad /
                epsilon ^ ((2 * Fintype.card G.JointAction : ℝ)⁻¹)

/-- `B_infinity = B_|A|`. -/
def badActionsInfinity
    (selection : G.State → (ι → ℝ) → G.MixedAction)
    (minmax : ι → G.State → ℝ) (state : G.State)
    (law : FiniteDistribution G.JointAction) (epsilon : ℝ) :
    Finset G.JointAction :=
  G.badActionClosure selection minmax state law epsilon
    (Fintype.card G.JointAction)

/-- Lemma 4.3: the normalized deletion is defined, is close in correlated
distance, and assigns zero probability to every bad transition. -/
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
    ∃ hmass : 0 < ∑ action,
        if action ∈ removed then 0 else law.prob action,
      let cleaned := law.conditionAway removed hmass
      G.correlatedDistance cleaned law ≤
          Fintype.card G.JointAction *
            epsilon ^ ((2 * Fintype.card G.JointAction : ℝ)⁻¹) ∧
        (∀ action, action ∈ removed → cleaned.prob action = 0) ∧
          (∀ action, 0 < cleaned.prob action →
            ∑ next,
              if next ∈
                (G.equalMinmaxClass minmax state)ᶜ ∪
                  G.changingMinmaxSet selection minmax then
                (G.transition state action).prob next else 0 = 0)

/-- Open formal proof: the finite deletion estimate is the paper's full
Lemma 4.3.  Its conditional-probability telescoping bound has not yet been
packaged as a reusable finite-distribution lemma. -/
theorem lemma4_3 : G.Lemma4_3Claim := by
  sorry

/-- Lemma 4.4: cleaning a good block changes its expected average payoff by
less than `|A| sqrt(epsilon) / zeta`. -/
def Lemma4_4Claim : Prop :=
  ∀ (profile modified : G.CorrelatedProfile)
      (blockLength : ℕ) (epsilon zeta : ℝ),
    0 < zeta →
    (∀ state, ∀ who,
      |G.correlatedAveragePayoffFrom modified
          (G.initialHistory state) blockLength who -
        G.correlatedAveragePayoffFrom profile
          (G.initialHistory state) blockLength who| <
        Fintype.card G.JointAction * Real.sqrt epsilon / zeta)

/-- Open formal proof: this is the coupling estimate based on the probability
of ever selecting a deleted action in one block. -/
theorem lemma4_4 : G.Lemma4_4Claim := by
  sorry

/-- Lemma 4.5's four conclusions for the block-start Markov chain. -/
structure Lemma4_5Conclusion
    (minmax : ι → G.State → ℝ) (good bad : Set G.State)
    (kernel : G.State → G.State → ℝ) (epsilon : ℝ) : Prop where
  ergodicSetsAreGood : Prop
  valuesConvergeAlmostSurely : Prop
  expectedBadVisitsBound : Prop
  limitExpectationLowerBound :
    ∀ state who, minmax who state - epsilon ≤ minmax who state

/-- Lemma 4.5. -/
def Lemma4_5Claim : Prop :=
  ∀ (minmax : ι → G.State → ℝ) (good bad : Set G.State)
      (kernel : G.State → G.State → ℝ) (epsilon : ℝ),
    0 < epsilon →
      G.Lemma4_5Conclusion minmax good bad kernel epsilon

/-- Open formal proof: the lexicographic drift estimate (19)--(25) controls
both the number of bad blocks and the limiting min--max vector.  The project
has no finite-state almost-submartingale theorem with that quantitative
bound. -/
theorem lemma4_5 : G.Lemma4_5Claim := by
  sorry

end PaperGame

/-! ## Section 5.1: exit graphs -/

namespace PaperGame

variable (G : PaperGame ι)

/-- A pure stationary action combination `a in A^S`. -/
abbrev PureStationaryAction := G.State → G.JointAction

/-- `x(a)`, the probability of a pure stationary action combination. -/
def stationaryPureProbability (x : G.StationaryProfile)
    (action : G.PureStationaryAction) : ℝ :=
  ∏ state, G.productProbability (x state) (action state)

/-- A `B`-graph: one positive-probability arrow out of every state in `B`,
with every iterated path eventually leaving `B`. -/
structure ExitGraph (states : Set G.State) where
  action : G.State → G.JointAction
  target : G.State → G.State
  positive : ∀ state, state ∈ states →
    0 < (G.transition state (action state)).prob (target state)
  eventuallyOutside : ∀ state, state ∈ states →
    ∃ steps : ℕ, (target^[steps]) state ∉ states

/-- Equation (26): weight of a `B`-graph. -/
def graphWeight {states : Set G.State} (x : G.StationaryProfile)
    (graph : G.ExitGraph states) : ℝ :=
  ∏ state,
    if state ∈ states then
      G.productProbability (x state) (graph.action state) *
        (G.transition state (graph.action state)).prob
          (graph.target state)
    else 1

/-- A graph path starting at `source` first exits at `target`. -/
def ExitGraph.EndsAt {states : Set G.State}
    (graph : G.ExitGraph states) (source target : G.State) : Prop :=
  ∃ steps : ℕ,
    (∀ earlier, earlier < steps →
      (graph.target^[earlier]) source ∈ states) ∧
    (graph.target^[steps]) source = target ∧ target ∉ states

/-- Stationary first-exit law from `states`. -/
def IsStationaryExitLaw (x : G.StationaryProfile) (states : Set G.State)
    (source : G.State) (law : G.State → ℝ) : Prop :=
  ∀ target, target ∉ states →
    Tendsto
      (fun steps =>
        G.firstExitAtWithin (G.stationaryBehaviorProfile x) states target
          (G.initialHistory source) steps)
      atTop (nhds (law target))

/-- Equation (27), the Freidlin--Wentzell graph formula. -/
def GraphExitFormulaClaim : Prop :=
  ∀ (states : Set G.State) (x : G.StationaryProfile)
      (source target : G.State) (law : G.State → ℝ),
    source ∈ states → target ∉ states →
    G.IsStationaryExitLaw x states source law →
      law target =
        (∑ graph : G.ExitGraph states,
          if graph.EndsAt source target then G.graphWeight x graph else 0) /
        (∑ graph : G.ExitGraph states, G.graphWeight x graph)

/-- Open formal proof: equation (27) is cited from Freidlin and Wentzell.
The current file records the exact finite graph identity but does not recreate
its matrix-tree proof. -/
theorem graphExitFormula : G.GraphExitFormulaClaim := by
  sorry

end PaperGame

/-! ## Section 5.2: asymptotic ratios and maximal graphs -/

namespace PaperGame

variable (G : PaperGame ι)

/-- A sequence of absorbing stationary profiles with all action-probability
ratios convergent as the approximation parameter vanishes. -/
structure AsymptoticProfileData where
  epsilon : ℕ → ℝ
  epsilonPositive : ∀ n, 0 < epsilon n
  epsilonTendsToZero : Tendsto epsilon atTop (nhds 0)
  profile : ℕ → G.StationaryProfile
  absorbing : ∀ n state,
    Tendsto
      (fun steps =>
        G.kernelHitsAbsorbingWithin
          (fun s next => G.mixedTransitionProbability s (profile n s) next)
          state steps)
      atTop (nhds 1)
  supportIndependent : ∀ m n state who action,
    0 < (profile m state who).prob action ↔
      0 < (profile n state who).prob action
  ratioLimit : G.PureStationaryAction → G.PureStationaryAction → ENNReal
  ratiosConverge : ∀ first second,
    0 < G.stationaryPureProbability (profile 0) second →
      Tendsto
        (fun n =>
          ENNReal.ofReal (G.stationaryPureProbability (profile n) first) /
            ENNReal.ofReal (G.stationaryPureProbability (profile n) second))
        atTop (nhds (ratioLimit first second))
  limitProfile : G.StationaryProfile
  profileConverges : ∀ state who action,
    Tendsto (fun n => (profile n state who).prob action)
      atTop (nhds ((limitProfile state who).prob action))
  limitPayoff : G.StatePayoff
  payoffConverges : Prop
  exitLimit : Set G.State → G.State → G.State → ℝ
  exitLawsConverge : Prop

/-- Definition 5.1: communication under the asymptotic ratio data `theta`. -/
def CommunicatesUnderTheta (data : G.AsymptoticProfileData)
    (states : Set G.State) : Prop :=
  states ⊆ {state | ¬G.IsAbsorbingState state} ∧
    ∀ source, source ∈ states → ∀ target,
      target ∈ states → target ≠ source →
        data.exitLimit (states \ {target}) source target = 1

/-- A graph is maximal when no competing graph has asymptotically infinite
weight relative to it. -/
def IsMaximalGraph (data : G.AsymptoticProfileData)
    {states : Set G.State} (graph : G.ExitGraph states) : Prop :=
  ∀ other : G.ExitGraph states,
    ¬ Tendsto
      (fun n =>
        ENNReal.ofReal (G.graphWeight (data.profile n) other) /
          ENNReal.ofReal (G.graphWeight (data.profile n) graph))
      atTop atTop

/-- Lemma 5.2: only maximal graphs contribute to the limiting exit law. -/
def Lemma5_2Claim : Prop :=
  ∀ (data : G.AsymptoticProfileData) (states : Set G.State),
    G.CommunicatesUnderTheta data states →
      ∀ source, source ∈ states → ∀ target, target ∉ states →
        data.exitLimit states source target =
          Filter.lim atTop
            (fun n =>
              (∑ graph : G.ExitGraph states,
                if G.IsMaximalGraph data graph ∧ graph.EndsAt source target then
                  G.graphWeight (data.profile n) graph else 0) /
              (∑ graph : G.ExitGraph states,
                G.graphWeight (data.profile n) graph))

/-- Open formal proof: this is the asymptotic pruning of equation (27).
It needs a finite-sum ratio-limit lemma allowing infinite extended-real
ratios. -/
theorem lemma5_2 : G.Lemma5_2Claim := by
  sorry

/-- Equation (29) and the induced law `mu_(theta,C)` of the first exit used. -/
def FirstUsedExitLawClaim : Prop :=
  ∀ (data : G.AsymptoticProfileData) (states : Set G.State),
    G.CommunicatesUnderTheta data states →
      ∃ exitLaw : FiniteDistribution
          (G.Exit data.limitProfile states),
        (∀ source, source ∈ states →
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)) ∧
        ∀ target, target ∉ states →
          G.inducedExitStateProbability exitLaw target =
            data.exitLimit states (Classical.choose
              (Set.nonempty_iff_ne_empty.mpr (by
                intro hempty
                subst states
                simp at *))) target

/-- Open formal proof: equation (29) identifies actual exits with maximal
exit graphs.  Formalization requires a coupled first-exit/first-used-exit
stopping law. -/
theorem firstUsedExitLaw : G.FirstUsedExitLawClaim := by
  sorry

end PaperGame

/-! ## Section 5.3: constrained fixed points and the proof of Theorem 2.4 -/

namespace PaperGame

variable (G : PaperGame ι)

/-- The constrained profile set `X_epsilon`: every action has probability at
least `epsilon^2`. -/
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

/-- Equation (31): the approximate-best-reply fixed-point equation. -/
def SatisfiesConstrainedFixedPointEquation (epsilon : ℝ)
    (x : G.StationaryProfile) (payoff : G.StatePayoff) : Prop :=
  ∀ state who choice,
    (x state who).prob choice =
      Real.rpow epsilon (G.continuationCost x payoff state who choice) /
        ∑ alternative,
          Real.rpow epsilon
            (G.continuationCost x payoff state who alternative)

/-- Existence of the Brouwer fixed points `x_epsilon`. -/
def ConstrainedFixedPointClaim : Prop :=
  ∀ epsilon, 0 < epsilon → epsilon < 1 →
    ∃ x : G.StationaryProfile, ∃ payoff : G.StatePayoff,
      G.IsInConstrainedProfileSet epsilon x ∧
        G.SatisfiesConstrainedFixedPointEquation epsilon x payoff

/-- Open formal proof: continuity of the undiscounted absorbing payoff on
`X_epsilon` and Brouwer's theorem must be connected to the paper-local finite
profile simplex. -/
theorem constrainedFixedPoint : G.ConstrainedFixedPointClaim := by
  sorry

/-- Equation (32): harmonicity of each fixed point's undiscounted payoff. -/
def FixedPointHarmonicity (x : G.StationaryProfile)
    (payoff : G.StatePayoff) : Prop :=
  ∀ state who,
    G.mixedContinuationValue state (x state)
      (fun next => payoff next who) = payoff state who

/-- Lemma 5.3: the limiting payoff is at least every player's uniform
min--max value. -/
def Lemma5_3Claim : Prop :=
  ∀ minmax : ι → G.State → ℝ, G.IsUniformMinmaxValue minmax →
    ∀ payoff : G.StatePayoff,
      (∀ state who, 0 ≤ payoff state who) →
      (∀ state who (choice : G.Action who),
        G.mixedContinuationValue state
          (G.replaceMixedAction
            (fun _ => Classical.choice inferInstance) who
            { prob := fun action => if action = choice then 1 else 0
              nonnegative := by
                intro action
                split_ifs <;> norm_num
              total := by simp })
          (fun next => payoff next who) ≤ payoff state who) →
        ∀ state who, minmax who state ≤ payoff state who

/-- Open formal proof: the paper's maximum-principle contradiction uses the
uniform punishment characterization on a maximal state class.  That dynamic
min--max separation lemma is not yet formalized. -/
theorem lemma5_3 : G.Lemma5_3Claim := by
  sorry

/-- Overall cost of a graph: the sum of every player's continuation costs on
its arrows. -/
def graphCost (x : G.StationaryProfile) (payoff : G.StatePayoff)
    {states : Set G.State} (graph : G.ExitGraph states) : ℝ :=
  ∑ state,
    if state ∈ states then
      ∑ who,
        G.continuationCost x payoff state who (graph.action state who)
    else 0

/-- Cost of an exit, represented by a maximal graph using that exit. -/
def IsExitCost {x : G.StationaryProfile} {states : Set G.State}
    (data : G.AsymptoticProfileData)
    (payoff : G.StatePayoff) (exit : G.Exit x states)
    (cost : ℝ) : Prop :=
  ∃ graph : G.ExitGraph states,
    G.IsMaximalGraph data graph ∧
      graph.action exit.1.state = exit.1.action ∧
        G.graphCost x payoff graph = cost

/-- Lemma 5.4: all exits with positive limiting exit mass have equal cost. -/
def Lemma5_4Claim : Prop :=
  ∀ (data : G.AsymptoticProfileData) (states : Set G.State)
      (payoff : G.StatePayoff)
      (exitLaw : FiniteDistribution (G.Exit data.limitProfile states))
      (first second : G.Exit data.limitProfile states)
      (firstCost secondCost : ℝ),
    0 < exitLaw.prob first → 0 < exitLaw.prob second →
      G.IsExitCost data payoff first firstCost →
        G.IsExitCost data payoff second secondCost →
          firstCost = secondCost

/-- Open formal proof: this is the exponential graph-weight comparison
coming from equation (31), including the case of equal action costs. -/
theorem lemma5_4 : G.Lemma5_4Claim := by
  sorry

/-- Lemma 5.5: a zero-cost directed tree reaches any selected root inside a
communicating set. -/
def Lemma5_5Claim : Prop :=
  ∀ (data : G.AsymptoticProfileData) (states : Set G.State),
    G.CommunicatesUnderTheta data states →
      ∀ root, root ∈ states →
        ∃ graph : G.ExitGraph (states \ {root}),
          (∀ source, source ∈ states \ {root} →
            ∃ steps, (graph.target^[steps]) source = root) ∧
          G.graphCost data.limitProfile data.limitPayoff graph = 0

/-- Open formal proof: the paper extracts a directed spanning tree from an
arbitrarily close communicating perturbation and then proves every supported
arrow has zero continuation cost. -/
theorem lemma5_5 : G.Lemma5_5Claim := by
  sorry

/-- Corollary 5.6: joint exits have zero cost; a unilateral exit's cost is
its owner's continuation loss. -/
def Corollary5_6Claim : Prop :=
  ∀ (data : G.AsymptoticProfileData) (states : Set G.State)
      (exit : G.Exit data.limitProfile states) (cost : ℝ),
    G.IsExitCost data data.limitPayoff exit cost →
      (exit.IsJoint → cost = 0) ∧
      ∀ who, exit.IsUnilateral who →
        cost = data.limitPayoff exit.1.state who -
          G.exitContinuationValue exit data.limitPayoff who

/-- Open formal proof: this is the graph-splicing consequence of Lemma 5.5.
It awaits the formal maximal-graph/exit-use relation from Section 5.2. -/
theorem corollary5_6 : G.Corollary5_6Claim := by
  sorry

/-- The final Section 5 assertion: the asymptotic fixed-point data satisfy all
seven hypotheses of Proposition 3.8. -/
def Section5_3SufficientDataClaim : Prop :=
  G.IsPositive → G.IsRecursive →
    ∃ data : G.StationarySufficientData, True

/-- Open formal proof: conditions 1--5 use the limiting harmonicity and
min--max lemma; conditions 6--7 use Lemmas 5.4--5.5 and Corollary 5.6.
Statistical implementation then invokes Proposition 3.8. -/
theorem section5_3SufficientData : G.Section5_3SufficientDataClaim := by
  sorry

end PaperGame

end Literature.SolanAndVieille2002a
