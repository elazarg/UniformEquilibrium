import Mathlib

noncomputable section

open Filter
open scoped BigOperators

/-!
# Solan and Vieille 2002b — Correlated Equilibrium in Stochastic Games

Eilon Solan and Nicolas Vieille, *Games and Economic Behavior* 38 (2002),
362–399, DOI `10.1006/game.2001.0887`.

This is the paper identified as **Solan & Vieille 2002b** in the repository
bibliography.  Solan & Vieille 2002a is *Quitting Games—An Example*.

This file remains in `Literature/future/`.  It records the semantic core that
must be fixed before the paper's later theorem statements are promoted:

* finite nonempty action sets;
* autonomous and stationary private-signal devices;
* exits represented by a coalition action, not by an arbitrary completion;
* the conditioned exit law of equation (5), supported on `S \ C`;
* harmonic stationary evaluation `q γ = γ`, without an added stage payoff;
* the two-stage limit defining the asymptotic exit law;
* the exact cleaning operation and drift equations (19)–(21);
* the outsider-support condition in graph use; and
* the “sufficiently small ε” quantifier and positive-recursive absorbing
  reduction used by the constrained fixed-point construction.

The substantive existence proofs are deliberately not restated as Lean
`theorem`s here.  In particular, no arbitrary `Prop` field stands in for the
cleaning construction or for equations (19)–(21).  The printed Proposition
3.8 is also not promoted: its proof invokes positivity in the unilateral-exit
case although its printed statement is phrased for a general stochastic game.
-/

namespace Literature.SolanAndVieille2002b

/-- A finitely supported probability law.  No global finiteness assumption on
`α` is hidden in this carrier. -/
structure FiniteLaw (α : Type*) where
  support : Finset α
  mass : α → ℝ
  nonnegative : ∀ a, 0 ≤ mass a
  zero_off_support : ∀ {a}, a ∉ support → mass a = 0
  total : ∑ a in support, mass a = 1

namespace FiniteLaw

variable {α : Type*}

/-- Positive mass, the paper's notion of support. -/
def InSupport (law : FiniteLaw α) (a : α) : Prop :=
  0 < law.mass a

end FiniteLaw

/-- The finite stochastic-game data from Section 2.  Nonemptiness of every
action set is explicit; otherwise Theorem 2.3 is false even as a statement of
an ordinary strategic game. -/
structure PaperGame (ι : Type*) [Fintype ι] where
  State : Type*
  Action : ι → Type*
  stateFintype : Fintype State
  stateDecidableEq : DecidableEq State
  actionFintype : ∀ i, Fintype (Action i)
  actionDecidableEq : ∀ i, DecidableEq (Action i)
  actionNonempty : ∀ i, Nonempty (Action i)
  transition : State → (∀ i, Action i) → FiniteLaw State
  stagePayoff : State → (∀ i, Action i) → ι → ℝ
  payoffBound : ∀ state action who, |stagePayoff state action who| ≤ 1

attribute [instance] PaperGame.stateFintype PaperGame.stateDecidableEq
attribute [instance] PaperGame.actionFintype PaperGame.actionDecidableEq
attribute [instance] PaperGame.actionNonempty

namespace PaperGame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

abbrev JointAction := ∀ i, G.Action i
abbrev MixedAction := ∀ i, FiniteLaw (G.Action i)
abbrev StationaryProfile := G.State → G.MixedAction
abbrev StatePayoff := G.State → ι → ℝ

/-- Product probability of a pure action profile under a mixed action. -/
def jointMass (x : G.MixedAction) (action : G.JointAction) : ℝ :=
  ∏ i, (x i).mass (action i)

/-- The mixed transition kernel. -/
def mixedTransitionProbability (state : G.State) (x : G.MixedAction)
    (next : G.State) : ℝ :=
  ∑ action : G.JointAction,
    G.jointMass x action * (G.transition state action).mass next

/-- Expected one-stage payoff under a mixed action. -/
def mixedStagePayoff (state : G.State) (x : G.MixedAction) (who : ι) : ℝ :=
  ∑ action : G.JointAction,
    G.jointMass x action * G.stagePayoff state action who

/-- A state is absorbing exactly as in Section 2. -/
def IsAbsorbingState (state : G.State) : Prop :=
  ∀ action : G.JointAction, (G.transition state action).mass state = 1

/-- Recursive games have zero stage payoff at every nonabsorbing state. -/
def IsRecursive : Prop :=
  ∀ state, ¬ G.IsAbsorbingState state →
    ∀ action : G.JointAction, ∀ who, G.stagePayoff state action who = 0

/-- Positivity is required at every absorbing state, action, and player. -/
def IsPositive : Prop :=
  ∀ state, G.IsAbsorbingState state →
    ∀ action : G.JointAction, ∀ who, 0 < G.stagePayoff state action who

/-- The class used in Section 5. -/
def IsPositiveRecursive : Prop :=
  G.IsPositive ∧ G.IsRecursive

/-- Finite-horizon probability of having reached `target`. -/
def hitWithin (kernel : G.State → G.State → ℝ) (target : Finset G.State) :
    ℕ → G.State → ℝ
  | 0, state => if state ∈ target then 1 else 0
  | horizon + 1, state =>
      if state ∈ target then 1
      else ∑ next, kernel state next * G.hitWithin kernel target horizon next

/-- Almost-sure eventual hitting, expressed as the limit of finite-horizon
hitting probabilities. -/
def HitsEventually (kernel : G.State → G.State → ℝ)
    (target : Finset G.State) : Prop :=
  ∀ state,
    Tendsto (fun horizon => G.hitWithin kernel target horizon state)
      atTop (nhds 1)

/-- The finite set of absorbing states. -/
noncomputable def absorbingStates : Finset G.State := by
  classical
  exact Finset.univ.filter G.IsAbsorbingState

/-- A stationary profile is fully mixed. -/
def IsFullyMixed (x : G.StationaryProfile) : Prop :=
  ∀ state who action, 0 < (x state who).mass action

/-- A stationary profile reaches the absorbing states almost surely. -/
def IsAbsorbingProfile (x : G.StationaryProfile) : Prop :=
  G.HitsEventually
    (fun state next => G.mixedTransitionProbability state (x state) next)
    G.absorbingStates

/-- Section 5 first reduces to games in which every fully mixed stationary
profile is absorbing. -/
def FullyMixedProfilesAbsorb : Prop :=
  ∀ x : G.StationaryProfile, G.IsFullyMixed x → G.IsAbsorbingProfile x

/-- Harmonicity of a stationary continuation payoff.  This is equation (32):
`q_{s,x} γ = γ_s`.  There is no stage-payoff summand. -/
def IsHarmonic (x : G.StationaryProfile) (value : G.StatePayoff) : Prop :=
  ∀ state who,
    (∑ next,
      G.mixedTransitionProbability state (x state) next * value next who) =
      value state who

/-- The continuation-value inequality against a pure unilateral action. -/
noncomputable def unilateralTransitionProbability
    (x : G.StationaryProfile) (state : G.State) (who : ι)
    (chosen : G.Action who) (next : G.State) : ℝ := by
  classical
  exact
    ∑ action : G.JointAction,
      (if action who = chosen then
        (∏ other in Finset.univ.erase who,
          (x state other).mass (action other)) *
          (G.transition state action).mass next
       else 0)

/-- Condition 2(b) of Proposition 3.8. -/
def NoProfitablePureContinuationDeviation
    (x : G.StationaryProfile) (value : G.StatePayoff) : Prop :=
  ∀ state who (chosen : G.Action who),
    (∑ next,
      G.unilateralTransitionProbability x state who chosen next *
        value next who) ≤ value state who

end PaperGame

/-! ## Definition 2.1: private autonomous and stationary devices -/

/-- An autonomous device chooses the stage-`n` joint signal from the history
of earlier joint signals only.  Stages are zero-indexed here. -/
structure AutonomousDevice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : PaperGame ι) where
  Signal : ℕ → ι → Type*
  signalFintype : ∀ n i, Fintype (Signal n i)
  signalDecidableEq : ∀ n i, DecidableEq (Signal n i)
  law : ∀ n,
    (∀ previous : Fin n, ∀ i, Signal previous.1 i) →
      FiniteLaw (∀ i, Signal n i)

attribute [instance] AutonomousDevice.signalFintype
attribute [instance] AutonomousDevice.signalDecidableEq

/-- A stationary device uses one fixed finite signal space and one fixed law
at every date. -/
structure StationaryDevice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : PaperGame ι) where
  Signal : ι → Type*
  signalFintype : ∀ i, Fintype (Signal i)
  signalDecidableEq : ∀ i, DecidableEq (Signal i)
  law : FiniteLaw (∀ i, Signal i)

attribute [instance] StationaryDevice.signalFintype
attribute [instance] StationaryDevice.signalDecidableEq

namespace StationaryDevice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {G : PaperGame ι}

/-- A stationary device is an autonomous device whose law ignores all prior
signals and is independent of the date. -/
def toAutonomous (device : StationaryDevice G) : AutonomousDevice G where
  Signal := fun _ => device.Signal
  signalFintype := fun _ => device.signalFintype
  signalDecidableEq := fun _ => device.signalDecidableEq
  law := fun _ _ => device.law

end StationaryDevice

namespace PaperGame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- A base-game history with `n` completed actions and `n+1` observed states. -/
structure History (n : ℕ) where
  state : Fin (n + 1) → G.State
  action : Fin n → G.JointAction

/-- A correlated profile in the base game, Section 3.1. -/
abbrev CorrelatedProfile :=
  ∀ n, G.History n → FiniteLaw G.JointAction

end PaperGame

namespace AutonomousDevice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {G : PaperGame ι}
variable (device : AutonomousDevice G)

/-- The private history observed by `who`: public states and actions, together
with that player's own signals. -/
structure PrivateHistory (who : ι) (n : ℕ) extends G.History n where
  signal : ∀ stage : Fin (n + 1), device.Signal stage.1 who

abbrev Strategy (who : ι) :=
  ∀ n, device.PrivateHistory who n → FiniteLaw (G.Action who)

abbrev Profile := ∀ who, device.Strategy who

end AutonomousDevice

/-!
Definition 2.2 quantifies, for every positive error, over a device and one
behavioral profile that is an approximate equilibrium and has approximately
the same state-indexed payoff in all sufficiently long Cesàro games and all
sufficiently patient discounted games.  A complete induced-law evaluator for
the dependent private-signal histories above has not yet been integrated, so
the definition and Theorems 2.3–2.4 remain source claims rather than being
hidden behind arbitrary payoff functions.
-/

/-! ## Section 3.4: communicating sets and exits -/

namespace PaperGame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- Support inclusion for perturbations of a stationary profile. -/
def IsPerturbation (x y : G.StationaryProfile) : Prop :=
  ∀ state who action,
    0 < (x state who).mass action → 0 < (y state who).mass action

/-- Stability of a finite set under a stationary profile. -/
def IsStableUnder (x : G.StationaryProfile) (states : Finset G.State) : Prop :=
  ∀ state, state ∈ states →
    ∑ next in states,
      G.mixedTransitionProbability state (x state) next = 1

/-- The paper's communicating-set definition, stated through almost-sure
hitting under a perturbation that keeps the set stable. -/
def CommunicatesUnder (x : G.StationaryProfile)
    (states : Finset G.State) : Prop :=
  ∀ target, target ∈ states →
    ∃ y : G.StationaryProfile,
      G.IsPerturbation x y ∧
      G.IsStableUnder y states ∧
      ∀ initial, initial ∈ states →
        Tendsto
          (fun horizon =>
            G.hitWithin
              (fun state next =>
                G.mixedTransitionProbability state (y state) next)
              {target} horizon initial)
          atTop (nhds 1)

/-- The paper's coalition action `aᴸ`.  Actions of outsiders are not stored. -/
abbrev CoalitionAction (coalition : Finset ι) :=
  ∀ who : ↥coalition, G.Action who.1

/-- A full action matches the coalition component of an exit. -/
def MatchesCoalition (action : G.JointAction) (coalition : Finset ι)
    (coalitionAction : G.CoalitionAction coalition) : Prop :=
  ∀ who : ↥coalition, action who.1 = coalitionAction who

/-- Outsiders use actions in the support of the reference profile. -/
def OutsidersSupported (x : G.StationaryProfile) (state : G.State)
    (coalition : Finset ι) (action : G.JointAction) : Prop :=
  ∀ who, who ∉ coalition → 0 < (x state who).mass (action who)

/-- Weight of a pure completion of `(x⁻ᴸ,aᴸ)`. -/
noncomputable def coalitionCompletionMass
    (x : G.StationaryProfile) (state : G.State)
    (coalition : Finset ι) (coalitionAction : G.CoalitionAction coalition)
    (action : G.JointAction) : ℝ := by
  classical
  exact
    if G.MatchesCoalition action coalition coalitionAction then
      ∏ who in Finset.univ.filter (fun who => who ∉ coalition),
        (x state who).mass (action who)
    else 0

/-- Transition probability under `(x⁻ᴸ,aᴸ)`. -/
noncomputable def exitTransitionProbability
    (x : G.StationaryProfile) (state : G.State)
    (coalition : Finset ι) (coalitionAction : G.CoalitionAction coalition)
    (next : G.State) : ℝ :=
  ∑ action : G.JointAction,
    G.coalitionCompletionMass x state coalition coalitionAction action *
      (G.transition state action).mass next

/-- Probability of leaving `states` under `(x⁻ᴸ,aᴸ)`. -/
noncomputable def exitOutsideProbability
    (x : G.StationaryProfile) (states : Finset G.State) (state : G.State)
    (coalition : Finset ι) (coalitionAction : G.CoalitionAction coalition) : ℝ := by
  classical
  exact
    ∑ next in Finset.univ.filter (fun next => next ∉ states),
      G.exitTransitionProbability x state coalition coalitionAction next

/-- Definition 3.5.  Minimality is with respect to restricting `aᴸ` to a
strict subcoalition. -/
structure Exit (x : G.StationaryProfile) (states : Finset G.State) where
  source : G.State
  coalition : Finset ι
  action : G.CoalitionAction coalition
  source_mem : source ∈ states
  coalition_nonempty : coalition.Nonempty
  leaves : 0 < G.exitOutsideProbability x states source coalition action
  minimal :
    ∀ smaller : Finset ι, ∀ hsub : smaller ⊆ coalition,
      smaller ≠ coalition →
        G.exitOutsideProbability x states source smaller
          (fun who => action ⟨who.1, hsub who.2⟩) = 0

/-- Denominator in equation (5). -/
noncomputable def inducedExitDenominator
    {x : G.StationaryProfile} {states : Finset G.State}
    (law : FiniteLaw (G.Exit x states)) : ℝ :=
  ∑ exit in law.support,
    law.mass exit *
      G.exitOutsideProbability x states exit.source exit.coalition exit.action

/-- Equation (5).  The conditioned exit-state law is zero on `states` and is
normalized only over states outside it. -/
noncomputable def inducedExitStateProbability
    {x : G.StationaryProfile} {states : Finset G.State}
    (law : FiniteLaw (G.Exit x states)) (next : G.State) : ℝ := by
  classical
  exact
    if next ∈ states then 0
    else
      (∑ exit in law.support,
        law.mass exit *
          G.exitTransitionProbability x exit.source exit.coalition exit.action next) /
        G.inducedExitDenominator law

@[simp] theorem inducedExitStateProbability_eq_zero_of_mem
    {x : G.StationaryProfile} {states : Finset G.State}
    (law : FiniteLaw (G.Exit x states)) {next : G.State}
    (hnext : next ∈ states) :
    G.inducedExitStateProbability law next = 0 := by
  simp [inducedExitStateProbability, hnext]

/-- Condition 5 of Proposition 3.8, using the conditioned law from equation
(5), not the unconditioned transition mass. -/
def ExitLawPreservesValue
    {x : G.StationaryProfile} {states : Finset G.State}
    (law : FiniteLaw (G.Exit x states)) (value : G.StatePayoff) : Prop :=
  ∀ state, state ∈ states → ∀ who,
    (∑ next,
      G.inducedExitStateProbability law next * value next who) =
      value state who

/-- A disjoint block system is represented by a partial block index.  The
specification makes membership unique. -/
structure ExitBlockSystem (x : G.StationaryProfile) where
  Block : Type*
  blockFintype : Fintype Block
  blockDecidableEq : DecidableEq Block
  states : Block → Finset G.State
  blockOf : G.State → Option Block
  blockOf_spec : ∀ state block, blockOf state = some block ↔ state ∈ states block
  exitLaw : ∀ block, FiniteLaw (G.Exit x (states block))

attribute [instance] ExitBlockSystem.blockFintype
attribute [instance] ExitBlockSystem.blockDecidableEq

/-- Equation (7): blocks use their conditioned exit laws; all remaining
states use the stationary transition kernel. -/
noncomputable def inducedKernel
    {x : G.StationaryProfile} (system : G.ExitBlockSystem x)
    (state next : G.State) : ℝ :=
  match system.blockOf state with
  | none => G.mixedTransitionProbability state (x state) next
  | some block => G.inducedExitStateProbability (system.exitLaw block) next

/-- Transience of a set under a stationary profile.  This hypothesis is
required by the graph-exit formula (27). -/
def IsTransientUnder (x : G.StationaryProfile)
    (states : Finset G.State) : Prop :=
  ∀ initial, initial ∈ states →
    Tendsto
      (fun horizon =>
        G.hitWithin
          (fun state next =>
            G.mixedTransitionProbability state (x state) next)
          (Finset.univ \ states) horizon initial)
      atTop (nhds 1)

end PaperGame

/-!
Equation (27), the ratio of sums of `B`-graph weights, is valid only under
`PaperGame.IsTransientUnder x B`.  The earlier draft omitted that premise.
The full graph enumeration and proof are not promoted in this future record.
-/

/-! ## Section 4.2: exact cleaning and equations (19)–(21) -/

namespace PaperGame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- States with the same full min–max vector. -/
noncomputable def equalValueClass (value : G.StatePayoff) (state : G.State) :
    Finset G.State := by
  classical
  exact Finset.univ.filter (fun next => ∀ who, value next who = value state who)

/-- The set `(S \ C_s) ∪ changing` used in Section 4.2. -/
noncomputable def escapeSet (value : G.StatePayoff)
    (changing : Finset G.State) (state : G.State) : Finset G.State := by
  classical
  exact (Finset.univ \ G.equalValueClass value state) ∪ changing

/-- `B₁`: pure joint actions that can reach the escape set with positive
probability. -/
noncomputable def initiallyBadActions (value : G.StatePayoff)
    (changing : Finset G.State) (state : G.State) : Finset G.JointAction := by
  classical
  exact
    Finset.univ.filter (fun action =>
      0 < ∑ next in G.escapeSet value changing state,
        (G.transition state action).mass next)

/-- One step of the closure `Bₙ ↦ Bₙ₊₁` from Section 4.2.2. -/
noncomputable def badActionClosureStep (epsilon : ℝ)
    (law : FiniteLaw G.JointAction) (bad : Finset G.JointAction) :
    Finset G.JointAction := by
  classical
  let exponent : ℝ := ((2 * Fintype.card G.JointAction : ℕ) : ℝ)⁻¹
  let scale : ℝ := Real.rpow epsilon exponent
  exact
    bad ∪ Finset.univ.filter (fun action =>
      ∃ badAction ∈ bad, law.mass action ≤ law.mass badAction / scale)

/-- The stabilized closure is reached after at most `|A|` steps. -/
noncomputable def badActionClosure (epsilon : ℝ)
    (law : FiniteLaw G.JointAction) (initial : Finset G.JointAction) :
    Finset G.JointAction :=
  (G.badActionClosureStep epsilon law)^[Fintype.card G.JointAction] initial

/-- Total mass retained after deleting the closed bad set. -/
noncomputable def retainedMass (epsilon : ℝ)
    (law : FiniteLaw G.JointAction) (initial : Finset G.JointAction) : ℝ := by
  classical
  exact
    ∑ action : G.JointAction,
      if action ∈ G.badActionClosure epsilon law initial then 0
      else law.mass action

/-- The paper's cleaned mass: delete the closed bad set and normalize. -/
noncomputable def cleanedMass (epsilon : ℝ)
    (law : FiniteLaw G.JointAction) (initial : Finset G.JointAction)
    (action : G.JointAction) : ℝ := by
  classical
  exact
    if action ∈ G.badActionClosure epsilon law initial then 0
    else law.mass action / G.retainedMass epsilon law initial

/-- A concrete statement that a proposed law is exactly the paper's cleaning.
This replaces the earlier unconstrained `isPaperCleaning : Prop` field. -/
def IsPaperCleaning (epsilon : ℝ) (law : FiniteLaw G.JointAction)
    (initial : Finset G.JointAction) (cleaned : G.JointAction → ℝ) : Prop :=
  0 < G.retainedMass epsilon law initial ∧
  (∀ action, cleaned action = G.cleanedMass epsilon law initial action) ∧
  (∀ action, 0 ≤ cleaned action) ∧
  (∑ action, cleaned action) = 1

/-- `n`-step transition probability of a finite kernel. -/
def kernelPower (kernel : G.State → G.State → ℝ) :
    ℕ → G.State → G.State → ℝ
  | 0, state, next => if state = next then 1 else 0
  | steps + 1, state, next =>
      ∑ middle, kernel state middle * G.kernelPower kernel steps middle next

/-- Probability that the value vector differs after exactly `steps` block
transitions. -/
noncomputable def valueChangeProbabilityAt
    (kernel : G.State → G.State → ℝ) (value : G.StatePayoff)
    (state : G.State) (steps : ℕ) : ℝ := by
  classical
  exact
    ∑ next in Finset.univ.filter (fun next =>
      ∃ who, value next who ≠ value state who),
      G.kernelPower kernel steps state next

/-- Expected next block value. -/
def expectedNextValue (kernel : G.State → G.State → ℝ)
    (value : G.StatePayoff) (state : G.State) (who : ι) : ℝ :=
  ∑ next, kernel state next * value next who

/-- Equation (19), with its two separate assertions. -/
def Equation19 (kernel : G.State → G.State → ℝ)
    (value : G.StatePayoff) (changing : Finset G.State)
    (omega : ℝ) : Prop :=
  ∀ state, state ∈ changing →
    (∀ who, value state who ≤ G.expectedNextValue kernel value state who) ∧
    ∃ steps, 1 ≤ steps ∧ steps ≤ Fintype.card G.State ∧
      omega ≤ G.valueChangeProbabilityAt kernel value state steps

/-- Equation (20): the value vector is unchanged almost surely from a good
state. -/
def Equation20 (kernel : G.State → G.State → ℝ)
    (value : G.StatePayoff) (good : Finset G.State) : Prop :=
  ∀ state, state ∈ good →
    ∑ next in G.equalValueClass value state, kernel state next = 1

/-- The error exponent appearing in equation (21). -/
def equation21Error (epsilon : ℝ) : ℝ :=
  epsilon ^ ((Fintype.card ι + 1) * Fintype.card G.State + 1)

/-- Equation (21): an almost-submartingale inequality and a lower bound on
one-step value change. -/
def Equation21 (kernel : G.State → G.State → ℝ)
    (value : G.StatePayoff) (bad : Finset G.State) (epsilon : ℝ) : Prop :=
  ∀ state, state ∈ bad →
    (∀ who,
      value state who - G.equation21Error epsilon ≤
        G.expectedNextValue kernel value state who) ∧
    epsilon ≤ G.valueChangeProbabilityAt kernel value state 1

/-- The exact drift system used by Lemma 4.5. -/
def PaperDriftSystem (kernel : G.State → G.State → ℝ)
    (value : G.StatePayoff) (changing good bad : Finset G.State)
    (epsilon omega : ℝ) : Prop :=
  G.Equation19 kernel value changing omega ∧
  G.Equation20 kernel value good ∧
  G.Equation21 kernel value bad epsilon

end PaperGame

/-!
Lemmas 4.4 and 4.5 are not declared here.  Their hypotheses are the concrete
cleaning formula and `PaperDriftSystem` above; replacing those hypotheses by
uninterpreted propositions would strengthen the lemmas and can make them
false.
-/

/-! ## Section 5.1–5.2: graphs, exits, and the order of limits -/

namespace PaperGame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- One outgoing labelled arrow per state of a `B`-graph. -/
structure BGraph (states : Finset G.State) where
  arrow : G.State → Option (G.JointAction × G.State)
  domain : ∀ state, arrow state ≠ none ↔ state ∈ states
  positive : ∀ state action next,
    arrow state = some (action, next) →
      0 < (G.transition state action).mass next
  reachesOutside : ∀ state, state ∈ states →
    ∃ steps,
      let successor : G.State → G.State := fun current =>
        match arrow current with
        | none => current
        | some (_, next) => next
      (successor^[steps] state) ∉ states

/-- A graph uses an exit only when its coalition component agrees and every
outsider action lies in the support of `x⁻ᴸ`.  No equality with an arbitrary
stored outsider completion is required. -/
def GraphUsesExit {x : G.StationaryProfile} {states : Finset G.State}
    (graph : G.BGraph states) (exit : G.Exit x states) : Prop :=
  ∃ action next,
    graph.arrow exit.source = some (action, next) ∧
    G.MatchesCoalition action exit.coalition exit.action ∧
    G.OutsidersSupported x exit.source exit.coalition action ∧
    next ∉ states

/-- The graph-exit ratio of equation (27) is meaningful only under this
explicit package. -/
structure GraphExitFormulaPremises (x : G.StationaryProfile)
    (states : Finset G.State) where
  transient : G.IsTransientUnder x states

end PaperGame

/-- Correct order of limits for the asymptotic exit law.  For each profile
`profileIndex`, first take the horizon to infinity; only then take the profile
index to infinity.  This rules out the invalid diagonal `horizon = index`.
-/
def HasTwoStageExitLimit {Exit : Type*}
    (firstExitUseWithin : ℕ → ℕ → Exit → ℝ) (limitLaw : Exit → ℝ) : Prop :=
  ∃ eventual : ℕ → Exit → ℝ,
    (∀ profileIndex exit,
      Tendsto
        (fun horizon => firstExitUseWithin profileIndex horizon exit)
        atTop (nhds (eventual profileIndex exit))) ∧
    ∀ exit,
      Tendsto (fun profileIndex => eventual profileIndex exit)
        atTop (nhds (limitLaw exit))

/-!
The paper's `μ_{θ,C}` is an instance of `HasTwoStageExitLimit`: under each
absorbing stationary profile `x_ε`, one first takes the eventual law of the
first exit used, and then lets `ε → 0`.  A hazard `2⁻ⁿ` shows why a diagonal
“exit within `n` steps under profile `n`” is not equivalent.
-/

/-! ## Section 5.3: the constrained fixed-point statement -/

namespace PaperGame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : PaperGame ι)

/-- The constrained simplex `X_ε`. -/
def InConstrainedSimplex (epsilon : ℝ) (x : G.StationaryProfile) : Prop :=
  ∀ state who action, epsilon ^ 2 ≤ (x state who).mass action

/-- A sufficient smallness condition for equation (31) to map into `X_ε`.
It implies `ε / |Aᵢ| ≥ ε²` for every player. -/
def IsSmallForActionSets (epsilon : ℝ) : Prop :=
  0 < epsilon ∧ epsilon < 1 ∧
  ∀ who, epsilon ≤ ((Fintype.card (G.Action who) : ℝ))⁻¹

abbrev StationaryValue := G.StationaryProfile → G.StatePayoff

/-- The actual stationary evaluation required by Section 5.  Harmonicity is
`q γ = γ`; adding the stage payoff would be inconsistent at positive
absorbing states. -/
def IsStationaryValue (value : G.StationaryValue) : Prop :=
  ∀ x, G.IsAbsorbingProfile x →
    G.IsHarmonic x (value x) ∧
    ∀ state, G.IsAbsorbingState state → ∀ who,
      value x state who = G.mixedStagePayoff state (x state) who

/-- Continuation payoff after a pure action of one player. -/
def pureContinuationValue (value : G.StationaryValue)
    (x : G.StationaryProfile) (state : G.State) (who : ι)
    (chosen : G.Action who) : ℝ :=
  ∑ next,
    G.unilateralTransitionProbability x state who chosen next *
      value x next who

/-- Best pure continuation payoff in equation (30). -/
noncomputable def bestPureContinuationValue (value : G.StationaryValue)
    (x : G.StationaryProfile) (state : G.State) (who : ι) : ℝ :=
  sSup (Set.range fun chosen : G.Action who =>
    G.pureContinuationValue value x state who chosen)

/-- Continuation cost (30). -/
noncomputable def continuationCost (value : G.StationaryValue)
    (x : G.StationaryProfile) (state : G.State) (who : ι)
    (chosen : G.Action who) : ℝ :=
  G.bestPureContinuationValue value x state who -
    G.pureContinuationValue value x state who chosen

/-- Fixed-point equation (31), written exactly with `ε ^ cost`. -/
def SatisfiesApproximateBestReplyEquation (value : G.StationaryValue)
    (epsilon : ℝ) (x : G.StationaryProfile) : Prop :=
  ∀ state who (chosen : G.Action who),
    (x state who).mass chosen =
      Real.rpow epsilon (G.continuationCost value x state who chosen) /
        (∑ alternative : G.Action who,
          Real.rpow epsilon
            (G.continuationCost value x state who alternative))

/-- The quantifier and scope of the Section 5.3 construction.  The paper
asserts the fixed point only for all sufficiently small positive `ε`, after
restricting to positive recursive games and making the absorbing reduction.
-/
def ConstrainedFixedPointClaim (value : G.StationaryValue) : Prop :=
  G.IsPositiveRecursive →
  G.FullyMixedProfilesAbsorb →
  G.IsStationaryValue value →
  ∃ epsilonZero : ℝ, 0 < epsilonZero ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonZero →
      G.IsSmallForActionSets epsilon ∧
      ∃ x : G.StationaryProfile,
        G.InConstrainedSimplex epsilon x ∧
        G.SatisfiesApproximateBestReplyEquation value epsilon x

end PaperGame

/-!
## Remaining paper claims

* Theorem 2.3: every finite stochastic game has a uniform autonomous
  correlated-equilibrium payoff.
* Theorem 2.4: every positive recursive game has a uniform stationary
  correlated-equilibrium payoff, with one stationary device independent of
  the requested error.

Both remain paper-only in this future record.  Promotion requires a concrete
induced-law semantics for the private devices and a corrected, fully checked
route through Proposition 3.8, Lemmas 4.4–4.5, the graph formula under
transience, the nested asymptotic exit law, and the constrained fixed point.
-/

end Literature.SolanAndVieille2002b
