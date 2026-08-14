/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Equilibrium.Uniform

/-!
# The uniform-equilibrium existence conjecture

This file records **the central open problem of stochastic game theory**:
every finite stochastic game admits a uniform equilibrium payoff from every
initial state.

It is separated from `Uniform.lean`, which carries the definitions and the
proved semantic/quantitative equivalence. The open claim is represented by a
definition of a proposition, not by an assumed theorem.

## Open declarations

`uniformDeviationCapConstructorConjecture` is the quantitative statement of
the conjecture. It is equivalent to the semantic form by
`hasUniformDeviationCapConstructor_iff`. The lemmas below record the semantic
consequences conditionally, without introducing a proof of the conjecture.

Known cases: two-player zero-sum games (Mertens--Neyman 1981), two-player games
(Vieille 2000), three-player absorbing games (Solan, *Three-Player Absorbing
Games*, MOR 24(3):669-698, 1999; verified against Solan's own doctoral
dissertation, the MOR journal PDF itself unread), and various
structured classes.  The general `n`-player case is open.

The finite-quitting case is stated separately in
`Quitting.Conjecture.Basic`. Discharging it would **not** discharge this file:
quitting games are a strict subclass, and no reduction from arbitrary finite
stochastic games to them is known.

## Scope: action sets are state-independent

`StochasticGame.Act : ι → Type` does not depend on the state, so the statement
below is the conjecture for finite stochastic games whose action sets are the
same at every state. A naive reduction from state-dependent action sets by
padding is **not** semantics-preserving for the present perfect-monitoring
behavioral notion: duplicate illegal labels can act as a public randomization
device. `PaddedDuplicateLotterySeparation.lean` gives a finite counterexample
to the claimed two-way transfer. A faithful extension therefore needs either
state-dependent action types or a semantics that observes only normalized
legal actions. Until one of those routes is formalized, the statement is the
conjecture for the state-independent class rather than for every textbook
presentation of a finite stochastic game.  Quitting games are unaffected:
their action set is `Bool` at every state.

## The nearest claimed counterexample is retracted

R. S. Simon, *A Stochastic Game without Approximate Equilibria*,
arXiv:2310.04217 (2023), announced a four-player "Mousetrap" with finitely many
states and actions and no approximate equilibria.  **It was withdrawn by its
author on 20 October 2023, fourteen days after posting, with the comment "The
proof is flawed."**  There is no published version and no repaired one.

Two independent readings of the withdrawn preprint agree on what it would have
cost us.  **Three defences a reader might reach for do not work.**  Its state space is
finite -- the paper's one-line justification is a non-sequitur, but the claim
holds for its numbers, since every stage payoff lies in `(1/10^4)ℤ` and the
totals are boxed.  Its payoff *is* recastable as a limit average of stage
payoffs; the one non-sum term is the most limit-average object in the game.
And perfect monitoring genuinely survives the stage-combining reduction -- the
cat's `102^101` action set is the standard agent-normal-form encoding of an
informational advantage, not a leak.  Do not cite finiteness, payoff shape, or
monitoring as reasons this statement is out of reach.

**One defence does work, and it is narrow.**  This file's notion is
`lim_T E[(1/T)Σ]` under a `∀T ≥ T₀` quantifier; the non-existence claim was
about `E[liminf]` on infinite plays.  Carrying an upper bound across needs
Fatou in the direction it does not go: `E[liminf] ≤ lim E` is the only
inequality available, and the on-path half needs the reverse.  Simon flags the
same distinction himself, noting his argument fails if `limsup` replaces
`liminf`.  So the escape is the *equilibrium notion*, not the model class;
closing that gap in either direction is a separate formalization obligation.

`arxiv.org/pdf/2310.04217` still serves the withdrawn v1, so a fetched PDF
looks current.  The Atom API's version list and `<arxiv:comment>` are
authoritative.
-/

namespace GameTheory

namespace StochasticGame

variable {ι : Type}

/-- Quantitative statement of the uniform-equilibrium existence problem.

This is the proof-construction waist at which analytic hierarchy,
public-response, coupling, and sublinear-ledger arguments meet. This definition
states the proposition but supplies no proof. -/
def uniformDeviationCapConstructorConjecture (G : StochasticGame ι)
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (s₀ : G.State) : Prop :=
  ∃ v : Payoff ι, G.HasUniformDeviationCapConstructor s₀ v

/-- **The uniform equilibrium existence problem.**

Every stochastic game with finitely many players, finitely many states, and
finitely many nonempty action sets admits a uniform equilibrium payoff from
every initial state.

This is the central open problem of stochastic game theory.  Known cases:
two-player zero-sum games (Mertens–Neyman 1981), two-player games
(Vieille 2000), three-player absorbing games (Solan, *Three-Player Absorbing
Games*, MOR 24(3):669-698, 1999; verified against Solan's own doctoral
dissertation, the MOR journal PDF itself unread), and various
structured classes (recursive games, quitting games under conditions).  The
general n-player case is open. Given the quantitative conjecture as a
hypothesis, this theorem derives the equivalent semantic statement without
weakening it. -/
theorem exists_uniformEquilibriumPayoff_of_conjecture (G : StochasticGame ι)
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (s₀ : G.State)
    (hconjecture : G.uniformDeviationCapConstructorConjecture s₀) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  obtain ⟨v, hv⟩ := hconjecture
  exact ⟨v, (G.hasUniformDeviationCapConstructor_iff s₀ v).mp hv⟩

/-- Conditional on the conjecture, for every `ε > 0` some behavior profile is
a uniform ε-equilibrium. -/
theorem exists_isUniformεEquilibrium_of_conjecture (G : StochasticGame ι)
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (s₀ : G.State)
    (hconjecture : G.uniformDeviationCapConstructorConjecture s₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : G.BehaviorProfile, G.IsUniformεEquilibrium s₀ ε σ := by
  obtain ⟨v, hv⟩ := G.exists_uniformEquilibriumPayoff_of_conjecture s₀ hconjecture
  obtain ⟨σ, T₀, h⟩ := hv ε hε
  exact ⟨σ, T₀, fun T hT => (h T hT).1⟩


end StochasticGame

end GameTheory
