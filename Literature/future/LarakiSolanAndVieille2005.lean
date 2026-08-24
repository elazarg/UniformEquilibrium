/-!
# R. Laraki, E. Solan and N. Vieille, "Continuous-Time Games of Timing" (2005)

Bibliography label: Laraki--Solan--Vieille 2005.

Published source: R. Laraki, E. Solan and N. Vieille, *Continuous-Time Games of
Timing*, Journal of Economic Theory 120(2) (2005), 206--238.
DOI: `https://doi.org/10.1016/j.jet.2004.02.001`.

Audited open version: CMSEMS Discussion Paper 1363, dated January 3, 2003,
`https://www.kellogg.northwestern.edu/research/math/papers/1363.pdf`.
The relevant source locations are Sections 1.1--1.3 (model and equilibrium
notions), Section 2.2 (the three-player counterexample), and Section 6
(continuous-to-discrete discretization and information extensions).

This file is a prose source note in `Literature/future/`.  It states no Lean
version of the paper's equilibrium theorem or counterexample.

## Exact model and strategy scope

The paper's baseline game has a finite player set.  For every nonempty stopping
coalition `S`, it has a deterministic, bounded, continuous terminal-payoff
function `u_S : [0, infinity) -> R^I`, and every player has a nonnegative
discount rate.  A pure strategy is one time in `[0, infinity]`; infinity means
never acting.  The first time chosen by anyone terminates the game, and the
players choosing that minimum time form the terminal coalition.  Nontermination
pays zero.

A mixed strategy is a probability law on `[0, infinity]`.  A profile uses the
product of the players' laws, so their randomizations are independent.  The
paper's Nash epsilon-equilibrium permits every unilateral mixed-law deviation;
it notes that testing pure-time deviations is equivalent.  Its additional
"super-strategy" is a consistent family of such laws, one for every starting
time, introduced to define subgame-perfect epsilon-equilibrium.  The
counterexample in Section 2.2 already excludes ordinary Nash
epsilon-equilibrium and does not rely on the super-strategy refinement.

The baseline model is complete-information and deterministic: there is no
external payoff process or nontrivial filtration.  It may therefore be
described as the trivial-filtration case, but that phrase should not obscure
the paper's actual formulation.  Section 6 separately discusses partial
extensions to public stochastic payoff processes.

## What Section 2.2 proves

The counterexample has exactly three players and is zero-sum.  Indices are read
modulo three.  Its terminal-payoff functions are constant.  If player `i` stops
alone, the cyclic payoffs to `(i, i+1, i+2)` are `(1, 0, -1)`.  If exactly
`i` and `i+1` stop, those payoffs are `(0, -1, 1)`.  If all three stop, all
payoffs are zero.

The players have one common discount rate `delta >= 0`; the proof is independent
of its value and explicitly includes the undiscounted case `delta = 0`.
"Constant payoff" here means that every displayed `u_S` is constant.  When
`delta > 0`, the actually received payoff still includes the paper's discount
factor at the stopping time.

The source first proves that this game has no exact Nash equilibrium.  It then
proves the strictly stronger robust statement: there is a positive accuracy
threshold such that the game has no Nash epsilon-equilibrium for every
sufficiently small positive epsilon.  The threshold is obtained by compactness
and a closed-graph argument for an auxiliary one-shot game; the paper does not
state a numerical value.

The decisive continuous-time move is a pure deviation to a deterministic time
strictly after zero but arbitrarily close to it.  Conditional on survival at
zero, the probability assigned by finitely many opponents' stopping laws to
the punctured interval `(0,t]` tends to zero with `t`.  Thus a player can move
after the time-zero atoms while preempting almost all later mass.  The generic
production lemma `Math.Probability.tendsto_measure_Ioc_zero_nhdsGT`
(`MathUE/Probability.lean`) records exactly this measure fact.  A discrete
clock has no date strictly between zero and its first positive date.

Section 6 gives the safe comparison in the other direction: discretizing an
existing continuous-time subgame-perfect epsilon-equilibrium yields, under
continuity and sufficiently small mesh, a discrete-time subgame-perfect
approximate equilibrium (the text says `2 epsilon`).  It does not prove that
discrete equilibria converge to continuous equilibria.  The counterexample is
therefore compatible with positive three-player results in discrete time.

## What this does not say about the quitting conjecture

The paper does not define or refute a continuous-time analogue of this project's
uniform-equilibrium-payoff predicate.  Its criterion is a one-shot expected
discounted terminal payoff under mixed stopping times.  The project instead
uses behavioral profiles in a repeated finite stochastic game and one profile
that works for every sufficiently long finite-average horizon at a fixed
accuracy.

The displayed coalition table can be reused as a three-player discrete quitting
reward, but the time domain and equilibrium semantics then change.  In fact,
the production theorem `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`)
applies to every reward table on `Fin 3`, hence also to that discrete table.  No
adapter identifying the paper's continuous strategies with the project's
behavioral profiles is claimed here.  The paper is therefore sharp boundary
evidence about dense-time preemption, not a counterexample to the project's
discrete conjecture and not evidence for a four-player discrete counterexample
without an additional construction.

## Correlation and later work

The primary paper does not assert that correlation repairs its example.  For
this particular payoff table, however, one can check an exact normal-form
correlated equilibrium directly.  A mediator uniformly chooses one of the
three unordered pairs, privately recommends "stop at zero" to that pair, and
recommends "continue" to the remaining player.  Conditional on a stop
recommendation, obedience and unilateral continuation both have expected
payoff `-1/2`; conditional on continuation, obedience pays `1`, while joining
at zero makes all three stop and pays `0`.  Deviating to a later time cannot
alter the time-zero outcome.  This calculation repairs this example only; it
is not a general correlated-existence theorem for continuous-time timing games.

A public 2022 seminar abstract titled *Stopping Games with Termination Rates*
advertises joint work of Eilon Solan and Catherine Rainer on restoring
epsilon-equilibrium after replacing instantaneous stopping by termination
intensities: `https://econ.biu.ac.il/en/node/6926`.  That announcement is not a
theorem source for this file, and no claim from a private or unpublished
version is assumed here.
-/

namespace Literature.LarakiSolanAndVieille2005

end Literature.LarakiSolanAndVieille2005
