# Continuation Games as States

**Status (2026-08-30).** Independent exploratory note.  The exact
all-Continue transport result below is proved in ordinary mathematics but has
not been checked in Lean.  The horizontal-replacement counterexample is exact.
No uniform-equilibrium producer is claimed.

## Question

Can a quitting game be made Markov-complete for the proof problem by treating
the continuation game itself as the state?  More precisely, can one construct
a compact state space which

1. contains the continuation data of every actual behavioral profile;
2. has an exact continuous transition when one product root is prefixed;
3. retains prescribed payoffs, unrestricted behavioral caps, terminal laws,
   escaping deadlines, and terminal bubbles; and
4. also supports the one-player replacements used by debt consumers?

The answer after this exploration is mixed.

* If a continuation game means only the quitting reward table with a variable
  all-Continue row, the construction is exactly the existing Bellman/semantic
  state.  It is useful but not new.
* The closed graph of every pure stopping-time response is a small, genuinely
  chronological compact augmentation.  It has an exact continuous prefix
  law, makes the unrestricted cap a continuous maximum coordinate, and makes
  every positive-survival prefix reversible on its image.  This recovers the
  exact second-day state even when the scalar cap maximum hides it.
* Payoff, terminal law, and all one-player response graphs still do **not**
  determine a horizontal one-player update.  A three-player, three-date
  counterexample proves this.
* Adding every player's complete stopping law repairs horizontal replacement
  for actual profiles, but not continuously at the compact boundary.  The
  correct boundary operation is a correlated closed relation, not a function.
  This remains true even when source law, terminal law, and every unary
  response graph converge jointly and the same moving replacement is used on
  both source sequences.
* There is a sharp positive exception: if the moving replacement laws have a
  proper weak limit, the full semantic target is unique and continuous.  More
  generally, if the limiting replacement has Never mass `q`, the semantic
  target fibre has diameter at most `2 M q` coordinatewise (with the mover's
  cap exactly fixed).
* The hyperspace is genuinely needed: with only two players, one infinity
  fibre can be any prescribed compact subset of a reward interval containing
  its endpoints.  There is no general interval or finite-bubble normal form.
* Storing all multi-player replacement kernels repairs the algebra at actual
  profiles.  Its full compact version approaches a universal strategic
  compactification and risks becoming tautological; it does not by itself
  turn horizontal better replies into an executable quitting chronology.

The most concrete new object is therefore the **completed response-graph
state**, developed in
[`EXACT_RESPONSE_GRAPH_TRANSPORT.md`](EXACT_RESPONSE_GRAPH_TRANSPORT.md).
Its precise limit is recorded in
[`HORIZONTAL_REPLACEMENT_NO_GO.md`](HORIZONTAL_REPLACEMENT_NO_GO.md).

## Main verdict

The idea isolates two different meanings of “the whole game as state.”

### Strategic continuation game

If every player is allowed to replace their whole future behavior, the pure
actions are stopping times in `Nat union {Never}`.  The resulting infinite
normal-form game is time-homogeneous: after all Continue, it is literally the
same strategic game.  As a state it is a self-loop and gives no progress.

### Profile-relative response game

If opponents remain fixed at their prescribed continuation, then each player
has a changing stopping problem.  Its complete pure-time value graph is not a
self-loop.  Prefixing acts on that graph by an explicit affine shift.  This is
the useful interpretation, but it is player-relative and is not closed under
changing an opponent unless more source data are retained.

Thus the promising research object is not another payoff matrix.  It is a
compact **profile-relative continuation passport** with a deterministic
vertical prefix action and a correlated horizontal replacement relation.
For adaptively selected deadlines the compact object must be a state-action-
target graph; a compact state alone cannot make the transition single-valued.

## Candidate consumer

A completed response-graph state could strengthen a supplied near-return:
recurrence in this state controls the entire pure-deadline obstacle, not only
its supremum.  Consequently it could feed a consumer of the form

```text
actual exact/punishment-admissible chronology
+ start and end close in completed response-graph state
+ positive cumulative paid charge
--------------------------------------------------------
terminal approximate Nash profiles with one payoff target.
```

This is only a plausible **consumer**.  The state does not produce the
admissible chronology.  In particular, iterated behavioral best replies yield
horizontal edges; compact recurrence of those edges is not temporal
realizability.

## Files

* [`EXACT_RESPONSE_GRAPH_TRANSPORT.md`](EXACT_RESPONSE_GRAPH_TRANSPORT.md):
  exact graph, cap, law, and prefix formulas.
* [`MATRIX_STATE_REDUCTION.md`](MATRIX_STATE_REDUCTION.md): the literal varying
  all-Continue matrix is exactly the existing `U` or `(U,B)` Bellman state.
* [`HORIZONTAL_REPLACEMENT_NO_GO.md`](HORIZONTAL_REPLACEMENT_NO_GO.md): exact
  counterexamples and the minimal actual-profile repair.
* [`FULL_REPLACEMENT_KERNEL_ATLAS.md`](FULL_REPLACEMENT_KERNEL_ATLAS.md): a
  larger algebraically closed state and why it is not yet a producer.
* [`FIBER_AND_ORDER_NO_GOS.md`](FIBER_AND_ORDER_NO_GOS.md): disconnected
  infinity fibres, the replacement-order escalation, and the constant-game
  dead end.
* [`INFINITY_FIBER_UNIVERSALITY.md`](INFINITY_FIBER_UNIVERSALITY.md): every
  compact subset of a reward interval containing its endpoints is realizable
  as a two-player infinity fibre.
* [`ALL_CONTINUE_BOUNDARY_FIXED_POINT.md`](ALL_CONTINUE_BOUNDARY_FIXED_POINT.md):
  repeated inert delay converges to a fixed response-bubble state.
* [`FIXED_DEADLINE_HORIZONTAL_CONTINUITY.md`](FIXED_DEADLINE_HORIZONTAL_CONTINUITY.md):
  any convergent replacement family with a proper limiting clock has
  continuous full-semantic transport; positive limiting Never mass retains
  the defect.
* [`NEVER_MASS_HORIZONTAL_FIBER_BOUND.md`](NEVER_MASS_HORIZONTAL_FIBER_BOUND.md):
  for a fixed replacement law, the completed target fibre has semantic
  diameter linear in that law's Never mass.
* [`OVERLAP_AND_SOURCES.md`](OVERLAP_AND_SOURCES.md): bounded source audit and
  relation to existing machinery.
* [`NEXT_QUESTIONS.md`](NEXT_QUESTIONS.md): concrete follow-up questions and
  falsification targets.

## Claims proved here versus conjectural

Proved in ordinary mathematics:

* behavioral strategies on the live spine are equivalent, for terminal
  semantics, to stopping laws on `Nat union {Never}`;
* the response graph recovers the complete behavioral cap;
* the exact one-root affine-shift formula for the response graph;
* injectivity and tail recovery of positive-survival prefixing on the graph
  state;
* the exact terminal-law and prescribed-payoff prefix formulas;
* failure of horizontal replacement from payoff, law, and all unary response
  graphs;
* exact horizontal replacement from the full vector of actual stopping laws;
* failure of continuity of terminal outcome evaluation in the weak compact
  stopping-law topology;
* continuity of horizontal replacement by a fixed proper stopping law;
* a linear Never-mass bound on the semantic diameter of a fixed replacement's
  boundary fibre, including the completed response graphs of nonmovers;
* universality of arbitrary compact endpoint-containing infinity fibres in a
  fixed two-player reward table;
* convergence of repeated all-Continue delay to the explicit fixed
  response-bubble state.

Conjectural or merely proposed:

* usefulness of response-graph recurrence to an existing near-return
  compiler;
* a minimal metrizable multi-replacement compactification closed under
  adaptively selected replacements;
* any route from this state construction to terminal approximate Nash
  profiles for an arbitrary quitting table.
