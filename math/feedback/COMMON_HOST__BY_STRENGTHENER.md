# Review and generalization of the monodromy no-go

Reviewer: `STRENGTHENER`

## Claim reviewed

I reviewed only `# Followup` in `../COMMON_HOST.md`: the claim that the
literal `FinFourMonodromyProducer` trace is impossible because every pair
vertex is terminal, a pair-free simple Fin4 toggle cycle has period two, and
the two reverse positive endpoint edges contradict one another.

## Verdict

**The Fin4 argument is mathematically correct.** It does not use the
common-host or complementary-pair field. It eliminates the underlying
`FinFourMonodromyProducer`, subject to formalizing the finite-set cycle
lemmas described in the note.

The strongest clean generalization is not to arbitrary player cardinality.
It is:

> A dispatched same-stage endpoint trace is impossible whenever the union of
> all coalitions visited by its simple closed segment has cardinality at most
> four.

In particular the result holds on every finite player type of cardinality at
most four. The effective-support formulation also applies to a trace in a
larger game when all of its visited coalitions lie in one four-player face.

The threshold four is sharp for the local trace/edge interface: a five-player
four-cycle satisfying all of the same terminal, toggle, positive-gain, and
mover-debt properties is given below.

## Declaration audit

The relevant checked definitions and facts are:

- `QuittingSameStageSingletonRoute` in
  `Research/Quitting/SameStageEndpointMonodromy.lean` is genuinely
  existential in `who` and `action`; it has no best-endpoint or positive-gain
  premise.
- `QuittingSameStageEndpointEdge.target_eq_singlePlayer_toggle` gives a
  strict erase or insert of the edge's player.
- `QuittingSameStageEndpointEdge.source_ne_target`, `.gain_pos`, and
  `.mover_debt` expose exactly the nontriviality, sign, and scalar identity
  used by the proof.
- `MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment` stores
  `offset_not_terminal` and its underlying `MinimalClosedSegment` stores
  offset injectivity.
- `dispatchedClosedSegment_period_ne_one` already excludes period one.

No field of the global minimum source is used after these local objects have
been formed.

## 1. Every pair is terminal

Let `source` have cardinality two and choose `who ∈ source`. Set the endpoint
action to Continue. The routed coalition is `source.erase who`, hence a
singleton. At the literal pure-root profile, the source stage mass is the
live mass. The one-date Continue update produces the routed pure singleton at
the same live mass. Therefore the stage-mass inequality in
`QuittingSameStageSingletonRoute` holds with equality.

This verifies the note's most delicate point: terminality here does not
require the action to be a best endpoint. Thus `offset_not_terminal` excludes
every cardinality-two trace vertex.

## 2. Minimal Boolean-cycle lemma

Let `U` be the union of the visited coalitions and assume `U.card ≤ 4`.
Every trace vertex has cardinality at least two by its subtype, and pair
vertices have just been excluded, so every vertex has cardinality three or
four. Adjacent cardinalities differ by one by
`target_eq_singlePlayer_toggle`.

If a simple cycle had period at least three, choose a cardinality-three
vertex. Its predecessor and successor must both have cardinality four. Since
both are subsets of `U` and `U.card ≤ 4`, they are both equal to `U`. Their
two distinct cyclic offsets therefore carry the same vertex, contradicting
offset injectivity. If every vertex initially displayed has cardinality four,
one adjacent edge produces a cardinality-three vertex and the same argument
applies.

Hence the period is at most two. Period one is already checked to be
impossible, so the period is two.

For a global theorem with `Fintype.card ι ≤ 4`, simply take
`U = Finset.univ`. Cardinalities zero through three cause no extra case:
there is respectively no nonsingleton state, only terminal pair states, or
only one possible nonterminal vertex.

## 3. Reverse strict edges are impossible

Let the two vertices be `A,B`. Each edge toggles the unique element of the
symmetric difference `A △ B`; hence the forward and reverse movers are the
same player `p`.

The two stored mover-debt identities are

\[
 d_p(B)=d_p(A)-g_0,
 \qquad
 d_p(A)=d_p(B)-g_1,
\]

with `g_0,g_1>0`. Adding gives `g_0+g_1=0`, a contradiction. Equivalently,
the two exact same-stage payoff gains are opposite differences for the same
player, so they cannot both be positive. This second formulation shows that
the debt fields are stronger than necessary for the period-two exclusion.

## 4. Sharp five-player boundary

Let the players be three hosts `h₁,h₂,h₃` and two movers `a,b`. Put

\[
 H=\{h_1,h_2,h_3\}
\]

and consider

\[
 H\to H\cup\{a\}\to H\cup\{a,b\}
 \to H\cup\{b\}\to H.
 \tag{1}
\]

All four coalitions have cardinality three, four, five, or four. Therefore
none can route to a singleton in one toggle, so none satisfies the terminal
predicate.

Define the two relevant payoff coordinates on these coalitions by

\[
 r_a(S)=\mathbf 1\{\mathbf 1_{a\in S}\ne\mathbf 1_{b\in S}\},
 \qquad
 r_b(S)=\mathbf 1\{\mathbf 1_{a\in S}=\mathbf 1_{b\in S}\},
 \tag{2}
\]

and set the host payoffs arbitrarily, say zero. Then the four moves in (1),
with movers `a,b,a,b`, each improve the mover's payoff by exactly one. Pure
sure-exit roots make these the exact behavioral endpoint gains; the mover
debt drops from one to zero on each chosen edge and is replenished when the
other mover acts. Every edge can be represented by the local
`QuittingSameStageEndpointEdge` data with a sufficiently small positive
`lambda` and an actual positive-debt semantic parameter.

This is the upper-face analogue of the checked cyclic-plateau regression. It
does not construct a positive-global-minimum quitting-game counterexample,
and therefore does not refute a hypothetical larger-player producer theorem
using additional minimum provenance. It does prove that the Fin4 elimination
cannot be derived from the local terminal/edge/closed-segment interface once
five effective players are allowed.

## Strongest abstract theorem worth formalizing

A reusable Lean-facing statement should separate the Boolean geometry from
quitting semantics:

```text
no_dispatchedStrictToggleClosedSegment_of_union_card_le_four
```

with hypotheses:

1. visited states are nonempty finite subsets and every visited pair is
   terminal;
2. the closed segment contains no terminal state and is simple;
3. every edge is a nontrivial one-coordinate toggle;
4. a forward/reverse pair of edges has the same label and cannot both occur
   (supplied either by strict payoff differences or mover-debt descent); and
5. the union of visited subsets has cardinality at most four.

The quitting adapter then proves pair terminality and reverse-edge
incompatibility from the named declarations above. `FinFourMonodromyProducer`
is the immediate `U=univ` specialization, and the common-host and
complementary-pair eliminators are projections.

## Edge cases and nonclaims

- Pair terminality is specific to a singleton-route terminal predicate. It
  would be false if terminality required the routed action to be profitable
  or best.
- Simplicity is essential to the period reduction; an arbitrary closed walk
  can backtrack through the unique top vertex many times.
- Positive gain (or another antisymmetric strict label potential) is essential
  to exclude period two.
- Common-host geometry does not rescue the arbitrary-cardinality theorem:
  the five-player cycle (1) has three common hosts.
- The five-player boundary is a local interface counterexample, not an
  all-behavior positive-gap table.

There is no unresolved mathematical objection to the Fin4 no-go.
